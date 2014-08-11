(* Various primitives *)

open Ocs_types
open Ocs_error
open Ocs_env
open Ocs_misc
open Ocs_sym
open Ocs_compile
open Ocs_macro

let logical_not =
  function
    Sfalse -> Strue
  | _ -> Sfalse
;;

(* Type predicates *)

let is_boolean =
  function
    Strue | Sfalse -> Strue
  | _ -> Sfalse
;;

let is_string =
  function
    Sstring _ -> Strue
  | _ -> Sfalse
;;

let is_char =
  function
    Schar _ -> Strue
  | _ -> Sfalse
;;

let is_pair =
  function
    Spair _ -> Strue
  | _ -> Sfalse
;;

let is_null =
  function
    Snull -> Strue
  | _ -> Sfalse
;;

let is_vector =
  function
    Svector _ -> Strue
  | _ -> Sfalse
;;

let is_proc =
  function
    Sproc _ -> Strue
  | _ -> Sfalse
;;

let is_port =
  function
    Sport _ -> Strue
  | _ -> Sfalse
;;

let is_symbol =
  function
    Ssymbol _ -> Strue
  | _ -> Sfalse
;;

let symbol_to_string =
  function
    Ssymbol s -> Sstring s
  | _ -> raise (Error "symbol->string: not a symbol")
;;

let string_to_symbol =
  function
    Sstring s -> get_symbol (String.copy s)
  | _ -> raise (Error "string->symbol: not a string")
;;

let is_eq a b =
  if a == b then Strue else Sfalse
;;

let is_eqv a b =
  if test_eqv a b then Strue else Sfalse
;;

let is_equal a b =
  if test_equal a b then Strue else Sfalse
;;

let new_param i c =
  Sparam
    {
      p_dynvar = Dynvar.dnew ();
      p_init = i;
      p_conv = c
    }
;;

let get_param p =
  match p with
    Sparam p ->
      begin
        try
          Dynvar.dref p.p_dynvar
        with
          _ -> p.p_conv p.p_init
      end
  | _ ->
      raise (Error "param_get: not a parameter")
;;

let set_param p x =
  match p with
    Sparam p ->
      begin
        try
          let _ = Dynvar.dset p.p_dynvar x in
            ()
        with
          _ -> p.p_init <- p.p_conv x
      end
  | _ ->
      raise (Error "param_set: not a parameter")
;;

let let_param p x f =
  match p with
    Sparam p ->
      Dynvar.dlet p.p_dynvar (p.p_conv x) f
  | _ ->
      raise (Error "param_let: not a parameter")
;;

let rec proc_has_rest : type a. a sg -> bool = function
    Pfix sg -> proc_has_rest sg
  | Prest _ -> true
  | Pret _ -> false
  | Pvoid _ -> false
;;

let rec proc_nargs : type a. a sg -> int = function
    Pfix sg -> 1 + proc_nargs sg
  | Pret _ -> 0
  | Prest _ -> 1
  | Pvoid _ -> 0
;;

let args_err sg proc_name n =
  if proc_has_rest sg then
    Printf.sprintf "procedure %s expected %d or more args got %d"
      proc_name (proc_nargs sg - 1) n
  else
    Printf.sprintf "procedure %s expected %d args got %d"
      proc_name (proc_nargs sg) n
;;

let rec apply th p av =
  match p with
    Sprim p
  | Sproc p ->
      let Pf (sg, f) = p.proc_fun in 
      let ret : type a. a ret -> a -> sval = fun r f ->
        match r with
          Rval ->
            f
        | Rcont ->
            f th
      in
      let rec loop : type a. a sg -> a -> _ -> sval = fun sg f al ->
        match sg, al with
          Pfix sg, a :: al ->
            loop sg (f a) al
        | Prest r, _ ->
            ret r (f al)
        | Pret r, [] ->
            ret r f
        | Pvoid r, [] ->
            ret r (f ())
        | _ ->
            raise (Error (args_err sg p.proc_name (List.length av)))
      in
        loop sg f av
  | Sparam _ as p ->
      begin
        match av with
          [] -> get_param p
        | a :: [] -> set_param p a; Sunspec
        | _ ->
            raise (Error ("apply: parameter expected 1 or 2 args, got " ^ (string_of_int (List.length av))))
      end
  | _ ->
      raise (Error "apply: not a procedure or primitive")
;;

let do_apply f av th =
  let rec loop = function
      [] -> raise (Error "apply: bad args")
    | [a] -> list_to_caml a
    | a :: av -> a :: loop av
  in
  let args = loop av in
    apply th f args
;;

let make_parameter args th =
  match args with
    init :: [] ->      
      new_param init (fun x -> x)
  | init :: converter :: [] ->
      new_param init (fun x -> apply th converter [ x ])
  | _ ->
      raise (Error "make-parameter: bad args")
;;

let force p _ =
  match p with
    Spromise p ->
      Lazy.force p
  | _ ->
      p (* if not a promise, we just return the argument *)
;;

let map_for_each av th is_map =
  let my_name = if is_map then "map" else "for-each" in
    match av with
      [] | _ :: [] ->
        raise (Error (my_name ^ ": bad args"))
    | proc :: args ->
        let get_cdr =
          function
            Spair { car = _; cdr = t } -> t
          | _ -> raise (Error (my_name ^ ": list lengths don't match"))
        and get_carc =
          function
            Spair { car = h; cdr = _ } -> h
          | _ -> raise (Error (my_name ^ ": list lengths don't match"))
        and result = ref (if is_map then Snull else Sunspec)
        and rtail = ref Snull in
        let append v =
          if !rtail == Snull then
            begin
              result := Spair { car = v; cdr = Snull };
              rtail := !result;
            end
          else
            begin
              match !rtail with
                Spair p ->
                  p.cdr <- Spair { car = v; cdr = Snull };
                  rtail := p.cdr
              | _ -> assert false
            end
        in
        let rec loop args =
          match args with
            Snull :: _ -> !result
          | Spair _ :: _ ->
              let v = apply th proc (List.map get_carc args) in
                if is_map then append v;
                loop (List.map get_cdr args)
          | _ -> raise (Error (my_name ^ ": invalid argument lists"))
        in
          loop args
;;

let map av th =
  map_for_each av th true
;;

let for_each av th =
  map_for_each av th false
;;

let report_env e _ =
  Sesym (env_copy e, Ssymbol "")
;;

let null_env _ =
  let e = top_env () in
    bind_lang e;
    bind_macro e;
    Sesym (e, Ssymbol "")
;;

let interact_env e =
  fun () -> Sesym (e, Ssymbol "") 
;;

let init e =
  set_pf1 e logical_not "not";
  set_pf1 e is_boolean "boolean?";
  set_pf1 e is_string "string?";
  set_pf1 e is_char "char?";
  set_pf1 e is_vector "vector?";
  set_pf1 e is_pair "pair?";
  set_pf1 e is_null "null?";
  set_pf1 e is_proc "procedure?";
  set_pf1 e is_port "port?";
  set_pf1 e is_symbol "symbol?";

  set_pf1 e symbol_to_string "symbol->string";
  set_pf1 e string_to_symbol "string->symbol";

  set_pf2 e is_eq "eq?";
  set_pf2 e is_eqv "eqv?";
  set_pf2 e is_equal "equal?";

  set_pfg e (Pfix (Prest Rcont)) do_apply "apply";

  set_pfg e (Prest Rcont) make_parameter "make-parameter";

  set_pfg e (Pfix (Pret Rcont)) force "force";

  set_pfg e (Prest Rcont) map "map";
  set_pfg e (Prest Rcont) for_each "for-each";

  set_pf1 e (report_env (env_copy e)) "scheme-report-environment";
  set_pf1 e null_env "null-environment";
  set_pf0 e (interact_env e) "interaction-environment";
;;

