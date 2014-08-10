(* Compile Scheme expressions into a form that can be evaluated efficiently.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc
open Ocs_env
open Ocs_vartable

(* Split the variables that are arguments to let/let*/letrec *)
let letsplit f =
  function
    Spair { car = (Ssymbol _ | Sesym (_, _)) as s;
            cdr = Spair { car = v; cdr = Snull }} -> f s v
  | _ -> raise (Error "invalid let arglist")
;;

(* Split the variables that are arguments to do *)
let dosplit f =
  function
    Spair { car = (Ssymbol _ | Sesym (_, _)) as sym;
            cdr = Spair { car = init; cdr = t }} ->
      begin
        match t with
          Snull -> f sym init sym
        | Spair { car = step; cdr = Snull } -> f sym init step
        | _ -> raise (Error "invalid do arglist")
      end
  | _ -> raise (Error "invalid do arglist")
;;

let genset b v =
  match b with
    Vglob g -> Csetg (g, v)
  | Vloc l -> l.l_mut <- true; Csetl (l.l_pos, v)
  | _ -> raise (Error "cannot change syntactic keywords")
;;

let gendef b v =
  match b with
    Vglob g -> Cdefine (g, v)
  | Vloc l -> l.l_mut <- true; Csetl (l.l_pos, v)
  | _ -> raise (Error "cannot change syntactic keywords")
;;

let genref =
  function
    Vglob g ->
      begin
        match g.g_val with
          Sprim _ -> Cval g.g_val
        | _ -> Cgetg g
      end
  | Vloc l -> Cgetl l.l_pos
  | Vsyntax _ -> Cval Sunspec
  | Vmacro _ -> Cval Sunspec
  | Vkeyword _ -> Cval Sunbound
;;

let make_lambda ?proc_name c n hr =
  { lam_body = c;
    lam_args = n;
    lam_has_rest = hr;
    lam_name = proc_name }
;;

let chksplice a =
  let n = Array.length a in
    let rec loop i =
      if i < n then
        begin
          match a.(i) with
            Cqqspl _ -> true
          | _ -> loop (i + 1)
        end
      else
        false
    in
      loop 0
;;

(* Scan quoted sections, eliminate environment-specific symbols *)
let rec scanquoted =
  function
    Sesym (_, sym) -> sym
  | Spair { car = h; cdr = t } ->
      Spair { car = scanquoted h; cdr = scanquoted t }
  | Svector v ->
      Svector (Array.map (fun x -> scanquoted x) v)
  | x -> x
;;

let is_uglobal e =
  vt_global e.env_vartable
;;

let is_global e =
  e.env_depth < 0
;;

let rec mkdefine e =
  function
    [] ->
      raise (Error "define: not enough args")
  | Spair { car = (Ssymbol _ | Sesym _) as s; cdr = al } :: _ :: _ as args ->
      let l = mklambda ~proc_name:(sym_name s) e al args in
        gendef (get_var e s) l
  | (Ssymbol _ | Sesym _) as s :: a1 :: [] ->
      gendef (get_var e s) (compile e a1)
  | (Ssymbol _ | Sesym _) as s :: [] ->
      gendef (get_var e s) (Cval Sunspec)
  | _ ->
      raise (Error "define: invalid syntax")

(* The following functions up to mkbody are used to compile the body
   of a lambda, let etc., with possible internal definitions.  The
   internal definitions may be created by macro expansion, so we need
   to do that here, too...and we might end up expanding a macro more
   than once (so there must be no side-effects to expansion).  *)
and idpp =
  function
    Spair { car = (Ssymbol _ | Sesym (_, _)) as s;
            cdr = Spair { car = v; cdr = Snull }} -> (s, s, v)
  | Spair { car = Spair { car = (Ssymbol _ | Sesym (_, _)) as s;
                          cdr = _ } as x;
            cdr = _ } as v -> (s, x, v)
  | _ -> raise (Error "invalid internal definition")

and getidef e =
  function
    Spair { car = (Ssymbol _ | Sesym (_, _)) as s; cdr = t } ->
      begin
        match find_var e s with
          Some (Vsyntax f) when f == mkdefine -> Some (idpp t)
        | Some (Vmacro f) -> getidef e (f e (Array.of_list (list_to_caml t)))
        | _ -> None
      end
  | _ -> None

and mkid e x v =
  match x with
    Spair { car = _; cdr = al } ->
      mklambda e al (list_to_caml v)
  | _ -> compile e v

and expand_begin e =
  function
    (Spair { car = (Ssymbol _ | Sesym (_, _)) as s; cdr = t }) as x ->
      begin
        match find_var e s with
          Some (Vsyntax f) when f == mkbegin ->
            List.concat (List.map (expand_begin e) (list_to_caml t))
        | Some (Vmacro f) ->
            expand_begin e (f e (Array.of_list (list_to_caml t)))
        | _ -> [ x ]
      end
  | x -> [ x ]

and mkbody e args =
  let args = List.concat (List.map (expand_begin e) args) in
  let rec loop r =
    function
      [] -> List.rev r, []
    | a :: al as args ->
        begin
          match getidef e a with
            Some d -> loop (d :: r) al
          | None -> List.rev r, args
        end
  in
  let ids, rest = loop [] args in
  let ids = List.map (fun (s, x, v) -> let r = bind_var e s in (r, x, v)) ids in
  let rest = List.map (fun x -> compile e x) rest in
  List.fold_right (fun (r, x, v) rest -> gendef r (mkid e x v) :: rest) ids rest

and mkset e =
  function
    (Ssymbol _ | Sesym _) as s :: a1 :: [] ->
      let v = compile e a1 in
        genset (get_var e s) v
  | _ :: _ :: [] ->
      raise (Error "set!: not a symbol")
  | _ ->
      raise (Error "set!: requires exactly two args")

(* Note that the first item of the "body" array is ignored, it
   corresponds to the argument list but may be in the form expected
   by either define or lambda.  *)
and mklambda ?proc_name e args body =
  let ne = new_frame e
  and largs = ref []
  and has_rest = ref false in
  let rec scanargs =
    function
      Spair { car = (Ssymbol _ | Sesym (_, _)) as s; cdr = tl } ->
        let r = bind_var ne s in
          largs := r :: !largs;
          scanargs tl
    | (Ssymbol _ | Sesym (_, _)) as s ->
        let r = bind_var ne s in
          largs := r :: !largs;
          has_rest := true;
          ()
    | Snull -> ()
    | _ -> raise (Error "lambda: bad arg list")
  in
    scanargs args;
    let largs = List.rev !largs in
    let body =
      Cseq (mkbody ne (List.tl body))
    in
      Clambda (make_lambda ?proc_name body largs !has_rest)

and mkif e =
  function
    a0 :: a1 :: [] ->
      Cif (compile e a0, compile e a1, Cval Sunspec)
  | a0 :: a1 :: a2 :: [] ->
      Cif (compile e a0, compile e a1, compile e a2)
  | _ ->
      raise (Error "if: needs two or three args")

and mknamedlet e s =
  function
    [] ->
      (* This possibility is ruled out in [mklet] below *)
      assert false
  | a1 :: args ->
      let argv =
        List.map
          (letsplit (fun s v -> s, compile e v))
          (list_to_caml a1) in
      let ar = new_var e in
      let ne = new_frame e in
        bind_name ne s ar;
        let largs = ref [] in
        let av =
          List.map (fun (s, v) -> let r = bind_var ne s in largs := r :: !largs; v) argv in
        let largs = List.rev !largs in
        let body = Cseq (mkbody ne args) in
        let proc =
          Clambda (make_lambda body largs false)
        in
          Cseq [ gendef ar proc; Capply (genref ar, av) ]

and mklet e =
  function
    [] | _ :: [] ->
      raise (Error "let: too few args")
  | (Ssymbol _ | Sesym _) as s :: args ->
      mknamedlet e s args
  | Snull :: args ->
      Cseq (mkbody e args)
  | Spair _ as al :: args ->
      let argv =
        List.map
          (letsplit (fun s v -> s, compile e v))
          (list_to_caml al) in
      let ne = new_frame e in
      let largs = ref [] in
      let av = List.map (fun (s, v) -> let r = bind_var ne s in largs := r :: !largs; v) argv in
      let largs = List.rev !largs in
      let body = Cseq (mkbody ne args) in
      let proc =
        Clambda (make_lambda body largs false)
      in
        Capply (proc, av)
  | _ ->
      raise (Error "let: missing argument list")

and mkletstar e =
  function
    [] | _ :: [] ->
      raise (Error "let*: too few args")
  | a0 :: args ->
      let rec build e =
        function
          x :: t ->
            let (s, v) = letsplit (fun s v -> s, compile e v) x in
            let ne = new_frame e in
            let r = bind_var ne s in
            let body = build ne t in
            let proc = Clambda (make_lambda body [r] false) in
              Capply (proc, [ v ])
        | [] -> Cseq (mkbody e args)
      in
        build e (list_to_caml a0)

and mkletrec e =
  function
    [] | _ :: [] ->
      raise (Error "letrec: too few args")
  | a0 :: args ->
      let ne = new_frame e in
      let largs = ref [] in
      let av =
        List.map (letsplit (fun s v -> let r = bind_var ne s in largs := r :: !largs; (r, v)))
          (list_to_caml a0) in
      let largs = List.rev !largs in
      let avi = List.map (fun (_, v) -> compile ne v) av in
      let ne' = new_frame ne in
      let largs' = ref [] in
      let sets = List.map (fun (r, _) ->
          let rr = new_var ne' in
            largs' := rr :: !largs';
            gendef r (genref rr)) av in
      let largs' = List.rev !largs' in
      let body = Cseq (List.append sets (mkbody ne' args)) in
      let proc =
        Clambda (make_lambda body largs' false) in
      let proc =
        Clambda (make_lambda (Capply (proc, avi)) largs false)
      in
        Capply (proc, List.map (fun _ -> Cval Sunspec) av)

and compileseq e s =
  Cseq (List.map (fun x -> compile e x) (list_to_caml s))

and mkcond e args =
  Ccond
    (List.map
      (function
          Spair { car = test;
                  cdr = Spair { car = (Ssymbol _ | Sesym (_, _)) as s;
                                cdr = Spair { car = x; cdr = Snull }}}
            when is_keyword e s "=>" ->
              (Ccondspec (compile e test), (compile e x))
        | Spair { car = (Ssymbol _ | Sesym (_, _)) as s; cdr = body }
            when is_keyword e s "else" ->
            (Cval Strue, compileseq e body)
        | Spair { car = test; cdr = body } ->
            (compile e test, compileseq e body)
        | _ -> raise (Error "cond: syntax error"))
      args)

and mkcase e =
  function
    [] ->
      assert false (* FIXME *)
  | a0 :: args ->
      Ccase
        (compile e a0,
         List.map
           (function
               Spair { car = (Ssymbol _ | Sesym (_, _)) as s; cdr = body }
               when is_keyword e s "else" ->
                 ([ ], compileseq e body)
             | Spair { car = Spair _ as c; cdr = body } ->
                 (list_to_caml c), compileseq e body
             | _ -> raise (Error "case: syntax error"))
           args)

and mkdo e =
  function
    [] | _ :: [] ->
      raise (Error "do: bad args")
  | a0 :: a1 :: args ->
      let vv =
        List.map
          (dosplit (fun sym init step -> sym, compile e init, step))
          (list_to_caml a0)
      and (test, result) =
        match a1 with
          Spair { car = t; cdr = r } -> t, r
        | _ -> raise (Error "do: bad args")
      and anonvar = new_var e
      and ne = new_frame e in
      let largs = ref [] in
      let av = List.map (fun (sym, init, _) ->
          let r = bind_var ne sym in largs := r :: !largs; init) vv in
      let largs = List.rev !largs in
      let body =
        Cif (compile ne test, compileseq ne result,
             Cseq 
               (List.append
                  (List.map (fun x -> compile ne x) args)
                  [ Capply (genref anonvar, List.map (fun (_, _, step) -> compile ne step) vv) ]))
      in
      let proc =
        Clambda (make_lambda body largs false)
      in
        Cseq [ gendef anonvar proc; Capply (genref anonvar, av) ]

and mkdelay e =
  function
    [ expr ] -> Cdelay (compile e expr)
  | _ -> raise (Error "delay: bad args")

and mkqq e =
  function
    [] | _ :: _ :: _ ->
      raise (Error "quasiquote: need exactly one arg")
  | a0 :: [] ->
      let rec qq depth =
        function
          Spair { car = (Ssymbol _ | Sesym (_, _)) as s;
                  cdr = Spair { car = x; cdr = Snull }} ->
            if is_syntax e s mkqq then
              Cqqp (Cval s, Cqqp (qq (depth + 1) x, Cval Snull))
            else if is_keyword e s "unquote" then
              begin
                if depth > 0 then
                  Cqqp (Cval s, Cqqp (qq (depth - 1) x, Cval Snull))
                else
                  compile e x
              end
            else if is_keyword e s "unquote-splicing" then
              begin
                if depth > 0 then
                  Cqqp (Cval s, Cqqp (qq (depth - 1) x, Cval Snull))
                else
                  Cqqspl (compile e x)
              end
            else
              Cqqp (Cval s, Cqqp (qq depth x, Cval Snull))
        | Spair { car = h; cdr = t } -> Cqqp (qq depth h, qq depth t)
        | Svector v ->
            let qv = Array.map (fun x -> qq depth x) v in
              if chksplice qv then
                Cqqvs (Array.to_list qv)
              else
                Cqqv (Array.to_list qv)
        | x -> Cval (scanquoted x)
      in
        qq 0 a0

and applysym e s args =
  match get_var e s with
    Vsyntax f -> f e args
  | Vmacro f -> compile e (f e (Array.of_list args))
  | r -> Capply (genref r, List.map (fun x -> compile e x) args)

and compile e =
  function
    (Ssymbol _ | Sesym (_, _)) as s -> genref (get_var e s)
  | Spair p ->
      let args = list_to_caml p.cdr in
        begin
          match p.car with
            (Ssymbol _ | Sesym (_, _)) as s -> applysym e s args
          | x ->
              Capply (compile e x, List.map (fun x -> compile e x) args)
        end
  | x -> Cval (scanquoted x)

and mkbegin e args =
  Cseq (List.map (fun x -> compile e x) args)
;;

let bind_lang e =
  let spec =
    [ sym_define, mkdefine;
      sym_set, mkset;
      sym_let, mklet;
      sym_letstar, mkletstar;
      sym_letrec, mkletrec;
      sym_if, mkif;
      sym_cond, mkcond;
      sym_case, mkcase;
      sym_do, mkdo;
      sym_begin, mkbegin;
      sym_and, (fun e args -> Cand (List.map (fun x -> compile e x) args));
      sym_or, (fun e args -> Cor (List.map (fun x -> compile e x) args));
      sym_lambda,
      (fun e args ->
         match args with
           [] ->
             raise (Error "lambda: needs at least one arg")
         | a0 :: _ ->
             mklambda e a0 args);
      sym_delay, mkdelay;
      sym_quote,
      (fun e args ->
         match args with
           a0 :: [] ->
             Cval (scanquoted a0)
         | _ ->
             raise (Error "quote: need exactly one arg"));
      sym_quasiquote, mkqq ]
  in
    List.iter (fun (s, f) -> bind_name e s (Vsyntax f)) spec;
    bind_name e sym_else (Vkeyword "else");
    bind_name e sym_arrow (Vkeyword "=>");
    bind_name e sym_unquote (Vkeyword "unquote");
    bind_name e sym_unquote_splicing (Vkeyword "unquote-splicing");
    bind_name e sym_syntax_rules (Vkeyword "syntax-rules");
;;

