(* Actual evaluator for the semi-compiled form.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc
open Ocs_prim
open Ocs_compile
open Ocs_env
  
  (* Staging environment, used during staging.  *)
type senv =
  [ `I of sval code
  | `M of sval ref code ] list

let bind e (v : vbind) (a : sval code) (cc : senv -> _ code) =
  if Ocs_env.is_mutable v then
    .< let x = ref .~a in .~(cc (`M .< x >. :: e)) >.
  else
    .< let x = .~a in .~(cc (`I .< x >. :: e)) >.

(* Local variables are stored either in th_frame or th_display.
   th_frame is the deepest frame, not yet part of the display.  *)

let getl e i =
  let i = List.length e - i - 1 in
    match List.nth e i with
      `I c -> c
    | `M c -> .< ! .~c >.
;;

let setl e i v =
  let i = List.length e - i - 1 in
    match List.nth e i with
      `I _ -> raise (Error "setl: internal error")
    | `M c -> .< .~c := .~v >.
;;

  (* This is necessary to pass a function ('a. 'a sg -> 'b) as an argument, see
     the case of [Clambda] in [Ocs_stage.stage] *)
type 'b slambda_c =
  {
    cc : 'a. 'a sg -> 'b
  }

let rec stage e =
  function
    Cval v -> .< v >.
  | Cseq s ->
      let rec loop =
        function
          [] ->
            .< Sunspec >.
        | s :: [] ->
            stage e s
        | s :: sl ->
            .< let _ = .~(stage e s) in .~(loop sl) >.
      in
        loop s
  | Cand s ->
      let rec loop =
        function
          [] -> .< Strue >.
        | s :: [] ->
            stage e s
        | s :: sl ->
            .< match .~(stage e s) with
                 Sfalse -> Sfalse
               | _ -> .~(loop sl) >.
      in
        loop s
  | Cor s ->
      let rec loop =
        function
          [] -> .< Sfalse >.
        | s :: [] ->
            stage e s
        | s :: sl ->
            .< match .~(stage e s) with
                 Sfalse -> .~(loop sl)
               | _ as x -> x >.
      in
        loop s
  | Cif (c, tx, fx) ->
      .< match .~(stage e c) with
           Sfalse -> .~(stage e fx)
         | _ -> .~(stage e tx) >.
  | Csetg (g, c) ->
      let err = "set!: unbound variable " ^ (sym_name g.g_sym) in
        .< if g.g_val == Sunbound then
             raise (Error err)
           else
             let () = g.g_val <- .~(stage e c) in Sunspec >.
  | Csetl (i, c) ->
      .< let () = .~(setl e i (stage e c)) in Sunspec >.
  | Cdefine (g, c) ->
      .< let () = g.g_val <- .~(stage e c) in Sunspec >.
  | Cgetg g ->
      let err = "unbound variable: " ^ (sym_name g.g_sym) in
        .< if g.g_val == Sunbound then
             raise (Error err)
           else
             g.g_val >.
  | Cgetl i ->
      getl e i
  | Capply (Cval (Sprim p), av) ->
      begin
        let Pf (sg, f) = p.proc_fun in
        let rec loop : type a. a sg -> a code -> _ -> sval code = fun sg f al ->
          match sg, al with
            Pfix sg, a :: al ->
              loop sg .< .~f .~(stage e a) >. al
          | Prest, _ ->
              let rec mkrest cc = function
                  [] -> cc .< [] >.
                | a :: al ->
                    mkrest (fun al -> cc .< .~(stage e a) :: .~al >.) al
              in
                mkrest (fun al -> .< .~f .~al >.) al
          | Pret, [] ->
              f
          | Pvoid, [] ->
              .< .~f () >.
          | _ ->
              raise (Error (args_err sg p.proc_name (List.length av)))
        in
          loop sg .< f >. av
      end
  | Capply (Clambda l, a) ->
      let e0 = e in
      let rec loop e args vals =
        match args, vals with
          [], [] ->
            stage e l.lam_body
        | [a], _ when l.lam_has_rest ->
            let rec mkrest cc = function
                [] -> cc .< Snull >.
              | v :: vals ->
                  mkrest (fun vals -> cc .< Spair { car = .~(stage e0 v); cdr = .~vals } >.) vals
            in
              mkrest (fun rest -> bind e a rest (fun e -> loop e [] [])) vals
        | a :: args, v :: vals ->
            bind e a (stage e0 v) (fun e -> loop e args vals)
        | _ ->
            raise (Error "apply: wrong number of arguments")
      in
        loop e l.lam_args a
  | Capply (c, a) ->
      .< let f = .~(stage e c) in
           .~begin
             let rec loop cc = function
                 [] -> cc .< [] >.
               | a :: al ->
                   loop (fun al -> cc .< .~(stage e a) :: .~al >.) al
             in
               loop
                 (fun al -> .< apply f .~al >.)
                 a
           end >.
  | Clambda { lam_has_rest = hr; lam_body = body; lam_args = args; lam_name = n } ->
      let rec scanargs cc = function
          [] ->
            cc.cc Pvoid
        | _ :: [] ->
            if hr then cc.cc Prest else cc.cc (Pfix Pret)
        | _ :: rest ->
            scanargs { cc = fun sg -> cc.cc (Pfix sg) } rest
      in
      let rec mkargs : type a. _ -> _ -> a sg -> a code = fun e largs sg ->
        match largs, sg with
          b :: largs, Pfix sg ->
            .< fun x ->
               .~(bind e b .< x >. (fun e -> mkargs e largs sg)) >.
        | [], Pret ->
            stage e body
        | a :: [], Prest ->
            .< fun x ->
               .~(bind e a .< list_of_caml x >.
                    (fun e -> stage e body)) >.
        | [], Pvoid ->
            .< fun () -> .~(stage e body) >.
        | _ ->
            assert false
      in
      let pf = scanargs { cc = fun sg -> .< Pf (sg, .~(mkargs e args sg)) >. } args in
      let proc_name = match n with None -> "#<unknown>" | Some n -> n in
        .< Sproc { proc_name; proc_fun = .~pf } >.
  | Cqqp (h, t) ->
      begin
        match h with
          Cqqspl x ->
            let findtl usl t =
              let rec loop =
                function
                  Spair ({ car = _; cdr = Snull } as p) ->
                    p.cdr <- t; usl
                | Spair { car = _; cdr = nt } -> loop nt
                | Snull -> t
                | _ -> raise (Error "unquote-splicing: not a list")
              in
                loop usl
            in
              .< findtl .~(stage e x) .~(stage e t) >.
        | _ ->
            .< Spair { car = .~(stage e h); cdr = .~(stage e t) } >.
      end
  | Cqqv v ->
      let n = List.length v in
        .< let qv = Array.make n Snull in
             .~begin
               let rec loop i =
                 function
                   [] ->
                     .< Svector qv >.
                 | v :: vl ->
                     .< let () = qv.(i) <- .~(stage e v) in .~(loop (i+1) vl) >.
               in
                 loop 0 v
             end >.
  | Cqqvs l ->
      begin
        let rec loop r =
          function
            [] ->
              .< Svector (Array.of_list .~r) >.
          | (Cqqspl x)::t ->
              loop .< (list_to_caml .~(stage e x)) @ .~r >. t
          | h::t ->
              loop .< .~(stage e h) :: .~r >. t
        in
          loop .< [] >. (List.rev l)
      end
  | Cqqspl x ->
      raise (Error "unquote-splicing: not valid here")
  | Ccond av ->
      let rec loop =
        function
          [] ->
            .< Sunspec >.
        | (Ccondspec c, b) :: al ->
            .< match .~(stage e c) with
                 Sfalse ->
                   .~(loop al)
               | _ as v ->
                   apply .~(stage e b) [ v ] >.
        | (c, b) :: al ->
            .< match .~(stage e c) with
                 Sfalse ->
                   .~(loop al)
               | _ ->
                   .~(stage e b) >.
      in
        loop av
  | Ccase (c, m) ->
      .< let v = .~(stage e c) in
           .~begin
             let rec loop =
               function
                 [] ->
                   .< Sunspec >.
               | ([], b) :: _ ->
                   stage e b
               | (mv, b) :: ml ->
                   let rec has =
                     function
                       [] ->
                         assert false
                     | mvv :: [] ->
                         .< mvv == v || test_eqv mvv v >.
                     | mvv :: mvvl ->
                         .< mvv == v || test_eqv mvv v || .~(has mvvl) >.
                   in
                     .< if .~(has mv) then
                          .~(stage e b)
                        else
                          .~(loop ml) >.
             in
               loop m
           end >.
  | Cdelay c ->
      .< Spromise (lazy .~(stage e c)) >.
  | Cparam (ps, c) ->
      let rec loop =
        function
          [] ->
            stage e c
        | (p, v) :: ps ->
            .< match .~(stage e p) with
                 Sparam _ as p ->
                   let_param p .~(stage e v) (fun () -> .~(loop ps))
               | _ ->
                   raise (Error "parametrize: bad args") >.
      in
        loop ps
  | _ ->
      raise (Error "stage: internal error")
;;

let stage c =
  stage [] c
;;

let load_file e name =
  let inp = Ocs_port.open_input_port name in
  let lex = Ocs_lex.make_lexer inp name in
  let rec loop () =
    match Ocs_read.read_expr lex with
      Seof -> ()
    | v ->
        let c = compile e v in
        let sc = stage c in
        let _ = Delimcc.push_prompt Ocs_contin.main_prompt (fun () -> Runcode.run sc) in
          loop ()
  in
    loop ()
;;

let load_prim e a =
  match a with
    Sstring name -> load_file e name; Sunspec
  | _ -> raise (Error "load: invalid name argument")
;;

let eval_prim expr e =
  match e with
    Sesym (e, _) ->
      let c = compile e expr in
      let sc = stage c in
        Runcode.run sc
  | _ -> raise (Error "eval: invalid args")
;;

let init e =
  set_pf1 e (load_prim e) "load";
  set_pf2 e eval_prim "eval";
;;
