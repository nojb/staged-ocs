(* Actual evaluator for the semi-compiled form.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc

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

let rec doapply th p av =
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
  | _ ->
      raise (Error "apply: not a procedure or primitive")

  (* This is necessary to pass a function ('a. 'a sg -> 'b) as an argument, see
     the case of [Clambda] in [Ocs_stage.stage] *)
type 'b slambda_c =
  {
    cc : 'a. 'a sg -> 'b
  }

let rec stage e th =
  function
    Cval v -> .< v >.
  | Cseq s ->
      let rec loop =
        function
          [] ->
            .< Sunspec >.
        | s :: [] ->
            stage e th s
        | s :: sl ->
            .< let _ = .~(stage e th s) in .~(loop sl) >.
      in
        loop s
  | Cand s ->
      let rec loop =
        function
          [] -> .< Strue >.
        | s :: [] ->
            stage e th s
        | s :: sl ->
            .< match .~(stage e th s) with
                 Sfalse -> Sfalse
               | _ -> .~(loop sl) >.
      in
        loop s
  | Cor s ->
      let rec loop =
        function
          [] -> .< Sfalse >.
        | s :: [] ->
            stage e th s
        | s :: sl ->
            .< match .~(stage e th s) with
                 Sfalse -> .~(loop sl)
               | _ as x -> x >.
      in
        loop s
  | Cif (c, tx, fx) ->
      .< match .~(stage e th c) with
           Sfalse -> .~(stage e th fx)
         | _ -> .~(stage e th tx) >.
  | Csetg (g, c) ->
      let err = "set!: unbound variable " ^ (sym_name g.g_sym) in
        .< if g.g_val == Sunbound then
             raise (Error err)
           else
             let () = g.g_val <- .~(stage e th c) in Sunspec >.
  | Csetl (i, c) ->
      .< let () = .~(setl e i (stage e th c)) in Sunspec >.
  | Cdefine (g, c) ->
      .< let () = g.g_val <- .~(stage e th c) in Sunspec >.
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
        let ret : type a. a ret -> a code -> sval code = fun r f ->
          match r with
            Rval ->
              f
          | Rcont ->
              .< .~f .~th >.
        in
        let rec loop : type a. a sg -> a code -> _ -> sval code = fun sg f al ->
          match sg, al with
            Pfix sg, a :: al ->
              loop sg .< .~f .~(stage e th a) >. al
          | Prest r, _ ->
              let rec mkrest cc = function
                  [] -> cc .< [] >.
                | a :: al ->
                    mkrest (fun al -> cc .< .~(stage e th a) :: .~al >.) al
              in
                mkrest (fun al -> ret r .< .~f .~al >.) al
          | Pret r, [] ->
              ret r f
          | Pvoid r, [] ->
              ret r .< .~f () >.
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
            stage e th l.lam_body
        | [a], _ when l.lam_has_rest ->
            let rec mkrest cc = function
                [] -> cc .< Snull >.
              | v :: vals ->
                  mkrest (fun vals -> cc .< Spair { car = .~(stage e0 th v); cdr = .~vals } >.) vals
            in
              mkrest (fun rest -> bind e a rest (fun e -> loop e [] [])) vals
        | a :: args, v :: vals ->
            bind e a (stage e0 th v) (fun e -> loop e args vals)
        | _ ->
            raise (Error "apply: wrong number of arguments")
      in
        loop e l.lam_args a
  | Capply (c, a) ->
      .< let f = .~(stage e th c) in
           .~begin
             let rec loop cc = function
                 [] -> cc .< [] >.
               | a :: al ->
                   loop (fun al -> cc .< .~(stage e th a) :: .~al >.) al
             in
               loop
                 (fun al -> .< doapply .~th f .~al >.)
                 a
           end >.
  | Clambda { lam_has_rest = hr; lam_body = body; lam_args = args; lam_name = n } ->
      let rec scanargs cc = function
          [] -> cc.cc (Pret Rcont)
        | _ :: [] when hr -> cc.cc (Prest Rcont)
        | _ :: rest -> scanargs { cc = fun sg -> cc.cc (Pfix sg) } rest
      in
      let rec mkargs : type a. _ -> _ -> a sg -> a code = fun e largs sg ->
        match largs, sg with
          b :: largs, Pfix sg ->
            .< fun x ->
               .~(bind e b .< x >. (fun e -> mkargs e largs sg)) >.
        | [], Pret Rcont ->
            .< fun th ->
               .~(stage e .< th >. body) >.
        | a :: [], Prest Rcont ->
            .< fun x th ->
               .~(bind e a .< list_of_caml x >.
                    (fun e -> stage e .< th >. body)) >.
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
              .< findtl .~(stage e th x) .~(stage e th t) >.
        | _ ->
            .< Spair { car = .~(stage e th h); cdr = .~(stage e th t) } >.
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
                     .< let () = qv.(i) <- .~(stage e th v) in .~(loop (i+1) vl) >.
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
              loop .< (list_to_caml .~(stage e th x)) @ .~r >. t
          | h::t ->
              loop .< .~(stage e th h) :: .~r >. t
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
            .< match .~(stage e th c) with
                 Sfalse ->
                   .~(loop al)
               | _ as v ->
                   doapply .~th .~(stage e th b) [ v ] >.
        | (c, b) :: al ->
            .< match .~(stage e th c) with
                 Sfalse ->
                   .~(loop al)
               | _ ->
                   .~(stage e th b) >.
      in
        loop av
  | Ccase (c, m) ->
      .< let v = .~(stage e th c) in
           .~begin
             let rec loop =
               function
                 [] ->
                   .< Sunspec >.
               | ([], b) :: _ ->
                   stage e th b
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
                          .~(stage e th b)
                        else
                          .~(loop ml) >.
             in
               loop m
           end >.
  | Cdelay c ->
      .< let p = let r = ref None in fun () ->
           match !r with
             None ->
               (* TODO check if `th` should be somehow freed after forcing the promise . *)
               begin
                 let v = .~(stage e th c) in
                   match !r with
                     None ->
                       (r := Some v; v)
                   | Some v ->
                       v
               end
           | Some v ->
               v
         in
           Spromise p >.
  | _ ->
      raise (Error "stage: internal error")
;;

let stage th c =
  stage [] th c
