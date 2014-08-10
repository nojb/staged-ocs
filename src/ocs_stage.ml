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

let rec doapply th (cc : sval -> unit) p av =
  match p with
    Sprim p
  | Sproc p ->
      let Pf (sg, f) = p.proc_fun in 
      let ret : type a. a ret -> a -> unit = fun r f ->
        match r with
          Rval ->
            cc f
        | Rcont ->
            f th cc
      in
      let rec loop : type a. a sg -> a -> _ -> unit = fun sg f al ->
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

let rec stage e th cc =
  function
    Cval v -> cc .< v >.
  | Cseq s ->
      let rec loop =
        function
          [] ->
            cc .< Sunspec >.
        | s :: [] ->
            stage e th cc s
        | s :: sl ->
            stage e th (fun v -> .< let _ = .~v in .~(loop sl) >.) s
      in
      loop s
  | Cand s ->
      .< let cc x = .~(cc .< x >.) in
           .~begin
             let rec loop =
               function
                 [] -> .< cc Strue >.
               | s :: [] ->
                   stage e th (fun x -> .< cc .~x >.) s
               | s :: sl ->
                   stage e th
                     (fun v ->
                        .< match .~v with
                             Sfalse -> cc Sfalse
                           | _ -> .~(loop sl) >.) s
             in
               loop s
           end >.
  | Cor s ->
      .< let cc x = .~(cc .< x >.) in
           .~begin
             let rec loop =
               function
                 [] -> .< cc Sfalse >.
               | s :: [] ->
                   stage e th (fun x -> .< cc .~x >.) s
               | s :: sl ->
                   stage e th
                     (fun v ->
                        .< match .~v with
                             Sfalse -> .~(loop sl)
                           | x -> cc x >.) s
             in
               loop s
           end >.
  | Cif (c, tx, fx) ->
      .< let cc x = .~(cc .< x >.) in
           .~(stage e th
                (fun v ->
                   .< match .~v with
                        Sfalse ->
                          .~(stage e th (fun x -> .< cc .~x >.) fx)
                      | _ ->
                          .~(stage e th (fun x -> .< cc .~x >.) tx) >.)
                c) >.
  | Csetg (g, c) ->
      stage e th
        (fun v ->
          let err = "set!: unbound variable " ^ (sym_name g.g_sym) in
            .< if g.g_val == Sunbound then
                 raise (Error err)
               else
                 let () = g.g_val <- .~v in .~(cc .< Sunspec >.) >.) c
  | Csetl (i, c) ->
      stage e th (fun v -> .< let () = .~(setl e i v) in .~(cc .< Sunspec >.) >.) c
  | Cdefine (g, c) ->
      stage e th (fun v -> .< let () = g.g_val <- .~v in .~(cc .< Sunspec >.) >.) c
  | Cgetg g ->
      let err = "unbound variable: " ^ (sym_name g.g_sym) in
        .< if g.g_val == Sunbound then
             raise (Error err)
           else
             .~(cc .< g.g_val >.) >.
  | Cgetl i -> cc (getl e i)
  | Capply (Cval (Sprim p), av) ->
      begin
        let Pf (sg, f) = p.proc_fun in
        let ret : type a. a ret -> a code -> unit code = fun r f ->
          match r with
            Rval ->
              cc f
          | Rcont ->
              .< .~f .~th (fun x -> .~(cc .< x >.)) >.
        in
        let rec loop : type a. a sg -> a code -> _ -> unit code = fun sg f al ->
          match sg, al with
            Pfix sg, a :: al ->
              stage e th (fun a -> loop sg .< .~f .~a >. al) a
          | Prest r, _ ->
              let rec mkrest cc = function
                  [] -> cc .< [] >.
                | a :: al ->
                    stage e th
                      (fun a ->
                        mkrest (fun al -> cc .< .~a :: .~al >.) al) a
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
            stage e th cc l.lam_body
        | [a], _ when l.lam_has_rest ->
            let rec mkrest cc = function
                [] -> cc .< Snull >.
              | v :: vals ->
                  stage e0 th
                    (fun v ->
                       mkrest (fun vals -> cc .< Spair { car = .~v; cdr = .~vals } >.) vals)
                    v
            in
              mkrest (fun rest -> bind e a rest (fun e -> loop e [] [])) vals
        | a :: args, v :: vals ->
            stage e0 th (fun v -> bind e a v (fun e -> loop e args vals)) v
        | _ ->
            raise (Error "apply: wrong number of arguments")
      in
        loop e l.lam_args a
  | Capply (c, a) ->
      stage e th
        (fun cv ->
          .< let f = .~cv in
               .~begin
                 let rec loop cc = function
                     [] -> cc .< [] >.
                   | a :: al ->
                       stage e th
                         (fun a ->
                           loop (fun al -> cc .< .~a :: .~al >.) al) a
                 in
                   loop
                     (fun al -> .< doapply .~th (fun x -> .~(cc .<x>.)) f .~al >.)
                     a
               end >.) c
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
            .< fun th cc ->
               .~(stage e .< th >. (fun x -> .< cc .~x >.) body) >.
        | a :: [], Prest Rcont ->
            .< fun x th cc ->
               .~(bind e a .< list_of_caml x >.
                    (fun e -> stage e .< th >. (fun x -> .< cc .~x >.) body)) >.
        | _ ->
            assert false
      in
      let pf = scanargs { cc = fun sg -> .< Pf (sg, .~(mkargs e args sg)) >. } args in
      let proc_name = match n with None -> "#<unknown>" | Some n -> n in
        cc .< Sproc { proc_name; proc_fun = .~pf } >.
  | Cqqp (h, t) ->
      begin
        match h with
          Cqqspl x ->
            stage e th (fun usl -> stage e th (fun t ->
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
                  cc .< findtl .~usl .~t >.) t) x
        | _ ->
            stage e th (fun h -> stage e th (fun t ->
              cc .< Spair { car = .~h; cdr = .~t } >.) t) h
      end
  | Cqqv v ->
      let n = List.length v in
        .< let qv = Array.make n Snull in
             .~begin
               let rec loop i =
                 function
                   [] -> cc .< Svector qv >.
                 | v :: vl ->
                     stage e th (fun x -> .< let () = qv.(i) <- .~x in .~(loop (i+1) vl) >.) v
               in
                 loop 0 v
             end >.
  | Cqqvs l ->
      begin
        let rec loop r =
          function
            [] -> cc .< Svector (Array.of_list .~r) >.
          | (Cqqspl x)::t ->
              stage e th (fun l -> loop .< (list_to_caml .~l) @ .~r >. t) x
          | h::t ->
              stage e th (fun x -> loop .< .~x :: .~r >. t) h
        in
          loop .< [] >. (List.rev l)
      end
  | Cqqspl x -> raise (Error "unquote-splicing: not valid here")
  | Ccond av ->
      .< let cc x = .~(cc .<x>.) in
           .~begin
             let rec loop =
               function
                 [] ->
                   .< cc Sunspec >.
               | (Ccondspec c, b) :: al ->
                   stage e th
                     (fun v ->
                        .< match .~v with
                             Sfalse -> .~(loop al)
                           | _ as v ->
                               .~(stage e th (fun b -> .< doapply .~th cc .~b [ v ] >.) b) >.)
                     c
               | (c, b) :: al ->
                   stage e th
                     (fun v ->
                        .< match .~v with
                             Sfalse -> .~(loop al)
                           | _ -> .~(stage e th (fun x -> .< cc .~x >.) b) >.) c
             in
               loop av
           end >.
  | Ccase (c, m) ->
      stage e th
        (fun v ->
           .< let cc x = .~(cc .< x >.) in
              let v = .~v in
                .~begin
                  let rec loop =
                    function
                      [] ->
                        .< cc Sunspec >.
                    | ([], b) :: _ ->
                        stage e th (fun x -> .< cc .~x >.) b
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
                               .~(stage e th (fun x -> .< cc .~x >.) b)
                             else
                               .~(loop ml) >.
                  in
                    loop m
                end >.) c
  | Cdelay c ->
      .< let p = let r = ref None in fun cc ->
           match !r with
             None ->
               (* TODO check if `th` should be somehow freed after forcing the promise . *)
               .~(stage e th (fun v ->
                   .< let v = .~v in
                        match !r with
                          None ->
                            let () = r := Some v in cc v
                        | Some v -> cc v >.) c)
           | Some v ->
               cc v
         in
           .~(cc .< Spromise p >.) >.
  | _ -> raise (Error "stage: internal error")
;;

let stage th cc c =
  stage [] th cc c
