(* Actual evaluator for the semi-compiled form.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc

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
  | Prests _ -> true
  | Pcont -> false
  | Pret -> false
  | Pvoid sg -> proc_has_rest sg
  | Pthread sg -> proc_has_rest sg
;;

let rec proc_nargs : type a. a sg -> int = function
    Pfix sg -> 1 + proc_nargs sg
  | Prest _ -> 1
  | Prests _ -> 1
  | Pcont -> 0
  | Pret -> 0
  | Pvoid sg -> proc_nargs sg
  | Pthread sg -> proc_nargs sg
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
    Sproc p ->
      let Pf (sg, f) = p.proc_fun in 
      let rec loop : type a. a sg -> a -> _ -> unit = fun sg f al ->
        match sg, al with
          Pfix sg, a :: al ->
            loop sg (f a) al
        | Pret, [] ->
            cc f
        | Pcont, [] ->
            f cc
        | Prests sg, _ ->
            let rec mkrest = function
                [] -> Snull
              | a :: al -> Spair { car = a; cdr = mkrest al }
            in
              loop sg (f (mkrest al)) []
        | Prest sg, _ ->
            loop sg (f (Array.of_list al)) []
        | Pvoid sg, _ ->
            loop sg (f ()) al
        | Pcont, _ :: _ ->
            raise (Error (args_err sg p.proc_name (List.length av)))
        | Pret, _ :: _ ->
            raise (Error (args_err sg p.proc_name (List.length av)))
        | Pfix _, [] ->
            raise (Error (args_err sg p.proc_name (List.length av)))
        | Pthread sg, _ ->
            loop sg (f th) al
      in
        loop sg f av
  | _ ->
      raise (Error "apply: not a procedure or primitive")

let rec stage e th cc =
  function
    Cval v -> cc .< v >.
  | Cseq [| |] ->
      cc .< Sunspec >.
  | Cseq s ->
      let n = Array.length s in
        let rec loop i =
          if i = n - 1 then
            stage e th cc s.(i)
          else
            stage e th (fun v -> .< let _ = .~v in .~(loop (i + 1)) >.) s.(i)
        in
          loop 0
  | Cand [| |] ->
      cc .< Strue >.
  | Cand s ->
      let n = Array.length s in
        .< let cc x = .~(cc .< x >.) in
             .~begin
               let rec loop i =
                 begin
                   if i = n - 1 then
                     stage e th (fun x -> .< cc .~x >.) s.(i)
                   else
                     stage e th
                       (fun v ->
                          .< match .~v with
                               Sfalse -> cc Sfalse
                             | _ -> .~(loop (i + 1)) >.)
                       s.(i)
                 end
               in
                 loop 0
             end >.
  | Cor [| |] ->
      cc .< Sfalse >.
  | Cor s ->
      let n = Array.length s in
        .< let cc x = .~(cc .< x >.) in
             .~begin
               let rec loop i =
                 if i = n - 1 then
                   stage e th (fun x -> .< cc .~x >.) s.(i)
                 else
                   stage e th
                     (fun v ->
                        .< match .~v with
                             Sfalse -> .~(loop (i + 1))
                           | x -> cc x >.)
                     s.(i)
               in
                 loop 0
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
  | Capply (Cval (Sproc p), av) ->
      begin
        let Pf (sg, f) = p.proc_fun in 
        let rec loop : type a. a sg -> a code -> _ -> unit code = fun sg f al ->
          match sg, al with
            Pfix sg, a :: al ->
              stage e th (fun a -> loop sg .< .~f .~a >. al) a
          | Pret, [] ->
              cc f
          | Pcont, [] ->
              .< .~f (fun x -> .~(cc .< x >.)) >.
          | Prests sg, _ ->
              let rec mkrest cc = function
                  [] -> cc .< Snull >.
                | a :: al ->
                    stage e th
                      (fun a ->
                         mkrest
                           (fun al -> cc .< Spair { car = .~a; cdr = .~al } >.) al) a
              in
                mkrest (fun al -> loop sg .< .~f .~al >. []) al
          | Prest sg, _ ->
              let rec mkrest cc = function
                  [] -> cc .< [] >.
                | a :: al ->
                    stage e th (fun a -> mkrest (fun al -> cc .< .~a :: .~al >.) al) a
              in
                mkrest (fun al -> loop sg .< .~f (Array.of_list .~al) >. []) al
          | Pvoid sg, _ ->
              loop sg .< .~f () >. al
          | Pcont, _ :: _ ->
              raise (Error (args_err sg p.proc_name (Array.length av)))
          | Pret, _ :: _ ->
              raise (Error (args_err sg p.proc_name (Array.length av)))
          | Pfix _, [] ->
              raise (Error (args_err sg p.proc_name (Array.length av)))
          | Pthread sg, _ ->
              loop sg .< .~f .~th >. al
        in
          loop sg .< f >. (Array.to_list av)
      end
  | Capply (Clambda l, a) ->
      let rec loop e args vals =
        match args, vals with
          [], [] ->
            stage e th cc l.lam_body
        | [a], _ when l.lam_has_rest ->
            let rec mkrest cc = function
                [] -> cc .< Snull >.
              | v :: vals ->
                  stage e th
                    (fun v ->
                       mkrest (fun vals -> cc .< Spair { car = .~v; cdr = .~vals } >.) vals)
                    v
            in
              mkrest (fun rest ->
                  if Ocs_env.is_mutable a then
                    .< let x = ref .~rest in .~(loop (`M .< x >. :: e) [] []) >.
                  else
                    .< let x = .~rest in .~(loop (`I .< x >. :: e) [] []) >.) vals
        | a :: args, v :: vals ->
            if Ocs_env.is_mutable a then
              stage e th (fun v -> .< let x = ref .~v in .~(loop (`M .< x >. :: e) args vals) >.) v
            else
              stage e th (fun v -> .< let x = .~v in .~(loop (`I .< x >. :: e) args vals) >.) v
        | _ ->
            raise (Error "apply: wrong number of arguments")
      in
        loop e l.lam_args (Array.to_list a)
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
                     (Array.to_list a)
               end >.) c
  | Clambda l ->
      let rec loop cc = function
          [] -> cc.cc (Pthread Pcont)
        | [_] when l.lam_has_rest -> cc.cc (Prests (Pthread Pcont))
        | _ :: rest -> loop { cc = fun sg -> cc.cc (Pfix sg) } rest
      in
      let rec mkargs : type a. _ -> _ -> a sg -> a code = fun e largs sg ->
        match largs, sg with
          b :: largs, Pfix sg ->
            if Ocs_env.is_mutable b then
              .< fun x -> let x = ref x in .~(mkargs (`M .<x>. :: e) largs sg) >.
            else
              .< fun x -> .~(mkargs (`I .<x>. :: e) largs sg) >.
        | [], Pthread Pcont ->
            .< fun th cc -> .~(stage e .< th >. (fun x -> .< cc .~x >.) l.lam_body) >.
        | [a], Prests (Pthread Pcont) ->
            if Ocs_env.is_mutable a then
              .< fun x th cc ->
                 let x = ref x in
                   .~(stage (`M .<x>. :: e) .< th >. (fun x -> .< cc .~x >.) l.lam_body) >.
            else
              .< fun x th cc ->
                 .~(stage (`I .<x>. :: e) .< th >. (fun x -> .< cc .~x >.) l.lam_body) >.
        | _ ->
            assert false
      in
      let pf = loop { cc = fun sg -> .< Pf (sg, .~(mkargs e l.lam_args sg)) >. } l.lam_args in
        cc .< Sproc { proc_name = l.lam_name; proc_is_prim = false; proc_fun = .~pf } >.
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
      let n = Array.length v in
        .< let qv = Array.make n Snull in
             .~begin
               let rec loop i =
                 if i = n then
                   cc .< Svector qv >.
                 else
                   stage e th
                     (fun x -> .< let () = qv.(i) <- .~x in .~(loop (i + 1)) >.) v.(i)
               in
                 loop 0
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
      let n = Array.length av in
        .< let cc x = .~(cc .<x>.) in
             .~begin
               let rec loop i =
                 if i < n then
                   begin
                     match av.(i) with
                       (Ccondspec c, b) ->
                         stage e th
                           (fun v ->
                             .< match .~v with
                                  Sfalse -> .~(loop (i+1))
                                | _ as v ->
                                    .~(stage e th (fun b -> .< doapply .~th cc .~b [ v ] >.) b) >.)
                           c
                     | (c, b) ->
                         stage e th
                           (fun v ->
                             .< match .~v with
                                  Sfalse -> .~(loop (i+1))
                                | _ -> .~(stage e th (fun x -> .< cc .~x >.) b) >.) c
                   end
                 else
                   .< cc Sunspec >.
               in
                 loop 0
             end >.
  | Ccase (c, m) ->
      stage e th
        (fun v ->
           let n = Array.length m in
             .< let cc x = .~(cc .< x >.) in
                let v = .~v in
                  .~begin
                    let rec loop i =
                      if i < n then
                        begin
                          match m.(i) with
                            ([| |], b) -> stage e th (fun x -> .< cc .~x >.) b
                          | (mv, b) ->
                              let n = Array.length mv in
                              let rec has i =
                                let mvv = mv.(i) in
                                  if i < n - 1 then
                                    begin
                                      let mvv = mv.(i) in
                                        .< mvv == v || test_eqv mvv v || .~(has (i+1)) >.
                                    end
                                  else
                                    .< mvv == v || test_eqv mvv v >.
                              in
                                .< if .~(has 0) then .~(stage e th (fun x -> .< cc .~x >.) b)
                                   else .~(loop (i + 1)) >.
                        end
                      else
                        .< cc Sunspec >.
                    in
                      loop 0
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

