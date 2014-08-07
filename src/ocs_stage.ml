(* Actual evaluator for the semi-compiled form.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc

(* Local variables are stored either in th_frame or th_display.
   th_frame is the deepest frame, not yet part of the display.  *)

let getl e i =
  Printf.eprintf "getl: i=%d l=%d\n%!" i (List.length e);
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
  | Pcont -> false
  | Pret -> false
  | Pvoid sg -> proc_has_rest sg
;;

let rec proc_nargs : type a. a sg -> int = function
    Pfix sg -> 1 + proc_nargs sg
  | Prest _ -> 1
  | Pcont -> 0
  | Pret -> 0
  | Pvoid sg -> proc_nargs sg
;;

(* let args_err p n = *)
(*   if p.proc_has_rest then *)
(*     Printf.sprintf "procedure %s expected %d or more args got %d" *)
(*       p.proc_name (p.proc_nargs - 1) n *)
(*   else *)
(*     Printf.sprintf "procedure %s expected %d args got %d" *)
(*       p.proc_name p.proc_nargs n *)

(* let chkargs p n = *)
(*   match p with *)
(*     Sproc (p, _) -> *)
(*       if n <> p.proc_nargs && (not p.proc_has_rest || n < p.proc_nargs - 1) then *)
(*         raise (Error (args_err p n)) *)
(*       else *)
(*         () *)
(*   | Sprim p -> *)
(*       if *)
(*         begin *)
(*           match p.prim_fun with *)
(*             Pf0 _ -> n = 0 *)
(*           | Pf1 _ -> n = 1 *)
(*           | Pf2 _ -> n = 2 *)
(*           | Pf3 _ -> n = 3 *)
(*           | Pfn _ | Pfcn _ -> true *)
(*         end *)
(*       then *)
(*         () *)
(*       else *)
(*         raise (Error (p.prim_name ^ ": wrong number of arguments")) *)
(*   | _ -> raise (Error "apply: not a procedure or primitive") *)
(* ;; *)

(* let rec doapply th cc p disp av = *)
(*   let th = { *)
(*     th with *)
(*     th_frame = Array.make p.proc_frame_size Seof; *)
(*     th_display = disp; *)
(*     th_depth = Array.length disp } *)
(*   in *)
(*     if p.proc_has_rest then *)
(*       begin *)
(*         let nfixed = p.proc_nargs - 1 *)
(*         and n = Array.length av in *)
(*           if nfixed > 0 then *)
(*             Array.blit av 0 th.th_frame 0 nfixed; *)
(*           let rec mkrest i r = *)
(*             if i < nfixed then r *)
(*             else mkrest (i - 1) (Spair { car = av.(i); cdr = r }) *)
(*           in *)
(*             th.th_frame.(nfixed) <- mkrest (n - 1) Snull *)
(*       end *)
(*     else *)
(*       Array.blit av 0 th.th_frame 0 p.proc_nargs; *)
(*     eval th cc p.proc_body *)

let rec stage e cc =
  function
    Cval v -> cc .< v >.
  | Cseq [| |] ->
      cc .< Sunspec >.
  | Cseq s ->
      let n = Array.length s in
        let rec loop i =
          if i = n - 1 then
            stage e cc s.(i)
          else
            stage e (fun v -> .< let _ = .~v in .~(loop (i + 1)) >.) s.(i)
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
                     stage e (fun x -> .< cc .~x >.) s.(i)
                   else
                     stage e
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
                   stage e (fun x -> .< cc .~x >.) s.(i)
                 else
                   stage e
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
           .~(stage e
                (fun v ->
                   .< match .~v with
                        Sfalse -> .~(stage e (fun x -> .< cc .~x >.) fx)
                      | _ -> .~(stage e (fun x -> .< cc .~x >.) tx) >.)
                c) >.
  | Csetg (g, c) ->
      stage e (fun v ->
          let err = "set!: unbound variable " ^ (sym_name g.g_sym) in
            .< if g.g_val == Sunbound then
                 raise (Error err)
               else
                 let () = g.g_val <- .~v in .~(cc .< Sunspec >.) >.) c
  | Csetl (i, c) ->
      stage e (fun v -> .< let () = .~(setl e i v) in .~(cc .< Sunspec >.) >.) c
  | Cdefine (g, c) ->
      stage e (fun v -> .< let () = g.g_val <- .~v in .~(cc .< Sunspec >.) >.) c
  | Cgetg g ->
      let err = "unbound variable: " ^ (sym_name g.g_sym) in
        .< if g.g_val == Sunbound then
             raise (Error err)
           else
             .~(cc .< g.g_val >.) >.
  | Cgetl i -> cc (getl e i)
  (* | Capplyn (c, a) -> *)
  (*     eval th (fun cv -> *)
  (*       let n = Array.length a in *)
  (*       let av = Array.make n Snull in *)
  (*       let rec loop i = *)
  (*         if i = n then *)
  (*           begin *)
  (*             chkargs cv n; *)
  (*             match cv with *)
  (*               Sproc (p, d) -> doapply th cc p d av *)
  (*             | Sprim p -> *)
  (*                 begin *)
  (*                   match p.prim_fun with *)
  (*                     Pfn f -> cc (f av) *)
  (*                   | Pfcn f -> f th cc av *)
  (*                   | _ -> assert false *)
  (*                 end *)
  (*             | _ -> assert false *)
  (*           end *)
  (*         else *)
  (*           eval th (fun x -> av.(i) <- x; loop (i + 1)) a.(i) *)
  (*       in *)
  (*         loop 0) c *)
  | Clambda l ->
      let is_mutable = function
          Vloc l -> l.l_mut
        | Vglob _ -> true
        | _ -> false
      in
      let rec loop cc = function
          [] -> cc.cc Pcont
        | [_] when l.lam_has_rest -> cc.cc (Prest Pcont)
        | _ :: rest -> loop { cc = fun sg -> cc.cc (Pfix sg) } rest
      in
      let rec mkargs : type a. _ -> _ -> a sg -> a code = fun e largs sg ->
        match largs, sg with
          b :: largs, Pfix sg ->
            if is_mutable b then
              .< fun x -> let x = ref x in .~(mkargs (`M .<x>. :: e) largs sg) >.
            else
              .< fun x -> .~(mkargs (`I .<x>. :: e) largs sg) >.
        | [], Pcont ->
            .< fun cc -> .~(stage e (fun x -> .< cc .~x >.) l.lam_body) >.
        | [a], Prest Pcont ->
            assert false
            (* if is_mutable a then *)
            (*   .< fun x cc -> let x = ref x in .~(stage (`M .<x>. :: e) (fun x -> .< cc .~x >.) l.lam_body) >. *)
            (* else *)
            (*   .< fun x cc -> .~(stage (`I .<x>. :: e) (fun x -> .< cc .~x >.) l.lam_body) >. *)
        | _ ->
            assert false
      in
      let pf = loop { cc = fun sg -> .< Pf (sg, .~(mkargs e l.lam_args sg)) >. } l.lam_args in
        cc .< Sproc { proc_name = l.lam_name; proc_is_prim = false; proc_fun = .~pf } >.
  | Cqqp (h, t) ->
      begin
        match h with
          Cqqspl x ->
            stage e (fun usl -> stage e (fun t ->
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
            stage e (fun h -> stage e (fun t ->
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
                   stage e (fun x -> .< let () = qv.(i) <- .~x in .~(loop (i + 1)) >.) v.(i)
               in
                 loop 0
             end >.
  | Cqqvs l ->
      begin
        let rec loop r =
          function
            [] -> cc .< Svector (Array.of_list .~r) >.
          | (Cqqspl x)::t ->
              stage e (fun l -> loop .< (list_to_caml .~l) @ .~r >. t) x
          | h::t ->
              stage e (fun x -> loop .< .~x :: .~r >. t) h
        in
          loop .< [] >. (List.rev l)
      end
  | Cqqspl x -> raise (Error "unquote-splicing: not valid here")
  (* | Ccond av -> *)
  (*     begin *)
  (*       let n = Array.length av in *)
  (*       let rec loop i = *)
  (*         if i < n then *)
  (*           begin *)
  (*             match av.(i) with *)
  (*               (Ccondspec c, b) -> *)
  (*                 eval th (fun v -> *)
  (*                   if v <> Sfalse then eval th cc (Capply1 (b, Cval v)) *)
  (*                   else loop (i + 1)) c *)
  (*             | (c, b) -> *)
  (*                 eval th (fun v -> *)
  (*                   if v <> Sfalse then eval th cc b *)
  (*                   else loop (i + 1)) c *)
  (*           end *)
  (*         else *)
  (*           cc Sunspec *)
  (*       in *)
  (*         loop 0 *)
  (*     end *)
  | Ccase (c, m) ->
      stage e
        (fun v ->
           let n = Array.length m in
             .< let cc x = .~(cc .< x >.) in
                let v = .~v in
                  .~begin
                    let rec loop i =
                      if i < n then
                        begin
                          match m.(i) with
                            ([| |], b) -> stage e (fun x -> .< cc .~x >.) b
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
                                .< if .~(has 0) then .~(stage e (fun x -> .< cc .~x >.) b)
                                   else .~(loop (i + 1)) >.
                        end
                      else
                        .< cc Sunspec >.
                    in
                      loop 0
                  end >.) c
  (* | Cdelay c -> *)
  (*     cc (Spromise { promise_code = c; *)
  (*                    promise_val = None; *)
  (*                    promise_th = Some { th with th_frame = th.th_frame } }) *)
  | _ -> raise (Error "stage: internal error")
;;

