(* Actual evaluator for the semi-compiled form.  *)

open Ocs_types
open Ocs_error
open Ocs_sym
open Ocs_misc

(* Local variables are stored either in th_frame or th_display.
   th_frame is the deepest frame, not yet part of the display.  *)

let getl th d i =
  if d >= Array.length th.th_display then
    th.th_frame.(i)
  else
    th.th_display.(d).(i)
;;

let setl th d i v =
  if d >= Array.length th.th_display then
    th.th_frame.(i) <- v
  else
    th.th_display.(d).(i) <- v
;;

let args_err p n =
  if p.proc_has_rest then
    Printf.sprintf "procedure %s expected %d or more args got %d"
      p.proc_name (p.proc_nargs - 1) n
  else
    Printf.sprintf "procedure %s expected %d args got %d"
      p.proc_name p.proc_nargs n

let chkargs p n =
  match p with
    Sproc (p, _) ->
      if n <> p.proc_nargs && (not p.proc_has_rest || n < p.proc_nargs - 1) then
        raise (Error (args_err p n))
      else
        ()
  | Sprim p ->
      if
        begin
          match p.prim_fun with
            Pf0 _ -> n = 0
          | Pf1 _ -> n = 1
          | Pf2 _ -> n = 2
          | Pf3 _ -> n = 3
          | Pfn _ | Pfcn _ -> true
        end
      then
        ()
      else
        raise (Error (p.prim_name ^ ": wrong number of arguments"))
  | _ -> raise (Error "apply: not a procedure or primitive")
;;

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

let rec stage th cc =
  function
    Cval v -> cc .< v >.
  | Cseq2 (s1, s2) ->
      stage th cc (Cseqn [| s1; s2 |])
  | Cseq3 (s1, s2, s3) ->
      stage th cc (Cseqn [| s1; s2; s3 |])
  | Cseqn s ->
      let n = Array.length s in
        let rec loop i =
          if i = n - 1 then
            stage th cc s.(i)
          else
            stage th (fun v -> .< let _ = .~v in .~(loop (i + 1)) >.) s.(i)
        in
          loop 0
  | Cand2 (s1, s2) ->
      stage th cc (Candn [| s1; s2 |])
  | Cand3 (s1, s2, s3) ->
      stage th cc (Candn [| s1; s2; s3 |])
  | Candn s ->
      let n = Array.length s in
        .< let cc x = .~(cc .< x >.) in
             .~begin
               let rec loop i =
                 begin
                   if i = n - 1 then
                     stage th (fun x -> .< cc .~x >.) s.(i)
                   else
                     stage th
                       (fun v ->
                          .< match .~v with
                               Sfalse -> cc Sfalse
                             | _ -> .~(loop (i + 1)) >.)
                       s.(i)
                 end
               in
                 loop 0
             end >.
  | Cor2 (s1, s2) ->
      stage th cc (Corn [| s1; s2 |])
  | Cor3 (s1, s2, s3) ->
      stage th cc (Corn [| s1; s2; s3 |])
  | Corn s ->
      let n = Array.length s in
        .< let cc x = .~(cc .< x >.) in
             .~begin
               let rec loop i =
                 if i = n - 1 then
                   stage th (fun x -> .< cc .~x >.) s.(i)
                 else
                   stage th
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
           .~(stage th
                (fun v ->
                   .< match .~v with
                        Sfalse -> .~(stage th (fun x -> .< cc .~x >.) fx)
                      | _ -> .~(stage th (fun x -> .< cc .~x >.) tx) >.)
                c) >.
  (* | Csetg (g, c) -> *)
  (*     eval th (fun v -> *)
  (*       if g.g_val == Sunbound then *)
  (*         raise (Error ("set!: unbound variable: " ^ (sym_name g.g_sym))) *)
  (*       else *)
  (*         g.g_val <- v; cc Sunspec) c *)
  (* | Csetl (d, i, c) -> *)
  (*     eval th (fun v -> setl th d i v; cc Sunspec) c *)
  (* | Cdefine (g, c) -> *)
  (*     eval th (fun v -> g.g_val <- v; cc Sunspec) c *)
  (* | Cgetg g -> *)
  (*     if g.g_val == Sunbound then *)
  (*       raise (Error ("unbound variable: " ^ (sym_name g.g_sym))) *)
  (*     else *)
  (*       cc g.g_val *)
  (* | Cgetl (d, i) -> cc (getl th d i) *)
  (* | Capply0 c -> *)
  (*     eval th (fun cv -> *)
  (*       chkargs cv 0; *)
  (*       match cv with *)
  (*         Sproc (p, d) -> doapply th cc p d [| |] *)
  (*       | Sprim p -> *)
  (*           begin *)
  (*             match p.prim_fun with *)
  (*               Pf0 f -> cc (f ()) *)
  (*             | Pfn f -> cc (f [| |]) *)
  (*             | Pfcn f -> f th cc [| |] *)
  (*             | _ -> assert false *)
  (*           end *)
  (*       | _ -> assert false) c *)
  (* | Capply1 (c, a1) -> *)
  (*     eval th (fun cv -> eval th (fun a1v -> *)
  (*       chkargs cv 1; *)
  (*       match cv with *)
  (*         Sproc (p, d) -> doapply th cc p d [| a1v |] *)
  (*       | Sprim p -> *)
  (*           begin *)
  (*             match p.prim_fun with *)
  (*               Pf1 f -> cc (f a1v) *)
  (*             | Pfn f -> cc (f [| a1v |]) *)
  (*             | Pfcn f -> f th cc [| a1v |] *)
  (*             | _ -> assert false *)
  (*           end *)
  (*       | _ -> assert false) a1) c *)
  (* | Capply2 (c, a1, a2) -> *)
  (*     eval th (fun cv -> eval th (fun a1v -> eval th (fun a2v -> *)
  (*       chkargs cv 2; *)
  (*       match cv with *)
  (*         Sproc (p, d) -> doapply th cc p d [| a1v; a2v |] *)
  (*       | Sprim p -> *)
  (*           begin *)
  (*             match p.prim_fun with *)
  (*               Pf2 f -> cc (f a1v a2v) *)
  (*             | Pfn f -> cc (f [| a1v; a2v |]) *)
  (*             | Pfcn f -> f th cc [| a1v; a2v |] *)
  (*             | _ -> assert false *)
  (*           end *)
  (*       | _ -> assert false) a2) a1) c *)
  (* | Capply3 (c, a1, a2, a3) -> *)
  (*     eval th (fun cv -> eval th (fun a1v -> eval th (fun a2v -> *)
  (*       eval th (fun a3v -> *)
  (*         chkargs cv 3; *)
  (*         match cv with *)
  (*           Sproc (p, d) -> doapply th cc p d [| a1v; a2v; a3v |] *)
  (*         | Sprim p -> *)
  (*             begin *)
  (*               match p.prim_fun with *)
  (*                 Pf3 f -> cc (f a1v a2v a3v) *)
  (*               | Pfn f -> cc (f [| a1v; a2v; a3v |]) *)
  (*               | Pfcn f -> f th cc [| a1v; a2v; a3v |] *)
  (*               | _ -> assert false *)
  (*             end *)
  (*         | _ -> assert false) a3) a2) a1) c *)
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
  (* | Clambda p -> *)
  (*     let n = th.th_depth + 1 in *)
  (*     let nd = Array.init n *)
  (*       (fun i -> if i < n - 1 then th.th_display.(i) *)
  (*                 else th.th_frame) *)
  (*     in *)
  (*       cc (Sproc (p, nd)) *)
  | Cqqp (h, t) ->
      begin
        match h with
          Cqqspl x ->
            stage th (fun usl -> stage th (fun t ->
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
            stage th (fun h -> stage th (fun t ->
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
                   stage th (fun x -> .< let () = qv.(i) <- .~x in .~(loop (i + 1)) >.) v.(i)
               in
                 loop 0
             end >.
  | Cqqvs l ->
      begin
        let rec loop r =
          function
            [] -> cc .< Svector (Array.of_list .~r) >.
          | (Cqqspl x)::t ->
              stage th (fun l -> loop .< (list_to_caml .~l) @ .~r >. t) x
          | h::t ->
              stage th (fun x -> loop .< .~x :: .~r >. t) h
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
      stage th
        (fun v ->
           let n = Array.length m in
             .< let cc x = .~(cc .< x >.) in
                let v = .~v in
                  .~begin
                    let rec loop i =
                      if i < n then
                        begin
                          match m.(i) with
                            ([| |], b) -> stage th (fun x -> .< cc .~x >.) b
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
                                .< if .~(has 0) then .~(stage th (fun x -> .< cc .~x >.) b)
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

