(* Continuations *)

open Ocs_types
open Ocs_error
open Ocs_prim
open Ocs_env
open Ocs_misc

  (* Dynamic extents are associated with threads and continuations.  *)
type dynext =
  {
    dynext_parent : dynext option;
    dynext_depth : int;
    dynext_before : unit -> sval;
    dynext_after : unit -> sval
  }

let winders : dynext option ref = ref None

let rec find_depth fdx tdx al bl =
  match (fdx, tdx) with
    (Some f, Some t) ->
      if f.dynext_parent == t.dynext_parent then
        (List.rev (f.dynext_after::al), t.dynext_before::bl)
      else if f.dynext_depth > t.dynext_depth then
        find_depth f.dynext_parent tdx (f.dynext_after::al) bl
      else if f.dynext_depth < t.dynext_depth then
        find_depth fdx t.dynext_parent al (t.dynext_before::bl)
      else
        find_depth f.dynext_parent t.dynext_parent
          (f.dynext_after::al) (t.dynext_before::bl)
  | (Some f, None) ->
      find_depth f.dynext_parent tdx (f.dynext_after::al) bl
  | (None, Some t) ->
      find_depth fdx t.dynext_parent al (t.dynext_before::bl)
  | _ -> (List.rev al, bl)
;;

(* Change from the dynamic extent fdx to the dynamic extent tdx *)
let dxswitch fdx tdx =
  if not (fdx == tdx) then
    let (al, bl) = find_depth fdx tdx [] [] in
    let rec bloop =
      function
        [] -> ()
      | h::t -> let _ = h () in bloop t
    in
    let rec aloop =
      function
        [] -> bloop bl
      | h::t -> let _ = h () in aloop t
    in
      aloop al
;;

let main_prompt =
  Delimcc.new_prompt ()
;;

let continuation dx cc =
  function
    [ x ] ->
      let () = dxswitch !winders dx in
        Delimcc.abort main_prompt (cc x)
  | av ->
      let () = dxswitch !winders dx in
        Delimcc.abort main_prompt (cc (Svalues av))
;;

(* [call/cc] in terms of [delimcc]:

   (define (call/cc f) (control (lambda (k) (k (f (lambda (v) (abort (k v))))))))

   See "Control Delimiters and their Hierarchies", p. 75, Sitaram, Felleisen, 1990. *)

let call_cc proc =
  let cont cc =
    Sproc { proc_name = "<continuation>";
            proc_fun = Pf (Prest, continuation !winders cc) }
  in
    Delimcc.control main_prompt
      (fun cc -> cc (apply proc [ cont cc ]))
;;

let values =
  function
    [ x ] -> x
  | av -> Svalues av
;;

let call_values producer consumer =
  match apply producer [] with
    Svalues av ->
      apply consumer av
  | x ->
      apply consumer [x]
;;

let dynamic_wind before thunk after =
  let _ = apply before [] in
  let oldw = !winders in
  let ndx = {
    dynext_parent = oldw;
    dynext_depth =
      (match oldw with
         None -> 0
       | Some dx -> dx.dynext_depth + 1);
    dynext_before = (fun () -> apply before []);
    dynext_after = (fun () -> apply after [])
  } in
  winders := Some ndx;
  let res = apply thunk [] in
    winders := oldw;
    let _ = apply after [] in
      res
;;

let init e =
  set_pf1 e call_cc "call-with-current-continuation";
  set_pf1 e call_cc "call/cc";

  set_pfn e values "values";

  set_pf2 e call_values "call-with-values";
  set_pf3 e dynamic_wind "dynamic-wind";
;;

