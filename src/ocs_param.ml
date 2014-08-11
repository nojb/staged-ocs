(* Dynamic bindings *)

open Ocs_types
open Ocs_stage
open Ocs_error
open Ocs_env

let make_parameter args th =
  match args with
    init :: [] ->      
      let dv = Dynvar.dnew () in
        Sparam { p_dynvar = dv; p_init = init; p_conv = (fun x -> x) }
  | init :: converter :: [] ->
      let dv = Dynvar.dnew () in
        Sparam { p_dynvar = dv; p_init = init; p_conv = (fun x -> doapply th converter [ x ]) }
  | _ ->
      raise (Error "make-parameter: bad args")
;;

let init e =
  set_pfg e (Prest Rcont) make_parameter "make-parameter";
;;
