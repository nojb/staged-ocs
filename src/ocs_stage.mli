(* Evaluation *)

open Ocs_types

val stage : scode -> sval code

val load_file : env -> string -> unit

val init : env -> unit
