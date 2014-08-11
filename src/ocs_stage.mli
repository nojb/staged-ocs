(* Evaluation *)

open Ocs_types

val stage : thread code -> scode -> sval code

val load_file : env -> thread -> string -> unit

val init : env -> unit
