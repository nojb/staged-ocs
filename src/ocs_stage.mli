(* Evaluation *)

open Ocs_types

val stage : thread code -> (sval code -> unit code) -> scode -> unit code

