(* Evaluation *)

open Ocs_types

val stage : thread code -> scode -> sval code

val doapply : thread -> sval -> sval list -> sval
