(* Evaluation *)

open Ocs_types

val stage : senv -> thread code -> (sval code -> unit code) -> scode -> unit code

val doapply : thread -> (sval -> unit) -> sval -> sval list -> unit
