(* Evaluation *)

open Ocs_types

val stage : senv -> (sval code -> unit code) -> scode -> unit code

val doapply : (sval -> unit) -> sval -> sval list -> unit
