(* Evaluation *)

open Ocs_types

val stage : [`I of sval code | `M of sval ref code] list -> (sval code -> unit code) -> scode -> unit code

val doapply : (sval -> unit) -> sval -> sval list -> unit
