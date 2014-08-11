(* Miscellaneous primitives.  *)

open Ocs_types

val args_err : _ sg -> string -> int -> string
val apply : thread -> sval -> sval list -> sval

val param_get : sval -> sval
val param_set : sval -> sval -> unit
val param_let : sval -> sval -> (unit -> 'a) -> 'a

val init : env -> unit

