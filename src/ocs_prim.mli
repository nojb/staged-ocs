(* Miscellaneous primitives.  *)

open Ocs_types

val args_err : _ sg -> string -> int -> string
val apply : sval -> sval list -> sval

val new_param : sval -> (sval -> sval) -> sval
val get_param : sval -> sval
val set_param : sval -> sval -> unit
val let_param : sval -> sval -> (unit -> 'a) -> 'a

val init : env -> unit

