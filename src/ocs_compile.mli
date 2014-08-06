(* Compile expressions *)

open Ocs_types

val compile : env -> sval -> scode

val bind_lang : env -> unit

(* Internal, used by ocs_macro *)
val letsplit : (sval -> sval -> 'a) -> sval -> 'a
val mkbody : env -> sval array -> scode array

