(* Create and initialize top level environment.  *)

open Ocs_types

val dstaged : bool ref

val make_env : unit -> env
val top_loop : env -> unit

val interactive : unit -> unit

