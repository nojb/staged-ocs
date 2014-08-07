(* Create and initialize top level environment.  *)

open Ocs_types

val dstaged : bool ref

val make_env : unit -> env
val make_thread : unit -> thread
val top_loop : env -> thread -> unit

val interactive : unit -> unit

