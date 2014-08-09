(* Miscellaneous utility functions *)

open Ocs_types

val list_to_caml : sval -> sval list
val list_of_caml : sval list -> sval
  
val make_slist : sval -> sval list -> sval

val test_eqv : sval -> sval -> bool
val test_equal : sval -> sval -> bool
