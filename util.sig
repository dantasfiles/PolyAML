signature UTIL =
sig
type pos
val zip : 'a list -> 'b list -> ('a * 'b) list

val zip3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list

val map_concat : ('a -> 'b list) -> 'a list -> 'b list

val subList : Id.id list -> Id.id list -> Id.id list

val make_pos : (int*int) -> (int*int) -> pos (* make a position given two line/column pairs *)
val string_of_pos : pos -> string            (* convert a position into a string *)
val start_pos : pos                          (* position at the start of a file *)

end