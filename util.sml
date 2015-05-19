structure Util :> UTIL = 
struct 

exception UtilError of string

type pos = (int*int) * (int*int)   (* beginning and end position in source code *)

   fun make_pos start finish = (start,finish)
   fun string_of_pos ((l1,c1),(l2,c2)) = (Int.toString l1)^ "." ^ (Int.toString c1)
                                          ^ " - " ^ (Int.toString l2) ^ "." ^ (Int.toString c2)
   val start_pos = make_pos (0,0) (0,0)

fun zip (h1::t1) (h2::t2) =
    (h1,h2)::(zip t1 t2)
  | zip nil nil =
    nil
  | zip _ _ = 
    raise UtilError "zip"
	  
fun zip3 (h1::t1) (h2::t2) (h3::t3) =
    (h1,h2,h3)::(zip3 t1 t2 t3)
  | zip3 nil nil nil =
    nil
  | zip3 _ _ _ = 
    raise UtilError "zip3"

fun map_concat f (h::t) =
    (f h)@(map_concat f t)
  | map_concat f nil =
    nil

fun subId (a::tvs1) b =
    if Id.eqid a b
    then tvs1
    else a::(subId tvs1 b)
  | subId nil b =
    nil

fun subList tvs1 (b::tvs2) =
    subList (subId tvs1 b) tvs2
  | subList tvs1 nil =
    tvs1
   



end