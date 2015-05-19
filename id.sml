(*
   Name: id.ml
   Created: 12/14 2004
   Author: David Walker
*)
structure Id :> ID =
  struct
    type id = string * int
      
    val count = ref 1
      
    fun freshid s = let
      val i = !count 
    in count := !count + 1; (s,i)
    end
  
    fun makeid s = (s,0)

    fun cloneid (s,n) =
	let
	    val i = !count 
	in
	    count := !count + 1; (s,i) 
	end


    fun compareid ((s1,n1),(s2,n2)) =
      case Int.compare(n1,n2) of
	EQUAL => String.compare(s1,s2)
      | x => x
    fun eqid id1 id2 = compareid(id1,id2) = EQUAL
    fun leqid id1 id2 = compareid(id1,id2) = LESS

    fun id2string (s,i) = 
      if i = 0 then s 
      else s ^ "$" ^ (Int.toString i)
  end