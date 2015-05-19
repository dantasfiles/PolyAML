(*
   Name: id.mli
   Created: 12/14 2004
   Author: David Walker
*)
signature ID =  sig
  (* type of identifiers *)
  type id
    
  (* generates unique id *)
  val freshid : string -> id
    
  (* generates id equivalent to string arg *)       
  val makeid : string -> id

  val cloneid : id -> id
    
  (* eqid id1 id2 if id1 and id2 are the same identifier *)
  val eqid : id -> id -> bool  
    
  (* leqid id1 id2 if id1 is less than id2 *)
  val leqid : id -> id -> bool
    
  (* return 0 if equal; -1 if less; 1 if greater *)
  val compareid : (id * id) -> order
    
  (* returns string representation of identifier.
   id2string (makeid s) == s
   id2string (freshid s) == s ^ "$" ^ i  for some integer i *)
  val id2string : id -> string
end
