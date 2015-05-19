signature ERRORMSG =
sig
    val anyErrors : bool ref
    val fileName : string ref
    val lineNum : int ref
    val linePos : int ref
    val sourceStream : TextIO.instream ref
    val error : (int*int)*(int*int) -> string -> unit
    exception Error
    val impossible : string -> 'a   (* raises Error *)
    val reset : unit -> unit
end

structure ErrorMsg : ERRORMSG =
struct

  val anyErrors = ref false
  val fileName = ref ""
  val lineNum = ref 1
  val linePos = ref 1
  val sourceStream = ref TextIO.stdIn

  fun reset() = (anyErrors:=false;
		 fileName:="";
		 lineNum:=1;
		 linePos:=1;
		 sourceStream:=TextIO.stdIn)

  exception Error

  fun error ((l1,c1),(l2,c2)) (msg:string) =
    (anyErrors := true; 
     print (!fileName);
     print " ";
     print ((Int.toString l1) ^ "." ^ (Int.toString c1));
     print " - ";
     print ((Int.toString l2) ^ "." ^ (Int.toString c2));
     print ":";
     print msg;
     print "\n")

  fun impossible msg =
      (app print ["Error: Compiler bug: ",msg,"\n"];
       TextIO.flushOut TextIO.stdOut;
       raise Error)

end  (* structure ErrorMsg *)
  
