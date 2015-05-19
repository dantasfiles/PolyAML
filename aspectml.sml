structure AspectML :> ASPECTML=
struct

open PrettyPrint

fun run s =
    let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp) = Inference.inferProg sourceabsyn
	val (sourcetyp', coreabsyn) = Translate.transProg infsourceabsyn
	val tc = TypeCheck.typeProg coreabsyn 
    in
	if tc
	then print (ppCProg (Eval.evalProg coreabsyn) ^ "\n")
	else ()
    end

fun parse s = 
    let 
	val _ = Compiler.Control.Print.printDepth := 100
    in 
	print (ppSProg (Parse.parse s) ^ "\n")
    end


fun infer s = 
    let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp) = Inference.inferProg sourceabsyn
    in 
	print (ppSProg infsourceabsyn ^ "\n")
    end

fun inferDebug s =
   let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp, T) = Inference.inferDebug sourceabsyn
   in 
       print (ppSExp infsourceabsyn ^ "\n\n" ^ ppInferT T)
   end

fun translate s =
   let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp) = Inference.inferProg sourceabsyn
	val (sourcetyp', coreabsyn) = Translate.transProg infsourceabsyn
   in 
       print (ppCProg coreabsyn ^ "\n")
   end

fun typecheck s = 
   let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp) = Inference.inferProg sourceabsyn
	val (sourcetyp', coreabsyn) = Translate.transProg infsourceabsyn
	val tc = TypeCheck.typeProg coreabsyn
   in
       print (ppCProg coreabsyn ^ (if tc 
				 then "\nTYPECHECKED!\n"
				 else "\n DID NOT TYPECHECK!"))
   end


fun eval s =
    let 
	val _ = Compiler.Control.Print.printDepth := 100
	val sourceabsyn = Parse.parse s
	val (infsourceabsyn, sourcetyp) = Inference.inferProg sourceabsyn
	val (sourcetyp', coreabsyn) = Translate.transProg infsourceabsyn
	val tc = TypeCheck.typeProg coreabsyn 
    in
	if tc
	then print (ppCProg (Eval.evalProgDebug coreabsyn) ^ "\n")
	else ()
    end

	  
  
end