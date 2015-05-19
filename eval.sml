structure Eval :> EVAL =
struct

open Core

exception EvalError of string
exception AbortError

val labCount = ref 0

fun newLab () = ((labCount := !labCount + 1);!labCount)

(*fun leq' ((l, _, _, l')::S) l2 =
    if l' = l2
    then true
    else leq' S l2
  | leq' nil l2 = 
    false*)

fun leq ((l, _, _, l')::S) l1 l2 = 
    if l = l1
    then (if l = l2 orelse l' = l2
	  then true
	  else leq S l' l2)
    else leq S l1 l2
  | leq nil l1 l2 =
    false
    
fun lookupLabS l ((l1, tvs, t, l2)::S) =
    if l = l1
    then (tvs, t, l2)
    else lookupLabS l S
  | lookupLabS l nil = 
    raise EvalError "lookupLabS"
		       
fun evalProg (Prog e) = 
    Prog (evalExpLoop nil nil e)
    handle EvalError s => (print ("Evalulation Error: " ^ s ^ "\n"); Prog UnitExp)
	 | (CoreError s) => (print ("Eval Core Error: " ^ s ^ "\n");  Prog UnitExp)
	 | AbortError => (print ("Program aborted.\n"); Prog UnitExp)

and evalProgDebug (Prog e) =
  Prog (evalExpDebugLoop nil nil e)
    handle EvalError s => (print ("Evalulation Error: " ^ s ^ "\n"); Prog UnitExp)


and evalExpDebugLoop S A e =
    if isVal e 
    then e
    else let 
	    val _ = print (PrettyPrint.ppCExp e ^ "\n\n")
	    val (S', A', e') = evalExp NilStExp S A e
	in  
	    evalExpDebugLoop S' A' e'
	end

and evalExpLoop S A e =
    if isVal e 
    then e
    else let 
	    val (S', A', e') = evalExp NilStExp S A e
	in  
	    evalExpLoop S' A' e'
	end
	    

and evalExp stack S A e =
    let 
	fun evalExp' (AppExp (FunExp (x,t,e1), e2)) = 
		      if isVal e2
		      then (S, A, substExp e2 x e1) 
		      else let 
			      val (S', A', e2') = evalExp' e2
			  in 
			      (S', A', AppExp (FunExp (x,t,e1), e2'))
			      end
	  | evalExp' (AppExp (e1, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', AppExp (e1', e2))
	    end
	  | evalExp' (TyAppExp (TyFunExp (a, e), t)) =
	    (S, A, tysubstExp t a e)
	  | evalExp' (TyAppExp (e, t)) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', TyAppExp (e', t))
	    end
	  | evalExp' (TupleExp es) =
	    let 
		val (S', A', es') = evalExpList stack S A es
	    in
		(S', A', TupleExp es')
	    end 
	  | evalExp' (LetExp (xs, TupleExp es, e)) =
	    if (List.all (fn(e) => isVal e) es)
	    then (S, A, substExpList es xs e)
	    else let 
		    val (S', A', es') = evalExpList stack S A es
		in
		    (S', A', LetExp(xs,TupleExp(es'),e))
		end 
	  | evalExp' (LetExp (xs, e1, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', LetExp (xs, e1', e2))
	    end
	  | evalExp' (PCExp (LabExp l, ts, e)) =
	    if isVal e
	    then let
		    val (tvs, t, l') = lookupLabS l S
		   (* val _ = print ("calling advComp " ^ PrettyPrint.ppCExp e ^ "\n")*)
		    val v' = advComp S A l (tysubstTypList ts tvs t)
		in 
		    (S, A, AppExp (v', e))
		end
	    else let 
		    val (S', A', e') = evalExp' e
		in 
		    (S', A', PCExp (LabExp l, ts, e')) 
		end
	  | evalExp' (PCExp (e1, ts, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in 
		(S', A', PCExp (e1', ts, e2))
	    end
	  | evalExp' (NewExp(tvs, t, LabExp l)) =
	    let 
		val l' = newLab ()
	    in 
		((l', tvs, t, l)::S, A, LabExp l')
	    end
	  | evalExp' (NewExp(tvs, t, e)) =
	    let 
		val (S', A', e') = evalExp' e
	    in 
		(S', A', NewExp (tvs, t, e'))
	    end
	  | evalExp' (AdvInstExp e) =
	    if isVal e
	    then (S, A@[e], UnitExp)
	    else let
		    val (S', A', e') = evalExp' e
		in 
		    (S', A', AdvInstExp e')
		end
	  | evalExp' (AdvExp (e1, tvs, x, t, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', AdvExp (e1', tvs, x, t, e2))
	    end 
	  | evalExp' (TypeCaseExp (a, t1, t2, tes)) =
	    let
		val (T,e) = case (List.find (fn (ti,ei) => (((mgu t2 ti);true)
									 handle MGUError => false)) tes) of
				 SOME (ti,ei) => (mgu t2 ti, ei)
			       | NONE => raise EvalError "TypeCaseExp: not complete match"
		val ts = map #1 T
		val tvs = map #2 T
	    in 
		(S, A, (tysubstExpList ts tvs e))
	    end
	  | evalExp' (SetExp es) =
	    let 
		val (S', A', es') = evalExpList stack S A es
	    in
		(S', A', SetExp es')
	    end 
	  | evalExp' (UnionExp (SetExp es1, SetExp es2)) =
	    if List.all (fn(e) => isVal e) es1
	    then if List.all (fn(e) => isVal e) es2
		 then (S, A, SetExp (es1 @ es2))
		 else let 
			 val (S', A', es2') = evalExpList stack S A es2
		     in
			 (S', A', UnionExp (SetExp es1, SetExp es2'))
		     end 
	    else let 
		    val (S', A', es1') = evalExpList stack S A es1
		in
		    (S', A', UnionExp (SetExp es1', SetExp es2))
		end 
	  | evalExp' (UnionExp (e1, e2)) =
	    if isVal e1
	    then let
		    val (S', A', e2') = evalExp' e2
		in 
		    (S', A', UnionExp (e1, e2')) 
		end 
	    else 
		let 
		    val (S', A', e1') = evalExp' e1
		in
		    (S', A', UnionExp (e1', e2))
		end 
	  | evalExp' StackExp =
	    (S, A, stack)
	  | evalExp' (PtStExp (e1, ts, e2, e3)) =
	    if isVal e1
	    then if isVal e2
		 then let 
			 val (S', A', e3') = evalExp' e3
		     in 
			 (S', A', PtStExp (e1, ts, e2, e3'))
		     end
		 else let 
			 val (S', A', e2') = evalExp' e2
		     in 
			 (S', A', PtStExp (e1, ts, e2', e3))
		     end
	    else let 
		    val (S', A', e1') = evalExp' e1
		in 
		    (S', A', PtStExp (e1', ts, e2, e3))
		end
	  | evalExp' (StoreExp (e1, ts, e2, e3)) =
	    if isVal e1
	    then if isVal e2
		 then if isVal e3
		      then (S, A, e3)
		      else let 
			      val (S', A', e3') = evalExp (PtStExp (e1, ts, e2, stack)) S A e3
			  in 
			      (S', A', StoreExp(e1, ts, e2, e3'))
			  end
		 else let 
			 val (S', A', e2') = evalExp' e2
		     in 
			 (S', A', StoreExp (e1, ts, e2', e3))
		     end
		
	    else let 
		    val (S', A', e1') = evalExp' e1
		in 
		    (S', A', StoreExp (e1', ts, e2, e3))
		end
	  | evalExp' (StkCaseExp (e1, pes)) =
	    if isVal e1
	    then if List.all isValPat (map #1 pes)
		 then let 
			 val (p,e) = (case (List.find (fn(pi,_) => 
						  case (stackMatch S e1 pi) of
						      SOME _ => true
						    | NONE => false) 
					       pes) of
					 SOME x => x
				       | NONE => raise EvalError "StkCaseExp: not complete match")
			 val (ts, tvs, vs, xs) = (case (stackMatch S e1 p) of
						     SOME x => x
						   | NONE => raise EvalError "StkCaseExp: impossible")
		     in 
			 (S, A, tysubstExpList ts tvs (substExpList vs xs e))
		     end
		 else let 
			 val (S', A', pes') = evalPatExpList stack S A pes
		     in 
			 (S', A', StkCaseExp (e1, pes'))
		     end
	    else let
		    val (S', A', e1') = evalExp' e1
		in 
		    (S', A', StkCaseExp (e1', pes))
		end
	  | evalExp' (PlusExp(IntExp i1, IntExp i2)) =
	    (S, A, IntExp (i1 + i2))
	  | evalExp' (PlusExp(IntExp i1, e)) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', PlusExp(IntExp i1, e'))
	    end
	  | evalExp' (PlusExp(e1, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', PlusExp(e1', e2))
	    end
	  | evalExp' (IfExp (BoolExp b, e1, e2)) =
	    (S, A, if b then e1 else e2)
	  | evalExp' (IfExp (e1, e2, e3)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', IfExp(e1', e2, e3))
	    end
	  | evalExp' (PrintExp (StringExp s)) =
	    ((print s); (S, A, UnitExp))
	  | evalExp' (PrintExp e) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', PrintExp e')
	    end
	  | evalExp' (ItoSExp (IntExp i)) =
	    (S, A, StringExp (Int.toString i))
	  | evalExp' (ItoSExp e) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', ItoSExp e')
	    end
	  | evalExp' (ConcatExp(StringExp s1, StringExp s2)) =
	    (S, A, StringExp (s1 ^ s2))
	  | evalExp' (ConcatExp(StringExp s1, e)) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', ConcatExp(StringExp s1, e'))
	    end
	  | evalExp' (ConcatExp(e1, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', ConcatExp(e1', e2))
	    end
	  | evalExp' (FixExp (f, t, e)) =
	    (S, A, substExp (FixExp (f, t, e)) f e)
	  | evalExp' AbortExp =
	    raise AbortError
	  | evalExp' (EqExp(StringExp s1, StringExp s2)) =
	    (S, A, BoolExp (case String.compare (s1, s2) of 
				EQUAL => true
			      | _ => false))
	  | evalExp' (EqExp(StringExp s1, e)) =
	    let 
		val (S', A', e') = evalExp' e
	    in
		(S', A', EqExp(StringExp s1, e'))
	    end
	  | evalExp' (EqExp(e1, e2)) =
	    let 
		val (S', A', e1') = evalExp' e1
	    in
		(S', A', EqExp(e1', e2))
	    end
	  | evalExp' (PosExp(pos', e)) =
	    if isVal e
	    then (S, A, e)
	    else let 
		    val (S', A', e') = evalExp' e
		in 
		    (S', A', PosExp (pos', e'))
		end
	  | evalExp' e = raise EvalError ("stuck at\n" ^ PrettyPrint.ppCExp e)
    in 
	if isVal e
	then raise EvalError "evalExp"
	else ((*(print (PrettyPrint.ppCExp e ^ "\n\n")); *)evalExp' e)
    end

and evalPat stack S A p = 
    let 
	fun evalPat' NilPat = 
	    (S, A, NilPat)
	  | evalPat' (PtPat(e, tvs, x, t, p)) =
	    if isVal e
	    then let 
		    val (S', A', p') = evalPat' p
		in 
		   (S', A', PtPat (e, tvs, x, t, p'))
		end
	    else let 
		    val (S', A', e') = evalExp stack S A e
		in
		    (S', A', PtPat (e', tvs, x, t, p))
		end
	  | evalPat' (VarPat x) =
	    (S, A, VarPat x)
	  | evalPat' (AllPat p) =
	    let 
		val (S', A', p') = evalPat' p
	    in 
		(S', A', AllPat p')
	    end
    in 
	if isValPat p
	then raise EvalError "evalPat"
	else evalPat' p
    end
	
and advComp S nil l t = 
    let 
	val x = Id.freshid "x"
    in 
	FunExp(x, t, VarExp x)
    end
  | advComp S (AdvExp(SetExp ls, tvs, x, t, e)::A) l t' =
    let 
	val v = advComp S A l t'
    in 
	if List.exists (fn(LabExp li) => leq S l li
			| _ => raise EvalError "advComp: AdvExp") ls
	then let 
		val ttvs = findSubst tvs t t'
		val ts = map #1 ttvs
		val tvs' = map #2 ttvs
		(*val _ = print ("found match" ^ PrettyPrint.ppCExp e ^ "\n")*)
	    in 
		FunExp(x, t', AppExp (v, tysubstExpList ts tvs' e))
	    end
	else v
    end
  | advComp _ (e::t) _ _ =
    raise EvalError ("AdvComp: " ^ PrettyPrint.ppCExp e)

and stackMatch S = 
    let 
	fun stackMatch' NilStExp NilPat =
	    SOME (nil, nil, nil, nil)
	  | stackMatch' (PtStExp(LabExp l, ts, v1, v2)) (PtPat(SetExp ls, tvs, x, t1, p)) =
	    let 
		val sub = stackMatch' v2 p
	    in 
		case sub of SOME (tysub1, tysub2, sub1, sub2) => 
			    if List.exists (fn(LabExp li) => leq S l li
					    | _ => raise EvalError "stackMatch: PtStExp PtPat") ls
			    then let 
				    val (tvs', t2, l') = lookupLabS l S
				    val otvs = findSubst tvs t1 (tysubstTypList ts tvs' t2)
				    val os = map #1 otvs
				    val tvs'' = map #2 otvs
				in 
				    SOME (os@tysub1, tvs''@tysub2, v1::sub1, x::sub2)
				end
			    else NONE
			  | NONE => NONE
	    end
	  | stackMatch' (PtStExp(l,ts,v1,v2)) (AllPat p) =
	    stackMatch' v2 p
	  | stackMatch' v (VarPat x) =
	    SOME (nil, nil, [v], [x])
	  | stackMatch' _ _ = 
	    NONE
    in 
	stackMatch'
    end
    


and evalExpList stack S A =
    let 
	fun evalExpList' (e::es) =
	    if (isVal e)
	    then let
		    val (S', A', es') = evalExpList' es
		in 
		    (S', A', e::es')
		end
	    else let 
		    val (S', A', e') = evalExp stack S A e 	    
		   (* val (S'', A'', es') = evalExpList stack S' A' es*)
				       
		in
		    (S', A', e'::es)
		end
	  | evalExpList' nil = (S, A, nil)
    in 
	evalExpList'
    end

and evalPatExpList stack S A =
    let 
	fun evalPatExpList' ((p,e)::pes) =
	    if (isValPat p)
	    then let
		    val (S', A', pes') = evalPatExpList' pes
		in 
		    (S', A', (p,e)::pes')
		end
	    else let 
		    val (S', A', p') = evalPat stack S A p	    
		in
		    (S', A', (p',e)::pes)
		end
	  | evalPatExpList' nil = (S, A, nil)
    in 
	evalPatExpList'
    end


end