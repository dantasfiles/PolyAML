structure Translate :> TRANSLATE =
struct

open Core PrettyPrint Util

exception TransError of string

structure S = Source
structure W = Word8

fun not_eq t1 t2 = 
    ppSTyp t1 ^ " != " ^ ppSTyp t2

fun trans_err pos s = 
  raise (TransError ("Position " ^ string_of_pos pos ^ ": " ^ s)) 
    
fun gen_typ D (S.ForAllPolyTyp (tvs1, t1)) (S.ForAllPolyTyp(tvs2, t2)) = 
    if S.checkTyp (tvs1@D) t1
    then (if S.checkTyp (tvs2@D) t2
	  then let 
		  val ttvs = S.findSubst tvs1 t2 t2
		  val ts = map #1 ttvs
		  val tvs = map #1 ttvs
	      in 
		  if List.all (fn(ti) => S.checkTyp D ti) ts
		  then true
		  else false
	      end
	  else false)
    else false


fun LetTExp (x,t,e1,e2) =
    AppExp (FunExp(x,t,e2), e1)
   
fun ForAllListTyp (tv::tvs, t) =
    ForAllTyp(tv, ForAllListTyp(tvs, t))
  | ForAllListTyp (nil, t) =
    t
    
fun TyFunListExp (tv::tvs, e) =
    TyFunExp (tv, TyFunListExp(tvs, e))
  | TyFunListExp (nill, e) =
    e
    
fun TyAppListExp (e, t::ts) =
    TyAppExp(TyAppListExp(e, ts), t)
  | TyAppListExp (e, nil) =
    e

(*fun StkCaseListExp (e1, p::p'::ps, e::e'::es, x, e2) =
    let
	val y = Id.freshid "y"
    in 
	LetTExp(y, StackTyp, e1, StkCaseListExp(VarExp y, p'::ps, e'::es, x, e2))
    end
  | StkCaseListExp (e1:exp, p::nil, e::nil, x, e2) =
    StkCaseExp (e1, p, e, x, e2)
  | StkCaseListExp (e1, _, _, x, e2) =
    raise TransError "StkCaseListExp"*)

(*fun TypeCaseListExp (a, t1, VarTyp b, ts:typ list, es:exp list, c, e2) =
    let 
	fun TypeCaseListExp' (t::t'::ts, e::e'::es) =
	    TypeCaseExp (a, t1, VarTyp b, t, e, c, TypeCaseListExp'(t'::ts, e'::es))
	  | TypeCaseListExp' (t::nil, e::nil) =
	    TypeCaseExp (a, t1, VarTyp b, t, e, c, e2)
	  | TypeCaseListExp' (_, _) =
	    raise TransError "TypeCaseListExp'"
    in 
	if (Id.eqid a c) andalso (Id.eqid a b)
	then TypeCaseListExp' (ts, es)
	else raise TransError "TypeCaseListExp1"
    end
  | TypeCaseListExp _ =
    raise TransError "TypeCaseListExp2"*)
    
fun split nil e = e
  | split ((x, y, z)::T) e = split T (LetExp([y, z], VarExp x, e))

fun completePatMatch pos ps = 
  let  
      fun completePatMatch' true nil = 
	  (false, nil)
	| completePatMatch' false nil = 
	  trans_err pos ("CompletePatMatch: match not complete")
	| completePatMatch' _ (S.NilPat::ps) =
	  completePatMatch' true ps
	| completePatMatch' _ ((S.VarPat _)::ps) =
	  (true,nil)
	| completePatMatch' hasNil ((S.AllPat p)::ps) =
	  let
	      val (b, ps') = completePatMatch' hasNil ps
	  in 
	      (b, p::ps')
	  end
	| completePatMatch' hasNil ((S.PtPat(S.AnyPtExp,_,_,p))::ps) =
	  let
	      val (b, ps') = completePatMatch' hasNil ps
	  in
	      (b,p::ps')
	  end
	| completePatMatch' hasNil ((S.AnnotPtPat(S.AnyPtExp,_,_,_,p))::ps) =
	  let
	      val (b, ps') = completePatMatch' hasNil ps
	  in
	      (b,p::ps')
	  end
	| completePatMatch' hasNil (_::ps) =
	  completePatMatch' hasNil ps
      val (b,ps') = completePatMatch' false ps
  in 
      if b 
      then true
      else completePatMatch pos ps'
  end

fun completeTypMatch pos ts = 
    let
	fun completeTypMatch' ftvss ts = 
	    let
		fun hasVarTyp (ftvs::ftvss) ((S.VarTyp b)::ts) =
		    if inList b ftvs
		    then true
		    else hasVarTyp ftvss ts
		  | hasVarTyp (_::ftvss) (_::ts) =
		    hasVarTyp ftvss ts
		  | hasVarTyp _ _ =
		    false
		fun hasBaseTyp t (t'::ts) =
		    if S.eq_typ t t'
		    then true
		    else hasBaseTyp t ts
		  | hasBaseTyp _ nil =
		    false
		fun filterArrTyp (ftvs::ftvss) ((S.ArrTyp (t1, t2))::ts) =
		    let 
			val (ftvss', _, t1s, _, t2s) = filterArrTyp ftvss ts
		    in 
			(ftvs::ftvss', nil, t1::t1s, nil, t2::t2s)
		    end
		  | filterArrTyp (ftvs::ftvss) (t::ts) =
		    filterArrTyp ftvss ts
		  | filterArrTyp _ _ = 
		    (nil, nil, nil, nil, nil)
		fun filterPCTyp (ftvs::ftvss) ((S.PCTyp (S.ForAllPolyTyp(tvs1,t1), S.ForAllPolyTyp(tvs2, t2)))::ts) =
		    let 
			val (ftvss', tvs1s, t1s, tvs2s, t2s) = filterPCTyp ftvss ts
		    in 
			(ftvs::ftvss', tvs1::tvs1s, t1::t1s, tvs2::tvs2s, t2::t2s)
		    end
		  | filterPCTyp (ftvs::ftvss) (t::ts) =
		    filterPCTyp ftvss ts
		  | filterPCTyp _ _ = 
		    (nil, nil, nil, nil, nil)
		fun hasComplexTyp (ftvss, tvs1s, t1s, tvs2s, t2s) =
		    let 
			val ftvss1 =  map (fn (tvs1, tvs2) => (tvs1 @ tvs2)) (zip ftvss tvs1s)
			val freetvs1s = map (fn(t) => S.FTV t) t1s
			val subftvss = map (fn (tvs1, tvs2) => (subList tvs1 tvs2)) (zip freetvs1s tvs1s)
			val stillftvss =  map (fn (tvs1, tvs2) => (subList tvs1 tvs2)) (zip ftvss subftvss)
			val ftvss2 = map (fn (tvs1, tvs2) => (tvs1 @ tvs2)) (zip stillftvss tvs2s)
					 
		    in
			completeTypMatch' ftvss1 t1s andalso completeTypMatch' ftvss2 t2s
		    end
	    in 
		if hasVarTyp ftvss ts
		then true
		else (if hasBaseTyp S.UnitTyp ts 
			 andalso hasBaseTyp S.StringTyp ts 
			 andalso hasBaseTyp S.StackTyp ts
			 andalso hasBaseTyp S.IntTyp ts 
			 andalso hasBaseTyp S.BoolTyp ts
			 andalso hasComplexTyp (filterArrTyp ftvss ts)
			 andalso hasComplexTyp (filterPCTyp ftvss ts)
			 andalso hasBaseTyp S.IntTyp ts 
			 andalso hasBaseTyp S.BoolTyp ts
		      then false
		      else trans_err pos ("CompleteTypMatch: match not complete"))
	    end
	val ftvss = map S.FTV ts
    in
	completeTypMatch' ftvss ts
    end
	    
	    

fun transTyp pos D =
    let
	fun transTyp' (S.VarTyp a) =
			if inList a D
			then VarTyp a
			else trans_err pos ("VarTyp: " ^ ppTyvar a)
	  | transTyp' S.UnitTyp =
	    UnitTyp
	  | transTyp' S.StringTyp =
	    StringTyp
	  | transTyp' S.StackTyp = 
	    StackTyp
	  | transTyp' (S.ArrTyp (t1, t2)) = 
	    ArrTyp (transTyp' t1, transTyp' t2)
	  | transTyp' (S.PCTyp (S.ForAllPolyTyp(tvs1, t1), S.ForAllPolyTyp(tvs2, t2))) =
	    let 
		val t1' = transTyp pos (tvs1@D) t1
		val t2' = transTyp pos (tvs2@D) t2
		val t1ss = TupleTyp [t1', StackTyp, StringTyp]
		val t1s = TupleTyp [t1', StringTyp]
		val t2ss = TupleTyp [t2', StackTyp, StringTyp]
	    in 
		TupleTyp [PCTyp (tvs1, t1ss), 
			  PCTyp (tvs1, t1s),
			  PCTyp (tvs2, t2ss)]
	    end
	  | transTyp' (S.InfVarTyp X) =
	    trans_err pos ("InfVarTyp: bad inference variable " ^ ppInfTyvar X)
	  | transTyp' (S.IntTyp) =
	    IntTyp
	  | transTyp' (S.BoolTyp) =
	    BoolTyp
    in
	transTyp'
    end

fun transLExp pos D P G =
    let 
	fun transLExp' (S.TyAnnExp(e, t)) =
	    let 
		val (t', e') = transGExp pos D P G e
	    in 
		if S.checkTyp D t
		then (if S.eq_typ t t'
		      then (t, e')
		      else trans_err pos ("TyAnnExp: " ^ not_eq t t'))
		else trans_err pos ("TyAnnExp: bad type " ^ ppSTyp t)
	    end
	  | transLExp' (S.VarExp x) =
	    let
		val t = S.lookupVarG x G
	    in 
		(t, VarExp x)
	    end
	  | transLExp' S.UnitExp =
	    (S.UnitTyp, UnitExp)
	  | transLExp' (S.StringExp s) =
	    (S.StringTyp, StringExp s)
	  | transLExp' (S.FunsPtExp (fs, s1, s2)) =
	    let
		val tvst1t2s = map (fn(f) => if inList f P
					  then let 
						  val (tvs, t) = S.lookupGenG f G
					      in 
						  case t of 
						      S.ArrTyp(t1, t2) => (tvs, t1, t2)
						    | _ => trans_err pos "FunsPtExp: f not arrow typ"
					      end
					  else trans_err pos "FunsPtExp: f not in P") fs		   
	    in 
		if List.all (fn (tvs, t1, _) => 
				gen_typ D s1 
					(S.ForAllPolyTyp (tvs,t1))) 
			    tvst1t2s
		then if List.all (fn (tvs, _, t2) =>  
				     gen_typ D s2 
					     (S.ForAllPolyTyp (tvs,t2))) 
				 tvst1t2s
		     then let 
			     val fbefores = map (fn (f) => VarExp (Id.makeid (Id.id2string f ^ "before"))) fs
			     val fstks = map (fn (f) => VarExp (Id.makeid (Id.id2string f ^ "stk"))) fs
			     val fafters = map (fn (f) => VarExp (Id.makeid (Id.id2string f ^ "after"))) fs	    
			 in 
			      (S.PCTyp (s1, s2), 
			       TupleExp [SetExp fbefores, 
					 SetExp fstks,
					 SetExp fafters])
			 end
		     else trans_err pos "FunsPtExp s1 did not generalize"
		else trans_err pos "FunsPtExp s1 did not generalize"
	    end
	  | transLExp' S.AnyPtExp = 
	    let
		val a = Id.freshid "a" 
	    in
		(S.PCTyp(S.ForAllPolyTyp([a], S.VarTyp a), 
		      S.ForAllPolyTyp([a], S.VarTyp a)), 
		 TupleExp [SetExp [VarExp (Id.makeid "Ubefore")],
			   SetExp [VarExp (Id.makeid "Ustk")],
			   SetExp [VarExp (Id.makeid "Uafter")]])
	    end
	  | transLExp' (S.IntExp i) =
	    (S.IntTyp, IntExp i)
	  | transLExp' (S.BoolExp b) =
	    (S.BoolTyp, BoolExp b)
	  | transLExp' (S.PosExp (pos', e)) =
	    let 
		val (t, e') = transLExp pos' D P G e
	    in 
		(t, PosExp (pos', e'))
	    end
	  | transLExp' _ =
	    trans_err pos "transLExp not found"
    in 
	transLExp'
    end

and transGExp pos D P G =
    let 
	fun transGExp' (S.AppExp(e1, e2)) =
	    let 
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
	(*	val _ = print (ppSExp e1 ^ "\n")
		val _ = print (ppSExp e2 ^ "\n")
		val _ = print (ppSTyp t1 ^ "\n")
		val _ = print (ppSTyp t2 ^ "\n")*)
	    in 
		case t1 of S.ArrTyp(t1a, t1b) => if S.eq_typ t1a t2
					      then (t1b, AppExp (e1', e2'))
					      else trans_err pos ("AppExp: " ^ not_eq t1a t2)
			 | _ => trans_err pos ("AppExp: " ^ ppSTyp t1 ^ " not ArrTyp")
	    end
	  | transGExp' (S.LetExp (d, e)) = 
	    transDec pos D P G d e
	  | transGExp' (S.StkCaseExp (e1, pes)) =
	    let 
		val (t1, e1') = transGExp' e1
		val ptes' = map (fn(pi,ei) => let 
				       val (pi', Di, Gi, Ti) = transPat pos D P G pi
				       val (ti, ei') = transGExp pos P (Di@D) (Gi@G) ei
				   in 
				       (pi', ti, split Ti ei') 
				   end) pes
		val ps' = map #1 ptes'
		val ts' = map #2 ptes'
		val es' = map #3 ptes'
		val (t'::ts'') = case ts' of
				     (t'::ts'') => (t'::ts'')
				   | nil => trans_err pos "StkCaseExp: impossible"
		val pes' = zip ps' es'
		val _ = if completePatMatch pos (map #1 pes) 
			then true 
			else trans_err pos "StkCaseExp: incomplete stack match"
	    in 
		if S.eq_typ t1 S.StackTyp
		then (if List.all (S.eq_typ t') ts'
		     then (t', StkCaseExp(e1', pes'))
		     else trans_err pos "StkCaseExp: not all same type")
		else trans_err pos ("StkCaseExp: " ^ not_eq t1 S.StackTyp)
	    end
	  | transGExp' (S.TypeCaseExp(t, a, tes)) =
	    let 
		val t' = transTyp pos D t
		val tes' = map (fn(ti,ei) => let
				      val Pi' = S.FTV ti 
				      val Di = subList (S.FTV ti) D
				      val ti' = transTyp pos (Di@D) ti
				      val (ti'', ei') = transGExp pos (Di@D) (Pi'@P) (S.tysubstG ti a G) ei
				      
				  in 
				      if S.eq_typ (S.tysubstTyp ti a t) ti'' 
				      then (if S.inList a (S.FTV ti)
					   then trans_err pos ("TypeCaseExp:" ^ ppTyvar a ^ "not in D")
					   else (ti', ei'))
				      else trans_err pos ("TypeCaseExp: " ^ not_eq (S.tysubstTyp ti a t) ti'')
				      
				  end)
			       tes
		val _ = if completeTypMatch pos (map #1 tes) then true else trans_err pos "TypeCaseExp: incomplete type match"
	    in 
		(t, TypeCaseExp(a, t', VarTyp a, tes'))
	    end
	  | transGExp' (S.TyAppExp (f, ts)) =
	    let 
		val (tvs, t) = S.lookupGenG f G
	(*	val _ = print ("tyappt: " ^ PrettyPrint.ppSTyp t ^ "\n")
		val _ = print ("tyapptvs: " ^ PrettyPrint.ppList (map PrettyPrint.ppTyvar tvs)^"\n") *)
		val ts' = map (transTyp pos D) ts
	    in 
		(S.tysubstTypList ts tvs t, TyAppListExp(VarExp f, ts')) 
	    end
	  | transGExp' (S.PlusExp (e1, e2)) =
	    let
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
	    in
		if S.eq_typ t1 S.IntTyp
		then (if S.eq_typ t2 S.IntTyp
		      then (t1, PlusExp(e1', e2'))
		      else trans_err pos ("PlusExp1: " ^ not_eq t2 S.IntTyp))
		else trans_err pos ("PlusExp2: " ^ not_eq t1 S.IntTyp)
	    end
	  | transGExp' (S.IfExp (e1, e2, e3)) =
	    let
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
		val (t3, e3') = transGExp' e3
	    in
		if S.eq_typ t1 S.BoolTyp
		then (if S.eq_typ t2 t3
		      then (t2, IfExp (e1', e2', e3'))
		      else trans_err pos ("IfExp1: " ^ not_eq t2 t3))
		else trans_err pos ("IfExp2: " ^ not_eq t1 S.BoolTyp)
	    end
	  | transGExp' (S.PrintExp e) =
	    let 
		val (t, e') = transGExp' e
	    in 
		if S.eq_typ t S.StringTyp
		then (S.UnitTyp, PrintExp e')
		else trans_err pos ("PrintExp: " ^ not_eq t S.StringTyp)
	    end
	  | transGExp' (S.ItoSExp e) =
	    let 
		val (t, e') = transGExp' e
	    in 
		if S.eq_typ t S.IntTyp
		then (S.StringTyp, ItoSExp e')
		else trans_err pos ("ItoSExp: " ^ not_eq t S.IntTyp)
	    end
	  | transGExp' (S.ConcatExp (e1, e2)) =
	    let
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
	    in
		if S.eq_typ t1 S.StringTyp
		then (if S.eq_typ t2 S.StringTyp
		      then (t1, ConcatExp(e1', e2'))
		      else trans_err pos ("ConcatExp1: " ^ not_eq t2 S.StringTyp))
		else trans_err pos ("ConcatExp2: " ^ not_eq t1 S.StringTyp)
	    end
	  | transGExp' (S.SeqExp(e1, e2)) =
	    let 
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
		val under = Id.freshid "_"
	    in 
		if S.eq_typ t1 S.UnitTyp 
		then (t2, LetTExp(under, UnitTyp, e1', e2'))
		else trans_err pos ("SeqExp: " ^ not_eq t1 S.UnitTyp)
	    end
	  | transGExp' S.AbortExp =
	    (S.UnitTyp, AbortExp)
	  | transGExp' (S.EqExp (e1, e2)) =
	    let
		val (t1, e1') = transGExp' e1
		val (t2, e2') = transGExp' e2
	    in
		if S.eq_typ t1 S.StringTyp
		then (if S.eq_typ t2 S.StringTyp
		      then (S.BoolTyp, EqExp(e1', e2'))
		      else trans_err pos ("EqExp1: " ^ not_eq t2 S.StringTyp))
		else trans_err pos ("EqExp2: " ^ not_eq t1 S.StringTyp)
	    end
	  | transGExp' (S.PosExp (pos', e)) =
	    transGExp pos' D P G e
	  | transGExp' e =
	    transLExp pos D P G e
    in 
	transGExp'
    end



and transPat pos D P G =
    let 
	fun transPat' S.NilPat =
	    (NilPat, nil, nil, nil)
	  | transPat' (S.VarPat x) =
	    (VarPat x, nil, [S.VarG(x, S.StackTyp)], nil)
	  | transPat' (S.AllPat p) =
	    let 
		val (p', D', G', T') = transPat' p
	    in 
		(AllPat p', D', G', T')
	    end
	  | transPat' (S.PtPat(e, x, z, p)) =
	    trans_err pos "PtPat"
	 (* | transPat' (S.PtPat(e, x, z, p)) =
	    let
		val (t, e') = transLExp D P G e
		val e'' = (let 
			       val x2 = Id.freshid "x"
			    in 
				LetExp([Id.freshid "_", x2, Id.freshid "_"],
				       e',
				       VarExp x2)
			    end)
		val (tvs, t') = case t of
				    S.PCTyp(S.ForAllPolyTyp(tvs, t'), s) => (tvs, t')
				  | _ => raise TransError ("PtPat: " ^ ppSTyp t)		
		val t'' = transTyp t'
		val (p', D', G', T) = transPat' p
		val y = Id.freshid "y"
		val tss = TupleTyp[t'', StringTyp]
	    in 
		(PtPat(e'', tvs, y, tss, p'), 
		 (tvs@D'),
		 S.VarG(z, S.StringTyp)::S.VarG(x,t')::G', 
		 (y,x,z)::T)	
	    end*)
	  | transPat' (S.AnnotPtPat(e, x, t3, z, p)) =
	    let
		val (t, e') = transLExp pos D P G e
		val e'' = (let 
			       val x2 = Id.freshid "x"
			    in 
				LetExp([Id.freshid "_", x2, Id.freshid "_"],
				       e',
				       VarExp x2)
			    end)
		val (tvs, t') = case t of
				    S.PCTyp(S.ForAllPolyTyp(tvs, t'), s) => (tvs, t')
				  | _ => trans_err pos ("PtPat: " ^ ppSTyp t)		
		val tvs' = subList (S.FTV t3) D
		val t3' = transTyp pos (tvs'@D) t3
		val s1 = S.ForAllPolyTyp(tvs, t')
		val s2 = S.ForAllPolyTyp(tvs', t3)
		val (p', D', G', T) = transPat' p
		val y = Id.freshid "y"
		val tss = TupleTyp[t3', StringTyp]
	    in 
		if S.eq_poly_typ s1 s2
		then (PtPat(e'', tvs', y, tss, p'), 
		      (tvs'@D'),
		      S.VarG(z, S.StringTyp)::S.VarG(x,t3)::G', 
		      (y,x,z)::T)	
		else trans_err pos ("AnnotPtPat: " ^ not_eq t' t3)
	    end
    in 
	transPat'
    end

and transDec pos D P G d e =
    let
	fun transDec' (S.FunDec (f, x, t1, t2, e1)) =
	    let 
		val (tvs', t3) = S.gen G (S.ArrTyp (t1, t2))
		val (t1, t2) = case t3 of 
				     S.ArrTyp(t1, t2) => (t1, t2)
				   | _ => trans_err pos "FunDec: bad ArrTyp"
		val tvs = subList ((S.FTV t1)@(S.FTV t2)) D
		val t1' = transTyp pos (tvs@D) t1
		val t2' = transTyp pos (tvs@D) t2
	(*	val _ = print ("t: " ^ PrettyPrint.ppSTyp t3 ^ "\n")
		val _ = print ("tvs: " ^ PrettyPrint.ppList (map PrettyPrint.ppTyvar tvs)^"\n") *)
		val (t2'', e1') = transGExp pos (tvs@D) (f::P) (S.VarG(x, t1)::S.VarG(f,S.ArrTyp (t1, t2))::G) e1
		val (t, e') = transGExp pos D (f::P) (S.GenG(f, tvs, S.ArrTyp(t1, t2))::G) e
		val fname = Id.id2string f
		val fafter = Id.makeid (fname ^ "after")
		val fbefore = Id.makeid (fname ^ "before")
		val fstk = Id.makeid (fname ^ "stk")
		val under = Id.freshid "_"
		val fafterlet = LetExp ([x, 
					 under, 
					 under], 
					PCExp(VarExp fafter, 
					      map VarTyp tvs, 
					      TupleExp [e1', 
							StackExp, 
							StringExp fname]), 
					VarExp x)
		val fbeforelet = LetExp ([x, 
					  under, 
					  under], 
					 PCExp (VarExp fbefore, 
						map VarTyp tvs, 
						TupleExp [VarExp x,
							  StackExp, 
							  StringExp fname]), 
					 fafterlet) 
		val flet = LetTExp (f, 
				    ForAllListTyp(tvs,
						  ArrTyp(t1', 
							 t2')), 
				    FixExp (f, 
					    ForAllListTyp(tvs,
							  ArrTyp(t1', 
								 t2')), 
					    TyFunListExp (tvs, 
							  FunExp(x, 
								 t1', 
								 StoreExp (VarExp fstk, 
									   map VarTyp tvs, 
									   TupleExp [VarExp x, 
										     StringExp fname], 
									   fbeforelet)))), 
					    e')
		val fstklet2 = LetTExp (fstk, 
					  LabTyp (tvs, 
						  TupleTyp [t1', 
							    StringTyp]), 
					  NewExp (tvs, 
						  TupleTyp [t1',
							    StringTyp], 
						  VarExp (Id.makeid "Ustk")), 
					  flet)
		val fafterlet2 = LetTExp (fafter, 
					    LabTyp (tvs, 
						    TupleTyp [t2', 
							      StackTyp,
							      StringTyp]), 
					  NewExp (tvs, 
						  TupleTyp [t2',
							    StackTyp,
							    StringTyp], 
						  VarExp (Id.makeid "Uafter")), 
					  fstklet2)
		val fbeforelet2 = LetTExp (fbefore, 
					    LabTyp (tvs, 
						    TupleTyp [t1', 
							      StackTyp,
							      StringTyp]), 
					  NewExp (tvs, 
						  TupleTyp [t1',
							    StackTyp,
							    StringTyp], 
						  VarExp (Id.makeid "Ubefore")),
					  fafterlet2)
	    in 
		if S.eq_typ t2'' t2
		then (t, fbeforelet2)
		else trans_err pos ("FunDec: " ^ not_eq t2'' t2)
	    end
	  | transDec' (S.InfFunDec _) =
	    trans_err pos "InfFunDec"
	  | transDec' (S.AdvDec _) = 
	    trans_err pos "AdvDec"
	  | transDec' (S.AnnotAdvDec (time, e1, x, t1b, y, z, e2)) =
	    let 
		val (pcpt, e1') = transLExp pos D P G e1
		val (tvs, t1) =	case pcpt of
				    S.PCTyp(s1, s2) => 
				    let 
					val (S.ForAllPolyTyp(tvs, t1)) = 
					    (case time of 
						 S.BeforeTime => s1
					       | S.AfterTime => s2)
				    in 
					(tvs, t1)
				    end
				  | _ => trans_err pos ("AdvDec: " ^ ppSTyp pcpt ^ " is not a pc typ")
		val tvs' = subList (S.FTV t1b) D
		val t1b' = transTyp pos (tvs'@D) t1b
		val e1'' = (let 
				val x2 = Id.freshid "x"
			    in 
				LetExp(case time of 
					   S.BeforeTime => [x2, Id.freshid "_", Id.freshid "_"]
					 | S.AfterTime => [Id.freshid "_", Id.freshid "_", x2], 
				       e1',
				       VarExp x2)
			    end)
		val (t2, e2') = transGExp pos 
					  (tvs'@D)
					 P 
					 (S.VarG(z,S.StringTyp)::
					  S.VarG(y,S.StackTyp)::
					  S.VarG(x,t1b)::
					  G) 
					 e2
		val (t, e') = transGExp pos D P G e
		val split = LetExp ([x,y,z], VarExp x, TupleExp [e2',VarExp y, VarExp z])
		val advice = AdvInstExp (AdvExp (e1'', tvs', x, TupleTyp [t1b',StackTyp,StringTyp] , split))
		val outerlet = LetTExp (Id.freshid "_", UnitTyp, advice, e')
	    in 
		if S.eq_poly_typ (S.ForAllPolyTyp (tvs, t1)) (S.ForAllPolyTyp (tvs', t1b))
		then if S.eq_typ t2 t1b
		     then (t, outerlet)
		     else trans_err pos ("AnnotAdvDec: " ^ not_eq t2 t1b)
		else trans_err pos "AnnotAdvDec: not eq"
	    end
	  | transDec' (S.CaseAdvDec (time, e1, x, t2, y, z, e2)) =
	    let 
		val (pcpt, e1') = transLExp pos D P G e1
		val a = Id.freshid "a"
		val (tvs, t1) = case pcpt of
				     S.PCTyp(s1, s2) => 
				     let 
					 val (S.ForAllPolyTyp(tvs, t1)) = 
					     (case time of 
						  S.BeforeTime => s1
						| S.AfterTime => s2)
				     in 
					 (tvs, t1)
				     end
				   | _ => trans_err pos ("CaseAdvDec: " ^ ppSTyp pcpt ^ " is not a pc typ")
					
		val t1' = transTyp pos (tvs@D) t1
		val tvs' = subList (S.FTV t2) D
		val t2' = transTyp pos (tvs'@D) t2
		val e1'' = (let 
				val x2 = Id.freshid "x"
			    in 
				LetExp(case time of 
					   S.BeforeTime => [x2, Id.freshid "_", Id.freshid "_"]
					 | S.AfterTime => [Id.freshid "_", Id.freshid "_", x2], 
				       e1',
				       VarExp x2)
			    end)
		val (t2b, e2') = transGExp pos
					   (tvs'@D)
					   P 
					   (S.VarG(z,S.StringTyp)::
					    S.VarG(y,S.StackTyp)::
					    S.VarG(x,t2)::
					    G) 
					   e2
		val (t, e') = transGExp pos D P G e
		val typecase = TypeCaseExp(a, 
					   VarTyp a, 
					   t1',
					   [(t2',e2'),
					    (VarTyp a, VarExp x)])
		val split = LetExp ([x,y,z], 
				    VarExp x, 
				    TupleExp[typecase,
					     VarExp y, 
					     VarExp z])
		val advice = AdvInstExp (AdvExp (e1'', 
						 tvs, 
						 x, 
						 TupleTyp [t1',
							   StackTyp,
							   StringTyp] ,
						 split))
		val outerlet = LetTExp (Id.freshid "_", 
					UnitTyp, 
					advice, 
					e')
	    in 
		if S.eq_typ t2 t2b
		then (t, outerlet)
		else trans_err pos "CaseAdvDec"
	    end
(*	  | transDec' (S.InfAdvDec (time, e1, x, y, z, e2)) =
	    raise TransError "InfAdvDec"*)

    in 
	transDec' d
    end

fun transProg (S.Prog e) =
    (let 
	val (t, e') = transGExp start_pos nil nil nil e 
	val U = LabExp U
	val a = Id.freshid "a"
	val astst =  TupleTyp [VarTyp a, StackTyp, StringTyp]
	val ast = TupleTyp [VarTyp a, StringTyp]
	val UstkExp = LetTExp(Id.makeid "Ustk", LabTyp ([a], ast), NewExp([a], ast, U), e')
	val UafterExp = LetTExp(Id.makeid "Uafter", LabTyp ([a], astst), NewExp([a], astst, U), UstkExp)
	val UbeforeExp = LetTExp(Id.makeid "Ubefore", LabTyp ([a], astst), NewExp([a], astst, U), UafterExp)
    in 
	(t, Prog UbeforeExp)
    end) handle (TransError s) => (print ("Translate Error: " ^ s ^ "\n" ^ ppSExp e ^ "\n"); (S.UnitTyp, Prog UnitExp))
	      | (S.SourceError s) => (print ("Translate Source Error: " ^ s ^ "\n" ^ ppSExp e ^ "\n"); (S.UnitTyp, Prog UnitExp))


end