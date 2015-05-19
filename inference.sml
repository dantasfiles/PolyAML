structure Inference :> INFERENCE =
struct

open Source PrettyPrint Util
     
exception InferError of string

fun inf_err pos s = 
  raise (InferError ("Position " ^ string_of_pos pos ^ ": " ^ s)) 
    

fun not_eq t1 t2 = 
    ppSTyp t1 ^ " != " ^ ppSTyp t2

fun inferTyp pos T =
    let 
	fun inferTyp' (VarTyp a) (VarTyp b) =
	    if Id.eqid a b
	    then T
	    else inf_err pos ("VarTyp: not eq" ^ ppTyvar a ^ " != " ^ ppTyvar b)
	  | inferTyp' UnitTyp UnitTyp = 
	    T
	  | inferTyp' StringTyp StringTyp = 
	    T
	  | inferTyp' StackTyp StackTyp = 
	    T
	  | inferTyp' (ArrTyp (t1, t2)) (ArrTyp (t3, t4)) =
	    let 
		val T' = inferTyp' t1 t3
	    in 
		inferTyp pos T' t2 t4
	    end
	  | inferTyp' (PCTyp(ForAllPolyTyp(tvs1, t1), 
			     ForAllPolyTyp(tvs2, t2))) 
		      (PCTyp(ForAllPolyTyp(tvs3, t3),
			     ForAllPolyTyp(tvs4, t4))) =
		      let
			  val T' = inferTyp' (tysubstTypList (map VarTyp tvs3) tvs1 t1) t3
		      in 
			  inferTyp pos T' (tysubstTypList (map VarTyp tvs4) tvs2 t2) t4
		      end
	  | inferTyp' IntTyp IntTyp =
	    T
	  | inferTyp' BoolTyp BoolTyp =
	    T
	  | inferTyp' (InfVarTyp X) t =
	    if inList X (map #2 T)
	    then inferTyp' (inftysubstTypList (map #1 T) (map #2 T) (InfVarTyp X)) t
	    else (if inList X (FTV t)
		  then inf_err pos ("TyVar t: inList " ^ ppTyvar X)
		  else (inftysubstTypList (map #1 T) (map #2 T) t, X)::T)
	  | inferTyp' t (InfVarTyp X) =
	    inferTyp' (InfVarTyp X) t
	  | inferTyp' t1 t2 = 
	    inf_err pos ("inferTyp': " ^ ppSTyp t1 ^ " and " ^ ppSTyp t2)
    in 
	inferTyp'
    end
	
and inferGen pos T (ForAllPolyTyp (tvs, t1)) (ForAllPolyTyp (tvs',t2)) =
    let 
	val Xs = map (fn (a) => Id.freshid "X") tvs
    in
	inferTyp pos T (tysubstTypList (map InfVarTyp Xs) tvs t1) t2
    end
	
and inferLExp pos T D P G = 
    let 
	fun inferLExp' (VarExp x) =
	    let 
		val t = (lookupVarG x G) 
	    in 
		(VarExp x, t, T)
	    end
	  | inferLExp' UnitExp =
	    (UnitExp, UnitTyp, T)
	  | inferLExp' (StringExp s) = 
	    (StringExp s, StringTyp, T)
	  | inferLExp' (AnyPtExp) =
	    let 
		val a1 = Id.freshid "a"
		val a2 = Id.freshid "a"
	    in 
		(AnyPtExp, PCTyp(ForAllPolyTyp([a1], VarTyp a1),
				 ForAllPolyTyp([a2], VarTyp a2)), 
		 T)
	    end
	  | inferLExp' (FunsPtExp (fs, s1, s2)) =
	    if checkPolyTyp D s1
	    then (if checkPolyTyp D s2
		  then (if List.all (fn (f) => inList f P) fs
			then (let
				  val ss = map (fn (f) => lookupGenG f G) fs
				  val tvss = map #1 ss
				  val ts = map #2 ss
				  val t1s = map (fn (ArrTyp(t1, t2)) => t1 
						  | t => inf_err pos ("timePtExp: " ^ ppSTyp t ^ " not ->")) ts
				  val t2s = map (fn (ArrTyp(t1, t2)) => t2 
						  | t => inf_err pos ("timePtExp: " ^ ppSTyp t ^ " not ->")) ts
					    
				  val Tn = foldl (fn ((tvs, t1, t2),Ti) => let
							 val Ti' = inferGen pos Ti s1 (ForAllPolyTyp(tvs, t1))
							 val Ti'' = inferGen pos Ti' s2 (ForAllPolyTyp(tvs, t2))
						     in 
							 Ti''
						     end)
						 T
						 (zip3 tvss t1s t2s)
			      in 
				  (FunsPtExp (fs, s1, s2), 
				   PCTyp (s1, s2),
				   Tn)
			      end)
			else inf_err pos ("TimePtExp Before: " ^ ppList (map ppVar fs) ^ " not in P"))
		  else inf_err pos  ("TimePtExp: bad type " ^ ppSPolyTyp s2))
	    else inf_err pos ("TimePtExp: bad type " ^ ppSPolyTyp s1)
	  | inferLExp' (TyAnnExp (e, t2)) =
	    let 
		val (e', t1, T') = inferGExp pos T D P G e
		val T'' = inferTyp pos T' t1 t2
	    in 
		(e', t2, T'') 
	    end
	  | inferLExp' (IntExp i) =
	    (IntExp i, IntTyp, T)
	  | inferLExp' (BoolExp b) =
	    (BoolExp b, BoolTyp, T)
	  | inferLExp' (PosExp (pos', e)) =
	    inferLExp pos' T D P G e
	  | inferLExp' _ = 
	    inf_err pos "inferLExp"
    in 
	inferLExp'
    end
		  
		  
and  inferGExp pos T D P G =
    let 
	fun inferGExp' (VarExp x) =
	    if isVarG x G
	    then let 
		    val t = lookupVarG x G
		in 
		    (VarExp x, t, T)
		end
	    else let
		    val (tvs, t) = lookupGenG x G
		    val Xs = map (fn (tv) => Id.freshid "X") tvs
		    val XVars = map InfVarTyp Xs
		    val t' = tysubstTypList XVars tvs t
		in 
		    (TyAppExp(x, XVars), t', T)
		end
	  | inferGExp' (AppExp (e1, e2)) = 
	    let 
		val (e1', t1, T2) = inferGExp' e1
		val (e2', t2, T3) = inferGExp pos T2 D P G e2
		val X = Id.freshid "X"
		val T4 = inferTyp pos T3 t1 (ArrTyp(t2, InfVarTyp X))
	    in 
		(AppExp (e1', e2'), InfVarTyp X, T4)
	    end
	  | inferGExp' (LetExp (d, e)) =
	    let 
		val (d', P', G', T') = inferDec pos T D P G d
		val (e', t, T'') = inferGExp pos T' D (P'@P) (G'@G) e
	    in 
		(LetExp (d', e'), 
		 t, 
		 T'')
	    end
	  | inferGExp' (StkCaseExp (e1, pes)) =
	    let 
		val (e1', t1, T0) = inferGExp' e1
		val T00 = inferTyp pos T0 t1 StackTyp
		val (p0', e0', t0, T0'', pes') = case pes of 
					    (p0,e0)::pes' => let 
						val (p0', T0', D0, G0) = inferPat pos T00 D P G p0
						val (e0', t0, T0'') = inferGExp pos T0' (D0@D) P (G0@G) e0
					    in 
						(p0', e0', t0, T0'', pes')
					    end
					  | _ => raise InferError "StkCaseExp: impossible"
		val (pes', Tn'') = foldl (fn ((pi, ei), (pes', oldT)) => 
				     let 
					 val (pi', Ti, Di, Gi) = inferPat pos oldT D P G pi
					 val (ei', ti, Ti') = inferGExp pos Ti (Di@D) P (Gi@G) ei
					 val Ti'' = inferTyp pos Ti' ti t0
				     in
					 (pes'@[(pi',ei')], Ti'')
				     end)
				 (nil,T0'') pes
	    in
		(StkCaseExp(e1', pes'), t0, Tn'')
	    end
	  | inferGExp' (TypeCaseExp (t, a, tes)) =
	    if inList a D
	    then (if checkTyp D t
		  then (let 
			    val (tes', Tn) = foldl (fn ((ti, ei), (tes', Tprev)) => 
						       let 
							   val Di = subList (FTV ti) D
							   val (ei', ti', Ti) = inferGExp pos Tprev (Di@D) P (tysubstG ti a G) ei
							   val Ti' = inferTyp pos Ti ti' (tysubstTyp ti a t)
						       in 
							   if inList a (FTV ti)
							   then inf_err pos ("TypeCaseExp: " ^ ppTyvar a ^ " in " ^ ppSTyp ti)
							   else (tes'@[(ti,ei')], Ti')
						       end)
						   (nil, T) tes
			in 
			    (TypeCaseExp(t, a, tes'), t, Tn)
			end)
		  else inf_err pos ("TypeCaseExp: bad type " ^ ppSTyp t))
	    else inf_err pos ("TypeCaseExp: " ^ ppTyvar a ^ " not in D")
	  | inferGExp' (PlusExp (e1, e2)) =
	    let 
		val (e1', t1, T') = inferGExp' e1
		val (e2', t2, T'') = inferGExp pos T' D P G e2
		val T''' = inferTyp pos T'' t1 IntTyp
		val T'''' = inferTyp pos T''' t2 IntTyp 
	    in 
		(PlusExp (e1', e2'), t1, T'''')
	    end
	  | inferGExp' (IfExp (e1, e2, e3)) =
	    let
		val (e1', t1, T') = inferGExp' e1
		val (e2', t2, T'') = inferGExp pos T' D P G e2
		val (e3', t3, T''') = inferGExp pos T'' D P G e3
		(*val _ = print ("lala: " ^ ppSTyp t1)*)
		val T4 = inferTyp pos T''' t1 BoolTyp
		val T5 = inferTyp pos T4 t2 t3
		(*val _ = print ("lala: " ^ ppSTyp t2)*)
		(*val _ = print ("lala2: " ^ ppSTyp t3)*)
	    in 
		(IfExp(e1', e2', e3'), t2, T5)
	    end
	  | inferGExp' (PrintExp e) =
	    let
		val (e', t, T') = inferGExp' e
		val T'' = inferTyp pos T' t StringTyp
	    in 
		(PrintExp e', UnitTyp, T'')
	    end
	  | inferGExp' (ItoSExp e) =
	    let
		val (e', t, T') = inferGExp' e
		val T'' = inferTyp pos T' t IntTyp
	    in 
		(ItoSExp e', StringTyp, T'')
	    end
	  | inferGExp' (ConcatExp (e1, e2)) =
	    let 
		val (e1', t1, T') = inferGExp' e1
		val (e2', t2, T'') = inferGExp pos T' D P G e2
		val T''' = inferTyp pos T'' t1 StringTyp
		val T'''' = inferTyp pos T''' t2 StringTyp 
	    in 
		(ConcatExp (e1', e2'), t1, T'''')
	    end
	  | inferGExp' (SeqExp (e1, e2)) =
	    let
		val (e1', t1, T') = inferGExp' e1
		val (e2', t2, T'') = inferGExp pos T' D P G e2
		val T''' = inferTyp pos T'' t1 UnitTyp
	    in 
		(SeqExp(e1', e2'), t2, T''')
	    end
	  | inferGExp' (TyAppExp (e, ts)) =
	    inf_err pos "TyAppExp"
	  | inferGExp' AbortExp =
	    (AbortExp, UnitTyp, T)
	  | inferGExp' (EqExp (e1, e2)) =
	    let 
		val (e1', t1, T') = inferGExp' e1
		val (e2', t2, T'') = inferGExp pos T' D P G e2
		val T''' = inferTyp pos T'' t1 StringTyp
		val T'''' = inferTyp pos T''' t2 StringTyp 
	    in 
		(EqExp (e1', e2'), BoolTyp, T'''')
	    end
	  | inferGExp' (PosExp (pos', e)) =
	    inferGExp pos' T D P G e
	  | inferGExp' e =
	    inferLExp pos T D P G e
    in 
	inferGExp'
    end

and inferDec pos T D P G =
    let
	fun inferDec' (FunDec(f, x, t1, t2, e)) =
	    let 
		val tvs = subList (FTV(t2)@FTV(t1)) D
		val (e', t3, T') = inferGExp pos T (tvs@D) (f::P) (VarG(x,t1)::VarG(f,ArrTyp(t1,t2))::G) e
		val T'' = inferTyp pos T' t2 t3

		val (tvs', t) = gen (inftysubstGList (map #1 T'') 
						     (map #2 T'') 
						     G) 
				    (inftysubstTypList (map #1 T'') 
						       (map #2 T'') 
						       (ArrTyp (t1, t2)))
	    in 
		(FunDec(f, x, t1, t2, e'), [f], [GenG(f,tvs',t)], T'')
	    end
	  | inferDec' (InfFunDec (f, x, e)) =
	    let 
		val X = Id.freshid "X"
		val Xt = InfVarTyp X
		val Y = Id.freshid "Y"
		val Yt = InfVarTyp Y
		val (e', t, T') = inferGExp pos T D (f::P) (VarG(x,Xt)::VarG(f,ArrTyp(Xt,Yt))::G) e
		val T'' = inferTyp pos T' Yt t 
	(*	val _ = print ("T'': " ^ ppInferT T'' ^ "\n") *)
		val G' = inftysubstGList (map #1 T'')
					 (map #2 T'') 
					 G
		val t' = inftysubstTypList (map #1 T'') 
					   (map #2 T'') 
					   (ArrTyp (Xt, Yt))
		val (tvs, t'') = gen G' t' 
	    in 
		(FunDec(f, x, Xt, Yt, e'), [f], [GenG(f,tvs,t'')], T'')
	    end
	  | inferDec' (AdvDec (time, e1, x, y, z, e2)) =
	    let
		val (e1', pcpt, T') = inferLExp pos T D P G e1
		val (tvs, t1) = case pcpt of
				    PCTyp (ForAllPolyTyp(tvsa, ta), 
					   ForAllPolyTyp(tvsb, tb)) => (case time of 
									   BeforeTime => (tvsa, ta)
									 | AfterTime => (tvsb, tb))
				  | _ => inf_err pos ("InfAdvDec: " ^ ppSTyp pcpt ^ " not PCTyp")
		val (e2', t2, T'') = inferGExp pos T' 
					       D 
					       P 
					       (VarG(z, StringTyp)::
						VarG(y,StackTyp)::
						VarG(x, t1)::
						G) 
					       e2
		val T''' = inferTyp pos T'' t1 t2
	    in 
		(AnnotAdvDec (time, e1', x, t1, y, z, e2'), 
		 nil, nil, T''')
	    end
	  | inferDec' (AnnotAdvDec (time, e1, x, t3, y, z, e2)) =
	    let
		val (e1', pcpt, T') = inferLExp pos T D P G e1
		val (tvs, t1) = case pcpt of
				    PCTyp (ForAllPolyTyp(tvsa, ta), 
					   ForAllPolyTyp(tvsb, tb)) => (case time of 
									    BeforeTime => (tvsa, ta)
									  | AfterTime => (tvsb, tb))
				  | _ => inf_err pos ("InfAdvDec: " ^ ppSTyp pcpt ^ " not PCTyp")
		val tvs' = subList (FTV t3) D
		val s1 = ForAllPolyTyp(tvs,t1)
		val s2 = ForAllPolyTyp(tvs',t3)
		val (e2', t2, T'') = inferGExp pos 
					       T' 
					       (tvs'@D)
					       P 
					       (VarG(z, StringTyp)::
						VarG(y,StackTyp)::
						VarG(x, t3)::
						G) 
					       e2
		val T''' = inferTyp pos T'' t3 t2
	(*	val T'''' = inferTyp T''' t1 t3*)
		(*val _ = print (ppSTyp t1 ^ " and " ^ ppSTyp t3 ^ "\n")*)
	    in 
		if eq_poly_typ s1 s2
		then 
		    (AnnotAdvDec (time, e1', x, t3, y, z, e2'), (*!!!!!!!*)
		     nil, nil, T''')
		else inf_err pos ("AnnotAdvDec" ^ not_eq t1 t3)
	    end
	  | inferDec' (CaseAdvDec (time, e1, x, t1, y, z, e2)) =
	    let
		val tvs = subList (FTV t1) D
		val (e1', pcpt, T') = inferLExp pos T D P G e1
		val (e2', t2, T'') = inferGExp pos
					       T' 
					       (tvs@D)
					       P 
					       (VarG(z, StringTyp)::
						VarG(y,StackTyp)::
						VarG(x, t1)::
						G) 
					       e2
		val T''' = inferTyp pos T'' t1 t2
	    in 
		(CaseAdvDec (time, e1', x, t1, y, z, e2'), 
		 nil, nil, T''')
	    end
    in 
	inferDec' 
    end

and inferPat pos T D P G =
    let
	fun inferPat' NilPat =
	    (NilPat, 
	     T,
	     nil, 
	     nil)
	  | inferPat' (VarPat x) =
	    (VarPat x, 
	     T,
	     nil,
	     [VarG(x, StackTyp)])
	  | inferPat' (AllPat p) =
	    let 
		val (p', T', D', G') = inferPat' p
	    in 
		(AllPat p', T', D', G')
	    end
	  | inferPat' (PtPat (e, x, z, p)) =
	    let 
		val (e',t,T') = inferLExp pos T D P G e
		val (tvs, t') = case t of 
				   PCTyp (ForAllPolyTyp(tvs, t'), s) => (tvs, t')
				 | _ => inf_err pos ("PtPat: " ^ ppSTyp t ^ " not PCD")
		val (p', T'', D', G') = inferPat pos T' D P G p
		(*val _ = print ("lala: " ^ ppSTyp t')*)
	    in
		(AnnotPtPat(e', x, t', z, p'), 
		 T'', 
		 D',
		 VarG(z,StringTyp)::VarG(x,t')::G')
	    end
	  | inferPat' (AnnotPtPat (e, x, t3, z, p)) =
	    let 
		val (e', t, T') = inferLExp pos T D P G e
		val (tvs, t') = case t of 
				   PCTyp (ForAllPolyTyp(tvs, t'), s) => (tvs, t')
				 | _ => inf_err pos ("PtPat: " ^ ppSTyp t ^ " not PCD")
		val tvs' = subList (FTV t3) D
		val s1 = ForAllPolyTyp (tvs, t')
		val s2 = ForAllPolyTyp (tvs', t3)
		val (p', T'', D', G') = inferPat pos T' D P G p
		(*val _ = print ("lala: " ^ ppSTyp t')*)
	    in
		if eq_poly_typ s1 s2
		then (AnnotPtPat(e', x, t', z, p'), 
		      T'', 
		      (tvs@D'), 
		      VarG(z,StringTyp)::VarG(x,t')::G')
		else inf_err pos "AnnotPtPat: s1 and s2 not equal"
	    end
	    in 
	inferPat'
    end

fun inferDebug (Prog e) = 
    inferGExp start_pos nil nil nil nil e

fun inferProg (Prog e) =
    (let 
	val (e', t, T) = inferGExp start_pos nil nil nil nil e
	val ts = map #1 T
	val Xs = map #2 T
	val e'' = inftysubstExpList ts Xs e'
	val t' = inftysubstTypList ts Xs t
    in 
	(Prog e'', t')
     end) handle (InferError s) => (print ("Infer Error: " ^ s ^ "\n"); (Prog UnitExp, UnitTyp))

end
