structure TypeCheck :> TYPECHECK =
struct

open Core PrettyPrint Util

exception TypeError of string

fun not_eq t1 t2 = 
    ppCTyp t1 ^ " != " ^ ppCTyp t2

fun type_err pos s = 
  raise (TypeError ("Position " ^ string_of_pos pos ^ ": " ^ s)) 
    
fun lookupVarG pos x (VarG(y,t)::G) = 
    if (Id.eqid x y) 
    then t 
    else lookupVarG pos x G
  | lookupVarG pos x (_::G) = 
    lookupVarG pos x G
  | lookupVarG pos x nil = 
    type_err pos ("lookupVarG " ^ ppVar x)

fun lookupLabG pos x (LabG(y,tvs,t)::G) = 
    if (x = y) 
    then (tvs,t) 
    else lookupLabG pos x G
  | lookupLabG pos x (_::G) = 
    lookupLabG pos x G
  | lookupLabG pos x nil = 
    type_err pos "lookupLabG"

val Ubefore = Id.makeid "Ubefore"
val Ustk = Id.makeid "Ustk"
val Uafter = Id.makeid "Uafter"

fun completePatMatch pos ps = 
  let  
      fun completePatMatch' true nil = 
	  (false, nil)
	| completePatMatch' false nil = 
	  type_err pos ("CompletePatMatch: match not complete")
	| completePatMatch' _ (NilPat::ps) =
	  completePatMatch' true ps
	| completePatMatch' _ ((VarPat _)::ps) =
	  (true,nil)
	| completePatMatch' hasNil ((AllPat p)::ps) =
	  let
	      val (b, ps') = completePatMatch' hasNil ps
	  in 
	      (b, p::ps')
	  end
	| completePatMatch' hasNil ((PtPat(LetExp ([_, x, _],
						   TupleExp [SetExp [VarExp Ubefore],
							     SetExp [VarExp Ustk],
							     SetExp [VarExp Uafter]], VarExp y),
					   _,
					   _,
					   _, 
					   p))::ps) =
	  if (Id.eqid x y)
	  then let
		  val (b, ps') = completePatMatch' hasNil ps
	      in
		  (b,p::ps')
	      end
	  else completePatMatch' hasNil ps
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
		fun hasVarTyp (ftvs::ftvss) ((VarTyp b)::ts) =
		    if inList b ftvs
		    then true
		    else hasVarTyp ftvss ts
		  | hasVarTyp (_::ftvss) (_::ts) =
		    hasVarTyp ftvss ts
		  | hasVarTyp _ _ =
		    false
		fun hasBaseTyp t (t'::ts) =
		    if eq_typ t t'
		    then true
		    else hasBaseTyp t ts
		  | hasBaseTyp _ nil =
		    false
		fun filterArrTyp (ftvs::ftvss) ((ArrTyp (t1, t2))::ts) =
		    let 
			val (ftvss', t1s::t2s::nil) = filterArrTyp ftvss ts
		    in 
			(ftvs::ftvss', [t1::t1s, t2::t2s])
		    end
		  | filterArrTyp (ftvs::ftvss) (t::ts) =
		    filterArrTyp ftvss ts
		  | filterArrTyp _ _ = 
		    (nil, [nil, nil])
		fun filterTupleTyp (ftvs::ftvss) ((TupleTyp ts)::ts') =
		    let 
			val (ftvss', tss) = filterTupleTyp ftvss ts'
		    in 
			case tss of
			    nil => 
			    (ftvs::ftvss', [ts])
			  | tss' => 
			    (ftvs::ftvss', map (fn(ts,ts') => ts::ts')
					       (zip ts tss))
		    end
		  | filterTupleTyp (ftvs::ftvss) (t::ts) =
		    filterTupleTyp ftvss ts
		  | filterTupleTyp _ _ = 
		    (nil, nil)
		fun hasTupleTyp (ftvss, tss) =
		    List.all (fn (ts) => completeTypMatch' ftvss ts) tss
		fun filterForAllTyp (ftvs::ftvss) ((ForAllTyp (tv, t))::ts) =
		    let 
			val (ftvss', ts') = filterForAllTyp ftvss ts
		    in 
			((subList ftvs [tv])::ftvss', t::ts')
		    end
		  | filterForAllTyp (ftvs::ftvss) (t::ts) =
		    filterForAllTyp ftvss ts
		  | filterForAllTyp _ _ = 
		    (nil, nil)
		fun filterPCTyp (ftvs::ftvss) ((PCTyp (tvs, t))::ts) =
		    let 
			val (ftvss', ts') = filterPCTyp ftvss ts
		    in 
			((subList ftvs tvs)::ftvss', t::ts')
		    end
		  | filterPCTyp (ftvs::ftvss) (t::ts) =
		    filterPCTyp ftvss ts
		  | filterPCTyp _ _ = 
		    (nil, nil)
		fun filterLabTyp (ftvs::ftvss) ((LabTyp (tvs, t))::ts) =
		    let 
			val (ftvss', ts') = filterLabTyp ftvss ts
		    in 
			((subList ftvs tvs)::ftvss', t::ts')
		    end
		  | filterLabTyp (ftvs::ftvss) (t::ts) =
		    filterLabTyp ftvss ts
		  | filterLabTyp _ _ = 
		    (nil, nil)
		fun hasComplexTyp (ftvss, ts) =
		    completeTypMatch' ftvss ts
	    in 
		if hasVarTyp ftvss ts
		then true
		else (if hasBaseTyp UnitTyp ts 
			 andalso hasBaseTyp StringTyp ts 
			 andalso hasBaseTyp StackTyp ts
			 andalso hasBaseTyp AdvTyp ts
			 andalso hasBaseTyp IntTyp ts 
			 andalso hasBaseTyp BoolTyp ts
			 andalso hasTupleTyp (filterArrTyp ftvss ts)
			 andalso hasTupleTyp (filterTupleTyp ftvss ts)
			 andalso hasComplexTyp (filterForAllTyp ftvss ts)
			 andalso hasComplexTyp (filterLabTyp ftvss ts)
			 andalso hasComplexTyp (filterPCTyp ftvss ts)
		      then false
		      else type_err pos ("CompleteTypMatch: match not complete"))
	    end
	val ftvss = map (FTV) ts
    in
	completeTypMatch' ftvss ts
    end
	    
	    


fun typeTyp pos D =
    let
	fun typeTyp' UnitTyp = 
	    true
	  | typeTyp' StringTyp = 
	    true
	  | typeTyp' (VarTyp a) =
	    inList a D
	  | typeTyp' (ArrTyp (t1, t2)) =
	    typeTyp' t1 andalso typeTyp' t2
	  | typeTyp' (ForAllTyp (tvs, t)) =
	    typeTyp pos (tvs::D) t
	  | typeTyp' (LabTyp (tvs, t)) =
	    typeTyp pos (tvs @ D) t
	  | typeTyp' (PCTyp (tvs, t)) =
	    typeTyp pos (tvs @ D) t
	  | typeTyp' AdvTyp =
	    true
	  | typeTyp' StackTyp =
	    true
	  | typeTyp' (TupleTyp ts) =
	    List.all (fn(t) => typeTyp' t) ts
	  | typeTyp' IntTyp =
	    true
	  | typeTyp' BoolTyp =
	    true
    in 
	typeTyp'
    end

fun typeExp pos D G =
    let
	fun typeExp' UnitExp = 
	    UnitTyp
	  | typeExp' (StringExp s) =
	    StringTyp
	  | typeExp' (VarExp x) =
	    lookupVarG pos x G
	  | typeExp' (FunExp (x, t, e)) =
	    if typeTyp pos D t
	    then 
		let 
		    val t' = typeExp pos D (VarG(x,t)::G) e
		in 
		    ArrTyp (t, t')
		end
	    else type_err pos ("FunExp: bad type " ^ ppCTyp t)
	  | typeExp' (AppExp (e1, e2)) =
	    let 
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		case t1 of 
		    ArrTyp (t1a, t2a) =>
		    if eq_typ t2 t1a
		    then t2a
		    else type_err pos ("AppExp: " ^ not_eq t1a t2)
		  | _ => type_err pos ("AppExp: not -> " ^ ppCTyp t1)
	    end
	  | typeExp' (TyFunExp (a,e)) =
	    let 
		val t = typeExp pos (a::D) G e
	    in 
		ForAllTyp(a,t)
	    end
	  | typeExp' (TyAppExp (e, t)) =
	    let 
		val t' = typeExp' e
	    in 
		if typeTyp pos D t
		then case t' of
			 ForAllTyp(a,t'') => tysubstTyp t a t''
		       | _ => type_err pos ("TyAppExp: not forall " ^ ppCTyp t')
		else type_err pos ("TyAppExp: bad type " ^ ppCTyp t)
	    end
	  | typeExp' (TupleExp es) =
	    TupleTyp(map (fn(e) => typeExp' e) es)
	  | typeExp' (LetExp(xs, e1, e2)) = 
	    let 
		val t1 = typeExp' e1
	(*	val _ = print (ppCExp (LetExp(xs,e1,e2)) ^ "\n")*)
	    in
		case t1 of
		    TupleTyp ts => typeExp pos D (letHelp pos G xs ts) e2
		  | _ => type_err pos ("LetExp: not tuple " ^ ppCTyp t1)
	    end
	  | typeExp' (LabExp l) =
	    let
		val (tvs, t) = lookupLabG pos l G
	    in 
		LabTyp (tvs, t)
	    end
	  | typeExp' (PCExp (e1,ts,e2)) =
	    let 
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if List.all (fn(t) => typeTyp pos D t) ts
		then case t1 of 
			 LabTyp (tvs, t) => if eq_typ t2 (tysubstTypList ts tvs t)
					   then t2
					   else type_err pos ("PCExp: " ^ not_eq t2 (tysubstTypList ts tvs t))
						      
		       | _ => type_err pos ("PCTyp: not lab " ^ ppCTyp t1)
		else type_err pos ("PCExp: bad type")
	    end
	  | typeExp' (NewExp (tvs, t, e)) =
	    let
		val t' = typeExp' e
	    in 
		case t' of 
		    LabTyp (tvs', t'') => if check_gen_typ pos D tvs' t'' tvs t
					then LabTyp (tvs,t)
					else type_err pos ("NewExp: doesn't generalize " ^ ppCTyp t'' ^ " and " ^ ppCTyp t)
		  | _ => type_err pos ("NewExp: not label " ^ ppCTyp t')
	    end
	  | typeExp' (AdvInstExp e) =
	    let
		val t = typeExp' e
	    in 
		case t of 
		    AdvTyp => UnitTyp
		  | _ => type_err pos ("AdvInstExp: not advice " ^ ppCTyp t)
	    end
	  | typeExp' (AdvExp (e1, tvs, x, t, e2)) =
	    let 
		val t1 = typeExp' e1
		val (tvs', t') = case t1 of 
				     PCTyp (tvs', t') => (tvs', t') 
				   | _ => type_err pos ("AdvExp: not PCTyp " ^ ppCTyp t1)
		val t2 = typeExp pos (tvs @ D) (VarG(x,t)::G) e2
		val (tvs', t') = case t1 of
				     PCTyp (tvs', t') => (tvs', t') 
				   | _ => type_err pos ("AdvExp: not PCTyp " ^ ppCTyp t1)
	    in
		if eq_typ t t2
		then (if check_gen_typ pos D tvs t tvs' t'
		      then AdvTyp
		      else type_err pos ("AdvExp: not gen " ^ ppCTyp t ^ " and " ^ ppCTyp t'))
		else type_err pos ("AdvExp1: " ^ not_eq  t t2)
	    end
	  | typeExp' (TypeCaseExp(a, t1, t2, tes)) =
	    if typeTyp pos (a::D) t1
	    then if typeTyp pos D t2
		 then let 
			 val _ = if completeTypMatch pos (map #1 tes) then true else  type_err pos "TypeCaseExp: incomplete type match"
			 val Ds = map (fn (ti) => subList (FTV ti) D) (map #1 tes)
			 val Ts = map (fn (ti) => (SOME (mgu t2 ti) handle MGUError => NONE)) (map #1 tes)
			 val tis' = map (fn (SOME Ti, Di, ei) => 
					    SOME (typeExp pos 
						      (Di@D) 
						      (tysubstGList (map #1 Ti) (map #2 Ti) G) 
						      (tysubstExpList (map #1 Ti) (map #2 Ti) ei))
					  | (NONE, _, _) => NONE)
					(zip3 Ts Ds (map #2 tes))
			 val tis'' = map (fn (SOME Ti, ti) => 
					     SOME (tysubstTypList 
						       (map #1 Ti) 
						       (map #2 Ti) 
						       (tysubstTyp ti a t1))
					   | (NONE, _) => NONE) 
				     (zip Ts (map #1 tes))
		     in 
			 if List.all (fn (SOME ti', SOME ti'') => eq_typ ti' ti''
				       | (_, _) => true)
			    (zip tis' tis'')
			 then (if List.all (fn (Di, SOME Ts') => List.all (fn (r,d) => typeTyp pos (Di@D) r) Ts'
					     | (_, NONE) => true)
					   (zip Ds Ts)
			       then tysubstTyp t2 a t1
			       else type_err pos "TypeCheckExp: cod not closed")
			 else type_err pos "TypeCheckExp: not correct branch type"		    
		     end
		 else type_err pos ("TypeCaseExp: bad type " ^ ppCTyp t2)
	    else type_err pos ("TypeCaseExp: bad type " ^ ppCTyp t1)
	  | typeExp' (SetExp es) =
	    let 
		val ts = map typeExp' es
			 
		val tvsts = map (fn(t) => case t of LabTyp(tvs, t) => (tvs, t) | _ => type_err pos ("SetExp: bad type " ^ ppCTyp t) ) ts
		val (tvs', t) = gen_list tvsts
	    in 
		PCTyp (tvs',t)
	    end
	  | typeExp' (UnionExp (e1, e2)) =
	    let 
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		case t1 of
		    LabTyp (tvs, t1') =>
		    (case t2 of 
			 LabTyp (tvs', t2') => let 
			     val (tvs'',t) = gen_list [(tvs,t1'),(tvs',t2')]
			 in 
			     LabTyp (tvs'', t)
			 end
		       | _  => type_err pos ("UnionExp: bad type " ^ ppCTyp t1))
		  | _  => type_err pos ("UnionExp: bad type " ^ ppCTyp t1)
	    end
	  | typeExp' StackExp =
	    StackTyp
	  | typeExp' NilStExp = 
	    StackTyp
	  | typeExp' (PtStExp (e1, ts, e2, e3)) =
	    let 
		val t1 = typeExp' e1
		val t2 = typeExp' e2
		val t3 = typeExp' e3
	    in 
		if List.all (fn(t) => typeTyp pos D t) ts
		then case t1 of 
			 LabTyp (tvs, t) => 
			 if eq_typ t2 (tysubstTypList ts tvs t) 
			 then if eq_typ t3 StackTyp
			      then StackTyp
			      else type_err pos ("PtStExp: " ^ not_eq t3 StackTyp)
			 else type_err pos ("PtStExp: " ^ not_eq t2 (tysubstTypList ts tvs t))
			 | _ => type_err pos( "PtStExp: not label " ^ ppCTyp t1)
		else type_err pos "PtStExp: bad type " 
	    end
	  | typeExp' (StoreExp (e1, ts, e2, e3)) =
	    let 
		val t1 = typeExp' e1
		val t2 = typeExp' e2 
		val t3 = typeExp' e3
	    in 
		if List.all (fn(t) => typeTyp pos D t) ts
		then case t1 of 
			 LabTyp (tvs, t) => 
			 if eq_typ t2 (tysubstTypList ts tvs t)
			 then t3
			 else type_err pos ("PtStExp: " ^ not_eq t2 (tysubstTypList ts tvs t))
			 | _ => type_err pos ("PtStExp: not label " ^ ppCTyp t1)
		else type_err pos "PtStExp: bad type " 
	    end
	  | typeExp' (StkCaseExp (e1, pes)) =
	    let 
		val t1 = typeExp' e1
		val _ = if completePatMatch pos (map #1 pes) then true else type_err pos "StkCaseExp: incomplete stack match"
		val ts = map (fn (pi,ei) => let
				     val (Di, Gi) = typePat pos D G pi
				 in 
				     typeExp pos (Di@D) (Gi@G) ei
				 end)
			     pes
	    in 
		if eq_typ t1 StackTyp
		then (join_typ_list ts handle (CoreError s) => type_err pos "StkCaseExp: cases not all eq")
		else type_err pos ("StkCaseExp: " ^ not_eq t1 StackTyp)
	    end
	  | typeExp' (IntExp i) =
	    IntTyp
	  | typeExp' (PlusExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 IntTyp
		then (if eq_typ t2 IntTyp
		      then IntTyp
		      else type_err pos ("PlusExp: " ^ not_eq t2 IntTyp))
		else type_err pos ("PlusExp: " ^ not_eq t1 IntTyp)
	    end
	  | typeExp' (BoolExp b) =
	    BoolTyp
	  | typeExp' (IfExp (e1, e2, e3)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
		val t3 = typeExp' e3
	    in 
		if eq_typ t1 BoolTyp
		then (join_typ t2 t3 handle (CoreError s) => type_err pos ("IfExp: " ^ not_eq t2 t3))
		else type_err pos ("IfExp: " ^ not_eq t1 BoolTyp)
	    end
	  | typeExp' (PrintExp e) =
	    let
		val t = typeExp' e
	    in 
		if eq_typ t StringTyp 
		then UnitTyp
		else type_err pos ("PrintExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (ItoSExp e) =
	    let
		val t = typeExp' e
	    in 
		if eq_typ t IntTyp 
		then StringTyp
		else type_err pos ("PrintExp: " ^ not_eq t StringTyp)
	    end
	  | typeExp' (ConcatExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 StringTyp
		then (if eq_typ t2 StringTyp
		      then t1
		      else type_err pos ("ConcatExp: " ^ not_eq t2 StringTyp))
		else type_err pos ("ConcatExp: " ^ not_eq t1 StringTyp)
	    end
	  | typeExp' (FixExp (f, t, e)) =
	    let 
		val t' = typeExp pos D (VarG(f,t)::G) e
	    in 
		if eq_typ t' t
		then t
		else type_err pos ("FixExp: " ^ not_eq t' t)
	    end
	  | typeExp' AbortExp =
	    UnitTyp
	  | typeExp' (EqExp (e1, e2)) =
	    let
		val t1 = typeExp' e1
		val t2 = typeExp' e2
	    in 
		if eq_typ t1 StringTyp
		then (if eq_typ t2 StringTyp
		      then BoolTyp
		      else type_err pos ("EqExp: " ^ not_eq t2 StringTyp))
		else type_err pos ("EqExp: " ^ not_eq t1 StringTyp)
	    end
	  | typeExp' (PosExp (pos', e)) =
	    typeExp pos' D G e
    in 
	typeExp'
    end	

and typePat pos D G =
    let 
	fun typePat' NilPat =
	   (nil, nil)
	  | typePat' (PtPat(e1, tvs, x, t, p)) =
	    let 
		val t1 = typeExp pos D G e1
		val (tvs', t') = case t1 of 
				     PCTyp (tvs', t') => (tvs', t') 
				   | _ => type_err pos ("AdvExp: not PCTyp " ^ ppCTyp t1)
		val (D',G') = typePat' p
	    in 
		if check_gen_typ pos D tvs t tvs' t'
		then ((tvs @ D'), (VarG(x,t)::G'))
		else type_err pos ("PtPat: not gen " ^ ppList (map ppTyvar tvs) ^ "." ^ ppCTyp t ^ " and " ^ ppList (map ppTyvar tvs') ^ "." ^ ppCTyp t')
	    end
	  | typePat' (VarPat x) =
	    (nil, [VarG(x,StackTyp)])
	  | typePat' (AllPat p) =
	    typePat' p
    in 
	typePat'
	end
    

and letHelp pos G (x::x') (t::t') = 
    letHelp pos ((VarG(x,t))::G) x' t'
  | letHelp pos G nil nil = 
    G
  | letHelp pos G (x::x') nil = 
    type_err pos ("letHelp: var " ^ ppVar x)
  | letHelp pos G nil (t::t') = 
    type_err pos ("letHelp: type " ^ ppCTyp t)

and check_gen_typ pos D tvs1 t1 tvs2 t2=
   if typeTyp pos (tvs1@D) t1
    then (if typeTyp pos (tvs2@D) t2
	  then check_core_gen_typ tvs1 t1 tvs2 t2
	  else false)
   else false


fun typeProg (Prog e) = 
    let 
	val a = Id.freshid "a" 
    in 
	((typeExp start_pos nil [LabG(U, [a], VarTyp a)] e);true)
	handle (TypeError s) => (print ("Type Error: " ^ s ^ "\n"); false)
	     | (CoreError s) => (print ("Type Core Error: " ^ s ^ "\n"); false)
	    (* | (CoreDebugError (t1, t2)) => (print ("Type CoreDebug Error: " ^ ppCTyp t1 ^ " and " ^ ppCTyp t2 ^ "\n"); false)*)
   
    end


end