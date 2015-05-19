structure Core :> CORE =
struct

open Util


type l = int
type var = Id.id
type tyvar = Id.id

val U = 0

exception CoreError of string
exception GenError
exception MGUError

datatype typ = UnitTyp
	     | StringTyp
	     | VarTyp of tyvar
	     | ArrTyp of typ * typ
	     | ForAllTyp of tyvar * typ
	     | LabTyp of tyvar list * typ
	     | PCTyp of tyvar list * typ
	     | AdvTyp
	     | StackTyp
	     | TupleTyp of typ list
	     | IntTyp
	     | BoolTyp

(*exception CoreDebugError of typ * typ *)


datatype exp = UnitExp
  | StringExp of string
  | VarExp of var
  | FunExp of var * typ * exp
  | AppExp of exp * exp
  | TyFunExp of tyvar * exp
  | TyAppExp of exp * typ
  | TupleExp of exp list
  | LetExp of var list * exp * exp
  | LabExp of l
  | PCExp of exp * typ list * exp
  | NewExp of tyvar list * typ * exp 
  | AdvInstExp of exp
  | AdvExp of exp * tyvar list * var * typ * exp
  | TypeCaseExp of tyvar * typ * typ * (typ * exp) list
  | SetExp of exp list
  | UnionExp of exp * exp
  | StackExp
  | NilStExp
  | PtStExp of exp * typ list * exp * exp 
  | StoreExp of exp * typ list * exp * exp
  | StkCaseExp of exp * (pat * exp) list
  | IntExp of int
  | PlusExp of exp * exp
  | BoolExp of bool
  | IfExp of exp * exp * exp
  | PrintExp of exp
  | ItoSExp of exp
  | ConcatExp of exp * exp 
  | FixExp of var * typ * exp
  | AbortExp 
  | EqExp of exp * exp
  | PosExp of Util.pos * exp
		

and pat = NilPat
  | PtPat of exp * tyvar list * var * typ * pat
  | VarPat of var
  | AllPat of pat

and prog =
    Prog of exp

and G = VarG of var * typ 
  | LabG of l * tyvar list * typ
 
fun cmp_pair ((a,b)::pair) c d =
    if Id.eqid a c andalso Id.eqid b d 
    then true
    else cmp_pair pair c d
  | cmp_pair nil c d =
    Id.eqid c d
    
(* you can use t1 in place of t2 *)
fun eq_typ UnitTyp UnitTyp = 
    true
  | eq_typ StringTyp StringTyp = 
    true
  | eq_typ (VarTyp a) (VarTyp b) = 
    Id.eqid a b
  | eq_typ (ArrTyp (t1, t2)) (ArrTyp(t3, t4)) =
    eq_typ t3 t1 andalso eq_typ t2 t4
  | eq_typ (ForAllTyp (a, t1)) (ForAllTyp (b, t2)) =
    let 
	val c = VarTyp (Id.freshid "c")
    in
	eq_typ (tysubstTyp c a t1) (tysubstTyp c b t2)
    end
  | eq_typ (LabTyp (ts1, t1)) (LabTyp (ts2, t2)) =
    if length ts1 = length ts2
    then let 
	    val cs = map VarTyp (map (fn _ => Id.freshid "c") ts1)
	in
	    eq_typ (tysubstTypList cs ts1 t1) (tysubstTypList cs ts2 t2)
	end
    else false
  | eq_typ (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2)) =
    check_core_gen_typ tvs2 t2 tvs1 t1
  | eq_typ AdvTyp AdvTyp = 
    true
  | eq_typ StackTyp StackTyp = 
    true
  | eq_typ (TupleTyp ts1) (TupleTyp ts2) =
    List.all (fn(t1, t2) => eq_typ t1 t2) (zip ts1 ts2)
  | eq_typ IntTyp IntTyp =
    true
  | eq_typ BoolTyp BoolTyp =
    true
  | eq_typ _ _ = 
    false

and join_typ UnitTyp UnitTyp =
    UnitTyp
  | join_typ StringTyp StringTyp =
    StringTyp
  | join_typ (VarTyp a) (VarTyp b) =
    if Id.eqid a b 
    then VarTyp a
    else raise CoreError "join_typ VarTyp"
  | join_typ (ArrTyp (t1a, t2a)) (ArrTyp (t1b, t2b)) =
    ArrTyp ((meet_typ t1a t1b), (join_typ t2a t2b))
  | join_typ (ForAllTyp (a, t1)) (ForAllTyp (b,t2)) =
     let 
	val c = VarTyp (Id.freshid "c")
    in
	join_typ (tysubstTyp c a t1) (tysubstTyp c b t2)
    end
  | join_typ (LabTyp (tvs1, t1)) (LabTyp (tvs2, t2)) =
    if length tvs1 = length tvs2 
    then let 
	    val cs = map (fn _ => Id.freshid "c") tvs1
	    val cvs = map VarTyp cs
	in
	    LabTyp (cs, join_typ (tysubstTypList cvs tvs1 t1) (tysubstTypList cvs tvs2 t2))
	end
    else raise CoreError "join LabTyp: not equal lengths"
  | join_typ (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2)) =
    PCTyp (gen_typ tvs1 t1 tvs2 t2)
  | join_typ AdvTyp AdvTyp =
    AdvTyp
  | join_typ StackTyp StackTyp =
    StackTyp
  | join_typ (TupleTyp ts1) (TupleTyp ts2) =
    if length ts1 = length ts2 
    then TupleTyp (map (fn(t1, t2) => join_typ t1 t2) (zip ts1 ts2))
    else raise CoreError "join TupleTyp"
  | join_typ IntTyp IntTyp =
    IntTyp
  | join_typ BoolTyp BoolTyp =
    BoolTyp
  | join_typ t1 t2 = 
    raise CoreError "join_typ bad"

and join_typ_list (t::ts) =
    foldl (fn (t', gent) =>
	      join_typ t' gent)
	  t
	  ts
  | join_typ_list nil = 
    raise CoreError "join_typs"


and meet_typ UnitTyp UnitTyp =
    UnitTyp
  | meet_typ StringTyp StringTyp =
    StringTyp
  | meet_typ (VarTyp a) (VarTyp b) =
    if Id.eqid a b 
    then VarTyp a
    else raise CoreError "meet_typ VarTyp"
  | meet_typ (ArrTyp (t1a, t2a)) (ArrTyp (t1b, t2b)) =
    ArrTyp ((join_typ t1a t1b), (meet_typ t2a t2b))
  | meet_typ (ForAllTyp (a, t1)) (ForAllTyp (b,t2)) =
     let 
	val c = VarTyp (Id.freshid "c")
    in
	meet_typ (tysubstTyp c a t1) (tysubstTyp c b t2)
    end
  | meet_typ (LabTyp (tvs1, t1)) (LabTyp (tvs2, t2)) =
    if length tvs1 = length tvs2 
    then let 
	    val cs = map (fn _ => Id.freshid "c") tvs1
	    val cvs = map VarTyp cs
	in
	    LabTyp (cs, meet_typ (tysubstTypList cvs tvs1 t1) (tysubstTypList cvs tvs2 t2))
	end
    else raise CoreError "join LabTyp: not equal lengths"
  | meet_typ (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2)) =
    PCTyp (meet_gen tvs1 t1 tvs2 t2)
  | meet_typ AdvTyp AdvTyp =
    AdvTyp
  | meet_typ StackTyp StackTyp =
    StackTyp
  | meet_typ (TupleTyp ts1) (TupleTyp ts2) =
    if length ts1 = length ts2 
    then TupleTyp (map (fn(t1, t2) => meet_typ t1 t2) (zip ts1 ts2))
    else raise CoreError "join TupleTyp"
  | meet_typ IntTyp IntTyp =
    IntTyp
  | meet_typ BoolTyp BoolTyp =
    BoolTyp
  | meet_typ t1 t2 = 
    raise CoreError "join_typ bad"

and meet_gen tvs1 t1 tvs2 t2 =
    let 
	val cs = map (fn _ => VarTyp (Id.freshid "c")) tvs1
	val ds = map (fn _ => VarTyp (Id.freshid "d")) tvs2
	val subst = (mgu (tysubstTypList cs tvs1 t1) (tysubstTypList ds tvs2 t2) handle MGUError => raise CoreError "bad meet_gen")	    
	val t = tysubstTypList (map #1 subst) (map #2 subst) t1
    in
	(FTV t, t)
    end
	




and FTV t =
    let
	fun FTV' btvs UnitTyp = 
	    nil
	  | FTV' btvs StringTyp = 
	    nil
	  | FTV' btvs (VarTyp a) =
	    if inList a btvs
	    then nil
	    else [a]
	  | FTV' btvs (ArrTyp (t1, t2)) =
	    (FTV' btvs t1) @ (FTV' btvs t2)
	  | FTV' btvs (ForAllTyp (a,t)) =
	    FTV' (a::btvs) t
	  | FTV' btvs (LabTyp(bs, t)) =
	    FTV' (bs@btvs) t
	  | FTV' btvs (PCTyp (bs, t)) =
	    FTV' (bs@btvs) t
	  | FTV' btvs AdvTyp =
	    nil
	  | FTV' btvs StackTyp = 
	    nil
	  | FTV' btvs (TupleTyp typs) =
	    foldr (fn(t, ftvs) => (FTV' btvs t)@ftvs) nil typs
	  | FTV' btvs IntTyp =
	    nil
	  | FTV' btvs BoolTyp = 
	    nil
    in 
	FTV' nil t
    end

and BTVPat NilPat =
    nil
  | BTVPat (PtPat(e, tvs, x, t, p)) =
    tvs@BTVPat p
  | BTVPat (VarPat _) =
    nil
  | BTVPat (AllPat p) =
    BTVPat p



and FV e =
    let 
	fun FV' bvs UnitExp =
	    nil
	  | FV' bvs (StringExp _)  =
	    nil
	  | FV' bvs (VarExp x) =
	    if inList x bvs
	    then nil
	    else [x]
	  | FV' bvs (FunExp(x, _, e)) =
	    FV' (x::bvs) e
	  | FV' bvs (AppExp(e1, e2)) = 
	    (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs (TyFunExp(_, e)) =
	    FV' bvs e
	  | FV' bvs (TyAppExp(e, _)) =
	    FV' bvs e
	  | FV' bvs (TupleExp(elist)) =
	    foldr (fn(e,fvs) => (FV' bvs e)@fvs) nil elist
	  | FV' bvs (LetExp(xs, e1, e2)) =
	    (FV' (xs@bvs) e1) @ (FV' bvs e2)
	  | FV' bvs (LabExp _) =
	    nil
	  | FV' bvs (PCExp(e1, _, e2)) =
	     (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs (NewExp(_, _, e)) =
	    FV' bvs e
	  | FV' bvs (AdvInstExp e) =
	    FV' bvs e
	  | FV' bvs (AdvExp(e1, _, x, _, e2)) =
	    (FV' bvs e1) @ (FV' (x::bvs) e2)
	  | FV' bvs (TypeCaseExp(_, _, _, tes)) =
	    map_concat (fn (t,e) => FV' bvs e) tes
	  | FV' bvs (SetExp (elist)) =
	    foldr (fn(e,fvs) => (FV' bvs e)@fvs) nil elist
	  | FV' bvs (UnionExp (e1, e2)) =
	    (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs StackExp =
	     nil
	  | FV' bvs NilStExp =
	    nil
	  | FV' bvs (PtStExp(e1, _, e2, e3)) =
	    (FV' bvs e1) @ (FV' bvs e2) @ (FV' bvs e3)
	  | FV' bvs (StoreExp(e1, _, e2, e3)) =
	    (FV' bvs e1) @ (FV' bvs e2) @ (FV' bvs e3)
	  | FV' bvs (StkCaseExp(e1, pes)) =
	    (FV' bvs e1) @ (map_concat (fn (p,e) => FV' ((BVPat p)@bvs) e) pes)
	  | FV' bvs (IntExp i) =
	    nil
	  | FV' bvs (PlusExp (e1, e2)) =
	    (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs (BoolExp b) =
	    nil
	  | FV' bvs (IfExp (e1, e2, e3)) =
	    (FV' bvs e1) @ (FV' bvs e2) @ (FV' bvs e3)
	  | FV' bvs (PrintExp e) =
	    FV' bvs e
	  | FV' bvs (ItoSExp e) =
	    FV' bvs e
	  | FV' bvs (ConcatExp (e1, e2)) =
	    (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs (FixExp (f, t, e)) =
	    FV' (f::bvs) e
	  | FV' bvs AbortExp =
	    nil
	  | FV' bvs (EqExp (e1, e2)) =
	    (FV' bvs e1) @ (FV' bvs e2)
	  | FV' bvs (PosExp (_, e)) =
	    FV' bvs e
    in 
	FV' nil e
    end

and BVPat NilPat =
    nil
    | BVPat (PtPat(e1, tvs, x, t, p)) =
      x::(BVPat p)
    | BVPat (VarPat x) =
      [x]
    | BVPat (AllPat p) =
      BVPat p

and tysubstTyp t a =
    let 
	fun tysubstTyp' UnitTyp =
	    UnitTyp
	  | tysubstTyp' StringTyp =
	    StringTyp
	  | tysubstTyp' (VarTyp b) =
	    if Id.eqid a b
	    then t
	    else VarTyp b
	  | tysubstTyp' (ArrTyp (t1, t2)) =
	    ArrTyp (tysubstTyp' t1, tysubstTyp' t2)
	  | tysubstTyp' (ForAllTyp (tv, t')) =
	    if Id.eqid a tv
	    then ForAllTyp (tv, t')
	    else let 
		    val (tv'::nil, t'') = tysubstTyp'' t [tv] t'
		in 
		    ForAllTyp (tv', tysubstTyp' t'')
		end
	  | tysubstTyp' (LabTyp (tvs, t')) =
	    if inList a tvs
	    then LabTyp (tvs, t')
	    else 
		let 
		   val (tvs', t'') = tysubstTyp'' t tvs t'
		in 
		    LabTyp (tvs',tysubstTyp' t'')
		end
	  | tysubstTyp' (PCTyp(tvs, t')) =
	    if inList a tvs
	    then PCTyp (tvs, t')
	    else 
		let 
		   val (tvs', t'') = tysubstTyp'' t tvs t'
		in 
		    PCTyp (tvs',tysubstTyp' t'')
		end
	  | tysubstTyp' AdvTyp =
	    AdvTyp
	  | tysubstTyp' StackTyp = 
	    StackTyp
	  | tysubstTyp' (TupleTyp (ts)) =
	    TupleTyp (map tysubstTyp' ts)
	  | tysubstTyp' IntTyp =
	    IntTyp
	  | tysubstTyp' BoolTyp =
	    BoolTyp

    in 
	tysubstTyp'
    end

and tysubstTyp'' t (tv::tvs) t' =
    if inList tv (FTV t)
    then let 
	    val tv' = Id.cloneid tv
	    val t'' = tysubstTyp (VarTyp tv') tv t'
	    val (tvs', t''') = tysubstTyp'' t tvs t''
	in 
	    (tv'::tvs', t''')
	end
    else 
	let 
	    val (tvs', t'') = tysubstTyp'' t tvs t'
	in 
	   (tv::tvs', t'')
	end
  | tysubstTyp'' t nil t' =
    (nil, t')
			


and tysubstTypList (t::ts) (tv::tvs) t' =
    tysubstTypList ts tvs (tysubstTyp t tv t')
  | tysubstTypList nil nil t = t
  | tysubstTypList _ _ _ = raise CoreError "tysubstTypList"
	



and substExp'' e (x::xs) e' =
    if inList x (FV e)
    then let 
	    val x' = Id.cloneid x
	    val e'' = substExp (VarExp x') x e'
	    val (xs', e''') = substExp'' e xs e''
	in 
	    (x'::xs', e''')
	end
    else 
	let 
	    val (xs', e'') = substExp'' e xs e'
	in 
	   (x::xs', e'')
	end
  | substExp'' e nil e' =
    (nil, e')
	   
and substExpList (v::vs) (x::xs) e =
    substExpList vs xs (substExp v x e)
  | substExpList nil nil e = e
  | substExpList _ _ _ = raise CoreError "substExpList"

and substExp v x =
    let
	fun substExp' UnitExp = 
	    UnitExp
	  | substExp' (StringExp s) = 
	    StringExp s
	  | substExp' (VarExp y) =
	    if Id.eqid x y
	    then v
	    else VarExp y
	  | substExp' (FunExp (y,t,e)) =
	    if Id.eqid x y 
	    then FunExp (y,t,e)
	    else let
		    val (y'::nil, e') = substExp'' v [y] e
		in 
		    FunExp(y', t, substExp' e')
		end
	  | substExp' (AppExp (e1, e2)) =
	    AppExp (substExp' e1, substExp' e2)
	  | substExp' (TyFunExp (a,e)) =
	    TyFunExp (a, substExp' e)
	  | substExp' (TyAppExp (e, t)) =
	    TyAppExp (substExp' e, t)
	  | substExp' (TupleExp es) =
	    TupleExp (map substExp' es)
	  | substExp' (LetExp (ys, e1, e2)) =
	    if List.all (fn(y) => not (Id.eqid x y)) ys
	    then LetExp (ys, substExp' e1, substExp' e2)
	    else let 
		    val (ys', e1') = substExp'' v ys e1
		in 
		    LetExp (ys', substExp' e1', e2)
		end
	  | substExp' (LabExp l) =
	    LabExp l
	  | substExp' (PCExp (e1,ts,e2)) =
	    PCExp (substExp' e1, ts, substExp' e2)
	  | substExp' (NewExp (ts, t, e)) =
	    NewExp (ts, t, substExp' e)
	  | substExp' (AdvInstExp e) =
	    AdvInstExp (substExp' e)
	  | substExp' (AdvExp (e1, ts, y, t, e2)) =
	    if Id.eqid x y
	    then AdvExp (substExp' e1, ts, y, t, e2)
	    else let 
		    val (y', e2') = substExp'' v [y] e2
		in 
		    AdvExp (substExp' e1, ts, y, t, substExp' e2')
		end
	  | substExp' (TypeCaseExp (ts, t1, t2, tes)) =
	    TypeCaseExp (ts, t1, t2, map (fn (t,e) => (t, substExp' e)) tes)
	  | substExp' (SetExp es) =
	    SetExp (map substExp' es)
	  | substExp' (UnionExp (e1, e2)) =
	    UnionExp (substExp' e1, substExp' e2)
	  | substExp' StackExp =
	    StackExp
	  | substExp' NilStExp =
	    NilStExp
	  | substExp' (PtStExp (e1, ts, e2, e3)) =
	    PtStExp (substExp' e1, ts, substExp' e2, substExp' e3)
	  | substExp' (StoreExp (e1, ts, e2, e3)) =
	    StoreExp (substExp' e1, ts, substExp' e2, substExp' e3)
	  | substExp' (StkCaseExp (e1, pes)) =
	    let 
		val pes' = map (fn (p,e) => 
				   let
				       val xs = BVPat p
				       val (xs', e') = if inList x xs
						       then (xs, e)
						       else let 
							       val (xs', e') = substExp'' v xs e
							   in 
							       (xs', substExp' e')
							   end
				       val p' = substPat v x (substPatList (map VarExp xs') xs p)
				   in 
				       (p',e')
				   end) 
			       pes
	    in 
		StkCaseExp (substExp' e1, pes')
	    end
	  | substExp' (IntExp i) =
	    IntExp i
	  | substExp' (PlusExp (e1, e2)) =
	    PlusExp (substExp' e1, substExp' e2)
	  | substExp' (BoolExp b) =
	    BoolExp b
	  | substExp' (IfExp (e1, e2, e3)) =
		IfExp (substExp' e1, substExp' e2, substExp' e3)
	  | substExp' (PrintExp e) =
	    PrintExp (substExp' e)
	  | substExp' (ItoSExp e) =
	    ItoSExp (substExp' e)
	  | substExp' (ConcatExp (e1, e2)) =
	    ConcatExp (substExp' e1, substExp' e2)
	  | substExp' (FixExp (f,t,e)) =
	    if Id.eqid x f
	    then FixExp (f,t,e)
	    else let
		    val (f'::nil, e') = substExp'' v [f] e
		in 
		    FixExp(f', t, substExp' e')
		end
	  | substExp' AbortExp =
	    AbortExp
	  | substExp' (EqExp (e1, e2)) =
	    EqExp (substExp' e1, substExp' e2)
	  | substExp' (PosExp (_, e)) =
	    substExp' e
    in 
	(*if isVal v
	then *)substExp'
	(*else raise CoreError "substExp: not a value"*)
    end


and substPat v x =
    let 
	fun substPat' NilPat =
	    NilPat
	  | substPat' (PtPat (e, ts, y, t, p)) =
	    PtPat(substExp v x e, ts, y, t, substPat' p)
	  | substPat' (VarPat y) =
	    VarPat y
	  | substPat' (AllPat p) =
		AllPat (substPat' p)
    in 
	substPat'
    end

and substPatList (v::vs) (x::xs) p =
    substPatList vs xs (substPat v x p)
  | substPatList nil nil p = p
  | substPatList _ _ _ = raise CoreError "substPatList"



and tysubstExp'' t (tv::tvs) e =
    if inList tv (FTV t)
    then let 
	    val tv' = Id.cloneid tv
	    val e' = tysubstExp (VarTyp tv') tv e
	    val (tvs', e'') = tysubstExp'' t tvs e'
	in 
	    (tv'::tvs', e'')
	end
    else 
	let 
	    val (tvs', e') = tysubstExp'' t tvs e
	in 
	   (tv::tvs', e')
	end
  | tysubstExp'' t nil e =
    (nil, e)
	

and tysubstExp t a =
    let
	fun tysubstExp' UnitExp = 
	    UnitExp
	  | tysubstExp' (StringExp s) = 
	    StringExp s
	  | tysubstExp' (VarExp x) =
	    VarExp x
	  | tysubstExp' (FunExp (x,t',e)) =
	    FunExp(x, tysubstTyp t a t', tysubstExp' e)
	  | tysubstExp' (AppExp (e1, e2)) =
	    AppExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (TyFunExp (b,e)) =
	    if Id.eqid a b 
	    then TyFunExp (b,e)
	    else let
		    val (b'::nil, e') = tysubstExp'' t [b] e
		in 
		    TyFunExp(b', tysubstExp' e')
		end
	  | tysubstExp' (TyAppExp (e, t')) =
	    TyAppExp (tysubstExp' e, tysubstTyp t a t')
	  | tysubstExp' (TupleExp es) =
	    TupleExp (map tysubstExp' es)
	  | tysubstExp' (LetExp (ys, e1, e2)) =
	    LetExp (ys, tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (LabExp l) =
	    LabExp l
	  | tysubstExp' (PCExp (e1,ts,e2)) =
	    PCExp (tysubstExp' e1, map (tysubstTyp t a) ts, tysubstExp' e2)
	  | tysubstExp' (NewExp (tvs, t', e)) =
	    let 
		val (tvs', t'') = tysubstTyp'' t tvs t'
	    in
		NewExp (tvs', tysubstTyp t a t'', tysubstExp' e)
	    end
	  | tysubstExp' (AdvInstExp e) =
	    AdvInstExp (tysubstExp' e)
	  | tysubstExp' (AdvExp (e1, tvs, y, t', e2)) =
	    if inList a tvs
	    then AdvExp (tysubstExp' e1, tvs, y, t', e2)
	    else let 
		    val (tvs', t'') = tysubstTyp'' t tvs t'
		    val e2' = tysubstExpList (map VarTyp tvs') tvs e2
		in 
		    AdvExp (tysubstExp' e1, tvs', y, tysubstTyp t a t'', tysubstExp' e2')
		end
	  | tysubstExp' (TypeCaseExp (b, t1, t2, tes)) =
	    let 
		val (b', t1') = if Id.eqid a b
				  then (b, t1)
				  else let 
					  val (b', t1') = tysubstTyp'' t [b] t1
				      in 
					  (hd b', tysubstTyp t a t1')
				      end
		val tes' = map (fn (t',e) => let
				       val tvs = FTV t'
				       val (tvs', e') = if inList a tvs
							then (tvs, e)
							else let 
								val (tvs', e') = tysubstExp'' t tvs e
							    in 
								(tvs', tysubstExp' e')
							    end
				       val t'' = tysubstTyp t a (tysubstTypList (map VarTyp tvs') tvs t')
				   in 
				       (t'', e')
				   end)
			       tes
	    in 
		TypeCaseExp (b', t1', tysubstTyp t a t2, tes')
	    end
	  | tysubstExp' (SetExp es) =
	    SetExp (map tysubstExp' es)
	  | tysubstExp' (UnionExp (e1, e2)) =
	    UnionExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' StackExp =
	    StackExp
	  | tysubstExp' NilStExp =
	    NilStExp
	  | tysubstExp' (PtStExp (e1, ts, e2, e3)) =
	    PtStExp (tysubstExp' e1, map (tysubstTyp t a) ts, tysubstExp' e2, tysubstExp' e3)
	  | tysubstExp' (StoreExp (e1, ts, e2, e3)) =
	    StoreExp (tysubstExp' e1, map (tysubstTyp t a) ts, tysubstExp' e2, tysubstExp' e3)
	  | tysubstExp' (StkCaseExp (e1, pes)) =
	    let
		val pes' = map (fn (p,e) => let 
				       val tvs = BTVPat p
				       val (tvs', e') = if inList a tvs
							then (tvs, e)
							else let 
								val (tvs', e') = tysubstExp'' t tvs e
							    in 
								(tvs', tysubstExp' e')
							    end
				       val p' = tysubstPat t a (tysubstPatList (map VarTyp tvs') tvs p)
				   in 
				       (p', e')
				   end)
			       pes
	    in
		StkCaseExp(tysubstExp' e1, pes')
	    end
	  | tysubstExp' (IntExp i) =
	    IntExp i
	  | tysubstExp' (PlusExp (e1, e2)) =
	    PlusExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (BoolExp b) =
	    BoolExp b
	  | tysubstExp' (IfExp (e1, e2, e3)) =
		IfExp (tysubstExp' e1, tysubstExp' e2, tysubstExp' e3)
	  | tysubstExp' (PrintExp e) =
	    PrintExp (tysubstExp' e)
	  | tysubstExp' (ItoSExp e) =
	    ItoSExp (tysubstExp' e)
	  | tysubstExp' (ConcatExp (e1, e2)) =
	    ConcatExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (FixExp (f,t',e)) =
	    FixExp(f, tysubstTyp t a t', tysubstExp' e)
	  | tysubstExp' AbortExp =
	    AbortExp
	  | tysubstExp' (EqExp (e1, e2)) =
	    EqExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (PosExp (_, e)) =
	    tysubstExp' e

    in 
	tysubstExp'
    end
			


and tysubstExpList (t::ts) (tv::tvs) e =
    tysubstExpList ts tvs (tysubstExp t tv e)
  | tysubstExpList nil nil e = e
  | tysubstExpList _ _ _ = raise CoreError "tysubstExpList"

and tysubstPat t a =
    let 
	fun tysubstPat' NilPat =
	    NilPat
	  | tysubstPat' (PtPat (e, tvs, y, t, p)) =
	    if inList a tvs
	    then PtPat(tysubstExp t a e, tvs, y, t, tysubstPat' p)
	    else let 
	    	    val (tvs', t') = tysubstTyp'' t tvs t
		in 
		    PtPat(tysubstExp t a e, tvs', y, tysubstTyp t a t', tysubstPat' p)
		end 
	  | tysubstPat' (VarPat x) =
	    VarPat x
	  | tysubstPat' (AllPat p) =
	    AllPat (tysubstPat' p)
    in 
	tysubstPat'
    end


and tysubstPatList (t::ts) (tv::tvs) p =
    tysubstPatList ts tvs (tysubstPat t tv p)
  | tysubstPatList nil nil p = p
  | tysubstPatList _ _ _ = raise CoreError "tysubstPatList"



and inList a (b::D) =
    if Id.eqid a b
    then true
    else inList a D
  | inList a nil =
    false

	    
and isVal UnitExp = true
  | isVal (StringExp _) = true
  | isVal (FunExp _) = true
  | isVal (TyFunExp _) = true
  | isVal (TupleExp es) = List.all (fn (e) => isVal e) es
  | isVal (LabExp _) = true
  | isVal (AdvExp (e,_,_,_,_)) = isVal e
  | isVal (SetExp es) = List.all (fn (e) => isVal e) es
  | isVal NilStExp = true
  | isVal (PtStExp (e1,_,e2,e3)) = isVal e1 
				   andalso isVal e2 
				   andalso isVal e3
  | isVal (IntExp _) = 
    true
  | isVal (BoolExp _) =
    true
  | isVal _ = false

and isValPat NilPat = true
  | isValPat (PtPat(e,_,_,_,p)) = isVal e 
				  andalso isValPat p
  | isValPat (VarPat _) = true
  | isValPat (AllPat p) = isValPat p

and combineSubst' a ((t, b)::subs) =
    if Id.eqid a b 
    then SOME t
    else combineSubst' a subs
  | combineSubst' a nil =
    NONE
    
and combineSubst'' a ((t, b)::subs) =
    if Id.eqid a b 
    then SOME t
    else combineSubst'' a subs
  | combineSubst'' a nil =
    NONE
    

and combineSubst subs:(typ*tyvar) list =
    let 
	fun combineSubst' subs1 ((t,a)::subs2) =
	    (case (combineSubst'' a subs1) of 
		 SOME t' => if eq_typ t' t
			    then combineSubst' subs1 subs2
			    else raise GenError
	       | NONE => combineSubst' ((t,a)::subs1) subs2)
	  | combineSubst' subs1 nil =
	    subs1
    in 
	combineSubst' nil subs
    end
	
and findSubst tvs1 =
    let 
	fun findSubst' pair tvs1 UnitTyp UnitTyp = 
	    nil
	  | findSubst' pair tvs1 StringTyp StringTyp =
	    nil
	  | findSubst' pair tvs1 (VarTyp a) (VarTyp b) =
	    if inList a tvs1 
	    then [(VarTyp b, a)]
	    else (if cmp_pair pair a b
		  then nil
		  else raise GenError)
	  | findSubst' pair tvs1 (VarTyp a) t2 =
	    if inList a tvs1
	    then [(t2, a)]
	    else raise GenError
	  | findSubst' pair tvs1 (ArrTyp (t1, t2)) (ArrTyp(t3, t4)) =
	    combineSubst (findSubst' pair tvs1 t1 t3)@(findSubst' pair tvs1 t2 t4)
	  | findSubst' pair tvs1 (ForAllTyp (a, t1)) (ForAllTyp (b, t2)) =
	    let 
		val tvs1' = subList tvs1 [a]
	    in 
		findSubst' ((a,b)::pair) tvs1' t1 t2
	    end
	  | findSubst' pair tvs1 (LabTyp (tvs3, t1)) (LabTyp (tvs4, t2)) =
	    let 
		val tvs1' = subList tvs1 tvs3
(* val tvs2' = subList tvs2 tvs4 *)
	    in 
		if length tvs3 = length tvs4
		then findSubst' ((zip tvs3 tvs4)@pair) tvs1' t1 t2
		else raise CoreError "findsubst LabTyp"
	    end
	  | findSubst' pair tvs1 (PCTyp (tvs3, t1)) (PCTyp (tvs4, t2)) =
	    let 
		val tvs1' = subList tvs1 tvs3
	(* val tvs2' = subList tvs2 tvs4 *)
	    in 
		if length tvs3 = length tvs4
		then findSubst' ((zip tvs3 tvs4)@pair) tvs1' t1 t2
		else raise CoreError "findsubst PCTyp"
	    end
	  | findSubst' pair tvs1 AdvTyp AdvTyp =
	    nil
	  | findSubst' pair tvs1 StackTyp StackTyp =
	    nil
	  | findSubst' pair tvs1 (TupleTyp ts1) (TupleTyp ts2) =
	    if length ts1 = length ts2
	    then let 
		    val t1t2s = zip ts1 ts2
		in 
		    combineSubst (map_concat (fn (t1, t2) => findSubst' pair tvs1 t1 t2) t1t2s)
		end
	    else raise CoreError "findsubst TupleTyp"
	  | findSubst' pair tvs1 IntTyp IntTyp =
	     nil
	  | findSubst' pair tvs1 BoolTyp BoolTyp =
	     nil
	  | findSubst' pair tvs1 t1 t2 = 
	    raise GenError
    in 
	findSubst' nil tvs1
    end 
	
and lookup_ctxt ctxt t1 t2 =
    let 
	fun lookup_ctxt' ((ct1, ct2,a)::t) t1 t2 =
	    if (eq_typ ct1 t1) andalso (eq_typ ct2 t2)
	    then (ctxt, VarTyp a)
	    else lookup_ctxt' t t1 t2
	  | lookup_ctxt' nil t1 t2 = 
	    let 
		val b = Id.freshid "a"
	    in 
		((t1, t2, b)::ctxt, VarTyp b)
	    end
    in
	lookup_ctxt' ctxt t1 t2
    end

and gen_typ tvs1 t1 tvs2 t2 = 
    let 
	fun gen_typ' ctxt UnitTyp UnitTyp =
	    (ctxt, UnitTyp)
	  | gen_typ' ctxt StringTyp StringTyp =
	    (ctxt, StringTyp)
	  | gen_typ' ctxt (ArrTyp(t1, t2)) (ArrTyp(t3, t4)) =
	    let 
		val (ctxt1, t1') = gen_typ' ctxt t1 t3
		val (ctxt2, t2') = gen_typ' ctxt1 t2 t4
	    in 
		(ctxt2, ArrTyp(t1', t2'))
	    end
	  | gen_typ' ctxt (ForAllTyp (a1, t1)) (ForAllTyp (a2, t2)) = 
	    let 
		val a' = Id.freshid "a"
		val t1' = tysubstTyp (VarTyp a') a1 t1
		val t2' = tysubstTyp (VarTyp a') a2 t2
		val (ctxt', t') = gen_typ' ctxt t1' t2'
	    in 
		(ctxt', ForAllTyp (a', t'))
	    end
	  | gen_typ' ctxt (LabTyp (tvs1, t1)) (LabTyp (tvs2, t2)) =
	    if length tvs1 = length tvs2
	    then let 
		    val tvs' = map (new_var) tvs1
		    val t1' = tysubstTypList (map VarTyp tvs') tvs1 t1
		    val t2' = tysubstTypList (map VarTyp tvs') tvs2 t2
		    val (ctxt', t') = gen_typ' ctxt t1' t2'
		in 
		    (ctxt', LabTyp (tvs', t'))
		end
	    else lookup_ctxt ctxt (LabTyp (tvs1, t1)) (LabTyp (tvs2, t2))
	  | gen_typ' ctxt (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2)) =
	    if length tvs1 = length tvs2
	    then let 
		    val tvs' = map (new_var) tvs1
		    val t1' = tysubstTypList (map VarTyp tvs') tvs1 t1
		    val t2' = tysubstTypList (map VarTyp tvs') tvs2 t2
		    val (ctxt', t') = gen_typ' ctxt t1' t2'
		in 
		    (ctxt', PCTyp (tvs', t'))
		end
	    else  lookup_ctxt ctxt (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2))
	  | gen_typ' ctxt AdvTyp AdvTyp =
	    (ctxt, AdvTyp)
	  | gen_typ' ctxt StackTyp StackTyp =
	    (ctxt, StackTyp) 
	  | gen_typ' ctxt (TupleTyp ts1) (TupleTyp ts2) =
	    if length ts1 = length ts2
	    then let
		    val (ctxt', ts') = foldl (fn ((t1,t2), (ctxt',ts')) => let
						     val (ctxt'', t') = gen_typ' ctxt' t1 t2
						 in 
						     (ctxt'',ts'@[t'])
						 end)
					     (ctxt, nil)
					     (zip ts1 ts2)
		in 
		    (ctxt', TupleTyp (ts'))
		end
	    else raise CoreError "gen_typ TupleTyp"
	  | gen_typ' ctxt IntTyp IntTyp =
	    (ctxt, IntTyp)
	  | gen_typ' ctxt BoolTyp BoolTyp =
	    (ctxt, BoolTyp)
	  | gen_typ' ctxt t1 t2 =
	    lookup_ctxt ctxt t1 t2 

	val (ctxt, t) = gen_typ' nil t1 t2
	val tvs = map #3 ctxt
    in 
	(tvs, t)
    end

and gen_list ((tvs,t)::tvsts) =
    foldl (fn ((tvs, t), (gentvs, gent)) =>
	      gen_typ tvs t gentvs gent)
	  (tvs,t)
	  tvsts
  | gen_list nil = 
    raise GenError

and tysubstG t a (LabG(l, tvs, t')::G) = 
    if inList a tvs
    then LabG(l,tvs,t')::(tysubstG t a G)
    else 
	let 
	    val (tvs', t'') = tysubstTyp'' t tvs t'
	in 
	    LabG(l, tvs',tysubstTyp t a t'')::(tysubstG t a G)
	end
  | tysubstG t a (VarG(x,t')::G) =
    VarG(x, tysubstTyp t a t')::(tysubstG t a G)
  | tysubstG t a nil =
    nil


and tysubstGList (t::ts) (tv::tvs) G =
    tysubstGList ts tvs (tysubstG t tv G)
  | tysubstGList nil nil G = G
  | tysubstGList _ _ _ = raise CoreError "tysubstGList"
	

and new_var x = Id.freshid "c"

and mgu t1 t2 =
    let 
	val ftvs1 = FTV t1
	val ftvs2 = FTV t2
	fun mgu' T UnitTyp UnitTyp =
	    nil
	| mgu' T StringTyp StringTyp =
	    nil
	| mgu' T AdvTyp AdvTyp =
	    nil
	| mgu' T StackTyp StackTyp =
	    nil
	| mgu' T IntTyp IntTyp =
	    nil
	| mgu' T BoolTyp BoolTyp =
	    nil
	| mgu' T (ArrTyp (t1a, t2a)) (ArrTyp (t1b, t2b)) =
	  mgu' (mgu' T t1a t1b) t2a t2b
	| mgu' T (ForAllTyp (tv1, t1)) (ForAllTyp (tv2, t2)) =
	  let 
	      val tv = Id.freshid "c"
	      val t1' = tysubstTyp (VarTyp tv) tv1 t1
	      val t2' = tysubstTyp (VarTyp tv) tv1 t2
	  in 
	      mgu' T t1' t2'
	  end
	| mgu' T (LabTyp (tvs1, t1)) (LabTyp (tvs2, t2)) =
	  if length tvs1 = length tvs2 
	  then let 
		  val tvs = map (fn (_) => Id.freshid "c") tvs1
		  val t1' = tysubstTypList (map VarTyp tvs) tvs1 t1
		  val t2' = tysubstTypList (map VarTyp tvs) tvs2 t2
	      in 
		  mgu' T t1' t2'
	      end
	  else raise MGUError
	| mgu' T (PCTyp (tvs1, t1)) (PCTyp (tvs2, t2)) =
	  if length tvs1 = length tvs2 
	  then let 
		  val tvs = map (fn (_) => Id.freshid "c") tvs1
		  val t1' = tysubstTypList (map VarTyp tvs) tvs1 t1
		  val t2' = tysubstTypList (map VarTyp tvs) tvs2 t2
	      in 
		  mgu' T t1' t2'
	      end
	  else raise MGUError
	| mgu' T (TupleTyp ts1) (TupleTyp ts2) =
	  foldl (fn ((t1, t2), Ti) => mgu' Ti t1 t2) T (zip ts1 ts2)
	| mgu' T (VarTyp a) (VarTyp b) =
	  if not (inList a ftvs1) andalso not (inList b ftvs2)
	  then (if Id.eqid a b
		then nil
		else raise MGUError)
	  else (if inList a ftvs1 
		then (if inList a (map #2 T)
		      then mgu' T (tysubstTypList (map #1 T) (map #2 T) (VarTyp a)) (VarTyp b)
		      else (if inList a (FTV (VarTyp b))
			    then raise MGUError
			    else (VarTyp b, a)::T))
		else (if inList b (map #2 T)
		      then mgu' T (tysubstTypList (map #1 T) (map #2 T) (VarTyp b)) (VarTyp a)
		      else (if inList b (FTV (VarTyp a))
			    then raise MGUError
			    else (VarTyp a, b)::T)))
	| mgu' T (VarTyp a) t2 =
	  if inList a ftvs1 
	  then (if inList a (map #2 T)
		then mgu' T (tysubstTypList (map #1 T) (map #2 T) (VarTyp a)) t2
		else (if inList a (FTV t2)
		      then raise MGUError
		      else (t2, a)::T))
	  else raise MGUError
	| mgu' T t1 (VarTyp b) =
	  if inList b ftvs2
	  then (if inList b (map #2 T)
		then mgu' T (tysubstTypList (map #1 T) (map #2 T) (VarTyp b)) t1
		else (if inList b (FTV t1)
		      then raise MGUError
		      else (t1, b)::T))
	  else raise MGUError
	| mgu' T t1 t2 =
	  raise MGUError
    in
	mgu' nil t1 t2
    end

and check_core_gen_typ tvs1 t1 tvs2 t2 = 
    let 
	val ttvs = findSubst tvs1 t2 t2
	val ts = map #1 ttvs
	val tvs = map #1 ttvs
    in 
	(*if List.all (fn(ti) => typeTyp pos D ti) ts*)
	true
    end
end