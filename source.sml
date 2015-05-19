structure Source :> SOURCE =
struct

open Util

type var = Id.id
type tyvar = Id.id
type inftyvar = Id.id

exception SourceError of string
exception GenError

datatype polytyp = 
	 ForAllPolyTyp of tyvar list * typ
			  
and typ = 
    VarTyp of tyvar
  | UnitTyp
  | StringTyp 
  | StackTyp
  | ArrTyp of typ * typ
  | PCTyp of polytyp * polytyp
  | InfVarTyp of inftyvar
  | IntTyp
  | BoolTyp

and time = 
    BeforeTime
  | AfterTime

   
and exp = 
    VarExp of var
  | UnitExp 
  | StringExp of string
  | AppExp of exp * exp
  | LetExp of dec * exp
  | StkCaseExp of exp * (pat * exp) list
  | TypeCaseExp of typ * tyvar * (typ * exp) list
  | FunsPtExp of var list * polytyp * polytyp
  | AnyPtExp
  | TyAnnExp of exp * typ
  | TyAppExp of var * typ list
  | IntExp of int
  | PlusExp of exp * exp
  | BoolExp of bool
  | IfExp of exp * exp * exp
  | PrintExp of exp
  | ItoSExp of exp
  | ConcatExp of exp * exp 
  | SeqExp of exp * exp
  | AbortExp
  | EqExp of exp * exp
  | PosExp of pos * exp
		
  
and pat = 
    NilPat
  | VarPat of var
  | AllPat of pat
  | PtPat of exp * var * var * pat
  | AnnotPtPat of exp * var * typ * var * pat

and dec =
   FunDec of var * var * typ * typ * exp
  | InfFunDec of var * var * exp
  | AdvDec of time * exp * var * var * var * exp
  | AnnotAdvDec of time * exp * var * typ * var * var * exp
  | CaseAdvDec of time * exp * var * typ * var * var * exp

and prog = 
    Prog of exp

datatype G = VarG of var * typ 
	   | GenG of var * tyvar list * typ

fun inList id (h::t) =
    if Id.eqid h id
    then true
    else inList id t
  | inList id nil =
    false

fun cmp_pair ((a,b)::pair) c d =
    if Id.eqid a c andalso Id.eqid b d 
    then true
    else cmp_pair pair c d
  | cmp_pair nil c d =
    Id.eqid c d
    
fun eq_typ' pair (VarTyp a) (VarTyp b) =
    cmp_pair pair a b
  | eq_typ' pair UnitTyp UnitTyp =
    true
  | eq_typ' pair StringTyp StringTyp =
    true
  | eq_typ' pair StackTyp StackTyp =
    true
  | eq_typ' pair (ArrTyp (t1, t2)) (ArrTyp (t3, t4)) =
    eq_typ' pair t1 t3 andalso eq_typ' pair t2 t4
  | eq_typ' pair (PCTyp(s1, s2)) (PCTyp(s3, s4)) =
    eq_poly_typ' pair s1 s3 andalso eq_poly_typ' pair s2 s4
  | eq_typ' pair (InfVarTyp X) (InfVarTyp Y) =
    Id.eqid X Y
  | eq_typ' pair IntTyp IntTyp =
    true
  | eq_typ' pair BoolTyp BoolTyp =
    true
  | eq_typ' pair _ _ =
    false

and eq_poly_typ' pair (ForAllPolyTyp(tvs1, t1)) (ForAllPolyTyp(tvs2, t2)) = 
    eq_typ' ((zip tvs1 tvs2)@pair) t1 t2

fun eq_poly_typ s1 s2 =
    eq_poly_typ' nil s1 s2

fun eq_typ t1 t2 =
    eq_typ' nil t1 t2

fun concat_list (h::t) l =
    if inList h l
    then concat_list t l
    else h::(concat_list t l)
  | concat_list nil l =
    l
    
    

fun FITV (VarTyp a) =
    nil
  | FITV UnitTyp =
    nil
  | FITV StringTyp =
    nil
  | FITV StackTyp =
    nil
  | FITV (ArrTyp (t1, t2)) =
    concat_list (FITV t1) (FITV t2)
  | FITV (PCTyp (ForAllPolyTyp (tvs1, t1), ForAllPolyTyp (tvs2, t2))) =
    concat_list (FITV t1) (FITV t2)
  | FITV (InfVarTyp X) =
    [X]
  | FITV IntTyp = 
    nil
  | FITV BoolTyp = 
    nil

fun FTV t =
    FTV' nil t
    
and FTV' btvs (VarTyp a) =
    if inList a btvs
    then nil
    else [a]
  | FTV' btvs UnitTyp = 
    nil
  | FTV' btvs StringTyp =
    nil
  | FTV' btvs StackTyp = 
    nil
  | FTV' btvs (ArrTyp (t1, t2)) =
    concat_list (FTV' btvs t1) (FTV' btvs t2)
  | FTV' btvs (PCTyp (s1, s2)) =
    concat_list (FTVPoly' btvs s1) (FTVPoly' btvs s2)
  | FTV' btvs (InfVarTyp X) =
    nil
  | FTV' btvs IntTyp =
    nil
  | FTV' btvs BoolTyp =
    nil

and FTVPoly' btvs (ForAllPolyTyp(tvs, t)) =
    FTV' (tvs@btvs) t
    
fun FTVG (VarG(x,t)::G) =
    concat_list (FTV t) (FTVG G)
  | FTVG (GenG(x, tvs, t)::G) =
    concat_list (FTV' tvs t) (FTVG G)
  | FTVG nil =
    nil

fun FITVG (VarG(x,t)::G) =
    concat_list (FITV t) (FITVG G)
  | FITVG (GenG(x, tvs, t)::G) =
    concat_list (FITV t) (FITVG G)
  | FITVG nil =
    nil

and tysubstPolyTyp t a (ForAllPolyTyp (tvs, t')) =
    if inList a tvs
    then ForAllPolyTyp (tvs, t')
    else let 
	    val (tvs', t'') = tysubstTyp'' t tvs t'
	in 
	    ForAllPolyTyp (tvs', tysubstTyp t a t'')
	end

and tysubstTyp t a =
    let
	fun tysubstTyp' (VarTyp b) =
	    if Id.eqid a b
	    then t
	    else VarTyp b
	  | tysubstTyp' UnitTyp =
	    UnitTyp
	  | tysubstTyp' StringTyp = 
	    StringTyp
	  | tysubstTyp' StackTyp =
	    StackTyp
	  | tysubstTyp' (ArrTyp (t1, t2)) =
	    ArrTyp (tysubstTyp' t1, tysubstTyp' t2)
	  | tysubstTyp' (PCTyp (s1, s2)) =
	    PCTyp (tysubstPolyTyp t a s1, tysubstPolyTyp t a s2)
	  | tysubstTyp' (InfVarTyp X) =
	    InfVarTyp X
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
  | tysubstTypList _ _ _ = raise SourceError "tysubstTypList"
		
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
	fun tysubstExp' (VarExp x) =
	    VarExp x
	  | tysubstExp' UnitExp = 
	    UnitExp
	  | tysubstExp' (StringExp s) =
	    StringExp s
	  | tysubstExp' (AppExp (e1, e2)) =
	    AppExp (tysubstExp' e1, tysubstExp' e2)
	  | tysubstExp' (LetExp (d, e)) =
	    LetExp (tysubstDec t a d, tysubstExp' e)
	  | tysubstExp' (StkCaseExp (e1, pes)) =
	    StkCaseExp (tysubstExp' e1, map (fn(p,e) => (tysubstPat t a p, tysubstExp' e)) pes)
	  | tysubstExp' (TypeCaseExp (t1, b, tes)) = 
	    let 
		val (b', t1') = if Id.eqid a b
				  then (b, t1)
				  else let 
					  val (b', t1') = tysubstTyp'' t [b] t1
				      in 
					  (hd b', tysubstTyp t a t1')
				      end
		val tvss = map (fn(ti,ei) => FTV ti) tes
		val tes' = map (fn(ti,ei) => let 
				       val tvs = FTV ti
				   in 
				       if inList a tvs
				       then (ti, ei)
				       else let 
					       val (tvs', ei') = tysubstExp'' t tvs ei
					       val ti' = tysubstTyp t a (tysubstTypList (map VarTyp tvs') tvs ti)
					   in 
					       (ti', tysubstExp' ei')
					   end
				   end) tes
			   
	    in
		TypeCaseExp (t1', b', tes')
	    end
	  | tysubstExp' (FunsPtExp (fs, s1, s2)) =
	    FunsPtExp (fs, tysubstPolyTyp t a s1, tysubstPolyTyp t a s2)
	  | tysubstExp' AnyPtExp =
	    AnyPtExp
	  | tysubstExp' (TyAnnExp (e, t')) = 
	    TyAnnExp (tysubstExp t a e, tysubstTyp t a t')
	  | tysubstExp' (TyAppExp (f, ts)) =
	    TyAppExp (f, map (tysubstTyp t a) ts)
	  | tysubstExp' (IntExp i) =
	    (IntExp i)
	  | tysubstExp' (PlusExp (e1, e2)) =
	    (PlusExp (tysubstExp' e1, tysubstExp' e2))
	  | tysubstExp' (BoolExp b) =
	    (BoolExp b)
	  | tysubstExp' (IfExp (e1, e2, e3)) =
	    (IfExp (tysubstExp' e1, tysubstExp' e2, tysubstExp' e3))
	  | tysubstExp' (PrintExp e)=
	    (PrintExp (tysubstExp' e))
	  | tysubstExp' (ItoSExp e)=
	    (ItoSExp (tysubstExp' e))
	  | tysubstExp' (ConcatExp (e1, e2)) =
	    (ConcatExp (tysubstExp' e1, tysubstExp' e2))
	  | tysubstExp' (SeqExp (e1, e2)) =
	    (SeqExp (tysubstExp' e1, tysubstExp' e2))
	  | tysubstExp' AbortExp =
	    AbortExp
	  | tysubstExp' (EqExp (e1, e2)) =
	    (EqExp (tysubstExp' e1, tysubstExp' e2))
	  | tysubstExp' (PosExp (p, e)) = 
	    tysubstExp' e
    in 
	tysubstExp'
    end

and tysubstExpList (t::ts) (tv::tvs) e =
    tysubstExpList ts tvs (tysubstExp t tv e)
  | tysubstExpList nil nil e = e
  | tysubstExpList _ _ _ = raise SourceError "tysubstExpList"
	
and tysubstPat t a =
    let
	fun tysubstPat' NilPat =
	    NilPat
	  | tysubstPat' (VarPat x) =
	    VarPat x
	  | tysubstPat' (AllPat p) =
	    tysubstPat' p
	  | tysubstPat' (PtPat (e, x, y, p)) =
	    PtPat (tysubstExp t a e, x, y, tysubstPat' p)
	  | tysubstPat' (AnnotPtPat (e, x, t', y, p)) =
	    AnnotPtPat (tysubstExp t a e, x, tysubstTyp t a t',  y, tysubstPat' p)
	    
    in
	tysubstPat'
    end

and tysubstDec t a =
    let
	fun tysubstDec' (FunDec (f, x, t1, t2, e)) =
	    FunDec (f, x, tysubstTyp t a t1, tysubstTyp t a t2, tysubstExp t a e)
	  | tysubstDec' (InfFunDec (f, x, e)) =
	    raise SourceError "tysubstDec InfFunDec"
	  | tysubstDec' (AnnotAdvDec (time, e1, x, t', s, n, e2)) =
	    AnnotAdvDec (time, tysubstExp t a e1, x, tysubstTyp t a t', s, n, tysubstExp t a e2)
	  | tysubstDec' (AdvDec (time, e1, x, s, n, e2)) =
	    AdvDec (time, tysubstExp t a e1, x, (*tysubstTyp t a t',*) s, n, tysubstExp t a e2)
	  | tysubstDec' (CaseAdvDec (time, e1, x, t', s, n, e2)) =
	    CaseAdvDec (time, tysubstExp t a e1, x, tysubstTyp t a t', s, n, tysubstExp t a e2) 

    in 
	tysubstDec'
    end

fun inftysubstPolyTyp (t:typ) X (ForAllPolyTyp(tvs, t')) =
    ForAllPolyTyp (tvs, inftysubstTyp t X t') 
    
and inftysubstTyp t X =
    let 
	fun inftysubstTyp' (VarTyp a) =
	    VarTyp a
	  | inftysubstTyp' UnitTyp =
	    UnitTyp
	  | inftysubstTyp' StringTyp =
	    StringTyp
	  | inftysubstTyp' StackTyp =
	    StackTyp 
	  | inftysubstTyp' (ArrTyp(t1, t2)) =
	    ArrTyp (inftysubstTyp' t1, inftysubstTyp' t2)
	  | inftysubstTyp' (PCTyp (s1, s2)) =
	    PCTyp (inftysubstPolyTyp t X s1, inftysubstPolyTyp t X s2)
	  | inftysubstTyp' (InfVarTyp Y) =
	    if Id.eqid X Y 
	    then t
	    else InfVarTyp Y
	  | inftysubstTyp' IntTyp =
	    IntTyp
	  | inftysubstTyp' BoolTyp =
	    BoolTyp
    in 
	inftysubstTyp'
    end

and inftysubstExp t X = 
    let
	fun inftysubstExp' (VarExp x) =
	    VarExp x
	  | inftysubstExp' UnitExp =
	    UnitExp
	  | inftysubstExp' (StringExp s) =
	    StringExp s
	  | inftysubstExp' (AppExp (e1, e2)) =
	    AppExp (inftysubstExp' e1, inftysubstExp' e2) 
	  | inftysubstExp' (LetExp (d, e)) =
	    LetExp (inftysubstDec t X d, inftysubstExp' e)
	  | inftysubstExp' (StkCaseExp (e1, pes)) =
	    StkCaseExp (inftysubstExp' e1, map (fn(pi,ei) => (inftysubstPat t X pi, inftysubstExp' ei)) pes) 
	  | inftysubstExp' (TypeCaseExp (t', a, tes)) =
	    TypeCaseExp (inftysubstTyp t X t', a, map (fn(ti, ei) => (inftysubstTyp t X ti, inftysubstExp' ei)) tes)
	  | inftysubstExp' (FunsPtExp (fs, s1, s2)) =
	    FunsPtExp (fs, inftysubstPolyTyp t X s1, inftysubstPolyTyp t X s2)
	  | inftysubstExp' AnyPtExp = 
	    AnyPtExp
	  | inftysubstExp' (TyAnnExp (e, t')) =
	    TyAnnExp (inftysubstExp' e, inftysubstTyp t X t')
	  | inftysubstExp' (TyAppExp (f, ts)) =
	    TyAppExp (f, map (inftysubstTyp t X) ts)
	  | inftysubstExp' (IntExp i) =
	    (IntExp i)
	  | inftysubstExp' (PlusExp (e1, e2)) =
	    (PlusExp (inftysubstExp' e1, inftysubstExp' e2))
	  | inftysubstExp' (BoolExp b) =
	    (BoolExp b)
	  | inftysubstExp' (IfExp (e1, e2, e3)) =
	    (IfExp (inftysubstExp' e1, inftysubstExp' e2, inftysubstExp' e3))
	  | inftysubstExp' (PrintExp e)=
	    (PrintExp (inftysubstExp' e))
	  | inftysubstExp' (ItoSExp e)=
	    (ItoSExp (inftysubstExp' e))
	  | inftysubstExp' (ConcatExp (e1, e2)) =
	    (ConcatExp (inftysubstExp' e1, inftysubstExp' e2))
	  | inftysubstExp' (SeqExp (e1, e2)) =
	    (SeqExp (inftysubstExp' e1, inftysubstExp' e2))
	  | inftysubstExp' AbortExp =
	    AbortExp
	  | inftysubstExp' (EqExp (e1, e2)) =
	    (EqExp (inftysubstExp' e1, inftysubstExp' e2))
	  | inftysubstExp' (PosExp (p, e)) =
	    inftysubstExp' e
    in 
	inftysubstExp'
    end

and inftysubstExpList (t::ts) (X::Xs) e =
    (*inftysubstExpList ts Xs (inftysubstExp t X e)*)
    inftysubstExp t X (inftysubstExpList ts Xs e)
  | inftysubstExpList nil nil e = e
  | inftysubstExpList _ _ _ = raise SourceError "inftysubstExpList"

and inftysubstPat t X =
    let
	fun inftysubstPat' NilPat = 
	    NilPat
	  | inftysubstPat' (VarPat x) =
	    VarPat x
	  | inftysubstPat' (AllPat p) =
	    AllPat (inftysubstPat' p)
	  | inftysubstPat' (PtPat (e, x, y, p)) =
	    PtPat (inftysubstExp t X e, x, y, inftysubstPat' p)
	  | inftysubstPat' (AnnotPtPat (e, x, t', y, p)) =
	    AnnotPtPat (inftysubstExp t X e, x, inftysubstTyp t X t', y, inftysubstPat' p)
    in 
	inftysubstPat'
    end

and inftysubstDec t X =
    let
	fun inftysubstDec' (FunDec (f, x, t1, t2, e)) =
	  (*  ((if Id.eqid f (Id.makeid "walk")
	     then print ("[" ^ "/" ^ Id.id2string X  ^ "] ")
	     else ());*)
	    FunDec (f, x, inftysubstTyp t X t1, inftysubstTyp t X t2, inftysubstExp t X e)
	  | inftysubstDec' (InfFunDec (f, x, e)) =
	    raise SourceError "inftysubstDec InfFunDec"
	  | inftysubstDec' (AdvDec (time, e1, x, y, z, e2)) =
	    AdvDec (time, inftysubstExp t X e1, x,(* inftysubstTyp t X t',*) y, z, inftysubstExp t X e2)
	  | inftysubstDec' (AnnotAdvDec (time, e1, x, t', y, z, e2)) =
	    AnnotAdvDec (time, inftysubstExp t X e1, x, inftysubstTyp t X t', y, z, inftysubstExp t X e2)
	  | inftysubstDec' (CaseAdvDec (time, e1, x, t', y, z, e2)) =
	    CaseAdvDec (time, inftysubstExp t X e1, x, inftysubstTyp t X t', y, z, inftysubstExp t X e2)
	(*  | inftysubstDec' (InfAdvDec (time, e1, x, y, z, e2)) =
	    raise SourceError "inftysubstDec InfAdvDec"*)
    in
	inftysubstDec'
    end

and inftysubstTypList (t::ts) (X::Xs) t' =
    (*inftysubstTypList ts Xs (inftysubstTyp t X t') *)
    inftysubstTyp t X (inftysubstTypList ts Xs t')
  | inftysubstTypList nil nil t = t
  | inftysubstTypList _ _ _ = raise SourceError "inftysubstExpList"
	
fun inftysubstG t X (VarG(x, t')::G) =
    VarG(x, inftysubstTyp t X t')::(inftysubstG t X G)
  | inftysubstG t X (GenG(x, tvs, t')::G) =
    GenG(x, tvs, inftysubstTyp t X t')::(inftysubstG t X G)
  | inftysubstG t X nil =
    nil
  
and inftysubstGList (t::ts) (tv::tvs) G =
    inftysubstGList ts tvs (inftysubstG t tv G)
  | inftysubstGList nil nil G = G
  | inftysubstGList _ _ _ = raise SourceError "tysubstGList"
	


	
fun tysubstG'' t (tv::tvs) t' =
    if inList tv (FTV t)
    then let 
	    val tv' = Id.cloneid tv
	    val t'' = tysubstTyp (VarTyp tv') tv t'
	    val (tvs', t''') = tysubstG'' t tvs t''
	in 
	    (tv'::tvs', t''')
	end
    else 
	let 
	    val (tvs', t'') = tysubstG'' t tvs t'
	in 
	   (tv::tvs', t'')
	end
  | tysubstG'' t nil t' =
    (nil, t')

fun tysubstG t a =
    let 
	fun tysubstG' (VarG(x, t')::G) =
	    VarG(x, tysubstTyp t a t')::(tysubstG' G)
	  | tysubstG' (GenG(x, tvs, t')::G) =
	    if inList a tvs
	    then (GenG(x, tvs, t'))::(tysubstG' G)
	    else let
		    val (tvs', t'') = tysubstG'' t tvs t'
		in 
		    GenG(x, tvs', tysubstTyp t a t'')::(tysubstG' G)
		end
	  | tysubstG' nil =
	    nil
    in
	tysubstG'
    end

and tysubstGList (t::ts) (tv::tvs) G =
    tysubstGList ts tvs (tysubstG t tv G)
  | tysubstGList nil nil G = G
  | tysubstGList _ _ _ = raise SourceError "tysubstGList"
	

fun lookupVarG x (VarG(y,t)::G) = 
    if (Id.eqid x y) 
    then t 
    else lookupVarG x G
  | lookupVarG x (_::G) = 
    lookupVarG x G
  | lookupVarG x nil = 
    raise SourceError ("lookupVarG" ^ Id.id2string x)

fun lookupGenG x (GenG(y,tvs,t)::G) = 
    if (Id.eqid x y) 
    then (tvs,t)
    else lookupGenG x G
  | lookupGenG x (_::G) = 
    lookupGenG x G
  | lookupGenG x nil = 
    raise SourceError "lookupGenG"

fun isVarG x G =
    ((lookupVarG x G); true) handle (SourceError s) => false

fun gen G t =
    let
	val Xs = subList (FITV t) (FITVG G)
	val tvs = map (fn _ => Id.freshid "a") Xs
	val t' = inftysubstTypList (map VarTyp tvs) Xs t
    in
	(tvs, t')
    end



fun checkTyp D = 
    let 
	fun checkTyp' (VarTyp a) =
	    inList a D
	    | checkTyp' UnitTyp =
	      true
	    | checkTyp' StringTyp =
	      true
	    | checkTyp' StackTyp = 
	      true
	    | checkTyp' (ArrTyp (t1, t2)) =
	      checkTyp' t1 andalso checkTyp' t2
	    | checkTyp' (PCTyp (s1, s2)) =
	      checkPolyTyp D s1 andalso checkPolyTyp D s2
	    | checkTyp' (InfVarTyp inftyvar) =
	      false
	    | checkTyp' IntTyp = 
	      true
	    | checkTyp' BoolTyp =
	      true
    in 
	checkTyp'
    end

and checkPolyTyp D (ForAllPolyTyp (tvs, t)) =
    checkTyp (tvs@D) t


fun combineSubst' a ((t, b)::subs) =
    if Id.eqid a b 
    then SOME t
    else combineSubst' a subs
  | combineSubst' a nil =
    NONE
    
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
   
fun combineSubst'' a ((t, b)::subs) =
    if Id.eqid a b 
    then SOME t
    else combineSubst'' a subs
  | combineSubst'' a nil =
    NONE
    

fun combineSubst subs:(typ*tyvar) list =
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

fun findSubst tvs1 =
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
	  | findSubst' pair tvs1 (PCTyp (ForAllPolyTyp (tvs1a, t1a), ForAllPolyTyp (tvs2a, t2a))) (PCTyp (ForAllPolyTyp (tvs1b, t1b), ForAllPolyTyp (tvs2b, t2b))) =
	    let 
		val tvs1' = subList tvs1 tvs1a
		val tvs2' = subList tvs1 tvs2a
	    in 
		if length tvs1a = length tvs2a andalso length tvs2a = length tvs2b
		then combineSubst (findSubst' ((zip tvs1a tvs1b)@pair) tvs1' t1a t1b)@(findSubst' ((zip tvs2a tvs2b)@pair) tvs2' t2a t2b)
		else raise SourceError "findsubst PCTyp"
	    end
	  | findSubst' pair tvs1 StackTyp StackTyp =
	    nil
	  | findSubst' pair tvs1 IntTyp IntTyp =
	     nil
	  | findSubst' pair tvs1 BoolTyp BoolTyp =
	     nil
	  | findSubst' pair tvs1 t1 t2 = 
	    raise GenError
    in 
	findSubst' nil tvs1
    end
	
end