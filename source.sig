signature SOURCE =
sig

type var = Id.id
type tyvar = Id.id
type inftyvar = Id.id

exception SourceError of string
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
  | PosExp of Util.pos * exp
  
and pat = 
    NilPat
  | VarPat of var
  | AllPat of pat
  | PtPat of exp * var * var * pat
  | AnnotPtPat of exp * var * typ * var * pat

and dec =
    FunDec of var * var * typ * typ * exp
  | InfFunDec of var * var * exp
  | AnnotAdvDec of time * exp * var * typ * var * var * exp
  | AdvDec of time * exp * var * var * var * exp
  | CaseAdvDec of time * exp * var * typ * var * var * exp

and prog = 
    Prog of exp

datatype G = VarG of var * typ 
	   | GenG of var * tyvar list * typ

val eq_typ : typ -> typ -> bool
val eq_poly_typ : polytyp -> polytyp -> bool

val tysubstTyp : typ -> tyvar -> typ -> typ
val tysubstTypList : typ list -> tyvar list -> typ -> typ
val tysubstG : typ -> tyvar -> G list -> G list
val tysubstGList : typ list -> tyvar list -> G list -> G list

val FTV : typ -> tyvar list
val FTVG : G list -> tyvar list
val FITV : typ -> inftyvar list 
val FITVG : G list -> inftyvar list

val inList : Id.id -> Id.id list -> bool

val inftysubstExpList : typ list -> inftyvar list -> exp -> exp
val inftysubstTypList : typ list -> inftyvar list -> typ -> typ
val inftysubstGList : typ list -> inftyvar list -> G list -> G list

val gen : G list -> typ -> tyvar list * typ

val lookupVarG : var -> G list -> typ
val lookupGenG : var -> G list -> tyvar list * typ
val isVarG : var -> G list -> bool

val checkTyp : tyvar list -> typ -> bool

val checkPolyTyp : tyvar list -> polytyp -> bool

val findSubst : tyvar list -> typ -> typ -> (typ * tyvar) list

end