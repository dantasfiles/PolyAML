signature CORE =
sig

type l = int
type var = Id.id
type tyvar = Id.id

exception CoreError of string
exception MGUError


val U : l

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

(*exception CoreDebugError of typ * typ*)

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

and prog = Prog of exp

and G = VarG of var * typ 
  | LabG of l * tyvar list * typ

val eq_typ : typ -> typ -> bool

val FTV : typ -> tyvar list

val tysubstExp : typ -> tyvar -> exp -> exp 
val tysubstExpList : typ list -> tyvar list -> exp -> exp

val tysubstTyp : typ -> tyvar -> typ -> typ
val tysubstTypList : typ list -> tyvar list -> typ -> typ

val tysubstG : typ -> tyvar -> G list -> G list 
val tysubstGList : typ list -> tyvar list -> G list -> G list

val substExp : exp -> var -> exp -> exp
val substExpList : exp list -> var list -> exp -> exp

val isVal : exp -> bool
val isValPat : pat -> bool

val inList : Id.id -> Id.id list -> bool

val findSubst : tyvar list -> typ -> typ -> (typ * tyvar) list

val gen_list : (tyvar list * typ) list -> (tyvar list * typ)

val mgu : typ -> typ -> (typ * tyvar) list

val check_core_gen_typ :  tyvar list -> typ -> tyvar list -> typ -> bool

val join_typ : typ -> typ -> typ

val join_typ_list : typ list -> typ

end