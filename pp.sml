structure PrettyPrint :> PRETTYPRINT =
struct

structure C = Core
structure S = Source

fun ppCTyp C.UnitTyp = 
    "1"
  | ppCTyp C.StringTyp = 
    "string"
  | ppCTyp (C.VarTyp tyvar) =
    Id.id2string tyvar
  | ppCTyp (C.ArrTyp (t1, t2)) =
    ppCTyp t1 ^ " -> " ^ ppCTyp t2
  | ppCTyp (C.ForAllTyp(a, t)) =
    "\\/" ^ ppTyvar a ^ "." ^ ppCTyp t
  | ppCTyp (C.LabTyp(ts, t)) = 
    "(" ^ ppList (map (fn(v) => ppTyvar v ^ ",") ts) ^ "." ^ ppCTyp t ^ ") label"
  | ppCTyp (C.PCTyp(ts, t)) = 
    "(" ^ ppList (map (fn(t) => ppTyvar t ^ ",") ts) ^ "." ^ ppCTyp t ^ ") pc"
  | ppCTyp C.AdvTyp =
    "advice"
  | ppCTyp C.StackTyp = 
    "stack"
  | ppCTyp (C.TupleTyp ts) =
    "( " ^ ppList (map (fn(t) => ppCTyp t ^ " * ") ts) ^ " )"
  | ppCTyp C.IntTyp =
    "int"
  | ppCTyp C.BoolTyp = 
    "bool"


and ppVar v =
    Id.id2string v

and ppTyvar v =
    Id.id2string v

and ppCExp C.UnitExp =
    "()"
  | ppCExp (C.StringExp s) =
    "\"" ^ s ^ "\""
  | ppCExp (C.VarExp v) =
    ppVar v
  | ppCExp (C.FunExp (x,t,e)) =
    "(\\" ^ ppVar x ^ ":" ^ ppCTyp t ^ "." ^ ppCExp e ^ ")"
  | ppCExp (C.AppExp (e1, e2)) =
    "( " ^ ppCExp e1 ^ " " ^ ppCExp e2 ^ " )"
  | ppCExp (C.TyFunExp (a, e)) =
    "( /\\" ^ ppTyvar a ^ "." ^ ppCExp e ^ " )"
  | ppCExp (C.TyAppExp (e, t)) =
    ppCExp e ^ "[" ^ ppCTyp t ^ "]"
  | ppCExp (C.TupleExp(es)) =
    "(" ^ ppList (map (fn(e) => ppCExp e ^ ",") es) ^ ")"
  | ppCExp (C.LetExp(xs, e1, e2)) =
    "let (" ^ ppList (map (fn(x) => ppVar x ^ ",") xs) ^ ") = " ^ ppCExp e1 ^ " in " ^ ppCExp e2
  | ppCExp (C.LabExp l) =
    "l" ^ Int.toString l
  | ppCExp (C.PCExp (e1, ts, e2)) =
    ppCExp e1 ^ "[" ^ ppList (map (fn(t) => ppCTyp t ^ ",") ts) ^ "][[" ^ ppCExp e2 ^ "]]"
  | ppCExp (C.NewExp (ts, t, e)) =
    "new " ^ ppList (map (fn(t) => ppTyvar t ^ ",") ts) ^ "." ^ ppCTyp t ^ " <= " ^ ppCExp e
  | ppCExp (C.AdvInstExp e) =
    "=>(" ^ ppCExp e ^ ")"
  | ppCExp (C.AdvExp(e1,ts, x, t, e2)) =
    "{{" ^ ppCExp e1 ^ "." ^ ppList (map (fn(t) => ppTyvar t ^ ",") ts) ^ ppVar x ^ ":" ^ ppCTyp t ^ " -> " ^ ppCExp e2 ^ "}}"
  | ppCExp (C.TypeCaseExp (a, t1, t2, tes)) =
    "typecase[" ^ ppTyvar a ^ "." ^ ppCTyp t1 ^ "] " ^ ppCTyp t2 ^ " ( " ^ ppList (map (fn (t,e) => ppCTyp t ^ " => " ^ ppCExp e ^ " | ") tes) ^ " )"
  | ppCExp (C.SetExp(es)) =
    "{" ^ ppList (map (fn(e) => ppCExp e ^ ",") es) ^ "}"
  | ppCExp (C.UnionExp (e1,e2)) =
    ppCExp e1 ^ " U " ^ ppCExp e2
  | ppCExp C.StackExp =
    "stack()"
  | ppCExp C.NilStExp =
    "nil"
  | ppCExp (C.PtStExp (e1, ts, e2, e3)) =
    ppCExp e1 ^ "[" ^  ppList (map (fn(t) => ppCTyp t ^ ",") ts) ^ "][["^ppCExp e2 ^ "]]::" ^ ppCExp e3
  | ppCExp (C.StoreExp (e1, ts, e2, e3)) =
     "store " ^ ppCExp e1 ^ "[" ^  ppList (map (fn(t) => ppCTyp t ^ ",") ts) ^ "][["^ppCExp e2 ^ "]] in " ^ ppCExp e3
  | ppCExp (C.StkCaseExp (e1, pes)) =
    "stkcase " ^ ppCExp e1 ^ " ( " ^ ppList (map (fn (p,e) => ppCPat p ^ " => " ^ ppCExp e ^ " | ") pes) ^ " )"
  | ppCExp (C.IntExp i) =
    "#" ^ Int.toString i
  | ppCExp (C.PlusExp (e1, e2)) =
    ppCExp e1 ^ " + " ^ ppCExp e2
  | ppCExp (C.BoolExp b) =
    if b then "true" else "false"
  | ppCExp (C.IfExp (e1, e2, e3)) =
    "if " ^ ppCExp e1 ^ " then " ^ ppCExp e2 ^ " else " ^ ppCExp e3
  | ppCExp (C.PrintExp e) =
    "(print " ^ ppCExp e ^ ")"
  | ppCExp (C.ItoSExp e) =
    "(itos " ^ ppCExp e ^ ")"
  | ppCExp (C.ConcatExp (e1, e2)) =
    ppCExp e1 ^ " ^ " ^ ppCExp e2
  | ppCExp (C.FixExp (f, t, e)) =
    "fix " ^ ppVar f ^ ":" ^ ppCTyp t ^ "." ^ ppCExp e
  | ppCExp C.AbortExp =
    " abort "
  | ppCExp (C.EqExp (e1, e2)) =
    ppCExp e1 ^ " =s= " ^ ppCExp e2
  | ppCExp (C.PosExp (_, e)) =
    ppCExp e
 


and ppCPat C.NilPat =
    "nil"
  | ppCPat (C.PtPat (e, ts, x, t, p)) =
       ppCExp e ^ "[" ^  ppList (map (fn(t) => ppTyvar t ^ ",") ts) ^ "][[" ^ ppVar x ^ "]]:"^ppCTyp t ^ "++" ^ ppCPat p
  | ppCPat (C.VarPat x) =
    ppVar x
  | ppCPat (C.AllPat p) =
    "_::" ^ ppCPat p


and ppList (h::t) =
    h ^ ppList t
  | ppList nil =
    ""

fun ppInfTyvar X =
    Id.id2string X

fun ppSTyp (S.VarTyp a) =
    ppTyvar a 
  | ppSTyp S.UnitTyp = 
    "1"
  | ppSTyp S.StringTyp =
    "string"
  | ppSTyp S.StackTyp = 
    "stack"
  | ppSTyp (S.ArrTyp (t1, t2)) =
    ppSTyp t1 ^ " -> " ^ ppSTyp t2
  | ppSTyp (S.PCTyp (s1, s2)) =
    "pc " ^ ppSPolyTyp s1 ^ ", " ^ ppSPolyTyp s2
  | ppSTyp (S.InfVarTyp X) =
    ppInfTyvar X
  | ppSTyp S.IntTyp =
    "int"
  | ppSTyp S.BoolTyp = 
    "bool"


and ppSPolyTyp (S.ForAllPolyTyp (tvs, t)) =
    "\\/ " ^ ppList (map (fn (a) => ppTyvar a ^ ", ") tvs) ^ " . " ^ ppSTyp t

fun ppList (h::t) =
    h ^ " " ^ ppList t
  | ppList nil =
    ""

fun ppCProg (C.Prog e) =
    ppCExp e


and ppSExp S.UnitExp =
    "()"
  | ppSExp (S.StringExp s) =
    "\"" ^ s ^ "\""
  | ppSExp (S.VarExp v) =
    ppVar v
  | ppSExp (S.AppExp (e1, e2)) =
    "( " ^ ppSExp e1 ^ " " ^ ppSExp e2 ^ " )"
  | ppSExp (S.LetExp(d,e)) =
    "let " ^ ppSDec d ^ " in\n" ^ ppSExp e
  | ppSExp (S.StkCaseExp (e1, pes)) =
    "stkcase " ^ ppSExp e1 ^ " of ( " ^ ppList (map (fn (p,e) => ppSPat p ^ " => " ^ ppSExp e ^ " | " ) pes) ^ " )"
  | ppSExp (S.TypeCaseExp (t, a, tes)) =
    "typecase [ " ^ ppSTyp t ^ " ] " ^ ppTyvar a ^ " ( " ^ ppList (map (fn (t,e) => ppSTyp t ^ " => " ^ ppSExp e ^ " | ") tes) ^ " )"
  | ppSExp (S.FunsPtExp(fs, s1, s2)) = 
    "{" ^ ppList (map (fn(f) => ppVar f ^ ",") fs) ^ "}:(" ^ ppSPolyTyp s1 ^ "," ^ ppSPolyTyp s2 ^ ")"
  | ppSExp S.AnyPtExp = 
    "any"
  | ppSExp (S.TyAnnExp (e, t)) =
    "(" ^ ppSExp e ^ ":" ^ ppSTyp t ^ ")"
  | ppSExp (S.TyAppExp (f, ts)) =
    "(" ^ ppVar f ^ "[" ^ ppList (map (fn(t) => ppSTyp t ^ ",") ts) ^ "]"
  | ppSExp (S.IntExp i) =
    "#" ^ Int.toString i
  | ppSExp (S.PlusExp (e1, e2)) =
    ppSExp e1 ^ " + " ^ ppSExp e2
  | ppSExp (S.BoolExp b) =
    if b then "true" else "false"
  | ppSExp (S.IfExp (e1, e2, e3)) =
    "if " ^ ppSExp e1 ^ " then " ^ ppSExp e2 ^ " else " ^ ppSExp e3
  | ppSExp (S.PrintExp e) =
    "print " ^ ppSExp e
  | ppSExp (S.ItoSExp e) =
    "itos " ^ ppSExp e
  | ppSExp (S.ConcatExp (e1, e2)) =
    ppSExp e1 ^ " ^ " ^ ppSExp e2
  | ppSExp (S.SeqExp (e1, e2)) =
    ppSExp e1 ^ ";" ^ ppSExp e2
  | ppSExp S.AbortExp =
    " abort " 
  | ppSExp (S.EqExp (e1, e2)) =
    ppSExp e1 ^ " =s= " ^ ppSExp e2
  | ppSExp (S.PosExp (p, e)) = 
    ppSExp e

and ppSPat S.NilPat =
    "nil"
  | ppSPat (S.VarPat x) =
    ppVar x
  | ppSPat (S.AllPat p) =
    "_++" ^ ppSPat p
  | ppSPat (S.PtPat (e, x, y, p)) =
    ppSExp e ^ "(" ^ ppVar x ^ "," ^ ppVar y ^ ")++" ^ ppSPat p
  | ppSPat (S.AnnotPtPat (e, x, t, y, p)) =
    ppSExp e ^ "(" ^ ppVar x ^ ":" ^ ppSTyp t ^ "," ^ ppVar y ^ ")++" ^ ppSPat p

and ppSDec (S.FunDec (f,x,t1,t2,e)) =
    "rec fun " ^ ppVar f ^ "(" ^ ppVar x ^ ":" ^ ppSTyp t1 ^ "):" ^ ppSTyp t2 ^ " = " ^ ppSExp e
  | ppSDec (S.InfFunDec (f,x,e)) =
    "rec fun " ^ ppVar f ^ "(" ^ ppVar x ^ ")" ^ " = " ^ ppSExp e
  | ppSDec (S.CaseAdvDec (time, e1, x, t, y, z, e2)) =
    "case-advice " ^ ppSTime time ^ " " ^ ppSExp e1 ^ " (" ^ ppVar x ^ ":" ^ ppSTyp t ^ "," ^ ppVar y ^ "," ^ ppVar z ^ ") = " ^ ppSExp e2
  | ppSDec (S.AdvDec (time, e1, x, y, z, e2)) =
    "advice " ^ ppSTime time ^ " " ^ ppSExp e1 ^ "(" ^ ppVar x ^ "," ^ ppVar y ^ "," ^ ppVar z ^ ") = " ^ ppSExp e2
  | ppSDec (S.AnnotAdvDec (time, e1, x,t, y, z, e2)) =
    "advice " ^ ppSTime time ^ " " ^ ppSExp e1 ^ "(" ^ ppVar x ^ ":" ^ ppSTyp t ^ "," ^ ppVar y ^ "," ^ ppVar z ^ ") = " ^ ppSExp e2

and ppSTime S.BeforeTime = 
    "before"
  | ppSTime S.AfterTime =
    "after" 

fun ppSProg (S.Prog e) =
    ppSExp e

fun ppInferT T =
    ppList (map (fn (t, X) => "[" ^ ppSTyp t ^ "/" ^ ppInfTyvar X ^ "]") T)

    


end