signature PRETTYPRINT =
sig

val ppCTyp : Core.typ -> string

val ppVar : Id.id -> string
val ppTyvar : Id.id -> string
val ppInfTyvar : Id.id -> string

val ppCExp : Core.exp -> string

val ppCPat : Core.pat -> string

val ppSTyp : Source.typ -> string

val ppSPolyTyp : Source.polytyp -> string

val ppList : string list -> string

val ppCProg : Core.prog -> string

val ppSExp : Source.exp -> string 
val ppSProg : Source.prog -> string

val ppInferT : (Source.typ * Source.inftyvar) list -> string

end