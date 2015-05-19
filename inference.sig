signature INFERENCE =
sig

    val inferDebug : Source.prog -> Source.exp * Source.typ * (Source.typ * Source.tyvar) list
    val inferProg : Source.prog -> Source.prog * Source.typ

end