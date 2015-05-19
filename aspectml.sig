signature ASPECTML =
sig
    val run : string -> unit

    val parse : string -> unit

    val infer : string -> unit
			  
    val inferDebug : string -> unit
			  
    val translate : string -> unit

    val typecheck : string -> unit

    val eval : string -> unit

    
end