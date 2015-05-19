structure Parse :> PARSE =
struct 
  structure AspectMLLrVals = AspectMLLrValsFun(structure Token = LrParser.Token)
  structure AspectMLLex = AspectMLLexFun(structure Tokens = AspectMLLrVals.Tokens)
  structure AspectMLParser = Join(structure ParserData = AspectMLLrVals.ParserData
			structure Lex=AspectMLLex
			structure LrParser = LrParser)
  fun parse filename =
      let val _ = (ErrorMsg.reset(); ErrorMsg.fileName := filename)
	  val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  fun parseerror(s,p1,p2) = ErrorMsg.error (p1,p2) s
	  val lexer = LrParser.Stream.streamify (AspectMLLex.makeLexer get)
	  val (absyn, _) = AspectMLParser.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
	   absyn
      end handle LrParser.ParseError => raise ErrorMsg.Error


 end



