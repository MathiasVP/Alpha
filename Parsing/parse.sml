structure Parse: sig val parse : string -> Absyn.decl list end =
struct 

structure AlphaLrVals = AlphaLrValsFun (structure Token = LrParser.Token)
structure Lex = AlphaLexFun (structure Tokens = AlphaLrVals.Tokens)
structure AlphaP = Join (
  structure ParserData = AlphaLrVals.ParserData
  structure Lex = Lex
  structure LrParser = LrParser
)

fun parse filename =
    let
	val _ = (ErrorMsg.reset (); ErrorMsg.fileName := filename)
	val file = TextIO.openIn filename
	fun get _ = TextIO.input file
	fun parseerror (s, p1, p2) = ErrorMsg.error p1 s
	val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	val (parseresult, _) = AlphaP.parse (30, lexer, parseerror, ())
    in
        TextIO.closeIn file;
		parseresult
    end 
    handle LrParser.ParseError => raise ErrorMsg.Error

end (* Parse *)

