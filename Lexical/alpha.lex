type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos

val commentLevel = ref 0
val unfinishedString = ref false
val currentString = ref ""

fun err (p1,p2) = ErrorMsg.error p1

fun eof () =
	let
		val pos = hd (!linePos)
	in
		if !commentLevel <> 0 then
			(ErrorMsg.error pos "unfinished comment at eof")
		else if !unfinishedString then
			(ErrorMsg.error pos "unfinished string at eof")
		else ();
	Tokens.EOF (pos,pos)
    end

fun s2i t pos =
    let
        val opti = (Int.fromString t) 
            handle Overflow => 
                   (ErrorMsg.error pos "Integer too large"; SOME 0)
        fun s2i_aux NONE = (ErrorMsg.error pos "Ill-formed integer"; 0)
          | s2i_aux (SOME n) = n
    in
        s2i_aux opti
    end
	
fun s2f t pos =
    let
        val opti = (Real.fromString t)
        fun s2f_aux NONE = (ErrorMsg.error pos "Ill-formed float"; 0.0)
          | s2f_aux (SOME n) = n
    in
        s2f_aux opti
    end
	
fun s2b t pos =
    let
        val opti = (Bool.fromString t)
        fun s2b_aux NONE = (ErrorMsg.error pos "Ill-formed bool"; false)
          | s2b_aux (SOME b) = b
    in
        s2b_aux opti
    end

fun dopos token yypos yylen = token (yypos, yypos + yylen)
fun dopos3 token value yypos yylen = token (value, yypos, yypos + yylen)

%%

%header (functor AlphaLexFun (structure Tokens: Alpha_TOKENS));

letter=[a-zA-Z];
digits=[0-9]+;
hexdigits4=[0-9A-Fa-f][0-9A-Fa-f][0-9A-Fa-f][0-9A-Fa-f];
floats=[0-9]*\.[0-9]+;
bools=true|false;
idchars=[a-zA-Z0-9_]*;
whitespace=[\ \t]+;
newline=[\r\n|\n\r|\r|\n]+;
escapeseqStr="\\0"|"\\n"|"\\t"|"\\r"|"\\\\"|"\\\""|"\\x"{hexdigits4};
escapeseqChar="\\0"|"\\n"|"\\t"|"\\r"|"\\\\"|"\\'"|"\\x"{hexdigits4};

%s COMMENT STRING CHARACTER;


%%

<INITIAL>"fun"				=> (dopos Tokens.FUN yypos 3);
<INITIAL>"var"				=> (dopos Tokens.VAR yypos 3);
<INITIAL>"if"				=> (dopos Tokens.IF yypos 2);
<INITIAL>"else"				=> (dopos Tokens.ELSE yypos 4);
<INITIAL>"return"			=> (dopos Tokens.RETURN yypos 6);
<INITIAL>"break"			=> (dopos Tokens.BREAK yypos 5);
<INITIAL>"while"			=> (dopos Tokens.WHILE yypos 5);
<INITIAL>"for"				=> (dopos Tokens.FOR yypos 3);
<INITIAL>"array"			=> (dopos Tokens.ARRAY yypos 5);
<INITIAL>"interface"		=> (dopos Tokens.INTERFACE yypos 9);
<INITIAL>"class"			=> (dopos Tokens.CLASS yypos 5);
<INITIAL>"extends"			=> (dopos Tokens.EXTENDS yypos 7);
<INITIAL>"implements"		=> (dopos Tokens.IMPLEMENTS yypos 10);
<INITIAL>"private"			=> (dopos Tokens.PRIVATE yypos 7);
<INITIAL>"protected"		=> (dopos Tokens.PROTECTED yypos 9);
<INITIAL>"public"			=> (dopos Tokens.PUBLIC yypos 6);
<INITIAL>"this"				=> (dopos Tokens.THIS yypos 4);
<INITIAL>"."				=> (dopos Tokens.DOT yypos 1);
<INITIAL>"("				=> (dopos Tokens.LPAREN yypos 1);
<INITIAL>")"				=> (dopos Tokens.RPAREN yypos 1);
<INITIAL>"{"				=> (dopos Tokens.LBRACE yypos 1);
<INITIAL>"}"				=> (dopos Tokens.RBRACE yypos 1);
<INITIAL>"["				=> (dopos Tokens.LBRACK yypos 1);
<INITIAL>"]"				=> (dopos Tokens.RBRACK yypos 1);
<INITIAL>"->"				=> (dopos Tokens.ARROW yypos 2);
<INITIAL>","				=> (dopos Tokens.COMMA yypos 1);
<INITIAL>"&&"				=> (dopos Tokens.AND yypos 2);
<INITIAL>"||"				=> (dopos Tokens.OR yypos 2);
<INITIAL>"++"				=> (dopos Tokens.PLUSPLUS yypos 2);
<INITIAL>"--"				=> (dopos Tokens.MINUSMINUS yypos 2);
<INITIAL>"+="				=> (dopos Tokens.PLUSASSIGN yypos 1);
<INITIAL>"-="				=> (dopos Tokens.MINUSASSIGN yypos 1);
<INITIAL>"*="				=> (dopos Tokens.TIMESASSIGN yypos 1);
<INITIAL>"/="				=> (dopos Tokens.DIVIDEASSIGN yypos 1);
<INITIAL>"+"				=> (dopos Tokens.PLUS yypos 1);
<INITIAL>"-"				=> (dopos Tokens.MINUS yypos 1);
<INITIAL>"!"				=> (dopos Tokens.BANG yypos 1);
<INITIAL>"*"				=> (dopos Tokens.TIMES yypos 1);
<INITIAL>"/"				=> (dopos Tokens.DIVIDE yypos 1);
<INITIAL>"=="				=> (dopos Tokens.EQ yypos 2);
<INITIAL>"!="				=> (dopos Tokens.NEQ yypos 2);
<INITIAL>">="				=> (dopos Tokens.GE yypos 2);
<INITIAL>"<="				=> (dopos Tokens.LE yypos 2);
<INITIAL>">"				=> (dopos Tokens.GT yypos 1);
<INITIAL>"<"				=> (dopos Tokens.LT yypos 1);
<INITIAL>"="				=> (dopos Tokens.ASSIGN yypos 1);
<INITIAL>";"				=> (dopos Tokens.SEMICOLON yypos 1);
<INITIAL>"/*"				=> (commentLevel := !commentLevel+1; YYBEGIN COMMENT; continue());
<INITIAL>"*/"				=> (ErrorMsg.error yypos ("Illegal end of comment"); continue());
<COMMENT>"*/"				=> (commentLevel := !commentLevel-1;
								if !commentLevel = 0 then
								(YYBEGIN INITIAL; continue())
								else continue());
<COMMENT>"/*"				=> (commentLevel := !commentLevel+1; continue());
<COMMENT>.					=> (continue());

<INITIAL>"'"				=> (YYBEGIN CHARACTER; currentString := ""; unfinishedString := true; continue());
<CHARACTER>"'"				=> (YYBEGIN INITIAL; unfinishedString := false; (dopos3 Tokens.CHAR (!currentString) (yypos - (size (!currentString)) - 1) (size (!currentString))));
<CHARACTER>{newline}		=> (ErrorMsg.error yypos ("Illegal newline in character: " ^ (!currentString)); continue());
<CHARACTER>{escapeseqChar}	=> (currentString := !currentString ^ yytext; continue());
<CHARACTER>.				=> (currentString := !currentString ^ yytext; continue());


<INITIAL>"\""				=> (YYBEGIN STRING; currentString := ""; unfinishedString := true; continue());
<STRING>"\""				=> (YYBEGIN INITIAL; unfinishedString := false; (dopos3 Tokens.STRING (!currentString) (yypos - (size (!currentString)) - 1) (size (!currentString))));
<STRING>{newline}			=> (ErrorMsg.error yypos ("Illegal newline in string: " ^ (!currentString)); continue());
<STRING>{escapeseqStr}		=> (currentString := !currentString ^ yytext; continue());
<STRING>.					=> (currentString := !currentString ^ yytext; continue());

<INITIAL>{digits}			=> (dopos3 Tokens.INT (s2i yytext yypos) yypos (size yytext));
<INITIAL>{bools}			=> (dopos3 Tokens.BOOL (s2b yytext yypos) yypos (size yytext));
<INITIAL>{floats}			=> (dopos3 Tokens.FLOAT (s2f yytext yypos) yypos (size yytext));
<INITIAL>{letter}{idchars}	=> (dopos3 Tokens.ID yytext yypos (size yytext));
<INITIAL>{whitespace}		=> (continue());

<INITIAL>.					=> (ErrorMsg.error yypos ("Illegal character " ^ yytext); continue());
<INITIAL>{newline}			=> (lineNum := !lineNum+1;
								linePos := yypos :: !linePos;
								continue());