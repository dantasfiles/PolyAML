type svalue = Tokens.svalue
type pos = int*int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult  = (svalue,pos) token


(* current line number *)
val lineNum:int ref = ErrorMsg.lineNum  

(* character position from beginning of file that corresponds to the 
 * beginning of lineNum *)
val linePos: int ref = ErrorMsg.linePos


(* increment the line number and set the character position from the begnning
 * of the file for lineNum to be p *)
fun newLine p = 
    (lineNum := !lineNum+1; linePos := p)

(* use p (the current character position from the beginning of the file)
 * and linePos to figure out the column number of this error *)
fun charPos p = 
    p - (!linePos)


fun make_pos yypos yytext = 
( (!lineNum, charPos yypos), (!lineNum, (charPos yypos) + String.size(yytext) - 1))


(* handling EOF *)
fun eof x = 
     Tokens.EOF(make_pos (!linePos) " ")

val charlist = ref [""]
fun addString (charlist,s:string) = charlist := s :: (!charlist)
fun makeString charlist = (concat(rev(!charlist)) before charlist := nil)

%%

%header (functor AspectMLLexFun(structure Tokens: AspectML_TOKENS));
%s S;

ws = ("\012"|[\t\ ])*;
alpha = [A-Za-z];
digit = [0-9];
number = ([1-9]{digit}*)|0;
idchars=[A-Za-z'_0-9];
id=[A-Za-z$]{idchars}*;
some_sym=[!%&+/:<=>?@~|#*]|\-|\^;
quote="`";

%%
<INITIAL>all => (Tokens.ALL(make_pos yypos yytext));
<INITIAL>unit => (Tokens.UNIT(make_pos yypos yytext));
<INITIAL>string => (Tokens.STRINGTYP(make_pos yypos yytext));
<INITIAL>stack => (Tokens.STACK(make_pos yypos yytext));
<INITIAL>let => (Tokens.LET(make_pos yypos yytext));
<INITIAL>in => (Tokens.IN(make_pos yypos yytext));
<INITIAL>of => (Tokens.OF(make_pos yypos yytext));
<INITIAL>nil => (Tokens.NIL(make_pos yypos yytext));
<INITIAL>before => (Tokens.BEFORE(make_pos yypos yytext));
<INITIAL>after => (Tokens.AFTER(make_pos yypos yytext));
<INITIAL>pc => (Tokens.PC(make_pos yypos yytext));
<INITIAL>stkcase => (Tokens.STKCASE(make_pos yypos yytext));
<INITIAL>typecase => (Tokens.TYPECASE(make_pos yypos yytext));
<INITIAL>any => (Tokens.ANY(make_pos yypos yytext));
<INITIAL>rec => (Tokens.REC(make_pos yypos yytext));
<INITIAL>advice => (Tokens.ADVICE(make_pos yypos yytext));
<INITIAL>case-advice => (Tokens.CASEADVICE(make_pos yypos yytext));
<INITIAL>true => (Tokens.TRUE(make_pos yypos yytext));
<INITIAL>false => (Tokens.FALSE(make_pos yypos yytext));
<INITIAL>if => (Tokens.IF(make_pos yypos yytext));
<INITIAL>then => (Tokens.THEN(make_pos yypos yytext));
<INITIAL>else => (Tokens.ELSE(make_pos yypos yytext));
<INITIAL>printint =>(Tokens.PRINTINT(make_pos yypos yytext));
<INITIAL>println => (Tokens.PRINTLN(make_pos yypos yytext));
<INITIAL>print => (Tokens.PRINT(make_pos yypos yytext));
<INITIAL>int => (Tokens.INTTYP(make_pos yypos yytext));
<INITIAL>bool => (Tokens.BOOL(make_pos yypos yytext));
<INITIAL>itos => (Tokens.ITOS(make_pos yypos yytext));
<INITIAL>abort => (Tokens.ABORT(make_pos yypos yytext));

<INITIAL>"==" => (Tokens.EQEQ(make_pos yypos yytext));
<INITIAL>"->" => (Tokens.ARROW(make_pos yypos yytext));
<INITIAL>"=>" => (Tokens.DOUBLEARROW(make_pos yypos yytext));
<INITIAL>"++" => (Tokens.DOUBLEPLUS(make_pos yypos yytext));

<INITIAL>"(" => (Tokens.LPAREN(make_pos yypos yytext));
<INITIAL>")" => (Tokens.RPAREN(make_pos yypos yytext));
<INITIAL>"[" => (Tokens.LBRACKET(make_pos yypos yytext));
<INITIAL>"]" => (Tokens.RBRACKET(make_pos yypos yytext));
<INITIAL>"{" => (Tokens.LBRACE(make_pos yypos yytext));
<INITIAL>"}" => (Tokens.RBRACE(make_pos yypos yytext));
<INITIAL>":" => (Tokens.COLON(make_pos yypos yytext));
<INITIAL>"\." => (Tokens.PERIOD(make_pos yypos yytext));
<INITIAL>"," => (Tokens.COMMA(make_pos yypos yytext));
<INITIAL>"=" => (Tokens.EQUALS(make_pos yypos yytext));
<INITIAL>"|" => (Tokens.PIPE(make_pos yypos yytext));
<INITIAL>"_" => (Tokens.UNDERSCORE(make_pos yypos yytext));
<INITIAL>"+" => (Tokens.PLUS(make_pos yypos yytext));
<INITIAL>";" => (Tokens.SEMICOLON(make_pos yypos yytext));
<INITIAL>"^" => (Tokens.CARET(make_pos yypos yytext));

<INITIAL>\"	=> (charlist := [""]; YYBEGIN S; continue());
<S>\"	        => (let val s = makeString charlist
                        val (p1, p2) = make_pos yypos yytext
                    in YYBEGIN INITIAL;
                       Tokens.STRING (s,p1,p2)
                    end);
<S>\\a		=> (addString(charlist, "\007"); continue());
<S>\\b		=> (addString(charlist, "\008"); continue());
<S>\\f		=> (addString(charlist, "\012"); continue());
<S>\\n		=> (addString(charlist, "\010"); continue());
<S>\\r		=> (addString(charlist, "\013"); continue());
<S>\\t		=> (addString(charlist, "\009"); continue());
<S>\\v		=> (addString(charlist, "\011"); continue());
<S>\\\\		=> (addString(charlist, "\\"); continue());
<S>\\\"		=> (addString(charlist, "\""); continue());
<S>({idchars}|{some_sym}|\[|\]|\(|\)|{quote}|[,.;^{}])+|.  => (addString(charlist,yytext); continue());



<INITIAL>{id}  => (let val (p1,p2) = make_pos yypos yytext in Tokens.ID (yytext, p1, p2) end);
<INITIAL>{number} => (let val (p1, p2) = make_pos yypos yytext in Tokens.INT ((case (Int.fromString yytext) of SOME i => i), p1, p2) end);
<INITIAL>\n       => (newLine yypos; continue ());
<INITIAL>[\ \t\b] => (continue ());
INITIAL>.        => (ErrorMsg.error (make_pos yypos yytext) ("illegal character " ^ yytext); continue ());
