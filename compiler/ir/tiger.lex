type svalue = Tokens.svalue 
type pos = int 
type ('a,'b) token = ('a,'b) Tokens.token 
type lexresult = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos


val s = ref ""
val strStart = ref ~1
val inString = ref false

val nestedComment = ref 0
val commentPos = ref ~1
fun err(p1,p2) = ErrorMsg.error p1
fun eof() = 
  let 
    val pos = hd(!linePos) 
  in 
  (
    if !nestedComment = 0 then () else ErrorMsg.error(!commentPos) ("Comment not closed");
    if not (!inString) then () else ErrorMsg.error(!strStart) ("String not closed");
    Tokens.EOF(pos,pos) 
  )
  end

fun linesInStr str =
  let
    fun helper([], num) = num
      | helper((c::l), num) = if c = #"\n" then helper(l, num + 1) else helper(l, num)
  in
    helper(String.explode str, 0)
  end;

fun numToChar str =
  Char.toString(Char.chr(valOf(Int.fromString(String.extract(str, 1, NONE)))));


%%
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s STRING COMMENT FORMAT;
num=[0-9]+;
space=[\n\r\ \t];
%%

<INITIAL> " "|\t => (continue());

<INITIAL> \n|\r\n => (lineNum := !lineNum+1; 
                 linePos := yypos :: !linePos; 
                 continue());

<INITIAL> "/*" => (YYBEGIN COMMENT;
       commentPos := yypos;
       nestedComment := 1;
       continue());
<COMMENT> "*/" => (if !nestedComment>1 then () else YYBEGIN INITIAL;
       nestedComment := !nestedComment-1;
       continue());
<COMMENT> "/*" => (nestedComment := !nestedComment+1;
       continue());
<COMMENT> "\n" => (continue());
<COMMENT> . => (continue());

<INITIAL>"\"" => (s := ""; inString:=true; strStart := yypos; YYBEGIN STRING; continue());
<STRING>"\""  => (YYBEGIN INITIAL; inString:=false; Tokens.STRING(!s, !strStart, yypos));
<STRING>"\\n" => (s := !s ^ "\n"; continue());
<STRING>"\\t" => (s := !s ^ "\t"; continue());
<STRING>"\\\""  => (s := !s ^ "\""; continue());
<STRING>"\\\\"    => (s := !s ^ "\\"; continue());
<STRING>"\\^"[a-zA-Z]  => (continue());
<STRING>"\\"    => (YYBEGIN FORMAT; continue());
<STRING>\\[0-9][0-9][0-9] => (s := !s ^ (numToChar yytext); continue());

<STRING>\n => (ErrorMsg.error yypos ("newline in string is not allowed " ^ yytext); continue());

<STRING>.   => (s := !s ^ yytext; continue());

<FORMAT> {space}+\\ => (YYBEGIN STRING; (lineNum := !lineNum+ (linesInStr yytext); continue()));
<FORMAT> \\         => (YYBEGIN STRING; (ErrorMsg.error yypos ("Must only contain space characters"); continue()));
<FORMAT> {space}+   => (lineNum := !lineNum+ (linesInStr yytext); continue());
<FORMAT> .          => (ErrorMsg.error yypos ("illegal whitespace character " ^ yytext); continue());



<INITIAL> while    => (Tokens.WHILE(yypos,yypos+5));
<INITIAL> for      => (Tokens.FOR(yypos,yypos+3));
<INITIAL> to       => (Tokens.TO(yypos,yypos+2));
<INITIAL> break    => (Tokens.BREAK(yypos,yypos+5));
<INITIAL> let      => (Tokens.LET(yypos,yypos+3));
<INITIAL> in       => (Tokens.IN(yypos,yypos+2));
<INITIAL> end      => (Tokens.END(yypos,yypos+3));
<INITIAL> function => (Tokens.FUNCTION(yypos,yypos+8));
<INITIAL> var      => (Tokens.VAR(yypos,yypos+3));
<INITIAL> type     => (Tokens.TYPE(yypos,yypos+4));
<INITIAL> array    => (Tokens.ARRAY(yypos,yypos+5));
<INITIAL> if       => (Tokens.IF(yypos,yypos+2));
<INITIAL> then     => (Tokens.THEN(yypos,yypos+4));
<INITIAL> else     => (Tokens.ELSE(yypos,yypos+4));
<INITIAL> do       => (Tokens.DO(yypos,yypos+2));
<INITIAL> of       => (Tokens.OF(yypos,yypos+2));
<INITIAL> nil      => (Tokens.NIL(yypos,yypos+3));

<INITIAL> ","  => (Tokens.COMMA(yypos,yypos+1));
<INITIAL> ":"  => (Tokens.COLON(yypos,yypos+1));
<INITIAL> ";"  => (Tokens.SEMICOLON(yypos,yypos+1));
<INITIAL> "("  => (Tokens.LPAREN(yypos,yypos+1));
<INITIAL> ")"  => (Tokens.RPAREN(yypos,yypos+1));
<INITIAL> "["  => (Tokens.LBRACK(yypos,yypos+1));
<INITIAL> "]"  => (Tokens.RBRACK(yypos,yypos+1));
<INITIAL> "{"  => (Tokens.LBRACE(yypos,yypos+1));
<INITIAL> "}"  => (Tokens.RBRACE(yypos,yypos+1));
<INITIAL> "."  => (Tokens.DOT(yypos,yypos+1));
<INITIAL> "+"  => (Tokens.PLUS(yypos,yypos+1));
<INITIAL> "-"  => (Tokens.MINUS(yypos,yypos+1));
<INITIAL> "*"  => (Tokens.TIMES(yypos,yypos+1));
<INITIAL> "/"  => (Tokens.DIVIDE(yypos,yypos+1));
<INITIAL> "="  => (Tokens.EQ(yypos,yypos+1));
<INITIAL> "<>" => (Tokens.NEQ(yypos,yypos+2));
<INITIAL> "<"  => (Tokens.LT(yypos,yypos+1));
<INITIAL> "<=" => (Tokens.LE(yypos,yypos+2));
<INITIAL> ">"  => (Tokens.GT(yypos,yypos+1));
<INITIAL> ">=" => (Tokens.GE(yypos,yypos+2));
<INITIAL> "&"  => (Tokens.AND(yypos,yypos+1));
<INITIAL> "|"  => (Tokens.OR(yypos,yypos+1));
<INITIAL> ":=" => (Tokens.ASSIGN(yypos,yypos+2));

<INITIAL> [0-9]+ => (Tokens.INT(valOf(Int.fromString(yytext)), yypos, yypos+size(yytext)));

<INITIAL> [a-zA-Z][a-zA-Z0-9_]* => (Tokens.ID(yytext, yypos, yypos+size(yytext)));

<INITIAL> .   => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());