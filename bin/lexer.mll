{
  open Parser

  let escaped_chars = [
    ('\\', "\\");
    ('\'', "'");
    ('"', "\"");
    ('n', "\n");
    ('t', "\t");
    ('b', "\b");
    ('r', "\r");
  ]

  let escaped_conv char =
    try 
      List.assoc char escaped_chars
    with Not_found ->
      failwith "escaped_conv error"
}

let lid = ( ['a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*
            | ['_' 'a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']+)

let uid = ['A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

let int = ['0'-'9'] ['0'-'9' '_']*

let int_ =
    ( ("0x" | "0X") ['0'-'9' 'a'-'f' 'A'-'F'] (['0'-'9' 'a'-'f' 'A'-'F'] | '_')*
    | ("0o" | "0O") ['0'-'7'] ['0'-'7' '_']*
    | ("0b" | "0B") ['0' '1'] ['0' '1' '_']*)

let float =
  '-'? ['0'-'9'] ['0'-'9' '_']*
  (('.' ['0'-'9' '_']*) (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)? |
   ('.' ['0'-'9' '_']*)? (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*))




rule token = parse
| '\n'                { Lexing.new_line lexbuf; token lexbuf }
| [' ' '\r' '\t']     { token lexbuf }
| "(*"                { comment 0 lexbuf }
| "true"              { BOOL true }
| "false"             { BOOL false }
| int                 { INT (int_of_string (Lexing.lexeme lexbuf)) }
| int_                { INT (int_of_string (Lexing.lexeme lexbuf)) }
| float               { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
| "'" ([^ '\\' '\''] as c) "'"  { CHAR c }
| "'" '\\' (['\\' '\'' 'n' 't' 'b' 'r'] as c) "'" { CHAR ((escaped_conv c).[0]) }
| '"'                 { STRING (string "" lexbuf) }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACK }
| "]" { RBRACK }
| "{" { LBRACE }
| "}" { RBRACE }
| "|" { BAR }
| ";;"{ SEMISEMI }
| ";" { SEMI }
| "," { COMMA }
| ":" { COLON }
| "." { DOT }

| "=" { EQ }
| "->" { ARROW }
| "!" { DEREF }
| ":=" { ASSIGN }
| "::" { CONS }
| "@"  { AT }

| "+" { PLUS }
| "-." { MINUSDOT }
| "-" { MINUS }
| "*" { STAR }
| "/" { DIV }
| "+." { PLUSDOT }
| "-." { MINUSDOT }
| "*." { STARDOT }
| "/." { DIVDOT }
| "**" { STARSTAR }
| "%" { MOD }
| "'" { QUOTE }
| "&&" { AMPERAMPER }
| "||" { BARBAR }
| "land" {LAND }
| "lor" { LOR }
| "lxor" { LXOR }
| "lnot" {LNOT }
| "lsl" { LSL }
| "lsr" { LSR }
| "asr" { ASR }

| "==" { EQIMM }
| "!=" { NQIMM }
| "=" { EQ }
| "<>" { NQ }
| "<" { LT }
| ">" { GT }
| "<=" { LE }
| ">=" { GE }

| "not" { NOT }


| "_" { WILD }
| "and" { AND }
| "begin" { BEGIN }
| "end" { END }
| "else" { ELSE }
| "function" { FUNCTION }
| "when"  { WHEN }
| "fun" { FUN }
| "if" { IF }
| "in" { IN }
| "open" { OPEN }
| "let" { LET }
| "of" { OF }
| "rec" { REC }
| "ref" { REF }
| "then" { THEN }
| "type" { TYPE }
| "unit" { TUNIT }
| "bool" { TBOOL }
| "int" { TINT }
| "float" { TFLOAT }
| "char" { TCHAR }
| "string" { TSTRING }

| lid as s { LID s }
| uid as s { UID s }

| eof { EOF }

| _ { failwith "lexer token error" }


and comment n = parse
| "*)"                { if n = 0 then token lexbuf else comment (n - 1) lexbuf }
| "(*"                { comment (n + 1) lexbuf }
| '\n'                { Lexing.new_line lexbuf; comment n lexbuf }
| _                   { comment n lexbuf }
| eof                 { failwith "lexer comment error" }

and string acc = parse
| '"'   { acc }
| '\\' (['\\' '"' 'n' 't' 'b' 'r'] as c) { string (acc ^ (escaped_conv c)) lexbuf }
| eof { failwith "lexer token error" }
| _ { string (acc ^ (Lexing.lexeme lexbuf)) lexbuf }