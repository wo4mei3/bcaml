%{
  open Syntax
  let make_loc i j = (Parsing.rhs_start_pos i, Parsing.rhs_end_pos j)
  let make_expr expr' i j = {ast = ref expr' ; pos = make_loc i j}
  let make_pat pat' i j = {ast = ref pat' ; pos = make_loc i j}
  let make_decl decl' i j = {ast = decl' ; pos = make_loc i j}
  let make_def def' i j = {ast = def' ; pos = make_loc i j}
%}
%token LPAREN "(" RPAREN ")" LBRACK "[" RBRACK "]" LBRACE "{" RBRACE "}"
%token COLON ":" COMMA "," SEMI ";" SEMISEMI ";;" CONS "::" QUOTE "'" DOT "."
%token BEGIN END TUNIT TBOOL TINT TFLOAT TSTRING TCHAR OPEN
%token <string> LID UID
%token WILD "_" AS
%token <int> INT
%token <char> CHAR
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token TYPE ARROW "->" OF
%token MATCH WITH FUNCTION
%token LET REC AND IN
%token FUN BAR "|" BARBAR "||"
%token IF THEN ELSE WHEN
%token REF DEREF "!" ASSIGN ":="
%token AT "@"
%token EQ "=" NQ "<>" LT "<" GT ">" LE "<=" GE ">=" EQIMM "==" NQIMM "!="
%token PLUS "+" PLUSDOT "+."
%token STAR "*" STARDOT "*." STARSTAR "**"
%token MINUS "-" MINUSDOT "-."
%token DIV "/" DIVDOT "/."
%token LSL LSR ASR
%token MOD
%token AMPERAMPER "&&" NOT
%token LAND LOR LXOR LNOT
%token EOF

%nonassoc IN
%right "->"
%right ";"
%right prec_list
%nonassoc ELSE

%right ":="
%left AS
%left "|"
%left "||"
%left "&&"
%left "=" "<>" "<" ">" "<=" ">=" "==" "!="
%right "@"
%right "::"
%left  "+" "+." "-" "-."
%left  "*" "*." "/" "/." MOD LAND LOR LXOR
%right LSL LSR ASR "**"
%right prec_uminus
%right REF "!" LNOT NOT

%start<def list> top
%start<def list> def

%%

top             : list(def_) EOF                     { $1 }

def             : list(def_) SEMISEMI                { $1 }
                | expr SEMISEMI                      { [make_def(Defexpr $1) 1 2] }

def_            : TYPE separated_nonempty_list(AND, ty_def)
                                                    { make_def(Deftype $2) 1 2 }
                | LET separated_nonempty_list(AND, let_def)
                                                    { make_def(Deflet $2) 1 2 }
                | LET REC separated_nonempty_list(AND, let_rec_def)
                                                    { make_def(Defletrec $3) 1 3 }
                | OPEN STRING                       { make_def(Defopen $2) 1 2 }                                         

expr            : simple_expr                       { $1 }
                | simple_expr_ simple_expr+         { make_expr(Eapply($1,$2)) 1 2 }
                | MATCH expr WITH function_case     { make_expr(Eapply(make_expr(Efunction($4)) 4 4,[$2])) 1 4 }
                | FUNCTION function_case            { make_expr(Efunction($2)) 1 2 }
                | FUN fun_case                      { make_expr(Efunction([$2])) 1 2 }
                | LET separated_nonempty_list(AND, let_def) IN expr
                                                    { make_expr(Elet($2,$4))1 4 }
                | LET REC separated_nonempty_list(AND, let_rec_def) IN expr
                                                    { make_expr(Eletrec($3,$5)) 1 5 }
                | expr ";" expr                     { make_expr(Esequence($1,$3)) 1 3 }
                | IF expr THEN expr ELSE expr       { make_expr(Econdition($2,$4,$6)) 1 6 }
                | expr binop expr                   { make_expr(Eapply(make_expr(Eprim $2) 2 2,$1::$3::[])) 1 3 }
                | expr ":=" expr                    { make_expr(Eassign($1,$3)) 1 3 }
                | expr "::" expr                    { make_expr(Econs($1,$3)) 1 3 }
                | "-" expr %prec prec_uminus        { make_expr(Eapply(make_expr(Eprim Pnegint) 1 1,$2::[])) 1 2 }
                | "-." expr %prec prec_uminus       { make_expr(Eapply(make_expr(Eprim Pnegfloat) 1 1,$2::[])) 1 2 }
                | LNOT expr                         { make_expr(Eapply(make_expr(Eprim Plnot) 1 1,$2::[])) 1 2 }
                | NOT expr                          { make_expr(Eapply(make_expr(Eprim Pnot) 1 1,$2::[])) 1 2 }
                | REF expr                          { make_expr(Eref($2)) 1 2 }
                | "!" expr                          { make_expr(Ederef($2)) 1 2 }
                | UID simple_expr                   { make_expr(Econstruct($1,$2)) 1 2 }

simple_expr     : UID                               { make_expr(Econstruct($1,make_expr Etag 1 1)) 1 1 }
                | simple_expr_                      { $1 }

simple_expr_    :
                | ident                             { make_expr(Evar $1) 1 1 }
                | "(" binop ")"                     { make_expr(Eprim $2) 1 3 }
                | const_expr                        { make_expr(Econstant $1) 1 1 }
                | "[" "]"                           { make_expr Enil 1 2 }
                | "[" expr_semi_list "]"            { List.fold_left (fun cdr car -> make_expr(Econs(car,cdr)) 1 3) (make_expr Enil 1 3) $2 }
                | "{" expr_label_list "}"           { make_expr (Erecord $2) 1 3 }
                | "(" ")"                           { make_expr Eunit 1 2 }
                | "(" expr "," separated_nonempty_list(",",expr) ")"
                                                    { make_expr(Etuple($2::$4)) 1 5 }
                | "(" expr ":" ty ")"               { make_expr(Econstraint($2,$4)) 1 5 }
                | "(" expr ")"                      { $2 }
                | BEGIN expr END                    { $2 }
                | simple_expr "." LID               { make_expr(Erecord_access($1,$3)) 1 3 }

expr_semi_list  : expr_semi_list ";" expr %prec prec_list
                                                    { $3::$1 }
                | expr %prec prec_list              { [$1] }

expr_label_list : expr_label_list ";" field "=" expr{ ($3,$5)::$1 }
                | field "=" expr                    { ($1,$3)::[] }
  

const_expr      : INT                               { (Cint($1)) }
                | CHAR                              { (Cchar($1)) }
                | STRING                            { (Cstring($1)) }
                | BOOL                              { (Cbool($1)) }
                | FLOAT                             { (Cfloat($1)) }

fun_case        : nonempty_list(simple_pat) "->" expr
                                                    { (make_pat(Pparams $1) 1 1,$3) }

function_case   : "|" pat "->" expr                 { [($2,$4)] }
                | "|" pat WHEN expr "->" expr       { [($2,make_expr(Ewhen($4,$6)) 4 4)] }
                | "|" pat "->" expr function_case   { ($2,$4)::$5 }
                | "|" pat WHEN expr "->" expr function_case
                                                    { ($2,make_expr(Ewhen($4,$6)) 4 4)::$7 }


let_def         : pat "=" expr                      { ($1,$3) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (make_pat(Pvar $1) 1 2,make_expr(Efunction((make_pat(Pparams $2) 2 2,$4)::[])) 4 4) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (make_pat(Pvar $1) 1 4,make_expr(Efunction((make_pat(Pparams $2) 2 2,make_expr(Econstraint($6,$4)) 6 6)::[])) 6 6) }

let_rec_def     : ident "=" expr                    { (make_pat(Pvar $1) 1 1,$3) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (make_pat(Pvar $1) 1 2,make_expr(Efunction((make_pat(Pparams $2) 2 2,$4)::[])) 4 4) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (make_pat(Pvar $1) 1 4,make_expr(Efunction((make_pat(Pparams $2) 2 2,make_expr(Econstraint($6,$4)) 6 6)::[])) 6 6) }

pat             : simple_pat                        { $1 }
                | pat AS lid                        { make_pat(Palias($1,$3)) 1 3 }
                | pat "::" pat                      { make_pat(Pcons($1,$3)) 1 3 }
                | UID simple_pat                    { make_pat(Pconstruct($1,$2)) 1 2 }
                | REF simple_pat                    { make_pat(Pref $2) 1 2 }

comma_pat       :  pat "," separated_nonempty_list(",", pat)
                                                    { $1::$3 }

pat_semi_list   : pat ";" pat_semi_list             { make_pat(Pcons($1,$3))1 3 }
                | pat                               { make_pat(Pcons($1,make_pat Pnil 1 1)) 1 1 }

simple_pat      : ident                             { make_pat(Pvar $1) 1 1 }
                | UID                               { make_pat(Pconstruct($1,make_pat Ptag 1 1)) 1 1 }
                | "_"                               { make_pat(Pwild) 1 1 }
                | const_expr                        { make_pat(Pconstant $1) 1 1 }
                | "{" separated_nonempty_list(";", separated_pair(field, "=", pat)) "}"
                                                    { make_pat (Precord $2) 1 3 }
                | "[" pat_semi_list "]"             { $2 }
                | "[" "]"                           { make_pat Pnil 1 2 }
                | "(" ")"                           { make_pat Punit 1 2 }
                | "(" pat ":" ty ")"                { make_pat (Pconstraint ($2,$4)) 1 5 }
                | "(" pat ")"                       { $2 }
                | "(" comma_pat ")"                 { make_pat (Ptuple $2) 1 2 }


lid             : LID                               { $1 }
field           : lid                               { $1 }
tyname          : lid                               { $1 }
ident           : lid                               { $1 }


%inline binop   : "||"                              { Por }
                | "&&"                              { Pand }
                | "="                               { Peq }
                | "<>"                              { Pnq }
                | "<"                               { Plt }
                | ">"                               { Pgt }
                | "<="                              { Ple }
                | ">="                              { Pge }
                | "=="                              { Peqimm }
                | "!="                              { Pnqimm }
                | "@"                               { Pconcat }
                | "+"                               { Paddint }
                | "-"                               { Psubint }
                | "*"                               { Pmulint }
                | "/"                               { Pdivint }
                | "+."                              { Paddfloat }
                | "-."                              { Psubfloat }
                | "*."                              { Pmulfloat }
                | "/."                              { Pdivfloat }
                | "**"                              { Ppower }
                | MOD                               { Pmod }
                | LAND                              { Pland }
                | LOR                               { Plor }
                | LXOR                              { Plxor }
                | LSL                               { Plsl }
                | LSR                               { Plsr }
                | ASR                               { Pasr }


param           : "'" lid                           { Tvar (ref (Unbound {id=Idstr $2; level= generic})) }

params          :                                   { [] }
                | param                             { $1::[] }
                | "(" separated_nonempty_list(",", param) ")"
                                                    { $2 }

ty_def          : params tyname "=" "{" separated_nonempty_list(";", separated_pair(field, ":", ty)) "}"
                                                    { make_decl(Drecord($2,$1,$5)) 1 6 }
                | params tyname "=" nonempty_list("|" sum_case { $2 })
                                                    { make_decl(Dvariant($2,$1,$4)) 1 4 }
                | params tyname "=" ty              { make_decl(Dabbrev($2,$1,$4)) 1 4 }

ty              : simple_ty                         { $1 }
                | ty "->" ty                        { Tarrow($1,$3) }
                | tuple_ty                          { Ttuple $1 }

tuple_ty        : simple_ty "*" separated_nonempty_list("*", simple_ty)
                                                    { $1::$3 }

simple_ty       : "(" ty "," separated_nonempty_list(",", ty) ")" tyname
                                                    { Tconstr($6,$2::$4) }
                | simple_ty tyname                  { Tconstr($2,$1::[]) }
                | TUNIT                             { Tunit }
                | TBOOL                             { Tbool }
                | TINT                              { Tint }
                | TFLOAT                            { Tfloat }
                | TCHAR                             { Tchar }
                | TSTRING                           { Tstring }
                | simple_ty REF                     { Tref $1 }
                | tyname                            { Tconstr($1,[]) }
                | param                             { $1 }
                | "(" ty ")"                        { $2 }

sum_case        : UID                               { ($1, Ttag) }
                | UID OF ty                         { ($1, $3) }
