%{
  open Syntax
  let make_loc i j = (i, j)
  let make_expr expr' i j = {ast = ref expr' ; pos = make_loc i j}
  let make_pat pat' i j = {ast = ref pat' ; pos = make_loc i j}
  let make_decl decl' i j = {ast = decl' ; pos = make_loc i j}
  let make_def mod' i j = {ast = mod' ; pos = make_loc i j}
%}
%token LPAREN "(" RPAREN ")" LBRACK "[" RBRACK "]" LBRACE "{" RBRACE "}"
%token COLON ":" COMMA "," SEMI ";" SEMISEMI ";;" CONS "::" QUOTE "'" DOT "."
%token BEGIN END TUNIT TBOOL TINT TFLOAT TSTRING TCHAR OPEN TLIST
%token <string> LID UID
%token WILD "_" AS
%token <int> INT
%token <char> CHAR
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token TYPE ARROW "->" OF
%token MATCH WITH FUNCTION
%token LET REC AND IN VAL STRUCT SIG FUNCTOR MODULE SIGNATURE INCLUDE
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

%start<mod_expr list> top
%start<mod_expr list> repl

%%

top             : list(def_) EOF                     { $1 }

repl            : list(def_) SEMISEMI                { $1 }
                | expr SEMISEMI                      { [make_def(Mexpr $1) ($startpos($1)) ($endpos($2))] }

def_            : TYPE separated_nonempty_list(AND, ty_def)
                                                    { make_def(Mtype $2)($startpos($1)) ($endpos($2)) }
                | LET separated_nonempty_list(AND, let_def)
                                                    { make_def(Mlet $2) ($startpos($1)) ($endpos($2)) }
                | LET REC separated_nonempty_list(AND, let_rec_def)
                                                    { make_def(Mletrec $3) ($startpos($1)) ($endpos($3)) }
                | OPEN path                         { make_def(Mopen $2) ($startpos($1)) ($endpos($2)) }                                         
                | MODULE UID "=" mod_expr           { make_def(Mmodule($2,$4)) ($startpos($1)) ($endpos($2)) }  
                | MODULE UID COLON sig_expr "=" mod_expr 
                { make_def(Mmodule($2,make_def(Mseal($6, $4)) ($startpos($4)) ($endpos($6)))) ($startpos($1)) ($endpos($6)) }  
                | SIGNATURE UID "=" sig_expr        { make_def(Msig($2,$4)) ($startpos($1)) ($endpos($2)) }  

sig_def         : VAL LID COLON ty                  { make_def(Sval($2,$4)) ($startpos($1)) ($endpos($4)) }
                | TYPE separated_nonempty_list(AND, ty_def)
                                                    { make_def(Stype $2)($startpos($1)) ($endpos($2)) }
                | MODULE UID ":" sig_expr           { make_def(Smodule($2,$4)) ($startpos($1)) ($endpos($4)) }  
                | SIGNATURE UID "=" sig_expr        { make_def(Ssig($2,$4)) ($startpos($1)) ($endpos($4)) }  
                | INCLUDE path                      { make_def(Sinclude $2) ($startpos($1)) ($endpos($2)) }    

sig_expr        : UID                               { make_def(Svar $1) ($startpos($1)) ($endpos($1))  }
                | UID WITH TYPE separated_nonempty_list(AND, ty_def_)
                                                    { make_def(Swith(make_def(Svar $1) ($startpos($1)) ($endpos($1)), $4)) ($startpos($1)) ($endpos($4)) }
                | SIG list(sig_def) END             { make_def(Sstruct $2) ($startpos($1)) ($endpos($3))  }
                | FUNCTOR LPAREN UID COLON sig_expr RPAREN "->" sig_expr  { make_def(Sfunctor(($3,$5),$8)) ($startpos($1)) ($endpos($8))  }

mod_expr        : mod_simple_expr                   { $1 }
                | mod_simple_expr mod_simple_expr+  { make_def(Mapply($1, $2)) ($startpos($1)) ($endpos($2)) }
                | FUNCTOR LPAREN UID COLON sig_expr RPAREN  "->"  mod_expr  
                    { make_def(Mfunctor(($3,$5), $8)) ($startpos($1)) ($endpos($8)) }

mod_simple_expr : UID                               { make_def(Mvar $1) ($startpos($1)) ($endpos($1)) }
                | LPAREN mod_expr RPAREN            { make_def($2.ast) ($startpos($1)) ($endpos($3)) }
                | STRUCT list(def_) END             { make_def(Mstruct $2) ($startpos($1)) ($endpos($3)) }
                | mod_simple_expr "." UID           { make_def(Maccess($1, $3)) ($startpos($1)) ($endpos($3)) }

path            : path "." UID                      { $1@[$3] }
                | UID                               { $1::[] }

expr            : simple_expr                       { $1 }
                | simple_expr_ simple_expr+         { make_expr(Eapply($1,$2)) ($startpos($1)) ($endpos($2)) }
                | MATCH expr WITH function_case     { make_expr(Eapply(make_expr(Efunction($4)) ($startpos($4)) ($endpos($4)),[$2])) ($startpos($1)) ($endpos($4)) }
                | FUNCTION function_case            { make_expr(Efunction($2)) ($startpos($1)) ($endpos($2)) }
                | FUN fun_case                      { make_expr(Efunction([$2])) ($startpos($1)) ($endpos($2)) }
                | LET separated_nonempty_list(AND, let_def) IN expr
                                                    { make_expr(Elet($2,$4)) ($startpos($1)) ($endpos($4)) }
                | LET REC separated_nonempty_list(AND, let_rec_def) IN expr
                                                    { make_expr(Eletrec($3,$5)) ($startpos($1)) ($endpos($5)) }
                | expr ";" expr                     { make_expr(Esequence($1,$3))($startpos($1)) ($endpos($3)) }
                | IF expr THEN expr ELSE expr       { make_expr(Econdition($2,$4,$6)) ($startpos($1)) ($endpos($6)) }
                | expr binop expr                   { make_expr(Eapply(make_expr(Eprim $2) ($startpos($2)) ($endpos($2)),$1::$3::[])) ($startpos($1)) ($endpos($3)) }
                | expr ":=" expr                    { make_expr(Eassign($1,$3)) ($startpos($1)) ($endpos($3)) }
                | expr "::" expr                    { make_expr(Econs($1,$3)) ($startpos($1)) ($endpos($3)) }
                | "-" expr %prec prec_uminus        { make_expr(Eapply(make_expr(Eprim Pnegint) ($startpos($1)) ($endpos($1)),$2::[])) ($startpos($1)) ($endpos($2)) }
                | "-." expr %prec prec_uminus       { make_expr(Eapply(make_expr(Eprim Pnegfloat)  ($startpos($1)) ($endpos($1)),$2::[])) ($startpos($1)) ($endpos($2)) }
                | LNOT expr                         { make_expr(Eapply(make_expr(Eprim Plnot) ($startpos($1)) ($endpos($1)),$2::[])) ($startpos($1)) ($endpos($2)) }
                | NOT expr                          { make_expr(Eapply(make_expr(Eprim Pnot) ($startpos($1)) ($endpos($1)),$2::[])) ($startpos($1)) ($endpos($2)) }
                | REF expr                          { make_expr(Eref($2)) ($startpos($1)) ($endpos($2)) }
                | "!" expr                          { make_expr(Ederef($2)) ($startpos($1)) ($endpos($2)) }
                | UID simple_expr                   { make_expr(Econstruct($1,$2)) ($startpos($1)) ($endpos($2)) }

simple_expr     : UID                               { make_expr(Econstruct($1,make_expr Etag ($startpos($1)) ($endpos($1)))) ($startpos($1)) ($endpos($1)) }
                | simple_expr_                      { $1 }

simple_expr_    :
                | ident                             { make_expr(Evar $1) ($startpos($1)) ($endpos($1)) }
                | "(" binop ")"                     { make_expr(Eprim $2) ($startpos($1)) ($endpos($3)) }
                | const_expr                        { make_expr(Econstant $1) ($startpos($1)) ($endpos($1)) }
                | "[" "]"                           { make_expr Enil ($startpos($1)) ($endpos($2)) }
                | "[" expr_semi_list "]"            { List.fold_left (fun cdr car -> make_expr(Econs(car,cdr)) ($startpos($1)) ($endpos($3))) (make_expr Enil ($startpos($1)) ($endpos($3))) $2 }
                | "{" expr_label_list "}"           { make_expr (Erecord $2) ($startpos($1)) ($endpos($3)) }
                | "(" ")"                           { make_expr Eunit ($startpos($1)) ($endpos($2)) }
                | "(" expr "," separated_nonempty_list(",",expr) ")"
                                                    { make_expr(Etuple($2::$4)) ($startpos($1)) ($endpos($5)) }
                | "(" expr ":" ty ")"               { make_expr(Econstraint($2,$4)) ($startpos($1)) ($endpos($5)) }
                | "(" expr ")"                      { make_expr(EBlock1($2)) ($startpos($1)) ($endpos($3)) }
                | BEGIN expr END                    { make_expr(EBlock1($2)) ($startpos($1)) ($endpos($3)) }
                | simple_expr_ "." LID              { make_expr(Erecord_access($1,$3)) ($startpos($1)) ($endpos($3)) }
                | path "." LID                      { make_expr(Epath($1,$3)) ($startpos($1)) ($endpos($3)) }

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
                                                    { (make_pat(Pparams $1) ($startpos($1)) ($endpos($1)),$3) }

function_case   : "|" pat "->" expr                 { [($2,$4)] }
                | "|" pat WHEN expr "->" expr       { [($2,make_expr(Ewhen($4,$6)) ($startpos($4)) ($endpos($4)))] }
                | "|" pat "->" expr function_case   { ($2,$4)::$5 }
                | "|" pat WHEN expr "->" expr function_case
                                                    { ($2,make_expr(Ewhen($4,$6)) ($startpos($4)) ($endpos($4)))::$7 }


let_def         : pat "=" expr                      { ($1,$3) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (make_pat(Pvar $1) ($startpos($1)) ($endpos($2)),make_expr(Efunction((make_pat(Pparams $2) ($startpos($2)) ($endpos($2)),$4)::[])) ($startpos($4)) ($endpos($4))) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (make_pat(Pvar $1) ($startpos($1)) ($endpos($4)),make_expr(Efunction((make_pat(Pparams $2) ($startpos($2)) ($endpos($2)),make_expr(Econstraint($6,$4)) ($startpos($6)) ($endpos($6)))::[])) ($startpos($6)) ($endpos($6))) }

let_rec_def     : ident "=" expr                    { (make_pat(Pvar $1) ($startpos($1))($endpos($1)) ,$3) }
                | ident nonempty_list(simple_pat) "=" expr
                                                    { (make_pat(Pvar $1) ($startpos($1)) ($endpos($2)),make_expr(Efunction((make_pat(Pparams $2) ($startpos($2)) ($endpos($2)),$4)::[])) ($startpos($4)) ($endpos($4))) }
                | ident nonempty_list(simple_pat) ":" ty "=" expr
                                                    { (make_pat(Pvar $1) ($startpos($1)) ($endpos($4)),make_expr(Efunction((make_pat(Pparams $2) ($startpos($2)) ($endpos($2)),make_expr(Econstraint($6,$4)) ($startpos($6)) ($endpos($6)))::[])) ($startpos($6)) ($endpos($6))) }

pat             : simple_pat                        { $1 }
                | pat AS lid                        { make_pat(Palias($1,$3)) ($startpos($1)) ($endpos($3)) }
                | pat "::" pat                      { make_pat(Pcons($1,$3)) ($startpos($1)) ($endpos($3)) }
                | UID simple_pat                    { make_pat(Pconstruct($1,$2)) ($startpos($1)) ($endpos($2)) }
                | REF simple_pat                    { make_pat(Pref $2) ($startpos($1)) ($endpos($2)) }

comma_pat       :  pat "," separated_nonempty_list(",", pat)
                                                    { $1::$3 }

pat_semi_list   : pat ";" pat_semi_list             { make_pat(Pcons($1,$3)) ($startpos($1)) ($endpos($3)) }
                | pat                               { make_pat(Pcons($1,make_pat Pnil ($startpos($1)) ($endpos($1)))) ($startpos($1)) ($endpos($1)) }

simple_pat      : ident                             { make_pat(Pvar $1)($startpos($1)) ($endpos($1)) }
                | UID                               { make_pat(Pconstruct($1,make_pat Ptag ($startpos($1)) ($endpos($1)))) ($startpos($1)) ($endpos($1)) }
                | "_"                               { make_pat(Pwild) ($startpos($1)) ($endpos($1)) }
                | const_expr                        { make_pat(Pconstant $1) ($startpos($1)) ($endpos($1)) }
                | "{" separated_nonempty_list(";", separated_pair(field, "=", pat)) "}"
                                                    { make_pat (Precord $2) ($startpos($1)) ($endpos($3)) }
                | "[" pat_semi_list "]"             { $2 }
                | "[" "]"                           { make_pat Pnil ($startpos($1)) ($endpos($2)) }
                | "(" ")"                           { make_pat Punit ($startpos($1)) ($endpos($2)) }
                | "(" pat ":" ty ")"                { make_pat (Pconstraint ($2,$4)) ($startpos($1)) ($endpos($5)) }
                | "(" pat ")"                       { $2 }
                | "(" comma_pat ")"                 { make_pat (Ptuple $2) ($startpos($1)) ($endpos($2)) }


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
                                                    { ($2, make_decl(Drecord($2,$1,$5)) ($startpos($1)) ($endpos($6))) }
                | params tyname "=" nonempty_list("|" sum_case { $2 })
                                                    { ($2, make_decl(Dvariant($2,$1,$4)) ($startpos($1)) ($endpos($4))) }
                | params tyname "=" ty              { ($2, make_decl(Dabbrev($2,$1,$4)) ($startpos($1)) ($endpos($4))) }
                | params tyname                     { ($2, make_decl(Dabs($2,$1, Tvar(ref (Linkto (Tabs (Tvar (ref (Unbound {id=Idstr $2; level= generic})), [])))))) ($startpos($1)) ($endpos($2))) }

ty_def_         : params tyname "=" "{" separated_nonempty_list(";", separated_pair(field, ":", ty)) "}"
                                                    { ($2, make_decl(Drecord($2,$1,$5)) ($startpos($1)) ($endpos($6))) }
                | params tyname "=" nonempty_list("|" sum_case { $2 })
                                                    { ($2, make_decl(Dvariant($2,$1,$4)) ($startpos($1)) ($endpos($4))) }
                | params tyname "=" ty              { ($2, make_decl(Dabbrev($2,$1,$4)) ($startpos($1)) ($endpos($4))) }


ty              : simple_ty                         { $1 }
                | ty "->" ty                        { Tarrow($1,$3) }
                | tuple_ty                          { Ttuple $1 }

tuple_ty        : simple_ty "*" separated_nonempty_list("*", simple_ty)
                                                    { $1::$3 }

simple_ty       : "(" ty "," separated_nonempty_list(",", ty) ")" tyname
                                                    { Tconstr($6,$2::$4) }
                | simple_ty tyname                  { Tconstr($2,$1::[]) }
                | tyname                            { Tconstr($1,[]) }
                | "(" ty "," separated_nonempty_list(",", ty) ")" path "." tyname
                                                    { Tvar(ref (Linkto(Tpath($6, Tconstr($8,$2::$4))))) }
                | simple_ty path "." tyname                  { Tvar(ref (Linkto (Tpath($2, Tconstr($4,$1::[]))))) }
                | path "." tyname                            { Tvar(ref (Linkto(Tpath($1, Tconstr($3,[]))))) }
                | TUNIT                             { Tunit }
                | TBOOL                             { Tbool }
                | TINT                              { Tint }
                | TFLOAT                            { Tfloat }
                | TCHAR                             { Tchar }
                | TSTRING                           { Tstring }
                | simple_ty REF                     { Tref $1 }
                | simple_ty TLIST                   { Tlist $1 }
                | param                             { $1 }
                | "(" ty ")"                        { $2 }

sum_case        : UID                               { ($1, Ttag) }
                | UID OF ty                         { ($1, $3) }
