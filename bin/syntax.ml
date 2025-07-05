let generic = -1
let notgeneric = 0

type id_kind = Idint of int | Idstr of string [@@deriving show]
type tyvar = { id : id_kind; level : int } [@@deriving show]

type link = Unbound of tyvar | Linkto of ty [@@deriving show]

and ty =
  | Tunknown
  | Tvar of link ref
  | Tunit
  | Tbool
  | Tint
  | Tfloat
  | Tchar
  | Tstring
  | Tlist of ty
  | Tref of ty
  | Tformat of ty * ty
  | Tarrow of ty * ty
  | Ttuple of ty list
  | Tconstr of string * ty list
  | Trecord of string * ty list * (string * ty) list
  | Tvariant of string * ty list * (string * ty) list
  | Tpath of string * path * ty
  | Tabs of string * ty * ty list
  | Ttag
[@@deriving show]

and tyl = ty list [@@deriving show]
and path = string list [@@deriving show]

let is_zero_arity = function
  | Tunit | Tbool | Tint | Tfloat | Tchar | Tstring -> true
  | _ -> false

type constant =
  | Cint of int
  | Cbool of bool
  | Cfloat of float
  | Cstring of string
  | Cchar of char
[@@deriving show]

type prim =
  | Peq
  | Pnq
  | Plt
  | Pgt
  | Ple
  | Pge
  | Peqimm
  | Pnqimm
  | Pnot
  | Pand
  | Por
  | Pnegint
  | Paddint
  | Psubint
  | Pmulint
  | Pdivint
  | Pmod
  | Plnot
  | Pland
  | Plor
  | Plxor
  | Plsl
  | Plsr
  | Pasr
  | Pnegfloat
  | Paddfloat
  | Psubfloat
  | Pmulfloat
  | Pdivfloat
  | Ppower
  | Pconcatstring
  | Pintoffloat
  | Pfloatofint
  | Pintofchar
  | Pcharofint
  | Pstringofbool
  | Pboolofstring
  | Pstringofint
  | Pintofstring
  | Pstringoffloat
  | Pfloatofstring
  | Pconcat
  | Pfailwith
  | Pprintf
  | Psprintf
[@@deriving show]

let get_pos
    ( { Lexing.pos_lnum = a1; Lexing.pos_bol = b1; Lexing.pos_cnum = c1; _ },
      { Lexing.pos_lnum = a2; Lexing.pos_bol = b2; Lexing.pos_cnum = c2; _ } ) =
  ((a1, c1 - b1 + 1), (a2, c2 - b2 + 1))

type pos = [%import: Lexing.position] [@@deriving show]
type position = pos * pos [@@deriving show]
type 'item ast = { ast : 'item; pos : position } [@@deriving show]

let file = ref ""

let print_loc file ((a1, b1), (a2, b2)) =
  if a2 > a1 then
    Printf.sprintf
      "File \"%s\", lines %d-%d, characters Ln%d, Col%d - Ln%d, Col%d:\n" file
      a1 a2 a1 b1 a2 b2
  else Printf.sprintf "File \"%s\", line %d, characters %d-%d:\n" file a1 b1 b2

let print_errloc filename pos =
  let pos = get_pos pos in
  print_loc filename pos

type expr = expr' ref ast [@@deriving show]

and expr' =
  | Evar of string
  | Econstant of constant
  | Eprim of prim
  | Etuple of expr list
  | Enil
  | Econs of expr * expr
  | Elist of expr list
  | Eref of expr
  | Ederef of expr
  | Eassign of expr * expr
  | Eloc of int
  | Etag
  | Eunit
  | Econstruct of string * expr
  | Eapply of expr * expr list
  | Elet of (pat * expr) list * expr
  | Eletrec of (pat * expr) list * expr
  | Efix of expr * (pat * expr) list
  | Efunction of (pat * expr) list
  | Esequence of expr * expr
  | Econdition of expr * expr * expr
  | Econstraint of expr * ty
  | Erecord of (string * expr) list
  | Erecord_access of expr * string
  | Ewhen of expr * expr
  | Epath of path * string
  | EBlock1 of expr
[@@deriving show]

and pat = pat' ref ast [@@deriving show]

and pat' =
  | Pwild
  | Pvar of string
  | Pparams of pat list
  | Palias of pat * string
  | Pconstant of constant
  | Ptuple of pat list
  | Pnil
  | Pcons of pat * pat
  | Pref of pat
  | Punit
  | Ptag
  | Pconstruct of string * pat
  | Pconstraint of pat * ty
  | Precord of (string * pat) list
[@@deriving show]

type type_decl = type_decl' ast [@@deriving show]

and type_decl' =
  | TDrecord of string * ty list * (string * ty) list
  | TDvariant of string * ty list * (string * ty) list
  | TDabbrev of string * ty list * ty
  | TDabs of string * ty list * ty
[@@deriving show]

type sig_expr = sig_expr' ast

and sig_expr' =
  | Svar of string
  | Sfunctor of (string * sig_expr) * sig_expr
  | Swith of sig_expr * (string * type_decl) list
  | Sstruct of decl_expr list
[@@deriving show]

and decl_expr = decl_expr' ast

and decl_expr' =
  | Dval of string * ty
  | Dtype of (string * type_decl) list
  | Dmodule of string * sig_expr
  | Dsig of string * sig_expr
  | Dinclude of path
[@@deriving show]

type mod_expr = mod_expr' ast [@@deriving show]

and mod_expr' =
  | Mvar of string
  | Maccess of mod_expr * string
  | Mfunctor of (string * sig_expr) * mod_expr
  | Mapply of mod_expr * mod_expr list
  | Mseal of mod_expr * sig_expr
  | Mstruct of bind_expr list
[@@deriving show]

and matches = (pat * expr) list [@@deriving show]
and def_list = mod_expr list [@@deriving show]
and bind_expr = bind_expr' ast [@@deriving show]

and bind_expr' =
  | Bexpr of expr
  | Blet of (pat * expr) list
  | Bletrec of (pat * expr) list
  | Btype of (string * type_decl) list
  | Bmodule of string * mod_expr
  | Bsig of (string * sig_expr)
  | Bopen of path
[@@deriving show]

type atomic_sig =
  | AtomSig_value of ty
  | AtomSig_type of type_decl
  | AtomSig_module of compound_sig
[@@deriving show]

and compound_sig =
  | ComSig_struct of ty list * (string * atomic_sig) list
  | ComSig_fun of ty list * (string * atomic_sig) * compound_sig
[@@deriving show]

type tyenv = (string * atomic_sig) list [@@deriving show]

let rec find_val n = function
  | (name, AtomSig_value ty) :: _ when n = name -> Some ty
  | _ :: xs -> find_val n xs
  | [] -> None

let rec find_type n = function
  | (name, AtomSig_type decl) :: _ when n = name -> Some decl
  | _ :: xs -> find_type n xs
  | [] -> None

let rec find_mod n = function
  | (name, AtomSig_module compound_sig) :: _ when n = name -> Some compound_sig
  | _ :: xs -> find_mod n xs
  | [] -> None

let get_struct = function
  | ComSig_struct (_, l) -> l
  | _ -> failwith "get_struct"

let get_functor = function
  | ComSig_fun (_, arg, ret) -> (arg, ret)
  | _ -> failwith "get_struct"

let get_abs = function ComSig_struct (l, _) | ComSig_fun (l, _, _) -> l

let get_constant = function
  | Econstant cst -> cst
  | _ -> failwith "get_constant"

let get_int = function Cint i -> i | _ -> failwith "get_int"
let get_bool = function Cbool b -> b | _ -> failwith "get_bool"
let get_float = function Cfloat f -> f | _ -> failwith "get_float"
let get_string = function Cstring s -> s | _ -> failwith "get_string"
let get_char = function Cchar c -> c | _ -> failwith "get_char"

let prim_list =
  [
    ("=", Peq);
    ("<>", Pnq);
    ("<", Plt);
    (">", Pgt);
    ("<=", Ple);
    (">=", Pge);
    ("==", Peqimm);
    ("!=", Pnqimm);
    ("not", Pnot);
    ("&&", Pand);
    ("||", Por);
    ("~-", Pnegint);
    ("+", Paddint);
    ("-", Psubint);
    ("*", Pmulint);
    ("/", Pdivint);
    ("mod", Pmod);
    ("lnot", Plnot);
    ("land", Pland);
    ("lor", Plor);
    ("lxor", Plxor);
    ("lsl", Plsl);
    ("lsr", Plsr);
    ("asr", Pasr);
    ("~-.", Pnegfloat);
    ("+.", Paddfloat);
    ("-.", Psubfloat);
    ("*.", Pmulfloat);
    ("/.", Pdivfloat);
    ("**", Ppower);
    ("^", Pconcatstring);
    ("int_of_float", Pintoffloat);
    ("float_of_int", Pfloatofint);
    ("int_of_char", Pintofchar);
    ("char_of_int", Pcharofint);
    ("string_of_bool", Pstringofbool);
    ("bool_of_string", Pboolofstring);
    ("string_of_int", Pstringofint);
    ("int_of_string", Pintofstring);
    ("string_of_float", Pstringoffloat);
    ("float_of_string", Pfloatofstring);
    ("@", Pconcat);
    ("failwith", Pfailwith);
    ("printf", Pprintf);
    ("sprintf", Psprintf);
  ]

let is_unary = function
  | Pnot | Pnegint | Plnot | Pnegfloat | Pintoffloat | Pfloatofint | Pintofchar
  | Pcharofint | Pstringofbool | Pboolofstring | Pstringofint | Pintofstring
  | Pstringoffloat | Pfloatofstring | Pfailwith ->
      true
  | _ -> false

let is_varargs = function Pprintf | Psprintf -> true | _ -> false
let is_binary prim = not (is_unary prim || is_varargs prim)

type unary_op =
  | Uint_to_int of (int -> int)
  | Uint_to_float of (int -> float)
  | Uint_to_char of (int -> char)
  | Uint_to_string of (int -> string)
  | Ubool_to_bool of (bool -> bool)
  | Ubool_to_string of (bool -> string)
  | Ufloat_to_float of (float -> float)
  | Ufloat_to_int of (float -> int)
  | Ufloat_to_string of (float -> string)
  | Ustring_to_string of (string -> string)
  | Ustring_to_bool of (string -> bool)
  | Ustring_to_int of (string -> int)
  | Ustring_to_float of (string -> float)
  | Uchar_to_char of (char -> char)
  | Uchar_to_int of (char -> int)

type binary_op =
  | Bint of (int -> int -> int)
  | Bbool of (bool -> bool -> bool)
  | Bfloat of (float -> float -> float)
  | Bstring of (string -> string -> string)
  | Bchar of (char -> char -> char)

let do_unary op e =
  match (op, !(e.ast)) with
  | Uint_to_int op, Econstant (Cint i) -> Econstant (Cint (op i))
  | Uint_to_float op, Econstant (Cint i) -> Econstant (Cfloat (op i))
  | Uint_to_char op, Econstant (Cint i) -> Econstant (Cchar (op i))
  | Uint_to_string op, Econstant (Cint i) -> Econstant (Cstring (op i))
  | Ubool_to_bool op, Econstant (Cbool b) -> Econstant (Cbool (op b))
  | Ubool_to_string op, Econstant (Cbool b) -> Econstant (Cstring (op b))
  | Ufloat_to_float op, Econstant (Cfloat f) -> Econstant (Cfloat (op f))
  | Ufloat_to_int op, Econstant (Cfloat f) -> Econstant (Cint (op f))
  | Ufloat_to_string op, Econstant (Cfloat f) -> Econstant (Cstring (op f))
  | Ustring_to_string op, Econstant (Cstring s) -> Econstant (Cstring (op s))
  | Ustring_to_bool op, Econstant (Cstring s) -> Econstant (Cbool (op s))
  | Ustring_to_int op, Econstant (Cstring s) -> Econstant (Cint (op s))
  | Ustring_to_float op, Econstant (Cstring s) -> Econstant (Cfloat (op s))
  | Uchar_to_char op, Econstant (Cchar c) -> Econstant (Cchar (op c))
  | Uchar_to_int op, Econstant (Cchar c) -> Econstant (Cint (op c))
  | _ -> failwith "do_unary"

let do_binary op x y =
  match (op, !(x.ast), !(y.ast)) with
  | Bint op, Econstant (Cint x), Econstant (Cint y) -> Econstant (Cint (op x y))
  | Bbool op, Econstant (Cbool x), Econstant (Cbool y) ->
      Econstant (Cbool (op x y))
  | Bfloat op, Econstant (Cfloat x), Econstant (Cfloat y) ->
      Econstant (Cfloat (op x y))
  | Bstring op, Econstant (Cstring x), Econstant (Cstring y) ->
      Econstant (Cstring (op x y))
  | Bchar op, Econstant (Cchar x), Econstant (Cchar y) ->
      Econstant (Cchar (op x y))
  | _ -> failwith "do_binary"

let do_binary_eq op x y =
  match (!(x.ast), !(y.ast)) with
  | Econstant (Cint x), Econstant (Cint y) ->
      Econstant (Cbool ((Obj.magic op : _ -> _ -> bool) x y))
  | Econstant (Cbool x), Econstant (Cbool y) ->
      Econstant (Cbool ((Obj.magic op : _ -> _ -> bool) x y))
  | Econstant (Cfloat x), Econstant (Cfloat y) ->
      Econstant (Cbool ((Obj.magic op : _ -> _ -> bool) x y))
  | Econstant (Cstring x), Econstant (Cstring y) ->
      Econstant (Cbool ((Obj.magic op : _ -> _ -> bool) x y))
  | Econstant (Cchar x), Econstant (Cchar y) ->
      Econstant (Cbool ((Obj.magic op : _ -> _ -> bool) x y))
  | _ -> failwith "do_binary_eq"
