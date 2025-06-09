open Eval
open Syntax

let int_to_alpha i =
  if i < 26 then Printf.sprintf "%c" (Char.chr (i + 97))
  else Printf.sprintf "%c%d" (Char.chr ((i mod 26) + 97)) (i / 26)

let tvars_counter = ref 0
let tvars_names = ref []

let reset_tvar_name () =
  tvars_counter := 0;
  tvars_names := []

let name_of_tvar tvar =
  try List.assoc tvar !tvars_names
  with Not_found ->
    let name = int_to_alpha !tvars_counter in
    let varname = name in
    incr tvars_counter;
    tvars_names := (tvar, varname) :: !tvars_names;
    varname

let rec pp_ty = function
  | Tvar { contents = Unbound { id; level } } when level = generic ->
      "'" ^ name_of_tvar id
  | Tvar { contents = Unbound { id; level = _ } } -> "'" ^ "_" ^ name_of_tvar id
  | Tvar { contents = Linkto ty } -> pp_ty ty
  | Tunit -> "unit"
  | Tbool -> "bool"
  | Tint -> "int"
  | Tfloat -> "float"
  | Tchar -> "char"
  | Tstring -> "string"
  | Tlist ty -> pp_ty ty ^ " list"
  | Tref ty -> pp_ty ty ^ " ref"
  | Tformat (fst, snd) -> "( " ^ pp_ty fst ^ "," ^ pp_ty snd ^ ") format"
  | Tarrow (l, r) ->
      let pp_l = pp_ty l in
      "(" ^ pp_l ^ " -> " ^ pp_ty r ^ ")"
  | Ttuple [] -> "(,)"
  | Ttuple (x :: xl) ->
      let pp_x = pp_ty x in
      "(" ^ pp_x ^ List.fold_left (fun s x -> s ^ " * " ^ pp_ty x) "" xl ^ ") "
  | Tconstr (name, []) -> name
  | Tconstr (name, x :: []) -> pp_ty x ^ " " ^ name
  | Tconstr (name, x :: xl) ->
      let pp_x = pp_ty x in
      "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ") " ^ name
  | Trecord (name, [], _) -> name
  | Trecord (name, x :: [], _) -> pp_ty x ^ " " ^ name
  | Trecord (name, x :: xl, _) ->
      let pp_x = pp_ty x in
      "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ") " ^ name
  | Tvariant (name, [], _) -> name
  | Tvariant (name, x :: [], _) -> pp_ty x ^ " " ^ name
  | Tvariant (name, x :: xl, _) ->
      let pp_x = pp_ty x in
      "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ") " ^ name
  | Tunknown -> "Tunknown"
  | Ttag -> "Ttag"
  | Tpath (name, path, _) -> String.concat "." path ^ "." ^ name
  | Tabs (name, _, _) -> name
(*^ show_ty ty*)
(*| ty -> failwith (Printf.sprintf "pp_ty %s" (show_ty ty))*)

let pp_decl decl =
  match decl.ast with
  | TDrecord (n, [], (name, ty) :: []) ->
      "type " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | TDrecord (n, x :: [], (name, ty) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | TDrecord (n, x :: xl, (name, ty) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | TDrecord (n, [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ pp_fields tl ^ "}"
  | TDrecord (n, x :: [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty
      ^ pp_fields tl ^ "}"
  | TDrecord (n, x :: xl, (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ pp_fields tl ^ "}"
  | TDvariant (n, [], (name, Ttag) :: []) -> "type " ^ n ^ " = | " ^ name
  | TDvariant (n, x :: [], (name, Ttag) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name
  | TDvariant (n, x :: xl, (name, Ttag) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name
  | TDvariant (n, [], (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = | " ^ name ^ pp_fields tl
  | TDvariant (n, x :: [], (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl
  | TDvariant (n, x :: xl, (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl
  | TDvariant (n, [], (name, ty) :: []) ->
      "type " ^ name ^ " = | " ^ n ^ " of " ^ pp_ty ty
  | TDvariant (n, x :: [], (name, ty) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
  | TDvariant (n, x :: xl, (name, ty) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
  | TDvariant (n, [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
  | TDvariant (n, x :: [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
      ^ pp_fields tl
  | TDvariant (n, x :: xl, (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
  | TDabbrev (n, [], ty) -> "type " ^ n ^ " = " ^ pp_ty ty
  | TDabbrev (n, x :: [], ty) -> "type " ^ pp_ty x ^ " " ^ n ^ " = " ^ pp_ty ty
  | TDabbrev (n, x :: xl, ty) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = " ^ pp_ty ty
  | TDabs (n, [], _) -> "type " ^ n
  | TDabs (n, x :: [], _) -> "type " ^ pp_ty x ^ " " ^ n
  | TDabs (n, x :: xl, _) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n
  | _ -> failwith "pp_tydecl"

let pp_cst = function
  | Cint i -> string_of_int i
  | Cbool b -> string_of_bool b
  | Cfloat f -> string_of_float f
  | Cchar c -> Printf.sprintf "'%C'" c
  | Cstring s -> Printf.sprintf "\"%s\"" s

let pp_val expr =
  let rec aux expr n =
    if n > 10 then "..."
    else
      match !(expr.ast) with
      | Econstant cst -> pp_cst cst
      | Eprim _ -> "<fun>"
      | Etuple (x :: xl) ->
          "("
          ^ aux x (n + 1)
          ^ List.fold_left (fun s x -> s ^ ", " ^ aux x (n + 1)) "" xl
          ^ ")"
      | Elist [] -> "[]"
      | Elist (x :: []) -> "[" ^ aux x (n + 1) ^ "]"
      | Elist (x :: xl) ->
          "["
          ^ aux x (n + 1)
          ^ List.fold_left (fun s x -> s ^ "; " ^ aux x (n + 1)) "" xl
          ^ "]"
      | Eloc l -> "ref " ^ aux (lookuploc l) (n + 1)
      | Eunit -> "()"
      | Econstruct (name, { ast = { contents = Etag; _ }; _ }) -> name
      | Econstruct (name, expr) -> name ^ " " ^ aux expr (n + 1)
      | Efix _ -> "<fun>"
      | Efunction _ -> "<fun>"
      | Erecord ((name, x) :: []) ->
          let pp_x = aux x (n + 1) in
          "{" ^ name ^ " = " ^ pp_x ^ "}"
      | Erecord ((name, x) :: xl) ->
          let pp_x = aux x (n + 1) in
          "{" ^ name ^ " = " ^ pp_x
          ^ List.fold_left
              (fun s (name, x) -> s ^ "; " ^ name ^ " = " ^ aux x (n + 1))
              "" xl
          ^ "}"
      | Epath (path, name) -> String.concat "." path ^ "." ^ name
      | _ -> failwith (show_expr expr)
  in
  aux expr 0

let rec pp_atomic_sig sema_sig =
  let ret =
    match sema_sig with
    | n, AtomSig_value ty -> "val " ^ n ^ " : " ^ pp_ty ty
    | _, AtomSig_type decl -> pp_decl decl
    | "_", AtomSig_module compound_sig -> pp_compound_sig compound_sig
    | n, AtomSig_module compound_sig ->
        "module type " ^ n ^ " = " ^ pp_compound_sig compound_sig
  in
  reset_tvar_name ();
  ret

and pp_compound_sig sema_sig =
  let ret =
    match sema_sig with
    | ComSig_struct env -> "sig" ^ pp_env env ^ " end"
    | ComSig_fun ((n, arg), ret) ->
        " functor (" ^ n ^ ": "
        ^ pp_atomic_sig ("_", arg)
        ^ " ) -> \n" ^ pp_compound_sig ret
  in
  reset_tvar_name ();
  ret

and pp_env env =
  List.fold_left (fun s sema_sig -> s ^ " " ^ pp_atomic_sig sema_sig) "" env
