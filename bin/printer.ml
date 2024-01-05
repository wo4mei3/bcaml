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
(*| ty -> Printf.sprintf "%s" (*(show_ty ty)*)*)
(*| ty -> failwith (Printf.sprintf "pp_ty %s" (show_ty ty))*)

let pp_decl = function
  | Drecord (n, [], (name, ty) :: []) ->
      "type " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | Drecord (n, x :: [], (name, ty) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | Drecord (n, x :: xl, (name, ty) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ "}"
  | Drecord (n, [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ pp_fields tl ^ "}"
  | Drecord (n, x :: [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty
      ^ pp_fields tl ^ "}"
  | Drecord (n, x :: xl, (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, ty) :: xl -> "; " ^ name ^ " : " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = {" ^ name ^ " : " ^ pp_ty ty ^ pp_fields tl ^ "}"
  | Dvariant (n, [], (name, Ttag) :: []) -> "type " ^ n ^ " = | " ^ name
  | Dvariant (n, x :: [], (name, Ttag) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name
  | Dvariant (n, x :: xl, (name, Ttag) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name
  | Dvariant (n, [], (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = | " ^ name ^ pp_fields tl
  | Dvariant (n, x :: [], (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl
  | Dvariant (n, x :: xl, (name, Ttag) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ pp_fields tl
  | Dvariant (n, [], (name, ty) :: []) ->
      "type " ^ name ^ " = | " ^ n ^ " of " ^ pp_ty ty
  | Dvariant (n, x :: [], (name, ty) :: []) ->
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
  | Dvariant (n, x :: xl, (name, ty) :: []) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
  | Dvariant (n, [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
  | Dvariant (n, x :: [], (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      "type " ^ pp_ty x ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty
      ^ pp_fields tl
  | Dvariant (n, x :: xl, (name, ty) :: tl) ->
      let rec pp_fields = function
        | [] -> ""
        | (name, Ttag) :: xl -> " | " ^ name ^ pp_fields xl
        | (name, ty) :: xl -> " | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields xl
      in
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = | " ^ name ^ " of " ^ pp_ty ty ^ pp_fields tl
  | Dabbrev (n, [], ty) -> "type " ^ n ^ " = " ^ pp_ty ty
  | Dabbrev (n, x :: [], ty) -> "type " ^ pp_ty x ^ " " ^ n ^ " = " ^ pp_ty ty
  | Dabbrev (n, x :: xl, ty) ->
      let pp_x = pp_ty x in
      "type " ^ "(" ^ pp_x
      ^ List.fold_left (fun s x -> s ^ "," ^ pp_ty x) "" xl
      ^ ")" ^ " " ^ n ^ " = " ^ pp_ty ty
  | _ -> failwith "pp_tydecl"

let pp_decls decls =
  let ret = List.fold_left (fun s decl -> s ^ "\n" ^ pp_decl decl) "" decls in
  reset_tvar_name ();
  ret

let pp_cst = function
  | Cint i -> string_of_int i
  | Cbool b -> string_of_bool b
  | Cfloat f -> string_of_float f
  | Cchar c -> Printf.sprintf "'%C'" c
  | Cstring s -> Printf.sprintf "\"%s\"" s

let pp_exp expr =
  let rec aux expr n =
    if n > 10 then "..."
    else
      match !expr with
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
      | Econstruct (name, { contents = Etag; _ }) -> name
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
      | _ -> failwith "pp_exp"
  in
  aux expr 0
