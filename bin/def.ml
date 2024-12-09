open Syntax
open Typing

let rec check_valid_ty tyl = function
  | Tvar { contents = Unbound { id; level = _ } } ->
      List.exists (occursin id) tyl
  | Tvar { contents = Linkto t } -> check_valid_ty tyl t
  | Tlist t -> check_valid_ty tyl t
  | Tref t -> check_valid_ty tyl t
  | Tarrow (arg, ret) -> check_valid_ty tyl arg && check_valid_ty tyl ret
  | Ttuple tyl' -> List.for_all (fun t -> check_valid_ty tyl t) tyl'
  | Tconstr (_, tyl') -> List.for_all (fun t -> check_valid_ty tyl t) tyl'
  | Trecord (_, _, fields) ->
      List.for_all (fun (_, t) -> check_valid_ty tyl t) fields
  | Tvariant (_, _, fields) ->
      List.for_all (fun (_, t) -> check_valid_ty tyl t) fields
  | _ -> true

let check_valid_decl decl =
  let rec aux = function
    | (_, { ast = Drecord (_, tyl, fields); _ }) :: rest ->
        if List.for_all (fun (_, t) -> check_valid_ty tyl t) fields then
          aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | (_, { ast = Dvariant (_, tyl, fields); _ }) :: rest ->
        if List.for_all (fun (_, t) -> check_valid_ty tyl t) fields then
          aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | (_, { ast = Dabbrev (_, tyl, ty); _ }) :: rest ->
        if check_valid_ty tyl ty then aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | [] -> ()
  in
  aux decl

type status = Checking | Checked

let name_is_checking name seen =
  if List.mem_assoc name seen then !(List.assoc name seen) = Checking else false

let name_is_checked name seen =
  if List.mem_assoc name seen then !(List.assoc name seen) = Checked else false

let rec is_abbrev name = function
  | (_, { ast = Dabbrev (name', _, _); _ }) :: _ when name = name' -> true
  | _ :: rest -> is_abbrev name rest
  | [] -> false

let rec abbrev_found_in_ty decl seen = function
  | Tlist t -> abbrev_found_in_ty decl seen (expand_abbrev t decl)
  | Tref t -> abbrev_found_in_ty decl seen (expand_abbrev t decl)
  | Tarrow (arg, ret) ->
      abbrev_found_in_ty decl seen (expand_abbrev arg decl);
      abbrev_found_in_ty decl seen (expand_abbrev ret decl)
  | Ttuple tyl ->
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev t decl))
        tyl
  | Tconstr (name, _) when name_is_checking name seen ->
      failwith (Printf.sprintf "recursive type abbreviation %s" name)
  | Tconstr (name, tyl) when name_is_checked name seen ->
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev t decl))
        tyl
  | Tconstr (name, tyl) when is_abbrev name decl ->
      abbrev_found_in_decl name seen decl;
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev t decl))
        tyl
  | _ -> ()

and abbrev_found_in_decl name seen decl =
  let rec aux = function
    | (_, { ast = Dabbrev (n, _, ty); _ }) :: _ when n = name ->
        let pair = (name, ref Checking) in
        abbrev_found_in_ty decl (pair :: seen) ty;
        snd pair := Checked
    | _ :: rest -> aux rest
    | [] -> failwith ("name not found abbrev_found_in_decl:" ^ name)
  in
  aux decl

let check_recursive_abbrev decl =
  let rec aux = function
    | (_, { ast = Dabbrev (name, _, _); _ }) :: rest ->
        abbrev_found_in_decl name [] decl;
        aux rest
    | _ :: rest -> aux rest
    | [] -> ()
  in
  aux decl

let rec is_def name = function
  | (_, { ast = Drecord (name', _, _); _ }) :: _ when name = name' -> true
  | (_, { ast = Dvariant (name', _, _); _ }) :: _ when name = name' -> true
  | _ :: rest -> is_def name rest
  | [] -> false

let rec def_found_in_ty decl seen = function
  | Tlist t -> def_found_in_ty decl seen t
  | Tarrow (arg, ret) ->
      def_found_in_ty decl seen arg;
      def_found_in_ty decl seen ret
  | Ttuple tyl -> List.iter (def_found_in_ty decl seen) tyl
  | Trecord (name, _, _) when name_is_checking name seen ->
      failwith (Printf.sprintf "recursive type definition %s" name)
  | Trecord (name, _, fields) when name_is_checked name seen ->
      List.iter (def_found_in_ty decl seen) (List.map snd fields)
  | Trecord (name, _, fields) when is_def name decl ->
      def_found_in_decl name seen decl;
      List.iter (abbrev_found_in_ty decl seen) (List.map snd fields)
  | Tvariant (name, _, _) when name_is_checking name seen ->
      failwith (Printf.sprintf "recursive type definition %s" name)
  | Tvariant (name, _, fields) when name_is_checked name seen ->
      List.iter (def_found_in_ty decl seen) (List.map snd fields)
  | Tvariant (name, _, fields) when is_def name decl ->
      def_found_in_decl name seen decl;
      List.iter (def_found_in_ty decl seen) (List.map snd fields)
  | Tconstr (name, _) when is_def name decl ->
      failwith (Printf.sprintf "recursive type definition %s" name)
  | Tconstr (_, _) as t -> def_found_in_ty decl seen (expand_abbrev t decl)
  | _ -> ()

and def_found_in_decl name seen decl =
  let rec aux = function
    | (_, { ast = Drecord (n, _, fields); _ }) :: _ when n = name ->
        let pair = (name, ref Checking) in
        List.iter
          (fun t -> def_found_in_ty decl (pair :: seen) t)
          (List.map snd fields);
        snd pair := Checked
    | (_, { ast = Dvariant (n, _, fields); _ }) :: _ when n = name ->
        let pair = (name, ref Checking) in
        List.iter
          (fun t -> def_found_in_ty decl (pair :: seen) t)
          (List.map snd fields);
        snd pair := Checked
    | _ :: rest -> aux rest
    | [] ->
        print_endline (Printf.sprintf "cycle found %s" name);
        failwith ("name not found def_found_in_decl:" ^ name)
  in
  aux decl

let check_recursive_def decl =
  let rec aux = function
    | (_, { ast = Drecord (name, _, _); _ }) :: rest ->
        def_found_in_decl name [] decl;
        aux rest
    | (_, { ast = Dvariant (name, _, _); _ }) :: rest ->
        def_found_in_decl name [] decl;
        aux rest
    | _ :: rest -> aux rest
    | [] -> ()
  in
  aux decl
