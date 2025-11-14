open Syntax
open Printer

let curr_id = ref 0

let gen_id () =
  let ret = !curr_id in
  incr curr_id;
  ret

let new_type_var level abstract =
  Tvar (ref { link = Unbound { id = Idint (gen_id ()); level }; abstract })

let min_opt lhs rhs =
  match (lhs, rhs) with
  | Some l, Some r -> Some (min l r)
  | Some l, None -> Some l
  | None, Some r -> Some r
  | None, None -> None

let rec get_type_level ty =
  match ty with
  | Tvar { contents = { link = Unbound { id = _; level }; _ } } -> Some level
  | Tvar { contents = { link = Linkto ty; _ } } -> get_type_level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar | Tstring -> None
  | Tlist ty | Tref ty -> get_type_level ty
  | Tarrow (arg, ret) -> min_opt (get_type_level arg) (get_type_level ret)
  | Ttuple tyl | Tconstr (_, tyl) -> get_type_level_list tyl
  | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
      get_type_level_list (List.map snd fields)
  | Ttag -> None
  | _ ->
      print_endline (show_ty ty);
      failwith "get_type_level"

and get_type_level_list = function
  | [] -> None
  | [ ty ] -> get_type_level ty
  | ty :: rest ->
      let lv1 = get_type_level ty in
      let lv2 = get_type_level_list rest in
      min_opt lv1 lv2

let free_type_vars level ty =
  let fv = ref [] in
  let rec free_vars ty =
    match ty with
    | Tvar _ -> (
        match get_type_level ty with
        | Some level' when level' >= level -> fv := ty :: !fv
        | _ -> ())
    | Tlist ty | Tref ty -> free_vars ty
    | Tarrow (arg, ret) ->
        free_vars arg;
        free_vars ret
    | Ttuple tyl | Tconstr (_, tyl) -> List.iter free_vars tyl
    | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
        List.iter free_vars (List.map snd fields)
    | _ -> ()
  in
  free_vars ty;
  !fv

let rec generalize level ty =
  match ty with
  | Tvar link -> (
      match link with
      | { contents = { link = Unbound { id; level = level' }; abstract } }
        when level' > level ->
          link := { link = Unbound { id; level = generic }; abstract }
      | { contents = { link = Linkto ty; _ } } -> generalize level ty
      | _ -> ())
  | Tlist ty -> generalize level ty
  | Tref ty -> generalize level ty
  | Tarrow (arg, ret) ->
      generalize level arg;
      generalize level ret
  | Ttuple tyl -> List.iter (generalize level) tyl
  | Tconstr (_, tyl) -> List.iter (generalize level) tyl
  | Trecord (_, _, fields) ->
      List.iter (fun (_, ty) -> generalize level ty) fields
  | Tvariant (_, _, fields) ->
      List.iter (fun (_, ty) -> generalize level ty) fields
  | _ -> ()

let instantiate_sub id_var_hash level ty is_expr =
  let rec f ty =
    match ty with
    | Tvar link -> (
        match link with
        | {
         contents = { link = Unbound { id; level = level' }; abstract = false };
        }
          when level' = generic && is_expr -> (
            try Hashtbl.find id_var_hash id
            with Not_found ->
              let tvar = new_type_var level false in
              Hashtbl.add id_var_hash id tvar;
              tvar)
        | { contents = { link = Linkto ty; abstract = false } } when is_expr ->
            Tvar { contents = { link = Linkto (f ty); abstract = false } }
            (*let tvar = new_type_var level abstract in
              ignore (ty, abstract);
                tvar*)
        | { contents = { link = Unbound { id; level = level' }; abstract } }
          when level' = generic && not is_expr -> (
            try Hashtbl.find id_var_hash id
            with Not_found ->
              let tvar = new_type_var level abstract in
              Hashtbl.add id_var_hash id tvar;
              tvar)
        | { contents = { link = Linkto ty; abstract } } when not is_expr ->
            Tvar { contents = { link = Linkto (f ty); abstract } }
            (*let tvar = new_type_var level abstract in
              ignore (ty, abstract);
                tvar*)
        | _ -> ty)
    | Tlist ty -> Tlist (f ty)
    | Tref ty -> Tref (f ty)
    | Tarrow (arg, ret) -> Tarrow (f arg, f ret)
    | Ttuple tyl -> Ttuple (List.map f tyl)
    | Tconstr (name, tyl) -> (
        try Hashtbl.find id_var_hash (Idstr name)
        with Not_found -> Tconstr (name, List.map f tyl))
    | Trecord (name, tyl, fields) ->
        Trecord
          (name, List.map f tyl, List.map (fun (n, ty) -> (n, f ty)) fields)
    | Tvariant (name, tyl, fields) ->
        Tvariant
          (name, List.map f tyl, List.map (fun (n, ty) -> (n, f ty)) fields)
    | _ -> ty
  in
  f ty

let instantiate level ty = instantiate_sub (Hashtbl.create 10) level ty true

let instantiate_mod_item id_var_hash level ty =
  instantiate_sub id_var_hash level ty false

let type_of_decl' = function
  | { ast = TDrecord (n, tyl, fields); _ } -> (
      match instantiate generic (Trecord (n, tyl, fields)) with
      | Trecord (_, tyl, _) as ty -> (tyl, ty)
      | _ -> failwith "type_of_decl")
  | { ast = TDvariant (n, tyl, fields); _ } -> (
      match instantiate generic (Tvariant (n, tyl, fields)) with
      | Tvariant (_, tyl, _) as ty -> (tyl, ty)
      | _ -> failwith "type_of_decl")
  | { ast = TDabbrev (n, tyl, ty); _ } -> (
      match instantiate generic (Trecord (n, tyl, [ ("temp", ty) ])) with
      | Trecord (_, tyl, [ ("temp", ty) ]) -> (tyl, ty)
      | _ -> failwith "type_of_decl")
  | { ast = TDabs (_, tyl, ty); _ } ->
      (*
        match instantiate generic (Trecord ("_", tyl, [ ("temp", ty) ])) with
        | Trecord (_, tyl, [ ("temp", ty) ]) -> (tyl, ty)
        | _ -> failwith "type_of_decl"*)
      (tyl, ty)

let rec type_of_decl env name =
  match env with
  | (n, AtomSig_type decl) :: _ when n = name -> type_of_decl' decl
  | _ :: xs -> type_of_decl xs name
  | [] -> failwith (Printf.sprintf "type_of_decl %s" name)

(*
let rec is_unbound_tvar = function
  | Tvar link -> (
      match link with
      | { contents = Unbound _ } -> true
      | { contents = Linkto ty } -> is_unbound_tvar ty)
  | _ -> false
*)
let rec occursin id = function
  | Tvar link -> (
      match link with
      | { contents = { link = Unbound { id = id'; level = _ }; _ } } -> id = id'
      | { contents = { link = Linkto ty; _ } } -> occursin id ty)
  | Tlist ty -> occursin id ty
  | Tref ty -> occursin id ty
  | Tarrow (arg, ret) -> occursin id arg || occursin id ret
  | Ttuple tyl | Tconstr (_, tyl) -> List.exists (occursin id) tyl
  | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
      List.exists (occursin id) (List.map snd fields)
  | _ -> false

let rec adjustlevel level = function
  | Tvar link -> (
      match link with
      | { contents = { link = Unbound { id = id'; level = level' }; abstract } }
        ->
          if level < level' then
            link := { link = Unbound { id = id'; level }; abstract }
      | { contents = { link = Linkto ty; _ } } -> adjustlevel level ty)
  | Tlist ty -> adjustlevel level ty
  | Tref ty -> adjustlevel level ty
  | Tarrow (arg, ret) ->
      adjustlevel level arg;
      adjustlevel level ret
  | Ttuple tyl | Tconstr (_, tyl) -> List.iter (adjustlevel level) tyl
  | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
      List.iter (adjustlevel level) (List.map snd fields)
  | _ -> ()

let rec instantiate_atomic_sub id_var_hash = function
  | n, AtomSig_value ty ->
      (n, AtomSig_value (instantiate_mod_item id_var_hash generic ty))
  | n, AtomSig_type decl ->
      let decl =
        match decl with
        | { ast = TDrecord (n, tyl, fields); pos } -> (
            match
              instantiate_mod_item id_var_hash generic
                (Trecord (n, tyl, fields))
            with
            | Trecord (n, tyl, fields) ->
                { ast = TDrecord (n, tyl, fields); pos }
            | _ -> failwith "instantiate_sema_sig")
        | { ast = TDvariant (n, tyl, fields); pos } -> (
            match
              instantiate_mod_item id_var_hash generic
                (Tvariant (n, tyl, fields))
            with
            | Tvariant (n, tyl, fields) ->
                { ast = TDvariant (n, tyl, fields); pos }
            | _ -> failwith "instantiate_sema_sig")
        | { ast = TDabbrev (n, tyl, ty); pos } -> (
            match
              instantiate_mod_item id_var_hash generic
                (Trecord (n, tyl, [ ("temp", ty) ]))
            with
            | Trecord (n, tyl, [ ("temp", ty) ]) ->
                { ast = TDabbrev (n, tyl, ty); pos }
            | _ -> failwith "instantiate_sema_sig")
        | { ast = TDabs (n, tyl, ty); pos } ->
            {
              ast = TDabs (n, tyl, instantiate_sub id_var_hash generic ty false);
              pos;
            }
      in
      (n, AtomSig_type decl)
  | n, AtomSig_module compound_sig ->
      (n, AtomSig_module (instantiate_compound_sub id_var_hash compound_sig))

and instantiate_compound_sub id_var_hash = function
  | ComSig_struct l ->
      ComSig_struct (List.map (instantiate_atomic_sub id_var_hash) l)
  | ComSig_fun ((name, atomic_sig), compound_sig) ->
      ComSig_fun
        ( instantiate_atomic_sub id_var_hash (name, atomic_sig),
          instantiate_compound_sub id_var_hash compound_sig )

let instantiate_atomic atomic_sig =
  instantiate_atomic_sub (Hashtbl.create 10) atomic_sig

and instantiate_compound compound_sig =
  instantiate_compound_sub (Hashtbl.create 10) compound_sig

let rec access_atomic path sema_sig =
  match (path, sema_sig) with
  | s :: path, (n, AtomSig_module compound_sig) when s = n ->
      access_compound path compound_sig
  | [], (_, AtomSig_module compound_sig) -> compound_sig
  | _ -> failwith ("invalid path" ^ show_path path)

and access_compound path sema_sig =
  match (path, sema_sig) with
  | s :: path, ComSig_struct l when List.mem_assoc s l ->
      access_atomic (s :: path) (s, List.assoc s l)
  | [], sema_sig -> sema_sig
  | _ -> failwith ("invalid path" ^ show_path path)

let rec unify env ty1 ty2 =
  match (ty1, ty2) with
  | Tvar link1, Tvar link2 when link1 = link2 -> ()
  | Tpath (_, path, Tconstr (name, [])), ty2
  | ty2, Tpath (_, path, Tconstr (name, [])) -> (
      let compound_sig = access_compound path (ComSig_struct env) in
      let _, ty1 =
        type_of_decl' (Option.get (find_type name (get_struct compound_sig)))
      in
      (*print_endline (show_ty ty1);*)
      try unify env ty1 ty2
      with _ ->
        Printf.printf "Cannot unify types between %s and %s" (pp_ty ty1)
          (pp_ty ty2);
        failwith
          (Printf.sprintf "Cannot unify types between %s and %s" (pp_ty ty1)
             (pp_ty ty2)))
  | Tvar { contents = { link = Linkto t1; abstract = false } }, t2
  | t1, Tvar { contents = { link = Linkto t2; abstract = false } } ->
      unify env t1 t2
  | ( Tvar
        ({ contents = { link = Unbound { id; level }; abstract = false } } as
         link),
      ty )
  | ( ty,
      Tvar
        ({ contents = { link = Unbound { id; level }; abstract = false } } as
         link) ) ->
      if occursin id ty then
        failwith
          (Printf.sprintf "unify error due to ocurr check %s %s" (pp_ty ty1)
             (pp_ty ty2));
      adjustlevel level ty;
      link := { link = Linkto ty; abstract = false }
  | Tlist t1, Tlist t2 -> unify env t1 t2
  | Tref t1, Tref t2 -> unify env t1 t2
  | Tformat (arg1, ret1), Tformat (arg2, ret2) ->
      unify env arg1 arg2;
      unify env ret1 ret2
  | Tarrow (arg1, ret1), Tarrow (arg2, ret2) ->
      unify env arg1 arg2;
      unify env ret1 ret2
  | Ttuple tyl1, Ttuple tyl2 -> unify_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Trecord (name2, tyl2, _) when name1 = name2 ->
      unify_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tvariant (name2, tyl2, _) when name1 = name2 ->
      unify_list env tyl1 tyl2
  | Trecord (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list env tyl1 tyl2
  | Tvariant (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list env tyl1 tyl2
  | Trecord (name1, _, fields1), Trecord (name2, _, fields2) when name1 = name2
    ->
      unify_list env (List.map snd fields1) (List.map snd fields2)
  | Tvariant (name1, _, fields1), Tvariant (name2, _, fields2)
    when name1 = name2 ->
      unify_list env (List.map snd fields1) (List.map snd fields2)
  | ty1, ty2 when ty1 = ty2 -> ()
  | _ ->
      Printf.printf "Cannot unify types between %s and %s" (show_ty ty1)
        (show_ty ty2);
      failwith
        (Printf.sprintf "Cannot unify types between %s and %s" (pp_ty ty1)
           (pp_ty ty2))

and unify_list env tyl1 tyl2 = List.iter2 (unify env) tyl1 tyl2

let rec expand_abbrev env ty =
  match ty with
  | Tconstr (name, params) ->
      let tyl, ty = type_of_decl env name in
      if List.length params = List.length tyl then (
        unify_list env params tyl;
        ty)
      else
        failwith
          ("the number of parameters of type constructor doesn't match:" ^ name)
  | Tlist t -> Tlist (expand_abbrev env t)
  | Tref t -> Tref (expand_abbrev env t)
  | Tarrow (arg, ret) -> Tarrow (expand_abbrev env arg, expand_abbrev env ret)
  | Ttuple tyl -> Ttuple (List.map (fun t -> expand_abbrev env t) tyl)
  | Trecord (name, tyl, fields) ->
      Trecord
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev env t)) fields)
  | Tvariant (name, tyl, fields) ->
      Tvariant
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev env t)) fields)
  | _ -> ty

let fields_of_type ty =
  let fields =
    match ty with
    | Trecord (_, _, fields) -> fields
    | Tvariant (_, _, fields) -> fields
    | _ -> failwith "not a record or variant type"
  in
  fields

let label_belong_to env label pos =
  let rec aux = function
    | (_, AtomSig_type decl) :: rest -> (
        match decl with
        | { ast = TDrecord (name, _, fields); _ }
          when List.mem_assoc label fields ->
            name
        | _ -> aux rest)
    | _ :: rest -> aux rest
    | [] ->
        failwith
          (Printf.sprintf "%s invalid label %s" (print_errloc !file pos) label)
  in
  aux env

let tag_belong_to env label pos =
  let rec aux = function
    | (_, AtomSig_type decl) :: rest -> (
        match decl with
        | { ast = TDvariant (name, _, fields); _ }
          when List.mem_assoc label fields ->
            name
        | _ -> aux rest)
    | _ :: rest -> aux rest
    | [] ->
        failwith
          (Printf.sprintf "%s invalid label %s" (print_errloc !file pos) label)
  in
  aux env

let rec is_simple expr =
  match !(expr.ast) with
  | Evar _ -> true
  | Econstant _ -> true
  | Eprim _ -> true
  | Etuple l -> List.for_all (fun x -> is_simple x) l
  | Enil -> true
  | Econs (car, cdr) -> is_simple car && is_simple cdr
  | Elist _ -> true
  | Eref _ -> false
  | Ederef _ -> false
  | Eassign (_, _) -> false
  | Eloc _ -> true
  | Eunit -> true
  | Etag -> true
  | Econstruct (_, expr) -> is_simple expr
  | Eapply _ -> false
  | Elet (l, body) ->
      List.for_all (fun x -> is_simple x) (List.map snd l) && is_simple body
  | Eletrec (l, body) ->
      List.for_all (fun x -> is_simple x) (List.map snd l) && is_simple body
  | Efix _ -> true
  | Efunction _ -> true
  | Esequence (expr1, expr2) -> is_simple expr1 && is_simple expr2
  | Econdition (_, ifso, ifelse) -> is_simple ifso && is_simple ifelse
  | Econstraint (expr, _) -> is_simple expr
  | Erecord l -> List.for_all (fun x -> is_simple x) (List.map snd l)
  | Erecord_access (expr, _) -> is_simple expr
  | Ewhen (expr, body) -> is_simple expr && is_simple body
  | EBlock1 expr -> is_simple expr
  | Epath _ -> true

let rec curry = function
  | {
      ast =
        { contents = Efunction [ ({ ast = { contents = Pparams [] }; _ }, e) ] };
      _;
    } ->
      e
  | {
      ast =
        {
          contents =
            Efunction [ ({ ast = { contents = Pparams (p :: pl) }; pos }, e) ];
        };
      _;
    } ->
      {
        ast =
          ref
            (Efunction
               [
                 ( p,
                   curry
                     {
                       ast =
                         ref
                           (Efunction
                              [ ({ ast = { contents = Pparams pl }; pos }, e) ]);
                       pos;
                     } );
               ]);
        pos;
      }
  | e -> e

let type_format fmt expr =
  let args = ref 0 in
  let len = String.length fmt in
  let ty_result = new_type_var notgeneric false in
  let rec skip_args j =
    if j >= len then j
    else
      match fmt.[j] with
      | '0' .. '9' | ' ' | '.' | '-' -> skip_args (j + 1)
      | _ -> j
  in
  let rec scan_format i =
    if i >= len then ty_result
    else
      match fmt.[i] with
      | '%' -> (
          let j = skip_args (i + 1) in
          match fmt.[j] with
          | '%' -> scan_format (j + 1)
          | 's' ->
              incr args;
              Tarrow (Tstring, scan_format (j + 1))
          | 'c' ->
              incr args;
              Tarrow (Tchar, scan_format (j + 1))
          | 'd' | 'o' | 'x' | 'X' | 'u' ->
              incr args;
              Tarrow (Tint, scan_format (j + 1))
          | 'f' | 'e' | 'E' | 'g' | 'G' ->
              incr args;
              Tarrow (Tfloat, scan_format (j + 1))
          | 'b' -> Tarrow (Tbool, scan_format (j + 1))
          | _ ->
              failwith
                (Printf.sprintf "%s bad format letter after %%"
                   (print_errloc !file expr.pos)))
      | _ -> scan_format (i + 1)
  in
  (!args, Tformat (scan_format 0, ty_result))

let type_prim level = function
  | Peq | Pnq | Plt | Pgt | Ple | Pge | Peqimm | Pnqimm ->
      let tvar = new_type_var level false in
      Tarrow (tvar, Tarrow (tvar, Tbool))
  | Pnot -> Tarrow (Tbool, Tbool)
  | Pand | Por -> Tarrow (Tbool, Tarrow (Tbool, Tbool))
  | Pnegint -> Tarrow (Tint, Tint)
  | Paddint | Psubint | Pmulint | Pdivint | Pmod ->
      Tarrow (Tint, Tarrow (Tint, Tint))
  | Plnot -> Tarrow (Tint, Tint)
  | Pland | Plor | Plxor | Plsl | Plsr | Pasr ->
      Tarrow (Tint, Tarrow (Tint, Tint))
  | Pnegfloat -> Tarrow (Tfloat, Tfloat)
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat | Ppower ->
      Tarrow (Tfloat, Tarrow (Tfloat, Tfloat))
  | Pconcatstring -> Tarrow (Tstring, Tarrow (Tstring, Tstring))
  | Pintoffloat -> Tarrow (Tfloat, Tint)
  | Pfloatofint -> Tarrow (Tint, Tfloat)
  | Pintofchar -> Tarrow (Tchar, Tint)
  | Pcharofint -> Tarrow (Tint, Tchar)
  | Pstringofbool -> Tarrow (Tbool, Tstring)
  | Pboolofstring -> Tarrow (Tstring, Tbool)
  | Pstringofint -> Tarrow (Tint, Tstring)
  | Pintofstring -> Tarrow (Tstring, Tint)
  | Pstringoffloat -> Tarrow (Tfloat, Tstring)
  | Pfloatofstring -> Tarrow (Tstring, Tfloat)
  | Pconcat ->
      let tvar = new_type_var level false in
      Tarrow (Tlist tvar, Tarrow (Tlist tvar, Tlist tvar))
  | Pfailwith ->
      let tvar = new_type_var level false in
      Tarrow (Tstring, tvar)
  | Pprintf ->
      let remain_ty = new_type_var notgeneric false in
      Tarrow (Tformat (remain_ty, Tunit), remain_ty)
  | Psprintf ->
      let remain_ty = new_type_var notgeneric false in
      Tarrow (Tformat (remain_ty, Tstring), remain_ty)

let unify_pat sema_sig pat actual_ty expected_ty =
  try unify sema_sig actual_ty expected_ty
  with _ ->
    failwith
      (Printf.sprintf
         "%s This pattern matches values of type %s,\n\
          but should match values of type %s.\n"
         (print_errloc !file pat.pos)
         (pp_ty actual_ty) (pp_ty expected_ty))

let rec type_pat env add_env level pat ty =
  match !(pat.ast) with
  | Pwild -> ("_", AtomSig_value ty) :: add_env
  | Pvar s -> (
      match find_val s add_env with
      | None -> (s, AtomSig_value ty) :: add_env
      | Some _ ->
          failwith
            (Printf.sprintf "%s a variable found more than twice: %s"
               (print_errloc !file pat.pos)
               s))
  | Pparams _ -> failwith "type_pat"
  | Palias (pat, s) -> (
      match find_val s add_env with
      | None -> type_pat env ((s, AtomSig_value ty) :: add_env) level pat ty
      | Some _ ->
          failwith
            (Printf.sprintf "%s a variable found more than twice: %s"
               (print_errloc !file pat.pos)
               s))
  | Pconstant cst ->
      let cst_ty =
        match cst with
        | Cint _ -> Tint
        | Cbool _ -> Tbool
        | Cfloat _ -> Tfloat
        | Cstring _ -> Tstring
        | Cchar _ -> Tchar
      in
      unify_pat env pat ty cst_ty;
      env
  | Ptuple patl ->
      let tyl =
        List.init (List.length patl) (fun _ -> new_type_var level false)
      in
      unify env (Ttuple tyl) ty;
      List.fold_left2
        (fun add_env -> type_pat env add_env level)
        add_env patl tyl
  | Pnil ->
      unify_pat env pat ty (Tlist (new_type_var level false));
      env
  | Pcons (car, cdr) ->
      let ty1 = new_type_var level false in
      let ty2 = new_type_var level false in
      let add_env = type_pat env add_env level car ty1 in
      let add_env = type_pat env add_env level cdr ty2 in
      unify_pat env pat ty2 (Tlist ty1);
      unify_pat env pat ty ty2;
      add_env
  | Pref expr ->
      let ty1 = new_type_var level false in
      let add_env = type_pat env add_env level expr ty1 in
      unify_pat env pat ty (Tref ty1);
      add_env
  | Punit ->
      unify_pat env pat ty Tunit;
      add_env
  | Ptag ->
      unify env ty Ttag;
      add_env
  | Pconstruct (name, pat) -> type_variant_pat env add_env level (name, pat) ty
  | Pconstraint (pat, expected) ->
      let add_env = type_pat env add_env level pat ty in
      unify_pat env pat ty (instantiate level expected);
      add_env
  | Precord fields -> type_record_pat env add_env level fields ty pat

and type_record_pat env add_env level fields ty pat =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to env first_label pat.pos in
  let record_ty = instantiate level (snd (type_of_decl env record_name)) in
  let fields2 = fields_of_type record_ty in
  unify env record_ty ty;
  try
    List.fold_left
      (fun add_env (name, ty) ->
        (type_pat env add_env level)
          (try List.assoc name fields
           with Not_found ->
             failwith
               (Printf.sprintf "%s not found: %s"
                  (print_errloc !file pat.pos)
                  name))
          ty)
      add_env fields2
  with _ ->
    failwith
      (Printf.sprintf "%s invalid record pattern" (print_errloc !file pat.pos))

and type_variant_pat env add_env level (tag_name, pat) ty =
  let variant_name = tag_belong_to env tag_name pat.pos in
  let _, variant_ty = type_of_decl env variant_name in
  unify env ty (instantiate level variant_ty);
  let ty =
    try List.assoc tag_name (fields_of_type variant_ty)
    with Not_found ->
      failwith
        (Printf.sprintf "%s not found: %s"
           (print_errloc !file pat.pos)
           tag_name)
  in
  type_pat env add_env level pat ty

and unify_expr env expr actual_ty expected_ty =
  try unify env actual_ty expected_ty
  with _ ->
    failwith
      (Printf.sprintf
         "%s This expression has type %s,\nbut is expected type %s.\n"
         (print_errloc !file expr.pos)
         (pp_ty actual_ty) (pp_ty expected_ty))

and function_error env level expr ty =
  failwith
    (try
       let param_ty = new_type_var level false in
       let ret_ty = new_type_var level false in
       unify env ty (Tarrow (param_ty, ret_ty));
       Printf.sprintf "%s This function is applied to too many arguments.\n"
         (print_errloc !file expr.pos)
     with _ ->
       Printf.sprintf
         "%s This expression is not a function, it cannot be applied.\n"
         (print_errloc !file expr.pos))

and type_expect env level expr expected_ty =
  match !(expr.ast) with
  | _ -> unify_expr env expr (type_expr env level expr) expected_ty

and type_expr env level expr =
  match !(expr.ast) with
  | Evar s ->
      let ty =
        try instantiate level (Option.get (find_val s env))
        with _ -> (
          try type_prim level (List.assoc s prim_list)
          with _ ->
            failwith
              (Printf.sprintf "%s not found: %s"
                 (print_errloc !file expr.pos)
                 s))
      in
      ty
  | Econstant cst ->
      let ty =
        match cst with
        | Cint _ -> Tint
        | Cbool _ -> Tbool
        | Cfloat _ -> Tfloat
        | Cstring _ -> Tstring
        | Cchar _ -> Tchar
      in
      ty
  | Eprim prim ->
      let ty = type_prim level prim in
      ty
  | Etuple l ->
      let ty = Ttuple (List.map (fun t -> type_expr env level t) l) in
      ty
  | Enil ->
      let ty = Tlist (new_type_var level false) in
      ty
  | Econs (car, cdr) ->
      let ty = type_expr env level cdr in
      let expected_ty = new_type_var level false in
      unify env (Tlist expected_ty) ty;
      type_expect env level car expected_ty;
      ty
  | Elist l ->
      let ty = new_type_var level false in
      List.iter (fun expr -> unify env ty (type_expr env level expr)) l;
      let ty = Tlist ty in
      ty
  | Eref e ->
      let ty = type_expr env level e in
      let ty = Tref ty in
      ty
  | Ederef e ->
      let ty = new_type_var level false in
      type_expect env level e (Tref ty);
      ty
  | Eassign (lhs, rhs) ->
      let ty = type_expr env level rhs in
      type_expect env level lhs (Tref ty);
      Tunit
  | Eloc _ ->
      let ty = new_type_var level false in
      let ty = Tref ty in
      ty
  | Eunit -> Tunit
  | Etag -> Ttag
  | Econstruct (tag_name, e) ->
      let ty = type_variant_expr env level (tag_name, e) in
      ty
  | Eapply (({ ast = { contents = Evar s }; _ } as p), args)
    when List.mem_assoc s prim_list ->
      let prim =
        try List.assoc s prim_list
        with Not_found ->
          failwith
            (Printf.sprintf "%s not found: %s" (print_errloc !file expr.pos) s)
      in
      let fct_ty = type_expr env level p in
      let args =
        if is_unary prim then (
          p.ast :=
            Efunction
              [
                ( { ast = ref (Pvar "0"); pos = expr.pos },
                  {
                    ast =
                      ref
                        (Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             [ { ast = ref (Evar "0"); pos = expr.pos } ] ));
                    pos = expr.pos;
                  } );
              ];
          List.map (type_expr env level) args)
        else if is_binary prim then (
          p.ast :=
            Efunction
              [
                ( {
                    ast =
                      ref
                        (Pparams
                           [
                             { ast = ref (Pvar "0"); pos = expr.pos };
                             { ast = ref (Pvar "1"); pos = expr.pos };
                           ]);
                    pos = expr.pos;
                  },
                  {
                    ast =
                      ref
                        (Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             [
                               { ast = ref (Evar "0"); pos = expr.pos };
                               { ast = ref (Evar "1"); pos = expr.pos };
                             ] ));
                    pos = expr.pos;
                  } );
              ];
          p.ast := !((curry p).ast);
          List.map (type_expr env level) args)
        else
          let fmt = List.hd args in
          let len, fmt_ty =
            match !(fmt.ast) with
            | Econstant (Cstring s) -> type_format s fmt
            | _ ->
                failwith
                  (Printf.sprintf "%s not a string"
                     (print_errloc !file expr.pos))
          in
          p.ast :=
            Efunction
              (( {
                   ast =
                     ref
                       (Pparams
                          (List.init (len + 1) (fun i ->
                               {
                                 ast = ref (Pvar (string_of_int i));
                                 pos = expr.pos;
                               })));
                   pos = expr.pos;
                 },
                 {
                   ast =
                     {
                       contents =
                         Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             List.init (len + 1) (fun i ->
                                 {
                                   ast = ref (Evar (string_of_int i));
                                   pos = expr.pos;
                                 }) );
                     };
                   pos = expr.pos;
                 } )
              :: []);
          p.ast := !((curry p).ast);
          fmt_ty :: List.map (type_expr env level) (List.tl args)
      in
      let ty =
        List.fold_left
          (fun fct_ty_ arg_ty ->
            let param_ty = new_type_var level false in
            let ret_ty = new_type_var level false in
            (try unify env fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error env level p fct_ty);
            unify env arg_ty param_ty;
            ret_ty)
          fct_ty args
      in
      ty
  | Eapply (({ ast = { contents = Eprim prim }; _ } as p), args) ->
      let fct_ty = type_expr env level p in
      let args =
        if is_unary prim then (
          p.ast :=
            Efunction
              [
                ( { ast = ref (Pvar "0"); pos = expr.pos },
                  {
                    ast =
                      ref
                        (Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             [ { ast = ref (Evar "0"); pos = expr.pos } ] ));
                    pos = expr.pos;
                  } );
              ];
          List.map (type_expr env level) args)
        else if is_binary prim then (
          p.ast :=
            Efunction
              [
                ( {
                    ast =
                      ref
                        (Pparams
                           [
                             { ast = ref (Pvar "0"); pos = expr.pos };
                             { ast = ref (Pvar "1"); pos = expr.pos };
                           ]);
                    pos = expr.pos;
                  },
                  {
                    ast =
                      ref
                        (Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             [
                               { ast = ref (Evar "0"); pos = expr.pos };
                               { ast = ref (Evar "1"); pos = expr.pos };
                             ] ));
                    pos = expr.pos;
                  } );
              ];
          p.ast := !((curry p).ast);
          List.map (type_expr env level) args)
        else
          let fmt = List.hd args in
          let len, fmt_ty =
            match !(fmt.ast) with
            | Econstant (Cstring s) -> type_format s fmt
            | _ ->
                failwith
                  (Printf.sprintf "%s not a string"
                     (print_errloc !file expr.pos))
          in
          p.ast :=
            Efunction
              (( {
                   ast =
                     ref
                       (Pparams
                          (List.init (len + 1) (fun i ->
                               {
                                 ast = ref (Pvar (string_of_int i));
                                 pos = expr.pos;
                               })));
                   pos = expr.pos;
                 },
                 {
                   ast =
                     {
                       contents =
                         Eapply
                           ( { ast = ref !(p.ast); pos = expr.pos },
                             List.init (len + 1) (fun i ->
                                 {
                                   ast = ref (Evar (string_of_int i));
                                   pos = expr.pos;
                                 }) );
                     };
                   pos = expr.pos;
                 } )
              :: []);
          p.ast := !((curry p).ast);
          fmt_ty :: List.map (type_expr env level) (List.tl args)
      in

      let ty =
        List.fold_left
          (fun fct_ty_ arg_ty ->
            let param_ty = new_type_var level false in
            let ret_ty = new_type_var level false in
            (try unify env fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error env level p fct_ty);
            unify env arg_ty param_ty;
            ret_ty)
          fct_ty args
      in
      ty
  | Eapply (fct, args) ->
      let fct_ty = type_expr env level fct in
      let ty =
        List.fold_left
          (fun fct_ty_ arg_ty ->
            let param_ty = new_type_var level false in
            let ret_ty = new_type_var level false in
            (try unify env fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error env level fct fct_ty);
            unify env arg_ty param_ty;
            ret_ty)
          fct_ty
          (List.map (type_expr env level) args)
      in
      ty
  | Elet (pat_expr, body) ->
      let patl = List.map (fun (pat, _) -> pat) pat_expr in
      let tyl = List.map (fun (_, _) -> new_type_var level false) pat_expr in
      let add_env =
        List.fold_left2 (fun add_env -> type_pat env add_env level) [] patl tyl
      in
      List.iter2
        (fun ty (_, expr) ->
          type_expect env (level + 1) expr ty;
          if is_simple expr then generalize (level + 1) ty)
        tyl pat_expr;
      let ty = type_expr (add_env @ env) level body in
      ty
  | Eletrec (pat_expr, body) ->
      let patl = List.map (fun (pat, _) -> pat) pat_expr in
      let tyl = List.map (fun (_, _) -> new_type_var level false) pat_expr in
      let add_env =
        List.fold_left2 (fun add_env -> type_pat env add_env level) [] patl tyl
      in
      List.iter2
        (fun ty (_, expr) ->
          type_expect (add_env @ env) (level + 1) expr ty;
          if is_simple expr then generalize (level + 1) ty)
        tyl pat_expr;
      let ty = type_expr (add_env @ env) level body in
      ty
  | Efix (e, l) ->
      let ty = new_type_var level false in
      type_expect env level e ty;
      List.iter (fun (_, e) -> type_expect env level e ty) l;
      ty
  | Efunction l -> (
      match l with
      | [] ->
          failwith
            (Printf.sprintf "%s empty function" (print_errloc !file expr.pos))
      | [ ({ ast = { contents = Pparams patl }; _ }, e) ] ->
          let tyl = List.map (fun _ -> new_type_var level false) patl in
          let add_env =
            List.fold_left2
              (fun add_env -> type_pat env add_env level)
              [] patl tyl
          in
          let ret_ty = type_expr (add_env @ env) level e in
          let ty =
            List.fold_left
              (fun ret_ty arg_ty -> Tarrow (arg_ty, ret_ty))
              ret_ty (List.rev tyl)
          in
          expr.ast := !((curry expr).ast);
          ty
      | pat_expr ->
          let arg_ty = new_type_var level false in
          let ret_ty = new_type_var level false in
          List.iter
            (fun (pat, e) ->
              let add_env = type_pat env [] level pat arg_ty in
              let ty = type_expr (add_env @ env) level e in
              unify env ty ret_ty)
            pat_expr;
          let ty = Tarrow (arg_ty, ret_ty) in
          ty)
  | Esequence (expr1, expr2) ->
      type_expect env level expr1 Tunit;
      type_expr env level expr2
  | Econdition (flag, ifso, ifelse) ->
      type_expect env level flag Tbool;
      let ty = type_expr env level ifso in
      type_expect env level ifelse ty;
      ty
  | Econstraint (e, expected) ->
      let ty = instantiate level expected in
      type_expect env level e ty;
      ty
  | Erecord [] ->
      failwith
        (Printf.sprintf "%s empty record fields" (print_errloc !file expr.pos))
  | Erecord l ->
      let ty = type_record_expr env level l expr in
      ty
  | Erecord_access (e, label) ->
      let record_name = label_belong_to env label expr.pos in
      let record_ty = instantiate level (snd (type_of_decl env record_name)) in
      type_expect env level e (instantiate level record_ty);
      let ty =
        try List.assoc label (fields_of_type record_ty)
        with Not_found ->
          failwith
            (Printf.sprintf "%s label not found %s" label
               (print_errloc !file expr.pos))
      in
      ty
  | Ewhen (e, body) ->
      type_expect env level e Tbool;
      let ty = type_expr env level body in
      ty
  | EBlock1 expr -> type_expr env level expr
  | Epath (path, name) -> (
      let l = access_compound path (ComSig_struct env) in
      match find_val name (get_struct l) with
      | Some ty -> ty
      | None -> failwith ("invalid path" ^ name))

and type_record_expr env level fields expr =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to env first_label expr.pos in
  let record_ty = instantiate level (snd (type_of_decl env record_name)) in
  let fields1 = List.map (fun (n, e) -> (n, type_expr env level e)) fields in
  let fields2 = fields_of_type record_ty in
  try
    List.iter
      (fun (name, ty) ->
        unify env
          (try List.assoc name fields1
           with Not_found ->
             failwith
               (Printf.sprintf " %s invalid label: %s"
                  (print_errloc !file expr.pos)
                  name))
          ty)
      fields2;
    record_ty
  with _ ->
    failwith
      (Printf.sprintf " %s invalid record expression"
         (print_errloc !file expr.pos))

and type_variant_expr env level (tag_name, expr) =
  let variant_name = tag_belong_to env tag_name expr.pos in
  let variant_ty = instantiate level (snd (type_of_decl env variant_name)) in
  let ty =
    try List.assoc tag_name (fields_of_type variant_ty)
    with Not_found ->
      failwith
        (Printf.sprintf " %s invalid tag: %s" tag_name
           (print_errloc !file expr.pos))
  in
  let ty1 = type_expr env level expr in
  unify env ty ty1;
  variant_ty

let type_let env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1) false) pat_expr in
  let add_env =
    List.fold_left2
      (fun add_env -> type_pat env add_env (level + 1))
      [] patl tyl
  in
  List.iter2
    (fun ty (_, expr) ->
      type_expect env (level + 1) expr ty;
      if is_simple expr then generalize level ty)
    tyl pat_expr;
  add_env

let type_letrec env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1) false) pat_expr in
  let add_env =
    List.fold_left2
      (fun add_env -> type_pat env add_env (level + 1))
      [] patl tyl
  in
  List.iter2
    (fun ty (_, expr) ->
      type_expect (add_env @ env) (level + 1) expr ty;
      if is_simple expr then generalize level ty)
    tyl pat_expr;
  add_env

let rec check_valid_ty tyl = function
  | Tvar { contents = { link = Unbound { id; level = _ }; _ } } ->
      List.exists (occursin id) tyl
  | Tvar { contents = { link = Linkto t; _ } } -> check_valid_ty tyl t
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
    | (_, AtomSig_type { ast = TDrecord (_, tyl, fields); _ }) :: rest ->
        if List.for_all (fun (_, t) -> check_valid_ty tyl t) fields then
          aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | (_, AtomSig_type { ast = TDvariant (_, tyl, fields); _ }) :: rest ->
        if List.for_all (fun (_, t) -> check_valid_ty tyl t) fields then
          aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | (_, AtomSig_type { ast = TDabbrev (_, tyl, ty); _ }) :: rest ->
        if check_valid_ty tyl ty then aux rest
        else
          failwith
            "a type variable doesn't appear in the type parameter list is found"
    | _ :: rest -> aux rest
    | _ -> ()
  in
  aux decl

type status = Checking | Checked

let name_is_checking name seen =
  if List.mem_assoc name seen then !(List.assoc name seen) = Checking else false

let name_is_checked name seen =
  if List.mem_assoc name seen then !(List.assoc name seen) = Checked else false

let rec is_abbrev name = function
  | (_, AtomSig_type { ast = TDabbrev (name', _, _); _ }) :: _ when name = name'
    ->
      true
  | _ :: rest -> is_abbrev name rest
  | [] -> false

let rec abbrev_found_in_ty decl seen = function
  | Tlist t -> abbrev_found_in_ty decl seen (expand_abbrev decl t)
  | Tref t -> abbrev_found_in_ty decl seen (expand_abbrev decl t)
  | Tarrow (arg, ret) ->
      abbrev_found_in_ty decl seen (expand_abbrev decl arg);
      abbrev_found_in_ty decl seen (expand_abbrev decl ret)
  | Ttuple tyl ->
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev decl t))
        tyl
  | Tconstr (name, _) when name_is_checking name seen ->
      failwith (Printf.sprintf "recursive type abbreviation %s" name)
  | Tconstr (name, tyl) when name_is_checked name seen ->
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev decl t))
        tyl
  | Tconstr (name, tyl) when is_abbrev name decl ->
      abbrev_found_in_decl name seen decl;
      List.iter
        (fun t -> abbrev_found_in_ty decl seen (expand_abbrev decl t))
        tyl
  | _ -> ()

and abbrev_found_in_decl name seen decl =
  let rec aux = function
    | (_, AtomSig_type { ast = TDabbrev (n, _, ty); _ }) :: _ when n = name ->
        let pair = (name, ref Checking) in
        abbrev_found_in_ty decl (pair :: seen) ty;
        snd pair := Checked
    | _ :: rest -> aux rest
    | [] -> failwith ("name not found abbrev_found_in_decl:" ^ name)
  in
  aux decl

let check_recursive_abbrev decl =
  let rec aux = function
    | (_, AtomSig_type { ast = TDabbrev (name, _, _); _ }) :: rest ->
        abbrev_found_in_decl name [] decl;
        aux rest
    | _ :: rest -> aux rest
    | [] -> ()
  in
  aux decl

let rec is_def name = function
  | (_, AtomSig_type { ast = TDrecord (name', _, _); _ }) :: _ when name = name'
    ->
      true
  | (_, AtomSig_type { ast = TDvariant (name', _, _); _ }) :: _
    when name = name' ->
      true
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
  | Tconstr (_, _) as t -> def_found_in_ty decl seen (expand_abbrev decl t)
  | _ -> ()

and def_found_in_decl name seen decl =
  let rec aux = function
    | (_, AtomSig_type { ast = TDrecord (n, _, fields); _ }) :: _ when n = name
      ->
        let pair = (name, ref Checking) in
        List.iter
          (fun t -> def_found_in_ty decl (pair :: seen) t)
          (List.map snd fields);
        snd pair := Checked
    | (_, AtomSig_type { ast = TDvariant (n, _, fields); _ }) :: _ when n = name
      ->
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
    | (_, AtomSig_type { ast = TDrecord (name, _, _); _ }) :: rest ->
        def_found_in_decl name [] decl;
        aux rest
    | (_, AtomSig_type { ast = TDvariant (name, _, _); _ }) :: rest ->
        def_found_in_decl name [] decl;
        aux rest
    | _ :: rest -> aux rest
    | [] -> ()
  in
  aux decl

(* instantiate ty1 so that it is equal to ty2 *)
let rec filter env ty1 ty2 =
  match (ty1, ty2) with
  | Tvar link1, Tvar link2 when link1 = link2 -> ()
  | Tpath (_, path, Tconstr (name, [])), ty2
  | ty2, Tpath (_, path, Tconstr (name, [])) -> (
      let compound_sig = access_compound path (ComSig_struct env) in
      let _, ty1 =
        type_of_decl' (Option.get (find_type name (get_struct compound_sig)))
      in
      (*print_endline (show_ty ty1);*)
      try filter env ty1 ty2
      with _ ->
        Printf.printf "Cannot filter types between %s and %s" (pp_ty ty1)
          (pp_ty ty2);
        failwith
          (Printf.sprintf "Cannot filter types between %s and %s" (pp_ty ty1)
             (pp_ty ty2)))
  | Tvar { contents = { link = Linkto t1; abstract = false } }, t2
  | t1, Tvar { contents = { link = Linkto t2; abstract = false } } ->
      filter env t1 t2
  | ( Tvar
        ({ contents = { link = Unbound { id; level }; abstract = false } } as
         link),
      ty )
  | ( ty,
      Tvar
        ({ contents = { link = Unbound { id; level }; abstract = false } } as
         link) ) ->
      if occursin id ty then
        failwith
          (Printf.sprintf "filter error due to ocurr check %s %s" (pp_ty ty1)
             (pp_ty ty2));
      adjustlevel level ty;
      link := { link = Linkto ty; abstract = false };
      ()
  | Tlist t1, Tlist t2 -> filter env t1 t2
  | Tref t1, Tref t2 -> filter env t1 t2
  | Tformat (arg1, ret1), Tformat (arg2, ret2) ->
      filter env arg1 arg2;
      filter env ret1 ret2
  | Tarrow (arg1, ret1), Tarrow (arg2, ret2) ->
      filter env arg1 arg2;
      filter env ret1 ret2
  | Ttuple tyl1, Ttuple tyl2 -> filter_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tconstr (name2, tyl2) when name1 = name2 ->
      filter_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Trecord (name2, tyl2, _) when name1 = name2 ->
      filter_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tvariant (name2, tyl2, _) when name1 = name2 ->
      filter_list env tyl1 tyl2
  | Trecord (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      filter_list env tyl1 tyl2
  | Tvariant (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      filter_list env tyl1 tyl2
  | Trecord (name1, _, fields1), Trecord (name2, _, fields2) when name1 = name2
    ->
      filter_list env (List.map snd fields1) (List.map snd fields2)
  | Tvariant (name1, _, fields1), Tvariant (name2, _, fields2)
    when name1 = name2 ->
      filter_list env (List.map snd fields1) (List.map snd fields2)
  | ty1, ty2 when ty1 = ty2 -> ()
  | _ ->
      (*Printf.printf "Cannot filter types between %s and %s" (show_ty ty1)
        (show_ty ty2);*)
      failwith
        (Printf.sprintf "Cannot filter types between %s and %s" (pp_ty ty1)
           (pp_ty ty2))

and filter_list env tyl1 tyl2 = List.iter2 (filter env) tyl1 tyl2

and type_match env ty1 ty2 =
  match (ty1, ty2) with
  | ( ty,
      Tvar
        ({ contents = { link = Unbound { id; level }; abstract = true } } as
         link) ) ->
      if occursin id ty then
        failwith
          (Printf.sprintf "filter error due to ocurr check %s %s" (pp_ty ty1)
             (pp_ty ty2));
      adjustlevel level ty;
      link := { link = Linkto ty; abstract = false };
      ()
  | Tvar { contents = { link = Linkto t1; _ } }, t2
  | t1, Tvar { contents = { link = Linkto t2; _ } } ->
      type_match env t1 t2
  | Tlist t1, Tlist t2 -> type_match env t1 t2
  | Tref t1, Tref t2 -> type_match env t1 t2
  | Tformat (arg1, ret1), Tformat (arg2, ret2) ->
      type_match env arg1 arg2;
      type_match env ret1 ret2
  | Tarrow (arg1, ret1), Tarrow (arg2, ret2) ->
      type_match env arg1 arg2;
      type_match env ret1 ret2
  | Ttuple tyl1, Ttuple tyl2 -> type_match_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tconstr (name2, tyl2) when name1 = name2 ->
      type_match_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Trecord (name2, tyl2, _) when name1 = name2 ->
      type_match_list env tyl1 tyl2
  | Tconstr (name1, tyl1), Tvariant (name2, tyl2, _) when name1 = name2 ->
      type_match_list env tyl1 tyl2
  | Trecord (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      type_match_list env tyl1 tyl2
  | Tvariant (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      type_match_list env tyl1 tyl2
  | Trecord (name1, _, fields1), Trecord (name2, _, fields2) when name1 = name2
    ->
      type_match_list env (List.map snd fields1) (List.map snd fields2)
  | Tvariant (name1, _, fields1), Tvariant (name2, _, fields2)
    when name1 = name2 ->
      type_match_list env (List.map snd fields1) (List.map snd fields2)
  | ty1, ty2 -> filter env ty1 ty2

and type_match_list env tyl1 tyl2 = List.iter2 (type_match env) tyl1 tyl2

let rec atomic_sig_match env sema_sig1 sema_sig2 =
  match sema_sig2 with
  | (name, AtomSig_value ty') :: xs -> (
      atomic_sig_match env sema_sig1 xs;
      match find_val name sema_sig1 with
      | Some ty -> type_match env ty ty'
      | None -> failwith "cannot find value")
  | (name, AtomSig_type decl') :: xs -> (
      atomic_sig_match env sema_sig1 xs;
      match find_type name sema_sig1 with
      | Some decl ->
          let tyl, ty = type_of_decl' decl
          and tyl', ty' = type_of_decl' decl' in
          type_match_list env tyl tyl';
          type_match env ty ty'
      | None -> failwith "cannot find type")
  | (name, AtomSig_module compound_sig') :: xs -> (
      atomic_sig_match env sema_sig1 xs;
      match find_mod name sema_sig1 with
      | Some compound_sig -> compound_sig_match env compound_sig compound_sig'
      | None -> failwith "cannot find value")
  | [] -> ()

and compound_sig_match env sema_sig1 sema_sig2 =
  match (sema_sig1, sema_sig2) with
  | ComSig_struct l1, ComSig_struct l2 -> atomic_sig_match env l1 l2
  | ComSig_fun (arg1, ret1), ComSig_fun (arg2, ret2) ->
      atomic_sig_match env [ arg2 ] [ arg1 ];
      compound_sig_match (arg1 :: env) ret1 ret2
  | _ -> failwith "compound signature matching"
