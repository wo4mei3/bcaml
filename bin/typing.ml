open Syntax
open Printer

let curr_id = ref 0

let gen_id () =
  let ret = !curr_id in
  incr curr_id;
  ret

let new_type_var level = Tvar (ref (Unbound { id = Idint (gen_id ()); level }))

let min_opt lhs rhs =
  match (lhs, rhs) with
  | Some l, Some r -> Some (min l r)
  | Some l, None -> Some l
  | None, Some r -> Some r
  | None, None -> None

let rec get_type_level ty =
  match ty with
  | Tvar { contents = Unbound { id = _; level } } -> Some level
  | Tvar { contents = Linkto ty } -> get_type_level ty
  | Tunit | Tbool | Tint | Tfloat | Tchar | Tstring -> None
  | Tlist ty | Tref ty -> get_type_level ty
  | Tarrow (arg, ret) -> min_opt (get_type_level arg) (get_type_level ret)
  | Ttuple tyl | Tconstr (_, tyl) -> get_type_level_list tyl
  | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
      get_type_level_list (List.map snd fields)
  | Ttag -> None
  | _ -> failwith "get_type_level"

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
      | { contents = Unbound { id; level = level' } } when level' > level ->
          link := Unbound { id; level = generic }
      | { contents = Linkto ty } -> generalize level ty
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

let instantiate' id_var_hash level ty =
  let rec f ty =
    match ty with
    | Tvar link -> (
        match link with
        | { contents = Unbound { id; level = level' } } when level' = generic
          -> (
            try Hashtbl.find id_var_hash id
            with Not_found ->
              let tvar = Tvar (ref (Linkto (new_type_var level))) in
              Hashtbl.add id_var_hash id tvar;
              tvar)
        | { contents = Linkto ty } -> f ty
        | _ -> ty)
    | Tlist ty -> Tlist (f ty)
    | Tref ty -> Tref (f ty)
    | Tarrow (arg, ret) -> Tarrow (f arg, f ret)
    | Ttuple tyl -> Ttuple (List.map f tyl)
    | Tconstr (name, tyl) -> Tconstr (name, List.map f tyl)
    | Trecord (name, tyl, fields) ->
        Trecord
          (name, List.map f tyl, List.map (fun (n, ty) -> (n, f ty)) fields)
    | Tvariant (name, tyl, fields) ->
        Tvariant
          (name, List.map f tyl, List.map (fun (n, ty) -> (n, f ty)) fields)
    | Tabs (ty, tyl) -> Tabs (f ty, List.map f tyl)
    | _ -> ty
  in
  f ty

let instantiate level ty = instantiate' (Hashtbl.create 10) level ty

let instantiate_sema_sig sema_sig =
  let id_var_hash = Hashtbl.create 10 in
  let rec f id_var_hash = function
    | Sigval (n, ty) -> Sigval (n, instantiate' id_var_hash 1 ty)
    | Sigtype l ->
        Sigtype (List.map (fun (n, decl) -> (n, g id_var_hash decl)) l)
    | Sigmod (n, sema_sig) -> Sigmod (n, f id_var_hash sema_sig)
    | Sigstruct l -> Sigstruct (List.map (f id_var_hash) l)
    | Sigfun (arg, ret) -> Sigfun (f id_var_hash arg, f id_var_hash ret)
  and g id_var_hash = function
    | { ast = Drecord (n, tyl, fields); pos } -> (
        match instantiate' id_var_hash 1 (Trecord (n, tyl, fields)) with
        | Trecord (n, tyl, fields) -> { ast = Drecord (n, tyl, fields); pos }
        | _ -> failwith "type_of_decl")
    | { ast = Dvariant (n, tyl, fields); pos } -> (
        match instantiate' id_var_hash 1 (Tvariant (n, tyl, fields)) with
        | Tvariant (n, tyl, fields) -> { ast = Dvariant (n, tyl, fields); pos }
        | _ -> failwith "type_of_decl")
    | { ast = Dabbrev (n, tyl, ty); pos } -> (
        match
          instantiate' id_var_hash 1 (Trecord (n, tyl, [ ("temp", ty) ]))
        with
        | Trecord (n, tyl, [ ("temp", ty) ]) ->
            { ast = Dabbrev (n, tyl, ty); pos }
        | _ -> failwith "type_of_decl")
    | { ast = Dabs (n, tyl, ty); pos } ->
        { ast = Dabs (n, tyl, instantiate' id_var_hash 1 ty); pos }
  in
  f id_var_hash sema_sig

let rec type_of_decl env name =
  let aux = function
    | { ast = Drecord (n, tyl, fields); _ } -> (
        match instantiate 1 (Trecord (n, tyl, fields)) with
        | Trecord (_, tyl, _) as ty -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | { ast = Dvariant (n, tyl, fields); _ } -> (
        match instantiate 1 (Tvariant (n, tyl, fields)) with
        | Tvariant (_, tyl, _) as ty -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | { ast = Dabbrev (n, tyl, ty); _ } -> (
        match instantiate 1 (Trecord (n, tyl, [ ("temp", ty) ])) with
        | Trecord (_, tyl, [ ("temp", ty) ]) -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | { ast = Dabs (_, tyl, ty); _ } -> (tyl, ty)
  in
  match env with
  | Sigtype l :: _ when List.mem_assoc name l -> aux (List.assoc name l)
  | _ :: xs -> type_of_decl xs name
  | [] -> failwith (Printf.sprintf "type_of_decl %s" name)

let rec access_sig path sema_sig =
  match (path, sema_sig) with
  | s :: path, Sigmod (n, sema_sig) when s = n -> access_sig path sema_sig
  | (s :: _ as path), Sigstruct l when Option.is_some (find_mod s l) ->
      access_sig path (Option.get (find_mod s l))
  | _ :: _, _ -> failwith "invalid path"
  | [], sema_sig -> instantiate_sema_sig sema_sig

let rec occursin id = function
  | Tvar link -> (
      match link with
      | { contents = Unbound { id = id'; level = _ } } -> id = id'
      | { contents = Linkto ty } -> occursin id ty)
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
      | { contents = Unbound { id = id'; level = level' } } ->
          if level < level' then link := Unbound { id = id'; level }
      | { contents = Linkto ty } -> adjustlevel level ty)
  | Tlist ty -> adjustlevel level ty
  | Tref ty -> adjustlevel level ty
  | Tarrow (arg, ret) ->
      adjustlevel level arg;
      adjustlevel level ret
  | Ttuple tyl | Tconstr (_, tyl) -> List.iter (adjustlevel level) tyl
  | Trecord (_, _, fields) | Tvariant (_, _, fields) ->
      List.iter (adjustlevel level) (List.map snd fields)
  | _ -> ()

let rec unify ty1 ty2 =
  match (ty1, ty2) with
  | Tvar link1, Tvar link2 when link1 = link2 -> ()
  | Tvar { contents = Linkto t1 }, t2 | t1, Tvar { contents = Linkto t2 } ->
      unify t1 t2
  | Tvar ({ contents = Unbound { id; level } } as link), ty
  | ty, Tvar ({ contents = Unbound { id; level } } as link) ->
      if occursin id ty then
        failwith
          (Printf.sprintf "unify error due to ocurr check %s %s" (pp_ty ty1)
             (pp_ty ty2));
      adjustlevel level ty;
      link := Linkto ty
  | Tlist t1, Tlist t2 -> unify t1 t2
  | Tref t1, Tref t2 -> unify t1 t2
  | Tformat (arg1, ret1), Tformat (arg2, ret2) ->
      unify arg1 arg2;
      unify ret1 ret2
  | Tarrow (arg1, ret1), Tarrow (arg2, ret2) ->
      unify arg1 arg2;
      unify ret1 ret2
  | Ttuple tyl1, Ttuple tyl2 -> unify_list tyl1 tyl2
  | Tconstr (name1, tyl1), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list tyl1 tyl2
  | Tconstr (name1, tyl1), Trecord (name2, tyl2, _) when name1 = name2 ->
      unify_list tyl1 tyl2
  | Tconstr (name1, tyl1), Tvariant (name2, tyl2, _) when name1 = name2 ->
      unify_list tyl1 tyl2
  | Trecord (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list tyl1 tyl2
  | Tvariant (name1, tyl1, _), Tconstr (name2, tyl2) when name1 = name2 ->
      unify_list tyl1 tyl2
  | Trecord (name1, _, fields1), Trecord (name2, _, fields2) when name1 = name2
    ->
      unify_list (List.map snd fields1) (List.map snd fields2)
  | Tvariant (name1, _, fields1), Tvariant (name2, _, fields2)
    when name1 = name2 ->
      unify_list (List.map snd fields1) (List.map snd fields2)
  | Tabs (ty1, tyl1), Tabs (ty2, tyl2) ->
      unify ty1 ty2;
      unify_list tyl1 tyl2
  | ty1, ty2 when ty1 = ty2 -> ()
  | _ ->
      failwith
        (Printf.sprintf "Cannot unify types between %s and %s" (pp_ty ty1)
           (pp_ty ty2))

and unify_list tyl1 tyl2 = List.iter2 unify tyl1 tyl2

let rec expand_abbrev ty env =
  match ty with
  | Tconstr (name, params) ->
      let tyl, ty = type_of_decl env name in
      if List.length params = List.length tyl then (
        unify_list params tyl;
        ty)
      else
        failwith
          ("the number of parameters of type constructor doesn't match:" ^ name)
  | Tlist t -> Tlist (expand_abbrev t env)
  | Tref t -> Tref (expand_abbrev t env)
  | Tarrow (arg, ret) -> Tarrow (expand_abbrev arg env, expand_abbrev ret env)
  | Ttuple tyl -> Ttuple (List.map (fun t -> expand_abbrev t env) tyl)
  | Trecord (name, tyl, fields) ->
      Trecord
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev t env)) fields)
  | Tvariant (name, tyl, fields) ->
      Tvariant
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev t env)) fields)
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
    | Sigtype l :: rest ->
        let rec aux2 = function
          | (_, { ast = Drecord (name, _, fields); _ }) :: _
            when List.mem_assoc label fields ->
              name
          | _ :: rest -> aux2 rest
          | [] -> aux rest
        in
        aux2 l
    | _ :: rest -> aux rest
    | [] ->
        failwith
          (Printf.sprintf "%s invalid label %s" (print_errloc !file pos) label)
  in
  aux env

let tag_belong_to env tag pos =
  let rec aux = function
    | Sigtype l :: rest ->
        let rec aux2 = function
          | (_, { ast = Dvariant (name, _, fields); _ }) :: _
            when List.mem_assoc tag fields ->
              name
          | _ :: rest -> aux2 rest
          | [] -> aux rest
        in
        aux2 l
    | _ :: rest -> aux rest
    | [] ->
        failwith
          (Printf.sprintf "%s invalid tag %s" (print_errloc !file pos) tag)
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
  let ty_result = new_type_var notgeneric in
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
      let tvar = new_type_var level in
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
      let tvar = new_type_var level in
      Tarrow (Tlist tvar, Tarrow (Tlist tvar, Tlist tvar))
  | Pfailwith ->
      let tvar = new_type_var level in
      Tarrow (Tstring, tvar)
  | Pprintf ->
      let remain_ty = new_type_var notgeneric in
      Tarrow (Tformat (remain_ty, Tunit), remain_ty)
  | Psprintf ->
      let remain_ty = new_type_var notgeneric in
      Tarrow (Tformat (remain_ty, Tstring), remain_ty)

let unify_pat pat actual_ty expected_ty =
  try unify actual_ty expected_ty
  with _ ->
    failwith
      (Printf.sprintf
         "%s This pattern matches values of type %s,\n\
          but should match values of type %s.\n"
         (print_errloc !file pat.pos)
         (pp_ty actual_ty) (pp_ty expected_ty))

let rec type_pat env add_env level pat ty =
  match !(pat.ast) with
  | Pwild -> Sigval ("_", ty) :: add_env
  | Pvar s -> (
      match find_val s add_env with
      | None -> Sigval (s, ty) :: add_env
      | Some _ ->
          failwith
            (Printf.sprintf "%s a variable found more than twice: %s"
               (print_errloc !file pat.pos)
               s))
  | Pparams _ -> failwith "type_pat"
  | Palias (pat, s) -> (
      match find_val s add_env with
      | None -> type_pat env (Sigval (s, ty) :: add_env) level pat ty
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
      unify_pat pat ty cst_ty;
      env
  | Ptuple patl ->
      let tyl = List.init (List.length patl) (fun _ -> new_type_var level) in
      unify (Ttuple tyl) ty;
      List.fold_left2
        (fun add_env -> type_pat env add_env level)
        add_env patl tyl
  | Pnil ->
      unify_pat pat ty (Tlist (new_type_var level));
      env
  | Pcons (car, cdr) ->
      let ty1 = new_type_var level in
      let ty2 = new_type_var level in
      let add_env = type_pat env add_env level car ty1 in
      let add_env = type_pat env add_env level cdr ty2 in
      unify_pat pat ty2 (Tlist ty1);
      unify_pat pat ty ty2;
      add_env
  | Pref expr ->
      let ty1 = new_type_var level in
      let add_env = type_pat env add_env level expr ty1 in
      unify_pat pat ty (Tref ty1);
      add_env
  | Punit ->
      unify_pat pat ty Tunit;
      add_env
  | Ptag ->
      unify ty Ttag;
      add_env
  | Pconstruct (name, pat) -> type_variant_pat env add_env level (name, pat) ty
  | Pconstraint (pat, expected) ->
      let add_env = type_pat env add_env level pat ty in
      unify_pat pat ty (instantiate level expected);
      add_env
  | Precord fields -> type_record_pat env add_env level fields ty pat

and type_record_pat env add_env level fields ty pat =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to env first_label pat.pos in
  let record_ty = instantiate level (snd (type_of_decl env record_name)) in
  let fields2 = fields_of_type record_ty in
  unify record_ty ty;
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
  unify ty (instantiate level variant_ty);
  let ty =
    try List.assoc tag_name (fields_of_type variant_ty)
    with Not_found ->
      failwith
        (Printf.sprintf "%s not found: %s"
           (print_errloc !file pat.pos)
           tag_name)
  in
  type_pat env add_env level pat ty

and unify_expr expr actual_ty expected_ty =
  try unify actual_ty expected_ty
  with _ ->
    failwith
      (Printf.sprintf
         "%s This expression has type %s,\nbut is expected type %s.\n"
         (print_errloc !file expr.pos)
         (pp_ty actual_ty) (pp_ty expected_ty))

and function_error level expr ty =
  failwith
    (try
       let param_ty = new_type_var level in
       let ret_ty = new_type_var level in
       unify ty (Tarrow (param_ty, ret_ty));
       Printf.sprintf "%s This function is applied to too many arguments.\n"
         (print_errloc !file expr.pos)
     with _ ->
       Printf.sprintf
         "%s This expression is not a function, it cannot be applied.\n"
         (print_errloc !file expr.pos))

and type_expect env level expr expected_ty =
  match !(expr.ast) with
  | _ -> unify_expr expr (type_expr env level expr) expected_ty

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
      let ty = Tlist (new_type_var level) in
      ty
  | Econs (car, cdr) ->
      let ty = type_expr env level cdr in
      let expected_ty = new_type_var level in
      unify (Tlist expected_ty) ty;
      type_expect env level car expected_ty;
      ty
  | Elist l ->
      let ty = new_type_var level in
      List.iter (fun expr -> unify ty (type_expr env level expr)) l;
      let ty = Tlist ty in
      ty
  | Eref e ->
      let ty = type_expr env level e in
      let ty = Tref ty in
      ty
  | Ederef e ->
      let ty = new_type_var level in
      type_expect env level e (Tref ty);
      ty
  | Eassign (lhs, rhs) ->
      let ty = type_expr env level rhs in
      type_expect env level lhs (Tref ty);
      Tunit
  | Eloc _ ->
      let ty = new_type_var level in
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
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            (try unify fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error level p fct_ty);
            unify arg_ty param_ty;
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
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            (try unify fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error level p fct_ty);
            unify arg_ty param_ty;
            ret_ty)
          fct_ty args
      in
      ty
  | Eapply (fct, args) ->
      let fct_ty = type_expr env level fct in
      let ty =
        List.fold_left
          (fun fct_ty_ arg_ty ->
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            (try unify fct_ty_ (Tarrow (param_ty, ret_ty))
             with _ -> function_error level fct fct_ty);
            unify arg_ty param_ty;
            ret_ty)
          fct_ty
          (List.map (type_expr env level) args)
      in
      ty
  | Elet (pat_expr, body) ->
      let patl = List.map (fun (pat, _) -> pat) pat_expr in
      let tyl = List.map (fun (_, _) -> new_type_var level) pat_expr in
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
      let tyl = List.map (fun (_, _) -> new_type_var level) pat_expr in
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
      let ty = new_type_var level in
      type_expect env level e ty;
      List.iter (fun (_, e) -> type_expect env level e ty) l;
      ty
  | Efunction l -> (
      match l with
      | [] ->
          failwith
            (Printf.sprintf "%s empty function" (print_errloc !file expr.pos))
      | [ ({ ast = { contents = Pparams patl }; _ }, e) ] ->
          let tyl = List.map (fun _ -> new_type_var level) patl in
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
          let arg_ty = new_type_var level in
          let ret_ty = new_type_var level in
          List.iter
            (fun (pat, e) ->
              let add_env = type_pat env [] level pat arg_ty in
              let ty = type_expr (add_env @ env) level e in
              unify ty ret_ty)
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
  | Epath _ -> Tint

and type_record_expr env level fields expr =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to env first_label expr.pos in
  let record_ty = instantiate level (snd (type_of_decl env record_name)) in
  let fields1 = List.map (fun (n, e) -> (n, type_expr env level e)) fields in
  let fields2 = fields_of_type record_ty in
  try
    List.iter
      (fun (name, ty) ->
        unify
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
  unify ty ty1;
  variant_ty

let type_let env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1)) pat_expr in
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
  add_env @ env

let type_letrec env pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1)) pat_expr in
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
  add_env @ env

let rec type_sig_expr env sig_expr =
  match sig_expr.ast with
  | Svar name -> access_sig [ name ] (Sigstruct env)
  | Sfunctor ((name, arg), ret) ->
      let arg = type_sig_expr env arg in
      let ret = type_sig_expr (Sigmod (name, arg) :: env) ret in
      Sigfun (arg, ret)
  | Sval (name, ty) -> Sigval (name, ty)
  | Sstruct l -> Sigstruct (List.map (type_sig_expr env) l)
  | Smodule (name, sig_expr) -> Sigmod (name, type_sig_expr env sig_expr)
  | Ssig (name, sig_expr) -> Sigmod (name, type_sig_expr env sig_expr)
  | Sinclude path -> access_sig path (Sigstruct env)
  | _ -> Sigstruct []
