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

let instantiate level ty =
  let id_var_hash = Hashtbl.create 10 in
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
    | _ -> ty
  in
  f ty

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
  | ty1, ty2 when ty1 = ty2 -> ()
  | _ ->
      failwith
        (Printf.sprintf "Cannot unify types between %s and %s" (pp_ty ty1)
           (pp_ty ty2))

and unify_list tyl1 tyl2 = List.iter2 unify tyl1 tyl2

let rec subst_ty t id ty =
  match t with
  | Tvar { contents = Unbound { id = id'; level = _ } } when id = id' -> ty
  | Tvar { contents = Unbound _ } -> t
  | Tvar { contents = Linkto t } -> subst_ty t id ty
  | Tlist t -> Tlist (subst_ty t id ty)
  | Tref t -> Tref (subst_ty t id ty)
  | Tarrow (arg, ret) -> Tarrow (subst_ty arg id ty, subst_ty ret id ty)
  | Ttuple tyl -> Ttuple (List.map (fun t -> subst_ty t id ty) tyl)
  | Tconstr (name, tyl) ->
      Tconstr (name, List.map (fun t -> subst_ty t id ty) tyl)
  | Trecord (name, tyl, fields) ->
      Trecord (name, tyl, List.map (fun (s, t) -> (s, subst_ty t id ty)) fields)
  | Tvariant (name, tyl, fields) ->
      Tvariant (name, tyl, List.map (fun (s, t) -> (s, subst_ty t id ty)) fields)
  | _ -> t

let rec type_of_decl name decls =
  let rec aux = function
    | Drecord (n, tyl, fields) :: _ when n = name -> (
        match instantiate 1 (Trecord (n, tyl, fields)) with
        | Trecord (_, tyl, _) as ty -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | Dvariant (n, tyl, fields) :: _ when n = name -> (
        match instantiate 1 (Tvariant (n, tyl, fields)) with
        | Tvariant (_, tyl, _) as ty -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | Dabbrev (n, tyl, ty) :: _ when n = name -> (
        match instantiate 1 (Trecord (n, tyl, [ ("temp", ty) ])) with
        | Trecord (_, tyl, [ ("temp", ty) ]) -> (tyl, ty)
        | _ -> failwith "type_of_decl")
    | _ :: rest -> aux rest
    | [] -> failwith (Printf.sprintf "type_of_decl %s" name)
  in
  aux decls

and expand_abbrev ty decls =
  match ty with
  | Tconstr (name, params) ->
      let tyl, ty = type_of_decl name decls in
      if List.length params = List.length tyl then (
        unify_list params tyl;
        ty)
      else
        failwith
          ("the number of parameters of type constructor doesn't match:" ^ name)
  | Tlist t -> Tlist (expand_abbrev t decls)
  | Tref t -> Tref (expand_abbrev t decls)
  | Tarrow (arg, ret) ->
      Tarrow (expand_abbrev arg decls, expand_abbrev ret decls)
  | Ttuple tyl -> Ttuple (List.map (fun t -> expand_abbrev t decls) tyl)
  | Trecord (name, tyl, fields) ->
      Trecord
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev t decls)) fields)
  | Tvariant (name, tyl, fields) ->
      Tvariant
        (name, tyl, List.map (fun (n, t) -> (n, expand_abbrev t decls)) fields)
  | _ -> ty

let fields_of_type ty =
  let fields =
    match ty with
    | Trecord (_, _, fields) -> fields
    | Tvariant (_, _, fields) -> fields
    | _ -> failwith "not a record or variant type"
  in
  fields

let label_belong_to label decls =
  let rec aux = function
    | Drecord (name, _, fields) :: _ when List.mem_assoc label fields -> name
    | _ :: rest -> aux rest
    | _ -> failwith (Printf.sprintf "invalid label %s" label)
  in
  aux decls

let tag_belong_to tag decls =
  let rec aux = function
    | Dvariant (name, _, fields) :: _ when List.mem_assoc tag fields -> name
    | _ :: rest -> aux rest
    | _ -> failwith (Printf.sprintf "invalid tag %s" tag)
  in
  aux decls

let rec is_simple expr =
  match !expr with
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

let rec curry = function
  | { contents = Efunction [ ({ contents = Pparams [] }, e) ] } -> e
  | { contents = Efunction [ ({ contents = Pparams (p :: pl) }, e) ] } ->
      ref
        (Efunction
           [ (p, curry (ref (Efunction [ ({ contents = Pparams pl }, e) ]))) ])
  | e -> e

let type_format fmt =
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
          | _ -> failwith "bad format letter after %")
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

let rec type_pat decls level new_env pat ty =
  match !pat with
  | Pwild -> ("_", ty) :: new_env
  | Pvar s ->
      if List.mem_assoc s new_env then
        failwith ("a variable found more than twice:" ^ s)
      else (s, ty) :: new_env
  | Pparams _ -> failwith "type_pat"
  | Palias (pat, s) ->
      if List.mem_assoc s new_env then
        failwith ("a variable found more than twice:" ^ s)
      else type_pat decls level ((s, ty) :: new_env) pat ty
  | Pconstant cst ->
      let cst_ty =
        match cst with
        | Cint _ -> Tint
        | Cbool _ -> Tbool
        | Cfloat _ -> Tfloat
        | Cstring _ -> Tstring
        | Cchar _ -> Tchar
      in
      unify ty cst_ty;
      new_env
  | Ptuple patl ->
      let tyl = List.init (List.length patl) (fun _ -> new_type_var level) in
      unify (Ttuple tyl) ty;
      List.fold_left2 (type_pat decls level) new_env patl tyl
  | Pnil ->
      unify ty (Tlist (new_type_var level));
      new_env
  | Pcons (car, cdr) ->
      let ty1 = new_type_var level in
      let ty2 = new_type_var level in
      let new_env = type_pat decls level new_env car ty1 in
      let new_env = type_pat decls level new_env cdr ty2 in
      unify (Tlist ty1) ty2;
      unify ty2 ty;
      new_env
  | Pref expr ->
      let ty1 = new_type_var level in
      let new_env = type_pat decls level new_env expr ty1 in
      unify (Tref ty1) ty;
      new_env
  | Punit ->
      unify Tunit ty;
      new_env
  | Ptag ->
      unify ty Ttag;
      new_env
  | Pconstruct (name, pat) ->
      type_variant_pat new_env decls level (name, pat) ty
  | Pconstraint (pat, expected) ->
      let new_env = type_pat decls level new_env pat ty in
      unify ty (instantiate level expected);
      new_env
  | Precord fields -> type_record_pat new_env decls level fields ty

and type_record_pat env decls level fields ty =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label decls in
  let record_ty = instantiate level (snd (type_of_decl record_name decls)) in
  let fields2 = fields_of_type record_ty in
  unify record_ty ty;
  try
    List.fold_left
      (fun env (name, ty) ->
        (type_pat decls level) env
          (try List.assoc name fields
           with Not_found -> failwith ("not found:" ^ name))
          ty)
      [] fields2
    @ env
  with _ -> failwith "invalid record pattern"

and type_variant_pat env decls level (tag_name, pat) ty =
  let variant_name = tag_belong_to tag_name decls in
  let _, variant_ty = type_of_decl variant_name decls in
  unify ty (instantiate level variant_ty);
  let ty =
    try List.assoc tag_name (fields_of_type variant_ty)
    with Not_found -> failwith ("not found:" ^ tag_name)
  in
  type_pat decls level [] pat ty @ env

and type_expr env decls level expr =
  match !expr with
  | Evar s ->
      let ty =
        try instantiate level (List.assoc s env)
        with Not_found -> (
          try type_prim level (List.assoc s prim_list)
          with Not_found -> failwith ("variable not found:" ^ s))
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
      let ty = Ttuple (List.map (fun t -> type_expr env decls level t) l) in
      ty
  | Enil ->
      let ty = Tlist (new_type_var level) in
      ty
  | Econs (car, cdr) ->
      let ty1 = type_expr env decls level car in
      let ty2 = type_expr env decls level cdr in
      unify (Tlist ty1) ty2;
      ty2
  | Elist l ->
      let ty = new_type_var level in
      List.iter (fun expr -> unify ty (type_expr env decls level expr)) l;
      let ty = Tlist ty in
      ty
  | Eref e ->
      let ty = type_expr env decls level e in
      let ty = Tref ty in
      ty
  | Ederef e ->
      let ty1 = new_type_var level in
      let ty2 = type_expr env decls level e in
      unify (Tref ty1) ty2;
      ty1
  | Eassign (lhs, rhs) ->
      let ty1 = type_expr env decls level lhs in
      let ty2 = type_expr env decls level rhs in
      unify ty1 (Tref ty2);
      Tunit
  | Eloc _ ->
      let ty = new_type_var level in
      let ty = Tref ty in
      ty
  | Eunit -> Tunit
  | Etag -> Ttag
  | Econstruct (tag_name, e) ->
      let ty = type_variant_expr env decls level (tag_name, e) in
      ty
  | Eapply (({ contents = Evar s } as p), args) when List.mem_assoc s prim_list
    ->
      let prim =
        try List.assoc s prim_list
        with Not_found -> failwith ("variable not found:" ^ s)
      in
      let fct_ty = type_expr env decls level p in
      let args =
        if is_unary prim then (
          p :=
            Efunction
              [ (ref (Pvar "0"), ref (Eapply (ref !p, [ ref (Evar "0") ]))) ];
          List.map (type_expr env decls level) args)
        else if is_binary prim then (
          p :=
            Efunction
              [
                ( ref (Pparams [ ref (Pvar "0"); ref (Pvar "1") ]),
                  ref (Eapply (ref !p, [ ref (Evar "0"); ref (Evar "1") ])) );
              ];
          p := !(curry p);
          List.map (type_expr env decls level) args)
        else
          let fmt = List.hd args in
          let len, fmt_ty =
            match !fmt with
            | Econstant (Cstring fmt) -> type_format fmt
            | _ -> failwith "not a string"
          in
          p :=
            Efunction
              (( ref
                   (Pparams
                      (List.init (len + 1) (fun i ->
                           ref (Pvar (string_of_int i))))),
                 {
                   contents =
                     Eapply
                       ( ref !p,
                         List.init (len + 1) (fun i ->
                             ref (Evar (string_of_int i))) );
                 } )
              :: []);
          p := !(curry p);
          fmt_ty :: List.map (type_expr env decls level) (List.tl args)
      in
      let ty =
        List.fold_left
          (fun fct_ty arg_ty ->
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            unify fct_ty (Tarrow (param_ty, ret_ty));
            unify arg_ty param_ty;
            ret_ty)
          fct_ty args
      in
      ty
  | Eapply (({ contents = Eprim prim } as p), args) ->
      let fct_ty = type_expr env decls level p in
      let args =
        if is_unary prim then (
          p :=
            Efunction
              [ (ref (Pvar "0"), ref (Eapply (ref !p, [ ref (Evar "0") ]))) ];
          List.map (type_expr env decls level) args)
        else if is_binary prim then (
          p :=
            Efunction
              [
                ( ref (Pparams [ ref (Pvar "0"); ref (Pvar "1") ]),
                  ref (Eapply (ref !p, [ ref (Evar "0"); ref (Evar "1") ])) );
              ];
          p := !(curry p);
          List.map (type_expr env decls level) args)
        else
          let fmt = List.hd args in
          let len, fmt_ty =
            match !fmt with
            | Econstant (Cstring fmt) -> type_format fmt
            | _ -> failwith "not a string"
          in
          p :=
            Efunction
              (( ref
                   (Pparams
                      (List.init (len + 1) (fun i ->
                           ref (Pvar (string_of_int i))))),
                 {
                   contents =
                     Eapply
                       ( ref !p,
                         List.init (len + 1) (fun i ->
                             ref (Evar (string_of_int i))) );
                 } )
              :: []);
          p := !(curry p);
          fmt_ty :: List.map (type_expr env decls level) (List.tl args)
      in
      let ty =
        List.fold_left
          (fun fct_ty arg_ty ->
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            unify fct_ty (Tarrow (param_ty, ret_ty));
            unify arg_ty param_ty;
            ret_ty)
          fct_ty args
      in
      ty
  | Eapply (fct, args) ->
      let fct_ty = type_expr env decls level fct in
      let ty =
        List.fold_left
          (fun fct_ty arg_ty ->
            let param_ty = new_type_var level in
            let ret_ty = new_type_var level in
            unify fct_ty (Tarrow (param_ty, ret_ty));
            unify arg_ty param_ty;
            ret_ty)
          fct_ty
          (List.map (type_expr env decls level) args)
      in
      ty
  | Elet (pat_expr, body) ->
      let patl = List.map (fun (pat, _) -> pat) pat_expr in
      let tyl = List.map (fun (_, _) -> new_type_var level) pat_expr in
      let add_env = List.fold_left2 (type_pat decls level) [] patl tyl @ env in
      List.iter2
        (fun ty (_, expr) ->
          unify ty (type_expr env decls (level + 1) expr);
          if is_simple expr then generalize (level + 1) ty)
        tyl pat_expr;
      let ty = type_expr (add_env @ env) decls level body in
      ty
  | Eletrec (pat_expr, body) ->
      let patl = List.map (fun (pat, _) -> pat) pat_expr in
      let tyl = List.map (fun (_, _) -> new_type_var level) pat_expr in
      let add_env = List.fold_left2 (type_pat decls level) [] patl tyl @ env in
      List.iter2
        (fun ty (_, expr) ->
          unify ty (type_expr (add_env @ env) decls (level + 1) expr);
          if is_simple expr then generalize (level + 1) ty)
        tyl pat_expr;
      let ty = type_expr (add_env @ env) decls level body in
      ty
  | Efix (e, l) ->
      let ty = new_type_var level in
      unify ty (type_expr env decls level e);
      List.iter (fun (_, e) -> unify ty (type_expr env decls level e)) l;
      ty
  | Efunction l -> (
      match l with
      | [] -> failwith "empty function"
      | [ ({ contents = Pparams patl }, e) ] ->
          let tyl = List.map (fun _ -> new_type_var level) patl in
          let add_env =
            List.fold_left2 (type_pat decls level) [] patl tyl @ env
          in
          let ret_ty = type_expr add_env decls level e in
          let ty =
            List.fold_left
              (fun ret_ty arg_ty -> Tarrow (arg_ty, ret_ty))
              ret_ty (List.rev tyl)
          in
          expr := !(curry expr);
          ty
      | pat_expr ->
          let arg_ty = new_type_var level in
          let ret_ty = new_type_var level in
          List.iter
            (fun (pat, e) ->
              let add_env = type_pat decls level [] pat arg_ty in
              let ty = type_expr (add_env @ env) decls level e in
              unify ty ret_ty)
            pat_expr;
          let ty = Tarrow (arg_ty, ret_ty) in
          ty)
  | Esequence (expr1, expr2) ->
      let ty = type_expr env decls level expr1 in
      unify ty Tunit;
      let ty = type_expr env decls level expr2 in
      ty
  | Econdition (flag, ifso, ifelse) ->
      let flag = type_expr env decls level flag in
      unify flag Tbool;
      let ty = type_expr env decls level ifso in
      unify ty (type_expr env decls level ifelse);
      ty
  | Econstraint (e, expected) ->
      let ty = type_expr env decls level e in
      unify ty (instantiate level expected);
      ty
  | Erecord [] -> failwith "empty record fields"
  | Erecord l ->
      let ty = type_record_expr env decls level l in
      ty
  | Erecord_access (e, label) ->
      let ty = type_expr env decls level e in
      let record_name = label_belong_to label decls in
      let record_ty =
        instantiate level (snd (type_of_decl record_name decls))
      in
      unify ty (instantiate level record_ty);
      let ty =
        try List.assoc label (fields_of_type record_ty)
        with Not_found -> failwith ("label not found:" ^ label)
      in
      ty
  | Ewhen (e, body) ->
      let ty = type_expr env decls level e in
      unify ty Tbool;
      let ty = type_expr env decls level body in
      ty

and type_record_expr env decls level fields =
  let first_label = fst (List.hd fields) in
  let record_name = label_belong_to first_label decls in
  let record_ty = instantiate level (snd (type_of_decl record_name decls)) in
  let fields1 =
    List.map (fun (n, e) -> (n, type_expr env decls level e)) fields
  in
  let fields2 = fields_of_type record_ty in
  try
    List.iter
      (fun (name, ty) ->
        unify
          (try List.assoc name fields1
           with Not_found -> failwith ("invalid label:" ^ name))
          ty)
      fields2;
    record_ty
  with _ -> failwith "invalid record expression"

and type_variant_expr env decls level (tag_name, expr) =
  let variant_name = tag_belong_to tag_name decls in
  let variant_ty = instantiate level (snd (type_of_decl variant_name decls)) in
  let ty =
    try List.assoc tag_name (fields_of_type variant_ty)
    with Not_found -> failwith ("invalid tag:" ^ tag_name)
  in
  let ty1 = type_expr env decls level expr in
  unify ty ty1;
  variant_ty

let type_let env decls pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1)) pat_expr in
  let add_env = List.fold_left2 (type_pat decls (level + 1)) [] patl tyl in
  List.iter2
    (fun ty (_, expr) ->
      unify ty (type_expr env decls (level + 1) expr);
      if is_simple expr then generalize level ty)
    tyl pat_expr;
  add_env

let type_letrec env decls pat_expr =
  let level = 0 in
  let patl = List.map (fun (pat, _) -> pat) pat_expr in
  let tyl = List.map (fun (_, _) -> new_type_var (level + 1)) pat_expr in
  let add_env = List.fold_left2 (type_pat decls (level + 1)) [] patl tyl in
  List.iter2
    (fun ty (_, expr) ->
      unify ty (type_expr (add_env @ env) decls (level + 1) expr);
      if is_simple expr then generalize level ty)
    tyl pat_expr;
  add_env
