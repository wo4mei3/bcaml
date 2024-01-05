open Syntax

exception InterpreterError of string

type ctx = (string * expr) list [@@deriving show]

let ctx = ref (List.map (fun (n, p) -> (n, ref (Eprim p))) prim_list)
let extendcontext name v = ctx := (name, v) :: !ctx
let lookupcontext name = List.assoc name !ctx

type store = expr list

let store = ref []

let extendstore v =
  let loc = List.length !store in
  store := !store @ [ v ];
  loc

let lookuploc l = List.nth !store l

let updatestore n v =
  let rec f s =
    match s with
    | 0, _ :: rest -> v :: rest
    | n, v' :: rest -> v' :: f (n - 1, rest)
    | _ -> failwith "bad index"
  in
  store := f (n, !store)

let rec isval expr =
  match !expr with
  | Evar _ -> false
  | Econstant _ -> true
  | Eprim Pprintf | Eprim Psprintf -> true
  | Eprim _ -> false
  | Etuple l -> List.for_all (fun x -> isval x) l
  | Enil | Econs _ -> false
  | Elist _ -> true
  | Eref _ | Ederef _ | Eassign _ -> false
  | Eloc _ | Etag | Eunit -> true
  | Econstruct (_, expr) -> isval expr
  | Eapply _ | Elet _ | Eletrec _ -> false
  | Efix _ -> true
  | Efunction _ -> true
  | Esequence _ -> false
  | Econdition _ -> false
  | Econstraint (expr, _) -> isval expr
  | Erecord l -> List.for_all (fun x -> isval x) (List.map snd l)
  | Erecord_access _ -> false
  | Ewhen _ -> true

let eval_prim_unary prim x =
  let x = x in
  match prim with
  | Pnot -> do_unary (Ubool_to_bool not) x
  | Pnegint -> do_unary (Uint_to_int ( ~- )) x
  | Plnot -> do_unary (Uint_to_int lnot) x
  | Pnegfloat -> do_unary (Ufloat_to_float ( ~-. )) x
  | Pintoffloat -> do_unary (Ufloat_to_int int_of_float) x
  | Pfloatofint -> do_unary (Uint_to_float float_of_int) x
  | Pintofchar -> do_unary (Uchar_to_int int_of_char) x
  | Pcharofint -> do_unary (Uint_to_char char_of_int) x
  | Pstringofbool -> do_unary (Ubool_to_string string_of_bool) x
  | Pboolofstring -> do_unary (Ustring_to_bool bool_of_string) x
  | Pstringofint -> do_unary (Uint_to_string string_of_int) x
  | Pintofstring -> do_unary (Ustring_to_int int_of_string) x
  | Pstringoffloat -> do_unary (Ufloat_to_string string_of_float) x
  | Pfloatofstring -> do_unary (Ustring_to_float float_of_string) x
  | Pfailwith -> raise (InterpreterError (get_string (get_constant !x)))
  | _ -> failwith "eval_prim_unary"

let rec eval_prim_eq x y =
  match (!x, !y) with
  | Econstant l, Econstant r -> l = r
  | Etuple l, Etuple r -> List.for_all2 (fun l r -> eval_prim_eq l r) l r
  | Elist l, Elist r -> List.for_all2 (fun l r -> eval_prim_eq l r) l r
  | Eloc l, Eloc r -> eval_prim_eq (lookuploc l) (lookuploc r)
  | Etag, Etag -> true
  | Eunit, Eunit -> true
  | Econstruct (ln, l), Econstruct (rn, r) when ln = rn -> eval_prim_eq l r
  | Erecord ls, Erecord rs ->
      List.for_all (fun (n, e) -> eval_prim_eq (List.assoc n ls) e) rs
  | Eprim _, Eprim _ -> raise (InterpreterError "comparison between functions")
  | Efunction _, Efunction _ ->
      raise (InterpreterError "comparison between functions")
  | _, _ -> failwith "eval_prim_eq"

let rec eval_prim_eq_imm x y =
  match (!x, !y) with
  | Econstant l, Econstant r -> l = r
  | Etuple l, Etuple r -> List.for_all2 (fun l r -> eval_prim_eq_imm l r) l r
  | Elist l, Elist r -> List.for_all2 (fun l r -> eval_prim_eq_imm l r) l r
  | Eloc l, Eloc r -> l = r
  | Etag, Etag -> true
  | Eunit, Eunit -> true
  | Econstruct (ln, l), Econstruct (rn, r) when ln = rn -> eval_prim_eq_imm l r
  | Erecord ls, Erecord rs ->
      List.for_all (fun (n, e) -> eval_prim_eq_imm (List.assoc n ls) e) rs
  | Eprim _, Eprim _ -> raise (InterpreterError "comparison between functions")
  | Efunction _, Efunction _ ->
      raise (InterpreterError "comparison between functions")
  | _, _ -> failwith "eval_prim_eq"

let eval_prim_binary prim x y =
  match prim with
  | Peq -> Econstant (Cbool (eval_prim_eq x y))
  | Pnq -> Econstant (Cbool (not (eval_prim_eq x y)))
  | Plt -> do_binary_eq ( < ) x y
  | Pgt -> do_binary_eq ( > ) x y
  | Ple -> do_binary_eq ( <= ) x y
  | Pge -> do_binary_eq ( >= ) x y
  | Peqimm -> Econstant (Cbool (eval_prim_eq_imm x y))
  | Pnqimm -> Econstant (Cbool (not (eval_prim_eq_imm x y)))
  | Pand -> do_binary (Bbool ( && )) x y
  | Por -> do_binary (Bbool ( || )) x y
  | Paddint -> do_binary (Bint ( + )) x y
  | Psubint -> do_binary (Bint ( - )) x y
  | Pmulint -> do_binary (Bint ( * )) x y
  | Pdivint -> do_binary (Bint ( / )) x y
  | Pmod -> do_binary (Bint ( mod )) x y
  | Pland -> do_binary (Bint ( land )) x y
  | Plor -> do_binary (Bint ( lor )) x y
  | Plxor -> do_binary (Bint ( lxor )) x y
  | Plsl -> do_binary (Bint ( lsl )) x y
  | Plsr -> do_binary (Bint ( lsr )) x y
  | Pasr -> do_binary (Bint ( asr )) x y
  | Paddfloat -> do_binary (Bfloat ( +. )) x y
  | Psubfloat -> do_binary (Bfloat ( -. )) x y
  | Pmulfloat -> do_binary (Bfloat ( *. )) x y
  | Pdivfloat -> do_binary (Bfloat ( /. )) x y
  | Ppower -> do_binary (Bfloat ( ** )) x y
  | Pconcatstring -> do_binary (Bstring ( ^ )) x y
  | Pconcat -> (
      match (!x, !y) with
      | Elist x, Elist y -> Elist (x @ y)
      | _ -> failwith "eval_prim_binary")
  | _ -> failwith "eval_prim_binary"

let eval_prim_printf fmt args =
  let len = String.length fmt in
  let printf = Printf.printf in
  let rec print i = function
    | arg :: args -> (
        if i >= len then ()
        else
          match fmt.[i] with
          | '%' -> (
              let j = i + 1 in
              match fmt.[j] with
              | '%' ->
                  printf "%%";
                  print (j + 1) (arg :: args)
              | 's' ->
                  printf "%s" (arg |> get_constant |> get_string);
                  print (j + 1) args
              | 'c' ->
                  printf "%c" (arg |> get_constant |> get_char);
                  print (j + 1) args
              | 'd' | 'o' | 'x' | 'X' | 'u' ->
                  printf "%d" (arg |> get_constant |> get_int);
                  print (j + 1) args
              | 'f' | 'e' | 'E' | 'g' | 'G' ->
                  printf "%f" (arg |> get_constant |> get_float);
                  print (j + 1) args
              | 'b' ->
                  printf "%b" (arg |> get_constant |> get_bool);
                  print (j + 1) args
              | _ -> failwith "bad format letter after %")
          | s ->
              printf "%c" s;
              print (i + 1) (arg :: args))
    | [] ->
        if i >= len then ()
        else (
          printf "%c" fmt.[i];
          print (i + 1) [])
  in
  print 0 args;
  ref Eunit

let eval_prim_sprintf fmt args =
  let len = String.length fmt in
  let sprintf = Printf.sprintf in
  let rec sprint i = function
    | arg :: args -> (
        if i >= len then ""
        else
          match fmt.[i] with
          | '%' -> (
              let j = i + 1 in
              match fmt.[j] with
              | '%' -> sprintf "%%" ^ sprint (j + 1) (arg :: args)
              | 's' ->
                  sprintf "%s" (arg |> get_constant |> get_string)
                  ^ sprint (j + 1) args
              | 'c' ->
                  sprintf "%c" (arg |> get_constant |> get_char)
                  ^ sprint (j + 1) args
              | 'd' | 'o' | 'x' | 'X' | 'u' ->
                  sprintf "%d" (arg |> get_constant |> get_int)
                  ^ sprint (j + 1) args
              | 'f' | 'e' | 'E' | 'g' | 'G' ->
                  sprintf "%f" (arg |> get_constant |> get_float)
                  ^ sprint (j + 1) args
              | 'b' ->
                  sprintf "%b" (arg |> get_constant |> get_bool)
                  ^ sprint (j + 1) args
              | _ -> failwith "bad format letter after %")
          | s -> sprintf "%c" s ^ sprint (i + 1) (arg :: args))
    | [] -> if i >= len then "" else sprintf "%c" fmt.[i] ^ sprint (i + 1) []
  in
  ref (Econstant (Cstring (sprint 0 args)))

let unique_name = ref 0

let gen_alpha () =
  let name = "Alpha" ^ string_of_int !unique_name in
  unique_name := !unique_name + 1;
  name

let rec collect_pvars pat =
  let aux l =
    match !pat with
    | Pwild -> l
    | Pvar name -> name :: l
    | Pparams pl ->
        List.fold_left (fun l pat -> collect_pvars pat @ l) [] pl @ l
    | Palias (pat, name) -> (name :: collect_pvars pat) @ l
    | Pconstant _ -> []
    | Ptuple pl -> List.fold_left (fun l pat -> collect_pvars pat @ l) [] pl @ l
    | Pnil -> []
    | Pcons (car, cdr) -> collect_pvars car @ collect_pvars cdr @ l
    | Pref pat -> collect_pvars pat @ l
    | Punit | Ptag -> []
    | Pconstruct (_, pat) -> collect_pvars pat @ l
    | Pconstraint (pat, _) -> collect_pvars pat @ l
    | Precord f ->
        List.fold_left (fun l (_, pat) -> collect_pvars pat @ l) [] f @ l
  in
  aux []

let rec subst_to_expr expr l =
  let conv_pat pat table =
    List.fold_left
      (fun pat (name, alpha) -> subst_to_pat pat [ (name, ref (Pvar alpha)) ])
      pat table
  in
  let conv_expr expr table =
    List.fold_left
      (fun expr (name, alpha) ->
        subst_to_expr expr [ (name, ref (Evar alpha)) ])
      expr table
  in
  let aux expr (n, e) =
    match !expr with
    | Evar name when n = name -> e
    | Evar _ -> expr
    | Econstant _ | Eprim _ -> expr
    | Etuple el -> ref (Etuple (List.map (fun e -> subst_to_expr e l) el))
    | Enil -> expr
    | Econs (car, cdr) -> ref (Econs (subst_to_expr car l, subst_to_expr cdr l))
    | Elist el -> ref (Elist (List.map (fun e -> subst_to_expr e l) el))
    | Eref e -> ref (Eref (subst_to_expr e l))
    | Ederef e -> ref (Ederef (subst_to_expr e l))
    | Eassign (lhs, rhs) ->
        ref (Eassign (subst_to_expr lhs l, subst_to_expr rhs l))
    | Eloc _ | Etag | Eunit -> expr
    | Econstruct (t, e) -> ref (Econstruct (t, subst_to_expr e l))
    | Eapply (f, args) ->
        ref
          (Eapply (subst_to_expr f l, List.map (fun e -> subst_to_expr e l) args))
    | Elet (pe, expr) ->
        let pvars =
          List.fold_left (fun l (p, _) -> collect_pvars p @ l) [] pe
        in
        let table = List.map (fun p -> (p, gen_alpha ())) pvars in
        let pe = List.map (fun (p, e) -> (conv_pat p table, e)) pe in
        let expr = conv_expr expr table in
        ref
          (Elet
             ( List.map (fun (p, e) -> (p, subst_to_expr e l)) pe,
               subst_to_expr expr l ))
    | Eletrec (pe, expr) ->
        let pvars =
          List.fold_left (fun l (p, _) -> collect_pvars p @ l) [] pe
        in
        let table = List.map (fun p -> (p, gen_alpha ())) pvars in
        let pe =
          List.map (fun (p, e) -> (conv_pat p table, conv_expr e table)) pe
        in
        let expr = conv_expr expr table in
        ref
          (Eletrec
             ( List.map (fun (p, e) -> (p, subst_to_expr e l)) pe,
               subst_to_expr expr l ))
    | Efix _ -> expr
    | Efunction pe ->
        ref
          (Efunction
             (List.map
                (fun (p, e) ->
                  let pvars = collect_pvars p in
                  let table = List.map (fun p -> (p, gen_alpha ())) pvars in
                  (conv_pat p table, subst_to_expr (conv_expr e table) l))
                pe))
    | Esequence (lhs, rhs) ->
        ref (Esequence (subst_to_expr lhs l, subst_to_expr rhs l))
    | Econdition (expr1, expr2, expr3) ->
        ref
          (Econdition
             ( subst_to_expr expr1 l,
               subst_to_expr expr2 l,
               subst_to_expr expr3 l ))
    | Econstraint (expr, t) -> ref (Econstraint (subst_to_expr expr l, t))
    | Erecord f ->
        ref (Erecord (List.map (fun (lbl, e) -> (lbl, subst_to_expr e l)) f))
    | Erecord_access (e, lbl) -> ref (Erecord_access (subst_to_expr e l, lbl))
    | Ewhen (lhs, rhs) -> ref (Ewhen (subst_to_expr lhs l, subst_to_expr rhs l))
  in
  List.fold_left aux expr l

and subst_to_pat pat l =
  let get_name = function
    | { contents = Pvar name } -> name
    | _ -> failwith "get_name"
  in
  let aux pat (n, p) =
    match !pat with
    | Pwild -> pat
    | Pvar name when n = name -> p
    | Pvar _ -> pat
    | Pparams pl -> ref (Pparams (List.map (fun p -> subst_to_pat p l) pl))
    | Palias (pat, name) ->
        ref
          (Palias
             (subst_to_pat pat l, get_name (subst_to_pat (ref (Pvar name)) l)))
    | Pconstant _ -> pat
    | Ptuple pl -> ref (Ptuple (List.map (fun p -> subst_to_pat p l) pl))
    | Pnil -> pat
    | Pcons (car, cdr) -> ref (Pcons (subst_to_pat car l, subst_to_pat cdr l))
    | Pref pat -> ref (Pref (subst_to_pat pat l))
    | Punit | Ptag -> pat
    | Pconstruct (t, pat) -> ref (Pconstruct (t, subst_to_pat pat l))
    | Pconstraint (pat, t) -> ref (Pconstraint (subst_to_pat pat l, t))
    | Precord f ->
        ref (Precord (List.map (fun (lbl, p) -> (lbl, subst_to_pat p l)) f))
  in
  List.fold_left aux pat l

(*
(fun pat -> expr) expr'
*)
let rec do_match pat expr =
  match (!pat, !expr) with
  | Pwild, _ -> [ ("_", expr) ]
  | Pvar name, _ -> [ (name, expr) ]
  | Pparams (p :: _), _ -> do_match p expr
  | Palias (p, name), _ -> (name, expr) :: do_match p expr
  | Pconstant cst1, Econstant cst2 when cst1 = cst2 -> []
  | Ptuple pl, Etuple el ->
      List.fold_left2 (fun l p e -> l @ do_match p e) [] pl el
  | Pnil, Elist [] -> []
  | Pcons (car, cdr), Elist (e :: el) ->
      do_match car e @ do_match cdr (ref (Elist el))
  | Pref p, Eloc loc -> do_match p (lookuploc loc)
  | Punit, Eunit | Ptag, Etag -> []
  | Pconstruct (name1, pat), Econstruct (name2, expr) when name1 = name2 ->
      do_match pat expr
  | Pconstraint (p, _), _ -> do_match p expr
  | Precord pf, Erecord ef ->
      List.fold_left
        (fun l p -> l @ do_match (snd p) (List.assoc (fst p) ef))
        [] pf
  | _ -> failwith "do_match'"

and do_matches pat_exprs expr' =
  match pat_exprs with
  | (pat, expr) :: rest -> (
      try
        let l = do_match pat expr' in
        let expr = subst_to_expr expr l in
        match !expr with
        | Ewhen (flag, expr) -> (
            match !(eval flag) with
            | Econstant (Cbool true) -> expr
            | _ -> do_matches rest expr')
        | _ -> expr
      with _ -> do_matches rest expr')
  | [] -> raise (InterpreterError "no matching found")

and eval1 expr =
  match !expr with
  | Evar name -> lookupcontext name
  | Etuple l when not (List.exists (fun x -> isval x) l) ->
      ref (Etuple (List.map eval1 l))
  | Enil -> ref (Elist [])
  | Econs (car, cdr) when not (isval car) -> ref (Econs (eval1 car, cdr))
  | Econs (car, cdr) when not (isval cdr) -> ref (Econs (car, eval1 cdr))
  | Econs (car, { contents = Elist cdr }) -> ref (Elist (car :: cdr))
  | Eref e when isval e -> ref (Eloc (extendstore e))
  | Eref expr -> ref (Eref (eval1 expr))
  | Ederef { contents = Eloc l } -> lookuploc l
  | Ederef expr -> ref (Ederef (eval1 expr))
  | Eassign (lhs, rhs) when not (isval lhs) -> ref (Eassign (eval1 lhs, rhs))
  | Eassign (lhs, rhs) when not (isval rhs) -> ref (Eassign (lhs, eval1 rhs))
  | Eassign ({ contents = Eloc l }, rhs) ->
      updatestore l rhs;
      ref Eunit
  | Econstruct (name, expr) when isval expr -> ref (Econstruct (name, expr))
  | Econstruct (name, expr) -> ref (Econstruct (name, eval1 expr))
  | Eapply (e, l) when not (List.for_all (fun x -> isval x) l) ->
      ref (Eapply (e, List.map (fun e -> eval e) l))
  | Eapply ({ contents = Eprim prim }, [ e ]) when is_unary prim ->
      ref (eval_prim_unary prim e)
  | Eapply ({ contents = Eprim prim }, [ e1; e2 ]) when is_binary prim ->
      ref (eval_prim_binary prim e1 e2)
  | Eapply ({ contents = Eprim prim }, fmt :: args) when is_varargs prim -> (
      match prim with
      | Pprintf ->
          eval_prim_printf
            (!fmt |> get_constant |> get_string)
            (List.map (fun e -> !e) args)
      | Psprintf ->
          eval_prim_sprintf
            (!fmt |> get_constant |> get_string)
            (List.map (fun e -> !e) args)
      | _ -> failwith "niether printf nor sprintf")
  | Eapply
      ({ contents = Efix (({ contents = Efunction _ } as f), pat_exprs') }, el)
    ->
      let f =
        List.fold_left
          (fun f (p, e) ->
            subst_to_expr f (do_match p (ref (Efix (e, pat_exprs')))))
          f pat_exprs'
      in
      ref (Eapply (f, el))
  | Eapply (e, l) when not (isval e) -> ref (Eapply (eval1 e, l))
  | Eapply ({ contents = Efunction pat_exprs }, e :: []) ->
      do_matches pat_exprs e
  | Eapply ({ contents = Efunction pat_exprs }, e :: el) ->
      ref (Eapply (do_matches pat_exprs e, el))
  | Elet (pat_exprs, expr) ->
      List.fold_left
        (fun expr (p, e) -> subst_to_expr expr (do_match p (eval e)))
        expr pat_exprs
  | Eletrec (pat_exprs, expr)
    when not (List.for_all (fun (_, x) -> isval x) pat_exprs) ->
      ref (Eletrec (List.map (fun (p, e) -> (p, eval e)) pat_exprs, expr))
  | Eletrec (pat_exprs, expr) ->
      let expr =
        List.fold_left
          (fun expr (p, e) ->
            let e' = ref (Efix (e, pat_exprs)) in
            subst_to_expr expr (do_match p e'))
          expr pat_exprs
      in
      expr
  | Esequence (lhs, rhs) when not (isval lhs) ->
      ref (Esequence (eval1 lhs, rhs))
  | Esequence ({ contents = Eunit }, rhs) -> rhs
  | Econdition ({ contents = Econstant (Cbool true) }, lhs, _) -> lhs
  | Econdition ({ contents = Econstant (Cbool false) }, _, rhs) -> rhs
  | Econdition (flag, lhs, rhs) -> ref (Econdition (eval1 flag, lhs, rhs))
  | Econstraint (expr, _) -> expr
  | Erecord fields
    when not (List.for_all (fun x -> isval x) (List.map snd fields)) ->
      ref (Erecord (List.map (fun (n, e) -> (n, eval1 e)) fields))
  | Erecord_access (expr, label) when not (isval expr) ->
      ref (Erecord_access (eval1 expr, label))
  | Erecord_access ({ contents = Erecord fields }, label) ->
      List.assoc label fields
  | _ when isval expr -> expr
  | _ -> failwith "eval1"

and eval expr : expr =
  let expr = eval1 expr in
  if isval expr then expr
  else
    try eval expr
    with Failure _ ->
      print_endline (show_expr expr);
      failwith "eval"

let eval_let pat_exprs =
  let ctx =
    List.fold_left
      (fun l (p, e) ->
        l
        @
        let ret = eval e in
        do_match p ret)
      [] pat_exprs
  in
  List.iter (fun (n, v) -> extendcontext n v) ctx;
  ctx

let eval_letrec pat_exprs =
  let ctx =
    List.fold_left
      (fun l (p, e) ->
        l
        @
        let ret = eval e in
        do_match p ret)
      [] pat_exprs
  in
  List.iter (fun (n, v) -> extendcontext n v) ctx;
  ctx
