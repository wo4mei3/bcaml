(* Resultモナドによるスモールステップ評価（ファイル末尾） *)

open Syntax
(* 例外廃止・Resultモナド徹底 *)

exception InterpreterError of string

let ctx =
  ref
    (List.map
       (fun (n, p) ->
         (n, { ast = ref (Eprim p); pos = (Lexing.dummy_pos, Lexing.dummy_pos) }))
       prim_list)

let extendcontext name v = ctx := (name, v) :: !ctx
let lookupcontext name = List.assoc name !ctx

type store = expr list

let store = ref []


let extendstore v =
  let loc = List.length !store in
  store := !store @ [ v ];
  Ok loc


let lookuploc l =
  try Ok (List.nth !store l) with _ -> Error "lookuploc: out of bounds"


let updatestore n v =
  let (>>=) r f = match r with Ok v -> f v | Error e -> Error e in
  let rec f s =
    match s with
    | 0, _ :: rest -> Ok (v :: rest)
    | n, v' :: rest -> f (n - 1, rest) >>= fun rest' -> Ok (v' :: rest')
    | _ -> Error "updatestore: bad index"
  in
  f (n, !store) >>= fun new_store -> store := new_store; Ok ()

let rec isval expr =
  match !(expr.ast) with
  | Evar _ -> false
  | Econstant _ -> true
  | Eprim Pprintf | Eprim Psprintf -> true
  | Eprim _ -> true
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
  | EBlock1 _ -> false
  | Epath _ -> false


let (>>=) r f = match r with Ok v -> f v | Error e -> Error e

let eval_prim_unary prim x =
  match prim with
  | Pnot -> Ok (do_unary (Ubool_to_bool not) x)
  | Pnegint -> Ok (do_unary (Uint_to_int ( ~- )) x)
  | Plnot -> Ok (do_unary (Uint_to_int lnot) x)
  | Pnegfloat -> Ok (do_unary (Ufloat_to_float ( ~-. )) x)
  | Pintoffloat -> Ok (do_unary (Ufloat_to_int int_of_float) x)
  | Pfloatofint -> Ok (do_unary (Uint_to_float float_of_int) x)
  | Pintofchar -> Ok (do_unary (Uchar_to_int int_of_char) x)
  | Pcharofint -> Ok (do_unary (Uint_to_char char_of_int) x)
  | Pstringofbool -> Ok (do_unary (Ubool_to_string string_of_bool) x)
  | Pboolofstring -> Ok (do_unary (Ustring_to_bool bool_of_string) x)
  | Pstringofint -> Ok (do_unary (Uint_to_string string_of_int) x)
  | Pintofstring -> Ok (do_unary (Ustring_to_int int_of_string) x)
  | Pstringoffloat -> Ok (do_unary (Ufloat_to_string string_of_float) x)
  | Pfloatofstring -> Ok (do_unary (Ustring_to_float float_of_string) x)
  | Pfailwith -> Error (get_string (get_constant !(x.ast)))
  | _ -> Error "eval_prim_unary"


let rec eval_prim_eq x y =
  match (!(x.ast), !(y.ast)) with
  | Econstant l, Econstant r -> Ok (l = r)
  | Etuple l, Etuple r ->
      let rec aux l r =
        match (l, r) with
        | [], [] -> Ok true
        | x::xs, y::ys -> eval_prim_eq x y >>= fun b -> if b then aux xs ys else Ok false
        | _ -> Error "tuple length mismatch"
      in aux l r
  | Elist l, Elist r ->
      let rec aux l r =
        match (l, r) with
        | [], [] -> Ok true
        | x::xs, y::ys -> eval_prim_eq x y >>= fun b -> if b then aux xs ys else Ok false
        | _ -> Error "list length mismatch"
      in aux l r
  | Eloc l, Eloc r -> lookuploc l >>= fun lx -> lookuploc r >>= fun rx -> eval_prim_eq lx rx
  | Etag, Etag -> Ok true
  | Eunit, Eunit -> Ok true
  | Econstruct (ln, l), Econstruct (rn, r) when ln = rn -> eval_prim_eq l r
  | Erecord ls, Erecord rs ->
      let rec aux ls rs =
        match rs with
        | [] -> Ok true
        | (n, e)::rest ->
            (try Ok (List.assoc n ls) with Not_found -> Error "record field not found") >>= fun v ->
            eval_prim_eq v e >>= fun b -> if b then aux ls rest else Ok false
      in aux ls rs
  | Eprim _, Eprim _ -> Error "comparison between functions"
  | Efunction _, Efunction _ -> Error "comparison between functions"
  | _, _ -> Error "eval_prim_eq"


let rec eval_prim_eq_imm x y =
  match (!(x.ast), !(y.ast)) with
  | Econstant l, Econstant r -> Ok (l = r)
  | Etuple l, Etuple r ->
      let rec aux l r =
        match (l, r) with
        | [], [] -> Ok true
        | x::xs, y::ys -> eval_prim_eq_imm x y >>= fun b -> if b then aux xs ys else Ok false
        | _ -> Error "tuple length mismatch"
      in aux l r
  | Elist l, Elist r ->
      let rec aux l r =
        match (l, r) with
        | [], [] -> Ok true
        | x::xs, y::ys -> eval_prim_eq_imm x y >>= fun b -> if b then aux xs ys else Ok false
        | _ -> Error "list length mismatch"
      in aux l r
  | Eloc l, Eloc r -> Ok (l = r)
  | Etag, Etag -> Ok true
  | Eunit, Eunit -> Ok true
  | Econstruct (ln, l), Econstruct (rn, r) when ln = rn -> eval_prim_eq_imm l r
  | Erecord ls, Erecord rs ->
      let rec aux ls rs =
        match rs with
        | [] -> Ok true
        | (n, e)::rest ->
            (try Ok (List.assoc n ls) with Not_found -> Error "record field not found") >>= fun v ->
            eval_prim_eq_imm v e >>= fun b -> if b then aux ls rest else Ok false
      in aux ls rs
  | Eprim _, Eprim _ -> Error "comparison between functions"
  | Efunction _, Efunction _ -> Error "comparison between functions"
  | _, _ -> Error "eval_prim_eq"


let eval_prim_binary prim x y =
  match prim with
  | Peq -> eval_prim_eq x y >>= fun b -> Ok (Econstant (Cbool b))
  | Pnq -> eval_prim_eq x y >>= fun b -> Ok (Econstant (Cbool (not b)))
  | Plt -> Ok (do_binary_eq ( < ) x y)
  | Pgt -> Ok (do_binary_eq ( > ) x y)
  | Ple -> Ok (do_binary_eq ( <= ) x y)
  | Pge -> Ok (do_binary_eq ( >= ) x y)
  | Peqimm -> eval_prim_eq_imm x y >>= fun b -> Ok (Econstant (Cbool b))
  | Pnqimm -> eval_prim_eq_imm x y >>= fun b -> Ok (Econstant (Cbool (not b)))
  | Pand -> Ok (do_binary (Bbool ( && )) x y)
  | Por -> Ok (do_binary (Bbool ( || )) x y)
  | Paddint -> Ok (do_binary (Bint ( + )) x y)
  | Psubint -> Ok (do_binary (Bint ( - )) x y)
  | Pmulint -> Ok (do_binary (Bint ( * )) x y)
  | Pdivint -> Ok (do_binary (Bint ( / )) x y)
  | Pmod -> Ok (do_binary (Bint ( mod )) x y)
  | Pland -> Ok (do_binary (Bint ( land )) x y)
  | Plor -> Ok (do_binary (Bint ( lor )) x y)
  | Plxor -> Ok (do_binary (Bint ( lxor )) x y)
  | Plsl -> Ok (do_binary (Bint ( lsl )) x y)
  | Plsr -> Ok (do_binary (Bint ( lsr )) x y)
  | Pasr -> Ok (do_binary (Bint ( asr )) x y)
  | Paddfloat -> Ok (do_binary (Bfloat ( +. )) x y)
  | Psubfloat -> Ok (do_binary (Bfloat ( -. )) x y)
  | Pmulfloat -> Ok (do_binary (Bfloat ( *. )) x y)
  | Pdivfloat -> Ok (do_binary (Bfloat ( /. )) x y)
  | Ppower -> Ok (do_binary (Bfloat ( ** )) x y)
  | Pconcatstring -> Ok (do_binary (Bstring ( ^ )) x y)
  | Pconcat -> (
      match (!(x.ast), !(y.ast)) with
      | Elist x, Elist y -> Ok (Elist (x @ y))
      | _ -> Error "eval_prim_binary: concat expects lists")
  | _ -> Error "eval_prim_binary: unknown primitive"


let eval_prim_printf fmt args =
  try
    let len = String.length fmt in
    let printf = Printf.printf in
    let rec print i = function
      | arg :: args -> (
          if i >= len then Ok ()
          else
            match fmt.[i] with
            | '%' -> (
                let j = i + 1 in
                match fmt.[j] with
                | '%' -> printf "%%"; print (j + 1) (arg :: args)
                | 's' -> printf "%s" (arg |> get_constant |> get_string); print (j + 1) args
                | 'c' -> printf "%c" (arg |> get_constant |> get_char); print (j + 1) args
                | 'd' | 'o' | 'x' | 'X' | 'u' -> printf "%d" (arg |> get_constant |> get_int); print (j + 1) args
                | 'f' | 'e' | 'E' | 'g' | 'G' -> printf "%f" (arg |> get_constant |> get_float); print (j + 1) args
                | 'b' -> printf "%b" (arg |> get_constant |> get_bool); print (j + 1) args
                | _ -> Error "bad format letter after %")
            | s -> printf "%c" s; print (i + 1) (arg :: args))
      | [] -> if i >= len then Ok () else (printf "%c" fmt.[i]; print (i + 1) [])
    in
    print 0 args >>= fun () -> Ok (ref Eunit)
  with _ -> Error "eval_prim_printf runtime error"


let eval_prim_sprintf fmt args =
  try
    let len = String.length fmt in
    let rec sprint i = function
      | arg :: args -> (
          if i >= len then Ok ""
          else
            match fmt.[i] with
            | '%' -> (
                let j = i + 1 in
                match fmt.[j] with
                | '%' -> sprint (j + 1) (arg :: args) >>= fun s -> Ok ("%" ^ s)
                | 's' -> sprint (j + 1) args >>= fun s -> Ok (Printf.sprintf "%s" (arg |> get_constant |> get_string) ^ s)
                | 'c' -> sprint (j + 1) args >>= fun s -> Ok (Printf.sprintf "%c" (arg |> get_constant |> get_char) ^ s)
                | 'd' | 'o' | 'x' | 'X' | 'u' -> sprint (j + 1) args >>= fun s -> Ok (Printf.sprintf "%d" (arg |> get_constant |> get_int) ^ s)
                | 'f' | 'e' | 'E' | 'g' | 'G' -> sprint (j + 1) args >>= fun s -> Ok (Printf.sprintf "%f" (arg |> get_constant |> get_float) ^ s)
                | 'b' -> sprint (j + 1) args >>= fun s -> Ok (Printf.sprintf "%b" (arg |> get_constant |> get_bool) ^ s)
                | _ -> Error "bad format letter after %")
            | s -> sprint (i + 1) (arg :: args) >>= fun str -> Ok (Printf.sprintf "%c" s ^ str))
      | [] -> if i >= len then Ok "" else sprint (i + 1) [] >>= fun str -> Ok (Printf.sprintf "%c" fmt.[i] ^ str)
    in
    sprint 0 args >>= fun s -> Ok (ref (Econstant (Cstring s)))
  with _ -> Error "eval_prim_sprintf runtime error"

let unique_name = ref 0

let gen_alpha () =
  let name = "Alpha" ^ string_of_int !unique_name in
  unique_name := !unique_name + 1;
  name

let rec collect_pvars pat =
  let aux l =
    match !(pat.ast) with
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

    let rec mapM f l = match l with [] -> Ok [] | x::xs -> f x >>= fun y -> mapM f xs >>= fun ys -> Ok (y::ys) in
    let conv_pat pat table =
      List.fold_left
        (fun acc (name, alpha) ->
          acc >>= fun pat' -> subst_to_pat pat' [ (name, ref (Pvar alpha)) ])
        (Ok pat) table
    in
    let conv_expr expr table =
      List.fold_left
        (fun acc (name, alpha) ->
          acc >>= fun expr' -> subst_to_expr expr' [ (name, ref (Evar alpha)) ])
        (Ok expr) table
    in
    let aux expr (n, e) =
    match !expr with
    | Evar name when n = name -> Ok e
    | Evar _ -> Ok expr
    | Econstant _ | Eprim _ -> Ok expr
    | Etuple el ->
      mapM (fun e -> subst_to_expr e l) el >>= fun el' -> Ok (ref (Etuple el'))
    | Enil -> Ok expr
    | Econs (car, cdr) ->
      subst_to_expr car l >>= fun car' -> subst_to_expr cdr l >>= fun cdr' -> Ok (ref (Econs (car', cdr')))
    | Elist el ->
      mapM (fun e -> subst_to_expr e l) el >>= fun el' -> Ok (ref (Elist el'))
    | Eref e -> subst_to_expr e l >>= fun e' -> Ok (ref (Eref e'))
    | Ederef e -> subst_to_expr e l >>= fun e' -> Ok (ref (Ederef e'))
    | Eassign (lhs, rhs) ->
      subst_to_expr lhs l >>= fun lhs' -> subst_to_expr rhs l >>= fun rhs' -> Ok (ref (Eassign (lhs', rhs')))
    | Eloc _ | Etag | Eunit -> Ok expr
    | Econstruct (t, e) -> subst_to_expr e l >>= fun e' -> Ok (ref (Econstruct (t, e')))
    | Eapply (f, args) ->
      subst_to_expr f l >>= fun f' ->
      mapM (fun e -> subst_to_expr e l) args >>= fun args' -> Ok (ref (Eapply (f', args')))
    | Elet (pe, expr) ->
      let pvars = List.fold_left (fun l (p, _) -> collect_pvars p @ l) [] pe in
      let table = List.map (fun p -> (p, gen_alpha ())) pvars in
      let pe' = List.map (fun (p, e) -> (conv_pat p table, e)) pe in
      conv_expr expr table >>= fun expr' ->
      mapM (fun (p, e) ->
        p >>= fun p' -> subst_to_expr e l >>= fun e' -> Ok (p', e')) pe' >>= fun pe'' ->
      subst_to_expr expr' l >>= fun expr'' -> Ok (ref (Elet (pe'', expr'')))
    | Eletrec (pe, expr) ->
      let pvars = List.fold_left (fun l (p, _) -> collect_pvars p @ l) [] pe in
      let table = List.map (fun p -> (p, gen_alpha ())) pvars in
      let pe' = List.map (fun (p, e) -> (conv_pat p table, conv_expr e table)) pe in
      conv_expr expr table >>= fun expr' ->
      mapM (fun (p, e) ->
        p >>= fun p' -> e >>= fun e' -> subst_to_expr e' l >>= fun e'' -> Ok (p', e'')) pe' >>= fun pe'' ->
      subst_to_expr expr' l >>= fun expr'' -> Ok (ref (Eletrec (pe'', expr'')))
    | Efix _ -> Ok expr
    | Efunction pe ->
      mapM (fun (p,e) -> subst_to_expr e l >>= fun e' -> Ok (p,e')) pe >>= fun pe' -> Ok (ref (Efunction pe'))
    | Esequence (lhs, rhs) ->
      subst_to_expr lhs l >>= fun lhs' -> subst_to_expr rhs l >>= fun rhs' -> Ok (ref (Esequence (lhs', rhs')))
    | Econdition (expr1, expr2, expr3) ->
      subst_to_expr expr1 l >>= fun e1 -> subst_to_expr expr2 l >>= fun e2 -> subst_to_expr expr3 l >>= fun e3 -> Ok (ref (Econdition (e1, e2, e3)))
    | Econstraint (expr, t) -> subst_to_expr expr l >>= fun e' -> Ok (ref (Econstraint (e', t)))
    | Erecord f ->
      mapM (fun (lbl,e) -> subst_to_expr e l >>= fun e' -> Ok (lbl,e')) f >>= fun f' -> Ok (ref (Erecord f'))
    | Erecord_access (e, lbl) -> subst_to_expr e l >>= fun e' -> Ok (ref (Erecord_access (e', lbl)))
    | Ewhen (lhs, rhs) -> subst_to_expr lhs l >>= fun lhs' -> subst_to_expr rhs l >>= fun rhs' -> Ok (ref (Ewhen (lhs', rhs')))
    | EBlock1 expr -> subst_to_expr expr l >>= fun e' -> Ok (ref (EBlock1 e'))
    | Epath _ -> Ok expr
    in
    let rec foldM f acc l = match l with [] -> Ok acc | x::xs -> f acc x >>= fun acc' -> foldM f acc' xs in
    foldM (fun acc x -> aux acc x) expr.ast l >>= fun ast' -> Ok { ast = ast'; pos = expr.pos }


and subst_to_pat pat l =
    let get_name = function
    | { contents = Pvar name } -> Ok name
    | _ -> Error "get_name: not a Pvar"
    in
    let rec mapM f l = match l with [] -> Ok [] | x::xs -> f x >>= fun y -> mapM f xs >>= fun ys -> Ok (y::ys) in
    let aux pat (n, p) =
    match !pat with
    | Pwild -> Ok pat
    | Pvar name when n = name -> Ok p
    | Pvar _ -> Ok pat
    | Pparams pl ->
      mapM (fun p -> subst_to_pat p l) pl >>= fun pl' -> Ok (ref (Pparams pl'))
    | Palias (pat, name) when n = name ->
      subst_to_pat pat l >>= fun pat' -> get_name p >>= fun n' -> Ok (ref (Palias (pat', n')))
    | Palias (pat, name) ->
      subst_to_pat pat l >>= fun pat' -> Ok (ref (Palias (pat', name)))
    | Pconstant _ -> Ok pat
    | Ptuple pl ->
      mapM (fun p -> subst_to_pat p l) pl >>= fun pl' -> Ok (ref (Ptuple pl'))
    | Pnil -> Ok pat
    | Pcons (car, cdr) ->
      subst_to_pat car l >>= fun car' -> subst_to_pat cdr l >>= fun cdr' -> Ok (ref (Pcons (car', cdr')))
    | Pref pat -> subst_to_pat pat l >>= fun pat' -> Ok (ref (Pref pat'))
    | Punit | Ptag -> Ok pat
    | Pconstruct (t, pat) -> subst_to_pat pat l >>= fun pat' -> Ok (ref (Pconstruct (t, pat')))
    | Pconstraint (pat, t) -> subst_to_pat pat l >>= fun pat' -> Ok (ref (Pconstraint (pat', t)))
    | Precord f ->
      mapM (fun (lbl,p) -> subst_to_pat p l >>= fun p' -> Ok (lbl,p')) f >>= fun f' -> Ok (ref (Precord f'))
    in
    let rec foldM f acc l = match l with [] -> Ok acc | x::xs -> f acc x >>= fun acc' -> foldM f acc' xs in
    foldM (fun acc x -> aux acc x) pat.ast l >>= fun ast' -> Ok { ast = ast'; pos = pat.pos }

(*
(fun pat -> expr) expr'
*)

let rec do_match pat expr =
  match (!(pat.ast), !(expr.ast)) with
  | Pwild, _ -> Ok [ ("_", expr) ]
  | Pvar name, _ -> Ok [ (name, expr) ]
  | Pparams (p :: _), _ -> do_match p expr
  | Palias (p, name), _ -> do_match p expr >>= fun l -> Ok ((name, expr) :: l)
  | Pconstant cst1, Econstant cst2 when cst1 = cst2 -> Ok []
  | Ptuple pl, Etuple el ->
    let rec aux acc pl el =
    match (pl, el) with
    | [], [] -> Ok acc
    | p::ps, e::es -> do_match p e >>= fun l -> aux (acc @ l) ps es
    | _ -> Error "tuple length mismatch in do_match"
    in aux [] pl el
  | Pnil, Elist [] -> Ok []
  | Pcons (car, cdr), Elist (e :: el) ->
    do_match car e >>= fun l1 ->
    do_match cdr { ast = ref (Elist el); pos = expr.pos } >>= fun l2 ->
    Ok (l1 @ l2)
  | Pref p, Eloc loc -> lookuploc loc >>= fun v -> do_match p v
  | Punit, Eunit | Ptag, Etag -> Ok []
  | Pconstruct (name1, pat), Econstruct (name2, expr) when name1 = name2 ->
    do_match pat expr
  | Pconstraint (p, _), _ -> do_match p expr
  | Precord pf, Erecord ef ->
    let rec aux acc pf =
    match pf with
    | [] -> Ok acc
    | (lbl, p)::ps ->
      (try Ok (List.assoc lbl ef) with Not_found -> Error "record field not found") >>= fun v ->
      do_match p v >>= fun l -> aux (acc @ l) ps
    in aux [] pf
  | _ -> Error "do_match: pattern match failure"


and do_matches pat_exprs expr' =
  match pat_exprs with
  | (pat, expr) :: rest ->
      do_match pat expr' >>= fun l ->
      let l' = List.map (fun (n, e) -> (n, e.ast)) l in
      subst_to_expr expr l' >>= fun expr_subst ->
      (match !(expr_subst.ast) with
      | Ewhen (flag, expr) ->
          eval1 flag >>= fun flag_v ->
          (match !(flag_v.ast) with
          | Econstant (Cbool true) -> Ok expr
          | _ -> do_matches rest expr')
      | _ -> Ok expr_subst)
  | [] -> Error ("no matching found: " ^ show_expr expr')


and eval1 expr =
  match !(expr.ast) with
  | Evar name -> Ok (lookupcontext name)
  | Etuple l when not (List.exists isval l) ->
    let rec mapM f l = match l with [] -> Ok [] | x::xs -> f x >>= fun y -> mapM f xs >>= fun ys -> Ok (y::ys) in
    mapM eval1 l >>= fun l' -> Ok { ast = ref (Etuple l'); pos = expr.pos }
  | Enil -> Ok { ast = ref (Elist []); pos = expr.pos }
  | Econs (car, cdr) when not (isval car) ->
    eval1 car >>= fun car' -> Ok { ast = ref (Econs (car', cdr)); pos = expr.pos }
  | Econs (car, cdr) when not (isval cdr) ->
    eval1 cdr >>= fun cdr' -> Ok { ast = ref (Econs (car, cdr')); pos = expr.pos }
  | Econs (car, { ast = { contents = Elist cdr }; _ }) ->
    Ok { ast = ref (Elist (car :: cdr)); pos = expr.pos }
  | Eref e when isval e -> extendstore e >>= fun l -> Ok { ast = ref (Eloc l); pos = expr.pos }
  | Eref expr -> eval1 expr >>= fun e' -> Ok { ast = ref (Eref e'); pos = expr.pos }
  | Ederef { ast = { contents = Eloc l }; _ } -> lookuploc l
  | Ederef expr -> eval1 expr >>= fun e' -> Ok { ast = ref (Ederef e'); pos = expr.pos }
  | Eassign (lhs, rhs) when not (isval lhs) ->
    eval1 lhs >>= fun lhs' -> Ok { ast = ref (Eassign (lhs', rhs)); pos = expr.pos }
  | Eassign (lhs, rhs) when not (isval rhs) ->
    eval1 rhs >>= fun rhs' -> Ok { ast = ref (Eassign (lhs, rhs')); pos = expr.pos }
  | Eassign ({ ast = { contents = Eloc l; _; }; _ }, rhs) ->
    updatestore l rhs >>= fun () -> Ok { ast = ref Eunit; pos = expr.pos }
  | Econstruct (name, expr) when isval expr ->
    Ok { ast = ref (Econstruct (name, expr)); pos = expr.pos }
  | Econstruct (name, expr) ->
    eval1 expr >>= fun e' -> Ok { ast = ref (Econstruct (name, e')); pos = expr.pos }
  | Eapply (e, l) when not (List.for_all isval l) ->
    let rec mapM f l = match l with [] -> Ok [] | x::xs -> f x >>= fun y -> mapM f xs >>= fun ys -> Ok (y::ys) in
    mapM eval1 l >>= fun l' -> Ok { ast = ref (Eapply (e, l')); pos = expr.pos }
  | Eapply ({ ast = { contents = Eprim prim }; _ }, [ e ]) when is_unary prim ->
    eval_prim_unary prim e >>= fun v -> Ok { ast = ref v; pos = expr.pos }
  | Eapply ({ ast = { contents = Eprim prim }; _ }, [ e1; e2 ]) when is_binary prim ->
    eval_prim_binary prim e1 e2 >>= fun v -> Ok { ast = ref v; pos = expr.pos }
  | Eapply ({ ast = { contents = Eprim prim }; _ }, fmt :: args) when is_varargs prim ->
    (match prim with
    | Pprintf ->
      eval_prim_printf (!(fmt.ast) |> get_constant |> get_string) (List.map (fun e -> !(e.ast)) args) >>= fun v -> Ok { ast = v; pos = expr.pos }
    | Psprintf ->
      eval_prim_sprintf (!(fmt.ast) |> get_constant |> get_string) (List.map (fun e -> !(e.ast)) args) >>= fun v -> Ok { ast = v; pos = expr.pos }
    | _ -> Error "niether printf nor sprintf")
  | Eapply ({ ast = { contents = Efix (f, pat_exprs'); _; }; _ }, el) ->
    let f' =
      List.fold_left
        (fun acc (p, e) ->
          acc >>= fun f_expr ->
          do_match p { ast = ref (Efix (e, pat_exprs')); pos = expr.pos } >>= fun l ->
          let l' = List.map (fun (n, e) -> (n, e.ast)) l in
          subst_to_expr f_expr l')
        (Ok f)
        pat_exprs'
    in
    f' >>= fun f_expr -> Ok { ast = ref (Eapply (f_expr, el)); pos = expr.pos }
  | Eapply (e, l) when not (isval e) ->
    eval1 e >>= fun e' -> Ok { ast = ref (Eapply (e', l)); pos = expr.pos }
  | Eapply ({ ast = { contents = Efunction pat_exprs }; _ }, e :: []) ->
    do_matches pat_exprs e
  | Eapply ({ ast = { contents = Efunction pat_exprs }; _ }, e :: el) ->
    do_matches pat_exprs e >>= fun v -> Ok { ast = ref (Eapply (v, el)); pos = expr.pos }
  | Elet (pat_exprs, expr) ->
    let rec aux acc = function
      | [] -> Ok acc
      | (p, e)::xs ->
        eval1 e >>= fun v ->
        do_match p v >>= fun l ->
        let l' = List.map (fun (n, e) -> (n, e.ast)) l in
        subst_to_expr acc l' >>= fun acc' -> aux acc' xs
    in
    aux expr pat_exprs
  | Eletrec (pat_exprs, expr) when not (List.for_all (fun (_, x) -> isval x) pat_exprs) ->
    let rec mapM f l = match l with [] -> Ok [] | (p,e)::xs -> eval1 e >>= fun v -> f (p,v) >>= fun y -> mapM f xs >>= fun ys -> Ok (y::ys) in
    mapM (fun (p,v) -> Ok (p,v)) pat_exprs >>= fun pe' -> Ok { ast = ref (Eletrec (pe', expr)); pos = expr.pos }
  | Eletrec (pat_exprs, expr) ->
    let rec aux acc = function
      | [] -> Ok acc
      | (p, e)::xs ->
        let e' = { ast = ref (Efix (e, pat_exprs)); pos = expr.pos } in
        do_match p e' >>= fun l ->
        let l' = List.map (fun (n, e) -> (n, e.ast)) l in
        subst_to_expr acc l' >>= fun acc' -> aux acc' xs
    in
    aux expr pat_exprs
  | Esequence (lhs, rhs) when not (isval lhs) ->
    eval1 lhs >>= fun lhs' -> Ok { ast = ref (Esequence (lhs', rhs)); pos = expr.pos }
  | Esequence ({ ast = { contents = Eunit }; _ }, rhs) -> Ok rhs
  | Econdition ({ ast = { contents = Econstant (Cbool true) }; _ }, lhs, _) -> Ok lhs
  | Econdition ({ ast = { contents = Econstant (Cbool false) }; _ }, _, rhs) -> Ok rhs
  | Econdition (flag, lhs, rhs) ->
    eval1 flag >>= fun flag' -> Ok { ast = ref (Econdition (flag', lhs, rhs)); pos = expr.pos }
  | Econstraint (expr, _) -> Ok expr
  | Erecord fields when not (List.for_all (fun x -> isval x) (List.map snd fields)) ->
    let rec mapM f l = match l with [] -> Ok [] | (n,e)::xs -> eval1 e >>= fun v -> mapM f xs >>= fun ys -> Ok ((n,v)::ys) in
    mapM (fun (n,e) -> eval1 e >>= fun v -> Ok (n,v)) fields >>= fun fields' -> Ok { ast = ref (Erecord fields'); pos = expr.pos }
  | Erecord_access (expr, label) when not (isval expr) ->
    eval1 expr >>= fun expr' -> Ok { ast = ref (Erecord_access (expr', label)); pos = expr.pos }
  | Erecord_access ({ ast = { contents = Erecord fields }; _ }, label) ->
    (try Ok (List.assoc label fields) with Not_found -> Error "record field not found")
  | EBlock1 expr -> Ok expr
  | Epath (s :: l, name) ->
    (try Ok (List.assoc s !ctx) with Not_found -> Error "path not found") >>= fun expr0 ->
    let rec aux acc = function
    | [] -> Ok acc
    | label::ls -> Ok { ast = ref (Erecord_access (acc, label)); pos = expr.pos } >>= fun acc' -> aux acc' ls
    in
    aux expr0 l >>= fun expr' -> Ok { ast = ref (Erecord_access (expr', name)); pos = expr.pos }
  | _ when isval expr -> Ok expr
  | _ -> Error (show_position expr.pos)


and eval expr : (expr, string) result =
  eval1 expr >>= fun expr' ->
  if isval expr' then Ok expr'
  else eval expr'
(*and (>>=) r f = match r with Ok v -> f v | Error e -> Error e

and eval1_result expr : (expr, string) result =
  match !(expr.ast) with
  | Evar name ->
    (try Ok (lookupcontext name)
     with Not_found -> Error ("unbound variable: " ^ name))
  | Etuple l when not (List.exists isval l) ->
    let rec eval_list acc = function
    | [] -> Ok (List.rev acc)
    | x::xs -> eval1_result x >>= fun v -> eval_list (v::acc) xs
    in
    eval_list [] l >>= fun l' ->
    Ok { ast = ref (Etuple l'); pos = expr.pos }
  | Enil -> Ok { ast = ref (Elist []); pos = expr.pos }
  | Econs (car, cdr) when not (isval car) ->
    eval1_result car >>= fun car' ->
    Ok { ast = ref (Econs (car', cdr)); pos = expr.pos }
  | Econs (car, cdr) when not (isval cdr) ->
    eval1_result cdr >>= fun cdr' ->
    Ok { ast = ref (Econs (car, cdr')); pos = expr.pos }
  | Econs (car, { ast = { contents = Elist cdr }; _ }) ->
    Ok { ast = ref (Elist (car :: cdr)); pos = expr.pos }
  | Eref e when isval e -> Ok { ast = ref (Eloc (extendstore e)); pos = expr.pos }
  | Eref expr -> eval1_result expr >>= fun e' -> Ok { ast = ref (Eref e'); pos = expr.pos }
  | Ederef { ast = { contents = Eloc l }; _ } -> Ok (lookuploc l)
  | Ederef expr -> eval1_result expr >>= fun e' -> Ok { ast = ref (Ederef e'); pos = expr.pos }
  | Eassign (lhs, rhs) when not (isval lhs) ->
    eval1_result lhs >>= fun lhs' -> Ok { ast = ref (Eassign (lhs', rhs)); pos = expr.pos }
  | Eassign (lhs, rhs) when not (isval rhs) ->
    eval1_result rhs >>= fun rhs' -> Ok { ast = ref (Eassign (lhs, rhs')); pos = expr.pos }
  | Eassign ({ ast = { contents = Eloc l }; _ }, rhs) ->
    updatestore l rhs;
    Ok { ast = ref Eunit; pos = expr.pos }
  | Econstruct (name, e) when isval e -> Ok { ast = ref (Econstruct (name, e)); pos = expr.pos }
  | Econstruct (name, e) -> eval1_result e >>= fun e' -> Ok { ast = ref (Econstruct (name, e')); pos = expr.pos }
  | Eapply (e, l) when not (List.for_all isval l) ->
    let rec eval_args acc = function
    | [] -> Ok (List.rev acc)
    | x::xs -> eval_result x >>= fun v -> eval_args (v::acc) xs
    and eval_result e = eval1_result e >>= fun v -> if isval v then Ok v else Error "not a value"
    in
    eval_args [] l >>= fun l' -> Ok { ast = ref (Eapply (e, l')); pos = expr.pos }
  | _ when isval expr -> Ok expr
  | _ -> Error ("no rule applies at: " ^ show_expr expr)
  
*)

let eval_let pat_exprs =
  let rec aux acc = function
    | [] -> Ok acc
    | (p, e)::xs ->
        eval e >>= fun v ->
        do_match p v >>= fun l ->
        Ok (l @ acc) >>= fun acc' -> aux acc' xs
  in
  aux [] pat_exprs >>= fun ctx ->
  List.iter (fun (n, v) -> extendcontext n v) ctx;
  Ok ctx


let eval_letrec pat_exprs =
  let rec aux acc = function
    | [] -> Ok acc
    | (p, e)::xs ->
        eval e >>= fun v ->
        do_match p v >>= fun l ->
        Ok (l @ acc) >>= fun acc' -> aux acc' xs
  in
  aux [] pat_exprs >>= fun ctx ->
  List.iter (fun (n, v) -> extendcontext n v) ctx;
  Ok ctx
