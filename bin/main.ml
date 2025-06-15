open Eval
open Syntax
open Typing
open Printer

let is_repl = ref false
let parser = ref Parser.top
let fnames = ref []

let if_is_repl f = if !is_repl then f ()

let rec type_bind_expr env mod_expr =
  match mod_expr.ast with
  | Bexpr expr ->
      let ty = type_expr env 0 expr in
      if_is_repl (fun () ->
          print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_val (eval expr)));
      [ ("_", AtomSig_value ty) ], [("_", eval expr)]
  | Blet l ->
      let add_env = type_let env l in
      (*List.iter
        (fun (name, expr) ->
          if_is_repl (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_let l);*)
      add_env, (eval_let l)
  | Bletrec l ->
      let add_env = type_letrec env l in
      (*List.iter
        (fun (name, expr) ->
          if_is_repl (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_letrec l);*)
      add_env,  (eval_letrec l)
  | Btype decl ->
      let add_env = List.map (fun (n, d) -> (n, AtomSig_type d)) decl in
      check_valid_decl add_env;
      check_recursive_abbrev add_env;
      check_recursive_def add_env;
      (*if_is_repl (fun () -> print_endline (pp_ add_env));*)
      add_env,  []
  | Bmodule (name, mod_expr) ->
      let compound_sig, expr = type_mod_expr env mod_expr in
      let atomic_sig = (name, AtomSig_module compound_sig) in
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      [ atomic_sig ], eval_let [{ast = ref(Pvar name);pos=mod_expr.pos}, expr]
  | Bsig (name, sig_expr) ->
      let atomic_sig = (name, AtomSig_module (type_sig_expr env sig_expr)) in
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      [ atomic_sig ], []
  | Bopen [ fname ] ->
      if List.mem fname !fnames then [],[]
      else
        let add_env = ref [] in
        if !is_repl then parser := Parser.top;
        do_interp fname
          (open_file (String.uncapitalize_ascii fname ^ ".bc"))
          add_env;
        if !is_repl then parser := Parser.repl;
        List.iter
          (function
            | name, AtomSig_value ty ->
                if free_type_vars notgeneric ty != [] then
                  failwith
                    (Printf.sprintf
                       "cannot generalize the type of this variable %s %s" name
                       (show_ty ty))
            | _, AtomSig_type _ -> ()
            | _, AtomSig_module _ -> ())
          !add_env;
        (*fnames := fname :: !fnames;*)
        !add_env, []
  | _ -> [],  []

and type_mod_expr env mod_expr =
  match mod_expr.ast with
  | Mvar name -> access_compound [ name ] (ComSig_struct env), eval {ast = ref(Evar name); pos = mod_expr.pos}
  | Maccess (mod_expr, n) -> (
      let l, expr = type_mod_expr env mod_expr in
      match find_mod n (get_struct l) with
      | Some m -> m, eval {ast = ref(Erecord_access(expr, n)); pos = mod_expr.pos}
      | None -> failwith "type_mod_expr")
  | Mfunctor ((n, sig_expr), ret) ->
      let arg = type_sig_expr env sig_expr in
      [ (n, AtomSig_module arg) ] |> show_tyenv |> print_endline;
      let ret, expr = type_mod_expr ((n, AtomSig_module arg) :: env) ret in
      ComSig_fun ((n, AtomSig_module arg), ret), eval {ast = ref(Efunction [{ast=ref(Pvar n);pos=sig_expr.pos}, expr]); pos = mod_expr.pos}
  | Mapply (fct, args) ->
      let fct_sig,fct = type_mod_expr env fct in
      let compound_sig =
        List.fold_left
          (fun fct_sig arg_sig ->
            match fct_sig with
            | ComSig_fun ((_, AtomSig_module param_sig), ret) ->
                compoundsigmatch env arg_sig param_sig;
                instantiate_compound ret
            | _ -> failwith "type_mod_expr")
          fct_sig
          (List.map (fun arg -> fst (type_mod_expr env arg)) args)
      in
      let args = (List.map (fun arg -> snd (type_mod_expr env arg)) args) in
      compound_sig, eval {ast = ref(Eapply (fct,args)); pos = mod_expr.pos}
  | Mseal (mod_expr, sig_expr) ->
      let sema_sig, expr = type_mod_expr env mod_expr in
      let seal_sig = type_sig_expr env sig_expr in
      show_compound_sig sema_sig |> print_endline;
      show_compound_sig seal_sig |> print_endline;
      compoundsigmatch env sema_sig seal_sig;
      seal_sig,expr
  | Mstruct l ->
      let l, ctx =
        List.fold_left_map
          (fun add_env bind_expr -> let new_env, new_ctx = (type_bind_expr (add_env@env) bind_expr) in 
          (new_env, new_ctx))
          [] l
      in
      ComSig_struct l, {ast = ref(Erecord (List.concat ctx)); pos = mod_expr.pos}

and interp env defs =
  List.fold_left
    (fun add_env bind_expr -> (type_bind_expr (add_env@env) bind_expr |> fst) @ add_env)
    [] defs

and do_interp fname inchan env =
  file := fname;
  try
    if_is_repl (fun () ->
        print_string "# ";
        flush stdout);
    let filebuf = Lexing.from_channel inchan in
    let ast = !parser Lexer.token filebuf in
    let e = interp !env ast in
    env := e @ !env
  with
  | InterpreterError msg -> print_endline ("InterpreterError " ^ msg)
  | Failure msg -> print_endline ("Failure " ^ msg)
  | Parser.Error -> print_endline "parser error"
  | Not_found -> print_endline "an unbound variable found"
  | _ -> print_endline "something went wrong"

and open_file fname =
  try open_in fname
  with Sys_error _ -> failwith (Printf.sprintf "file not found %s" fname)

let () =
  let argc = Array.length Sys.argv in
  if argc = 1 then (
    parser := Parser.repl;
    let env = ref [] in
    print_endline "        BCaml a bear's interpreter of caml language";
    print_endline "";
    print_endline "";
    while true do
      is_repl := true;
      do_interp "" stdin env
    done)
  else if argc = 2 then (
    let fname = Sys.argv.(1) in
    is_repl := false;
    do_interp fname (open_file fname) (ref []))
  else (
    Format.printf "Usage: ./bcaml [filename]\n";
    exit (-1))
