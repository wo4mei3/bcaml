open Eval
open Syntax
open Typing
open Printer

let is_repl = ref false
let parser = ref Parser.top
let fnames = ref []
let extend_env env add_env = env := add_env @ !env
let restore_env env = env := List.tl !env
let if_is_repl f = if !is_repl then f ()

let rec type_bind_expr env mod_expr =
  match mod_expr.ast with
  | Bexpr expr ->
      let ty = type_expr !env 0 expr in
      if_is_repl (fun () ->
          print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_val (eval expr)));
      [ ("_", AtomSig_value ty) ]
  | Blet l ->
      let add_env = type_let !env l in
      List.iter
        (fun (name, expr) ->
          if_is_repl (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_let l);
      extend_env env add_env;
      add_env
  | Bletrec l ->
      let add_env = type_letrec !env l in
      List.iter
        (fun (name, expr) ->
          if_is_repl (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_letrec l);
      extend_env env add_env;
      add_env
  | Btype decl ->
      let add_env = List.map (fun (n, d) -> (n, AtomSig_type d)) decl in
      check_valid_decl add_env;
      check_recursive_abbrev add_env;
      check_recursive_def add_env;
      if_is_repl (fun () -> print_endline (pp_env add_env));
      extend_env env add_env;
      add_env
  | Bmodule (name, mod_expr) ->
      let atomic_sig = (name, AtomSig_module (type_mod_expr env mod_expr)) in
      extend_env env [ atomic_sig ];
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      [ atomic_sig ]
  | Bsig (name, sig_expr) ->
      let atomic_sig = (name, AtomSig_module (type_sig_expr !env sig_expr)) in
      extend_env env [ atomic_sig ];
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      [ atomic_sig ]
  | Bopen [ fname ] ->
      if List.mem fname !fnames then []
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
        extend_env env !add_env;
        !add_env
  | _ -> []

and type_mod_expr env mod_expr =
  match mod_expr.ast with
  | Mvar name -> access_compound [ name ] (ComSig_struct !env)
  | Maccess (mod_expr, m) -> (
      let l = type_mod_expr env mod_expr in
      match find_mod m (get_struct l) with
      | Some m -> m
      | None -> failwith "type_mod_expr")
  | Mfunctor ((n, sig_expr), ret) ->
      let arg = instantiate_compound (type_sig_expr !env sig_expr) in
      extend_env env [ (n, AtomSig_module arg) ];
      let ret = type_mod_expr env ret in
      restore_env env;
      (*print_endline (show_sema_sig (Sigfun (Sigmod (n, arg), ret)));*)
      ComSig_fun ((n, AtomSig_module arg), ret)
  | Mapply (fct, args) ->
      let fct_sig = type_mod_expr env fct in
      let compound_sig =
        List.fold_left
          (fun fct_sig arg_sig ->
            match fct_sig with
            | ComSig_fun ((_, AtomSig_module param_sig), ret) ->
                compoundsigmatch !env arg_sig param_sig;
                instantiate_compound ret
            | _ -> failwith "type_mod_expr")
          fct_sig
          (List.map (fun arg -> type_mod_expr env arg) args)
      in
      (*print_endline (show_sema_sig sema_sig);*)
      compound_sig
  | Mseal (mod_expr, sig_expr) ->
      let sema_sig = type_mod_expr env mod_expr in
      let seal_sig = type_sig_expr !env sig_expr in
      compoundsigmatch !env sema_sig seal_sig;
      seal_sig
  | Mstruct l ->
      let l =
        List.fold_left
          (fun add_env bind_expr -> type_bind_expr env bind_expr @ add_env)
          [] l
      in
      ComSig_struct l

and interp env defs =
  List.fold_left
    (fun add_env bind_expr -> type_bind_expr env bind_expr @ add_env)
    [] defs

and do_interp fname inchan env =
  file := fname;
  try
    if_is_repl (fun () ->
        print_string "# ";
        flush stdout);
    let filebuf = Lexing.from_channel inchan in
    let ast = !parser Lexer.token filebuf in
    let e = interp env ast in
    env := e @ !env
  with
  (*| InterpreterError msg -> print_endline ("InterpreterError " ^ msg)*)
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
