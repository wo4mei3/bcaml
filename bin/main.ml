(*open Eval*)
open Syntax
open Typing
open Printer

let debug = ref false
let parser = ref Parser.top
let fnames = ref []
let extend_env env add_env = env := add_env @ !env
let restore_env env = env := List.tl !env

let if_debug f =
  if !debug then (
    parser := Parser.repl;
    f ())
  else parser := Parser.top

let rec type_mod_expr env mod_expr =
  match mod_expr.ast with
  | Mvar name -> access_sig [ name ] (Sigstruct !env)
  | Mexpr expr ->
      let ty = type_expr !env 0 expr in
      (*if_debug (fun () ->
          print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_val expr));*)
      Sigval ("_", ty)
  | Mlet l ->
      let add_env = type_let !env l in
      (*List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_let l);*)
      extend_env env add_env;
      Sigstruct add_env
  | Mletrec l ->
      let add_env = type_letrec !env l in
      (*List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_letrec l);*)
      extend_env env add_env;
      Sigstruct add_env
  | Mtype decl ->
      let add_env = Sigtype decl :: [] in
      check_valid_decl decl;
      check_recursive_abbrev decl;
      check_recursive_def decl;
      if_debug (fun () -> print_endline (pp_env add_env));
      extend_env env add_env;
      Sigstruct add_env
  | Maccess (mod_expr, m) -> (
      let l = type_mod_expr env mod_expr in
      match find_mod m [ l ] with
      | Some m -> m
      | None -> failwith "type_mod_expr")
  | Mfunctor ((n, sig_expr), ret) ->
      let arg = instantiate_sema_sig (type_sig_expr !env sig_expr) in
      extend_env env [ Sigmod (n, arg) ];
      let ret = type_mod_expr env ret in
      restore_env env;
      (*print_endline (show_sema_sig (Sigfun (Sigmod (n, arg), ret)));*)
      Sigfun (Sigmod (n, arg), ret)
  | Mapply (fct, args) ->
      let fct_sig = type_mod_expr env fct in
      let sema_sig =
        List.fold_left
          (fun fct_sig arg_sig ->
            match fct_sig with
            | Sigfun (param_sig, ret) ->
                sigmatch !env [ arg_sig ] [ param_sig ];
                instantiate_sema_sig ret
            | _ -> failwith "type_mod_expr")
          fct_sig
          (List.map (fun arg -> type_mod_expr env arg) args)
      in
      (*print_endline (show_sema_sig sema_sig);*)
      sema_sig
  | Mseal (mod_expr, sig_expr) ->
      let sema_sig = type_mod_expr env mod_expr in
      let seal_sig = type_sig_expr !env sig_expr in
      sigmatch !env [ sema_sig ] [ seal_sig ];
      seal_sig
  | Mstruct l ->
      let l =
        List.fold_left
          (fun add_env mod_expr -> type_mod_expr env mod_expr :: add_env)
          [] l
      in
      Sigstruct l
  | Mmodule (name, mod_expr) ->
      let sema_sig = Sigmod (name, type_mod_expr env mod_expr) in
      extend_env env [ sema_sig ];
      sema_sig
  | Msig (name, sig_expr) ->
      let sema_sig = Sigmod (name, type_sig_expr !env sig_expr) in
      extend_env env [ sema_sig ];
      sema_sig
  | Mopen [ fname ] ->
      if List.mem fname !fnames then Sigstruct []
      else
        let add_env = ref [] in
        debug := false;
        do_interp fname
          (open_file (String.uncapitalize_ascii fname ^ ".bc"))
          add_env;
        List.iter
          (function
            | Sigtype _ -> ()
            | Sigval (name, ty) ->
                if free_type_vars notgeneric ty != [] then
                  failwith
                    (Printf.sprintf
                       "cannot generalize the type of this variable %s %s" name
                       (show_ty ty))
            | Sigmod _ -> ()
            | Sigfun _ -> ()
            | Sigstruct _ -> ())
          !add_env;
        (*fnames := fname :: !fnames;*)
        extend_env env !add_env;
        Sigstruct !add_env
  | _ -> Sigstruct []

and interp env defs =
  type_mod_expr env
    { ast = Mstruct defs; pos = (Lexing.dummy_pos, Lexing.dummy_pos) }

and do_interp fname inchan env =
  file := fname;
  (*try*)
  if_debug (fun () ->
      print_string "# ";
      flush stdout);
  let filebuf = Lexing.from_channel inchan in
  let ast = !parser Lexer.token filebuf in
  let e = interp env ast in
  env := e :: !env
(*with
  | InterpreterError msg -> print_endline ("InterpreterError " ^ msg)
  | Failure msg -> print_endline ("Failure " ^ msg)
  | Parser.Error -> print_endline "parser error"
  | Not_found -> print_endline "an unbound variable found"
  | _ -> print_endline "something went wrong"*)

and open_file fname =
  try open_in fname
  with Sys_error _ -> failwith (Printf.sprintf "file not found %s" fname)

let () =
  let argc = Array.length Sys.argv in
  if argc = 1 then (
    let env = ref [] in
    print_endline "        BCaml a bear's interpreter of caml language";
    print_endline "";
    print_endline "";
    while true do
      debug := true;
      do_interp "" stdin env
    done)
  else if argc = 2 then (
    let fname = Sys.argv.(1) in
    debug := false;
    do_interp fname (open_file fname) (ref []))
  else (
    Format.printf "Usage: ./bcaml [filename]\n";
    exit (-1))
