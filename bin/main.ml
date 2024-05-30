open Def
open Eval
open Syntax
open Typing
open Printer

let debug = ref false
let parser = ref Parser.top
let fnames = ref []

let if_debug f =
  if !debug then (
    parser := Parser.def;
    f ())
  else parser := Parser.top

let rec check_ast env decls = function
  | { ast = Deftype decl; _ } :: rest ->
      check_valid_decl decl;
      check_recursive_abbrev decl;
      check_recursive_def decl;
      if_debug (fun () -> print_endline (pp_decls decl));
      check_ast env (decl @ decls) rest
  | { ast = Defexpr expr; _ } :: rest ->
      let ty = type_expr env decls 0 expr in
      let expr = eval expr in
      if_debug (fun () ->
          print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_exp expr));
      check_ast env decls rest
  | { ast = Deflet l; _ } :: rest ->
      let add_env = type_let env decls l in
      List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_exp expr ^ " : "
                ^ pp_ty (List.assoc name add_env))))
        (eval_let l);
      check_ast (add_env @ env) decls rest
  | { ast = Defletrec l; _ } :: rest ->
      let add_env = type_letrec env decls l in
      List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_exp expr ^ " : "
                ^ pp_ty (List.assoc name add_env))))
        (eval_letrec l);
      check_ast (add_env @ env) decls rest
  | { ast = Defopen fname; _ } :: rest ->
      let fname = Filename.basename fname in
      if List.mem fname !fnames then check_ast env decls rest
      else
        let add_env, add_decls = (ref [], ref []) in
        debug := false;
        do_interp fname (open_file fname) add_env add_decls;
        List.iter
          (fun (name, ty) ->
            if free_type_vars notgeneric ty != [] then
              failwith
                (Printf.sprintf "cannot generalize the type of this variable %s"
                   name))
          !add_env;
        fnames := fname :: !fnames;
        check_ast (!add_env @ env) (!add_decls @ decls) rest
  | [] -> (env, decls)

and interp env defs = check_ast env defs

and do_interp fname inchan env decls =
  file := fname;
  try
    if_debug (fun () ->
        print_string "# ";
        flush stdout);
    let filebuf = Lexing.from_channel inchan in
    let ast = !parser Lexer.token filebuf in
    let e, d = interp !env !decls ast in
    env := e;
    decls := d
  with
  | InterpreterError msg -> print_endline ("InterpreterError " ^ msg)
  | Failure msg -> print_endline msg
  | Parser.Error -> print_endline "parser error"
  | Not_found -> print_endline "an unbound variable found"
  | _ -> print_endline "something went wrong"

and open_file fname =
  try open_in fname
  with Sys_error _ -> failwith (Printf.sprintf "file not found %s" fname)

let () =
  let argc = Array.length Sys.argv in
  if argc = 1 then (
    let env = ref [] in
    let decls = ref [] in
    print_endline "        BCaml a bear's interpreter of caml language";
    print_endline "";
    print_endline "";
    while true do
      debug := true;
      do_interp "" stdin env decls
    done)
  else if argc = 2 then (
    let fname = Sys.argv.(1) in
    debug := false;
    ignore (do_interp fname (open_file fname) (ref []) (ref [])))
  else (
    Format.printf "Usage: ./bcaml [filename]\n";
    exit (-1))
