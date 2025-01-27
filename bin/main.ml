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
    parser := Parser.repl;
    f ())
  else parser := Parser.top

let rec check_ast env = function
  | { ast = Mtype decl; _ } :: rest ->
      let add_env = Sigtype decl :: [] in
      check_valid_decl decl;
      check_recursive_abbrev decl;
      check_recursive_def decl;
      if_debug (fun () -> print_endline (pp_env add_env));
      check_ast (add_env @ env) rest
  | { ast = Mexpr expr; _ } :: rest ->
      let ty = type_expr env 0 expr in
      let expr = eval expr in
      if_debug (fun () ->
          print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_val expr));
      check_ast env rest
  | { ast = Mlet l; _ } :: rest ->
      let add_env = type_let env l in
      List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_let l);
      check_ast add_env rest
  | { ast = Mletrec l; _ } :: rest ->
      let add_env = type_letrec env l in
      List.iter
        (fun (name, expr) ->
          if_debug (fun () ->
              print_endline
                ("val " ^ name ^ " = " ^ pp_val expr ^ " : "
                ^ pp_ty (Option.get (find_val name add_env)))))
        (eval_letrec l);
      check_ast add_env rest
  | { ast = Mopen [ fname ]; _ } :: rest ->
      (*let fname = Filename.basename fname in*)
      if List.mem fname !fnames then check_ast env rest
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
        fnames := fname :: !fnames;
        check_ast (!add_env @ env) rest
  | _ -> env

and interp env defs = check_ast env defs

and do_interp fname inchan env =
  file := fname;
  try
    if_debug (fun () ->
        print_string "# ";
        flush stdout);
    let filebuf = Lexing.from_channel inchan in
    let ast = !parser Lexer.token filebuf in
    let e = interp !env ast in
    env := e
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
