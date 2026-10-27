open Bcaml__Eval
open Bcaml__Typing
open Bcaml__Syntax
open Bcaml__Printer

let is_repl = ref false
let parser = ref Bcaml__Parser.top
let fnames = ref []
let if_is_repl f = if !is_repl then f ()

let rec typing_decl_expr env decl_expr =
  match decl_expr.ast with
  | Dval (name, ty) -> [ (name, AtomSig_value (expand_abbrev env ty)) ]
  | Dtype decl ->
      let decl = List.map (fun (n, d) -> (n, AtomSig_type d)) decl in
      decl
  | Dmodule (name, sig_expr) ->
      [ (name, AtomSig_module (typing_sig_expr env sig_expr)) ]
  | Dsig (name, sig_expr) ->
      [ (name, AtomSig_module (typing_sig_expr env sig_expr)) ]
  | Dinclude path ->
      let compound_sig = access_compound path (ComSig_struct env) in
      get_struct compound_sig

and typing_sig_expr env sig_expr =
  match sig_expr.ast with
  | Svar name ->
      let compound_sig = access_compound [ name ] (ComSig_struct env) in
      instantiate_compound compound_sig
  | Sfunctor ((name, arg), ret) ->
      let arg = typing_sig_expr env arg in
      let ret = typing_sig_expr ((name, AtomSig_module arg) :: env) ret in
      ComSig_fun ((name, AtomSig_module arg), ret)
  | Sstruct l ->
      let l =
        List.fold_left
          (fun add_env decl_expr ->
            let new_env = typing_decl_expr (add_env @ env) decl_expr in
            new_env @ add_env)
          [] l
      in
      ComSig_struct l
  | Swith (sig_expr, l) -> (
      let sema_sig = typing_sig_expr env sig_expr in
      let f (n, decl) =
        match find_type n (get_struct sema_sig) with
        | Some decl' ->
            let tyl, ty = type_of_decl' decl
            and tyl', ty' = type_of_decl' decl' in
            type_match_list env tyl tyl' |> ignore;
            type_match env ty ty' |> ignore
        | None -> failwith "typing_sig_expr"
      in
      List.iter f l;
      let replace_type (name, decl) =
        match decl.ast with
        | TDabbrev (_, params, ty) ->
            ( name,
              AtomSig_type { ast = TDabbrev (name, params, ty); pos = decl.pos }
            )
        | _ ->
            failwith "typing_sig_expr: type constraint must be an abbreviation"
      in
      let constrained_types =
        List.map (fun (name, decl) -> (name, replace_type (name, decl))) l
      in
      match sema_sig with
      | ComSig_struct fields ->
          let fields =
            List.map
              (fun (name, atomic_sig) ->
                match List.assoc_opt name constrained_types with
                | Some (_, replacement) -> (name, replacement)
                | None -> (name, atomic_sig))
              fields
          in
          ComSig_struct fields
      | _ -> sema_sig)

let rec typing_bind_expr env mod_expr =
  match mod_expr.ast with
  | Bexpr expr ->
      let ty = type_expr env 0 expr in
      ([ ("_", AtomSig_value ty) ], Some ty)
  | Blet l ->
      let add_env = type_let env l in
      (add_env, None)
  | Bletrec l ->
      let add_env = type_letrec env l in
      (add_env, None)
  | Btype decl ->
      let add_env = List.map (fun (n, d) -> (n, AtomSig_type d)) decl in
      check_valid_decl (add_env @ env);
      check_recursive_abbrev (add_env @ env);
      check_recursive_def (add_env @ env);
      (*if_is_repl (fun () -> print_endline (pp_ add_env));*)
      (add_env, None)
  | Bmodule (name, mod_expr) ->
      let compound_sig = typing_mod_expr env mod_expr in
      let atomic_sig = (name, AtomSig_module compound_sig) in
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      ([ atomic_sig ], None)
  | Bsig (name, sig_expr) ->
      let atomic_sig = (name, AtomSig_module (typing_sig_expr env sig_expr)) in
      if_is_repl (fun () -> print_endline (pp_atomic_sig atomic_sig));
      ([ atomic_sig ], None)
  | Bopen [ fname ] ->
      if List.mem fname !fnames then ([], None)
      else
        let add_env = ref [] in
        if !is_repl then parser := Bcaml__Parser.top;
        let inchan = open_file (String.uncapitalize_ascii fname ^ ".bc") in
        let completed = do_interp fname inchan add_env in
        close_in inchan;
        if not completed then failwith ("failed to open " ^ fname);
        if !is_repl then parser := Bcaml__Parser.repl;
        (* fnames := fname :: !fnames; *)
        (!add_env, None)
  | _ -> ([], None)

and typing_mod_expr env mod_expr =
  match mod_expr.ast with
  | Mvar name -> access_compound [ name ] (ComSig_struct env)
  | Maccess (mod_expr, n) -> (
      let l = typing_mod_expr env mod_expr in
      match find_mod n (get_struct l) with
      | Some m -> m
      | None -> failwith "typing_mod_expr")
  | Mfunctor ((n, sig_expr), ret) ->
      let arg = typing_sig_expr env sig_expr in
      let ret = typing_mod_expr ((n, AtomSig_module arg) :: env) ret in
      ComSig_fun ((n, AtomSig_module arg), ret)
  | Mapply (fct, args) ->
      let fct_sig = typing_mod_expr env fct in
      let compound_sig =
        List.fold_left
          (fun fct_sig arg ->
            let arg_sig = typing_mod_expr env arg in
            match fct_sig with
            | ComSig_fun ((name, AtomSig_module param_sig), ret) ->
                let ls =
                  compound_sig_match
                    ((name, AtomSig_module arg_sig) :: env)
                    arg_sig param_sig
                in
                List.iter
                  (fun ({ contents = { link; _ } } as x) ->
                    x := { link; abstract = false })
                  ls;
                ret
            | _ -> failwith "typing_mod_expr")
          fct_sig args
      in
      compound_sig
  | Mseal (mod_expr, sig_expr) ->
      let sema_sig = typing_mod_expr env mod_expr in
      let seal_sig = typing_sig_expr env sig_expr in
      let save_sig = instantiate_compound seal_sig in
      compound_sig_match env sema_sig seal_sig |> ignore;
      save_sig
  | Mstruct l ->
      let l, _ =
        List.fold_left_map
          (fun add_env bind_expr ->
            let new_env, _ = typing_bind_expr (add_env @ env) bind_expr in
            (new_env @ add_env, ()))
          [] l
      in
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
        l;
      ComSig_struct l

and eval_bind_expr mod_expr =
  match mod_expr.ast with
  | Bexpr expr ->
      let ret = eval expr in
      [ ("_", ret) ]
  | Blet l -> eval_let l
  | Bletrec l ->
      let ret = eval_letrec l in
      List.iter
        (fun (name, expr) ->
          if_is_repl (fun () ->
              print_endline ("val " ^ name ^ " = " ^ pp_val expr)))
        ret;
      ret
  | Bmodule (name, mod_expr) ->
      let expr = eval_mod_expr mod_expr in
      eval_let [ ({ ast = ref (Pvar name); pos = mod_expr.pos }, expr) ]
  | Bopen [ fname ] -> if List.mem fname !fnames then [] else []
  | _ -> []

and eval_mod_expr mod_expr =
  match mod_expr.ast with
  | Mvar name -> { ast = ref (Evar name); pos = mod_expr.pos }
  | Maccess (mod_expr, n) ->
      eval
        {
          ast = ref (Erecord_access (eval_mod_expr mod_expr, n));
          pos = mod_expr.pos;
        }
  | Mfunctor ((n, sig_expr), ret) ->
      {
        ast =
          ref
            (Efunction
               [
                 ({ ast = ref (Pvar n); pos = sig_expr.pos }, eval_mod_expr ret);
               ]);
        pos = mod_expr.pos;
      }
  | Mapply (fct, args) ->
      let args = List.map eval_mod_expr args in
      { ast = ref (Eapply (eval_mod_expr fct, args)); pos = mod_expr.pos }
  | Mseal (mod_expr, _) -> eval_mod_expr mod_expr
  | Mstruct l ->
      let rec pattern_names pat =
        match !(pat.ast) with
        | Pvar name -> [ name ]
        | Pparams pats | Ptuple pats ->
            List.concat (List.map pattern_names pats)
        | Palias (pat, name) -> name :: pattern_names pat
        | Pconstruct (_, pat) | Pconstraint (pat, _) | Pref pat ->
            pattern_names pat
        | Precord fields ->
            List.concat (List.map (fun (_, pat) -> pattern_names pat) fields)
        | Pcons (lhs, rhs) -> pattern_names lhs @ pattern_names rhs
        | _ -> []
      in
      let fields =
        List.concat
          (List.map
             (fun bind_expr ->
               match bind_expr.ast with
               | Blet bindings | Bletrec bindings ->
                   List.concat
                     (List.map
                        (fun (pat, _) ->
                          List.map
                            (fun name ->
                              (name, { ast = ref (Evar name); pos = pat.pos }))
                            (pattern_names pat))
                        bindings)
               | Bmodule (name, _) ->
                   [ (name, { ast = ref (Evar name); pos = bind_expr.pos }) ]
               | _ -> [])
             l)
      in
      let rec build = function
        | [] -> { ast = ref (Erecord fields); pos = mod_expr.pos }
        | bind_expr :: rest -> (
            let body = build rest in
            match bind_expr.ast with
            | Blet bindings ->
                { ast = ref (Elet (bindings, body)); pos = bind_expr.pos }
            | Bletrec bindings ->
                { ast = ref (Eletrec (bindings, body)); pos = bind_expr.pos }
            | Bmodule (name, module_expr) ->
                {
                  ast =
                    ref
                      (Elet
                         ( [
                             ( { ast = ref (Pvar name); pos = bind_expr.pos },
                               eval_mod_expr module_expr );
                           ],
                           body ));
                  pos = bind_expr.pos;
                }
            | Bexpr expr ->
                { ast = ref (Esequence (expr, body)); pos = bind_expr.pos }
            | _ -> body)
      in
      build l

and interp env defs =
  List.fold_left
    (fun add_env bind_expr ->
      let new_env, ty = typing_bind_expr (add_env @ env) bind_expr in
      let values = eval_bind_expr bind_expr in
      (match (bind_expr.ast, ty, values) with
      | Bexpr _, Some ty, [ ("_", ret) ] ->
          if_is_repl (fun () ->
              print_endline ("- : " ^ pp_ty ty ^ " = " ^ pp_val ret))
      | _ -> ());
      new_env @ add_env)
    [] defs

and do_interp fname inchan env =
  file := fname;
  try
    if_is_repl (fun () ->
        print_string "# ";
        flush stdout);
    let filebuf = Lexing.from_channel inchan in
    let ast = !parser Bcaml__Lexer.token filebuf in
    let e = interp !env ast in
    env := e @ !env;
    true
  with
  | End_of_file -> false
  | InterpreterError msg ->
      print_endline ("InterpreterError " ^ msg);
      true
  | Failure msg ->
      print_endline ("Failure " ^ msg);
      true
  | Bcaml__Parser.Error ->
      print_endline "parser error";
      false
  | Not_found ->
      print_endline "an unbound variable found";
      true
  | _ ->
      print_endline "something went wrong";
      true

and open_file fname =
  try open_in fname
  with Sys_error _ -> failwith (Printf.sprintf "file not found %s" fname)

let () =
  let argc = Array.length Sys.argv in
  if argc = 1 then (
    parser := Bcaml__Parser.repl;
    let env = ref [] in
    is_repl := true;
    print_endline "        BCaml a bear's interpreter of caml language";
    print_endline "";
    print_endline "";
    while do_interp "" stdin env do
      ()
    done)
  else if argc = 2 then (
    let fname = Sys.argv.(1) in
    is_repl := false;
    let inchan = open_file fname in
    let completed = do_interp fname inchan (ref []) in
    close_in inchan;
    if not completed then exit 1)
  else (
    Format.printf "Usage: ./bcaml [filename]\n";
    exit (-1))
