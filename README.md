# Bcaml

## 1. Project Overview

Bcaml is an interpreter for the Bcaml language implemented in OCaml.  
This project was created primarily to deepen my understanding of functional programming.


## 2. Features

- Bcaml language interpreter  
- Robust implementation using OCaml  
- Evaluation based on Abstract Syntax Trees (AST)  
- Module system  
- Support for Signatures  
- Support for Functors  
- Basic data types (integers, booleans, etc.)  
- Algebraic Data Types  
- Pattern Matching  
- Lists  
- Mutable References (similar to OCaml's `ref`)  
- Let bindings, function definitions and applications, conditional expressions (if)  
- Arithmetic and comparison operators  


## 3. Getting Started

### Prerequisites

To build and run Bcaml, the following software is required:

- OCaml (recommended version: 4.14.0 or later)  
- Dune (recommended version: 3.0 or later)

### Building Bcaml

```sh
git clone https://github.com/Wo4mei3/bcaml.git
cd bcaml
dune build
```

The executable for the Bcaml interpreter will typically be located at `_build/default/bin/main.exe`.


## 4. Running Bcaml Code

To run Bcaml code with the built interpreter, provide a `.bc` source file as an argument.

```sh
./_build/default/bin/main.exe <your_source_file.bc>
```

### Example:

To run `examples/hello.bc` from the repository:

```sh
$ cat examples/hello.bc
module Hello = struct
    let message = "Hello,"
    let hello () = printf "%s" message
end

let () = Hello.hello ()

module type Hello_Sig = sig
      val hello: unit -> unit
end

module Hello2 : Hello_Sig = Hello

module Hello3 : Hello_Sig = struct
    let hello () = printf "%s" "Hello3!"
end

module type AbstTypeSig = sig
    type t
    val get_t : int -> t
    val print : t -> unit
end

module AbstTypeInt : AbstTypeSig = struct
    type t = int
    let get_t i = i
    let print t = printf " world! %d\n" t
end

let t = AbstTypeInt.get_t 0
(*let () = printf "%d" t*)
let () = AbstTypeInt.print t

$ ./_build/default/bin/main.exe examples/hello.bc
Hello, world! 0
```


## 5. Examples

The `examples/` directory contains several sample programs written in Bcaml.  
You can run these to verify the behavior of the interpreter.


## 6. About the Bcaml Language

The Bcaml language is based on the core computation features of ML-style languages.  
One of its most notable aspects is the implementation of advanced abstraction mechanisms such as modules, signatures, and functors at the language level, inspired by OCaml.

Additionally, it supports expressive features such as algebraic data types, pattern matching, and mutable references, which are valuable for understanding structured code, code reuse, and large-scale design patterns.


## 7. Future Enhancements - Potential Areas for Growth

Bcaml already provides rich features. To go beyond the learning purpose and improve usability and developer experience, the following areas can be enhanced:

- I/O: Extending standard input/output and adding file I/O will allow Bcaml programs to interact with the external environment.  
- Error Handling: Implementing exception mechanisms (such as `try...with`) at the language level will enable more robust error management. Improving clarity and detail of error messages is also beneficial.  
- Standard Library: Adding more built-in data structures (e.g., arrays, hash tables, sets) and comprehensive string manipulation functions will make Bcaml more versatile.  
- Developer Tools: Although REPL is available, tools such as debuggers, linters/formatters, and package managers can greatly improve the development workflow.


## 8. License

This project is licensed under the GPLv2.0.  
Please refer to the `LICENCE` file for more details.


## 9. Contact

If you have any questions or issues, please use the GitHub Issues page.