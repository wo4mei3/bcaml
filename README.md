# bcaml
Usage

```bash
$ dune exec bin/main.exe
```

Result

```
        BCaml a bear's interpreter of caml language


# 5;;
- : int = 5
# type 'a tree =
| Node of 'a tree ref * 'a tree ref
| Leaf of 'a
;;

type 'a tree = | Node of ('a tree ref * 'a tree ref)  | Leaf of 'a
# Node(ref (Leaf 3), ref (Leaf 5));;
- : int tree = Node (ref Leaf 3, ref Leaf 5)
# type 'a option =
| Some of 'a
| None
;;


type 'a option = | Some of 'a | None
#
(function
| Some a when a = 5 -> true
| None -> failwith "None") (Some 5);;
- : bool = true
# type 'a x = {name:string;data:'a};;

type 'a x = {name : string; data : 'a}
# {name="a";data=0};;
- : int x = {data = 0; name = "a"}
# let x::xl = [5;6];;
val x = 5 : int
val xl = [6] : int list
# let rec gcd m n =
  if m = 0 then n else
  if m <= n then gcd m (n-m) else
  gcd n (m-n)
  in gcd 21600 337500;;
- : int = 2700
#
```