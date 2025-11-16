(* 最小スモークテスト *)
let test_smoke () = Alcotest.(check bool) "smoke" true true

let () =
  let open Alcotest in
  run "bcaml tests" [
    "basic", [
      test_case "smoke" `Quick test_smoke
    ]
  ]