open Extracted

let str l = String.of_seq (List.to_seq l)
let show_exn = function
  | Success n -> Printf.sprintf "success %d" n
  | Exception e -> Printf.sprintf "exception %S" (str e)
let show_list l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"
let check name got expected =
  Printf.printf "%-34s %s\n" name (if got = expected then "ok" else "FAIL: got " ^ got);
  if got <> expected then exit 1

let () =
  (* exceptions *)
  check "collatz_steps 6" (show_exn (collatz_steps_x 6)) "success 8";
  check "collatz_steps 0" (show_exn (collatz_steps_x 0)) "exception \"collatz: zero\"";
  print_endline "all tests passed"
