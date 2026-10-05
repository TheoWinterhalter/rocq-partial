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
  (* plain recursion *)
  check "collatz_len 27" (string_of_int (collatz_len_x 27)) "111";
  (* exceptions *)
  check "collatz_steps 6" (show_exn (collatz_steps_x 6)) "success 8";
  check "collatz_steps 0" (show_exn (collatz_steps_x 0)) "exception \"collatz: zero\"";
  (* state *)
  let (steps, trace) = collatz_trace_x 6 [] in
  check "collatz_trace 6 (result)" (string_of_int steps) "8";
  check "collatz_trace 6 (state)" (show_list trace) "[1;2;4;8;16;5;10;3;6]";
  let (m, ticks) = collatz_max_x 27 0 in
  check "collatz_max 27 (max)" (string_of_int m) "9232";
  check "collatz_max 27 (ticks)" (string_of_int ticks) "112";
  let (r, s) = sum_lens_x 10 0 in
  check "sum_lens 10 (result)" (string_of_int r) "67";
  check "sum_lens 10 (state)" (string_of_int s) "67";
  print_endline "all tests passed"
