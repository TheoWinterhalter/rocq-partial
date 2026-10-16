open Extracted

let show_exn show = function
  | Success x -> "success " ^ show x
  | Exception e -> "exception \"" ^ e ^ "\""

let rec show_ty = function
  | Bool -> "bool"
  | Arr (a, b) -> Printf.sprintf "(%s -> %s)" (show_ty a) (show_ty b)

let rec fin_to_int = function
  | F0 _ -> 0
  | FS (_, f) -> 1 + fin_to_int f

let show_unit () = "tt"
let show_fin f = string_of_int (fin_to_int f)

let check name got expected =
  let msg = if got = expected then "ok" else "FAIL: got " ^ got in
  Printf.printf "%-34s %s\n" name msg ;
  if got <> expected then exit 1

let check_int name got expected =
  check name (string_of_int got) expected

let check_fin name got expected =
  check name (show_fin got) expected

let check_exn show name got expected =
  check name (show_exn show got) expected

let () =
  check_int "minus 5 3" (minux_x 5 3) "2";
  check_int "minus 4 0" (minux_x 4 0) "4";
  check_int "pred 5" (pred_x 5) "4";
  check_int "pred' 5" (pred'_x 5) "4";
  check_int "pred_twice 5" (pred_twice_x 5) "3";
  check_int "gcd 48 18" (gcd_x 48 18) "6";
  check_int "gcd 18 48" (gcd_x 18 48) "6";
  check_int "gcd 7 0" (gcd_x 7 0) "7";
  check_fin "as_fin 3 1" (as_fin_x 3 1) "1";
  check_fin "as_fin 5 4" (as_fin_x 5 4) "4";
  check_exn string_of_int "predX 5" (predX_x 5) "success 4";
  check_exn string_of_int "predX 0" (predX_x 0) "exception \"pred of 0\"";
  check_exn show_fin "as_finX 3 1" (as_finX_x 3 1) "success 1";
  check_exn show_fin "as_finX 2 5" (as_finX_x 2 5) "exception \"Too big to fit.\"";
  check_exn show_unit "eqty bool bool" (eqty_x Bool Bool) "success tt";
  check_exn show_unit "eqty (b->b) (b->b)" (eqty_x (Arr (Bool, Bool)) (Arr (Bool, Bool))) "success tt";
  check_exn show_unit "eqty bool (b->b)" (eqty_x Bool (Arr (Bool, Bool))) "exception \"Arr ≠ Bool\"";
  check_exn show_ty "infer idbool" (infer_x [] idbool) "success (bool -> bool)";
  check_exn show_ty "infer ok" (infer_x [] ok) "success bool";
  check_exn show_ty "infer good_if" (infer_x [] good_if) "success bool";
  check_exn show_ty "infer bad_if" (infer_x [] bad_if) "success (bool -> bool)";
  check_exn show_ty "infer if fas tru fas" (infer_x [] (Ifte (Fas, Tru, Fas))) "success bool";
  check_exn show_ty "infer var 0" (infer_x [] (Var 0)) "exception \"Unbound variable\"";
  check_exn show_ty "infer var 0 in [bool]" (infer_x [Bool] (Var 0)) "success bool";
  check_exn show_ty "infer tru tru" (infer_x [] (Ap (Tru, Tru))) "exception \"Cannot be applied\"";
  print_endline "all tests passed"
