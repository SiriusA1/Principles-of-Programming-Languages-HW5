open OUnit2

open Checked.Ast
open Checked.Checker
open Checked.ReM

(* texper tea_result == (texpr, tenv) a_result == tenv -> texpr result
 * == tenv -> (Ok of texpr | Error of string) *)

(* Generic error result for tests that should produce an error *)
let generic_err : 'a result = Error ("<message>")


(* A unit test constructor has (name, code, result, points).
 *
 * For student-defined tests, the point value field is irrelevant.
 *
 * Results which are errors should be a single generic error instead of a
 * specific error message. Thus, use generic_err for such tests.
*)
type unit_test =
  | Check of string * string * texpr result * int


let string_of_texpr_result : texpr result -> string = function
  | Ok v -> "Ok (" ^ (string_of_texpr v) ^ ")"
  | Error s -> "Error (" ^ s ^ ")"


(* Transforms our unit_test into an OUnit test with pretty printing *)
let test_of_unit_test (test : unit_test) : OUnit2.test =
  let enhanced_assert name points result target =
    let failed =
      name ^ " failed, -" ^ (string_of_int points) ^ " point(s)"
    in
    assert_equal
      ~msg:(failed)
      ~printer:string_of_texpr_result
      result
      target
  in

  (* exceptions are turned into "error" results to preserve pretty
   * printing, but an exception is always considered incorrect behavior *)
  let err_test (name : string) (code : string) (points : int) func =
    name >:: (fun _ ->
      let target = try func code with e ->
        match generic_err with
        | Ok _ -> failwith "unexpected"
        | Error msg ->
            let str_exn = Printexc.to_string e in
            Error ("exception: " ^ str_exn ^ " (no " ^ msg ^ ")")
      in
      match target with
      | Error _ -> ()
      | Ok _ as value -> enhanced_assert name points generic_err value)
  in

  let normal_test name code result points func =
    name >:: (fun _ ->
      let target = try func code with e ->
        Error (Printexc.to_string e)
      in
      enhanced_assert name points result target)
  in

  match test with
  | Check (name, code, Error _, points) ->
      err_test name code points chk
  | Check (name, code, result, points) ->
      normal_test name code result points chk

let run_suite (name : string) (tests : unit_test list list) =
  let suite = List.(map test_of_unit_test (concat tests)) in
  run_test_tt_main (name >::: suite)
