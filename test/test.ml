open Checked.Ast
open Checked.ReM
open Test_lib

(* 15 points *)
let ref_tests : unit_test list = [
  Check (
    "newref-nested",
    "newref(newref(3))",
    Ok (RefType (RefType IntType)),
    3
  );
  Check (
    "newref-proc",
    "newref(proc (x:int) { x })",
    Ok (RefType (FuncType (IntType, IntType))),
    3
  );
  Check(
    "setref-int",
    "let x = newref(5) in setref(x, 6)",
    Ok UnitType,
    3
  );
  Check (
    "deref-int",
    "let x = newref(5) in deref(x)",
    Ok IntType,
    3
  );
  Check (
    "deref-newref",
    "deref(newref(newref(3)))",
    Ok (RefType IntType),
    3
  );
]

(* 20 points *)
let pair_tests : unit_test list = [
  Check (
    "pair-ints",
    "pair(3, 4)",
    Ok (PairType (IntType, IntType)),
    2
  );
  Check (
    "pair-nested",
    "pair(pair(3, 4), 5)",
    Ok (PairType ((PairType (IntType, IntType)), IntType)),
    3
  );
  Check (
    "pair-bool-int",
    "pair(zero?(0), 3)",
    Ok (PairType (BoolType, IntType)),
    3
  );
  Check (
    "pair-proc",
    "pair(proc (x:int) { x - 1 }, 4)",
    Ok (PairType (FuncType (IntType, IntType), IntType)),
    3
  );
  Check (
    "unpair-ints",
    "unpair (a, b) = pair(1, 2) in a + b",
    Ok IntType,
    3
  );
  Check (
    "unpair-in-proc",
    "proc (z:<int*bool>) { unpair(x, y) = z in pair(y, x) }",
    Ok (FuncType ((PairType (IntType, BoolType)), (PairType (BoolType, IntType)))),
    3
  );
  Check (
    "unpair-swap",
    "let f = proc (z:<int*bool>) { unpair (x,y)=z in pair(y,x) } in (f pair (1, zero?(0)))",
    Ok (PairType (BoolType, IntType)),
    3
  );
]

(* 30 points *)
let list_tests : unit_test list = [
  Check (
    "emptylist",
    "emptylist int",
    Ok (ListType IntType),
    4
  );
  Check (
    "singleton-int",
    "cons(1, emptylist int)",
    Ok (ListType IntType),
    4
  );
  Check (
    "singleton-bool",
    "cons(zero?(1), emptylist bool)",
    Ok (ListType BoolType),
    4
  );
  Check (
    "list-of-lists",
    "let x = 4 in cons(cons(x - 1, emptylist int), emptylist list(int))",
    Ok (ListType (ListType (IntType))),
    6
  );
  Check (
    "null",
    "null?(emptylist list(int))",
    Ok BoolType,
    4
  );
  Check (
    "hd-list-int",
    "hd(cons(1, emptylist int))",
    Ok IntType,
    4
  );
  Check (
    "tl-list-int",
    "tl(cons(1, emptylist int))",
    Ok (ListType IntType),
    4
  );
]

(* 30 points *)
let tree_tests : unit_test list = [
  Check (
    "emptytree",
    "emptytree int",
    Ok (TreeType IntType),
    3
  );
  Check (
    "null-tree",
    "nullT?(emptytree int)",
    Ok BoolType,
    3
  );
  Check (
    "not-null-tree",
    "nullT?(node(1, node(2, emptytree int, emptytree int), emptytree int))",
    Ok BoolType,
    6
  );
  Check (
    "get-data",
    "getData(node(1, node(2, emptytree int, emptytree int), emptytree int))",
    Ok IntType,
    6
  );
  Check (
    "get-lst",
    "getLST(node(1, node(2, emptytree int, emptytree int), emptytree int))",
    Ok (TreeType IntType),
    6
  );
  Check (
    "get-rst",
    "getRST(node(1, node(2, emptytree int, emptytree int), emptytree int))",
    Ok (TreeType IntType),
    6
  );
]

(* NOTE: Total points add to 95 as Unit is provided *)
let _ = run_suite "graded test suite" [
  ref_tests;
  pair_tests;
  list_tests;
  tree_tests;
]
