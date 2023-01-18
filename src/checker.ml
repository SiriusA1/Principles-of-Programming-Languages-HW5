open Ast
open ReM
open Dst

(* Conor McGullam *)

let rec type_of_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    type_of_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    type_of_expr e1 >>= fun t1 ->
    type_of_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    type_of_expr e1 >>= fun t1 ->
    type_of_expr e2 >>= fun t2 ->
    type_of_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    type_of_expr e >>= fun t ->
    extend_tenv id t >>+
    type_of_expr body
  | Proc(var,t1,e) ->
    extend_tenv var t1 >>+
    type_of_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | App(e1,e2) ->
    type_of_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    type_of_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec(id,param,tParam,tRes,body,target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     type_of_expr body >>= fun t ->
     if t=tRes 
     then type_of_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")

  (* references *)
  | BeginEnd(es) ->
    List.fold_left (fun r e -> r >>= fun _ -> type_of_expr e) (return UnitType) es 
  | NewRef(e) ->
    type_of_expr e >>= fun t ->
    return (RefType(t))
  | DeRef(e) ->
    type_of_expr e >>= fun t1 ->
    (match t1 with
    | RefType(t2) -> return t2
    | _ -> error "deref: Expected a reference type")  
  | SetRef(e1,e2) ->
    type_of_expr e1 >>= fun t1 ->
    type_of_expr e2 >>= fun t2 ->
    (match t1 with
    | RefType(t) when t = t2 -> return UnitType
    | RefType(t) -> error "setref: type mismatch"
    | _ -> error "setref: Expected a reference type")

  (* pairs *)
  | Pair(e1,e2) ->
    type_of_expr e1 >>= fun t1 ->
    type_of_expr e2 >>= fun t2 ->
    return (PairType(t1,t2))
  | Unpair(id1,id2,e1,e2) ->
    type_of_expr e1 >>=
    pair_of_pairType "unpair: " >>= fun (r,l) ->
    extend_tenv id1 r >>+
    extend_tenv id2 l >>+
    type_of_expr e2
      
  (* lists *)
  | EmptyList(t) ->
    return (ListType(t)) 
  | Cons(h, t) ->
    type_of_expr h >>= fun t1 ->
    type_of_expr t >>= fun t2 ->
    (match t2 with
    | ListType(t3) when t3 = t1 -> return (ListType(t3))
    | ListType(t3) -> error "cons: type of head and tail do not match"
    | _ -> error "cons: Expected a list type")
  | Null(e) ->
    type_of_expr e >>= fun t1 ->
    (match t1 with
    | ListType(t) -> return BoolType
    | _ -> error "null: Expected a list type")  
  | Hd(e) ->
    type_of_expr e >>= fun t1 ->
    (match t1 with
    | ListType(t) -> return t
    | _ -> error "hd: Expected a list type") 
  | Tl(e) ->
    type_of_expr e >>= fun t1 ->
    (match t1 with
    | ListType(t) -> return (ListType(t))
    | _ -> error "tl: Expected a list type")  

  (* trees *)
  | EmptyTree(t) ->
    return (TreeType(t))
  | Node(de, le, re) ->
    type_of_expr de >>= fun dt ->
    type_of_expr le >>= fun lt ->
    type_of_expr re >>= fun rt ->
    (match lt with
    | TreeType(t1) when t1 = dt -> 
      (match rt with
      | TreeType(t2) when t2 = dt -> return (TreeType(t2))
      | TreeType(t2) -> error "node: Type of right tree doesn't match type of root"
      | _ -> error "node: Expected a tree type (right tree)")
    | TreeType(t1) -> error "node: Type of left tree doesn't match type of root"
    | _ -> error "node: Expected a tree type (left tree)")
  | NullT(t) ->
    type_of_expr t >>= fun t1 ->
    (match t1 with
    | TreeType(t2) -> return BoolType
    | _ -> error "nullt: Expected a tree type") 
  | GetData(t) ->
    type_of_expr t >>= fun t1 ->
    (match t1 with
    | TreeType(t2) -> return t2
    | _ -> error "getdata: Expected a tree type")   
  | GetLST(t) ->
    type_of_expr t >>= fun t1 ->
    (match t1 with
    | TreeType(t2) -> return (TreeType(t2))
    | _ -> error "getlst: Expected a tree type") 
  | GetRST(t) ->
    type_of_expr t >>= fun t1 ->
    (match t1 with
    | TreeType(t2) -> return (TreeType(t2))
    | _ -> error "getrst: Expected a tree type")   


  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug called!"
  | _ -> error "type_of_expr: implement"    



let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast


(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> type_of_expr
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> type_of_expr
  in run_teac (c >>= fun t -> return @@ Ast.string_of_texpr t)

