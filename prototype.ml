open Printf
exception Foo of string


let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl


let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└── "
      else
        "├── "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;


type effName = string
type argName = string
type mn = string

type value = Unit
  | Const of int
  | Variable of string

and eff_handler = (effName * argName * expr)

and handler = (string * expr (*Base*) * eff_handler list)

and expr = Value of value
  | FunCall of (string * string list)
  | Let of (string * expr * expr)
  | IfElse of (value * expr * expr)
  | Match of (expr * handler)
  | Perform of (string * value)
  | Resume of value

and meth = (mn * argName list * expr * spec * spec)

and program = meth list

and terms = Name of string
  | Num  of int
  | Plus of terms * terms

and pure = TRUE
  | FALSE
  | Gt of terms * terms
  | Lt of terms * terms
  | GtEq of terms * terms
  | LtEq of terms * terms
  | Eq of terms * terms
  | PureOr of pure * pure
  | PureAnd of pure * pure
  | Neg of pure

and flow = Normal of value | Eff of (effName * value * spec)

and single_spec = (pure * flow)

and spec = single_spec list

let rec string_of_terms (t:terms):string =
  match t with
  | Name name -> name
  | Num n -> string_of_int n
  | Plus (t1, t2) -> (string_of_terms t1) ^ ("+") ^ (string_of_terms t2)
;;

(*To pretty print pure formulea*)
let rec string_of_pure (p:pure):string =
  match p with
  | TRUE -> "true"
  | FALSE -> "false"
  | Gt (t1, t2) -> (string_of_terms t1) ^ ">" ^ (string_of_terms t2)
  | Lt (t1, t2) -> (string_of_terms t1) ^ "<" ^ (string_of_terms t2)
  | GtEq (t1, t2) -> (string_of_terms t1) ^ ">=" ^ (string_of_terms t2)
  | LtEq (t1, t2) -> (string_of_terms t1) ^ "<=" ^ (string_of_terms t2)
  | Eq (t1, t2) -> (string_of_terms t1) ^ "=" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "\\/" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> "("^string_of_pure p1 ^ "/\\" ^ string_of_pure p2^")"
  | Neg p -> "(!" ^ "(" ^ string_of_pure p^"))"
;;

let string_of_v (v:value) : string =
  match v with
  | Const i -> string_of_int i
  | Variable s ->  s
  | Unit -> "()"
;;


let rec string_of_spec (li:spec): string =
  let string_of_single_spec (s:single_spec) : string =
    let string_of_flow (f:flow) : string =
      match f with
      | Normal v -> "Normal(" ^ string_of_v v ^ ")"
      | Eff (eff_n, eff_v, ss) ->
        "Eff(" ^ eff_n ^ " " ^ string_of_v eff_v ^ " "
        ^ string_of_spec ss
    in
    let (pi, f) = s in
    let string_of_pi = string_of_pure pi in
    let string_of_flow = string_of_flow f in
    "(" ^ string_of_pi ^","^ string_of_flow ^ ")"
  in 
  match li with 
  | [] -> "No Spec"
  | [a] -> string_of_single_spec a
  | a::xs -> (string_of_single_spec a) ^ " \\/ " ^  string_of_spec xs 

let vTot (v:value) : terms =
  match v with
  | Const i -> Num i
  | Variable s -> Name s
  | _ -> raise (Foo "Converting Unit to erms ")
;;

let rec retrive_handler (li: eff_handler list) (eff_name: string) : eff_handler option  =
  match li with
  | []-> None
  | (eff, str, e):: xs ->
  if String.compare eff eff_name == 0 then  Some (eff, str, e)
  else retrive_handler xs eff_name
;;

let rec string_of_arg_list (li:string list):string = 
  match li with 
  | [] -> ""
  | [x] -> x 
  | x::xs -> x ^ "," ^ string_of_arg_list xs
;;


let rec string_of_expr (expr:expr): string = 
  
  let string_of_handler (handler:handler) : string = 
    let rec helper handLi : string =
      match handLi with 
      | [] -> ""
      | (eff_name, eff_var, eff_e)::xs -> "| effect (" ^ eff_name 
        ^ " " ^ eff_var ^ ") -> " ^ string_of_expr eff_e ^"\n" ^ helper xs 
    in 
    let (base_v, base_e, li) = handler in 
    "| " ^ base_v ^ " -> " ^ string_of_expr base_e ^ "\n" ^  helper li
  in

  match expr with 
  | Resume v -> "resume "^ string_of_v v 
  | Match (e1, handler) -> "match (" ^ string_of_expr e1 ^ ") with \n" ^ string_of_handler handler
  | Perform (eff, v) -> "perform (" ^ eff ^ " "^ string_of_v v ^")"
  | Value v -> string_of_v v 
  | Let (var, e1, e2) -> "let " ^ var ^" = " ^ string_of_expr e1 ^ " in " ^ string_of_expr e2 
  | IfElse (v, e1, e2) -> "if " ^ string_of_v v ^ " then " ^ string_of_expr e1 ^ "\nelse " ^ string_of_expr e2 
  | FunCall (mn, varLi) -> mn ^ "(" ^ string_of_arg_list varLi ^")"
 ;;

let normalPure (pi:pure) : pure = 
match pi with 
| PureAnd (TRUE, TRUE) -> TRUE
| PureAnd (TRUE, other) -> other
| PureAnd (other, TRUE) -> other
| _ -> pi
;;






let formLetSeq (e:expr) (e1:expr) : expr =
  Let ("_", e, e1)

let skip_cont: spec = [(TRUE, Normal Unit)]

let rec findMethod (program:program) (str:string) : (spec* spec) option =
  match program with 
  | [] -> None 
  | (mn, _, _, pre, post):: xs ->  if String.compare str mn == 0 then Some (pre, post) else findMethod xs str
  ;;

let concatenateSpec ((pi, f): single_spec) (tail:spec) : spec = 
  match f with 
  | Normal v -> List.map (fun (a, b)-> (PureAnd(a, pi), b)) tail
  | Eff (eff_name, eff_v, eff_cons) -> [(pi, Eff(eff_name, eff_v, tail))]
  ;;

let nullable (spec:spec) : bool = 
  List.fold_left (fun acc (pi, f) -> acc || 
    match f with 
    | Normal _ -> true 
    | Eff _ -> false 
  ) false spec;;

let fst (spec:spec): (effName * value) list = 
  List.flatten (List.map (fun  (pi, f) ->
    match f with 
    | Normal _ -> [] 
    | Eff (name, v, _) -> [(name, v)] 
  ) spec)

let compareV (v1:value) (v2:value) : bool =
  match (v1, v2) with 
  | (Unit, Unit) -> true
  | (Const n1, Const n2) -> n1 == n2
  | (Variable v1, Variable v2) -> String.compare v1 v2 == 0 
  | _ -> false
;;


let derivitive (spec:spec) (inp_f: (effName * value)): spec = 
  let (inp_name, inp_v) = inp_f in 
  List.flatten (List.map (fun  (pi, f) ->
    match f with 
    | Normal _ -> []
    | Eff (name, v, cons) -> if String.compare name inp_name ==0 && compareV v inp_v then cons else []
  ) spec)

let showEntail (eff1:spec)( eff2:spec):string = string_of_spec eff1 ^ " |- "  ^ string_of_spec eff2;;


(* Entailent *)
let rec entailment (lhs:spec) (rhs:spec) : (bool*binary_tree) = 
  if nullable lhs && (not (nullable rhs)) then (false, Node(showEntail lhs rhs^ "   [Nullable]", [])) 
  else let f_Set = fst lhs in 
  let (res, subtrees) = 
  List.fold_left (fun acc f -> 
    (let (acc_bool, acc_tree) = acc in 
     let der_lhs = derivitive lhs f in 
     let der_rhs = derivitive rhs f in   
     let (new_bool, new_tree) = entailment der_lhs der_rhs in 
     (acc_bool && new_bool, new_tree :: acc_tree )
    )
  ) (true, [])  f_Set in 
  (res, Node(showEntail lhs rhs ^ "   [Unfold]", subtrees) )

let rec forward_shell (program:program) (preHandler:(handler*spec) option)  (preState:spec) (exprOut:expr) : spec =
  let rec forward (curHandler:(handler*spec) option) (curState:single_spec) (exprIn:expr) : spec =
    
    (*print_string ("=================\n");
    print_string (string_of_spec [curState]^"\n");
    print_string (string_of_expr exprIn ^ "\n");*)
    

    let (pi, flow) = curState in
    let pi = normalPure pi in 

    match flow with
    | Eff (eff_name, eff_v, eff_cons) -> 
      (match exprIn with 
      | Match (e1, handler) ->

        let (x_base, e_base, eff_han) = handler in
        let eff1 = forward curHandler curState e1 in


        let aff_final = List.map (fun final -> 
          let (pi1, f1) = final in
          match f1 with
          | Normal v -> forward curHandler final e_base
          | Eff(eff_name, v, cons) ->
            (match retrive_handler eff_han eff_name with
            | None -> [final]
            | Some (_, var_s, e_h)-> 
              (*print_string (string_of_expr exprIn ^"\n");
              print_string (string_of_spec [final] ^"\n");
              *)
              
              forward (Some (handler, cons)) (pi1, Normal(Unit)) e_h
            )
        ) eff1 in
        List.flatten aff_final
      | _ ->
        let expr_spec = forward_shell program curHandler eff_cons exprIn in 
        [(pi, Eff(eff_name, eff_v, expr_spec))]
      )
    | Normal (v_old) -> 
      (match exprIn with 
      | Value v ->  [(pi, Normal (v))]
      | Perform (eff, v) -> [(pi, Eff(eff, v, skip_cont))]
      | Let (x, e1, e2) ->
        (match e1 with 
        | Resume v -> 
          let expr_spec = forward curHandler curState (Resume v) in 
          forward_shell program None expr_spec e2
        | _ -> 
          let eff1 = forward curHandler curState e1 in
          List.flatten (List.map (fun (eff1_pi, eff1_f) -> 
            match eff1_f with
            | Normal eff1_v -> forward curHandler (PureAnd(eff1_pi, Eq(Name x, vTot eff1_v)), eff1_f) e2
            | _ -> forward_shell program curHandler eff1 e2
          ) eff1)
          
        )
        
      | IfElse (v, e1, e2) ->
        let newCur1 = (PureAnd (pi, Eq(vTot v, Num 1)), flow) in
        let newCur2 = (PureAnd (pi, Eq(vTot v, Num 0)), flow) in
        let eff1 = forward curHandler newCur1 e1 in
        let eff2 = forward curHandler newCur2 e2 in
        List.append eff1 eff2
      | Match (e1, handler) ->

        let (x_base, e_base, eff_han) = handler in
        let eff1 = forward curHandler curState e1 in
        

        let aff_final = List.map (fun final -> 
          let (pi1, f1) = final in
          match f1 with
          | Normal v -> forward curHandler final e_base
          | Eff(eff_name, v, cons) ->
            (match retrive_handler eff_han eff_name with
            | None -> [final]
            | Some (_, var_s, e_h)-> 
              (*print_string (string_of_expr exprIn ^"\n");
              print_string (string_of_spec [final] ^"\n");
              *)
              
              forward (Some (handler, cons)) (pi1, Normal(Unit)) e_h
            )
        ) eff1 in
        List.flatten aff_final

      | Resume v -> 
        (match curHandler with 
        | None -> raise (Foo "resuming but has no handler")
        | Some (han, spec) -> 
          let hahah = List.map (fun final->  
          let (x_base, e_base, eff_han) = han in
          let (expr_pi, expr_f) = final in 
          match expr_f with
          | Normal v -> 
            (*print_string ("hahhahahhaha\n");
            print_string (string_of_expr e_base ^ "\n");
            print_string (string_of_spec (forward xs curState e_base) ^ "\n");
            *)

            forward None curState e_base
          | Eff(eff_nameIn, eff_vIn, eff_consIn) ->
            (match retrive_handler eff_han eff_nameIn with
            | None -> [final]
            | Some (_, var_s, e_h)-> 
              forward None final (Match (Value(Unit), han))
            )
          ) spec
          in List.flatten hahah
        )
      | FunCall (mn, _) -> 
        (match findMethod program mn with 
        | None -> raise (Foo ("Method " ^ mn ^" is not defined!\n"))
        | Some (pre, post) -> 
          let (res, tree) = entailment [curState] pre in 
          let print_Tree = printTree ~line_prefix:"* " ~get_name ~get_children tree in 
          if res then concatenateSpec curState post
          else  raise (Foo ("Method " ^ mn ^" precondition is not met!\n" ^ print_Tree))
        )
      )
    
  in List.flatten (List.map (fun cur -> forward preHandler cur exprOut) preState)





(*** Tests ***)

let startState = (TRUE,  Normal Unit)


let performAunit = (Perform ("A", Unit))
let performBunit = (Perform ("B", Unit))
let const3 = Value (Const 3)
let const5 = Value (Const 5)
let const50 = Value (Const 50)
let const300 = Value (Const 300)

let folowedByUnit = Let ("_", performAunit, Value (Const 1))
let seqE1E2 e1 e2 = Let ("_", e1, e2)
let resumeUnit = Resume (Unit)
let resumeUnitCons = Let ("_", resumeUnit, Value (Const 30))
let testExpr1:expr = Match (folowedByUnit, ("x", Value (Const 100), [("A", "x", seqE1E2 performAunit resumeUnit)]))
let testExprNoResume:expr = Match (folowedByUnit, ("x", Value (Const 100), [("A", "x", Value (Unit))]))
let testExpr2:expr = 
  Match (folowedByUnit, 
  ("x", Value (Const 100), [("A", "x", Let("_", Resume (Unit), Value (Const 50)))]))

let handleTestExpr1:expr = Match (testExpr1, ("x", Value (Const 1000), [("A", "x", resumeUnit)]))

let ifElse = IfElse (Variable "x", seqE1E2 performAunit const50, const300)
let ifElseElse = IfElse (Variable "x", performAunit, IfElse (Variable "y", performBunit, const3))

let handler1:expr = Match (ifElse, ("x", Value (Const 100), [("A", "x", resumeUnit )]))
let handlerskip:expr = Match (ifElse, ("x", Value (Const 100), [("A", "x", const3 )]))
let handlerLeakB:expr = Match (ifElse, ("x", Value (Const 100), [("B", "x", resumeUnit )]))
let lerseqAB:expr = seqE1E2 performAunit performBunit

let handlerseqAB:expr = Match (seqE1E2 performAunit performBunit, ("x", Value (Const 100), [("A", "x", resumeUnit);("B", "x", resumeUnit )]))

let handlerseqARest:expr = Match (performAunit, ("x", Value (Const 100), [("A", "x", seqE1E2 resumeUnit const3)]))

let handlerseqABRest:expr = Match (seqE1E2 performAunit performBunit, ("x", Value (Const 100), [("A", "x", seqE1E2 resumeUnit const5);("B", "x", seqE1E2 resumeUnit const50 )]))

let handlerseqBARest:expr = Match (seqE1E2 performBunit performAunit, ("x", Value (Const 100), [("A", "x", seqE1E2 resumeUnit const5);("B", "x", seqE1E2 resumeUnit const50 )]))

let x1ifElse = Let ("x", Value(Const 1), ifElse)

let xy1Ifelse = Let ("y", Value(Const 1), Let ("x", Value(Variable "y"), ifElse))

let test() = forward_shell [] None [startState] testExpr1
let performAunitTest () = forward_shell []  None [startState] performAunit

let test_expression (exprLi:expr list) =
  List.fold_left (fun acc expr -> 
    print_string("\n=====" ^ "TEST EXPR" ^ string_of_int acc ^"=========\n\n");
    print_string (string_of_expr expr); 
    let eff = forward_shell [] None [startState] expr in 
    print_string("\n--------------\nFinal = \n" ^string_of_spec eff ^"\n\n");
    acc + 1
  ) 1 exprLi 


let ifelseP = ("f", ["x"],  ifElse ,  [(TRUE, Normal (Unit))] ,  [(TRUE, Normal (Const 3));(TRUE, Eff ("A", Unit, [(TRUE, Normal (Const 50))]))])
let handlerP:meth = ("handle", [], Match (FunCall ("f", [ "1"]), ("x", Value (Const 100), [("A", "x", resumeUnit )])), [(TRUE, Normal (Unit))], [(TRUE, Normal (Const 100))])
let handlerP1:meth = ("handle", [], Match (FunCall ("f", [ "1"]), ("x", Value (Const 100), [("A", "x", Value (Unit) )])), [(TRUE, Normal (Unit))], [(TRUE, Normal (Const 100)); (TRUE, Normal (Unit))])


let string_of_meth (name, arL, expr, pre, post) : string =
  let rec helper li =
    match li with
    | [] -> ""
    | [x] -> x 
    | x :: xs ->  x ^ ", " ^ helper xs
  in name ^ " (" ^ helper arL ^ ") =\nPre: "^ string_of_spec pre ^ "\nPost: " ^string_of_spec post ^ "\n\n" ^string_of_expr expr ^ "\n"

let test_program (exprLi:program) =
  List.fold_left (fun acc (p_name, argL, expr, pre, post) -> 
    print_string("\n=====" ^ "TEST PRGM" ^ string_of_int acc ^"=========\n\n");
    print_string (string_of_meth ((p_name, argL, expr, pre, post))); 
    let eff = forward_shell exprLi None pre expr in 
    print_string("--------------\n");
    (*print_string("\n--------------\nFinal = \n" ^string_of_spec eff ^"\n\n"); *)
    let (result, tree) =  entailment eff post in 
    let print_Tree = printTree ~line_prefix:"* " ~get_name ~get_children tree in 
    
    let () = (if result then print_string ("[VERIFICATION SUCCEED]\n" ^ print_Tree)
    else print_string ("[VERIFICATION FAILED]\n"^ print_Tree ^ "\n") ) in 
    acc + 1
  ) 1 exprLi 


let main = test_program [ifelseP; handlerP; handlerP1]; 

 test_expression 
  [handleTestExpr1;
  ifElse;
  x1ifElse;
  xy1Ifelse;
  ifElseElse;
  handler1;
  handlerskip;
  handlerLeakB;
  lerseqAB;
  handlerseqAB;
  handlerseqARest;
  handlerseqABRest;
  handlerseqBARest]
  


