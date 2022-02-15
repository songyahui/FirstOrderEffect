exception Foo of string
type effName = string
type argName = string

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

and meth = (string * string list * expr * spec * spec)

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
  | Eq (t1, t2) -> (string_of_terms t1) ^ "==" ^ (string_of_terms t2)
  | PureOr (p1, p2) -> "("^string_of_pure p1 ^ "\\/" ^ string_of_pure p2^")"
  | PureAnd (p1, p2) -> "("^string_of_pure p1 ^ "/\\" ^ string_of_pure p2^")"
  | Neg p -> "(!" ^ "(" ^ string_of_pure p^"))"
;;

let string_of_v (v:value) : string =
  match v with
  | Const i -> "const_" ^ string_of_int i
  | Variable s -> "var_" ^ s
  | Unit -> "unit"
;;


let rec string_of_spec (li:spec): string =
  let string_of_single_spec (s:single_spec) : string =
    let string_of_flow (f:flow) : string =
      match f with
      | Normal v -> "Normal(" ^ string_of_v v ^ ")"
      | Eff (eff_n, eff_v, ss) ->
        "(" ^ eff_n ^ "," ^ string_of_v eff_v ^ "):\n  "
        ^ string_of_spec ss
    in
    let (pi, f) = s in
    let string_of_pi = string_of_pure pi in
    let string_of_flow = string_of_flow f in
    "(" ^ string_of_pi ^","^ string_of_flow ^ ")"
  in List.fold_left (fun acc a -> acc ^ string_of_single_spec a ) "" li

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

let formLetSeq (e:expr) (e1:expr) : expr =
  Let ("null", e, e1)

let skip_cont: spec = [(TRUE, Normal Unit)]

let rec forward_shell (preState:spec) (expr:expr) : spec =
  let rec forward (curState:single_spec) (expr:expr) : spec =
    let (pi, flow) = curState in
    match flow with
    | Eff (eff_name, eff_v, eff_cons) -> 
      let expr_spec = forward_shell eff_cons expr in 
      [(pi, Eff(eff_name, eff_v, expr_spec))]
    | Normal (v_old) -> 
      (match expr with 
      | Value v ->  [(pi, Normal (v))]
      | Perform (eff, v) -> [(pi, Eff(eff, v, skip_cont))]
      | Let (x, e1, e2) ->
        let eff1 = forward curState e1 in
        forward_shell eff1 e2
      | IfElse (v, e1, e2) ->
        let newCur1 = (PureAnd (pi, Eq(vTot v, Num 1)), flow) in
        let newCur2 = (PureAnd (pi, Eq(vTot v, Num 0)), flow) in
        let eff1 = forward newCur1 e1 in
        let eff2 = forward newCur2 e2 in
        List.append eff1 eff2
      | Match (e1, handler) ->
        let (x_base, e_base, eff_han) = handler in
        let eff1 = forward curState e1 in
        let aff_final = List.map (fun final -> 
          let (pi1, f1) = final in
          match f1 with
          | Normal v -> forward final e_base
          | Eff(eff_name, v, cons) ->
            (match retrive_handler eff_han eff_name with
            | None -> [final]
            | Some (_, var_s, e_h)-> forward final (Match (e_h, handler))
            )
        ) eff1 in
        List.flatten aff_final
      | _ -> raise (Foo "Not yet!") (*| FunCall of (string * string list)*)
      )
    
  in List.flatten (List.map (fun cur -> forward cur expr) preState)


let startState = (TRUE,  Normal Unit)


let testExpr1:expr = Match ((Perform ("A", Unit)), ("x", Value Unit, [("A", "x", Resume (Unit))]))

let test = forward_shell [startState] testExpr1

let main = print_string (string_of_spec test)




(*


 match flow with 
    | Normal v -> 
    match expr with


 -> 
(* I F E L S E *) 
    
(* R E S U M E *) 
    | Resume v ->
      (match flow with
      | Normal -> raise (Foo "resuming but has no continusation")
      | Eff (eff_n, v, cons) -> 
        let newCur = (PureAnd (pi, Eq(vTot v, Name str)), flow, c1) in
        forward newCur e
      )



    


*)