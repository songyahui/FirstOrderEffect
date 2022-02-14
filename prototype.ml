exception Foo of string
type effName = string
type argName = string

type value = Unit
  | Const of int
  | Variable of string
  | Lambda of (string * expr)

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

and flow = Normal | Eff of (effName * value * spec)

and single_spec = (pure * value (*result value*) * flow)

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
  | Lambda (str, expr) -> "lam_" ^ str
;;


let rec string_of_spec (li:spec): string =
  let string_of_single_spec (s:single_spec) : string =
    let string_of_flow (f:flow) : string =
      match f with
      | Normal -> "Normal"
      | Eff (eff_n, eff_v, ss) ->
        "(" ^ eff_n ^ "," ^ string_of_v eff_v ^ "):\n  "
        ^ string_of_spec ss
    in
    let (pi, v,  f) = s in
    let string_of_pi = string_of_pure pi in
    let string_of_value = string_of_v v in
    let string_of_flow = string_of_flow f in
    "(" ^ string_of_pi ^","^ string_of_value ^","^ string_of_flow ^ ")"
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

let rec forward_shell (curState:spec) (expr:expr) : spec =
  let rec forward (curState:single_spec) (expr:expr) : spec =
    let (pi, res, flow) = curState in
    match expr with
(* V A L U E *)
    | Value v ->  [(pi, v, flow)]
(* P E R F O R M *)
    | Perform (eff, v) -> 
      let cons =[(TRUE, Unit, Normal)] in [(pi, res, Eff(eff, v, cons))]
(* L E T *)  
    | Let (x, e1, e2) ->
      let eff1 = forward curState e1 in
      let final_effs :spec list= List.map (
        fun final->
          let (pi_f, v_f, flow_f) = final in
          match flow_f with 
          | Normal -> forward final e2
          | Eff (eff_n, v, cons) -> 
            let reStart = List.map 
              (fun (cons_pi, cons_v, cons_cons) ->  (cons_pi, Unit, Normal)) cons in 
            let eff2:spec = forward_shell reStart e2 in
            [(pi_f, v_f, Eff (eff_n, v, eff2))]
            
      ) eff1 in
      List.flatten final_effs
(* I F E L S E *) 
    | IfElse (v, e1, e2) ->
      let newCur1 = (PureAnd (pi, Eq(vTot v, Num 1)), res, flow) in
      let newCur2 = (PureAnd (pi, Eq(vTot v, Num 0)), res, flow) in
      let eff1 = forward newCur1 e1 in
      let eff2 = forward newCur2 e2 in
      List.append eff1 eff2
(* R E S U M E *) 
    | Resume v ->
      (match flow with
      | Normal -> raise (Foo "resuming but has no continusation")
      | Eff (eff_n, v, cons) -> 
        let newCur = (PureAnd (pi, Eq(vTot v, Name str)), flow, c1) in
        forward newCur e
      )


    | _ -> raise (Foo "Not yet!") (*| FunCall of (string * string list)*)
  

  in List.flatten (List.map (fun cur -> forward cur expr) curState)


let startState = (TRUE, Unit,  Normal)


let testExpr1:expr = Match ((Perform ("A", Unit)), ("x", Value Unit, [("A", "x", Value Unit)]))

let test = forward_shell [startState] testExpr1




(*






| Match (e1, handler) ->
    let (x_base, e_base, eff_han) = handler in
    let eff1 = forward curState e1 in
    let aff_final = List.map (fun final ->
  let (pi1, f1, c1) = final in
  match f1 with
  | Normal -> forward final e_base
  | Eff(eff_name, v) ->
(match retrive_handler eff_han eff_name with
| None -> [final]
| Some (_, var_s, e_h)->
    (* Recursively catching it*)

    forward final (Match (e_h, handler))
)
    ) eff1 in
    List.flatten aff_final


*)