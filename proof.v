Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Inductive value : Type := unit | const (c:nat) | variable (v:string).

Inductive sigmal : Type := A | B | C | D.


Inductive flow : Type := 
| Normal (v:value) 
| Eff : sigmal -> value -> list flow -> flow.

Definition spec : Type := list flow.


Inductive expression :  Type :=
| Val : value -> expression
| Call : string -> list string -> expression
| LetBind : string -> expression -> expression -> expression
| IfElse : string -> expression -> expression -> expression
| Perform : sigmal -> value ->  expression
| Resume : value -> expression
| MatchCases : expression -> handler -> expression
with handler : Type :=
| Handler : string -> expression -> list (sigmal * string * expression) -> handler. 

Fixpoint forward (ctx:handler * spec) (current:spec) (expr:expression) : spec :=
List.flat_map (fun f =>  
  match f with 
  | Eff s v flow => current
  | Normal v => 
    match expr with 
    | Val v' => [(Normal v')]
    | IfElse _  e1 e2 => 
      let state1 := forward ctx [(Normal v)] e1 in 
      let state2 := forward ctx [(Normal v)] e2 in 
      List.app state1 state2
    | Perform s v => [(Eff s v [(Normal unit)]) ]
    | Resume v => 
      let (han, rest) := ctx in 
      let (x_base, e_base, eff_han) = han in
      List.map (fun f' => ) rest
    | _ => current
    end 
  end 
) current. 
