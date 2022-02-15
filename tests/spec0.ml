effect Foo : int -> int
effect Goo : int -> unit
effect Normal : unit -> unit

(*

v = unit | c | x 


L, cont  ::= \/ (pi, flow)
flow     ::= Norm v | Eff (name, v, cont)




L, cont  ::= \/ (res=v, pi, flow)
flow     ::= Norm | Eff (name, v, cont)


L, cont  ::= \/ (pi, flow)
flow     ::= (label, cont)
label    ::= (name, v)




L        ::= \/ (res=v, pi, flow, cont)
flow     ::= Eff (name, arg)
cont     ::= skip | L 
*)

let f () = 
(* req true *)
(* ens res=() /\ x=1+1 /\ 
          flow = Eff(Foo, 1, cont=(res=x+2 /\ TRUE /\ flow=norm)) *)
  let x = 1+1 in 
  let y = perform (Foo 1) in 
  ()

let handler1 = 
  match f() with 
  | _ -> ()
  | effect (Foo x) k -> continue k 100
  (*| effect (Foo x) -> resume 100 *)


let f_if_else () = 
(* req true *)
(* ens res=() /\ x=1+1 /\ 
          flow = Eff(Foo, 1, cont=(res=x+2 /\ TRUE /\ flow=norm)) *)
  let x = 1+1 in 
  let y = perform (Foo 1) in 
  if x >1 then x+2
  else x+3


let fg () = 
(* req true *)
(* ens res=() /\ x = 1+1 /\ flow = (Foo 1) /\  
            cont=(res=x+2 /\ z=x+2 /\ flow=(Goo 2) /\ 
                cont=(res=z+3 /\ flow=norm)) *)
  let x = 1+1 in 
  let y = perform (Foo 1) in 
  let z = x+2 in 
  let w = perform (Goo 2) in 
  z+3

let if_else1 () = 
(* req true *)
(* ens res=() /\ x=1+1 /\ x>1 /\ flow=(Foo 1) /\  
            cont=(res=x+2 /\ flow=norm) 
    \/ res=x+3 /\ x=1+1 /\ !(x>1) /\ flow=norm *)
  let x = 1+1 in 
  if x>1 then 
    let y = perform (Foo 1) in 
    x+2
  else x+3

let if_else2 () = 
(* req true *)
(* ens res=() /\ x=1+1 /\ x>1 /\ flow=(Foo 1) /\  
            cont=(res=x+2 /\ flow=norm) 
    \/ res=() /\ x=1+1 /\ !(x>1) /\ flow=(Goo 2) /\  
            cont=(res=x+3 /\ flow=norm)  *)
  let x = 1+1 in 
  if x>1 then 
    let y = perform (Foo 1) in 
    x+2
  else 
    let y = perform (Goo 2) in 
    x+3


