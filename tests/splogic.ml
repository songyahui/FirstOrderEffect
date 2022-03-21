effect Foo : unit

let f () 
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Foo) @*)
= 
  perform Foo 

let code () 
  (*@ requires true, emp @*)
  (*@ ensures  x=0/\Eff(Foo, [x=x+1, Norm((), [])])  @*)
= 
  let x = ref 0 in
  f();
  x := !x + 1;
  (*assert (!x = 1) *)

let handler 
  (*@ requires true, emp @*)
  (*@ ensures  x=0/\[x=x+1, Norm((), [x=x+1, Norm(())])]  @*)
= 
  match code () with 
  | _ -> ()
  | effect Foo k ->   (continue (Obj.clone_continuation k) ()); continue k ()