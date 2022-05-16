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
  print_string (string_of_int (!x)^"\n");
  Printf.printf "%d\n" ((Obj.magic x) )

let handler 
  (*@ requires true, emp @*)
  (*@ ensures  x=0/\[x=x+1, Norm((), [x=x+1, Norm(())])]  @*)
= 
  match code () with 
  | _ -> ()
  | effect Foo k ->   (continue  k ()); continue k ()