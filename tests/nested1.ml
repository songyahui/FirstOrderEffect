effect Foo : (unit)
effect Goo : (unit)


let f 
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Foo [Eff(Goo [Normal()])]) @*)
= 
    perform Foo;
    perform Goo

let handler1 
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Goo [Normal()]) @*)
= match f () with 
| _ -> ()
| effect Foo k -> continue k ()

let handler2
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Foo [Normal()]) @*)
= match f () with 
| _ -> ()
| effect Goo k -> continue k ()


let handler3
  (*@ requires true, emp @*)
  (*@ ensures  true, Normal() @*)
= match handler2() with 
| _ -> ()
| effect Foo k ->  ()

