effect Foo : (unit)
effect Goo : (unit)


let f 
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Foo [Eff(Goo [Normal()])and hist = Goo ]) @*) hist = Foo
= 
    perform Foo;
    perform Goo

let handler1 
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Goo [Normal()]) @*) hist=Foo.H(Foo).Goo
= match f () with 
| _ -> ()
| effect Foo k -> continue k ()

let handler2
  (*@ requires true, emp @*)
  (*@ ensures  true, Eff(Foo [Normal()]) @*) hist=Foo.Goo.H(Goo)
= match f () with 
| _ -> 
| effect Goo k -> continue k ()


let handler3
  (*@ requires true, emp @*)
  (*@ ensures  true, Normal() @*) 
= match handler2() with 
| _ -> ()
| effect Foo k ->  ()

