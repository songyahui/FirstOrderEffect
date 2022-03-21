effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
  (*@ requires true, emp @*)
  (*@ ensures  true, Foo!.Foo?(()) @*)
= 
  perform Foo


let handle 
  (*@ requires true, emp @*)
  (*@ ensures  true, Foo.Foo! @*)
=
  match f () with 
  | _ -> ()
  | effect Foo k -> perform Foo; ()
