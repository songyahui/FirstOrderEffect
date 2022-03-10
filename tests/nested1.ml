effect Foo : (unit)
effect Goo : (unit)

let print_and_perform_Foo () = 
    print_string ("Foo\n"); perform Foo

let f () = 
    print_and_perform_Foo ()

let handler1 () = 
    match f () with 
    | _ -> print_string ("Done  handler1 \n")
    | effect Goo k -> continue k ()

let handler2 = 
    match handler1 () with 
    | _ -> print_string ("Done  handler2 \n")
    | effect Foo k -> continue k ()

