effect Foo : (unit)
effect Goo : (unit)

let print_and_perform_Foo () = 
    print_string ("Foo\n"); perform Foo

let print_and_perform_Goo () = 
    print_string ("Goo\n"); perform Goo


let f () = 
    print_and_perform_Foo ();
    print_and_perform_Goo () 

let handle = 
    match f () with 
    | _ -> print_string ("Done\n")
    | effect Foo k -> continue k (); print_string ("After Foo\n")
    | effect Goo k -> continue k (); print_string ("After Goo\n")
