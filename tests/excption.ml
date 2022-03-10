effect Foo : (unit)

let print_and_perform_Foo () = 
    print_string ("Foo\n"); perform Foo

let f () = 
    print_and_perform_Foo ()

let handle = 
    match f () with 
    | _ -> print_string ("Done\n\n")
    | effect Foo k -> ()
