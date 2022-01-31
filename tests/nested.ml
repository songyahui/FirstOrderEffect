effect Foo : (unit)
effect Goo : (unit)
effect Zoo : (unit)

let print_and_perform_Foo () = 
    print_string ("Foo\n"); perform Foo

let print_and_perform_Goo () = 
    print_string ("Goo\n"); perform Goo

let print_and_perform_Zoo () = 
    print_string ("Zoo\n"); perform Zoo


let f () = 
    print_and_perform_Foo ();
    print_and_perform_Goo ()

let handle = 
    match f () with 
    | _ -> print_string ("Done Outter \n")
    | effect Foo k -> 
        (match print_and_perform_Zoo () with
        | _ -> print_string ("Done Inner \n")
        | effect Zoo kk -> continue k ()
        )
    | effect Goo k -> continue k ()
