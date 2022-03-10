effect Foo : (unit -> unit)

let f () = 
    let x = perform Foo in 
    x ()

let handle = 
    match f () with 
    | _ -> ()
    | effect Foo k -> continue k (fun () -> perform Foo ())
