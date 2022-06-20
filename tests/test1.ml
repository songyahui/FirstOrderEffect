effect Foo : (int)


(* Example 1 *)
let f1 () = 
    (perform Foo) + 1 

let handle1 () = 
    (match f1 () with 
    | v -> v
    | effect Foo k -> continue k 2
    )

let main1 = print_string (string_of_int (handle1 ()) ^ "\n")

(*
(display  
        (+ 1 (call/cc
        (lambda (k)
          (k 2)))))
*)

(* Example 2 *)
let f2 () = 
    (perform Foo) + 1 

let handle2 () = 
    5 + 
    (match f2 () with 
    | v -> v
    | effect Foo k -> continue k 2
    )

let main2 = print_string (string_of_int (handle2 ()) ^ "\n")

(*
(display (+ 5 
        (+ 1 (call/cc
        (lambda (k)
          (k 2))))))
*)

(* Example 3 Abanden the continueation *)
let f3 () = 
    (perform Foo) + 1 

let handle3 () = 
    (match f3 () with 
    | v -> v
    | effect Foo k -> 10
    )

let main3 = print_string (string_of_int (handle3 ()) ^ "\n")

(*
(display  
        reset (+ 1 (shift (fun k -> 10 )
        (lambda (k)
          10))))
*)
