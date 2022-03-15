let print_time a b = print_string (string_of_int a ^ "*" ^ string_of_int b ^"\n"); a * b

let rec times lst = 
  match lst with
  | [] -> 1
  | 0 :: rest -> 0 
  | first :: rest -> print_time first (times rest)

effect Zero : int 

let rec times' lst = 
  match lst with
  | [] -> 1
  | 0 :: rest -> perform Zero 
  | first :: rest -> print_time first (times' rest)

let handler lst =
  match times' lst with 
  | n -> n  
  | effect Zero k -> print_string("Discard the continuation!\n"); 0 

let main = handler [1;2;3;4;0]


(*
let rec times lst = 
  match lst with
  | [] -> 1
  | 0 :: rest -> 0 
  | first :: rest -> 
    let restT = times rest in 
    let res = first * restT in 
    print_string (string_of_int first ^ "*" ^ string_of_int restT ^ "\n");
    res 

effect Zero : int 

let rec times1 lst = 
  match lst with
  | [] -> 1
  | 0 :: rest -> perform Zero 
  | first :: rest -> 
      let restT = times1 rest in 
    let res = first * restT in 
    print_string (string_of_int first ^ "*" ^ string_of_int restT ^ "\n");
    res 

let handler lst =
  match times1 lst with 
  | n -> n  
  | effect Zero k -> 0 

let main = handler [1;2;3;4;0]
*)