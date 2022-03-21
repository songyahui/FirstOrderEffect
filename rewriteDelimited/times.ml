let print_time a b = print_string (string_of_int a ^ "*" ^ string_of_int b ^"\n"); a * b

effect Zero : int 

let rec times' lst 
  (*@ requires true, emp @*)
  (*@ ensures  true, emp \/ Zero @*)
= 
  match lst with
  | [] -> 1
  | 0 :: rest -> perform Zero 
  | first :: rest -> print_time first (times' rest)

let handler lst 
  (*@ requires true, emp @*)
  (*@ ensures  true, emp \/ Zero @*)
=
  match times' lst with 
  | n -> n  
  | effect Zero k -> print_string("Discard the continuation!\n"); 0 

let main = handler [1;2;3;4;0]

