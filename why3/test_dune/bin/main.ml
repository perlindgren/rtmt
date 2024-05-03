open N_cobs
open Printf

let rec makeList v i = if i = 0 then [] else i+1000 :: (makeList v (i-1))

let () =
  (*let input = [] in *)
  let input = makeList 41 260 in
  (* let input = [ 41; 0 ] in *)
  (* let input = [ 0; 41 ] in *)
  (* let input = [ 41; 0; 42 ] in *)
  print_string "Input ";
  List.iter (printf "%d ") input;

  let e = encode (List.map Z.of_int input) in
  let l : int list = List.map Z.to_int e in

  print_string "\nEncoded ";
  List.iter (printf "%d ") l;

  print_string "\nOutput ";
  let d = decode e in
  let decoded = List.map Z.to_int d in
  List.iter (printf "%d ") decoded;
  print_newline ();
  printf "Len input %d, len decoded %d \n " (List.length input) (List.length decoded);
  assert (decoded == input)
