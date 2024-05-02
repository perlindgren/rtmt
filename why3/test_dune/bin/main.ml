open N_cobs
open Printf

let () =
  let input = [] in

  (* let l = [ 0 ] in *)
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
  assert (decoded == input)
