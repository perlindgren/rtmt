let rec rec_encode (l: (Z.t) list) : (Z.t) * ((Z.t) list) =
  match l with
  | [] -> (Z.one, Z.zero :: [] )
  | e :: ll ->
    (let (n, ln) = rec_encode ll in
     if Z.equal e Z.zero
     then (Z.one, n :: ln)
     else
       begin
         if Z.equal n (Z.of_string "254")
         then (Z.one, Z.of_string "255" :: e :: ln)
         else (Z.add Z.one n, e :: ln) end)

let rec rec_decode (cn: Z.t) (cl: (Z.t) list) : (Z.t) list =
  match cl with
  | [] -> [] 
  | _ :: ([]) -> [] 
  | e :: ll ->
    if Z.equal cn Z.one
    then
      if Z.equal e (Z.of_string "255")
      then rec_decode (Z.of_string "255") ll
      else Z.zero :: rec_decode e ll
    else e :: rec_decode (Z.sub cn Z.one) ll

let encode (l: (Z.t) list) : (Z.t) list =
  let (cn, cl) = rec_encode l in cn :: cl

let decode (l: (Z.t) list) : (Z.t) list =
  match l with
  | [] -> [] 
  | cn1 :: cl1 -> rec_decode cn1 cl1

let test_encode (_: unit) : (Z.t) list = encode ([] )

let test_encode_41 (_: unit) : (Z.t) list = encode (Z.of_string "41" :: [] )

let test_encode_0 (_: unit) : (Z.t) list = encode (Z.zero :: [] )

let test_encode_41_42_43 (_: unit) : (Z.t) list =
  encode (Z.of_string "41" :: Z.of_string "42" :: Z.of_string "43" :: [] )

let test_encode_41_0_43 (_: unit) : (Z.t) list =
  encode (Z.of_string "41" :: Z.zero :: Z.of_string "43" :: [] )

let test (_: unit) : (Z.t) list = decode (test_encode ())

let test_41 (_: unit) : (Z.t) list = decode (test_encode_41 ())

let test_41_42_43 (_: unit) : (Z.t) list = decode (test_encode_41_42_43 ())

let test_0 (_: unit) : (Z.t) list = decode (test_encode_0 ())

let test_41_0_43 (_: unit) : (Z.t) list = decode (test_encode_41_0_43 ())

