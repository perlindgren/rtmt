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

