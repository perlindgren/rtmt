let rec fn_next_0 (l: (Z.t) list) : (Z.t) * ((Z.t) list) =
  match l with
  | [] -> (Z.one, Z.zero :: [] )
  | e :: ll ->
    (let (n, ln) = fn_next_0 ll in
     if Z.equal e Z.zero then (Z.one, n :: ln) else (Z.add Z.one n, e :: ln))

let rec fn_encode (l: (Z.t) list) : (Z.t) list =
  let (n1, ll) = fn_next_0 l in n1 :: ll

let rec fn_next_decode (l: (Z.t) list) (n2: Z.t) : (Z.t) list =
  match l with
  | [] -> [] 
  | e :: ll1 ->
    if Z.equal e Z.zero
    then [] 
    else
      begin
        if Z.equal n2 Z.one
        then Z.zero :: fn_next_decode ll1 e
        else e :: fn_next_decode ll1 (Z.sub n2 Z.one) end

let rec fn_decode (l: (Z.t) list) : (Z.t) list =
  match l with
  | [] -> [] 
  | n2 :: ll1 -> fn_next_decode ll1 n2

