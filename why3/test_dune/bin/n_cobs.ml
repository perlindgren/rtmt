let rec rec_encode (l: (Z.t) list) : (Z.t) * ((Z.t) list) =
  match l with
  | [] -> (Z.one, Z.zero :: [] )
  | e :: ll ->
    (let (n, ln) = rec_encode ll in
     if Z.equal e Z.zero then (Z.one, n :: ln) else (Z.add Z.one n, e :: ln))

let encode (l: (Z.t) list) : (Z.t) list =
  let (n1, ll) = rec_encode l in n1 :: ll

let rec rec_decode (n2: Z.t) (l: (Z.t) list) : (Z.t) list =
  match l with
  | [] -> assert false (* absurd *)
  | _e :: ([]) -> [] 
  | e :: ll1 ->
    begin match Z.equal n2 Z.one with
    | true -> Z.zero :: rec_decode e ll1
    | false -> e :: rec_decode (Z.sub n2 Z.one) ll1
    end

let decode (l: (Z.t) list) : (Z.t) list =
  match l with
  | [] -> assert false (* absurd *)
  | cn :: cl -> rec_decode cn cl

