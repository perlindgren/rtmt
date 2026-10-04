import LeanNcobs

open Ncobs Ncobs.Online Ncobs.Online

/-- Payloads covering the interesting cases: empty, zero-free, zeros at both
    ends, a zero run, and negative payload bytes (which the Rust convention
    encodes as offsets that a value-based decoder would misread). -/
def samples : List (List Byte) :=
  [[], [7], [65, 66, 67], [65, 0, 67], [0], [0, 0], [0, 0, 0], [-5], [-5, 0, -128],
    List.replicate 126 65, List.replicate 127 65]

def hexByte (b : Byte) : String := s!"{Int8.toInt b}"

def showBytes (l : List Byte) : String :=
  "[" ++ String.intercalate ", " (l.map hexByte) ++ "]"

def verdict (p : List Byte) : String :=
  if fits (-1) p != true then "unencodable (too long)"
  else if decodeBody (recEncode (-1) p) == p then "round-trips"
  else "MISMATCH"

def main : IO Unit := do
  IO.println "Nested COBS — single-frame encoder"
  IO.println "payload → frame (sign convention of the Rust implementation)\n"
  for p in samples do
    IO.println s!"  {showBytes p}
      → {showBytes (encode p)}   [{verdict p}]  (overhead {(encode p).length - p.length})"

  IO.println "\nDriving the frame one byte at a time -- each line is a legal preemption point:"
  let p : List Byte := [65, 0, 66, 0, 67, 0]
  let rec go (s : State) (l : List Byte) (acc : List Byte) : IO Unit := do
    match l with
    | [] =>
        IO.println s!"      frameEnd: {showBytes (frameEnd s)}   full frame: {showBytes (acc ++ frameEnd s)}"
        IO.println s!"      batch encoder agrees: {acc ++ frameEnd s == encode p}"
    | b :: rest =>
        let (out, s') := step s b
        IO.println s!"      byte {hexByte b} -> emitted {showBytes out}, counter now {s'.c}, sent so far {showBytes (acc ++ out)}"
        go s' rest (acc ++ out)
  go frameBegin p []
