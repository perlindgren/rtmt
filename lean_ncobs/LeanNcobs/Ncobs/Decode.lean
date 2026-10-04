/-
  The Nested COBS decoder, and reversibility.

  Decoding runs *right to left*, from the sentinel inwards: the last byte of a
  codeword is the final offset, and each offset points back to the position that
  has to be replaced by a zero. `recDecode` therefore consumes the codeword
  structurally from the left while threading its state in from the right, which
  keeps it structurally recursive -- no fuel, no well-founded trickery.

  The decoder never inspects a byte's *value* to decide whether it is data or an
  offset; only its position relative to the counter. That is what makes negative
  payload bytes harmless. It is also the property the parent repo's Why3 test
  vectors never exercised: every one of them uses `41`, i.e. `'A'`.
-/
import LeanNcobs.Ncobs.Encode

namespace Ncobs

/-- Right-to-left decoder walk. Returns the counter state arriving at the left
    edge of the codeword, beside the reconstructed payload. For a well-formed
    codeword that started at `c`, that left-edge state is exactly `c`. -/
def recDecode : List Byte → Int × List Byte
  | [] => (0, [])
  | b :: rest =>
      match rest with
      | [] => (val b, [])
      | _ :: rest' =>
          let (d, out) := recDecode rest
          if d = 1 then (val b, 0 :: out) else (shift d, b :: out)

@[simp] theorem recDecode_nil : recDecode [] = (0, []) := rfl

theorem recDecode_single (b : Byte) : recDecode [b] = (val b, []) := rfl

/-- Two bytes are needed before the state can actually move: the head is data or
    a replacement zero, and only the second byte can carry the next offset. -/
theorem recDecode_cons2 (b r : Byte) (rest : List Byte) :
    recDecode (b :: r :: rest) =
      (if (recDecode (r :: rest)).1 = 1 then
          (val b, 0 :: (recDecode (r :: rest)).2)
        else
          (shift (recDecode (r :: rest)).1, b :: (recDecode (r :: rest)).2)) := rfl

/-- **Reversibility.** A codeword for starting counter `c` and payload `p`
    decodes to `c` and `p`.

    Stated over the specification rather than over `recEncode`, and that is what
    makes the induction close: the counter is an index of `Encodes`, so the
    induction hypothesis arrives already generalized over the successor counter.
    This one lemma subsumes the accumulator-strengthening step the Why3
    development never managed to automate. -/
theorem decode_correct : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → recDecode e = (c, p) := by
  intro p
  induction p with
  | nil =>
      intro c e h
      cases h with
      | stop hc =>
          rw [recDecode_single, val_byte c (offset_to_inRange hc)]
  | cons a as ih =>
      intro c e
      cases e with
      | nil => intro h; cases h
      | cons e0 e1 =>
          intro h
          cases h with
          | zero hc h' =>
              have hi := ih 1 e1 h'
              have ne : e1 ≠ [] := by
                intro hh
                subst hh
                have h1 := congrArg Prod.fst hi
                simp at h1
              obtain ⟨r, rest, rfl⟩ := neNil_eq_cons ne
              rw [recDecode_cons2, hi]
              rw [if_pos rfl, val_byte c (offset_to_inRange hc)]
          | data hc ha h' =>
              have hi := ih (bump c) e1 h'
              have ne : e1 ≠ [] := by
                intro hh
                subst hh
                have h1 := congrArg Prod.fst hi
                simp at h1
                exact bump_ne_zero h1.symm
              obtain ⟨r, rest, rfl⟩ := neNil_eq_cons ne
              rw [recDecode_cons2, hi]
              rw [if_neg (bump_ne_one hc), shift_bump]

/-! ## The protocol interface -/

/-- The transmitted frame: codeword followed by the frame sentinel. -/
def encode (p : List Byte) : List Byte := recEncode (-1) p ++ [0]

/-- Decoding a frame body. The sentinel belongs to the framing layer: for a
    single frame it is just the final byte, and in the nested protocol it is the
    synchronisation point at which a preempted frame gets skipped. -/
def decodeBody (e : List Byte) : List Byte := (recDecode e).2

/-- **Round trip.** -/
theorem decode_encode {p : List Byte} (h : fits (-1) p = true) :
    decodeBody (recEncode (-1) p) = p :=
  congrArg Prod.snd
    (decode_correct p (-1) (recEncode (-1) p) (encodes_of_fits p (-1) h))

/-- Framing soundness: inside a frame the sentinel occurs nowhere. Without this,
    `0` could not delimit anything -- and nesting is precisely the art of
    exploiting its single occurrence. -/
theorem encode_body_sentinel_free {p : List Byte} (h : fits (-1) p = true) :
    ∀ b ∈ recEncode (-1) p, b ≠ 0 :=
  encodes_sentinel_free p (-1) (recEncode (-1) p) (encodes_of_fits p (-1) h)

/-- The overhead is exactly one byte, for every payload, regardless of content.
    That constancy is the "consistent" in consistent overhead byte stuffing. -/
theorem encode_overhead {p : List Byte} (h : fits (-1) p = true) :
    (recEncode (-1) p).length = p.length + 1 :=
  encodes_length p (-1) (recEncode (-1) p) (encodes_of_fits p (-1) h)

/-- Every payload of at most 126 bytes round-trips, whatever it contains. This is
    the headline claim, in one place: `decode_encode` needs `fits`, and
    `fits_of_length_le_126` supplies it without looking at the bytes. -/
theorem decode_encode_of_length_le_126 {p : List Byte} (hp : p.length ≤ 126) :
    decodeBody (recEncode (-1) p) = p :=
  decode_encode (fits_of_length_le_126 hp)

/-- Framing: scan to the next sentinel, then decode what came before it. This is
    the whole of the framing layer for a single frame, and the reason `0` can do
    its job is exactly `encode_body_sentinel_free`. -/
def decodeFrame (s : List Byte) : List Byte := decodeBody (s.takeWhile (· ≠ 0))

/-- Everything up to but excluding the sentinel. The hypothesis is exactly
    `encode_body_sentinel_free`: without it this equation is false, and the
    sentinel would not delimit anything. -/
theorem takeWhile_stop {l : List Byte} (h : ∀ b ∈ l, b ≠ 0) :
    (l ++ [0]).takeWhile (· ≠ 0) = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have ha : a ≠ 0 := h a List.mem_cons_self
      have h1 : (a :: as ++ [0]).takeWhile (· ≠ 0) = a :: (as ++ [0]).takeWhile (· ≠ 0) := by
        simp [List.cons_append, List.takeWhile_cons, ha]
      rw [h1, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- A transmitted frame, decoded from the byte stream, yields the payload. -/
theorem decodeFrame_encode {p : List Byte} (hp : p.length ≤ 126) :
    decodeFrame (encode p) = p := by
  show decodeBody ((recEncode (-1) p ++ [0]).takeWhile (· ≠ 0)) = p
  rw [takeWhile_stop]
  · exact decode_encode_of_length_le_126 hp
  · exact encode_body_sentinel_free (fits_of_length_le_126 hp)

/-- **The decoder does not check canonicality.** Here is a byte string that no
    encoder emits from any counter -- a terminating offset of `-1` is unreachable,
    since `bump x ≠ -1` for every `x` -- which the decoder nonetheless accepts,
    with a legal counter, a sentinel-free codeword, and a payload that passes
    `fits`. The last byte of a real codeword for `[5,7]` would be `-3`.

    So the converse of `decode_correct` fails with the hypotheses one would
    naturally reach for: `recDecode e = (c, p)`, sentinel-free `e`, and `fits c p`
    do not imply `e = recEncode c p`. What is missing is a condition on the
    counters the *decoder's own* right-to-left walk computes, which is not the
    same walk `fits` performs over the payload -- that is precisely why the
    distinction is invisible here. In this example the arriving counter passes
    through `0`, which no encoder state can ever be.

    A framing protocol cannot promise more than this without a checksum, and
    ncobs has none: corruption inside a codeword yields a plausible payload
    rather than a rejection. The consequence worth stating is that `decode_encode`
    is a statement about the encoder's image only, and any receiver-side
    reasoning -- in particular "a skipped preempted frame leaves the outer frame
    intact" -- has to say which codewords it admits, not merely which the
    encoder produces. -/
theorem decoder_accepts_non_canonical :
    recDecode ([5, 7, -1] : List Byte) = (1, [5, 7])
      ∧ (∀ b ∈ ([5, 7, -1] : List Byte), b ≠ 0)
      ∧ fits 1 [5, 7] = true
      ∧ recEncode 1 [5, 7] ≠ ([5, 7, -1] : List Byte) := by
  decide

/-! ## Sanity checks against the Rust implementation

  These are the README's examples, translated into the sign convention the Rust
  encoder and `n_cobs.why` actually use (the README's tables are globally
  sign-flipped relative to its own code). -/

example : encode [] = [-1, 0] := by decide
example : encode [7] = [7, -2, 0] := by decide
example : encode [65, 66, 67] = [65, 66, 67, -4, 0] := by decide
example : encode [65, 0, 67] = [65, -2, 67, 2, 0] := by decide
example : encode [0] = [-1, 1, 0] := by decide
example : encode [0, 0] = [-1, 1, 1, 0] := by decide

/-- A negative payload byte survives: the decoder must not read it as an offset.
    None of the parent repo's Why3 test vectors cover this. -/
example : encode [-5] = [-5, -2, 0] := by decide
example (h : fits (-1) [-5, 0, -128] = true) :
    decodeBody (recEncode (-1) [-5, 0, -128]) = [-5, 0, -128] := decode_encode h

end Ncobs
