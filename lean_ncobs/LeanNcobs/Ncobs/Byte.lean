/-
  The byte alphabet for Nested COBS.

  We use `Int8`, not `UInt8`: ncobs offsets are *signed*, and the sign is what
  distinguishes "distance back to start-of-frame" from "distance back to a
  replaced zero". Note that payload bytes are transmitted verbatim, so a payload
  may legitimately contain negative bytes; the decoder never tells data from
  offset by value, only by position. (The Why3 test vectors in the parent repo
  all use `41`, so negative data was never exercised there.)

  Design note: the encoder's running offset counter lives in `Int`, and is
  converted to `Int8` only at emission. This keeps wrapping arithmetic out of
  every proof; the cost is that correctness theorems must carry the range
  hypothesis, which is exactly the `Fits` predicate in `Ncobs/Spec.lean`.
-/

namespace Ncobs

/-- A transmitted byte. -/
abbrev Byte := Int8

/-- The frame sentinel. Excluded from every codeword body, which is what makes
    `0` an unambiguous frame delimiter. -/
def sentinel : Byte := 0

/-- An `Int` is representable as a byte. -/
def InRange (c : Int) : Prop := -128 ≤ c ∧ c ≤ 127

theorem inRange_iff (c : Int) : InRange c ↔ -128 ≤ c ∧ c ≤ 127 := Iff.rfl

/-- Legal offsets. Stricter than "representable": the extreme value `-128` is
    *reserved* as the long-frame chaining marker, so a frame whose last run is
    127 bytes -- which would force an offset of `-(127+1) = -128` -- is not a
    legal short frame. Verified empirically against the prototype: a 127-byte
    zero-free payload encodes with final offset `-128` and then crashes its
    decoder, which reads `-128` as "chain" and walks off the front of the frame.
    Reserving the extreme is what makes short frames composable with chaining. -/
def Offset (c : Int) : Prop := -127 ≤ c ∧ c ≤ 127 ∧ c ≠ 0

theorem offset_to_inRange {c : Int} (h : Offset c) : InRange c := by
  simp only [Offset] at h
  exact ⟨by omega, h.2.1⟩
theorem offset_ne_zero {c : Int} (h : Offset c) : c ≠ 0 := h.2.2
theorem offset_ne_reserved {c : Int} (h : Offset c) : c ≠ -128 := by
  simp only [Offset] at h
  omega

/-- Emit an offset as a byte. -/
abbrev byte (c : Int) : Byte := Int8.ofInt c

/-- The byte value carried by a codeword position. -/
abbrev val (b : Byte) : Int := Int8.toInt b

theorem val_byte (c : Int) (h : InRange c) : val (byte c) = c := by
  obtain ⟨h1, h2⟩ := h
  exact Int8.toInt_ofInt_of_le (by omega) (by omega)

/-- Two in-range offsets that are sent as the same byte are equal. This is the
    only place where the byte width could silently break the protocol: two
    distinct offsets collapsing onto one byte. -/
theorem byte_inj {x y : Int} (hx : InRange x) (hy : InRange y) (h : byte x = byte y) :
    x = y := by
  have := congrArg val h
  rwa [val_byte x hx, val_byte y hy] at this

/-- Two bytes that carry the same value are equal. -/
theorem val_injective {a b : Byte} (h : val a = val b) : a = b := by
  have := congrArg Int8.ofInt h
  rwa [Int8.ofInt_toInt, Int8.ofInt_toInt] at this

/-- No nonzero in-range offset is sent as the sentinel. The `c ≠ 0` hypothesis is
    load-bearing, not pedantry: `byte 0 = sentinel`, so the claim is simply false
    without it. Offsets are never `0` by construction (see `bump_ne_zero`). -/
theorem sentinel_ne_byte {c : Int} (h : InRange c) (h0 : c ≠ 0) : byte c ≠ sentinel := by
  intro e
  have e' : byte c = byte (0 : Int) := e
  have := byte_inj h ⟨by omega, by omega⟩ e'
  omega

end Ncobs
