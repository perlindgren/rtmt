/-
  The Nested COBS encoder, and the proof that it meets the specification.

  The encoder is *online*: it buffers nothing, and a preempting frame may
  interleave between any two of its steps. That is the entire point of the
  protocol, so this model deliberately mirrors the incremental Rust one
  (`src/short_frame_encode.rs`) rather than a whole-buffer pass.

  The running counter lives in `Int`; only `byte c` ever sees the byte width.
  That is not cosmetic -- `omega` in Lean 4.34 has no `Int8` support at all, it
  treats `Int8.toInt` as an opaque atom, so keeping the arithmetic in `Int` is
  what makes these proofs automatable. The cost is that correctness theorems
  must carry a range hypothesis, which is what `fits` and `Legit` are for.
-/
import LeanNcobs.Ncobs.Spec

namespace Ncobs

/-- `recEncode c p` encodes payload `p` from running offset `c`, producing the
    codeword *without* the trailing frame sentinel. -/
def recEncode : Int → List Byte → List Byte
  | c, [] => [byte c]
  | c, b :: bs => if b = 0 then byte c :: recEncode 1 bs
                  else b :: recEncode (bump c) bs

-- Stated as `rfl` so every proof below rewrites against a fixed shape, rather
-- than against whatever equation lemmas happen to be generated this release.
@[simp] theorem recEncode_nil (c : Int) : recEncode c [] = [byte c] := rfl

@[simp] theorem recEncode_cons (c : Int) (b : Byte) (bs : List Byte) :
    recEncode c (b :: bs) =
      (if b = 0 then byte c :: recEncode 1 bs else b :: recEncode (bump c) bs) := rfl

/-- **Completeness of the specification.** `Encodes` admits nothing that
    `recEncode` would not produce. -/
theorem Encodes.eq_recEncode : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → e = recEncode c p := by
  intro p
  induction p with
  | nil => intro c e h; cases h with | stop => rw [recEncode_nil]
  | cons a as ih =>
      intro c e
      cases e with
      | nil => intro h; cases h
      | cons e0 e1 =>
          intro h
          cases h with
          | zero _ h' =>
              rw [recEncode_cons, ih 1 _ h']
              simp only [reduceIte]
          | data _ ha h' => rw [recEncode_cons, if_neg ha, ih _ _ h']

/-- Determinism, derived from the bridge above: a payload and starting counter
    fix the codeword. -/
theorem encodes_unique : ∀ {p : List Byte} {e e' : List Byte} {c : Int},
    Encodes c p e → Encodes c p e' → e = e' := fun h h' => by
  rw [Encodes.eq_recEncode _ _ _ h, Encodes.eq_recEncode _ _ _ h']

/-! ## Well-formedness -/

/-- Decidable well-formedness of a payload under a running counter: at every
    position the counter must be a legal offset. Checked at *every* position, not
    only at emission points, matching the `c ≠ 0` premise of `Encodes.data`. -/
def fits : Int → List Byte → Bool
  | c, [] => ok c
  | c, b :: bs => ok c && if b = 0 then fits 1 bs else fits (bump c) bs

@[simp] theorem fits_nil (c : Int) : fits c [] = ok c := rfl

@[simp] theorem fits_cons (c : Int) (b : Byte) (bs : List Byte) :
    fits c (b :: bs) = (ok c && if b = 0 then fits 1 bs else fits (bump c) bs) := rfl

/-- Everything that fits is encodable. -/
theorem encodes_of_fits : ∀ (p : List Byte) (c : Int),
    fits c p = true → Encodes c p (recEncode c p) := by
  intro p
  induction p with
  | nil =>
      intro c h
      rw [fits_nil] at h
      exact Encodes.stop (ok_iff.mp h)
  | cons a as ih =>
      intro c h
      rw [fits_cons] at h
      by_cases ha : a = 0
      · subst ha
        simp only [Bool.and_eq_true, if_pos (rfl : (0 : Byte) = 0)] at h
        obtain ⟨hok, hrest⟩ := h
        rw [recEncode_cons, if_pos (rfl : (0 : Byte) = 0)]
        exact Encodes.zero (ok_iff.mp hok) (ih 1 hrest)
      · simp only [Bool.and_eq_true, if_neg ha] at h
        obtain ⟨hok, hrest⟩ := h
        rw [ok_iff] at hok
        rw [recEncode_cons, if_neg ha]
        exact Encodes.data hok.2.2 ha (ih (bump c) hrest)

/-! ## Deriving the numerical bound

  `fits` is an honest hypothesis, but the protocol's advertised claim is "one
  byte of overhead for frames up to 127 bytes". That bound should be a
  consequence, not an assumption, so it is derived below. -/

/-- `Legit n c p`: `p` is the suffix of a frame of total length `n`, and `c` is a
    counter that can genuinely occur there.

    The asymmetry is the whole story. A *negative* counter has seen only data
    bytes since the frame began, so `-c` counts those plus one, bounded by
    `n + 1`. A *positive* counter means a zero has already been replaced, so at
    least one of the `n` bytes lies behind it, giving the tighter `c ≤ n`. That
    one-byte asymmetry is exactly why the negative side can reach `-128` while
    the positive side stops at `127` -- and hence why the short-frame limit is
    127 rather than 126. -/
def Legit (n : Nat) (c : Int) (p : List Byte) : Prop :=
  (p.length : Int) ≤ (n : Int) ∧ c ≠ 0
    ∧ (c < 0 → -c ≤ (n : Int) - p.length + 1)
    ∧ (0 < c → (c : Int) ≤ (n : Int) - p.length)

/-- The heart of the bound. A *negative* counter has consumed nothing but data
    since the frame began, so `-c` is that count plus one, at most `n + 1`; the
    binding constraint is therefore `-c ≤ 127`, i.e. a frame of at most 126
    bytes. A *positive* counter additionally has a replaced zero behind it,
    granting it one byte of slack it cannot use. The old `-128` bound was exactly
    this byte -- and `-128` is precisely what a 127-byte frame was forced to
    emit, which is the collision that broke the prototype. -/
theorem legit_ok {n : Nat} {c : Int} {p : List Byte} (hl : Legit n c p)
    (hn : n ≤ 126) : ok c = true := by
  obtain ⟨h1, hne, hneg, hpos⟩ := hl
  have key : -127 ≤ c ∧ c ≤ 127 := by
    by_cases hc : c < 0
    · have hle := hneg hc
      exact ⟨by omega, by omega⟩
    · have hlt : 0 < c := by omega
      have hle := hpos hlt
      refine ⟨by omega, by omega⟩
  simp [ok, Offset, key, hne]

/-- Note there is no `b ≠ 0` hypothesis: `Legit` constrains the counter and the
    remaining length, neither of which depends on the payload head's value. -/
theorem legit_data {n : Nat} {c : Int} {b : Byte} {p : List Byte}
    (hl : Legit n c (b :: p)) : Legit n (bump c) p := by
  obtain ⟨h1, _, hneg, hpos⟩ := hl
  have hlen : (p.length : Int) + 1 ≤ (n : Int) := by
    have hcons : ((b :: p).length : Int) = (p.length : Int) + 1 := by simp
    omega
  have hneg' : c < 0 → -c ≤ (n : Int) - p.length := by
    intro hc
    have hle := hneg hc
    simp at hle
    omega
  have hpos' : 0 < c → (c : Int) ≤ (n : Int) - p.length - 1 := by
    intro hc
    have hle := hpos hc
    simp at hle
    omega
  refine ⟨by omega, bump_ne_zero, ?_, ?_⟩
  · intro hnew
    by_cases hc : c < 0
    · rw [bump_neg hc] at hnew ⊢
      have hle := hneg' hc
      omega
    · rw [bump_pos (by omega)] at hnew
      omega
  · intro hnew
    by_cases hc : c < 0
    · rw [bump_neg hc] at hnew
      omega
    · rw [bump_pos (by omega)] at hnew ⊢
      have hle := hpos' (by omega)
      omega

theorem legit_zero {n : Nat} {c : Int} {p : List Byte}
    (hl : Legit n c (0 :: p)) : Legit n 1 p := by
  obtain ⟨h1, _, _, _⟩ := hl
  have hlen : (p.length : Int) + 1 ≤ (n : Int) := by
    have : ((0 :: p).length : Int) = (p.length : Int) + 1 := by simp
    omega
  refine ⟨by omega, by omega, fun h => by omega, fun _ => ?_⟩
  omega

/-- A frame of at most 127 bytes fits, so it costs exactly one byte of overhead.
    This is the README's headline claim, as a theorem. -/
theorem fits_of_legit : ∀ (p : List Byte) (n : Nat), n ≤ 126 →
    ∀ (c : Int), Legit n c p → fits c p = true := by
  intro p
  induction p with
  | nil => intro n hn c hl; rw [fits_nil]; exact legit_ok hl hn
  | cons a as ih =>
      intro n hn c hl
      by_cases ha : a = 0
      · rw [fits_cons, if_pos ha, Bool.and_eq_true]
        exact ⟨legit_ok hl hn, ih n hn 1 (legit_zero hl)⟩
      · rw [fits_cons, if_neg ha, Bool.and_eq_true]
        exact ⟨legit_ok hl hn, ih n hn (bump c) (legit_data hl)⟩

theorem fits_of_length_le_126 {p : List Byte} (hp : p.length ≤ 126) :
    fits (-1) p = true :=
  fits_of_legit p p.length (by omega) (-1)
    ⟨by omega, by omega, fun h => by omega, fun h => by omega⟩

/-- Hence every short frame is encodable. -/
theorem encodable_of_length_le_126 {p : List Byte} (hp : p.length ≤ 126) :
    ∃ e, Encodes (-1) p e :=
  ⟨recEncode (-1) p, encodes_of_fits _ _ (fits_of_length_le_126 hp)⟩

end Ncobs
