/-
  The Nested COBS *specification*: what a codeword means, independent of any
  algorithm that produces one.

  Method. The parent repo's Why3 development contains both a design that worked
  and one that did not. `cobs_simple.why` states the protocol as an inductive
  relation, and reversibility is fully proven there. `n_cobs.why` states it as a
  function with `ensures` postconditions, and its session file carries 63
  recorded proof attempts with no completed proof. This file follows the former.

  Why that choice decides the outcome. The running offset `c` is what makes these
  proofs hard. As a postcondition it has to be smuggled into the induction
  hypothesis by hand, which is exactly where Alt-Ergo and CVC5 gave up. As an
  *index* of the relation it is generalized for free: the induction hypothesis
  arrives already quantified over the successor counter.
-/
import LeanNcobs.Ncobs.Byte

namespace Ncobs

/-- Offset counter update when a nonzero data byte is consumed: magnitude grows
    by one, sign is preserved. -/
def bump (c : Int) : Int := if c < 0 then c - 1 else c + 1

/-- Inverse of `bump`: the counter as it was one data byte earlier. -/
def shift (d : Int) : Int := if d > 0 then d - 1 else d + 1

theorem bump_neg {c : Int} (h : c < 0) : bump c = c - 1 := if_pos h
theorem bump_pos {c : Int} (h : 0 < c) : bump c = c + 1 := if_neg (by omega)

theorem bump_ne_zero {c : Int} : bump c ≠ 0 := by
  unfold bump
  split <;> omega

/-- Hypothesis-free, which is worth having: the decoder's undoing step never
    depends on a fact the decoder cannot itself check. -/
theorem shift_bump {c : Int} : shift (bump c) = c := by
  unfold bump shift
  split <;> split <;> omega

theorem bump_ne_one {c : Int} (h : c ≠ 0) : bump c ≠ 1 := by
  by_cases hc : c < 0
  · rw [bump_neg hc]; omega
  · rw [bump_pos (by omega)]; omega

/-- Decidable form of `Offset`. -/
def ok (c : Int) : Bool := -127 ≤ c && c ≤ 127 && c ≠ 0

theorem ok_iff {c : Int} : ok c = true ↔ Offset c := by
  simp only [ok, Offset, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  omega

/-- An in-range nonzero offset is never sent as the sentinel. -/
theorem byte_ne_sentinel {x : Int} (hx : Offset x) : byte x ≠ 0 := by
  have h1 : -127 ≤ x := hx.1
  have h2 : x ≤ 127 := hx.2.1
  intro contra
  have h1' : Int8.toInt (Int8.ofInt x) = x := Int8.toInt_ofInt_of_le (by omega) (by omega)
  have h2' : Int8.toInt (0 : Int8) = (0 : Int) := rfl
  have := congrArg Int8.toInt contra
  rw [h1', h2'] at this
  exact hx.2.2 this

/-! ## The specification -/

/-- `Encodes c p e`: starting with running offset `c`, payload `p` encodes to
    codeword `e`.

    `e` excludes the trailing frame sentinel. Its last byte is always the final
    offset, which is why `e` has exactly one byte more than `p`.

    Read right-to-left, as the protocol decodes:
    - `stop`: payload exhausted; emit the final offset byte.
    - `zero`: a payload zero is replaced by the current offset byte; the counter
      restarts at `+1`.
    - `data`: a nonzero payload byte passes through verbatim, *including negative
      bytes* -- which is what forces the decoder to decide by position rather
      than by value.

    Every constructor demands `c ≠ 0` at the position it stands at, and each
    sub-counter is then nonzero by `bump_ne_zero` (or is `+1`). So nonzero-ness
    holds at every position, not just at emission points. That is stricter than
    framing needs: `bump 0 = 1` flips the counter's sign, so a zero counter
    corrupts the codeword even where nothing is emitted. -/
inductive Encodes : Int → List Byte → List Byte → Prop where
  | stop : ∀ {c : Int}, Offset c → Encodes c [] [byte c]
  | zero : ∀ {c : Int} {p e : List Byte}, Offset c →
      Encodes 1 p e → Encodes c (0 :: p) (byte c :: e)
  | data : ∀ {c : Int} {b : Byte} {p e : List Byte}, c ≠ 0 → b ≠ 0 →
      Encodes (bump c) p e → Encodes c (b :: p) (b :: e)

/-! The lemmas below are stated with the payload as the *first* binder, so that
`induction p` forms the motive with the counter and codeword still to be
introduced. Inducting on the derivation instead is impossible: `zero` hard-codes
its sub-counter as the literal `1`, and a literal in an index position stops
Lean from abstracting that premise into an induction hypothesis. -/

/-- No emitted byte is ever the sentinel: the property that makes `0` a sound
    frame delimiter, and therefore the property that makes nesting parseable. -/
theorem encodes_sentinel_free : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → ∀ b ∈ e, b ≠ 0 := by
  intro p
  induction p with
  | nil =>
      intro c e h
      cases h with
      | stop hc =>
          intro b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact byte_ne_sentinel hc
  | cons a as ih =>
      intro c e h
      cases h with
      | zero hc h' =>
          intro b hb
          rw [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact byte_ne_sentinel hc
          · exact ih 1 _ h' b hb
      | data _ ha h' =>
          intro b hb
          rw [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact ha
          · exact ih _ _ h' b hb

theorem encodes_counter_ne_zero : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → c ≠ 0 := by
  intro p
  induction p with
  | nil => intro c e h; cases h with | stop hc => exact offset_ne_zero hc
  | cons a as ih =>
      intro c e h
      cases h with
      | zero hc _ => exact offset_ne_zero hc
      | data h0 _ _ => exact h0

/-- Codewords are exactly one byte longer than their payload. Nesting needs this
    badly: skipping a preempted inner frame costs its *encoded* length, and this
    is the only thing that converts that from the decoded length.
    `n_cobs_nested.why` uses the decoded length directly and never states the
    relation between the two, which is a large part of why it never closed. -/
theorem encodes_length : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → e.length = p.length + 1 := by
  intro p
  induction p with
  | nil => intro c e h; cases h with | stop => rfl
  | cons a as ih =>
      intro c e h
      cases h with
      | zero _ h' =>
          have hi := ih 1 _ h'
          simp only [List.length_cons] at *
          omega
      | data _ _ h' =>
          have hi := ih _ _ h'
          simp only [List.length_cons] at *
          omega

theorem encodes_nonempty : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → e ≠ [] := by
  intro p
  induction p with
  | nil => intro c e h; cases h with | stop => simp
  | cons a as ih =>
      intro c e h
      cases h with
      | zero => simp
      | data => simp

theorem neNil_eq_cons {α : Type} {l : List α} (h : l ≠ []) : ∃ a l', l = a :: l' := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l' => exact ⟨a, l', rfl⟩

end Ncobs
