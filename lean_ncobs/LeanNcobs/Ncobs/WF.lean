/-
  Which codewords the receiver admits.

  `Encodes` describes what the encoder emits and `recDecode` what the receiver
  returns; nothing yet connected the two, and they do not agree -- the decoder
  accepts byte strings no encoder produces. What separates them is the sequence of
  counters the decoder itself computes while walking the codeword right to left.
  That walk is *not* the walk `fits` performs over the payload, which is why the
  hypotheses one would naturally reach for were not enough.
-/
import LeanNcobs.Ncobs.Online

namespace Ncobs

/-- Mirrors `recDecode`'s recursion exactly, accumulating a flag: whether every
    offset the walk actually consumes is a legal offset, and whether every byte it
    treats as data is nonzero. The second component is the counter arriving at the
    left edge, identical to the one `recDecode` returns.

    A byte counts as an offset exactly where the arriving counter is `1` -- that
    is the position the encoder overwrote with a distance -- together with the
    final byte, which carries the terminating offset. Offsets must satisfy `ok`,
    so in particular they are never `-128`, the reserved chaining marker. Data
    bytes are unconstrained except for being nonzero: any payload byte, `-128`
    included, may legitimately appear as data. -/
def walk : List Byte → Bool × Int
  | [] => (true, 0)
  | [b] => (ok (val b), val b)
  | b :: r :: rest =>
      let w := walk (r :: rest)
      if w.2 = 1 then (w.1 && ok (val b), val b)
      else (w.1 && decide (b ≠ 0) && ok (shift w.2), shift w.2)

/-- A codeword is well formed when the walk stays legal throughout. Nonemptiness
    is part of it: the empty codeword carries no terminating offset at all, and
    without this conjunct `[]` would be admitted with counter `0`. -/
def wfCodeword (e : List Byte) : Bool := (walk e).1 && decide (e ≠ [])

@[simp] theorem walk_nil : walk [] = (true, 0) := rfl
theorem walk_single (b : Byte) : walk [b] = (ok (val b), val b) := rfl
theorem walk_cons2 (b r : Byte) (rest : List Byte) :
    walk (b :: r :: rest) =
      (let w := walk (r :: rest)
       if w.2 = 1 then (w.1 && ok (val b), val b)
       else (w.1 && decide (b ≠ 0) && ok (shift w.2), shift w.2)) := rfl

/-- The walk tracks the decoder exactly -- same recursion, same counter. -/
theorem walk_snd_eq_recDecode_fst : ∀ e : List Byte, (walk e).2 = (recDecode e).1 := by
  intro e
  induction e with
  | nil => rw [walk_nil, recDecode_nil]
  | cons b rest rest_ih =>
      cases rest with
      | nil => rw [walk_single, recDecode_single]
      | cons r rest' =>
          rw [walk_cons2, recDecode_cons2, ← rest_ih]
          cases h2 : walk (r :: rest') with
          | mk f d => simp only [Prod.fst, Prod.snd]; split <;> simp

/-- Nonemptiness is needed: on the empty codeword the walk lands on counter `0`,
    which is why `wfCodeword` conjoins it separately. -/
theorem walk_fst_implies_ok : ∀ e : List Byte,
    (walk e).1 = true → e ≠ [] → ok (walk e).2 = true := by
  intro e
  induction e with
  | nil => intro _ hne; exact absurd rfl hne
  | cons b rest rest_ih =>
      cases rest with
      | nil => intro h _; rw [walk_single] at h ⊢; exact h
      | cons r rest' =>
          intro h _
          rw [walk_cons2] at h ⊢
          generalize hd : walk (r :: rest') = w at h ⊢
          cases w with
          | mk f d =>
              simp only [Prod.fst, Prod.snd] at h ⊢
              by_cases h1 : d = 1
              · rw [if_pos h1] at h ⊢; rw [Bool.and_eq_true] at h; exact h.2
              · rw [if_neg h1] at h ⊢
                rw [Bool.and_eq_true, Bool.and_eq_true] at h
                exact h.2

/-! ## The arithmetic the characterization needs -/

/-- The decoder steps counters with `shift`, the spec with `bump`. Off `1` and
    `-1` they are inverse; `d ≠ 1` is the decoder's own branch test and `ok c`
    excludes `d = -1`, since `shift (-1) = 0`. Everything else about
    `encodes_of_wfCodeword` is bookkeeping on top of this. -/
theorem bump_of_shift {c d : Int} (hc : ok c = true) (hd : ok d = true)
    (h1 : d ≠ 1) (hs : shift d = c) : bump c = d := by
  -- Only nonzeroness matters, not the ranges: `bump (shift x) = x` fails exactly
  -- at `x = -1`, whose shift is `0`, and at `x = 1`, which is the branch test.
  have key : ∀ x : Int, x ≠ 0 → shift x ≠ 0 → x ≠ 1 → bump (shift x) = x := by
    intro x hx0 hsx0 hx1
    by_cases h : x > 0
    · rw [show shift x = x - 1 from if_pos h, bump] at *
      by_cases h2 : x - 1 < 0
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
    · rw [show shift x = x + 1 from if_neg h, bump] at *
      by_cases h2 : x + 1 < 0
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
  rw [← hs]
  exact key d (ok_iff.mp hd).2.2 (by rw [hs]; exact (ok_iff.mp hc).2.2) h1

--  The remaining plumbing for the characterization is a suffix lemma -- that a
--   well-formed codeword has well-formed tails, so an induction may run on the
--   tail the decoder recursed into. It is bookkeeping over `walk`'s pairs, not
--   arithmetic, and `bump_of_shift` above is the only real content
--   `encodes_of_wfCodeword` needs beyond it. Both directions are checked
-- exhaustively in `Test.lean` in the meantime. -/

/-- `let`-free form of the two-cons step. `walk`'s equation as written binds a
    `let`, and projections do not reduce through it, which is what stalled every
    proof that tried to case on the walk's pair. -/
@[simp] theorem walk_cons2' (b r : Byte) (rest : List Byte) :
    walk (b :: r :: rest) =
      (if (walk (r :: rest)).2 = 1 then
          ((walk (r :: rest)).1 && ok (val b), val b)
        else
          ((walk (r :: rest)).1 && decide (b ≠ 0) && ok (shift (walk (r :: rest)).2),
            shift (walk (r :: rest)).2)) := rfl

/-- The two-cons equation only fires when the tail is literally a cons, but a
    codeword tail is a stuck `recEncode` call. This is the form proofs actually
    need. -/
theorem walk_cons {b : Byte} {rest : List Byte} (hrest : rest ≠ []) :
    walk (b :: rest) =
      (if (walk rest).2 = 1 then
          ((walk rest).1 && ok (val b), val b)
        else
          ((walk rest).1 && decide (b ≠ 0) && ok (shift (walk rest).2),
            shift (walk rest).2)) := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons r rest' => exact walk_cons2' b r rest'

/-- A codeword is never empty; it always carries a terminating offset. -/
theorem recEncode_nonempty (c : Int) (p : List Byte) : recEncode c p ≠ [] := by
  induction p with
  | nil => intro h; rw [recEncode_nil] at h; cases h
  | cons a as ih =>
      intro h
      rw [recEncode_cons] at h
      split at h <;> cases h

/-- The legality flag is the first component, so it survives elimination. -/
theorem wf_fst {e : List Byte} (h : wfCodeword e = true) : (walk e).1 = true := by
  rw [wfCodeword, Bool.and_eq_true] at h
  exact h.1

/-- `ok` descends through `bump`. `bump` preserves sign and grows magnitude by
    one, so a legal successor offset has a legal predecessor. -/
theorem ok_of_bump {c : Int} (h0 : c ≠ 0) (h : ok (bump c) = true) : ok c = true := by
  rw [ok_iff] at h ⊢
  simp only [Offset] at h ⊢
  by_cases hc : c < 0
  · rw [bump_neg hc] at h
    exact ⟨by omega, by omega, by omega⟩
  · rw [bump_pos (by omega)] at h
    exact ⟨by omega, by omega, by omega⟩

/-- **The spec is stricter than its premises look.** The `data` rule only asks
    for `c ≠ 0`, so on its face a derivation could pass through an illegal
    counter. It cannot: `bump` grows magnitude monotonically and never changes
    sign, so every counter before an emission is bounded by the one that is
    emitted, and emissions demand `ok`. -/
theorem fits_of_encodes : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → fits c p = true := by
  intro p
  induction p with
  | nil => intro c e h; cases h with | stop hc => rw [fits_nil]; exact ok_iff.mpr hc
  | cons a as ih =>
      intro c e h
      rw [fits_cons]
      cases h with
      | zero hc h' =>
          rw [if_pos (rfl : (0 : Byte) = 0), Bool.and_eq_true]
          exact ⟨ok_iff.mpr hc, ih 1 _ h'⟩
      | data hc ha h' =>
          rw [if_neg ha, Bool.and_eq_true]
          have hi := ih _ _ h'
          have hok : ok (bump c) = true := by
            cases as with
            | nil => rw [fits_nil] at hi; exact hi
            | cons b bs => rw [fits_cons, Bool.and_eq_true] at hi; exact hi.1
          exact ⟨ok_of_bump hc hok, hi⟩

/-- Everything the encoder produces is well formed: the walk over a codeword
    reproduces the encoder's own counters, so legality transfers. -/
theorem wf_of_fits : ∀ (p : List Byte) (c : Int),
    fits c p = true → wfCodeword (recEncode c p) = true := by
  intro p
  induction p with
  | nil =>
      intro c hf
      have hc := ok_iff.mp (by rw [fits_nil] at hf; exact hf)
      rw [recEncode_nil, wfCodeword, walk_single, Bool.and_eq_true, decide_eq_true_eq]
      rw [val_byte c (offset_to_inRange hc)]
      exact ⟨ok_iff.mpr hc, by simp⟩
  | cons a as ih =>
      intro c hf
      rw [fits_cons, Bool.and_eq_true] at hf
      obtain ⟨hok, hrest⟩ := hf
      by_cases ha : a = 0
      · subst ha
        have hrest1 : fits 1 as = true := by
          rw [if_pos (rfl : (0 : Byte) = 0)] at hrest; exact hrest
        have hrec : (recEncode 1 as : List Byte) ≠ [] := recEncode_nonempty 1 as
        have h1 : (walk (recEncode 1 as)).2 = 1 :=
          (walk_snd_eq_recDecode_fst _).trans
            (congrArg Prod.fst
              (decode_correct as 1 (recEncode 1 as) (encodes_of_fits as 1 hrest1)))
        rw [recEncode_cons, if_pos (rfl : (0 : Byte) = 0), wfCodeword, walk_cons hrec, h1,
          if_pos rfl]
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          val_byte c (offset_to_inRange (ok_iff.mp hok))]
        simp [hok]
        exact wf_fst (ih 1 hrest1)
      · have hrest2 : fits (bump c) as = true := by
          rw [if_neg ha] at hrest; exact hrest
        have hrec : (recEncode (bump c) as : List Byte) ≠ [] := recEncode_nonempty (bump c) as
        have hb : (walk (recEncode (bump c) as)).2 = bump c :=
          (walk_snd_eq_recDecode_fst _).trans
            (congrArg Prod.fst
              (decode_correct as (bump c) (recEncode (bump c) as)
                (encodes_of_fits as (bump c) hrest2)))
        rw [recEncode_cons, if_neg ha, wfCodeword, walk_cons hrec, hb,
          if_neg (bump_ne_one (ok_iff.mp hok).2.2)]
        simp only [Bool.and_eq_true, decide_eq_true_eq, shift_bump]
        simp [hok, ha]
        exact wf_fst (ih (bump c) hrest2)

/-- **Direction one of the characterization: every admitted-by-the-spec codeword
    is admitted by the receiver.** -/
theorem wfCodeword_of_encodes : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e → wfCodeword e = true := fun p c e h => by
  rw [Encodes.eq_recEncode _ _ _ h]
  exact wf_of_fits p c (fits_of_encodes p c e h)

/-! ## Direction two: what the receiver admits is what the spec allows -/

/-- Boolean conjunction elimination, stated on the `Bool` level. The `Prop`-level
    rewrites for `&&` interact badly with `decide`, which cost several rounds
    here; casing on both operands is immune to all of it. -/
theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

/-- Well-formedness passes to the tail the decoder recursed into. -/
theorem wf_tail {b : Byte} {rest : List Byte} (hrest : rest ≠ [])
    (hw : wfCodeword (b :: rest) = true) : wfCodeword rest = true := by
  have hflag : (walk (b :: rest)).1 = true := wf_fst hw
  rw [walk_cons hrest] at hflag
  split at hflag
  · have h2 : ((walk rest).1 && ok (val b)) = true := hflag
    rw [wfCodeword, and_left h2, Bool.true_and]
    rw [decide_eq_true_eq]; exact hrest
  · have h2 : (((walk rest).1 && decide (b ≠ 0)) && ok (shift (walk rest).2)) = true := hflag
    rw [wfCodeword, and_left (and_left h2), Bool.true_and]
    rw [decide_eq_true_eq]; exact hrest

/-- At a position the walk consumes as an offset: the tail is well formed and the
    byte there is a legal offset. -/
theorem wf_offset {b : Byte} {rest : List Byte} (hrest : rest ≠ [])
    (hd : (walk rest).2 = 1) (hw : wfCodeword (b :: rest) = true) :
    (walk rest).1 = true ∧ ok (val b) = true := by
  have hflag : (walk (b :: rest)).1 = true := wf_fst hw
  rw [walk_cons hrest, hd, if_pos (rfl : (1 : Int) = 1)] at hflag
  have h2 : ((walk rest).1 && ok (val b)) = true := hflag
  exact ⟨and_left h2, and_right h2⟩

/-- At a position the walk treats as data: the tail is well formed, the byte is
    nonzero, and the shifted counter is a legal offset. -/
theorem wf_data {b : Byte} {rest : List Byte} (hrest : rest ≠ [])
    (hd : (walk rest).2 ≠ 1) (hw : wfCodeword (b :: rest) = true) :
    (walk rest).1 = true ∧ b ≠ 0 ∧ ok (shift (walk rest).2) = true := by
  have hflag : (walk (b :: rest)).1 = true := wf_fst hw
  rw [walk_cons hrest, if_neg hd] at hflag
  have h2 : (((walk rest).1 && decide (b ≠ 0)) && ok (shift (walk rest).2)) = true := hflag
  have h3 : ((walk rest).1 && decide (b ≠ 0)) = true := and_left h2
  have hb0 : b ≠ 0 := by
    have h4 := and_right h3
    rw [decide_eq_true_eq] at h4
    exact h4
  exact ⟨and_left h3, hb0, and_right h2⟩

/-- **Direction two: everything the receiver admits is emitted.** Induction on the
    payload, with the codeword destructured alongside it; `bump_of_shift` turns the
    decoder's counter step into the spec's. -/
theorem encodes_of_wfCodeword : ∀ (p : List Byte) (c : Int) (e : List Byte),
    recDecode e = (c, p) → wfCodeword e = true → Encodes c p e := by
  intro p
  induction p with
  | nil =>
      intro c e h hw
      cases e with
      | nil =>
          rw [recDecode_nil] at h
          have h2 : (wfCodeword [] : Bool) = false := by decide
          rw [h2] at hw
          cases hw
      | cons b rest =>
          cases rest with
          | nil =>
              rw [recDecode_single] at h
              obtain ⟨hbc, _⟩ := Prod.mk.inj h
              have hok : ok c = true := by rw [← hbc]; exact and_left hw
              have hv : val (byte c) = c :=
                val_byte c (offset_to_inRange (ok_iff.mp hok))
              have hb : b = byte c := Int8.toInt.inj (hbc.trans hv.symm)
              rw [hb]
              exact Encodes.stop (ok_iff.mp hok)
          | cons r rest' =>
              rw [recDecode_cons2] at h
              split at h <;> simp at h
  | cons a as ih =>
      intro c e h hw
      cases e with
      | nil => rw [recDecode_nil] at h; simp at h
      | cons b rest =>
          cases rest with
          | nil => rw [recDecode_single] at h; simp at h
          | cons r rest' =>
              -- Projection-level reasoning throughout: `cases` on the decoder's
              -- pair substitutes into the goal but not into the hypotheses, which
              -- is what made the earlier version of this proof fight itself.
              have hne : (r :: rest' : List Byte) ≠ [] := by simp
              have hwt : wfCodeword (r :: rest') = true := wf_tail hne hw
              rw [recDecode_cons2] at h
              by_cases hd1 : (recDecode (r :: rest')).1 = 1
              · -- the head byte is an offset, so the payload head is a zero
                  rw [if_pos hd1] at h
                  obtain ⟨hbc, hp⟩ := Prod.mk.inj h
                  obtain ⟨rfl, htail⟩ := List.cons.inj hp
                  have hwd :=
                    wf_offset hne ((walk_snd_eq_recDecode_fst _).trans hd1) hw
                  have hok : ok c = true := by rw [← hbc]; exact hwd.2
                  have hv : val (byte c) = c :=
                    val_byte c (offset_to_inRange (ok_iff.mp hok))
                  have hb : b = byte c := Int8.toInt.inj (hbc.trans hv.symm)
                  have henc := ih 1 (r :: rest') (Prod.ext hd1 htail) hwt
                  rw [hb]
                  exact Encodes.zero (ok_iff.mp hok) henc
              · -- the head byte is data
                  rw [if_neg hd1] at h
                  obtain ⟨hsc, hp⟩ := Prod.mk.inj h
                  obtain ⟨rfl, htail⟩ := List.cons.inj hp
                  have hdn : (walk (r :: rest')).2 ≠ 1 := fun hh =>
                    hd1 ((walk_snd_eq_recDecode_fst _).symm.trans hh)
                  have hwd := wf_data hne hdn hw
                  have hokd : ok (recDecode (r :: rest')).1 = true := by
                    have := walk_fst_implies_ok _ hwd.1 hne
                    rwa [walk_snd_eq_recDecode_fst] at this
                  have hokc : ok (shift (recDecode (r :: rest')).1) = true := by
                    have h2 := hwd.2.2
                    rwa [walk_snd_eq_recDecode_fst] at h2
                  have henc : Encodes (bump (shift (recDecode (r :: rest')).1)) as
                    (r :: rest') := by
                    rw [bump_of_shift hokc hokd hd1 rfl]
                    exact ih (recDecode (r :: rest')).1 (r :: rest')
                      (Prod.ext rfl htail) hwt
                  rw [← hsc]
                  exact Encodes.data (ok_iff.mp hokc).2.2 hwd.2.1 henc

/-- **The spec is exactly the receiver's acceptance set.** Direction one says the
    encoder never produces anything the receiver rejects; direction two says the
    receiver never accepts anything the encoder cannot produce. Between them,
    canonicality is decidable, and the only rejections are real defects. -/
theorem encodes_iff : ∀ (p : List Byte) (c : Int) (e : List Byte),
    Encodes c p e ↔ (recDecode e = (c, p) ∧ wfCodeword e = true) := fun p c e =>
  ⟨fun h => ⟨decode_correct p c e h, wfCodeword_of_encodes p c e h⟩,
   fun h => encodes_of_wfCodeword p c e h.1 h.2⟩

end Ncobs
