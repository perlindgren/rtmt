/-
  The model, stated the way the protocol states it.

  Everything before this file treats a frame as a list that is present all at
  once. That is enough to prove the codec correct, but it cannot express the
  claims the protocol is actually sold on -- "no critical sections on the sender
  side", "preemption at an arbitrary point" -- because a function that consumes
  a whole list has no preemption points to speak of. This file gives the
  incremental machine, and proves it emits exactly the codeword `recEncode`
  produces, so the round trip carries over.

  The encoder's whole state is one signed integer, and that is the point: there
  is no payload buffer in the type, so there is nothing for a preempting frame to
  corrupt. The claim "the sender holds nothing across a preemption point" stops
  being a comment and becomes a fact about which types are inhabited.
-/
import LeanNcobs.Ncobs.Decode

namespace Ncobs.Online
open Ncobs

/-- The complete encoder state between two bytes: the running offset counter,
    whose sign also records whether the frame has seen a zero yet. No buffer, no
    length, no history. -/
structure State where
  c : Int

/-- Open a frame. Emits nothing. -/
def frameBegin : State := ⟨-1⟩

/-- One byte in, zero or more bytes out. This is the only place encoding
    happens, and it is where a preemption can intervene: the machine is fully
    described by `State` the instant `step` returns. -/
def step : State → Byte → List Byte × State
  | ⟨c⟩, b =>
      if b = 0 then ([byte c], { c := 1 })
      else ([b], { c := bump c })

/-- Close a frame: emit the terminating offset, then the frame sentinel. -/
def frameEnd : State → List Byte
  | ⟨c⟩ => [byte c, 0]

/-- Drive the machine over a payload. Returns the emitted bytes and the state
    left for `frameEnd` to consume. -/
def stream : State → List Byte → List Byte × State
  | s, [] => ([], s)
  | s, b :: bs =>
      ((step s b).1 ++ (stream (step s b).2 bs).1,
        (stream (step s b).2 bs).2)

/-- A complete transmitted frame, produced incrementally. -/
def encodeOnline (p : List Byte) : List Byte :=
  (stream frameBegin p).1 ++ frameEnd (stream frameBegin p).2

@[simp] theorem step_zero (c : Int) : step ⟨c⟩ 0 = ([byte c], { c := 1 }) := rfl

theorem step_data {c : Int} {b : Byte} (hb : b ≠ 0) :
    step ⟨c⟩ b = ([b], { c := bump c }) := by
  simp only [step, if_neg hb]

@[simp] theorem stream_nil (s : State) : stream s [] = ([], s) := rfl

@[simp] theorem stream_cons (s : State) (b : Byte) (bs : List Byte) :
    stream s (b :: bs) =
      ((step s b).1 ++ (stream (step s b).2 bs).1, (stream (step s b).2 bs).2) := rfl

/-- **The incremental machine is the codec.** Driving the machine over a payload
    and then closing the frame yields precisely `recEncode`: the machine never
    buffers a byte whose value it will need later, because the only thing it
    carries forward is the counter. -/
theorem recEncode_eq_stream : ∀ (p : List Byte) (s : State),
    recEncode s.c p = (stream s p).1 ++ [byte (stream s p).2.c] := by
  intro p
  induction p with
  | nil => intro s; simp [recEncode_nil]
  | cons a as ih =>
      intro s
      by_cases ha : a = 0
      · subst ha
        rw [recEncode_cons, stream_cons, step_zero, ih ⟨1⟩]
        rfl
      · rw [recEncode_cons, if_neg ha, stream_cons, step_data ha, ih ⟨bump s.c⟩]
        rfl

/-- So the two encoders agree on whole frames, and every theorem about
    `recEncode` -- sentinel-freeness, the one-byte overhead, the round trip --
    is a theorem about the machine that actually runs. -/
theorem encodeOnline_eq_encode (p : List Byte) : encodeOnline p = encode p := by
  show (stream frameBegin p).1 ++ frameEnd (stream frameBegin p).2 =
       recEncode frameBegin.c p ++ [0]
  rw [recEncode_eq_stream p frameBegin]
  cases stream frameBegin p with
  | mk out s => simp [frameEnd, List.append_assoc]

/-- **Arbitrary preemption points, on the sender.** The bytes the machine emits
    for a prefix are final: they do not depend on, and are not revised by,
    anything that follows. Everything carried across the boundary is `State`.
    This is the property that makes preemption possible at all -- a sender that
    had to revisit earlier bytes could not hand the channel over mid-frame. -/
theorem stream_append : ∀ (p : List Byte) (s : State) (q : List Byte),
    stream s (p ++ q) =
      ((stream s p).1 ++ (stream (stream s p).2 q).1, (stream (stream s p).2 q).2) := by
  intro p
  induction p with
  | nil => intro s q; simp
  | cons a as ih =>
      intro s q
      simp only [List.cons_append, stream_cons]
      have key := ih (step s a).2 q
      rw [key]
      simp [List.append_assoc]

/-- In particular, what has been sent is a prefix of what will be sent. Nothing
    emitted is ever taken back. -/
theorem emitted_is_prefix (s : State) (p q : List Byte) :
    List.IsPrefix (stream s p).1 (stream s (p ++ q)).1 := by
  rw [stream_append p s q]
  exact ⟨_, rfl⟩

end Ncobs.Online
