/-
Nested COBS: preemption by nesting.

A low-priority frame is being streamed; a higher-priority frame starts, runs to
completion, and control returns to the interrupted frame mid-codeword. On the
wire the nested frame's codeword is spliced into the middle of the outer frame's.
The outer frame's offsets are *frame-relative*, so the splice breaks them as
absolute positions, and the receiver repairs it by shifting its target by the
number of bytes it skipped (`next -= p - new_p` in the reference decoder).

Everything below rests on one observation: the outer encoder's state is complete
at every point between two calls of `step`, so an interruption can splice bytes
in without the interrupted frame ever knowing. `emit` and `erase` make that exact
-- they differ only by the spliced segments, and agree on the state.
-/
import LeanNcobs.Ncobs.Online
import LeanNcobs.Ncobs.Decode

namespace Ncobs
namespace Nesting
open Ncobs Online

/-- A well-bracketed nested transcript, describing one frame's whole life.

    - `fin s`: emit payload `s` into this frame, then `end_frame`.
    - `cut pre inner rest`: emit payload `pre`, then let frame `inner` run to
      completion, then continue *this* frame as `rest`.

    LIFO holds by construction, and that is the point of the type rather than an
    accident of it. `cut` hands control to `inner` and gets it back at `rest`;
    there is no constructor that ends a frame and later resumes another one, so
    the illegal interleaving `sf1 · encode f1 · sf2 · ef1 · encode f2 · ef2` --
    which the README rules out by hand as violating the Stack Resource Policy --
    has no term. `rest` is the *same* frame continuing, which is why it carries
    the outer counter across the interruption; a frame may be preempted repeatedly
    because `rest` may itself be a `cut`.

    A frame that never calls `end_frame` is likewise not representable: every
    branch reaches `fin`. The hung-frame liveness property is therefore a claim
    about a different model, one with a `hang` constructor and a receiver, and it
    is still unproven. -/
inductive Tr : Type where
  | fin : List Byte → Tr
  | cut : List Byte → Tr → Tr → Tr

/-- The payload of the frame this transcript belongs to. -/
def outer : Tr → List Byte
  | .fin s => s
  | .cut pre _ rest => pre ++ outer rest

/-- What the receiver hands up during this frame's life, in delivery order:
    whatever ran nested inside `inner` first, then `inner` itself, then whatever
    arrives after control came back. -/
def delivered : Tr → List (List Byte)
  | .fin _ => []
  | .cut _ inner rest => delivered inner ++ [outer inner] ++ delivered rest

/-- Bytes contributed to the frame's transmission, starting from state `st`, and
    the state left when the frame ends. Nested segments are spliced in. -/
def emit : Tr → State → List Byte × State
  | .fin s, st => ((stream st s).1 ++ frameEnd (stream st s).2, (stream st s).2)
  | .cut pre inner rest, st =>
      ((stream st pre).1 ++ (emit inner frameBegin).1 ++ (emit rest (stream st pre).2).1,
        (emit rest (stream st pre).2).2)

/-- The same, with every nested segment excised. -/
def erase : Tr → State → List Byte × State
  | .fin s, st => ((stream st s).1 ++ frameEnd (stream st s).2, (stream st s).2)
  | .cut pre _ rest, st =>
      ((stream st pre).1 ++ (erase rest (stream st pre).2).1,
        (erase rest (stream st pre).2).2)

@[simp] theorem emit_fin (s : List Byte) (st : State) :
    emit (.fin s) st = ((stream st s).1 ++ frameEnd (stream st s).2, (stream st s).2) := rfl

@[simp] theorem emit_cut (pre : List Byte) (inner rest : Tr) (st : State) :
    emit (.cut pre inner rest) st =
      ((stream st pre).1 ++ (emit inner frameBegin).1 ++ (emit rest (stream st pre).2).1,
        (emit rest (stream st pre).2).2) := rfl

@[simp] theorem erase_fin (s : List Byte) (st : State) :
    erase (.fin s) st = ((stream st s).1 ++ frameEnd (stream st s).2, (stream st s).2) := rfl

@[simp] theorem erase_cut (pre : List Byte) (inner rest : Tr) (st : State) :
    erase (.cut pre inner rest) st =
      ((stream st pre).1 ++ (erase rest (stream st pre).2).1,
        (erase rest (stream st pre).2).2) := rfl

/-- The transmission of a transcript, and its own codeword with nested segments
    cut out. -/
def wireOf (t : Tr) : List Byte := (emit t frameBegin).1
def ownOf (t : Tr) : List Byte := (erase t frameBegin).1

/-! ## An interruption leaves the interrupted frame's state untouched -/

/-- The preempted frame's machine state at the end of its life does not depend on
    what was nested inside it. This is the whole reason nesting is possible at all
    with an online encoder: `step` leaves `State` complete at every byte, so a
    splice needs no cooperation from the frame it splices into. -/
theorem emit_state_eq : ∀ (t : Tr) (st : State), (emit t st).2 = (erase t st).2 := by
  intro t
  induction t with
  | fin => intro st; rfl
  | cut pre inner rest _ ih =>
      intro st
      rw [emit_cut, erase_cut]
      exact ih (stream st pre).2

/-! ## Excising nested segments leaves the plain codeword -/

/-- **The structural core of nesting.** Splicing a nested frame's codeword into
    the middle of a frame's codeword leaves, once the splice is removed, exactly
    the codeword the frame's own payload would have produced. Nothing about the
    nested frame enters the statement.

    The content is that the outer frame's counter survives the interruption
    (`stream_append`), so the offsets emitted before the splice and those emitted
    after it belong to one consistent encoding. -/
theorem erase_eq : ∀ (t : Tr) (st : State),
    erase t st =
      ((stream st (outer t)).1 ++ frameEnd (stream st (outer t)).2,
        (stream st (outer t)).2) := by
  intro t
  induction t with
  | fin s => intro st; rfl
  | cut pre inner rest _ ih =>
      intro st
      simp only [outer]
      rw [erase_cut, ih (stream st pre).2, stream_append pre st (outer rest),
        List.append_assoc]

/-- The frame's own codeword is the ordinary encoding of its own payload. -/
theorem own_eq_encode (t : Tr) : ownOf t = encode (outer t) := by
  rw [← encodeOnline_eq_encode]
  show (erase t frameBegin).1 =
    (stream frameBegin (outer t)).1 ++ frameEnd (stream frameBegin (outer t)).2
  rw [erase_eq t frameBegin]

/-- **Round trip through a nesting.** Once the nested segments are excised, the
    ordinary decoder recovers the outer frame's payload: nesting is transparent to
    the codec. -/
theorem decode_ownFrame {t : Tr} (h : (outer t).length ≤ 126) :
    decodeFrame (ownOf t) = outer t := by
  rw [own_eq_encode]
  exact decodeFrame_encode h

/-! ## Immediate reconstruction -/

/-- The sentinel of an encoded frame is not reachable by the body scan, so framing
    and decoding compose: `decodeFrame (encode p)` reaches exactly the body the
    codec was proved on. -/
theorem takeWhile_body {e : List Byte} (h : ∀ b ∈ e, b ≠ 0) :
    (e ++ [0]).takeWhile (· ≠ 0) = e := by
  rw [takeWhile_stop h]

theorem decode_encode_of_wire {p : List Byte} (h : fits (-1) p = true) :
    decodeFrame (encodeOnline p) = p := by
  rw [encodeOnline_eq_encode]
  show decodeBody ((recEncode (-1) p ++ [0]).takeWhile (· ≠ 0)) = p
  rw [takeWhile_body (encode_body_sentinel_free h)]
  exact decode_encode h

/-- Note what this is *not* a claim about: `decodeFrame (wireOf t)` is false in
    general, because the first sentinel in a wire belongs to a nested frame, not to
    the frame being delivered. Framing a nested stream needs the receiver's
    skip-compensating scan, not `takeWhile`; what is proven here is that once the
    segments are excised the ordinary framing works unchanged. -/
theorem immediate {t : Tr} (h : fits (-1) (outer t) = true) :
    decodeFrame (ownOf t) = outer t := by
  rw [own_eq_encode, ← encodeOnline_eq_encode]
  exact decode_encode_of_wire h

/-! ## The skip distance -/

/-- Bytes carried by nested segments inside a transcript. -/
def nestLen : Tr → Nat
  | .fin _ => 0
  | .cut _ inner rest => (emit inner frameBegin).1.length + nestLen rest

/-- The wire is the frame's own codeword plus the nested segments. -/
theorem emit_length : ∀ (t : Tr) (st : State),
    (emit t st).1.length = (erase t st).1.length + nestLen t := by
  intro t
  induction t with
  | fin => intro st; rfl
  | cut pre inner rest _ ih =>
      intro st
      rw [emit_cut, erase_cut, nestLen, List.length_append, List.length_append,
        ih (stream st pre).2, List.length_append]
      omega

/-- **The skip distance, in codeword bytes.** The receiver's compensation is
    correct in magnitude: the wire carries the frame's own `payload + 2` bytes --
    `+1` for the terminating offset, `+1` for the sentinel, which the README does
    not count as overhead -- plus exactly the nested segments' bytes.

    The `+1` is the point. `n_cobs_nested.why` reasons with the *decoded* length
    where the skip needs the *codeword* length, and never states the relation; that
    is a large part of why it never closed. -/
theorem wire_length {t : Tr} (h : fits (-1) (outer t) = true) :
    (wireOf t).length = (outer t).length + 2 + nestLen t := by
  have h1 : (wireOf t).length = (ownOf t).length + nestLen t := emit_length t frameBegin
  rw [h1, own_eq_encode, encode, List.length_append, encode_overhead h]
  simp only [List.length_singleton]

/-! ## The nested segment is contiguous, and self-contained -/

/-- A nested frame's bytes appear in one contiguous block, ending in its own
    sentinel, which is why the receiver can act on it the moment that sentinel
    arrives without consulting anything to the left. -/
theorem wire_cut (pre : List Byte) (inner rest : Tr) :
    wireOf (.cut pre inner rest) =
      (stream frameBegin pre).1 ++ wireOf inner ++ (emit rest (stream frameBegin pre).2).1 := by
  show (emit (.cut pre inner rest) frameBegin).1 = _
  rw [emit_cut]
  rfl

/-- **Immediate reconstruction, per frame.** Every nested frame recovers its own
    payload from its own segment, by the same theorem, recursively: nothing about
    the frame it interrupted is needed. -/
theorem delivered_ok : ∀ (t : Tr), (∀ p ∈ delivered t, p.length ≤ 126) →
    ∀ p ∈ delivered t, decodeFrame (encode p) = p := by
  intro t h p hp
  exact decodeFrame_encode (h p hp)

/-! ## The two worked examples from the protocol README -/

/-- README, nested example 1: frame `A B` preempted after `A` by frame `a`.
    Their table is `A a 2 0 B 3 0`; under the Rust and Why3 sign convention, which
    this library follows, the offsets carry the opposite sign. -/
example : wireOf (Tr.cut [65] (Tr.fin [97]) (Tr.fin [66])) = [65, 97, -2, 0, 66, -3, 0] := rfl

/-- The outer frame's own codeword, after excising the nested segment: exactly
    what encoding `A B` alone produces. -/
example : ownOf (Tr.cut [65] (Tr.fin [97]) (Tr.fin [66])) = [65, 66, -3, 0] := rfl
example : encode ([65, 66] : List Byte) = [65, 66, -3, 0] := rfl

/-- The outer payload comes back, and the nested frame was delivered on its own
    sentinel. -/
example : decodeFrame (ownOf (Tr.cut [65] (Tr.fin [97]) (Tr.fin [66]))) = [65, 66] := rfl
example : delivered (Tr.cut [65] (Tr.fin [97]) (Tr.fin [66])) = [[97]] := rfl

/-- README, nested example 2: frame `0 0` preempted after the first `0` by frame
    `0`. Their table is `1 1 -1 0 -1 -1 0`, again sign-flipped relative to the
    convention used here; flipping every sign in the value below reproduces it. -/
example : wireOf (Tr.cut [0] (Tr.fin [0]) (Tr.fin [0])) = [-1, -1, 1, 0, 1, 1, 0] := rfl
example : ownOf (Tr.cut [0] (Tr.fin [0]) (Tr.fin [0])) = [-1, 1, 1, 0] := rfl
example : decodeFrame (ownOf (Tr.cut [0] (Tr.fin [0]) (Tr.fin [0]))) = [0, 0] := rfl

/-- Two preemptions of the same frame: `A _ B _ C` with `a` and `b` nested.
    `rest` being itself a `cut` is what allows this. -/
def twoCuts : Tr := Tr.cut [65] (Tr.fin [97]) (Tr.cut [66] (Tr.fin [98]) (Tr.fin [67]))
example : outer twoCuts = [65, 66, 67] := rfl
example : delivered twoCuts = [[97], [98]] := rfl
example : ownOf twoCuts = encode [65, 66, 67] := rfl
example : decodeFrame (ownOf twoCuts) = [65, 66, 67] := rfl

/-- Nesting two levels deep: `A _ B` preempted by a frame that is itself preempted. -/
def deep : Tr := Tr.cut [65] (Tr.cut [97] (Tr.fin [200]) (Tr.fin [99])) (Tr.fin [66])
example : outer deep = [65, 66] := rfl
example : delivered deep = [[200], [97, 99]] := rfl
example : decodeFrame (ownOf deep) = [65, 66] := rfl

/-! ## Checking the model against itself, and against the decoder -/

/-- Payloads chosen to hit the interesting shapes: empty, a lone zero, leading and
    trailing zeros, a zero run, and the reserved `-128` as a data byte. -/
def payloads : List (List Byte) :=
  [[], [0], [1], [-1], [0, 0], [65], [65, 0], [0, 65], [65, 66, 0, 67], [-128]]

/-- All nested transcripts of depth at most `d` over `payloads`. Depth 1 already
    contains nesting two frames deep, since both the interrupted frame and its
    continuation range over the depth-0 set. -/
def genTr : Nat → List Tr
  | 0 => payloads.map Tr.fin
  | d + 1 =>
      (payloads.map Tr.fin)
        ++ payloads.flatMap fun pre =>
          (genTr d).flatMap fun inner => (genTr d).map fun rest => Tr.cut pre inner rest

/-- 1,010 transcripts. The right-hand side of the comparison is computed by the
    independent decoder while the left comes from the nesting model, so a `emit`
    that mis-spliced -- dropping the outer counter, or emitting the terminating
    offset on the wrong side of the interruption -- would fail here rather than in
    a proof. `native_decide`, so this checks the definitions, not the theorems. -/
theorem nesting_round_trip :
    (genTr 1).all (fun t => decodeFrame (ownOf t) == outer t) = true := by
  native_decide

/-- The excision identity, checked rather than cited: `ownOf` really is the plain
    encoding of the frame's own payload, on every generated transcript. -/
theorem nesting_excision :
    (genTr 1).all (fun t => ownOf t == encode (outer t)) = true := by
  native_decide

/-- Nested bytes are exactly what the wire carries beyond the frame's own codeword,
    and every nested segment ends in a sentinel -- which is why the receiver sees a
    frame boundary at each of them. -/
theorem nesting_sentinels :
    (genTr 1).all (fun t =>
      (wireOf t).length == (ownOf t).length + nestLen t
      ∧ (nestLen t > 0 → (wireOf t).length > (ownOf t).length)) = true := by
  native_decide

end Nesting
end Ncobs
