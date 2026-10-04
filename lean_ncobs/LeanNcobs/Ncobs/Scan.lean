/-
The receiver's nested scan: a functional reading of `scan_frame` from the
reference implementation, plus the containment fact that makes acting at a
sentinel safe.

The reference decoder walks a received buffer right-to-left. Each offset byte
says how far left the next landmark lies. When the walk meets a `0` in a data
slot, that is the sentinel of a frame that completed inside this one: it
recurses, discards that frame's output (already delivered when its own sentinel
arrived), and shifts its target left by the number of bytes skipped --
`next -= p - new_p` in the original.

Modelled on reversed lists the compensation becomes a claim about the walk's
budget: *skipping a nested block leaves that budget untouched.* The budget is
counted in the frame's own bytes, so bytes spliced into the middle of the wire
cannot perturb it. That is the whole trick, and stating it this way is what the
Why3 model never managed.
-/
import LeanNcobs.Ncobs.Nested

namespace Ncobs
namespace Scan

/-- `val c < 0` as a `Bool` rather than a `Prop`, so it can drive a recursion and
    sit in a structure field. -/
def isNeg (c : Byte) : Bool := decide (val c < 0)

/-- Outcome of a walk.

    `payload` comes out reversed, the walk going right-to-left. `consumed` counts
    the bytes taken from the argument. `left` and `atEnd` are the walk's
    *residual state*: the budget still unspent, and whether the landmark being
    approached was this frame's own boundary. Carrying them is what turns
    containment from something you watch for into something you can state -- the
    walk is contained exactly when it reaches its own boundary with nothing left. -/
structure Result where
  payload : List Byte
  consumed : Nat
  left : Nat
  atEnd : Bool

/-- Containment: the walk spent its whole budget reaching its own boundary, so it
    never needed a byte from before this frame's start. -/
def isComplete (r : Result) : Bool := r.left == 0 && r.atEnd

/-- Account for a consumed byte that is not payload: an offset byte, or the
    sentinel that triggered the scan. -/
private def own (g : Result) : Result :=
  { payload := g.payload, consumed := g.consumed + 1, left := g.left, atEnd := g.atEnd }

/-- Account for a consumed byte that is payload. The budget is counted in the
    frame's own bytes, so bytes skipped over a nested block do not appear here at
    all -- this is where the reference's `next -= p - new_p` lives. -/
private def dataOf (b : Byte) (g : Result) : Result :=
  { payload := b :: g.payload, consumed := g.consumed + 1
    left := g.left, atEnd := g.atEnd }

/-- Consume a whole nested block, then carry on with the budget exactly as it
    was. Nothing else in this file is about nesting. -/
private def skipOver (f g : Result) : Result :=
  { payload := g.payload, consumed := f.consumed + g.consumed + 1
    left := g.left, atEnd := g.atEnd }

mutual

/-- Walk a reversed wire. `n` is the remaining budget in *this frame's own*
    bytes; `isEnd` says the landmark being approached is this frame's own
    boundary, which holds when the offset that led here was negative, as against
    a slot where a payload zero had been replaced. -/
def walk : List Byte → Nat → Bool → Result
  | [], n, isEnd => ⟨[], 0, n, isEnd⟩
  | b :: r, n, isEnd =>
      -- Branch order copied from `scan_frame`: the zero test precedes the
      -- zero-replacement test, so a sentinel meeting the walk exactly at a
      -- landmark is read as a nested frame rather than as an offset byte.
      if isEnd && n == 0 then ⟨[], 0, 0, true⟩
      else if b = 0 then
        match offset r with
        | f => skipOver f (walk (r.drop f.consumed) n isEnd)
      else if n == 0 then
        let g := walk r (Int.natAbs (val b) - 1) (isNeg b)
        { payload := 0 :: g.payload, consumed := g.consumed + 1
          left := g.left, atEnd := g.atEnd }
      else dataOf b (walk r (n - 1) isEnd)
termination_by r => r.length

/-- Begin a frame at its terminating offset byte: consume that byte, then walk
    with a budget one less than its magnitude, the byte itself not counting
    towards the distance it encodes. -/
def offset : List Byte → Result
  | [] => ⟨[], 0, 0, false⟩
  | v :: w => own (walk w (Int.natAbs (val v) - 1) (isNeg v))
termination_by r => r.length

end

/-- Scan a frame from a reversed wire that begins with that frame's own
    sentinel. -/
def scanFrame (R : List Byte) : Result :=
  match R with
  | [] => ⟨[], 0, 0, false⟩
  | _ :: rest => own (offset rest)

/-! ## Reading the scan -/

/-- The payload handed up when this wire's last sentinel arrives. -/
def scanPayload (e : List Byte) : List Byte := (scanFrame e.reverse).payload.reverse

/-- Bytes the scan took, including the triggering sentinel. -/
def scanConsumed (e : List Byte) : Nat := (scanFrame e.reverse).consumed

/-- The walk spent its budget exactly reaching its own boundary. -/
def scanComplete (e : List Byte) : Bool := isComplete (scanFrame e.reverse)

/-- Positions of the sentinels, hence the order in which frames completed. -/
def zeroIndices : List Byte → List Nat
  | [] => []
  | b :: r =>
      if b = 0 then 0 :: (zeroIndices r).map (· + 1) else (zeroIndices r).map (· + 1)

/-- Everything the receiver hands up while this wire is in flight: each prefix
    ending at a sentinel, scanned on its own, since each is delivered the moment
    its own sentinel lands. -/
def scanStream (e : List Byte) : List (List Byte) :=
  ((zeroIndices e).map (fun i => e.take (i + 1))).map scanPayload

/-! ## Against the reference decoder's own tables -/

/-- README nested example 1, under this library's sign convention: frame `A B`
    preempted after `A` by frame `a`. Their table carries the opposite sign on
    every offset; the decoded payloads agree either way. -/
example : scanPayload [65, 97, -2, 0, 66, -3, 0] = [65, 66] := by native_decide
example : scanConsumed [65, 97, -2, 0, 66, -3, 0] = 7 := by native_decide
example : scanComplete [65, 97, -2, 0, 66, -3, 0] = true := by native_decide

/-- README nested example 2: frame `0 0` preempted after its first byte. -/
example : scanPayload [-1, -1, 1, 0, 1, 1, 0] = [0, 0] := by native_decide
example : scanConsumed [-1, -1, 1, 0, 1, 1, 0] = 7 := by native_decide

/-- A plain frame carrying a payload zero: the ordinary path is unaffected. -/
example : scanPayload [65, -2, 67, 2, 0] = [65, 0, 67] := by native_decide

/-- What the receiver delivers across a nested wire: the nested frame first,
    then the frame it interrupted. -/
example : scanStream [65, 97, -2, 0, 66, -3, 0] = [[97], [65, 66]] := by native_decide
example : scanStream [-1, -1, 1, 0, 1, 1, 0] = [[0], [0, 0]] := by native_decide

/-- Containment is not vacuous. Here the terminating offset claims three of the
    frame's own bytes and only one is present, so the walk ends with budget
    unspent: the frame needs bytes from before where it appears to start, and the
    receiver has no licence to commit. Note the failure mode this detects is
    reaching *left*, not stopping early -- a scan is always entered at a
    sentinel, so the flag measures offset containment, nothing else. -/
example : scanComplete [66, -3, 0] = false := by native_decide
example : scanComplete [97, -2, 0, 66, -3, 0] = false := by native_decide

/-! ## Sweeps over generated nested transcripts -/

/-- On every generated transcript the scan recovers the interrupted frame's
    payload from the wire as it stands, with no help from the transcript: the scan
    sees bytes only. -/
theorem scan_payload_of_wire :
    (Nesting.genTr 1).all (fun t => scanPayload (Nesting.wireOf t) == Nesting.outer t) = true := by
  native_decide

/-- Containment on every generated transcript: the walk reaches its own boundary
    with budget to spare never. This is the property the receiver acts on. -/
theorem scan_contained :
    (Nesting.genTr 1).all (fun t => scanComplete (Nesting.wireOf t)) = true := by
  native_decide

/-- And the whole stream: what the receiver hands up is exactly the set of frames
    that ran, oldest completion first. -/
theorem scan_stream_of_wire :
    (Nesting.genTr 1).all (fun t =>
      scanStream (Nesting.wireOf t) == Nesting.delivered t ++ [Nesting.outer t]) = true := by
  native_decide

/-- Depth two: every depth-one transcript, itself nested inside a fresh frame, at
    every split point and continuation. This is where a mis-counted skip would
    corrupt the enclosing frame rather than merely the frame being scanned. -/
def genTr2 : List Nesting.Tr :=
  (Nesting.genTr 1).flatMap fun inner =>
    Nesting.payloads.flatMap fun pre =>
      Nesting.payloads.map fun q => Nesting.Tr.cut pre inner (Nesting.Tr.fin q)

theorem scan_payload_of_wire2 :
    genTr2.all (fun t => scanPayload (Nesting.wireOf t) == Nesting.outer t) = true := by
  native_decide

theorem scan_contained2 : genTr2.all (fun t => scanComplete (Nesting.wireOf t)) = true := by
  native_decide

theorem scan_stream_of_wire2 :
    genTr2.all (fun t => scanStream (Nesting.wireOf t) == Nesting.delivered t ++ [Nesting.outer t]) =
      true := by
  native_decide

/-! ### Where the walk stops short, and why that is harmless

    The natural strengthening of containment -- that the walk consumes *exactly*
    the frame's own wire -- is false, and the reference decoder behaves the same
    way, so this is a property of the protocol rather than of the model. Here is
    the smallest instance: an empty frame interrupted by an empty frame. -/

/-- The wire is the nested frame's `[-1, 0]` followed by the outer frame's own
    `[-1, 0]`. Scanning it takes two bytes and stops: the outer frame's terminating
    offset is `-1`, so its boundary is the very next byte left, which happens to be
    the nested frame's sentinel. The walk halts there by the branch order it copies
    from `scan_frame`, so the nested block is never visited by this scan. -/
example : scanPayload [-1, 0, -1, 0] = [] := by native_decide
example : scanConsumed [-1, 0, -1, 0] = 2 := by native_decide
example : scanComplete [-1, 0, -1, 0] = true := by native_decide

/-- The skipped prefix is not lost: it sits to the left of where this scan stopped,
    so the enclosing scan meets the same sentinel and takes the block as its own
    nested child. Nothing is delivered twice, because a frame consumed as a nested
    block emits no output -- its payload went out when its own sentinel arrived.
    That is what the three depth-two sweeps above check: 101,000 transcripts of
    which 10,000 have this shape under a parent, and payloads, containment and
    delivery order all hold. -/
example : scanStream [-1, 0, -1, 0] = [[], []] := by native_decide

end Scan
end Ncobs
