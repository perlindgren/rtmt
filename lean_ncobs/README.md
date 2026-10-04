# lean_ncobs

A Lean 4 formalization of **Nested COBS** (ncobs), the preemptive-framing
extension of COBS specified in the parent project's `README.md`.

Toolchain: `leanprover/lean4:v4.34.1`. **No dependencies** -- core Lean only.

## The model, pinned down

- **Alphabet.** `Byte = Int8`. Payload bytes are arbitrary `Int8` values;
  nothing is escaped, excluded, or transformed except the zeros that get
  replaced.
- **Framing.** A frame is a codeword followed by the sentinel `0`. The sentinel
  is the only byte with a reserved meaning, and inside a frame it does not occur.
- **Offsets.** A nonzero `Int` counter, converted to a byte only when emitted.
  Negative = distance back to the start of the frame; positive = distance
  forward to the zero that was replaced. This is the *code's* convention; the
  parent README's tables are globally sign-flipped. **Which one is normative is
  still an open decision** -- see the note on my retracted argument below.
- **Legal offsets** are `-127 ≤ c ≤ 127`, `c ≠ 0`. `-128` is *reserved* as the
  long-frame chaining marker, so it is not a legal terminating offset.
- **Short frames.** The round trip holds for every payload satisfying `fits`,
  which includes arbitrarily long ones whose zeros reset the counter often
  enough. What is derived is the *uniform* bound: every payload of at most 126
  bytes fits, whatever it contains, and 127 does not.
- **The encoder is a step machine** -- state is one integer, no payload buffer.

## Status

| Claim | Theorem |
|---|---|
| The spec admits nothing the encoder wouldn't produce | `Encodes.eq_recEncode` |
| The encoding is deterministic | `encodes_unique` |
| No codeword byte is the sentinel | `Encodes.sentinel_free` |
| Overhead is exactly one byte | `encode_overhead` |
| Frames up to 126 bytes are encodable | `encodable_of_length_le_126` |
| 127 bytes is not | `Test`, by `decide` |
| The step machine *is* the codec | `Online.recEncode_eq_stream` |
| Sender output for a prefix is final | `Online.stream_append`, `emitted_is_prefix` |
| **decode (encode p) = p**, length ≤ 126 | `decode_encode_of_length_le_126` |
| same, for any `fits`-legal payload | `decode_encode` |
| framing: scan to the sentinel, decode | `decodeFrame_encode` |
| the decoder does *not* reject non-codewords | `decoder_accepts_non_canonical` |
| the spec never lets an illegal counter through | `fits_of_encodes` |
| what the spec allows, the receiver accepts | `wfCodeword_of_encodes` |
| what the receiver accepts, the spec allows | `encodes_of_wfCodeword` |
| **those two are the same set of codewords** | `encodes_iff` |
| an interruption leaves the interrupted frame's state intact | `Nesting.emit_state_eq` |
| excising nested segments leaves the plain codeword | `Nesting.erase_eq`, `Nesting.own_eq_encode` |
| the outer payload round-trips through nesting | `Nesting.immediate` |
| the skip distance, in codeword bytes | `Nesting.wire_length` |
| the scan reproduces both reference decode tables | `Scan`, by `native_decide` |
| the scan never reaches left of its own frame | `Scan.scan_contained`, `Scan.scan_contained2` |
| the scan hands up exactly the frames that ran, in order | `Scan.scan_stream_of_wire`, `..._of_wire2` |

Axioms: `propext`, `Quot.sound`, and `Classical.choice` in the few lemmas that
reach `Int8.ofInt_toInt`. No `sorryAx` anywhere. The `Online` results need
`propext` alone.

`Test.lean` has two kinds of check. `exhaustive_kernel` is `decide`, so the
kernel verifies it. The wider sweeps use `native_decide`, which is *not*
kernel-verified -- it trusts the compiler, and each such theorem carries a
`native_decide` axiom that `#print axioms` will show.

## Layout

- `Ncobs/Byte.lean` -- `Byte = Int8`, `Offset`, the `Int`/`Int8` bridge.
- `Ncobs/Spec.lean` -- the protocol as an inductive relation `Encodes c p e`.
- `Ncobs/Encode.lean` -- batch encoder, `fits`, derived 126-byte bound.
- `Ncobs/Decode.lean` -- right-to-left decoder, reversibility.
- `Ncobs/Online.lean` -- the incremental machine, and why it equals the batch one.
- `Ncobs/Nested.lean` -- nested transcripts: LIFO by construction, splice semantics,
  the excision theorem, and the skip distance.
- `Ncobs/Scan.lean` -- the receiver's `scan_frame` as a functional walk, with the
  skip compensation and the containment flag.
- `Ncobs/WF.lean` -- codeword well-formedness: the receiver's own walk, and
  `encodes_iff`.
- `Ncobs/Test.lean` -- exhaustive checks, and the 126/127 boundary.

## The 126-byte bound

A negative counter has consumed nothing but data since the frame began, so `-c`
is that count plus one, at most `n + 1`; requiring `-c ≥ -127` gives `n ≤ 126`. A
positive counter additionally has a replaced zero behind it, so it gets a byte of
slack it cannot use. Reserving `-128` for chaining is what makes the limit 126
rather than 127.

This is not a hypothetical. At exactly 127 zero-free bytes the prototype encoder
emits a terminating offset of `-128`, and its decoder reads that as a chain
marker and walks off the front of the frame. Verified by compiling the
prototype's own encoder and decoder and running the boundary:

| payload | final offset | prototype decoder |
|---|---|---|
| 125 B | `-126` | recovers 125 |
| 126 B | `-127` | recovers 126 |
| **127 B** | **`-128`** | **panics** |
| 128 B | chain marker + offset | recovers 128 |

So the parent README's "single byte overhead for short frames up to 127 bytes" is
off by one. `Test.lean` pins both sides with `decide`.

## Three things to know before editing

**Keep the counter in `Int`.** `omega` in Lean 4.34 has no `Int8` support -- it
treats `Int8.toInt` as an opaque atom, and `grind` fails on `toInt` bounds too.
Correctness theorems therefore carry a range hypothesis, which is what `fits` and
`Legit` exist to discharge.

**Induct on the payload, not the derivation.** `Encodes.zero` hard-codes its
sub-counter as the literal `1`, and a literal in an index position stops Lean
abstracting that premise into an IH. Every lemma takes the payload as its first
binder and does `induction p`, introducing the counter and codeword afterwards.

**The spec needs `c ≠ 0` at data positions, not just emission points.** Nothing
is emitted there, but `bump 0 = 1` flips the counter's sign, silently corrupting
the codeword. Without that premise the decoder's `d = 1` test in the `data` case
is unprovable, and the IH cannot supply it.

## The decoder is not canonicality-checking

`decode_correct` says what the decoder does with strings the encoder emits. The
converse fails, and not for a subtle reason: `[5, 7, -1]` is decoded as counter
`1`, payload `[5, 7]`, the codeword is sentinel-free, `fits 1 [5, 7]` holds, and
no encoder produces that byte string from any starting counter -- a terminating
offset of `-1` is unreachable, since `bump x ≠ -1` for every `x`. A real codeword
for `[5, 7]` ends in `-3`.

The hypotheses one would naturally reach for are therefore insufficient, and the
reason is instructive: `fits` constrains the counters the *encoder* walks through
the payload, which is not the walk the decoder performs over the codeword. In the
example the decoder's counter passes through `0`, a value no encoder state can
hold. Repairing the converse needs a well-formedness predicate on the codeword
itself. That belongs with nesting: "a skipped preempted frame leaves the outer
frame intact" is a claim about which codewords the receiver admits, not merely
which the encoder produces, so the predicate has to exist before that question can
even be asked. Without a checksum -- and ncobs has none -- no framing protocol
can promise more than this.

## Which codewords the receiver admits

`Ncobs/WF.lean` defines the predicate that answers this: walk the codeword the way
`recDecode` walks it, and require that every offset the walk actually consumes is a
legal offset, and every byte it treats as data is nonzero. `walk` mirrors
`recDecode`'s recursion exactly and is proven to track its counter
(`walk_snd_eq_recDecode_fst`).

**`encodes_iff`: the spec is exactly the receiver's acceptance set.**

```lean
Encodes c p e ↔ (recDecode e = (c, p) ∧ wfCodeword e = true)
```

Direction one (`wfCodeword_of_encodes`) says the encoder never produces anything the
receiver rejects; it goes through `fits_of_encodes`, which is worth stating on its
own. The `data` rule of the spec asks only for `c ≠ 0`, so on its face a derivation
could pass through an illegal counter. It cannot: `bump` grows magnitude
monotonically and never changes sign, so every counter before an emission is bounded
by the one eventually emitted, and emissions demand `ok`. Direction two
(`encodes_of_wfCodeword`) says the receiver never accepts anything the encoder
cannot produce, and `bump_of_shift` is its arithmetic heart -- the decoder steps
counters with `shift`, the spec with `bump`, and they are inverse off `1` (the
decoder's own branch test) and `-1` (excluded by `ok c`).

Together they make canonicality decidable by a single pass, and mean the receiver's
only rejections are real defects rather than incidental ones.

Two things the equivalence does *not* say, because neither is true. The predicate is
not merely "decode and re-encode gives back the same bytes": `[1, -128]` is a fixed
point of that round trip and is still rejected, since it spends the reserved `-128`
as an offset and `byte` will represent any `Int` without consulting `ok`. And
`fits`, the encoder-side legality check, is not the same predicate either -- it walks
the payload, the walk walks the codeword, and the divergence between them is exactly
the reason the naive converse of `decode_encode` is false.

`Test.lean` checks the equivalence exhaustively over 6,561 strings from an 8-symbol
alphabet, computing the right-hand side from the encoder (`fits` over the payload,
`recEncode` rebuilding the codeword) and comparing against the receiver's walk.
That is `native_decide`, so it validates the statement rather than the proof -- it
is the check that would have caught a misstated theorem, which is worth something
given that the first version of the predicate was misstated and a sweep caught it.

## Nesting

A low-priority frame is being streamed; a higher-priority frame starts, runs to
completion, and control returns to the interrupted frame *mid-codeword*. On the wire
the nested frame's codeword is spliced into the middle of the outer one's. The outer
offsets are frame-relative, so the splice breaks them as absolute positions, and the
receiver repairs this by shifting its target by however many bytes it skipped --
`next -= p - new_p` in the reference decoder.

`Nesting.Tr` is the transcript type, and LIFO is a property of the type rather than a
hypothesis: `cut pre inner rest` hands control to a complete frame `inner` and gets it
back at `rest`, which is the *same* frame continuing. There is no constructor that ends
a frame and later resumes another, so the interleaving the README rules out by hand
(`sf1 · encode f1 · sf2 · ef1 · encode f2 · ef2`) has no term. Repeated preemption of
one frame is expressible because `rest` may itself be a `cut`. The price is that a frame
which never calls `end_frame` is also inexpressible, so the hung-frame liveness claim
cannot be stated in this model; it needs a `hang` constructor and a receiver.

Three results carry the milestone:

- **`emit_state_eq`** -- the interrupted frame's machine state at its end does not
  depend on what was nested inside it. This is why online nesting is possible at all:
  `step` leaves `State` complete between every two bytes, so a splice needs no
  cooperation from the frame it splices into.
- **`erase_eq` / `own_eq_encode`** -- excise the nested segments from a frame's wire and
  what remains is *exactly* `encode (outer t)`, the ordinary codeword of the frame's own
  payload. Nothing about the nested frame appears in the statement. The content is
  `stream_append`: the outer counter survives the interruption, so the offsets emitted
  before the splice and after it belong to one consistent encoding. Everything else
  about nesting is bookkeeping on top of this.
- **`wire_length`** -- the wire carries the frame's own `payload + 2` bytes (`+1`
  terminating offset, `+1` sentinel, which the README does not count as overhead) plus
  exactly the nested segments' bytes. This is the skip distance in *codeword* bytes,
  which is the quantity the receiver's compensation needs; `n_cobs_nested.why` reasons
  with the decoded length instead and never states the relation.

`immediate` gives the round trip: `decodeFrame (ownOf t) = outer t`. Note what it is
*not*: `decodeFrame (wireOf t)` is false in general, because the first sentinel in a
nested wire belongs to a nested frame. Framing a nested stream needs the receiver's
skip-compensating scan, not `takeWhile`.

The two worked examples in the protocol README are in the file as `rfl`, and match
byte for byte under the Rust and Why3 sign convention (theirs is the opposite sign, so
flipping every offset reproduces their tables): frame `A B` preempted after `A` by `a`
gives `A a -2 0 B -3 0`, and frame `0 0` preempted after the first `0` by `0` gives
`-1 -1 1 0 1 1 0`. Beyond those, three `native_decide` sweeps over 1,010 generated
transcripts -- including nesting two frames deep -- check the round trip, the excision
identity, and the length relation against the independent decoder.

## The receiver's scan

`Scan.lean` is `scan_frame` transcribed into Lean: a right-to-left walk over the
received bytes, carrying a *budget* of this frame's own bytes until the next
landmark, and a flag saying whether that landmark is the frame's own boundary (the
offset that led here was negative) or a slot where a payload zero had been replaced.

Two transcription choices are worth their own sentence each.

The **branch order is copied**, including the one that looks like a typo: the test
for a sentinel byte comes *before* the zero-replacement test, so a nested frame's
sentinel meeting the walk exactly at a landmark is read as a nested frame rather
than as an offset byte. Rearranging those two branches changes which frames decode.

The **budget is in the frame's own bytes**, which is what makes the compensation a
non-event: at a nested block the walk recurses, drops the block, and continues with
the budget it already had. There is no `next -= p - new_p` arithmetic anywhere in the
model because the quantity that needed correcting was never disturbed in the first
place. Reversed lists make the same point geometrically -- the compensation is a
`drop`, and the bytes it removes never enter the budget.

To make containment statable rather than merely observable, `Result` carries the
walk's *residual state*: the budget left unspent, and the flag at the moment it
stopped. The frame is contained exactly when it lands on its own boundary with
nothing left:

```
def isComplete (r : Result) : Bool := r.left == 0 && r.atEnd
```

What is established, and how:

| | |
|---|---|
| both README decode tables reproduce | `native_decide`, byte-exact |
| payload recovery, containment, delivery order | `native_decide` over 1,010 depth-1 and 101,000 depth-2 transcripts |
| containment is not vacuous | `scanComplete [66, -3, 0] = false`: an offset claiming three bytes with one present |

**These are checks, not proofs.** The nesting results above are theorems; the scan's
correctness is computation over 102,010 wires plus the two tables by hand. That is a
real difference in kind and the file says so.

### Where the walk stops short

The obvious strengthening of containment -- that the scan consumes *exactly* the
frame's own wire -- is false. The smallest instance is an empty frame interrupted by
an empty frame:

```
wireOf (cut [] (fin []) [])     = [-1, 0, -1, 0]
scanPayload [-1, 0, -1, 0]      = []           -- correct
scanConsumed [-1, 0, -1, 0]     = 2            -- not 4
```

The outer frame's terminating offset is `-1`, so its boundary is the very next byte
left, which is the nested frame's sentinel; the boundary test fires before the nested
test and the block is never visited. **The reference decoder does exactly the same
thing** -- `next = p - |offset|`, and `p == next` with a negative offset returns at
once -- so this is a property of the protocol, not of the transcription.

It is also harmless, and that claim is checked rather than waved at: the unvisited
block lies to the *left* of where the scan stopped, so the enclosing scan meets the
same sentinel and takes the block as its own nested child; nothing is delivered twice
because a frame consumed as a block emits no output, its payload having gone out when
its own sentinel arrived. The depth-2 sweep is aimed precisely at this: 10,000
transcripts with the pathological shape under a parent frame, all three properties
holding.

## A retracted argument

I previously argued that the README's sign convention is impossible because its
chain marker would need `+128`, which does not fit an `Int8`. That was wrong: the
README uses `+127`, which fits. What `Int8`'s extra negative value actually buys
is one byte -- 126-byte frames under the code's convention, 125 under the
README's. That is a reason to prefer the code's convention, not a proof that it
is the intended one. The choice is still yours.

## Not yet formalized

- **A proof that the scan is correct.** The scan exists and is checked on 102,010
  nested wires, but containment is not *proved*. The induction needs one invariant
  tying the walk's budget to the encoder's counter: if `stream c s = (e, c')`, then
  scanning `reverse e` entered with budget `|c'| - 1` recovers `s` and lands with
  residual `|c|` and the sign of `c` as its flag. Given that, the splice argument
  goes through and containment follows for every transcript. The `Result` residual
  fields exist to make that invariant expressible; the invariant itself is the gap.
- **Long frames and `-128` chaining**, including the encoder's need to know the
  frame size in advance to place the marker.
- **Receiver-side incrementality.** The sender's is proven (`Online`), and the
  per-frame payload round trip through nesting is proven (`Nesting.immediate`). That
  a frame is reconstructible *the instant* its sentinel arrives, mid-stream, is a
  claim about the scan above, not about the codec.
- **Liveness**: a frame that never calls `end_frame` still lets every
  higher-priority frame through. Needs a stream model, not a codec one.
