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

## A retracted argument

I previously argued that the README's sign convention is impossible because its
chain marker would need `+128`, which does not fit an `Int8`. That was wrong: the
README uses `+127`, which fits. What `Int8`'s extra negative value actually buys
is one byte -- 126-byte frames under the code's convention, 125 under the
README's. That is a reason to prefer the code's convention, not a proof that it
is the intended one. The choice is still yours.

## Not yet formalized

- **Nesting / preemption.** Needs an inductive type of well-bracketed frame
  stacks so the LIFO discipline holds by construction and `sf1 · encode f1 · sf2
  · ef1` is not a representable term. `Encodes.length` is the lemma the
  skip-distance argument rests on; `n_cobs_nested.why` uses the *decoded* length
  and never states the relation, which is a large part of why it never closed.
- **Long frames and `-128` chaining**, including the encoder's need to know the
  frame size in advance to place the marker.
- **Receiver-side preemption.** The sender's incrementality is now proven
  (`Online`). The receiver's claim -- that a frame is reconstructible the moment
  its sentinel arrives, no matter what arrived in between -- is not, and it is
  the nesting milestone.
- **Liveness**: a frame that never calls `end_frame` still lets every
  higher-priority frame through. Needs a stream model, not a codec one.
