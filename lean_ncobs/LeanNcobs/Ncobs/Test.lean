/-
  Executable sanity checks, complementing the proofs.

  `decode_encode` is proved for every payload that `fits`; the theorems say the
  protocol is right. What follows says the *definitions* still agree with
  themselves on every small payload that can be built -- which is what catches a
  transcription error in the model rather than a gap in the reasoning. The
  kernel check is the one that matters; the compiled check only widens coverage.
-/
import Lean
import LeanNcobs.Ncobs.Decode
import LeanNcobs.Ncobs.Online
import LeanNcobs.Ncobs.WF

namespace Ncobs.Test
open Ncobs

/-- All payloads over `alpha` of length at most `n`. -/
def allUpTo (alpha : List Byte) : Nat → List (List Byte)
  | 0 => [[]]
  | n + 1 =>
      let shorter := allUpTo alpha n
      shorter ++ shorter.flatMap fun l => alpha.map fun a => a :: l

def holds (p : List Byte) : Bool :=
  fits (-1) p == true && decodeBody (recEncode (-1) p) == p

/-- Kernel-checked. Kept deliberately small: `decide` evaluates in the kernel,
    and the recursion-depth limit is reached somewhere around a few hundred
    payloads, so the wide sweeps below go through `native_decide` instead. -/
theorem exhaustive_kernel : (allUpTo [0, 1, -1] 2).all holds = true := by
  decide

/-- Same, widened one step beyond what the kernel will stomach. -/
theorem exhaustive_small : (allUpTo [0, 1, -1] 3).all holds = true := by
  native_decide

/-- Widened to the byte-width boundaries: `-128` is the most negative offset the
    encoder can emit, `127` the most positive, so payloads reaching both are
    exactly where an off-by-one in the range check would show up. -/
theorem exhaustive_boundaries :
    (allUpTo [0, 1, -1, -128, 127] 4).all holds = true := by
  native_decide

/-- `fits` is not the same condition as "short". A payload whose zeros keep
    resetting the counter never approaches the reserved extreme, however long it
    is, so the round trip covers it too. What 126 buys is that it holds
    *uniformly*, for every payload of that length whatever it contains -- the
    only form of the claim a protocol can advertise without inspecting data. -/
example : fits (-1) (List.replicate 300 (0 : Byte)) = true := by native_decide
example : decodeBody (recEncode (-1) (List.replicate 300 (0 : Byte)))
          = List.replicate 300 (0 : Byte) :=
  decode_encode (by native_decide)

/-- The boundary, decided. One hundred twenty-six bytes is a legal short frame;
    one hundred twenty-seven is not, because its terminating offset would be
    `-128`, the reserved chaining marker. That single length is where the
    prototype encodes a frame and then crashes its own decoder, and it is the
    reason the advertised "up to 127 bytes" is off by one. -/
example : fits (-1) (List.replicate 126 (65 : Byte)) = true := by decide
example : fits (-1) (List.replicate 127 (65 : Byte)) = false := by decide

/-- The incremental machine agrees with the batch codec on every payload, which
    is what lets the round-trip theorem speak about the encoder that runs. -/
theorem online_matches_batch :
    (allUpTo [0, 1, -1, -128, 127] 4).all
        (fun p => Online.encodeOnline p == encode p) = true := by
  native_decide

/-- Streaming a prefix emits bytes that are already final. -/
theorem prefix_stability :
    (allUpTo [0, 1, -1] 3).all
        (fun p => List.take ((Online.stream Online.frameBegin p).1).length
                    ((Online.stream Online.frameBegin (p ++ [7, 0, 9])).1)
                  == (Online.stream Online.frameBegin p).1) = true := by
  native_decide

/-- Non-vacuity, so neither check above is checking nothing. `allUpTo` counts
    `(1 + |alpha|) ^ n`: every payload of length ≤ n over `alpha`, since each
    shorter payload contributes itself plus one extension per alphabet letter. -/
example : (allUpTo [0, 1, -1] 3).length = 64 := by native_decide
example : (allUpTo [0, 1, -1, -128, 127] 4).length = 1296 := by native_decide

end Ncobs.Test

open Ncobs

/-- **The predicate, validated by exhaustion.** Neither direction below is a
    proof; both are `native_decide`, so they check the *definition* rather than
    vouching for reasoning. Together they say the predicate is exactly as wide as
    it should be, and no wider. Each sweep covers 6,561 strings.

    (i) Everything the encoder emits is admitted. Sweeping payloads rather than
    codewords makes this independent of the walk's own bookkeeping. -/
theorem wf_admits_every_encoding :
    (Ncobs.Test.allUpTo [0, 1, -1, -2, 5, -128, 127, -3] 4).all
        (fun p => ! (fits (-1) p) || wfCodeword (recEncode (-1) p)) = true := by
  native_decide

/-- (ii) Everything admitted re-encodes to itself, i.e. is the encoding of the
    payload the decoder extracted, under the counter the decoder landed on.
    `0` counterexamples across 6,561 strings. -/
theorem wf_admits_only_canonical :
    (Ncobs.Test.allUpTo [0, 1, -1, -2, 5, -128, 127, -3] 4).all
        (fun e => ! (wfCodeword e)
          || recEncode (recDecode e).1 (recDecode e).2 == e) = true := by
  native_decide

/-- (iii) **The characterization, checked.** `encodes_iff` is now a theorem, so
    what still needs testing is whether the statement says anything true. The
    right-hand side below is computed entirely from the *encoder* -- `fits` walking
    the payload, `recEncode` rebuilding the codeword -- while the left-hand side is
    the receiver's walk. They agree on every string in the sample, which is the
    check that would have caught a misstated theorem. -/
theorem wf_matches_encoder_side :
    (Ncobs.Test.allUpTo [0, 1, -1, -2, 5, -128, 127, -3] 4).all
        (fun e => wfCodeword e
          == (fits (recDecode e).1 (recDecode e).2
              && recEncode (recDecode e).1 (recDecode e).2 == e)) = true := by
  native_decide

/-- The converse of (ii) genuinely fails, and it fails in exactly the way the
    predicate exists to prevent: a codeword that re-encodes to itself may still
    spend the reserved `-128` as an offset, since `byte` will represent any `Int`
    without checking `ok`. So `wfCodeword` is strictly narrower than "the decoder
    is a fixed point", which is the whole point. -/
example : recEncode (recDecode [1, -128]).1 (recDecode [1, -128]).2 = ([1, -128] : List Byte)
    ∧ wfCodeword [1, -128] = false := by
  decide
