# Real Time Monitoring and Trace

De-serialization of the Real Time Monitoring and Trace (RTMT) protocol as specified by the proposed RISC-V Real Time extension.

At it core, it relies on a custom COBS like protocol for predictive and small overhead. In the following a brief overview of the protocol is presented.

A more thorough investigation is set target for current and future work. The specification for Nested COBS might eventually move to another repository.

## Nested COBS

Nested COBS (`ncobs`) - An extension of the COBS protocol allowing preemptive framing.

[COBS](http://www.stuartcheshire.org/papers/COBSforToN.pdf) (Consistent Overhead Byte Stuffing) is commonly adopted protocol for packet framing over a shared channel. The distinguishing feature is the consistent and low overhead.

- single byte overhead for short frames (up to 254 bytes)
- one byte extra overhead per 254 bytes payload

COBS encoding requires buffering on the sender side, and the implementation of an encoder walking the complete package to send.

This brings two problems regarding light-weight and real-time implementations. Firstly the buffer space requirement and secondly the unbounded blocking time (as the encoding is non-preemptive).

The former problem can be solved by reversing the protocol as implemented e.g., by [rcobs](https://github.com/Dirbaio/rcobs), which allows on-line encoding without buffering overhead. However, the fundamental shortcoming of COBS in context of real-time systems remains.

Nested COBS extends on COBS/rcobs by allowing frame preemption, while combining the advantages of both COBS and rcobs with minimal added overhead (cost).

- single byte overhead for short frames up to 127 bytes
- one byte extra overhead per 127 bytes payload (with an asymptotic overhead of 0.8% instead of 0.4% as compared to COBS/rcobs).

(Notice, as a framing marker is inevitable, it is not considered as overhead for the discussion.)

In context of real-time communication, timelines is at any rate what counts, and here is where Nested COBS shines.

- arbitrary preemption points (i.e, no critical sections on the sender side regarding the streaming output)
- immediate frame reconstruction (i.e., as soon as the last byte of a frame has been received, the associated package can be immediately reconstructed even in presence of arbitrary preemptions)

## Assumptions and Guarantees

Sender side assumptions:

- The sender needs to call `start_frame` (`sf`) before sending any data belonging to the frame. (This does not cause any data output, but needed for the state of the encoder.)
- The sender needs to call `encode` for each byte in the frame.
- The sender needs to call the `end_frame` (`ef`) after `encode` of the last byte.
- Frames can optionally have zero-sized payload (thus, `start_frame` followed by `end_frame` is legal).
- Preemptive framing under LIFO order, i.e., sequences like `sf1` `encode f1` `sf2` `ef1` `encode f2` is not allowed.  

The LIFO assumption adheres to Stack Resource Policy based scheduling, in essence we can see the transmission channel as a shared resource accessed preemptively in a nested fashion (which the highest priority always on top of the stack).  

Due to the preemptive nature, even if the sender fails to call `end_frame`, the protocol is still operational. Any new frames (higher priority) started will be guaranteed to be transmitted and received. However, on-going transmissions that were preempted by the non-ending frame will not. This property ensures suitability to mixed critical systems, where highest priority transmissions can be guaranteed to succeed even in the presence of systems partially malfunctioning, (where some lower priority transmission task is failing).

Receiver side assumptions:

The implementation uses statically allocated single buffer sufficient parametric to the `MAX_FRAME_SIZE * PRIORITY_LEVELS`, which is sufficient in the worst case. Alternatively (as the current POC implementation), dynamic allocations can be used in order to accommodate to required memory of the application.

For each byte received, the `decode` function should be called. Regarding guarantees, the decoding is immediate (as soon as the frame marker is received the package is decoded and returned). For the current implementation, output buffer is dynamic and holds all received frames (merging split frames). The user may call the `clear` function to reset the input and output buffer, in case the outermost frame has been received.

Additional protocols can be built on-top of Nested COBS, e.g., piping data to different endpoints etc., but is out of scope for this discussion.

---

## Protocol specification

### Frame Encoding

For the presentation 0 is used as the frame sentinel, like COBS/rcobs any other value could be used as marker.

Key to Nested COBS is the adoption of a *signed* offsets for the encoding. A positive value is used to indicate the offset until end (start of frame), while a negative value gives the offset to next encoded 0.

1) | 0 | 1 | 2 |
   | - | - | - |
   | A | B | C |

   will be encoded similarly to rcobs as:

   | 0 | 1 | 2 | 3 | 4 |
   | - | - | - | - | - |
   | A | B | C | 4 | 0 |

   where 4 (at index 3) is a *positive* signed offset to end (start of frame).

2) | 0 | 1 | 2 |
   | - | - | - |
   | A | 0 | C |

   will be encoded as:

   | 0 | 1 | 2 | 3  | 4 |
   | - | - | - | -  | - |
   | A | 2 | C | -2 | 0 |

   where 2 (at index 1) is the *positive* offset to end (start of frame), -2 (at index 3) the *negative* offset to next encoded 0.

3) An empty frame | |, will be encoded as:

   | 0 | 1 |
   | - | - |
   | 1 | 0 |

### Frame Decoding

Decoding starts from the end similar to rcobs.

1) We read `4`, add `C`, `B`, `A` in reverse order and reach the end (or start of frame)

2) We read `-2`, add `C`, reach `2`, and replace `2` by `0`. At this point `2` indicates the offset to end, so we add `A` and reach the start of the frame.

3) We read `1` and reach the end without adding any output.

### Nested Frame Encoding

1) Consider a frame | A | B |, preempted by a higher priority frame | a |. Column `p` gives the frame priority, while 0, 1, 2 are points in time.

   | p | 0 | 1 | 2 |
   | - | - | - | - |
   | 2 |   | a |   |
   | 1 | A |   | B |

   The frames are encoded by the sequence:

   | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
   | - | - | - | - | - | - | - |  
   | A | a | 2 | 0 | B | 3 | 0 |

2) A frame | 0 | 0 |, preempted by a higher priority frame | 0 | at time 1:

   | p | 0 | 1 | 2 |
   | - | - | - | - |
   | 2 |   | 0 |   |
   | 1 | 0 |   | 0 |

   The frames are encoded by the sequence:

   | 0 | 1 | 2  | 3 | 4  | 5  | 6 |
   | - | - | -  | - | -  | -  | - |  
   | 1 | 1 | -1 | 0 | -1 | -1 | 0 |

### Nested Frame Decoding

As for previous example we start decoding from the end. Here we focus on the outermost (lowest priority frame), inner (higher priority frames have at this point already been processed by an online implementation).

1) We read `3` (the length + 1 of the low priority frame), we read and add `B` to output. Now we run into higher priority frame (as denoted by the 0 delimiter). We skip the inner frame | a | 2 | 0 | (by decoding it and its potentially inner frames while suppressing output). We continue by reading and adding `A` and reach the end.

2) We read `-1` (the offset to next 0 to replace), we add 0, read another `-1`. Now we run into higher priority frame (as denoted by the 0 delimiter). We skip the inner frame | 1 | -1 | 0 | (by decoding and skipping it and its potentially inner frames). We continue by reading `1` (which we replace by 0) and reach the end.

### Larger frames

Using COBS, the first byte read (from left) holds the offset to next 0 to replace or if pointing to 0, the end of frame. A value 255 indicates that the frame continues with an offset of 255 to the start. This encoding allows chaining of frames with an overhead of 1/254.

In rcobs a similar approach can be taken where the last byte holds the offset. Landing the 0 marker of previous packet denotes the end, landing on 255 denotes chaining.

Nested COBS is slightly more complex, here is an example on what might go wrong with an rcobs like encoding, using 127 (max positive byte) to indicate chaining: The example shows a problematic encoding of `d0-d126` followed by `A`.

 | p | 0 | 1  | 2  | 3.. | 127 | 128 | 129 | 130 |
 | - | - | -  | -  | -   | -   | -   | -   | -   |
 | 2 |   | d0 | d1 | ... | 127 | A   | 2   | 0   |
 | 1 | x |    |    |     |     |     |     |     |

The problem here is that there is no way to tell if the read `2` indicates the end, or refers to the chain (127).

We propose to solve this as follows:

 | p | 0 | 1  | 2 | 3  | 4.. | 127  | 128 | 129 | 131 |
 | - | - | -  | - | -  | -   | -    | -   | -   | -   |
 | 2 |   | d0 | 2 | d1 | ... | d126 | A   | 127 | 0   |
 | 1 | x |    |   |    |     |      |     |     |     |

The `127` (at index 129) now refers to `2`, which in turn holds the end of frame offset. Even longer frames can be encoded, by chaining. Assume `127` was stored at index 2, our frame holds another 126 bytes, etc. so the approach generalize to arbitrary frame size.

The crux here is that the encoder needs to know the size of the frame, to know where to inject the end of frame marker (the `2` at index 2 for the example), as there is no in place-method to back-patch the end-of frame marker in an online encoder.

Notice, it is enough to know the frame size, we can still use an un-buffered encoder.The end of frame offset can be computed as size%126, while the number of chains is computed as size/126.
