# Real Time Monitoring and Trace

De-serialization of the Real Time Monitoring and Trace (RTMT) protocol as specified by the proposed RISC-V Real Time extension.

## Real-Time COBS - A Broken Frame

An extension of the cobs protocol allowing preemptive framing.

[COBS](http://www.stuartcheshire.org/papers/COBSforToN.pdf) (Consistent Overhead Byte Stuffing) is commonly adopted protocol for packet framing over a shared channel. The distinguishing feature is the consistent and low overhead.

- single byte overhead for short frames
- one byte extra overhead per 254 bytes

However COBS encoding requires buffering on the sender side, and the implementation of an encoder walking the complete package to send.

This brings two problems regarding light weight and real-time implementations. Firstly the buffer space requirement, and secondly the unbounded blocking time (as the encoding is non-preemptive).

The former problem can be solved by reversing the protocol as implemented e.g., by [rcobs](https://github.com/Dirbaio/rcobs), which allows on-line encoding without buffering overhead. However, the fundamental shortcoming of COBS in context of real-time systems remains.

Real-time COBS extends on COBS by allowing frame preemption, while remaining advantages of both `COBS` and `rcobs` with minimal added cost.

- single byte overhead for short frames
- one byte extra overhead per 127 bytes (with an asymptotic overhead of 0.8% instead of 0.4%).

(Notice, as a framing marker is inevitable, it is not considered as overhead for the discussion.)

In context of real-time communication, timelines is at any rate what counts, and here is where RT-COBS shines.

- arbitrary preemption points (i.e, no critical sections on the sender side regarding the streaming output)
- immediate frame reconstruction (i.e., as soon as the last byte of a frame has been received, the associated package can be immediately reconstructed even in presence of arbitrary preemptions)

## Guarantees

Sender side assumptions:

- The sender needs to call `start_frame` before sending any data belonging to the frame. (This does not cause any data output, but needed for the state of the encoder.)
- The sender needs to call `encode` for each byte in the frame.
- The sender needs to call the `end_frame` after `encode` of the last byte.
- Preemptive framing under LIFO order.

Frames can optionally have zero-sized payload (thus, `start_frame` followed by `end_frame` is legal).

This assumption adheres to Stack Resource Policy based scheduling, in essence we can see the transmission channel as a shared resource accessed preemptively in a nested fashion (which the highest priority always on top of the stack).  

Due to the preemptive nature, even if the sender fails to call `end_frame`, the protocol is still operational. Any new frames (higher priority) started will be guaranteed to be transmitted and received. However, on-going transmissions that were preempted by the non-ending frame will not. This property ensures suitability to mixed critical systems, where highest priority transmissions can be guaranteed to succeed even in the presence of systems partially malfunctioning, (where some lower priority transmission task is failing).
