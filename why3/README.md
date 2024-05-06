# Why COBS

## Install Opam/Why3

- opam, through package manager
- opam install why3-ide alt-ergo
- eval $(opam env)

## Other provers

Proofs provided are typically discharged by CVC5, so install through package manager.

## Setup

```shell
why3 config detect
```

## Why3 ide

```shell
why3 ide n_cobs.why
```

## Testing

```shell
why3 execute n_cobs.why --use=NestedCobs 'test_encode ()'
```

## Extraction

```shell
why3 extract -D ocaml64 cobs.why  -o test_dune/bin/cobs.ml
```

---

## Approach

While the practical implementation and use of Nested COBS might on the sender (target) side be an HDL implementation (e.g. in SystemVerilog) and on the receiver (host) in Rust, there is still a value in:

- proving the protocol to be reversible
- providing a reference implementation

### Provided proofs

- `cobs_simple.why`, a simplified version of the original COBS protocol using BigNum (zarith) representation. Reversibility (`decode(encode(l)) = l`) has been fully proven. Under this relaxation, frames can be of arbitrary size as header offset can be arbitrary large.
- `cobs_simple2.why`, essentially the same as `cobs_simple` but taking another proof approach.
- `cobs`, enforces byte size restriction to the representation (essentially replicating the byte sized behavior of the original COBS). Reversibility has not yet been fully proven.
- `n_cobs`, modelling of the proposed Nested COBS using BinNum. Implementation test and extraction works as intended. Proof is currently limited to showing that that frame marker is not present (besides in the header). Full proof or reversibility is still lacking.
