# Why COBS

## Install

- opam, through package manager
- opam install why3-ide alt-ergo
- eval $(opam env)

## Why3 ide

```shell
why3 ide cobs.why
```

## Extraction

```shell
why3 extract -D ocaml64 cobs.why  -o test_dune/bin/cobs.ml
```
