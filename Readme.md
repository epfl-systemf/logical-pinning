# Precise Reasoning about Container-Internal Pointers with Logical Pinning

## Contents

The following are the most interesting parts of the development:

### `theories/Lib`: Core library

- `Borrowable.v`: Core logic for handling borrowable values.
- `ValOps.v`: Specs and proofs for operations on single cells.
- `MRecord.v`: Definitions and lemmas of records.
- `Stdlib.v`: Helpful functions.

### `theories/Examples`: Case studies

- `Lists`: Linked lists
  - `List_impl.v`: Implementation of list APIs.
  - `ListE_API.v`: Lists with borrowable elements.
  - `ListES_API.v`: Lists with borrowable elements and borrowable tails.

- `Trees`: Binary trees
  - `Tree_impl.v`: Implementation of tree APIs.
  - `Tree_API.v`: Plain trees.
  - `Tree_E.v`: Tree with borrowable elements.
  - `Tree_S.v`: Tree with borrowable subtrees.
  - `Tree_ES.v`: Tree with borrowable elements and borrowable subtrees.

- Other examples:
  - “Logger” (using `incr_all` instead of `set_level_all`):
    `Triple_logger_example` in `ListE_API.v`.
  - “Element swapping”:
    `Triple_swap_elem` in `ListE_API.v`.
  - “find” API from CPP'16:
    `Triple_find` in `TreeS_API.v` (or `TreeES_API.v`).
  - “Binary-tree left rotation”:
    - Conceptually complicated proof using plain representation predicates:
      `Triple_left_rotate` in `Tree_API.v`
    - Simple proof using logical pinning:
      `Triple_left_rotate` in `TreeS_API.v` (or `TreeES_API.v`).
  - "Subtree-compare":
    `Triple_subtree_compare` in `TreeS_API.v`.

## Setup

### Automatic Setup

Run our provided build script `run.sh`.

### Manual Setup

This artifact depends on the [Equations](https://github.com/mattam82/Coq-Equations) plugin as well as the [CFML](https://github.com/charguer/cfml.git) and [TLC](https://github.com/charguer/tlc.git) libraries.  We have tested it with Coq 8.20.1 built with OCaml 4.14.1.  We recommend creating a clean OPAM switch for testing purposes:

```
opam update
opam switch create lp ocaml-base-compiler.4.14.1
eval $(opam env --switch=lp --set-switch)
```

### Installing Coq

```
opam pin add -y coq 8.20.1
```

### Installing `Equations`

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -y coq-equations 1.3.1+8.20
```

### Installing CFML and TLC

CFML and TLC are not hosted on OPAM, so they must be built manually.  We have included their source code in this artifact.

1. Install dependencies

   ```
   opam install -y pprint menhir
   ```

2. Build TLC and install it:

   ```
   make -C tlc -j
   make -C tlc install
   ```

3. Build CFML and install it:

   ```
   make -C cfml depend
   make -C cfml -j libcoq stdlib
   ```

### Compiling this artifact

Run `make`.
