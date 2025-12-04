# Precise Reasoning about Container-Internal Pointers with Logical Pinning

This artifact contains the mechanized formalization accompanying the article *Precise Reasoning about Container-Internal Pointers with Logical Pinning*. It provides:
- The complete Rocq development of the logical pinning model;
- The mechanized formalization of all case studies and examples stated in the paper, illustrating the application of the model and proof discipline;
- A reproducible build environment based on opam;
- Guide on how to compile the development and navigate the code structure.

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

You can run our provided build script `run.sh`. This script will:
- create a new opam switch called "lp";
- install all dependencies and compile them;
- compile our development.

At the end of running the script (this can take several minutes), if everything succeeded you should see the following line: "[logical-pinning] Compiled all proofs.".

This build script is tested on Ubuntu 24.04. For other platforms, please refer to the manual setup.

### Manual Setup

This artifact depends on the [Equations](https://github.com/mattam82/Coq-Equations) plugin, the [TLC](https://github.com/charguer/tlc.git) library and a [variant](https://github.com/yawen-guan/cfml.git) of the [CFML](https://github.com/charguer/cfml.git) library.  We have tested it with Coq 8.20.1 built with OCaml 4.14.2.  We recommend creating a clean OPAM switch for testing purposes:

```
opam update
opam switch create lp ocaml-base-compiler.4.14.2
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

We have tested the above commands on Ubuntu 24.04. For other platforms, please consult the links provided above for each package.

### Compiling this artifact

Run `make`.
