(*** Implemention of List API **)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.

Set Implicit Arguments.

Import NotationForVariables.
Import NotationForTerms.

Definition _elem: field := 0%nat.
Definition _next: field := 1%nat.

Notation "'_get_elem'" := (val_get_field _elem).
Notation "'_get_next'" := (val_get_field _next).
Notation "'_set_elem'" := (val_set_field _elem).
Notation "'_set_next'" := (val_set_field _next).
Notation "'_get_elem_ptr'" := (val_get_field_loc _elem).
Notation "'_get_next_ptr'" := (val_get_field_loc _next).

Notation "''elem'" := ("elem":var) : var_scope.
Notation "''next'" := ("next":var) : var_scope.

Definition _is_empty: val :=
  Fun 'p := 'p '= null.

Definition _new: val :=
  Fun 'elem 'next :=
    Let 'p := (val_record_alloc (_elem :: _next :: nil)) tt in
    _set_elem 'p 'elem '; _set_next 'p 'next '; 'p.

Definition _size: val :=
  Fix 'f 'p :=
    If_ 'not (_is_empty 'p) Then ('f (_get_next 'p) '+ 1) Else 0.

Definition _push_front: val :=
  Fun 'p 'x := _new 'x 'p.

Definition _incr_all: val :=
  Fix 'f 'p :=
    If_ 'not (_is_empty 'p) Then (
      Let 'q := _get_next 'p in
      Let 'd := _get_elem_ptr 'p in
      Stdlib._incr 'd ';
      'f 'q
    ) Else ``tt.

Definition _nth_elem: val :=
  Fix 'f 'p 'n :=
    If_ 'n '= 0 Then _get_elem 'p
    Else 'f (_get_next 'p) ('n '- 1).

Definition _nth_elem_ptr: val :=
  Fix 'f 'p 'n :=
    If_ 'n '= 0 Then _get_elem_ptr 'p
    Else 'f (_get_next 'p) ('n '- 1).

Definition _nth_tail: val :=
  Fix 'f 'p 'n :=
    If_ 'n '= 0 Then 'p
    Else 'f (_get_next 'p) ('n '- 1).

(* Assume p <> null. *)
Definition _get_last_node: val :=
  Fun 'p :=
    Let 'n := _size 'p in
    _nth_tail 'p ('n '- 1).

Definition _get_last_elem_ptr: val :=
  Fun 'p :=
    Let 'n := _size 'p in
    _nth_elem_ptr 'p ('n '- 1).

(* append, requires [l1 <> nil] *)
Definition _append: val :=
  Fix 'f 'p1 'p2 :=
    Let 'next := _get_next 'p1 in
    If_ (_is_empty 'next) Then _set_next 'p1 'p2
    Else 'f 'next 'p2.

Definition _append_last: val :=
  Fun 'p1 'p2 := _set_next (_get_last_node 'p1) 'p2.

(* append, allows [l1] to be [nil] or [cons] and returns a pointer. *)
(* like [nconc] in lisp *)
Definition _append_rp: val :=
  Fix 'f 'p1 'p2 :=
    If_ (_is_empty 'p1) Then 'p2
    Else (_append 'p1 'p2 '; 'p1).

(* push_back, require [l <> nil] *)
Definition _push_back: val :=
  Fun 'p 'elem := _append 'p (_new 'elem null).

(* push_back, allows [l] to be [nil] or [cons] *)
Definition _push_back_rp: val :=
  Fun 'p 'elem := _append_rp 'p (_new 'elem null).

Definition _read_front: val :=
  Fun 'p := _get_elem 'p.

Definition _pop_front: val :=
  Fun 'p :=
    Let 'next := _get_next 'p in
    val_free (_get_next_ptr 'p) ';
    'next.

Definition _free_node: val :=
  Fun 'p :=
    val_free (_get_elem_ptr 'p) ';
    val_free (_get_next_ptr 'p).

Definition _pop_and_free_front: val :=
  Fun 'p :=
    Let 'next := _get_next 'p in
    _free_node 'p '; 'next.

Definition _swap_elem: val :=
  Fun 'p 'n1 'n2 :=
    Stdlib._swap (_nth_elem_ptr 'p 'n1) (_nth_elem_ptr 'p 'n2).
