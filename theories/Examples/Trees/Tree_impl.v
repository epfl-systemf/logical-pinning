(*** Tree API Implementation *)
#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
From LogicalPinning Require Import List_impl.

Set Implicit Arguments.

Import NotationForVariables.
Import NotationForTerms.

Definition _elem: field := 0%nat.
Definition _ltree: field := 1%nat.
Definition _rtree: field := 2%nat.

#[warnings="-notation-overridden"]
Notation "'_get_elem'"  := (val_get_field _elem).
Notation "'_get_ltree'" := (val_get_field _ltree).
Notation "'_get_rtree'" := (val_get_field _rtree).

#[warnings="-notation-overridden"]
Notation "'_set_elem'"  := (val_set_field _elem).
Notation "'_set_ltree'" := (val_set_field _ltree).
Notation "'_set_rtree'" := (val_set_field _rtree).

#[warnings="-notation-overridden"]
Notation "'_get_elem_ptr'"  := (val_get_field_loc _elem).
Notation "'_get_ltree_ptr'" := (val_get_field_loc _ltree).
Notation "'_get_rtree_ptr'" := (val_get_field_loc _rtree).

Notation "''pl'" := ("pl":var) : var_scope.
Notation "''pr'" := ("pr":var) : var_scope.
Notation "''pd'" := ("pd":var) : var_scope.
Notation "''pll'" := ("pll":var) : var_scope.
Notation "''plr'" := ("plr":var) : var_scope.
Notation "''prl'" := ("prl":var) : var_scope.
Notation "''prr'" := ("prr":var) : var_scope.
Notation "''sl'" := ("sl":var) : var_scope.
Notation "''sr'" := ("sr":var) : var_scope.

Definition _is_empty :=
  Fun 'p := ('p '= null).

Definition _size: val :=
  Fix 'f 'p :=
    If_ 'not (_is_empty 'p) Then (
      Let 'pl := _get_ltree 'p in
      Let 'pr := _get_rtree 'p in
      1 '+ ('f 'pl) '+ ('f 'pr)
    )
    Else 0.

Definition _incr: val :=
  Fix 'f 'p :=
    If_ 'not (_is_empty 'p) Then (
      Let 'pl := _get_ltree    'p in
      Let 'pr := _get_rtree    'p in
      Let 'pd := _get_elem_ptr 'p in
      Stdlib._incr 'pd ';
      'f 'pl ';
      'f 'pr
    ) Else ``tt.

Definition _left_rotate :=
  Fun 'p :=
    If_ 'not (_is_empty 'p) Then (
      Let 'pr := _get_rtree 'p in
      If_ 'not (_is_empty 'pr) Then (
        Let 'prl := _get_ltree 'pr in
        _set_rtree 'p  'prl ';
        _set_ltree 'pr 'p ';
        'pr
      ) Else 'p
    ) Else 'p.

Definition _right_rotate :=
  Fun 'p :=
    If_ 'not (_is_empty 'p) Then (
      Let 'pl := _get_ltree 'p in
      If_ 'not (_is_empty 'pl) Then (
        Let 'plr := _get_rtree 'pl in
        _set_rtree 'pl 'p ';
        _set_ltree 'p  'plr ';
        'pl
      ) Else 'p
    ) Else 'p.

(* p points to the tree, q points to the path *)
Definition _find: val :=
  Fix 'f 'p 'q :=
    If_ 'not (List_impl._is_empty 'q) Then (
      Let 'h := List_impl._read_front 'q in
      Let 'q1 := List_impl._pop_and_free_front 'q in
      If_ 'h '= 0 Then (
        'f (_get_ltree 'p) 'q1
      ) Else (
        'f (_get_rtree 'p) 'q1
      )
    ) Else 'p.

(* Check if a tree has value v. *)
Definition _has: val :=
  Fix 'f 'p 'v :=
    If_ 'not (_is_empty 'p) Then (
      If_ (_get_elem 'p) '= 'v Then true
      Else (
        If_ ('f (_get_ltree 'p) 'v) Then true
        Else 'f (_get_rtree 'p) 'v
      )
    ) Else false.

(* Look up first subtree with root v. *)
Definition _lookup: val :=
  Fix 'f 'p 'v :=
    If_ 'not (_is_empty 'p) Then (
      If_ (_get_elem 'p) '= 'v Then 'p
      Else (
        Let 'pl := (_get_ltree 'p) in
        If_ (_has 'pl 'v) Then 'f 'pl 'v
        Else 'f (_get_rtree 'p) 'v
      )
    ) Else null.

(* Compare two trees. The subtree-compare example does not care about the
   implementation of [_comapre]. *)
Definition _compare: val :=
  Fun 'p1 'p2 := true.
