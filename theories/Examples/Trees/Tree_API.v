(*** Non-Borrowable Trees **)

From Coq Require Import List.
Import ListNotations.

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
From LogicalPinning.Examples.Trees.LibBare Require Import Tree TreeExec.
Require Import Tree_impl.

Ltac auto_star ::=
  simpl MRecord.subst;
  try solve [ easy ];
  try solve [ intuition eauto with maths ].
Ltac auto_tilde ::=
  intros; subst; auto_star.

(** Tree Definition *)

Definition ztree: Type := tree Z.

Implicit Types (p q: loc) (x: Z) (t tl tr: ztree).

Fixpoint Tree t p: hprop :=
  match t with
  | leaf => \[p = null]
  | fork x tl tr =>
      MRecord ([(_elem,  MCell $ x);
                (_ltree, ɣI Tree $ tl);
                (_rtree, ɣI Tree $ tr)]%list) p
  end.
Arguments Tree: simpl never.

Lemma Tree_leaf: forall p, Tree leaf p = \[p = null].
Proof. reflexivity. Qed.

Lemma Tree_fork_record: forall x tl tr p,
  Tree (fork x tl tr) p
  = MRecord ([(_elem,  MCell $ x);
              (_ltree, ɣI Tree $ tl);
              (_rtree, ɣI Tree $ tr)]%list) p.
Proof. reflexivity. Qed.

Lemma Tree_fork_not_null: forall x tl tr p,
  Tree (fork x tl tr) p = Tree (fork x tl tr) p \* \[p <> null].
Proof. intros. xpull~. xchange Tree_fork_record. xchanges* MRecord_not_null. Qed.

Lemma Tree_fork_I: forall x tl tr p,
  Tree (fork x tl tr) p
  = MCell x (p+_elem)%nat \* ɣI Tree tl (p+_ltree)%nat \* ɣI Tree tr (p+_rtree)%nat
    \* \[p <> null].
Proof. intros. rewrite Tree_fork_record. simpl; unfold MField. xsimpl*. Qed.

Lemma Tree_fork_n: forall x tl tr p,
  Tree (fork x tl tr) p
  = MCell x (p+_elem)%nat
    \* \exists ql, MCell ql (p+_ltree)%nat \* Tree tl ql
    \* \exists qr, MCell qr (p+_rtree)%nat \* Tree tr qr
    \* \[p <> null].
Proof. intros. rewrite Tree_fork_I. unfold ɣI; xpull; intros; xsimpl*. Qed.

(** Tree API *)

Lemma Triple_is_empty: forall t p,
  SPEC (_is_empty p)
  PRE  (Tree t p)
  POST (fun (r: bool) => \[r = isTrue (t = leaf)] \* Tree t p).
Proof.
  xwp. mxapp Triple_eq. destruct t; rewrite isTrue_eq_isTrue_eq.
  - rewrite Tree_leaf. xsimpl*.
  - xchange Tree_fork_not_null. xsimpl*.
Qed.

Lemma Triple_get_ltree: forall p pl tl,
  SPEC (_get_ltree p)
  PRE  (MCell pl (p+_ltree)%nat \* Tree tl pl)
  POST (fun (r: loc) => \[r = pl] \* MCell pl (p+_ltree)%nat \* Tree tl pl).
Proof. xwp. mxapp Triple_ptr_add_nat. mxapp Triple_get_cell. xsimpl*. Qed.

Lemma Triple_set_ltree: forall (p pl q: loc),
  SPEC (_set_ltree p q)
  PRE  (MCell pl (p+_ltree)%nat)
  POST (fun (r: unit) => MCell q (p+_ltree)%nat).
Proof. xwp. mxapp Triple_ptr_add_nat. mxapp Triple_set_cell. xsimpl*. Qed.

Lemma Triple_get_rtree: forall p pr tr,
  SPEC (_get_rtree p)
  PRE  (MCell pr (p+_rtree)%nat \* Tree tr pr)
  POST (fun (r: loc) => \[r = pr] \* MCell pr (p+_rtree)%nat \* Tree tr pr).
Proof. xwp. mxapp Triple_ptr_add_nat. mxapp Triple_get_cell. xsimpl*. Qed.

Lemma Triple_set_rtree: forall (p pr q: loc),
  SPEC (_set_rtree p q)
  PRE  (MCell pr (p+_rtree)%nat)
  POST (fun (r: unit) => MCell q (p+_rtree)%nat).
Proof. xwp. mxapp Triple_ptr_add_nat. mxapp Triple_set_cell. xsimpl*. Qed.

Ltac handle_not_is_empty :=
  mxapp Triple_is_empty; mxapp Triple_neg; xif; auto_tilde.

Definition leftRotate [A] (t: tree A): tree A :=
  match t with
  | fork x tl (fork xr trl trr) =>
      fork xr (fork x tl trl) trr
  | _ => t
  end.

Lemma Triple_left_rotate: forall p t x tl tr,
  t = fork x tl tr ->
  SPEC (_left_rotate p)
  PRE (Tree t p)
  POST (fun (r: loc) => Tree (leftRotate t) r).
Proof.
  intros; subst.
  xwp. handle_not_is_empty.
  xchange Tree_fork_n; intros pl pr Hp.
  mxapp Triple_get_rtree.
  destruct tr as [| xr trl trr].
  - mxapp Triple_is_empty. mxapp Triple_neg. xif; intros; try easy.
    mxvals. simpl. rewrite Tree_fork_n. xsimpl*.
  - handle_not_is_empty.
    xchange Tree_fork_n; intros prl prr Hpr.
    mxapp Triple_get_ltree.
    mxapp Triple_set_rtree. mxapp Triple_set_ltree. mxval.
    simpl. rewrite Tree_fork_n. xsimpl*.
    rewrite Tree_fork_n. xsimpl*.
Qed.
