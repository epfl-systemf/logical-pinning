(*** Trees with Borrowable Elements *)

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

Definition ztree: Type := tree (ɣb Z).

Implicit Types (p q: loc) (x: ɣb Z) (v: Z) (t tl tr: ztree).

Fixpoint Tree t p :=
  match t with
  | leaf => \[p = null]
  | fork x tl tr =>
      MRecord ([(_elem,  ɣB MCell $ x);
                (_ltree, ɣI Tree $ tl);
                (_rtree, ɣI Tree $ tr)]%list) p
  end.
Arguments Tree: simpl never.

Lemma Tree_leaf: forall p, Tree leaf p = \[p = null].
Proof. reflexivity. Qed.

Lemma Tree_fork_record: forall p x tl tr,
  Tree (fork x tl tr) p = MRecord ([(_elem,  ɣB MCell $ x);
                                     (_ltree, ɣI Tree $ tl);
                                     (_rtree, ɣI Tree $ tr)]%list) p.
Proof. reflexivity. Qed.

Lemma Tree_fork_I: forall x tl tr p,
  Tree (fork x tl tr) p
  =    ɣB MCell x (p+_elem)%nat
    \* ɣI Tree tl (p+_ltree)%nat
    \* ɣI Tree tr (p+_rtree)%nat
    \* \[p <> null].
Proof. intros. rewrite Tree_fork_record. simpl; unfold MField. xsimpl~. Qed.

Lemma Tree_fork_not_null: forall x tl tr p,
  Tree (fork x tl tr) p = Tree (fork x tl tr) p \* \[p <> null].
Proof. intros. xpull~. xchange Tree_fork_record. xchanges* MRecord_not_null. Qed.

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

Ltac handle_not_is_empty :=
  mxapp Triple_is_empty; mxapp Triple_neg; xif; auto_tilde.

Lemma Triple_size: forall t p,
  SPEC (_size p)
  PRE (Tree t p)
  POST (fun (r: Z) => \[r = size t] \* Tree t p).
Proof.
  induction t as [| x tl IHtl tr IHtr];
    xwp;
    handle_not_is_empty; [ solve [mxvals*] | ].
  xchange Tree_fork_record.
  mxapp* Triple_get_field_I; intros ql.
  mxapp* Triple_get_field_I; intros qr.
  xchange* (MRecord_IBp_eq_cell_and_B _ltree). xchange Bo_eq_n.
    mxapp IHtl. mxapp Triple_add.
  xchange* (MRecord_IBp_eq_cell_and_B _rtree). xchange Bo_eq_n.
    mxapp IHtr. mxapp Triple_add.
  xchange* (MRecord_I_fold _ltree).
  xchange* (MRecord_I_fold _rtree).
  xchanges <- Tree_fork_record. simpl; math.
Qed.

Lemma spec_incr: forall (p: loc) (t: ztree),
  TreeExec.Forall is_available t = true ->
  SPEC (_incr p)
  PRE (Tree t p)
  POSTUNIT (Tree (Tree.map (Borrowable.map (fun v => v + 1)) t) p).
Proof.
  (* Convert [TreeExec.Forall] to [Tree.Forall] *)
  introv H. erewrite TreeExec.Forall_eq in H; [| apply isAvailable_isTrue_pred].
  rewrite isTrue_eq_true_eq in H.

  gen p.
  induction t as [| x tl IHtl tr IHtr];
    autorewrite with rew_Forall in *; simpl in *;
    xwp;
    handle_not_is_empty; [ solve [mxvals*] | ].

  xchange Tree_fork_record.
  mxapp* Triple_get_field_I; intros pl.
  mxapp* Triple_get_field_I; intros pr.
  destruct H as [Hx *].
  apply isAvailable_available in Hx. destruct Hx as [vx [qs__x ->]].
  mxapp* Triple_get_field_loc_B; intros px. simpl pinb.
  xchange~ (MRecord_Bof_eq_Bb _elem).
    mxapp Stdlib.Triple_incr.
    xchange* (MRecord_Bb_eq_Bof _elem).
    xchange* (MRecord_B_forget_fst _elem).
  xchange* (MRecord_IBp_eq_cell_and_B _ltree). xchange* Bo_eq_n.
    mxapp* IHtl.
    xchange* (MRecord_I_fold _ltree).
  xchange* (MRecord_IBp_eq_cell_and_B _rtree). xchange* Bo_eq_n.
    mxapp* IHtr.
    xchange* (MRecord_I_fold _rtree).
  xchanges* <- Tree_fork_record.
Qed.

Ltac auto_star ::= auto_star_default.
Ltac auto_tilde ::= auto_tilde_default.
