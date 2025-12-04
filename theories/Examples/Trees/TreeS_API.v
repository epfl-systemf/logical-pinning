(*** Trees with Borrowable Subtrees *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning.Examples.Trees.LibBStruct Require Import Tree.
Require Import Coq.Arith.PeanoNat.
Require Import Tree_impl.

Import NotationForVariables.
Import NotationForTerms.

(** Tactics *)

Ltac auto_star ::=
  simpl MRecord.subst;
  try solve [ easy ];
  try solve [ intuition eauto with maths res_structForall ].
Ltac auto_tilde ::=
  intros; subst; auto_star.
Ltac my_simpl := simpl in *; simp isIn substk lookup rew_structForall in *.

(** Tree Definition *)

Implicit Types (t: tree nat) (bt: ɣb tree nat) (k: nat) (p q: loc).

Notation "bt ⟦ k ':=' bt1 ⟧" := (substk Nat.eqb k bt1 bt)
  (at level 64, right associativity).
Notation "bt ⟦ k ⟧" := (lookup Nat.eqb k (missing) bt)
  (at level 64, right associativity).
Notation "k '∈?' bt " := (isIn Nat.eqb k bt)
  (at level 64, right associativity).

Fixpoint Tree t p: hprop :=
  match t with
  | leaf => \[p = null]
  | fork x btl btr =>
      MRecord ([(_elem,  MCell $ x);
                (_ltree, ɣIB Tree $ btl);
                (_rtree, ɣIB Tree $ btr)]%list) p
  end.
Arguments Tree: simpl never.

Lemma Tree_leaf: forall p, Tree leaf p = \[p = null].
Proof. reflexivity. Qed.

Lemma Tree_fork_not_null: forall p x bl br,
  Tree (fork x bl br) p ==> \[p <> null] \* Tree (fork x bl br) p.
Proof. intros. unfold Tree; fold Tree. xchanges* MRecord_not_null. Qed.

Lemma Tree_fork_record: forall p x bl br,
    Tree (fork x bl br) p
  = MRecord ([(_elem,  MCell $ x);
              (_ltree, ɣIB Tree $ bl);
              (_rtree, ɣIB Tree $ br)]%list) p.
Proof. reflexivity. Qed.

Lemma Tree_fork: forall p x bl br,
    Tree (fork x bl br) p
  = MCell x (p+_elem)%nat
    \* (ɣIB Tree) bl (p+_ltree)%nat
    \* (ɣIB Tree) br (p+_rtree)%nat
    \* \[p <> null].
Proof. intros. rewrite Tree_fork_record. simpl; unfold MField; xsimpl*. Qed.

Lemma Tree_fork_Bsubtrees: forall p x bl br,
    Tree (fork x bl br) p
  = MCell x (p+_elem)%nat
    \* \exists ql, MCell ql (p+_ltree)%nat \* (ɣB Tree) bl ql
    \* \exists qr, MCell qr (p+_rtree)%nat \* (ɣB Tree) br qr
    \* \[p <> null].
Proof. intros. rewrite Tree_fork. unfold ɣI. xsimpl*. Qed.

Section TreeTrans.

  Ltac solve_eq_with lemma :=
    intros; do 2 rewrite Tree_fork; xpull; intros;
      unfold ɣI; xpull; intros;
      [ xchanges* lemma | xchanges* <- lemma ].

  Ltac solve_to_with lemma :=
    intros; do 2 rewrite Tree_fork; xpull; intros;
      unfold ɣI; xpull; intros;
      xchanges* lemma.

  Lemma Tree_ltree_of_eq_b: forall p x tl q qs btr,
    Tree (fork x (offered tl @ q :; qs) btr) p = Tree (fork x (borrowed @ q :; qs) btr) p \* Tree tl q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma Tree_ltree_forget_fst: forall p x otl q qs btr,
    Tree (fork x (mkB otl (q :: qs)) btr) p ==> Tree (fork x (mkB otl qs) btr) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma Tree_ltree_pinb_eq_b: forall p x btl q btr,
    Tree (fork x (pinb btl q) btr) p = Tree (fork x (borrowed @ q :; nil) btr) p \* ɣB Tree btl q.
  Proof using. solve_eq_with Bpinb_eq_Bb. Qed.

  Lemma Tree_ltree_forget_pinb: forall p x btl q btr,
    Tree (fork x (pinb btl q) btr) p ==> Tree (fork x btl btr) p.
  Proof using. solve_to_with B_forget_pinb. Qed.

  Lemma Tree_rtree_of_eq_b: forall p x btl tr q qs,
    Tree (fork x btl (offered tr @ q :; qs)) p = Tree (fork x btl (borrowed @ q :; qs)) p \* Tree tr q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma Tree_rtree_forget_fst: forall p x btl otr q qs,
    Tree (fork x btl (mkB otr (q :: qs))) p ==> Tree (fork x btl (mkB otr qs)) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma Tree_rtree_pinb_eq_b: forall p x btl q btr,
    Tree (fork x btl (pinb btr q)) p = Tree (fork x btl (borrowed @ q :; nil)) p \* ɣB Tree btr q.
  Proof using. solve_eq_with Bpinb_eq_Bb. Qed.

  Lemma Tree_rtree_forget_pinb: forall p x btl btr q,
    Tree (fork x btl (pinb btr q)) p ==> Tree (fork x btl btr) p.
  Proof using. solve_to_with B_forget_pinb. Qed.

  Lemma Tree_pinb_eq_b: forall v p bt bt1 q,
    v ∈? bt = true ->
    ɣB Tree (bt⟦v := pinb bt1 q⟧) p = ɣB Tree (bt⟦v := borrowed @ q :; []⟧) p \* ɣB Tree bt1 q.
  Proof using.
    intros v p bt. gen v p.
    BTree_ind bt;
      intros; my_simpl; try easy.
    destruct (Nat.eqb x v) eqn: EQxv; my_simpl.
    - rewrite* Bpinb_eq_Bb.
    - destruct (isIn Nat.eqb v btl) eqn: Vinl; my_simpl.
      all: unfold ɣB at 1 2; do 2 rewrite Tree_fork_Bsubtrees.
      + xpull; intros; xsimpl*; [xchange* IHl | xchange* <- IHl].
      + xpull; intros; xsimpl*; [xchange* IHr | xchange* <- IHr].
  Qed.

  Lemma Tree_forget_pinb: forall v p bt bt1 q,
    ɣB Tree (bt⟦v := pinb bt1 q⟧) p ==> ɣB Tree (bt⟦v := bt1⟧) p.
  Proof using.
    intros v p bt. gen v p.
    BTree_ind bt;
      intros; my_simpl; try solve [xsimpl].
    destruct (Nat.eqb x v) eqn: EQxv; my_simpl.
    - xchange B_forget_pinb.
    - destruct (isIn Nat.eqb v btl) eqn: Vinl;
        unfold ɣB at 1 2; do 2 rewrite Tree_fork_Bsubtrees; xpull; xsimpl*.
  Qed.

  Lemma Tree_forget_pinb_substk_lookup_same: forall v u p q bt,
    v ∈? bt = true ->
    ɣB Tree (bt⟦v := pinb (bt⟦v⟧) q⟧⟦u⟧) p ==> ɣB Tree (bt⟦u⟧) p.
  Proof using.
    intros v u p q bt. gen v u p q.
    BTree_ind bt;
      introv H; my_simpl; try easy.
    destruct (Nat.eqb x v) eqn: EQxv; my_simpl;
      destruct (Nat.eqb x u) eqn: EQxu; my_simpl;
      xsimpl; try solve [xchange B_forget_fst].
    - destruct (v ∈? btl) eqn: Vinl; my_simpl; rewrite EQxu;
      unfold ɣB; do 2 rewrite Tree_fork_Bsubtrees; xpull; intros; xsimpl*;
      xchange Tree_forget_pinb; rewrite* substk_lookup_same.
    - destruct (v ∈? btl) eqn: Vinl; my_simpl; rewrite EQxu;
        destruct (u ∈? btl) eqn: Uinl; my_simpl; [.. | solve [xsimpl]].
      all: rewrite isIn_substk_pinb; rewrite Uinl.
      + apply* IHl.
      + xsimpl.
  Qed.

  Lemma Tree_forget_pinb_substk_substk: forall v u p q bt bt1,
    v ∈? bt = true ->
    ɣB Tree (bt⟦v := pinb (bt⟦v⟧) q⟧⟦u := bt1⟧) p ==> ɣB Tree (bt⟦u := bt1⟧) p.
  Proof using.
    intros v u p q bt. gen v u p q.
    BTree_ind bt;
      introv H; my_simpl; try easy.
    destruct (Nat.eqb x v) eqn: EQxv; my_simpl;
      destruct (Nat.eqb x u) eqn: EQxu; my_simpl;
      try solve [xsimpl].
    - destruct (u ∈? btl) eqn: Uinl; my_simpl; xchange B_forget_fst.
    - destruct (v ∈? btl) eqn: Vinl; my_simpl; rewrite EQxu; xsimpl.
    - destruct (v ∈? btl) eqn: Vinl; my_simpl; rewrite EQxu;
        destruct (u ∈? btl) eqn: Uinl; my_simpl.
      1, 2: rewrite isIn_substk_pinb; rewrite Uinl.
      all: unfold ɣB; do 2 rewrite Tree_fork_Bsubtrees; xpull; intros; xsimpl*.
      all: xchange Tree_forget_pinb; rewrite* substk_lookup_same.
  Qed.

End TreeTrans.

Section TreeGetSet.

  Ltac solve_with lemma :=
    intros; rewrite Tree_fork_record; xapplys~ lemma.

  Lemma Triple_get_elem: forall p x bl br,
    SPEC (_get_elem p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: nat) => \[r = x] \* Tree (fork x bl br) p).
  Proof using. solve_with (Triple_get_field_cell _elem). Qed.

  Lemma Triple_get_ltree: forall p x bl br,
    SPEC (_get_ltree p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: loc) => Tree (fork x (pinb bl r) br) p).
  Proof using. solve_with (Triple_get_field_IB _ltree). Qed.

  Lemma Triple_get_rtree: forall p x bl br,
    SPEC (_get_rtree p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: loc) => Tree (fork x bl (pinb br r)) p).
  Proof using. solve_with (Triple_get_field_IB _rtree). Qed.

  Lemma Triple_set_ltree: forall p q x bl br,
    SPEC (_set_ltree p q)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: unit) => Tree (fork x (borrowed @ q :; nil) br) p \* \exists r, ɣB Tree bl r).
  Proof. solve_with (Triple_set_field_IB _ltree). Qed.

  Lemma Triple_set_rtree: forall p q x bl br,
    SPEC (_set_rtree p q)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: unit) => Tree (fork x bl (borrowed @ q :; nil)) p \* \exists q, ɣB Tree br q).
  Proof. solve_with (Triple_set_field_IB _rtree). Qed.

End TreeGetSet.

Lemma Triple_is_empty: forall p t,
  SPEC (_is_empty p)
  PRE  (Tree t p)
  POST (fun (r: bool) => \[r = isTrue (t = leaf)] \* Tree t p).
Proof using.
  xwp. mxapp Triple_eq. destruct t; rewrite isTrue_eq_isTrue_eq.
  - rewrite Tree_leaf. xsimpl*.
  - xchange Tree_fork_not_null. xsimpl*.
Qed.

Ltac solve_post := solve [mxval*; unfold ɣB at 1; xsimpl*].

Ltac handle_not_is_empty :=
  mxapp Triple_is_empty; mxapp Triple_neg; xif; auto_tilde.

Lemma Triple_size: forall p bt,
  structForall isAvailable bt ->
  SPEC (_size p)
  PRE  (ɣB Tree bt p)
  POST (fun (r: Z) => \[r = sizeb bt] \* ɣB Tree bt p).
Proof using.
  intros p bt. gen p.
  BTree_ind bt;
    introv SF;
    simp rew_structForall in *; try easy;
    xwp; unfold ɣB at 1; xpull; intros Hqs;
    handle_not_is_empty; [solve_post |].
  mxapp Triple_get_ltree; intros q1.
  mxapp Triple_get_rtree; intros q2.
  xchange Tree_ltree_pinb_eq_b;
    mxapp* IHl; mxapp Triple_add;
    xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
  xchange Tree_rtree_pinb_eq_b;
    mxapp* IHr; mxapp Triple_add;
    xchange <- Tree_rtree_pinb_eq_b; xchange Tree_rtree_forget_pinb.
  rewrite sizeb_fork. unfold ɣB at 1; xsimpl*.
Qed.

Lemma Triple_size': forall p t,
  structForall isAvailable (owned t) ->
  SPEC (_size p)
  PRE  (Tree t p)
  POST (fun (r: Z) => \[r = size t] \* Tree t p).
Proof.
  intros p t. gen p.
  Tree_ind t as x tl tr;
    introv SF;
    my_simpl; try easy;
    xwp;
    handle_not_is_empty; [solve [mxvals*] |].
  mxapp Triple_get_ltree; intros q__tl. simpl pinb.
  mxapp Triple_get_rtree; intros q__tr. simpl pinb.
  xchange Tree_ltree_of_eq_b. mxapp* IH__tl. mxapp Triple_add.
  xchange Tree_rtree_of_eq_b. mxapp* IH__tr. mxapp Triple_add.
  xchange <- Tree_ltree_of_eq_b. xchange Tree_ltree_forget_fst.
  xchange <- Tree_rtree_of_eq_b. xchange Tree_rtree_forget_fst.
  xsimpl; simpl; math.
Qed.

Lemma Triple_left_rotate: forall p t x btl tr qs__tr,
  t = fork x btl (available tr @ qs__tr) ->
  SPEC (_left_rotate p)
  PRE (Tree t p)
  POST (fun (r: loc) => ɣB Tree (leftRotateb (offered t @ p :; nil)) r).
Proof.
  intros; subst. xwp. handle_not_is_empty.
  mxapp Triple_get_rtree; intros pr. simpl pinb.
  xchange Tree_rtree_of_eq_b.
  destruct tr as [| xr btrl btrr];
    handle_not_is_empty; simpl in *.
  - mxvals.
    xchange <- Tree_rtree_of_eq_b. xchange Tree_rtree_forget_fst.
    xchange <- Bo_eq_n. xchanges B_pin.
  - mxapp Triple_get_ltree; intros prl.
    mxapp Triple_set_rtree; intros pr1.
      unfold ɣB; xpull; simpl; intros [-> Hpr].
    mxapp Triple_set_ltree; intros prl1.
      xchange B_pinb_extract; intros ->. xchange B_forget_pinb.
    xchange <- Tree_rtree_pinb_eq_b. xchange Tree_rtree_forget_pinb.
    xchange <- Tree_ltree_of_eq_b.
    mxvals*.
Qed.

Section FindExample.

#[warnings="-require-in-section -notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import ListE_API.

Lemma Triple_find: forall l p__t p__l bt bt1,
  Forall isAvailable l ->
  find bt l = Some bt1 ->
  SPEC (_find p__t p__l)
  PRE (ɣB Tree bt p__t \* List__e l p__l)
  POST (fun (r: loc) => ɣB Tree (subst bt (pinb bt1 r) l) p__t).
Proof.
  induction l as [| x l1];
    introv Hl Ht; xwp;
    mxapp Triple_is_empty; mxapp Triple_neg; xif; intros; try easy; clear H.
  { xchange List__e_nil; intros. mxvals. }
  apply Forall_inv in Hl as Hx. apply Forall_inv_tail in Hl as Hl1.
  apply isAvailable_available in Hx. destruct Hx as [v__x [qs__x ->]].
  mxapp Triple_read_front.
  mxapp Triple_pop_and_free_front; intros p__l1.
  mxapp Triple_eq; xif; intros H__vx.
  all: apply find_cons in Ht as H__bt; destruct H__bt as [x__t [btl [btr [qs ->]]]];
    unfold ɣB at 1; xpull; intros Heq.
  1: mxapp Triple_get_ltree; intros q; xchange Tree_ltree_pinb_eq_b.
  2: mxapp Triple_get_rtree; intros q; xchange Tree_rtree_pinb_eq_b.
  all: simpl in Ht; destruct v__x; try easy;
    mxapp* IHl1; intros q'; simpl.
  1: xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
  2,3: xchange <- Tree_rtree_pinb_eq_b; xchange Tree_rtree_forget_pinb.
  all: unfold ɣB; xsimpl*.
Qed.

End FindExample.

Lemma Triple_has: forall p k bt,
  structForall isAvailable bt ->
  SPEC (_has p k)
  PRE  (ɣB Tree bt p)
  POST (fun (r: bool) => \[r = k ∈? bt] \* ɣB Tree bt p).
Proof using.
  intros p k bt. gen p k.
  BTree_ind bt;
    introv SF; my_simpl; try easy;
    xwp; unfold ɣB at 1; xpull; intros Hqs;
    handle_not_is_empty; [solve_post |].
  mxapp Triple_get_elem. mxapp Triple_eq.
  xif; simpl; intros EQxk; subst.
  - (* x = k *)
    rewrite Nat.eqb_refl. solve_post.
  - (* x <> k *)
    mxapp Triple_get_ltree; intros p1.
    xchange Tree_ltree_pinb_eq_b;
      mxapp* IHl;
      xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
    destruct (k ∈? btl) eqn: Kinl; xif; try easy; intros _.
    + (* k in btl *)
      apply Nat.eqb_neq in EQxk; rewrite EQxk. solve_post.
    + (* k in btr *)
      mxapp Triple_get_rtree; intros p2.
      xchange Tree_rtree_pinb_eq_b;
        mxapp* IHr;
        xchange <- Tree_rtree_pinb_eq_b; xchange Tree_rtree_forget_pinb.
      apply Nat.eqb_neq in EQxk; rewrite EQxk. unfold ɣB at 1; xsimpl*.
Qed.

Lemma Triple_lookup_absent: forall p k bt,
  k ∈? bt = false ->
  structForall isAvailable bt ->
  SPEC (_lookup p k)
  PRE  (ɣB Tree bt p)
  POST (fun (r: loc) => \[r = null] \* ɣB Tree bt p).
Proof using.
  intros p k bt. gen p k.
  BTree_ind bt;
    introv H SF; do 2 my_simpl; try easy;
    xwp; unfold ɣB at 1; xpull; intros Hqs;
    handle_not_is_empty; [solve_post |].
  mxapp Triple_get_elem. mxapp Triple_eq.
  xif; simpl; intros EQxk; subst.
  - (* x = k *)
    rewrite Nat.eqb_refl in H. easy.
  - (* x <> k *)
    apply Nat.eqb_neq in EQxk; rewrite EQxk in H.
    mxapp Triple_get_ltree; intros p1.
    xchange Tree_ltree_pinb_eq_b;
      mxapp* Triple_has.
      xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
    destruct (k ∈? btl) eqn: Kinl; xif; try easy; intros _.
    (* k is not in btl *)
    mxapp Triple_get_rtree; intros p2.
    xchange Tree_rtree_pinb_eq_b;
      mxapp* IHr;
      xchange <- Tree_rtree_pinb_eq_b; xchange Tree_rtree_forget_pinb.
    unfold ɣB at 1; xsimpl*.
Qed.

Lemma Triple_lookup_present: forall p k bt,
  k ∈? bt = true ->
  structForall isAvailable bt ->
  SPEC (_lookup p k)
  PRE  (ɣB Tree bt p)
  POST (fun (r: loc) => ɣB Tree (bt⟦k := pinb (bt⟦k⟧) r⟧) p).
Proof using.
  intros p k bt. gen p k.
  BTree_ind bt;
    introv H SF; my_simpl; try easy.
  xwp; unfold ɣB at 1; xpull; intros Hqs; handle_not_is_empty.
  mxapp Triple_get_elem. mxapp Triple_eq.
  xif; simpl; intros EQxk; subst.
  - (* x = k *)
    mxval. do 2 (rewrite Nat.eqb_refl; my_simpl). unfold ɣB; xsimpl*.
  - (* x <> k *)
    apply Nat.eqb_neq in EQxk; rewrite EQxk in H.
    mxapp Triple_get_ltree; intros p1.
    xchange Tree_ltree_pinb_eq_b; mxapp* Triple_has.
    destruct (k ∈? btl) eqn: Kinl; my_simpl; rewrite EQxk;
      xif; try easy; intros _.
    + (* k in btl *)
      mxapp* IHl; intros r1.
      xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
      my_simpl; rewrite EQxk, Kinl. unfold ɣB at 1; xsimpl*.
    + (* k in btr *)
      xchange <- Tree_ltree_pinb_eq_b; xchange Tree_ltree_forget_pinb.
      mxapp Triple_get_rtree; intros p2.
      xchange Tree_rtree_pinb_eq_b;
        mxapp* IHr; intros r2.
        xchange <- Tree_rtree_pinb_eq_b; xchange Tree_rtree_forget_pinb.
      my_simpl; rewrite EQxk, Kinl; my_simpl. unfold ɣB at 1; xsimpl*.
Qed.

Lemma Triple_compare: forall (p1 p2: loc) bt1 bt2 (H1 H2: hprop),
  structForall isAvailable bt1 ->
  structForall isAvailable bt2 ->
  SPEC (_compare p1 p2)
  PRE (hand (ɣB Tree bt1 p1 \* H1) (ɣB Tree bt2 p2 \* H2))
  POST (fun (r: bool) => \[r = true] \* ɣB Tree bt2 p2 \* H2).
Proof using.
  introv SF1 SF2. xwp. mxval.
  xchange himpl_hand_l_l. xsimpl*.
Qed.

Section SubtreeCompareExample.

Context (f: btree nat -> btree nat -> bool).

Context (Triple_compare: forall (p1 p2: loc) bt1 bt2 (H1 H2: hprop),
  structForall isAvailable bt1 ->
  structForall isAvailable bt2 ->
  SPEC (_compare p1 p2)
  PRE (hand (ɣB Tree bt1 p1 \* H1) (ɣB Tree bt2 p2 \* H2))
  POST (fun (r: bool) => \[r = f bt1 bt2] \* ɣB Tree bt2 p2 \* H2)).

Definition _subtree_compare: val :=
  Fun 'p 'v1 'v2 :=
    Let 'q1 := _lookup 'p 'v1 in
    Let 'q2 := _lookup 'p 'v2 in
    Let 'r := _compare 'q1 'q2 in
    'r.

Lemma Triple_subtree_compare: forall p bt (k1 k2: nat),
  structForall isAvailable bt ->
  k1 ∈? bt = true ->
  k2 ∈? bt = true ->
  SPEC (_subtree_compare p k1 k2)
  PRE (ɣB Tree bt p)
  POST (fun (r: bool) => \[r = f (bt⟦k1⟧) (bt⟦k2⟧)] \* ɣB Tree bt p).
Proof using Triple_compare.
  introv SF H1 H2. xwp.
  mxapp* Triple_lookup_present; intros q1.
  mxapp Triple_lookup_present.
  { rewrite* isIn_substk_pinb. }
  { apply* structForall_isAvailable_substk_pinb. }
  intros q2.
  set (bt1 := bt⟦k1⟧). set (bt2 := bt⟦k1 := pinb bt1 q1⟧⟦k2⟧).
  mxapp_pre tt.
  applys xapp_untyped_lemma_hand Triple_compare.
  - apply* (structForall_isAvailable_lookup Nat.eqb k1).
  - apply* (structForall_isAvailable_lookup Nat.eqb k2).
  - (* [ɣB Tree (bt⟦k1 := pinb bt1 q1⟧⟦k2 := pinb bt2 q2⟧) p ==> ɣB Tree (bt⟦k1⟧) q1 \* ?H1] *)
    xchange (Tree_forget_pinb k2).
    subst bt2. rewrite substk_lookup_same;
      [| solve [subst bt1; rewrite* isIn_substk_pinb]].
    xchanges* (Tree_pinb_eq_b k1).
  - (* [ɣB Tree (bt⟦k1 := pinb bt1 q1⟧⟦k2 := pinb bt2 q2⟧) p ==> ɣB Tree (bt⟦k2⟧) q2 \* ?H2] *)
    xchanges (Tree_pinb_eq_b k2). { subst bt1; rewrite* isIn_substk_pinb. }
    xchange* Tree_forget_pinb_substk_substk.
    subst bt2; xchange* Tree_forget_pinb_substk_lookup_same.
  - (* postcondition *)
    xapp_simpl tt. intros r ->.
    xchange* <- (Tree_pinb_eq_b k2); xchange (Tree_forget_pinb k2).
    subst bt2; rewrite* substk_lookup_same. mxvals*.
Qed.

End SubtreeCompareExample.

Ltac auto_star ::= auto_star_default.
Ltac auto_tilde ::= auto_tilde_default.
