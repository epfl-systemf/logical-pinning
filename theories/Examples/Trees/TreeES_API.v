(*** Trees with Borrowable Elements and Borrowable Subtrees *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning.Examples.Trees.LibBStruct Require Import Tree.
Require Import Tree_impl.

Ltac auto_star ::=
  simpl MRecord.subst;
  try solve [ easy ];
  try solve [ intuition eauto with maths res_structForall res_itemForall ].
Ltac auto_tilde ::=
  intros; subst; auto_star.

(** Tree Definition *)

Definition ztree: Type := tree (ɣb Z).
Notation "'bztree'" := (ɣb ztree).

Implicit Types (t tl tr: ztree)
               (bl btl btr: ɣb ztree)
               (z: Z) (x: ɣb Z) (n: nat)
               (p q: loc).

Fixpoint Tree t p: hprop :=
  match t with
  | leaf => \[p = null]
  | fork x bl br =>
      MRecord ([(_elem,  ɣB MCell $ x);
                (_ltree, ɣIB Tree $ bl);
                (_rtree, ɣIB Tree $ br)]%list) p
  end.
Arguments Tree: simpl never.

Lemma Tree_leaf: forall p, Tree leaf p = \[p = null].
Proof. reflexivity. Qed.

Lemma Tree_fork_not_null: forall p x bl br,
  Tree (fork x bl br) p ==> \[p <> null] \* Tree (fork x bl br) p.
Proof. intros. unfold Tree; fold Tree. xchanges* MRecord_not_null. Qed.

Lemma Tree_fork_record: forall p x bl br,
    Tree (fork x bl br) p
  = MRecord ([(_elem,  ɣB MCell $ x);
              (_ltree, ɣIB Tree $ bl);
              (_rtree, ɣIB Tree $ br)]%list) p.
Proof. reflexivity. Qed.

Lemma Tree_fork: forall p x bl br,
    Tree (fork x bl br) p
  = ɣB MCell x (p+_elem)%nat
    \* (ɣIB Tree) bl (p+_ltree)%nat
    \* (ɣIB Tree) br (p+_rtree)%nat
    \* \[p <> null].
Proof. intros. rewrite Tree_fork_record. simpl; unfold MField; xsimpl*. Qed.

(** Borrowing State Transitions *)

Section TreeTrans.

  Ltac solve_eq_with lemma :=
    intros; do 2 rewrite Tree_fork; xpull; intros;
      unfold ɣI; xpull; intros;
      [ xchanges* lemma | xchanges* <- lemma ].

  Ltac solve_to_with lemma :=
    intros; do 2 rewrite Tree_fork; xpull; intros;
      unfold ɣI; xpull; intros;
      xchanges* lemma.

  Lemma Tree_item_of_eq_b: forall p v q qs btl btr,
    Tree (fork (offered v @ q :; qs) btl btr) p = Tree (fork (borrowed @ q :; qs) btl btr) p \* MCell v q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma Tree_item_forget_fst: forall p ov q qs btl btr,
    Tree (fork (pinned ov @ q :; qs) btl btr) p ==> Tree (fork (mkB ov qs) btl btr) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma Tree_ltree_of_eq_b: forall p x tl q qs btr,
    Tree (fork x (offered tl @ q :; qs) btr) p = Tree (fork x (borrowed @ q :; qs) btr) p \* Tree tl q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma Tree_ltree_pinb_eq_b: forall p x btl q btr,
    Tree (fork x (pinb btl q) btr) p = Tree (fork x (borrowed @ q :; nil) btr) p \* ɣB Tree btl q.
  Proof. solve_eq_with Bpinb_eq_Bb. Qed.

  Lemma Tree_ltree_forget_fst: forall p x otl q qs btr,
    Tree (fork x (mkB otl (q :: qs)) btr) p ==> Tree (fork x (mkB otl qs) btr) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma Tree_ltree_forget_pinb: forall p x btl q btr,
    Tree (fork x (pinb btl q) btr) p ==> Tree (fork x btl btr) p.
  Proof. solve_to_with B_forget_pinb. Qed.

  Lemma Tree_rtree_of_eq_b: forall p x btl tr q qs,
    Tree (fork x btl (offered tr @ q :; qs)) p = Tree (fork x btl (borrowed @ q :; qs)) p \* Tree tr q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma Tree_rtree_pinb_eq_b: forall p x btl q btr,
    Tree (fork x btl (pinb btr q)) p = Tree (fork x btl (borrowed @ q :; nil)) p \* ɣB Tree btr q.
  Proof. solve_eq_with Bpinb_eq_Bb. Qed.

  Lemma Tree_rtree_forget_fst: forall p x btl otr q qs,
    Tree (fork x btl (mkB otr (q :: qs))) p ==> Tree (fork x btl (mkB otr qs)) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma Tree_rtree_forget_pinb: forall p x btl btr q,
    Tree (fork x btl (pinb btr q)) p ==> Tree (fork x btl btr) p.
  Proof. solve_to_with B_forget_pinb. Qed.

End TreeTrans.

(** Tree API *)

Section GetSet.

  Ltac solve_with lemma :=
    intros; rewrite Tree_fork_record; xapplys~ lemma.

  Lemma Triple_get_ltree: forall p x bl br,
    SPEC (_get_ltree p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: loc) => Tree (fork x (pinb bl r) br) p).
  Proof. solve_with (Triple_get_field_IB _ltree). Qed.

  Lemma Triple_get_rtree: forall p x bl br,
    SPEC (_get_rtree p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: loc) => Tree (fork x bl (pinb br r)) p).
  Proof. solve_with (Triple_get_field_IB _rtree). Qed.

  Lemma Triple_get_elem_ptr: forall p x bl br,
    SPEC (_get_elem_ptr p)
    PRE (Tree (fork x bl br) p)
    POST (fun (r: loc) => Tree (fork (pinb x r) bl br) p).
  Proof. solve_with (Triple_get_field_loc_B _elem). Qed.

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

End GetSet.

Lemma Triple_is_empty: forall p t,
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

Lemma Triple_size: forall p t,
  structForall isAvailable (owned t) ->
  SPEC (_size p)
  PRE  (Tree t p)
  POST (fun (r: Z) => \[r = size t] \* Tree t p).
Proof.
  intros p t. gen p.
  Tree_ind t as x tl tr;
    introv Hsf;
    autorewrite with rew_structForall in *;
    try easy;
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

(* Unique for TreeES *)
Lemma Triple_incr: forall p t,
  structForall isAvailable (owned t) ->
  itemForall isAvailable (owned t) ->
  SPEC (_incr p)
  PRE (Tree t p)
  POSTUNIT (Tree (map (Borrowable.map (fun v => v + 1)) t) p).
Proof.
  intros p t. gen p.
  Tree_ind t as x tl tr;
    introv Hsf Hif;
    autorewrite with rew_structForall rew_itemForall in *;
    try easy;
    xwp;
    handle_not_is_empty; [solve [mxvals*] |].
  mxapp Triple_get_ltree; intro q__tl. simpl pinb.
  mxapp Triple_get_rtree; intro q__tr. simpl pinb.
  destruct Hif as [Hx [Hif__tl Hif__tr]].
  apply isAvailable_available in Hx. destruct Hx as [vx [qs__x ->]].
  mxapp Triple_get_elem_ptr; intros qx. simpl pinb.
  xchange Tree_item_of_eq_b. mxapp Stdlib.Triple_incr.
    xchange <- Tree_item_of_eq_b. xchange Tree_item_forget_fst.
  xchange Tree_ltree_of_eq_b. mxapp* IH__tl.
    xchange <- Tree_ltree_of_eq_b. xchange Tree_ltree_forget_fst.
  xchange Tree_rtree_of_eq_b. mxapp* IH__tr.
    xchange <- Tree_rtree_of_eq_b. xchange Tree_rtree_forget_fst.
  xsimpl.
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

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
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

Ltac auto_star ::= auto_star_default.
Ltac auto_tilde ::= auto_tilde_default.
