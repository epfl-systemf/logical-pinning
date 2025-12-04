(*** Library: Trees with generic elements and borrowable substructures. *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.

#[warnings="-notation-incompatible-prefix"]
From Equations Require Export Equations.

From Coq Require Export List.
Export ListNotations.

(* tree *)

Inductive tree {A} :=
| leaf
| fork (v: A) (bl: ɣb tree) (br: ɣb tree).
Arguments tree: clear implicits.

Notation "'btree' A" := (ɣb tree A)
  (at level 64, no associativity).

Definition ltree [A] (t: tree A): btree A :=
  match t with
  | leaf => missing
  | fork _ bl _ => bl
  end.

Definition rtree [A] (t: tree A): btree A :=
  match t with
  | leaf => missing
  | fork _ _ br => br
  end.

Inductive direction := dirL | dirR.

Notation "'path'" := (list direction)
  (at level 64, no associativity).

Fixpoint size [A] (t: tree A): nat :=
  match t with
  | leaf => O
  | fork _ bl br =>
      let sl := (match bl with
                | available tl @ _ => size tl
                | _ => O
                end) in
      let sr := (match br with
                | available tr @ _ => size tr
                | _ => O
                end) in
      1 + sl + sr
  end.

Definition sizeb [A] (bt: btree A): nat :=
  match bt with
  | available t @ _ => size t
  | _ => O
  end.

Lemma sizeb_fork: forall [A] (x: A) (btl btr: btree A) qs,
  sizeb (available (fork x btl btr) @ qs) = (1 + sizeb btl + sizeb btr)%nat.
Proof.
  intros. simpl. destructb btl as tl; destructb btr as tr; simpl; math.
Qed.

Section treeIndPrinciple.

  Context A (P: tree A -> Prop)
    (evPleaf: P leaf)
    (evPfork: forall x bl br, pred P bl -> pred P br -> P (fork x bl br)).

  Fixpoint better_tree_ind (t: tree A): P t :=
    match t with
    | leaf => evPleaf
    | fork x bl br => evPfork x bl br (prove P better_tree_ind bl) (prove P better_tree_ind br)
    end.

End treeIndPrinciple.

Ltac tree_ind t x tl tr :=
  let btl := fresh "btl" in
  let btr := fresh "btr" in
  let IH__tl := fresh "IH__" tl in
  let IH__tr := fresh "IH__" tr in
  let qs__tl := fresh "qs__" tl in
  let qs__tr := fresh "qs__" tr in
  pattern t;
  eapply better_tree_ind;
  [ | intros x btl btr IH__tl IH__tr; destruct btl as [[tl |] qs__tl]; destruct btr as [[tr |] qs__tr] ].

Tactic Notation "Tree_ind" ident(t) :=
  let x := fresh "x" in
  let tl := fresh "tl" in
  let tr := fresh "tr" in
  tree_ind t x tl.
Tactic Notation "Tree_ind" ident(t) "as" ident(x) ident(tl) ident(tr) := tree_ind t x tl tr.

Section btreeIndPrinciple.

  Context A (P: btree A -> Prop)
    (evPnone: forall qs, P (unavailable @ qs))
    (evPsomel: forall qs, P (available leaf @ qs))
    (evPsomef: forall x btl btr qs, P btl -> P btr -> P (available (fork x btl btr) @ qs)).

  Equations btree_ind (bt: btree A): P bt by wf (sizeb bt) :=
  | unavailable @ qs := evPnone qs
  | available leaf @ qs := evPsomel qs
  | available (fork x btl btr) @ qs := evPsomef x btl btr qs (btree_ind btl) (btree_ind btr).

  Obligation 1.
  Proof. destruct btl as [[] []]; destruct btr as [[] []]; simpl; math. Qed.

  Obligation 2.
  Proof. destruct btl as [[] []]; destruct btr as [[] []]; simpl; math. Qed.

End btreeIndPrinciple.

Ltac btree_ind bt x btl btr qs :=
  let IHl := fresh "IHl" in
  let IHr := fresh "IHr" in
  pattern bt;
  eapply btree_ind;
  [ intros qs | intros qs | intros x btl btr qs IHl IHr ].

Tactic Notation "BTree_ind" ident(bt) :=
  let x := fresh "x" in
  let btl := fresh "btl" in
  let btr := fresh "btr" in
  let qs := fresh "qs" in
  btree_ind bt x btl btr qs.
Tactic Notation "BTree_ind" ident(bt) "as" ident(x) ident(btl) ident(btr) ident(qs) := btree_ind bt x btl btr qs.

Fixpoint getItem_default [A] (d: A) (pth: path) (t: tree A): A :=
  match pth with
  | nil =>
      match t with
      | fork v _ _ => v
      | leaf => d
      end
  | dirL :: pth' =>
      match t with
      | fork _ btl _ => Borrowable.get_default d (Borrowable.map (getItem_default d pth') btl)
      | leaf => d
      end
  | dirR :: pth' =>
      match t with
      | fork _ _ btr => Borrowable.get_default d (Borrowable.map (getItem_default d pth') btr)
      | leaf => d
      end
  end.

Fixpoint map [A] (f: A -> A) (t: tree A): tree A :=
  match t with
  | leaf => leaf
  | fork v btl btr => fork (f v) (Borrowable.map (map f) btl) (Borrowable.map (map f) btr)
  end.

Section structForallDef.

  Context [A: Type] (P: btree A -> Prop).
  Implicit Types (x: A) (bt bl br: btree A) (qs: list loc) (t: tree A).

  Inductive structForall: btree A -> Prop :=
  | SFsomef: forall x bl br qs,
      P (available (fork x bl br) @ qs) ->
      structForall bl ->
      structForall br ->
      structForall (available (fork x bl br) @ qs)
  | SFsomel: forall qs,
      P (available leaf @ qs) ->
      structForall (available leaf @ qs)
  | SFnone: forall qs,
      P (unavailable @ qs) ->
      structForall (unavailable @ qs).

  Lemma structForall_some_fork: forall x bl br qs,
    structForall (available (fork x bl br) @ qs) =
    (P (available (fork x bl br) @ qs) /\ structForall bl /\ structForall br).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | intros [H1 [H2 H3]]; constructor; auto]. Qed.

  Lemma structForall_some_leaf: forall qs,
    structForall (available leaf @ qs) = P (available leaf @ qs).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | constructor; auto]. Qed.

  Lemma structForall_none: forall qs,
    structForall (unavailable @ qs) = P (unavailable @ qs).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | constructor; auto]. Qed.

End structForallDef.

#[global] Hint Rewrite structForall_some_fork
                       structForall_some_leaf
                       structForall_none: rew_structForall.

Section structForallProps.

  Context [A: Type].
  Implicit Types (P: btree A -> Prop) (bt: btree A) (qs: list loc) (t: tree A) (ot: option (tree A)).

  Lemma structForall_locIrrelevant: forall P ot qs1 qs2,
    locIrrelevant P ->
    structForall P (mkB ot qs1) ->
    structForall P (mkB ot qs2).
  Proof. introv HP H. unfold locIrrelevant in HP.
    destruct ot;
      inverts H; constructor; auto;
      erewrite <- HP; eauto.
  Qed.

  Lemma structForall_isAvailable_locIrrelevant: forall ot qs1 qs2,
    structForall isAvailable (mkB ot qs1) ->
    structForall isAvailable (mkB ot qs2).
  Proof. intros. eapply structForall_locIrrelevant; eauto. apply isAvailable_locIrrelevant. Qed.

  Lemma structForall_isAvailable_pinb: forall bt q,
    structForall isAvailable bt ->
    structForall isAvailable (pinb bt q).
  Proof.
    introv H.
    destructb bt as t; [destruct t |];
      repeat (simp rew_structForall in *; simpl in *); try easy.
  Qed.

End structForallProps.

#[global] Hint Resolve structForall_isAvailable_locIrrelevant: res_structForall.

Section itemForallDef.

  Context [A: Type] (P: A -> Prop).
  Implicit Types (x: A) (bt bl br: btree A) (qs: list loc) (t: tree A).

  Inductive itemForall: btree A -> Prop :=
  | IFsomef: forall x bl br qs,
      P x -> itemForall bl -> itemForall br ->
      itemForall (available (fork x bl br) @ qs)
  | IFsomel: forall qs,
      itemForall (available leaf @ qs)
  | IFnone: forall qs,
      itemForall (unavailable @ qs).

  Lemma itemForall_some_fork: forall x bl br qs,
    itemForall (available (fork x bl br) @ qs) =
    (P x /\ itemForall bl /\ itemForall br).
  Proof. intros. apply prop_ext. split.
    - intro H. inverts H. auto.
    - intros [H1 [H2 H3]]. apply IFsomef; auto.
  Qed.

  Lemma itemForall_some_leaf: forall qs,
    itemForall (available leaf @ qs) = True.
  Proof. intros. apply prop_ext. split; auto; intros; apply IFsomel. Qed.

  Lemma itemForall_none: forall qs,
    itemForall (unavailable @ qs) = True.
  Proof. intros. apply prop_ext. split; auto; intros; apply IFnone. Qed.

End itemForallDef.

#[global] Hint Rewrite itemForall_some_fork
                       itemForall_some_leaf
                       itemForall_none: rew_itemForall.

Section itemForallProps.

  Context [A: Type].
  Implicit Types (P: A -> Prop) (qs: list loc).

  Lemma itemForall_locIrrelevant: forall P o qs1 qs2,
    itemForall P (mkB o qs1) ->
    itemForall P (mkB o qs2).
  Proof. introv H. destruct o; inverts H; constructor; auto. Qed.

End itemForallProps.

#[global] Hint Resolve itemForall_locIrrelevant: res_itemForall.


Module structForallPlayground.
Section test.
  Context [A: Type] [P: btree A -> Prop].
  Implicit Types (v: A) (bt btl btr: btree A) (qs: list loc).

  Equations structForall (bt: btree A): Prop by wf (sizeb bt) :=
  | available (fork v bl br) @ qs :=
      let bt := available (fork v bl br) @ qs in
      P bt /\ structForall bl /\ structForall br
  | bt := P bt.

  Obligation 1.
  Proof. destruct bl as [[] []]; simpl; math. Qed.

  Obligation 2.
  Proof. destruct br as [[] []]; simpl; math. Qed.

  Equations structForall' (bt: btree A): Prop by wf (sizeb bt) :=
  | bt := P bt /\
      match bt as bt' return bt' = bt -> Prop with
      | available (fork v bl br) @ _ => fun _ => structForall' bl /\ structForall' br
      | _ => fun _ => True
      end eq_refl.

  Obligation 1.
  Proof. destruct bl as [[] []]; simpl; math. Qed.

  Obligation 2.
  Proof. destruct br as [[] []]; simpl; math. Qed.
End test.
End structForallPlayground.

Definition leftRotateb [A] (bt: btree A): btree A :=
  match bt with
  | available (fork x btl (available (fork xr btrl btrr) @ qs__tr)) @ qs =>
      available (fork xr (available (fork x btl btrl) @ qs) btrr) @ qs__tr
  | _ => bt
  end.

Definition leftRotate [A] (t: tree A) (qs: list loc): btree A :=
  match t with
  | fork x btl (available (fork xr btrl btrr) @ qs__tr) =>
      available (fork xr (available (fork x btl btrl) @ qs) btrr) @ qs__tr
  | _ => available t @ qs
  end.

Definition rightRotate [A] (t: tree A) (qs: list loc): btree A :=
  match t with
  | fork x (available (fork xl btll btlr) @ qs__tl) btr =>
      available (fork xl btll (available (fork x btlr btr) @ qs)) @ qs__tl
  | _ => available t @ qs
  end.

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import ListE_API.

Fixpoint find [A] (bt: btree A) (l: zlist): option (btree A) :=
  match l with
  | nil => Some bt
  | cons (available 0 @ _) l1 => match bt with
                 | available (fork _ btl _) @ _ => find btl l1
                 | _ => None
                end
  | cons _ l1 => match bt with
                 | available (fork _ _ btr) @ _ => find btr l1
                 | _ => None
                end
  end.

Lemma find_cons: forall [A] (bt bt1: btree A) (l: zlist) (x: borrowable Z),
  find bt (x :: l) = Some bt1 ->
  exists x btl btr qs, bt = available (fork x btl btr) @ qs.
Proof.
  destruct bt as [[] ];
    intros; simpl in *;
    destruct x as [[v|] qs__v];
    try destruct v; try destruct qs__v; try destruct t; try easy.
  all: exists v bl br qs; reflexivity.
Qed.

Fixpoint subst [A] (bt bt__new: btree A) (l: zlist): btree A :=
  match l with
  | nil => bt
  | cons (available 0 @ _) l1 =>
      match bt with
        | available (fork x btl btr) @ qs => available (fork x (subst btl bt__new l1) btr) @ qs
        | _ => bt
      end
  | cons _ l1 =>
      match bt with
        | available (fork x btl btr) @ qs => available (fork x btl (subst btr bt__new l1)) @ qs
        | _ => bt
      end
  end.

Ltac solve_obligation btl btr :=
  destruct btl as [[] []]; destruct btr as [[] []]; simpl; math.

Section isInDef.
  Context [A] (eqb: A -> A -> bool) (v: A).

  Equations isIn (bt: btree A): bool by wf (sizeb bt) :=
  | available (fork x btl btr) @ qs :=
      if eqb x v
      then true
      else (if isIn btl then true else isIn btr)
  | _ := false.

  Obligation 1. Proof. solve_obligation btl btr. Qed.
  Obligation 2. Proof. solve_obligation btl btr. Qed.
End isInDef.

Section lookupDef.
  Context [A] (eqb: A -> A -> bool) (v: A) (default: btree A).

  Equations lookup (bt: btree A): btree A by wf (sizeb bt) :=
  | available (fork x btl btr) @ qs :=
      if eqb x v
      then available (fork x btl btr) @ qs
      else (if isIn eqb v btl then lookup btl else lookup btr)
  | _ := default.

  Obligation 1. Proof. solve_obligation btl btr. Qed.
  Obligation 2. Proof. solve_obligation btl btr. Qed.
End lookupDef.

Section substkDef.
  Context [A] (eqb: A -> A -> bool) (v: A) (bt1: btree A).

  Equations substk (bt: btree A): btree A by wf (sizeb bt) :=
  | available (fork x btl btr) @ qs :=
      if eqb x v
      then bt1
      else
        if isIn eqb v btl
        then available (fork x (substk btl) btr) @ qs
        else available (fork x btl (substk btr)) @ qs
  | bt := bt.

  Obligation 1. Proof. solve_obligation btl btr. Qed.
  Obligation 2. Proof. solve_obligation btl btr. Qed.
End substkDef.

Section isIn_lookup_substk_props.
  Ltac my_simpl := simpl in *; simp isIn substk lookup rew_structForall in *.

  Context [A] (eqb: A -> A -> bool).

  Notation "bt '⟦' k ':=' bt1 '⟧'" := (substk eqb k bt1 bt)
    (at level 64, right associativity).
  Notation "bt ⟦ k ⟧" := (lookup eqb k (missing) bt)
    (at level 64, right associativity).
  Notation "k '∈?' bt " := (isIn eqb k bt)
    (at level 64, right associativity).

  Lemma isIn_pinb: forall v bt q,
    v ∈? (pinb bt q) = v ∈? bt.
  Proof.
    intros. destructb bt as t; my_simpl; auto. destruct t; my_simpl; auto.
  Qed.

  Lemma isIn_substk_pinb: forall v u bt q,
    v ∈? (bt⟦u := pinb (bt⟦u⟧) q⟧) = v ∈? bt.
  Proof.
    intros v u bt. gen v u.
    BTree_ind bt;
      intros; my_simpl; try easy.
    destruct (eqb x v) eqn: EQxv;
      destruct (eqb x u) eqn: EQxu;
        my_simpl; try rewrite* EQxv;
      destruct (u ∈? btl) eqn: Uinl;
        my_simpl; rewrite* EQxv;
      destruct (v ∈? btl) eqn: Vinl; auto;
        rewrite IHl, Vinl; auto.
  Qed.

  Lemma substk_lookup_same: forall v bt,
    v ∈? bt = true ->
    bt⟦v := bt⟦v⟧⟧ = bt.
  Proof.
    intros v bt. gen v.
    BTree_ind bt;
      introv H; my_simpl; try easy.
    destruct (eqb x v) eqn: EQxv; auto.
    destruct (v ∈? btl) eqn: Vinl; my_simpl; [rewrite* IHl | rewrite* IHr].
  Qed.

  Lemma structForall_isAvailable_substk_pinb: forall v bt q,
    v ∈? bt = true ->
    structForall isAvailable bt ->
    structForall isAvailable (bt⟦v := pinb (bt⟦v⟧) q⟧).
  Proof.
    intros v bt. gen v.
    BTree_ind bt;
      introv H SF; my_simpl.
    destruct (eqb x v) eqn: EQxv; do 2 my_simpl.
    destruct (v ∈? btl) eqn: Vinl; my_simpl;
      destruct SF as [? []]; do 2 split; auto.
  Qed.

  Lemma structForall_isAvailable_lookup: forall v bt,
    v ∈? bt = true ->
    structForall isAvailable bt ->
    structForall isAvailable (bt⟦v⟧).
  Proof.
    intros v bt. gen v.
    BTree_ind bt;
      introv H SF; my_simpl; try easy.
    destruct (eqb x v) eqn: EQxv; do 2 my_simpl.
    destruct (v ∈? btl) eqn: Vinl; my_simpl; [apply* IHl | apply* IHr].
  Qed.

End isIn_lookup_substk_props.
