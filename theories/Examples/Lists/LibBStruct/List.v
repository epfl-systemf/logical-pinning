(*** Library: Lists with generic elements and borrowable substructures. *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.

#[warnings="-notation-incompatible-prefix"]
From Equations Require Import Equations.

Declare Scope blist_scope.
Open Scope blist_scope.

Inductive List {A} :=
| Nil
| Cons (x: A) (bl: ɣb List).
Arguments List: clear implicits.

Notation "x ';;' bl" := (Cons x bl)
  (at level 60, right associativity).

Notation "'blist' A" := (ɣb List A)
  (at level 64, no associativity).

Definition head [A] (default: A) (l: List A): A :=
  match l with
  | Nil => default
  | Cons x _ => x
  end.

Definition tail [A] (l: List A): blist A :=
  match l with
  | Nil => missing
  | Cons _ btl => btl
  end.

Fixpoint length [A] (l: List A): nat :=
  match l with
  | Nil => O
  | Cons _ bl1 =>
      S (match bl1 with
         | available l1 @ _ => length l1
         | _ => O
         end)
  end.

Definition lengthb [A] (bl: blist A): nat :=
  match bl with
  | available l @ _ => length l
  | _ => O
  end.

Lemma length_Cons: forall [A] (x: A) (bl: blist A),
  length (Cons x bl) = S (lengthb bl).
Proof. destructb bl; simpl; auto. Qed.

Lemma lengthb_Cons: forall [A] (x: A) (bl: blist A) (qs: list loc),
  lengthb (available (Cons x bl) @ qs) = S (lengthb bl).
Proof. destructb bl; simpl; auto. Qed.

Section listIndPrinciple.

  Context A (P: List A -> Prop)
    (evPNil: P Nil)
    (evPCons: forall x bl, pred P bl -> P (Cons x bl)).

  Fixpoint better_list_ind (l: List A): P l :=
    match l with
    | Nil => evPNil
    | Cons x bl => evPCons x bl (prove P better_list_ind bl)
    end.

End listIndPrinciple.

Ltac list_ind l x tl :=
  let btl := fresh "btl" in
  let IH__tl := fresh "IH" tl in
  pattern l;
  eapply better_list_ind;
  [ | intros x btl IH; destruct btl as [[tl |] ] ].

Tactic Notation "List_ind" ident(l) :=
  let x := fresh "x" in
  let tl := fresh "tl" in
  list_ind l x tl.

Tactic Notation "List_ind" ident(l) "as" ident(x) ident(tl) := list_ind l x tl.

Module listIndPrinciplePlayground.

  Section listIndPrinciple.

    Context A (P: List A -> Prop)
      (evPn: P Nil)
      (evPcs: forall x tl qs, P tl -> P (Cons x (available tl @ qs)))
      (evPcn: forall x    qs,         P (Cons x (unavailable  @ qs))).

    Fixpoint better_List_ind (l: List A): P l :=
      match l with
      | Nil => evPn
      | Cons x (available tl @ qs) => evPcs x tl qs (better_List_ind tl)
      | Cons x (unavailable @ qs) => evPcn x qs
      end.

  End listIndPrinciple.

End listIndPrinciplePlayground.

Section blistIndPrinciple.

  Context A (P: blist A -> Prop)
    (evPbm: forall qs, P (unavailable @ qs))
    (evPpoNil: forall qs, P (available Nil @ qs))
    (evPpoCons: forall x btl qs, P btl -> P (available (Cons x btl) @ qs)).

  Equations blist_ind (bl: blist A): P bl by wf (lengthb bl) :=
  | unavailable @ qs := evPbm qs
  | available Nil @ qs := evPpoNil qs
  | available (Cons x btl) @ qs := evPpoCons x btl qs (blist_ind btl).

End blistIndPrinciple.

Ltac blist_ind bl x btl qs :=
  let IH := fresh "IH__" btl in
  pattern bl;
  eapply blist_ind;
  [ intros ?qs | intros ?qs | intros ?x ?btl ?qs ?IH ].

Tactic Notation "BList_ind" ident(bl) :=
  let x := fresh "x" in
  let btl := fresh "btl" in
  let qs := fresh "qs" in
  blist_ind bl x btl qs.

Tactic Notation "BList_ind" ident(bl) "as" ident(x) ident(btl) ident(qs) := blist_ind bl x btl qs.

Fixpoint getItem_default [A] (d: A) (n: nat) (l: List A): A :=
  match n with
  | O => match l with
         | Cons v _ => v
         | Nil => d
         end
  | S n1 => match l with
            | Cons _ btl => Borrowable.get_default d (Borrowable.map (getItem_default d n1) btl)
            | Nil => d
            end
  end.

Fixpoint getItem [A] `{IA: Inhab A} (n: nat) (l: List A): A :=
  match n with
  | O => match l with
         | Cons v _ => v
         | _ => arbitrary
         end
  | S n1 => match l with
            | Cons _ btl => Borrowable.get_default arbitrary (Borrowable.map (getItem n1) btl)
            | Nil => arbitrary
            end
  end.

Fixpoint getTailb {A} (n: nat) (bl: blist A): blist A :=
  match n with
  | O => bl
  | S n1 => match bl with
            | available (Cons _ btl) @ _ => getTailb n1 btl
            | _ => missing (* default value *)
            end
  end.

Fixpoint substItem {A} (n: nat) (vnew: A) (l: List A): List A :=
  match n with
  | O => match l with
        | Nil => Nil
        | v ;; btl => vnew ;; btl
        end
  | S n1 => match l with
            | Nil => l (* default value *)
            | v ;; btl => v ;; (Borrowable.map (substItem n1 vnew) btl)
            end
  end.

Fixpoint substTail {A} (n: nat) (bnew: blist A) (l: List A): List A :=
  match n with
  | O => Borrowable.get_default Nil bnew
  | S n1 => match l with
            | Nil => l (* default value *)
            | x ;; btl => x ;; (Borrowable.map (substTail n1 bnew) btl)
            end
  end.

Lemma substTail_S: forall [A] n bnew x (l: List A) qs,
  substTail (S n) bnew (x ;; available l @ qs) = x ;; available (substTail n bnew l) @ qs.
Proof. destruct n; simpl; intros; auto. Qed.

Fixpoint map {A} (f: A -> A) (l: List A): List A :=
  match l with
  | Nil => Nil
  | Cons v btl => Cons (f v) (Borrowable.map (map f) btl)
  end.

Section structForallDef.

  Context [A: Type] (P: blist A -> Prop).
  Implicit Types (x: A) (qs: list loc) (l: List A).

  Inductive structForall: blist A -> Prop :=
  | SFsomec: forall x btl qs,
      P (available (x ;; btl) @ qs) ->
      structForall btl ->
      structForall (available (x ;; btl) @ qs)
  | SFsomen: forall qs,
      P (available Nil @ qs) ->
      structForall (available Nil @ qs)
  | SFnone: forall qs,
      P (unavailable @ qs) -> structForall (unavailable @ qs).

  Lemma structForall_some_Cons: forall x btl qs,
    structForall (available (Cons x btl) @ qs) =
    (P (available (Cons x btl) @ qs) /\ structForall btl).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | intros [H1 H2]; constructor; auto]. Qed.

  Lemma structForall_some_Nil: forall qs,
    structForall (available Nil @ qs) = P (available Nil @ qs).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | constructor; auto]. Qed.

  Lemma structForall_none: forall qs,
    structForall (unavailable @ qs) = P (unavailable @ qs).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | constructor; auto]. Qed.

End structForallDef.

#[global] Hint Rewrite structForall_some_Cons
                       structForall_some_Nil
                       structForall_none: rew_structForall.

Section structForallProps.

  Context [A: Type].
  Implicit Types (P: blist A -> Prop) (qs: list loc) (l: List A).

  Lemma structForall_locIrrelevant: forall P ol qs1 qs2,
    locIrrelevant P ->
    structForall P (mkB ol qs1) ->
    structForall P (mkB ol qs2).
  Proof. introv HP H. destruct ol; inverts H; constructor; auto.
    all: erewrite <- HP; eauto.
  Qed.

  Lemma structForall_isAvailable_locIrrelevant: forall ol qs1 qs2,
    @structForall A isAvailable (mkB ol qs1) ->
    @structForall A isAvailable (mkB ol qs2).
  Proof. intros. eapply structForall_locIrrelevant; eauto. apply isAvailable_locIrrelevant. Qed.

  Lemma structForall_isAvailable_pinb: forall bl p,
    @structForall A isAvailable bl ->
    @structForall A isAvailable (pinb bl p).
  Proof. intros. destructb bl; simpl.
    all: eapply structForall_isAvailable_locIrrelevant; eauto.
  Qed.

  Lemma structForall_top: forall P bl,
    structForall P bl -> P bl.
  Proof. intros. destructb bl; inverts H; auto. Qed.

  Lemma structForall_getTailb: forall P n bl,
    structForall P bl ->
    n < lengthb bl ->
    P (getTailb n bl).
  Proof.
    induction n;
      introv Hsf Hn; simpl in *.
    - apply structForall_top; auto.
    - destruct bl as [[[] |]]; simpl in *; try solve [math].
      inverts Hsf. apply IHn; auto.
      destruct bl; simpl; math.
  Qed.

End structForallProps.

#[global] Hint Resolve structForall_isAvailable_locIrrelevant
                       structForall_isAvailable_pinb: res_List.

Section itemForallDef.

  Context [A: Type] (P: A -> Prop).
  Implicit Types (x: A) (qs: list loc) (l: List A).

  Inductive itemForall: blist A -> Prop :=
  | IFsomec: forall x btl qs,
      P x ->
      itemForall btl ->
      itemForall (available (Cons x btl) @ qs)
  | IFsomen: forall qs,
      itemForall (available Nil @ qs)
  | IFnone: forall qs,
      itemForall (unavailable @ qs).

  Lemma itemForall_some_Cons: forall x btl qs,
    itemForall (available (x ;; btl) @ qs) = (P x /\ itemForall btl).
  Proof. intros. apply prop_ext.
    split; [intro H; inverts H; auto | intros [H1 H2]; constructor; auto]. Qed.

  Lemma itemForall_some_Nil: forall qs,
    itemForall (available Nil @ qs) = True.
  Proof. intros. apply prop_ext; split; auto; constructor. Qed.

  Lemma itemForall_none: forall qs,
    itemForall (unavailable @ qs) = True.
  Proof. intros. apply prop_ext; split; auto; constructor. Qed.

End itemForallDef.

#[global] Hint Rewrite itemForall_some_Cons
                       itemForall_some_Nil
                       itemForall_none: rew_itemForall.

Section itemForallProps.

  Context [A: Type].
  Implicit Types (P: A -> Prop) (x: A) (qs: list loc).

  Lemma itemForall_locIrrelevant: forall P o qs1 qs2,
    itemForall P (mkB o qs1) ->
    itemForall P (mkB o qs2).
  Proof. introv H. destruct o; inverts H; constructor; auto. Qed.

End itemForallProps.

#[global] Hint Resolve itemForall_locIrrelevant: res_List.

(* Update location if the stored List [l1] is [Nil] *)
Definition blist_map [A] (f: List A -> List A) (qs: list loc) (bl1: blist A): blist A :=
  match bl1 with
  | mkB (Some l1) qs1 =>
      match l1 with
      | Nil => mkB (Some (f l1)) qs
      | _   => mkB (Some (f l1)) qs1
      end
  | _ => bl1 (* default value *)
  end.

Fixpoint append [A] (l2: List A) (qs2: list loc) (l1: List A): List A :=
  match l1 with
  | Nil => l2
  | Cons x btl1 => Cons x (blist_map (append l2 qs2) qs2 btl1)
  end.

Lemma append_length: forall [A] (l1 l2: List A) (qs2: list loc),
  structForall isAvailable (owned l1) ->
  length (append l2 qs2 l1) = (length l2 + length l1)%nat.
Proof.
  intros A l1. List_ind l1;
    intros;
    simp rew_structForall in *; [ easy | | easy ].
  simpl pred in IH. simpl append.
  destruct tl.
  - simpl. math.
  - repeat rewrite length_Cons. unfold lengthb.
    rewrite IH.
    + rewrite length_Cons. math.
    + simp rew_structForall in *. easy.
Qed.

Equations append2b [A] (bl2 bl1: blist A): blist A by wf (lengthb bl1) :=
| bl2, available Nil @ qs := bl2
| bl2, available (Cons x btl1) @ qs := available (Cons x (append2b bl2 btl1)) @ qs
| bl2, unavailable @ qs := bl2.

Notation "bl1 '+++' bl2" := (append2b bl2 bl1)
  (at level 50, left associativity): blist_scope.

(* correctness *)

Lemma append2b_append_Nil: forall {A} (l2: List A) (qs1 qs2: list loc),
  (append2b (available l2 @ qs2) (available Nil @ qs1)) = available (append l2 qs2 Nil) @ qs2.
Proof. intros. simp append2b. reflexivity. Qed.

Lemma append2b_append_Cons: forall {A} (l1 l2: List A) (qs1 qs2: list loc),
  l1 <> Nil ->
  structForall isAvailable (owned l1) ->
  (append2b (available l2 @ qs2) (available l1 @ qs1)) = available (append l2 qs2 l1) @ qs1.
Proof.
  intros A l1.
  List_ind l1;
    introv Hl1 Hsf;
    simp rew_structForall append2b in *; simpl in *;
    [ easy | | easy ].
  destruct tl as [| x1 tl1];
    simp rew_structForall append2b in *; [ reflexivity | ].
  rewrite <- IH; try easy. simp append2b. reflexivity.
Qed.

Lemma append2b_correct: forall {A} (l1 l2: List A) (qs1 qs2: list loc),
  structForall isAvailable (owned l1) ->
  (append2b (available l2 @ qs2) (available l1 @ qs1)) = blist_map (append l2 qs2) qs2 (available l1 @ qs1).
Proof. intros. destruct l1.
  - rewrite append2b_append_Nil. reflexivity.
  - rewrite append2b_append_Cons; easy.
Qed.

(* properties *)

Lemma append2b_length: forall {A} (bl1 bl2: blist A),
  structForall isAvailable bl1 ->
  lengthb (append2b bl2 bl1) = (lengthb bl2 + lengthb bl1)%nat.
Proof.
  intros A bl1.
  BList_ind bl1;
    introv H1;
    simp rew_structForall append2b in *;
    [ easy | easy | ].
  rewrite lengthb_Cons. rewrite* IH__btl.
Qed.

Lemma append2b_assoc: forall [A] (bl1 bl2 bl3: blist A),
  structForall isAvailable bl1 ->
  bl1 +++ bl2 +++ bl3 = bl1 +++ (bl2 +++ bl3).
Proof.
  intros A bl1.
  BList_ind bl1;
    introv SF1;
    simp append2b rew_structForall in *;
    [ reflexivity .. | ].
  rewrite IH__btl; easy.
Qed.
