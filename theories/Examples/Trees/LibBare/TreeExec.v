#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
From LogicalPinning.Examples.Trees.LibBare Require Import Tree.

Fixpoint Forall [A] (p: A -> bool) (t: tree A): bool :=
  match t with
  | leaf => true
  | fork x tl tr => p x && Forall p tl && Forall p tr
  end.

Lemma Forall_eq: forall [A] (p: A -> bool) (P: A -> Prop) (t: tree A),
  isTrue_pred p P ->
  Forall p t = isTrue (Tree.Forall P t).
Proof.
  introv H. induction t as [| x tl IHtl tr IHtr]; simpl.
  - rewrite true_eq_isTrue_eq. constructor.
  - rewrite H, IHtl, IHtr. repeat rewrite <- isTrue_and.
    rewrite isTrue_eq_isTrue_eq. iff M.
    + constructor*.
    + inverts* M.
Qed.
