(*** Library: Trees with generic elements (non-borrowable or borrowable). *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.

Inductive tree {A} :=
| leaf
| fork (x: A) (tl: tree) (tr: tree).
Arguments tree: clear implicits.

Inductive direction := dirL | dirR.

Notation "'path'" := (list direction)
  (at level 64, no associativity).

Fixpoint size [A] (t: tree A): nat :=
  match t with
  | leaf => O
  | fork _ tl tr => 1%nat + size tl + size tr
  end.

Inductive Forall [A] (P: A -> Prop): tree A -> Prop :=
| Fleaf: Forall P leaf
| Ffork: forall (x: A) (tl tr: tree A),
    P x -> Forall P tl -> Forall P tr -> Forall P (fork x tl tr).
Hint Constructors Forall: core.

Section ForallRewrite.

  Context [A: Type] [P: A -> Prop].
  Implicit Types (x: A) (t tl tr: tree A).

  Lemma Forall_leaf: Forall P leaf = True.
  Proof. auto. Qed.

  Lemma Forall_fork: forall x tl tr,
    Forall P (fork x tl tr) = (P x /\ Forall P tl /\ Forall P tr).
  Proof. intros. eapply prop_ext. iff M.
    - inverts* M.
    - constructors*.
  Qed.

End ForallRewrite.

#[global] Hint Rewrite Forall_leaf Forall_fork: rew_Forall.

Fixpoint map [A] (f: A -> A) (t: tree A): tree A :=
  match t with
  | leaf => leaf
  | fork x tl tr => fork (f x) (map f tl) (map f tr)
  end.

Section mapLemmas.

  Context [A: Type] (f: A -> A).

  Lemma map_fork: forall x tl tr,
    map f (fork x tl tr) = fork (f x) (map f tl) (map f tr).
  Proof. reflexivity. Qed.

End mapLemmas.

Fixpoint subst [A] (pth: path) (new: tree A) (t: tree A): tree A :=
  match pth with
  | nil => new
  | dirL :: pth' => match t with
                     | fork x tl tr => fork x (subst pth' new tl) tr
                     | _ => t (* default value *)
                     end
  | dirR :: pth' => match t with
                     | fork x tl tr => fork x tl (subst pth' new tr)
                     | _ => t (* default value *)
                     end
  end.

Definition leftRotate [A] (t: tree A): tree A :=
  match t with
  | leaf => leaf
  | fork x tl tr =>
      match tr with
      | leaf => t (* default value *)
      | fork xr trl trr => fork xr (fork x tl trl) trr
      end
  end.

Definition rightRotate [A] (t: tree A): tree A :=
  match t with
  | leaf => leaf
  | fork x tl tr =>
      match tl with
      | leaf => t (* default value *)
      | fork xl tll tlr => fork xl tll (fork x tlr tr)
      end
  end.
