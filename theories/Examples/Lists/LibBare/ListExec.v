(** Buffer for more executable operations for lists.
    Extends TLC's [LibListExec]. *)

Set Implicit Arguments.
Generalizable Variables A B.
#[warnings="-notation-incompatible-prefix"]
From TLC Require Import LibTactics LibReflect.
From TLC Require Export LibList LibListExec.

(* ---------------------------------------------------------------------- *)
(* ** Autorewrite *)
(* Copied from [LibListExec.v] in TLC. *)

Module Import RewListExec.

Tactic Notation "rew_list_exec" :=
  autorewrite with rew_list_exec.
Tactic Notation "rew_list_exec" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_list_exec).
  (* autorewrite with rew_list_exec in *. *)
Tactic Notation "rew_list_exec" "in" hyp(H) :=
  autorewrite with rew_list_exec in H.

End RewListExec.

(* ---------------------------------------------------------------------- *)
(* ** [nth] *)

Fixpoint nth A `{IA: Inhab A} (n:nat) (l:list A) {struct l} : A :=
  match l with
  | nil => arbitrary
  | x::l' =>
     match n with
     | 0 => x
     | S n' => nth n' l'
     end
  end.

Lemma nth_eq: forall A `{IA: Inhab A} (n: nat) (l: list A),
  nth n l = LibList.nth n l.
Proof.
  Transparent LibList.nth LibList.nth_default.
  intros. gen n. induction l as [| x l]; simpl; intros.
  - unfold LibList.nth. unfold nth_default. reflexivity.
  - destruct n.
    + rewrite nth_zero. reflexivity.
    + rewrite nth_succ. apply IHl.
Qed.

#[global] Hint Rewrite nth_eq : rew_list_exec.
