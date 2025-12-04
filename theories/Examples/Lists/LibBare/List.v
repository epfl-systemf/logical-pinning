(*** Library: Lists with generic elements (non-borrowable or borrowable). *)

(* This file extends TLC's [LibList]. *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Borrowable Stdlib.

Notation "⟦ n ':=' v ⟧ l" := (LibList.update n v l)
  (at level 64, right associativity).

Hint Rewrite length_update update_zero update_succ nth_zero nth_succ LibList.length_map: rew_list.

Lemma update_overwrite: forall [A: Type] [l: list A] (n: nat) (v1 v2: A),
  ⟦n := v2⟧ ⟦n := v1⟧ l = ⟦n := v2⟧ l.
Proof.
  induction l; destruct n; intros; rew_list in *; try easy.
  rewrite IHl; auto.
Qed.

Hint Rewrite update_overwrite: rew_list.

Lemma update_comm: forall [A: Type] [l: list A] (n1 n2: nat) (v1 v2: A),
  n1 <> n2 -> n1 < LibList.length l -> n2 < LibList.length l ->
  ⟦n2 := v2⟧ ⟦n1 := v1⟧ l = ⟦n1 := v1⟧ ⟦n2 := v2⟧ l.
Proof.
  induction l; destruct n1, n2; intros; rew_list in *; try easy.
  rewrite IHl; auto; math.
Qed.

Hint Rewrite nth_update_neq using (solve [first [assumption | symmetry; assumption]]): rew_list.
Hint Rewrite nth_update_same using (solve [rew_list; auto]): rew_list.
Hint Rewrite update_nth_same using (solve [rew_list; auto]): rew_list.
Hint Rewrite update_overwrite using (solve [rew_list; auto]): rew_list.

Lemma nth_update_map: forall [A B] `{Inhab B} n (v: B) (f: A->B) (l: list A),
  n < LibList.length l ->
  LibList.nth n (⟦n := v⟧ (LibList.map f l)) = v.
Proof. intros. rewrite nth_update_same; auto. rewrite LibList.length_map; auto. Qed.
Hint Rewrite nth_update_map: rew_list.
