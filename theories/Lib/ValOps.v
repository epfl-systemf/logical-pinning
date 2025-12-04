(** Single-Cell Operations **)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
Require Import WPUntyped Borrowable.

Ltac auto_star ::= try solve [ intuition eauto with maths ].
Ltac auto_tilde ::= intros; subst; auto_star.

Implicit Types (p q: loc) (n: nat) (z: Z).
Transparent repr.

(** ------------------------------------------------------------------------- *)
(** [val_get] *)

Lemma Triple_get_cell: forall A `{Enc A} v p,
  Triple (val_get p)
    (MCell v p)
    (fun (r: A) => \[r = v] \* MCell v p).
Proof. intros. xapplys* Triple_get. Qed.

Lemma Triple_get_B_cell: forall A `{Enc A} v qs p,
  Triple (val_get p)
    (ɣB MCell (available v @ qs) p)
    (fun (r: A) => \[r = v] \* ɣB MCell (available v @ qs) p).
Proof.
  intros. simplb. rewrite hstars_pick_last_2. apply Triple_hpure; intros.
  xapplys* Triple_get_cell.
Qed.

Lemma Triple_get_IB: forall A R (x: ɣb A) p,
  Triple (val_get p)
    ((ɣIB R) x p)
    (fun (r: loc) => (ɣIB R) (pinb x r) p).
Proof.
  intros. destruct x as [[v|] [|locs]];
    unfold ɣI; simpl; apply~ Triple_hexists; (* handle ɣI *)
    simplb. (* handle ɣB *)
  - xapplys~ Triple_get_cell. simpl; auto.
  - rewrite hstars_pick_last_3. apply Triple_hpure; intros [-> ?].
    xapplys~ Triple_get_cell. simpl; auto.
  - xapplys~ Triple_get_cell. simpl; auto.
  - rewrite hstars_pick_last_2. apply Triple_hpure; intros [-> ?].
    xapplys~ Triple_get_cell. simpl; auto.
Qed.

Lemma Triple_get_I: forall A R (v: A) p,
  Triple (val_get p)
    (ɣI R v p)
    (fun (r: loc) => (ɣIB R) (available v @ (r::nil)) p).
Proof.  intros. rewrite I_eq_IBo. xapplys Triple_get_IB. Qed.

(** ------------------------------------------------------------------------- *)
(** [val_set] *)

Lemma Triple_set_strong_cell: forall A `{EA: Enc A} B `{EB: Enc B} (v1: A) (v2: B) p,
  Triple (val_set p ``v2)
    (MCell v1 p)
    (fun (r: unit) => MCell v2 p).
Proof. intros. xapplys Triple_set_strong. Qed.

Lemma Triple_set_cell: forall A `{Enc A} (v1 v2: A) p,
  Triple (val_set p ``v2)
    (MCell v1 p)
    (fun (r: unit) => MCell v2 p).
Proof. intros. xapplys Triple_set_strong_cell. Qed.

Lemma Triple_set_Bcell: forall A `{Enc A} (u v: A) qs p,
  Triple (val_set p ``u)
    (ɣB MCell (available v @ qs) p)
    (fun (r: unit) => ɣB MCell (available u @ qs) p).
Proof.
  intros. simplb. rewrite hstar_comm. apply Triple_hpure; intros.
  xapplys* Triple_set_cell.
Qed.

Lemma Triple_set_IB: forall A (R: A->loc->hprop) (x1: ɣb A) p1 p2,
  Triple (val_set p1 ``p2)
    ((ɣIB R) x1 p1)
    (fun (r: unit) => (ɣIB R) (borrowed @ p2 :; nil) p1 \* \exists q, ɣB R x1 q).
Proof.
  intros. unfold ɣI. rewrite hstar_hexists. apply Triple_hexists; intros q.
  xapplys Triple_set_strong_cell. unfold ɣB; simpl; xsimpl*.
Qed.

Lemma Triple_set_I: forall A (R: A->loc->hprop) v1 p1 p2,
  Triple (val_set p1 ``p2)
    (ɣI R v1 p1)
    (fun (r: unit) => (ɣIB R) (borrowed @ p2 :; nil) p1 \* \exists q, R v1 q).
Proof. intros. rewrite I_eq_IBo. xapplys Triple_set_IB. xchanges Bo_eq_n. Qed.

(** ------------------------------------------------------------------------- *)
(** [val_ref] *)

Lemma Triple_ref_cell: forall A `{Enc A} (v: A),
  Triple (val_ref ``v)
    \[]
    (fun (r: loc) => MCell v r).
Proof. intros. xapplys Triple_ref. Qed.

(** ------------------------------------------------------------------------- *)
(** [val_alloc] *)

Section AllocPreparation.

  (* TODO: clean up this proof *)
  Lemma Alloc_fmap_conseq : forall l k,
    l <> null ->
    (Alloc k l) ((Fmap.conseq (LibList.make k val_uninitialized) l), 0).
  Proof using.
    Transparent loc null.
    introv N. gen l. induction k; intros; rew_Alloc.
    { rewrite LibList.make_zero, Fmap.conseq_nil. applys~ hempty_intro. }
    { rewrite LibList.make_succ, Fmap.conseq_cons.
      set (s2 := Fmap.conseq (make k val_uninitialized) (S l)).
      set (s1 := Fmap.single l val_uninitialized).
      change (Fmap.union (Fmap.single l val_uninitialized) s2) with (Fmap.union s1 s2).
      set (h2 := (s2, 0)). set (h1 := (s1, 0)).
      change (Fmap.union s1 s2, 0) with (h1 \u h2).
      applys hstar_intro.
      { split~. }
      { applys IHk. unfolds loc, null. math. }
      { applys~ Fmap.disjoint_single_conseq. } }
  Qed.

  Lemma hoare_alloc : forall (H: hprop) (n: Z),
    n >= 0 ->
    hoare (val_alloc n)
      H
      (fun r => (\exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l) \* H).
  Proof using. (* Note: [abs n] currently does not compute in Coq. *)
    introv N. intros h Hh.
    destruct h.
    forwards~ (l&Dl&Nl): (@Fmap.conseq_fresh _ null s (LibList.make (abs n) val_uninitialized)).
    match type of Dl with Fmap.disjoint ?hc _ => sets s1': hc end.
    exists ((s1', 0) \u (s, z)) (val_loc l). splits~.
    { applys~ (eval_alloc (abs n)).
      unfold Semantics.Fmap.disjoint. unfold Semantics.Fmap.map_disjoint.
      unfold Fmap.disjoint in Dl. unfold Fmap.map_disjoint in Dl.
      unfold Fmap.fmap_data in Dl. unfold Semantics.Fmap.fmap_data.
      intros x. destruct (Dl x); auto. }
    { apply~ hstar_intro.
      { exists l. applys~ himpl_hstar_hpure_r. applys~ Alloc_fmap_conseq. } }
  Qed.

  Lemma triple_alloc : forall (n: Z),
    n >= 0 ->
    triple (val_alloc n)
      \[]
      (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
  Proof using.
    intros. applys triple_of_hoare. intros HF.
    esplit; split. { applys* hoare_alloc. } { xsimpl*. }
  Qed.

  Transparent Triple Post.
  Lemma Triple_alloc : forall (n: Z),
    n >= 0 ->
    Triple (val_alloc n)
      \[]
      (fun l => \[l <> null] \* Alloc (abs n) l).
  Proof using.
    introv N. unfold Triple, Post. xapplys* triple_alloc.
  Qed.

  Lemma Triple_alloc_nat : forall (n: nat),
    Triple (val_alloc (n: int))
      \[]
      (fun l => \[l <> null] \* Alloc n l).
  Proof using.
    intros. xapplys* Triple_alloc. rewrite abs_nat. xsimpl.
  Qed.

End AllocPreparation.

(** ------------------------------------------------------------------------- *)
(** [val_free] *)

Lemma Triple_free_cell: forall A `{EA: Enc A} (v: A) (p: loc),
  Triple (val_free p)
    (MCell v p)
    (fun (r: unit) => \[]).
Proof. intros. xapplys Triple_free. Qed.

Ltac auto_star ::= auto_star_default.
Ltac auto_tilde ::= auto_tilde_default.
