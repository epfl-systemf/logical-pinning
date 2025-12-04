(**  Heterogeneous Records *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
Require Import WPUntyped Borrowable ValOps.

From Coq Require Import List.
Import ListNotations.

Import NotationForVariables.
Import NotationForTerms.

Ltac auto_star ::= try solve [ intuition eauto with maths ].
Ltac auto_tilde ::= intros; subst; auto_star.

Implicit Types (p q: loc) (k: field).

(* ========================================================================== *)
(** [ReprVal]: A bundle of type, representation predicate and value. *)

#[projections(primitive=yes)]
Record ReprVal := mkReprVal {
    rv_t: Type;
    rv_repr: rv_t -> loc -> hprop;
    rv_val: rv_t
}.
Arguments mkReprVal {rv_t} rv_repr rv_val.

Notation "R '$' v" := (mkReprVal R v)
  (at level 60, no associativity, format "R '$' v"): record_scope.

(* ========================================================================== *)
(* Helpful Notations *)

(* TODO: move it *)
Notation "⟦ n ':=' v ⟧ l" := (LibList.update n v l)
  (at level 64, right associativity).

(* ========================================================================== *)
(** Record operations: get, set, alloc, init, delete
    Similar to the definitions in [WPRecord.v] in cfml. *)

Definition val_get_field (k:field): val :=
  Fun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field): val :=
  Fun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

(** Note: make sure any [k] in [ks] is a valid index. *)
Definition val_record_alloc (ks:fields): val :=
  Fun 'u := val_alloc (1 + fold_right Nat.max 0%nat ks)%nat.

(** Specialized to two fields. TODO: generalize to n fields. *)
Definition val_record_init: val :=
  Fun 'p 'v1 'v2 :=
    (val_set_field 0%nat) 'p 'v1 ';
    (val_set_field 1%nat) 'p 'v2.

Definition val_record_new: val :=
  Fun 'v1 'v2 :=
    Let 'p := (val_record_alloc ([0%nat; 1%nat])) tt in
    val_record_init 'p 'v1 'v2 '; 'p.

(* Print val_record_delete. *)

Definition val_get_field_loc (k:field): val :=
  Fun 'p := val_ptr_add 'p (nat_to_Z k).

(** Notation for record operations. Copied from [WPRecord.v] in CFML. *)

#[warnings="-notation-overridden"]
Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 56, f at level 0, format "t1 ''.' f" ) : trm_scope.

#[warnings="-notation-overridden"]
Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2") : trm_scope.

#[warnings="-notation-overridden -non-reversible-notation"]
Notation "'New' `{ f1 := x1 ; f2 := x2 }" :=
  (val_record_new x1 x2)
  (at level 0, f1 at level 0, f2 at level 0)
  : trm_scope.

(* ========================================================================== *)
(** Record definition *)

Definition Record_field: Type := field * ReprVal.
Definition Record_fields: Type := list Record_field.

Implicit Types (rv: ReprVal) (krvs: Record_fields).

(** ------------------------------------------------------------------------- *)
(** [MField] *)

Definition MField {A} R (v: A) p k: hprop :=
  R v (p+k)%nat \* \[p <> null].

Lemma MField_fold: forall p k A R (v: A),
  p <> null -> R v (p+k)%nat = MField R v p k.
Proof. unfold MField. xsimpl*. Qed.

Lemma MField_not_null: forall A R (v: A) k p,
  MField R v p k ==> MField R v p k \* \[p <> null].
Proof. unfold MField. xsimpl*. Qed.

(** ------------------------------------------------------------------------- *)
(** [MRecord] *)

Fixpoint MRecord (krvs: Record_fields) p: hprop :=
  match krvs with
  | nil => \[]
  | (k, mkReprVal r v) :: krvs1 => MField r v p k \* MRecord krvs1 p
  end.

Lemma MRecord_nil: forall p, MRecord nil p = \[].
Proof. reflexivity. Qed.

Lemma MRecord_cons: forall A R (v: A) p k krvs,
  MRecord ((k, mkReprVal R v) :: krvs) p = MField R v p k \* MRecord krvs p.
Proof. reflexivity. Qed.

Lemma MRecord_not_null: forall krvs p,
  krvs <> nil ->
  MRecord krvs p ==> MRecord krvs p \* \[p <> null].
Proof. destruct krvs as [| [k [t r v]] krvs]; intros; [solve [congruence] |].
  rewrite MRecord_cons. xchanges* MField_not_null.
Qed.

Lemma MRecord_unfold2: forall k1 k2 A R1 (v1: A) B R2 (v2: B) p,
  MRecord ([(k1, R1 $ v1); (k2, R2 $ v2)]) p
  = MField R1 v1 p k1 \* MField R2 v2 p k2.
Proof. simpl. xsimpl*. Qed.

(**  Record operations *)

Fixpoint get k krvs: option ReprVal :=
  match krvs with
  | nil => None
  | (k1, rv1) :: krvs1 => if (k =? k1)%nat then Some rv1 else get k krvs1
  end.

Fixpoint subst k rv krvs: Record_fields :=
  match krvs with
  | nil => nil
  | (k1, rv1) :: krvs1 => if (k =? k1)%nat
                          then (k, rv) :: krvs1
                          else (k1, rv1) :: subst k rv krvs1
  end.

Section substLemmas.

  Context (k: nat) (krvs: Record_fields).

  Lemma subst_cons_same: forall rv2 rv1,
    subst k rv2 ((k, rv1) :: krvs) = (k, rv2) :: krvs.
  Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma subst_cons_neq: forall rv2 k1 rv1,
    (k =? k1)%nat = false ->
    subst k rv2 ((k1, rv1) :: krvs) = (k1, rv1) :: subst k rv2 krvs.
  Proof. introv Hneq. simpl. rewrite Hneq. reflexivity. Qed.

  Ltac ind_krvs :=
    induction krvs as [| [k1 rv1] krvs1 IH]; simpl; [solve [easy] |];
    destruct (k =? k1)%nat eqn: Hk; [apply Nat.eqb_eq in Hk |].

  Lemma subst_overwrite: forall rv2 rv1,
    subst k rv2 (subst k rv1 krvs) = subst k rv2 krvs.
  Proof.
    ind_krvs;
      simpl; intros.
    - rewrite Nat.eqb_refl. reflexivity.
    - rewrite Hk. rewrite IH. reflexivity.
  Qed.

  Lemma subst_same: forall rv,
    get k krvs = Some rv ->
    subst k rv krvs = krvs.
  Proof.
    ind_krvs;
      introv H; inversion H; clear H; intros; subst; simpl.
    - reflexivity.
    - rewrite IH; auto.
  Qed.

End substLemmas.

Lemma get_subst: forall k rv1 rv2 krvs,
  get k krvs = Some rv1 ->
  get k (subst k rv2 krvs) = Some rv2.
Proof.
  induction krvs as [| [k1 rv1'] krvs IH]; simpl; [solve [easy] |].
  destruct (k =? k1)%nat eqn: Hk; [apply Nat.eqb_eq in Hk |].
  all: introv H; inversion H; clear H; intros; subst; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite Hk. eapply IH; auto.
Qed.

Section MRecordTrans.

  Context (k: field) (p: loc) [A: Type].
  Implicit Types (R: A->loc->hprop) (v: A) (x y: ɣb A).

  Ltac ind_krvs krvs H IH :=
    induction krvs as [| [?k1 ?rv1] ?krvs1 IH]; simpl; [solve [easy] |];
    destruct (k =? k1)%nat eqn: Hk; [apply Nat.eqb_eq in Hk |];
    introv H; inversion H; intros; subst; simpl.

  Ltac solve_eq_with krvs lemma :=
    let H := fresh "H" in
    let IH := fresh "IH" in
    ind_krvs krvs H IH;
    [ unfold MField; rewrite lemma
    | apply IH in H; auto; first [rewrite H | xsimpl; rewrite H] ]; xsimpl*.

  Ltac solve_to_with krvs lemma :=
    let H := fresh "H" in
    let IH := fresh "IH" in
    ind_krvs krvs H IH;
    [ unfold MField; xchanges* lemma
    | xchanges* IH ].

  (* ------------------------------------------------------------------------ *)
  (* [ɣB] transitions *)

  Lemma MRecord_Bof_eq_Bb: forall v q qs R krvs,
    get k krvs = Some (ɣB R $ offered v @ q :; qs) ->
    MRecord krvs p = MRecord (subst k (ɣB R $ borrowed @ q :; qs) krvs) p \* R v q.
  Proof. solve_eq_with krvs Bof_eq_Bb. Qed.

  Lemma MRecord_Bb_eq_Bof: forall v q qs R krvs,
    get k krvs = Some (ɣB R $ borrowed @ q :; qs) ->
    MRecord krvs p \* R v q = MRecord (subst k (ɣB R $ offered v @ q :; qs) krvs) p.
  Proof. solve_eq_with krvs Bof_eq_Bb. Qed.

  Lemma MRecord_n_eq_Bo: forall v R krvs,
    get k krvs = Some (R $ v) ->
    MRecord krvs p = MRecord (subst k (ɣB R $ owned v) krvs) p.
  Proof. solve_eq_with krvs Bo_eq_n. Qed.

  Lemma MRecord_Bo_eq_n: forall v R krvs,
    get k krvs = Some (ɣB R $ owned v) ->
    MRecord krvs p = MRecord (subst k (R $ v) krvs) p.
  Proof. solve_eq_with krvs Bo_eq_n. Qed.

  Lemma MRecord_B_forget_fst: forall ov q qs R krvs,
    get k krvs = Some (ɣB R $ pinned ov @ q :; qs) ->
    MRecord krvs p ==> MRecord (subst k (ɣB R $ mkB ov qs) krvs) p.
  Proof. solve_to_with krvs B_forget_fst. Qed.

  Lemma MRecord_B_forget_all: forall ov qs R krvs,
    get k krvs = Some (ɣB R $ mkB ov qs) ->
    MRecord krvs p ==> MRecord (subst k (ɣB R $ mkB ov nil) krvs) p.
  Proof. solve_to_with krvs B_forget_all. Qed.

  (* ------------------------------------------------------------------------ *)
  (* [ɣI] transitions *)

  Lemma MRecord_I_fold: forall q v R krvs,
    get k krvs = Some (MCell $ q) ->
    MRecord krvs p \* R v q ==> MRecord (subst k (ɣI R $ v) krvs) p.
  Proof. solve_to_with krvs I_fold. Qed.

  Lemma MRecord_I_unfold: forall v R krvs,
    get k krvs = Some (ɣI R $ v) ->
    MRecord krvs p = \exists (q: loc), MRecord (subst k (MCell $ q) krvs) p \* R v q.
  Proof.
    intros v R krvs. xpull.
    - solve_to_with krvs I_unfold.
    - intros H q. xchange MRecord_I_fold.
      + erewrite get_subst; auto_star.
      + rewrite subst_overwrite. rewrite subst_same; auto.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [ɣIB] transitions *)

  Lemma MRecord_IBp_eq_cell_and_B: forall ov q qs R krvs,
    get k krvs = Some (ɣIB R $ pinned ov @ q :; qs) ->
    MRecord krvs p = MRecord (subst k (MCell $ q) krvs) p \* ɣB R (mkB ov qs) q.
  Proof. solve_eq_with krvs IBp_eq_cell_and_B. Qed.

  Lemma MRecord_cell_and_B_eq_IBp: forall ov q qs R krvs,
    get k krvs = Some (MCell $ q) ->
    MRecord krvs p \* ɣB R (mkB ov qs) q = MRecord (subst k (ɣIB R $ pinned ov @ q :; qs) krvs) p.
  Proof. solve_eq_with krvs IBp_eq_cell_and_B. Qed.

  Lemma MRecord_IB_forget_fst: forall ov q qs R krvs,
    get k krvs = Some (ɣIB R $ pinned ov @ q :; qs) ->
    MRecord krvs p ==> MRecord (subst k (ɣIB R $ mkB ov qs) krvs) p.
  Proof. solve_to_with krvs IB_forget_fst. Qed.

  Lemma MRecord_IB_forget_all: forall ov qs R krvs,
    get k krvs = Some (ɣIB R $ mkB ov qs) ->
    MRecord krvs p ==> MRecord (subst k (ɣIB R $ mkB ov nil) krvs) p.
  Proof. solve_to_with krvs IB_forget_all. Qed.

  Lemma MRecord_IBof_eq_IBb: forall v q qs R krvs,
    get k krvs = Some (ɣIB R $ offered v @ q :; qs) ->
    MRecord krvs p = MRecord (subst k (ɣIB R $ borrowed @ q :; qs) krvs) p \* R v q.
  Proof. solve_eq_with krvs IBof_eq_IBb. Qed.

  Lemma MRecord_IBb_eq_IBof: forall v q qs R krvs,
    get k krvs = Some (ɣIB R $ borrowed @ q :; qs) ->
    MRecord krvs p \* R v q = MRecord (subst k (ɣIB R $ offered v @ q :; qs) krvs) p.
  Proof. solve_eq_with krvs IBof_eq_IBb. Qed.

  Lemma MRecord_IBo_eq_I: forall v R krvs,
    get k krvs = Some (ɣIB R $ owned v) ->
    MRecord krvs p = MRecord (subst k (ɣI R $ v) krvs) p.
  Proof. solve_eq_with krvs IBo_eq_I. Qed.

End MRecordTrans.

(** ========================================================================= *)
(** Record Operation Specifications *)

Module FieldSpecs.

  Section getField_setField.

  Context (k: field) (p: loc) [A: Type].
  Implicit Types (v: A) (x: ɣb A) (R: A->loc->hprop).

  Ltac solve_with lemma :=
    xwp; mxapp Triple_ptr_add_nat;
    unfold MField; xpull; intros;
    mxapp* lemma; xsimpl*.

  Lemma Triple_get_field_cell: forall `{Enc A} v,
    Triple ((val_get_field k) p)
      (MField MCell v p k)
      (fun (r: A) => \[r = v] \* MField MCell v p k).
  Proof. solve_with Triple_get_cell. Qed.

  Lemma Triple_get_field_IB: forall x R,
    Triple ((val_get_field k) p)
      (MField (ɣIB R) x p k)
      (fun (r: loc) => MField (ɣIB R) (pinb x r) p k).
  Proof. solve_with Triple_get_IB. Qed.

  Lemma Triple_get_field_I: forall v R,
    Triple ((val_get_field k) p)
      (MField (ɣI R) v p k)
      (fun (r: loc) => MField (ɣIB R) (available v @ (r::nil)) p k).
  Proof. solve_with Triple_get_I. Qed.

  Lemma Triple_get_field_B_cell: forall `{Enc A} v qs,
    Triple ((val_get_field k) p)
      (MField (ɣB MCell) (available v @ qs) p k)
      (fun (r: A) => \[r = v] \* MField (ɣB MCell) (available v @ qs) p k).
  Proof. solve_with Triple_get_B_cell. Qed.

  Lemma Triple_set_field_strong_cell: forall `{EA: Enc A} B `{EB: Enc B} (v1: A) (v2: B),
    Triple ((val_set_field k) p ``v2)
      (MField MCell v1 p k)
      (fun (r: unit) => MField MCell v2 p k).
  Proof. solve_with Triple_set_strong_cell. Qed.

  Lemma Triple_set_field_cell: forall `{EA: Enc A} v1 v2,
    Triple ((val_set_field k) p ``v2)
      (MField MCell v1 p k)
      (fun (r: unit) => MField MCell v2 p k).
  Proof. intros. apply Triple_set_field_strong_cell. Qed.

  Lemma Triple_set_field_Bcell: forall `{EA: Enc A} (u v: A) qs,
    Triple ((val_set_field k) p ``u)
      (MField (ɣB MCell) (available v @ qs) p k)
      (fun (r: unit) => MField (ɣB MCell) (available u @ qs) p k).
  Proof. solve_with Triple_set_Bcell. Qed.

  Lemma Triple_set_field_IB: forall R x1 p2,
    Triple ((val_set_field k) p p2)
      (MField (ɣIB R) x1 p k)
      (fun (r: unit) => MField (ɣIB R) (borrowed @ p2 :; nil) p k \* \exists q, ɣB R x1 q).
  Proof. solve_with Triple_set_IB. Qed.

  Lemma Triple_set_field_I: forall R v1 p2,
    Triple ((val_set_field k) p p2)
      (MField (ɣI R) v1 p k)
      (fun (r: unit) => MField (ɣIB R) (borrowed @ p2 :; nil) p k \* \exists q, R v1 q).
  Proof. solve_with Triple_set_I. Qed.

  End getField_setField.

  Section getFieldLoc.

  Context (k: field) (p: loc) [A: Type].
  Implicit Types (v: A) (x: ɣb A) (R: A->loc->hprop).

  Lemma MField_Bo_eq_n: forall v R,
    MField (ɣB R) (owned v) p k = MField R v p k.
  Proof. unfold MField. intros. rewrite Bo_eq_n. xsimpl*. Qed.

  Lemma Triple_get_field_loc_B: forall x R,
    Triple ((val_get_field_loc k) p)
      (MField (ɣB R) x p k)
      (fun (r: loc) => MField (ɣB R) (pinb x r) p k).
  Proof.
    xwp. mxapp Triple_ptr_add_nat. unfold MField; xpull; intros.
    destruct x as [[v|] [|locs]]; simpl; simplb; xsimpl~.
  Qed.

  Lemma Triple_get_field_loc: forall v R,
    Triple ((val_get_field_loc k) p)
      (MField R v p k)
      (fun (r: loc) => MField (ɣB R) (mkB (Some v) (r::nil)) p k).
  Proof. intros. rewrite <- MField_Bo_eq_n. xapplys Triple_get_field_loc_B. Qed.

  End getFieldLoc.

End FieldSpecs.

Section recordOpSpecs.

  Context (k: field) (p: loc) (krvs: Record_fields) [A: Type].
  Implicit Types (v: A) (x: ɣb A) (R: A->loc->hprop).

  Ltac ind_krvs IH :=
    let k1 := fresh "k1" in
    induction krvs as [| [k1 ?rv1] ?krvs1 IH]; simpl; [solve [easy] |];
    destruct (k =? k1)%nat eqn: Hk; [apply Nat.eqb_eq in Hk |];
    introv H; inversion H; intros; subst; simpl.

  Ltac solve_with lemma :=
    let IH := fresh "IH" in
    ind_krvs IH; [xapplys* lemma | xapplys* IH].

  (** ----------------------------------------------------------------------- *)
  (** get field *)

  Lemma Triple_get_field_cell: forall `{EA: Enc A} v,
    get k krvs = Some (MCell $ v) ->
    Triple ((val_get_field k) p)
      (MRecord krvs p)
      (fun (r: A) => \[r = v] \* MRecord krvs p).
  Proof. solve_with FieldSpecs.Triple_get_field_cell. Qed.

  Lemma Triple_get_field_IB: forall R x,
    get k krvs = Some (ɣIB R $ x) ->
    Triple ((val_get_field k) p)
      (MRecord krvs p)
      (fun (r: loc) => MRecord (subst k (ɣIB R $ pinb x r) krvs) p).
  Proof. solve_with FieldSpecs.Triple_get_field_IB. Qed.

  Lemma Triple_get_field_I: forall v R,
    get k krvs = Some (ɣI R $ v) ->
    Triple ((val_get_field k) p)
      (MRecord krvs p)
      (fun (r: loc) => MRecord (subst k (ɣIB R $ available v @ (r::nil)) krvs) p).
  Proof. solve_with FieldSpecs.Triple_get_field_I. Qed.

  Lemma Triple_get_field_B_cell: forall `{EA: Enc A} v qs,
    get k krvs = Some (ɣB MCell $ (available v @ qs)) ->
    Triple ((val_get_field k) p)
      (MRecord krvs p)
      (fun (r: A) => \[r = v] \* MRecord krvs p).
  Proof. solve_with FieldSpecs.Triple_get_field_B_cell. Qed.

  (** ----------------------------------------------------------------------- *)
  (** set field *)

  Lemma Triple_set_field_strong_cell:
    forall `{EA: Enc A} (v1: A) B `{EB: Enc B} (v2: B),
    get k krvs = Some (MCell $ v1) ->
    Triple ((val_set_field k) p ``v2)
      (MRecord krvs p)
      (fun (_: unit) => MRecord (subst k (MCell $ v2) krvs) p).
  Proof. solve_with FieldSpecs.Triple_set_field_strong_cell. Qed.

  Lemma Triple_set_field_cell: forall `{EA: Enc A} (v1 v2: A),
    get k krvs = Some (MCell $ v1) ->
    Triple ((val_set_field k) p ``v2)
      (MRecord krvs p)
      (fun (_: unit) => MRecord (subst k (MCell $ v2) krvs) p).
  Proof. solve_with FieldSpecs.Triple_set_field_cell. Qed.

  Lemma Triple_set_field_Bcell: forall `{EA: Enc A} (u v: A) qs,
    get k krvs = Some (ɣB MCell $ available v @ qs) ->
    Triple ((val_set_field k) p ``u)
      (MRecord krvs p)
      (fun (_: unit) => MRecord (subst k (ɣB MCell $ available u @ qs) krvs) p).
  Proof. solve_with FieldSpecs.Triple_set_field_Bcell. Qed.

  Lemma Triple_set_field_IB: forall R x1 p2,
    get k krvs = Some (ɣIB R $ x1) ->
    Triple ((val_set_field k) p p2)
      (MRecord krvs p)
      (fun (r: unit) =>
        MRecord (subst k (ɣIB R $ borrowed @ p2 :; nil) krvs) p \* \exists q, ɣB R x1 q).
  Proof. solve_with FieldSpecs.Triple_set_field_IB. Qed.

  Lemma Triple_set_field_I: forall R v1 p2,
    get k krvs = Some (ɣI R $ v1) ->
    Triple ((val_set_field k) p p2)
      (MRecord krvs p)
      (fun (r: unit) =>
        MRecord (subst k (ɣIB R $ borrowed @ p2 :; nil) krvs) p \* \exists q, R v1 q).
  Proof. solve_with FieldSpecs.Triple_set_field_I. Qed.

  (** ----------------------------------------------------------------------- *)
  (** get field loc *)

  Lemma Triple_get_field_loc_B: forall R x,
    get k krvs = Some (ɣB R $ x) ->
    Triple ((val_get_field_loc k) p)
      (MRecord krvs p)
      (fun (r: loc) => MRecord (subst k (ɣB R $ pinb x r) krvs) p).
  Proof. solve_with FieldSpecs.Triple_get_field_loc_B. Qed.

  Lemma Triple_get_field_loc: forall v R,
    get k krvs = Some (R $ v) ->
    Triple ((val_get_field_loc k) p)
      (MRecord krvs p)
      (fun (r: loc) => MRecord (subst k (ɣB R $ mkB (Some v) (r::nil)) krvs) p).
  Proof. solve_with FieldSpecs.Triple_get_field_loc. Qed.

End recordOpSpecs.

Lemma Triple_get_field_loc_bare: forall k p,
  Triple ((val_get_field_loc k) p)
    \[]
    (fun (r: loc) => \[r = (p+k)%nat]).
Proof. xwp. mxapp Triple_ptr_add_nat. xsimpl*. Qed.

(** ------------------------------------------------------------------------- *)
(**  alloc *)

Definition completeFields (ks: list field): list field :=
  nat_seq O (1 + fold_right Nat.max O ks)%nat.

Definition uninitRecordFields (ks: list field): Record_fields :=
  LibListExec.map (fun k => (k, (@MCell val Enc_val $ val_uninitialized))) ks.

Lemma eq_MRecord_Alloc: forall (n st: nat) p,
  p <> null ->
  Alloc n (p+st)%nat = MRecord (uninitRecordFields (nat_seq st n)) p.
Proof.
  Transparent nat_seq Alloc.
  induction n; simpl; intros; [solve [easy] | ].
  pose (Heq := IHn (S st) p H).
  unfold MField, MCell. xsimpl.
  - assumption.
  - rewrite plus_n_Sm. xchange Heq.
  - intros _. rewrite plus_n_Sm. xchange <- Heq.
Qed.

Lemma Triple_record_alloc: forall (ks: list field),
  Triple ((val_record_alloc ks) tt)
    \[]
    (fun (r: loc) => MRecord (uninitRecordFields (completeFields ks)) r).
Proof.
  xwp. mxapp Triple_alloc_nat. intros p Hp. unfold completeFields.
  set (n := (1 + fold_right Nat.max 0%nat ks)%nat).
  pose (Heq := @eq_MRecord_Alloc n 0 p Hp). rewrite Nat.add_0_r in Heq.
  rewrite Heq. xsimpl.
Qed.

Ltac auto_tilde ::= auto_tilde_default.
Ltac auto_star ::= auto_star_default.
