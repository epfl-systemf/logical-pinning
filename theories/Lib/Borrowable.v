(** Core Definition for Borrowable and Indirectly-Stored Value.
    Includes: - borrowing states;
              - representation predicate transformers;
              - transition lemmas **)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From CFML Require Export WPLib Stdlib.

Declare Scope borrow_scope.
Open Scope borrow_scope.

Ltac auto_tilde ::=
  intros; subst; try solve [ intuition eauto with maths ].

Implicit Types (p q: loc) (op oq: option loc).

(** ========================================================================= *)
(** MCell *)

Section MCellDef.

  Context {A: Type} {EA: Enc A}.
  Implicit Types (v: A).

  Definition MCell v p: hprop :=
    hsingle p (@enc A EA v). (* === hsingle p (enc v) *)

  Lemma MCell_not_null: forall v p,
    MCell v p ==> MCell v p \* \[p <> null].
  Proof. intros. xchange hsingle_not_null. xsimpl; auto. Qed.

End MCellDef.

(** ========================================================================= *)
(** option *)

Definition option_pred {A} (P: A -> Prop) (o: option A): Prop :=
  match o with
  | Some v => P v
  | None => True
  end.

Definition option_prove {A} (P: A -> Prop) (pr: forall A, P A) (o: option A): option_pred P o :=
  match o with
  | Some v => pr v
  | None => I
  end.

Definition option_rel {A B} (P: A -> B -> Prop) (oa: option A) (ob: option B): Prop :=
  match oa, ob with
  | Some a, Some b => P a b
  | None, None => True
  | _, _ => False
  end.

Definition option_hasSome {A} (o: option A): Prop :=
  match o with
  | Some _ => True
  | None => False
  end.

Definition option_has_some {A} (o: option A): bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Definition option_get_default {A} (d: A) (o: option A): A :=
  match o with
  | Some v => v
  | None => d
  end.

Definition option_subst {A} (v: A) (o: option A): option A :=
  match o with
  | Some v1 => Some v
  | None => None
  end.

Definition option_subst' {A} (new old: option A): option A :=
  match new, old with
  | Some v, Some _ => new
  | _, _ => old
  end.

Definition consistent {A} (o: option A) (v: A): Prop :=
  match o with
  | Some v1 => v = v1
  | None => True
  end.

Lemma consistent_none: forall {A} (v: A), consistent None v.
Proof. reflexivity. Qed.

Lemma consistent_some: forall {A} (v: A), consistent (Some v) v.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** borrowable *)

Inductive borrowable {A} :=
| mkB (ov: option A) (qs: list loc).
Arguments borrowable: clear implicits.

Notation "'ɣb' A" := (borrowable A)
  (at level 60, right associativity): borrow_scope.

Notation "'available' v @ qs" := (mkB (Some v) qs)
  (at level 60, no associativity): borrow_scope.
Notation "'unavailable' @ qs" := (mkB None qs)
  (at level 60, no associativity): borrow_scope.
Notation "'pinned' ov @ q :; qs" := (mkB ov (q::qs))
  (at level 60, no associativity): borrow_scope.
Notation "'floating' ov" := (mkB ov nil)
  (at level 60, no associativity): borrow_scope.
Notation "'owned' v" := (mkB (Some v) nil)
  (at level 60, no associativity): borrow_scope.
Notation "'offered' v @  q :; qs " := (mkB (Some v) (q::qs))
  (at level 60, no associativity): borrow_scope.
Notation "'borrowed' @ q :; qs" := (mkB None (q::qs))
  (at level 60, no associativity): borrow_scope.
Notation "'missing'"     := (mkB None nil)
  (at level 60, no associativity): borrow_scope.

(* Destruct to available or unavailable. *)
Ltac destructb x :=
  let v := fresh "v" x in
  destruct x as [[v | ] ].
Ltac destructb_as x v :=
  destruct x as [[v | ] ].
Tactic Notation "destructb" ident(x) := destructb x.
Tactic Notation "destructb" ident(x) "as" ident(v) := destructb_as x v.

#[global]
Instance inhab_ɣb: forall A, Inhab (ɣb A).
Proof. intros. apply (Inhab_of_val (mkB None nil)). Qed.

Section borrowOps.

  Context {A: Type}.
  Implicit Types (v: A) (x: ɣb A).

  Definition map {B} (f: A -> B) (x: ɣb A): ɣb B :=
    match x with
    | mkB ov op => mkB (option_map f ov) op
    end.

  Definition pred (P: A -> Prop) x: Prop :=
    match x with
    | mkB ov _ => option_pred P ov
    end.

  Definition prove (P: A -> Prop) (pr: forall A, P A) x: pred P x :=
    match x with
    | mkB ov _ => option_prove P pr ov
    end.

  Definition rel {B} (P: A -> B -> Prop) (x1: ɣb A) (x2: ɣb B): Prop :=
    match x1, x2 with
    | mkB ov1 _, mkB ov2 _ => option_rel P ov1 ov2
    end.

  Definition pinb x p: ɣb A :=
    match x with
    | mkB ov locs => mkB ov (p::locs)
    end.

  Definition isAvailable x: Prop :=
    match x with
    | mkB ov _ => option_hasSome ov
    end.

  Definition is_available x: bool :=
    match x with
    | mkB ov _ => option_has_some ov
    end.

  Definition get_default (d: A) x: A :=
    match x with
    | mkB ov _ => option_get_default d ov
    end.

  Definition get x: isAvailable x -> A :=
    match x return isAvailable x -> A with
    | mkB (Some v) _ => fun _ => v
    | _ => False_rect A
    end.

  Definition subst v x: ɣb A :=
    match x with
    | mkB ov op => mkB (option_subst v ov) op
    end.

  Definition substb (new old: ɣb A): ɣb A :=
    match new, old with
    | mkB ov__new _, mkB ov__old op => mkB (option_subst' ov__new ov__old) op
    end.

End borrowOps.

Definition locIrrelevant {A} (P: ɣb A -> Prop): Prop :=
  forall (ov: option A) (qs1 qs2: list loc), P (mkB ov qs1) = P (mkB ov qs2).

Section isAvailableProps.

  Context {A: Type}.
  Implicit Types (x: ɣb A).

  Lemma isAvailable_locIrrelevant: locIrrelevant (@isAvailable A).
  Proof. unfold locIrrelevant. reflexivity. Qed.

  Lemma isAvailable_isTrue_pred:
    @isTrue_pred (ɣb A) is_available isAvailable.
  Proof.
    intro x; destructb x; simpl;
      try rewrite isTrue_True; try rewrite isTrue_False;
      reflexivity.
  Qed.

  Lemma isAvailable_available: forall x,
    isAvailable x <-> exists v qs, x = available v @ qs.
  Proof. intros; split; destructb x; eauto; try easy.
    intros [v [qs' H]]; easy. Qed.

  Lemma is_available_correct: forall x,
    is_available x = true <-> isAvailable x.
  Proof. destructb x; simpl; easy. Qed.

  Lemma isAvailable_pinb: forall [A] (x: ɣb A) q,
    isAvailable x -> isAvailable (pinb x q).
  Proof. intros. destructb x; simpl; easy. Qed.

End isAvailableProps.

Section borrowRepr.

  Context {A: Type}.
  Implicit Types (R: A->loc->hprop) (v: A) (x: ɣb A) (locs: list loc).

  Fixpoint eqlocs locs p: Prop :=
    match locs with
    | nil => True
    | loc1::locs1 => (p = loc1) /\ eqlocs locs1 p
    end.
  Lemma eqlocs_nil: forall p, eqlocs nil p = True.
  Proof. easy. Qed.
  Lemma eqlocs_cons: forall p q locs, eqlocs (q::locs) p = (p = q /\ eqlocs locs p).
  Proof. easy. Qed.

  Definition ɣB R x p: hprop :=
    match x with
    | mkB (Some v) locs => R v p \* \[eqlocs locs p]
    | mkB None     locs => \[eqlocs locs p]
    end.

End borrowRepr.

#[global] Hint Rewrite eqlocs_nil eqlocs_cons: rw_borrow.
#[global] Hint Rewrite <- hempty_eq_hpure_true: rw_borrow.
#[global] Hint Rewrite hstar_hempty_l hstar_hempty_r: rw_borrow.

Definition ɣI {A} (R: A->loc->hprop) v p: hprop :=
  \exists (q: loc), MCell q p \* R v q.

Notation "'ɣBI' R" := (ɣB (ɣI R))
  (at level 60, no associativity): borrow_scope.
Notation "'ɣIB' R" := (ɣI (ɣB R))
  (at level 60, no associativity): borrow_scope.
Notation "'ɣBIB' R" := (ɣB (ɣI (ɣB R)))
  (at level 60, no associativity): borrow_scope.

Arguments ɣB: simpl never.
Arguments ɣI: simpl never.

Ltac simplb := unfold ɣB; autorewrite with rw_borrow.

Ltac destruct_and :=
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.

Section B_Trans.

  Context [A: Type].
  Implicit Types (R: A->loc->hprop) (v: A) (x: ɣb A).

  (* ------------------------------------------------------------------------ *)
  (* eq *)

  Lemma Bo_eq_n: forall p v R,
    ɣB R (owned v)  p = R v p.
  Proof. intros; simplb. reflexivity. Qed.

  Lemma Bof_eq_Bb: forall p v q qs R,
    ɣB R (offered v @  q :; qs) p = ɣB R (borrowed @ q :; qs) p \* R v q.
  Proof. intros; simplb. xsimpl*.
    all: intros [-> ?]; auto.
  Qed.

  Lemma Bpinb_eq_Bb: forall p x q R,
    ɣB R (pinb x q) p = ɣB R (borrowed @ q :; nil) p \* ɣB R x q.
  Proof. intros; destruct x as [[] []];
      simpl; simplb;
      xpull; intros; repeat destruct_and; subst;
      xsimpl*.
  Qed.

  (* static calculation *)
  Lemma B_pin: forall p ov qs R,
    ɣB R (mkB ov qs) p = ɣB R (mkB ov (p :: qs)) p.
  Proof. intros. destruct ov; simplb; xsimpl*. Qed.

  (* ------------------------------------------------------------------------ *)
  (* to *)

  (* logical forget *)
  Lemma B_forget_fst: forall p ov q qs R,
    ɣB R (mkB ov (q :: qs)) p ==> ɣB R (mkB ov qs) p.
  Proof. intros. destruct ov; simplb; xsimpl*. Qed.

  Lemma B_forget_all: forall p ov qs R,
    ɣB R (mkB ov qs) p ==> ɣB R (mkB ov nil) p.
  Proof. intros. destruct ov; simplb; xsimpl*. Qed.

  Lemma B_forget_pinb: forall p x q R,
    ɣB R (pinb x q) p ==> ɣB R x p.
  Proof. intros. destruct x as [[] []]; simpl; simplb; xsimpl*. Qed.

  (* ------------------------------------------------------------------------ *)
  (* [pinb] *)

  Lemma B_pinb_extract: forall p q x R,
    ɣB R (pinb x q) p ==> ɣB R (pinb x q) p \* \[p = q].
  Proof. intros. destruct x as [[] []]; simpl; simplb; xsimpl*. Qed.

End B_Trans.

Section I_Trans.

  Context [A: Type].
  Implicit Types (R: A->loc->hprop) (v: A).

  Lemma I_unfold: forall p v R,
    ɣI R v p = \exists (q: loc), MCell q p \* R v q.
  Proof. unfold ɣI. xsimpl. Qed.

  Lemma I_fold: forall p v q R,
    MCell q p \* R v q ==> ɣI R v p.
  Proof. intros. rewrite I_unfold. xsimpl. Qed.

  Lemma I_eq_IBo: forall p v R,
    ɣI R v p = (ɣIB R) (owned v) p.
  Proof.
    unfold ɣI. xpull; intros; xsimpl.
    - xchange <- Bo_eq_n.
    - xchange Bo_eq_n.
  Qed.

End I_Trans.

Section IB_Trans.

  Context [A: Type].
  Implicit Types (R: A->loc->hprop) (v: A) (x: ɣb A).

  (* ------------------------------------------------------------------------ *)
  (* IB specific *)

  Lemma IBp_eq_cell_and_B: forall p ov q qs R,
    (ɣIB R) (mkB ov (q :: qs)) p = MCell q p \* ɣB R (mkB ov qs) q.
  Proof. intros. unfold ɣI, ɣB; xpull.
    - destruct ov as [v|]; simpl; xpull; intros x [-> H]; xsimpl*.
    - destruct ov as [v|]; simpl; xsimpl*.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* inherited from [ɣB] *)

  Ltac solve_eq_with lemma :=
    intros; unfold ɣI; xpull; intros; [ xchanges lemma | xchanges <- lemma ].

  Ltac solve_to_with lemma :=
    intros; unfold ɣI; xpull; intros; xchanges* lemma.

  Lemma IB_forget_fst: forall p ov q qs R,
    (ɣIB R) (pinned ov @  q :; qs ) p ==> (ɣIB R) (mkB ov qs) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma IB_forget_all: forall p ov qs R,
    (ɣIB R) (mkB ov qs) p ==> (ɣIB R) (mkB ov nil) p.
  Proof. solve_to_with B_forget_all. Qed.

  Lemma IBof_eq_IBb: forall p v q qs R,
    (ɣIB R) (offered v @ q :; qs) p = (ɣIB R) (borrowed @ q :; qs) p \* R v q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma IBo_eq_I: forall p v R,
    (ɣIB R) (owned v) p = ɣI R v p.
  Proof. solve_eq_with Bo_eq_n. Qed.

End IB_Trans.

Ltac auto_tilde ::= auto_tilde_default.
