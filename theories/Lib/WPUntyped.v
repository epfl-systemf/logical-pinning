(** This file contains lemmas and tactics for reasoning about programs written
    in the untyped imperative lambda calculus with the lifted characteristic
    formulas [Wpgen]. *)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From CFML Require Export WPLib Stdlib.
Set Implicit Arguments.

Declare Scope Wp_untyped_scope.
Open Scope Wp_untyped_scope.

(* ========================================================================== *)
(**  [Wpgen_let] *)

(** [xlet_lemma] is copied from [WPRecord.v] in CFML.
    For goal [PRE H CODE (Let x := F1 in F2) POST Q], produces two goals:
    1. [PRE H CODE F1 POST ?Q1]
    2. [forall x, PRE (?Q1 x) CODE F2 POST Q] *)
Lemma xlet_lemma : forall A1 (EA1:Enc A1) (Q1:A1->hprop) H A (EA:Enc A) (Q:A->hprop) ,
  forall (F1:Formula) (F2of:forall A1 (EA1:Enc A1), A1->Formula),
  Structural F1 ->
  H ==> F1 A1 EA1 Q1 ->
  (forall (X:A1), Q1 X ==> ^(@F2of A1 EA1 X) Q) ->
  H ==> ^(@Wpgen_let F1 F2of) Q.
Proof using.
  introv HF1 M1 M2. applys MkStruct_erase. applys himpl_hexists_r A1.
  applys himpl_hexists_r EA1. xchange M1. applys* Structural_conseq.
Qed.

(** For goal [PRE H CODE (Let x := F1 in F2) POST Q], produces one goal:
    [PRE H CODE F1 POST (fun x => F2 Q)] *)
Lemma xlet_cont_lemma : forall A1 (EA1:Enc A1) H A (EA:Enc A) (Q:A->hprop),
  forall (F1:Formula) (F2of: forall B (EB: Enc B), B->Formula),
  H ==> ^F1 (fun (X:A1) => (@F2of A1 EA1 X) A EA Q) ->
  H ==> ^(@Wpgen_let F1 F2of) Q.
Proof. introv M. xchange M; clear M. applys MkStruct_erase. xsimpl. Qed.

(* -------------------------------------------------------------------------- *)
(** [mxlet] for [Wpgen_let]

    For goal [PRE H CODE (Let x := F1 in F2) POST Q],

    [mxlet]: produces two goals, [PRE H CODE F1 POST ?Q1] and
    [PRE (?Q1 x) CODE F2 POST Q] (x is an auto-generated name).

    [mxlet as]: produces two goals, [PRE H CODE F1 POST ?Q1] and
    [forall x, PRE (?Q1 x) CODE F2 POST Q].

    [mxlet Q1]: produces two goals, [PRE H CODE F1 POST Q1] and
    [PRE (Q1 x) CODE F2 POST Q] (x is an auto-generated name).

    [mxlet Q1 as]: produces two goals, [PRE H CODE F1 POST Q1] and
    [forall x, PRE (Q1 x) CODE F2 POST Q].

    [mxlet_cont]: produces one goal, [PRE H CODE F1 POST (fun x => F2 Q)] *)

Ltac mxlet_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let _ _) => idtac
  end.

Ltac mxlet_common lemma cont :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let ?F1 (fun A E x => ?F2of)) =>
      let a := fresh x in
      eapply lemma; [try solve [xstructural] | ..]; [ | intros a; cont a]
  end.

(* [mxlet] *)

Ltac mxlet_core cont :=
  mxlet_pre tt;
  mxlet_common (@xlet_lemma) cont.

Tactic Notation "mxlet" :=
  mxlet_core ltac:(fun a => idtac).

Tactic Notation "mxlet" "as" :=
  mxlet_core ltac:(fun a => revert a).

(* [mxlet Q1] *)

Ltac mxlet_st_common Q1 cont :=
  mxlet_pre tt;
  mxlet_common (@xlet_lemma _ _ Q1) cont.

Tactic Notation "mxlet" constr(Q1) :=
  mxlet_st_common Q1 ltac:(fun a => idtac).

Tactic Notation "mxlet" constr(Q1) "as" :=
  mxlet_st_common Q1 ltac:(fun a => revert a).

(* [mxlet_cont] *)

Ltac mxlet_cont_core tt :=
  mxlet_pre tt;
  eapply xlet_cont_lemma.

Tactic Notation "mxlet_cont" :=
  mxlet_cont_core tt.

(* ========================================================================== *)
(** [Wpgen_app_untyped] *)

Notation "'UntypedApp'' f" :=
 ((*Wptag*) (Wpgen_app_untyped f))
  (in custom cf at level 68, f constr at level 0): Wp_untyped_scope.

(* xlemma. Copied from [WPRecord.v] in cfml. *)
Lemma xapp_untyped_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_app_untyped t) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp. applys* Triple_ramified_frame.
Qed.

(* variant that supports [(hand H1 H2)] precondition *)
Lemma xapp_untyped_lemma_hand: forall A `{EA:Enc A} (Q1:A->hprop) (t:trm) H1 H2 H Q,
  Triple t (hand H1 H2) Q1 ->
  H ==> H1 ->
  H ==> H2 ->
  \[] ==> (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_app_untyped t) Q.
Proof. introv Mt M1 M2 MQ.
  eapply xapp_untyped_lemma; [exact Mt |].
  pose (M12 := himpl_hand_r M1 M2).
  rewrite <- hstar_hempty_r at 1.
  apply himpl_frame_lr; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(**  [mxapp] for [Wpgen_app_untyped] *)

Ltac mxlet_xseq_cont_step tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlet_trm_cont
  | (Wpgen_let _ _) => mxlet_cont
  | (Wpgen_seq _ _) => xseq_cont
  end.

Ltac mxlet_xseq_cont_steps tt :=
  xcheck_pull tt;
  repeat (mxlet_xseq_cont_step tt).

Ltac mxapp_pre_wp tt :=
  mxlet_xseq_cont_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app_untyped _) => idtac
  (* | (Wpgen_record_new ?Lof) => idtac --- added in WPRecord *)
  end.

Ltac mxapp_pre tt :=
  xcheck_pull tt;
  first [ mxapp_pre_wp tt | xapp_pre_triple tt ].

Tactic Notation "mxapp_nosubst" constr(E) :=
  mxapp_pre tt;
  forwards_nounfold_then E ltac:(fun K => applys xapp_untyped_lemma K; xapp_simpl tt).

(** [xapp_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "mxapp_try_subst" :=
  try match goal with
  | |- forall r, (r = _) -> _ => intros ? ->
  | |- forall r, forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.

Tactic Notation "mxapp_apply_spec" :=
  first [ solve [ eauto with triple ]
        | match goal with H: _ |- _ => eapply H end ].

Tactic Notation "mxapp_nosubst" :=
  mxapp_pre tt;
  applys xapp_untyped_lemma; [ mxapp_apply_spec | xapp_simpl tt ].

Tactic Notation "mxapp" constr(E) :=
  mxapp_nosubst E; mxapp_try_subst.
Tactic Notation "mxapp" "~" constr(E) :=
  mxapp E; auto_tilde.
Tactic Notation "mxapp" "*" constr(E)  :=
  mxapp E; auto_star.

Tactic Notation "mxapp" :=
  mxapp_nosubst; mxapp_try_subst.

Tactic Notation "mxapp" "~" :=
  mxapp; auto_tilde.
Tactic Notation "mxapp" "*"  :=
  mxapp; auto_star.

(* #[global] Hint Resolve Triple_set: triple. *)
(* Print HintDb triple. *)

(* ========================================================================== *)
(**  [Wpgen_let_trm_cont]: originally used in the internal CF generator, now
     replaced by [Wpgen_let_trm]. *)

(* Print Wpgen_let_trm. *)
(* Print Wpgen_let_trm_cont. *)
(* Check xlet_trm_cont_lemma. *)

(* Lemma xlet_trm_cont_lemma': forall A1 (EA1:Enc A1) H A (EA:Enc A) (Q:A->hprop), *)
(*   forall (F1:Formula) (F2of:A1->Formula), *)
(*   H ==> ^F1 (fun (X:A1) => (F2of X) A EA Q) -> *)
(*   H ==> ^(@Wpgen_let_trm_cont F1 A1 EA1 (@F2of)) Q. *)
(* Proof using. introv M. xchange M. applys MkStruct_erase. xsimpl. Qed. *)

(* ========================================================================== *)
(**  [Wpgen_seq_cont]
  *
  *  Originally used in the internal CF generator, now replaced by [Wpgen_seq].
  *)

(* Print Wpgen_seq. *)
(* Print Wpgen_seq_cont. *)
(* Check xseq_lemma. *)
(* Check xseq_cont_lemma. *)

(* Lemma seqcont_xseq_cont_lemma : forall H A (EA:Enc A) (Q:A->hprop), *)
(*   forall (F1 F2:Formula), *)
(*   H ==> ^F1 (fun (_:unit) => ^F2 Q) -> *)
(*   H ==> ^(@Wpgen_seq_cont F1 F2) Q. *)
(* Proof. introv M. eapply MkStruct_erase. xchange M. Qed. *)

(* ========================================================================== *)
(**  [Wpgen_val_unlifted] *)

Lemma xval_unlifted_lemma: forall A `{EA:Enc A} (V:A) H (Q:A->hprop),
  H ==> Q V ->
  H ==> ^(Wpgen_val_unlifted ``V) Q.
Proof using.
  introv M. xchange M. applys MkStruct_erase.
  unfold Post. xsimpl~.
Qed.

Lemma xval_unlifted_lemma_inst : forall A `{EA:Enc A} (V:A) H,
  H ==> ^(Wpgen_val_unlifted ``V) (fun x => \[x = V] \* H).
Proof using. intros. apply xval_unlifted_lemma. xsimpl*. Qed.

Ltac mxval_pre tt :=
  xcheck_pull tt;
  xlet_xseq_cont_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
  | (Wpgen_val_unlifted _) => idtac
  end.

Ltac mxval_post tt :=
  xcleanup.

Ltac mxval_core tt :=
  mxval_pre tt;
  first [ eapply xval_unlifted_lemma_inst
        | eapply xval_unlifted_lemma
        | eapply xval_lemma_inst
        | eapply xval_lemma ];
  mxval_post tt.

Tactic Notation "mxval" :=
  mxval_core tt.
Tactic Notation "mxval" "~" :=
  mxval; auto_tilde.
Tactic Notation "mxval" "*"  :=
  mxval; auto_star.

(** [xvals] *)

Ltac mxvals_core tt :=
  mxval; xsimpl.

Tactic Notation "mxvals" :=
  mxvals_core tt.
Tactic Notation "mxvals" "~" :=
  mxvals; auto_tilde.
Tactic Notation "mxvals" "*"  :=
  mxvals; auto_star.

(* ========================================================================== *)
(** Demo programs *)

Import NotationForVariables.
Import NotationForTerms.

Definition val_incr : val :=
Fun 'p :=
  Let 'n := '! 'p in
  Let 'm := 'n '+ 1 in
  'p ':= 'm.

Lemma spec_incr_using_xlemmas: forall (p: loc) (n: Z),
  SPEC (val_incr p)
  PRE (p ~> Hsingle n)
  POSTUNIT (p ~> Hsingle (n + 1)).
Proof.
  intros.
  (* xwp *)
  eapply xwp_lemma_funs; try reflexivity; simpl.
  rewrite dyn_to_val_dyn_make.
  (* xlet *)
  eapply (@xlet_lemma _ _ (fun r => \[r = n] \* p ~> Hsingle n)); [xstructural | ..].
  - (* xapp *)
    eapply xapp_untyped_lemma.
    eapply Triple_get.
    xapp_simpl tt.
    intros; xsimpl; auto.
  - intros ?; xpull; intros; subst.
    (* xlet *)
    eapply (@xlet_lemma _ _ (fun r => \[r = n + 1] \* p ~> Hsingle n)); [xstructural | ..].
    + (* xapp *)
      eapply xapp_untyped_lemma.
      eapply Triple_add.
      xapp_simpl tt.
      intros; xsimpl; auto.
    + intros ?; xpull; intros; subst.
      (* xapp *)
      eapply xapp_untyped_lemma.
      eapply Triple_set.
      xapp_simpl tt.
      xsimpl.
Qed.

Ltac auto_tilde ::= intros; subst; try solve [ intuition eauto with maths ].

Lemma spec_incr_lifted_using_xtactics: forall (p: loc) (n: Z),
  SPEC (val_incr p)
  PRE (p ~> Hsingle n)
  POSTUNIT (p ~> Hsingle (n + 1)).
Proof.
  xwp. rewrite dyn_to_val_dyn_make.
  mxlet (fun r => \[r = n] \* p ~> Hsingle n); [ mxapp Triple_get; xsimpl~ |].
  xpull~. mxlet (fun r => \[r = n + 1] \* p ~> Hsingle n); [ mxapp Triple_add; xsimpl~ |].
  xpull~. mxapp Triple_set; xsimpl.
Qed.

Ltac auto_tilde ::= auto_tilde_default.
