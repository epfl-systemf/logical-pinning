(*** Lists with Borrowable Elements **)

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
From LogicalPinning.Examples.Lists.LibBare Require Import List ListExec.
Import ListExec.RewListExec.
Require Import List_impl.

From Coq Require Import List.
Import ListNotations.

Import NotationForVariables.
Import NotationForTerms.

Ltac auto_star_list :=
  simpl MRecord.subst; simpl dyn_value;
  autorewrite with my_rew_maths;
  try solve [ easy ];
  try solve [ intuition eauto with maths ].
Ltac auto_star ::= auto_star_list.
Ltac auto_tilde ::= intros; subst; auto_star.

(** List Definition *)

Definition zlist := list (ɣb Z).

Implicit Types (l: zlist) (p q: loc) (x y: ɣb Z) (v z: Z) (n: nat).

Fixpoint List__e l p: hprop :=
  match l with
  | nil => \[p = null]
  | x :: tl => MRecord ([(_elem, ɣB MCell $ x); (_next, ɣI List__e $ tl)]) p
  end.
Arguments List__e: simpl never.

Lemma List__e_nil: forall p, List__e nil p = \[p = null].
Proof. reflexivity. Qed.

Lemma List__e_nil_intro: \[] = List__e nil null.
Proof. rewrite List__e_nil. xsimpl*. Qed.

Lemma List__e_cons_record: forall p x l,
  List__e (x :: l) p = MRecord ([(_elem, ɣB MCell $ x); (_next, ɣI List__e $ l)]) p.
Proof. reflexivity. Qed.

Lemma List__e_cons: forall p x l,
  List__e (x :: l) p = ɣB MCell x (p+_elem)%nat \* ɣI List__e l (p+_next)%nat \* \[p <> null].
Proof. intros. rewrite List__e_cons_record. simpl; unfold MField; xsimpl*. Qed.

Lemma List__e_cons_not_null: forall p x l,
  List__e (x :: l) p ==> List__e (x :: l) p \* \[p <> null].
Proof. intros. rewrite List__e_cons_record. xchanges* MRecord_not_null. Qed.

Hint Rewrite List__e_nil List__e_cons: rew_mlist.

(** List Segment Definition *)

Fixpoint ListSeg q l p: hprop :=
  match l with
  | nil => \[p = q]
  | x :: tl => MRecord ([(_elem, ɣB MCell $ x); (_next, ɣI (ListSeg q) $ tl)]) p
  end.
Arguments ListSeg: simpl never.

Lemma ListSeg_nil: forall p q,
  ListSeg q nil p = \[p = q].
Proof. reflexivity. Qed.

Lemma ListSeg_cons_record: forall p q x l,
  ListSeg q (x::l) p = MRecord ([(_elem, ɣB MCell $ x); (_next, ɣI (ListSeg q) $ l)]) p.
Proof. reflexivity. Qed.

Lemma ListSeg_cons: forall x l p q,
  ListSeg q (x::l) p = ɣB MCell x (p+_elem)%nat \* ɣI (ListSeg q) l (p+_next)%nat \* \[p <> null].
Proof. intros. rewrite ListSeg_cons_record. simpl; unfold MField; xsimpl*. Qed.


(**  Borrowing State Transitions *)

Section ListTrans.

  Ltac ind_list l n IH :=
    induction l as [| ?x1 ?l1 IH];
      simpl; [solve [math] |]; intro n; intros;
      destruct n; autorewrite with rew_list rew_mlist; subst.

  Ltac solve_eq_with l lemma :=
    let n := fresh "n" in
    let IH := fresh "IH" in
    ind_list l n IH;
    [ rewrite lemma; xsimpl*
    | unfold ɣI; xpull; intros; [xchanges~ (IH n) | xchanges~ <- (IH n)] ].

  Ltac solve_to_with l lemma :=
    let n := fresh "n" in
    let IH := fresh "IH" in
    ind_list l n IH;
    [ xchanges* lemma
    | unfold ɣI; xsimpl* ].

  Lemma List__e_Bof_eq_Bb: forall n p v q qs l,
    n < LibListExec.length l ->
    ListExec.nth n l = offered v @ q :; qs ->
    List__e l p = List__e (⟦n := borrowed @ q :; qs⟧ l) p \* MCell v q.
  Proof. intros n p v q qs l. gen n p. solve_eq_with l Bof_eq_Bb. Qed.

  Lemma List__e_Bb_eq_Bof: forall n p v q qs l,
    n < LibListExec.length l ->
    ListExec.nth n l = borrowed @ q :; qs ->
    List__e l p \* MCell v q = List__e (⟦n := offered v @ q :; qs⟧ l) p.
  Proof. intros n p v q qs l. gen n p. solve_eq_with l Bof_eq_Bb. Qed.

  Lemma List__e_B_forget_fst: forall n p v q qs l,
    n < LibListExec.length l ->
    ListExec.nth n l = offered v @ q :; qs ->
    List__e l p ==> List__e (⟦n := available v @ qs⟧ l) p.
  Proof. intros n p v q qs l. gen n p. solve_to_with l B_forget_fst. Qed.

End ListTrans.

(** List API *)

Lemma Triple_new: forall v q l,
  SPEC (_new v q)
  PRE  (List__e l q)
  POST (fun (r: loc) => List__e ((mkB (Some v) nil) :: l) r).
Proof.
  xwp. mxapp Triple_record_alloc; intros p.
  (* TODO: avoid [replace] *)
  replace (completeFields ([_elem; _next])) with [_elem%nat; _next%nat] by reflexivity.
  simpl uninitRecordFields.
  do 2 mxapp~ Triple_set_field_strong_cell. mxval.
  xchange* (MRecord_n_eq_Bo _elem). xchange* (MRecord_I_fold _next).
  xchanges <- List__e_cons_record.
Qed.

Lemma Triple_new_null: forall v,
  SPEC (_new v null)
  PRE  \[]
  POST (fun (r: loc) => List__e ((owned v) :: nil) r).
Proof. rewrite List__e_nil_intro. intros. xapplys Triple_new. Qed.

Lemma Triple_get_elem: forall p v qs l,
  SPEC (_get_elem p)
  PRE  (List__e ((available v @ qs) :: l) p)
  POST (fun (r: Z) => \[r = v] \* List__e ((available v @ qs) :: l) p).
Proof. intros. xapplys* (Triple_get_field_B_cell _elem). Qed.

Lemma Triple_read_front: forall p v qs l,
  SPEC (_read_front p)
  PRE  (List__e ((available v @ qs) :: l) p)
  POST (fun (r: Z) => \[r = v] \* List__e ((available v @ qs) :: l) p).
Proof. xwp. mxapp Triple_get_elem. xsimpl*. Qed.

Lemma Triple_set_elem: forall p u v qs bl,
  SPEC (_set_elem p u)
  PRE (List__e ((available v @ qs) :: bl) p)
  POST (fun (r: unit) => List__e ((available u @ qs) :: bl) p).
Proof. intros. xapplys* (Triple_set_field_Bcell _elem). Qed.

Lemma Triple_get_elem_ptr: forall p x l,
  SPEC (_get_elem_ptr p)
  PRE  (List__e (x :: l) p)
  POST (fun (r: loc) => List__e (pinb x r :: l) p).
Proof. intros. xapplys* (Triple_get_field_loc_B _elem). Qed.

Lemma Triple_get_next: forall p x l,
  SPEC (_get_next p)
  PRE  (List__e (x::l) p)
  POST (fun (r: loc) => MRecord ([(_elem, ɣB MCell $ x); (_next, ɣIB List__e $ offered l @ r :; nil)]) p).
Proof. intros. rewrite List__e_cons_record. xapplys~ (Triple_get_field_I _next). Qed.

Lemma Triple_set_next: forall p1 p2 x1 l1,
  SPEC (_set_next p1 p2)
  PRE (List__e (x1 :: l1) p1)
  POST (fun (r: unit) => MRecord ([(_elem, ɣB MCell $ x1); (_next, ɣIB List__e $ borrowed @ p2 :; nil)]) p1 \* \exists q, List__e l1 q).
Proof. intros. rewrite List__e_cons_record. xapplys* (Triple_set_field_I _next). Qed.

Lemma Triple_is_empty: forall p l,
  SPEC (_is_empty p)
  PRE  (List__e l p)
  POST (fun (r: bool) => \[r = isTrue (l = nil)] \* List__e l p).
Proof.
  xwp. mxapp Triple_eq. destruct l; rewrite isTrue_eq_isTrue_eq.
  - rewrite List__e_nil. xsimpl*.
  - xchange List__e_cons_not_null. xsimpl*.
Qed.

Ltac handle_not_is_empty :=
  mxapp Triple_is_empty; mxapp Triple_neg; xif; auto_tilde.

Lemma Triple_size: forall p l,
  SPEC (_size p)
  PRE  (List__e l p)
  POST (fun (r: Z) => \[r = length l] \* List__e l p).
Proof.
  intros p l; gen p.
  induction l as [| x l IHl];
    xwp;
    handle_not_is_empty; [ solve [mxvals*] | ].
  xchange List__e_cons_record.
  mxapp* Triple_get_field_I; intros q.
  xchange* (MRecord_IBp_eq_cell_and_B _next). xchange Bo_eq_n.
  mxapp IHl. mxapp Triple_add. xchange* (MRecord_I_fold _next).
  xchanges <- List__e_cons_record. simpl; math.
Qed.

Lemma Triple_push_front: forall p v l,
  SPEC (_push_front p v)
  PRE  (List__e l p)
  POST (fun (r: loc) => List__e (owned v :: l) r).
Proof. xwp. mxapp* Triple_new; xsimpl. Qed.

Lemma Triple_pop_front: forall p x l,
  SPEC (_pop_front p)
  PRE  (List__e (x::l) p)
  POST (fun (r: loc) => List__e l r \* (ɣB MCell) x (p+_elem)%nat).
Proof.
  xwp. mxapp Triple_get_next; intros r.
  xchange* (MRecord_IBp_eq_cell_and_B _next). xchange Bo_eq_n.
  simpl; unfold MField. xpull; intros.
  mxapp* (Triple_get_field_loc_bare _next). mxapp Triple_free_cell. mxvals.
Qed.

Lemma Triple_free_node: forall p v qs__v q,
  SPEC (_free_node p)
  PRE  (MRecord ([(_elem, ɣB MCell $ available v @ qs__v); (_next, MCell $ q)]) p)
  POST (fun (r: unit) => \[]).
Proof.
  xwp. simpl; unfold MField; xpull; intros.
  mxapp* (Triple_get_field_loc_bare _elem).
  xchange B_forget_all. xchange Bo_eq_n. mxapp Triple_free_cell.
  mxapp* (Triple_get_field_loc_bare _next). mxapp Triple_free_cell.
  xsimpl.
Qed.

Lemma Triple_pop_and_free_front: forall p v qs__v l,
  SPEC (_pop_and_free_front p)
  PRE  (List__e ((available v @ qs__v)::l) p)
  POST (fun (r: loc) => List__e l r).
Proof.
  xwp. mxapp Triple_get_next; intros r.
  xchange* (MRecord_IBp_eq_cell_and_B _next). xchange Bo_eq_n.
  mxapp Triple_free_node. mxvals.
Qed.

Lemma Triple_incr_all: forall p l,
  LibListExec.Forall is_available l = true ->
  SPEC (_incr_all p)
  PRE  (List__e l p)
  POSTUNIT (List__e (LibList.map (Borrowable.map (fun v => v + 1)) l) p).
Proof.
  (* Convert [LibListExec.Forall] to [List.Forall] *)
  intros p l H.
  erewrite LibListExec.Forall_eq in H; [| solve [apply isAvailable_isTrue_pred]].
  rewrite isTrue_eq_true_eq in H.

  gen p.
  induction l as [| x l IHl];
    xwp;
    handle_not_is_empty; [ solve [mxvals*] | ].
  xchange List__e_cons_record.
  mxapp~ Triple_get_field_I.
  apply Forall_cons_inv_head in H as Hx. apply Forall_cons_inv_tail in H as Hl.
  apply isAvailable_available in Hx as [vx [qs ->]].
  mxapp* (Triple_get_field_loc_B _elem); intros px. simpl pinb.
  xchange~ (MRecord_Bof_eq_Bb _elem).
    mxapp Stdlib.Triple_incr.
    xchange* (MRecord_Bb_eq_Bof _elem).
    xchange* (MRecord_B_forget_fst _elem).
  xchange* (MRecord_IBp_eq_cell_and_B _next).
    xchange* Bo_eq_n.
    mxapp* IHl.
    xchange* (MRecord_I_fold _next).
  xchanges <- List__e_cons_record.
Qed.

Ltac handle_n_eq_O n :=
  let n' := fresh "n" in
  mxapp Triple_eq;
  destruct n as [| n'];
    xif; simpl; try math;
    rew_list in *; intros; subst.

Lemma Triple_nth_elem: forall l z n p v qs,
  nat_to_Z n = z -> (* z > 0 *)
  n < LibListExec.length l ->
  ListExec.nth n l = available v @ qs ->
  SPEC (_nth_elem p z)
  PRE  (List__e l p)
  POST (fun (r: Z) => \[r = v] \* List__e l p).
Proof.
  induction l;
    simpl; [solve [math] |];
    xwp;
    handle_n_eq_O n.
  - (* [n = O] *) mxapp Triple_get_elem; xsimpl*.
  - (* [n = S n1] *)
    xchange List__e_cons_record.
    mxapp* (Triple_get_field_I _next); intros q.
    xchange* (MRecord_IBp_eq_cell_and_B _next). xchange* Bo_eq_n.
    mxapp* Triple_sub. mxapp* IHl.
    xchange* (MRecord_I_fold _next).
    xchanges* <- List__e_cons_record.
Qed.

Lemma Triple_nth_elem_ptr: forall l z n p,
  nat_to_Z n = z ->
  n < LibListExec.length l ->
  let x := ListExec.nth n l in
  SPEC (_nth_elem_ptr p z)
  PRE  (List__e l p)
  POST (fun (r: loc) => List__e (update n (pinb x r) l) p).
Proof.
  induction l;
    simpl; [solve [math] |];
    xwp;
    handle_n_eq_O n.
  - (* [n = O] *) mxapp~ Triple_get_elem_ptr. xsimpl*.
  - (* [n = S n1] *)
    xchange List__e_cons_record.
    mxapp* (Triple_get_field_I _next); intros qn.
    mxapp* Triple_sub.
    xchange* (MRecord_IBp_eq_cell_and_B _next). xchange Bo_eq_n.
    mxapp* IHl; intros qx.
    xchange* (MRecord_I_fold _next).
    xchanges* <- List__e_cons_record.
Qed.

Lemma Triple_nth_tail_0: forall z p l,
    z = 0 ->
    SPEC (_nth_tail p z)
    PRE  (List__e l p)
    POST (fun (r: loc) => \[r = p] \* List__e l p).
Proof. xwp. subst. mxapp Triple_eq. xif; simpl; intros; [| solve [math]]. mxvals*. Qed.

Lemma Triple_nth_tail_gt0: forall n p z l,
    nat_to_Z n = z ->
    0 < n -> n < length l ->
    SPEC (_nth_tail p z)
    PRE  (List__e l p)
    POST (fun (r: loc) => ListSeg r (firstn n l) p \* List__e (skipn n l) r).
Proof.
  intros n p z l; gen n p z.
  induction l as [| x l];
    introv Hz H0 Hlen; simpl in *; [solve [math] |].
  xwp. mxapp Triple_eq. xif; simpl; intros; [solve [math] |].
  mxapp Triple_get_next; intros pn. mxapp Triple_sub.
  xchange* (MRecord_IBof_eq_IBb _next).
  destruct n as [| n1]; [solve [math] |].
  destruct n1.
  - subst. mxapp* Triple_nth_tail_0.
    xchange* (MRecord_IBb_eq_IBof _next).
    simpl firstn; simpl skipn. rewrite ListSeg_cons.
    simpl; unfold MField; unfold ɣI; xpull; intros; subst.
    xsimpl*. simplb. rewrite ListSeg_nil. xpull; intros [-> _]; xsimpl*.
  - Opaque firstn skipn.
    mxapp* (IHl (S n1) pn (z-1)); intros q.
    Transparent firstn skipn.
    rewrite firstn_cons. rewrite skipn_cons. rewrite ListSeg_cons.
    simpl MRecord; unfold MField. xpull; intros. xsimpl*.
    unfold ɣI; xpull; intros. simplb. xpull; intros [-> _]; xsimpl*.
Qed.

Lemma Triple_nth_tail: forall n p z l,
    nat_to_Z n = z ->
    n < length l ->
    SPEC (_nth_tail p z)
    PRE  (List__e l p)
    POST (fun (r: loc) => ListSeg r (firstn n l) p \* List__e (skipn n l) r).
Proof.
  intros. destruct n.
  - xapplys* Triple_nth_tail_0. intros ? ->; simpl. rewrite ListSeg_nil. xsimpl*.
  - xapplys* Triple_nth_tail_gt0.
Qed.

Lemma Triple_append: forall p1 l1 p2 l2,
  l1 <> nil ->
  SPEC (_append p1 p2)
  PRE (List__e l1 p1 \* List__e l2 p2)
  POST (fun (r: unit) => List__e (l1++l2) p1).
Proof.
  intros p1 l1. gen p1.
  induction l1 as [| x l]; [easy |].
  xwp. mxapp Triple_get_next; intros pn.
  xchange* (MRecord_IBof_eq_IBb _next). mxapp Triple_is_empty.
  destruct l; xif; try easy; intros _.
  - mxapp* Triple_set_field_IB. intros q. simpl app.
    xchange* (MRecord_IBb_eq_IBof _next). xchange* (MRecord_IB_forget_fst _next).
    xchange* (MRecord_IBo_eq_I _next). rewrite List__e_cons_record. rewrite List__e_nil.
    unfold ɣB at 2. xpull; intros; xsimpl.
  - mxapp* IHl. xchange* (MRecord_IBb_eq_IBof _next). xchange* (MRecord_IB_forget_fst _next).
    xchange* (MRecord_IBo_eq_I _next). rewrite List__e_cons_record.
    rewrite app_comm_cons. xsimpl.
Qed.

Lemma Triple_append_rp: forall p1 l1 p2 l2,
  SPEC (_append_rp p1 p2)
  PRE (List__e l1 p1 \* List__e l2 p2)
  POST (fun (r: loc) => List__e (l1 ++ l2) r \* \[l1 <> nil -> r = p1]).
Proof.
  xwp.
  mxapp Triple_is_empty.
  destruct l1;
    xif; intros; try easy.
  - mxval. simpl. rewrite List__e_nil. xsimpl*.
  - mxapp* Triple_append. mxvals*.
Qed.

Lemma Triple_push_back_rp: forall p v l,
  SPEC (_push_back_rp p v)
  PRE (List__e l p)
  POST (fun (r: loc) => List__e (l ++ ((owned v) :: nil)) r \* \[l <> nil -> r = p]).
Proof.
  intros p v l. gen p v.
  xwp. mxapp Triple_new_null. intros q. mxapp Triple_append_rp.
  intros. xsimpl*.
Qed.

Ltac auto_star ::=
  repeat (
    simpl MRecord.subst; simpl dyn_value;
    autorewrite with my_rew_maths;
    rew_list_exec; rew_list;
    try solve [ easy ];
    try solve [ intuition eauto with maths ]).

Lemma Triple_swap_elem: forall l z1 z2 n1 n2 p v1 qs1 v2 qs2,
  nat_to_Z n1 = z1 ->
  nat_to_Z n2 = z2 ->
  n1 < LibListExec.length l ->
  n2 < LibListExec.length l ->
  n1 <> n2 ->
  ListExec.nth n1 l = available v1 @ qs1 ->
  ListExec.nth n2 l = available v2 @ qs2 ->
  SPEC (_swap_elem p z1 z2)
  PRE  (List__e l p)
  POST (fun (_: unit) => List__e (⟦n1 := available v2 @ qs1⟧ ⟦n2 := available v1 @ qs2⟧ l) p).
Proof.
  introv Hn1 Hn2 Hlen1 Hlen2 Hneq Hv1 Hv2. rew_list_exec in *.
  xwp.
  mxapp* Triple_nth_elem_ptr; rewrite Hv1; intros r1. simpl pinb.
  mxapp* Triple_nth_elem_ptr; rewrite Hv2; intros r2. simpl pinb.
  (* TODO: normalization instead of manual massaging *)
  xchange~ (List__e_Bof_eq_Bb n1). rewrite update_comm; auto_star.
  xchange~ (List__e_Bof_eq_Bb n2). rewrite update_comm; auto_star.
  mxapp Stdlib.Triple_swap.
  xchange* (List__e_Bb_eq_Bof n1 p v2 r1). xchange* (List__e_B_forget_fst n1).
  xchange* (List__e_Bb_eq_Bof n2 p v1 r2). xchange* (List__e_B_forget_fst n2).
  rewrite update_comm; auto_star.
  xsimpl.
Qed.

Section LoggerExample.

(**  Helper *)

Lemma Forall_nth_pinb: forall l n q,
  n < LibList.length l ->
  LibList.Forall isAvailable l ->
  LibList.Forall isAvailable (⟦ n := pinb (LibList.nth n l) q ⟧ l).
Proof.
  induction l; destruct n;
    introv Hlen H;
    rew_list in *; simpl; try easy.
  all: invert H; intros; subst.
  - constructor; simpl; auto. apply isAvailable_pinb; auto.
  - constructor; simpl; auto. apply IHl; auto; math.
Qed.

(**  Program *)

(* Simplified from the logger example: lookup, map, use the previous exposed pointer *)
Definition _logger_example: val :=
  Fun 'p 'n :=
    Let 'q := _nth_elem_ptr 'p 'n in
    _incr_all 'p ';
    '! 'q.

(**  Proof *)

Lemma Triple_logger_example: forall l p n z v qs,
  nat_to_Z n = z ->
  n < LibListExec.length l ->
  ListExec.nth n l = available v @ qs ->
  LibListExec.Forall is_available l = true ->
  SPEC (_logger_example p z)
  PRE  (List__e l p)
  POST (fun (r: Z) => \[r = v + 1] \* List__e (LibList.map (Borrowable.map (fun v => v + 1)) l) p).
Proof.
  introv Hn Hlen Hnth Hforall. rew_list_exec in *.
  xwp.
  mxapp* Triple_nth_elem_ptr; intros q.
  mxapp* Triple_incr_all.
  { erewrite LibListExec.Forall_eq in *;
      try rewrite isTrue_eq_true_eq in *;
      try solve [apply isAvailable_isTrue_pred].
    apply Forall_nth_pinb; auto. }
  rewrite Hnth; simpl. rewrite LibList.map_update; simpl; auto.
  xchange (List__e_Bof_eq_Bb n); rew_list_exec; rew_list*.
  mxapp Triple_get_cell.
  xchange (List__e_Bb_eq_Bof n); rew_list_exec; rew_list*.
  xchange (List__e_B_forget_fst n); rew_list_exec; rew_list*.
  replace (available v + 1 @ qs) with (Borrowable.map (fun v => v + 1) (LibList.nth n l)); cycle 1.
  { rewrite Hnth; auto. }
  rewrite <- map_update; auto. rewrite update_nth_same; auto. xsimpl*.
Qed.

End LoggerExample.

Ltac auto_tilde ::= auto_tilde_default.
Ltac auto_star  ::= auto_star_default.
