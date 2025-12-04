(*** Lists with Borrowable Elements and Borrowable Tails **)

From Coq Require Import List.
Import ListNotations.

#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
From LogicalPinning Require Import Stdlib.
From LogicalPinning.Examples.Lists.LibBStruct Require Import List.
Require Import List_impl.

#[warnings="-notation-incompatible-prefix"]
From Equations Require Import Equations.

Ltac auto_star_list :=
  simpl MRecord.subst; simpl dyn_value;
  autorewrite with my_rew_maths rew_structForall;
  try easy;
  try solve [ intuition eauto with maths res_List ].
Ltac auto_star ::= auto_star_list.
Ltac auto_tilde ::= intros; subst; auto_star.


(** List Definition *)

Definition zlist: Type := List (ɣb Z).
Notation "'bzlist'" := (ɣb zlist).

Implicit Types (l tl: zlist) (p q: loc) (x: ɣb Z) (v z: Z) (n: nat).

Fixpoint List__es l p: hprop :=
  match l with
  | Nil => \[p = null]
  | Cons x btl => MRecord ([(_elem, ɣB MCell $ x); (_next, ɣIB List__es $ btl)]%list) p
  end.
Arguments List__es: simpl never.

Lemma List__es_Nil: forall p, List__es Nil p = \[p = null].
Proof. reflexivity. Qed.

Lemma List__es_Nil_intro: \[] = List__es Nil null.
Proof. rewrite List__es_Nil. xsimpl*. Qed.

Lemma List__es_Nil_is_null: forall p, List__es Nil p = List__es Nil p \* \[p = null].
Proof. intros. rewrite List__es_Nil. xsimpl*. Qed.

Lemma List__es_Cons_record: forall p x bl,
  List__es (Cons x bl) p
  = MRecord ([(_elem, ɣB MCell $ x); (_next, ɣIB List__es $ bl)]%list) p.
Proof. reflexivity. Qed.

Lemma List__es_Cons: forall p x bl,
  List__es (Cons x bl) p
  = ɣB MCell x (p+_elem)%nat \* (ɣIB List__es) bl (p+_next)%nat \* \[p <> null].
Proof. intros. rewrite List__es_Cons_record. simpl; unfold MField; xsimpl*. Qed.

Lemma List__es_Cons_not_null: forall x bl p,
  List__es (Cons x bl) p ==> List__es (Cons x bl) p \* \[p <> null].
Proof. intros. rewrite List__es_Cons_record. xchanges* MRecord_not_null. Qed.


(**  Borrowing State Transitions *)

Section ListTrans.

  (* inherited *)

  Ltac solve_eq_with lemma :=
    intros; do 2 rewrite List__es_Cons; xpull; intros;
      unfold ɣI; xpull; intros;
      [ xchanges* lemma | xchanges* <- lemma ].

  Ltac solve_to_with lemma :=
    intros; do 2 rewrite List__es_Cons; xpull; intros;
      unfold ɣI; xpull; intros;
      xchanges* lemma.

  Lemma List__es_item_of_eq_b: forall p v q qs btl,
    List__es (offered v @ q :; qs ;; btl) p = List__es (borrowed @ q :; qs ;; btl) p \* MCell v q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma List__es_item_forget_fst: forall p ov btl q qs,
    List__es (pinned ov @ q :; qs ;; btl) p ==> List__es (mkB ov qs ;; btl) p.
  Proof. solve_to_with B_forget_fst. Qed.

  Lemma List__es_tail_of_eq_b: forall p x tl q qs,
    List__es (x ;; offered tl @ q :; qs) p = List__es (x ;; borrowed @ q :; qs) p \* List__es tl q.
  Proof. solve_eq_with Bof_eq_Bb. Qed.

  Lemma List__es_tail_forget_fst: forall p x otl q qs,
    List__es (x ;; pinned otl @ q :; qs) p ==> List__es (x ;; mkB otl qs) p.
  Proof. solve_to_with B_forget_fst. Qed.

  (* specific *)

  Lemma List__es_append2b_forget: forall bl p x ol q qs,
    List__es (x ;; (append2b (mkB ol (q::qs)) bl)) p ==>
    List__es (x ;; (append2b (mkB ol qs) bl)) p.
  Proof.
    intros bl.
    BList_ind bl;
      intros; simp append2b.
    1, 2: xchange List__es_tail_forget_fst.
    do 2 rewrite List__es_Cons. xsimpl~.
    unfold ɣI, ɣB; xpull; intros. xchanges* IH__btl.
  Qed.

  Lemma List__es_append_forget: forall l1 l2 q qs p,
    List__es (append l2 (q::qs) l1) p ==>
    List__es (append l2 qs l1) p.
  Proof. intros l1.
    List_ind l1;
      intros; simpl; try solve [xsimpl].
    destruct tl.
    - xchange* List__es_tail_forget_fst.
    - do 2 rewrite List__es_Cons. xsimpl~.
      unfold ɣI, ɣB; xpull; intros. xchanges* IH.
  Qed.

  Lemma List__es_append2b_weaken: forall p1 l1 qs2 l2 (r: loc),
    structForall isAvailable (owned l1) ->
    ɣB List__es (append2b (available l2 @ qs2) (offered l1 @ p1 :; nil)) r ==>
    List__es (append l2 qs2 l1) r \* \[l1 <> Nil -> r = p1].
  Proof.
    introv SF.
    destruct l1.
    - simp append2b. unfold ɣB. destruct qs2; xsimpl*.
    - simp rew_structForall in *.
      rewrite append2b_correct with (l1 := Cons x bl); auto_star.
      simpl; unfold ɣB. xsimpl*.
      simpl; intros [-> _] _; auto.
  Qed.

End ListTrans.

(** List API *)

Section GetSet.

  Ltac solve_with lemma := intros; xapplys* lemma.

  Lemma Triple_get_elem: forall p v qs bl,
    SPEC (_get_elem p)
    PRE (List__es (available v @ qs ;; bl) p)
    POST (fun (r: Z) => \[r = v] \* List__es (available v @ qs ;; bl) p).
  Proof. solve_with (Triple_get_field_B_cell _elem). Qed.

  Lemma Triple_set_elem: forall p u v qs bl,
    SPEC (_set_elem p u)
    PRE (List__es ((available v @ qs) ;; bl) p)
    POST (fun (r: unit) => List__es ((available u @ qs);; bl) p).
  Proof. solve_with (Triple_set_field_Bcell _elem). Qed.

  Lemma Triple_get_elem_ptr: forall p x bl,
    SPEC (_get_elem_ptr p)
    PRE (List__es (x ;; bl) p)
    POST (fun (r: loc) => List__es (pinb x r ;; bl) p).
  Proof. solve_with (Triple_get_field_loc_B _elem). Qed.

  Lemma Triple_get_next: forall p x bl,
    SPEC (_get_next p)
    PRE (List__es (x ;; bl) p)
    POST (fun (r: loc) => List__es (x ;; pinb bl r) p).
  Proof. solve_with (Triple_get_field_IB _next). Qed.

  Lemma Triple_set_next: forall p1 p2 x1 bl1,
    SPEC (_set_next p1 p2)
    PRE (List__es (x1 ;; bl1) p1)
    POST (fun (r: unit) => List__es (x1 ;; borrowed @ p2 :; nil) p1 \* \exists q, ɣB List__es bl1 q).
  Proof. solve_with (Triple_set_field_IB _next). Qed.

End GetSet.

Lemma Triple_is_empty: forall p l,
  SPEC (_is_empty p)
  PRE  (List__es l p)
  POST (fun (r: bool) => \[r = isTrue (l = Nil)] \* List__es l p).
Proof.
  xwp. mxapp Triple_eq. destruct l; rewrite isTrue_eq_isTrue_eq.
  - rewrite List__es_Nil. xsimpl*.
  - xchange List__es_Cons_not_null. xsimpl*.
Qed.

Ltac handle_is_empty :=
  mxapp Triple_is_empty; xif; auto_tilde.

Ltac handle_not_is_empty :=
  mxapp Triple_is_empty; mxapp Triple_neg; xif; auto_tilde.

Lemma Triple_new: forall v q l,
  SPEC (_new v q)
  PRE  (List__es l q)
  POST (fun (r: loc) => List__es (owned v ;; offered l @ q :; nil) r).
Proof.
  xwp. mxapp Triple_record_alloc; intros p.
  (* TODO: how to avoid [replace] here? *)
  replace (completeFields ([_elem; _next]%list)) with ([_elem%nat; _next%nat]%list) by reflexivity.
  simpl uninitRecordFields.
  do 2 mxapp~ Triple_set_field_strong_cell. mxval.
  xchange* (MRecord_n_eq_Bo _elem).
    xchange* <- Bo_eq_n.
    xchange* (MRecord_cell_and_B_eq_IBp _next).
    xchanges <- List__es_Cons_record.
Qed.

Lemma Triple_new_null: forall v,
  SPEC (_new v null)
  PRE  \[]
  POST (fun (r: loc) => List__es (owned v ;; owned Nil) r).
Proof. rewrite List__es_Nil_intro. intros. xapplys~ Triple_new. xchanges List__es_tail_forget_fst. Qed.

Lemma Triple_size: forall p l,
  structForall isAvailable (owned l) ->
  SPEC (_size p)
  PRE (List__es l p)
  POST (fun (r: Z) => \[r = length l] \* List__es l p).
Proof.
  intros p l. gen p.
  List_ind l as x tl;
    introv SF;
    autorewrite with rew_structForall in *; [.. | easy]; (* solve unavailable case *)
    xwp;
    handle_not_is_empty; [solve [mxvals*] |].

  destruct SF as [Ho SF].
  mxapp* Triple_get_next; intros q. simpl pinb.
  xchange List__es_tail_of_eq_b. mxapp* IH. mxapp Triple_add.
  xchange <- List__es_tail_of_eq_b. xchanges* List__es_tail_forget_fst. simpl; math.
Qed.

Lemma Triple_push_front: forall p v l,
  SPEC (_push_front p v)
  PRE (List__es l p)
  POST (fun (r: loc) => List__es (owned v ;; offered l @ p :; nil) r).
Proof. xwp. mxapp Triple_new; xsimpl. Qed.

Lemma Triple_incr_all: forall p l,
  structForall isAvailable (owned l) ->
  itemForall isAvailable (owned l) ->
  SPEC (_incr_all p)
  PRE (List__es l p)
  POSTUNIT (List__es (map (Borrowable.map (fun v => v + 1)) l) p).
Proof.
  intros p l. gen p.
  List_ind l as x tl;
    introv SF IF;
    autorewrite with rew_structForall rew_itemForall in *; simpl;
    [ .. | easy ];
    xwp;
    handle_not_is_empty; [ solve [mxvals*] | ].
  (* The only case: [l =  x ;; available tl @ qs))] *)
  destruct IF as [Hx IF].
  mxapp* Triple_get_next; intros pn. simpl pinb.
  apply isAvailable_available in Hx as [vx [qs__x ->]].
  mxapp* Triple_get_elem_ptr; intros px. simpl pinb.
  xchange List__es_item_of_eq_b.
    mxapp Stdlib.Triple_incr.
    xchange <- List__es_item_of_eq_b.
    xchange* List__es_item_forget_fst.
  xchange~ List__es_tail_of_eq_b.
    mxapp* IH.
    xchange <- List__es_tail_of_eq_b.
    xchanges* List__es_tail_forget_fst.
Qed.

Lemma Triple_nth_elem: forall z n p l v qs__v,
  nat_to_Z n = z -> (* z > 0 *)
  n < length l ->
  getItem n l = available v @ qs__v ->
  SPEC (_nth_elem p z)
  PRE (List__es l p)
  POST (fun (r: Z) => \[r = v] \* List__es l p).
Proof.
  intros z n p l; gen z n p.
  List_ind l as x tl;
    introv Hn Hlen;
    simpl in *; [solve [math] |..];
    xwp; mxapp Triple_eq.
  - (* [l = x ;; available tl @ qs] *)
    destruct n as [| n1]; simpl in *; subst; xif; try solve [math]; intros _.
    + mxapp Triple_get_elem. xsimpl*.
    + (* n = S n1 *)
      mxapp* Triple_get_next; intros pn. simpl pinb. subst.
      mxapp* Triple_sub.
      xchange List__es_tail_of_eq_b.
        mxapp* IH.
        xchange <- List__es_tail_of_eq_b. xchanges* List__es_tail_forget_fst.
  - (* [l = x ;; unavailable @ qs] *)
    assert (n = O) by math; subst; simpl in *; subst.
    xif; [ intros _ | easy ].
    mxapp Triple_get_elem. xsimpl*.
Qed.

Lemma Triple_nth_elem_ptr: forall z n p l ov qs__v,
  nat_to_Z n = z -> (* z > 0 *)
  n < length l ->
  getItem n l = mkB ov qs__v ->
  SPEC (_nth_elem_ptr p z)
  PRE (List__es l p)
  POST (fun (r: loc) => List__es (substItem n (mkB ov (r :: qs__v)) l) p).
Proof.
  intros z n p l; gen z n p.
  List_ind l as x tl;
    introv Hn Hlen;
    simpl in *; [solve [math] |..];
    xwp; mxapp Triple_eq.
  - (* [l = x ;; available tl @ qs] *)
    destruct n as [| n1]; simpl in *; subst; xif; try solve [math]; intros _.
    + mxapp Triple_get_elem_ptr. xsimpl*.
    + (* n = S n1 *)
      mxapp* Triple_get_next; intros pn. simpl pinb. subst.
      mxapp* Triple_sub.
      xchange List__es_tail_of_eq_b.
        mxapp* IH.
        xchange <- List__es_tail_of_eq_b. xchanges* List__es_tail_forget_fst.
  - (* [l = x ;; unavailable @ qs] *)
    assert (n = O) by math; subst; simpl in *; subst.
    xif; [ intros _ | easy ].
    mxapp Triple_get_elem_ptr. xsimpl*.
Qed.

Lemma Triple_nth_tail_0: forall z p l,
    z = 0 ->
    SPEC (_nth_tail p z)
    PRE  (List__es l p)
    POST (fun (r: loc) => \[r = p] \* List__es l p).
Proof. xwp. subst. mxapp Triple_eq. xif; simpl; intros; [| solve [math]]. mxvals*. Qed.

Lemma Triple_nth_tail_gt0: forall n p z l,
    nat_to_Z n = z ->
    0 < n -> n < length l ->
    SPEC (_nth_tail p z)
    PRE  (List__es l p)
    POST (fun (r: loc) =>
      List__es (substTail n (pinb (getTailb n (owned l)) r) l) p).
Proof.
  intros n p z l; gen n p z.
  List_ind l as x1 tl1;
    introv Hz H0 Hlen;
    simpl in *; try solve [math].
  xwp. mxapp Triple_eq. xif; simpl; intros; [solve [math] |].
  mxapp Triple_get_next; intros pn. simpl pinb.
  mxapp Triple_sub.
  destruct n as [| n1]; [solve [math] |].
  xchange List__es_tail_of_eq_b.
  destruct n1.
  - subst; simpl. mxapp* Triple_nth_tail_0.
    xchange <- List__es_tail_of_eq_b. xchanges List__es_tail_forget_fst.
  - mxapp* (IH (S n1) pn (z-1)); intros q.
    xchange <- List__es_tail_of_eq_b. rewrite substTail_S. xchanges List__es_tail_forget_fst.
Qed.

Lemma Triple_nth_tail: forall n p z l,
    nat_to_Z n = z ->
    n < length l ->
    let btl := getTailb n (owned l) in
    SPEC (_nth_tail p z)
    PRE  (List__es l p)
    POST (fun (r: loc) => List__es (substTail n (pinb btl r) l) p).
Proof.
  introv Hz Hlen. intros btl.
  destruct n.
  - mxapp* Triple_nth_tail_0. simpl. xsimpl.
  - mxapp* Triple_nth_tail_gt0; intros q. xsimpl.
Qed.

Lemma Triple_nth_tail': forall n p z l,
    nat_to_Z n = z ->
    n < length l ->
    SPEC (_nth_tail p z)
    PRE  (List__es l p)
    POST (fun (r: loc) =>
      List__es (substTail n (pinb (getTailb n (owned l)) r) l) p).
Proof.
  introv Hz Hlen.
  destruct n.
  - mxapp* Triple_nth_tail_0. simpl. xsimpl.
  - mxapp* Triple_nth_tail_gt0. xsimpl.
Qed.

Lemma Triple_nth_tail_nat': forall n p l,
    n < length l ->
    SPEC (_nth_tail p (enc (nat_to_Z n)))
    PRE  (List__es l p)
    POST (fun (r: loc) =>
      List__es (substTail n (pinb (getTailb n (owned l)) r) l) p).
Proof. intros. xapplys* Triple_nth_tail'. Qed.

Lemma Triple_get_last_node: forall p l,
  l <> Nil ->
  structForall isAvailable (owned l) ->
  let n := Nat.pred (length l) in
  let btl := getTailb n (owned l) in
  SPEC (_get_last_node p)
  PRE (List__es l p)
  POST (fun (r: loc) =>
    List__es (substTail n (pinb btl r) l) p).
Proof.
  intros p l. gen p.
  List_ind l;
    intros p Hl SF n btl;
    autorewrite with rew_structForall in *; simpl in *; try easy.
  destruct SF as [_ SF].
  xwp. mxapp* Triple_size.
  mxapp Triple_sub; simpl; auto_star.

  mxapp Triple_nth_tail; simpl; auto_star.
  intros q. xsimpl.
Qed.

Lemma Triple_append: forall p1 l1 p2 l2,
  l1 <> Nil ->
  structForall isAvailable (owned l1) ->
  SPEC (_append p1 p2)
  PRE (List__es l1 p1 \* List__es l2 p2)
  POST (fun (r: unit) => List__es (append l2 (p2::nil) l1) p1).
Proof.
  intros p1 l1. gen p1.
  List_ind l1;
    [easy | ..]; (* solve Nil case *)
    introv _ SF;
    autorewrite with rew_structForall in SF; simpl in *; destruct SF as [_ SF];
    [.. | easy]. (* solve unavailable case *)
  xwp.
  mxapp* Triple_get_next; intros pn. simpl pinb.
  xchange List__es_tail_of_eq_b. mxapp Triple_is_empty.
  destruct tl as [| x1 tl1];
    autorewrite with rew_structForall in SF; simpl;
    xif; intros; try easy.
  - mxapp Triple_set_next; intros q. xchange <- List__es_tail_of_eq_b.
    unfold ɣB at 1. xchange~ List__es_Nil. xsimpl.
  - mxapp* IH. xchange <- List__es_tail_of_eq_b. xchanges List__es_tail_forget_fst.
Qed.

Lemma Triple_append_b: forall p1 l1 p2 l2,
  l1 <> Nil ->
  structForall isAvailable (owned l1) ->
  let x1 := head (missing) l1 in
  let btl1 := tail l1 in
  SPEC (_append p1 p2)
  PRE (List__es l1 p1 \* List__es l2 p2)
  POST (fun (r: unit) => List__es (x1 ;; (append2b (offered l2 @ p2 :; nil) btl1)) p1).
Proof.
  intros p1 l1. gen p1.
  List_ind l1 as x1 tl1;
    [ easy | .. ]; (* solve Nil case *)
    introv _ SF;
    autorewrite with rew_structForall in SF; simpl in *; destruct SF as [_ SF];
    [ .. | easy ]. (* solve unavailable case *)
  (* [l1 = x1 ;; available tl1 @ qs] *)
  xwp. mxapp Triple_get_next; intros pn. simpl pinb.
  xchange List__es_tail_of_eq_b.
  destruct tl1 as [| x2 tl2];
    autorewrite with rew_structForall in SF; simp append2b;
    handle_is_empty.
  - mxapp Triple_set_next; intros q. xchange <- List__es_tail_of_eq_b.
    unfold ɣB at 1. xchange~ List__es_Nil. xsimpl.
  - mxapp* IH. simpl. xchange <- List__es_tail_of_eq_b. xchanges List__es_tail_forget_fst.
Qed.

Lemma Triple_append_rp: forall p1 l1 p2 l2,
  structForall isAvailable (owned l1) ->
  SPEC (_append_rp p1 p2)
  PRE (List__es l1 p1 \* List__es l2 p2)
  POST (fun (r: loc) => ɣB List__es (append2b (offered l2 @ p2 :; nil) (offered l1 @ p1 :; nil)) r).
Proof.
  intros p1 l1. gen p1.
  List_ind l1 as x1 tl1;
    introv SF;
    simp rew_structForall append2b in *;
    [ .. | easy ];
    xwp; handle_is_empty.
  - (* [l1 = Nil] *)
    xchange~ List__es_Nil. unfold ɣB. mxvals*.
  - (* [l1 = Cons _ _] *)
    mxapp* Triple_append_b. simpl.
    unfold ɣB. mxvals*.
Qed.

Lemma Triple_append_rp': forall p1 l1 p2 l2,
  structForall isAvailable (owned l1) ->
  SPEC (_append_rp p1 p2)
  PRE (List__es l1 p1 \* List__es l2 p2)
  POST (fun (r: loc) => List__es (append l2 (p2::nil) l1) r \* \[l1 <> Nil -> r = p1]).
Proof.
  introv SF.
  xapply* Triple_append_rp.
  - xsimpl.
  - xpull; intros r. xchanges* List__es_append2b_weaken.
Qed.

Lemma Triple_push_back: forall p v l,
  l <> Nil ->
  structForall isAvailable (owned l) ->
  let x := head (missing) l in
  let btl := tail l in
  let lv := owned v ;; owned Nil in
  SPEC (_push_back p v)
  PRE (List__es l p)
  POST (fun (r: unit) => List__es (x ;; (append2b (owned lv) btl)) p).
Proof.
  intros p v l. gen p v.
  List_ind l;
    [ easy | .. ]; (* solve Nil case *)
    introv Hl SF;
    simp rew_structForall in *;
    [ | easy ]. (* solve inaccessible case *)
  simpl in *.
  xwp. mxapp Triple_new_null; intro q.
  mxapp* Triple_append_b. simpl.
  xchanges* List__es_append2b_forget.
Qed.

Lemma Triple_push_back': forall p v l,
  l <> Nil ->
  structForall isAvailable (owned l) ->
  let lv := owned v ;; owned Nil in
  SPEC (_push_back p v)
  PRE (List__es l p)
  POST (fun (r: unit) => List__es (append lv nil l) p).
Proof.
  intros p v l. gen p v.
  List_ind l;
    [solve [easy] | ..]; (* solve Nil case *)
    introv Hl SF;
    simp rew_structForall in *;
    [ | solve [easy] ]. (* solve inaccessible case *)
  xwp. mxapp Triple_new_null; intro q.
  mxapp* Triple_append.
  xchanges* List__es_append_forget.
Qed.

Lemma Triple_push_back_rp: forall p v l,
  structForall isAvailable (owned l) ->
  let lv := owned v ;; owned Nil in
  SPEC (_push_back_rp p v)
  PRE (List__es l p)
  POST (fun (r: loc) => ɣB List__es (append2b (owned lv) (offered l @ p :; nil)) r).
Proof.
  intros p v l. gen p v.
  List_ind l;
    intros;
    simp rew_structForall in *; [ .. | easy ].
  all: xwp;
    mxapp Triple_new_null; intros q;
    mxapp* Triple_append_rp; intros r.
  all: simp append2b; unfold ɣB.
  - xsimpl*.
  - xchanges* List__es_append2b_forget.
Qed.

Lemma Triple_push_back_rp': forall p v l,
  structForall isAvailable (owned l) ->
  let lv := owned v ;; owned Nil in
  SPEC (_push_back_rp p v)
  PRE (List__es l p)
  POST (fun (r: loc) => List__es (append lv nil l) r \* \[l <> Nil -> r = p]).
Proof.
  intros * SF lv.
  xapply* Triple_push_back_rp.
  - xsimpl.
  - xpull; intros r. xchanges* List__es_append2b_weaken.
Qed.

Lemma Triple_pop_front: forall p x l qs,
  SPEC (_pop_front p)
  PRE  (List__es (x ;; available l @ qs) p)
  POST (fun (r: loc) =>
          List__es l r \* \[eqlocs qs r] \* (ɣB MCell) x (p+_elem)%nat).
Proof.
  xwp. mxapp Triple_get_next; intros q. simpl pinb.
  xchanges~ List__es_Cons. xchange IBp_eq_cell_and_B.
  mxapp* (Triple_get_field_loc_bare _next). mxapp Triple_free_cell.
  unfold ɣB at 1. xpull; intros; mxvals*.
Qed.

Lemma Triple_free_node': forall p v q,
  SPEC (_free_node p)
  PRE  (MRecord ([(_elem, MCell $ v); (_next, MCell $ q)])%list p)
  POST (fun (r: unit) => \[]).
Proof.
  xwp. simpl; unfold MField; xpull; intros.
  mxapp* (Triple_get_field_loc_bare _elem). mxapp Triple_free_cell.
  mxapp* (Triple_get_field_loc_bare _next). mxapp Triple_free_cell.
  xsimpl.
Qed.

Lemma Triple_free_node'': forall p v qs__v q__tl qs__tl,
  SPEC (_free_node p)
  PRE  (List__es (available v @ qs__v ;; borrowed @ q__tl :; qs__tl) p)
  POST (fun (r: unit) => \[eqlocs qs__tl q__tl]).
Proof.
  xwp. rewrite List__es_Cons_record.
  xchange* (MRecord_B_forget_all _elem). xchange* (MRecord_Bo_eq_n _elem).
  xchange* (MRecord_IBp_eq_cell_and_B _next). unfold ɣB at 1.
  simpl; unfold MField; xpull; intros.
  mxapp* (Triple_get_field_loc_bare _elem). mxapp Triple_free_cell.
  mxapp* (Triple_get_field_loc_bare _next). mxapp Triple_free_cell.
  xsimpl*.
Qed.

Lemma Triple_pop_and_free_front: forall p v qs__v l qs__l,
  SPEC (_pop_and_free_front p)
  PRE  (List__es (available v @ qs__v ;; available l @ qs__l) p)
  POST (fun (r: loc) => List__es l r \* \[eqlocs qs__l r]).
Proof.
  xwp. mxapp Triple_get_next; intros q. simpl pinb.
  xchange List__es_tail_of_eq_b.
  mxapp~ Triple_free_node''. mxvals*.
Qed.

Lemma Triple_read_front: forall p v qs__v bl,
  SPEC (_read_front p)
  PRE  (List__es (available v @ qs__v ;; bl) p)
  POST (fun (r: Z) => \[r = v] \* List__es (available v @ qs__v ;; bl) p).
Proof. xwp. mxapp Triple_get_elem. xsimpl*. Qed.

(** Deletes the list structure. *)
(*     If the elem is stored indirectly, leaves the elem intact. Otherwise, the *)
(*     in-place elem is deleted along with the structure. *)

(*     in C:   [node* -> unit] *)
(*     in Coq: [loc   -> unit] *)
(*  *)
(* Parameter delete: val. *)

(* Parameter spec_delete: forall (l: zlist) (p: loc), *)
(*   SPEC (delete p) *)
(*   PRE (List__es l p) *)
(*   POST (fun (r: unit) => \[]). *)

(* Parameter spec_delete': forall (l: zlist) (p: loc), *)
(*   SPEC (delete p) *)
(*   PRE (List__es l p) *)
(*   POST (fun (r: unit) => \[]). *)
