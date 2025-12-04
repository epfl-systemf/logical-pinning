#[warnings="-notation-overridden -ambiguous-paths -notation-incompatible-prefix"]
Require Export WPUntyped Borrowable ValOps MRecord.

Import NotationForVariables.
Import NotationForTerms.
Notation "''tmp'" := ("tmp":var) : var_scope.

Implicit Types (p q: loc) (n: nat) (z: Z).

Lemma nat_to_Z_sub: forall n,
  nat_to_Z (S n) - 1 = nat_to_Z n.
Proof. math. Qed.
#[global] Hint Rewrite nat_to_Z_sub: my_rew_maths.

Definition _incr: val :=
  Fun 'p := 'p ':= (('! 'p) '+ 1).

Lemma Triple_incr: forall z p,
  Triple (_incr p)
    (MCell z p)
    (fun _: unit => MCell (z+1) p).
Proof. xwp. mxapp Triple_get_cell. mxapp Triple_add. mxapp Triple_set_cell. xsimpl. Qed.

Definition _swap: val :=
  Fun 'p1 'p2 := Let 'tmp := '! 'p1 in 'p1 ':= ('! 'p2) '; 'p2 ':= 'tmp.

Lemma Triple_swap: forall p1 p2 A `{Enc A} (v1 v2: A),
  SPEC (_swap p1 p2)
  PRE (MCell v1 p1 \* MCell v2 p2)
  POST (fun _: unit => MCell v2 p1 \* MCell v1 p2).
Proof. xwp. do 2 mxapp Triple_get_cell. do 2 mxapp Triple_set_cell. xsimpl. Qed.
