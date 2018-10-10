Require Omega.
Import BinInt.

Lemma jhead_termination: forall n,
  _GHC.Base.<_ n 10%Z = false ->
  Z.abs_nat (n / 10) < Z.abs_nat n.
Proof.
  intros.
  assert (0 < n)%Z. {
    destruct n; Coq.Program.Tactics.program_simpl.
    apply Pos2Z.is_pos.
  }
  apply Zabs.Zabs_nat_lt. split.
  - apply Zdiv.Z_div_pos; Omega.omega.
  - apply Zdiv.Z_div_lt; Omega.omega.
Qed.

Lemma jblock'_termination: forall d,
  _GHC.Base.==_ d 1%Z = false ->
  _GHC.Base.<_ d 1%Z = false ->
  Z.abs_nat (d - 1) < Z.abs_nat d.
Proof.
  intros.
  assert (0 < d)%Z. {
    destruct d; Coq.Program.Tactics.program_simpl.
    apply Pos2Z.is_pos.
  } apply Zabs.Zabs_nat_lt. Omega.omega.
Qed.

Lemma jsplitf_termination: forall p n,
  _GHC.Base.<=_ p 1%Z = false ->
  _GHC.Base.>_ p n = false ->
  Z.abs_nat n - Z.abs_nat (p * p - 1) < Z.abs_nat n - Z.abs_nat (p - 1).
Proof.
  intros p n Hp1 Hpn.
  unfold GHC.Base.op_zlze__ in Hp1. unfold GHC.Base.op_zg__ in Hpn. unfold Base.Ord_Integer___ in Hp1,Hpn. simpl in Hp1,Hpn.
  apply Z.leb_gt in Hp1. apply Z.ltb_ge in Hpn.
  assert (1 * 1 <= p * p)%Z. {
    apply Z.mul_le_mono_nonneg; Omega.omega.
  }
  rewrite 3! Znat.Zabs2Nat.abs_nat_nonneg by Omega.omega.
  rewrite <- 2! Znat.Z2Nat.inj_sub by Omega.omega.
  set (m := (n - (p * p - 1))%Z).
  destruct (0 <=? m)%Z eqn:Hleb.
  - apply Z.leb_le in Hleb.
    rewrite <- 2! Znat.Zabs2Nat.abs_nat_nonneg; try Omega.omega.
    apply Zabs.Zabs_nat_lt.
    split. { assumption. }
    apply Z.sub_le_lt_mono. { apply Z.le_refl. }
    apply Z.sub_lt_le_mono; try Omega.omega.
    rewrite <- Z.mul_1_l at 1.
    apply Z.mul_lt_mono_pos_r; Omega.omega.
  - apply Z.leb_gt in Hleb.
    destruct m; inversion Hleb.
    rewrite Znat.Z2Nat.inj_neg.
    rewrite <- Znat.Zabs2Nat.abs_nat_nonneg by Omega.omega.
    rewrite <- Znat.Zabs2Nat.inj_0.
    apply Zabs.Zabs_nat_lt.
    Omega.omega.
Qed.

Ltac solve_integerToString_termination :=
  Coq.Program.Tactics.program_simpl;
  first [apply jhead_termination | apply jblock'_termination | apply jsplitf_termination];
  assumption.