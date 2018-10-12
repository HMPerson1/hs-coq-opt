Require Omega.
Import BinInt.

Lemma showInt_go_termination: forall i : GHC.Num.Integer,
  _GHC.Base.==_ i 0%Z = false ->
  _GHC.Base.<_ i 0%Z = false ->
  BinInt.Z.abs_nat (i / 10) < BinInt.Z.abs_nat i.
Proof.
  intros.
  assert (0 < i)%Z. {
    destruct i; try Omega.omega; Coq.Program.Tactics.program_simpl.
    apply Pos2Z.is_pos.
  }
  apply Zabs.Zabs_nat_lt. split.
  - apply Zdiv.Z_div_pos; Omega.omega.
  - apply Zdiv.Z_div_lt; Omega.omega.
Qed.

Ltac solve_showInt_termination :=
  Coq.Program.Tactics.program_simpl; apply showInt_go_termination; assumption.
