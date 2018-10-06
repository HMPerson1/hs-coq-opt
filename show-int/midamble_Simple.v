Require Omega.
Import BinInt.

Lemma showInt_go_termination: forall arg_2__ : GHC.Num.Integer,
  _GHC.Base.==_ arg_2__ 0%Z = false ->
  _GHC.Base.<_ arg_2__ 0%Z = false ->
  BinInt.Z.abs_nat (arg_2__ / 10) < BinInt.Z.abs_nat arg_2__.
Proof.
  intros.
  assert (0 < arg_2__)%Z. {
    induction arg_2__; try Omega.omega; Coq.Program.Tactics.program_simpl.
    apply Pos2Z.is_pos.
  }
  apply Zabs.Zabs_nat_lt. split.
  - apply Zdiv.Z_div_pos; Omega.omega.
  - apply Zdiv.Z_div_lt; Omega.omega.
Qed.

Ltac solve_showInt_termination :=
  Coq.Program.Tactics.program_simpl; apply showInt_go_termination; assumption.
