(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require GHC.Real.
Require GHC.Wf.
Require Proofs.Termination.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

Import Omega.
Require Import ZArith.

Axiom __CHEAT__ : False.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Program Definition showInt : GHC.Num.Integer -> GHC.Base.String :=
          fun i =>
            let digit2char : GHC.Num.Integer -> GHC.Char.Char :=
              GHC.Char.chr GHC.Base.∘
              ((fun arg_0__ => arg_0__ GHC.Num.+ GHC.Base.ord (GHC.Char.hs_char__ "0"))
               GHC.Base.∘
               GHC.Num.fromInteger) in
            let go : GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
              GHC.Wf.wfFix2 lt (fun arg_2__ arg_3__ => Z.abs_nat arg_2__) _
                            (fun arg_2__ arg_3__ go =>
                               match arg_2__, arg_3__ with
                               | num_4__, s =>
                                   if Bool.Sumbool.sumbool_of_bool (num_4__ GHC.Base.== #0) then s else
                                   match arg_2__, arg_3__ with
                                   | i, s =>
                                       let 'pair tens ones := GHC.Real.divMod i #10 in
                                       go tens (cons (digit2char ones) s)
                                   end
                               end) in
            match GHC.Base.compare i #0 with
            | Lt => cons (GHC.Char.hs_char__ "-") (go (GHC.Num.negate i) nil)
            | Eq => GHC.Base.hs_string__ "0"
            | Gt => go i nil
            end.
Next Obligation.
destruct (Z.compare arg_2__ 0) eqn:Heq.
- rewrite Z.compare_eq_iff in Heq. rewrite Heq in H. rewrite Base.Eq_reflI in H; inversion H.
- rewrite Z.compare_lt_iff in Heq. destruct arg_2__; inversion Heq.
  rewrite <- Pos2Z.opp_pos.
  assert (forall x, Z.abs_nat (- x) = Z.abs_nat x) as Z_abs_nat_opp. {
    intros x.
    rewrite Zabs2Nat.abs_nat_spec.
    rewrite Z.abs_opp.
    rewrite <- Zabs2Nat.abs_nat_spec.
    reflexivity.
  }
  destruct (((Z.pos p) mod 10 =? 0)%Z) eqn:Heq2.
  * rewrite Z.eqb_eq in Heq2. rewrite Zdiv.Z_div_zero_opp_full by assumption.
    rewrite Z_abs_nat_opp, Z_abs_nat_opp.
    apply Zabs2Nat.inj_lt.
    + apply Zdiv.Z_div_pos. { omega. } { apply Zle_0_pos. }
    + apply Zle_0_pos.
    + apply Zdiv.Z_div_lt. { omega. } { apply Zgt_pos_0. }
  * rewrite Z.eqb_neq in Heq2. rewrite Zdiv.Z_div_nz_opp_full by assumption.
    assert (forall x, (- x - 1 = - (x+1))%Z). { intros x. ring. } rewrite H0.
    rewrite Z_abs_nat_opp, Z_abs_nat_opp.
    apply Zabs2Nat.inj_lt.
    + assert (forall x, 0 <= x -> 0 <= x+1)%Z. { intros. omega. } apply H1. apply Zdiv.Z_div_pos. { omega. } { apply Zle_0_pos. }
    + apply Zle_0_pos.
    + exfalso. apply __CHEAT__.
- rewrite Z.compare_gt_iff in Heq.
  apply Zabs2Nat.inj_lt. { apply Z_div_pos; omega. } { omega. }
  apply Zdiv.Z_div_lt; omega.
Qed.
(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt cons nil pair GHC.Base.String
     GHC.Base.compare GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.ord
     GHC.Char.Char GHC.Char.chr GHC.Num.Integer GHC.Num.fromInteger GHC.Num.negate
     GHC.Num.op_zp__ GHC.Real.divMod GHC.Wf.wfFix2 Proofs.Termination.NonNeg
*)
