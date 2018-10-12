(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinInt.
Require Coq.Init.Peano.
Require GHC.Base.
Require GHC.Char.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Require GHC.Wf.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Midamble *)

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

(* Converted value declarations: *)

Program Definition showInt : GHC.Num.Integer -> GHC.Base.String :=
          fun i =>
            let digit2char : GHC.Num.Integer -> GHC.Char.Char :=
              fun x =>
                let y := GHC.Real.fromIntegral x in
                GHC.Char.chr (y GHC.Num.+ GHC.Base.ord (GHC.Char.hs_char__ "0")) in
            let go : GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun i s => BinInt.Z.abs_nat i) _ (fun i s go =>
                               if Bool.Sumbool.sumbool_of_bool (i GHC.Base.== #0) then s else
                               if Bool.Sumbool.sumbool_of_bool (i GHC.Base.< #0)
                               then GHC.Err.error (GHC.Base.hs_string__ "go {< 0}") else
                               let 'pair tens ones := GHC.Real.divMod i #10 in
                               go tens (cons (digit2char ones) s)) in
            match GHC.Base.compare i #0 with
            | Lt => cons (GHC.Char.hs_char__ "-") (go (GHC.Num.negate i) nil)
            | Eq => GHC.Base.hs_string__ "0"
            | Gt => go i nil
            end.
Solve Obligations with (solve_showInt_termination).

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt cons nil pair BinInt.Z.abs_nat
     Coq.Init.Peano.lt GHC.Base.String GHC.Base.compare GHC.Base.op_zeze__
     GHC.Base.op_zl__ GHC.Base.ord GHC.Char.Char GHC.Char.chr GHC.Err.error
     GHC.Num.Integer GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__
     GHC.Real.divMod GHC.Real.fromIntegral GHC.Wf.wfFix2
*)
