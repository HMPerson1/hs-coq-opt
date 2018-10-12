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
(* Converted value declarations: *)

Definition quotRemInteger
   : GHC.Num.Integer ->
     GHC.Num.Integer -> (GHC.Num.Integer * GHC.Num.Integer)%type :=
  fun a b => let 'pair q r := GHC.Real.divMod a b in pair q r.

Program Definition integerToString
           : GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
          fun n0 cs0 =>
            let jblock'
             : GHC.Num.Int -> GHC.Num.Int -> GHC.Base.String -> GHC.Base.String :=
              GHC.Wf.wfFix3 Coq.Init.Peano.lt (fun d n cs => BinInt.Z.abs_nat d) _ (fun d
                             n
                             cs
                             jblock' =>
                               let 'pair q r := GHC.Real.divMod n #10 in
                               if Bool.Sumbool.sumbool_of_bool (d GHC.Base.== #1)
                               then let 'c := GHC.Base.unsafeChr (GHC.Base.ord (GHC.Char.hs_char__ "0")
                                                                  GHC.Num.+
                                                                  n) in
                                    cons c cs else
                               if Bool.Sumbool.sumbool_of_bool (d GHC.Base.< #1)
                               then GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__ "jblock' {< 1}") else
                               let 'c := GHC.Base.unsafeChr (GHC.Base.ord (GHC.Char.hs_char__ "0") GHC.Num.+
                                                             r) in
                               jblock' (d GHC.Num.- #1) q (cons c cs)) in
            let jblock := jblock' #18 in
            let jhead : GHC.Num.Int -> GHC.Base.String -> GHC.Base.String :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun n cs => BinInt.Z.abs_nat n) _ (fun n
                             cs
                             jhead =>
                               let 'pair q r := GHC.Real.divMod n #10 in
                               if Bool.Sumbool.sumbool_of_bool (n GHC.Base.< #10)
                               then let 'c := GHC.Base.unsafeChr (GHC.Base.ord (GHC.Char.hs_char__ "0")
                                                                  GHC.Num.+
                                                                  n) in
                                    cons c cs else
                               let 'c := GHC.Base.unsafeChr (GHC.Base.ord (GHC.Char.hs_char__ "0") GHC.Num.+
                                                             r) in
                               jhead q (cons c cs)) in
            let jprintb : list GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
              fix jprintb arg_20__ arg_21__
                    := match arg_20__, arg_21__ with
                       | nil, cs => cs
                       | cons n ns, cs =>
                           let 'pair q' r' := quotRemInteger n #1000000000000000000 in
                           let r := GHC.Num.fromInteger r' in
                           let q := GHC.Num.fromInteger q' in jblock q (jblock r (jprintb ns cs))
                       end in
            let jprinth : list GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
              fun arg_29__ arg_30__ =>
                match arg_29__, arg_30__ with
                | cons n ns, cs =>
                    let 'pair q' r' := quotRemInteger n #1000000000000000000 in
                    let r := GHC.Num.fromInteger r' in
                    let q := GHC.Num.fromInteger q' in
                    if Bool.Sumbool.sumbool_of_bool (q GHC.Base.> #0)
                    then jhead q (jblock r (jprintb ns cs))
                    else jhead r (jprintb ns cs)
                | nil, _ => GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__ "jprinth []")
                end in
            let jsplitb : GHC.Num.Integer -> list GHC.Num.Integer -> list GHC.Num.Integer :=
              fix jsplitb arg_39__ arg_40__
                    := match arg_39__, arg_40__ with
                       | _, nil => nil
                       | p, cons n ns =>
                           let 'pair q r := quotRemInteger n p in
                           cons q (cons r (jsplitb p ns))
                       end in
            let jsplith : GHC.Num.Integer -> list GHC.Num.Integer -> list GHC.Num.Integer :=
              fun arg_46__ arg_47__ =>
                match arg_46__, arg_47__ with
                | p, cons n ns =>
                    let 'pair q r := quotRemInteger n p in
                    if Bool.Sumbool.sumbool_of_bool (q GHC.Base.> #0)
                    then cons q (cons r (jsplitb p ns))
                    else cons r (jsplitb p ns)
                | _, nil => GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__ "jsplith: []")
                end in
            let jsplitf : GHC.Num.Integer -> GHC.Num.Integer -> list GHC.Num.Integer :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun p n =>
                               BinInt.Z.abs_nat n - BinInt.Z.abs_nat (p - 1)) _ (fun p n jsplitf =>
                               if Bool.Sumbool.sumbool_of_bool (p GHC.Base.<= #1)
                               then GHC.Err.errorWithoutStackTrace (GHC.Base.hs_string__ "jsplitf {<= 1}") else
                               if Bool.Sumbool.sumbool_of_bool (p GHC.Base.> n) then cons n nil else
                               jsplith p (jsplitf (p GHC.Num.* p) n)) in
            let integerToString' : GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String :=
              fun n cs =>
                if Bool.Sumbool.sumbool_of_bool (n GHC.Base.< #1000000000000000000)
                then jhead (GHC.Num.fromInteger n) cs else
                jprinth (jsplitf (#1000000000000000000 GHC.Num.* #1000000000000000000) n) cs in
            if Bool.Sumbool.sumbool_of_bool (n0 GHC.Base.< #0)
            then cons (GHC.Char.hs_char__ "-") (integerToString' (GHC.Num.negate n0)
                       cs0) else
            integerToString' n0 cs0.
Solve Obligations with (solve_integerToString_termination).

Definition showInt : GHC.Num.Integer -> GHC.Base.String :=
  fun i => integerToString i (GHC.Base.hs_string__ "").

(* External variables:
     Bool.Sumbool.sumbool_of_bool cons list nil op_zm__ op_zt__ pair BinInt.Z.abs_nat
     Coq.Init.Peano.lt GHC.Base.String GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.ord GHC.Base.unsafeChr
     GHC.Err.errorWithoutStackTrace GHC.Num.Int GHC.Num.Integer GHC.Num.fromInteger
     GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Real.divMod
     GHC.Wf.wfFix2 GHC.Wf.wfFix3
*)
