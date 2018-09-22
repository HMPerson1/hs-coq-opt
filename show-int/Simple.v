(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Peano.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require GHC.Real.
Require GHC.Wf.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

Require GHC.Nat.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Program Definition showInt : GHC.Num.Integer -> GHC.Base.String :=
          fun i =>
            let digit2char : nat -> GHC.Char.Char :=
              fun x =>
                let y := GHC.Real.fromIntegral x in
                GHC.Char.chr (y GHC.Num.+ GHC.Base.ord (GHC.Char.hs_char__ "0")) in
            let go : nat -> GHC.Base.String -> GHC.Base.String :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_2__ arg_3__ => arg_2__) _ (fun arg_2__
                             arg_3__
                             go =>
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
            | Lt =>
                cons (GHC.Char.hs_char__ "-") (go (GHC.Num.fromInteger (GHC.Num.negate i)) nil)
            | Eq => GHC.Base.hs_string__ "0"
            | Gt => go (GHC.Num.fromInteger i) nil
            end.

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt cons nat nil pair Coq.Init.Peano.lt
     GHC.Base.String GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.ord GHC.Char.Char
     GHC.Char.chr GHC.Num.Integer GHC.Num.fromInteger GHC.Num.negate GHC.Num.op_zp__
     GHC.Real.divMod GHC.Real.fromIntegral GHC.Wf.wfFix2
*)
