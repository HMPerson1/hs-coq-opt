
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require Prelude.
Require Simple.
Require GhcShow.
Import BinInt.

Example Simple_show_123: Simple.showInt 321%Z = GHC.Base.hs_string__ "321".
Proof.
  simpl.
  unfold Simple.showInt.
  unfold Wf.wfFix2.
  unfold Wf.wfFix1.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  reflexivity.
Qed.

Example show_321: GhcShow.showInt 321%Z = Simple.showInt 321%Z.
Proof.
  unfold Simple.showInt.
  unfold GhcShow.showInt.
  unfold GhcShow.integerToString.
  unfold Wf.wfFix2.
  unfold Wf.wfFix1.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  reflexivity.
Qed.

Example show_n456: GhcShow.showInt (-456)%Z = Simple.showInt (-456)%Z.
Proof.
  unfold Simple.showInt.
  unfold GhcShow.showInt.
  unfold GhcShow.integerToString.
  unfold Wf.wfFix2.
  unfold Wf.wfFix1.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  rewrite ! Coq.Program.Wf.WfExtensionality.fix_sub_eq_ext.
  simpl.
  reflexivity.
Qed.
