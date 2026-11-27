(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order finmap algebra.

(**md**************************************************************************)
(* # Compatibility layer with recent MathComp versions                        *)
(*                                                                            *)
(* This files contains lemmas and definitions recently added in mathcomp,     *)
(* in order to be able to compile analysis with older versions of mathcomp.   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(**************************)
(* MathComp 2.7 additions *)
(**************************)

(* PR 1654 *)

HB.mixin Record ZmodQuotient_isLmodQuotient (R : pzRingType) T eqT
  (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (scaleT : R -> T -> T)
  (Q : Type) of ZmodQuotient T eqT zeroT oppT addT Q & GRing.Lmodule R Q := {
  pi_scaler : forall a, {morph \pi_Q%qT : x / scaleT a x >-> a *: x}
}.

#[short(type="lmodQuotType")]
HB.structure Definition LmodQuotient R T eqT zeroT oppT addT scaleT :=
  {Q of ZmodQuotient_isLmodQuotient R T eqT zeroT oppT addT scaleT Q &
   ZmodQuotient T eqT zeroT oppT addT Q & GRing.Lmodule R Q }.

Section LModQuotient.
Context {R : pzRingType} {T : Type} (eqT : rel T)
  (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (scaleT : R -> T -> T).
Implicit Type zqT : LmodQuotient.type eqT zeroT oppT addT scaleT.

Canonical pi_scale_quot_morph zqT a := PiMorph1 (@pi_scaler _ _ _ _ _ _ _ zqT a).

End LModQuotient.

Section PiLinear.
Context {R : pzRingType} {L : lmodType R} (equivL : rel L) (zeroL : L)
  (Q : @lmodQuotType R L equivL zeroL -%R +%R *:%R).

Lemma pi_is_linear : linear \pi_Q%qT.
Proof. by move=> a x y /=; rewrite !piE. Qed.

HB.instance Definition _ := GRing.isLinear.Build R L Q _ \pi_Q%qT pi_is_linear.

End PiLinear.

HB.factory Record SubmodClosed_isZmodClosed
  (R : pzRingType) (L : lmodType R) (P : {pred L}) of GRing.SubmodClosed R P :=
  {}.

HB.builders Context R L P of SubmodClosed_isZmodClosed R L P.

Lemma submodClosedB : oppr_closed P.
Proof. by move=> x xP; rewrite -scaleN1r; apply: rpredZ. Qed.

HB.instance Definition _ := GRing.isOppClosed.Build L P submodClosedB.
HB.end.

Module Quotient.
Export Quotient.

Section LmodQuotient.
Context {R : pzRingType} {L : lmodType R} (P : submodClosed L).

Definition Pzmod : {pred _} := P.
HB.instance Definition _ := GRing.SubmodClosed.on Pzmod.
HB.instance Definition _ := @SubmodClosed_isZmodClosed.Build R L Pzmod.

Definition zmodquot := (quot Pzmod).

Definition scale a := lift_op1 zmodquot ( *:%R a).

Lemma pi_scale a : {morph \pi : x / a *: x >-> scale a x}%qT.
Proof.
move=> x; unlock scale; apply/eqP; rewrite piE equivE.
by rewrite -scalerBr rpredZ// idealrBE reprK.
Qed.

Canonical pi_scale_morph a := PiMorph1 (pi_scale a).

Let scalerA a b f : scale a (scale b f) = scale (a * b) f.
Proof. by rewrite -[f]reprK !piE scalerA. Qed.

Let scale1r : left_id 1 scale.
Proof. by move=> f; rewrite -[f]reprK !piE scale1r. Qed.

Let scalerDr : right_distributive scale +%R.
Proof. by move=> a f g; rewrite -[f]reprK -[g]reprK !piE scalerDr. Qed.

Let scalerDl f : {morph scale^~ f: a b / a + b}.
Proof. by move=> a b; rewrite -[f]reprK !piE scalerDl. Qed.

#[export]
HB.instance Definition _ := ZmodQuotient.on zmodquot.
#[export]
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R zmodquot scalerA scale1r scalerDr scalerDl.
#[export]
HB.instance Definition _ :=
  ZmodQuotient_isLmodQuotient.Build R L (equiv Pzmod) 0 -%R +%R *:%R zmodquot pi_scale.

End LmodQuotient.
Module Exports. HB.reexport. End Exports.
End Quotient.

Export Quotient.Exports.

(* / PR 1654 *)
