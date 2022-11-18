(* mathcomp analysis (c) 2022               *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions cardinality mathcomp_extra.
Require Import ereal reals signed topology prodnormedzmodule.
Require Import normedtype derive set_interval.
From HB Require Import structures.

(******************************************************************************)
(* This file provides properties of standard real-valued functions over real  *)
(* numbers (e.g., the continuity of the inverse of a continuous function).    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

(* vvv probability vvv *)
Reserved Notation "x %:pr" (at level 0, format "x %:pr").
Reserved Notation "p '.~'" (format "p .~", at level 5).

Module Prob.
Section prob.
Variable (R : numDomainType).
Record t := mk { p :> R ; Op1 : 0 <= p <= 1 }.
Definition O1 (p : t) := Op1 p.
Arguments O1 : simpl never.
End prob.
Module Exports.
Section exports.
Variables (R : numDomainType).
Canonical prob_subType := Eval hnf in [subType for @p R].
Local Notation prob := (t R).
Definition prob_eqMixin := [eqMixin of prob by <:].
Canonical prob_eqType := Eval hnf in EqType _ prob_eqMixin.
Definition prob_choiceMixin := [choiceMixin of prob by <:].
Canonical prob_choiceType := ChoiceType prob prob_choiceMixin.
Definition prob_porderMixin := [porderMixin of prob by <:].
Canonical prob_porderType := POrderType ring_display prob prob_porderMixin.
Lemma prob_ge0 (p : prob) : 0 <= Prob.p p.
Proof. by case: p => p /= /andP[]. Qed.
Lemma prob_le1 (p : prob) : Prob.p p <= 1.
Proof. by case: p => p /= /andP[]. Qed.
End exports.
Global Hint Resolve prob_ge0 : core.
Global Hint Resolve prob_le1 : core.
End Exports.
End Prob.
Export Prob.Exports.
Notation prob := Prob.t.
Notation "q %:pr" := (@Prob.mk _ q (@Prob.O1 _ _)).
Coercion Prob.p : prob >-> Num.NumDomain.sort.
(*  ^^^ probability ^^^ *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.

Variable R : realType.
Variables (f : R -> R) (a b : R).
Hypothesis ab : (a < b)%R.

Definition Df x: R := f^`() x.
Definition DDf x := f^`(2) x.

Hypothesis DDf_ge0 : forall x, a <= x <= b -> (0 <= DDf x)%R.

Let prob := Prob.t R.


Definition conv' (a b: R) (p:prob) : R := conv a b (Prob.p p).

Definition L (x : R) := (f a + (x - a) / (b - a) * (f b - f a))%R.

Lemma LE x : L x = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)%R.
Proof.
rewrite /L mulrBr [in LHS]addrA addrAC; congr (_ + _)%R.
rewrite -{1}(mul1r (f a)) -mulrBl; congr (_ * _)%R.
rewrite -(@mulrV _ (b-a)); last first.
  by move: ab; rewrite unitfE subr_eq0 lt_def => /andP [ba _].
by rewrite -mulrBl opprB addrA subrK.
Qed.

Lemma divrNN (x y: R): (- x) / (- y) = x / y.
Proof. by rewrite -[RHS]mulrNN -invrN. Qed.

Lemma sub_divC (x y c d: R): 
    (x - y) / (c - d) = (y - x) / (d - c).
Proof. by rewrite -divrNN !opprB. Qed.

Lemma convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x)%R ->
  forall t, f (conv' a b t) <= conv' (f a) (f b) t.
Proof.
move=> H t.
set p := (Prob.p t). set x := conv' a b t.
have : (a <= x <= b)%R.
  rewrite -(conv1 a b) -{1}(conv0 a b) /x le_conv // le_conv //.
  by apply/andP.
move/H; rewrite subr_ge0 => /le_trans. apply.
rewrite LE.
have -> : ((b - x) / (b - a) = 1 - p).
  rewrite /x sub_divC -/(factor b a _) /conv' conv_sym.
  by rewrite convK // gt_eqF.
have -> : ((x - a) / (b - a) = p).
  rewrite /x -/(factor a b _) /conv'.
  by rewrite convK // lt_eqF.
done.
Qed.

Variable pderivable : (R -> R) -> (R -> Prop) -> Prop.
Definition derive_pt (f: R -> R) (x: R) : R := f^`() x.
Let I := fun x0 => (a <= x0 <= b).
Hypothesis HDf : pderivable f I.

Lemma MVT_cor1_pderivable
     : forall (a b : R) (f : R -> R) (pr : pderivable f (fun x : R => a <= x <= b)),
    a < b ->
    exists (c : R) (Hc : a <= c <= b),
      f b - f a = derive_pt f c * (b - a) /\ a < c < b.
Proof.
Admitted.
(*use MVT in derive.v *)

Hypothesis DfE : forall (x : R) (Hx : I x), Df x = derive_pt f x.
Hypothesis DDfE : forall x (Hx : I x), DDf x = derive_pt Df x.

Lemma unitfB: forall (x y:R), x < y -> y - x \is a GRing.unit.
Proof.
  by move=> x y xy; rewrite unitfE subr_eq0 (gt_eqF xy).
Qed.

Lemma second_derivative_convexf_pt : forall t : prob,
    f (conv a b t) <= conv (f a) (f b) t.
Proof.
have note1 : forall x, 1 = (x - a) / (b - a) + (b - x) / (b - a).
  move=> x; rewrite -mulrDl addrC addrA subrK mulrV //.
  exact: unitfB.
have step1 : forall x, f x = (x - a) / (b - a) * f x + (b - x) / (b - a) * f x.
  by move=> x; rewrite -mulrDl -note1 mul1r.
apply /convexf_ptP => // x axb.
rewrite /L.
move: axb => /andP [].
rewrite le_eqVlt => /orP [/eqP -> _|].
  rewrite /L subrr 2!mul0r addr0 subrr. exact/lexx.
move=> ax.
rewrite le_eqVlt => /orP -[/eqP ->|].
  rewrite /L  mulrV ?mul1r; last exact/unitfB.
  rewrite (addrC (f a)) subrK subrr; exact/lexx.
move=> xb.
have {step1}step2 : L x - f x =
  (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
  (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)).
  rewrite {1}step1 {step1}.
  rewrite opprD addrA addrC addrA.
  rewrite LE //.
  rewrite -(mulrN _ (f x)).
  rewrite addrA. rewrite -mulrDr (addrC _ (f a)).
  rewrite -(mulrN _ (f x)) -addrA -mulrDr.
  rewrite addrC.
  rewrite -(opprK (f a - f x)) mulrN  opprB.
  congr (_ + _).
  - rewrite -!mulrA; congr (_ * _); rewrite mulrCA; congr (_ * _).
    by rewrite mulrCA mulrV ?mulr1 // unitfB //.
  - rewrite -!mulNr -!mulrA; congr (_ * _); rewrite mulrCA; congr (_ * _).
    by rewrite mulrCA mulrV ?mulr1 // unitfB //.
have [c2 [Ic2 Hc2]] : exists c2, (x < c2 < b /\ (f b - f x) / (b - x) = Df c2).
  have H : pderivable f (fun x0 => x <= x0 <= b).
(*    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
*)
    admit.
  case: (@MVT_cor1_pderivable x b f H xb) => c2 [Ic2 [H1 H2]].
  exists c2; split => //.
  rewrite H1  -mulrA mulrV ?mulr1; last exact/unitfB.
  rewrite DfE //.
  apply /andP. split.
    apply (@le_trans _ _ x); [exact/ltW | by move: Ic2 => /andP []].
  by case: (andP H2) => _ /ltW.
have [c1 [Ic1 Hc1]] : exists c1, (a < c1 < x /\ (f x - f a) / (x - a) = Df c1).
  have H : pderivable f (fun x0 => a <= x0 <= x).
(*    move=> z [z1 z2]; apply HDf; split => //.
    apply (@leR_trans x) => //; exact: ltRW.
*)
    admit.
  case: (@MVT_cor1_pderivable a x f H ax) => c1 [Ic1 [H1 H2]].
  exists c1; split => //.
  rewrite H1 -mulrA mulrV ?mulr1; last by exact/unitfB.
  rewrite DfE// . (*; last by move=> ?; exact: proof_derive_irrelevance.*)
  apply/andP. split.
  - by case: (andP H2) => /ltW.
  - apply (@le_trans _ _ x).
    by case: (andP H2) => _ /ltW.
    apply (@le_trans _ _ c2); apply/ltW; by case: (andP Ic2).
have c1c2 : c1 < c2 by apply (@lt_trans _ _ x); [case: (andP Ic1) | case: (andP Ic2)].
have {step2 Hc1 Hc2}step3 : (L x - f x =
  (b - x) * (x - a) * (c2 - c1) / (b - a) * ((Df c2 - Df c1) / (c2 - c1)))%R.
  rewrite {}step2 Hc2 Hc1 (mulrC (x - a)%R) -mulrBr -!mulrA.
  congr (_ * (_ * _)); rewrite mulrCA; congr (_ * _).
  rewrite mulrCA mulrV ?mulr1 //. exact/unitfB.
have [d [Id H]] : exists d, c1 < d < c2 /\ (Df c2 - Df c1) / (c2 - c1) = DDf d.
  have H : pderivable Df (fun x0 => c1 <= x0 <= c2)%R.
(*
    move=> z [z1 z2]; apply HDDf; split => //.
    - apply (@leR_trans c1) => //; by case: Ic1 => /ltRW.
    - apply (@leR_trans c2) => //; by case: Ic2 => _ /ltRW.
*)
    admit.
  case: (@MVT_cor1_pderivable c1 c2 Df H c1c2) => d [Id [H1 H2]].
  exists d; split => //.
  rewrite H1 -mulrA mulrV ?mulr1; last exact/unitfB.
  rewrite DDfE //.
  apply/andP. split.
  - apply (@le_trans _ _ c1); last by case: (andP Id) H1.
    by apply/ltW; case: (andP Ic1).
  - apply (@le_trans _ _ c2); last by case: (andP Ic2) => _ /ltW.
    by case: (andP H2) => _ /ltW.
rewrite {}step3 {}H.
apply/mulr_ge0; last first.
  apply /DDf_ge0 /andP; split.
    apply (@le_trans _ _ c1).
      apply/ltW; by case: (andP Ic1).
     by case: (andP Id) => /ltW.
  apply (@le_trans _ _ c2).
    by case: (andP Id) => _ /ltW.
  apply/ltW; by case: (andP Ic2).
apply/mulr_ge0; last by rewrite invr_ge0 subr_ge0 ltW.
apply/mulr_ge0; last first.
  by rewrite subr_ge0; case: (andP Id) => Id1 Id2; apply (@le_trans _ _ d); exact/ltW.
by apply/mulr_ge0; rewrite subr_ge0; exact/ltW.
Admitted.

End twice_derivable_convex.
