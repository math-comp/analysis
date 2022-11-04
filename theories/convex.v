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

Lemma second_derivative_convexf_pt : forall t : prob,
    f (conv a b t) <= conv (f a) (f b) t.
Proof.
Admitted.

End twice_derivable_convex.
