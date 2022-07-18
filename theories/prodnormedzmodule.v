From HB Require Import structures.
From mathcomp Require Import all_ssreflect fingroup ssralg poly ssrnum.
Require Import signed.

(******************************************************************************)
(* This file equips the product of two normedZmodTypes with a canonical       *)
(* normedZmodType structure. It is a short file that has been added here for  *)
(* convenience during the rebase of MathComp-Analysis on top of MathComp 1.1. *)
(* The contents is likely to be moved elsewhere.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Module ProdNormedZmodule.
Section ProdNormedZmodule.
Context {R : numDomainType} {U V : normedZmodType R}.

Definition norm (x : U * V) : R := Num.max `|x.1| `|x.2|.

Lemma normD x y : norm (x + y) <= norm x + norm y.
Proof.
rewrite /norm num_le_maxl !(le_trans (ler_norm_add _ _)) ?ler_add//;
by rewrite comparable_le_maxr ?lexx ?orbT// real_comparable.
Qed.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Proof.
case: x => x1 x2 /eqP; rewrite eq_le num_le_maxl 2!normr_le0 -andbA/=.
by case/and3P => /eqP -> /eqP ->.
Qed.

Lemma normMn x n : norm (x *+ n) = (norm x) *+ n.
Proof. by rewrite /norm pairMnE -mulr_natl maxr_pmulr ?mulr_natl ?normrMn. Qed.

Lemma normrN x : norm (- x) = norm x.
Proof. by rewrite /norm/= !normrN. Qed.

#[export]
HB.instance Definition _ := Num.Zmodule_IsNormed.Build R (U * V)%type
  normD norm_eq0 normMn normrN.

Lemma prod_normE (x : [the normedZmodType R of (U * V)%type]) :
  `|x| = Num.max `|x.1| `|x.2|.
Proof. by []. Qed.

End ProdNormedZmodule.

Module Exports.
HB.reexport.
Definition prod_normE := @prod_normE.
End Exports.

End ProdNormedZmodule.
Export ProdNormedZmodule.Exports.
