From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly ssrnum.
Require Import nngnum.

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
rewrite /norm nng_le_maxl !(le_trans (ler_norm_add _ _)) ?ler_add//;
by rewrite comparable_le_maxr ?lexx ?orbT// real_comparable.
Qed.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Proof.
case: x => x1 x2 /eqP; rewrite eq_le nng_le_maxl 2!normr_le0 -andbA/=.
by case/and3P => /eqP -> /eqP ->.
Qed.

Lemma normMn x n : norm (x *+ n) = (norm x) *+ n.
Proof. by rewrite /norm pairMnE -mulr_natl maxr_pmulr ?mulr_natl ?normrMn. Qed.

Lemma normrN x : norm (- x) = norm x.
Proof. by rewrite /norm/= !normrN. Qed.

Definition normedZmodMixin :
  @Num.normed_mixin_of R [zmodType of U * V] (Num.NumDomain.class R) :=
  @Num.NormedMixin _ _ _ norm normD norm_eq0 normMn normrN.

Canonical normedZmodType := NormedZmodType R (U * V) normedZmodMixin.

Lemma prod_normE (x : normedZmodType) : `|x| = Num.max `|x.1| `|x.2|.
Proof. by []. Qed.

End ProdNormedZmodule.

Module Exports.
Canonical normedZmodType.
Definition prod_normE := @prod_normE.
End Exports.

End ProdNormedZmodule.
Export ProdNormedZmodule.Exports.
