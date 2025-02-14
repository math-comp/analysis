(* mathcomp analysis (c) 2020 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect fingroup ssralg poly ssrnum.
From mathcomp Require Import all_classical.
From mathcomp Require Import itv.

(**md**************************************************************************)
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

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
HB.instance Definition _ := gen_eqMixin {linear U -> V | s}.
HB.instance Definition _ := gen_choiceMixin {linear U -> V | s}.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : GRing.Scale.law R V).
HB.instance Definition _ :=
  isPointed.Build {linear U -> V | GRing.Scale.Law.sort s} \0.
End Linear2.

Module ProdNormedZmodule.
Section ProdNormedZmodule.
Context {R : numDomainType} {U V : normedZmodType R}.

Definition norm (x : U * V) : R := Num.max `|x.1| `|x.2|.

Lemma normD x y : norm (x + y) <= norm x + norm y.
Proof.
rewrite /norm num_ge_max !(le_trans (ler_normD _ _)) ?lerD//;
by rewrite comparable_le_max ?lexx ?orbT// real_comparable.
Qed.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Proof.
case: x => x1 x2 /eqP; rewrite eq_le num_ge_max 2!normr_le0 -andbA/=.
by case/and3P => /eqP -> /eqP ->.
Qed.

Lemma normMn x n : norm (x *+ n) = (norm x) *+ n.
Proof. by rewrite /norm pairMnE -mulr_natl maxr_pMr ?mulr_natl ?normrMn. Qed.

Lemma normrN x : norm (- x) = norm x.
Proof. by rewrite /norm/= !normrN. Qed.

#[export]
HB.instance Definition _ := Num.Zmodule_isNormed.Build R (U * V)%type
  normD norm_eq0 normMn normrN.

Lemma prod_normE (x : U * V) : `|x| = Num.max `|x.1| `|x.2|.
Proof. by []. Qed.

End ProdNormedZmodule.

Module Exports.
HB.reexport.
Definition prod_normE := @prod_normE.
End Exports.

End ProdNormedZmodule.
Export ProdNormedZmodule.Exports.
