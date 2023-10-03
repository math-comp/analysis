Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import fsbigop cardinality set_interval.
From mathcomp Require Import Rstruct complex.
Require Import constructive_ereal reals signed topology normedtype ereal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Lemma ereal_nbhs_pinftyE (R : numFieldType) (A : set (\bar R)) :
   (\forall k \near +oo%E, A k) = (A +oo%E /\ \forall k \near +oo%R, A k%:E).
Proof.
apply/propeqP; split; last first.
  by move=> [Ay [M [Mreal AM]]]; exists M; split=> // -[r | |]//; apply: AM.
move=> [M [Mreal AM]]; split; first exact: AM.
by exists M; split=> // y My; apply: AM.
Qed.

Definition C := R[i].

Lemma ereal_nbhs_nbhs :
  ereal_nbhs +oo (`](0 : \bar C), +oo]%classic) /\
  ~ ereal_nbhs +oo (ereal_nbhs^~ `](0 : \bar C), +oo]%classic).
Proof.
have [i Ni_eq1 iNreal] : (exists2 i : C, (`|i| = 1)%R & i \isn't Num.real).
  by exists 'i; rewrite ?normCi// nonRealCi.
have NiV2_lt1 : (`|i / 2| < 1)%R.
  by rewrite normf_div Ni_eq1 gtr0_norm// mul1r invf_lt1// ltr_addl.
rewrite ![ereal_nbhs _ _]ereal_nbhs_pinftyE.
split.
  split=> //=; first by rewrite in_itv/= lt0y lexx.
  exists 0%R; split=> // x x_gt0; rewrite in_itv//= lte_fin x_gt0//=.
  by rewrite real_leey/= gtr0_real.
move=> [_ [M [Mreal]]]/(_ (M + 1)%R _)[]; first by rewrite ltr_addl.
move=> x /= x_gt0/=.
have x_neq0 : x != 0%R by rewrite gt_eqF.
have x_real: x \is Num.real by rewrite gtr0_real.
move=> /(_ (M + 1 + x * (i / 2))%R) /=.
rewrite opprD addNKr normrN normrM gtr0_norm//.
rewrite -ltr_pdivl_mull// mulVf ?gt_eqF// => /(_ NiV2_lt1).
suff: (M + 1 + x * (i / 2))%R \isn't Num.real.
  apply: contraNnot; move: (_ + _)%R => y.
  by rewrite in_itv/= => /andP[/gtr0_real].
rewrite rpredDl/=; last by rewrite rpredD// rpred1.
by rewrite fpredMl//= fpred_divr// rpred_nat.
Qed.
