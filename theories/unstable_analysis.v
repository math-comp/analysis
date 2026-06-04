(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *) 
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat finmap ssralg ssrnum ssrint.
From mathcomp Require Import vector archimedean interval complex.
From mathcomp.classical Require Export unstable.

(**md**************************************************************************)
(* # MathComp extra                                                           *)
(*                                                                            *)
(* This files contains lemmas that should eventually be backported            *)
(* to mathcomp. These lemmas may change before being backported to mathcomp,  *)
(* don't use anything in this file outside of Analysis. For this same reason, *)
(* nothing in this file should be mentionned in the changelog.                *)
(* Once a result is backported to mathcomp, please move it to mathcomp_extra.v*)
(* and mention it in the changelog.                                           *)
(******************************************************************************)

Attributes warn(note="The unstable_analysis.v file should only be used inside analysis.",
  cats="internal-analysis").

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope complex_scope.
Local Open Scope ring_scope.

Notation  "f %:Rfun" := (f : (Rcomplex _) -> (Rcomplex _))
  (at level 5,  format "f %:Rfun")  : complex_scope.

Notation  "v %:RC" :=   (v : (Rcomplex _))
  (at level 5, format "v %:RC")  : complex_scope.

(* TODO: backport to real-closed *)
Section complex_extras.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt. 
Local Notation C := (Rcomplex R).

Import Normc.
Import Num.Def.
Import complex.

(*TODO : rename scale regular and put there*)
Lemma scalecE (w v: C^o) : v *: w = v * w.
Proof. by []. Qed.

Lemma scalerc (h : R) (c : C) : h *: (c : Rcomplex R) = h%:C * c.
Proof.
case : c => x y.
by rewrite /(real_complex _) /(_ *: _) /( _ * _) /= /= /scalec !mul0r subr0 addr0.
Qed.

(* FIXME: unused *)
Lemma normcr (x : R) : normc (x%:C) = normr x.
Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.

Lemma Im_mul (x : R) : x *i = x%:C * 'i%C.
Proof. by simpc. Qed.

Lemma mulrnc (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma complexA (h : C^o) : h%:A = h.
Proof. by rewrite scalecE mulr1. Qed.

Lemma normc_natmul (k : nat) : normc k%:R = k%:R :> R.
Proof. by rewrite mulrnc /= mul0rn expr0n addr0 sqrtr_sqr normr_nat. Qed.

Lemma normc_mulrn (x : C) k : normc (x *+ k) = (normc x) *+ k.
Proof.
by rewrite -mulr_natr normcM -[in RHS]mulr_natr normc_natmul.
Qed.

Lemma gt0_normc (r : C) : 0 < r -> r = (normc r)%:C.
Proof.
case: r => x y /= /andP[] /eqP -> x0.
by rewrite expr0n addr0 sqrtr_sqr gtr0_norm.
Qed.

Lemma gt0_realC (r : C) : 0 < r -> r = (Re r)%:C.
Proof. by case: r => x y /andP[] /eqP -> _. Qed.

Lemma ltc0E  (k : R): (0 < k%:C) = (0 < k).
Proof. by simpc. Qed.

Lemma ltc0P  (k : R): (0 < k%:C) <-> (0 < k).
Proof. by simpc. Qed.

Lemma ltcP  (k t: R): (t%:C < k%:C) <-> (t < k).
Proof. by simpc. Qed.

Lemma lecP  (k t: R): (t%:C <= k%:C) <-> (t <= k).
Proof. by simpc. Qed.

(* (*TBA algC *) *)
Lemma realC_gt0 (d : C) : 0 < d -> (0 < Re d :> R).
Proof. by rewrite ltcE => /andP [] //. Qed.

Lemma Creal_gtE (c d : C) : c < d -> (complex.Re c < complex.Re d).
Proof. by rewrite ltcE => /andP [] //. Qed.

Lemma realC_norm (b : R) : `|b%:C| = `|b|%:C.
Proof. by rewrite normc_def /= expr0n addr0 sqrtr_sqr. Qed.

Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (r s : R) : (r *i == s *i) = (r == s).
Proof. by apply/idP/idP => [/eqP[] ->//|/eqP ->]. Qed.

Lemma neqCr0 (r : R) : (r%:C != 0) = (r != 0).
Proof. by apply/negP/negP; rewrite ?eqCr. Qed.

Lemma real_normc_ler (x : C) :
  `|Re x| <= normc x.
Proof.
case: x => x y /=.
rewrite -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=.
by rewrite lerDl ?sqr_ge0.
Qed.

Lemma im_normc_ler (x : C) :
  `|Im x| <= normc x.
Proof.
case: x => x y /=.
rewrite -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=.
by rewrite lerDr ?sqr_ge0.
Qed.

Lemma realC_alg (a : R) : a *: (1%:RC) = a%:C.
Proof. by rewrite /GRing.scale/= mulr1 mulr0. Qed.

Lemma scalecV (h: R) (v: Rcomplex R):
  h != 0 -> v != 0 -> (h *: v)^-1 = h^-1 *: v^-1. (* scaleCV *)
Proof.
by move=> h0 v0; rewrite scalerc invrM // ?unitfE ?eqCr // mulrC  scalerc fmorphV.
Qed.

(* TODO: clean lemmas about scalec *)
Lemma scalerc_regular (h : R) (c : R[i]): h *: (c : Rcomplex R) = h%:C *: (c : C^o).
Proof.
by rewrite scalecE scalerc.
Qed.

Lemma scalec1 (h : R) : h *: (1 : C^o) = h%:C.
Proof.
by rewrite scalerc mulr1.
Qed.

End complex_extras.
