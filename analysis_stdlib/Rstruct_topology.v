(**md**************************************************************************)
(* # Compatibility with the real numbers of Coq                               *)
(*                                                                            *)
(* Lemmas about continuity                                                    *)
(******************************************************************************)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
Require Import Rtrigo1 Reals.
From mathcomp Require Import all_ssreflect ssralg poly mxpoly ssrnum.
From mathcomp Require Import archimedean.
From HB Require Import structures.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import reals itv.
From mathcomp Require Import topology.
From mathcomp Require Export Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope R_scope.
Local Open Scope ring_scope.

Section analysis_struct.

HB.instance Definition _ := PseudoMetric.copy R R^o.
HB.instance Definition _ := Pointed.copy R R^o.

(* TODO: express using ball?*)
Lemma continuity_pt_nbhs (f : R -> R) x :
  continuity_pt f x <->
  forall eps : {posnum R}, nbhs x (fun u => `|f u - f x| < eps%:num).
Proof.
split=> [fcont e|fcont _/RltP/posnumP[e]]; last first.
  have [_/posnumP[d] xd_fxe] := fcont e.
  exists d%:num; split; first by apply/RltP; have := [gt0 of d%:num].
  by move=> y [_ /RltP yxd]; apply/RltP/xd_fxe; rewrite /= distrC.
have /RltP egt0 := [gt0 of e%:num].
have [_ [/RltP/posnumP[d] dx_fxe]] := fcont e%:num egt0.
exists d%:num => //= y xyd; case: (eqVneq x y) => [->|xney].
  by rewrite subrr normr0.
apply/RltP/dx_fxe; split; first by split=> //; apply/eqP.
by have /RltP := xyd; rewrite distrC.
Qed.

Lemma continuity_pt_cvg (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof.
eapply iff_trans; first exact: continuity_pt_nbhs.
apply iff_sym.
have FF : Filter (f @ x)%classic.
  by typeclasses eauto.
  (*by apply fmap_filter; apply: @filter_filter' (locally_filter _).*)
case: (@fcvg_ballP _ _ (f @ x)%classic FF (f x)) => {FF}H1 H2.
(* TODO: in need for lemmas and/or refactoring of already existing lemmas (ball vs. Rabs) *)
split => [{H2} - /H1 {}H1 eps|{H1} H].
- have {H1} [//|_/posnumP[x0] Hx0] := H1 eps%:num.
  exists x0%:num => //= Hx0' /Hx0 /=.
  by rewrite /= distrC; apply.
- apply H2 => _ /posnumP[eps]; move: (H eps) => {H} [_ /posnumP[x0] Hx0].
  exists x0%:num => //= y /Hx0 /= {}Hx0.
  by rewrite /ball /= distrC.
Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_cvg. Qed.

Local Open Scope classical_set_scope.

Lemma continuity_pt_cvg' f x :
  continuity_pt f x <-> f @ x^' --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx. Qed.

Lemma continuity_pt_dnbhs f x :
  continuity_pt f x <->
  forall eps, 0 < eps -> x^' (fun u => `|f x - f u| < eps).
Proof.
by rewrite continuity_pt_cvg' -filter_fromP cvg_ballP -filter_fromP.
Qed.

Lemma nbhs_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  nbhs (f x) P -> continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_cvg; apply. Qed.

End analysis_struct.
