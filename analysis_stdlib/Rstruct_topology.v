(**md**************************************************************************)
(* # Compatibility with the real numbers of Coq                               *)
(*                                                                            *)
(* Lemmas about continuity                                                    *)
(******************************************************************************)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
Require Import Rtrigo1 Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum archimedean.
From mathcomp Require Import boolp classical_sets reals interval_inference.
From mathcomp Require Export Rstruct.
From mathcomp Require Import topology.
(* The following line is for RexpE. *)
From mathcomp Require normedtype sequences.
(* The following line is for RlnE. *)
From mathcomp Require exp.

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

Module RexpE.
Import normedtype sequences.

(* proof by comparing the defining power series *)
Lemma RexpE (x : R) : Rtrigo_def.exp x = expR x.
Proof.
apply/esym; rewrite /exp /exist_exp; case: Alembert_C3 => y.
rewrite /Pser /infinite_sum /= => exp_ub.
rewrite /expR /exp_coeff /series/=; apply: (@cvg_lim R^o) => //.
rewrite -cvg_shiftS /=; apply/cvgrPdist_lt => /= e /RltP /exp_ub[N Nexp_ub].
near=> n.
have nN : (n >= N)%coq_nat by apply/ssrnat.leP; near: n; exact: nbhs_infty_ge.
move: Nexp_ub => /(_ _ nN) /[!RdistE] /RltP /=.
rewrite distrC sum_f_R0E; congr (`| _ - _ | < e).
by apply: eq_bigr=> k _; rewrite RinvE RpowE mulrC factE INRE.
Unshelve. all: by end_near. Qed.

End RexpE.

Definition RexpE := RexpE.RexpE.

Lemma RlnE (x : R) : Rpower.ln x = exp.ln x.
Proof.
rewrite /Rpower.ln /Rln.
have [xle0|xgt0] := leP x 0.
  by case: Rlt_dec => //= /[dup] /RltP + ?; rewrite exp.ln0// ltNge xle0.
case: (Rlt_dec 0 x) => [/= ? | /RltP/[!xgt0]//].
by case: ln_exists => y ->; rewrite RexpE exp.expRK.
Qed.
