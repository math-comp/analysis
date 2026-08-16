(**md**************************************************************************)
(* # Compatibility with the real numbers of Stdlib                            *)
(*                                                                            *)
(* Extension to Rstruct.v (lemmas about continuity)                           *)
(******************************************************************************)

From Stdlib Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
From Stdlib Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
From Stdlib Require Import Rtrigo1 Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum archimedean.
From mathcomp Require Import interval arithmetic_tactic.
From mathcomp Require Import boolp classical_sets reals interval_inference.
From mathcomp Require Export Rstruct.
From mathcomp Require Import topology.
(* The following line is for RexpE and RcosE. *)
From mathcomp Require normedtype sequences.
(* The following line is for RlnE. *)
From mathcomp Require exp.
(* The following line is for RcosE, PIE and RsinE. *)
From mathcomp Require trigo.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
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

(* PRed to mathcomp (#1637) *)
Section big_nat_dvdn.

Lemma iotaS (m n : nat) : iota m n.+1 = rcons (iota m n) (m + n)%N.
Proof. by rewrite -addn1 iotaD cats1. Qed.

Lemma index_iotaS (m n : nat) :
  (m <= n)%N -> index_iota m n.+1 = rcons (index_iota m n) n.
Proof. by move=> ?; rewrite /index_iota subSn// iotaS subnKC. Qed.

Lemma big_nat_recr_op (R : Type) (idx : R) (op : R -> R -> R)
  (n m : nat) (P : pred nat) (F : nat -> R) :
  (m <= n)%N ->
  let idx' := if P n then op (F n) idx else idx in
  \big[op/idx]_(m <= i < n.+1 | P i) F i = \big[op/idx']_(m <= i < n | P i) F i.
Proof. by move=> ?; rewrite index_iotaS// big_rcons_op. Qed.

Lemma big_nat_dvdn (R : Type) (idx : R) (op : R -> R -> R)
  (n d : nat) (F : nat -> R) :
  \big[op/idx]_(0 <= i < n | d.+1 %| i) F i =
  \big[op/idx]_(0 <= i < (n + d) %/ d.+1) F (d.+1 * i)%N.
Proof.
elim: n idx.
  by move=> ?; rewrite divn_small// !big_nil.
move=> n IHn idx.
rewrite addSn divnS// -addnS dvdn_addl// big_nat_recr_op// IHn.
case/boolP: (d.+1 %| n) => H /=.
  rewrite add1n big_nat_recr_op//.
  rewrite divnDl// (@divn_small d)// addn0.
  congr bigop.body; congr op; congr F.
  by rewrite muln_divCA// divnn muln1.
by rewrite add0n.
Qed.

End big_nat_dvdn.

Module RcosE.
Import normedtype sequences.
Local Open Scope classical_set_scope.

Lemma RcosE (x : R) : Rtrigo_def.cos x = trigo.cos x.
Proof.
apply/esym; rewrite /cos.
case: exist_cos => y.
rewrite /cos_in /cos_n /infinite_sum/=.
set G : nat -> R^o := (G in sum_f_R0 G).
move=> cos_ub.
have Gy : series G x @[x --> \oo] --> y.
  rewrite -cvg_shiftS/=; apply/cvgrPdist_lt => /= e /RltP /cos_ub[N Ncos_ub].
  near=> n.
  have nN : (n >= N)%coq_nat by apply/ssrnat.leP; near: n; exact: nbhs_infty_ge.
  move: Ncos_ub => /(_ _ nN) /[!RdistE] /RltP /=.
  by rewrite /G distrC sum_f_R0E.
rewrite trigo.cosE /series/=; apply: (@cvg_lim R^o) => //.
evar (F : nat -> R); rewrite [X in fmap X](_ : _ = fun n => F n.+1).
  apply: funext => n.
  under eq_bigr do rewrite -dvdn2 -!mulrA mulr_natl mulrb.
  rewrite -big_mkcond/=.
  rewrite big_nat_dvdn.
  rewrite addn1.
  pattern n.+1; rewrite [EQ in EQ n.+1]lock.
  have : forall f g, f = g -> forall y, locked (fun x => f x = g x) y.
    by move=> ? ? ? ? ->; rewrite -lock.
  by apply; unlock; rewrite {}/F; reflexivity.
rewrite -/(mk_sequence F) cvg_shiftS/= -[X in _ --> X]/(nbhs y).
have divn2_cofinal : divn^~ 2 @ \oo --> \oo.
  move=> N [] n _ nN.
  exists (n * 2)%N => // m/=.
  have := nN (m %/ 2)%N => /=.
  by rewrite leq_divRL.
have := (cvg_comp (divn^~ 2%N) _ divn2_cofinal Gy).
rewrite [X in fmap X](_ : _ = F)//.
apply: funext => n/=.
apply: eq_bigr => i _.
rewrite /G/= plusE addn0 addnn Rsqr_def !RealsE.
by rewrite -expr2 -exprM mul2n doubleK mulrA.
Unshelve. all: by end_near. Qed.

End RcosE.

Definition RcosE := RcosE.RcosE.

Section PIE.

Let pihalf_spec (x : R) := 0 <= x <= 2 /\ trigo.cos.body x = 0.

Let pihalf_unique (x y : R) : pihalf_spec x -> pihalf_spec y -> x = y.
Proof.
case=> /andP[] x0 x2 cosx0 [] /andP[] y0 y2 cosy0.
apply: trigo.cos_inj.
- rewrite in_itv/=; apply/andP; split => //.
  by rewrite (le_trans x2)// trigo.pi_ge2.
- rewrite in_itv/=; apply/andP; split => //.
  by rewrite (le_trans y2)// trigo.pi_ge2.
by rewrite cosx0 cosy0.
Qed.

Let PI2E : PI2 = trigo.pi / 2.
Proof.
rewrite /PI2; case: PI_2_aux => x /= [] [] /RleP x78 /RleP x74.
move/Ropp_eq_compat; rewrite Ropp_involutive Ropp_0 RealsE => cosx0.
rewrite trigo.pihalfE.
have x_pihalf : pihalf_spec x.
  split; [|by rewrite -RcosE].
  rewrite (le_trans _ x78)/= ?RealsE/=; [lra|].
  by rewrite (le_trans x74)// ?RealsE/=; lra.
apply/esym/get_unique => //= y y_pihalf.
exact: pihalf_unique.
Qed.

Lemma PIE : PI = trigo.pi.
Proof. by rewrite /PI PI2E !RealsE/= mulrCA divff// mulr1. Qed.

End PIE.

Lemma RsinE (x : R) : Rtrigo_def.sin x = trigo.sin x.
Proof. by rewrite sin_cos RcosE PIE !RealsE/= addrC trigo.cosDpihalf opprK. Qed.

Definition RealsE := (RealsE, RexpE, RlnE, RcosE, PIE, RsinE).
