(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences esum.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import bernoulli_distribution.

(**md**************************************************************************)
(* # Binomial distribution                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*     binomial_pmf n p == binomial pmf with parameters n : nat and p : R     *)
(*    binomial_prob n p == binomial probability measure when 0 <= p <= 1      *)
(*                         and \d_0%N otherwise                               *)
(*       bin_prob n k p == $\binom{n}{k}p^k (1-p)^(n-k)$                      *)
(*                         Computes a binomial distribution term for          *)
(*                         k successes in n trials with success rate p        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section binomial_pmf.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : R).

Definition binomial_pmf k := p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k).

Lemma binomial_pmf_ge0 k : 0 <= p <= 1 -> 0 <= binomial_pmf k.
Proof.
by move=> /andP[p0 p1]; rewrite mulrn_wge0// mulr_ge0 ?exprn_ge0// onem_ge0.
Qed.

End binomial_pmf.

Lemma measurable_binomial_pmf {R : realType} D n k :
  measurable_fun D (@binomial_pmf R n ^~ k).
Proof.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x : R => x *+ 'C(n, k))%R) => /=.
  exact: natmul_measurable.
by apply: measurable_funM => //; apply: measurable_funX; exact: measurable_funB.
Qed.

Definition binomial_prob {R : realType} (n : nat) (p : R) : set nat -> \bar R :=
  fun U => if 0 <= p <= 1 then
    \esum_(k in U) (binomial_pmf n p k)%:E else \d_0%N U.

Section binomial.
Context {R : realType} (n : nat) (p : R).
Local Open Scope ereal_scope.

Local Notation binomial := (binomial_prob n p).

Let binomial0 : binomial set0 = 0.
Proof. by rewrite /binomial measure0; case: ifPn => //; rewrite esum_set0. Qed.

Let binomial_ge0 U : 0 <= binomial U.
Proof.
rewrite /binomial; case: ifPn => // p01; apply: esum_ge0 => /= k Uk.
by rewrite lee_fin binomial_pmf_ge0.
Qed.

Let binomial_sigma_additive : semi_sigma_additive binomial.
Proof.
move=> F mF tF mUF; rewrite /binomial; case: ifPn => p01; last first.
  exact: measure_semi_sigma_additive.
apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: lee_sum_nneg_natr => // k _ _.
  by apply: esum_ge0 => /= ? _; exact: binomial_pmf_ge0.
by rewrite nneseries_sum_bigcup// => i; rewrite lee_fin binomial_pmf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ binomial
  binomial0 binomial_ge0 binomial_sigma_additive.

Let binomial_setT : binomial [set: _] = 1.
Proof.
rewrite /binomial; case: ifPn; last by move=> _; rewrite probability_setT.
move=> p01; rewrite /binomial_pmf.
have pkn k : 0%R <= (p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k))%:E.
  case/andP : p01 => p0 p1.
  by rewrite lee_fin mulrn_wge0// mulr_ge0 ?exprn_ge0 ?subr_ge0.
rewrite (esumID `I_n.+1)// [X in _ + X]esum1 ?adde0; last first.
  by move=> /= k [_ /negP]; rewrite -leqNgt => nk; rewrite bin_small.
rewrite setTI esum_fset// -fsbig_ord//=.
under eq_bigr do rewrite mulrC.
rewrite sumEFin -exprDn_comm; last exact: mulrC.
by rewrite addrC add_onemK expr1n.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R binomial binomial_setT.

End binomial.

Section binomial_probability.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : R)
        (p0 : (0 <= p)%R) (p1 : ((NngNum p0)%:num <= 1)%R).

Definition bin_prob (k : nat) : {nonneg R} :=
  ((NngNum p0)%:num ^+ k * (NngNum (onem_ge0 p1))%:num ^+ (n - k)%N *+ 'C(n, k))%:nng.

Lemma bin_prob0 : bin_prob 0 = ((NngNum (onem_ge0 p1))%:num^+n)%:nng.
Proof.
rewrite /bin_prob bin0 subn0/=; apply/val_inj => /=.
by rewrite expr0 mul1r mulr1n.
Qed.

Lemma bin_prob1 : bin_prob 1 =
  ((NngNum p0)%:num * (NngNum (onem_ge0 p1))%:num ^+ n.-1 *+ n)%:nng.
Proof.
by rewrite /bin_prob bin1/=; apply/val_inj => /=; rewrite expr1 subn1.
Qed.

Lemma binomial_msum :
  binomial_prob n p = msum (fun k => mscale (bin_prob k) \d_k) n.+1.
Proof.
apply/funext => U.
rewrite /binomial_prob; case: ifPn => [_|]; last by rewrite p1 p0.
rewrite /msum/= /mscale/= /binomial_pmf.
have pkn k : (0%R <= (p ^+ k * p.~ ^+ (n - k) *+ 'C(n, k))%:E)%E.
  by rewrite lee_fin mulrn_wge0// mulr_ge0 ?exprn_ge0 ?subr_ge0.
rewrite (esumID `I_n.+1)//= [X in _ + X]esum1 ?adde0; last first.
  by move=> /= k [_ /negP]; rewrite -leqNgt => nk; rewrite bin_small.
rewrite esum_mkcondl esum_fset//; last by move=> i /= _; case: ifPn.
rewrite -fsbig_ord//=; apply: eq_bigr => i _.
by rewrite diracE; case: ifPn => /= iU; [rewrite mule1|rewrite mule0].
Qed.

Lemma binomial_probE U : binomial_prob n p U =
  (\sum_(k < n.+1) (bin_prob k)%:num%:E * (\d_(nat_of_ord k) U))%E.
Proof. by rewrite binomial_msum. Qed.

Lemma integral_binomial (f : nat -> \bar R) : (forall x, 0 <= f x)%E ->
  (\int[binomial_prob n p]_y (f y) =
   \sum_(k < n.+1) (bin_prob k)%:num%:E * f k)%E.
Proof.
move=> f0; rewrite binomial_msum ge0_integral_measure_sum//=.
apply: eq_bigr => i _.
by rewrite ge0_integral_mscale//= integral_dirac//= diracT mul1e.
Qed.

End binomial_probability.

Lemma integral_binomial_prob (R : realType) n p U : 0 <= p <= 1 ->
  (\int[binomial_prob n p]_y \d_(0 < y)%N U =
  bernoulli_prob (1 - p.~ ^+ n) U :> \bar R)%E.
Proof.
move=> /andP[p0 p1]; rewrite bernoulli_probE//=; last first.
  rewrite subr_ge0 exprn_ile1//=; [|exact/onem_ge0|exact/onem_le1].
  by rewrite -subr_ge0 opprB subrKC; exact/exprn_ge0/onem_ge0.
rewrite (@integral_binomial _ n p _ _ (fun y => \d_(1 <= y)%N U))//.
rewrite !big_ord_recl/=.
rewrite expr0 mul1r subn0 bin0 ltnn mulr1n addrC.
rewrite onemD opprK onem1 add0r; congr +%E.
rewrite /bump; under eq_bigr do rewrite leq0n add1n ltnS leq0n.
rewrite -ge0_sume_distrl; last first.
  by move=> i _; apply/mulrn_wge0; rewrite mulr_ge0 ?exprn_ge0// onem_ge0.
congr *%E.
transitivity (\sum_(i < n.+1) (p.~ ^+ (n - i) * p ^+ i *+ 'C(n, i))%:E -
              (p.~ ^+ n)%:E)%E.
  rewrite big_ord_recl/=.
  rewrite expr0 mulr1 subn0 bin0 mulr1n addrAC -EFinD subrr add0e.
  by rewrite /bump; under [RHS]eq_bigr do rewrite leq0n add1n mulrC.
by rewrite sumEFin -(@exprDn _ p.~ p n)// subrK expr1n.
Qed.

Lemma measurable_binomial_prob (R : realType) (n : nat) :
  measurable_fun setT (binomial_prob n : R -> pprobability _ _).
Proof.
apply: (measurability (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
apply: measurable_fun_if => //=.
  by apply: measurable_and => //; exact: measurable_fun_ler.
apply: (eq_measurable_fun (fun t =>
    \sum_(k <oo | k \in Ys) (binomial_pmf n t k)%:E))%E.
  move=> x /set_mem[_/= x01].
  rewrite nneseries_esum//; last by move=> *; rewrite lee_fin binomial_pmf_ge0.
  by rewrite set_mem_set.
apply: ge0_emeasurable_sum.
  by move=> k x/= [_ x01] _; rewrite lee_fin binomial_pmf_ge0.
by move=> k Ysk; apply/measurableT_comp => //; exact: measurable_binomial_pmf.
Qed.
