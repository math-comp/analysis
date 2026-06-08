(**md**************************************************************************)
(* # Gaussian-Gaussian conjugate prior                                        *)
(*                                                                            *)
(* Stated against mathcomp-analysis' [normal_prob m s] (mean [m], standard    *)
(* deviation [s]) from [probability_theory/normal_distribution.v].            *)
(*                                                                            *)
(* For prior [theta ~ normal_prob mu0 sigma0] and Gaussian likelihood         *)
(* [X | theta ~ normal_prob theta sigma], the posterior of [theta] given      *)
(* [X = x] is itself Gaussian, [normal_prob (mu_post ..) (sigma_post ..)].    *)
(*                                                                            *)
(* ```                                                                        *)
(*    sigma_post sigma0 sigma                                                 *)
(*      := Num.sqrt (sigma0^+2 * sigma^+2 / (sigma0^+2 + sigma^+2))           *)
(*    mu_post mu0 sigma0 x sigma                                              *)
(*      := (sigma^+2 * mu0 + sigma0^+2 * x) / (sigma0^+2 + sigma^+2)          *)
(*                                                                            *)
(*    normal_pdf_conjugate ==                                                 *)
(*      sigma0 != 0 -> sigma != 0 ->                                          *)
(*      normal_pdf theta sigma x * normal_pdf mu0 sigma0 theta                *)
(*      = normal_pdf mu0 (Num.sqrt (sigma0^+2 + sigma^+2)) x                  *)
(*        * normal_pdf (mu_post ..) (sigma_post ..) theta.                    *)
(*    normal_prob_conjugate ==                                                *)
(*      \int[normal_prob mu0 sigma0]_(theta in V) normal_pdf theta sigma x    *)
(*      / \int[normal_prob mu0 sigma0]_theta normal_pdf theta sigma x         *)
(*      = normal_prob (mu_post ..) (sigma_post ..) V.                         *)
(* ```                                                                        *)
(*                                                                            *)
(* The main theorem is Bayes' rule integrated over [V]: the prior is the      *)
(* integration measure, the likelihood [p(x | theta)] is the integrand, and   *)
(* the marginal evidence [p(x)] in the denominator is computed as the total   *)
(* integral of the likelihood against the prior (no closed-form Gaussian      *)
(* density appears in the statement).  The marginal factor cancels in the     *)
(* quotient, so its explicit value (a Gaussian by [normal_probD] from         *)
(* mathcomp/analysis PR #1955) plays no role -- the load-bearing step is the  *)
(* pointwise "complete the square" identity [normal_pdf_conjugate].           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum ssrint interval.
From mathcomp Require Import archimedean finmap interval_inference.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import measure exp trigo numfun realfun.
From mathcomp Require Import measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc gauss_integral.
From mathcomp Require Import probability_theory.random_variable.
From mathcomp Require Import probability_theory.normal_distribution.
From mathcomp Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Reserved Notation "'\Pr_' mu '[' V '|' lik ']'"
  (at level 0, V at level 0, lik at level 0, mu at level 0,
   format "'\Pr_' mu [ V  |  lik ]").

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** ** Vendored from mathcomp/analysis PR #1955

    [integral_normal_prob] is the Radon-Nikodym change-of-variables for
    [normal_prob], copied (statement only) from
    [theories/probability_theory/normal_distribution.v] on branch
    [normal_20260426] of [affeldt-aist/analysis].  Delete this section
    when PR #1955 lands. *)
Section vendored_pr1955.
Context {R : realType}.
Local Open Scope ereal_scope.

Lemma integral_normal_prob (m s : R) (f : R -> \bar R) (U : set R) :
  measurable U ->
  (normal_prob m s).-integrable U f ->
  \int[normal_prob m s]_(x in U) f x
  = \int[lebesgue_measure]_(x in U) (f x * (normal_pdf m s x)%:E).
Proof. Admitted.

End vendored_pr1955.

(** ** Bayes posterior probability

    Generic measure-theoretic formulation of Bayes' rule.  Given a prior
    measure [mu] on the parameter space and a likelihood [lik : R -> R]
    -- the density of the observation, viewed as a function of the
    parameter (i.e., [lik theta = p(observation | theta)]) -- the
    posterior probability of a measurable set [V] of parameters is
    [(integral over V of lik against mu) / (total integral of lik
    against mu)].  Independent of the conjugate-prior application
    below; suitable for placement in [probability_theory/]. *)
Section bayes_posterior.
Context {d : measure_display} {T : measurableType d} {R : realType}.
Local Open Scope ereal_scope.

Definition bayes_posterior
    (mu : {measure set T -> \bar R}) (lik : T -> R) (V : set T) : \bar R :=
  (\int[mu]_(theta in V) (lik theta)%:E)
   / (\int[mu]_theta (lik theta)%:E).

End bayes_posterior.

Notation "'\Pr_' mu '[' V '|' lik ']'" := (bayes_posterior mu lik V)
  : ereal_scope.

Section gaussian_conjugate.
Context {R : realType}.
Implicit Types (sigma x theta : R) (V : set R).

(** Posterior standard deviation; squared:
    [sigma0^2 * sigma^2 / (sigma0^2 + sigma^2)]. *)
Definition sigma_post (sigma0 sigma : R) : R :=
  Num.sqrt (sigma0 ^+ 2 * sigma ^+ 2 / (sigma0 ^+ 2 + sigma ^+ 2)).

(** Posterior mean given observation [x]. *)
Definition mu_post (mu0 sigma0 x sigma : R) : R :=
  (sigma ^+ 2 * mu0 + sigma0 ^+ 2 * x) / (sigma0 ^+ 2 + sigma ^+ 2).

(** "Complete the square": the joint density [p(x | theta) * p(theta)]
    factors as [K(x) * p_posterior(theta | x)] for some [theta]-independent
    factor [K(x)].  Pure [R]-side algebraic identity, established by:
    rewriting both [normal_pdf] calls on each side via [normal_pdfE] into
    a [normal_peak] match (closed by [sqrtrM] / [invfM] + [field] under
    positivity) and a [normal_fun] match (the exponents combine via
    [expRD]; equating them is the actual "complete the square" polynomial
    identity in [theta], discharged by [field] under the sign
    hypotheses).  Concretely, [K(x) = normal_pdf mu0 (Num.sqrt
    (sigma0^+2 + sigma^+2)) x], but the value is irrelevant to the main
    theorem since it cancels in the Bayes quotient. *)
Lemma normal_pdf_conjugate mu0 sigma0 sigma x theta :
  sigma0 != 0 -> sigma != 0 ->
  normal_pdf theta sigma x * normal_pdf mu0 sigma0 theta
  = normal_pdf mu0 (Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2)) x
    * normal_pdf (mu_post mu0 sigma0 x sigma)
                 (sigma_post sigma0 sigma) theta.
Proof.
move=> sigma0_neq0 sigma_neq0.
have sigma0_2pos : 0 < sigma0 ^+ 2 by rewrite exprn_even_gt0.
have sigma_2pos : 0 < sigma ^+ 2 by rewrite exprn_even_gt0.
have sumpos : 0 < sigma0 ^+ 2 + sigma ^+ 2 by apply: addr_gt0.
have sum_neq0 : sigma0 ^+ 2 + sigma ^+ 2 != 0 by rewrite lt0r_neq0.
have sqrt_sum_neq0 : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0
  by rewrite sqrtr_eq0 -ltNge.
have sigma_post_pos : 0 < sigma_post sigma0 sigma.
  rewrite /sigma_post sqrtr_gt0; apply: divr_gt0 => //.
  by apply: mulr_gt0.
have sigma_post_neq0 : sigma_post sigma0 sigma != 0 by rewrite lt0r_neq0.
rewrite !normal_pdfE // mulrACA [RHS]mulrACA.
congr (_ * _); first last.
  rewrite /normal_fun -2!expRD; congr (expR _).
  rewrite sqr_sqrtr; last exact: ltW sumpos.
  rewrite /sigma_post sqr_sqrtr; first last.
    apply: divr_ge0; first by apply: mulr_ge0; exact: ltW.
    exact: ltW.
  rewrite /mu_post; field.
  by apply/and3P; split.
have sigmapi2_ge0 : 0 <= sigma ^+ 2 * pi *+ 2
  by apply: mulrn_wge0; apply: mulr_ge0;
     [exact: ltW sigma_2pos | exact: pi_ge0].
have sigma0pi2_ge0 : 0 <= sigma0 ^+ 2 * pi *+ 2
  by apply: mulrn_wge0; apply: mulr_ge0;
     [exact: ltW sigma0_2pos | exact: pi_ge0].
have sumpi2_ge0 : 0 <= (sigma0 ^+ 2 + sigma ^+ 2) * pi *+ 2
  by apply: mulrn_wge0; apply: mulr_ge0;
     [exact: ltW sumpos | exact: pi_ge0].
have sqsum_eq :
  Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) ^+ 2 = sigma0 ^+ 2 + sigma ^+ 2
  by rewrite sqr_sqrtr // ltW.
have sqpost_eq : sigma_post sigma0 sigma ^+ 2
  = sigma0 ^+ 2 * sigma ^+ 2 / (sigma0 ^+ 2 + sigma ^+ 2).
  rewrite /sigma_post sqr_sqrtr //.
  apply: divr_ge0; first by apply: mulr_ge0; exact: ltW.
  exact: ltW.
rewrite /normal_peak sqsum_eq sqpost_eq -invfM -[RHS]invfM -!sqrtrM //.
congr GRing.inv; congr Num.sqrt; field.
exact: sum_neq0.
Qed.

(** Integrability of the likelihood-as-function-of-theta against the
    prior.  Pdf values are in [[0, normal_peak sigma]], so the integrand
    is bounded, and [normal_prob] is a probability measure, hence
    finite.  Local because used only in [normal_prob_conjugate]. *)
Local Lemma integrable_normal_pdf_likelihood mu0 sigma0 sigma x V :
  sigma != 0 -> measurable V ->
  (normal_prob mu0 sigma0).-integrable V
    (fun theta => (normal_pdf theta sigma x)%:E).
Proof.
move=> sigma_neq0 mV.
have pdf_sym theta : normal_pdf theta sigma x = normal_pdf x sigma theta.
  rewrite !normal_pdfE //; congr (_ * _).
  by rewrite /normal_fun -[in LHS](opprB theta x) sqrrN.
have -> :
  (fun theta : R => (normal_pdf theta sigma x)%:E)
  = (fun theta : R => (normal_pdf x sigma theta)%:E)
  by apply/funext => theta; rewrite pdf_sym.
change ((normal_prob mu0 sigma0).-integrable V (EFin \o normal_pdf x sigma)).
apply: (measurable_bounded_integrable
          (mu := normal_prob mu0 sigma0)
          (f := normal_pdf x sigma) mV).
- apply: le_lt_trans; first exact: probability_le1.
  by rewrite ltey.
- by apply: measurable_funTS; exact: measurable_normal_pdf.
- exists (normal_peak sigma); split; first by rewrite num_real.
  move=> y ynp theta _.
  rewrite /= ger0_norm; last exact: normal_pdf_ge0.
  exact: le_trans (normal_pdf_ub _ _ sigma_neq0) (ltW ynp).
Qed.

(** ** Main theorem *)

(** Gaussian-Gaussian conjugate prior: the posterior of [theta] given
    [X = x] is a single Gaussian [normal_prob (mu_post ..) (sigma_post ..)].

    Reading the equation. The LHS is Bayes' rule [p(theta | x) =
    p(x | theta) p(theta) / p(x)] integrated over [V]:
    - [normal_prob mu0 sigma0] (integration measure) is the *prior*;
    - [normal_pdf theta sigma x] (integrand) is the *likelihood*
      density [p(x | theta)];
    - the *marginal* evidence [p(x)] in the denominator is computed as
      the total integral of the likelihood against the prior -- no
      closed-form Gaussian density appears in the statement. *)
Lemma normal_prob_conjugate mu0 sigma0 sigma x V :
  sigma0 != 0 -> sigma != 0 -> measurable V ->
  (\Pr_(normal_prob mu0 sigma0)
       [V | fun theta => normal_pdf theta sigma x]
   = normal_prob (mu_post mu0 sigma0 x sigma)
                 (sigma_post sigma0 sigma) V)%E.
Proof.
move=> sigma0_neq0 sigma_neq0 mV.
set tmp : {measure set (measurableTypeR R) -> \bar R} := normal_prob _ _.
rewrite /bayes_posterior /=.
pose K := normal_pdf mu0 (Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2)) x.
pose P := normal_prob (mu_post mu0 sigma0 x sigma)
                      (sigma_post sigma0 sigma) V.
have sigma0sigma_neq0 : Num.sqrt (sigma0 ^+ 2 + sigma ^+ 2) != 0.
  rewrite sqrtr_eq0 -ltNge; apply: addr_gt0; rewrite exprn_even_gt0 //=.
have Kpos : 0 < K.
  rewrite /K normal_pdfE //; apply: mulr_gt0.
    by rewrite normal_peak_gt0.
  by rewrite /normal_fun expR_gt0.
have KEneq0 : (K%:E != 0)%E by rewrite eqe; apply: lt0r_neq0.
have num_eq :
  (\int[normal_prob mu0 sigma0]_(theta in V) (normal_pdf theta sigma x)%:E
   = K%:E * P)%E.
  rewrite integral_normal_prob //;
    last exact: integrable_normal_pdf_likelihood.
  under eq_integral => theta _ do
    rewrite -EFinM
            (normal_pdf_conjugate mu0 x theta sigma0_neq0 sigma_neq0)
            EFinM.
  rewrite -/K ge0_integralZl_EFin //=; first last.
  - exact: ltW.
  - apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - by move=> theta _; rewrite lee_fin; exact: normal_pdf_ge0.
have denom_eq :
  (\int[normal_prob mu0 sigma0]_theta (normal_pdf theta sigma x)%:E
   = K%:E)%E.
  rewrite integral_normal_prob //;
    last exact: integrable_normal_pdf_likelihood.
  under eq_integral => theta _ do
    rewrite -EFinM
            (normal_pdf_conjugate mu0 x theta sigma0_neq0 sigma_neq0)
            EFinM.
  rewrite -/K ge0_integralZl_EFin //=; first last.
  - exact: ltW.
  - apply/measurable_EFinP/measurable_funTS; exact: measurable_normal_pdf.
  - by move=> theta _; rewrite lee_fin; exact: normal_pdf_ge0.
  by rewrite integral_normal_pdf // mule1.
by rewrite num_eq denom_eq muleAC divee // mul1e.
Qed.

End gaussian_conjugate.

(** ** Random-variable-style restatement

    Sugar over the measure-theoretic statement above.  Given a random
    variable [X] on a probability space [P] with [X \~ N(mu0, sigma0)]
    and a likelihood family [lik t y = p(Y = y | X = t)] (the Gaussian
    case is [lik = normal_pdf ^~ sigma]), the conditional distribution
    [\Pr[X | lik = y]] -- computed via Bayes' rule -- is the Gaussian
    posterior.

    [\Pr[X | lik = y] \~ D] is shorthand for "the Bayes posterior under
    prior [distribution P X] and likelihood [lik^~ y] agrees with [D]
    on all measurable sets".  The proof of the RV-style statement is
    just one [rewrite] using the [X \~ _] hypothesis followed by the
    underlying [normal_prob_conjugate]. *)

Section gaussian_conjugate_RV.
Context {d : measure_display} {T : measurableType d} {R : realType}.
Variable P : pprobability T R.

Local Notation "X '\~' D" := (distribution P X = D)
  (at level 70).

Local Notation "'\Pr[' X '|' F 'at' y ']' '\~' D" :=
  (forall V, measurable V ->
     (bayes_posterior (distribution P X) (F^~ y) V = D V)%E)
  (at level 70, X at next level, F at next level, y at next level).

(** **Note: canonical-structure obstacle.**

    The proof below should be one line:
    [move=> _ _ HX HL V mV; rewrite HX HL; exact: normal_prob_conjugate.]
    After [rewrite HX HL], the goal is *syntactically* the conclusion
    of [normal_prob_conjugate].  But [exact:] still fails because
    [{RV P >-> R}] in [distribution P X] picks the *default* canonical
    measurable structure on [R] ([Real_sort__canonical__measurable_
    structure_Measurable]), while [normal_prob] integrates over [R]
    viewed with the *ocitv* canonical structure ([lebesgue_stieltjes_
    measure_ocitv_type__canonical__measurable_structure_Measurable]).
    These two canonical instances are propositionally the same Borel
    sigma-algebra on [R] but Coq does not unify them.  Resolving this
    is an upstream issue in mathcomp-analysis (unify R's canonical
    measurable structure, or add a transfer lemma between the two). *)
Theorem normal_prob_conjugate_RV
    (X : {RV P >-> R}) (mu0 sigma0 sigma y : R) :
  sigma0 != 0%R -> sigma != 0%R ->
  X \~ normal_prob mu0 sigma0 ->
  \Pr[X | (fun x => normal_pdf x sigma) at y]
  \~ normal_prob (mu_post mu0 sigma0 y sigma) (sigma_post sigma0 sigma).
Proof.
move=> S00 S0 HX V mV.
rewrite /bayes_posterior/=.
rewrite -normal_prob_conjugate//.
rewrite /bayes_posterior.
rewrite -HX.
congr (_ / _)%E => //.
  simpl.
  rewrite HX//.
  rewrite /bayes_posterior.
  set tmp := normal_prob _ _.
(*Set Printing All.*)
  rewrite /Real_sort__canonical__measurable_structure_Measurable/=.
  rewrite /reverse_coercion/=.
  set A := (X in @integral _ X).
  set B := (X in _ = @integral _ X _ _ _ _).
  have : A = B := erefl.
  set f := (X in integral tmp V X = _).
  set g := (X in _ = integral tmp V X).
  have := (@eq_integral _ (measurableTypeR R) _ tmp V f g).
  
have := (@normal_prob_conjugate R mu0 sigma0 sig]ma y V S00 S0 mV).




 Qed.
 Admitted.

End gaussian_conjugate_RV.
