From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section ite.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variables (R : realType) (f : T -> bool) (u1 u2 : R.-sfker T ~> T').

Definition ite (mf : measurable_fun setT f) : T -> set T' -> \bar R :=
  fun t => if f t then u1 t else u2 t.

Variables mf : measurable_fun setT f.

Lemma ite0 tb : ite mf tb set0 = 0.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_ge0 tb (U : set _) : 0 <= ite mf tb U.
Proof. by rewrite /ite; case: ifPn => //. Qed.

Lemma ite_sigma_additive tb : semi_sigma_additive (ite mf tb).
Proof.
rewrite /ite.
case: ifPn => ftb.
  exact: measure_semi_sigma_additive.
exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ tb := isMeasure.Build _ _ _ (ite mf tb)
  (ite0 tb) (ite_ge0 tb) (@ite_sigma_additive tb).

Definition ite' : R.-sfker
  [the measurableType _ of (T * bool)%type] ~> T' :=
  [the R.-sfker _ ~> _ of add_of_kernels
    [the R.-sfker _ ~> T' of ite_true u1]
    [the R.-sfker _ ~> T' of ite_false u2] ].

Definition mite := [the sfinite_kernel _ _ _ of kernel_mfun R mf] \; ite'.

End ite.

Section bernoulli27.
Variable R : realType.

Local Open Scope ring_scope.
Notation "'2/7'" := (2%:R / 7%:R)%:nng.
Definition twoseven : {nonneg R} := (2%:R / 7%:R)%:nng.
Definition fiveseven : {nonneg R} := (5%:R / 7%:R)%:nng.

Definition bernoulli27 : set _ -> \bar R :=
  measure_add
    [the measure _ _ of mscale twoseven [the measure _ _ of dirac true]]
    [the measure _ _ of mscale fiveseven [the measure _ _ of dirac false]].

HB.instance Definition _ := Measure.on bernoulli27.

Local Close Scope ring_scope.

Lemma bernoulli27_setT : bernoulli27 [set: _] = 1.
Proof.
rewrite /bernoulli27/= /measure_add/= /msum 2!big_ord_recr/= big_ord0 add0e/=.
rewrite /mscale/= !diracE !in_setT !mule1 -EFinD.
by rewrite -mulrDl -natrD divrr// unitfE pnatr_eq0.
Qed.

HB.instance Definition _ := @isProbability.Build _ _ R bernoulli27 bernoulli27_setT.

End bernoulli27.

Section insn.
Variables (R : realType).

Definition letin (d d' d3 : _)
  (X : measurableType d) (Y : measurableType d') (Z : measurableType d3)
  (l : R.-sfker X ~> Y)
  (k : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  : R.-sfker X ~> Z :=
  [the sfinite_kernel _ _ _ of (l \; k)].

Definition Return (d d' : _) (T : measurableType d) (T' : measurableType d')
  (f : T -> T') (mf : measurable_fun setT f) : R.-sfker T ~> T' :=
  [the sfinite_kernel _ _ _ of @kernel_mfun _ _ T T' R f mf].

Definition sample_bernoulli27 (d : _) (T : measurableType d) :=
  [the sfinite_kernel T _ _ of
   kernel_probability [the probability _ _ of bernoulli27 R]] .

(* NB: score r = observe 0 from exp r,
       the density of the exponential distribution exp(r) at 0 is r = r e^(-r * 0)
       more generally, score (r e^(-r * t)) = observe t from exp(r),
       score (f(r)) = observe r from p where f is the density of p *)
Definition Score (d : _) (T : measurableType d) (r : T -> R) (mr : measurable_fun setT r) :
    R.-sfker T ~> Datatypes_unit__canonical__measure_Measurable :=
  [the sfinite_kernel _ _ R of @kernel_score R _ _ r mr].

Definition Ite (d d' : _) (T : measurableType d) (T' : measurableType d')
    (f : T -> bool) (mf : measurable_fun setT f)
    (u1 u2 : R.-sfker T ~> T')
    : R.-sfker T ~> T' :=
  [the R.-sfker _ ~> _ of mite u1 u2 mf].

Lemma IteE (d d' : _) (T : measurableType d) (T' : measurableType d')
    (f : T -> bool) (mf : measurable_fun setT f)
    (u1 u2 : R.-sfker T ~> T') tb U :
  Ite mf u1 u2 tb U = ite u1 u2 mf tb U.
Proof.
rewrite /= /kcomp /ite.
rewrite integral_dirac//=.
rewrite indicT /cst.
rewrite mul1e.
rewrite -/(measure_add (ite_true u1 (tb, f tb))
                       (ite_false u2 (tb, f tb))).
rewrite measure_addE.
rewrite /ite_true /ite_false/=.
case: (ifPn (f tb)) => /=.
  by rewrite /mzero adde0.
by rewrite /mzero add0e.
Qed.

End insn.

(* a few laws *)

Section letin_return.
Variables (d d' d3 : _) (R : realType) (X : measurableType d)
  (Y : measurableType d') (Z : measurableType d3).

Lemma letin_ureturn (u : R.-sfker X ~> Y)
  (f : _ -> Z) (mf : measurable_fun setT f) :
  forall x U, measurable U -> letin u (Return R mf) x U = u x ((fun y => f (x, y)) @^-1` U).
Proof.
move=> x U mU.
rewrite /letin/= /kcomp/= integral_indic// ?setIT//.
move/measurable_fun_prod1 : mf => /(_ x)/(_ measurableT U mU).
by rewrite setTI.
Qed.

Lemma letin_returnu
  (u : R.-sfker [the measurableType (d, d').-prod of (X * Y)%type] ~> Z)
  (f : _ -> Y) (mf : measurable_fun setT f) :
  forall x U, measurable U -> letin (Return R mf) u x U = u (x, f x) U.
Proof.
move=> x U mU.
rewrite /letin/= /kcomp/= integral_dirac//.
  by rewrite indicE mem_set// mul1e.
have /measurable_fun_prod1 := measurable_kernel u _ mU.
exact.
Qed.

End letin_return.

Section letin_ite.
Variables (R : realType) (d d2 d3 : _) (T : measurableType d)
  (T2 : measurableType d2) (T3 : measurableType d3)
  (u1 u2 : R.-sfker T ~> T3) (u : R.-sfker [the measurableType _ of (T * T3)%type] ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin_ite_true : f t -> letin (Ite mf u1 u2) u t U = letin u1 u t U.
Proof.
move=> ftT.
rewrite /letin/= /kcomp.
apply eq_measure_integral => V mV _.
by rewrite IteE /ite ftT.
Qed.

Lemma letin_ite_false : ~~ f t -> letin (Ite mf u1 u2) u t U = letin u2 u t U.
Proof.
move=> ftF.
rewrite /letin/= /kcomp.
apply eq_measure_integral => V mV _.
by rewrite IteE/= /ite (negbTE ftF).
Qed.

End letin_ite.

(* sample programs *)

Require Import exp.

Definition poisson (R : realType) (r : R) (k : nat) := (r ^+ k / k%:R^-1 * expR (- r))%R.

Definition poisson3 (R : realType) := poisson (3%:R : R) 4. (* 0.168 *)
Definition poisson10 (R : realType) := poisson (10%:R : R) 4. (* 0.019 *)

Lemma poisson_ge0 (R : realType) (r : R) k : (0 <= r)%R -> (0 <= poisson r k)%R.
Proof.
move=> r0; rewrite /poisson mulr_ge0//.
  by rewrite mulr_ge0// exprn_ge0//.
by rewrite ltW// expR_gt0.
Qed.

Lemma mpoisson (R : realType) k : measurable_fun setT (@poisson R ^~ k).
Proof.
apply: measurable_funM => /=.
  apply: measurable_funM => //=; last exact: measurable_fun_cst.
  exact/measurable_fun_exprn/measurable_fun_id.
apply: measurable_fun_comp.
  apply: continuous_measurable_fun.
  exact: continuous_expR.
apply: continuous_measurable_fun.
by have := (@opp_continuous R [the normedModType R of R^o]).
Qed.

Section cst_fun.
Variables (R : realType) (d : _) (T : measurableType d).

Definition kn (n : nat) := @measurable_fun_cst _ _ T _ setT (n%:R : R).
Definition k3 : measurable_fun _ _ := kn 3.
Definition k10 : measurable_fun _ _ := kn 10.

End cst_fun.

Lemma ScoreE (R : realType) (d : _) (T : measurableType d) (t : T) (U : set bool) (n : nat)  (b : bool)
  (f : R -> R) (f0 : forall r, (0 <= r)%R -> (0 <= f r)%R) (mf : measurable_fun setT f) :
  Score (measurable_fun_comp mf (@measurable_fun_snd _ _ _ _))
    (t, b, cst n%:R (t, b))
    ((fun y : unit => (snd \o fst) (t, b, y)) @^-1` U) =
  (f n%:R)%:E * \d_b U.
Proof.
rewrite /Score/= /mscore/= diracE.
have [U0|U0] := set_unit ((fun=> b) @^-1` U).
- rewrite U0 eqxx memNset ?mule0//.
  move=> Ub.
  move: U0.
  move/seteqP => [/(_ tt)] /=.
  by move/(_ Ub).
- rewrite U0 setT_unit ifF//; last first.
    by apply/negbTE/negP => /eqP/seteqP[/(_ tt erefl)].
  rewrite /= mem_set//; last first.
    by move: U0 => /seteqP[_]/(_ tt)/=; exact.
  by rewrite mule1 ger0_norm// f0.
Qed.

Lemma letin_sample_bernoulli27 (R : realType) (d d' : _) (T : measurableType d)
    (T' : measurableType d')
    (u : R.-sfker [the measurableType _ of (T * bool)%type] ~> T') x y :
  letin (sample_bernoulli27 R T) u x y =
  (2 / 7)%:E * u (x, true) y + (5 / 7)%:E * u (x, false) y.
Proof.
rewrite {1}/letin/= {1}/kcomp/=.
rewrite ge0_integral_measure_sum//.
rewrite 2!big_ord_recl/= big_ord0 adde0/=.
rewrite !ge0_integral_mscale//=.
rewrite !integral_dirac//=.
by rewrite indicE in_setT mul1e indicE in_setT mul1e.
Qed.

(* *)

Section program1.
Variables (R : realType) (d : _) (T : measurableType d).

Definition program1 : R.-sfker T ~> _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Return R (@measurable_fun_snd _ _ _ _)) (* T * B -> B *).

Lemma program1E (t : T) (U : _) : program1 t U =
  ((twoseven R)%:num)%:E * \d_true U +
  ((fiveseven R)%:num)%:E * \d_false U.
Proof.
rewrite /program1.
by rewrite letin_sample_bernoulli27.
Qed.

End program1.

Section program2.
Variables (R : realType) (d : _) (T : measurableType d).

Definition program2  : R.-sfker T ~> _ :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Score (measurable_fun_cst (1%:R : R))).

End program2.

Section program3.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   return r *)

Definition program3 :
  R.-sfker T ~> [the measurableType default_measure_display of Real_sort__canonical__measure_Measurable R] :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (Ite (@measurable_fun_snd _ _ _ _)
       (Return R (@k3 _ _ [the measurableType _ of (T * bool)%type]))
       (Return R (@k10 _ _ [the measurableType _ of (T * bool)%type]))).

Lemma program3E (t : T) (U : _) : program3 t U =
  ((twoseven R)%:num)%:E * \d_(3%:R : R) U +
  ((fiveseven R)%:num)%:E * \d_(10%:R : R) U.
Proof.
rewrite /program3 letin_sample_bernoulli27.
congr (_ * _ + _ * _).
by rewrite IteE.
by rewrite IteE.
Qed.

End program3.

Section program4.
Variables (R : realType) (d : _) (T : measurableType d).

(* let x = sample (bernoulli (2/7)) in
   let r = case x of {(1, _) => return (k3()), (2, _) => return (k10())} in
   let _ = score (1/4! r^4 e^-r) in
   return x *)

Definition program4 : R.-sfker T ~> Datatypes_bool__canonical__measure_Measurable :=
  letin
    (sample_bernoulli27 R T) (* T -> B *)
    (letin
      (letin (* T * B -> unit *)
        (Ite (@measurable_fun_snd _ _ _ _)
          (Return R (@k3 _ _ [the measurableType _ of (T * bool)%type]))
          (Return R (@k10 _ _ [the measurableType _ of (T * bool)%type]))) (* T * B -> R *)
        (Score (measurable_fun_comp (@mpoisson R 4) (@measurable_fun_snd _ _ _ _))) (* B * R -> unit *))
      (Return R (measurable_fun_comp (@measurable_fun_snd _ _ _ _) (@measurable_fun_fst _ _ _ _)))).

(* true -> 5/7 * 0.019 = 5/7 * 10^4 e^-10 / 4! *)
(* false -> 2/7 * 0.168 = 2/7 * 3^4 e^-3 / 4! *)

Lemma program4E (t : T) (U : _) : program4 t U =
  ((twoseven R)%:num)%:E * (poisson 3%:R 4)%:E * \d_(true) U +
  ((fiveseven R)%:num)%:E * (poisson 10%:R 4)%:E * \d_(false) U.
Proof.
rewrite /program4.
rewrite letin_sample_bernoulli27.
rewrite -!muleA.
congr (_ * _ + _ * _).
  rewrite letin_ureturn //.
  rewrite letin_ite_true//.
  rewrite letin_returnu//.
  by rewrite ScoreE// => r r0; exact: poisson_ge0.
rewrite letin_ureturn //.
rewrite letin_ite_false//.
rewrite letin_returnu//.
by rewrite ScoreE// => r r0; exact: poisson_ge0.
Qed.

End program4.
