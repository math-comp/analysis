(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
Require Import real_interval exp numfun lebesgue_measure lebesgue_integral.
Require Import reals ereal signed topology normedtype derive sequences esum.
Require Import measure exp numfun lebesgue_measure lebesgue_integral kernel.
Require Import probability.

(**md**************************************************************************)
(* # Sampling experiment (wip)                                                *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Rajani https://math.uchicago.edu/~may/REU2019/REUPapers/Rajani.pdf       *)
(* - Mitzenmacher Upfal Probability and Computing                             *)
(*   https://www.cs.purdue.edu/homes/spa/courses/pg17/mu-book.pdf             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Section probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_setC A : d.-measurable A -> P (~` A) = 1 - P A.
Proof.
move=> mA.
rewrite -(@probability_setT _ _ _ P) -[in RHS](setTI A).
rewrite -measureD ?setTD ?setCK//.
by rewrite [ltLHS](@probability_setT _ _ _ P) ltry.
Qed.

Lemma probability_setC' A : d.-measurable A -> P A = 1 - P (~` A).
Proof.
move=> mA.
rewrite -(@probability_setT _ _ _ P) -[in RHS](setTI (~` A)).
rewrite -measureD ?setTD ?setCK//; first exact: measurableC.
by rewrite [ltLHS](@probability_setT _ _ _ P) ltry.
Qed.

End probability.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%E/1%:E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%E/1%:E]_(i <- r) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%E/1%:E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%E/1%:E]_(m <= i < n) F%E) : ereal_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%E/1%:E]_(i | P%B) F%E) : ereal_scope.
Notation "\prod_ i F" :=
  (\big[*%E/1%:E]_i F%E) : ereal_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%E/1%:E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%E/1%:E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%E/1%:E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%E/1%:E]_(i < n) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%E/1%:E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%E/1%:E]_(i in A) F%E) : ereal_scope.

Lemma indic_setI {R : ringType} T (A B : set T) :
  \1_A \* \1_B = \1_(A `&` B) :> (T -> R).
Proof.
by apply/funext => x/=; rewrite /indic in_setI/= -natrM mulnb.
Qed.

Lemma preimage_class_mindic {R : realType} d {T : measurableType d}
    (A : set T) (mA : measurable A) :
  preimage_class [set: T] (mindic R mA) measurable A.
Proof.
exists [set 1%R] => //; rewrite setTI preimage_indic/=.
by rewrite mem_set// memNset//=; apply/eqP; rewrite eq_sym oner_eq0.
Qed.

(* TODO: move near nnfun_muleindic_ge0 *)
Section nnfun_mulrindic_ge0.

Lemma mulrf_ge0 (R : realDomainType) x (f : R -> R) :
  0 <= f x -> (x < 0 -> f x = 0) -> 0 <= x * f x.
Proof.
move=> A0 xA /=; have [x0|x0] := ltP x 0%R; first by rewrite (xA x0) mulr0.
by rewrite mulr_ge0.
Qed.

Lemma nnfun_mulrindic_ge0 d (T : measurableType d) (R : realDomainType)
  (f : {nnfun T >-> R}) r z : (0 <= r * (\1_(f @^-1` [set r]) z))%R.
Proof.
apply: (@mulrf_ge0 _ _ (fun r => \1_(f @^-1` [set r]) z)).
  by rewrite indicE.
by move=> r0; rewrite preimage_nnfun0// indic0.
Qed.

End nnfun_mulrindic_ge0.

(* TODO: move to lebesgue_integral.v *)
Section integrable_comp.
Local Open Scope ereal_scope.

Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variable phi : X -> Y.
Hypothesis mphi : measurable_fun [set: X] phi.
Variable mu : {measure set X -> \bar R}.
Variable f : Y -> \bar R.
Hypothesis mf : measurable_fun [set: Y] f.
Hypothesis intf : mu.-integrable [set: X] (f \o phi).
Local Open Scope ereal_scope.

Lemma integrable_comp_funeneg : (pushforward mu mphi).-integrable [set: Y] f^\-.
Proof.
apply/integrableP; split.
  exact: measurable_funeneg.
move/integrableP : (intf) => [_].
apply: le_lt_trans.
rewrite ge0_integral_pushforward//=; last first.
  apply: measurableT_comp => //=.
  exact: measurable_funeneg.
apply: ge0_le_integral => //=.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
exact: measurable_funeneg.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
move=> x _.
rewrite -/((abse \o (f \o phi)) x).
rewrite (fune_abse (f \o phi)) /=.
by rewrite gee0_abs// leeDr.
Qed.

Lemma integrable_comp_funepos : (pushforward mu mphi).-integrable [set: Y] f^\+.
Proof.
apply/integrableP; split.
  exact: measurable_funepos.
move/integrableP : (intf) => [_].
apply: le_lt_trans.
rewrite ge0_integral_pushforward//=; last first.
  apply: measurableT_comp => //=.
  exact: measurable_funepos.
apply: ge0_le_integral => //=.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
exact: measurable_funepos.
apply: measurableT_comp => //=.
apply: measurableT_comp => //=.
move=> x _.
rewrite -/((abse \o (f \o phi)) x).
rewrite (fune_abse (f \o phi)) /=.
by rewrite gee0_abs// leeDl.
Qed.

End integrable_comp.

Section transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (mu : {measure set X -> \bar R}).

Lemma integral_pushforward (f : Y -> \bar R) :
  measurable_fun setT f ->
  mu.-integrable setT (f \o phi) ->
  \int[pushforward mu mphi]_y f y = \int[mu]_x (f \o phi) x.
Proof.
move=> mf intf.
transitivity (\int[mu]_y ((f^\+ \o phi) \- (f^\- \o phi)) y); last first.
  by apply: eq_integral => x _; rewrite [in RHS](funeposneg (f \o phi)).
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite -[X in _ = X - _]ge0_integral_pushforward//; last first.
  exact: measurable_funepos.
rewrite -[X in _ = _ - X]ge0_integral_pushforward//; last first.
  exact: measurable_funeneg.
rewrite -integralB//=; last first.
- apply: integrable_comp_funepos => //.
    exact: measurableT_comp.
  exact: integrableN.
- exact: integrable_comp_funepos.
- apply/eq_integral => x _.
  by rewrite /= [in LHS](funeposneg f).
Qed.

End transfer.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

(* TODO: rename integral_distribution to ge0_integral_distribution *)
Lemma integral_distribution' (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun setT f ->
    P.-integrable [set: T] (f \o X) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf intf; rewrite integral_pushforward. Qed.

End transfer_probability.

Section integral_measure_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (m1 m2 : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Variable f : T -> \bar R.
Hypothesis intf1 : m1.-integrable D f.
Hypothesis intf2 : m2.-integrable D f.
Hypothesis mf : measurable_fun D f.

Lemma integral_measure_add :
  \int[measure_add m1 m2]_(x in D) f x = \int[m1]_(x in D) f x + \int[m2]_(x in D) f x.
Proof.
transitivity (\int[m1]_(x in D) (f^\+ \- f^\-) x +
              \int[m2]_(x in D) (f^\+ \- f^\-) x); last first.
  by congr +%E; apply: eq_integral => x _; rewrite [in RHS](funeposneg f).
rewrite integralB//; last 2 first.
  exact: integrable_funepos.
  exact: integrable_funeneg.
rewrite integralB//; last 2 first.
  exact: integrable_funepos.
  exact: integrable_funeneg.
rewrite addeACA.
rewrite -ge0_integral_measure_add//; last first.
  apply: measurable_funepos.
  exact: measurable_int intf1.
rewrite -oppeD; last first.
  by rewrite ge0_adde_def// inE integral_ge0.
rewrite -ge0_integral_measure_add//; last first.
  apply: measurable_funeneg.
  exact: measurable_int intf1.
by rewrite integralE.
Qed.

End integral_measure_add.

Lemma expR_prod d (T : measurableType d) (R : realType) (P : probability T R)
  (X : seq {RV P >-> R}) (f : {RV P >-> R} -> R) :
  (\prod_(x <- X) expR (f x) = expR (\sum_(x <- X) f x))%R.
Proof.
elim: X => [|h t ih]; first by rewrite !big_nil expR0.
by rewrite !big_cons ih expRD.
Qed.

(* TODO: move *)
Lemma ln_div {R : realType} :
  {in Num.pos &, {morph ln (R:=R) : x y / (x / y)%R >-> (x - y)%R}}.
Proof.
move=> x y; rewrite !posrE => x0 y0.
by rewrite lnM ?posrE ?invr_gt0// lnV ?posrE.
Qed.

Lemma norm_expR {R : realType} : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

Lemma le01_expR_ge1Dx {R : realType} (x : R) :
  (-1 <= x <= 0 -> 1 + x <= expR x)%R.
Proof.
move=> /andP [N1x x0].
pose f : R^o -> R := (expR \- (cst 1 \+ id))%R.
rewrite -subr_ge0 (_ : 0%R = f 0%R); last first.
  by rewrite /f !fctE/= expR0 addr0 subrr.
pose f' : R^o -> R := (expR \- (cst 0 \+ cst 1))%R.
move: N1x; rewrite le_eqVlt => /predU1P[<-|N1x].
  by rewrite /f !fctE /= expR0 addr0 subrr subr0 expR_ge0.
move: x0; rewrite le_eqVlt => /predU1P[<-//|x0].
have [c cx] : exists2 c, c \in `]x, 0%R[ & (f 0 - f x)%R = (f' c * (0 - x))%R.
  apply: MVT => //.
  apply: continuous_subspaceT => /= z.
  apply: cvgB; first exact: continuous_expR.
  by apply: cvgD => //; exact: cvg_cst.
rewrite -[leRHS]/(f x) -subr_le0 sub0r /f' => ->; apply: mulr_le0_ge0.
  rewrite /=subr_le0 add0r -expR0 ler_expR.
  by move: cx; rewrite in_itv => /andP[_ /ltW].
by rewrite lerNr oppr0 ltW.
Qed.

(* mu-book p. 66 *)
Lemma analytical_argument_thm22 {R : realType} (delta : R) :
  0 <= delta <= 1 ->
  (- delta - (1 - delta) * ln (1 - delta) <= - delta ^+ 2 / 2)%R.
Proof.
move=> d01.
pose f (x : R) := - x - (1 - x) * ln (1 - x) + x ^+2 / 2.
pose f' (x : R) := ln (1 - x) + x.
pose f'' (x : R) := - (1 - x)^-1 + 1.
have f''01 (x : R) : 0 <= x <= 1 -> f'' x < 0.
  admit.
have f'0 : f' 0 = 0 by rewrite /f' subr0 ln1 addr0.
have f'01 (x : R) : 0 <= x <= 1 -> f' x <= 0.
  admit.
have f0 : f 0 = 0 :> R.
  by rewrite /f subr0 ln1 mulr0 expr0n mul0r subr0 addrC subrr.
have f01 (x : R) : 0 <= x <= 1 -> f x <= 0.
  admit.
rewrite -subr_le0.
rewrite mulNr opprK.
exact: f01.
Admitted.

(* mu-book p. 65 *)
Lemma analytical_argument_thm26 {R : realType} (delta : R) :
  0 <= delta <= 1 ->
  ((1 + delta) * ln (1 + delta) >= delta + delta^+2 / 3)%R.
Proof.
move=> d01.
pose f x : R := x - (1 + x) * ln (1 + x) + x^+2 / 3.
pose f' x : R := 1 - (1 + x) / (1 - x) - ln (1 + x) + (2 / 3) * x.
have f'E x : f' x = - ln (1 + x) + (2 / 3) * x.
   admit.
pose f'' x : R := - (1 + x)^-1 + 2 / 3.
have f''P1 (x : R) : 0 <= x < 1/2 -> f'' x < 0.
  admit.
have f''P2 x : x > 1/2 -> f'' x > 0.
  admit.
have f'0 : f' 0 = 0.
  by rewrite /f' subr0 divr1 mulr0 addr0 ln1 subr0 subrr addr0.
have f'1 : f' 1 < 0.
  admit.
have f'01 (x : R) : 0 <= x <= 1 -> f' x <= 0.
  admit.
have f0 : f 0 = 0.
  by rewrite /f addr0 expr0n/= mul0r ln1 mulr0 subrr addr0.
have f01 (x : R) : 0 <= x <= 1 -> f x <= 0.
  admit.
have := f01 _ d01.
by rewrite /f addrAC subr_le0.
Admitted.

(* WIP *)
Section independent_events.
Context {R : realType} d {T : measurableType d}.
Variable P : probability T R.
Local Open Scope ereal_scope.

(* klenke def 2.3 (independence of events) *)
Definition mutually_independent_events (I : choiceType) (A : I -> set T) :=
(*  (forall i, J i -> measurable (A i)) /\*)
  forall J : {fset I},
    P (\big[setI/setT]_(i <- J) A i) = \prod_(i <- J) P (A i).

End independent_events.

(* iklenke def 2.11, p.59 (independence of classed of events) *)
Section independent_class.
Context {R : realType} d {T : measurableType d}.
Variable P : probability T R.
Local Open Scope ereal_scope.

Definition independent_class (I : choiceType) (D : set I) (C : I -> set (set T)) :=
  (forall i, D i -> C i `<=` @measurable _ T) /\
  forall J : {fset I},
    [set` J] `<=` D ->
    forall E : I -> set T,
      (forall i : I, i \in J -> E i \in C i) ->
        P (\big[setI/setT]_(j <- J) E j) = \prod_(j <- J) P (E j).

End independent_class.

Section thm213.
Local Open Scope ereal_scope.
Context {R : realType} d {T : measurableType d}.
Variable P : probability T R.

Lemma thm213i (I : choiceType) (D : {fset I}) (C : I -> set (set T)) :
  (forall i : I, i \in D -> C i `<=` @measurable _ T /\ [set: T] \in C i) ->
  independent_class P [set` D] C <->
  forall E : I -> set T,
    (forall i : I, i \in D -> E i \in C i) ->
    P (\big[setI/setT]_(j <- D) E j) = \prod_(j <- D) P (E j).
Proof.
move=> mCT; split => [PC E EC|].
  move: PC => [_].
  move=> /(_ D).
  move=> /(_ (@subset_refl _ _)).
  by move=> /(_ E EC).
move=> h; split=> [i Di|J JD E EC].
  by have [] := mCT i Di.
pose F i := if i \in J then E i else setT.
have {}/h : forall i, i \in D -> F i \in C i.
  by move=> i iD; rewrite /F; case: ifPn => [|iJ]; [exact: EC|have [] := mCT i iD].
rewrite [in X in X = _ -> _](bigID (mem J))/=.
rewrite [X in _ `&` X]big1 ?setIT; last by move=> i iJ; rewrite /F (negbTE iJ).
rewrite [in X in _ = X -> _](bigID (mem J))/=.
rewrite [X in _ * X]big1 ?mule1; last first.
  by move=> i iJ; rewrite /F (negbTE iJ) probability_setT.
rewrite (eq_bigr E); last by move=> i iJ; rewrite /F iJ.
rewrite [X in _ = X -> _](eq_bigr (P \o E)); last by move=> i iJ; rewrite /F iJ.
rewrite big_fset_condE/=.
have DJJ : [fset i | i in D & i \in J]%fset = J.
  by apply/fsetP => i; rewrite !inE/= andb_idl// => /JD.
rewrite DJJ => ->.
by rewrite big_fset_condE/= DJJ.
Qed.

End thm213.

Section independent_RV.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.

Definition generated_salgebra (X : {RV P >-> R}) : set (set T) :=
  preimage_class setT X (@measurable _ R).

Definition independent_RV (I : choiceType) (X : I -> {RV P >-> R}) :=
  independent_class P setT (fun i : I => generated_salgebra (X i)).

Definition independent_RV_tuple n (X : n.-tuple {RV P >-> R}) :=
  independent_class P setT (fun i => generated_salgebra (X `_ i)).

Lemma independent_RV_tuple_thead_prod_behead n (X : n.+1.-tuple {RV P >-> R}) :
  independent_RV_tuple X ->
  independent_RV_tuple [tuple thead X; (\prod_(j <- behead X) j)%R].
Proof.
move: X; elim: n => [X [h1 h2]|].
  have -> : behead X = nil. admit.
  rewrite big_nil.
  rewrite /independent_RV_tuple/independent_class/=.
  split.
    case => //=.
      by move: (h1 0); rewrite {1}(tuple_eta X).
    case => //=.
      rewrite /generated_salgebra /preimage_class.
      admit.
    case => /= [|_].
      admit.
    admit.
  admit.
(*rewrite /independent_RV_tuple/independent_class/= => [[h1 h2]].
split.
  admit.
move=> J E h3.
rewrite h2// => i iJ.
have := h3 i iJ.
move: iJ.
case: i => [//|i _].*)
Admitted.

Lemma independent_RV_tuple_behead n (X : n.-tuple {RV P >-> R}) :
  independent_RV_tuple X -> independent_RV_tuple [tuple of behead X].
Proof.
move: X; case: n => [X|n X].
  by rewrite tuple0.
rewrite /independent_RV_tuple/independent_class/=.
move=> [iXm iX].
split; first by move=> i; rewrite nth_behead; exact: iXm.
move=> J _ E h.
pose E' n := match n with
               0 => setT
             | S m => E m
             end.
have := (@iX (0 |` [fset i.+1 | i in J])%fset (@subsetT _ _) E').
have ? : 0 \notin [fset i.+1 | i in J]%fset.
  apply/negP.
  move/imfsetP.
  by case.
rewrite big_fsetU1//=.
rewrite setTI big_fsetU1//=.
rewrite probability_setT mul1e.
rewrite big_imfset/=; last first.
  move=> x y _ _; exact: succn_inj.
move=> ->; last first.
  elim.
    move=> _.
    rewrite/generated_salgebra/preimage_class.
    (* TODO: make lemma *)
    rewrite inE/=.
    exists setT => //.
    by rewrite setTI preimage_setT.
  rewrite /E' => l _ h1.
  have := (h l).
  rewrite /generated_salgebra.
  rewrite nth_behead => -> //.
  move: h1.
  move/fset1UP => []//.
  move/imfsetP.
  case => k/= kJ.
  by case => ->.
rewrite big_imfset//=.
move=> x y _ _; exact: succn_inj.
Qed.

End independent_RV.

Section independent_product.
Context {R : realType} d {T : measurableType d}.
Variable P : probability T R.
Local Open Scope ereal_scope.

Let independent_RVs_expectation2_prob (A B : set T)
  (mA : measurable A) (mB : measurable B) :
  independent_RV_tuple [tuple of [:: mindic R mA : {RV P >-> R};
                                     mindic R mB : {RV P >-> R}]] ->
  P (A `&` B) = P A * P B.
Proof.
move=> AB.
pose O1 := [fset 0; 1]%N%fset.
pose funO1 := [eta fun=> set0 with 0 |-> A, 1 |-> B]%N.
have : forall i : nat, i \in O1 ->
    funO1 i \in @generated_salgebra _ _ _ P [:: mindic R mA : {RV P >-> R} ;
                                                mindic R mB : {RV P >-> R}]`_i.
  move=> [|[|?]]; rewrite /O1 ?inE//= => _.
  + by rewrite /generated_salgebra; exact: preimage_class_mindic.
  + by rewrite /generated_salgebra; exact: preimage_class_mindic.
move/AB.2 => /(_ (@subsetT _ _)).
by rewrite /O1 !big_fsetU1/= ?inE// !big_seq_fset1/=.
Qed.

Let independent_RVs_expectation2_indic (A B : set T)
  (mA : measurable A) (mB : measurable B) :
  independent_RV_tuple [tuple of [:: mindic R mA : {RV P >-> R};
                                     mindic R mB : {RV P >-> R}]] ->
  'E_P[\1_A * \1_B] = 'E_P[\1_A] * 'E_P[\1_B].
Proof.
move=> AB.
transitivity ('E_P[\1_(A `&` B)]).
  by rewrite -indic_setI.
rewrite !expectation_indic//; last exact: measurableI.
exact: independent_RVs_expectation2_prob.
Qed.

Let independent_RVs_expectation2_nnsfun (f g : {nnsfun T >-> R}) :
  independent_RV_tuple [tuple of [:: f : {RV P >-> R} ;
                                     g : {RV P >-> R}]] ->
  'E_P[f \* g] = 'E_P[f] * 'E_P[g].
Proof.
move=> fg.
rewrite [in RHS]unlock.
under [X in _ = X * _]eq_integral do rewrite (fimfunE f) -fsumEFin//.
under [X in _ = _ * X]eq_integral do rewrite (fimfunE g) -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  by move=> n; apply/measurableT_comp => //; exact/measurable_funM.
  by move=> n x _/=; rewrite lee_fin//=; exact: nnfun_mulrindic_ge0.
rewrite ge0_integral_fsum//; last 2 first.
  by move=> n; apply/measurableT_comp => //; exact/measurable_funM.
  by move=> n x _/=; rewrite lee_fin//=; exact: nnfun_mulrindic_ge0.
under [in X in _ = X * _]eq_fsbigr.
  move=> x xf.
  rewrite (integralZl_indic measurableT (fun k => f @^-1` [set x]))//; last first.
    exact: preimage_nnfun0.
  rewrite integral_indic// setIT.
  over.
rewrite /=.
under [in X in _ = _ * X]eq_fsbigr.
  move=> x xf.
  rewrite (integralZl_indic measurableT (fun k => g @^-1` [set x]))//; last first.
    exact: preimage_nnfun0.
  rewrite integral_indic// setIT.
  over.
rewrite /=.
rewrite !fsbig_finite//=.
rewrite ge0_sume_distrl; last by move=> r _; rewrite nnsfun_mulemu_ge0.
under eq_bigr.
  move=> r _.
  rewrite ge0_sume_distrr; last by move=> s _; rewrite nnsfun_mulemu_ge0.
  under eq_bigr do rewrite muleACA.
  over.
rewrite /=.
transitivity (
  (\sum_(i <- fset_set (range f))
      \sum_(i0 <- fset_set (range g))
         (i%:E * i0%:E * (P (f @^-1` [set i] `&` g @^-1` [set i0])))%E)%R
); last first.
  rewrite big_seq [RHS]big_seq; apply: eq_bigr => r rf.
  rewrite big_seq [RHS]big_seq; apply: eq_bigr => s sf.
  congr *%E.
  rewrite -[in RHS](setIT (f @^-1` [set r])).
  rewrite -[in RHS](setIT (g @^-1` [set s])).
  do 2 rewrite -[in RHS]integral_indic//.
  do 2 rewrite integral_indic//.
  rewrite !setIT.
  apply: independent_RVs_expectation2_prob => /=.
  rewrite /independent_RV_tuple/independent_class/= in fg.
  case: (fg) => _.
  admit.
transitivity (
  \int[P]_x (\sum_(i <- fset_set (range f))
      \sum_(i0 <- fset_set (range g))
         (i%:E * i0%:E * (\1_(f @^-1` [set i] `&` g @^-1` [set i0]) x)%:E)%E)%R
); last first.
  rewrite ge0_integral_sum//=; last 2 first.
    move=> r; apply: emeasurable_fun_sum => // s.
    apply: emeasurable_funM => //.
    apply: measurableT_comp => //.
    apply: measurable_indic.
    exact: measurableI.
    move=> r t _.
    apply: sume_ge0 => // s _.
    rewrite -indic_setI/= EFinM.
    by rewrite -muleACA mule_ge0//; exact: nnfun_muleindic_ge0.
  apply: eq_bigr => r _.
  rewrite ge0_integral_sum//=; last 2 first.
    move=> s; apply: emeasurable_funM => //.
    apply: measurableT_comp => //.
    apply: measurable_indic.
    exact: measurableI.
    move=> s t _.
    rewrite -indic_setI/= EFinM.
    by rewrite -muleACA mule_ge0//; exact: nnfun_muleindic_ge0.
  apply: eq_bigr => s _.
  under eq_integral do rewrite -muleA.
  rewrite integralZl//; last first.
    admit.
  rewrite -muleA.
  congr *%E.
  rewrite integralZl//; last first.
    admit.
  congr *%E.
  rewrite integral_indic ?setIT//.
  exact: measurableI.
rewrite unlock.
apply: eq_integral => x _.
under eq_bigr do rewrite sumEFin.
rewrite sumEFin.
congr EFin.
rewrite /=.
rewrite (fimfunE f).
rewrite (fimfunE g).
rewrite !fsbig_finite//=.
rewrite big_distrl//=.
apply: eq_bigr => r _.
rewrite big_distrr//=.
apply: eq_bigr => s _.
rewrite mulrACA.
by rewrite -indic_setI.
Admitted.

Let independent_RVs_expectation2_ge0 (X Y : {RV P >-> R}) :
  independent_RV_tuple [tuple of [:: X; Y]] ->
  (forall x, 0 <= X x)%R ->
  (forall x, 0 <= Y x)%R ->
  'E_P[X * Y] = 'E_P[X] * 'E_P[Y].
Proof.
move=> XY X0 Y0.
have mX : measurable_fun setT (EFin \o X) by exact/measurableT_comp.
have mY : measurable_fun setT (EFin \o Y) by exact/measurableT_comp.
have [X_ [ndX_ X_X]] := approximation measurableT mX (fun t _ => X0 t).
have [Y_ [ndY_ Y_Y]] := approximation measurableT mY (fun t _ => Y0 t).
transitivity (limn (fun n => \int[P]_x ((X_ n \* Y_ n) x)%:E)).
  admit.
transitivity (limn (fun n => \int[P]_x ((X_ n) x)%:E * \int[P]_y ((Y_ n) y)%:E)).
  admit.
transitivity (\int[P]_x 'E_P [X] * \int[P]_y 'E_P [Y]).
  admit.
Admitted.

Lemma independent_RVs_expectation2 (X Y : {RV P >-> R}) :
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  independent_RV_tuple [tuple of [:: X; Y]] ->
  'E_P[X * Y] = 'E_P[X] * 'E_P[Y].
Proof.
move=> iX iY XY.
have iXY : P.-integrable setT (EFin \o (X \* Y)%R).
  admit.
have dX := funeposneg (EFin \o X).
have dY := funeposneg (EFin \o X).
Admitted.

(*
Lemma independent_RVs_expectation (X : seq {RV P >-> R}) :
  independent_RV X -> 'E_P[\prod_(Xi <- X) Xi] = \prod_(Xi <- X) 'E_P[Xi].
Proof.
elim: n X => [|n ih X iX].
  move=> X _.
  have -> : X = nil by exact/tuple0.
  by rewrite !big_nil expectation_cst.
have XE := tuple_eta X.
rewrite XE !big_cons.
rewrite independent_RVs_expectation2//; last 3 first.
  admit.
  admit.
  exact: independent_RV_tuple_thead_prod_behead.
congr *%E.
apply: (ih [tuple of behead X]).
exact: independent_RV_tuple_behead.
Admitted.
*)

End independent_product.

(* alternative formalization
Definition inde_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :=
  forall (s : I -> set R), mutually_independent P A (fun i => X i @^-1` s i).
Definition kwise_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) k :=
  forall (s : I -> set R), kwise_independent P A (fun i => X i @^-1` s i) k.
this should be equivalent according to wikipedia https://en.wikipedia.org/wiki/Independence_(probability_theory)#For_real_valued_random_variables
*)

Section real_of_bool.
Context {R : realType}.

Definition real_of_bool (b : bool) : R := b%:R.

Lemma measurable_fun_real_of_bool : measurable_fun [set: bool] real_of_bool.
Proof. by []. Qed.

Lemma real_of_bool1 : real_of_bool @^-1` [set 1%R] = [set true].
Proof.
by apply/seteqP; split => [x|x ->]; case: x => // /esym/eqP; rewrite oner_eq0.
Qed.

Lemma real_of_bool0 : real_of_bool @^-1` [set 0%R] = [set false].
Proof.
by apply/seteqP; split => [x|x ->]; case: x => //= /eqP/=; rewrite oner_eq0.
Qed.

End real_of_bool.

Section bernoulli_trial.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Definition bernoulli_RV (X : {RV P >-> R}) :=
  distribution P X = pushforward (bernoulli p) measurable_fun_real_of_bool
  /\ range X = [set 0; 1]%R.

Lemma bernoulli_RV1 (X : {RV P >-> R}) : bernoulli_RV X ->
  P [set i | X i == 1%R] == p%:E.
Proof.
move=> [/(congr1 (fun f => f [set 1%:R]))].
rewrite /bernoulli/= /pushforward ifT//.
rewrite real_of_bool1 fsbig_set1/= /distribution /= => <- _.
apply/eqP; congr (P _).
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_RV2 (X : {RV P >-> R}) : bernoulli_RV X ->
  P [set i | X i == 0%R] == (`1-p)%:E.
Proof.
move=> [/(congr1 (fun f => f [set 0%:R]))].
rewrite /bernoulli/= /pushforward ifT//.
rewrite real_of_bool0 fsbig_set1/= /distribution /= => <- _.
apply/eqP; congr (P _).
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_ge0 (X : {RV P >-> R}) : bernoulli_RV X ->
  forall t, (X t >= 0)%R.
Proof.
move=> bX t.
suff: (range X) (X t) by rewrite bX.2 => -[] ->.
by exists t.
Qed.

Lemma bernoulli_expectation (X : {RV P >-> R}) :
  bernoulli_RV X -> 'E_P[X] = p%:E.
Proof.
move=> bX.
rewrite unlock.
transitivity (\int[P]_w `|X w|%:E).
  apply: eq_integral => t _.
  by rewrite ger0_norm// bernoulli_ge0.
rewrite -(@integral_distribution _ _ _ _ _ (EFin \o normr))//; last 2 first.
  exact: measurableT_comp.
  by move=> y //=.
rewrite bX.1 ge0_integral_pushforward/=; last 2 first.
  exact: measurableT_comp.
  by move=> /= r; rewrite lee_fin.
rewrite integral_bernoulli//.
by rewrite /real_of_bool normr1 normr0 !mule0 adde0 mule1.
Qed.

Lemma bernoulli_sqr (X : {RV P >-> R}) :
  bernoulli_RV X -> bernoulli_RV (X ^+ 2 : {RV P >-> R})%R.
Proof.
rewrite /bernoulli_RV => -[Xp1 X01]; split.
  rewrite -Xp1; apply/funext => A.
  rewrite /distribution /pushforward/=; congr (P _).
  by apply/seteqP; split => [t|t];
    (have : (range X) (X t) by exists t);
    rewrite X01/= /GRing.mul/= => -[] ->; rewrite ?(mul0r,mul1r).
rewrite -X01; apply/seteqP; split => [x|x].
- move=> [t _] /=; rewrite /GRing.mul/= -expr2 => <-;
  (have : (range X) (X t) by exists t);
  by rewrite X01/= /GRing.mul/= => -[] Xt;
    exists t => //; rewrite Xt ?(expr0n,expr1n).
- move=> [t _] /=; rewrite /GRing.mul/= => <-;
  (have : (range X) (X t) by exists t);
  by rewrite X01/= => -[] Xt;
    exists t => //=; rewrite Xt/= ?(mulr0,mulr1).
Qed.

Lemma integrable_bernoulli (X : {RV P >-> R}) :
  bernoulli_RV X -> P.-integrable [set: T] (EFin \o X).
Proof.
move=> bX.
apply/integrableP; split; first by apply: measurableT_comp.
have -> : \int[P]_x `|(EFin \o X) x| = 'E_P[X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  rewrite gee0_abs //= lee_fin.
  by rewrite bernoulli_ge0//.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma bernoulli_variance (X : {RV P >-> R}) :
(* NB(rei): no need for that?
   P.-integrable setT (EFin \o X) ->
   P.-integrable [set: T] (EFin \o (X ^+ 2)%R) ->*)
  bernoulli_RV X -> 'V_P[X] = (p * (`1-p))%:E.
Proof.
move=> b.
rewrite varianceE; last 2 first.
  exact: integrable_bernoulli.
  exact: integrable_bernoulli (bernoulli_sqr b).
rewrite (bernoulli_expectation b).
have b2 := bernoulli_sqr b.
rewrite (bernoulli_expectation b2) /=.
by rewrite -EFinD mulrDr mulr1 mulrN.
Qed.

Definition is_bernoulli_trial n (X : n.-tuple {RV P >-> R}) :=
  (forall Xi, Xi \in X -> bernoulli_RV Xi) /\
  independent_RV_tuple X.

Definition bernoulli_trial (X : seq {RV P >-> R}) :=
  (\sum_(Xi <- X) Xi)%R.

Lemma expectation_bernoulli_trial n (X : n.-tuple {RV P >-> R}) :
  is_bernoulli_trial X -> 'E_P[@bernoulli_trial X] = (n%:R * p)%:E.
Proof.
move=> [bRV [_ Xn]]; rewrite expectation_sum; last first.
  by move=> Xi XiX; exact: (integrable_bernoulli (bRV _ XiX)).
under eq_big_seq => Xi XiX.
  by rewrite (bernoulli_expectation (bRV Xi _))//; over.
rewrite /= -[in RHS](size_tuple X).
rewrite -sum1_size natr_sum big_distrl/= sumEFin; congr EFin.
by under [RHS]eq_bigr do rewrite mul1r.
Qed.

Lemma bernoulli_trial_ge0 n (X : n.-tuple {RV P >-> R}) :
  is_bernoulli_trial X ->
  (forall t, 0 <= bernoulli_trial X t)%R.
Proof.
move=> [bRV Xn] t.
rewrite /bernoulli_trial [leRHS](_ : _ = \sum_(Xi <- X) Xi t)%R; last first.
  by rewrite {bRV Xn}; elim/big_ind2 : _ => //= _ f _ g <- <-.
  (* NB: this maybe need to be a lemma*)
by rewrite big_seq; apply: sumr_ge0 => i iX; exact/bernoulli_ge0/bRV.
Qed.

Lemma bernoulli_mmt_gen_fun (X : {RV P >-> R}) (t : R) :
  bernoulli_RV X -> 'E_P[expR \o t \o* X] = (p * expR t + (1-p))%:E.
Admitted.

Lemma binomial_mmt_gen_fun n (X_ : n.-tuple {RV P >-> R}) (t : R) :
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ : {RV P >-> R} in
  mmt_gen_fun X t = ((p * expR t + (1 - p)) `^ n%:R)%:E.
Proof.
rewrite /is_bernoulli_trial /independent_RV /bernoulli_trial.
move=> [bX1 [bX2 bX3]] /=.
rewrite -[LHS]fineK; last first.
  rewrite /mmt_gen_fun unlock /expectation.
  apply: integral_fune_fin_num => //.
  admit.
(* TODO(ale) *)
(*rewrite bX2 big_seq.
apply: congr1.
under eq_bigr => Xi XiX do rewrite (bernoulli_mmt_gen_fun _ (bX1 _ _))//=.*)
Admitted.

End bernoulli_trial.

Section rajani.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

(* Rajani lem 2.3 *)
Lemma lm23 n (X_ : n.-tuple {RV P >-> R}) (t : R) :
  (0 <= t)%R ->
  is_bernoulli_trial p X_ ->
  let X := bernoulli_trial X_ : {RV P >-> R} in
  let mu := 'E_P[X] in
  mmt_gen_fun X t <= (expR (fine mu * (expR t - 1)))%:E.
Proof.
rewrite /= => t0 bX.
set X := bernoulli_trial X_.
set mu := 'E_P[X].
have -> : @mmt_gen_fun _ _ _ P X t = (\prod_(Xi <- X_) fine (mmt_gen_fun Xi t))%:E.
  rewrite -[LHS]fineK; last by rewrite (binomial_mmt_gen_fun p01 _ bX).
  congr EFin.
  rewrite /mmt_gen_fun.
  transitivity (fine 'E_P[expR \o t \o* (\sum_(i < n) tnth X_ i)%R]).
    congr (fine 'E_P[ _ ]).
    apply/funext => x/=.
    congr expR.
    rewrite /X /bernoulli_trial /=.
    rewrite big_tnth//.
    admit.
  transitivity (fine 'E_P[\prod_(i < n ) (expR \o t \o* (tnth X_ i))]).
    congr (fine 'E_P[ _ ]).
    apply/funext => x/=.
    (* TODO: use expR_prod *)
    admit.
  admit.
under eq_big_seq => Xi XiX.
  have -> : @mmt_gen_fun _ _ _ P Xi t = (1 + p * (expR t - 1))%:E.
    rewrite /mmt_gen_fun.
    rewrite (bernoulli_mmt_gen_fun p01)//; last exact: bX.1.
    apply: congr1.
    by rewrite mulrBr mulr1 addrCA.
  over.
rewrite lee_fin /=.
apply: (le_trans (@ler_prod _ _ _ _ _ (fun x => expR (p * (expR t - 1)))%R _)).
  move=> Xi _.
  rewrite addr_ge0//=; last first.
    rewrite mulr_ge0//; first by case/andP : p01.
    by rewrite subr_ge0 -expR0 ler_expR.
  rewrite expR_ge1Dx// mulr_ge0//; first by case/andP : p01.
  by rewrite subr_ge0 -expR0 ler_expR.
rewrite expR_prod -mulr_suml.
move: t0; rewrite le_eqVlt => /predU1P[<-|t0].
  by rewrite expR0 subrr !mulr0.
rewrite ler_expR ler_pM2r; last first.
  by rewrite subr_gt0 -expR0 ltr_expR.
rewrite /mu big_seq expectation_sum; last first.
  by move=> Xi XiX; apply: (integrable_bernoulli p01); exact: bX.1.
rewrite big_seq -sum_fine.
  apply: ler_sum => Xi XiX; rewrite (bernoulli_expectation p01) //=.
  exact: bX.1.
by move=> Xi XiX; rewrite (bernoulli_expectation p01) //=; exact: bX.1.
Admitted.

Lemma end_thm24 n (X_ : n.-tuple {RV P >-> R}) (t delta : R) :
  is_bernoulli_trial p X_ ->
  (0 < delta)%R ->
  let X := bernoulli_trial X_ in
  let mu := 'E_P[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> bX d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite mulr_ge0// expR_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpM2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expRM lnK// posrE addr_gt0.
Qed.

(* Rajani thm 2.4 Rajani / mu-book thm 4.4.(2) *)
Theorem thm24 n (X_ : n.-tuple {RV P >-> R}) (delta : R) :
  is_bernoulli_trial p X_ ->
  (0 < delta)%R ->
  let X := bernoulli_trial X_ in
  let mu := 'E_P[X] in
  P [set i | X i >= (1 + delta) * fine mu]%R <=
    ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => bX delta0.
set X := bernoulli_trial X_.
set mu := 'E_P[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltrDl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expR (fine mu * (expR t - 1)))%:E *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  by apply: (lm23 _ bX); rewrite le_eqVlt t0 orbT.
rewrite mulrC expRM -mulNr mulrA expRM.
exact: (end_thm24 _ bX).
Qed.

(* Rajani thm 2.5 *)
Theorem poisson_ineq n (X : n.-tuple {RV P >-> R}) (delta : R) :
  is_bernoulli_trial p X ->
  let X' := bernoulli_trial X in
  let mu := 'E_P[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  P [set i | X' i >= (1 + delta) * fine mu]%R <=
    (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> bX X' mu n0 /andP[delta0 delta1].
apply: (@le_trans _ _
    (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK; last by rewrite posrE addr_gt0.
  exact: (thm24 bX).
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    rewrite fine_ge0//; apply: expectation_ge0 => t.
    exact: (bernoulli_trial_ge0 bX).
  by rewrite lerB// analytical_argument_thm26// (ltW delta0) (ltW delta1).
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

(* Rajani thm 2.6 / mu-book thm 4.5.(2) *)
Theorem thm26 n (X : n.-tuple {RV P >-> R}) (delta : R) :
  is_bernoulli_trial p X -> (0 < delta < 1)%R ->
  let X' : {RV P >-> R} := bernoulli_trial X  in
  let mu := 'E_P[X'] in
  P [set i | X' i <= (1 - delta) * fine mu]%R <=
    (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> bX /andP[delta0 delta1] /=.
set X' := bernoulli_trial X : {RV P >-> R}.
set mu := 'E_P[X'].
apply: (@le_trans _ _
    (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
      P [set i | (X' i <= (1 - delta) * fine mu)%R] =
      P [set i | `|(expR \o t \o* X') i|%:E >=
                 (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltrNr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltrBlDr ltrDl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _
      ((fine 'E_P[normr \o expR \o t \o* X']) /
       (expR (t * (1 - delta) * fine mu)))%:E).
    rewrite EFinM lee_pdivl_mulr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ P (expR \o t \o* X' : {RV P >-> R}) id
       (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - exact: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_P[expR \o t \o* X'] = mmt_gen_fun X' t by [].
      by rewrite (binomial_mmt_gen_fun p01 _ bX).
  apply: (@le_trans _ _ ((expR ((expR t - 1) * fine mu)) /
                         (expR (t * (1 - delta) * fine mu)))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_P[expR \o t \o* X'] = mmt_gen_fun X' t by [].
    rewrite (binomial_mmt_gen_fun p01 _ bX)/=.
    rewrite /mu /X' (expectation_bernoulli_trial p01 bX)/=.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expRM powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      rewrite addr_ge0// ?subr_ge0; last by case/andP : p01.
      rewrite mulr_ge0//; first by case/andP : p01.
      by rewrite subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expRM.
    rewrite addrCA -{2}(mulr1 p) -mulrBr addrAC subrr sub0r mulrC mulNr.
    apply: le01_expR_ge1Dx.
    rewrite lerNl opprK mulr_ile1//=;
      [|exact: ltW|by case/andP : p01 |exact: ltW|by case/andP : p01].
    by rewrite lerNl oppr0 mulr_ge0//; [exact: ltW|case/andP : p01].
  rewrite !lnK ?posrE ?subr_gt0//.
  rewrite -addrAC subrr sub0r -mulrA [X in (_ / X)%R]expRM lnK ?posrE ?subr_gt0//.
  rewrite -[in leRHS]powR_inv1 ?powR_ge0// powRM// ?expR_ge0 ?invr_ge0 ?powR_ge0//.
  by rewrite powRAC powR_inv1 ?powR_ge0// powRrM expRM.
rewrite lee_fin.
rewrite -mulrN -mulrA [in leRHS]mulrC expRM ge0_ler_powR// ?nnegrE.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- by rewrite expR_ge0.
- rewrite -ler_ln ?posrE ?divr_gt0 ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_div ?posrE ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK//.
  rewrite /powR (*TODO: lemma ln of powR*) gt_eqF ?subr_gt0// expRK.
  apply: analytical_argument_thm22.
  by rewrite (ltW delta0) (ltW delta1).
Qed.

(* Rajani corollary 2.7 / mu-book -> corollary 4.6 *)
Corollary cor27 n (X : n.-tuple {RV P >-> R}) (delta : R) :
  is_bernoulli_trial p X -> (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (p != 0)%R ->
  let X' := bernoulli_trial X in
  let mu := 'E_P[X'] in
  P [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
    (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> bX /andP[d0 d1] n0 p0 /=.
set X' := bernoulli_trial X.
set mu := 'E_P[X'].
under eq_set => x.
  rewrite ler_normr.
  rewrite lerBrDl opprD opprK -{1}(mul1r (fine mu)) -mulrDl.
  rewrite -lerBDr -(lerN2 (- _)%R) opprK opprB.
  rewrite -{2}(mul1r (fine mu)) -mulrBl.
  rewrite -!lee_fin.
  over.
rewrite /=.
rewrite set_orb.
rewrite measureU; last 3 first.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  exact: measurableT_comp.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  exact: measurableT_comp.
- rewrite disjoints_subset => x /=.
  rewrite /mem /in_mem/= => X0; apply/negP.
  rewrite -ltNge.
  apply: (@lt_le_trans _ _ _ _ _ _ X0).
  rewrite !EFinM.
  rewrite lte_pmul2r//; first by rewrite lte_fin ltrD2l gt0_cp.
  rewrite fineK /mu/X' (expectation_bernoulli_trial p01 bX)// lte_fin.
  by rewrite mulr_gt0// ?ltr0n// lt_neqAle eq_sym p0; case/andP : p01.
rewrite mulr2n EFinD leeD//=.
- by apply: (poisson_ineq bX); rewrite //d0 d1.
- apply: (le_trans (@thm26 _ _ delta bX _)); first by rewrite d0 d1.
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  by rewrite /X' lee_fin; apply: (bernoulli_trial_ge0 bX).
Qed.

(* Rajani thm 3.1 / mu-book thm 4.7 *)
Theorem sampling n (X : n.-tuple {RV P >-> R}) (theta delta : R) :
  let X_sum := bernoulli_trial X in
  let X' x := (X_sum x) / n%:R in
  p != 0%R ->
  is_bernoulli_trial p X ->
  (0 < delta <= 1)%R -> (0 < theta < p)%R -> (0 < n)%N ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  P [set i | `| X' i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X_sum X' p0 bX /andP[delta0 delta1] /andP[theta0 thetap] n0 tdn.
have E_X_sum: 'E_P[X_sum] = (p * n%:R)%:E.
  rewrite expectation_sum/=; last first.
    by move=> Xi XiX; exact: integrable_bernoulli (bX.1 Xi XiX).
  rewrite big_seq.
  under eq_bigr.
    move=> Xi XiX; rewrite (bernoulli_expectation p01 (bX.1 _ XiX)); over.
  rewrite /= -[in RHS](size_tuple X).
  by rewrite -sum1_size natr_sum big_distrr/= sumEFin mulr1 -big_seq.
set epsilon := theta / p.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r//;
    rewrite lt_neqAle eq_sym p0; case/andP : p01.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : P [set i | `| X' i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in P X <= _](_ : _ =
      [set i | `| X_sum i - p * n%:R | >= epsilon * p * n%:R]%R); last first.
    apply/seteqP; split => [t|t]/=.
      move/(@ler_wpM2r _ n%:R (ler0n _ _)) => /le_trans; apply.
      rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R)// -normrM mulrBl.
      by rewrite -mulrA mulVf ?mulr1// gt_eqF ?ltr0n.
    move/(@ler_wpM2r _ n%:R^-1); rewrite invr_ge0// ler0n => /(_ erefl).
    rewrite -(mulrA _ _ n%:R^-1) divff ?mulr1 ?gt_eqF ?ltr0n//.
    move=> /le_trans; apply.
    rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R^-1)// -normrM mulrBl.
    by rewrite -mulrA divff ?mulr1// gt_eqF// ltr0n.
  rewrite -mulrA.
  have -> : (p * n%:R)%R = fine (p * n%:R)%:E by [].
  rewrite -E_X_sum.
  exact: (@cor27 _ X epsilon bX).
have step2 : P [set i | `| X' i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![leRHS]mulrA.
  rewrite [leRHS]mulrCA.
  rewrite -[leLHS]mulrA.
  rewrite ler_wpM2l//.
  rewrite (mulrC epsilon) exprMn -mulrA ler_wpM2r//.
    by rewrite divr_ge0// sqr_ge0.
  by rewrite expr2 ler_piMl//; case/andP : p01.
suff : delta%:E >= P [set i | (`|X' i - p| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in P X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p| < theta)%R]); last first.
    apply/seteqP; split => [t|t]/=.
      by rewrite leNgt => /negP.
    by rewrite ltNge => /negP/negPn.
  have ? : measurable [set i | (`|X' i - p| < theta)%R].
    under eq_set => x do rewrite -lte_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_lt => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  rewrite probability_setC// lee_subel_addr//.
  rewrite -lee_subel_addl//; last by rewrite fin_num_measure.
  move=> /le_trans; apply.
  rewrite le_measure ?inE//.
    under eq_set => x do rewrite -lee_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_le => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  by move=> t/= /ltW.
(* NB: last step in the pdf *)
apply: (le_trans step2).
rewrite lee_fin -(mulr_natr _ 2) -ler_pdivlMr//.
rewrite -(@lnK _ (delta / 2)); last by rewrite posrE divr_gt0.
rewrite ler_expR mulNr lerNl -lnV; last by rewrite posrE divr_gt0.
rewrite invf_div ler_pdivlMr// mulrC.
rewrite -ler_pdivrMr; last by rewrite exprn_gt0.
by rewrite mulrAC.
Qed.

End rajani.
