(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop reals.
From mathcomp Require Import interval_inference ereal topology normedtype.
From mathcomp Require Import sequences esum numfun.
From mathcomp Require Import measurable_structure measure_function.
From mathcomp Require Import measure_negligible.

(**md**************************************************************************)
(* # Measure Extension                                                        *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* ## Measure Extension Theorem:                                              *)
(*                                                                            *)
(* This file provides the Measure Extension theorem that builds a measure     *)
(* given a function defined over a semiring of sets, the intermediate outer   *)
(* measure being                                                              *)
(* $\inf_F\{ \sum_{k=0}^\infty \mu(F_k)  | X \subseteq \bigcup_k F_k\}.$      *)
(*                                                                            *)
(* ```                                                                        *)
(*      sigma_subadditive mu == predicate defining sigma-subadditivity        *)
(* {outer_measure set T -> \bar R} == type of an outer measure over sets      *)
(*                              of elements of type T : Type where R is       *)
(*                              expected to be a numFieldType                 *)
(*                              The HB class is OuterMeasure.                 *)
(*                              interfaces: isOuterMeasure,                   *)
(*                              isSubsetOuterMeasure                          *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*      mu.-caratheodory == the set of Caratheodory measurable sets for the   *)
(*                          outer measure mu, i.e., sets A such that          *)
(*                          forall B, mu A = mu (A `&` B) + mu (A `&` ~` B)   *)
(*  caratheodory_type mu := T, where mu : {outer_measure set T -> \bar R}     *)
(*                          It is a canonical measurableType copy of T.       *)
(*                          The restriction of the outer measure mu to the    *)
(*                          sigma algebra of Caratheodory measurable sets is  *)
(*                          a measure.                                        *)
(*                          Remark: sets that are negligible for              *)
(*                          this measure are Caratheodory measurable.         *)
(* mu .-cara.-measurable == sigma-algebra of Caratheodory measurable sets     *)
(* ```                                                                        *)
(*                                                                            *)
(* From a premeasure to an outer measure (Measure Extension Theorem part 1):  *)
(* ```                                                                        *)
(*    measurable_cover X == the set of sequences F such that                  *)
(*                          - forall k, F k is measurable                     *)
(*                          - X `<=` \bigcup_k (F k)                          *)
(*                  mu^* == extension of the measure mu over a semiring of    *)
(*                          sets (it is an outer measure)                     *)
(* ```                                                                        *)
(*                                                                            *)
(* From an outer measure to a measure (Measure Extension Theorem part 2):     *)
(* ```                                                                        *)
(*  measure_extension mu == extension of the content mu over a                *)
(*                          semiring of sets to a measure over the            *)
(*                          generated sigma algebra (requires a proof of      *)
(*                          sigma-sub-additivity)                             *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* completed_measure_extension mu == similar to measure_extension but returns *)
(*                            a complete measure                              *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

(*Reserved Notation "{ 'outer_measure' fUV }" (format "{ 'outer_measure'  fUV }").
Reserved Notation "[ 'outer_measure' 'of' f 'as' g ]"
  (format "[ 'outer_measure'  'of'  f  'as'  g ]").
Reserved Notation "[ 'outer_measure' 'of' f ]"
  (format "[ 'outer_measure'  'of'  f ]").*)
Reserved Notation "{ 'outer_measure' 'set' T '->' '\bar' R }"
  (T at level 37, format "{ 'outer_measure'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "mu .-caratheodory" (format "mu .-caratheodory").
Reserved Notation "mu .-cara" (format "mu .-cara").
Reserved Notation "mu .-cara.-measurable" (format "mu .-cara.-measurable").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Open Scope ereal_scope.

Definition sigma_subadditive {T} {R : numFieldType}
  (mu : set T -> \bar R) := forall (F : (set T) ^nat),
  mu (\bigcup_n (F n)) <= \sum_(i <oo) mu (F i).

HB.mixin Record isOuterMeasure
    (R : numFieldType) (T : Type) (mu : set T -> \bar R) := {
  outer_measure0 : mu set0 = 0 ;
  outer_measure_ge0 : forall x, 0 <= mu x ;
  le_outer_measure : {homo mu : A B / A `<=` B >-> A <= B} ;
  outer_measure_sigma_subadditive : sigma_subadditive mu }.

#[short(type=outer_measure)]
HB.structure Definition OuterMeasure (R : numFieldType) (T : Type) :=
  {mu & isOuterMeasure R T mu}.

Notation "{ 'outer_measure' 'set' T '->' '\bar' R }" := (outer_measure R T)
  : ring_scope.

#[global] Hint Extern 0 (_ set0 = 0%R) => solve [apply: outer_measure0] : core.
#[global] Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

Arguments outer_measure0 {R T} _.
Arguments outer_measure_ge0 {R T} _.
Arguments le_outer_measure {R T} _.
Arguments outer_measure_sigma_subadditive {R T} _.

HB.factory Record isSubsetOuterMeasure
    (R : realType) (T : Type) (mu : set T -> \bar R) := {
  outer_measure0 : mu set0 = 0 ;
  outer_measure_ge0 : forall x, 0 <= mu x ;
  subset_outer_measure_sigma_subadditive :
    forall A F, subset_sigma_subadditive mu A F}.

HB.builders Context {R : realType} T mu of isSubsetOuterMeasure R T mu.

Lemma le_outer_measure : {homo mu : A B / A `<=` B >-> A <= B}.
Proof.
move=> A B AB; pose B_ k := if k is 0%N then B else set0.
have -> : mu B = \sum_(n <oo) mu (B_ n).
  rewrite nneseries_recl//; last by move=> *; rewrite outer_measure_ge0.
  rewrite eseries_cond/= eseries0 ?adde0// => -[|]//= k _ _.
  by rewrite outer_measure0.
apply: subset_outer_measure_sigma_subadditive => //.
by rewrite bigcup_recl/= bigcup0 ?setU0// => -[/negP|].
Qed.

Lemma outer_measure_sigma_subadditive : sigma_subadditive mu.
Proof. by move=> F; exact: subset_outer_measure_sigma_subadditive. Qed.

HB.instance Definition _ := isOuterMeasure.Build R T mu outer_measure0
  outer_measure_ge0 le_outer_measure outer_measure_sigma_subadditive.

HB.end.

Lemma outer_measure_sigma_subadditive_tail (T : Type) (R : realType)
    (mu : {outer_measure set T -> \bar R}) N (F : (set T) ^nat) :
  (mu (\bigcup_(n in ~` `I_N) (F n)) <= \sum_(N <= i <oo) mu (F i))%E.
Proof.
rewrite bigcup_mkcond.
have := outer_measure_sigma_subadditive mu
  (fun n => if n \in ~` `I_N then F n else set0).
move/le_trans; apply.
rewrite [in leRHS]eseries_cond [in leRHS]eseries_mkcondr; apply: lee_nneseries.
- by move=> k _ _; exact: outer_measure_ge0.
- move=> k _; rewrite fun_if; case: ifPn => Nk; first by rewrite mem_not_I Nk.
  by rewrite mem_not_I (negbTE Nk) outer_measure0.
Qed.

Section outer_measureU.
Context (T : Type) (R : realType).
Variable mu : {outer_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma outer_measure_subadditive (F : (set T)^nat) n :
  mu (\big[setU/set0]_(i < n) F i) <= \sum_(i < n) mu (F i).
Proof.
pose F' := fun k => if (k < n)%N then F k else set0.
rewrite -(big_mkord xpredT F) big_nat (eq_bigr F')//; last first.
  by move=> k /= kn; rewrite /F' kn.
rewrite -big_nat big_mkord.
have := outer_measure_sigma_subadditive mu F'.
rewrite (bigcup_splitn n) (_ : bigcup _ _ = set0) ?setU0; last first.
  by rewrite bigcup0 // => k _; rewrite /F' /= ltnNge leq_addr.
move/le_trans; apply.
rewrite (nneseries_split _ n); last by move=> ? ?; exact: outer_measure_ge0.
rewrite [X in _ + X]eseries0 ?adde0; last first.
  by move=> k nk _; rewrite /F' ltnNge nk/= outer_measure0.
by rewrite big_mkord; apply: lee_sum => i _; rewrite /F' ltn_ord.
Qed.

Lemma outer_measureU2 A B : mu (A `|` B) <= mu A + mu B.
Proof.
have := outer_measure_subadditive (bigcup2 A B) 2.
by rewrite !big_ord_recl/= !big_ord0 setU0 adde0.
Qed.

End outer_measureU.

Local Open Scope ereal_scope.
Lemma le_outer_measureIC (R : realFieldType) T
  (mu : {outer_measure set T -> \bar R}) (A X : set T) :
  mu X <= mu (X `&` A) + mu (X `&` ~` A).
Proof.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have cvg_mu : (fun n => \sum_(i < n) mu (B i)) @ \oo --> mu (B 0%N) + mu (B 1%N).
  rewrite -2!cvg_shiftS /=.
  rewrite [X in X @ \oo --> _](_ : _ = (fun=> mu (B 0%N) + mu (B 1%N))); last first.
    rewrite funeqE => i; rewrite 2!big_ord_recl /= big1 ?adde0 // => j _.
    by rewrite /B /bigcup2 /=.
  exact: cvg_cst.
have := outer_measure_sigma_subadditive mu B.
suff : \bigcup_n B n = X.
  move=> -> /le_trans; apply; under eq_fun do rewrite big_mkord.
  by rewrite (cvg_lim _ cvg_mu).
transitivity (\big[setU/set0]_(i < 2) B i).
  by rewrite (bigcup_splitn 2) // -bigcup_mkord setUidl// => t -[].
by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIUr setUCr setIT.
Unshelve. all: by end_near. Qed.
Local Close Scope ereal_scope.

Definition caratheodory_measurable (R : realType) (T : Type)
  (mu : set T -> \bar R) (A : set T) := forall X,
  mu X = mu (X `&` A) + mu (X `&` ~` A).

Notation "mu .-caratheodory" :=
   (caratheodory_measurable mu) : classical_set_scope.

Lemma le_caratheodory_measurable (R : realType) T
  (mu : {outer_measure set T -> \bar R}) (A : set T) :
  (forall X, mu (X `&` A) + mu (X `&` ~` A) <= mu X)%E ->
  mu.-caratheodory A.
Proof.
move=> suf X; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: le_outer_measureIC | exact: suf].
Qed.

Section caratheodory_theorem_sigma_algebra.
Local Open Scope ereal_scope.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> \bar R}).

Lemma outer_measure_bigcup_lim (A : (set T) ^nat) X :
  mu (X `&` \bigcup_k A k) <= \sum_(k <oo) mu (X `&` A k).
Proof.
apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
by apply/le_outer_measure; rewrite setI_bigcupr.
Qed.

Let M := mu.-caratheodory.

Lemma caratheodory_measurable_set0 : M set0.
Proof. by move=> X /=; rewrite setI0 outer_measure0 add0e setC0 setIT. Qed.

Lemma caratheodory_measurable_setC A : M A -> M (~` A).
Proof. by move=> MA X; rewrite setCK addeC -MA. Qed.

Lemma caratheodory_measurable_setU_le (X A B : set T) :
  mu.-caratheodory A -> mu.-caratheodory B ->
  mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <= mu X.
Proof.
move=> mA mB; pose Y := X `&` A `|` X `&` B `&` ~` A.
have /(leeD2r (mu (X `&` ~` (A `|` B)))) :
    mu Y <= mu (X `&` A) + mu (X `&` B `&` ~` A).
  pose Z := bigcup2 (X `&` A) (X `&` B `&` ~` A).
  have -> : Y = \bigcup_k Z k.
    rewrite predeqE => t; split=> [[?|?]|[]]; [by exists O|by exists 1%N|].
    by move=> [_ ?|[_ ?|//]]; [left|right].
  rewrite (le_trans (outer_measure_sigma_subadditive mu Z))//.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply/cvg_lim => //; rewrite -(cvg_shiftn 2)/=; apply: cvg_near_cst.
  apply: nearW => k; rewrite big_mkord addn2 2!big_ord_recl big1 ?adde0//.
  by move=> ? _; exact: outer_measure0.
have /le_trans : mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <=
    mu Y + mu (X `&` ~` (A `|` B)).
  rewrite setIUr (_ : X `&` A `|` X `&` B = Y) //.
  rewrite /Y -[in LHS](setIT B) -(setUCr A) 2!setIUr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply: subIset; right.
suff -> : mu (X `&` A) + mu (X `&` B `&` ~` A) +
    mu (X `&` (~` (A `|` B))) = mu X by exact.
by rewrite setCU setIA -(setIA X) setICA (setIC B) -addeA -mB -mA.
Qed.

Lemma caratheodory_measurable_setU A B : M A -> M B -> M (A `|` B).
Proof.
move=> mA mB X; apply/eqP; rewrite eq_le.
by rewrite le_outer_measureIC andTb caratheodory_measurable_setU_le.
Qed.

Lemma caratheodory_measurable_bigsetU (A : (set T) ^nat) :
  (forall n, M (A n)) -> forall n, M (\big[setU/set0]_(i < n) A i).
Proof.
move=> MA n; elim/big_ind : _ => //; first exact: caratheodory_measurable_set0.
exact: caratheodory_measurable_setU.
Qed.

Lemma caratheodory_measurable_setI A B : M A -> M B -> M (A `&` B).
Proof.
move=> mA mB; rewrite -(setCK A) -(setCK B) -setCU.
by apply/caratheodory_measurable_setC/caratheodory_measurable_setU;
  exact/caratheodory_measurable_setC.
Qed.

Lemma caratheodory_measurable_setD A B : M A -> M B -> M (A `\` B).
Proof.
move=> mA mB; rewrite setDE; apply: caratheodory_measurable_setI => //.
exact: caratheodory_measurable_setC.
Qed.

Section additive_ext_lemmas.
Variable A B : set T.
Hypothesis (mA : M A) (mB : M B).

Let caratheodory_decomp X :
  mu X = mu (X `&` A `&` B) + mu (X `&` A `&` ~` B) +
         mu (X `&` ~` A `&` B) + mu (X `&` ~` A `&` ~` B).
Proof. by rewrite mA mB [X in _ + _ + X = _]mB addeA. Qed.

(* TODO: not used? *)
Let caratheodory_decompIU X : mu (X `&` (A `|` B)) =
  mu (X `&` A `&` B) + mu (X `&` ~` A `&` B) + mu (X `&` A `&` ~` B).
Proof.
rewrite caratheodory_decomp -!addeA; congr (mu _ + _).
  rewrite -!setIA; congr (_ `&` _).
  by rewrite setIC; apply/setIidPl; apply: subIset; left; exact: subsetUl.
rewrite addeA addeC [X in mu X + _](_ : _ = set0); last first.
  by rewrite -setIA -setCU -setIA setICr setI0.
rewrite outer_measure0 add0e addeC -!setIA; congr (mu (X `&` _) + mu (X `&` _)).
  by rewrite setIC; apply/setIidPl; apply: subIset; right; exact: subsetUr.
by rewrite setIC; apply/setIidPl; apply: subIset; left; exact: subsetUl.
Qed.

Lemma disjoint_caratheodoryIU X : [disjoint A & B] ->
  mu (X `&` (A `|` B)) = mu (X `&` A) + mu (X `&` B).
Proof.
move=> /eqP AB; rewrite caratheodory_decomp -setIA AB setI0 outer_measure0.
rewrite add0e addeC -setIA -setCU -setIA setICr setI0 outer_measure0 add0e.
rewrite -!setIA; congr (mu (X `&` _ ) + mu (X `&` _)).
rewrite (setIC A) setIA setIC; apply/setIidPl.
- by rewrite setIUl setICr setU0 subsetI; move/disjoints_subset in AB; split.
- rewrite setIA setIC; apply/setIidPl; rewrite setIUl setICr set0U.
  by move: AB; rewrite setIC => /disjoints_subset => AB; rewrite subsetI; split.
Qed.

End additive_ext_lemmas.

Lemma caratheodory_additive (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall n X,
    mu (X `&` \big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (X `&` A i).
Proof.
move=> MA ta; elim=> [|n ih] X; first by rewrite !big_ord0 setI0 outer_measure0.
rewrite big_ord_recr /= disjoint_caratheodoryIU // ?ih ?big_ord_recr //.
- exact: caratheodory_measurable_bigsetU.
- by apply/eqP/(@trivIset_bigsetUI _ predT) => //; rewrite /predT /= trueE.
Qed.

Lemma caratheodory_lime_le (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall X,
  \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` (\bigcup_k A k)) <= mu X.
Proof.
move=> MA tA X.
set A' := \bigcup_k A k; set B := fun n => \big[setU/set0]_(k < n) (A k).
suff : forall n, \sum_(k < n) mu (X `&` A k) + mu (X `&` ~` A') <= mu X.
  move=> XA; rewrite (_ : limn _ = ereal_sup
      ((fun n => \sum_(k < n) mu (X `&` A k)) @` setT)); last first.
    under eq_fun do rewrite big_mkord.
    apply/cvg_lim => //; apply: ereal_nondecreasing_cvgn.
    apply: (lee_sum_nneg_ord (fun n => mu (X `&` A n)) xpredT) => n _.
    exact: outer_measure_ge0.
  move XAx : (mu (X `&` ~` A')) => [x| |].
  - rewrite -leeBrDr //; apply: ge_ereal_sup => /= _ [n _] <-.
    by rewrite EFinN leeBrDr // -XAx XA.
  - suff : mu X = +oo by move=> ->; rewrite leey.
    by apply/eqP; rewrite -leye_eq -XAx le_outer_measure.
  - by rewrite addeNy leNye.
move=> n.
apply: (@le_trans _ _ (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` B n))).
  apply/leeD2l/le_outer_measure; apply: setIS; exact/subsetC/bigsetU_bigcup.
rewrite [in leRHS](caratheodory_measurable_bigsetU MA n) leeD2r//.
by rewrite caratheodory_additive.
Qed.

Lemma caratheodory_measurable_trivIset_bigcup (A : (set T) ^nat) :
  (forall n, M (A n)) -> trivIset setT A -> M (\bigcup_k (A k)).
Proof.
move=> MA tA; apply: le_caratheodory_measurable => X /=.
have /(leeD2r (mu (X `&` ~` (\bigcup_k A k)))) := outer_measure_bigcup_lim A X.
by move/le_trans; apply; exact: caratheodory_lime_le.
Qed.

Lemma caratheodory_measurable_bigcup (A : (set T) ^nat) : (forall n, M (A n)) ->
  M (\bigcup_k (A k)).
Proof.
move=> MA; rewrite -eq_bigcup_seqD_bigsetU.
apply/caratheodory_measurable_trivIset_bigcup; last first.
  by apply: trivIset_seqD => m n mn; exact/subsetPset/subset_bigsetU.
by case=> [|n /=]; [| apply/caratheodory_measurable_setD => //];
  exact/caratheodory_measurable_bigsetU.
Qed.

End caratheodory_theorem_sigma_algebra.

Definition caratheodory_type (R : realType) (T : Type)
  (mu : set T -> \bar R) := T.

Notation "mu .-cara.-measurable" :=
  (measurable : set (set (caratheodory_type mu))) : classical_set_scope.

Definition caratheodory_display R T : (set T -> \bar R) -> measure_display.
Proof. exact. Qed.

Notation "mu .-cara" := (caratheodory_display mu) : measure_display_scope.

Section caratheodory_sigma_algebra.
Variables (R : realType) (T : pointedType) (mu : {outer_measure set T -> \bar R}).

HB.instance Definition _ := Pointed.on (caratheodory_type mu).
HB.instance Definition _ := @isMeasurable.Build (caratheodory_display mu)
  (caratheodory_type mu) mu.-caratheodory
    (caratheodory_measurable_set0 mu)
    (@caratheodory_measurable_setC _ _ mu)
    (@caratheodory_measurable_bigcup _ _ mu).

End caratheodory_sigma_algebra.

Section caratheodory_measure.
Local Open Scope ereal_scope.
Variables (R : realType) (T : pointedType).
Variable mu : {outer_measure set T -> \bar R}.
Let U := caratheodory_type mu.

Lemma caratheodory_measure0 : mu (set0 : set U) = 0.
Proof. exact: outer_measure0. Qed.

Lemma caratheodory_measure_ge0 (A : set U) : 0 <= mu A.
Proof. exact: outer_measure_ge0. Qed.

Lemma caratheodory_measure_sigma_additive :
  semi_sigma_additive (mu : set U -> _).
Proof.
move=> A mA tA mbigcupA; set B := \bigcup_k A k.
suff : forall X, mu X = \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` B).
  move/(_ B); rewrite setICr outer_measure0 adde0.
  rewrite (_ : (fun n => _) = fun n => \sum_(k < n) mu (A k)); last first.
    rewrite funeqE => n; rewrite big_mkord; apply: eq_bigr => i _; congr (mu _).
    by rewrite setIC; apply/setIidPl; exact: bigcup_sup.
  move=> ->.
  have := fun n (_ : xpredT n) (_ : xpredT n) => outer_measure_ge0 mu (A n).
  move/(@is_cvg_nneseries _ _ _ 0) => /cvg_ex[l] hl.
  under [in X in _ --> X]eq_fun do rewrite -(big_mkord xpredT (mu \o A)).
  by move/cvg_lim : (hl) => ->.
move=> X.
have mB : mu.-cara.-measurable B := caratheodory_measurable_bigcup mA.
apply/eqP; rewrite eq_le (caratheodory_lime_le mA tA X) andbT.
have /(leeD2r (mu (X `&` ~` B))) := outer_measure_bigcup_lim mu A X.
by rewrite -le_caratheodory_measurable // => ?; rewrite -mB.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  (mu : set (caratheodory_type mu) -> _)
  caratheodory_measure0 caratheodory_measure_ge0
  caratheodory_measure_sigma_additive.

Lemma measure_is_complete_caratheodory :
  measure_is_complete (mu : set (caratheodory_type mu) -> _).
Proof.
move=> B [A [mA muA0 BA]]; apply: le_caratheodory_measurable => X.
suff -> : mu (X `&` B) = 0.
  by rewrite add0e le_outer_measure //; apply: subIset; left.
have muB0 : mu B = 0.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  by apply: (le_trans (le_outer_measure mu _ _ BA)); rewrite -muA0.
apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
have : X `&` B `<=` B by apply: subIset; right.
by move/(le_outer_measure mu); rewrite muB0 => ->.
Qed.

End caratheodory_measure.

Section measurable_cover.
Context d (T : semiRingOfSetsType d).
Implicit Types (X : set T) (F : (set T)^nat).

Definition measurable_cover X := [set F : (set T)^nat |
  (forall i, measurable (F i)) /\ X `<=` \bigcup_k (F k)].

Lemma cover_measurable X F : measurable_cover X F -> forall k, measurable (F k).
Proof. by move=> + k; rewrite /measurable_cover => -[] /(_ k). Qed.

Lemma cover_subset X F : measurable_cover X F -> X `<=` \bigcup_k (F k).
Proof. by case. Qed.

End measurable_cover.

Section outer_measure_construction.
Local Open Scope ereal_scope.
Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : set T -> \bar R.
Hypothesis (measure0 : mu set0 = 0) (measure_ge0 : forall X, mu X >= 0).
Hint Resolve measure_ge0 measure0 : core.

Definition mu_ext (X : set T) : \bar R :=
  ereal_inf [set \sum_(k <oo) mu (A k) | A in measurable_cover X].
Local Notation "mu^*" := mu_ext.

Lemma le_mu_ext : {homo mu^* : A B / A `<=` B >-> A <= B}.
Proof.
move=> A B AB; apply/ereal_inf_le_tmp => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_ge0 A : 0 <= mu^* A.
Proof.
apply: le_ereal_inf_tmp => x [B [mB AB] <-{x}]; rewrite lime_ge //=.
  exact: is_cvg_nneseries.
by near=> n; rewrite sume_ge0.
Unshelve. all: by end_near. Qed.

Lemma mu_ext0 : mu^* set0 = 0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last exact/mu_ext_ge0.
rewrite /mu_ext; apply: ereal_inf_lbound; exists (fun=> set0); first by split.
by apply: lim_near_cst => //; near=> n => /=; rewrite big1.
Unshelve. all: by end_near. Qed.

Lemma mu_ext_sigma_subadditive : sigma_subadditive mu^*.
Proof.
move=> A; have [[i ioo]|] := pselect (exists i, mu^* (A i) = +oo).
  rewrite (eseries_pinfty _ _ ioo) ?leey// => n _.
  by rewrite -ltNye (lt_le_trans _ (mu_ext_ge0 _)).
rewrite -forallNE => Aoo.
suff add2e (e : {posnum R}) :
    mu^* (\bigcup_n A n) <= \sum_(i <oo) mu^* (A i) + e%:num%:E.
  by apply/lee_addgt0Pr => _/posnumP[].
rewrite (le_trans _ (epsilon_trick _ _ _))//; last first.
  by move=> n; exact: mu_ext_ge0.
pose P n (B : (set T)^nat) := measurable_cover (A n) B /\
  \sum_(k <oo) mu (B k) <= mu^* (A n) + (e%:num / (2 ^ n.+1)%:R)%:E.
have [G PG] : {G : ((set T)^nat)^nat & forall n, P n (G n)}.
  apply: (@choice _ _ P) => n; rewrite /P /mu_ext.
  set S := (X in ereal_inf X); move infS : (ereal_inf S) => iS.
  case: iS infS => [r Sr|Soo|Soo].
  - have en1 : (0 < e%:num / (2 ^ n.+1)%:R)%R by [].
    have /(lb_ereal_inf_adherent en1) : ereal_inf S \is a fin_num by rewrite Sr.
    move=> [x [B [mB AnB muBx] xS]].
    by exists B; split => //; rewrite muBx -Sr; exact/ltW.
  - by have := Aoo n; rewrite /mu^* Soo.
  - suff : lbound S 0 by move/le_ereal_inf_tmp; rewrite Soo.
    by move=> /= _ [B [mB AnB] <-]; exact: nneseries_ge0.
have muG_ge0 x : 0 <= (mu \o uncurry G) x by exact: measure_ge0.
apply: (@le_trans _ _ (\esum_(i in setT) (mu \o uncurry G) i)).
  rewrite /mu_ext; apply: ereal_inf_lbound => /=.
  have /card_esym/ppcard_eqP[f] := card_nat2.
  exists (uncurry G \o f).
    split => [i|]; first exact/measurable_uncurry/(PG (f i).1).1.1.
    apply: (@subset_trans _  (\bigcup_n \bigcup_k G n k)) => [t [i _]|].
      by move=> /(cover_subset (PG i).1) -[j _ ?]; exists i => //; exists j.
    move=> t [i _ [j _ Bijt]]; exists (f^-1%FUN (i, j)) => //=.
    by rewrite invK ?inE.
  rewrite -(esum_pred_image (mu \o uncurry G) _ xpredT) ?[fun=> _]set_true//.
  by rewrite image_eq.
rewrite (_ : esum _ _ = \sum_(i <oo) \sum_(j <oo ) mu (G i j)); last first.
  pose J : nat -> set (nat * nat) := fun i => [set (i, j) | j in setT].
  rewrite (_ : setT = \bigcup_k J k); last first.
    by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b.
  rewrite esum_bigcupT /=; last 2 first.
    - apply/trivIsetP => i j _ _ ij.
      rewrite predeqE => -[n m] /=; split => //= -[] [_] _ [<-{n} _].
      by move=> [m' _] [] /esym/eqP; rewrite (negbTE ij).
    - by move=> /= [n m]; apply: measure_ge0; exact: (cover_measurable (PG n).1).
  rewrite -(image_id [set: nat]) -fun_true esum_pred_image//; last first.
    by move=> n _; exact: esum_ge0.
  apply: eq_eseriesr => /= j _.
  rewrite -(esum_pred_image (mu \o uncurry G) (pair j) predT)//=; last first.
    by move=> ? ? _ _; exact: (@can_inj _ _ _ snd).
  by congr esum; rewrite predeqE => -[a b]; split; move=> [i _ <-]; exists i.
apply: lee_lim.
- apply: is_cvg_nneseries => n *.
  by apply: nneseries_ge0 => m *; exact: (muG_ge0 (n, m)).
- by apply: is_cvg_nneseries => n *; apply: adde_ge0 => //; exact: mu_ext_ge0.
- by near=> n; apply: lee_sum => i _; exact: (PG i).2.
Unshelve. all: by end_near. Qed.

End outer_measure_construction.

Declare Scope measure_scope.
Delimit Scope measure_scope with mu.
Notation "mu ^*" := (mu_ext mu) : measure_scope.
Local Open Scope measure_scope.

Section outer_measure_of_content.
Context d (R : realType) (T : semiRingOfSetsType d).
Variable mu : {content set T -> \bar R}.

HB.instance Definition _ := isOuterMeasure.Build
  R T _ (@mu_ext0 _ _ _ _ (measure0 mu) (measure_ge0 mu))
      (mu_ext_ge0 (measure_ge0 mu))
      (le_mu_ext mu)
      (mu_ext_sigma_subadditive (measure_ge0 mu)).

End outer_measure_of_content.

Section Rmu_ext.
Import SetRing.
Local Open Scope measure_scope.

Lemma Rmu_ext d (R : realType) (T : semiRingOfSetsType d)
    (mu : {content set T -> \bar R}) :
  (measure mu)^* = mu^*.
Proof.
apply/funeqP => /= X; rewrite /mu_ext/=; apply/eqP; rewrite eq_le.
rewrite !le_ereal_inf_tmp// => _ [F [Fm XS] <-]; rewrite ereal_inf_lbound//; last first.
  exists F; first by split=> // i; exact: sub_gen_smallest.
  by rewrite (eq_eseriesr (fun _ _ => RmuE _ (Fm _))).
pose K := [set: nat] `*`` fun i => decomp (F i).
have /ppcard_eqP[f] : (K #= [set: nat])%card.
  apply: cardXR_eq_nat => // i; split; last by apply/set0P; rewrite decompN0.
  by apply: finite_set_countable => //; exact: decomp_finite_set.
pose g i := (f^-1%FUN i).2; exists g; first split.
- move=> k; have [/= _ /mem_set] : K (f^-1%FUN k) by apply: funS.
  exact: decomp_measurable.
- move=> i /XS [k _]; rewrite -[F k]cover_decomp => -[D /= DFk Di].
  by exists (f (k, D)) => //; rewrite /g invK// inE.
rewrite !nneseries_esumT//= /measure.
transitivity (\esum_(i in setT) \sum_(X0 \in decomp (F i)) mu X0); last first.
  by apply: eq_esum => /= k _; rewrite fsbig_finite//; exact: decomp_finite_set.
rewrite -(eq_esum (fun _ _ => esum_fset _ _))//; last first.
  by move=> ? _; exact: decomp_finite_set.
rewrite esum_esum//= (reindex_esum K setT f) => //=.
by apply: eq_esum => i Ki; rewrite /g funK ?inE.
Qed.

End Rmu_ext.

Local Open Scope measure_scope.
Lemma measurable_mu_extE d (R : realType) (T : semiRingOfSetsType d)
    (mu : {measure set T -> \bar R}) X :
  measurable X -> mu^* X = mu X.
Proof.
move=> mX; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ereal_inf_lbound; exists (fun n => if n is 0%N then X else set0).
    by split=> [[]// _|t Xt]; exists 0%N.
  apply/cvg_lim => //; rewrite -cvg_shiftS.
  rewrite (_ : [sequence _]_n = cst (mu X)); first exact: cvg_cst.
  by rewrite funeqE => n /=; rewrite big_nat_recl//= big1 ?adde0.
apply/le_ereal_inf_tmp => x [A [mA XA] <-{x}].
have XUA : X = \bigcup_n (X `&` A n).
  rewrite predeqE => t; split => [Xt|[i _ []//]].
  by have [i _ Ait] := XA _ Xt; exists i.
apply: (@le_trans _ _ (\sum_(i <oo) mu (X `&` A i))%E).
  by rewrite measure_sigma_subadditive//= -?XUA => // i; apply: measurableI.
apply: lee_lim; [exact: is_cvg_nneseries|exact: is_cvg_nneseries|].
by apply: nearW => n; apply: lee_sum => i  _; exact: measureIr.
Qed.

Lemma measurable_Rmu_extE d (R : realType) (T : semiRingOfSetsType d)
    (mu : {measure set T -> \bar R}) X :
  d.-ring.-measurable X -> mu^* X = SetRing.measure mu X.
Proof. by move=> Xm/=; rewrite -Rmu_ext/= measurable_mu_extE. Qed.
Local Close Scope measure_scope.

Section measure_extension.
Local Open Scope ereal_scope.
Local Open Scope measure_scope.
Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Let Rmu := SetRing.measure mu.
Notation rT := (SetRing.type T).

Lemma sub_caratheodory :
  (d.-measurable).-sigma.-measurable `<=` mu^*.-cara.-measurable.
Proof.
suff: <<s d.-ring.-measurable >> `<=` mu^*.-cara.-measurable.
   by apply: subset_trans; apply: sub_smallest2r => //; exact: sub_smallest.
apply: smallest_sub.
  split => //; [by move=> X mX; rewrite setTD; exact: measurableC |
                by move=> u_ mu_; exact: bigcupT_measurable].
move=> A mA; apply le_caratheodory_measurable => // X.
apply: le_ereal_inf_tmp => _ [B [mB XB] <-].
rewrite -(eq_eseriesr (fun _ _ => SetRing.RmuE _ (mB _))) => //.
have RmB i : measurable (B i : set rT) by exact: sub_gen_smallest.
set BA := eseries (fun n => Rmu (B n `&` A)).
set BNA := eseries (fun n => Rmu (B n `&` ~` A)).
apply: (@le_trans _ _ (limn BA + limn BNA)); [apply: leeD|].
  - rewrite (_ : BA = eseries (fun n => mu_ext mu (B n `&` A))); last first.
      rewrite funeqE => n; apply: eq_bigr => k _.
      by rewrite /= measurable_Rmu_extE //; exact: measurableI.
    apply: (@le_trans _ _ (mu_ext mu (\bigcup_k (B k `&` A)))).
      by apply: le_mu_ext; rewrite -setI_bigcupl; exact: setISS.
    exact: outer_measure_sigma_subadditive.
  - rewrite (_ : BNA = eseries (fun n => mu_ext mu (B n `\` A))); last first.
      rewrite funeqE => n; apply: eq_bigr => k _.
      by rewrite /= measurable_Rmu_extE //; exact: measurableD.
    apply: (@le_trans _ _ (mu_ext mu (\bigcup_k (B k `\` A)))).
      by apply: le_mu_ext; rewrite -setI_bigcupl; exact: setISS.
    exact: outer_measure_sigma_subadditive.
have cBNA : cvg (BNA @ \oo) by exact: is_cvg_nneseries.
have cBA : cvg (BA @ \oo) by exact: is_cvg_nneseries.
have cB : cvg (eseries (Rmu \o B) @ \oo) by exact: is_cvg_nneseries.
have [def|] := boolP (lim (BA @ \oo) +? lim (BNA @ \oo)); last first.
  rewrite /adde_def negb_and !negbK=> /orP[/andP[BAoo BNAoo]|/andP[BAoo BNAoo]].
  - suff -> : limn (eseries (Rmu \o B)) = +oo by rewrite leey.
    apply/eqP; rewrite -leye_eq -(eqP BAoo); apply/(lee_lim cBA cB).
    near=> n; apply: lee_sum => m _; apply: le_measure; rewrite /mkset; by
      [rewrite inE; exact: measurableI | rewrite inE | apply: subIset; left].
  - suff -> : limn (eseries (Rmu \o B)) = +oo by rewrite leey.
    apply/eqP; rewrite -leye_eq -(eqP BNAoo); apply/(lee_lim cBNA cB).
    by near=> n; apply: lee_sum => m _; rewrite -setDE; apply: le_measure;
       rewrite /mkset ?inE//; apply: measurableD.
rewrite -(limeD cBA cBNA) // (_ : (fun _ => _) =
    eseries (fun k => Rmu (B k `&` A) + Rmu (B k `&` ~` A))); last first.
  by rewrite funeqE => n; rewrite -big_split /=; exact: eq_bigr.
apply/lee_lim => //.
  by apply/is_cvg_nneseries => // n *; exact: adde_ge0.
near=> n; apply: lee_sum => i _; rewrite -measure_semi_additive2.
- apply: le_measure; rewrite /mkset ?inE//; [|by rewrite -setIUr setUCr setIT].
  by apply: measurableU; [exact:measurableI|rewrite -setDE; exact:measurableD].
- exact: measurableI.
- by rewrite -setDE; exact: measurableD.
- by apply: measurableU; [exact:measurableI|rewrite -setDE; exact:measurableD].
- by rewrite setIACA setICr setI0.
Unshelve. all: by end_near. Qed.

Let I : measurableType _ := g_sigma_algebraType (@measurable _ T).

Definition measure_extension : set I -> \bar R := mu^*.

Local Lemma measure_extension0 : measure_extension set0 = 0.
Proof. exact: mu_ext0. Qed.

Local Lemma measure_extension_ge0 (A : set I) : 0 <= measure_extension A.
Proof. exact: mu_ext_ge0. Qed.

Local Lemma measure_extension_semi_sigma_additive :
  semi_sigma_additive measure_extension.
Proof.
move=> F mF tF mUF; rewrite /measure_extension.
apply: caratheodory_measure_sigma_additive => //; last exact: sub_caratheodory.
by move=> i; exact: (sub_caratheodory (mF i)).
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ measure_extension
  measure_extension0 measure_extension_ge0
  measure_extension_semi_sigma_additive.

Lemma measure_extension_sigma_finite : @sigma_finite _ T _ setT mu ->
  @sigma_finite _ _ _ setT measure_extension.
Proof.
move=> -[S setTS mS]; exists S => //; move=> i; split.
  by have := (mS i).1; exact: sub_sigma_algebra.
by rewrite /measure_extension /= measurable_mu_extE //;
  [exact: (mS i).2 | exact: (mS i).1].
Qed.

Lemma measure_extension_unique : sigma_finite [set: T] mu ->
  (forall mu' : {measure set I -> \bar R},
    (forall X, d.-measurable X -> mu X = mu' X) ->
    (forall X, (d.-measurable).-sigma.-measurable X ->
      measure_extension X = mu' X)).
Proof.
move=> [F TF /all_and2[Fm muF]] mu' mu'mu X mX.
apply: (@measure_unique _ _ I d.-measurable F) => //.
- by move=> A B Am Bm; apply: measurableI.
- by move=> A Am; rewrite /= /measure_extension measurable_mu_extE// mu'mu.
- by move=> k; rewrite /= /measure_extension measurable_mu_extE.
Qed.

End measure_extension.

Local Open Scope measure_scope.
Lemma caratheodory_measurable_mu_ext d (R : realType) (T : semiRingOfSetsType d)
    (mu : {measure set T -> \bar R}) A :
  d.-measurable A -> mu^*.-cara.-measurable A.
Proof.
by move=> Am; apply: sub_caratheodory => //; apply: sub_sigma_algebra.
Qed.
Local Close Scope measure_scope.

Section completed_measure_extension.
Local Open Scope ereal_scope.
Context d (T : semiRingOfSetsType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Notation rT := (SetRing.type T).
Let Rmu : set rT -> \bar R := SetRing.measure mu.

Let I : measurableType _ := caratheodory_type (mu^*)%mu.

Definition completed_measure_extension : set I -> \bar R := (mu^*)%mu.

Let measure0 : completed_measure_extension set0 = 0.
Proof. exact: mu_ext0. Qed.

Let measure_ge0 (A : set I) : 0 <= completed_measure_extension A.
Proof. exact: mu_ext_ge0. Qed.

Let measure_semi_sigma_additive :
  semi_sigma_additive completed_measure_extension.
Proof.
move=> F mF tF mUF; rewrite /completed_measure_extension.
exact: caratheodory_measure_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ completed_measure_extension
  measure0 measure_ge0 measure_semi_sigma_additive.

Lemma completed_measure_extension_sigma_finite : @sigma_finite _ T _ setT mu ->
  @sigma_finite _ _ _ setT completed_measure_extension.
Proof.
move=> -[S setTS mS]; exists S => //; move=> i; split.
- apply: sub_caratheodory; apply: sub_sigma_algebra.
  exact: (mS i).1.
- by rewrite /completed_measure_extension /= measurable_mu_extE //;
    [exact: (mS i).2 | exact: (mS i).1].
Qed.

End completed_measure_extension.
