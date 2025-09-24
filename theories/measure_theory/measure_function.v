(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop reals.
From mathcomp Require Import interval_inference ereal topology normedtype.
From mathcomp Require Import sequences esum numfun.
From mathcomp Require Import measurable_structure measurable_function.

(**md**************************************************************************)
(* # Measure Functions                                                        *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* ## Structures for functions on set systems                                 *)
(*                                                                            *)
(* Hierarchy of contents, measures, s-finite/sigma-finite/finite measures,    *)
(* etc. Also contains a number of details about its implementation.           *)
(*                                                                            *)
(* ```                                                                        *)
(* {content set T -> \bar R} == type of contents                              *)
(*                              T is expected to be a semiring of sets and R  *)
(*                              a numFieldType.                               *)
(*                              The HB class is Content.                      *)
(*         Content_isMeasure == interface that extends a content to a measure *)
(*                              with the proof that it is semi_sigma_additive *)
(* {measure set T -> \bar R} == type of (non-negative) measures               *)
(*                              T is expected to be a semiring of sets and    *)
(*                              R is expected to be a numFieldType.           *)
(*                              The HB class is Measure.                      *)
(*                 isMeasure == interface corresponding to the "textbook      *)
(*                              definition" of measures                       *)
(* ```                                                                        *)
(* ## Instances of measures                                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*         msum mu n == the measure corresponding to the sum of the measures  *)
(*                      mu_0, ..., mu_{n-1}                                   *)
(*        @mzero T R == the zero measure                                      *)
(* measure_add m1 m2 == the measure corresponding to the sum of the           *)
(*                      measures m1 and m2                                    *)
(*        mscale r m == the measure of corresponding to fun A => r * m A      *)
(*                      where r has type {nonneg R}                           *)
(*      mseries mu n == the measure corresponding to the sum of the           *)
(*                      measures mu_n, mu_{n+1}, ...                          *)
(*   pushforward m f == pushforward of a set function m : set T1 -> \bar R    *)
(*                      by f : T1 -> T2;  pushforward/image measure if m is   *)
(*                      a measure and f measurable                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*    G.-ring.-measurable A == A belongs to the ring of sets <<r G >>         *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*               fin_num_fun == predicate for finite function over measurable *)
(*                              sets                                          *)
(*           sfinite_measure == predicate for s-finite measure functions      *)
(*          sigma_finite A f == the measure function f is sigma-finite on the *)
(*                              A : set T with T a semiring of sets           *)
(*              mrestr mu mD == restriction of the measure mu to a set D      *)
(*                              mD is a proof that D is measurable.           *)
(*                 isSFinite == interface for functions that satisfy the      *)
(*                              sfinite_measure predicate                     *)
(* {sfinite_measure set T -> \bar R} == type of s-finite measures             *)
(*                              The HB class is SFiniteMeasure.               *)
(*             isSigmaFinite == interface for functions that satisfy          *)
(*                              sigma finiteness                              *)
(* {sigma_finite_content set T -> \bar R} == contents that are also sigma     *)
(*                              finite                                        *)
(*                              The HB class is SigmaFiniteContent.           *)
(* {sigma_finite_measure set T -> \bar R} == measures that are also sigma     *)
(*                              finite                                        *)
(*                              The HB class is SigmaFiniteMeasure.           *)
(*         Measure_isSFinite == interface that extends a measure to an        *)
(*                              s-finite measure using a sequence of finite   *)
(*                              measures                                      *)
(*                  isFinite == interface for functions that satisfy the      *)
(*                              fin_num_fun predicate                         *)
(*            FinNumFun.type == type of functions over semiring of sets       *)
(*                              returning a fin_num                           *)
(*                              The HB class is FinNumFun.                    *)
(* {finite_measure set T -> \bar R} == finite measures                        *)
(*                              The HB class is FiniteMeasure.                *)
(*          Measure_isFinite == interface that extends a measure to a finite  *)
(*                              measure using a proof of fin_num_fun          *)
(*    sfinite_measure_seq mu == the sequence of finite measures of the        *)
(*                              s-finite measure mu                           *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*  mfrestr mD muDoo == finite measure corresponding to the restriction of    *)
(*                      the measure mu over D with mu D < +oo,                *)
(*                      mD : measurable D, muDoo : mu D < +oo                 *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*             lim_sup_set F == limit superior (or upper limit) of a          *)
(*                              sequence of sets F                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

(*Reserved Notation "{ 'content' fUV }" (format "{ 'content'  fUV }").*)
Reserved Notation "{ 'content' 'set' T '->' '\bar' R }"
  (T at level 37, format "{ 'content'  'set'  T  '->'  '\bar'  R }").
(*Reserved Notation "[ 'content' 'of' f 'as' g ]"
  (format "[ 'content'  'of'  f  'as'  g ]").
Reserved Notation "[ 'content' 'of' f ]" (format "[ 'content'  'of'  f ]").*)
(*Reserved Notation "{ 'measure' fUV }" (format "{ 'measure'  fUV }").*)
Reserved Notation "{ 'measure' 'set' T '->' '\bar' R }"
  (T at level 37, format "{ 'measure'  'set'  T  '->'  '\bar'  R }").
(*Reserved Notation "[ 'measure' 'of' f 'as' g ]"
  (format "[ 'measure'  'of'  f  'as'  g ]").
Reserved Notation "[ 'measure' 'of' f ]" (format "[ 'measure'  'of'  f ]").*)
Reserved Notation "d .-ring" (format "d .-ring").
Reserved Notation "d .-ring.-measurable" (format "d .-ring.-measurable").
Reserved Notation "{ 'sfinite_measure' 'set' T '->' '\bar' R }"
  (T at level 37, format "{ 'sfinite_measure'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'sigma_finite_content' 'set' T '->' '\bar' R }"
  (T at level 37,
   format "{ 'sigma_finite_content'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'sigma_finite_measure' 'set' T '->' '\bar' R }"
  (T at level 37,
   format "{ 'sigma_finite_measure'  'set'  T  '->'  '\bar'  R }").
Reserved Notation "{ 'finite_measure' 'set' T '->' '\bar' R }"
  (T at level 37, format "{ 'finite_measure'  'set'  T  '->'  '\bar'  R }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section additivity.
Context d (R : numFieldType) (T : semiRingOfSetsType d)
        (mu : set T -> \bar R).

(* TODO: undocumented *)
Definition semi_additive2 := forall A B, measurable A -> measurable B ->
  measurable (A `|` B) ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition semi_additive := forall F n,
 (forall k : nat, measurable (F k)) -> trivIset setT F ->
  measurable (\big[setU/set0]_(k < n) F k) ->
  mu (\big[setU/set0]_(i < n) F i) = \sum_(i < n) mu (F i).

Definition semi_sigma_additive :=
  forall F, (forall i : nat, measurable (F i)) -> trivIset setT F ->
  measurable (\bigcup_n F n) ->
  (fun n => \sum_(0 <= i < n) mu (F i)) @ \oo --> mu (\bigcup_n F n).

Definition additive2 := forall A B, measurable A -> measurable B ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition additive :=
  forall F, (forall i : nat, measurable (F i)) -> trivIset setT F ->
  forall n, mu (\big[setU/set0]_(i < n) F i) = \sum_(i < n) mu (F i).

Definition sigma_additive :=
  forall F, (forall i : nat, measurable (F i)) -> trivIset setT F ->
  (fun n => \sum_(0 <= i < n) mu (F i)) @ \oo --> mu (\bigcup_n F n).

Definition subadditive := forall (A : set T) (F : nat -> set T) n,
  (forall k, `I_n k -> measurable (F k)) -> measurable A ->
  A `<=` \big[setU/set0]_(k < n) F k ->
  (mu A <= \sum_(k < n) mu (F k))%E.

Definition measurable_subset_sigma_subadditive :=
  forall (A : set T) (F : nat -> set T),
    (forall n, measurable (F n)) -> measurable A ->
    subset_sigma_subadditive mu A F.

Lemma semi_additiveW : mu set0 = 0 -> semi_additive -> semi_additive2.
Proof.
move=> mu0 amx A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(amx (bigcup2 A B))->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- by move=> [|[|i]] [|[|j]]/= _ _; rewrite ?(AB, setI0, set0I, setIC) => -[].
Qed.

End additivity.

Section ring_additivity.
Context d (R : numFieldType) (T : ringOfSetsType d) (mu : set T -> \bar R).

Lemma semi_additiveE : semi_additive mu = additive mu.
Proof.
rewrite propeqE; split=> [sa A mA tA n|+ A m mA tA UAm]; last by move->.
by rewrite sa //; exact: bigsetU_measurable.
Qed.

Lemma semi_additive2E : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma additive2P : mu set0 = 0 -> semi_additive mu <-> additive2 mu.
Proof.
move=> mu0; rewrite -semi_additive2E; split; first exact: semi_additiveW.
rewrite semi_additiveE semi_additive2E => muU A Am Atriv n.
elim: n => [|n IHn]; rewrite ?(big_ord_recr, big_ord0) ?mu0//=.
rewrite muU ?IHn//=; first by apply: bigsetU_measurable.
rewrite -bigcup_mkord -subset0 => x [[/= m + Amx] Anx].
by rewrite (Atriv m n) ?ltnn//=; exists x.
Qed.

End ring_additivity.

(* NB: realFieldType cannot be weakened to numFieldType in the current
   state because cvg_lim requires a topology for \bar R which is
   defined for at least realFieldType *)
Lemma semi_sigma_additive_is_additive d (T : semiRingOfSetsType d)
    (R : realFieldType) (mu : set T -> \bar R) :
  mu set0 = 0 -> semi_sigma_additive mu -> semi_additive mu.
Proof.
move=> mu0 samu A n Am Atriv UAm.
have := samu (fun i => if (i < n)%N then A i else set0).
rewrite (bigcup_splitn n) bigcup0 ?setU0; last first.
  by move=> i _; rewrite -ltn_subRL subnn.
under eq_bigr do rewrite ltn_ord.
move=> /(_ _ _ UAm)/(@cvg_lim _) <-//; last 2 first.
- by move=> i; case: ifP.
- move=> i j _ _; do 2![case: ifP] => ? ?; do ?by rewrite (setI0, set0I) => -[].
  by move=> /Atriv; apply.
apply: lim_near_cst => //=; near=> i.
have /subnKC<- : (n <= i)%N by near: i; exists n.
transitivity (\sum_(j < n + (i - n)) mu (if (j < n)%N then A j else set0)).
  by rewrite big_mkord.
rewrite big_split_ord/=; under eq_bigr do rewrite ltn_ord.
by rewrite [X in _ + X]big1 ?adde0// => ?; rewrite -ltn_subRL subnn.
Unshelve. all: by end_near. Qed.

Lemma semi_sigma_additiveE
  (R : numFieldType) d (T : sigmaRingType d) (mu : set T -> \bar R) :
  semi_sigma_additive mu = sigma_additive mu.
Proof.
rewrite propeqE; split=> [amu A mA tA|amu A mA tA mbigcupA]; last exact: amu.
by apply: amu => //; exact: bigcupT_measurable.
Qed.

Lemma sigma_additive_is_additive
  (R : realFieldType) d (T : sigmaRingType d) (mu : set T -> \bar R) :
  mu set0 = 0 -> sigma_additive mu -> additive mu.
Proof.
move=> mu0; rewrite -semi_sigma_additiveE -semi_additiveE.
exact: semi_sigma_additive_is_additive.
Qed.

HB.mixin Record isContent d
    (T : semiRingOfSetsType d) (R : numFieldType) (mu : set T -> \bar R) := {
  measure_ge0 : forall x, (0 <= mu x)%E ;
  measure_semi_additive : semi_additive mu }.

HB.structure Definition Content d
    (T : semiRingOfSetsType d) (R : numFieldType) := {
  mu & isContent d T R mu }.

Notation content := Content.type.
Notation "{ 'content' 'set' T '->' '\bar' R }" := (content T R) : ring_scope.

Arguments measure_ge0 {d T R} _.

Section content_signed.
Context d (T : semiRingOfSetsType d) (R : numFieldType).
Variable mu : {content set T -> \bar R}.

Lemma content_inum_subproof S :
  Itv.spec (@ext_num_sem R) (Itv.Real `[0%Z, +oo[) (mu S).
Proof.
apply/and3P; split.
- by rewrite real_fine -real_leNye; apply: le_trans (measure_ge0 _ _).
- by rewrite /= bnd_simp measure_ge0.
- by rewrite bnd_simp.
Qed.

Canonical content_inum S := Itv.mk (content_inum_subproof S).

End content_signed.

Section content_on_semiring_of_sets.
Context d (T : semiRingOfSetsType d) (R : numFieldType)
        (mu : {content set T -> \bar R}).

Lemma measure0 : mu set0 = 0.
Proof.
have /[!big_ord0] ->// := @measure_semi_additive _ _ _ mu (fun=> set0) 0%N.
exact: trivIset_set0.
Qed.

Lemma measure_gt0 x : (0%R < mu x)%E = (mu x != 0).
Proof. by rewrite lt_def measure_ge0 andbT. Qed.

Hint Resolve measure0 : core.

Hint Resolve measure_ge0 : core.

Hint Resolve measure_semi_additive : core.

Lemma measure_semi_additive_ord n (F : 'I_n -> set T) :
  (forall (k : 'I_n), measurable (F k)) ->
  trivIset setT F ->
  measurable (\big[setU/set0]_(k < n) F k) ->
  mu (\big[setU/set0]_(i < n) F i) = \sum_(i < n) mu (F i).
Proof.
move=> mF tF mUF; pose F' (i : nat) := oapp F set0 (insub i).
have FE (i : 'I_n) : F i = (F' \o val) i by rewrite /F'/= valK/=.
rewrite (eq_bigr (F' \o val))// (eq_bigr (mu \o F' \o val))//; last first.
  by move=> i _; rewrite FE.
rewrite -measure_semi_additive//.
- by move=> k; rewrite /F'; case: insubP => /=.
- apply/trivIsetP=> i j _ _; rewrite /F'.
  do 2?[case: insubP; rewrite ?(set0I, setI0)//= => ? _ <-].
  by move/trivIsetP: tF; apply.
- by rewrite (eq_bigr (F' \o val)) in mUF.
Qed.

Lemma measure_semi_additive_ord_I (F : nat -> set T) (n : nat) :
  (forall k, (k < n)%N -> measurable (F k)) ->
  trivIset `I_n F ->
  measurable (\big[setU/set0]_(k < n) F k) ->
  mu (\big[setU/set0]_(i < n) F i) = \sum_(i < n) mu (F i).
Proof.
move=> mF tF; apply: measure_semi_additive_ord.
  by move=> k; apply: mF.
by rewrite trivIset_comp// ?(image_eq [surjfun of val])//; apply: 'inj_val.
Qed.

Lemma content_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D ->
    trivIset D F ->
    (forall i, D i -> measurable (F i)) ->
    measurable (\bigcup_(i in D) F i) ->
  mu (\bigcup_(i in D) F i) = \sum_(i \in D) mu (F i).
Proof.
elim/choicePpointed: I => I in D F *.
  by rewrite !emptyE => *; rewrite fsbig_set0 bigcup0.
move=> [n /ppcard_eqP[f]] Ftriv Fm UFm.
rewrite -(image_eq [surjfun of f^-1%FUN])/= in UFm Ftriv *.
rewrite bigcup_image fsbig_image//= bigcup_mkord -fsbig_ord/= in UFm *.
rewrite (@measure_semi_additive_ord_I (F \o f^-1))//= 1?trivIset_comp//.
by move=> k kn; apply: Fm; exact: funS.
Qed.

Lemma measure_semi_additive2 : semi_additive2 mu.
Proof. exact/semi_additiveW. Qed.
Hint Resolve measure_semi_additive2 : core.

End content_on_semiring_of_sets.
Arguments measure0 {d T R} _.

#[global] Hint Extern 0
  (is_true (0%R <= (_ : {content set _ -> \bar _}) _)%E) =>
  solve [apply: measure_ge0] : core.

#[global] Hint Extern 0
  (is_true (0%:E <= (_ : {content set _ -> \bar _}) _)%E) =>
  solve [apply: measure_ge0] : core.

#[global] Hint Extern 0
  ((_ : {content set _ -> \bar _}) set0 = 0%R)%E =>
  solve [apply: measure0] : core.

#[global]
Hint Resolve measure_semi_additive2 measure_semi_additive : core.

Section content_on_ring_of_sets.
Context d (R : realFieldType)(T : ringOfSetsType d)
        (mu : {content set T -> \bar R}).

Lemma measureU : additive2 mu.
Proof. by rewrite -semi_additive2E. Qed.

Lemma measure_bigsetU : additive mu.
Proof. by rewrite -semi_additiveE. Qed.

Lemma measure_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D ->
    trivIset D F ->
    (forall i, D i -> measurable (F i)) ->
  mu (\bigcup_(i in D) F i) = \sum_(i \in D) mu (F i).
Proof.
move=> Dfin Ftriv Fm; rewrite content_fin_bigcup//.
exact: fin_bigcup_measurable.
Qed.

Lemma measure_bigsetU_ord_cond n (P : {pred 'I_n}) (F : 'I_n -> set T) :
  (forall i : 'I_n, P i -> measurable (F i)) -> trivIset P F ->
  mu (\big[setU/set0]_(i < n | P i) F i) = (\sum_(i < n | P i) mu (F i))%E.
Proof.
move=> mF tF; rewrite !(big_mkcond P)/= measure_semi_additive_ord//.
- by apply: eq_bigr => i _; rewrite (fun_if mu) measure0.
- by move=> k; case: ifP => //; apply: mF.
- by rewrite -patch_pred trivIset_restr setIT.
- by apply: bigsetU_measurable=> k _; case: ifP => //; apply: mF.
Qed.

Lemma measure_bigsetU_ord n (P : {pred 'I_n}) (F : 'I_n -> set T) :
  (forall i : 'I_n, measurable (F i)) -> trivIset setT F ->
  mu (\big[setU/set0]_(i < n | P i) F i) = (\sum_(i < n | P i) mu (F i))%E.
Proof.
by move=> mF tF; rewrite measure_bigsetU_ord_cond//; apply: sub_trivIset tF.
Qed.

Lemma measure_fbigsetU (I : choiceType) (A : {fset I}) (F : I -> set T) :
  (forall i, i \in A -> measurable (F i)) -> trivIset [set` A] F ->
  mu (\big[setU/set0]_(i <- A) F i) = (\sum_(i <- A) mu (F i))%E.
Proof.
by move=> mF tF; rewrite -bigcup_fset measure_fin_bigcup// -fsbig_seq.
Qed.

End content_on_ring_of_sets.

#[global]
Hint Resolve measureU measure_bigsetU : core.

HB.mixin Record Content_isMeasure d (T : semiRingOfSetsType d)
    (R : numFieldType) (mu : set T -> \bar R) of Content d mu := {
  measure_semi_sigma_additive : semi_sigma_additive mu }.

#[short(type=measure)]
HB.structure Definition Measure d (T : semiRingOfSetsType d)
    (R : numFieldType) :=
  {mu of Content d mu & Content_isMeasure d T R mu }.

Notation "{ 'measure' 'set' T '->' '\bar' R }" := (measure T%type R)
  : ring_scope.

Section measure_signed.
Context d (R : numFieldType) (T : semiRingOfSetsType d).

Variable mu : {measure set T -> \bar R}.

Lemma measure_inum_subproof S :
  Itv.spec (@ext_num_sem R) (Itv.Real `[0%Z, +oo[) (mu S).
Proof.
apply/and3P; split.
- by rewrite real_fine -real_leNye; apply: le_trans (measure_ge0 _ _).
- by rewrite /= bnd_simp measure_ge0.
- by rewrite bnd_simp.
Qed.

Canonical measure_inum S := Itv.mk (measure_inum_subproof S).

End measure_signed.

HB.factory Record isMeasure d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : set T -> \bar R) := {
  measure0 : mu set0 = 0 ;
  measure_ge0 : forall x, (0 <= mu x)%E ;
  measure_semi_sigma_additive : semi_sigma_additive mu }.

HB.builders Context d (T : semiRingOfSetsType d) (R : realFieldType)
  (mu : set T -> \bar R) of isMeasure _ T R mu.

Let semi_additive_mu : semi_additive mu.
Proof.
apply: semi_sigma_additive_is_additive.
- exact: measure0.
- exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ := isContent.Build d T R mu
  measure_ge0 semi_additive_mu.
HB.instance Definition _ := Content_isMeasure.Build d T R mu
  measure_semi_sigma_additive.
HB.end.

Lemma eq_measure d (T : measurableType d) (R : realFieldType)
  (m1 m2 : {measure set T -> \bar R}) :
  (m1 = m2 :> (set T -> \bar R)) -> m1 = m2.
Proof.
move: m1 m2 => [m1 [[m10 m1ge0 [m1sa]]]] [m2 [[+ + [+]]]] /= m1m2.
rewrite -{}m1m2 => m10' m1ge0' m1sa'; f_equal.
by rewrite (_ : m10' = m10)// (_ : m1ge0' = m1ge0)// (_ : m1sa' = m1sa).
Qed.

Section measure_lemmas.
Context d (R : realFieldType) (T : semiRingOfSetsType d).
Variable mu : {measure set T -> \bar R}.

Lemma measure_semi_bigcup A : (forall i : nat, measurable (A i)) ->
    trivIset setT A -> measurable (\bigcup_n A n) ->
  mu (\bigcup_n A n) = (\sum_(i <oo) mu (A i))%E.
Proof. by move=> Am Atriv /measure_semi_sigma_additive/cvg_lim<-//. Qed.

End measure_lemmas.

#[global] Hint Extern 0 (_ set0 = 0%R)%E => solve [apply: measure0] : core.
#[global] Hint Extern 0 (is_true (0%:E <= _)) => solve [apply: measure_ge0] : core.

Section measure_lemmas.
Context d (R : realFieldType) (T : sigmaRingType d).
Variable mu : {measure set T -> \bar R}.

Lemma measure_sigma_additive : sigma_additive mu.
Proof.
by rewrite -semi_sigma_additiveE //; apply: measure_semi_sigma_additive.
Qed.

Lemma measure_bigcup (D : set nat) F : (forall i, D i -> measurable (F i)) ->
  trivIset D F -> mu (\bigcup_(n in D) F n) = (\sum_(i <oo | i \in D) mu (F i))%E.
Proof.
move=> mF tF; rewrite bigcup_mkcond measure_semi_bigcup.
- by rewrite [in RHS]eseries_mkcond; apply: eq_eseriesr => n _; case: ifPn.
- by move=> i; case: ifPn => // /set_mem; exact: mF.
- by move/trivIset_mkcond : tF.
- by rewrite -bigcup_mkcond; exact: bigcup_measurable.
Qed.

End measure_lemmas.
Arguments measure_bigcup {d R T} _ _.

#[global] Hint Extern 0 (sigma_additive _) =>
  solve [apply: measure_sigma_additive] : core.

Section measure_sum.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (m : {measure set T -> \bar R}^nat) (n : nat).

Definition msum (A : set T) : \bar R := \sum_(k < n) m k A.

Let msum0 : msum set0 = 0. Proof. by rewrite /msum big1. Qed.

Let msum_ge0 B : 0 <= msum B. Proof. by rewrite /msum; apply: sume_ge0. Qed.

Let msum_sigma_additive : semi_sigma_additive msum.
Proof.
move=> F mF tF mUF; rewrite [X in _ --> X](_ : _ =
    lim ((fun n => \sum_(0 <= i < n) msum (F i)) @ \oo)).
  by apply: is_cvg_ereal_nneg_natsum => k _; exact: sume_ge0.
rewrite nneseries_sum//; apply: eq_bigr => /= i _.
exact: measure_semi_bigcup.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ msum
  msum0 msum_ge0 msum_sigma_additive.

End measure_sum.
Arguments msum {d T R}.

Section measure_zero.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realFieldType).

Definition mzero (A : set T) : \bar R := 0.

Let mzero0 : mzero set0 = 0. Proof. by []. Qed.

Let mzero_ge0 B : 0 <= mzero B. Proof. by []. Qed.

Let mzero_sigma_additive : semi_sigma_additive mzero.
Proof.
move=> F mF tF mUF; rewrite [X in X @ \oo--> _](_ : _ = cst 0); first exact: cvg_cst.
by apply/funext => n; rewrite big1.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ mzero
  mzero0 mzero_ge0 mzero_sigma_additive.

End measure_zero.
Arguments mzero {d T R}.

Lemma msum_mzero d (T : sigmaRingType d) (R : realType)
    (m_ : {measure set T -> \bar R}^nat) :
  msum m_ 0 = mzero.
Proof. by apply/funext => A/=; rewrite /msum big_ord0. Qed.

Section measure_add.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (m1 m2 : {measure set T -> \bar R}).

Definition measure_add := msum (fun n => if n is 0%N then m1 else m2) 2.

Lemma measure_addE A : measure_add A = m1 A + m2 A.
Proof. by rewrite /measure_add/= /msum 2!big_ord_recl/= big_ord0 adde0. Qed.

End measure_add.

Section measure_scale.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realFieldType).
Variables (r : {nonneg R}) (m : {measure set T -> \bar R}).

Definition mscale (A : set T) : \bar R := r%:num%:E * m A.

Let mscale0 : mscale set0 = 0. Proof. by rewrite /mscale measure0 mule0. Qed.

Let mscale_ge0 B : 0 <= mscale B.
Proof. by rewrite /mscale mule_ge0. Qed.

Let mscale_sigma_additive : semi_sigma_additive mscale.
Proof.
move=> F mF tF mUF; rewrite [X in X @ \oo --> _](_ : _ =
    (fun n => (r%:num)%:E * \sum_(0 <= i < n) m (F i))); last first.
  by apply/funext => k; rewrite ge0_sume_distrr.
rewrite /mscale; have [->|r0] := eqVneq r%:num 0%R.
  rewrite mul0e [X in X @ \oo --> _](_ : _ = cst 0); first exact: cvg_cst.
  by under eq_fun do rewrite mul0e.
by apply: cvgeZl => //; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ mscale
  mscale0 mscale_ge0 mscale_sigma_additive.

End measure_scale.
Arguments mscale {d T R}.

Section measure_series.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (m : {measure set T -> \bar R}^nat) (n : nat).

Definition mseries (A : set T) : \bar R := \sum_(n <= k <oo) m k A.

Let mseries0 : mseries set0 = 0.
Proof. by rewrite /mseries ereal_series eseries0. Qed.

Let mseries_ge0 B : 0 <= mseries B.
Proof. by rewrite /mseries ereal_series nneseries_esum//; exact: esum_ge0. Qed.

Let mseries_sigma_additive : semi_sigma_additive mseries.
Proof.
move=> F mF tF mUF; rewrite [X in _ --> X](_ : _ =
  lim ((fun n => \sum_(0 <= i < n) mseries (F i)) @ \oo)); last first.
  rewrite [in LHS]/mseries.
  transitivity (\sum_(n <= k <oo) \sum_(i <oo) m k (F i)).
    rewrite 2!ereal_series.
    apply: (@eq_eseriesr _ (fun k => m k (\bigcup_n0 F n0))) => i ni.
    exact: measure_semi_bigcup.
  rewrite ereal_series nneseries_interchange//.
  apply: (@eq_eseriesr _ (fun j => \sum_(i <oo | (n <= i)%N) m i (F j))
    (fun i => \sum_(n <= k <oo) m k (F i))).
  by move=> i _; rewrite ereal_series.
apply: is_cvg_ereal_nneg_natsum => k _.
by rewrite /mseries ereal_series; exact: nneseries_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ mseries
  mseries0 mseries_ge0 mseries_sigma_additive.

End measure_series.
Arguments mseries {d T R}.

Definition pushforward d1 d2 (T1 : sigmaRingType d1) (T2 : sigmaRingType d2)
  (R : realFieldType) (m : set T1 -> \bar R) (f : T1 -> T2)
  := fun A => m (f @^-1` A).
Arguments pushforward {d1 d2 T1 T2 R}.

Section pushforward_measure.
Local Open Scope ereal_scope.
Context d d' (T1 : measurableType d) (T2 : measurableType d')
        (R : realFieldType).
Variables (m : {measure set T1 -> \bar R}) (f : T1 -> T2).
Hypothesis mf : measurable_fun [set: T1] f.

Let pushforward0 : pushforward m f set0 = 0.
Proof. by rewrite /pushforward preimage_set0 measure0. Qed.

Let pushforward_ge0 A : 0 <= pushforward m f A.
Proof. by apply: measure_ge0; rewrite -[X in measurable X]setIT; apply: mf. Qed.

Let pushforward_sigma_additive : semi_sigma_additive (pushforward m f).
Proof.
move=> F mF tF mUF; rewrite /pushforward preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: mf.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mf.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  (pushforward m f) pushforward0 pushforward_ge0 pushforward_sigma_additive.

End pushforward_measure.

Module SetRing.
Definition type (T : Type) := T.
Definition display : measure_display -> measure_display. Proof. by []. Qed.

Section SetRing.
Local Open Scope ereal_scope.
Context d {T : semiRingOfSetsType d}.

Notation rT := (type T).
#[export]
HB.instance Definition _ := Pointed.on rT.
#[export]
HB.instance Definition _ := isRingOfSets.Build (display d) rT
  (@setring0 T measurable) (@setringU T measurable) (@setringD T measurable).

Local Notation "d .-ring" := (display d).
Local Notation "d .-ring.-measurable" :=
  ((d%mdisp.-ring).-measurable : set (set (type _))).

Local Definition measurable_fin_trivIset : set (set T) :=
  [set A | exists B : set (set T),
    [/\ A = \bigcup_(X in B) X, forall X : set T, B X -> measurable X,
      finite_set B & trivIset B id]].

Lemma ring_measurableE : d.-ring.-measurable = measurable_fin_trivIset.
Proof.
apply/seteqP; split; last first.
  move=> _ [B [-> Bm Bfin Btriv]]; apply: fin_bigcup_measurable => //.
  by move=> i Di; apply: sub_gen_smallest; apply: Bm.
have mdW A : measurable A -> measurable_fin_trivIset A.
  move=> Am; exists [set A]; split; do ?by [rewrite bigcup_set1|move=> ? ->|].
  by move=> ? ? -> ->.
have mdI : setI_closed measurable_fin_trivIset.
  move=> _ _ [A [-> Am Afin Atriv]] [B [-> Bm Bfin Btriv]].
  rewrite setI_bigcupl; under eq_bigcupr do rewrite setI_bigcupr.
  rewrite -bigcup_setX -(bigcup_image _ _ id).
  eexists; split; [reflexivity | | exact/finite_image/finite_setX |].
    by move=> _ [X [? ?] <-]; apply: measurableI; [apply: Am|apply: Bm].
  apply: trivIset_sets => -[a b] [a' b']/= [Xa Xb] [Xa' Xb']; rewrite setIACA.
  by move=> [x [Ax Bx]]; rewrite (Atriv a a') 1?(Btriv b b')//; exists x.
have mdisj_bigcap : finN0_bigcap_closed measurable_fin_trivIset.
   exact/finN0_bigcap_closedP/mdI.
have mDbigcup I (D : set I) (A : set T) (B : I -> set T) : finite_set D ->
    measurable A -> (forall i, D i -> measurable (B i)) ->
    measurable_fin_trivIset (A `\` \bigcup_(i in D) B i).
  have [->|/set0P D0] := eqVneq D set0.
    by rewrite bigcup0// setD0 => *; apply: mdW.
  move=> Dfin Am Bm; rewrite -bigcupDr//; apply: mdisj_bigcap=> // i Di.
  by have [F [Ffin Fm -> ?]] := semi_measurableD A (B i) Am (Bm _ Di); exists F.
have mdU : fin_trivIset_closed measurable_fin_trivIset.
  elim/Pchoice=> I D F Dfin Ftriv Fm.
  have /(_ _ (set_mem _))/cid-/(all_sig_cond_dep (fun=> set0))
       [G /(_ _ (mem_set _))GP] := Fm _ _.
  under eq_bigcupr => i Di do case: (GP i Di) => ->.
  rewrite -bigcup_setX_dep -(bigcup_image _ _ id); eexists; split=> //.
  - by move=> _ [i [Di Gi] <-]; have [_ + _ _] := GP i.1 Di; apply.
  - by apply: finite_image; apply: finite_setXR=> // i Di; have [] := GP i Di.
  apply: trivIset_sets => -[i X] [j Y] /= [Di Gi] [Dj Gj] XYN0.
  suff eqij : i = j.
    by rewrite {i}eqij in Di Gi *; have [_ _ _ /(_ _ _ _ _ XYN0)->] := GP j Dj.
  apply: Ftriv => //; have [-> _ _ _] := GP j Dj; have [-> _ _ _] := GP i Di.
  by case: XYN0 => [x [Xx Yx]]; exists x; split; [exists X|exists Y].
have mdDI : setD_closed measurable_fin_trivIset.
  move=> A B mA mB; have [F [-> Fm Ffin Ftriv]] := mA.
  have [F' [-> F'm F'fin F'triv]] := mB.
  have [->|/set0P F'N0] := eqVneq F' set0.
    by rewrite bigcup_set0 setD0; exists F.
  rewrite setD_bigcupl; apply: mdU => //; first by apply: trivIset_setIr.
  move=> X DX; rewrite -bigcupDr//; apply: mdisj_bigcap => //.
  move=> Y DY; case: (semi_measurableD X Y); [exact: Fm|exact: F'm|].
  by move=> G [Gfin Gm -> Gtriv]; exists G.
apply: smallest_sub => //; split=> //; first by apply: mdW.
move=> A B mA mB; rewrite -(setUIDK B A) setUA [X in X `|` _]setUidl//.
rewrite -bigcup2inE; apply: mdU => //; last by move=> [|[]]// _; apply: mdDI.
by move=> [|[]]// [|[]]//= _ _ []; rewrite setDE ?setIA => X [] []//.
Qed.

Lemma measurable_subring : (d.-measurable : set (set T)) `<=` d.-ring.-measurable.
Proof. by rewrite /measurable => X Xmeas /= M /= [_]; apply. Qed.

Lemma ring_finite_set (A : set rT) : measurable A -> exists B : set (set T),
  [/\ finite_set B,
      (forall X, B X -> X !=set0),
      trivIset B id,
      (forall X : set T, X \in B -> measurable X) &
      A = \bigcup_(X in B) X].
Proof.
rewrite ring_measurableE => -[B [-> Bm Bfin Btriv]].
exists (B `&` [set X | X != set0]); split.
- by apply: sub_finite_set Bfin; exact: subIsetl.
- by move=> ?/= [_ /set0P].
- by move=> X Y/= [XB _] [YB _]; exact: Btriv.
- by move=> X/= /[!inE] -[] /Bm.
rewrite bigcup_mkcondr; apply: eq_bigcupr => X Bx; case: ifPn => //.
by rewrite notin_setE/= => /negP/negPn/eqP.
Qed.

Definition decomp (A : set rT) : set (set T) :=
  if A == set0 then [set set0] else
  if pselect (measurable A) is left mA then projT1 (cid (ring_finite_set mA))
  else [set A].

Lemma decomp_finite_set (A : set rT) : finite_set (decomp A).
Proof.
rewrite /decomp; case: ifPn => // A0; case: pselect => // X.
by case: cid => /= ? [].
Qed.

Lemma decomp_triv (A : set rT) : trivIset (decomp A) id.
Proof.
rewrite /decomp; case: ifP => _; first by move=> i j/= -> ->.
case: pselect => // Am; first by case: cid => //= ? [].
by move=> i j /= -> ->.
Qed.
Hint Resolve decomp_triv : core.

Lemma all_decomp_neq0 (A : set rT) :
  A !=set0 -> (forall X, decomp A X -> X !=set0).
Proof.
move=> /set0P AN0; rewrite /decomp/= (negPf AN0).
case: pselect => //= Am; first by case: cid => //= ? [].
by move=> X ->; exact/set0P.
Qed.

Lemma decomp_neq0 (A : set rT) X : A !=set0 -> X \in decomp A -> X !=set0.
Proof. by move=> /all_decomp_neq0/(_ X) /[!inE]. Qed.

Lemma decomp_measurable (A : set rT) (X : set T) :
  measurable A -> X \in decomp A -> measurable X.
Proof.
rewrite /decomp; case: ifP => _; first by rewrite inE => _ ->.
by case: pselect => // Am _; case: cid => //= ? [_ _ _ + _]; apply.
Qed.

Lemma cover_decomp (A : set rT) : \bigcup_(X in decomp A) X = A.
Proof.
rewrite /decomp; case: ifP => [/eqP->|_]; first by rewrite bigcup0.
case: pselect => // Am; first by case: cid => //= ? [].
by rewrite bigcup_set1.
Qed.

Lemma decomp_sub (A : set rT) (X : set T) : X \in decomp A -> X `<=` A.
Proof.
rewrite /decomp; case: ifP => _; first by rewrite inE/= => ->//.
case: pselect => //= Am; last by rewrite inE => ->.
by case: cid => //= D [_ _ _ _ ->] /[!inE] XD; apply: bigcup_sup.
Qed.

Lemma decomp_set0 : decomp set0 = [set set0].
Proof. by rewrite /decomp eqxx. Qed.

Lemma decompN0 (A : set rT) : decomp A != set0.
Proof.
rewrite /decomp; case: ifPn => [_|AN0]; first by apply/set0P; exists set0.
case: pselect=> //= Am; last by apply/set0P; exists A.
case: cid=> //= D [_ _ _ _ Aeq]; apply: contra_neq AN0; rewrite Aeq => ->.
by rewrite bigcup_set0.
Qed.

Definition measure (R : numDomainType) (mu : set T -> \bar R)
  (A : set rT) : \bar R := \sum_(X \in decomp A) mu X.

Section content.
Context {R : realFieldType} (mu : {content set T -> \bar R}).
Local Notation Rmu := (measure mu).
Arguments big_trivIset {I D T R idx op} A F.

Lemma Rmu_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D -> trivIset D F -> (forall i, i \in D -> measurable (F i)) ->
  Rmu (\bigcup_(i in D) F i) = \sum_(i \in D) mu (F i).
Proof.
move=> Dfin Ftriv Fm; rewrite /measure.
have mUD : measurable (\bigcup_(i in D) F i : set rT).
  apply: fin_bigcup_measurable => // *; apply: sub_gen_smallest.
  exact/Fm/mem_set.
have [->|/set0P[i0 Di0]] := eqVneq D set0.
  by rewrite bigcup_set0 decomp_set0 fsbig_set0 fsbig_set1.
set E := decomp _; have Em X := decomp_measurable mUD X.
transitivity (\sum_(X \in E) \sum_(i \in D) mu (X `&` F i)).
  apply: eq_fsbigr => /= X XE; have XDF : X = \bigcup_(i in D) (X `&` F i).
    by rewrite -setI_bigcupr setIidl//; exact: decomp_sub.
  rewrite [in LHS]XDF content_fin_bigcup//; first exact: trivIset_setIl.
  - by move=> i /mem_set Di; apply: measurableI; [exact: Em|exact: Fm].
  - by rewrite -XDF; exact: Em.
rewrite exchange_fsbig //; last exact: decomp_finite_set.
apply: eq_fsbigr => i Di; have Feq : F i = \bigcup_(X in E) (X `&` F i).
  rewrite -setI_bigcupl setIidr// cover_decomp.
  by apply/bigcup_sup; exact: set_mem.
rewrite -content_fin_bigcup -?Feq//; [exact/decomp_finite_set| | |exact/Fm].
- exact/trivIset_setIr/decomp_triv.
- by move=> X /= XE; apply: measurableI; [apply: Em; rewrite inE | exact: Fm].
Qed.

Lemma RmuE (A : set T) : measurable A -> Rmu A = mu A.
Proof.
move=> Am; rewrite -[A in LHS](@bigcup_set1 _ unit _ tt).
by rewrite Rmu_fin_bigcup// ?fsbig_set1// => -[].
Qed.

Let Rmu0 : Rmu set0 = 0.
Proof.
rewrite -(bigcup_set0 (fun _ : void => set0)).
by rewrite Rmu_fin_bigcup// fsbig_set0.
Qed.

Lemma Rmu_ge0 A : (Rmu A >= 0)%E.
Proof. by rewrite sume_ge0. Qed.

Lemma Rmu_additive : semi_additive Rmu.
Proof.
apply/(additive2P Rmu0) => // A B /ring_finite_set[/= {}A [? _ Atriv Am ->]].
move=> /ring_finite_set[/= {}B [? _ Btriv Bm ->]].
rewrite -subset0 => coverAB0.
have AUBfin : finite_set (A `|` B) by rewrite finite_setU.
have AUBtriv : trivIset (A `|` B) id.
  move=> X Y [] ABX [] ABY; do ?by [exact: Atriv|exact: Btriv].
    by move=> [u [Xu Yu]]; case: (coverAB0 u); split; [exists X|exists Y].
  by move=> [u [Xu Yu]]; case: (coverAB0 u); split; [exists Y|exists X].
rewrite -bigcup_setU !Rmu_fin_bigcup//=.
- rewrite fsbigU//= => [X /= [XA XB]]; have [->//|/set0P[x Xx]] := eqVneq X set0.
  by case: (coverAB0 x); split; exists X.
- by move=> X /set_mem [|] /mem_set ?; [exact: Am|exact: Bm].
Qed.

#[export]
HB.instance Definition _ := isContent.Build _ _ _ Rmu Rmu_ge0 Rmu_additive.

End content.

End SetRing.
Module Exports.
HB.reexport.
HB.reexport SetRing.
End Exports.
End SetRing.
Export SetRing.Exports.
Notation "d .-ring" := (SetRing.display d) : measure_display_scope.
Notation "d .-ring.-measurable" :=
  ((d%mdisp.-ring).-measurable : set (set (SetRing.type _))) : classical_set_scope.

Lemma le_measure d (R : realFieldType) (T : semiRingOfSetsType d)
    (mu : {content set T -> \bar R}) :
  {in measurable &, {homo mu : A B / A `<=` B >-> (A <= B)%E}}.
Proof.
move=> A B; rewrite ?inE => mA mB AB; have [|muBfin] := leP +oo%E (mu B).
  by rewrite leye_eq => /eqP ->; rewrite leey.
rewrite -[leRHS]SetRing.RmuE// -[B](setDUK AB) measureU/= ?setDIK//.
- by rewrite SetRing.RmuE ?leeDl.
- exact: sub_gen_smallest.
- by apply: measurableD; exact: sub_gen_smallest.
Qed.

Lemma measure_le0 d (T : semiRingOfSetsType d) (R : realFieldType)
  (mu : {content set T -> \bar R}) (A : set T) :
  (mu A <= 0)%E = (mu A == 0)%E.
Proof. by case: ltgtP (measure_ge0 mu A). Qed.

Section more_content_semiring_lemmas.
Context d (R : realFieldType) (T : semiRingOfSetsType d).
Variable mu : {content set T -> \bar R}.

Lemma content_subadditive : subadditive mu.
Proof.
move=> X A n Am Xm XA; pose B i := A\_`I_n i `&` X.
have XE : X = \big[setU/set0]_(i < n) B i.
  rewrite -big_distrl/= setIidr// => x /XA/=.
  by rewrite -!bigcup_mkord => -[k nk Ax]; exists k; rewrite // patchT ?inE.
have Bm i : measurable (B i).
  case: (ltnP i n) => ltin; last by rewrite /B patchC ?inE ?set0I//= leq_gtF.
  by rewrite /B ?patchT ?inE//; apply: measurableI => //; apply: Am.
have subBA i : B i `<=` A i.
  by rewrite /B/patch; case: ifP; rewrite // set0I//= => _ ?.
have subDUB i : seqDU B i `<=` A i by  move=> x [/subBA].
have DUBm i : measurable (seqDU B i : set (SetRing.type T)).
  apply: measurableD; first exact: sub_gen_smallest.
  by apply: bigsetU_measurable => ? _; apply: sub_gen_smallest.
have DU0 i : (i >= n)%N -> seqDU B i = set0.
  move=> leni; rewrite -subset0 => x []; rewrite /B patchC ?inE/= ?leq_gtF//.
  by case.
rewrite -SetRing.RmuE// XE bigsetU_seqDU measure_bigsetU//.
rewrite [leRHS](big_ord_widen n (mu \o A))//= [leRHS]big_mkcond/=.
rewrite lee_sum => // i _; case: ltnP => ltin; last by rewrite DU0 ?measure0.
rewrite -[leRHS]SetRing.RmuE; last exact: Am.
by rewrite le_measure ?inE//=; last by apply: sub_gen_smallest; apply: Am.
Qed.

Lemma content_sub_fsum (I : choiceType) D (A : set T) (A_ : I -> set T) :
  finite_set D ->
  (forall i, D i -> measurable (A_ i)) ->
  measurable A ->
  A `<=` \bigcup_(i in D) A_ i -> (mu A <= \sum_(i \in D) mu (A_ i))%E.
Proof.
elim/choicePpointed: I => I in A_ D *.
  rewrite !emptyE bigcup_set0// subset0 => _ _ _ ->.
  by rewrite measure0 fsbig_set0.
move=> Dfin A_m Am Asub; have [n /ppcard_eqP[f]] := Dfin.
rewrite (reindex_fsbig f^-1%FUN `I_n)//= -fsbig_ord.
rewrite (@content_subadditive A (A_ \o f^-1%FUN))//=.
  by move=> i ltin; apply: A_m; apply: funS.
rewrite (fsbig_ord _ _ (A_ \o f^-1%FUN))/= -(reindex_fsbig _ _ D)//=.
by rewrite fsbig_setU.
Qed.

(* (* alternative proof *) *)
(* Theorem semi_Boole_inequality : sub_additive mu. *)
(* Proof. *)
(* move=> X A n Am Xm Xsub; rewrite -SetRing.RmuE//. *)
(* under eq_bigr => i do [rewrite -SetRing.RmuE; do ?by apply: Am=> /=]. *)
(* pose rT := SetRing.type T. *)
(* have {}Am i : `I_n i -> measurable (A i : set rT). *)
(*   by move=> *; apply/SetRing.measurableW/Am => /=. *)
(* have {}Xm : measurable (X : set rT) by exact: SetRing.measurableW. *)
(* pose ammu := [additive_measure of SetRing.measure mu]. *)
(* rewrite (le_trans (le_measure ammu  _ _ Xsub)) ?inE// {Xsub}. *)
(*   by rewrite -bigcup_mkord; apply: fin_bigcup_measurable. *)
(* elim: n Am Xm => [|n IHn] Am Xm; first by rewrite !big_ord0 measure0. *)
(* have Anm : measurable (A n : set rT) by apply: Am => /=. *)
(* set B := \big[setU/set0]_(i < n) A i. *)
(* set C := \big[setU/set0]_(i < n.+1) A i. *)
(* have -> : C = B `|` (A n `\` B). *)
(*   suff -> : A n `\` B = C `\` B by rewrite setDUK// /C big_ord_recr/=; left. *)
(*   by rewrite /C big_ord_recr/= !setDE setIUl -!setDE setDv set0U. *)
(* have Bm : measurable (B : set rT). *)
(*   by rewrite -[B]bigcup_mkord; apply: fin_bigcup_measurable => //= i /ltnW/Am. *)
(* rewrite measureU // ?setDIK//; last exact: measurableD. *)
(* rewrite (@le_trans _ _ (ammu B + ammu (A n))) // ?leeD2l //; last first. *)
(*   by rewrite big_ord_recr /= leeD2r// IHn// => i /ltnW/Am. *)
(* by rewrite le_measure // ?inE// ?setDE//; exact: measurableD. *)
(* Qed. *)

End more_content_semiring_lemmas.

Section content_ring_lemmas.
Local Open Scope ereal_scope.
Context d (R : realType) (T : ringOfSetsType d).
Variable mu : {content set T -> \bar R}.

Lemma content_ring_sup_sigma_additive (A : nat -> set T) :
  (forall i, measurable (A i)) -> measurable (\bigcup_i A i) ->
  trivIset [set: nat] A -> \sum_(i <oo) mu (A i) <= mu (\bigcup_i A i).
Proof.
move=> Am UAm At; rewrite lime_le//; first exact: is_cvg_nneseries.
near=> n; rewrite big_mkord -measure_bigsetU//= le_measure ?inE//=.
- exact: bigsetU_measurable.
- by rewrite -bigcup_mkord; apply: bigcup_sub => i lein; apply: bigcup_sup.
Unshelve. all: by end_near. Qed.

Lemma content_ring_sigma_additive :
  measurable_subset_sigma_subadditive mu -> semi_sigma_additive mu.
Proof.
move=> mu_sub A Am Atriv UAm.
suff <- : \sum_(i <oo) mu (A i) = mu (\bigcup_n A n) by exact: is_cvg_nneseries.
by apply/eqP; rewrite eq_le mu_sub// ?content_ring_sup_sigma_additive.
Qed.

End content_ring_lemmas.

Section ring_sigma_subadditive_content.
Local Open Scope ereal_scope.
Context d (R : realType) (T : semiRingOfSetsType d)
        (mu : {content set T -> \bar R}).
Local Notation Rmu := (SetRing.measure mu).
Import SetRing.

Lemma ring_sigma_subadditive :
  measurable_subset_sigma_subadditive mu ->
  measurable_subset_sigma_subadditive Rmu.
Proof.
move=> muS; move=> /= D A Am Dm Dsub.
rewrite /Rmu -(eq_eseriesr (fun _ _ => esum_fset _ _))//; last first.
  by move=> *; exact: decomp_finite_set.
rewrite nneseries_esum ?esum_esum//=; last by move=> *; rewrite esum_ge0.
set K := _ `*`` _.
have /ppcard_eqP[f] : (K #= [set: nat])%card.
  apply: cardXR_eq_nat => [|i].
    by rewrite (_ : [set _ | true] = setT)//; exact/predeqP.
  split; first by apply/finite_set_countable; exact: decomp_finite_set.
  exact/set0P/decompN0.
have {Dsub} : D `<=` \bigcup_(k in K) k.2.
  apply: (subset_trans Dsub); apply: bigcup_sub => i _.
  rewrite -[A i]cover_decomp; apply: bigcup_sub => X/= XAi.
  by move=> x Xx; exists (i, X).
rewrite -(image_eq [bij of f^-1%FUN])/=.
rewrite (esum_set_image _ f^-1)//= bigcup_image => Dsub.
have DXsub X : X \in decomp D -> X `<=` \bigcup_i ((f^-1%FUN i).2 `&` X).
  move=> XD; rewrite -setI_bigcupl -[Y in Y `<=` _](setIidr (decomp_sub XD)).
  by apply: setSI.
have mf i : measurable ((f^-1)%function i).2.
  have [_ /mem_set/decomp_measurable] := 'invS_f (I : setT i).
  by apply; exact: Am.
have mfD i X : X \in decomp D -> measurable (((f^-1)%FUN i).2 `&` X : set T).
  by move=> XD; apply: measurableI; [exact: mf|exact: (decomp_measurable _ XD)].
apply: (@le_trans _ _
    (\sum_(i <oo) \sum_(X <- fset_set (decomp D)) mu ((f^-1%FUN i).2 `&` X))).
  rewrite nneseries_sum// fsbig_finite/=; last exact: decomp_finite_set.
  rewrite [leLHS]big_seq [leRHS]big_seq.
  rewrite lee_sum// => X /[!in_fset_set]; last exact: decomp_finite_set.
  move=> XD; have Xm := decomp_measurable Dm XD.
  by apply: muS => // [i|]; [exact: mfD|exact: DXsub].
apply: lee_lim => /=; do ?apply: is_cvg_nneseries=> //.
  by move=> n _ _; exact: sume_ge0.
near=> n; rewrite [n in _ <= n]big_mkcond; apply: lee_sum => i _.
rewrite ifT ?inE//.
under eq_big_seq.
  move=> x; rewrite in_fset_set=> [xD|]; last exact: decomp_finite_set.
  rewrite -RmuE//; last exact: mfD.
  over.
rewrite -fsbig_finite/=; last exact: decomp_finite_set.
rewrite -measure_fin_bigcup//=.
- rewrite -setI_bigcupr (cover_decomp D) -[leRHS]RmuE// ?le_measure ?inE//.
    by apply: measurableI => //; apply: sub_gen_smallest; apply: mf.
  by apply: sub_gen_smallest; apply: mf.
- exact: decomp_finite_set.
- by apply: trivIset_setIl; apply: decomp_triv.
- by move=> X /= XD; apply: sub_gen_smallest; apply: mfD; rewrite inE.
Unshelve. all: by end_near. Qed.

Lemma ring_semi_sigma_additive :
  measurable_subset_sigma_subadditive mu -> semi_sigma_additive Rmu.
Proof.
by move=> mu_sub; exact/content_ring_sigma_additive/ring_sigma_subadditive.
Qed.

Lemma semiring_sigma_additive :
  measurable_subset_sigma_subadditive mu -> semi_sigma_additive mu.
Proof.
move=> /ring_semi_sigma_additive Rmu_sigmadd F Fmeas Ftriv cupFmeas.
have Fringmeas i : d.-ring.-measurable (F i) by apply: measurable_subring.
have := Rmu_sigmadd F Fringmeas Ftriv (measurable_subring cupFmeas).
rewrite SetRing.RmuE//.
by under eq_fun do under eq_bigr do rewrite SetRing.RmuE//=.
Qed.

End ring_sigma_subadditive_content.

#[key="mu"]
HB.factory Record Content_SigmaSubAdditive_isMeasure d (R : realType)
    (T : semiRingOfSetsType d) (mu : set T -> \bar R) of Content d mu := {
  measure_sigma_subadditive : measurable_subset_sigma_subadditive mu }.

HB.builders Context d (R : realType) (T : semiRingOfSetsType d)
  (mu : set T -> \bar R) of Content_SigmaSubAdditive_isMeasure d R T mu.

HB.instance Definition _ := Content_isMeasure.Build d T R mu
  (semiring_sigma_additive (measure_sigma_subadditive)).

HB.end.

Section more_premeasure_ring_lemmas.
Local Open Scope ereal_scope.
Context d (R : realType) (T : semiRingOfSetsType d).
Variable mu : {measure set T -> \bar R}.
Import SetRing.

Lemma measure_sigma_subadditive : measurable_subset_sigma_subadditive mu.
Proof.
move=> X A Am Xm XA; pose B i := A i `&` X.
have XE : X = \bigcup_i B i by rewrite -setI_bigcupl setIidr.
have Bm i : measurable (B i) by rewrite /B; apply: measurableI.
have subBA i : B i `<=` A i by rewrite /B.
have subDUB i : seqDU B i `<=` A i by  move=> x [/subBA].
have DUBm i : measurable (seqDU B i : set (SetRing.type T)).
  by apply: measurableD => //;
     do 1?apply: bigsetU_measurable => *; apply: sub_gen_smallest.
rewrite XE; move: (XE); rewrite seqDU_bigcup_eq.
under eq_bigcupr do rewrite -[seqDU B _]cover_decomp//.
rewrite -bigcup_setX_dep; set K := _ `*`` _.
have /ppcard_eqP[f] : (K #= [set: nat])%card.
  apply: cardXR_eq_nat=> // i; split; last by apply/set0P; rewrite decompN0.
  exact/finite_set_countable/decomp_finite_set.
pose f' := f^-1%FUN; rewrite -(image_eq [bij of f'])/= bigcup_image/=.
pose g n := (f' n).2; have fVtriv : trivIset [set: nat] g.
  move=> i j _ _; rewrite /g.
  have [/= _ f'iB] : K (f' i) by apply: funS.
  have [/= _ f'jB] : K (f' j) by apply: funS.
  have [f'ij|f'ij] := eqVneq (f' i).1 (f' j).1.
    move=> /(decomp_triv f'iB)/=; rewrite f'ij => /(_ f'jB) f'ij2.
    apply: 'inj_f'; rewrite ?inE//= -!/(f' _); move: f'ij f'ij2.
    by case: (f' i) (f' j) => [? ?] [? ?]//= -> ->.
  move=> [x [f'ix f'jx]]; have Bij := @trivIset_seqDU _ B (f' i).1 (f' j).1 I I.
  rewrite Bij ?eqxx// in f'ij; exists x; split.
  - by move/mem_set : f'iB => /decomp_sub; apply.
  - by move/mem_set : f'jB => /decomp_sub; apply.
have g_inj : set_inj [set i | g i != set0] g.
  by apply: trivIset_inj=> [i /set0P//|]; apply: sub_trivIset fVtriv.
move=> XEbig; rewrite measure_semi_bigcup//= -?XEbig//; last first.
  move=> i; have [/= _ /mem_set] : K (f' i) by apply: funS.
  exact: decomp_measurable.
rewrite [leLHS](_ : _ = \sum_(i <oo | g i != set0) mu (g i)); last first.
  rewrite !nneseries_esum// esum_mkcond [RHS]esum_mkcond; apply: eq_esum.
  move=> i _; rewrite ifT ?inE//=; case: ifPn => //.
  by rewrite notin_setE /= -/(g _) => /negP/negPn/eqP ->.
rewrite -(esum_pred_image mu g)//.
rewrite [leLHS](_ : _ = \esum_(X in range g) mu X); last first.
  rewrite esum_mkcond [RHS]esum_mkcond; apply: eq_esum.
  move=> Y _; case: ifPn; rewrite ?(inE, notin_setE)/=.
    by move=> [i giN0 giY]; rewrite ifT// ?inE//=; exists i.
  move=> Ngx; case: ifPn; rewrite ?(inE, notin_setE)//=.
  move=> [i _ giY]; apply: contra_not_eq Ngx; rewrite -giY => mugi.
  by exists i => //; apply: contra_neq mugi => ->; rewrite measure0.
have -> : range g = \bigcup_i (decomp (seqDU B i)).
  apply/predeqP => /= Y; split => [[n _ gnY]|[n _ /= YBn]].
  have [/= _ f'nB] : K (f' n) by apply: funS.
    by exists (f' n).1 => //=; rewrite -gnY.
  by exists (f (n, Y)) => //; rewrite /g /f' funK//= inE.
rewrite esum_bigcup//; last first.
   move=> i j /=.
   have [->|/set0P DUBiN0] := eqVneq (seqDU B i) set0.
     rewrite decomp_set0 ?set_fset1 => /negP[].
     apply/eqP/predeqP=> x; split=> [[Y/=->]|->]//; first by rewrite measure0.
     by exists set0.
   have [->|/set0P DUBjN0] := eqVneq (seqDU B j) set0.
     rewrite decomp_set0 ?set_fset1 => _ /negP[].
     apply/eqP/predeqP=> x; split=> [[Y/=->]|->]//=; first by rewrite measure0.
     by exists set0.
   move=> _ _ [Y /= [/[dup] +]].
   move=> /mem_set /decomp_sub YBi /mem_set + /mem_set /decomp_sub YBj.
   move=> /(decomp_neq0 DUBiN0) [y Yy].
   apply: (@trivIset_seqDU _ B) => //; exists y.
   by split => //; [exact: YBi|exact: YBj].
rewrite nneseries_esumT// le_esum// => i _.
rewrite [leLHS](_ : _ = \sum_(j \in decomp (seqDU B i)) mu j); last first.
  by rewrite esum_fset//; exact: decomp_finite_set.
rewrite -SetRing.Rmu_fin_bigcup//=; last 3 first.
  exact: decomp_finite_set.
  exact: decomp_triv.
  by move=> ?; exact: decomp_measurable.
rewrite -[leRHS]SetRing.RmuE// le_measure//; last by rewrite cover_decomp.
- rewrite inE; apply: fin_bigcup_measurable; first exact: decomp_finite_set.
  move=> j /mem_set jdec; apply: sub_gen_smallest.
  exact: decomp_measurable jdec.
- by rewrite inE; apply: sub_gen_smallest; exact: Am.
Qed.

End more_premeasure_ring_lemmas.

Lemma measure_sigma_subadditive_tail d (R : realType) (T : semiRingOfSetsType d)
  (mu : {measure set T -> \bar R}) (A : set T) (F : nat -> set T) N :
    (forall n, measurable (F n)) -> measurable A ->
    A `<=` \bigcup_(n in ~` `I_N) F n ->
  (mu A <= \sum_(N <= n <oo) mu (F n))%E.
Proof.
move=> mF mA AF; rewrite eseries_cond eseries_mkcondr.
rewrite (@eq_eseriesr _ _ (fun n => mu (if (N <= n)%N then F n else set0))).
- apply: measure_sigma_subadditive => //.
  + by move=> n; case: ifPn.
  + move: AF; rewrite bigcup_mkcond.
    by under eq_bigcupr do rewrite mem_not_I.
- by move=> o _; rewrite (fun_if mu) measure0.
Qed.

Section ring_sigma_content.
Context d (R : realType) (T : semiRingOfSetsType d)
        (mu : {measure set T -> \bar R}).
Local Notation Rmu := (SetRing.measure mu).
Import SetRing.

Let ring_sigma_content : semi_sigma_additive Rmu.
Proof. exact/ring_semi_sigma_additive/measure_sigma_subadditive. Qed.

HB.instance Definition _ := Content_isMeasure.Build _ _ _ Rmu
  ring_sigma_content.

End ring_sigma_content.

Definition fin_num_fun d (T : semiRingOfSetsType d) (R : numDomainType)
  (mu : set T -> \bar R) := forall U, measurable U -> mu U \is a fin_num.

Lemma fin_num_fun_lty d (T : algebraOfSetsType d) (R : realFieldType)
  (mu : set T -> \bar R) : fin_num_fun mu -> (mu setT < +oo)%E.
Proof. by move=> h; rewrite ltey_eq h. Qed.

Lemma lty_fin_num_fun d (T : algebraOfSetsType d)
    (R : realFieldType) (mu : {measure set T -> \bar R}) :
  (mu setT < +oo)%E -> fin_num_fun mu.
Proof.
move=> h U mU; rewrite fin_real// (lt_le_trans _ (measure_ge0 mu U))//=.
by rewrite (le_lt_trans _ h)//= le_measure// inE.
Qed.

Definition sfinite_measure d (T : sigmaRingType d) (R : realType)
    (mu : set T -> \bar R) :=
  exists2 s : {measure set T -> \bar R}^nat,
    forall n, fin_num_fun (s n) &
    forall U, measurable U -> mu U = mseries s 0 U.

Definition sigma_finite d (T : semiRingOfSetsType d) (R : numDomainType)
    (A : set T) (mu : set T -> \bar R) :=
  exists2 F : (set T)^nat, A = \bigcup_(i : nat) F i &
      forall i, measurable (F i) /\ (mu (F i) < +oo)%E.

Lemma fin_num_fun_sigma_finite d (T : algebraOfSetsType d)
    (R : realFieldType) (mu : set T -> \bar R) : (mu set0 < +oo)%E ->
  fin_num_fun mu -> sigma_finite setT mu.
Proof.
move=> muoo; exists (fun i => if i \in [set 0%N] then setT else set0).
  by rewrite -bigcup_mkcondr setTI bigcup_const//; exists 0%N.
by move=> n; split; case: ifPn => // _; rewrite fin_num_fun_lty.
Qed.

Definition mrestr d (T : sigmaRingType d) (R : realFieldType) (D : set T)
  (f : set T -> \bar R) (mD : measurable D) := fun X => f (X `&` D).

Section measure_restr.
Context d (T : sigmaRingType d) (R : realFieldType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Local Notation restr := (mrestr mu mD).

Let restr0 : restr set0 = 0%E. Proof. by rewrite /mrestr set0I. Qed.

Let restr_ge0 (A : set _) : (0 <= restr A)%E.
Proof. by rewrite /restr; apply: measure_ge0; exact: measurableI. Qed.

Let restr_sigma_additive : semi_sigma_additive restr.
Proof.
move=> F mF tF mU; pose FD i := F i `&` D.
have mFD i : measurable (FD i) by exact: measurableI.
have tFD : trivIset setT FD.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /FD setIACA => ->; rewrite set0I.
by rewrite /restr setI_bigcupl; exact: measure_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ restr
  restr0 restr_ge0 restr_sigma_additive.

End measure_restr.

Lemma sfinite_measure_sigma_finite d (T : measurableType d)
    (R : realType) (mu : {measure set T -> \bar R}) :
  sigma_finite setT mu -> sfinite_measure mu.
Proof.
move=> [F UF mF]; rewrite /sfinite_measure.
have mDF k : measurable (seqDU F k).
  apply: measurableD; first exact: (mF k).1.
  by apply: bigsetU_measurable => i _; exact: (mF i).1.
exists (fun k => mrestr mu (mDF k)) => [n|U mU].
- apply: lty_fin_num_fun => //=.
  rewrite /mrestr setTI (@le_lt_trans _ _ (mu (F n)))//.
  + apply: le_measure; last exact: subDsetl.
    * rewrite inE; apply: measurableD; first exact: (mF n).1.
      by apply: bigsetU_measurable => i _; exact: (mF i).1.
    * by rewrite inE; exact: (mF n).1.
  + exact: (mF n).2.
rewrite /mseries/= /mrestr/=; apply/esym/cvg_lim => //.
rewrite -[X in _ --> mu X]setIT UF seqDU_bigcup_eq setI_bigcupr.
apply: (@measure_sigma_additive _ _ _ mu (fun k => U `&` seqDU F k)).
  by move=> i; exact: measurableI.
exact/trivIset_setIl/trivIset_seqDU.
Qed.

HB.mixin Record isSFinite d (T : sigmaRingType d) (R : realType)
    (mu : set T -> \bar R) := {
  s_finite : sfinite_measure mu }.

HB.structure Definition SFiniteMeasure d (T : sigmaRingType d) (R : realType) :=
  {mu of @Measure _ T R mu & isSFinite _ T R mu }.
Arguments s_finite {d T R} _.

Notation "{ 'sfinite_measure' 'set' T '->' '\bar' R }" :=
  (SFiniteMeasure.type T R) : ring_scope.

HB.mixin Record isSigmaFinite d (T : semiRingOfSetsType d) (R : numFieldType)
  (mu : set T -> \bar R) := { sigma_finiteT : sigma_finite setT mu }.

#[short(type="sigma_finite_content")]
HB.structure Definition SigmaFiniteContent d T R :=
  { mu of @Content d T R mu & isSigmaFinite d T R mu }.

Arguments sigma_finiteT {d T R} s.
#[global] Hint Resolve sigma_finiteT : core.

Notation "{ 'sigma_finite_content' 'set' T '->' '\bar' R }" :=
  (sigma_finite_content T R) : ring_scope.

#[short(type="sigma_finite_measure")]
HB.structure Definition SigmaFiniteMeasure d T R :=
  { mu of @SFiniteMeasure d T R mu & isSigmaFinite d T R mu }.

Notation "{ 'sigma_finite_measure' 'set' T '->' '\bar' R }" :=
  (sigma_finite_measure T R) : ring_scope.

HB.factory Record Measure_isSigmaFinite d (T : measurableType d)
    (R : realType) (mu : set T -> \bar R) of isMeasure _ _ _ mu :=
  { sigma_finiteT : sigma_finite setT mu }.

HB.builders Context d (T : measurableType d) (R : realType)
  mu of @Measure_isSigmaFinite d T R mu.

Lemma sfinite : sfinite_measure mu.
Proof. exact/sfinite_measure_sigma_finite/sigma_finiteT. Qed.

HB.instance Definition _ := @isSFinite.Build _ _ _ mu sfinite.

HB.instance Definition _ := @isSigmaFinite.Build _ _ _ mu sigma_finiteT.

HB.end.

Lemma sigma_finite_mzero d (T : measurableType d) (R : realFieldType) :
  sigma_finite setT (@mzero d T R).
Proof. by apply: fin_num_fun_sigma_finite => //; rewrite measure0. Qed.

HB.instance Definition _ d (T : measurableType d) (R : realFieldType) :=
  @isSigmaFinite.Build d T R mzero (@sigma_finite_mzero d T R).

Lemma sfinite_mzero d (T : measurableType d) (R : realType) :
  sfinite_measure (@mzero d T R).
Proof. exact/sfinite_measure_sigma_finite/sigma_finite_mzero. Qed.

HB.instance Definition _ d (T : measurableType d) (R : realType) :=
  @isSFinite.Build d T R mzero (@sfinite_mzero d T R).

HB.mixin Record isFinite d (T : semiRingOfSetsType d) (R : numDomainType)
  (k : set T -> \bar R) := { fin_num_measure : fin_num_fun k }.

HB.structure Definition FinNumFun d (T : semiRingOfSetsType d)
  (R : numFieldType) := { k of isFinite _ T R k }.

HB.structure Definition FiniteMeasure d (T : sigmaRingType d) (R : realType) :=
  { k of @SigmaFiniteMeasure _ _ _ k & isFinite _ T R k }.
Arguments fin_num_measure {d T R} _.

Notation "{ 'finite_measure' 'set' T '->' '\bar' R }" :=
  (FiniteMeasure.type T R) : ring_scope.

HB.factory Record Measure_isFinite d (T : measurableType d)
    (R : realType) (k : set T -> \bar R)
  of isMeasure _ _ _ k := { fin_num_measure : fin_num_fun k }.

HB.builders Context d (T : measurableType d) (R : realType) k
  of Measure_isFinite d T R k.

Let sfinite : sfinite_measure k.
Proof.
apply: sfinite_measure_sigma_finite.
by apply: fin_num_fun_sigma_finite; [rewrite measure0|exact: fin_num_measure].
Qed.

HB.instance Definition _ := @isSFinite.Build d T R k sfinite.

Let sigma_finite : sigma_finite setT k.
Proof.
by apply: fin_num_fun_sigma_finite; [rewrite measure0|exact: fin_num_measure].
Qed.

HB.instance Definition _ := @isSigmaFinite.Build d T R k sigma_finite.

Let finite : fin_num_fun k. Proof. exact: fin_num_measure. Qed.

HB.instance Definition _ := @isFinite.Build d T R k finite.

HB.end.

Section finite_restr.
Context d (T : measurableType d) (R : realType).
Variables (mu : {finite_measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.

Local Notation restr := (mrestr mu mD).

Let fin_num_restr : fin_num_fun restr.
Proof.
move=> A mA; have := fin_num_measure mu A mA.
rewrite !ge0_fin_numE//=; apply: le_lt_trans.
by rewrite /mrestr; apply: le_measure => //; rewrite inE//=; exact: measurableI.
Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ T _ restr fin_num_restr.

End finite_restr.

Section finite_mscale.
Context d (T : measurableType d) (R : realType).
Variables (mu : {finite_measure set T -> \bar R}) (r : {nonneg R}).

Local Notation scale := (mscale r mu).

Let fin_num_scale : fin_num_fun scale.
Proof.
by move=> A mA; have muA := fin_num_measure mu A mA; rewrite fin_numM.
Qed.

HB.instance Definition _ := @Measure_isFinite.Build _ T _ scale fin_num_scale.

End finite_mscale.

HB.factory Record Measure_isSFinite d (T : sigmaRingType d)
    (R : realType) (k : set T -> \bar R) of isMeasure _ _ _ k := {
  s_finite : exists s : {finite_measure set T -> \bar R}^nat,
    forall U, measurable U -> k U = mseries s 0 U }.

HB.builders Context d (T : sigmaRingType d) (R : realType)
  k of Measure_isSFinite d T R k.

Let sfinite : sfinite_measure k.
Proof.
have [s sE] := s_finite.
by exists s => //=> n; exact: fin_num_measure.
Qed.

HB.instance Definition _ := @isSFinite.Build d T R k sfinite.

HB.end.

Section sfinite_measure.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {sfinite_measure set T -> \bar R}).

Let s : (set T -> \bar R)^nat := let: exist2 x _ _ := cid2 (s_finite mu) in x.

Let s0 n : s n set0 = 0.
Proof. by rewrite /s; case: cid2. Qed.

Let s_ge0 n x : 0 <= s n x.
Proof. by rewrite /s; case: cid2. Qed.

Let s_semi_sigma_additive n : semi_sigma_additive (s n).
Proof.
by rewrite /s; case: cid2 => s' s'1 s'2; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ n := @isMeasure.Build _ _ _ (s n) (s0 n) (s_ge0 n)
  (@s_semi_sigma_additive n).

Let s_fin n : fin_num_fun (s n).
Proof. by rewrite /s; case: cid2 => F finF muE; exact: finF. Qed.

HB.instance Definition _ n := @Measure_isFinite.Build d T R (s n) (s_fin n).

Definition sfinite_measure_seq : {finite_measure set T -> \bar R}^nat := s.

Lemma sfinite_measure_seqP U : measurable U ->
  mu U = mseries sfinite_measure_seq O U.
Proof.
by move=> mU; rewrite /mseries /= /s; case: cid2 => // x xfin ->.
Qed.

End sfinite_measure.

Definition mfrestr d (T : measurableType d) (R : realFieldType) (D : set T)
    (f : set T -> \bar R) (mD : measurable D) of (f D < +oo)%E :=
  mrestr f mD.

Section measure_frestr.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Hypothesis moo : mu D < +oo.

Local Notation restr := (mfrestr mD moo).

HB.instance Definition _ := Measure.on restr.

Let restr_fin : fin_num_fun restr.
Proof.
move=> U mU; rewrite /restr /mrestr ge0_fin_numE ?measure_ge0//.
by rewrite (le_lt_trans _ moo)// le_measure// ?inE//; exact: measurableI.
Qed.

HB.instance Definition _ := Measure_isFinite.Build _ _ _ restr restr_fin.

End measure_frestr.

Section content_semiRingOfSetsType.
Local Open Scope ereal_scope.
Context d (T : semiRingOfSetsType d) (R : realFieldType).
Variables (mu : {content set T -> \bar R}) (A B : set T).
Hypotheses (mA : measurable A) (mB : measurable B).

Lemma measureIl : mu (A `&` B) <= mu A.
Proof. by rewrite le_measure ?inE//; apply: measurableI. Qed.

Lemma measureIr : mu (A `&` B) <= mu B.
Proof. by rewrite le_measure ?inE//; apply: measurableI. Qed.

Lemma subset_measure0 : A `<=` B -> mu B = 0 -> mu A = 0.
Proof. by move=> ? B0; apply/eqP; rewrite -measure_le0 -B0 le_measure ?inE. Qed.

End content_semiRingOfSetsType.

Section content_ringOfSetsType.
Local Open Scope ereal_scope.
Context d (T : ringOfSetsType d) (R : realFieldType).
Variable mu : {content set T -> \bar R}.
Implicit Types A B : set T.

Lemma measureDI A B : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -measure_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma measureD A B : measurable A -> measurable B ->
  mu A < +oo -> mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB mAoo.
rewrite (measureDI mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- by rewrite (le_lt_trans _ mAoo)// le_measure // ?inE//; exact: measurableI.
- by rewrite (lt_le_trans _ (measure_ge0 _ _)).
Qed.

Lemma measureU2 A B : measurable A -> measurable B ->
  mu (A `|` B) <= mu A + mu B.
Proof.
move=> ? ?; rewrite -bigcup2inE bigcup_mkord.
rewrite (le_trans (@content_subadditive _ _ _ mu _ (bigcup2 A B) 2%N _ _ _))//.
by move=> -[//|[//|[|]]].
by apply: bigsetU_measurable => -[] [//|[//|[|]]].
by rewrite big_ord_recr/= big_ord_recr/= big_ord0 add0e.
Qed.

End content_ringOfSetsType.

Section measureU.
Local Open Scope ereal_scope.
Context d (T : ringOfSetsType d) (R : realFieldType).
Variable mu : {measure set T -> \bar R}.

Lemma measureUfinr A B : measurable A -> measurable B -> mu B < +oo ->
  mu (A `|` B) = mu A + mu B - mu (A `&` B).
Proof.
move=> Am Bm mBfin; rewrite -[B in LHS](setDUK (@subIsetl _ _ A)) setUA.
rewrite [A `|` _]setUidl; last exact: subIsetr.
rewrite measureU//=; [|rewrite setDIr setDv set0U ?setDIK//..].
- by rewrite measureD// ?setIA ?setIid 1?setIC ?addeA//; exact: measurableI.
- exact: measurableD.
Qed.

Lemma measureUfinl A B : measurable A -> measurable B -> mu A < +oo ->
  mu (A `|` B) = mu A + mu B - mu (A `&` B).
Proof. by move=> *; rewrite setUC measureUfinr// setIC [mu B + _]addeC. Qed.

Lemma null_set_setU A B : measurable A -> measurable B ->
  mu A = 0 -> mu B = 0 -> mu (A `|` B) = 0.
Proof.
move=> mA mB A0 B0; rewrite measureUfinl/= ?A0//= ?B0 ?add0e.
by apply/eqP; rewrite oppe_eq0 -measure_le0/= -A0 measureIl.
Qed.

Lemma measureU0 A B : measurable A -> measurable B -> mu B = 0 ->
  mu (A `|` B) = mu A.
Proof.
move=> mA mB B0; rewrite measureUfinr/= ?B0// adde0.
by rewrite (@subset_measure0 _ _ _ _ (A `&` B) B) ?sube0//; exact: measurableI.
Qed.

End measureU.

Lemma eq_measureU d (T : ringOfSetsType d) (R : realFieldType) (A B : set T)
   (mu mu' : {measure set T -> \bar R}):
    measurable A -> measurable B ->
  mu A = mu' A -> mu B = mu' B -> mu (A `&` B) = mu' (A `&` B) ->
  mu (A `|` B) = mu' (A `|` B).
Proof.
move=> mA mB muA muB muAB; have [mu'ANoo|] := ltP (mu' A) +oo%E.
  by rewrite !measureUfinl/= ?muA ?muB ?muAB.
rewrite leye_eq => /eqP mu'A; transitivity (+oo : \bar R)%E; apply/eqP.
  by rewrite -leye_eq -mu'A -muA le_measure ?inE//=; apply: measurableU.
by rewrite eq_sym -leye_eq -mu'A le_measure ?inE//=; apply: measurableU.
Qed.

Section measure_continuity.
Local Open Scope ereal_scope.

Lemma nondecreasing_cvg_mu d (T : ringOfSetsType d) (R : realFieldType)
  (mu : {measure set T -> \bar R}) (F : (set T) ^nat) :
  (forall i, measurable (F i)) -> measurable (\bigcup_n F n) ->
  nondecreasing_seq F ->
  mu \o F @ \oo --> mu (\bigcup_n F n).
Proof.
move=> mF mbigcupF ndF.
have Binter : trivIset setT (seqD F) := trivIset_seqD ndF.
have FBE : forall n, F n.+1 = F n `|` seqD F n.+1 := setU_seqD ndF.
have FE n : \big[setU/set0]_(i < n.+1) (seqD F) i = F n :=
  nondecreasing_bigsetU_seqD n ndF.
rewrite -eq_bigcup_seqD.
have mB i : measurable (seqD F i) by elim: i => * //=; exact: measurableD.
apply: cvg_trans (measure_semi_sigma_additive _ mB Binter _); last first.
  by rewrite eq_bigcup_seqD.
apply: (@cvg_trans _ (\sum_(i < n.+1) mu (seqD F i) @[n --> \oo])).
  rewrite [X in _ --> X @ \oo](_ : _ = mu \o F) // funeqE => n.
  by rewrite -measure_semi_additive ?FE// => -[|].
move=> S [n _] nS; exists n => // m nm.
under eq_fun do rewrite -(big_mkord predT (mu \o seqD F)).
exact/(nS m.+1)/(leq_trans nm).
Qed.

Lemma nonincreasing_cvg_mu d (T : algebraOfSetsType d) (R : realFieldType)
  (mu : {measure set T -> \bar R}) (F : (set T) ^nat) :
  mu (F 0%N) < +oo ->
  (forall i, measurable (F i)) -> measurable (\bigcap_n F n) ->
  nonincreasing_seq F -> mu \o F @ \oo --> mu (\bigcap_n F n).
Proof.
move=> F0pos mF mbigcapF niF; pose G n := F O `\` F n.
have ? : mu (F 0%N) \is a fin_num by rewrite ge0_fin_numE.
have F0E r : mu (F 0%N) - (mu (F 0%N) - r) = r.
  by rewrite oppeB ?addeA ?subee ?add0e// fin_num_adde_defr.
rewrite -[x in _ --> x] F0E.
have -> : mu \o F = fun n => mu (F 0%N) - (mu (F 0%N) - mu (F n)).
  by apply: funext => n; rewrite F0E.
apply: cvgeB; rewrite ?fin_num_adde_defr//; first exact: cvg_cst.
have -> : \bigcap_n F n = F 0%N `&` \bigcap_n F n.
  by rewrite setIidr//; exact: bigcap_inf.
rewrite -measureD // setDE setC_bigcap setI_bigcupr -[x in bigcup _ x]/G.
have -> : (fun n => mu (F 0%N) - mu (F n)) = mu \o G.
  by apply: funext => n /=; rewrite measureD// setIidr//; exact/subsetPset/niF.
apply: nondecreasing_cvg_mu.
- by move=> ?; apply: measurableD; exact: mF.
- rewrite -setI_bigcupr; apply: measurableI; first exact: mF.
  by rewrite -@setC_bigcap; exact: measurableC.
- by move=> n m NM; apply/subsetPset; apply: setDS; apply/subsetPset/niF.
Qed.

End measure_continuity.


Section g_sigma_algebra_measure_unique_trace.
Context d (R : realType) (T : measurableType d).
Variables (G : set (set T)) (D : set T) (mD : measurable D).
Let H := [set X | G X /\ X `<=` D] (* "trace" of G wrt D *).
Hypotheses (Hm : H `<=` measurable) (setIH : setI_closed H).
Variables m1 m2 : {measure set T -> \bar R}.
Hypothesis m1m2D : m1 D = m2 D.
Hypotheses (m1m2 : forall A, H A -> m1 A = m2 A) (m1oo : (m1 D < +oo)%E).

Lemma g_sigma_algebra_measure_unique_trace :
  (forall X, (<<s D, H >>) X -> X `<=` D) -> forall X, <<s D, H >> X ->
  m1 X = m2 X.
Proof.
move=> sDHD; set E := [set A | [/\ measurable A, m1 A = m2 A & A `<=` D] ].
have HE : H `<=` E.
  by move=> X HX; rewrite /E /=; split; [exact: Hm|exact: m1m2|case: HX].
have setDE : setSD_closed E.
  move=> A B BA [mA m1m2A AD] [mB m1m2B BD]; split; first exact: measurableD.
  - rewrite measureD//; last first.
      by rewrite (le_lt_trans _ m1oo)//; apply: le_measure => // /[!inE].
    rewrite setIidr//= m1m2A m1m2B measureD// ?setIidr//.
    by rewrite (le_lt_trans _ m1oo)//= -m1m2A; apply: le_measure => // /[!inE].
  - by rewrite setDE; apply: subIset; left.
have ndE : ndseq_closed E.
  move=> A ndA EA; split; have mA n : measurable (A n) by have [] := EA n.
  - exact: bigcupT_measurable.
  - transitivity (limn (m1 \o A)).
      apply/esym/cvg_lim=>//.
      exact/(nondecreasing_cvg_mu mA _ ndA)/bigcupT_measurable.
    transitivity (limn (m2 \o A)).
      by apply/congr_lim/funext => n; have [] := EA n.
    apply/cvg_lim => //.
    exact/(nondecreasing_cvg_mu mA _ ndA)/bigcupT_measurable.
  - by apply: bigcup_sub => n; have [] := EA n.
have sDHE : <<s D, H >> `<=` E.
  by apply: lambda_system_subset => //; split => //; [move=> ? []|split].
by move=> X /sDHE[].
Qed.

End g_sigma_algebra_measure_unique_trace.
Arguments g_sigma_algebra_measure_unique_trace {d R T} G D.
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `g_sigma_algebra_measure_unique_trace`")]
Notation g_salgebra_measure_unique_trace := g_sigma_algebra_measure_unique_trace (only parsing).

Definition lim_sup_set T (F : (set T)^nat) := \bigcap_n \bigcup_(j >= n) F j.

Section borel_cantelli_realFieldType.
Context {d} {T : measurableType d} {R : realFieldType}
        (mu : {measure set T -> \bar R}).
Implicit Types F : (set T)^nat.
Local Open Scope ereal_scope.

Lemma lim_sup_set_ub F n : (forall k, measurable (F k)) ->
  mu (lim_sup_set F) <= mu (\bigcup_(k >= n) F k).
Proof.
move=> mF; rewrite /lim_sup_set le_measure// ?inE/=.
- by apply: bigcap_measurable => // k _; exact: bigcup_measurable.
- exact: bigcup_measurable.
- exact: bigcap_inf.
Qed.

Lemma lim_sup_set_cvg F : (forall k, measurable (F k)) ->
  mu (\bigcup_(k >= 0) F k) < +oo ->
  mu (\bigcup_(k >= n) F k) @[n --> \oo] --> mu (lim_sup_set F).
Proof.
move=> mF mFoo; apply: nonincreasing_cvg_mu => //.
- by move=> i; apply: bigcup_measurable => k /= _; exact: mF.
- apply: bigcap_measurable => // k _.
  by apply: bigcup_measurable => j /= _; exact: mF.
- move=> m n mn; apply/subsetPset => t [k /= nk Akt].
  by exists k => //=; rewrite (leq_trans mn).
Qed.

End borel_cantelli_realFieldType.
Arguments lim_sup_set_cvg {d T R} mu F.

Section borel_cantelli.
Context d (T : measurableType d) {R : realType} (mu : {measure set T -> \bar R}).
Implicit Types F : (set T)^nat.
Local Open Scope ereal_scope.

Lemma lim_sup_set_cvg0 F : (forall k, measurable (F k)) ->
  \sum_(n <oo) mu (F n) < +oo -> mu (lim_sup_set F) = 0.
Proof.
move=> mF bigUoo; apply/eqP; rewrite eq_le measure_ge0 andbT.
have /cvg_lim <- // : (\sum_(i <= n <oo) mu (F n))%E @[i --> \oo] --> 0%E.
  exact: nneseries_tail_cvg.
apply: lime_ge; first by apply/cvg_ex; exists 0; exact: nneseries_tail_cvg.
apply: nearW => n; rewrite (le_trans (lim_sup_set_ub mu n mF))//.
by apply: measure_sigma_subadditive_tail => //;
  [exact: bigcup_measurable|rewrite -setC_I].
Qed.

End borel_cantelli.

Section boole_inequality.
Context d (R : realFieldType) (T : ringOfSetsType d).
Variable mu : {content set T -> \bar R}.

Theorem Boole_inequality (A : (set T) ^nat) n :
    (forall i, (i < n)%N -> measurable (A i)) ->
  (mu (\big[setU/set0]_(i < n) A i) <= \sum_(i < n) mu (A i))%E.
Proof.
move=> Am; rewrite content_subadditive// -bigcup_mkord.
exact: fin_bigcup_measurable.
Qed.

End boole_inequality.
Notation le_mu_bigsetU := Boole_inequality.

Section sigma_finite_lemma.
Context d (T : ringOfSetsType d) (R : realFieldType) (A : set T)
        (mu : {content set T -> \bar R}).

Lemma sigma_finiteP : sigma_finite A mu <->
  exists F, [/\ A = \bigcup_i F i,
    nondecreasing_seq F & forall i, measurable (F i) /\ mu (F i) < +oo]%E.
Proof.
split=> [[F AUF mF]|[F [? ? ?]]]; last by exists F.
exists (fun n => \big[setU/set0]_(i < n.+1) F i); split.
- rewrite AUF; apply/seteqP; split.
    by apply: subset_bigcup => i _; exact: bigsetU_sup.
  by apply: bigcup_sub => i _; exact: bigsetU_bigcup.
- by move=> i j ij; exact/subsetPset/subset_bigsetU.
- move=> i; split; first by apply: bigsetU_measurable => j _; exact: (mF j).1.
  rewrite (le_lt_trans (Boole_inequality _ _))//.
    by move=> j _; exact: (mF _).1.
  by apply/lte_sum_pinfty => j _; exact: (mF j).2.
Qed.

End sigma_finite_lemma.

Section generalized_boole_inequality.
Context d (T : ringOfSetsType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Theorem generalized_Boole_inequality (A : (set T) ^nat) :
  (forall i, measurable (A i)) -> measurable (\bigcup_n A n) ->
  (mu (\bigcup_n A n) <= \sum_(i <oo) mu (A i))%E.
Proof. by move=> Am UAm; rewrite measure_sigma_subadditive. Qed.

End generalized_boole_inequality.
Notation le_mu_bigcup := generalized_Boole_inequality.

Section g_sigma_algebra_measure_unique.
Context d (R : realType) (T : measurableType d).
Variable G : set (set T).
Hypothesis Gm : G `<=` measurable.
Variable g : (set T)^nat.
Hypotheses Gg : forall i, G (g i).
Hypothesis g_cover : \bigcup_k (g k) = setT.
Variables m1 m2 : {measure set T -> \bar R}.

Lemma g_sigma_algebra_measure_unique_cover :
  (forall n A, <<s G >> A -> m1 (g n `&` A) = m2 (g n `&` A)) ->
  forall A, <<s G >> A -> m1 A = m2 A.
Proof.
pose GT : ringOfSetsType G.-sigma:= g_sigma_algebraType G.
move=> sGm1m2; pose g' k := \bigcup_(i < k) g i.
have sGm := smallest_sub (@sigma_algebra_measurable _ T) Gm.
have Gg' i : <<s G >> (g' i).
  apply: (@fin_bigcup_measurable _ GT) => //.
  by move=> n _; apply: sub_sigma_algebra.
have sG'm1m2 n A : <<s G >> A -> m1 (g' n `&` A) = m2 (g' n `&` A).
  move=> sGA; rewrite setI_bigcupl bigcup_mkord.
  elim: n => [|n IHn] in A sGA *; rewrite (big_ord0, big_ord_recr) ?measure0//=.
  have sGgA i : <<s G >> (g i `&` A).
    by apply: (@measurableI _ GT) => //; exact: sub_sigma_algebra.
  apply: eq_measureU; rewrite ?sGm1m2 ?IHn//; last first.
  - by rewrite -big_distrl -setIA big_distrl/= IHn// setICA setIid.
  - exact/sGm.
  - by apply: bigsetU_measurable => i _; apply/sGm.
have g'_cover : \bigcup_k (g' k) = setT.
  by rewrite -subTset -g_cover => x [k _ gx]; exists k.+1 => //; exists k => /=.
have nd_g' : nondecreasing_seq g'.
  move=> m n lemn; rewrite subsetEset => x [k km gx]; exists k => //=.
  exact: leq_trans lemn.
move=> A gA.
have -> : A = \bigcup_n (g' n `&` A) by rewrite -setI_bigcupl g'_cover setTI.
transitivity (lim (m1 (g' n `&` A) @[n --> \oo])).
  apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
  - by move=> n; apply: measurableI; exact/sGm.
  - by apply: bigcupT_measurable => k; apply: measurableI; exact/sGm.
  - by move=> ? ? ?; apply/subsetPset; apply: setSI; exact/subsetPset/nd_g'.
transitivity (lim (m2 (g' n `&` A) @[n --> \oo])).
  by apply/congr_lim/funext => x; apply: sG'm1m2 => //; exact/sGm.
apply/cvg_lim => //; apply: nondecreasing_cvg_mu.
- by move=> k; apply: measurableI => //; exact/sGm.
- by apply: bigcupT_measurable => k; apply: measurableI; exact/sGm.
- by move=> a b ab; apply/subsetPset; apply: setSI; exact/subsetPset/nd_g'.
Qed.

Hypothesis setIG : setI_closed G.
Hypothesis m1m2 : forall A, G A -> m1 A = m2 A.
Hypothesis m1goo : forall k, (m1 (g k) < +oo)%E.

Lemma g_sigma_algebra_measure_unique : forall E, <<s G >> E -> m1 E = m2 E.
Proof.
pose G_ n := [set X | G X /\ X `<=` g n]. (* "trace" *)
have G_E n : G_ n = [set g n `&` C | C in G].
  rewrite eqEsubset; split.
    by move=> X [GX Xgn] /=; exists X => //; rewrite setIidr.
  by rewrite /G_ => X [Y GY <-{X}]; split; [exact: setIG|apply: subIset; left].
have gIsGE n : [set g n `&` A | A in <<s G >>] =
               <<s g n, preimage_set_system (g n) id G >>.
  rewrite g_sigma_preimageE eqEsubset; split.
    by move=> _ /= [Y sGY <-]; exists Y => //; rewrite preimage_id setIC.
  by move=> _ [Y mY <-] /=; exists Y => //; rewrite preimage_id setIC.
have preimg_gGE n : preimage_set_system (g n) id G = G_ n.
  rewrite eqEsubset; split => [_ [Y GY <-]|].
    by rewrite preimage_id G_E /=; exists Y => //; rewrite setIC.
  by move=> X [GX Xgn]; exists X => //; rewrite preimage_id setIidr.
apply: g_sigma_algebra_measure_unique_cover => //.
move=> n A sGA; apply: (g_sigma_algebra_measure_unique_trace G (g n)) => //.
- exact: Gm.
- by move=> ? [? _]; exact/Gm.
- by move=> ? ? [? ?] [? ?]; split; [exact: setIG|apply: subIset; tauto].
- exact: m1m2.
- by move=> ? [? ?]; exact: m1m2.
- move=> X; rewrite -/(G_ n) -preimg_gGE -gIsGE.
  by case=> B sGB <-{X}; apply: subIset; left.
- by rewrite -/(G_ n) -preimg_gGE -gIsGE; exists A.
Qed.

End g_sigma_algebra_measure_unique.
Arguments g_sigma_algebra_measure_unique {d R T} G.
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `g_sigma_algebra_measure_unique_cover`")]
Notation g_salgebra_measure_unique_cover := g_sigma_algebra_measure_unique_cover (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `g_sigma_algebra_measure_unique`")]
Notation g_salgebra_measure_unique := g_sigma_algebra_measure_unique (only parsing).

Section measure_unique.
Context d (R : realType) (T : measurableType d).
Variables  (G : set (set T)) (g : (set T)^nat).
Hypotheses (mG : measurable = <<s G >>) (setIG : setI_closed G).
Hypothesis Gg : forall i, G (g i).
Hypothesis g_cover : \bigcup_k (g k) = setT.
Variables m1 m2 : {measure set T -> \bar R}.
Hypothesis m1m2 : forall A, G A -> m1 A = m2 A.
Hypothesis m1goo : forall k, (m1 (g k) < +oo)%E.

Lemma measure_unique A : measurable A -> m1 A = m2 A.
Proof.
move=> mA; apply: (g_sigma_algebra_measure_unique G); rewrite -?mG//.
by rewrite mG; exact: sub_sigma_algebra.
Qed.

End measure_unique.
Arguments measure_unique {d R T} G g.
