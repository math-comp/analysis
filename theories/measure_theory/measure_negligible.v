(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import interval_inference ereal topology normedtype.
From mathcomp Require Import sequences numfun.
From mathcomp Require Import measurable_structure measure_function.

(**md**************************************************************************)
(* # Negligibility                                                            *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* ```                                                                        *)
(*          mu.-negligible A == A is mu negligible                            *)
(*    measure_is_complete mu == the measure mu is complete                    *)
(*                {ae mu, P} == P holds almost everywhere for the measure mu, *)
(*                              declared as an instance of the type of        *)
(*                              filters                                       *)
(*                              P must be of the form forall x, Q x.          *)
(*                              Prefer this notation when P is an existing    *)
(*                              statement (i.e., a definition) that needs to  *)
(*                              be relativised.                               *)
(*                              The notation used the definition              *)
(*                              `almost_everywhere`.                          *)
(*     \forall x \ae mu, P x == equivalent to {ae mu, forall x, P x}          *)
(*                              Prefer this notation when the statement       *)
(*                              forall x, P x does not stand alone.           *)
(*      f = g %[ae mu in D ] == f is equal to g almost everywhere in D        *)
(*            f = g %[ae mu] == f is equal to g almost everywhere             *)
(*              mu-.null_set == (measure-theoretic) null sets                 *)
(*                 m1 `<< m2 == m1 is absolutely continuous w.r.t. m2 or      *)
(*                              m2 dominates m1                               *)
(*   content_dominates mu nu == forall A, measurable A ->                     *)
(*                              mu A = 0 -> nu A = 0                          *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "mu .-negligible" (format "mu .-negligible").
Reserved Notation "{ 'ae' m , P }" (format "{ 'ae'  m ,  P }").
Reserved Notation "\forall x \ae mu , P"
  (at level 200, x name, P at level 200, format "\forall  x  \ae  mu ,  P").
Reserved Notation "f = g %[ae mu 'in' D ]"
  (at level 70, g at next level, format "f  =  g  '%[ae'  mu  'in'  D ]").
Reserved Notation "f = g %[ae mu ]"
  (at level 70, g at next level, format "f  =  g  '%[ae'  mu ]").
Reserved Notation "m .-null_set" (at level 2, format "m .-null_set").
Reserved Notation "m1 `<< m2" (at level 51).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section negligible.
Context d (T : semiRingOfSetsType d) (R : realFieldType).

Definition negligible (mu : set T -> \bar R) N :=
  exists A, [/\ measurable A, mu A = 0 & N `<=` A].

Local Notation "mu .-negligible" := (negligible mu).

Variable mu : {content set T -> \bar R}.

Lemma negligibleP A : measurable A -> mu.-negligible A <-> mu A = 0.
Proof.
move=> mA; split => [[B [mB mB0 AB]]|mA0]; last by exists A; split.
by apply/eqP; rewrite -measure_le0 -mB0 le_measure ?inE.
Qed.

Lemma negligible_set0 : mu.-negligible set0.
Proof. exact/negligibleP. Qed.

Lemma measure_negligible (A : set T) :
  measurable A -> mu.-negligible A -> mu A = 0%E.
Proof. by move=> mA /negligibleP ->. Qed.

Lemma negligibleS A B : B `<=` A -> mu.-negligible A -> mu.-negligible B.
Proof.
by move=> BA [N [mN N0 AN]]; exists N; split => //; exact: subset_trans AN.
Qed.

Lemma negligibleI A B :
  mu.-negligible A -> mu.-negligible B -> mu.-negligible (A `&` B).
Proof.
move=> [N [mN N0 AN]] [M [mM M0 BM]]; exists (N `&` M); split => //.
- exact: measurableI.
- by apply/eqP; rewrite -measure_le0 -N0 le_measure ?inE//; exact: measurableI.
- exact: setISS.
Qed.

End negligible.
Notation "mu .-negligible" := (negligible mu) : type_scope.

Definition measure_is_complete d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : set T -> \bar R) :=
  mu.-negligible `<=` measurable.

Section negligible_ringOfSetsType.
Context d (T : ringOfSetsType d) (R : realFieldType).
Variable mu : {content set T -> \bar R}.

Lemma negligibleU A B :
  mu.-negligible A -> mu.-negligible B -> mu.-negligible (A `|` B).
Proof.
move=> [N [mN N0 AN]] [M [mM M0 BM]]; exists (N `|` M); split => //.
- exact: measurableU.
- apply/eqP; rewrite -measure_le0 -N0 -[leRHS]adde0 -M0 -bigsetU_bigcup2.
  apply: le_trans.
  + apply: (@content_subadditive _ _ _ _ _ (bigcup2 N M) 2%N) => //.
    * by move=> [|[|[|]]].
    * apply: bigsetU_measurable => // i _; rewrite /bigcup2.
      by case: ifPn => // i0; case: ifPn.
  + by rewrite big_ord_recr/= big_ord_recr/= big_ord0 add0e.
- exact: setUSS.
Qed.

Lemma negligible_bigsetU (F : (set T)^nat) s (P : pred nat) :
  (forall k, P k -> mu.-negligible (F k)) ->
  mu.-negligible (\big[setU/set0]_(k <- s | P k) F k).
Proof.
by move=> PF; elim/big_ind : _ => //;
  [exact: negligible_set0|exact: negligibleU].
Qed.

End negligible_ringOfSetsType.

Lemma negligible_bigcup d (T : sigmaRingType d) (R : realFieldType)
    (mu : {measure set T -> \bar R}) (F : (set T)^nat) :
  (forall k, mu.-negligible (F k)) -> mu.-negligible (\bigcup_k F k).
Proof.
move=> mF; exists (\bigcup_k sval (cid (mF k))); split.
- by apply: bigcupT_measurable => // k; have [] := svalP (cid (mF k)).
- rewrite seqDU_bigcup_eq measure_bigcup//; last first.
    move=> k _; apply: measurableD; first by case: cid => //= A [].
    by apply: bigsetU_measurable => i _; case: cid => //= A [].
  rewrite eseries0// => k _ _.
  have [mFk mFk0 ?] := svalP (cid (mF k)).
  rewrite measureD//=.
  + rewrite mFk0 sub0e eqe_oppLRP oppe0; apply/eqP; rewrite -measure_le0.
    rewrite -[leRHS]mFk0 le_measure//= ?inE//; apply: measurableI => //.
    by apply: bigsetU_measurable => i _; case: cid => // A [].
  + by apply: bigsetU_measurable => i _; case: cid => // A [].
  + by rewrite mFk0.
- by apply: subset_bigcup => k _; rewrite /sval/=; by case: cid => //= A [].
Qed.

Section ae.

Definition almost_everywhere d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : set T -> \bar R) : set_system T :=
  fun P => mu.-negligible (~` [set x | P x]).

Let almost_everywhereT d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : {content set T -> \bar R}) : almost_everywhere mu setT.
Proof. by rewrite /almost_everywhere setCT; exact: negligible_set0. Qed.

Let almost_everywhereS d (T : semiRingOfSetsType d) (R : realFieldType)
    (mu : {measure set T -> \bar R}) A B : A `<=` B ->
  almost_everywhere mu A -> almost_everywhere mu B.
Proof. by move=> AB; apply: negligibleS; exact: subsetC. Qed.

Let almost_everywhereI d (T : ringOfSetsType d) (R : realFieldType)
    (mu : {measure set T -> \bar R}) A B :
  almost_everywhere mu A -> almost_everywhere mu B ->
  almost_everywhere mu (A `&` B).
Proof.
by rewrite /almost_everywhere => mA mB; rewrite setCI; exact: negligibleU.
Qed.

Definition ae_filter_ringOfSetsType d {T : ringOfSetsType d} (R : realFieldType)
  (mu : {measure set T -> \bar R}) : Filter (almost_everywhere mu).
Proof.
by split; [exact: almost_everywhereT|exact: almost_everywhereI|
  exact: almost_everywhereS].
Qed.

Definition ae_properfilter_algebraOfSetsType d {T : algebraOfSetsType d}
    (R : realFieldType) (mu : {measure set T -> \bar R}) :
  (mu [set: T] > 0)%E -> ProperFilter (almost_everywhere mu).
Proof.
move=> muT; split=> [|]; last exact: ae_filter_ringOfSetsType.
rewrite /almost_everywhere setC0 => /(measure_negligible measurableT).
by move/eqP; rewrite -measure_le0 leNgt => /negP.
Qed.

End ae.

#[global] Hint Extern 0 (Filter (almost_everywhere _)) =>
  (apply: ae_filter_ringOfSetsType) : typeclass_instances.
#[global] Hint Extern 0 (Filter (nbhs (almost_everywhere _))) =>
  (apply: ae_filter_ringOfSetsType) : typeclass_instances.

#[global] Hint Extern 0 (ProperFilter (almost_everywhere _)) =>
  (apply: ae_properfilter_algebraOfSetsType) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter (nbhs (almost_everywhere _))) =>
  (apply: ae_properfilter_algebraOfSetsType) : typeclass_instances.

Notation "{ 'ae' m , P }" := {near almost_everywhere m, P} : type_scope.
Notation "\forall x \ae mu , P" := (\forall x \near almost_everywhere mu, P)
  : type_scope.
Definition ae_eq d (T : semiRingOfSetsType d) (R : realType)
    (mu : {measure set T -> \bar R}) (V : T -> Type) D (f g : forall x, V x) :=
  \forall x \ae mu, D x -> f x = g x.
Notation "f = g %[ae mu 'in' D ]" := (\forall x \ae mu, D x -> f x = g x).
Notation "f = g %[ae mu ]" := (f = g %[ae mu in setT ]).

Lemma measure0_ae d {T : algebraOfSetsType d} {R : realType}
    (mu : {measure set T -> \bar R}) (P : set T) :
  mu [set: T] = 0 -> \forall x \ae mu, P x.
Proof. by move=> x; exists setT. Qed.

Lemma aeW {d} {T : semiRingOfSetsType d} {R : realFieldType}
    (mu : {measure set _ -> \bar R}) (P : T -> Prop) :
  (forall x, P x) -> \forall x \ae mu, P x.
Proof.
move=> aP; have -> : P = setT by rewrite predeqE => t; split.
by apply/negligibleP; [rewrite setCT|rewrite setCT measure0].
Qed.

Instance ae_eq_equiv d (T : ringOfSetsType d) R mu V D :
  RelationClasses.Equivalence (@ae_eq d T R mu V D).
Proof.
split.
- by move=> f; near=> x.
- by move=> f g eqfg; near=> x => Dx; rewrite (near eqfg).
- by move=> f g h eqfg eqgh; near=> x => Dx; rewrite (near eqfg) ?(near eqgh).
Unshelve. all: by end_near. Qed.

Section ae_eq.
Local Open Scope ring_scope.
Context d (T : sigmaRingType d) (R : realType).
Implicit Types (U V : Type) (W : pzRingType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Local Notation ae_eq := (ae_eq mu D).

Lemma ae_eq0 U (f g : T -> U) : measurable D -> mu D = 0 -> f = g %[ae mu in D].
Proof. by move=> mD D0; exists D; split => // t/= /not_implyP[]. Qed.

Instance comp_ae_eq U V (j : T -> U -> V) :
  Proper (ae_eq ==> ae_eq) (fun f x => j x (f x)).
Proof. by move=> f g; apply: filterS => x /[apply] /= ->. Qed.

Instance comp_ae_eq2 U U' V (j : T -> U -> U' -> V) :
  Proper (ae_eq ==> ae_eq ==> ae_eq) (fun f g x => j x (f x) (g x)).
Proof. by move=> f f' + g g'; apply: filterS2 => x + + Dx => -> // ->. Qed.

Instance comp_ae_eq2' U U' V (j : U -> U' -> V) :
  Proper (ae_eq ==> ae_eq ==> ae_eq) (fun f g x => j (f x) (g x)).
Proof. by move=> f f' + g g'; apply: filterS2 => x + + Dx => -> // ->. Qed.

Instance sub_ae_eq2 : Proper (ae_eq ==> ae_eq ==> ae_eq) (@GRing.sub_fun T R).
Proof. exact: (@comp_ae_eq2' _ _  R (fun x y => x - y)). Qed.

Lemma ae_eq_refl U (f : T -> U) : ae_eq f f. Proof. exact/aeW. Qed.
Hint Resolve ae_eq_refl : core.

Lemma ae_eq_comp U V (j : U -> V) f g : ae_eq f g -> ae_eq (j \o f) (j \o g).
Proof. by move->. Qed.

Lemma ae_eq_comp2 U V (j : T -> U -> V) f g :
  ae_eq f g -> ae_eq (fun x => j x (f x)) (fun x => j x (g x)).
Proof. by apply: filterS => x /[swap] + ->. Qed.

Local Open Scope ereal_scope.
Lemma ae_eq_funeposneg (f g : T -> \bar R) :
  ae_eq f g <-> ae_eq f^\+ g^\+ /\ ae_eq f^\- g^\-.
Proof.
split=> [fg|[pfg nfg]].
  by split; near=> x => Dx; rewrite !(funeposE,funenegE) (near fg).
by near=> x => Dx; rewrite (funeposneg f) (funeposneg g) ?(near pfg, near nfg).
Unshelve. all: by end_near. Qed.
Local Close Scope ereal_scope.

Lemma ae_eq_sym U (f g : T -> U) : ae_eq f g -> ae_eq g f.
Proof. by symmetry. Qed.

Lemma ae_eq_trans U (f g h : T -> U) : ae_eq f g -> ae_eq g h -> ae_eq f h.
Proof. by apply transitivity. Qed.

Lemma ae_eq_sub W (f g h i : T -> W) : ae_eq f g -> ae_eq h i -> ae_eq (f \- h) (g \- i).
Proof. by apply: filterS2 => x + + Dx => /= /(_ Dx) -> /(_ Dx) ->. Qed.

Lemma ae_eq_mul2r W (f g h : T -> W) : ae_eq f g -> ae_eq (f \* h) (g \* h).
Proof. by move=>/(ae_eq_comp2 (fun x y => y * h x)). Qed.

Lemma ae_eq_mul2l W (f g h : T -> W) : ae_eq f g -> ae_eq (h \* f) (h \* g).
Proof. by move=>/(ae_eq_comp2 (fun x y => h x * y)). Qed.

Lemma ae_eq_mul1l W (f g : T -> W) : ae_eq f (cst 1) -> ae_eq g (g \* f).
Proof. by apply: filterS => x /= /[apply] ->; rewrite mulr1. Qed.

Lemma ae_eq_abse (f g : T -> \bar R) : ae_eq f g -> ae_eq (abse \o f) (abse \o g).
Proof. by apply: filterS => x /[apply] /= ->. Qed.

Lemma ae_foralln (P : nat -> T -> Prop) :
  (forall n, \forall x \ae mu, P n x) -> \forall x \ae mu, forall n, P n x.
Proof.
move=> /(_ _)/cid - /all_sig[A /all_and3[Ameas muA0 NPA]].
have seqDUAmeas := seqDU_measurable Ameas.
exists (\bigcup_n A n); split => //.
- exact/bigcup_measurable.
- rewrite seqDU_bigcup_eq measure_bigcup// eseries0// => i _ _.
  by rewrite (@subset_measure0 _ _ _ _ _ (A i))//=; apply: subset_seqDU.
- by move=> x /=; rewrite -existsNP => -[n NPnx]; exists n => //; apply: NPA.
Qed.

End ae_eq.

Section ae_eq_lemmas.
Context d (T : sigmaRingType d) (R : realType) (U : Type).
Implicit Types (mu : {measure set T -> \bar R}) (A : set T) (f g : T -> U).

Lemma ae_eq_subset mu A B f g : B `<=` A -> ae_eq mu A f g -> ae_eq mu B f g.
Proof. by move=> BA; apply: filterS => x + /BA; apply. Qed.

End ae_eq_lemmas.

Section ae_eqe.
Context d (T : sigmaRingType d) (R : realType).
Local Open Scope ereal_scope.
Implicit Types (mu : {measure set T -> \bar R}) (D : set T) (f g h : T -> \bar R).

Lemma ae_eqe_mul2l mu D f g h : ae_eq mu D f g -> ae_eq mu D (h \* f)%E (h \* g).
Proof. by apply: filterS => x /= /[apply] ->. Qed.

End ae_eqe.

Section null_set.
Context d (T : semiRingOfSetsType d) (R : numDomainType).
Implicit Types m : set T -> \bar R.

Definition null_set m :=
  [set N | forall A, measurable A -> A `<=` N -> m A = 0].

End null_set.
Notation "m .-null_set" := (null_set m).

Section null_set_lemmas.
Context d (T : semiRingOfSetsType d) (R : numDomainType).
Implicit Types m : set T -> \bar R.

Lemma subset_null_set m A B : A `<=` B -> m.-null_set B -> m.-null_set A.
Proof. by move=> AB + N mN NA; apply => //; exact: subset_trans AB. Qed.

End null_set_lemmas.

Section content_null_set_lemmas.
Context d (T : measurableType d) (R : realType).
Implicit Types m : {content set T -> \bar R}.

Lemma negligible_null_set m A : m.-negligible A -> m.-null_set A.
Proof.
move=> [N [mN N0 AN]]; apply: (subset_null_set AN) => C mC CN.
by apply/eqP; rewrite -measure_le0 -N0 le_measure// inE.
Qed.

Lemma measure_null_setP m A : measurable A -> m.-null_set A <-> m A = 0.
Proof.
move=> mA; split; [exact|move=> A0].
by apply: negligible_null_set; exists A; split.
Qed.

Lemma null_setU m B : measurable B ->
  m.-null_set B <->
  (forall A, measurable A -> m (A `|` B) = m A).
Proof.
move=> mB; split.
- move=> nullB A mA; apply/eqP; rewrite eq_le.
  rewrite (@le_measure _ _ _ _ A) ?inE ?andbT//; last exact: measurableU.
  by rewrite (le_trans (measureU2 _ _ _))// (nullB B)// adde0.
- move=> B0 A mA AB.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  by rewrite -(measure0 m) -[leRHS]B0// set0U le_measure// inE.
Qed.

End content_null_set_lemmas.

Section absolute_continuity.
Context d (T : semiRingOfSetsType d) (R : realType).
Implicit Types m : set T -> \bar R.

Definition null_dominates m2 m1 := m2.-null_set `<=` m1.-null_set.

End absolute_continuity.
Notation "m1 `<< m2" := (null_dominates m2 m1).

Section null_dominates_lemmas.
Context d (T : semiRingOfSetsType d) (R : realType).
Implicit Types m : set T -> \bar R.

Lemma null_dominates_trans m1 m2 m3 : m1 `<< m2 -> m2 `<< m3 -> m1 `<< m3.
Proof. by move=> m12 m23 A /m23 /m12. Qed.

End null_dominates_lemmas.

Definition content_dominates {d} {T : measurableType d} {R : realType}
    (mu : {content set T -> \bar R}) (nu : set T -> \bar R) :=
  forall A, measurable A -> mu A = 0 -> nu A = 0.

Section content_null_dominates_lemmas.
Context d (T : measurableType d) (R : realType).
Implicit Types (mu : {content set T -> \bar R}).

Lemma content_null_dominatesP (nu : set T -> \bar R) mu :
  nu `<< mu <-> content_dominates mu nu.
Proof.
split.
- by move=> dom A mA muA0; apply: (dom A) => //; exact/measure_null_setP.
- by move=> + A muA0 B mB BA; apply => //; exact: muA0.
Qed.

End content_null_dominates_lemmas.

Section measure_null_dominates_lemmas.
Context d (T : measurableType d) (R : realType) (U : Type).
Implicit Types (nu mu : {measure set T -> \bar R}) (f g : T -> U).

Lemma null_dominates_ae_eq nu mu f g E : measurable E ->
  nu `<< mu -> ae_eq mu E f g -> ae_eq nu E f g.
Proof.
move=> mE /content_null_dominatesP m21 [A [*]]; exists A; split => //.
exact: m21.
Qed.

End measure_null_dominates_lemmas.
#[deprecated(since="mathcomp-analysis 1.15.0", note="renamed `null_dominates_ae_eq`")]
Notation measure_dominates_ae_eq := null_dominates_ae_eq (only parsing).
