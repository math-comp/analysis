(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum finmap.
Require Import boolp classical_sets reals ereal posnum nngnum topology.
Require Import normedtype sequences cardinality csum.
From HB Require Import structures.

(******************************************************************************)
(*                            Measure Theory                                  *)
(*                                                                            *)
(* semiRingOfSetsType == the type of semirings of sets                        *)
(*     ringOfSetsType == the type of rings of sets                            *)
(*  algebraOfSetsType == the type of algebras of sets                         *)
(*     measurableType == the type of sigma-algebras                           *)
(*   sigma_finite A f == the measure f is sigma-finite on A : set T with      *)
(*                       T : ringOfSetsType.                                  *)
(*                                                                            *)
(* {additive_measure set T -> {ereal R}} == type of a function over sets of   *)
(*                    elements of type T where R is expected to be a          *)
(*                    numFieldType such that this function maps set0 to 0, is *)
(*                    non-negative over measurable sets, and is semi-additive *)
(* {measure set T -> {ereal R}} == type of a function over sets of elements   *)
(*                   of type T where R is expected to be a numFieldType such  *)
(*                   that this function maps set0 to 0, is non-negative over  *)
(*                   measurable sets and is semi-sigma-additive               *)
(*                                                                            *)
(*          seqDU F == the sequence F_0, F_1 \ F_0, F_2 \ (F_0 U F_1),...     *)
(*           seqD F == the sequence F_0, F_1 \ F_0, F_2 \ F_1,...             *)
(*                                                                            *)
(* Theorems: Boole_inequality, generalized_Boole_inequality                   *)
(*                                                                            *)
(* mu.-negligible A == A is mu negligible                                     *)
(* {ae mu, forall x, P x} == P holds almost everywhere for the measure mu     *)
(*                                                                            *)
(* {outer_measure set T -> {ereal R}} == type of an outer measure over sets   *)
(*                                 of elements of type T where R is expected  *)
(*                                 to be a numFieldType                       *)
(*                                                                            *)
(*    mu.-measurable X == X is Caratheodory measurable for the outer measure  *)
(*                        mu, i.e.,                                           *)
(*                        forall Y, mu X = mu (X `&` Y) + mu (X `&` ~` Y)     *)
(* measure_is_complete mu == the measure mu is complete                       *)
(*                                                                            *)
(*     measurable_fun D f == the function f with domain D is measurable       *)
(*                                                                            *)
(* Caratheodory theorem:                                                      *)
(* caratheodory_type mu := T, where mu : {outer_measure set T -> {ereal R}}   *)
(*                         it is a canonical mesurableType copy of T.         *)
(* caratheodory_measure mu == the restriction of the outer measure mu to the  *)
(*                         sigma algebra of Caratheodory measurable sets is a *)
(*                         measure                                            *)
(*                         Remark: sets that are negligible for               *)
(*                         caratheodory_measure are Caratheodory measurable   *)
(*                                                                            *)
(* Extension theorem:                                                         *)
(* measurable_cover X == the set of sequences F such that                     *)
(*                       - forall i, F i is measurable                        *)
(*                       - X `<=` \bigcup_i (F i)                             *)
(*          mu_ext mu == the extension of the measure mu, a measure over a    *)
(*                       ring of sets; it is an outer measure, declared as    *)
(*                       canonical (i.e., we have the notation                *)
(*                       [outer_measure of mu_ext mu])                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Reserved Notation "mu .-negligible" (at level 2, format "mu .-negligible").
Reserved Notation "{ 'ae' m , P }" (at level 0, format "{ 'ae'  m ,  P }").
Reserved Notation "mu .-measurable" (at level 2, format "mu .-measurable").

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: remove when available in all the Coq versions supported by the CI
   (as of today, only in Coq 8.13) *)
Definition uncurry {A B C : Type} (f : A -> B -> C)
  (p : A * B) : C := match p with (x, y) => f x y end.

Definition bigcup2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0%N then A else if i == 1%N then B else set0.

Lemma bigcup2E T (A B : set T) : \bigcup_i (bigcup2 A B) i = A `|` B.
Proof.
rewrite predeqE => t; split=> [|[At|Bt]]; [|by exists 0%N|by exists 1%N].
by case=> -[_ At|[_ Bt|//]]; [left|right].
Qed.

HB.mixin Record isSemiRingOfSets T := {
  measurable : set (set T) ;
  diff_fsets : set T -> set T -> {fset (set T)} ;
  measurable0 : measurable set0 ;
  measurableI : forall A B, measurable A -> measurable B ->
    measurable (A `&` B) ;
  measurable_diff_fsets : forall A B C, measurable A -> measurable B ->
    is_true (C \in diff_fsets A B) -> measurable C ;
  (* we skip the hypos measurable A measurable B because we can define a *)
  (* default behavior (diff A B = [set A `\` B]) when A or B are not in  *)
  (* measurable *)
  diff_fsetsE : forall A B, (*measurable A -> measurable B -> *)
    A `\` B = \big[setU/set0]_(X <- enum_fset (diff_fsets A B)) X ;
  diff_fsets_disjoint : forall A B C D, (*measurable A -> measurable B ->*)
    is_true (C != D) -> is_true (C \in diff_fsets A B) ->
    is_true (D \in diff_fsets A B) -> C `&` D = set0 }.

HB.structure Definition SemiRingOfSets := {T of isSemiRingOfSets T}.

Notation semiRingOfSetsType := SemiRingOfSets.type.

HB.mixin Record RingOfSets_from_semiRingOfSets T of isSemiRingOfSets T := {
  measurableU : forall A B : set T,
    measurable A -> measurable B -> measurable (A `|` B) }.

HB.structure Definition RingOfSets := {T of RingOfSets_from_semiRingOfSets T &}.

Notation ringOfSetsType := RingOfSets.type.

HB.mixin Record AlgebraOfSets_from_RingOfSets T of RingOfSets T := {
  measurableT : measurable (@setT T)
}.

HB.structure Definition AlgebraOfSets := {T of AlgebraOfSets_from_RingOfSets T &}.

Notation algebraOfSetsType := AlgebraOfSets.type.

HB.mixin Record Measurable_from_algebraOfSets T of AlgebraOfSets T := {
  measurable_bigcup : forall U : (set T)^nat, (forall i, measurable (U i)) ->
    measurable (\bigcup_i (U i))
}.

HB.structure Definition Measurable := {T of Measurable_from_algebraOfSets T &}.

Notation measurableType := Measurable.type.

HB.factory Record isAlgebraOfSets T := {
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableU : forall A B, measurable A -> measurable B -> measurable (A `|` B) ;
  measurableC : forall A, measurable A -> measurable (~` A)
}.

HB.builders Context T of isAlgebraOfSets T.

Lemma semiRingOfSets_measurableI (A B : set T) :
  measurable A -> measurable B -> measurable (A `&` B).
Proof.
move=> mA mB.
have -> : A `&` B = ~` (~` A `|` ~` B).
  by rewrite -setCI setCK.
by apply: measurableC; apply: measurableU; apply: measurableC.
Qed.

Definition diff_fsets := (fun A B : set T => ([fset (A `&` ~` B)%classic])%fset).

Lemma semiRingOfSets_measurableD (A B C : set T) :
  measurable A -> measurable B -> C \in diff_fsets A B -> measurable C.
Proof.
move=> mA mB; rewrite inE => /eqP ->.
by apply: semiRingOfSets_measurableI => //; apply: measurableC.
Qed.

Lemma semiRingOfSets_diff_fsetsE A B :
  A `\` B = \big[setU/set0]_(X <- enum_fset (diff_fsets A B)) X.
Proof. by rewrite big_seq_fset1. Qed.

Lemma semiRingOfSets_diff_fsets_disjoint A B C D : C != D ->
  C \in diff_fsets A B -> D \in diff_fsets A B -> C `&` D = set0.
Proof.
by move=> /= CS; rewrite !inE => CAB DAB; move: CS; rewrite CAB DAB eqxx.
Qed.

HB.instance Definition T_isSemiRingOfSets : isSemiRingOfSets T :=
  @isSemiRingOfSets.Build T measurable diff_fsets
    measurable0
    semiRingOfSets_measurableI
    semiRingOfSets_measurableD
    semiRingOfSets_diff_fsetsE
    semiRingOfSets_diff_fsets_disjoint.

HB.instance Definition T_isRingOfSets : RingOfSets_from_semiRingOfSets T :=
  RingOfSets_from_semiRingOfSets.Build T measurableU.

Lemma measurableT : measurable (@setT T).
Proof. by rewrite -setC0; apply measurableC; exact: measurable0. Qed.

HB.instance Definition T_isAlgebraOfSets : AlgebraOfSets_from_RingOfSets T :=
  AlgebraOfSets_from_RingOfSets.Build T measurableT.

HB.end.

HB.factory Record isMeasurable T := {
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableC : forall A, measurable A -> measurable (~` A) ;
  measurable_bigcup : forall U : (set T)^nat, (forall i, measurable (U i)) ->
    measurable (\bigcup_i (U i))
}.

HB.builders Context T of isMeasurable T.

Obligation Tactic := idtac.

Lemma algebraOfSets_measurableU (A B : set T) :
  measurable A -> measurable B -> measurable (A `|` B).
Proof.
move=> mA mB; rewrite -bigcup2E.
by apply measurable_bigcup => -[//|[//|i]]; exact: measurable0.
Qed.

Lemma algebraOfSets_measurableC (A : set T) : measurable A -> measurable (~` A).
Proof. by move=> mA; apply: measurableC. Qed.

HB.instance Definition T_isAlgebraOfSets : isAlgebraOfSets T :=
  @isAlgebraOfSets.Build T measurable
    measurable0
    algebraOfSets_measurableU
    algebraOfSets_measurableC.

HB.instance Definition T_isMeasurable : Measurable_from_algebraOfSets T :=
  @Measurable_from_algebraOfSets.Build _ measurable_bigcup.

HB.end.

Section ringofsets_lemmas.
Variables T : ringOfSetsType.
Implicit Types A B : set T.

Lemma bigsetU_measurable I r (P : pred I) (F : I -> set T) :
  (forall i, P i -> measurable (F i)) ->
  measurable (\big[setU/set0]_(i <- r | P i) F i).
Proof.
move=> mF; elim/big_ind : _ => //; [exact: measurable0|exact: measurableU].
Qed.

Lemma measurableD A B : measurable A -> measurable B -> measurable (A `\` B).
Proof.
move=> mA mB; rewrite diff_fsetsE big_seq_cond; apply: bigsetU_measurable => /=.
by move=> i; rewrite andbT; exact: measurable_diff_fsets.
Qed.

End ringofsets_lemmas.

Section algebraofsets_lemmas.
Variables T : algebraOfSetsType.
Implicit Types A B : set T.

Lemma measurableC A : measurable A -> measurable (~` A).
Proof.
by move=> mA; rewrite -setTD; apply: measurableD => //; exact: measurableT.
Qed.

Lemma bigsetI_measurable I r (P : pred I) (F : I -> set T) :
  (forall i, P i -> measurable (F i)) ->
  measurable (\big[setI/setT]_(i <- r | P i) F i).
Proof.
move=> mF; rewrite -[X in measurable X]setCK setC_bigsetI; apply: measurableC.
by apply: bigsetU_measurable => i Pi; apply/measurableC/mF.
Qed.

End algebraofsets_lemmas.

Section measurable_lemmas.
Variables T : measurableType.
Implicit Types A B : set T.

Lemma bigcup_measurable (F : (set T)^nat) (P : set nat) :
  (forall k, P k -> measurable (F k)) -> measurable (\bigcup_(i in P) F i).
Proof.
move=> PF; rewrite bigcup_mkcond; apply: measurable_bigcup => k.
by case: asboolP => Pk; [exact: PF|exact: measurable0].
Qed.

Lemma bigcap_measurable (F : (set T)^nat) (P : set nat) :
  (forall k, P k -> measurable (F k)) -> measurable (\bigcap_(i in P) F i).
Proof.
move=> PF; rewrite -[X in measurable X]setCK setC_bigcap; apply: measurableC.
by apply: bigcup_measurable => k Pk; exact/measurableC/PF.
Qed.

Lemma measurable_bigcap (F : (set T)^nat) :
  (forall i, measurable (F i)) -> measurable (\bigcap_i (F i)).
Proof. by move=> ?; apply: bigcap_measurable. Qed.

End measurable_lemmas.

Local Open Scope ereal_scope.

Definition sigma_finite (R : numDomainType) (T : ringOfSetsType) (A : set T)
    (mu : set T -> \bar R) :=
  exists2 F : (set T)^nat,
    A = \bigcup_(i : nat) F i &
      forall i, measurable (F i) /\ mu (F i) < +oo.

Section semi_additivity.
Variables (R : numFieldType) (T : semiRingOfSetsType) (mu : set T -> \bar R).

Definition semi_additive2 := forall A B, measurable A -> measurable B ->
  measurable (A `|` B) ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition semi_additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  (forall n, measurable (\big[setU/set0]_(i < n) A i)) ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (A i).

Definition semi_sigma_additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  measurable (\bigcup_n A n) ->
  (fun n => \sum_(i < n) mu (A i)) --> mu (\bigcup_n A n).

Definition additive2 := forall A B, measurable A -> measurable B ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (A i).

Definition sigma_additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  (fun n => \sum_(i < n) mu (A i)) --> mu (\bigcup_n A n).

Lemma semi_additive2P : mu set0 = 0 -> semi_additive <-> semi_additive2.
Proof.
move=> mu0; split => [amx A B mA mB mAB AB|a2mx A mA /trivIsetP ATI mbigA n].
  set C := bigcup2 A B.
  have tC : trivIset setT C.
    by apply/trivIsetP => -[|[|i]] [|[|j]]; rewrite ?set0I ?setI0// setIC.
  have mC : forall i, measurable (C i).
    by move=> [|[]] //= i; exact: measurable0.
  have := amx _ mC tC _ 2%N; rewrite !big_ord_recl !big_ord0 adde0/= setU0.
  rewrite /C /bigcup2 /=; apply.
  (* TODO: clean *)
  case=> [|[|n]].
  by rewrite big_ord0; exact: measurable0.
  by rewrite big_ord_recr /= big_ord0 set0U.
  by rewrite !big_ord_recl /= big1 // setU0.
elim: n => [|n IHn] in A mA ATI mbigA *.
  by rewrite !big_ord0.
rewrite big_ord_recr /= a2mx //; last 3 first.
- exact: mbigA.
- by have := mbigA n.+1; rewrite big_ord_recr.
- by rewrite big_distrl /= big1 // => i _; rewrite ATI// ltn_eqF.
- by rewrite IHn // [in RHS]big_ord_recr.
Qed.

End semi_additivity.

Section additivity.
Variables (R : numFieldType) (T : ringOfSetsType) (mu : set T -> \bar R).

Lemma semi_additiveE : semi_additive mu = additive mu.
Proof.
rewrite propeqE; split=> [samu A mA tA n|amu A mA tA _ n]; last by rewrite amu.
by rewrite samu // => {}n; exact: bigsetU_measurable.
Qed.

Lemma semi_additive2E : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma additive2P : mu set0 = 0 -> additive mu <-> additive2 mu.
Proof. by rewrite -semi_additive2E -semi_additiveE; exact/semi_additive2P. Qed.

End additivity.

Lemma semi_sigma_additive_is_additive
  (R : realFieldType (*TODO: numFieldType if possible?*))
  (X : semiRingOfSetsType) (mu : set X -> \bar R) :
  mu set0 = 0 -> semi_sigma_additive mu -> semi_additive mu.
Proof.
move=> mu0 samu; apply/semi_additive2P => // A B mA mB mAB AB_eq0.
pose C := bigcup2 A B.
have tC : trivIset setT C.
  by apply/trivIsetP=> -[|[|i]] [|[|j]]; rewrite ?setI0 ?set0I// setIC.
have -> : A `|` B = \bigcup_i C i.
  rewrite predeqE => x; split.
    by case=> [Ax|Bx]; by [exists 0%N|exists 1%N].
  by case=> [[|[|n]]]//; by [left|right].
have mC : forall i, measurable (C i).
  by move=> [|[]] //= i; rewrite /C /=; exact: measurable0.
have mbigcupC : measurable (\bigcup_n C n) by rewrite bigcup2E.
have /cvg_unique := samu C mC tC mbigcupC; apply => //.
apply: cvg_near_cst.
exists 3%N => // -[//|[//|n]] _.
by rewrite !big_ord_recl /= big1 ?adde0.
Qed.

Lemma semi_sigma_additiveE
  (R : numFieldType) (X : measurableType) (mu : set X -> \bar R) :
  semi_sigma_additive mu = sigma_additive mu.
Proof.
rewrite propeqE; split=> [amu A mA tA|amu A mA tA mbigcupA]; last exact: amu.
by apply: amu => //; exact: measurable_bigcup.
Qed.

Lemma sigma_additive_is_additive
  (R : realFieldType) (X : measurableType) (mu : set X -> \bar R) :
  mu set0 = 0 -> sigma_additive mu -> additive mu.
Proof.
move=> mu0; rewrite -semi_sigma_additiveE -semi_additiveE.
exact: semi_sigma_additive_is_additive.
Qed.

Module AdditiveMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, measurable x -> 0 <= mu x ;
  _ : semi_additive2 mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation additive_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation AdditiveMeasure fA := (Pack (Phant _) fA).
Notation "{ 'additive_measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'additive_measure'  fUV }") : ring_scope.
Notation "[ 'additive_measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'additive_measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'additive_measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'additive_measure'  'of'  f ]") : form_scope.
End Exports.

End AdditiveMeasure.
Include AdditiveMeasure.Exports.

Section additive_measure_on_semiring_of_sets.
Variables (R : realFieldType) (T : semiRingOfSetsType)
  (mu : {additive_measure set T -> \bar R}).

Lemma measure0 : mu set0 = 0.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure0 : core.

Lemma measure_ge0 : forall x, measurable x -> 0 <= mu x.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_ge0 : core.

Lemma measure_semi_additive2 : semi_additive2 mu.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_semi_additive2 : core.

Lemma measure_semi_additive : semi_additive mu.
Proof. exact/semi_additive2P. Qed.

End additive_measure_on_semiring_of_sets.

Hint Resolve measure0 measure_ge0 measure_semi_additive2
  measure_semi_additive : core.

Section additive_measure_on_ring_of_sets.
Variables (R : realFieldType) (T : ringOfSetsType)
  (mu : {additive_measure set T -> \bar R}).

Lemma measureU : additive2 mu.
Proof. by rewrite -semi_additive2E. Qed.

Lemma measure_bigcup : additive mu.
Proof. by rewrite -semi_additiveE. Qed.

End additive_measure_on_ring_of_sets.

Hint Resolve measureU measure_bigcup : core.

Module Measure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, measurable x -> 0 <= mu x ;
  _ : semi_sigma_additive mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation is_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation Measure fA := (Pack (Phant _) fA).
Notation "{ 'measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'measure'  fUV }") : ring_scope.
Notation "[ 'measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'measure'  'of'  f ]") : form_scope.
End Exports.

End Measure.
Include Measure.Exports.

Section measure_lemmas.
Variables (R : numFieldType) (T : semiRingOfSetsType).
Variable mu : {measure set T -> \bar R}.

Lemma measure_semi_sigma_additive : semi_sigma_additive mu.
Proof. by case: mu => ? []. Qed.

End measure_lemmas.

Section measure_lemmas.
Variables (R : numFieldType) (T : measurableType).
Variable mu : {measure set T -> \bar R}.

Lemma measure_sigma_additive : sigma_additive mu.
Proof.
by rewrite -semi_sigma_additiveE //; apply: measure_semi_sigma_additive.
Qed.

End measure_lemmas.

Hint Extern 0 (_ set0 = 0) => solve [apply: measure0] : core.
Hint Extern 0 (sigma_additive _) =>
  solve [apply: measure_sigma_additive] : core.

Section measure_is_additive_measure.
Variables (R : realFieldType) (T : semiRingOfSetsType)
  (mu : {measure set T -> \bar R}).

Lemma measure_is_additive_measure : additive_measure mu.
Proof.
case: mu => f [f0 fg0 fsa]; split => //.
exact/(semi_additive2P f0)/semi_sigma_additive_is_additive.
Qed.

Canonical measure_additive_measure :=
  AdditiveMeasure measure_is_additive_measure.

End measure_is_additive_measure.

Coercion measure_additive_measure : Measure.map >-> AdditiveMeasure.map.

(* measure is monotone *)
Lemma le_measure (R : realFieldType) (T : ringOfSetsType)
  (mu : {additive_measure set T -> \bar R}) :
  {in [set x | measurable x] &, {homo mu : A B / A `<=` B >-> A <= B}}.
Proof.
move=> A B mA mB AB; have {1}-> : B = A `|` (B `\` A).
  rewrite funeqE => x; rewrite propeqE.
  have [Ax|Ax] := pselect (A x).
    split=> [Bx|]; by [left | move=> -[/AB //|] []].
  by split=> [Bx|]; by [right| move=> -[//|] []].
rewrite 2!inE in mA, mB.
have ? : measurable (B `\` A) by apply: measurableD.
rewrite measure_semi_additive2 // ?lee_addl // ?measure_ge0 //.
  exact: measurableU.
by rewrite setDE setICA (_ : _ `&` ~` _ = set0) ?setI0 // setICr.
Qed.

Section measureD.
Variables (R : realFieldType) (T : ringOfSetsType).
Variable mu : {measure set T -> \bar R}.

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
- rewrite (le_lt_trans _ mAoo)// le_measure // ?inE//.
  + exact: measurableI.
  + by apply: subIset; left.
- rewrite (lt_le_trans _ (measure_ge0 _ _))// ?lte_ninfty//.
  exact: measurableI.
Qed.

End measureD.

Section seqDU.
Variables (T : Type).
Implicit Types F : (set T)^nat.

Definition seqDU F n := F n `\` \big[setU/set0]_(k < n) F k.

Lemma trivIset_seqDU F : trivIset setT (seqDU F).
Proof.
move=> i j _ _; wlog ij : i j / (i < j)%N => [/(_ _ _ _) tB|].
  by have [ij /tB->|ij|] := ltngtP i j; rewrite //setIC => /tB ->.
move=> /set0P; apply: contraNeq => _; apply/eqP.
rewrite /seqDU 2!setDE !setIA setIC (bigD1 (Ordinal ij)) //=.
by rewrite setCU setIAC !setIA setICl !set0I.
Qed.

Lemma bigsetU_seqDU F n :
  \big[setU/set0]_(k < n) F k = \big[setU/set0]_(k < n) seqDU F k.
Proof.
elim: n => [|n ih]; first by rewrite 2!big_ord0.
rewrite !big_ord_recr /= predeqE => t; split=> [[Ft|Fnt]|[Ft|[Fnt Ft]]].
- by left; rewrite -ih.
- have [?|?] := pselect ((\big[setU/set0]_(i < n) seqDU F i) t); first by left.
  by right; split => //; rewrite ih.
- by left; rewrite ih.
- by right.
Qed.

Lemma seqDU_bigcup_eq F : \bigcup_k F k = \bigcup_k seqDU F k.
Proof.
rewrite /seqDU predeqE => t; split=> [[n _ Fnt]|[n _]]; last first.
  by rewrite setDE => -[? _]; exists n.
have [UFnt|UFnt] := pselect ((\big[setU/set0]_(k < n) F k) t); last by exists n.
suff [m [Fmt FNmt]] : exists m, F m t /\ forall k, (k < m)%N -> ~ F k t.
  by exists m => //; split => //; rewrite -bigcup_mkord => -[k kj]; exact: FNmt.
move: UFnt; rewrite -bigcup_mkord => -[/= k _ Fkt] {Fnt n}.
have [n kn] := ubnP k; elim: n => // n ih in t k Fkt kn *.
case: k => [|k] in Fkt kn *; first by exists O.
have [?|] := pselect (forall m, (m <= k)%N -> ~ F m t); first by exists k.+1.
move=> /existsNP[i] /not_implyP[ik] /contrapT Fit; apply (ih t i) => //.
by rewrite (leq_ltn_trans ik).
Qed.

End seqDU.

Section seqD.
Variables (T : Type).
Implicit Types F : (set T) ^nat.

Definition seqD F :=
  fun n => if n isn't n'.+1 then F O else F n `\` F n'.

Lemma seqDUE F : nondecreasing_seq F -> seqDU F = seqD F.
Proof.
move=> ndF; rewrite funeqE => -[|n] /=; first by rewrite /seqDU big_ord0 setD0.
rewrite /seqDU big_ord_recr /= setUC; congr (_ `\` _); apply/setUidPl.
by rewrite -bigcup_mkord => + [k /= kn]; exact/subsetPset/ndF/ltnW.
Qed.

Lemma trivIset_seqD F : nondecreasing_seq F -> trivIset setT (seqD F).
Proof. by move=> ndF; rewrite -seqDUE //; exact: trivIset_seqDU. Qed.

Lemma bigsetU_seqD F n :
  \big[setU/set0]_(i < n) F i = \big[setU/set0]_(i < n) seqD F i.
Proof.
case: n => [|n]; first by rewrite 2!big_ord0.
elim: n => [|n ih]; first by rewrite !big_ord_recl !big_ord0.
rewrite big_ord_recr [in RHS]big_ord_recr /= -{}ih predeqE => x; split.
  move=> [?|?]; first by left.
  have [?|?] := pselect (F n x); last by right.
  by left; rewrite big_ord_recr /=; right.
by move=> [?|[? ?]]; [left | right].
Qed.

Lemma setU_seqD F : nondecreasing_seq F ->
  forall n, F n.+1 = F n `|` seqD F n.+1.
Proof.
move=> ndF n; rewrite /seqD funeqE => x; rewrite propeqE; split.
by move=> ?; have [?|?] := pselect (F n x); [left | right].
by move=> -[|[]//]; move: x; exact/subsetPset/ndF.
Qed.

Lemma eq_bigsetU_seqD F n : nondecreasing_seq F ->
  F n = \big[setU/set0]_(i < n.+1) seqD F i.
Proof.
move=> ndF; elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
- by move=> ?; rewrite big_ord_recl big_ord0; left.
- by rewrite big_ord_recl big_ord0 setU0.
- rewrite (setU_seqD ndF) => -[|/=].
  by rewrite big_ord_recr /= -ih => Fnx; left.
  by move=> -[Fn1x Fnx]; rewrite big_ord_recr /=; right.
- by rewrite big_ord_recr /= -ih => -[|[]//]; move: x; exact/subsetPset/ndF.
Qed.

Lemma eq_bigcup_seqD F : \bigcup_n F n = \bigcup_n seqD F n.
Proof.
rewrite funeqE => x; rewrite propeqE; split.
  case; elim=> [_ F0x|n ih _ Fn1x]; first by exists O.
  have [|Fnx] := pselect (F n x); last by exists n.+1.
  by move=> /(ih I)[m _ Fmx]; exists m.
case; elim=> [_ /= F0x|n ih _ /= [Fn1x Fnx]]; by [exists O | exists n.+1].
Qed.

Lemma eq_bigcup_seqD_bigsetU F :
  \bigcup_n (seqD (fun n => \big[setU/set0]_(i < n.+1) F i) n) = \bigcup_n F n.
Proof.
rewrite -(@eq_bigcup_seqD (fun n => \big[setU/set0]_(i < n.+1) F i)).
rewrite eqEsubset; split => [t [i _]|t [i _ Fit]].
  by rewrite -bigcup_set_cond => -[/= j _ Fjt]; exists j.
by exists i => //; rewrite big_ord_recr /=; right.
Qed.

End seqD.

(* 401,p.43 measure is continuous from below *)
Lemma cvg_mu_inc (R : realFieldType) (T : ringOfSetsType)
  (mu : {measure set T -> \bar R}) (A : (set T) ^nat) :
  (forall i, measurable (A i)) -> measurable (\bigcup_n A n) ->
  nondecreasing_seq A ->
  mu \o A --> mu (\bigcup_n A n).
Proof.
move=> mA mbigcupA ndA.
have Binter : trivIset setT (seqD A) := trivIset_seqD ndA.
have ABE : forall n, A n.+1 = A n `|` seqD A n.+1 := setU_seqD ndA.
have AE n : A n = \big[setU/set0]_(i < n.+1) (seqD A) i := eq_bigsetU_seqD n ndA.
rewrite eq_bigcup_seqD.
have mB : forall i, measurable (seqD A i).
  by elim=> [|i ih] //=; apply: measurableD.
apply: cvg_trans (measure_semi_sigma_additive mB Binter _); last first.
  by rewrite -eq_bigcup_seqD.
apply: (@cvg_trans _ [filter of (fun n => \sum_(i < n.+1) mu (seqD A i))]).
  rewrite [X in _ --> X](_ : _ = mu \o A) // funeqE => n.
  rewrite -measure_semi_additive // -?AE// => -[|k]; last by rewrite -AE.
  by rewrite big_ord0; exact: measurable0.
by move=> S [n _] nS; exists n => // m nm; apply/(nS m.+1)/(leq_trans nm).
Qed.

Section boole_inequality.
Variables (R : realFieldType) (T : ringOfSetsType).
Variables (mu : {additive_measure set T -> \bar R}).

Theorem Boole_inequality (A : (set T) ^nat) : (forall i, measurable (A i)) ->
  forall n, mu (\big[setU/set0]_(i < n) A i) <= \sum_(i < n) mu (A i).
Proof.
move=> mA; elim => [|n ih]; first by rewrite !big_ord0 measure0.
set B := \big[setU/set0]_(i < n) A i.
set C := \big[setU/set0]_(i < n.+1) A i.
have -> : C = B `|` (A n `\` B).
  rewrite predeqE => x; split => [|[|[An1x _]]].
  - rewrite /C big_ord_recr /= => -[sumA|]; first by left.
    by have [?|?] := pselect (B x); [left|right].
  - by rewrite /C big_ord_recr; left.
  - by rewrite /C big_ord_recr; right.
have ? : measurable B by apply bigsetU_measurable.
rewrite measureU //; last 2 first.
  exact: measurableD.
  by rewrite setIC -setIA (_ : ~` _ `&` _ = set0) ?setI0 // setICl.
rewrite (@le_trans _ _ (mu B + mu (A n))) // ?lee_add2l //; last first.
  by rewrite big_ord_recr /= lee_add2r.
rewrite le_measure //.
- by rewrite inE; exact: measurableD.
- by rewrite inE; exact: mA.
- by apply subIset; left.
Qed.

End boole_inequality.
Notation le_mu_bigsetU := Boole_inequality.

Section sigma_finite_lemma.
Variables (R : realFieldType) (T : ringOfSetsType) (A : set T)
  (mu : {additive_measure set T -> \bar R}).

Lemma sigma_finiteP : sigma_finite A mu ->
  exists2 F, A = \bigcup_i F i &
    nondecreasing_seq F /\ forall i, measurable (F i) /\ mu (F i) < +oo.
Proof.
move=> [S AS moo]; exists (fun n => \big[setU/set0]_(i < n.+1) S i).
  rewrite AS predeqE => t; split => [[i _ Sit]|[i _]].
    by exists i => //; rewrite big_ord_recr /=; right.
  by rewrite -bigcup_mkord => -[j /= ji Sjt]; exists j.
split=> [|i].
- apply/nondecreasing_seqP => i.
  rewrite [in X in (_ <= X)%O]big_ord_recr /=.
  by apply/subsetPset; left.
- split; first by apply: bigsetU_measurable => j _; exact: (moo j).1.
  rewrite (@le_lt_trans _ _ (\sum_(j < i.+1) mu (S j)))//.
    by apply: Boole_inequality => j; exact: (moo j).1.
  by apply/lte_sum_pinfty => j _; exact: (moo j).2.
Qed.

End sigma_finite_lemma.

Section generalized_boole_inequality.
Variables (R : realType) (T : ringOfSetsType).
Variable (mu : {measure set T -> \bar R}).

(* 404,p.44 measure satisfies generalized Boole's inequality *)
Theorem generalized_Boole_inequality (A : (set T) ^nat) :
  (forall i, measurable (A i)) -> measurable (\bigcup_n A n) ->
  mu (\bigcup_n A n) <= \sum_(i <oo) mu (A i).
Proof.
move=> mA mbigcupA; set B := fun n => \big[setU/set0]_(i < n.+1) (A i).
have AB : \bigcup_k A k = \bigcup_n B n.
  rewrite predeqE => x; split => [[k _ ?]|[m _]].
    by exists k => //; rewrite /B big_ord_recr /=; right.
  rewrite /B big_ord_recr /= => -[|Amx]; last by exists m.
  by rewrite -bigcup_mkord => -[k ? ?]; exists k.
have ndB : nondecreasing_seq B.
  by move=> n m nm; exact/subsetPset/subset_bigsetU.
have mB : forall i, measurable (B i) by move=> i; exact: bigsetU_measurable.
rewrite AB.
move/(@cvg_mu_inc _ _ mu _ mB) : ndB => /(_ _)/cvg_lim <- //; last first.
  by rewrite -AB.
have -> : lim (mu \o B) = ereal_sup ((mu \o B) @` setT).
  suff : nondecreasing_seq (mu \o B).
    by move/nondecreasing_ereal_cvg; exact/cvg_lim.
  move=> n m nm; apply: le_measure => //; try by rewrite inE; apply mB.
  by move: nm; rewrite -ltnS; exact/subset_bigsetU.
have BA : forall m, mu (B m) <= \sum_(i <oo) mu (A i).
  move=> m.
  rewrite (le_trans (le_mu_bigsetU (measure_additive_measure mu) mA m.+1)) //.
  rewrite -(big_mkord xpredT (mu \o A)).
  apply: (@ereal_nneg_series_lim_ge _ (mu \o A) xpredT) => n _.
  exact: measure_ge0.
by apply ub_ereal_sup => /= x [n _ <-{x}]; apply BA.
Qed.

End generalized_boole_inequality.
Notation le_mu_bigcup := generalized_Boole_inequality.

Section negligible.
Variables (R : realFieldType) (T : ringOfSetsType).

Definition negligible (mu : set T -> \bar R) (N : set T) :=
  exists A : set T, [/\ measurable A, mu A = 0 & N `<=` A].

Local Notation "mu .-negligible" := (negligible mu).

Lemma negligibleP (mu : {measure _ -> _}) A :
  measurable A -> mu.-negligible A <-> mu A = 0.
Proof.
move=> mA; split => [[B [mB mB0 AB]]|mA0]; last by exists A; split.
apply/eqP; rewrite eq_le measure_ge0 // andbT -mB0.
by apply: (le_measure (measure_additive_measure mu)) => //; rewrite in_setE.
Qed.

Lemma negligible_set0 (mu : {measure _ -> _}) : mu.-negligible set0.
Proof. by apply/negligibleP => //; exact: measurable0. Qed.

Definition almost_everywhere (mu : set T -> \bar R) (P : T -> Prop)
     & (phantom Prop (forall x, P x)) :=
   mu.-negligible (~` [set x | P x]).
Local Notation "{ 'ae' m , P }" :=
  (almost_everywhere m (inPhantom P)) : type_scope.

Lemma aeW (mu : {measure _ -> _}) (P : T -> Prop) :
  (forall x, P x) -> {ae mu, forall x, P x}.
Proof.
move=> aP; have -> : P = setT by rewrite predeqE => t; split.
apply/negligibleP; first by rewrite setCT; exact: measurable0.
by rewrite setCT measure0.
Qed.

End negligible.

Notation "mu .-negligible" := (negligible mu) : type_scope.

Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom P)) : type_scope.

Definition sigma_subadditive (R : numFieldType) (T : Type)
  (mu : set T -> \bar R) := forall (A : (set T) ^nat),
  mu (\bigcup_n (A n)) <= \sum_(i <oo) mu (A i).

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : Type).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, 0 <= mu x ;
  _ : {homo mu : A B / A `<=` B >-> A <= B} ;
  _ : sigma_subadditive mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation outer_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation OuterMeasure fA := (Pack (Phant _) fA).
Notation "{ 'outer_measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'outer_measure'  fUV }") : ring_scope.
Notation "[ 'outer_measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'outer_measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'outer_measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'outer_measure'  'of'  f ]") : form_scope.
End Exports.

End OuterMeasure.
Include OuterMeasure.Exports.

Section outer_measure_lemmas.
Variables (R : numFieldType) (T : Type).
Variable mu : {outer_measure set T -> \bar R}.

Lemma outer_measure0 : mu set0 = 0.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_ge0 : forall x, 0 <= mu x.
Proof. by case: mu => ? []. Qed.

Lemma le_outer_measure : {homo mu : A B / A `<=` B >-> A <= B}.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_sigma_subadditive : sigma_subadditive mu.
Proof. by case: mu => ? []. Qed.

End outer_measure_lemmas.

Hint Extern 0 (_ set0 = 0) => solve [apply: outer_measure0] : core.
Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

Lemma le_outer_measureIC (R : realFieldType) T
  (mu : {outer_measure set T -> \bar R}) (A X : set T) :
  mu X <= mu (X `&` A) + mu (X `&` ~` A).
Proof.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have cvg_mu : (fun n => \sum_(i < n) mu (B i)) --> mu (B 0%N) + mu (B 1%N).
  rewrite -2!cvg_shiftS /=.
  rewrite [X in X --> _](_ : _ = (fun=> mu (B 0%N) + mu (B 1%N))); last first.
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
Grab Existential Variables. all: end_near. Qed.

Definition caratheodory_measurable (R : realType) (T : Type)
  (mu : {outer_measure set T -> \bar R}) (A : set T) := forall X,
  mu X = mu (X `&` A) + mu (X `&` ~` A).

Notation "mu .-measurable" := (caratheodory_measurable mu)
  (at level 2, format "mu .-measurable") : type_scope.

Lemma le_caratheodory_measurable (R : realType) T
  (mu : {outer_measure set T -> \bar R}) (A : set T) :
  (forall X, mu (X `&` A) + mu (X `&` ~` A) <= mu X) ->
  mu.-measurable A.
Proof.
move=> suf X; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: le_outer_measureIC | exact: suf].
Qed.

Section caratheodory_theorem_sigma_algebra.

Variables (R : realType) (T : Type) (mu : {outer_measure set T -> \bar R}).

Lemma outer_measure_bigcup_lim (A : (set T) ^nat) X :
  mu (X `&` \bigcup_k A k) <= \sum_(k <oo) mu (X `&` A k).
Proof.
apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
by apply/le_outer_measure; rewrite setI_bigcupr.
Qed.

Let M := mu.-measurable.

Lemma caratheodory_measurable_set0 : M set0.
Proof. by move=> X /=; rewrite setI0 outer_measure0 add0e setC0 setIT. Qed.

Lemma caratheodory_measurable_setC A : M A -> M (~` A).
Proof. by move=> MA X; rewrite setCK addeC -MA. Qed.

Lemma caratheodory_measurable_setU_le (X A B : set T) :
  mu.-measurable A -> mu.-measurable B ->
  mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <= mu X.
Proof.
move=> mA mB; pose Y := X `&` A `|` X `&` B `&` ~` A.
have /(lee_add2r (mu (X `&` ~` (A `|` B)))) :
    mu Y <= mu (X `&` A) + mu (X `&` B `&` ~` A).
  pose Z := bigcup2 (X `&` A) (X `&` B `&` ~` A).
  have -> : Y = \bigcup_k Z k.
    rewrite predeqE => t; split=> [[?|?]|[]]; [by exists O|by exists 1%N|].
    by move=> [_ ?|[_ ?|//]]; [left|right].
  rewrite (le_trans (outer_measure_sigma_subadditive mu Z)) //.
  suff : ((fun n => \sum_(i < n) mu (Z i)) -->
      mu (X `&` A) + mu (X `&` B `&` ~` A)).
    move/cvg_lim => /=; under [in X in X <= _]eq_fun do rewrite big_mkord.
    by move=> ->.
  rewrite -(cvg_shiftn 2) /=; set l := (X in _ --> X).
  rewrite [X in X --> _](_ : _ = cst l); first exact: cvg_cst.
  rewrite funeqE => i; rewrite addn2 2!big_ord_recl big1 ?adde0 //.
  by move=> ? _; exact: outer_measure0.
have /le_trans : mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <=
    mu Y + mu (X `&` ~` (A `|` B)).
  rewrite setIUr (_ : X `&` A `|` X `&` B = Y) //.
  rewrite /Y -[in LHS](setIT B) -(setUCr A) 2!setIUr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply subIset; right.
suff -> : mu (X `&` A) + mu (X `&` B `&` ~` A) +
    mu (X `&` (~` (A `|` B))) = mu X by exact.
by rewrite setCU setIA -(setIA X) setICA (setIC B) -addeA -mB -mA.
Qed.

Lemma caratheodory_measurable_setU A B : M A -> M B -> M (A `|` B).
Proof.
move=> mA mB X; apply/eqP; rewrite eq_le.
by rewrite le_outer_measureIC andTb caratheodory_measurable_setU_le.
Qed.

Lemma caratheodory_measurable_bigsetU (A : (set T) ^nat) : (forall n, M (A n)) ->
  forall n, M (\big[setU/set0]_(i < n) A i).
Proof.
move=> MA; elim=> [|n ih]; first by rewrite big_ord0; exact: caratheodory_measurable_set0.
by rewrite big_ord_recr; apply caratheodory_measurable_setU.
Qed.

Lemma caratheodory_measurable_setI A B : M A -> M B -> M (A `&` B).
Proof.
move=> mA mB; rewrite -(setCK A) -(setCK B) -setCU.
by apply/caratheodory_measurable_setC/caratheodory_measurable_setU;
  exact/caratheodory_measurable_setC.
Qed.

Lemma caratheodory_measurable_setD A B : M A -> M B -> M (A `\` B).
Proof.
move=> mA mB; rewrite setDE; apply caratheodory_measurable_setI => //.
exact: caratheodory_measurable_setC.
Qed.

Section additive_ext_lemmas.
Variable A B : set T.
Hypothesis (mA : M A) (mB : M B).

Let caratheodory_decomp X :
  mu X = mu (X `&` A `&` B) + mu (X `&` A `&` ~` B) +
         mu (X `&` ~` A `&` B) + mu (X `&` ~` A `&` ~` B).
Proof. by rewrite mA mB [X in _ + _ + X = _]mB addeA. Qed.

Let caratheorody_decompIU X : mu (X `&` (A `|` B)) =
  mu (X `&` A `&` B) + mu (X `&` ~` A `&` B) + mu (X `&` A `&` ~` B).
Proof.
rewrite caratheodory_decomp -!addeA; congr (mu _ + _).
  rewrite -!setIA; congr (_ `&` _).
  by rewrite setIC; apply/setIidPl; apply subIset; left; left.
rewrite addeA addeC [X in mu X + _](_ : _ = set0); last first.
  by rewrite -setIA -setCU -setIA setICr setI0.
rewrite outer_measure0 add0e addeC -!setIA; congr (mu (X `&` _) + mu (X `&` _)).
by rewrite setIC; apply/setIidPl; apply subIset; right; right.
by rewrite setIC; apply/setIidPl; apply subIset; left; left.
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

Lemma caratheodory_lim_lee (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall X,
  \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` \bigcup_k A k) <= mu X.
Proof.
move=> MA tA X.
set A' := \bigcup_k A k; set B := fun n => \big[setU/set0]_(k < n) (A k).
suff : forall n, \sum_(k < n) mu (X `&` A k) + mu (X `&` ~` A') <= mu X.
  move=> XA; rewrite (_ : lim _ = ereal_sup
      ((fun n => \sum_(k < n) mu (X `&` A k)) @` setT)); last first.
    under eq_fun do rewrite big_mkord.
    apply/cvg_lim => //; apply/nondecreasing_ereal_cvg.
    apply: (lee_sum_nneg_ord (fun n => mu (X `&` A n)) xpredT) => n _.
    exact: outer_measure_ge0.
  move XAx : (mu (X `&` ~` A')) => [x| |].
  - rewrite -lee_subr_addr //; apply ub_ereal_sup => /= _ [n _] <-.
    by rewrite NEFin lee_subr_addr // -XAx XA.
  - suff : mu X = +oo by move=> ->; rewrite lee_pinfty.
    apply/eqP; rewrite -lee_pinfty_eq -XAx le_outer_measure //.
    by apply subIset; left.
  - by rewrite addeC /= lee_ninfty.
move=> n.
apply (@le_trans _ _ (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` B n))).
  apply/lee_add2l/le_outer_measure; apply: setIS; apply: subsetC => t.
  by rewrite /B -bigcup_mkord => -[i ? ?]; exists i.
rewrite [in X in _ <= X](caratheodory_measurable_bigsetU MA n) lee_add2r //.
by rewrite caratheodory_additive.
Qed.

Lemma caratheodory_measurable_trivIset_bigcup (A : (set T) ^nat) :
  (forall n, M (A n)) -> trivIset setT A -> M (\bigcup_k (A k)).
Proof.
move=> MA tA; apply le_caratheodory_measurable => X /=.
have /(lee_add2r (mu (X `&` ~` \bigcup_k A k))) := outer_measure_bigcup_lim A X.
by move/le_trans; apply; exact: caratheodory_lim_lee.
Qed.

Lemma caratheodory_measurable_bigcup (A : (set T) ^nat) : (forall n, M (A n)) ->
  M (\bigcup_k (A k)).
Proof.
move=> MA; rewrite -eq_bigcup_seqD_bigsetU.
apply/caratheodory_measurable_trivIset_bigcup; last first.
  apply: (@trivIset_seqD _ (fun n => \big[setU/set0]_(i < n.+1) A i)).
  by move=> n m nm; exact/subsetPset/subset_bigsetU.
by case=> [|n /=]; [| apply/caratheodory_measurable_setD => //];
  exact/caratheodory_measurable_bigsetU.
Qed.

End caratheodory_theorem_sigma_algebra.

Definition caratheodory_type (R : realType) (T : Type)
  (mu : {outer_measure set T -> \bar R}) := T.

Section caratheodory_sigma_algebra.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> \bar R}).

HB.instance Definition caratheodory_mixin := @isMeasurable.Build
  (caratheodory_type mu) mu.-measurable
    (caratheodory_measurable_set0 mu)
    (@caratheodory_measurable_setC _ _ mu)
    (@caratheodory_measurable_bigcup _ _ mu).

End caratheodory_sigma_algebra.

Definition measure_is_complete (R : realType) (T : measurableType)
    (mu : set T -> \bar R) :=
  forall X, mu.-negligible X -> measurable X.

Definition measurable_fun (T U : measurableType) (D : set T) (f : T -> U) :=
  forall Y, measurable Y -> measurable ((f @^-1` Y) `&` D).

Section caratheodory_measure.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> \bar R}).
Local Notation U := (caratheodory_type mu).

Lemma caratheodory_measure0 : mu (set0 : set U) = 0.
Proof. exact: outer_measure0. Qed.

Lemma caratheodory_measure_ge0 (A : set U) : measurable A -> 0 <= mu A.
Proof. by move=> mx; apply outer_measure_ge0. Qed.

Lemma caratheodory_measure_sigma_additive : semi_sigma_additive (mu : set U -> _).
Proof.
move=> A mA tA mbigcupA; set B := \bigcup_k A k.
suff : forall X, mu X = \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` B).
  move/(_ B); rewrite setICr outer_measure0 adde0.
  rewrite (_ : (fun n => _) = fun n => \sum_(k < n) mu (A k)); last first.
    rewrite funeqE => n; rewrite big_mkord; apply eq_bigr => i _; congr (mu _).
    by rewrite setIC; apply/setIidPl => t Ait; exists i.
  move=> ->; have := fun n (_ : xpredT n) => outer_measure_ge0 mu (A n).
  move/(@is_cvg_ereal_nneg_series _ _) => /cvg_ex[l] hl.
  under eq_fun do rewrite -(big_mkord xpredT (mu \o A)).
  by move/(@cvg_lim _ (@ereal_hausdorff R)) : (hl) => ->.
move=> X.
have mB : mu.-measurable B := caratheodory_measurable_bigcup mA.
apply/eqP; rewrite eq_le (caratheodory_lim_lee mA tA X) andbT.
have /(lee_add2r (mu (X `&` ~` B))) := outer_measure_bigcup_lim mu A X.
by rewrite -le_caratheodory_measurable // => ?; rewrite -mB.
Qed.

Definition caratheodory_measure_mixin := Measure.Axioms caratheodory_measure0
  caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
Definition caratheodory_measure : {measure set U -> \bar R} :=
  Measure caratheodory_measure_mixin.

Lemma measure_is_complete_caratheodory : measure_is_complete caratheodory_measure.
Proof.
move=> B [A [mA muA0 BA]]; apply le_caratheodory_measurable => X.
suff -> : mu (X `&` B) = 0.
  by rewrite add0e le_outer_measure //; apply subIset; left.
have muB0 : mu B = 0.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  by apply: (le_trans (le_outer_measure mu BA)); rewrite -muA0.
apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
have : X `&` B `<=` B by apply subIset; right.
by move/(le_outer_measure mu); rewrite muB0 => ->.
Qed.

End caratheodory_measure.

(* TODO: move? *)
Lemma cvg_geometric_series_half (R : archiFieldType) (r : R) n :
  series (fun k => r / (2 ^ (k + n.+1))%:R : R^o) --> (r / 2 ^+ n : R^o).
Proof.
rewrite (_ : series _ = series (geometric (r / (2 ^ n.+1)%:R) 2^-1%R)); last first.
  rewrite funeqE => m; rewrite /series /=; apply eq_bigr => k _.
  by rewrite expnD natrM (mulrC (2 ^ k)%:R) invfM exprVn (natrX _ 2 k) mulrA.
apply: cvg_trans.
  apply: cvg_geometric_series.
  by rewrite ger0_norm // invr_lt1 // ?ltr1n // unitfE.
rewrite [X in (X - _)%R](splitr 1) div1r addrK.
by rewrite -mulrA -invfM expnSr natrM -mulrA divff// mulr1 natrX.
Qed.
Arguments cvg_geometric_series_half {R} _ _.

Lemma epsilon_trick (R : realType) (A : (\bar R)^nat) (e : {nonneg R})
    (P : pred nat) : (forall n, 0 <= A n) ->
  \sum_(i <oo | P i) (A i + (e%:nngnum / (2 ^ i.+1)%:R)%:E) <=
  \sum_(i <oo | P i) A i + e%:nngnum%:E.
Proof.
move=> A0; rewrite (@le_trans _ _ (lim (fun n => (\sum_(0 <= i < n | P i) A i) +
    \sum_(0 <= i < n) (e%:nngnum / (2 ^ i.+1)%:R)%:E))) //.
  rewrite ereal_pseriesD //; last by move=> n _; apply: divr_ge0.
  rewrite ereal_limD //.
  - rewrite lee_add2l //; apply: lee_lim => //.
    + by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
    + by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
    + by near=> n; apply: lee_sum_nneg_subset => // i _; apply divr_ge0.
  - exact: is_cvg_ereal_nneg_series.
  - by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
  - by apply: adde_def_nneg_series => // n _; apply: divr_ge0.
suff cvggeo : (fun n => \sum_(0 <= i < n) (e%:nngnum / (2 ^ i.+1)%:R)%:E) -->
    e%:nngnum%:E.
  rewrite ereal_limD //.
  - by rewrite lee_add2l // (cvg_lim _ cvggeo).
  - exact: is_cvg_ereal_nneg_series.
  - by apply: is_cvg_ereal_nneg_series => ?; rewrite lee_fin divr_ge0.
  - by rewrite (cvg_lim _ cvggeo) //= fin_num_adde_def.
rewrite (_ : (fun n => _) = EFin \o
    (fun n => \sum_(0 <= i < n) (e%:nngnum / (2 ^ (i + 1))%:R))%R); last first.
  rewrite funeqE => n /=; rewrite (@big_morph _ _ EFin 0 adde)//.
  by under [in RHS]eq_bigr do rewrite addn1.
apply: cvg_comp; last apply cvg_refl.
have := cvg_geometric_series_half e%:nngnum O.
by rewrite expr0 divr1; apply: cvg_trans.
Grab Existential Variables. all: end_near. Qed.

Section measurable_cover.
Variable T : ringOfSetsType.
Implicit Types (X : set T) (F : (set T)^nat).

Definition measurable_cover X := [set F : (set T)^nat |
  (forall i, measurable (F i)) /\ X `<=` \bigcup_k (F k)].

Lemma cover_measurable X F : measurable_cover X F -> forall k, measurable (F k).
Proof. by move=> + k; rewrite /measurable_cover => -[] /(_ k). Qed.

Lemma cover_subset X F : measurable_cover X F -> X `<=` \bigcup_k (F k).
Proof. by case. Qed.

End measurable_cover.

Section measure_extension.
Variables (R : realType) (T : ringOfSetsType) (mu : {measure set T -> \bar R}).

Definition mu_ext (X : set T) : \bar R :=
  ereal_inf [set \sum_(i <oo) mu (A i) | A in measurable_cover X].

Lemma le_mu_ext : {homo mu_ext : A B / A `<=` B >-> A <= B}.
Proof.
move=> A B AB; apply/le_ereal_inf => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_ge0 A : 0 <= mu_ext A.
Proof.
apply: lb_ereal_inf => x [B [mB AB] <-{x}]; rewrite ereal_lim_ge //=.
  by apply: is_cvg_ereal_nneg_series => // n _; exact: measure_ge0.
by near=> n; rewrite sume_ge0 // => i _; apply: measure_ge0.
Grab Existential Variables. all: end_near. Qed.

Lemma mu_ext0 : mu_ext set0 = 0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: mu_ext_ge0; exact: measurable0.
rewrite /mu_ext; apply ereal_inf_lb; exists (fun _ => set0).
  by split => // _; exact: measurable0.
by apply: (@lim_near_cst _ _ _ _ _ 0) => //; near=> n => /=; rewrite big1.
Grab Existential Variables. all: end_near. Qed.

Lemma measurable_uncurry (G : ((set T)^nat)^nat) (x : nat * nat) :
  measurable (G x.1 x.2) -> measurable (uncurry G x).
Proof. by case: x. Qed.

Lemma mu_ext_sigma_subadditive : sigma_subadditive mu_ext.
Proof.
move=> A; have [[i ioo]|] := pselect (exists i, mu_ext (A i) = +oo).
  rewrite (ereal_nneg_series_pinfty _ _ ioo)// ?lee_pinfty// => n _.
  exact: mu_ext_ge0.
rewrite -forallNE => Aoo.
suff add2e : forall e : {posnum R},
    mu_ext (\bigcup_n A n) <= \sum_(i <oo) mu_ext (A i) + e%:num%:E.
  apply lee_adde => e.
  by rewrite -(mul1r e%:num) -(@divff _ 2%:R)// -mulrAC -mulrA add2e.
move=> e; rewrite (le_trans _ (epsilon_trick _ _ _))//; last first.
  by move=> n; apply: mu_ext_ge0.
pose P n (B : (set T)^nat) := measurable_cover (A n) B /\
  \sum_(k <oo) mu (B k) <= mu_ext (A n) + (e%:num / (2 ^ n.+1)%:R)%:E.
have [G PG] : {G : ((set T)^nat)^nat & forall n, P n (G n)}.
  apply: (@choice _ _ P) => n; rewrite /P /mu_ext.
  set S := (X in ereal_inf X); move infS : (ereal_inf S) => iS.
  case: iS infS => [r Sr|Soo|Soo].
  - have en1 : (0 < e%:num / (2 ^ n.+1)%:R)%R.
      by rewrite divr_gt0 // ltr0n expn_gt0.
    have /(lb_ereal_inf_adherent (PosNum en1)) : ereal_inf S \is a fin_num.
      by rewrite Sr.
    move=> [x [[B [mB AnB muBx]] xS]].
    exists B; split => //; rewrite muBx -Sr; apply/ltW.
    by rewrite (lt_le_trans xS) // lee_add2l //= lee_fin ler_pmul.
  - by have := Aoo n; rewrite /mu_ext Soo.
  - suff : lbound S 0 by move/lb_ereal_inf; rewrite Soo.
    move=> /= _ [B [mB AnB] <-].
    by apply: ereal_nneg_series_lim_ge0 => ? _; exact: measure_ge0.
have muG_ge0 : forall x, 0 <= (mu \o uncurry G) x.
  by move=> x; apply/measure_ge0/measurable_uncurry/(PG x.1).1.1.
apply (@le_trans _ _ (\csum_(i in setT) (mu \o uncurry G) i)).
  rewrite /mu_ext; apply: ereal_inf_lb => /=.
  have [f [Tf fi]] : exists e, enumeration (@setT (nat * nat)) e /\ injective e.
    have /card_eq_sym/card_eqP[f [fI fT fS]] := countably_infinite_prod_nat.
    exists f; split; last by move=> ? ? /fI; apply; rewrite !inE.
    rewrite /enumeration eqEsubset; split=> // x _ /=.
    by have [n [_ ->]] := fS x I; exists n.
  exists (uncurry G \o f).
    split => [i|]; first exact/measurable_uncurry/(PG (f i).1).1.1.
    apply: (@subset_trans _  (\bigcup_n \bigcup_k G n k)) => [t [i _]|].
      by move=> /(cover_subset (PG i).1) -[j _ ?]; exists i => //; exists j.
    move=> t [i _ [j _ Bijt]].
    have [k fkij] : exists k, f k = (i, j).
      by have : setT (i, j) by []; rewrite Tf => -[k _ fkij]; exists k.
    by exists k => //=; rewrite fkij.
  rewrite -(@csum_image _ _ (mu \o uncurry G) _ xpredT) //; congr csum.
  by rewrite Tf predeqE=> -[a b]; split=> -[n _ <-]; exists n.
rewrite (_ : csum _ _ = \sum_(i <oo) \sum_(j <oo ) mu (G i j)); last first.
  pose J : nat -> set (nat * nat) := fun i => [set (i, j) | j in setT].
  rewrite (_ : setT = \bigcup_k J k); last first.
    by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b.
  rewrite csum_bigcup /=; last 2 first.
    - apply/trivIsetP => i j _ _ ij.
      rewrite predeqE => -[n m] /=; split => //= -[] [_] _ [<-{n} _].
      by move=> [m' _] [] /esym/eqP; rewrite (negbTE ij).
    - by move=> /= [n m]; apply/measure_ge0; exact: (cover_measurable (PG n).1).
  rewrite (_ : setT = id @` xpredT); last first.
    by rewrite image_id funeqE => x; rewrite trueE.
  rewrite csum_image //; last by move=> n _; apply: csum_ge0.
  apply: eq_ereal_pseries => /= j.
  pose x_j : nat -> nat * nat := fun y => (j, y).
  have [enux injx] : enumeration (J j) x_j /\ injective x_j.
    by split => [|x y [] //]; rewrite /enumeration predeqE=> -[? ?]; split.
  rewrite -(@csum_image R _ (mu \o uncurry G) x_j predT) //=; last first.
    by move=> x _; move: (muG_ge0 (j, x)).
  by congr csum; rewrite predeqE => -[a b]; split; move=> [i _ <-]; exists i.
apply lee_lim.
- apply: is_cvg_ereal_nneg_series => n _.
  by apply: ereal_nneg_series_lim_ge0 => m _; exact: (muG_ge0 (n, m)).
- by apply: is_cvg_ereal_nneg_series => n _; apply: adde_ge0 => //;
    [exact: mu_ext_ge0 | rewrite lee_fin // divr_ge0].
- by near=> n; apply: lee_sum => i _; exact: (PG i).2.
Grab Existential Variables. all: end_near. Qed.

End measure_extension.

Canonical outer_measure_of_measure (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> \bar R}) : {outer_measure set T -> \bar R} :=
    OuterMeasure (OuterMeasure.Axioms (mu_ext0 mu) (mu_ext_ge0 mu)
      (le_mu_ext mu) (mu_ext_sigma_subadditive mu)).
