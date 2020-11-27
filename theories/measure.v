(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum finmap.
Require Import boolp classical_sets reals ereal posnum topology normedtype.
Require Import sequences.
From HB Require Import structures.

(******************************************************************************)
(*                            Measure Theory                                  *)
(*                                                                            *)
(* WIP.                                                                       *)
(*                                                                            *)
(* semiRingOfSetsType == the type of semirings of sets                        *)
(* ringOfSetsType == the type of rings of sets                                *)
(* measurableType == the type of sigma-algebras                               *)
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
(* Theorems: Boole_inequality, generalized_Boole_inequality                   *)
(*                                                                            *)
(* mu.-negligible A == A is mu negligible                                     *)
(* {ae mu, P} == P holds almost everywhere for the measure mu                 *)
(*                                                                            *)
(* {outer_measure set T -> {ereal R}} == type of an outer measure over sets   *)
(*                                 of elements o ftype T where R is expected  *)
(*                                 to be a numFieldType                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Reserved Notation "{ 'ae' m , P }" (at level 0, format "{ 'ae'  m ,  P }").

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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

HB.mixin Record Measurable_from_ringOfSets T of RingOfSets T := {
  measurableT : measurable (@setT T) ;
  measurable_bigcup : forall U : (set T)^nat, (forall i, measurable (U i)) ->
    measurable (\bigcup_i (U i))
}.

HB.structure Definition Measurable := {T of Measurable_from_ringOfSets T &}.

Notation measurableType := Measurable.type.

HB.factory Record isRingOfSets T := {
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableU : forall A B, measurable A -> measurable B -> measurable (A `|` B) ;
  measurableC : forall A, measurable A -> measurable (~` A)
}.

HB.builders Context T of isRingOfSets T.

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

Definition T_isSemiRingOfSets : isSemiRingOfSets T :=
  @isSemiRingOfSets.Build T measurable diff_fsets
    measurable0
    semiRingOfSets_measurableI
    semiRingOfSets_measurableD
    semiRingOfSets_diff_fsetsE
    semiRingOfSets_diff_fsets_disjoint.

HB.instance T T_isSemiRingOfSets.

Definition T_isRingOfSets : RingOfSets_from_semiRingOfSets T :=
  RingOfSets_from_semiRingOfSets.Build T measurableU.

HB.instance T T_isRingOfSets.

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

Program Definition T_isRingOfSets : isRingOfSets T :=
  @isRingOfSets.Build T measurable measurable0 _ _.
Next Obligation.
move=> A B mA mB; rewrite -bigcup2E.
by apply measurable_bigcup => -[//|[//|i]]; exact: measurable0.
Qed.
Next Obligation. by move=> A mA; apply: measurableC. Qed.

HB.instance T T_isRingOfSets.

Program Definition T_isMeasurable : Measurable_from_ringOfSets T :=
  @Measurable_from_ringOfSets.Build _ _ measurable_bigcup.
Next Obligation.
by rewrite -setC0; apply: measurableC; apply: measurable0.
Qed.

HB.instance T T_isMeasurable.

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

Section measurable_lemmas.
Variables T : measurableType.
Implicit Types A B : set T.

Lemma measurableC A : measurable A -> measurable (~` A).
Proof.
by move=> mA; rewrite -setTD; apply measurableD => //; exact: measurableT.
Qed.

Lemma measurableT : measurable (setT : set T).
Proof. by rewrite -setC0; apply measurableC; exact: measurable0. Qed.

Lemma measurable_bigcap (U : (set T)^nat) :
  (forall i, measurable (U i)) -> measurable (\bigcap_i (U i)).
Proof.
move=> mU; rewrite bigcapCU; apply/measurableC/measurable_bigcup => i.
exact: measurableC.
Qed.

End measurable_lemmas.

Section semi_additivity.
Variables (R : numFieldType) (T : semiRingOfSetsType) (mu : set T -> {ereal R}).

Definition semi_additive2 := forall A B, measurable A -> measurable B ->
  measurable (A `|` B) ->
  A `&` B = set0 -> mu (A `|` B) = (mu A + mu B)%E.

Definition semi_additive :=
  forall A, (forall i, measurable (A i)) -> trivIset A ->
  (forall n, measurable (\big[setU/set0]_(i < n) A i)) ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = (\sum_(i < n) mu (A i))%E.

Definition semi_sigma_additive :=
  forall A, (forall i, measurable (A i)) -> trivIset A ->
  measurable (\bigcup_n A n) ->
  (fun n => (\sum_(i < n) mu (A i))%E) --> mu (\bigcup_n A n).

Definition additive2 := forall A B, measurable A -> measurable B ->
  A `&` B = set0 -> mu (A `|` B) = (mu A + mu B)%E.

Definition additive :=
  forall A, (forall i, measurable (A i)) -> trivIset A ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = (\sum_(i < n) mu (A i))%E.

Definition sigma_additive :=
  forall A, (forall i, measurable (A i)) -> trivIset A ->
  (fun n => (\sum_(i < n) mu (A i))%E) --> mu (\bigcup_n A n).

Lemma semi_additive2P : mu set0 = 0%:E -> semi_additive <-> semi_additive2.
Proof.
move=> mu0; split => [amx A B mA mB mAB AB|a2mx A mA ATI mbigA n].
  set C := bigcup2 A B.
  have tC : trivIset C by move=> [|[|i]] [|[|j]]; rewrite ?set0I ?setI0// setIC.
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
   exact: mbigA.
   have := mbigA n.+1.
   by rewrite big_ord_recr.
   rewrite big_distrl /= big1 // => i _; apply: ATI; rewrite lt_eqF //.
   exact: ltn_ord.
by rewrite IHn // [in RHS]big_ord_recr.
Qed.

End semi_additivity.

Section additivity.
Variables (R : numFieldType) (T : ringOfSetsType) (mu : set T -> {ereal R}).

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

Lemma additive2P : mu set0 = 0%:E -> additive mu <-> additive2 mu.
Proof. by rewrite -semi_additive2E -semi_additiveE; exact/semi_additive2P. Qed.

End additivity.

Lemma semi_sigma_additive_is_additive
  (R : realFieldType (*TODO: numFieldType if possible?*))
  (X : semiRingOfSetsType) (mu : set X -> {ereal R}) :
  mu set0 = 0%:E -> semi_sigma_additive mu -> semi_additive mu.
Proof.
move=> mu0 samu; apply/semi_additive2P => // A B mA mB mAB AB_eq0.
pose C := bigcup2 A B.
have tC : trivIset C by move=> [|[|i]] [|[|j]]; rewrite ?setI0 ?set0I// setIC.
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
  (R : numFieldType) (X : measurableType) (mu : set X -> {ereal R}) :
  semi_sigma_additive mu = sigma_additive mu.
Proof.
rewrite propeqE; split=> [amu A mA tA|amu A mA tA mbigcupA]; last exact: amu.
by apply: amu => //; exact: measurable_bigcup.
Qed.

Lemma sigma_additive_is_additive
  (R : realFieldType) (X : measurableType) (mu : set X -> {ereal R}) :
  mu set0 = 0%:E -> sigma_additive mu -> additive mu.
Proof.
move=> mu0; rewrite -semi_sigma_additiveE -semi_additiveE.
exact: semi_sigma_additive_is_additive.
Qed.

Module AdditiveMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> {ereal R}) := Axioms {
  _ : mu set0 = 0%:E ;
  _ : forall x, measurable x -> (0%:E <= mu x)%E ;
  _ : semi_additive2 mu }.

Structure map (phUV : phant (set T -> {ereal R})) :=
  Pack {apply : set T -> {ereal R} ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> {ereal R})) (f g : set T -> {ereal R}).
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
  (mu : {additive_measure set T -> {ereal R}}).

Lemma measure0 : mu set0 = 0%:E.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure0.

Lemma measure_ge0 : forall x, measurable x -> (0%:E <= mu x)%E.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_ge0.

Lemma measure_semi_additive2 : semi_additive2 mu.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_semi_additive2.

Lemma measure_semi_additive : semi_additive mu.
Proof. exact/semi_additive2P. Qed.

End additive_measure_on_semiring_of_sets.

Hint Resolve measure0 measure_ge0 measure_semi_additive2
  measure_semi_additive : core.

Section additive_measure_on_ring_of_sets.
Variables (R : realFieldType) (T : ringOfSetsType)
  (mu : {additive_measure set T -> {ereal R}}).

Lemma measure_additive2 : additive2 mu.
Proof. by rewrite -semi_additive2E. Qed.

Lemma measure_additive : additive mu.
Proof. by rewrite -semi_additiveE. Qed.

End additive_measure_on_ring_of_sets.

Hint Resolve measure_additive2 measure_additive : core.

Module Measure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> {ereal R}) := Measure {
  _ : mu set0 = 0%:E ;
  _ : forall x, measurable x -> (0%:E <= mu x)%E ;
  _ : semi_sigma_additive mu }.

Structure map (phUV : phant (set T -> {ereal R})) :=
  Pack {apply : set T -> {ereal R} ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> {ereal R})) (f g : set T -> {ereal R}).
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
Variable mu : {measure set T -> {ereal R}}.

Lemma measure_semi_sigma_additive : semi_sigma_additive mu.
Proof. by case: mu => ? []. Qed.

End measure_lemmas.

Section measure_lemmas.
Variables (R : numFieldType) (T : measurableType).
Variable mu : {measure set T -> {ereal R}}.

Lemma measure_sigma_additive : sigma_additive mu.
Proof.
by rewrite -semi_sigma_additiveE //; apply: measure_semi_sigma_additive.
Qed.

End measure_lemmas.

Hint Extern 0 (_ set0 = 0%:E) => solve [apply: measure0] : core.
Hint Extern 0 (sigma_additive _) =>
  solve [apply: measure_sigma_additive] : core.

Section measure_is_additive_measure.
Variables (R : realFieldType) (T : semiRingOfSetsType)
  (mu : {measure set T -> {ereal R}}).

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
  (mu : {additive_measure set T -> {ereal R}}) :
  {in [set x | measurable x] &, {homo mu : A B / A `<=` B >-> (A <= B)%E}}.
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

Section trivIfy.
Variables (T : Type).

Definition B_of (A : (set T) ^nat) :=
  fun n => if n isn't n'.+1 then A O else A n `\` A n'.

Lemma trivIset_B_of (A : (set T) ^nat) :
  {homo A : n m / (n <= m)%nat >-> n `<=` m} -> trivIset (B_of A).
Proof.
move=> ndA i j; wlog : i j / (i < j)%N.
  move=> h; rewrite neq_ltn => /orP[|] ?; by
    [rewrite h // ltn_eqF|rewrite setIC h // ltn_eqF].
move=> ij _; move: j i ij; case => // j [_ /=|n].
  rewrite funeqE => x; rewrite propeqE; split => // -[A0 [Aj1 Aj]].
  exact/Aj/(ndA O).
rewrite ltnS => nj /=; rewrite funeqE => x; rewrite propeqE; split => //.
by move=> -[[An1 An] [Aj1 Aj]]; apply/Aj/(ndA n.+1).
Qed.

Lemma UB_of (A : (set T) ^nat) : {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  forall n, A n.+1 = A n `|` B_of A n.+1.
Proof.
move=> ndA n; rewrite /B_of funeqE => x; rewrite propeqE; split.
by move=> ?; have [?|?] := pselect (A n x); [left | right].
by move=> -[|[]//]; apply: ndA.
Qed.

Lemma bigUB_of (A : (set T) ^nat) n :
  \big[setU/set0]_(i < n.+1) A i = \big[setU/set0]_(i < n.+1) B_of A i.
Proof.
elim: n => [|n ih]; first by rewrite !big_ord_recl !big_ord0.
rewrite big_ord_recr [in RHS]big_ord_recr /= predeqE => x; split=> [[Ax|An1x]|].
    by rewrite -ih; left.
  rewrite -ih.
  have [Anx|Anx] := pselect (A n x); last by right.
  by left; rewrite big_ord_recr /=; right.
move=> [summyB|[An1x NAnx]]; by [rewrite ih; left | right].
Qed.

Lemma eq_bigsetUB_of (A : (set T) ^nat) n :
  {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  A n = \big[setU/set0]_(i < n.+1) B_of A i.
Proof.
move=> ndA; elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
- by move=> ?; rewrite big_ord_recl big_ord0; left.
- by rewrite big_ord_recl big_ord0 setU0.
- rewrite (UB_of ndA) => -[|/=].
  by rewrite big_ord_recr /= -ih => Anx; left.
  by move=> -[An1x Anx]; rewrite big_ord_recr /=; right.
- rewrite big_ord_recr /= -ih => -[|[]//]; exact: ndA.
Qed.

Lemma eq_bigcupB_of (A : (set T) ^nat) :
  {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  \bigcup_n A n = \bigcup_n (B_of A) n.
Proof.
move=> ndA; rewrite funeqE => x; rewrite propeqE; split.
  move=> -[n _]; rewrite (eq_bigsetUB_of _ ndA) bigcup_ord => -[m mn ?].
  by exists m.
move=> -[m _] myBAmx; exists m => //; rewrite (eq_bigsetUB_of _ ndA) bigcup_ord.
by exists m.
Qed.

End trivIfy.

Section boole_inequality.
Variables (R : realFieldType) (T : ringOfSetsType).
Variables (mu : {measure set T -> {ereal R}}).

(* 401,p.43 measure is continuous from below *)
Lemma cvg_mu_inc (A : (set T) ^nat) :
  (forall i, measurable (A i)) ->
  (measurable (\bigcup_n A n)) ->
  {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  mu \o A --> mu (\bigcup_n A n).
Proof.
move=> mA mbigcupA ndA.
have Binter : trivIset (B_of A) := trivIset_B_of ndA.
have ABE : forall n, A n.+1 = A n `|` B_of A n.+1 := UB_of ndA.
have AE n : A n = \big[setU/set0]_(i < n.+1) (B_of A) i := eq_bigsetUB_of n ndA.
have -> : \bigcup_n A n = \bigcup_n (B_of A) n := eq_bigcupB_of ndA.
have mB : forall i, measurable (B_of A i).
  by elim=> [|i ih] //=; apply: measurableD.
apply: cvg_trans (measure_semi_sigma_additive mB Binter _); last first.
  by rewrite -eq_bigcupB_of.
apply: (@cvg_trans _ [filter of (fun n => (\sum_(i < n.+1) mu (B_of A i))%E)]); last first.
  by move=> S [n _] nS; exists n => // m nm; apply/(nS m.+1)/(leq_trans nm).
rewrite (_ : (fun n => \sum_(i < n.+1) mu (B_of A i))%E = mu \o A) //.
rewrite funeqE => n; rewrite -measure_semi_additive // -?AE //.
case=> [|k].
  by rewrite big_ord0; exact: measurable0.
by rewrite -AE.
Qed.

Theorem Boole_inequality (A : (set T) ^nat) : (forall i, measurable (A i)) ->
  forall n, (mu (\big[setU/set0]_(i < n) A i) <= \sum_(i < n) mu (A i))%E.
Proof.
move=> mA; elim => [|n ih]; first by rewrite !big_ord0 measure0.
set B := \big[setU/set0]_(i < n) A i.
set C := \big[setU/set0]_(i < n.+1) A i.
have -> : C = B `|` (A n `\` B).
  rewrite predeqE => x; split => [|].
    rewrite /C big_ord_recr /= => -[sumA|]; first by left.
    by have [?|?] := pselect (B x); [left|right].
  move=> -[|[An1x _]].
    by rewrite /C big_ord_recr; left.
  by rewrite /C big_ord_recr; right.
have ? : measurable B by apply bigsetU_measurable.
rewrite measure_additive2 //; last 2 first.
  by apply measurableD.
  rewrite setIC -setIA (_ : ~` _ `&` _ = set0) ?setI0 //.
  by rewrite funeqE => x; rewrite propeqE; split => // -[].
rewrite (@le_trans _ _ (mu B + mu (A n))%E) // ?lee_add2l //.
  rewrite le_measure //; last 2 first.
    by rewrite inE; apply mA.
    by apply subIset; left.
    by rewrite inE; apply measurableD.
by rewrite big_ord_recr /= lee_add2r.
Qed.

End boole_inequality.
Notation le_mu_bigsetU := Boole_inequality.

Section generalized_boole_inequality.
Variables (R : realType) (T : ringOfSetsType).
Variable (mu : {measure set T -> {ereal R}}).

(* 404,p.44 measure satisfies generalized Boole's inequality *)
Theorem generalized_Boole_inequality (A : (set T) ^nat) :
  (forall i : nat, measurable (A i)) ->
  (measurable (\bigcup_n A n)) ->
  (mu (\bigcup_n A n) <= lim (fun n => \sum_(i < n) mu (A i)))%E.
Proof.
move=> mA mbigcupA; set B := fun n => \big[setU/set0]_(i < n.+1) (A i).
have AB : \bigcup_k A k = \bigcup_n B n.
  rewrite predeqE => x; split.
  by move=> -[k _ Akx]; exists k => //; rewrite /B big_ord_recr /=; right.
  move=> -[m _].
  rewrite /B big_ord_recr /= => -[].
  by rewrite bigcup_ord => -[k km Akx]; exists k.
  by move=> Amx; exists m.
have ndB : {homo B : n m / (n <= m)%N >-> n `<=` m}.
  by move=> n m nm; apply subset_bigsetU.
have mB : forall i, measurable (B i) by move=> i; exact: bigsetU_measurable.
rewrite AB.
move/(@cvg_mu_inc _ _ mu _ mB _) : ndB => /(_ _)/cvg_lim <- //; last first.
  by rewrite -AB.
have -> : lim (mu \o B) = ereal_sup ((mu \o B) @` setT).
  suff : nondecreasing_seq (mu \o B).
    by move/nondecreasing_seq_ereal_cvg; apply/cvg_lim.
  move=> n m nm; apply: le_measure => //; try by rewrite inE; apply mB.
  exact: subset_bigsetU.
have BA : forall m, (mu (B m) <= lim (fun n : nat => \sum_(i < n) mu (A i)))%E.
  move=> m; rewrite (le_trans (le_mu_bigsetU mu mA m.+1)) // -/(B m).
  by apply: (@ereal_nneg_series_lim_ge _ (mu \o A)) => n; exact: measure_ge0.
by apply ub_ereal_sup => /= x [n _ <-{x}]; apply BA.
Qed.

End generalized_boole_inequality.
Notation le_mu_bigcup := generalized_Boole_inequality.

Section negligible.
Variables (R : realFieldType) (T : ringOfSetsType).

Definition negligible (mu : set T -> {ereal R}) (N : set T) :=
  exists A : set T, [/\ measurable A, mu A = 0%:E & N `<=` A].

Local Notation "mu .-negligible" := (negligible mu)
  (at level 2, format "mu .-negligible").

Lemma negligibleP (mu : {measure _ -> _}) A :
  measurable A -> mu.-negligible A <-> mu A = 0%:E.
Proof.
move=> mA; split => [[B [mB mB0 AB]]|mA0]; last by exists A; split.
apply/eqP; rewrite eq_le measure_ge0 // andbT -mB0.
by apply: (le_measure (measure_additive_measure mu)) => //; rewrite in_setE.
Qed.

Lemma negligible_set0 (mu : {measure _ -> _}) : mu.-negligible set0.
Proof. by apply/negligibleP => //; exact: measurable0. Qed.

Definition almost_everywhere (mu : set T -> {ereal R})
    (P : T -> Prop) & (phantom Prop (forall x, P x)) :=
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

Notation "mu .-negligible" := (negligible mu)
  (at level 2, format "mu .-negligible").

Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom (forall x, P x)))
  (at level 0, format "{ 'ae'  m ,  P }") : type_scope.

Definition sigma_subadditive (R : numFieldType) (T : Type)
  (mu : set T -> {ereal R}) := forall (A : (set T) ^nat),
  (mu (\bigcup_n (A n)) <= lim (fun n => \sum_(i < n) mu (A i)))%E.

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : Type).
Record axioms (mu : set T -> {ereal R}) := OuterMeasure {
  _ : mu set0 = 0%:E ;
  _ : forall x, (0%:E <= mu x)%E ;
  _ : {homo mu : A B / A `<=` B >-> (A <= B)%E} ;
  _ : sigma_subadditive mu}.

Structure map (phUV : phant (set T -> {ereal R})) :=
  Pack {apply : set T -> {ereal R} ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> {ereal R})) (f g : set T -> {ereal R}).
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
Variable mu : {outer_measure set T -> {ereal R}}.

Lemma outer_measure0 : mu set0 = 0%:E.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_ge0 : forall x, (0%:E <= mu x)%E.
Proof. by case: mu => ? []. Qed.

Lemma le_outer_measure : {homo mu : A B / A `<=` B >-> (A <= B)%E}.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_sigma_subadditive : sigma_subadditive mu.
Proof. by case: mu => ? []. Qed.

End outer_measure_lemmas.

Hint Extern 0 (_ set0 = 0%:E) => solve [apply: outer_measure0] : core.
Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

Lemma le_outer_measureIC (R : realFieldType) T
  (mu : {outer_measure set T -> {ereal R}}) (A X : set T) :
  (mu X <= mu (X `&` A) + mu (X `&` ~` A))%E.
Proof.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have cvg_mu :
    (fun n => (\sum_(i < n) mu (B i))%E) --> (mu (B 0%N) + mu (B 1%N))%E.
  rewrite -2!cvg_shiftS /=.
  rewrite [X in X --> _](_ : _ = (fun=> mu (B 0%N) + mu (B 1%N)))%E; last first.
    rewrite funeqE => i; rewrite 2!big_ord_recl /= big1 ?adde0 // => j _.
    by rewrite /B /bigcup2 /=.
  exact: cvg_cst.
have := outer_measure_sigma_subadditive mu B.
suff : \bigcup_n B n = X.
  by move=> -> /le_trans; apply; rewrite (cvg_lim _ cvg_mu).
transitivity (\big[setU/set0]_(i < 2) B i).
  rewrite (bigcup_recl 2) // bigcup_ord [X in _ `|` X](_ : _ = set0) ?setU0 //.
  by rewrite predeqE => t; split => // -[].
by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIUr setUCr setIT.
Grab Existential Variables. all: end_near. Qed.
