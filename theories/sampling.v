(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype sequences.
From mathcomp Require Import realfun convex.
From mathcomp Require Import derive esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.
From mathcomp Require Import independence.

Reserved Notation "' P [ A | B ]".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section independent_events.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma sub_independent_events (I : choiceType) (A B : set I) (E : I -> set T) :
  A `<=` B -> independent_events P B E -> independent_events P A E.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Definition kwise_independent (I : choiceType) (A : set I) (E : I -> set T) k :=
  (forall i, A i -> measurable (E i)) /\
  forall B : {fset I}, [set` B] `<=` A -> (#|` B | <= k)%nat ->
    P (\bigcap_(i in [set` B]) E i) = \prod_(i <- B) P (E i).

Lemma sub_kwise_independent (I : choiceType) (A B : set I) (E : I -> set T) k :
  A `<=` B -> kwise_independent B E k -> kwise_independent A E k.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Lemma mutual_indep_is_kwise_indep (I : choiceType) (A : set I) (E : I -> set T) k :
  independent_events P A E -> kwise_independent A E k.
Proof.
rewrite /independent_events /kwise_independent.
move=> [mE miE]; split=> // B BleA _.
exact: miE.
Qed.

Lemma nwise_indep_is_mutual_indep (I : choiceType) (A : {fset I}) (E : I -> set T) n :
  #|` A | = n -> kwise_independent [set` A] E n -> independent_events P [set` A] E.
Proof.
rewrite /independent_events /kwise_independent.
move=> nA [mE miE]; split=> // B BleA.
apply: miE => //; rewrite -nA fsubset_leq_card//.
by apply/fsubsetP => x xB; exact: (BleA x).
Qed.

Lemma mutually_independent_weak (I : choiceType) (E : I -> set T) (B : set I) :
  (forall b, ~ B b -> E b = setT) ->
  independent_events P [set: I] E <->
  independent_events P B E.
Proof.
move=> BE; split; first exact: sub_independent_events.
move=> [mE h]; split=> [i _|C _].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last first.
  rewrite -CBD; exact: subIsetr.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Lemma kwise_independent_weak (I : choiceType) (E : I -> set T) (B : set I) k :
  (forall b, ~ B b -> E b = setT) ->
  kwise_independent [set: I] E k <->
  kwise_independent B E k.
Proof.
move=> BE; split; first exact: sub_kwise_independent.
move=> [mE h]; split=> [i _|C _ Ck].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last 2 first.
  - rewrite -CBD; exact: subIsetr.
  - rewrite (leq_trans _ Ck)// fsubset_leq_card// -(set_fsetK D) -(set_fsetK C).
    by rewrite -fset_set_sub// -CBD; exact: subIsetl.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Lemma kwise_independent_weak01 E1 E2 :
  kwise_independent [set: nat] (bigcap2 E1 E2) 2%N <->
  kwise_independent [set 0%N; 1%N] (bigcap2 E1 E2) 2%N.
Proof.
apply: kwise_independent_weak.
by move=> n /= /not_orP[/eqP /negbTE -> /eqP /negbTE ->].
Qed.

Lemma independent_events_weak' (I : choiceType) (E : I -> set T) (B : set I) :
  (forall b, ~ B b -> E b = setT) ->
  independent_events P [set: I] E <->
  independent_events P B E.
Proof.
move=> BE; split; first exact: sub_independent_events.
move=> [mE h]; split=> [i _|C CI].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last first.
  - rewrite -CBD; exact: subIsetr.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Definition pairwise_independent E1 E2 :=
  kwise_independent [set 0; 1]%N (bigcap2 E1 E2) 2.

Lemma pairwise_independentM_old (E1 E2 : set T) :
  pairwise_independent E1 E2 <->
  [/\ d.-measurable E1, d.-measurable E2 & P (E1 `&` E2) = P E1 * P E2].
Proof.
split.
- move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
  rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => ->; last 2 first.
  + by rewrite set_fsetU !set_fset1; exact: subset_refl.
  + rewrite cardfs2//.
  split => //.
  + by apply: (mE1E2 0%N) => /=; left.
  + by apply: (mE1E2 1%N) => /=; right.
- move=> [mE1 mE2 E1E2M].
  split => //=.
  + by move=> [| [| [|]]]//=.
  + move=> B _; have [B0|B0] := boolP (0%N \in B); last first.
      have [B1|B1] := boolP (1%N \in B); last first.
        rewrite big1_fset; last first.
          move=> k kB _; rewrite /bigcap2.
          move: kB B0; case: ifPn => [/eqP -> ->//|k0 kB B0].
          move: kB B1; case: ifPn => [/eqP -> ->//|_ _ _].
          by rewrite probability_setT.
        rewrite bigcapT ?probability_setT// => k/= kB.
        move: kB B0 B1; case: ifPn => [/eqP -> ->//|k0].
        by case: ifPn => [/eqP -> ->|].
      rewrite (bigcap_setD1 1%N _ [set` B])//=.
      rewrite bigcapT ?setIT; last first.
        move=> k [/= kB /eqP /negbTE ->].
        by move: kB B0; case: ifPn => [/eqP -> ->|].
      rewrite (big_fsetD1 1%N)//= big1_fset ?mule1// => k.
      rewrite !inE => /andP[/negbTE -> kB] _.
      move: kB B0; case: ifPn => [/eqP -> ->//|k0 kB B0].
      by rewrite probability_setT.
    rewrite (bigcap_setD1 0%N _ [set` B])//.
    have [B1|B1] := boolP (1%N \in B); last first.
      rewrite bigcapT ?setIT; last first.
        move=> k [/= kB /eqP /negbTE ->].
        by move: kB B1; case: ifPn => [/eqP -> ->|].
      rewrite (big_fsetD1 0%N)//= big1_fset ?mule1// => k.
      rewrite !inE => /andP[/negbTE -> kB] _.
      move: kB B1; case: ifPn => [/eqP -> ->//|k1 kB B1].
      by rewrite probability_setT.
    rewrite (bigcap_setD1 1%N _ ([set` B] `\ 0%N))// bigcapT ?setIT; last first.
      by move=> n/= [[nB]/eqP/negbTE -> /eqP/negbTE ->].
    rewrite E1E2M (big_fsetD1 0%N)//= (big_fsetD1 1%N)/=; last by rewrite !inE B1.
    rewrite big1_fset ?mule1//= => k.
    rewrite !inE => -/and3P[/negbTE -> /negbTE -> kB] _;
    by rewrite probability_setT.
Qed.

Lemma pairwise_independentM (E1 E2 : set T) :
  pairwise_independent E1 E2 <->
  [/\ d.-measurable E1, d.-measurable E2 & P (E1 `&` E2) = P E1 * P E2].
Proof.
split.
- move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
  rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => ->; last 2 first.
  + by rewrite set_fsetU !set_fset1; exact: subset_refl.
  + by rewrite cardfs2.
  split => //.
  + by apply: (mE1E2 0%N) => /=; left.
  + by apply: (mE1E2 1%N) => /=; right.
- move=> [mE1 mE2 E1E2M].
  rewrite /pairwise_independent.
  split.
  + by move=> [| [| [|]]]//=.
  + move=> B B01 B2.
    have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
    * rewrite B_set0.
      move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
      by rewrite big_nil bigcap_set0 probability_setT.
    * rewrite B_set0 bigcap_set1 /=.
      by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
    * rewrite B_set1 bigcap_set1 /=.
      by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
    * rewrite B_set01 bigcap_setU1 bigcap_set1/=.
      rewrite fsbig_seq//= B_set01.
      rewrite fsbigU//=; last first.
        by move=> n [/= ->].
      by rewrite !fsbig_set1//=.
Qed.

Lemma pairwise_independent_setC (E1 E2 : set T) :
  pairwise_independent E1 E2 -> pairwise_independent E1 (~` E2).
Proof.
rewrite/pairwise_independent.
move/pairwise_independentM=> [mE1 mE2 h].
apply/pairwise_independentM; split=> //.
- exact: measurableC.
- rewrite -setDE measureD//; last first.
    exact: (le_lt_trans (probability_le1 P mE1) (ltry _)).
  rewrite probability_setC// muleBr// ?mule1 -?h//.
  by rewrite fin_num_measure.
Qed.

Lemma pairwise_independentC (E1 E2 : set T) :
  pairwise_independent E1 E2 -> pairwise_independent E2 E1.
Proof.
rewrite/pairwise_independent/kwise_independent; move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => h.
split.
- case=> [_|[_|]]//=.
  + by apply: (mE1E2 1%N) => /=; right.
  + by apply: (mE1E2 0%N) => /=; left.
- move=> B B01 B2.
  have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
  + rewrite B_set0.
    move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
    by rewrite big_nil bigcap_set0 probability_setT.
  + rewrite B_set0 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
  + rewrite B_set1 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
  + rewrite B_set01 bigcap_setU1 bigcap_set1/=.
    rewrite fsbig_seq//= B_set01.
    rewrite fsbigU//=; last first.
    by move=> n [/= ->].
    rewrite !fsbig_set1//= muleC setIC.
    apply: h.
    * by rewrite set_fsetU !set_fset1; exact: subset_refl.
    * by rewrite cardfs2.
Qed.
(* ale: maybe interesting is thm 8.3 and exercise 8.6 from shoup/ntb at this point *)

End independent_events.

Section conditional_probability.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Definition conditional_probability (P : probability T R) E1 E2 := (fine (P (E1 `&` E2)) / fine (P E2))%:E.
Local Notation "' P [ E1 | E2 ]" := (conditional_probability P E1 E2).

Lemma conditional_independence (P : probability T R) E1 E2 :
  P E2 != 0 -> pairwise_independent P E1 E2 -> 'P [ E1 | E2 ] = P E1.
Proof.
move=> PE2ne0 iE12.
have /= mE1 := (iE12.1 0%N).
have /= mE2 := (iE12.1 1%N).
rewrite/conditional_probability.
have [_ _ ->] := (pairwise_independentM _ _ _).1 iE12.
rewrite fineM ?fin_num_measure//; [|apply: mE1; left=>//|apply: mE2; right=>//].
rewrite -mulrA mulfV ?mulr1 ?fineK// ?fin_num_measure//; first by apply: mE1; left.
by rewrite fine_eq0// fin_num_measure//; apply: mE2; right.
Qed.

(* TODO (klenke thm 8.4): if P B > 0 then 'P[.|B] is a probability measure *)

Lemma conditional_independent_is_pairwise_independent (P : probability T R) E1 E2 :
  d.-measurable E1 -> d.-measurable E2 ->
  P E2 != 0 ->
    'P[E1 | E2] = P E1 -> pairwise_independent P E1 E2.
Proof.
rewrite /conditional_probability/pairwise_independent=> mE1 mE2 pE20 pE1E2.
split.
- by case=> [|[|]]//=.
- move=> B B01 B2; have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
  + rewrite B_set0.
    move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
    by rewrite big_nil bigcap_set0 probability_setT.
  + rewrite B_set0 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
  + rewrite B_set1 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
  + rewrite B_set01 bigcap_setU1 bigcap_set1/=.
    rewrite fsbig_seq//= B_set01.
    rewrite fsbigU//=; last first.
    by move=> n [/= ->].
    rewrite !fsbig_set1//= -pE1E2 -{2}(@fineK _ (P E2)).
    rewrite -EFinM -mulrA mulVf ?mulr1 ?fine_eq0// ?fineK//.
    all: by apply: fin_num_measure => //; apply: measurableI.
Qed.

Lemma conditional_independentC (P : probability T R) E1 E2 :
  d.-measurable E1 -> d.-measurable E2 ->
  P E1 != 0 -> P E2 != 0 ->
    reflect ('P[E1 | E2] == P E1) ('P[E2 | E1] == P E2).
Proof.
move=> mE1 mE2 pE10 pE20.
apply/(iffP idP)=>/eqP.
+ move/(@conditional_independent_is_pairwise_independent _ _ _ mE2 mE1 pE10).
  move/pairwise_independentC.
  by move/(conditional_independence pE20)/eqP.
+ move/(@conditional_independent_is_pairwise_independent _ _ _ mE1 mE2 pE20).
  move/pairwise_independentC.
  by move/(conditional_independence pE10)/eqP.
Qed.

(* Lemma summation (I : choiceType) (A : {fset I}) E F (P : probability T R) : *)
(*   (* the sets are disjoint *) *)
(*   P (\bigcap_(i in [set` A]) F i) = 1 -> P E = \prod_(i <- A) ('P [E | F i] * P (F i)). *)
(* Proof. *)
(* move=> pF1. *)

Lemma bayes (P : probability T R) E F :
  d.-measurable E -> d.-measurable F ->
  'P[ E | F ] = ((fine ('P[F | E] * P E)) / (fine (P F)))%:E.
Proof.
rewrite /conditional_probability => mE mF.
have [PE0|PE0] := eqVneq (P E) 0.
  have -> : P (E `&` F) = 0.
    by apply/eqP; rewrite eq_le -{1}PE0 (@measureIl _ _ _ P E F mE mF)/= measure_ge0.
  by rewrite PE0 fine0 invr0 mulr0 mule0 mul0r.
by rewrite -{2}(@fineK _ (P E)) -?EFinM -?(mulrA (fine _)) ?mulVf ?fine_eq0 ?fin_num_measure// mul1r setIC//.
Qed.

End conditional_probability.
Notation "' P [ E1 | E2 ]" := (conditional_probability P E1 E2).

From mathcomp Require Import real_interval.

Section independent_RVs.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Definition pairwise_independent_RV (X Y : {RV P >-> R}) :=
  forall s t, pairwise_independent P (X @^-1` s) (Y @^-1` t).

Lemma conditional_independent_RV (X Y : {RV P >-> R}) :
  pairwise_independent_RV X Y ->
  forall s t, P (Y @^-1` t) != 0 -> 'P [X @^-1` s | Y @^-1` t] = P (X @^-1` s).
Proof.
move=> iRVXY s t PYtne0.
exact: conditional_independence.
Qed.

Definition mutually_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :=
  forall x_ : I -> R, independent_events P A (fun i => X i @^-1` `[(x_ i), +oo[%classic).

Definition kwise_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) k :=
  forall x_ : I -> R, kwise_independent P A (fun i => X i @^-1` `[(x_ i), +oo[%classic) k.

Lemma nwise_indep_is_mutual_indep_RV (I : choiceType) (A : {fset I}) (X : I -> {RV P >-> R}) n :
  #|` A | = n -> kwise_independent_RV [set` A] X n -> mutually_independent_RV [set` A] X.
Proof.
rewrite/mutually_independent_RV/kwise_independent_RV=> nA kwX s.
by apply: nwise_indep_is_mutual_indep; rewrite ?nA.
Qed.

(* alternative formalization
Definition inde_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :=
  forall (s : I -> set R), mutually_independent P A (fun i => X i @^-1` s i).

Definition kwise_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) k :=
  forall (s : I -> set R), kwise_independent P A (fun i => X i @^-1` s i) k.

this should be equivalent according to wikipedia https://en.wikipedia.org/wiki/Independence_(probability_theory)#For_real_valued_random_variables
*)

(* Remark 2.15 (i) *)
Lemma prob_inde_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :
  mutually_independent_RV A X ->
    forall J : {fset I}, [set` J] `<=` A ->
      forall x_ : I -> R,
        P (\bigcap_(i in [set` J]) X i @^-1` `[(x_ i), +oo[%classic) =
          \prod_(i <- J) P (X i @^-1` `[(x_ i), +oo[%classic).
Proof.
move=> iRVX J JleA x_.
apply: (iRVX _).2 => //.
Qed.

(*
Lemma mutually_independent_RV' (I : choiceType) (A : set I)
  (X : I -> {RV P >-> R}) (S : I -> set R) :
  mutually_independent_RV A X -> 
  (forall i, A i -> measurable (S i)) ->
  mutually_independent P A (fun i => X i @^-1` S i).
Proof.
move=> miX mS.
split; first by move=> i Ai; exact/measurable_sfunP/(mS i Ai).
move=> B BA.
Abort.
*)

Lemma inde_expectation (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :
  mutually_independent_RV A X ->
    forall B : {fset I}, [set` B] `<=` A ->
    'E_P[\prod_(i <- B) X i] = \prod_(i <- B) 'E_P[X i].
Proof.
move=> AX B BA.
rewrite [in LHS]unlock.
rewrite /mutually_independent_RV in AX.
rewrite /independent_events in AX.
Abort.

End independent_RVs.

Section bool_to_real.
Context d (T : measurableType d) (R : realType) (P : probability T R) (f : {mfun T >-> bool}).
Definition bool_to_real : T -> R := (fun x => x%:R) \o (f : T -> bool).

Lemma measurable_bool_to_real : measurable_fun [set: T] bool_to_real.
Proof.
rewrite /bool_to_real.
apply: measurableT_comp => //=.
exact: (@measurable_funP _ _ _ _ f).
Qed.
(* HB.about isMeasurableFun.Build. *)
HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ bool_to_real measurable_bool_to_real.

HB.instance Definition _ := MeasurableFun.on bool_to_real.

Definition btr : {RV P >-> R} := bool_to_real.

End bool_to_real.

Section independent_RVs_btr.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs_btr
    (I : set nat) (X : nat -> {mfun T >-> bool}) :
  independent_RVs P I X -> independent_RVs P I (fun i : nat => btr P (X i)).
Proof.
move=> PIX; split.
- move=> i Ii.
  rewrite /g_sigma_algebra_preimage/= /preimage_set_system/= => _ [A mA <-].
  by rewrite setTI; exact/measurable_sfunP.
- move=> J JI E/= JEfX; apply PIX => // j jJ.
  have := JEfX _ jJ; rewrite !inE.
  rewrite /g_sigma_algebra_preimage /preimage_set_system/= => -[A mA <-].
  by exists ((fun x => x%:R) @^-1` A).
Qed.

End independent_RVs_btr.

Section mfunM.
Context {d} (T : measurableType d) {R : realType}.

HB.instance Definition _ (f g : {mfun T >-> R}) :=
  @isMeasurableFun.Build d _ _ _ (f \* g)%R (measurable_funM (@measurable_funP _ _ _ _ f) ((@measurable_funP _ _ _ _ g))).

End mfunM.

Section move.

Lemma sumr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\sum_(i <- l | Q i) f i) x = \sum_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ g _ h <- <-. Qed.

Lemma prodr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\prod_(i <- l | Q i) f i) x = \prod_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ h _ g <- <-. Qed.

Definition sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) : T -> R :=
  fun x => \sum_(f <- s) f x.

Lemma measurable_sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :
  measurable_fun setT (sumrfct s).
Proof.
apply/measurable_EFinP => /=; apply/measurableT_comp => //.
exact: measurable_sum.
Qed.

HB.instance Definition _ {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (sumrfct s) (measurable_sumrfct s).

Lemma sum_mfunE {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) x :
  ((\sum_(f <- s) f) x = sumrfct s x)%R.
Proof. by rewrite/sumrfct; elim/big_ind2 : _ => //= u a v b <- <-. Qed.


End move.

Definition measure_tuple_display : measure_display -> measure_display.
Proof. exact. Qed.

Definition g_sigma_preimage d (rT : semiRingOfSetsType d) (aT : Type)
    (n : nat) (f : 'I_n -> aT -> rT) : set (set aT) :=
  <<s \big[setU/set0]_(i < n) preimage_set_system setT (f i) measurable >>.

HB.instance Definition _ (n : nat) (T : pointedType) :=
  isPointed.Build (n.-tuple T) (nseq n point).

Definition mtuple (n : nat) d (T : measurableType d) : Type := n.-tuple T.

HB.instance Definition _ (n : nat) d (T : measurableType d) := Pointed.on (mtuple n T).

Lemma countable_range_bool d (T : measurableType d) (b : bool) :
  countable (range (@cst T _ b)).
Proof. exact: countableP. Qed.

HB.instance Definition _ d (T : measurableType d) b :=
  MeasurableFun_isDiscrete.Build d _ T _  (cst b) (countable_range_bool T b).

Section measurable_tuple.
Context {d} {T : measurableType d}.
Variable n : nat.

Let coors := (fun i x => @tnth n T x i).

Let prod_salgebra_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let prod_salgebra_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let prod_salgebra_bigcup (F : _^nat) :
  (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build (measure_tuple_display d)
    (mtuple n T) (g_sigma_preimage coors)
    (prod_salgebra_set0) (prod_salgebra_setC) (prod_salgebra_bigcup).

End measurable_tuple.

Section bernoulli.

Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Definition bernoulli_RV (X : {RV P >-> bool}) :=
  distribution P X = bernoulli p.

Lemma bernoulli_RV1 (X : {RV P >-> bool}) : bernoulli_RV X ->
  P [set i | X i == 1%R] = p%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 1%:R]))]].
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= mem_set// mule1// diracE/= memNset//.
rewrite mule0 adde0.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_RV2 (X : {RV P >-> bool}) : bernoulli_RV X ->
  P [set i | X i == 0%R] = (`1-p)%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 0%:R]))]].
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= memNset//.
rewrite mule0// diracE/= mem_set// add0e mule1.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_expectation (X : {RV P >-> bool}) :
  bernoulli_RV X -> 'E_P[btr P X] = p%:E.
Proof.
move=> bX.
rewrite unlock /btr.
rewrite -(@ge0_integral_distribution _ _ _ _ _ _ X (EFin \o [eta GRing.natmul 1]))//; last first.
  by move=> y //=.
rewrite /bernoulli/=.
rewrite (@eq_measure_integral _ _ _ _ (bernoulli p)); last first.
  by move=> A mA _/=; rewrite (_ : distribution P X = bernoulli p).
rewrite integral_bernoulli//=.
by rewrite -!EFinM -EFinD mulr0 addr0 mulr1.
Qed.

Lemma integrable_bernoulli (X : {RV P >-> bool}) :
  bernoulli_RV X -> P.-integrable [set: T] (EFin \o btr P X).
Proof.
move=> bX.
apply/integrableP; split; first by apply: measurableT_comp => //; exact: measurable_bool_to_real.
have -> : \int[P]_x `|(EFin \o btr P X) x| = 'E_P[btr P X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  by rewrite gee0_abs //= lee_fin.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma bool_RV_sqr (X : {dRV P >-> bool}) :
  ((btr P X ^+ 2) = btr P X :> (T -> R))%R.
Proof.
apply: funext => x /=.
rewrite /GRing.exp /btr/bool_to_real /GRing.mul/=.
by case: (X x) => /=; rewrite ?mulr1 ?mulr0.
Qed.

Lemma bernoulli_variance (X : {dRV P >-> bool}) :
  bernoulli_RV X -> 'V_P[btr P X] = (p * (`1-p))%:E.
Proof.
move=> b.
rewrite (@varianceE _ _ _ _ (btr P X));
  [|rewrite ?[X in _ \o X]bool_RV_sqr; exact: integrable_bernoulli..].
rewrite [X in 'E_P[X]]bool_RV_sqr !bernoulli_expectation//.
by rewrite expe2 -EFinD onemMr.
Qed.

(* TODO: define a mixin *)
Program Definition is_bernoulli_trial n (X : n.-tuple {RV P >-> bool}) :=
  (forall i : 'I_n, bernoulli_RV (tnth X i)) /\
  independent_RVs P `I_n (fun i => nth _ X i).
Next Obligation.
move=> n X i.
have @h : {RV P >-> bool}.
  exact: (cst false).
exact: h.
Defined.

Axiom pro : forall (n : nat) (P : probability T R), probability (mtuple n T) R.

Definition sumrfct_tuple n (s : n.-tuple {mfun T >-> R}) : mtuple n T -> R :=
  (fun x => \sum_(i < n) (tnth s i) (tnth x i))%R.

Lemma measurable_sumrfct_tuple n (s : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (sumrfct_tuple s).
Proof.
Admitted.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (sumrfct_tuple s) (measurable_sumrfct_tuple s).

Definition prodrfct_tuple n (s : n.-tuple {mfun T >-> R}) : mtuple n T -> R :=
  (fun x => \prod_(i < n) (tnth s i) (tnth x i))%R.

Lemma measurable_prodrfct_tuple n (s : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (prodrfct_tuple s).
Admitted.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (prodrfct_tuple s) (measurable_prodrfct_tuple s).

Lemma measurable_tnth n (i : 'I_n.+1) :
  measurable_fun [set: mtuple n.+1 T] (@tnth _ T ^~ i).
Proof.
move=> _ Y mY.
rewrite setTI.
have -> : (@tnth _ T)^~ i @^-1` Y
    = \bigcup_(t in [set t : n.+1.-tuple T| @tnth n.+1 T t i \in Y]) [set t].
  apply/seteqP; split=> [t/= Yti|t].
  - exists t => //=.
    by rewrite inE.
  - move=> [t' /= t'iY] tt'.
    subst t'.
    by move/set_mem in t'iY.
Abort.

Definition bernoulli_trial n (X : n.-tuple {RV P >-> bool}) : {RV (pro n P) >-> R} :=
  sumrfct_tuple [the n.-tuple _ of (map (btr P)
   (map (fun t : {RV P >-> bool} => t : {mfun T >-> bool}) X))].

(*
was wrong
Definition bernoulli_trial n (X : {dRV P >-> bool}^nat) : {RV (pro n P) >-> R} :=
  (\sum_(i<n) (btr P (X i)))%R. (* TODO: add HB instance measurablefun sum*)
*)

Lemma expectation_sum_pro n (X : n.-tuple {RV P >-> R}) :
    (forall Xi, Xi \in X -> P.-integrable [set: T] (EFin \o Xi)) ->
  'E_(pro n P)[sumrfct_tuple X] = \sum_(i < n) ('E_P[(tnth X i)]).
Proof.
move: n X.
elim => [X|n IH X] /= intX.
- rewrite /sumrfct_tuple.
  under eq_fun do rewrite big_ord0.
  by rewrite big_ord0 expectation_cst.
pose X0 := tnth X ord0.
have intX0 : P.-integrable [set: T] (EFin \o X0).
  by apply: intX; rewrite mem_tnth.
have {}intX Xi : Xi \in X -> P.-integrable [set: T] (EFin \o Xi).
  by move=> XiX; exact: intX.
rewrite big_ord_recr/=.
rewrite /sumrfct_tuple/=.
under eq_fun do rewrite big_ord_recr/=.
pose X1 := fun x : mtuple n.+1 T =>
                (\sum_(i < n) MeasurableFun.sort (tnth X (widen_ord (leqnSn n) i)) (tnth x (widen_ord (leqnSn n) i)))%R.
have mX1 : measurable_fun setT X1.
  apply: measurable_sum => /= i.
  admit.
pose build_mX1 := isMeasurableFun.Build _ _ _ _ _ mX1.
pose Y1 : {mfun mtuple n.+1 T >-> R} := HB.pack X1 build_mX1.
pose X2 := fun x : mtuple n.+1 T =>
                MeasurableFun.sort (tnth X ord_max) (tnth x ord_max).
have mX2 : measurable_fun setT X2.
  rewrite /X2 /=.
  admit.
pose build_mX2 := isMeasurableFun.Build _ _ _ _ _ mX2.
pose Y2 : {mfun mtuple n.+1 T >-> R} := HB.pack X2 build_mX2.
rewrite [X in 'E__[X]](_ : _ = Y1 \+ Y2)//.
rewrite expectationD; last 2 first.
  admit.
  admit.
congr (_ + _); last first.
- rewrite /Y1/X1/=.
  rewrite unlock /expectation.
  pose phi : mtuple n.+1 T -> T := (fun w => @tnth n.+1 T w ord_max).
  have mphi : measurable_fun setT phi.
    rewrite /phi.
    admit.
  rewrite -(@integral_pushforward _ _ _ _ _ phi mphi _ (fun w => (tnth X ord_max w)%:E)); last 2 first.
    admit.
    admit.
  congr (\int[_]__ _).
  rewrite /pushforward.
  apply: funext => x.
  admit.
rewrite /Y2/X2/=.
Admitted.

Lemma expectation_bernoulli_trial n (X : n.-tuple {RV P >-> bool}) :
  is_bernoulli_trial X -> 'E_(pro n P)[bernoulli_trial X] = (n%:R * p)%:E.
Proof.
move=> bRV. rewrite /bernoulli_trial.
transitivity ('E_(pro n P)[sumrfct_tuple (map (btr P) X)]).
  (*by rewrite big_map -[in RHS](subn0 n) big_mkord.*) admit.
rewrite expectation_sum_pro; last first.
  move=> Xi.
  move=> /mapP[/= k kn] ->.
  have [i ki] : exists i : 'I_n, k = tnth X i.
    by apply/tnthP.
  apply: integrable_bernoulli.
  rewrite ki.
  by apply bRV.
(*rewrite big_map -[in LHS](subn0 n) big_mkord.*)
transitivity (\sum_(i < n) p%:E).
  apply: eq_bigr => k _.
  (*rewrite bernoulli_expectation//.
  apply bRV.
  by [].*) admit.
by rewrite sumEFin big_const_ord iter_addr addr0 mulrC mulr_natr.
(*rewrite /is_bernoulli_trial /bernoulli_RV.
move=> [bRV iRV].
rewrite /bernoulli_trial.
rewrite expectation_sum_pro; last first.
  move=> /= Xi.
  rewrite map_f.
  move/mapP => []Xj /=+ ->.
  rewrite /mem/=/in_mem/=.
  apply: integrable_bernoulli.
  admit.
under eq_bigr do rewrite !tnth_map/= bernoulli_expectation//.
by rewrite sumr_const card_ord EFinM mule_natl.*)
Admitted.

Lemma bernoulli_trial_ge0 n (X : n.-tuple {RV P >-> bool}) : is_bernoulli_trial X ->
  (forall t, 0 <= bernoulli_trial X t)%R.
Proof.
move=> [bRV Xn] t.
rewrite /bernoulli_trial.
(*have -> : (\sum_(i < n) btr P (X i))%R = (\sum_(s <- map (btr P \o X) (iota 0 n)) s)%R.
  by rewrite big_map -[in RHS](subn0 n) big_mkord.
have -> : (\sum_(s <- [seq (btr P \o X) i | i <- iota 0 n]) s)%R t = (\sum_(s <- [seq (btr P \o X) i | i <- iota 0 n]) s t)%R.
  by rewrite sum_mfunE.
rewrite big_map.
by apply: sumr_ge0 => i _/=; rewrite /bool_to_real/= ler0n.
Qed.*) Admitted.

(* this seems to be provable like in https://www.cs.purdue.edu/homes/spa/courses/pg17/mu-book.pdf page 65
taylor_ln_le :
  forall (delta : R), ((1 + delta) * ln (1 + delta) >= delta + delta^+2 / 3)%R.  *)
Section taylor_ln_le.
Local Open Scope ring_scope.

Axiom expR2_lt8 : expR 2 <= 8 :> R.

Lemma taylor_ln_le (x : R) : x \in `]0, 1[ -> (1 + x) * ln (1 + x) >= x + x^+2 / 3.
Proof.
move=> x01; rewrite -subr_ge0.
pose f (x : R) := (1 + x) * ln (1 + x) - (x + x ^+ 2 / 3).
have f0 : f 0 = 0 by rewrite /f expr0n /= mul0r !addr0 ln1 mulr0 subr0.
rewrite [leRHS](_ : _ = f x) // -f0.
evar (df0 : R -> R); evar (df : R -> R).
have idf (y : R) : 0 < 1 + y -> is_derive y (1:R) f (df y).
  move=> y1.
  rewrite (_ : df y = df0 y).
    apply: is_deriveB; last exact: is_deriveD.
    apply: is_deriveM=> //.
    apply: is_derive1_comp=> //.
    exact: is_derive1_ln.
  rewrite /df0.
  rewrite deriveD// derive_cst derive_id.
  rewrite /GRing.scale /= !(mulr0,add0r,mulr1).
  rewrite divff ?lt0r_neq0// opprD addrAC addrA subrr add0r.
  instantiate (df := fun y : R => - (3^-1 * (y + y)) + ln (1 + y)).
  reflexivity.
clear df0.
have y1cc y : y \in `[0, 1] -> 0 < 1 + y.
  rewrite in_itv /= => /andP [] y0 ?.
  by have y1: 0 < 1 + y by apply: (le_lt_trans y0); rewrite ltrDr.
have y1oo y : y \in `]0, 1[ -> 0 < 1 + y by move/subset_itv_oo_cc/y1cc.
have dfge0 y : y \in `]0, 1[ -> 0 <= df y.
  move=> y01.
  have:= y01.
  rewrite /df in_itv /= => /andP [] y0 y1.
  rewrite -lerBlDl opprK add0r -mulr2n -(mulr_natl _ 2) mulrA.
  rewrite [in leLHS](_ : y = 1 + y - 1); last by rewrite addrAC subrr add0r.
  pose iy:= Itv01 (ltW y0) (ltW y1).
  have y1E: 1 + y = @convex.conv _ R^o iy 1 2.
    rewrite convRE /= /onem mulr1 (mulr_natr _ 2) mulr2n.
    by rewrite addrACA (addrC (- y)) subrr addr0.
  rewrite y1E; apply: (le_trans _ (concave_ln _ _ _))=> //.
  rewrite -y1E addrAC subrr add0r convRE ln1 mulr0 add0r /=.
  rewrite mulrC ler_pM// ?(@ltW _ _ 0)// mulrC.
  rewrite ler_pdivrMr//.
  rewrite -[leLHS]expRK -[leRHS]expRK ler_ln ?posrE ?expR_gt0//.
  rewrite expRM/= powR_mulrn ?expR_ge0// lnK ?posrE//.
  rewrite !exprS expr0 mulr1 -!natrM mulnE /=.
  by rewrite expR2_lt8.
apply: (@ger0_derive1_homo R f 0 1 true false).
- by move=> y /y1oo /idf /@ex_derive.
- by move=> y /[dup] /y1oo /idf /@derive_val ->; exact: dfge0.
- by apply: derivable_within_continuous=> y /y1cc /idf /@ex_derive.
- by rewrite bound_itvE.
- exact: subset_itv_oo_cc.
- by have:= x01; rewrite in_itv=> /andP /= [] /ltW.
Qed.

End taylor_ln_le.

Lemma independent_mmt_gen_fun (X : {RV P >-> bool}^nat) n t :
  let mmtX (i : nat) : {RV P >-> R} := expR \o t \o* (btr P (X i)) in
  independent_RVs P `I_n X -> independent_RVs P `I_n mmtX.
Proof.
rewrite /= => PnX.
apply: independent_RVs_comp => //.
apply: independent_RVs_scale => //=.
exact: independent_RVs_btr.
Qed.

Lemma expectation_prod_independent_RVs n (X : n.-tuple {RV P >-> R}) :
  independent_RVs P `I_n (fun i => nth (@cst T R 0%R : {mfun T >-> R})
      (map (fun x : {RV P >-> R} => x : {mfun T >-> R}) X)
    i) ->
  'E_(pro n P)[ prodrfct_tuple X  ] = \prod_(i < n) 'E_P[ (tnth X i) ].
Proof.
Admitted.

(* wrong lemma *)
Lemma bernoulli_trial_mmt_gen_fun n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ in
  'M_X t = \prod_(i < n) 'M_(btr P (tnth X_ i)) t.
Proof.
move=> []bRVX iRVX /=.
rewrite /bernoulli_trial/mmt_gen_fun.
pose mmtX : n.-tuple {mfun T >-> R} := map (fun X => mmt_gen_fun0 X t)
  (map (btr P)  X_).
(*pose mmtX (i : 'I_n) : {RV P >-> R} := expR \o t \o* (btr P (tnth X_ i)).*)
have iRV_mmtX : independent_RVs P setT (fun i => tnth mmtX i).
  (*exact: independent_mmt_gen_fun.*) admit.
transitivity ('E_(pro n P)[ prodrfct_tuple mmtX ])%R.
  (*congr ('E_P[_]).
  apply: funext => x/=.
  rewrite sumr_map mulr_suml expR_sum prodr_map.
  exact: eq_bigr.*) admit.
rewrite /mmtX.
rewrite expectation_prod_independent_RVs; last first.
  admit.
apply: eq_bigr => /= i _.
congr expectation.
rewrite /=.
rewrite tnth_map/=.
by rewrite tnth_map/=.
Admitted.

Arguments sub_countable [T U].
Arguments card_le_finite [T U].

Lemma bernoulli_mmt_gen_fun (X : {RV P >-> bool}) (t : R) :
  bernoulli_RV X -> 'M_(btr P X : {RV P >-> R}) t = (p * expR t + (1-p))%:E.
Proof.
move=> bX. rewrite/mmt_gen_fun.
pose mmtX : {RV P >-> R} := expR \o t \o* (btr P X).
set A := X @^-1` [set true].
set B := X @^-1` [set false].
have mA: measurable A by exact: measurable_sfunP.
have mB: measurable B by exact: measurable_sfunP.
have dAB: [disjoint A & B]
  by rewrite /disj_set /A /B preimage_true preimage_false setICr.
have TAB: setT = A `|` B by rewrite -preimage_setU -setT_bool preimage_setT.
rewrite unlock.
rewrite TAB integral_setU_EFin -?TAB//.
under eq_integral.
  move=> x /=.
  rewrite /A inE /bool_to_real /= => ->.
  rewrite mul1r.
  over.
rewrite integral_cst//.
under eq_integral.
  move=> x /=.
  rewrite /B inE /bool_to_real /= => ->.
  rewrite mul0r.
  over.
rewrite integral_cst//.
rewrite /A /B /preimage /=.
under eq_set do rewrite (propext (rwP eqP)).
rewrite (bernoulli_RV1 bX).
under eq_set do rewrite (propext (rwP eqP)).
rewrite (bernoulli_RV2 bX).
rewrite -EFinD; congr (_ + _)%:E; rewrite mulrC//.
by rewrite expR0 mulr1.
Qed.

(* wrong lemma *)
Lemma binomial_mmt_gen_fun n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ : {RV pro n P >-> R} in
  'M_X t = ((p * expR t + (1-p))`^(n%:R))%:E.
Proof.
move: p01 => /andP[p0 p1] bX/=.
rewrite bernoulli_trial_mmt_gen_fun//.
under eq_bigr => i _.
  rewrite bernoulli_mmt_gen_fun; last exact: bX.1.
  over.
rewrite big_const iter_mule mule1 cardT size_enum_ord -EFin_expe powR_mulrn//.
by rewrite addr_ge0// ?subr_ge0// mulr_ge0// expR_ge0.
Qed.

Lemma mmt_gen_fun_expectation n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  (0 <= t)%R ->
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ : {RV pro n P >-> R} in
  'M_X t <= (expR (fine 'E_(pro n P)[X] * (expR t - 1)))%:E.
Proof.
move=> t0 bX/=.
have /andP[p0 p1] := p01.
rewrite binomial_mmt_gen_fun// lee_fin.
rewrite expectation_bernoulli_trial//.
rewrite addrCA -{2}(mulr1 p) -mulrN -mulrDr.
rewrite -mulrA (mulrC (n%:R)) expRM ge0_ler_powR// ?nnegrE ?expR_ge0//.
  by rewrite addr_ge0// mulr_ge0// subr_ge0 -expR0 ler_expR.
exact: expR_ge1Dx.
Qed.

Lemma end_thm24 n (X_ : n.-tuple {RV P >-> bool}) (t delta : R) :
  is_bernoulli_trial X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(pro n P)[X] in
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

(* theorem 2.4 Rajani / thm 4.4.(2) mu-book *)
Theorem bernoulli_trial_inequality1 n (X_ : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(pro n P)[X] in
  (pro n P) [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => bX delta0.
set X := @bernoulli_trial n X_.
set mu := 'E_(pro n P)[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltrDl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expR (fine mu * (expR t - 1)))%:E *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  by apply: (mmt_gen_fun_expectation _ bX); rewrite le_eqVlt t0 orbT.
rewrite mulrC expRM -mulNr mulrA expRM.
exact: (end_thm24 _ bX).
Qed.

(* theorem 2.5 *)
Theorem bernoulli_trial_inequality2 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_(pro n P)[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  (pro n P) [set i | X' i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> bX X' mu n0 /[dup] delta01 /andP[delta0 _].
apply: (@le_trans _ _ (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK; last rewrite posrE addr_gt0//.
  apply: (bernoulli_trial_inequality1 bX) => //.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    by rewrite fine_ge0//; apply: expectation_ge0 => t; exact: (bernoulli_trial_ge0 bX).
  rewrite lerB//.
  apply: taylor_ln_le.
  by rewrite in_itv /=.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

Lemma norm_expR : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

(* Rajani thm 2.6 / mu-book thm 4.5.(2) *)
Theorem bernoulli_trial_inequality3 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X -> (0 < delta < 1)%R ->
  let X' := @bernoulli_trial n X : {RV pro n P >-> R} in
  let mu := 'E_(pro n P)[X'] in
  (pro n P) [set i | X' i <= (1 - delta) * fine mu]%R <= (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> bX /andP[delta0 delta1] /=.
set X' := @bernoulli_trial n X : {RV pro n P >-> R}.
set mu := 'E_(pro n P)[X'].
have /andP[p0 p1] := p01.
apply: (@le_trans _ _ (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    (pro n P) [set i | (X' i <= (1 - delta) * fine mu)%R] = (pro n P) [set i | `|(expR \o t \o* X') i|%:E >= (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltrNr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltrBlDr ltrDl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ (((fine 'E_(pro n P)[normr \o expR \o t \o* X']) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite EFinM lee_pdivl_mulr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ (pro n P) (expR \o t \o* X' : {RV (pro n P) >-> R}) id (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - apply: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_(pro n P)[expR \o t \o* X'] = 'M_X' t by [].
      by rewrite (binomial_mmt_gen_fun _ bX).
  apply: (@le_trans _ _ (((expR ((expR t - 1) * fine mu)) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_(pro n P)[expR \o t \o* X'] = 'M_X' t by [].
    rewrite (binomial_mmt_gen_fun _ bX)/=.
    rewrite /mu /X' (expectation_bernoulli_trial bX)/=.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expRM powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      by rewrite addr_ge0 ?mulr_ge0// subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expRM.
    rewrite addrCA -{2}(mulr1 p) -mulrBr addrAC subrr sub0r mulrC mulNr.
    by apply: expR_ge1Dx.
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
  (* requires analytical argument: see p.66 of mu's book *)
  Local Open Scope ring_scope.
  rewrite -(@ler_pM2r _ 2)// -mulrA mulVf// mulr1 mulrDl.
  rewrite -subr_le0 mulNr opprK.
  rewrite addrC !addrA.
  have->: delta ^+ 2 - delta * 2 = (1 - delta)^+2 - 1.
    rewrite sqrrB expr1n mul1r [RHS]addrC !addrA addNr add0r addrC -mulNrn.
    by rewrite -(mulr_natr (- delta) 2) mulNr.
  rewrite addrAC subr_le0.
  set f := fun (x : R) => x ^+ 2 + - (x * ln x) * 2.
  have @idf (x : R^o) : 0 < x -> {df | is_derive x 1 (f : R^o -> R^o) df}.
    move=> x0; evar (df : (R : Type)); exists df.
    apply: is_deriveD; first by [].
    apply: is_deriveM; last by [].
    apply: is_deriveN.
    apply: is_deriveM; first by [].
    exact: is_derive1_ln.
  suff: forall x : R, x \in `]0, 1[ -> f x <= 1.
    by apply; rewrite memB_itv0 in_itv /= delta0 delta1.
  move=> x x01.
  have->: 1 = f 1 by rewrite /f expr1n ln1 mulr0 oppr0 mul0r addr0.
  apply: (@ger0_derive1_homo _ f 0 1 false false)=> //.
  - move=> t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - move=> t /[!in_itv] /= /andP [] t0 t1.
    Local Arguments derive_val {R V W a v f df}.
    rewrite (derive_val (svalP (idf _ t0))) /=.
    clear idf.
    rewrite exp_derive derive_cst derive_id .
    rewrite scaler0 add0r /GRing.scale /= !mulr1 expr1.
    rewrite -mulrDr mulr_ge0// divff ?lt0r_neq0//.
    rewrite opprD addrA subr_ge0 -ler_expR.
    have:= t0; rewrite -lnK_eq => /eqP ->.
    by rewrite -[leLHS]addr0 -(subrr 1) addrCA expR_ge1Dx.
  - apply: derivable_within_continuous => t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - by apply: (subset_itvW_bound _ _ x01); rewrite bnd_simp.
  - by rewrite in_itv /= ltr01 lexx.
  - by move: x01; rewrite in_itv=> /= /andP [] _ /ltW.
Qed.
Local Open Scope ereal_scope.

(* Rajani -> corollary 2.7 / mu-book -> corollary 4.7 *)
Corollary bernoulli_trial_inequality4 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X -> (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (0 < p)%R ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_(pro n P)[X'] in
  (pro n P) [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> bX /andP[d0 d1] n0 p0 /=.
set X' := @bernoulli_trial n X.
set mu := 'E_(pro n P)[X'].
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
  apply: measurableT_comp => //.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply: measurableT_comp => //.
- rewrite disjoints_subset => x /=.
  rewrite /mem /in_mem/= => X0; apply/negP.
  rewrite -ltNge.
  apply: (@lt_le_trans _ _ _ _ _ _ X0).
  rewrite !EFinM.
  rewrite lte_pmul2r//; first by rewrite lte_fin ltrD2l gt0_cp.
  by rewrite fineK /mu/X' (expectation_bernoulli_trial bX)// lte_fin  mulr_gt0 ?ltr0n.
rewrite mulr2n EFinD lee_add//=.
- by apply: (bernoulli_trial_inequality2 bX); rewrite //d0 d1.
- have d01 : (0 < delta < 1)%R by rewrite d0.
  apply: (le_trans (@bernoulli_trial_inequality3 _ X delta bX d01)).
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  by rewrite /X' lee_fin; apply: (bernoulli_trial_ge0 bX).
Qed.

(* Rajani thm 3.1 / mu-book thm 4.7 *)
Theorem sampling n (X : n.-tuple {RV P >-> bool}) (theta delta : R) :
  let X_sum := bernoulli_trial X in
  let X' x := (X_sum x) / n%:R in
  (0 < p)%R ->
  is_bernoulli_trial X ->
  (0 < delta <= 1)%R -> (0 < theta < p)%R -> (0 < n)%nat ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  (pro n P) [set i | `| X' i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X_sum X' p0 bX /andP[delta0 delta1] /andP[theta0 thetap] n0 tdn.
have E_X_sum: 'E_(pro n P)[X_sum] = (p * n%:R)%:E.
  by rewrite /X_sum expectation_bernoulli_trial// mulrC.
have /andP[_ p1] := p01.
set epsilon := theta / p.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : (pro n P) [set i | `| X' i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in (pro n P) X <= _](_ : _ =
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
  exact: (@bernoulli_trial_inequality4 _ X epsilon bX).
have step2 : (pro n P) [set i | `| X' i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA.
  rewrite /epsilon -mulrA mulVf ?gt_eqF// mulr1 -!mulrA !ler_wpM2l ?(ltW theta0)//.
  rewrite mulrCA ler_wpM2l ?(ltW theta0)//.
  rewrite [X in (_ * X)%R]mulrA mulVf ?gt_eqF// -[leLHS]mul1r [in leRHS]mul1r.
  by rewrite ler_wpM2r// invf_ge1.
suff : delta%:E >= (pro n P) [set i | (`|X' i - p| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in (pro n P) X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p| < theta)%R]); last first.
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
Admitted.

End bernoulli.
