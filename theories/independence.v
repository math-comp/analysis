(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop interval_inference.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure kernel probability.

(**md**************************************************************************)
(* # Independence                                                             *)
(*                                                                            *)
(* ```                                                                        *)
(* independent_events I F == the events F indexed by I are independent        *)
(* mutual_independence I F == the set systems F indexed by I are independent  *)
(* independent_RVs I X == the random variables X indexed by I are independent *)
(* independent_RVs2 X Y == the random variables X and Y are independent       *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "I .-independent X" (at level 2, format "I .-independent  X").

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section independent_events.
Context {R : realType} d {T : measurableType d} (P : probability T R)
  {I0 : choiceType}.
Local Open Scope ereal_scope.

Definition independent_events (I : set I0) (E : I0 -> set T) :=
  (forall i, I i -> measurable (E i)) /\
  forall J : {fset I0}, [set` J] `<=` I ->
    P (\bigcap_(i in [set` J]) E i) = \prod_(i <- J) P (E i).

Definition kwise_independent_events (A : set I0) (E : I0 -> set T) k :=
  (forall i, A i -> measurable (E i)) /\
  forall B : {fset I0}, [set` B] `<=` A -> (#|` B | <= k)%nat ->
    P (\bigcap_(i in [set` B]) E i) = \prod_(i <- B) P (E i).

End independent_events.

Section independent_events.
Context {R : realType} d {T : measurableType d} (P : probability T R)
  {I0 : choiceType}.
Local Open Scope ereal_scope.

Lemma sub_independent_events (A B : set I0) (E : I0 -> set T) :
  A `<=` B -> independent_events P B E -> independent_events P A E.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Lemma sub_kwise_independent (A B : set I0) (E : I0 -> set T) k :
  A `<=` B -> kwise_independent_events P B E k -> kwise_independent_events P A E k.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Lemma independent_events_is_kwise_independent (A : set I0) (E : I0 -> set T) k :
  independent_events P A E -> kwise_independent_events P A E k.
Proof.
rewrite /independent_events /kwise_independent_events.
move=> [mE miE]; split=> // B BleA _.
exact: miE.
Qed.

Lemma nwise_indep_is_mutual_indep (A : {fset I0}) (E : I0 -> set T) n :
  #|` A | = n -> kwise_independent_events P [set` A] E n -> independent_events P [set` A] E.
Proof.
rewrite /independent_events /kwise_independent_events.
move=> nA [mE miE]; split=> // B BleA.
apply: miE => //; rewrite -nA fsubset_leq_card//.
by apply/fsubsetP => x xB; exact: (BleA x).
Qed.

Lemma independent_events_weak (E : I0 -> set T) (B : set I0) :
    (forall b, ~ B b -> E b = setT) ->
  independent_events P [set: I0] E <-> independent_events P B E.
Proof.
move=> BE; split; first exact: sub_independent_events.
move=> [mE h]; split=> [i _|C _].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I0}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last first.
  rewrite -CBD; exact: subIsetr.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Lemma kwise_independent_events_weak (E : I0 -> set T) (B : set I0) k :
    (forall b, ~ B b -> E b = setT) ->
  kwise_independent_events P [set: I0] E k <-> kwise_independent_events P B E k.
Proof.
move=> BE; split; first exact: sub_kwise_independent.
move=> [mE h]; split=> [i _|C _ Ck].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I0}, [set` C] `&` B = [set` D].
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

End independent_events.

Section independent_events.
Context {R : realType} d {T : measurableType d} (P : probability T R).
Local Open Scope ereal_scope.

Lemma kwise_independent_weak01 E1 E2 :
  kwise_independent_events P [set: nat] (bigcap2 E1 E2) 2%N <->
  kwise_independent_events P [set 0%N; 1%N] (bigcap2 E1 E2) 2%N.
Proof.
apply kwise_independent_events_weak.
by move=> n /= /not_orP[/eqP /negbTE -> /eqP /negbTE ->].
Qed.

End independent_events.

Section pairwise_independent_events.
Context {R : realType} d {T : measurableType d} (P : probability T R).
Local Open Scope ereal_scope.

Definition pairwise_independent_events E1 E2 :=
  @independent_events _ _ _ P bool [set false; true] (bigcap2 E1 E2).

Lemma pairwise_independent_eventsM (E1 E2 : set T) :
  pairwise_independent_events E1 E2 <->
  [/\ d.-measurable E1, d.-measurable E2 & P (E1 `&` E2) = P E1 * P E2].
Proof.
split.
- move=> /(independent_events_is_kwise_independent 2) [mE1E2 /(_ [fset false; true]%fset)].
  rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => ->; last 2 first.
  + by rewrite set_fsetU !set_fset1; exact: subset_refl.
  + by rewrite cardfs2.
  split => //.
  + by apply: (mE1E2 false) => /=; left.
  + by apply: (mE1E2 true) => /=; right.
- move=> [mE1 mE2 E1E2M].
  rewrite /pairwise_independent_events.
  split.
  + by move=> [| [|]]//=.
  + move=> B B01.
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

Lemma pairwise_independent_events_setC (E1 E2 : set T) :
  pairwise_independent_events E1 E2 -> pairwise_independent_events E1 (~` E2).
Proof.
rewrite/pairwise_independent_events.
move/pairwise_independent_eventsM=> [mE1 mE2 h].
apply/pairwise_independent_eventsM; split=> //.
- exact: measurableC.
- rewrite -setDE measureD//; last first.
    exact: (le_lt_trans (probability_le1 P mE1) (ltry _)).
  rewrite probability_setC// muleBr// ?mule1 -?h//.
  by rewrite fin_num_measure.
Qed.

Lemma pairwise_independent_eventsC (E1 E2 : set T) :
  pairwise_independent_events E1 E2 -> pairwise_independent_events E2 E1.
Proof.
rewrite/pairwise_independent_events.
move=> [mE1E2 /(_ [fset false; true]%fset)].
rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => h.
split.
- case=> [_|[_|]]//=.
  + by apply: (mE1E2 false) => /=; left.
  + by apply: (mE1E2 true) => /=; right.
- move=> B B01.
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
Qed.

End pairwise_independent_events.

Section mutual_independence.
Context {R : realType} d {T : measurableType d} (P : probability T R)
  {I0 : choiceType}.
Local Open Scope ereal_scope.

(* NB: not used *)
Definition g_sigma_family (I : set I0) (F : I0 -> set_system T)
    : set_system T :=
  <<s \bigcup_(i in I) F i >>.

Definition mutual_independence (I : set I0) (F : I0 -> set_system T) :=
  (forall i, I i -> F i `<=` measurable) /\
  forall J : {fset I0}, [set` J] `<=` I ->
    forall E, (forall i, i \in J -> E i \in F i) ->
      P (\big[setI/setT]_(j <- J) E j) = \prod_(j <- J) P (E j).

Definition kwise_independence (I : set I0) (F : I0 -> set_system T) k :=
  (forall i, I i -> F i `<=` measurable) /\
  forall J : {fset I0}, [set` J] `<=` I -> (#|` J | <= k)%nat ->
    forall E, (forall i, i \in J -> E i \in F i) ->
      P (\big[setI/setT]_(j <- J) E j) = \prod_(j <- J) P (E j).

Lemma eq_mutual_independence (I : set I0) (F F' : I0 -> set_system T) :
    (forall i, I i -> F i = F' i) ->
  mutual_independence I F -> mutual_independence I F'.
Proof.
move=> FF' IF; split => [i Ii|J JI E EF'].
  by rewrite -FF'//; apply IF.
apply IF => // i iJ.
by rewrite FF' ?EF'//; exact: JI.
Qed.

Lemma mutual_independence_is_kwise_independence (I : set I0) (F : I0 -> set_system T) k :
  mutual_independence I F -> kwise_independence I F k.
Proof.
rewrite /mutual_independence/kwise_independence.
move=> [mE miE]; split=> // B BleA _.
exact: miE.
Qed.

Lemma nwise_independence_is_mutual_independence (I : {fset I0}) (F : I0 -> set_system T) n :
  #|` I | = n -> kwise_independence [set` I] F n -> mutual_independence [set` I] F.
Proof.
rewrite /kwise_independence/mutual_independence.
move=> nA [mE miE]; split=> // B BleA.
apply: miE => //; rewrite -nA fsubset_leq_card//.
by apply/fsubsetP => x xB; exact: (BleA x).
Qed.

End mutual_independence.

Section independence.
Context {R : realType} d {T : measurableType d} (P : probability T R).
Local Open Scope ereal_scope.

Definition independence (F G : set_system T) :=
  [/\ F `<=` measurable , G `<=` measurable &
      forall A B, A \in F -> B \in G -> P (A `&` B) = P A * P B].

Lemma independenceP (F G : set_system T) : independence F G <->
  mutual_independence P [set: bool] (fun b => if b then F else G).
Proof.
split=> [[mF mG FG]|/= indeF].
  split=> [/= [|]//|/= J Jbool E EF].
  have [/eqP Jtrue|/eqP Jfalse| |] := set_bool [set` J].
  - rewrite -bigcap_fset Jtrue bigcap_set1.
    by rewrite fsbig_seq ?Jtrue ?fsbig_set1.
  - rewrite -bigcap_fset Jfalse bigcap_set1.
    by rewrite fsbig_seq// ?Jfalse fsbig_set1.
  - rewrite set_seq_eq0 => /eqP ->.
    by rewrite !big_nil probability_setT.
  - rewrite setT_bool => /eqP {}Jbool.
    rewrite -bigcap_fset Jbool bigcap_setU1 bigcap_set1.
    rewrite FG//.
    + rewrite -(set_fsetK J) Jbool.
      rewrite fset_setU1//= fset_set1.
      rewrite big_fsetU1 ?inE//=.
      by rewrite big_seq_fset1.
    + rewrite EF//.
      rewrite -(set_fsetK J) Jbool.
      by rewrite in_fset_set// !inE/=; left.
    + rewrite EF//.
      rewrite -(set_fsetK J) Jbool.
      by rewrite in_fset_set// !inE/=; right.
split.
- by case: indeF => /= [+ _] => /(_ true); exact.
- by case: indeF => /= [+ _] => /(_ false); exact.
- move=> A B AF BG.
  case: indeF => _ /= /(_ [fset true; false]%fset _ (fun b => if b then A else B)).
  do 2 rewrite big_fsetU1/= ?inE//= big_seq_fset1.
  by apply => // -[].
Qed.

End independence.

Lemma setI_closed_setT T (F : set_system T) :
  setI_closed F -> setI_closed (F `|` [set setT]).
Proof.
move=> IF=> C D [FC|/= ->{C}].
- move=> [FD|/= ->{D}].
    by left; exact: IF.
  by rewrite setIT; left.
- move=> [FD|->{D}].
    by rewrite setTI; left.
  by rewrite !setTI; right.
Qed.

Lemma setI_closed_set0 T (F : set_system T) :
  setI_closed F -> setI_closed (F `|` [set set0]).
Proof.
move=> IF=> C D [FC|/= ->{C}].
- move=> [FD|/= ->{D}].
    by left; exact: IF.
  by rewrite setI0; right.
- move=> [FD|->{D}].
    by rewrite set0I; right.
  by rewrite !set0I; right.
Qed.

Lemma setI_closed_set0' T (F : set_system T) :
  F set0 ->
  setI_closed (F `|` [set set0]) -> setI_closed F.
Proof.
move=> F0 IF C D FC FD.
have [//|/= ->//] : (F `|` [set set0]) (C `&` D).
by apply: IF; left.
Qed.

Lemma g_sigma_setU d {T : measurableType d} (F : set_system T) A :
  <<s F>> A ->
  <<s F >> = @measurable _ T ->
  <<s F >> = <<s F `|` [set A] >>.
Proof.
move=> FA sFT; apply/seteqP; split=> [B|B].
  by apply: sub_sigma_algebra2; exact: subsetUl.
apply: smallest_sub => // C [FC|/= ->//].
exact: sub_gen_smallest.
Qed.

Lemma g_sigma_algebra_finite_measure_unique {d} {T : measurableType d}
    {R : realType} (G : set_system T) :
  G `<=` d.-measurable ->
  setI_closed G ->
  forall m1 m2 : {finite_measure set T -> \bar R},
    m1 [set: T] = m2 [set: T] ->
    (forall A : set T, G A -> m1 A = m2 A) ->
    forall E : set T, <<s G >> E -> m1 E = m2 E.
Proof.
move=> Gm IG m1 m2 m1m2T m1m2 E sGE.
apply: (@g_sigma_algebra_measure_unique _ _ _
    (G `|` [set setT]) _ (fun=> setT)) => //.
- by move=> A [/Gm//|/= ->//].
- by right.
- by rewrite bigcup_const.
- exact: setI_closed_setT.
- by move=> B [/m1m2 //|/= ->].
- by move=> n; apply: fin_num_fun_lty; exact: fin_num_measure.
- move: E sGE; apply: smallest_sub => // C GC.
  by apply: sub_gen_smallest; left.
Qed.

(*Section lem142b.
Context d {T : measurableType d} {R : realType}.
Variable mu : {finite_measure set T -> \bar R}.
Variable F : set_system T.
Hypothesis setI_closed_F : setI_closed F. (* pi-system *)
Hypothesis FT : F `<=` @measurable _ T.
Hypothesis sFT : <<s F >> = @measurable _ T.

Lemma lem142b : forall nu : {finite_measure set T -> \bar R},
  (mu setT = nu setT) ->
  (forall E, F E -> nu E = mu E) ->
  forall A, measurable A -> mu A = nu A.
Proof.
move=> nu munu numu A mA.
apply: (measure_unique (F `|` [set setT]) (fun=> setT)) => //.
- rewrite -sFT; apply: g_sigma_setU => //.
  by rewrite sFT.
- exact: setI_closed_setT.
- by move=> n /=; right.
- by rewrite bigcup_const.
- move=> E [/numu //|/= ->].
  by rewrite munu.
- move=> n.
  apply: fin_num_fun_lty.
  exact: fin_num_measure.
Qed.

End lem142b.*)

Section mutual_independence_properties.
Context {R : realType} d {T : measurableType d} (P : probability T R).
Local Open Scope ereal_scope.

(**md see Achim Klenke's Probability Theory, Ch.2, sec.2.1, thm.2.13(i) *)
Lemma mutual_independence_fset {I0 : choiceType} (I : {fset I0})
    (F : I0 -> set_system T) :
  (forall i, i \in I -> F i `<=` measurable /\ (F i) [set: T]) ->
  mutual_independence P [set` I] F <->
  forall E, (forall i, i \in I -> E i \in F i) ->
      P (\big[setI/setT]_(j <- I) E j) = \prod_(j <- I) P (E j).
Proof.
move=> mF; split=> [indeF E EF|indeF]; first by apply indeF.
split=> [i /mF[]//|J JI E EF].
pose E' i := if i \in J then E i else [set: T].
have /indeF : forall i, i \in I -> E' i \in F i.
  move=> i iI; rewrite /E'; case: ifPn => [|iJ]; first exact: EF.
  by rewrite inE; apply mF.
move/fsubsetP : (JI) => /(big_fset_incl _) <- /=; last first.
  by move=> j jI jJ; rewrite /E' (negbTE jJ).
move/fsubsetP : (JI) => /(big_fset_incl _) <- /=; last first.
  by move=> j jI jJ; rewrite /E' (negbTE jJ); rewrite probability_setT.
rewrite big_seq [in X in X = _ -> _](eq_bigr E); last first.
  by move=> i iJ; rewrite /E' iJ.
rewrite -big_seq => ->.
by rewrite !big_seq; apply: eq_bigr => i iJ; rewrite /E' iJ.
Qed.

(**md see Achim Klenke's Probability Theory, Ch.2, sec.2.1, thm.2.13(ii) *)
Lemma mutual_independence_finiteS {I0 : choiceType} (I : set I0)
    (F : I0 -> set_system T) :
  mutual_independence P I F <->
  (forall J : {fset I0}%fset, [set` J] `<=` I ->
    mutual_independence P [set` J] F).
Proof.
split=> [indeF J JI|indeF].
  split=> [i /JI Ii|K KJ E EF].
    by apply indeF.
  by apply indeF => // i /KJ /JI.
split=> [i Ii|J JI E EF].
  have : [set` [fset i]%fset] `<=` I.
    by move=> j; rewrite /= inE => /eqP ->.
  by move/indeF => [+ _]; apply; rewrite /= inE.
by have [_] := indeF _ JI; exact.
Qed.

(**md see Achim Klenke's Probability Theory, Ch.2, sec.2.1, thm.2.13(iii) *)
Theorem mutual_independence_finite_g_sigma {I0 : choiceType} (I : set I0)
    (F : I0 -> set_system T) :
  (forall i, i \in I -> setI_closed (F i `|` [set set0])) ->
  mutual_independence P I F <-> mutual_independence P I (fun i => <<s F i>>).
Proof.
split=> indeF; last first.
  split=> [i Ii|J JI E EF].
    case: indeF => /(_ _ Ii) + _.
    by apply: subset_trans; exact: sub_gen_smallest.
  apply indeF => // i iJ; rewrite inE.
  by apply: sub_gen_smallest; exact/set_mem/EF.
split=> [i Ii|K KI E EF].
  case: indeF => + _ => /(_ _ Ii).
  by apply: smallest_sub; exact: sigma_algebra_measurable.
suff: forall J J' : {fset I0}%fset, (J `<=` J')%fset -> [set` J'] `<=` I ->
  forall E, (forall i, i \in J -> E i \in <<s F i >>) ->
            (forall i, i \in [set` J'] `\` [set` J] -> E i \in F i) ->
    P (\big[setI/setT]_(j <- J') E j) = \prod_(j <- J') P (E j).
  move=> /(_ K K (@fsubset_refl _ _) KI E); apply.
  - by move=> i iK; exact: EF.
  - by move=> i; rewrite setDv inE.
move=> {E EF K KI}.
apply: finSet_rect => K ih J' KJ' J'I E EsF EF.
have [K0|/fset0Pn[j jK]] := eqVneq K fset0.
  apply indeF => // i iJ'.
  by apply: EF; rewrite !inE; split => //=; rewrite K0 inE.
pose J := (K `\ j)%fset.
have jI : j \in I by apply/mem_set/J'I => /=; move/fsubsetP : KJ'; exact.
have JK : (J `<` K)%fset by rewrite fproperD1.
have JjJ' : (j |` J `<=` J')%fset by apply: fsubset_trans KJ'; rewrite fsetD1K.
have JJ' : (J `<=` J')%fset by apply: fsubset_trans JjJ'; exact: fsubsetU1.
have J'mE i : i \in J' -> d.-measurable (E i).
  move=> iJ'.
  case: indeF => + _ => /(_ i (J'I _ iJ')) Fim.
  suff: <<s F i>> (E i).
    by apply: smallest_sub => //; exact: sigma_algebra_measurable.
  apply/set_mem.
  have [iK|iK] := boolP (i \in K); first by rewrite EsF.
  have /set_mem : E i \in F i.
    by rewrite EF// !inE/=; split => //; exact/negP.
  by move/sub_sigma_algebra => /(_ setT)/mem_set.
have mmu : measurable (\big[setI/[set: T]]_(j0 <- (J' `\ j)%fset) (E j0)).
  rewrite big_seq; apply: bigsetI_measurable => i /[!inE] /andP[_ iJ'].
  exact: J'mE.
pose mu0 A := P (A `&` \big[setI/[set: T]]_(j0 <- (J' `\ j)%fset) (E j0)).
pose mu := [the {finite_measure set _ -> \bar _} of mrestr P mmu].
pose nu0 A := P A * \prod_(j0 <- (J' `\ j)%fset) P (E j0).
have nuk : (0 <= fine (\prod_(j0 <- (J' `\ j)%fset) P (E j0)))%R.
  by rewrite fine_ge0// prode_ge0.
pose nu := [the measure _ _ of mscale (NngNum nuk) P].
have nuEj A : nu A = P A * \prod_(j0 <- (J' `\ j)%fset) P (E j0).
  rewrite /nu/= /mscale muleC/= fineK// big_seq.
  rewrite prode_fin_num// => i /[!inE]/= /andP[ij iJ'].
  by rewrite fin_num_measure//; exact: J'mE.
have JJ'j : (J `<=` J' `\ j)%fset by exact: fsetSD.
have J'jI : [set` (J' `\ j)%fset] `<=` I.
  by apply: subset_trans J'I; apply/fsubsetP; exact: fsubsetDl.
have jJ' : j \in J' by move/fsubsetP : JjJ'; apply; rewrite !inE eqxx.
have Fjmunu A : (F j `|` [set set0; setT]) A -> mu A = nu A.
  move=> [FjA|[->|->]].
  - rewrite nuEj.
    pose E' i := if i == j then A else E i.
    transitivity (P (\big[setI/[set: T]]_(j <- J') E' j)).
      rewrite [in RHS](big_fsetD1 j)//= {1}/E' eqxx//; congr (P (_ `&` _)).
      rewrite !big_seq; apply: eq_bigr => i /[!inE] /andP[ij _].
      by rewrite /E' (negbTE ij).
    transitivity (\prod_(j <- J') P (E' j)); last first.
      rewrite [in LHS](big_fsetD1 j)//= {1}/E' eqxx//; congr (P _ * _).
      rewrite !big_seq; apply: eq_bigr => i /[!inE] /andP[ij _].
      by rewrite /E' (negbTE ij).
    apply: (ih _ JK _ JJ' J'I).
    + move=> i iJ.
      rewrite /E'; case: ifPn => [/eqP ->|ij].
        by rewrite inE; exact: sub_sigma_algebra.
      rewrite EsF//.
      by move/fproper_sub : JK => /fsubsetP; apply.
    + move=> i.
      rewrite ![in X in X -> _]inE /= ![in X in X -> _]inE => -[] iJ' /negP.
      rewrite negb_and negbK => /predU1P[ij|iK].
        by rewrite /E' ij eqxx inE.
      rewrite /E' ifF//; last first.
        apply/negP => /eqP ij.
        by rewrite ij jK in iK.
      by rewrite EF// !inE/=; split => //; exact/negP.
  - by rewrite !measure0.
  - rewrite /mu /= /mrestr /= nuEj setTI probability_setT mul1e.
    apply: (ih _ JK _ JJ'j J'jI).
    + move=> i iJ.
      rewrite EsF//.
      by move/fproper_sub : JK => /fsubsetP; apply.
    + move=> i.
      rewrite ![in X in X -> _]inE /= ![in X in X -> _]inE => -[].
      move=> /andP[-> iJ'] iK.
      by rewrite EF// !inE.
have sFjmunu A : <<s F j >> A -> mu A = nu A.
  move=> sFjA.
  apply: (@g_sigma_algebra_finite_measure_unique _ _ _ (F j `|` [set set0])).
  - move=> B /= [|->//].
    move: B.
    case: indeF => + _.
    by apply; exact/set_mem.
  - exact: H.
  - rewrite /mu/= /mrestr/= nuEj setTI probability_setT mul1e.
    apply: (ih _ JK _ JJ'j J'jI).
    + move=> i iJ.
      rewrite EsF//.
      by move/fproper_sub : JK => /fsubsetP; apply.
    + move=> i.
      rewrite ![in X in X -> _]inE /= ![in X in X -> _]inE => -[].
      move=> /andP[ij iJ'].
      rewrite ij/= => iK.
      by rewrite EF// !inE.
  - move=> B FjB; apply: Fjmunu.
    case: FjB => [|->//]; first by left.
    by right; left.
  - by move: sFjA; exact: sub_smallest2r.
rewrite [in LHS](big_fsetD1 j)//= [in RHS](big_fsetD1 j)//=.
have /sFjmunu : <<s F j >> (E j) by apply/set_mem; rewrite EsF.
by rewrite /mu/= /mrestr/= nuEj.
Qed.

(* pick an i from I_ k s.t. E k \in F (f k) *)
Local Definition f (K0 : choiceType) (K : {fset K0})
  (I0 : pointedType) (F : I0 -> set_system T) E I_
  (EF : forall k, k \in K -> E k \in \bigcup_(i in I_ k) F i) k :=
  if pselect (k \in K) is left kK then
     sval (cid2 (set_mem (EF _ kK)))
   else
     point.

Local Lemma f_prop (K0 : choiceType) (K : {fset K0})
    (I0 : pointedType) (F : I0 -> set_system T) E I_
    (EF : forall k, k \in K -> E k \in \bigcup_(i in I_ k) F i) k :
  k \in K -> E k \in F (f EF k).
Proof.
move=> kK; rewrite /f; case: pselect => [kK_/=|//].
by case: cid2 => // i/= ? /mem_set.
Qed.

Local Lemma f_inj (K0 : choiceType) (K K' : {fset K0})
  (K'K : [set` K'] `<=` [set` K]) (I0 : pointedType) (F : I0 -> set_system T)
  E I_ (EF : forall k, k \in K' -> E k \in \bigcup_(i in I_ k) F i)
  (KI : trivIset [set` K] I_) k1 k2 :
  k1 \in K' -> k2 \in K'-> k1 != k2 ->
  ([fset f EF k1] `&` [fset f EF k2] = fset0)%fset.
Proof.
move=> k1K' k2K' k1k2; apply/eqP; rewrite -fsubset0.
apply/fsubsetP => i /[!inE] /andP[].
rewrite /f; case: pselect => // k1K'_.
case: cid2 => // i' i'k1 Fi' /eqP ->{i}.
case: pselect => // k2K'_.
case: cid2 => // j ik2 FjEk2 /eqP/= i'j.
rewrite -{j}i'j in ik2 FjEk2 *.
move/trivIsetP : KI => /(_ _ _ (K'K _ k1K') (K'K _ k2K') k1k2).
by move/seteqP => [+ _] => /(_ i')/=; rewrite -falseE; exact.
Qed.

Local Definition g (K0 : pointedType) (K' : {fset K0})
    (I0 : Type) (I_ : K0 -> set I0) (i : I0) : K0 :=
  if pselect (exists2 k, k \in K' & i \in I_ k) is left e then
    sval (cid2 e)
  else
    point.

Local Lemma gf (K0 I0 : pointedType) (F : I0 -> set_system T)
  (K K' : {fset K0}) (K'K : [set` K'] `<=` [set` K])
  E I_ (EF : forall k, k \in K' -> E k \in \bigcup_(i in I_ k) F i)
  (KI : trivIset [set` K] (fun i => I_ i)) i : i \in K' -> g K I_ (f EF i) = i.
Proof.
move=> iK'; rewrite /f; case: pselect => // iK'_.
case: cid2 => // j jIi FjEi.
rewrite /g; case: pselect => // k'; last first.
  exfalso; apply: k'.
  by exists i => //; [exact: K'K|exact/mem_set].
case: cid2 => //= k'' k''K jIk'.
apply/eqP/negP => /negP k'i.
move/trivIsetP : KI => /(_ k'' i) /= /(_ k''K (K'K _ iK') k'i)/= /eqP.
apply/negP/set0P; exists j; split => //.
exact/set_mem.
Qed.

(**md see Achim Klenke's Probability Theory, Ch.2, sec.2.1, thm.2.13(iv) *)
Lemma mutual_independence_bigcup (K0 I0 : pointedType) (K : {fset K0})
    (I_ : K0 -> set I0) (I : set I0) (F : I0 -> set_system T) :
  trivIset [set` K] (fun i => I_ i) ->
  (forall k, k \in K -> I_ k `<=` I) ->
  mutual_independence P I F ->
  mutual_independence P [set` K] (fun k => \bigcup_(i in I_ k) F i).
Proof.
move=> KI I_I PIF.
split=> [i Ki A [j ij FjA]|K' K'K E EF].
  by case: PIF => + _ => /(_ j); apply => //; exact: (I_I _ Ki).
case: PIF => Fm PIF.
pose f' := f EF.
pose g' := g K I_.
pose J' := (\bigcup_(k <- K') [fset f' k])%fset.
pose E' := E \o g'.
suff: P (\big[setI/[set: T]]_(j <- J') E' j) = \prod_(j <- J') P (E' j).
  move=> suf.
  transitivity (P (\big[setI/[set: T]]_(j <- J') E' j)).
    congr (P _).
    apply/seteqP; split=> [t|].
      rewrite -!bigcap_fset => L j => /bigfcupP[k] /[!andbT] kK'.
      rewrite !inE => /eqP ->{j}.
      apply: L => //=.
      by rewrite /g' /f' gf.
    move=> t.
    rewrite -!bigcap_fset => L j/= jK'.
    have /= := L (f' j).
    rewrite /E' /g' /f'/= gf//.
    by apply; apply/bigfcupP; exists j;[rewrite jK'|rewrite inE].
  rewrite suf partition_disjoint_bigfcup//=.
    rewrite [LHS]big_seq [RHS]big_seq; apply: eq_big => // k kK'.
    by rewrite big_seq_fset1 /E' /g' /f' /= gf.
  move=> k1 k2 k1K' k2K' k1k2 /=.
  by rewrite -fsetI_eq0 -fsubset0 (f_inj K'K).
apply: PIF.
- move=> i/= /bigfcupP[k] /[!andbT] kK' /[!inE] /eqP ->.
  apply: (I_I k) => /=; first exact: K'K.
  by rewrite /f' /f; case: pselect => // kK'_; case: cid2.
- move=> i /bigfcupP[k'] /[!andbT] k'K /[!inE] /eqP ->{i}.
  by rewrite /E' /g' /f'/= gf//; exact/set_mem/f_prop.
Qed.

End mutual_independence_properties.

(* NB: g_sigma_algebra_preimage is in measure.v *)
Section g_sigma_algebra_preimage_comp.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  {d3} {T3 : measurableType d3}.

Lemma g_sigma_algebra_preimage_comp (X : {mfun T1 >-> T2}) (f : T2 -> T3) :
  measurable_fun setT f ->
  g_sigma_algebra_preimage (f \o X)%R `<=` g_sigma_algebra_preimage X.
Proof. exact: preimage_set_system_compS. Qed.
End g_sigma_algebra_preimage_comp.
Arguments g_sigma_algebra_preimage_comp {d1 T1 d2 T2 d3 T3 X} f.

Section g_sigma_algebra_preimage_lemmas.
Context d {T : measurableType d} {R : realType}.

Lemma g_sigma_algebra_preimage_funrpos (X : {mfun T >-> R}) :
  g_sigma_algebra_preimage X^\+%R `<=` d.-measurable.
Proof.
by move=> A/= -[B mB] <-; have := measurable_funrpos (measurable_funP X); exact.
Qed.

Lemma g_sigma_algebra_preimage_funrneg (X : {mfun T >-> R}) :
  g_sigma_algebra_preimage X^\-%R `<=` d.-measurable.
Proof.
by move=> A/= -[B mB] <-; have := measurable_funrneg (measurable_funP X); exact.
Qed.

End g_sigma_algebra_preimage_lemmas.

Section independent_RVs.
Context {R : realType} d (T : measurableType d).
Context {I0 : choiceType}.
Context {d' : I0 -> _} (T' : forall i : I0, measurableType (d' i)).
Variable P : probability T R.

Definition independent_RVs (I : set I0)
  (X : forall i : I0, {RV P >-> T' i}) : Prop :=
  mutual_independence P I (fun i => g_sigma_algebra_preimage (X i)).

Definition kwise_independent_RV (I : set I0)
  (X : forall i : I0, {RV P >-> R}) k : Prop :=
  kwise_independence P I (fun i => g_sigma_algebra_preimage (X i)) k.

End independent_RVs.

Notation "I .-independent X" := (independent_RVs I X).

Section independent_RVs2.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.

Definition independent_RVs2 (X Y : {RV P >-> T'}) :=
  [set: bool].-independent (fun b => if b then Y else X).

End independent_RVs2.

Section independent_RVs_comp.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs_comp (I0 : choiceType)
    (I : set I0) (X : I0 -> {RV P >-> T'}) (f : {mfun T' >-> R}) :
  independent_RVs I X -> independent_RVs I (fun i => [the {RV P >-> R} of f \o X i]).
Proof.
move=> PIX; split.
- move=> i Ii.
  rewrite /g_sigma_algebra_preimage/= /preimage_set_system/= => _ [A mA <-].
  by rewrite setTI; exact/measurable_sfunP.
- move=> J JI E/= JEfX; apply PIX => // j jJ.
  by have := JEfX _ jJ; rewrite !inE; exact: g_sigma_algebra_preimage_comp.
Qed.

End independent_RVs_comp.

Section independent_RVs_scale.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs_scale (I0 : choiceType)
    (I : set I0) (X : I0 -> {RV P >-> R}) k :
  independent_RVs I X -> independent_RVs I (fun i => k \o* X i : {RV P >-> R}).
Proof.
move=> PIX; split.
- move=> i Ii.
  rewrite /g_sigma_algebra_preimage/= /preimage_set_system/= => _ [A mA <-].
  by rewrite setTI; exact/measurable_sfunP.
- move=> J JI E/= JEfX; apply PIX => // j jJ.
  have := JEfX _ jJ; rewrite !inE.
  rewrite mulr_funEcomp.
  apply: g_sigma_algebra_preimage_comp.
  exact: measurable_funM.
Qed.

End independent_RVs_scale.

Section independent_RVs_lemmas.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs2_comp (X Y : {RV P >-> R}) (f g : {mfun R >-> R}) :
  independent_RVs2 X Y -> independent_RVs2 (f \o X : {RV P >-> R}) (g \o Y).
Proof.
move=> indeXY; split => /=.
- move=> [] _ /= A.
  + by rewrite /g_sigma_algebra_preimage/= /preimage_set_system/= => -[B mB <-];
      exact/measurableT_comp.
  + by rewrite /g_sigma_algebra_preimage/= /preimage_set_system/= => -[B mB <-];
      exact/measurableT_comp.
- move=> J _ E JE.
  apply indeXY => //= i iJ; have := JE _ iJ.
  by move: i {iJ} =>[|]//=; rewrite !inE => Eg;
    exact: g_sigma_algebra_preimage_comp Eg.
Qed.

Lemma independent_RVs2_funrposneg (X Y : {RV P >-> R}) :
  independent_RVs2 X Y -> @independent_RVs2 _ _ _ _ _ P X^\+ Y^\-.
Proof.
move=> indeXY; split=> [[|]/= _|J J2 E JE].
- exact: g_sigma_algebra_preimage_funrneg.
- exact: g_sigma_algebra_preimage_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr x 0)%R) => //.
    exact: measurable_funrpos.
Qed.

Lemma independent_RVs2_funrnegpos (X Y : {RV P >-> R}) :
  independent_RVs2 X Y -> @independent_RVs2 _ _ _ _ _ P X^\- Y^\+.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrpos.
- exact: g_sigma_algebra_preimage_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrnegneg (X Y : {RV P >-> R}) :
  independent_RVs2 X Y -> @independent_RVs2 _ _ _ _ _ P X^\- Y^\-.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrneg.
- exact: g_sigma_algebra_preimage_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrpospos (X Y : {RV P >-> R}) :
  independent_RVs2 X Y -> @independent_RVs2 _ _ _ _ _ P X^\+ Y^\+.
Proof.
move=> indeXY; split=> [/= [|]//= _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrpos.
- exact: g_sigma_algebra_preimage_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (@g_sigma_algebra_preimage_comp _ _ _ R _ R _ (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
Qed.

End independent_RVs_lemmas.

Local Open Scope ereal_scope.
(**md see Achim Klenke's Probability Theory, Ch.2, remark 2.15 *)
Lemma independence_RVsP {R : realType} d (T : measurableType d)
    {I0 : choiceType} {d'} (T' : measurableType d') (P : probability T R)
    (I : set I0) (X : I0 -> {mfun T >-> T'}) :
  independent_RVs (P := P) I X <->
  forall J : {fset I0}, [set` J] `<=` I ->
    forall A : I0  -> set T', (forall j, I j -> A j \in measurable) ->
      P (\big[setI/setT]_(j <- J) (X j @^-1` A j))
      = \prod_(j <- J) P (X j @^-1` A j).
Proof.
split.
  move=> [H1 +] J JI A IA.
  apply => // j jJ /=.
  rewrite inE/=.
  exists (A j).
    exact/set_mem/IA/JI.
  by rewrite setTI.
move=> H; split.
  move=> j Ij _ [B mB] <-.
  rewrite setTI.
  exact: measurable_sfunP.
move=> J JI E JE.
pose A : I0 -> set T' := fun i => match pselect (i \in J) with
  left H => sval (cid2 (set_mem (JE i H))) | right _ => setT end.
have H1 (j : I0) : I j -> A j \in d'.-measurable.
  move=> Ij.
  rewrite /A.
  case: pselect => [|]; last by rewrite inE.
  move=> jJ.
  rewrite inE.
  by case: cid2.
have := H _ JI A H1 => {}H.
apply: eq_trans.
  apply: eq_trans; last exact: H.
  congr (P _).
  rewrite big_seq [RHS]big_seq.
  apply: eq_bigr => j jJ.
  rewrite /A.
  case: pselect; last by [].
  move=> jJ'.
  case: cid2 => //= ? ?.
  by rewrite setTI.
rewrite big_seq [RHS]big_seq.
apply: eq_bigr => j jJ.
rewrite /A.
case: pselect; last by [].
move=> jJ'.
case: cid2 => //= ?.
by rewrite setTI => ? ->.
Qed.

Section independent_generators.
Context {R : realType} d (T : measurableType d).
Context {I0 : choiceType}.
Context {d' : I0 -> _} (T' : forall i : I0, measurableType (d' i)).
Variable P : probability T R.

(**md see Achim Klenke's Probability Theory, Ch.2, sec.2.1, thm.2.16 *)
Theorem independent_generators (I : set I0) (F : forall i : I0, set_system (T' i))
    (X : forall i, {RV P >-> T' i}) :
  (forall i, i \in I -> setI_closed (F i)) ->
  (forall i, i \in I -> F i `<=` @measurable _ (T' i)) ->
  (forall i, i \in I -> @measurable _ (T' i) = <<s F i>>) ->
  mutual_independence P I (fun i => preimage_set_system setT (X i) (F i)) ->
  independent_RVs I X.
Proof.
move=> IF FA AsF indeX1.
have closed_preimage i : I i -> setI_closed (preimage_set_system setT (X i) (F i)).
  move=> Ii A B [A' FiA']; rewrite setTI => <-{A}.
  move=> [B' FiB']; rewrite setTI => <-{B}.
  rewrite /preimage_set_system/=; exists (A' `&` B').
  apply: IF => //.
  - exact/mem_set.
  - by rewrite setTI.
have gen_preimage i : I i ->
    <<s preimage_set_system setT (X i) (F i) >> = g_sigma_algebra_preimage (X i).
  move=> Ii.
  rewrite /g_sigma_algebra_preimage AsF; last exact/mem_set.
  by rewrite -g_sigma_preimageE.
rewrite /independent_RVs.
suff: mutual_independence P I (fun i => <<s preimage_set_system setT (X i) (F i) >>).
  exact: eq_mutual_independence.
apply: (mutual_independence_finite_g_sigma _ _).1.
- by move=> i Ii; apply: setI_closed_set0; exact/closed_preimage/set_mem.
- split => [i Ii A [A' mA'] <-{A}|J JI E EF].
    by apply/measurable_funP => //; apply: FA => //; exact/mem_set.
  by apply indeX1.
Qed.

End independent_generators.

Definition preimage_classes I0 (I : set I0) (d_ : forall i : I, measure_display)
    (T_ : forall k : I, semiRingOfSetsType (d_ k)) (T : Type)
    (f_ : forall k : I, T -> T_ k) :=
  <<s \bigcup_(k : I) preimage_set_system setT (f_ k) measurable >>.
Arguments preimage_classes {I0} I d_ T_ {T} f_.

Lemma measurable_prod d [T : measurableType d] [R : realType] [D : set T] [I : eqType]
    (s : seq I) [h : I -> T -> R] :
  (forall i, i \in s -> measurable_fun D (h i)) ->
  measurable_fun D (fun x => (\prod_(i <- s) h i x)%R).
Proof.
elim: s => [mh|x y ih mh].
  under eq_fun do rewrite big_nil//=.
  exact: measurable_cst.
under eq_fun do rewrite big_cons//=.
apply: measurable_funM => //.
  apply: mh.
  by rewrite mem_head.
apply: ih => n ny.
apply: mh.
by rewrite inE orbC ny.
Qed.

Section pairRV.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  (P : probability T R).

Definition pairRV (X Y : {RV P >-> T'}) : T * T -> T' * T' :=
  (fun x => (X x.1, Y x.2)).

Lemma pairM (X Y : {RV P >-> T'}) : measurable_fun setT (pairRV X Y).
Proof.
rewrite /pairRV.
apply/prod_measurable_funP; split => //=.
  rewrite (_ : (fst \o (fun x : T * T => (X x.1, Y x.2))) = (fun x => X x.1))//.
  by apply/measurableT_comp => //=.
rewrite (_ : (snd \o (fun x : T * T => (X x.1, Y x.2))) = (fun x => Y x.2))//.
by apply/measurableT_comp => //=.
Qed.

HB.instance Definition _ (X Y : {RV P >-> T'}) :=
  @isMeasurableFun.Build _ _ _ _ (pairRV X Y) (pairM X Y).

End pairRV.

Section product_expectation.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ereal_scope.

Let mu := @lebesgue_measure R.

Let mprod_m (X Y : {RV P >-> R}) (A1 : set R) (A2 : set R) :
  measurable A1 -> measurable A2 ->
  (distribution P X \x distribution P Y) (A1 `*` A2) =
  ((distribution P X) A1 * (distribution P Y) A2)%E.
Proof.
move=> mA1 mA2.
etransitivity.
  by apply: product_measure1E.
rewrite /=.
done.
Qed.

Lemma tmp0 (X Y : {RV P >-> R}) (B1 B2 : set R) :
  measurable B1 -> measurable B2 ->
  independent_RVs2 X Y ->
  P (X @^-1` B1 `&` Y @^-1` B2) = P (X @^-1` B1) * P (Y @^-1` B2).
Proof.
move=> mB1 mB2.
rewrite /independent_RVs2 /independent_RVs /mutual_independence /= => -[_].
move/(_ [fset false; true]%fset (@subsetT _ _)
  (fun b => if b then Y @^-1` B2 else X @^-1` B1)).
rewrite !big_fsetU1 ?inE//= !big_seq_fset1/=.
apply => -[|] /= _; rewrite !inE; rewrite /g_sigma_algebra_preimage.
by exists B2 => //; rewrite setTI.
by exists B1 => //; rewrite setTI.
Qed.

Lemma tmp1 (X Y : {RV P >-> R}) (B1 B2 : set R) :
  measurable B1 -> measurable B2 ->
  independent_RVs2 X Y ->
  P (X @^-1` B1 `&` Y @^-1` B2) = (P \x P) (pairRV X Y @^-1` (B1 `*` B2)).
Proof.
move=> mB1 mB2 XY.
rewrite (_ : ((fun x : T * T => (X x.1, Y x.2)) @^-1` (B1 `*` B2)) =
             (X @^-1` B1) `*` (Y @^-1` B2)); last first.
  by apply/seteqP; split => [[x1 x2]|[x1 x2]]//.
rewrite product_measure1E; last 2 first.
  rewrite -[_ @^-1` _]setTI.
  by apply: (measurable_funP X).
  rewrite -[_ @^-1` _]setTI.
  by apply: (measurable_funP Y).
by rewrite tmp0//.
Qed.

Let phi (x : R * R) := (x.1 * x.2)%R.
Let mphi : measurable_fun setT phi.
Proof.
rewrite /= /phi.
by apply: measurable_funM.
Qed.

Lemma PP : (P \x P) setT = 1.
Proof.
rewrite /product_measure1 /=.
rewrite /xsection/=.
under eq_integral.
  move=> t _.
  rewrite (_ : [set y | (t, y) \in [set: T * T]] = setT); last first.
    apply/seteqP; split => [x|x]// _ /=.
    by rewrite in_setT.
  rewrite probability_setT.
  over.
rewrite integral_cst // mul1e.
apply: probability_setT.
Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R (P \x P) PP.

Lemma integrable_expectationM (X Y : {RV P >-> R}) :
  independent_RVs2 X Y ->
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  'E_(P \x P) [(fun x => `|X x.1 * Y x.2|)%R] < +oo.
Proof.
move=> indeXY iX iY.
rewrite unlock.
rewrite [ltLHS](_ : _ =
    \int[distribution (P \x P) (pairRV X Y)%R]_x `|x.1 * x.2|%:E); last first.
  rewrite ge0_integral_distribution//=; last first.
    apply/measurable_EFinP => //=.
    by apply/measurableT_comp => //=.
rewrite [ltLHS](_ : _ =
    \int[distribution P X \x distribution P Y]_x `|x.1 * x.2|%:E); last first.
  apply: eq_measure_integral => // A mA _.
  apply/esym.
  apply: product_measure_unique => //= A1 A2 mA1 mA2.
  rewrite /pushforward/=.
  rewrite -tmp1//.
  by rewrite tmp0//.
rewrite fubini_tonelli1//=; last first.
  by apply/measurable_EFinP => /=; apply/measurableT_comp => //=.
rewrite /fubini_F/= -/mu.
rewrite [ltLHS](_ : _ = \int[distribution P X]_x `|x|%:E *
                        \int[distribution P Y]_y `|y|%:E); last first.
  rewrite -ge0_integralZr//=; last 2 first.
    exact/measurable_EFinP.
    by apply: integral_ge0 => //.
  apply: eq_integral => x _.
  rewrite -ge0_integralZl//=.
    by under eq_integral do rewrite normrM.
  exact/measurable_EFinP.
rewrite ge0_integral_distribution//=; last exact/measurable_EFinP.
rewrite ge0_integral_distribution//=; last exact/measurable_EFinP.
rewrite lte_mul_pinfty//.
- exact: integral_ge0.
- apply: integral_fune_fin_num => //=.
  by move/integrable_abse : iX.
- apply: integral_fune_lt_pinfty => //.
  by move/integrable_abse : iY.
Qed.

End product_expectation.

Section product_expectation.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ereal_scope.

Import HBNNSimple.

Let expectationM_nnsfun (f g : {nnsfun T >-> R}) :
  (forall y y', y \in range f -> y' \in range g ->
    P (f @^-1` [set y] `&` g @^-1` [set y']) =
    P (f @^-1` [set y]) * P (g @^-1` [set y'])) ->
  'E_P [f \* g] = 'E_P [f] * 'E_P [g].
Proof.
move=> fg; transitivity
    ('E_P [(fun x => (\sum_(y \in range f) y * \1_(f @^-1` [set y]) x)%R)
        \* (fun x => (\sum_(y \in range g) y * \1_(g @^-1` [set y]) x)%R)]).
  by congr ('E_P [_]); apply/funext => t/=; rewrite (fimfunE f) (fimfunE g).
transitivity ('E_P [(fun x => (\sum_(y \in range f) \sum_(y' \in range g) y * y'
                    * \1_(f @^-1` [set y] `&` g @^-1` [set y']) x)%R)]).
  congr ('E_P [_]); apply/funext => t/=.
  rewrite mulrC; rewrite fsbig_distrr//=. (* TODO: lemma fsbig_distrl *)
  apply: eq_fsbigr => y yf; rewrite mulrC; rewrite fsbig_distrr//=.
  by apply: eq_fsbigr => y' y'g; rewrite indicI mulrCA !mulrA (mulrC y').
rewrite unlock.
under eq_integral do rewrite -fsumEFin//.
transitivity (\sum_(y \in range f) (\sum_(y' \in range g)
  ((y * y')%:E * \int[P]_w (\1_(f @^-1` [set y] `&` g @^-1` [set y']) w)%:E))).
  rewrite ge0_integral_fsum//=; last 2 first.
  - move=> r; under eq_fun do rewrite -fsumEFin//.
    apply: emeasurable_fsum => // s.
    apply/measurable_EFinP/measurable_funM => //.
    exact/measurable_indic/measurableI.
  - move=> r t _; rewrite lee_fin sumr_ge0 // => s _; rewrite -lee_fin.
    by rewrite indicI/= indicE -mulrACA EFinM mule_ge0// nnfun_muleindic_ge0.
  apply: eq_fsbigr => y yf.
  under eq_integral do rewrite -fsumEFin//.
  rewrite ge0_integral_fsum//=; last 2 first.
  - move=> r; apply/measurable_EFinP; apply: measurable_funM => //.
    exact/measurable_indic/measurableI.
  - move=> r t _.
    by rewrite indicI/= indicE -mulrACA EFinM mule_ge0// nnfun_muleindic_ge0.
  apply: eq_fsbigr => y' y'g.
  under eq_integral do rewrite EFinM.
  by rewrite integralZl//; exact/integrable_indic/measurableI.
transitivity (\sum_(y \in range f) (\sum_(y' \in range g)
  ((y * y')%:E * (\int[P]_w (\1_(f @^-1` [set y]) w)%:E *
                  \int[P]_w (\1_(g @^-1` [set y']) w)%:E)))).
  apply: eq_fsbigr => y fy; apply: eq_fsbigr => y' gy'; congr *%E.
  transitivity ('E_P[\1_(f @^-1` [set y] `&` g @^-1` [set y'])]).
    by rewrite unlock.
  transitivity ('E_P[\1_(f @^-1` [set y])] * 'E_P[\1_(g @^-1` [set y'])]);
    last by rewrite unlock.
  rewrite expectation_indic//; last exact: measurableI.
  by rewrite !expectation_indic// fg.
transitivity (
    (\sum_(y \in range f) (y%:E * (\int[P]_w (\1_(f @^-1` [set y]) w)%:E))) *
    (\sum_(y' \in range g) (y'%:E * \int[P]_w (\1_(g @^-1` [set y']) w)%:E))).
  transitivity (\sum_(y \in range f) (\sum_(y' \in range g)
      (y'%:E * \int[P]_w (\1_(g @^-1` [set y']) w)%:E)%E)%R *
        (y%:E * \int[P]_w (\1_(f @^-1` [set y]) w)%:E)%E%R); last first.
    rewrite !fsbig_finite//= ge0_sume_distrl//; last first.
      move=> r _; rewrite -integralZl//; last exact: integrable_indic.
      by apply: integral_ge0 => t _; rewrite nnfun_muleindic_ge0.
    by apply: eq_bigr => r _; rewrite muleC.
  apply: eq_fsbigr => y fy.
  rewrite !fsbig_finite//= ge0_sume_distrl//; last first.
    move=> r _; rewrite -integralZl//; last exact: integrable_indic.
    by apply: integral_ge0 => t _; rewrite nnfun_muleindic_ge0.
  apply: eq_bigr => r _; rewrite (mulrC y) EFinM.
  by rewrite [X in _ * X]muleC muleACA.
suff: forall h : {nnsfun T >-> R},
    (\sum_(y \in range h) (y%:E * \int[P]_w (\1_(h @^-1` [set y]) w)%:E)%E)%R
    = \int[P]_w (h w)%:E.
  by move=> suf; congr *%E; rewrite suf.
move=> h.
apply/esym.
under eq_integral do rewrite (fimfunE h).
under eq_integral do rewrite -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
- by move=> r; exact/measurable_EFinP/measurable_funM.
- by move=> r t _; rewrite lee_fin -lee_fin nnfun_muleindic_ge0.
by apply: eq_fsbigr => y fy; rewrite -integralZl//; exact/integrable_indic.
Qed.

Lemma expectationM_ge0 (X Y : {RV P >-> R}) :
  independent_RVs2 X Y ->
  'E_P[X] *? 'E_P[Y] ->
  (forall t, 0 <= X t)%R -> (forall t, 0 <= Y t)%R ->
  'E_P [X * Y] = 'E_P [X] * 'E_P [Y].
Proof.
move=> indeXY defXY X0 Y0.
have mX : measurable_fun setT (EFin \o X) by exact/measurable_EFinP.
have mY : measurable_fun setT (EFin \o Y) by exact/measurable_EFinP.
pose X_ := nnsfun_approx measurableT mX.
pose Y_ := nnsfun_approx measurableT mY.
have EXY : 'E_P[X_ n \* Y_ n] @[n --> \oo] --> 'E_P [X * Y].
  rewrite unlock; have -> : \int[P]_w ((X * Y) w)%:E =
      \int[P]_x limn (fun n => (EFin \o (X_ n \* Y_ n)%R) x).
    apply: eq_integral => t _; apply/esym/cvg_lim => //=.
    rewrite fctE EFinM; under eq_fun do rewrite EFinM.
    by apply: cvgeM; [rewrite mule_def_fin//|
      apply: cvg_nnsfun_approx => //= x _; rewrite lee_fin..].
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP; exact: measurable_funM.
  - by move=> n t _; rewrite lee_fin.
  - move=> t _ m n mn.
    by rewrite lee_fin/= ler_pM//; exact/lefP/nd_nnsfun_approx.
have EX : 'E_P[X_ n] @[n --> \oo] --> 'E_P [X].
  rewrite unlock.
  have -> : \int[P]_w (X w)%:E = \int[P]_x limn (fun n => (EFin \o X_ n) x).
    by apply: eq_integral => t _; apply/esym/cvg_lim => //=;
      apply: cvg_nnsfun_approx => // x _; rewrite lee_fin.
 apply: cvg_monotone_convergence => //.
  - by move=> n; exact/measurable_EFinP.
  - by move=> n t _; rewrite lee_fin.
  - by move=> t _ m n mn; rewrite lee_fin/=; exact/lefP/nd_nnsfun_approx.
have EY : 'E_P[Y_ n] @[n --> \oo] --> 'E_P [Y].
  rewrite unlock.
  have -> : \int[P]_w (Y w)%:E = \int[P]_x limn (fun n => (EFin \o Y_ n) x).
    by apply: eq_integral => t _; apply/esym/cvg_lim => //=;
      apply: cvg_nnsfun_approx => // x _; rewrite lee_fin.
 apply: cvg_monotone_convergence => //.
  - by move=> n; exact/measurable_EFinP.
  - by move=> n t _; rewrite lee_fin.
  - by move=> t _ m n mn; rewrite lee_fin/=; exact/lefP/nd_nnsfun_approx.
have {EX EY}EXY' : 'E_P[X_ n] * 'E_P[Y_ n] @[n --> \oo] --> 'E_P[X] * 'E_P[Y].
  apply: cvgeM => //.
suff : forall n, 'E_P[X_ n \* Y_ n] = 'E_P[X_ n] * 'E_P[Y_ n].
  by move=> suf; apply: (cvg_unique _ EXY) => //=; under eq_fun do rewrite suf.
move=> n; apply: expectationM_nnsfun => x y xX_ yY_.
suff : P (\big[setI/setT]_(j <- [fset false; true]%fset)
    [eta fun=> set0 with 0%N |-> X_ n @^-1` [set x],
                       1%N |-> Y_ n @^-1` [set y]] j) =
   \prod_(j <- [fset false; true]%fset)
      P ([eta fun=> set0 with 0%N |-> X_ n @^-1` [set x],
                            1%N |-> Y_ n @^-1` [set y]] j).
  by rewrite !big_fsetU1/= ?inE//= !big_seq_fset1/=.
move: indeXY => [/= _]; apply => // i.
pose AX := dyadic_approx setT (EFin \o X).
pose AY := dyadic_approx setT (EFin \o Y).
pose BX := integer_approx setT (EFin \o X).
pose BY := integer_approx setT (EFin \o Y).
have mA (Z : {RV P >-> R}) m k : (k < m * 2 ^ m)%N ->
    g_sigma_algebra_preimage Z (dyadic_approx setT (EFin \o Z) m k).
  move=> mk; rewrite /g_sigma_algebra_preimage /dyadic_approx mk setTI.
  rewrite /preimage_set_system/=; exists [set` dyadic_itv R m k] => //.
  rewrite setTI/=; apply/seteqP; split => z/=.
    by rewrite inE/= => Zz; exists (Z z).
  by rewrite inE/= => -[r rmk] [<-].
have mB (Z : {RV P >-> R}) k :
    g_sigma_algebra_preimage Z (integer_approx setT (EFin \o Z) k).
  rewrite /g_sigma_algebra_preimage /integer_approx setTI /preimage_set_system/=.
  by exists `[k%:R, +oo[%classic => //; rewrite setTI preimage_itvcy.
have m1A (Z : {RV P >-> R}) : forall k, (k < n * 2 ^ n)%N ->
    measurable_fun setT
    (\1_(dyadic_approx setT (EFin \o Z) n k) : g_sigma_algebra_preimageType Z -> R).
  move=> k kn.
  exact/(@measurable_indicP _ (g_sigma_algebra_preimageType Z))/mA.
rewrite !inE => /orP[|]/eqP->{i} //=.
  have : @measurable_fun _ _ (g_sigma_algebra_preimageType X) _ setT (X_ n).
    rewrite nnsfun_approxE//.
    apply: measurable_funD => //=.
      apply: measurable_sum => //= k'; apply: measurable_funM => //.
      by apply: measurable_indic; exact: mA.
    apply: measurable_funM => //.
    by apply: measurable_indic; exact: mB.
  rewrite /measurable_fun => /(_ measurableT _ (measurable_set1 x)).
  by rewrite setTI.
have : @measurable_fun _ _ (g_sigma_algebra_preimageType Y) _ setT (Y_ n).
  rewrite nnsfun_approxE//.
  apply: measurable_funD => //=.
    apply: measurable_sum => //= k'; apply: measurable_funM => //.
    by apply: measurable_indic; exact: mA.
  apply: measurable_funM => //.
  by apply: measurable_indic; exact: mB.
move=> /(_ measurableT [set y] (measurable_set1 y)).
by rewrite setTI.
Qed.

Lemma integrable_expectationM000 (X Y : {RV P >-> R}) :
  independent_RVs2 X Y ->
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  `|'E_P [X * Y]| < +oo.
Proof.
move=> indeXY iX iY.
apply: (@le_lt_trans _ _ 'E_P[(@normr _ _ \o X) * (@normr _ _ \o Y)]).
  rewrite unlock/=.
  rewrite (le_trans (le_abse_integral _ _ _))//.
    apply/measurable_EFinP/measurable_funM.
      by have /measurable_EFinP := measurable_int _ iX.
    by have /measurable_EFinP := measurable_int _ iY.
  apply: ge0_le_integral => //=.
  - by apply/measurable_EFinP; exact/measurableT_comp.
  - by move=> x _; rewrite lee_fin/= mulr_ge0/=.
  - by apply/measurable_EFinP; apply/measurable_funM; exact/measurableT_comp.
  - by move=> t _; rewrite lee_fin/= normrM.
rewrite expectationM_ge0//=.
- rewrite lte_mul_pinfty//.
  + by rewrite expectation_ge0/=.
  + rewrite expectation_fin_num//= compA//.
    exact: (integrable_abse iX).
  + by move/integrableP : iY => [_ iY]; rewrite unlock.
- exact: independent_RVs2_comp.
- apply: mule_def_fin; rewrite unlock integral_fune_fin_num//.
  + exact: (integrable_abse iX).
  + exact: (integrable_abse iY).
Qed.

Lemma independent_integrableM (X Y : {RV P >-> R}) :
  independent_RVs2 X Y ->
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  P.-integrable setT (EFin \o (X \* Y)%R).
Proof.
move=> indeXY iX iY.
apply/integrableP; split; first exact/measurable_EFinP/measurable_funM.
have := integrable_expectationM000 indeXY iX iY.
rewrite unlock => /abse_integralP; apply => //.
exact/measurable_EFinP/measurable_funM.
Qed.

(* TODO: rename to expectationM when deprecation is removed  *)
Lemma expectation_mul (X Y : {RV P >-> R}) :
  independent_RVs2 X Y ->
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  'E_P [X * Y] = 'E_P [X] * 'E_P [Y].
Proof.
move=> XY iX iY.
transitivity ('E_P[(X^\+ - X^\-) * (Y^\+ - Y^\-)]).
  congr ('E_P[_]).
  apply/funext => /=t.
  by rewrite [in LHS](funrposneg X)/= [in LHS](funrposneg Y).
have ? : P.-integrable [set: T] (EFin \o X^\-%R).
  by rewrite -funerneg; exact/integrable_funeneg.
have ? : P.-integrable [set: T] (EFin \o X^\+%R).
  by rewrite -funerpos; exact/integrable_funepos.
have ? : P.-integrable [set: T] (EFin \o Y^\+%R).
  by rewrite -funerpos; exact/integrable_funepos.
have ? : P.-integrable [set: T] (EFin \o Y^\-%R).
  by rewrite -funerneg; exact/integrable_funeneg.
have ? : P.-integrable [set: T] (EFin \o (X^\+ \* Y^\+)%R).
  by apply: independent_integrableM => //=; exact: independent_RVs2_funrpospos.
have ? : P.-integrable [set: T] (EFin \o (X^\- \* Y^\+)%R).
  by apply: independent_integrableM => //=; exact: independent_RVs2_funrnegpos.
have ? : P.-integrable [set: T] (EFin \o (X^\+ \* Y^\-)%R).
  by apply: independent_integrableM => //=; exact: independent_RVs2_funrposneg.
have ? : P.-integrable [set: T] (EFin \o (X^\- \* Y^\-)%R).
  by apply: independent_integrableM => //=; exact: independent_RVs2_funrnegneg.
transitivity ('E_P[X^\+ * Y^\+] - 'E_P[X^\- * Y^\+]
              - 'E_P[X^\+ * Y^\-] + 'E_P[X^\- * Y^\-]).
  rewrite mulrDr !mulrDl -expectationB//= -expectationB//=; last first.
    rewrite (_ : _ \o _ = EFin \o (X^\+ \* Y^\+)%R \-
                          (EFin \o (X^\- \* Y^\+)%R))//.
    exact: integrableB.
  rewrite -expectationD//=; last first.
    rewrite (_ : _ \o _ = (EFin \o (X^\+ \* Y^\+)%R)
      \- (EFin \o (X^\- \* Y^\+)%R) \- (EFin \o (X^\+ \* Y^\-)%R))//.
    by apply: integrableB => //; exact: integrableB.
  congr ('E_P[_]); apply/funext => t/=.
  by rewrite !fctE !(mulNr,mulrN,opprK,addrA)/=.
rewrite [in LHS]expectationM_ge0//=; last 2 first.
  exact: independent_RVs2_funrpospos.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]expectationM_ge0//=; last 2 first.
  exact: independent_RVs2_funrnegpos.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]expectationM_ge0//=; last 2 first.
  exact: independent_RVs2_funrposneg.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]expectationM_ge0//=; last 2 first.
  exact: independent_RVs2_funrnegneg.
  by rewrite mule_def_fin// expectation_fin_num//=.
transitivity ('E_P[X^\+ - X^\-] * 'E_P[Y^\+ - Y^\-]).
  rewrite -addeA -addeACA -muleBr; last 2 first.
    by rewrite expectation_fin_num.
    by rewrite fin_num_adde_defr// expectation_fin_num.
  rewrite -oppeB; last first.
    by rewrite fin_num_adde_defr// fin_numM// expectation_fin_num.
  rewrite -muleBr; last 2 first.
    by rewrite expectation_fin_num.
    by rewrite fin_num_adde_defr// expectation_fin_num.
  rewrite -muleBl; last 2 first.
    by rewrite fin_numB// !expectation_fin_num//.
    by rewrite fin_num_adde_defr// expectation_fin_num.
  by rewrite -expectationB//= -expectationB.
by congr *%E; congr ('E_P[_]); rewrite [RHS]funrposneg.
Qed.

Lemma prodE (s : seq nat) (X : {RV P >-> R}^nat) (t : T) :
  (\prod_(i <- s) X i t)%R = ((\prod_(j <- s) X j)%R t).
Proof.
by elim/big_ind2 : _ => //= {}X x {}Y y -> ->.
Qed.

Lemma set_cons2 (I : eqType) (x y : I) : [set` [:: x; y]] = [set x ; y].
Proof.
apply/seteqP; split => z /=; rewrite !inE.
  move=> /orP[|] /eqP ->; auto.
by move=> [|] ->; rewrite eqxx// orbT.
Qed.

Lemma independent_RVsD1 (I : {fset nat}) i0 (X : {RV P >-> R}^nat) :
  independent_RVs [set` I] X -> independent_RVs [set` (I `\ i0)%fset] X.
Proof.
move=> H.
split => [/= i|/= J JIi0 E EK].
  rewrite !inE => /andP[ii0 iI].
  by apply H.
apply H => //.
by move=> /= x /JIi0 /=; rewrite !inE => /andP[].
Qed.

Lemma independent_product_independent (I : {fset nat}) (X : {RV P >-> R}^nat) :
  independent_RVs [set` I] X ->
    forall i, i \in I -> independent_RVs2 (X i) (\prod_(j <- (I `\ i)%fset) (X j))%R.
Proof.
Abort.

End product_expectation.
