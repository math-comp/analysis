(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect interval_inference.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop interval_inference.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.
From mathcomp Require Import hoelder.

(**md**************************************************************************)
(* # Independence                                                             *)
(*                                                                            *)
(* The status of this file is experimental.                                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   independent_events I F == the events F indexed by I are independent      *)
(*  mutual_independence I F == the set systems F indexed by I are independent *)
(*      independent_RVs I X == the random variables X indexed by I are        *)
(*                             independent                                    *)
(*     independent_RVs2 X Y == the random variables X and Y are independent   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

End independent_events.

Section mutual_independence.
Context {R : realType} d {T : measurableType d} (P : probability T R)
  {I0 : choiceType}.
Local Open Scope ereal_scope.

Definition mutual_independence (I : set I0) (F : I0 -> set_system T) :=
  (forall i, I i -> F i `<=` measurable) /\
  forall J : {fset I0}, [set` J] `<=` I ->
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

End mutual_independence.

Section independence.
Context {R : realType} d {T : measurableType d} (P : probability T R).
Local Open Scope ereal_scope.

Definition independence2 (F G : set_system T) :=
  [/\ F `<=` measurable , G `<=` measurable &
      forall A B, A \in F -> B \in G -> P (A `&` B) = P A * P B].

Lemma independence2P (F G : set_system T) : independence2 F G <->
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

Section g_sigma_algebra_preimage_lemmas.
Context d {T : measurableType d} {R : realType}.

Lemma g_sigma_algebra_preimage_comp (X : {mfun T >-> R}) (f : R -> R) :
  measurable_fun setT f ->
  g_sigma_algebra_preimage (f \o X)%R `<=` g_sigma_algebra_preimage X.
Proof. exact: preimage_set_system_compS. Qed.

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
Arguments g_sigma_algebra_preimage_comp {d T R X} f.

Section independent_RVs.
Context {R : realType} d (T : measurableType d).
Context {I0 : choiceType}.
Context {d' : I0 -> _} (T' : forall i : I0, measurableType (d' i)).
Variable P : probability T R.

Definition independent_RVs (I : set I0)
  (X : forall i : I0, {mfun T >-> T' i}) : Prop :=
  mutual_independence P I (fun i => g_sigma_algebra_preimage (X i)).

End independent_RVs.

Section independent_RVs_properties.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.

Lemma independent_RVsD1 (I : {fset nat}) i0 (X : {RV P >-> T'}^nat) :
  independent_RVs P [set` I] X -> independent_RVs P [set` (I `\ i0)%fset] X.
Proof.
move=> PIX; split => [/= i|/= J JIi0 E EK].
  by rewrite !inE => /andP[ii0 iI]; exact: PIX.1.
by apply: PIX.2 => //= x /JIi0 /=; rewrite !inE => /andP[].
Qed.

End independent_RVs_properties.

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
  independent_RVs P I X.
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
    <<s preimage_set_system setT (X i) (F i) >> =
    g_sigma_algebra_preimage (X i).
  move=> Ii.
  rewrite /g_sigma_algebra_preimage AsF; last exact/mem_set.
  by rewrite -g_sigma_preimageE.
rewrite /independent_RVs.
suff: mutual_independence P I
    (fun i => <<s preimage_set_system setT (X i) (F i) >>).
  exact: eq_mutual_independence.
apply: (mutual_independence_finite_g_sigma _ _).1.
- by move=> i Ii; apply: setI_closed_set0; exact/closed_preimage/set_mem.
- split => [i Ii A [A' mA'] <-{A}|J JI E EF].
    by apply/measurable_funP => //; apply: FA => //; exact/mem_set.
  by apply indeX1.
Qed.

End independent_generators.

Section independent_RVs2.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.

Definition independent_RVs2 (X Y : {mfun T >-> T'}) :=
  independent_RVs P [set: bool] (fun b => if b then Y else X).

End independent_RVs2.

Section independent_RVs2_properties.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs2_comp (X Y : {RV P >-> R}) (f g : {mfun R >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P (f \o X) (g \o Y).
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
  independent_RVs2 P X Y -> independent_RVs2 P X^\+ Y^\-.
Proof.
move=> indeXY; split=> [[|]/= _|J J2 E JE].
- exact: g_sigma_algebra_preimage_funrneg.
- exact: g_sigma_algebra_preimage_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr x 0)%R) => //.
    exact: measurable_funrpos.
Qed.

Lemma independent_RVs2_funrnegpos (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\- Y^\+.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrpos.
- exact: g_sigma_algebra_preimage_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrnegneg (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\- Y^\-.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrneg.
- exact: g_sigma_algebra_preimage_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrpospos (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\+ Y^\+.
Proof.
move=> indeXY; split=> [/= [|]//= _ |J J2 E JE].
- exact: g_sigma_algebra_preimage_funrpos.
- exact: g_sigma_algebra_preimage_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (g_sigma_algebra_preimage_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
Qed.

End independent_RVs2_properties.

Section pairRV.
Context d d' {T : measurableType d} {T' : measurableType d'} {R : realType}
  (P : probability T R).

Definition pairRV (X Y : {RV P >-> T'}) : T * T -> T' * T' :=
  (fun x => (X x.1, Y x.2)).

Lemma measurable_pairM (X Y : {RV P >-> T'}) : measurable_fun setT (pairRV X Y).
Proof.
rewrite /pairRV.
apply/measurable_fun_pairP; split => //=.
- rewrite [X in measurable_fun _ X](_ : _ = X \o fst)//.
  exact/measurableT_comp.
- rewrite [X in measurable_fun _ X](_ : _ = Y \o snd)//.
  exact/measurableT_comp.
Qed.

HB.instance Definition _ (X Y : {RV P >-> T'}) :=
  @isMeasurableFun.Build _ _ _ _ (pairRV X Y) (measurable_pairM X Y).

End pairRV.

Section independent_RVs2_properties_realType.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ereal_scope.

Lemma independent_RVs2_setI_preimage (X Y : {mfun T >-> R}) (A1 A2 : set R) :
  measurable A1 -> measurable A2 ->
  independent_RVs2 P X Y ->
  P (X @^-1` A1 `&` Y @^-1` A2) = P (X @^-1` A1) * P (Y @^-1` A2).
Proof.
move=> mA1 mA2.
rewrite /independent_RVs2 /independent_RVs /mutual_independence /= => -[_].
move/(_ [fset false; true]%fset (@subsetT _ _)
  (fun b => if b then Y @^-1` A2 else X @^-1` A1)).
rewrite !big_fsetU1 ?inE//= !big_seq_fset1/=.
apply => -[|] /= _; rewrite !inE; rewrite /g_sigma_algebra_preimage.
by exists A2 => //; rewrite setTI.
by exists A1 => //; rewrite setTI.
Qed.

Lemma independent_RVs2_product_measure1 (X Y : {RV P >-> R}) (A1 A2 : set R) :
  measurable A1 -> measurable A2 ->
  independent_RVs2 P X Y ->
  (P \x P) (pairRV X Y @^-1` (A1 `*` A2)) = P (X @^-1` A1 `&` Y @^-1` A2).
Proof.
move=> mA1 mA2 iPXY.
rewrite (_ : (pairRV X Y @^-1` (A1 `*` A2)) =
           (X @^-1` A1) `*` (Y @^-1` A2)); last first.
  by apply/seteqP; split => [[x1 x2]|[x1 x2]].
rewrite product_measure1E.
- by rewrite independent_RVs2_setI_preimage.
- by rewrite -[_ @^-1` _]setTI; exact: (measurable_funP X).
- by rewrite -[_ @^-1` _]setTI; exact: (measurable_funP Y).
Qed.

End independent_RVs2_properties_realType.

Section product_expectation_over_product_measure.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ereal_scope.

Lemma independent_Lfun1_expectation_product_measure_lty (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
  (X : _ -> _) \in Lfun P 1 -> (Y : _ -> _) \in Lfun P 1 ->
  'E_(P \x P) [(fun x => `|X x.1 * Y x.2|)%R] < +oo.
Proof.
move=> indeXY iX iY.
rewrite unlock.
rewrite [ltLHS](_ : _ =
    \int[distribution (P \x P) (pairRV X Y)%R]_x `|x.1 * x.2|%:E); last first.
  rewrite ge0_integral_distribution//=; last first.
    apply/measurable_EFinP => //=.
    by apply/measurableT_comp => //=; exact/measurable_funM.
rewrite [ltLHS](_ : _ =
    \int[distribution P X \x distribution P Y]_x `|x.1 * x.2|%:E); last first.
  apply: eq_measure_integral => // A mA _.
  apply/esym. (* NB: don't simpl here! *)
  apply: product_measure_unique => //= A1 A2 mA1 mA2.
  by rewrite independent_RVs2_product_measure1// independent_RVs2_setI_preimage.
rewrite fubini_tonelli1//=; last first.
  apply/measurable_EFinP => /=; apply/measurableT_comp => //=.
  exact/measurable_funM.
rewrite /fubini_F/=.
rewrite [ltLHS](_ : _ = \int[distribution P X]_x `|x|%:E *
                        \int[distribution P Y]_y `|y|%:E); last first.
  rewrite -ge0_integralZr//=; last 2 first.
    exact/measurable_EFinP.
    exact: integral_ge0.
  apply: eq_integral => x _.
  rewrite -ge0_integralZl//=.
    by under eq_integral do rewrite normrM.
  exact/measurable_EFinP.
rewrite ge0_integral_distribution//=; last exact/measurable_EFinP.
rewrite ge0_integral_distribution//=; last exact/measurable_EFinP.
rewrite lte_mul_pinfty//.
- exact: integral_ge0.
- apply: integrable_fin_num => //=.
  by move/Lfun1_integrable : iX => /integrable_abse.
- apply: integrable_lty => //.
  by move/Lfun1_integrable : iY => /integrable_abse.
Qed.

End product_expectation_over_product_measure.

Section product_expectation.
Context {R : realType} d (T : measurableType d).
Variable P : probability T R.
Local Open Scope ereal_scope.

Import HBNNSimple.

Lemma expectationM_nnsfun (f g : {nnsfun T >-> R}) :
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

Lemma ge0_independent_expectationM (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
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
- have : @measurable_fun _ _ (g_sigma_algebra_preimageType X) _ setT (X_ n).
    rewrite nnsfun_approxE//.
    apply: measurable_funD => //=.
      apply: measurable_sum => //= k'; apply: measurable_funM => //.
      by apply: measurable_indic; exact: mA.
    apply: measurable_funM => //.
    by apply: measurable_indic; exact: mB.
  rewrite /measurable_fun => /(_ measurableT _ (measurable_set1 x)).
  by rewrite setTI.
- have : @measurable_fun _ _ (g_sigma_algebra_preimageType Y) _ setT (Y_ n).
    rewrite nnsfun_approxE//.
    apply: measurable_funD => //=.
      apply: measurable_sum => //= k'; apply: measurable_funM => //.
      by apply: measurable_indic; exact: mA.
    apply: measurable_funM => //.
    by apply: measurable_indic; exact: mB.
  move=> /(_ measurableT [set y] (measurable_set1 y)).
  by rewrite setTI.
Qed.

Lemma independent_Lfun1_expectationM_lty (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
  (X : _ -> _) \in Lfun P 1 -> (Y : _ -> _) \in Lfun P 1 ->
  `|'E_P [X * Y]| < +oo.
Proof.
move=> indeXY iX iY.
apply: (@le_lt_trans _ _ 'E_P[(@normr _ _ \o X) * (@normr _ _ \o Y)]).
  rewrite unlock/= (le_trans (le_abse_integral _ _ _))//.
    apply/measurable_EFinP/measurable_funM.
      by move/Lfun1_integrable : iX => /measurable_int/measurable_EFinP.
    by move/Lfun1_integrable : iY => /measurable_int/measurable_EFinP.
  apply: ge0_le_integral => //=.
  - by apply/measurable_EFinP; exact/measurableT_comp.
  - by apply/measurable_EFinP; apply/measurable_funM; exact/measurableT_comp.
  - by move=> t _; rewrite lee_fin/= normrM.
rewrite ge0_independent_expectationM//=.
- rewrite lte_mul_pinfty//.
  + by rewrite expectation_ge0/=.
  + rewrite expectation_fin_num//=.
    by move: iX => /Lfun_norm.
  + move : iY => /Lfun1_integrable/integrableP[_].
    by rewrite unlock.
- exact: independent_RVs2_comp.
- apply: mule_def_fin; rewrite unlock integrable_fin_num//.
  + by move/Lfun_norm : iX => /Lfun1_integrable.
  + by move/Lfun_norm : iY => /Lfun1_integrable.
Qed.

Lemma independent_Lfun1M (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
  (X : _ -> _) \in Lfun P 1 -> (Y : _ -> _) \in Lfun P 1 ->
  (X \* Y)%R \in Lfun P 1.
Proof.
move=> indeXY iX iY.
apply/Lfun1_integrable.
apply/integrableP; split => //.
  move/Lfun1_integrable : iX => /integrableP[iX _].
  move/Lfun1_integrable : iY => /integrableP[iY _].
  exact/measurable_EFinP/measurable_funM/measurable_EFinP.
have := independent_Lfun1_expectationM_lty indeXY iX iY.
rewrite unlock => /abse_integralP; apply => //.
exact/measurable_EFinP/measurable_funM.
Qed.

Lemma independent_expectationM (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
  (X : _ -> _) \in Lfun P 1 -> (Y : _ -> _) \in Lfun P 1 ->
  'E_P [X * Y] = 'E_P [X] * 'E_P [Y].
Proof.
move=> XY iX iY.
transitivity ('E_P[(X^\+ - X^\-) * (Y^\+ - Y^\-)]).
  by rewrite !funrposBneg.
have ? : X^\-%R \in Lfun P 1.
  apply/Lfun1_integrable; rewrite -funerneg; apply/integrable_funeneg => //.
  exact/Lfun1_integrable.
have ? : X^\-%R \in Lfun P 1.
  apply/Lfun1_integrable; rewrite -funerneg; apply/integrable_funeneg => //.
  exact/Lfun1_integrable.
have ? : X^\+%R \in Lfun P 1.
  apply/Lfun1_integrable; rewrite -funerpos; apply/integrable_funepos => //.
  exact/Lfun1_integrable.
have ? : Y^\+%R \in Lfun P 1.
  apply/Lfun1_integrable; rewrite -funerpos; apply/integrable_funepos => //.
  exact/Lfun1_integrable.
have ? : Y^\-%R \in Lfun P 1.
  apply/Lfun1_integrable; rewrite -funerneg; apply/integrable_funeneg => //.
  exact/Lfun1_integrable.
have ? : (X^\+ \* Y^\+)%R \in Lfun P 1.
  by apply: independent_Lfun1M => //=; exact: independent_RVs2_funrpospos.
have ? : (X^\- \* Y^\+)%R \in Lfun P 1.
  by apply: independent_Lfun1M => //=; exact: independent_RVs2_funrnegpos.
have ? : (X^\+ \* Y^\-)%R \in Lfun P 1.
  by apply: independent_Lfun1M => //=; exact: independent_RVs2_funrposneg.
have ? : (X^\- \* Y^\-)%R \in Lfun P 1.
  by apply: independent_Lfun1M => //=; exact: independent_RVs2_funrnegneg.
transitivity ('E_P[X^\+ * Y^\+] - 'E_P[X^\- * Y^\+]
              - 'E_P[X^\+ * Y^\-] + 'E_P[X^\- * Y^\-]).
  rewrite mulrDr !mulrDl -!expectationB//=; last by rewrite rpredB.
  rewrite -expectationD//=; last by rewrite !rpredB.
  congr ('E_P[_]); apply/funext => t/=.
  by rewrite !fctE !(mulNr,mulrN,opprK,addrA).
rewrite [in LHS]ge0_independent_expectationM//=; last 2 first.
  exact: independent_RVs2_funrpospos.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]ge0_independent_expectationM//=; last 2 first.
  exact: independent_RVs2_funrnegpos.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]ge0_independent_expectationM//=; last 2 first.
  exact: independent_RVs2_funrposneg.
  by rewrite mule_def_fin// expectation_fin_num.
rewrite [in LHS]ge0_independent_expectationM//=; last 2 first.
  exact: independent_RVs2_funrnegneg.
  by rewrite mule_def_fin// expectation_fin_num.
transitivity ('E_P[X^\+ - X^\-] * 'E_P[Y^\+ - Y^\-]).
  rewrite -addeA -addeACA -muleBr; last 2 first.
    by rewrite expectation_fin_num.
    by rewrite fin_num_adde_defr// expectation_fin_num.
  rewrite -oppeB; last first.
    by rewrite fin_num_adde_defr// fin_numM// expectation_fin_num.
  rewrite -muleBr; last 2 first.
    by rewrite expectation_fin_num.
    by rewrite fin_num_adde_defr// expectation_fin_num.
  rewrite -muleBl.
  - by rewrite -!expectationB.
  - by rewrite fin_numB// !expectation_fin_num.
  - by rewrite fin_num_adde_defr// expectation_fin_num.
by rewrite !funrposBneg.
Qed.

End product_expectation.
