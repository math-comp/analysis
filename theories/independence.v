(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal signed topology normedtype sequences.
From mathcomp Require Import esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.

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

Definition g_sigma_family (I : set I0) (F : I0 -> set_system T)
    : set_system T :=
  <<s \bigcup_(i in I) F i >>.

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

(**md see Achim Klenke's Probability Thery, Ch.2, sec.2.1, thm.2.13(i) *)
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

(**md see Achim Klenke's Probability Thery, Ch.2, sec.2.1, thm.2.13(ii) *)
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

(**md see Achim Klenke's Probability Thery, Ch.2, sec.2.1, thm.2.13(iii) *)
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

(**md see Achim Klenke's Probability Thery, Ch.2, sec.2.1, thm.2.13(iv) *)
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

Section g_sigma_algebra_mapping_lemmas.
Context d {T : measurableType d} {R : realType}.

Lemma g_sigma_algebra_mapping_comp (X : {mfun T >-> R}) (f : R -> R) :
  measurable_fun setT f ->
  g_sigma_algebra_mapping (f \o X)%R `<=` g_sigma_algebra_mapping X.
Proof. exact: preimage_class_comp. Qed.

Lemma g_sigma_algebra_mapping_funrpos (X : {mfun T >-> R}) :
  g_sigma_algebra_mapping X^\+%R `<=` d.-measurable.
Proof.
by move=> A/= -[B mB] <-; have := measurable_funrpos (measurable_funP X); exact.
Qed.

Lemma g_sigma_algebra_mapping_funrneg (X : {mfun T >-> R}) :
  g_sigma_algebra_mapping X^\-%R `<=` d.-measurable.
Proof.
by move=> A/= -[B mB] <-; have := measurable_funrneg (measurable_funP X); exact.
Qed.

End g_sigma_algebra_mapping_lemmas.
Arguments g_sigma_algebra_mapping_comp {d T R X} f.

Section independent_RVs.
Context {R : realType} d (T : measurableType d).
Context {I0 : choiceType}.
Context {d' : I0 -> _} (T' : forall i : I0, measurableType (d' i)).
Variable P : probability T R.

Definition independent_RVs (I : set I0)
  (X : forall i : I0, {mfun T >-> T' i}) : Prop :=
  mutual_independence P I (fun i => g_sigma_algebra_mapping (X i)).

End independent_RVs.

Section independent_RVs2.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.

Definition independent_RVs2 (X Y : {mfun T >-> T'}) :=
  independent_RVs P [set: bool] (fun b => if b then Y else X).

End independent_RVs2.

Section independent_generators.
Context {R : realType} d (T : measurableType d).
Context {I0 : choiceType}.
Context {d' : I0 -> _} (T' : forall i : I0, measurableType (d' i)).
Variable P : probability T R.

(**md see Achim Klenke's Probability Thery, Ch.2, sec.2.1, thm.2.16 *)
Theorem independent_generators (I : set I0) (F : forall i : I0, set_system (T' i))
    (X : forall i, {RV P >-> T' i}) :
  (forall i, i \in I -> setI_closed (F i)) ->
  (forall i, i \in I -> F i `<=` @measurable _ (T' i)) ->
  (forall i, i \in I -> @measurable _ (T' i) = <<s F i>>) ->
  mutual_independence P I (fun i => preimage_class setT (X i) (F i)) ->
  independent_RVs P I X.
Proof.
move=> IF FA AsF indeX1.
have closed_preimage i : I i -> setI_closed (preimage_class setT (X i) (F i)).
  move=> Ii A B [A' FiA']; rewrite setTI => <-{A}.
  move=> [B' FiB']; rewrite setTI => <-{B}.
  rewrite /preimage_class/=; exists (A' `&` B').
  apply: IF => //.
  - exact/mem_set.
  - by rewrite setTI.
have gen_preimage i : I i ->
    <<s preimage_class setT (X i) (F i) >> = g_sigma_algebra_mapping (X i).
  move=> Ii.
  rewrite /g_sigma_algebra_mapping AsF; last exact/mem_set.
  by rewrite -sigma_algebra_preimage_classE.
rewrite /independent_RVs.
suff: mutual_independence P I (fun i => <<s preimage_class setT (X i) (F i) >>).
  exact: eq_mutual_independence.
apply: (mutual_independence_finite_g_sigma _ _).1.
- by move=> i Ii; apply: setI_closed_set0; exact/closed_preimage/set_mem.
- split => [i Ii A [A' mA'] <-{A}|J JI E EF].
    by apply/measurable_funP => //; apply: FA => //; exact/mem_set.
  by apply indeX1.
Qed.

End independent_generators.

Section independent_RVs_lemmas.
Context {R : realType} d d' (T : measurableType d) (T' : measurableType d').
Variable P : probability T R.
Local Open Scope ring_scope.

Lemma independent_RVs2_comp (X Y : {RV P >-> R}) (f g : {mfun R >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P (f \o X) (g \o Y).
Proof.
move=> indeXY; split => /=.
- move=> [] _ /= A.
  + by rewrite /g_sigma_algebra_mapping/= /preimage_class/= => -[B mB <-];
      exact/measurableT_comp.
  + by rewrite /g_sigma_algebra_mapping/= /preimage_class/= => -[B mB <-];
      exact/measurableT_comp.
- move=> J _ E JE.
  apply indeXY => //= i iJ; have := JE _ iJ.
  by move: i {iJ} =>[|]//=; rewrite !inE => Eg;
    exact: g_sigma_algebra_mapping_comp Eg.
Qed.

Lemma independent_RVs2_funrposneg (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\+ Y^\-.
Proof.
move=> indeXY; split=> [[|]/= _|J J2 E JE].
- exact: g_sigma_algebra_mapping_funrneg.
- exact: g_sigma_algebra_mapping_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr x 0)%R) => //.
    exact: measurable_funrpos.
Qed.

Lemma independent_RVs2_funrnegpos (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\- Y^\+.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_mapping_funrpos.
- exact: g_sigma_algebra_mapping_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrnegneg (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\- Y^\-.
Proof.
move=> indeXY; split=> [/= [|]// _ |J J2 E JE].
- exact: g_sigma_algebra_mapping_funrneg.
- exact: g_sigma_algebra_mapping_funrneg.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr (- x) 0)%R).
    exact: measurable_funrneg.
Qed.

Lemma independent_RVs2_funrpospos (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y -> independent_RVs2 P X^\+ Y^\+.
Proof.
move=> indeXY; split=> [/= [|]//= _ |J J2 E JE].
- exact: g_sigma_algebra_mapping_funrpos.
- exact: g_sigma_algebra_mapping_funrpos.
- apply indeXY => //= i iJ; have := JE _ iJ.
  move/J2 : iJ; move: i => [|]// _; rewrite !inE.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
  + apply: (g_sigma_algebra_mapping_comp (fun x => maxr x 0)%R).
    exact: measurable_funrpos.
Qed.

End independent_RVs_lemmas.

Definition preimage_classes I0 (I : set I0) (d_ : forall i : I, measure_display)
    (T_ : forall k : I, semiRingOfSetsType (d_ k)) (T : Type)
    (f_ : forall k : I, T -> T_ k) :=
  <<s \bigcup_(k : I) preimage_class setT (f_ k) measurable >>.
Arguments preimage_classes {I0} I d_ T_ {T} f_.

(* composition of kernels *)

(* TODO: move *)
Lemma nneseriesD1 {R : realType} [P : pred nat] [F : nat -> \bar R] (j : nat) :
  P j ->
  (forall i, 0 <= F i)%E ->
  (\big[+%E/0%E]_(0 <= i <oo | P i) F i =
  F j + (\big[+%E/0%E]_(0 <= i <oo | P i && (i != j)) F i))%E.
Proof.
move=> Pj F0.
rewrite (@nneseries_split_cond _ F 0%N j.+1 P)// add0n.
rewrite big_mkcond/= big_nat_recr//= Pj -big_mkcond/=.
rewrite -addrA addrCA; congr +%E.
rewrite [RHS]eseries_mkcondr.
rewrite [in RHS](@nneseries_split_cond _ _ 0%N j.+1 P)//; last first.
  by move=> k Pk; case: ifPn.
rewrite add0n.
rewrite [X in _ = X + _]big_mkcond/=.
rewrite big_nat_recr//= Pj eqxx/= adde0 -big_mkcond//=.
congr +%E.
  rewrite big_seq_cond [RHS]big_seq_cond.
  apply: eq_bigr => /= i.
  rewrite mem_index_iota leq0n/= => /andP[ij Pi].
  by rewrite lt_eqF.
rewrite eseries_cond [RHS]eseries_cond.
apply: eq_eseriesr => i /andP[Pi ji].
by rewrite gt_eqF.
Qed.

Lemma nneseries_recl {R : realType} [P : pred nat] [F : nat -> \bar R] :
  P 0%N ->
  (forall i, 0 <= F i)%E ->
  (\big[+%E/0%E]_(0 <= i <oo | P i) F i =
  F 0%N + (\big[+%E/0%E]_(1 <= i <oo | P i) F i))%E.
Proof.
move=> P0 F0.
rewrite (nneseriesD1 P0)//; congr +%E.
rewrite [RHS]eseries_cond.
apply: eq_eseriesl => n.
by rewrite lt0n.
Qed.

Lemma indicC {R : realType} T (A : set T) :
  \1_(~` A) = (fun x => (~~ (x \in A))%:R) :> (_ -> R).
Proof. by apply/funext=> u/=; rewrite indicE in_setC. Qed.

Lemma indicbigcup {R : realType} T (A : (set T)^nat) (xy : T) :
  trivIset [set: nat] A ->
  (\1_(\bigcup_n A n) xy)%:E =
   \big[+%R/0]_(0 <= n <oo) (\1_(A n) xy)%:E :> \bar R.
Proof.
move=> tA.
have [Axy|Axy] := eqVneq (\1_(\bigcup_n A n) xy) (1 : R).
  move: (Axy) => /eqP.
  rewrite pnatr_eq1 eqb1 => /asboolP[i _] xyAi.
  rewrite Axy.
  apply/esym.
  rewrite (@nneseriesD1 _ _ _ i)//; last by move=> j; rewrite lee_fin.
  rewrite indicE mem_set//.
  rewrite eseries0 ?adde0// => j _/= ji.
  rewrite indicE.
  rewrite memNset// => Ajxy.
  move/trivIsetP : tA => /(_ j i Logic.I Logic.I ji).
  by apply/eqP/set0P; exists xy.
have {}Axy : \1_(\bigcup_n A n) xy = 0 :> R.
  apply/eqP.
  move: Axy.
  by rewrite pnatr_eq1 eqb1 pnatr_eq0 eqb0.
move: (Axy) => /eqP.
rewrite pnatr_eq0 eqb0 notin_setE => Axy'.
rewrite Axy eseries0// => j _ _.
rewrite indicE.
rewrite memNset// => Ajxy.
apply: Axy'.
by exists j.
Qed.
(* /TODO: move *)

(* klenke 1.82 *)
Lemma measurability_comp I0 (I : set I0) (d_ : forall i : I, measure_display)
   (T_ : forall i : I, measurableType (d_ i)) d (T : measurableType d)
   d' (T' : measurableType d')
   (X_ : forall i : I, T' -> T_ i) :
  (forall i : I, measurable_fun [set: T'] (X_ i)) ->
  @measurable _ T' = preimage_classes I d_ T_ X_ ->
  forall Y : T -> T',
    measurable_fun setT Y <-> forall i : I, measurable_fun setT (X_ i \o Y).
Proof.
move=> mX_ T'E Y.
split=> [mY i|mXY]; first exact: measurableT_comp.
set E' := \bigcup_(i : I) preimage_class setT (X_ i) (@measurable _ (T_ i)).
apply: (@measurability _ _ _ _ _ _ E'); first exact: T'E.
move=> _ [B [i _] mB] <-.
case: mB => Ai mAi <-{B}.
have := mXY i measurableT _ mAi.
by rewrite comp_preimage !setTI.
Qed.

Lemma finite_sigma_finite [d : measure_display] [T : measurableType d]
    [R : realType] [mu : {measure set T -> \bar R}] :
  fin_num_fun mu -> sigma_finite setT mu.
Proof.
move=> fmu.
apply: fin_num_fun_sigma_finite => //.
by rewrite measure0.
Qed.

Lemma finite_sfinite_measure [d : measure_display] [T : measurableType d]
  [R : realType] [mu : {measure set T -> \bar R}] :
  fin_num_fun mu -> sfinite_measure mu.
Proof.
move=> fmu.
exists (fun n => if n is O then mu else mzero).
  by case.
move=> U mU.
rewrite /mseries.
rewrite nneseries_recl//.
by rewrite eseries0 ?adde0// => -[|].
Qed.

(* lem 14.13 *)
Section measurability_prod.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).

Let di := (fun b : [set false; true] => if val b then d2 else d1).

Let T (i : [set false; true]) : measurableType (di i).
Proof.
destruct i as [b]; destruct b; [exact: T2|exact: T1].
Defined.

Let X (i : [set false; true]) : T1 * T2 -> T i.
Proof.
destruct i as [b]; destruct b; [exact: snd|exact: fst].
Defined.

Let mX (i : [set false; true]) : measurable_fun [set: T1 * T2] (X i).
Proof.
destruct i as [b]; destruct b; [exact: measurable_snd|exact: measurable_fst].
Defined.

Let preimage_class2 :
  \bigcup_k preimage_class [set: T1 * T2] (X k) (di k).-measurable =
    preimage_class [set: T1 * T2] fst d1.-measurable
    `|` preimage_class [set: T1 * T2] snd d2.-measurable.
Proof.
apply/seteqP; split => [B [x]|B/= [|]?].
- destruct x as [b].
  by destruct b => /= [_|_]; by rewrite /di/=; auto.
- have @j : [set false; true] by exists false; rewrite inE/=; left.
  by exists j.
- have @j : [set false; true] by exists true; rewrite inE/=; right.
  by exists j.
Qed.

(* PR in progress *)
Lemma xsectionE (A : set (T1 * T2)) (x : T1) :
  xsection A x = (fun y => (x, y)) @^-1` A.
Proof. by apply/seteqP; split => [y|y] /xsectionP. Qed.

(* PR in progress *)
Lemma ysectionE (A : set (T1 * T2)) (y : T2) :
  ysection A y = (fun x => (x, y)) @^-1` A.
Proof. by apply/seteqP; split => [x|x] /ysectionP. Qed.

(* PR in progress *)
Lemma measurable_xsection (A : set (T1 * T2)) (x : T1) :
  measurable A -> measurable (xsection A x).
Proof.
move=> mA; pose i (y : T2) := (x, y).
have mi : measurable_fun setT i by exact: measurable_pair1.
by rewrite xsectionE -[X in measurable X]setTI; exact: mi.
Qed.

(* PR in progress *)
Lemma measurable_ysection (A : set (T1 * T2)) (y : T2) :
  measurable A -> measurable (ysection A y).
Proof.
move=> mA; pose i (x : T1) := (x, y).
have mi : measurable_fun setT i by exact: measurable_pair2.
by rewrite ysectionE -[X in measurable X]setTI; exact: mi.
Qed.

Lemma measurability_prod2 {R : realType} (f : T1 * T2 -> \bar R) (w1 : T1) :
  measurable_fun setT f -> measurable_fun setT (fun w2 => f (w1, w2)).
Proof.
move=> mf.
(*by apply: measurableT_comp.*)
pose i (w2 : T2) := (w1, w2).
have f1 : fst \o i = cst w1 by exact/funext.
have f2 : snd \o i = id by exact/funext.
suff: measurable_fun setT i.
  exact: measurableT_comp.
apply/(@measurability_comp _ [set false; true] di T _ T2 _ (T1 * T2)%type X).
- exact: mX.
- by rewrite /preimage_classes preimage_class2.
- move=> i0.
  apply: measurableT_comp => //.
  exact: measurable_pair1.
Qed.

Lemma measurability_prod1 {R : realType} (f : T1 * T2 -> \bar R) (w2 : T2) :
  measurable_fun setT f -> measurable_fun setT (fun w1 => f (w1, w2)).
Proof.
move=> mf.
pose i (w1 : T1) := (w1, w2).
have f2 : snd \o i = cst w2 by exact/funext.
have f1 : fst \o i = id by exact/funext.
suff: measurable_fun setT i by exact: measurableT_comp.
apply/(@measurability_comp bool [set false; true] di T _ T1 _ (T1 * T2)%type X).
- exact: mX.
- by rewrite /preimage_classes preimage_class2.
- move=> i0.
  apply: measurableT_comp => //.
  exact: measurable_pair2.
Qed.

End measurability_prod.

(* klenke def 8.25 *)
HB.mixin Record isFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  finite_finite_transition_kernel : forall x, fin_num_fun (k x) }.

#[short(type=finite_transition_kernel)]
HB.structure Definition FiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ _ k & isFiniteTransitionKernel _ _ X Y R k }.

Reserved Notation "R .-ftker X ~> Y"
  (at level 42, format "R .-ftker  X  ~>  Y").
Notation "R .-ftker X ~> Y" := (finite_transition_kernel X%type Y R).

HB.mixin Record isSigmaFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  sigma_finite_finite_transition_kernel : forall x, sigma_finite setT (k x) }.

#[short(type=sigma_finite_transition_kernel)]
HB.structure Definition SigmaFiniteTransitionKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ _ k & isSigmaFiniteTransitionKernel _ _ X Y R k }.

Reserved Notation "R .-sigmaftker X ~> Y"
  (at level 42, format "R .-sigmaftker  X  ~>  Y").
Notation "R .-sigmaftker X ~> Y" := (sigma_finite_transition_kernel X%type Y R).

HB.mixin Record isMarkovKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  markov_transition_kernel : forall x, k x setT = 1%E }.

#[short(type=markov_kernel)]
HB.structure Definition MarkovKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ _ k & isMarkovKernel _ _ X Y R k }.

Reserved Notation "R .-mker X ~> Y"
  (at level 42, format "R .-mker  X  ~>  Y").
Notation "R .-mker X ~> Y" := (markov_kernel X%type Y R).

HB.mixin Record isSubMarkovKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  submarkov_transition_kernel : forall x, (k x setT <= 1)%E }.

#[short(type=submarkov_kernel)]
HB.structure Definition SubMarkovKernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k of @Kernel _ _ _ _ _ k & isSubMarkovKernel _ _ X Y R k }.

Reserved Notation "R .-submker X ~> Y"
  (at level 42, format "R .-submker  X  ~>  Y").
Notation "R .-submker X ~> Y" := (submarkov_kernel X%type Y R).

(* composition of a finite transition kernel and a function, as in def 14.20 *)
Definition kfcomp d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (R : realType) (k : R.-ftker T1 ~> T2) (f : T1 * T2 -> \bar R) : T1 -> \bar R :=
  fun x => (\int[k x]_y f (x, y))%E.

Import HBNNSimple.

(* lem 14.20 *)
Lemma measurable_kfcomp d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
    (R : realType) (k : R.-ftker T1 ~> T2)
    (f : T1 * T2 -> \bar R) : measurable_fun [set: (T1 * T2)%type] f ->
  (forall t, (0 <= f t)%E) ->
  measurable_fun [set: T1] (kfcomp k f).
Proof.
move=> mf f0.
rewrite /kfcomp.
pose I (f : T1 * T2 -> \bar R) w1 := (\int[k w1]_w2 f (w1, w2))%E.
have mf1 x : measurable_fun setT (fun z => f (x, z)).
  exact/measurability_prod2.
(* therefore If is well defined *)
pose g (A1 : set T1) (A2 : set T2) : T1 * T2 -> \bar R := EFin \o \1_(A1 `*` A2).
have IgE (A1 : set T1) (A2 : set T2) w1 : measurable A1 -> measurable A2 ->
    I (g A1 A2) w1 = ((\1_A1 w1)%:E * k w1 A2)%E.
  move=> mA1 mA2.
  rewrite /I /g/= integral_indic//; last first.
    rewrite [X in measurable X](_ : _ = xsection (A1 `*` A2) w1); last first.
      by apply/seteqP; split=> [y [A1w1 A2y]|y]; rewrite /xsection/= inE.
    apply: measurable_xsection.
    exact: measurableX.
  have [w1A1|w1A1] := boolP (w1 \in A1).
    rewrite indicE w1A1 mul1e; congr (k _ _).
    by rewrite setIT/=; apply/seteqP; split => [y []//|y]; move/set_mem: w1A1.
  rewrite indicE (negbTE w1A1) mul0e [X in k _ X = _](_ : _ = set0)//.
  by rewrite setIT/=; apply/seteqP; split => [y []//|y]; rewrite notin_setE in w1A1.
suff: measurable_fun [set: T1] (I f) by [].
pose f_ := nnsfun_approx measurableT mf.
have If_cvg w1 : I (EFin \o (f_ n)) w1 @[n --> \oo] --> I f w1.
  rewrite /I.
  pose g' := (fun n y => (EFin \o f_ n) (w1, y)).
  rewrite [X in _ --> X](_ : _ =
      (\int[k w1]_w2 (fun t => limn (g' ^~ t)) w2)%E); last first.
    apply: eq_integral => y _.
    by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP; exact: measurableT_comp.
  - by move=> n y _; rewrite /= lee_fin.
  - move=> y _ a b ab /=; rewrite lee_fin.
    by have /lefP/(_ (w1, y)) := nd_nnsfun_approx measurableT mf ab.
apply: (emeasurable_fun_cvg (fun n => I (EFin \o f_ n))).
  move=> m.
  pose D := [set A | measurable A /\ measurable_fun setT (I (EFin \o \1_A))].
  have setSD_D : setSD_closed D.
    move=> B A AB; rewrite /D/= => -[mB mIB] [mA mIA].
    have IE : (I (EFin \o \1_(B `\` A)) = I (EFin \o \1_B) \- I (EFin \o \1_A))%E.
      apply/funext => x/=.
      rewrite /I.
      pose kx : {measure set T2 -> \bar R} := k x.
      pose H1 := isFinite.Build _ _ _ _
        (@finite_finite_transition_kernel _ _ _ _ R k x).
      pose H2 := isSFinite.Build _ _ _ _
        (finite_sfinite_measure (@finite_finite_transition_kernel _ _ _ _ R k x)).
      pose H3 := isSigmaFinite.Build _ _ _ _
        (finite_sigma_finite (@finite_finite_transition_kernel _ _ _ _ R k x)).
      pose kx' := HB.pack_for (FiniteMeasure.type T2 R) (Measure.sort kx) H1 H2 H3.
      have kxE : kx = kx' by exact: eq_measure.
      rewrite (*TODO: use RintegralB when merged*) -integralB_EFin//; last 2 first.
        rewrite -/kx kxE; apply: integrable_indic => //.
        rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
        exact: measurable_xsection.
        rewrite -/kx kxE; apply: integrable_indic => //.
        rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
        exact: measurable_xsection.
      apply: eq_integral => y _/=.
      rewrite setDE indicI indicC/=.
      have [/= xyA|/= xyA] := boolP ((x, y) \in _).
        rewrite mulr0 EFinN !indicE xyA/= EFinN.
        move/set_mem : xyA => /AB /mem_set ->.
        by rewrite subee.
      by rewrite mulr1 EFinN !indicE (negbTE xyA)/= oppr0 adde0.
    split; first exact: measurableD.
    by rewrite IE; exact: emeasurable_funB.
  have lambda_D : lambda_system setT D.
    split => //.
    - rewrite /D/= indicT/=; split => //.
      rewrite [X in measurable_fun _ X](_ : _ = (fun x => k x setT)); last first.
        rewrite /I; apply/funext => x/=.
        by rewrite integral_cst// mul1e.
      exact: measurable_kernel.
    - suff: D = [set A | (d1, d2).-prod.-measurable A /\
             measurable_fun [set: T1] ((fun C x => k x (xsection C x)) A)].
        by move=> ->; exact: xsection_ndseq_closed.
      apply/seteqP; split=> [/= A [mA /= mIA]|/= A [/= mA mIA]].
        split => //.
          rewrite [X in measurable_fun _ X](_ : _ = I (EFin \o \1_A))//.
          apply/funext => x.
          rewrite /I/= integral_indic// ?setIT//.
          by rewrite -[X in _ = k x X]/(_ @^-1` _) -xsectionE.
        rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
        exact: measurable_xsection.
      split => //.
      rewrite /I [X in measurable_fun _ X](_ : _ = (fun x => k x (xsection A x)))//.
      apply/funext => x.
      rewrite integral_indic//; last first.
        rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
        exact: measurable_xsection.
      by rewrite setIT xsectionE.
  rewrite /= in lambda_D.
  have DE : D = @measurable _ (T1 * T2)%type.
    (* NB: setI_closed_g_dynkin_g_sigma_algebra is not exactly Dynkin' pi-lambda theorem
       because it should not be closed under setI but contain a generator that is closed
       under setI *)
    apply/seteqP; split => [/= A []//|].
    rewrite measurable_prod_measurableType. (* IMP *)
    apply: lambda_system_subset => //.
      (* replay of a proof in Section xsection *)
      move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
      exists (X1 `&` Y1); first exact: measurableI.
      by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
    move=> /= C [A mA [B mB] <-].
    split; first exact: measurableX.
    rewrite [X in measurable_fun _ X](_ : _ =
        (fun s => ((\1_A s)%:E * k s B)%E)); last first.
        by apply/funext => s; rewrite IgE.
      apply: emeasurable_funM; first exact/measurable_EFinP.
      exact: measurable_kernel.
  have mI1 (A : set (T1 * T2)) : measurable A ->
      measurable_fun setT (I (EFin \o \1_A)).
    by rewrite -DE => -[].
  rewrite [X in measurable_fun _ X](_ : _ = I
    (EFin \o (fun x => \sum_(y \in range (f_ m)) y *
                       \1_(f_ m @^-1` [set y]) x))); last first.
    apply/funext => x/=.
    apply: eq_integral => y _ /=.
    by rewrite fimfunE.
  rewrite /I/=.
  rewrite [X in measurable_fun _ X](_ : _ = (fun x =>
     \sum_(y \in range (f_ m))
       (\int[k x]_w2 (y * \1_(f_ m @^-1` [set y]) (x, w2))%:E)%E)); last first.
    apply/funext => x.
    under eq_integral.
      move=> y _.
      rewrite -fsumEFin//.
      over.
    rewrite /= ge0_integral_fsum//=.
      move=> r.
      under eq_fun do rewrite EFinM.
      apply: emeasurable_funM => //.
      by apply/measurable_EFinP; exact: measurableT_comp.
    by move=> r y _; rewrite EFinM nnfun_muleindic_ge0.
  apply: emeasurable_fsum => // r.
  rewrite [X in measurable_fun _ X](_ : _ = (fun x =>
      (r%:E * \int[k x]_w2 (\1_(f_ m @^-1` [set r]) (x, w2))%:E)%E)); last first.
    apply/funext => x.
    under eq_integral do rewrite EFinM.
    rewrite integralZl//.
      pose kx : {measure set T2 -> \bar R} := k x.
      pose H1 := isFinite.Build _ _ _ _
        (@finite_finite_transition_kernel _ _ _ _ R k x).
      pose H2 := isSFinite.Build _ _ _ _
        (finite_sfinite_measure (@finite_finite_transition_kernel _ _ _ _ R k x)).
      pose H3 := isSigmaFinite.Build _ _ _ _
        (finite_sigma_finite (@finite_finite_transition_kernel _ _ _ _ R k x)).
      pose kx' := HB.pack_for (FiniteMeasure.type T2 R) (Measure.sort kx)H1 H2 H3.
      have kxE : kx = kx' by apply: eq_measure.
      rewrite -/kx kxE; apply: integrable_indic => //.
    rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
    exact: measurable_xsection.
  by apply: emeasurable_funM => //; exact: mI1.
by move=> ? _; exact: If_cvg.
Qed.

(* intermediate function used in thm 14.22 *)
Definition k1comp d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k : (T0 * T1)%type -> {measure set T2 -> \bar R}(*R.-ftker (T0 * T1) ~> T2*)) A
  := fun xy => (\int[k xy]_z (\1_A (xy.2, z))%:E)%E.

Lemma measurable_k1comp d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k2 : R.-ftker (T0 * T1) ~> T2) A : measurable A ->
  measurable_fun setT (k1comp k2 A).
Proof.
move=> mA.
apply: (@measurable_kfcomp _ _ (T0 * T1)%type T2 R k2
  (fun abc => (\1_A (abc.1.2, abc.2))%:E)) => //.
  apply/measurable_EFinP => //=.
  apply: measurableT_comp => //=.
  apply/prod_measurable_funP; split => /=.
    rewrite [X in measurable_fun _ X](_ : _ = snd \o fst)//.
    exact: measurableT_comp.
  by rewrite [X in measurable_fun _ X](_ : _ = snd).
by move=> t; rewrite lee_fin.
Qed.

(* composition of two finite transition kernels in thm 14.22 *)
Definition kkcomp_dep d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : T0 -> {measure set T1 -> \bar R})
    (k2 : T0 * T1 -> {measure set T2 -> \bar R}) : T0 -> set (T1 * T2) -> \bar R
     := (* NB: not exactly kcomp k1 k2 because of the return type*)
  fun (x : T0) (A : set (T1 * T2)) =>
  (\int[k1 x]_w1 (k1comp k2 A (x, w1)))%E.

Definition kkcomp_undep d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : T0 -> {measure set T1 -> \bar R})
    (k2 : T1 -> {measure set T2 -> \bar R}) : T0 -> set (T1 * T2) -> \bar R
     := kkcomp_dep k1 (fun x01 => k2 x01.2).

Lemma kkcomp_depE d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) A :
  (kkcomp_dep k1 k2) ^~ A =
    (fun w0 => \int[k1 w0]_w1 (k1comp k2 A) (w0, w1))%E.
Proof. by apply/funext => w0. Qed.

(* thm 14.22 b *)
Theorem semi_sigma_additive_kkcomp_dep d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) w0 :
  semi_sigma_additive (kkcomp_dep k1 k2 w0).
Proof.
move=> /= A mA tA mbigcup.
have := kkcomp_depE k1 k2 (\bigcup_n A n).
move=> /(congr1 (fun x => x w0)) ->.
rewrite (_ : (fun n => _) = (fun n =>
  \int[k1 w0]_w1
    (\sum_(0 <= i < n) k1comp k2 (A i) (w0, w1))))%E; last first.
  apply/funext => n.
  rewrite ge0_integral_sum//.
    move=> m.
    have := measurable_k1comp k2 (mA m).
    exact: measurability_prod2.
  move=> m x _.
  apply: integral_ge0 => y _.
  by rewrite lee_fin.
pose g' : nat -> T1 -> \bar R := fun n =>
  (fun w1 => \sum_(0 <= i < n) (k1comp k2 (A i) (w0, w1)))%E.
rewrite [X in _ --> X](_ : _ = (\int[k1 w0]_x limn (g'^~ x))%E); last first.
  apply: eq_integral => x _.
  rewrite /g' /k1comp.
  rewrite -(@integral_nneseries _ _ R (k2 (w0, x)) _ measurableT
    (fun i z => (\1_(A i) (x, z))%:E))//.
  - by apply: eq_integral => y _ /=; rewrite indicbigcup.
  - move=> n.
    apply/measurable_EFinP => //.
    apply: measurable_indic.
    rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
    exact: measurable_xsection.
  - by move=> n y _; rewrite lee_fin.
apply: (@cvg_monotone_convergence _ _ _ (k1 w0) _ measurableT g') => //.
- move=> n.
  rewrite /g'.
  apply: (@emeasurable_sum _ _ R setT _ _ (fun i t => k1comp k2 (A i) (w0, t))) => m.
  have := measurable_k1comp k2 (mA m).
  by apply: measurability_prod2.
- move=> n x _.
  rewrite /g'.
  apply: sume_ge0 => m _.
  by apply: integral_ge0 => y _; rewrite lee_fin.
- move=> x _ a b ab.
  rewrite /g'.
  apply: lee_sum_nneg_natr => // m _ _.
  by apply: integral_ge0 => y _; rewrite lee_fin.
Qed.

Section kkcomp_dep_measure.
Context d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2).

Let kkcomp_dep0 (x : T0) : kkcomp_dep k1 k2 x set0 = 0.
Proof.
apply: integral0_eq => y _.
apply: integral0_eq => z _.
by rewrite indic0.
Qed.

Let kkcomp_dep_ge0 (x : T0) A : (0 <= kkcomp_dep k1 k2 x A)%E.
Proof.
apply: integral_ge0 => y _.
apply: integral_ge0 => z _.
by rewrite lee_fin.
Qed.

Let kkcomp_dep_additive (x : T0) : semi_sigma_additive (kkcomp_dep k1 k2 x).
Proof. exact: semi_sigma_additive_kkcomp_dep. Qed.

HB.instance Definition _ (x : T0) := isMeasure.Build
  (measure_prod_display (d1, d2)) (T1 * T2)%type R (kkcomp_dep k1 k2 x)
  (kkcomp_dep0 x) (kkcomp_dep_ge0 x) (@kkcomp_dep_additive x).

End kkcomp_dep_measure.

Section mkkcomp_dep.
Context d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2).

Definition mkkcomp_dep := (kkcomp_dep k1 k2 : T0 -> {measure set (T1 * T2) -> \bar R}).

End mkkcomp_dep.

(* thm 14.22 a *)
Theorem measurable_kkcomp_dep d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2)
    A : measurable A ->
  measurable_fun [set: T0] ((kkcomp_dep k1 k2) ^~ A).
Proof.
move=> mA; rewrite kkcomp_depE; apply: measurable_kfcomp => // t.
  exact: measurable_k1comp.
by apply: integral_ge0 => y _; rewrite lee_fin.
Qed.

HB.instance Definition _ d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2) :=
  @isKernel.Build _ _ T0 (T1 * T2)%type R
    (mkkcomp_dep k1 k2) (measurable_kkcomp_dep k1 k2).

From mathcomp Require Import archimedean.

Section sigma_finite_kkcomp_dep.
Context d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-ftker T0 ~> T1) (k2 : R.-ftker (T0 * T1) ~> T2).

(* thm 14.22 c *)
Theorem sigma_finite_kkcomp_dep w0 : sigma_finite setT (kkcomp_dep k1 k2 w0).
Proof.
pose A n := [set w1 | k2 (w0, w1) setT < n%:R%:E]%E.
have mA n : measurable (A n).
  rewrite /A -[X in measurable X]setTI.
  apply: emeasurable_fun_infty_o => //.
  have := @measurable_kernel _ _ _ _ R k2 _ measurableT.
  exact: measurability_prod2.
have bigcupA : \bigcup_n A n = setT.
  have Hk2 : forall w0w1, fin_num_fun (k2 w0w1).
    move=> w0w1.
    by apply: finite_finite_transition_kernel.
  apply/seteqP; split => // x _.
  have {}Hk2 := Hk2 (w0, x) _ measurableT.
  exists (Num.trunc (fine (k2 (w0, x) setT))).+1 => //=.
  rewrite /A/=.
  have : 0 <= fine (k2 (w0, x) [set: T2]) by rewrite fine_ge0//.
  move=> /Num.Theory.trunc_itv/andP[_].
  by rewrite -lte_fin fineK//.
have lty n : (kkcomp_dep k1 k2 w0 (A n `*` setT) < +oo)%E.
  have Hk1 : fin_num_fun (k1 w0) by apply: finite_finite_transition_kernel.
  apply: (@le_lt_trans _ _ (n%:R%:E * k1 w0 (A n))%E) => /=.
    rewrite /kkcomp_dep.
    rewrite [leLHS](_ : _ = \int[k1 w0]_(x in A n) k2 (w0, x) setT)%E; last first.
      under eq_integral.
        move=> x _.
        rewrite /k1comp(*NB:lemma?*) integral_indic//; last first.
          rewrite -[X in measurable X]/(_ @^-1` _) -xsectionE.
          by apply: measurable_xsection; exact: measurableX.
        rewrite setIT.
        over.
      rewrite [RHS]integral_mkcond.
      apply: eq_integral => x _.
      rewrite patchE.
      case: ifPn => Anx.
        congr (k2 _ _).
        apply/funext => y/=.
        apply/propext; split => // _; split => //.
        exact/set_mem.
      rewrite [X in k2 _ X = _](_ : _ = set0) ?measure0//.
      rewrite -subset0// => y/= [].
      move: Anx.
      by rewrite notin_setE.
    apply: (@le_trans _ _ (\int[k1 w0]_(x in A n) n%:R%:E)%E).
      apply: ge0_le_integral => //.
      apply: measurable_funTS.
      have := @measurable_kernel _ _ _ _ _ k2 _ measurableT.
      exact: measurability_prod2.
      by move=> x; rewrite /A/= => /ltW.
    by rewrite integral_cst.
  by rewrite lte_mul_pinfty// ltey_eq Hk1//.
exists (fun n => A n `*` setT) => /=.
  by rewrite -setX_bigcupl bigcupA setXTT.
move=> n; split => //.
exact: measurableX.
Qed.

HB.instance Definition _ (x : T0) := @isSigmaFiniteTransitionKernel.Build d0
  (measure_prod_display (d1, d2)) T0 (T1 * T2)%type R
    (mkkcomp_dep k1 k2) sigma_finite_kkcomp_dep.

End sigma_finite_kkcomp_dep.

Definition kkcomp d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-submker T0 ~> T1)
    (k2 : R.-submker T1 ~> T2) : T0 -> set T2 -> \bar R
     :=
  fun (w0 : T0) (A : set T2) => (\int[k1 w0]_w1 (k2 w1 A))%E.

(* thm 14.26 a *)
Lemma kkcompE d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-submker T0 ~> T1)
    (k2 : R.-submker T1 ~> T2) w0 A :
  measurable A ->
  kkcomp k1 k2 w0 A = kkcomp_undep k1 k2 w0 (snd @^-1` A).
Proof.
move=> mA.
rewrite /kkcomp /kkcomp_undep /kkcomp_dep.
apply: eq_integral => x _ /=.
rewrite /k1comp/=(*NB:lemma?*) integral_indic//; last first.
congr (k2 x _).
by rewrite setIT.
Qed.

(* thm 14.26 b *)
Lemma submarkov_kkcomp d0 d1 d2 (T0 : measurableType d0)
    (T1 : measurableType d1) (T2 : measurableType d2) {R : realType}
    (k1 : R.-submker T0 ~> T1)
    (k2 : R.-submker T1 ~> T2) :
  forall x, (kkcomp k1 k2 x setT <= 1)%E.
Proof.
move=> x.
rewrite kkcompE//.
rewrite preimage_setT.
have H1 := @submarkov_transition_kernel _ _ _ _ _ k1.
have H2 := @submarkov_transition_kernel _ _ _ _ _ k2.
rewrite /kkcomp_undep.
rewrite /kkcomp_dep.
rewrite /k1comp/=.
rewrite [leLHS](_ : _ = \int[k1 x]_w1 (k2 w1 setT))%E; last first.
  apply: eq_integral => y _.
  rewrite integral_indic//; last first.
    rewrite [X in measurable X](_ : _ = ysection setT y).
      exact: measurable_ysection.
    by rewrite ysectionE.
  by rewrite setIT.
apply: (@le_trans _ _ (\int[k1 x]_w1 1)%E).
  apply: ge0_le_integral => //.
  exact: measurable_kernel.
by rewrite integral_cst// mul1e.
Qed.

(* xxx *)

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
  independent_RVs2 P X Y ->
  P (X @^-1` B1 `&` Y @^-1` B2) = P (X @^-1` B1) * P (Y @^-1` B2).
Proof.
move=> mB1 mB2.
rewrite /independent_RVs2 /independent_RVs /mutual_independence /= => -[_].
move/(_ [fset false; true]%fset (@subsetT _ _)
  (fun b => if b then Y @^-1` B2 else X @^-1` B1)).
rewrite !big_fsetU1 ?inE//= !big_seq_fset1/=.
apply => -[|] /= _; rewrite !inE; rewrite /g_sigma_algebra_mapping.
by exists B2 => //; rewrite setTI.
by exists B1 => //; rewrite setTI.
Qed.

Lemma tmp1 (X Y : {RV P >-> R}) (B1 B2 : set R) :
  measurable B1 -> measurable B2 ->
  independent_RVs2 P X Y ->
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
  independent_RVs2 P X Y ->
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o Y) ->
  'E_(P \x P) [(fun x => `|X x.1 * Y x.2|)%R] < +oo
(*  `|'E_(P) [(fun x => X x * Y x)%R]| < +oo *) .
Proof.
move=> indeXY iX iY.
(*apply: (@le_lt_trans _ _ 'E_(P \x P)[(fun x => `|(X x.1 * Y x.2)|%R)]
   (* 'E_(P)[(fun x => `|(X x * Y x)|%R)] *)  ).
  rewrite unlock/=.
  rewrite (le_trans (le_abse_integral _ _ _))//.
  apply/measurable_EFinP/measurable_funM.
    by apply/measurableT_comp => //.
  by apply/measurableT_comp => //.*)
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
  by apply: integral_ge0 => //.
  apply: integral_fune_fin_num => //=.
  by move/integrable_abse : iX => //.
apply: integral_fune_lt_pinfty => //.
by move/integrable_abse : iY => //.
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
    g_sigma_algebra_mapping Z (dyadic_approx setT (EFin \o Z) m k).
  move=> mk; rewrite /g_sigma_algebra_mapping /dyadic_approx mk setTI.
  rewrite /preimage_class/=; exists [set` dyadic_itv R m k] => //.
  rewrite setTI/=; apply/seteqP; split => z/=.
    by rewrite inE/= => Zz; exists (Z z).
  by rewrite inE/= => -[r rmk] [<-].
have mB (Z : {RV P >-> R}) k :
    g_sigma_algebra_mapping Z (integer_approx setT (EFin \o Z) k).
  rewrite /g_sigma_algebra_mapping /integer_approx setTI /preimage_class/=.
  by exists `[k%:R, +oo[%classic => //; rewrite setTI preimage_itvcy.
have m1A (Z : {RV P >-> R}) : forall k, (k < n * 2 ^ n)%N ->
    measurable_fun setT
    (\1_(dyadic_approx setT (EFin \o Z) n k) : g_sigma_algebra_mappingType Z -> R).
  move=> k kn.
  exact/(@measurable_indicP _ (g_sigma_algebra_mappingType Z))/mA.
rewrite !inE => /orP[|]/eqP->{i} //=.
  have : @measurable_fun _ _ (g_sigma_algebra_mappingType X) _ setT (X_ n).
    rewrite nnsfun_approxE//.
    apply: measurable_funD => //=.
      apply: measurable_sum => //= k'; apply: measurable_funM => //.
      by apply: measurable_indic; exact: mA.
    apply: measurable_funM => //.
    by apply: measurable_indic; exact: mB.
  rewrite /measurable_fun => /(_ measurableT _ (measurable_set1 x)).
  by rewrite setTI.
have : @measurable_fun _ _ (g_sigma_algebra_mappingType Y) _ setT (Y_ n).
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
  independent_RVs2 P X Y ->
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
  independent_RVs2 P X Y ->
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
Lemma expectation_prod (X Y : {RV P >-> R}) :
  independent_RVs2 P X Y ->
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
  independent_RVs P [set` I] X -> independent_RVs P [set` (I `\ i0)%fset] X.
Proof.
move=> H.
split => [/= i|/= J JIi0 E EK].
  rewrite !inE => /andP[ii0 iI].
  by apply H.
apply H => //.
by move=> /= x /JIi0 /=; rewrite !inE => /andP[].
Qed.

End product_expectation.
