(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop signed reals ereal.
From mathcomp Require Import topology normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun exp convex itv.

(**md**************************************************************************)
(* # Hoelder's Inequality                                                     *)
(*                                                                            *)
(* This file provides Hoelder's inequality.                                   *)
(* ```                                                                        *)
(*           'N[mu]_p[f] := (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1             *)
(*                          The corresponding definition is Lnorm.            *)
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
Local Open Scope ereal_scope. (*Problematic ?*)

Reserved Notation "'N[ mu ]_ p [ F ]"
  (at level 5, F at level 36, mu at level 10,
  format "'[' ''N[' mu ]_ p '/  ' [ F ] ']'").
(* for use as a local notation when the measure is in context: *)
Reserved Notation "'N_ p [ F ]"
  (at level 5, F at level 36, format "'[' ''N_' p '/  ' [ F ] ']'").

Section extended_essential_supremum.
  Local Open Scope classical_set_scope.
  Local Open Scope ring_scope.
  Local Open Scope ereal_scope.
  Context d {T : semiRingOfSetsType d} {R : realType}.
  Variable mu : {measure set T -> \bar R}.
  Implicit Types (f : T -> \bar R).

  Definition ess_supe f :=
    ereal_inf ([set r | mu ([set x | r < f x]%E) = 0]%E). (* '[r, +oo] ? *)

  Definition ess_infe f := - ess_supe (\- f). 

  Lemma ess_supe_ge0 f : 0 < mu setT -> (forall t, 0%E <= f t) ->
    0 <= ess_supe f.
  Proof. 
    move=> H H0. apply: lb_ereal_inf. move => r /= /eqP H1.
    case r eqn:H2; 
    rewrite ?le0y // leNgt; 
    apply/negP => r0; apply/negP : H1; 
    rewrite -preimage_itv_o_infty gt_eqF// (_ : f @^-1` _ = setT)//= 
    ?setIidr //=; apply/seteqP; split => // x _ /=; 
    rewrite in_itv/= (lt_le_trans _ (H0 x)) //= leey //.  
  Qed.
  
  Lemma ess_infe_le0 f : 0 < mu setT -> (forall t, f t <= 0) -> ess_infe f <= 0.
  Proof.
    move => H H0. rewrite /ess_infe oppe_le0. 
    apply : ess_supe_ge0. rewrite //=. move => t.  
    rewrite oppe_ge0 //.
  Qed.

  Lemma ess_infe_ge0 f : 0 < mu setT -> (forall t, 0%E <= f t) ->
    0 <= ess_infe f.
  Proof. 
    move => H H0. 
    rewrite /ess_infe oppe_ge0 /ess_supe. 
    apply ereal_inf_le.
    rewrite exists2E.
    exists 0. split; rewrite //=.
    have H1 : [set x | 0%R < - f x] = set0.
    - apply eq_set => x. 
      have H1 := H0 x.
      rewrite -falseE oppe_gt0.
      rewrite leNgt in H1; apply negbTE in H1.
      rewrite H1 //=.
    by rewrite H1.
  Qed.

(*
Lemma aku (S : set (\bar R)) : S != set0 -> 
- ereal_sup S = ereal_sup (-%E @` S).
Proof.
  move => H. rewrite /ereal_sup / supremum. rewrite (negPf H).
  have H0 := negP H.
  case: ifPn => H1.
  - have H2 := (image_set0_set0 (eqP H1)).
    move : H1; by rewrite H2 (image_set0 -%E) -{1}H2.
    Check @xgetPex (\bar R) -oo (supremums S).
  -
Qed.  
*)

End extended_essential_supremum.


Definition lne {R : realType} (x : \bar R) :=
  match x with
  | x'%:E => (ln x')%:E
  | +oo => +oo
  | -oo => 0
  end.

Definition geo_mean {d} {T : measurableType d} {R : realType} 
  (P : probability T R) (g : T -> \bar R) := 
expeR (\int[P]_x (lne (g x)))%E.

Declare Scope Lnorme_scope.

HB.lock Definition Lnorme 
  {d} {T : measurableType d} {R : realType} (P : probability T R) 
(p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (if p == 0%R then
              geo_mean P f
            else
              (\int[P]_x (`|f x| `^ p)) `^ p^-1)%E
  | +oo%E => (if P [set: T] > 0 then ess_supe P (abse \o f) else 0)%E
  | -oo%E => (if P [set: T] > 0 then ess_infe P (abse \o f) else 0)%E
  end.
Canonical locked_Lnorme := Unlockable Lnorme.unlock.
Arguments Lnorme {d T R} P p f.

Section Lnorme_properties.
  Context d {T : measurableType d} {R : realType}.
  Variable P : probability T R.
  Local Open Scope ereal_scope.
  Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).

  Local Notation "'Ne_ p [ f ]" := (Lnorme P p f).

  Lemma Lnorme1 f : 'Ne_1[f] = \int[P]_x `|f x|.
  Proof. 
    rewrite unlock oner_eq0 invr1// poweRe1//.
    - by apply : eq_integral => t _; rewrite poweRe1.
    - by apply : integral_ge0 => t _; rewrite  poweRe1.
  Qed.
  
  Lemma Lnorme_ge0 p f : 0 <= 'Ne_p[f].
  Proof. 
    rewrite unlock. move : p => [r/=|/=|//].
    - case: ifPn => // _; 
      rewrite ?/geo_mean ?expeR_ge0 ?poweR_ge0//.
    - case: ifPn => H //; rewrite ess_supe_ge0 //;
      move => t; rewrite compE //=.
    - case: ifPn => H //; rewrite ess_infe_ge0 //.
      move => t; rewrite compE //=.
  Qed.

  Lemma eq_Lnorme p f g : f =1 g -> 'Ne_p[f] = 'Ne_p[g].
  Proof.
    move => H; congr Lnorme; exact /funext.
  Qed.

  Lemma emeasurable_fun_fine D f : 
    measurable_fun D (fine \o f) -> 
    (forall E, E `<=` [set -oo; 0%R; +oo] ->  d.-measurable (f @^-1` E)) -> 
    measurable_fun D f.
  Proof.
    move => H HE H0 //= Y H1.
    rewrite 
    (_ : (f @^-1` Y) =  
      ((fine \o f) @^-1` (fine @` (Y `\` [set -oo; 0; +oo])))
      `|` 
      ((f @^-1`(Y `&` [set -oo; 0; +oo]%E)))
    ); last first.
    apply/seteqP; split => [t //= H2 | t //= H2].
    -
    case ((f t) == 0) eqn:H3; first by
    right; split => //=; left; right; apply (eqP H3).
    case (f t) as [s | | ].
    -- 
    left. exists s%:E => //=. split => //=. repeat rewrite not_orE.
    repeat split => //=. apply negbT in H3. 
    by rewrite contra.Internals.eqType_neqP.
    -- by right; split => //=; right.
    -- by right; split => //=; repeat left.
    -
    case H2 as [[x [H2 H3]] | [H2 H3]].
    - 
    repeat rewrite not_orE in H3.
    case H3 as [[H3 H5] H6].
    case x as [s | | ] => //=.
    rewrite //= in H4.
    case (f t) as [s' | | ].
    -- by rewrite H4 in H2.
    -- by rewrite H4 in H5. 
    -- by rewrite H4 in H5.
    -- by apply H2.
    rewrite setIUr.
    -
    apply : measurableU.
    -
    apply : H => //=.
    rewrite (_ : 
    (fine @` (Y `\` [set -oo; 0; +oo])) = 
    (fine @` (Y `\` [set -oo; +oo])) `\`(fine @` [set 0])
    ); last first. 
      apply/seteqP; split => 
        [t //= [x [H2 H3] H4] | t //= [[x [H2 H3]] H4] H5].
      -- split.
      --- 
      exists x => //=. split => //=. 
      move : H3; repeat rewrite not_orE; move => [[H3 H5] H6].
      split => //=.
      ---
      rewrite /not => H5.
      case H5 as [x' H6].
      rewrite -H in H4.
      rewrite H6 //= in H4.
      repeat rewrite not_orE in H3.
      case H3 as [[H3 H7] H8].
      case x as [s | | ];
      rewrite //= in H4; move : H3 H7 H8 => //=;
      rewrite H4; contradiction.
      --
      exists x => //=. split => //=.
      move : H3. repeat rewrite not_orE.
      move => [H3 H6].
      rewrite /not in H5.
      repeat split => //=.
      case (x == 0) eqn:H7.
      --- 
      have H8 := (eqP H7).
      exfalso. apply H5.
      exists x => //=.
      ---
      rewrite contra.Internals.eqType_neqP.
      by apply negbT.
    apply measurableI.
    apply : measurable_image_fine => //=.
    apply measurableC.
    rewrite image_set1 => //=. 
    apply measurableI => //=.
    apply : HE => //=.
  Qed.

  Lemma measurable_poweR r :
    measurable_fun [set: \bar R] (@poweR R ^~ r).
  Proof.
    move => _ /= B H.
    rewrite setIidr; last first. 
      apply subsetT.
    rewrite [X in measurable X]
      (_ : (poweR^~ r @^-1` B) = 
      if (r == 0%R) then 
        (if 1 \in B then [set : \bar R] else set0) 
      else
        EFin @` ( @powR R ^~ r @^-1` (fine @` (B `\` [set -oo; +oo])))  
        `|` (B `&` [set +oo])
        `|` (if 0 \in B then [set -oo] else set0)
      ); last first.
    case: ifPn => [/eqP ->|r0].
      case: ifPn => [/set_mem B1|B1]; apply/seteqP; 
        split=> // x /=; rewrite poweRe0// => /mem_set; exact: negP.
      apply/seteqP; split => [a/=Bar|a/=].
        case a as [s | | ].
        - by left; left; exists s => //; 
          exists (s `^ r)%:E => //; split => //; case.
        - by rewrite /= (negbTE r0) in Bar; 
          left; right => /=; split=> //.
        - by right; rewrite /= (negbTE r0) in Bar; 
          case: ifPn => //; rewrite notin_setE.
      case.
        case.
          by case=> x; case; case=> [y| |] []+ /not_orP[]// _ _/=; 
            move=> /[swap]->/[swap] <-.
        by case=> /[swap] ->/=; rewrite (negbTE r0).
      by case: ifPn => // /[swap] /= -> /=; rewrite (negbTE r0)=>/set_mem.
    case: ifPn => [|_]; first by case: ifPn => //.
    repeat apply : measurableU.
    apply: measurable_image_EFin.
    rewrite -[X in measurableR X] setTI.
    apply: @measurable_powR => //.
    exact: measurable_image_fine.
    exact: measurableI.
    by case: ifP.
  Qed.

  Lemma Lnorme_eq0_eq0 r f : 
  (0 < r)%R -> 
  measurable_fun setT f ->
  'Ne_r%:E[f] = 0 -> 
  ae_eq P [set: T] (fun t => (`|f t| `^ r)) (cst 0).
  Proof.
    move => H H0. rewrite unlock (gt_eqF H) => /poweR_eq0_eq0 H1.
    apply/ae_eq_integral_abs => //=.
      apply: (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r)) => //=.
      apply /measurable_poweR.
      exact : measurableT_comp. 
    under eq_integral => x _ do rewrite (gee0_abs (poweR_ge0 _ _)).
    apply H1. apply: integral_ge0 => t _. apply poweR_ge0.
  Qed.
    
  Lemma powR_Lnorme f r : r != 0%R ->
    'Ne_r%:E[f] `^ r = \int[P]_x (`| f x | `^ r).
  Proof.
    move => H. rewrite unlock (negbTE H) -poweRrM mulVf// poweRe1//.
    by apply : integral_ge0 => x _; rewrite poweR_ge0.
  Qed.

End Lnorme_properties.

  #[global] Hint Extern 0 (measurable_fun _ (@poweR _ ^~ _)) =>
  solve [apply: measurable_poweR] : core.

  #[global]
  Hint Extern 0 (0 <= Lnorme _ _ _) => solve [apply: Lnorme_ge0] : core.

  Notation "'Ne[ mu ]_ p [ f ]" := (Lnorme mu p f).

  Section hoelder.
  Context d {T : measurableType d} {R : realType}.
  Variable P : probability T R.
  Local Open Scope ereal_scope.
  Implicit Types (r : R) (p q : \bar R) (f g : T -> \bar R).

  Lemma measurable_poweR' r :
    measurable_fun [set: \bar R] (@poweR R ^~ r).
  Proof.
     apply emeasurable_fun_fine.

  Let measurableT_comp_poweR f r :
    measurable_fun [set: T] f -> measurable_fun setT (fun x => (f x) `^ r).
  Proof. apply (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r)) => //=. Qed.

  Local Notation "'Ne_ p [ f ]" := (Lnorme P p f).

  Let integrable_poweR f r : (0 < r)%R ->
      measurable_fun [set: T] f -> 'Ne_r%:E[f] != +oo ->
    P.-integrable [set: T] (fun x => (`|f x| `^ r)).
  Proof.
    move => H H0 H1; apply /integrableP; split.
      apply: measurableT_comp_poweR.
      exact: measurableT_comp.
    rewrite ltey. apply : contra H1.
    move => /eqP/(@eqy_poweR _ _ r^-1). rewrite invr_gt0 => /(_ H) <-.
    rewrite unlock (gt_eqF H); apply/eqP; congr (_ `^ _). 
    by apply/eq_integral => t _; rewrite [RHS]gee0_abs // poweR_ge0.
  Qed.
  

  Let hoelder0 f g p q : measurable_fun setT f -> measurable_fun setT g ->
      (0 < p) -> (0 < q) -> ((p `^-1) + (q `^-1) = 1) ->
    'Ne_p[f] = 0 -> 'Ne_1[(f \* g)]  <= 'Ne_p[f] * 'Ne_q[g].
  Proof. 
    move => H H0 H1 H2 H3 H4;
      case p as [p' | | ] => //=; case q as [q' | | ] => //=.
    -
    move : H1 H2; rewrite ?lte_fin => H1 H2. 
    rewrite H4 mul0e Lnorme1 [leLHS](_ : _ = 0)//.
    rewrite (ae_eq_integral (cst 0)) => [|//||//|]; 
    first by rewrite integral0.
    -- by apply : measurableT_comp => //; exact: emeasurable_funM.
    --  apply: filterS (Lnorme_eq0_eq0 H1 H H4) 
        => t /(_ I) /poweR_eq0_eq0 + _ => //=.
    rewrite abse_ge0 abseM => H5; rewrite H5 ?mul0e //=.
    - all : rewrite //= (_ : -1 == 0%R = false) in H3 
      => //=; apply : negbTE => //=.
  Qed.

  Let normalized p f x := (`|f x|) * (('Ne_p[f])`^-1)%E.

  Let normalized_ge0 p f x : (0 <= normalized p f x)%E.
  Proof. by rewrite /normalized mule_ge0 //= poweR_ge0. Qed.

  Let measurable_normalized p f : measurable_fun [set: T] f ->
    measurable_fun [set: T] (normalized p f).
  Proof. by move=> mf; apply: emeasurable_funM => //; exact: measurableT_comp. Qed.

  Let integral_normalized f r : (0 < r)%R -> 0 < 'Ne_r%:E[f] ->
      P.-integrable [set: T] (fun x => (`|f x| `^ r)) ->
    \int[P]_x (normalized r%:E f x `^ r) = 1.
  Proof.
    move => H H0 H1.
    apply lt0r_neq0 in H as H2.
    rewrite /normalized.
    under eq_integral.
      move => x _; rewrite poweRM; first last. 
      - apply poweR_ge0.
      - apply abse_ge0.
      rewrite poweRAC unlock /Lnorme 
        (gt_eqF H) -(poweRrM _ r^-1 r) mulVf 
        //= poweRe1; last first.
        apply integral_ge0 => x0 _.
        apply poweR_ge0.
    over.
    have [H3 H4] := (integrableP _ _ _ H1).
    rewrite //= ge0_integralZr => //=; last first.
      - apply poweR_ge0.
      - move => x _; apply poweR_ge0.
    have H5 : (-oo < \int[P]_x  `|f x| `^ r).
    Search "le" "lt" "trans".
    rewrite //=.
    (*
    move => H H0 H1.
    transitivity (\int[P]_x (`|f x| `^ r * ('Ne_r%:E[f] `^ r)`^-1)).
      apply: eq_integral => t _.
      rewrite poweRM//; last by apply poweR_ge0. 
      rewrite poweRAC => //=.
    have fp0 : 0 < \int[P]_x (`|f x| `^ r).
      rewrite unlock (gt_eqF H) in H0.
      apply : gt0_poweR H0; rewrite ?invr_gt0 ?poweR_ge0//.
      by apply integral_ge0 => x _; apply poweR_ge0.
    rewrite unlock (gt_eqF H) 
      -[((\int[P]_x0  `|f x0| `^ r) `^ r^-1) `^ r]poweRrM 
      mulVf ?(gt_eqF H)// (poweRe1 (ltW fp0))//.
      under eq_integral do rewrite muleC.
      have H2 : \int[P]_x (`|f x| `^ r) < +oo.
        move/integrableP: H1 => -[_].
        by under eq_integral do rewrite gee0_abs// ?poweR_ge0//.
    *)


     
    


    


