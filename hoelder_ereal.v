(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop signed reals ereal.
From mathcomp Require Import topology normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun exp convex.

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
    ereal_inf ([set r | mu ([set x | r < f x]%E) = 0]%E).

  Definition ess_infe f := - ess_supe (\- f). 

  Lemma ess_supe_ge0 f : 0 < mu setT -> (forall t, 0%E <= f t) ->
    0 <= ess_supe f.
  Proof. 
    move=> H H0. apply: lb_ereal_inf. move => r /= /eqP H1.
    case r eqn:H2; 
    rewrite ?le0y // leNgt; 
    apply/negP => r0; apply/negP : H1; 
    rewrite -preimage_itvoy gt_eqF// (_ : f @^-1` _ = setT)//= 
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

End extended_essential_supremum.

Definition geo_mean {d} {T : measurableType d} {R : realType} 
  (P : probability T R) (g : T -> \bar R) := 
expeR (\int[P]_x (lne (g x)))%E.

Declare Scope Lnorme_scope.

HB.lock Definition Lnorme {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => (if p == 0%R then
              mu (f @^-1` (setT `\ 0%R))
            else
              (\int[mu]_x (`|f x| `^ p%:E)) `^ p^-1%:E)%E
  | +oo%E => (if mu [set: T] > 0 then ess_supe mu (abse \o f) else 0)%E
  | -oo%E => (if mu [set: T] > 0 then ess_infe mu (abse \o f) else 0)%E
  end.

Definition Lmeane {d} {T : measurableType d} {R : realType}
  (P : probability T R) (p : \bar R) (f : T -> \bar R) :=
  if p == 0 then geo_mean P f else Lnorme P p f.

Definition HLmeane {d} {T : measurableType d} {R : realType}
  (P : probability T R) (p : \bar R) (f : T -> \bar R) :=
  (Lmeane P p ((poweR ^~ -1%:E) \o f)) `^ -1%:E.

Definition HLmeane' {d} {T : measurableType d} {R : realType}
  (P : probability T R) (p : \bar R) (f : T -> \bar R) :=
  match p with
  | p%:E => if p == 0%R then (geo_mean P ((poweR ^~ -1%:E) \o f)) `^ -1%:E else Lmeane P (-p%:E) f
  | +oo%E => (if P [set: T] > 0 then ess_infe P (abse \o f) else 0)%E
  | -oo%E => (if P [set: T] > 0 then ess_supe P (abse \o f) else 0)%E
  end.

  (*
Lemma HGmeane_isHGmeane' d T R P p f : @HGmeane d T R P p f = HGmeane' P p f.
Admitted. 
*)

Section Lnorme_properties.
  Context d {T : measurableType d} {R : realType}.
  Variable mu : {measure set T -> \bar R}.
  Local Open Scope ereal_scope.
  Implicit Types (p : \bar R) (f g : T -> \bar R) (r : R).
  
  Local Notation "'Ne_ p [ f ]" := (Lnorme mu p f).
  
  Lemma Lnorme1 f : 'Ne_1[f] = \int[mu]_x `|f x|.
  Proof. 
    rewrite unlock oner_eq0 invr1 poweRe1; 
        first by apply : eq_integral => t _; rewrite poweRe1 // abse_ge0.
    by apply : integral_ge0 => t _; rewrite  poweRe1 abse_ge0.
  Qed.
  
  Lemma Lnorme_ge0 p f : 0 <= 'Ne_p[f].
  Proof. 
    rewrite unlock. move : p => [r/=|/=|//].
    - by case: ifPn => // _; 
      rewrite ?/geo_mean ?expeR_ge0 ?poweR_ge0.
    - by case: ifPn => H //; rewrite ess_supe_ge0 //;
      move => t; rewrite compE //= abse_ge0.
    - by case: ifPn => H //; rewrite ess_infe_ge0 //;
      move => t; rewrite compE //= abse_ge0.
  Qed.
  
  Lemma eq_Lnorme p f g : f =1 g -> 'Ne_p[f] = 'Ne_p[g].
  Proof.
    move => H; congr Lnorme; exact /funext.
  Qed.

  Search "measurable" "U".

  Lemma emeasurable_fun_fine D f : 
    measurable_fun D (fine \o f) -> 
    d.-measurable (f @^-1` [set -oo]) -> 
    d.-measurable (f @^-1` [set 0]) -> 
    d.-measurable (f @^-1` [set +oo]) -> 
    measurable_fun D f.
  Proof.
    move => mfinef mfi_y mfi_0 mfi_Ny mD //= Y mY.
    rewrite 
    (_ : (f @^-1` Y) =  
      ((fine \o f) @^-1` (fine @` (Y `\` [set -oo; 0; +oo])))
      `|` 
      ((f @^-1`(Y `&` [set -oo; 0; +oo]%E)))
    ); last first. 
    -
    apply/seteqP; f_equal; split => 
    [t //=  
    |t //= [[x [+ /not_orP [/not_orP [+ +]] +]] 
    | [Yft [[ftNy|ft0]|fty]]]]; 
    case H : ((f t) == 0); move: H => /eqP; case ft: (f t) => //=.
    + by right; split => //; left; right.
    + by left; exists (f t); rewrite ft //; rewrite !not_orE; repeat split. 
    + by right; split => //; right. 
    + by right; split => //; left; left.
    all: try by case : x => [?||] => //= + + + + + <-.
    all: try by case : x => [?||] => //= _ ? _ + _ => /[swap] ->.
    all: try by rewrite ftNy in ft.
    all: try by rewrite ?ft ?ftNy in Yft.
    -
    rewrite setIUr; apply /measurableU; try apply /mfinef => //.
    rewrite (_ : 
    (fine @` (Y `\` [set -oo; 0; +oo])) = 
    (fine @` (Y `\` [set -oo; +oo])) `\`(fine @` [set 0])
    ); last first.
    apply /seteqP; split => 
    [r //= [[a||] [Yx /not_orP [/not_orP [xNy x0] xy //= xr]]]
    |r //= [[[a||] [Yx /not_orP [xNy xy]]] //= xr]] => //.
      split; first by exists a%:E => //; split => //=; move=> [|].
        by move=> [? -> //=]; move : x0 xr => + <- => /[swap] <-.
      move=> ?; exists a%:E=> //; split=> //; repeat rewrite not_orE. 
      by repeat split=> //=; move=>  a0; 
        have: (exists2 x : \bar R, x = 0%R & fine x = r); first by exists a%:E.
    apply measurableI.
    apply : measurable_image_fine => //=.
    apply measurableC.
    rewrite image_set1 => //=. 
    apply measurableI => //=.
    rewrite preimage_setI.
    rewrite !preimage_setU.
    rewrite !setIUr.
    rewrite -!preimage_setI.
    by repeat apply : measurableU; rewrite setI1;
    case : (_ \in Y) => //=; rewrite preimage_set0.
  Qed.

  (*TODO: generalize for p ereal*)

  Lemma measurable_poweR r :
      measurable_fun [set: \bar R] (poweR ^~ r%:E).
  Proof.
  move => _ /= B mB.
  rewrite setIidr; last by apply subsetT.
  rewrite [X in measurable X]
  (_ : (poweR^~ r%:E @^-1` B) = 
    if (r == 0%R) then 
      (if 1 \in B then [set : \bar R] else set0) 
    else
      EFin @` ( @powR R ^~ r @^-1` (fine @` (B `\` [set -oo; +oo])))  
      `|` (if (0 < r)%R then (B `&` [set +oo]) 
          else if 0 \in B then [set +oo] else set0)
      `|` (if 1 \in B then [set -oo] else set0)
    ); first last.
  -
  case : (ltgtP 0%R r) => r0; repeat case : ifPn; 
    try move => /set_mem ?; try rewrite notin_setE => ?;
    try move => /set_mem ?; try rewrite notin_setE => ?; 
    apply /seteqP; split => [[s||] //= |x //=];
    rewrite ?poweR_EFin.
    all: try (by left;left; exists s => //; exists (s `^ r)%:E => //; 
         split => //; rewrite not_orE; split).
    all: try by (rewrite ?poweRNye // ?poweRyPe //;left;right ).
    all: try by right.
    all: try (by move => [[[a [[z||] [Bz /not_orP [zneqNy zneqy] //= zar <-]]]|H]|xNy];
         rewrite -lte_fin in r0; try (case H => + xy); 
         rewrite ?poweR_EFin -?zar ?xy ?H ?(poweRyPe r0) ?(poweRyNe r0) ?xNy ?poweRNye).
    all: try by (rewrite ?(gt_eqF r0) ?r0 => //; left; right).
    all: try by rewrite poweRyNe.
    all: try by rewrite -r0 ?poweRe0 ?powRr0.
  -
  case : (ltgtP 0%R r) => r0; repeat case : ifPn; 
    try move => /set_mem B1; try rewrite notin_setE => nB1;
    try move => /set_mem B0; try rewrite notin_setE => nB0;
    repeat apply : measurableU => //=; try apply: measurable_image_EFin;
    try rewrite -[X in measurableR X] setTI; try apply: @measurable_powR => //;
    by try exact: measurable_image_fine; try exact: measurableI => //=.
  Qed.

Lemma Lnorme_eq0_eq0 r f : 
(0 < r)%R -> 
measurable_fun setT f ->
'Ne_r%:E[f] = 0 -> 
ae_eq mu [set: T] (fun t => (`|f t| `^ r%:E)) (cst 0).
Proof.
  move=> rgt0 mf /eqP; rewrite unlock (gt_eqF rgt0) poweR_eq0y.
  have igt0 : (0 < (r^-1))%R; first by rewrite invr_gt0.
  rewrite lte_fin.
  move=> /orP [/orP [/orP [/andP [/eqP Ieq0 /eqP invrneq0]|
         /andP [Igt1 /eqP ieqNy]]|
         /andP [Igt0 /eqP ieqy]]| 
         /andP [/eqP Ieqy ilt0]] //=; 
         last by have := lt_trans ilt0 igt0; rewrite ltxx.      
  apply/ae_eq_integral_abs => //=.
  apply: (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r%:E)) => //=.
  apply /measurable_poweR.
    exact : measurableT_comp. 
  under eq_integral => x _ do rewrite (gee0_abs (poweR_ge0 _ _)).
  apply Ieq0; rewrite -powR_inv1.
  by rewrite integral_ge0 // => x _; rewrite poweR_ge0.
Qed.

(*weakened !!!*)
Lemma poweR_Lnorme f r : (0 < r)%R ->
  'Ne_r%:E[f] `^ r%:E = \int[mu]_x (`| f x | `^ r%:E).
Proof.
move => r0; rewrite unlock ?(gt_eqF r0); move : r0.
have : 0 <= \int[mu]_x (`| f x | `^ r%:E); 
    first by apply integral_ge0 => ? _; rewrite poweR_ge0.
case intfx : (\int[mu]_x  `|f x| `^ r%:E) => [x||] // x0 r0; last first. 
- rewrite !poweRyPe ?invr_gt0 ?lte_fin ?invr_gt0 => //.
- rewrite !poweR_EFin; f_equal. rewrite -powRrM mulVf;
  last by rewrite negbT // eq_sym; apply (lt_eqF r0).
  apply powRr1; by move : x0; rewrite lee_fin.
Qed. 

Lemma compre_mule (h : \bar R -> R) (f g : T -> \bar R) :
  {morph h : x y / x * y >-> (x * y)%R} ->
  h \o  (f \* g) = ((h \o  f) \* (h \o  g))%R.
  Proof. move => mh; apply/funext => t //=. Qed.

(*TODO: generalize fineM*)

Lemma fun_fineM f g :  fine \o  f \* g = ((fine \o f) \* (fine \o g))%R.
Proof.
  apply compre_mule => //=.
  move => [a||] [b||] //=; try by rewrite ?fineM //.
  all: rewrite ?mulr0 ?mul0r ?mulNyy ?mulyNy ?mulyy //=.
  all: try case : (ltgtP 0 a%:E) => z0; try case : (ltgtP 0 b%:E) => z0;
  try by rewrite -?z0 ?mul0e 
    ?mule0 ?(gt0_muley z0) ?(gt0_mulye z0) ?(lt0_muley z0) ?(lt0_mulye z0)
    ?(gt0_muleNy z0)?(gt0_mulNye z0) ?(lt0_muleNy z0) ?(lt0_mulNye z0).
Qed.


End Lnorme_properties.

#[global] Hint Extern 0 (measurable_fun _ (@poweR _ ^~ _)) =>
solve [apply: measurable_poweR] : core.

#[global]
Hint Extern 0 (0 <= Lnorme _ _ _) => solve [apply: Lnorme_ge0] : core.

Notation "'Ne[ mu ]_ p [ f ]" := (Lnorme mu p f).

Section hoelder.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.
Implicit Types (r s : R) (p q : \bar R) (f g : T -> \bar R).

(*TODO: generalize for p ereal*)

Let measurableT_comp_poweR f r :
  measurable_fun [set: T] f -> measurable_fun setT (fun x => (f x) `^ r%:E).
Proof. apply (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r%:E)) => //=. Qed.

Local Notation "'Ne_ p [ f ]" := (Lnorme mu p f).

Let integrable_poweR f r : (0 < r)%R ->
    measurable_fun [set: T] f -> 'Ne_r%:E[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ r%:E)).
Proof.
  move => H H0 H1; apply /integrableP; split.
    apply: measurableT_comp_poweR.
    exact: measurableT_comp.
  rewrite ltey. apply : contra H1.
  move => /eqP/(@eqy_poweR _ _ r^-1%:E). rewrite lte_fin invr_gt0 => /(_ H) <-.
  rewrite unlock (gt_eqF H); apply/eqP; congr (_ `^ _). 
  by apply/eq_integral => t _; rewrite [RHS]gee0_abs // poweR_ge0.
Qed.

(*TODO: generalize for p q ereals*)

Let hoelder0 f g r s : measurable_fun setT f -> measurable_fun setT g ->
    (0 < r%:E) -> (0 < s%:E) -> (r^-1 + s^-1 = 1)%R ->
  'Ne_r%:E[f] = 0 -> 'Ne_1[(f \* g)]  <= 'Ne_r%:E[f] * 'Ne_s%:E[g].
Proof.
  move => mf mg p0 q0 pq f0; rewrite f0 mul0e Lnorme1 [leLHS](_ : _ = 0)//.
  rewrite (ae_eq_integral (cst 0)) => //; first by rewrite integral0.
  - apply : measurableT_comp => //; exact : emeasurable_funM.
  - apply: filterS (Lnorme_eq0_eq0 p0 mf f0) => //= x /(_ I).
    move=> /(introT eqP) + _; rewrite poweR_eq0y; last by apply abse_ge0. 
    move=> /orP[/orP[/orP[/andP[/eqP absfx0]|
      /andP[]]|/andP[]]|/andP[_ ltp0]] => //=; 
    last by have := lt_trans ltp0 p0; rewrite ltxx.
    by rewrite abseM ?absfx0 ?mul0e.
Qed.

Let normalized p f x := (`|f x|) * (('Ne_p[f])`^-1%:E)%E.

Let normalized_ge0 p f x : (0 <= normalized p f x)%E.
Proof. by rewrite /normalized mule_ge0 ?abse_ge0 ?poweR_ge0. Qed.

Let measurable_normalized p f : measurable_fun [set: T] f ->
  measurable_fun [set: T] (normalized p f).
Proof. by move=> mf; apply: emeasurable_funM => //; exact: measurableT_comp. Qed.

Let integral_normalized f r : (0 < r)%R -> 0 < 'Ne_r%:E[f] ->
    mu.-integrable [set: T] (fun x => (`|f x| `^ r%:E)) ->
  \int[mu]_x (normalized r%:E f x `^ r%:E) = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ r%:E * ('Ne_r%:E[f] `^ r%:E)`^ -1%:E)).
  apply eq_integral => t _.
  rewrite /normalized poweRM ?abse_ge0 ?gt_eqF ?poweR_ge0// poweRAC//.
  apply/andP;split;apply/orP;right; last by rewrite -EFinM ltNyr.
  by apply:(le_lt_trans _ lt0y);rewrite muleC ?pmule_rle0.
have fp0 : 0 < \int[mu]_x (`|f x| `^ r%:E).
  rewrite unlock (gt_eqF p0) in fpos.
  apply: gt0_poweR fpos; rewrite ?lte_fin ?invr_gt0 //.
  by apply integral_ge0 => x _;exact: poweR_ge0.
rewrite unlock (gt_eqF p0).
rewrite unlock (gt_eqF p0) -[ X in X `^ (- (1))]poweRrM; last first.
  apply /andP; split; last by rewrite -EFinM ltNyr ?orbT.
  by rewrite (_ : 0 <= _) ?lee_fin ?invr_ge0 ?le_eqVlt ?p0 ?orbT.
rewrite -EFinM mulVf ?(poweRe1 (ltW fp0)); last by rewrite negbT ?gt_eqF.
under eq_integral do rewrite muleC.
have : \int[mu]_x (`|f x| `^ r%:E) < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?poweR_ge0//.
have : -oo < \int[mu]_x (`|f x| `^ r%:E).
  apply /(lt_le_trans ltNy0) /integral_ge0 => x _; apply poweR_ge0.
move: fp0; case fr : (\int[mu]_x (`|f x| `^ r%:E)) => // fp0 _ _.
rewrite poweR_EFin integralZl// fr powR_inv1; last by apply /ltW.
apply /eqP; rewrite eqe_pdivrMl ?mule1 // negbT // gt_eqF //. 
Qed.

Lemma hoelder f g r s : measurable_fun setT f -> measurable_fun setT g ->
  (0 < r)%R -> (0 < s)%R -> (r^-1 + s^-1 = 1)%R ->
'Ne_1[(f \* g)] <= 'Ne_r%:E[f] * 'Ne_s%:E[g].
Proof.
move=>? ? ? ? ?;have [f0|f0] := eqVneq 'Ne_r%:E[f] 0; first by exact: hoelder0.
have [g0|g0] := eqVneq 'Ne_s%:E[g] 0. 
  rewrite muleC; apply: le_trans; last first. 
    apply: hoelder0 => //; first by rewrite addrC.
    by under eq_Lnorme do rewrite /= muleC.
have fpos : 0 < 'Ne_r%:E[f] by rewrite lt0e f0 Lnorme_ge0.
have gpos : 0 < 'Ne_s%:E[g] by rewrite lt0e g0 Lnorme_ge0.
have [foo|foo] := eqVneq 'Ne_r%:E[f] +oo; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'Ne_s%:E[g] +oo; first by rewrite goo gt0_muley ?leey.
pose F := normalized r%:E f; pose G := normalized s%:E g.
rewrite [leLHS](_:_= 'Ne_1[(F \* G)] * 'Ne_r%:E[f] * 'Ne_s%:E[g]);last first.
  rewrite !Lnorme1; under [in RHS]eq_integral.
    move=> x _; rewrite /F /G /normalized/=.
    rewrite gee0_abs; last by rewrite !mule_ge0 ?abse_ge0 ?poweR_ge0 //.
    rewrite muleACA -abseM; over.
  rewrite ge0_integralZr//; last 3 first.
    - apply: measurableT_comp => //; exact: emeasurable_funM.
    - by move => ? _; rewrite abse_ge0.
    - by rewrite mule_ge0 ?poweR_ge0 //.
  rewrite -muleA -muleA [X in _ * X](_ : _ = 1) ?mule1// muleACA.
    move: fpos gpos foo goo; case: ('Ne_ r%:E [f]); 
      case: ('Ne_ s%:E [g]) => // a b + + _ _. 
    rewrite !lte_fin !poweR_EFin -EFinM=> bpos apos;f_equal.
    rewrite !powR_inv1; try by rewrite ?le0r ?bpos ?apos orbC.
    by rewrite !mulVf ?mul1r ?gt_eqF.
  rewrite -(mul1e ('Ne_r%:E[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnorme_ge0//.
  rewrite [leRHS](_ : _ = 
    \int[mu]_x ((F x `^ r%:E)*(r^-1%:E)  + (G x `^ s%:E)*(s^-1%:E) )).
    rewrite Lnorme1 ae_ge0_le_integral //.
    - by move => x _; rewrite abse_ge0.
    - apply: measurableT_comp => //.
      apply: emeasurable_funM=> //; exact: measurable_normalized.
    - move=> x _; rewrite // /F /G /normalized.
      have := le_lt_trans leNy0 fpos; have := le_lt_trans leNy0 gpos.
      move: foo goo fpos gpos; case If : ('Ne_ r%:E [f]); 
        case Ig : ('Ne_ s%:E [g]) => // foo goo fpos gpos _ _.
        + by rewrite ?adde_ge0 ?mule_ge0 ?poweR_ge0 ?ltW ?lte_fin ?invr_gt0.
        + apply /emeasurable_funD; apply /emeasurable_funM => //;
          apply /measurableT_comp_poweR; exact: measurable_normalized.
        + apply /aeW => x _; rewrite gee0_abs; 
            last by rewrite mule_ge0 // normalized_ge0.
          by rewrite conjugate_poweR// normalized_ge0. 
rewrite ge0_integralD//; last 4 first.
- by move=> x _;rewrite mule_ge0 ?poweR_ge0 ?lee_fin ?invr_ge0 ?ltW.
1,3: apply /emeasurable_funM => //;
  by apply /measurableT_comp_poweR /measurable_normalized.
- by move=> x _; rewrite mule_ge0 ?poweR_ge0 ?ltW ?lte_fin ?invr_gt0.
rewrite !ge0_integralZr//; last 3 first.
all: try by apply /measurableT_comp_poweR; exact: measurable_normalized.
all: try by move=> x _; rewrite poweR_ge0.
all: try by rewrite lee_fin invr_ge0 ltW.
repeat (rewrite integral_normalized//; last exact:integrable_poweR).
by rewrite !mul1e -EFinD;f_equal; apply esym.
Qed.
