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

Lemma poweRM x y r : (r != 0)%R -> 0 <= x -> 0 <= y -> (x * y) `^ r%:E = x `^ r%:E * y `^ r%:E.
Proof.
have [->|rN0] := eqVneq r 0%R; first by rewrite !poweRe0 mule1.
have powyrM s : (0 <= s)%R -> (+oo * s%:E) `^ r%:E = +oo `^ r%:E * s%:E `^ r%:E.
  case: ltgtP => // [s_gt0 _|<- _]; last first.
    by rewrite poweR0e // !mule0 poweR0e.
    rewrite gt0_mulye //;move: rN0;case: (ltgtP r 0%R) => // p0 _.
      by rewrite poweRyNe ?mul0e.
      rewrite poweRyPe // gt0_mulye // poweR_gt0_lt0r //. apply /andP => //=.
      by rewrite lee_fin le0r p0 orbC //= ltry.
case: x y => [x||] [y||]// _ x0 y0.
- by rewrite ?poweR_EFin -EFinM; f_equal; rewrite powRM.
- by rewrite muleC [X in _ = X]muleC powyrM.
- by rewrite powyrM.
- rewrite mulyy; move: rN0; case: (ltgtP r 0%R) => // rN0 _.
  + by rewrite poweRyNe ?mule0.
  + by rewrite poweRyPe ?mulyy.
Qed.

Lemma poweRrML_gtr0' (x y z : \bar R) : x `^ (y * z) = (x `^ y) `^ z.
Proof.
have [x0|x0|->] := (ltgtP x 0); last first.
- have [->|y0] := eqVneq y 0; have [->|z0] := eqVneq z 0;
  rewrite ?mul0e ?mule0 ?poweRe0 ?poweR1e ?poweR0e ?mule_neq0 //.
- move: x y z x0 => [x||]//[y||]//[z||]// => x0; 
  try have [y0|y0|y0] := (ltgtP y%:E 0);
  try have [z0|z0|z0] := (ltgtP z%:E 0);
  try have neq0y := negbT (gt_eqF y0);
  try have neqy0 := negbT (lt_eqF y0);
  try have neq0z := negbT (gt_eqF z0);
  try have neqz0 := negbT (lt_eqF z0);
  try have yz0 := mule_gt0 y0 z0;
  try have yz0 := mule_lt0_gt0 y0 z0;
  try have yz0 := mule_gt0_lt0 y0 z0;
  try have yz0 := mule_lt0_lt0 y0 z0;
  last first; rewrite ?y0 ?z0
  ?mulyy ?mulNyy ?mulNyNy ?mulyNy ?mul0e ?mule0
  ?(gt0_muleNy y0) ?(lt0_muleNy y0) ?(gt0_muley y0) ?(lt0_muley y0)
  ?(gt0_mulNye z0) ?(lt0_mulNye z0) ?(gt0_mulye z0) ?(lt0_mulye z0).
  (*+oo `^ (-oo * -oo) = (+oo `^ -oo) `^ -oo*) 
  + admit.
  all: try by rewrite 
    ?(poweRyPe yz0) ?(poweRyNe yz0)
    ?(poweRyNe ltNy0) ?(poweRyPe lt0y) 
    ?(poweRyPe y0) ?(poweRyNe y0) ?(poweRyPe z0) ?(poweRyNe z0)
    ?poweRe0 ?poweR0e ?poweR1e
    ?(poweRyNe ltNy0) ?(poweRyPe lt0y)
    ?(poweRyPe y0) ?(poweRyNe y0)
    ?(poweRyPe z0) ?(poweRyNe z0).
  (*+oo `^ (-oo * z%:E) = (+oo `^ -oo) `^ z%:E, z%:E < 0%R*)
  + admit.
  (*+oo `^ (y%:E * -oo) = (+oo `^ -oo) `^ y%:E, y%:E < 0%R*)
  + admit.
  (*+oo `^ (y%:E * z%:E) = (+oo `^ y%:E) `^ z%:E, y%:E < 0%R, z%:E < 0%R*)
  + admit.
  all: try by (rewrite -EFinM !poweR_EFin; f_equal; rewrite powRrM).
  (*x%:E `^ (+oo * -oo) = (x%:E `^ +oo) `^ -oo -> x = 1*) 
  (*x%:E `^ (+oo * +oo) = (x%:E `^ +oo) `^ +oo -> x = 1*)
  (*x%:E `^ (y%:E * -oo) = (x%:E `^ y%:E) `^ -oo, 0 < y%:E -> x = 1*)
  (*x%:E `^ (y%:E * +oo) = (x%:E `^ y%:E) `^ +oo, 0 < y%:E -> x = 1*)
  5,6,9,11: admit.
  all: try have [x1|x1|->] := (ltgtP x%:E 1); rewrite ?poweR1e //.
  all: try (have gelt0x1 : 0 <= x%:E < 1; 
    first by apply /andP; split => //; rewrite le_eqVlt x0 orbC). 
  all: try (have ltlt0x1 : 0 < x%:E < 1; first by apply /andP; split).
  all: try by rewrite 
    ?(poweRey_lt1 gelt0x1) ?(poweReNy_lt1 ltlt0x1) 
    ?(poweRyNe ltNy0) ?(poweRyPe lt0y)
    ?(poweReNy_gt1 x1) ?(poweRey_gt1 x1)
    ?poweR0e.
  (*x%:E `^ (-oo * -oo) = (x%:E `^ -oo) `^ -oo, 1 < x%:E *)
  + admit.
  
  rewrite ?(poweReNy_gt1 x1) poweR0e. (poweRyPe lt0y).
    
- by rewrite [X in _ = X `^ _]lt0_poweR // poweR1e lt0_poweR.


Let integral_normalized f r : (0 < r)%R -> 0 < 'Ne_r%:E[f] ->
    mu.-integrable [set: T] (fun x => (`|f x| `^ r%:E)) ->
  \int[mu]_x (normalized r%:E f x `^ r%:E) = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ r%:E * ('Ne_r%:E[f] `^ r%:E)`^ -1%:E)).
  apply eq_integral => t _.
  rewrite /normalized poweRM ?abse_ge0 ?gt_eqF ?poweR_ge0 //.
  Search "poweR".
(*
Let integral_normalized f p : (0 < p)%R -> 0 < 'N_p%:E[f] ->
    mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E) ->
  \int[mu]_x (normalized p f x `^ p)%:E = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ p / fine ('N_p%:E[f] `^ p))%:E).
  apply: eq_integral => t _.
  rewrite powRM//; last by rewrite invr_ge0 fine_ge0// Lnorm_ge0.
  rewrite -[in LHS]powR_inv1; last by rewrite fine_ge0 // Lnorm_ge0.
  by rewrite fine_poweR powRAC -powR_inv1 // powR_ge0.
have fp0 : 0 < \int[mu]_x (`|f x| `^ p)%:E.
  rewrite unlock (gt_eqF p0) in fpos.
  apply: gt0_poweR fpos; rewrite ?invr_gt0//.
  by apply integral_ge0 => x _; rewrite lee_fin; exact: powR_ge0.
rewrite unlock (gt_eqF p0) -poweRrM mulVf ?(gt_eqF p0)// (poweRe1 (ltW fp0))//.
under eq_integral do rewrite EFinM muleC.
have foo : \int[mu]_x (`|f x| `^ p)%:E < +oo.
  move/integrableP: ifp => -[_].
  by under eq_integral do rewrite gee0_abs// ?lee_fin ?powR_ge0//.
rewrite integralZl//; apply/eqP; rewrite eqe_pdivrMl ?mule1.
- by rewrite fineK// gt0_fin_numE.
- by rewrite gt_eqF// fine_gt0// foo andbT.
Qed.
*)

Lemma hoelder f g r s : measurable_fun setT f -> measurable_fun setT g ->
  (0 < r)%R -> (0 < s)%R -> (r^-1 + s^-1 = 1)%R ->
'Ne_1[(f \* g)] <= 'Ne_r%:E[f] * 'Ne_s%:E[g].
Proof.
move=> mf mg r0 s0 rs.
have [f0|f0] := eqVneq 'Ne_r%:E[f] 0; first by exact: hoelder0.
have [g0|g0] := eqVneq 'Ne_s%:E[g] 0.
  rewrite muleC; apply: le_trans; last first. 
    apply: hoelder0 => //; first by rewrite addrC.
  by under eq_Lnorme do rewrite /= muleC.
have {f0}fpos : 0 < 'Ne_r%:E[f] by rewrite lt0e f0 Lnorme_ge0.
have {g0}gpos : 0 < 'Ne_s%:E[g] by rewrite lt0e g0 Lnorme_ge0.
have [foo|foo] := eqVneq 'Ne_r%:E[f] +oo; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'Ne_s%:E[g] +oo; first by rewrite goo gt0_muley ?leey.
pose F := normalized r%:E f; pose G := normalized s%:E g.
rewrite [leLHS](_ : _ = 'Ne_1[(F \* G)] * 'Ne_r%:E[f] * 'Ne_s%:E[g]); last first.
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
  
(*
  Lemma hoelder f g p q : measurable_fun setT f -> measurable_fun setT g ->
        (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
    'N_1[(f \* g)%R] <= 'N_p%:E[f] * 'N_q%:E[g].
    Proof.
    move=> mf mg p0 q0 pq.
    have [f0|f0] := eqVneq 'N_p%:E[f] 0%E; first exact: hoelder0.
    have [g0|g0] := eqVneq 'N_q%:E[g] 0%E.
      rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
      by under eq_Lnorm do rewrite /= mulrC.
    have {f0}fpos : 0 < 'N_p%:E[f] by rewrite lt0e f0 Lnorm_ge0.
    have {g0}gpos : 0 < 'N_q%:E[g] by rewrite lt0e g0 Lnorm_ge0.
    have [foo|foo] := eqVneq 'N_p%:E[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
    have [goo|goo] := eqVneq 'N_q%:E[g] +oo%E; first by rewrite goo gt0_muley ?leey.
    pose F := normalized p f; pose G := normalized q g.

    rewrite [leLHS](_ : _ = 'N_1[(F \* G)%R] * 'N_p%:E[f] * 'N_q%:E[g]); last first.
    rewrite !Lnorm1; under [in RHS]eq_integral.
      move=> x _; rewrite /F /G /normalized/=.
      rewrite ger0_norm; last by rewrite mulr_ge0 ?divr_ge0 ?fine_ge0 ?Lnorm_ge0.
      by rewrite mulrACA -normrM EFinM; over.
    rewrite ge0_integralZr//; last 2 first.
      - by do 2 apply: measurableT_comp => //; exact: measurable_funM.
      - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// Lnorm_ge0.
    rewrite -!muleA [X in _ * X](_ : _ = 1) ?mule1// EFinM muleACA.
    rewrite (_ : _ * 'N_p%:E[f] = 1) ?mul1e; last first.
      rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
      by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// fpos/= ltey.
    rewrite -[X in _ * X]fineK; last by rewrite ge0_fin_numE ?ltey// Lnorm_ge0.
    by rewrite -EFinM mulVr ?unitfE ?gt_eqF// fine_gt0// gpos/= ltey.
rewrite -(mul1e ('N_p%:E[f] * _)) -muleA lee_pmul ?mule_ge0 ?Lnorm_ge0//.
rewrite [leRHS](_ : _ = \int[mu]_x (F x `^ p / p + G x `^ q / q)%:E).
  rewrite Lnorm1 ae_ge0_le_integral //.
  - do 2 apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_normalized.
  - by move=> x _; rewrite lee_fin addr_ge0// divr_ge0// ?powR_ge0// ltW.
  - by apply: measurableT_comp => //; apply: measurable_funD => //;
       apply: measurable_funM => //; apply: measurableT_comp_powR => //;
       exact: measurable_normalized.
  apply/aeW => x _; rewrite lee_fin ger0_norm ?conjugate_powR ?normalized_ge0//.
  by rewrite mulr_ge0// normalized_ge0.
under eq_integral do rewrite EFinD.
rewrite ge0_integralD//; last 4 first.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurable_funM => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?powR_ge0// ltW.
- apply: measurableT_comp => //; apply: measurable_funM => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
under eq_integral do rewrite EFinM.
rewrite [X in X + _]ge0_integralZr//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
under [X in _ + X]eq_integral => x _ do rewrite EFinM.
rewrite ge0_integralZr//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_powR => //; exact: measurable_normalized.
- by move=> x _; rewrite lee_fin powR_ge0.
- by rewrite lee_fin invr_ge0 ltW.
rewrite integral_normalized//; last exact: integrable_powR.
rewrite integral_normalized//; last exact: integrable_powR.
by rewrite 2!mul1e -EFinD pq.
Qed.
*)
(*
(*Is it ok to work just with a probability*)
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
move => _ /= B mB.
rewrite setIidr; last first. 
apply subsetT.
rewrite [X in measurable X]
(_ : (poweR^~ r @^-1` B) = 
  if (r == 0%R) then 
    (if 1 \in B then [set : \bar R] else set0) 
  else
    EFin @` ( @powR R ^~ r @^-1` (fine @` (B `\` [set -oo; +oo])))  
    `|` (if (0 < r)%R then (B `&` [set +oo]) 
        else if 0 \in B then [set +oo] else set0)
    `|` (if 1 \in B then [set -oo] else set0)
  ); last first.
case : (ltgtP 0%R r) => r0; repeat case : ifPn; 
  try move => /set_mem B1; try rewrite notin_setE => nB1;
  try move => /set_mem B0; try rewrite notin_setE => nB0; 
  apply /seteqP; split => [x //= Bxr|x //=].  
  1,3,5,7,9,11 : destruct x as [s | |]; first by left; left; 
        exists s => //; exists (s `^ r)%:E => //; 
        split => //; rewrite not_orE; split.
  1,3: by left; right; rewrite (poweRyPr r0) in Bxr.
  1,4,6,8,10: by right.
  by rewrite poweRNyr in Bxr.
  1,2: by left; right.
  1,2: by left; left; rewrite (poweRyNr r0) in Bxr.
  1,2,3,4,5,6: 
    move => [[[a [[s||] [Bz NzNyOzy //= nfzar <- //=]]]|]|] //=;
    first by rewrite -nfzar.
  1,2 : by move : NzNyOzy; rewrite not_orE; move => [H H0].  
  1,5: by move => [+ xy]; rewrite (eqy_poweR r0 _) xy.
  1,7,13: by move => ->; rewrite poweRNyr.
  1,2,3,4: by move : NzNyOzy; rewrite not_orE; move => [H H0].
  1,4: by move => ->; rewrite (poweRyNr r0).
  1,3,4,5,6: by move : NzNyOzy; rewrite not_orE; move => [H H0].
  by rewrite -nfzar.
  by rewrite -r0 poweRe0.
  by rewrite -r0 poweRe0 in Bxr.
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
  ae_eq P [set: T] (fun t => (`|f t| `^ r)) (cst 0).
  Proof.
    move => H H0. rewrite unlock (gt_eqF H) => /poweR_eq0_nNr_eq0.
    
    move => H H0. rewrite unlock (gt_eqF H) => /poweR_eq0_eq0 H1.
    apply/ae_eq_integral_abs => //=.
      apply: (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r)) => //=.
      apply /measurable_poweR.
      exact : measurableT_comp. 
    under eq_integral => x _ do rewrite (gee0_abs (poweR_ge0 _ _)).
    apply H1. apply: integral_ge0 => t _. apply poweR_ge0.
  Qed.


(*
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
    
  Lemma poweR_Lnorme f r : r != 0%R ->
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
*)
*)
     
    


    