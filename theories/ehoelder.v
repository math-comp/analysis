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
Local Open Scope ereal_scope.

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

Declare Scope Lnorme_scope.

(*
Definition ifpoweR {R : realType} (x : \bar R) r := 
  if x is x'%:E 
  then (x' `^ r)%:E 
  else 
    if x is +oo then 
      if r == 0%R then 1 else +oo
    else 
      if r == 0%R then 1 else 0%R.

Lemma poweR_ifpoweR {R : realType} : @poweR R = ifpoweR.
Proof.
  by apply funext => x; case : x => [r| //= | //=].
Qed.
*)


Definition lne {R : realType} (x : \bar R) :=
  match x with
  | x'%:E => (ln x')%:E
  | +oo => +oo
  | -oo => 0
  end.

Definition geo_mean {d} {T : measurableType d} {R : realType} (P : probability T R) (g : T -> \bar R) := 
expeR (\int[P]_x (lne (g x)))%E.

HB.lock Definition Lnorme {d} {T : measurableType d} {R : realType} (P : probability T R) 
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

  Lemma Lnorm1 f : 'Ne_1[f] = \int[P]_x `|f x|.
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

  Lemma measurable_poweR r :
  measurable_fun [set: \bar R] (@poweR R ^~ r).
  Proof.
  move => _ /= B H.
  rewrite setIidr; last first. 
    apply subsetT.
  Print poweR.
  rewrite [X in measurable X]
  (_ : (poweR^~ r @^-1` B) = 
  if (r == 0%R) then (
    if 1 \in B then [set : \bar R] else set0 ) 
  else
  (B `&` [set +oo]) `|` (if 0 \in B then [set -oo] else set0) `|`
  EFin @` (
    @powR R ^~ r @^-1` (fine @` (B `\` [set -oo; +oo]))
          )
  ); last first. 
  case (r == 0%R) eqn:H0; apply/seteqP; 
  split => [a //= H1 //= | a //= H1 //=].
  - (*r == 0*)
  move : H1; rewrite (eqP H0) //= => H1. 
  -- split => //=; apply poweRe0.
  -- destruct H1 as [H1 H2]; apply H1.
  - (*r != 0*)
  -- (*B <= B*)
     move : H1; rewrite /poweR H0 => H1.
     case a as [s| | ].
  --- (*a = s %:E*) 
      right. 
      exists s; last first => //=. 
      exists (s%:E `^ r); last first =>  //=.
      split => //=. rewrite not_orE //=.
  --- (*a = +oo*)
      repeat left; split => //=; rewrite not_orE //=.
  --- (*a = -oo*)
      left. right. case : ifPn => //=. move => H2.
      rewrite notin_setE in H2. contradiction.
  -- (*B <= A*)
  --- case H1.
  ---- case.
  ----- move => H2. destruct H2 as [H2 H3]. 
       by move : H2; rewrite H3 //= H0.
  ----- case : ifPn => //=. move => H2 H3.
       rewrite H3 //= H0. by rewrite in_setE in H2.
  ---- move => H2. destruct H2 as [b [c [H2 H3]] H4].
       rewrite not_orE in H3. destruct H3 as [H3 H6].
       case c as [s | | ]. 
  ----- move : H5 H2 => //= => H5. 
        by rewrite H5 -H4 poweR_EFin.
  ----- contradiction.
  ----- contradiction.
  
       

    
  Qed.



  Lemma Lnorme_eq0_eq0 r f : 
  (0 < r)%R -> 
  measurable_fun setT f ->
  'Ne_r%:E[f] = 0 -> 
  ae_eq P [set: T] (fun t => (`|f t| `^ r)) (cst 0).
  Proof.
    move => H H0. rewrite unlock (gt_eqF H) => /poweR_eq0_eq0 H1.
    apply/ae_eq_integral_abs => //=.
      Search (poweR).
      apply: (@measurableT_comp _ _ _ _ _ _ (@poweR R ^~ r)) => //=.



End Lnorme_properties.