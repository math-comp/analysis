Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype landau.


Require Import hahn_banach.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory .

Local Open Scope ring_scope .
Local Open Scope classical_set_scope.
 

Section LinearContinuousBounded.
(* Everything in this section in stated for scalar functions.          *)
(* Making this available for linear function into normed spaces over R *)
  (* would just necessitate to replace normr lemmas by normm lemmas      *)
  
Variables (V  : normedModType R ) . 

Definition continuousR_at x (f : V -> R) :=   ( f @ x) --> (f x).

Lemma continuousR_atP x (f : V -> R) :
  (continuousR_at x f) <-> forall eps : posreal, \forall y \near f @ x, ball (f x) eps%:num y.
Proof.
  rewrite /continuousR_at. split.
   - by move => /flim_ballPpos. 
   - by move => /flim_ballPpos. 
Qed.


Definition continuousR_on F f :=  forall x , F x -> (continuousR_at x f ).


(* Case for linear function into normed spaces, slightly different than real functions*)
(*Lemma continuous_bounded0 (f : { linear V -> W}) :
  (continuous_at 0 f) -> 
   ( exists  r , (r > 0 ) /\ (forall x : V,   ( `|[f x]| ) <=  (`|[x]| ) * r  )  ) . 
Proof.
  move => /continuous_atP H. have H' : (0 < 1) by []. move : (H (1%:pos))  {H'} .
  rewrite (linear0 f) /( _ @ _ ) //=. move => H'{H}. 
  have : exists t , (t > 0) /\  forall x , ball 0 t x -> ball 0 1 (f x ).
    rewrite -!ball_normE /ball_.  (*rewrite sub0r*) admit.  

  move => [t [tp H]].
  exists (2*t^-1). split.  rewrite mulr_gt0.
    by [].
    by [].
    by rewrite invr_gt0.
  move => x ; case :  (boolp.EM (x=0)).
  - by move => -> ; rewrite (linear0 f) !normm0 //= mul0r. 
  - move => xneq0. 
    have normxle0 : `|[x]| > 0 .  rewrite normm_gt0.
    (*proving (x <> y) -> (x != y), where is it done ? *)
    case : (boolp.EM (x==0)).
    - move => /eqP x0. by have : False by apply : ( xneq0 x0). 
    - by move => /negP. 
    pose a := (  `|[x]|^-1 * t/2 ) *: x.
    (*going from ball to norm is done through ball_normE and unfolding ball_. 
    I looked a long time for this *)
    have ball0ta : ball 0 t a. 
     apply : ball_sym ; rewrite -ball_normE /ball_  subr0.
     rewrite normmZ absRE mulrC normedtype.R_AbsRingMixin_obligation_1.
     rewrite !gtr0_norm. rewrite mulrA mulrA divrr. 
     rewrite mul1r mulrC ltr_pdivr_mull. rewrite ltr_pmull.   
      (* 1 <2 ??? *) admit.
      by [].
      by [].  
      (* `|[x]| \is a GRing.unit *) admit.
      by  rewrite invr_gt0.
      apply : mulr_gt0. 
       by rewrite invr_gt0.
       by [].
    move : (H a ball0ta) ;rewrite -ball_normE /ball_ sub0r normmN {ball0ta}. 
    have  : ( f a =  ( (`|[x]|^-1) * t/2 ) *: ( f x)) .
      have : a = (`|[x]|^-1 * t/2) *: x + 0 by rewrite addrC add0r.  
      by move => -> ; rewrite linearP (linear0 f) addrC add0r.   
    move => -> . 
    rewrite normmZ absRE. rewrite normedtype.R_AbsRingMixin_obligation_1 !(gtr0_norm). 
    rewrite mulrC mulrC  -mulrA. rewrite -mulrA  ltr_pdivr_mull. 
    rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr. rewrite ltr_pdivr_mull. 
     move => Ht.  apply : ltrW ; rewrite mulrC -mulrA (mulrC t^-1). 
      by [].
      by [].
      by []. 
      by [].
      by rewrite invr_gt0.  
      apply : mulr_gt0. 
       by rewrite invr_gt0.
       by [].  
Admitted.*)



Lemma continuousR_bounded0 (f : {scalar V}) :
  (continuousR_at 0 f) -> 
   ( exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|[x]| ) * r  )  ) . 
Proof.
  move => /continuousR_atP H.
  have  H':  (0 < 1) by []. move : (H (1%:pos)) {H'}.
  rewrite (linear0 f) /( _ @ _ ) //= nearE => H0 {H}.
  (* I had a hard time finding nearE as it is not in the abstract *)
  move : (locally_ex H0) => [ tp  H] {H0}.
  move : H. 
  pose t := tp%:num. 
  exists (2*t^-1). split.  rewrite mulr_gt0.
    by [].
    by [].
    by rewrite invr_gt0.
  move => x ; case :  (boolp.EM (x=0)).
  -  by move => -> ; rewrite (linear0 f) normm0 normr0 //= mul0r. 
  - move => xneq0. 
    have normxle0 : `|[x]| > 0 .
      rewrite normm_gt0 ; case : (boolp.EM (x==0)).
    (*proving (x <> y) -> (x != y), where is it done ? *)
    - by move => /eqP x0 ; have : False by apply : ( xneq0 x0). 
    - by move => /negP. 
  pose a := (  `|[x]|^-1 * t/2 ) *: x.
  (*going from ball to norm is done through ball_normE and unfolding ball_. *)
  (* I looked a long time for this *) 
  have ball0ta : ball 0 t a.
   apply : ball_sym ; rewrite -ball_normE /ball_  subr0.
   rewrite normmZ absRE mulrC normedtype.R_AbsRingMixin_obligation_1.
   rewrite !gtr0_norm. rewrite mulrC.
   rewrite -mulrA -mulrA  ltr_pdivr_mull.
   rewrite mulrC -mulrA  gtr_pmull.
   rewrite invr_lt1.
     by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
     (* 2 Gring.Unit ?*)  apply/unitrPr. exists 2^-1. (*it can't be*)  admit.
     by [].
     by  rewrite mulr_gt0.
     by []. 
     by rewrite invr_gt0.
      apply : mulr_gt0. by rewrite invr_gt0.
     by [].
  move : (H a ball0ta) ;  rewrite ball_absE /ball_ sub0r absRE normrN. 
  have  : ( f a =  ( (`|[x]|^-1) * t/2 ) * ( f x)) .
  have : a = (`|[x]|^-1 * t/2) *: x + 0 by rewrite addrC add0r.  
   by move => -> ; rewrite linearP (linear0 f) addrC add0r.   
  move => -> .
  rewrite normedtype.R_AbsRingMixin_obligation_1 (gtr0_norm).  
  rewrite mulrC mulrC  -mulrA. rewrite -mulrA  ltr_pdivr_mull.  
  rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr.
  rewrite invf_div => Ht.
   by apply : ltrW. 
     by apply : mulr_gt0.
     by [].
     apply : mulr_gt0. 
     apply : mulr_gt0.
     by rewrite invr_gt0.
     by [].  
     by []. 
Admitted.


(* Unable to use linear_continuous of landau.v because I use f : {scalar V} *)
(* instead of f : {linear V -> W } *)

(* Thus I adapt the proof to scalar functions, and to notations without =0 *)
(* that I can't manage to use, as =O_0 does not typecheck                  *)

Check eqO_exP.
Check nearE. Check bigO_exP. Check linearB. 

Lemma scalar_continuous (f: {scalar V }) :
  (exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|[x]| ) * r)) -> continuousR_at 0 f .
Proof.
  move => [r [lt0r H]]. 
  apply/flim_ballP => eps lt0eps.  rewrite nearE (linear0 f).
  rewrite /( _ @ _). rewrite /([filter of _ ]) /(_ @^-1` _). Search "neigh" "".
  Print neigh. Print open. Print locally. 
  Search _  "open".
Admitted.  
(*  suff ballf0 : ball 
  rewrite -ball_normE.  Unset Printing Notations.
  rewrite ball_normm.
  -ball_. 
  
  Search "locally".
  rewrite locallynorm.
  Unset Printing Notations. move => //=.
  near +oo => k .
  Check flim_normP. Check eqO_exP.
apply/flim_normP => _/posnumP[e]; rewrite !near_simpl.
  rewrite (ler_lt_trans (near flip k _ _)) // -ltr_pdivl_mull //.
  near: y; apply/locally_normP.
    by eexists; last by move=> ?; rewrite /= sub0r normmN; apply.

    
move=> /eqO_exP [_/posnumP[k0] Of1] x.
apply/flim_normP => _/posnumP[e]; rewrite !near_simpl.
rewrite (near_shift 0) /= subr0; near=> y => /=.
rewrite -linearB opprD addrC addrNK linearN normmN; near: y.
suff flip : \forall k \near +oo, forall x, `|[f x]| <= k * `|[x]|.
  near +oo => k; near=> y.
  rewrite (ler_lt_trans (near flip k _ _)) // -ltr_pdivl_mull //.
  near: y; apply/locally_normP.
  by eexists; last by move=> ?; rewrite /= sub0r normmN; apply.
have /locally_normP [_/posnumP[d]] := Of1.
rewrite /cst [X in _ * X]absr1 mulr1 => fk; near=> k => y.
case: (ler0P `|[y]|) => [|y0].
  by rewrite normm_le0 => /eqP->; rewrite linear0 !normm0 mulr0.
have ky0 : 0 <= k0%:num / (k * `|[y]|).
  by rewrite pmulr_rge0 // invr_ge0 mulr_ge0 // ltrW.
rewrite -[X in _ <= X]mulr1 -ler_pdivr_mull ?pmulr_rgt0 //.
rewrite -(ler_pmul2l [gt0 of k0%:num]) mulr1 mulrA -[_ / _]ger0_norm //.
rewrite -normm_s.
have <- : GRing.Scale.op s_law =2 s by rewrite GRing.Scale.opE.
rewrite -linearZ fk //= normmB subr0 normmZ absRE ger0_norm //.
rewrite invfM mulrA mulfVK ?lt0r_neq0 // ltr_pdivr_mulr //.
by rewrite mulrC -ltr_pdivr_mulr //; near: k; apply: locally_pinfty_gt.
Grab Existential Variables. all: end_near. Qed.

Lemma bounded_continuousR  (f : { scalar V }) : 
  ( exists  r, (0 < r) /\ (forall x : V,   ( `|f x| ) <=   (`|[x]| ) * r) ) ->
  continuous f.  
Proof.
  pose lincont := (linear_continuous). move : (lincont V R^o f).
  Check bigOP. Check bigO_exP. Check bigOE. rewrite -eqOE.  /( _ =O_(0 : V) _ ).
  Search "eqO"  in landau.
  Check eqOP. rewrite 
  apply :  linear_cont0_continuous . 
  apply : (proj2 (continuous_atP 0 f)). 
Admitted.



Lemma bounded_continuousR  (f : {scalar V}) : 
  ( exists  r : posreal, (forall x : V,   ( `|f x| ) <=   (`|[x]| ) * r%:num  )  ) ->
  continuous f.  
Proof.
  (*use linear_continuous of landau and landau_cst_bounded*)
  move => H.
  apply :  linear_cont0_continuousR . 
  apply : (proj2 (continuousR_atP 0 f)). 
Admitted. *)

Lemma continuousR0_continuous (f : {scalar V}):
  continuousR_at 0 f -> continuous f.
Proof.
  move => cont0f x. Search flim "linear".
Admitted.

End LinearContinuousBounded.


Section HBGeomNormed.
Variable ( V : normedModType R) ( F G: pred V ) (f : {scalar V}) ( F0 : F 0).
Variable (Flin : (forall (v1 v2 : V) (l : R_realFieldType), F v1 -> F v2 -> F (v1 + l *: v2))).
Variable Choice_prop :  forall T U (P : T -> U -> Prop),
    (forall t : T, exists u : U,  P t u) -> (exists e, forall t,  P t (e t)).


 (* Upper bound *)
Definition ubd (A : set R) (a : R) := forall x, A x -> x <= a.                                                                                                  

 (* Lower bound *)
Definition ibd (A : set R) (a : R) := forall x, A x -> a <= x. 


(*Unset Printing Notations.*)
(*Set Printing Coercions.*)

(* From the sup properties proven in bool in reals, we deduce the version in Prop 
  that we used in our proof of hahn_banacH *)
Lemma mymysup : forall (A : set R) (a m : R),
     A a -> ubd A m ->
     {s : R | ubd A s /\ forall u, ubd A u -> s <= u}.
Proof.
  move => A a  m  Aa majAm.  
  have : (has_sup  (in_set A)).
  split . 
  - by exists a ; rewrite in_setE.
  - exists m ; rewrite in_setE // => x ;apply : propF ; rewrite negb_imply //= . 
    move  => /andP ; apply and_ind; rewrite in_setE  => Ax /negP nxm.
      by apply : (nxm (majAm x Ax)).
  move => /has_supP has_sup_A {m majAm a Aa}. 
  exists (real_sup (in_set A)).  
  split.  
  - move => x Ax ; move : (real_sup_ub (has_sup_A)) => //= /ubP H.
    have Axb : x \in in_set A by rewrite in_setE.
    by apply : (H x Axb).  
  - move => x xmajA.
    have ubdA : is_upper_bound A x by move => y Ay ; move : (xmajA y Ay) ;  move => /RleP.   
    (*I spent a long time looking for RleP*)
    have majAxb : is_upper_bound  (fun x : R => in_set A x) x.
    by move =>y ; rewrite in_setE => Ay ; move : (xmajA y Ay) ; move => /RleP.   
    move : (proj2 (real_sup_is_lub has_sup_A) x majAxb).
    by move => /RleP.
Qed.     
 

Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  ibd A m ->
     {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.
Admitted.


Notation myHB := (hahn_banach.HahnBanach (boolp.EM) Choice_prop mymysup mymyinf) .

Theorem HB_geom_normed :
  (forall x , F x -> continuousR_at x f)
   -> exists g : {scalar V} , ( continuous g ) /\ ( forall x, F x -> (f x = g x) ) .  
Proof.
  move   => H.
  move : (continuousR_bounded0 (H 0 F0)) => [r [ltr0 fxrx]] {H}.
  pose p := fun x : V => `|[x]|*r.
  have convp: convex p.
   move => v1 v2 l m lm1 //=.  rewrite !/( p _) !mulrA -mulrDl.
   have l_m1 : (l = 1 - m). rewrite -lm1. (*m - m =0 *) admit.
   rewrite l_m1. rewrite  [(1-_)*_]mulrDl -addrA.
   have blou : `|[(1 - m) *: v1 + m *: v2]| <= `|(1 - m)| *`|[ v1]| + `| m| *`|[v2]|.
   rewrite -!absRE -!normmZ.  by apply : ler_normm_add.
   admit.
 Check (myHB F F0 Flin convp ).  


Admitted. 

End HBGeomNormed.


Module TopVec.
 
 Variable (R : realFieldType).
 
 Record mixin_of1 ( V : lmodType R) : Type := Mixin { base :  Type ;  
                     vec :  GRing.Lmodule.class_of R base ;
                     top : Topological.class_of base}. 
 
 Variable (T : topologicalType). 
  
 Record mixin_of2 ( T : topologicalType) : Type := Mixin {  
                       vec :  GRing.Lmodule.class_of R T ;
                       _ : topology.hausdorff T ;                               
                       (* _ : continuous  (fun t => GRing.Zmodule.add (vec) t )  ;  *)
                       (* _ : continuous (GRing.Lmodule.scale vec )  *) }.
                                                    }.

 Structure type := Pack {sort; _ : class_of sort}.

End TopVec.



Module convTopVec.

(*Add convex. Show that they are UniformTypes. *)

End convTopvec.  