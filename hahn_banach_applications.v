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
(* Everything in this section in stated for scalar functions.                       *)
(* They will be turned into lemmas for linear functions into normed spaces soon     *)
  
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
   rewrite invf_lt1.
     by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
     by []. 
     by  rewrite mulr_gt0.
     by []. 
     by rewrite invr_gt0.
     apply : mulr_gt0.
         by rewrite invr_gt0 //=.
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
    by   apply : ltrW.
    by  apply : mulr_gt0 .
    by [].   
     apply : mulr_gt0. 
    apply : mulr_gt0.
       rewrite invr_gt0 //=.
     by [].  
     by []. 
Qed.


(* Unable to use linear_continuous of landau.v because I use f : {scalar V} *)
(* instead of f : {linear V -> W } *)

(*  I can't manage to use bigO, as =O_0 does not typecheck                  *)

Lemma scalar_continuous (f: {scalar V }) :
  (exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|[x]| ) * r)) -> continuousR_at 0 f .
Proof.
  move => [r [lt0r H]].  
  apply/(continuousR_atP 0) => eps ;  rewrite nearE  (linear0 f).
  rewrite /( _ @ _) /([filter of _ ]) /(_ @^-1` _);  apply/locallyP.
  (* locally is proved via an existential. Long search *)
  exists (eps%:num *2^-1*r^-1).  
   by  rewrite !divr_gt0. 
   move => a ; rewrite -ball_normE  /(ball_)  addrC addr0 normmN.
   move => na ; rewrite ball_absE /(ball_) addrC addr0 absRE normrN.
   have na0: `|[a]| * r <= eps%:num / 2 by  apply : ltrW ; rewrite -ltr_pdivl_mulr. 
  have faeps2 : `|f a| <= eps%:num /2 by exact : ler_trans ( H a) na0.
  have eps2eps : eps%:num  / 2 < eps%:num  .
  rewrite gtr_pmulr.
  rewrite invf_lt1 .
    by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
    by [].     
    by [].       
 Search _  ( _ <= _ ) ( _ < _ ). 
 (* going from <= to < *)
Admitted.

Lemma continuousR0_continuous (f : {scalar V}):
  continuousR_at 0 f -> continuous f.
Proof.
  move => cont0f x. Search "flim".
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
  that we used in our proof of hahn banach theorem in hahn_banach.v *)
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

Check normm_gt0. Check normr_gt0.
Search _ ( 0 <= `|[_]|).

Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  ibd A m ->
     {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.
Admitted.


Notation myHB := (hahn_banach.HahnBanach (boolp.EM) Choice_prop mymysup mymyinf).
Check myHB.



Check normr_idP.  
Theorem HB_geom_normed :
 continuousR_on F f ->
  exists g : {scalar V} , ( continuous g ) /\ ( forall x, F x -> (f x = g x) ) .  
Proof.
  move   => H.
  move : (continuousR_bounded0 (H 0 F0)) => [r [ltr0 fxrx]] {H}.
  pose p := fun x : V => `|[x]|*r.
  have convp: convex p. 
   move => v1 v2 l m [lt0l lt0m] addlm1 //= ; rewrite !/( p _) !mulrA -mulrDl.
   have normp : `|[l *: v1 + m *: v2]|  <= (l * `|[v1]| + m * `|[v2]|).
    have labs : `|l| = l by apply/normr_idP.
    have mabs: `|m| = m by apply/normr_idP.
   rewrite -[in(_*_)]labs -[in(m*_)]mabs. rewrite -!absRE -!normmZ.
   apply : ler_normm_add.
   apply : ler_pmul.
    by apply : normm_ge0.
    by apply : ltrW.
    by [].
    by [].   
  Check myHB.
    
Admitted. 



End HBGeomNormed.

Check HB_geom_normed. 

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