Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp ereal reals Rstruct.
Require Import classical_sets posnum topology prodnormedzmodule normedtype.
 

Require Import hahn_banach.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope .
Local Open Scope classical_set_scope.
 

Section LinearContinuousBounded.
(* Everything in this section in stated for scalar functions.                 *)
(* They should be turned into lemmas for linear functions into normed spaces  *)
  
Variables (*R: realFieldType*) (V  : normedModType R). 

Definition continuousR_at x (f : V -> R) :=   (f @ x) --> (f x).
(*Not working with R : RealFieldtype *)

Lemma continuousR_atP x (f : V -> R) :
(continuousR_at x f) <-> forall eps : posreal, \forall y \near f @ x, ball (f x) eps%:num y.
Proof.
  rewrite /continuousR_at. split ; by move => /flim_ballPpos.  
Qed.

Lemma continuousR_bounded0 (f : {scalar V}) :
  (continuousR_at 0 f) -> 
   ( exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|x| ) * r  )  ) . 
Proof.
  move => /continuousR_atP H. 
  have  H':  (0 < 1) by [].
  move : (H (1%:pos)) {H'}.
  rewrite (linear0 f) /( _ @ _ ) //= nearE => H0 {H}. 
  (* I had a hard time finding nearE as it is not in the abstract *)
  move : (locally_ex H0) => [ tp  H] {H0} ;  pose t := tp%:num. 
  move : H. 
  exists (2*t^-1). split; first by [].
  move => x ; case :  (boolp.EM (x=0)).
  - by move => -> ; rewrite (linear0 f) !normr0 //= mul0r. 
  - move => xneq0. 
    have normxle0 : `|x| > 0 .
      rewrite normr_gt0 ; case : (boolp.EM (x==0)).
    (*proving (x <> y) -> (x != y), where is it done ? *)
     - by move => /eqP x0 ; have : False by apply: (xneq0 x0). 
     - by move => /negP. 
  pose a := (  `|x|^-1 * t/2 ) *: x.
  (*going from ball to norm is done through ball_normE and unfolding ball_. *)
  (* I looked a long time for this *) 
  have ball0ta : ball 0 t a. 
   apply : ball_sym ; rewrite -ball_normE /ball_  subr0.
   rewrite normmZ mulrC normrM. 
   rewrite !gtr0_norm //= mulrC. 
   rewrite -mulrA -mulrA  ltr_pdivr_mull //=. 
   rewrite mulrC -mulrA  gtr_pmull. 
   rewrite invf_lt1 //=. 
     by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
     by rewrite mulr_gt0 //=. 
   apply : mulr_gt0.  
     by apply: posnum_gt0.
     by rewrite invr_gt0 //=.
  move : (H a ball0ta); rewrite /ball /ball_ //= sub0r normrN. 
  suff ->  : ( f a =  ( (`|x|^-1) * t/2 ) * ( f x)) .
     rewrite normrM gtr0_norm. 
     rewrite mulrC mulrC  -mulrA  -mulrA  ltr_pdivr_mull //=.   
  rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr.
  rewrite invf_div => Ht. 
    by   apply : ltW.
    by  apply : mulr_gt0.
    apply : mulr_gt0 ; last by [].
       apply : mulr_gt0 ; last by [].
      by rewrite invr_gt0 //=.
   suff -> : a = (`|x|^-1 * t/2) *: x + 0  by  rewrite linearP (linear0 f) addrC add0r.
     by rewrite addrC add0r.
Qed.     

Lemma bounded_continuousR0 (f: {scalar V }) :
  (exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|x| ) * r))
  -> continuousR_at 0 f .
Proof.
  move => [r [lt0r H]].
  apply/(continuousR_atP 0) => eps; rewrite nearE (linear0 f).
  rewrite /( _ @ _) /([filter of _ ]) /(_ @^-1` _).
  apply/locallyP.  
  (* locally_ is proved via an existential which gives 
    the radius of the ball contained in locally *)
  exists (eps%:num *2^-1*r^-1).  
   by  rewrite !divr_gt0. 
   move => a ; rewrite -ball_normE  /(ball_)  addrC addr0 normrN.
   move => na ; rewrite /ball /(ball_) //= addrC addr0 normrN.
  have na0: `|a| * r <= eps%:num / 2. Check ltW. by  apply : ltW; rewrite -ltr_pdivl_mulr. 
  have faeps2 : `|f a| <= eps%:num /2 by exact : le_trans (H a) na0.
  have eps2eps : eps%:num  / 2 < eps%:num. rewrite gtr_pmulr ; last by []. 
    by  rewrite invf_lt1 ; have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ;
      apply : ltr_spaddr.
  by apply : (le_lt_trans faeps2).
Qed.

   
Lemma continuousRat0_continuous (f : {scalar V}):
  continuousR_at 0 f -> continuous f.
Proof.
 move => cont0f  x ; rewrite flim_locally => eps pos.
 move : (continuousR_bounded0 cont0f) => [r [rpos Hr]]. 
 rewrite nearE /ball_ //.
 rewrite /(_@_) /[filter of _] locallyP -ball_normE /ball_.
 exists (eps /r).
  -  by rewrite mulr_gt0 //= invr_gt0 .
  - move => y Hxy.
    rewrite /(_ @^-1`_) /ball //= -(linearB f).   
    suff : `|x - y| * r < eps by apply : le_lt_trans (Hr (x-y)).
    by rewrite -ltr_pdivl_mulr.
Qed.      


End LinearContinuousBounded.




Section HBGeom.

Variable ( V : normedModType R) ( F : pred V ) (f :  V -> R) ( F0 : F 0).
Hypothesis (linF : (forall (v1 v2 : V) (l : R_realFieldType),
                       F v1 -> F v2 -> F (v1 + l *: v2))).
Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 -> 
                              f (v1 + l *: v2) = f v1 + l * (f v2).


Hypothesis (Choice_prop : ((forall T U  (Q : T -> U -> Prop),
                      (forall t : T, exists u : U,  Q t u) -> (exists e, forall t,  Q t (e t))))).

 

(*Looked a long time for within *)
Definition continuousR_on ( G : set V ) ( f : V -> R) :=
  (forall x, (f @ (within G (locally x))) --> f x).

(*Do we need to have F x ?*)
Definition continuousR_on_at (G : set V ) (x : V ) (g : V -> R)  :=
  (g @ (within G (locally x)) --> f x).

Lemma continuousR_scalar_on_bounded :
  (continuousR_on_at F 0 f) ->
  (exists  r , (r > 0 ) /\ (forall x : V, F x ->   (`|f x| ) <=  `|x| * r)).
Proof.
  rewrite /continuousR_on_at.
  move  => /flim_ballPpos  H.
    have  H':  (0 < 1) by []. 
  move : (H (1%:pos)) {H'}.
  have f0 : f 0 = 0.
     suff -> : f 0 = f (0 + (-1)*: 0) by rewrite linfF // mulNr mul1r addrN. 
     by rewrite scaleNr scaler0 addrN.
  rewrite near_simpl /( _ @ _ ) //= nearE /(within _ ) near_simpl f0.
  rewrite -locally_nearE => H0 {H} ; move : (locally_ex H0) => [tp H] {H0}.  
  pose t := tp%:num .
  exists (2*t^-1). split=> //. 
  move => x. case :  (boolp.EM (x=0)).
  -  by move => -> ; rewrite f0 normr0 normr0 //= mul0r. 
  - move/eqP => xneq0 Fx. 
  pose a : V := (`|x|^-1 * t/2 ) *: x.
  have Btp : ball 0 t a.
   apply : ball_sym ; rewrite -ball_normE /ball_  subr0.
   rewrite normmZ mulrC (*normedtype.R_AbsRingMixin_obligation_1*) normrM.
   rewrite !gtr0_norm //= ; last by rewrite  pmulr_lgt0 // invr_gt0 normr_gt0.
   rewrite mulrC -mulrA -mulrA  ltr_pdivr_mull; last by rewrite normr_gt0.
   rewrite mulrC -mulrA  gtr_pmull. 
   rewrite invf_lt1 //=.
     by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
   by  rewrite pmulr_lgt0 //  !normr_gt0.  
 have Fa : F a by rewrite -[a]add0r; apply: linF. 
 have :  `|f a| < 1.
    by move: (H _ Btp Fa); rewrite /ball /ball_ //= sub0r normrN.
  suff ->  : ( f a =  ( (`|x|^-1) * t/2 ) * ( f x)) .
     rewrite (*normedtype.R_AbsRingMixin_obligation_1*)normrM (gtr0_norm) //.
     rewrite mulrC mulrC  -mulrA  -mulrA  ltr_pdivr_mull //= ;
       last by rewrite normr_gt0.
     rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr //.
     by rewrite invf_div => Ht; apply : ltW.
     by  rewrite !mulr_gt0 // invr_gt0 normr_gt0. 
 suff -> : a = 0+ (`|x|^-1 * t/2) *: x by rewrite linfF // f0 add0r.
 by rewrite add0r.  
Qed. 


 (* Upper bound *)
Definition ubd (A : set R) (a : R) := forall x, A x -> x <= a.                                                                                                  

 (* Lower bound *)
Definition ibd (A : set R) (a : R) := forall x, A x -> a <= x. 

(* From the sup properties proven in bool in reals,
   we deduce the version in Prop that we used in our proof
    of hahn banach theorem in hahn_banach.v *)

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
    have ubdA : is_upper_bound A x
      by move => y Ay; move : (xmajA y Ay); move => /RleP.   
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


Notation myHB :=
  (hahn_banach.HahnBanach (boolp.EM) Choice_prop mymysup mymyinf F0 linF linfF).


(*Isn't the assumption too strong ? Is really continuousR_on what we want ? *)
Theorem HB_geom_normed :
  continuousR_on_at F 0  f ->
  exists g : {scalar V} , ( continuous g ) /\ ( forall x, F x -> (g x = f x) ).  
Proof.
 move => H; move: ( continuousR_scalar_on_bounded H) => [r [ltr0 fxrx]] {H}.
 pose p := fun x : V => `|x|*r ;   have convp: convex p. 
   move => v1 v2 l m [lt0l lt0m] addlm1 //= ; rewrite !/( p _) !mulrA -mulrDl.
   suff : `|l *: v1 + m *: v2|  <= (l * `|v1| + m * `|v2|).
     move => h ; apply : ler_pmul  ; last by [].
     by apply : normr_ge0.
     by apply : ltW. 
       by [].
   have labs : `|l| = l by apply/normr_idP.
   have mabs: `|m| = m by apply/normr_idP.
   rewrite -[in(_*_)]labs -[in(m*_)]mabs -!normmZ.
   by apply : ler_norm_add.
 have majfp : forall x, F x -> f x <= p x.      
   move => x Fx; rewrite /(p _) ; apply : le_trans ; last by [].
   apply : le_trans.
   apply : ler_norm.
   by apply : (fxrx x Fx).   
 move : (myHB convp majfp) => [ g  [majgp  F_eqgf] ] {majfp}. 
 exists g ;  split ; last by []. 
  move => x ; rewrite /(continuousR_at) ; apply : (continuousRat0_continuous).
  apply : bounded_continuousR0 ; exists r.  
   split; first by [].  
   move => x0 ; rewrite ler_norml ; apply /andP ; split.
   rewrite -sub0r (ler_subl_addr) ; move : (majgp (-x0)) ; rewrite /(p _) normrN (linearN g).  
   by  rewrite -sub0r ler_subl_addl.
   by exact : majgp x0.  
Qed.

End HBGeom.


(*Defining induced topologies*)
(*Definition locally_restricted (G : set V)  (x : V) :=
  fun A => (A= setT) \/ (exists B, locally x B /\ (B `&` G = A)).


Lemma setTS ( Q : set V) : setT `<=` Q -> Q = setT. 
Proof.
  by move => H ; apply : eqEsubset.  
Qed.

Locate within. 

(*The following does not work as this is not a Filter on V *)
(*locally c'est les voisinages et neigh c'est les voisinages ouverts *)
Lemma restricted_filter  (G : set V) (x: V)  :
  Filter (locally_restricted G x) .
Proof.
  split.
  - by left. 
  - move => P Q  xP xQ ; case : xP ; case : xQ. 
   - by move => -> -> ; left ; rewrite setIT. 
   - move => [BQ [xB BGQ]] -> ; right ; exists BQ ; split.
       by [].
       by rewrite ![setT `&`_ ]setIC !setIT.  
   - move => -> [BP [xB BPQ]] ; right ; exists BP ; split.
       by [].
       by rewrite setIT.  
   -  move => [BP [xBP BPQ]] [BQ [xBQ BGQ]]  ; right ; exists (BP `&` BQ) ; split.
       by apply filterI. 
       rewrite -BPQ -BGQ . rewrite setIA. admit. (*assoc and com*)
   - move => P Q SPQ xPG ; case : xPG.   
       by move => PT ; left ; apply setTS ; rewrite -PT.
       move => [ B [xB BGP]] ; right ;  exists (B `|` (Q `\` P)) ; split.
        - have Bsub : B `<=` (B `|` Q`\`P) by move => z Bz ; left.
          by apply :   (filterS Bsub). rewrite setDE. admit. (* associativity and rewriting*)
 Admitted.  


Definition continuourR_on (G : set V) (f : V -> R) :=
  forall x , G x -> ( (f @ locally_restricted G x) --> f x).*)

(*Lemma continuousR_bounded0 (f : {scalar V}) :
  (continuousR_at 0 f) -> 
   ( exists  r , (r > 0 ) /\ (forall x : V,   ( `|f x| ) <=  (`|[x]| ) * r  )  ) . 
Proof.
  move => /continuousR_atP H. 
  have  H':  (0 < 1) by [].
  move : (H (1%:pos)) {H'}.
  rewrite (linear0 f) /( _ @ _ ) //= nearE => H0 {H}. 
  (* I had a hard time finding nearE as it is not in the abstract *)
  move : (locally_ex H0) => [ tp  H] {H0} ;  pose t := tp%:num. 
  move : H. 
  exists (2*t^-1). split; first by [].
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
   rewrite !gtr0_norm //=. rewrite mulrC. 
   rewrite -mulrA -mulrA  ltr_pdivr_mull //=. 
   rewrite mulrC -mulrA  gtr_pmull. 
   rewrite invf_lt1 //=. 
     by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
     by rewrite mulr_gt0 //=. 
   apply : mulr_gt0 ; last by [].
     by rewrite invr_gt0 //=.
  move : (H a ball0ta) ;  rewrite ball_absE /ball_ sub0r absRE normrN. 
  suff ->  : ( f a =  ( (`|[x]|^-1) * t/2 ) * ( f x)) .
     rewrite normedtype.R_AbsRingMixin_obligation_1 (gtr0_norm). 
     rewrite mulrC mulrC  -mulrA  -mulrA  ltr_pdivr_mull //=.   
  rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr.
  rewrite invf_div => Ht. 
    by   apply : ltrW.
    by  apply : mulr_gt0.
    apply : mulr_gt0 ; last by [].
       apply : mulr_gt0 ; last by [].
      by rewrite invr_gt0 //=.
   suff -> : a = (`|[x]|^-1 * t/2) *: x + 0  by  rewrite linearP (linear0 f) addrC add0r.
   by rewrite addrC add0r.  
Qed.*)
