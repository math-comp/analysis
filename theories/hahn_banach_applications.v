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
  (* TODO : update PR adapted and rebase hahnbanah and banach steinhauss on it *)
  
Variables (R: numFieldType) (V  W: normedModType R).

Lemma ball_nonempty (x: V) (a: R): a > 0 -> exists y, (ball x a y /\ `|x -y|>0).
Admitted.

Lemma linear_boundedP (f: {linear V -> W}) : bounded_on f (nbhs (0:V)) <->
        (exists r, 0 <= r /\ (forall x : V, `|f x| <=  `|x| * r )).
Proof.
  split.
  -  move => /ex_bound [M /nbhs_ballP [a a0 Ba0]] //=.
     exists (M * 2 *a^-1).
     split.
     - rewrite !mulr_ge0 //= ?invr_ge0 ; last by apply: ltW.
       move : (Ba0 0 (ballxx 0 a0 )); rewrite linear0 normr0 //=.
     - move => x. rewrite mulrA ler_pdivl_mulr //=.
       case: (boolp.EM (x=0)).
       - by move => ->; rewrite linear0 !normr0 !mul0r.
       - move => /eqP x0 ; rewrite -lter_pdivr_mull ?normr_gt0 //=. 
         rewrite [X in ( _ <= X)]mulrC -lter_pdivr_mull //=. 
         have ->: 2^-1 *(`|x|^-1 * (`|f x| * a))=`|f ((2^-1 * `|x|^-1 * a)*:x)|.
           rewrite linearZ normmZ !normrM !ger0_norm ?invr_ge0 //= ?ltW //=.
           by rewrite mulrA mulrA mulrAC.
         apply: Ba0 ;rewrite -ball_normE /= sub0r normrN ?normr_gt0 //=.
         rewrite normmZ !normrM !normrV ?unitfE ?normrE // !ger0_norm ?ltW //=.
         rewrite mulrAC -mulrA -mulrA [_ * (_ * a)]mulrA.
         rewrite mulVr ?unitf_gt0 //= ?normr_gt0 //= mul1r.
         rewrite mulrC gtr_pmulr ?invr_lte1 //= ?unitfE ?ltr_spaddr //=.
     - move => [r [r0 fr]]; apply/ex_bound; exists r.
       rewrite nbhs_ballP; exists 1; first by [].
       move=> x; rewrite -ball_normE //= sub0r normrN => x1; apply: le_trans.
       apply: fr.
       rewrite -[X in _ <= X]mul1r; apply: ler_pmul; rewrite ?normr_ge0 //=.
       by apply: ltW.
Qed.

Lemma linear_continuous0 (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_on f (nbhs (0:V)).
Proof.
move=> /cvg_ballP /(_ _ ltr01) .
rewrite linear0 /= nearE => /nbhs_ex[tp ball_f]; apply/linear_boundedP.
pose t := tp%:num; exists (2 * t^-1); split => // x.
have [->|x0] := eqVneq x 0; first by rewrite linear0 !normr0 mul0r.
have /ball_f : ball 0 t ((`|x|^-1 * t /2) *: x).
  apply: ball_sym; rewrite -ball_normE /ball_  subr0 normmZ mulrC 2!normrM.
  rewrite 2!mulrA normrV ?unitfE ?normr_eq0 // normr_id.
  rewrite divrr ?mul1r ?unitfE ?normr_eq0 // gtr0_norm // gtr_pmulr //.
  by rewrite gtr0_norm // invr_lt1 // ?unitfE // ltr1n.
rewrite -ball_normE //= sub0r normrN linearZ /= normmZ -mulrA normrM.
rewrite normrV ?unitfE ?normr_eq0 // normr_id -mulrA.
rewrite ltr_pdivr_mull ?mulr1 ?normr_gt0 // -ltr_pdivl_mull ?normr_gt0 //.
by rewrite gtr0_norm // invf_div mulrC => /ltW.
Qed.

Lemma linear_bounded0 (f : {linear V -> W}) :
 bounded_on f (nbhs (0:V)) -> {for 0, continuous f} .
Proof.
move=> /linear_boundedP [r]; rewrite le0r=>  [[/orP r0]]; case: r0.
- move/eqP => -> fr; apply: near_cst_continuous; near=> y.
  by move: (fr y); rewrite mulr0 normr_le0; apply/eqP.
- move => r0 fr;  apply/cvg_ballP => e e0. 
  rewrite nearE linear0 /= nbhs_ballP.
  exists (e / 2 / r); first by rewrite !divr_gt0.
  move=> x; rewrite -2!ball_normE /= 2!sub0r 2!normrN => xr.
  have /le_lt_trans -> // : `|f x| <= e / 2.
  by rewrite (le_trans (fr x)) // -ler_pdivl_mulr // ltW.
  by rewrite gtr_pmulr // invr_lt1 // ?unitfE // ltr1n.
  Grab Existential Variables. by end_near.
Qed.

Lemma continuousfor0_continuous (f : {linear V -> W}) :
  {for 0, continuous f} -> continuous f.
Proof.
move=> /(linear_continuous0) /linear_boundedP [r].
rewrite le0r=>  [[/orP r0]]; case: r0 => r0 fr x.
- admit. 
- rewrite cvg_to_locally => e e0; rewrite nearE /= nbhs_ballP.
  exists (e / r). 
   - by rewrite mulr_gt0 //= invr_gt0. 
   - move=> y; rewrite -!ball_normE //= => xy; rewrite -linearB.
     by rewrite (le_lt_trans (fr (x - y))) // -ltr_pdivl_mulr.
Admitted.

Lemma linear_bounded_continuus (f : {linear V -> W}) :
  bounded_on f (nbhs (0 : V)) <-> continuous f.
Proof.
  split; first by move=> /linear_bounded0; apply continuousfor0_continuous.
  by move => /(_ 0) /linear_continuous0 /=.
Qed.

End LinearContinuousBounded.




Section HBGeom.

Variable (R : realType) (V : normedModType R) (F : pred V) (f :  V -> R^o) (F0 : F 0).
Hypothesis (linF : (forall (v1 v2 : V) (l : R),
                       F v1 -> F v2 -> F (v1 + l *: v2))).
Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 ->
                              f (v1 + l *: v2) = f v1 + l * (f v2).


Hypothesis (Choice_prop : ((forall T U  (Q : T -> U -> Prop),
                      (forall t : T, exists u : U,  Q t u) -> (exists e, forall t,  Q t (e t))))).


(*Looked a long time for within *)
Definition continuousR_on ( G : set V ) ( f : V -> R^o) :=
  (forall x, (f @ (within G (nbhs x))) --> f x).

(*Do we need to have F x ?*)
Definition continuousR_on_at (G : set V ) (x : V ) (g : V -> R^o)  :=
  g @ (within G (nbhs x)) --> (f x).

Lemma continuousR_scalar_on_bounded :
  (continuousR_on_at F 0 f) ->
  (exists  r , (r > 0 ) /\ (forall x : V, F x ->   (`|f x| ) <=  `|x| * r)).
Proof.
  rewrite /continuousR_on_at.
  move  => /cvg_ballPpos  H.
    have H':  (0 < 1) by [].
  move: (H (1%:pos)) {H'}.
  have f0 : f 0 = 0.
     suff -> : f 0 = f (0 + (-1)*: 0) by rewrite linfF // mulNr mul1r addrN.
     by rewrite scaleNr scaler0 addrN.
  rewrite near_simpl /( _ @ _ ) //= nearE /(within _ ) near_simpl f0.
  rewrite -nbhs_nearE => H0 {H} ; move : (nbhs_ex H0) => [tp H] {H0}.
  pose t := tp%:num .
  exists (2*t^-1). split=> //.
  move=> x. case:  (boolp.EM (x=0)).
  - by move=> ->; rewrite f0 normr0 normr0 //= mul0r.
  - move/eqP=> xneq0 Fx.
  pose a : V := (`|x|^-1 * t/2 ) *: x.
  have Btp : ball 0 t a.
   apply : ball_sym ; rewrite -ball_normE /ball_  subr0.
   rewrite normmZ mulrC normrM.
   rewrite !gtr0_norm //= ; last by rewrite  pmulr_lgt0 // invr_gt0 normr_gt0.
   rewrite mulrC -mulrA -mulrA  ltr_pdivr_mull; last by rewrite normr_gt0.
   rewrite mulrC -mulrA  gtr_pmull.
   rewrite invf_lt1 //=.
     by have lt01 : 0 < 1 by []; have le11 : 1 <= 1 by [] ; apply : ltr_spaddr.
   by  rewrite pmulr_lgt0 // !normr_gt0.
 have Fa : F a by rewrite -[a]add0r; apply: linF.
 have :  `|f a| < 1.
    by move: (H _ Btp Fa); rewrite /ball /ball_ //= sub0r normrN.
  suff ->  : ( f a =  ( (`|x|^-1) * t/2 ) * ( f x)) .
     rewrite normrM (gtr0_norm) //.
     rewrite mulrC mulrC  -mulrA  -mulrA  ltr_pdivr_mull //= ;
       last by rewrite normr_gt0.
     rewrite mulrC [(_*1)]mulrC mul1r -ltr_pdivl_mulr //.
     by rewrite invf_div => Ht; apply : ltW.
     by  rewrite !mulr_gt0 // invr_gt0 normr_gt0. 
 suff -> : a = 0+ (`|x|^-1 * t/2) *: x by rewrite linfF // f0 add0r.
 by rewrite add0r.
Qed.

Lemma mymysup : forall (A : set R) (a m : R),
     A a -> ubound A m ->
     {s : R | ubound A s /\ forall u, ubound A u -> s <= u}.
Proof.
  move => A a m Aa majAm. 
  have [A0 Aub]: has_sup A. split; first by exists a.
    by exists m => x; apply majAm.
  exists (reals.sup A).
  split; first by apply: sup_ub.
  by move => x; apply: sup_le_ub.
Qed.

Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  lbound A m ->
     {s : R | lbound A s /\ forall u, lbound A u -> u <= s}.
  move => A a m Aa minAm.
  have [A0 Alb]: has_inf A. split; first by exists a.
    by exists m => x; apply minAm.
  exists (reals.inf A).
  split; first by apply: inf_lb.
  by move => x; apply: lb_le_inf.
Qed.


Notation myHB :=
  (hahn_banach.HahnBanach (boolp.EM) Choice_prop mymysup mymyinf F0 linF linfF).


Theorem HB_geom_normed :
  continuousR_on_at F 0  f ->
  exists g: {scalar V}, (continuous (g : V -> R^o)) /\ (forall x, F x -> (g x = f x)).
Proof. 
 move=> H; move: (continuousR_scalar_on_bounded H) => [r [ltr0 fxrx]] {H}.
 pose p:= fun x : V => `|x|*r ;   have convp: convex p.
   move=> v1 v2 l m [lt0l lt0m] addlm1 //= ; rewrite !/( p _) !mulrA -mulrDl.
   suff: `|l *: v1 + m *: v2|  <= (l * `|v1| + m * `|v2|).
     move => h; apply : ler_pmul; last by [].
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
  move=> x; rewrite /cvgP; apply: (continuousfor0_continuous).
  apply: linear_bounded0; exists r.
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
