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

Section HBGeom.

Variable (R : realType) (V : normedModType R) (F : pred V) (f :  V -> R^o) (F0 : F 0).
Hypothesis (linF : (forall (v1 v2 : V) (l : R),
                       F v1 -> F v2 -> F (v1 + l *: v2))).
Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 ->
                              f (v1 + l *: v2) = f v1 + l * (f v2).


Hypothesis (Choice_prop : ((forall T U  (Q : T -> U -> Prop),
                      (forall t : T, exists u : U,  Q t u) -> (exists e, forall t,  Q t (e t))))).


(*Looked a long time for within *)
Definition continuousR_on ( G : set V ) (g : V -> R^o) :=
  (forall x, (g @ (within G (nbhs x))) --> g x).

(*Do we need to have F x ?*)
Definition continuousR_on_at (G : set V ) (x : V ) (g : V -> R^o)  :=
  g @ (within G (nbhs x)) --> (g x).

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
 move: (myHB convp majfp) => [ g  [majgp  F_eqgf] ] {majfp}.
 exists g;  split; last by [].
  move=> x; rewrite /cvgP; apply: (continuousfor0_continuous).
  apply: linear_bounded0; exists r.
  split; first by rewrite realE; apply/orP; left; apply: ltW. (* r is Numreal ... *)
  move => M m1; rewrite nbhs_ballP;  exists 1; first by [].
  move => y; rewrite -ball_normE //= sub0r => y1.
  rewrite ler_norml; apply/andP; split.
  - rewrite ler_oppl -linearN; apply: (le_trans (majgp (-y))).
    by rewrite /p -[X in _ <= X]mul1r; apply: ler_pmul; rewrite ?normr_ge0 ?ltW //=.
  - apply: (le_trans (majgp (y))); rewrite /p -[X in _ <= X]mul1r -normrN.
    apply: ler_pmul; rewrite ?normr_ge0 ?ltW //=.
Qed.

End HBGeom.
