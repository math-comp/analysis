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

Variables (V W : normedModType R ) . 

Definition continuous_at x (f : V -> W) :=   ( f @ x) --> (f x).

Lemma continuous_atP x (f : V -> W) :
  (continuous_at x f) <-> forall eps : posreal, \forall y \near f @ x, ball (f x) eps%:num y.
Proof.
  rewrite /continuous_at. split.
   - by move => /flim_ballPpos. 
   - by move => /flim_ballPpos. 
Qed.



(*Lemma locallyP (Z : normedModType R ) (x : Z) A : (locally x A) <-> (exists r:posreal, ball x r%:num `<=` A).
Proof.
Admitted.  *)

Definition continuous_on F f :=  forall x , F x -> (continuous_at x f ).

Lemma div_abs ( x y : R) : `| x^-1 * y |%real = `| x^1 | * `| y| . 
Proof.
  Search _ ( `| _ | * `| _ |). rewrite -normedtype.R_AbsRingMixin_obligation_1.
 Search   (_%coqR) in reals.  
Admitted.

Lemma continuous_bounded0 (f : { linear V -> W}) :
  (continuous_at 0 f) -> 
  (*( forall z, (filtermap f (locally z) `=>` ( locally (f z)))  )*)
  ( exists  r , (r > 0 ) /\ (forall x : V,   ( `|[f x]| ) <=  (`|[x]| ) * r  )  ) . 
Proof.
  move => /continuous_atP H. have H' : (0 < 1) by []. move : (H (1%:pos))  {H'} .
  rewrite (linear0 f) /( _ @ _ ) //=. move => H'{H}. Check (locally_ ball 0). 
  (* H'= locally_ ball 0 (fun a => ball 0 1 (f a )).*)
  have : exists t , (t > 0) /\  forall x , ball 0 t x -> ball 0 1 (f x ).
    rewrite -!ball_normE /ball_. (*rewrite sub0r*) admit. 

  move => [t [tp H]].
  exists t^-1. split. by rewrite invr_gt0.
  move => x ; case :  (boolp.EM (x=0)).
  - by move => -> ; rewrite (linear0 f) !normm0 //= mul0r. 
  - move => xneq0. 
    have normxle0 : `|[x]| > 0 .  rewrite normm_gt0.
    (*proving (x <> y) -> (x != y), where is it done ? *)
    case : (boolp.EM (x==0)).
    - move => /eqP x0. by have : False by apply : ( xneq0 x0). 
    - by move => /negP. 
    pose a := (  `|[x]|^-1 * t ) *: x.
    (*going from ball to norm is done through ball_normE and unfolding ball_. 
    I looked a long time for this *)
    have ball0ta : ball 0 t a. 
     apply : ball_sym ; rewrite -ball_normE /ball_ subr0.
     rewrite normmZ . admit.
     (* stuck with %real , search a view*)(* rewrite normedtype.R_AbsRingMixin_obligation_1. *)
    move : (H a ball0ta) ;rewrite -ball_normE /ball_ sub0r normmN. 
    have  : ( f a =  ( (`|[x]|^-1) * t ) *: ( f x)) .
      have : a = (`|[x]|^-1 * t) *: x + 0 by rewrite addrC add0r.  
      by move => -> ; rewrite (linearP f  (`|[x]|^-1 * t) x 0) (linear0 f) addrC add0r.  
    move => -> . 
    rewrite normmZ (div_abs `|[x]| t) (gtr0_norm tp) (ger0_norm (normm_ge0 x)).
    rewrite mulrC mulrC -mulrA.  
    rewrite (ltr_pdivr_mull 1  (t*`|[f x]|) normxle0 ).
    rewrite mulrC (mulrC `|[x]| 1) mul1r -(ltr_pdivl_mulr `|[f x]| `|[x]| tp).
    by move => Ht ; apply : ltrW. 
Admitted.


(*
Lemma landau_cst_bounded ( g : V -> W) :
  ( (g : _ -> _) =O_ (0 : V) (cst (1 : R^o))=O_0 cst 1) ->
  exists  r : posreal, (forall x : V,   ( `|[f x]| ) <=    (`|[x]| ) * r%:num  ) .

*)

  
Lemma linear_cont0_continuous  (f : { linear V -> W}) :
  continuous_at 0 f -> continuous f.
Proof.
Admitted.
  


Lemma bounded_continuous  (f : { linear V -> W}) : 
  ( exists  r : posreal, (forall x : V,   ( `|[f x]| ) <=   (`|[x]| ) * r%:num  )  ) ->
  continuous f.  
Proof.
  (*use linear_continuous of landau and landau_cst_bounded*)
  move => H.
  apply :  linear_cont0_continuous . 
  apply : (proj2 (continuous_atP 0 f)). move => A f0A. 
Admitted.

End LinearContinuousBounded.


Section HBGeomNormed.
Variable ( V : normedModType R) ( F G: pred V ) (f : {scalar V}) ( F0 : F 0).

Variable Choice_prop :  forall T U (P : T -> U -> Prop),
    (forall t : T, exists u : U,  P t u) -> (exists e, forall t,  P t (e t)).


 (* Upper bound *)
Definition ubd (A : set R) (a : R) := forall x, A x -> x <= a.                                                                                                   (*ub in reals *)

 (* Lower bound *)
Definition ibd (A : set R) (a : R) := forall x, A x -> a <= x. (*ib in reals*) 

(*Lemma mysup : forall (A : set R) (a m : R),
     A a -> ub (in_set A) m ->
     {s : R | ub (in_set A) s /\ forall u, ub (in_set A) u -> s <= u}.
Proof.
  move => A a  m  Aa majAm.  
  have : (has_sup  (in_set A)).  (*It seems that I havent imported somtehing from classical sets here, allowing for a pred structure on sets *) 
  split . 
  - by exists a ; rewrite in_setE.
  - exists m ; rewrite in_setE // => x ;apply : propF ; rewrite negb_imply //= . 
    move  => /andP ; apply and_ind; rewrite in_setE  => Ax /negP nxm.
    Check (ub (in_set A)).   by apply : (nxm (majAm x Ax)).
  move => /has_supP has_sup_A. pose s :=  (real_sup (in_set A)).
  exists s  => //=. 
  split.  
  - move => x Ax.  move : (real_sup_ub (has_sup_A)) => //=.   admit.
  - move => x xmajA.
    have ubdA : is_upper_bound A x.  move => y Ay. Check (xmajA y Ay). (* Je suis dans coqR*) admit. 
    Check proj2 (real_sup_is_lub has_sup_A) x. admit. (* (cannot unify "is_true (in_set A x0)" and "A x0")*)
Admitted.*)  

Lemma mymysup : forall (A : set R) (a m : R),
     A a -> ubd A m ->
     {s : R | ubd A s /\ forall u, ubd A u -> s <= u}.
Proof.
  move => A a  m  Aa majAm.  Search _ (Prop -> bool ).  
  have : (has_sup  (in_set A)).
  split . 
  - by exists a ; rewrite in_setE.
  - exists m ; rewrite in_setE // => x ;apply : propF ; rewrite negb_imply //= . 
    move  => /andP ; apply and_ind; rewrite in_setE  => Ax /negP nxm.
      by apply : (nxm (majAm x Ax)).
  move => /has_supP has_sup_A.
  pose s :=  (real_sup (in_set A)) ; exists s .
  split.  
  - move => x Ax.  move : (real_sup_ub (has_sup_A)) => //= /ubP H.
    have Axb : x \in in_set A by rewrite in_setE.
    by apply : (H x Axb).  
  - move => x xmajA.
    have ubdA : is_upper_bound A x.  move => y Ay. Check (xmajA y Ay).  admit.
    (* cannot go in coqR*)
    have majAmb : is_upper_bound  (fun x : R => in_set A x) m.
    move => y ; rewrite in_setE => Ay. Check (xmajA y Ay).   admit. (* cannot go in coqR*)
    Check proj2 (real_sup_is_lub has_sup_A) m majAmb.   admit. (* cannot go in coqR*)
Admitted. 
 

Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  ibd A m ->
     {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.
Admitted.


Notation myHB := (hahn_banach.HahnBanach (boolp.EM) Choice_prop mymysup mymyinf) .

(*  need to give  scalar R is of type V -> W *)

(*Theorem HB_geom_normed :
  (forall x , F x -> continuous_at x f)
   -> exists g : {scalar V} , ( continuous f ) /\ ( forall x, F x -> (f x = g x) ) .  
 Proof.  
 Admitted.  *)

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
