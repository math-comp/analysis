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
  (continuous_at x f) <-> forall A , locally (f x) A -> locally  x ( f @^-1` A). 
Proof.
(*split=> fcont; first by rewrite !openE => A Aop ? /Aop /fcont.
move=> s A; rewrite locally_simpl /= !locallyE => - [B [[Bop Bfs] sBA]].
by exists (f @^-1` B); split; [split=> //; apply/fcont|move=> ? /sBA].
Qed.*)
Admitted.

Lemma locallyP (Z : normedModType R ) (x : Z) A : (locally x A) <-> (exists r:posreal, ball x r%:num `<=` A).
Proof.
Admitted.  

Definition continuous_on F f :=  forall x , F x -> (continuous_at x f ).

Lemma div_abs ( x y : R) : `| x^-1 * y |%real = `| x |^-1 * `| y| . 
Proof.
Admitted. 

Lemma continuous_bounded0 (f : { linear V -> W}) :
  (continuous_at 0 f) -> 
  (*( forall z, (filtermap f (locally z) `=>` ( locally (f z)))  )*)
  ( exists  r : posreal, (forall x : V,   ( `|[f x]| ) <=   (`|[x]| ) * r%:num  )  ) . 
Proof.
  move => /continuous_atP H ; move : (H (ball_ norm 0 1)).
  rewrite (linear0 f) ;  move => H2 {H}. 
  move : (H2 (locally_ball_norm  0 (1%:pos))) ; rewrite /(_ @^-1`_ ) //=.
  move => /locallyP [tp H] {H2}. 
  pose  t := tp%:num. 
  pose r:= t^-1.  exists (PosNum (inv_pos_gt0 tp)). 
  move => x. case :  (boolp.EM (x=0)).
  - move => ->. by rewrite (linear0 f) !normm0 //= mul0r. 
  - move => xneq0.
    have normxle0 : `|[x]| > 0 . admit. 
    pose a := (  `|[x]|^-1 * t ) *: x.  
    have lem : ball 0 t a . rewrite -ball_normE. unfold ball_. admit.
    move : (H a lem).  rewrite sub0r.  rewrite normmN //= {H}.
    have  : ( f a =  ( (`|[x]|^-1) * t ) *: ( f x))  by admit.
    move => -> .
    rewrite normmZ (div_abs `|[x]| t) (ger0_norm (posnum_ge0 tp)) (ger0_norm (normm_ge0 x)). 
    Check (ltr_pdivr_mull 1  (tp%:num*`|[f x]|) normxle0 ).  (*l'associativie de la multiplicaiton*)
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

Search _  "sup" in Real.
Print Real.sup. 
About sup. 

Locate real. 

 (* Upper bound *)
Definition ubd (A : set R) (a : R) := forall x, A x -> x <= a.                                                                                                   (*ub in reals *)

 (* Lower bound *)
Definition ibd (A : set R) (a : R) := forall x, A x -> a <= x. (*ib in reals*) Check reals.sup. 

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
    have ubdA : is_upper_bound A x.  move => y Ay. Check (xmajA y Ay).  admit. (* cannot go in coqR*)
    
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
