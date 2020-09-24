From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum ssrint fintype bigop order matrix interval.
From mathcomp  Require Import boolp reals posnum.
From mathcomp Require Import classical_sets topology prodnormedzmodule  posnum topology normedtype landau forms sequences.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


Section Close_Ball.
Definition close_ball_ (R : numDomainType) (V: zmodType) (norm : V -> R) (x : V) (e :R) :=
[set y | (norm (x- y) <=e)%O ] .
Definition close_ball (R : realType) (M : completeNormedModType R) (x : M) (e : R) :=
  close_ball_ normr x e.

Lemma closed_close_ball (R : realType) (M : completeNormedModType R) (x : M) (e : R) :
  closed (close_ball x e).
Proof.
  Search _ closed.
  pose f := fun y => normr ( x - y).
  have : close_ball x e  = f @^-1` [set x | (x<= e)%O] by rewrite /close_ball /close_ball_ /preimage.
  move ->.
  apply (@closed_comp _ _ (f : M -> R^o) _).
  have H : forall x : M , x \in (~` f @^-1` (fun x : R => (x<=e)%O))  -> {for x, continuous ( f : M -> R^o)}.
   move => y Hy.  
   apply  (@continuous_comp _ _ _ (fun y : M => (x-y)) (normr : M -> R^o) y) .
    apply: continuousB.
     by apply: cst_continuous.
     by [].
    by apply : norm_continuous.
   move=> a.
   exact (H a).
  by apply: closed_le.
Qed.

Variable (K : realType).


Lemma neighBall (U : completeNormedModType K) (y : U) (A : set U) :
  open_nbhs y A -> exists (r : {posnum K}), ball y r%:num `<=` A.
Proof.
  by move=> /open_nbhs_nbhs /(@nbhs_ballP _ _ y A) /exists2P [r [supr prop]]; exists (PosNum supr).
Qed.


Lemma closeNeigh_ball (U : completeNormedModType K) (y : U) (A : set U) :
  open_nbhs y A -> exists (r : {posnum K}), close_ball y r%:num `<=` A.
Proof.
  move=> H.
  have [r Hr] : (exists r : {posnum K}, ball y r%:num `<=` A).
    by apply: neighBall.
  have Hrr : r%:num / 2 > 0.
    by [].
  exists (PosNum Hrr).
  apply (@subset_trans  _ (ball y r%:num) _ _).
  rewrite -?ball_normE;  move=> a Ha;
  apply (@le_lt_trans _ _  (PosNum Hrr)%:num (`| y - a|) r%:num); rewrite ?(@ltr_pdivr_mulr _ 2 r%:num r%:num);
  by rewrite -?(@ltr_pdivr_mull _ r%:num 2 r%:num) //= mulrC mulfV ?ltr1n.
  by [].  
Qed.

Lemma close_ball_center (U :completeNormedModType K) (x : U) (r : {posnum K}) :
  close_ball x r%:num x.
Proof.
  by rewrite /close_ball /close_ball_ //= subrr normr0.
Qed.

Lemma close_neigh_ball (U : completeNormedModType K) (x : U) (r : {posnum K}) :
  open_nbhs x (close_ball x r%:num)^°.
Proof.
  split.
    by apply: open_interior.
    apply: nbhs_singleton; apply: nbhs_interior; apply /nbhs_ballP; exists r%:num.
    by [].
    by rewrite -ball_normE; move=> a; apply/ltW.
Qed.


Lemma close_ball_ler (U : completeNormedModType K) (x : U) (e1 e2 : K) :
  (e1 <= e2)%O -> close_ball x e1 `<=` close_ball x e2.
  by move=> H e Y; apply: (@le_trans _ _ e1 (`|x-e|) e2). 
Qed.

End Close_Ball.

Section Baire.
Variable (K: realType). 
Definition dense (U : completeNormedModType K) (S : U  -> Prop) :=
  forall (O : set U), (exists y, O y) -> open O ->  exists x, (setI O S) x.

(*Definition dense_ (U : completeNormedModType K) (S : U -> Prop) :=
  forall O, (O <> set0) -> open O -> ((setI O S) <> set0).
Definition dense_alt (U : completeNormedModType K) (S : U -> Prop) :=
  closure S = setT.
Definition dense_altbis ( U : completeNormedModType K) (S : U -> Prop) :=
  forall x, exists O , (neigh x) O -> (O `&` S) <> set0.
Lemma densityEbis  (U : completeNormedModType K) (S : U -> Prop) :
  dense S <-> dense_ S.
Admitted.
Lemma densityE (U : completeNormedModType K) (S : U -> Prop) :
  dense S <-> dense_alt S.
Admitted.*)
Lemma floor_nat_comp (M :K) : (0 <= M) -> (M < `|Rtoint(floor M + 1%:~R)|%:R).
       move=> Hyp.
       set n:= (X in ( M < X)).
       have ->  : n = (floor M + 1).
       rewrite {}/n.
       have /RintP [z Hmz] := isint_floor M.
       rewrite Hmz -intrD Rtointz.
       have S : z +  1 = Posz (  `|(z+1)%R|%N).
       rewrite gez0_abs.
       by [].
       rewrite -(@ler_int K 0 (z+1)) intrD -Hmz (@le_trans _ _ M 0 (floor M + 1)).
       by [].
       by [].
       by apply/ltW; apply: floorS_gtr.
       by rewrite  S.       
       by apply: floorS_gtr.
Qed. 

Lemma minr_le1 (x y : K) : (x >= minr x y ).
Proof.
  case : (@lerP _ x y).
  by [].
  by apply: ltW.
Qed.

Lemma minr_le2 ( x y : K) : ( y >= minr x y).
Proof.
  by case : (@lerP _ x y).
Qed.
Lemma lt_inv (x y : K) : (x > 0) -> (y > 0) -> (x^-1 < y^-1) = (y < x).
Proof.
 by move => supx supy; rewrite -(mulr1 x^-1) ltr_pdivr_mull ?ltr_pdivl_mulr ?(mulrC 1 y) ?(mulr1 y).
Qed.

Definition Baire (U : completeNormedModType K) :=
  forall (F: nat -> (set U)), (forall i, open (F i) /\  dense (F i))  ->
                      dense (\bigcap_(i : nat) (F i)).

(* Definition Baire (U : completeNormedModType K) :=
  forall (F: nat -> (set U)), (forall i, open (F i) /\  dense (F i))  ->
                      dense (\bigcap_(i : nat) (F i)). *)

Theorem DeBaire  (U : completeNormedModType K) : Baire U.
Proof.
move=> F Hf D Dy  OpenD.
have [H /(_ D  Dy OpenD) [a0 DF0a0 ] ] : open (F 0%nat) /\ dense (F 0%nat)
  by apply Hf.
have openIDF0 : open (D `&` F 0%N) by apply: openI.
have neigh_a0 : open_nbhs a0 (D `&` F 0%N) by [].
move: (@closeNeigh_ball _ _   a0 (D `&` F 0%N) neigh_a0)
         {DF0a0 openIDF0} => [ r0 Ball_a0] {neigh_a0} . 
pose P (m: nat) (arn : U * {posnum K}) (arm : U * {posnum K}) :=
  close_ball arm.1 (arm.2%:num)
                  `<=` ((close_ball (arn).1 ((arn).2%:num))^°
   `&` (F m)) /\ (arm.2%:num < ((S(m))%:R^-1)).
have Ar: forall na : nat * (U * {posnum K}), exists b : (U * {posnum K}) , P (S(na.1)) na.2 b.
  move=> [n [an rn]].
  move: (Hf ((S n)%N))=> [ openFn denseFn ].
  have [an1 B0Fn2an1]: exists x, ((close_ball an (numpos K rn))^° `&` F (S n)%N) x .
  move: (close_neigh_ball an rn)=> [h1 h2]; apply: denseFn.
   - by exists an.
   - by [].
simpl in (type of an1).
have openIB0Fn1 : open ((close_ball an (numpos K rn))^° `&` F (S n)%N).
  apply: openI; last by [].
  by apply: open_interior.
have neigh_an1 : open_nbhs an1 ((close_ball an (numpos K rn))^° `&` F (S n)%N) by [].
move: (@closeNeigh_ball _ _ an1  ((close_ball an (numpos K rn))^° `&` F (S n)%N) neigh_an1)
        {B0Fn2an1 openIB0Fn1 openFn denseFn} => [rn01 Ball_an1].
pose a := ((n.+3)%:R^-1 : K).
have asup: a > 0 by [].
pose abis := PosNum asup.
pose rn1b := minr abis%:num rn01%:num.
have majr : rn1b > 0 by apply min_pos_gt0.
pose rn1 := PosNum majr.
exists (an1,rn1); split.
   - have temp : close_ball an1 rn1b `<=` close_ball an1 rn01%:num
     by apply : close_ball_ler; apply: minr_le2.
     by apply:  (@subset_trans _ (close_ball an1 rn01%:num) _ _).
   - apply: (@le_lt_trans _ _ (n.+3%:R^-1) rn1b (n.+2%:R^-1)).
     by apply: minr_le1.
     by rewrite lt_inv ?ltr_nat.
move: (choice Ar) => [f Pf].
pose fix ar (n: nat):= match n with
                     | 0 => (a0,r0)
                     | S p => (f (p,(ar p)))
                     end .
pose a := fun n => (ar n).1 .
pose r := fun n => (ar n).2 .
have Suite_ball : forall (n m :nat) , (n <= m)%N -> close_ball (a m) (r m)%:num
                                            `<=` close_ball (a n) (r n)%:num.
 move=> n m.
 elim m=> [| k iHk].
  by rewrite leqn0; move=> /eqP ->.
 move=> iHk2. 
 have step : close_ball (a k.+1) (r k.+1)%:num `<=` close_ball (a k) (r k)%:num.
 have [Htemp _]: P k.+1 (a k, r k)   (a (k.+1), r (k.+1)) by apply: (Pf (k, ar k)).
 move: Htemp ; rewrite subsetI.
 move=> [tempbis _].
 apply: (@subset_trans _ (close_ball (a k, r k).1 (numpos K (a k, r k).2))^° _ _).
   by [].
   by apply : interior_subset.  
 rewrite leq_eqVlt in iHk2.
 have : (n==k.+1) \/ (n<k.+1)%N by apply /orP.
 case.
 - by move=> /eqP ->.
 - move => temp.
   have: (n<= k)%N by []. 
   move  => /iHk final.
   by apply : (@subset_trans _ (close_ball (a k) (numpos K (r k))) _ _).   
have cauchyexa: (cauchy_ex (a @ \oo )).
 move => e e0.
 rewrite /fmapE -ball_normE /ball_.
 have [n Hn]: exists n : nat , 2*(r n)%:num < e.
 pose eps := e/2.
 have [n Hn]: exists n : nat , ((n.+1)%:R^-1 < eps).
 exists `|Rtoint (floor eps^-1 + 1%:~R)|%N.
 have He : (eps^-1 < `|Rtoint(floor eps^-1 + 1%:~R)|%:R)
   by apply : floor_nat_comp;rewrite invr_ge0 ler_pdivl_mulr ?(mulrC 0 2) ?(mulr0 2) ?ltW.
 have : (eps^-1 < `|Rtoint(floor eps^-1 + 1%:~R)|%:R) by [].
 rewrite -(mulr1 eps^-1) ltr_pdivr_mull.
 rewrite mulrC -ltr_pdivr_mull mulr1.
    rewrite mulr1; move=> Ht; apply (@lt_trans _ _ (`|Rtoint (floor eps^-1 + 1%:~R)|%:R^-1) _ _).
    rewrite lt_inv //=.
      by rewrite ltr_nat //=.
      by rewrite (@lt_trans _ _ eps^-1 _ _) ?invr_gt0  ?ltr_pdivl_mulr ?(mulrC 0 2) ?(mulr0 2) //=.
      by [].
      by rewrite (@lt_trans _ _ eps^-1 _ _) ?invr_gt0  ?ltr_pdivl_mulr ?(mulrC 0 2) ?(mulr0 2) //=.
      by rewrite ltr_pdivl_mulr ?(mulrC 0 2) ?(mulr0 2).
 exists (n.+1).
 have: (r n.+1)%:num < n.+1%:R^-1. 
 have: P n.+1 (a n, r n)   (a (n.+1), r (n.+1)) by apply: (Pf (n, ar n)).
 by move=> [_ B]; apply: (@lt_trans _ _ (n.+2%:R^-1) _ _);  rewrite ?lt_inv ?ltr_nat .
  move=> temp; apply: (@lt_trans _ _ (2* n.+1%:R^-1) _ _);
  by rewrite -ltr_pdivl_mull ?mulrA ?(mulrC 2^-1 2) ?mulfV ?(mulrC 2^-1 e) ?div1r.
 exists (a n); exists n; first by [].
 move =>  m nsupm.
 apply: (@lt_trans _ _ (2*(r n)%:num) (`|a n - a m|) e); last first. by [].
 have : (close_ball (a n) (r n)%:num) (a m).
 move : (Suite_ball n m nsupm).
 have : close_ball (a m) (r m)%:num (a m) by apply: close_ball_center.
 by move=> temp1 Ha; move : (Ha (a m) temp1).
 by move=> temp; rewrite (@le_lt_trans _ _ (r n)%:num (`|a n - a m|) (2*(r n)%:num)) -?ltr_pdivr_mulr ?mulfV ?ltr1n.
have cauchya : (cauchy (a @ \oo)) by apply: cauchy_exP.
have : cvg (a @ \oo) by apply: cauchy_cvg. 
rewrite cvg_ex //=.
move=> [l Hl] {Hf Dy OpenD H cauchya cauchyexa}.
exists l.
have partie1 : D l.
 have Hinter : (close_ball a0 r0%:num) l.
  apply: (@closed_cvg _ _ \oo eventually_filter a); first by [].
  move=> m.
  have temp:  (0 <= m)%N by apply: leq0n.
    move : (Suite_ball 0%N m temp).
    have : close_ball (a m) (r m)%:num (a m) by apply: close_ball_center.
  by move=> temp1 Ha; move : (Ha (a m) temp1).
 by apply: closed_close_ball.
have : close_ball a0 r0%:num `<=` D by move: Ball_a0; rewrite subsetI; apply:  proj1.
by move=>  Htemp; move : (Htemp l Hinter).
have partie2 : (\bigcap_i F i) l.
move=> i _.
 have : close_ball (a i) (r i)%:num l.
  rewrite -(@cvg_shiftn i _ a l) in Hl.
  simpl in Hl.
  have partiecvg:  forall n : nat, close_ball (a i) (r i)%:num (a (n + i)%N).
   move=> n.
   have temp : (i <= (n +i)%N)%N by apply: leq_addl.
   have temp2 : close_ball (a (n+i)%N) (r (n+i)%N)%:num (a (n+i)%N) by apply: close_ball_center.
   by move : (Suite_ball i (n +i)%N temp (a (n+i)%N) temp2).
  apply (@closed_cvg _ _ \oo eventually_filter (fun n : nat => a (n+i)%N)).  
  by [].
  by [].  
  by apply :  closed_close_ball.
case i.
by rewrite subsetI in Ball_a0; move: Ball_a0; move=> [_ p] la0; move : (p l la0).
move=> n.
have [temp _] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply : (Pf (n , ar n)).
by rewrite subsetI in temp; move : temp; move=> [_ p] lan1; move: (p l lan1). 
by [].  
Qed.


End Baire.

Section banach_steinhauss.
Variable (K: realType).
Variable (V: completeNormedModType K)  (W: normedModType K).
(*Theorem banach_steinhauss *)

Check bounded_on.
Print bounded_on.

(*Definition bounded_alt (f: V -> W) :=
  bounded_on f (locally (0:V)).*)

Definition bounded (f: V -> W) := forall r, exists M,
      forall x, (`|x| <= r) -> (`|(f x)| <= M).

(*Lemma bounded_ballE (f: V -> W) : bounded f <-> bounded_alt f.
Proof.
Admitted.*)

Definition pointwise_bounded (F: (V -> W) -> Prop) := forall x, exists M,
      forall f , F f ->  (`|f x| <= M)%O.

Definition uniform_bounded (F: (V -> W) -> Prop) := forall r, exists M,
      forall f, F f -> forall x, (`|x| <= r)  -> (`|f x| <= M)%O.

Lemma bounded_landau (f :{linear V->W}) :
  bounded f <-> ((f : V -> W) =O_ (0:V) cst (1 : K^o)).
Proof.
  split.
  - rewrite eqOP => bf.
    move: (bf 1) => [M bm]. 
    rewrite !nearE /=; exists M; split. by  apply : num_real.
    move => x Mx; rewrite nearE nbhs_normP /=. 
    exists 1; first by [].
    move => y /=. rewrite -ball_normE /ball_ sub0r normrN /cst normr1 mulr1 => y1.
    apply: (@le_trans _ _ M _ _).
    apply: (bm y); by apply: ltW.
    by apply: ltW.
  - rewrite eqOP !nearE /+oo /cst normr1; move=> [M [Mr Bf]] r.
    move: (Bf (2*M)); rewrite nearE /=.
    have: M < 2 * M by admit.
    move=> lem /(_ lem) {lem} //=; rewrite nbhs_normP /cst -mulrA mulr1 .
    move=> [R oR] BR; exists (R^-1 * r * 2 * 2 * M)  => x xr.
    case: (EM (0 < `|x|)). (*ameliorer*)
     - move => x0.
       have r0 : 0 < r by apply: (@lt_le_trans _ _ (`|x|)). 
       move: (BR ((R * (2 * r)^-1) *: x)); simpl. rewrite -ball_normE /ball_ sub0r normrN.
       have R2r10 : (0 < R/(2*r)) by rewrite divr_gt0 ?mulr_gt0 //=.
       have: (`|(R / (2 * r)) *: x| < R)%O by rewrite normmZ gtr0_norm //= -mulrA -ltr_pdivl_mull //= mulVf;
         rewrite ?lt0r_neq0 //= ltr_pdivr_mull ?mulr1 ?mulr_gt0 //= (@le_lt_trans _ _ r) //=;
         rewrite -ltr_pdivr_mulr //= divff ?lt0r_neq0 //= ltr1n //=.
       move=> lem /(_ lem) {lem}.
       rewrite linearZZ normmZ gtr0_norm //= (mulrC R) -(mulrA (2*r)^-1) ler_pdivr_mull ?mulr_gt0 //= (mulrC 2 r).
       by rewrite -ler_pdivl_mull //= !mulrA.
     - move => x0.
       have -> :  x = 0.
        have : ~~ (0%R < `|x|)%O by apply /negP.
        by rewrite -leNgt normrE; apply: eqP.
       have M0 : 0 <= M.
        have temp : (PosNum oR)%:num = R by [].
        rewrite -temp in BR; move:  (BR 0 (@ball_center _ _ 0 (PosNum oR))).
        by rewrite linear0 normr0 -ler_pdivr_mull ?mulr0 //=.        
       have r0 : 0 <= r by apply: (@le_trans _ _ (`|x|)); rewrite ?normr_ge0 //=.
       rewrite linear0 normr0 !mulr_ge0 //= ?invr_ge0 ?ltW //=.
       
Admitted.

Lemma bounded_imply_landau (f :{linear V->W}) :
  bounded f -> ((f : V->W) =O_ (0:V) cst (1 : K^o)).
Proof.
  rewrite eqOP => bf.
    move: (bf 1) => [M bm]. 
    rewrite !nearE /=; exists M; split. by  apply : num_real.
    move => x Mx; rewrite nearE nbhs_normP /=. 
    exists 1; first by [].
    move => y /=. rewrite -ball_normE /ball_ sub0r normrN /cst normr1 mulr1 => y1.
    apply: (@le_trans _ _ M _ _).
    apply: (bm y); by apply: ltW.
    by apply: ltW.
Qed.

Lemma denseNE (S : set V) : (not(dense S)) -> (exists O, ( exists x, (open_nbhs x) O) /\ (O `&` S = set0)).
Proof.
  rewrite /dense /open_nbhs => /existsNP [X /not_implyP [[x Xx] /not_implyP [ Ox /forallNP A ]]].
  exists X; split; first by exists x; split.
  by rewrite -subset0; apply/A => y.
Qed.


Lemma setIsubset (A B : set V) : A `&` B = set0 -> A `<=` ~` B.
Proof.
  by rewrite -setD_eq0; move <-; rewrite setDE setCK.
Qed.

Lemma linearsub  (a b : V) (f : V -> W ) :
  linear f -> (f (a-b) = f(a) - f(b)).
Proof.
  by rewrite addrC -scaleN1r; move ->; rewrite addrC scaleN1r.
Qed.

Lemma not_and_or : forall P Q : Prop , ~(P /\ Q) -> ~ P \/ ~ Q.
Proof.
  by move => P Q H; apply: or_asboolP; rewrite !asbool_neg -negb_and -asbool_and; apply /asboolPn.  
Qed.

Theorem Banach_Steinhauss (F: set ((V -> W))):
  (forall f, (F f) -> bounded f /\ linear f) ->
  pointwise_bounded F -> uniform_bounded F.
Proof.
  move=> Propf.
  move=> BoundedF.
  set O := (fun n :nat => \bigcup_(f in F) ((normr \o f)@^-1` [set y | y > n%:R])).
  have O_open: forall n : nat, open ( O n ).
   - move=>n.
     apply: open_bigU.
     move=> i App.
     apply: (@open_comp _ _ ((normr : W -> K^o) \o i) [set y | y > n%:R]).
     have Ci : continuous i.
     + have Li : linear i by apply Propf.
       have Bi : bounded i by apply Propf.
       have Landaui : i =O_ (0:V) cst (1:K^o) by apply (@bounded_imply_landau (Linear Li)).
       by apply: (@linear_continuous K V W (Linear Li)).
     move=> x Hx ; apply: continuous_comp.
       + by apply: Ci.
       + by apply: norm_continuous.
      by apply: open_gt.     
  set O_inf := (\bigcap_i ( O i)).
  have  O_infempty : O_inf = set0.
     rewrite -subset0 => x //=.
     move: (BoundedF x) => [M HMx].
     rewrite /O_inf  /O //=  /bigsetI /bigsetU //=.
     case  /(_ (`|Rtoint (floor M + 1%:~R)|%N)).
     -  by rewrite /setT.
     - move=> f  Hf abs; move : (HMx f Hf) => abs2.
     have: (`|Rtoint (floor M + 1%:~R)|%:R < M) by  apply: (@lt_le_trans _ _ (`|f x|)).
     have : (M < `|Rtoint(floor M + 1%:~R)|%:R) by apply : floor_nat_comp; apply:  (@le_trans _ _ `|f x|).       
     by apply : lt_nsym.
  have BaireV : Baire V by apply : DeBaire.
  have ContraBaire : exists i : nat, not (dense (O i)).
   - unfold Baire in BaireV.
     have BaireO : (forall i : nat, open(O i) /\ dense (O i)) -> dense (O_inf) by apply (BaireV O).
     apply contrap  in BaireO.
     + move: BaireO => /asboolPn /existsp_asboolPn [n /and_asboolP /nandP Hn].
       by exists n ; case : Hn => /asboolPn.
    + rewrite /dense O_infempty ; apply /existsNP.
       exists setT. elim.
       * by move=> x; rewrite setI0.
       * by exists point.
       * by apply: openT.
  have BaireContra : exists n :nat , exists x : V,
               exists r : {posnum K}, (ball x r%:num) `<=` (~` (O n)).
    - move: ContraBaire =>
      [ i /(denseNE) [ O0 [ [ x /(neighBall) [ r H1 ] ]
      /((@subsetI_eq0 _ (ball x r%:num) O0 (O i) (O i)) )  ]  ] /(_ H1) ] H2. 
       by exists i; exists x; exists r;apply: setIsubset; apply H2.
  move: BaireContra => [n [x0 [ r H ] ] k]; exists ((n%:R + n%:R) * k * 2 /r%:num); move=> f Hf y Hx.
  move: (Propf f Hf) => [ _ linf].
  case: (eqVneq y 0) => [-> | Zeroy]; last first. 
  - have  majballi : forall f, forall x, F f -> (ball x0 r%:num) x -> (`|f x | <= n%:R)%O.
    move=> g x Fg Bx; move: (H x Bx).
    rewrite /O //= /bigsetU //= /setC exists2P -forallNP.
    move /(_  g).  case /not_and_or ; first by [].
    by move=> /(@negP ((n%:R < `|g x|)%O)); rewrite -leNgt .
    have majball : forall f, forall x, F f -> (ball x0 r%:num) x -> (`|f (x - x0) | <= (n%:R + n%:R))%O.
    move=> g x Fg; move: (Propf g Fg) => [Bg Lg].
    have Ling : g(x - x0) = g(x) - g(x0) by apply: (@linearsub x x0 g).
    rewrite Ling.
    move=> Ballx.
    move: (majballi g x Fg Ballx) => Majx.
    move: (majballi g x0 Fg   (ball_center x0 r)) => Majx0.
    have Majf : `| g x | + `|g x0| <= n%:R + n%:R
      by apply: (@ler_add _ `|g x| n%:R `|g x0| n%:R).
    apply: (@le_trans _ _ (`|g x| + `|g x0|) (`|g x - g x0|) (n%:R + n%:R)).
    - by apply: ler_norm_sub.
    - by [].
    have ballprop : ball x0 r%:num (2^-1  * (r%:num / `|y|) *: y  + x0).
      rewrite -ball_normE /ball_ opprD. 
      rewrite addrC -addrA (@addrC _ (-x0) x0) addrN addr0 normrN normmZ.
      rewrite R_normZ R_normZ -mulrA -mulrA  -(@normr_id _ _ y) -R_normZ normr_id.
      rewrite /GRing.scale //= mulVf; last by rewrite normr_eq0. 
      rewrite normr1  mulr1 gtr0_norm; last by rewrite invr_gt0. 
      by rewrite gtr0_norm //=  gtr_pmull //= invf_lt1 //= ltr1n. 
    move: (majball f (2^-1 * (r%:num/`|y|)*:y + x0) Hf ballprop). 
    rewrite -addrA addrN linf.
    have -> : f 0 =0 by rewrite -(linear0  (Linear linf)). 
    rewrite addr0 normmZ !R_normZ -ler_pdivl_mull //=.
    rewrite !gtr0_norm //= ; last by rewrite invr_gt0 normr_gt0.
    rewrite mulrA mulrC invf_div mulrA (@mulrC _ (2^-1) _) invf_div mulrA.
    move=> Currentmaj {Propf BoundedF O O_open O_inf O_infempty BaireV ContraBaire H majball majballi}.
    rewrite (@le_trans  _ _ ((n%:R + n%:R) * `|y| * 2 / r%:num)) //= => {Currentmaj}.    
    rewrite (mulrC (n%:R + n%:R)) -ler_pdivl_mulr //=.
    rewrite invrK -(mulrC r%:num) -(mulrC r%:num^-1) (mulrA r%:num) mulfV //=. 
    rewrite (mulrC 1) mulr1 -ler_pdivl_mulr //=.  
    rewrite -(mulrC 2) -(mulrC 2^-1) (mulrA 2^-1) mulVf //= (mulrC 1) mulr1.
    case: n. 
    - by rewrite addr0 mulr0 (mulrC 0) mulr0.
    - move => n. 
      rewrite -ler_pdivl_mulr //= -mulrC mulrA mulVf //=.
      by rewrite (mulrC 1) mulr1. 
    rewrite mulr_gt0 ?invr_gt0 ?normr_gt0 //=. 
    rewrite mulr_gt0 ?invr_gt0 ?normr_gt0 //=. 
    by rewrite invr_neq0; rewrite ?normrE. 
    have -> : f 0 =0 by rewrite -(linear0  (Linear linf)).
    rewrite normr0 !mulr_ge0 //=.
    by rewrite (@le_trans _ _ `|y| _ _).
Qed.

End banach_steinhauss.
