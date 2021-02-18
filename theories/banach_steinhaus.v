From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum ssrint fintype order bigop order interval.
From mathcomp Require Import boolp reals posnum.
From mathcomp Require Import classical_sets topology normedtype landau forms sequences.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


Definition dense (T : topologicalType) (S : T  -> Prop) :=
  forall (O : set T), (exists y, O y) -> open O ->  exists x, (setI O S) x.

Lemma denseNE (T : topologicalType) (S : set T) : (not(dense S)) ->
                  (exists O, ( exists x, (open_nbhs x) O) /\ (O `&` S = set0)).
Proof.
  rewrite /dense /open_nbhs => /existsNP [X /not_implyP [[x Xx] /not_implyP [ Ox /forallNP A ]]].
  exists X; split; first by exists x; split.
  by rewrite -subset0; apply/A => y.
Qed.

Lemma le_closed_ball (R : numFieldType) (M : pseudoMetricNormedZmodType R)
   (x : M) (e1 e2 : R) :
  (e1 <= e2)%O -> closed_ball x e1 `<=` closed_ball x e2.
Proof.
  by rewrite /closed_ball => le; apply: closure_subset; apply: le_ball.
Qed.

Section order.

Lemma minr_le1 (K : orderType _)  (x y : K) : (x >= minr x y ).
Proof.
by rewrite le_minl; apply /orP; left.
Qed.

Lemma minr_le2 (K : orderType _) (x y : K) : (y >= minr x y).
Proof.
by rewrite le_minl; apply /orP; right.
Qed.


End order.

Section Baire.
Variable (K: realType).

Lemma floor_nat_comp (M :K) : (0 <= M) -> (M < `|Rtoint (Rfloor M + 1%:~R)|%:R).
move=> M0.
set n:= (X in ( M < X)).
have ->  : n = (Rfloor M + 1); last by apply: lt_succ_Rfloor.
rewrite /n.
have /RintP [z h] := isint_Rfloor M.
rewrite h -intrD Rtointz.
suff -> : z +  1 = Posz (`|(z+1)%R|%N) by [].
 rewrite gez0_abs //= -(ler_int K) intrD -h (@le_trans _ _ M) //=.
 by apply/ltW; apply: lt_succ_Rfloor.
Qed.

Definition Baire (U : completeNormedModType K) :=
  forall (F: nat -> (set U)), (forall i, open (F i) /\  dense (F i))  ->
                      dense (\bigcap_(i : nat) (F i)).

Theorem DeBaire  (U : completeNormedModType K) : Baire U.
Proof.
move=> F Hf D Dy  OpenD.
have [H /(_ D  Dy OpenD) [a0 DF0a0 ]]: open (F 0%nat) /\ dense (F 0%nat)
  by apply Hf.
have openIDF0 : open (D `&` F 0%N) by apply: openI.
have /open_nbhs_nbhs /nbhs_closedballP [r0 Ball_a0]: open_nbhs a0 (D `&` F 0%N) by [].
pose P (m: nat) (arn : U * {posnum K}) (arm : U * {posnum K}) :=
  closed_ball arm.1 (arm.2%:num)
                  `<=` ((closed_ball (arn).1 ((arn).2%:num))^°
   `&` (F m)) /\ (arm.2%:num < ((S(m))%:R^-1)).
have Ar: forall na : nat * (U * {posnum K}), exists b : (U * {posnum K}) , P (S(na.1)) na.2 b.
  move=> [n [an rn]].
  move: (Hf ((S n)%N)) => [ openFn denseFn ].
  have [an1 B0Fn2an1]: exists x, ((closed_ball an (numpos K rn))^° `&` F (S n)%N) x .
    move: (open_nbhs_closed_ball an rn)=> [h1 h2]; apply: denseFn; last by [].
    by exists an.
  simpl in (type of an1).
  have openIB0Fn1 : open ((closed_ball an (numpos K rn))^° `&` F (S n)%N).
    apply: openI; last by [].
    by apply: open_interior.
  have /open_nbhs_nbhs /nbhs_closedballP [rn01 Ball_an1] :
    open_nbhs an1 ((closed_ball an (numpos K rn))^° `&` F (S n)%N) by [].
  pose a := ((n.+3)%:R^-1 : K).
  have asup: a > 0 by [].
  pose abis := PosNum asup.
  pose rn1b := minr abis%:num rn01%:num.
  have majr : rn1b > 0 by apply min_pos_gt0.
  pose rn1 := PosNum majr.
  exists (an1,rn1); split.
    have temp: closed_ball an1 rn1b `<=` closed_ball an1 rn01%:num
      by apply : le_closed_ball; apply: minr_le2.
    by apply: (subset_trans temp).
  apply: (@le_lt_trans _ _ (n.+3%:R^-1) rn1b (n.+2%:R^-1)).
    by apply: minr_le1.
  by rewrite ltf_pinv ?ltr_nat  ?posrE //=.
move: (choice Ar) => [f Pf].
pose fix ar (n: nat):= match n with
                     | 0 => (a0,r0)
                     | S p => (f (p,(ar p)))
                     end .
pose a := fun n => (ar n).1 .
pose r := fun n => (ar n).2 .
have Suite_ball : forall (n m :nat) , (n <= m)%N -> closed_ball (a m) (r m)%:num
                                            `<=` closed_ball (a n) (r n)%:num.
 move=> n m.
 elim m=> [| k iHk].
  by rewrite leqn0; move=> /eqP ->.
 move=> iHk2.
 have step : closed_ball (a k.+1) (r k.+1)%:num `<=` closed_ball (a k) (r k)%:num.
   have [Htemp _]: P k.+1 (a k, r k) (a (k.+1), r (k.+1)) by apply: (Pf (k, ar k)).
   move: Htemp ; rewrite subsetI; move => [tempbis _].
   by apply: subset_trans; last by apply: interior_subset.
 rewrite leq_eqVlt in iHk2.
 have : (n==k.+1) \/ (n<k.+1)%N by apply /orP.
 case; first by move=> /eqP ->.
 by move => /iHk temp; apply : subset_trans; first by apply: step.
have cauchyexa: (cauchy_ex (a @ \oo )).
 move => e e0; rewrite /fmapE -ball_normE /ball_.
 have [n Hn]: exists n: nat , 2*(r n)%:num < e.
   pose eps := e/2.
   have [n Hn]: exists n: nat, ((n.+1)%:R^-1 < eps).
     pose z := `|Rtoint (Rfloor eps^-1 + 1%:~R)|%N.
     have He : (eps^-1 < z%:R).
       apply : floor_nat_comp.
       by rewrite invr_ge0 ler_pdivl_mulr ?(mulrC 0 2) ?(mulr0 2) ?ltW.
     exists z.
     rewrite -(invrK eps).
     rewrite ltf_pinv ?posrE ?invr_gt0 ?divr_gt0 //=.
     apply: lt_trans; first by apply: He.
     by rewrite ltr_nat.
   exists (n.+1).
   have temp: (r n.+1)%:num < n.+1%:R^-1.
    have: P n.+1 (a n, r n)   (a (n.+1), r (n.+1)) by apply: (Pf (n, ar n)).
    move=> [_ B]; apply: (@lt_trans _ _ (n.+2%:R^-1) _ _); rewrite //=.
    by rewrite //= ltf_pinv ?posrE ?ltr_nat //=.
   apply: (@lt_trans _ _ (2* n.+1%:R^-1) _ _);
   by rewrite -ltr_pdivl_mull ?mulrA ?(mulrC 2^-1 2) ?mulfV ?(mulrC 2^-1 e) ?div1r.
 exists (a n); exists n; first by [].
 move =>  m nsupm.
 apply: (@lt_trans _ _ (2*(r n)%:num) (`|a n - a m|) e); last  by [].
 have : (closed_ball (a n) (r n)%:num) (a m).
   move : (Suite_ball n m nsupm).
   have : closed_ball (a m) (r m)%:num (a m) by apply: closed_ballxx.
   by move=> temp1 Ha; move : (Ha (a m) temp1).
 rewrite closed_ballE /closed_ball_ //= => temp.
 rewrite (@le_lt_trans _ _ (r n)%:num (`|a n - a m|) (2*(r n)%:num)) //.
 rewrite  -?ltr_pdivr_mulr ?mulfV ?ltr1n //=.
have cauchya : (cauchy (a @ \oo)) by apply: cauchy_exP.
have : cvg (a @ \oo) by apply: cauchy_cvg.
rewrite cvg_ex //=.
move=> [l Hl] {Hf Dy OpenD H cauchya cauchyexa}.
exists l; split.
  have Hinter : (closed_ball a0 r0%:num) l.
  apply: (@closed_cvg _ _ \oo eventually_filter a); first by [].
  move=> m.
  have temp:  (0 <= m)%N by apply: leq0n.
    move : (Suite_ball 0%N m temp).
    have : closed_ball (a m) (r m)%:num (a m) by apply: closed_ballxx.
  by move=> temp1 Ha; move : (Ha (a m) temp1).
  by apply: closed_ball_closed.
  have : closed_ball a0 r0%:num `<=` D.
   move: Ball_a0; rewrite closed_ballE //= subsetI; apply:  proj1.
  by move=>  Htemp; move : (Htemp l Hinter).
move=> i _.
have : closed_ball (a i) (r i)%:num l.
rewrite -(@cvg_shiftn i _ a l) in Hl.
simpl in Hl.
have partiecvg:  forall n : nat, closed_ball (a i) (r i)%:num (a (n + i)%N).
  move=> n; apply: (Suite_ball i (n +i)%N); first by apply: leq_addl.
  by apply: closed_ballxx.
apply: (@closed_cvg _ _ \oo eventually_filter (fun n : nat => a (n+i)%N)) => //=.
  by apply: closed_ball_closed.
case i.
   by rewrite subsetI in Ball_a0; move: Ball_a0; move=> [_ p] la0; move: (p l la0).
move=> n.
have [temp _] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply : (Pf (n , ar n)).
by rewrite subsetI in temp; move : temp; move=> [_ p] lan1; move: (p l lan1).
Qed.

End Baire.

Section banach_steinhaus.
Variable (K: realType).
Variable (V: completeNormedModType K)  (W: normedModType K).

Definition bounded_fun_norm (f : V -> W) :=
  forall r, exists M, forall x, `|x| <= r -> `|f x| <= M.

Lemma bounded_landau (f :{linear V->W}) : (* imp to define in normedtype.v *)
  bounded_fun_norm f <-> ((f : V -> W) =O_ (0:V) cst (1 : K^o)).
Proof.
split.
  rewrite eqOP => bf.
  move: (bf 1) => [M bm].
  rewrite !nearE /=; exists M; split. by  apply : num_real.
  move => x Mx; rewrite nearE nbhs_normP /=.
  exists 1; first by [].
  move => y /=; rewrite -ball_normE /ball_ //= sub0r normrN /cst normr1 mulr1 => y1.
  apply: (@le_trans _ _ M _ _).
  apply: (bm y); by apply: ltW.
  by apply: ltW.
 rewrite eqOP /=; move => Bf; apply/bounded_funP; rewrite /bounded_near.
 near=>M.
 set P :=  (X in (nbhs _ X)).
 have -> : P  = (fun x : V => (`|f x| <= M * `|cst 1%R x|)%O).
   by apply: funext => x; rewrite /cst normr1 mulr1.
 by near: M.
Grab Existential Variables. all: end_near. Qed.


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
move => P Q H; apply: or_asboolP; rewrite !asbool_neg -negb_and -asbool_and.
by apply /asboolPn.
Qed.

Definition pointwise_bounded (F : set (V -> W)) :=
  forall x, exists M, forall f, F f -> `|f x| <= M.

Definition uniform_bounded (F : set (V -> W)) :=
  forall r, exists M, forall f, F f -> forall x, `|x| <= r -> `|f x| <= M.

Theorem Banach_Steinhauss (F: set ((V -> W))):
  (forall f, (F f) -> bounded_fun_norm f /\ linear f) ->
  pointwise_bounded F -> uniform_bounded F.
Proof.
move=> Propf BoundedF.
set O := (fun n :nat => \bigcup_(f in F) ((normr \o f)@^-1` [set y | y > n%:R])).
have O_open: forall n : nat, open ( O n ).
  move=>n.
  apply: open_bigU => i App.
  apply: (@open_comp _ _ ((normr : W -> K^o) \o i) [set y | y > n%:R]).
  have Ci : continuous i.
    have Li : linear i by apply Propf.
    have Bi : bounded_fun_norm i by apply Propf.
    have Landaui : i =O_ (0:V) cst (1:K^o) by apply (@bounded_landau (Linear Li)).
    by apply: (@linear_continuous K V W (Linear Li)).
  move=> x Hx ; apply: continuous_comp; first by apply: Ci.
  by apply: norm_continuous.
  by apply: open_gt.
set O_inf := (\bigcap_i ( O i)).
have  O_infempty : O_inf = set0.
rewrite -subset0 => x //=.
move: (BoundedF x) => [M HMx];  rewrite /O_inf  /O //=  /bigsetI /bigsetU //=.
case  /(_ (`|Rtoint (Rfloor M + 1%:~R)|%N)); first by rewrite /setT.
move=> f  Hf abs; move : (HMx f Hf) => abs2.
have: (`|Rtoint (Rfloor M + 1%:~R)|%:R < M) by  apply: (@lt_le_trans _ _ (`|f x|)).
have : (M < `|Rtoint(Rfloor M + 1%:~R)|%:R)
  by apply : floor_nat_comp; apply: (@le_trans _ _ `|f x|).
by apply : lt_nsym.
have BaireV : Baire V by apply : DeBaire.
have ContraBaire : exists i : nat, not (dense (O i)).
  unfold Baire in BaireV.
  have BaireO : (forall i : nat, open(O i) /\ dense (O i)) -> dense (O_inf) by apply (BaireV O).
  apply contra_not in BaireO.
  move: BaireO => /asboolPn /existsp_asboolPn [n /and_asboolP /nandP Hn].
  by exists n ; case : Hn => /asboolPn.
  rewrite /dense O_infempty ; apply /existsNP;exists setT; elim.
  * by move=> x; rewrite setI0.
  * by exists point.
  * by apply: openT.
have [n [x0 [ r H ] ] k] : exists n :nat , exists x : V,
             exists r : {posnum K}, (ball x r%:num) `<=` (~` (O n)).
  move: ContraBaire =>
  [i /(denseNE) [ O0 [ [ x /open_nbhs_nbhs /nbhs_ballP [r [r0 bxr]]
   /((@subsetI_eq0 _ (ball x r) O0 (O i) (O i)))]]]] H2.
   by exists i; exists x; exists (PosNum r0) ;apply: setIsubset; apply H2.
exists ((n%:R + n%:R) * k * 2 /r%:num).
move=> f Hf y Hx; move: (Propf f Hf) => [ _ linf].
case: (eqVneq y 0) => [-> | Zeroy].
  have -> : f 0 =0 by rewrite -(linear0  (Linear linf)).
  rewrite normr0 !mulr_ge0 -?natrD ?ler0n //=.
  by rewrite (@le_trans _ _ `|y| _ _).
have majballi : forall f, forall x, F f -> (ball x0 r%:num) x -> (`|f x | <= n%:R)%O.
move=> g x Fg Bx; move: (H x Bx).
rewrite /O //= /bigsetU /setC //= exists2P -forallNP.
move /(_  g); case /not_and_or ; first by [].
by move=> /(@negP ((n%:R < `|g x|)%O)); rewrite -leNgt .
have majball : forall f, forall x, F f -> (ball x0 r%:num) x -> (`|f (x - x0) | <= (n%:R + n%:R))%O.
move=> g x Fg; move: (Propf g Fg) => [Bg Lg].
have Ling : g(x - x0) = g(x) - g(x0) by apply: (@linearsub x x0 g).
rewrite Ling => Ballx.
move: (majballi g x Fg Ballx) => Majx.
move: (majballi g x0 Fg   (ball_center x0 r)) => Majx0.
have Majf : `| g x | + `|g x0| <= n%:R + n%:R
  by apply: (@ler_add _ `|g x| n%:R `|g x0| n%:R).
apply: (@le_trans _ _ (`|g x| + `|g x0|) (`|g x - g x0|) (n%:R + n%:R)).
  by apply: ler_norm_sub.
by [].
have ballprop : ball x0 r%:num (2^-1  * (r%:num / `|y|) *: y  + x0).
  rewrite -ball_normE /ball_ /= opprD.
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
case: n; first by rewrite addr0 mulr0 (mulrC 0) mulr0.
move=> n; rewrite -ler_pdivl_mulr //= -mulrC mulrA mulVf //=.
by rewrite (mulrC 1) mulr1.
rewrite mulr_gt0 ?invr_gt0 ?normr_gt0 //=.
rewrite mulr_gt0 ?invr_gt0 ?normr_gt0 //=.
by rewrite invr_neq0; rewrite ?normrE.
Qed.

End banach_steinhaus.
