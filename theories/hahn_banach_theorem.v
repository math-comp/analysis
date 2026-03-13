From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable wochoice boolp classical_sets topology reals.
From mathcomp Require Import filter reals normedtype convex.
Import numFieldNormedType.Exports.
Local Open Scope classical_set_scope.

(* Marie's proposal: encode the "partial" properties by reasoning on
  the graph of functions. The other option would be to study a partial
  order defined on subsets of the ambiant space V, on which it is possible
  to obtain a bounded lineEar form extending f. But this options seems much
  less convenient, in particular when establishing that one can extend f
  on a space with one more dimension. Indeed, exhibiting a term of type
  V -> R requires a case ternary analysis on F, the new line, and an
  explicit direct sum to ensure the definition is exhaustive. Working with
  graphs allows to leave this argument completely implicit. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.




Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope real_scope.
Import GRing.Theory.
Import Num.Theory.

 
Module Lingraph.
Section Lingraphsec.

Variables (R : numDomainType) (V : lmodType R).

Definition graph := V -> R -> Prop. 

Definition linear_graph (f : graph) :=
   forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Variable f : graph.
Hypothesis lrf : linear_graph f.

Lemma lingraph_00 x r : f x r -> f 0 0.
 Proof.
 suff -> : f 0 0 = f (x + (-1) *: x) (r + (-1) * r) by move=> h; apply: lrf.
 by rewrite scaleNr mulNr mul1r scale1r !subrr.
 Qed.

 Lemma lingraph_scale x r l : f x r -> f (l *: x) (l * r).
 Proof.
 move=> fxr.
 have -> : f (l *: x) (l * r) = f (0 + l *: x) (0 + l * r) by rewrite !add0r.
 by apply: lrf=> //; apply: lingraph_00 fxr.
 Qed.

 Lemma lingraph_add x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2)(r1 - r2).
 Proof.
     have -> : x1 - x2 = x1 + (-1) *: x2 by rewrite scaleNr scale1r.
     have -> : r1 - r2 = r1 + (-1) * r2 by rewrite mulNr mul1r.
     by apply: lrf.
 Qed.


 Definition add_line f w a := fun v r =>
   exists v' : V, exists r' : R, exists lambda : R,
         [/\ f v' r', v = v' + lambda *: w & r = r' + lambda * a].

End Lingraphsec.
End Lingraph.


Section HBPreparation.
Import Lingraph.
 (* TODO: getting rid of relations and linear relations to make Zorn act on functions only ? *)

Variables (R : realType) (V : lmodType R) (F : pred V).

Variables (F' : subLmodType F) (phi : {linear F' -> R}) (p : V -> R).

Implicit Types (f g : graph V).

Hypothesis phi_le_p : forall v, (phi v) <= (p (val v)).
 
Hypothesis p_cvx : (@convex_function  R V [set: V]  p).

Definition extend_graph f := forall (v : F'), f (\val v) (phi v).

Definition le_graph p f :=
   forall v r, f v r -> r <= p v.

Definition functional_graph f :=
  forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

Definition linear_graph f :=
   forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Definition le_extend_graph f :=
   [/\ functional_graph f, linear_graph f, le_graph p f &  extend_graph f].

Record zorn_type : Type := ZornType
   {carrier : graph V; specP : le_extend_graph carrier}.

Let spec_phi : le_extend_graph (fun v r =>  exists2 y : F', v = val y & r = phi y).
Proof.
split.
- by move=> v r1 r2 [y1 ->  ->] [y2 + ->] => /val_inj ->.
- move => v1 v2 l r1 r2 [y1 -> ->] [y2 ->  ->].
  by exists (y1 + l *: y2); rewrite !linearD !linearZ //.  
- by move => r v [y -> ->].
- by move => v; exists v.   
Qed. 

Definition zphi := ZornType spec_phi.

Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
Proof.
case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; move: pm1 pm2; rewrite e => pm1 pm2.
by congr ZornType; apply: Prop_irrelevance.
Qed.

Definition zornS (z1 z2 : zorn_type):= 
   forall x y, (carrier z1 x y) ->  (carrier z2 x y ). 

 (* Zorn applied to the relation of extending the graph of the first function *)
 Lemma zornS_ex : exists g : zorn_type, forall z, zornS g z -> z = g.
 Proof.
 pose Rbool := (fun x y => `[< zornS x y >]).
 have RboolP : forall z t, Rbool z t <-> zornS z t by split; move => /asboolP //=. 
 suff [t st]:  exists t : zorn_type, forall s : zorn_type, Rbool t s -> s = t. 
    by exists t;  move => z /RboolP tz; apply: st. 
         apply: (@Zorn zorn_type Rbool).
 - by move => t; apply/RboolP. 
 - by move => r s t /RboolP  a /RboolP  b; apply/RboolP => x y /a /b. 
 - move => r s /RboolP a /RboolP b; apply: zorn_type_eq.
   by apply: funext => z; apply: funext => h;apply: propext; split => [/a | /b]. 
 - move => A Amax.
 case: (lem (exists a, A a)) => [[w Aw] | eA]; last first.
   by exists zphi => a Aa; elim: eA; exists a.
 (* g is the union of the graphs indexed by elements in a *)
 pose g v r := exists a, A a /\ (carrier a v r).
 have g_fun : functional_graph g.
   move=> v r1 r2 [a [Aa avr1]] [b [Ab bvr2]].
   have [] : Rbool a b \/ Rbool b a by exact: Amax.
      - rewrite /Rbool /RboolP /zornS; case: b Ab bvr2 {Aa}.
        move => s2 [fs2 _ _ _] /= _ s2vr2 /asboolP ecas2.
     by move/ecas2: avr1 => /fs2 /(_ s2vr2).
   - rewrite /Rbool /RboolP  /zornS; case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 /asboolP ecbs1.
     by move/ecbs1: bvr2; apply: fs1.
 have g_lin : linear_graph g.
   move=> v1 v2 l r1 r2 [a1 [Aa1 c1]] [a2 [Aa2 c2]]. 
   have [/RboolP sc12 | /RboolP sc21] := Amax _ _ Aa1 Aa2.
   - have {c1 sc12 Aa1 a1} c1 :  carrier a2 v1 r1 by apply: sc12.
     exists a2; split=> //; case: a2 {Aa2} c2 c1 => c /= [_ hl _ _] *; exact: hl.
   - have {c2 sc21 Aa2 a2} c2 :  carrier a1 v2 r2 by apply: sc21.
     exists a1; split=> //; case: a1 {Aa1} c2 c1 => c /= [_ hl _ _] *; exact: hl.
 have g_majp : le_graph p g by move=> v r [[c [fs1 ls1 ms1 ps1]]] /= [_ /ms1].
 have g_prol : extend_graph g.
   move=> *; exists w; split=> //; case: w Aw => [c [_ _ _ hp]] _ //=; exact: hp.
 have spec_g : le_extend_graph g by split.
 pose zg := ZornType spec_g.
 by  exists zg => [a Aa]; apply/RboolP; rewrite /zornS  => v r cvr; exists a.
 Qed. 

 
 Variable g : zorn_type.

 Hypothesis gP : forall z, zornS g z -> z = g.

 (*The next lemma proves that when z is of zorn_type, it can be extended on any
  real line directed by an arbitrary vector v *)

 Lemma divDl_ge0 (s t : R) (s0 : 0 <= s) (t0 : 0 <= t) : 0 <= s / (s +t).
 by apply: divr_ge0 => //; apply: addr_ge0.
 Qed.
 
 Lemma divDl_le1 (s t : R) (s0 : 0 <= s) (t0 : 0 <= t) :  s / (s +t) <= 1.
 move: s0; rewrite le0r => /orP []; first by move => /eqP ->; rewrite mul0r //.
 move: t0; rewrite le0r => /orP [].
   by move => /eqP -> s0; rewrite addr0 divff //=; apply: lt0r_neq0. 
 by move=> t0 s0; rewrite ler_pdivrMr ?mul1r ?addr_gt0 // lerDl ltW.
 Qed.    

 Lemma divD_onem (s t : R) (s0 : 0 < s) (t0 : 0 < t): (s / (s + t)).~ = t / (s + t).
 rewrite /(_).~.
 suff -> : 1 = (s + t)/(s + t) by rewrite -mulrBl -addrAC subrr add0r. 
 rewrite divff // /eqP addr_eq0; apply/negbT/eqP => H.
 by move: s0; rewrite H oppr_gt0 ltNge; move/negP; apply; rewrite ltW.
 Qed.
 
 Lemma domain_extend  (z : zorn_type) v :
     exists2 ze : zorn_type, (zornS z ze) & (exists r, (carrier ze)  v r).
 Proof.
 case: (lem (exists r, (carrier z v r))).
   by case=> r rP; exists z => //; exists r.
 case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
 have c00 : c 0 0.
   have <- : phi 0 = 0 by rewrite linear0.
   by move: ps1; rewrite /extend_graph /= => /(_ 0) /=; rewrite GRing.val0; apply. 
 have [a aP] : exists a,  forall (x : V) (r lambda : R),
       c x r -> r + lambda * a <= p (x + lambda *: v).
   suff [a aP] : exists a,  forall (x : V) (r lambda : R),
       c x r -> 0 < lambda ->
       r + lambda * a <= p (x + lambda *: v) /\
       r - lambda * a <= p (x - lambda *: v).
     exists a=> x r lambda cxr.
     have {aP} aP := aP _ _ _ cxr.
     case: (ltrgt0P lambda) ; [by case/aP | move=> ltl0 | move->]; last first.
       by rewrite mul0r scale0r !addr0; apply: ms1.
     rewrite -[lambda]opprK scaleNr mulNr.
     have /aP [] : 0 < - lambda by rewrite oppr_gt0.
     done.
   pose b (x : V) r lambda : R := (p (x + lambda *: v) - r) / lambda.
   pose a (x : V) r lambda : R := (r - p (x - lambda *: v)) / lambda.
   have le_a_b x1 x2 r1 r2 s t : c x1 r1 -> c x2 r2 -> 0 < s -> 0 < t ->
                                 a x1 r1 s <= b x2 r2 t.
     move=> cxr1 cxr2 lt0s lt0t; rewrite /a /b.
     rewrite ler_pdivlMr // mulrAC ler_pdivrMr // mulrC [_ * s]mulrC.
     rewrite !mulrDr !mulrN lerBlDr addrAC lerBrDr.
     have /ler_pM2r <- : 0 < (s + t) ^-1 by rewrite invr_gt0 addr_gt0.
     set y1 : V := _ + _ *: _; set y2 : V :=  _ - _ *: _.
     set rhs := (X in _ <= X).
     have step1 : p (s  / (s + t) *: y1 + t  / (s + t) *: y2) <= rhs. 
       rewrite /rhs !mulrDl ![_  * _ / _]mulrAC. 
       pose st := Itv01 (divDl_ge0 (ltW lt0s) (ltW lt0t)) ((divDl_le1 (ltW lt0s) (ltW lt0t))). 
       move: (p_cvx st (in_setT y1) (in_setT y2)). 
       by rewrite /conv /= [X in ((_ <= X)-> _)]/conv /= divD_onem /=.
     apply: le_trans step1 => {rhs}.
     set u : V := (X in p X).
     have {u y1 y2} -> : u = t  / (s + t) *: x1 + s / (s + t) *: x2.
       rewrite /u ![_ / _]mulrC -!scalerA -!scalerDr /y1 /y2; congr (_ *: _).
       by rewrite !scalerDr addrCA scalerN scalerA [s * t]mulrC -scalerA addrK.
     set l := t / _; set m := s / _; set lhs := (X in X <= _).
     have {lhs} -> : lhs = l * r1 + m * r2.
       by rewrite /lhs mulrDl ![_  * _ / _]mulrAC.
     apply: ms1; apply: (ls1) => //.
     rewrite -[_ *: _]add0r -[_ * _] add0r; apply: ls1 => //.
     pose Pa : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = a x1 r1 s1].
     pose Pb : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = b x1 r1 s1].
     pose sa := reals.sup Pa. (* This is why we need realTypes, we need p with values in a realType *)
     have Pax : Pa !=set0 by exists (a 0 0 1); exists 0; exists 0; exists 1; split.
     have ubdP : ubound Pa sa.
       apply: sup_upper_bound; split => //=.
       exists (b 0 0 1) =>/= x [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have saP: forall u : R, ubound Pa u -> sa <= u by move=> u; apply: ge_sup.  
     pose ib := reals.inf Pb. (* This is why we need realTypes, we need P with values in a realType *)
     have Pbx : Pb !=set0 by exists (b 0 0 1); exists 0; exists 0; exists 1; split.
     have ibdP : lbound Pb ib.
       by apply: ge_inf; exists (a 0 0 1) =>/= x [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have ibP: forall u : R, lbound Pb u -> u <= ib by move=> u; apply: lb_le_inf Pbx.
     have le_sa_ib : sa <= ib.
       apply: saP=> r' [y [r [l [cry lt0l -> {r'}]]]].
       apply: ibP=> s' [z [s [m [crz lt0m -> {s'}]]]]; exact: le_a_b.
     pose alpha := ((sa + ib) / 2%:R).
     have le_alpha_ib : alpha <= ib by rewrite /alpha midf_le.
     have le_sa_alpha : sa <= alpha by rewrite /alpha midf_le.
     exists alpha => x r l cxr lt0l; split.
     - suff : alpha <= b x r l.
         by rewrite /b; move/ler_pdivlMr: lt0l->; rewrite lerBrDl mulrC.
       by apply: le_trans le_alpha_ib _; apply: ibdP; exists x; exists r; exists l.
     - suff : a x r l <= alpha.
         rewrite /a. move/ler_pdivrMr: lt0l->.
         by rewrite lerBlDl -lerBlDr mulrC.
         by apply: le_trans le_sa_alpha; apply: ubdP; exists x; exists r; exists l.
 pose z' := fun k r =>
   exists v' : V, exists r' : R, exists lambda : R,
         [/\ c v' r', k = v' + lambda *: v & r = r' + lambda * a].
 have z'_extends :  forall v r, c v r -> z' v r.
   move=> x r cxr; exists x; exists r; exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 have z'_prol : extend_graph z'.
  move=> x; exists (val x); exists (phi x); exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 - have z'_maj_by_p : le_graph p z'.
   by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
 - have z'_lin : linear_graph z'.
   move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
   set w := (X in z' X _); set s := (X in z' _ X).
   have {w} -> : w = w1 + l *: w2 + (m1 + l * m2) *: v.
     by rewrite /w !scalerDr !scalerDl scalerA -!addrA [X in _ + X]addrCA.
   have {s} -> : s = s1 + l * s2 + (m1 + l * m2) * a.
     by rewrite /s !mulrDr !mulrDl mulrA -!addrA [X in _ + X]addrCA.
   exists (w1 + l *: w2); exists (s1 + l * s2); exists (m1 + l * m2); split=> //.
   exact: ls1.
 - have z'_functional : functional_graph z'.
   move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
   have h1 (x : V) (r l : R) : x = l *: v ->  c x r -> x = 0 /\ l = 0.
     move=> -> cxr; case: (l =P 0) => [-> | /eqP ln0]; first by rewrite scale0r.
     suff cvs: c v (l^-1 * r) by elim:nzv; exists (l^-1 * r).
     suff -> : v = l ^-1 *: (l *: v).
       have -> :
       c ( l ^-1 *: (l *: v)) (l^-1 * r) =  
       c (0 + l ^-1 *: (l *: v)) (0 + l^-1 * r) by rewrite !add0r.
       by apply: ls1=> //; apply: linrel_00 fxr.
     by rewrite scalerA mulVf ?scale1r.
   have [rw12 erw12] : exists r,  c (w1 - w2) r.
     exists (s1 + (-1) * s2).
     have -> : w1 - w2 = w1 + (-1) *: w2 by rewrite scaleNr scale1r.
     by apply: ls1.
   have [ew12 /eqP]: w1 - w2 = 0 /\ (m2 - m1 = 0).
     apply: h1 erw12; rewrite scalerBl; apply/eqP; rewrite subr_eq addrC addrA.
     by rewrite -subr_eq opprK e1.
   suff -> : s1 = s2 by rewrite subr_eq0=> /eqP->.
   by apply: fs1 cws2; move/eqP: ew12; rewrite subr_eq0=> /eqP<-.
 have z'_spec : le_extend_graph z' by split.
 pose zz' := ZornType z'_spec.
 exists zz'; rewrite /zornS => //=; exists a; exists 0; exists 0; exists 1.
 by rewrite add0r mul1r scale1r add0r; split.
 Qed.

 Let tot_g v : exists r, carrier g v r.
 Proof.
 have [z /gP sgz [r zr]]:= domain_extend g v.
 by exists r; rewrite -sgz.
 Qed.


Lemma hb_witness : exists h : V -> R, forall v r, carrier g v r <-> (h v = r).
Proof.
move: (choice tot_g) => [h hP]; exists h => v r; split; last by move<-.
case: g gP tot_g hP => c /= [fg lg mg pg] => gP' tot_g' hP cvr.
by have -> // := fg v r (h v).
Qed.


 End HBPreparation.


Section HahnBanach.
Import Lingraph.
(* Now we prove HahnBanach on functions*)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)
  
 Variables (R : realType) (V : lmodType R) (F : pred V).

 Variables (F' : subLmodType F) (f : {linear F' -> R}) (p : V -> R).


(* MathComp seems to lack of an interface for submodules of V, so for now
   we state "by hand" that F is closed under linear combinations. *)

Hypothesis p_cvx : (@convex_function  R V [set: V]  p).

Hypothesis f_bounded_by_p : forall (z : F'), (f z  <= p (\val z)).

Theorem HahnBanach : exists g : {scalar V}, 
  (forall x,  g x <= p x) /\ (forall (z : F'), g (\val z) = f z). 
Proof.
pose graphF (v : V) r := exists2 z : F', v = \val z & r = f z.
have [z zmax]:= zornS_ex f_bounded_by_p.
have [g gP]:= (hb_witness p_cvx zmax).  
have scalg : linear_for *%R g.
  case: z {zmax} gP=> [c [_ ls1 _ _]] /= gP.
  have addg : additive g.
    by move=> w1 w2;  apply/gP; apply: lingraph_add =>//; apply/gP.
  suff scalg : scalable_for  *%R g.
    by move=> a u v; rewrite -gP (addrC _ v) (addrC _ (g v)); apply: ls1; apply /gP.
  by move=> w l; apply/gP; apply: lingraph_scale=> //; apply/gP.
pose H := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g H. 
exists g'.
split; last first. 
  by move => z'; apply/gP; case: z {zmax gP} => [c [_ _ _ pf]] /=; exact: pf.
by case: z {zmax} gP => [c [_ _ bp _]] /= gP => x; apply: bp; apply/gP.
Qed.

End HahnBanach.

Section HBGeom.
Variable (R : realType) (V : normedModType R) (F : pred V)
(F' : subLmodType F) (f : {linear F' -> R}).

Let setF := [set x : V  | exists (z : F'), val z = x].

(* TODO : define (F : subNormedModType V) so as to have (f : {linear_continuous F ->
R}), and to obtain the first hypothesis of the following theorem through the
lemmas continuous_linear_bounded*)

Theorem HB_geom_normed :
   (exists  r , (r > 0 ) /\ (forall (z : F'), (`|f z| ) <=  `|(val z)| * r)) ->
  exists g: {scalar V}, (continuous (g : V -> R)) /\ (forall (x : F'), (g (val x) = f x)).
Proof.
  move=> [r [ltr0 fxrx]].
  pose p:= fun x : V => `|x|*r.
 have convp: (@convex_function _ _ [set: V] p).
 rewrite /convex_function /conv => l v1 v2 _ _ /=.
 rewrite [X in (_ <= X)]/conv /= /p.
 apply: le_trans.
   have H  :  `|l%:num *: v1 + (l%:num).~ *: v2|  <=  `|l%:num *: v1|  + `|(l%:num).~ *: v2|.
     by apply: ler_normD.
   by apply: (@ler_pM _ _ _ r r _ _ H) => //; apply: ltW.
   rewrite mulrDl !normrZ -![_ *: _]/(_ * _).
   have -> : `|l%:num| = l%:num by apply/normr_idP.
   have -> : `|(l%:num).~| = (l%:num).~ by apply/normr_idP; apply: onem_ge0.
   by rewrite !mulrA. 
   have majfp : forall z : F', f z <= p (\val z). 
   move => z; rewrite /(p _) ; apply : le_trans; last by []. 
   by apply : ler_norm.
 move: (HahnBanach convp majfp) => [ g  [majgp  F_eqgf] ] {majfp}.
 exists g;  split; last by [].
  move=> x; rewrite /cvgP; apply: (continuousfor0_continuous).
  apply: bounded_linear_continuous.
  exists r.
  split; first by rewrite realE; apply/orP; left; apply: ltW. (* r is Numreal ... *)
  move => M m1; rewrite nbhs_ballP;  exists 1 => /=; first by [].
  move => y; rewrite -ball_normE //= sub0r => y1.
  rewrite ler_norml; apply/andP. split.
  - rewrite lerNl  -linearN; apply: (le_trans (majgp (-y))).
    by rewrite /p -[X in _ <= X]mul1r; apply: ler_pM; rewrite ?normr_ge0 ?ltW //=.
  - apply: (le_trans (majgp (y))); rewrite /p -[X in _ <= X]mul1r -normrN.
    apply: ler_pM; rewrite ?normr_ge0 ?ltW //=.
Qed.     

End HBGeom.
