From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import interval_inference.
From mathcomp Require Import wochoice boolp classical_sets topology reals.
From mathcomp Require Import filter reals normedtype.
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
 Import GRing.Theory.
 Import Num.Theory.

Section SetPredRels.

 Variables T U : Type.
 Implicit Types f g : T -> U -> Prop.
 (* Functional (possibly empty or partial) graphs *)
 Definition functional f :=
   forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

End SetPredRels.


Section OrderRels.

 Variable (R : numDomainType).

 (* Upper bound *)
 Definition ubd (s : set R) (a : R) := forall x, s x -> x <= a.

 (* Lower bound *)
 Definition ibd (s : set R) (a : R) := forall x, s x -> a <= x.

 (* the intension is that f is the graph of a function bounded by p *)
 Definition maj_by T p (f : T -> R -> Prop) :=
   forall v r, f v r -> r <= p v.

 End OrderRels.


 Section LinAndCvx.

 Variables (R : numDomainType) (V : lmodType R).

 Definition convex_fun (p : V -> R) :=  forall v1 v2 l m,
   ( 0 <= l /\ 0 <= m) ->  l + m = 1 -> p (l *: v1 + m *: v2) <= l * (p v1) + m * (p v2).

 Definition linear_rel (f : V -> R -> Prop) :=
   forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

 Variable f : V -> R -> Prop.
 Hypothesis lrf : linear_rel f.

 Lemma linrel_00 x r : f x r -> f 0 0.
 Proof.
 suff -> : f 0 0 = f (x + (-1) *: x) (r + (-1) * r) by move=> h; apply: lrf.
 by rewrite scaleNr mulNr mul1r scale1r !subrr.
 Qed.

 Lemma linrel_scale x r l : f x r -> f (l *: x) (l * r).
 Proof.
 move=> fxr.
 have -> : f (l *: x) (l * r) = f (0 + l *: x) (0 + l * r) by rewrite !add0r.
 by apply: lrf=> //; apply: linrel_00 fxr.
 Qed.

 Lemma linrel_add x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2)(r1 - r2).
 Proof.
     have -> : x1 - x2 = x1 + (-1) *: x2 by rewrite scaleNr scale1r.
     have -> : r1 - r2 = r1 + (-1) * r2 by rewrite mulNr mul1r.
     by apply: lrf.
 Qed.


 Definition add_line f w a := fun v r =>
   exists v' : V, exists r' : R, exists lambda : R,
         [/\ f v' r', v = v' + lambda *: w & r = r' + lambda * a].

 End LinAndCvx.


 Section HBPreparation.

 Variables (R : realFieldType) (V : lmodType R).

 Variables (F G : set V) (phi : V -> R) (p : V -> R).

Hypothesis linphiF : forall v1 v2 l, F v1 -> F v2 ->
                              phi (v1 + l *: v2) = phi v1 + l * (phi v2).

 Implicit Types (f g : V -> R -> Prop).

 Hypothesis F0 : F 0.

Fact phi0 : phi 0 = 0.
Proof.
have -> : 0 = 0 + (-1) *: 0 :> V by rewrite scaler0 addr0.
by rewrite linphiF // mulN1r addrN.
Qed.

 Hypothesis p_cvx : convex_fun p.

 Hypothesis sup : forall (A : set R) (a m : R),
     A a -> ubd A m ->
     {s : R | ubd A s /\ forall u, ubd A u -> s <= u}.

 Hypothesis inf : forall (A : set R) (a m : R),
     A a ->  ibd A m ->
     {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

 (* f is a subset of (V x R), if v is in pi_1 f, then (v, phi v) is in f.
    Otherwise said, the graph of phi restructed to pi_1 f is included in f*)

 Definition prol f := forall v, F v -> f v (phi v).

 Definition spec (f : V -> R -> Prop) :=
   [/\ functional f, linear_rel f, maj_by p f &  prol f].

 Record zorn_type : Type := ZornType
   {carrier : V -> R -> Prop; specP : spec carrier}.

 Hypothesis spec_phi : spec (fun v r => F v /\ r = phi v).

 Definition zphi := ZornType spec_phi.

 Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
 Proof.
 case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; move: pm1 pm2; rewrite e => pm1 pm2.
 by congr ZornType; apply: Prop_irrelevance.
 Qed.

  Definition zorn_rel (z1 z2 : zorn_type):= forall x y, (carrier z1 x y) ->  (carrier z2 x y ). 
 
 (* Zorn applied to the relation of extending the graph of the first function *)
 Lemma zorn_rel_ex : exists g : zorn_type, forall z, zorn_rel g z -> z = g.
 Proof.
 pose Rbool := (fun x y => `[< zorn_rel x y >]).
 have RboolP : forall z t, Rbool z t <-> zorn_rel z t by split; move => /asboolP //=. 
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
 have g_fun : functional g.
   move=> v r1 r2 [a [Aa avr1]] [b [Ab bvr2]].
   have [] : Rbool a b \/ Rbool b a by exact: Amax.
      - rewrite /Rbool /RboolP /zorn_rel; case: b Ab bvr2 {Aa}.
        move => s2 [fs2 _ _ _] /= _ s2vr2 /asboolP ecas2.
     by move/ecas2: avr1 => /fs2 /(_ s2vr2).
   - rewrite /Rbool /RboolP  /zorn_rel; case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 /asboolP ecbs1.
     by move/ecbs1: bvr2; apply: fs1.
 have g_lin : linear_rel g.
   move=> v1 v2 l r1 r2 [a1 [Aa1 c1]] [a2 [Aa2 c2]]. 
   have [/RboolP sc12 | /RboolP sc21] := Amax _ _ Aa1 Aa2.
   - have {c1 sc12 Aa1 a1} c1 :  carrier a2 v1 r1 by apply: sc12.
     exists a2; split=> //; case: a2 {Aa2} c2 c1 => c /= [_ hl _ _] *; exact: hl.
   - have {c2 sc21 Aa2 a2} c2 :  carrier a1 v2 r2 by apply: sc21.
     exists a1; split=> //; case: a1 {Aa1} c2 c1 => c /= [_ hl _ _] *; exact: hl.
 have g_majp : maj_by p g by move=> v r [[c [fs1 ls1 ms1 ps1]]] /= [_ /ms1].
 have g_prol : prol g.
   move=> *; exists w; split=> //; case: w Aw => [c [_ _ _ hp]] _ //=; exact: hp.
 have spec_g : spec g by split.
 pose zg := ZornType spec_g.
 by  exists zg => [a Aa]; apply/RboolP; rewrite /zorn_rel  => v r cvr; exists a.
 Qed. 

 
 Variable g : zorn_type.

 Hypothesis gP : forall z, zorn_rel g z -> z = g.

 (*The next lemma proves that when z is of zorn_type, it can be extended on any
  real line directed by an arbitrary vector v *)

 Lemma domain_extend  (z : zorn_type) v :
     exists2 ze : zorn_type, (zorn_rel z ze) & (exists r, (carrier ze)  v r).
 Proof.
 case: (lem (exists r, (carrier z v r))).
   by case=> r rP; exists z => //; exists r.
 case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
 have c00 : c 0 0.
   rewrite -phi0; exact: ps1.
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
       rewrite /rhs !mulrDl ![_  * _ / _]mulrAC; apply: p_cvx.
       split.
        rewrite divr_ge0 //=.
          by apply : ltW.
          by rewrite addr_ge0 //= ; apply: ltW.
        rewrite divr_ge0 //=.
          by apply : ltW.
          by rewrite  addr_ge0 //= ;  apply: ltW.
     by rewrite -mulrDl mulfV //; apply: lt0r_neq0; rewrite addr_gt0.
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
     have exPa : Pa (a 0 0 1) by exists 0; exists 0; exists 1; split.
     have exPb : Pb (b 0 0 1) by exists 0; exists 0; exists 1; split.
     have majPa x : Pa x -> x <= b 0 0 1.
       move=> [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have minPb x : Pb x -> a 0 0 1 <= x.
       move=> [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have [sa [ubdP saP]]:= sup exPa majPa; have [ib [ibdP ibP]]:= inf exPb minPb.
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
 pose z' := add_line c v a.
 have z'_extends :  forall v r, c v r -> z' v r.
   move=> x r cxr; exists x; exists r; exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 have z'_prol : prol z'.
   move=> x /ps1 cxphix; exists x; exists (phi x); exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 - have z'_maj_by_p : maj_by p z'.
   by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
 - have z'_lin : linear_rel z'.
   move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
   set w := (X in z' X _); set s := (X in z' _ X).
   have {w} -> : w = w1 + l *: w2 + (m1 + l * m2) *: v.
     by rewrite /w !scalerDr !scalerDl scalerA -!addrA [X in _ + X]addrCA.
   have {s} -> : s = s1 + l * s2 + (m1 + l * m2) * a.
     by rewrite /s !mulrDr !mulrDl mulrA -!addrA [X in _ + X]addrCA.
   exists (w1 + l *: w2); exists (s1 + l * s2); exists (m1 + l * m2); split=> //.
   exact: ls1.
 - have z'_functional : functional z'.
   move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
   have h1 (x : V) (r l : R) : x = l *: v ->  c x r -> x = 0 /\ l = 0.
     move=> -> cxr; case: (l =P 0) => [-> | /eqP ln0]; first by rewrite scale0r.
     suff cvs: c v (l^-1 * r) by elim:nzv; exists (l^-1 * r).
     suff -> : v = l ^-1 *: (l *: v) by exact: linrel_scale.
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
 have z'_spec : spec z' by split.
 pose zz' := ZornType z'_spec.
 exists zz'; rewrite /zorn_rel => //=; exists a; exists 0; exists 0; exists 1.
 by rewrite add0r mul1r scale1r add0r; split.
 Qed.

 Lemma tot_g v : exists r, carrier g v r.
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


 Section HahnBanachold.
(* Now we prove HahnBanach on functions*)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)
  
Variables (R : realFieldType) (V : lmodType R).

Hypothesis sup : forall (A : set R) (a m : R),
    A a -> ubd A m ->
    {s : R | ubd A s /\ forall u, ubd A u -> s <= u}. 

(* This could be obtained from sup but we are lazy here *)
Hypothesis inf : forall (A : set R) (a m : R),
    A a ->  ibd A m ->
    {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

(* F and G are of type V -> bool, as required by the Mathematical Components
   interfaces. f is a linear application from (the entire) V to R. *)
Variables (F G : pred V) (f : V -> R) (p : V -> R).

(* MathComp seems to lack of an interface for submodules of V, so for now
   we state "by hand" that F is closed under linear combinations. *)
Hypothesis F0 : F 0.
Hypothesis linF : forall v1 v2 l, F v1 -> F v2 -> F (v1 + l *: v2).

Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 -> 
                              f (v1 + l *: v2) = f v1 + l * (f v2).

(* In fact we do not need G to be a superset of F *)
(* Hypothesis sFG : subpred F G. *)

Hypothesis p_cvx : convex_fun p.

Hypothesis f_bounded_by_p : forall x, F x -> f x <= p x.

Theorem HahnBanachold : exists g : {scalar V}, 
  (forall x,  g x <= p x) /\ (forall x, F x -> g x = f x).
pose graphF v r := F v /\ r = f v.
have func_graphF : functional graphF by move=> v r1 r2 [Fv ->] [_ ->].
have lin_graphF : linear_rel graphF.
  move=> v1 v2 l r1 r2 [Fv1 ->] [Fv2 ->]; split; first exact: linF.
  by rewrite linfF.
have maj_graphF : maj_by p graphF by move=> v r [Fv ->]; exact: f_bounded_by_p.

have prol_graphF : prol F f graphF by move=> v Fv; split.
have graphFP : spec F f p graphF by split.
have [z zmax]:= zorn_rel_ex graphFP.
pose FP v : Prop := F v.
have FP0 : FP 0 by [].
have [g gP]:= hb_witness linfF FP0 p_cvx sup inf zmax.
have scalg : linear_for *%R g.
  case: z {zmax} gP=> [c [_ ls1 _ _]] /= gP.
  have addg : additive g.
     move=> w1 w2;  apply/gP.
     apply: linrel_add.
     exact ls1.
     by apply /gP.
     by apply /gP.
  suff scalg : scalable_for  *%R g.
    move=> a u v.
    rewrite -gP.
    rewrite (addrC _ v).
    rewrite (addrC _ (g v)).
    apply: ls1.
    by apply /gP.
    by apply /gP.
  by move=> w l; apply/gP; apply: linrel_scale=> //; apply/gP.
pose H := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g H.
exists g'.
have grxtf v : F v -> g v = f v.
  move=> Fv; apply/gP; case: z {zmax gP} => [c [_ _ _ pf]] /=; exact: pf.
  suff pmajg v :  g v <= p v by split.
    by  case: z {zmax} gP => [c [_ _ bp _]] /= gP; apply/bp/gP.
Qed.

End HahnBanachold.

 

Section HahnBanachnew.
(* Now we prove HahnBanach on functions*)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)

Variables (R : realFieldType) (V : lmodType R).

Hypothesis sup : forall (A : set R) (a m : R),
    A a -> ubd A m ->
    {s : R | ubd A s /\ forall u, ubd A u -> s <= u}.

(* This could be obtained from sup but we are lazy here *)
Hypothesis inf : forall (A : set R) (a m : R),
    A a ->  ibd A m ->
    {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

Variables (F : subLmodType V) (f : {linear F -> R}) (p : V -> R).

Hypothesis p_cvx : convex_fun p.

Hypothesis f_bounded_by_p : forall x : F,  (f x) <= (p (val x)).

Theorem newHahnBanach : exists g : {scalar V},
  (forall x,  g x <= p x) /\ (forall x, F x -> g (val x) = f x).
pose graphF v r :=  r = f v.
have graphFP: spec [set: F] f (fun z => p (val z)) graphF. split => //=.
 - by move=> v r1 r2  [->] [ ->]. 
 - by move=> v1 v2 l r1 r2; rewrite /graphF => -> -> ;rewrite !linearE. 
   by  move=> v r [->].
(*   
have [z zmax]:= zorn_rel_ex graphFP.
(*   z : zorn_type (fun x : V => F x) f p
  zmax : forall z0 : zorn_type (fun x : V => F x) f p, zorn_rel z z0 -> z0 = z
*)
pose FP v : Prop := F v.
have FP0 : FP 0 by [].
have [g gP]:= hb_witness linfF FP0 p_cvx sup inf zmax.
have scalg : linear_for *%R g.
  case: z {zmax} gP=> [c [_ ls1 _ _]] /= gP.
  have addg : additive g.
     move=> w1 w2;  apply/gP.
     apply: linrel_add.
     exact ls1.
     by apply /gP.
     by apply /gP.
  suff scalg : scalable_for  *%R g.
    move=> a u v.
    rewrite -gP.
    rewrite (addrC _ v).
    rewrite (addrC _ (g v)).
    apply: ls1.
    by apply /gP.
    by apply /gP.
  by move=> w l; apply/gP; apply: linrel_scale=> //; apply/gP.
pose H := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g H.
exists g'.
have grxtf v : F v -> g v = f v.
  move=> Fv; apply/gP; case: z {zmax gP} => [c [_ _ _ pf]] /=; exact: pf.
  suff pmajg v :  g v <= p v by split.
    by  case: z {zmax} gP => [c [_ _ bp _]] /= gP; apply/bp/gP.
Qed.
 *)
Admitted.
End HahnBanachnew.


Section HBGeom.
Variable (R : realType) (V : normedModType R) (F : pred V) (f : V -> R) (F0 : F 0).

Hypothesis linF : forall (v1 v2 : V) (l : R), F v1 -> F v2 -> F (v1 + l *: v2).
Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 -> f (v1 + l *: v2) = f v1 + l * (f v2).

(*Looked a long time for within *)
Definition continuousR_on ( G : set V ) (g : V -> R) :=
  {within G, continuous g}.
(*  (forall x, (g @ (within G (nbhs x))) --> g x).*)

(*Do we need to have F x ?*)
Definition continuousR_on_at (G : set V ) (x : V ) (g : V -> R)  :=
  g @ (within G (nbhs x)) --> (g x).

Lemma continuousR_scalar_on_bounded :
  (continuousR_on_at F 0 f) ->
  (exists  r , (r > 0 ) /\ (forall x : V, F x ->   (`|f x| ) <=  `|x| * r)).
Proof.
  rewrite /continuousR_on_at.
  move  => /cvg_ballP  H.
  have H':  (0 < 1) by [].
  have : \forall x \near within (fun x : V => F x) (nbhs 0), ball (f 0) 1 (f x).
  apply: H. by [].
  have f0 : f 0 = 0.
     suff -> : f 0 = f (0 + (-1)*: 0) by rewrite linfF // mulNr mul1r addrN.
     by rewrite scaleNr scaler0 addrN.
  rewrite /( _ @ _ ) //= nearE /(within _ ) f0 //=. rewrite near_simpl.
  rewrite -nbhs_nearE => H0 {H} ; move : (nbhs_ex H0) => [tp H] {H0}.
  (*pose t := tp%:num .  *)
  exists (2*(tp%:num)^-1). split=> //.
  move=> x. case:  (lem (x=0)).
  - by move=> ->; rewrite f0 normr0 normr0 //= mul0r.
  - move/eqP=> xneq0 Fx.
  pose a : V := (`|x|^-1 * (tp%:num)/2 ) *: x.
  have Btp : ball 0  (tp%:num) a.
   apply : ball_sym ; rewrite -ball_normE /ball_ /=  subr0.
   rewrite normrZ mulrC normrM.
   rewrite !gtr0_norm //= ; last first.
     rewrite  pmulr_lgt0 // ?invr_gt0 ?normr_gt0 //.
   rewrite mulrC -mulrA -mulrA ltr_pdivrMl; last by rewrite normr_gt0.
   rewrite mulrC -mulrA  gtr_pMl.
   rewrite invf_lt1 //=.
     by rewrite ltr1n.
   by  rewrite pmulr_lgt0 // !normr_gt0.
 have Fa : F a by rewrite -[a]add0r; apply: linF.
 have :  `|f a| < 1.
    by move: (H _ Btp Fa); rewrite /ball /ball_ //= sub0r normrN.
  suff ->  : ( f a =  ( (`|x|^-1) * (tp%:num)/2 ) * ( f x)) .
     rewrite normrM (gtr0_norm) //.
     rewrite mulrC mulrC  -mulrA  -mulrA  ltr_pdivrMl //= ;
       last by rewrite normr_gt0.
     rewrite mulrC [(_*1)]mulrC mul1r.
     rewrite -[X in _ * X < _ ]invf_div ltr_pdivrMr //=; apply: ltW.
     by rewrite !mulr_gt0  ?normr_gt0  // ?invr_gt0 normr_gt0.
 suff -> : a = 0+ (`|x|^-1 * tp%:num /2) *: x by rewrite linfF // f0 add0r.
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
split.
  by apply: sup_upper_bound.
  by move => x; apply: sup_le_ub.
Qed.

(*TODO: should be lb_le_inf: *)
Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  lbound A m ->
     {s : R | lbound A s /\ forall u, lbound A u -> u <= s}.
  move => A a m Aa minAm.
  have [A0 Alb]: has_inf A. split; first by exists a.
    by exists m => x; apply minAm.
  exists (reals.inf A).
  split.
    exact: ge_inf.
  by move => x; apply: lb_le_inf.
Qed.

Notation myHB :=
  (HahnBanachold mymysup mymyinf F0 linF linfF).

Theorem HB_geom_normed :
  continuousR_on_at F 0 f ->
  exists g: {scalar V}, (continuous (g : V -> R)) /\ (forall x, F x -> (g x = f x)).
Proof.
  move=> H; move: (continuousR_scalar_on_bounded H) => [r [ltr0 fxrx]] {H}.
  pose p:= fun x : V => `|x|*r.
 have convp: convex_fun p.
   move=> v1 v2 l m [lt0l lt0m] addlm1 //= ; rewrite !/( p _) !mulrA -mulrDl.
   suff: `|l *: v1 + m *: v2|  <= (l * `|v1| + m * `|v2|).
     move => h; apply : ler_pM; last by [].
     by apply : normr_ge0.
     by apply : ltW.
       by [].
   have labs : `|l| = l by apply/normr_idP.
   have mabs: `|m| = m by apply/normr_idP.
   rewrite -[in(_*_)]labs -[in(m*_)]mabs.
   rewrite -!normrZ.
   by apply : ler_normD.
 have majfp : forall x, F x -> f x <= p x.
   move => x Fx; rewrite /(p _) ; apply : le_trans ; last by [].
   apply : le_trans.
   apply : ler_norm.
   by apply : (fxrx x Fx).
 move: (myHB convp majfp) => [ g  [majgp  F_eqgf] ] {majfp}.
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


Section newHBGeom.

  (* TODO: port to ctvsType, by porting lemmas on continuous bounded linear functions there *)

Variable (R : realType) (V: normedModType R) (F : subLmodType V) (f : {linear F -> R}).

(* One needs to define the topological structure on F as the one induced by V, and make it  a normedModtype, as was done for subLmodType *)


(*
Lemma mymysup : forall (A : set R) (a m : R),
     A a -> ubound A m ->
     {s : R | ubound A s /\ forall u, ubound A u -> s <= u}.
Proof.
  move => A a m Aa majAm.
  have [A0 Aub]: has_sup A. split; first by exists a.
    by exists m => x; apply majAm.
  exists (reals.sup A).
split.
  by apply: sup_upper_bound.
  by move => x; apply: sup_le_ub.
Qed.

(*TODO: should be lb_le_inf: *)
Lemma mymyinf : forall (A : set R) (a m : R),
     A a ->  lbound A m ->
     {s : R | lbound A s /\ forall u, lbound A u -> u <= s}.
  move => A a m Aa minAm.
  have [A0 Alb]: has_inf A. split; first by exists a.
    by exists m => x; apply minAm.
  exists (reals.inf A).
  split.
    exact: ge_inf.
  by move => x; apply: lb_le_inf.
Qed.


Notation myHB :=
  (HahnBanach (boolp.EM)  mymysup mymyinf F0 linF linfF).
 *)

 Search "continuous" "subspace".  
(* bounded_linear_continuous: forall [R : numFieldType] [V W : normedModType R] [f : {linear V -> W}], bounded_near f (nbhs (0 : V)) -> continuous f
linear_bounded_continuous: forall [R : numFieldType] [V W : normedModType R] (f : {linear V -> W}), bounded_near f (nbhs 0) <-> continuous f
continuous_linear_bounded: forall [R : numFieldType] [V W : normedModType R] (x : V) [f : {linear V -> W}], {for 0, continuous f} -> bounded_near f (nbhs x) *)

 (*TODO : clean the topological structure on F. Define subctvs ? *)
Theorem new_HB_geom_normed :
  continuous (f : (@initial_topology (sub_type F) V val) -> R) -> 
  exists g: {scalar V}, (continuous (g : V -> R)) /\ (forall (x : F), (g (val x) = f x)).
Proof.
  move /(_ 0) => /= H; rewrite /from_subspace /=.
  have f0 : {for 0, continuous ( (f : (@initial_topology (sub_type F) V val) -> R))}.
  admit.  
  Check (continuous_linear_bounded).
  (* TODO ; to apply this lemma, F needs to be given a normedmodtype structure *)
 (*  move=> H; move: (continuousR_scalar_on_bounded H) => [r [ltr0 fxrx]] {H}.
  (* want :   r :
  ltr0 : 0 < r
  fxrx : forall x : V, F x -> `|f x| <= `|x| * r*)
 pose p:= fun x : V => `|x|*r.
 have convp: hahn_banach_theorem.convex p.
   move=> v1 v2 l m [lt0l lt0m] addlm1 //= ; rewrite !/( p _) !mulrA -mulrDl.
   suff: `|l *: v1 + m *: v2|  <= (l * `|v1| + m * `|v2|).
     move => h; apply : ler_pM; last by [].
     by apply : normr_ge0.
     by apply : ltW.
       by [].
   have labs : `|l| = l by apply/normr_idP.
   have mabs: `|m| = m by apply/normr_idP.
   rewrite -[in(_*_)]labs -[in(m*_)]mabs.
   rewrite -!normrZ.
   by apply : ler_normD.
 have majfp : forall x, F x -> f x <= p x.
   move => x Fx; rewrite /(p _) ; apply : le_trans ; last by [].
   apply : le_trans.
   apply : ler_norm.
   by apply : (fxrx x Fx).
 move: (myHB convp majfp) => [ g  [majgp  F_eqgf] ] {majfp}.
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
*)
Admitted.  


End newHBGeom.
