From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets filter.
From mathcomp Require Import topology convex reals normedtype.

(**md**************************************************************************)
(* # The Hahn-Banach theorem                                                  *)
(*                                                                            *)
(* This file proves the Hahn-Banach theorem thanks to Zorn's lemma. Theorem   *)
(* `hahn_banach_extension` states that, considering `V` an lmodType on a      *)
(* realtype, a linear function on a subLmodType of V, that is bounded by a    *)
(* convex function, can be extended to a linear map on V bounded by the same  *)
(* convex function.                                                           *)
(* Theorem `hahn_banach_extension_normed` specifies this to the extension of  *)
(* a linear continuous function on a subspace to the whole normed module.     *)
(*                                                                            *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope real_scope.

(* TODO : use a lightweight factory to make every subLmodType a subnormedmodtype *)

(**md module with definitions on linear relations, thought of as graph of
  functions *)
Module LinearGraphInternal.
Section linear_graph.
Context (R : numDomainType) (V : lmodType R).

Definition graph := V -> R -> Prop.

Definition linear_graph (f : graph) :=
  forall v1 v2 l r1 r2, f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Variable f : graph.
Hypothesis lf : linear_graph f.

Lemma lingraph_00 x r : f x r -> f 0 0.
Proof.
by move=> fxr; have := lf (-1) fxr fxr; rewrite scaleN1r mulN1r !subrr.
Qed.

Lemma lingraphZ x r l : f x r -> f (l *: x) (l * r).
Proof. by move=> fxr; have := lf l (lingraph_00 fxr) fxr; rewrite !add0r. Qed.

Lemma lingraphD x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2) (r1 - r2).
Proof. by move=> f1 f2; have := lf (-1) f1 f2; rewrite !scaleN1r mulN1r. Qed.

End linear_graph.
End LinearGraphInternal.

(**md module with definition of the type `zorn_type` of linear functional
      graphs, bounded by a convex function and extending to the whole space a
      given linear graph *)
Module HahnBanachZornInternal.
Section hahnbanachzorn.
Import LinearGraphInternal.
Context (R : realType) (V : lmodType R) (F : pred V).
Variables (F' : subLmodType F) (phi : {linear F' -> R}) (p : V -> R).

Implicit Types f g : graph V.

Hypothesis phi_le_p : forall v, phi v <= p (val v).

Hypothesis p_cvx : @convex_function R V [set: V] p.

Definition extend_graph f := forall v : F', f (\val v) (phi v).

Definition le_graph p f := forall v r, f v r -> r <= p v.

Definition functional_graph f := forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

Definition le_extend_graph f :=
  [/\ functional_graph f, linear_graph f, le_graph p f & extend_graph f].

Record zorn_type : Type := ZornType
  {carrier : graph V; specP : le_extend_graph carrier}.

Implicit Types z : zorn_type.

Let spec_phi :
  le_extend_graph (fun v r => exists2 y : F', v = val y & r = phi y).
Proof.
split.
- by move=> v r1 r2 [y1 ->  ->] [y2 + ->] => /val_inj ->.
- move => v1 v2 l r1 r2 [y1 -> ->] [y2 -> ->].
  by exists (y1 + l *: y2); rewrite !linearD !linearZ.
- by move=> r v [y -> ->].
- by move=> v; exists v.
Qed.

Definition zphi := ZornType spec_phi.

Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
Proof.
case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; rewrite e in pm1 pm2 *.
by congr ZornType; exact: Prop_irrelevance.
Qed.

Definition zornS z1 z2 := forall x y, carrier z1 x y -> carrier z2 x y.

(* Zorn applied to the relation of extending the graph of the first function: *)
Lemma zornS_ex : exists g : zorn_type, forall z, zornS g z -> z = g.
Proof.
pose Rbool x y := `[< zornS x y >].
have RboolP z t : Rbool z t <-> zornS z t by split => /asboolP.
suff [t st] : exists t : zorn_type, forall s : zorn_type, Rbool t s -> s = t.
  by exists t; move => z /RboolP tz; exact: st.
apply: (@Zorn zorn_type Rbool); first by move=> t; exact/RboolP.
- by move=> r s t /RboolP a /RboolP b; apply/RboolP => x y /a /b.
- move=> r s /RboolP a /RboolP b; apply: zorn_type_eq.
  by apply: funext => z; apply: funext => h; apply: propext; split => [/a | /b].
move=> A Amax.
have [[w Aw]|eA] := lem (exists a, A a); last first.
  by exists zphi => a Aa; absurd: eA; exists a.
(* g is the union of the graphs indexed by elements in a *)
pose g v r := exists2 a, A a & carrier a v r.
have g_fun : functional_graph g.
  move=> v r1 r2 [a Aa avr1] [b Ab bvr2].
  have [|] : Rbool a b \/ Rbool b a by exact: Amax.
  - rewrite /Rbool /RboolP /zornS.
    case: b Ab bvr2 {Aa} => s2 [fs2 _ _ _] /= _ s2vr2 /asboolP ecas2.
    by move/ecas2 : avr1 => /fs2 /(_ s2vr2).
  - rewrite /Rbool /RboolP /zornS.
    case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 /asboolP ecbs1.
    by move/ecbs1: bvr2; exact: fs1.
have g_lin : linear_graph g.
  move=> v1 v2 l r1 r2 [a1 Aa1 c1] [a2 Aa2 c2].
  have [/RboolP sc12 | /RboolP sc21] := Amax _ _ Aa1 Aa2.
  - have {sc12 Aa1 a1} {}c1 : carrier a2 v1 r1 by exact: sc12.
    by exists a2 => //; case: a2 {Aa2} c2 c1 => c /= [_ + _ _] *; exact.
  - have {sc21 Aa2 a2} {}c2 : carrier a1 v2 r2 by exact: sc21.
    by exists a1 => //; case: a1 {Aa1} c2 c1 => c /= [_ + _ _] *; exact.
have g_majp : le_graph p g by move=> v r [[c/= [fs1 ls1 ms1 ps1]]]/= _ => /ms1.
have g_prol : extend_graph g.
   by move=> *; exists w => //; case: w Aw => [c [_ _ _ +]] _ //=; exact.
have spec_g : le_extend_graph g by split.
pose zg := ZornType spec_g.
by exists zg => [a Aa]; apply/RboolP; rewrite /zornS => v r cvr; exists a.
Qed.

Variable g : zorn_type.

(* The next lemma proves that when z is of zorn_type, it can be extended on any
real line directed by an arbitrary vector v *)
Lemma domain_extend z v : exists2 ze, zornS z ze & exists r, (carrier ze) v r.
Proof.
have [[r rP]|] := lem (exists r, carrier z v r).
  by exists z => //; exists r.
case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
have c00 : c 0 0.
  have <- : phi 0 = 0 by rewrite linear0.
  by have := ps1 0; rewrite GRing.val0.
have [a aP] : exists a, forall (x : V) (r lambda : R), c x r ->
    r + lambda * a <= p (x + lambda *: v).
  suff [a aP] : exists a, forall (x : V) (r lambda : R), c x r -> 0 < lambda ->
    r + lambda * a <= p (x + lambda *: v) /\
    r - lambda * a <= p (x - lambda *: v).
      exists a => x r lambda /[dup] cxr /aP {}aP.
      have [/aP[]// | ltl0 | ->] := ltrgt0P lambda.
        rewrite -[lambda]opprK scaleNr mulNr.
        by have /aP[] : 0 < - lambda by rewrite oppr_gt0.
      by rewrite mul0r scale0r !addr0 ms1.
   pose b (x : V) r lambda : R := (p (x + lambda *: v) - r) / lambda.
   pose a (x : V) r lambda : R := (r - p (x - lambda *: v)) / lambda.
   have le_a_b x1 x2 r1 r2 (s t : R) : c x1 r1 -> c x2 r2 -> 0 < s -> 0 < t ->
       a x1 r1 s <= b x2 r2 t.
     move=> cxr1 cxr2 lt0s lt0t; rewrite /a /b.
     rewrite ler_pdivlMr// mulrAC ler_pdivrMr// [leLHS]mulrC [leRHS]mulrC.
     rewrite !mulrDr !mulrN lerBlDr addrAC lerBrDr.
     have /ler_pM2r <- : 0 < (s + t)^-1 by rewrite invr_gt0 addr_gt0.
     set y1 : V := _ + _ *: _; set y2 : V :=  _ - _ *: _.
     rewrite (@le_trans _ _ (p (s / (s + t) *: y1 + t / (s + t) *: y2)))//.
       set u : V := (X in p X).
       have {u y1 y2} -> : u = t / (s + t) *: x1 + s / (s + t) *: x2.
         rewrite /u ![_ / _]mulrC -!scalerA -!scalerDr /y1 /y2; congr (_ *: _).
         by rewrite !scalerDr addrCA scalerN scalerA (mulrC s) -scalerA addrK.
       set l := t / _; set m := s / _.
       rewrite [leLHS](_ : _ = l * r1 + m * r2).
         by rewrite mulrDl ![_ * _ / _]mulrAC.
       apply: ms1; apply: (ls1) => //.
       by rewrite -[_ *: _]add0r -[_ * _]add0r; exact: ls1.
     rewrite !mulrDl ![_  * _ / _]mulrAC -divD_onem//.
     pose st := Itv01 (divDl_ge0 (ltW lt0s) (ltW lt0t))
                      (divDl_le1 (ltW lt0s) (ltW lt0t)).
     exact: (p_cvx st (in_setT y1) (in_setT y2)).
   pose Pa :=
     [set r | exists x1 r1 (s1 : R), [/\ c x1 r1, 0 < s1 & r = a x1 r1 s1]].
   pose Pb :=
     [set r | exists x1 r1 (s1 : R), [/\ c x1 r1, 0 < s1 & r = b x1 r1 s1]].
   pose sa := sup Pa. (* We need p with values in a *realType* *)
   have Pax : Pa !=set0 by exists (a 0 0 1), 0, 0, 1.
   have ubdP : ubound Pa sa.
     apply: sup_upper_bound; split => //=.
     by exists (b 0 0 1) =>/= x [y [r [s [cry lt0s ->]]]]; exact: le_a_b.
   have saP (u : R) : ubound Pa u -> sa <= u by exact: ge_sup.
   pose ib := inf Pb. (* We need P with values in a *realType* *)
   have Pbx : Pb !=set0 by exists (b 0 0 1), 0, 0, 1.
   have ibdP : lbound Pb ib.
     apply: ge_inf; exists (a 0 0 1) => /= x [y [r [s [cry lt0s ->]]]].
     exact: le_a_b.
   have ibP (u : R) : lbound Pb u -> u <= ib by exact: lb_le_inf Pbx.
   have le_sa_ib : sa <= ib.
     apply: saP => _ [y [r [l [cry lt0l ->]]]].
     by apply: ibP => _ [z [s [m [crz lt0m ->]]]]; exact: le_a_b.
   pose alpha := (sa + ib) / 2.
   exists alpha => x r l cxr lt0l; split.
   - suff : alpha <= b x r l by rewrite (ler_pdivlMr _ _ lt0l) lerBrDl mulrC.
     by apply: (le_trans (midf_le le_sa_ib).2); apply: ibdP; exists x, r, l.
   - suff : a x r l <= alpha.
       by rewrite (ler_pdivrMr _ _ lt0l) lerBlDl -lerBlDr mulrC.
     by apply: (le_trans _ (midf_le le_sa_ib).1); apply: ubdP; exists x, r, l.
pose z' := fun k r => exists (v' : V) (r' lambda : R),
                      [/\ c v' r', k = v' + lambda *: v & r = r' + lambda * a].
have z'_extends x r : c x r -> z' x r.
  by move=> cxr; exists x, r, 0; split; rewrite // ?scale0r ?mul0r ?addr0.
have z'_prol : extend_graph z'.
  move=> x.
  by exists (val x), (phi x), 0; split; rewrite // ?scale0r ?mul0r ?addr0.
have z'_maj_by_p : le_graph p z'
  by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
have z'_lin : linear_graph z'.
   move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
   rewrite [X in z' X _](_ : _ = w1 + l *: w2 + (m1 + l * m2) *: v).
     by rewrite !scalerDr !scalerDl scalerA -!addrA [X in _ + X]addrCA.
   rewrite [X in z' _ X](_ : _ = s1 + l * s2 + (m1 + l * m2) * a).
     by rewrite !mulrDr !mulrDl mulrA -!addrA [X in _ + X]addrCA.
   exists (w1 + l *: w2), (s1 + l * s2), (m1 + l * m2); split => //.
   exact: ls1.
have z'_functional : functional_graph z'.
  move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
  have [rw12 erw12] : exists r, c (w1 - w2) r.
    by exists (s1 + -1 * s2); rewrite -(scaleN1r w2); exact: ls1.
  have h1 (x : V) (r l : R) : x = l *: v -> c x r -> x = 0 /\ l = 0.
    move=> -> cxr; have [->|ln0] := eqVneq l 0; first by rewrite scale0r.
    suff cvs : c v (l^-1 * r) by absurd: nzv; exists (l^-1 * r).
    suff -> : v = l ^-1 *: (l *: v).
      by rewrite -(add0r (_ *: _)) -(add0r (_ * _)); exact: ls1.
    by rewrite scalerA mulVf ?scale1r.
  have [ew12] : w1 - w2 = 0 /\ m2 - m1 = 0.
    apply: h1 erw12; rewrite scalerBl.
    by apply: subr0_eq; rewrite opprB addrACA e1 -opprD subrr.
  suff -> : s1 = s2 by move/subr0_eq => ->.
  by apply: fs1 cws2; rewrite -(subr0_eq ew12).
have z'_spec : le_extend_graph z' by [].
exists (ZornType z'_spec) => //=; exists a, 0, 0, 1.
by rewrite !add0r mul1r scale1r.
Qed.

Hypothesis gP : forall z, zornS g z -> z = g.

Let total_g v : exists r, carrier g v r.
Proof.
have [z /gP sgz [r zr]] := domain_extend g v.
by exists r; rewrite -sgz.
Qed.

Lemma hahn_banach_witness :
  exists h : V -> R, forall v r, carrier g v r <-> h v = r.
Proof.
have [h hP] := choice total_g.
exists h => v r; split=> [|<-//].
move: g gP total_g hP => [c /= [fg _ _ _]] _ _ hP cvr.
by rewrite (fg v r (h v)).
Qed.

End hahnbanachzorn.
End HahnBanachZornInternal.

(* NB: could go to convex.v *)
Section hahn_banach.
Import LinearGraphInternal.
Import HahnBanachZornInternal.
(* Now we prove HahnBanach on functions *)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)
Context {R : realType} (V : lmodType R) (F : pred V).
Variables (F' : subLmodType F) (f : {linear F' -> R}) (p : V -> R).

Hypothesis p_cvx : @convex_function R V [set: V] p.

Hypothesis f_bounded_by_p : forall z : F', f z <= p (\val z).

Theorem hahn_banach_extension : exists2 g : {scalar V},
  (forall x, g x <= p x) & forall z : F', g (\val z) = f z.
Proof.
pose graphF (v : V) r := exists2 z : F', v = \val z & r = f z.
have [z /(hahn_banach_witness p_cvx)[g gP]] := zornS_ex f_bounded_by_p.
have scalg : linear_for *%R g.
  case: z gP => [c [_ ls1 _ _]] /= gP.
  have addg : zmod_morphism g.
    by move=> w1 w2; apply/gP; apply: lingraphD => //; apply/gP.
  suff scalg : scalable_for *%R g.
    by move=> a u v; rewrite -gP -(addrC v) -(addrC (g v)); apply/ls1; exact/gP.
  by move=> w l; apply/gP; apply: lingraphZ => //; exact/gP.
pose lg := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g lg.
exists g'.
  by case: z gP => [c [_ _ bp _]] /= gP => x; apply: bp; exact/gP.
by move=> z'; apply/gP; case: z {gP} => [c [_ _ _ pf]] /=; exact: pf.
Qed.

End hahn_banach.

Section hahn_banach_normed.
Variable (R : realType) (V : normedModType R) (F : pred V)
  (F' : subNormedModType F) (f : {linear_continuous F' -> R}).

Theorem hahn_banach_extension_normed :
  exists g : {linear_continuous V -> R}, forall x : F', g (val x) = f x.
Proof.
have [r ltr0 fxrx] : exists2 r, r > 0 & forall z : F', `|f z| <= `|val z| * r.
  suff: \forall r \near +oo, forall x : F', `|f x| <= r * `|x|.
    move=> [t [_ tf]].
    exists (`|t| + 1); first by rewrite ltr_wpDl.
    move=> z; rewrite mulrC Num.norm_valE tf//.
    by rewrite (le_lt_trans (ler_norm _)) ?ltrDl.
  exact/linear_boundedP/continuous_linear_bounded/continuous_fun.
pose p := fun x : V => `|x| * r.
have convp : @convex_function _ _ [set: V] p.
  rewrite /convex_function /conv => l v1 v2 _ _ /=.
  rewrite [in leRHS]/conv /= /p.
  apply: le_trans.
    have /ler_pM := ler_normD (l%:num *: v1) (l%:num.~ *: v2).
    by apply => //; exact: ltW.
  rewrite mulrDl !normrZ -![_ *: _]/(_ * _) (@ger0_norm _ l%:num)//.
  by rewrite (@ger0_norm _ l%:num.~)// ?mulrA// onem_ge0.
have : forall z : F', f z <= p (\val z).
  by move=> z; rewrite /p (le_trans (ler_norm _)).
move=> /(hahn_banach_extension convp)[g majgp F_eqgf].
have ling : linear (g : V -> R) by exact: linearP.
have contg : continuous (g : V -> R).
  move=> x; apply/continuousfor0_continuous/bounded_linear_continuous.
  exists r; split; first exact: gtr0_real.
  move=> M rM; rewrite nbhs_ballP; exists 1 => //=.
  move=> y; rewrite -ball_normE//= sub0r => y1.
  rewrite ler_norml; apply/andP; split.
  - rewrite lerNl -linearN (le_trans (majgp (- y)))//.
    by rewrite /p -(mul1r M) ltW// ltr_pM// ltW.
  - by rewrite (le_trans (majgp y))// /p -(mul1r M) -normrN ltW// ltr_pM// ltW.
pose lcg := isLinearContinuous.Build _ _ _ _ g ling contg.
pose g' : {linear_continuous V -> R | *%R} := HB.pack (g : V -> R) lcg.
by exists g'.
Qed.

End hahn_banach_normed.
