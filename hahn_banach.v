From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp  Require Import all_ssreflect all_algebra.


(* Proposition de Marie : encoder la partialité dans le graphe, et
raisonner sur le graphe. Autre facon de partir : faire une relation
sur les sur-ensembles de F sur lesquels il y a un prolongement lineaire,
mais là il faut traiter des constructions explicites de prolongements 
avec passages par supplémentaires pour dire si on est dans F alors, 
si on est x alors, et sinon. *) 

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Quelques définitions et quelques conséquences des axiomes classiques, 
fournies par boolp. On se donne ici les axiomes utilisés "tels quels", sans
souci de minimalité. *)

Axiom Prop_irrelevance : forall (P : Prop) (x y : P), x = y.
Axiom funext : forall (T U : Type) (f g : T -> U), (f =1 g) -> f = g.
Axiom propext : forall (P Q : Prop), (P <-> Q) -> (P = Q).
Axiom EM : forall (P : Prop), P \/ ~ P.

Definition set (A : Type) := A -> Prop.
Definition total_on T (A : set T) (R : T -> T -> Prop) :=
  forall s t, A s -> A t -> R s t \/ R t s.

Axiom Zorn : forall T (R : T -> T -> Prop),
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, forall s, R t s -> s = t.


Local Open Scope ring_scope.
Import GRing.Theory.
Import Num.Theory.



Section Draft.


Variables (R : realFieldType) (V : lmodType R).

Definition ubd (s : set R) (a : R) := forall x, s x -> x <= a.

Definition ibd (s : set R) (a : R) := forall x, s x -> a <= x.


Hypothesis sup : forall (A : set R) (a m : R),
    A a -> ubd A m ->
    {s : R | ubd A s /\ forall u, ubd A u -> s <= u}. 

Hypothesis inf : forall (A : set R) (a m : R),
    A a ->  ibd A m ->
    {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

Variables (F G : set V) (phi : {scalar V}) (p : V -> R).

Hypothesis F0 : F 0.
Hypothesis p_cvx : forall v1 v2 l m,
    l + m = 1 -> p (l *: v1 + m *: v2) <= l * (p v1) + m * (p v2).
  
Implicit Types (f g : V -> R -> Prop).

(* Extends is just relation inclusion *)

Definition extends f g := forall v r, f v r -> g v r.

Lemma extends_refl f : extends f f. Proof. by []. Qed.

Lemma extends_trans f2 f1 f3 : extends f1 f2 -> extends f2 f3 -> extends f1 f3. 
Proof. by move=> h1 h2 v r /h1 /h2. Qed.

Lemma extends_antisym f g : extends f g -> extends g f -> f = g.
Proof.
move=> efg egf; apply: funext => v; apply: funext=> r; apply: propext; split.
- exact: efg.
- exact: egf.
Qed.

(* Functional (possibly empty or partial) graphs *)
Definition functional f :=
  forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

(* Graph of a function *)
Definition graph_of (h : V -> R) v r := r = h v.

(* the intension is that f is the graph of a function, bounded by p *)
Definition maj_by_p f := forall v r, f v r -> r <= p v.

(* the intension is that f is the graph of a function, which
   coincides with f on F *)
Definition prol_phi f := forall v, F v -> f v (phi v).

Definition linear_rel f :=
  forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Definition spec (f : V -> R -> Prop) :=
  [/\ functional f, linear_rel f, maj_by_p f & prol_phi f].

Record zorn_type : Type := ZornType
  {carrier : V -> R -> Prop; specP : spec carrier}.

Definition phi_graph v r := phi v = r.

Hypothesis spec_phi : spec phi_graph.

Definition zphi := ZornType spec_phi.

Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
Proof.
case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; move: pm1 pm2; rewrite e => pm1 pm2.
by congr ZornType; apply: Prop_irrelevance.
Qed.

Definition zorn_rel (z1 z2 : zorn_type) := extends (carrier z1) (carrier z2).

Lemma zorn_rel_refl z : zorn_rel z z.
Proof. rewrite /zorn_rel. exact: extends_refl. Qed.  

Lemma zorn_rel_trans z1 z2 z3 :
  zorn_rel z1 z2 -> zorn_rel z2 z3 -> zorn_rel z1 z3.
Proof. rewrite /zorn_rel; exact: extends_trans. Qed.

Lemma zorn_rel_antisym z1 z2 : zorn_rel z1 z2 -> zorn_rel z2 z1 -> z1 = z2.
Proof.
rewrite /zorn_rel /= => s12 s21; apply: zorn_type_eq; exact: extends_antisym.
Qed.

(* Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q. *)
(* Proof. move=> qp np q; apply: np; exact: qp. Qed. *)

(* Lemma propF (P : Prop) : ~ P -> P = False. *)
(* Proof. by move=> ?; rewrite propeqE; tauto. Qed. *)

Lemma zorn_rel_maj (A : set zorn_type) : total_on A zorn_rel ->
   exists t, forall s, A s -> zorn_rel s t.
Proof.
move=> htot.
case: (EM (exists a, A a)) => [[w Aw] | eA]; last first.  
  by exists zphi => a Aa; elim: eA; exists a.
pose g v r := exists a, A a /\ (carrier a v r).
have g_fun : functional g.
  move=> v r1 r2 [a [Aa avr1]] [b [Ab bvr2]].
  have [] : zorn_rel a b \/ zorn_rel b a by exact: htot.  
  - rewrite /zorn_rel; case: b Ab bvr2 {Aa} => s2 [fs2 _ _ _] /= _ s2vr2 ecas2.
    by move/ecas2: avr1 => /fs2 /(_ s2vr2).
  - rewrite /zorn_rel; case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 ecbs1.
    by move/ecbs1: bvr2; apply: fs1.
have g_lin : linear_rel g. 
  move=> v1 v2 l r1 r2 [a1 [Aa1 c1]] [a2 [Aa2 c2]].
  have [sc12 | sc21] := htot _ _ Aa1 Aa2.
  - have {c1 sc12 Aa1 a1} c1 :  carrier a2 v1 r1 by apply: sc12.
    exists a2; split=> //; case: a2 {Aa2} c2 c1 => c /= [_ hl _ _] *; exact: hl.
  - have {c2 sc21 Aa2 a2} c2 :  carrier a1 v2 r2 by apply: sc21.
    exists a1; split=> //; case: a1 {Aa1} c2 c1 => c /= [_ hl _ _] *; exact: hl.
have g_majp : maj_by_p g by move=> v r [[c [fs1 ls1 ms1 ps1]]] /= [_ /ms1].  
have g_prol_phi : prol_phi g.
  move=> v r; exists w; split=> //; case: w {Aw} => [c [fs1 ls1 ms1 ps1]] /=.
  exact: ps1.
have spec_g : spec g by split.
pose zg := ZornType spec_g.
by exists zg => [a Aa]; rewrite /zorn_rel /= => v r cvr; exists a.  
Qed.

Lemma zorn_rel_ex : exists g : zorn_type, forall z, zorn_rel g z -> z = g.
Proof.
apply: Zorn.
- exact: zorn_rel_refl.
- exact: zorn_rel_trans.
- exact: zorn_rel_antisym.
- exact: zorn_rel_maj.
Qed.

Variable g : zorn_type.

Hypothesis gP : forall z, zorn_rel g z -> z = g.

Definition add_line f w a := fun v r =>
  exists v' : V, exists r' : R, exists lambda : R,
        [/\ f v' r', v = v' + lambda *: w & r = r' + lambda * a].

Lemma domain_extend  (z : zorn_type) v :
    exists2 ze : zorn_type, (zorn_rel z ze) & (exists r, (carrier ze)  v r).
Proof.
case: (EM (exists r, (carrier z v r))).
  by case=> r rP; exists z => //; exists r.
case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
have c00 : c 0 0.
  have -> : 0 = phi 0 by rewrite linear0. 
  exact: ps1.
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
    rewrite ler_pdivl_mulr // mulrAC ler_pdivr_mulr // mulrC [_ * s]mulrC.
    rewrite !mulrDr !mulrN ler_subl_addr addrAC ler_subr_addr. 
    have /ler_pmul2r <- : 0 < (s + t) ^-1 by rewrite invr_gt0 addr_gt0.
    set y1 : V := _ + _ *: _; set y2 : V :=  _ - _ *: _.
    set rhs := (X in _ <= X).
    have step1 : p (s  / (s + t) *: y1 + t  / (s + t) *: y2) <= rhs.
      rewrite /rhs !mulrDl ![_  * _ / _]mulrAC; apply: p_cvx.
      by rewrite -mulrDl mulfV //; apply: lt0r_neq0; rewrite addr_gt0.
    apply: ler_trans step1 => {rhs}.
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
        by rewrite /b; move/ler_pdivl_mulr: lt0l->; rewrite ler_subr_addl mulrC. 
      by apply: ler_trans le_alpha_ib _; apply: ibdP; exists x; exists r; exists l.
    - suff : a x r l <= alpha.          
        rewrite /a. move/ler_pdivr_mulr: lt0l->.
        by rewrite ler_subl_addl -ler_subl_addr mulrC. 
      by apply: ler_trans le_sa_alpha; apply: ubdP; exists x; exists r; exists l.
pose z' := add_line c v a.
have z'_extends :  extends c z'.
  move=> x r cxr; exists x; exists r; exists 0; split=> //.
  - by rewrite scale0r addr0.
  - by rewrite mul0r addr0.
have z'_prol_phi : prol_phi z'.
  move=> x /ps1 cxphix; exists x; exists (phi x); exists 0; split=> //.
  - by rewrite scale0r addr0.
  - by rewrite mul0r addr0.
- have z'_maj_by_p : maj_by_p z'.
  by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
- have z'_lin : linear_rel z'.
  move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
  set w := (X in z' X _); set s := (X in z' _ X).
  have {w} -> : w = w1 + l *: w2 + (m1 + l * m2) *: v by admit.
  have {s} -> : s = s1 + l * s2 + (m1 + l * m2) * a by admit.
  exists (w1 + l *: w2); exists (s1 + l * s2); exists (m1 + l * m2); split=> //.
  exact: ls1.  
- have z'_functional : functional z'.
  move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
  have h1 (x : V) (r l : R) : x = l *: v ->  c x r -> x = 0 /\ l = 0.
    move->. admit.
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
rewrite add0r mul1r scale1r add0r; split => //.
Admitted.


Lemma tot_g v : exists r, carrier g v r.
Proof.
have [z /gP sgz [r zr]]:= domain_extend g v.
by exists r; rewrite -sgz.
Qed.


Axiom choice : forall A B (P : A -> B -> Prop),
    (forall a : A, exists b : B,  P a b) -> (exists e, forall a,  P a (e a)).

Lemma hb_witness : exists h : V -> R, forall v r, carrier g v r <-> (h v = r).
Proof.
have [h hP] : exists h,  forall v, carrier g v (h v) by exact: choice tot_g.
exists h => v r.
split; last by move<-.
case: g gP tot_g hP => c /= [fg lg mg pg] => gP' tot_g' hP cvr.
by have -> // := fg v r (h v).
Qed.


End Draft.












