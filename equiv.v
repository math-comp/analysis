(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Rcomplements Rbar Markov Iter Lub.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp reals.
Require Import Rstruct set R_ext hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Delimit Scope R_scope with coqR.
Delimit Scope real_scope with real.
Local Close Scope R_scope.
Local Open Scope ring_scope.
Local Open Scope real_scope.
Local Open Scope classical_set_scope.



(* Tentative to handle small o and big O notations *)
Section Domination.

Context {K : absRingType} {T : Type} {V W : normedModType K}.

Definition littleo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps, eps > 0 -> \near x in F, `|[f x]| <= eps * `|[g x]|.

Structure littleo_type (F : set (set T)) (g : T -> W) := Littleo {
  littleo_fun :> T -> V;
  _ : `[< littleo F littleo_fun g >]
}.
Notation "''o_' F" := (littleo_type F)
  (at level 0, F at level 0, format "''o_' F").

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Structure filterType T := FilterType {
  filter_term :> set (set T);
  _ : Filter filter_term
}.
Identity Coercion test : set >-> Funclass.

Canonical locally_filterType (U : uniformType) (x : U) :=
  FilterType (@filter_filter' _ _ (locally_filter x)).

Global Instance Filter_filterType T (F : filterType T) : Filter F.
Proof. by case: F T. Qed.

Lemma littleo0 F g : Filter F -> littleo F \0 g.
Proof.
move=> FF eps /= eps_gt0 ; apply: filter_forall => x; rewrite normm0.
by rewrite mulr_ge0 // ltrW.
Qed.

Canonical little0 (F : filterType T) g := Littleo (asboolT (@littleo0 F g _)).

Lemma littleoP (F : set (set T)) (g : T -> W) (f : 'o_F g) :
  forall eps, eps > 0 -> \near x in F, `|[f x]| <= eps * `|[g x]|.
Proof. by case: f => ? /= /asboolP. Qed.

Definition the_littleo (F : filterType T) h (d : 'o_F h) f := insubd d f.
Arguments the_littleo : simpl never.

Notation "f = g '+o_' F h" :=
  (f%function = g%function \+ @the_littleo F h (@little0 F h) (f \- g))
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" := (f = \0 +o_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Lemma add_littleo_subproof (F : filterType T) e (df dg :'o_F e) :
  littleo F (df \+ dg) e.
Proof. Admitted.

Canonical add_littleo (F : filterType T) e (df dg :'o_F e) :=
  Littleo (asboolT (add_littleo_subproof df dg)).

Lemma funaddo (F : filterType T) e (df dg :'o_F e) (f g: T -> V) :
  @the_littleo F e df f \+ @the_littleo F e dg g =
  @the_littleo F e (@little0 F e)
                   (add_littleo (@the_littleo F e df f) (@the_littleo F e dg g)).
Proof.
by rewrite {3}/the_littleo /insubd insubT //; apply/asboolP; apply: littleoP.
Qed.

Lemma addo (F : filterType T) e (df dg :'o_F e) (f g: T -> V) x :
  @the_littleo F e df f x + @the_littleo F e dg g x =
  @the_littleo F e (@little0 F e)
                   ((add_littleo (@the_littleo F e df f) (@the_littleo F e dg g))) x.
Proof. by move: x; rewrite -/(_ \+ _ =1 _) {1}funaddo. Qed.

(* This notation is printing only in order to display 'o
   without looking at the contents *)
Notation "''o' '_' F h" := (@the_littleo F h _ _)
  (at level 0, F at level 0, h at level 200, format "''o' '_' F  h").

Lemma eqaddoP (F : filterType T) (e : T -> W) (f g : T -> V) dh h :
  f = g \+ @the_littleo F e dh h -> littleo F (f \- g) e.
Proof.
rewrite /the_littleo /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_] eps eps_gt0 /=.
  near x; first by rewrite /= addrAC subrr add0r; assume_near x.
  by end_near; apply: fg_o_e.
near x => /=; first by rewrite addrC addKr; assume_near x.
by end_near; apply: littleoP.
Qed.

Lemma eqoP (F : filterType T) (e : T -> W) (f g : T -> V) :
   (f = g +o_ F e) <-> (littleo F (f \- g) e).
Proof.
split=> [/eqaddoP//|/asboolP fg_o_e].
by rewrite /the_littleo /insubd insubT funeqE => x /=; rewrite addrC addrNK.
Qed.

Lemma eqoE (F : filterType T) (e : T -> W) (f g : T -> V) dh h :
  f = g \+ @the_littleo F e dh h -> f = g +o_ F e.
Proof. by move=> /eqaddoP /eqoP. Qed.

Lemma eqo_trans (F : filterType T) (f g h : T -> V) (e : T -> W):
  f = g +o_ F e -> g = h +o_F e -> f = h +o_F e.
Proof.
by move=> -> ->; apply: eqoE; rewrite funeqE=> x; rewrite /= -addrA addo.
Qed.

(* add a spec to replace a 'o_F e by a "canonical one" *)
(* mostly to prevent problems with depend types *)

Definition bigo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists k, \near x in F, `|[f x]| < k * `|[g x]|.

End Domination.

Notation "''o_' F" := (@littleo_type _ _ _ _ F)
  (at level 0, F at level 0, format "''o_' F").

Notation "f = g '+o_' F h" :=
  (f%function = g%function \+ @the_littleo F h (@little0 F h) (f \- g))
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" := (f = \0 +o_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Notation "''o' '_' F h" := (@the_littleo F h _ _)
  (at level 0, F at level 0, h at level 200, format "''o' '_' F  h").
