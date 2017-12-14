(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp reals.
Require Import Rstruct Rbar set posnum hierarchy landau.

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

Notation "f '~_' F g" := (f = g +o_ F g)
  (at level 70, F at level 0, g at next level, format "f  '~_' F  g").
Notation "f '~~_' F g" := (f == g +o_ F g)
  (at level 70, F at level 0, g at next level, format "f  '~~_' F  g").

Section equivalence.

Context {K : absRingType} {T : Type} {V W : normedModType K}.
Implicit Types F : filter_on T.

Lemma equivOLR F (f g : T -> V) : f ~_F g -> f =O_F g.
Proof. by move=> ->; apply: eqOE; rewrite {1}[g](idO F) addrC addfO. Qed.

Lemma equiv_refl F (f : T -> V) : f ~_F f.
Proof. by apply/eqaddoP; rewrite subrr. Qed.

Lemma equivoRL (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  f ~_F g -> [o_F g of h] =o_F f.
Proof.
move=> ->; apply/eqoP; move=> _/posnumP[eps]; begin_near x.
  rewrite -ler_pdivr_mull // -[X in g + X]opprK oppo.
  rewrite (ler_trans _ (ler_distm_dist _ _)) //.
  rewrite [X in _ <= X]ger0_norm ?ler_subr_addr ?add0r; last first.
    by rewrite -[X in _ <= X]mul1r; near x.
  rewrite [X in _ <= X]splitr [_ / 2]mulrC.
  rewrite ler_add ?ler_pdivr_mull ?mulrA //; near x.
by end_near; apply: littleoP.
Qed.

Lemma equiv_sym F (f g : T -> V) : f ~_F g -> g ~_F f.
Proof.
move=> fg; have /(canLR (addrK _))<- := fg.
by apply:eqaddoE; rewrite oppo (equivoRL _ fg).
Qed.

Lemma equivoLR (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  f ~_F g -> [o_F f of h] =o_F g.
Proof. by move/equiv_sym/equivoRL. Qed.

Lemma equivORL F (f g : T -> V) : f ~_F g -> g =O_F f.
Proof. by move/equiv_sym/equivOLR. Qed.

Lemma eqoaddo (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  [o_F f + [o_F f of g] of h] =o_F f.
Proof. by apply: equivoLR. Qed.

Lemma equiv_trans F (f g h : T -> V) : f ~_F g -> g ~_F h -> f ~_F h.
Proof. by move=> -> ->; apply: eqaddoE; rewrite eqoaddo -addrA addo. Qed.

Lemma equivalence_rel_equiv F :
  equivalence_rel [rel f g : T -> V | f ~~_F g].
Proof.
move=> f g h; split; first by apply/eqP/equiv_refl.
by move=> /eqP fg /=; apply/eqP/eqP; apply/equiv_trans => //; apply/equiv_sym.
Qed.

End equivalence.
