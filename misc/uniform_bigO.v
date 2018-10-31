(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype landau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Section UniformBigO.

(*
  This section shows how we can formalize the uniform bigO from:

  Boldo, Clément, Filliâtre, Mayero, Melquiond, Weis.
  Wave Equation Numerical Resolution: A Comprehensive Mechanized Proof of a C
  Program.
  Journal of Automated Reasoning 2013.

  The corresponding source code is here:

  http://fost.saclay.inria.fr/coq_total/BigO.html
*)

Context (A : Type) (P : set (R * R)).

Definition OuP (f : A -> R * R -> R) (g : R * R -> R) :=
  { alp : R & { C : R |
  0 < alp /\ 0 < C /\
  forall X : A, forall dX : R * R,
  sqrt (Rsqr (fst dX) + Rsqr (snd dX)) < alp -> P dX ->
  Rabs (f X dX) <= C * Rabs (g dX)}}.

(* first we replace sig with ex and the l^2 norm with the l^oo norm *)

Definition OuPex (f : A -> R * R -> R^o) (g : R * R -> R^o) :=
  exists2 alp, 0 < alp & exists2 C, 0 < C &
    forall X, forall dX : R^o * R^o, `|[dX]| < alp -> P dX ->
    `|[f X dX]| <= C * `|[g dX]|.

Lemma ler_norm2 (x : R^o * R^o) :
  `|[x]| <= sqrt (Rsqr (fst x) + Rsqr (snd x)) <= Num.sqrt 2 * `|[x]|.
Proof.
rewrite RsqrtE; last by rewrite addr_ge0 //; apply/RleP/Rle_0_sqr.
rewrite !Rsqr_pow2 !RpowE; apply/andP; split.
  by rewrite ler_maxl; apply/andP; split;
    rewrite -[`|[_]|]sqrtr_sqr ler_wsqrtr // (ler_addl, ler_addr) sqr_ge0.
wlog lex12 : x / (`|x.1| <= `|x.2|).
  move=> ler_norm; case: (lerP `|x.1| `|x.2|) => [/ler_norm|/ltrW lex21] //.
  by rewrite addrC [`|[_]|]maxrC (ler_norm (x.2, x.1)).
rewrite [`|[_]|]maxr_r // [`|[_]|]absRE -[X in X * _]ger0_norm // -normrM.
rewrite -sqrtr_sqr ler_wsqrtr // exprMn sqr_sqrtr // mulr_natl mulr2n ler_add2r.
rewrite -[_ ^+ 2]ger0_norm ?sqr_ge0 // -[X in _ <=X]ger0_norm ?sqr_ge0 //.
by rewrite !normrX ler_expn2r // nnegrE normr_ge0.
Qed.

Lemma OuP_to_ex f g : OuP f g -> OuPex f g.
Proof.
move=> [_ [_ [/posnumP[a] [/posnumP[C] fOg]]]].
exists (a%:num / Num.sqrt 2) => //; exists C%:num => // x dx ltdxa Pdx.
apply: fOg; move: ltdxa; rewrite ltr_pdivl_mulr //; apply: ler_lt_trans.
by rewrite mulrC; have /andP[] := ler_norm2 dx.
Qed.

Lemma Ouex_to_P f g : OuPex f g -> OuP f g.
Proof.
move=> /exists2P /getPex; set Q := fun a => _ /\ _ => - [lt0getQ].
move=> /exists2P /getPex; set R := fun C => _ /\ _ => - [lt0getR fOg].
apply: existT (get Q) _; apply: exist (get R) _; split=> //; split => //.
move=> x dx ltdxgetQ; apply: fOg; apply: ler_lt_trans ltdxgetQ.
by have /andP [] := ler_norm2 dx.
Qed.

(* then we replace the epsilon/delta definition with bigO *)

Definition OuO (f : A -> R * R -> R^o) (g : R * R -> R^o) :=
  (fun x => f x.1 x.2) =O_ (filter_prod [set setT]
  (within P [filter of 0 : R^o * R^o])) (fun x => g x.2).

Lemma OuP_to_O f g : OuP f g -> OuO f g.
Proof.
move=> /OuP_to_ex [_/posnumP[a] [_/posnumP[C] fOg]].
apply/eqOP; near=> k; near=> x; apply: ler_trans (fOg _ _ _ _) _; last 2 first.
- by near: x; exists (setT, P); [split=> //=; apply: withinT|move=> ? []].
- by rewrite ler_pmul => //; near: k; exists C%:num => ? /ltrW.
- near: x; exists (setT, ball norm (0 : R^o * R^o) a%:num); last first.
    by move=> x [_ /=]; rewrite normmB subr0.
  split=> //=; rewrite /within; near=> x =>_; near: x.
  exact: (@locally_ball _ [normedModType R of R^o * R^o]).
Grab Existential Variables. all: end_near. Qed.

Lemma OuO_to_P f g : OuO f g -> OuP f g.
Proof.
move=> fOg; apply/Ouex_to_P; move: fOg => /eqOP [k hk].
have /hk [Q [->]] : k < maxr 1 (k + 1) by rewrite ltr_maxr ltr_addl orbC ltr01.
rewrite /= -(@filter_from_norm_locally _ [normedModType R of R^o * R^o]).
move=> -[_/posnumP[e] seQ] fOg; exists e%:num => //; exists (maxr 1 (k + 1)).
  by rewrite ltr_maxr ltr01.
move=> x dx dxe Pdx; apply: (fOg (x, dx)); split=> //=.
by apply: seQ => //; rewrite /ball normmB subr0.
Qed.

End UniformBigO.