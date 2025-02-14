(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop order ssralg ssrnum.
From mathcomp Require Import boolp reals Rstruct_topology ereal.
From mathcomp Require Import classical_sets itv topology normedtype landau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section UniformBigO.

(**md**************************************************************************)
(* This section shows how we can formalize the uniform bigO from:             *)
(* Boldo, Clément, Filliâtre, Mayero, Melquiond, Weis,                        *)
(* Wave Equation Numerical Resolution: A Comprehensive Mechanized Proof of a  *)
(* C Program, Journal of Automated Reasoning 2013. The corresponding source   *)
(* code is here: http://fost.saclay.inria.fr/coq_total/BigO.html.             *)
(******************************************************************************)

Context (A : Type) (P : set (R * R)).

Definition OuP (f : A -> R * R -> R) (g : R * R -> R) :=
  { alp : R & { C : R |
  0 < alp /\ 0 < C /\
  forall X : A, forall dX : R * R,
  sqrt (Rsqr (fst dX) + Rsqr (snd dX)) < alp -> P dX ->
  Rabs (f X dX) <= C * Rabs (g dX)}}.

(* first we replace sig with ex and the l^2 norm with the l^oo norm *)

Let normedR2 : normedModType _ := (R^o * R^o)%type.

Definition OuPex (f : A -> R * R -> R^o) (g : R * R -> R^o) :=
  exists2 alp, 0 < alp & exists2 C, 0 < C &
    forall X, forall dX : normedR2,
    `|dX| < alp -> P dX -> `|f X dX| <= C * `|g dX|.

Lemma ler_norm2 (x : normedR2) :
  `|x| <= sqrt (Rsqr (fst x) + Rsqr (snd x)) <= Num.sqrt 2 * `|x|.
Proof.
rewrite RsqrtE !Rsqr_pow2 !RpowE; apply/andP; split.
  by rewrite ge_max; apply/andP; split;
    rewrite -[`|_|]sqrtr_sqr ler_wsqrtr // (lerDl, lerDr) sqr_ge0.
wlog lex12 : x / (`|x.1| <= `|x.2|).
  move=> ler_norm; case: (lerP `|x.1| `|x.2|) => [/ler_norm|] //.
  rewrite lt_leAnge => /andP [lex21 _].
  rewrite RplusE.
  by rewrite addrC [`|_|]maxC (ler_norm (x.2, x.1)).
rewrite [`|_|]max_r // -[X in X * _]ger0_norm // -normrM.
rewrite -sqrtr_sqr ler_wsqrtr // exprMn sqr_sqrtr // mulr_natl mulr2n lerD2r.
rewrite -[_ ^+ 2]ger0_norm ?sqr_ge0 // -[X in _ <=X]ger0_norm ?sqr_ge0 //.
by rewrite !normrX lerXn2r // nnegrE normr_ge0.
Qed.

Lemma OuP_to_ex f g : OuP f g -> OuPex f g.
Proof.
move=> [_ [_ [/posnumP[a] [/posnumP[C] fOg]]]].
exists (a%:num / Num.sqrt 2) => //; exists C%:num => // x dx ltdxa Pdx.
apply: fOg; move: ltdxa; rewrite ltr_pdivlMr //; apply: le_lt_trans.
by rewrite mulrC; have /andP[] := ler_norm2 dx.
Qed.

Lemma Ouex_to_P f g : OuPex f g -> OuP f g.
Proof.
move=> /exists2P /getPex; set Q := fun a => _ /\ _ => - [lt0getQ].
move=> /exists2P /getPex; set R := fun C => _ /\ _ => - [lt0getR fOg].
apply: existT (get Q) _; apply: exist (get R) _; split=> //; split => //.
move=> x dx ltdxgetQ; apply: fOg; apply: le_lt_trans ltdxgetQ.
by have /andP [] := ler_norm2 dx.
Qed.

(* then we replace the epsilon/delta definition with bigO *)

Definition OuO (f : A -> R * R -> R^o) (g : R * R -> R^o) :=
  (fun x => f x.1 x.2) =O_ (filter_prod [set setT]%classic
  (within P (nbhs (0%R:R^o, 0%R:R^o))(*[filter of 0 : R^o * R^o]*))) (fun x => g x.2).

Lemma OuP_to_O f g : OuP f g -> OuO f g.
Proof.
move=> /OuP_to_ex [_/posnumP[a] [_/posnumP[C] fOg]].
apply/eqOP; near=> k; near=> x; apply: le_trans (fOg _ _ _ _) _; last 2 first.
- by near: x; exists (setT, P); [split=> //=; apply: withinT|move=> ? []].
- by rewrite ler_pM.
- near: x; exists (setT, ball (0 : R^o * R^o) a%:num).
    by split=> //=; rewrite /within /=; near=> x =>_; near: x; apply: nbhsx_ballx.
  move=> x [_ [/=]]; rewrite -ball_normE /= distrC subr0 distrC subr0.
  by move=> ? ?; rewrite gt_max; apply/andP.
Unshelve. all: by end_near. Qed.

Lemma OuO_to_P f g : OuO f g -> OuP f g.
Proof.
move=> fOg; apply/Ouex_to_P; move: fOg => /eqOP [k [kreal hk]].
have /hk [Q [->]] : k < maxr 1 (k + 1) by rewrite lt_max ltrDl orbC ltr01.
move=> [R [[_/posnumP[e1] Re1] [_/posnumP[e2] Re2]] sRQ] fOg.
exists (minr e1%:num e2%:num); first by apply: gt0; exact: RbaseSymbolsImpl.R.
exists (maxr 1 (k + 1)); first by rewrite lt_max ltr01.
move=> x dx dxe Pdx; apply: (fOg (x, dx)); split=> //=.
move: dxe; rewrite gt_max !lt_min => /andP[/andP [dxe11 _] /andP [_ dxe22]].
by apply/sRQ => //; split; [apply/Re1|apply/Re2]; rewrite /= distrC subr0.
Qed.

End UniformBigO.
