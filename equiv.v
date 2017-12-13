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

Section equivalence.

Notation "f '~_' F g" := (f = g +o_ F f)
  (at level 70, F at level 0, g at next level, format "f  '~_' F  g").

Context {K : absRingType} {T : Type} {V W : normedModType K}.
Implicit Types  F : filter_on T.

Lemma equiv_O (f g : T -> V) F : f ~_F g -> f =O_F g.
Proof.
move=> fg.
suff /bigOE H : bigO F f g by apply: eqOE.
move/eqP: fg; rewrite addrC -subr_eq -opprB=> /eqP/eqoE; rewrite littleoNE=> fg.
exists 2%:R => //.
have {fg}fg : littleo F (g - f) f by rewrite fg.
have /fg{fg}fg : 0 < (1 / 2 : R) by [].
begin_near x.
  suff : `|[f x]| - `|[g x]| <= 1 / 2 * `|[f x]|.
    rewrite ler_subl_addr addrC -ler_subl_addr -{1}(mul1r `|[f x]|) -mulrBl.
    by rewrite {1}(splitr 1) addrK mulrC -ler_pdivl_mulr // !div1r invrK mulrC.
  rewrite (ler_trans (ler_trans _ (ler_distm_dist (g x) (f x)))) //; [|by near x].
  by rewrite absrB real_ler_norm // num_real.
end_near.
Qed.

Lemma equiv_refl F (f : T -> V) : f ~_F f.
Proof. by rewrite eqaddoP subrr. Qed.

Lemma equiv_sym F (f g : T -> V) : f ~_F g -> g ~_F f.
Proof.
move=> fg; have fOg := equiv_O fg.
apply/eqP; rewrite addrC -subr_eq; apply/eqP.
apply: (@eqoO_trans _ _ _ _ _ _ _ _ f); last by rewrite {1}fOg.
suff : g - f =o_F f by move=> ->.
by rewrite -opprB littleoNE {1}fg -addrA addrCA subrr addr0.
Qed.

Lemma equiv_trans F (f g h : T -> V) : f ~_F g -> g ~_F h -> f ~_F h.
Proof.
move/equiv_sym/eqP; rewrite addrC -subr_eq -opprB => /eqP/eqoE.
rewrite littleoNE => fg gh.
have fh : f - h =o_F g.
  move/eqP : gh; rewrite addrC -subr_eq => /eqP gh.
  by rewrite (subr_trans g) fg gh addo.
have := equiv_O gh => /(eqoO_trans fh){fh}.
move/eqP; rewrite subr_eq addrC => /eqP fh.
apply/equiv_sym/eqP; rewrite addrC -subr_eq; apply/eqP.
apply/littleoN; by rewrite fh opprB addrAC subrr add0r.
Qed.

Lemma equivalence_rel_equiv F :
  equivalence_rel [rel f g : T -> V | `[< f ~_F g >] ].
Proof.
move=> f g h; split; first by apply/asboolP/equiv_refl.
move/asboolP => fg; apply asbool_equiv_eq; split; last exact: equiv_trans.
by apply/equiv_trans/equiv_sym.
Qed.

End equivalence.

