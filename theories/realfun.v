(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
Require Import boolp ereal reals.
Require Import classical_sets posnum nngnum topology prodnormedzmodule.
Require Import normedtype.

(******************************************************************************)
(* This file provides properties of standard real-valued functions over real  *)
(* numbers.                                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Import numFieldNormedType.Exports.

Section real_inverse_function_instances.

Variable R : realType.

Lemma exp_continuous n : continuous (@GRing.exp R ^~ n).
Proof.
move=> x; elim: n=> [ | n Ih]; first by apply: cst_continuous.
have cid : {for x, continuous id} by [].
have cexp : {for x, continuous (@GRing.exp R ^~ n)} by rewrite forE; apply: Ih.
have := continuousM cid cexp; rewrite forE /=.
rewrite exprS (_ : @GRing.exp R ^~ n.+1 = (@idfun R) * (@GRing.exp R ^~ n))//.
by apply: funext => y; rewrite exprS.
Qed.

Lemma sqr_continuous : continuous (@exprz R ^~ 2).
Proof. exact: (@exp_continuous 2%N). Qed.

Lemma sqrt_continuous : continuous (@Num.sqrt R).
Proof.
move=> x; case: (ltrgtP x 0) => [xlt0 | xgt0 | ->].
- apply: (near_cst_continuous 0); rewrite (near_shift 0 x).
  near=> z; rewrite subr0 /=; apply: ltr0_sqrtr.
  rewrite -(opprK x) subr_lt0; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; rewrite ltr_oppr oppr0.
- suff main b : 0 <= b -> {in `]0 ^+ 2, (b ^+ 2)[, continuous (@Num.sqrt R)}.
    apply: (@main (x + 1)); rewrite ?ler_paddl// ?in_itv/= ?ltW// expr0n xgt0/=.
    by rewrite sqrrD1 ltr_paddr// ltr_paddl ?sqr_ge0// (ltr_pmuln2l _ 1%N 2%N).
  move=> b0; apply: (@segment_can_le_continuous _ _ _ (@GRing.exp _^~ _)) => //.
    by apply: in1W; apply: exp_continuous.
  by move=> y y0b; rewrite sqrtr_sqr ger0_norm// (itvP y0b).
- apply/cvg_distP => _ /posnumP[e]; rewrite !near_simpl /=; near=> y.
  rewrite sqrtr0 sub0r normrN ger0_norm ?sqrtr_ge0 //.
  have [ylt0|yge0] := ltrP y 0; first by rewrite ltr0_sqrtr//.
  have: `|y| < e%:num ^+ 2 by near: y; apply: nbhs0_lt.
  by rewrite -ltr_sqrt// ger0_norm// sqrtr_sqr ger0_norm.
Grab Existential Variables. all: end_near. Qed.

End real_inverse_function_instances.
