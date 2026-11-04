(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import topology normedtype landau.

(**md**************************************************************************)
(* # Negligible sequences                                                     *)
(*                                                                            *)
(* A sequence is negligible when its absolute value is eventually below every *)
(* inverse power of the index. Negligible sequences form a submodule of the   *)
(* sequences.                                                                 *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - J. Katz, Y. Lindell. Introduction to Modern Cryptography, 2nd edition.   *)
(*   CRC Press, 2015. Definition 3.4.                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*   negligible_seq == predicate of the sequences u : R ^nat such that for    *)
(*                     every c, `|u n| < n%:R ^- c for n large enough         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section negligible_seq_pred.
Context {R : archiRealFieldType}.

Definition negligible_seq : {pred R ^nat} :=
  mem [set u | forall c : nat, \forall n \near \oo, `|u n| < n%:R ^- c].
Definition negligible_seq_key : pred_key negligible_seq.
Proof. exact. Qed.
Canonical negligible_seq_keyed := KeyedPred negligible_seq_key.

End negligible_seq_pred.

Section negligible_seq.
Context {R : archiRealFieldType}.
Implicit Types u v : R ^nat.

Lemma negligible_seq_cvgP u : u \in negligible_seq <->
  forall c : nat, (fun n => n%:R ^+ c * u n) @ \oo --> 0.
Proof.
split=> [/set_mem un c|un].
  apply/cvgr0Pnorm_lt => e e_gt0; near=> n.
  have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
  rewrite normrM normrX normr_nat.
  have : `|u n| < n%:R ^- c.+1 by near: n; exact: un.
  rewrite -(ltr_pM2l (_ : 0 < n%:R ^+ c)) ?exprn_gt0 ?ltr0n // exprSr invfM.
  rewrite mulVKf ?expf_neq0 ?pnatr_eq0 -?lt0n // => /lt_trans; apply.
  rewrite -[e]invrK ltf_pV2 ?posrE ?ltr0n ?invr_gt0 //.
  by near: n; exact: nbhs_infty_gtr.
apply/mem_set => c; near=> n.
have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
have : `|n%:R ^+ c * u n| < 1.
  by near: n; apply: (cvgr0Pnorm_lt _).1 ltr01; exact: un.
by rewrite normrM normrX normr_nat -ltr_pdivlMl ?exprn_gt0 ?ltr0n ?mulr1.
Unshelve. all: by end_near. Qed.

Lemma negligible_seq_submod_closed : submod_closed (@negligible_seq R).
Proof.
split=> [|a u v /negligible_seq_cvgP un /negligible_seq_cvgP vn].
  apply/negligible_seq_cvgP => c.
  by under eq_fun do rewrite /= mulr0; exact: cvg_cst.
apply/negligible_seq_cvgP => c; under eq_fun do rewrite /= mulrDr mulrCA.
rewrite -(addr0 0) -{1}(mulr0 a); apply: cvgD (vn c).
by apply: cvgM; [exact: cvg_cst|exact: un].
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build _ _ negligible_seq negligible_seq_submod_closed.

Lemma le_negligible_seq u v :
  (\forall n \near \oo, `|u n| <= `|v n|) ->
  v \in negligible_seq -> u \in negligible_seq.
Proof.
move=> uv /set_mem vn; apply/mem_set => c.
by apply: filterS2 uv (vn c) => n; exact: le_lt_trans.
Qed.

Lemma negligible_seq_eqoP u :
  u \in negligible_seq <-> forall c : nat, u =o_\oo (fun n => n%:R ^- c : R).
Proof.
split=> [/negligible_seq_cvgP un c|uo].
  apply/eqoP => e e_gt0; near=> n.
  have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
  have : `|n%:R ^+ c * u n| < e.
    by near: n; apply: (cvgr0Pnorm_lt _).1 e_gt0; exact: un.
  rewrite normrM normrX normr_nat normfV normrX normr_nat.
  by rewrite ler_pdivlMr ?exprn_gt0 ?ltr0n // mulrC => /ltW.
apply/mem_set => c; near=> n.
have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
have : `|u n| <= 2^-1 * `|n%:R ^- c : R|.
  by near: n; apply: (eqoP _ _ _).1 (uo c) _ _; rewrite invr_gt0 ltr0n.
rewrite normfV normrX normr_nat => /le_lt_trans; apply.
by rewrite gtr_pMl ?invf_lt1 ?ltr1n // invr_gt0 exprn_gt0 ?ltr0n.
Unshelve. all: by end_near. Qed.

Lemma negligible_seqXnM u d :
  u \in negligible_seq -> (fun n => n%:R ^+ d * u n) \in negligible_seq.
Proof.
move=> /negligible_seq_cvgP un; apply/negligible_seq_cvgP => c.
by under eq_fun do rewrite mulrA -exprD; exact: un.
Qed.

Let exp2_gt_linear (c k : nat) : (c * c + c <= k)%N -> (c * k.+1 < 2 ^ k)%N.
Proof.
move=> k_ge; have [d kE] : exists d, k = (c + d)%N.
  by exists (k - c)%N; rewrite subnKC // (leq_trans _ k_ge) // leq_addl.
have cc_le : (c * c <= d)%N by move: k_ge; rewrite kE addnC leq_add2l.
rewrite kE; apply: leq_trans (_ : c.+1 * d.+1 <= _)%N; last first.
  by rewrite expnD leq_mul // ltn_expl.
by rewrite mulnS mulnDr mulSn mulnS addnA addnA ltn_add2r addnC ltn_add2r ltnS.
Qed.

Let exp2_gt_monomial (c n : nat) :
  (2 ^ (c * c + c) <= n)%N -> (n ^ c < 2 ^ n)%N.
Proof.
move=> n_ge; have n_gt0 : (0 < n)%N by rewrite (leq_trans _ n_ge) // expn_gt0.
move: n_ge; case: c => [_|c n_ge].
  by rewrite expn0 -{1}(expn0 2) ltn_exp2l.
set k := trunc_log 2 n.
have k_ge : (c.+1 * c.+1 + c.+1 <= k)%N by apply: trunc_log_max.
apply: leq_ltn_trans (_ : 2 ^ (c.+1 * k.+1) < _)%N.
  by rewrite mulnC expnM leq_exp2r // ltnW // trunc_log_ltn.
rewrite ltn_exp2l //.
by apply: leq_trans (exp2_gt_linear k_ge) (trunc_logP _ _).
Qed.

Lemma negligible_seqV v :
  (forall c : nat, \forall n \near \oo, n%:R ^+ c <= v n) ->
  (fun n => (v n)^-1) \in negligible_seq.
Proof.
move=> v_ge; apply/mem_set => c; near=> n.
have n_gt1 : (1 < n)%N by near: n; exact: nbhs_infty_gt.
have Xn_gt0 k : 0 < n%:R ^+ k :> R by rewrite exprn_gt0 // ltr0n ltnW.
have vn : n%:R ^+ c.+1 <= v n by near: n; exact: v_ge.
have vn_gt0 := lt_le_trans (Xn_gt0 _) vn.
rewrite normfV gtr0_norm // (@le_lt_trans _ _ (n%:R ^- c.+1)) //.
  by rewrite lef_pV2 ?posrE.
by rewrite ltf_pV2 ?posrE ?ltr_eXn2l ?ltr1n.
Unshelve. all: by end_near. Qed.

Lemma negligible_seq_exprnN (p : nat) : (1 < p)%N ->
  (fun n => p%:R ^- n : R) \in negligible_seq.
Proof.
move=> p_gt1; apply: negligible_seqV => c; near=> n.
rewrite -natrX -natrX ler_nat.
rewrite (leq_trans (ltnW (exp2_gt_monomial _))) ?leq_exp2r //.
  by near: n; exact: nbhs_infty_ge.
by near: n; exact: nbhs_infty_gt.
Unshelve. all: by end_near. Qed.

End negligible_seq.
