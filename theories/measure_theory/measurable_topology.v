(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat algebra finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality reals topology.
From mathcomp Require Import measurable_structure normedtype.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.

Definition borelType (T : topologicalType) := g_sigma_algebraType (@open T).

Section borel_normedModType.
Local Open Scope ring_scope.
Context {R : realType} {V : normedModType R}.

Lemma singleton_bigcap (x : V) :
  [set x] = \bigcap_(k : nat) ball x (k.+1%:R)^-1.
Proof.
apply/seteqP; split => [_ -> k _|y xy].
  by rewrite -ball_normE/= subrr normr0 invr_gt0 ltr0n.
apply/eqP; rewrite eq_sym -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pl => e e0; rewrite addr0.
have := xy (truncn e^-1) I; rewrite -ball_normE/= => /ltW/le_trans; apply.
by rewrite invf_ple ?posrE ?ltr0n ?invr_gt0//; apply/ltW/truncnS_gt.
Qed.

Lemma measurable1 (x : borelType V) : measurable [set x].
Proof.
rewrite singleton_bigcap; apply: bigcap_measurable => // k _.
by apply: sub_sigma_algebra; exact: ball_open.
Qed.
#[local] Hint Resolve measurable1 : core.

End borel_normedModType.

#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable1] : core.

#[non_forgetful_inheritance]
HB.instance Definition _ (R : realType) (V : normedModType R) :=
  Measurable.copy V (borelType V).


