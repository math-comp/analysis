From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical_sets posnum topology
  normedtype landau sequences boolp reals ereal derive.

Import GRing.Theory Num.Theory Num.ExtraDef.
Import Order.POrderTheory Order.TotalTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section real_inverse_functions.

Variable R : realType.

(* All uses of this lemma have been removed, replacing them with
  uses of interval_is_interval, but it would be better if
  is_interval used large comparisons instead of strict ones. *)
Lemma itvcc_le (x y : R) (I : interval R) :
  x <= y -> (`[x, y] <= I)%O = ((x \in I) && (y \in I)).
Proof.
by move=> C; case: I => [[[] l| []] [[|] u| [|]]];
  rewrite !subitvE ?in_itv -?andbA //=; apply/idP/idP;
  repeat (move/andP=>[] ?); move=> ?; repeat (apply/andP; split=> //);
  rewrite ?(le_trans C) ?(le_trans _ C) ?(lt_le_trans _ C) ?(le_lt_trans C).
Qed.

(* This is just an example showing how to use interval_is_interval
  in the case of large comparisons. the lemma is not used otherwise.
  the pattern is re-used several time during proofs, but not this lemma
  in the hope that is_interval starts using large comparisons. *)
Lemma interval_connected_le (I : interval R) (a b c : R) :
  a \in I -> b \in I -> a <= c <= b -> c \in I.
Proof.
move=> aI bI; rewrite !le_eqVlt.
move=> /andP[] /orP[/eqP <- // | aLc] /orP [/eqP -> // | cLb].
by rewrite (interval_is_interval aI bI) ?aLc.
Qed.

Lemma near_0_in_interval (a b : R) :
  {in `]a, b[, forall y, \forall z \near 0 : R, (z + y : R) \in `]a, b[}.
Proof.
move=> y ayb.
rewrite (near_shift y 0); near=> z; rewrite /= sub0r subrK; near: z.
by rewrite near_simpl; apply: near_in_itv.
Grab Existential Variables. all: end_near. Qed.


  {in ([set y | y in (interior [set f x | x in [set x | x \in I]])])%classic,
  continuous g}.
Proof.
Admitted.

Ltac staged_split :=
  repeat (rewrite andb_idr;[ | move=> *]).

(* This is an example that appears in the following proof.  I think
  there could be a use case for tactic that leads the user to proving
  a conjunction by addressing the second component with the assumption
  that the first one already holds. *)
Fact itv_example (x e  : R):
  0 < e -> [&& x < x + e, x - e < x & x - e < x + e].
Proof.
(* create hypotheses to retain facts that will be proved later, and
  re-used in other branches. *)
move=> e0 [:xlt] [:xgt]; apply/and3P; split.
- by abstract: xlt; rewrite ltr_addl.
- by abstract: xgt; rewrite ltr_subl_addr.
exact: (lt_trans xgt).
Qed.

End real_inverse_functions.

