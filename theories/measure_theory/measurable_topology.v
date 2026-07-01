From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat algebra finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import measurable_structure topology_structure metric_structure.

(**md**************************************************************************)
(* # Measure theory applied to topological spaces via the Borel sigma-algebra.*)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ```Soon : default display open.-sigma for topological types                *)
(* ```                                                                        *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section measurable_topology.
Context {T : topologicalType}.

Lemma salgebra_countable_basis {B : set_system T} (D : set T) : 
countable B -> basis B -> <<s D, B>> = <<s D, open>>.
Proof.
rewrite eqEsubset => /countable_bijP [A /card_esym/pcard_eqP/bijPex/= 
  [g [fg _ ag]]] /basisP [BO bB]; split. exact: sigma_algebra_sub.
apply: sigma_algebra_subl=> U /bB ->.
have sgU : set_surj (A `&` [set n | g n `<=` U]) (B `&` [set W | W `<=` U]) g.
by rewrite surjE in ag; rewrite surjE=> W [/ag [n An <-]/= gnU]; exists n.
rewrite (reindex_bigcup _ _ _ _ _ sgU). move=> n /= [a u]; split=>//. exact: fg.
rewrite bigcup_mkcond; apply: sigma_algebra_bigcup=> i. case: ifP=>//[|_].
  rewrite in_setE=> [[Ai _]]. apply: sub_sigma_algebra. exact: fg.
exact: sigma_algebra0.
Qed.

Lemma salgebra_open_closedE : 
<<s (@open T)>> = <<s closed>>.
Proof.
rewrite eqEsubset; split; apply: sigma_algebra_subl.
  move=> U oU; rewrite -(setCK U); apply: (sigma_algebraC (sub_sigma_algebra _)); 
  exact: open_closedC.
move=> F cF; rewrite -(setCK F); apply: (sigma_algebraC (sub_sigma_algebra _));
exact: closed_openC.
Qed.

End measurable_topology.