From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat algebra finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality all_reals.
From mathcomp Require Import measurable_structure topology measurable_function.
From mathcomp Require Import normedtype interval_inference.

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
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "N .-open" (at level 1, format "N .-open").
Reserved Notation "N .-open.-measurable"
 (at level 2, format "N .-open.-measurable").

Section normed_lemmas.
Context {R : realType} {N : normedModType R}.

Lemma set1_bigcap_ball (x : N) : [set x] = \bigcap_n ball x n.+1%:R^-1.
Proof.
rewrite eqEsubset/bigcap; split=> [y -> n _ | y /= bn]/=. 
  by apply: ballxx; rewrite invr_gt0.
apply: close_eq _=>//; rewrite ball_close=> e0; rewrite ball_symE. 
apply: (le_ball _ (bn (truncn e0%:num^-1) I)). rewrite invf_ple ?posrE//.
exact: (ltW (truncnS_gt _)).
Qed.

End normed_lemmas.

Section open.
Context {R : realType} {N : normedModType R}.

Definition open_type : Type := N.

HB.instance Definition _ := Pointed.on open_type.

Let measurable : set_system N := @measurable _ (g_sigma_algebraType (@open N)).

Let measurable0 : measurable set0. Proof. exact: measurable0. Qed.

Let measurableC A : measurable A -> measurable (~` A).
Proof. by move=> /measurableC. Qed.

Let measurable_bigcup (F : (set N)^nat) : (forall i, measurable (F i)) ->
  measurable (\bigcup_i (F i)).
Proof. move=> mF; exact: bigcupT_measurable. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build (sigma_display (@open N))
    open_type measurable measurable0 measurableC measurable_bigcup.

End open.

Notation "N .-open" := (sigma_display (@open N)) : measure_display_scope.
Notation "N .-open.-measurable" := (measurable : set_system (@open_type _ N)) :
  classical_set_scope.

Module MeasurableOpen.
Section measurableOpen.
Context {R : realType} {N : normedModType R}.

Definition measurableTypeO := g_sigma_algebraType (@open N).

Definition borel_display : measure_display := N.-open.

Definition measurableO : set_system N := N.-open.-measurable.

HB.instance Definition _ : Measurable borel_display measurableTypeO :=
   Measurable.on measurableTypeO.
(* Presumably it is safe to use NFI here because morally R is unique
   and nothing else can be used here *)
#[non_forgetful_inheritance]
HB.instance Definition _ := Measurable.copy N measurableTypeO.

Lemma measurable_set1 (x : N) : measurable [set x].
Proof.
rewrite set1_bigcap_ball; apply: bigcap_measurable => // k _.
apply: sub_sigma_algebra; exact: ball_open.
Qed.
#[local] Hint Resolve measurable_set1 : core.

Lemma measurable_ball_norm (x : N) e : measurable (ball x e).
Proof. by apply: (sub_sigma_algebra (ball_open _ _)). Qed.

End measurableOpen.
Arguments measurableTypeO : clear implicits.
#[global]
Hint Extern 0 (measurable (_ @^-1` [set _])) =>
  solve [apply: measurable_funPTI; exact: measurable_set1] : core.
#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable_set1] : core.
(* #[global] causes some bugs bc it used to not be auto
Hint Extern 0 (measurable (ball _ _) ) => exact: measurable_ball_norm : core. *)

Lemma measurable_funP1 {d} {aT : measurableType d} {rT : realType} 
  {nT : normedModType rT} (f : {mfun aT >-> nT}) D (z : nT) :
  measurable D -> measurable (D `&` f @^-1` [set z]).
Proof. by move=> /(measurable_funP f); exact. Qed.
#[deprecated(since="mathcomp-analysis 1.13.0", use=measurable_funP1)]
Notation measurable_sfun_inP := measurable_funP1 (only parsing).
#[global] Hint Extern 0 (measurable (_ `&` _ @^-1` [set _])) =>
  solve [apply: measurable_funP1; assumption] : core.

Section measurableReal.
Context {R : realType}.
Import numFieldNormedType.Exports.

Definition measurableTypeR := @measurableTypeO R R.

Definition lebesgue_display : measure_display := @borel_display R R.

Definition measurableR := @measurableO R R.
(* Shouldn't be needing ideally... *)
HB.instance Definition _ := Measurable.copy R measurableTypeR.

End measurableReal.
Arguments measurableTypeR : clear implicits.

End MeasurableOpen.

Module MeasurableR.
Export numFieldNormedType.Exports.
Export MeasurableOpen.
End MeasurableR.