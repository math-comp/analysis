(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import topology normedtype measure.

(**md**************************************************************************)
(* # Sigma-algebra for normed modules                                         *)
(*                                                                            *)
(* `borel_type N`                                                             *)
(* : alias for `N : normedModType R`                                          *)
(*                                                                            *)
(* `borel_display N`                                                          *)
(* : display for `borel_type N`                                               *)
(*                                                                            *)
(* `N .-open.-measurable`                                                     *)
(* : the set of measurable sets                                               *)
(*                                                                            *)
(* `MeasurableNormedModule`                                                   *)
(* : module that contains the definition of a sigma-algebra for normed        *)
(* : modules                                                                  *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "R .-open" (at level 1, format "R .-open").
Reserved Notation "R .-open.-measurable"
 (at level 2, format "R .-open.-measurable").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section open.
Context {R : numFieldType} {N : normedModType R}.

Definition borel_type : Type := N.

Definition borel_display : measure_display := sigma_display (@open N).

(*HB.instance Definition _ := Pointed.on borel_type.*)

HB.instance Definition _ :=
  Measurable.copy borel_type (g_sigma_algebraType (@open N)).

End open.
Arguments borel_type {R} N.
Arguments borel_display {R} N.

Notation "N .-open" := (borel_display N) : measure_display_scope.
Notation "N .-open.-measurable" := (measurable : set_system (@borel_type _ N)) :
  classical_set_scope.

Module MeasurableNormedModuleOpen.
Section measurableOpen.
Context {R : archiRealFieldType} {N : normedModType R}.

Let measurableTypeNormedModule := g_sigma_algebraType (@open N).

HB.instance Definition _ : Measurable (borel_display N) measurableTypeNormedModule :=
   Measurable.on measurableTypeNormedModule.

(* Presumably it is safe to use NFI here because the sigma-algebra of opens
   for N is unique and nothing else can be used here *)
#[non_forgetful_inheritance]
HB.instance Definition _ := Measurable.copy N measurableTypeNormedModule.

Lemma measurable_set1 (x : N) : measurable [set x].
Proof.
rewrite set1_bigcap_ball; apply: bigcap_measurable => // k _.
by apply: sub_sigma_algebra; exact: ball_open.
Qed.
#[local] Hint Resolve measurable_set1 : core.

Lemma measurable_ball_norm (x : N) e : measurable (ball x e).
Proof. exact: (sub_sigma_algebra (ball_open _ _)). Qed.

End measurableOpen.

Lemma measurable_funP1 {d} {aT : measurableType d} {rT : archiRealFieldType}
  {nT : normedModType rT} (f : {mfun aT >-> nT}) D (z : nT) :
  measurable D -> measurable (D `&` f @^-1` [set z]).
Proof.
by move=> /(measurable_funP f); apply => //; exact: measurable_set1.
Qed.

(* NB: really used, e.g., in simple_functions.v *)
#[global] Hint Extern 0 (measurable (_ @^-1` [set _])) =>
  solve [apply: measurable_funPTI; exact: measurable_set1] : core.

(* NB: really used, e.g., in radon_nikodym.v *)
#[global] Hint Extern 0 (measurable (_ `&` _ @^-1` [set _])) =>
  solve [apply: measurable_funP1; assumption] : core.

(* NB: really used, e.g., in realfun.v *)
#[global] Hint Extern 0 (measurable [set _]) =>
  solve [apply: measurable_set1] : core.

End MeasurableNormedModuleOpen.

Module MeasurableNormedModule.
Export numFieldNormedType.Exports.
Export MeasurableNormedModuleOpen.
End MeasurableNormedModule.
