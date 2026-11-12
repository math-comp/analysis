(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import topology normedtype measure.

(**md**************************************************************************)
(* # Sigma-algebra for normed modules                                         *)
(*                                                                            *)
(* `open_type N`                                                              *)
(* : alias for `N : normedModType R`                                          *)
(*                                                                            *)
(* `N .-open.-measurable`                                                     *)
(* : the set of measurable sets                                               *)
(*                                                                            *)
(* `MeasurableNormedModule`                                                   *)
(* : module that contains the definition of the sigma-algebra for normed      *)
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

(* TODO: borel_type? *)
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

Module MeasurableNormedModuleOpen.
Section measurableOpen.
Context {R : archiRealFieldType} {N : normedModType R}.
Import numFieldNormedType.Exports.

Let measurableTypeNormedModule := g_sigma_algebraType (@open N).

Definition borel_display : measure_display := N.-open.

Let measurableNormedModule : set_system N := N.-open.-measurable.

HB.instance Definition _ : Measurable borel_display measurableTypeNormedModule :=
   Measurable.on measurableTypeNormedModule.
(* Presumably it is safe to use NFI here because morally R is unique
   and nothing else can be used here *)
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
