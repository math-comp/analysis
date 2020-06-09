(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences measure.

(******************************************************************************)
(*           Scratch file for formalization of integrals (WIP)                *)
(*                                                                            *)
(* Written by the participants to the mathcomp-analysis-dev meeting circa May *)
(* 2019.                                                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Reserved Notation "{ 'ae' P }" (at level 0, format "{ 'ae'  P }").

(* TODO d'ordre general:
   1. better lim notation *)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition fct_sequence (R : numDomainType) (T : Type) := (T -> {ereal R}) ^nat.

Definition increasing (R : numDomainType) (T : Type) (D : set T) (f_ : fct_sequence R T) :=
  forall n, (forall x, D x -> real_of_er (f_ n x) <= real_of_er (f_ n.+1 x)).


Module Type INTEGRAL.

Parameter measurable_fun : forall (R : numDomainType) (T : measurableType) (f : T -> {ereal R}), bool.

Parameter integral :
  forall (R : numDomainType) (T : measurableType) (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}), {ereal R}.

(* NB: integrable to be defined as measurable and of finite integral
of absolute value *)
Parameter integrable :
  forall (R : numDomainType) (T : measurableType) (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}), bool.

Definition almost_everywhere (R : numDomainType) (T : measurableType) (m : set T -> {ereal R})
  (P : T -> Prop) & (phantom Prop (forall x, P x)) :=
  exists A : set T, measurable A /\ m A = 0%:E /\ forall x, A x \/ P x.
(* TODO: issue remove the Coercion real : Rbar >-> R in Rbar.v*)
Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom P))
  (at level 0, format "{ 'ae'  m ,  P }") : type_scope.

(* section about positive or infinite functions *)
Section pos_fct.
Variable R : numFieldType.
Variable T : measurableType.
Variable m : set T -> {ereal R}.
Variable D : set T.

(* TODO: we have to restrict linearity to:
   1. positive and measurable
   2. integrable functions
   (Need two "integral" symbols for Canonical declarations?) *)
Axiom integral_is_linear :
  linear_for *%R ((fun f => real_of_er (integral m D (fun x => (f x)%:E))) : (T -> R^o) -> R).
Canonical integral_linear := Linear integral_is_linear.

(* TODO: order structure about functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
in order to be able to use the notation {homo ...}
in order to rewrite the lemma integral_ler *)

Axiom integral_ler : forall (f g : T -> R),
  (forall x, f x <= g x) -> real_of_er (integral m D (fun x => (f x)%:E)) <= real_of_er (integral m D (fun x => (g x)%:E)).
(* TODO: need two variants
   1. take into account that diverge(f) -> diverge(g)
   2. when we talk only about measurable functions
*)

(* monotone convergence theorem:
   voir necessite de la condition de positivite (wikipedia.fr),
   pas de variante pour les fonctions non-necessairement positive
   (no variant 2., see convergence dominee) *)
Axiom cvg_monotone :
  forall (f_ : fct_sequence R T) (*should be positive*),
  (forall n, measurable_fun (f_ n)) ->
  increasing D f_ ->
  let f := fun t => lim ((fun n => real_of_er (f_ n t)) : nat -> R^o) in
  measurable_fun (fun x => (f x)%:E) /\
  real_of_er (integral m D (fun x => (f x)%:E)) = lim ((fun n => real_of_er (integral m D (f_ n))) : nat -> R^o).

(* TODO: Fatou's Lemma *)

End pos_fct.

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)
Section fin_fct.
Variable R : numFieldType.
Variable T : measurableType.
Variable m : set T -> R.
Variable D : set T.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : fct_sequence R T) (f : T -> R) (g : T -> R),
  (forall n, integrable (fun x => (m x)%:E) D (f_ n)) ->
  integrable (fun x => (m x)%:E) D (fun x => (g x)%:E) ->
  (forall n, {ae (fun x => (m x)%:E), forall x, `| real_of_er (f_ n x) | <= g x}) ->
  {ae (fun x => (m x)%:E), forall x, ((fun n => (real_of_er (f_ n x) : R)) : nat -> R^o) --> (f x : R^o)} ->
  (fun n => real_of_er (integral (fun x => (m x)%:E) D (f_ n))) @ \oo --> (real_of_er (integral (fun x => (m x)%:E) D (fun x => (f x)%:E)) : R^o).

End fin_fct.

(* TODO *)
Axiom product_measure : forall (R : numFieldType) (X Y : measurableType)
  (mx : set X -> R) (my : set Y -> R), set (X * Y) -> R.
Axiom product_measurableType_sigma_algebra : forall (X Y : measurableType), is_sigma_algebra (X * Y).
Canonical product_measurableType X Y := Measurable.Pack (product_measurableType_sigma_algebra X Y).
Axiom sigma_algebra_completion : forall (R : numFieldType) (T : Type) (X : is_sigma_algebra T) (mx : set T -> R),
 is_sigma_algebra T.
Definition measurable_completion (R : numFieldType) (X : measurableType) (m : set X -> {ereal R}) :=
  @Measurable.Pack X (sigma_algebra_completion (Measurable.class X) (fun x => real_of_er (m x))).

Section fubini.

Variables (R : numFieldType) (X Y : measurableType).
Variables (mx : set X -> R) (my : set Y -> R).
Let mz : set (X * Y) -> R := product_measure mx my.
Variable f : @measurable_completion R (product_measurableType X Y) (fun x => (mz x)%:E) -> {ereal R}.

(* see faraut p.61 *)
Axiom fubini_tonelli : measurable_fun f ->
  (forall x, 0 <= real_of_er (f x)) ->
  let F := fun x => integral (fun x => (my x)%:E) setT (fun y => f (x, y)) in
  measurable_fun F /\
  integral (fun x => (mz x)%:E) setT f = integral (fun x => (mx x)%:E) setT F.

End fubini.

End INTEGRAL.
