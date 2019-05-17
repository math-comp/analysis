(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Reserved Notation "{ 'ae' P }" (at level 0, format "{ 'ae'  P }").

(* TODO d'ordre general:
   1. better lim notation *)

Local Open Scope classical_set_scope.

Definition fct_sequence (T : Type) := nat -> (T -> Rbar).

Definition increasing (T : Type) (D : set T) (f_ : fct_sequence T) :=
  forall n, (forall x, D x -> f_ n x <= f_ n.+1 x :> R).

Module Type INTEGRAL.

Module Measurable.

Parameter class_of : forall (T : Type), Type.
Notation sigma_algebra := class_of.

Parameter sets : forall T, class_of T -> set (set T).

Structure type := Pack {
  sort : Type ; class : class_of sort }.

Module Exports.
Notation measurableType := type.
Coercion sort : type >-> Sortclass.
Definition measurable (T : type) := sets (class T).
Notation sigma_algebra := class_of.
End Exports.

(* TODO: property that all measurable sets are indeed measurable *)

End Measurable.

Export Measurable.Exports.

Parameter measurable_fun : forall (T : measurableType) (f : T -> Rbar), bool.

Parameter integral :
  forall (T : measurableType) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), Rbar.

(* NB: integrable to be defined as measurable and of finite integral
of absolute value *)
Parameter integrable :
  forall (T : measurableType) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), bool.

Definition almost_everywhere (T : measurableType) (m : set T -> Rbar)
  (P : T -> Prop) & (phantom Prop (forall x, P x)) :=
  exists A : set T, measurable A /\ m A = Finite 0 /\ forall x, A x \/ P x.
(* TODO: issue remove the Coercion real : Rbar >-> R in Rbar.v*)
Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom P))
  (at level 0, format "{ 'ae'  m ,  P }") : type_scope.

(* section about positive or infinite functions *)
Section pos_fct.
Variable T : measurableType.
Variable m : set T -> Rbar.
Variable D : set T.

(* TODO: we have to restrict linearity to:
   1. positive and measurable
   2. integrable functions
   (Need two "integral" symbols for Canonical declarations?) *)
Axiom integral_is_linear :
  linear_for *%R (integral m D : (T -> R^o) -> R).
Canonical integral_linear := Linear integral_is_linear.

(* TODO: order structure about functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
in order to be able to use the notation {homo ...}
in order to rewrite the lemma integral_ler *)

Axiom integral_ler : forall (f g : T -> R),
  (forall x, f x <= g x) -> integral m D f <= integral m D g :> R.
(* TODO: need two variants
   1. take into account that diverge(f) -> diverge(g)
   2. when we talk only about measurable functions
*)

(* monotone convergence theorem:
   voir necessite de la condition de positivite (wikipedia.fr),
   pas de variante pour les fonctions non-necessairement positive
   (no variant 2., see convergence dominee) *)
Axiom cvg_monotone :
  forall (f_ : fct_sequence T) (*should be positive*),
  (forall n, measurable_fun (f_ n)) ->
  increasing D f_ ->
  let f := fun t => lim (f_ ^~ t) in
  measurable_fun f /\
  integral m D f = lim (fun n => integral m D (f_ n)).

(* TODO: Fatou's Lemma *)

End pos_fct.

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)
Section fin_fct.
Variable T : measurableType.
Variable m : set T -> R.
Variable D : set T.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : fct_sequence T) (f : T -> R) (g : T -> R),
  (forall n, integrable m D (f_ n)) ->
  integrable m D g ->
  (forall n, {ae m, forall x, `| f_ n x : R | <= g x}) ->
  {ae m, forall x, (fun n => f_ n x) --> f x} ->
  (fun n => integral m D (f_ n)) @ \oo --> integral m D f.

End fin_fct.

(* TODO *)
Axiom product_measure : forall (X Y : measurableType)
  (mx : set X -> R) (my : set Y -> R), set (X * Y) -> R.
Axiom product_measurableType_sigma_algebra : forall (X Y : measurableType), sigma_algebra (X * Y).
Canonical product_measurableType X Y := Measurable.Pack (product_measurableType_sigma_algebra X Y).
Axiom sigma_algebra_completion : forall (T : Type) (X : sigma_algebra T) (mx : set T -> R),
 sigma_algebra T.
Definition measurable_completion (X : measurableType) (m : set X -> Rbar) :=
  @Measurable.Pack X (sigma_algebra_completion (Measurable.class X) m).

Section fubini.

Variables X Y : measurableType.
Variables (mx : set X -> R) (my : set Y -> R).
Let mz : set (X * Y) -> R := product_measure mx my.
Variable f : @measurable_completion (product_measurableType X Y) mz -> Rbar.

(* see faraut p.61 *)
Axiom fubini_tonelli : measurable_fun f ->
  (forall x, 0 <= f x :> R) ->
  let F := fun x => integral my setT (fun y => f (x, y)) in
  measurable_fun F /\
  integral mz setT f = integral mx setT F.

End fubini.

End INTEGRAL.
