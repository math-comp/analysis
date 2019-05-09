(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype
  landau.
  (* TODO: move structures about functions out of landau *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Reserved Notation "{ 'ae' P }" (at level 0, format "{ 'ae'  P }").

(* TODO d'ordre general:
   1. better for the lim notation *)

Local Open Scope classical_set_scope.

Definition fct_sequence (T : Type) := nat -> (T -> Rbar).

Definition increasing (T : Type) (D : set T) (f_ : fct_sequence T) :=
  forall n, (forall x, D x -> f_ n x <= f_ n.+1 x :> R).

Module Type INTEGRAL.

Parameter integrable :
  forall (T : Type) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), bool.

Parameter integral :
  forall (T : Type) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), Rbar.

Definition almost_everywhere (P : Prop) : Prop := P.
(* TODO: imiter ssrbool l.1606
Notation "{ 'in' d , P }" :=
  (prop_in1 (mem d) (inPhantom P))
  (at level 0, format "{ 'in'  d ,  P }") : type_scope.  *)

Local Notation "{ 'ae' P }" := (almost_everywhere P).

(* section about positive or infinite functions *)
Section pos_fct.
Variable T : Type.
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
  forall (f_ : fct_sequence T) (*should be measurable and positive*),
  increasing D f_ ->
  let f := fun t => lim (f_ ^~ t) in
  (* TODO: the function f must be measurable *)
  integral m D f = lim (fun n => integral m D (f_ n)).

(* TODO: Fatou's Lemma *)

End pos_fct.

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)
Section fin_fct.
Variable T : Type.
Variable m : set T -> R.
Variable D : set T.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : fct_sequence T) (f : T -> R) (g : T -> R),
  (forall n, integrable m D (f_ n)) ->
  integrable m D g ->
  (forall n, {ae forall x, `| f_ n x : R | <= g x}) ->
  {ae forall x, (fun n => f_ n x) --> f x} ->
  (fun n => integral m D (f_ n)) @ \oo --> integral m D f.

End fin_fct.

End INTEGRAL.
