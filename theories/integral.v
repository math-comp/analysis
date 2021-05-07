(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets posnum topology normedtype sequences measure.

(******************************************************************************)
(*                      Formalization of integrals (WIP)                      *)
(*                                                                            *)
(* This file is a scratch file for formalization of integrals, whose first    *)
(* version has been written by the participants to the mathcomp-analysis-dev  *)
(* meeting circa May 2019.                                                    *)
(*                                                                            *)
(* It contains a Module Type that specifies an interface for a theory         *)
(* of integration which is work-in-progress.                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Notation "0" := 0%:E : ereal_scope.
Notation "1" := 1%:E : ereal_scope.

Definition complete_measure (R : realType) (T : measurableType)
   (mu : set T -> \bar R) :=
  forall X, mu.-negligible X -> measurable X.

Definition measurable_fun (T U : measurableType) (D : set T) (f : T -> U) : Prop :=
  forall Y, measurable Y -> measurable ((f @^-1` Y) `&` D).

Module Type INTEGRAL.

Section tmp.

Variable R : realType.

Parameter measurableR : set (set R).
Parameter measurableR0 : measurableR set0.
Parameter measurableRC : forall A, measurableR A -> measurableR (~` A).
Parameter measurableR_bigcup : forall U : (set R)^nat, (forall i, measurableR (U i)) ->
    measurableR (\bigcup_i (U i)).

Definition R_isMeasurable : isMeasurable R :=
  isMeasurable.Build _ measurableR0 measurableRC measurableR_bigcup.
HB.instance (Real.sort R) R_isMeasurable.

Parameter measurableErealR : set (set \bar R).
Parameter measurableErealR0 : measurableErealR set0.
Parameter measurableErealRC : forall A, measurableErealR A -> measurableErealR (~` A).
Parameter measurableErealR_bigcup : forall U : (set \bar R)^nat, (forall i, measurableErealR (U i)) ->
    measurableErealR (\bigcup_i (U i)).

Definition erealR_isMeasurable : isMeasurable \bar R :=
  isMeasurable.Build _ measurableErealR0 measurableErealRC measurableErealR_bigcup.
HB.instance (\bar (Real.sort R)) erealR_isMeasurable.

Axiom measurableEreal_gee : forall x, measurable [set y : \bar R | x <= y]%E.
Axiom measurableEreal_lee : forall x, measurable [set y : \bar R | y <= x]%E.
Axiom measurableEreal_setT : measurable (setT : set \bar R).

Section integral.

Variable T : measurableType.

Lemma measurable_funN (D : set T) (f : T -> \bar R) :
  measurable_fun D (fun x => - f x)%E = measurable_fun D f.
Proof.
Admitted.

Lemma measurable_fun_measurable (D : set T) (f : T -> \bar R) :
  measurable_fun D f -> measurable D.
Proof. by move=> /(_ _ measurableEreal_setT); rewrite setTI. Qed.

Parameter integral : forall (m : set T -> \bar R) (D : set T)
  (f : T -> \bar R), \bar R.

Definition Rintegral (m : set T -> \bar R) (D : set T)
  (f : T -> \bar R) : R := real_of_extended (integral m D f).

Definition integrable (m : set T -> \bar R) (D : set T) (f : T -> \bar R) :=
  measurable_fun D f /\ (integral m D (fun x => `| f x |) < +oo)%E.

Lemma integrable_measurable
    (m : set T -> \bar R) (D : set T) (f : T -> \bar R) :
  integrable m D f -> measurable D.
Proof. by move=> [/measurable_fun_measurable]. Qed.

Axiom integral1 : forall (m : set T -> \bar R) (D : set T),
  integral m D (fun=> 1%:E) = m D.

Axiom integral_is_linear : forall (m : set T -> \bar R) (D : set T)
  (k : \bar R) (f g : T -> \bar R),
  (0 <= k)%E ->
  {ae m, forall t, D t -> 0 <= f t}%E ->
  {ae m, forall t, D t -> 0 <= g t}%E ->
  measurable_fun D f -> measurable_fun D g ->
  integral m D (fun x => f x + k * g x)%E = (integral m D f + k * integral m D g)%E.

Axiom integral_ler : forall (m : set T -> \bar R) (D : set T)
   (f g : T -> \bar R),
  {ae m, forall t, D t -> 0 <= f t}%E -> {ae m, forall t, D t -> 0 <= g t}%E ->
  measurable_fun D f -> measurable_fun D g ->
  {ae m, forall x, D x -> f x <= g x}%E -> (integral m D f <= integral m D g)%E.

Lemma integral_disjoint_dom : forall (m : set T -> \bar R) (D1 D2 : set T)
    (f : T -> \bar R),
   measurable D1 -> measurable D2 -> m.-negligible (D1 `&` D2) ->
 integral m (D1 `|` D2) f = (integral m D1 f + integral m D2 f)%E.
Proof.
Admitted.

Variables (m : {measure set T -> \bar R}) (D : set T).

(* TODO: order structure about functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
in order to be able to use the notation {homo ...}
in order to rewrite the lemma integral_ler *)

(* monotone convergence theorem:
   voir necessite de la condition de positivite (wikipedia.fr),
   pas de variante pour les fonctions non-necessairement positives
   (no variant 2., see convergence dominee) *)
Axiom cvg_monotone : forall (f_ : (T -> \bar R)^nat),
  (forall n, {ae m, forall t, D t -> 0 <= f_ n t}%E) ->
  (forall n, measurable_fun D (f_ n)) ->
  (forall x, D x -> {homo f_^~ x : m n / (m <= n)%N >-> (m <= n)%E}) ->
  let f x := lim (f_^~ x) in
  measurable_fun D f /\ integral m D f = lim (integral m D \o f_).

(* TODO: Fatou's Lemma *)

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)

Axiom Rintegral_is_linear : forall (f g : T -> \bar R) (k : R),
  integrable m D f -> integrable m D g ->
  Rintegral m D (fun x => f x + k%:E * g x)%E = Rintegral m D f + k * Rintegral m D g.
(*TODO: Canonical integral_linear := Linear integral_is_linear.*)

Axiom Rintegral_ler : forall (f g : T -> \bar R),
  integrable m D f -> integrable m D g ->
  measurable D ->
  {ae m, forall t, D t -> f t <= g t}%E -> Rintegral m D f <= Rintegral m D g.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : (T -> \bar R)^nat) (f g : T -> \bar R),
  (forall n, integrable m D (f_ n)) ->
  integrable m D g ->
  (forall n, {ae m, forall t, `| f_ n t | <= g t}%E) ->
  {ae m, forall t, f_ n t @[n --> \oo]--> f t} ->
  (Rintegral m D \o f_) @ \oo --> (Rintegral m D f : R^o).

End integral.

Axiom mprodType_is_measurable : forall (X Y : measurableType)
  (mx : set X -> \bar R) (my : set Y -> \bar R), isMeasurable (X * Y)%type.

Definition mprodType (X Y : measurableType)
  (mx : set X -> \bar R) (my : set Y -> \bar R) := (X * Y)%type.

Axiom product_measure : forall (X Y : measurableType)
  (mx : set X -> \bar R) (my : set Y -> \bar R), set (mprodType mx my) -> \bar R.
Arguments product_measure {X Y} _ _.

Section prod_measurable.
Variables X Y : measurableType.
Variables (mx : set X -> \bar R) (my : set Y -> \bar R).

HB.instance (mprodType mx my) (mprodType_is_measurable mx my).

End prod_measurable.
(*Canonical product_measurableType X Y := Measurable.Pack (product_measurableType_sigma_algebra X Y).*)

Section fubini.

Variables (X Y : measurableType).
Variables (mx : set X -> \bar R) (my : set Y -> \bar R).
Notation m := (product_measure mx my).
Variable f : mprodType mx my -> \bar R.
Variable DX : set X.
Variable DY : set Y.
Let D : set (mprodType mx my) := DX `*` DY.

Axiom product_measure_is_measure : is_measure m.
Canonical product_measure_measure := Measure product_measure_is_measure.

(* see faraut p.61 *)
Axiom fubini_tonelli : sigma_finite DX mx -> sigma_finite DY my ->
  {ae m, (forall x, D x -> 0 <= f x)%E} ->
  measurable_fun D f ->
  let F : X -> \bar R := fun x => integral my DY (fun y => f (x, y)) in
  measurable_fun DX F /\
  integral m D f = integral mx DX F.

Axiom fubini_lebesgue : complete_measure mx -> complete_measure my ->
  integrable m D f ->
  let F : X -> \bar R := fun x => integral my DY (fun y => f (x, y)) in
  integrable mx DX F /\ Rintegral m D f = Rintegral mx DX F.

End fubini.

End tmp.

End INTEGRAL.
