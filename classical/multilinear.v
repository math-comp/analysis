From HB Require Import structures.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect ssralg vector ring_quotient.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import finmap boolp functions classical_sets.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Definition is_multilinear (I : eqType) (R : pzSemiRingType)
    (V : I -> lSemiModType R) (W : lSemiModType R)
    (f : (forall i, V i) -> W):=forall i : I, forall v :(forall i, V i),
    linear (f \o (fun x : V i => dfwith v x)).

HB.mixin Record isMultilinear (I : eqType) (R : pzSemiRingType)
    (V : I -> lSemiModType R) (W : lSemiModType R)
    (f : (forall i, V i) -> W) := {
  ilinear : forall i : I, forall v :(forall i, V i),
    linear (f \o (fun x : V i => dfwith v x))
}.

#[short(type="multilinearType")]
HB.structure Definition Multilinear (I : eqType) (R : pzSemiRingType)
  (V : I -> lSemiModType R) (W : lSemiModType R):=
  {f of @isMultilinear I R V W f}.

Lemma multilinearEP (I : eqType) (R : pzSemiRingType)
  (V : I -> lSemiModType R) (W : lSemiModType R) (f g : multilinearType V W):
  f = g <-> f =1 g.
Proof.
case: f g => [f [[ffun]]] [g [[gfun]]]/= ; split=> [[->//]|/funext eqfg].
rewrite eqfg in ffun *; congr {| Multilinear.sort := _; Multilinear.class := {|
  Multilinear.multilinear_isMultilinear_mixin :=
    {| isMultilinear.ilinear := _|}|}|}.
exact: Prop_irrelevance.
Qed.

Section TopologicalNmoduleTheory.
Variables (R : pzSemiRingType) (I : eqType) (V : I -> lSemiModType R)
  (W : lSemiModType R).

Let addfun_multilinear (f g : multilinearType V W) : is_multilinear (f \+ g).
Proof.
move=> i v.
admit.

Admitted.

HB.instance Definition _ (f g : continuousType M N) :=
  isContinuous.Build M N (f \+ g) (@addfun_continuous f g).

Let addrA : associative (fun f g : continuousType M N => f \+ g).
Proof. by move=> f g h; apply/continuousEP => x; apply: addrA. Qed.

Let addrC : @commutative _ (continuousType M N)
  (fun f g : continuousType M N => f \+ g).
Proof. by move=> f g; apply/continuousEP => x; apply: addrC. Qed.

Let add0r : @left_id (continuousType M N) _ (cst 0)
  (fun f g : continuousType M N => f \+ g).
Proof. by move=> f; apply/continuousEP => x; apply: add0r. Qed.

HB.instance Definition _ :=
  GRing.isNmodule.Build (continuousType M N) addrA addrC add0r.

End TopologicalNmoduleTheory.
