(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp reals.
Require Import Rstruct Rbar classical_sets posnum topology hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(** For Pierre-Yves : definition of sums *)

From mathcomp Require fintype bigop finmap.

Section totally.

Import fintype bigop finmap.
Local Open Scope fset_scope.
(* :TODO: when eventually is generalized to any lattice *)
(* totally can just be replaced by eventually *)
Definition totally {I : choiceType} : set (set {fset I}) :=
  filter_from setT (fun A => [set B | A `<=` B]).

Canonical totally_filter_source {I : choiceType} X :=
  @Filtered.Source X _ {fset I} (fun f => f @ totally).

Instance totally_filter {I : choiceType} : ProperFilter (@totally I).
Proof.
eapply filter_from_proper; last by move=> A _; exists A; rewrite fsubset_refl.
apply: filter_fromT_filter; first by exists fset0.
by move=> A B /=; exists (A `|` B) => P /=; rewrite fsubUset => /andP[].
Qed.

Definition partial_sum {I : choiceType} {R : zmodType}
  (x : I -> R) (A : {fset I}) : R := \sum_(i : A) x (val i).

Definition sum (I : choiceType) {K : absRingType} {R : normedModType K}
   (x : I -> R) : R := lim (partial_sum x).

Definition summable (I : choiceType) {K : absRingType} {R : normedModType K}
   (x : I -> R) :=
   \forall M \near +oo, forall J,
   partial_sum (fun i => `|[x i]|) J <= M.

Lemma eq_partial_sum {I : choiceType} {R : zmodType} J (x y : I -> R) :
  x =1 y -> partial_sum x J = partial_sum y J.
Proof. by move=> eq_xy; apply/eq_bigr. Qed.

Lemma ler_partial_sum {I : choiceType} {R : numDomainType} J (x y : I -> R) :
  (forall i, x i <= y i) -> partial_sum x J <= partial_sum y J.
Proof. by move=> le_xy; apply/ler_sum. Qed.

Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition opp_fun_head t (f : U -> V) x := let: tt := t in - f x.
End LiftedZmod.

Notation "\- f" := (opp_fun_head tt f) (at level 40) : ring_scope.

Section Summable.
Context {I : choiceType} {K : absRingType} {E : normedModType K}.

Implicit Types x y : I -> E.

Lemma summableN x : summable x -> summable (\- x).
Proof.
apply: filterS => /= v h J; apply: (ler_trans _ (h J)).
by apply: ler_partial_sum => i; rewrite normmN.
Qed.

Lemma summableD x y : summable x -> summable y -> summable (x \+ y).
Proof.
move=> [vx vxP] [vy vyP]; near=> v => J; rewrite (@ler_trans _ (vx + vy)%R)//=.
rewrite (ler_trans _ (ler_add (vxP _ _ J) (vyP _ _ J)))//.
by rewrite -big_split ler_sum => //= ? _; apply: ler_normm_add.
Grab Existential Variables. all: end_near. Qed.

End Summable.

End totally.
