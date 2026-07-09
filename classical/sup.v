From HB Require Import structures.
From mathcomp Require Import all_ssreflect.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Local Open Scope order_scope.

About family.

From mathcomp Require Import classical_sets boolp.

Record universe := Universe {universe_sort :> Type; El : universe_sort -> Type}.
(* Definition universe_universe := @Universe universe universe_sort. *)

Definition family (U : universe) X := {I : U & {P : set (El I) & El I -> X}}.

Definition finfamily := @family (@Universe finType (id : finType -> Type)).
Definition seqfamily := @family (@Universe {A : eqType & seq A} (fun X => {x | x \in projT2 X})).
(* Definition seqfamily_ (I : eqType) := @family (seq I) (fun s => {x | x \in s}). *)

HB.mixin Record isSup d (T : porderType d) (pT : predType T)
    (Q : set pT) (sup : pT -> T) := {
  supP : forall (A : Q) (y : T),
    reflect (forall x : T, x \in val A -> x <= y) (sup (val A) <= y)
}.
HB.structure Definition Sup d T pT Q := {sup of @isSup d T pT Q sup}.

(* HB.mixin Record isSupFam d (I : porderType d) T Q (sup : set I -> (I -> T) -> T) := { *)
(*   supP : F (y : T), *)
(*     reflect (forall x : T, x \in val A -> x <= y) (sup (val A) <= y) *)
(* }. *)
(* HB.structure Definition Sup d T pT Q := {sup of @isSup d T pT Q sup}. *)


HB.mixin Record isLeftAdjoint d d' (C : porderType d') (D : porderType d)
    (R : D -> C) (L : C -> D) := {
  LeftP : forall A y, (L A <= y) = (A <= R y)
}.
HB.structure Definition LeftAdjoint d d' T U R :=
  {L of @isLeftAdjoint d d' T U R L}.

From mathcomp Require Import classical_sets boolp reals constructive_ereal ereal.
Local Open Scope classical_set_scope.
Section RealSup.
Variable (R : realType).

Lemma sup_isSup : @isSup _ R (set R) (@has_ubound _ R `&` nonempty) sup.
Proof.
split=> -[/= A /[!inE]/= -[Abnd AN0]] y; apply: (iffP idP).
  move=> supA_le_y x xA; rewrite (le_trans _ supA_le_y)//.
  by apply/ub_le_sup => //=; exact/set_mem.
by move=> ble; apply/ge_sup => // x /mem_set; apply/ble.
Qed.
HB.instance Definition _ := sup_isSup.

Lemma ereal_sup_isSup :
  @isSup _ (\bar R) (set (\bar R)) [set: set (\bar R)] (@ereal_sup R).
Proof.
split=> -[/= A _] y; apply: (equivP ereal_supP).
by split=> [Ay x /set_mem|Ay x /mem_set]; apply: Ay.
Qed.
HB.instance Definition _ := ereal_sup_isSup.
