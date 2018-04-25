(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import xfinmap boolp set reals.
(* ------- *) Require (*--*) Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope real_scope.

Section PredSubtype.
Section Def.
Variable T : Type.
Variable E : pred T.

Record pred_sub : Type :=
  PSubSub { rsval : T; rsvalP : rsval \in E }.

Coercion rsval : pred_sub >-> T.

Canonical pred_sub_subType := Eval hnf in [subType for rsval].
End Def.

Definition pred_sub_eqMixin (T : eqType) (E : pred T) :=
  Eval hnf in [eqMixin of pred_sub E by <:].
Canonical pred_sub_eqType (T : eqType) (E : pred T) :=
  Eval hnf in EqType (@pred_sub T E) (pred_sub_eqMixin E).

Definition pred_sub_choiceMixin (T : choiceType) (E : pred T) :=
  Eval hnf in [choiceMixin of pred_sub E by <:].
Canonical pred_sub_choiceType (T : choiceType) (E : pred T) :=
  Eval hnf in ChoiceType (@pred_sub T E) (pred_sub_choiceMixin E).

Definition pred_sub_countMixin (T : countType) (E : pred T) :=
  Eval hnf in [countMixin of pred_sub E by <:].
Canonical pred_sub_countType (T : countType) (E : pred T) :=
  Eval hnf in CountType (@pred_sub T E) (pred_sub_countMixin E).
End PredSubtype.

Notation "[ 'psub' E ]" := (@pred_sub _ E)
  (format "[ 'psub'  E ]").

(* -------------------------------------------------------------------- *)
Section PIncl.
Variables (T : Type) (E F : pred T) (le : {subset E <= F}).

Definition pincl (x : [psub E]) : [psub F] :=
  PSubSub (le (valP x)).
End PIncl.

(* -------------------------------------------------------------------- *)
Definition countable {T : Type} (E : pred T) := (Countable.mixin_of [psub E]).

Section Countable.
Context {T : Type} {E : pred T}.

Definition countable_sort (c : countable E) := [psub E].

Variable (c : countable E).

Canonical countable_eqType := EqType (countable_sort c) (Countable.EqMixin c).
Canonical countable_choiceType := ChoiceType (countable_sort c) (CountChoiceMixin c).
Canonical countable_countType := CountType (countable_sort c) c.

End Countable.

Coercion countable_sort : countable >-> Sortclass.

Lemma countType_countable (T : countType) (E : pred T) : countable E.
Proof. by exists pickle unpickle; apply/pickleK. Qed.

Local Open Scope classical_set_scope.

Lemma classic_countable (T : choiceType) (E : pred T) :
  (exists p, forall x : T, x \in E -> exists n : nat, p n = some x) -> countable E.
Proof.
move=> /(xgetPex ((fun=> None) : _ -> _)); set f := xget _ _ => fP.
pose pickle (e : [psub E]) := projT1 (sig_eqW (fP (val e) (valP e))).
exists pickle (obind insub \o f); rewrite /pickle => -[x xP] /=.
by case: sig_eqW => //= n -> /=; rewrite insubT.
Qed.

CoInductive finite {T : Type} (E : pred T) :=
  Finite (n : nat) (fpickle : [psub E] -> 'I_n)
(* Cyril: maybe put an enumeration instead, for conversion purposes *)
         (unfpickle : nat -> option [psub E])
         of pcancel fpickle unfpickle.

Section Finite.
Context {T : Type} {E : pred T}.

Definition finite_sort (f : finite E) := [psub E].

Variable (f : finite E).

Lemma finite_countable : countable E.
Proof. by case: f => n p up pK; exists p up. Qed.

Canonical finite_eqType :=
  EqType (finite_sort f) (Countable.EqMixin finite_countable).
Canonical finite_choiceType :=
  ChoiceType (finite_sort f) (CountChoiceMixin finite_countable).
Canonical finite_countType := CountType (finite_sort f) finite_countable.

Local Coercion list_of_option T : option T -> seq T :=
  fun x => if x is Some t then [:: t] else [::].

Lemma finite_finMixin : {s : seq (finite_sort f) & Finite.axiom s}.
Proof.
case: f => n p up pK.
exists (undup (flatten [seq (up (val i) : seq (finite_sort f)) | i in 'I_n])).
move=> x; rewrite count_uniq_mem ?undup_uniq // mem_undup; apply/eqP.
by rewrite eqb1; apply/flatten_imageP; exists (p x); rewrite // pK mem_head.
Qed.

Canonical finite_finType := FinType (finite_sort f)
  (Finite.Mixin (finite_countable : Countable.mixin_of (finite_sort f))
                (projT2 finite_finMixin)).

End Finite.

(* -------------------------------------------------------------------- *)
Section CountSub.
Variables (T : eqType) (E F : pred T).

Lemma countable_sub: {subset E <= F} -> countable F -> countable E.
Proof.
move=> le_EF [f g fgK]; pose f' (x : [psub E]) := f (pincl le_EF x).
pose g' x := obind (insub (sT := [subType of [psub E]])) (omap val (g x)).
by exists f' g' => x; rewrite /f' /g' fgK /= valK.
Qed.
End CountSub.

(* -------------------------------------------------------------------- *)
Section CountableUnion.
Variables (T : eqType) (E : nat -> pred T).

Hypothesis cE : forall i, countable (E i).

Lemma cunion_countable : countable [pred x | `[exists i, x \in E i]].
Proof.
pose S := { i : nat & cE i }; set F := [pred x | _].
have H: forall (x : [psub F]), exists i : nat, val x \in E i.
  by case=> x /= /existsbP[i] Eix; exists i.
have G: forall (x : S), val (tagged x) \in F.
  by case=> i [x /= Eix]; apply/existsbP; exists i.
pose f (x : [psub F]) : S := Tagged (fun i => [psub E i])
  (PSubSub (xchooseP (H x))).
pose g (x : S) := PSubSub (G x).
by have /CanCountMixin: cancel f g by case=> x hx; apply/val_inj.
Qed.

End CountableUnion.

CoInductive infinite (T : Type) (E : pred T) :=
  Infinite enum of forall n : nat, enum n \in E & injective enum.

(* -------------------------------------------------------------------- *)
Section FiniteTheory.

Lemma choice_finite {T : eqType} (E : pred T) :
  (exists s : seq T, {subset E <= s}) -> finite E.
Proof.
Admitted.

Lemma finiteVinfinite {T : Type} (E : pred T) : finite E + infinite E.
Admitted.

Lemma not_finite {T : Type} (E : pred T) : (finite E -> False) -> infinite E.
Proof. by have [] := finiteVinfinite E. Qed.

Lemma not_infinite {T : Type} (E : pred T) : (infinite E -> False) -> finite E.
Proof. by have [] := finiteVinfinite E. Qed.

End FiniteTheory.

Lemma big_infinite (T : Type) (E : pred T) :
  (forall n, exists f : 'I_n -> [psub E], injective f) -> infinite E.
Admitted.

Lemma infinite_itv (R : numFieldType) (a b : R) : a < b ->
  infinite [pred x | a < x < b].
Proof.
move=> lt_ab; apply: big_infinite => n.
pose f i := ((b - a) * (i%:R / n.+1%:R) + a).
have f_mono : {mono f : i j / (i <= j)%N >-> i <= j}.
  apply: homo_leq_mono => i j lt_ij; rewrite /f ltr_add2r.
  by rewrite ltr_pmul2l ?ltr_pmul2r ?subr_gt0 ?ltr_nat ?invr_gt0 ?ltr0Sn.
have fP (i : 'I_n) : f i.+1 \in [pred x | a < x < b].
have -> : a = f 0%N by rewrite /f mul0r mulr0 add0r.
have -> : b = f n.+1 by rewrite /f divff ?pnatr_eq0 // mulr1 addrNK.
  by rewrite inE !(leq_lerW_mono f_mono) // !ltnS leq0n ltn_ord.
exists (fun i => PSubSub (fP i)) => i j /= [].
by move=> /(leq_mono_inj f_mono) [] /val_inj.
Qed.

Lemma infiniteIfinite (T : Type) (E F : pred T) :
  infinite E -> finite F -> finite (predI E F).
Admitted.

Notation cofinite E := (finite (predC E)).

Lemma infiniteIcofinite (T : Type) (E F : pred T) :
  infinite E -> cofinite F -> infinite (predI E F).
Admitted.

Lemma finite_seq (T : eqType) (s : seq T) : finite (mem s).
Admitted.
