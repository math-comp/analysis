(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun finset finmap bigop ssralg ssrnum ssrint.
Require Import tuple bigenough boolp reals.
Require (*--*) Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

Local Open Scope ring_scope.
Local Open Scope real_scope.

(* -------------------------------------------------------------------- *)
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
Section Countable.
Variable (T : Type) (E : pred T).

CoInductive countable : Type :=
  Countable
    (rpickle : [psub E] -> nat)
    (runpickle : nat -> option [psub E])
    of pcancel rpickle runpickle.

Definition rpickle (c : countable) :=
  let: Countable p _ _ := c in p.

Definition runpickle (c : countable) :=
  let: Countable _ p _ := c in p.

Lemma rpickleK c: pcancel (rpickle c) (runpickle c).
Proof. by case: c. Qed.
End Countable.

(* -------------------------------------------------------------------- *)
Section CountableTheory.
Lemma countable_countable (T : countType) (E : pred T) : countable E.
Proof. by exists pickle unpickle; apply/pickleK. Qed.

Section CanCountable.
Variables (T : Type) (U : countType) (E : pred T).
Variables (f : [psub E] -> U) (g : U -> [psub E]).

Lemma can_countable : cancel f g -> countable E.
Proof.
pose p := pickle \o f; pose u n := omap g (unpickle n).
move=> can_fg; apply (@Countable _ E p u) => x.
by rewrite {}/u {}/p /= pickleK /= can_fg.
Qed.
End CanCountable.

Section CountType.
Variables (T : eqType) (E : pred T) (c : countable E).

Definition countable_countMixin  := CountMixin (rpickleK c).
Definition countable_choiceMixin := CountChoiceMixin countable_countMixin.

Definition countable_choiceType :=
  ChoiceType [psub E] countable_choiceMixin.

Definition countable_countType :=
  CountType countable_choiceType countable_countMixin.
End CountType.
End CountableTheory.

Notation "[ 'countable' 'of' c ]" := (countable_countType c)
  (format "[ 'countable'  'of'  c ]").

(* -------------------------------------------------------------------- *)
Section CountableUnion.
Variables (T : eqType) (E : nat -> pred T).

Hypothesis cE : forall i, countable (E i).

Lemma cunion_countable : countable [pred x | `[exists i, x \in E i]].
Proof.
pose S := { i : nat & [countable of cE i] }; set F := [pred x | _].
have H: forall (x : [psub F]), exists i : nat, val x \in E i.
  by case=> x /= /existsbP[i] Eix; exists i.
have G: forall (x : S), val (tagged x) \in F.
  by case=> i [x /= Eix]; apply/existsbP; exists i.
pose f (x : [psub F]) : S := Tagged (fun i => [psub E i])
  (PSubSub (xchooseP (H x))).
pose g (x : S) := PSubSub (G x).
by have /can_countable: cancel f g by case=> x hx; apply/val_inj.
Qed.
End CountableUnion.

(* -------------------------------------------------------------------- *)
Section Summable.
Variables (T : choiceType) (R : realType) (f : T -> R).

Definition summable := exists (M : R), forall (J : {fset T}),
  \sum_(x : J) `|f (val x)| <= M.

Definition sum : R :=
  (* We need some ticked `image` operator *)
  let S := [pred x | `[exists J : {fset T}, x == \sum_(x : J) `|f (val x)|]] in
  if `[summable] then sup S else 0.
End Summable.

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (T : choiceType) (R : realType).

Structure distr := Distr {
  mu : T -> R;
  _  : forall x, 0 <= mu x;
  _  : summable mu;
  _  : sum mu <= 1
}.

Definition distr_of of phant T & phant R := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant T) (Phant R))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.
