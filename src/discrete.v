(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun finset finmap bigop ssralg ssrnum ssrint.
Require Import tuple bigenough ssrprop collections reals.
Require (*--*) Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

Local Open Scope rset_scope.
Local Open Scope ring_scope.
Local Open Scope real_scope.

Local Ltac idone := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Record mclassic := {
  _ : forall (P : Prop), {P}+{~P};
  _ : forall (P : Prop), P = True \/ P = False
}.

Axiom classic : mclassic.

(* -------------------------------------------------------------------- *)
Lemma pselect (P : Prop): {P}+{~P}.
Proof. by case classic. Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by case classic. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

(* -------------------------------------------------------------------- *)
Definition asbool (P : Prop) :=
  if pselect P then true else false.

Lemma asboolP (P : Prop): reflect P (asbool P).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

(* -------------------------------------------------------------------- *)
Section RSetSubtype.
Section Def.
Variable T : Type.
Variable E : {rset T}.

Record rset_sub : Type :=
  RSetSub { rsval : T; rsvalP : asbool (rsval \mem E) }.

Coercion rsval : rset_sub >-> T. 

Canonical rset_sub_subType := Eval hnf in [subType for rsval].
End Def.

Definition rset_sub_eqMixin (T : eqType) (E : {rset T}) :=
  Eval hnf in [eqMixin of rset_sub E by <:].
Canonical rset_sub_eqType (T : eqType) (E : {rset T}) :=
  Eval hnf in EqType (@rset_sub T E) (rset_sub_eqMixin E).

Definition rset_sub_choiceMixin (T : choiceType) (E : {rset T}) :=
  Eval hnf in [choiceMixin of rset_sub E by <:].
Canonical rset_sub_choiceType (T : choiceType) (E : {rset T}) :=
  Eval hnf in ChoiceType (@rset_sub T E) (rset_sub_choiceMixin E).

Definition rset_sub_countMixin (T : countType) (E : {rset T}) :=
  Eval hnf in [countMixin of rset_sub E by <:].
Canonical rset_sub_countType (T : countType) (E : {rset T}) :=
  Eval hnf in CountType (@rset_sub T E) (rset_sub_countMixin E).
End RSetSubtype.

Notation "[ 'rsub' E ]" := (@rset_sub _ E).

(* -------------------------------------------------------------------- *)
Section Countable.
Variable (T : Type) (E : {rset T}).

CoInductive countable : Type :=
  Countable
    (rpickle   : [rsub E] -> nat)
    (runpickle : nat -> option [rsub E])
    of pcancel rpickle runpickle.
End Countable.

(* -------------------------------------------------------------------- *)
Section CountableTheory.
Variable (T : countType) (E : {rset T}).

Lemma countable_countable : countable E.
Proof. by exists pickle unpickle; apply/pickleK. Qed.
End CountableTheory.

(* -------------------------------------------------------------------- *)
Section Summable.
Variables (T : choiceType) (R : realType) (f : T -> R).

Definition summable := exists (M : R), forall (J : {fset T}),
  \sum_(x : J) `|f (val x)| <= M.

Definition sum : R :=
  let S := [rset \sum_(x : J) `|f (val x)| | J : {fset T}] in
  select { sup S if summable, else 0 }.
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
