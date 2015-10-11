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
Inductive countable (R : Type) (E : {rset R}) : Type :=
  Countable (pick : R -> option nat) (unpick : nat -> R) of
      pcancel unpick pick
    & (forall x, (x \mem E) <-> (exists y, unpick y = x)).

(* -------------------------------------------------------------------- *)
Section CountableTheory.
Variables (R : Type) (E : {rset R}) (cE : countable E).

Definition pick   := let: Countable f _ _ _ := cE in f.
Definition unpick := let: Countable _ f _ _ := cE in f.

Lemma unpickK : pcancel unpick pick.
Proof. by rewrite /unpick /pick; case cE. Qed.

Lemma unpickP : forall x, (x \mem E) <-> (exists y, unpick y = x).
Proof. by rewrite /unpick /pick; case cE. Qed.
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
End Distribution.
