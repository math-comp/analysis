(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete.
From SsrReals Require Import realseq realsum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

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

(* -------------------------------------------------------------------- *)
Section DistrTheory.
Context {R : realType}.

Definition isdistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x, summable mu & sum mu <= 1].
End DistrTheory.
