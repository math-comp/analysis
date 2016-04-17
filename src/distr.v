(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete.
From SsrReals Require Import realseq realsum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (R : realType) (T : choiceType).

Structure distr := Distr {
  mu :> T -> R;
  _  :  forall x, 0 <= mu x;
  _  :  summable mu;
  _  :  sum mu <= 1
}.

Definition distr_of of phant R & phant T := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant R) (Phant T))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.

(* -------------------------------------------------------------------- *)
Section StdDefs.
Context {R : realType} (T : choiceType).

Definition dinsupp (mu : {distr T / R}) :=
  fun x => mu x != 0 :> R.

Definition pr (mu : {distr T / R}) (E : pred T) :=
  psum (fun x => (E x)%:R * mu x).
End StdDefs.

(* -------------------------------------------------------------------- *)
Section DistrTheory.
Context {R : realType}.

Definition isdistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x, summable mu & sum mu <= 1].
End DistrTheory.

(* -------------------------------------------------------------------- *)
Section Std.
Context {R : realType}.

Local Notation distr T := {distr T / R}.

Implicit Types (T U : choiceType).

Axiom dnull : forall T, distr T.
Axiom dunit : forall T, T -> distr T.
Axiom dlet  : forall T U, (T -> distr U) -> distr T -> distr U.
Axiom dlim  : forall T, (nat -> distr T) -> distr T.
Axiom dfst  : forall T U, distr (T * U) -> distr T.
Axiom dsnd  : forall T U, distr (T * U) -> distr U.
End Std.