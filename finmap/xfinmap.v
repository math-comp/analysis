(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
From SsrReals Require Export finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

(* -------------------------------------------------------------------- *)
Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).

Lemma big_fset0_cond (T : choiceType) (P : pred _) (F : _ -> R) :
  \big[op/idx]_(i : @fset0 T | P i) F i = idx :> R.
Proof. by apply: big_pred0 => -[j hj]; have := hj; rewrite in_fset0. Qed.

Lemma big_fset0 (T : choiceType) (F : _ -> R) :
  \big[op/idx]_(i : @fset0 T) F i = idx :> R.
Proof. by apply/(big_fset0_cond xpredT). Qed.
End BigFSet.
