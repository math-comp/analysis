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

Lemma big_fset1 (T : choiceType) (F : T -> R) c :
  \big[op/idx]_(i : seq_fset [:: c]) F (val i) = F c.
Proof.
rewrite -(big_map val xpredT) /index_enum; set s := map _ _.
suff ->: s = [:: c] by rewrite big_seq1.
rewrite /s unlock val_fset_sub_enum //=; apply/perm_eq_small=> //.
by apply/uniq_perm_eq=> // x; rewrite sort_keysE.
Qed.
End BigFSet.

(* -------------------------------------------------------------------- *)
Section BigFSetCom.
Variable (R : Type) (idx : R).

Local Notation "1" := idx.

Variable op : Monoid.com_law 1.

Notation Local "'*%M'" := op (at level 0).
Notation Local "x * y" := (op x y).

Lemma big_fset_seq_cond (T : choiceType) (J : {fset T}) P F :
    \big[*%M/1]_(x : J | P (val x)) F (val x)
  = \big[*%M/1]_(x <- fset_keys J | P x) F x.
Proof.
case: J=> J c; rewrite -(big_map val) /index_enum.
by rewrite !unlock val_fset_sub_enum ?canonical_uniq.
Qed.

Lemma big_fset_seq (T : choiceType) (J : {fset T}) F :
    \big[*%M/1]_(x : J) F (val x)
  = \big[*%M/1]_(x <- fset_keys J) F x.
Proof. by apply/big_fset_seq_cond. Qed.

Lemma big_seq_fset_cond (T : choiceType) (s : seq T) P F : uniq s ->
    \big[*%M/1]_(x : seq_fset s | P (val x)) F (val x)
  = \big[*%M/1]_(x <- s | P x) F x.
Proof.
move=> eq_s; rewrite big_fset_seq_cond; apply/eq_big_perm.
by apply/uniq_perm_eq=> //=; apply/sort_keysE.
Qed.

Lemma big_seq_fset (T : choiceType) (s : seq T) F : uniq s ->
    \big[*%M/1]_(x : seq_fset s) F (val x)
  = \big[*%M/1]_(x <- s) F x.
Proof. by apply/big_seq_fset_cond. Qed.
End BigFSetCom.

Arguments big_fset_seq_cond [R idx op T J] P F.
Arguments big_fset_seq [R idx op T J] F.
Arguments big_seq_fset_cond [R idx op T s] P F _.
Arguments big_seq_fset [R idx op T s] F _.
