(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Export finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Lemma uniq_fset_keys {K : choiceType} (J : {fset K}) : uniq (fset_keys J).
Proof. by case: J => J /= /canonical_uniq. Qed.

Hint Resolve uniq_fset_keys.

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

(* -------------------------------------------------------------------- *)
Section BigFSetU.
Context {R : Type} {T : choiceType} (idx : R) (op : Monoid.com_law idx).

Lemma big_fsetU (A B : {fset T}) F : [disjoint A & B] ->
  \big[op/idx]_(j : A `|` B) F (val j) =
    op (\big[op/idx]_(j : A) F (val j))
       (\big[op/idx]_(j : B) F (val j)).
Proof.
move=> dj_AB; rewrite !big_fset_seq -big_cat; apply/eq_big_perm.
apply/uniq_perm_eq=> //.
+ rewrite cat_uniq ?uniq_fset_keys !(andbT, andTb); apply/hasPn => x /=.
  by rewrite -!pred_of_finsetE; apply/fdisjointP; rewrite fdisjoint_sym.
+ by move=> x; rewrite mem_cat -!pred_of_finsetE in_fsetE.
Qed.
End BigFSetU.

(* -------------------------------------------------------------------- *)
Section BigFSetOrder.
Variable (R : realDomainType) (T : choiceType).

Lemma big_fset_subset (I J : {fset T}) (F : T -> R) :
  (forall x, (0 <= F x)%R) -> {subset I <= J} ->
    \sum_(i : I) F (val i) <= \sum_(j : J) F (val j).
Proof.
move=> ge0_F le_IJ; rewrite !big_fset_seq /=.
rewrite [X in _<=X](bigID [pred j : T | j \in I]) /=.
rewrite ler_paddr ?sumr_ge0 // -[X in _<=X]big_filter.
rewrite ler_eqVlt; apply/orP; left; apply/eqP/eq_big_perm.
apply/uniq_perm_eq; rewrite ?filter_uniq //; last move=> i.
rewrite mem_filter -!pred_of_finsetE; case/boolP: (_ \in _) => //=.
by move/le_IJ => ->.
Qed.

Lemma big_nat_mkfset (F : nat -> R) n :
  \sum_(0 <= i < n) F i =
    \sum_(i : seq_fset (iota 0 n)) F (val i).
Proof.
rewrite -(big_map val xpredT) /=; apply/eq_big_perm.
apply/uniq_perm_eq; rewrite ?iota_uniq //.
  rewrite map_inj_uniq /=; last apply/val_inj.
  by rewrite /index_enum -enumT enum_uniq.
move=> i; rewrite /index_enum unlock val_fset_sub_enum /=.
  by rewrite sort_keysE /index_iota subn0.
  by apply/sort_keys_uniq.
Qed.

Lemma big_ord_mkfset (F : nat -> R) n :
  \sum_(i < n) F i =
    \sum_(i : seq_fset (iota 0 n)) F (val i).
Proof. by rewrite -(big_mkord xpredT) big_nat_mkfset. Qed.
End BigFSetOrder.

(* -------------------------------------------------------------------- *)
Lemma enum_fsetT {I : finType} :
  perm_eq (enum [fset i | i in I]) (enum I).
Proof.
apply/uniq_perm_eq; rewrite ?enum_uniq //.
by move=> i /=; rewrite !mem_enum in_imfset.
Qed.

(* -------------------------------------------------------------------- *)
