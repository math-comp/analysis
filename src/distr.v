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
Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

(* -------------------------------------------------------------------- *)
Require Import xfinmap.

Section BigFSet.
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
End BigFSet.

Arguments big_fset_seq_cond [R idx op T J] P F.
Arguments big_fset_seq [R idx op T J] F.
Arguments big_seq_fset_cond [R idx op T s] P F _.
Arguments big_seq_fset [R idx op T s] F _.

(* -------------------------------------------------------------------- *)
Lemma summable_seqP {R : realType} (T : choiceType) (f : T -> R) :
  summable f <-> (exists2 M, 0 <= M &
    forall s : seq T, uniq s -> \sum_(x <- s) `|f x| <= M).
Proof.
split=> [/summableP|] [M gt0_M h]; exists M => //.
  by move=> s uq_s; have := h (seq_fset s); rewrite (big_seq_fset \`|f|).
by case=> J cJ; rewrite (big_fset_seq \`|_|) /=; apply/h/canonical_uniq.
Qed.

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (R : realType) (T : choiceType).

Structure distr := Distr {
  mu :> T -> R;
  _  :  forall x, 0 <= mu x;
  _  :  summable mu;
  _  :  psum mu <= 1
}.

Definition distr_of of phant R & phant T := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant R) (Phant T))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.

(* -------------------------------------------------------------------- *)
Section Clamp.
Context {R : realType}.

Definition clamp (x : R) :=
  Num.max (Num.min x 1) 0.

Lemma ge0_clamp x : 0 <= clamp x.
Proof. by rewrite ler_maxr lerr orbT. Qed.

Lemma le1_clamp x : clamp x <= 1.
Proof. by rewrite ler_maxl ler_minl lerr ler01 orbT. Qed.

Definition cp01_clamp := (ge0_clamp, le1_clamp).

Lemma clamp_in01 x : 0 <= x <= 1 -> clamp x = x.
Proof.
case/andP=> ge0_x le1_x; rewrite /clamp maxr_l.
  by rewrite ler_minr ge0_x ler01. by rewrite minr_l.
Qed.

Lemma clamp_id x : clamp (clamp x) = clamp x.
Proof. by rewrite clamp_in01 // !cp01_clamp. Qed.

Lemma clamp0 : clamp 0 = 0.
Proof. by rewrite clamp_in01 // lerr ler01. Qed.

Lemma clamp1 : clamp 1 = 1.
Proof. by rewrite clamp_in01 // lerr ler01. Qed.
End Clamp.

(* -------------------------------------------------------------------- *)
Section StdDefs.
Context {R : realType} (T : choiceType).

Definition dinsupp (mu : {distr T / R}) :=
  fun x => mu x != 0 :> R.

Definition pr (mu : {distr T / R}) (E : pred T) :=
  psum (fun x => (E x)%:R * mu x).
End StdDefs.

(* -------------------------------------------------------------------- *)
Lemma gerfin_psum {R : realType} {T : choiceType} (f : T -> R) (J : {fset T}) :
  summable f -> \sum_(j : J) `|f (val j)| <= psum f.
Proof. Admitted.

Lemma gerfinseq_psum {R : realType} {T : choiceType} (f : T -> R) (r : seq T) :
  uniq r -> summable f -> \sum_(j <- r) `|f j| <= psum f.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Section DistrTheory.
Context {R : realType} {T : choiceType} (mu : T -> R).

Definition isdistr :=
  (forall x, 0 <= mu x) /\ (forall J, uniq J -> \sum_(j <- J) mu j <= 1).

Hypothesis isd : isdistr.

Local Lemma isd1 : forall x, 0 <= mu x.
Proof. by case: isd. Qed.

Local Lemma isd2 : summable mu.
Proof.
case: isd=> _ h; apply/summable_seqP; exists 1=> //.
move=> s /h /(ler_trans _); apply; rewrite ler_eqVlt; apply/orP.
by left; apply/eqP/eq_bigr=> i _; rewrite ger0_norm ?isd1.
Qed.

Local Lemma isd3 : psum mu <= 1.
Proof. Admitted.

Definition mkdistr := @Distr R T mu isd1 isd2 isd3.

Lemma mkdistrE : mkdistr =1 mu.
Proof. by []. Qed.

Definition ispredistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x & summable mu].
End DistrTheory.

Lemma isdistr_finP {R : realType} {I : finType} (mu : I -> R) :
  (isdistr mu) <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof. split=> -[ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(ler_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= ler_addl sumr_ge0.
Qed.

(* -------------------------------------------------------------------- *)
Section DRat.
Context {R : realType} (T : choiceType).

Local Notation distr := {distr T / R}.

Implicit Types (s : seq T).

Definition mrat (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma ge0_mrat s : forall x, 0 <= mrat s x.
Proof. by move=> x; rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Lemma summable_mrat s: summable (mrat s).
Proof.
apply/summable_seqP; exists 1=> // J uqJ; rewrite (eq_bigr (mrat s)).
  by move=> j _; rewrite ger0_norm ?ge0_mrat.
rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivr_mulr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
Admitted.

Lemma isd_mrat s : isdistr (mrat s).
Proof. Admitted.

Definition drat s := locked (mkdistr (isd_mrat s)).

Lemma drat1E s x :
  drat s x = (count_mem x s)%:R / (size s)%:R.
Proof. by unlock drat; rewrite mkdistrE. Qed.

Definition dnull   := locked (drat [::]).
Definition dunit x := locked (drat [:: x]).
Definition duni  s := locked (drat (undup s)).

Lemma dnull1E x : dnull x = 0.
Proof. by unlock dnull; rewrite drat1E invr0 mulr0. Qed.

Lemma dunit1E x y : (dunit x) y = (x == y)%:R.
Proof. by unlock dunit; rewrite drat1E /= !(simpm, invr1). Qed.

Lemma duni1E s x : (duni s) x = (x \in s)%:R / (size (undup s))%:R.
Proof.
by unlock duni; rewrite drat1E count_uniq_mem ?(mem_undup, undup_uniq).
Qed.
End DRat.

(* -------------------------------------------------------------------- *)
Lemma summable_fin {R : realType} (I : finType) (f : I -> R) : summable f.
Proof. Admitted.

Lemma psum_fin {R : realType} (I : finType) (f : I -> R) :
  psum f = \sum_i `|f i|.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Section Flip.
Context {R : realType}.

Definition mflip (xt : R) :=
  fun b => if b then clamp xt else 1 - clamp xt.

Lemma isd_mflip xt : isdistr (mflip xt).
Proof. apply/isdistr_finP; split=> [b|].
+ by case: b; rewrite ?subr_ge0 cp01_clamp.
+ by rewrite /index_enum !unlock /= addr0 addrCA subrr addr0.
Qed.

Definition dflip (xt : R) := locked (mkdistr (isd_mflip xt)).

Lemma dflip1E xt : dflip xt =1 mflip xt.
Proof. by unlock dflip; apply/mkdistrE. Qed.
End Flip.

(* -------------------------------------------------------------------- *)
Section Std.
Context {R : realType}.

Local Notation distr T := {distr T / R}.

Implicit Types (T U : choiceType).

(* -------------------------------------------------------------------- *)
Section Bind.
Variables (T U : choiceType) (f : T -> distr U) (mu : distr T).

Definition mlet := fun y : U =>
  psum (fun x => mu x * f x y).

Lemma isd_mlet : isdistr mlet.
Proof. Admitted.

Definition dlet := locked (mkdistr isd_mlet).
End Bind.

(* -------------------------------------------------------------------- *)
Definition mlim T (f : nat -> distr T) :=
  fun x => nlim (fun n => f n x).

Lemma isd_mlim T (f : nat -> distr T) : isdistr (mlim f).
Proof. Admitted.  

Definition dlim T (f : nat -> distr T) :=
  locked (mkdistr (isd_mlim f)).

(* -------------------------------------------------------------------- *)
Lemma ge0_psum (T : choiceType) (f : T -> R) : 0 <= psum f.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Section Marginals.
Variable (T U : choiceType) (mu : distr (T * U)).

Definition mfst := fun x => psum (fun y => mu (x, y)).
Definition msnd := fun y => psum (fun x => mu (x, y)).

Lemma isd_mfst : isdistr mfst.
Proof. Admitted.

Lemma isd_msnd : isdistr msnd.
Proof. Admitted.

Definition dfst := locked (mkdistr isd_mfst).
Definition dsnd := locked (mkdistr isd_msnd).
End Marginals.
End Std.

(* -------------------------------------------------------------------- *)
Section PrTheory.
Context {R : realType} (T : choiceType).

Lemma pr_dunit (E : pred T) (x : T) :
  pr (R := R) (dunit x) E = (E x)%:R.
Proof. Admitted.
End PrTheory.

(* -------------------------------------------------------------------- *)
