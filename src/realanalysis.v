(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finset bigop ssralg ssrnum ssrint rat poly bigenough.
Require Import boolp reals.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

(* -------------------------------------------------------------------- *)
Local Open Scope real_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "c %:F"
  (at level 2, format "c %:F").
Reserved Notation "f \* g"
  (at level 45, left associativity).
Reserved Notation "f \^+ n"
  (at level 29, left associativity).

(* -------------------------------------------------------------------- *)
Notation "c %:F"   := (fun _ => c) : ring_scope.
Notation "f \* g"  := (fun x => f x * g x) : ring_scope.
Notation "f \^+ n" := (fun x => (f x)^+n) : ring_scope.

Reserved Notation "[ 'lim' f --[ z ]> c ]"
  (at level 0, format "[ 'lim'  f  --[ z ]>  c ]").

Reserved Notation "[ 'slim' u --> c ]"
  (at level 0, u, c at level 10, format "[ 'slim'  u  -->  c ]").

(* -------------------------------------------------------------------- *)
Section Neiborhood.
Variable R : realType.

Implicit Types c x y z : R.

CoInductive nbh c : predArgType :=
  Nbh (r : R) of 0 < r.

Definition radius c (v : nbh c) :=
  let: Nbh r _ := v in r.

Canonical nbh_subType c :=
  Eval hnf in [subType for @radius c].

Coercion pred_of_nbh (c : R) (v : nbh c) :=
  let: Nbh r _ := v in [pred x | `|x - c| < r].

Definition mknbh c r : nbh c := insubd (Nbh c ltr01) r.

Lemma gt0_radius c (v : nbh c) : 0 < radius v.
Proof. by case: v. Qed.

Lemma mem_nbh c (v : nbh c) x : (x \in v) = (`|x - c| < radius v).
Proof. by case: v. Qed.

Lemma mem_mknbh c r x : 0 < r -> (x \in mknbh c r) = (`|x - c| < r).
Proof. by move=> gt0_r; rewrite /mknbh /insubd insubT mem_nbh. Qed.

Lemma mem_center c (v : nbh c) : c \in v.
Proof. by rewrite mem_nbh subrr normr0 gt0_radius. Qed.

Lemma radius_mknbh c r : 0 < r -> radius (mknbh c r) = r.
Proof. by move=> gt0_r; rewrite /mknbh /insubd insubT. Qed.
End Neiborhood.

Local Notation inE := (mem_nbh, mem_mknbh, inE).

Notation "''V_' a" := (nbh a)
  (at level 8, a at level 2, format "''V_' a").

Notation "''B_' ( c , r )" := (mknbh c r)
  (at level 8, c, r at level 2, format "''B_' ( c ,  r )").

(* -------------------------------------------------------------------- *)
Section NbhTheory.
Variable R : realType.

Implicit Types c x y z : R.

Lemma separable c1 c2 : c1 != c2 ->
  { v : 'V_c1 * 'V_c2 | forall x, ~ ((x \in v.1) && (x \in v.2)) }.
Proof.
move=> ne_c1c2; pose e := `|c1 - c2|; pose me := e / 2%:R.
have gt0_me: 0 < me by rewrite divr_gt0 ?ltr0Sn // normr_gt0 subr_eq0.
exists ('B_(c1, me), 'B_(c2, me)) => x /=; rewrite !mem_mknbh //.
case/andP=> lt1 lt2; have := ltr_add lt1 lt2.
move/(ler_lt_trans (ler_norm_sub _ _)).
rewrite opprB [c2-_]addrC addrACA subrr add0r.
rewrite addrC distrC -mulr2n -mulr_natr mulrAC.
by rewrite -mulrA divff ?mulr1 ?ltrr // gtr_eqF ?ltr0Sn.
Qed.

Lemma joinable c1 c2 :
  { v : 'V_c1 * 'V_c2 | nonempty [predI v.1 & v.2] }.
Proof.
pose e := `|c1 - c2|; pose me := e + 1.
have gt0_me: 0 < me by rewrite ltr_paddl // normr_ge0.
exists ('B_(c1, me), 'B_(c2, me)); exists c1.
rewrite !inE !radius_mknbh // !ltr_spaddr //.
by rewrite subrr normr0 normr_ge0.
Qed.

Lemma nbhI c (v1 v2 : 'V_c) :
  { v : 'V_c | {subset v <= v1} /\ {subset v <= v2} }.
Proof.
pose r := Num.min (radius v1) (radius v2); exists 'B_(c, r).
have gt0_r : 0 < r by rewrite ltr_minr !gt0_radius.
by split=> x; rewrite !mem_mknbh // mem_nbh ltr_minr=> /andP[].
Qed.
End NbhTheory.

(* -------------------------------------------------------------------- *)
Section Sequence.
Variable R : realType.

Implicit Types c x y z : R.
Implicit Types u v : nat -> R.

Definition slim u c :=
  forall (v : 'V_c), exists N,
    forall n, (N < n)%N -> u n \in v.

Notation "[ 'slim' u --> c ]" := (slim u c) : form_scope.

Lemma eq_slim u v c :
     (exists N, forall n, (N < n)%N -> u n = v n)
  -> [slim v --> c]
  -> [slim u --> c].
Proof.
case=> [N eq_uv limvc vc]; case: (limvc vc)=> N' lv.
pose_big_enough i; first exists i=> n lt_in.
  by rewrite eq_uv; first apply/lv; apply/(ltn_trans _ lt_in).
by close.
Qed.

Lemma uniq_slim u c1 c2 :
  [slim u --> c1] -> [slim u --> c2] -> c1 = c2.
Proof.
move=> lim1 lim2; apply/eqP/contraT => /separable.
case=> [[v1 v2]] /=; move: (lim1 v1) (lim2 v2).
case=> [N1 limv1] [N2 limv2]; pose_big_enough i.
  by case/(_ (u i)); rewrite limv1 ?limv2.
by close.
Qed.
End Sequence.
