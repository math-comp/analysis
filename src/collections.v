(* -------------------------------------------------------------------- *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype finset.
Require Import seq bigop ssrprop Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac idone := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Delimit Scope rset_scope with rset.

Local Open Scope rset_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'rset' R }"
  (at level 2, format "{ 'rset'  R }").
Reserved Notation "x \mem A"
  (at level 70, format "'[hv' x '/ '  \mem  A ']'", no associativity).
Reserved Notation "x \notmem A"
  (at level 70, format "'[hv' x '/ '  \notmem  A ']'", no associativity).

Reserved Notation "{{ x | P }}"
  (at level 0, x at level 99, format "{{  x   |  P  }}").
Reserved Notation "{{ x : A | P }}"
  (at level 0, x at level 99, format "{{  x : A  |  P  }}").

(* -------------------------------------------------------------------- *)
Section Collection.

Variable (T : Type).

Inductive rset : Type := Collection of (T -> Prop).

Definition topred (E : rset) := let: Collection p := E in p.
Definition mem    (E : rset) := fun x => topred E x.

Fact rset_key : unit. Proof. by []. Qed.

Definition rset_of_pred    k := locked_with k Collection.
Canonical  rset_unlockable k := [unlockable fun rset_of_pred k].

Definition pred_of_rset (E : rset) := topred E.

Coercion pred_of_rset : rset >-> Funclass.
End Collection.

Notation "{{ x : T | P }}" := (rset_of_pred rset_key (fun x : T => P)) : form_scope.
Notation "{{ x | P }}"     := {{ x : _ | P }} : form_scope.
Notation "x \mem E"        := (mem E x) : form_scope.
Notation "x \notmem E"     := (~ mem E x) : form_scope.
Notation "{ 'rset' R }"    := (rset R) : form_scope.

(* -------------------------------------------------------------------- *)
Section RSetOps.
Variable T : Type.

Implicit Types x y z : T.
Implicit Types A B : {rset T}.

Definition rset0     := {{ x : T | False }}%rset.
Definition rsetT     := {{ x : T | True }}%rset.
Definition rset1 c   := {{ x : T | x = c }}%rset.
Definition rsetU A B := {{ x : T | x \mem A \/ x \mem B }}%rset.
Definition rsetI A B := {{ x : T | x \mem A /\ x \mem B }}%rset.
Definition rsetC A   := {{ x : T | ~ x \mem A }}%rset.
Definition rsetD A B := {{ x : T | x \mem A /\ ~ x \mem B }}%rset.

Definition rset_eq A B := forall x, x \mem A <-> x \mem B.
Definition rset_le A B := forall x, x \mem A  -> x \mem B.

Definition rdisjoint A B := forall x, x \mem A -> x \notmem B.

Definition rimage {T U : Type} (f : T -> U) (E : {rset T}) :=
  {{ y | exists2 x : T, x \mem E & y = f x }}.
End RSetOps.

Global Arguments rset0 {T}%type.
Global Arguments rsetT {T}%type.

Notation "[ 'set' x ]" := (rset1 x)     : rset_scope.
Notation "A :|: B"     := (rsetU A B)   : rset_scope.
Notation "A :&: B"     := (rsetI A B)   : rset_scope.
Notation "~: A"        := (rsetC A)     : rset_scope.
Notation "A :\: B"     := (rsetD A B)   : rset_scope.
Notation "A == B"      := (rset_eq A B) : rset_scope.
Notation "A <= B"      := (rset_le A B) : rset_scope.

(* -------------------------------------------------------------------- *)
Section FSetEq.
Variable T U : Type.

Implicit Types x y z : T.
Implicit Types A B C : {rset T}.
Implicit Types f g h : T -> U.

Local Notation rseq := (@rset_eq T) (only parsing).

Lemma req_refl A : (A == A)%rset.
Proof. by []. Qed.

Lemma req_sym A B : (A == B)%rset -> (B == A)%rset.
Proof. by move=> eq_AB x; rewrite eq_AB. Qed.

Lemma req_trans A B C :
  (A == B)%rset -> (B == C)%rset -> (A == C)%rset.
Proof. by move=> eq_AB eq_BC x; rewrite eq_AB eq_BC. Qed.

Lemma rle_refl A : (A <= A)%rset.
Proof. by []. Qed.

Lemma rle_asym A B :
  (A <= B)%rset -> (B <= A)%rset -> (A == B)%rset.
Proof. by move=> le_AB le_BA x; split=> [/le_AB|/le_BA]. Qed.

Lemma rle_trans A B C :
  (A <= B)%rset -> (B <= C)%rset -> (A <= C)%rset.
Proof. by move=> le_AB le_BC x /le_AB /le_BC. Qed.

Lemma in_rset P x : x \mem {{ y | P y }} <-> P x.
Proof. by rewrite unlock. Qed.

Lemma rsetP A B : (A == B) = (forall x, x \mem A <-> x \mem B).
Proof. by []. Qed.
End FSetEq.

(* -------------------------------------------------------------------- *)
Local Notation inE := (in_rset, inE).

Add Parametric Relation {T} : {rset T} (@rset_eq T)
  reflexivity  proved by (@req_refl  T)
  symmetry     proved by (@req_sym   T)
  transitivity proved by (@req_trans T)
  as req_equality.

Add Parametric Relation {T} : {rset T} (@rset_le T)
  reflexivity  proved by (@rle_refl  T)
  transitivity proved by (@rle_trans T)
  as rle_porder.

Add Parametric Morphism {T} : (@mem T) with
  signature @rset_eq T ==> @eq T ==> iff as rset_mem_morphism.
Proof. by move=> A B; apply. Qed.

Add Parametric Morphism {T} : (@rsetC T) with
  signature @rset_eq T ==> @rset_eq T as rsetC_morphism.
Proof. by move=> A B eq_AB x; rewrite !inE (eq_AB x). Qed.

Add Parametric Morphism {T} : (@rsetU T) with
  signature @rset_eq T ==> @rset_eq T ==> @rset_eq T as rsetU_morphism.
Proof. by move=> A B eq_AB C D eq_CD x; rewrite !inE (eq_AB x) (eq_CD x). Qed.

Add Parametric Morphism {T} : (@rsetI T) with
  signature @rset_eq T ==> @rset_eq T ==> @rset_eq T as rsetI_morphism.
Proof. by move=> A B eq_AB C D eq_CD x; rewrite !inE (eq_AB x) (eq_CD x). Qed.

Add Parametric Morphism {T} : (@rsetD T) with
  signature @rset_eq T ==> @rset_eq T ==> @rset_eq T as rsetD_morphism.
Proof. by move=> A B eq_AB C D eq_CD x; rewrite !inE (eq_AB x) (eq_CD x). Qed.

Add Parametric Morphism {T} : (@rset_le T) with
  signature @rset_eq T ==> @rset_eq T ==> iff as rsetle_morphism.
Proof.
move=> A B eq_AB C D eq_CD; split=> le x;
  by move=> /eq_AB /le /eq_CD.
Qed.

(* -------------------------------------------------------------------- *)
Section FSetTheory.
Variables T U : Type.

Implicit Types x y z : T.
Implicit Types A B C : {rset T}.
Implicit Types f g h : T -> U.

Lemma in_rset0 x : x \mem @rset0 T <-> False.
Proof. by rewrite inE. Qed.

Lemma in_rsetT x : x \mem @rsetT T.
Proof. by rewrite inE. Qed.

Lemma in_rsetU A B x :
  (x \mem A :|: B) <-> (x \mem A \/ x \mem B).
Proof. by rewrite inE. Qed.

Lemma in_rsetI A B x :
  (x \mem A :&: B) <-> (x \mem A /\ x \mem B).
Proof. by rewrite inE. Qed.

Lemma in_rsetD A B x :
  (x \mem A :\: B) <-> (x \mem A /\ x \notmem B).
Proof. by rewrite inE. Qed.

Lemma in_rsetC A x :
  (x \mem ~: A) <-> (x \notmem A).
Proof. by rewrite inE. Qed.

(*-------------------------------------------------------------------- *)
Lemma rsetUC A B : A :|: B == B :|: A.
Proof. by move=> x; rewrite !inE orpC. Qed.

Lemma rset0U A : rset0 :|: A == A.
Proof. by move=> x; rewrite !inE orFp. Qed.

Lemma rsetU0 A : A :|: rset0 == A.
Proof. by rewrite rsetUC rset0U. Qed.

Lemma rsetUA A B C : A :|: (B :|: C) == A :|: B :|: C.
Proof. by move=> x; rewrite !inE orpA. Qed.

Lemma rsetUCA A B C : A :|: (B :|: C) == B :|: (A :|: C).
Proof. by rewrite !rsetUA (rsetUC B). Qed.

Lemma rsetUAC A B C : A :|: B :|: C == A :|: C :|: B.
Proof. by rewrite -!rsetUA (rsetUC B). Qed.

Lemma rsetUACA A B C D : (A :|: B) :|: (C :|: D) == (A :|: C) :|: (B :|: D).
Proof. by rewrite -!rsetUA (rsetUCA B). Qed.

Lemma rsetTU A : rsetT :|: A == rsetT.
Proof. by move=> x; rewrite !inE orTp. Qed.

Lemma rsetUT A : A :|: rsetT == rsetT.
Proof. by rewrite rsetUC rsetTU. Qed.

Lemma rsetUid A : A :|: A == A.
Proof. by move=> x; rewrite inE orpp. Qed.

Lemma rsetUUl A B C : A :|: B :|: C == (A :|: C) :|: (B :|: C).
Proof. by rewrite rsetUA !(rsetUAC _ C) -(rsetUA _ C) rsetUid. Qed.

Lemma rsetUUr A B C : A :|: (B :|: C) == (A :|: B) :|: (A :|: C).
Proof. by rewrite !(rsetUC A) rsetUUl. Qed.

(* -------------------------------------------------------------------- *)
Lemma rsetIC A B : A :&: B == B :&: A.
Proof. by move=> x; rewrite !inE andpC. Qed.

Lemma rsetTI A : rsetT :&: A == A.
Proof. by move=> x; rewrite !inE andTp. Qed.

Lemma setIT A : A :&: rsetT == A.
Proof. by rewrite rsetIC rsetTI. Qed.

Lemma rset0I A : rset0 :&: A == rset0.
Proof. by move=> x; rewrite !inE andFp. Qed.

Lemma rsetI0 A : A :&: rset0 == rset0.
Proof. by rewrite rsetIC rset0I. Qed.

Lemma rsetIA A B C : A :&: (B :&: C) == A :&: B :&: C.
Proof. by move=> x; rewrite !inE andpA. Qed.

Lemma rsetICA A B C : A :&: (B :&: C) == B :&: (A :&: C).
Proof. by rewrite !rsetIA (rsetIC A). Qed.

Lemma rsetIAC A B C : A :&: B :&: C == A :&: C :&: B.
Proof. by rewrite -!rsetIA (rsetIC B). Qed.

Lemma rsetIACA A B C D : (A :&: B) :&: (C :&: D) == (A :&: C) :&: (B :&: D).
Proof. by rewrite -!rsetIA (rsetICA B). Qed.

Lemma rsetIid A : A :&: A == A.
Proof. by move=> x; rewrite inE andpp. Qed.

Lemma rsetIIl A B C : A :&: B :&: C == (A :&: C) :&: (B :&: C).
Proof. by rewrite rsetIA !(rsetIAC _ C) -(rsetIA _ C) rsetIid. Qed.

Lemma rsetIIr A B C : A :&: (B :&: C) == (A :&: B) :&: (A :&: C).
Proof. by rewrite !(rsetIC A) rsetIIl. Qed.

(* -------------------------------------------------------------------- *)
Lemma rsetIUr A B C : A :&: (B :|: C) == (A :&: B) :|: (A :&: C).
Proof. by move=> x; rewrite !inE andp_orr. Qed.

Lemma rsetIUl A B C : (A :|: B) :&: C == (A :&: C) :|: (B :&: C).
Proof. by move=> x; rewrite !inE andp_orl. Qed.

Lemma rsetUIr A B C : A :|: (B :&: C) == (A :|: B) :&: (A :|: C).
Proof. by move=> x; rewrite !inE orp_andr. Qed.

Lemma rsetUIl A B C : (A :&: B) :|: C == (A :|: C) :&: (B :|: C).
Proof. by move=> x; rewrite !inE orp_andl. Qed.

Lemma rsetUK A B : (A :|: B) :&: A == A.
Proof. by move=> x; rewrite !inE orpK. Qed.

Lemma rsetKU A B : A :&: (B :|: A) == A.
Proof. by move=> x; rewrite !inE orKp. Qed.

Lemma rsetIK A B : (A :&: B) :|: A == A.
Proof. by move=> x; rewrite !inE andpK. Qed.

Lemma rsetKI A B : A :|: (B :&: A) == A.
Proof. by move=> x; rewrite !inE andKp. Qed.

(* -------------------------------------------------------------------- *)
Lemma rsetCK A : classical -> ~: (~: A) == A.
Proof. by move=> lem x; rewrite !inE negpK. Qed.

Lemma mem_rsetCC A x : x \mem A -> x \mem ~: (~: A).
Proof. by  rewrite !inE => xA; apply. Qed.
End FSetTheory.

(* -------------------------------------------------------------------- *)
Section Image.
Variable T U : Type.

Implicit Types A B C : {rset T}.
Implicit Types f g h : T -> U.

Lemma mem_image f A x : x \mem A -> f x \mem rimage f A.
Proof. by move=> xA; rewrite in_rset; exists x. Qed.

Lemma imageP f A y :
  (exists2 x, x \mem A & y = f x) <-> (y \mem rimage f A).
Proof. by rewrite in_rset. Qed.

Lemma sub_image f (A : {rset T}) (B : {rset U}) :
      (rimage f A <= B)
  <-> (forall x, x \mem A -> f x \mem B).
Proof.
split=> [le_fA_B x xA|]; first by apply/le_fA_B/mem_image.
by move=> le_fA_B x /in_rset [y yA ->]; apply/le_fA_B.
Qed.
End Image.

(* -------------------------------------------------------------------- *)
Lemma mem_bigU {I T} (s : seq I) (F : I -> {rset T}) x:
      (x \mem \big[@rsetU _/rset0]_(i <- s) (F i))
  <-> (exists2 i, i < size s & x \mem nth rset0 (map F s) i).
Proof.
elim: s => [|A s ih].
  rewrite !big_nil; split=> [/(@in_rset0 _ x)|] //.
  by case=> i _; rewrite nth_nil => /in_rset0.
rewrite big_cons in_rsetU; split.
  by case=> [|/ih [] i] h; [exists 0 | exists i.+1].
by case=> [] [|i] /= h; [left|right; apply/ih; exists i].
Qed.

(* -------------------------------------------------------------------- *)
Lemma big_endo_rset I {T} f idx op (r : seq I) (F : I -> {rset T}):
     (f idx == idx)%rset
  -> (forall A B, f (op A B) == op (f A) (f B))%rset
  -> (forall A B C D, A == B -> C == D -> op A C == op B D)%rset
  -> (f (\big[op/idx]_(i <- r) (F i)) == \big[op/idx]_(i <- r) (f (F i)))%rset.
Proof.
move=> f0 fop feq; elim/big_ind2: _ => //.
by move=> A B C D; rewrite fop => /feq; apply.
Qed.
