(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool eqtype ssrfun ssrprop collections.
Require Import ssrnat choice fintype seq bigop.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope rel_scope with rel.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'rel' R }"
  (at level 2, format "{ 'rel'  R }").
Reserved Notation "x ~_[ R ] y"
  (at level 70, format "x  ~_[ R ]  y", no associativity).
Reserved Notation "[ 'rel' x y | E ]"
  (at level 0, x ident, y ident, format "[ 'rel'  x  y  |  E ]").
Reserved Notation "[ 'rel' x y : T | E ]"
  (at level 0, x ident, y ident, format "[ 'rel'  x  y  :  T  |  E ]").

Reserved Notation "R :.: S"
  (at level 54, left associativity).
Reserved Notation "~: R"
  (at level 35, right associativity).

Reserved Notation "R ^?"
  (at level 3, format "R ^?", left associativity).
Reserved Notation "R ^*"
  (at level 3, format "R ^*", left associativity).
Reserved Notation "R ^+"
  (at level 3, format "R ^+", left associativity).
Reserved Notation "R ^="
  (at level 3, format "R ^=", left associativity).

(* -------------------------------------------------------------------- *)
Section Relations.
Variable T : Type.

Inductive rel := Rel of (T -> T -> Prop).

Definition torel (R : rel) := let: Rel r := R in r.

Fact rel_key : unit. Proof. by []. Qed.

Definition rel_of_pred    k := locked_with k Rel.
Canonical  rel_unlockable k := [unlockable fun rel_of_pred k].

Definition pred_of_rel (R : rel) := torel R.

Coercion pred_of_rel : rel >-> Funclass.
End Relations.

Bind Scope rel_scope with rel.

Notation "{ 'rel' T }" := (rel T).
Notation "x ~_[ R ] y" := (torel R%rel x y).

Notation "[ 'rel' x y : T | E ]" := (rel_of_pred rel_key (fun (x y : T) => E)).
Notation "[ 'rel' x y  | E ]"    := [rel x y : _ | E].

Global Arguments torel {T}%type_scope R%rel_scope _ _.

(* -------------------------------------------------------------------- *)
Section RelFacts.
Variable T : Type.

Lemma in_rel (E : T -> T -> Prop) x y:
  x ~_[[rel a b | E a b]] y <-> E x y.
Proof. by rewrite unlock. Qed.
End RelFacts.

(* -------------------------------------------------------------------- *)
Section StdRelations.
Context {T : Type}.

Implicit Types x y : T.
Implicit Types R S : {rel T}.

Definition rel_eq R S :=
  forall x y, (x ~_[R] y) <-> (x ~_[S] y).

Definition subrel R S :=
  forall x y, x ~_[R] y -> x ~_[S] y.

Definition rel0 := [rel x y : T | False].
Definition relT := [rel x y : T | True].

Definition relU R S := [rel x y | x ~_[R] y \/ x ~_[S] y].
Definition relI R S := [rel x y | x ~_[R] y /\ x ~_[S] y].
Definition relD R S := [rel x y | x ~_[R] y /\ ~ x ~_[S] y].
Definition relS R S := [rel x y | exists z, x ~_[R] z /\ z ~_[S] y].

Inductive tc (R : T -> T -> Prop) : T -> T -> Prop :=
| TC_R : forall x y, R x y -> tc R x y
| TC_T : forall y x z, R x y -> tc R y z -> tc R x z.

Inductive eqv (R : T -> T -> Prop) : T -> T -> Prop :=
| TE_R : forall x, eqv R x x
| TE_S : forall x y, eqv R x y -> eqv R y x
| TE_T : forall y x z, R x y -> eqv R y z -> eqv R x z.

Definition relCR  R := [rel x y | x = y \/ x ~_[R] y].
Definition relCT  R := [rel x y | tc R x y].
Definition relCRT R := [rel x y | x = y \/ tc R x y].
Definition relCS  R := [rel x y | y ~_[R] x].
Definition relCE  R := [rel x y | eqv R x y].

Definition relF (F : T -> option T) := [rel x y | Some y = F x].

Definition rmap {U} (R : {rel T}) (f : U -> T) :=
  [rel x y | f x ~_[R] f y].

Definition irreflexive R :=
  forall x, ~(x ~_[R] x).

Definition reflexive R :=
  forall x, x ~_[R] x.

Definition symmetric R :=
  forall x y, x ~_[R] y -> y ~_[R] x.

Definition transitive R :=
  forall y x z, x ~_[R] y -> y ~_[R] z -> x ~_[R] z.

Definition equivalence R :=
  [/\ reflexive R, symmetric R & transitive R].

Definition acyclic R :=
  irreflexive (relCT R).
End StdRelations.

Notation "R :.: S" := (relS R S) : rel_scope.
Notation "R :|: S" := (relU R S) : rel_scope.
Notation "R :&: S" := (relI R S) : rel_scope.
Notation "R :\: S" := (relD R S) : rel_scope.
Notation "R \o f"  := (rmap R f) : rel_scope.

Notation "R ^*"  := (relCRT R) : rel_scope.
Notation "R ^+"  := (relCT R)  : rel_scope.
Notation "R ^-1" := (relCS R)  : rel_scope.
Notation "R ^?"  := (relCR R)  : rel_scope.

Notation "R == S" := (rel_eq R S) : rel_scope.
Notation "R <= S" := (subrel R S) : rel_scope.

Notation "R <= S <= V" := (subrel R S /\ subrel S V) : rel_scope.

(* -------------------------------------------------------------------- *)
Section RelEq.
Variable T : Type.

Implicit Types x y z : T.
Implicit Types R S V : {rel T}.

Lemma req_refl S : (S == S)%rel.
Proof. by []. Qed.

Lemma req_sym R S : (R == S)%rel -> (S == R)%rel.
Proof. by move=> eq_RS x y; rewrite eq_RS. Qed.

Lemma req_trans R S V : (R == S)%rel -> (S == V)%rel -> (R == V)%rel.
Proof. by move=> eq_RS eq_SV x y; rewrite eq_RS eq_SV. Qed.
End RelEq.

Add Parametric Relation T : {rel T} (@rel_eq T)
  reflexivity  proved by (@req_refl  T)
  symmetry     proved by (@req_sym   T)
  transitivity proved by (@req_trans T)
  as req_equality.

Add Parametric Morphism {T} : (@torel T) with
  signature @rel_eq T ==> @eq T  ==> @eq T ==> iff as foo.
Proof. by move=> R S; apply. Qed.

Add Parametric Morphism {T} : (@relU T) with
  signature @rel_eq T ==> @rel_eq T ==> @rel_eq T as relU_morphism.
Proof.
  move=> R S eq_RS V W eq_VW x y.
  by rewrite !in_rel (eq_RS x) (eq_VW x).
Qed.

Add Parametric Morphism {T} : (@relI T) with
  signature @rel_eq T ==> @rel_eq T ==> @rel_eq T as relI_morphism.
Proof.
  move=> R S eq_RS V W eq_VW x y.
  by rewrite !in_rel (eq_RS x) (eq_VW x).
Qed.

(* -------------------------------------------------------------------- *)
Add Parametric Morphism {T} : (@relCR T) with
  signature @rel_eq T ==> @rel_eq T as relCR_morphism.
Proof. by move=> R S eq_RS x y; rewrite !in_rel eq_RS. Qed.

Add Parametric Morphism {T} : (@relCS T) with
  signature @rel_eq T ==> @rel_eq T as relCS_morphism.
Proof. by move=> R S eq_RS x y; rewrite !in_rel eq_RS. Qed.

Fact tc_morph {T} (R S : T -> T -> Prop) :
     (forall x y, R x y -> S x y)
  -> (forall x y, tc R x y -> tc S x y).
Proof.
move=> le_RS x y; elim=> {x y} [x y Rxy | y x z Rxy _ ih].
  by apply/TC_R/le_RS. by apply/(TC_T (le_RS _ _ Rxy)).
Qed.

Add Parametric Morphism {T} : (@relCT T) with
  signature @rel_eq T ==> @rel_eq T as relCT_morphism.
Proof.
move=> R S eq_RS x y; rewrite !in_rel; split;
  by move/(@tc_morph T); apply=> x' y'; rewrite eq_RS.
Qed.

Add Parametric Morphism {T} : (@relCRT T) with
  signature @rel_eq T ==> @rel_eq T as relCRT_morphism.
Proof.
move=> R S eq_RS x y; rewrite !in_rel; apply/orp_id2l;
  by split; move/(@tc_morph T); apply=> x' y'; rewrite eq_RS.
Qed.

(* -------------------------------------------------------------------- *)
Add Parametric Morphism {T} : (@subrel T) with
  signature @rel_eq T ==> @rel_eq T ==> iff as subrel_morphism.
Proof.
move=> R1 R2 eq_R S1 S2 eq_S; split=> le x y;
  by rewrite (=^~ eq_R, eq_R) (=^~ eq_S, eq_S) => /le.
Qed.

(* -------------------------------------------------------------------- *)
Add Parametric Morphism {T} : (@transitive T) with
  signature @rel_eq T ==> iff as reltr_morphism.
Proof.
move=> R S eq_RS; split=> h y x z;
  by rewrite (eq_RS, =^~ eq_RS); apply/h.
Qed.

(* -------------------------------------------------------------------- *)
Definition domain {T} (R : {rel T}) := {{ x : T | exists y, x ~_[R] y}}.
Definition range  {T} (R : {rel T}) := {{ y : T | exists x, x ~_[R] y}}.

Add Parametric Morphism {T} : (@domain T) with
  signature rel_eq ==> @rset_eq T as domain_morphism.
Proof.
move=> R S eq_RS x; rewrite !in_rset; split;
  by case=> y ?; exists y; rewrite (eq_RS, =^~ eq_RS).
Qed.

Add Parametric Morphism  {T} : (@range T) with
  signature rel_eq ==> @rset_eq T as range_morphism.
Proof.
move=> R S eq_RS x; rewrite !in_rset; split;
  by case=> y ?; exists y; rewrite (eq_RS, =^~ eq_RS).
Qed.

(* -------------------------------------------------------------------- *)
Definition rbigU {T} (R : seq {rel T}) :=
  [rel x y | exists i, x ~_[nth rel0 R i] y].

Definition rbigI {T} (R : seq {rel T}) :=
  [rel x y | forall i, x ~_[nth rel0 R i] y].

(* -------------------------------------------------------------------- *)
Lemma in_rel0 {T} {x y : T} : x ~_[rel0] y <-> False.
Proof. by rewrite in_rel. Qed.

Lemma in_relU {T} (R S : {rel T}) x y :
  x ~_[R :|: S] y <-> (x ~_[R] y \/ x ~_[S] y).
Proof. by rewrite in_rel. Qed.

Lemma in_relI {T} (R S : {rel T}) x y :
  x ~_[R :&: S] y <-> (x ~_[R] y /\ x ~_[S] y).
Proof. by rewrite in_rel. Qed.

Lemma in_relD {T} (R S : {rel T}) x y :
  x ~_[R :\: S] y <-> (x ~_[R] y /\ ~ x ~_[S] y).
Proof. by rewrite in_rel. Qed.

Lemma in_relV {T} (R : {rel T}) x y :
  x ~_[R^-1] y <-> y ~_[R] x.
Proof. by rewrite in_rel. Qed.

Lemma in_relS {T} (R1 R2:rel T) x y :
  x ~_[R1 :.: R2] y <-> exists z, x ~_[R1] z /\ z ~_[R2] y.
Proof. by rewrite in_rel. Qed.

Lemma in_relBU {T} (R : seq {rel T}) x y :
  x ~_[rbigU R] y <-> exists i, x ~_[nth rel0 R i] y.
Proof. by rewrite in_rel. Qed.

Lemma in_relBI {T} (R : seq {rel T}) x y :
  x ~_[rbigI R] y <-> forall i, x ~_[nth rel0 R i] y.
Proof. by rewrite in_rel. Qed.

Lemma in_rmap {T U} (R : {rel T}) (f : U -> T) x y :
  x ~_[R \o f] y <-> f x ~_[R] f y.
Proof. by rewrite in_rel. Qed.

(* -------------------------------------------------------------------- *)
Lemma in_rel3U {T} (R1 R2 R3 : {rel T}) x y :
      (x ~_[R1 :|: R2 :|: R3] y)
  <-> [\/ x ~_[R1] y, x ~_[R2] y | x ~_[R3] y].
Proof.
  rewrite !in_relU; split; last by case; tauto.
  (do! case)=> ?; do [by apply/Or31 | by apply/Or32 | by apply/Or33].
Qed.

Lemma in_rel4U {T} (R1 R2 R3 R4 : {rel T}) x y :
      (x ~_[R1 :|: R2 :|: R3 :|: R4] y)
  <-> [\/ x ~_[R1] y, x ~_[R2] y, x ~_[R3] y | x ~_[R4] y].
Proof.
  rewrite !in_relU; split; last by case; tauto.
  (do! case)=> ?; do [
     by apply/Or41 | by apply/Or42
   | by apply/Or43 | by apply/Or44 ].
Qed.

(* -------------------------------------------------------------------- *)
Lemma in_rel3I {T} (R1 R2 R3 : {rel T}) x y :
      (x ~_[R1 :&: R2 :&: R3] y)
  <-> [/\ x ~_[R1] y, x ~_[R2] y & x ~_[R3] y].
Proof. by rewrite !in_relI; split=> [[] []|[]]. Qed.

Lemma in_rel4I {T} (R1 R2 R3 R4 : {rel T}) x y :
      (x ~_[R1 :&: R2 :&: R3 :&: R4] y)
  <-> [/\ x ~_[R1] y, x ~_[R2] y, x ~_[R3] y & x ~_[R4] y].
Proof. by rewrite !in_relI; split=> [[] [] []|[]]. Qed.

(* -------------------------------------------------------------------- *)
Lemma relUl {T} (R S : {rel T}) : (R <= R :|: S)%rel.
Proof. by move=> x y Rxy; rewrite in_rel; left. Qed.

Lemma relUr {T} (R S : {rel T}) : (S <= R :|: S)%rel.
Proof. by move=> x y Rxy; rewrite in_rel; right. Qed.

(* -------------------------------------------------------------------- *)
Lemma relU31 T (R1 R2 R3 : {rel T}) x y :
  x ~_[R1] y -> x ~_[R1 :|: R2 :|: R3] y.
Proof. by move=> xR1y; apply/in_rel3U; apply/Or31. Qed.

Lemma relU32 T (R1 R2 R3 : {rel T}) x y :
  x ~_[R2] y -> x ~_[R1 :|: R2 :|: R3] y.
Proof. by move=> xR2y; apply/in_rel3U; apply/Or32. Qed.

Lemma relU33 T (R1 R2 R3 : {rel T}) x y :
  x ~_[R3] y -> x ~_[R1 :|: R2 :|: R3] y.
Proof. by move=> xR3y; apply/in_rel3U; apply/Or33. Qed.

(* -------------------------------------------------------------------- *)
Lemma rbigUE {T} (s : seq (rel T)) :
  (rbigU s == \big[relU/rel0]_(R <- s) R)%rel.
Proof.
move=> x y; elim: s => [|R s ih].
  rewrite big_nil !in_rel; split=> //; case.
  by move=> i; rewrite nth_nil in_rel0.
rewrite big_cons !in_rel; split; last first.
  case=> [|/ih /in_relBU [i Rxy]]; last by exists i.+1.
  by move=> Rxy; exists 0.
case=> [] [|i] /= h; [by left | right].
by apply/ih/in_relBU; exists i.
Qed.

(* -------------------------------------------------------------------- *)
Lemma rbigIE {T} (s : seq (rel T)) :
  (rbigI s == \big[relI/rel0]_(R <- s) R)%rel.
Proof.
move=> x y; elim: s => [|R s ih].
  by rewrite big_nil !in_rel; split=> // /(_ 0) /in_rel0.
rewrite big_cons !in_rel; split.
  move=> h; split; first by apply/(h 0).
  by rewrite -ih in_relBI => i; apply/(h i.+1).
by case=> xRy /ih /in_relBI x_sI_y [|i] /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma big_endo_rel I {T} f idx op (r : seq I) (F : I -> {rel T}) :
     (f idx == idx)%rel
  -> (forall A B, f (op A B) == op (f A) (f B))%rel
  -> (forall A B C D, A == B -> C == D -> op A C == op B D)%rel
  -> (f (\big[op/idx]_(i <- r) (F i)) == \big[op/idx]_(i <- r) (f (F i)))%rel.
Proof.
move=> f0 fop feq; elim/big_ind2: _ => //.
by move=> A B C D; rewrite fop => /feq; apply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma relUC {T} (R S : {rel T}) : (R :|: S == S :|: R)%rel.
Proof. by move=> x y; rewrite !in_rel orpC. Qed.

Lemma relUA {T} (R S V : {rel T}) : (R :|: (S :|: V) == R :|: S :|: V)%rel.
Proof. by move=> x y; rewrite !in_rel orpA. Qed.

Lemma relU0 {T} (R : {rel T}) : (R :|: rel0 == R)%rel.
Proof. by move=> x y; rewrite !in_rel orpF. Qed.

Lemma rel0U {T} (R : {rel T}) : (rel0 :|: R == R)%rel.
Proof. by rewrite relUC relU0. Qed.

Lemma relU1 {T} (R : {rel T}) : (R :|: relT == relT)%rel.
Proof. by move=> x y; rewrite !in_rel orpT. Qed.

Lemma rel1U {T} (R : {rel T}) : (relT :|: R == relT)%rel.
Proof. by move=> x y; rewrite relUC relU1. Qed.

(* -------------------------------------------------------------------- *)
Lemma relIC {T} (R S : {rel T}) : (R :&: S == S :&: R)%rel.
Proof. by move=> x y; rewrite !in_rel andpC. Qed.

Lemma relIA {T} (R S V : {rel T}) : (R :&: (S :&: V) == R :&: S :&: V)%rel.
Proof. by move=> x y; rewrite !in_rel andpA. Qed.

Lemma relI0 {T} (R : {rel T}) : (R :&: rel0 == rel0)%rel.
Proof. by move=> x y; rewrite !in_rel andpF. Qed.

Lemma rel0I {T} (R : {rel T}) : (rel0 :&: R == rel0)%rel.
Proof. by rewrite relIC relI0. Qed.

Lemma relI1 {T} (R : {rel T}) : (R :&: relT == R)%rel.
Proof. by move=> x y; rewrite !in_rel andpT. Qed.

Lemma rel1I {T} (R : {rel T}) : (relT :&: R == R)%rel.
Proof. by move=> x y; rewrite relIC relI1. Qed.

(* -------------------------------------------------------------------- *)
Lemma relSA {T} (R S V : {rel T}) : (R :.: (S :.: V) == R :.: S :.: V)%rel.
Proof.
move=> x z; rewrite !in_rel; split.
  case=> y [xRy /in_relS [w] [yRw wRz]]; exists w.
  by split=> //; apply/in_relS; exists y; split.
case=> y [/in_relS [w] [xRw wRy] yRz]; exists w.
by split=> //; apply/in_relS; exists y; split.
Qed.

Lemma relS0 {T} (R : {rel T}) : (R :.: rel0 == rel0)%rel.
Proof. by move=> x y; rewrite !in_rel; split=> //; case=> z [_ /in_rel]. Qed.

Lemma rel0S {T} (R : {rel T}) : (rel0 :.: R == rel0)%rel.
Proof. by move=> x y; rewrite !in_rel; split=> //; case=> z [/in_rel]. Qed.

Lemma relSc {T} (R S : {rel T}) x y z :
  x ~_[R] y -> y ~_[S] z -> x ~_[R :.: S] z.
Proof. by move=> xRy yRz; apply/in_relS; exists y; split. Qed.

(*--------------------------------------------------------------------- *)
Lemma relD0 {T} (R : {rel T}) : (R :\: rel0 == R)%rel.
Proof. move=> x y; rewrite !in_rel; tauto. Qed.

Lemma relDT {T} (R : {rel T}) : (R :\: relT == rel0)%rel.
Proof. move=> x y; rewrite !in_rel; tauto. Qed.

Lemma relDRR {T} (R : {rel T}) : (R :\: R == rel0)%rel.
Proof. move=> x y; rewrite !in_rel; tauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma relV0 {T} : ((@rel0 T)^-1 == rel0)%rel.
Proof. by move=> x y; rewrite !in_rel. Qed.

Lemma relVU {T} (R S : rel T) : ((R :|: S)^-1 == (R^-1 :|: S^-1))%rel.
Proof. by move=> x y; rewrite !in_rel. Qed.

Lemma relVBU {T} (s : seq {rel T}) :
  ((rbigU s)^-1 == \big[relU/rel0]_(R <- s) R^-1)%rel.
Proof.
rewrite rbigUE; apply/big_endo_rel => [|A B|????->->//].
  by rewrite relV0. by rewrite relVU.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_rmap {T U} (R : {rel T}) (f1 f2 : U -> T) :
  (forall x, f1 x = f2 x) -> (R \o f1 == R \o f2)%rel.
Proof. by move=> eq x y; rewrite !in_rel !eq. Qed.

(* FIXME: set pointwise_eq for `f` *)
Add Parametric Morphism {T U} : (@rmap T U) with
  signature @rel_eq T ==> @eq _ ==> @rel_eq U as rmap_morphism.
Proof. by move=> R S eq_RS f x y; rewrite !in_rel eq_RS. Qed.

Lemma refl_rmap {T U} (R : {rel T}) (f : U -> T):
  reflexive R -> reflexive (R \o f).
Proof. by move=> refl_R x; rewrite !in_rmap; apply/refl_R. Qed.

Lemma sym_rmap {T U} (R : {rel T}) (f : U -> T):
  symmetric R -> symmetric (R \o f).
Proof. by move=> sym_R x y; rewrite !in_rmap; apply/sym_R. Qed.

Lemma trans_rmap {T U} (R : {rel T}) (f : U -> T):
  transitive R -> transitive (R \o f).
Proof. by move=> trans_R y z x; rewrite !in_rmap; apply/trans_R. Qed.

(* -------------------------------------------------------------------- *)
Lemma leRR {T} (R : {rel T}) : (R <= R)%rel.
Proof. by []. Qed.

Lemma leR_trans {T} (R1 R2 R3 : {rel T}) :
  (R1 <= R2)%rel -> (R2 <= R3)%rel -> (R1 <= R3)%rel.
Proof. by move=> le_12 le_23 x y /le_12 /le_23. Qed.

Lemma eqR_le {T} (R S : {rel T}) : (R == S)%rel <-> (R <= S <= R)%rel.
Proof.
split=> [eq_RS|[le_RS le_SR]].
  by rewrite eq_RS; split; apply/leRR.
by move=> x y; split=> [/le_RS|/le_SR].
Qed.

Add Parametric Relation T : {rel T} (@subrel T)
  reflexivity  proved by (@leRR T)
  transitivity proved by (@leR_trans T)
  as subrel_order.

(* -------------------------------------------------------------------- *)
Lemma leUR {T} (R S V : {rel T}) :
  (R <= V)%rel -> (S <= V)%rel -> (R :|: S <= V)%rel.
Proof. by move=> le_RV le_SV x y /in_relU [/le_RV|/le_SV]. Qed.

Lemma le0R {T} (R : {rel T}) : (rel0 <= R)%rel.
Proof. by move=> x y /in_rel0. Qed.

Lemma leR_rbigU {T} R (s : seq {rel T}) :
     (forall i, i < size s -> nth rel0 s i <= R)%rel
  -> (rbigU s <= R)%rel.
Proof.
rewrite rbigUE; elim: s => [|S s ih] le.
  by rewrite big_nil; apply/le0R.
rewrite big_cons; apply/leUR; first by apply/(le 0).
by apply/ih=> i; apply/(le i.+1).
Qed.

(* -------------------------------------------------------------------- *)
Lemma relCRxx {T} (R : {rel T}) : reflexive R^?.
Proof. by move=> x; rewrite in_rel; left. Qed.

Lemma relCR1 {T} (R : {rel T}) : (R <= R^?)%rel.
Proof. by move=> x y; rewrite in_rel; right. Qed.

Lemma relCRE {T} (R : {rel T}) : (R^? == [rel x y | x = y] :|: R)%rel.
Proof. by move=> x y; rewrite !in_rel. Qed.

Lemma relCR_min {T} (R S : {rel T}) :
  reflexive S -> (R <= S <= R^?)%rel -> (R^? == S)%rel.
Proof.
move=> refl_S [le_RS le_SRR]; rewrite eqR_le; split=> //.
move=> x y; rewrite relCRE !in_rel; case=> [->|].
  by apply/refl_S. by move/le_RS.
Qed.

Lemma relCR_id {T} (R : {rel T}) : reflexive R -> (R^? == R)%rel.
Proof. by move=> refl_R; apply/relCR_min=> //; split=> //; apply/relCR1. Qed.

Lemma relCRK {T} (R : {rel T}) : (R^?^? == R^?)%rel.
Proof. by rewrite relCR_id //; apply/relCRxx. Qed.

(* -------------------------------------------------------------------- *)
Lemma relCTW T (R : {rel T}) (P : T -> T -> Prop) :
     (forall x y, x ~_[R] y -> P x y)
  -> (forall y x z, x ~_[R] y -> y ~_[R^+] z -> P y z -> P x z)
  -> forall {x y}, x ~_[R^+] y -> P x y.
Proof.
move=> h1 hT x y /in_rel; elim=> // {x y} y x z.
by move=> Rxy tcRyz /hT; apply=> //; apply/in_rel.
Qed.

Lemma relCT1 {T} (R : {rel T}) : (R <= R^+)%rel.
Proof. by move=> x y Rxy; apply/in_rel/TC_R. Qed.

Lemma relCT1l {T} (R : {rel T}) y x z :
  x ~_[R] y -> y ~_[R^+] z -> x ~_[R^+] z.
Proof. by move=> Rxy /in_rel tcRyz; apply/in_rel/(TC_T Rxy). Qed.

Lemma relCT1r {T} (R : {rel T}) y x z :
  x ~_[R^+] y -> y ~_[R] z -> x ~_[R^+] z.
Proof.
move/in_rel; elim=> {x y} [x y Rxy | x t Rxy Rtx _ ih].
  by move/(@relCT1 T); apply/relCT1l.
by move/ih; apply/relCT1l.
Qed.

Lemma trans_relCT {T} (R : {rel T}) : transitive R^+.
Proof.
move=> y x z /in_rel; elim=> {x y} [x y|]; first by apply/relCT1l.
by move=> y x t Rxy _ ih /ih; apply/(relCT1l Rxy).
Qed.

Lemma relCT_min {T} (R S : {rel T}) :
  transitive S -> (R <= S <= R^+)%rel -> (R^+ == S)%rel.
Proof.
move=> trans_S [le_RS le_SRT]; rewrite eqR_le; split=> //.
move=> x y /in_rel; elim=> {x y} [x y | y x z /le_RS Sxy _ Syz].
  by move/le_RS. by apply/(trans_S y).
Qed.

Lemma relCT_id {T} (R : {rel T}) : transitive R -> (R^+ == R)%rel.
Proof. by move=> trans_R; apply/relCT_min=> //; split=> //; apply/relCT1. Qed.

Lemma relCTK {T} (R : {rel T}) : (R^+^+ == R^+)%rel.
Proof. by rewrite relCT_id //; apply/trans_relCT. Qed.

(* -------------------------------------------------------------------- *)
Lemma leR_relS_mono {T} (R1 R2 S1 S2 : rel T) :
  (R1 <= R2 -> S1 <= S2 -> R1 :.: S1 <= R2 :.: S2)%rel.
Proof.
move=> le_R le_S x y; rewrite !in_relS.
by case=> z [/le_R R2_xz /le_S S2_yz]; exists z.
Qed.

Lemma leR_relSS_trans {T} (R : {rel T}) : (R :.: R <= R^+)%rel.
Proof.
move=> x y /in_relS [z [Rxz Rzy]].
by apply/(trans_relCT (relCT1 Rxz))/relCT1.
Qed.

Lemma leR_relS_trans_mono {T} (R1 R2 S : rel T) :
  (R1 <= S -> R2 <= S -> R1 :.: R2 <= S^+)%rel.
Proof.
move=> le_R1S le_R2S; transitivity (S :.: S)%rel.
  by apply/leR_relS_mono. by apply/leR_relSS_trans.
Qed.

(* -------------------------------------------------------------------- *)
Lemma subrelCT {T} (R S : {rel T}) : (R <= S)%rel -> (R^+ <= S^+)%rel.
Proof.
move=> le_RS x y /in_rel; elim=> {x y} [x y|x y z].
  by move/le_RS=> Sxy; apply/relCT1.
by move/le_RS=> Sxy _; apply/relCT1l.
Qed.

(* -------------------------------------------------------------------- *)
Section DomainTheory.
Context {T : Type}.

Implicit Types R S : {rel T}.

Lemma range_domain R : (range R == domain R^-1)%rset.
Proof.
move=> x; rewrite !in_rset; split=> [] [y Rxy];
  by exists y; rewrite (in_relV, =^~ in_relV).
Qed.

Lemma domain0 : (domain rel0 == @rset0 T)%rset.
Proof. by move=> x; rewrite !in_rset; split=> // [] [y] /in_rel0. Qed.

Lemma domainU R S : (domain (R :|: S) == domain R :|: domain S)%rset.
Proof.
move=> x; rewrite in_rsetU !in_rset; split.
  by case=> y; rewrite in_relU; case; [left|right]; exists y.
by case=> [] [y ?]; exists y; rewrite in_relU; tauto.
Qed.

Lemma domainI R S : (domain (R :&: S) <= domain R :&: domain S)%rset.
move=> x; rewrite in_rsetI !in_rset; case=> y.
by case/in_relI=> [Rxy Sxy]; split; exists y.
Qed.

Lemma domainS R S : (domain (R :.: S) <= domain R)%rset.
Proof.
move=> a /in_rset [_] /in_relS [x] [aSx _].
by apply/in_rset; exists x.
Qed.

Lemma rangeS R S : (range (R :.: S) <= range S)%rset.
Proof.
move=> a /in_rset [_] /in_relS [x] [_ xSa].
by apply/in_rset; exists x.
Qed.

Lemma domainBU (s : seq {rel T}) :
  (domain (rbigU s) == \big[@rsetU _/rset0]_(R <- s) (domain R))%rset.
Proof.
rewrite rbigUE; elim: s => [|R s ih].
  by rewrite !big_nil domain0.
by rewrite !big_cons domainU ih.
Qed.

Lemma domainBI (s : seq {rel T}) :
  (domain (rbigI s) <= \big[@rsetI _/rset0]_(R <- s) (domain R))%rset.
Proof.
rewrite rbigIE; elim: s => [|R s ih].
  by rewrite !big_nil domain0.
rewrite !big_cons; apply/(rle_trans (@domainI _ _)).
by move=> x; rewrite !in_rsetI; case=> h1 /ih h2.
Qed.

Lemma mem_domain (R : rel T) x y :
  x ~_[R] y -> x \mem domain R.
Proof. by rewrite in_rset => Rxy; exists y. Qed.

Lemma mem_range (R : rel T) x y :
  x ~_[R] y -> y \mem range R.
Proof. by rewrite in_rset => Rxy; exists x. Qed.

Lemma trans_single (R : rel T) : 
  rdisjoint (domain R) (range R) -> transitive R. 
Proof.
  move=> disj_drR y x z /(@mem_range R) /disj_drR.
  by move=> y_notin_rR /(@mem_domain R) /y_notin_rR.
Qed.

End DomainTheory.

(* -------------------------------------------------------------------- *)
Lemma acyclicNP {T} (R : rel T) : classical ->
  ~(acyclic R) -> exists x, x ~_[R^+] x.   
Proof. by move=> cl; rewrite negp_forallN. Qed.

Lemma acyclic_subrel {T} (R1 R2 : rel T) :
  (R2 <= R1)%rel -> acyclic R1 -> acyclic R2.  
Proof. by move=> le_R1R2 ac_R1 x /(subrelCT le_R1R2) /ac_R1. Qed.

(* -------------------------------------------------------------------- *)
Section RelTheory.
Variable T : Type.

Implicit Types R S : rel T.

Lemma relI_trans R S :
  transitive R -> transitive S -> transitive (R :&: S).
Proof.
move=> trR trS y x z /in_relI [xRy xSy] /in_relI [yRz ySz].
by apply/in_relI; split; [apply/(trR y) | apply/(trS y)].
Qed.

Lemma relU_trans R S :
  transitive R -> transitive S ->
    (forall x, x \mem range R -> ~ x \mem domain S) ->
    (forall x, x \mem range S -> ~ x \mem domain R) ->
    transitive (R :|: S).
Proof.
move=> tr_R tr_S ne_RS ne_SR y x z; rewrite 2!in_relU.
case=> [Rxy|Sxy] [Ryz|Syz].
  by apply/relUl; move/tr_R: Rxy; apply.
  by case: (ne_RS y); rewrite in_rset; [exists x | exists z].
  by case: (ne_SR y); rewrite in_rset; [exists x | exists z].
  by apply/relUr; move/tr_S: Sxy; apply.
Qed.

Lemma relBU_trans (s : seq {rel T}) :
     (forall i, i < size s -> transitive (nth rel0 s i))
  -> (forall i j, i != j -> i < size s -> j < size s ->
        forall x, x \mem range (nth rel0 s i) ->
          ~ x \mem domain (nth rel0 s j))
  -> transitive (rbigU s).
Proof.
elim: s => [|R s ih] trans_s ne_s.
  by move=> y z x; rewrite rbigUE big_nil in_rel0.
move=> y z x; rewrite !rbigUE big_cons; apply/relU_trans.
+ by apply/(trans_s 0).
+ move=> {y x z} y z x; rewrite -!rbigUE; apply/ih.
    by move=> i; apply/(trans_s i.+1).
  by move=> i j; apply/(ne_s i.+1 j.+1).
+ move=> {y z x} x Rx; rewrite -rbigUE domainBU.
  rewrite -(big_map domain predT idfun) => /mem_bigU.
  case=> i; rewrite size_map => lt_i_szs.
  by rewrite map_id (nth_map rel0) //; apply/(ne_s 0 i.+1).
move=> {y z x} x; rewrite range_domain -rbigUE relVBU.
rewrite -(big_map relCS predT idfun) /=.
rewrite -rbigUE domainBU; case/mem_bigU=> i.
rewrite size_map -map_comp => lt_i_szs.
by rewrite (nth_map rel0) //= -range_domain; apply/(ne_s i.+1 0).
Qed.
End RelTheory.
