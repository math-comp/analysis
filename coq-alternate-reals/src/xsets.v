(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect order set.
From SsrReals Require Import boolp.

Import Order.Def Order.Syntax Order.Theory SET.SetSyntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

(* -------------------------------------------------------------------- *)
Axiom ssrchoice : forall (T : eqType), Choice.mixin_of T.

(* -------------------------------------------------------------------- *)
Module Classic.
Section Choice.
Variable  (T : Type) (mT : Equality.mixin_of T).

Canonical T_eqType := EqType T mT.

Definition choiceType :=
  ChoiceType T (ssrchoice [eqType of T]).
End Choice.

Definition eqMixin (T : Type) :=
  EqMixin (fun x y => asboolP (x = y :> T)).
Definition eqType (T : Type) :=
  EqType T (eqMixin T).
End Classic.

(* -------------------------------------------------------------------- *)
Section PredEq.
Variable (T : eqType).

Definition pred_eq (p1 p2 : pred T) :=
  `[forall x, p1 x == p2 x].

Lemma pred_eqP p1 p2 : reflect (p1 = p2) (pred_eq p1 p2).
Proof.
apply: (iffP (@forallbP _ _)) => [|->//].
by move=> eq; apply/funext=> x; apply/eqP.
Qed.

Definition pred_eqMixin := EqMixin pred_eqP.
Canonical pred_eqType := EqType (pred T) pred_eqMixin.

Definition eqpP (p1 p2 : pred T) : (p1 = p2) <-> (p1 =1 p2).
Proof. by split=> [->//|] eq; apply/eqP/forallbP=> x; apply/eqP. Qed.
End PredEq.

(* -------------------------------------------------------------------- *)
Canonical pred_choiceType (T : eqType) :=
  Eval hnf in @Classic.choiceType (pred T) [eqMixin of pred T].

(* -------------------------------------------------------------------- *)
Module PredSet.
Section PredSet.
Variable (T : eqType).

Implicit Types p : pred T.

Definition le p1 p2 := `[forall x, p1 x ==> p2 x].

Lemma leP p1 p2 : reflect (forall x : T, p1 x -> p2 x) (le p1 p2).
Proof. by apply/forallPP=> x; apply/implyP. Qed.

Lemma lepp : reflexive le.
Proof. by move=> p; apply/leP. Qed.

Lemma le_antisym : antisymmetric le.
Proof.
move=> p1 p2 /andP[] /leP p12 /leP p21.
by apply/eqpP=> x; apply/idP/idP=> [/p12|/p21].
Qed.

Lemma le_trans : transitive le.
Proof. by move=> p2 p1 p3 /leP p12 /leP p23; apply/leP=> x /p12 /p23. Qed.

Definition pred_porderMixin :=
  POrderMixin (fun _ _ => erefl) lepp le_antisym le_trans.

Canonical pred_porderType := Eval hnf in
  POrderType (SET.display_set tt) (pred T) pred_porderMixin.

Notation subsetpP := leP.

Lemma eqsetpP p1 p2: (p1 = p2) <-> (forall x, (x \in p1) = (x \in p2)).
Proof. by apply/eqpP. Qed.

Definition meetp p1 p2 : pred T := [predI p1 & p2].
Definition joinp p1 p2 : pred T := [predU p1 & p2].

Local Lemma meetpE p1 p2 : forall x, (meetp p1 p2) x = p1 x && p2 x.
Proof. by []. Qed.

Local Lemma joinpE p1 p2 : forall x, (joinp p1 p2) x = p1 x || p2 x.
Proof. by []. Qed.

Local Notation mjE := (meetpE, joinpE).

Local Lemma meetpC : commutative meetp.
Proof. by move=> p1 p2; apply/eqpP=> x; rewrite !mjE andbC. Qed.

Local Lemma meetpA : associative meetp.
Proof. by move=> p1 p2 p3; apply/eqpP=> x; rewrite !mjE andbA. Qed.

Local Lemma joinpC : commutative joinp.
Proof. by move=> p1 p2; apply/eqpP=> x; rewrite !mjE orbC. Qed.

Local Lemma joinpA : associative joinp.
Proof. by move=> p1 p2 p3; apply/eqpP=> x; rewrite !mjE orbA. Qed.

Local Lemma joinpKI p2 p1 : meetp p1 (joinp p1 p2) = p1.
Proof. by apply/eqpP=> x; rewrite !mjE andb_idr // => ->. Qed.

Local Lemma meetpKU p2 p1 : joinp p1 (meetp p1 p2) = p1.
Proof. by apply/eqpP=> x; rewrite !mjE orb_idr // => /andP[]. Qed.

Local Lemma lepEmeet p1 p2 : (p1 \subset p2) = (meetp p1 p2 == p1).
Proof.
apply/subsetpP/eqP=> [h|h x]; first apply/eqpP=> x.
+ by rewrite mjE andb_idr //; apply/h.
+ by move=> p1x; move/eqpP/(_ x): h; rewrite mjE p1x.
Qed.

Local Lemma meetpUl : left_distributive meetp joinp.
Proof. by move=> p1 p2 p3; apply/eqpP=> x; rewrite !mjE andb_orl. Qed.

Definition pred_latticeMixin :=
  LatticeMixin meetpC joinpC meetpA joinpA joinpKI meetpKU lepEmeet meetpUl.

Canonical pred_latticeType := Eval hnf in
  LatticeType (pred T) pred_latticeMixin.

Local Lemma subset0p p : (pred0 : pred _) \subset p.
Proof. by apply/subsetpP. Qed.

Local Lemma subsetp1 p : p \subset (predT : pred _).
Proof. by apply/subsetpP. Qed.

Definition pred_blatticeMixin := BLatticeMixin subset0p.
Canonical pred_blatticeType := BLatticeType (pred T) pred_blatticeMixin.

Definition pred_tblatticeMixin := TBLatticeMixin subsetp1.
Canonical pred_tblatticeType := TBLatticeType (pred T) pred_tblatticeMixin.

Definition subp p1 p2 : pred _ := [predD p1 & p2].

Local Lemma subpKI p1 p2 : p2 :&: (subp p1 p2) = set0.
Proof. by apply/eqsetpP=> x; rewrite !inE; case: (x \in p2). Qed.

Local Lemma joinpIB p1 p2 : (p1 :&: p2) :|: (subp p1 p2) = p1.
Proof.
by apply/eqsetpP=> x; rewrite !inE [X in X||_]andbC -andb_orl orbN.
Qed.

Definition pred_cblatticeMixin := CBLatticeMixin subpKI joinpIB.
Canonical pred_cblatticeType := CBLatticeType (pred T) pred_cblatticeMixin.

Definition complp p : pred _ := [predC p].

Local Lemma complE p : complp p = subp setT p.
Proof. by apply/eqpP=> x; rewrite /subp /= andbT. Qed.

Definition pred_ctblatticeMixin := CTBLatticeMixin complE.
Canonical pred_ctblatticeType := CTBLatticeType (pred T) pred_ctblatticeMixin.
End PredSet.
End PredSet.

(* -------------------------------------------------------------------- *)
Definition subsetpP := @PredSet.leP.
Definition eqsetpP  := @PredSet.eqsetpP.
