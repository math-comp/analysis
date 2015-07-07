(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype.
Require Import Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Ltac done := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Definition classical := forall P, P \/ ~P.

(* -------------------------------------------------------------------- *)
Module Classical.
Implicit Types P Q : Prop.

Lemma contra P Q : classical -> (~Q -> ~P) -> P -> Q.
Proof. by move=> lem ??; case: (lem Q). Qed.
End Classical.

(*--------------------------------------------------------------------- *)
Section Props.
Variable A B C : Prop.

Lemma orpC : A \/ B <-> B \/ A.                   Proof. by []. Qed.
Lemma orpA : A \/ (B \/ C) <-> (A \/ B) \/ C.     Proof. by []. Qed.
Lemma orpF : (A \/ False) <-> A.                  Proof. by []. Qed.
Lemma orFp : (False \/ A) <-> A.                  Proof. by []. Qed.
Lemma orpT : (A \/ True) <-> True.                Proof. by []. Qed.
Lemma orTp : (True \/ A) <-> True.                Proof. by []. Qed.
Lemma orpp : (A \/ A) <-> A.                      Proof. by []. Qed.

Lemma andpC : A /\ B <-> B /\ A.                  Proof. by []. Qed.
Lemma andpA : A /\ (B /\ C) <-> (A /\ B) /\ C.    Proof. by []. Qed.
Lemma andpF : (A /\ False) <-> False.             Proof. by []. Qed.
Lemma andFp : (False /\ A) <-> False.             Proof. by []. Qed.
Lemma andpT : (A /\ True) <-> A.                  Proof. by []. Qed.
Lemma andTp : (True /\ A) <-> A.                  Proof. by []. Qed.
Lemma andpp : (A /\ A) <-> A.                     Proof. by []. Qed.

Lemma andp_orr : A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C). Proof. by []. Qed.
Lemma andp_orl : (B \/ C) /\ A <-> (B /\ A) \/ (C /\ A). Proof. by []. Qed.
Lemma orp_andr : A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C). Proof. by []. Qed.
Lemma orp_andl : (B /\ C) \/ A <-> (B \/ A) /\ (C \/ A). Proof. by []. Qed.

Lemma andpK : A /\ B \/ A   <-> A.  Proof. by []. Qed.
Lemma andKp : A \/ B /\ A   <-> A.  Proof. by []. Qed.
Lemma orpK  : (A \/ B) /\ A <-> A.  Proof. by []. Qed.
Lemma orKp  : A /\ (B \/ A) <-> A.  Proof. by []. Qed.

Lemma andp_idl : (B -> A) -> (A /\ B <-> B).
Proof. by []. Qed.
Lemma andp_idr : (A -> B) -> (A /\ B <-> A).
Proof. by []. Qed.
Lemma andp_id2l : (A -> (B <-> C)) -> (A /\ B <-> A /\ C).
Proof. by []. Qed.
Lemma andp_id2r : (B -> (A <-> C)) -> (A /\ B <-> C /\ B).
Proof. by []. Qed.

Lemma orp_idl : (A -> B) -> (A \/ B <-> B).
Proof. by []. Qed.
Lemma orp_idr : (B -> A) -> (A \/ B <-> A).
Proof. by []. Qed.
Lemma orp_id2l : (B <-> C) -> (A \/ B <-> A \/ C).
Proof. by []. Qed.
Lemma orp_id2r : (B <-> C) -> (A \/ B <-> A \/ C).
Proof. by []. Qed.

Section Classical.
Hypothesis lem : classical.

Lemma negpK P : ~ ~ P <-> P.
Proof. by case/(_ P): lem. Qed.

Lemma negp_or : ~ (A \/ B) <-> (~A /\ ~B).
Proof. by case/(_ A): lem. Qed.

Lemma negp_and : ~ (A /\ B) <-> (~A \/ ~B).
Proof. by case/(_ A): lem. Qed.

Lemma negp_forall {T} (P : T -> Prop) :
  ~ (forall x, P x) <-> (exists x, ~ P x).
Proof.
split; [move=> NPx; apply/negpK=> NEx | by case].
by apply/NPx=> x; apply/negpK=> Px; apply/NEx; exists x.
Qed.

Lemma negp_exists {T} (P : T -> Prop) :
  ~ (exists x, P x) <-> (forall x, ~ P x).
Proof. by split=> [NEx x Px|NPx [] //]; apply/NEx; exists x. Qed.

Lemma negp_existsN {T} (P : T -> Prop) :
  ~(exists x, ~ P x) <-> (forall x, P x).
Proof. by rewrite negp_exists; split=> // h x; apply/negpK. Qed.

Lemma negp_forallN {T} (P : T -> Prop) :
  ~(forall x, ~ P x) <-> (exists x, P x).
Proof.
rewrite negp_forall; split; case=> x Px.
  by exists x; apply/negpK. by exists x.
Qed.
End Classical.
End Props.
