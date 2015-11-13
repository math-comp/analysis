(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Record mclassic := {
  _ : forall (P : Prop), {P}+{~P};
  _ : forall (P : Prop), P = True \/ P = False
}.

Axiom classic : mclassic.

(* -------------------------------------------------------------------- *)
Lemma pselect (P : Prop): {P}+{~P}.
Proof. by case classic. Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by case classic. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

(* -------------------------------------------------------------------- *)
Definition asbool (P : Prop) :=
  if pselect P then true else false.

Lemma asboolP (P : Prop): reflect P (asbool P).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolE (P : Prop) : asbool P -> P.
Proof. by case: asboolP. Qed.

(* -------------------------------------------------------------------- *)
Inductive box := Box of bool.

Bind    Scope box_scope with box.
Delimit Scope box_scope with P.

Definition idbox {T : Type} (B : box) :=
  fun (x : T) => B.

Definition unbox {T : Type} (B : T -> box) : bool := 
  asbool (forall x : T, let: Box b := B x in b).

Notation ", F" := (Box F) (at level 200, format ", '/ '  F") : box_scope.

Notation "[ x | B ]" := (unbox (fun x => idbox B x)) (at level 0, x ident).
Notation "[ x : T | B ]" := (unbox (fun (x : T) => idbox B x)) (at level 0, x ident).

Notation "[ 'box' x B ]" := [x | B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'box'  x B ] ']'") : bool_scope.

Notation "[ 'box' x : T B ]" := [x : T | B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.

Notation ", 'box' x B" := (Box [x | B])
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'box'  x B") : box_scope.

Notation ", 'box' x : T B" := (Box [x : T | B])
  (at level 200, x at level 99, B at level 200, only parsing) : box_scope.

Lemma boxP {T : Type} (P : pred T):
  reflect (forall x, P x) [box x : T, P x].
Proof. by apply: (iffP idP) => /asboolP. Qed.
