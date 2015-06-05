(* We follow the 4CT dedekind construction of reals, but adapted to the *)
(* SSReflect hierarchy (see reals.v)                                    *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg ssrnum ssrint rat.
Require Import Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Ltac done := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Module Classical.
Parameter lpo : forall {T : countType} (P : T -> Prop),
  forall (x : T), {P x} + {~(P x)}.

Parameter pex : forall {T : countType} (P Q : T -> Prop),
  (forall (x : T), P x <-> Q x) -> P = Q.

Parameter choice : forall {T : Type} (P : T -> Prop),
  (exists x, P x) -> { x | P x }.

Parameter choiceeq : forall {T : Type} (P Q : T -> Prop),
  forall (p : exists x, P x) (q : exists x, Q x),
    (forall x, P x <-> Q x) -> tag (choice p) = tag (choice q).

Lemma dec (P : Prop): {P} + {~P}.
Proof. by case: (lpo (fun (_ : unit) => P) tt). Qed.

Lemma decT {T : Type} (P : Prop) (x y : T):
  P -> (if dec P then x else y) = x.
Proof. by case: (dec _). Qed.

Lemma decF {T : Type} (P : Prop) (x y : T):
  ~P -> (if dec P then x else y) = y.
Proof. by case: (dec _). Qed.
End Classical.

Import Classical.

(* -------------------------------------------------------------------- *)
CoInductive ratx : predArgType := RatX of (rat -> Prop).

Definition ratx_val x := let: RatX x := x in x.

Canonical ratx_subType := Eval hnf in [newType for ratx_val].

(* -------------------------------------------------------------------- *)
Fact ratx_key : unit. Proof. by []. Qed.
Definition ratx_of_pred    k := locked_with k RatX.
Canonical  ratx_unlockable k := [unlockable fun ratx_of_pred k].

Definition pred_of_ratx X q := ratx_val X q.

Coercion pred_of_ratx : ratx >-> Funclass.

(* -------------------------------------------------------------------- *)
Definition eqrx (X1 X2 : ratx) :=
  if dec (forall q, X1 q <-> X2 q) then true else false.

Lemma eqrxP X1 X2 : reflect (X1 = X2) (eqrx X1 X2).
Proof.
apply: (iffP idP)=> [|<-]; last by rewrite /eqrx decT.
rewrite /eqrx; case: (dec _)=> //= eqv h.
by case: X1 X2 eqv => [X1] [X2] /= eqv; rewrite (@pex _ X1 X2).
Qed.

Definition ratx_eqMixin := EqMixin eqrxP.
Canonical  ratx_eqType  := Eval hnf in EqType ratx ratx_eqMixin.

(* -------------------------------------------------------------------- *)
Lemma ratx_choiceMixin: choiceMixin ratx.
Proof.
pose find (P : pred ratx) (_ : nat) : option ratx :=
  if   dec (exists x, P x) is left h
  then (Some (tag (choice h)))
  else None;
exists find=> [P n r|P|P Q] /=.
+ by rewrite /find; case: (dec _)=> // h [<-]; case: (choice h).
+ by move=> h; exists 0; rewrite /find; case: (dec _).
move=> eqPQ n; rewrite /find; case: (dec _)=> hP; last first.
  case: (dec _)=> //; case=> q hQq; absurd False=> //.
  by apply/hP; exists q; rewrite eqPQ.
case: (dec _)=> [hQ|].
  by rewrite (choiceeq hP hQ) // => x; rewrite eqPQ.
move=> hQ; absurd False=> //; apply/hQ; case: hP.
by move=> x Px; exists x; rewrite -eqPQ.
Qed.

Canonical ratx_choiceType := Eval hnf in ChoiceType ratx ratx_choiceMixin.

(* -------------------------------------------------------------------- *)
CoInductive is_cut (X : rat -> Prop) : Prop :=
  IsCut (ub : exists a, X a)
        (lb : exists a, ~ X a)
        (filter : forall a b, X a -> (a < b)%R -> X b)
        (open : forall a, X a -> exists2 b, X b & (b < a)%R).

Definition is_cutb (X : rat -> Prop) :=
  if dec (is_cut X) then true else false.

CoInductive cut : predArgType := Cut (ltc : ratx) of is_cutb ltc.

Coercion ltc x := let: Cut ltc_x _ := x in ltc_x.

Canonical cut_subType := Eval hnf in [subType for ltc].

(* -------------------------------------------------------------------- *)
Definition cut_eqMixin := Eval hnf in [eqMixin of cut by <:].
Canonical  cut_eqType  := Eval hnf in EqType cut cut_eqMixin.

(* -------------------------------------------------------------------- *)
Definition cut_choiceMixin := [choiceMixin of cut by <:].
Canonical  cut_choiceType  := Eval hnf in ChoiceType cut cut_choiceMixin.
