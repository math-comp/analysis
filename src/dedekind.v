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
CoInductive is_cut (X : rat -> Prop) : Prop :=
  IsCut (ub : exists a, X a)
        (lb : exists a, ~ X a)
        (filter : forall a b, X a -> (a < b)%R -> X b)
        (open : forall a, X a -> exists2 b, X b & (b < a)%R).

Definition is_cutb (X : rat -> Prop) :=
  if dec (is_cut X) then true else false.

CoInductive cut := Cut (ltc : ratx) of is_cutb ltc.

Coercion ltc x := let: Cut ltc_x _ := x in ltc_x.

Canonical cut_subType := Eval hnf in [subType for ltc].

(* -------------------------------------------------------------------- *)
Definition cut_eqMixin := Eval hnf in [eqMixin of cut by <:].
Canonical  cut_eqType  := Eval hnf in EqType cut cut_eqMixin.
