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

Delimit Scope real_scope with RR.

Local Open Scope real_scope.

(* -------------------------------------------------------------------- *)
Implicit Types a b c : rat.

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

Lemma classical (P : Prop): P \/ ~P.
Proof. by case: (dec P). Qed.
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

Lemma is_cutP X : reflect (is_cut X) (is_cutb X).
Proof. by rewrite /is_cutb; case: (dec _)=> /= h; constructor. Qed.

CoInductive cut : predArgType := Cut (ratx : ratx) of is_cutb ratx.

Coercion cut_val x := let: Cut x _ := x in x.

Canonical cut_subType := Eval hnf in [subType for cut_val].

Definition mkcut (X : rat -> Prop) (h : is_cut X) :=
  @Cut (RatX X) (introT (is_cutP X) h).

(* -------------------------------------------------------------------- *)
Definition cut_eqMixin := Eval hnf in [eqMixin of cut by <:].
Canonical  cut_eqType  := Eval hnf in EqType cut cut_eqMixin.

(* -------------------------------------------------------------------- *)
Definition cut_choiceMixin := [choiceMixin of cut by <:].
Canonical  cut_choiceType  := Eval hnf in ChoiceType cut cut_choiceMixin.

(* -------------------------------------------------------------------- *)
Implicit Types x y : cut.

Bind Scope real_scope with cut.

Lemma cutW (P : cut -> Prop):
     (forall (E : rat -> Prop) (h : is_cutb (RatX E)), is_cut E -> P (Cut h))
  -> forall x, P x.
Proof. by move=> ih [[x] h]; apply/ih/is_cutP. Qed.

(* -------------------------------------------------------------------- *)
Definition ltc (c : cut) (a : rat) := nosimpl (c a).

Local Notation "x < a"  := (ltc x a) : real_scope.
Local Notation "x >= b" := (~ ltc x b) : real_scope.

Lemma ltcE X (h : is_cutb (RatX X)) a : (Cut h < a) = X a.
Proof. by []. Qed.

Lemma ltcP x a : x < a \/ x >= a.
Proof. by case: (lpo x a). Qed.

Lemma cut_ub x : exists a, x < a.
Proof. by elim/cutW: x => x h []. Qed.

Lemma cut_lb x : exists b, x >= b.
Proof. by elim/cutW: x => x h []. Qed.

Lemma ltc_trans x a b : x < a -> (a < b)%R -> x < b.
Proof. by elim/cutW: x a b => x h []. Qed.

Lemma open x a : x < a -> exists2 b, x < b & (b < a)%R.
Proof. by elim/cutW: x a => x h []. Qed.

Lemma ltc_le_trans x a b : x < a -> (a <= b)%R -> x < b.
Proof. by rewrite ler_eqVlt => ltxa /predU1P[<-//| /(ltc_trans ltxa)]. Qed.

Lemma gec_lt_trans a x b : x >= a -> x < b -> (a < b)%R.
Proof. by case: ltrP => // /ltc_le_trans-leba leax /leba. Qed.

Lemma le_gec_trans a b x : (a <= b)%R -> x >= b -> x >= a.
Proof. by move=> leab lebx ltxa; apply: lebx (ltc_le_trans ltxa leab). Qed.

Lemma lt_gec_trans a b x : (a < b)%R -> x >= b -> x >= a.
Proof. by move/ltrW; apply: le_gec_trans. Qed.

(* -------------------------------------------------------------------- *)
Definition leR x y := forall a, y < a -> x < a.

Local Notation "x <= y" := (leR x y) : real_scope.

Lemma leR_ltc_trans x y a : x <= y -> y < a -> x < a.
Proof. exact. Qed.

Lemma gec_leR_trans a x y : x >= a -> x <= y -> y >= a.
Proof. by move=> leax lexy /lexy. Qed.

Lemma leR_trans x y z : x <= y -> y <= z -> x <= z.
Proof. by move=> le_xy le_yz a /le_yz/le_xy. Qed.

(* -------------------------------------------------------------------- *)
Fact lt_is_cut a : is_cut (Num.lt a).
Proof.
split=> [||b c /ltr_trans| b /midf_lt[ltac ltcb]]; last 2 [exact].
- by exists (a + 1)%R; rewrite ltr_addl.
- by exists a; rewrite ltrr.
by exists ((a + b) / 2%:R)%R.
Qed.

Local Coercion ratR a := mkcut (lt_is_cut a).

Local Notation "0" := (ratR 0) : real_scope.
Local Notation "1" := (ratR 1) : real_scope.

(* -------------------------------------------------------------------- *)
Definition has E := exists x, E x.

Definition ub E z := forall y, E y -> y <= z.

Definition down E x := exists2 y, E y & x <= y.

Definition has_sup E := has E /\ has (ub E).

Definition lt_sup E a := exists2 b, forall x, E x -> x < b & b < a.

Fact sup_is_cut E : is_cut (fun a => IF has_sup E then lt_sup E a else 0 < a).
Proof.
split=> [||a b ltEa ltab| a].
- have [supE|] := classical (has_sup E); last by exists 1%R; right.
  have [_ [x ubEx]] := supE; have [a /open[b ltab ltbx]] := cut_ub x.
  by exists a; left; split; last by exists b => // y /ubEx/leR_ltc_trans; apply.
- have [supE|] := classical (has_sup E); last by exists 0%R => -[][].
  have [[y Ey] _] := supE; have [a leay] := cut_lb y.
  by exists a => -[][] // _ [b ltEb /lt_gec_trans/(_ leay)[]]; apply: ltEb.
- case: ltEa => -[supE ltEa]; last by right; rewrite ltcE (ltr_trans ltEa).
  by have [c] := ltEa; left; split=> //; exists c; last apply: ltr_trans ltab.
case=> -[supE]  => [supEa | /open[c]]; last by exists c; first right.
have [c ltEc /open[b ltcb ltba]] := supEa.
by exists b; first by left; split; last exists c.
Qed.

Definition sup E := mkcut (sup_is_cut E).
