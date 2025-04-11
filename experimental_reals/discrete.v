(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From Corelib Require Setoid.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp Require Import xfinmap reals.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope real_scope.

Section ProofIrrelevantChoice.
Context {T : choiceType}.

Lemma existsTP (P : T -> Prop) : { x : T | P x } + (forall x, ~ P x).
Proof.
case: (boolP `[<exists x : T, P x>]) => [/exists_asboolP | /asboolPn] h.
  by case/cid: h => w Pw; left; exists w; apply/asboolP.
by right=> x Px; apply/h; exists x.
Qed.

End ProofIrrelevantChoice.

(* -------------------------------------------------------------------- *)
Section PredSubtype.
Section Def.
Variable T : Type.
Variable E : pred T.

Record pred_sub : Type :=
  PSubSub { rsval :> T; rsvalP : rsval \in E }.

HB.instance Definition _ := [isSub for rsval].
End Def.

HB.instance Definition _ (T : eqType) (E : pred T) :=
  [Equality of pred_sub E by <:].

HB.instance Definition _ (T : choiceType) (E : pred T) :=
  [Choice of pred_sub E by <:].

HB.instance Definition _ (T : countType) (E : pred T) :=
  [Countable of pred_sub E by <:].
End PredSubtype.

Notation "[ 'psub' E ]" := (@pred_sub _ E)
  (format "[ 'psub'  E ]").

(* -------------------------------------------------------------------- *)
Section PIncl.
Variables (T : Type) (E F : pred T) (le : {subset E <= F}).

Definition pincl (x : [psub E]) : [psub F] :=
  PSubSub (le (valP x)).
End PIncl.

(* -------------------------------------------------------------------- *)
Section Countable.
Variable (T : Type) (E : pred T).

Variant countable : Type :=
  Countable
    (rpickle : [psub E] -> nat)
    (runpickle : nat -> option [psub E])
    of pcancel rpickle runpickle.

Definition rpickle (c : countable) :=
  let: Countable p _ _ := c in p.

Definition runpickle (c : countable) :=
  let: Countable _ p _ := c in p.

Lemma rpickleK c: pcancel (rpickle c) (runpickle c).
Proof. by case: c. Qed.
End Countable.

(* -------------------------------------------------------------------- *)
Section CountableTheory.
Lemma countable_countable (T : countType) (E : pred T) : countable E.
Proof. by exists choice.pickle choice.unpickle; apply/choice.pickleK. Qed.

Section CanCountable.
Variables (T : Type) (U : countType) (E : pred T).
Variables (f : [psub E] -> U) (g : U -> [psub E]).

Lemma can_countable : cancel f g -> countable E.
Proof.
pose p := choice.pickle \o f; pose u n := omap g (choice.unpickle n).
move=> can_fg; apply (@Countable _ E p u) => x.
by rewrite {}/u {}/p /= choice.pickleK /= can_fg.
Qed.
End CanCountable.

Section CountType.
Variables (T : eqType) (E : pred T) (c : countable E).

Definition countable_countMixin  := Countable.copy [psub E]
  (pcan_type (rpickleK c)).
Definition countable_choiceMixin := Choice.copy [psub E]
  (pcan_type (rpickleK c)).
End CountType.
End CountableTheory.

(* -------------------------------------------------------------------- *)
Section Finite.
Variables (T : eqType).

CoInductive finite (E : pred T) : Type :=
| Finite s of uniq s & {subset E <= s}.
End Finite.

(* -------------------------------------------------------------------- *)
Section FiniteTheory.
Context {T : choiceType}.


Lemma finiteP (E : pred T) : (exists s : seq T, {subset E <= s}) -> finite E.
Proof.
case/cid=> s sEs; exists (undup s); first by rewrite undup_uniq.
by move=> x; rewrite mem_undup; exact: sEs.
Qed.


Lemma finiteNP (E : pred T): (forall s : seq T, ~ {subset E <= s}) ->
  forall n, exists s : seq T, [/\ size s = n, uniq s & {subset s <= E}].
Proof.
move=> finN; elim=> [|n [s] [<- uq_s sE]]; first by exists [::].
have [x sxN xE]: exists2 x, x \notin s & x \in E.
  apply: contra_notP (finN (filter (mem E) s)) => /forall2NP finE x Ex.
  move/or_asboolP: (finE x).
  by rewrite !asbool_neg !asboolb negbK Ex mem_filter orbF [(mem E) x]Ex.
exists (x :: s) => /=; rewrite sxN; split=> // y.
by rewrite in_cons => /orP[/eqP->//|/sE].
Qed.

End FiniteTheory.

(* -------------------------------------------------------------------- *)
Section FiniteCountable.
Variables (T : eqType) (E : pred T).

Lemma finite_countable : finite E -> countable E.
Proof.
case=> s uqs Es; pose t := pmap (fun x => (insub x : option [psub E])) s.
pose f x := index x t; pose g i := nth None [seq Some x | x <- t] i.
apply (@Countable _ E f g) => x; rewrite {}/f {}/g /=.
have x_in_t: x \in t; first case: x => x h.
  by rewrite {}/t mem_pmap_sub /= Es.
by rewrite (nth_map x) ?index_mem ?nth_index.
Qed.
End FiniteCountable.

(* -------------------------------------------------------------------- *)
Section CountSub.
Variables (T : eqType) (E F : pred T).

Lemma countable_sub: {subset E <= F} -> countable F -> countable E.
Proof.
move=> le_EF [f g fgK]; pose f' (x : [psub E]) := f (pincl le_EF x).
pose g' x := obind (insub (sT := [psub E])) (omap val (g x)).
by exists f' g' => x; rewrite /f' /g' fgK /= valK.
Qed.
End CountSub.

(* -------------------------------------------------------------------- *)
Section CountableUnion.
Variables (T : eqType) (E : nat -> pred T).

Hypothesis cE : forall i, countable (E i).

Lemma cunion_countable : countable [pred x | `[< exists i, x \in E i >]].
Proof.
pose Ci i : countType := HB.pack [psub (E i)] (countable_countMixin (cE i)).
pose S := { i : nat & Ci i }; set F := [pred x | _].
have H: forall (x : [psub F]), exists i : nat, val x \in E i.
  by case=> x /= /asboolP[i] Eix; exists i.
have G: forall (x : S), val (tagged x) \in F.
  by case=> i [x /= Eix]; apply/asboolP; exists i.
pose f (x : [psub F]) : S := Tagged (fun i => [psub E i])
  (PSubSub (xchooseP (H x))).
pose g (x : S) := PSubSub (G x).
by have /can_countable: cancel f g by case=> x hx; apply/val_inj.
Qed.
End CountableUnion.
