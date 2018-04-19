(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* Quoting Coq'standard library:
"This file provides classical logic and indefinite description under
the form of Hilbert's epsilon operator":

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A->Prop),
    (exists x, P x) -> { x : A | P x }

In fact it also derives the consequences of this axiom, which include
informative excluded middle, choice, etc.                               *)
Require Import ClassicalEpsilon.

(* We also want functional extensionality *)
Require Import FunctionalExtensionality.

(* We also want propositional extensionality *)
Require Import PropExtensionality PropExtensionalityFacts.

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FunctionalExtensionality PropExtensionality.
Require Import ClassicalEpsilon.

(* -------------------------------------------------------------------- *)
(* Functional extensionality *)

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. exact: functional_extensionality. Qed.

(* -------------------------------------------------------------------- *)
(* Propositional extensionality *)

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof.
apply: propositional_extensionality; split => [-> // |].
exact: propositional_extensionality.
Qed.

Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

Lemma funeq2E {T U V : Type} (f g : T -> U -> V) : (f = g) = (f =2 g).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite funeqE.
Qed.

Lemma funeq3E {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) = (forall x y z, f x y z = g x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> x y; rewrite funeqE.
Qed.

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
Qed.

Lemma predeq2E {T U} (P Q : T -> U -> Prop) :
   (P = Q) = (forall x y, P x y <-> Q x y).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> ??; rewrite propeqE.
Qed.

Lemma predeq3E {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) = (forall x y z, P x y z <-> Q x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq3E=> ???; rewrite propeqE.
Qed.

Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Lemma notb (b : bool) : (~ b) = ~~ b.
Proof. apply: reflect_eq; exact: negP. Qed.


(* -------------------------------------------------------------------- *)
(* Informative excluded middle *)

Lemma pselect (P : Prop) : {P} + {~P}.
Proof. exact: excluded_middle_informative P. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

Definition asbool (P : Prop) :=
  if pselect P then true else false.

Notation "[ P 'as' 'bool' ]" := (asbool P)
  (at level 0, format "[ P  'as'  'bool' ]") : bool_scope.

Lemma asboolE (P : Prop) : [P as bool] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

Lemma asboolP (P : Prop) : reflect P [P as bool].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ [P as bool]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolW (P : Prop) : [P as bool] -> P.
Proof. by case: asboolP. Qed.

Lemma asboolT (P : Prop) : P -> [P as bool].
Proof. by case: asboolP. Qed.

Lemma asboolF (P : Prop) : ~ P -> [P as bool] = false.
Proof. by apply/introF/asboolP. Qed.

Lemma is_true_inj : injective is_true.
Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed.

Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> [P as bool] = [Q as bool].
Proof. by rewrite -propeqE => ->. Qed.

Lemma asbool_eq_equiv {P Q : Prop} : [P as bool] = [Q as bool] -> (P <-> Q).
Proof.
by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP.
Qed.

(* -------------------------------------------------------------------- *)
(* Reflection (and boolean equality) lemmas *)

Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) ([P as bool] && [Q as bool]).
Proof.
apply: (iffP idP); first by case/andP=> /asboolP hP /asboolP hQ.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) ([P as bool] || [Q as bool]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma asbool_neg {P : Prop} : [~ P as bool] = ~~ [P as bool].
Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed.

Lemma asbool_or {P Q : Prop} : [P \/ Q as bool] = [P as bool] || [Q as bool].
Proof.
apply/idP/idP; first by move=> /asboolW/or_asboolP.
move/or_asboolP; exact: asboolT.
Qed.

Lemma asbool_and {P Q : Prop} : [P /\ Q as bool] = [P as bool] && [Q as bool].
Proof.
apply/idP/idP; first by move=> /asboolW/and_asboolP.
move/and_asboolP; exact: asboolT.
Qed.


Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) ([P as bool] ==> [Q as bool]).
Proof.
apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|].
by move=> PQ /asboolP/PQ/asboolT.
Qed.

Lemma asbool_imply {P Q : Prop} : [P -> Q as bool] = [P as bool] ==> [Q as bool].
Proof.
apply/idP/idP; first by move/asboolW=> /imply_asboolP.
move/imply_asboolP; exact: asboolT.
Qed.


Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ [P -> Q as bool]).
Proof.
by rewrite asbool_imply negb_imply -asbool_neg; apply: (iffP idP) => /and_asboolP.
Qed.

Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, [P x as bool]) ([forall x, P x as bool]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, [P x as bool]) ([exists x, P x as bool]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.


(* -------------------------------------------------------------------- *)
Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof.
move=> cb /asboolPn nb; apply/asboolPn.
by apply: contra nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNN := contra.

Lemma contrapL (Q P : Prop) : (Q -> ~ P) -> P -> ~ Q.
Proof.
move=> cb /asboolP hb; apply/asboolPn.
by apply: contraL hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTN := contrapL.

Lemma contrapR (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof.
move=> cb /asboolPn nb; apply/asboolP.
by apply: contraR nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNT := contrapR.

Lemma contrapLR (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof.
move=> cb /asboolP hb; apply/asboolP.
by apply: contraLR hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTT := contrapLR.

Lemma contrapT P : ~ ~ P -> P.
Proof.
by move/asboolPn=> nnb; apply/asboolP; apply: contraR nnb => /asboolPn /asboolP.
Qed.

Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by move=> ?; case: (pselect P). Qed.

Lemma notT (P : Prop) : P = False -> ~ P. Proof. by move->. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False.
Proof. by move=> nP; rewrite propeqE; split. Qed.

Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof.
move=> P; rewrite propeqE; split; first exact: contrapT.
by move=> ? ?.
Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.

Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

(* -------------------------------------------------------------------- *)

Lemma not_forall {T} (P : T -> Prop) : (~ forall x, P x) = exists y, ~ P y.
Proof.
rewrite propeqE; split; last by case=> x Px allP; apply: Px.
by apply: contrapR=> /contrapR nexP x; apply: nexP => nPx; exists x.
Qed.

Lemma not_forallN  {T} (P : T -> Prop) : (~ forall x, ~ P x) = exists y, P y.
Proof. rewrite not_forall; apply: eq_exists => x; exact: notK. Qed.

Lemma not_exists {T} (P : T -> Prop) : (~ exists x, P x) = forall x, ~ P x.
Proof.
by apply: notLR; rewrite not_forall; apply: eq_exists => x; rewrite notK.
Qed.

Lemma not_existsN {T} (P : T -> Prop) : (~ exists x, ~ P x) = forall x, P x.
Proof. by apply: notLR; rewrite not_forall; apply: eq_exists=> x. Qed.

Lemma not_exists2 {T} (P Q : T -> Prop) :
  (~ exists2 x, P x & Q x) = forall x, P x -> ~ Q x.
Proof.
apply: notLR; rewrite not_forall; rewrite propeqE; split; case=> x.
  by move=> Px Qx; exists x; apply: contrapL Qx; apply.
move=> hx; exists x; first exact: contrapR hx.
exact: contrapR hx.
Qed.

(* -------------------------------------------------------------------- *)
(* Any type can be equipped with a choiceType structure.*)


Section GenericChoice.

Variable T : Type.


(* Didn't find this one??? *)
Fact eq_imply b1 b2 : (b1 ==> b2) && (b2 ==> b1) = (b1 == b2).
Proof. by case: b1; case: b2. Qed.

Fact Peps (P : pred T) (i1 i2 : inhabited T) :
  P (epsilon i1 P) = P (epsilon i2 P).
Proof.
suff {i1 i2} hi x1 x2: P (epsilon x1 P) -> P  (epsilon x2 P).
  apply/eqP; rewrite -eq_imply; apply/andP; split; apply/implyP; exact: hi.
by move=> P1; rewrite (epsilon_inh_irrelevance _ x1) //; exists (epsilon x1 P).
Qed.

Definition gen_pick (P : pred T) (_ : nat) :=
  if (pselect (inhabited T)) is left inhT then
    let x := epsilon inhT P in
    if P x then Some x else None
  else None.

Fact gen_pick_inhab P n (i : inhabited T) :
  gen_pick P n = let x := epsilon i P in if P x then Some x else None.
Proof.
rewrite /gen_pick; case: (pselect _) => p //; rewrite !(Peps _ p i).
case: ifP=> // Pei; rewrite (epsilon_inh_irrelevance _ i) //.
by exists (epsilon i P).
Qed.

Fact gen_pick_some P n x : gen_pick P n = Some x -> P x.
Proof.
by rewrite /gen_pick; case: (pselect _) => p //; case: ifP=> // Px [<-].
Qed.

(* epsilon : forall A : Type, inhabited A -> (A -> Prop) -> A
Why not just epsilon: forall A : Type, A -> (A -> Prop) -> A ?
or may be epsilon: forall A : Type, (A -> Prop), A -> A ?*)

Fact gen_pick_ex (P : pred T) :
  (exists x : T, P x) -> exists n, gen_pick P n.
Proof.
move=> exP; case: (exP) => x Px; exists 0.
have inhT : inhabited T := inhabits x.
have Peps: P (epsilon inhT P) := (epsilon_spec inhT _ exP).
rewrite /gen_pick; case: (pselect _) => p //; case: ifP=> //.
by rewrite -(epsilon_inh_irrelevance inhT) // Peps.
Qed.


Fact gen_pick_ext (P Q : pred T) : P =1 Q -> gen_pick P =1 gen_pick Q.
Proof.
move=> PEQ n; rewrite /gen_pick; case: (pselect _) => p //.
set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

Definition T_choiceMixin : choiceMixin T :=
  Choice.Mixin gen_pick_some gen_pick_ex gen_pick_ext.

End GenericChoice.
