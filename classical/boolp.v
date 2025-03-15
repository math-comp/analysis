(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require internal_Eqdep_dec.

(**md**************************************************************************)
(* # Classical Logic                                                          *)
(*                                                                            *)
(* This file provides the axioms of classical logic and tools to perform      *)
(* classical reasoning in the Mathematical Compnent framework. The three      *)
(* axioms are taken from the standard library of Coq, more details can be     *)
(* found in Section 5 of                                                      *)
(* - R. Affeldt, C. Cohen, D. Rouhling. Formalization Techniques for          *)
(*   Asymptotic Reasoning in Classical Analysis. JFR 2018                     *)
(*                                                                            *)
(* ## Axioms                                                                  *)
(* ```                                                                        *)
(* functional_extensionality_dep == functional extensionality (on dependently *)
(*                     typed functions), i.e., functions that are pointwise   *)
(*                     equal are equal                                        *)
(* propositional_extensionality == propositional extensionality, i.e., iff    *)
(*                     and equality are the same on Prop                      *)
(* constructive_indefinite_description == existential in Prop (ex) implies    *)
(*                     existential in Type (sig)                              *)
(*              cid := constructive_indefinite_description (shortcut)         *)
(* ```                                                                        *)
(*                                                                            *)
(* A number of properties are derived below from these axioms and are         *)
(* often more pratical to use than directly using the axioms. For instance    *)
(* propext, funext, the excluded middle (EM),...                              *)
(*                                                                            *)
(* ## Boolean View of Prop                                                    *)
(* ```                                                                        *)
(*         `[< P >] == boolean view of P : Prop, see all lemmas about asbool  *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Mathematical Components Structures                                      *)
(* ```                                                                        *)
(*  {classic T} == Endow T : Type with a canonical eqType/choiceType.         *)
(*                 This is intended for local use.                            *)
(*                 E.g., T : Type |- A : {fset {classic T}}                   *)
(*                 Alternatively one may use elim/Pchoice: T => T in H *.     *)
(*                 to substitute T with T : choiceType once and for all.      *)
(* {eclassic T} == Endow T : eqType with a canonical choiceType.              *)
(*                 On the model of {classic _}.                               *)
(*                 See also the lemmas Peq and eqPchoice.                     *)
(* ```                                                                        *)
(*                                                                            *)
(* Functions onto a porderType (resp. latticeType) are equipped with          *)
(* a porderType (resp. latticeType), so that the generic notation (_ <= _)%O  *)
(* (resp. `&`, `|`) from `order.v` can be used.                               *)
(* ```                                                                        *)
(*     FunOrder.lef f g == pointwise large inequality between two functions   *)
(*     FunOrder.ltf f g == pointwise strict inequality between two functions  *)
(* FunLattice.meetf f g == pointwise meet between two functions               *)
(* FunLattice.joinf f g == pointwise join between two functions               *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope box_scope.
Declare Scope quant_scope.

Axiom functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g.
Axiom propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.
Notation cid := constructive_indefinite_description.

Lemma cid2 (A : Type) (P Q : A -> Prop) :
  (exists2 x : A, P x & Q x) -> {x : A | P x & Q x}.
Proof.
move=> PQA; suff: {x | P x /\ Q x} by move=> [a [*]]; exists a.
by apply: cid; case: PQA => x; exists x.
Qed.

Lemma existT_inj1 (T : Type) (P : T -> Type) (x y : T) (Px : P x) (Py : P y) :
  existT P x Px = existT P y Py -> x = y.
Proof. by case. Qed.

Lemma existT_inj2 (T : eqType) (P : T -> Type) (x : T) (Px1 Px2 : P x) :
  existT P x Px1 = existT P x Px2 -> Px1 = Px2.
Proof.
apply: internal_Eqdep_dec.inj_pair2_eq_dec => y z.
by have [|/eqP] := eqVneq y z; [left|right].
Qed.

Lemma surjective_existT (T : Type) (P : T -> Type) (p : {x : T & P x}):
  existT [eta P] (projT1 p) (projT2 p) = p.
Proof. by case: p. Qed.

Record mextensionality := {
  _ : forall (P Q : Prop), (P <-> Q) -> (P = Q);
  _ : forall {T U : Type} (f g : T -> U),
        (forall x, f x = g x) -> f = g;
}.

Fact extensionality : mextensionality.
Proof.
split.
- exact: propositional_extensionality.
- by move=> T U f g; apply: functional_extensionality_dep.
Qed.

Lemma propext (P Q : Prop) : (P <-> Q) -> (P = Q).
Proof. by have [propext _] := extensionality; apply: propext. Qed.

Ltac eqProp := apply: propext; split.

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. by case: extensionality=> _; apply. Qed.

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof. by apply: propext; split=> [->|/propext]. Qed.

Lemma propeqP (P Q : Prop) : (P = Q) <-> (P <-> Q).
Proof. by rewrite propeqE. Qed.

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

Lemma funeqP {T U : Type} (f g : T -> U) : (f = g) <-> (f =1 g).
Proof. by rewrite funeqE. Qed.

Lemma funeq2P {T U V : Type} (f g : T -> U -> V) : (f = g) <-> (f =2 g).
Proof. by rewrite funeq2E. Qed.

Lemma funeq3P {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) <-> (forall x y z, f x y z = g x y z).
Proof. by rewrite funeq3E. Qed.

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

Lemma predeqP {T} (A B : T -> Prop) : (A = B) <-> (forall x, A x <-> B x).
Proof. by rewrite predeqE. Qed.

Lemma predeq2P {T U} (P Q : T -> U -> Prop) :
   (P = Q) <-> (forall x y, P x y <-> Q x y).
Proof. by rewrite predeq2E. Qed.

Lemma predeq3P {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) <-> (forall x y z, P x y z <-> Q x y z).
Proof. by rewrite predeq3E. Qed.

Lemma propT {P : Prop} : P -> P = True.
Proof. by move=> p; rewrite propeqE. Qed.

Lemma Prop_irrelevance (P : Prop) (x y : P) : x = y.
Proof. by move: x (x) y => /propT-> [] []. Qed.
#[global] Hint Resolve Prop_irrelevance : core.

Record mclassic := {
  _ : forall (P : Prop), {P} + {~P};
  _ : forall T, hasChoice T
}.

Lemma choice X Y (P : X -> Y -> Prop) :
  (forall x, exists y, P x y) -> {f & forall x, P x (f x)}.
Proof. by move=> /(_ _)/constructive_indefinite_description -/all_tag. Qed.

(* Diaconescu Theorem *)
Theorem EM P : P \/ ~ P.
Proof.
pose U val := fun Q : bool => Q = val \/ P.
have Uex val : exists b, U val b by exists val; left.
pose f val := projT1 (cid (Uex val)).
pose Uf val : U val (f val) := projT2 (cid (Uex val)).
have : f true != f false \/ P.
  have [] := (Uf true, Uf false); rewrite /U.
  by move=> [->|?] [->|?] ; do ?[by right]; left.
move=> [/eqP fTFN|]; [right=> p|by left]; apply: fTFN.
have UTF : U true = U false by rewrite predeqE /U => b; split=> _; right.
rewrite /f; move: (Uex true) (Uex false); rewrite UTF => p1 p2.
by congr (projT1 (cid _)).
Qed.

Lemma pselect (P : Prop): {P} + {~P}.
Proof.
have : exists b, if b then P else ~ P.
  by case: (EM P); [exists true|exists false].
by move=> /cid [[]]; [left|right].
Qed.

Lemma pselectT T : (T -> False) + T.
Proof.
have [/cid[]//|NT] := pselect (exists t : T, True); first by right.
by left=> t; case: NT; exists t.
Qed.

Lemma classic : mclassic.
Proof.
split=> [|T]; first exact: pselect.
exists (fun (P : pred T) (n : nat) =>
  if pselect (exists x, P x) isn't left ex then None
  else Some (projT1 (cid ex)))
  => [P n x|P [x Px]|P Q /funext -> //].
  by case: pselect => // ex [<- ]; case: cid.
by exists 0; case: pselect => // -[]; exists x.
Qed.

Lemma gen_choiceMixin (T : Type) : hasChoice T.
Proof. by case: classic. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_fun T rT (U V : T -> rT) :
  (forall x : T, U x = V x) -> (fun x => U x) = (fun x => V x).
Proof. by move=> /funext->. Qed.

Lemma eq_fun2 T1 T2 rT (U V : T1 -> T2 -> rT) :
  (forall x y, U x y = V x y) -> (fun x y => U x y) = (fun x y => V x y).
Proof. by move=> UV; rewrite funeq2E => x y; rewrite UV. Qed.

Lemma eq_fun3  T1 T2 T3 rT (U V : T1 -> T2 -> T3 -> rT) :
  (forall x y z, U x y z = V x y z) ->
  (fun x y z => U x y z) = (fun x y z => V x y z).
Proof. by move=> UV; rewrite funeq3E => x y z; rewrite UV. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_forall2 T S (U V : forall x : T, S x -> Prop) :
  (forall x y, U x y = V x y) -> (forall x y, U x y) = (forall x y, V x y).
Proof. by move=> UV; apply/eq_forall => x; apply/eq_forall. Qed.

Lemma eq_forall3 T S R (U V : forall (x : T) (y : S x), R x y -> Prop) :
  (forall x y z, U x y z = V x y z) ->
  (forall x y z, U x y z) = (forall x y z, V x y z).
Proof. by move=> UV; apply/eq_forall2 => x y; apply/eq_forall. Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma eq_exists2 T S (U V : forall x : T, S x -> Prop) :
  (forall x y, U x y = V x y) -> (exists x y, U x y) = (exists x y, V x y).
Proof. by move=> UV; apply/eq_exists => x; apply/eq_exists. Qed.

Lemma eq_exists3 T S R (U V : forall (x : T) (y : S x), R x y -> Prop) :
  (forall x y z, U x y z = V x y z) ->
  (exists x y z, U x y z) = (exists x y z, V x y z).
Proof. by move=> UV; apply/eq_exists2 => x y; apply/eq_exists. Qed.

Lemma eq_exist T (P : T -> Prop) (s t : T) (p : P s) (q : P t) :
  s = t -> exist P s p = exist P t q.
Proof. by move=> st; case: _ / st in q *; apply/congr1. Qed.

Lemma forall_swap T S (U : forall (x : T) (y : S), Prop) :
   (forall x y, U x y) = (forall y x, U x y).
Proof. by rewrite propeqE; split. Qed.

Lemma exists_swap T S (U : forall (x : T) (y : S), Prop) :
   (exists x y, U x y) = (exists y x, U x y).
Proof. by rewrite propeqE; split => -[x [y]]; exists y, x. Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Definition asbool (P : Prop) := if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

Lemma asboolP (P : Prop) : reflect P `[<P>].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

Lemma asboolb (b : bool) : `[< b >] = b.
Proof. by apply/asboolP/idP. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[<P>]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolW (P : Prop) : `[<P>] -> P.
Proof. by case: asboolP. Qed.

Lemma orW A B : A \/ B -> A + B.
Proof.
have [|NA] := asboolP A; first by left.
have [|NB] := asboolP B; first by right.
by move=> AB; exfalso; case: AB.
Qed.

Lemma or3W A B C : [\/ A, B | C] -> A + B + C.
Proof.
have [|NA] := asboolP A; first by left; left.
have [|NB] := asboolP B; first by left; right.
have [|NC] := asboolP C; first by right.
by move=> ABC; exfalso; case: ABC.
Qed.

Lemma or4W A B C D : [\/ A, B, C | D] -> A + B + C + D.
Proof.
have [|NA] := asboolP A; first by left; left; left.
have [|NB] := asboolP B; first by left; left; right.
have [|NC] := asboolP C; first by left; right.
have [|ND] := asboolP D; first by right.
by move=> ABCD; exfalso; case: ABCD.
Qed.

(* Shall this be a coercion ?*)
Lemma asboolT (P : Prop) : P -> `[<P>].
Proof. by case: asboolP. Qed.

Lemma asboolF (P : Prop) : ~ P -> `[<P>] = false.
Proof. by apply/introF/asboolP. Qed.

Lemma eq_opE (T : eqType) (x y : T) : (x == y : Prop) = (x = y).
Proof. by apply/propext; split=> /eqP. Qed.

Lemma is_true_inj : injective is_true.
Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed.

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Proof. by move=> x y; apply: (iffP (asboolP _)). Qed.
Definition gen_eqMixin (T : Type) : hasDecEq T :=
  hasDecEq.Build T (@gen_eqP T).

HB.instance Definition _ (T : Type) (T' : T -> eqType) :=
  gen_eqMixin (forall t : T, T' t).

HB.instance Definition _ (T : Type) (T' : T -> choiceType) :=
  gen_choiceMixin (forall t : T, T' t).

HB.instance Definition _ := gen_eqMixin Prop.
HB.instance Definition _ := gen_choiceMixin Prop.

Section classicType.
Variable T : Type.
Definition classicType := T.
HB.instance Definition _ := gen_eqMixin classicType.
HB.instance Definition _ := gen_choiceMixin classicType.
End classicType.
Notation "'{classic' T }" := (classicType T)
 (format "'{classic'  T }") : type_scope.

Section eclassicType.
Variable T : eqType.
Definition eclassicType : Type := T.
HB.instance Definition _ := Equality.copy eclassicType T.
HB.instance Definition _ := gen_choiceMixin eclassicType.
End eclassicType.
Notation "'{eclassic' T }" := (eclassicType T)
 (format "'{eclassic'  T }") : type_scope.

Definition canonical_of T U (sort : U -> T) := forall (G : T -> Type),
  (forall x', G (sort x')) -> forall x, G x.
Notation canonical_ sort := (@canonical_of _ _ sort).
Notation canonical T E := (@canonical_of T E id).

Lemma canon T U (sort : U -> T) :
  (forall x, exists y, sort y = x) -> canonical_ sort.
Proof. by move=> + G Gs x => /(_ x)/cid[x' <-]. Qed.
Arguments canon {T U sort} x.

Lemma Peq : canonical Type eqType.
Proof. by apply: canon => T; exists {classic T}. Qed.
Lemma Pchoice : canonical Type choiceType.
Proof. by apply: canon => T; exists {classic T}. Qed.
Lemma eqPchoice : canonical eqType choiceType.
Proof. by apply: canon => T; exists {eclassic T}; case: T => //= T [?]//. Qed.

Lemma not_True : (~ True) = False. Proof. exact/propext. Qed.
Lemma not_False : (~ False) = True. Proof. by apply/propext; split=> _. Qed.

Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[<P>] = `[<Q>].
Proof. by rewrite -propeqE => ->. Qed.

Lemma asbool_equiv_eqP {P Q : Prop} b : reflect Q b -> (P <-> Q) -> `[<P>] = b.
Proof. by move=> Q_b [PQ QP]; apply/asboolP/Q_b. Qed.

Lemma asbool_equiv {P Q : Prop} : (P <-> Q) -> (`[<P>] <-> `[<Q>]).
Proof. by move/asbool_equiv_eq->. Qed.

Lemma asbool_eq_equiv {P Q : Prop} : `[<P>] = `[<Q>] -> (P <-> Q).
Proof. by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP. Qed.

Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[< P >] && `[< Q >]).
Proof.
apply: (iffP idP); first by case/andP => /asboolP p /asboolP q.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma and3_asboolP (P Q R : Prop) :
  reflect [/\ P, Q & R] [&& `[< P >], `[< Q >] & `[< R >]].
Proof.
apply: (iffP idP); first by case/and3P => /asboolP p /asboolP q /asboolP r.
by case => /asboolP -> /asboolP -> /asboolP ->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[< P >] || `[< Q >]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma or3_asboolP (P Q R : Prop) :
  reflect [\/ P, Q | R] [|| `[< P >], `[< Q >] | `[< R >]].
Proof.
apply: (iffP idP); last by case=> [| |] /asboolP -> //=; rewrite !orbT.
by case/orP=> [/asboolP p|/orP[]/asboolP]; [exact:Or31|exact:Or32|exact:Or33].
Qed.

Lemma asbool_neg {P : Prop} : `[<~ P>] = ~~ `[<P>].
Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed.

Lemma asbool_or {P Q : Prop} : `[<P \/ Q>] = `[<P>] || `[<Q>].
Proof. exact: (asbool_equiv_eqP (or_asboolP _ _)). Qed.

Lemma asbool_and {P Q : Prop} : `[<P /\ Q>] = `[<P>] && `[<Q>].
Proof. exact: (asbool_equiv_eqP (and_asboolP _ _)). Qed.

Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[<P>] ==> `[<Q>]).
Proof.
apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|].
by move=> PQ /asboolP/PQ/asboolT.
Qed.

Lemma asbool_imply {P Q : Prop} : `[<P -> Q>] = `[<P>] ==> `[<Q>].
Proof. exact: (asbool_equiv_eqP imply_asboolP). Qed.

Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[<P -> Q>]).
Proof.
apply: (iffP idP).
by rewrite asbool_imply negb_imply -asbool_neg => /and_asboolP.
by move/and_asboolP; rewrite asbool_neg -negb_imply asbool_imply.
Qed.

Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[<P x>]) (`[<forall x, P x>]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[<P x>]) (`[<exists x, P x>]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)

Variant BoolProp : Prop -> Type :=
 | TrueProp : BoolProp True
 | FalseProp : BoolProp False.

Lemma PropB P : BoolProp P.
Proof. by case: (asboolP P) => [/propT-> | /propF->]; [left | right]. Qed.

Lemma notB : ((~ True) = False) * ((~ False) = True).
Proof. by rewrite /not; split; eqProp. Qed.

Lemma andB : left_id True and * right_id True and
          * (left_zero False and * right_zero False and * idempotent and).
Proof. by do ![split] => /PropB[]; eqProp=> // -[]. Qed.

Lemma orB : left_id False or * right_id False or
          * (left_zero True or * right_zero True or * idempotent or).
Proof. do ![split] => /PropB[]; eqProp=> -[] //; by [left | right]. Qed.

Lemma implyB : let imply (P Q : Prop) :=  P -> Q in
    (imply False =1 fun=> True) * (imply^~ False =1 not)
  * (left_id True imply * right_zero True imply * self_inverse True imply).
Proof. by do ![split] => /PropB[]; eqProp=> //; apply. Qed.

Lemma decide_or P Q : P \/ Q -> {P} + {Q}.
Proof. by case/PropB: P; [left | rewrite orB; right]. Qed.

(* -------------------------------------------------------------------- *)

Lemma notT (P : Prop) : P = False -> ~ P.
Proof. by move->. Qed.

Lemma contrapT P : ~ ~ P -> P.
Proof. by case: (PropB P) => //; rewrite not_False. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False. Proof. by case: (PropB P). Qed.

Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. by move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof. by case/PropB; rewrite !(not_False,not_True). Qed.

Lemma contra_notP (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof. by move: Q P => /PropB[] /PropB[]. Qed.

Lemma contraPP (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof. by move: Q P => /PropB[] /PropB[]//; rewrite not_False not_True. Qed.

Lemma contra_notT b (P : Prop) : (~~ b -> P) -> ~ P -> b.
Proof. by move=> bP; apply: contra_notP => /negP. Qed.

Lemma contraPT (P : Prop) b : (~~ b -> ~ P) -> P -> b.
Proof. by move=> /contra_notT; rewrite notK. Qed.

Lemma contraTP b (Q : Prop) : (~ Q -> ~~ b) -> b -> Q.
Proof. by move=> QB; apply: contraPP => /QB/negP. Qed.

Lemma contraNP (P : Prop) (b : bool) : (~ P -> b) -> ~~ b -> P.
Proof. by move=> /contra_notP + /negP => /[apply]. Qed.

Lemma contra_neqP (T : eqType) (x y : T) P : (~ P -> x = y) -> x != y -> P.
Proof. by move=> Pxy; apply: contraNP => /Pxy/eqP. Qed.

Lemma contra_eqP (T : eqType) (x y : T) Q : (~ Q -> x != y) -> x = y -> Q.
Proof. by move=> Qxy /eqP; apply: contraTP. Qed.

Lemma contra_leP {disp1} {T1 : porderType disp1} [P : Prop] [x y : T1] :
  (~ P -> (x < y)%O) -> (y <= x)%O -> P.
Proof.
move=> Pxy yx; apply/asboolP.
by apply: Order.POrderTheory.contra_leT yx => /asboolPn.
Qed.

Lemma contra_ltP {disp1} {T1 : porderType disp1} [P : Prop] [x y : T1] :
  (~ P -> (x <= y)%O) -> (y < x)%O -> P.
Proof.
move=> Pxy yx; apply/asboolP.
by apply: Order.POrderTheory.contra_ltT yx => /asboolPn.
Qed.

Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by case: (PropB P); exact. Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.

Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

Lemma iff_notr (P Q : Prop) : (P <-> ~ Q) <-> (~ P <-> Q).
Proof. by split=> [/propext ->|/propext <-]; rewrite notK. Qed.

Lemma iff_not2 (P Q : Prop) : (~ P <-> ~ Q) <-> (P <-> Q).
Proof. by split=> [/iff_notr|PQ]; [|apply/iff_notr]; rewrite notK. Qed.

(* assia : let's see if we need the simplpred machinery. In any case, we sould
   first try definitions + appropriate Arguments setting to see whether these
   can replace the canonical structures machinery. *)

Definition predp T := T -> Prop.

Identity Coercion fun_of_pred : predp >-> Funclass.

Definition relp T := T -> predp T.

Identity Coercion fun_of_rel : rel >-> Funclass.

Notation xpredp0 := (fun _ => False).
Notation xpredpT := (fun _ => True).
Notation xpredpI := (fun (p1 p2 : predp _) x => p1 x /\ p2 x).
Notation xpredpU := (fun (p1 p2 : predp _) x => p1 x \/ p2 x).
Notation xpredpC := (fun (p : predp _) x => ~ p x).
Notation xpredpD := (fun (p1 p2 : predp _) x => ~ p2 x /\ p1 x).
Notation xpreimp := (fun f (p : predp _) x => p (f x)).
Notation xrelpU := (fun (r1 r2 : relp _) x y => r1 x y \/ r2 x y).

Definition pred0p (T : Type) (P : predp T) : bool := `[<P =1 xpredp0>].
Prenex Implicits pred0p.

Lemma pred0pP  (T : Type) (P : predp T) : reflect (P =1 xpredp0) (pred0p P).
Proof. by apply: (iffP (asboolP _)). Qed.

Lemma forallp_asboolPn {T} {P : T -> Prop} :
  reflect (forall x : T, ~ P x) (~~ `[<exists x : T, P x>]).
Proof.
apply: (iffP idP)=> [/asboolPn NP x Px|NP].
by apply/NP; exists x. by apply/asboolP=> -[x]; apply/NP.
Qed.

Lemma existsp_asboolPn {T} {P : T -> Prop} :
  reflect (exists x : T, ~ P x) (~~ `[<forall x : T, P x>]).
Proof.
apply: (iffP idP); last by case=> x NPx; apply/asboolPn=> /(_ x).
move/asboolPn=> NP; apply/asboolP/negbNE/asboolPn=> h.
by apply/NP=> x; apply/asboolP/negbNE/asboolPn=> NPx; apply/h; exists x.
Qed.

Lemma asbool_forallNb {T : Type} (P : pred T) :
  `[< forall x : T, ~~ (P x) >] = ~~ `[< exists x : T, P x >].
Proof.
apply: (asbool_equiv_eqP forallp_asboolPn);
  by split=> h x; apply/negP/h.
Qed.

Lemma asbool_existsNb {T : Type} (P : pred T) :
  `[< exists x : T, ~~ (P x) >] = ~~ `[< forall x : T, P x >].
Proof.
apply: (asbool_equiv_eqP existsp_asboolPn);
  by split=> -[x h]; exists x; apply/negP.
Qed.

Lemma not_implyP (P Q : Prop) : ~ (P -> Q) <-> P /\ ~ Q.
Proof.
split=> [/asboolP|[p nq pq]]; [|exact/nq/pq].
by rewrite asbool_neg => /imply_asboolPn.
Qed.

Lemma not_andE (P Q : Prop) : (~ (P /\ Q)) = ~ P \/ ~ Q.
Proof.
eqProp=> [/asboolPn|[|]]; try by apply: contra_not => -[].
by rewrite asbool_and negb_and => /orP[]/asboolPn; [left|right].
Qed.

Lemma not_andP (P Q : Prop) : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof. by rewrite not_andE. Qed.

Lemma not_and3P (P Q R : Prop) : ~ [/\ P, Q & R] <-> [\/ ~ P, ~ Q | ~ R].
Proof.
split=> [/and3_asboolP|/or3_asboolP].
by rewrite 2!negb_and -3!asbool_neg => /or3_asboolP.
by rewrite 3!asbool_neg -2!negb_and => /and3_asboolP.
Qed.

Lemma notP (P : Prop) : ~ ~ P <-> P.
Proof. by split => [|p]; [exact: contrapT|exact]. Qed.

Lemma notE (P : Prop) : (~ ~ P) = P. Proof. by rewrite propeqE notP. Qed.

Lemma not_orE (P Q : Prop) : (~ (P \/ Q)) = ~ P /\ ~ Q.
Proof. by rewrite -[_ /\ _]notE not_andE 2!notE. Qed.

Lemma not_orP (P Q : Prop) : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. by rewrite not_orE. Qed.

Lemma not_implyE (P Q : Prop) : (~ (P -> Q)) = (P /\ ~ Q).
Proof. by rewrite propeqE not_implyP. Qed.

Lemma implyE (P Q : Prop) : (P -> Q) = (~ P \/ Q).
Proof. by rewrite -[LHS]notE not_implyE propeqE not_andP notE. Qed.

Lemma orC : commutative or.
Proof. by move=> /PropB[] /PropB[] => //; rewrite !orB. Qed.

Lemma orA : associative or.
Proof. by move=> P Q R; rewrite propeqE; split=> [|]; tauto. Qed.

Lemma orCA : left_commutative or.
Proof. by move=> P Q R; rewrite !orA (orC P). Qed.

Lemma orAC : right_commutative or.
Proof. by move=> P Q R; rewrite -!orA (orC Q). Qed.

Lemma orACA : interchange or or.
Proof. by move=> P Q R S; rewrite !orA (orAC P). Qed.

Lemma orNp P Q : (~ P \/ Q) = (P -> Q).
Proof. by case/PropB: P; rewrite notB orB implyB. Qed.

Lemma orpN P Q : (P \/ ~ Q) = (Q -> P). Proof. by rewrite orC orNp. Qed.

Lemma or3E P Q R : [\/ P, Q | R] = (P \/ Q \/ R).
Proof.
rewrite -(asboolE P) -(asboolE Q) -(asboolE R) (reflect_eq or3P).
by rewrite -2!(reflect_eq orP).
Qed.

Lemma or4E P Q R S : [\/ P, Q, R | S] = (P \/ Q \/ R \/ S).
Proof.
rewrite -(asboolE P) -(asboolE Q) -(asboolE R) -(asboolE S) (reflect_eq or4P).
by rewrite -3!(reflect_eq orP).
Qed.

Lemma andC : commutative and.
Proof. by move=> /PropB[] /PropB[]; rewrite !andB. Qed.

Lemma andA : associative and.
Proof. by move=> P Q R; rewrite propeqE; split=> [|]; tauto. Qed.

Lemma andCA : left_commutative and.
Proof. by move=> P Q R; rewrite !andA (andC P). Qed.

Lemma andAC : right_commutative and.
Proof. by move=> P Q R; rewrite -!andA (andC Q). Qed.

Lemma andACA : interchange and and.
Proof. by move=> P Q R S; rewrite !andA (andAC P). Qed.

Lemma and3E P Q R : [/\ P, Q & R] = (P /\ Q /\ R).
Proof. by eqProp=> [[] | [? []]]. Qed.

Lemma and4E P Q R S : [/\ P, Q, R & S] = (P /\ Q /\ R /\ S).
Proof. by eqProp=> [[] | [? [? []]]]. Qed.

Lemma and5E P Q R S T : [/\ P, Q, R, S & T] = (P /\ Q /\ R /\ S /\ T).
Proof. by eqProp=> [[] | [? [? [? []]]]]. Qed.

Lemma implyNp P Q : (~ P -> Q : Prop) = (P \/ Q).
Proof. by rewrite -orNp notK. Qed.

Lemma implypN (P Q : Prop) : (P -> ~ Q) = ~ (P /\ Q).
Proof. by case/PropB: P; rewrite implyB andB ?notB. Qed.

Lemma implyNN P Q : (~ P -> ~ Q) = (Q -> P).
Proof. by rewrite implyNp orpN. Qed.

Lemma or_andr : right_distributive or and.
Proof. by case/PropB=> Q R; rewrite !orB ?andB. Qed.

Lemma or_andl : left_distributive or and.
Proof. by move=> P Q R; rewrite -!(orC R) or_andr. Qed.

Lemma and_orr : right_distributive and or.
Proof. by move=> P Q R; apply/not_inj; rewrite !(not_andE, not_orE) or_andr. Qed.

Lemma and_orl : left_distributive and or.
Proof. by move=> P Q R; apply/not_inj; rewrite !(not_andE, not_orE) or_andl. Qed.

Lemma forallNE {T} (P : T -> Prop) : (forall x, ~ P x) = ~ exists x, P x.
Proof.
by rewrite propeqE; split => [fP [x /fP]//|nexP x Px]; apply: nexP; exists x.
Qed.

Lemma existsNE {T} (P : T -> Prop) : (exists x, ~ P x) = ~ forall x, P x.
Proof.
rewrite propeqE; split=> [[x Px] aP //|NaP].
by apply: contrapT; rewrite -forallNE => aP; apply: NaP => x; apply: contrapT.
Qed.

Lemma existsNP T (P : T -> Prop) : (exists x, ~ P x) <-> ~ forall x, P x.
Proof. by rewrite existsNE. Qed.

Lemma not_existsP T (P : T -> Prop) : (exists x, P x) <-> ~ forall x, ~ P x.
Proof. by rewrite forallNE notK. Qed.

Lemma forallNP T (P : T -> Prop) : (forall x, ~ P x) <-> ~ exists x, P x.
Proof. by rewrite forallNE. Qed.

Lemma not_forallP T (P : T -> Prop) : (forall x, P x) <-> ~ exists x, ~ P x.
Proof. by rewrite existsNE notK. Qed.

Lemma exists2E A P Q : (exists2 x : A, P x & Q x) = (exists x, P x /\ Q x).
Proof. by eqProp=> -[x]; last case; exists x. Qed.

Lemma exists2P T (P Q : T -> Prop) :
  (exists2 x, P x & Q x) <-> exists x, P x /\ Q x.
Proof. by rewrite exists2E. Qed.

Lemma not_exists2P T (P Q : T -> Prop) :
  (exists2 x, P x & Q x) <-> ~ forall x, ~ P x \/ ~ Q x.
Proof.
rewrite exists2P not_existsP.
by split; apply: contra_not => PQx x;  apply/not_andP; apply: PQx.
Qed.

Lemma forall2NP T (P Q : T -> Prop) :
  (forall x, ~ P x \/ ~ Q x) <-> ~ (exists2 x, P x & Q x).
Proof.
split=> [PQ [t Pt Qt]|PQ t]; first by have [] := PQ t.
by rewrite -not_andP => -[Pt Qt]; apply PQ; exists t.
Qed.

Lemma forallPNP T (P Q : T -> Prop) :
  (forall x, P x -> ~ Q x) <-> ~ (exists2 x, P x & Q x).
Proof.
split=> [PQ [t Pt Qt]|PQ t]; first by have [] := PQ t.
by move=> Pt Qt; apply: PQ; exists t.
Qed.

Lemma existsPNP T (P Q : T -> Prop) :
  (exists2 x, P x & ~ Q x) <-> ~ (forall x, P x -> Q x).
Proof.
split=> [[x Px NQx] /(_ x Px)//|]; apply: contra_notP => + x Px.
by apply: contra_notP => NQx; exists x.
Qed.

Lemma forallp_asboolPn2 {T} {P Q : T -> Prop} :
  reflect (forall x : T, ~ P x \/ ~ Q x) (~~ `[<exists2 x : T, P x & Q x>]).
Proof.
apply: (iffP idP)=> [/asboolPn NP x|NP].
  by move/forallPNP : NP => /(_ x)/and_rec/not_andP.
by apply/asboolP=> -[x Px Qx]; have /not_andP := NP x; exact.
Qed.

Section bigmaxmin.
Local Notation max := Order.max.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : Order.disp_t) (T : orderType d).
Variables (x : T) (I : finType) (P : pred I) (m : T) (F : I -> T).

Import Order.TTheory.

Lemma bigmax_geP : reflect (m <= x \/ exists2 i, P i & m <= F i)
                           (m <= \big[max/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[mx|[i Pi mFi]]].
- rewrite leNgt => /bigmax_ltP /not_andP[/negP|]; first by rewrite -leNgt; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -leNgt; right; exists i.
- by rewrite bigmax_idl le_max mx.
- by rewrite (bigmaxD1 i)// le_max mFi.
Qed.

Lemma bigmax_gtP : reflect (m < x \/ exists2 i, P i & m < F i)
                           (m < \big[max/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[mx|[i Pi mFi]]].
- rewrite ltNge => /bigmax_leP /not_andP[/negP|]; first by rewrite -ltNge; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -ltNge; right; exists i.
- by rewrite bigmax_idl lt_max mx.
- by rewrite (bigmaxD1 i)// lt_max mFi.
Qed.

Lemma bigmin_leP : reflect (x <= m \/ exists2 i, P i & F i <= m)
                           (\big[min/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[xm|[i Pi Fim]]].
- rewrite leNgt => /bigmin_gtP /not_andP[/negP|]; first by rewrite -leNgt; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -leNgt; right; exists i.
- by rewrite bigmin_idl ge_min xm.
- by rewrite (bigminD1 i)// ge_min Fim.
Qed.

Lemma bigmin_ltP : reflect (x < m \/ exists2 i, P i & F i < m)
                           (\big[min/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[xm|[i Pi Fim]]].
- rewrite ltNge => /bigmin_geP /not_andP[/negP|]; first by rewrite -ltNge; left.
  by move=> /existsNP[i /not_implyP[Pi /negP]]; rewrite -ltNge; right; exists i.
- by rewrite bigmin_idl gt_min xm.
- by rewrite (bigminD1 _ _ _ Pi) gt_min Fim.
Qed.

End bigmaxmin.

Module FunOrder.
Section FunOrder.
Import Order.TTheory.
Variables (aT : Type) (d : Order.disp_t) (T : porderType d).
Implicit Types f g h : aT -> T.

Lemma fun_display : Order.disp_t. Proof. exact: Order.default_display. Qed.

Definition lef f g := `[< forall x, (f x <= g x)%O >].
Local Notation "f <= g" := (lef f g).

Definition ltf f g := `[< (forall x, (f x <= g x)%O) /\ exists x, f x != g x >].
Local Notation "f < g" := (ltf f g).

Lemma ltf_def f g : (f < g) = (g != f) && (f <= g).
Proof.
apply/idP/andP => [fg|[gf fg]]; [split|apply/asboolP; split; [exact/asboolP|]].
- by apply/eqP => gf; move: fg => /asboolP[fg] [x /eqP]; apply; rewrite gf.
- apply/asboolP => x; rewrite le_eqVlt; move/asboolP : fg => [fg [y gfy]].
  by have [//|gfx /=] := boolP (f x == g x); rewrite lt_neqAle gfx /= fg.
- apply/not_existsP => h.
  have : f =1 g by move=> x; have /negP/negPn/eqP := h x.
  by rewrite -funeqE; apply/nesym/eqP.
Qed.

Fact lef_refl : reflexive lef. Proof. by move=> f; apply/asboolP => x. Qed.

Fact lef_anti : antisymmetric lef.
Proof.
move=> f g => /andP[/asboolP fg /asboolP gf]; rewrite funeqE => x.
by apply/eqP; rewrite eq_le fg gf.
Qed.

Fact lef_trans : transitive lef.
Proof.
move=> g f h /asboolP fg /asboolP gh; apply/asboolP => x.
by rewrite (le_trans (fg x)).
Qed.

#[export]
HB.instance Definition _ := @Order.isPOrder.Build
  fun_display (aT -> T) lef ltf ltf_def lef_refl lef_anti lef_trans.

End FunOrder.

Section FunLattice.
Import Order.TTheory.
Variables (aT : Type) (d : Order.disp_t) (T : latticeType d).
Implicit Types f g h : aT -> T.

Definition meetf f g := fun x => Order.meet (f x) (g x).
Definition joinf f g := fun x => Order.join (f x) (g x).

Lemma meetfC : commutative meetf.
Proof. move=> f g; apply/funext => x; exact: meetC. Qed.

Lemma joinfC : commutative joinf.
Proof. move=> f g; apply/funext => x; exact: joinC. Qed.

Lemma meetfA : associative meetf.
Proof. move=> f g h; apply/funext => x; exact: meetA. Qed.

Lemma joinfA : associative joinf.
Proof. move=> f g h; apply/funext => x; exact: joinA. Qed.

Lemma joinfKI g f : meetf f (joinf f g) = f.
Proof. apply/funext => x; exact: joinKI. Qed.

Lemma meetfKU g f : joinf f (meetf f g) = f.
Proof. apply/funext => x; exact: meetKU. Qed.

Lemma lef_meet f g : (f <= g)%O = (meetf f g == f).
Proof.
apply/idP/idP => [/asboolP f_le_g|/eqP <-].
- apply/eqP/funext => x; exact/meet_l/f_le_g.
- apply/asboolP => x; exact: leIr.
Qed.

#[export]
HB.instance Definition _ := Order.POrder_isLattice.Build _ (aT -> T)
  meetfC joinfC meetfA joinfA joinfKI meetfKU lef_meet.

End FunLattice.
Module Exports.
HB.reexport.
End Exports.
End FunOrder.
Export FunOrder.Exports.

Lemma lefP (aT : Type) d (T : porderType d) (f g : aT -> T) :
  reflect (forall x, (f x <= g x)%O) (f <= g)%O.
Proof. by apply: (iffP idP) => [fg|fg]; [exact/asboolP | exact/asboolP]. Qed.

Lemma meetfE (aT : Type) d (T : latticeType d) (f g : aT -> T) x :
  ((f `&` g) x = f x `&` g x)%O.
Proof. by []. Qed.

Lemma joinfE (aT : Type) d (T : latticeType d) (f g : aT -> T) x :
  ((f `|` g) x = f x `|` g x)%O.
Proof. by []. Qed.

Lemma iterfS {T} (f : T -> T) (n : nat) : iter n.+1 f = f \o iter n f.
Proof. by []. Qed.

Lemma iterfSr {T} (f : T -> T) (n : nat) : iter n.+1 f = iter n f \o f.
Proof. by apply/funeqP => ?; rewrite iterSr. Qed.

Lemma iter0 {T} (f : T -> T) : iter 0 f = id.
Proof. by []. Qed.

Section Inhabited.
Variable (T : Type).

Lemma inhabitedE: inhabited T = exists x : T, True.
Proof. by eqProp; case. Qed.

Lemma inhabited_witness: inhabited T -> T.
Proof. by rewrite inhabitedE => /cid[]. Qed.

End Inhabited.

Lemma uncurryK {X Y Z : Type} : cancel (@uncurry X Y Z) curry.
Proof. by move=> f; rewrite funeq2E. Qed.

Lemma curryK {X Y Z : Type} : cancel curry (@uncurry X Y Z).
Proof. by move=> f; rewrite funeqE=> -[]. Qed.
