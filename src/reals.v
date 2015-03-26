(* -------------------------------------------------------------------- *)
(* We modified the axiomatization present in the 4CT development by:    *)
(*  - using Leibniz equality instead of (<= ∩ >=)                       *)
(*  - changing the axiomatization of order, explicting that it is       *)
(*    a total relation and that ((<=) = (<) ∪ (=))                      *)
(*  - changing the definition of lub, which is now an adherent point.   *)
(*    This should provide the required flavour of choice operator       *)
(*    for compactness arguments.                                        *)
(*                                                                      *)
(* Rationale: we use Prop as a sort confining the use of classical      *)
(*            reasoning.                                                *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype funtype ssrnat div.
Require Import ssralg ssrnum ssrint rat intdiv bigop.
Require Import Setoid SetoidClass.

Import Monoid.
Import GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac done := solve [intuition] || ssreflect.done.

Hint Resolve iff_refl.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope    with RR.
Delimit Scope realset_scope with Rset.

Local Open Scope real_scope.

Notation "n %:Z" := n%N%:Z%R (only parsing).
Notation "n %:R" := n%N%:R%R (only parsing).
Notation "m %:Q" := m%:Q%R%N (only parsing).

(* -------------------------------------------------------------------- *)
Module Equiv.
  Inductive equiv (P Q : Prop) : Prop :=
  | Iff of P -> Q & Q -> P.

  Implicit Types P Q R : Prop.

  Lemma equivP P Q: (equiv P Q) <-> (P <-> Q).
  Proof. by []. Qed.

  Lemma iffLR P Q: equiv P Q -> (P -> Q). Proof. by []. Qed.
  Lemma iffRL P Q: equiv P Q -> (Q -> P). Proof. by []. Qed.

  Lemma iffLRn P Q: equiv P Q -> (~P -> ~Q). Proof. by []. Qed.
  Lemma iffRLn P Q: equiv P Q -> (~Q -> ~P). Proof. by []. Qed.

  Lemma iff_refl: Reflexive equiv.
  Proof. by rewrite /Reflexive. Qed.

  Lemma iff_sym: Symmetric equiv.
  Proof. by rewrite /Symmetric. Qed.

  Lemma iff_trans: Transitive equiv.
  Proof. by rewrite /Transitive. Qed.

  Instance equiv_Reflexive  : Reflexive  equiv := iff_refl.
  Instance equiv_Symmetric  : Symmetric  equiv := iff_sym.
  Instance equiv_Transitive : Transitive equiv := iff_trans.

  Program Instance equiv_equivalence : Equivalence equiv.
  Program Instance equiv_Rewrite: RewriteRelation equiv.

  Program Instance iff_setoid : Setoid Prop :=
    { equiv := equiv ; setoid_equiv := equiv_equivalence }.
End Equiv.

Notation "P <~> Q" := (Equiv.equiv P Q) (at level 95, no associativity).

Hint View for move/  Equiv.iffLRn|2 Equiv.iffRLn|2 Equiv.iffLR|2 Equiv.iffRL|2.
Hint View for apply/ Equiv.iffRLn|2 Equiv.iffLRn|2 Equiv.iffRL|2 Equiv.iffLR|2.

(* -------------------------------------------------------------------- *)
Module Real.
Record structure : Type := Structure {
  sort : Type;
  le   : sort -> sort -> Prop;
  sup  : (sort -> Prop) -> sort;
  add  : sort -> sort -> sort;
  zero : sort;
  opp  : sort -> sort;
  mul  : sort -> sort -> sort;
  one  : sort;
  inv  : sort -> sort
}.

Module Exports.
Coercion sort : structure >-> Sortclass.
End Exports.
End Real.

Import Real.Exports.

(* -------------------------------------------------------------------- *)
Notation "{ x | P }" := (fun x : Real.sort _ => P : Prop) : realset_scope.

Bind Scope real_scope with Real.sort.

Global Arguments Real.zero {s}%type.
Global Arguments Real.one  {s}%type.
Global Arguments Real.le   {s}%type (_ _)%real_scope.
Global Arguments Real.sup  {s}%type (_)%realset_scope.
Global Arguments Real.add  {s}%type (_ _)%real_scope.
Global Arguments Real.opp  {s}%type (_)%real_scope.
Global Arguments Real.mul  {s}%type (_ _)%real_scope.
Global Arguments Real.inv  {s}%type (_)%real_scope.

(* -------------------------------------------------------------------- *)
Notation "'sup' E" := (Real.sup E) (at level 10, E at level 8) : real_scope.
Notation "x + y"   := (Real.add x y) : real_scope.
Notation "0"       := (@Real.zero _) : real_scope.
Notation "- y"     := (Real.opp y) : real_scope.
Notation "x - y"   := (x + - y) : real_scope.
Notation "x * y"   := (Real.mul x y) : real_scope.
Notation "1"       := (@Real.one _) : real_scope.
Notation "y ^-1"   := (Real.inv y) : real_scope.
Notation "x / y"   := (x * y^-1) : real_scope.

Notation "x <= y" := (Real.le x y) : real_scope.
Notation "x >= y" := (y <= x) (only parsing) : real_scope.
Notation "x < y"  := (~ (y <= x)) : real_scope.
Notation "x > y"  := (y < x) (only parsing) : real_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : real_scope.
Notation "x < y <= z"  := (x < y /\ y <= z) : real_scope.
Notation "x <= y < z"  := (x <= y /\ y < z) : real_scope.
Notation "x < y < z"   := (x < y /\ y < z) : real_scope.

Notation "2" := (1 + 1) : real_scope.
Notation "- 1" := (- (1)) : real_scope.
Notation "- 2" := (- (2)) : real_scope.

Notation "+%R" := (@Real.add _) (at level 0).
Notation "-%R" := (@Real.opp _) (at level 0).
Notation "*%R" := (@Real.mul _) (at level 0, format " *%R").

Local Notation structure := Real.structure.

(* -------------------------------------------------------------------- *)
(* A few basic derived operations and relations.                        *)

(* Real set non-emptyness. *)
Definition nonempty (R : structure) (E : R -> Prop) :=
  exists x : R, E x.

(* Real upper bound set. *)
Definition ub (R : structure) (E : R -> Prop) : R -> Prop :=
  { z | forall y : R, E y -> y <= z }%Rset.

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down (R : structure) (E : R -> Prop) : R -> Prop :=
  { x | exists2 y : R, E y & x <= y }%Rset.

(* Real set supremum existence condition. *)
Definition has_ub  (R : structure) (E : R -> Prop) := nonempty (ub E).
Definition has_sup (R : structure) (E : R -> Prop) := nonempty E /\ has_ub E.

(* Real set image. *)
Definition image (R R' : structure) (phi : R -> R') (E : R -> Prop) (x' : R') :=
  exists2 x : R, E x & x' = (phi x).

Global Arguments ub      {R}%type _%realset_scope _%real_scope.
Global Arguments has_ub  {R}%type _%realset_scope.
Global Arguments has_sup {R}%type _%realset_scope.
Global Arguments down    {R}%type _%realset_scope _%real_scope.

(* -------------------------------------------------------------------- *)
Record axioms (R : structure) : Prop := Axioms {
  (* Ordering axioms *)
  le_reflexive:
    forall x : R, x <= x;
  le_transitive :
    forall y x z : R, x <= y -> y <= z -> x <= z;
  le_total :
    forall x y : R, x <= y \/ y < x ;
  le_def :
    forall x y : R, x <= y <-> x < y \/ x = y ;

  (* Least upper bound axions *)
  sup_upper_bound :
    forall E : R -> Prop, has_sup E -> ub E (sup E);
  sup_adherent :
    forall (E : R -> Prop) (eps : R), has_sup E -> 0 < eps ->
      exists2 e : R, E e & (sup E - eps) < e;

  (* Monotonicity of ordering w.r.t ring operations *)
  add_monotone :
    forall x y z : R, y <= z -> x + y <= x + z;
  mul_monotone :
    forall x y z : R, 0 <= x -> y < z -> x * y <= x * z;

  (* Field operations *)
  add_commutative : @commutative R R +%R;
  add_associative : @associative R +%R;
  add_zero_left : @left_id R R 0 +%R;
  add_left_inverse : @left_inverse R R R 0 -%R +%R;
  mul_commutative : @commutative R R *%R;
  mul_associative : @associative R *%R;
  mul_left_distributive : @left_distributive R R *%R +%R;
  mul_one_left : @left_id R R 1 *%R;
  mul_inverse_right : forall x : R, x <> 0 -> x / x = 1;
  one_nonzero : 1 <> 0 :> R
}.

(* -------------------------------------------------------------------- *)
Record model : Type := Model {
  model_structure : structure;
  model_axioms : axioms model_structure
}.

Coercion model_structure : model >-> structure.
Coercion model_axioms : model >-> axioms.

(* -------------------------------------------------------------------- *)
Record morphism (R R' : structure) (phi : R -> R') : Prop := Morphism {
  morph_le   : forall x y, phi x <= phi y <-> x <= y;
  morph_sup  : forall E, has_sup E -> phi (sup E) = (sup (image phi E));
  morph_add  : forall x y, phi (x + y) = phi x + phi y;
  morph_zero : phi 0 = 0;
  morph_opp  : forall x, phi (-x) = -(phi x);
  morph_mul  : forall x y, phi (x * y) = (phi x) * (phi y);
  morph_one  : phi 1 = 1;
  morph_inv  : forall x, x <> 0 -> phi x^-1 = (phi x)^-1
}.

(******************************************************************************)
(**  Derived real operations:                                                 *)
(*    select {x1 if P1, x2 if P2} == definition by nondeterministic cases.    *)
(*     select {x1 if P1, else x2} == definition by deterministic cases.       *)
(*           min x1 x2, max x1 x2 == (binary) minimum, maximum.               *)
(*             intf R m, ratf R a == injections from Z and Q into R.          *)
(*                                  (made locally into coercions for fixed R) *)
(*                        floor x == the largest integral y <= x.             *)
(*                     range1 x y == y is in the unit interval [x, x+1).      *)
(* We use 'R' as the suffix standing for real arguments, since 'r' is already *)
(* used in the MathComp library for generic ring arguments.                   *)
(******************************************************************************)

Section RealOperations.
Variable R : structure.

Definition pickR_set P1 P2 (x1 x2 : R) :=
  { y | P1 /\ y = x1 \/ P2 /\ y = x2 }%Rset.

Definition pickR P1 P2 x1 x2 := sup (pickR_set P1 P2 x1 x2).

Definition selectR P := pickR P (~ P).

Definition min x1 x2 := pickR (x1 <= x2) (x2 <= x1) x1 x2.

Definition max x1 x2 := pickR (x1 <= x2) (x2 <= x1) x2 x1.

Definition intR (m : int) : R := match m with
  | Posz 0    => 0
  | Posz n.+1 => iter n (Real.add 1) 1
  | Negz n    => - iter n (Real.add 1) 1
  end.

Definition ratR (a : rat) :=
  if a \is a Qint then intR (numq a) else intR (numq a) / intR (denq a).

Inductive floor_set (x : R) : R -> Prop :=
  FloorSet (m : int) of intR m <= x : floor_set x (intR m).

Definition floor x := sup (floor_set x).

Definition range1 (x y : R) := x <= y < x + 1.

End RealOperations.

Notation "'select' { x1 'if' P1 , x2 'if' P2 }" := (pickR P1 P2 x1 x2)
   (at level 10, x1, x2, P1, P2 at level 100,
    format "'select'  { x1  'if'  P1 ,  x2  'if'  P2 }") : real_scope.

Notation "'select' { x1 'if' P , 'else' x2 }" := (selectR P x1 x2)
   (at level 10, x1, x2, P at level 100,
    format "'select'  { x1  'if'  P ,  'else'  x2 }") : real_scope.

Prenex Implicits min max.

(******************************************************************************)
(* Basic arithmetic/order/setoid lemmas for real numbers.                     *)
(* Note that the sup and inverse operators are not morphisms because they are *)
(* only partially defined by the axioms.                                      *)
(*   Most of the lemmas here do not depend explicitly on classical reasoning; *)
(* to emphasize this we only prove the excluded middle at the very end of     *)
(* this section, when it is needed to prove, e.g., the archimedean property.  *)
(******************************************************************************)
Section RealLemmas.

Variable R : model.
Implicit Types x y z : R.
Implicit Types E : R -> Prop.
Implicit Types m d : int.
Implicit Types n p : nat.
Implicit Types a b : rat.

Local Coercion intRR := intR R.
Local Coercion ratRR := ratR R.
Local Notation Rtype := (Real.sort R) (only parsing).

(* -------------------------------------------------------------------- *)
Lemma addRC: @commutative R R +%R.
Proof. exact: add_commutative R. Qed.

Lemma addRA: @associative R +%R.
Proof. exact: add_associative R. Qed.

Lemma add0R : @left_id R R 0 +%R.
Proof. exact: (add_zero_left R). Qed.

Lemma addR0 : @right_id R R 0 +%R.
Proof. by move=> x; rewrite addRC add0R. Qed.

Lemma addNR : @left_inverse R R R 0 -%R +%R.
Proof. exact: (add_left_inverse R). Qed.

Lemma addRN : @right_inverse R R R 0 -%R +%R.
Proof. by move=> x; rewrite addRC addNR. Qed.

Definition subRR := addRN.

Canonical addR_monoid := Monoid.Law addRA add0R addR0.
Canonical addR_comoid := Monoid.ComLaw addRC.

Lemma addRCA : @left_commutative R R +%R.
Proof. exact: mulmCA. Qed.

Lemma addRAC : @right_commutative R R +%R.
Proof. exact: mulmAC. Qed.

Lemma addRACA : @interchange R +%R +%R.
Proof. exact: mulmACA. Qed.

Lemma addKR : @left_loop R R -%R +%R.
Proof. by move=> x y; rewrite addRA addNR add0R. Qed.

Lemma addNKR : @rev_left_loop R R -%R +%R.
Proof. by move=> x y; rewrite addRA addRN add0R. Qed.

Lemma addRK : @right_loop R R -%R +%R.
Proof. by move=> x y; rewrite -addRA addRN addR0. Qed.

Lemma addRNK : @rev_right_loop R R -%R +%R.
Proof. by move=> x y; rewrite -addRA addNR addR0. Qed.

Definition subRK := addRNK.

Lemma addRI : @right_injective R R R +%R.
Proof. move=> x; exact: can_inj (addKR x). Qed.

Lemma addIR : @left_injective R R R +%R.
Proof. move=> y; exact: can_inj (addRK y). Qed.

Lemma oppRK : @involutive R -%R.
Proof. by move=> x; apply: (@addIR (- x)); rewrite addNR addRN. Qed.

Lemma oppR_inj : @injective R R -%R.
Proof. exact: inv_inj oppRK. Qed.

Lemma oppR0 : -0 = 0 :> R.
Proof. by rewrite -[-0]add0R subRR. Qed.

Lemma oppR_eq0 x : (- x = 0) <-> (x = 0).
Proof.
split=> [|->]; last by rewrite oppR0.
by rewrite (inv_eq oppRK) oppR0.
Qed.

Lemma subR0 x : x - 0 = x. Proof. by rewrite oppR0 addR0. Qed.
Lemma sub0R x : 0 - x = - x. Proof. by rewrite add0R. Qed.

Lemma oppRD : {morph -%R: x y / x + y : R}.
Proof.
by move=> x y; apply: (@addRI (x + y)); rewrite addRA subRR addRAC addRK subRR.
Qed.

Lemma oppRB x y : - (x - y) = y - x.
Proof. by rewrite oppRD addRC oppRK. Qed.

(* -------------------------------------------------------------------- *)
Lemma leRR x : x <= x.
Proof. exact: (le_reflexive R). Qed.
Hint Resolve leRR.

Lemma ltRW x y : x < y -> x <= y.
Proof. by move=> lt_xy; rewrite (le_def R). Qed.

Lemma leR_trans x2 x1 x3 : x1 <= x2 -> x2 <= x3 -> x1 <= x3.
Proof. exact: (le_transitive R). Qed.

Lemma leR_add2l x y z : y <= z -> x + y <= x + z.
Proof. by move/(add_monotone R). Qed.

Lemma leR_add2r x y z : y <= z -> y + x <= z + x.
Proof. by move/(add_monotone R x); rewrite ![x+_]addRC. Qed.

Lemma subR_gt0 x y : 0 < y - x <-> x < y.
Proof.
split=> h.
  by move/(add_monotone R (-x)); rewrite addNR addRC.
by move/(add_monotone R x); rewrite addRCA subRR !addR0.
Qed.

(*-------------------------------------------------------------------- *)
Lemma sup_ub E : has_ub E -> ub E (sup E).
Proof.
move=> ubE x E_x; apply: (sup_upper_bound R) (E_x).
by split; first by exists x.
Qed.

Lemma sup_total E x : has_sup E -> down E x \/ sup E <= x.
Proof.
move=> has_supE; case: (le_total R (sup E) x) => hx //; left.
have /(sup_adherent R has_supE) : 0 < sup E - x by apply/subR_gt0.
case=> e Ee hlte; exists e => //.
by move: hlte; rewrite oppRB addRCA subRR addR0 => /ltRW.
Qed.
End RealLemmas.
