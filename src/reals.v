Require Import ssreflect ssrbool ssrfun.

(* We play with modifying the axiomatization present in the 4CT development by:
   - changing le for lt in the structure (usefull?)
   - using Leibniz equality instead of the conjunction of <= and >=
   - defining le in terms of Leibniz equality or lt
   - changing the axiomatization of order for a trichotomy in Prop
   - changing the definition of lub, which is now an adherent point.
     The hope being that this provides the required flavour of choice operator
     for compactness arguments.

We need to prove
  sup_total :
    forall (E : R -> Prop) (x : R), has_sup E -> down E x \/ le (sup E) x;

The floor function is no longer there, as it cannot be effectively implemented.

Rationale: we try to use Prop as a sort confining the use of classical reasoning.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Module Real.

Record structure : Type := Structure {
   sort : Type;
   lt : sort -> sort -> Prop;
   sup : (sort -> Prop) -> sort;
   add : sort -> sort -> sort;
   zero : sort;
   opp : sort -> sort;
   mul : sort -> sort -> sort;
   one : sort;
   inv : sort -> sort
}.

Arguments zero {s}.
Arguments one  {s}.

Local Coercion sort : structure >-> Sortclass.

(* A few basic derived operations and relations, used in the real axioms. *)

Notation le x y := (lt x y \/ x = y).
Notation minus x y := (add x (opp y)).

(* Real set non-emptyness. *)
Definition nonempty (R : structure) (E : R -> Prop) :=
  exists x : R, E x.

(* Real upper bound set. *)
Definition ub (R : structure) (E : R -> Prop) : R -> Prop :=
  fun z : R => forall y : R, E y -> le y z.

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down (R : structure) (E : R -> Prop) : R -> Prop :=
  fun x : R => exists2 y : R, E y & le x y.

(* Real set supremum existence condition. *)
Definition has_ub (R : structure) (E : R -> Prop) := nonempty (ub E).
Definition has_sup (R : structure) (E : R -> Prop) := nonempty E /\ has_ub E.

(* Real set image. *)
Definition image (R R' : structure) (phi : R -> R') (E : R -> Prop) (x' : R') :=
  exists2 x : R, E x & x' = (phi x).

(* A ternary xor for the specification of the total order property *)
CoInductive compare_real {R : structure} (x y : R) : Prop :=
  | CompareRealLt of lt x y : compare_real x y
  | CompareRealGt of lt y x : compare_real x y
  | CompareRealEq of x = y : compare_real x y.

Record axioms (R : structure) : Prop := Axioms {
  lt_transitive :
    forall y x z : R, lt x y -> lt y z -> lt x z;
  ltngeP : forall x y : R, compare_real x y;
  sup_upper_bound :
    forall E : R -> Prop, has_sup E -> ub E (sup E);
  sup_adherent :
    forall E : R -> Prop, forall eps : R,
    has_sup E -> lt zero eps -> exists2 e : R, E e & lt (minus (sup E) eps) e;
  add_monotone :
    forall x y z : R, le y z -> le (add x y) (add x z);
  add_commutative : @commutative R R add;
  add_associative : @associative R add;
  add_zero_left : @left_id R R zero add;
  add_opposite_right : @right_inverse R R R zero opp add;
  mul_monotone :
    forall x y z : R, le zero x -> le y z -> le (mul x y) (mul x z);
  mul_commutative : @commutative R R mul;
  mul_associative : @associative R mul;
  mul_distributive_right : @right_distributive R R mul add;
  mul_one_left : @left_id R R one mul;
  mul_inverse_right :
    forall x : R, x <> zero -> mul x (inv x) = one;
  one_nonzero : one <> zero :> R
}.

Record model : Type := Model {
  model_structure : structure;
  model_axioms : axioms model_structure
}.

(* We use monomorphisms, so we can lift real axioms in R' back to R. *)
Record morphism (R R' : structure) (phi : R -> R') : Prop := Morphism {
  morph_lt : forall x y, lt (phi x) (phi y) <-> lt x y;
  morph_sup : forall E, has_sup E -> phi (sup E) = (sup (image phi E));
  morph_add : forall x y, phi (add x y) = add (phi x) (phi y);
  morph_zero : phi zero = zero;
  morph_opp : forall x, phi (opp x) = opp (phi x);
  morph_mul : forall x y, phi (mul x y) = mul (phi x) (phi y);
  morph_one : phi one = one;
  morph_inv : forall x, x <> zero -> phi (inv x) = inv (phi x)
}.

End Real.

Coercion Real.sort : Real.structure >-> Sortclass.
Coercion Real.model_structure : Real.model >-> Real.structure.
Coercion Real.model_axioms : Real.model >-> Real.axioms.
