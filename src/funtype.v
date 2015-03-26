(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool ssrfun.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Section EqFun.
Variables T U : Type.
Variables f : T -> U.
Variables g : U -> T.
Variables h : T -> T.

Lemma inj_eq : injective f -> forall x y, (f x = f y) <-> (x = y).
Proof. by move=> inj_f x y; split=> [|-> //]; exact: inj_f. Qed.

Lemma can_eq : cancel f g -> forall x y, (f x = f y) <-> (x = y).
Proof. move/can_inj; exact: inj_eq. Qed.

Lemma bij_eq : bijective f -> forall x y, (f x = f y) <-> (x = y).
Proof. move/bij_inj; apply: inj_eq. Qed.

Lemma can2_eq : cancel f g -> cancel g f -> forall x y, (f x = y) <-> (x = g y).
Proof. by move=> fK gK x y; rewrite -{1}[y]gK; exact: can_eq. Qed.
End EqFun.

(* -------------------------------------------------------------------- *)
Section Endo.
Variables T : Type.
Variables h : T -> T.

Lemma inv_eq : involutive h -> forall x y : T, (h x = y) <-> (x = h y).
Proof. by move=> fK; exact: can2_eq. Qed.
End Endo.
