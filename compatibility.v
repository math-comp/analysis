Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov hierarchy.

From mathcomp Require Import ssrbool eqtype ssrnat choice fintype ssralg.

Section AbelianGroup1.

Notation AbelianGroup := zmodType.

Context {G : AbelianGroup}.

Notation plus := +%R.
Notation opp := GRing.opp.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).
Notation zero := (0%R : G).

Import GRing.Theory.

Lemma plus_comm : forall x y : G, plus x y = plus y x.
Proof. exact: addrC. Qed.

Lemma plus_assoc : forall x y z : G, plus x (plus y z) = plus (plus x y) z.
Proof. exact: addrA. Qed.

Lemma plus_zero_r : forall x : G, plus x zero = x.
Proof. exact: addr0. Qed.

Lemma plus_opp_r : forall x : G, plus x (opp x) = zero.
Proof. exact: addrN. Qed.

Lemma plus_zero_l : forall x : G, plus zero x = x.
Proof. exact: add0r. Qed.

Lemma plus_opp_l : forall x : G, plus (opp x) x = zero.
Proof. exact: addNr. Qed.

Lemma opp_zero : opp zero = zero.
Proof. exact: oppr0. Qed.

Lemma minus_zero_r : forall x : G, minus x zero = x.
Proof. exact: subr0. Qed.

Lemma minus_eq_zero (x : G) : minus x x = zero.
Proof. exact: subrr. Qed.

Lemma plus_reg_l : forall r x y : G, plus r x = plus r y -> x = y.
Proof.
move=> r x y /eqP.
by rewrite (addrC r y) -subr_eq addrAC subrr add0r => /eqP.
Qed.

Lemma plus_reg_r : forall r x y : G, plus x r = plus y r -> x = y.
Proof.
by move=> r x y => /eqP; rewrite -subr_eq -addrA subrr addr0 => /eqP.
Qed.

Lemma opp_opp : forall x : G, opp (opp x) = x.
Proof. exact: opprK. Qed.

Lemma opp_plus : forall x y : G, opp (plus x y) = plus (opp x) (opp y).
Proof. exact: opprD. Qed.

Lemma opp_minus (x y : G) : opp (minus x y) = minus y x.
Proof. exact: opprB. Qed.

Lemma minus_trans (r x y : G) : minus x y = plus (minus x r) (minus r y).
Proof. by rewrite addrA -(addrA x) (addrC _ r) subrr addr0. Qed.

End AbelianGroup1.
