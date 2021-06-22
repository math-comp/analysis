Require Import Rdefinitions Raxioms RIneq.
Require Import Lra.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrint ssrnum.
Require Import Rstruct.

Delimit Scope R_scope with Re.

Local Open Scope ring_scope.

(* Adapted from http://github.com/pi8027/formalized-postscript/blob/master/stdlib_ext.v *)

Ltac mclra_hyps2R :=
  match goal with
  | H : context [andb _ _] |- _ => let H0 := fresh in case/andP: H => H H0
  | H : context [orb _ _] |- _ => case/orP: H => H
  | H : context [?L <= ?R] |- _ => move/RleP: H => H
  | H : context [?L < ?R] |- _ => move/RltP : H => H
  | H : context [?L == ?R] |- _ => move/eqP : H => H
  | H : context [?L + ?R] |- _ => rewrite -RplusE in H
  | H : context [?L * ?R] |- _ => rewrite -RmultE in H
  | H : context [?L - ?R] |- _ => rewrite -RminusE in H
  | H : context [- ?R] |- _ => rewrite -RoppE in H
  | H : context [?x%:R] |- _ =>
    rewrite -INRE INR_IZR_INZ [IZR (Z.of_nat _)]/= in H
  | H : context [?x%:~R] |- _ =>
    rewrite -pmulrn -INRE INR_IZR_INZ [IZR (Z.of_nat _)]/= in H
  end.

Ltac mclra_goal2R :=
  match goal with
  | |- is_true (andb _ _) => apply/andP; split
  | |- is_true (orb _ _) => try apply/orP
  | |- is_true (_ <= _) => try apply/RleP
  | |- is_true (_ < _) => try apply/RltP
  | |- is_true (_ == _) => try apply/eqP
  | |- context [?L + ?R] => rewrite -RplusE
  | |- context [?L * ?R] => rewrite -RmultE
  | |- context [?L - ?R] => rewrite -RminusE
  | |- context [- ?R] => rewrite -RoppE
  | |- context [?x%:R] => rewrite -INRE INR_IZR_INZ [IZR (Z.of_nat _)]/=
  | |- context [?x%:~R] =>
    rewrite -pmulrn -INRE INR_IZR_INZ [IZR (Z.of_nat _)]/=
  end.

Ltac mclra := repeat mclra_hyps2R; repeat mclra_goal2R; lra.

(* A few tests/examples *)

Goal forall x y : R,
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
move=> x y lineq_xy lineq'_xy.
mclra.
Qed.

Goal forall x y : R,
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y > 2%:R -> False.
Proof.
move=> x y lineq_xy lineq_xy' lineq_xy''.
mclra.
Qed.

Goal forall x : R, x <= -11%:~R -> x <= 12%:R.
Proof.
move=> x lineq_xy.
mclra.
Qed.

Goal forall (n : int) (x : R), x <= n%:~R -> x + x <= n%:~R + n%:~R.
Proof.
move=> n x lineq_xy.
mclra.
Qed.
