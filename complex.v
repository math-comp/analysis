From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import boolp reals.
From mathcomp Require Import realalg complex.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section test.
Context {R : realType}.

Check R[i].

End test.