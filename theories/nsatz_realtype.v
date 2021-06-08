Require Import Nsatz.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
Require Import boolp reals ereal.

(******************************************************************************)
(*                           nsatz for realType                               *)
(*                                                                            *)
(* This file registers the ring corresponding to the MathComp-Analysis type   *)
(* realType to the tactic nsatz of Coq. This enables some automation used for *)
(* example in the file trigo.v.                                               *)
(*                                                                            *)
(* ref: https://coq.inria.fr/refman/addendum/nsatz.html                       *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Nsatz_realType.
Variable T : realType.

Lemma Nsatz_realType_Setoid_Theory : Setoid.Setoid_Theory T (@eq T).
Proof. by constructor => [x //|x y //|x y z ->]. Qed.

Definition Nsatz_realType0 := (0%:R : T).
Definition Nsatz_realType1 := (1%:R : T).
Definition Nsatz_realType_add (x y : T) := (x + y)%R.
Definition Nsatz_realType_mul (x y : T) := (x * y)%R.
Definition Nsatz_realType_sub (x y : T) := (x - y)%R.
Definition Nsatz_realType_opp (x  : T) := (- x)%R.

#[global]
Instance Nsatz_realType_Ring_ops:
   (@Ncring.Ring_ops T Nsatz_realType0 Nsatz_realType1
  Nsatz_realType_add
  Nsatz_realType_mul
  Nsatz_realType_sub
  Nsatz_realType_opp (@eq T)).
Defined.

#[global]
Instance Nsatz_realType_Ring : (Ncring.Ring (Ro:=Nsatz_realType_Ring_ops)).
Proof.
constructor => //.
- exact: Nsatz_realType_Setoid_Theory.
- by move=> x y -> x1 y1 ->.
- by move=> x y -> x1 y1 ->.
- by move=> x y -> x1 y1 ->.
- by move=> x y ->.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulr1.
- exact: mulrA.
- exact: mulrDl.
- move=> x y z; exact: mulrDr.
- exact: subrr.
Defined.

#[global]
Instance Nsatz_realType_Cring: (Cring.Cring (Rr:=Nsatz_realType_Ring)).
Proof. exact: mulrC. Defined.

#[global]
Instance Nsatz_realType_Integral_domain :
   (Integral_domain.Integral_domain (Rcr:=Nsatz_realType_Cring)).
Proof.
constructor.
  move=> x y.
  rewrite -[_ _ Algebra_syntax.zero]/(x * y = 0)%R => /eqP.
  by rewrite mulf_eq0 => /orP[] /eqP->; [left | right].
rewrite -[_ _ Algebra_syntax.zero]/(1 = 0)%R; apply/eqP.
by rewrite (eqr_nat T 1 0).
Defined.

End Nsatz_realType.

Tactic Notation "nsatz" := nsatz_default.
