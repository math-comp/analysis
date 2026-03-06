(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat finmap ssralg ssrint ssrnum interval.
From mathcomp Require Import interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets set_interval.
From mathcomp Require Import reals topology.

(**md**************************************************************************)
(* # Convexity                                                                *)
(*                                                                            *)
(* This file provides a small account of convexity using convex spaces, to be *)
(* completed with material from InfoTheo.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*  convex_quasi_associative == quasi-associativity of the operator of        *)
(*                              convex spaces                                 *)
(*         isConvexSpace R T == interface for convex spaces with              *)
(*                              R : numDomainType                             *)
(*                              The HB class is ConvexSpace.                  *)
(*               a <| t |> b == convexity operator                            *)
(* ```                                                                        *)
(*                                                                            *)
(* For `R : numDomainType`, `E : lmodType R` and `R` itself are shown to be   *)
(* convex spaces with the following aliases:                                  *)
(* ```                                                                        *)
(*       convex_lmodType E == E : lmodType R as a convex space                *)
(*  convex_numDomainType R == R : numDomainType as a convex space             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 49).

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Declare Scope convex_scope.
Local Open Scope convex_scope.

Module ConvexQuasiAssoc.
Section def.
Variables (R : numDomainType) (T : Type) (conv : {i01 R} -> T -> T -> T).

Local Notation "x <| p |> y" := (conv p x y).

Definition law := forall (p q r s : {i01 R}) (a b c : T),
  p%:num = r%:num * s%:num ->
  s%:num.~ = p%:num.~ * q%:num.~ ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
End def.

(** technical relations between the parameters of the quasi-associativity law *)
Section lemmas.

Lemma pq_sr (R : comPzRingType) (p q r s : R) :
  p = r * s ->
  1 - s = (1 - p) * (1 - q) ->
  (1 - p) * q = s * (1 - r).
Proof.
move=> prs spq; rewrite mulrBr [s * r]mulrC -prs mulr1 -[s](subKr 1) spq.
by rewrite addrAC -[X in _ = X - _]mulr1 -mulrBr subKr.
Qed.

Lemma sE (R : pzRingType) (p q s : R) :
  1 - s = (1 - p) * (1 - q) ->
  s = 1 - (1 - p) * (1 - q).
Proof. by move/eqP; rewrite subr_eq addrC -subr_eq => /eqP ->. Qed.

Lemma qE (R : comUnitRingType) (p q r s : R) :
  1 - p \is a GRing.unit ->
  p = r * s ->
  1 - s = (1 - p) * (1 - q) ->
  q = (s * (1 - r)) / (1 - p).
Proof.
by move=> p1unit /pq_sr /[apply] /(canRL (mulKr p1unit)); rewrite mulrC.
Qed.

Lemma rE (R : unitRingType) (p r s : R) :
  s \is a GRing.unit -> p = r * s -> r = p / s.
Proof. by move=> sunit /(canLR (mulrK sunit)) <-. Qed.

End lemmas.

End ConvexQuasiAssoc.

Definition convex_quasi_associative := ConvexQuasiAssoc.law.

HB.mixin Record isConvexSpace (R : numDomainType) T := {
  conv : {i01 R} -> T -> T -> T ;
  conv1 : forall a b, conv 1%:i01 a b = a ;
  convmm : forall (p : {i01 R}) a, conv p a a = a ;
  convC : forall (p : {i01 R}) a b, conv p a b = conv (1 - p%:inum)%:i01 b a;
  convA : convex_quasi_associative conv
}.

#[short(type=convType)]
HB.structure Definition ConvexSpace (R : numDomainType) :=
  {T of isConvexSpace R T & Choice T}.

Notation "a <| p |> b" := (conv p a b) : convex_scope.

Section convex_space_lemmas.
Context R (A : convType R).
Implicit Types a b : A.

Lemma conv0 a b : a <| 0%:i01 |> b = b.
Proof.
rewrite convC/= [X in _ <| X |> _](_ : _ = 1%:i01) ?conv1//.
by apply/val_inj => /=; rewrite subr0.
Qed.

End convex_space_lemmas.

Local Open Scope convex_scope.

Definition convex_lmodType {R : numDomainType} (E : lmodType R) : Type := E.

Section lmodType_convex_space.
Context {R : numDomainType} {E' : lmodType R}.
Implicit Type p q r : {i01 R}.

Let E := convex_lmodType E'.

Let avg p (a b : E) := p%:inum *: a + p%:inum.~ *: b.

Let avg1 a b : avg 1%:i01 a b = a.
Proof. by rewrite /avg/= onem1 scale0r scale1r addr0. Qed.

Let avgI p x : avg p x x = x.
Proof. by rewrite /avg -scalerDl/= add_onemK scale1r. Qed.

Let avgC p x y : avg p x y = avg (1 - (p%:inum))%:i01 y x.
Proof. by rewrite /avg onemK addrC. Qed.

Let avgA : convex_quasi_associative avg.
Proof.
move=> p q r s a b c prs spq; rewrite /avg.
rewrite [in LHS]scalerDr [in LHS]addrA [in RHS]scalerDr; congr (_ + _ + _).
- by rewrite scalerA mulrC prs.
- by rewrite !scalerA; congr *:%R; rewrite (ConvexQuasiAssoc.pq_sr prs).
- by rewrite scalerA spq.
Qed.

HB.instance Definition _ := Choice.on E.

HB.instance Definition _ :=
  isConvexSpace.Build R E avg1 avgI avgC avgA.

End lmodType_convex_space.

Definition convex_numDomainType (R : numDomainType) : Type := R^o.

Section numDomainType_convex_space.
Context {R : numDomainType}.
Implicit Types p q : {i01 R}.

Let avg p (a b : convex_lmodType R^o) := a <| p |> b.

Let avg1 a b : avg 1%:i01 a b = a.
Proof. exact: conv1. Qed.

Let avgI p x : avg p x x = x.
Proof. exact: convmm. Qed.

Let avgC p x y : avg p x y = avg (1 - (p%:inum))%:i01 y x.
Proof. exact: convC. Qed.

Let avgA : convex_quasi_associative avg.
Proof. exact: convA. Qed.

HB.instance Definition _ := @isConvexSpace.Build R R^o
  _ avg1 avgI avgC avgA.

End numDomainType_convex_space.

Section conv_numDomainType.
Context {R : numDomainType}.

Lemma convR_gt0 (a b : R^o) (t : {i01 R}) : 0 < a -> 0 < b -> 0 < a <| t |> b.
Proof.
move=> a0 b0.
have [->|t0] := eqVneq t 0%:i01; first by rewrite conv0.
have [->|t1] := eqVneq t 1%:i01; first by rewrite conv1.
rewrite addr_gt0// mulr_gt0//; first by rewrite lt_neqAle eq_sym t0 ge0.
by rewrite subr_gt0 lt_neqAle t1 le1.
Qed.

Lemma convRE (a b : R^o) (t : {i01 R}) :
  a <| t |> b = t%:inum * a + t%:inum.~ * b.
Proof. by []. Qed.

Let convRCE (a b : R^o) (t : {i01 R}) :
  a <| t |> b = t%:inum.~ * b + t%:inum * a.
Proof. by rewrite addrC convRE. Qed.

Lemma convR_line_path (a b : R^o) (t : {i01 R}) :
  a <| t |> b = line_path b a t%:num.
Proof. by rewrite convRCE. Qed.

Lemma convN (a b : R^o) (t : {i01 R}) : - (a <| t |> b) = - a <| t |> - b.
Proof. by rewrite !convRE opprD !mulrN. Qed.

Lemma conv_le (a b : R^o) (t : {i01 R}) : a <= b -> a <| t |> b <= b.
Proof.
move=> ab; rewrite convRE mulrBl mul1r addrCA -mulrBr gerDl.
by rewrite mulr_ge0_le0// subr_le0.
Qed.

Lemma convR_itv (a b : R^o) (t : {i01 R}) : a <= b -> a <| t |> b \in `[a, b].
Proof. by move=> ab; rewrite in_itv/= -lerN2 convN convC !conv_le ?lerN2. Qed.

End conv_numDomainType.


Definition convex_function (R : numFieldType) (E : lmodType R) (E' := convex_lmodType E) (D : set E') (f : E' -> R^o) :=
  forall (t : {i01 R}),
    {in D &, forall (x y : E'), (f (x <| t |> y) <= f x <| t |> f y)%R}.
(* TODO: generalize to convTypes once we have ordered convTypes (mathcomp 2) *)
