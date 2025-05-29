(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import set_interval functions cardinality ereal reals.
From mathcomp Require Import topology prodnormedzmodule normedtype derive.
From mathcomp Require Import realfun interval_inference.
From HB Require Import structures.

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

Declare Scope convex_scope.
Local Open Scope convex_scope.

Module ConvexQuasiAssoc.
Section def.
Variables (R : numDomainType) (T : Type) (conv : {i01 R} -> T -> T -> T).

Local Notation "x <| p |> y" := (conv p x y).

Definition law := forall (p q r s : {i01 R}) (a b c : T),
  p%:num = r%:num * s%:num ->
  `1- (s%:num) = `1- (p%:num) * `1- (q%:num) ->
  a <| p |> (b <| q |> c) = (a <| r |> b) <| s |> c.
End def.

(** technical relations between the parameters of the quasi-associativity law *)
Section lemmas.

Lemma pq_sr (R : comRingType) (p q r s : R) :
  p = r * s ->
  1 - s = (1 - p) * (1 - q) ->
  (1 - p) * q = s * (1 - r).
Proof.
move=> prs spq.
rewrite -[LHS]opprK -mulrN -[X in - X = _](addrK ((1 - p) * 1)).
rewrite -mulrDr (addrC _ 1) -spq mulr1 prs.
by rewrite !opprB addrC subrKA mulrDr mulr1 mulrN mulrC.
Qed.

Lemma sE (R : ringType) (p q s : R) :
  1 - s = (1 - p) * (1 - q) ->
  s = 1 - (1 - p) * (1 - q).
Proof. by move/eqP; rewrite subr_eq addrC -subr_eq => /eqP ->. Qed.

Lemma qE (R : comUnitRingType) (p q r s : R) :
  1 - p \is a GRing.unit ->
  p = r * s ->
  1 - s = (1 - p) * (1 - q) ->
  q = (s * (1 - r)) / (1 - p).
Proof.
move=> p1unit /pq_sr /[apply] /(congr1 ( *%R (1 - p)^-1)).
by rewrite mulrA mulVr// mul1r mulrC.
Qed.

Lemma rE (R : unitRingType) (p r s : R) :
  s \is a GRing.unit -> p = r * s -> r = p / s.
Proof.
move=> sunit /(congr1 ( *%R^~ s^-1)) ->.
by rewrite -mulrA divrr// mulr1.
Qed.

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

Let avg p (a b : E) := p%:inum *: a + `1-(p%:inum) *: b.

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
  a <| t |> b = t%:inum * a + `1-(t%:inum) * b.
Proof. by []. Qed.

Lemma convR_itv (a b : R^o) (t : {i01 R}) : a <= b -> a <| t |> b \in `[a, b].
Proof.
move=> ab; rewrite convRE in_itv /=.
rewrite -{1}(subrKC a b).
rewrite mulrDr addrA -mulrDl.
rewrite subrKC mul1r.
rewrite lerDl mulr_ge0/=; [|by rewrite subr_ge0 le1|by rewrite subr_ge0].
rewrite -[leRHS](convmm t b) convRE lerD//.
by rewrite ler_wpM2l.
Qed.

Let convRCE (a b : R^o) (t : {i01 R}) :
  a <| t |> b = `1-(t%:inum) * b + t%:inum * a.
Proof. by rewrite addrC convRE. Qed.

Lemma convR_line_path (a b : R^o) (t : {i01 R}) :
  a <| t |> b = line_path b a t%:num.
Proof. by rewrite convRCE. Qed.

End conv_numDomainType.

Definition convex_function (R : realType) (D : set R) (f : R -> R^o) :=
  forall (t : {i01 R}),
    {in D &, forall (x y : R^o), (f (x <| t |> y) <= f x <| t |> f y)%R}.
(* TODO: generalize to convTypes once we have ordered convTypes (mathcomp 2) *)

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.
Context {R : realType}.
Variables (f : R -> R^o) (a b : R^o).

Let Df := 'D_1 f.
Let DDf := 'D_1 Df.

Hypothesis DDf_ge0 : forall x, a < x < b -> 0 <= DDf x.
Hypothesis cvg_left : (f @ b^'-) --> f b.
Hypothesis cvg_right : (f @ a^'+) --> f a.

Let L x := f a + factor a b x * (f b - f a).

Let LE x : a < b -> L x = factor b a x * f a + factor a b x * f b.
Proof.
move=> ab; rewrite /L -(@onem_factor _ a) ?lt_eqF// /onem mulrBl mul1r.
by rewrite -addrA -mulrN -mulrDr (addrC (f b)).
Qed.

Let convexf_ptP : a < b -> (forall x, a <= x <= b -> 0 <= L x - f x) ->
  forall t, f (a <| t |> b) <= f a <| t |> f b.
Proof.
move=> ba h t; set x := a <| t |> b; have /h : a <= x <= b.
  by have:= convR_itv t (ltW ba); rewrite in_itv/=.
rewrite subr_ge0 => /le_trans; apply.
by rewrite LE// /x {2}convC 2!convR_line_path !line_pathK//= ?(eq_sym b) lt_eqF.
Qed.

Hypothesis HDf : {in `]a, b[, forall x, derivable f x 1}.
Hypothesis HDDf : {in `]a, b[, forall x, derivable Df x 1}.

Let cDf : {within `]a, b[, continuous Df}.
Proof. by apply: derivable_within_continuous => z zab; exact: HDDf. Qed.

Lemma second_derivative_convex (t : {i01 R}) : a <= b ->
  f (a <| t |> b) <= f a <| t |> f b.
Proof.
rewrite le_eqVlt => /predU1P[<-|/[dup] ab]; first by rewrite !convmm.
move/convexf_ptP; apply => x /andP[].
rewrite le_eqVlt => /predU1P[<-|ax].
  by rewrite /L factorl mul0r addr0 subrr.
rewrite le_eqVlt => /predU1P[->|xb].
  by rewrite /L factorr ?lt_eqF// mul1r addrAC addrA subrK subrr.
have [c2 Ic2 Hc2] : exists2 c2, x < c2 < b & (f b - f x) / (b - x) = 'D_1 f c2.
  have xbf : {in `]x, b[, forall z, derivable f z 1} :=
    in1_subset_itv (subset_itvW _ _ (ltW ax) (lexx b)) HDf.
  have derivef z : z \in `]x, b[ -> is_derive z 1 f ('D_1 f z).
    by move=> zxb; apply/derivableP/xbf; exact: zxb.
  have [|z zxb fbfx] := MVT xb derivef.
    apply/(derivable_oo_continuous_bnd_within (And3 xbf _ cvg_left)).
    apply/cvg_at_right_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//.
    by apply; rewrite inE/= in_itv/= ax.
  by exists z => //; rewrite fbfx -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have [c1 Ic1 Hc1] : exists2 c1, a < c1 < x & (f x - f a) / (x - a) = 'D_1 f c1.
  have axf : {in `]a, x[, forall z, derivable f z 1} :=
    in1_subset_itv (subset_itvW _ _ (lexx a) (ltW xb)) HDf.
  have derivef z : z \in `]a, x[ -> is_derive z 1 f ('D_1 f z).
    by move=> zax; apply /derivableP/axf.
  have [|z zax fxfa] := MVT ax derivef.
    apply/(derivable_oo_continuous_bnd_within (And3 axf cvg_right _)).
    apply/cvg_at_left_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//.
    by apply; rewrite inE/= in_itv/= ax.
  exists z; first by [].
  by rewrite fxfa -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have c1c2 : c1 < c2.
  by move: Ic2 Ic1 => /andP[+ _] => /[swap] /andP[_] /lt_trans; apply.
have [d Id h] :
    exists2 d, c1 < d < c2 & ('D_1 f c2 - 'D_1 f c1) / (c2 - c1) = DDf d.
  have h : {in `]c1, c2[, forall z, derivable Df z 1}.
    apply: (in1_subset_itv (subset_itvW _ _ (ltW (andP Ic1).1) (lexx _))).
    apply: (in1_subset_itv (subset_itvW _ _ (lexx _) (ltW (andP Ic2).2))).
    exact: HDDf.
  have derivef z : z \in `]c1, c2[ -> is_derive z 1 Df ('D_1 Df z).
    by move=> zc1c2; apply/derivableP/h.
  have [|z zc1c2 {}h] := MVT c1c2 derivef.
    apply: (derivable_oo_continuous_bnd_within (And3 h _ _)).
    + apply: cvg_at_right_filter.
      move: cDf; rewrite continuous_open_subspace//.
      by apply; rewrite inE/= in_itv/= (andP Ic1).1 (lt_trans _ (andP Ic2).2).
    + apply: cvg_at_left_filter.
      move: cDf; rewrite continuous_open_subspace//.
      by apply; rewrite inE/= in_itv/= (andP Ic2).2 (lt_trans (andP Ic1).1).
  exists z; first by [].
  rewrite h -mulrA divff; first exact: mulr1.
  by rewrite subr_eq0 gt_eqF.
have LfE : L x - f x =
    ((x - a) * (b - x)) / (b - a) * ((f b - f x) / (b - x)) -
    ((b - x) * factor a b x) * ((f x - f a) / (x - a)).
  rewrite !mulrA -(mulrC (b - x)) -(mulrC (b - x)^-1) !mulrA.
  rewrite mulVf ?mul1r ?subr_eq0 ?gt_eqF//.
  rewrite -(mulrC (x - a)) -(mulrC (x - a)^-1) !mulrA.
  rewrite mulVf ?mul1r ?subr_eq0 ?gt_eqF//.
  rewrite -/(factor a b x).
  rewrite -(opprB a b) -(opprB x b) invrN mulrNN -/(factor b a x).
  rewrite -(@onem_factor _ a) ?lt_eqF//.
  rewrite /onem mulrBl mul1r opprB addrA -mulrDr addrA subrK.
  by rewrite /L -addrA addrC opprB -addrA (addrC (f a)).
have {Hc1 Hc2} -> : L x - f x = (b - x) * (x - a) * (c2 - c1) / (b - a) *
                                (('D_1 f c2 - 'D_1 f c1) / (c2 - c1)).
  rewrite LfE Hc2 Hc1.
  rewrite -(mulrC (b - x)) mulrA -mulrBr.
  rewrite (mulrC ('D_1 f c2 - _)) ![in RHS]mulrA; congr *%R.
  rewrite -2!mulrA; congr *%R.
  by rewrite mulrCA divff ?mulr1// subr_eq0 gt_eqF.
rewrite {}h mulr_ge0//; last first.
  rewrite DDf_ge0//; apply/andP; split.
    by rewrite (lt_trans (andP Ic1).1)//; case/andP : Id.
  by rewrite (lt_trans (andP Id).2)//; case/andP : Ic2.
rewrite mulr_ge0// ?invr_ge0 ?subr_ge0 ?(ltW ab)//.
rewrite mulr_ge0// ?subr_ge0 ?(ltW c1c2)//.
by rewrite mulr_ge0// subr_ge0 ltW.
Qed.

End twice_derivable_convex.
