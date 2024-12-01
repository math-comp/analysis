(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets set_interval.
From mathcomp Require Import functions cardinality ereal reals.
From mathcomp Require Import topology prodnormedzmodule normedtype derive.
From mathcomp Require Import realfun itv.
From HB Require Import structures.

(**md**************************************************************************)
(* # Convexity                                                                *)
(*                                                                            *)
(* This file provides a small account of convexity using convex spaces, to be *)
(* completed with material from infotheo.                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*   isConvexSpace R T == interface for convex spaces                         *)
(*       ConvexSpace R == structure of convex space                           *)
(*         a <| t |> b == convexity operator                                  *)
(* ```                                                                        *)
(*                                                                            *)
(* E : lmodType R with R : realDomainType and R : realDomainType are shown to *)
(* be convex spaces with the following aliases:                               *)
(*       convex_lmodType E == E : lmodType T as a convex spaces               *)
(* convex_realDomainType R == R : realDomainType as a convex space            *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x <| p |> y" (format "x  <| p |>  y", at level 49).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

Declare Scope convex_scope.
Local Open Scope convex_scope.

HB.mixin Record isConvexSpace (R : realDomainType) T := {
  conv : {i01 R} -> T -> T -> T ;
  conv0 : forall a b, conv 0%:i01 a b = a ;
  convmm : forall (p : {i01 R}) a, conv p a a = a ;
  convC : forall (p : {i01 R}) a b, conv p a b = conv (1 - p%:inum)%:i01 b a;
  convA : forall (p q r : {i01 R}) (a b c : T),
    p%:inum * (`1-(q%:inum)) = (`1-(p%:inum * q%:inum)) * r%:inum ->
    conv p a (conv q b c) = conv (p%:inum * q%:inum)%:i01 (conv r a b) c
}.

#[short(type=convType)]
HB.structure Definition ConvexSpace (R : realDomainType) :=
  {T of isConvexSpace R T & Choice T}.

Notation "a <| p |> b" := (conv p a b) : convex_scope.

Section convex_space_lemmas.
Context R (A : convType R).
Implicit Types a b : A.

Lemma conv1 a b : a <| 1%:i01 |> b = b.
Proof.
rewrite convC/= [X in _ <| X |> _](_ : _ = 0%:i01) ?conv0//.
by apply/val_inj => /=; rewrite subrr.
Qed.

End convex_space_lemmas.

Local Open Scope convex_scope.

Definition convex_lmodType {R : realDomainType} (E : lmodType R) : Type := E.

Section lmodType_convex_space.
Context {R : realDomainType} {E' : lmodType R}.
Implicit Type p q r : {i01 R}.

Let E := convex_lmodType E'.

Let avg p (a b : E) := `1-(p%:inum) *: a + p%:inum *: b.

Let avg0 a b : avg 0%:i01 a b = a.
Proof. by rewrite /avg/= onem0 scale0r scale1r addr0. Qed.

Let avgI p x : avg p x x = x.
Proof. by rewrite /avg -scalerDl/= addrC add_onemK scale1r. Qed.

Let avgC p x y : avg p x y = avg (1 - (p%:inum))%:i01 y x.
Proof. by rewrite /avg onemK addrC. Qed.

Let avgA p q r (a b c : E) :
  p%:inum * (`1-(q%:inum)) = (`1-(p%:inum * q%:inum)) * r%:inum ->
  avg p a (avg q b c) = avg (p%:inum * q%:inum)%:i01 (avg r a b) c.
Proof.
move=> pq; rewrite /avg.
rewrite [in LHS]scalerDr [in LHS]addrA [in RHS]scalerDr; congr (_ + _ + _).
- rewrite scalerA; congr (_ *: _) => /=.
  by rewrite mulrDr mulr1 mulrN -pq mulrBr mulr1 opprB addrA subrK.
- by rewrite 2!scalerA; congr (_ *: _).
- by rewrite scalerA.
Qed.

HB.instance Definition _ := Choice.on E.

HB.instance Definition _ :=
  isConvexSpace.Build R E avg0 avgI avgC avgA.

End lmodType_convex_space.

Definition convex_realDomainType (R : realDomainType) : Type := R^o.

Section realDomainType_convex_space.
Context {R : realDomainType}.
Implicit Types p q : {i01 R}.

Let E := @convex_realDomainType R.

Let avg p (a b : convex_lmodType R^o) := a <| p |> b.

Let avg0 a b : avg 0%:i01 a b = a.
Proof. by rewrite /avg conv0. Qed.

Let avgI p x : avg p x x = x.
Proof. by rewrite /avg convmm. Qed.

Let avgC p x y : avg p x y = avg (1 - (p%:inum))%:i01 y x.
Proof. by rewrite /avg convC. Qed.

Let avgA p q r (a b c : R) :
  p%:inum * (`1-(q%:inum)) = (`1-(p%:inum * q%:inum)) * r%:inum ->
  avg p a (avg q b c) = avg (p%:inum * q%:inum)%:i01 (avg r a b) c.
Proof. by move=> h; rewrite /avg (convA _ _ r). Qed.

HB.instance Definition _ := @isConvexSpace.Build R R^o
  _ avg0 avgI avgC avgA.

End realDomainType_convex_space.

Section conv_realDomainType.
Context {R : realDomainType}.

Lemma conv_gt0 (a b : R^o) (t : {i01 R}) : 0 < a -> 0 < b -> 0 < a <| t |> b.
Proof.
move=> a0 b0.
have [->|t0] := eqVneq t 0%:i01; first by rewrite conv0.
have [->|t1] := eqVneq t 1%:i01; first by rewrite conv1.
rewrite addr_gt0// mulr_gt0//; last by rewrite lt_neqAle eq_sym t0/=.
by rewrite onem_gt0// lt_neqAle t1/=.
Qed.

Lemma convRE (a b : R^o) (t : {i01 R}) : a <| t |> b = `1-(t%:inum) * a + t%:inum * b.
Proof. by []. Qed.

End conv_realDomainType.

Definition convex_function (R : realType) (D : set R) (f : R -> R^o) :=
  forall (t : {i01 R}), {in D &, forall (x y : R^o), (f (x <| t |> y) <= f x <| t |> f y)%R}.
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
move=> ab h t; set x := a <| t |> b; have /h : a <= x <= b.
  by rewrite -(conv1 a b) -{1}(conv0 a b) /x !le_line_path//= ge0/=.
rewrite subr_ge0 => /le_trans; apply.
by rewrite LE// /x line_pathK ?lt_eqF// convC line_pathK ?gt_eqF.
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
    apply/(derivable_oo_continuous_bnd_within (And3 xbf _ cvg_left))/cvg_at_right_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= ax.
  by exists z => //; rewrite fbfx -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have [c1 Ic1 Hc1] : exists2 c1, a < c1 < x & (f x - f a) / (x - a) = 'D_1 f c1.
  have axf : {in `]a, x[, forall z, derivable f z 1} :=
    in1_subset_itv (subset_itvW _ _ (lexx a) (ltW xb)) HDf.
  have derivef z : z \in `]a, x[ -> is_derive z 1 f ('D_1 f z).
    by move=> zax; apply /derivableP/axf.
  have [|z zax fxfa] := MVT ax derivef.
    apply/(derivable_oo_continuous_bnd_within (And3 axf cvg_right _))/cvg_at_left_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= ax.
  by exists z => //; rewrite fxfa -mulrA divff ?mulr1// subr_eq0 gt_eqF.
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
      move: cDf; rewrite continuous_open_subspace//; last exact: interval_open.
      by apply; rewrite inE/= in_itv/= (andP Ic1).1 (lt_trans _ (andP Ic2).2).
    + apply: cvg_at_left_filter.
      move: cDf; rewrite continuous_open_subspace//; last exact: interval_open.
      by apply; rewrite inE/= in_itv/= (andP Ic2).2 (lt_trans (andP Ic1).1).
  by exists z => //; rewrite h -mulrA divff ?mulr1// subr_eq0 gt_eqF.
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
