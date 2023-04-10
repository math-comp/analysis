(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions cardinality mathcomp_extra.
Require Import ereal reals signed topology prodnormedzmodule.
Require Import normedtype derive set_interval itv.
From HB Require Import structures.

(******************************************************************************)
(*                                Convexity                                   *)
(*                                                                            *)
(* This file provides a small account of convexity using convex spaces, to be *)
(* completed with material from infotheo.                                     *)
(*                                                                            *)
(*   isConvexSpace R T == interface for convex spaces                         *)
(*       ConvexSpace R == structure of convex space                           *)
(*         a <| t |> b == convexity operator                                  *)
(* E : lmodType R with R : realDomainType and R : realDomainType are shown to *)
(* be convex spaces                                                           *)
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

Lemma cvg_at_right_filter (R : numFieldType) (V : topologicalType)
  (f : R -> V) (x : R) :
  f z @[z --> x] --> f x -> f z @[z --> x^'+] --> f x.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_left_filter (R : numFieldType)
  (K : numDomainType) (V : pseudoMetricNormedZmodType K)
  (f : R -> V) (x : R) :
  f z @[z --> x] --> f x -> f z @[z --> x^'-] --> f x.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma derivable_oo_itvW {R : numFieldType} (V : normedModType R)
    (f : R -> V) (a b a' b' : R) :
    a <= a' -> b' <= b ->
  {in `]a, b[, forall x, derivable f x 1} ->
  {in `]a', b'[, forall x, derivable f x 1}.
Proof. by move=> aa' bb' + x xab; apply; exact: subset_itvW xab. Qed.

Lemma derivable_within_continuous {R : numFieldType} (V : normedModType R)
    (F : R -> V) (i : interval R) :
  {in i, forall x, derivable F x 1} ->
  {within [set` i], continuous F}.
Proof.
move=> di; apply/continuous_in_subspaceT => z /[1!inE] zA.
apply/differentiable_continuous; rewrite -derivable1_diffP.
by apply: di; rewrite inE.
Qed.

Lemma cvg_at_right_within (R : numFieldType)
  (K : numDomainType) (V : pseudoMetricNormedZmodType K) (F : R -> V) (x : R) :
  F x @[x --> x^'+] --> F x ->
  F x @[x --> within (fun u => x <= u) (nbhs x)] --> F x.
Proof.
move=> Fxr; apply/cvgrPdist_lt => e e0.
rewrite /at_right in Fxr; move/cvgrPdist_lt : Fxr => /(_ _ e0).
rewrite !near_withinE; apply: filterS => y h.
by rewrite le_eqVlt => /predU1P[->|//]; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma cvg_at_left_within (R : numFieldType)
  (K : numDomainType) (V : pseudoMetricNormedZmodType K) (F : R -> V) (y : R) :
  F x @[x --> y^'-] --> F y ->
  F x @[x --> within (fun u => u <= y) (nbhs y)] --> F y.
Proof.
move=> Fyl; apply/cvgrPdist_lt => e e0.
rewrite /at_left in Fyl; move/cvgrPdist_lt : Fyl => /(_ _ e0).
rewrite !near_withinE; apply: filterS => x h.
by rewrite le_eqVlt => /predU1P[->|//]; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma derivable_oo_within_cc_continuous {R : numFieldType} {V : normedModType R}
  (F : R -> V) (x y : R):
    {in `]x, y[, forall x, derivable F x 1} ->
  F @ x^'+ --> F x -> F @ y^'- --> F y -> {within `[x, y], continuous F}.
Proof.
move=> Fxy Fxr Fyl; apply/subspace_continuousP => z /=.
rewrite in_itv/= => /andP[]; rewrite le_eqVlt => /predU1P[<-{z} xy|].
  have := cvg_at_right_within Fxr; apply: cvg_trans; apply: cvg_app.
  by apply: within_subset => z/=; rewrite in_itv/= => /andP[].
move=> /[swap].
rewrite le_eqVlt => /predU1P[->{z} xy|zy xz].
  have := cvg_at_left_within Fyl; apply: cvg_trans; apply: cvg_app.
  by apply: within_subset => z/=; rewrite in_itv/= => /andP[].
apply: cvg_within_filter.
apply/differentiable_continuous; rewrite -derivable1_diffP.
by apply: Fxy; rewrite in_itv/= xz zy.
Unshelve. all: by end_near. Qed.

Declare Scope convex_scope.

Local Open Scope convex_scope.

HB.mixin Record isConvexSpace (R : realDomainType) (T : Type) := {
  convexspacechoiceclass : Choice.class_of T ;
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
  {T of isConvexSpace R T }.

Canonical conv_eqType (R : realDomainType) (T : convType R) :=
  Eval hnf in EqType (ConvexSpace.sort T) convexspacechoiceclass.
Canonical conv_choiceType (R : realDomainType) (T : convType R) :=
  Eval hnf in ChoiceType (ConvexSpace.sort T) convexspacechoiceclass.
Coercion conv_choiceType : convType >-> choiceType.

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

Section lmodType_convex_space.
Context {R : realDomainType} {E : lmodType R}.
Implicit Type p q r : {i01 R}.

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

HB.instance Definition _ :=
  @isConvexSpace.Build R E (Choice.class _) avg avg0 avgI avgC avgA.

End lmodType_convex_space.

Section realDomainType_convex_space.
Context {R : realDomainType}.
Implicit Types p q : {i01 R}.

Let avg p (a b : [the lmodType R of R^o]) := a <| p |> b.

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
  (Choice.class _) _ avg0 avgI avgC avgA.

End realDomainType_convex_space.

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.
Context {R : realType}.
Variables (f : R -> R^o) (a b : R^o).
Hypothesis ab : a < b.

Let Df := 'D_1 f.
Let DDf := 'D_1 Df.

Hypothesis DDf_ge0 : forall x, a < x < b -> 0 <= DDf x.
Hypothesis cvg_left : (f @ b^'-) --> f b.
Hypothesis cvg_right : (f @ a^'+) --> f a.

Let L x := f a + factor a b x * (f b - f a).

Let LE x : L x = factor b a x * f a + factor a b x * f b.
Proof.
rewrite /L -(@onem_factor _ a) ?lt_eqF// /onem mulrBl mul1r.
by rewrite -addrA -mulrN -mulrDr (addrC (f b)).
Qed.

Let convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x) ->
  forall t, f (a <| t |> b) <= f a <| t |> f b.
Proof.
move=> h t; set x := a <| t |> b; have /h : a <= x <= b.
  by rewrite -(conv1 a b) -{1}(conv0 a b) /x !le_line_path//= itv_ge0/=.
rewrite subr_ge0 => /le_trans; apply.
by rewrite LE /x line_pathK ?lt_eqF// convC line_pathK ?gt_eqF.
Qed.

Hypothesis HDf : {in `]a, b[, forall x, derivable f x 1}.
Hypothesis HDDf : {in `]a, b[, forall x, derivable Df x 1}.

Let cDf : {within `]a, b[, continuous Df}.
Proof. by apply: derivable_within_continuous => z zab; exact: HDDf. Qed.

Lemma second_derivative_convexf_pt (t : {i01 R}) :
  f (a <| t |> b) <= f a <| t |> f b.
Proof.
apply/convexf_ptP => x /andP[].
rewrite le_eqVlt => /predU1P[<-|ax].
  by rewrite /L factorl mul0r addr0 subrr.
rewrite le_eqVlt => /predU1P[->|xb].
  by rewrite /L factorr ?lt_eqF// mul1r addrAC addrA subrK subrr.
have [c2 Ic2 Hc2] : exists2 c2, x < c2 < b & (f b - f x) / (b - x) = 'D_1 f c2.
  have xbf : {in `]x, b[, forall z, derivable f z 1} :=
    derivable_oo_itvW (ltW ax) (lexx _) HDf.
  have derivef z : z \in `]x, b[ -> is_derive z 1 f ('D_1 f z).
    by move=> zxb; apply/derivableP/xbf; exact: zxb.
  have [|z zxb fbfx] := MVT xb derivef.
    apply/(derivable_oo_within_cc_continuous xbf _ cvg_left)/cvg_at_right_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= ax.
  by exists z => //; rewrite fbfx -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have [c1 Ic1 Hc1] : exists2 c1, a < c1 < x & (f x - f a) / (x - a) = 'D_1 f c1.
  have axf : {in `]a, x[, forall z, derivable f z 1} :=
    derivable_oo_itvW (lexx _ ) (ltW xb) HDf.
  have derivef z : z \in `]a, x[ -> is_derive z 1 f ('D_1 f z).
    by move=> zax; apply /derivableP/axf.
  have [|z zax fxfa] := MVT ax derivef.
    apply/(derivable_oo_within_cc_continuous axf cvg_right)/cvg_at_left_filter.
    have := derivable_within_continuous HDf.
    rewrite continuous_open_subspace//; last exact: interval_open.
    by apply; rewrite inE/= in_itv/= ax.
  by exists z => //; rewrite fxfa -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have c1c2 : c1 < c2.
  by move: Ic2 Ic1 => /andP[+ _] => /[swap] /andP[_] /lt_trans; apply.
have [d Id h] :
    exists2 d, c1 < d < c2 & ('D_1 f c2 - 'D_1 f c1) / (c2 - c1) = DDf d.
  have h : {in `]c1, c2[, forall z, derivable Df z 1}.
    exact/(derivable_oo_itvW (ltW (andP Ic1).1) (lexx _))
         /(derivable_oo_itvW (lexx _) (ltW (andP Ic2).2)).
  have derivef z : z \in `]c1, c2[ -> is_derive z 1 Df ('D_1 Df z).
    by move=> zc1c2; apply/derivableP/h.
  have [|z zc1c2 {}h] := MVT c1c2 derivef.
    apply: (derivable_oo_within_cc_continuous h).
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
