
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(*Require Import ssrsearch.*)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool fieldext falgebra vector.
From mathcomp Require Import ssrnat eqtype seq choice fintype bigop order.
From mathcomp Require Import ssralg ssrnum ssrfun matrix complex.
From mathcomp Require Import unstable boolp reals ereal derive.
From mathcomp Require Import classical_sets functions interval_inference.
From mathcomp Require Import topology normedtype landau.

(**md**************************************************************************)
(* # Holomorphic functions                                                    *)
(*                                                                            *)
(* This file develops the theory of holomorphic functions. We endow complex   *)
(* (denoted C below) and Rcomplex with structures of normedModType. We prove  *)
(* that the holomorphic functions are the R-differentiable functions from C   *)
(* to C satisfying the Cauchy-Riemann equation.                               *)
(*                                                                            *)
(*          holomorphic f == f is holomorphic, i.e. C-derivable               *)
(*      Rdifferentiable f == f is differentiable on Rcomplex                  *)
(*    CauchyRiemannEq f c == The Cauchy-Riemman equation for f at point c     *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

HB.instance Definition _ (R : rcfType) := NormedModule.copy R[i] R[i]^o.
HB.instance Definition _ (R : rcfType) := UniformZmodule.copy R[i] R[i]^o.

HB.instance Definition _ (R : rcfType) := UniformZmodule.copy (Rcomplex R) R[i].
HB.instance Definition _ (R : rcfType) := Pointed.copy (Rcomplex R) R[i].

Module Rcomplex_NormedModType.
Section Rcomplex_NormedModType.
Variable (R : rcfType).

Definition ball_Rcomplex : Rcomplex R -> R -> Rcomplex R -> Prop :=
  ball_ Num.norm.

Lemma entourage_RcomplexE : entourage = entourage_ ball_Rcomplex.
Proof.
rewrite entourage_nbhsE/= eqEsubset.
split; apply/subsetP => U; rewrite inE => -[].
  move=> V []/= e; rewrite ltcE => /andP[]/eqP/= ei0 e0.
  have ->: e = (Re e)%:C by case: e ei0 {e0} => r i/= ->.
  move=> /subsetP eV /subsetP VU.
  rewrite inE; exists (Re e) => //.
  apply/subsetP => -[] a b; rewrite inE/= /ball/= => abe.
  by apply: VU; rewrite inE/=; apply: eV; rewrite inE/= add0r opprB ltcR.
move=> e/= e0 /subsetP eU.
rewrite inE; exists (ball_Rcomplex 0 e).
  exists e%:C; first by rewrite /= ltcR.
  by apply/subsetP => x; rewrite !inE/= ltcR.
apply/subsetP => x; rewrite inE/= inE /ball_Rcomplex/= add0r opprB => xe.
by apply: eU; rewrite inE.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R (Rcomplex R)
  ball_norm_center ball_norm_symmetric ball_norm_triangle entourage_RcomplexE.
HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build R (Rcomplex R) erefl.

Lemma normcZ (l : R) (x : Rcomplex R) : `|l *: x| = `|l| * `|x|.
Proof.
by case: x => ??; rewrite /normr/= !exprMn -mulrDr sqrtrM ?sqr_ge0// sqrtr_sqr.
Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build R (Rcomplex R) normcZ.

Lemma Rcomplex_findim : Vector.axiom 2 (Rcomplex R).
Proof.
exists (fun x => \row_(i < 2) [:: Re x; Im x]`_i).
  move=> r x y; apply/rowP; move=> i /=; rewrite !mxE.
  case: i => i /=; rewrite ltnS leq_eqVlt => /orP[/eqP ->/=|].
    by rewrite raddfD/= linearZ.
  by rewrite ltnS leqn0 => /eqP -> /=; rewrite raddfD/= linearZ.
apply: (@Bijective _ _ _ (fun x : 'rV_2 => x ord0 ord0 +i* x ord0 ord_max)).
  by case=> x y; rewrite !mxE.
move=> x; apply/rowP => i; rewrite mxE/=.
case: i => i /[dup] + ilt; rewrite ltnS leq_eqVlt => /orP[/eqP /= i1|].
  by rewrite {1}i1/=; congr (x ord0); apply: val_inj.
rewrite ltnS leqn0 => /eqP i0/=.
by rewrite {1}i0/=; congr (x ord0); apply: val_inj.
Qed.

HB.instance Definition _ :=
  Lmodule_hasFinDim.Build R (Rcomplex R) Rcomplex_findim.

End Rcomplex_NormedModType.
End Rcomplex_NormedModType.

Section Holomorphe_der.
Variable R : realType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Rc := (Rcomplex R).

Definition holomorphic (f : C -> C) (c : C) :=
  cvg ((fun h => h^-1 *: (f (c + h) - f c)) @ 0^').

Lemma holomorphicP (f : C -> C) (c : C) : holomorphic f c <-> derivable f c 1.
Proof.
rewrite /holomorphic /derivable.
suff ->: (fun h : C => h^-1 *: ((f (c + h) - f c))) =
         ((fun h : C => h^-1 *: ((f \o shift c) (h *: 1) - f c))) by [].
by apply: funext => h; rewrite complexA [X in f X]addrC.
Qed.

Definition Rdifferentiable (f : C -> C) (c : C) := differentiable f%:Rfun c%:Rc.

Definition realC : R -> C := (fun r => r%:C).

Lemma continuous_realC: continuous realC.
Proof.
move=> x A /= [] r /[dup] /realC_gt0 Rer0 /gt0_realC rRe H; exists (Re r) => //.
by move=> z /= nz; apply: (H z%:C); rewrite /= -raddfB realC_norm rRe ltcR.
Qed. 

Lemma Rdiff1 (f : C -> C) c :
  lim ((fun h : C => h^-1 *: ((f (c + h) - f c))) @ (realC @ 0^'))
  = 'D_1 (f%:Rfun) c%:Rc.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : C => h^-1 *: ((f (c + h) - f c)))
                  \o realC @ 0^')).
suff ->: (fun h : C => h^-1 *: (f (c + h) - f c)) \o realC
  = fun h : R => h^-1 *: ((f \o shift c) (h *: (1%:Rc)) - f c)%:Rc.
  by [].
apply: funext => h /=.
by rewrite -fmorphV /= -!scalecr realC_alg [X in f X]addrC.
Qed.

Lemma Rdiffi (f : C -> C) c:
  lim ((fun h : C => h^-1 *: ((f (c + h * 'i) - f c))) @ (realC @ 0^'))
  = 'D_('i) (f%:Rfun) c%:Rc.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : (R[i]) => h^-1 *: (f (c + h * 'i) - f c))
                  \o realC @ 0^')).
suff -> : (fun h : (R[i]) => h^-1 * (f (c + h * 'i) - f c)) \o realC
  = fun h : R => h^-1 *: ((f \o shift c) (h *: ('i%:Rc)) - f c)%:Rc.
  by [].
apply: funext => h /=.
by rewrite -fmorphV -scalecE -!scalecr realCZ [X in f X]addrC.
Qed.

(* should be generalized to equivalent norms *)
(* but there is no way to state it for now *)
Lemma littleoCo (h e : C -> C) (x : C) :
   [o_x (e : C -> C) of (h : C -> C)] =
   [o_x (e : Rc -> Rc) of (h : Rc -> Rc)].
Proof.
suff heP : (h : C -> C) =o_x (e : C -> C) <->
           (h : Rc -> Rc) =o_x (e : Rc -> Rc).
  have [ho|hNo] := asboolP ((h : C -> C) =o_x (e : C -> C)).
    by rewrite !littleoE// -!eqoP// -heP.
  by rewrite !littleoE0// -!eqoP// -heP.
rewrite !eqoP; split => small/= _ /posnumP[eps]; near=> y.
  rewrite -lecR/= rmorphM/=.
  near: y.
  by apply: small; rewrite ltcR.
rewrite -[_%:num]ger0_norm// -rmorphM/= lecR.
by near: y; apply: small; rewrite (@normr_gt0 _ (Rcomplex R))//.
Unshelve. all: by end_near. Qed.

Definition CauchyRiemannEq (f : C -> C) c :=
  'i * 'D_1 f%:Rfun c%:Rc = 'D_('i) f%:Rfun c%:Rc.

Lemma holo_differentiable (f : C -> C) (c : C) :
  holomorphic f c -> Rdifferentiable f c.
Proof.
move=> /holomorphicP /derivable1_diffP /diff_locallyP => -[cdiff holo].
pose df : Rc -> Rc := 'd f c.
have lDf : linear df by move=> t u v; rewrite /df !scalecr linearP.
pose df' : {linear Rc -> Rc} :=
  HB.pack df (GRing.isLinear.Build _ _ _ _ df lDf).
apply/diff_locallyP; split; first exact: linear_findim_continuous.
have eqdf : f%:Rfun \o +%R^~ c = cst (f c) + df' +o_ (0 : Rc) id.
  rewrite [LHS]holo /df'/=/df/=.
  congr (_ + _).
  exact: littleoCo.
rewrite (@diff_unique R (Rcomplex R) (Rcomplex R) _ df' _ _ eqdf).
  exact: eqdf.
exact: linear_findim_continuous.
(* TODO: fix Qed performance issue (which is due to the proof of `eqdf`).
  3.684s *)
Qed.

Lemma holo_CauchyRiemann (f : C -> C) c: holomorphic f c -> CauchyRiemannEq f c.
Proof.
move=> /cvg_ex; rewrite //= /CauchyRiemannEq. rewrite -Rdiff1 -Rdiffi.
set quotC : C -> C := fun h : R[i] => h^-1 *: (f (c + h) - f c).
set quotR : C -> C:= fun h => h^-1 *: (f (c + h * 'i) - f c) .
move => /= [l H].
have -> :  quotR @ (realC @ 0^') =  (quotR \o realC) @ 0^' by [].
have realC'0:  realC @ 0^' --> 0^'.
  rewrite -[0 in X in _ --> X]/(realC 0).
  apply: within_continuous_withinNx; first by apply: continuous_realC.
  by move => /= x /complexI.
have HR0:(quotC \o (realC) @ 0^')  --> l.
 by apply: cvg_comp; last by exact: H.
have lem : quotC \o  *%R^~ 'i%R @ (realC @ (0 : R)^') --> l.
  apply: cvg_comp; last by exact: H.
  apply: (@cvg_comp _ _ _ realC ( *%R^~ 'i)); first by exact: realC'0.
  rewrite -[0 in X in _ `=>` X](mul0r 'i%C).
  apply: within_continuous_withinNx; first exact: scalel_continuous.
  move=> x /eqP; rewrite mul0r mulIr_eq0; last by apply/rregP; apply: neq0Ci.
  exact: eqP.
have HRcomp: cvg (quotC \o *%R^~ 'i%R @ (realC @ ((0 : R)^'))) .
  by apply/cvg_ex; simpl; exists l.
have ->: lim (quotR @ (realC @ ((0 : R)^')))
  = 'i *: lim (quotC \o ( fun h => h *'i) @ (realC @ ((0 : R)^'))).
  have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR.
  move=> h /=; rewrite /quotC /quotR /=.
  rewrite invfM scalerA mulrC -mulrA mulVf ?mulr1 ?neq0Ci //.
  by move=> /funext <-; rewrite limZr.
rewrite scalecE.
suff ->: lim (quotC @ (realC @ ((0 : R)^')))
      = lim (quotC \o  *%R^~ 'i%R @ (realC @ ((0 : R)^'))) by [].
suff ->: lim (quotC @ (realC @ ((0 : R)^'))) = l.
  by apply/eqP; rewrite eq_sym; apply/eqP; apply: (cvg_lim _ lem).
by apply: cvg_lim; last exact: HR0.
Qed.

Lemma Diff_CR_holo (f : C -> C) (c : C):
  (Rdifferentiable f c) /\ (CauchyRiemannEq f c) -> (holomorphic f c).
Proof.
move=> [] /= /[dup] H /diff_locallyP => [[derc diff]] CR.
apply/holomorphicP/derivable1_diffP/diff_locallyP.
pose Df := (fun h : C => h *: ('D_1 f%:Rfun c : C)).
have lDf : linear Df by move=> t u v /=; rewrite /Df scalerDl scalerA scalecE.
pose df : {linear R[i] -> R[i]} :=
  HB.pack Df (GRing.isLinear.Build _ _ _ _ Df lDf).
have cdf : continuous df by apply: scalel_continuous.
have lem : Df = 'd (f%:Rfun) (c : Rc). (* issue with notation *)
  apply: funext => z; rewrite  /Df.
  set x := Re z; set y := Im z.
  have zeq : z = x *: 1 %:Rc + y *: 'i%:Rc.
  by rewrite [LHS]complexE /= realC_alg scalecr scalecE [in RHS]mulrC.
  rewrite [X in 'd _ _ X]zeq addrC linearP linearZ /= -!deriveE //.
  rewrite -CR (scalerAl y) -scalecE !scalecr /=.
  rewrite -(scalerDl  (('D_1 f%:Rfun (c : Rc)) : C) _  (real_complex R x)).
  by rewrite addrC -!scalecr -realC_alg -zeq.
have holo:  f \o shift c = cst (f c) + df +o_ ( 0 : C) id.
  rewrite [LHS]diff /= lem.
  congr (_ + _).
  exact/esym/littleoCo.
by rewrite (diff_unique cdf holo).
(* TODO: fix Qed performance issue (which is due to the proof of `holo`).
  6.519s *)
Qed.

Lemma holomorphic_Rdiff (f : C -> C) (c : C) :
  (Rdifferentiable f c) /\ (CauchyRiemannEq f c) <-> (holomorphic f c).
Proof.
split=> H; first exact: Diff_CR_holo.
split; first exact: holo_differentiable.
exact: holo_CauchyRiemann.
Qed.

End Holomorphe_der.
