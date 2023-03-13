(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions cardinality mathcomp_extra.
Require Import ereal reals signed topology prodnormedzmodule.
Require Import normedtype derive set_interval itv.
From HB Require Import structures.

(******************************************************************************)
(* isConvexSpace R T == interface for convex spaces *)
(* ConvexSpace R == structure of convex space*)
(* a <| t |> b == convexity operator*)
(* E : lmodType R with R : realDomainType and R : realDomainType are shown to be convex spaces *)
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

(* NB: recent addition to MathComp *)
Lemma divrNN (R : unitRingType) (x y: R) : (- x) / (- y) = x / y.
Proof. exact: divrNN. Qed.

(* TODO: move *)
Lemma factorE {R : numDomainType} (a b x : R) : factor a b x = (a - x) / (a - b).
Proof.
by rewrite /factor -(opprB x a) -(opprB b a) invrN mulrNN.
Qed.

(* TODO: move *)
Lemma factor1 {R : numFieldType} (a b x : R) : a != b ->
  factor a b x + factor b a x = 1.
Proof.
move=> ab.
by rewrite factorE /factor -mulrDl addrA subrK divrr// unitfE subr_eq0.
Qed.

(* TODO: move *)
Lemma in_IntervalW d {T : porderType d} (a b c e : T):
  (a <= b)%O -> (c <= e)%O -> forall x, x \in `[b, c] -> x \in `[a, e].
Proof.
move=> ab ce x; rewrite 2!in_itv /= => /andP[bx xc].
by rewrite (le_trans ab)//= (le_trans _ ce).
Qed.

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
HB.structure Definition ConvexSpace (R : realDomainType) := {T of isConvexSpace R T }.

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

Let avgC p x y : avg p x y = avg (`1-(p%:inum))%:i01 y x.
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

Let avgC p x y : avg p x y = avg `1-(p%:inum)%:i01 y x.
Proof. by rewrite /avg convC. Qed.

Let avgA p q r (a b c : R) :
  p%:inum * (`1-(q%:inum)) = (`1-(p%:inum * q%:inum)) * r%:inum ->
  avg p a (avg q b c) = avg (p%:inum * q%:inum)%:i01 (avg r a b) c.
Proof. by move=> h; rewrite /avg (convA _ _ r). Qed.

HB.instance Definition _ := @isConvexSpace.Build R R^o
  (Choice.class _) _ avg0 avgI avgC avgA.

End realDomainType_convex_space.

Definition derivable_interval {R : numFieldType} (f : R -> R) (a b : R) :=
  forall x, x \in `[a, b] -> derivable f x 1.

Lemma derivable_continuous {R : realType} (F : R -> R) (x y : R):
  derivable_interval F x y -> {within `[x, y], continuous F}.
Proof.
move=> di.
have h z : z \in `[x, y] -> {for z, continuous F}.
  move=> zxy; apply/differentiable_continuous.
  by rewrite -derivable1_diffP; exact: di.
by apply/continuous_in_subspaceT => z /[1!inE] zin; exact: h.
Qed.

Lemma derivable_interval_le {R : numFieldType} (f : R -> R) (a b a' : R) :
  a <= a' -> derivable_interval f a b -> derivable_interval f a' b.
Proof.
rewrite /derivable_interval => aa' deriv x xab; apply/deriv.
exact: in_IntervalW xab.
Qed.

Lemma derivable_interval_ge {R : numFieldType} (f : R -> R) (a b b' : R) :
  b >= b' -> derivable_interval f a b -> derivable_interval f a b'.
Proof.
rewrite/derivable_interval => b'b deriv x xab'; apply/deriv.
exact: in_IntervalW xab'.
Qed.

(* ref: http://www.math.wisc.edu/~nagel/convexity.pdf *)
Section twice_derivable_convex.
Context {R : realType}.
Variables (f : R -> R^o) (a b : R^o).
Hypothesis ab : a < b.

Let Df := 'D_1 f.
Let DDf := 'D_1 Df.

Hypothesis DDf_ge0 : forall x, a <= x <= b -> 0 <= DDf x.

Let L x := f a + factor a b x * (f b - f a).

Let LE x : L x = factor b a x * f a + factor a b x * f b.
Proof.
rewrite /L mulrBr [in LHS]addrA addrAC; congr +%R.
rewrite -{1}(mul1r (f a)) -mulrBl; congr *%R.
rewrite -(@mulrV _ (b-a)); last first.
  by move: ab; rewrite unitfE subr_eq0 lt_def => /andP [ba _].
rewrite -factorE.
rewrite factorr ?gt_eqF// -(@factor1 _ a b x) ?lt_eqF//.
by rewrite addrAC subrr add0r.
Qed.

Let convexf_ptP : (forall x, a <= x <= b -> 0 <= L x - f x) ->
  forall t, f (a <| t |> b) <= f a <| t |> f b.
Proof.
move=> H t; set x := a <| t |> b.
have /H : a <= x <= b.
  rewrite -(conv1 (a : R^o) b) -{1}(conv0 (a : R^o) b) /x.
  by rewrite !le_conv//= ge0/=.
rewrite subr_ge0 => /le_trans; apply.
by rewrite LE /x convK ?lt_eqF// convC convK ?gt_eqF.
Qed.

Hypothesis HDf : derivable_interval f a b.
Hypothesis HDDf : derivable_interval Df a b.

Lemma second_derivative_convexf_pt (t : {i01 R}) :
  f (a <| t |> b) <= f a <| t |> f b.
Proof.
apply/convexf_ptP => x /andP[]; rewrite /L.
rewrite le_eqVlt => /predU1P[-> _|ax].
  by rewrite factorl mul0r addr0 subrr lexx.
rewrite le_eqVlt => /predU1P[->|xb].
  by rewrite factorr ?lt_eqF// mul1r addrCA subrr addr0 subrr.
have LfE : L x - f x =
    (x - a) * (b - x) / (b - a) * ((f b - f x) / (b - x)) -
    (b - x) * (x - a) / (b - a) * ((f x - f a) / (x - a)).
  rewrite !mulrA -(mulrC (b - x)) -(mulrC (b - x)^-1) !mulrA.
  rewrite mulVr ?mul1r ?unitfE ?subr_eq0 ?gt_eqF//.
  rewrite -(mulrC (x - a)) -(mulrC (x - a)^-1) !mulrA.
  rewrite mulVr ?mul1r ?unitfE ?subr_eq0 ?gt_eqF//.
  rewrite -factorE -/(factor _ _ _).
  rewrite !mulrBr opprB -!mulrN addrACA -mulrDl factor1 ?mul1r ?lt_eqF//.
  by rewrite LE (addrC (_ * f b)).
have [c2 Ic2 Hc2] : exists2 c2, x < c2 < b & (f b - f x) / (b - x) = 'D_1 f c2.
  have h : derivable_interval f x b := derivable_interval_le (ltW ax) HDf.
  have derivef z : z \in `]x, b[ -> is_derive z 1 f ('D_1 f z).
    by move=> zxb; apply/derivableP/h; exact: subset_itv_oo_cc zxb.
  have [ |z zxb fbfx] := MVT xb derivef; first by apply/derivable_continuous.
  by exists z => //; rewrite fbfx -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have [c1 Ic1 Hc1] : exists2 c1, a < c1 < x & (f x - f a) / (x - a) = 'D_1 f c1.
  have h : derivable_interval f a x := derivable_interval_ge (ltW xb) HDf.
  have derivef z : z \in `]a, x[ -> is_derive z 1 f ('D_1 f z).
    by move=> zax; apply /derivableP/h/subset_itv_oo_cc.
  have [|z zax fxfa] := MVT ax derivef; first exact/derivable_continuous.
  by exists z => //; rewrite fxfa -mulrA divff ?mulr1// subr_eq0 gt_eqF.
have c1c2 : c1 < c2.
  by move: Ic2 Ic1 => /andP[+ _] => /[swap] /andP[_] /lt_trans; apply.
have {LfE Hc1 Hc2}lfE : L x - f x = (b - x) * (x - a) * (c2 - c1) / (b - a) *
                                    (('D_1 f c2 - 'D_1 f c1) / (c2 - c1)).
  rewrite LfE Hc2 Hc1 (mulrC (x - a)%R) -mulrBr -!mulrA.
  congr (_ * (_ * _)); rewrite mulrCA; congr (_ * _).
  by rewrite mulrCA mulrV ?mulr1// unitfE subr_eq0 gt_eqF.
have [d Id h] :
    exists2 d, c1 < d < c2 & ('D_1 f c2 - 'D_1 f c1) / (c2 - c1) = DDf d.
  have h : derivable_interval Df c1 c2.
    exact/(derivable_interval_le (ltW (andP Ic1).1))
         /(derivable_interval_ge (ltW (andP Ic2).2)).
  have derivef z : z \in `]c1, c2[ -> is_derive z 1 Df ('D_1 Df z).
    by move=> zc1c2; apply/derivableP/h/subset_itv_oo_cc.
  have [|z zc1c2 {}h] := MVT c1c2 derivef; first by apply /derivable_continuous.
  by exists z => //; rewrite h -mulrA divff ?mulr1// subr_eq0 gt_eqF.
rewrite {}lfE {}h mulr_ge0//; last first.
  rewrite DDf_ge0//; apply/andP; split.
    by rewrite (le_trans (ltW (andP Ic1).1))// (le_trans (ltW (andP Id).1)).
  by rewrite (le_trans (ltW (andP Id).2))// (le_trans (ltW (andP Ic2).2)).
rewrite mulr_ge0// ?invr_ge0 ?subr_ge0 ?(ltW ab)//.
rewrite mulr_ge0// ?subr_ge0 ?(ltW c1c2)//.
by rewrite mulr_ge0// subr_ge0 ltW.
Qed.

End twice_derivable_convex.
