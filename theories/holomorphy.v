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
Import Normc.

Definition ball_Rcomplex (R : rcfType) : (Rcomplex R) -> R -> set (Rcomplex R) :=
  ball_ (@normc R).

(* beware that Re and complex.Re don't look similar *)
Lemma entourage_RcomplexE : entourage = entourage_ (@ball_Rcomplex R).
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


(* Lemmas to be used generally when norm is redefined *)

#[local] Lemma ler_normcD : forall (x y : Rcomplex R), normc (x + y) <= normc x + normc y.
Proof.
Admitted.

#[local] Lemma normrcMn : forall (x : Rcomplex R) n, normc (x *+ n) = normc x *+ n.
Proof.
Admitted.

#[local] Lemma normrcN : forall (x : Rcomplex R), normc (- x) = normc x.
Proof.
Admitted.

HB.instance Definition _ := @Num.Zmodule_isSemiNormed.Build R (Rcomplex R) (@normc R) ler_normcD normrcMn normrcN.

#[local] Lemma normrc0_eq0 : forall x : Rcomplex R, normc x = 0 -> x = 0.
Proof.
Admitted.

HB.instance Definition _ := @Num.SemiNormedZmodule_isPositiveDefinite.Build R (Rcomplex R) normrc0_eq0.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R (Rcomplex R)
  ball_norm_center ball_norm_symmetric ball_norm_triangle entourage_RcomplexE.
HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build R (Rcomplex R) erefl.

Lemma normcZ (l : R) (x : Rcomplex R) : `|l *: x| = `|l| * `|x|.
Proof.
by case: x => ??; rewrite /normr/= !exprMn -mulrDr sqrtrM ?sqr_ge0// sqrtr_sqr.
Qed.

#[export] HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build R (Rcomplex R) normcZ. 

Check (Rcomplex R : normedModType R). 

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

#[export] HB.instance Definition _ :=
  Lmodule_hasFinDim.Build R (Rcomplex R) Rcomplex_findim.

End Rcomplex_NormedModType.
End Rcomplex_NormedModType.
HB.export Rcomplex_NormedModType.

Section Holomorphe_der.
Variable R : realType.


Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Rc := (Rcomplex R). 
Check (Rcomplex R : normedModType R).
Check (Rcomplex R : vectType R).
Check (Rcomplex R : normedVectType R).


From mathcomp Require Import ssrAC.

Lemma normRcomplex (x : R[i]) : `|x : Rc|%:C = `|x|.
Proof.
by []. 
Qed.

(* TODO: clean lemmas about scalec *)
Lemma scaleCr (h : R) (c : R[i]): h *: (c : Rc) = h%:C *: (c : C^o).
Proof.
by rewrite  scalecE scalerc.
Qed.

Lemma scaleC1 (h : R) : h *: (1 : C^o) = h%:C.
Proof.
by rewrite scaleCr scaler1.
Qed.

(* TODO : put the h at the left *)
Definition holomorphic (f : C -> C) (c : C) :=
  cvg ((fun (h : C) => h^-1 * (f (c + h) - f c)) @ 0^').


Lemma holomorphicP (f : C -> C) (c : C) : holomorphic f c <-> derivable (f : C^o -> C^o) c 1.
Proof.
rewrite /holomorphic /derivable.
suff ->: (fun h : C => h^-1 * ((f (c + h) - f c))) =
         ((fun h : C => h^-1 * ((f \o shift c) (h *: (1 : C^o)) - f c))) by [].
by apply: funext => h; rewrite complexA [X in f X]addrC.
Qed.
  
Definition Rdifferentiable (f : C -> C) (c : C) := differentiable f%:Rfun c%:Rc.

Definition realC : R -> C := (fun r => r%:C).

Lemma continuous_realC: continuous realC.
Proof.
move=> x A /= [] r /[dup] /realC_gt0 Rer0 /gt0_realC rRe H; exists (Re r) => //.
by move=> z /= nz; apply: (H z%:C); rewrite /= -raddfB realC_norm rRe ltcR.
Qed. 

Lemma Rdiff1 (f : C -> C) (c : C) :
  lim ((fun h : C => h^-1 * ((f (c + h) - f c))) @ (realC @ 0^'))
  = 'D_1 (f%:Rfun) c%:Rc.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : C => h^-1 * ((f (c + h) - f c)))
                  \o realC @ 0^')).
suff ->: (fun h : C => h^-1 * (f (c + h) - f c)) \o realC
  = fun h : R => h^-1 *: ((f \o shift c) (h *: (1%:Rc)) - f c)%:Rc.
  by [].
apply: funext => h /=.
by rewrite -fmorphV realC_alg [X in f X]addrC /realC /= scalerc.
Qed.

Lemma Rdiffv (f : C -> C) (v c : C) :
  lim ((fun h : C => h^-1 * ((f (c + h *: (v : C^o)) - f c))) @ (realC @ 0^'))
  = 'D_v (f%:Rfun) c%:Rc.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : C => h^-1 * ((f (c + h *: (v : C^o)) - f c)))
                  \o realC @ 0^')).
suff ->: (fun h : C => h^-1 * (f (c + h *: (v : C^o)) - f c)) \o realC
  = fun h : R => h^-1 *: ((f \o shift c) (h *: (v:Rc)) - f c)%:Rc.
  by [].
apply: funext => h /=.
by rewrite -fmorphV [X in f X]addrC /realC /= scalerc scaleCr.
Qed.

Lemma Cdiff1 (f : C -> C) (c : C) :
  lim ((fun h : C => h^-1 * ((f (h + c) - f c))) @  0^')
  = 'D_1 (f : C^o -> C^o) c.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : C => h^-1 * ((f (h + c) - f c)))
                   @ 0^')). 
suff ->: (fun h : C => h^-1 * (f (h + c) - f c))  
  = (fun h : C => h^-1 *: (( (f : C^o -> C^o) \o shift c) (h *: 1 : C^o) - f c) : C^o).
  by [].
apply: funext => h /=.
by rewrite scalecE scaler1. 
Qed.


Lemma Rdiffi (f : C^o -> C^o) c:
  lim ((fun h : C => h^-1 * ((f (c + h * 'i) - f c))) @ (realC @ 0^'))
  = 'D_('i) (f%:Rfun) c%:Rc.
Proof.
rewrite /derive.
rewrite -[LHS]/(lim ((fun h : (R[i]) => h^-1 * (f (c + h * 'i) - f c))
                  \o realC @ 0^')).
suff -> : (fun h : (R[i]) => h^-1 * (f (c + h * 'i) - f c)) \o realC
  = fun h : R => h^-1 *: ((f \o shift c) (h *: ('i%:Rc)) - f c)%:Rc.
  by [].
apply: funext => h /=. 
by rewrite -fmorphV realCZ [X in f X]addrC scalerc.
Qed.





Definition CauchyRiemannEq (f : C -> C) c :=
  'i * 'D_1 f%:Rfun c%:Rc = 'D_('i) f%:Rfun c%:Rc.


Lemma is_derive_holo (f : C -> C) (c : C) :
    Rdifferentiable f c -> CauchyRiemannEq f c ->
    is_derive (c : C^o) 1 (f : C^o -> C^o) ('D_1 (f%:Rfun) c%:Rc). Proof.
move => fdiff CR.
suff lem: (h^-1 * (f (h + c) - f c) @[h --> 0^']) --> 'D_1 (f%:Rfun) (c%:Rc).
  split; last first. 
    by rewrite -Cdiff1; apply: cvg_lim lem; by [].
  apply/cvg_ex. eexists. rewrite /=. under eq_fun do rewrite scaler1/=. exact: lem.
move => /= A. 
  move => [/= _ /posnumP [r]] /=; rewrite /ball_ /= => H.
  near_simpl.
  near=> t.
  apply: H => /=.
  rewrite deriveE => //. 
  rewrite [f _](@diff_locallyx R Rc Rc) => //=.
  rewrite (ACl (1*4*2*3)) /= subrr add0r.  
  have -> : 'd (f%:Rfun) (c%:Rc) (t : Rc) = t * 'd (f%:Rfun) (c%:Rc) (1: Rc).
    rewrite (complexE t).
    rewrite !linearD. 
    have -> : (Re t)%:C = Re t *: 1 by rewrite scaleC1.
    have -> : 'i%C * (Im t)%:C = Im t *: 'i%C by rewrite scalecr mulrC.
    rewrite !linearZ -!deriveE // -CR -scalecE /= !scaleCr scalerA. 
    by rewrite -(scalerDl ('D_1 f%:Rfun c : C^o)) !scalecE mulr1.
  rewrite mulrDr mulKf //; last by near:t; exact: nbhs_dnbhs_neq.
  rewrite opprD addNKr normrN. 
  near: t.
  case: littleo.
  move => h /= H. 
  near=> t. 
  rewrite normrM normfV ltr_pdivrMl; last by rewrite normr_gt0; near: t; apply: nbhs_dnbhs_neq.   
  rewrite (@le_lt_trans _ _ ((r%:num/2  * `|t|)))  //.
    rewrite -!normRcomplex. 
    rewrite [r%:num/2]gt0_normc // -rmorphM /= lecR.
    near: t; apply: nbhs_dnbhs; near_simpl.
    by apply: H => //; rewrite -[Normc.normc _]/(`|_|) normr_gt0 //. 
  rewrite mulrC ltr_pM2l //. 
    by rewrite gtr_pMr // invf_lt1 // ?ltr1n //.
  rewrite normr_gt0; near: t;  apply: nbhs_dnbhs_neq. 
Unshelve. all: by end_near. 
Qed.

Lemma diff_CR_holo (f : C -> C) (c : C):
  Rdifferentiable f c -> CauchyRiemannEq f c -> holomorphic f c.
Proof. 
by move=> /is_derive_holo /[apply] ?; exact/holomorphicP.
Qed.


Lemma eqaddoPx {K : numDomainType} {T : Type} {V W : normedModType K}
  (F : filter_on T) (f g : T -> V) (e : T -> W) :
(forall x, f x = g x +o_(x \near F) e x)  <->
 forall eps :  K,  0 < eps -> \near F, `|(f - g) F| <= eps * `|e F|.
Proof.
rewrite -eqaddoP; split=> [fE|->]; last exact/eqaddoEx.
by apply/funext=> x; rewrite fctE.
Qed.

Lemma holo_differentiable (f : C -> C) (c v : C):
   holomorphic f c -> Rdifferentiable f c.
Proof.
move => /holomorphicP/derivable1_diffP fdiff.
rewrite /Rdifferentiable.
pose df (v : Rc) : Rc := 'd (f : C^o -> C^o) (c : C^o) v.
have lindf : linear df.
  by move=> /= k x y; rewrite !scaleCr /df /= linearP.
pose Df : {linear Rc -> Rc} := 
HB.pack df (@GRing.isLinear.Build _ _ _ _ df lindf).
apply: (exists_diff).  
exists Df; first exact: linear_findim_continuous. 
rewrite /Df /df /=.
apply/eqaddoPx.
move => r r0.
near=> w.
rewrite /Df /df /=.
have /diff_locallyxP [_ ] := fdiff.
move  => /(_ (w - c)). 
rewrite !fctE subrK => ->.
rewrite opprD.  
rewrite (AC (3*2) ((1*4)*(2*5)*3)) /=.
rewrite !subrr !add0r.
near: w.
case : littleo => /=.
move => h heps.
near=> w.
rewrite -lecR.
rewrite rmorphM /=.
rewrite !normRcomplex.
near: w.
suff: \forall x \near c, `|h (x - c)| <= r%:C * `|x - c|.
  exact.
apply/nbhs0P.
near do rewrite addrC addKr.
apply: heps.
by rewrite ltcR.
Unshelve. all: end_near. Qed.

Lemma is_derive_Rdiff  (f : C -> C) (c v : C):
    is_derive (c%:Rc) v (f%:Rfun) ('D_v (f : C^o -> C^o) c). 
Proof.
Admitted.
(*
move => fdiff.
suff lem: ((h^-1 : R) *: ((f%:Rfun) ( h *:v + (c%:Rc)) - (f%:Rfun) (c%:Rc)) @[h --> 0^']) --> 'D_v (f : C^o -> C^o) (c%:Rc).
  split; last first. 
    rewrite -Rdiffv. apply: cvg_lim. by [].  
    Search "cvg"  "comp". admit. 
  apply/cvg_ex. eexists. . under eq_fun do rewrite scaler1/=. exact: lem.
move => /= A. 
  move => [/= _ /posnumP [r]] /=; rewrite /ball_ /= => H.
  near_simpl.
  near=> t.
  apply: H => /=.
  rewrite deriveE => //. 
  rewrite [f _](@diff_locallyx R Rc Rc) => //=.
  rewrite (ACl (1*4*2*3)) /= subrr add0r.  
  have -> : 'd (f%:Rfun) (c%:Rc) (t : Rc) = t * 'd (f%:Rfun) (c%:Rc) (1: Rc).
    rewrite (complexE t).
    rewrite !linearD. 
    have -> : (Re t)%:C = Re t *: 1 by rewrite scaleC1.
    have -> : 'i%C * (Im t)%:C = Im t *: 'i%C by rewrite scalecr mulrC.
    rewrite !linearZ -!deriveE // -CR -scalecE /= !scaleCr scalerA. 
    by rewrite -(scalerDl ('D_1 f%:Rfun c : C^o)) !scalecE mulr1.
  rewrite mulrDr mulKf //; last by near:t; exact: nbhs_dnbhs_neq.
  rewrite opprD addNKr normrN. 
  near: t.
  case: littleo.
  move => h /= H. 
  near=> t. 
  rewrite normrM normfV ltr_pdivrMl; last by rewrite normr_gt0; near: t; apply: nbhs_dnbhs_neq.   
  rewrite (@le_lt_trans _ _ ((r%:num/2  * `|t|)))  //.
    rewrite -!normRcomplex. 
    rewrite [r%:num/2]gt0_normc // -rmorphM /= lecR.
    near: t; apply: nbhs_dnbhs; near_simpl.
    by apply: H => //; rewrite -[Normc.normc _]/(`|_|) normr_gt0 //. 
  rewrite mulrC ltr_pM2l //. 
    by rewrite gtr_pMr // invf_lt1 // ?ltr1n //.
  rewrite normr_gt0; near: t;  apply: nbhs_dnbhs_neq. 
Unshelve. all: by end_near. 
*)



(* exact: linear_findim_continuous. *)
(*Lemma thm_qui_manque (K : numFieldType) (V W : normedModType K) (f : V -> W) (c h v: V) (df : W): is_derive c v f df -> 
  forall h, f ( c + h *: v) = f c + df +o_(v \near c) (v - c).
Admitted.
*)



Lemma holo_CauchyRiemann (f : C -> C) c: holomorphic f c -> CauchyRiemannEq f c.
Proof.
move=> /cvg_ex; rewrite //= /CauchyRiemannEq. rewrite -Rdiff1 -Rdiffi.
set quotC : C -> C := fun h : R[i] => h^-1 * (f (c + h) - f c).
set quotR : C -> C:= fun h => h^-1 *: ((f (c + h * 'i) - f c) : C^o) .
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
  apply: within_continuous_withinNx; first by apply: mulrr_continuous.
  move=> x /eqP; rewrite mul0r mulIr_eq0; last by apply/rregP; apply: neq0Ci.
  exact: eqP.
have HRcomp: cvg (quotC \o *%R^~ 'i%R @ (realC @ ((0 : R)^'))).
  by apply/cvg_ex; simpl; exists l.
have ->: lim (quotR @ (realC @ ((0 : R)^')))
  = 'i * lim (quotC \o ( fun h => h *'i) @ (realC @ ((0 : R)^'))).
  have: (fun x => 'i) \* quotC \o ( fun h => h *'i) =1 quotR.
    move=> h /=; rewrite /quotC /quotR /=.
    rewrite invfM mulrA (mulrC _ ('i)^-1) mulrA divff ?complexiE ?neq0Ci //. 
    by rewrite mul1r scalecE. 
  move=> /funext <-. rewrite limM ?lim_cst.  by []. by []. exact: cvg_cst.  by []. by [].  
suff ->: lim (quotC @ (realC @ ((0 : R)^')))
      = lim (quotC \o  *%R^~ 'i%R @ (realC @ ((0 : R)^'))) by [].
suff ->: lim (quotC @ (realC @ ((0 : R)^'))) = l.
  by apply/eqP; rewrite eq_sym; apply/eqP; apply: (cvg_lim _ lem).
by apply: cvg_lim; last exact: HR0.
Qed.


Lemma holomorphic_Rdiff (f : C -> C) (c : C) :
  (Rdifferentiable f c) /\ (CauchyRiemannEq f c) <-> (holomorphic f c).
Proof.
split; first by move => [Rdiff CR]; exact: diff_CR_holo.
split; first by exact: holo_differentiable.
by exact: holo_CauchyRiemann.
Qed.

End Holomorphe_der.

Search "scale" "C".
Search "scale" "c".
Check scalerc.
