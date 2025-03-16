(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import boolp classical_sets interval_inference reals.
From mathcomp Require Import functions cardinality topology normedtype ereal.
From mathcomp Require Import sequences esum exp measure numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral hoelder ess_sup_inf.

(**md**************************************************************************)
(* # Lp-spaces                                                                *)
(*                                                                            *)
(* Definition of L-spaces and properties of the L-norm.                       *)
(*                                                                            *)
(* ```                                                                        *)
(*    finite_norm mu p f := the L-norm of real-valued function f is finite    *)
(*                          The parameter p is an extended real.              *)
(*        LfunType mu p1 == type of measurable functions f with a finite      *)
(*                          L-norm                                            *)
(*                          p1 is a proof that the extended real number p is  *)
(*                          greater or equal to 1.                            *)
(*                          The HB class is Lfun.                             *)
(*            f \in lfun == holds for f : LfunType mu p1                      *)
(*            Lequiv f g == f is equal to g almost everywhere                 *)
(*                          The functions f and g have type LfunType mu p1.   *)
(*                          Lequiv is made a canonical equivalence relation.  *)
(*      LspaceType mu p1 == type of the elements of the Lp space for the      *)
(*                          measure mu                                        *)
(*          mu.-Lspace p == Lp space as a set                                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition finite_norm d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) :=
  ('N[ mu ]_p [ EFin \o f ] < +oo)%E.

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) (f : T -> R)
  of @MeasurableFun d _ T R f := {
  lfuny : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of @MeasurableFun d _ T R f & isLfun d T R mu p p1 f}.

Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) => solve [apply: lfuny] : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

HB.instance Definition _ := gen_eqMixin (LfunType mu p1).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p1).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Definition Lequiv (f g : LfunType mu p1) := `[< f = g %[ae mu] >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP/ae_eq_sym.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_eq_trans gf fh).
Qed.

Canonical Lequiv_canonical :=
  EquivRel Lequiv Lequiv_refl Lequiv_sym Lequiv_trans.

Local Open Scope quotient_scope.

Definition LspaceType := {eq_quot Lequiv}.
Canonical LspaceType_quotType := [the quotType _ of LspaceType].
Canonical LspaceType_eqType := [the eqType of LspaceType].
Canonical LspaceType_choiceType := [the choiceType of LspaceType].
Canonical LspaceType_eqQuotType := [the eqQuotType Lequiv of LspaceType].

Lemma LequivP (f g : LfunType mu p1) :
  reflect (f = g %[ae mu]) (f == g %[mod LspaceType]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

Record LType := MemLType { Lfun_class : LspaceType }.
Coercion LfunType_of_LType (f : LType) : LfunType mu p1 :=
  repr (Lfun_class f).

End Lequiv.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p (p1 : (1 <= p)%E) := [set: LType mu p1].
Arguments Lspace : clear implicits.

Lemma LType1_integrable (f : LType mu (@lexx _ _ 1%E)) :
  mu.-integrable setT (EFin \o f).
Proof.
apply/integrableP; split; first exact/measurable_EFinP.
have := lfuny _ f.
rewrite /finite_norm unlock /Lnorm invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1.
by under eq_integral => i _ do rewrite poweRe1//.
Qed.

Let le12 : (1 <= 2%:E :> \bar R)%E.
Proof.
rewrite lee_fin.
rewrite (ler_nat _ 1 2).
by [].
Qed.

Lemma LType2_integrable_sqr (f : LType mu le12) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  apply/measurable_EFinP.
  exact/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
rewrite (@lty_poweRy _ _ 2^-1)//.
rewrite (le_lt_trans _ (lfuny _ f))//.
rewrite unlock.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= leey integral_ge0// => x _.
- rewrite in_itv/= leey integral_ge0// => x _.
  by rewrite lee_fin powR_ge0.
- rewrite ge0_le_integral//.
  + apply: measurableT_comp => //; apply/measurable_EFinP.
    exact/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
  + by move=> x _; rewrite lee_fin powR_ge0.
  + apply/measurable_EFinP.
    apply/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R) => //.
    exact/measurableT_comp.
  + by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finlfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition lfun : {pred _ -> _} := [predI @mfun _ _ T R & finlfun].
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
Lemma sub_lfun_mfun : {subset lfun <= mfun}.
Proof. by move=> x /andP[]. Qed.
Lemma sub_lfun_finlfun : {subset lfun <= finlfun}.
Proof. by move=> x /andP[]. Qed.

End lfun_pred.

Section lfun.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Notation lfun := (@lfun _ T R mu p).
Section Sub.
Context (f : T -> R) (fP : f \in lfun).
Definition lfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ T R f (set_mem (sub_lfun_mfun fP)).
#[local] HB.instance Definition _ := lfun_Sub1_subproof.
Definition lfun_Sub2_subproof :=
  @isLfun.Build d T R mu p p1 f (set_mem (sub_lfun_finlfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := lfun_Sub2_subproof.
Definition lfun_Sub : LfunType mu p1 := f.
End Sub.

Lemma lfun_rect (K : LfunType mu p1 -> Type) :
  (forall f (Pf : f \in lfun), K (lfun_Sub Pf)) -> forall u, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]].
have Pf : f \in lfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_lfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_lfun_finlfun Pf) by [].
exact: Ksub.
Qed.

Lemma lfun_valP f (Pf : f \in lfun) : lfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ :=
  isSub.Build _ _ (LfunType mu p1) lfun_rect lfun_valP.

Lemma lfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Import numFieldNormedType.Exports.

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0// ltry. Qed.

HB.instance Definition _ := @isLfun.Build d T R mu p p1 (cst 0) lfuny0.

Lemma mfunP (f : {mfun T >-> R}) : (f : T -> R) \in mfun.
Proof. exact: valP. Qed.

Lemma lfunP (f : LfunType mu p1) : (f : T -> R) \in lfun.
Proof. exact: valP. Qed.

Lemma mfun_scaler_closed : scaler_closed (@mfun _ _ T R).
Proof. move=> a/= f; rewrite !inE; exact: measurable_funM. Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ (@mfun _ _ T R)
  mfun_scaler_closed.
HB.instance Definition _ := [SubZmodule_isSubLmodule of {mfun T >-> R} by <:].

Lemma LnormZ (f : LfunType mu p1) a :
  ('N[mu]_p[EFin \o (a \*: f)] = `|a|%:E * 'N[mu]_p[EFin \o f])%E.
Proof.
rewrite unlock /Lnorm.
case: p p1 f => //[r r1 f|? f].
- under eq_integral do rewrite /= -mulr_algl scaler1 normrM powRM ?EFinM//.
  rewrite integralZl//; last first.
    apply/integrableP; split.
      apply: measurableT_comp => //.
      apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
      exact: measurableT_comp.
    apply: (@lty_poweRy _ _ r^-1).
      by rewrite gt_eqF// invr_gt0 ?(lt_le_trans ltr01).
    rewrite [ltLHS](_ : _ = 'N[mu]_r%:E[EFin \o f]); first exact: (lfuny r1 f).
    rewrite unlock /Lnorm.
    by under eq_integral do rewrite gee0_abs ?lee_fin ?powR_ge0//.
  rewrite poweRM ?integral_ge0=> //[||x _]; rewrite ?lee_fin ?powR_ge0//.
  by rewrite poweR_EFin -powRrM mulfV ?gt_eqF ?(lt_le_trans ltr01)// powRr1.
- case: ifPn => mu0; last by rewrite mule0.
  rewrite -ess_supZl//; apply/eq_ess_sup/nearW => t /=.
  by rewrite normrZ EFinM.
Qed.

Lemma lfun_submod_closed : submod_closed lfun.
Proof.
split.
  by rewrite -[0]/(cst 0); exact: lfunP.
move=> a/= f g fP gP.
rewrite -[f]lfun_valP -[g]lfun_valP.
move: (lfun_Sub _) (lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=; apply: (le_lt_trans (eminkowski _ _ _ _)) => //.
- suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
- rewrite lte_add_pinfty//; last exact: lfuny.
  by rewrite LnormZ lte_mul_pinfty// ?lee_fin//; exact: lfuny.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ lfun
  lfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End lfun.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (p : \bar R) (p1 : (1 <= p)%E).

(* TODO: 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Let nm f := fine ('N[mu]_p[EFin \o f]).

Lemma finite_norm_fine (f : ty) : (nm f)%:E = 'N[mu]_p[EFin \o f].
Proof.
rewrite /nm fineK// fin_numElt (lt_le_trans ltNy0) ?Lnorm_ge0//=.
exact: lfuny.
Qed.

Lemma ler_LnormD (f g : ty) : nm (f + g) <= nm f + nm g.
Proof. by rewrite -lee_fin EFinD !finite_norm_fine eminkowski. Qed.

Lemma LnormN (f : ty) : nm (\-f) = nm f.
Proof. by rewrite /nm oppr_Lnorm. Qed.

Lemma Lnorm_natmul (f : ty) k : nm (f *+ k) = nm f *+ k.
Proof.
apply/EFin_inj; rewrite finite_norm_fine -scaler_nat LnormZ normr_nat.
by rewrite -[in RHS]mulr_natl EFinM finite_norm_fine.
Qed.

(* TODO : fix the definition *)
(* waiting for MathComp 2.4.0
HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (LfunType mu p1)
     nm ler_Lnorm_add Lnorm_natmul LnormN.
*)

(* TODO: add equivalent of mx_normZ and HB instance *)

Lemma fine_Lnorm_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
move=> /eqP; rewrite -eqe => /eqP.
rewrite finite_norm_fine => /Lnorm_eq0_eq0.
by apply; rewrite ?(lt_le_trans _ p1).
Qed.

End Lspace_norm.

Section Lspace_inclusion.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma Lspace_inclusion (p q : \bar R) :
  forall (p1 : 1 <= p) (q1 : 1 <= q),
    mu [set: T] < +oo -> p < q ->
    forall f : {mfun T >-> R}, finite_norm mu q f -> finite_norm mu p f.
Proof.
have := measure_ge0 mu [set: T].
rewrite le_eqVlt => /predU1P[mu0 p1 q1 _ _ f _|mu_pos].
  rewrite /finite_norm unlock /Lnorm.
  move: p p1; case=> //; last by rewrite -mu0 ltxx ltry.
  move=> r r1.
  under eq_integral do rewrite /= -[(_ `^ _)%R]ger0_norm ?powR_ge0//=.
  rewrite (@integral_abs_eq0 _ _ _ _ setT setT (fun x => (`|f x| `^ r)%:E))//.
    by rewrite poweR0r// invr_neq0// gt_eqF// -lte_fin (lt_le_trans _ r1).
  apply/measurable_EFinP.
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)) => //.
  exact: measurableT_comp.
move: p q.
case=> //[p|]; case=> //[q|] p1 q1; last first.
  have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
  move=> muoo _ f.
  rewrite /finite_norm unlock /Lnorm mu_pos => supf_lty.
  rewrite poweR_lty//; move: supf_lty => /ess_supr_bounded[M fM].
  rewrite (@le_lt_trans _ _ (\int[mu]_x (M `^ p)%:E)); [by []| |]; last first.
    by rewrite integral_cst// lte_mul_pinfty// lee_fin powR_ge0.
  apply: ae_ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin powR_ge0.
    apply/measurable_EFinP.
    apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
    exact: measurableT_comp.
  - by move=> x _; rewrite lee_fin powR_ge0.
    apply: filterS fM => t/= ftM _.
    rewrite lee_fin ge0_ler_powR//; first exact: ltW.
    by rewrite nnegrE (le_trans _ ftM).
move=> mu_fin pleq f ffin.
have:= ffin; rewrite /finite_norm.
have p0 : (0 < p)%R by rewrite ?(lt_le_trans ltr01).
have pN0 : p != 0%R by rewrite gt_eqF.
have q0 : (0 < q)%R by rewrite ?(lt_le_trans ltr01).
have qinv0 : q^-1 != 0%R by rewrite invr_neq0// gt_eqF.
pose r := q/p.
pose r' := (1 - r^-1)^-1.
have := (@hoelder _ _ _ mu (fun x => `|f x| `^ p) (cst 1)%R r r')%R.
rewrite (_ : (_ \* cst 1)%R = (fun x : T => `|f x| `^ p))%R -?fctM ?mulr1//.
rewrite Lnorm_cst1 unlock /Lnorm invr1.
have mfp : measurable_fun [set: T] (fun x : T => (`|f x| `^ p)%R).
  apply: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ p)) => //.
  exact: measurableT_comp.
have m1 : measurable_fun [set: T] (@cst _ R 1%R).
  exact: measurable_cst.
have r0 : (0 < r)%R by rewrite/r divr_gt0.
have r'0 : (0 < r')%R.
  by rewrite /r' invr_gt0 subr_gt0 invf_lt1 ?(lt_trans ltr01)//;
    rewrite /r ltr_pdivlMr// mul1r.
have rr'1 : r^-1 + r'^-1 = 1%R.
  by rewrite /r' /r invf_div invrK addrCA subrr addr0.
move=> /(_ mfp m1 r0 r'0 rr'1).
under [in leLHS] eq_integral do rewrite /= powRr1// norm_powR// normrE.
under [in leRHS] eq_integral do
  rewrite /= norm_powR// normr_id -powRrM mulrCA divff// mulr1.
rewrite [X in X <= _]poweRe1; last
  by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
move=> h1 /lty_poweRy h2.
apply: poweR_lty.
apply: (le_lt_trans h1).
rewrite muleC lte_mul_pinfty ?fin_numElt?poweR_ge0//.
  by rewrite (lt_le_trans _ (poweR_ge0 _ _)) ?ltNyr// ?poweR_lty.
rewrite poweR_lty// (lty_poweRy qinv0)//.
by have:= ffin; rewrite /finite_norm unlock /Lnorm.
Qed.

End Lspace_inclusion.
