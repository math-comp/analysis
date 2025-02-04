(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import boolp reals ereal.
From HB Require Import structures.
From mathcomp Require Import classical_sets signed functions topology normedtype cardinality.
From mathcomp Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import exp hoelder.

(******************************************************************************)
(*                                                                            *)
(*         LfunType mu p == type of measurable functions f such that the      *)
(*                          integral of |f| ^ p is finite                     *)
(*            LType mu p == type of the elements of the Lp space              *)
(*          mu.-Lspace p == Lp space                                          *)
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
  ('N[ mu ]_p [ f ] < +oo)%E.

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : {mfun T >-> R}) := {
  lfuny : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) :=
  {f : {mfun T >-> R} & isLfun d T R mu p f}.

Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) =>
  solve [apply: lfuny] : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

HB.instance Definition _ := gen_eqMixin (LfunType mu p).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition Lequiv (f g : LfunType mu p) := `[< f = g %[ae mu] >].

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

Lemma LequivP (f g : LfunType mu p) :
  reflect (f = g %[ae mu]) (f == g %[mod LspaceType]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

Record LType := MemLType { Lfun_class : LspaceType }.
Coercion LfunType_of_LType (f : LType) : LfunType mu p :=
  repr (Lfun_class f).

End Lequiv.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p := [set: LType mu p].
Arguments Lspace : clear implicits.

Lemma LType1_integrable (f : LType mu 1) : mu.-integrable setT (EFin \o f).
Proof.
apply/integrableP; split; first exact/EFin_measurable_fun.
have := lfuny f.
rewrite /finite_norm unlock /Lnorm ifF ?oner_eq0// invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1//.
by under eq_integral => i _ do rewrite powRr1//.
Qed.

Lemma LType2_integrable_sqr (f : LType mu 2%:E) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
rewrite (@lty_poweRy _ _ (2^-1))//.
rewrite (le_lt_trans _ (lfuny f))//.
rewrite unlock /Lnorm ifF ?gt_eqF//.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= integral_ge0// leey.
- rewrite in_itv/= leey integral_ge0// => x _.
  by rewrite lee_fin powR_ge0.
rewrite ge0_le_integral//.
- apply: measurableT_comp => //.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
- by move=> x _; rewrite lee_fin powR_ge0.
- exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R)/measurableT_comp.
- by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.


Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Definition lfun : {pred (LType mu p)} := topred (mu.-Lspace p).
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
End lfun_pred.

Section Lspace_zmodule.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Hypothesis (p1 : (1 <= p)%E).

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof.
rewrite /finite_norm unlock /Lnorm.
case: p => //[r|].
- case: ifPn => r0.
    rewrite preimage_cst ifF ?measure0// in_setD in_setT/=.
    by apply /negP; rewrite in_setE/=.
  under eq_integral => x _ do rewrite /= normr0 powR0//.
  by rewrite integral0 poweR0r// invr_neq0.
case: ifPn => //mu0.
rewrite (_ : normr \o _ = cst 0); last by apply: funext => x/=; rewrite normr0.
rewrite /ess_sup.
under eq_set do rewrite preimage_cst/=.
rewrite ereal_inf_EFin ?ltry//.
rewrite /has_lbound/lbound.
- exists 0 => /= x.
  case: ifPn => [_|]; first by move: mu0 => /[swap] ->; rewrite ltNge lexx.
  by rewrite set_itvE notin_setE//= ltNge => /negP/negbNE.
by exists 0 => /=; rewrite ifF//; rewrite set_itvE;
  rewrite memNset //=; apply/negP; rewrite -real_leNgt.
Qed.

HB.instance Definition _ := @isLfun.Build d T R mu p (cst 0) lfuny0.

(* TODO: move to lebesgue_measure.v *)
Lemma measurable_funN_subproof (f : {mfun T >-> R}) :
  measurable_fun setT (\-f).
Proof. exact: measurableT_comp. Qed.

HB.instance Definition _ (f : {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (\-f) (measurable_funN_subproof _).

Lemma lfuny_opp f : finite_norm mu p f -> finite_norm mu p (\-f).
Proof. by rewrite /finite_norm oppr_Lnorm. Qed.

Lemma Lfun_opp_subproof (f : LfunType mu p) : finite_norm mu p (\-f).
Proof. exact: lfuny_opp. Qed.

HB.instance Definition _ (f : LfunType mu p) :=
  @isLfun.Build d T R mu p (\- f) (Lfun_opp_subproof _).

Lemma minkowskie :
forall [d : measure_display] [T : measurableType d] [R : realType] 
  (mu : measure T R) [f g : T -> R] [p : \bar R],
measurable_fun [set: T] f ->
measurable_fun [set: T] g ->
(1 <= p)%E -> ('N[mu]_p[(f \+ g)%R] <= 'N[mu]_p[f] + 'N[mu]_p[g])%E.
(* TODO: Jairo is working on this *)
Admitted.

Lemma lfunyD (f g : {mfun T >-> R}) :
  finite_norm mu p f -> finite_norm mu p g ->
    finite_norm mu p (f + g).
Proof.
rewrite /finite_norm => ff fg.
apply: le_lt_trans; first exact: minkowskie.
exact: lte_add_pinfty.
Qed.

Lemma LfunD_subproof (f g : LfunType mu p) : finite_norm mu p (f \+ g).
Proof. exact: lfunyD. Qed.

HB.instance Definition _ (f g : LfunType mu p) :=
  @isLfun.Build d T R mu p (f \+ g) (LfunD_subproof _ _).

HB.about GRing.isZmodule.Build.
(* Program Definition fct_zmodMixin := *)
(*   @GRing.isZmodule.Build (LfunType mu p) _ _ _ _ _ _ _. *)

Lemma powRMn (x : R) r n : 0 <= x -> ((x *+ n) `^ r) = ((x `^ r) * (n%:R `^ r)).
Proof. by move=> x0; rewrite -[in LHS]mulr_natr powRM. Qed.

Local Notation "f \*+ n" := (fun x => f x *+ n) (at level 10).

Lemma ess_sup0 : (ess_sup mu (cst 0)%R = 0)%E.
Admitted.

Lemma ess_supMn f n : (ess_sup mu (f \*+ n) = ess_sup mu f *+ n)%E.
Admitted.

Lemma mule0n n : (0 *+ n = 0 :> \bar R)%E.
Proof. by rewrite -mule_natl mule0. Qed.


Lemma LnormMn (f : LfunType mu p) n : ('N[mu]_p[f \*+ n] = 'N[mu]_p[f] *+ n)%E.
Proof.
rewrite unlock /Lnorm.
move: p1 f.
case: p => [r||].
- rewrite lee_fin => r1 f.
  have r0 : 0 < r by rewrite (lt_le_trans _ r1).
  under eq_integral => x _ do rewrite normrMn powRMn// EFinM.
  rewrite (gt_eqF r0) integralZr//; last first.
    apply/integrableP; split.
      apply: measurable_funT_comp => //.
      apply: (measurable_funT_comp (measurable_powR _)) => //.
      exact: measurable_funT_comp.
    under eq_integral => x _ do rewrite gee0_abs ?lee_fin ?powR_ge0//.
    apply: (@lty_poweRy _ _ (r^-1)); first by rewrite invr_neq0// gt_eqF.
    have := lfuny f.
    by rewrite /finite_norm unlock /Lnorm gt_eqF.
  rewrite poweRM; last 2 first.
  - by apply: integral_ge0 => x _; rewrite lee_fin powR_ge0.
  - by rewrite lee_fin powR_ge0.
  by rewrite poweR_EFin -powRrM divff// ?gt_eqF// powRr1// muleC mule_natl.
- move=> _ f; case: ifPn => mu0.
  rewrite (_ : normr \o f \*+ n = (normr \o f) \*+ n); last first.
    by apply: funext => x/=; rewrite normrMn.
  exact: ess_supMn.
- by rewrite mule0n.
by rewrite leeNy_eq => /eqP.
Qed.

Lemma lfunyMn (f : LfunType mu p) n :
  finite_norm mu p f -> finite_norm mu p (f \*+ n)%E.
Proof.
by rewrite/finite_norm LnormMn => ff; rewrite -mule_natl; exact: lte_mul_pinfty.
Qed.

Lemma LfunyMn_subproof (f : LfunType mu p) (n : nat) : finite_norm mu p (f \*+ n).
Proof. exact: lfunyMn. Qed.

(* HB.instance Definition _ (f : LfunType mu p) n := *)
(*   @isLfun.Build d T R mu p (f \*+ n) (LfunyMn_subproof _ _). *)

End Lspace_zmodule.
Notation "f \*+ n" := (fun x => f x *+ n) (at level 10).

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable (p : R) (p1 : 1 <= p).

(* 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LType mu (p%:E)).
Definition nm f := fine ('N[mu]_p%:E[f]).


(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

(* measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R *)

(* Notation ty := (LfunType mu p%:E). *)
(* Definition nm (f : ty) := fine ('N[mu]_p%:E[f]). *)

(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

Lemma ler_Lnorm_add (f g : ty) :
  nm (f \+ g) <= nm f + nm g.
Proof.
rewrite /nm -fineD ?fine_le ?minkowski// fin_numElt (lt_le_trans ltNy0) ?Lnorm_ge0//=.
- rewrite (le_lt_trans (minkowski _ _ _ _))//.
  by rewrite lte_add_pinfty//; exact: lfuny.
- by rewrite lte_add_pinfty//; exact: lfuny.
- by rewrite adde_ge0 ?Lnorm_ge0.
all: exact: lfuny.
Qed.

Lemma natmulfctE (U : pointedType) (K : ringType) (f : U -> K) n :
  f *+ n = (fun x => f x *+ n).
Proof. by elim: n => [//|n h]; rewrite funeqE=> ?; rewrite !mulrSr h. Qed.

Lemma LnormN (f : ty) : nm (\-f) = nm f.
Proof. by rewrite /nm oppr_Lnorm. Qed.

Lemma enatmul_ninfty (n : nat) : (-oo *+ n.+1 = -oo :> \bar R)%E \/ (-oo *+ n.+1 = +oo :> \bar R)%E.
Proof. by elim: n => //=[|n []->]; rewrite ?addNye; left. Qed.

Lemma Lnorm0 : ('N[mu]_p%:E[0%R] = 0)%E.
Proof.
rewrite unlock /Lnorm.
case: ifPn => _.
  by rewrite preimage_cst ifF//=; apply/negP; rewrite in_setE/=; case.
under eq_integral => x _ do rewrite normr0 powR0 ?gt_eqF// ?(lt_le_trans _ p1)//.
by rewrite integral0 poweR0r// gt_eqF// invr_gt0 (lt_le_trans _ p1).
Qed.

Lemma Lnorm_natmul (f : ty) k : nm (f \*+ k) = nm f *+ k.
Proof.
rewrite /nm LnormMn// -mule_natl -[RHS]mulr_natl fineM// fin_numElt.
have := lfuny f.
by rewrite /finite_norm (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _)) => ->.
Qed.

Lemma Lnorm_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
rewrite /nm => /eqP.
rewrite fine_eq0; last by
  rewrite fin_numElt (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _))//=; exact: lfuny.
have p0 : 0 < p by exact: lt_le_trans.
move/eqP/Lnorm_eq0_eq0 => /(_ p0 (measurable_funP _)) eqnorm.
near=> x => Dx.
suffices: ((`|f x| `^ p)%:E = cst 0 x)%E.
  by rewrite (_ : 0 x = 0)//=; case; move/powR_eq0_eq0/normr0_eq0.
apply: (near eqnorm x) => //.
Unshelve. all: by end_near.
Qed.

HB.about Num.Zmodule_isSemiNormed.Build.

(* TODO : fix the definition *)
(* HB.instance Definition _ := *)
(*   @Num.Zmodule_isSemiNormed.Build R (LfunType mu p%:E) ty *)
(*     nm ler_Lnorm_add Lnorm_natmul LnormN. *)

(* todo: add equivalent of mx_normZ and HB instance *)

End Lspace_norm.

(*
Section Lspace_inclusion.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma Lspace_inclusion p q : (p <= q)%E ->
  forall (f : LfunType mu q), ('N[ mu ]_p [ f ] < +oo)%E.
Proof.
move=> pleq f.

isLfun d T R mu p f.

End Lspace_inclusion.
*)
