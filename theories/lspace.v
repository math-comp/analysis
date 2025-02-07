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
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) =>
  solve [apply: lfuny] : core.

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

Lemma LType1_integrable (f : LType mu (@lexx _ _ 1%E)) : mu.-integrable setT (EFin \o f).
Proof.
apply/integrableP; split; first exact/EFin_measurable_fun.
have := lfuny _ f.
rewrite /finite_norm unlock /Lnorm ifF ?oner_eq0// invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1//.
by under eq_integral => i _ do rewrite powRr1//.
Qed.

Let le12 : (1 <= 2%:E :> \bar R)%E.
rewrite lee_fin.
rewrite (ler_nat _ 1 2).
by [].
Qed.

Lemma LType2_integrable_sqr (f : LType mu le12) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
rewrite (@lty_poweRy _ _ (2^-1))//.
rewrite (le_lt_trans _ (lfuny _ f))//.
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

(* move to hoelder.v *)
Section conjugate.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Hypothesis (p1 : (1 <= p)%E).

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition conjugate :=
  match p with
  | r%:E => [get q : R | r^-1 + q^-1 = 1]%:E
  | +oo  => 1
  | -oo  => 0
  end.

Lemma conjugateE :
  conjugate = if p is r%:E then (r * (r-1)^-1)%:E
              else if p == +oo then 1 else 0.
Proof.
rewrite /conjugate.
move: p1.
case: p => [r|//=|//].
rewrite lee_fin => r1.
have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
congr (_%:E).
apply: get_unique.
  by rewrite invf_div mulrBl divff// mul1r addrCA subrr addr0.
move=> /= y h0.
suffices -> : y = (1 - r^-1)^-1.
  by rewrite -(mul1r r^-1) -{1}(divff r0) -mulrBl invf_div.
by rewrite -h0 -addrAC subrr add0r invrK.
Qed.

End conjugate.


Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finlfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition lfun : {pred _ -> _} := [predI @mfun _ _ T R & finlfun].
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
Lemma sub_lfun_mfun : {subset lfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_lfun_finlfun : {subset lfun <= finlfun}. Proof. by move=> x /andP[]. Qed.
End lfun_pred.


Lemma minkowskie :
forall [d : measure_display] [T : measurableType d] [R : realType] 
  (mu : measure T R) [f g : T -> R] [p : \bar R],
measurable_fun [set: T] f ->
measurable_fun [set: T] g ->
(1 <= p)%E -> ('N[mu]_p[(f \+ g)%R] <= 'N[mu]_p[f] + 'N[mu]_p[g])%E.
(* TODO: Jairo is working on this *)
Admitted.


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

HB.instance Definition _ := isSub.Build _ _ (LfunType mu p1) lfun_rect lfun_valP.

Lemma lfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Import numFieldNormedType.Exports.

Lemma ess_sup_cst_lty r : (0 < mu setT)%E -> (ess_sup mu (cst r) < +oo)%E.
Proof.
rewrite /ess_sup => mu0.
under eq_set do rewrite preimage_cst/=.
rewrite ereal_inf_EFin ?ltry//.
- exists r => x/=; case: ifPn => [_|].
    by move: mu0 => /[swap] ->; rewrite ltNge lexx.
  by rewrite set_itvE notin_setE//= ltNge => /negP/negbNE.
by exists r => /=; rewrite ifF//; rewrite set_itvE;
  rewrite memNset //=; apply/negP; rewrite -real_leNgt ?num_real.
Qed.

Lemma ess_sup_cst r : (0 < mu setT)%E -> (ess_sup mu (cst r) = r%:E)%E.
Proof.
rewrite /ess_sup => mu0.
under eq_set do rewrite preimage_cst/=.
rewrite ereal_inf_EFin.
- congr (_%:E).
  rewrite [X in inf X](_ : _ = `[r, +oo[%classic); last first.
    apply/seteqP; split => /=x/=.
      case: ifPn => [_|]; first by move: mu0=> /[swap] ->; rewrite ltNge lexx.
      by rewrite set_itvE notin_setE/= ltNge in_itv andbT/= => /negP /negPn.
    rewrite in_itv/= => /andP[x0 _].
    by rewrite ifF// set_itvE; apply/negP; rewrite in_setE/= ltNge => /negP.
  by rewrite inf_itv.
- exists r => x/=; case: ifPn => [_|].
    by move: mu0 => /[swap] ->; rewrite ltNge lexx.
  by rewrite set_itvE notin_setE//= ltNge => /negP/negbNE.
by exists r => /=; rewrite ifF//; rewrite set_itvE;
  rewrite memNset //=; apply/negP; rewrite -real_leNgt ?num_real.
Qed.

Lemma Lnorm0 : 'N[mu]_p[cst 0] = 0.
Proof.
rewrite unlock /Lnorm.
move: p1.
case: p => [r||//].
- rewrite lee_fin => r1.
  have r0: r != 0 by rewrite gt_eqF// (lt_le_trans _ r1).
  rewrite gt_eqF ?(lt_le_trans _ r1)//.
  under eq_integral => x _ do rewrite /= normr0 powR0//.
  by rewrite integral0 poweR0r// invr_neq0.
case: ifPn => //mu0 _.
rewrite (_ : normr \o _ = 0); last by apply: funext => x/=; rewrite normr0.
exact: ess_sup_cst.
Qed.

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0. Qed.

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

Lemma LnormZ (f : LfunType mu p1) a : ('N[mu]_p[a \*: f] = `|a|%:E * 'N[mu]_p[f])%E.
Admitted.

Lemma lfun_submod_closed : submod_closed (lfun).
Proof.
split.
  rewrite -[0]/(cst 0). exact: lfunP.
move=> a/= f g fP gP.
rewrite -[f]lfun_valP -[g]lfun_valP.
move: (lfun_Sub _) (lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=.
rewrite /finite_norm.
apply: (le_lt_trans (minkowskie _ _ _ _)) => //=.
  suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
rewrite lte_add_pinfty//; last exact: lfuny.
by rewrite LnormZ lte_mul_pinfty//; exact: lfuny.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ lfun
  lfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End lfun.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable (p : \bar R) (p1 : (1 <= p)%E).

(* 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Definition nm f := fine ('N[mu]_p[f]).


(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

(* measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R *)

(* Notation ty := (LfunType mu p%:E). *)
(* Definition nm (f : ty) := fine ('N[mu]_p%:E[f]). *)

(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

Lemma ler_Lnorm_add (f g : ty) :
  nm (f + g) <= nm f + nm g.
Proof.
rewrite /nm -fineD ?fine_le ?minkowskie// fin_numElt (lt_le_trans ltNy0) ?Lnorm_ge0//=.
- rewrite (le_lt_trans (minkowskie _ _ _ _))//.
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

Lemma Lnorm_natmul (f : ty) k : nm (f *+ k) = nm f *+ k.
Proof.
rewrite /nm -scaler_nat LnormZ fineM//= ?normr_nat ?mulr_natl// fin_numElt.
have := lfuny p1 f.
by rewrite /finite_norm (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _)) => ->.
Qed.


HB.about Num.Zmodule_isSemiNormed.Build.

(* TODO : fix the definition *)
HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (LfunType mu p1)
     nm ler_Lnorm_add Lnorm_natmul LnormN.

(* todo: add equivalent of mx_normZ and HB instance *)

Lemma ess_sup_ger f (r : R) : (forall x, f x <= r) -> (ess_sup mu f <= r%:E)%E.
Proof.
move=> fr.
rewrite /ess_sup.
apply: ereal_inf_le.
apply/exists2P.
exists r%:E => /=; split => //.
apply/exists2P.
exists r; split => //.
rewrite preimage_itvoy.
suffices -> : [set x | r < f x] = set0 by [].
apply/seteqP; split => x //=.
rewrite lt_neqAle => /andP[rneqfx rlefx].
move: (fr x) => fxler.
have: (f x <= r <= f x) by rewrite rlefx fxler.
by move/le_anti; move: rneqfx => /[swap] -> /eqP.
Qed.

Lemma ess_sup_eq0 (f : {mfun T >-> R}) : ess_sup mu (normr \o f) = 0 -> f = 0 %[ae mu].
Admitted.


(* TODO: move to hoelder *)
Lemma Lnorm_eq0_eq0 (f : {mfun T >-> R}) : (0 < p)%E ->
  'N[mu]_p[f] = 0 -> f = 0 %[ae mu].
Proof.
rewrite unlock /Lnorm => p0.
move: p0.
case: p => [r r0||].
- case: ifPn => _.
    rewrite preimage_setI preimage_setT setTI -preimage_setC => /negligibleP.
    move/(_ (measurableC _)); rewrite -[X in d.-measurable X]setTI.
    move/(_ (measurable_funP _ measurableT _ (measurable_set1 _))) => /=.
    by case => A [mA muA0 fA]; exists A; split => // x/= ?; exact: fA.
  move=> /poweR_eq0_eq0.
  move=> /(_ (integral_ge0 _ _)) h.
  have: (\int[mu]_x (`|f x| `^ r)%:E)%E = 0 by apply: h => x _; rewrite lee_fin powR_ge0.
  under eq_integral => x _ do rewrite -[_%:E]gee0_abs ?lee_fin ?powR_ge0//.
  have mp: measurable_fun [set: T] (fun x : T => (`|f x| `^ r)%:E).
    apply: measurableT_comp => //.
    apply (measurableT_comp (measurable_powR _)) => //.
    apply: measurableT_comp => //.
  move/(ae_eq_integral_abs _ measurableT mp).
  apply: filterS => x/= /[apply].
  by case=> /powR_eq0_eq0 /eqP; rewrite normr_eq0 => /eqP.
- case: ifPn => [mu0 _|].
    exact: ess_sup_eq0.
  rewrite ltNge => /negbNE mu0 _ _.
  suffices mueq0: mu setT = 0 by exact: ae_eq0.
  move: mu0 (measure_ge0 mu setT) => mu0 mu1.
  suffices: (mu setT <= 0 <= mu setT)%E by move/le_anti.
  by rewrite mu0 mu1.
by [].
Qed.


Lemma Lnorm_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
have: 'N[mu]_p[f] \is a fin_num by
  rewrite fin_numElt (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _))//=; exact: lfuny.
have p0 : (0 < p)%E by exact: lt_le_trans.
rewrite /nm => h /eqP.
rewrite fine_eq0//.
move/eqP.
exact: Lnorm_eq0_eq0.
Qed.


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
