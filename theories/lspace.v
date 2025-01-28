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

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) := {
  measurable_lfun : measurable_fun [set: T] f ;
  lfuny : ('N[ mu ]_p [ f ] < +oo)%E
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) :=
  {f : T -> R & isLfun d T R mu p f}.

#[global] Hint Resolve measurable_lfun : core.
Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

HB.instance Definition _ := gen_eqMixin (LfunType mu p).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition Lequiv (f g : LfunType mu p) := `[< {ae mu, forall x, f x = g x} >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP; exact: filterS h.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(filterS2 _ _ gf fh) => x ->.
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
  reflect {ae mu, forall x, f x = g x} (f == g %[mod LspaceType]).
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
rewrite unlock /Lnorm ifF ?oner_eq0// invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1//.
by under eq_integral => i _ do rewrite powRr1//.
Qed.

Lemma LType2_integrable_sqr (f : LType mu 2%:E) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f)/measurable_lfun.
rewrite (@lty_poweRy _ _ (2^-1))//.
rewrite (le_lt_trans _ (lfuny f))//.
rewrite unlock /Lnorm ifF ?gt_eqF//.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= integral_ge0// leey.
- rewrite in_itv/= leey integral_ge0// => x _.
  by rewrite lee_fin powR_ge0.
rewrite ge0_le_integral//.
- apply: measurableT_comp => //.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f)/measurable_lfun.
- by move=> x _; rewrite lee_fin powR_ge0.
- exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R)/measurableT_comp/measurable_lfun.
- by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable (p : R). (* add hypothesis p > 1 *)

(* 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (T -> R).
Definition nm f := fine ('N[mu]_p%:E[f]).

(* Program Definition fct_zmodMixin := *)
(*   @GRing.isZmodule.Build (LfunType mu p%:E) 0 (fun f x => - f x) (fun f g => f \+ g). *)

(* measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R *)

(* Notation ty := (LfunType mu p%:E). *)
(* Definition nm (f : ty) := fine ('N[mu]_p%:E[f]). *)

(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

Lemma ler_Lnorm_add (f g : ty) :
  nm (f \+ g) <= nm f + nm g.
Proof.
rewrite /nm.
have : (-oo < 'N[mu]_p%:E[f])%E by exact: (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _)). 
have : (-oo < 'N[mu]_p%:E[g])%E by exact: (lt_le_trans ltNy0 (Lnorm_ge0 _ _ _)). 
rewrite !ltNye_eq => /orP[f_fin /orP[g_fin|/eqP foo]|/eqP goo].
- rewrite -fineD ?fine_le//.
  - admit.
  - by rewrite fin_numD f_fin g_fin//.
  rewrite minkowski//. admit. admit. admit.
- rewrite foo/= add0r.
  have : ('N[mu]_p%:E[f] <= 'N[mu]_p%:E[(f \+ g)])%E.
  rewrite unlock /Lnorm.
  rewrite {1}(@ifF _ (p == 0)).
  rewrite {1}(@ifF _ (p == 0)).
  rewrite gt0_ler_poweR.
  - by [].
  - admit.
  - admit.
  - admit.
  rewrite ge0_le_integral//.
  - move => x _. rewrite lee_fin powR_ge0//.
  - admit.
  - move => x _. rewrite lee_fin powR_ge0//.
  - admit.
  - move => x _. rewrite lee_fin gt0_ler_powR//. admit. (* rewrite normr_le. *)

Admitted.

Lemma natmulfctE (U : pointedType) (K : ringType) (f : U -> K) n :
  f *+ n = (fun x => f x *+ n).
Proof. by elim: n => [//|n h]; rewrite funeqE=> ?; rewrite !mulrSr h. Qed.


Lemma Lnorm_eq0 f : nm f = 0 -> {ae mu, f =1 0}.
rewrite /nm => /eqP.
rewrite fine_eq0; last first. admit.
move/eqP/Lnorm_eq0_eq0.
(* ale: I don't think it holds almost everywhere equal does not mean equal *
rewrite unlock /Lnorm ifF.
rewrite poweR_eq0.
rewrite integral_abs_eq0. *)
Admitted.

Lemma Lnorm_natmul f k : nm (f *+ k) = nm f *+ k.
rewrite /nm unlock /Lnorm.
case: (ifP (p == 0)).
  admit.

move => p0.
under eq_integral => x _.
  rewrite -mulr_natr/=.
  rewrite fctE (_ : k%:R _ = k%:R); last by rewrite natmulfctE.
  rewrite normrM powRM//=.
  rewrite mulrC EFinM.
  over.
rewrite /=.
rewrite integralZl//; last first. admit.
rewrite poweRM; last 2 first.
- by rewrite lee_fin powR_ge0.
- by rewrite integral_ge0// => x _; rewrite lee_fin powR_ge0.

rewrite poweR_EFin -powRrM mulfV; last admit.
rewrite powRr1//.
rewrite fineM//; last admit.
rewrite mulrC.

Admitted.

Lemma LnormN f : nm (-f) = nm f.
rewrite /nm.
congr (fine _).
rewrite unlock /Lnorm.
case: ifP.
move=> p0.
 admit.

move=> p0.
congr (_ `^ _)%E.
apply eq_integral => x _.
congr ((_ `^ _)%:E).
by rewrite normrN.
Admitted.

(*
Lemma ler_Lnorm_add f g :
  'N[mu]_p%:E[(f \+ g)%R] <= 'N[mu]_p%:E[f] + 'N[mu]_p%:E[g].
Admitted.

Lemma Lnorm_eq0 f : 'N[mu]_p%:E[f] = 0 -> f = 0%R.
Admitted.

Lemma Lnorm_natmul f k : 'N[mu]_p%:E [f *+ k]%R = 'N[mu]_p%:E [f] *+ k.
Admitted.

Lemma LnormN f : 'N[mu]_p%:E [- f]%R = 'N[mu]_p%:E [f].
Admitted.
*)

HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (*LType mu p%:E*) ty
    nm ler_Lnorm_add Lnorm_natmul LnormN.

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
