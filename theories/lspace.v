(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets signed functions topology normedtype cardinality.
Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.
Require Import exp.

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
    (mu : {measure set T -> \bar R}) (p : R) (f : T -> R) := {
  measurable_lfun : measurable_fun [set: T] f ;
  lfuny : (\int[mu]_x (`|f x| `^ p)%:E < +oo)%E
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : R) :=
  {f : T -> R & isLfun d T R mu p f}.

#[global] Hint Resolve measurable_lfun : core.
Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : R).

Canonical Lfun_eqType := EqType (LfunType mu p) gen_eqMixin.
Canonical Lfun_choiceType := ChoiceType (LfunType mu p) gen_choiceMixin.
End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : R).

Definition Lequiv (f g : LfunType mu p) := `[< {ae mu, forall x, f x = g x} >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(ae_imply _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP; exact: ae_imply h.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_imply2 _ gf fh).
by move=> x ->.
Qed.

Canonical Lequiv_canonical :=
  EquivRel Lequiv Lequiv_refl Lequiv_sym Lequiv_trans.

Local Open Scope quotient_scope.

Definition LspaceType := {eq_quot Lequiv}.
Canonical LspaceType_quotType := [quotType of LspaceType].
Canonical LspaceType_eqType := [eqType of LspaceType].
Canonical LspaceType_choiceType := [choiceType of LspaceType].
Canonical LspaceType_eqQuotType := [eqQuotType Lequiv of LspaceType].

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
split; first exact/EFin_measurable_fun.
under eq_integral.
  move=> x _ /=.
  rewrite -(@powere_pose1 _ `|f x|%:E)//.
  over.
exact: lfuny f.
Qed.

Lemma LType2_integrable_sqr (f : LType mu 2) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
split; first exact/EFin_measurable_fun/measurable_fun_exprn.
rewrite (le_lt_trans _ (lfuny f))// ge0_le_integral//.
- apply: measurable_funT_comp => //.
  exact/EFin_measurable_fun/measurable_fun_exprn.
- by move=> x _; rewrite lee_fin power_pos_ge0.
- apply/EFin_measurable_fun.
  under eq_fun do rewrite power_pos_mulrn//.
  exact/measurable_fun_exprn/measurable_funT_comp.
- by move=> t _/=; rewrite lee_fin normrX power_pos_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.
