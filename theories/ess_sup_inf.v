From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals interval_inference ereal.
From mathcomp Require Import topology normedtype sequences esum numfun.
From mathcomp Require Import measure lebesgue_measure.

(**md**************************************************************************)
(* ```                                                                        *)
(*  ess_sup f == essential supremum of the function f : T -> R where T is a   *)
(*               semiRingOfSetsType and R is a realType                       *)
(*  ess_inf f == essential infimum                                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section essential_supremum.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (f g : T -> \bar R) (h k : T -> R).

(* TODO: move *)
Lemma measure0_ae (P : set T) : mu [set: T] = 0 -> \forall x \ae mu, P x.
Proof. by move=> x; exists setT; split. Qed.

Definition ess_sup f := ereal_inf [set y | \forall x \ae mu, f x <= y].

Lemma ess_supEae (f : T -> \bar R) :
  ess_sup f = ereal_inf [set y | \forall x \ae mu, f x <= y].
Proof. by []. Qed.

Lemma ae_le_measureP f y : measurable_fun setT f ->
  (\forall x \ae mu, f x <= y) <-> (mu (f @^-1` `]y, +oo[) = 0).
Proof.
move=> f_meas; have fVroo_meas : d.-measurable (f @^-1` `]y, +oo[).
  by rewrite -[_ @^-1` _]setTI; apply/f_meas=> //; exact/emeasurable_itv.
have setCfVroo : (f @^-1` `]y, +oo[) = ~` [set x | f x <= y].
  by apply: setC_inj; rewrite preimage_setC setCitv/= set_itvxx setU0 setCK.
split.
  move=> [N [dN muN0 inN]]; rewrite (subset_measure0 _ dN)// => x.
  by rewrite setCfVroo; apply: inN.
set N := (X in mu X) => muN0; exists N; rewrite -setCfVroo.
by split => //; exact: fVroo_meas.
Qed.

Lemma ess_supEmu0 (f : T -> \bar R) : measurable_fun setT f ->
   ess_sup f = ereal_inf [set y | mu (f @^-1` `]y, +oo[) = 0].
Proof.
by move=> ?; congr (ereal_inf _); apply/predeqP => r; exact: ae_le_measureP.
Qed.

Lemma ess_sup_ge f : \forall x \ae mu, f x <= ess_sup f.
Proof.
rewrite ess_supEae//; set I := (X in ereal_inf X).
have [->|IN0] := eqVneq I set0.
  by rewrite ereal_inf0; apply: nearW => ?; rewrite leey.
have [u uI uinf] := ereal_inf_seq IN0.
rewrite -(cvg_lim _ uinf)//; near=> x.
rewrite lime_ge//; first by apply/cvgP: uinf.
by apply: nearW; near: x; apply/ae_foralln => n; apply: uI.
Unshelve. all: by end_near. Qed.

Lemma ess_supP f a : reflect (\forall x \ae mu, f x <= a) (ess_sup f <= a).
Proof.
apply: (iffP (ereal_inf_leP _)) => /=; last 2 first.
- by move=> [y fy ya]; near do apply: le_trans ya.
- by move=> fa; exists a.
by rewrite -ess_supEae//; exact: ess_sup_ge.
Unshelve. all: by end_near. Qed.

Lemma le_ess_sup f g : (\forall x \ae mu, f x <= g x) -> ess_sup f <= ess_sup g.
Proof.
move=> fg; apply/ess_supP => //.
near do rewrite (le_trans (near fg _ _))//=.
exact: ess_sup_ge.
Unshelve. all: by end_near. Qed.

Lemma eq_ess_sup f g : (\forall x \ae mu, f x = g x) -> ess_sup f = ess_sup g.
Proof.
move=> fg; apply/eqP; rewrite eq_le !le_ess_sup//=;
  by apply: filterS fg => x ->.
Qed.

Lemma ess_sup_cst r : 0 < mu [set: T] -> ess_sup (cst r) = r.
Proof.
move=> muT_gt0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ess_supP => //; apply: nearW.
have ae_proper := ae_properfilter_algebraOfSetsType muT_gt0.
by near (almost_everywhere mu) => x; near: x; apply: ess_sup_ge.
Unshelve. all: by end_near. Qed.

Lemma ess_sup_ae_cst f r : 0 < mu [set: T] ->
  (\forall x \ae mu, f x = r) -> ess_sup f = r.
Proof. by move=> muT_gt0 /= /eq_ess_sup->; rewrite ess_sup_cst. Qed.

Lemma ess_sup_gee f y : 0 < mu [set: T] ->
  (\forall x \ae mu, y <= f x)%E -> y <= ess_sup f.
Proof. by move=> *; rewrite -(ess_sup_cst y)//; apply: le_ess_sup. Qed.

Lemma abs_sup_eq0_ae_eq f : ess_sup (abse \o f) = 0 -> f = \0 %[ae mu].
Proof.
move=> ess_sup_f_eq0; near=> x => _ /=; apply/eqP.
rewrite -abse_eq0 eq_le abse_ge0 andbT; near: x.
by apply/ess_supP; rewrite ess_sup_f_eq0.
Unshelve. all: by end_near. Qed.

Lemma abs_ess_sup_eq0 f : mu [set: T] > 0 ->
  f = \0 %[ae mu] -> ess_sup (abse \o f) = 0.
Proof.
move=> muT_gt0 f0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ess_supP => /=; near do rewrite (near f0 _ _)//= normr0//.
by rewrite -[0]ess_sup_cst// le_ess_sup//=; near=> x; rewrite abse_ge0.
Unshelve. all: by end_near. Qed.

Lemma ess_sup_pZl f (a : R) : (0 < a)%R ->
  ess_sup (cst a%:E \* f) = a%:E * ess_sup f.
Proof.
move=> /[dup] /ltW a_ge0 a_gt0.
gen have esc_le : a f a_ge0 a_gt0 /
    (ess_sup (cst a%:E \* f) <= a%:E * ess_sup f)%E.
  by apply/ess_supP; near do rewrite /cst/= lee_pmul2l//; apply/ess_supP.
apply/eqP; rewrite eq_le esc_le// -lee_pdivlMl//=.
apply: le_trans (esc_le _ _ _ _); rewrite ?invr_gt0 ?invr_ge0//.
by under eq_fun do rewrite muleA -EFinM mulVf ?mul1e ?gt_eqF//.
Unshelve. all: by end_near. Qed.

Lemma ess_supZl f (a : R) : mu [set: T] > 0 -> (0 <= a)%R ->
  ess_sup (cst a%:E \* f) = a%:E * ess_sup f.
Proof.
move=> muTN0; case: ltgtP => // [a_gt0|<-] _; first exact: ess_sup_pZl.
by under eq_fun do rewrite mul0e; rewrite mul0e ess_sup_cst.
Qed.

Lemma ess_sup_eqNyP f : ess_sup f = -oo <-> \forall x \ae mu, f x = -oo.
Proof.
rewrite (rwP eqP) -leeNy_eq (eq_near (fun=> rwP eqP)).
by under eq_near do rewrite -leeNy_eq; apply/(rwP2 idP (ess_supP _ _)).
Qed.

Lemma ess_supD f g : ess_sup (f \+ g) <= ess_sup f + ess_sup g.
Proof.
by apply/ess_supP; near do rewrite lee_add//; apply/ess_supP.
Unshelve. all: by end_near. Qed.

Lemma ess_sup_absD f g :
  ess_sup (abse \o (f \+ g)) <= ess_sup (abse \o f) + ess_sup (abse \o g).
Proof.
rewrite (le_trans _ (ess_supD _ _))// le_ess_sup//.
by apply/nearW => x; apply/lee_abs_add.
Qed.

End essential_supremum.
Arguments ess_sup_ae_cst {d T R mu f}.
Arguments ess_supP {d T R mu f a}.

Section real_essential_supremum.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types f : T -> R.

Notation ess_supr f := (ess_sup mu (EFin \o f)).

Lemma ess_supr_bounded f : ess_supr f < +oo ->
  exists M, \forall x \ae mu, (f x <= M)%R.
Proof.
set g := EFin \o f => ltfy; have [|supfNy] := eqVneq (ess_sup mu g) -oo.
  by move=> /ess_sup_eqNyP fNy; exists 0%:R; apply: filterS fNy.
have supf_fin : ess_supr f \is a fin_num by case: ess_sup ltfy supfNy.
by exists (fine (ess_supr f)); near do rewrite -lee_fin fineK//; apply/ess_supP.
Unshelve. all: by end_near. Qed.

Lemma ess_sup_eqr0_ae_eq f : ess_supr (normr \o f) = 0 -> f = 0%R %[ae mu].
Proof.
under [X in ess_sup _ X]eq_fun do rewrite /= -abse_EFin.
move=> /abs_sup_eq0_ae_eq; apply: filterS => x /= /(_ _)/eqP.
by rewrite eqe => /(_ _)/eqP.
Qed.

Lemma ess_suprZl f (y : R) : mu setT > 0 -> (0 <= y)%R ->
  ess_supr (cst y \* f)%R = y%:E * ess_supr f.
Proof. by move=> muT_gt0 r_ge0; rewrite -ess_supZl. Qed.

Lemma ess_sup_ger f x : 0 < mu [set: T] -> (forall t, x <= (f t)%:E) ->
  x <= ess_supr f.
Proof. by move=> muT f0; apply/ess_sup_gee => //=; apply: nearW. Qed.

Lemma ess_sup_ler f y : (forall t, (f t)%:E <= y) -> ess_supr f <= y.
Proof. by move=> ?; apply/ess_supP; apply: nearW. Qed.

Lemma ess_sup_cstr y : (0 < mu setT)%E -> (ess_supr (cst y) = y%:E)%E.
Proof. by move=> muN0; rewrite (ess_sup_ae_cst y%:E)//=; apply: nearW. Qed.

Lemma ess_suprD f g : ess_supr (f \+ g) <= ess_supr f + ess_supr g.
Proof. by rewrite (le_trans _ (ess_supD _ _ _)). Qed.

Lemma ess_sup_normD f g :
  ess_supr (normr \o (f \+ g)) <= ess_supr (normr \o f) + ess_supr (normr \o g).
Proof.
rewrite (le_trans _ (ess_suprD _ _))// le_ess_sup//.
by apply/nearW => x; apply/ler_normD.
Qed.

End real_essential_supremum.
Notation ess_supr mu f := (ess_sup mu (EFin \o f)).

Section essential_infimum.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types f : T -> \bar R.

Definition ess_inf f := ereal_sup [set y | \forall x \ae mu, y <= f x].
Notation ess_sup := (ess_sup mu).

Lemma ess_infEae (f : T -> \bar R) :
  ess_inf f = ereal_sup [set y | \forall x \ae mu, y <= f x].
Proof. by []. Qed.

Lemma ess_infEN (f : T -> \bar R) : ess_inf f = - ess_sup (\- f).
Proof.
rewrite ess_supEae ess_infEae ereal_infEN oppeK; congr (ereal_sup _).
apply/seteqP; split=> [y /= y_le|_ [/= y y_ge <-]].
  by exists (- y); rewrite ?oppeK//=; apply: filterS y_le => x; rewrite leeN2.
by apply: filterS y_ge => x; rewrite leeNl.
Qed.

Lemma ess_supEN (f : T -> \bar R) : ess_sup f = - ess_inf (\- f).
Proof.
by rewrite ess_infEN oppeK; apply/eq_ess_sup/nearW => ?; rewrite oppeK.
Qed.

Lemma ess_infN (f : T -> \bar R) : ess_inf (\- f) = - ess_sup f.
Proof. by rewrite ess_supEN oppeK. Qed.

Lemma ess_supN (f : T -> \bar R) : ess_sup (\- f) = - ess_inf f.
Proof. by rewrite ess_infEN oppeK. Qed.

Lemma ess_infP f a : reflect (\forall x \ae mu, a <= f x) (a <= ess_inf f).
Proof.
by rewrite ess_infEN leeNr; apply: (iffP ess_supP);
   apply: filterS => x; rewrite leeN2.
Qed.

Lemma ess_inf_le f : \forall x \ae mu, ess_inf f <= f x.
Proof. exact/ess_infP. Qed.

Lemma le_ess_inf f g : (\forall x \ae mu, f x <= g x) -> ess_inf f <= ess_inf g.
Proof.
move=> fg; apply/ess_infP => //.
near do rewrite (le_trans _ (near fg _ _))//=.
exact: ess_inf_le.
Unshelve. all: by end_near. Qed.

Lemma eq_ess_inf f g : (\forall x \ae mu, f x = g x) -> ess_inf f = ess_inf g.
Proof.
move=> fg; apply/eqP; rewrite eq_le !le_ess_inf//=;
  by apply: filterS fg => x ->.
Qed.

Lemma ess_inf_cst r : 0 < mu [set: T] -> ess_inf (cst r) = r.
Proof.
by move=> ?; rewrite ess_infEN (ess_sup_ae_cst (- r)) ?oppeK//=; apply: nearW.
Qed.

Lemma ess_inf_ae_cst f r : 0 < mu [set: T] ->
  (\forall x \ae mu, f x = r) -> ess_inf f = r.
Proof. by move=> muT_gt0 /= /eq_ess_inf->; rewrite ess_inf_cst. Qed.

Lemma ess_inf_gee f y : 0 < mu [set: T] ->
  (\forall x \ae mu, y <= f x)%E -> y <= ess_inf f.
Proof. by move=> *; rewrite -(ess_inf_cst y)//; apply: le_ess_inf. Qed.

Lemma ess_inf_pZl f (a : R) : (0 < a)%R ->
  (ess_inf (cst a%:E \* f) = a%:E * ess_inf f).
Proof.
move=> a_gt0; rewrite !ess_infEN muleN; congr (- _)%E.
by under eq_fun do rewrite -muleN; rewrite ess_sup_pZl.
Qed.

Lemma ess_infZl f (a : R) : mu [set: T] > 0 -> (0 <= a)%R ->
  (ess_inf (cst a%:E \* f) = a%:E * ess_inf f).
Proof.
move=> muTN0; case: ltgtP => // [a_gt0|<-] _; first exact: ess_inf_pZl.
by under eq_fun do rewrite mul0e; rewrite mul0e ess_inf_cst.
Qed.

Lemma ess_inf_eqyP f : ess_inf f = +oo <-> \forall x \ae mu, f x = +oo.
Proof.
rewrite (rwP eqP) -leye_eq (eq_near (fun=> rwP eqP)).
by under eq_near do rewrite -leye_eq; apply/(rwP2 idP (ess_infP _ _)).
Qed.

Lemma ess_infD f g : ess_inf (f \+ g) >= ess_inf f + ess_inf g.
Proof.
by apply/ess_infP; near do rewrite lee_add//; apply/ess_infP.
Unshelve. all: by end_near. Qed.

End essential_infimum.
Arguments ess_inf_ae_cst {d T R mu f}.
Arguments ess_infP {d T R mu f a}.

Section real_essential_infimum.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types f : T -> R.

Notation ess_infr f := (ess_inf mu (EFin \o f)).

Lemma ess_infr_bounded f : ess_infr f > -oo ->
  exists M, \forall x \ae mu, (f x >= M)%R.
Proof.
set g := EFin \o f => ltfy; have [|inffNy] := eqVneq (ess_inf mu g) +oo.
  by move=> /ess_inf_eqyP fNy; exists 0%:R; apply: filterS fNy.
have inff_fin : ess_infr f \is a fin_num by case: ess_inf ltfy inffNy.
by exists (fine (ess_infr f)); near do rewrite -lee_fin fineK//; apply/ess_infP.
Unshelve. all: by end_near. Qed.

Lemma ess_infrZl f (y : R) : mu setT > 0 -> (0 <= y)%R ->
  ess_infr (cst y \* f)%R = y%:E * ess_infr f.
Proof. by move=> muT_gt0 r_ge0; rewrite -ess_infZl. Qed.

Lemma ess_inf_ger f x : 0 < mu [set: T] -> (forall t, x <= (f t)%:E) ->
  x <= ess_infr f.
Proof. by move=> muT f0; apply/ess_inf_gee => //=; apply: nearW. Qed.

Lemma ess_inf_ler f y : (forall t, y <= (f t)%:E) -> y <= ess_infr f.
Proof. by move=> ?; apply/ess_infP; apply: nearW. Qed.

Lemma ess_inf_cstr y : (0 < mu setT)%E -> (ess_infr (cst y) = y%:E)%E.
Proof. by move=> muN0; rewrite (ess_inf_ae_cst y%:E)//=; apply: nearW. Qed.

End real_essential_infimum.
Notation ess_infr mu f := (ess_inf mu (EFin \o f)).
