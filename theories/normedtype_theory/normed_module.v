(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint.
From mathcomp Require Import archimedean rat interval zmodp vector.
From mathcomp Require Import fieldext falgebra.
From mathcomp Require Import boolp classical_sets filter functions cardinality.
From mathcomp Require Import set_interval interval_inference ereal reals.
From mathcomp Require Import topology function_spaces real_interval.
From mathcomp Require Import prodnormedzmodule tvs num_normedtype.
From mathcomp Require Import ereal_normedtype pseudometric_normed_Zmodule.

(**md**************************************************************************)
(* # Normed modules                                                           *)
(*                                                                            *)
(* We define normed modules. We prove the intermediate value theorem (IVT).   *)
(*                                                                            *)
(* ## Normed modules                                                          *)
(* ```                                                                        *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K       *)
(*                                   The HB class is NormedModule.            *)
(*                           `|x| == the norm of x (notation from ssrnum.v)   *)
(* ```                                                                        *)
(*                                                                            *)
(* We endow `numFieldType` with the types of norm-related notions (accessible *)
(* with `Import numFieldNormedType.Exports`).                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*   pseudoMetric_normed M == an alias for the pseudometric structure defined *)
(*                            from a normed module                            *)
(*                            M : normedZmodType K with K : numFieldType.     *)
(*      Lmodule_isNormed M == factory for a normed module defined using       *)
(*                            an L-module M over R : numFieldType             *)
(* ```                                                                        *)
(* ## Hulls                                                                   *)
(* ```                                                                        *)
(*                        Rhull A == the real interval hull of a set A        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Lipschitz functions                                                     *)
(* ```                                                                        *)
(*                      self_sub f x := f x.1 - f x.2                         *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                   contraction q f == f is q.-lipschitz and q < 1           *)
(*                  is_contraction f == exists q, f is q.-lipschitz and q < 1 *)
(*                                                                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "k .-lipschitz_on f"
  (at level 2, format "k .-lipschitz_on  f").
Reserved Notation "k .-lipschitz_ A f"
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Reserved Notation "k .-lipschitz f" (at level 2, format "k .-lipschitz  f").
Reserved Notation "[ 'lipschitz' E | x 'in' A ]"
  (at level 0, x name, format "[ 'lipschitz'  E  |  x  'in'  A ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Modules with a norm depending on a numDomain *)

HB.mixin Record PseudoMetricNormedZmod_Tvs_isNormedModule K V
    of PseudoMetricNormedZmod K V & Tvs K V := {
  normrZ : forall (l : K) (x : V), `| l *: x | = `| l | * `| x |;
}.

#[short(type="normedModType")]
HB.structure Definition NormedModule (K : numDomainType) :=
  {T of PseudoMetricNormedZmod K T & Tvs K T
   & PseudoMetricNormedZmod_Tvs_isNormedModule K T}.

HB.factory Record PseudoMetricNormedZmod_Lmodule_isNormedModule (K : numFieldType) V
    of PseudoMetricNormedZmod K V & GRing.Lmodule K V := {
 normrZ : forall (l : K) (x : V), `| l *: x | = `| l | * `| x |;
}.

HB.builders Context K V of PseudoMetricNormedZmod_Lmodule_isNormedModule K V.

(* NB: These lemmas are done later with more machinery. They should
   be simplified once normedtype is split, and the present section can
   depend on near lemmas on pseudometricnormedzmodtype? *)
(* add_continuous has been moved to pseudometric_normed_Zmodule.v,
  scale_continuous is proved but is not proved again anymore later in this file *)
Lemma add_continuous : continuous (fun x : V * V => x.1 + x.2).
Proof. exact: add_continuous. Qed.

Lemma scale_continuous : continuous (fun z : K^o * V => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_K => M.
near=> l z => /=; have M0 : 0 < M by [].
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normrZ.
  rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpM2r -?ltr_pdivlMl//.
  by near: z; apply: cvgr_dist_lt; rewrite // mulr_gt0 ?invr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
  by near: z; near: M; apply: cvg_bounded (@cvg_refl _ _).
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma locally_convex :
  exists2 B : set (set V), (forall b, b \in B -> convex b) & basis B.
Proof.
exists [set B | exists x r, B = ball x r].
  move=> b; rewrite inE /= => [[x]] [r] -> z y l.
  rewrite !inE -!ball_normE /= => zx yx l0; rewrite -subr_gt0 => l1.
  have -> : x = l *: x + (1 - l) *: x by rewrite addrC scalerBl subrK scale1r.
  rewrite [X in `|X|](_ : _ = l *: (x - z) + (1 - l) *: (x - y)); last first.
    by rewrite opprD addrACA -scalerBr -scalerBr.
  rewrite (@le_lt_trans _ _ (`|l| * `|x - z| + `|1 - l| * `|x - y|))//.
    by rewrite -!normrZ ler_normD.
  rewrite (@lt_le_trans _ _ (`|l| * r + `|1 - l| * r ))//.
    by rewrite ltr_leD// lter_pM2l// ?normrE ?gt_eqF// ltW.
  by rewrite !gtr0_norm// -mulrDl addrC subrK mul1r.
split.
  move=> B [x] [r] ->.
  rewrite openE/= -ball_normE/= /interior => y /= bxy; rewrite -nbhs_ballE.
  exists (r - `|x - y|) => /=; first by rewrite subr_gt0.
  move=> z; rewrite -ball_normE/= ltrBrDr.
  by apply: le_lt_trans; rewrite [in leRHS]addrC ler_distD.
move=> x B; rewrite -nbhs_ballE/= => -[r] r0 Bxr /=.
by exists (ball x r) => //; split; [exists x, r|exact: ballxx].
Qed.

HB.instance Definition _ :=
  PreTopologicalNmodule_isTopologicalNmodule.Build V add_continuous.
HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalLmodule.Build K V scale_continuous.
HB.instance Definition _ := Uniform_isTvs.Build K V locally_convex.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K V normrZ.

HB.end.

(**md see also `Section standard_topology_pseudoMetricNormedZmod` in
  `pseudometric_normed_Zmodule.v` *)
Section standard_topology_normedMod.
Variable R : numFieldType.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build R R^o (@normrM _).

End standard_topology_normedMod.

Module numFieldNormedType.

Section realType.
Variable (R : realType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End realType.

Section rcfType.
Variable (R : rcfType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End rcfType.

Section archiFieldType.
Variable (R : archiRealFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.RealField.on R.
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.ClosedField.on R.
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.NumField.on R.
End numFieldType.

Module Exports. Export numFieldTopology.Exports. HB.reexport. End Exports.

End numFieldNormedType.
Import numFieldNormedType.Exports.

Definition pseudoMetric_normed (M : Type) : Type := M.

HB.instance Definition _ (K : numFieldType) (M : normedZmodType K) :=
  Choice.on (pseudoMetric_normed M).
HB.instance Definition _ (K : numFieldType) (M : normedZmodType K) :=
  Num.NormedZmodule.on (pseudoMetric_normed M).

Module pseudoMetric_from_normedZmodType.
Section pseudoMetric_from_normedZmodType.
Variables (K : numFieldType) (M : normedZmodType K).

Notation T := (pseudoMetric_normed M).

Definition ball (x : T) (r : K) : set T := ball_ Num.norm x r.

Definition ent : set_system (T * T) := entourage_ ball.

Definition nbhs (x : T) : set_system T := nbhs_ ent x.

Lemma nbhsE : nbhs = nbhs_ ent. Proof. by []. Qed.

#[export] HB.instance Definition _ := hasNbhs.Build T nbhs.

Lemma ball_center x (e : K) : 0 < e -> ball x e x.
Proof. by rewrite /ball/= subrr normr0. Qed.

Lemma ball_sym x y (e : K) : ball x e y -> ball y e x.
Proof. by rewrite /ball /= distrC. Qed.

Lemma ball_triangle x y z e1 e2 : ball x e1 y -> ball y e2 z ->
  ball x (e1 + e2) z.
Proof.
rewrite /ball /= => ? ?.
rewrite -[x](subrK y) -(addrA (x + _)).
by rewrite (le_lt_trans (ler_normD _ _))// ltrD.
Qed.

Lemma entourageE : ent = entourage_ ball.
Proof. by []. Qed.

#[export] HB.instance Definition _ := @Nbhs_isPseudoMetric.Build K T
  ent nbhsE ball ball_center ball_sym ball_triangle entourageE.

End pseudoMetric_from_normedZmodType.
Module Exports. HB.reexport. End Exports.
End pseudoMetric_from_normedZmodType.
Export pseudoMetric_from_normedZmodType.Exports.

HB.factory Record Lmodule_isNormed (R : numFieldType) M
    of GRing.Lmodule R M := {
 norm : M -> R;
 ler_normD : forall x y, norm (x + y) <= norm x + norm y ;
 normrZ : forall (l : R) (x : M), norm (l *: x) = `|l| * norm x ;
 normr0_eq0 : forall x : M, norm x = 0 -> x = 0
}.

HB.builders Context R M of Lmodule_isNormed R M.

Lemma normrMn x n : norm (x *+ n) = norm x *+ n.
Proof.
have := normrZ n%:R x; rewrite ger0_norm// mulr_natl => <-.
by rewrite scaler_nat.
Qed.

Lemma normrN x : norm (- x) = norm x.
Proof. by have := normrZ (- 1)%R x; rewrite scaleN1r normrN normr1 mul1r. Qed.

HB.instance Definition _ := Num.Zmodule_isNormed.Build
  R M ler_normD normr0_eq0 normrMn normrN.

HB.instance Definition _ := PseudoMetric.copy M (pseudoMetric_normed M).

HB.instance Definition _ := isPointed.Build M 0.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R M erefl.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build R M normrZ.

HB.end.

Lemma scaler1 {R : numFieldType} h : h%:A = h :> R.
Proof. by rewrite /GRing.scale/= mulr1. Qed.

Lemma limf_esup_dnbhsN {R : realType} (f : R -> \bar R) (a : R) :
  limf_esup f a^' = limf_esup (fun x => f (- x)%R) (- a)%R^'.
Proof.
rewrite /limf_esup dnbhsN image_comp/=.
congr (ereal_inf [set _ | _ in _]); apply/funext => A /=.
rewrite image_comp/= -compA (_ : _ \o _ = idfun)// funeqE => x/=.
by rewrite opprK.
Qed.

Lemma cvg_patch {R : realType} (f : R -> R^o) (a b : R) (x : R) : (a < b)%R ->
  x \in `]a, b[ ->
  f @ (x : subspace `[a, b]) --> f x ->
  (f \_ `[a, b] x) @[x --> x] --> f x.
Proof.
move=> ab xab xf; apply/cvgrPdist_lt => /= e e0.
move/cvgrPdist_lt : xf => /(_ e e0) xf.
near=> z.
rewrite patchE ifT//; last first.
  rewrite inE; apply: subset_itv_oo_cc.
  by near: z; exact: near_in_itvoo.
near: z.
rewrite /prop_near1 /nbhs/= /nbhs_subspace ifT// in xf; last first.
  by rewrite inE/=; exact: subset_itv_oo_cc xab.
case: xf => x0 /= x00 xf.
near=> z.
apply: xf => //=.
rewrite inE; apply: subset_itv_oo_cc.
by near: z; exact: near_in_itvoo.
Unshelve. all: by end_near. Qed.

Section NormedModule_numDomainType.
Variables (K : numDomainType) (V : normedModType K).

Lemma normrZV (x : V) : `|x| \in GRing.unit -> `| `| x |^-1 *: x | = 1.
Proof. by move=> nxu; rewrite normrZ normrV// normr_id mulVr. Qed.

Lemma near_shift (y x : V) (P : set V) :
   (\near x, P x) = (\forall z \near y, (P \o shift (x - y)) z).
Proof.
rewrite propeqE nbhs0P [X in _ <-> X]nbhs0P/= -propeqE.
by apply: eq_near => e; rewrite [_ + _ + _]addrC subrKA.
Qed.

Lemma cvg_comp_shift {T : Type} (x y : V) (f : V -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Lemma ball_open (x : V) (r : K) : 0 < r -> open (ball x r).
Proof.
rewrite openE -ball_normE /interior => r0 y /= Bxy; near=> z.
rewrite /= (le_lt_trans (ler_distD y _ _)) // addrC -ltrBrDr.
by near: z; apply: cvgr_dist_lt; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ball_open_nbhs (x : V) (r : K) : 0 < r -> open_nbhs x (ball x r).
Proof. by move=> e0; split; [exact: ball_open|exact: ballxx]. Qed.

End NormedModule_numDomainType.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Section NormedModule_numFieldType.
Variables (K : numFieldType) (V : normedModType K).

Lemma normfZV (x : V) : x != 0 -> `| `|x|^-1 *: x | = 1.
Proof. by rewrite -normr_eq0 -unitfE => /normrZV->. Qed.

Lemma cvg_at_rightE (f : K -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'+).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_right _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _]; apply: xe_A.
Qed.

Lemma cvg_at_leftE (f : K -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'-).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_left _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _].
by apply: xe_A => //; rewrite eq_sym.
Qed.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).
Proof. exact: scale_continuous. Abort.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous _ _ (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous _ _ (_, _))).
Qed.

End NormedModule_numFieldType.
Arguments cvg_at_rightE {K V} f x.
Arguments cvg_at_leftE {K V} f x.

Section NormedModule_continuous.
Variables (K : numFieldType) (U V : normedModType K).

Lemma continuous_shift (f : U -> V) u :
  {for u, continuous f} = {for 0, continuous (f \o shift u)}.
Proof.
by rewrite [in RHS]forE /continuous_at/= add0r cvg_comp_shift add0r.
Qed.

Lemma continuous_withinNshiftx (f : U -> V) u :
  f \o shift u @ 0^' --> f u <-> {for u, continuous f}.
Proof.
rewrite continuous_shift; split=> [cfu|].
  by apply/(continuous_withinNx _ _).2/(cvg_trans cfu); rewrite /= add0r.
by move/(continuous_withinNx _ _).1/cvg_trans; apply; rewrite /= add0r.
Qed.

End NormedModule_continuous.

Lemma near0Z {R : numFieldType} {V : normedModType R} (y : V) (P : set V) :
  (\forall x \near 0, P x) -> (\forall k \near 0, P (k *: y)).
Proof.
by have /= := @scalel_continuous R V y 0 _; rewrite scale0r; apply.
Qed.

Section NVS_continuity_mul.
Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K * K => z.1 * z.2).
Proof. exact: scale_continuous. Qed.

Lemma mulrl_continuous (x : K) : continuous ( *%R x).
Proof. exact: scaler_continuous. Qed.

Lemma mulrr_continuous (y : K) : continuous ( *%R^~ y : K -> K).
Proof. exact: scalel_continuous. Qed.

Lemma inv_continuous (x : K) : x != 0 -> {for x, continuous (@GRing.inv K)}.
Proof.
move=> x_neq0; have nx_gt0 : `|x| > 0 by rewrite normr_gt0.
apply/(@cvgrPdist_ltp _ _ _ (nbhs x)); near (0 : K)^'+ => d. near=> e.
near=> y; have y_neq0 : y != 0 by near: y; apply: (cvgr_neq0 x).
rewrite /= -div1r -[y^-1]div1r -mulNr addf_div// mul1r mulN1r normrM normfV.
rewrite ltr_pdivrMr ?normr_gt0 ?mulf_neq0// (@lt_le_trans _ _ (e * d))//.
  by near: y;  apply: cvgr_distC_lt => //; rewrite mulr_gt0.
rewrite ler_pM2l => //=; rewrite normrM -ler_pdivrMl//.
near: y; apply: (cvgr_norm_ge x) => //; rewrite ltr_pdivrMl//.
by near: d; apply: nbhs_right_lt; rewrite mulr_gt0.
Unshelve. all: by end_near. Qed.

End NVS_continuity_mul.

Section cvg_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof.
move=> ? ?; apply: continuous2_cvg => //.
have := (@scale_continuous K V (k, a)).
rewrite /continuous_at/=.
exact.
Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZr_tmp s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr_tmp s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZr_tmp  _); apply. Qed.

Lemma cvgZl_tmp k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. by apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl_tmp k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZl_tmp  _); apply. Qed.

Lemma is_cvgZlE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZl_tmp k^-1)|/(@cvgZl_tmp k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

End cvg_composition_normed.
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `cvgZr_tmp`")]
Notation cvgZl := cvgZr_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgZr_tmp`")]
Notation is_cvgZl := is_cvgZr_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `cvgZl_tmp`")]
Notation cvgZr := cvgZl_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgZl_tmp`")]
Notation is_cvgZr := is_cvgZl_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgZlE`")]
Notation is_cvgZrE := is_cvgZlE (only parsing).

Section cvg_composition_field.
Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma cvgV f a : a != 0 -> f @ F --> a -> f\^-1 @ F --> a^-1.
Proof.
by move=> k_neq0 f_cvg; apply: continuous_cvg => //; apply: inv_continuous.
Qed.

Lemma cvgVP f a : a != 0 -> f\^-1 @ F --> a^-1 <-> f @ F --> a.
Proof.
move=> aN0; split=> /(cvgV _); last exact.
by rewrite invrK invr_eq0 inv_funK; apply.
Qed.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg (f\^-1 @ F).
Proof. by move=> /cvgV cvf /cvf /cvgP. Qed.

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f \* g) @ F --> a * b.
Proof. exact: cvgZ. Qed.

Lemma cvgMr_tmp f a b : f @ F --> a -> f x * b @[x --> F] --> a * b.
Proof. exact: cvgZr_tmp. Qed.

Lemma cvgMl_tmp g a b : g @ F --> b -> a * g x @[x --> F] --> a * b.
Proof. exact: cvgZl_tmp. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMl_tmp g a (f := fun=> a) : cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZl_tmp. Qed.

Lemma is_cvgMlE_tmp g a (f := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (g @ F).
Proof. exact: is_cvgZlE. Qed.

Lemma is_cvgMr_tmp f a (g := fun=> a) : cvg (f @ F) -> cvg (f \* g @ F).
Proof.
move=> f_cvg; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMl_tmp.
Qed.

Lemma is_cvgMrE_tmp f a (g := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (f @ F).
Proof.
move=> a_neq0; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMlE_tmp.
Qed.

End cvg_composition_field.
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `cvgMr_tmp`")]
Notation cvgMl := cvgMr_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `cvgMl_tmp`")]
Notation cvgMr := cvgMl_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgMl_tmp`")]
Notation is_cvgMr := is_cvgMl_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgMr_tmp`")]
Notation is_cvgMl := is_cvgMr_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgMrE_tmp`")]
Notation is_cvgMlE := is_cvgMrE_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `is_cvgMlE_tmp`")]
Notation is_cvgMrE := is_cvgMlE_tmp (only parsing).

Section limit_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
  lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; exact: cvgZ. Qed.

Lemma limZr_tmp s a : cvg (s @ F) ->
  lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; exact: cvgZr_tmp. Qed.

Lemma limZl_tmp k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; exact: cvgZl_tmp. Qed.

End limit_composition_normed.
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `limZr_tmp`")]
Notation limZl := limZr_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `limZl_tmp`")]
Notation limZr := limZl_tmp (only parsing).

Section limit_composition_field.
Context {K : numFieldType} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
  lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; exact: cvgM. Qed.

End limit_composition_field.

Section cvg_composition_field_proper.
Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma limV f : lim (f @ F) != 0 -> lim (f\^-1 @ F) = (lim (f @ F))^-1.
Proof.
by move=> ?; apply: cvg_lim => //; apply: cvgV => //; exact: cvgNpoint.
Qed.

Lemma is_cvgVE f : lim (f @ F) != 0 -> cvg (f\^-1 @ F) = cvg (f @ F).
Proof.
move=> ?; apply/propeqP; split=> /is_cvgV; last exact.
by rewrite inv_funK; apply; rewrite limV ?invr_eq0.
Qed.

End cvg_composition_field_proper.

Section ProperFilterRealType.
Context {T : Type} {F : set_system T} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g h : T -> R) (a b : R).

Lemma cvgr_to_ge f a b : f @ F --> a -> (\near F, b <= f F) -> b <= a.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_ge _ b))/[apply]. Qed.

Lemma cvgr_to_le f a b : f @ F --> a -> (\near F, f F <= b) -> a <= b.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_le _ b))/[apply]. Qed.

Lemma limr_ge x f : cvg (f @ F) -> (\near F, x <= f F) -> x <= lim (f @ F).
Proof. exact: cvgr_to_ge. Qed.

Lemma limr_le x f : cvg (f @ F) -> (\near F, x >= f F) -> x >= lim (f @ F).
Proof. exact: cvgr_to_le. Qed.

End ProperFilterRealType.

Section local_continuity.
Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K) (x : T) (k : K) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Proof. by move=> f_cont g_cont; apply: cvgD. Qed.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Proof. by move=> f_cont g_cont; apply: cvgB. Qed.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Proof. by move=> ? ?; apply: cvgZ. Qed.

Lemma continuousZl_tmp f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; exact: cvgZl_tmp. Qed.

Lemma continuousZr_tmp s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; exact: cvgZr_tmp. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s \* t)}.
Proof. by move=> f_cont g_cont; exact: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1%R)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `continuousZl_tmp`")]
Notation continuousZr := continuousZl_tmp (only parsing).
#[deprecated(since="mathcomp-analysis 1.12.0", note="renamed to `continuousZr_tmp`")]
Notation continuousZl := continuousZr_tmp (only parsing).

Section cvg_fin.
Context {R : numFieldType}.

Section filter.
Context {F : set_system \bar R} {FF : Filter F}.

Lemma fine_fcvg a : F --> a%:E -> fine @ F --> a.
Proof.
move=> /(_ _)/= Fa; apply/cvgrPdist_lt=> // _/posnumP[e]; rewrite near_simpl.
by apply: Fa; apply/nbhs_EFin => /=; apply: (@cvgr_dist_lt _ _ _ (nbhs a)).
(* BUG: using cvgr_dist_lt without (nbhs _) expands the definition of nbhs, *)
(*    so that it is not recognized as a filter anymore *)
Qed.

Lemma fcvg_is_fine a : F --> a%:E -> \near F, F \is a fin_num.
Proof. by apply; apply/nbhs_EFin; near=> x. Unshelve. all: by end_near. Qed.

End filter.

Section limit.
Context {I : Type} {F : set_system I} {FF : Filter F} (f : I -> \bar R).

Lemma fine_cvg a : f @ F --> a%:E -> fine \o f @ F --> a.
Proof. exact: fine_fcvg. Qed.

Lemma cvg_is_fine a : f @ F --> a%:E -> \near F, f F \is a fin_num.
Proof. exact: fcvg_is_fine. Qed.

Lemma cvg_EFin a : (\near F, f F \is a fin_num) -> fine \o f @ F --> a ->
  f @ F --> a%:E.
Proof.
move=> Ffin Fa P/= /nbhs_EFin /Fa; rewrite !near_simpl.
by apply: filterS2 Ffin => x /fineK->.
Qed.

Lemma fine_cvgP a :
   f @ F --> a%:E <-> (\near F, f F \is a fin_num) /\ fine \o f @ F --> a.
Proof.
by split;[split;[exact: (@cvg_is_fine a)|exact: fine_cvg]|case; apply: cvg_EFin].
Qed.

Lemma neq0_fine_cvgP a : a != 0 -> f @ F --> a%:E <-> fine \o f @ F --> a.
Proof.
move=> a_neq0; split=> [|Fa]; first exact: fine_cvg.
apply: cvg_EFin=> //; near (0 : R)^'+ => e.
have lea : e <= `|a| by near: e; apply: nbhs_right_le; rewrite normr_gt0.
near=> x; have : `|a - fine (f x)| < e by near: x; apply: cvgr_dist_lt.
by case: f=> //=; rewrite subr0; apply: contra_ltT.
Unshelve. all: by end_near. Qed.

End limit.

End cvg_fin.

Section ecvg_realFieldType.
Context {I} {F : set_system I} {FF : Filter F} {R : realFieldType}.
Implicit Types f g u v : I -> \bar R.
Local Open Scope ereal_scope.

Lemma cvgeD f g a b :
  a +? b -> f @ F --> a -> g @ F --> b -> f \+ g @ F --> a + b.
Proof.
have yE u v x : u @ F --> +oo -> v @ F --> x%:E -> u \+ v @ F --> +oo.
  move=> /cvgeyPge/= foo /fine_cvgP[Fg gb]; apply/cvgeyPgey.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -leeBlDr// (@le_trans _ _ (A - (x - 1))%:E)//; last by near: n.
  rewrite ?EFinB leeB// leeBlDr// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distlDr// ltW//; near: n; apply: cvgr_dist_lt.
have NyE u v x : u @ F --> -oo -> v @ F --> x%:E -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle/= foo /fine_cvgP -[Fg gb]; apply/cvgeNyPleNy.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -leeBrDr// (@le_trans _ _ (A - (x + 1))%:E)//; first by near: n.
  rewrite ?EFinB ?EFinD leeB// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distlCDr// ltW//; near: n; apply: cvgr_dist_lt.
have yyE u v : u @ F --> +oo -> v @ F --> +oo -> u \+ v @ F --> +oo.
  move=> /cvgeyPge foo /cvgeyPge goo; apply/cvgeyPge => A; near=> y.
  by rewrite -[leLHS]adde0 leeD//; near: y; [apply: foo|apply: goo].
have NyNyE u v : u @ F --> -oo -> v @ F --> -oo -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle foo /cvgeNyPle goo; apply/cvgeNyPle => A; near=> y.
  by rewrite -[leRHS]adde0 leeD//; near: y; [apply: foo|apply: goo].
have addfC u v : u \+ v = v \+ u.
  by apply/funeqP => x; rewrite /= addeC.
move: a b => [a| |] [b| |] //= _; rewrite ?(addey, addye, addeNy, addNye)//=;
  do ?by [apply: yE|apply: NyE|apply: yyE|apply: NyNyE].
- move=> /fine_cvgP[Ff fa] /fine_cvgP[Fg ga]; rewrite -EFinD.
  apply/fine_cvgP; split.
    by near do [rewrite fin_numD; apply/andP; split].
  apply: (@cvg_trans _ ((fine \o f) \+ (fine \o g) @ F))%R; last exact: cvgD.
  by apply: near_eq_cvg; near do rewrite /= fineD//.
- by move=> /[swap]; rewrite addfC; apply: yE.
- by move=> /[swap]; rewrite addfC; apply: NyE.
Unshelve. all: by end_near. Qed.

Lemma cvgeN f x : f @ F --> x -> - f x @[x --> F] --> - x.
Proof. by move=> ?; apply: continuous_cvg => //; exact: oppe_continuous. Qed.

Lemma cvgeNP f a : - f x @[x --> F] --> - a <-> f @ F --> a.
Proof.
by split=> /cvgeN//; rewrite oppeK//; under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvgeB f g a b :
  a +? - b -> f @ F --> a -> g @ F --> b -> f \- g @ F --> a - b.
Proof. by move=> ab fa gb; apply: cvgeD => //; exact: cvgeN. Qed.

Lemma sube_cvg0 f (k : \bar R) :
  k \is a fin_num -> (fun x => f x - k) @ F --> 0 <-> f @ F --> k.
Proof.
move=> kfin; split.
  move=> /cvgeD-/(_ (cst k) _ isT (cvg_cst _)).
  by rewrite add0e; under eq_fun => x do rewrite subeK//.
move: k kfin => [k _ fk| |]//; rewrite -(@subee _ k%:E)//.
by apply: cvgeB => //; exact: cvg_cst.
Qed.

Lemma abse_continuous : continuous (@abse R).
Proof.
case=> [r|A /= [r [rreal rA]]|A /= [r [rreal rA]]]/=.
- exact/(cvg_comp _ _ (@norm_continuous _ R r)).
- by exists r; split => // y ry; apply: rA; rewrite (lt_le_trans ry)// lee_abs.
- exists (- r)%R; rewrite realN; split => // y; rewrite EFinN -lteNr => yr.
  by apply: rA; rewrite (lt_le_trans yr)// -abseN lee_abs.
Qed.

Lemma cvg_abse f (a : \bar R) : f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Proof. by apply: continuous_cvg => //; exact: abse_continuous. Qed.

Lemma is_cvg_abse (f : I -> \bar R) : cvg (f @ F) -> cvg (`|f x|%E @[x --> F]).
Proof. by move/cvg_abse/cvgP. Qed.

Lemma is_cvgeN f : cvg (f @ F) -> cvg (\- f @ F).
Proof. by move=> /cvg_ex[l fl]; apply: (cvgP (- l)); exact: cvgeN. Qed.

Lemma is_cvgeNE f : cvg (\- f @ F) = cvg (f @ F).
Proof.
rewrite propeqE; split=> /cvgeNP/cvgP//.
by under [X in X -> _]eq_is_cvg do rewrite oppeK.
Qed.

Lemma mule_continuous (r : R) : continuous (mule r%:E).
Proof.
rewrite /continuous_at; wlog r0 : r / (r > 0)%R => [hwlog|].
  have [r0|r0|->] := ltrgtP r 0; do ?exact: hwlog; last first.
    by move=> x; rewrite mul0e; apply: cvg_near_cst; near=> y; rewrite mul0e.
  have -> : *%E r%:E = \- ( *%E (- r)%:E ).
    by apply/funeqP=> x /=; rewrite EFinN mulNe oppeK.
  move=> x; apply: (continuous_comp (hwlog (- r)%R _ _)); rewrite ?oppr_gt0//.
  exact: oppe_continuous.
move=> [s||]/=.
- rewrite -EFinM; apply: cvg_EFin => /=.
    by apply/nbhs_EFin; near do rewrite fin_numM//.
  move=> P /= Prs; apply/nbhs_EFin=> //=.
  by apply: near_fun => //=; apply: continuousM => //=; apply: cvg_cst.
- rewrite gt0_muley ?lte_fin// => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x rux; apply: uA; move: rux; rewrite EFinM lte_pdivrMl.
- rewrite gt0_muleNy ?lte_fin// => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x xru; apply: uA; move: xru; rewrite EFinM lte_pdivlMl.
Unshelve. all: by end_near. Qed.

Lemma cvgeZl f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => y * f n) @ F --> y * x.
Proof. by move: y => [r| |]// _ /cvg_comp; apply; exact: mule_continuous. Qed.

Lemma is_cvgeZl f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => y * f n) @ F).
Proof. by move=> fy /(cvgeZl fy)/cvgP. Qed.

Lemma cvgeZr f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => f n * y) @ F --> x * y.
Proof.
by move=> ? ?; rewrite muleC; under eq_fun do rewrite muleC; exact: cvgeZl.
Qed.

Lemma is_cvgeZr f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => f n * y) @ F).
Proof. by move=> fy /(cvgeZr fy)/cvgP. Qed.

Lemma cvg_abse0P f : abse \o f @ F --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_abse; rewrite abse0.
move=> /cvg_ballP f0; apply/cvg_ballP => _/posnumP[e].
have := [elaborate f0 _ (gt0 e)].
rewrite !near_simpl => absf0; rewrite near_simpl.
apply: filterS absf0 => x /=; rewrite /ball/= /ereal_ball !contract0 !sub0r !normrN.
have [fx0|fx0] := leP 0 (f x); first by rewrite gee0_abs.
by rewrite (lte0_abs fx0) contractN normrN.
Qed.

Let cvgeM_gt0_pinfty f g b :
  (0 < b)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b_gt0 /cvgeyPge foo /fine_cvgP[gfin gb]; apply/cvgeyPgey.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite (@le_trans _ _ (f n * e%:E))// ?lee_pmul// ?lee_fin//.
- by rewrite -lee_pdivrMr ?divr_gt0//; near: n; apply: foo.
- by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
by near: n; apply: (cvgr_ge b).
Unshelve. all: end_near. Qed.

Let cvgeM_lt0_pinfty  f g b :
  (b < 0)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 /cvgeyPge foo /fine_cvgP -[gfin gb]; apply/cvgeNyPleNy.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite -leeN2 -muleN (@le_trans _ _ (f n * e%:E))//.
  by rewrite -lee_pdivrMr ?mulr_gt0 ?oppr_gt0//; near: n; apply: foo.
rewrite lee_pmul ?lee_fin//.
  by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
near: n; apply: (cvgr_ge (- b)); rewrite 1?cvgNP//.
by near: e; apply: nbhs_right_lt; rewrite oppr_gt0.
Unshelve. all: end_near. Qed.

Let cvgeM_gt0_ninfty f g b :
  (0 < b)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_lt0_pinfty _ _ (- b)%R); first by rewrite oppr_lt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Let cvgeM_lt0_ninfty f g b :
  (b < 0)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_gt0_pinfty _ _ (- b)%R); first by rewrite oppr_gt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Lemma cvgeM f g (a b : \bar R) :
 a *? b -> f @ F --> a -> g @ F --> b -> f \* g @ F --> a * b.
Proof.
move=> [:apoo] [:bnoo] [:poopoo] [:poonoo]; move: a b => [a| |] [b| |] //.
- move=> _ /fine_cvgP[finf fa] /fine_cvgP[fing gb].
  apply/fine_cvgP; split.
    by near do apply: fin_numM; [apply: finf | apply: fing].
  apply: (@cvg_trans _ (((fine \o f) \* (fine \o g)) @ F)%R).
    apply: near_eq_cvg; near=> n => //=.
    rewrite -[in RHS](@fineK _ (f n)); last by near: n; exact: finf.
    by rewrite -[in RHS](@fineK _ (g n)) //; near: n; exact: fing.
  exact: cvgM.
- move: f g a; abstract: apoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulry ltr0_sg// mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_pinfty a0).
  + rewrite mulry gtr0_sg// mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_pinfty a0).
  + by rewrite /mule_def eqxx.
- move: f g a; abstract: bnoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulrNy ltr0_sg// mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_ninfty a0).
  + rewrite mulrNy gtr0_sg// mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_ninfty a0).
  + by rewrite /mule_def eqxx.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: apoo.
- move=> _; move: f g; abstract: poopoo.
  move=> {}f {}g /cvgeyPge foo /cvgeyPge goo.
  rewrite mulyy; apply/cvgeyPgey; near=> A; near=> n.
  have A_gt0 : (0 <= A)%R by [].
  by rewrite -[leLHS]mule1 lee_pmul//=; near: n; [apply: foo|apply: goo].
- move=> _; move: f g; abstract: poonoo.
  move=> {}f {}g /cvgeyPge foo /cvgeNyPle goo.
  rewrite mulyNy; apply/cvgeNyPle => A; near=> n.
  rewrite (@le_trans _ _ (g n))//; last by near: n; exact: goo.
  apply: lee_nemull; last by near: n; apply: foo.
  by rewrite (@le_trans _ _ (- 1)%:E)//; near: n; apply: goo; rewrite ltrN10.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: bnoo.
- move=> _ foo goo.
  by under eq_fun do rewrite muleC; exact: poonoo.
- move=> _ foo goo; rewrite mulNyNy -mulyy.
  by under eq_fun do rewrite -muleNN; apply: poopoo;
    rewrite -/(- -oo); apply: cvgeN.
Unshelve. all: end_near. Qed.

End ecvg_realFieldType.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `sube_cvg0`")]
Notation cvge_sub0 := sube_cvg0 (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `cvgeZl`")]
Notation cvgeMl := cvgeZl (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `is_cvgeZl`")]
Notation is_cvgeMl := is_cvgeZl (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `cvgeZr`")]
Notation cvgeMr := cvgeZr (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `is_cvgeZr`")]
Notation is_cvgeMr := is_cvgeZr (only parsing).

Section max_cts.
Context {R : realType} {T : topologicalType}.

Lemma continuous_min (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \min g)}.
Proof.
move=> ctsf ctsg.
under [_ \min _]eq_fun => ? do rewrite minr_absE.
apply: cvgM; [|exact: cvg_cst]; apply: cvgD; first exact: cvgD.
by apply: cvgN; apply: cvg_norm; apply: cvgB.
Qed.

Lemma continuous_max (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \max g)}.
Proof.
move=> ctsf ctsg.
under [_ \max _]eq_fun => ? do rewrite maxr_absE.
apply: cvgM; [|exact: cvg_cst]; apply: cvgD; first exact: cvgD.
by apply: cvg_norm; apply: cvgB.
Qed.

End max_cts.

Lemma limit_pointP (T : archiRealFieldType) (A : set T) (x : T) :
  limit_point A x <-> exists a_ : nat -> T,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ @ \oo --> x].
Proof.
split=> [Ax|[a_ [aTA a_x] ax]]; last first.
  move=> U /ax[m _ a_U]; near \oo => n; exists (a_ n); split => //.
  by apply aTA; exists n.
  by apply a_U; near: n; exists m.
pose U := fun n : nat => [set z : T | `|x - z| < n.+1%:R^-1].
suff /(_ _)/cid-/all_sig[a_ anx] : forall n, exists a, a != x /\ (U n `&` A) a.
  exists a_; split.
  - by move=> a [n _ <-]; have [? []] := anx n.
  - by move=> n; have [] := anx n.
  - apply/cvgrPdist_lt => _/posnumP[e]; near=> n;  have [? [] Uan Aan] := anx n.
    by rewrite (lt_le_trans Uan)// ltW//; near: n; exact: near_infty_natSinv_lt.
move=> n; have : nbhs (x : T) (U n).
  by apply/(nbhs_ballP (x:T) (U n)); rewrite nbhs_ballE; exists n.+1%:R^-1 => //=.
by move/Ax/cid => [/= an [anx Aan Uan]]; exists an.
Unshelve. all: by end_near. Qed.

Lemma limit_point_infinite_setP {R : archiRealFieldType} (E : set R) (a : R) :
  limit_point E a <-> (forall U, nbhs a U -> infinite_set (U `&` E)).
Proof.
split=> [Ea V aV|]; last first.
  move=> aE U /aE /infiniteP /pcard_leP /injfunPex[/= f funf injf].
  have [f0a|f0a] := eqVneq (f O) a; last first.
    by exists (f 0); case: (funf 0 Logic.I).
  have [Uf1 Ef1]:= funf 1 Logic.I.
  exists (f 1); split=> //; apply/eqP => f1a.
  have := injf 1 0 (in_setT _) (in_setT _).
  by rewrite f1a f0a => /(_ erefl); exact/eqP/oner_neq0.
(* we build 2 sequences a_ and r_ s.t. a_i and r_i have the properties: *)
pose elt_prop (ar : R * R) := [/\ ball a ar.2 `<=` V,
  ar.1 \in E, ar.1 \in (ball a ar.2 : set R), ar.2 > 0 & ar.1 != a].
pose elt_type := {ar : R * R | elt_prop ar}.
pose a_ (x : elt_type) := (proj1_sig x).2.
pose r_ (x : elt_type) := (proj1_sig x).1.
(* two successive (a_i, r_i) and (a_j, r_j) satisfy the relation: *)
pose elt_rel i j := `|a - r_ i| = a_ j /\ ball a (a_ j) `<=` ball a (a_ i) /\
  `|a - r_ j| < `|a - r_ i| /\ r_ i != r_ j.
move: aV => -[r0/= r0_gt0 ar0V].
pose V0 : set R := ball a r0.
move/limit_pointP : Ea => [y_ [y_E y_neq_a y_cvg_a]].
have [a0 [a0a a0V0 a0E]] : exists a0, [/\ a0 != a, a0 \in V0 & a0 \in E].
  move/cvgrPdist_lt : y_cvg_a => /(_ _ r0_gt0)[M _ May_r0].
  exists (y_ M); split=> //.
  - by apply/mem_set/May_r0 => /=.
  - by apply/mem_set/y_E/imageT.
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0 = exist _ (a0, r0) (And5 ar0V a0E a0V0 r0_gt0 a0a) /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice => -[[ai ri] [/= ariV xE aiari ri_gt0 aia]].
  pose rj : R := `|a - ai|.
  have rj_gt0 : 0 < rj by rewrite /rj normr_gt0 subr_eq0 eq_sym.
  apply/cid; move/cvgrPdist_lt : y_cvg_a => /(_ _ rj_gt0)[M/= _ May_rj].
  pose Vj : set R := ball a rj.
  have VjV : Vj `<=` V.
    apply: subset_trans ariV => z /lt_trans; apply.
    by move: aiari; rewrite inE.
  have y_MVj : y_ M \in Vj.
    rewrite inE; apply: (@lt_le_trans _ _ rj) => //.
    by apply: May_rj => /=.
  have y_ME : y_ M \in E by rewrite inE; apply/y_E/imageT.
  exists (exist _ (y_ M, rj) (And5 VjV y_ME y_MVj rj_gt0 (y_neq_a M))) => /=.
  split; first exact.
  split; rewrite /a_ /r_/=.
    by apply: le_ball; move: aiari; rewrite inE => /ltW.
  split; first by move: y_MVj; rewrite inE.
  by apply/eqP => aiyM; move: y_MVj; rewrite -aiyM inE /Vj /ball/= /rj ltxx.
apply/infiniteP/pcard_leP/injfunPex => /=; exists (r_ \o v).
  move=> n _; rewrite /r_ /=.
  by case: (v n) => -[ai ri] [/= ariV /set_mem Eai /set_mem/ariV aiari _ _].
have arv q p : (p < q)%N -> `|a - r_ (v q)| < `|a - r_ (v p)|.
  elim: q p => [[]//|q ih p].
  by rewrite ltnS leq_eqVlt => /predU1P[->|/ih]; last apply: lt_trans;
    by case: (Pv q) => _ [] _ [].
move=> p q _ _ /=; apply: contraPP => /eqP.
by rewrite neq_lt => /orP[] /arv /[swap] ->; rewrite ltxx.
Qed.

Lemma limit_point_setD {R : archiRealFieldType} (A V : set R) a :
  finite_set V -> limit_point A a -> limit_point (A `\` V) a.
Proof.
move=> finV /limit_point_infinite_setP aA.
apply/limit_point_infinite_setP => U aU.
by rewrite setIDA; apply: infinite_setD => //; exact: aA.
Qed.

Lemma EFin_lim (R : realFieldType) (f : nat -> R) : cvgn f ->
  limn (EFin \o f) = (limn f)%:E.
Proof.
move=> cf; apply: cvg_lim => //; move/cvg_ex : cf => [l fl].
by apply: (cvg_comp _ _ fl); rewrite (cvg_lim _ fl).
Qed.

Section ecvg_realFieldType_proper.
Context {I} {F : set_system I} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g : I -> \bar R) (u v : I -> R) (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma is_cvgeD f g :
  lim (f @ F) +? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \+ g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeD fg fc gc. Qed.

Lemma limeD f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) +? lim (g @ F) ->
  lim (f \+ g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeD. Qed.

Lemma limeMl f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => y * f n) @ F) = y * lim (f @ F).
Proof. by move=> yfn cf; apply/cvg_lim => //; exact: cvgeZl. Qed.

Lemma limeMr f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => f n * y) @ F) = lim (f @ F) * y.
Proof. by move=> yfn cf; apply/cvg_lim => //; apply: cvgeZr. Qed.

Lemma is_cvgeM f g :
  lim (f @ F) *? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeM fg fc gc. Qed.

Lemma limeM f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) *? lim (g @ F) ->
  lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeM. Qed.

Lemma limeN f : cvg (f @ F) -> lim (\- f @ F) = - lim (f @ F).
Proof. by move=> cf; apply/cvg_lim => //; apply: cvgeN. Qed.

Lemma cvge_ge f a b : (\forall x \near F, b <= f x) -> f @ F --> a -> b <= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_ge//=; apply: cvgP fa. Qed.

Lemma cvge_le f a b : (\forall x \near F, b >= f x) -> f @ F --> a -> b >= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_le//=; apply: cvgP fa. Qed.

Lemma cvg_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> f j @ F --> l j) ->
  \sum_(j <- r | P j) f j i @[i --> F] --> \sum_(j <- r | P j) l j.
Proof.
pose bigsimp := (big_nil, big_cons);
elim: r => [|x r IHr]/= f0 fl; rewrite bigsimp; under eq_fun do rewrite bigsimp.
  exact: cvg_cst.
case: ifPn => [Px|Pnx]; last exact: IHr.
apply: cvgeD; [|exact: fl|exact: IHr].
by rewrite ge0_adde_def ?inE// ?sume_ge0// => [|j Pj];
   rewrite (cvge_ge _ (fl _ _))//; apply: f0.
Qed.

Lemma lim_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> cvg (f j @ F)) ->
  lim (\sum_(j <- r | P j) f j i @[i --> F]) = \sum_(j <- r | P j) (lim (f j @ F)).
Proof. by move=> ? ?; apply/cvg_lim => //; apply: cvg_nnesum. Qed.

End ecvg_realFieldType_proper.

Section cvg_0_pinfty.
Context {R : realFieldType} {I : Type} {a : set_system I} {FF : Filter a}.
Implicit Types f : I -> R.

Lemma gtr0_cvgV0 f : (\near a, 0 < f a) -> f\^-1 @ a --> 0 <-> f @ a --> +oo.
Proof.
move=> f_gt0; split; last first.
  move=> /cvgryPgt cvg_f_oo; apply/cvgr0Pnorm_lt => _/posnumP[e].
  near=> i; rewrite gtr0_norm ?invr_gt0//=; last by near: i.
  by rewrite -ltf_pV2 ?qualifE/= ?invr_gt0 ?invrK//=; near: i.
move=> /cvgr0Pnorm_lt uB; apply/cvgryPgty.
near=> M; near=> i; suff: `|(f i)^-1| < M^-1.
  by rewrite gtr0_norm ?ltf_pV2 ?qualifE ?invr_gt0//=; near: i.
by near: i; apply: uB; rewrite ?invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVy f : (\near a, 0 < f a) -> f\^-1 @ a --> +oo <-> f @ a --> 0.
Proof.
by move=> f_gt0; rewrite -gtr0_cvgV0 ?inv_funK//; near do rewrite invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ltr0_cvgV0 f : (\near a, 0 > f a) -> f\^-1 @ a --> 0 <-> f @ a --> -oo.
Proof.
move=> fL0; rewrite -cvgNP oppr0 (_ : - f\^-1 =  (- f)\^-1); last first.
   by apply/funeqP => i; rewrite opprfctE/= invrN.
by rewrite gtr0_cvgV0 ?cvgNry//; near do rewrite oppr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVNy f : (\near a, 0 > f a) -> f\^-1 @ a --> -oo <-> f @ a --> 0.
Proof.
by move=> f_lt0; rewrite -ltr0_cvgV0 ?inv_funK//; near do rewrite invr_lt0.
Unshelve. all: by end_near. Qed.

End cvg_0_pinfty.

Section FilterRealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma squeeze_cvgr f h g : (\near a, f a <= g a <= h a) ->
  forall (l : R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh l lfa lga; apply/cvgrPdist_lt => e e_gt0.
near=> x; have /(_ _)/andP[//|fg gh] := near fgh x.
rewrite distrC ltr_distl (lt_le_trans _ fg) ?(le_lt_trans gh)//=.
  by near: x; apply: (cvgr_lt l); rewrite // ltrDl.
by near: x; apply: (cvgr_gt l); rewrite // gtrDl oppr_lt0.
Unshelve. all: end_near. Qed.

Lemma ger_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgryPge ucvg; apply/cvgryPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma ler_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgrNyPle ucvg; apply/cvgrNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

End FilterRealType.

Section TopoProperFilterRealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma ler_cvg_to f g (l l' : R) : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> fl gl; under eq_near do rewrite -subr_ge0; rewrite -subr_ge0.
by apply: cvgr_to_ge; apply: cvgB.
Qed.

Lemma ler_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: ler_cvg_to. Qed.

End TopoProperFilterRealType.

Section FilterERealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma gee_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgeyPge uecvg; apply/cvgeyPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma lee_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgeNyPle uecvg; apply/cvgeNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma squeeze_fin f g h : (\near a, f a <= g a <= h a) ->
    (\near a, f a \is a fin_num) -> (\near a, h a \is a fin_num) ->
  (\near a, g a \is a fin_num).
Proof.
apply: filterS3 => x /andP[fg gh].
rewrite !fin_numElt => /andP[oof _] /andP[_ hoo].
by rewrite (lt_le_trans oof) ?(le_lt_trans gh).
Qed.

Lemma squeeze_cvge f g h : (\near a, f a <= g a <= h a) ->
  forall (l : \bar R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh [l||]; last 2 first.
- by move=> + _; apply: gee_cvgy; apply: filterS fgh => ? /andP[].
- by move=> _; apply: lee_cvgNy; apply: filterS fgh => ? /andP[].
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fh hl]; apply/fine_cvgP.
have Fg := squeeze_fin fgh Ff Fh; split=> //.
apply: squeeze_cvgr fl hl; near=> x => /=.
by have /(_ _)/andP[//|fg gh] := near fgh x; rewrite !fine_le//=; near: x.
Unshelve. all: end_near. Qed.

End FilterERealType.

Section TopoProperFilterERealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma lee_cvg_to f g l l' : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> + + fg; move: l' l.
move=> /= [l'||] [l||]//=; rewrite ?leNye ?leey//=; first 1 last.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
- by move=> /cvg_lim <-// /(lee_cvgNy fg) /cvg_lim<-.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fg gl].
rewrite lee_fin -(cvg_lim _ fl)// -(cvg_lim _ gl)//.
by apply: ler_lim; [apply: cvgP fl|apply: cvgP gl|near do apply: fine_le].
Unshelve. all: end_near. Qed.

Lemma lee_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: lee_cvg_to. Qed.

End TopoProperFilterERealType.

Section Rhull.
Variable R : realType.

Definition Rhull (X : set R) : interval R := Interval
  (if `[< has_lbound X >] then BSide `[< X (inf X) >] (inf X)
                          else BInfty _ true)
  (if `[< has_ubound X >] then BSide (~~ `[< X (sup X) >]) (sup X)
                          else BInfty _ false).

Lemma Rhull0 : Rhull set0 = `]0, 0[ :> interval R.
Proof.
rewrite /Rhull  (asboolT (has_lbound0 R)) (asboolT (has_ubound0 R)) asboolF //.
by rewrite sup0 inf0.
Qed.

Lemma sub_Rhull (X : set R) : X `<=` [set x | x \in Rhull X].
Proof.
move=> x Xx/=; rewrite in_itv/=.
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
+ by case: asboolP => ?; case: asboolP => ? //=;
     rewrite !(lteifF,lteifT,ub_le_sup,ge_inf,sup_ub_strict,inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lteifF, lteifT);
     [rewrite ge_inf | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lteifF, lteifT);
     [rewrite ub_le_sup | rewrite sup_ub_strict].
Qed.

Lemma is_intervalP (X : set R) : is_interval X <-> X = [set x | x \in Rhull X].
Proof.
split=> [iX|->]; last exact: interval_is_interval.
rewrite predeqE => x /=; split; [exact: sub_Rhull | rewrite in_itv/=].
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
- case: asboolP => XinfX; case: asboolP => XsupX;
    rewrite !(lteifF, lteifT).
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx].
    rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx supXx].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[infXx]; rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> ?; apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
- case: asboolP => XinfX; rewrite !(lteifF, lteifT, andbT).
  + rewrite le_eqVlt => /orP[/eqP<-//|infXx].
    apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
  + move=> infXx; apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
- case: asboolP => XsupX /=.
  + rewrite le_eqVlt => /orP[/eqP->//|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
  + move=> xsupX; apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
- by move=> _; rewrite (interval_unbounded_setT iX).
Qed.

Lemma connected_intervalP (E : set R) : connected E <-> is_interval E.
Proof.
split => [cE x y Ex Ey z /andP[xz zy]|].
- apply: contrapT => Ez.
  pose Az := E `&` [set x | x < z]; pose Bz := E `&` [set x | z < x].
  apply/connectedPn : cE; exists (fun b => if b then Az else Bz); split.
  + move: xz zy Ez.
    rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy] Ez.
    by case; [exists x | exists y].
  + rewrite /Az /Bz -setIUr; apply/esym/setIidPl => u Eu.
    by apply/orP; rewrite -neq_lt; apply/negP; apply: contraPnot Eu => /eqP <-.
  + split; [|rewrite setIC].
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_gt => zu.
      by rewrite /Az setCI; right; apply/negP; rewrite -leNgt.
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_lt => zu.
      by rewrite /Bz setCI; right; apply/negP; rewrite -leNgt.
- apply: contraPP => /connectedPn[A [A0 EU sepA]] intE.
  have [/= x A0x] := A0 false; have [/= y A1y] := A0 true.
  wlog xy : A A0 EU sepA x A0x y A1y / x < y.
    move=> /= wlog_hypo; have [xy|yx|{wlog_hypo}yx] := ltgtP x y.
    + exact: (wlog_hypo _ _ _ _ _ A0x _ A1y).
    + apply: (wlog_hypo (A \o negb) _ _ _ y _ x) => //=;
      by [rewrite setUC | rewrite separatedC].
    + move/separated_disjoint : sepA; rewrite predeqE => /(_ x)[] + _; apply.
      by split => //; rewrite yx.
  pose z := sup (A false `&` [set z | x <= z <= y]).
  have A1z : ~ (A true) z.
    have cA0z : closure (A false) z.
      suff : closure (A false `&` [set z | x <= z <= y]) z by case/closureI.
      apply: closure_sup; last by exists y => u [_] /andP[].
      by exists x; split => //; rewrite /mkset lexx /= (ltW xy).
    by move: sepA; rewrite /separated => -[] /disjoints_subset + _; apply.
  have /andP[xz zy] : x <= z < y.
    rewrite ub_le_sup//=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle ge_sup ?andbT; last by move=> u [_] /andP[].
      * by apply/negP; apply: contraPnot A1y => /eqP <-.
      * by exists x; split => //; rewrite /mkset /= lexx /= (ltW xy).
    + by split=> //; rewrite /mkset lexx (ltW xy).
  have [A0z|A0z] := pselect ((A false) z); last first.
  have {}xzy : x <= z <= y by rewrite xz ltW.
    have : ~ E z by rewrite EU => -[].
    by apply; apply (intE x y) => //; rewrite EU; [left|right].
  suff [z1 [/andP[zz1 z1y] Ez1]] : exists z1 : R, z <= z1 <= y /\ ~ E z1.
    apply Ez1; apply (intE x y) => //; rewrite ?EU; [by left|by right|].
    by rewrite z1y (le_trans _ zz1).
  have [r zcA1] : {r:{posnum R}| ball z r%:num `<=` ~` closure (A true)}.
    have ? : ~ closure (A true) z.
      by move: sepA; rewrite /separated => -[] _ /disjoints_subset; apply.
    have ? : open (~` closure (A true)) by exact/closed_openC/closed_closure.
    exact/nbhsC_ball/open_nbhs_nbhs.
  pose z1 : R := z + r%:num / 2; exists z1.
  have z1y : z1 <= y.
    rewrite leNgt; apply/negP => yz1.
    suff : (~` closure (A true)) y by apply; exact: subset_closure.
    apply zcA1; rewrite /ball /= ltr_distl (lt_le_trans zy) // ?lerDl //.
    rewrite andbT ltrBlDl addrC (lt_trans yz1) // ltrD2l.
    by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
  rewrite z1y andbT lerDl; split => //.
  have ncA1z1 : (~` closure (A true)) z1.
    apply zcA1; rewrite /ball /= /z1 opprD addNKr normrN.
    by rewrite ger0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
  have nA0z1 : ~ (A false) z1.
    move=> A0z1; have : z < z1 by rewrite /z1 ltrDl.
    apply/negP; rewrite -leNgt.
     apply: ub_le_sup; first by exists y => u [_] /andP[].
    by split => //; rewrite /mkset /z1 (le_trans xz) /= ?lerDl // (ltW z1y).
  by rewrite EU => -[//|]; apply: contra_not ncA1z1; exact: subset_closure.
Qed.

Lemma set_itvK : {in neitv, cancel pred_set Rhull}.
Proof.
move=> [[[] x|[]] [[] y|[]]] /neitvP //;
  rewrite /Rhull /= !(in_itv, inE)/= ?bnd_simp => xy.
- rewrite asboolT// inf_itv// lexx/= xy asboolT// asboolT//=.
  by rewrite asboolF//= sup_itv//= ltxx ?andbF.
- by rewrite asboolT// inf_itv// ?asboolT// ?sup_itv// ?lexx ?xy.
- by rewrite asboolT//= inf_itv// lexx asboolT// asboolF.
- rewrite asboolT// inf_itv//= ltxx asboolF// asboolT//.
  by rewrite sup_itv// ltxx andbF asboolF.
  rewrite asboolT // inf_itv // ltxx asboolF // asboolT //.
  by rewrite sup_itv // xy lexx asboolT.
- by rewrite asboolT // inf_itv// ltxx asboolF // asboolF.
- by rewrite asboolF // asboolT // sup_itv// ltxx asboolF.
- by rewrite asboolF // asboolT // sup_itv// lexx asboolT.
- by rewrite asboolF // asboolF.
Qed.

Lemma RhullT : Rhull setT = `]-oo, +oo[%R :> interval R.
Proof. by rewrite /Rhull -set_itvNyy asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)), cancel Rhull pred_set}.
Proof. by move=> X /asboolP iX; exact/esym/is_intervalP. Qed.

Lemma set_itv_setT (i : interval R) : [set` i] = setT -> i = `]-oo, +oo[.
Proof.
have [i0  /(congr1 Rhull)|] := boolP (neitv i).
  by rewrite set_itvK// => ->; exact: RhullT.
by rewrite negbK => /eqP ->; rewrite predeqE => /(_ 0)[_]/(_ Logic.I).
Qed.

Lemma Rhull_smallest A : [set` Rhull A] = smallest (@is_interval R) A.
Proof.
apply/seteqP; split; last first.
  by apply: smallest_sub; [apply: interval_is_interval | apply: sub_Rhull].
move=> x /= + I [Iitv AI]; rewrite /Rhull.
have [|] := asboolP (has_lbound A) => lA; last first.
  have /forallNP/(_ x)/existsNP[a] := lA.
  move=> /existsNP[Aa /negP]; rewrite -ltNge => ax.
  have [|]:= asboolP (has_ubound A) => uA; last first.
    move=> ?; have /forallNP/(_ x)/existsNP[b] := uA.
    move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
    have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
    by rewrite ax xb.
  have [As|NAs]/= := asboolP (A _) => xA.
    by apply: (Iitv a (sup A)); by [apply: AI | rewrite ltW ?ax].
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists a | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [|]:= asboolP (has_ubound A) => uA; last first.
  have /forallNP/(_ x)/existsNP[b] := uA.
  move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
  have [Ai|NAi]/= := asboolP (A _) => xA.
    by apply: (Iitv (inf A) b); by [apply: AI | rewrite (ltW xb)].
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists b | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [Ai|NAi]/= := asboolP (A _); have [As|NAs]/= := asboolP (A _).
- by apply: Iitv; apply: AI.
- move=> xA.
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists (inf A) | rewrite (itvP xA)].
  have /(_ (inf A) b) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW xb).
- move=> xA.
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists (sup A) | rewrite (itvP xA)].
  have /(_ a (sup A)) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW ax).
have [->|/set0P AN0] := eqVneq A set0.
  by rewrite inf0 sup0 itv_ge//= ltBSide/= ltxx.
move=> xA.
have [||a Aa ax] := @inf_lt _ A x; do ?by [|rewrite (itvP xA)].
have [||b Ab xb] := @sup_gt _ A x; do ?by [|rewrite (itvP xA)].
have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
by rewrite ax xb.
Qed.

Lemma le_Rhull : {homo Rhull : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A B AB; suff: [set` Rhull A] `<=` [set` Rhull B] by [].
rewrite Rhull_smallest; apply: smallest_sub; first exact: interval_is_interval.
by rewrite Rhull_smallest; apply: sub_smallest.
Qed.

Lemma neitv_Rhull A : ~~ neitv (Rhull A) -> A = set0.
Proof.
move/negPn/eqP => A0; rewrite predeqE => r; split => // /sub_Rhull.
by rewrite A0.
Qed.

Lemma Rhull_involutive A : Rhull [set` Rhull A] = Rhull A.
Proof.
have [A0|/neitv_Rhull] := boolP (neitv (Rhull A)); first by rewrite set_itvK.
by move=> ->; rewrite ?Rhull0 set_itvE Rhull0.
Qed.

Lemma disj_itv_Rhull (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B -> disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK ?inE.
Qed.

End Rhull.

(**md properties of segments in $\bar{R}$ *)
Section segment.
Context {R : realType}.

Lemma segment_connected (a b : R) : connected `[a, b].
Proof. exact/connected_intervalP/interval_is_interval. Qed.

Lemma segment_compact (a b : R) : compact `[a, b].
Proof.
have [leab|ltba] := lerP a b; last first.
  by move=> F FF /filter_ex [x abx]; move: ltba; rewrite (itvP abx).
rewrite compact_cover => I D f fop sabUf.
set B := [set x | exists2 E : {fset I}, {subset E <= D} &
  `[a, x] `<=` \bigcup_(i in [set` E]) f i /\ (\bigcup_(i in [set` E]) f i) x].
set A := `[a, b] `&` B.
suff Aeab : A = `[a, b]%classic.
  suff [_ [E ? []]] : A b by exists E.
  by rewrite Aeab/= inE/=; exact/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite in_itv /= lexx.
  exists a; split=> //; have /sabUf [i /= Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE inE => /eqP->.
  split; last by exists i => //=; rewrite inE.
  move=> x /= aex; exists i; [by rewrite /= inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [E sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite inE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists E => //; split; last by exists i => //; apply/xe_fi.
  move=> z /= ayz; have [lezx|ltxz] := lerP z x.
    by apply/saxUf; rewrite /= in_itv/= (itvP ayz) lezx.
  exists i => //; apply/xe_fi; rewrite /ball_/= distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltrBlDl; apply: le_lt_trans lezy _; rewrite -ltrBlDr.
    by have := xe_y; rewrite /ball_ => /ltr_distlCBl.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: interval_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [E sD [sayUf _]]] xe_y]] :=
  nbhsx_ballx x e%:num ltac:(by []).
exists (i |` E)%fset; first by move=> j /fset1UP[->|/sD] //; rewrite inE.
split=> [z axz|]; last first.
  exists i; first by rewrite /= !inE eq_refl.
  by apply/xe_fi; rewrite /ball_/= subrr normr0.
have [lezy|ltyz] := lerP z y.
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite in_itv /= (itvP axz) lezy.
  by exists j => //=; rewrite inE orbC Dj.
exists i; first by rewrite /= !inE eq_refl.
apply/xe_fi; rewrite /ball_/= ger0_norm; last by rewrite subr_ge0 (itvP axz).
rewrite ltrBlDl -ltrBlDr; apply: lt_trans ltyz.
by apply: ltr_distlCBl; rewrite distrC.
Qed.

End segment.

Lemma IVT (R : realType) (f : R -> R) (a b v : R) :
  a <= b -> {within `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab fcont; gen have ivt : f v fcont / f a <= v <= f b ->
    exists2 c, c \in `[a, b] & f c = v; last first.
  case: (leP (f a) (f b)) => [] _ fabv /=; first exact: ivt.
  have [| |c cab /oppr_inj] := ivt (- f) (- v); last by exists c.
  - by move=> x /=; apply/continuousN/fcont.
  - by rewrite lerNr opprK lerNr opprK andbC.
move=> favfb; suff: is_interval (f @` `[a,b]).
  apply; last exact: favfb.
  - by exists a => //=; rewrite in_itv/= lexx.
  - by exists b => //=; rewrite in_itv/= leab lexx.
apply/connected_intervalP/connected_continuous_connected => //.
exact: segment_connected.
Qed.

Section prod_NormedModule.
Context {K : numFieldType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normrZ maxr_pMr. Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K (U * V)%type
  prod_norm_scale.

End prod_NormedModule.

Section prod_NormedModule_lemmas.
Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma fcvgr2dist_ltP {F : set_system U} {G : set_system V}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V) :
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgr2dist_ltP {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof.
rewrite fcvgr2dist_ltP; split=> + e e0 => /(_ e e0);
  by rewrite !near_simpl// => ?; rewrite !near_simpl.
Qed.

Lemma cvgr2dist_lt {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof. by rewrite cvgr2dist_ltP. Qed.

End prod_NormedModule_lemmas.
Arguments cvgr2dist_ltP {_ _ _ _ _ F G FF FG}.
Arguments cvgr2dist_lt {_ _ _ _ _ F G FF FG}.

(* Local properties in R *)

(* Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : {posnum R}, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
(*     forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) -> *)
(*   {near x & y, forall x y, P x y} ->  *)
(*   {near x & y, forall x y, Q x y}. *)
(* Proof. *)
(* move=> P Q x y /= K => /locallyP [d _ H]. *)
(* apply/locallyP; exists d => // uv Huv. *)
(* by apply (K d) => //. *)
(* Qed. *)

(* Lemma locally_2d_1d_const_x : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally y (fun t => P x t). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* exists d => // z Hz. *)
(* by apply (Hd (x, z)). *)
(* Qed. *)

(* Lemma locally_2d_1d_const_y : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally x (fun t => P t y). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* apply/locallyP; exists d => // z Hz. *)
(* by apply (Hd (z, y)). *)
(* Qed. *)

(* Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R): *)
(*   (\near x & y, P x y) -> *)
(*   \forall u \near x & v \near y, *)
(*       forall (t : R), 0 <= t <= 1 -> *)
(*       \forall z \near t, \forall a \near (x + z * (u - x)) *)
(*                                & b \near (y + z * (v - y)), P a b. *)
(* Proof. *)
(* move=> P x y. *)
(* apply locally_2d_align => eps HP uv Huv t Ht. *)
(* set u := uv.1. set v := uv.2. *)
(* have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0. *)
(* rewrite ler_eqVlt in Zm. *)
(* case/orP : Zm => Zm. *)
(* - apply filterE => z. *)
(*   apply/locallyP. *)
(*   exists eps => // pq. *)
(*   rewrite !(RminusE,RmultE,RplusE). *)
(*   move: (Zm). *)
(*   have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm). *)
(*   rewrite ler_maxl => /andP[H1 H2] _. *)
(*   rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite !(mulr0,addr0); by apply HP. *)
(* - have : Num.max (`|u - x|) (`|v - y|) < eps. *)
(*     rewrite ltr_maxl; apply/andP; split. *)
(*     - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*     - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*   rewrite -subr_gt0 => /RltP H1. *)
(*   set d1 := mk{posnum R} _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mk{posnum R} _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [{posnum R} of d1 / 2] => //= pq Hpq. *)
(*   set p := pq.1. set q := pq.2. *)
(*   apply HP; split. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //. *)
(*     apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)). *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //. *)
(*     rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //. *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr orbT. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(* Qed. *)
(* Admitted. *)

(* TODO redo *)
(* Lemma locally_2d_1d (P : R -> R -> Prop) x y : *)
(*   locally_2d x y P -> *)
(*   locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P). *)
(* Proof. *)
(* move/locally_2d_1d_strong. *)
(* apply: locally_2d_impl. *)
(* apply locally_2d_forall => u v H t Ht. *)
(* specialize (H t Ht). *)
(* have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by []. *)
(* by apply: locally_singleton. *)
(* Qed. *)

(* TODO redo *)
(* Lemma locally_2d_ex_dec : *)
(*   forall P x y, *)
(*   (forall x y, P x y \/ ~P x y) -> *)
(*   locally_2d x y P -> *)
(*   {d : {posnum R} | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" :=
  (dominated_by (self_sub id) k (self_sub f)) : type_scope.

Lemma sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
    (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set_system (V * V)) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Lemma sub_lipschitz (K : numFieldType) (V W : normedModType K)
    (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Proof. by move=> FG; rewrite /lipschitz_on; apply: filterS => M; apply: FG. Qed.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set_system (V * V)) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Proof. by move=> f_lip; apply/ex_dom_bound; exists k. Qed.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A))) : type_scope.
Notation "k .-lipschitz f" := (k.-lipschitz_setT f) : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A))) : type_scope.
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma lipschitz_set0 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) : [lipschitz f x | x in set0].
Proof. by apply: nearW; rewrite setX0 => ?; apply: globally0. Qed.

Lemma lipschitz_set1 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) (a : V) : [lipschitz f x | x in [set a]].
Proof.
apply: (@klipschitzW _ _ _ `|f a|).
  exact: (@globally_properfilter _ _ (a, a)).
by move=> [x y] /= [] -> ->; rewrite !subrr !normr0 mulr0.
Qed.

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R) (k : R)
    (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Proof. by move=> + x Ax; apply: sub_klipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Proof. by move=> + x Ax; apply: sub_lipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) :
  1.-lipschitz (@id V).
Proof. by move=> [/= x y] _; rewrite mul1r. Qed.
Arguments lipschitz_id {R V}.

Section LinearContinuousBounded.
Variables (R : numFieldType) (V W : normedModType R).

Lemma linear_boundedP (f : {linear V -> W}) : bounded_near f (nbhs 0) <->
  \forall r \near +oo, forall x, `|f x| <= r * `|x|.
Proof.
split=> [|/pinfty_ex_gt0 [r r0 Bf]]; last first.
  apply/ex_bound; exists r; apply/nbhs_norm0P; exists 1 => //= x /=.
  by rewrite -(gtr_pMr _ r0) => /ltW; exact/le_trans/Bf.
rewrite /bounded_near => /pinfty_ex_gt0 [M M0 /nbhs_norm0P [_/posnumP[e] efM]].
near (0 : R)^'+ => d; near=> r => x.
have[->|x0] := eqVneq x 0; first by rewrite raddf0 !normr0 mulr0.
have nd0 : d / `|x| > 0 by rewrite divr_gt0 ?normr_gt0.
have: `|f (d / `|x| *: x)| <= M.
  by apply: efM => /=; rewrite normrZ gtr0_norm// divfK ?normr_eq0//.
rewrite linearZ/= normrZ gtr0_norm// -ler_pdivlMl//; move/le_trans; apply.
rewrite invfM invrK mulrAC ler_wpM2r//; near: r; apply: nbhs_pinfty_ge.
by rewrite rpredM// ?rpredV ?gtr0_real.
Unshelve. all: by end_near. Qed.

Lemma continuous_linear_bounded (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for/continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
near do rewrite /= linearD (le_trans (ler_normD _ _))// -lerBrDl.
by apply: cvgr0_norm_le; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma bounded_linear_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) -> continuous f.
Proof.
move=> /linear_boundedP [y [yreal fr]] x; near +oo_R => r.
apply/(@cvgrPdist_lt _ _ _ (nbhs x)) => e e_gt0; near=> z; rewrite -linearB.
rewrite (le_lt_trans (fr r _ _))// -?ltr_pdivlMl//.
by near: z; apply: cvgr_dist_lt => //; rewrite mulrC divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma continuousfor0_continuous (f : {linear V -> W}) :
  {for 0, continuous f} -> continuous f.
Proof. by move=> /continuous_linear_bounded/bounded_linear_continuous. Qed.

Lemma linear_bounded_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs 0) <-> continuous f.
Proof.
split; first exact: bounded_linear_continuous.
by move=> /(_ 0); exact: continuous_linear_bounded.
Qed.

Lemma bounded_funP (f : {linear V -> W}) :
  (forall r, exists M, forall x, `|x| <= r -> `|f x| <= M) <->
  bounded_near f (nbhs (0 : V)).
Proof.
split => [/(_ 1) [M Bf]|/linear_boundedP fr y].
  apply/ex_bound; exists M; apply/nbhs_normP => /=; exists 1 => //= x /=.
  by rewrite sub0r normrN => x1; exact/Bf/ltW.
near +oo_R => r; exists (r * y) => x xe.
rewrite (@le_trans _ _ (r * `|x|)) //; first by move: {xe} x; near: r.
by rewrite ler_pM.
Unshelve. all: by end_near. Qed.

End LinearContinuousBounded.

Section contractions.
Context {R : numDomainType} {X Y : normedModType R} {U : set X} {V : set Y}.

Definition contraction (q : {nonneg R}) (f : {fun U >-> V}) :=
  q%:num < 1 /\ q%:num.-lipschitz_U f.

Definition is_contraction (f : {fun U >-> V}) := exists q, contraction q f.

End contractions.

Lemma contraction_fixpoint_unique {R : realDomainType}
    {X : normedModType R} (U : set X) (f : {fun U >-> U}) (x y : X) :
  is_contraction f -> U x -> U y -> x = f x -> y = f y -> x = y.
Proof.
case => q [q1 ctrfq] Ux Uy fixx fixy; apply/subr0_eq/normr0_eq0/eqP.
have [->|xyneq] := eqVneq x y; first by rewrite subrr normr0.
have xypos : 0 < `|x - y| by rewrite normr_gt0 subr_eq0.
suff : `|x - y| <= q%:num * `|x - y| by rewrite ler_pMl // leNgt q1.
by rewrite [in leLHS]fixx [in leLHS]fixy; exact: (ctrfq (_, _)).
Qed.

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvgn a -> bounded_fun a.
Proof.
move=> /cvg_bounded/ex_bound => -[/= Moo] => -[N _ /(_ _) aM].
have Moo_real : Moo \is Num.real by rewrite ger0_real ?(le_trans _ (aM N _))/=.
rewrite /bounded_near /=; near=> M => n _.
have [nN|nN]/= := leqP N n; first by apply: (le_trans (aM _ _)).
move: n nN; suff /(_ (Ordinal _)) : forall n : 'I_N, `|a n| <= M by [].
by near: M; apply: filter_forall => i; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

End cvg_seq_bounded.

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded_set A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  by move=> p _; exists (floor `|p| + 1) => //=; rewrite floorD1_gt.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite /= -subr_gt0 => ltpn.
  apply/nbhs_ballP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltrBrDr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_normD.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmax_real//; split=> // x ltmaxx p /DcovA [n Dn /lt_trans /(_ _)/ltW].
apply; apply: le_lt_trans ltmaxx.
have : n \in enum_fset D by [].
by rewrite enum_fsetE => /mapP[/= i iD ->]; exact/le_bigmax.
Qed.

Section Closed_Ball_normedModType.

Lemma closed_closed_ball_ (R : realFieldType) (V : normedModType R)
  (x : V) (e : R) : closed (closed_ball_ normr x e).
Proof.
rewrite /closed_ball_ -/((normr \o (fun y => x - y)) @^-1` [set x | x <= e]).
apply: (closed_comp _ (@closed_le _ _)) => y _.
apply: (continuous_comp _ (@norm_continuous _ _ _)).
exact: (continuousB (@cst_continuous _ _ _ _)).
Qed.

Lemma closed_ballE (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed_ball x r = closed_ball_ normr x r.
Proof.
move=> /posnumP[e]; rewrite eqEsubset; split => y.
  rewrite /closed_ball closureE; apply; split; first exact: closed_closed_ball_.
  by move=> z; rewrite -ball_normE; exact: ltW.
have [-> _|xy] := eqVneq x y; first exact: closed_ballxx.
rewrite /closed_ball closureE -ball_normE.
rewrite /closed_ball_ /= le_eqVlt.
move => /orP[/eqP xye B [Bc Be]|xye _ [_ /(_ _ xye)]//].
apply: Bc => B0 /nbhs_ballP[s s0] B0y.
have [es|se] := leP s e%:num; last first.
  exists x; split; first by apply: Be; rewrite ball_normE; apply: ballxx.
  by apply: B0y; rewrite -ball_normE /ball_ /= distrC xye.
exists (y + (s / 2) *: (`|x - y|^-1 *: (x - y))); split; [apply: Be|apply: B0y].
  rewrite /= opprD addrA -[X in `|X - _|](scale1r (x - y)) scalerA -scalerBl.
  rewrite -[X in X - _](@divff _ `|x - y|) ?normr_eq0 ?subr_eq0//.
  rewrite -mulrBl -scalerA normrZ normfZV ?subr_eq0// mulr1.
  rewrite gtr0_norm; first by rewrite ltrBlDl xye ltrDr mulr_gt0.
  by rewrite subr_gt0 xye ltr_pdivrMr // mulr_natr mulr2n ltr_pwDl.
rewrite -ball_normE /ball_ /= opprD addNKr normrN normrZ normfZV ?subr_eq0//.
by rewrite mulr1 normf_div !gtr0_norm// ltr_pdivrMr// ltr_pMr //ltr1n.
Qed.

Lemma closed_ball_itv (R : realFieldType) (x r : R) : 0 < r ->
  closed_ball x r = `[x - r, x + r]%classic.
Proof.
by move=> r0; apply/seteqP; split => y;
  rewrite closed_ballE// /closed_ball_ /= in_itv/= ler_distlC.
Qed.

Lemma closed_ball_ball {R : realFieldType} (x r : R) : 0 < r ->
  closed_ball x r = [set x - r] `|` ball x r `|` [set x + r].
Proof.
move=> r0; rewrite closed_ball_itv// -(@setU1itv _ _ _ (x - r)); last first.
  by rewrite bnd_simp lerBlDr -addrA lerDl ltW// addr_gt0.
rewrite -(@setUitv1 _ _ _ (x + r)); last first.
  by rewrite bnd_simp ltrBlDr -addrA ltrDl addr_gt0.
by rewrite ball_itv setUA.
Qed.

Lemma closed_ballR_compact (R : realType) (x e : R) : 0 < e ->
  compact (closed_ball x e).
Proof.
move=> e_gt0; have : compact `[x - e, x + e] by apply: segment_compact.
by rewrite closed_ballE//; under eq_set do rewrite in_itv -ler_distlC.
Qed.

Lemma closed_ball_subset (R : realFieldType) (M : normedModType R) (x : M)
  (r0 r1 : R) : 0 < r0 -> r0 < r1 -> closed_ball x r0 `<=` ball x r1.
Proof.
move=> r00 r01; rewrite (_ : r0 = (PosNum r00)%:num) // closed_ballE //.
by move=> m xm; rewrite -ball_normE /ball_ /= (le_lt_trans _ r01).
Qed.

Lemma nbhs_closedballP (R : realFieldType) (M : normedModType R) (B : set M)
  (x : M) : nbhs x B <-> exists r : {posnum R}, closed_ball x r%:num `<=` B.
Proof.
split=> [/nbhs_ballP[_/posnumP[r] xrB]|[e xeB]]; last first.
  apply/nbhs_ballP; exists e%:num => //=.
  exact: (subset_trans (@subset_closure _ _) xeB).
exists (r%:num / 2)%:itv.
apply: (subset_trans (closed_ball_subset _ _) xrB) => //=.
by rewrite lter_pdivrMr // ltr_pMr // ltr1n.
Qed.

End Closed_Ball_normedModType.

Lemma open_subball {R : numFieldType} {M : normedModType R} (A : set M)
  (x : M) : open A -> A x -> \forall e \near 0^'+, ball x e `<=` A.
Proof.
move=> oA Ax; have /nbhsr0P/= : nbhs x A by exact/open_nbhs_nbhs.
apply: filterS => e xeA y exy; apply: xeA.
by rewrite -ball_normE/= in exy; exact: ltW.
Qed.

Lemma open_subball_rat {R : realType} (S : set R) x : open S -> x \in S ->
  exists c r, let B : set R := ball (@ratr R c) (ratr r) in x \in B /\ B `<=` S.
Proof.
move=> oS /set_mem/(open_subball oS)[r/= r0 rS].
have [y yxr] : exists y, ball x (r / 4) (ratr y).
  suff : ball x (r / 4) `&` range ratr !=set0.
    by move=> [/= _ []] /[swap] -[y _ <-]; exists y.
  apply: dense_rat; last by apply: ball_open; rewrite divr_gt0.
  by exists x; apply: ballxx; rewrite divr_gt0.
have [q /andP[rq qr]] : exists q, r / 4 < ratr q < r / 2.
  have : ball (r / 3) (r / 12) `&` range ratr !=set0.
    apply: dense_rat; last by apply: ball_open; rewrite divr_gt0.
    by exists (r / 3); apply: ballxx; rewrite divr_gt0.
  move=> [/= _ []] /[swap] -[z _ <-].
  rewrite ball_itv/= in_itv/= => /andP[rz zr]; exists z; apply/andP; split.
  - rewrite (le_lt_trans _ rz)// -mulrBr ler_pM2l// -(@ler_pM2l _ 12)//.
    rewrite mulrBr divff// (@natrM _ 3 4) -mulrA divff// mulr1.
    by rewrite mulrAC divff// mul1r -lerBlDr opprK natr1.
  - rewrite (lt_le_trans zr)// -mulrDr ler_pM2l// -(@ler_pM2l _ 12)//.
    rewrite mulrDr divff// (@natrM _ 3 4) mulrAC divff// mul1r.
    by rewrite natr1 (@natrM _ 2 2) -!mulrA divff// mulr1 -natrM ler_nat.
have [yqxr xrS] : ball (@ratr R y) (ratr q) `<=` ball x r /\ ball x r `<=` S.
  split => [z yqz|z /rat_in_itvoo[p]].
  - rewrite /ball/= -(subrK (ratr y) x) -(addrA _ (ratr y)).
    rewrite (le_lt_trans (ler_normD _ _))// (splitr r) ltrD//.
      by apply: le_ball yxr; rewrite ler_pM2l// lef_pV2 ?posrE// ler_nat.
    by rewrite (lt_trans yqz).
  - rewrite in_itv/= => /andP[xzp pr]; apply: (rS (ratr p)) => //=.
    + by rewrite sub0r normrN gtr0_norm// (le_lt_trans _ xzp).
    + exact: le_lt_trans xzp.
exists y, q; split; last exact: subset_trans xrS.
exact/mem_set/ball_sym/(le_ball _ yxr)/ltW.
Qed.

Section countable_isolated.
Context {R : realType}.
Variable S : set R.

Fact isolated_rat_ball (x : R) : isolated S x -> exists cr,
  let B : set R := ball (@ratr R cr.1) (ratr cr.2) in
  x \in B /\ (forall y : R, isolated S y -> y \in B -> x = y).
Proof.
move=> Sx.
have [e Sxe] : exists e : {posnum R},
    forall y : R, isolated S y -> y \in (ball x e%:num : set R) -> x = y.
  case: Sx => [xS/= [V xV /seteqP[VSx _]]].
  have [e /= e0 exV] : \forall e \near 0^'+, ball x e `<=` V°.
    apply: open_subball; first exact: open_interior.
    by move/nbhs_interior : xV; exact: nbhs_singleton.
  have e20 : 0 < e / 2 by rewrite divr_gt0.
  exists (PosNum e20) => y [Sy [/= U yU USy /set_mem xey]].
  apply/eqP/negPn/negP => xy.
  suff : (V `&` S) y by move/VSx/esym; exact/eqP.
  split => //; last exact/set_mem.
  apply: interior_subset; apply: exV xey => //.
  by rewrite /ball_/= sub0r normrN gtr0_norm// gtr_pMr// invf_lt1// ltr1n.
have [c [r [xcr crxe]]] : exists c r,
  let B : set R := ball (@ratr R c) (ratr r) in x \in B /\ B `<=` ball x e%:num.
  by apply: open_subball_rat; [exact: ball_open|exact/mem_set/ballxx].
by exists (c, r); split=> //= y /Sxe /[!inE] /[swap] /crxe /[swap] /[apply].
Qed.

Lemma countable_isolated : countable (isolated S).
Proof.
apply/pcard_injP => /=.
pose g r := if pselect (isolated S r) is left H then
  sval (cid (isolated_rat_ball H)) else 0.
have /card_bijP[h /bij_inj injh] := card_rat2.
exists (set_val \o h \o to_setT \o g) => x y /set_mem xS /set_mem yS /=.
rewrite /= /g; case: pselect => // xS'; case: pselect => // yS'.
case: cid => //= [ar [xar Nxar]]{xS'}; case: cid => //= [bd [ybd Nybd]]{yS'} ab.
have /injh/(congr1 (fun x => \val x)) : h (to_setT ar) = h (to_setT bd).
  move: (h (to_setT ar)) (h (to_setT bd)) ab => [n nT] [m mT].
  by rewrite !set_valE/= => ->; congr exist.
by rewrite -inv_to_setT !funK ?inE// => {}ab; apply: Nxar => //; rewrite ab.
Qed.

End countable_isolated.

Lemma closed_disjoint_closed_ball {R : realFieldType} {M : normedModType R}
    (K : set M) z : closed K -> ~ K z ->
  \forall d \near 0^'+, closed_ball z d `&` K = set0.
Proof.
rewrite -openC => /open_subball /[apply]; move=> [e /= e0].
move=> /(_ (e / 2)) /= ; rewrite sub0r normrN gtr0_norm ?divr_gt0//.
rewrite ltr_pdivrMr// ltr_pMr// ltr1n => /(_ erefl isT).
move/subsets_disjoint; rewrite setCK => ze2K0.
exists (e / 2); first by rewrite /= divr_gt0.
move=> x /= + x0; rewrite sub0r normrN gtr0_norm// => xe.
by move: ze2K0; apply: subsetI_eq0 => //=; exact: closed_ball_subset.
Qed.

Lemma interior_closed_ballE (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> (closed_ball x r)° = ball x r.
Proof.
move=> r0; rewrite eqEsubset; split; last first.
  by rewrite -open_subsetE; [exact: subset_closure | exact: ball_open].
move=> /= t; rewrite closed_ballE // /interior /= -nbhs_ballE => [[]] s s0.
have [-> _|nxt] := eqVneq t x; first exact: ballxx.
near ((0 : R^o)^') => e; rewrite -ball_normE /closed_ball_ => tsxr.
pose z := t + `|e| *: (t - x); have /tsxr /= : `|t - z| < s.
  rewrite opprD addNKr normrN normrZ normr_id.
  rewrite -ltr_pdivlMr ?(normr_gt0,subr_eq0) //.
  by near: e; apply/dnbhs0_lt; rewrite divr_gt0 // normr_gt0 subr_eq0.
rewrite /z opprD addrA -scalerN -{1}(scale1r (x - t)) opprB -scalerDl normrZ.
apply lt_le_trans; rewrite ltr_pMl; last by rewrite normr_gt0 subr_eq0 eq_sym.
by rewrite ger0_norm // ltrDl normr_gt0; near: e; exists 1 => /=.
Unshelve. all: by end_near. Qed.

Lemma open_nbhs_closed_ball (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> open_nbhs x (closed_ball x r)°.
Proof.
move=> r0; split; first exact: open_interior.
by rewrite interior_closed_ballE //; exact: ballxx.
Qed.

Lemma locally_compactR (R : realType) : locally_compact [set: R].
Proof.
move=> x _; rewrite withinET; exists (closed_ball x 1).
  by apply/nbhs_closedballP; exists 1%:pos.
by split; [apply: closed_ballR_compact | apply: closed_ball_closed].
Qed.

Section bigcup_ointsub_lemmas.
Context {R : realType} {U : set R}.

Lemma bigcup_ointsubxx q : open U -> U (ratr q) ->
  ratr q \in bigcup_ointsub U q.
Proof.
move=> oU Uq.
have [e /= e0 eU] := open_subball oU Uq.
pose B := ball (@ratr R q) (e / 2).
have Bq : B (ratr q) by apply: ballxx; rewrite divr_gt0.
apply/mem_set; exists B => //; split => //; split.
- by apply: ball_open; rewrite divr_gt0.
- by rewrite /B ball_itv; exact: interval_is_interval.
- apply: eU => //; last by rewrite divr_gt0.
  rewrite ball_normE/= /ball/= sub0r normrN gtr0_norm ?divr_gt0//.
  by rewrite gtr_pMr// invf_lt1// ltr1n.
Qed.

Lemma nondisjoint_bigcup_ointsub (p q : rat) :
  bigcup_ointsub U p `&` bigcup_ointsub U q !=set0 ->
  bigcup_ointsub U p = bigcup_ointsub U q.
Proof.
move=> [x /= [[A [[oA itvA AU Ap Ax]]] [B [[oB itvB BU Bq Bx]]]]].
rewrite eqEsubset; split.
- apply: bigcup_ointsub_sup.
  + exact: open_bigcup_ointsub.
  + exact: is_interval_bigcup_ointsub.
  + exact: bigcup_ointsub_sub.
  + exists (A `|` B) => /= ; last by right.
    split; last by left.
    split; [exact: openU| |by rewrite subUset].
    apply/connected_intervalP/connectedU; [|exact/connected_intervalP..].
    by exists x.
- apply: bigcup_ointsub_sup.
  + exact: open_bigcup_ointsub.
  + exact: is_interval_bigcup_ointsub.
  + exact: bigcup_ointsub_sub.
  + exists (A `|` B) => /= ; last by left.
    split; last by right.
    split; [exact: openU| |by rewrite subUset].
    apply/connected_intervalP/connectedU; [|exact/connected_intervalP..].
    by exists x.
Qed.

End bigcup_ointsub_lemmas.

(**md proof that an open set of real numbers can be written as
   the union of disjoint open intervals *)
Module OpenSetDisjointItvs.
Section opensetdisjointitvs.
Context {R : realType}.
Variable U : set R.
Hypothesis oU : open U.

(**md We first work out a proof where disjoint open intervals are indexed by
   rational numbers. The "sequence" of open intervals in question is
   `lt_disjoint_rat_seq`. This is the "sequence" of `bigcup_ointsub U` that
   are non-overlapping. *)
Section rat_index.
Variables (f : rat -> nat) (g : nat -> rat).
Hypotheses (cfg : cancel f g) (cgf : cancel g f).

Definition lt_disjoint := [set q | forall p, U (ratr p) ->
  (f p < f q)%N -> bigcup_ointsub U q `&` bigcup_ointsub U p = set0].

Let bigcup_lt_disjoint :
  U = \bigcup_(q in lt_disjoint) bigcup_ointsub U q.
Proof.
rewrite [LHS]open_bigcup_rat//; apply/seteqP; split => /=; last first.
  by move=> r [q/= ?] Uqr; exists q => //=; exact: bigcup_ointsub_mem Uqr.
move=> r [q/= Uq] Uqr.
suff [p_idx [pUq Up]] : exists p_idx,
    let p := g p_idx in ratr p \in bigcup_ointsub U q /\
    forall q', ratr q' \in bigcup_ointsub U q -> (f p <= f q')%N.
  have q_p : bigcup_ointsub U q `&` bigcup_ointsub U (g p_idx) !=set0.
    exists (ratr (g p_idx)); split; first exact/set_mem.
    apply/set_mem; rewrite bigcup_ointsubxx//.
    by move/set_mem : pUq; exact: bigcup_ointsub_sub.
  exists (g p_idx).
  - rewrite /= => q' Uq' q'p.
    apply/notP => /eqP/set0P[s [ps ts]].
    suff : ratr q' \in bigcup_ointsub U q by move/Up; rewrite leqNgt q'p.
    rewrite (@nondisjoint_bigcup_ointsub _ _ _ (g p_idx))//.
    rewrite (@nondisjoint_bigcup_ointsub _ _ _ q') ?bigcup_ointsubxx//.
    by exists s.
  - by rewrite (@nondisjoint_bigcup_ointsub _ _ _ q)// setIC.
pose P := [pred i : 'I_(f q).+1 | ratr (g i) \in bigcup_ointsub U q].
have Pord_max : P ord_max.
  by rewrite /P/= cfg// bigcup_ointsubxx//; exact/set_mem.
pose min : 'I_(f q).+1 := [arg min_(i < ord_max | P i) idfun i].
exists min => /=; split.
- by rewrite /min; case: arg_minnP.
- move=> q' pUp; rewrite /min; case: arg_minnP => //= i giq ismall.
  rewrite cgf.
  have [fq'fq|fqfq'] := ltnP (f q') (f q).+1.
    have := ismall (Ordinal fq'fq).
    by rewrite cfg => /(_ pUp).
  by rewrite (leq_trans _ (ltnW fqfq'))// (ismall ord_max).
Qed.

Let lt_disjoint_rat_seq0 q : set R :=
  if pselect (lt_disjoint q) then bigcup_ointsub U q else set0.

Let lt_disjoint_rat_seq0_trivIset : trivIset (U \o ratr) lt_disjoint_rat_seq0.
Proof.
apply/trivIsetP => /= i j Ui Uj.
wlog : i j Ui Uj / i < j.
  move=> wlg; rewrite neq_lt => /orP[|] ij.
    by rewrite wlg// lt_eqF.
  by rewrite setIC wlg// lt_eqF.
move=> ij _.
rewrite /lt_disjoint_rat_seq0/=.
case: pselect => disj_i; case: pselect => disj_j; rewrite ?(setI0,set0I)//.
have [?|fjfi] := ltnP (f i) (f j); first by rewrite setIC disj_j.
rewrite disj_i// ltn_neqAle fjfi andbT.
have : i != j by rewrite lt_eqF.
apply: contra => /eqP.
by move/can_inj : cfg => /[apply] => /esym/eqP.
Qed.

Let lt_disjoint_rat_seq0_comp_trivIset :
  trivIset (U \o ratr \o g) (lt_disjoint_rat_seq0 \o g).
Proof.
apply/trivIsetP => i j/= Ugi Ugj ij.
move/trivIsetP : lt_disjoint_rat_seq0_trivIset => /(_ (g i) (g j)) /=.
by apply => //; apply: contra ij; move/eqP/(can_inj cgf)/eqP.
Qed.

Let lt_disjoint_rat_seq0_set0 q :
  ratr q \notin U -> lt_disjoint_rat_seq0 q = set0.
Proof.
move=> qU.
rewrite /lt_disjoint_rat_seq0; case: pselect => //= disj_q.
rewrite /bigcup_ointsub bigcup0// => B/=[[]oB iB].
by move=> /[apply] /mem_set; rewrite (negPf qU).
Qed.

Let lt_disjoint_rat_seq0_open_itv q :
  open (lt_disjoint_rat_seq0 q) /\ is_interval (lt_disjoint_rat_seq0 q).
Proof.
split.
- rewrite /lt_disjoint_rat_seq0; case: pselect => //= _.
  + exact: open_bigcup_ointsub.
  + exact: open0.
- rewrite /lt_disjoint_rat_seq0; case: pselect => //= _.
  + exact: is_interval_bigcup_ointsub.
  + by [].
Qed.

Let bigcup_lt_disjoint_rat_seq0 : U = \bigcup_q lt_disjoint_rat_seq0 q.
Proof.
rewrite bigcup_lt_disjoint bigcup_mkcond; apply: eq_bigcup => // q _.
rewrite /lt_disjoint_rat_seq0; case: pselect => //= Icondq.
- by rewrite mem_set.
- by rewrite memNset.
Qed.

Let bigcup_U_lt_disjoint_rat_seq :
  U = \bigcup_(q in [set n | U (ratr n)]) lt_disjoint_rat_seq0 q.
Proof.
rewrite [LHS]bigcup_lt_disjoint_rat_seq0 [RHS]bigcup_mkcond.
apply: eq_bigcupr => q _; case: ifPn => //.
rewrite notin_setE/= => Uq.
by rewrite lt_disjoint_rat_seq0_set0// memNset.
Qed.

Definition lt_disjoint_rat_seq q : set R :=
  if ratr q \in U then lt_disjoint_rat_seq0 q else set0.

Lemma lt_disjoint_rat_seq_open_itv q :
  open (lt_disjoint_rat_seq q) /\ is_interval (lt_disjoint_rat_seq q).
Proof. by rewrite /lt_disjoint_rat_seq; case: ifPn => qU//; split. Qed.

Lemma lt_disjoint_rat_seq_trivIset : trivIset setT (lt_disjoint_rat_seq \o g).
Proof.
move/trivIset_mkcond: lt_disjoint_rat_seq0_trivIset => // /trivIsetP H.
apply/trivIsetP => i j/= _ _ ij.
rewrite /lt_disjoint_rat_seq; case: ifPn => //; rewrite ?(setI0,set0I)//.
rewrite /lt_disjoint_rat_seq0; case: pselect => /=; rewrite ?(setI0,set0I)//.
case: ifPn => //; rewrite ?(setI0,set0I)//.
case: pselect => /=; rewrite ?(setI0,set0I)//.
move=> disj_gj gjU K3 K4.
have := H (g i) (g j) Logic.I Logic.I.
rewrite !ifT//.
rewrite /lt_disjoint_rat_seq0/=; case: pselect => //=; case: pselect => //= _ _.
apply.
by apply: contra ij => /eqP/(can_inj cgf)/eqP.
Qed.

Lemma bigcup_lt_disjoint_rat_seq : U = \bigcup_q lt_disjoint_rat_seq q.
Proof.
rewrite [LHS]bigcup_U_lt_disjoint_rat_seq.
rewrite [in LHS]bigcup_mkcond [in RHS]bigcup_mkcond.
apply: eq_bigcupr => q _.
by rewrite [in RHS]mem_set.
Qed.

End rat_index.

(**md now the proof where disjoint open intervals are indexed by
   natural numbers *)
Lemma open_disjoint_itv : exists I : nat -> set R,
  [/\ forall q, open (I q) /\ is_interval (I q),
      trivIset setT I & U = \bigcup_q I q].
Proof.
have /card_set_bijP[/= f] := card_rat.
rewrite setTT_bijective => -[g cfg cgf].
exists (lt_disjoint_rat_seq f \o g); split.
- by move=> n; exact: lt_disjoint_rat_seq_open_itv.
- exact: lt_disjoint_rat_seq_trivIset.
- rewrite (bigcup_lt_disjoint_rat_seq cfg cgf) [LHS](reindex_bigcup g setT)//.
  by move=> q/= _; exists (f q).
Qed.

End opensetdisjointitvs.
End OpenSetDisjointItvs.

(* proof that an open set of real numbers can be written as
   the union of disjoint open intervals *)
Section open_set_disjoint_real_intervals.
Context {R : realType}.
Variable U : set R.
Hypothesis oU : open U.

(* the sequence of non-overlapping open intervals that cover U *)
Definition open_disjoint_itv : nat -> set R :=
  sval (cid (OpenSetDisjointItvs.open_disjoint_itv oU)).

Lemma open_disjoint_itv_open i : open (open_disjoint_itv i).
Proof. by rewrite /open_disjoint_itv; case: cid => //= I [/(_ i)[]]. Qed.

Lemma open_disjoint_itv_is_interval i : is_interval (open_disjoint_itv i).
Proof. by rewrite /open_disjoint_itv; case: cid => //= I [/(_ i)[]]. Qed.

Lemma open_disjoint_itv_trivIset : trivIset [set: nat] open_disjoint_itv.
Proof. by rewrite /open_disjoint_itv; case: cid => //= I [_]. Qed.

Lemma open_disjoint_itv_bigcup : U = \bigcup_q open_disjoint_itv q.
Proof. by rewrite /open_disjoint_itv; case: cid => //= I [_]. Qed.

End open_set_disjoint_real_intervals.
