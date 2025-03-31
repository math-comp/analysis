(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals topology.
From mathcomp Require Import function_spaces real_interval.
From mathcomp Require Import prodnormedzmodule tvs num_normedtype.
From mathcomp Require Import pseudometric_normed_Zmodule.

(**md**************************************************************************)
(* # Normed modules                                                           *)
(*                                                                            *)
(* We define normed modules. We prove the intermediate value theorem and      *)
(* the Heine-Borel theorem, which states that the compact sets of             *)
(* $\mathbb{R}^n$ are the closed and bounded sets.                            *)
(*                                                                            *)
(* We endow `numFieldType` with the types of norm-related notions (accessible *)
(* with `Import numFieldNormedType.Exports`).                                 *)
(*                                                                            *)
(* ## Normed modules                                                          *)
(* ```                                                                        *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K       *)
(*                                   The HB class is NormedModule.            *)
(*                           `|x| == the norm of x (notation from ssrnum)     *)
(*                      ball_norm == balls defined by the norm                *)
(*                      nbhs_norm == neighborhoods defined by the norm        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Filters                                                                 *)
(* ```                                                                        *)
(*                     x^'-, x^'+ == filters on real numbers for predicates   *)
(*                                   s.t. nbhs holds on the left/right of x   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Domination notations                                                    *)
(* ```                                                                        *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*                  bounded_near f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets                   *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of functions bounded on their     *)
(*                                      whole domain                          *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                   contraction q f == f is q.-lipschitz and q < 1           *)
(*                  is_contraction f == exists q, f is q.-lipschitz and q < 1 *)
(*                                                                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*                           Rhull A == the real interval hull of a set A     *)
(*                         shift x y == y + x                                 *)
(*                          center c := shift (- c)                           *)
(*                    closed_ball == closure of a ball                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x ^'+" (at level 3, left associativity, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, left associativity, format "x ^'-").
Reserved Notation "[ 'bounded' E | x 'in' A ]"
  (at level 0, x name, format "[ 'bounded'  E  |  x  'in'  A ]").
Reserved Notation "k .-lipschitz_on f"
  (at level 2, format "k .-lipschitz_on  f").
Reserved Notation "k .-lipschitz_ A f"
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Reserved Notation "k .-lipschitz f" (at level 2, format "k .-lipschitz  f").
Reserved Notation "[ 'lipschitz' E | x 'in' A ]"
  (at level 0, x name, format "[ 'lipschitz'  E  |  x  'in'  A ]").
Reserved Notation "k *` A" (at level 40, left associativity, format "k  *`  A").

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
   depend on near lemmas on pseudometricnormedzmodtype ?*)
Lemma add_continuous : continuous (fun x : V * V => x.1 + x.2).
Proof.
move=> [/= x y]; apply/cvg_ballP => e e0 /=.
exists (ball x (e / 2), ball y (e / 2)) => /=.
  by split; apply: nbhsx_ballx; rewrite divr_gt0.
rewrite -ball_normE /ball_/= => xy /= [nx ny].
by rewrite opprD addrACA (le_lt_trans (ler_normD _ _)) // (splitr e) ltrD.
Qed.

Lemma scale_continuous : continuous (fun z : K^o * V => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvg_ballP => e e0 /=.
near +oo_K => M.
pose r := `|e| / 2 / M.
exists (ball k r, ball x r).
  by split; apply: nbhsx_ballx; rewrite !divr_gt0// normr_gt0// gt_eqF.
rewrite -ball_normE /ball/= => lz /= [nk nx].
have := @ball_split _ _ (k *: lz.2)  (k *: x)  (lz.1 *: lz.2) `|e|.
rewrite -ball_normE /= real_lter_normr ?gtr0_real//.
rewrite (_ : _ < - e = false) ?orbF; last by rewrite ltr_nnorml// oppr_le0 ltW.
apply.
  rewrite -scalerBr normrZ -(@ltr_pM2r _ M^-1) ?invr_gt0//.
  by rewrite (le_lt_trans _ nx)// mulrC ler_pdivrMl// ler_wpM2r// invr_gt0.
rewrite -scalerBl normrZ.
rewrite (@le_lt_trans _ _ (`|k - lz.1| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
rewrite (@le_trans _ _ (`|lz.2| + `|x|)) ?lerDl//.
rewrite (@le_trans _ _ (`|x| + (`|x| + r)))//.
  rewrite addrC lerD// -lerBlDl -(normrN x) (le_trans (lerB_normD _ _))//.
  by rewrite distrC ltW.
rewrite [leRHS](_ : _ = M^-1 * (M *  M)); last first.
  by rewrite mulrA mulVf ?mul1r// gt_eqF.
rewrite [leLHS](_ : _ = M^-1 * (M * (`|x| + `|x|) + `|e| / 2)); last first.
  by rewrite mulrDr mulrA mulVf ?mul1r ?gt_eqF// mulrC addrA.
by rewrite ler_wpM2l ?invr_ge0// ?ltW// -ltrBrDl -mulrBr ltr_pM// ltrBrDl.
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
    rewrite ltr_leD//.
      by rewrite -ltr_pdivlMl ?mulrA ?mulVf ?mul1r // ?normrE ?gt_eqF.
    by rewrite -ler_pdivlMl ?mulrA ?mulVf ?mul1r ?ltW // ?normrE ?gt_eqF.
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
 Uniform_isTvs.Build K V add_continuous scale_continuous locally_convex.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K V normrZ.

HB.end.

Section standard_topology.
Variable R : numFieldType.
HB.instance Definition _ := Num.NormedZmodule.on R^o.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R R^o erefl.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build R R^o (@normrM _).

End standard_topology.

Lemma ball_itv {R : realFieldType} (x r : R) :
  ball x r = `]x - r, x + r[%classic.
Proof.
rewrite -(@ball_normE _ R^o) /ball_ set_itvE.
by apply/seteqP; split => t/=; rewrite ltr_distlC.
Qed.

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
Variable (R : archiFieldType).
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

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normrZV (x : V) : `|x| \in GRing.unit -> `| `| x |^-1 *: x | = 1.
Proof. by move=> nxu; rewrite normrZ normrV// normr_id mulVr. Qed.

End NormedModule_numDomainType.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Lemma normfZV (x : V) : x != 0 -> `| `|x|^-1 *: x | = 1.
Proof. by rewrite -normr_eq0 -unitfE => /normrZV->. Qed.

End NormedModule_numFieldType.

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R) := within (fun u => x < u) (nbhs x).
Local Notation "x ^'-" := (at_left x) : classical_set_scope.
Local Notation "x ^'+" := (at_right x) : classical_set_scope.

Global Instance at_right_proper_filter (x : R) : ProperFilter x^'+.
Proof.
apply: Build_ProperFilter => -[_/posnumP[d] /(_ (x + d%:num / 2))].
apply; last by rewrite ltrDl.
by rewrite /= opprD addNKr normrN ger0_norm// gtr_pMr// invf_lt1// ltr1n.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter x^'-.
Proof.
apply: Build_ProperFilter => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last by rewrite gtrBl.
by rewrite /= opprB addrC subrK ger0_norm// gtr_pMr// invf_lt1// ltr1n.
Qed.

Lemma nbhs_right0P x (P : set R) :
  (\forall y \near x^'+, P y) <-> \forall e \near 0^'+, P (x + e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P -propeqE.
by apply: (@eq_near _ (nbhs (0 : R))) => y; rewrite ltrDl.
Qed.

Lemma nbhs_left0P x (P : set R) :
  (\forall y \near x^'-, P y) <-> \forall e \near 0^'+, P (x - e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P; split=> Px.
  rewrite -oppr0 nearN; near=> e; rewrite ltrN2 opprK => e_lt0.
  by apply: (near Px) => //; rewrite gtrDl.
by rewrite -oppr0 nearN; near=> e; rewrite gtrDl oppr_lt0; apply: (near Px).
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_leftP (p : R) (P : pred R) :
  (\forall x \near (- p)^'+, (P \o -%R) x) <-> (\forall x \near p^'-, P x).
Proof.
by rewrite nbhs_right0P nbhs_left0P; split;
  apply: filterS=> r/=; rewrite opprD opprK.
Qed.

Lemma nbhs_right_gt x : \forall y \near x^'+, x < y.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_left_lt x : \forall y \near x^'-, y < x.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_right_neq x : \forall y \near x^'+, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /gt_eqF->. Qed.

Lemma nbhs_left_neq x : \forall y \near x^'-, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /lt_eqF->. Qed.

Lemma nbhs_right_ge x : \forall y \near x^'+, x <= y.
Proof. by rewrite near_withinE; apply: nearW; apply/ltW. Qed.

Lemma nbhs_left_le x : \forall y \near x^'-, y <= x.
Proof. by rewrite near_withinE; apply: nearW => ?; apply/ltW. Qed.

Lemma nbhs_right_lt x z : x < z -> \forall y \near x^'+, y < z.
Proof.
move=> xz; exists (z - x) => //=; first by rewrite subr_gt0.
by move=> y /= + xy; rewrite distrC ?ger0_norm ?subr_ge0 1?ltW// ltrD2r.
Qed.

Lemma nbhs_right_ltW x z : x < z -> \forall y \near nbhs x^'+, y <= z.
Proof.
by move=> xz; near=> y; apply/ltW; near: y; exact: nbhs_right_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_ltDr x e : 0 < e -> \forall y \near x ^'+, y - x < e.
Proof.
move=> e0; near=> y; rewrite ltrBlDr; near: y.
by apply: nbhs_right_lt; rewrite ltrDr.
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_le x z : x < z -> \forall y \near x^'+, y <= z.
Proof. by move=> xz; near do apply/ltW; apply: nbhs_right_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_gt x z : z < x -> \forall y \near x^'-, z < y.
Proof.
move=> xz; rewrite nbhs_left0P; near do rewrite -ltrN2 opprB ltrBlDl.
by apply: nbhs_right_lt; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ge x z : z < x -> \forall y \near x^'-, z <= y.
Proof.
by move=> xz; near do apply/ltW; apply: nbhs_left_gt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ltBl x e : 0 < e -> \forall y \near x^'-, x - y < e.
Proof.
move=> e0; near=> y; rewrite -ltrBrDl ltrNl opprB; near: y.
by apply: nbhs_left_gt; rewrite ltrBlDr ltrDl.
Unshelve. all: by end_near. Qed.

Lemma withinN (A : set R) a :
  within A (nbhs (- a)) = - x @[x --> within (-%R @` A) (nbhs a)].
Proof.
rewrite eqEsubset /=; split; move=> E /= [e e0 aeE]; exists e => //.
  move=> r are ra; apply: aeE; last by rewrite memNE opprK.
  by rewrite /= opprK addrC distrC.
move=> r aer ar; rewrite -(opprK r); apply: aeE; last by rewrite -memNE.
by rewrite /= opprK -normrN opprD.
Qed.

Let fun_predC (T : choiceType) (f : T -> T) (p : pred T) : involutive f ->
  [set f x | x in p] = [set x | x in p \o f].
Proof.
by move=> fi; apply/seteqP; split => _/= [y hy <-];
  exists (f y) => //; rewrite fi.
Qed.

Lemma at_rightN a : (- a)^'+ = -%R @ a^'-.
Proof.
rewrite /at_right withinN [X in within X _](_ : _ = [set u | u < a])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

Lemma at_leftN a : (- a)^'- = -%R @ a^'+.
Proof.
rewrite /at_left withinN [X in within X _](_ : _ = [set u | a < u])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

(* NB: In not_near_at_rightP (and not_near_at_rightP), R has type numFieldType.
  It is possible realDomainType could make the proof simpler and at least as
  useful. *)
Lemma not_near_at_rightP (p : R) (P : pred R) :
  ~ (\forall x \near p^'+, P x) <->
  forall e : {posnum R}, exists2 x, p < x < p + e%:num & ~ P x.
Proof.
split=> [pPf e|ex_notPx].
- apply: contrapT => /forallPNP peP; apply: pPf; near=> t.
  apply: contrapT; apply: peP; apply/andP; split.
  + by near: t; exact: nbhs_right_gt.
  + by near: t; apply: nbhs_right_lt; rewrite ltrDl.
- rewrite /at_right near_withinE nearE.
  rewrite -filter_from_ballE /filter_from/= -forallPNP => _ /posnumP[d].
  have [x /andP[px xpd] notPx] := ex_notPx d; rewrite -existsNP; exists x => /=.
  apply: contra_not notPx; apply => //.
  by rewrite /ball/= ltr0_norm ?subr_lt0// opprB ltrBlDl.
Unshelve. all: by end_near. Qed.

Lemma not_near_at_leftP (p : R) (P : pred R) :
  ~ (\forall x \near p^'-, P x) <->
  forall e : {posnum R}, exists2 x : R, p - e%:num < x < p & ~ P x.
Proof.
rewrite -nbhs_right_leftP not_near_at_rightP; split => + e => /(_ e)[r pre Pr].
- by exists (- r) => //; rewrite ltrNr andbC ltrNl opprB addrC.
- by exists (- r) => /=; rewrite ?opprK// ltrN2 ltrNl opprD opprK andbC.
Qed.

End at_left_right.
#[global] Typeclasses Opaque at_left at_right.
Notation "x ^'-" := (at_left x) : classical_set_scope.
Notation "x ^'+" := (at_right x) : classical_set_scope.

#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

Lemma cvg_at_leftNP {T : topologicalType} {R : numFieldType}
    (f : R -> T) a (l : T) :
  f @ a^'- --> l <-> f \o -%R @ (- a)^'+ --> l.
Proof.
by rewrite at_rightN -?fmap_comp; under [_ \o _]eq_fun => ? do rewrite /= opprK.
Qed.

Lemma cvg_at_rightNP {T : topologicalType} {R : numFieldType}
    (f : R -> T) a (l : T) :
  f @ a^'+ --> l <-> f \o -%R @ (- a)^'- --> l.
Proof.
by rewrite at_leftN -?fmap_comp; under [_ \o _]eq_fun => ? do rewrite /= opprK.
Qed.

Section open_itv_subset.
Context {R : realType}.
Variables (A : set R) (x : R).

Lemma open_itvoo_subset :
  open A -> A x -> \forall r \near 0^'+, `]x - r, x + r[ `<=` A.
Proof.
move=> /[apply] -[] _/posnumP[r] /subset_ball_prop_in_itv xrA.
exists r%:num => //= k; rewrite /= distrC subr0 set_itvoo => /ltr_normlW kr k0.
by apply/(subset_trans _ xrA)/subset_itvW; apply/ltW;
  [rewrite ler_ltB | rewrite ler_ltD].
Qed.

Lemma open_itvcc_subset :
  open A -> A x -> \forall r \near 0^'+, `[x - r, x + r] `<=` A.
Proof.
move=> /[apply] -[] _/posnumP[r].
have -> : r%:num = 2 * (r%:num / 2) by rewrite mulrCA divff// mulr1.
move/subset_ball_prop_in_itvcc => /= xrA; exists (r%:num / 2) => //= k.
rewrite /= distrC subr0 set_itvcc => /ltr_normlW kr k0.
move=> z /andP [xkz zxk]; apply: xrA => //; rewrite in_itv/=; apply/andP; split.
  by rewrite (le_trans _ xkz)// lerB// ltW.
by rewrite (le_trans zxk)// lerD// ltW.
Qed.

End open_itv_subset.

Section at_left_right_topologicalType.
Variables (R : numFieldType) (V : topologicalType) (f : R -> V) (x : R).

Lemma cvg_at_right_filter (l : V) :
  f z @[z --> x] --> l -> f z @[z --> x^'+] --> l.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_left_filter (l : V) :
  f z @[z --> x] --> l -> f z @[z --> x^'-] --> l.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_right_within : f x @[x --> x^'+] --> f x ->
  f x @[x --> within (fun u => x <= u) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [<-|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

Lemma cvg_at_left_within : f x @[x --> x^'-] --> f x ->
  f x @[x --> within (fun u => u <= x) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [->|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

End at_left_right_topologicalType.

Section at_left_right_pmNormedZmod.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, `|x - y| <= e -> P y).
Proof.
rewrite nbhs0P/= near_withinE/= !near_simpl.
split=> /nbhs_norm0P[/= _/posnumP[e] /(_ _) Px]; apply/nbhs_norm0P.
  exists e%:num => //= r /= re yr y xyr; rewrite -[y](addrNK x) addrC.
  by apply: Px; rewrite /= distrC (le_lt_trans _ re)// gtr0_norm.
exists (e%:num / 2) => //= r /= re; apply: (Px (e%:num / 2)) => //=.
  by rewrite gtr0_norm// ltr_pdivrMr// ltr_pMr// ltr1n.
by rewrite opprD addNKr normrN ltW.
Qed.

Let cvgrP {F : set_system V} {FF : Filter F} (y : V) : [<->
  F --> y;
  forall eps, 0 < eps -> \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| < eps].
Proof.
tfae; first by move=> *; apply: cvgr_dist_le.
- by move=> Fy; near do apply: Fy; apply: nbhs_right_gt.
- move=> Fy; near=> e; near (0:R)^'+ => d; near=> x.
  rewrite (@le_lt_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_lt; near: e; apply: nbhs_right_gt.
- move=> Fy; apply/cvgrPdist_lt => e e_gt0; near (0:R)^'+ => d.
  near=> x; rewrite (@lt_le_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma cvgrPdist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 1)%N. Qed.

Lemma cvgrPdist_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| < eps.
Proof. exact: (cvgrP _ 0 3)%N. Qed.

Lemma cvgrPdist_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 2)%N. Qed.

Lemma cvgrPdistC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| <= eps.
Proof.
rewrite cvgrPdist_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_ltp; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| <= eps.
Proof.
by rewrite cvgrPdist_lep; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgr0Pnorm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| <= eps.
Proof.
rewrite cvgrPdistC_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_ltp; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| <= eps.
Proof.
by rewrite cvgrPdistC_lep; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| < u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have : `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)) /real_ltr_normlW.
rewrite realB// ltrBlDl => /(_ _)/lt_le_trans; apply => //.
by rewrite -lerBrDl; near: k; apply: nbhs_right_le; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| <= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_lt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| > u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have: `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)); rewrite distrC => /real_ltr_normlW.
rewrite realB// ltrBlDl  -ltrBlDr => /(_ isT); apply: le_lt_trans.
rewrite lerBrDl -lerBrDr; near: k; apply: nbhs_right_le.
by rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ge {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| >= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_gt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_neq0 {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> y != 0 -> \forall t \near F, f t != 0.
Proof.
move=> Fy z; near do rewrite -normr_gt0.
by apply: (@cvgr_norm_gt _ _ _ _ y); rewrite // normr_gt0.
Unshelve. all: by end_near. Qed.

End at_left_right_pmNormedZmod.
Arguments cvgr_norm_lt {R V T F FF f}.
Arguments cvgr_norm_le {R V T F FF f}.
Arguments cvgr_norm_gt {R V T F FF f}.
Arguments cvgr_norm_ge {R V T F FF f}.
Arguments cvgr_neq0 {R V T F FF f}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_lt end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_neq end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_neq end : core.
#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_lt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.

#[global] Hint Extern 0 (ProperFilter _^'-) =>
  (apply: at_left_proper_filter) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter _^'+) =>
  (apply: at_right_proper_filter) : typeclass_instances.

Section at_left_rightR.
Variable (R : numFieldType).

Lemma real_cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t < z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -(ltrD2r (- y)) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real ->  f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t <= z.
Proof.
move=> /real_cvgr_lt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

Lemma real_cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, y > z -> \forall t \near F, f t \is Num.real -> f t > z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -ltrN2 -(ltrD2l y) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z < y -> \forall t \near F, f t \is Num.real -> f t >= z.
Proof.
move=> /real_cvgr_gt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

End at_left_rightR.
Arguments real_cvgr_le {R T F FF f}.
Arguments real_cvgr_lt {R T F FF f}.
Arguments real_cvgr_ge {R T F FF f}.
Arguments real_cvgr_gt {R T F FF f}.

Section realFieldType.
Context (R : realFieldType).

Lemma at_right_in_segment (x : R) (P : set R) :
  (\forall e \near 0^'+, {in `[x - e, x + e], forall x, P x}) <-> (\near x, P x).
Proof.
rewrite nbhsr0P -propeqE; apply: eq_near => y /=.
by rewrite -propeqE; apply: eq_forall => z; rewrite ler_distlC.
Qed.

Lemma cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t < z.
Proof.
move=> Fy z zy; near=> x; rewrite -(ltrD2r (- y)) ltr_normlW//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t <= z.
Proof.
by move=> /cvgr_lt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

Lemma cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, y > z -> \forall t \near F, f t > z.
Proof.
move=> Fy z zy; near=> x; rewrite -ltrN2 -(ltrD2l y) ltr_normlW//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z < y -> \forall t \near F, f t >= z.
Proof.
by move=> /cvgr_gt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

End realFieldType.
Arguments cvgr_le {R T F FF f}.
Arguments cvgr_lt {R T F FF f}.
Arguments cvgr_ge {R T F FF f}.
Arguments cvgr_gt {R T F FF f}.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Definition fun1 {T : Type} {K : numFieldType} : T -> K := fun=> 1.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numDomainType)
    (V W : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (F G : set_system T) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

Lemma sub_dominatedr (T : Type) (K : numDomainType)
    (V : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set_system T) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Lemma dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Proof.
rewrite /dominated_by; split => [/pinfty_ex_gt0[M M_gt0]|[M]] FM.
  by exists M.
have [] := pselect (exists x, (h x != 0) && (`|f x| <= M * `|h x|)); last first.
  rewrite -forallNE => Nex; exists 0; split => //.
  move=> k k_gt0; apply: filterS FM => x /= f_le_Mh.
  have /negP := Nex x; rewrite negb_and negbK f_le_Mh orbF => /eqP h_eq0.
  by rewrite h_eq0 normr0 !mulr0 in f_le_Mh *.
case => x0 /andP[hx0_neq0] /(le_trans (normr_ge0 _)) /ger0_real.
rewrite realrM // ?normr_eq0// => M_real.
exists M; split => // k Mk; apply: filterS FM => x /le_trans/= ->//.
by rewrite ler_wpM2r// ltW.
Qed.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pM2r ?normr_gt0// ltrDl.
Qed.

Definition bounded_near {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (F G : set_system T) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Proof. by move=> FG f; rewrite /bounded_near; apply: filterS=> M; apply: FG. Qed.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (f g : T -> V) (F : set_system T) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Proof.
move=> le_fg; rewrite /bounded_near; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Unshelve. all: by end_near. Qed.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : Filter F}:
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltrDl.
Qed.

Notation "[ 'bounded' E | x 'in' A ]" :=
  (bounded_near (fun x => E) (globally A)).
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_cst (K : numFieldType) {V : pseudoMetricNormedZmodType K}
  (k : V) T (A : set T) : [bounded k | _ in A].
Proof.
rewrite /bounded_near; near=> M => t At /=.
by near: M; exact: nbhs_pinfty_ge.
Unshelve. all: end_near. Qed.

Lemma bounded_fun_has_ubound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_ubound (range a).
Proof.
move=> [M [Mreal]]/(_ (`|M| + 1)).
rewrite (le_lt_trans (ler_norm _)) ?ltrDl// => /(_ erefl) aM.
by exists (`|M| + 1) => _ [n _ <-]; rewrite (le_trans (ler_norm _))// aM.
Qed.

Lemma bounded_funN (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> bounded_fun (- a).
Proof.
move=> [M [Mreal aM]]; rewrite /bounded_fun /bounded_near; near=> x => y /= _.
by rewrite normrN; apply: aM.
Unshelve. all: by end_near. Qed.

Lemma bounded_fun_has_lbound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_lbound (range a).
Proof.
move=> /bounded_funN/bounded_fun_has_ubound ba; apply/has_lb_ubN.
by apply: subset_has_ubound ba => _ [_ [n _] <- <-]; exists n.
Qed.

Lemma bounded_funD (T : Type) (R : realFieldType) (a b : T -> R) :
  bounded_fun a -> bounded_fun b -> bounded_fun (a \+ b).
Proof.
move=> [M [Mreal Ma]] [N [Nreal Nb]].
rewrite /bounded_fun/bounded_near; near=> x => y /= _.
rewrite (le_trans (ler_normD _ _))// [x]splitr.
by rewrite lerD// (Ma, Nb)// ltr_pdivlMr//;
   near: x; apply: nbhs_pinfty_gt; rewrite ?rpredM ?rpred_nat.
Unshelve. all: by end_near. Qed.

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" :=
  (dominated_by (self_sub id) k (self_sub f)) : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set_system (V * V)) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
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

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Section cvgr_norm_infty.
Variables (I : Type) (F : set_system I) (FF : Filter F) (f : I -> V) (y : V).

Lemma cvgr_norm_lty :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| < M.
Proof. by move=> Fy; near do exact: (cvgr_norm_lt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ley :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| <= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_le y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gtNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| > M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_gt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_geNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| >= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_ge y).
Unshelve. all: by end_near. Qed.

End cvgr_norm_infty.

Lemma cvg_bounded {I} {F : set_system I} {FF : Filter F} (f : I -> V) (y : V) :
  f @ F --> y -> bounded_near f F.
Proof. exact: cvgr_norm_ley. Qed.

End NormedModule_numFieldType.
Arguments cvgr_norm_lty {R V I F FF}.
Arguments cvgr_norm_ley {R V I F FF}.
Arguments cvgr_norm_gtNy {R V I F FF}.
Arguments cvgr_norm_geNy {R V I F FF}.
Arguments cvg_bounded {R V I F FF}.
#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Lemma cvg_at_rightE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'+).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_right _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _]; apply: xe_A.
Qed.
Arguments cvg_at_rightE {R V} f x.

Lemma cvg_at_leftE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'-).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_left _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _].
by apply: xe_A => //; rewrite eq_sym.
Qed.
Arguments cvg_at_leftE {R V} f x.

Section continuous_within_itvP.
Context {R : realType}.
Implicit Type f : R -> R.

Let near_at_left (a : itv_bound R) b f eps : (a < BLeft b)%O -> 0 < eps ->
  {within [set` Interval a (BRight b)], continuous f} ->
  \forall t \near b^'-, normr (f b - f t) < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (cf b).
rewrite /dnbhs/= near_withinE !near_simpl /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//; last first.
  rewrite /= in_itv/= lexx andbT.
  by move: a ab {cf} => [[a|a]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: a ab {cf} => [a0 a/= /[!bnd_simp] ab|[_|//]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?lt_eqF// !in_itv/= (ltW ac)/= andbT; move: cba => /=.
  rewrite gtr0_norm ?subr_gt0// ltrD2l ltrNr opprK => {}ac.
  by case: a0 => //=; exact/ltW.
- by exists 1%R => //= c cb1 + bc; apply; rewrite ?lt_eqF ?in_itv/= ?ltW.
Qed.

Let near_at_right a (b : itv_bound R) f eps : (BRight a < b)%O -> 0 < eps ->
  {within [set` Interval (BLeft a) b], continuous f} ->
  \forall t \near a^'+, normr (f a - f t) < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (cf a).
rewrite /dnbhs/= near_withinE !near_simpl// /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//; last first.
  rewrite /= in_itv/= lexx//=.
  by move: b ab {cf} => [[b|b]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: b ab {cf} => [b0 b/= /[!bnd_simp] ab|[//|_]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?gt_eqF// !in_itv/= (ltW ac)/=; move: cba => /=.
  rewrite ltr0_norm ?subr_lt0// opprB ltrD2r.
  by case: b0 => //= /ltW.
- by exists 2%R => //= c ca1 + ac; apply; rewrite ?gt_eqF ?in_itv/= ?ltW.
Qed.

Lemma continuous_within_itvP a b f : a < b ->
  {within `[a, b], continuous f} <->
  [/\ {in `]a, b[, continuous f}, f @ a^'+ --> f a & f @b^'- --> f b].
Proof.
move=> ab; split=> [abf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=..].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by move: abf; exact/continuous_subspaceW/subset_itvW.
  - by apply: near_at_right => //; rewrite bnd_simp.
  - by apply: near_at_left => //; rewrite bnd_simp.
case=> ctsoo ctsL ctsR; apply/subspace_continuousP => x /andP[].
rewrite !bnd_simp/= !le_eqVlt => /predU1P[<-{x}|ax] /predU1P[|].
- by move/eqP; rewrite lt_eqF.
- move=> _; apply/cvgrPdist_lt => eps eps_gt0 /=.
  move/cvgrPdist_lt/(_ _ eps_gt0): ctsL; rewrite /at_right !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  have : a <= c by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> ->; apply/cvgrPdist_lt => eps eps_gt0 /=.
  move/cvgrPdist_lt/(_ _ eps_gt0): ctsR; rewrite /at_left !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0 // => c cba + ac.
  have : c <= b by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> xb; have aboox : x \in `]a, b[ by rewrite !in_itv/= ax.
  rewrite within_interior; first exact: ctsoo.
  suff : `]a, b[ `<=` interior `[a, b] by exact.
  by rewrite -open_subsetE; [exact: subset_itvW| exact: interval_open].
Qed.

Lemma continuous_within_itvcyP a (f : R -> R) :
  {within `[a, +oo[, continuous f} <->
  {in `]a, +oo[, continuous f} /\ f x @[x --> a^'+] --> f a.
Proof.
split=> [cf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?; rewrite /= !in_itv !andbT/= => /ltW.
  - by apply: near_at_right => //; rewrite bnd_simp.
move=> [cf fa]; apply/subspace_continuousP => x /andP[].
rewrite bnd_simp/= le_eqVlt => /predU1P[<-{x}|ax] _.
- apply/cvgrPdist_lt => eps eps_gt0/=; move/cvgrPdist_lt/(_ _ eps_gt0) : fa.
  rewrite /at_right !near_withinE; apply: filter_app.
  exists 1%R => //= c c1a /[swap]; rewrite in_itv/= andbT le_eqVlt.
  by move=> /predU1P[->|/[swap]/[apply]//]; rewrite subrr normr0.
- have xaoo : x \in `]a, +oo[ by rewrite in_itv/= andbT.
  rewrite within_interior; first exact: cf.
  suff : `]a, +oo[ `<=` interior `[a, +oo[ by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/= !andbT; exact: ltW.
Qed.

Lemma continuous_within_itvNycP b (f : R -> R) :
  {within `]-oo, b], continuous f} <->
  {in `]-oo, b[, continuous f} /\ f x @[x --> b^'-] --> f b.
Proof.
split=> [cf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?/=; rewrite !in_itv/=; exact: ltW.
  - by apply: near_at_left => //; rewrite bnd_simp.
move=> [cf fb]; apply/subspace_continuousP => x /andP[_].
rewrite bnd_simp/= le_eqVlt=> /predU1P[->{x}|xb].
- apply/cvgrPdist_lt => eps eps_gt0/=; move/cvgrPdist_lt/(_ _ eps_gt0) : fb.
  rewrite /at_right !near_withinE; apply: filter_app.
  exists 1%R => //= c c1b /[swap]; rewrite in_itv/= le_eqVlt.
  by move=> /predU1P[->|/[swap]/[apply]//]; rewrite subrr normr0.
- have xb_i : x \in `]-oo, b[ by rewrite in_itv/=.
  rewrite within_interior; first exact: cf.
  suff : `]-oo, b[ `<=` interior `]-oo, b] by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/=; exact: ltW.
Qed.

End continuous_within_itvP.

Lemma within_continuous_continuous {R : realType} a b (f : R -> R) x : (a < b)%R ->
  {within `[a, b], continuous f} -> x \in `]a, b[ -> {for x, continuous f}.
Proof.
by move=> ab /continuous_within_itvP-/(_ ab)[+ _] /[swap] xab cf; exact.
Qed.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE maxr_pMr.
Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build K 'M[K]_(m.+1, n.+1)
    mx_normZ.

End matrix_NormedModule.

Section prod_NormedModule.
Context {K : numFieldType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normrZ maxr_pMr. Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K (U * V)%type
  prod_norm_scale.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangle m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof. exact: ler_normD. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. exact: ler_normD. Qed.

End example_of_sharing.

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

(** Normed vector spaces have some continuous functions that are in fact
continuous on pseudoMetricNormedZmodType *)
Section NVS_continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; apply/cvgrPdist_lt=> e e0; near do rewrite -opprD normrN.
exact: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.

Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Proof.
case: n => [|n] x; first exact: cvg_cst.
apply/cvgrPdist_lt=> _/posnumP[e]; near=> a.
by rewrite -mulrnBl normrMn -mulr_natr -ltr_pdivlMr.
Unshelve. all: by end_near. Qed.

Lemma norm_continuous : continuous (normr : V -> K).
Proof.
move=> x; apply/cvgrPdist_lt => e e0; apply/nbhs_normP; exists e => //= y.
exact/le_lt_trans/ler_dist_dist.
Qed.

End NVS_continuity_pseudoMetricNormedZmodType.

Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).
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

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous (_, _))).
Qed.

End NVS_continuity_normedModType.

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

Section cvg_composition_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> - f @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

Lemma cvgNP f a : - f @ F --> - a <-> f @ F --> a.
Proof. by split=> /cvgN//; rewrite !opprK. Qed.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Proof. by move=> /cvgN /cvgP. Qed.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Proof. by rewrite propeqE; split=> /cvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Proof. by move=> ?;  apply: continuous_cvg => //; exact: natmul_continuous. Qed.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Proof. by move=> /cvgMn /cvgP. Qed.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply add_continuous. Qed.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Proof. by have := cvgP _ (cvgD _ _); apply. Qed.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Proof. by move=> ? ?; apply: cvgD => //; apply: cvgN. Qed.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Proof. by have := cvgP _ (cvgB _ _); apply. Qed.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cvgD; apply.
by move=> /is_cvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Proof. by rewrite addrC; apply: is_cvgDlE. Qed.

Lemma cvg_sub0 f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Proof.
by move=> Cfg Cg; have := cvgD Cfg Cg; rewrite subrK add0r; apply.
Qed.

Lemma cvg_zero f a : (f - cst a) @ F --> (0 : V) -> f @ F --> a.
Proof. by move=> Cfa; apply: cvg_sub0 Cfa (cvg_cst _). Qed.

Lemma subr_cvg0 f a : (fun x => f x - a) @ F --> 0 <-> f @ F --> a.
Proof.
split=> [?|fFk]; first exact: cvg_zero.
by rewrite -(@subrr _ a)//; apply: cvgB => //; exact: cvg_cst.
Qed.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K).
Proof. by apply: continuous_cvg; apply: norm_continuous. Qed.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K) @ F).
Proof. by have := cvgP _ (cvg_norm _); apply. Qed.

Lemma norm_cvg0P f : `|f x| @[x --> F] --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_norm; rewrite normr0.
move=> f0; apply/cvgr0Pnorm_lt => e e_gt0.
by near do rewrite -normr_id; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma norm_cvg0 f : `|f x| @[x --> F] --> 0 -> f @ F --> 0.
Proof. by rewrite norm_cvg0P. Qed.

End cvg_composition_pseudometric.

Lemma cvgr_expr2 {R : realFieldType} : (x ^+ 2 : R) @[x --> +oo] --> +oo.
Proof.
by apply/cvgryPge => M; near=> x; rewrite (@le_trans _ _ x)// expr2 ler_peMl.
Unshelve. all: end_near. Qed.

Lemma cvgr_idn {R : realType} : (n%:R : R) @[n --> \oo] --> +oo.
Proof.
by apply/cvgryPge => M; exact: nbhs_infty_ger.
Unshelve. all: end_near. Qed.

Section cvg_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply scale_continuous. Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZl  _); apply. Qed.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZr  _); apply. Qed.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZr k^-1)|/(@cvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

End cvg_composition_normed.

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

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Proof. exact: cvgZl. Qed.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Proof. exact: cvgZr. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZr. Qed.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (g @ F).
Proof. exact: is_cvgZrE. Qed.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f \* g @ F).
Proof.
move=> f_cvg; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMr.
Qed.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (f @ F).
Proof.
move=> a_neq0; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMrE.
Qed.

End cvg_composition_field.

Section limit_composition_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgN. Qed.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgD. Qed.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgB. Qed.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K) @ F) = `|lim (f @ F)|.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_norm. Qed.

End limit_composition_pseudometric.

Section limit_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgZ. Qed.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZl. Qed.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZr. Qed.

End limit_composition_normed.

Section limit_composition_field.
Context {K : numFieldType} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgM. Qed.

End limit_composition_field.

Section cvg_composition_field_proper.
Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma limV f : lim (f @ F) != 0 -> lim (f\^-1 @ F) = (lim (f @ F))^-1.
Proof.
by move=> ?; apply: cvg_lim => //; apply: cvgV => //; apply: cvgNpoint.
Qed.

Lemma is_cvgVE f : lim (f @ F) != 0 -> cvg (f\^-1 @ F) = cvg (f @ F).
Proof.
move=> ?; apply/propeqP; split=> /is_cvgV; last exact.
by rewrite inv_funK; apply; rewrite limV ?invr_eq0//.
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

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s \* t)}.
Proof. by move=> f_cont g_cont; apply: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1%R)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.

Section nbhs_ereal.
Context {R : numFieldType} (P : \bar R -> Prop).

Lemma nbhs_EFin (x : R) : (\forall y \near x%:E, P y) <-> \near x, P x%:E.
Proof. done. Qed.

Lemma nbhs_ereal_pinfty :
  (\forall x \near +oo%E, P x) <-> [/\ P +oo%E & \forall x \near +oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.

Lemma nbhs_ereal_ninfty :
  (\forall x \near -oo%E, P x) <-> [/\ P -oo%E & \forall x \near -oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.
End nbhs_ereal.

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
- exact/(cvg_comp (@norm_continuous _ R r)).
- by exists r; split => // y ry; apply: rA; rewrite (lt_le_trans ry)// lee_abs.
- exists (- r)%R; rewrite realN; split => // y; rewrite EFinN -lteNr => yr.
  by apply: rA; rewrite (lt_le_trans yr)// -abseN lee_abs.
Qed.

Lemma cvg_abse f (a : \bar R) : f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Proof. by apply: continuous_cvg => //; apply: abse_continuous. Qed.

Lemma is_cvg_abse (f : I -> \bar R) : cvg (f @ F) -> cvg (`|f x|%E @[x --> F]).
Proof. by move/cvg_abse/cvgP. Qed.

Lemma is_cvgeN f : cvg (f @ F) -> cvg (\- f @ F).
Proof. by move=> /cvg_ex[l fl]; apply: (cvgP (- l)); exact: cvgeN. Qed.

Lemma is_cvgeNE f : cvg (\- f @ F) = cvg (f @ F).
Proof.
rewrite propeqE; split=> /cvgeNP/cvgP//.
by under eq_is_cvg do rewrite oppeK.
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

Lemma cvgeMl f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => y * f n) @ F --> y * x.
Proof. by move: y => [r| |]// _ /cvg_comp; apply; exact: mule_continuous. Qed.

Lemma is_cvgeMl f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => y * f n) @ F).
Proof. by move=> fy /(cvgeMl fy)/cvgP. Qed.

Lemma cvgeMr f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => f n * y) @ F --> x * y.
Proof.
by move=> ? ?; rewrite muleC; under eq_fun do rewrite muleC; exact: cvgeMl.
Qed.

Lemma is_cvgeMr f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => f n * y) @ F).
Proof. by move=> fy /(cvgeMr fy)/cvgP. Qed.

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
  + rewrite mulry ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_pinfty a0).
  + rewrite mulry gtr0_sg// ?mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_pinfty a0).
  + by rewrite /mule_def eqxx.
- move: f g a; abstract: bnoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulrNy ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_ninfty a0).
  + rewrite mulrNy gtr0_sg// ?mul1e.
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

Section closure_left_right_open.
Variable R : realFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R) = [set x | z <= x].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{v}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 zB]; near (0 : R)^'+ => d.
exists (z + d); split; rewrite /= ?ltrDl//; apply: zB => /=.
by rewrite opprD addNKr normrN gtr0_norm//.
Unshelve. all: by end_near. Qed.

Lemma closure_lt z : closure ([set x : R | x < z]) = [set x | x <= z].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{z}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 vB]; near (0 : R)^'+ => d.
exists (v - d); split; rewrite /= ?gtrDl ?oppr_lt0//; apply: vB => /=.
by rewrite opprB addrC addrNK gtr0_norm//; near: d.
Unshelve. all: by end_near. Qed.

End closure_left_right_open.

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

Lemma limit_pointP (T : archiFieldType) (A : set T) (x : T) :
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

Lemma EFin_lim (R : realFieldType) (f : nat -> R) : cvgn f ->
  limn (EFin \o f) = (limn f)%:E.
Proof.
move=> cf; apply: cvg_lim => //; move/cvg_ex : cf => [l fl].
by apply: (cvg_comp fl); rewrite (cvg_lim _ fl).
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
Proof. by move=> yfn cf; apply/cvg_lim => //; exact: cvgeMl. Qed.

Lemma limeMr f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => f n * y) @ F) = lim (f @ F) * y.
Proof. by move=> yfn cf; apply/cvg_lim => //; apply: cvgeMr. Qed.

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
     rewrite !(lteifF,lteifT,sup_ubound,inf_lbound,sup_ub_strict,inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lteifF, lteifT);
     [rewrite inf_lbound | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lteifF, lteifT);
     [rewrite sup_ubound | rewrite sup_ub_strict].
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
    rewrite sup_ubound//=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle sup_le_ub ?andbT; last by move=> u [_] /andP[].
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
     apply: sup_ubound; first by exists y => u [_] /andP[].
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
Proof. by rewrite /Rhull -set_itv_infty_infty asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)), cancel Rhull pred_set}.
Proof. by move=> X /asboolP iX; apply/esym/is_intervalP. Qed.

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

Section segment.
Variable R : realType.

(** properties of segments in R *)

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

Lemma rV_compact (T : ptopologicalType) n (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (prod_topology _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (prod_topology _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter_ex.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : prod_topology _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in [set x | 'I_n.+1 x]];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R]_n.+1) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R]_n.+1 | forall i, v ord0 i \in `[(- (M + 1)), (M + 1)]].
  apply: (@rV_compact _  _ (fun _ => `[(- (M + 1)), (M + 1)]%classic)).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltrDl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v x.1 x.2| | x : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
by rewrite [leRHS]/normr /= mx_normrE; apply/bigmax_geP; right => /=; exists j.
Qed.

(** Some limits on real functions *)

Section Shift.
Context {R : zmodType} {T : Type}.

Definition shift (x y : R) := y + x.
Notation center c := (shift (- c)).
Arguments shift x / y.

Lemma comp_shiftK (x : R) (f : R -> T) : (f \o shift x) \o center x = f.
Proof. by rewrite funeqE => y /=; rewrite addrNK. Qed.

Lemma comp_centerK (x : R) (f : R -> T) : (f \o center x) \o shift x = f.
Proof. by rewrite funeqE => y /=; rewrite addrK. Qed.

Lemma shift0 : shift 0 = id.
Proof. by rewrite funeqE => x /=; rewrite addr0. Qed.

Lemma center0 : center 0 = id.
Proof. by rewrite oppr0 shift0. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

Lemma near_shift {K : numDomainType} {R : normedModType K}
   (y x : R) (P : set R) :
   (\near x, P x) = (\forall z \near y, (P \o shift (x - y)) z).
Proof.
(* rewrite propeqE nbhs0P [X in _ <-> X]nbhs0P/= -propeqE. *)
(* by apply: eq_near => e; rewrite ![_ + e]addrC addrACA subrr addr0. *)
rewrite propeqE; split=> /= /nbhs_normP [_/posnumP[e] ye];
apply/nbhs_normP; exists e%:num => //= t et.
  by apply: ye; rewrite /= distrC addrCA [x + _]addrC addrK distrC.
by have /= := ye (t - (x - y)); rewrite opprB addrCA subrKA addrNK; exact.
Qed.

Lemma cvg_comp_shift {T : Type} {K : numDomainType} {R : normedModType K}
  (x y : R) (f : R -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Section continuous_shift.
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

End continuous_shift.

Lemma ball_open (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open (ball x r).
Proof.
rewrite openE -ball_normE /interior => r0 y /= Bxy; near=> z.
rewrite /= (le_lt_trans (ler_distD y _ _)) // addrC -ltrBrDr.
by near: z; apply: cvgr_dist_lt; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ball_open_nbhs (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open_nbhs x (ball x r).
Proof. by move=> e0; split; [exact: ball_open|exact: ballxx]. Qed.

Section Closed_Ball.

Definition closed_ball_ (R : numDomainType) (V : zmodType) (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

Lemma closed_closed_ball_ (R : realFieldType) (V : normedModType R)
  (x : V) (e : R) : closed (closed_ball_ normr x e).
Proof.
rewrite /closed_ball_ -/((normr \o (fun y => x - y)) @^-1` [set x | x <= e]).
apply: (closed_comp _ (@closed_le _ _)) => y _.
apply: (continuous_comp _ (@norm_continuous _ _ _)).
exact: (continuousB (@cst_continuous _ _ _ _)).
Qed.

Definition closed_ball (R : numDomainType) (V : pseudoMetricType R)
  (x : V) (e : R) := closure (ball x e).

Lemma closed_ball0 (R : realFieldType) (a r : R) :
  r <= 0 -> closed_ball a r = set0.
Proof.
move=> /ball0 r0; apply/seteqP; split => // y.
by rewrite /closed_ball r0 closure0.
Qed.

Lemma closed_ballxx (R : numDomainType) (V : pseudoMetricType R) (x : V)
  (e : R) : 0 < e -> closed_ball x e x.
Proof. by move=> ?; exact/subset_closure/ballxx. Qed.

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
  rewrite -[X in X - _](@divrr _ `|x - y|) ?unitfE ?normr_eq0 ?subr_eq0//.
  rewrite -mulrBl -scalerA normrZ normfZV ?subr_eq0// mulr1.
  rewrite gtr0_norm; first by rewrite ltrBlDl xye ltrDr mulr_gt0.
  by rewrite subr_gt0 xye ltr_pdivrMr // mulr_natr mulr2n ltr_pwDl.
rewrite -ball_normE /ball_ /= opprD addrA addrN add0r normrN normrZ.
rewrite normfZV ?subr_eq0// mulr1 normrM (gtr0_norm s0) gtr0_norm //.
by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
Qed.

Lemma closed_ball_closed (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : closed (closed_ball x r).
Proof. exact: closed_closure. Qed.

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

Lemma subset_closed_ball (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : ball x r `<=` closed_ball x r.
Proof. exact: subset_closure. Qed.

Lemma open_subball {R : numFieldType} {M : normedModType R} (A : set M)
  (x : M) : open A -> A x -> \forall e \near 0^'+, ball x e `<=` A.
Proof.
move=> oA Ax; have /nbhsr0P/= : nbhs x A by exact/open_nbhs_nbhs.
apply: filterS => e xeA y exy; apply: xeA.
by rewrite -ball_normE/= in exy; exact: ltW.
Qed.

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

Lemma locally_compactR (R : realType) : locally_compact [set: R].
Proof.
move=> x _; rewrite withinET; exists (closed_ball x 1).
  by apply/nbhs_closedballP; exists 1%:pos.
by split; [apply: closed_ballR_compact | apply: closed_ball_closed].
Qed.

Lemma subset_closure_half (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : 0 < r -> closed_ball x (r / 2) `<=` ball x r.
Proof.
move:r => _/posnumP[r] z /(_ (ball z ((r%:num/2)%:pos)%:num)) [].
  exact: nbhsx_ballx.
by move=> y [+/ball_sym]; rewrite [t in ball x t z]splitr; apply: ball_triangle.
Qed.

Lemma le_closed_ball (R : numFieldType) (M : pseudoMetricNormedZmodType R)
  (x : M) (e1 e2 : R) : (e1 <= e2)%O -> closed_ball x e1 `<=` closed_ball x e2.
Proof. by rewrite /closed_ball => le; apply/closure_subset/le_ball. Qed.

Lemma interior_closed_ballE (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> (closed_ball x r)° = ball x r.
Proof.
move=> r0; rewrite eqEsubset; split; last first.
  by rewrite -open_subsetE; [exact: subset_closure | exact: ball_open].
move=> /= t; rewrite closed_ballE // /interior /= -nbhs_ballE => [[]] s s0.
have [-> _|nxt] := eqVneq t x; first exact: ballxx.
near ((0 : R^o)^') => e; rewrite -ball_normE /closed_ball_ => tsxr.
pose z := t + `|e| *: (t - x); have /tsxr /= : `|t - z| < s.
  rewrite distrC addrAC subrr add0r normrZ normr_id.
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

End Closed_Ball.

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
