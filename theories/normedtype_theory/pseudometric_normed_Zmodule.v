(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals topology.
From mathcomp Require Import function_spaces real_interval prodnormedzmodule.
From mathcomp Require Import tvs num_normedtype.

(**md**************************************************************************)
(* # Normed topological abelian groups                                        *)
(*                                                                            *)
(* This directory (`normed_theory`) file extends the topological hierarchy    *)
(* with norm-related notions. Note that balls in `topology_theory` are not    *)
(* necessarily open, here they are.                                           *)
(*                                                                            *)
(* ## Helper functions                                                        *)
(* To be used in `normed_module.v`.                                           *)
(* ```                                                                        *)
(*                      shift x y == y + x                                    *)
(*                       center c := shift (- c)                              *)
(*                                   This is a notation.                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Left and right filters                                                  *)
(* ```                                                                        *)
(*                     x^'-, x^'+ == filters on real numbers for predicates   *)
(*                                   s.t. nbhs holds on the left/right of x   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Normed topological abelian groups                                       *)
(* ```                                                                        *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   abelian group equipped with a norm       *)
(*                                   The HB class is PseudoMetricNormedZmod.  *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Closed balls                                                            *)
(* ```                                                                        *)
(*             closed_ball_ norm x e := [set y | norm (x - y) <= e]           *)
(*                       closed_ball == closure of a ball                     *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Domination                                                              *)
(* ```                                                                        *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*     strictly_dominated_by h k f F == `|f| < k * `|h|, near F               *)
(*                  bounded_near f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets                   *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of functions bounded on their     *)
(*                                      whole domain                          *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                   fun1 : T -> K^o := fun=> 1                               *)
(*                                      where K : numFiedlType                *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x ^'+" (at level 3, left associativity, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, left associativity, format "x ^'-").
Reserved Notation "[ 'bounded' E | x 'in' A ]"
  (at level 0, x name, format "[ 'bounded'  E  |  x  'in'  A ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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

Lemma centerN (x y : R) : center x (- y) = - shift x y.
Proof. by rewrite /shift opprD. Qed.

Lemma shiftN (x y : R) : shift x (- y) = - center x y.
Proof. by rewrite /shift opprD opprK. Qed.

Lemma image_centerN (E : set R) (x : R) :
  [set center x (- y) | y in E] =[set - (shift x y) | y in E].
Proof.
by apply/seteqP; split => y [] u Eu <- /=; exists u => //; rewrite opprD.
Qed.

Lemma image_shiftN (E : set R) (x : R) :
  [set shift x (- y) | y in E] = [set - (center x y) | y in E].
Proof. by rewrite -(opprK x) image_centerN opprK. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

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

End at_left_right.
#[global] Typeclasses Opaque at_left at_right.
Notation "x ^'-" := (at_left x) : classical_set_scope.
Notation "x ^'+" := (at_right x) : classical_set_scope.

#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

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

HB.mixin Record NormedZmod_PseudoMetric_eq (R : numDomainType) T
    of Num.NormedZmodule R T & PseudoPointedMetric R T := {
  pseudo_metric_ball_norm : ball = ball_ (fun x : T => `| x |)
}.

#[short(type="pseudoMetricNormedZmodType")]
HB.structure Definition PseudoMetricNormedZmod (R : numDomainType) :=
  {T of Num.NormedZmodule R T & PseudoMetric R T
   & NormedZmod_PseudoMetric_eq R T & isPointed T}.

Section pseudoMetricNormedZmod_numDomainType.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

(**md Balls defined by the norm: *)
Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by rewrite pseudo_metric_ball_norm. Qed.

(**md Neighborhoods defined by the norm: *)
Local Notation nbhs_norm := (nbhs_ball_ ball_norm).

(* if we do not give the V argument to nbhs, the universally quantified set that
appears inside the notation for cvg_to has type
set (let '{| PseudoMetricNormedZmodule.sort := T |} := V in T) instead of set V,
which causes an inference problem in derive.v *)
Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Proof. by rewrite ball_normE funeqE => x; rewrite -filter_from_ballE. Qed.

Lemma nbhs_normP x (P : V -> Prop) : (\near x, P x) <-> nbhs_norm x P.
Proof. by rewrite nbhs_nbhs_norm. Qed.

Lemma nbhs_le_nbhs_norm (x : V) : @nbhs V _ x `=>` nbhs_norm x.
Proof. by move=> P [e e0 subP]; apply/nbhs_normP; exists e. Qed.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Proof. by move=> P /nbhs_normP [e e0 Pxe]; exists e. Qed.

Lemma filter_from_norm_nbhs x :
  @filter_from K _ [set x : K | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : V -> Prop) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : V -> Prop) :
  @filter_from K _ [set x : K | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : V -> Prop) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum K}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num => /=. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum K}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : K) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : K) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : K) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma fcvgrPdist_lt {F : set_system V} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !nbhs_simpl. Qed.

Lemma cvgrPdist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgrPdistC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_lt; under eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgr_dist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| < eps.
Proof. by move=> /cvgrPdist_lt. Qed.

Lemma cvgr_distC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| < eps.
Proof. by move=> /cvgrPdistC_lt. Qed.

Lemma cvgr_dist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma cvgr_distC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_distC_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_norm0P {P : V -> Prop} :
  (\forall x \near 0, P x) <->
  filter_from [set e | 0 < e] (fun e => [set y | `|y| < e]) P.
Proof.
rewrite nbhs_normP; split=> -[/= e e0 Pe];
by exists e => // y /=; have /= := Pe y; rewrite distrC subr0.
Qed.

Lemma cvgr0Pnorm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_lt; under eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| < eps.
Proof. by move=> /cvgr0Pnorm_lt. Qed.

Lemma cvgr0_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs0_lt e : 0 < e -> \forall x \near (0 : V), `|x| < e.
Proof. exact: cvgr0_norm_lt. Qed.

Lemma dnbhs0_lt e : 0 < e -> \forall x \near (0 : V)^', `|x| < e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_lt. Qed.

Lemma nbhs0_le e : 0 < e -> \forall x \near (0 : V), `|x| <= e.
Proof. exact: cvgr0_norm_le. Qed.

Lemma dnbhs0_le e : 0 < e -> \forall x \near (0 : V)^', `|x| <= e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_le. Qed.

Lemma nbhs_norm_ball x (eps : {posnum K}) : nbhs_norm x (ball x eps%:num).
Proof. by rewrite nbhs_nbhs_norm; exact: nbhsx_ballx. Qed.

Lemma nbhsDl (P : set V) (x y : V) :
  (\forall z \near (x + y), P z) <-> (\near x, P (x + y)).
Proof.
split=> /nbhs_normP[_/posnumP[e]/= Px]; apply/nbhs_normP; exists e%:num => //=.
  by move=> z /= xze; apply: Px; rewrite /= [z + y]addrC addrKA.
by move=> z /= xyz; rewrite -[z](addrNK y); apply: Px; rewrite /= opprB addrA.
Qed.

Lemma nbhsDr (P : set V) x y :
  (\forall z \near (x + y), P z) <-> (\near y, P (x + y)).
Proof. by rewrite addrC nbhsDl -propeqE; apply: eq_near => ?; rewrite addrC. Qed.

Lemma nbhs0P (P : set V) x : (\near x, P x) <-> (\forall e \near 0, P (x + e)).
Proof. by rewrite -nbhsDr addr0. Qed.

End pseudoMetricNormedZmod_numDomainType.
#[global] Hint Resolve normr_ge0 : core.
Arguments cvgr_dist_lt {_ _ _ F FF}.
Arguments cvgr_distC_lt {_ _ _ F FF}.
Arguments cvgr_dist_le {_ _ _ F FF}.
Arguments cvgr_distC_le {_ _ _ F FF}.
Arguments cvgr0_norm_lt {_ _ _ F FF}.
Arguments cvgr0_norm_le {_ _ _ F FF}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr_dist_lt] end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr_distC_lt] end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr0_norm_lt] end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr_dist_le] end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr_distC_le] end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: cvgr0_norm_le] end : core.

Section pseudoMetricNormedZmod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma norm_hausdorff : hausdorff_space V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num.
  by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltrD acr bcr); rewrite -r22 (distrC b c).
by move/(le_lt_trans (ler_distD c a b)); rewrite -mulrA mulVf// mulr1 ltxx.
Qed.
Local Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

(* TODO: check if the following lemma are indeed useless *)
(*       i.e. where the generic lemma is applied, *)
(*            check that norm_hausdorff is not used in a hard way *)

Lemma norm_closeE (x y : V): close x y = (x = y). Proof. exact: closeE. Qed.
Lemma norm_close_eq (x y : V) : close x y -> x = y. Proof. exact: close_eq. Qed.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Proof. exact: cvg_unique. Qed.

Lemma norm_cvg_eq (x y : V) : x --> y -> x = y. Proof. exact: (@cvg_eq V). Qed.
Lemma norm_lim_id (x : V) : lim (nbhs x) = x. Proof. exact: lim_id. Qed.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Proof. exact: (@cvg_lim V). Qed.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. exact: lim_near_cst. Qed.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Proof. exact: lim_cst. Qed.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Proof. exact: cvgi_unique. Qed.

Lemma norm_cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof. exact: cvgi_lim. Qed.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_split _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitr _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitl _ _ z x y e; rewrite -ball_normE. Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
by move=> /posnumP[{}e] /le_lt_trans ->//; rewrite [ltRHS]splitr ltr_pwDl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

End pseudoMetricNormedZmod_numFieldType.
#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

Section prod_pseudoMetricNormedZmod.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite comparable_gt_max// ?real_comparable//; split=> /andP.
Qed.

Lemma prod_norm_ball : @ball _ (U * V)%type = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build K (U * V)%type
  prod_norm_ball.

End prod_pseudoMetricNormedZmod.

Section standard_topology_pseudoMetricNormedZmod.
Variable R : numFieldType.

HB.instance Definition _ := Num.NormedZmodule.on R^o.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R R^o erefl.

End standard_topology_pseudoMetricNormedZmod.

Lemma ball_itv {R : realFieldType} (x r : R) :
  ball x r = `]x - r, x + r[%classic.
Proof.
rewrite -(@ball_normE _ R^o) /ball_ set_itvE.
by apply/seteqP; split => t/=; rewrite ltr_distlC.
Qed.

(** Normed vector spaces have some continuous functions that are in fact
continuous on pseudoMetricNormedZmodType *)
Section continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma oppr_continuous : continuous (@GRing.opp V).
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
move=> x; apply/(@cvgrPdist_lt K K^o) => e e0; apply/nbhs_normP.
by exists e => //= y; exact/le_lt_trans/ler_dist_dist.
Qed.

End continuity_pseudoMetricNormedZmodType.
#[deprecated(since="mathcomp-analysis 1.11.0", note="renamed to `oppr_continuous`")]
Notation opp_continuous := oppr_continuous (only parsing).

(* TODO: generalize to R : numFieldType *)
Section hausdorff.

#[deprecated(since="mathcomp-analysis 1.10.0", note="use `norm_hausdorff` instead")]
Lemma pseudoMetricNormedZModType_hausdorff (R : realFieldType)
    (V : pseudoMetricNormedZmodType R) :
  hausdorff_space V.
Proof. exact: norm_hausdorff. Qed.

End hausdorff.

Section at_left_right.
Variable R : numFieldType.

Lemma nbhs_right0P x (P : set R) :
  (\forall y \near x^'+, P y) <-> \forall e \near 0^'+, P (x + e).
Proof.
rewrite !near_withinE !near_simpl.
rewrite (@nbhs0P R R^o)// -propeqE.
by apply: (@eq_near _ (nbhs (0 : R))) => y; rewrite ltrDl.
Qed.

Lemma nbhs_left0P x (P : set R) :
  (\forall y \near x^'-, P y) <-> \forall e \near 0^'+, P (x - e).
Proof.
rewrite !near_withinE !near_simpl (@nbhs0P R R^o); split=> Px.
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

Lemma nbhs_left_gt (x z : R) : z < x -> \forall y \near x^'-, z < y.
Proof.
move=> xz; rewrite nbhs_left0P; near do rewrite -ltrN2 opprB ltrBlDl.
by apply: nbhs_right_lt; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ge (x z : R) : z < x -> \forall y \near x^'-, z <= y.
Proof.
by move=> xz; near do apply/ltW; apply: nbhs_left_gt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ltBl (x : R) e : 0 < e -> \forall y \near x^'-, x - y < e.
Proof.
move=> e0; near=> y; rewrite -ltrBrDl ltrNl opprB; near: y.
by apply: nbhs_left_gt; rewrite ltrBlDr ltrDl.
Unshelve. all: by end_near. Qed.

Lemma not_near_at_leftP (p : R) (P : pred R) :
  ~ (\forall x \near p^'-, P x) <->
  forall e : {posnum R}, exists2 x : R, p - e%:num < x < p & ~ P x.
Proof.
rewrite -nbhs_right_leftP not_near_at_rightP; split => + e => /(_ e)[r pre Pr].
- by exists (- r) => //; rewrite ltrNr andbC ltrNl opprB addrC.
- by exists (- r) => /=; rewrite ?opprK// ltrN2 ltrNl opprD opprK andbC.
Qed.

Let fun_predC (T : choiceType) (f : T -> T) (p : pred T) : involutive f ->
  [set f x | x in p] = [set x | x in p \o f].
Proof.
by move=> fi; apply/seteqP; split => _/= [y hy <-];
  exists (f y) => //; rewrite fi.
Qed.

Lemma at_rightN (a : R) : (- a)^'+ = -%R @ a^'-.
Proof.
rewrite /at_right withinN [X in within X _](_ : _ = [set u | u < a])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

Lemma at_leftN (a : R) : (- a)^'- = -%R @ a^'+.
Proof.
rewrite /at_left withinN [X in within X _](_ : _ = [set u | a < u])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

End at_left_right.

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

Section at_left_right_pseudoMetricNormedZmod.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, `|x - y| <= e -> P y).
Proof.
rewrite nbhs0P/= near_withinE/= !near_simpl.
split.
  move => /nbhs_norm0P[/= _/posnumP[e] /(_ _) Px].
  apply/(@nbhs_norm0P R R^o).
  exists e%:num => //= r /= re yr y xyr; rewrite -[y](addrNK x) addrC.
  by apply: Px; rewrite /= distrC (le_lt_trans _ re)// gtr0_norm.
move => /(@nbhs_norm0P R R^o)[/= _/posnumP[e] /(_ _) Px].
apply/(@nbhs_norm0P R V).
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

End at_left_right_pseudoMetricNormedZmod.
Arguments cvgr_norm_lt {R V T F FF f}.
Arguments cvgr_norm_le {R V T F FF f}.
Arguments cvgr_norm_gt {R V T F FF f}.
Arguments cvgr_norm_ge {R V T F FF f}.
Arguments cvgr_neq0 {R V T F FF f}.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_right_gt] end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_left_lt] end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_right_neq] end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_left_neq] end : core.
#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_left_gt] end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_right_lt] end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_right_ge] end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_left_le] end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_right_ge] end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_left_le] end : core.

#[global] Hint Extern 0 (ProperFilter _^'-) =>
  (apply: at_left_proper_filter) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter _^'+) =>
  (apply: at_right_proper_filter) : typeclass_instances.

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

Lemma dense_set1C {R : realType} (r : R) : dense (~` [set r]).
Proof.
move=> /= O O0 oO.
suff [s Os /eqP sr] : exists2 s, O s & s != r by exists s; split.
case: O0 => o Oo.
have [->{r}|ro] := eqVneq r o; last by exists o => //; rewrite eq_sym.
have [e' /= e'0 e'o] := open_itvoo_subset oO Oo.
near (0:R)^'+ => e.
exists (o + e/2)%R; last by rewrite gt_eqF// ltrDl// divr_gt0.
apply: (e'o e) => //=.
  by rewrite sub0r normrN gtr0_norm.
rewrite in_itv/= !ltrD2l; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0%R) ?divr_ge0// ltrNl oppr0.
by rewrite gtr_pMr// invf_lt1// ltr1n.
Unshelve. all: by end_near. Qed.

Section pseudoMetricNormedZmod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).
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

End pseudoMetricNormedZmod_numFieldType.
Arguments cvgr_norm_lty {R V I F FF}.
Arguments cvgr_norm_ley {R V I F FF}.
Arguments cvgr_norm_gtNy {R V I F FF}.
Arguments cvgr_norm_geNy {R V I F FF}.

Section at_left_rightR.
Variable (R : numFieldType).

Lemma real_cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t < z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -(ltrD2r (- y)) real_ltr_normlW// ?rpredB//.
by near: x; apply: (@cvgr_distC_lt R R^o) => //; rewrite subr_gt0.
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
by near: x; apply: (@cvgr_dist_lt _ R^o) => //; rewrite subr_gt0.
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
rewrite (@nbhsr0P _ R^o) -propeqE; apply: eq_near => y /=.
by rewrite -propeqE; apply: eq_forall => z; rewrite ler_distlC.
Qed.

Lemma cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t < z.
Proof.
move=> Fy z zy; near=> x; rewrite -(ltrD2r (- y)) ltr_normlW//.
by near: x; apply: (@cvgr_distC_lt _ R^o) => //; rewrite subr_gt0.
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
by near: x; apply: (@cvgr_dist_lt _ R^o) => //; rewrite subr_gt0.
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

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Section continuous_within_itvP.
Context {R : realType}.
Implicit Type f : R -> R.

Let near_at_left (a : itv_bound R) b f eps : (a < BLeft b)%O -> 0 < eps ->
  {within [set` Interval a (BRight b)], continuous f} ->
  \forall t \near b^'-, normr (f b - f t) < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0) : (cf b).
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
move/continuous_withinNx/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0) : (cf a).
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
  split; [apply/in_continuous_mksetP|apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0 /=..].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by move: abf; exact/continuous_subspaceW/subset_itvW.
  - by apply: near_at_right => //; rewrite bnd_simp.
  - by apply: near_at_left => //; rewrite bnd_simp.
case=> ctsoo ctsL ctsR; apply/subspace_continuousP => x /andP[].
rewrite !bnd_simp/= !le_eqVlt => /predU1P[<-{x}|ax] /predU1P[|].
- by move/eqP; rewrite lt_eqF.
- move=> _; apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0 /=.
  move/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0): ctsL; rewrite /at_right !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  have : a <= c by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> ->; apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0 /=.
  move/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0): ctsR; rewrite /at_left !near_withinE.
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
  split; [apply/in_continuous_mksetP|apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?; rewrite /= !in_itv !andbT/= => /ltW.
  - by apply: near_at_right => //; rewrite bnd_simp.
move=> [cf fa]; apply/subspace_continuousP => x /andP[].
rewrite bnd_simp/= le_eqVlt => /predU1P[<-{x}|ax] _.
- apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0/=; move/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0) : fa.
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
  split; [apply/in_continuous_mksetP|apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?/=; rewrite !in_itv/=; exact: ltW.
  - by apply: near_at_left => //; rewrite bnd_simp.
move=> [cf fb]; apply/subspace_continuousP => x /andP[_].
rewrite bnd_simp/= le_eqVlt=> /predU1P[->{x}|xb].
- apply/(@cvgrPdist_lt _ R^o) => eps eps_gt0/=; move/(@cvgrPdist_lt _ R^o)/(_ _ eps_gt0) : fb.
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

Section cvg_composition_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> - f @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: oppr_continuous. Qed.

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

Lemma norm_cvg0P f : `|f x| @[x --> F] --> (0:K^o) <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_norm; rewrite normr0.
move=> f0; apply/cvgr0Pnorm_lt => e e_gt0.
by near do rewrite -normr_id; apply: (@cvgr0_norm_lt _ K^o).
Unshelve. all: by end_near. Qed.

Lemma norm_cvg0 f : `|f x| @[x --> F] --> (0:K^o) -> f @ F --> 0.
Proof. by rewrite norm_cvg0P. Qed.

End cvg_composition_pseudometric.

Section Closed_Ball.

Definition closed_ball_ (R : numDomainType) (V : zmodType) (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

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

Lemma closed_ball_closed (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : closed (closed_ball x r).
Proof. exact: closed_closure. Qed.

Lemma subset_closed_ball (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : ball x r `<=` closed_ball x r.
Proof. exact: subset_closure. Qed.

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

End Closed_Ball.

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
Proof.
move=> ?; apply: cvg_lim.
  exact: (@norm_hausdorff K K^o).
exact: cvg_norm.
Qed.

End limit_composition_pseudometric.

Section domination.
Context {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}.

Definition dominated_by (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by (h : T -> V) (k : K) (f : T -> W)
    (F : set_system T) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (h : T -> V) (k : K) (F G : set_system T) : F `=>` G ->
  (dominated_by h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

End domination.

Lemma sub_dominatedr (T : Type) (K : numDomainType)
    (V : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set_system T) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Section ex_dom_bound.
Context {T : Type} {K : numFieldType} {V W : pseudoMetricNormedZmodType K}.

Lemma ex_dom_bound (h : T -> V) (f : T -> W) (F : set_system T)
    {PF : ProperFilter F} :
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

Lemma ex_strict_dom_bound (h : T -> V) (f : T -> W) (F : set_system T)
    {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pM2r ?normr_gt0// ltrDl.
Qed.

End ex_dom_bound.

Definition bounded_near {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Notation "[ 'bounded' E | x 'in' A ]" :=
  (bounded_near (fun x => E) (globally A)).
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Definition fun1 {T : Type} {K : numFieldType} : T -> K^o := fun=> 1.
Arguments fun1 {T K} x /.

Section bounded_near.
Context {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma sub_boundedr (F G : set_system T) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Proof. by move=> FG f; rewrite /bounded_near; apply: filterS=> M; apply: FG. Qed.

Lemma sub_boundedl (f g : T -> V) (F : set_system T) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Proof.
move=> le_fg; rewrite /bounded_near; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_strict_bound_gt0 (f : T -> V) (F : set_system T) {PF : Filter F} :
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltrDl.
Qed.

Lemma dominated_by1 :
  @dominated_by T K K^o V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma boundedE :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma strictly_dominated_by1 :
  @strictly_dominated_by T K K^o V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_bound (f : T -> V) (F : set_system T) {PF : ProperFilter F} :
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound (f : T -> V) (F : set_system T) {PF : ProperFilter F} :
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Unshelve. all: by end_near. Qed.

End bounded_near.

Section cvg_bounded.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma cvg_bounded {I} {F : set_system I} {FF : Filter F} (f : I -> V) (y : V) :
  f @ F --> y -> bounded_near f F.
Proof. exact: cvgr_norm_ley. Qed.

End cvg_bounded.
Arguments cvg_bounded {R V I F FF}.

Lemma bounded_cst (K : numFieldType) {V : pseudoMetricNormedZmodType K}
  (k : V) T (A : set T) : [bounded k | _ in A].
Proof.
rewrite /bounded_near; near=> M => t At /=.
by near: M; exact: nbhs_pinfty_ge.
Unshelve. all: end_near. Qed.

Lemma bounded_fun_has_ubound (T : Type) (R : realFieldType) (a : T -> R^o) :
  bounded_fun a -> has_ubound (range a).
Proof.
move=> [M [Mreal]]/(_ (`|M| + 1)).
rewrite (le_lt_trans (ler_norm _)) ?ltrDl// => /(_ erefl) aM.
by exists (`|M| + 1) => _ [n _ <-]; rewrite (le_trans (ler_norm _))// aM.
Qed.

Lemma bounded_funN (T : Type) (R : realFieldType) (a : T -> R^o) :
  bounded_fun a -> bounded_fun (- a).
Proof.
move=> [M [Mreal aM]]; rewrite /bounded_fun /bounded_near; near=> x => y /= _.
by rewrite normrN; apply: aM.
Unshelve. all: by end_near. Qed.

Lemma bounded_fun_has_lbound (T : Type) (R : realFieldType) (a : T -> R^o) :
  bounded_fun a -> has_lbound (range a).
Proof.
move=> /bounded_funN/bounded_fun_has_ubound ba; apply/has_lb_ubN.
by apply: subset_has_ubound ba => _ [_ [n _] <- <-]; exists n.
Qed.

Lemma bounded_funD (T : Type) (R : realFieldType) (a b : T -> R^o) :
  bounded_fun a -> bounded_fun b -> bounded_fun (a \+ b).
Proof.
move=> [M [Mreal Ma]] [N [Nreal Nb]].
rewrite /bounded_fun/bounded_near; near=> x => y /= _.
rewrite (le_trans (ler_normD _ _))// [x]splitr.
by rewrite lerD// (Ma, Nb)// ltr_pdivlMr//;
   near: x; apply: nbhs_pinfty_gt; rewrite ?rpredM ?rpred_nat.
Unshelve. all: by end_near. Qed.
