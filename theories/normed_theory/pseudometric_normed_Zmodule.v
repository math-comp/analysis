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
(* ```                                                                        *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   Abelian group equipped with a norm       *)
(*                                   The HB class is PseudoMetricNormedZmod.  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record NormedZmod_PseudoMetric_eq (R : numDomainType) T
    of Num.NormedZmodule R T & PseudoPointedMetric R T := {
  pseudo_metric_ball_norm : ball = ball_ (fun x : T => `| x |)
}.

#[short(type="pseudoMetricNormedZmodType")]
HB.structure Definition PseudoMetricNormedZmod (R : numDomainType) :=
  {T of Num.NormedZmodule R T & PseudoMetric R T
   & NormedZmod_PseudoMetric_eq R T & isPointed T}.

Section pseudoMetricNormedZmod_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

(** balls defined by the norm: *)
Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by rewrite pseudo_metric_ball_norm. Qed.

End pseudoMetricNormedZmod_lemmas.

Section PseudoMetricNormedZmod_numDomainType.
Variables (R : numDomainType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_ball := (@nbhs_ball _ V).

(** neighborhoods defined by the norm: *)
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
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : V -> Prop) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : V -> Prop) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : V -> Prop) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num => /=. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
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

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
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

End PseudoMetricNormedZmod_numDomainType.
#[global] Hint Resolve normr_ge0 : core.
Arguments cvgr_dist_lt {_ _ _ F FF}.
Arguments cvgr_distC_lt {_ _ _ F FF}.
Arguments cvgr_dist_le {_ _ _ F FF}.
Arguments cvgr_distC_le {_ _ _ F FF}.
Arguments cvgr0_norm_lt {_ _ _ F FF}.
Arguments cvgr0_norm_le {_ _ _ F FF}.

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

Section PseudoMetricNormedZMod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff_space V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num.
  by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltrD acr bcr); rewrite -r22 (distrC b c).
move/(le_lt_trans (ler_distD c a b)).
by rewrite -mulrA mulVr ?mulr1 ?ltxx // unitfE.
Qed.
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

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

End PseudoMetricNormedZMod_numFieldType.

(* TODO: generalize to R : numFieldType *)
Section hausdorff.

Lemma pseudoMetricNormedZModType_hausdorff (R : realFieldType)
    (V : pseudoMetricNormedZmodType R) :
  hausdorff_space V.
Proof.
move=> p q clp_q; apply/subr0_eq/normr0_eq0/Rhausdorff => A B pq_A.
rewrite -(@normr0 _ V) -(subrr p) => pp_B.
suff loc_preim r C : nbhs`|p - r| C ->
    nbhs r ((fun r => `|p - r|) @^-1` C).
  have [r []] := clp_q _ _ (loc_preim _ _ pp_B) (loc_preim _ _ pq_A).
  by exists `|p - r|.
move=> [e egt0 pre_C]; apply: nbhs_le_nbhs_norm; exists e => //= s /= rse.
apply: pre_C; apply: le_lt_trans (ler_dist_dist _ _) _.
by rewrite opprB addrC subrKA distrC.
Qed.

End hausdorff.

Section prod_PseudoMetricNormedZmodule.
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

End prod_PseudoMetricNormedZmodule.

Section matrix_PseudoMetricNormedZmodule.
Variables (K : numFieldType) (m n : nat).

Local Lemma ball_gt0 (x y : 'M[K]_(m.+1, n.+1)) e : ball x e y -> 0 < e.
Proof. by move/(_ ord0 ord0); apply: le_lt_trans. Qed.

Lemma mx_norm_ball : @ball _ 'M[K]_(m.+1, n.+1) = ball_ (fun x => `| x |).
Proof.
rewrite /normr /ball_ predeq3E => x e y /=; rewrite mx_normE; split => xey.
- have e_gt0 : 0 < e := ball_gt0 xey.
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0 xey.
  rewrite num_lt; apply/bigmax_ltP => /=.
  by rewrite -num_lt /=; split => // -[? ?] _; rewrite !mxE; exact: xey.
- have e_gt0 : 0 < e by rewrite (le_lt_trans _ xey).
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0.
  move=> /(bigmax_ltP _ _ _ (fun _ => _%:itv)) /= [e0 xey] i j.
  by move: (xey (i, j)); rewrite !mxE; exact.
Qed.

HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build K 'M[K]_(m.+1, n.+1) mx_norm_ball.

End matrix_PseudoMetricNormedZmodule.
