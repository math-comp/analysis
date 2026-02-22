(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import interval_inference reals real_interval.
From mathcomp Require Import topology_structure.
From mathcomp Require Import uniform_structure pseudometric_structure.
From mathcomp Require Import order_topology matrix_topology.

(**md**************************************************************************)
(* # Topological notions for numerical types                                  *)
(*                                                                            *)
(* We endow `numFieldType` with the types of topological notions (accessible  *)
(* with `Import numFieldTopology.Exports`).                                   *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.instance Definition _ (R : numDomainType) := hasNbhs.Build R^o
  (nbhs_ball_ (ball_ (fun x => `|x|))).

Module TopologicalNumDomainType.
Section TopologicalNumDomainType.
Variable (R : numDomainType).

Lemma nbhs_filter (p : R^o) : ProperFilter (nbhs p).
Proof.
split.
  by move=> [] e e0 /subsetP/(_ p); rewrite !in_setE/= subrr normr0.
split=> [|P Q|P Q].
- by exists 1; [exact: ltr01|exact: subsetT].
- move=> [] /= e e0 /subsetP eP [] /= f f0 /subsetP fQ.
  exists (Order.min e f) => /=.
    by rewrite [Num.min e f]/(Order.min e f); case: ifP.
  apply/subsetP => x.
  rewrite in_setE in_setI/= => pef.
  apply/andP; split.
    apply/eP/mem_set/(lt_le_trans pef).
    by case: (@real_ltP _ e f) => //; exact: gtr0_real.
  apply/fQ/mem_set/(lt_le_trans pef).
  by case: (@real_ltP _ f e) => //; exact: gtr0_real.
- move=> PQ [] /= e e0 eP.
  by exists e => //; exact: (subset_trans eP).
Qed.

Lemma nbhs_singleton (p : R^o) (A : set R) : nbhs p A -> A p.
Proof.
move=> [] /= e e0 /subsetP /(_ p).
by rewrite !in_setE/= subrr normr0 e0 => /(_ erefl).
Qed.

Lemma nbhs_nbhs (p : R^o) (A : set R) : nbhs p A -> nbhs p (nbhs^~ A).
Proof.
move=> [] /= e e0 /subsetP eA; exists e => //.
apply/subsetP => x /[!inE]/= xe.
exists (e - `|p - x|); first by rewrite /= subr_gt0.
apply/subsetP => y; rewrite inE/= ltrBrDl => ye.
apply/eA/mem_set => /=.
by rewrite -(subrK x p) -addrA (le_lt_trans (ler_normD _ _)).
Qed.

End TopologicalNumDomainType.

End TopologicalNumDomainType.

HB.instance Definition _ (R : numDomainType) := Nbhs_isNbhsTopological.Build R^o
  (@TopologicalNumDomainType.nbhs_filter R)
  (@TopologicalNumDomainType.nbhs_singleton R)
  (@TopologicalNumDomainType.nbhs_nbhs R).

HB.instance Definition _ (R : numFieldType) := Nbhs_isPseudoMetric.Build R R^o
  nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

HB.instance Definition _ (R : numFieldType) :=
  Uniform_isPseudoMetric.Build R R^o
    ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma real_order_nbhsE (R : realFieldType) (x : R^o) : nbhs x =
  filter_from (fun i => itv_open_ends i /\ x \in i) (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U.
  case => _ /posnumP[e] xeU.
  exists (`]x - e%:num, x + e%:num[); first split => //.
    by rewrite in_itv/= -lter_distl subrr normr0.
  apply: subset_trans xeU => z /=.
  by rewrite in_itv /= -lter_distl distrC.
case => [][[[]l|[]]] [[]r|[]] []//= _.
- move=> xlr lrU; exists (Order.min (x - l) (r - x)).
    by rewrite /= lt_min ?lterBDr ?add0r ?(itvP xlr).
  apply/(subset_trans _ lrU)/subset_ball_prop_in_itv.
  suff : (`]x - Order.min (x - l) (r - x), x + Order.min (x - l) (r - x)[
          <= `]l, r[)%O by move/subitvP => H ? ?; exact: H.
  rewrite subitvE 2!lteBSide/=.
  by rewrite lerBrDl [_ + l]addrC -2!lerBrDl 2!ge_min 2!lexx orbT.
- move=> xl lU; exists (x - l) => /=; first by rewrite lterBDr add0r (itvP xl).
  apply/(subset_trans _ lU)/subset_ball_prop_in_itv.
  suff : (`]x - (x - l), x + (x - l)[ <= `]l, +oo[)%O.
    by move/subitvP => + ?; exact.
  by rewrite subitvE lteBSide/= subKr lexx.
- move=> xr rU; exists (r - x) => /=; first by rewrite lterBDr add0r (itvP xr).
  apply/(subset_trans _ rU)/subset_ball_prop_in_itv.
  suff : (`]x - (r - x), x + (r - x)[ <= `]-oo, r[)%O.
    by move/subitvP => + ?; exact.
  by rewrite subitvE lteBSide/= addrC subrK.
- by move=> _; rewrite set_itvE subTset => ->; exists 1 => /=.
Qed.

Module numFieldTopology.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : rcfType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : archiRealFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numClosedFieldType) :=
  PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) :=
  Order_isNbhs.Build _ R (@real_order_nbhsE R).

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realType) :=
  Order_isNbhs.Build _ R (@real_order_nbhsE R).

Module Exports. HB.reexport. End Exports.

End numFieldTopology.
Import numFieldTopology.Exports.

Reserved Notation "x ^'+" (at level 3, left associativity, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, left associativity, format "x ^'-").

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

(* NB: In not_near_at_rightP, R has type numFieldType.
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

Lemma closure_sup (R : realType) (A : set R) :
  A !=set0 -> has_ubound A -> closure A (sup A).
Proof.
move=> A0 ?; have [|AsupA] := pselect (A (sup A)); first exact: subset_closure.
rewrite closure_isolated_limit_point.
right => U /nbhs_ballP[_ /posnumP[e]] supAeU.
suff [x [Ax /andP[sAex xsA]]] : exists x, A x /\ sup A - e%:num < x < sup A.
  exists x; split => //; first by rewrite lt_eqF.
  apply supAeU; rewrite /ball /= ltr_distl (addrC x e%:num) -ltrBlDl sAex.
  by rewrite andbT (le_lt_trans _ xsA) // lerBlDl lerDr.
apply: contrapT => /forallNP Ax.
suff /(ge_sup A0) : ubound A (sup A - e%:num).
  by rewrite leNgt => /negP; apply; rewrite ltrBlDl ltrDr.
move=> y Ay; have /not_andP[//|/negP] := Ax y.
rewrite negb_and leNgt => /orP[//|]; apply: contra => sAey.
rewrite lt_neqAle sup_upper_bound // andbT.
by apply: contra_not_neq AsupA => <-.
Qed.

Lemma right_bounded_interior (R : realType) (X : set R) :
  has_ubound X -> X° `<=` [set r | r < sup X].
Proof.
move=> uX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP supXr|]; last first.
  by apply/negP; rewrite -leNgt ub_le_sup//; exact: interior_subset.
suff : ~ X° (sup X) by rewrite supXr.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (sup X + f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprD addNKr normrN.
  by rewrite gtr0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
have : sup X + f%:num <= sup X by exact: ub_le_sup.
by apply/negP; rewrite -ltNge; rewrite ltrDl.
Qed.

Lemma left_bounded_interior (R : realType) (X : set R) :
  has_lbound X -> X° `<=` [set r | inf X < r].
Proof.
move=> lX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP rinfX|]; last first.
  by apply/negP; rewrite -leNgt ge_inf//; exact: interior_subset.
suff : ~ X° (inf X) by rewrite -rinfX.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (inf X - f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprB addrC subrK.
  by rewrite gtr0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
have : inf X <= inf X - f%:num by exact: ge_inf.
by apply/negP; rewrite -ltNge; rewrite ltrBlDr ltrDl.
Qed.

Lemma nbhsN {R : numFieldType} (x : R) : nbhs (- x) = -%R @ x.
Proof.
rewrite predeqE => A; split=> //= -[] e e_gt0 xeA; exists e => //= y /=.
  by move=> ?; apply: xeA => //=; rewrite -opprD normrN.
by rewrite -opprD normrN => ?; rewrite -[y]opprK; apply: xeA; rewrite /= opprK.
Qed.

Lemma cvg_compNP {T : topologicalType} {R : numFieldType} (f : R -> T) (a : R)
    (l : T) :
  (f \o -%R) x @[x --> a] --> l <-> f x @[x --> (- a)] --> l.
Proof. by rewrite nbhsN. Qed.

Lemma nbhsNimage {R : numFieldType} (x : R) :
  nbhs (- x) = [set -%R @` A | A in nbhs x].
Proof.
rewrite nbhsN /fmap/=; under eq_set => A do rewrite preimageEinv//= inv_oppr.
by rewrite (eq_imageK opprK opprK).
Qed.

Lemma nearN {R : numFieldType} (x : R) (P : R -> Prop) :
  (\forall y \near - x, P y) <-> \near x, P (- x).
Proof. by rewrite -[X in X <-> _]near_simpl nbhsN. Qed.

Lemma openN {R : numFieldType} (A : set R) : open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior nbhsNimage; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK nbhsNimage; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

Lemma dnbhsN {R : numFieldType} (r : R) :
  (- r)%R^' = (fun A => -%R @` A) @` r^'.
Proof.
apply/seteqP; split=> [A [e/= e0 reA]|_/= [A [e/= e0 reA <-]]].
  exists (-%R @` A).
    exists e => // x/= rxe xr; exists (- x)%R; rewrite ?opprK//.
    by apply: reA; rewrite ?eqr_opp//= opprK addrC distrC.
  rewrite image_comp (_ : _ \o _ = idfun) ?image_id// funeqE => x/=.
  by rewrite opprK.
exists e => //= x/=; rewrite -opprD normrN => axe xa.
exists (- x)%R; rewrite ?opprK//; apply: reA; rewrite ?eqr_oppLR//=.
by rewrite opprK.
Qed.

Lemma withinN {R : numFieldType} (A : set R) (r : R) :
  within A (nbhs (- r)) = - x @[x --> within (-%R @` A) (nbhs r)].
Proof.
rewrite eqEsubset /=; split; move=> E /= [e e0 reE]; exists e => //.
  move=> s rse sA; apply: reE; last by rewrite memNE opprK.
  by rewrite /= opprK addrC distrC.
move=> s res rs; rewrite -(opprK s); apply: reE; last by rewrite -memNE.
by rewrite /= opprK -normrN opprD.
Qed.

Lemma in_continuous_mksetP {T : realFieldType} {U : nbhsType}
    (i : interval T) (f : T -> U) :
  {in i, continuous f} <-> {in [set` i], continuous f}.
Proof.
by split => [fi x /set_mem/=|fi x xi]; [exact: fi|apply: fi; rewrite inE].
Qed.

Lemma nbhs0_ltW (R : realFieldType) (x : R) : (0 < x)%R ->
 \forall r \near nbhs (0%R:R), (r <= x)%R.
Proof.
exists x => // y; rewrite /ball/= sub0r normrN => /ltW.
by apply: le_trans; rewrite ler_norm.
Qed.

Lemma nbhs0_lt (R : realFieldType) (x : R) : (0 < x)%R ->
 \forall r \near nbhs (0%R:R), (r < x)%R.
Proof.
exists x => // z /=; rewrite sub0r normrN.
by apply: le_lt_trans; rewrite ler_norm.
Qed.

Lemma lt_nbhsl {R : realType} (x a : R) : x < a ->
  \forall y \near nbhs x, y < a.
Proof.
move=> xb; exists ((a - x) / 2) => /=; first by rewrite divr_gt0// subr_gt0.
move=> r/=; rewrite ltr_pdivlMr// ltrBrDr; apply: le_lt_trans.
by rewrite -lerBlDr -normrN opprB (le_trans (ler_norm _))// ler_peMr// ler1n.
Qed.

Lemma Nlt_nbhsl {R : realType} (x a : R) :
  - x < a -> \forall y \near nbhs x, - y < a.
Proof.
move=> xb; exists ((a + x) / 2) => /=.
  by rewrite divr_gt0// -(opprK x) subr_gt0.
move=> r/=; rewrite ltr_pdivlMr// -ltrBlDr; apply: le_lt_trans.
by rewrite -lerBlDr opprK addrC (le_trans (ler_norm _))// ler_peMr// ler1n.
Qed.

Section nbhs_lt_le.
Context {R : numFieldType}.
Implicit Types x z : R.

Lemma lt_nbhsl_lt x z : x < z -> \forall y \near x, x <= y -> y < z.
Proof.
move=> xz; near=> y.
rewrite le_eqVlt => /predU1P[<-//|].
near: y; exists (z - x) => /=; first by rewrite subr_gt0.
move=> y/= /[swap] xy; rewrite ltr0_norm ?subr_lt0//.
by rewrite opprD addrC ltrBlDr subrK opprK.
Unshelve. all: by end_near. Qed.

Lemma lt_nbhsl_le x z : x < z -> \forall y \near x, x <= y -> y <= z.
Proof.
by move=> xz; apply: filterS (lt_nbhsl_lt xz) => y /[apply] /ltW.
Qed.

End nbhs_lt_le.
#[deprecated(since="mathcomp-analysis 1.9.0", note="use `lt_nbhsl_lt` instead")]
Notation nbhs_lt := lt_nbhsl_lt (only parsing).
#[deprecated(since="mathcomp-analysis 1.9.0", note="use `lt_nbhsl_le` instead")]
Notation nbhs_le := lt_nbhsl_le (only parsing).

Lemma lt_nbhsr {R : realFieldType} (a z : R) : a < z ->
  \forall x \near z, a < x.
Proof.
rewrite -subr_gt0 => za0; exists (z - a) => //= u/=.
rewrite ltrBrDl addrC -ltrBrDl => /lt_le_trans; apply.
rewrite lerBlDl.
have [uz|uz] := leP u z.
  by rewrite ger0_norm ?subr_ge0// subrK.
by rewrite ltr0_norm ?subr_lt0// opprB addrAC -lerBlDr opprK lerD// ?ltW.
Qed.

Global Instance Proper_dnbhs_regular_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last by rewrite addrC -subr_eq0 addrK.
by rewrite /ball /= opprD addNKr normrN ger0_norm// [ltRHS]splitr ltr_pwDl.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last by rewrite addrC -subr_eq0 addrK.
by rewrite /ball /= opprD addNKr normrN ger0_norm// [ltRHS]splitr ltr_pwDl.
Qed.

Lemma dense_rat (R : realType) : dense (@ratr R @` setT).
Proof.
move=> A [r Ar]; rewrite openE => /(_ _ Ar)/nbhs_ballP[_/posnumP[e] reA].
have /rat_in_itvoo[q /itvP qre] : r < r + e%:num by rewrite ltrDl.
exists (ratr q) => //; split; last by exists q.
apply: reA; rewrite /ball /= distrC ltr_distl qre andbT.
by rewrite (@le_lt_trans _ _ r)// ?qre// lerBlDl lerDr ltW.
Qed.

Lemma separated_open_countable
    {R : realType} (I : Type) (B : I -> set R) (D : set I) :
    (forall i, open (B i)) -> (forall i, B i !=set0) ->
  trivIset D B -> countable D.
Proof.
move=> oB B0 tB; have [f fB] :
    {f : I -> rat & forall i, D i -> B i (ratr (f i))}.
  apply: (@choice _ _ (fun x y => D x -> B x (ratr y))) => i.
  have [r [Bir [q _ qr]]] := dense_rat (B0 _) (oB i).
  by exists q => Di; rewrite qr.
have inj_f : {in D &, injective f}.
  move=> i j /[!inE] Di Dj /(congr1 ratr) ratrij.
  have ? : (B i `&` B j) (ratr (f i)).
    by split => //; [exact: fB|rewrite ratrij; exact: fB].
  by apply/(tB _ _ Di Dj); exists (ratr (f i)).
apply/pcard_injP; have /card_bijP/cid[g bijg] := card_rat.
pose nat_of_rat (q : rat) : nat := set_val (g (to_setT q)).
have inj_nat_of_rat : injective nat_of_rat.
  rewrite /nat_of_rat; apply: inj_comp => //; apply: inj_comp => //.
  exact/bij_inj.
by exists (nat_of_rat \o f) => i j Di Dj /inj_nat_of_rat/inj_f; exact.
Qed.

Lemma continuous_rsubmx {R : numFieldType} m {n1 n2} :
  continuous (rsubmx : 'M[R]_(m, n1 + n2) -> 'M[R]_(m, n2)).
Proof.
move=> u A /nbhs_ballP[e /= e0 eA].
apply/nbhs_ballP; exists e => //= v [_ uv]; apply: eA; split => // i j.
by apply: (le_lt_trans _ (uv i (rshift n1 j))); rewrite !mxE.
Qed.

Lemma continuous_lsubmx {R : numFieldType} m {n1 n2} :
  continuous (lsubmx : 'M[R]_(m, n1 + n2) -> 'M[R]_(m, n1)).
Proof.
move=> u A /nbhs_ballP[e /= e0 eA].
apply/nbhs_ballP; exists e => //= v [_ uv]; apply: eA; split => // i j.
by apply: (le_lt_trans _ (uv i (lshift n2 j))); rewrite !mxE.
Qed.

(* An internal theory prepared for the next section (realField_topology).     *)
(* This module itself is all about order_topology and says nothing specific   *)
(* to num_topology.                                                           *)
Module EndlessDenseOrderTopologyTheory.
Import unstable.EndlessDenseOrderTheory.

Section theory.

Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Context {d} {T : orderTopologicalType d}.
Implicit Types x y : T.

Lemma open_itv_open_ends (i : interval T) :
  is_endless_porderType T -> is_dense_porderType T -> neitv i ->
  open [set` i] -> itv_open_ends i.
Proof.
move=> T_endless T_dense.
case: i => l r /neitv_lt_bnd/= lr.
rewrite openE /interior/=.
(under [X in X -> _]eq_forall do rewrite itv_nbhsE/=) => i_open.
apply/negbNE/negP; case/(itv_open_endsPn lr) => x lrx.
have: x \in Interval l r.
  move: lr; case: lrx => ->; rewrite itv_boundlr lexx ?leBRight_ltBLeft//.
  by rewrite ltBRight_leBLeft => ->.
case/i_open => -[l' r'] [] + xj; rewrite -subset_itvP => /[swap].
have := xj; rewrite itv_boundlr => /andP[l'x xr'].
rewrite -subitvP//; last exact: xj.
rewrite subitvE => /andP[] ll' r'r.
apply/negP/itv_open_endsPn; [exact: (itv_boundlr_lt xj) | exists x].
move: l'x xr' ll' r'r.
by case: lrx => <-; [left|right]; apply/le_anti/andP; split.
Qed.

Lemma closed_itv_closed_ends (i : interval T) :
  is_endless_porderType T -> is_dense_porderType T -> neitv i ->
  closed [set` i] -> itv_closed_ends i.
Proof.
move=> T_endless T_dense.
case: i => l r /neitv_lt_bnd/= lr.
rewrite closedE/= /prop_near1/=.
(under [X in X -> _]eq_forall do rewrite itv_nbhsE/=) => i_closed.
apply/negbNE/negP; case/(itv_closed_endsPn lr) => x lrx.
have: ~ (x \in Interval l r).
  by case: lrx => ->; rewrite itv_boundlr !bnd_simp// andbF.
apply; apply: i_closed => -[[l' r'][]] /itv_open_ends_boundlr -> /andP[] l'x xr'.
move: lr; case: lrx => -> => [xr|lx].
  have : BRight x < Order.min r r' by rewrite lt_min xr xr'.
  case/itv_bound_half_dense => // y /andP[] xy yr /(_ y); apply.
    rewrite /= itv_boundlr.
    have := yr; rewrite lt_min -!leBRight_ltBLeft => /andP[] _ ->.
    by rewrite andbT (le_trans _ xy)// ltW// ltBRight_leBLeft ltW.
  rewrite itv_boundlr xy/= leBRight_ltBLeft.
  by have := yr; rewrite lt_min => /andP[].
have : Order.max l l' < BLeft x by rewrite gt_max lx l'x.
case/itv_bound_half_dense => // y /andP[] ly yx /(_ y); apply.
  rewrite /= itv_boundlr.
  have := ly; rewrite ge_max => /andP[] _ -> /=.
  by rewrite leBRight_ltBLeft (lt_trans yx)// -leBRight_ltBLeft ltW.
rewrite itv_boundlr leBRight_ltBLeft yx andbT.
by have := ly; rewrite ge_max => /andP[].
Qed.

Let itvoo_closureE (x y : T) :
  is_endless_porderType T -> is_dense_porderType T -> neitv `]x, y[%O ->
  closure `]x, y[ = `[x, y].
Proof.
move=> T_endless T_dense /neitv_lt_bnd/= /[!bnd_simp] xy.
have ineq0 bb1 bb2 : neitv (Interval (BSide bb1 x) (BSide bb2 y)).
  have[z /andP[xz zy]]:= T_dense x y xy.
  apply/set0P; exists z; rewrite /= in_itv/=.
  by case: bb1; case: bb2; apply/andP; split; rewrite /= ?ltW.
have subcc : `]x, y[ `<=` `[x, y] by apply: subset_itv; rewrite !bnd_simp.
apply/seteqP; split.
  by rewrite (closure_id `[x, y]).1; [exact: closure_subset|exact: itv_closed].
rewrite (closureEbigcap_itvcc `[x, y])//; last exact: itv_closed.
rewrite setorder_itv_setDl_image// setDitvoo//.
rewrite powerset2 !image_setU !image_set1 setD0 setDitv1l setDitv1r setDitv2.
rewrite setIC !setIUl => /= z ? i -[[[]|]|] []->// ci.
all: exfalso; move/closed_itv_closed_ends: ci.
all: cbn; rewrite falseE; apply => //.
all: exact: ineq0.
Qed.

Lemma fin_itv_closureE (x y : T) b1 b2 :
  is_endless_porderType T -> is_dense_porderType T ->
  neitv (Interval (BSide b1 x) (BSide b2 y)) ->
  closure [set` Interval (BSide b1 x) (BSide b2 y)] = `[x, y].
Proof.
move=> T_endless T_dense /neitv_lt_bnd/=  bxy.
have : x <= y by move: bxy; case: b1; case: b2; rewrite bnd_simp// => /ltW.
rewrite le_eqVlt => /orP[/eqP xy| xy].
  move: b1 b2 bxy; rewrite xy => -[][]; rewrite !bnd_simp// => _.
  by rewrite -((closure_id `[y,y]).1)//; exact: itv_closed.
apply/seteqP; split.
  rewrite (closure_id `[x, y]).1; last exact: itv_closed.
  by apply/closure_subset/subset_itv; rewrite !bnd_simp.
rewrite -itvoo_closureE//.
  by apply/closure_subset/subset_itv; rewrite !bnd_simp.
have[z /andP[xz zy]]:= T_dense x y xy.
by apply/set0P; exists z; rewrite /= in_itv/= xz zy.
Qed.

Let itvoy_closureE (x : T) :
  is_endless_porderType T -> is_dense_porderType T ->
  closure `]x, +oo[ = `[x, +oo[.
Proof.
move=> T_endless T_dense.
have subcy : `]x, +oo[ `<=` `[x, +oo[.
  by apply: subset_itv => //; rewrite !bnd_simp.
apply/seteqP; split.
  rewrite (closure_id `[x, +oo[).1; first exact: closure_subset.
  exact: rray_closed.
rewrite (closureEbigcap_itvcc `[x, +oo[)//; last exact: rray_closed.
rewrite setorder_itv_setDl_image// setDcitvy; last first.
  by apply/set0P; exists x; rewrite /= in_itv/= lexx.
rewrite powerset1 image_setU !image_set1 setD0 setDitv1l setIC setIUl.
move=> /= z/= zx /= i [] [] -> // ci; exfalso.
move/closed_itv_closed_ends: ci; cbn; rewrite falseE; apply => //.
have[_ [y xy]]:= T_endless x.
by apply/set0P; exists y; rewrite /= in_itv/= xy.
Qed.

Lemma rinfty_itv_closureE (x : T) b :
  is_endless_porderType T -> is_dense_porderType T ->
  closure [set` Interval (BSide b x) +oo] = `[x, +oo[.
Proof.
move=> T_endless T_dense.
have subcy: [set` Interval (BSide b x) +oo] `<=` `[x, +oo[.
  by apply: subset_itv => //; rewrite !bnd_simp.
apply/seteqP; split.
  rewrite (closure_id `[x, +oo[).1; first exact: closure_subset.
  exact: rray_closed.
rewrite -itvoy_closureE//.
by apply/closure_subset/subset_itv => //; rewrite !bnd_simp.
Qed.

Let itvNyo_closureE (x : T) :
  is_endless_porderType T -> is_dense_porderType T ->
  closure `]-oo, x[ = `]-oo, x].
Proof.
move=> T_endless T_dense.
have subcy : `]-oo, x[ `<=` `]-oo, x].
  by apply: subset_itv => //; rewrite !bnd_simp.
apply/seteqP; split.
  rewrite (closure_id `]-oo, x]).1; first exact: closure_subset.
  exact: lray_closed.
rewrite (closureEbigcap_itvcc `]-oo, x])//; last exact: lray_closed.
rewrite setorder_itv_setDl_image// setDcitvNy; last first.
  by apply/set0P; exists x; rewrite /= in_itv/= lexx.
rewrite powerset1 image_setU !image_set1 setD0 setDitv1r setIC setIUl.
move=> /= z/= zx /= i [] [] -> // ci; exfalso.
move/closed_itv_closed_ends: ci; cbn; rewrite falseE; apply => //.
have[[y yx] _]:= T_endless x.
by apply/set0P; exists y; rewrite /= in_itv/= yx.
Qed.

Lemma linfty_itv_closureE (x : T) b :
  is_endless_porderType T -> is_dense_porderType T ->
  closure [set` Interval -oo (BSide b x)] = `]-oo, x].
Proof.
move=> T_endless T_dense.
have subNyc: [set` Interval -oo (BSide b x)] `<=` `]-oo, x].
  by apply: subset_itv => //; rewrite !bnd_simp.
apply/seteqP; split.
  rewrite (closure_id `]-oo, x]).1; first exact: closure_subset.
  exact: lray_closed.
rewrite -itvNyo_closureE//.
by apply/closure_subset/subset_itv => //; rewrite !bnd_simp.
Qed.

Lemma rinfty_itv_interiorE (x : T) b :
  is_endless_porderType T -> is_dense_porderType T ->
  [set` Interval (BSide b x) +oo]° = `]x, +oo[.
Proof.
move=> T_endless T_dense.
by apply: setC_inj; rewrite -closure_setC !setCitvr linfty_itv_closureE.
Qed.

Lemma linfty_itv_interiorE (x : T) b :
  is_endless_porderType T -> is_dense_porderType T ->
  [set` Interval -oo (BSide b x)]° = `]-oo, x[.
Proof.
move=> T_endless T_dense.
by apply: setC_inj; rewrite -closure_setC !setCitvl rinfty_itv_closureE.
Qed.

Lemma fin_itv_interiorE (x y : T) b1 b2 :
  is_endless_porderType T -> is_dense_porderType T ->
  [set` Interval (BSide b1 x) (BSide b2 y)]° = `]x, y[.
Proof.
move=> T_endless T_dense.
apply: setC_inj.
rewrite -closure_setC !setCitv/= closureU.
by rewrite linfty_itv_closureE// rinfty_itv_closureE.
Qed.

Lemma itv_closureE (l r : itv_bound T) :
  is_endless_porderType T -> is_dense_porderType T -> neitv (Interval l r) ->
  closure [set` Interval l r] =
    [set` Interval
        (match l with BSide _ x => BLeft x  | BInfty _ => l end)
        (match r with BSide _ y => BRight y | BInfty _ => r end)].
Proof.
move=> T_endless T_dense.
case: l => [b1 x | b1]; case: r => [b2 y | b2]; case: b1; case: b2 => ineq0.
all: rewrite ?set_itv_infty_set0 ?closure0//.
all: rewrite ?set_itvNyy ?closureT//.
all: by rewrite (fin_itv_closureE, rinfty_itv_closureE, linfty_itv_closureE).
Qed.

Lemma itv_interiorE (l r : itv_bound T) :
  is_endless_porderType T -> is_dense_porderType T ->
  [set` Interval l r]° =
    [set` Interval
        (match l with BSide _ x => BRight x  | BInfty _ => l end)
        (match r with BSide _ y => BLeft y | BInfty _ => r end)].
Proof.
move=> T_endless T_dense.
case: l => [b1 x | b1]; case: r => [b2 y | b2]; case: b1; case: b2.
all: rewrite ?set_itv_infty_set0 ?interior0//.
all: rewrite ?set_itvNyy ?interiorT//.
all: by rewrite (fin_itv_interiorE, rinfty_itv_interiorE, linfty_itv_interiorE).
Qed.

End theory.

End EndlessDenseOrderTopologyTheory.

Section realField_topology.
Variable R : realFieldType.
Local Open Scope order_scope.

Let real_is_endless := @EndlessDenseOrderTheory.numDomain_is_endless R.
Let real_is_dense := @EndlessDenseOrderTheory.numField_is_dense R.

Lemma open_itv_open_ends (i : interval R) :
  neitv i -> open [set` i] -> itv_open_ends i.
Proof. exact: EndlessDenseOrderTopologyTheory.open_itv_open_ends. Qed.

Lemma closed_itv_closed_ends (i : interval R) :
  neitv i -> closed [set` i] -> itv_closed_ends i.
Proof. exact: EndlessDenseOrderTopologyTheory.closed_itv_closed_ends. Qed.

Lemma itv_closureE (l r : itv_bound R) :
  neitv (Interval l r) ->
  closure [set` Interval l r] =
    [set` Interval
        (match l with BSide _ x => BLeft x  | BInfty _ => l end)
        (match r with BSide _ y => BRight y | BInfty _ => r end)].
Proof. exact: EndlessDenseOrderTopologyTheory.itv_closureE. Qed.

Lemma itv_interiorE (l r : itv_bound R) :
  [set` Interval l r]° =
    [set` Interval
        (match l with BSide _ x => BRight x  | BInfty _ => l end)
        (match r with BSide _ y => BLeft y | BInfty _ => r end)].
Proof. exact: EndlessDenseOrderTopologyTheory.itv_interiorE. Qed.

End realField_topology.
