(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import interval_inference reals topology_structure.
From mathcomp Require Import uniform_structure pseudometric_structure.
From mathcomp Require Import order_topology.

(**md**************************************************************************)
(* # Topological notions for numerical types                                  *)
(*                                                                            *)
(* We endow `numFieldType` with the types of topological notions (accessible  *)
(* with `Import numFieldTopology.Exports).                                    *)
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
  exists (`]x - e%:num, x + e%:num[); first split; first by right.
    by rewrite in_itv/= -lter_distl subrr normr0.
  apply: subset_trans xeU => z /=.
  by rewrite in_itv /= -lter_distl distrC.
case => [][[[]l|[]]] [[]r|[]] [[]]//= _.
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

Lemma in_continuous_mksetP {T : realFieldType} {U : realFieldType}
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
