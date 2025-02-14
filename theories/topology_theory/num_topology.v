(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean.
From mathcomp Require Import all_classical.
From mathcomp Require Import itv reals topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure order_topology.

(**md**************************************************************************)
(* # Topological notions for numerical types                                  *)
(*                                                                            *)
(* We endow `numFieldType` with the types of topological notions (accessible  *)
(* with `Import numFieldTopology.Exports.                                     *)
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

HB.instance Definition _ (R : numFieldType) :=
  Nbhs_isPseudoMetric.Build R R^o
    nbhs_ball_normE ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma real_order_nbhsE (R : realFieldType) (x : R^o) : nbhs x =
  filter_from (fun i => itv_open_ends i /\ x \in i) (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U.
  case => _ /posnumP[e] xeU.
  exists (`]x - e%:num, x + e%:num[); first split; first by right.
    by rewrite in_itv /= -real_lter_distl subrr // normr0.
  apply: (subset_trans _ xeU) => z /=.
  by rewrite in_itv /= -real_lter_distl //= distrC.
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
    by move/subitvP => H ?; exact: H.
  by rewrite subitvE lteBSide/= subKr lexx.
- move=> xr rU; exists (r - x) => /=; first by rewrite lterBDr add0r (itvP xr).
  apply/(subset_trans _ rU)/subset_ball_prop_in_itv.
  suff : (`]x - (r - x), x + (r - x)[ <= `]-oo, r[)%O.
    by move/subitvP => H ?; exact: H.
  by rewrite subitvE lteBSide/= addrC subrK.
- by move=> _; rewrite set_itvE subTset => ->; exists 1 => /=.
Qed.

Module numFieldTopology.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : rcfType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : archiFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) := PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numClosedFieldType) :=
  PseudoPointedMetric.copy R R^o.

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) :=
  Order_isNbhs.Build _ R (@real_order_nbhsE R).

#[export, non_forgetful_inheritance]
HB.instance Definition _ (R : numFieldType) := PseudoPointedMetric.copy R R^o.

Module Exports. HB.reexport. End Exports.

End numFieldTopology.

Import numFieldTopology.Exports.

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

Global Instance Proper_dnbhs_regular_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2)%R; apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
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
