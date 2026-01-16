(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import product_topology pseudometric_structure.

(**md**************************************************************************)
(* # Order topology                                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*                    POrderedNbhs == join of Nbhs and isPOrder               *)
(*             POrderedTopological == join of Topological and isPOrder        *)
(*                 POrderedUniform == join of Uniform and isPOrder            *)
(*            POrderedPseudoMetric == join of PseudoMetric and isPOrder       *)
(*      POrderedPointedTopological == join of PointedTopological and isPOrder *)
(*            orderTopologicalType == a topology built from intervals         *)
(*                order_topology T == the induced order topology on T         *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition POrderedNbhs d :=
  { T of Nbhs T & Order.isPOrder d T }.

HB.structure Definition POrderedTopological d :=
  { T of Topological T & Order.isPOrder d T }.

HB.structure Definition POrderedUniform d :=
  {T of Uniform T & Order.isPOrder d T}.

HB.structure Definition POrderedPseudoMetric d (R : numDomainType) :=
  {T of PseudoMetric R T & Order.isPOrder d T}.

HB.structure Definition POrderedPointedTopological d :=
  {T of PointedTopological T & Order.isPOrder d T}.

(** TODO: generalize this to a preOrder once that's available *)
HB.mixin Record Order_isNbhs d (T : Type) of Nbhs T & Order.Total d T := {
  (** Note that just the intervals `]a, b[ doesn't work when the order has a
      top or bottom element, so we also need the rays `]-oo, b[ and ]a, +oo[ *)
  itv_nbhsE : forall x : T, nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i])
}.

#[short(type="orderNbhsType")]
HB.structure Definition OrderNbhs d :=
  { T of Nbhs T & Order.Total d T & Order_isNbhs d T }.

#[short(type="orderTopologicalType")]
HB.structure Definition OrderTopological d :=
  { T of Topological T & Order.Total d T & Order_isNbhs d T }.

#[short(type="orderUniformType")]
HB.structure Definition OrderUniform d :=
  {T of Uniform T & OrderTopological d  T}.

#[short(type="orderPseudoMetricType")]
HB.structure Definition OrderPseudoMetric d (R : numDomainType) :=
  {T of PseudoMetric R T & OrderTopological d T}.

Section order_topologies.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Context {d} {T : orderTopologicalType d}.
Implicit Types x y : T.

Lemma rray_open x : @open T `]x, +oo[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists `]x, +oo[%O => //; split => //; left.
Qed.
Hint Resolve rray_open : core.

Lemma lray_open x : @open T `]-oo, x[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists (`]-oo, x[)%O => //; split => //; left.
Qed.
Hint Resolve lray_open : core.

Lemma itv_open x y : @open T `]x, y[.
Proof. by rewrite set_itv_splitI /=; apply: openI. Qed.
Hint Resolve itv_open : core.

Lemma itv_open_ends_open (i : interval T) : itv_open_ends i -> open [set` i].
Proof.
case: i; rewrite /itv_open_ends => [[[]t1|[]]] [[]t2|[]] /orP[]? => //.
by rewrite set_itvE; exact: openT.
Qed.

Lemma rray_closed x : @closed T `[x, +oo[.
Proof. by rewrite -setCitvl closedC. Qed.
Hint Resolve rray_closed : core.

Lemma lray_closed x : @closed T `]-oo, x].
Proof. by rewrite -setCitvr closedC. Qed.
Hint Resolve lray_closed : core.

Lemma itv_closed x y : @closed T `[x, y].
Proof. by rewrite set_itv_splitI; apply: closedI => /=. Qed.
Hint Resolve itv_closed : core.

Lemma itv_closure x y : closure `]x, y[ `<=` `[x, y].
Proof.
rewrite closureE => r; apply; split => //.
by apply: subset_itvScc => /=; rewrite bnd_simp.
Qed.

Lemma itv_closed_infimums (A : set T) : A !=set0 -> closed A ->
  infimums A `<=` A.
Proof.
move=> [a0 Aa0] + l [loL] hiL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q []]].
have [E|E] := eqVneq ([set` Interval (BSide true l) q] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: q E.
- move=> b q /[swap] /itv_open_ends_rside -> E lpq ; suff : lbound A q.
    move/hiL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`[l, q[ `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[|//].
  by rewrite ltNge (loL _ Aa).
- move=> b _ /itv_open_ends_rinfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundlr /= => /andP[pl _]; apply/andP.
  by split => //; exact/(le_trans pl)/loL.
Qed.

Lemma itv_closed_supremums (A : set T) : A !=set0 -> closed A ->
  supremums A `<=` A.
Proof.
move=> [a0 Aa0] + l [upL] lbL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q[]]].
have [E|E] := eqVneq ([set` Interval p (BSide false l)] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: p E.
- move=> b p /[swap] /itv_open_ends_lside -> E lpq ; suff : ubound A p.
    move/lbL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`]p, l] `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[//|].
  by rewrite ltNge (upL _ Aa).
- move=> b _ /itv_open_ends_linfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundrl /= => /andP[_ pl]; apply/andP.
  by split => //; exact/(le_trans _ pl)/upL.
Qed.

Let sub_open_mem x (U : set T) (i : interval T) :=
  [/\ [set` i] `<=` U, open [set` i] & x \in i].

Lemma clopen_bigcup_clopen x (U : set T) : clopen U -> U x ->
  clopen (\bigcup_(i in sub_open_mem x U) [set` i]).
Proof.
pose I := \bigcup_(i in sub_open_mem x U) [set` i].
move=> clU Ux; split; first by apply: bigcup_open => ? [].
have cIV : closure I `<=` U.
  rewrite closureE => z /(_ U); apply; split; first by case: clU.
  by move=> ? [? [+ _ _]]; exact.
apply/closure_id; rewrite eqEsubset; split; first exact: subset_closure.
move=> z cIi; have Uz : U z by exact: cIV.
case: clU => + _;  rewrite {1}openE => /(_ _ Uz).
rewrite /interior /= itv_nbhsE /= => -[i [/itv_open_ends_open oi iy] siU].
case/(_ [set` i]): cIi; first by move: oi; rewrite openE; exact.
move=> /= w [[j [jU oJ jy jw]]] wi; exists (i `|` j)%O; first last.
  exact/(le_trans iy)/leUl.
split; first by rewrite itv_setU ?{1}subUset //; exists w.
by rewrite itv_setU ?{1}subUset //; [exact: openU | exists w].
exact/(le_trans jy)/leUr.
Qed.

End order_topologies.
Hint Resolve lray_open : core.
Hint Resolve rray_open : core.
Hint Resolve itv_open : core.
Hint Resolve lray_closed : core.
Hint Resolve rray_closed : core.
Hint Resolve itv_closed : core.

Definition order_topology (T : Type) : Type := T.

Section induced_order_topology.

Context {d} {T : orderType d}.

Local Notation oT := (order_topology T).

HB.instance Definition _ := isPointed.Build (interval T) (`]-oo,+oo[).

HB.instance Definition _ := Order.Total.on oT.
HB.instance Definition _ := @isSubBaseTopological.Build oT
  (interval T) (itv_is_open_unbounded) (fun i => [set` i]).

Lemma order_nbhs_itv (x : oT) : nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U; first last.
  case=> /= i [ro xi /filterS]; apply; move: ro => /orP [rayi|].
    exists [set` i]; split => //=.
    exists [set [set` i]]; last by rewrite bigcup_set1.
    move=> A ->; exists (fset1 i); last by rewrite set_fset1 bigcap_set1.
    by move=> ?; rewrite !inE => /eqP ->.
  case: i xi => [][[]l|[]] [[]r|[]] xlr//= ?; exists `]l, r[%classic.
  split => //; exists [set `]l, r[%classic]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset `]-oo, r[ ; `]l, +oo[]%fset.
    by move=> ?; rewrite !inE => /orP[] /eqP ->.
  rewrite set_fsetU !set_fset1 bigcap_setU !bigcap_set1.
  by rewrite (@set_itv_splitI _ _ `]l, r[) /= setIC.
case=> ? [[ I Irp] <-] [?] /[dup] /(Irp _) [F rayF <-] IF Fix IU.
pose j := \big[Order.meet/`]-oo, +oo[]_(i <- F) i.
exists j; first split.
- rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//.
  + apply: (big_ind itv_open_ends) => //=; first exact: itv_open_endsI.
    by rewrite /itv_open_ends;  move=> i /rayF /set_mem ->.
  + by move=> p /=; rewrite !inE/=; exact: andb_id2l.
- pose f (i : interval T) : Prop := x \in i; suff : f j by [].
  rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//=.
  + by apply: big_ind => //=; rewrite /f /= => a ? xa ?; rewrite in_itvI xa.
  + by move=> p /=; rewrite !inE/=; exact: andb_id2l.
- suff -> : [set` j] = \bigcap_(i in [set` F]) [set` i].
    by move=> i Fi; apply: IU; exists (\bigcap_(i in [set` F]) [set` i]).
  rewrite -bigsetI_fset_set ?set_fsetK//.
  pose f (i : interval T) (j : set T) : Prop := [set` i] = j.
  suff : f j (\big[setI/[set: T]]_(i <- F) [set` i]) by [].
  rewrite /j big_mkcond /=; apply: big_ind2; rewrite /f ?set_itvE//.
  by move=> ? ? ? ? <- <-; rewrite itv_setI.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ oT order_nbhs_itv.
End induced_order_topology.

Lemma min_continuous {d} {T : orderTopologicalType d} :
  continuous (fun xy : T * T => Order.min xy.1 xy.2).
Proof.
case=> x y; have [<- U /=|]:= eqVneq x y.
  rewrite min_l// => Ux; exists (U, U) => //= -[a b [Ua Ub]].
  by have /orP[?|?]/= := le_total a b; [rewrite min_l|rewrite min_r].
wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP[|yx /eqP/nesym/eqP yNx]; first exact: WH.
  rewrite (_ : (fun _ => _) = (fun xy => Order.min xy.1 xy.2) \o @swap T T).
    by apply: continuous_comp; [exact: swap_continuous|exact: WH].
  apply/funext => -[a b/=]; have /orP[ab|ba] := le_total a b.
  - by rewrite min_l // min_r.
  - by rewrite min_r // min_l.
move=> _ U /=; rewrite (min_l (ltW xy)) => Ux.
have [[z xzy]|/forallNP/= xNy] := pselect (exists z, x < z < y)%O.
  exists (U `&` `]-oo, z[, `]z, +oo[%classic) => /=.
    split; [apply: filterI =>//|]; apply: open_nbhs_nbhs.
    - by split; [exact: lray_open|rewrite set_itvE; case/andP: xzy].
    - by split; [exact: rray_open|rewrite set_itvE; case/andP: xzy].
  case=> a b /= [[Ua]]; rewrite !in_itv andbT /= => az zb.
  by rewrite min_l// (ltW (lt_trans az _)).
exists (U `&` `]-oo, y[, `]x, +oo[%classic) => /=.
  split; [apply: filterI => //|]; apply: open_nbhs_nbhs.
  - by split; [exact: lray_open|rewrite set_itvE].
  - by split; [exact: rray_open|rewrite set_itvE].
case=> a b /= [[Ua]]; rewrite !in_itv andbT /= => ay xb.
rewrite min_l// leNgt; apply: contra_notN (xNy b) => ba.
by rewrite xb (lt_trans ba).
Qed.

Lemma min_fun_continuous {d} {X : topologicalType} {T : orderTopologicalType d}
    (f g : X -> T) :
  continuous f -> continuous g -> continuous (f \min g).
Proof.
move=> fc gc z; apply: continuous2_cvg; [|exact: fc|exact: gc].
by apply min_continuous.
Qed.

Lemma max_continuous {d} {T : orderTopologicalType d} :
  continuous (fun xy : T * T => Order.max xy.1 xy.2).
Proof.
case=> x y; have [<- U|] := eqVneq x y.
  rewrite /= max_r // => ux; exists (U, U) => //= -[a b] [/= Ua Ub].
  by have /orP[?|?]/= := le_total a b; [rewrite max_r|rewrite max_l].
wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP[|yx /eqP/nesym/eqP yNx]; first exact: WH.
  rewrite (_ : (fun _ => _) = (fun xy => Order.max xy.1 xy.2) \o @swap T T).
    by apply: continuous_comp; [exact: swap_continuous|exact: WH].
  apply/funext => -[a b] /=; have /orP [ab|ba] := le_total a b.
  - by rewrite max_r // max_l.
  - by rewrite max_l // max_r.
move=> _ U /=; rewrite (max_r (ltW xy)) => Ux.
have [[z xzy]|/forallNP /= xNy] := pselect (exists z, x < z < y)%O.
  exists (`]-oo, z[%classic, U `&` `]z, +oo[) => /=.
    split; [|apply: filterI =>//]; apply: open_nbhs_nbhs.
    - by split; [exact: lray_open|rewrite set_itvE; case/andP: xzy].
    - by split; [exact: rray_open|rewrite set_itvE; case/andP: xzy].
  case=> a b /= [] + []; rewrite !in_itv andbT /= => az Ub zb.
  by rewrite (max_r (ltW (lt_trans az _))).
exists (`]-oo, y[%classic, U `&` `]x, +oo[) => /=.
  split; [|apply: filterI => //]; apply: open_nbhs_nbhs.
  - by split; [exact: lray_open|rewrite set_itvE].
  - by split; [exact: rray_open|rewrite set_itvE].
case=> a b /=; rewrite !in_itv /= andbT => [/=] [ay] [Ub] xb.
rewrite max_r// leNgt; apply: contra_notN (xNy b) => ba.
by rewrite xb (lt_trans ba).
Qed.

Lemma max_fun_continuous {d} {X : topologicalType} {T : orderTopologicalType d}
    (f g : X -> T):
  continuous f -> continuous g -> continuous (f \max g).
Proof.
move=> fc gc z; apply: continuous2_cvg; [|exact: fc|exact: gc].
by apply max_continuous.
Qed.
