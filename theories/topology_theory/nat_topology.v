(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure order_topology.

(**md**************************************************************************)
(* # Topology for natural numbers                                             *)
(*                                                                            *)
(* Natural numbers `nat` are endowed with the structure of topology.          *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section nat_topologicalType.

Let D : set nat := setT.
Let b : nat -> set nat := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite predeqE => i; split => // _; exists i. Qed.

Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof. by move=> i j t _ _ -> ->; exists j. Qed.

HB.instance Definition _ := isBaseTopological.Build nat bT bD.

End nat_topologicalType.

Lemma nbhs_infty_gt N : \forall n \near \oo, (N < n)%N.
Proof. by exists N.+1. Qed.
#[global] Hint Resolve nbhs_infty_gt : core.

Lemma nbhs_infty_ge N : \forall n \near \oo, (N <= n)%N.
Proof. by exists N. Qed.

Lemma nbhs_infty_ger {R : realType} (r : R) :
  \forall n \near \oo, (r <= n%:R)%R.
Proof.
exists `|Num.ceil r|%N => // n /=; rewrite -(ler_nat R); apply: le_trans.
by rewrite (le_trans (ceil_ge _))// natr_absz ler_int ler_norm.
Qed.

Lemma cvg_addnl N : addn N @ \oo --> \oo.
Proof.
by move=> P [n _ Pn]; exists (n - N)%N => // m; rewrite /= leq_subLR => /Pn.
Qed.

Lemma cvg_addnr N : addn^~ N @ \oo --> \oo.
Proof. by under [addn^~ N]funext => n do rewrite addnC; apply: cvg_addnl. Qed.

Lemma cvg_subnr N : subn^~ N @ \oo --> \oo.
Proof.
move=> P [n _ Pn]; exists (N + n)%N => //= m le_m.
by apply: Pn; rewrite /= leq_subRL// (leq_trans _ le_m)// leq_addr.
Qed.

Lemma cvg_mulnl N : (N > 0)%N -> muln N @ \oo --> \oo.
Proof.
case: N => N // _ P [n _ Pn]; exists (n %/ N.+1).+1 => // m.
by rewrite /= ltn_divLR// => n_lt; apply: Pn; rewrite mulnC /= ltnW.
Qed.

Lemma cvg_mulnr N :(N > 0)%N -> muln^~ N @ \oo --> \oo.
Proof.
by move=> N_gt0; under [muln^~ N]funext => n do rewrite mulnC; apply: cvg_mulnl.
Qed.

Lemma cvg_divnr N : (N > 0)%N -> divn^~ N @ \oo --> \oo.
Proof.
move=> N_gt0 P [n _ Pn]; exists (n * N)%N => //= m.
by rewrite /= -leq_divRL//; apply: Pn.
Qed.

Lemma near_inftyS (P : set nat) :
  (\forall x \near \oo, P (S x)) -> (\forall x \near \oo, P x).
Proof. case=> N _ NPS; exists (S N) => // [[]]; rewrite /= ?ltn0 //. Qed.

Section infty_nat.
Local Open Scope nat_scope.

Let cvgnyP {F : set_system nat} {FF : Filter F} : [<->
(* 0 *) F --> \oo;
(* 1 *) forall A, \forall x \near F, A <= x;
(* 2 *) forall A, \forall x \near F, A < x;
(* 3 *) \forall A \near \oo, \forall x \near F, A < x;
(* 4 *) \forall A \near \oo, \forall x \near F, A <= x ].
Proof.
tfae; first by move=> Foo A; apply: Foo; apply: nbhs_infty_ge.
- move=> AF A; near \oo => B; near=> x.
  suff : (B <= x)%N by apply: leq_trans; near: B; apply: nbhs_infty_gt.
  by near: x; apply: AF; near: B.
- by move=> Foo; near do apply: Foo.
- by apply: filterS => ?; apply: filterS => ?; apply: ltnW.
case=> [A _ AF] P [n _ Pn]; near \oo => B; near=> m; apply: Pn => /=.
suff: (B <= m)%N by apply: leq_trans; near: B; apply: nbhs_infty_ge.
by near: m; apply: AF; near: B; apply: nbhs_infty_ge.
Unshelve. all: end_near. Qed.

Section map.
Context {I : Type} {F : set_system I} {FF : Filter F} (f : I -> nat).

Lemma cvgnyPge :
  f @ F --> \oo <-> forall A, \forall x \near F, A <= f x.
Proof. exact: (cvgnyP 0%N 1%N). Qed.

Lemma cvgnyPgt :
  f @ F --> \oo <-> forall A, \forall x \near F, A < f x.
Proof. exact: (cvgnyP 0%N 2%N). Qed.

Lemma cvgnyPgty :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A < f x.
Proof. exact: (cvgnyP 0%N 3%N). Qed.

Lemma cvgnyPgey :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A <= f x.
Proof. exact: (cvgnyP 0%N 4%N). Qed.

End map.

End infty_nat.

Lemma discrete_nat : discrete_space nat.
Proof.
rewrite /discrete_space predeq2E => n U; split.
   by case => /= V [_ Vn VU]; exact/principal_filterP/VU.
move/principal_filterP => Un; exists U; split => //=; exists U => //.
by rewrite eqEsubset; split => [z [i Ui ->//]|z Uz]; exists z.
Qed.

Section nat_ord_topology.
Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Local Lemma nat_nbhs_itv (n : nat) :
  nbhs n = filter_from
    (fun i => itv_open_ends i /\ n \in i)
    (fun i => [set` i]).
Proof.
rewrite discrete_nat eqEsubset; split=> U; first last.
  by case => V [_ Vb] VU; apply/principal_filterP/VU; apply: Vb.
move/principal_filterP; case: n.
  move=> U0; exists `]-oo, 1[; first split => //; first by left.
  by move=> r /=; rewrite in_itv /=; case: r.
move=> n USn; exists `]n, n.+2[; first split => //; first by right.
  by rewrite in_itv; apply/andP;split => //=; rewrite /Order.lt //=.
move=> r /=; rewrite in_itv /= => nr2; suff: r = n.+1 by move=> ->.
exact/esym/le_anti.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ nat nat_nbhs_itv.

End nat_ord_topology.
