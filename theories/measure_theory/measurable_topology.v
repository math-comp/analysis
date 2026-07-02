From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat algebra finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality all_reals.
From mathcomp Require Import measurable_structure topology.
From mathcomp Require Import normed_module real_interval.

(**md**************************************************************************)
(* # Measure theory applied to topological spaces via the Borel sigma-algebra.*)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ```Soon : default display open.-sigma for topological types                *)
(* ```                                                                        *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section measurable_topology.
Context {T : topologicalType}.

Lemma salgebra_countable_basis {B : set_system T} (D : set T) : 
countable B -> basis B -> <<s D, B>> = <<s D, open>>.
Proof.
rewrite eqEsubset => /countable_bijP [A /card_esym/pcard_eqP/bijPex/= 
  [g [fg _ ag]]] /basisP [BO bB]; split. exact: sigma_algebra_sub.
apply: sigma_algebra_subl=> U /bB ->.
have sgU : set_surj (A `&` [set n | g n `<=` U]) (B `&` [set W | W `<=` U]) g.
by rewrite surjE in ag; rewrite surjE=> W [/ag [n An <-]/= gnU]; exists n.
rewrite (reindex_bigcup _ _ _ _ _ sgU). move=> n /= [a u]; split=>//. exact: fg.
rewrite bigcup_mkcond; apply: sigma_algebra_bigcup=> i. case: ifP=>//[|_].
  rewrite in_setE=> [[Ai _]]. apply: sub_sigma_algebra. exact: fg.
exact: sigma_algebra0.
Qed.

Lemma salgebra_open_closedE : 
<<s (@open T)>> = <<s closed>>.
Proof.
rewrite eqEsubset; split; apply: sigma_algebra_subl.
  move=> U oU; rewrite -(setCK U); apply: (sigma_algebraC (sub_sigma_algebra _)); 
  exact: open_closedC.
move=> F cF; rewrite -(setCK F); apply: (sigma_algebraC (sub_sigma_algebra _));
exact: closed_openC.
Qed.

End measurable_topology.

Section measurable_real.
Context {R : realType}.
Definition ocitv := [set `]ab.1,ab.2]%classic | ab in [set:R*R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Proof. by exists (a, b). Qed.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma salgebra_measurable {T : choiceType} (G : set_system T) : 
  <<s G>> = G.-sigma.-measurable.
Proof. by rewrite/measurable. Qed.

Lemma ocitv_measurable_set1 (r : R) : 
  measurable [set r : g_sigma_algebraType ocitv].
Proof.
rewrite set1_bigcap_oc; apply: bigcap_measurable => // k _. 
exact: sub_sigma_algebra.
Qed.
#[local] Hint Resolve ocitv_measurable_set1 : core.

Lemma ocitv_measurable_itv (i : interval R) : <<s ocitv>> [set` i].
Proof.
rewrite salgebra_measurable.
have moc (a b : R) : measurable (`]a, b] : set (g_sigma_algebraType ocitv)).
  by apply: sub_sigma_algebra.
have mopoo (x : R) : measurable (`]x, +oo[ : set (g_sigma_algebraType ocitv)).
  by rewrite itv_bndy_bigcup_BRight; exact: bigcup_measurable.
have mnooc (x : R) : measurable (`]-oo, x] : set (g_sigma_algebraType ocitv)).
  by rewrite -setCitvr; exact/measurableC.
have ooE (a b : R) : `]a, b[%classic = `]a, b] `\ b.
  by rewrite setDitv1r.
have moo (a b : R) : measurable (`]a, b[ : set (g_sigma_algebraType ocitv)).
  rewrite ooE; exact: measurableD.
have mcc (a b : R) : measurable (`[a, b] : set (g_sigma_algebraType ocitv)).
  case: (boolP (a <= b)) => ab; last by rewrite set_itv_ge.
  by rewrite -setU_1itvob//; apply/measurableU.
have mco (a b : R) : measurable (`[a, b[ : set (g_sigma_algebraType ocitv)).
  case: (boolP (a < b)) => ab; last by rewrite set_itv_ge.
  by rewrite -setU_1itvob//; apply/measurableU.
have oooE (b : R) : `]-oo, b[%classic = `]-oo, b] `\ b.
  by rewrite setDitv1r.
case: i => [[[] a|[]] [[] b|[]]] => //; do ?by rewrite set_itv_ge.
- by rewrite -setU_1itvob//; exact/measurableU.
- by rewrite oooE; exact/measurableD.
- by rewrite set_itvNyy.
Qed.
#[local] Hint Resolve ocitv_measurable_itv : core.


Lemma open_octiv_measurable (U : set R) (oU : open U) : <<s ocitv>> U.
Proof.
rewrite (open_disjoint_itv_bigcup oU); apply: sigma_algebra_bigcup => k.
have /is_intervalP -> := @open_disjoint_itv_is_interval _ U oU k. 
exact : ocitv_measurable_itv.
Qed.

Lemma octiv_open_measurable (a b : R) : <<s open>> `]a,b]%classic.
Proof.
rewrite [(`]a,b]%classic)] (_:_ = \bigcap_k `]a,b+(k.+1%:R)^-1[%classic).
  rewrite eqEsubset set_itvoc. split=> [x /= /andP[ax xb] i _|x cupx/=].
    rewrite set_itvoo/=. apply/andP; split=>[//|]. apply: (le_lt_trans xb).
    rewrite -[X in X<_]addr0; apply: ler_ltD=>//. by rewrite invr_gt0.
  apply/andP; split. have :=cupx 1%N I. by rewrite set_itvoo => /=/andP[ax].
  apply/ler_gtP=> z bz. have := cupx (truncn (z-b)^-1) I.
  rewrite set_itvoo/= =>/andP[_ xbz]. have := (addrNK b z); rewrite addrC => <-.
  apply: (ltW (lt_trans xbz (lt_le_trans (ler_ltD (le_refl b) _) (le_refl _)))).
  rewrite invf_plt ?posrE // ?subr_gt0//. exact: truncnS_gt.
rewrite -[X in _ X]setCK setC_bigcap; apply: sigma_algebraC.
apply: sigma_algebra_bigcup=>i; apply: sigma_algebraC; exact: sub_sigma_algebra.
Qed.

Lemma salgebra_ocitv_openE : <<s open>> = <<s ocitv>>.
Proof.
rewrite eqEsubset; split; apply: sigma_algebra_subl => /= E.
  by move=>/open_octiv_measurable. 
move=> [[a b] _ /= <-]; exact: octiv_open_measurable.
Qed.

Lemma measurable_ocitv_openE : 
  (@open R).-sigma.-measurable = ocitv.-sigma.-measurable.
Proof. exact: salgebra_ocitv_openE. Qed.

End measurable_real.