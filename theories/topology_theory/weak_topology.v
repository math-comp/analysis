(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import itv reals topology_structure uniform_structure.
From mathcomp Require Import order_topology pseudometric_structure.

(**md**************************************************************************)
(* # Weak topology                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*         weak_topology f == weak topology by a function f : S -> T on S     *)
(*                            S must be a choiceType and T a topologicalType. *)
(* ```                                                                        *)
(* `weak_topology` is equipped with the structures of:                        *)
(* - uniform space                                                            *)
(* - pseudometric space (the metric space for weak topologies)                *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition weak_topology {S : Type} {T : Type}
  (f : S -> T) : Type := S.

Section Weak_Topology.
Variable (S : choiceType) (T : topologicalType) (f : S -> T).
Local Notation W := (weak_topology f).

Definition wopen := [set f @^-1` A | A in open].

Local Lemma wopT : wopen [set: W].
Proof. by exists setT => //; apply: openT. Qed.

Local Lemma wopI (A B : set W) : wopen A -> wopen B -> wopen (A `&` B).
Proof.
by move=> [C Cop <-] [D Dop <-]; exists (C `&` D) => //; apply: openI.
Qed.

Local Lemma wop_bigU (I : Type) (g : I -> set W) :
  (forall i, wopen (g i)) -> wopen (\bigcup_i g i).
Proof.
move=> gop.
set opi := fun i => [set Ui | open Ui /\ g i = f @^-1` Ui].
exists (\bigcup_i get (opi i)).
  apply: bigcup_open => i.
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
have g_preim i : g i = f @^-1` (get (opi i)).
  by have /getPex [] : exists U, opi i U by have [U] := gop i; exists U.
rewrite predeqE => s; split=> [[i _]|[i _]]; last by rewrite g_preim; exists i.
by rewrite -[_ _]/((f @^-1` _) _) -g_preim; exists i.
Qed.

HB.instance Definition _ := Choice.on W.
HB.instance Definition _ :=
  isOpenTopological.Build W wopT wopI wop_bigU.

Lemma weak_continuous : continuous (f : W -> T).
Proof. by apply/continuousP => A ?; exists A. Qed.

Lemma cvg_image (F : set_system S) (s : S) :
  Filter F -> f @` setT = setT ->
  F --> (s : W) <-> ([set f @` A | A in F] : set_system _) --> f s.
Proof.
move=> FF fsurj; split=> [cvFs|cvfFfs].
  move=> A /weak_continuous [B [Bop Bs sBAf]].
  have /cvFs FB : nbhs (s : W) B by apply: open_nbhs_nbhs.
  rewrite nbhs_simpl; exists (f @^-1` A); first exact: filterS FB.
  exact: image_preimage.
move=> A /= [_ [[B Bop <-] Bfs sBfA]].
have /cvfFfs [C FC fCeB] : nbhs (f s) B by rewrite nbhsE; exists B.
rewrite nbhs_filterE; apply: filterS FC.
by apply: subset_trans sBfA; rewrite -fCeB; apply: preimage_image.
Qed.

End Weak_Topology.

HB.instance Definition _ (S : pointedType) (T : topologicalType) (f : S -> T) :=
  Pointed.on (weak_topology f).

Section weak_uniform.
Local Open Scope relation_scope.
Variable (pS : choiceType) (U : uniformType) (f : pS -> U).

Let S := weak_topology f.

Definition weak_ent : set_system (S * S) :=
  filter_from (@entourage U) (fun V => (map_pair f)@^-1` V).

Lemma weak_ent_filter : Filter weak_ent.
Proof.
apply: filter_from_filter; first by exists setT; exact: entourageT.
by move=> P Q ??; (exists (P `&` Q); first exact: filterI) => ?.
Qed.

Lemma weak_ent_refl A : weak_ent A -> diagonal `<=` A.
Proof.
by move=> [B ? sBA] [x y]/diagonalP ->; apply/sBA; exact: entourage_refl.
Qed.

Lemma weak_ent_inv A : weak_ent A -> weak_ent A^-1.
Proof.
move=> [B ? sBA]; exists B^-1; first exact: entourage_inv.
by move=> ??; exact/sBA.
Qed.

Lemma weak_ent_split A : weak_ent A -> exists2 B, weak_ent B & B \; B `<=` A.
Proof.
move=> [B entB sBA]; have : exists C, entourage C /\ C \; C `<=` B.
  exact/exists2P/entourage_split_ex.
case=> C [entC CsubB]; exists ((map_pair f)@^-1` C); first by exists C.
by case=> x y [a ? ?]; apply/sBA/CsubB; exists (f a).
Qed.

Lemma weak_ent_nbhs : nbhs = nbhs_ weak_ent.
Proof.
rewrite predeq2E => x V; split.
  case=> [? [[B  ? <-] ? BsubV]]; have: nbhs (f x) B by apply: open_nbhs_nbhs.
  move=> /nbhsP [W ? WsubB]; exists ((map_pair f) @^-1` W); first by exists W.
  by move=>??; exact/BsubV/WsubB.
case=> W [V' entV' V'subW] /filterS; apply.
have : nbhs (f x) (xsection V' (f x)) by apply/nbhsP; exists V'.
rewrite (@nbhsE U) => [[O [openU Ofx Osub]]].
(exists (f @^-1` O); repeat split => //); first by exists O => //.
by move=> w ?; apply/mem_set; apply: V'subW; apply/set_mem; exact: Osub.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build (weak_topology f) weak_ent
  weak_ent_filter weak_ent_refl weak_ent_inv weak_ent_split weak_ent_nbhs.

End weak_uniform.

HB.instance Definition _ (pS : pointedType) (U : uniformType) (f : pS -> U) :=
  Pointed.on (weak_topology f).

Section weak_pseudoMetric.
Context {R : realType} (pS : choiceType) (U : pseudoMetricType R) .
Variable (f : pS -> U).

Notation S := (weak_topology f).

Definition weak_ball (x : S) (r : R) (y : S) := ball (f x) r (f y).

Lemma weak_pseudo_metric_ball_center (x : S) (e : R) : 0 < e -> weak_ball x e x.
Proof. by move=> /posnumP[{}e]; exact: ball_center. Qed.

Lemma weak_pseudo_metric_entourageE : entourage = entourage_ weak_ball.
Proof.
rewrite /entourage /= /weak_ent -entourage_ballE /entourage_.
have -> : (fun e => [set xy | ball (f xy.1) e (f xy.2)]) =
   (preimage (map_pair f) \o fun e => [set xy | ball xy.1 e xy.2])%FUN.
  by [].
rewrite eqEsubset; split; apply/filter_fromP.
- apply: filter_from_filter; first by exists 1 => /=.
  move=> e1 e2 e1pos e2pos; wlog e1lee2 : e1 e2 e1pos e2pos / e1 <= e2.
    by have [?|/ltW ?] := lerP e1 e2; [exact | rewrite setIC; exact].
  exists e1 => //; rewrite -preimage_setI; apply: preimage_subset.
  by move=> ? ?; split => //; apply: le_ball; first exact: e1lee2.
- by move=> E [e ?] heE; exists e => //; apply: preimage_subset.
- apply: filter_from_filter.
    by exists [set xy | ball xy.1 1 xy.2]; exists 1 => /=.
  move=> E1 E2 [e1 e1pos he1E1] [e2 e2pos he2E2].
  wlog ? : E1 E2 e1 e2 e1pos e2pos he1E1 he2E2 / e1 <= e2.
    have [? /(_ _ _ e1 e2)|/ltW ? ] := lerP e1 e2; first exact.
    by rewrite setIC => /(_ _ _ e2 e1); exact.
  exists (E1 `&` E2) => //; exists e1 => // xy /= B; split; first exact: he1E1.
  by apply/he2E2/le_ball; last exact: B.
- by move=> e ?; exists [set xy | ball xy.1 e xy.2] => //; exists e => /=.
Qed.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R S
  weak_pseudo_metric_ball_center (fun _ _ _ => @ball_sym _ _ _ _ _)
  (fun _ _ _ _ _ => @ball_triangle _ _ _ _ _ _ _)
  weak_pseudo_metric_entourageE.

Lemma weak_ballE (e : R) (x : S) : f @^-1` (ball (f x) e) = ball x e.
Proof. by []. Qed.

End weak_pseudoMetric.

(** for an orderedTopologicalType T, and subtype U
    (order_topology (sub_type U)) `<=` (weak_topology (sub_type U))
    but generally the topologies are not equal!
    Consider `[0,1[ | {2}` as a subset of `[0,3]` for an example
*)
Section weak_order_refine.
Context {d} {X : orderTopologicalType d} {Y : subType X}.

Let OrdU : orderTopologicalType d := order_topology (sub_type Y).
Let WeakU : topologicalType := @weak_topology (sub_type Y) X val.

Lemma open_order_weak (U : set Y) : @open OrdU U -> @open WeakU U.
Proof.
rewrite ?openE /= /interior => + x Ux => /(_ x Ux); rewrite itv_nbhsE /=.
move=> [][][[]l|[]] [[]r|[]][][]//= _ xlr /filterS; apply.
- exists `]l, r[%classic; split => //=; exists `]\val l, \val r[%classic.
    exact: itv_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- exists `]l, +oo[%classic; split => //=; exists `]\val l, +oo[%classic.
    exact: rray_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- exists `]-oo, r[%classic; split => //=; exists `]-oo, \val r[%classic.
    exact: lray_open.
  by rewrite eqEsubset; split => z; rewrite preimage_itv.
- by rewrite set_itvE; exact: filterT.
Qed.

End weak_order_refine.

Lemma continuous_comp_weak {Y : choiceType} {X Z : topologicalType} (w : Y -> Z)
  (f : X -> weak_topology w) :
  continuous (w \o f) -> continuous f.
Proof.
move=> cf z U [?/= [[W oW <-]]] /= Wsfz /filterS; apply; apply: cf.
exact: open_nbhs_nbhs.
Qed.
