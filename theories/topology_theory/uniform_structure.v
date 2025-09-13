(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure.

(**md**************************************************************************)
(* # Uniform Spaces                                                           *)
(* This file provides uniform spaces, and their theory. It also includes      *)
(* complete spaces, which extends uniform in the hierarchy.                   *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### Uniform                                                                *)
(* ```                                                                        *)
(*                      nbhs_ ent == neighborhoods defined using entourages   *)
(*                    uniformType == interface type for uniform spaces: a     *)
(*                                   type equipped with entourages            *)
(*                                   The HB class is Uniform.                 *)
(*                   puniformType == a pointed and uniform space              *)
(*                      entourage == set of entourages in a uniform space     *)
(*                    split_ent E == when E is an entourage, split_ent E is   *)
(*                                   an entourage E' such that E' \o E' is    *)
(*                                   included in E when seen as a relation    *)
(*         countable_uniformity T == T's entourage has a countable base       *)
(*                                   This is equivalent to `T` being          *)
(*                                   metrizable.                              *)
(*              unif_continuous f == f is uniformly continuous                *)
(*                entourage_ ball == entourages defined using balls           *)
(* ```                                                                        *)
(* ## Factories                                                               *)
(* ```                                                                        *)
(*                 Nbhs_isUniform == factory to build a topological space     *)
(*                                   from a mixin for a uniform space         *)
(*                                                                            *)
(* ```                                                                        *)
(* ### Complete uniform spaces                                                *)
(* ```                                                                        *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (entourage definition)                   *)
(*                   completeType == interface type for a complete uniform    *)
(*                                   space structure                          *)
(*                                   The HB class is Complete.                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition nbhs_ {T T'} (ent : set_system (T * T')) (x : T) :=
  filter_from ent (fun A => xsection A x).

Lemma nbhs_E {T T'} (ent : set_system (T * T')) x :
  nbhs_ ent x = filter_from ent (fun A => xsection A x).
Proof. by []. Qed.

Local Open Scope relation_scope.

HB.mixin Record Nbhs_isUniform_mixin M of Nbhs M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal_subproof :
    forall A, entourage A -> diagonal `<=` A;
  entourage_inv_subproof : forall A, entourage A -> entourage A^-1;
  entourage_split_ex_subproof :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE_subproof : nbhs = nbhs_ entourage;
}.

#[short(type="uniformType")]
HB.structure Definition Uniform :=
  {T of Topological T & Nbhs_isUniform_mixin T}.

#[short(type="puniformType")]
HB.structure Definition PointedUniform :=
  {T of PointedTopological T & Nbhs_isUniform_mixin T}.


HB.factory Record Nbhs_isUniform M of Nbhs M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE : nbhs = nbhs_ entourage;
}.

Local Close Scope relation_scope.

HB.builders Context M of Nbhs_isUniform M.

Let nbhs_filter (p : M) : ProperFilter (nbhs p).
Proof.
rewrite nbhsE nbhs_E; apply: filter_from_proper; last first.
  by move=> A entA; exists p; apply/mem_set; apply: entourage_diagonal entA _ _.
apply: filter_from_filter.
  by exists setT; exact: @filterT entourage_filter.
move=> A B entA entB; exists (A `&` B); last by rewrite xsectionI.
exact: (@filterI _ _ entourage_filter).
Qed.

Let nbhs_singleton (p : M) A : nbhs p A -> A p.
Proof.
rewrite nbhsE nbhs_E  => - [B entB sBpA].
by apply/sBpA/mem_set; exact: entourage_diagonal entB _ _.
Qed.

Let nbhs_nbhs (p : M) A : nbhs p A -> nbhs p (nbhs^~ A).
Proof.
rewrite nbhsE nbhs_E => - [B entB sBpA].
have /entourage_split_ex[C entC sC2B] := entB.
exists C => // q Cpq; rewrite nbhs_E; exists C => // r Cqr.
by apply/sBpA/mem_set/sC2B; exists q; exact/set_mem.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build M
  nbhs_filter nbhs_singleton nbhs_nbhs.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build M
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex nbhsE.

HB.end.

Local Open Scope relation_scope.

HB.factory Record isUniform M of Choice M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
}.

Local Close Scope relation_scope.

HB.builders Context M of isUniform M.

HB.instance Definition _ := @hasNbhs.Build M (nbhs_ entourage).

HB.instance Definition _ := @Nbhs_isUniform.Build M entourage
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex erefl.

HB.end.

Lemma nbhs_entourageE {M : uniformType} : nbhs_ (@entourage M) = nbhs.
Proof. by rewrite -Nbhs_isUniform_mixin.nbhsE_subproof. Qed.

Lemma entourage_sym {X Y : Type} E (x : X) (y : Y) :
  E (x, y) <-> (E ^-1)%relation (y, x).
Proof. by []. Qed.

Lemma filter_from_entourageE {M : uniformType} x :
  filter_from (@entourage M) (fun A => xsection A x) = nbhs x.
Proof. by rewrite -nbhs_entourageE. Qed.

Module Export NbhsEntourage.
Definition nbhs_simpl :=
  (nbhs_simpl,@filter_from_entourageE,@nbhs_entourageE).
End NbhsEntourage.

Lemma nbhsP {M : uniformType} (x : M) P : nbhs x P <-> nbhs_ entourage x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma filter_inv {T : Type} (F : set (set (T * T))) :
  Filter F -> Filter [set V^-1 | V in F]%relation.
Proof.
move=> FF; split => /=.
- by exists [set: T * T] => //; exact: filterT.
- by move=> P Q [R FR <-] [S FS <-]; exists (R `&` S) => //; exact: filterI.
- move=> P Q PQ [R FR RP]; exists Q^-1%relation => //; first last.
    by rewrite eqEsubset; split; case.
  by apply: filterS FR; case=> ? ? /= ?; apply: PQ; rewrite -RP.
Qed.

Section uniformType1.
Local Open Scope relation_scope.
Context {M : uniformType}.

Lemma entourage_refl (A : set (M * M)) x : entourage A -> A (x, x).
Proof. by move=> entA; exact: entourage_diagonal_subproof entA _ _. Qed.

Global Instance entourage_filter' : Filter (@entourage M).
Proof.
exact: entourage_filter.
Qed.

Lemma entourageT : entourage [set: M * M].
Proof. exact: filterT. Qed.

Lemma entourage_inv (A : set (M * M)) : entourage A -> entourage A^-1.
Proof. exact: entourage_inv_subproof. Qed.

Lemma entourage_split_ex (A : set (M * M)) :
  entourage A -> exists2 B, entourage B & B \; B `<=` A.
Proof. exact: entourage_split_ex_subproof. Qed.

Definition split_ent (A : set (M * M)) :=
  get (entourage `&` [set B | B \; B `<=` A]).

Lemma split_entP (A : set (M * M)) : entourage A ->
  entourage (split_ent A) /\ split_ent A \; split_ent A `<=` A.
Proof. by move/entourage_split_ex/exists2P/getPex. Qed.

Lemma entourage_split_ent (A : set (M * M)) : entourage A ->
  entourage (split_ent A).
Proof. by move=> /split_entP []. Qed.

Lemma subset_split_ent (A : set (M * M)) : entourage A ->
  split_ent A \; split_ent A `<=` A.
Proof. by move=> /split_entP []. Qed.

Lemma entourage_split (z x y : M) A : entourage A ->
  split_ent A (x, z) -> split_ent A (z, y) -> A (x, y).
Proof. by move=> /subset_split_ent sA ? ?; apply: sA; exists z. Qed.

Lemma nbhs_entourage (x : M) A : entourage A -> nbhs x (xsection A x).
Proof. by move=> ?; apply/nbhsP; exists A. Qed.

Lemma cvg_entourageP F (FF : Filter F) (p : M) :
  F --> p <-> forall A, entourage A -> \forall q \near F, A (p, q).
Proof.
rewrite -filter_fromP [X in filter_from _ X](_ : _ = @xsection M M ^~ p)//.
  by rewrite filter_from_entourageE.
by apply/funext => E; apply/seteqP; split => [|] ? /xsectionP.
Qed.

Lemma cvg_entourage {F} {FF : Filter F} (x : M) :
  F --> x -> forall A, entourage A -> \forall y \near F, A (x, y).
Proof. by move/cvg_entourageP. Qed.

Lemma cvg_app_entourageP T (f : T -> M) F (FF : Filter F) p :
  f @ F --> p <-> forall A, entourage A -> \forall t \near F, A (p, f t).
Proof. exact: cvg_entourageP. Qed.

Lemma entourage_invI (E : set (M * M)) : entourage E -> entourage (E `&` E^-1).
Proof. by move=> ?; apply: filterI; last exact: entourage_inv. Qed.

Lemma split_ent_subset (E : set (M * M)) : entourage E -> split_ent E `<=` E.
Proof.
move=> entE; case=> x y splitxy; apply: subset_split_ent => //; exists y => //.
by apply: entourage_refl; exact: entourage_split_ent.
Qed.

End uniformType1.

Global Instance entourage_pfilter {M : puniformType} :
  ProperFilter (@entourage M).
Proof.
apply Build_ProperFilter_ex; last exact: entourage_filter.
by move=> A entA; exists (point, point); apply: entourage_refl.
Qed.

#[global]
Hint Extern 0 (entourage (split_ent _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (get _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (_^-1)%relation) => exact: entourage_inv : core.
Arguments entourage_split {M} z {x y A}.
#[global]
Hint Extern 0 (nbhs _ (xsection _ _)) => exact: nbhs_entourage : core.

Lemma ent_closure {M : uniformType} (x : M) E : entourage E ->
  closure (xsection (split_ent E) x) `<=` xsection E x.
Proof.
pose E' := (split_ent E) `&` (split_ent E)^-1%relation.
move=> entE z /(_ (xsection E' z))[].
  by rewrite -nbhs_entourageE; exists E' => //; exact: filterI.
move=> y; rewrite xsectionI => -[/xsectionP xy [_ /xsectionP yz]].
by apply/xsectionP; move: xy yz; exact: entourage_split.
Qed.

Lemma continuous_withinNx {U V : uniformType} (f : U -> V) x :
  {for x, continuous f} <-> f @ x^' --> f x.
Proof.
split=> - cfx P /= fxP.
  by rewrite !near_simpl; apply: cvg_within; apply: cfx.
rewrite !nbhs_nearE !near_map !near_nbhs in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Unshelve. all: by end_near. Qed.

Lemma continuous_injective_withinNx
  (T U : topologicalType) (f : T -> U) (x : T) :
  {for x, continuous f} ->
  (forall y, f y = f x -> y = x) -> f @ x^' --> (f x)^'.
Proof.
move=> cf fI A; rewrite /nbhs /= /dnbhs !withinE/= => -[V Vfx AV].
exists (f @^-1` V); first exact: cf Vfx.
by apply/seteqP; split=> y/=;
  move/predeqP : AV => /(_ (f y))/= AV [AVfy yx];
  have /contra_neq /(_ yx) := fI y; tauto.
Qed.

(* This property is primarily useful for metrizability on uniform spaces *)
Definition countable_uniformity (T : uniformType) :=
  exists R : set_system (T * T), [/\
    countable R,
    R `<=` entourage &
    forall P, entourage P -> exists2 Q, R Q & Q `<=` P].

Lemma countable_uniformityP {T : uniformType} :
  countable_uniformity T <-> exists2 f : nat -> set (T * T),
    (forall A, entourage A -> exists N, f N `<=` A) &
    (forall n, entourage (f n)).
Proof.
split=> [[M []]|[f fsubE entf]].
  move=> /pfcard_geP[-> _ /(_ _ (@entourageT _))[]//|/unsquash f eM Msub].
  exists f; last by move=> n; apply: eM; exact: funS.
  by move=> ? /Msub [Q + ?] => /(@surj _ _ _ _ f)[n _ fQ]; exists n; rewrite fQ.
exists (range f); split; first exact: card_image_le.
  by move=> E [n _] <-; exact: entf.
by move=> E /fsubE [n fnA]; exists (f n) => //; exists n.
Qed.

Lemma open_nbhs_entourage (U : uniformType) (x : U) (A : set (U * U)) :
  entourage A -> open_nbhs x (xsection A x)°.
Proof.
move=> entA; split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; exact: nbhs_entourage.
Qed.

Definition unif_continuous (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourage --> entourage.

Definition entourage_set (U : uniformType) (A : set ((set U) * (set U))) :=
  exists2 B, entourage B & forall PQ, A PQ -> forall p q,
    PQ.1 p -> PQ.2 q -> B (p,q).

(** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set_system T) := (F, F) --> entourage.

Lemma cvg_cauchy {T : puniformType} (F : set_system T) : Filter F ->
  [cvg F in T] -> cauchy F.
Proof.
move=> FF cvF A entA; have /entourage_split_ex [B entB sB2A] := entA.
exists (xsection (B^-1%relation) (lim F), xsection B (lim F)).
  split=> /=; apply: cvF; rewrite /= -nbhs_entourageE; last by exists B.
  by exists B^-1%relation => //; exact: entourage_inv.
move=> ab [/= /xsectionP Balima /xsectionP Blimb]; apply: sB2A.
by exists (lim F).
Qed.

HB.mixin Record Uniform_isComplete T of PointedUniform T := {
  cauchy_cvg :
    forall (F : set_system T), ProperFilter F -> cauchy F -> cvg F
}.

#[short(type="completeType")]
HB.structure Definition Complete :=
  {T of Uniform T & Uniform_isComplete T & isPointed T}.

#[deprecated(since="mathcomp-analysis 2.0", note="use cauchy_cvg instead")]
Notation complete_ax := cauchy_cvg (only parsing).

Section completeType1.

Context {T : completeType}.

Lemma cauchy_cvgP (F : set_system T) (FF : ProperFilter F) : cauchy F <-> cvg F.
Proof. by split=> [/cauchy_cvg|/cvg_cauchy]. Qed.

End completeType1.
Arguments cauchy_cvg {T} F {FF} _ : rename.
Arguments cauchy_cvgP {T} F {FF}.
