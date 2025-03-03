From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure compact weak_topology.

(**md**************************************************************************)
(* # One-Point Compactifications                                              *)
(*                                                                            *)
(* Builds the one-point compactification of a topological space `X`. The main *)
(* results are that the compactification is indeed compact, and that `X`      *)
(* embeds into its one-point compactification.                                *)
(*                                                                            *)
(*      one_point_compactification X == the one-point compactification of `X` *)
(*                                      as an alias of `option X`             *)
(******************************************************************************)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition one_point_compactification (X : Type) : Type := option X.

Section one_point_compactification.
Context {X : topologicalType}.

Local Notation opc := (one_point_compactification X).

HB.instance Definition _ := Choice.on opc.
HB.instance Definition _ := Pointed.on opc.

Definition one_point_nbhs (x : opc) : set_system opc :=
  if x is Some x' then Some @ nbhs x' else
    filter_from (compact `&` closed) (fun U => (Some @` ~`U) `|` [set None]).

Let one_point_filter (x : opc) : ProperFilter (one_point_nbhs x).
Proof.
case: x => [x|]; first exact: fmap_proper_filter.
apply: filter_from_proper; last by move=> ? _; exists None; right.
apply: filter_from_filter.
  by exists set0; split; [exact: compact0 | exact: closed0].
move=> P Q [cptP cloP] [cptQ cloQ]; exists (P `|` Q).
- by split; [exact: compactU | exact: closedU].
- case=> [x [|//]|[] //= _]; [|by split; right..].
  by move=> [a /not_orP[Pa Qa]] [<-{x}]; split => //; left; exists a.
Qed.

Let one_point_singleton (x : opc) U : one_point_nbhs x U -> U x.
Proof. by case: x => [x' /= /nbhs_singleton//|[W _]]; apply; right. Qed.

Let one_point_nbhs_nbhs (p : opc) (A : set opc) :
  one_point_nbhs p A -> one_point_nbhs p (one_point_nbhs^~ A).
Proof.
case: p => [r /=|].
  rewrite nbhs_simpl nbhsE => -[U [oU Ur] USA/=].
  by exists U => //= z /=; rewrite nbhs_simpl nbhsE => Uz; exists U.
case=> C [cptC cloC] nCA /=; exists C => // -[|_]; last by exists C.
move=> x [|//] [y] /[swap] -[-> /=] nCx; rewrite nbhs_simpl nbhsE/=.
exists (~` C); first by split => //; exact: closed_openC.
by move=> z /= nCz; apply: nCA; left.
Qed.

HB.instance Definition _ := hasNbhs.Build opc one_point_nbhs.

HB.instance Definition _ := @Nbhs_isNbhsTopological.Build opc
  one_point_filter one_point_singleton one_point_nbhs_nbhs.

Lemma one_point_compactification_compact : compact [set: opc].
Proof.
apply/compact_near_coveringP => ? F /= P FF FT.
have [[U i] [[W [cptW cW] /= WU nFi UiP]]] := FT None I.
have P'F x : W x -> \near x & F, P F (Some x).
  move=> Wx; suff: \forall y \near Some @ x & f \near id @ F, P f y.
    by rewrite near_map2.
  exact: FT (Some x) I.
move/compact_near_coveringP/(_ _ F _ FF P'F) : cptW => cWP.
near=> j => z _; case: z => [z|].
- have [?|Wz] := pselect (W z); first exact: (near cWP).
  by apply: (UiP (_, _)); split => /=;
    [apply: WU; left; exists z|exact: (near nFi)].
- by apply: (UiP (_, _)); split => /=; [apply: WU; right|exact: (near nFi)].
Unshelve. all: by end_near. Qed.

Lemma one_point_compactification_some_nbhs (x : X) (U : set X) :
  nbhs x U -> @nbhs _ opc (Some x) (Some @` U).
Proof. exact/filterS/preimage_image. Qed.

Lemma one_point_compactification_some_continuous : continuous (Some : X -> opc).
Proof. by move=> x U. Qed.

Lemma one_point_compactification_open_some (U : set X) :
  open U -> @open opc (Some @` U).
Proof.
rewrite !openE/= => UU' opcX [x /UU' Ux <-].
exact/one_point_compactification_some_nbhs.
Qed.

Lemma one_point_compactification_weak_topology :
  @nbhs _ (@weak_topology X opc Some) = @nbhs _ X.
Proof.
rewrite predeq2E => x U; split; rewrite /(@nbhs _ (weak_topology _))/=.
  case=> _ [[/= W] oW <- /= WSs] /filterS; apply.
  exact/one_point_compactification_some_continuous/oW.
rewrite nbhsE => -[V [oV Vx VU]]; exists V; split => //.
exists (Some @` V); first exact: one_point_compactification_open_some.
by rewrite eqEsubset; split=> [y [z Vz [<-//]]|]; exact: preimage_image.
Qed.

End one_point_compactification.
