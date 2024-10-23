From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import signed topology_structure uniform_structure.
From mathcomp Require Import pseudometric_structure compact weak_topology.

(**md**************************************************************************)
(* # One Point Compactifications                                              *)
(*                                                                            *)
(* Builds the one point compactification of a topological space `X`. The main *)
(* results are that the compactification is indeed compact, and that `X`      *)
(* embeds into its one point compactification                                 *)
(*                                                                            *)
(*      one_point_compactification X == the one point compactification of `X` *)
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
case: x; first by move=>?; exact: fmap_proper_filter. 
apply: filter_from_proper; last by move=> ? _; exists None; right.
apply: filter_from_filter.
  by exists set0; split; [exact: compact0 | exact: closed0].
move=> P Q [? ?] [? ?]; exists (P `|` Q); last case.
- by split; [exact: compactU | exact: closedU].
- by move=> ? []// [a /not_orP [? ?]] /Some_inj <-; split=>//; left; exists a.
- by case => //= _; split; right.
Qed.

Let one_point_singleton (x : opc) U : one_point_nbhs x U -> U x.
Proof.
case: x; first by move=> x' /= /nbhs_singleton.
by case=> W _; apply; right.
Qed.

Let one_point_nbhs_nbhs (p : opc) (A : set opc) : 
  one_point_nbhs p A -> one_point_nbhs p (one_point_nbhs^~ A).
Proof.
case: p.
  move=> r /=; rewrite nbhs_simpl nbhsE; case => U [oU Ur] UsA /=.
  by exists U => //= z /=; rewrite nbhs_simpl => Uz; rewrite nbhsE; exists U.
case => C [? ?] nCA /=; exists C => //; case; last by move=> _; exists C.
move=> x [] // [] y /[swap] /Some_inj -> /= nCx; rewrite nbhs_simpl.
rewrite nbhsE; exists (~` C); first by split => //; apply/closed_openC.
by move=> z /= nCz; apply nCA; left.
Qed.

HB.instance Definition _ := hasNbhs.Build opc one_point_nbhs.

HB.instance Definition _ := @Nbhs_isNbhsTopological.Build opc 
  one_point_filter one_point_singleton one_point_nbhs_nbhs.

Lemma one_point_compactification_compact : compact [set: opc].
Proof.
apply/compact_near_coveringP => ? F /= P FF FT.
have [//| [U i [[W /= [cptW cW WU nfI UIP]]]]] := FT None.
have P'F : forall x, W x -> \near x & F, P F (Some x).
  move=> x Wx; suff : \forall y \near Some @ x & f \near id @ F, P f y.
    by rewrite near_map2.
  exact: FT (Some x) I.
move/compact_near_coveringP/(_ _ F _ FF P'F):cptW => cWP.
near=> j => z _; case: z; first last.
  apply: (UIP (None,j)); split => //=; first by apply: WU; right.
  exact: (near nfI _).
move=> z; case: (pselect (W z)); first by move=> ?; exact: (near cWP).
move=> ?; apply: (UIP (Some z,j)); split => //=. 
  by apply: WU; left; exists z.
exact: (near nfI _).
Unshelve. all: by end_near. Qed.

Lemma one_point_compactification_some_nbhs (x : X) (U : set X) : 
  nbhs x U -> @nbhs _ opc (Some x) (Some @` U).
Proof.
rewrite {2}/nbhs /= nbhs_simpl /= => /filterS; apply; exact: preimage_image.
Qed.

Lemma one_point_compactification_some_continuous : continuous (Some : X -> opc).
Proof. by move=> x U. Qed.

Lemma one_point_compactification_open_some (U : set X) : 
  open U -> @open opc (Some @` U).
Proof.
rewrite ?openE /= => Uo ? /= [x /[swap] <- Ux] /=. 
by apply: one_point_compactification_some_nbhs; apply: Uo.
Qed.

Lemma one_point_compactification_weak_topology : 
  @nbhs _ (@weak_topology X opc Some) = @nbhs _ X.
Proof. 
rewrite funeq2E=> x U; apply/propeqP; split; rewrite /(@nbhs _ (weak_topology _)) /=.
  case => V [[/= W] oW <- /= Ws] /filterS; apply. 
  by apply: one_point_compactification_some_continuous; exact: oW.
rewrite nbhsE; case => V [? ? ?]; exists V; split => //.
exists (Some @` V); first exact: one_point_compactification_open_some.
rewrite eqEsubset; split => z /=; first by case=> ? /[swap] /Some_inj ->.
by move=> ?; exists z.
Qed.

End one_point_compactification.