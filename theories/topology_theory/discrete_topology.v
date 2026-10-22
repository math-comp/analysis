(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra all_classical all_reals.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import order_topology pseudometric_structure compact.

(**md**************************************************************************)
(* # Discrete Topology                                                        *)
(* ```                                                                        *)
(*              discreteNbhsType == neighborhoods are principal filters       *)
(*                  discrete_ent == entourages of the discrete uniformity     *)
(*                                  topology, equipped with the Uniform       *)
(*                                  structure                                 *)
(*                 discrete_ball == singleton balls for the discrete metric,  *)
(*                                  equipped with the Uniform structure       *)
(*       discreteTopologicalType == types with a discrete topology            *)
(*  discreteOrderTopologicalType == an order type with the discrete topology  *)
(*      pdiscreteTopologicalType == pointed type with the discrete topology   *)
(* pdiscreteOrderTopologicalType == pointed, ordered, and discrete            *)
(*           discreteUniformType == a uniform space where the diagonal is an  *)
(*                                  entourage                                 *)
(*      discretePseudoMetricType == a pseudometric space where the only balls *)
(*                                  are singletons                            *)
(*           discrete_topology T == alias attaching discrete structures for   *)
(*                                  topology, uniformity, and pseudometric    *)
(* ```                                                                        *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record Discrete_ofNbhs d T & Nbhs d T := {
  nbhs_principalE : (@nbhs _ T _) = principal_filter;
}.

#[short(type="discreteNbhsType")]
HB.structure Definition DiscreteNbhs d := {T of Nbhs d T & Discrete_ofNbhs d T}.

HB.instance Definition _ d d' (T : discreteNbhsType d) :=
  Discrete_ofNbhs.Build d' (with_fdisp d' T) nbhs_principalE.

Definition discrete_ent {T} : set_system (T * T) :=
  globally (range (fun x => (x, x))).

(** Note: having the discrete topology does not guarantee the discrete
    uniformity. Likewise for the discrete metric. Consider [set 1/n | n in R] *)
HB.mixin Record Discrete_ofUniform d T & Uniform d T := {
  uniform_discrete : @entourage _ T = discrete_ent
}.

Definition discrete_ball {R : numDomainType} {T} (x : T) (eps : R) y : Prop :=
  x = y.

HB.mixin Record Discrete_ofPseudometric d {R : numDomainType} T &
    PseudoMetric d R T := {
  metric_discrete : @ball _ R T = @discrete_ball R T
}.

#[short(type="discreteTopologicalType")]
HB.structure Definition DiscreteTopology d :=
  { T of DiscreteNbhs d T & Topological d T}.

#[short(type="discreteOrderTopologicalType")]
HB.structure Definition DiscreteOrderTopology td od :=
  { T of Discrete_ofNbhs td T & OrderTopological td od T}.

#[short(type="pdiscreteTopologicalType")]
HB.structure Definition PointedDiscreteTopology d :=
  { T of DiscreteTopology d T & Pointed T}.

#[short(type="pdiscreteOrderTopologicalType")]
HB.structure Definition PointedDiscreteOrderTopology td od :=
  { T of Discrete_ofNbhs td T & OrderTopological td od T & Pointed T}.

#[short(type="discreteUniformType")]
HB.structure Definition DiscreteUniform d :=
  { T of Discrete_ofUniform d T & Uniform d T & Discrete_ofNbhs d T}.

#[short(type="discretePseudoMetricType")]
HB.structure Definition DiscretePseudoMetric {R : numDomainType} d :=
  { T of Discrete_ofPseudometric d R T & PseudoMetric d R T 
    & DiscreteUniform d T }.

HB.saturate with_fdisp.

HB.builders Context d T & Discrete_ofNbhs d T.

Local Lemma principal_nbhs_filter (p : T) : ProperFilter (nbhs p).
Proof. rewrite nbhs_principalE; exact: principal_filter_proper. Qed.

Local Lemma principal_nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Proof. by rewrite nbhs_principalE => /principal_filterP. Qed.

Local Lemma principal_nbhs_nbhs (p : T) (A : set T) :
  nbhs p A -> nbhs p (nbhs^~ A).
Proof. by move=> ?; rewrite {1}nbhs_principalE; apply/principal_filterP. Qed.

HB.instance Definition _ := @Nbhs_isNbhsTopological.Build d T
  principal_nbhs_filter principal_nbhs_singleton principal_nbhs_nbhs.

HB.end.

HB.factory Record DiscreteUniform_ofNbhs d T 
  & Discrete_ofNbhs d T & Nbhs d T := {}.
HB.builders Context d T & DiscreteUniform_ofNbhs d T.

Local Open Scope relation_scope.

Local Notation dE := (@discrete_ent T).

Local Lemma discrete_entourage_filter : Filter dE.
Proof. exact: globally_filter. Qed.

Local Lemma discrete_entourage_diagonal : forall A, dE A -> diagonal `<=` A.
Proof.
by move=> ? + x x12; apply; exists x.1; rewrite // {2}x12 -surjective_pairing.
Qed.

Local Lemma discrete_entourage_inv : forall A, dE A -> dE A^-1.
Proof. by move=> ? dA x [i _ <-]; apply: dA; exists i. Qed.

Local Lemma discrete_entourage_split_ex :
    forall A, dE A -> exists2 B, dE B & B \; B `<=` A.
Proof.
move=> ? dA; exists (range (fun x => (x, x))) => //.
by rewrite set_compose_diag => x [i _ <-]; apply: dA; exists i.
Qed.

Local Lemma discrete_entourage_nbhsE : (@nbhs _ T _) = nbhs_ dE.
Proof.
rewrite funeqE => x; rewrite nbhs_principalE eqEsubset; split => U.
  move/principal_filterP => ?; exists diagonal; first by move=> ? [w _ <-].
  by move=> z /= /set_mem; rewrite /diagonal /= => <-.
case => w entW wU; apply/principal_filterP; apply: wU; apply/mem_set.
exact: entW.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build d T
  discrete_ent
  discrete_entourage_filter
  discrete_entourage_diagonal
  discrete_entourage_inv
  discrete_entourage_split_ex
  discrete_entourage_nbhsE.

HB.instance Definition _ := @Discrete_ofUniform.Build d T erefl.

HB.end.

HB.factory Record DiscretePseudoMetric_ofUniform d (R : numDomainType) T &
  DiscreteUniform d T := {}.

HB.builders Context d R T & DiscretePseudoMetric_ofUniform d R T.

Local Lemma discrete_ball_center x (eps : R) : 0 < eps ->
  @discrete_ball R T x eps x.
Proof. by []. Qed.

Local Lemma discrete_ball_sym (x y : T) (e : R) :
  discrete_ball x e y -> discrete_ball y e x.
Proof. by move=>->. Qed.
Local Lemma discrete_ball_triangle (x y z:T) (e1 e2 : R) :
  discrete_ball x e1 y -> discrete_ball y e2 z -> discrete_ball x (e1 + e2) z.
Proof. by move=> -> ->. Qed.

Local Lemma discrete_entourageE : entourage = entourage_ (@discrete_ball R T).
Proof.
rewrite predeqE => P; rewrite uniform_discrete; split; last first.
  by move=> dbP ? [?] _ <-; move: dbP; case => /= ? ?; apply.
move=> entP; exists 1 => //= z z12; apply: entP; exists z.1 => //.
by rewrite {2}z12 -surjective_pairing.
Qed.

HB.instance Definition _ :=
  @Uniform_isPseudoMetric.Build d R T (@discrete_ball R T)
    discrete_ball_center discrete_ball_sym discrete_ball_triangle
    discrete_entourageE.

Local Lemma discrete_ballE : @ball _ R T = @discrete_ball R T.
Proof. by rewrite funeq2E => ? ?. Qed.

HB.instance Definition _ := @Discrete_ofPseudometric.Build d R T discrete_ballE.

HB.end.

Definition discrete_topology (T : Type) : Type := T.
Fact discrete_fdisp : fdisp_t.
Proof. by []. Qed.

HB.instance Definition _ (T : choiceType) :=
  Choice.copy (discrete_topology T) T.
HB.instance Definition _ (T : pointedType) :=
  Pointed.on (discrete_topology T).
HB.instance Definition _ (T : choiceType) :=
  hasNbhs.Build discrete_fdisp (discrete_topology T) principal_filter.
HB.instance Definition _ (T : choiceType) :=
  Discrete_ofNbhs.Build _ (discrete_topology T) erefl.
HB.saturate discrete_topology.
HB.instance Definition _ (T : choiceType) :=
  DiscreteUniform_ofNbhs.Build _ (discrete_topology T).
HB.instance Definition _ {R : numDomainType} (T : choiceType) :=
  @DiscretePseudoMetric_ofUniform.Build _ R (discrete_topology T).

Section discrete_topology.

Context {d} {X : discreteTopologicalType d}.

Lemma discrete_open (A : set X) : open A.
Proof.
rewrite openE => ? ?; rewrite /interior nbhs_principalE.
exact/principal_filterP.
Qed.

Lemma discrete_set1 (x : X) : nbhs x [set x].
Proof. by apply: open_nbhs_nbhs; split => //; exact: discrete_open. Qed.

Lemma discrete_closed (A : set X) : closed A.
Proof. by rewrite -[A]setCK closedC; exact: discrete_open. Qed.

Lemma discrete_cvg (F : set_system X) (x : X) :
  Filter F -> F --> x <-> F [set x].
Proof.
rewrite nbhs_principalE nbhs_simpl; split; first by exact.
by move=> Fx U /principal_filterP ?; apply: filterS Fx => ? ->.
Qed.

End discrete_topology.
