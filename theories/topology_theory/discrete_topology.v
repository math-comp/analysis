From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical all_reals.
From mathcomp Require Import topology_structure uniform_structure.
From mathcomp Require Import order_topology pseudometric_structure compact.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


HB.mixin Record Discrete_ofNbhs T of Nbhs T := {
  nbhs_principalE : (@nbhs T _) = principal_filter;
}.

#[short(type="discreteNbhsType")]
HB.structure Definition DiscreteNbhs := {T of Nbhs T & Discrete_ofNbhs T}.


Definition discrete_ent {T} : set (set (T * T)) :=
  globally (range (fun x => (x, x))).

(** Note: having the discrete topology does not guarantee the discrete 
    uniformity. Likewise for the discrete metric. Consider [set 1/n | n in R] *)
HB.mixin Record Discrete_ofUniform T of Uniform T := {
  uniform_discrete : @entourage T = discrete_ent
}.

Definition discrete_ball {R : numDomainType} {T} (x : T) (eps : R) y : Prop := x = y.

HB.mixin Record Discrete_ofPseudometric {R : numDomainType} T of 
    PseudoMetric R T := {
  metric_discrete : @ball R T = @discrete_ball R T
}.

#[short(type="discreteTopologicalType")]
HB.structure Definition DiscreteTopology := 
  { T of DiscreteNbhs T & Topological T}.

#[short(type="discreteOrderTopologicalType")]
HB.structure Definition DiscreteOrderTopology d := 
  { T of Discrete_ofNbhs T & OrderTopological d T}.

#[short(type="pdiscreteTopologicalType")]
HB.structure Definition PointedDiscreteTopology := 
  { T of DiscreteTopology T & Pointed T}.

#[short(type="pdiscreteOrderTopologicalType")]
HB.structure Definition PointedDiscreteOrderTopology d := 
  { T of Discrete_ofNbhs T & OrderTopological d T & Pointed T}.

#[short(type="discreteUniformType")]
HB.structure Definition DiscreteUniform := 
  { T of Discrete_ofUniform T & Uniform T & Discrete_ofNbhs T}.

#[short(type="discretePseudoMetricType")]
HB.structure Definition DiscretePseudoMetric {R : numDomainType} := 
  { T of Discrete_ofPseudometric R T & PseudoMetric R T & DiscreteUniform T}.

HB.builders Context T of Discrete_ofNbhs T.

Local Lemma principal_nbhs_filter (p : T) : ProperFilter (nbhs p).
Proof. rewrite nbhs_principalE; exact: principal_filter_proper. Qed.

Local Lemma principal_nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Proof. by rewrite nbhs_principalE => /principal_filterP. Qed.

Local Lemma principal_nbhs_nbhs (p : T) (A : set T) : nbhs p A -> nbhs p (nbhs^~ A).
Proof. by move=> ?; rewrite {1}nbhs_principalE; apply/principal_filterP. Qed.

HB.instance Definition _ := @Nbhs_isNbhsTopological.Build T
  principal_nbhs_filter principal_nbhs_singleton principal_nbhs_nbhs.

HB.end.

HB.factory Record DiscreteUniform_ofNbhs T of Discrete_ofNbhs T & Nbhs T := {}.
HB.builders Context T of DiscreteUniform_ofNbhs T.

Local Open Scope relation_scope.

Local Notation d := (@discrete_ent T).

Local Lemma discrete_entourage_filter : Filter d.
Proof. exact: globally_filter. Qed.

Local Lemma discrete_entourage_diagonal : forall A, d A -> diagonal `<=` A.
Proof.
by move=> ? + x x12; apply; exists x.1; rewrite // {2}x12 -surjective_pairing.
Qed.

Local Lemma discrete_entourage_inv : forall A, d A -> d A^-1.
Proof. by move=> ? dA x [i _ <-]; apply: dA; exists i. Qed.

Local Lemma discrete_entourage_split_ex :
    forall A, d A -> exists2 B, d B & B \; B `<=` A.
Proof.
move=> ? dA; exists (range (fun x => (x, x))) => //.
by rewrite set_compose_diag => x [i _ <-]; apply: dA; exists i.
Qed.

Local Lemma discrete_entourage_nbhsE : (@nbhs T _) = nbhs_ d.
Proof.
rewrite funeqE => x; rewrite nbhs_principalE eqEsubset; split => U.
  move/principal_filterP => ?; exists diagonal; first by move=> ? [w _ <-]. 
  by move=> z /= /set_mem; rewrite /diagonal /= => <-.
case => w entW wU; apply/principal_filterP; apply: wU; apply/mem_set.
exact: entW.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build T
  discrete_ent 
  discrete_entourage_filter 
  discrete_entourage_diagonal 
  discrete_entourage_inv
  discrete_entourage_split_ex
  discrete_entourage_nbhsE.

HB.instance Definition _ := @Discrete_ofUniform.Build T erefl.

HB.end.

HB.factory Record DiscretePseudoMetric_ofUniform (R : numDomainType) T of 
  DiscreteUniform T := {}.

HB.builders Context R T of DiscretePseudoMetric_ofUniform R T.

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
  @Uniform_isPseudoMetric.Build R T (@discrete_ball R T) 
    discrete_ball_center discrete_ball_sym discrete_ball_triangle 
    discrete_entourageE.

Local Lemma discrete_ballE : @ball R T = @discrete_ball R T.
Proof. by rewrite funeq2E => ? ?. Qed.

HB.instance Definition _ := @Discrete_ofPseudometric.Build R T discrete_ballE.

HB.end.

(** we introducing an alias attaching discrete structures for 
    topology, uniformity, and pseudometric *)
Definition discrete_topology (T : Type) : Type := T.
HB.instance Definition _ (T : choiceType) :=
  Choice.copy (discrete_topology T) T.
HB.instance Definition _ (T : pointedType) :=
  Pointed.on (discrete_topology T).
HB.instance Definition _ (T : choiceType) :=
  hasNbhs.Build (discrete_topology T) principal_filter.
HB.instance Definition _ (T : choiceType) :=
  Discrete_ofNbhs.Build (discrete_topology T) erefl.
HB.instance Definition _ (T : choiceType) := 
  DiscreteUniform_ofNbhs.Build (discrete_topology T).
HB.instance Definition _ {R : numDomainType} (T : choiceType) := 
  @DiscretePseudoMetric_ofUniform.Build R (discrete_topology T).

Section discrete_topology.

Context {X : discreteTopologicalType}.

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
