(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum vector.
From mathcomp Require Import interval_inference.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import convex set_interval reals topology num_normedtype.
From mathcomp Require Import pseudometric_normed_Zmodule.

(**md**************************************************************************)
(* # Topological vector spaces                                                *)
(*                                                                            *)
(* This file introduces locally convex topological vector spaces.             *)
(* ```                                                                        *)
(*            NbhsLmodule K == HB class, join of Nbhs and Lmodule over K      *)
(*                             K is a numDomainType.                          *)
(* preTopologicalLmodType K == topological space and Lmodule over K           *)
(*                             K is a numDomainType                           *)
(*                             The HB class is PreTopologicalLmodule.         *)
(*    topologicalLmodType K == topologicalNmodule and Lmodule over K with a   *)
(*                             continuous scaling operation                   *)
(*                             The HB class is TopologicalLmodule.            *)
(*         convexTvsType R  == interface type for a locally convex            *)
(*                             tvs on a numDomain R                           *)
(*                             A convex tvs is constructed over a uniform     *)
(*                             space.                                         *)
(*                             The HB class is ConvexTvs.                     *)
(*   subConvexTvsType R V S == join of subTopologicalType, convexTvsType,     *)
(*                             and subLmoduleType                             *)
(*                             The HB class is SubConvexTvs.                  *)
(*                             Instance: in particular, it is shown that a    *)
(*                             sub-Lmodule is a sub-convex TVS.               *)
(* PreTopologicalLmod_isConvexTvs == factory allowing the construction of a   *)
(*                             convex tvs from an Lmodule which is also a     *)
(*                             topological space                              *)
(* {linear_continuous E -> F} == the type of all linear and continuous        *)
(*                             functions between E and F, where E is a        *)
(*                             NbhsLmodule.type and F a NbhsZmodule.type over *)
(*                             a numDomainType R                              *)
(*                             The HB class is called LinearContinuous.       *)
(*                             The notation {linear_continuous E -> F | s}    *)
(*                             also exists.                                   *)
(*              lcfun E F s == membership predicate for linear continuous     *)
(*                             functions of type E -> F with scalar operator  *)
(*                             s : K -> F -> F                                *)
(*                             E and F have type convexTvsType K.             *)
(*                             This is used in particular to attach a type of *)
(*                             lmodType to {linear_continuous E -> F | s}.    *)
(*             lcfun_spec f == specification for membership of the linear     *)
(*                             continuous function f                          *)
(* ```                                                                        *)
(* HB instances:                                                              *)
(* - The type R^o (R : numFieldType) is endowed with the structure of         *)
(*   ConvexTvs.                                                               *)
(* - The product of two Tvs is endowed with the structure of ConvexTvs.       *)
(* - {linear_continuous E-> F} is endowed with a lmodType structure when E    *)
(*   and F are convexTvs.                                                     *)
(******************************************************************************)

Reserved Notation "'{' 'linear_continuous' U '->' V '|' s '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'linear_continuous'  U  ->  V  |  s }").
Reserved Notation "'{' 'linear_continuous' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
    format "{ 'linear_continuous'  U  ->  V }").

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition NbhsLmodule (K : numDomainType) :=
  {M of Nbhs M & GRing.Lmodule K M}.

#[short(type="preTopologicalLmodType")]
HB.structure Definition PreTopologicalLmodule (K : numDomainType) :=
  {M of Topological M & GRing.Lmodule K M}.

HB.mixin Record TopologicalZmodule_isTopologicalLmodule (R : numDomainType) M
    & PreTopologicalLmodule R M := {
  scale_continuous : continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

#[short(type="topologicalLmodType")]
HB.structure Definition TopologicalLmodule (K : numDomainType) :=
  {M of TopologicalZmodule M & GRing.Lmodule K M
        & TopologicalZmodule_isTopologicalLmodule K M}.

Section TopologicalLmodule_theory.
Context {R : numFieldType} (E : topologicalType) (F : topologicalLmodType R).

Lemma fun_cvgZ (U : set_system E) {FF : Filter U} (l : E -> R) (f : E -> F)
    (r : R) a :
  l @ U --> r -> f @ U --> a ->
  l x *: f x @[x --> U] --> r *: a.
Proof.
by move=> *; apply: continuous2_cvg => //; exact: (scale_continuous (_, _)).
Qed.

Lemma fun_cvgZr (U : set_system E) {FF : Filter U} k (f : E -> F) a :
  f @ U --> a -> k \*: f @ U --> k *: a.
Proof. by apply: fun_cvgZ => //; exact: cvg_cst. Qed.

End TopologicalLmodule_theory.

HB.factory Record TopologicalNmodule_isTopologicalLmodule (R : numDomainType) M
    & PreTopologicalLmodule R M := {
  scale_continuous : continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.builders Context R M & TopologicalNmodule_isTopologicalLmodule R M.

Let opp_continuous : continuous (-%R : M -> M).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => -1 *: x)); first by move=> y; rewrite scaleN1r.
rewrite -[- x]scaleN1r.
apply: (@continuous_comp M (R^o * M)%type M (fun x => (-1, x))
  (fun x => x.1 *: x.2)); last exact: scale_continuous.
by apply: (@cvg_pair _ _ _ _ (nbhs (-1 : R^o))); [exact: cvg_cst|exact: cvg_id].
Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build M opp_continuous.
HB.instance Definition _ :=
  TopologicalZmodule_isTopologicalLmodule.Build R M scale_continuous.

HB.end.

HB.mixin Record Uniform_isConvexTvs (R : numDomainType) E
    & Uniform E & GRing.Lmodule R E := {
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> convex_set b) & basis B
}.

#[short(type="convexTvsType")]
HB.structure Definition ConvexTvs (R : numDomainType) :=
  {E of Uniform_isConvexTvs R E & UniformZmodule E & TopologicalLmodule R E}.

#[short(type="subConvexTvsType")]
HB.structure Definition SubConvexTvs (R : numDomainType) (V : convexTvsType R)
    (S : pred V) :=
  { U of SubTopological V S U & ConvexTvs R U & @GRing.SubLmodule R V S U }.

Section SubLmodule_isSubConvexTvs.
Context (R : numFieldType) (V : convexTvsType R) (S : pred V) (U : subLmodType S).

Local Notation sub_init_topo := (sub_initial_topology U).
HB.instance Definition _ := Uniform.on sub_init_topo.
HB.instance Definition _ := GRing.Lmodule.on sub_init_topo.

Let add_sub: continuous (fun x : sub_init_topo * sub_init_topo => x.1 + x.2).
Proof.
apply: continuous_comp_initial => -[/= x y].
pose h := fun xy : U * U => (\val xy.1, \val xy.2).
pose g := fun xy : V * V => xy.1 + xy.2.
rewrite (_ : _ \o _ = g \o h).
  by apply/funext => i /=; rewrite GRing.valD.
apply: continuous_comp; last exact: add_continuous.
apply: cvg_pair => //=.
- apply: (cvg_comp _ _ cvg_fst).
  exact: (continuous_valE (x : sub_init_topo)).
- apply: (cvg_comp _ _ cvg_snd).
  exact: (continuous_valE (y : sub_init_topo)).
Qed.

HB.instance Definition _ :=
  @PreTopologicalNmodule_isTopologicalNmodule.Build sub_init_topo add_sub.

Let opp_sub : continuous (-%R : sub_init_topo -> sub_init_topo).
Proof.
apply: continuous_comp_initial => x.
rewrite (_ : _ \o _ = -%R \o \val).
  by apply/funext=> i /=; rewrite GRing.valN.
apply: continuous_comp; first exact: continuous_valE.
exact: opp_continuous.
Qed.

HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build sub_init_topo opp_sub.

Let scale_sub : continuous (fun z : R^o * sub_init_topo => z.1 *: z.2).
Proof.
apply: continuous_comp_initial => - [] /= x /= y.
pose h := fun xy : R * U => (xy.1, \val xy.2).
pose g := fun xy : R * V => xy.1 *: xy.2.
rewrite (_ : _ \o _ = g \o h); first by apply/funext=> i /=; rewrite GRing.valZ.
apply: continuous_comp; last exact: scale_continuous.
move=> /= A [/= [/= B C]] [[r/= r0 xrB]].
move/(continuous_valE (y : sub_init_topo)) => [/= C' [woC' C'y C'C] BCA].
apply: filterS; first exact: BCA.
exists (ball x r, C') => /=.
  by split; [exact: nbhsx_ballx|exists C'; split].
by move=> su/= [xru C'u]; split; [exact: xrB|exact: C'C].
Qed.

HB.instance Definition _ :=
  TopologicalZmodule_isTopologicalLmodule.Build R sub_init_topo scale_sub.

Let add_unif_continuous :
  unif_continuous (fun x : sub_init_topo * sub_init_topo => x.1 + x.2).
Proof.
apply/initial_unif_continuous_comp.
rewrite (_ : _ \o _ = (fun x => x.1 + x.2) \o (fun x => (val x.1, val x.2)))/=.
  by apply/funext => x/=; exact: linearD.
apply: unif_continuous_comp; last exact: add_unif_continuous.
by apply: pair_unif_continuous => //=;
  [exact: initial_unif_continuous_comp_fst|
   exact: initial_unif_continuous_comp_snd].
Qed.

HB.instance Definition _ :=
  PreUniformNmodule_isUniformNmodule.Build sub_init_topo add_unif_continuous.

Let opp_unif_continuous : unif_continuous (-%R : sub_init_topo -> sub_init_topo).
Proof.
apply/initial_unif_continuous_comp.
rewrite (_ : _ \o _ = (fun x => - x) \o val)/=.
  by apply/funext => x/=; exact: linearN.
by apply: unif_continuous_comp;
  [exact: initial_unif_continuous|exact: opp_unif_continuous].
Qed.

HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build sub_init_topo opp_unif_continuous.

Local Open Scope convex_scope.

Let locally_convex_sub : exists2 B : set_system sub_init_topo,
  (forall b, b \in B -> convex_set b) & basis B.
Proof.
have [B convexB [openB/= genB]] := @locally_convex R V.
exists [set a | exists2 b, B b & \val @^-1` b = a].
  move=> a /[!inE]/= -[b Bb ba] r s l ra sa.
  suff : \val (r <|l|> s) \in b by rewrite !inE /= -ba.
  rewrite !GRing.valD !GRing.valZ convexB//; first exact: mem_set.
  - by move: ra; rewrite -ba !inE.
  - by move: sa; rewrite -ba !inE.
split => /=.
  move=> a/= [b Bb <-]; rewrite /open/= /initial_open/=; exists b => //.
  exact: openB.
move=> x a [/= b [[/=c openc] cb bx ba]].
rewrite /nbhs/= /filter_from/=.
have : nbhs (val x) c.
 rewrite nbhsE /=; exists c => //; split => //.
 by move: bx; rewrite -cb.
move/genB => [d [Bd dx dc]].
exists (\val @^-1` d); first by split => //; exists d.
by move=> y dy; apply: ba; rewrite -cb; exact: dc.
Qed.

Local Close Scope convex_scope.

HB.instance Definition _ :=
  @Uniform_isConvexTvs.Build R sub_init_topo locally_convex_sub.
HB.instance Definition _ := GRing.SubLmodule.on sub_init_topo.

End SubLmodule_isSubConvexTvs.

Section properties_of_topologicalLmodule.
Context (R : numDomainType) (E : preTopologicalLmodType R) (U : set E).

Lemma nbhsN_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) (x : E) :
  nbhs x U -> nbhs (-x) (-%R @` U).
Proof.
move=> Ux; move: (f (-1, -x) U); rewrite /= scaleN1r opprK => /(_ Ux) [] /=.
move=> [B] B12 [B1 B2] BU; near=> y; exists (- y); rewrite ?opprK// -scaleN1r//.
apply: (BU (-1, y)); split => /=; last by near: y.
by move: B1 => [] ? ?; apply => /=; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma nbhs0N_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) :
  nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by move => Ux; rewrite -oppr0; exact: nbhsN_subproof. Qed.

Lemma nbhsT_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (x : E) :
  nbhs 0 U -> nbhs x (+%R x @` U).
Proof.
move => U0; have /= := f (x, -x) U; rewrite subrr => /(_ U0).
move=> [B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

Lemma nbhsB_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (z x : E) :
  nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof.
move=> U0; have /= := f (x + z, -x) U; rewrite [x + z]addrC addrK.
move=> /(_ U0)[B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

End properties_of_topologicalLmodule.

HB.factory Record PreTopologicalLmod_isConvexTvs (R : numDomainType) E
    & PreTopologicalLmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> convex_set b) & basis B
  }.

HB.builders Context R E & PreTopologicalLmod_isConvexTvs R E.

Definition entourage : set_system (E * E) :=
  fun P => exists (U : set E), nbhs (0 : E) U  /\
                     (forall xy : E * E, (xy.1 - xy.2) \in U -> xy \in P).

Let nbhs0N (U : set E) : nbhs (0 : E) U -> nbhs (0 : E) (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsN (U : set E) (x : E) : nbhs x U -> nbhs (-x) (-%R @` U).
Proof. exact/nbhsN_subproof/scale_continuous. Qed.

Let nbhsT (U : set E) (x : E) : nbhs (0 : E) U -> nbhs x (+%R x @`U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Let nbhsB (U : set E) (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

Lemma entourage_filter : Filter entourage.
Proof.
split; first by exists [set: E]; split; first exact: filter_nbhsT.
  move=> P Q; rewrite /entourage nbhsE /=.
  move=> [U [[B B0] BU Bxy]] [V [[C C0] CV Cxy]].
  exists (U `&` V); split => [|xy].
    by exists (B `&` C); [exact: open_nbhsI|exact: setISS].
  by rewrite !in_setI => /andP[/Bxy-> /Cxy->].
by move=> P Q PQ [U [HU Hxy]]; exists U; split=> [|xy /Hxy /[!inE] /PQ].
Qed.

Let entourage_refl (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
move=> [U [U0 Uxy]] xy eq_xy; apply/set_mem/Uxy; rewrite eq_xy subrr.
apply/mem_set; exact: nbhs_singleton.
Qed.

Let entourage_inv (A : set (E * E)) :
  entourage A -> entourage A^-1%relation.
Proof.
move=> [/= U [U0 Uxy]]; exists (-%R @` U); split; first exact: nbhs0N.
move=> xy /set_mem /=; rewrite -opprB => [[yx] Uyx] /oppr_inj yxE.
by apply/Uxy/mem_set; rewrite /= -yxE.
Qed.

Let entourage_split_ex (A : set (E * E)) : entourage A ->
  exists2 B : set (E * E), entourage B & (B \; B)%relation `<=` A.
Proof.
move=> [/= U] [U0 Uxy]; rewrite /entourage /=.
have := @add_continuous (0, 0); rewrite /continuous_at/= addr0 => /(_ U U0)[]/=.
move=> [W1 W2] []; rewrite nbhsE/= => [[U1 nU1 UW1] [U2 nU2 UW2]] Wadd.
exists [set w | (W1 `&` W2) (w.1 - w.2)].
  exists (W1 `&` W2); split; last by [].
  exists (U1 `&` U2); first exact: open_nbhsI.
  by move=> t [U1t U2t]; split; [exact: UW1|exact: UW2].
move => xy /= [z [H1 _] [_ H2]]; apply/set_mem/(Uxy xy)/mem_set.
rewrite [_ - _](_ : _ = (xy.1 - z) + (z - xy.2)); first by rewrite addrA subrK.
exact: (Wadd (xy.1 - z,z - xy.2)).
Qed.

Let nbhsE : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_ /=; apply/funext => x; rewrite /filter_from/=.
apply/funext => U; apply/propext => /=; rewrite /entourage /=; split.
- pose V : set E := [set v | x - v \in U].
  move=> nU; exists [set xy | xy.1 - xy.2 \in V]; last first.
    by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrC subrK inE.
  exists V; split; last by move=> xy; rewrite !inE /= inE.
  have /= := nbhsB x (nbhsN nU); rewrite subrr /= /V.
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U])//.
  apply/funext => /= v /=; rewrite inE; apply/propext; split.
    by move=> [x0 [x1]] Ux1 <- <-; rewrite opprB addrC subrK.
  move=> Uxy; exists (v - x); last by rewrite addrC subrK.
  by exists (x - v); rewrite ?opprB.
- move=> [A [U0 [nU UA]] H]; near=> z; apply: H; apply/xsectionP/set_mem/UA.
  near: z; rewrite nearE; have := nbhsT x (nbhs0N nU).
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U0])//.
  apply/funext => /= z /=; apply/propext; split.
    by move=> [x0] [x1 Ux1 <-] <-; rewrite opprB addrC subrK inE.
  rewrite inE => Uxz; exists (z - x); last by rewrite addrC subrK.
  by exists (x - z); rewrite ?opprB.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl
    entourage_inv entourage_split_ex
    nbhsE.

HB.instance Definition _ := PreTopologicalNmodule_isTopologicalNmodule.Build E add_continuous.

HB.instance Definition _ := TopologicalNmodule_isTopologicalLmodule.Build R E scale_continuous.

Let nbhs0_split (U : set E) : nbhs 0 U ->
  exists2 V : set E, nbhs 0 V & forall u v, V u -> V v -> U (u + v).
Proof.
move=> U0.
have : nbhs ((0 : E, 0 : E).1 + (0 : E, 0 : E).2) U.
  by rewrite /= add0r.
move/add_continuous => [[/= A B] [A0 B0] ABU].
exists (A `&` B); first exact: filterI A0 B0.
move=> u v [Au _] [_ Bv].
exact: (ABU (u, v)).
Qed.

Let add_unif_continuous : unif_continuous (fun x : E * E => x.1 + x.2).
Proof.
move=> P /= [U [U0 UP]].
have [V V0 VU] := nbhs0_split U0.
pose A := [set x | x.1 - x.2 \in V].
have entA : @entourage A by exists V; split=> // x xV; rewrite /A inE.
exists (A, A) => //=.
move=> -[[x1 y1] [x2 y2]] /= [Ax Ay].
exists ((x1, x2), (y1, y2)) => //=.
apply/set_mem/UP => /=.
rewrite /= opprD addrACA inE.
by apply: VU; [exact/set_mem/Ax|exact/set_mem/Ay].
Qed.

HB.instance Definition _ :=
  PreUniformNmodule_isUniformNmodule.Build E add_unif_continuous.

Let opp_unif_continuous : unif_continuous (-%R : E -> E).
Proof.
move=> P /= [U [U0 UP]].
exists [set z | U (- z)]; split.
  have /opp_continuous : nbhs (- 0) U by rewrite oppr0.
  exact.
move=> [x y] /= Uxy.
apply: UP => /=.
by rewrite -opprD.
Qed.

HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build E opp_unif_continuous.

HB.instance Definition _ := Uniform_isConvexTvs.Build R E locally_convex.

HB.end.

Section ConvexTvs_numDomain.
Context {R : numDomainType} (E : convexTvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @` U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

End ConvexTvs_numDomain.

Lemma nbhsB {R : numDomainType} {E : topologicalLmodType R} (U : set E)
    (z x : E) :
  nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

(* NB: similar to nbhsDl *)
Lemma near_shiftE (R : numDomainType) (E : topologicalLmodType R) (U : set E) (x a : E) :
  (\forall y \near x + a, U y) = (\near x, U (x + a)).
Proof.
eqProp; rewrite -!nbhs_nearE.
- move/(nbhsB (-a)).
  rewrite addrC addrK.
  apply: filterS => _ [y Uy <-].
  by rewrite addrC addNKr.
- move/(nbhsB a); rewrite addrC.
  apply: filterS => ? [y Uya <-].
  by rewrite addrC.
Qed.

Section ConvexTvs_numField.

Lemma nbhs0Z (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous (r^-1, 0) U.
rewrite scaler0 => /(_ U0)[]/= B [B1 B2] BU.
near=> x => //=; exists (r^-1 *: x); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1, x)); split => //=;[exact: nbhs_singleton|near: x].
Unshelve. all: by end_near. Qed.

Lemma nbhsZ (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous ((r^-1, r *: x)) U.
rewrite scalerA mulVf// scale1r =>/(_ U0)[] /= B [B1 B2] BU.
near=> z; exists (r^-1 *: z); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1,z)); split; [exact: nbhs_singleton|near: z].
Unshelve. all: by end_near. Qed.

Lemma nearZE (R : numFieldType) (T : convexTvsType R) (c : R) (x : T) (P : set T) :
  c != 0 -> (\forall y \near c *: x, P y) = (\near x, P (c *: x)).
Proof.
move=> c_neq0.
have cinv_neq0 : c^-1 != 0 by apply: invr_neq0.
eqProp.
- move/(nbhsZ cinv_neq0).
  rewrite scalerK//.
  apply: filterS => ? [y Py <-].
  by rewrite scalerKV.
- move/(nbhsZ c_neq0).
  by apply: filterS => ? [y Pcy <-].
Qed.

End ConvexTvs_numField.

Section standard_topology.
Context {R : numFieldType}.

Local Open Scope convex_scope.

Let standard_ball_convex_set (x : R^o) (r : R) : convex_set (ball x r).
Proof.
apply/convex_setW => z y; rewrite !inE -!ball_normE /= => zx yx l l0 l1.
rewrite inE/=.
rewrite [X in `|X|](_ : _ = (x - z : convex_lmodType _) <| l |>
                            (x - y : convex_lmodType _)).
  by rewrite opprD -[in LHS](convmm l x) addrACA -scalerBr -scalerBr.
rewrite (le_lt_trans (ler_normD _ _))// !normrM.
rewrite (@ger0_norm _ l%:num)// (@ger0_norm _ l%:num.~) ?onem_ge0//.
rewrite -[ltRHS]mul1r -(add_onemK l%:num) [ltRHS]mulrDl.
by rewrite ltrD// ltr_pM2l// onem_gt0.
Qed.

Let standard_locally_convex_set :
  exists2 B : set_system R^o, (forall b, b \in B -> convex_set b) & basis B.
Proof.
exists [set B | exists x r, B = ball x r].
  by move=> B/= /[!inE]/= [[x]] [r] ->; exact: standard_ball_convex_set.
split; first by move=> B [x] [r] ->; exact: ball_open.
move=> x B; rewrite -nbhs_ballE/= => -[r] r0 Bxr /=.
by exists (ball x r) => //=; split; [exists x, r|exact: ballxx].
Qed.

HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalLmodule.Build R R^o standard_scale_continuous.

HB.instance Definition _ :=
  Uniform_isConvexTvs.Build R R^o standard_locally_convex_set.

End standard_topology.

Section prod_ConvexTvs.
Context (K : numFieldType) (E F : convexTvsType K).

Local Lemma prod_scale_continuous :
  continuous (fun z : K^o * (E * F) => z.1 *: z.2).
Proof.
move => [/= r [x y]] /= U /= []/= [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @scale_continuous K E (r, x) _ nA.
have [/= B0 [B01 B02] nB1] := @scale_continuous K F (r, y) _ nB .
exists (A0.1 `&` B0.1, A0.2 `*` B0.2).
  by split; [exact: filterI|exists (A0.2,B0.2)].
by move=> [l [e f]] /= [] [Al Bl] [] Ae Be; apply: nU; split;
  [exact: (nA1 (l, e))|exact: (nB1 (l, f))].
Qed.

Local Lemma prod_locally_convex :
  exists2 B : set_system (E * F), (forall b, b \in B -> convex_set b) & basis B.
Proof.
have [Be Bcb Beb] := @locally_convex K E.
have [Bf Bcf Bfb] := @locally_convex K F.
pose B := [set ef : set (E * F) | open ef /\
  exists be, exists2 bf, Be be & Bf bf /\ be `*` bf = ef].
have : basis B.
  rewrite /basis/=; split; first by move=> b => [] [].
  move=> /= [x y] ef [[ne nf]] /= [Ne Nf] Nef.
  case: Beb => Beo /(_ x ne Ne) /= -[a] [] Bea ax ea.
  case: Bfb => Bfo /(_ y nf Nf) /= -[b] [] Beb yb fb.
  exists [set z | a z.1 /\ b z.2]; last first.
    by apply: subset_trans Nef => -[zx zy] /= [] /ea + /fb.
  split=> //=; split; last by exists a, b.
  rewrite openE => [[z z'] /= [az bz]]; exists (a, b) => /=; last by [].
  rewrite !nbhsE /=; split; first by exists a => //; split => //; exact: Beo.
  by exists b => //; split => // []; exact: Bfo.
exists B => // => b; rewrite inE /= => [[]] bo [] be [] bf Bee [] Bff <-.
move => [x1 y1] [x2 y2] l /[!inE] /= -[xe1 yf1] [xe2 yf2].
split.
  by apply/set_mem/Bcb; [exact/mem_set|exact/mem_set|exact/mem_set].
by apply/set_mem/Bcf; [exact/mem_set|exact/mem_set|exact/mem_set].
Qed.

HB.instance Definition _ := TopologicalNmodule_isTopologicalLmodule.Build
  K (E * F)%type prod_scale_continuous.

HB.instance Definition _ :=
  Uniform_isConvexTvs.Build K (E * F)%type prod_locally_convex.

End prod_ConvexTvs.

HB.structure Definition LinearContinuous (K : numDomainType) (E : NbhsLmodule.type K)
  (F : NbhsZmodule.type) (s : K -> F -> F) :=
  {f of @GRing.Linear K E F s f &  @Continuous E F f }.

(* https://github.com/math-comp/math-comp/issues/1536
   we use GRing.Scale.law even though it is claimed to be internal *)
HB.factory Structure isLinearContinuous (K : numDomainType) (E : NbhsLmodule.type K)
  (F : NbhsZmodule.type) (s : GRing.Scale.law K F) (f : E -> F) := {
    linearP : linear_for s f ;
    continuousP : continuous f
  }.

HB.builders Context K E F s f & @isLinearContinuous K E F s f.

HB.instance Definition _ := GRing.isLinear.Build K E F s f linearP.
HB.instance Definition _ := isContinuous.Build E F f continuousP.

HB.end.

Section lcfun_pred.
Context  {K : numDomainType} {E : NbhsLmodule.type K}  {F : NbhsZmodule.type}
  {s : K -> F -> F}.

Definition lcfun : {pred E -> F} :=
  mem [set f | linear_for s f /\ continuous f].

Definition lcfun_key : pred_key lcfun. Proof. exact. Qed.

Canonical lcfun_keyed := KeyedPred lcfun_key.

End lcfun_pred.

Notation "{ 'linear_continuous' U -> V | s }" :=
  (@LinearContinuous.type _ U%type V%type s) : type_scope.
Notation "{ 'linear_continuous' U -> V }" :=
  {linear_continuous U%type -> V%type | *:%R} : type_scope.

Section lcfun.
Context {R : numDomainType} {E : NbhsLmodule.type R}
  {F : NbhsZmodule.type} {s : GRing.Scale.law R F}.

Notation T := {linear_continuous E -> F | s}.

Notation lcfun := (@lcfun _ E F s).

Section Sub.
Context (f : E -> F) (fP : f \in lcfun).

#[local] Definition lcfun_Sub_subproof :=
  @isLinearContinuous.Build _ E F s f (proj1 (set_mem fP)) (proj2 (set_mem fP)).

#[local] HB.instance Definition _ := lcfun_Sub_subproof.

Definition lcfun_Sub : {linear_continuous _  -> _ | _ } := f.

End Sub.

Let lcfun_rect (K : T -> Type) :
  (forall f (Pf : f \in lcfun), K (lcfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2] [Pf3]]].
set G := (G in K G).
have Pf : f \in lcfun.
  by rewrite inE /=; split => // x u v; rewrite Pf1 Pf2.
suff -> : G = lcfun_Sub Pf by apply: Ksub.
rewrite {}/G.
congr (LinearContinuous.Pack (LinearContinuous.Class _ _ _)).
- by congr GRing.isNmodMorphism.Axioms_; exact: Prop_irrelevance.
- by congr GRing.isScalable.Axioms_; exact: Prop_irrelevance.
- by congr isContinuous.Axioms_; exact: Prop_irrelevance.
Qed.

Let lcfun_valP f (Pf : f \in lcfun) : lcfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T lcfun_rect lcfun_valP.

Lemma lcfun_eqP (f g : {linear_continuous E -> F | s}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {linear_continuous E -> F | s} by <:].

Variant lcfun_spec (f : E -> F) : (E -> F) -> bool -> Type :=
| Islcfun (l : {linear_continuous E -> F | s}) : lcfun_spec f l true.

Lemma lcfunP (f : E -> F) : f \in lcfun -> lcfun_spec f f (f \in lcfun).
Proof.
move=> /[dup] f_lc ->.
have {2}-> : f = lcfun_Sub f_lc by rewrite lcfun_valP.
by constructor.
Qed.

End lcfun.

Section lcfun_comp.
Context {R : numDomainType} {E F : NbhsLmodule.type R}
  {S : NbhsZmodule.type} {s : GRing.Scale.law R S}
  (f : {linear_continuous E -> F}) (g : {linear_continuous F -> S | s}).

#[local] Lemma lcfun_comp_subproof1 : linear_for s (g \o f).
Proof. by move=> *; move=> *; rewrite !linearP. Qed.

#[local] Lemma lcfun_comp_subproof2 : continuous (g \o f).
Proof. by move=> x; apply: continuous_comp; exact/continuous_fun. Qed.

HB.instance Definition _ := @isLinearContinuous.Build R E S s (g \o f)
  lcfun_comp_subproof1 lcfun_comp_subproof2.

End lcfun_comp.

Section lcfun_lmodtype.
Import GRing.Theory.
Context {R : numFieldType} {E F : convexTvsType R}.
Implicit Types (r : R) (f g : {linear_continuous E -> F}).

Lemma null_fun_continuous : continuous (\0 : E -> F).
Proof. by apply: cst_continuous. Qed.

HB.instance Definition _ := isContinuous.Build E F \0 null_fun_continuous.

#[local] Lemma lcfun_continuousD f g : continuous (f \+ g).
Proof. by move=> /= x; apply: cvgD; exact: continuous_fun. Qed.

HB.instance Definition _ f g :=
  isContinuous.Build E F (f \+ g) (@lcfun_continuousD f g).

#[local] Lemma lcfun_continuousN f : continuous (\- f).
Proof. by move=> /= x; apply: cvgN; exact: continuous_fun. Qed.

HB.instance Definition _ f :=
  isContinuous.Build E F (\- f) (@lcfun_continuousN f).

#[local] Lemma lcfun_continuousM r g : continuous (r \*: g).
Proof. by move=> /= x; apply: fun_cvgZr; exact: continuous_fun. Qed.

HB.instance Definition _ r g :=
  isContinuous.Build E F (r \*: g) (@lcfun_continuousM r g).

#[local] Lemma lcfun_submod_closed : submod_closed (@lcfun R E F *:%R).
Proof.
split; first by rewrite inE; split; first apply/linearP; exact: cst_continuous.
move=> r /= _ _  /lcfunP[f] /lcfunP[g].
by rewrite inE /=; split; [exact: linearP | exact: lcfun_continuousD].
Qed.

HB.instance Definition _ :=
  @GRing.isSubmodClosed.Build _  _ lcfun lcfun_submod_closed.

HB.instance Definition _ :=
  [SubChoice_isSubLmodule of {linear_continuous E -> F } by <:].

End lcfun_lmodtype.

Section lcfunproperties.
Context {R : numDomainType} {E F : NbhsLmodule.type R}
  (f : {linear_continuous E -> F}).

#[warn(note="Consider using `continuous_fun` instead.",cats="discoverability")]
Lemma lcfun_continuous : continuous f.
Proof. exact: continuous_fun. Qed.

#[warn(note="Consider using `linearP` instead.",cats="discoverability")]
Lemma lcfun_linear : linear f.
Proof. move => *; exact: linearP. Qed.

End lcfunproperties.
