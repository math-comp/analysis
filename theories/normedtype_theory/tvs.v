(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum vector.
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
(*              NbhsNmodule == HB class, join of Nbhs and Nmodule             *)
(*              NbhsZmodule == HB class, join of Nbhs and Zmodule             *)
(*            NbhsLmodule K == HB class, join of Nbhs and Lmodule over K      *)
(*                             K is a numDomainType.                          *)
(*    PreTopologicalNmodule == HB class, join of Topological and Nmodule      *)
(*       TopologicalNmodule == HB class, PreTopologicalNmodule with a         *)
(*                             continuous addition                            *)
(*    PreTopologicalZmodule == HB class, join of Topological and Zmodule      *)
(*      topologicalZmodType == topological abelian group                      *)
(*       TopologicalZmodule == HB class, join of TopologicalNmodule and       *)
(*                             Zmodule with a continuous opposite operator    *)
(* preTopologicalLmodType K == topological space and Lmodule over K           *)
(*                             K is a numDomainType                           *)
(*                             The HB class is PreTopologicalLmodule.         *)
(*    topologicalLmodType K == topologicalNmodule and Lmodule over K with a   *)
(*                             continuous scaling operation                   *)
(*                             The HB class is TopologicalLmodule.            *)
(*        PreUniformNmodule == HB class, join of Uniform and Nmodule          *)
(*           UniformNmodule == HB class, join of Uniform and Nmodule with a   *)
(*                             uniformly continuous addition                  *)
(*        PreUniformZmodule == HB class, join of Uniform and Zmodule          *)
(*           UniformZmodule == HB class, join of UniformNmodule and Zmodule   *)
(*                             with uniformly continuous opposite operator    *)
(*      PreUniformLmodule K == HB class, join of Uniform and Lmodule over K   *)
(*                             K is a numDomainType.                          *)
(*         UniformLmodule K == HB class, join of UniformNmodule and Lmodule   *)
(*                             with a uniformly continuous scaling operation  *)
(*                             K is a numFieldType.                           *)
(*         convexTvsType R  == interface type for a locally convex            *)
(*                             tvs on a numDomain R                           *)
(*                             A convex tvs is constructed over a uniform     *)
(*                             space.                                         *)
(*                             The HB class is ConvexTvs.                     *)
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

(* HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}. *)
(* HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}. *)
(* HB.structure Definition PointedLmodule (K : numDomainType) := *)
(*   {M of Pointed M & GRing.Lmodule K M}. *)

(* HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}. *)
(* HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}. *)
(* HB.structure Definition FilteredLmodule (K : numDomainType) := *)
(*   {M of Filtered M M & GRing.Lmodule K M}. *)
HB.structure Definition NbhsLmodule (K : numDomainType) :=
  {M of Nbhs M & GRing.Lmodule K M}.

HB.mixin Record PreTopologicalNmodule_isTopologicalNmodule M
    & PreTopologicalNmodule M := {
  add_continuous : continuous (fun x : M * M => x.1 + x.2) ;
}.

HB.structure Definition TopologicalNmodule :=
  {M of PreTopologicalNmodule M & PreTopologicalNmodule_isTopologicalNmodule M}.

Section TopologicalNmodule_theory.
Variable (E : topologicalType) (F : TopologicalNmodule.type) (U : set_system E).

(** TODO:
  We have observed one thing:
  `pseudometric_normedZmodType` is morally a `topologicalNmodule`
  but `topologicalNmodule` is defined later in `tvs.v` (which imports `pseudometric_normed_zmodule.v`).
  We think that it should be defined at the beginning of `pseudometric_normed_zmodule.v` and that
  `pseudometric_normedZmodType` should be defined using `topologicalNmodule`.
  We have realized this because of the lemmas such as `cvgD/fun_cvgD` that we needed to duplicate. *)
Lemma fun_cvgD {FF : Filter U} (f g : E -> F) a b :
  f @ U --> a -> g @ U --> b -> (f \+ g) @ U --> a + b.
Proof.
move=> fa ga.
by apply: continuous2_cvg; [exact: (add_continuous (a, b))|by []..].
Qed.

Lemma cvg_sum (I : Type) (r : seq I) (P : pred I)
    (Ff : I -> E -> F) (Fa : I -> F) :
  Filter U -> (forall i, P i -> Ff i x @[x --> U] --> Fa i) ->
  \sum_(i <- r | P i) Ff i x @[x --> U] --> \sum_(i <- r| P i) Fa i.
Proof. by move=> FF Ffa; apply: cvg_big => //; apply: add_continuous. Qed.

Lemma sum_continuous (I : Type) (r : seq I) (P : pred I) (f : I -> E -> F) :
  (forall i : I, P i -> continuous (f i)) ->
  continuous (fun x1 : E => \sum_(i <- r | P i) f i x1).
Proof. by move=> FC0; apply: continuous_big => //; apply: add_continuous. Qed.

End TopologicalNmodule_theory.

HB.mixin Record TopologicalNmodule_isTopologicalZmodule M
    & Topological M & GRing.Zmodule M := {
  opp_continuous : continuous (-%R : M -> M) ;
}.

#[short(type="topologicalZmodType")]
HB.structure Definition TopologicalZmodule :=
  {M of TopologicalNmodule M & GRing.Zmodule M
        & TopologicalNmodule_isTopologicalZmodule M}.

Section TopologicalZmoduleTheory.
Variables (M : topologicalZmodType).

Lemma sub_continuous : continuous (fun x : M * M => x.1 - x.2).
Proof.
move=> x; apply: (@continuous_comp _ _ _ (fun x => (x.1, - x.2))
  (fun x : M * M => x.1 + x.2)); last exact: add_continuous.
apply: cvg_pair; first exact: cvg_fst.
by apply: continuous_comp; [exact: cvg_snd|exact: opp_continuous].
Qed.

Lemma fun_cvgN (F : topologicalZmodType) (U : set_system M) {FF : Filter U}
    (f : M -> F) a :
  f @ U --> a -> \- f @ U --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

End TopologicalZmoduleTheory.

HB.factory Record PreTopologicalNmodule_isTopologicalZmodule M
    & Topological M & GRing.Zmodule M := {
  sub_continuous : continuous (fun x : M * M => x.1 - x.2) ;
}.

HB.builders Context M & PreTopologicalNmodule_isTopologicalZmodule M.

Let opp_continuous : continuous (-%R : M -> M).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => 0 - x)); first by move=> y; exact: add0r.
rewrite -[- x]add0r.
apply: (@continuous_comp _ _ _ (fun x => (0, x)) (fun x : M * M => x.1 - x.2)).
  by apply: cvg_pair => /=; [exact: cvg_cst|exact: cvg_id].
exact: sub_continuous.
Qed.

Let add_continuous : continuous (fun x : M * M => x.1 + x.2).
Proof.
move=> x; rewrite /continuous_at.
rewrite -(@eq_cvg _ _ _ (fun x => x.1 - (- x.2))).
  by move=> y; rewrite opprK.
rewrite -[in x.1 + _](opprK x.2).
apply: (@continuous_comp _ _ _ (fun x => (x.1, - x.2)) (fun x => x.1 - x.2)).
  apply: cvg_pair; first exact: cvg_fst.
  by apply: continuous_comp; [exact: cvg_snd|exact: opp_continuous].
exact: sub_continuous.
Qed.

HB.instance Definition _ :=
  PreTopologicalNmodule_isTopologicalNmodule.Build M add_continuous.

HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalZmodule.Build M opp_continuous.

HB.end.

#[short(type="preTopologicalLmodType")]
HB.structure Definition PreTopologicalLmodule (K : numDomainType) :=
  {M of Topological M & GRing.Lmodule K M}.

HB.mixin Record TopologicalZmodule_isTopologicalLmodule (R : numDomainType) M
    & Topological M & GRing.Lmodule R M := {
  scale_continuous : continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

#[short(type="topologicalLmodType")]
HB.structure Definition TopologicalLmodule (K : numDomainType) :=
  {M of TopologicalZmodule M & GRing.Lmodule K M
        & TopologicalZmodule_isTopologicalLmodule K M}.

Section TopologicalLmodule_theory.
Variables (R : numFieldType) (E : topologicalType) (F : topologicalLmodType R).

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
    & Topological M & GRing.Lmodule R M := {
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

HB.mixin Record PreUniformNmodule_isUniformNmodule M & PreUniformNmodule M := {
  add_unif_continuous : unif_continuous (fun x : M * M => x.1 + x.2)
}.

HB.structure Definition UniformNmodule :=
  {M of PreUniformNmodule M & PreUniformNmodule_isUniformNmodule M}.

HB.mixin Record UniformNmodule_isUniformZmodule M
    & Uniform M & GRing.Zmodule M := {
  opp_unif_continuous : unif_continuous (-%R : M -> M)
}.

HB.structure Definition UniformZmodule :=
  {M of UniformNmodule M & GRing.Zmodule M & UniformNmodule_isUniformZmodule M}.

HB.factory Record PreUniformNmodule_isUniformZmodule M
    & Uniform M & GRing.Zmodule M := {
  sub_unif_continuous : unif_continuous (fun x : M * M => x.1 - x.2)
}.

HB.builders Context M & PreUniformNmodule_isUniformZmodule M.

Lemma opp_unif_continuous : unif_continuous (-%R : M -> M).
Proof.
have unif : unif_continuous (fun x => (0, x) : M * M).
  move=> /= U [[]] /= U1 U2 [] U1e U2e /subsetP U12.
  apply: filterS U2e => x xU2/=.
  have /U12 : ((0, 0), x) \in U1 `*` U2.
    by rewrite in_setX/= (mem_set xU2) andbT inE; exact: entourage_refl.
  by rewrite inE/= => -[[[a1 a2] [b1 b2]]]/= /[swap]-[] -> -> <-.
move=> /= U /sub_unif_continuous /unif /=.
rewrite -comp_preimage/= /comp/= /nbhs/=.
by congr entourage => /=; rewrite eqEsubset; split=> x /=; rewrite !sub0r.
Qed.

Lemma add_unif_continuous : unif_continuous (fun x : M * M => x.1 + x.2).
Proof.
have unif: unif_continuous (fun x => (x.1, -x.2) : M * M).
  move=> /= U [[]]/= U1 U2 [] U1e /opp_unif_continuous.
  rewrite /nbhs/= => U2e /subsetP U12.
  apply: (@filterS _ _ entourage_filter
      ((fun xy => (xy.1.1, xy.2.1, (-xy.1.2, -xy.2.2))) @^-1` (U1 `*` U2))).
    move=> /= [] [] a1 a2 [] b1 b2/= [] ab1 ab2.
    have /U12 : (a1, b1, (-a2, -b2)) \in U1 `*` U2 by rewrite !inE.
    by rewrite inE/= => [] [] [] [] c1 c2 [] d1 d2/= cd [] <- <- <- <-.
  exists (U1, ((fun xy : M * M => (- xy.1, - xy.2)) @^-1` U2)); first by split.
  by move=> /= [] [] a1 a2 [] b1 b2/= [] aU bU; exists (a1, b1, (a2, b2)).
move=> /= U /sub_unif_continuous/unif; rewrite /nbhs/=.
rewrite -comp_preimage/=/comp/=.
by congr entourage; rewrite eqEsubset; split=> x /=; rewrite !opprK.
Qed.

HB.instance Definition _ :=
  PreUniformNmodule_isUniformNmodule.Build M add_unif_continuous.
HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build M opp_unif_continuous.

HB.end.

Section UniformZmoduleTheory.
Variables (M : UniformZmodule.type).

Lemma sub_unif_continuous : unif_continuous (fun x : M * M => x.1 - x.2).
Proof.
suff unif: unif_continuous (fun x => (x.1, - x.2) : M * M).
  by move=> /= U /add_unif_continuous/unif; rewrite /nbhs/= -comp_preimage.
move=> /= U [[]]/= U1 U2 [] U1e /opp_unif_continuous.
rewrite /nbhs/= => U2e /subsetP U12.
apply: (@filterS _ _ entourage_filter
    ((fun xy => (xy.1.1, xy.2.1, (- xy.1.2, - xy.2.2))) @^-1` (U1 `*` U2))).
  move=> /= [] [] a1 a2 [] b1 b2/= [] ab1 ab2.
  have /U12 : (a1, b1, (-a2, -b2)) \in U1 `*` U2 by rewrite !inE.
  by rewrite inE/= => [] [] [] [] c1 c2 [] d1 d2/= cd [] <- <- <- <-.
exists (U1, ((fun xy : M * M => (- xy.1, - xy.2)) @^-1` U2)); first by split.
by move=> /= [] [] a1 a2 [] b1 b2/= [] aU bU; exists (a1, b1, (a2, b2)).
Qed.

End UniformZmoduleTheory.

HB.structure Definition PreUniformLmodule (K : numDomainType) :=
  {M of Uniform M & GRing.Lmodule K M}.

HB.mixin Record PreUniformLmodule_isUniformLmodule (R : numFieldType) M
    & PreUniformLmodule R M := {
  scale_unif_continuous : unif_continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.structure Definition UniformLmodule (R : numFieldType) :=
  {M of UniformZmodule M & GRing.Lmodule R M
        & PreUniformLmodule_isUniformLmodule R M}.

HB.factory Record UniformNmodule_isUniformLmodule (R : numFieldType) M
    & PreUniformLmodule R M := {
  scale_unif_continuous : unif_continuous (fun z : R^o * M => z.1 *: z.2) ;
}.

HB.builders Context R M & UniformNmodule_isUniformLmodule R M.

Lemma opp_unif_continuous : unif_continuous (-%R : M -> M).
Proof.
have unif: unif_continuous (fun x => (-1, x) : R^o * M).
  move=> /= U [[]] /= U1 U2 [] U1e U2e /subsetP U12.
  rewrite /nbhs/=.
  apply: filterS U2e => x xU2/=.
  have /U12 : ((-1, -1), x) \in U1 `*` U2.
    rewrite in_setX/= (mem_set xU2) andbT.
    by apply/mem_set; exact: entourage_refl.
  by rewrite inE/= => [[[]]] [] a1 a2 [] b1 b2/= abU [] {2}<- <- <-/=.
move=> /= U /scale_unif_continuous/unif/=.
rewrite /nbhs/=.
rewrite -comp_preimage/=/comp/=.
by congr entourage; rewrite eqEsubset; split=> x /=; rewrite !scaleN1r.
Qed.

#[warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  UniformNmodule_isUniformZmodule.Build M opp_unif_continuous.
HB.instance Definition _ :=
  PreUniformLmodule_isUniformLmodule.Build R M scale_unif_continuous.

HB.end.

HB.mixin Record Uniform_isConvexTvs (R : numDomainType) E
    & Uniform E & GRing.Lmodule R E := {
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> convex_set b) & basis B
}.

#[short(type="convexTvsType")]
HB.structure Definition ConvexTvs (R : numDomainType) :=
  {E of Uniform_isConvexTvs R E & Uniform E & TopologicalLmodule R E}.

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
    & Topological E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set_system E,
    (forall b, b \in B -> convex_set b) & basis B
  }.

HB.builders Context R E & PreTopologicalLmod_isConvexTvs R E.

Definition entourage : set_system (E * E) :=
  fun P => exists (U : set E), nbhs (0 : E) U  /\
                     (forall xy : E * E,  (xy.1 - xy.2) \in U -> xy \in P).

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

Local Lemma entourage_refl (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
move=> [U [U0 Uxy]] xy eq_xy; apply/set_mem/Uxy; rewrite eq_xy subrr.
apply/mem_set; exact: nbhs_singleton.
Qed.

Local Lemma entourage_inv (A : set (E * E)) :
  entourage A -> entourage A^-1%relation.
Proof.
move=> [/= U [U0 Uxy]]; exists (-%R @` U); split; first exact: nbhs0N.
move=> xy /set_mem /=; rewrite -opprB => [[yx] Uyx] /oppr_inj yxE.
by apply/Uxy/mem_set; rewrite /= -yxE.
Qed.

Local Lemma entourage_split_ex (A : set (E * E)) : entourage A ->
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

Local Lemma nbhsE : nbhs = nbhs_ entourage.
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

HB.instance Definition _ := Uniform_isConvexTvs.Build R E locally_convex.

HB.end.

Section ConvexTvs_numDomain.
Context (R : numDomainType) (E : convexTvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @` U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Lemma nbhsB (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

End ConvexTvs_numDomain.

Section ConvexTvs_numField.

Lemma nbhs0Z (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous (r^-1, 0) U.
rewrite scaler0 => /(_ U0)[]/= B [B1 B2] BU.
near=> x => //=; exists (r^-1 *: x); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1, x)); split => //=;[exact: nbhs_singleton|near: x].
Unshelve. all: by end_near. Qed.

Lemma nbhsZ  (R : numFieldType) (E : convexTvsType R) (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous ((r^-1, r *: x)) U.
rewrite scalerA mulVf// scale1r =>/(_ U0)[] /= B [B1 B2] BU.
near=> z; exists (r^-1 *: z); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1,z)); split; [exact: nbhs_singleton|near: z].
Unshelve. all: by end_near. Qed.

End ConvexTvs_numField.

Section standard_topology.
Variable R : numFieldType.

(** NB: we have almost the same proof in `pseudometric_normed_Zmodule.v` *)
Let standard_add_continuous : continuous (fun x : R^o * R^o => x.1 + x.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.

Let standard_scale_continuous : continuous (fun z : R^o * R^o => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_R => M.
near=> l z => /=; have M0 : 0 < M by [].
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normrM.
  rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpM2r -?ltr_pdivlMl//.
  by near: z; apply: cvgr_dist_lt; rewrite // mulr_gt0 ?invr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
  by near: z; near: M; exact: (@cvg_bounded _ R^o _ _ _ _ _ (@cvg_refl _ _)).
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: by end_near. Qed.

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
  PreTopologicalNmodule_isTopologicalNmodule.Build R^o standard_add_continuous.
HB.instance Definition _ :=
  TopologicalNmodule_isTopologicalLmodule.Build R R^o standard_scale_continuous.
HB.instance Definition _ :=
  Uniform_isConvexTvs.Build R R^o standard_locally_convex_set.

End standard_topology.

Section prod_ConvexTvs.
Context (K : numFieldType) (E F : convexTvsType K).

Local Lemma prod_add_continuous :
  continuous (fun x : (E * F) * (E * F) => x.1 + x.2).
Proof.
move => [/= xy1 xy2] /= U /= [] [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @add_continuous E (xy1.1, xy2.1) _ nA.
have [/= B0 [B01 B02] nB1] := @add_continuous F (xy1.2, xy2.2) _ nB.
exists ([set xy | A0.1 xy.1 /\ B0.1 xy.2], [set xy | A0.2 xy.1 /\ B0.2 xy.2]).
  by split; [exists (A0.1, B0.1)|exists (A0.2, B0.2)].
move => [[x1 y1][x2 y2]] /= [] [] a1 b1 [] a2 b2.
by apply: nU; split; [exact: (nA1 (x1, x2))|exact: (nB1 (y1, y2))].
Qed.

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

HB.instance Definition _ := PreTopologicalNmodule_isTopologicalNmodule.Build
  (E * F)%type prod_add_continuous.
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
  mem [set f | linear_for s f /\ continuous f ].

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
Proof. by move=> /= x; apply: fun_cvgD; exact: continuous_fun. Qed.

HB.instance Definition _ f g :=
  isContinuous.Build E F (f \+ g) (@lcfun_continuousD f g).

#[local] Lemma lcfun_continuousN f : continuous (\- f).
Proof. by move=> /= x; apply: fun_cvgN; exact: continuous_fun. Qed.

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
