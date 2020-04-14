(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp ereal reals Rstruct.
Require Import classical_sets posnum topology prodnormedzmodule.

(******************************************************************************)
(* This file extends the topological hierarchy with norm-related notions.     *)
(*                                                                            *)
(* ball_ N == balls defined by the norm/absolute value N                      *)
(*                                                                            *)
(* * Normed Topological Abelian groups:                                       *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   Abelian group equipped with a norm       *)
(*  PseudoMetricNormedZmodule.Mixin nb == builds the mixin for a normed       *)
(*                                   topological Abelian group from the       *)
(*                                   compatibility between the norm and       *)
(*                                   balls; the carrier type must have a      *)
(*                                   normed Zmodule over a numDomainType.     *)
(*                                                                            *)
(* * Normed modules :                                                         *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K.      *)
(*           NormedModMixin normZ == builds the mixin for a normed module     *)
(*                                   from the property of the linearity of    *)
(*                                   the norm; the carrier type must have a   *)
(*                                   pseudoMetricNormedZmodType structure     *)
(*            NormedModType K T m == packs the mixin m to build a             *)
(*                                   normedModType K; T must have canonical   *)
(*                                   pseudoMetricNormedZmodType K and         *)
(*                                   pseudoMetricType structures.             *)
(*  [normedModType K of T for cT] == T-clone of the normedModType K structure *)
(*                                   cT.                                      *)
(*         [normedModType K of T] == clone of a canonical normedModType K     *)
(*                                   structure on T.                          *)
(*                           `|x| == the norm of x (notation from ssrnum).    *)
(*                      ball_norm == balls defined by the norm.               *)
(*                   locally_norm == neighborhoods defined by the norm.       *)
(*                        bounded == set of bounded sets.                     *)
(*                                                                            *)
(* * Complete normed modules :                                                *)
(*        completeNormedModType K == interface type for a complete normed     *)
(*                                   module structure over a realFieldType    *)
(*                                   K.                                       *)
(* [completeNormedModType K of T] == clone of a canonical complete normed     *)
(*                                   module structure over K on T.            *)
(*                                                                            *)
(* * Filters :                                                                *)
(*          at_left x, at_right x == filters on real numbers for predicates   *)
(*                                   that locally hold on the left/right of   *)
(*                                   x.                                       *)
(*               ereal_locally' x == filter on extended real numbers that     *)
(*                                   corresponds to locally' x if x is a real *)
(*                                   number and to predicates that are        *)
(*                                   eventually true if x is +oo/-oo.         *)
(*                ereal_locally x == same as ereal_locally' where locally' is *)
(*                                   replaced with locally.                   *)
(*                ereal_loc_seq x == sequence that converges to x in the set  *)
(*                                   of extended real numbers.                *)
(*                                                                            *)
(* --> We used these definitions to prove the intermediate value theorem and  *)
(*     the Heine-Borel theorem, which states that the compact sets of R^n are *)
(*     the closed and bounded sets.                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section add_to_mathcomp.

Lemma subr_trans (M : zmodType) (z x y : M) : x - y = (x - z) + (z - y).
Proof. by rewrite addrA addrNK. Qed.

Lemma ltr_distW (R : realDomainType) (x y e : R) :
  `|x - y| < e -> y - e < x.
Proof. by rewrite ltr_distl => /andP[]. Qed.

Lemma ler_distW (R : realDomainType) (x y e : R):
  `|x - y| <= e -> y - e <= x.
Proof. by rewrite ler_distl => /andP[]. Qed.

End add_to_mathcomp.

Local Open Scope classical_set_scope.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%R y /.

Definition pointed_of_zmodule (R : zmodType) : pointedType := PointedType R 0.

Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R := Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R)) (locally_ (ball_ (fun x => `|x|)))).

Section pseudoMetric_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ normr x e x.
Proof. by move=> ? /=; rewrite subrr normr0. Qed.
Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ normr x e y -> ball_ normr y e x.
Proof. by rewrite /= distrC. Qed.
Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ normr x e1 y -> ball_ normr y e2 z -> ball_ normr x (e1 + e2) z.
Proof.
move=> /= ? ?; rewrite -(subr0 x) -(subrr y) opprD opprK (addrA x _ y) -addrA.
by rewrite (le_lt_trans (ler_norm_add _ _)) // ltr_add.
Qed.
Definition pseudoMetric_of_normedDomain
  : PseudoMetric.mixin_of K (@locally_ K R R (ball_ (fun x => `|x|)))
  := PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
End pseudoMetric_of_normedDomain.

Canonical R_pointedType := [pointedType of
  Rdefinitions.R for pointed_of_zmodule R_ringType].
(* NB: similar definition in topology.v *)
Canonical R_filteredType := [filteredType Rdefinitions.R of
  Rdefinitions.R for filtered_of_normedZmod R_normedZmodType].
Canonical R_topologicalType : topologicalType := TopologicalType Rdefinitions.R
  (topologyOfBallMixin (pseudoMetric_of_normedDomain R_normedZmodType)).
Canonical R_pseudoMetricType : pseudoMetricType R_numDomainType :=
  PseudoMetricType Rdefinitions.R (pseudoMetric_of_normedDomain R_normedZmodType).

Section numFieldType_canonical.
Variable R : numFieldType.
(*Canonical topological_of_numFieldType := [numFieldType of R^o].*)
Canonical numFieldType_pointedType :=
  [pointedType of R^o for pointed_of_zmodule R].
Canonical numFieldType_filteredType :=
  [filteredType R of R^o for filtered_of_normedZmod R].
Canonical numFieldType_topologicalType : topologicalType := TopologicalType R^o
  (topologyOfBallMixin (pseudoMetric_of_normedDomain [normedZmodType R of R])).
Canonical numFieldType_pseudoMetricType := @PseudoMetric.Pack R R^o (@PseudoMetric.Class R R
  (Topological.class numFieldType_topologicalType) (@pseudoMetric_of_normedDomain R R)).
Definition numdFieldType_lalgType : lalgType R := @GRing.regular_lalgType R.
End numFieldType_canonical.

Lemma locallyN (R : numFieldType) (x : R^o) :
  locally (- x) = [set [set - y | y in A] | A in locally x].
Proof.
rewrite predeqE => A; split=> [[e egt0 oppxe_A]|[B [e egt0 xe_B] <-]];
  last first.
  exists e => // y xe_y; exists (- y); last by rewrite opprK.
  apply/xe_B.
  by rewrite /ball_ opprK -normrN -mulN1r mulrDr !mulN1r.
exists [set - y | y in A]; last first.
  rewrite predeqE => y; split=> [[z [t At <- <-]]|Ay]; first by rewrite opprK.
  by exists (- y); [exists y|rewrite opprK].
exists e => // y xe_y; exists (- y); last by rewrite opprK.
by apply/oppxe_A; rewrite /ball_ distrC opprK addrC.
Qed.

Lemma openN (R : numFieldType) (A : set R^o) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior locallyN; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R^o) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK locallyN; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

Module PseudoMetricNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (loc : T -> set (set T))
    (m : PseudoMetric.mixin_of R loc) := Mixin {
  _ : PseudoMetric.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  locally_mixin : Filtered.locally_of T T ;
  topological_mixin : @Topological.mixin_of T locally_mixin ;
  pseudoMetric_mixin : @PseudoMetric.mixin_of R T locally_mixin ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ pseudoMetric_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.
Definition base2 T c := @PseudoMetric.Class _ _
    (@Topological.Class _
      (Filtered.Class
       (Pointed.Class (@base T c) (pointed_mixin c))
       (locally_mixin c))
      (topological_mixin c))
    (pseudoMetric_mixin c).
Local Coercion base2 : class_of >-> PseudoMetric.class_of.
(* TODO: base3? *)

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0
  (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : PseudoMetric.class_of R T) & phant_id (@PseudoMetric.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack xT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition pseudoMetric_zmodType := @GRing.Zmodule.Pack pseudoMetricType xclass.
Definition pointed_normedZmodType := @Num.NormedZmodule.Pack R phR pointedType xclass.
Definition filtered_normedZmodType := @Num.NormedZmodule.Pack R phR filteredType xclass.
Definition topological_normedZmodType := @Num.NormedZmodule.Pack R phR topologicalType xclass.
Definition pseudoMetric_normedZmodType := @Num.NormedZmodule.Pack R phR pseudoMetricType xclass.

End ClassDef.

(*Definition numDomain_normedDomainType (R : numDomainType) : type (Phant R) :=
  Pack (Phant R) (@Class R _ _ (NumDomain.normed_mixin (NumDomain.class R))).*)

Module Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion base2 : class_of >-> PseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical pseudoMetric_zmodType.
Canonical pointed_normedZmodType.
Canonical filtered_normedZmodType.
Canonical topological_normedZmodType.
Canonical pseudoMetric_normedZmodType.
Notation pseudoMetricNormedZmodType R := (type (Phant R)).
Notation PseudoMetricNormedZmodType R T m :=
  (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T ]" :=
  (@clone _ (Phant R) T _ _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T ]") : form_scope.
End Exports.

End PseudoMetricNormedZmodule.
Export PseudoMetricNormedZmodule.Exports.

Section pseudoMetricnormedzmodule_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by case: V => ? [? ? ? ? ? []]. Qed.

End pseudoMetricnormedzmodule_lemmas.

Section numFieldType_canonical_contd.
Variable R : numFieldType.
Lemma R_ball : @ball _ [pseudoMetricType R of R^o] = ball_ (fun x => `| x |).
Proof. by []. Qed.
Definition numFieldType_pseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin R_ball.
Canonical numFieldType_pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodType R R^o numFieldType_pseudoMetricNormedZmodMixin.
End numFieldType_canonical_contd.

(** locally *)

Section Locally.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma forallN {U} (P : set U) : (forall x, ~ P x) = ~ exists x, P x.
Proof. (*boolP*)
rewrite propeqE; split; first by move=> fP [x /fP].
by move=> nexP x Px; apply: nexP; exists x.
Qed.

Lemma eqNNP (P : Prop) : (~ ~ P) = P. (*boolP*)
Proof. by rewrite propeqE; split=> [/contrapT|?]. Qed.

Lemma existsN {U} (P : set U) : (exists x, ~ P x) = ~ forall x, P x. (*boolP*)
Proof.
rewrite propeqE; split=> [[x Px] Nall|Nall]; first exact: Px.
by apply: contrapT; rewrite -forallN => allP; apply: Nall => x; apply: contrapT.
Qed.
End Locally.

Section Locally'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallN eqNNP => exNP.
pose D := [set d : R | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma locallyC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  locally x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/locallyP; exists e%:num. Qed.

Lemma locallyC_ball (x : T) (P : set T) :
  locally x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /locallyP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma locally_ex (x : T) (P : T -> Prop) : locally x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /locallyP xP.
pose D := [set d : R | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End Locally'.

Lemma ler_addgt0Pr (R : numFieldType) (x y : R) :
   reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy _/posnumP[e] | lexye]; first by rewrite ler_paddr.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye//.
  by rewrite ler_addl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
by rewrite -(@addrK _ y y) addrAC -addrA 2!mulrDl -splitr lexye// divr_gt0//
  subr_gt0.
Qed.

Lemma ler_addgt0Pl (R : numFieldType) (x y : R) :
  reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma in_segment_addgt0Pr (R : numFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(x - e), (z + e)]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz _/posnumP[e] | xyz_e].
  rewrite inE/=; apply/andP; split; last by rewrite ler_paddr // (itvP xyz).
  by rewrite ler_subl_addr ler_paddr // (itvP xyz).
rewrite inE/=; apply/andP.
by split; apply/ler_addgt0Pr => ? /xyz_e /andP /= []; rewrite ler_subl_addr.
Qed.

Lemma in_segment_addgt0Pl (R : numFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K^o]_(m.+1, n.+1) => M i j).
Proof.
move=> /= M s /= /(locallyP (M i j)); rewrite locally_E => -[e e0 es].
apply/locallyP; rewrite locally_E; exists e => //= N MN; exact/es/MN.
Qed.

Global Instance Proper_locally'_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter (locally' x).
Proof.
apply: Build_ProperFilter => A [_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
Qed.

Global Instance Proper_locally'_realType (R : realType) (x : R^o) :
  ProperFilter (locally' x).
Proof. exact: Proper_locally'_numFieldType. Qed.

(** * Some Topology on [Rbar] *)

Canonical ereal_pointed (R : numDomainType) := PointedType {ereal R} (+oo%E).

Section ereal_locally.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R^o].
Local Open Scope ereal_scope.
Definition ereal_locally' (a : {ereal R}) (P : {ereal R} -> Prop) : Prop :=
  match a with
    | a%:E => @locally' R_topologicalType a (fun x => P x%:E)
    | +oo => exists M, M \is Num.real /\ forall x, (M%:E < x)%E -> P x
    | -oo => exists M, M \is Num.real /\ forall x, (x < M%:E)%E -> P x
  end.
Definition ereal_locally (a : {ereal R}) (P : {ereal R} -> Prop) : Prop :=
  match a with
    | a%:E => @locally _ R_topologicalType a (fun x => P x%:E)
    | +oo => exists M, M \is Num.real /\ forall x, (M%:E < x)%E -> P x
    | -oo => exists M, M \is Num.real /\ forall x, (x < M%:E)%E -> P x
  end.
Canonical ereal_ereal_filter := FilteredType {ereal R} {ereal R} (ereal_locally).
End ereal_locally.

Section ereal_locally_instances.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R^o].

Global Instance ereal_locally'_filter :
  forall x : {ereal R}, ProperFilter (ereal_locally' x).
Proof.
case=> [x||].
- case: (Proper_locally'_numFieldType x) => x0 [//= xT xI xS].
  apply Build_ProperFilter' => //=; apply Build_Filter => //=.
  move=> P Q lP lQ; exact: xI.
  by move=> P Q PQ /xS; apply => y /PQ.
- apply Build_ProperFilter.
    move=> P [x [xr xP]]; exists (x + 1)%:E; apply xP => /=.
    by rewrite lte_fin ltr_addl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|; rewrite realE normr_ge0; split => // x Hx; split.
        by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0 lee_fin.
      by apply gtMQ; rewrite (le_lt_trans _ Hx) // lee_fin real_ler_normr // lexx.
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists `|MP|; rewrite realE normr_ge0; split => // x MPx; split.
      by apply gtMP; rewrite (le_lt_trans _ MPx) // lee_fin real_ler_normr // lexx.
      by apply gtMQ; rewrite (le_lt_trans _ MPx) // lee_fin MQ0.
    have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
    have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= posnum_ge0 /=; split => //.
    case=> [r| |//].
    * rewrite lte_fin pos_ltUx /= => /andP[MPx MQx]; split.
      by apply/gtMP; rewrite lte_fin (le_lt_trans _ MPx) // real_ler_normr // lexx.
      by apply/gtMQ; rewrite lte_fin (le_lt_trans _ MQx) // real_ler_normr // lexx.
    * by move=> _; split; [apply/gtMP | apply/gtMQ].
  + by exists M; split => // ? /gtM /sPQ.
- apply Build_ProperFilter.
  + move=> P [M [Mr ltMP]]; exists (M - 1)%:E.
    by apply: ltMP; rewrite lte_fin gtr_addl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0; rewrite real0.
    * have [/eqP MP0|MP0] := boolP (MP == 0).
        have [/eqP MQ0|MQ0] := boolP (MQ == 0).
          by exists 0; rewrite real0; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|); rewrite realN realE normr_ge0; split => // x xMQ; split.
          by apply ltMP; rewrite (lt_le_trans xMQ) // lee_fin MP0 ler_oppl oppr0.
       apply ltMQ; rewrite (lt_le_trans xMQ) // lee_fin ler_oppl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        exists (- `|MP|); rewrite realN realE normr_ge0; split => // x MPx; split.
          apply ltMP; rewrite (lt_le_trans MPx) // lee_fin ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        by apply ltMQ; rewrite (lt_le_trans MPx) // lee_fin MQ0 ler_oppl oppr0.
      have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
      have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
      exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num).
      rewrite realN realE /= posnum_ge0 /=; split => //.
      case=> [r|//|].
      - rewrite lte_fin ltr_oppr pos_ltUx => /andP[].
        rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
          apply/ltMP; rewrite lte_fin (lt_le_trans MPx) //= ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        apply/ltMQ; rewrite lte_fin (lt_le_trans MQx) //= ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      - by move=> _; split; [apply/ltMP | apply/ltMQ].
    * by exists M; split => // x /ltM /sPQ.
Qed.
Typeclasses Opaque ereal_locally'.

Global Instance ereal_locally_filter :
  forall x, ProperFilter (@ereal_locally R x).
Proof.
case=> [x| |].
- case: (ereal_locally'_filter x%:E) => x0 [//=nxT xI xS].
  apply Build_ProperFilter => //=.
  by move=> P [r r0 xr]; exists x%:E; apply xr => //=; rewrite subrr normr0.
  apply Build_Filter => //=.
  by rewrite locallyE'.
  move=> P Q.
  rewrite !locallyE' => -[xP axP] [xQ axQ]; split => //=.
  exact: xI.
  move=> P Q PQ; rewrite !locallyE' => -[xP axP]; split => //=.
  apply (xS P) => //=.
  exact: PQ.
exact: (ereal_locally'_filter +oo).
exact: (ereal_locally'_filter -oo).
Qed.
Typeclasses Opaque ereal_locally.

End ereal_locally_instances.

Definition pinfty_locally (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_locally R : clear implicits.
Definition ninfty_locally (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_locally R : clear implicits.

Notation "+oo" := (pinfty_locally _) : ring_scope.
Notation "-oo" := (ninfty_locally _) : ring_scope.

Section infty_locally_instances.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R^o].

Global Instance proper_pinfty_locally : ProperFilter (pinfty_locally R).
Proof.
apply Build_ProperFilter.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0; rewrite real0.
- have [/eqP MP0|MP0] := boolP (MP == 0).
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      by exists 0; rewrite real0; split => // x x0; split;
      [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
    exists `|MQ|; rewrite realE normr_ge0; split => // x Hx; split.
      by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0.
    by apply gtMQ; rewrite (le_lt_trans _ Hx) // real_ler_normr // lexx.
  have [/eqP MQ0|MQ0] := boolP (MQ == 0).
    exists `|MP|; rewrite realE normr_ge0; split => // x MPx; split.
    by apply gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
    by apply gtMQ; rewrite (le_lt_trans _ MPx) // MQ0.
  have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
  have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
  exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
  rewrite realE /= posnum_ge0 /=; split => // x.
  rewrite pos_ltUx /= => /andP[MPx MQx]; split.
  by apply/gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
  by apply/gtMQ; rewrite (le_lt_trans _ MQx) // real_ler_normr // lexx.
- by exists M; split => // ? /gtM /sPQ.
Defined.
Typeclasses Opaque proper_pinfty_locally.

Global Instance proper_ninfty_locally : ProperFilter (ninfty_locally R).
Proof.
apply Build_ProperFilter.
- move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtr_addl oppr_lt0.
- split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
      exists (- `|MQ|); rewrite realN realE normr_ge0; split => // x xMQ; split.
        by apply ltMP; rewrite (lt_le_trans xMQ) // MP0 ler_oppl oppr0.
      apply ltMQ; rewrite (lt_le_trans xMQ) // ler_oppl -normrN.
     by rewrite real_ler_normr ?realN // lexx.
  + have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists (- `|MP|); rewrite realN realE normr_ge0; split => // x MPx; split.
        apply ltMP; rewrite (lt_le_trans MPx) // ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      by apply ltMQ; rewrite (lt_le_trans MPx) // MQ0 ler_oppl oppr0.
    have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
    have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
    exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num).
    rewrite realN realE /= posnum_ge0 /=; split => // x.
    rewrite ltr_oppr pos_ltUx => /andP[].
    rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
      apply/ltMP; rewrite (lt_le_trans MPx) //= ler_oppl -normrN.
      by rewrite real_ler_normr ?realN // lexx.
    apply/ltMQ; rewrite (lt_le_trans MQx) //= ler_oppl -normrN.
    by rewrite real_ler_normr ?realN // lexx.
  + by exists M; split => // x /ltM /sPQ.
Defined.
Typeclasses Opaque proper_ninfty_locally.

(*Global Instance ereal_locally'_filter :
  forall x : {ereal R}, ProperFilter (ereal_locally' x).
Proof.
case=> [x||]; first exact: Proper_locally'_numFieldType.
- apply Build_ProperFilter.
    by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|; rewrite realE normr_ge0; split => // x Hx; split.
        by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0.
      by apply gtMQ; rewrite (le_lt_trans _ Hx) // real_ler_normr // lexx.
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists `|MP|; rewrite realE normr_ge0; split => // x MPx; split.
      by apply gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
      by apply gtMQ; rewrite (le_lt_trans _ MPx) // MQ0.
    have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
    have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= posnum_ge0 /=; split => // x.
    rewrite pos_ltUx /= => /andP[MPx MQx]; split.
    by apply/gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
    by apply/gtMQ; rewrite (le_lt_trans _ MQx) // real_ler_normr // lexx.
  + by exists M; split => // ? /gtM /sPQ.
- apply Build_ProperFilter.
  + move=> P [M [Mr ltMP]]; exists (M - 1).
    by apply: ltMP; rewrite gtr_addl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0; rewrite real0.
    * have [/eqP MP0|MP0] := boolP (MP == 0).
        have [/eqP MQ0|MQ0] := boolP (MQ == 0).
          by exists 0; rewrite real0; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|); rewrite realN realE normr_ge0; split => // x xMQ; split.
          by apply ltMP; rewrite (lt_le_trans xMQ) // MP0 ler_oppl oppr0.
        apply ltMQ; rewrite (lt_le_trans xMQ) // ler_oppl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        exists (- `|MP|); rewrite realN realE normr_ge0; split => // x MPx; split.
          apply ltMP; rewrite (lt_le_trans MPx) // ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        by apply ltMQ; rewrite (lt_le_trans MPx) // MQ0 ler_oppl oppr0.
      have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
      have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
      exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num).
      rewrite realN realE /= posnum_ge0 /=; split => // x.
      rewrite ltr_oppr pos_ltUx => /andP[].
      rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
        apply/ltMP; rewrite (lt_le_trans MPx) //= ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      apply/ltMQ; rewrite (lt_le_trans MQx) //= ler_oppl -normrN.
      by rewrite real_ler_normr ?realN // lexx.
    * by exists M; split => // x /ltM /sPQ.
Qed.
Typeclasses Opaque ereal_locally'.*)

(*Global Instance ereal_locally_filter :
  forall x, ProperFilter (@ereal_locally R x).
Proof.
case=> [x||].
exact: ereal_locally_filter.
exact: (ereal_locally'_filter +oo).
exact: (ereal_locally'_filter -oo).
Qed.
Typeclasses Opaque ereal_locally.*)

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
move=> [M [Mreal AM]]; exists (M * 2); split.
  by rewrite realM // realE; apply/orP; left.
by move=> x; rewrite -ltr_pdivl_mulr //; apply: AM.
Qed.

Lemma locally_pinfty_gt (c : {posnum R}) : \forall x \near +oo, c%:num < x.
Proof. by  exists c%:num; split => // ; rewrite realE posnum_ge0. Qed.

Lemma locally_pinfty_ge (c : {posnum R}) : \forall x \near +oo, c%:num <= x.
Proof. by exists c%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

End infty_locally_instances.

Hint Extern 0 (is_true (0 < _)) => match goal with
  H : ?x \is_near (locally +oo) |- _ =>
    solve[near: x; exists 0 => _/posnumP[x] //] end : core.

(** ** Modules with a norm *)

Module NormedModule.

Record mixin_of (K : numDomainType)
  (V : pseudoMetricNormedZmodType K) (scale : K -> V -> V) := Mixin {
  _ : forall (l : K) (x : V), `| scale l x | = `| l | * `| x |;
}.

Section ClassDef.

Variable K : numDomainType.

Record class_of (T : Type) := Class {
  base : PseudoMetricNormedZmodule.class_of K T ;
  lmodmixin : GRing.Lmodule.mixin_of K (GRing.Zmodule.Pack base) ;
  mixin : @mixin_of K (PseudoMetricNormedZmodule.Pack (Phant K) base)
                      (GRing.Lmodule.scale lmodmixin)
}.
Local Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.
Local Coercion base2 T (c : class_of T) : GRing.Lmodule.class_of K T :=
  @GRing.Lmodule.Class K T (base c) (lmodmixin c).
Local Coercion mixin : class_of >-> mixin_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phK T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0
                (m0 : @mixin_of K (@PseudoMetricNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@PseudoMetricNormedZmodule.class K (Phant K) bT) b =>
  fun l & phant_id l0 l =>
  fun m & phant_id m0 m => Pack phK (@Class T b l m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType := @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition pseudoMetric_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricType xclass.
Definition normedZmod_lmodType := @GRing.Lmodule.Pack K phK normedZmodType xclass.
Definition pseudoMetricNormedZmod_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricNormedZmodType xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.
Coercion base2 : class_of >-> GRing.Lmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Canonical pointed_lmodType.
Canonical filtered_lmodType.
Canonical topological_lmodType.
Canonical pseudoMetric_lmodType.
Canonical normedZmod_lmodType.
Canonical pseudoMetricNormedZmod_lmodType.
Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ idfun _ idfun _ idfun).
Notation NormedModMixin := Mixin.
Notation "[ 'normedModType' K 'of' T 'for' cT ]" := (@clone _ (Phant K) T cT _ idfun)
  (at level 0, format "[ 'normedModType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'normedModType' K 'of' T ]" := (@clone _ (Phant K) T _ _ id)
  (at level 0, format "[ 'normedModType'  K  'of'  T ]") : form_scope.
End Exports.

End NormedModule.

Export NormedModule.Exports.

Fail Canonical R_NormedModule := [normedModType Rdefinitions.R of Rdefinitions.R^o].

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normmZ l (x : V) : `| l *: x | = `| l | * `| x |.
Proof. by case: V x => V0 [a b [c]] //= v; rewrite c. Qed.

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation locally_norm := (locally_ ball_norm).

Lemma locally_le_locally_norm (x : V) : locally x `=>` locally_norm x.
Proof.
move=> P [_ /posnumP[e] subP]; apply/locallyP.
by eexists; last (move=> y Py; apply/subP; rewrite ball_normE; apply/Py).
Qed.

Lemma locally_norm_le_locally x : locally_norm x `=>` locally x.
Proof.
move=> P /locallyP [_ /posnumP[e] Pxe].
by exists e%:num => // y; rewrite ball_normE; apply/Pxe.
Qed.

Lemma locally_locally_norm : locally_norm = locally.
Proof.
by rewrite funeqE => x; rewrite /locally_norm ball_normE filter_from_ballE.
Qed.

Lemma locally_normP x P : locally x P <-> locally_norm x P.
Proof. by rewrite locally_locally_norm. Qed.

Lemma filter_from_norm_locally x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = locally x.
Proof. by rewrite -locally_locally_norm. Qed.

Lemma locally_normE (x : V) (P : set V) :
  locally_norm x P = \near x, P x.
Proof. by rewrite locally_locally_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : set V) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_locally. Qed.

Lemma near_locally_norm (x : V) (P : set V) :
  (\forall x \near locally_norm x, P x) = \near x, P x.
Proof. exact: locally_normE. Qed.

Lemma locally_norm_ball_norm x (e : {posnum R}) :
  locally_norm x (ball_norm x e%:num).
Proof. by exists e%:num. Qed.

Lemma locally_ball_norm (x : V) (eps : {posnum R}) : locally x (ball_norm x eps%:num).
Proof. rewrite -locally_locally_norm; apply: locally_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let locally_simpl :=
  (locally_simpl,@locally_locally_norm,@filter_from_norm_locally).

Lemma cvg_normP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !locally_simpl. Qed.

Lemma cvg_norm {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Proof. by move=> /cvg_normP. Qed.

Lemma locally_norm_ball x (eps : {posnum R}) : locally_norm x (ball x eps%:num).
Proof. rewrite locally_locally_norm; by apply: locally_ball. Qed.

(* TODO: commented out on 2020-03-10, prove me *)
(*
Lemma closeE (x y : V) : close x y = (x = y).
Proof.
rewrite propeqE; split => [cl_xy|->//]; have [//|neq_xy] := eqVneq x y.
have dxy_gt0 : `|x - y| > 0.
  by rewrite normr_gt0 subr_eq0.
have dxy_ge0 := ltW dxy_gt0.
have := cl_xy (PosNum dxy_gt0).
by rewrite -ball_normE /= ltxx.
Qed.

Lemma eq_close (x y : V) : close x y -> x = y. by rewrite closeE. Qed.

Lemma norm_close x y : close x y = (forall eps : {posnum R}, ball_norm x eps%:num y).
Proof. by rewrite propeqE ball_normE. Qed.
*)

End NormedModule_numDomainType.
Hint Resolve normr_ge0 : core.
Arguments cvg_norm {_ _ F FF}.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation locally_norm := (locally_ ball_norm).

Lemma normedModType_hausdorff : hausdorff V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltr_add acr bcr); rewrite -r22 (distrC b c).
move/(le_lt_trans (ler_dist_add c a b)).
by rewrite -mulrA mulVr ?mulr1 ?ltxx // unitfE.
Qed.
Hint Extern 0 (hausdorff _) => exact: normedModType_hausdorff.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_split _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitr _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitl _ _ z x y e; rewrite -ball_normE. Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
move=> /posnumP[{e}e] /le_lt_trans ->//.
by rewrite [X in _ < X]splitr ltr_spaddl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

(*Lemma normedModType_separated : separated V.
Proof.
move=> a b anb.
have ab : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
exists (PosNum ab, PosNum ab); apply/eqP; rewrite -(eqNNP (_ = _)) =>/eqP/set0P[v [av bv]].
by move: (ball_splitl av bv); rewrite -ball_normE /ball_ ltxx.
Qed.
Hint Extern 0 (separated _) => exact: normedModType_separated.*)

Lemma cvg_normW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Proof.
move=> cv; apply/cvg_normP => _/posnumP[e]; near=> x.
by apply: normm_leW => //; near: x; apply: cv.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_bounded_real {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y ->
  \forall M \near +oo, M \is Num.real /\ \forall y' \near F, `|y'| < M.
Proof.
move=> /cvg_norm Fy; exists `|y|; rewrite normr_real; split => // M.
rewrite -subr_gt0 => subM_gt0; split.
  rewrite -comparabler0 (@comparabler_trans _ (M - `|y|)) //.
    by rewrite -subr_comparable0 opprD addrA subrr add0r opprK comparabler0
      normr_real.
  by rewrite comparablerE subr0 realE ltW.
have := Fy _ subM_gt0.
apply: filterS => y' yy'; rewrite -(@ltr_add2r _ (- `|y|)).
rewrite (le_lt_trans _ yy') // (le_trans _ (ler_dist_dist _ _)) // distrC.
by rewrite real_ler_norm // realB.
Qed.

Lemma cvg_bounded {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> \forall M \near +oo, \forall y' \near F, `|y'| < M.
Proof. move/cvg_bounded_real; by apply: filterS => x []. Qed.

End NormedModule_numFieldType.
Arguments cvg_bounded {_ _ F FF}.
Hint Extern 0 (hausdorff _) => exact: normedModType_hausdorff : core.

Module Export LocallyNorm.
Definition locally_simpl :=
  (locally_simpl,@locally_locally_norm,@filter_from_norm_locally).
End LocallyNorm.

Section hausdorff.

Lemma Rhausdorff (R : realFieldType) : hausdorff [topologicalType of R^o].
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/(@in_segment_addgt0Pr _ x _ x) => _ /posnumP[e].
rewrite inE -ler_distl; set he := (e%:num / 2)%:pos.
have [z []] := clxy _ _ (locally_ball x he) (locally_ball y he).
move=> zx_he yz_he.
rewrite (subr_trans z) (le_trans (ler_norm_add _ _) _)// ltW //.
by rewrite (splitr e%:num) (distrC z); apply: ltr_add.
Qed.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @locally_normE,
   @filter_from_normE, @near_locally_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Lemma continuous_cvg_norm {R : numFieldType}
  (V W : normedModType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Proof.
move=> cf xl e.
move/cvg_norm: (cf l) => /(_ _ (posnum_gt0 e)).
rewrite nearE /= => /locallyP; rewrite locally_E => -[i i0]; apply.
have /@cvg_norm : Filter [filter of x] by apply: filter_on_Filter.
move/(_ _ xl _ i0).
rewrite nearE /= => /locallyP; rewrite locally_E => -[j j0].
by move/(_ _ (ballxx _ j0)); rewrite -ball_normE.
Qed.

(* TODO: general purpose lemma? *)
Lemma filter_andb I r (a P : pred I) :
  [seq i <- r | P i && a i] = [seq i <- [seq j <- r | P j] | a i].
Proof. by elim: r => //= i r ->; case P. Qed.

Module BigmaxrNonneg.
Section bigmaxr_nonneg.
Variable (R : numDomainType).

Lemma bigmaxr_mkcond I r (P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i =
     \big[maxr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite unlock; elim: r x => //= i r ihr x.
case P; rewrite ihr // join_r //; elim: r {ihr} => //= j r ihr.
by rewrite lexU ihr orbT.
Qed.

Lemma bigmaxr_split I r (P : pred I) (F1 F2 : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) (maxr (F1 i) (F2 i)) =
  maxr (\big[maxr/x]_(i <- r | P i) F1 i) (\big[maxr/x]_(i <- r | P i) F2 i).
Proof.
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?joinxx //.
by rewrite joinCA -!joinA joinCA.
Qed.

Lemma bigmaxr_idl I r (P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i = maxr x (\big[maxr/x]_(i <- r | P i) F i).
Proof.
rewrite -big_filter; elim: [seq i <- r | P i] => [|i l ihl].
  by rewrite big_nil joinxx.
by rewrite big_cons joinCA -ihl.
Qed.

Lemma bigmaxrID I r (a P : pred I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(i <- r | P i) F i =
  maxr (\big[maxr/x]_(i <- r | P i && a i) F i)
    (\big[maxr/x]_(i <- r | P i && ~~ a i) F i).
Proof.
rewrite -!(big_filter _ (fun _ => _ && _)) !filter_andb !big_filter.
rewrite ![in RHS](bigmaxr_mkcond _ _ F) !big_filter -bigmaxr_split.
have eqmax : forall i, P i ->
  maxr (if a i then F i else x) (if ~~ a i then F i else x) = maxr (F i) x.
  by move=> i _; case: (a i) => //=; rewrite joinC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -joinA -bigmaxr_idl ihl.
Qed.

Lemma bigmaxr_seq1 I (i : I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(j <- [:: i]) F j = maxr (F i) x.
Proof. by rewrite unlock /=. Qed.

Lemma bigmaxr_pred1_eq (I : finType) (i : I) (F : I -> {nonneg R}) x :
  \big[maxr/x]_(j | j == i) F j = maxr (F i) x.
Proof. by rewrite -big_filter filter_index_enum enum1 bigmaxr_seq1. Qed.

Lemma bigmaxr_pred1 (I : finType) i (P : pred I) (F : I -> {nonneg R}) x :
  P =1 pred1 i -> \big[maxr/x]_(j | P j) F j = maxr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigmaxr_pred1_eq. Qed.

Lemma bigmaxrD1 (I : finType) j (P : pred I) (F : I -> {nonneg R}) x :
  P j -> \big[maxr/x]_(i | P i) F i
    = maxr (F j) (\big[maxr/x]_(i | P i && (i != j)) F i).
Proof.
move=> Pj; rewrite (bigmaxrID _ (pred1 j)) [in RHS]bigmaxr_idl joinA.
by congr maxr; apply: bigmaxr_pred1 => i; rewrite /= andbC; case: eqP => //->.
Qed.

Lemma ler_bigmaxr_cond (I : finType) (P : pred I) (F : I -> {nonneg R}) x i0 :
  P i0 -> F i0 <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigmaxrD1 _ _ Pi0) lexU lexx. Qed.

Lemma ler_bigmaxr (I : finType) (F : I -> {nonneg R}) (i0 : I) x :
  F i0 <= \big[maxr/x]_i F i.
Proof. exact: ler_bigmaxr_cond. Qed.

Lemma bigmaxr_lerP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (x <= m /\ forall i, P i -> F i <= m)
    (\big[maxr/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[lexm leFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite leUx =>->.
rewrite bigmaxr_idl leUx => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigmaxr_sup (I : finType) i0 (P : pred I) m (F : I -> {nonneg R}) x :
  P i0 -> m <= F i0 -> m <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0 ?; apply: le_trans (ler_bigmaxr_cond _ _ Pi0). Qed.

Lemma bigmaxr_ltrP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (x < m /\ forall i, P i -> F i < m)
    (\big[maxr/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[ltxm ltFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite ltUx =>->.
rewrite bigmaxr_idl ltUx => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigmaxr_gerP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (m <= x \/ exists2 i, P i & m <= F i)
  (m <= \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[lemx|[i Pi lemFi]]]; last 2 first.
- by rewrite bigmaxr_idl lexU lemx.
- by rewrite (bigmaxrD1 _ _ Pi) lexU lemFi.
rewrite leNgt => /bigmaxr_ltrP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -leNgt; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -leNgt; right; exists i.
Qed.

Lemma bigmaxr_gtrP (I : finType) (P : pred I) m (F : I -> {nonneg R}) x :
  reflect (m < x \/ exists2 i, P i & m < F i)
  (m < \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[ltmx|[i Pi ltmFi]]]; last 2 first.
- by rewrite bigmaxr_idl ltxU ltmx.
- by rewrite (bigmaxrD1 _ _ Pi) ltxU ltmFi.
rewrite ltNge => /bigmaxr_lerP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -ltNge; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -ltNge; right; exists i.
Qed.

End bigmaxr_nonneg.
Module Exports.
Arguments bigmaxr_mkcond {R I r}.
Arguments bigmaxrID {R I r}.
Arguments bigmaxr_pred1 {R I} i {P F}.
Arguments bigmaxrD1 {R I} j {P F}.
Arguments ler_bigmaxr_cond {R I P F}.
Arguments ler_bigmaxr {R I F}.
Arguments bigmaxr_sup {R I} i0 {P m F}.
End Exports.
End BigmaxrNonneg.
Export BigmaxrNonneg.Exports.

Module BigmaxBigminr.
Section bigmax_bigmin.
Variable (R : realDomainType).

Lemma bigmaxr_mkcond I r (P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i =
     \big[maxr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite unlock; elim: r x => //= i r ihr x.
case P; rewrite ihr // join_r //; elim: r {ihr} => //= j r ihr.
by rewrite lexU ihr orbT.
Qed.

Lemma bigminr_maxr I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i = - \big[maxr/- x]_(i <- r | P i) - F i.
Proof.
by elim/big_rec2: _ => [|i y _ _ ->]; rewrite ?oppr_max opprK.
Qed.

Lemma bigminr_mkcond I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i =
     \big[minr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite !bigminr_maxr bigmaxr_mkcond; congr (- _).
by apply: eq_bigr => i _; case P.
Qed.

Lemma bigmaxr_split I r (P : pred I) (F1 F2 : I -> R) x :
  \big[maxr/x]_(i <- r | P i) (maxr (F1 i) (F2 i)) =
  maxr (\big[maxr/x]_(i <- r | P i) F1 i) (\big[maxr/x]_(i <- r | P i) F2 i).
Proof.
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?joinxx //.
by rewrite joinCA -!joinA joinCA.
Qed.

Lemma bigminr_split I r (P : pred I) (F1 F2 : I -> R) x :
  \big[minr/x]_(i <- r | P i) (minr (F1 i) (F2 i)) =
  minr (\big[minr/x]_(i <- r | P i) F1 i) (\big[minr/x]_(i <- r | P i) F2 i).
Proof.
rewrite !bigminr_maxr -oppr_max -bigmaxr_split; congr (- _).
by apply: eq_bigr => i _; rewrite oppr_min.
Qed.

Lemma bigmaxr_idl I r (P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i = maxr x (\big[maxr/x]_(i <- r | P i) F i).
Proof.
rewrite -big_filter; elim: [seq i <- r | P i] => [|i l ihl].
  by rewrite big_nil joinxx.
by rewrite big_cons joinCA -ihl.
Qed.

Lemma bigminr_idl I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i = minr x (\big[minr/x]_(i <- r | P i) F i).
Proof. by rewrite !bigminr_maxr {1}bigmaxr_idl oppr_max opprK. Qed.

Lemma bigmaxrID I r (a P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i =
  maxr (\big[maxr/x]_(i <- r | P i && a i) F i)
    (\big[maxr/x]_(i <- r | P i && ~~ a i) F i).
Proof.
rewrite -!(big_filter _ (fun _ => _ && _)) !filter_andb !big_filter.
rewrite ![in RHS](bigmaxr_mkcond _ _ F) !big_filter -bigmaxr_split.
have eqmax : forall i, P i ->
  maxr (if a i then F i else x) (if ~~ a i then F i else x) = maxr (F i) x.
  by move=> i _; case: (a i) => //=; rewrite joinC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -joinA -bigmaxr_idl ihl.
Qed.

Lemma bigminrID I r (a P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i =
  minr (\big[minr/x]_(i <- r | P i && a i) F i)
    (\big[minr/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite !bigminr_maxr -oppr_max -bigmaxrID. Qed.

Lemma bigmaxr_seq1 I (i : I) (F : I -> R) x :
  \big[maxr/x]_(j <- [:: i]) F j = maxr (F i) x.
Proof. by rewrite unlock /=. Qed.

Lemma bigminr_seq1 I (i : I) (F : I -> R) x :
  \big[minr/x]_(j <- [:: i]) F j = minr (F i) x.
Proof. by rewrite unlock /=. Qed.

Lemma bigmaxr_pred1_eq (I : finType) (i : I) (F : I -> R) x :
  \big[maxr/x]_(j | j == i) F j = maxr (F i) x.
Proof. by rewrite -big_filter filter_index_enum enum1 bigmaxr_seq1. Qed.

Lemma bigminr_pred1_eq (I : finType) (i : I) (F : I -> R) x :
  \big[minr/x]_(j | j == i) F j = minr (F i) x.
Proof. by rewrite bigminr_maxr bigmaxr_pred1_eq oppr_max !opprK. Qed.

Lemma bigmaxr_pred1 (I : finType) i (P : pred I) (F : I -> R) x :
  P =1 pred1 i -> \big[maxr/x]_(j | P j) F j = maxr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigmaxr_pred1_eq. Qed.

Lemma bigminr_pred1 (I : finType) i (P : pred I) (F : I -> R) x :
  P =1 pred1 i -> \big[minr/x]_(j | P j) F j = minr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigminr_pred1_eq. Qed.

Lemma bigmaxrD1 (I : finType) j (P : pred I) (F : I -> R) x :
  P j -> \big[maxr/x]_(i | P i) F i
    = maxr (F j) (\big[maxr/x]_(i | P i && (i != j)) F i).
Proof.
move=> Pj; rewrite (bigmaxrID _ (pred1 j)) [in RHS]bigmaxr_idl joinA.
by congr maxr; apply: bigmaxr_pred1 => i; rewrite /= andbC; case: eqP => //->.
Qed.

Lemma bigminrD1 (I : finType) j (P : pred I) (F : I -> R) x :
  P j -> \big[minr/x]_(i | P i) F i
    = minr (F j) (\big[minr/x]_(i | P i && (i != j)) F i).
Proof.
by move=> Pj; rewrite !bigminr_maxr (bigmaxrD1 _ _ Pj) oppr_max opprK.
Qed.

Lemma ler_bigmaxr_cond (I : finType) (P : pred I) (F : I -> R) x i0 :
  P i0 -> F i0 <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigmaxrD1 _ _ Pi0) lexU lexx. Qed.

Lemma bigminr_ler_cond (I : finType) (P : pred I) (F : I -> R) x i0 :
  P i0 -> \big[minr/x]_(i | P i) F i <= F i0.
Proof. by move=> Pi0; rewrite (bigminrD1 _ _ Pi0) leIx lexx. Qed.

Lemma ler_bigmaxr (I : finType) (F : I -> R) (i0 : I) x :
  F i0 <= \big[maxr/x]_i F i.
Proof. exact: ler_bigmaxr_cond. Qed.

Lemma bigminr_ler (I : finType) (F : I -> R) (i0 : I) x :
  \big[minr/x]_i F i <= F i0.
Proof. exact: bigminr_ler_cond. Qed.

Lemma bigmaxr_lerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x <= m /\ forall i, P i -> F i <= m)
    (\big[maxr/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[lexm leFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite leUx =>->.
rewrite bigmaxr_idl leUx => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigminr_gerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m <= x /\ forall i, P i -> m <= F i)
    (m <= \big[minr/x]_(i | P i) F i).
Proof.
rewrite bigminr_maxr ler_oppr; apply: (iffP idP).
  by move=> /bigmaxr_lerP [? lemF]; split=> [|??]; rewrite -ler_opp2 ?lemF.
by move=> [? lemF]; apply/bigmaxr_lerP; split=> [|??]; rewrite ler_opp2 ?lemF.
Qed.

Lemma bigmaxr_sup (I : finType) i0 (P : pred I) m (F : I -> R) x :
  P i0 -> m <= F i0 -> m <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0 ?; apply: le_trans (ler_bigmaxr_cond _ _ Pi0). Qed.

Lemma bigminr_inf (I : finType) i0 (P : pred I) m (F : I -> R) x :
  P i0 -> F i0 <= m -> \big[minr/x]_(i | P i) F i <= m.
Proof. by move=> Pi0 ?; apply: le_trans (bigminr_ler_cond _ _ Pi0) _. Qed.

Lemma bigmaxr_ltrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x < m /\ forall i, P i -> F i < m)
    (\big[maxr/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[ltxm ltFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite ltUx =>->.
rewrite bigmaxr_idl ltUx => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigminr_gtrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m < x /\ forall i, P i -> m < F i)
    (m < \big[minr/x]_(i | P i) F i).
Proof.
rewrite bigminr_maxr ltr_oppr; apply: (iffP idP).
  by move=> /bigmaxr_ltrP [? ltmF]; split=> [|??]; rewrite -ltr_opp2 ?ltmF.
by move=> [? ltmF]; apply/bigmaxr_ltrP; split=> [|??]; rewrite ltr_opp2 ?ltmF.
Qed.

Lemma bigmaxr_gerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m <= x \/ exists2 i, P i & m <= F i)
  (m <= \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[lemx|[i Pi lemFi]]]; last 2 first.
- by rewrite bigmaxr_idl lexU lemx.
- by rewrite (bigmaxrD1 _ _ Pi) lexU lemFi.
rewrite leNgt => /bigmaxr_ltrP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -leNgt; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -leNgt; right; exists i.
Qed.

Lemma bigminr_lerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x <= m \/ exists2 i, P i & F i <= m)
  (\big[minr/x]_(i | P i) F i <= m).
Proof.
rewrite bigminr_maxr ler_oppl; apply: (iffP idP).
  by move=> /bigmaxr_gerP [?|[i ??]]; [left|right; exists i => //];
    rewrite -ler_opp2.
by move=> [?|[i ??]]; apply/bigmaxr_gerP; [left|right; exists i => //];
  rewrite ler_opp2.
Qed.

Lemma bigmaxr_gtrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m < x \/ exists2 i, P i & m < F i)
  (m < \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[ltmx|[i Pi ltmFi]]]; last 2 first.
- by rewrite bigmaxr_idl ltxU ltmx.
- by rewrite (bigmaxrD1 _ _ Pi) ltxU ltmFi.
rewrite ltNge => /bigmaxr_lerP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -ltNge; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -ltNge; right; exists i.
Qed.

Lemma bigminr_ltrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x < m \/ exists2 i, P i & F i < m)
  (\big[minr/x]_(i | P i) F i < m).
Proof.
rewrite bigminr_maxr ltr_oppl; apply: (iffP idP).
  by move=> /bigmaxr_gtrP [?|[i ??]]; [left|right; exists i => //];
    rewrite -ltr_opp2.
by move=> [?|[i ??]]; apply/bigmaxr_gtrP; [left|right; exists i => //];
  rewrite ltr_opp2.
Qed.

Lemma bigmaxr_eq_arg (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> x <= F i) ->
  \big[maxr/x]_(i | P i) F i = F [arg max_(i > i0 | P i) F i]%O.
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le ler_bigmaxr_cond // andbT.
by apply/bigmaxr_lerP; split => //; exact: PxF.
Qed.

Lemma bigminr_eq_arg (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> F i <= x) ->
  \big[minr/x]_(i | P i) F i = F [arg min_(i < i0 | P i) F i]%O.
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigminr_ler_cond //=.
by apply/bigminr_gerP; split => //; exact: PFx.
Qed.

Lemma eq_bigmaxr (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in I & \big[maxr/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmaxr_eq_arg Pi0) //; eexists. Qed.

Lemma eq_bigminr (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in I & \big[minr/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigminr_eq_arg Pi0) //; eexists. Qed.

End bigmax_bigmin.
Module Exports.
Arguments bigmaxr_mkcond {R I r}.
Arguments bigmaxrID {R I r}.
Arguments bigmaxr_pred1 {R I} i {P F}.
Arguments bigmaxrD1 {R I} j {P F}.
Arguments ler_bigmaxr_cond {R I P F}.
Arguments ler_bigmaxr {R I F}.
Arguments bigmaxr_sup {R I} i0 {P m F}.
Arguments bigminr_mkcond {R I r}.
Arguments bigminrID {R I r}.
Arguments bigminr_pred1 {R I} i {P F}.
Arguments bigminrD1 {R I} j {P F}.
Arguments bigminr_ler_cond {R I P F}.
Arguments bigminr_ler {R I F}.
Arguments bigminr_inf {R I} i0 {P m F}.
Arguments bigmaxr_eq_arg {R I} i0 {P F}.
Arguments bigminr_eq_arg {R I} i0 {P F}.
Arguments eq_bigmaxr {R I} i0 {P F}.
Arguments eq_bigminr {R I} i0 {P F}.
End Exports.
End BigmaxBigminr.
Export BigmaxBigminr.Exports.

(** ** Matrices *)

Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).

Definition mx_norm x : K := (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:nngnum.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:nngnum.
Proof. by []. Qed.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
rewrite -nng_le; apply/BigmaxrNonneg.bigmaxr_lerP; split.
  exact: addr_ge0.
move=> ij _; rewrite mxE; apply: le_trans (ler_norm_add _ _) _.
rewrite ler_add // -nng_abs_le //= nng_le /= normr_id -nng_le;
  exact/BigmaxrNonneg.ler_bigmaxr.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le => /andP [/BigmaxrNonneg.bigmaxr_lerP [_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -nng_abs_eq0 eq_le (x0 (i,j)) // andTb nng_le /= normr_ge0.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%:nng)) /=.
  by elim/big_ind : _ => // a b /val_inj ->{a} /val_inj ->{b}; rewrite joinxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b != 0%:nng by exists i.
  by apply: contra H => b0; rewrite join_r.
+ suff /Ha[i xi] : a != 0%:nng by exists i.
  by apply: contra H => a0; rewrite join_l // ltW.
Qed.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/eqP/mx_norm_eq0->|x0] := boolP (mx_norm x == 0).
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -nng_abs_le; last by rewrite addr_ge0 // mulrn_wge0.
apply/BigmaxrNonneg.bigmaxr_gerP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; by rewrite normr_id.
Qed.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Proof.
congr (_%:nngnum).
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE nng_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite join_r | rewrite join_l // ltW].
Qed.

Definition matrix_normedZmodMixin (K : numDomainType) (m n : nat) :=
  @Num.NormedMixin _ _ _ (@mx_norm K m.+1 n.+1) (@ler_mx_norm_add _ _ _)
    (@mx_norm_eq0 _ _ _) (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Canonical matrix_normedZmodType (K : numDomainType) (m n : nat) :=
  NormedZmodType K 'M[K]_(m.+1, n.+1) (matrix_normedZmodMixin K m n).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Lemma mx_norm_ball :
  @ball _ [pseudoMetricType K of 'M[K^o]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Proof.
rewrite /= /normr /= predeq3E => x e y; split.
- move=> xe_y; rewrite /ball_ mx_normE.
  (* TODO:  lemma : ball x e y -> 0 < e *)
  have lee0 : ( 0 < e) by rewrite (le_lt_trans _ (xe_y ord0 ord0)) //.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  rewrite -nng_lt; apply/BigmaxrNonneg.bigmaxr_ltrP.
- split; [rewrite nng_lt //= | move=> ??; rewrite !mxE; exact: xe_y].
  rewrite /ball_; rewrite mx_normE => H.
  have lee0 : (0 < e) by rewrite (le_lt_trans _ H) // nonnegnum_ge0.
  move : H.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  move => /BigmaxrNonneg.bigmaxr_ltrP => -[e0 xey] i j.
  move: (xey (i, j)); rewrite !mxE; exact.
Qed.

Definition matrix_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K 'M[K^o]_(m.+1, n.+1) matrix_PseudoMetricNormedZmodMixin.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite nng_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
rewrite nonneg_maxr; congr (maxr _ _)%:nngnum; exact/val_inj.
Qed.

Definition matrix_NormedModMixin := NormedModMixin mx_normZ.
Canonical matrix_normedModType :=
  NormedModType K 'M[K^o]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_NormedModule.

(** ** Pairs *)

Section prod_NormedModule.
Context {K : numDomainType} {U V : normedModType K}.

Lemma prod_normE (x : U * V) : `| x | =
  (Num.max `| x.1 |%:nng `|x.2|%:nng)%:nngnum.
Proof. by []. Qed.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof.
rewrite prod_normE /= nonneg_maxr /=.
by congr (maxr _ _ )%:nngnum; apply val_inj => /=; rewrite normmZ.
Qed.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite nng_ltUx /=; split=> /andP.
Qed.

Lemma prod_norm_ball : @ball _ [pseudoMetricType K of U * V] = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

Definition prod_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin prod_norm_ball.
Canonical prod_topologicalZmodType :=
  PseudoMetricNormedZmodType K (U * V) prod_PseudoMetricNormedZmodMixin.

Definition prod_NormedModMixin := NormedModMixin prod_norm_scale.
Canonical prod_normedModType :=
  NormedModType K (U * V) prod_NormedModMixin.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangke m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof. apply ler_norm_add. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. apply ler_norm_add. Qed.

End example_of_sharing.

Section prod_NormedModule_lemmas.

Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma cvg_norm2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: cvg_normP. Qed.

(* Lemma cvg_norm_supP {F : set (set U)} {G : set (set V)} *)
(*   {FF : Filter F} {FG : Filter G} (y : U) (z : V): *)
(*   (F, G) --> (y, z) <-> *)
(*   forall eps : {posnum R}, {near F & G, forall y' z', *)
(*           (`|[y - y']| < eps) /\ (`|[z - z']| < eps) }. *)
(* Proof. *)
(* rewrite cvg_ballP; split => [] P eps. *)
(* - have [[A B] /=[FA GB] ABP] := P eps; exists (A, B) => -//[a b] [/= Aa Bb]. *)
(*   apply/andP; rewrite -ltr_maxl. *)
(*   have /= := (@sub_ball_norm_rev _ _ (_, _)). *)

Lemma cvg_norm2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. by rewrite cvg_normP. Qed.

End prod_NormedModule_lemmas.
Arguments cvg_norm2 {_ _ _ F G FF FG}.

(** Rings with absolute values are normed modules *)

(*Definition AbsRing_NormedModMixin (K : absRingType) :=
  @NormedModule.Mixin K _ _ _ (abs : K^o -> R) ler_abs_add absrM (ball_absE K)
  absr0_eq0.
Canonical AbsRing_NormedModType (K : absRingType) :=
  NormedModType K K^o (AbsRing_NormedModMixin _).*)

Lemma R_normZ (R : numDomainType) (l : R) (x : R^o) :
  `| l *: x | = `| l | * `| x |.
Proof. by rewrite normrM. Qed.

Definition numFieldType_NormedModMixin (R : numFieldType) :=
  NormedModMixin (@R_normZ R).
Canonical numFieldType_normedModType (R : numFieldType) :=
  NormedModType R R^o (numFieldType_NormedModMixin R).

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : numFieldType} {V : normedModType K}.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/=x y]; apply/cvg_normP=> _/posnumP[e].
rewrite !near_simpl /=; near=> a b => /=; rewrite opprD addrACA.
by rewrite normm_lt_split //; [near: a|near: b]; apply: cvg_norm.
Grab Existential Variables. all: end_near. Qed.

End NVS_continuity.

(* kludge *)
Global Instance filter_locally (K' : numFieldType) (k : K'^o) :
  Filter (locally k).
Proof.
exact: (@locally_filter [topologicalType of K'^o]).
Qed.

Section NVS_continuity1.
Context {K : numFieldType} {V : normedModType K}.
Local Notation "'+oo'" := (pinfty_locally K).

Lemma scale_continuous : continuous (fun z : K^o * V => z.1 *: z.2).
Proof.
move=> [k x]; apply/cvg_normP=> _/posnumP[e].
rewrite !near_simpl /=; near +oo => M; near=> l z => /=.
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normmZ.
  rewrite (le_lt_trans (ler_pmul _ _ (_ : _ <= `|k| + 1) (lexx _))) //.
  by rewrite ler_addl.
  rewrite -ltr_pdivl_mull // ?(lt_le_trans ltr01) ?ler_addr //; near: z.
  by apply: cvg_norm; rewrite // mulr_gt0 // ?invr_gt0 ltr_paddl.
have zM : @normr _ V z < M.
  by near: z; near: M; apply: cvg_bounded; apply: cvg_refl.
rewrite (le_lt_trans (ler_pmul _ _ (lexx _) (_ : _ <= M))) // ?ltW //.
rewrite -ltr_pdivl_mulr ?(le_lt_trans _ zM) //.
near: l; apply: (cvg_norm (_ : K^o)) => //.
by rewrite divr_gt0 //; near: M; exists 0; rewrite real0.
(* NB: the last three lines used to be one *)
Grab Existential Variables. all: end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_const _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K^o => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_const _) (scale_continuous (_, _))).
Qed.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; rewrite -scaleN1r => P /scaler_continuous /=.
by rewrite !locally_nearE near_map; apply: filterS => x'; rewrite scaleN1r.
Qed.

End NVS_continuity1.

Section limit_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.

Lemma cvg_cst (a : V) (F : set (set V)) {FF : Filter F} : (fun=> a) @ F --> a.
Proof. exact: cst_continuous. Qed.
Hint Resolve cvg_cst : core.

Lemma cvgD (F : set (set T)) (FF : Filter F) (f g : T -> V) (a b : V) :
  f @ F --> a -> g @ F --> b -> (f \+ g) @ F --> a + b.
Proof. by move=> ??; apply: cvg_continuous2 => //; exact: add_continuous. Qed.

Lemma continuousD (f g : T -> V) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun x => f x + g x)}.
Proof. by move=> ??; apply: cvgD. Qed.

Lemma cvgZ (F : set (set T)) (FF : Filter F) (f : T -> K) (g : T -> V)
  (k : K^o) (a : V) :
  f @ F --> k -> g @ F --> a -> (fun x => (f x) *: (g x)) @ F --> k *: a.
Proof. move=> ??; apply: cvg_continuous2 => //; exact: scale_continuous. Qed.

Lemma cvgZl (F : set (set T)) (FF : Filter F) (f : T -> K) (a : V) (k : K^o) :
  f @ F --> k -> (fun x => (f x) *: a) @ F --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cst_continuous. Qed.

Lemma cvgZr (F : set (set T)) (FF : Filter F) (f : T -> V) (k : K) (a : V) :
  f @ F --> a -> k \*: f  @ F --> k *: a.
Proof.
apply: cvgZ => //; exact: (@cst_continuous _ [topologicalType of K^o]).
Qed.

Lemma continuousZ (f : T -> V) k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl (k : T -> K^o) (f : V) x :
  {for x, continuous k} -> {for x, continuous (fun z => k z *: f)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma cvgN (F : set (set T)) (FF : Filter F) (f : T -> V) (a : V) :
  f @ F --> a -> (fun x => - f x) @ F --> - a.
Proof. by move=> ?; apply: cvg_continuous => //; apply: opp_continuous. Qed.

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma cvgM (x y : K^o) : z.1 * z.2 @[z --> (x, y)] --> x * y.
Proof. exact: (@scale_continuous _ [normedModType K of K^o]). Qed.

Lemma continuousM (f g : T -> K^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun x => f x * g x)}.
Proof. by move=> fc gc; apply: cvg_comp2 fc gc _; apply: cvgM. Qed.

End limit_composition.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : numFieldType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (PseudoMetric.Pack base)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : Complete.class_of K T :=
  @Complete.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack :=
  fun bT (b : NormedModule.class_of K T) & phant_id (@NormedModule.class K phK bT) b =>
  fun mT m & phant_id (@Complete.class K mT) (@Complete.Class K T b m) =>
    Pack phK (@Class T b m).
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition normedModType := @NormedModule.Pack K phK cT xclass.
Definition completeType := @Complete.Pack _ cT xclass.
Definition complete_zmodType := @GRing.Zmodule.Pack completeType xclass.
Definition complete_lmodType := @GRing.Lmodule.Pack K phK completeType xclass.
Definition complete_normedZmodType := @Num.NormedZmodule.Pack K phK completeType xclass.
Definition complete_normedModType := @NormedModule.Pack K phK completeType xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> Complete.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Canonical complete_zmodType.
Canonical complete_lmodType.
Canonical complete_normedZmodType.
Canonical complete_normedModType.
Notation completeNormedModType K := (type (Phant K)).
Notation "[ 'completeNormedModType' K 'of' T ]" := (@pack _ (Phant K) T _ _ idfun _ _ idfun)
  (at level 0, format "[ 'completeNormedModType'  K  'of'  T ]") : form_scope.
End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

(** * Extended Types *)

(** * The topology on real numbers *)

(* TODO: Remove R_complete_lim and use lim instead *)
(* Definition R_lim (F : (R -> Prop) -> Prop) : R := *)
(*   sup (fun x : R => `[<F (ball (x + 1) 1)>]). *)

(* move: (Lub_Rbar_correct (fun x : R => F (ball (x + 1) 1))). *)
(* move Hl : (Lub_Rbar _) => l{Hl}; move: l => [x| |] [Hx1 Hx2]. *)
(* - case: (HF (Num.min 2 eps%:num / 2)%:pos) => z Hz. *)
(*   have H1 : z - Num.min 2 eps%:num / 2 + 1 <= x + 1. *)
(*     rewrite ler_add //; apply/RleP/Hx1. *)
(*     apply: filterS Hz. *)
(*     rewrite /ball /= => u; rewrite /AbsRing_ball absrB ltr_distl. *)
(*     rewrite absrB ltr_distl. *)
(*     case/andP => {Hx1 Hx2 FF HF x F} Bu1 Bu2. *)
(*     have H : Num.min 2 eps%:num <= 2 by rewrite ler_minl lerr. *)
(*     rewrite addrK -addrA Bu1 /= (ltr_le_trans Bu2) //. *)
(*     rewrite -addrA ler_add // -addrA addrC ler_subr_addl. *)
(*     by rewrite ler_add // ler_pdivr_mulr // ?mul1r. *)
(*   have H2 : x + 1 <= z + Num.min 2 eps%:num / 2 + 1. *)
(*     rewrite ler_add //; apply/RleP/(Hx2 (Finite _)) => v Hv. *)
(*     apply: Rbar_not_lt_le => /RltP Hlt. *)
(*     apply: filter_not_empty. *)
(*     apply: filterS (filterI Hz Hv). *)
(*     rewrite /ball /= => w []; rewrite /AbsRing_ball //. *)
(*     rewrite absrB ltr_distl => /andP[_ Hw1]. *)
(*     rewrite absrB ltr_distl addrK => /andP[Hw2 _]. *)
(*     by move: (ltr_trans (ltr_trans Hw1 Hlt) Hw2); rewrite ltrr. *)
(*   apply: filterS Hz. *)
(*   rewrite /ball /= => u; rewrite /AbsRing_ball absrB absRE 2!ltr_distl. *)
(*   case/andP => {Hx1 Hx2 F FF HF} H H0. *)
(*   have H3 : Num.min 2 eps%:num <= eps by rewrite ler_minl lerr orbT. *)
(*   apply/andP; split. *)
(*   - move: H1; rewrite -ler_subr_addr addrK ler_subl_addr => H1. *)
(*     rewrite ltr_subl_addr // (ltr_le_trans H0) //. *)
(*     rewrite -ler_subr_addr (ler_trans H1) //. *)
(*     rewrite -ler_subr_addl -!addrA (addrC x) !addrA subrK. *)
(*     rewrite ler_subr_addr -mulrDl ler_pdivr_mulr //. *)
(*     by rewrite -mulr2n -mulr_natl mulrC ler_pmul. *)
(*   - move: H2; rewrite -ler_subr_addr addrK. *)
(*     move/ler_lt_trans; apply. *)
(*     move: H; rewrite // ltr_subl_addr => H. *)
(*     rewrite -ltr_subr_addr (ltr_le_trans H) //. *)
(*     rewrite addrC -ler_subr_addr -!addrA (addrC u) !addrA subrK. *)
(*     rewrite -ler_subl_addr opprK -mulrDl ler_pdivr_mulr // -mulr2n -mulr_natl. *)
(*     by rewrite mulrC ler_pmul. *)
(* - case (HF 1%:pos) => y Fy. *)
(*   case: (Hx2 (y + 1)) => x Fx. *)
(*   apply: Rbar_not_lt_le => Hlt. *)
(*   apply: filter_not_empty. *)
(*   apply: filterS (filterI Fy Fx) => z [Hz1 Hz2]. *)
(*   apply: Rbar_le_not_lt Hlt;  apply/RleP. *)
(*   rewrite -(ler_add2r (-(y - 1))) opprB !addrA -![in X in _ <= X]addrA. *)
(*   rewrite (addrC y) ![in X in _ <= X]addrA subrK. *)
(*   suff : `|x + 1 - y|%R <= 1 + 1 by rewrite ler_norml => /andP[]. *)
(*   rewrite ltrW // (@subr_trans _ z). *)
(*   by rewrite (ler_lt_trans (ler_norm_add _ _)) // ltr_add // distrC. *)
(* - case: (HF 1%:pos) => y Fy. *)
(*   case: (Hx1 (y - 1)); by rewrite addrAC addrK. *)
(* Qed. *)
(* Admitted. *)

Arguments cvg_normW {_ _ F FF}.

Lemma R_complete (R : realType) (F : set (set R^o)) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down (mem A)).
have /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup (mem D); first split.
- exists (x0 - 1); rewrite in_setE => A FA.
  apply/existsbP; near F => x; first exists x.
    by rewrite ler_distW 1?distrC 1?ltW ?andbT ?in_setE //; near: x.
- exists (x0 + 1); apply/forallbP => x; apply/implyP; rewrite in_setE.
  move=> /(_ _ x01) /existsbP [y /andP[]]; rewrite in_setE.
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltr_subl_addr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup (mem D)).
apply: (cvg_normW (_ : R^o)) => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl sup_upper_bound //=.
  apply: sup_le_ub => //; first by case: D_has_sup.
  apply/forallbP => y; apply/implyP; rewrite in_setE.
  move=> /(_ (ball_ (fun x => `| x |) x eps%:num) _) /existsbP [].
    by near: x; apply: nearP_dep; apply: F_cauchy.
  move=> z /andP[]; rewrite in_setE /ball_ ltr_distl ltr_subl_addr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite in_setE /D /= => A FA; near F => y.
apply/existsbP; exists y; apply/andP; split.
  by rewrite in_setE; near: y.
rewrite ler_subl_addl -ler_subl_addr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Grab Existential Variables. all: end_near. Qed.

Canonical R_completeType (R : realType) := CompleteType R^o (@R_complete R).
(* Canonical R_NormedModule := [normedModType R of R^o]. *)

Canonical R_CompleteNormedModule (R : realType) := [completeNormedModType R of R^o].

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R^o) := within (fun u => u < x) (locally x).
Definition at_right (x : R^o) := within (fun u : R => x < u) (locally x).
(* :TODO: We should have filter notation ^- and ^+ for these *)

Global Instance at_right_proper_filter (x : R^o) : ProperFilter (at_right x).
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x + d%:num / 2))].
apply; last (by rewrite ltr_addl); rewrite /=.
rewrite opprD !addrA subrr add0r normrN normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter (at_left x).
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last (by rewrite ltr_subl_addl ltr_addr); rewrite /=.
rewrite opprD !addrA subrr add0r opprK normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.
End at_left_right.

Typeclasses Opaque at_left at_right.

(** Continuity of norm *)

Lemma continuous_norm {K : numFieldType} {V : normedModType K} :
  continuous ((@normr _ V) : V -> K^o).
Proof.
move=> x; apply/(@cvg_normP _ [normedModType K of K^o]) => _/posnumP[e] /=.
rewrite !near_simpl; apply/locally_normP; exists e%:num => // y Hy.
exact/(le_lt_trans (ler_dist_dist _ _)).
Qed.

(* :TODO: yet, not used anywhere?! *)
Lemma cvg_norm0 {U} {K : numFieldType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : K^o)
  -> f @ F --> (0 : V).
Proof.
move=> /(cvg_norm (_ : K^o)) fx0; apply/cvg_normP => _/posnumP[e].
rewrite near_simpl; have := fx0 _ [gt0 of e%:num]; rewrite near_simpl.
by apply: filterS => x; rewrite !sub0r !normrN [ `|_| ]ger0_norm.
Qed.

Section TODO_add_to_ssrnum.

Lemma maxr_real (K : realDomainType) (x y : K) :
  x \is Num.real -> y \is Num.real -> maxr x y \is Num.real.
Proof.
by rewrite !realE => /orP[|] x0 /orP[|] y0; rewrite lexU leUx x0 y0 !(orbT,orTb).
Qed.

Lemma bigmaxr_real (K : realDomainType) (R : choiceType) (x : K) (D : seq R) (f : R -> K):
  x \is Num.real ->
  (forall x, x \in D -> f x \is Num.real) ->
  \big[maxr/x]_(n <- D) f n \is Num.real.
Proof.
move=> ?; elim/big_ind : _ => // *; by [rewrite maxr_real | rewrite num_real].
Qed.

End TODO_add_to_ssrnum.

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_locally K).

(* TODO: simplify using extremumP when PR merged in mathcomp *)
Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  [cvg a in V] -> {M | forall n, `|a n| <= M}.
Proof.
move=> a_cvg; suff: exists M, M \is Num.real /\ forall n, `|a n| <= M.
  by move=> /(@getPex [pointedType of K^o]) [?]; set M := get _; exists M.
near +oo => M.
have [//|Mreal [N _ /(_ _ _) /ltW a_leM]] := !! near (cvg_bounded_real a_cvg) M.
exists (maxr `|M|%:nng (\big[maxr/0%:nng]_(n < N) `|a (val (rev_ord n))|%:nng))%:nngnum.
split => [|/= n]; first by rewrite realE nng_lexU normr_ge0.
rewrite nng_lexU; have [nN|nN] := leqP N n.
  by rewrite (@le_trans _ _ M) //=; [exact: a_leM | rewrite real_ler_norm].
apply/orP; right => {a_leM}; elim: N n nN=> //= N IHN n.
rewrite leq_eqVlt => /orP[/eqP[->] |/IHN a_le];
by rewrite big_ord_recl subn1 /= nng_lexU ?a_le ?lexx ?orbT.
Grab Existential Variables. all: end_near. Qed.

End cvg_seq_bounded.

Section some_sets.
Variable R : realFieldType (* TODO: can we generalize to numFieldType? *).

(** Some open sets of [R] *)

Lemma open_lt (y : R) : open [set x : R^o | x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0; exists (y - x) => // z.
by rewrite /= distrC ltr_distl addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt (y : R) : open [set x : R^o | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= distrC ltr_distl opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : open [set x : R^o | x != y].
Proof.
rewrite (_ : xpredC _ = [set x | x < y] `|` [set x | x > y] :> set _) /=.
  by apply: openU => //; apply: open_lt.
rewrite predeqE => x /=; rewrite eq_le !leNgt negb_and !negbK orbC.
by symmetry; apply (rwP orP).
Qed.

(** Some closed sets of [R] *)

Lemma closed_le (y : R) : closed [set x : R^o | x <= y].
Proof.
rewrite (_ : [set x | x <= _] = ~` (> y) :> set _).
  by apply: closedC; exact: open_gt.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_ge (y : R) : closed [set x : R^o | y <= x].
Proof.
rewrite (_ : (>= _) = ~` [set x | x < y] :> set _).
  by apply: closedC; exact: open_lt.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_eq (y : R) : closed [set x : R^o | x = y].
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

End some_sets.

Section segment.
Variable R : realType.

(** properties of segments in [R] *)

Lemma segment_connected (a b : R) : connected [set x : R^o | x \in `[a, b]].
Proof.
move=> A [y Ay] Aop Acl.
move: Aop; apply: contrapTT; rewrite predeqE => /asboolPn /existsp_asboolPn [x].
wlog ltyx : a b (* leab *) A y Ay Acl x / y < x.
  move=> scon; case: (ltrP y x); first exact: scon.
  rewrite le_eqVlt; case/orP=> [/eqP xey|ltxy].
    move: Acl => [B Bcl AeabB].
    have sAab : A `<=` [set x | x \in `[a, b]] by rewrite AeabB => ? [].
    move=> /asboolPn; rewrite asbool_and=> /nandP [/asboolPn /(_ (sAab _))|] //.
    by move=> /imply_asboolPn [abx nAx] [C Cop AeabC]; apply: nAx; rewrite xey.
  move=> Axneabx [C Cop AeabC].
  have setIN B : A = [set x | x \in `[a, b]] `&` B ->
    [set - x | x in A] = [set x | x \in `[(- b), (- a)]] `&` [set - x | x in B].
    move=> AeabB; rewrite predeqE => z; split.
      move=> [t At]; have := At; rewrite AeabB => - [abt Bt] <-.
      by split; [rewrite oppr_itvcc !opprK|exists t].
    move=> [abz [t Bt tez]]; exists t => //; rewrite AeabB; split=> //.
    by rewrite -[t]opprK tez oppr_itvcc.
  apply: (scon (- b) (- a) (* _ *) [set - x | x in A] (- y)) (- x) _ _ _.
  - by exists y.
  - move: Acl => [B Bcl AeabB]; exists [set - x | x in B]; first exact: closedN.
    exact: setIN.
  - by rewrite ltr_oppr opprK.
  - move=> Axeabx; apply: Axneabx; split=> [|abx].
      by rewrite AeabC => - [].
    have /Axeabx [z Az zex] : - x \in `[(- b), (- a)].
      by rewrite oppr_itvcc !opprK.
    by rewrite -[x]opprK -zex opprK.
  - by exists [set - x | x in C]; [apply: openN|apply: setIN].
move: Acl => [B Bcl AeabB].
have sAab : A `<=` [set x | x \in `[a, b]] by rewrite AeabB => ? [].
move=> /asboolPn; rewrite asbool_and => /nandP [/asboolPn /(_ (sAab _))|] //.
move=> /imply_asboolPn [abx nAx] [C Cop AeabC].
set Altx := fun y => y \in A `&` [set y | y < x].
have Altxn0 : reals.nonempty Altx by exists y; rewrite in_setE.
have xub_Altx : x \in ub Altx.
  by apply/ubP => ?; rewrite in_setE => - [_ /ltW].
have Altxsup : has_sup Altx by apply/has_supP; split=> //; exists x.
set z := sup Altx.
have yxz : z \in `[y, x].
  rewrite inE; apply/andP; split; last exact: sup_le_ub.
  by apply/sup_upper_bound => //; rewrite in_setE.
have Az : A z.
  rewrite AeabB; split.
    suff : {subset `[y, x] <= `[a, b]} by apply.
    by apply/subitvP; rewrite /= (itvP abx); have /sAab/itvP-> := Ay.
  apply: Bcl => D [_ /posnumP[e] ze_D].
  have [t] := sup_adherent Altxsup [gt0 of e%:num].
  rewrite in_setE => - [At lttx] ltzet.
  exists t; split; first by move: At; rewrite AeabB => - [].
  apply/ze_D; rewrite /= ltr_distl.
  apply/andP; split; last by rewrite -ltr_subl_addr.
  rewrite ltr_subl_addr; apply: ltr_spaddr => //.
  by apply/sup_upper_bound => //; rewrite in_setE.
have ltzx : 0 < x - z.
  have : z <= x by rewrite (itvP yxz).
  by rewrite subr_gt0 le_eqVlt => /orP [/eqP zex|] //; move: nAx; rewrite -zex.
have := Az; rewrite AeabC => - [_ /Cop [_ /posnumP[e] ze_C]].
suff [t Altxt] : exists2 t, Altx t & z < t.
  by rewrite ltNge => /negP; apply; apply/sup_upper_bound.
exists (z + (minr (e%:num / 2) ((PosNum ltzx)%:num / 2))); last first.
  by rewrite ltr_addl.
rewrite in_setE; split; last first.
  rewrite -[_ < _]ltr_subr_addl ltIx; apply/orP; right.
  by rewrite ltr_pdivr_mulr // mulrDr mulr1 ltr_addl.
rewrite AeabC; split; last first.
  apply: ze_C; rewrite /ball_ ltr_distl.
  apply/andP; split; last by rewrite -addrA ltr_addl.
  rewrite -addrA gtr_addl subr_lt0 ltIx; apply/orP; left.
  by rewrite [X in _ < X]splitr ltr_addl.
rewrite inE; apply/andP; split.
  by apply: ler_paddr => //; have := Az; rewrite AeabB => - [/itvP->].
have : x <= b by rewrite (itvP abx).
apply: le_trans; rewrite -ler_subr_addl leIx; apply/orP; right.
by rewrite ler_pdivr_mulr // mulrDr mulr1 ler_addl; apply: ltW.
Qed.

Lemma segment_closed (a b : R) : closed [set x : R^o | x \in `[a, b]].
Proof.
have -> : [set x | x \in `[a, b]] = [set x | x >= a] `&` [set x | x <= b].
  by rewrite predeqE => ?; rewrite inE; split=> [/andP [] | /= [->]].
by apply closedI; [apply closed_ge | apply closed_le].
Qed.

Lemma segment_compact (a b : R) : compact [set x : R^o | x \in `[a, b]].
Proof.
case: (lerP a b) => [leab|ltba]; last first.
  by move=> F FF /filter_ex [x abx]; move: ltba; rewrite (itvP abx).
rewrite compact_cover => I D f fop sabUf.
set B := [set x | exists2 D' : {fset I}, {subset D' <= D} &
  [set y | y \in `[a, x]] `<=` \bigcup_(i in [set i | i \in D']) f i /\
  (\bigcup_(i in [set i | i \in D']) f i) x].
set A := [set x | x \in `[a, b]] `&` B.
suff Aeab : A = [set x | x \in `[a, b]].
  suff [_ [D' ? []]] : A b by exists D'.
  by rewrite Aeab inE/=; apply/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite inE/=; apply/andP.
  exists a; split=> //; have /sabUf [i Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE in_setE => /eqP->.
  split; last by exists i => //; rewrite inE.
  move=> x aex; exists i; [by rewrite inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [D' sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite in_setE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists D' => //; split; last by exists i => //; apply/xe_fi.
  move=> z ayz; case: (lerP z x) => [lezx|ltxz].
    by apply/saxUf; rewrite inE/= (itvP ayz) lezx.
  exists i=> //; apply/xe_fi; rewrite /ball_ distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltr_subl_addl; apply: le_lt_trans lezy _; rewrite -ltr_subl_addr.
    by have := xe_y; rewrite /ball_ => /ltr_distW.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: segment_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [D' sD [sayUf _]]] xe_y]] := locally_ball x e.
exists (i |` D')%fset; first by move=> j /fset1UP[->|/sD] //; rewrite in_setE.
split=> [z axz|]; last first.
  exists i; first by rewrite !inE eq_refl.
  by apply/xe_fi; rewrite /ball_ subrr normr0.
case: (lerP z y) => [lezy|ltyz].
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite inE/= (itvP axz) lezy.
  by exists j => //; rewrite inE orbC Dj.
exists i; first by rewrite !inE eq_refl.
apply/xe_fi; rewrite /ball_ ger0_norm; last first.
  by rewrite subr_ge0 (itvP axz).
rewrite ltr_subl_addl -ltr_subl_addr; apply: lt_trans ltyz.
by apply: ltr_distW; rewrite distrC.
Qed.

End segment.

Lemma ler0_addgt0P (R : numFieldType) (x : R) :
  reflect (forall e, e > 0 -> x <= e) (x <= 0).
Proof.
apply: (iffP idP) => [lex0 e egt0|lex0]; first by rewrite (le_trans lex0)// ltW.
have [|//|x0] := comparable_leP.
  by rewrite (@comparabler_trans _ 1)// /Order.comparable ?lex0// ler01 orbT.
have : x <= x / 2 by rewrite lex0// divr_gt0.
rewrite {1}(splitr x) ger_addl pmulr_lle0 // => /(lt_le_trans x0);
  by rewrite ltxx.
Qed.

Lemma IVT (R : realType) (f : R^o -> R^o) (a b v : R^o) :
  a <= b -> {in `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab; wlog : f v / f a <= f b.
  move=> ivt; case: (lerP (f a) (f b)) => [|/ltW lefba].
    exact: ivt.
  move=> fcont fabv; have [] := ivt (fun x => - f x) (- v).
  - by rewrite ler_oppr opprK.
  - by move=> x /fcont; apply: (@continuousN _ [normedModType R of R^o]).
  - by rewrite -oppr_max -oppr_min ler_oppr opprK ler_oppr opprK andbC.
  by move=> c cab /eqP; rewrite eqr_opp => /eqP; exists c.
move=> lefab fcont; rewrite meet_l // join_r // => /andP [].
rewrite le_eqVlt => /orP [/eqP<- _|ltfav].
  by exists a => //; rewrite inE/= lexx leab.
rewrite le_eqVlt => /orP [/eqP->|ltvfb].
  by exists b => //; rewrite inE/= lexx leab.
set A := [pred c | (c <= b) && (f c <= v)].
have An0 : reals.nonempty A by exists a; apply/andP; split=> //; apply: ltW.
have supA : has_sup A.
  by apply/has_supP; split=> //; exists b; apply/ubP => ? /andP [].
have supAab : sup A \in `[a, b].
  rewrite inE; apply/andP; split; last first.
    by apply: sup_le_ub => //; apply/ubP => ? /andP [].
  by apply: sup_upper_bound => //; rewrite inE leab andTb ltW.
exists (sup A) => //; have lefsupv : f (sup A) <= v.
  rewrite leNgt; apply/negP => ltvfsup.
  have vltfsup : 0 < f (sup A) - v by rewrite subr_gt0.
  have /fcont /(_ _ (@locally_ball _ [normedModType R of R^o] _ (PosNum vltfsup))) [_/posnumP[d] supdfe]
    := supAab.
  have [t At supd_t] := sup_adherent supA [gt0 of d%:num].
  suff /supdfe : @ball _ [normedModType R of R^o] (sup A) d%:num t.
    rewrite /= /ball /= ltr_norml => /andP [_].
    by rewrite ltr_add2l ltr_oppr opprK ltNge; have /andP [_ ->] := At.
  rewrite /= /ball /= ger0_norm.
    by rewrite ltr_subl_addr -ltr_subl_addl.
  by rewrite subr_ge0 sup_upper_bound.
apply/eqP; rewrite eq_le; apply/andP; split=> //.
rewrite -subr_le0; apply/ler0_addgt0P => _/posnumP[e].
rewrite ler_subl_addr -ler_subl_addl ltW //.
have /fcont /(_ _ (@locally_ball _ [normedModType R of R^o] _ e)) [_/posnumP[d] supdfe] := supAab.
have atrF := at_right_proper_filter (sup A); near (at_right (sup A)) => x.
have /supdfe /= : @ball _ [normedModType R of R^o] (sup A) d%:num x.
  by near: x; rewrite /= locally_simpl; exists d%:num => //.
rewrite /= => /ltr_distW; apply: le_lt_trans.
rewrite ler_add2r ltW //; suff : forall t, t \in `](sup A), b] -> v < f t.
  apply; rewrite inE; apply/andP; split; first by near: x; exists 1.
  near: x; exists (b - sup A).
    rewrite subr_gt0 lt_def (itvP supAab) andbT; apply/negP => /eqP besup.
    by move: lefsupv; rewrite leNgt -besup ltvfb.
  move=> t lttb ltsupt; move: lttb; rewrite /= distrC.
  by rewrite gtr0_norm ?subr_gt0 // ltr_add2r; apply: ltW.
move=> t /andP [ltsupt /= letb]; rewrite ltNge; apply/negP => leftv.
move: ltsupt => /=; rewrite ltNge => /negP; apply; apply: sup_upper_bound => //.
by rewrite inE leftv letb.
Grab Existential Variables. all: end_near. Qed.

(** Local properties in [R] *)

(* TODO: generalize to numFieldType? *)
Lemma lt_ereal_locally (R : realFieldType) (a b : {ereal R}) (x : R) :
  (a < x%:E)%E -> (x%:E < b)%E ->
  exists delta : {posnum R},
    forall y, `|y - x| < delta%:num -> ((a < y%:E) && (y%:E < b))%E.
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog. (*BUG*)
  move=> {a b} a b ltxa ltxb.
  have m_gt0 : (minr ((x - a) / 2) ((b - x) / 2) > 0).
    by rewrite ltxI !divr_gt0 // ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite ltxI !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite 2!lte_fin (lt_trans _ ay) ?(lt_trans yb) //=.
    by rewrite -subr_gt0 opprD addrA {1}[b - x]splitr addrK divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[x - a]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (x + 1); rewrite ?lte_fin ?ltr_addl //.
  by exists d => y /dP /andP[->].
- have [//||d dP] := wlog (x - 1) b; rewrite ?lte_fin ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->].
- by exists 1%:pos.
Qed.

(* TODO: generalize to numFieldType? *)
Lemma locally_interval (R : realFieldType) (P : R -> Prop) (x : R^o) (a b : {ereal R}) :
  (a < x%:E)%E -> (x%:E < b)%E ->
  (forall y : R, a < y%:E -> y%:E < b -> P y)%E ->
  locally x P.
Proof.
move => Hax Hxb Hp; case: (lt_ereal_locally Hax Hxb) => d Hd.
exists d%:num => //= y; rewrite /= distrC.
by move=> /Hd /andP[??]; apply: Hp.
Qed.

(** * Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : {posnum R}, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
(*     forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) -> *)
(*   {near x & y, forall x y, P x y} ->  *)
(*   {near x & y, forall x y, Q x y}. *)
(* Proof. *)
(* move=> P Q x y /= K => /locallyP [d _ H]. *)
(* apply/locallyP; exists d => // uv Huv. *)
(* by apply (K d) => //. *)
(* Qed. *)

(* Lemma locally_2d_1d_const_x : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally y (fun t => P x t). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* exists d => // z Hz. *)
(* by apply (Hd (x, z)). *)
(* Qed. *)

(* Lemma locally_2d_1d_const_y : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally x (fun t => P t y). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* apply/locallyP; exists d => // z Hz. *)
(* by apply (Hd (z, y)). *)
(* Qed. *)

(* Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R): *)
(*   (\near x & y, P x y) -> *)
(*   \forall u \near x & v \near y, *)
(*       forall (t : R), 0 <= t <= 1 -> *)
(*       \forall z \near t, \forall a \near (x + z * (u - x)) *)
(*                                & b \near (y + z * (v - y)), P a b. *)
(* Proof. *)
(* move=> P x y. *)
(* apply locally_2d_align => eps HP uv Huv t Ht. *)
(* set u := uv.1. set v := uv.2. *)
(* have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0. *)
(* rewrite ler_eqVlt in Zm. *)
(* case/orP : Zm => Zm. *)
(* - apply filterE => z. *)
(*   apply/locallyP. *)
(*   exists eps => // pq. *)
(*   rewrite !(RminusE,RmultE,RplusE). *)
(*   move: (Zm). *)
(*   have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm). *)
(*   rewrite ler_maxl => /andP[H1 H2] _. *)
(*   rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite !(mulr0,addr0); by apply HP. *)
(* - have : Num.max (`|u - x|) (`|v - y|) < eps. *)
(*     rewrite ltr_maxl; apply/andP; split. *)
(*     - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*     - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*   rewrite -subr_gt0 => /RltP H1. *)
(*   set d1 := mk{posnum R} _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mk{posnum R} _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [{posnum R} of d1 / 2] => //= pq Hpq. *)
(*   set p := pq.1. set q := pq.2. *)
(*   apply HP; split. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //. *)
(*     apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)). *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //. *)
(*     rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //. *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr orbT. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(* Qed. *)
(* Admitted. *)

(* TODO redo *)
(* Lemma locally_2d_1d (P : R -> R -> Prop) x y : *)
(*   locally_2d x y P -> *)
(*   locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P). *)
(* Proof. *)
(* move/locally_2d_1d_strong. *)
(* apply: locally_2d_impl. *)
(* apply locally_2d_forall => u v H t Ht. *)
(* specialize (H t Ht). *)
(* have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by []. *)
(* by apply: locally_singleton. *)
(* Qed. *)

(* TODO redo *)
(* Lemma locally_2d_ex_dec : *)
(*   forall P x y, *)
(*   (forall x y, P x y \/ ~P x y) -> *)
(*   locally_2d x y P -> *)
(*   {d : {posnum R} | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

Section bounded.
Variable K : numFieldType.
Definition bounded (V : normedModType K) (A : set V) :=
  \forall M \near +oo, A `<=` [set x | `|x| < M].
End bounded.

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  move=> p Ap; exists (ifloor `|p| + 1) => //.
  by rewrite rmorphD /= -floorE floorS_gtr.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite -subr_gt0 => ltpn.
  apply/locallyP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltr_subr_addr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_norm_add.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmaxr_real ?real0 //; split => //.
move=> x ltmaxx p /DcovA [n Dn /lt_trans]; apply; apply: le_lt_trans ltmaxx.
have {} : n \in enum_fset D by [].
rewrite enum_fsetE => /mapP[/= i iD ->]; exact/BigmaxBigminr.ler_bigmaxr.
Qed.

Lemma rV_compact (T : topologicalType) n (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (product_topologicalType _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (product_topologicalType _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC row_simpl.
  by rewrite predeqE => ?; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {f_D} f_D :
  locally (f : product_topologicalType _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite locallyE.
  set Pj := fun j Bj => neigh (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, neigh (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite locallyE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; split; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in 'I_n.+1];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    apply/asboolP; exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R^o]_n.+1) :
  bounded A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R^o]_n.+1 | (forall i, (v ord0 i) \in `[(- (M + 1)), (M + 1)])].
  apply: (@rV_compact [topologicalType of R^o] _ (fun _ => [set x | x \in `[(- (M + 1)), (M + 1)]])).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvltM i.
suff /ltW : `|v ord0 i : R^o| < M + 1 by rewrite ler_norml.
apply: le_lt_trans (normvltM _ _); last by rewrite ltr_addl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v ij.1 ij.2| | ij : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
rewrite [in X in _ <= X]/normr /= mx_normrE.
by apply/BigmaxBigminr.bigmaxr_gerP; right => /=; exists j.
Qed.

(** Open sets in [Rbar] *)

Section open_sets_in_Rbar.

Lemma ereal_locally'_le (R : numFieldType) (x : {ereal R}) :
  ereal_locally' x --> ereal_locally x.
Proof.
move: x => [x P [_/posnumP[e] HP] |x P|x P] //=.
by exists e%:num => // ???; apply: HP.
Qed.

Lemma ereal_locally'_le_finite (R : numFieldType) (x : R) :
  ereal_locally' x%:E --> locally x%:E.
Proof.
by move=> P [_/posnumP[e] HP] //=; exists e%:num => // ???; apply: HP.
Qed.

Variable R : realFieldType (* TODO: generalize to numFieldType? *).

Lemma open_ereal_lt (y : {ereal R}) : open [set u : R^o | u%:E < y]%E.
Proof.
case: y => [y||] /=; first exact: open_lt.
rewrite [X in open X](_ : _ = setT); first exact: openT.
by rewrite funeqE => ?; rewrite trueE.
rewrite [X in open X](_ : _ = set0); first exact: open0.
by rewrite funeqE => ?; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set u : R^o | y < u%:E]%E.
Proof.
case: y => [y||] /=; first exact: open_gt.
rewrite [X in open X](_ : _ = set0); first exact: open0.
by rewrite funeqE => ?; rewrite falseE.
rewrite [X in open X](_ : _ = setT); first exact: openT.
by rewrite funeqE => ?; rewrite trueE.
Qed.

Lemma open_ereal_lt' (x y : {ereal R}) : (x < y)%E ->
  ereal_locally x (fun u => u < y)%E.
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
case: y => [y||//] /= in xy *.
exists y; rewrite num_real; split => //= x ? //.
by exists 0.
case: y => [y||//] /= in xy *.
exists y; rewrite num_real; split => //= x ? //.
by exists 0; rewrite real0; split => // x /lt_le_trans; apply.
Qed.

Lemma open_ereal_gt' (x y : {ereal R}) : (y < x)%E ->
  ereal_locally x (fun u => y < u)%E.
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0; rewrite real0.
by exists y; rewrite num_real.
by move=> _; exists 0; rewrite real0; split => // x; apply/le_lt_trans.
Qed.

End open_sets_in_Rbar.

(** * Some limits on real functions *)

Definition ereal_loc_seq (R : numDomainType) (x : {ereal R}) (n : nat) :=
  match x with
    | x%:E => (x + (n%:R + 1)^-1)%:E
    | +oo%E => n%:R%:E
    | -oo%E => (- n%:R%:E)%E
  end.

Lemma cvg_ereal_loc_seq (R : realType) (x : {ereal R}) :
  ereal_loc_seq x --> ereal_locally' x.
Proof.
move=> P; rewrite /ereal_loc_seq.
case: x => /= [x [_/posnumP[d] Hp] |[d [dreal Hp]] |[d [dreal Hp]]]; last 2 first.
    have /ZnatP [N Nfloor] : ifloor (maxr d 0) \is a Znat.
      by rewrite Znat_def ifloor_ge0 lexU lexx orbC.
    exists N.+1 => // n ltNn; apply: Hp.
    have /le_lt_trans : d <= maxr d 0 by rewrite lexU lexx.
    apply; apply: lt_le_trans (floorS_gtr _) _; rewrite floorE Nfloor.
    by rewrite -(@natrD R N 1) ler_nat addn1.
  have /ZnatP [N Nfloor] : ifloor (maxr (- d) 0) \is a Znat.
    by rewrite Znat_def ifloor_ge0 lexU lexx orbC.
  exists N.+1 => // n ltNn; apply: Hp; rewrite lte_fin ltr_oppl.
  have /le_lt_trans : - d <= maxr (- d) 0 by rewrite lexU lexx.
  apply; apply: lt_le_trans (floorS_gtr _) _; rewrite floorE Nfloor.
  by rewrite -(@natrD R N 1) ler_nat addn1.
have /ZnatP [N Nfloor] : ifloor (d%:num^-1) \is a Znat.
  by rewrite Znat_def ifloor_ge0.
exists N => // n leNn; have gt0Sn : (0 < n%:R + 1 :> R).
  apply: ltr_spaddr => //; exact/ler0n.
apply: Hp; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym; apply/invr_neq0/lt0r_neq0.
rewrite /= opprD addrA subrr distrC subr0.
rewrite gtr0_norm; last by rewrite invr_gt0.
rewrite -[X in X < _]mulr1 ltr_pdivr_mull // -ltr_pdivr_mulr // div1r.
apply: lt_le_trans (floorS_gtr _) _; rewrite floorE Nfloor ler_add //.
by rewrite ler_nat.
Qed.

(* TODO: express using ball?*)
Lemma continuity_pt_locally (f : Rdefinitions.R -> Rdefinitions.R) x :
  Ranalysis1.continuity_pt f x <->
  forall eps : {posnum Rdefinitions.R}, locally x (fun u => `|f u - f x| < eps%:num).
Proof.
split=> [fcont e|fcont _/RltP/posnumP[e]]; last first.
  have [_/posnumP[d] xd_fxe] := fcont e.
  exists d%:num; split; first by apply/RltP; have := [gt0 of d%:num].
  by move=> y [_ /RltP yxd]; apply/RltP/xd_fxe; rewrite /= distrC.
have /RltP egt0 := [gt0 of e%:num].
have [_ [/RltP/posnumP[d] dx_fxe]] := fcont e%:num egt0.
exists d%:num => // y xyd; case: (eqVneq x y) => [->|xney].
  by rewrite subrr normr0.
apply/RltP/dx_fxe; split; first by split=> //; apply/eqP.
by have /RltP := xyd; rewrite distrC.
Qed.

Lemma continuity_pt_cvg (f : Rdefinitions.R -> Rdefinitions.R) (x : Rdefinitions.R) :
  Ranalysis1.continuity_pt f x <-> {for x, continuous f}.
Proof.
eapply iff_trans; first exact: continuity_pt_locally.
apply iff_sym.
have FF : Filter (f @ x).
  by typeclasses eauto.
  (*by apply fmap_filter; apply: @filter_filter' (locally_filter _).*)
case: (@cvg_ballP _ _ (f @ x) FF (f x)) => {FF}H1 H2.
(* TODO: in need for lemmas and/or refactoring of already existing lemmas (ball vs. Rabs) *)
split => [{H2} - /H1 {H1} H1 eps|{H1} H].
- have {H1} [//|_/posnumP[x0] Hx0] := H1 eps%:num.
  exists x0%:num => // Hx0' /Hx0 /=.
  by rewrite /= distrC; apply.
- apply H2 => _ /posnumP[eps]; move: (H eps) => {H} [_ /posnumP[x0] Hx0].
  exists x0%:num => // y /Hx0 /= {Hx0}Hx0.
  by rewrite /ball /= distrC.
Qed.

Lemma continuity_ptE (f : Rdefinitions.R -> Rdefinitions.R) (x : Rdefinitions.R) :
  Ranalysis1.continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_cvg. Qed.

Lemma continuous_withinNx (R : numFieldType) {U V : pseudoMetricType R}
  (f : U -> V) x :
  {for x, continuous f} <-> f @ locally' x --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /locally' !near_simpl near_withinE.
  by rewrite /locally'; apply: cvg_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not inferred *)
rewrite !locally_nearE !near_map !near_locally in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: locally_singleton|near: y].
Grab Existential Variables. all: end_near. Qed.

Lemma continuity_pt_cvg' f x :
  Ranalysis1.continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx. Qed.

Lemma continuity_pt_locally' f x :
  Ranalysis1.continuity_pt f x <->
  forall eps, 0 < eps -> locally' x (fun u => `|f x - f u| < eps).
Proof.
rewrite continuity_pt_cvg' (@cvg_normP _ [normedModType _ of Rdefinitions.R^o]).
exact.
Qed.

Lemma locally_pt_comp (P : Rdefinitions.R -> Prop)
  (f : Rdefinitions.R -> Rdefinitions.R) (x : Rdefinitions.R) :
  locally (f x) P -> Ranalysis1.continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_cvg; apply. Qed.
