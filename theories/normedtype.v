(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
Require Import boolp ereal reals.
Require Import classical_sets posnum nngnum topology prodnormedzmodule.


(******************************************************************************)
(* This file extends the topological hierarchy with norm-related notions.     *)
(*                                                                            *)
(* Note that balls in topology.v are not necessarily open, here they are.     *)
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
(*                      nbhs_norm == neighborhoods defined by the norm.       *)
(*                    closed_ball == closure of a ball.                       *)
(*                                                                            *)
(* * Domination notations:                                                    *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*                  bounded_near f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets.                  *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of functions bounded on their     *)
(*                                      whole domain.                         *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                                                                            *)
(*                     is_interval E == the set E is an interval              *)
(*                           Rhull E == the real interval hull of a set       *)
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
(*                                   s.t. nbhs holds on the left/right of x   *)
(*                                                                            *)
(* --> We used these definitions to prove the intermediate value theorem and  *)
(*     the Heine-Borel theorem, which states that the compact sets of R^n are *)
(*     the closed and bounded sets.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition pointed_of_zmodule (R : zmodType) : pointedType := PointedType R 0.

Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R := Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|)))).

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
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|)))
  := PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.

Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ normr) = nbhs_ (entourage_ (ball_ normr)).
Proof.
rewrite /nbhs_ entourage_E predeq2E => x A; split.
  move=> [e egt0 sbeA].
  by exists [set xy | ball_ normr xy.1 e xy.2] => //; exists e.
by move=> [E [e egt0 sbeE] sEA]; exists e => // ??; apply/sEA/sbeE.
Qed.
End pseudoMetric_of_normedDomain.

Lemma nbhsN (R : numFieldType) (x : R) :
  nbhs (- x) = [set [set - y | y in A] | A in nbhs x].
Proof.
rewrite -!filter_from_ballE predeqE => A.
split=> [[e egt0 oppxe_A]|[B [e egt0 xe_B] <-]]; last first.
  exists e => // y xe_y; exists (- y); last by rewrite opprK.
  by apply/xe_B; rewrite /ball /= opprK -normrN opprD.
exists [set - y | y in A]; last first.
  rewrite predeqE => y; split=> [[z [t At <- <-]]|Ay]; first by rewrite opprK.
  by exists (- y); [exists y|rewrite opprK].
exists e => // y xe_y; exists (- y); last by rewrite opprK.
by apply/oppxe_A; rewrite /ball /= distrC opprK addrC.
Qed.

Lemma openN (R : numFieldType) (A : set R) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior nbhsN; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK nbhsN; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

Module PseudoMetricNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (ent : set (set (T * T)))
    (m : PseudoMetric.mixin_of R ent) := Mixin {
  _ : PseudoMetric.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  nbhs_mixin : Filtered.nbhs_of T T ;
  topological_mixin : @Topological.mixin_of T nbhs_mixin ;
  uniform_mixin : @Uniform.mixin_of T nbhs_mixin ;
  pseudoMetric_mixin :
    @PseudoMetric.mixin_of R T (Uniform.entourage uniform_mixin) ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ pseudoMetric_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.
Definition base2 T c := @PseudoMetric.Class _ _
    (@Uniform.Class _
      (@Topological.Class _
        (Filtered.Class
         (Pointed.Class (@base T c) (pointed_mixin c))
         (nbhs_mixin c))
        (topological_mixin c))
      (uniform_mixin c))
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
  @Pack phR T (@Class T b u u u u u m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack xT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition uniform_zmodType := @GRing.Zmodule.Pack uniformType xclass.
Definition pseudoMetric_zmodType := @GRing.Zmodule.Pack pseudoMetricType xclass.
Definition pointed_normedZmodType := @Num.NormedZmodule.Pack R phR pointedType xclass.
Definition filtered_normedZmodType := @Num.NormedZmodule.Pack R phR filteredType xclass.
Definition topological_normedZmodType := @Num.NormedZmodule.Pack R phR topologicalType xclass.
Definition uniform_normedZmodType := @Num.NormedZmodule.Pack R phR uniformType xclass.
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
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical uniform_zmodType.
Canonical pseudoMetric_zmodType.
Canonical pointed_normedZmodType.
Canonical filtered_normedZmodType.
Canonical topological_normedZmodType.
Canonical uniform_normedZmodType.
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
Proof. by case: V => ? [? ? ? ? ? ? []]. Qed.

End pseudoMetricnormedzmodule_lemmas.

(** locally *)

Section Nbhs'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallNE notK => exNP.
pose D := [set d : R^o | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/nbhs_ballP; exists e%:num. Qed.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /nbhs_ballP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /nbhs_ballP xP.
pose D := [set d : R^o | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End Nbhs'.

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
  by rewrite in_itv /= ler_subl_addr !ler_paddr // (itvP xyz).
by rewrite in_itv /= ; apply/andP; split; apply/ler_addgt0Pr => ? /xyz_e;
  rewrite in_itv /= ler_subl_addr => /andP [].
Qed.

Lemma in_segment_addgt0Pl (R : numFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Proof.
move=> /= M s /= /(nbhs_ballP (M i j)) [e e0 es].
apply/nbhs_ballP; exists e => //= N MN; exact/es/MN.
Qed.

Global Instance Proper_nbhs'_numFieldType (R : numFieldType) (x : R) :
  ProperFilter (nbhs' x).
Proof.
apply: Build_ProperFilter => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
Qed.

Global Instance Proper_nbhs'_realType (R : realType) (x : R) :
  ProperFilter (nbhs' x).
Proof. exact: Proper_nbhs'_numFieldType. Qed.

(** * Some Topology on [Rbar] *)

Definition pinfty_nbhs (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R].

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Proof.
apply Build_ProperFilter.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0; rewrite real0.
- exists (Num.max MP MQ); split=> [|x]; first exact: max_real.
  by rewrite comparable_lt_maxl ?real_comparable // => /andP[/gtMP ? /gtMQ].
- by exists M; split => // ? /gtM /sPQ.
Qed.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Proof.
apply Build_ProperFilter.
  move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtr_addl oppr_lt0.
split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
- by exists 0; rewrite real0.
- exists (Num.min MP MQ); split=> [|x]; first exact: min_real.
  by rewrite comparable_lt_minr ?real_comparable // => /andP[/ltMP ? /ltMQ].
- by exists M; split => // x /ltM /sPQ.
Qed.

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
    rewrite pos_lt_maxl /= => /andP[MPx MQx]; split.
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
      rewrite ltr_oppr pos_lt_maxl => /andP[].
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

Lemma nbhs_pinfty_gt (c : {posnum R}) : \forall x \near +oo, c%:num < x.
Proof. by exists c%:num; split => // ; rewrite realE posnum_ge0. Qed.

Lemma nbhs_pinfty_ge (c : {posnum R}) : \forall x \near +oo, c%:num <= x.
Proof. by exists c%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

Lemma nbhs_pinfty_gt_real (c : R) : c \is Num.real ->
  \forall x \near +oo, c < x.
Proof. by exists c. Qed.

Lemma nbhs_pinfty_ge_real (c : R) : c \is Num.real ->
  \forall x \near +oo, c <= x.
Proof. by exists c; split => //; apply: ltW. Qed.

Lemma nbhs_minfty_lt (c : {posnum R}) : \forall x \near -oo, c%:num > x.
Proof. by exists c%:num; split => // ; rewrite realE posnum_ge0. Qed.

Lemma nbhs_minfty_le (c : {posnum R}) : \forall x \near -oo, c%:num >= x.
Proof.
by exists c%:num; rewrite realE posnum_ge0 /=; split => // x; apply: ltW.
Qed.

Lemma nbhs_minfty_lt_real (c : R) : c \is Num.real ->
  \forall x \near -oo, c > x.
Proof. by exists c. Qed.

Lemma nbhs_minfty_le_real (c : R) : c \is Num.real ->
  \forall x \near -oo, c >= x.
Proof. by exists c; split => // ?; apply: ltW. Qed.

End infty_nbhs_instances.

Hint Extern 0 (is_true (0 < _)) => match goal with
  H : ?x \is_near (nbhs +oo) |- _ =>
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
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType := @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition uniform_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass.
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
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Canonical pointed_lmodType.
Canonical filtered_lmodType.
Canonical topological_lmodType.
Canonical uniform_lmodType.
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

Module regular_topology.

Section regular_topology.
Local Canonical pseudoMetricNormedZmodType (R : numFieldType) :=
  @PseudoMetricNormedZmodType
    R R^o
    (PseudoMetricNormedZmodule.Mixin (erefl : @ball _ R = ball_ Num.norm)).
Local Canonical normedModType (R : numFieldType) :=
  NormedModType R R^o (@NormedModMixin _ _ ( *:%R : R -> R^o -> _) (@normrM _)).
End regular_topology.

Module Exports.
Canonical pseudoMetricNormedZmodType.
Canonical normedModType.
End Exports.

End regular_topology.
Export regular_topology.Exports.

Module numFieldNormedType.

Section realType.
Variable (R : realType).
Local Canonical real_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical real_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical real_algType := [algType R of R for [algType R of R^o]].
Local Canonical real_comAlgType := [comAlgType R of R].
Local Canonical real_unitAlgType := [unitAlgType R of R].
Local Canonical real_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical real_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical real_FalgType := [FalgType R of R].
Local Canonical real_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical real_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical real_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End realType.

Section rcfType.
Variable (R : rcfType).
Local Canonical rcf_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical rcf_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical rcf_algType := [algType R of R for [algType R of R^o]].
Local Canonical rcf_comAlgType := [comAlgType R of R].
Local Canonical rcf_unitAlgType := [unitAlgType R of R].
Local Canonical rcf_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical rcf_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical rcf_FalgType := [FalgType R of R].
Local Canonical rcf_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical rcf_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical rcf_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
Local Canonical archiField_lmodType :=
  [lmodType R of R for [lmodType R of R^o]].
Local Canonical archiField_lalgType :=
  [lalgType R of R for [lalgType R of R^o]].
Local Canonical archiField_algType := [algType R of R for [algType R of R^o]].
Local Canonical archiField_comAlgType := [comAlgType R of R].
Local Canonical archiField_unitAlgType := [unitAlgType R of R].
Local Canonical archiField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical archiField_vectType :=
  [vectType R of R for [vectType R of R^o]].
Local Canonical archiField_FalgType := [FalgType R of R].
Local Canonical archiField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical archiField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical archiField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
Local Canonical realField_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical realField_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical realField_algType := [algType R of R for [algType R of R^o]].
Local Canonical realField_comAlgType := [comAlgType R of R].
Local Canonical realField_unitAlgType := [unitAlgType R of R].
Local Canonical realField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical realField_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical realField_FalgType := [FalgType R of R].
Local Canonical realField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical realField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical realField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_latticeType := [latticeType of realField_lmodType].
Definition lmod_distrLatticeType := [distrLatticeType of realField_lmodType].
Definition lmod_orderType := [orderType of realField_lmodType].
Definition lmod_realDomainType := [realDomainType of realField_lmodType].
Definition lalg_latticeType := [latticeType of realField_lalgType].
Definition lalg_distrLatticeType := [distrLatticeType of realField_lalgType].
Definition lalg_orderType := [orderType of realField_lalgType].
Definition lalg_realDomainType := [realDomainType of realField_lalgType].
Definition alg_latticeType := [latticeType of realField_algType].
Definition alg_distrLatticeType := [distrLatticeType of realField_algType].
Definition alg_orderType := [orderType of realField_algType].
Definition alg_realDomainType := [realDomainType of realField_algType].
Definition comAlg_latticeType := [latticeType of realField_comAlgType].
Definition comAlg_distrLatticeType :=
  [distrLatticeType of realField_comAlgType].
Definition comAlg_orderType := [orderType of realField_comAlgType].
Definition comAlg_realDomainType := [realDomainType of realField_comAlgType].
Definition unitAlg_latticeType := [latticeType of realField_unitAlgType].
Definition unitAlg_distrLatticeType :=
  [distrLatticeType of realField_unitAlgType].
Definition unitAlg_orderType := [orderType of realField_unitAlgType].
Definition unitAlg_realDomainType := [realDomainType of realField_unitAlgType].
Definition comUnitAlg_latticeType := [latticeType of realField_comUnitAlgType].
Definition comUnitAlg_distrLatticeType :=
  [distrLatticeType of realField_comUnitAlgType].
Definition comUnitAlg_orderType := [orderType of realField_comUnitAlgType].
Definition comUnitAlg_realDomainType :=
  [realDomainType of realField_comUnitAlgType].
Definition vect_latticeType := [latticeType of realField_vectType].
Definition vect_distrLatticeType := [distrLatticeType of realField_vectType].
Definition vect_orderType := [orderType of realField_vectType].
Definition vect_realDomainType := [realDomainType of realField_vectType].
Definition Falg_latticeType := [latticeType of realField_FalgType].
Definition Falg_distrLatticeType := [distrLatticeType of realField_FalgType].
Definition Falg_orderType := [orderType of realField_FalgType].
Definition Falg_realDomainType := [realDomainType of realField_FalgType].
Definition fieldExt_latticeType := [latticeType of realField_fieldExtType].
Definition fieldExt_distrLatticeType :=
  [distrLatticeType of realField_fieldExtType].
Definition fieldExt_orderType := [orderType of realField_fieldExtType].
Definition fieldExt_realDomainType :=
  [realDomainType of realField_fieldExtType].
Definition pseudoMetricNormedZmod_latticeType :=
  [latticeType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_distrLatticeType :=
  [distrLatticeType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_orderType :=
  [orderType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_realDomainType :=
  [realDomainType of realField_pseudoMetricNormedZmodType].
Definition normedMod_latticeType := [latticeType of realField_normedModType].
Definition normedMod_distrLatticeType :=
  [distrLatticeType of realField_normedModType].
Definition normedMod_orderType := [orderType of realField_normedModType].
Definition normedMod_realDomainType :=
  [realDomainType of realField_normedModType].
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
Local Canonical numClosedField_lmodType :=
  [lmodType R of R for [lmodType R of R^o]].
Local Canonical numClosedField_lalgType :=
  [lalgType R of R for [lalgType R of R^o]].
Local Canonical numClosedField_algType :=
  [algType R of R for [algType R of R^o]].
Local Canonical numClosedField_comAlgType := [comAlgType R of R].
Local Canonical numClosedField_unitAlgType := [unitAlgType R of R].
Local Canonical numClosedField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical numClosedField_vectType :=
  [vectType R of R for [vectType R of R^o]].
Local Canonical numClosedField_FalgType := [FalgType R of R].
Local Canonical numClosedField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical numClosedField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical numClosedField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_decFieldType := [decFieldType of numClosedField_lmodType].
Definition lmod_closedFieldType := [closedFieldType of numClosedField_lmodType].
Definition lalg_decFieldType := [decFieldType of numClosedField_lalgType].
Definition lalg_closedFieldType := [closedFieldType of numClosedField_lalgType].
Definition alg_decFieldType := [decFieldType of numClosedField_algType].
Definition alg_closedFieldType := [closedFieldType of numClosedField_algType].
Definition comAlg_decFieldType := [decFieldType of numClosedField_comAlgType].
Definition comAlg_closedFieldType :=
  [closedFieldType of numClosedField_comAlgType].
Definition unitAlg_decFieldType := [decFieldType of numClosedField_unitAlgType].
Definition unitAlg_closedFieldType :=
  [closedFieldType of numClosedField_unitAlgType].
Definition comUnitAlg_decFieldType :=
  [decFieldType of numClosedField_comUnitAlgType].
Definition comUnitAlg_closedFieldType :=
  [closedFieldType of numClosedField_comUnitAlgType].
Definition vect_decFieldType := [decFieldType of numClosedField_vectType].
Definition vect_closedFieldType := [closedFieldType of numClosedField_vectType].
Definition Falg_decFieldType := [decFieldType of numClosedField_FalgType].
Definition Falg_closedFieldType := [closedFieldType of numClosedField_FalgType].
Definition fieldExt_decFieldType :=
  [decFieldType of numClosedField_fieldExtType].
Definition fieldExt_closedFieldType :=
  [closedFieldType of numClosedField_fieldExtType].
Definition pseudoMetricNormedZmod_decFieldType :=
  [decFieldType of numClosedField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_closedFieldType :=
  [closedFieldType of numClosedField_pseudoMetricNormedZmodType].
Definition normedMod_decFieldType :=
  [decFieldType of numClosedField_normedModType].
Definition normedMod_closedFieldType :=
  [closedFieldType of numClosedField_normedModType].
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical numField_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical numField_algType := [algType R of R for [algType R of R^o]].
Local Canonical numField_comAlgType := [comAlgType R of R].
Local Canonical numField_unitAlgType := [unitAlgType R of R].
Local Canonical numField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical numField_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical numField_FalgType := [FalgType R of R].
Local Canonical numField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical numField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical numField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_porderType := [porderType of numField_lmodType].
Definition lmod_numDomainType := [numDomainType of numField_lmodType].
Definition lalg_pointedType := [pointedType of numField_lalgType].
Definition lalg_filteredType := [filteredType R of numField_lalgType].
Definition lalg_topologicalType := [topologicalType of numField_lalgType].
Definition lalg_uniformType := [uniformType of numField_lalgType].
Definition lalg_pseudoMetricType := [pseudoMetricType R of numField_lalgType].
Definition lalg_normedZmodType := [normedZmodType R of numField_lalgType].
Definition lalg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_lalgType].
Definition lalg_normedModType := [normedModType R of numField_lalgType].
Definition lalg_porderType := [porderType of numField_lalgType].
Definition lalg_numDomainType := [numDomainType of numField_lalgType].
Definition alg_pointedType := [pointedType of numField_algType].
Definition alg_filteredType := [filteredType R of numField_algType].
Definition alg_topologicalType := [topologicalType of numField_algType].
Definition alg_uniformType := [uniformType of numField_algType].
Definition alg_pseudoMetricType := [pseudoMetricType R of numField_algType].
Definition alg_normedZmodType := [normedZmodType R of numField_algType].
Definition alg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_algType].
Definition alg_normedModType := [normedModType R of numField_algType].
Definition alg_porderType := [porderType of numField_algType].
Definition alg_numDomainType := [numDomainType of numField_algType].
Definition comAlg_pointedType := [pointedType of numField_comAlgType].
Definition comAlg_filteredType := [filteredType R of numField_comAlgType].
Definition comAlg_topologicalType := [topologicalType of numField_comAlgType].
Definition comAlg_uniformType := [uniformType of numField_comAlgType].
Definition comAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_comAlgType].
Definition comAlg_normedZmodType := [normedZmodType R of numField_comAlgType].
Definition comAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_comAlgType].
Definition comAlg_normedModType := [normedModType R of numField_comAlgType].
Definition comAlg_porderType := [porderType of numField_comAlgType].
Definition comAlg_numDomainType := [numDomainType of numField_comAlgType].
Definition unitAlg_pointedType := [pointedType of numField_unitAlgType].
Definition unitAlg_filteredType := [filteredType R of numField_unitAlgType].
Definition unitAlg_topologicalType := [topologicalType of numField_unitAlgType].
Definition unitAlg_uniformType := [uniformType of numField_unitAlgType].
Definition unitAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_unitAlgType].
Definition unitAlg_normedZmodType := [normedZmodType R of numField_unitAlgType].
Definition unitAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_unitAlgType].
Definition unitAlg_normedModType := [normedModType R of numField_unitAlgType].
Definition unitAlg_porderType := [porderType of numField_unitAlgType].
Definition unitAlg_numDomainType := [numDomainType of numField_unitAlgType].
Definition comUnitAlg_pointedType := [pointedType of numField_comUnitAlgType].
Definition comUnitAlg_filteredType :=
  [filteredType R of numField_comUnitAlgType].
Definition comUnitAlg_topologicalType :=
  [topologicalType of numField_comUnitAlgType].
Definition comUnitAlg_uniformType := [uniformType of numField_comUnitAlgType].
Definition comUnitAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_comUnitAlgType].
Definition comUnitAlg_normedZmodType :=
  [normedZmodType R of numField_comUnitAlgType].
Definition comUnitAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_comUnitAlgType].
Definition comUnitAlg_normedModType :=
  [normedModType R of numField_comUnitAlgType].
Definition comUnitAlg_porderType := [porderType of numField_comUnitAlgType].
Definition comUnitAlg_numDomainType :=
  [numDomainType of numField_comUnitAlgType].
Definition vect_pointedType := [pointedType of numField_vectType].
Definition vect_filteredType := [filteredType R of numField_vectType].
Definition vect_topologicalType := [topologicalType of numField_vectType].
Definition vect_uniformType := [uniformType of numField_vectType].
Definition vect_pseudoMetricType := [pseudoMetricType R of numField_vectType].
Definition vect_normedZmodType := [normedZmodType R of numField_vectType].
Definition vect_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_vectType].
Definition vect_normedModType := [normedModType R of numField_vectType].
Definition vect_porderType := [porderType of numField_vectType].
Definition vect_numDomainType := [numDomainType of numField_vectType].
Definition Falg_pointedType := [pointedType of numField_FalgType].
Definition Falg_filteredType := [filteredType R of numField_FalgType].
Definition Falg_topologicalType := [topologicalType of numField_FalgType].
Definition Falg_uniformType := [uniformType of numField_FalgType].
Definition Falg_pseudoMetricType := [pseudoMetricType R of numField_FalgType].
Definition Falg_normedZmodType := [normedZmodType R of numField_FalgType].
Definition Falg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_FalgType].
Definition Falg_normedModType := [normedModType R of numField_FalgType].
Definition Falg_porderType := [porderType of numField_FalgType].
Definition Falg_numDomainType := [numDomainType of numField_FalgType].
Definition fieldExt_pointedType := [pointedType of numField_fieldExtType].
Definition fieldExt_filteredType := [filteredType R of numField_fieldExtType].
Definition fieldExt_topologicalType :=
  [topologicalType of numField_fieldExtType].
Definition fieldExt_uniformType := [uniformType of numField_fieldExtType].
Definition fieldExt_pseudoMetricType :=
  [pseudoMetricType R of numField_fieldExtType].
Definition fieldExt_normedZmodType :=
  [normedZmodType R of numField_fieldExtType].
Definition fieldExt_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_fieldExtType].
Definition fieldExt_normedModType := [normedModType R of numField_fieldExtType].
Definition fieldExt_porderType := [porderType of numField_fieldExtType].
Definition fieldExt_numDomainType := [numDomainType of numField_fieldExtType].
Definition pseudoMetricNormedZmod_ringType :=
  [ringType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_comRingType :=
  [comRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_unitRingType :=
  [unitRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_comUnitRingType :=
  [comUnitRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_idomainType :=
  [idomainType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_fieldType :=
  [fieldType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_porderType :=
  [porderType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_numDomainType :=
  [numDomainType of numField_pseudoMetricNormedZmodType].
Definition normedMod_ringType := [ringType of numField_normedModType].
Definition normedMod_comRingType := [comRingType of numField_normedModType].
Definition normedMod_unitRingType := [unitRingType of numField_normedModType].
Definition normedMod_comUnitRingType :=
  [comUnitRingType of numField_normedModType].
Definition normedMod_idomainType := [idomainType of numField_normedModType].
Definition normedMod_fieldType := [fieldType of numField_normedModType].
Definition normedMod_porderType := [porderType of numField_normedModType].
Definition normedMod_numDomainType := [numDomainType of numField_normedModType].
End numFieldType.

Module Exports.
Export topology.numFieldTopology.Exports.
(* realType *)
Canonical real_lmodType.
Canonical real_lalgType.
Canonical real_algType.
Canonical real_comAlgType.
Canonical real_unitAlgType.
Canonical real_comUnitAlgType.
Canonical real_vectType.
Canonical real_FalgType.
Canonical real_fieldExtType.
Canonical real_pseudoMetricNormedZmodType.
Canonical real_normedModType.
Coercion real_lmodType : realType >-> lmodType.
Coercion real_lalgType : realType >-> lalgType.
Coercion real_algType : realType >-> algType.
Coercion real_comAlgType : realType >-> comAlgType.
Coercion real_unitAlgType : realType >-> unitAlgType.
Coercion real_comUnitAlgType : realType >-> comUnitAlgType.
Coercion real_vectType : realType >-> vectType.
Coercion real_FalgType : realType >-> FalgType.
Coercion real_fieldExtType : realType >-> fieldExtType.
Coercion real_pseudoMetricNormedZmodType :
  realType >-> pseudoMetricNormedZmodType.
Coercion real_normedModType : realType >-> normedModType.
(* rcfType *)
Canonical rcf_lmodType.
Canonical rcf_lalgType.
Canonical rcf_algType.
Canonical rcf_comAlgType.
Canonical rcf_unitAlgType.
Canonical rcf_comUnitAlgType.
Canonical rcf_vectType.
Canonical rcf_FalgType.
Canonical rcf_fieldExtType.
Canonical rcf_pseudoMetricNormedZmodType.
Canonical rcf_normedModType.
Coercion rcf_lmodType : rcfType >-> lmodType.
Coercion rcf_lalgType : rcfType >-> lalgType.
Coercion rcf_algType : rcfType >-> algType.
Coercion rcf_comAlgType : rcfType >-> comAlgType.
Coercion rcf_unitAlgType : rcfType >-> unitAlgType.
Coercion rcf_comUnitAlgType : rcfType >-> comUnitAlgType.
Coercion rcf_vectType : rcfType >-> vectType.
Coercion rcf_FalgType : rcfType >-> FalgType.
Coercion rcf_fieldExtType : rcfType >-> fieldExtType.
Coercion rcf_pseudoMetricNormedZmodType :
  rcfType >-> pseudoMetricNormedZmodType.
Coercion rcf_normedModType : rcfType >-> normedModType.
(* archiFieldType *)
Canonical archiField_lmodType.
Canonical archiField_lalgType.
Canonical archiField_algType.
Canonical archiField_comAlgType.
Canonical archiField_unitAlgType.
Canonical archiField_comUnitAlgType.
Canonical archiField_vectType.
Canonical archiField_FalgType.
Canonical archiField_fieldExtType.
Canonical archiField_pseudoMetricNormedZmodType.
Canonical archiField_normedModType.
Coercion archiField_lmodType : archiFieldType >-> lmodType.
Coercion archiField_lalgType : archiFieldType >-> lalgType.
Coercion archiField_algType : archiFieldType >-> algType.
Coercion archiField_comAlgType : archiFieldType >-> comAlgType.
Coercion archiField_unitAlgType : archiFieldType >-> unitAlgType.
Coercion archiField_comUnitAlgType : archiFieldType >-> comUnitAlgType.
Coercion archiField_vectType : archiFieldType >-> vectType.
Coercion archiField_FalgType : archiFieldType >-> FalgType.
Coercion archiField_fieldExtType : archiFieldType >-> fieldExtType.
Coercion archiField_pseudoMetricNormedZmodType :
  archiFieldType >-> pseudoMetricNormedZmodType.
Coercion archiField_normedModType : archiFieldType >-> normedModType.
(* realFieldType *)
Canonical realField_lmodType.
Canonical realField_lalgType.
Canonical realField_algType.
Canonical realField_comAlgType.
Canonical realField_unitAlgType.
Canonical realField_comUnitAlgType.
Canonical realField_vectType.
Canonical realField_FalgType.
Canonical realField_fieldExtType.
Canonical realField_pseudoMetricNormedZmodType.
Canonical realField_normedModType.
Canonical lmod_latticeType.
Canonical lmod_distrLatticeType.
Canonical lmod_orderType.
Canonical lmod_realDomainType.
Canonical lalg_latticeType.
Canonical lalg_distrLatticeType.
Canonical lalg_orderType.
Canonical lalg_realDomainType.
Canonical alg_latticeType.
Canonical alg_distrLatticeType.
Canonical alg_orderType.
Canonical alg_realDomainType.
Canonical comAlg_latticeType.
Canonical comAlg_distrLatticeType.
Canonical comAlg_orderType.
Canonical comAlg_realDomainType.
Canonical unitAlg_latticeType.
Canonical unitAlg_distrLatticeType.
Canonical unitAlg_orderType.
Canonical unitAlg_realDomainType.
Canonical comUnitAlg_latticeType.
Canonical comUnitAlg_distrLatticeType.
Canonical comUnitAlg_orderType.
Canonical comUnitAlg_realDomainType.
Canonical vect_latticeType.
Canonical vect_distrLatticeType.
Canonical vect_orderType.
Canonical vect_realDomainType.
Canonical Falg_latticeType.
Canonical Falg_distrLatticeType.
Canonical Falg_orderType.
Canonical Falg_realDomainType.
Canonical fieldExt_latticeType.
Canonical fieldExt_distrLatticeType.
Canonical fieldExt_orderType.
Canonical fieldExt_realDomainType.
Canonical pseudoMetricNormedZmod_latticeType.
Canonical pseudoMetricNormedZmod_distrLatticeType.
Canonical pseudoMetricNormedZmod_orderType.
Canonical pseudoMetricNormedZmod_realDomainType.
Canonical normedMod_latticeType.
Canonical normedMod_distrLatticeType.
Canonical normedMod_orderType.
Canonical normedMod_realDomainType.
Coercion realField_lmodType : realFieldType >-> lmodType.
Coercion realField_lalgType : realFieldType >-> lalgType.
Coercion realField_algType : realFieldType >-> algType.
Coercion realField_comAlgType : realFieldType >-> comAlgType.
Coercion realField_unitAlgType : realFieldType >-> unitAlgType.
Coercion realField_comUnitAlgType : realFieldType >-> comUnitAlgType.
Coercion realField_vectType : realFieldType >-> vectType.
Coercion realField_FalgType : realFieldType >-> FalgType.
Coercion realField_fieldExtType : realFieldType >-> fieldExtType.
Coercion realField_pseudoMetricNormedZmodType :
  Num.RealField.type >-> PseudoMetricNormedZmodule.type.
Coercion realField_normedModType : Num.RealField.type >-> NormedModule.type.
(* numClosedFieldType *)
Canonical numClosedField_lmodType.
Canonical numClosedField_lalgType.
Canonical numClosedField_algType.
Canonical numClosedField_comAlgType.
Canonical numClosedField_unitAlgType.
Canonical numClosedField_comUnitAlgType.
Canonical numClosedField_vectType.
Canonical numClosedField_FalgType.
Canonical numClosedField_fieldExtType.
Canonical numClosedField_pseudoMetricNormedZmodType.
Canonical numClosedField_normedModType.
Canonical lmod_decFieldType.
Canonical lmod_closedFieldType.
Canonical lalg_decFieldType.
Canonical lalg_closedFieldType.
Canonical alg_decFieldType.
Canonical alg_closedFieldType.
Canonical comAlg_decFieldType.
Canonical comAlg_closedFieldType.
Canonical unitAlg_decFieldType.
Canonical unitAlg_closedFieldType.
Canonical comUnitAlg_decFieldType.
Canonical comUnitAlg_closedFieldType.
Canonical vect_decFieldType.
Canonical vect_closedFieldType.
Canonical Falg_decFieldType.
Canonical Falg_closedFieldType.
Canonical fieldExt_decFieldType.
Canonical fieldExt_closedFieldType.
Canonical pseudoMetricNormedZmod_decFieldType.
Canonical pseudoMetricNormedZmod_closedFieldType.
Canonical normedMod_decFieldType.
Canonical normedMod_closedFieldType.
Coercion numClosedField_lmodType : numClosedFieldType >-> lmodType.
Coercion numClosedField_lalgType : numClosedFieldType >-> lalgType.
Coercion numClosedField_algType : numClosedFieldType >-> algType.
Coercion numClosedField_comAlgType : numClosedFieldType >-> comAlgType.
Coercion numClosedField_unitAlgType : numClosedFieldType >-> unitAlgType.
Coercion numClosedField_comUnitAlgType : numClosedFieldType >-> comUnitAlgType.
Coercion numClosedField_vectType : numClosedFieldType >-> vectType.
Coercion numClosedField_FalgType : numClosedFieldType >-> FalgType.
Coercion numClosedField_fieldExtType : numClosedFieldType >-> fieldExtType.
Coercion numClosedField_pseudoMetricNormedZmodType :
  numClosedFieldType >-> pseudoMetricNormedZmodType.
Coercion numClosedField_normedModType : numClosedFieldType >-> normedModType.
(* numFieldType *)
Canonical numField_lmodType.
Canonical numField_lalgType.
Canonical numField_algType.
Canonical numField_comAlgType.
Canonical numField_unitAlgType.
Canonical numField_comUnitAlgType.
Canonical numField_vectType.
Canonical numField_FalgType.
Canonical numField_fieldExtType.
Canonical numField_pseudoMetricNormedZmodType.
Canonical numField_normedModType.
Canonical lmod_porderType.
Canonical lmod_numDomainType.
Canonical lalg_pointedType.
Canonical lalg_filteredType.
Canonical lalg_topologicalType.
Canonical lalg_uniformType.
Canonical lalg_pseudoMetricType.
Canonical lalg_normedZmodType.
Canonical lalg_pseudoMetricNormedZmodType.
Canonical lalg_normedModType.
Canonical lalg_porderType.
Canonical lalg_numDomainType.
Canonical alg_pointedType.
Canonical alg_filteredType.
Canonical alg_topologicalType.
Canonical alg_uniformType.
Canonical alg_pseudoMetricType.
Canonical alg_normedZmodType.
Canonical alg_pseudoMetricNormedZmodType.
Canonical alg_normedModType.
Canonical alg_porderType.
Canonical alg_numDomainType.
Canonical comAlg_pointedType.
Canonical comAlg_filteredType.
Canonical comAlg_topologicalType.
Canonical comAlg_uniformType.
Canonical comAlg_pseudoMetricType.
Canonical comAlg_normedZmodType.
Canonical comAlg_pseudoMetricNormedZmodType.
Canonical comAlg_normedModType.
Canonical comAlg_porderType.
Canonical comAlg_numDomainType.
Canonical unitAlg_pointedType.
Canonical unitAlg_filteredType.
Canonical unitAlg_topologicalType.
Canonical unitAlg_uniformType.
Canonical unitAlg_pseudoMetricType.
Canonical unitAlg_normedZmodType.
Canonical unitAlg_pseudoMetricNormedZmodType.
Canonical unitAlg_normedModType.
Canonical unitAlg_porderType.
Canonical unitAlg_numDomainType.
Canonical comUnitAlg_pointedType.
Canonical comUnitAlg_filteredType.
Canonical comUnitAlg_topologicalType.
Canonical comUnitAlg_uniformType.
Canonical comUnitAlg_pseudoMetricType.
Canonical comUnitAlg_normedZmodType.
Canonical comUnitAlg_pseudoMetricNormedZmodType.
Canonical comUnitAlg_normedModType.
Canonical comUnitAlg_porderType.
Canonical comUnitAlg_numDomainType.
Canonical vect_pointedType.
Canonical vect_filteredType.
Canonical vect_topologicalType.
Canonical vect_uniformType.
Canonical vect_pseudoMetricType.
Canonical vect_normedZmodType.
Canonical vect_pseudoMetricNormedZmodType.
Canonical vect_normedModType.
Canonical vect_porderType.
Canonical vect_numDomainType.
Canonical Falg_pointedType.
Canonical Falg_filteredType.
Canonical Falg_topologicalType.
Canonical Falg_uniformType.
Canonical Falg_pseudoMetricType.
Canonical Falg_normedZmodType.
Canonical Falg_pseudoMetricNormedZmodType.
Canonical Falg_normedModType.
Canonical Falg_porderType.
Canonical Falg_numDomainType.
Canonical fieldExt_pointedType.
Canonical fieldExt_filteredType.
Canonical fieldExt_topologicalType.
Canonical fieldExt_uniformType.
Canonical fieldExt_pseudoMetricType.
Canonical fieldExt_normedZmodType.
Canonical fieldExt_pseudoMetricNormedZmodType.
Canonical fieldExt_normedModType.
Canonical fieldExt_porderType.
Canonical fieldExt_numDomainType.
Canonical pseudoMetricNormedZmod_ringType.
Canonical pseudoMetricNormedZmod_comRingType.
Canonical pseudoMetricNormedZmod_unitRingType.
Canonical pseudoMetricNormedZmod_comUnitRingType.
Canonical pseudoMetricNormedZmod_idomainType.
Canonical pseudoMetricNormedZmod_fieldType.
Canonical pseudoMetricNormedZmod_porderType.
Canonical pseudoMetricNormedZmod_numDomainType.
Canonical normedMod_ringType.
Canonical normedMod_comRingType.
Canonical normedMod_unitRingType.
Canonical normedMod_comUnitRingType.
Canonical normedMod_idomainType.
Canonical normedMod_fieldType.
Canonical normedMod_porderType.
Canonical normedMod_numDomainType.
Coercion numField_lmodType : numFieldType >-> lmodType.
Coercion numField_lalgType : numFieldType >-> lalgType.
Coercion numField_algType : numFieldType >-> algType.
Coercion numField_comAlgType : numFieldType >-> comAlgType.
Coercion numField_unitAlgType : numFieldType >-> unitAlgType.
Coercion numField_comUnitAlgType : numFieldType >-> comUnitAlgType.
Coercion numField_vectType : numFieldType >-> vectType.
Coercion numField_FalgType : numFieldType >-> FalgType.
Coercion numField_fieldExtType : numFieldType >-> fieldExtType.
Coercion numField_pseudoMetricNormedZmodType :
  numFieldType >-> pseudoMetricNormedZmodType.
Coercion numField_normedModType : numFieldType >-> normedModType.
End Exports.

End numFieldNormedType.
Import numFieldNormedType.Exports.

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normmZ l (x : V) : `| l *: x | = `| l | * `| x |.
Proof. by case: V x => V0 [a b [c]] //= v; rewrite c. Qed.

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma nbhs_le_nbhs_norm (x : V) : nbhs x `=>` nbhs_norm x.
Proof.
move=> P [_ /posnumP[e] subP]; apply/nbhs_ballP.
by eexists; last (move=> y Py; apply/subP; apply/Py).
Qed.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Proof.
move=> P /nbhs_ballP [_ /posnumP[e] Pxe].
by exists e%:num => // y; apply/Pxe.
Qed.

Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Proof. by rewrite funeqE => x; rewrite -filter_from_ballE. Qed.

Lemma nbhs_normP x P : nbhs x P <-> nbhs_norm x P.
Proof. by rewrite nbhs_nbhs_norm. Qed.

Lemma filter_from_norm_nbhs x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : set V) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : set V) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : set V) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma cvg_distP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !nbhs_simpl. Qed.

Lemma cvg_dist {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Proof. by move=> /cvg_distP. Qed.

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
Proof. rewrite nbhs_nbhs_norm; by apply: nbhsx_ballx. Qed.

End NormedModule_numDomainType.
Hint Resolve normr_ge0 : core.
Arguments cvg_dist {_ _ F FF}.

Lemma pinfty_ex_gt {R : numFieldType} (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Proof.
by move=> m_real Agt; near (pinfty_nbhs R) => M;
   exists M; near: M => //; exists m.
Grab Existential Variables. all: end_near. Qed.

Lemma pinfty_ex_gt0 {R : numFieldType} (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Proof. by apply: pinfty_ex_gt; rewrite real0. Qed.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Definition fun1 {T : Type} {K : numFieldType} :
  T -> K := fun=> 1.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : normedModType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : normedModType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numFieldType) (V W : normedModType K)
   (h : T -> V) (k : K) (F G : set (set T)) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

Lemma sub_dominatedr (T : Type) (K : numFieldType) (V : normedModType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set (set T)) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Lemma dominated_by1 {T : Type} {K : numFieldType} {V : normedModType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType} {V : normedModType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_dom_bound {T : Type} {K : numFieldType} {V W : normedModType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Proof.
rewrite /dominated_by; split => [/pinfty_ex_gt0[M M_gt0]|[M]] FM.
  by exists M.
have [] := pselect (exists x, (h x != 0) && (`|f x| <= M * `|h x|)); last first.
  rewrite -forallNE; move=> Nex; exists 0; rewrite real0; split => //.
  move=> k k_gt0; apply: filterS FM => x /= f_le_Mh.
  have /negP := Nex x; rewrite negb_and negbK f_le_Mh orbF => /eqP h_eq0.
  by rewrite h_eq0 normr0 !mulr0 in f_le_Mh *.
case => x0 /andP[hx0_neq0] /(le_trans (normr_ge0 _)) /ger0_real.
rewrite realrM // ?normr_eq0// => M_real.
exists M; split => // k Mk; apply: filterS FM => x /le_trans/= ->//.
by rewrite ler_wpmul2r// ltW.
Qed.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType} {V W : normedModType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pmul2r ?normr_gt0// ltr_addl.
Qed.

Definition bounded_near {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : normedModType K} :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : normedModType K)
     (F G : set (set T)) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Proof. by move=> FG f; rewrite /bounded_near; apply: filterS=> M; apply: FG. Qed.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : normedModType K)
     (f g : T -> V) (F : set (set T)) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Proof.
move=> le_fg; rewrite /bounded_near; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_bound {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Grab Existential Variables. all: end_near. Qed.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : Filter F}:
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltr_addl.
Qed.

Notation "[ 'bounded' E | x 'in' A ]" := (bounded_near (fun x => E) (globally A))
  (at level 0, x ident, format "[ 'bounded'  E  |  x  'in'  A ]").
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" := (dominated_by (self_sub id) k (self_sub f))
  (at level 2, format "k .-lipschitz_on  f") : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set (set (V * V))) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Proof. by move=> FG; rewrite /lipschitz_on; apply: filterS => M; apply: FG. Qed.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set (set (V * V))) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Proof. by move=> f_lip; apply/ex_dom_bound; exists k. Qed.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A)))
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Notation "k .-lipschitz f" := (k.-lipschitz_setT f)
  (at level 2, format "k .-lipschitz  f") : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A)))
  (at level 0, x ident, format "[ 'lipschitz'  E  |  x  'in'  A ]").
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R)
   (k : R) (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Proof.
by move=> bndf x Ax; apply: sub_klipschitz bndf; apply: within_nbhsW.
Qed.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Proof.
by move=> bndf x Ax; apply: sub_lipschitz bndf; apply: within_nbhsW.
Qed.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) : 1.-lipschitz (@id V).
Proof. by move=> [/= x y] _; rewrite mul1r. Qed.
Arguments lipschitz_id {R V}.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).
Implicit Types (x y z : V).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff V.
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
Hint Extern 0 (hausdorff _) => solve[apply: norm_hausdorff] : core.

(* TODO: check if the following lemma are indeed useless *)
(*       i.e. where the generic lemma is applied, *)
(*            check that norm_hausdorff is not used in a hard way *)

Lemma norm_closeE x y : close x y = (x = y). Proof. exact: closeE. Qed.
Lemma norm_close_eq x y : close x y -> x = y. Proof. exact: close_eq. Qed.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Proof. exact: cvg_unique. Qed.

Lemma norm_cvg_eq x y : x --> y -> x = y. Proof. exact: cvg_eq. Qed.
Lemma norm_lim_id x : lim x = x. Proof. exact: lim_id. Qed.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Proof. exact: cvg_lim. Qed.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. exact: lim_near_cst. Qed.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Proof. exact: lim_cst. Qed.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Proof. exact: cvgi_unique. Qed.

Lemma norm_cvgi_map_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof. exact: cvgi_map_lim. Qed.

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
move=> /posnumP[{}e] /le_lt_trans ->//.
by rewrite [X in _ < X]splitr ltr_spaddl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

Lemma cvg_distW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Proof.
move=> cv; apply/cvg_distP => _/posnumP[e]; near=> x.
by apply: normm_leW => //; near: x; apply: cv.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_bounded {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> bounded_near id F.
Proof.
move=> /cvg_dist Fy; exists `|y|; rewrite normr_real; split => //= M.
rewrite -subr_gt0 => /Fy; apply: filterS => y' yy'; apply: ltW.
by rewrite -(@ltr_add2r _ (- `|y|)) (le_lt_trans (ler_sub_dist _ _))// distrC.
Qed.

Lemma normrZV (x : V) : x != 0 -> `| `| x |^-1 *: x | = 1.
Proof. by move=> ?; rewrite normmZ normfV normr_id mulVf ?normr_eq0. Qed.

End NormedModule_numFieldType.
Arguments cvg_bounded {_ _ F FF}.
Hint Extern 0 (hausdorff _) => solve[apply: norm_hausdorff] : core.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Section hausdorff.

Lemma Rhausdorff (R : realFieldType) : hausdorff R.
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/in_segment_addgt0Pr => _ /posnumP[e].
rewrite in_itv /= -ler_distl; set he := (e%:num / 2)%:pos.
have [z [zx_he yz_he]] := clxy _ _ (nbhsx_ballx x he) (nbhsx_ballx y he).
have := ball_triangle yz_he (ball_sym zx_he).
by rewrite -mulr2n -mulr_natr divfK // => /ltW.
Qed.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Lemma continuous_cvg_dist {R : numFieldType}
  (V W : normedModType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Proof.
move=> + + e => /(_ l)/cvg_dist/(_ _ (posnum_gt0 e)).
rewrite near_map => /nbhs_ballP[_/posnumP[a]] + xl; apply.
move/cvg_ball : xl => /(_ _ a)/nbhs_ballP[_/posnumP[b]]; apply; exact: ballxx.
Qed.

Module BigmaxBigminr.
Section bigmax_bigmin.
Variable (R : realDomainType).

Lemma bigmaxr_mkcond I r (P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i =
     \big[maxr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite unlock; elim: r x => //= i r ihr x.
case P; rewrite ihr // max_r //; elim: r {ihr} => //= j r ihr.
by rewrite le_maxr ihr orbT.
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
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?maxxx //.
by rewrite maxCA -!maxA maxCA.
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
  by rewrite big_nil maxxx.
by rewrite big_cons maxCA -ihl.
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
  by move=> i _; case: (a i) => //=; rewrite maxC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -maxA -bigmaxr_idl ihl.
Qed.

Lemma bigminrID I r (a P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i =
  minr (\big[minr/x]_(i <- r | P i && a i) F i)
    (\big[minr/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite !bigminr_maxr -oppr_max -bigmaxrID. Qed.

Lemma bigmaxr_seq1 I (i : I) (F : I -> R) x :
  \big[maxr/x]_(j <- [:: i]) F j = maxr (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigminr_seq1 I (i : I) (F : I -> R) x :
  \big[minr/x]_(j <- [:: i]) F j = minr (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigmaxr_pred1_eq (I : finType) (i : I) (F : I -> R) x :
  \big[maxr/x]_(j | j == i) F j = maxr (F i) x.
Proof.
have [e1 <- _ [e_enum _]] := big_enumP (pred1 i).
by rewrite (perm_small_eq _ e_enum) enum1 ?bigmaxr_seq1.
Qed.

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
move=> Pj; rewrite (bigmaxrID _ (pred1 j)) [in RHS]bigmaxr_idl maxA.
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
Proof. by move=> Pi0; rewrite (bigmaxrD1 _ _ Pi0) le_maxr lexx. Qed.

Lemma bigminr_ler_cond (I : finType) (P : pred I) (F : I -> R) x i0 :
  P i0 -> \big[minr/x]_(i | P i) F i <= F i0.
Proof. by move=> Pi0; rewrite (bigminrD1 _ _ Pi0) le_minl lexx. Qed.

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
  by elim/big_ind: _ => // ??; rewrite le_maxl =>->.
rewrite bigmaxr_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
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
  by elim/big_ind: _ => // ??; rewrite lt_maxl =>->.
rewrite bigmaxr_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
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
- by rewrite bigmaxr_idl le_maxr lemx.
- by rewrite (bigmaxrD1 _ _ Pi) le_maxr lemFi.
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
- by rewrite bigmaxr_idl lt_maxr ltmx.
- by rewrite (bigmaxrD1 _ _ Pi) lt_maxr ltmFi.
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
rewrite nng_le; apply/BigmaxrNonneg.bigmaxr_lerP; split.
  exact: addr_ge0.
move=> ij _; rewrite mxE; apply: le_trans (ler_norm_add _ _) _.
rewrite ler_add // -nng_abs_le //= -nng_le /= normr_id nng_le;
  exact/BigmaxrNonneg.ler_bigmaxr.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le => /andP [/BigmaxrNonneg.bigmaxr_lerP [_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -nng_abs_eq0 eq_le (x0 (i,j)) // andTb -nng_le /= normr_ge0.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%:nng)) /=.
  by elim/big_ind : _ => // a b /val_inj ->{a} /val_inj ->{b}; rewrite maxxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b != 0%:nng by exists i.
  by apply: contra H => b0; rewrite max_r.
+ suff /Ha[i xi] : a != 0%:nng by exists i.
  by apply: contra H => a0; rewrite max_l // ltW.
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
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE -nng_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite max_r | rewrite max_l // ltW].
Qed.

Definition matrix_normedZmodMixin (K : numDomainType) (m n : nat) :=
  @Num.NormedMixin _ _ _ (@mx_norm K m.+1 n.+1) (@ler_mx_norm_add _ _ _)
    (@mx_norm_eq0 _ _ _) (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Canonical matrix_normedZmodType (K : numDomainType) (m n : nat) :=
  NormedZmodType K 'M[K]_(m.+1, n.+1) (matrix_normedZmodMixin K m n).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Lemma mx_norm_ball :
  @ball _ [pseudoMetricType K of 'M[K]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Proof.
rewrite /= /normr /= predeq3E => x e y; split.
- move=> xe_y; rewrite /ball_/= mx_normE.
  (* TODO:  lemma : ball x e y -> 0 < e *)
  have lee0 : ( 0 < e) by rewrite (le_lt_trans _ (xe_y ord0 ord0)) //.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  rewrite nng_lt; apply/BigmaxrNonneg.bigmaxr_ltrP.
- split; [rewrite -nng_lt //= | move=> ??; rewrite !mxE; exact: xe_y].
  rewrite /ball_/= mx_normE => H.
  have lee0 : (0 < e) by rewrite (le_lt_trans _ H) // nonnegnum_ge0.
  move : H.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  move => /BigmaxrNonneg.bigmaxr_ltrP => -[e0 xey] i j.
  move: (xey (i, j)); rewrite !mxE; exact.
Qed.

Definition matrix_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K 'M[K]_(m.+1, n.+1) matrix_PseudoMetricNormedZmodMixin.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -nng_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
rewrite nonneg_maxr; congr (maxr _ _)%:nngnum; exact/val_inj.
Qed.

Definition matrix_NormedModMixin := NormedModMixin mx_normZ.
Canonical matrix_normedModType :=
  NormedModType K 'M[K]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_NormedModule.

(** ** Pairs *)

Section prod_PseudoMetricNormedZmodule.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite comparable_lt_maxl// ?real_comparable//; split=> /andP.
Qed.

Lemma prod_norm_ball : @ball _ [pseudoMetricType K of U * V] = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

Definition prod_pseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin prod_norm_ball.
Canonical prod_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K (U * V) prod_pseudoMetricNormedZmodMixin.

End prod_PseudoMetricNormedZmodule.

Section prod_NormedModule.
Context {K : numDomainType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normmZ maxr_pmulr. Qed.

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

Lemma cvg_dist2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: cvg_distP. Qed.

(* Lemma cvg_dist_supP {F : set (set U)} {G : set (set V)} *)
(*   {FF : Filter F} {FG : Filter G} (y : U) (z : V): *)
(*   (F, G) --> (y, z) <-> *)
(*   forall eps : {posnum R}, {near F & G, forall y' z', *)
(*           (`|[y - y']| < eps) /\ (`|[z - z']| < eps) }. *)
(* Proof. *)
(* rewrite cvg_ballP; split => [] P eps. *)
(* - have [[A B] /=[FA GB] ABP] := P eps; exists (A, B) => -//[a b] [/= Aa Bb]. *)
(*   apply/andP; rewrite -ltr_maxl. *)
(*   have /= := (@sub_ball_norm_rev _ _ (_, _)). *)

Lemma cvg_dist2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. by rewrite cvg_distP. Qed.

End prod_NormedModule_lemmas.
Arguments cvg_dist2 {_ _ _ F G FF FG}.

(** Rings with absolute values are normed modules *)

(*Definition AbsRing_NormedModMixin (K : absRingType) :=
  @NormedModule.Mixin K _ _ _ (abs : K^o -> R) ler_abs_add absrM (ball_absE K)
  absr0_eq0.
Canonical AbsRing_NormedModType (K : absRingType) :=
  NormedModType K K^o (AbsRing_NormedModMixin _).*)





(** Normed vector spaces have some continuous functions *)

(* kludge *)

Global Instance filter_nbhs (K' : numFieldType) (k : K') :
  Filter (nbhs k).
Proof.
exact: (@nbhs_filter).
Qed.


Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.
Local Notation "'+oo'" := (pinfty_nbhs K).

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/=x y]; apply/cvg_distP=> _/posnumP[e].
rewrite !near_simpl /=; near=> a b => /=; rewrite opprD addrACA.
by rewrite normm_lt_split //; [near: a|near: b]; apply: cvg_dist.
Grab Existential Variables. all: end_near. Qed.


Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Proof.
case: n => [|n] x; first exact: cvg_cst.
apply/cvg_distP=> _/posnumP[e]; rewrite !near_simpl /=; near=> a.
rewrite -mulrnBl normrMn -mulr_natr -ltr_pdivl_mulr//.
by near: a; apply: cvg_dist.
Grab Existential Variables. all: end_near. Qed.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).

Proof.
move=> [k x]; apply/cvg_distP=> _/posnumP[e].
rewrite !near_simpl /=; near +oo => M.
have M_gt0 : M > 0 by near: M; apply: nbhs_pinfty_gt_real; rewrite real0.
near=> l z => /=.
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normmZ.
  suff: (`|k| + 1) * `|x - z| < e%:num / 2.
    by apply: le_lt_trans; rewrite ler_pmul// ler_addl.
  rewrite -ltr_pdivl_mull // ?(lt_le_trans ltr01) ?ler_addr //; near: z.
  by apply: cvg_dist; rewrite // mulr_gt0 // ?invr_gt0 ltr_paddl.
have zM : `|z| <= M by near: z; near: M; apply:cvg_bounded; apply: cvg_refl.
rewrite (le_lt_trans (ler_pmul _ _ (lexx _) zM)) // ?ltW // -ltr_pdivl_mulr//.
by near: l; apply: cvg_dist; rewrite // mulr_gt0// invr_gt0.
Grab Existential Variables. all: end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous (_, _))).
Qed.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; rewrite -scaleN1r => P /scaler_continuous /=.
by rewrite !nbhs_nearE near_map; apply: filterS => x'; rewrite scaleN1r.
Qed.

(** Continuity of norm *)

Lemma norm_continuous : continuous (normr : V -> K).
Proof.
move=> x; apply/cvg_distP => _/posnumP[e].
rewrite near_map; apply/nbhs_normP; exists e%:num => // y.
by rewrite -ball_normE; apply/(le_lt_trans (ler_dist_dist _ _)).
Qed.

End NVS_continuity_normedModType.

Lemma cvg_dist0 {U} {K : numFieldType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : K)
  -> f @ F --> (0 : V).
Proof.
move=> /(cvg_dist (_ : K)) fx0; apply/cvg_distP => _/posnumP[e].
rewrite near_simpl; have := fx0 _ [gt0 of e%:num]; rewrite near_simpl.
by apply: filterS => x; rewrite !sub0r !normrN [ `|_| ]ger0_norm.
Qed.

Section NVS_continuity_mul.

Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K * K => z.1 * z.2).
Proof. exact: scale_continuous. Qed.

Lemma inv_continuous (x : K) : x != 0 -> {for x, continuous GRing.inv}.
Proof.
move=> x_neq0 /=; apply/cvg_distP => _/posnumP[e]; rewrite !nearE/=; near=> y.
have y_gt : `|y| > `|x| / 2.
  have /(le_lt_trans (ler_sub_dist _ _)) : `|x - y| < `|x| / 2.
    by near: y; apply: cvg_dist; rewrite // divr_gt0// normr_gt0//.
  by rewrite ltr_subl_addr -ltr_subl_addl {1}[ `|x| ]splitr addrK.
have y_neq0 : y != 0.
  by rewrite -normr_eq0 gt_eqF// (le_lt_trans _ y_gt) ?divr_ge0.
rewrite /= -div1r -[y^-1]div1r -mulNr addf_div// mul1r mulN1r normrM normfV.
rewrite ltr_pdivr_mulr ?normr_gt0 ?mulf_neq0//.
apply: (@lt_le_trans _ _ (e%:num * (`|x| * (`|x| / 2)))).
  by rewrite distrC; near: y; apply: cvg_dist; rewrite ?mulr_gt0// ?normr_gt0.
by rewrite normrM !ler_wpmul2l// ltW.
Grab Existential Variables. all: end_near. Qed.

End NVS_continuity_mul.

Section cvg_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> (- f) @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Proof. by move=> /cvgN /cvgP. Qed.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Proof. by rewrite propeqE; split=> /cvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Proof. by move=> ?;  apply: continuous_cvg => //; exact: natmul_continuous. Qed.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Proof. by move=> /cvgMn /cvgP. Qed.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Proof. by move=> ? ?; apply: continuous2_cvg => //; exact: add_continuous. Qed.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Proof. by have := cvgP _ (cvgD _ _); apply. Qed.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Proof. by move=> ? ?; apply: cvgD => //; apply: cvgN. Qed.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Proof. by have := cvgP _ (cvgB _ _); apply. Qed.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cvgD; apply.
by move=> /is_cvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Proof. by rewrite addrC; apply: is_cvgDlE. Qed.

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof. move=> ? ?; apply: continuous2_cvg => //; exact: scale_continuous. Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZl  _); apply. Qed.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZr  _); apply. Qed.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZr k^-1)|/(@cvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K).
Proof. by apply: continuous_cvg; apply: norm_continuous. Qed.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K) @ F).
Proof. by have := cvgP _ (cvg_norm _); apply. Qed.

End cvg_composition.

Section cvg_composition_field.

Context {K : numFieldType}  {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f * g) @ F --> a * b.
Proof. exact: cvgZ. Qed.

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Proof. exact: cvgZl. Qed.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Proof. exact: cvgZr. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f * g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f * g @ F).
Proof. exact: is_cvgZr. Qed.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f * g @ F) = cvg (g @ F).
Proof. exact: is_cvgZrE. Qed.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f * g @ F).
Proof. by move=> f_cvg; rewrite mulrC; apply: is_cvgMr. Qed.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f * g @ F) = cvg (f @ F).
Proof. by move=> a_neq0; rewrite mulrC is_cvgMrE. Qed.

Lemma cvgV f a : a != 0 -> f @ F --> a -> (f x)^-1 @[x --> F] --> a^-1.
Proof.
by move=> k_neq0 f_cvg; apply: continuous_cvg => //; apply: inv_continuous.
Qed.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg ((fun x => (f x)^-1) @ F).
Proof. by move=> /cvgV cvf /cvf /cvgP. Qed.

End cvg_composition_field.

Section limit_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgN. Qed.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgD. Qed.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgB. Qed.

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgZ. Qed.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZl. Qed.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZr. Qed.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K) @ F) = `|lim (f @ F)|.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_norm. Qed.

End limit_composition.

Section limit_composition_field.

Context {K : numFieldType}  {T : topologicalType}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f * g @ F) = lim (f @ F) * lim (g @ F).
Proof.
by move=> ? ?; apply: cvg_lim => //; apply: cvgM.
Qed.

Lemma limV f : cvg (f @ F) -> lim (f @ F) != 0 -> lim ((fun x => (f x)^-1) @ F) = (lim (f @ F))^-1.
Proof.
by move=> ? ?; apply: cvg_lim => //; apply: cvgV.
Qed.

End limit_composition_field.

Section local_continuity.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K) (x : T) (k : K) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Proof. by move=> f_cont g_cont; apply: cvgD. Qed.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Proof. by move=> f_cont g_cont; apply: cvgB. Qed.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Proof. by move=> ? ?; apply: cvgZ. Qed.

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s * t)}.
Proof. by move=> f_cont g_cont; apply: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : numFieldType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (PseudoMetric.Pack base)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompletePseudoMetric.class_of K T :=
  @CompletePseudoMetric.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> CompletePseudoMetric.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack :=
  fun bT (b : NormedModule.class_of K T) & phant_id (@NormedModule.class K phK bT) b =>
  fun mT m & phant_id (@Complete.class mT) (@Complete.Class T b m) =>
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
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition normedModType := @NormedModule.Pack K phK cT xclass.
Definition completeType := @Complete.Pack cT xclass.
Definition completePseudoMetricType := @CompletePseudoMetric.Pack K cT xclass.
Definition complete_zmodType := @GRing.Zmodule.Pack completeType xclass.
Definition complete_lmodType := @GRing.Lmodule.Pack K phK completeType xclass.
Definition complete_normedZmodType := @Num.NormedZmodule.Pack K phK completeType xclass.
Definition complete_pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK completeType xclass.
Definition complete_normedModType := @NormedModule.Pack K phK completeType xclass.
Definition completePseudoMetric_lmodType : GRing.Lmodule.type phK :=
  @GRing.Lmodule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_zmodType : GRing.Zmodule.type :=
  @GRing.Zmodule.Pack (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_normedModType : NormedModule.type phK :=
  @NormedModule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_normedZmodType : Num.NormedZmodule.type phK :=
  @Num.NormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass.
Definition completePseudoMetric_pseudoMetricNormedZmodType :
  PseudoMetricNormedZmodule.type phK :=
  @PseudoMetricNormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> CompletePseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
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
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion completePseudoMetricType : type >-> CompletePseudoMetric.type.
Canonical completePseudoMetricType.
Canonical complete_zmodType.
Canonical complete_lmodType.
Canonical complete_normedZmodType.
Canonical complete_pseudoMetricNormedZmodType.
Canonical complete_normedModType.
Canonical completePseudoMetric_lmodType.
Canonical completePseudoMetric_zmodType.
Canonical completePseudoMetric_normedModType.
Canonical completePseudoMetric_normedZmodType.
Canonical completePseudoMetric_pseudoMetricNormedZmodType.
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

Arguments cvg_distW {_ _ F FF}.

Lemma R_complete (R : realType) (F : set (set R)) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchy_ballP F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down A).
have /cauchy_ballP /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup D; first split.
- exists (x0 - 1) => A FA.
  near F => x.
  apply/downP; exists x; first by near: x.
  by rewrite ler_distl_subl // ltW //; near: x.
- exists (x0 + 1); apply/ubP => x /(_ _ x01) /downP [y].
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltr_subl_addr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup D).
apply: (cvg_distW) => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl; move/ubP: (sup_upper_bound D_has_sup) => -> //=.
  apply: sup_le_ub => //; first by case: D_has_sup.
  have Fxeps : F (ball_ [eta normr] x (eps)%:num).
    by near: x; apply: nearP_dep; apply: F_cauchy.
  apply/ubP => y /(_ _ Fxeps) /downP[z].
  rewrite /ball_/= ltr_distl ltr_subl_addr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite /D /= => A FA; near F => y.
apply/downP; exists y.
by near: y.
rewrite ler_subl_addl -ler_subl_addr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Grab Existential Variables. all: end_near. Qed.

Canonical R_regular_completeType (R : realType) :=
  CompleteType R^o (@R_complete R). (*todo : delete*)
Canonical R_regular_CompleteNormedModule (R : realType) :=
  [completeNormedModType R of R^o]. (*todo : delete*)

Canonical R_completeType (R : realType) :=
  [completeType of R for [completeType of R^o]].
Canonical R_CompleteNormedModule (R : realType) :=
  [completeNormedModType R of R].
(* new *)

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R) := within (fun u : R => x < u) (nbhs x).

(* :TODO: We should have filter notation ^- and ^+ for these *)

Global Instance at_right_proper_filter (x : R) : ProperFilter (at_right x).
Proof.
apply: Build_ProperFilter' => -[_/posnumP[d] /(_ (x + d%:num / 2))].
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

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvg a -> bounded_fun a.
Proof.
move=> /cvg_bounded/ex_bound => -[/= Moo]; rewrite !near_simpl/=.
rewrite [(\near a, _ <= _)](near_map _ \oo) => -[N _ /(_ _) a_leM].
have Moo_real : Moo \is Num.real
  by rewrite ger0_real ?(le_trans _ (a_leM N _))/=.
rewrite /bounded_near /=; near=> M => n _.
have [nN|nN]/= := leqP N n.
  by apply: (le_trans (a_leM _ _)) => //; near: M; apply: nbhs_pinfty_ge_real.
move: n nN; suff /(_ (Ordinal _)) : forall n : 'I_N, `|a n| <= M by [].
by near: M; apply: filter_forall => i; apply: nbhs_pinfty_ge_real.
Grab Existential Variables. all: end_near. Qed.

End cvg_seq_bounded.

Lemma closure_sup (R : realType) (A : set R) :
  A !=set0 -> has_ubound A -> closure A (sup A).
Proof.
move=> A0 ?; have [|AsupA] := pselect (A (sup A)); first exact: subset_closure.
rewrite closure_limit_point; right => U /nbhs_ballP[_ /posnumP[e]] supAeU.
suff [x [Ax /andP[sAex xsA]]] : exists x, A x /\ sup A - e%:num < x < sup A.
  exists x; split => //; first by rewrite lt_eqF.
  apply supAeU; rewrite /ball /= ltr_distl (addrC x e%:num) -ltr_subl_addl sAex.
  by rewrite andbT (le_lt_trans _ xsA) // ler_subl_addl ler_addr.
apply: contrapT => /forallNP Ax.
suff /(sup_le_ub A0) : ubound A (sup A - e%:num).
  by rewrite leNgt => /negP; apply; rewrite ltr_subl_addl ltr_addr.
move=> y Ay; have /not_andP[//|/negP] := Ax y.
rewrite negb_and leNgt => /orP[//|]; apply: contra => sAey.
rewrite lt_neqAle sup_upper_bound // andbT.
by apply: contra_not_neq AsupA => <-.
Qed.

Lemma near_infty_natSinv_lt (R : archiFieldType) (z : R) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Proof.
near=> n; rewrite -(@ltr_pmul2r _ n.+1%:R) // mulVr ?unitfE //.
rewrite -(@ltr_pmul2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // ltr_nat.
by near: n; exists (Num.bound e%:num^-1).
Grab Existential Variables. all: end_near. Qed.

Lemma limit_pointP (T : archiFieldType) (A : set T) (x : T) :
  limit_point A x <-> exists a_ : nat -> T,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ --> x].
Proof.
split=> [Ax|[a_ [aTA a_x] ax]]; last first.
  move=> U /ax[m _ a_U]; near \oo => n; exists (a_ n); split => //.
  by apply aTA; exists n.
  by apply a_U; near: n; exists m.
pose U := fun n : nat => [set z : T | `|x - z| < n.+1%:R^-1].
suff [a_ anx] : exists a_, forall n, a_ n != x /\ (U n `&` A) (a_ n).
  exists a_; split.
  - by move=> a [n _ <-]; have [? []] := anx n.
  - by move=> n; have [] := anx n.
  - apply/cvg_distP => _/posnumP[e]; rewrite near_map; near=> n.
    have [? [] xann Aan] := anx n.
    by rewrite (lt_le_trans xann) // ltW //; near: n; exact: near_infty_natSinv_lt.
have @a_ : nat -> T.
  move=> n; have : nbhs (x : T) (U n).
    by apply/(nbhs_ballP (x:T) (U n)); rewrite nbhs_ballE; exists n.+1%:R^-1.
  by move/Ax/cid => [/= an [anx Aan Uan]]; exact: an.
by exists a_ => n; rewrite /a_ /= /ssr_have; case: cid => ? [].
Grab Existential Variables. all: end_near. Qed.

Section open_closed_sets.
Variable R : realFieldType (* TODO: can we generalize to numFieldType? *).

(* TODO : topology on R *)
(** Some open sets of [R] *)

Lemma open_lt (y : R) : open [set x : R| x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0; exists (y - x) => // z.
by rewrite /= distrC ltr_distl addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.


Lemma open_gt (y : R) : open [set x : R | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= distrC ltr_distl opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : open [set x : R | x != y].
Proof.
rewrite (_ : mkset _ = [set x | x < y] `|` [set x | x > y]); first exact: openU.
rewrite predeqE => x /=; rewrite eq_le !leNgt negb_and !negbK orbC.
by symmetry; apply (rwP orP).
Qed.

(** Some closed sets of [R] *)

Lemma closed_le (y : R) : closed [set x : R | x <= y].
Proof.
rewrite (_ : mkset _ = ~` [set x | x > y]); first exact: closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.


Lemma closed_ge (y : R) : closed [set x : R | y <= x].
Proof.
rewrite (_ : mkset _ = ~` [set x | x < y]); first exact: closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.


Lemma closed_eq (y : R) : closed [set x : R | x = y].
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

Definition bound_side d (T : porderType d) (c : bool) (x : itv_bound T) :=
  if x is BSide c' _ then c == c' else false.

Lemma interval_open a b : ~~ bound_side true a -> ~~ bound_side false b ->
  open [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _.
- have -> : [set x | a < x < b] = [set x | a < x] `&` [set x | x < b].
    by rewrite predeqE => r; rewrite /mkset; split => [/andP[? ?] //|[-> ->]].
  by apply openI; [exact: open_gt | exact: open_lt].
- by under eq_set do rewrite itv_ge// inE.
- by under eq_set do rewrite in_itv andbT/=; exact: open_gt.
- exact: open_lt.
- by rewrite (_ : mkset _ = setT); [exact: openT | rewrite predeqE].
Qed.
Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _;
  do ?by under eq_set do rewrite itv_ge// inE falseE; apply: closed0.
- have -> : [set x | x \in `[a, b]] = [set x | x >= a] `&` [set x | x <= b].
    by rewrite predeqE => ?; rewrite /= in_itv/=; split=> [/andP[]|[->]].
  by apply closedI; [exact: closed_ge | exact: closed_le].
- by under eq_set do rewrite in_itv andbT/=; exact: closed_ge.
- exact: closed_le.
Qed.

End open_closed_sets.

Hint Extern 0 (open _) => now apply: open_gt : core.
Hint Extern 0 (open _) => now apply: open_lt : core.
Hint Extern 0 (open _) => now apply: open_neq : core.
Hint Extern 0 (closed _) => now apply: closed_ge : core.
Hint Extern 0 (closed _) => now apply: closed_le : core.
Hint Extern 0 (closed _) => now apply: closed_eq : core.

Section closure_left_right_open.
Variable R : archiFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R) = [set x | z <= x].
Proof.
rewrite predeqE => v; split.
  by rewrite closureE; apply; split => [|W /ltW //]; exact: closed_ge.
rewrite /mkset le_eqVlt => /orP[/eqP <-{v}|]; last first.
  by move=> ?; exact: subset_closure.
apply/subset_limit_point/limit_pointP; exists (fun n => z + n.+1%:R^-1); split.
- by move=> u [] m _ <-; rewrite ltr_addl.
- by move=> n; rewrite -subr_eq0 addrAC subrr add0r.
- apply/cvg_distP => _/posnumP[e]; rewrite near_map; near=> n.
  rewrite opprD addrA subrr add0r normrN ger0_norm //.
  by near: n; exact: near_infty_natSinv_lt.
Grab Existential Variables. all: end_near. Qed.

Lemma closure_lt z : closure ([set x : R | x < z]) = [set x | x <= z].
Proof.
rewrite predeqE => v; split.
  by rewrite closureE; apply; split => [|w /ltW //]; exact: closed_le.
rewrite /mkset le_eqVlt => /orP[/eqP <-{z}|]; last first.
  by move=> ?; exact: subset_closure.
apply/subset_limit_point/limit_pointP; exists (fun n => v - n.+1%:R^-1); split.
- by move=> u [] m _ <-; rewrite ltr_subl_addl ltr_addr.
- by move=> n; rewrite -subr_eq0 addrAC subrr add0r oppr_eq0.
- apply/cvg_distP => _/posnumP[e]; rewrite near_map; near=> n.
  rewrite opprD addrA subrr add0r opprK ger0_norm //.
  by near: n; exact: near_infty_natSinv_lt.
Grab Existential Variables. all: end_near. Qed.

End closure_left_right_open.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x < z < y -> E z.

Lemma is_intervalPle (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x <= z <= y -> E z.
Proof.
split=> iE x y Ex Ey z /andP[].
  rewrite le_eqVlt => /orP[/eqP <-//|xz]; rewrite le_eqVlt => /orP[/eqP ->//|?].
  by apply (iE _ _ Ex Ey); rewrite xz.
by move=> xz zy; apply (iE _ _ Ex Ey); rewrite (ltW xz) (ltW zy).
Qed.

Lemma interval_is_interval (i : interval R) : is_interval [set x | x \in i].
Proof.
by case: i => -[[]a|[]] [[]b|[]] // x y /=; do ?[by rewrite ?itv_ge//];
   move=> xi yi z; rewrite -[x < z < y]/(z \in `]x, y[); apply/subitvP;
   rewrite subitvE /Order.le/= ?(itvP xi, itvP yi).
Qed.

End interval.

Lemma right_bounded_interior (R : realType) (X : set R) :
  has_ubound X -> X^° `<=` [set r | r < sup X].
Proof.
move=> uX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP supXr|]; last first.
  by apply/negP; rewrite -leNgt sup_ub //; exact: interior_subset.
suff : ~ X^° (sup X) by rewrite supXr.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (sup X + f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprD addrA subrr.
  by rewrite sub0r normrN gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : sup X + f%:num <= sup X by apply sup_ub.
by apply/negP; rewrite -ltNge; rewrite ltr_addl.
Qed.

Lemma left_bounded_interior (R : realType) (X : set R) :
  has_lbound X -> X^° `<=` [set r | inf X < r].
Proof.
move=> lX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP rinfX|]; last first.
  by apply/negP; rewrite -leNgt inf_lb //; exact: interior_subset.
suff : ~ X^° (inf X) by rewrite -rinfX.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (inf X - f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprB addrCA subrr.
  by rewrite addr0 gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : inf X <= inf X - f%:num by apply inf_lb.
by apply/negP; rewrite -ltNge; rewrite ltr_subl_addr ltr_addl.
Qed.

(* TODO: move to reals.v? *)
Lemma inf_lb_strict (R : realType) (X : set R) : has_lbound X ->
  ~ X (inf X) -> X `<=` [set r | inf X < r].
Proof.
move=> lX XinfX r Xr; rewrite /mkset lt_neqAle inf_lb // andbT.
by apply/negP => /eqP infXr; move: XinfX; rewrite infXr.
Qed.

Lemma sup_ub_strict (R : realType) (X : set R) : has_ubound X ->
  ~ X (sup X) -> X `<=` [set r | r < sup X].
Proof.
move=> ubX XsupX r Xr; rewrite /mkset lt_neqAle sup_ub // andbT.
by apply/negP => /eqP supXr; move: XsupX; rewrite -supXr.
Qed.

Section interval_realType.
Variable R : realType.

Lemma interval_unbounded_setT (X : set R) : is_interval X ->
  ~ has_lbound X -> ~ has_ubound X -> X = setT.
Proof.
move=> iX lX uX; rewrite predeqE => x; split => // _.
move/has_lbPn : lX => /(_ x) [y Xy xy].
move/has_ubPn : uX => /(_ x) [z Xz xz].
by apply: (iX _ _ Xy Xz); rewrite xy xz.
Qed.

Lemma interval_left_unbounded_interior (X : set R) : is_interval X ->
  ~ has_lbound X -> has_ubound X -> X^° = [set r | r < sup X].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: right_bounded_interior.
rewrite -(open_subsetE _ (@open_lt _ _)) => r rsupX.
move/has_lbPn : lX => /(_ r)[y Xy yr].
have hsX : has_sup X by split => //; exists y.
have /(sup_adherent hsX)[e Xe] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => re; apply (iX _ _ Xy Xe); rewrite yr re.
Qed.

Lemma interval_right_unbounded_interior (X : set R) : is_interval X ->
  has_lbound X -> ~ has_ubound X -> X^° = [set r | inf X < r].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: left_bounded_interior.
rewrite -(open_subsetE _ (@open_gt _ _)) => r infXr.
move/has_ubPn : uX => /(_ r)[y Xy yr].
have hiX : has_inf X by split => //; exists y.
have /(inf_adherent hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
by rewrite addrCA subrr addr0 => er; apply: (iX _ _ Xe Xy); rewrite yr er.
Qed.

Lemma interval_bounded_interior (X : set R) : is_interval X ->
  has_lbound X -> has_ubound X -> X^° = [set r | inf X < r < sup X].
Proof.
move=> iX bX aX; rewrite eqEsubset; split=> [r Xr|].
  apply/andP; split;
    [exact: left_bounded_interior|exact: right_bounded_interior].
rewrite -open_subsetE; last exact: (@interval_open _ (BRight _) (BLeft _)).
move=> r /andP[iXr rsX].
have [/set0P X0|/negPn/eqP X0] := boolP (X != set0); last first.
  by move: (lt_trans iXr rsX); rewrite X0 inf_out ?sup_out ?ltxx // => - [[]].
have hiX : has_inf X by split.
have /(inf_adherent hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
rewrite addrCA subrr addr0 => er.
have hsX : has_sup X by split.
have /(sup_adherent hsX)[f Xf] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => rf; apply: (iX _ _ Xe Xf); rewrite er rf.
Qed.

Definition Rhull (X : set R) : interval R := Interval
  (if `[< has_lbound X >] then BSide `[< X (inf X) >] (inf X)
                          else BInfty _ true)
  (if `[< has_ubound X >] then BSide (~~ `[< X (sup X) >]) (sup X)
                          else BInfty _ false).

Lemma Rhull0 : Rhull set0 = `]0, 0[ :> interval R.
Proof.
rewrite /Rhull  (asboolT (has_lbound0 R)) (asboolT (has_ubound0 R)) asboolF //.
by rewrite sup0 inf0.
Qed.

Lemma sub_Rhull (X : set R) : X `<=` [set x | x \in Rhull X].
Proof.
move=> x Xx/=; rewrite in_itv/=.
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
+ by case: asboolP => ?; case: asboolP => ? //=;
     rewrite !(lteifF, lteifT, sup_ub, inf_lb, sup_ub_strict, inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lteifF, lteifT);
     [rewrite inf_lb | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lteifF, lteifT);
     [rewrite sup_ub | rewrite sup_ub_strict].
Qed.

Lemma is_intervalP (X : set R) : is_interval X <-> X = [set x | x \in Rhull X].
Proof.
split=> [iX|->]; last exact: interval_is_interval.
rewrite predeqE => x /=; split; [exact: sub_Rhull | rewrite in_itv/=].
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
- case: asboolP => XinfX; case: asboolP => XsupX;
    rewrite !(lteifF, lteifT).
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx].
    rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx supXx].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[infXx]; rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> ?; apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
- case: asboolP => XinfX; rewrite !(lteifF, lteifT, andbT).
  + rewrite le_eqVlt => /orP[/eqP<-//|infXx].
    apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
  + move=> infXx; apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
- case: asboolP => XsupX /=.
  + rewrite le_eqVlt => /orP[/eqP->//|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
  + move=> xsupX; apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
- by move=> _; rewrite (interval_unbounded_setT iX).
Qed.

Lemma connected_intervalP (E : set R) : connected E <-> is_interval E.
Proof.
split => [cE x y Ex Ey z /andP[xz zy]|].
- apply: contrapT => Ez.
  pose Az := E `&` [set x | x < z]; pose Bz := E `&` [set x | z < x].
  apply/connectedPn : cE; exists (fun b => if b then Az else Bz); split.
  + by case; [exists x | exists y].
  + rewrite /Az /Bz -setIUr; apply/esym/setIidPl => u Eu.
    by apply/orP; rewrite -neq_lt; apply/negP; apply: contraPnot Eu => /eqP <-.
  + split; [|rewrite setIC].
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_gt => zu.
      by rewrite /Az setCI; right; apply/negP; rewrite -leNgt.
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_lt => zu.
      by rewrite /Bz setCI; right; apply/negP; rewrite -leNgt.
- apply: contraPP => /connectedPn[A [A0 EU sepA]] intE.
  have [/= x A0x] := A0 false; have [/= y A1y] := A0 true.
  wlog xy : A A0 EU sepA x A0x y A1y / x < y.
    move=> /= wlog_hypo; have [xy|yx|{wlog_hypo}yx] := ltgtP x y.
    + exact: (wlog_hypo _ _ _ _ _ A0x _ A1y).
    + apply: (wlog_hypo (A \o negb) _ _ _ y _ x) => //=;
      by [rewrite setUC | rewrite separatedC].
    + move/separated_disjoint : sepA; rewrite predeqE => /(_ x)[] + _; apply.
      by split => //; rewrite yx.
  pose z := sup (A false `&` [set z | x <= z <= y]).
  have A1z : ~ (A true) z.
    have cA0z : closure (A false) z.
      suff : closure (A false `&` [set z | x <= z <= y]) z by case/closureI.
      apply: closure_sup; last by exists y => u [_] /andP[].
      by exists x; split => //; rewrite /mkset lexx /= (ltW xy).
    by move: sepA; rewrite /separated => -[] /disjoints_subset + _; apply.
  have /andP[xz zy] : x <= z < y.
    rewrite sup_ub //=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle sup_le_ub ?andbT; last by move=> u [_] /andP[].
      * by apply/negP; apply: contraPnot A1y => /eqP <-.
      * by exists x; split => //; rewrite /mkset /= lexx /= (ltW xy).
    + by split=> //; rewrite /mkset lexx (ltW xy).
  have [A0z|A0z] := pselect ((A false) z); last first.
    have {}xzy : x < z < y.
      by rewrite zy lt_neqAle xz !andbT; apply/eqP; apply: contra_not A0z => <-.
    have : ~ E z by rewrite EU => -[].
    by apply; apply (intE x y) => //; rewrite EU; [left|right].
  suff [z1 [/andP[zz1 z1y] Ez1]] : exists z1 : R, z < z1 < y /\ ~ E z1.
    apply Ez1; apply (intE x y) => //; rewrite ?EU; [by left|by right|].
    by rewrite z1y (le_lt_trans _ zz1).
  have [r zcA1] : {r:{posnum R}| ball z r%:num `<=` ~` closure (A true)}.
    have ? : ~ closure (A true) z.
      by move: sepA; rewrite /separated => -[] _ /disjoints_subset; apply.
    have ? : open (~` closure (A true)) by exact/openC/closed_closure.
    exact/nbhsC_ball/open_nbhs_nbhs.
  pose z1 : R := z + r%:num / 2; exists z1.
  have z1y : z1 < y.
    rewrite ltNge; apply/negP => yz1.
    suff : (~` closure (A true)) y by apply; exact: subset_closure.
    apply zcA1; rewrite /ball /= ltr_distl (lt_le_trans zy) // ?ler_addl //.
    rewrite andbT ltr_subl_addl addrC (le_lt_trans yz1) // ltr_add2l.
    by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  rewrite z1y andbT ltr_addl; split => //.
  have ncA1z1 : (~` closure (A true)) z1.
    apply zcA1; rewrite /ball /= /z1 opprD addrA subrr add0r normrN.
    by rewrite ger0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  have nA0z1 : ~ (A false) z1.
    move=> A0z1; have : z < z1 by rewrite /z1 ltr_addl.
    apply/negP; rewrite -leNgt; apply sup_ub; first by exists y => u [_] /andP[].
    by split => //; rewrite /mkset /z1 (le_trans xz) /= ?ler_addl // (ltW z1y).
  by rewrite EU => -[//|]; apply: contra_not ncA1z1; exact: subset_closure.
Qed.
End interval_realType.

Section segment.
Variable R : realType.

(** properties of segments in [R] *)

Lemma segment_connected (a b : R) : connected [set x : R | x \in `[a, b]].
Proof. exact/connected_intervalP/interval_is_interval. Qed.

Lemma segment_compact (a b : R) : compact [set x | x \in `[a, b]].
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
  by rewrite Aeab/= inE/=; apply/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite inE/=; apply/andP.
  exists a; split=> //; have /sabUf [i /= Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE inE => /eqP->.
  split; last by exists i => //=; rewrite inE.
  move=> x /= aex; exists i; [by rewrite /= inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [D' sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite inE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists D' => //; split; last by exists i => //; apply/xe_fi.
  move=> z /= ayz; case: (lerP z x) => [lezx|ltxz].
    by apply/saxUf; rewrite /= in_itv/= (itvP ayz) lezx.
  exists i => //; apply/xe_fi; rewrite /ball_/= distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltr_subl_addl; apply: le_lt_trans lezy _; rewrite -ltr_subl_addr.
    by have := xe_y; rewrite /ball_ => /ltr_distlC_subl.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: interval_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [D' sD [sayUf _]]] xe_y]] := nbhsx_ballx x e.
exists (i |` D')%fset; first by move=> j /fset1UP[->|/sD] //; rewrite inE.
split=> [z axz|]; last first.
  exists i; first by rewrite /= !inE eq_refl.
  by apply/xe_fi; rewrite /ball_/= subrr normr0.
case: (lerP z y) => [lezy|ltyz].
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite in_itv /= (itvP axz) lezy.
  by exists j => //=; rewrite inE orbC Dj.
exists i; first by rewrite /= !inE eq_refl.
apply/xe_fi; rewrite /ball_/= ger0_norm; last first.
  by rewrite subr_ge0 (itvP axz).
rewrite ltr_subl_addl -ltr_subl_addr; apply: lt_trans ltyz.
by apply: ltr_distlC_subl; rewrite distrC.
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

Lemma IVT (R : realType) (f : R -> R) (a b v : R) :
  a <= b -> {in `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab fcont; gen have ivt : f v fcont / f a <= v <= f b ->
    exists2 c, c \in `[a, b] & f c = v; last first.
  case: (leP (f a) (f b)) => [] _ fabv; first exact: ivt.
  have [||c cab /oppr_inj] := ivt (- f) (- v); last by exists c.
    by move=> x /fcont; apply: continuousN.
  by rewrite ler_oppr opprK ler_oppr opprK andbC.
move=> /andP[]; rewrite le_eqVlt => /orP [/eqP<- _|ltfav].
  by exists a => //; rewrite in_itv /= lexx leab.
rewrite le_eqVlt => /orP [/eqP->|ltvfb].
  by exists b => //; rewrite in_itv /= lexx leab.
set A := [set c | (c <= b) && (f c <= v)].
have An0 : nonempty A by exists a; apply/andP; split=> //; apply: ltW.
have supA : has_sup A by split=> //; exists b; apply/ubP => ? /andP [].
have supAab : sup A \in `[a, b].
  rewrite inE; apply/andP; split; last first.
    by apply: sup_le_ub => //; apply/ubP => ? /andP [].
  by move/ubP : (sup_upper_bound supA); apply; rewrite /A/= leab andTb ltW.
exists (sup A) => //; have lefsupv : f (sup A) <= v.
  rewrite leNgt; apply/negP => ltvfsup.
  have vltfsup : 0 < f (sup A) - v by rewrite subr_gt0.
  have /fcont /(_ _ (nbhsx_ballx _ (PosNum vltfsup))) [_/posnumP[d] supdfe]
    := supAab.
  have [t At supd_t] := sup_adherent supA [gt0 of d%:num].
  suff /supdfe : ball (sup A) d%:num t.
    rewrite /= /ball /= ltr_norml => /andP [_].
    by rewrite ltr_add2l ltr_oppr opprK ltNge; have /andP [_ ->] := At.
  rewrite /= /ball /= ger0_norm.
    by rewrite ltr_subl_addr -ltr_subl_addl.
  by rewrite subr_ge0; move/ubP : (sup_upper_bound supA); exact.
apply/eqP; rewrite eq_le; apply/andP; split=> //.
rewrite -subr_le0; apply/ler0_addgt0P => _/posnumP[e].
rewrite ler_subl_addr -ler_subl_addl ltW //.
have /fcont /(_ _ (nbhsx_ballx _ e)) [_/posnumP[d] supdfe] := supAab.
have atrF := at_right_proper_filter (sup A); near (at_right (sup A)) => x.
have /supdfe /= : ball (sup A) d%:num x.
  by near: x; rewrite /= nbhs_simpl; exists d%:num => //.
rewrite /= => /ltr_distlC_subl; apply: le_lt_trans.
rewrite ler_add2r ltW //; suff : forall t, t \in `](sup A), b] -> v < f t.
  apply; rewrite inE; apply/andP; split; first by near: x; exists 1.
  near: x; exists (b - sup A) => /=.
    rewrite subr_gt0 lt_def (itvP supAab) andbT; apply/negP => /eqP besup.
    by move: lefsupv; rewrite leNgt -besup ltvfb.
  move=> t lttb ltsupt; move: lttb; rewrite /= distrC.
  by rewrite gtr0_norm ?subr_gt0 // ltr_add2r; apply: ltW.
move=> t; rewrite in_itv /=; case/andP => ltsupt letb.
apply/contra_lt: ltsupt => leftv.
by move/ubP : (sup_upper_bound supA); apply; rewrite /A/= leftv letb.
Grab Existential Variables. all: end_near. Qed.

(** Local properties in [R] *)

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

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded_set A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  move=> p Ap; exists (floor `|p| + 1) => //.
  by rewrite rmorphD /= -RfloorE lt_succ_Rfloor.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite /= -subr_gt0 => ltpn.
  apply/nbhs_ballP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltr_subr_addr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_norm_add.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmax_real ?real0//; last by move=> ? _; rewrite realz.
split => // x ltmaxx p /DcovA [n Dn /lt_trans /(_ _)/ltW].
apply; apply: le_lt_trans ltmaxx.
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
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : product_topologicalType _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; split; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in [set x | 'I_n.+1 x]];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R]_n.+1) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R]_n.+1 | (forall i, (v ord0 i) \in `[(- (M + 1)), (M + 1)])].
  apply: (@rV_compact _  _ (fun _ => [set x | x \in `[(- (M + 1)), (M + 1)]])).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltr_addl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v ij.1 ij.2| | ij : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
rewrite [in X in _ <= X]/normr /= mx_normrE.
by apply/BigmaxBigminr.bigmaxr_gerP; right => /=; exists j.
Qed.

Lemma ereal_nbhs'_le (R : numFieldType) (x : \bar R) :
  ereal_nbhs' x --> ereal_nbhs x.
Proof.
move: x => [x P [_/posnumP[e] HP] |x P|x P] //=.
by exists e%:num => // ???; apply: HP.
Qed.

Lemma ereal_nbhs'_le_finite (R : numFieldType) (x : R) :
  ereal_nbhs' x%:E --> nbhs x%:E.
Proof.
by move=> P [_/posnumP[e] HP] //=; exists e%:num => // ???; apply: HP.
Qed.

Section open_closed_sets_ereal.
Variable R : realFieldType (* TODO: generalize to numFieldType? *).
Local Open Scope ereal_scope.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R | r%:E < y].
Proof.
case: y => [y||] /=; first exact: open_lt.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite lte_pinfty trueE.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set r : R | y < r%:E].
Proof.
case: y => [y||] /=; first exact: open_gt.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite lte_ninfty trueE.
Qed.

Lemma open_ereal_lt' x y : x < y -> ereal_nbhs x (fun u => u < y).
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
- case: y => [y||//] /= in xy *; last by exists 0%R.
  by exists y; rewrite num_real; split => //= x ?.
- case: y => [y||//] /= in xy *.
  + by exists y; rewrite num_real; split => //= x ?.
  + exists 0%R; rewrite real0; split => // x.
    by move/lt_le_trans; apply; rewrite lee_pinfty.
Qed.

Lemma open_ereal_gt' x y : y < x -> ereal_nbhs x (fun u => y < u).
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0; rewrite real0.
- by exists y; rewrite num_real.
- move=> _; exists 0%R; rewrite real0; split => // x.
  by apply/le_lt_trans; rewrite lee_ninfty.
Qed.

Let open_ereal_lt_real r : open (fun x => x < r%:E).
Proof.
case => [? | // | ?]; [rewrite lte_fin => xy | by exists r].
by move: (@open_ereal_lt r%:E); rewrite openE; apply; rewrite /= lte_fin.
Qed.

Lemma open_ereal_lt_ereal x : open [set y | y < x].
Proof.
case: x => [x | | [] // ] /=; first exact: open_ereal_lt_real.
suff -> : [set y | y < +oo] = \bigcup_r [set y : \bar R | y < r%:E].
  by apply open_bigU => x _; exact: open_ereal_lt_real.
rewrite predeqE => -[r | | ]/=.
- rewrite lte_pinfty; split => // _.
  by exists (r + 1)%R => //=; rewrite lte_fin ltr_addl.
- by rewrite ltxx; split => // -[] x /=; rewrite ltNge lee_pinfty.
- by split => // _; exists 0%R => //=; rewrite lte_ninfty.
Qed.

Let open_ereal_gt_real r : open (fun x => r%:E < x).
Proof.
case => [? | ? | //]; [rewrite lte_fin => xy | by exists r].
by move: (@open_ereal_gt r%:E); rewrite openE; apply; rewrite /= lte_fin.
Qed.

Lemma open_ereal_gt_ereal x : open [set y | x < y].
Proof.
case: x => [x | [] // | ] /=; first exact: open_ereal_gt_real.
suff -> : [set y | -oo < y] = \bigcup_r [set y : \bar R | r%:E < y].
  by apply open_bigU => x _; exact: open_ereal_gt_real.
rewrite predeqE => -[r | | ]/=.
- rewrite lte_ninfty; split => // _.
  by exists (r - 1)%R => //=; rewrite lte_fin ltr_subl_addr ltr_addl.
- by split => // _; exists 0%R => //=; rewrite lte_pinfty.
- by rewrite ltxx; split => // -[] x _ /=; rewrite ltNge lee_ninfty.
Qed.

Lemma closed_ereal_le_ereal y : closed [set x | y <= x].
Proof.
rewrite (_ : [set x | y <= x] = ~` [set x | y > x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal y : closed [set x | y >= x].
Proof.
rewrite (_ : [set x | y >= x] = ~` [set x | y < x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_gt_ereal.
Qed.

End open_closed_sets_ereal.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_ERFin (x : R) (X : set R) :
  nbhs x X -> nbhs x%:E ((fun r => r%:E) @` X).
Proof.
case => _/posnumP[e] xeX; exists e%:num => //= r xer.
by exists r => //; apply xeX.
Qed.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_pinfty r : nbhs +oo%E [set y | r%:E < y]%E.
Proof.
rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_pinfty].
Qed.

Lemma nbhs_open_ereal_ninfty r : nbhs -oo%E [set y | y < r%:E]%E.
Proof.
rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_ninfty].
Qed.

Lemma ereal_hausdorff : hausdorff (ereal_topologicalType R).
Proof.
move=> -[r| |] // [r' | |] //=.
- move=> rr'; congr (_%:E); apply Rhausdorff => /= A B rA r'B.
  have [/= z [[r0 ? r0z] [r1 ?]]] :=
    rr' _ _ (nbhs_image_ERFin rA) (nbhs_image_ERFin r'B).
  by rewrite -r0z => -[r1r0]; exists r0; split => //; rewrite -r1r0.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r : r < r + 1.
    by rewrite ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_pinfty (r + 1))) => -[z [zr rz]].
  by move: (lt_trans rz zr); rewrite lte_fin ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) loc_r : r - 1 < r.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_ninfty (r - 1))) => -[z [rz zr]].
  by move: (lt_trans zr rz); rewrite ltxx.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r' : r' < r' + 1.
    by rewrite ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_pinfty (r' + 1)) loc_r') => -[z [r'z zr']].
  by move: (lt_trans zr' r'z); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_pinfty 0) (nbhs_open_ereal_ninfty 0)).
  by move=> -[z [zx xz]]; move: (lt_trans xz zx); rewrite ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) yB : r' - 1 < r'.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_ninfty (r' - 1)) yB) => -[z [zr' r'z]].
  by move: (lt_trans r'z zr'); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_ninfty 0) (nbhs_open_ereal_pinfty 0)).
  by move=> -[z [zO Oz]]; move: (lt_trans Oz zO); rewrite ltxx.
Qed.

End ereal_is_hausdorff.

Hint Extern 0 (hausdorff _) => solve[apply: ereal_hausdorff] : core.

(** * Some limits on real functions *)

Lemma continuous_withinNx (R : numFieldType) {U V : pseudoMetricType R}
  (f : U -> V) x :
  {for x, continuous f} <-> f @ nbhs' x --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /nbhs' !near_simpl near_withinE.
  by apply: cvg_within; apply: cfx.
rewrite !nbhs_nearE !near_map !near_nbhs in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Grab Existential Variables. all: end_near. Qed.

Section Closed_Ball.

Lemma ball_open (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open (ball x r).
Proof.
rewrite openE -ball_normE /interior => r0 y /= Bxy; near=> z.
rewrite /= (le_lt_trans (ler_dist_add y _ _)) // addrC -ltr_subr_addr.
by near: z; apply: cvg_dist; rewrite // subr_gt0.
Grab Existential Variables. all: end_near. Qed.

Definition closed_ball_ (R : numDomainType) (V : zmodType) (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

Lemma closed_closed_ball_ (R : realFieldType) (V : normedModType R)
  (x : V) (e : R) : closed (closed_ball_ normr x e).
Proof.
rewrite /closed_ball_ -/((normr \o (fun y => x - y)) @^-1` [set x | x <= e]).
apply: (closed_comp _ (@closed_le _ _)) => y _.
apply: (continuous_comp _ (@norm_continuous _ _ _)).
exact: (continuousB (@cst_continuous _ _ _ _)).
Qed.

Definition closed_ball (R : numDomainType) (V : pseudoMetricType R)
  (x : V) (e : R) := closure (ball x e).

Lemma closed_ballxx (R: numDomainType) (V : pseudoMetricType R) (x : V)
  (e : R) : 0 < e -> closed_ball x e x.
Proof. by move=> ?; exact/subset_closure/ballxx. Qed.

Lemma closed_ballE (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed_ball x r = closed_ball_ normr x r.
Proof.
move=> /posnumP[e]; rewrite eqEsubset; split => y.
  rewrite /closed_ball closureE; apply; split; first exact: closed_closed_ball_.
  by move=> z; rewrite -ball_normE; exact: ltW.
have [/eqP -> _|xy] := boolP (x == y); first exact: closed_ballxx.
rewrite /closed_ball closureE -ball_normE.
rewrite /closed_ball_ /= le_eqVlt.
move => /orP [/eqP xye B [Bc Be]|xye _ [_ /(_ _ xye)]//].
apply: Bc => B0 /nbhs_ballP[s s0] B0y.
have [es|se] := leP s e%:num; last first.
  exists x; split; first by apply: Be; rewrite ball_normE; apply: ballxx.
  by apply: B0y; rewrite -ball_normE /ball_ /= distrC xye.
exists (y + (s / 2) *: (`|x - y|^-1 *: (x - y))); split; [apply: Be|apply: B0y].
  rewrite /= opprD addrA -[X in `|X - _|](scale1r (x - y)) scalerA -scalerBl.
  rewrite -[X in X - _](@divrr _ `|x - y|) ?unitfE ?normr_eq0 ?subr_eq0//.
  rewrite -mulrBl -scalerA normmZ normrZV ?subr_eq0// mulr1.
  rewrite gtr0_norm; first by rewrite ltr_subl_addl xye ltr_addr mulr_gt0.
  by rewrite subr_gt0 xye ltr_pdivr_mulr // mulr_natr mulr2n ltr_spaddl.
rewrite -ball_normE /ball_ /= opprD addrA addrN add0r normrN normmZ.
rewrite normrZV ?subr_eq0// mulr1 normrM (gtr0_norm s0) gtr0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
Qed.

Lemma closed_ball_closed (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed (closed_ball x r).
Proof. by move => r0; rewrite closed_ballE //; exact: closed_closed_ball_. Qed.

Lemma closed_ball_subset (R : realFieldType) (M : normedModType R) (x : M)
  (r0 r1 : R) : 0 < r0 -> r0 < r1 -> closed_ball x r0 `<=` ball x r1.
Proof.
move=> r00 r01; rewrite (_ : r0 = (PosNum r00)%:num) // closed_ballE //.
by move=> m xm; rewrite -ball_normE /ball_ /= (le_lt_trans _ r01).
Qed.

Lemma nbhs_closedballP (R : realFieldType) (M : normedModType R) (B : set M)
  (x : M) : nbhs x B <-> exists (r : {posnum R}), closed_ball x r%:num `<=` B.
Proof.
split=> [/nbhs_ballP[r r0 xrB]|[e xeB]]; last first.
  apply/nbhs_ballP; exists e%:num => //.
  exact: (subset_trans (@subset_closure _ _) xeB).
have r20 : 0 < r / 2 by apply divr_gt0.
exists (PosNum r20); apply: (subset_trans (closed_ball_subset _ _) xrB) => //=.
by rewrite lter_pdivr_mulr // ltr_pmulr // ltr1n.
Qed.

Lemma subset_closed_ball (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> ball x r `<=` closed_ball x r.
Proof. move=> r0; rewrite /closed_ball; apply: subset_closure. Qed.

(*TBA topology.v once ball_normE is there*)

Lemma nbhs0_lt (K : numFieldType) (V : normedModType K) e :
  0 < e -> \forall x \near nbhs (0 : V), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma nbhs'0_lt (K : numFieldType) (V : normedModType K) e :
  0 < e -> \forall x \near nbhs' (0 : V), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma nbhs0_le (K : numFieldType) (V : normedModType K) e :
  0 < e -> \forall x \near nbhs (0 : V), `|x| <= e.
Proof.
by move => e_gt0; near=> x; apply: ltW; near: x; apply: nbhs0_lt.
Grab Existential Variables. all: end_near. Qed.

Lemma nbhs'0_le (K : numFieldType) (V : normedModType K) e :
  0 < e -> \forall x \near nbhs' (0 : V), `|x| <= e.
Proof.
by move => e_gt0; near=> x; apply: ltW; near: x; apply: nbhs'0_lt.
Grab Existential Variables. all: end_near. Qed.


Lemma interior_closed_ballE (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> (closed_ball x r)^° = ball x r.
Proof.
move=> r0; rewrite eqEsubset; split; last first.
  by rewrite -open_subsetE; [exact: subset_closure | exact: ball_open].
move=> /= t; rewrite closed_ballE // /interior /= -nbhs_ballE => [[]] s s0.
have [/eqP -> _|nxt] := boolP (t == x); first exact: ballxx.
near (nbhs' (0 : R^o)) => e; rewrite -ball_normE /closed_ball_ => tsxr.
pose z := t + `|e| *: (t - x); have /tsxr /= : `|t - z| < s.
  rewrite distrC addrAC subrr add0r normmZ normr_id.
  rewrite -ltr_pdivl_mulr ?(normr_gt0,subr_eq0) //.
  by near: e; apply/nbhs'0_lt; rewrite divr_gt0 // normr_gt0 subr_eq0.
rewrite /z opprD addrA -scalerN -{1}(scale1r (x - t)) opprB -scalerDl normmZ.
apply lt_le_trans; rewrite ltr_pmull; last by rewrite normr_gt0 subr_eq0 eq_sym.
by rewrite ger0_norm // ltr_addl normr_gt0 //; near: e; exists 1.
Grab Existential Variables. all: end_near. Qed.

Lemma open_nbhs_closed_ball (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> open_nbhs x (closed_ball x r)^°.
Proof.
move=> r0; split; first exact: open_interior.
by rewrite interior_closed_ballE //; exact: ballxx.
Qed.

End Closed_Ball.

Section LinearContinuousBounded.

Variables (R : numFieldType) (V W : normedModType R).

Lemma linear_boundedP (f : {linear V -> W}) : bounded_near f (nbhs (0 : V)) <->
  \forall r \near +oo, forall x, `|f x| <= r * `|x|.
Proof.
split=> [|/pinfty_ex_gt0 [r r0 Bf]]; last first.
  apply/ex_bound; exists r; apply/nbhs_ballP; exists 1 => // x.
  rewrite -ball_normE //= sub0r normrN -(gtr_pmulr _ r0) => /ltW.
  exact/le_trans/Bf.
rewrite /bounded_near => /pinfty_ex_gt0 [M M0 /nbhs_ballP [_/posnumP[e] efM]].
near (nbhs' 0 : set (set R^o)) => y; near=> r => x.
have [->|x0] := eqVneq x 0; first by rewrite linear0 !normr0 mulr0.
rewrite -ler_pdivr_mulr ?normr_gt0// -[ `|x|]normr_id mulrC.
have y_gt0 : 0 < `|y| by rewrite normr_gt0; near: y; exists 1.
rewrite -(ler_pmul2l y_gt0) -normfV -!normmZ scalerA -linearZ.
rewrite (le_trans (efM _ _)) //; last first.
  rewrite -ler_pdivr_mull //; near: r; apply: nbhs_pinfty_ge_real.
  by rewrite rpredM// ?ger0_real ?invr_ge0// ltW.
rewrite -ball_normE/= sub0r normrN normmZ normrM normfV //.
rewrite normr_id -mulrA mulVf ?normr_eq0 // mulr1; near: y.
by apply/nbhs_ballP; exists e%:num=> // z; rewrite -ball_normE /= sub0r normrN.
Grab Existential Variables. all: end_near. Qed.

Lemma linear_continuous0 (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs (0 : V)).
Proof.
move=> /cvg_ballP/(_ _ ltr01); rewrite linear0 nearE => /nbhs_ex[e ef1].
apply/linear_boundedP; near=> d; move=> x.
have [->|x0] := eqVneq x 0; first by rewrite linear0 !normr0 mulr0.
have d0 : 0 < d.
  by near: d; exists 1; rewrite real1; split => // r; apply le_lt_trans.
pose dx := d * `|x|; have dx0 : 0 < dx by rewrite mulr_gt0 // normr_gt0.
suff : `| f (dx^-1 *: x) | < 1.
  rewrite linearZ normmZ normfV ?gt_eqF //.
  by rewrite ltr_pdivr_mull ?(normr_gt0,gt_eqF)// mulr1 gtr0_norm// => /ltW.
suff /ef1 : ball 0 e%:num (dx^-1 *: x) by rewrite -ball_normE /= sub0r normrN.
rewrite -ball_normE /ball_ /= sub0r normrN normmZ normfV ?gt_eqF //.
rewrite normrM normr_id (gtr0_norm d0) invfM ?(normr_eq0,gt_eqF)//.
rewrite mulrAC -mulrA mulfV ?normr_eq0 // mulr1 -div1r ltr_pdivr_mulr //.
near: d; exists e%:num^-1; rewrite realE invr_ge0 posnum_ge0; split => // r.
by rewrite -ltr_pdivr_mull ?mulr1.
Grab Existential Variables. by end_near. Qed.

Lemma linear_bounded0 (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) -> {for 0, continuous f}.
Proof.
move=> /linear_boundedP [y [yreal fr]]; near (@pinfty_nbhs R) => r.
have r0  : 0 < r.
  by near: r; exists 1; rewrite real1; split => // z; apply le_lt_trans.
apply/cvg_ballP => _/posnumP[e]; rewrite nearE linear0 /= nbhs_ballP.
exists (e%:num / 2 / r); first by rewrite /= divr_gt0.
move=> x; rewrite -2!ball_normE /= 2!sub0r 2!normrN => xer.
rewrite (@le_lt_trans _ _ (e%:num / 2)) //; last first.
  by rewrite gtr_pmulr // invf_lt1 // ltr1n.
move: xer; rewrite ltr_pdivl_mulr // => /ltW; apply le_trans.
rewrite mulrC; apply fr; near: r; exists (y + 1) => //.
by rewrite realD ?real1 //; split => // z; apply le_lt_trans; rewrite ler_addl.
Grab Existential Variables. by end_near. Qed.

Lemma continuousfor0_continuous (f : {linear V -> W}) :
  {for 0, continuous f} -> continuous f.
Proof.
move=> /linear_continuous0 /linear_boundedP [y [yreal fr]].
near (@pinfty_nbhs R) => r.
have r0  : 0 < r.
  by near: r; exists 1; rewrite real1; split => // z; apply le_lt_trans.
move=> x; apply/cvg_ballP => _/posnumP[e]; rewrite nearE /= nbhs_ballP.
exists (e%:num / r); first by rewrite /= divr_gt0.
move=> z; rewrite -!ball_normE //= => xy; rewrite -linearB.
move: xy; rewrite ltr_pdivl_mulr //; apply le_lt_trans.
rewrite mulrC; apply fr.
near: r; exists (y + 1); rewrite realD // ?real1 //; split => // x.
by apply le_lt_trans; rewrite ler_addl.
Grab Existential Variables. by end_near. Qed.

Lemma linear_bounded_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) <-> continuous f.
Proof.
split=> [/linear_bounded0|/(_ 0)/linear_continuous0//].
exact: continuousfor0_continuous.
Qed.

Lemma bounded_funP (f : {linear V -> W}) :
  (forall r, exists M, forall x, `|x| <= r -> `|f x| <= M) <->
  bounded_near f (nbhs (0 : V)).
Proof.
split => [/(_ 1) [M Bf]|/linear_boundedP fr y].
  apply/ex_bound; exists M; apply/nbhs_ballP; exists 1 => // x.
  by rewrite -ball_normE /ball_ /= sub0r normrN => x1; exact/Bf/ltW.
near (@pinfty_nbhs R) => r; exists (y * r) => x xe.
rewrite mulrC (@le_trans _ _ (r * `|x|)) //; first by move: {xe} x; near: r.
rewrite ler_pmul //; near: r; exists 1.
by rewrite real1; split => // x /ltW; apply le_trans.
Grab Existential Variables. by end_near. Qed.

End LinearContinuousBounded.
