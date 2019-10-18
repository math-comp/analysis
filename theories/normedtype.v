(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology.

(******************************************************************************)
(* This file extends the topological hierarchy with norm-related notions.     *)
(*                                                                            *)
(* * Rings with absolute value :                                              *)
(*                    absRingType == interface type for a ring with absolute  *)
(*                                   value structure.                         *)
(*     AbsRingMixin abs0 absN1 absD absM abseq0 == builds the mixin for a     *)
(*                                   ring with absolute value from the        *)
(*                                   algebraic properties of the absolute     *)
(*                                   value; the carrier type must have a      *)
(*                                   ringType structure.                      *)
(*      [absRingType of T for cT] == T-clone of the absRingType structure cT. *)
(*             [absRingType of T] == clone of a canonical absRingType         *)
(*                                   structure on T.                          *)
(*                           `|x| == the absolute value of x.                 *)
(*                        ball_ N == balls defined by the norm/absolute value *)
(*                                   N.                                       *)
(*                   locally_dist == neighbourhoods defined by a "distance"   *)
(*                                   function                                 *)
(*                                                                            *)
(* * Normed modules :                                                         *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the ring with absolute    *)
(*                                   value K.                                 *)
(*     NormedModMixin normD normZ balln normeq0 == builds the mixin for a     *)
(*                                   normed module from the algebraic         *)
(*                                   properties of the norm and the           *)
(*                                   compatibility between the norm and       *)
(*                                   balls; the carrier type must have a      *)
(*                                   lmodType K structure for K an            *)
(*                                   absRingType.                             *)
(*            NormedModType K T m == packs the mixin m to build a             *)
(*                                   normedModType K; T must have canonical   *)
(*                                   lmodType K and uniformType structures.   *)
(*  [normedModType K of T for cT] == T-clone of the normedModType K structure *)
(*                                   cT.                                      *)
(*         [normedModType K of T] == clone of a canonical normedModType K     *)
(*                                   structure on T.                          *)
(*                         `|[x]| == the norm of x.                           *)
(*                      ball_norm == balls defined by the norm.               *)
(*                   locally_norm == neighbourhoods defined by the norm.      *)
(*                        bounded == set of bounded sets.                     *)
(*                                                                            *)
(* * Complete normed modules :                                                *)
(*        completeNormedModType K == interface type for a complete normed     *)
(*                                   module structure over the ring with      *)
(*                                   absolute value K.                        *)
(* [completeNormedModType K of T] == clone of a canonical complete normed     *)
(*                                   module structure over K on T.            *)
(*                                                                            *)
(* * Filters :                                                                *)
(*          at_left x, at_right x == filters on real numbers for predicates   *)
(*                                   that locally hold on the left/right of   *)
(*                                   x.                                       *)
(*                Rbar_locally' x == filter on extended real numbers that     *)
(*                                   corresponds to locally' x if x is a real *)
(*                                   number and to predicates that are        *)
(*                                   eventually true if x is +oo/-oo.         *)
(*                 Rbar_locally x == same as Rbar_locally' where locally' is  *)
(*                                   replaced with locally.                   *)
(*                 Rbar_loc_seq x == sequence that converges to x in the set  *)
(*                                   of extended real numbers.                *)
(*                                                                            *)
(* --> We used these definitions to prove the intermediate value theorem and  *)
(*     the Heine-Borel theorem, which states that the compact sets of R^n are *)
(*     the closed and bounded sets.                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Def Order.Syntax GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(*Module AbsRing.

Record mixin_of (D : ringType) := Mixin {
  abs : D -> R;
  ax1 : abs 0 = 0 ;
  ax2 : abs (- 1) = 1 ;
  ax3 : forall x y : D, abs (x + y) <= abs x + abs y ;
  ax4 : forall x y : D, abs (x * y) = abs x * abs y ;
  ax5 : forall x : D, abs x = 0 -> x = 0
}.

Section ClassDef.

Record class_of (K : Type) := Class {
  base : Num.NumDomain.class_of K ;
  mixin : mixin_of (Num.NumDomain.Pack base)
}.
Local Coercion base : class_of >-> Num.NumDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : mixin_of (@Num.NumDomain.Pack T b0)) :=
  fun bT b & phant_id (Num.NumDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @Num.NumDomain.Pack cT xclass.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Num.NumDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Notation AbsRingMixin := Mixin.
Notation AbsRingType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'absRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'absRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'absRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'absRingType'  'of'  T ]") : form_scope.
Notation absRingType := type.

End Exports.

End AbsRing.

Export AbsRing.Exports.

Definition abs {K : absRingType} : K -> R := @AbsRing.abs _ (AbsRing.class K).

Section AbsRing1.

Local Notation "`| x |" := (abs x%R) : R_scope.
Local Notation "`| x |" := (abs x%R) : real_scope.

Context {K : absRingType}.
Implicit Types x : K.

Lemma absr0 : `|0 : K| = 0. Proof. exact: AbsRing.ax1. Qed.

Lemma absrN1: `|- 1 : K| = 1.
Proof. exact: AbsRing.ax2. Qed.

Lemma ler_abs_add (x y : K) :  `|x + y| <= `|x|%real + `|y|%real.
Proof. exact: AbsRing.ax3. Qed.

Lemma absrM (x y : K) : `|x * y| = `|x|%real * `|y|%real.
Proof. exact: AbsRing.ax4. Qed.

Lemma absr0_eq0 (x : K) : `|x| = 0 -> x = 0.
Proof. exact: AbsRing.ax5. Qed.

Lemma absrN x : `|- x| = `|x|.
Proof.
gen have le_absN1 : x / `|- x| <= `|x|.
  by rewrite -mulN1r absrM absrN1 mul1r.
by apply/eqP; rewrite eq_le le_absN1 /= -{1}[x]opprK le_absN1.
Qed.

Lemma absrB (x y : K) : `|x - y| = `|y - x|.
Proof. by rewrite -absrN opprB. Qed.

Lemma absr1 : `|1 : K| = 1. Proof. by rewrite -absrN absrN1. Qed.

Lemma absr_ge0 x : 0 <= `|x|.
Proof.
rewrite -(@pmulr_rge0 _ 2) // mulr2n mulrDl !mul1r.
by rewrite -{2}absrN (le_trans _ (ler_abs_add _ _)) // subrr absr0.
Qed.

Lemma absr_eq0 x : (`|x| == 0) = (x == 0).
Proof. by apply/eqP/eqP=> [/absr0_eq0//|->]; rewrite absr0. Qed.

Lemma absr1_gt0 : `|1 : K| > 0.
Proof. by rewrite lt_def absr1 oner_eq0 /=. Qed.

Lemma absrX x n : `|x ^+ n| <= `|x|%real ^+ n.
Proof.
elim: n => [|n IH]; first  by rewrite !expr0 absr1.
by rewrite !exprS absrM ler_pmul // absr_ge0.
Qed.

End AbsRing1.
Hint Resolve absr_ge0 : core.
Hint Resolve absr1_gt0 : core.
*)
Definition ball_ (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V)
  (e : R) := [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%R y /.

(* :TODO: to math-comp *)
Lemma subr_trans (M : zmodType) (z x y : M) : x - y = (x - z) + (z - y).
Proof. by rewrite addrA addrNK. Qed.

(*Section AbsRing_UniformSpace.

Context {K : absRingType}.

Definition AbsRing_ball := ball_ (@abs K).

Lemma AbsRing_ball_center (x : K) (e : R) : 0 < e -> AbsRing_ball x e x.
Proof. by rewrite /AbsRing_ball /= subrr absr0. Qed.

Lemma AbsRing_ball_sym (x y : K) (e : R) :
  AbsRing_ball x e y -> AbsRing_ball y e x.
Proof. by rewrite /AbsRing_ball /= absrB. Qed.

Lemma AbsRing_ball_triangle (x y z : K) (e1 e2 : R) :
  AbsRing_ball x e1 y -> AbsRing_ball y e2 z -> AbsRing_ball x (e1 + e2) z.
Proof.
rewrite /AbsRing_ball /= => xy yz.
by rewrite (subr_trans y) (le_lt_trans (ler_abs_add _ _)) ?ltr_add.
Qed.

Definition AbsRingUniformMixin :=
  UniformMixin AbsRing_ball_center AbsRing_ball_sym AbsRing_ball_triangle erefl.

End AbsRing_UniformSpace.

(* :TODO: DANGEROUS ! Must change this to include uniform type et al inside absring *)
Coercion absRing_pointedType (K : absRingType) := PointedType K 0.
Canonical absRing_pointedType.
Coercion absRing_filteredType (K : absRingType) :=
   FilteredType K K (locally_ AbsRing_ball).
Canonical absRing_filteredType.
Coercion absRing_topologicalType (K : absRingType) :=
  TopologicalType K (topologyOfBallMixin AbsRingUniformMixin).
Canonical absRing_topologicalType.
Coercion absRing_UniformType (K : absRingType) := UniformType K AbsRingUniformMixin.
Canonical absRing_UniformType.

Lemma ball_absE (K : absRingType) : ball = ball_ (@abs K).
Proof. by []. Qed.
*)

Definition pointed_of_zmodule (R : zmodType) : pointedType := PointedType R 0.

Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R := Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R)) (locally_ (ball_ (fun x => `|x|)))).

Section uniform_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : (0%R < e)%O -> ball_ normr x e x.
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
Definition uniform_of_normedDomain
  : Uniform.mixin_of K (@locally_ K R R (ball_ (fun x => `|x|)))
  := UniformMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl.
End uniform_of_normedDomain.

Section realFieldType_canonical.
Variable R : realFieldType.
(*Canonical topological_of_realFieldType := [realFieldType of R^o].*)
Canonical realFieldType_pointedType :=
  [pointedType of R^o for pointed_of_zmodule R].
Canonical realFieldType_filteredType :=
  [filteredType R of R^o for filtered_of_normedZmod R].
Canonical realFieldType_topologicalType : topologicalType := TopologicalType R^o
  (topologyOfBallMixin (uniform_of_normedDomain [normedZmodType R of R])).
Canonical realFieldType_uniformType := @Uniform.Pack R R^o (@Uniform.Class R R
  (Topological.class realFieldType_topologicalType) (@uniform_of_normedDomain R R)).
End realFieldType_canonical.

Lemma locallyN (R : realFieldType) (x : R^o) :
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

Lemma openN (R : realFieldType) (A : set R^o) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior locallyN; exists A.
Qed.

Lemma closedN (R : realFieldType) (A : set R^o) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK locallyN; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

(** real numbers *)

Module UniformNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (loc : T -> set (set T))
    (m : Uniform.mixin_of R loc) := Mixin {
  _ : Uniform.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  locally_mixin : Filtered.locally_of T T ;
  topological_mixin : @Topological.mixin_of T locally_mixin ;
  uniform_mixin : @Uniform.mixin_of R T locally_mixin ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ uniform_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.
Definition base2 T c := @Uniform.Class _ _
    (@Topological.Class _
      (Filtered.Class
       (Pointed.Class (@base T c) (pointed_mixin c))
       (locally_mixin c))
      (topological_mixin c))
    (uniform_mixin c).
Local Coercion base2 : class_of >-> Uniform.class_of.
(* TODO: base3? *)

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0 (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : Uniform.class_of R T) & phant_id (@Uniform.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack xT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack R cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition uniform_zmodType := @GRing.Zmodule.Pack uniformType xclass.
Definition pointed_normedZmodType := @Num.NormedZmodule.Pack R phR pointedType xclass.
Definition filtered_normedZmodType := @Num.NormedZmodule.Pack R phR filteredType xclass.
Definition topological_normedZmodType := @Num.NormedZmodule.Pack R phR topologicalType xclass.
Definition uniform_normedZmodType := @Num.NormedZmodule.Pack R phR uniformType xclass.

End ClassDef.

(*Definition numDomain_normedDomainType (R : numDomainType) : type (Phant R) :=
  Pack (Phant R) (@Class R _ _ (NumDomain.normed_mixin (NumDomain.class R))).*)

Module Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion base2 : class_of >-> Uniform.class_of.
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
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical uniform_zmodType.
Canonical pointed_normedZmodType.
Canonical filtered_normedZmodType.
Canonical topological_normedZmodType.
Canonical uniform_normedZmodType.
Notation uniformNormedZmoduleType R := (type (Phant R)).
Notation UniformNormedZmoduleType R T m := (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
Notation "[ 'uniformNormedZmoduleType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'uniformNormedZmoduleType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'uniformNormedZmoduleType' R 'of' T ]" :=
  (@clone _ (Phant R) T _ _ idfun)
  (at level 0, format "[ 'uniformNormedZmoduleType'  R  'of'  T ]") : form_scope.
End Exports.

End UniformNormedZmodule.
Export UniformNormedZmodule.Exports.

Canonical R_pointedType := [pointedType of
  Rdefinitions.R for pointed_of_zmodule R_ringType].
(* NB: similar definition in topology.v *)
Canonical R_filteredType := [filteredType Rdefinitions.R of
  Rdefinitions.R for filtered_of_normedZmod R_normedZmodType].
Canonical R_topologicalType : topologicalType := TopologicalType Rdefinitions.R
  (topologyOfBallMixin (uniform_of_normedDomain R_normedZmodType)).
Canonical R_uniformType : uniformType R_numDomainType :=
  UniformType Rdefinitions.R (uniform_of_normedDomain R_normedZmodType).

Section realFieldType_canonical_contd.
Variable R : realFieldType.
Lemma R_ball : @ball _ [uniformType R of R^o] = ball_ (fun x => `| x |).
Proof. by []. Qed.
Definition realFieldType_uniformNormedZmodMixin := UniformNormedZmodule.Mixin R_ball.
Canonical realFieldType_uniformNormedZmodType := @UniformNormedZmoduleType R R^o realFieldType_uniformNormedZmodMixin.
End realFieldType_canonical_contd.

(*TODO: create a Definition that creates, given a ring structure, a
pointed type with 0 as a default element and a Definition that creates,
locally open ball and all the proofs from normedDomainType and then
use to create R_pointedType, etc.*)

(*
TODO
Canonical R_uniformNormedZmoduleType := [uniformNormedZmoduleType Rdefinitions.R of Rdefinitions.R].
*)

(** locally *)

Section Locally.
Context {R : realFieldType} {T : uniformType R}.

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

End Locally.

Lemma ler_addgt0Pr (R : realFieldType) (x y : R) :
  reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy _/posnumP[e] | lexye]; first by rewrite ler_paddr.
case: (lerP x y) => // ltyx.
have /midf_lt [_] := ltyx; rewrite ltNge -eqbF_neg => /eqP<-.
suff -> : (y + x) / 2 = y + (x - y) / 2.
  by apply/lexye/divr_gt0 => //; rewrite subr_gt0.
by rewrite !mulrDl addrC -mulN1r -mulrA mulN1r [RHS]addrC {3}(splitr y)
  [RHS]GRing.subrKA.
Qed.

Lemma ler_addgt0Pl (R : realFieldType) (x y : R) :
  reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma in_segment_addgt0Pr (R : realFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(x - e), (z + e)]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz _/posnumP[e] | xyz_e].
  rewrite inE/=; apply/andP; split; last by rewrite ler_paddr // (itvP xyz).
  by rewrite ler_subl_addr ler_paddr // (itvP xyz).
rewrite inE/=; apply/andP.
by split; apply/ler_addgt0Pr => ? /xyz_e /andP /= []; rewrite ler_subl_addr.
Qed.

Lemma in_segment_addgt0Pl (R : realFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

(*Lemma absRE (x : R) : `|x|%real = `|x|%R.
Proof. by []. Qed.*)

Lemma coord_continuous {K : realFieldType} m n i j :
  continuous (fun M : 'M[[filteredType _ of K^o]]_(m.+1, n.+1) => M i j).
Proof.
move=> /= M s /= /(@locallyP _ _ (M i j)); rewrite locally_E => -[e e0 es].
apply/locallyP; rewrite locally_E; exists e => //= N MN; exact/es/MN.
Qed.

(** * Some Topology on [Rbar] *)

(* NB: already defined in R_scope in Rbar.v *)
(* TODO: factor *)
Notation "'+oo'" := (@ERPInf _) : real_scope.
Notation "'-oo'" := (@ERNInf _) : real_scope.
Section rbar.
Context {R : realType}.
Let R_topologicalType := [topologicalType of R^o].
Definition Rbar_locally' (a : {ereal R}) (P : R -> Prop) :=
  match a with
    | ERFin a => @locally' R_topologicalType a P
    | +oo => exists M, forall x, (M < x)%O -> P x
    | -oo => exists M, forall x, (x < M)%O -> P x
  end.
Definition Rbar_locally (a : {ereal R}) (P : R -> Prop) :=
  match a with
    | ERFin a => @locally _ R_topologicalType a P
    | +oo => exists M, forall x, (M < x)%O -> P x
    | -oo => exists M, forall x, (x < M)%O -> P x
  end.

(*Canonical Rbar_choiceType := ChoiceType Rbar gen_choiceMixin.*)
Canonical Rbar_pointed := PointedType {ereal R} (+oo).
Canonical Rbar_filter := FilteredType R {ereal R} (Rbar_locally).

Global Instance Rlocally'_proper (x : R) : ProperFilter (@locally' R_topologicalType x).
Proof.
apply: Build_ProperFilter => A [_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /= opprD addrA subrr distrC subr0 ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_spaddl.
Qed.

Global Instance Rbar_locally'_filter : forall x, ProperFilter (Rbar_locally' x).
Proof.
case=> [x||]; first exact: Rlocally'_proper.
  apply Build_ProperFilter.
    by move=> P [M gtMP]; exists (M + 1); apply: gtMP; rewrite ltr_addl.
  split=> /= [|P Q [MP gtMP] [MQ gtMQ] |P Q sPQ [M gtMP]]; first by exists 0.
    by exists (maxr MP MQ) => ?; rewrite ltUx => /andP [/gtMP ? /gtMQ].
  by exists M => ? /gtMP /sPQ.
apply Build_ProperFilter.
  by move=> P [M ltMP]; exists (M - 1); apply: ltMP; rewrite gtr_addl oppr_lt0.
split=> /= [|P Q [MP ltMP] [MQ ltMQ] |P Q sPQ [M ltMP]]; first by exists 0.
  by exists (minr MP MQ) => ?; rewrite ltxI => /andP [/ltMP ? /ltMQ].
by exists M => ? /ltMP /sPQ.
Qed.
Typeclasses Opaque Rbar_locally'.

Global Instance Rbar_locally_filter : forall x, ProperFilter (Rbar_locally x).
Proof.
case=> [x||].
by apply/(@locally_filter R_topologicalType).
exact: (Rbar_locally'_filter +oo).
exact: (Rbar_locally'_filter -oo).
Qed.
Typeclasses Opaque Rbar_locally.

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
by move=> [M AM]; exists (M * 2) => x; rewrite -ltr_pdivl_mulr //; apply: AM.
Qed.

Lemma locally_pinfty_gt (c : R) : \forall x \near +oo, c < x.
Proof. by exists c. Qed.

Lemma locally_pinfty_ge c : \forall x \near +oo, c <= x.
Proof. by exists c; apply: ltW. Qed.

Hint Extern 0 (is_true (0 < _)) => match goal with
  H : ?x \is_near (locally +oo) |- _ =>
    solve[near: x; exists 0 => _/posnumP[x] //] end : core.

End rbar.

(** ** Modules with a norm *)

(*Reserved Notation  "`|[ x ]|" (at level 0, x at level 99, format "`|[ x ]|").*)

Module NormedModule.

Record mixin_of (K : numDomainType)
  (V : uniformNormedZmoduleType K) (scale : K -> V -> V) := Mixin {
  _ : forall (l : K) (x : V), `| scale l x | = `| l | * `| x |;
}.

Section ClassDef.

Variable K : numDomainType.

(* joint of normedDomainType and Lmodule *)
Record class_of (T : Type) := Class {
  base : UniformNormedZmodule.class_of K T ;
  lmodmixin : GRing.Lmodule.mixin_of K (GRing.Zmodule.Pack base) ;
  mixin : @mixin_of K (UniformNormedZmodule.Pack (Phant K) base)
                      (GRing.Lmodule.scale lmodmixin)
}.
Local Coercion base : class_of >-> UniformNormedZmodule.class_of.
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
                (m0 : @mixin_of K (@UniformNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@UniformNormedZmodule.class K (Phant K) bT) b =>
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
Definition uniformType := @Uniform.Pack K cT xclass.
Definition uniformNormedZmodType := @UniformNormedZmodule.Pack K phK cT xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition uniform_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass.
Definition normedZmod_lmodType := @GRing.Lmodule.Pack K phK normedZmodType xclass.
Definition uniformNormedZmod_lmodType := @GRing.Lmodule.Pack K phK uniformNormedZmodType xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> UniformNormedZmodule.class_of.
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
Coercion uniformNormedZmodType : type >-> UniformNormedZmodule.type.
Canonical uniformNormedZmodType.
Canonical pointed_lmodType.
Canonical filtered_lmodType.
Canonical topological_lmodType.
Canonical uniform_lmodType.
Canonical normedZmod_lmodType.
Canonical uniformNormedZmod_lmodType.
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

(*Definition norm {K : absRingType} {V : normedModType K} : V -> R :=
  NormedModule.norm (NormedModule.class _).
Notation "`|[ x ]|" := (norm x) : ring_scope.*)

Section NormedModule1.
Context {K : numDomainType(*absRingType*)} {V : normedZmodType K}.
Implicit Types (l : K) (x y : V) (eps : posreal).

(*TODO: useless? *)
Lemma ler_normm_add x y : `| x + y | <= `| x | + `| y |.
Proof. exact: ler_norm_add. Qed.

Lemma normm0_eq0 x : `|x| = 0 -> x = 0.
Proof. by move/eqP; rewrite normr_eq0 => /eqP. Qed.

Lemma normmN x : `|- x| = `|x|.
Proof. by rewrite normrN. Qed.

Lemma normmB x y : `|x - y| = `|y - x|.
Proof. by rewrite -normmN opprB. Qed.

Lemma normm0 : `|0 : V| = 0.
Proof. by rewrite normr0. Qed.
Hint Resolve normm0 : core.

Lemma normm_eq0 x : (`|x| == 0) = (x == 0).
Proof. exact: normr_eq0. Qed.

Lemma normm_ge0 x : 0 <= `|x|.
Proof. exact: normr_ge0. Qed.

Lemma normm_gt0 x : (0 < `|x|) = (x != 0).
Proof. by rewrite normr_gt0. Qed.

Lemma normm_lt0 x : (`|x| < 0) = false.
Proof. by rewrite normr_lt0. Qed.

Lemma normm_le0 x : (`|x| <= 0) = (x == 0).
Proof. exact: normr_le0. Qed.

Lemma ler_distm_dist x y : `| `|x| - `|y| | <= `|x - y|.
Proof. exact: ler_dist_dist. Qed.

End NormedModule1.

Section NormedModule1'.
Context {K : numDomainType(*absRingType*)} {V : uniformNormedZmoduleType K}.
Implicit Types (l : K) (x y : V) (eps : posreal).

Notation ball_norm := (ball_ (@normr K V)).

Notation locally_norm := (locally_ ball_norm).

Lemma ball_normE : ball_norm = ball.
Proof. by case: V => ? [? ? ? ? ? []]. Qed.

End NormedModule1'.

Section NormedModule1''.
Variables (R : numFieldType) (V : normedModType R).

Lemma normmZ l (x : V) : `| l *: x | = `| l | * `| x |.
Proof. by case: V x => V0 [a b [c]] //= v; rewrite c. Qed.

Notation ball_norm := (ball_ (@normr R V)).

Notation locally_norm := (locally_ ball_norm).

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof.
have := @ball_split _ _ z x y e.
by rewrite -ball_normE.
Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof.
have := @ball_splitr _ _ z x y e.
by rewrite -ball_normE.
Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof.
have := @ball_splitl _ _ z x y e.
by rewrite -ball_normE.
Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
move=> /posnumP[{e}e] /le_lt_trans ->//.
by rewrite [X in _ < X]splitr ltr_spaddl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < (e / 2)%R -> `|y| < (e / 2)%R -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

Lemma closeE (x y : V) : close x y = (x = y).
Proof.
rewrite propeqE; split => [cl_xy|->//]; have [//|neq_xy] := eqVneq x y.
have dxy_gt0 : `|x - y| > 0.
  by rewrite normm_gt0 subr_eq0.
have dxy_ge0 := ltW dxy_gt0.
have := cl_xy ((PosNum dxy_gt0)%:num / 2)%:pos.
rewrite -ball_normE /= -subr_lt0 le_gtF //.
rewrite -[X in X - _]mulr1 -mulrBr mulr_ge0 //.
by rewrite subr_ge0 -(@ler_pmul2r _ 2) // mulVf // mul1r ler1n.
Qed.
Lemma eq_close (x y : V) : close x y -> x = y. by rewrite closeE. Qed.

Lemma locally_le_locally_norm (x : V) : flim (locally x) (locally_norm x).
Proof.
move=> P [_ /posnumP[e] subP]; apply/locallyP.
by eexists; last (move=> y Py; apply/subP; rewrite ball_normE; apply/Py).
Qed.

Lemma locally_norm_le_locally x : flim (locally_norm x) (locally x).
Proof.
move=> P /locallyP [_ /posnumP[e] Pxe].
by exists e%:num => // y; rewrite ball_normE; apply/Pxe.
Qed.

(* NB: this lemmas was not here before *)
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

Lemma locally_norm_ball x (eps : {posnum R}) : locally_norm x (ball x eps%:num).
Proof. rewrite locally_locally_norm; by apply: locally_ball. Qed.

Lemma locally_ball_norm (x : V) (eps : {posnum R}) : locally x (ball_norm x eps%:num).
Proof. rewrite -locally_locally_norm; apply: locally_norm_ball_norm. Qed.

(* TODO: useless? *)
Lemma ball_norm_triangle' (x y z : V) (e1 e2 : R) :
  ball_norm x e1 y -> ball_norm y e2 z -> ball_norm x (e1 + e2) z.
Proof. exact: ball_norm_triangle. Qed.

Lemma ball_norm_center' (x : V) (e : {posnum R}) : ball_norm x e%:num x.
Proof. exact: ball_norm_center. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm -opprB normmN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Lemma norm_close x y : close x y = (forall eps : {posnum R}, ball_norm x eps%:num y).
Proof. by rewrite propeqE ball_normE. Qed.

Lemma ball_norm_eq x y : (forall eps : {posnum R}, ball_norm x eps%:num y) -> x = y.
Proof. by rewrite -norm_close closeE. Qed.

Lemma flim_unique {F} {FF : ProperFilter F} :
  is_prop [set x : V | F --> x].
Proof. by move=> Fx Fy; rewrite -closeE; apply: flim_close. Qed.

Lemma locally_flim_unique (x y : V) : x --> y -> x = y.
Proof. by rewrite -closeE; apply: flim_close. Qed.

Lemma lim_id (x : V) : lim x = x.
Proof. by symmetry; apply: locally_flim_unique; apply/cvg_ex; exists x. Qed.

Lemma flim_lim {F} {FF : ProperFilter F} (l : V) :
  F --> l -> lim F = l.
Proof. by move=> Fl; have Fcv := cvgP Fl; apply: (@flim_unique F). Qed.

Lemma flim_map_lim {T : Type} {F} {FF : ProperFilter F} (f : T -> V) (l : V) :
  f @ F --> l -> lim (f @ F) = l.
Proof. exact: flim_lim. Qed.

(* TODO: should move to reals.v *)
Lemma Rhausdorff : hausdorff [topologicalType of Rdefinitions.R].
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/(@in_segment_addgt0Pr _ x _ x) => _ /posnumP[e].
rewrite inE -ler_distl; set he := (e%:num / 2)%:pos.
have [z []] := clxy _ _ (@locally_ball _ R_uniformType x he) (locally_ball y he).
move=> zx_he yz_he.
rewrite (subr_trans z) (le_trans (ler_norm_add _ _) _)// ltW //.
by rewrite (splitr e%:num) (distrC z); apply: ltr_add.
Qed.

End NormedModule1''.

Section NormedModule1'''.

Variable (V : normedModType Rdefinitions.R).

Lemma normedModType_hausdorff : hausdorff V.
Proof.
move=> p q clp_q; apply/subr0_eq/normm0_eq0/Rhausdorff => A B pq_A.
rewrite -(@normm0 _ V) -(subrr p) => pp_B.
suff loc_preim r C :
  locally `|p - r| C -> locally r ((fun r => `|p - r|) @^-1` C).
  have [r []] := clp_q _ _ (loc_preim _ _ pp_B) (loc_preim _ _ pq_A).
  by exists `|p - r|.
move=> [e egt0 pre_C]; apply: locally_le_locally_norm; exists e => // s re_s.
apply: pre_C; apply: le_lt_trans (ler_distm_dist _ _) _.
by rewrite opprB addrC -subr_trans normmB.
Qed.

End NormedModule1'''.

Module Export LocallyNorm.
Definition locally_simpl := (locally_simpl,@locally_locally_norm,@filter_from_norm_locally).
End LocallyNorm.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @locally_normE,
   @filter_from_normE, @near_locally_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Section NormedModule2.

Context {T : Type} {K : realFieldType(*absRingType*)} {V : normedModType K}.

Lemma flimi_unique {F} {FF : ProperFilter F} (f : T -> set V) :
  {near F, is_fun f} -> is_prop [set x : V | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE; apply: flimi_close. Qed.

Lemma flim_normP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !locally_simpl. Qed.

Lemma flim_normW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Proof.
move=> cv; apply/flim_normP => _/posnumP[e]; near=> x.
by apply: normm_leW => //; near: x; apply: cv.
Grab Existential Variables. all: end_near. Qed.

Lemma flim_norm {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Proof. by move=> /flim_normP. Qed.

End NormedModule2.
Hint Resolve normm_ge0 : core.
Arguments flim_norm {_ _ F FF}.

Section NormedModule2'.

Context {T : Type}.

Lemma flim_bounded {R : realType} {V : normedModType R} {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> \forall M \near +oo, \forall y' \near F, `|y'| < M.
Proof.
move=> /flim_norm Fy; exists `|y| => M.
rewrite -subr_gt0 => subM_gt0; have := Fy _ subM_gt0.
apply: filterS => y' yy'; rewrite -(@ltr_add2r _ (- `|y|)).
rewrite (le_lt_trans _ yy') //.
by rewrite (le_trans _ (ler_distm_dist _ _)) // (*absRE*) distrC ler_norm.
Qed.

Lemma flimi_map_lim {R : realFieldType} {V : normedModType R} {F} {FF : ProperFilter F} (f : T -> V -> Prop) (l : V) :
  F (fun x : T => is_prop (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
move=> f_prop f_l; apply: get_unique => // l' f_l'.
exact: flimi_unique _ f_l' f_l.
Qed.

End NormedModule2'.
Arguments flim_bounded {_ _ F FF}.

Lemma continuous_flim_norm {R : realFieldType} (*{K : absRingType}*) (V W : normedModType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Proof.
move=> cf xl e.
move/flim_norm: (cf l) => /(_ _ (posnum_gt0 e)).
rewrite nearE /= => /locallyP; rewrite locally_E => -[i i0]; apply.
have /@flim_norm : Filter [filter of x] by apply: filter_on_Filter.
move/(_ _ xl _ i0).
rewrite nearE /= => /locallyP; rewrite locally_E => -[j j0].
by move/(_ _ (ballxx _ j0)); rewrite -ball_normE.
Qed.

(** ** Matrices *)

Section mx_norm.

Variables (K : realFieldType) (m n : nat).

(* take m.+1, n.+1 because ball_normE is not provable for m = 0 or n = 0 *)
(* TODO: check if we can remove .+1 partially *)
Definition mx_norm (x : 'M[K]_(m.+1, n.+1)) :=
  bigmaxr 0 [seq `|x ij.1 ij.2| | ij : 'I_m.+1 * 'I_n.+1].

Lemma ler_mx_norm_add (x y : 'M_(m.+1, n.+1)) : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
apply/bigmaxr_lerP=> [|i]; rewrite size_map -cardT mxvec_cast // => ltimn.
rewrite (nth_map (ord0, ord0)); last by rewrite -cardT mxvec_cast.
rewrite mxE; apply: le_trans (ler_norm_add _ _) _.
do 2 ?[rewrite -(nth_map _ 0 (fun p => `|_ p.1 p.2|)) -?cardT ?mxvec_cast //].
by apply: ler_add; apply: bigmaxr_ler; rewrite size_map -cardT mxvec_cast.
Qed.

Lemma mx_norm_eq0 (x : 'M_(m.+1, n.+1)) : mx_norm x = 0 -> x = 0.
Proof.
move=> x0; apply/matrixP => i j; rewrite mxE; apply/eqP.
rewrite -normr_eq0 eq_le; apply/andP; split; last exact: normr_ge0.
have /(bigmaxr_ler 0) :
  (index (i, j) (enum [finType of 'I_m.+1 * 'I_n.+1]) <
   size [seq (`|x ij.1 ij.2|)%R | ij : 'I_m.+1 * 'I_n.+1])%N.
  by rewrite size_map index_mem mem_enum.
rewrite -{3}x0; apply: le_trans.
rewrite (nth_map (ord0, ord0)); last by rewrite index_mem mem_enum.
by rewrite nth_index // mem_enum.
Qed.

Lemma mx_norm_natmul (x : 'M_(m.+1, n.+1)) n0 :  mx_norm (x *+ n0) = mx_norm x *+ n0.
Proof.
apply/bigmaxrP; split=> [|i].
  have : (0 < size [seq `|x ij.1 ij.2|%R | ij : 'I_m.+1 * 'I_n.+1])%O.
    by rewrite size_map -cardT mxvec_cast.
  move=> /bigmaxr_mem - /(_ 0) /mapP [ij ijP normx]; rewrite [mx_norm _]normx.
  by apply/mapP; exists ij => //; rewrite mulmxnE normrMn.
rewrite size_map -cardT mxvec_cast // => ltimn.
rewrite (nth_map (ord0, ord0)); last by rewrite -cardT mxvec_cast.
rewrite mulmxnE normrMn ler_muln2r /=.
case/boolP : (n0 == O) => n0O //=.
rewrite -(nth_map _ 0 (fun p => `|x p.1 p.2|)).
  by apply: bigmaxr_ler; rewrite size_map -cardT mxvec_cast.
by rewrite -cardT mxvec_cast.
Qed.

Lemma mx_normN (x : 'M_(m.+1, n.+1)) : mx_norm (- x) = mx_norm x.
Proof.
rewrite /mx_norm; congr (bigmaxr 0 _).
apply eq_in_map => /= i _; by rewrite mxE normrN.
Qed.

End mx_norm.

(* TODO: bigmaxr_morph *)
Lemma bigmaxr_scale (K : realFieldType) m n (s : seq [finType of 'I_m.+1 * 'I_n.+1]) (k : K) (x : 'M[K]_(m.+1, n.+1)) :
  bigmaxr 0 (map (fun ij => `|(k *: x) ij.1 ij.2|) s) =
  `| k | * bigmaxr 0 (map (fun ij => `|x ij.1 ij.2|) s).
Proof.
elim: s k x => /= [k _|h [|h' t] ih k x]; first by rewrite bigmaxr_nil mulr0.
  by rewrite !bigmaxr_un mxE normrM.
by rewrite bigmaxr_cons ih bigmaxr_cons maxr_pmulr ?normr_ge0 // mxE normrM.
Qed.

Section matrix_normedMod.

Variables (K : realFieldType(*absRingType*)) (m n : nat).

Definition matrix_normedZmodMixin :=
  Num.NormedMixin (@ler_mx_norm_add K m n)
    (@mx_norm_eq0 _ _ _) (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Canonical matrix_normedZmodType :=
  NormedZmoduleType K 'M[K]_(m.+1, n.+1) matrix_normedZmodMixin.

(* TODO: show the norm axiom and then use a factory
to instantiate the types below *)

(*Canonical K_filteredType := [filteredType K of K for filtered_of_normedZmod K].

Canonical K_topologicalType : topologicalType := @Topological.Pack K
  (@Topological.Class K (Filtered.class K_filteredType)
    (@topologyOfBallMixin _ K _ (@uniform_of_normedDomain K K))).

Canonical K_uniformType : uniformType K := @Uniform.Pack K K (@Uniform.Class K K
  (Topological.class K_topologicalType) (@uniform_of_normedDomain K K)).
*)

(*Definition K_lalgType : lalgType K := @GRing.regular_lalgType K.*)

Lemma mx_norm_ball :
  @ball _ [uniformType K of 'M[K^o]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Proof.
rewrite /= /normr /= /mx_norm.
rewrite predeq3E => x e y; split.
  move=> xe_y; apply/bigmaxr_ltrP; rewrite size_map -cardT mxvec_cast //.
  move=> i iltmn; rewrite (nth_map (ord0, ord0)).
    by rewrite !mxE; apply: xe_y.
  by rewrite -cardT mxvec_cast.
move=> /bigmaxr_ltrP; rewrite size_map -cardT mxvec_cast => xe_y i j.
have := xe_y _ (index (i, j) (enum [finType of 'I_m.+1 * 'I_n.+1])).
have memij : (i, j) \in enum [finType of 'I_m.+1 * 'I_n.+1].
  by rewrite mem_enum.
rewrite (nth_map (ord0, ord0)); last by rewrite index_mem.
by rewrite !mxE !nth_index //=; apply=> //; rewrite -mxvec_cast cardT index_mem.
Qed.

Definition matrix_UniformNormedZmodMixin :=
  UniformNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_uniformNormedZmodType :=
  UniformNormedZmoduleType K 'M[K^o]_(m.+1, n.+1) matrix_UniformNormedZmodMixin.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof. by rewrite {1 3}/normr /= /mx_norm bigmaxr_scale. Qed.

Definition matrix_NormedModMixin := NormedModMixin mx_normZ.
Canonical matrix_normedModType :=
  NormedModType K 'M[K^o]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_normedMod.

(** ** Pairs *)

Section prod_NormedModule.

Context {K : realFieldType(*absRingType*)} {U V : normedModType K}.

Lemma prod_normE (x : U * V) : `|x| = maxr `|x.1| `|x.2|.
Proof. by []. Qed.

Lemma prod_norm_scale (l : K) (x : U * V) : `|l *: x| = `|l| * `|x|.
Proof. by rewrite !prod_normE !normmZ maxr_pmulr. Qed.

Lemma ball_prod_normE : ball = ball_ (@normr _ [normedZmodType K of U * V]).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball.
by rewrite -!ball_normE /ball_ ltUx; split=> /andP.
Qed.

End prod_NormedModule.

Section prod.
Variables (K : realFieldType) (U V : normedModType K).

Lemma prod_norm_ball :
  @ball _ [uniformType K of U * V] = ball_ (fun x => `|x|).
Proof. by rewrite /= -ball_prod_normE. Qed.

Definition prod_UniformNormedZmodMixin :=
  UniformNormedZmodule.Mixin prod_norm_ball.
Canonical prod_uniformNormedZmodType :=
  UniformNormedZmoduleType K (U * V) prod_UniformNormedZmodMixin.

Definition prod_NormedModMixin := NormedModMixin prod_norm_scale.
Canonical prod_normedModType :=
  NormedModType K (U * V) prod_NormedModMixin.

End prod.

Section NormedModule3.

Context {T : Type} {K : realFieldType(*absRingType*)} {U : normedModType K}
                   {V : normedModType K}.

Lemma flim_norm2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. exact: flim_normP. Qed.

(* Lemma flim_norm_supP {F : set (set U)} {G : set (set V)} *)
(*   {FF : Filter F} {FG : Filter G} (y : U) (z : V): *)
(*   (F, G) --> (y, z) <-> *)
(*   forall eps : {posnum R}, {near F & G, forall y' z', *)
(*           (`|[y - y']| < eps) /\ (`|[z - z']| < eps) }. *)
(* Proof. *)
(* rewrite flim_ballP; split => [] P eps. *)
(* - have [[A B] /=[FA GB] ABP] := P eps; exists (A, B) => -//[a b] [/= Aa Bb]. *)
(*   apply/andP; rewrite -ltr_maxl. *)
(*   have /= := (@sub_ball_norm_rev _ _ (_, _)). *)

Lemma flim_norm2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. by rewrite flim_normP. Qed.

End NormedModule3.
Arguments flim_norm2 {_ _ _ F G FF FG}.

(** Rings with absolute values are normed modules *)

(*Definition AbsRing_NormedModMixin (K : absRingType) :=
  @NormedModule.Mixin K _ _ _ (abs : K^o -> R) ler_abs_add absrM (ball_absE K)
  absr0_eq0.
Canonical AbsRing_NormedModType (K : absRingType) :=
  NormedModType K K^o (AbsRing_NormedModMixin _).*)

Lemma R_normZ (R : realFieldType) (l : R) (x : R^o) : `| l *: x | = `| l | * `| x |.
Proof. by rewrite normrM. Qed.
Definition realFieldType_NormedModMixin (R : realFieldType) := NormedModMixin (@R_normZ R).
Canonical realFieldType_normedModType (R : realFieldType) :=
  NormedModType R R^o (realFieldType_NormedModMixin R).

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : realFieldType(*absRingType*)} {V : normedModType K}.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/=x y]; apply/flim_normP=> _/posnumP[e].
rewrite !near_simpl /=; near=> a b => /=; rewrite opprD addrACA.
by rewrite normm_lt_split //; [near: a|near: b]; apply: flim_norm.
Grab Existential Variables. all: end_near. Qed.

End NVS_continuity.

(* kludge *)
Global Instance filter_locally (K' : realFieldType) (k : K'^o) : Filter (locally k).
Proof.
exact: (@locally_filter [topologicalType of K'^o]).
Qed.

Section NVS_continuity1.
Context {K : realType} {V : normedModType K}.
Local Notation "'+oo'" := (@ERPInf K).
Local Notation "'-oo'" := (@ERNInf K).

Lemma scale_continuous :
  continuous (fun z : [filteredType _ of K^o * V] => z.1 *: z.2).
Proof.
move=> [k x]; apply/flim_normP=> _/posnumP[e].
rewrite !near_simpl /=; near +oo => M; near=> l z => /=.
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normmZ.
  rewrite (le_lt_trans (ler_pmul _ _ (_ : _ <= `|k| + 1) (lexx _)))
          ?ler_addl //.
  rewrite -ltr_pdivl_mull // ?(lt_le_trans ltr01) ?ler_addr //; near: z.
  by apply: flim_norm; rewrite // mulr_gt0 // ?invr_gt0 ltr_paddl.
have zM : `|z| < M by near: z; near: M; apply: flim_bounded; apply: flim_refl.
rewrite (le_lt_trans (ler_pmul _ _ (lexx _) (_ : _ <= M))) // ?ltW//.
rewrite -ltr_pdivl_mulr ?(le_lt_trans _ zM) //.
near: l; apply: (flim_norm (_ : K^o)) => //.
by rewrite divr_gt0 //; near: M; exists 0. (*NB(rei): the last three lines used to be one *)
Grab Existential Variables. all: end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (flim_comp2 (flim_const _) flim_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : [filteredType _ of K^o] => k *: x).
Proof.
by move=> k; apply: (flim_comp2 flim_id (flim_const _) (scale_continuous (_, _))).
Qed.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; rewrite -scaleN1r => P /scaler_continuous /=.
rewrite !locally_nearE near_map.
by apply: filterS => x'; rewrite scaleN1r.
Qed.

End NVS_continuity1.

Section limit_composition.

Context {K : realType(*absRingType*)} {V : normedModType K} {T : topologicalType}.

Lemma lim_cst (a : V) (F : set (set V)) {FF : Filter F} : (fun=> a) @ F --> a.
Proof. exact: cst_continuous. Qed.
Hint Resolve lim_cst : core.

Lemma lim_add (F : set (set T)) (FF : Filter F) (f g : T -> V) (a b : V) :
  f @ F --> a -> g @ F --> b -> (f \+ g) @ F --> a + b.
Proof. by move=> ??; apply: lim_cont2 => //; exact: add_continuous. Qed.

Lemma continuousD (f g : T -> V) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun x => f x + g x)}.
Proof. by move=> ??; apply: lim_add. Qed.

Lemma lim_scale (F : set (set T)) (FF : Filter F) (f : T -> K) (g : T -> V)
  (k : K^o) (a : V) :
  f @ F --> k -> g @ F --> a -> (fun x => (f x) *: (g x)) @ F --> k *: a.
Proof. move=> ??; apply: lim_cont2 => //; exact: scale_continuous. Qed.

Lemma lim_scalel (F : set (set T)) (FF : Filter F) (f : T -> K) (a : V) (k : K^o) :
  f @ F --> k -> (fun x => (f x) *: a) @ F --> k *: a.
Proof. by move=> ?; apply: lim_scale => //; exact: cst_continuous. Qed.

Lemma lim_scaler (F : set (set T)) (FF : Filter F) (f : T -> V) (k : K) (a : V) :
  f @ F --> a -> k \*: f  @ F --> k *: a.
Proof.
apply: lim_scale => //; exact: (@cst_continuous _ [topologicalType of K^o]).
Qed.

Lemma continuousZ (f : T -> V) k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: lim_scaler. Qed.

Lemma continuousZl (k : T -> K^o) (f : V) x :
  {for x, continuous k} -> {for x, continuous (fun z => k z *: f)}.
Proof. by move=> ?; apply: lim_scalel. Qed.

Lemma lim_opp (F : set (set T)) (FF : Filter F) (f : T -> V) (a : V) :
  f @ F --> a -> (fun x => - f x) @ F --> - a.
Proof. by move=> ?; apply: lim_cont => //; apply: opp_continuous. Qed.

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: lim_opp. Qed.

Lemma lim_mult (x y : K^o) : z.1 * z.2 @[z --> (x, y)] --> x * y.
Proof. exact: (@scale_continuous _ [normedModType K of K^o]). Qed.

Lemma continuousM (f g : T -> K^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (fun x => f x * g x)}.
Proof. by move=> fc gc; apply: flim_comp2 fc gc _; apply: lim_mult. Qed.

End limit_composition.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : realFieldType(*absRingType*).

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (Uniform.Pack base)
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
Definition uniformType := @Uniform.Pack _ cT xclass.
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
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
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

Arguments flim_normW {_ _ F FF}.

(* :TODO: add to mathcomp *)
Lemma ltr_distW (R : realDomainType) (x y e : R):
   (`|x - y|%R < e) -> y - e < x.
Proof. by rewrite ltr_distl => /andP[]. Qed.

(* :TODO: add to mathcomp *)
Lemma ler_distW (R : realDomainType) (x y e : R):
   (`|x - y|%R <= e) -> y - e <= x.
Proof. by rewrite ler_distl => /andP[]. Qed.

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
apply: (flim_normW (_ : R^o)) => /= _ /posnumP[eps]; near=> x.
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
Variable R : realType.

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

Lemma continuous_norm {K : realFieldType} {V : normedModType K} :
  continuous ((@normr _ V) : V -> K^o).
Proof.
move=> x; apply/(@flim_normP _ [normedModType K of K^o]) => _/posnumP[e] /=.
rewrite !near_simpl; apply/locally_normP; exists e%:num => // y Hy.
exact/(le_lt_trans (ler_distm_dist _ _)).
Qed.

(* :TODO: yet, not used anywhere?! *)
Lemma flim_norm0 {U} {K : realFieldType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : [filteredType _ of K^o])
  -> f @ F --> (0 : V).
Proof.
move=> /(flim_norm (_ : K^o)) fx0; apply/flim_normP => _/posnumP[e].
rewrite near_simpl; have := fx0 _ [gt0 of e%:num]; rewrite near_simpl.
by apply: filterS => x; rewrite !sub0r !normmN [ `|_| ]ger0_norm.
Qed.

Section cvg_seq_bounded.
Context {K : realType}.
Local Notation "'+oo'" := (@ERPInf K).

(* TODO: simplify using extremumP when PR merged in mathcomp *)
Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  [cvg a in V] -> {M | forall n, normr (a n) <= M}.
Proof.
move=> a_cvg; suff: exists M, forall n, normr (a n) <= M.
  by move=> /(@getPex [pointedType of K^o]); set M := get _; exists M.
near +oo => M.
have [//|N _ /(_ _ _) /ltW a_leM] := !! near (flim_bounded _ a_cvg) M.
exists (maxr M (\big[maxr/M]_(n < N) `|a (val (rev_ord n))|)) => /= n.
rewrite lexU; have [nN|nN] := leqP N n; first by rewrite a_leM.
apply/orP; right => {a_leM}; elim: N n nN=> //= N IHN n.
rewrite leq_eqVlt => /orP[/eqP[->] |/IHN a_le];
by rewrite big_ord_recl subn1 /= lexU ?a_le ?lexx ?orbT.
Grab Existential Variables. all: end_near. Qed.

End cvg_seq_bounded.

(** Some open sets of [R] *)

Section some_open_sets.
Variable R : realType.

Lemma open_lt (y : R) : @open [topologicalType of R^o] [set x | x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0; exists (y - x) => // z.
by rewrite /= distrC ltr_distl addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt (y : R) : @open [topologicalType of R^o] [set x | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= distrC ltr_distl opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : @open [topologicalType of R^o] (xpredC (eq_op^~ y)).
Proof.
rewrite (_ : xpredC _ = [set x | x < y] `|` [set x | x > y] :> set _) /=.
  by apply: openU => //; apply: open_lt.
rewrite predeqE => x /=; rewrite eq_le !leNgt negb_and !negbK orbC.
by symmetry; apply (rwP orP).
Qed.

(** Some closed sets of [R] *)

Lemma closed_le (y : R) : @closed [topologicalType of R^o] [set x | x <= y].
Proof.
rewrite (_ : [set x | x <= _] = ~` (> y) :> set _).
  by apply: closedC; exact: open_gt.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_ge (y : R) : @closed [topologicalType of R^o] (>= y).
Proof.
rewrite (_ : (>= _) = ~` [set x | x < y] :> set _).
  by apply: closedC; exact: open_lt.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_eq (y : R) : @closed [topologicalType of R^o] (eq^~ y).
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

(** properties of segments in [R] *)

Lemma segment_connected (a b : R) : @connected [topologicalType of R^o] [set x | x \in `[a, b]].
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

Lemma segment_closed (a b : R) : @closed [topologicalType of R^o] [set x | x \in `[a, b]].
Proof.
have -> : [set x | x \in `[a, b]] = [set x | x >= a] `&` [set x | x <= b].
  by rewrite predeqE => ?; rewrite inE; split=> [/andP [] | /= [->]].
exact: closedI (@closed_ge _) (@closed_le _).
Qed.

Lemma segment_compact (a b : R) : @compact [topologicalType of R^o] [set x | x \in `[a, b]].
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

End some_open_sets.

Lemma ler0_addgt0P (R : realFieldType) (x : R) :
  reflect (forall e, e > 0 -> x <= e) (x <= 0).
Proof.
apply: (iffP idP) => [lex0 e egt0|lex0].
  by apply: le_trans lex0 _; apply: ltW.
case: (lerP x 0) => // lt0x.
have /midf_lt [_] := lt0x; rewrite ltNge -eqbF_neg => /eqP<-.
by rewrite add0r; apply: lex0; rewrite -[x]/((PosNum lt0x)%:num).
Qed.

Lemma IVT (f : Rdefinitions.R -> Rdefinitions.R) (a b v : Rdefinitions.R) :
  a <= b -> {in `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab; wlog : f v / f a <= f b.
  move=> ivt; case: (lerP (f a) (f b)) => [|/ltW lefba].
    exact: ivt.
  move=> fcont fabv; have [] := ivt (fun x => - f x) (- v).
  - by rewrite ler_oppr opprK.
  - by move=> x /fcont; apply: (@continuousN _ [normedModType Rdefinitions.R of Rdefinitions.R^o]).
  - by rewrite -oppr_max -oppr_min ler_oppr opprK ler_oppr opprK andbC.
  by move=> c cab /eqP; rewrite eqr_opp => /eqP; exists c.
move=> lefab fcont; rewrite (elimT meet_idPl) // (elimT join_idPl) // => /andP [].
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
  have /fcont /(_ _ (locally_ball _ (PosNum vltfsup))) [_/posnumP[d] supdfe]
    := supAab.
  have [t At supd_t] := sup_adherent supA [gt0 of d%:num].
  suff /supdfe : ball (sup A) d%:num t.
    rewrite /= /ball /= ltr_norml => /andP [_].
    by rewrite ltr_add2l ltr_oppr opprK ltNge; have /andP [_ ->] := At.
  rewrite /= /ball /= ger0_norm.
    by rewrite ltr_subl_addr -ltr_subl_addl.
  by rewrite subr_ge0 sup_upper_bound.
apply/eqP; rewrite eq_le; apply/andP; split=> //.
rewrite -subr_le0; apply/ler0_addgt0P => _/posnumP[e].
rewrite ler_subl_addr -ler_subl_addl ltW //.
have /fcont /(_ _ (locally_ball _ e)) [_/posnumP[d] supdfe] := supAab.
have atrF := at_right_proper_filter (sup A); near (at_right (sup A)) => x.
have /supdfe /= : ball (sup A) d%:num x.
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

(* NB: this is a proof that was in Rbar and that has been ported to {ereal _} *)
Lemma lt_ereal_locally (R : realType) (a b : {ereal R}) (x : R) :
  lt_ereal a (ERFin x) -> lt_ereal (ERFin x) b ->
  exists delta : {posnum R},
    forall y, `|y - x| < delta%:num -> lt_ereal a (ERFin y) && lt_ereal (ERFin y) b.
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog. (*BUG*)
  move=> {a b} a b ltxa ltxb.
  have m_gt0 : minr ((x - a) / 2) ((b - x) / 2) > 0.
    by rewrite ltxI !divr_gt0 // ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite ltxI !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite (lt_trans _ ay) ?(lt_trans yb) //=.
    by rewrite -subr_gt0 opprD addrA {1}[b - x]splitr addrK divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[x - a]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (x + 1); rewrite ?ltr_addl //.
  by exists d => y /dP /andP[->].
- have [//||d dP] := wlog (x - 1) b; rewrite ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->].
- by exists 1%:pos.
Qed.

Lemma locally_interval (R : realType) (P : R -> Prop) (x : R) (a b : {ereal R}) :
  lt_ereal a (ERFin x) -> lt_ereal (ERFin x) b ->
  (forall y : R, lt_ereal a (ERFin y) -> lt_ereal (ERFin y) b -> P y) ->
  @locally _ [filteredType _ of R^o] x P.
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
Variable K : realType.
Local Notation "'+oo'" := (@ERPInf K).
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
  rewrite -ball_normE /= ltr_subr_addr normmB; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_normm_add.
move=> D _ DcovA.
exists (bigmaxr 0 [seq n%:~R | n <- enum_fset D]).
move=> x ltmaxx p /DcovA [n Dn /lt_trans]; apply; apply: le_lt_trans ltmaxx.
have ltin : (index n (enum_fset D) < size (enum_fset D))%N by rewrite index_mem.
rewrite -(nth_index 0 Dn) -(nth_map _ 0) //; apply: bigmaxr_ler.
by rewrite size_map.
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

Lemma bounded_closed_compact n (A : set 'rV[Rdefinitions.R]_n.+1) :
  bounded A -> closed A -> compact A.
Proof.
move=> [M normAltM] Acl.
have Mnco : compact
  [set v : 'rV[Rdefinitions.R]_n.+1 | (forall i, (v ord0 i) \in `[(- (M + 1)), (M + 1)])].
  apply: (@rV_compact _ _ (fun _ => [set x | x \in `[(- (M + 1)), (M + 1)]])).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvltM i.
suff /ltW : `|v ord0 i : Rdefinitions.R^o| < M + 1 by rewrite ler_norml.
apply: le_lt_trans (normvltM _ _); last by rewrite ltr_addl.
have vinseq : `|v ord0 i| \in [seq `|v ij.1 ij.2| | ij : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
rewrite -[X in X <= _](nth_index 0 vinseq); apply: bigmaxr_ler.
by rewrite index_mem.
Qed.

(** Open sets in [Rbar] *)

Section open_sets_in_Rbar.
Variable R : realType.

Lemma open_Rbar_lt y : open (fun u : [topologicalType of R^o] => lt_ereal (ERFin u) y).
Proof.
case: y => [y||] /=.
exact: open_lt.
by rewrite trueE; apply: openT.
by rewrite falseE; apply: open0.
Qed.

Lemma open_Rbar_gt y : open (fun u : [topologicalType of R^o] => lt_ereal y (ERFin u)).
Proof.
case: y => [y||] /=.
exact: open_gt.
by rewrite falseE; apply: open0.
by rewrite trueE; apply: openT.
Qed.

Lemma open_Rbar_lt' x y : lt_ereal x y -> Rbar_locally x (fun u : R => lt_ereal (ERFin u) y).
Proof.
case: x => [x|//|] xy; first exact: open_Rbar_lt.
case: y => [y||//] /= in xy *.
exists y => /= x ? //.
by exists 0.
case: y => [y||//] /= in xy *.
exists y => /= x ? //.
by exists 0.
Qed.

Lemma open_Rbar_gt' x y : lt_ereal y x -> Rbar_locally x (fun u : R => lt_ereal y (ERFin u)).
Proof.
case: x => [x||] //=; do ?[exact: open_Rbar_gt];
  case: y => [y||] //=; do ?by exists 0.
by exists y => x yx //=.
Qed.

Lemma Rbar_locally'_le (x : {ereal R}) : Rbar_locally' x --> Rbar_locally x.
Proof.
move: x => [x P [_/posnumP[e] HP] |x P|x P] //=.
by exists e%:num => // ???; apply: HP.
Qed.

Lemma Rbar_locally'_le_finite (x : R) : Rbar_locally' (ERFin x) --> locally (ERFin x).
Proof.
by move=> P [_/posnumP[e] HP] //=; exists e%:num => // ???; apply: HP.
Qed.

End open_sets_in_Rbar.

(** * Some limits on real functions *)

Definition Rbar_loc_seq (R : realType) (x : {ereal R}) (n : nat) := match x with
    | ERFin x => x + (n%:R + 1)^-1
    | +oo => n%:R
    | -oo => - n%:R
  end.

Lemma flim_Rbar_loc_seq (R : realType) (x : {ereal R}) :
  flim (filter_of (Phantom (nat -> R^o) (Rbar_loc_seq x)))
       (filter_of (Phantom ((R^o -> Prop) -> Prop) (@Rbar_locally' R x))).
(*TODO(notation issue): was Rbar_loc_seq x --> Rbar_locally' x *)
Proof.
move=> P; rewrite /Rbar_loc_seq.
case: x => /= [x [_/posnumP[delta] Hp] |[delta Hp] |[delta Hp]]; last 2 first.
    have /ZnatP [N Nfloor] : ifloor (maxr delta 0) \is a Znat.
      by rewrite Znat_def ifloor_ge0 lexU lexx orbC.
    exists N.+1 => // n ltNn; apply: Hp.
    have /le_lt_trans : delta <= maxr delta 0 by rewrite lexU lexx.
    apply; apply: lt_le_trans (floorS_gtr _) _; rewrite floorE Nfloor.
    by rewrite -(@natrD [ringType of R] N 1) ler_nat addn1.
  have /ZnatP [N Nfloor] : ifloor (maxr (- delta) 0) \is a Znat.
    by rewrite Znat_def ifloor_ge0 lexU lexx orbC.
  exists N.+1 => // n ltNn; apply: Hp; rewrite ltr_oppl.
  have /le_lt_trans : - delta <= maxr (- delta) 0 by rewrite lexU lexx.
  apply; apply: lt_le_trans (floorS_gtr _) _; rewrite floorE Nfloor.
  by rewrite -(@natrD [ringType of R] N 1) ler_nat addn1.
have /ZnatP [N Nfloor] : ifloor (delta%:num^-1) \is a Znat.
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
Lemma continuity_pt_locally (f : Rdefinitions.R -> Rdefinitions.R) x : Ranalysis1.continuity_pt f x <->
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

Lemma continuity_pt_flim (f : Rdefinitions.R -> Rdefinitions.R) (x : Rdefinitions.R) :
  Ranalysis1.continuity_pt f x <-> {for x, continuous f}.
Proof.
eapply iff_trans; first exact: continuity_pt_locally.
apply iff_sym.
have FF : Filter (f @ x).
(* (* BUG: this should work *) *)
(*   by typeclasses eauto. *)
  by apply filtermap_filter; apply: @filter_filter' (locally_filter _).
case: (@flim_ballP _ _ (f @ x) FF (f x)) => {FF}H1 H2.
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
Proof. exact: continuity_pt_flim. Qed.

Lemma continuous_withinNx (R : realType) {U V : uniformType R}
  (f : U -> V) x :
  {for x, continuous f} <-> f @ locally' x --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /locally' !near_simpl near_withinE.
  by rewrite /locally'; apply: flim_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not inferred *)
rewrite !locally_nearE !near_map !near_locally in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: locally_singleton|near: y].
Grab Existential Variables. all: end_near. Qed.

Lemma continuity_pt_flim' f x :
  Ranalysis1.continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx. Qed.

Lemma continuity_pt_locally' f x :
  Ranalysis1.continuity_pt f x <->
  forall eps, 0 < eps -> locally' x (fun u => `|f x - f u| < eps)%R.
Proof.
rewrite continuity_pt_flim' (@flim_normP _ [normedModType _ of Rdefinitions.R^o]).
exact.
Qed.

Lemma locally_pt_comp (P : Rdefinitions.R -> Prop) (f : Rdefinitions.R -> Rdefinitions.R) (x : Rdefinitions.R) :
  locally (f x) P -> Ranalysis1.continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_flim; apply. Qed.
