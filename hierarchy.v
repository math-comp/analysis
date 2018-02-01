(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop ssralg ssrnum finmap matrix.
From SsrReals Require Import boolp reals.
Require Import Rstruct Rbar set posnum topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

(** * Uniform spaces defined using balls *)

Definition locally_ {T T'} (ball : T -> R -> set T') (x : T) :=
   @filter_from R _ [set x | 0 < x] (ball x).

Lemma locally_E {T T'} (ball : T -> R -> set T') x :
  locally_ ball x = @filter_from R _ [set x : R | 0 < x] (ball x).
Proof. by []. Qed.

Module Uniform.

Record mixin_of (M : Type) (locally : M -> set (set M)) := Mixin {
  ball : M -> R -> M -> Prop ;
  ax1 : forall x (e : R), 0 < e -> ball x e x ;
  ax2 : forall x y (e : R), ball x e y -> ball y e x ;
  ax3 : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  ax4 : locally = locally_ ball
}.

Record class_of (M : Type) := Class {
  base : Topological.class_of M;
  mixin : mixin_of (Filtered.locally_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Topological.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack loc (m : @mixin_of T loc) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.locally_op b)) =>
  @Pack T (@Class _ b m') T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filteredType := @Filtered.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Topological.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.
Notation "[ 'uniformType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'uniformType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'uniformType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'uniformType'  'of'  T ]") : form_scope.

End Exports.

End Uniform.

Export Uniform.Exports.

Section UniformTopology.

Lemma my_ball_le (M : Type) (loc : M -> set (set M))
  (m : Uniform.mixin_of loc) :
  forall (x : M) (e1 e2 : R), e1 <= e2 ->
  forall (y : M), Uniform.ball m x e1 y -> Uniform.ball m x e2 y.
Proof.
move=> x e1 e2 le12 y xe1_y.
move: le12; rewrite ler_eqVlt => /orP [/eqP <- //|].
rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: Uniform.ax3 xe1_y.
suff : Uniform.ball m x (PosNum lt12)%:num x by [].
exact: Uniform.ax1.
Qed.

Program Definition uniform_TopologicalTypeMixin (T : Type)
  (loc : T -> set (set T)) (m : Uniform.mixin_of loc) :
  Topological.mixin_of loc := topologyOfFilterMixin _ _ _.
Next Obligation.
rewrite (Uniform.ax4 m) locally_E; apply filter_from_proper; last first.
  move=> e egt0; exists p; suff : Uniform.ball m p (PosNum egt0)%:num p by [].
  exact: Uniform.ax1.
apply: filter_from_filter; first by exists 1%:pos%:num.
move=> e1 e2 e1gt0 e2gt0; exists (Num.min e1 e2).
  by have := min_pos_gt0 (PosNum e1gt0) (PosNum e2gt0).
by move=> q pmin_q; split; apply: my_ball_le pmin_q;
  rewrite ler_minl lerr // orbC.
Qed.
Next Obligation.
move: H; rewrite (Uniform.ax4 m) locally_E => - [e egt0]; apply.
by have : Uniform.ball m p (PosNum egt0)%:num p by exact: Uniform.ax1.
Qed.
Next Obligation.
move: H; rewrite (Uniform.ax4 m) locally_E => - [e egt0 pe_A].
exists ((PosNum egt0)%:num / 2) => // q phe_q.
rewrite locally_E; exists ((PosNum egt0)%:num / 2) => // r qhe_r.
by apply: pe_A; rewrite [e]splitr; apply: Uniform.ax3 qhe_r.
Qed.

End UniformTopology.

Definition ball {M : uniformType} := Uniform.ball (Uniform.class M).

Definition entourages {T : uniformType} : set (set (T * T)):=
  filter_from [set eps : R | eps > 0]
              (fun eps => [set xy | ball xy.1 eps xy.2]).

Definition unif_cont (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourages --> entourages.

Lemma unif_contP (U V : uniformType) (f : U -> V) :
  unif_cont f <-> forall e, e > 0 -> exists2 d, d > 0 &
    forall x y, ball x d y -> ball (f x) e (f y).
Proof.
split=> fcont=> [e egt0|A [e egt0 e_A]]; last first.
  by have /fcont [d ? fde] := egt0; exists d => // ? /fde ?; apply: e_A.
have [|d dgt0 fde] := fcont [set xy | ball xy.1 e xy.2].
  by rewrite near_simpl; exists e.
by exists d => // x y ?; rewrite -[y]/((x, y).2) -{1}[x]/((x, y).1); apply: fde.
Qed.

Lemma locally_ballE {M : uniformType} : locally_ (@ball M) = locally.
Proof. by case: M=> [?[?[]]]. Qed.

Lemma filter_from_ballE {M : uniformType} x :
  @filter_from R _ [set x : R | 0 < x] (@ball M x) = locally x.
Proof. by rewrite -locally_ballE. Qed.

Module Export LocallyBall.
Definition locally_simpl := (locally_simpl,@filter_from_ballE,@locally_ballE).
End LocallyBall.

Lemma locallyP {M : uniformType} (x : M) P :
  locally x P <-> locally_ ball x P.
Proof. by rewrite locally_simpl. Qed.

Section uniformType1.
Context {M : uniformType}.

Lemma ball_center (x : M) (e : posreal) : ball x e%:num x.
Proof. exact: Uniform.ax1. Qed.
Hint Resolve ball_center.

Lemma ballxx (x : M) (e : R) : (0 < e)%R -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: Uniform.ax2. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2)%R z.
Proof. exact: Uniform.ax3. Qed.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2)%R z -> ball z (e / 2)%R y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -splitr. Qed.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2)%R x -> ball z (e / 2)%R y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

Lemma ball_ler (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y; case: ltrgtP le12 => [//|lte12 _|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma ball_le (x : M) (e1 e2 : R) : (e1 <= e2)%coqR -> ball x e1 `<=` ball x e2.
Proof. by move=> /RleP/ball_ler. Qed.

Definition close (x y : M) : Prop := forall eps : posreal, ball x eps%:num y.

Lemma close_refl (x : M) : close x x. Proof. by []. Qed.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof. by move=> ??; apply: ball_sym. Qed.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof. by move=> cxy cyz eps; apply: ball_split (cxy _) (cyz _). Qed.

Lemma close_limxx (x y : M) : close x y -> x --> y.
Proof.
move=> cxy P /= /locallyP /= [_/posnumP [eps] epsP].
apply/locallyP; exists (eps%:num / 2) => // z bxz.
by apply: epsP; apply: ball_splitr (cxy _) bxz.
Qed.

End uniformType1.

Hint Resolve ball_center.
Hint Resolve close_refl.

(** ** Specific uniform spaces *)

(** rings with an absolute value *)

Module AbsRing.

Record mixin_of (D : ringType) := Mixin {
  abs : D -> R;
  ax1 : abs 0 = 0 ;
  ax2 : abs (- 1) = 1 ;
  ax3 : forall x y : D, abs (x + y) <= abs x + abs y ;
  ax4 : forall x y : D, abs (x * y) <= abs x * abs y ;
  ax5 : forall x : D, abs x = 0 -> x = 0
}.

Section ClassDef.

Record class_of (K : Type) := Class {
  base : Num.NumDomain.class_of K ;
  mixin : mixin_of (Num.NumDomain.Pack base K)
}.
Local Coercion base : class_of >-> Num.NumDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : mixin_of (@Num.NumDomain.Pack T b0 T)) :=
  fun bT b & phant_id (Num.NumDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.

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
Notation "`| x |" := (abs x%R) : R_scope.
Notation "`| x |" := (abs x%R) : real_scope.

Section AbsRing1.

Context {K : absRingType}.
Implicit Types x : K.

Lemma absr0 : `|0 : K| = 0. Proof. exact: AbsRing.ax1. Qed.

Lemma absrN1: `|- 1 : K| = 1.
Proof. exact: AbsRing.ax2. Qed.

Lemma ler_abs_add (x y : K) :  `|x + y| <= `|x|%real + `|y|%real.
Proof. exact: AbsRing.ax3. Qed.

Lemma absrM (x y : K) : `|x * y| <= `|x|%real * `|y|%real.
Proof. exact: AbsRing.ax4. Qed.

Lemma absr0_eq0 (x : K) : `|x| = 0 -> x = 0.
Proof. exact: AbsRing.ax5. Qed.

Lemma absrN x : `|- x| = `|x|.
Proof.
gen have le_absN1 : x / `|- x| <= `|x|.
  by rewrite -mulN1r (ler_trans (absrM _ _)) //= absrN1 mul1r.
by apply/eqP; rewrite eqr_le le_absN1 /= -{1}[x]opprK le_absN1.
Qed.

Lemma absrB (x y : K) : `|x - y| = `|y - x|.
Proof. by rewrite -absrN opprB. Qed.

Lemma absr1 : `|1 : K| = 1. Proof. by rewrite -absrN absrN1. Qed.

Lemma absr_ge0 x : 0 <= `|x|.
Proof.
rewrite -(@pmulr_rge0 _ 2) // mulr2n mulrDl !mul1r.
by rewrite -{2}absrN (ler_trans _ (ler_abs_add _ _)) // subrr absr0.
Qed.

Lemma absr_eq0 x : (`|x| == 0) = (x == 0).
Proof. by apply/eqP/eqP=> [/absr0_eq0//|->]; rewrite absr0. Qed.

Lemma absr1_gt0 : `|1 : K| > 0.
Proof. by rewrite ltr_def absr1 oner_eq0 /=. Qed.

Lemma absrX x n : `|x ^+ n| <= `|x|%real ^+ n.
Proof.
elim: n => [|n IH]; first  by rewrite !expr0 absr1.
by rewrite !exprS (ler_trans (absrM _ _)) // ler_pmul // absr_ge0.
Qed.

End AbsRing1.
Hint Resolve absr_ge0.
Hint Resolve absr1_gt0.

Definition ball_ (V : zmodType) (norm : V -> R) (x : V)
  (e : R) := [set y | norm (x - y) < e].
Arguments ball_ {V} norm x e%R y /.

Section AbsRing_UniformSpace.

Context {K : absRingType}.

Definition AbsRing_ball := ball_ (@abs K).

Lemma AbsRing_ball_center (x : K) (e : R) : 0 < e -> AbsRing_ball x e x.
Proof. by rewrite /AbsRing_ball /= subrr absr0. Qed.

Lemma AbsRing_ball_sym (x y : K) (e : R) :
  AbsRing_ball x e y -> AbsRing_ball y e x.
Proof. by rewrite /AbsRing_ball /= absrB. Qed.

(* :TODO: to math-comp *)
Lemma subr_trans (M : zmodType) (z x y : M) : x - y = (x - z) + (z - y).
Proof. by rewrite addrA addrNK. Qed.

Lemma AbsRing_ball_triangle (x y z : K) (e1 e2 : R) :
  AbsRing_ball x e1 y -> AbsRing_ball y e2 z -> AbsRing_ball x (e1 + e2) z.
Proof.
rewrite /AbsRing_ball /= => xy yz.
by rewrite (subr_trans y) (ler_lt_trans (ler_abs_add _ _)) ?ltr_add.
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
  TopologicalType K (uniform_TopologicalTypeMixin AbsRingUniformMixin).
Canonical absRing_topologicalType.
Coercion absRing_UniformType (K : absRingType) := UniformType K AbsRingUniformMixin.
Canonical absRing_UniformType.

(** real numbers *)

Program Definition R_AbsRingMixin :=
 @AbsRing.Mixin _ normr (normr0 _) (normrN1 _) (@ler_norm_add _) _ (@normr0_eq0 _).
Next Obligation. by rewrite normrM. Qed.
Canonical R_absRingType := AbsRingType R R_AbsRingMixin.

Canonical R_pointedType := [pointedType of R for R_absRingType].
Canonical R_filteredType := [filteredType R of R for R_absRingType].
Canonical R_topologicalType := [topologicalType of R for R_absRingType].
Canonical R_uniformType := [uniformType of R for R_absRingType].
Canonical Ro_pointedType := [pointedType of R^o for R_absRingType].
Canonical Ro_filteredType := [filteredType R^o of R^o for R_absRingType].
Canonical Ro_topologicalType := [topologicalType of R^o for R_absRingType].
Canonical Ro_uniformType := [uniformType of R^o for R_absRingType].

(** locally *)

Section Locally.
Context {T : uniformType}.

Lemma locally_ball (x : T) (eps : posreal) : locally x (ball x eps%:num).
Proof. by apply/locallyP; exists eps%:num. Qed.
Hint Resolve locally_ball.

Lemma forallN {U} (P : set U) : (forall x, ~ P x) = ~ exists x, P x.
Proof. (*boolP*)
rewrite propeqE; split; first by move=> fP [x /fP].
by move=> nexP x Px; apply: nexP; exists x.
Qed.

Lemma NNP (P : Prop) : (~ ~ P) <-> P. (*boolP*)
Proof. by split=> [nnp|p /(_ p)//]; have [//|/nnp] := asboolP P. Qed.

Lemma eqNNP (P : Prop) : (~ ~ P) = P. (*boolP*)
Proof. by rewrite propeqE NNP. Qed.

Lemma existsN {U} (P : set U) : (exists x, ~ P x) = ~ forall x, P x. (*boolP*)
Proof.
rewrite propeqE; split=> [[x Px] Nall|Nall]; first exact: Px.
by apply/NNP; rewrite -forallN => allP; apply: Nall => x; apply/NNP.
Qed.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : posreal, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : posreal | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallN eqNNP => exNP.
pose D := [set d : R | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma locallyN (x : T) (P : set T) :
  ~ (forall eps : posreal, ~ (ball x eps%:num `<=` ~` P)) ->
  locally x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/locallyP; exists e%:num. Qed.

Lemma locallyN_ball (x : T) (P : set T) :
  locally x (~` P) -> {d : posreal | ball x d%:num `<=` ~` P}.
Proof.
move=> /locallyP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma locally_ex (x : T) (P : T -> Prop) : locally x P ->
  {d : posreal | forall y, ball x d%:num y -> P y}.
Proof.
move=> /locallyP xP.
pose D := [set d : R | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

Lemma flim_close {F} {FF : ProperFilter F} (x y : T) :
  F --> x -> F --> y -> close x y.
Proof.
move=> Fx Fy e; near F have z; [by apply: (@ball_splitl _ z); near: z|].
by end_near; [apply/Fx/locally_ball|apply/Fy/locally_ball].
Qed.

Lemma flimx_close (x y : T) : x --> y -> close x y.
Proof. exact: flim_close. Qed.

End Locally.
Hint Resolve locally_ball.

(** matrices *)

Section matrix_Uniform.

Variables (m n : nat) (T : uniformType).

Implicit Types x y : 'M[T]_(m, n).

Definition mx_ball x (e : R) y := forall i j, ball (x i j) e (y i j).

Lemma mx_ball_center x (e : R) : 0 < e -> mx_ball x e x.
Proof. by move=> ???; apply: ballxx. Qed.

Lemma mx_ball_sym x y (e : R) : mx_ball x e y -> mx_ball y e x.
Proof. by move=> xe_y ??; apply/ball_sym/xe_y. Qed.

Lemma mx_ball_triangle x y z (e1 e2 : R) :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ??; apply: ball_triangle; [apply: xe1_y| apply: ye2_z].
Qed.

Lemma ltr_bigminr (I : finType) (R : realDomainType) (f : I -> R) (x0 x : R) :
  x < x0 -> (forall i, x < f i) -> x < \big[minr/x0]_i f i.
Proof.
move=> ltx0 ltxf; elim/big_ind: _ => // y z ltxy ltxz.
by rewrite ltr_minr ltxy ltxz.
Qed.

Lemma bigminr_ler (I : finType) (R : realDomainType) (f : I -> R) (x0 : R) i :
  \big[minr/x0]_j f j <= f i.
Proof.
have := mem_index_enum i; rewrite unlock; elim: (index_enum I) => //= j l ihl.
by rewrite inE => /orP [/eqP->|/ihl leminlfi];
  rewrite ler_minl ?lerr // leminlfi orbC.
Qed.

Lemma exists2P A (P Q : A -> Prop) :
  (exists2 a, P a & Q a) <-> exists a, P a /\ Q a.
Proof. by split=> [[a ??] | [a []]]; exists a. Qed.

Lemma mx_locally : locally = locally_ mx_ball.
Proof.
rewrite predeq2E => x A; split; last first.
  by move=> [e egt0 xe_A]; exists (fun i j => ball (x i j) (PosNum egt0)%:num).
move=> [P]; rewrite -locally_ballE => x_P sPA.
exists (\big[minr/1]_i \big[minr/1]_j
  get (fun e : R => 0 < e /\ ball (x i j) e `<=` P i j)).
  apply: ltr_bigminr => // i; apply: ltr_bigminr => // j.
  by have /exists2P/getPex [] := x_P i j.
move=> y xmin_y; apply: sPA => i j; have /exists2P/getPex [_] := x_P i j; apply.
apply: ball_ler (xmin_y i j).
by apply: ler_trans (bigminr_ler _ _ i) _; apply: bigminr_ler.
Qed.

Definition matrix_uniformType_mixin :=
  Uniform.Mixin mx_ball_center mx_ball_sym mx_ball_triangle mx_locally.

Canonical matrix_uniformType :=
  UniformType 'M[T]_(m, n) matrix_uniformType_mixin.

End matrix_Uniform.

(** product of two uniform spaces *)

Section prod_Uniform.

Context {U V : uniformType}.
Implicit Types (x y : U * V).

Definition prod_point : U * V := (point, point).

Definition prod_ball x (eps : R) y :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).

Lemma prod_ball_center x (eps : R) : 0 < eps -> prod_ball x eps x.
Proof. by move=> /posnumP[e]; split. Qed.

Lemma prod_ball_sym x y (eps : R) : prod_ball x eps y -> prod_ball y eps x.
Proof. by move=> [bxy1 bxy2]; split; apply: ball_sym. Qed.

Lemma prod_ball_triangle x y z (e1 e2 : R) :
  prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Proof.
by move=> [bxy1 bxy2] [byz1 byz2]; split; eapply ball_triangle; eassumption.
Qed.

Lemma prod_locally : locally = locally_ prod_ball.
Proof.
rewrite predeq2E => -[x y] P; split=> [[[A B] /=[xX yY] XYP] |]; last first.
  by move=> [_ /posnumP[eps] epsP]; exists (ball x eps%:num, ball y eps%:num) => /=.
move: xX yY => /locallyP [_ /posnumP[ex] eX] /locallyP [_ /posnumP[ey] eY].
exists (minr ex%:num ey%:num) => // -[x' y'] [/= xx' yy'].
apply: XYP; split=> /=.
  by apply/eX/(ball_ler _ xx'); rewrite ler_minl lerr.
by apply/eY/(ball_ler _ yy'); rewrite ler_minl lerr orbT.
Qed.

Definition prod_uniformType_mixin :=
  Uniform.Mixin prod_ball_center prod_ball_sym prod_ball_triangle prod_locally.

End prod_Uniform.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (@prod_uniformType_mixin U V).

(** Functional metric spaces *)

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).

Lemma fct_ball_center (x : T -> U) (e : R) : 0 < e -> fct_ball x e x.
Proof. by move=> /posnumP[{e}e] t. Qed.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Proof. by move=> P t; apply: ball_sym. Qed.

Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof. by move=> xy yz t; apply: (@ball_triangle _ (y t)). Qed.

Definition fct_uniformType_mixin :=
  UniformMixin fct_ball_center fct_ball_sym fct_ball_triangle erefl.

Definition fct_topologicalTypeMixin :=
  uniform_TopologicalTypeMixin fct_uniformType_mixin.

Canonical generic_source_filter := @Filtered.Source _ _ _ (locally_ fct_ball).
Canonical fct_topologicalType :=
  TopologicalType (T -> U) fct_topologicalTypeMixin.
Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.

End fct_Uniform.

(** ** Local predicates *)
(** locally_dist *)
(** Where is it used ??*)

Definition locally_dist {T : Type}  :=
  locally_ (fun (d : T -> R) delta => [set y | (d y < (delta : R))%R]).

Global Instance locally_dist_filter T (d : T -> R) : Filter (locally_dist d).
Proof.
apply: filter_from_filter; first by exists 1.
move=> _ _ /posnumP[e1] /posnumP[e2]; exists (minr e1%:num e2%:num) => //.
by move=> P /=; rewrite ltr_minr => /andP [dPe1 dPe2].
Qed.

Section Locally_fct.

Context {T : Type} {U : uniformType}.

Lemma near_ball (y : U) (eps : posreal) :
   \forall y' \near y, ball y eps%:num y'.
Proof. exact: locally_ball. Qed.

Lemma flim_ballP {F} {FF : Filter F} (y : U) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by rewrite -filter_fromP !locally_simpl /=. Qed.
Definition flim_locally := @flim_ballP.

Lemma flim_ball {F} {FF : Filter F} (y : U) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by move/flim_ballP. Qed.

Lemma app_flim_locally {F} {FF : Filter F} (f : T -> U) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: flim_ballP. Qed.

Lemma flimi_ballP {F} {FF : Filter F} (f : T -> U -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Proof.
split=> [Fy _/posnumP[eps] |Fy P] /=; first exact/Fy/locally_ball.
move=> /locallyP[_ /posnumP[eps] subP].
rewrite near_simpl near_mapi; near=> x.
  have [//|z [fxz yz]] := near (Fy _ (posnum_gt0 eps)) x.
  by exists z => //; split => //; apply: subP.
by end_near.
Qed.
Definition flimi_locally := @flimi_ballP.

Lemma flimi_ball {F} {FF : Filter F} (f : T -> U -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/flimi_ballP. Qed.

Lemma flimi_close {F} {FF: ProperFilter F} (f : T -> set U) (l l' : U) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: infer {near F, is_totalfun f} by exact: flim_close fFl fFl'.
apply: filter_app f_prop; near=> x; first split=> //=.
  by have [//|y [fxy _]] := near (flimi_ball fFl [gt0 of 1]) x; exists y.
by end_near.
Qed.
Definition flimi_locally_close := @flimi_close.

End Locally_fct.

Section Locally_fct2.

Context {T : Type} {U V : uniformType}.

Lemma flim_ball2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall y' \near F & z' \near G,
                ball y eps y' /\ ball z eps z'.
Proof. exact: flim_ballP. Qed.

End Locally_fct2.

Lemma flim_const {T} {U : uniformType} {F : set (set T)}
   {FF : Filter F} (a : U) : a @[_ --> F] --> a.
Proof.
move=> P /locallyP[_ /posnumP[eps] subP]; rewrite !near_simpl /=.
by apply: filterE=> ?; apply/subP.
Qed.
Arguments flim_const {T U F FF} a.

Section Cvg.

Context {U : uniformType}.

Lemma close_lim (F1 F2 : set (set U)) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
move=> F12 F21; have [/(flim_trans F21) F2l|dvgF1] := pselect (cvg F1).
  by apply: (@flim_close _ F2) => //; apply: cvgP F2l.
have [/(flim_trans F12)/cvgP//|dvgF2] := pselect (cvg F2).
by rewrite dvgP // dvgP //.
Qed.

Lemma flim_closeP (F : set (set U)) (l : U) : ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Proof.
move=> FF; split=> [Fl|[cvF]Cl].
  by have /cvgP := Fl; split=> //; apply: flim_close.
by apply: flim_trans (close_limxx Cl).
Qed.

End Cvg.
Arguments close_lim {U} F1 F2 {FF2} _.

(** ** Complete uniform spaces *)

(* :TODO: Use cauchy2 alternative to define cauchy? *)
(* Or not: is the fact that cauchy F -/> ProperFilter F a problem? *)
Definition cauchy_ex {T : uniformType} (F : set (set T)) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy {T : uniformType} (F : set (set T)) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_entouragesP (T  : uniformType) (F : set (set T)) :
  Filter F -> cauchy F <-> (F, F) --> entourages.
Proof.
move=> FF; split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply: cauchyF; exists eps%:num.
move=> U [_/posnumP[eps] xyepsU].
by near=> x; [by apply: xyepsU; near: x|end_near; apply: cauchyF].
Qed.

Lemma cvg_cauchy_ex {T : uniformType} (F : set (set T)) :
  [cvg F in T] -> cauchy_ex F.
Proof. by move=> Fl _/posnumP[eps]; exists (lim F); apply/Fl/locally_ball. Qed.

Lemma cauchy_exP (T : uniformType) (F : set (set T)) : Filter F ->
  cauchy_ex F -> cauchy F.
Proof.
move=> FF Fcauchy /= _/posnumP[e].
have [//|x /= Fbx] := Fcauchy (e%:num / 2).
exists ((ball x (e%:num / 2)), (ball x (e%:num / 2))) => //.
by move=> [y z] [/=] /ball_splitr; apply.
Qed.

Lemma cauchyP (T : uniformType) (F : set (set T)) : ProperFilter F ->
  cauchy F <-> cauchy_ex F.
Proof.
move=> FF; split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
near F have x; first by exists x; near: x.
by end_near; apply: (@nearP_dep _ _ F F); apply: Fcauchy.
Qed.

Lemma cvg_cauchy {T : uniformType} (F : set (set T)) : Filter F ->
  [cvg F in T] -> cauchy F.
Proof. by move=> FF /cvg_cauchy_ex /cauchy_exP. Qed.

Module Complete.

Definition axiom (T : uniformType) :=
  forall (F : set (set T)), ProperFilter F -> cauchy F -> F --> lim F.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : axiom (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> Complete.axiom.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : axiom (@Uniform.Pack T b0 T)) :=
  fun bT b of phant_id (Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filteredType := @Filtered.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Notation completeType := type.
Notation "[ 'completeType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completeType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completeType'  'of'  T ]") : form_scope.
Notation CompleteType T m := (@pack T _ m _ _ idfun _ idfun).

End Exports.

End Complete.

Export Complete.Exports.

Section completeType1.

Context {T : completeType}.

Lemma complete_cauchy (F : set (set T)) (FF : ProperFilter F) :
  cauchy F -> F --> lim F.
Proof. by case: T F FF => [? [?]]. Qed.

End completeType1.
Arguments complete_cauchy {T} F {FF} _.

Section matrix_Complete.

Variables (T : completeType) (m n : nat).

Lemma mx_complete (F : set (set 'M[T]_(m, n))) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _) /complete_cauchy cvF :
  cauchy ((fun M : 'M[T]_(m, n) => M _ _) @ F).
  by move=> ?? _ /posnumP[e]; rewrite near_simpl; apply: filterS (Fc _ _).
apply/cvg_ex.
exists (\matrix_(i, j) (lim ((fun M : 'M[T]_(m, n) => M i j) @ F) : T)).
apply/flim_ballP => _ /posnumP[e]; near=> M.
  move=> i j; rewrite mxE; near F have M' => /=.
    by apply: (@ball_splitl _ (M' i j)); last move: (i) (j); near: M'.
  by end_near; [apply/cvF/locally_ball|near: M].
by end_near; apply: nearP_dep; apply: filterS (Fc _ _).
Qed.

Canonical matrix_completeType := CompleteType 'M[T]_(m, n) mx_complete.

End matrix_Complete.

Section fun_Complete.

Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set (set (T -> U)))
  {FF :  ProperFilter F} : cauchy F -> cvg F.
Proof.
move=> Fc; have /(_ _) /complete_cauchy Ft_cvg : cauchy (@^~_ @ F).
  by move=> t e ?; rewrite near_simpl; apply: filterS (Fc _ _).
apply/cvg_ex; exists (fun t => lim (@^~t @ F)).
apply/flim_ballP => _ /posnumP[e]; near=> f => [t|].
  near F have g => /=.
    by apply: (@ball_splitl _ (g t)); last move: (t); near: g.
  by end_near; [exact/Ft_cvg/locally_ball|near: f].
by end_near; apply: nearP_dep; apply: filterS (Fc _ _).
Qed.

Canonical fun_completeType := CompleteType (T -> U) fun_complete.

End fun_Complete.

(** ** Limit switching *)

Section Flim_switch.

Context {T1 T2 : choiceType}.

Lemma flim_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/flim_ballP => _ /posnumP[eps]; rewrite !near_simpl.
near F1 have x; first near=> y.
+ apply: (@ball_split _ (h x)); first by near: x.
  apply: (@ball_split _ (f x y)); first by near: y.
  by apply/ball_sym; move: (y); near: x.
+ by end_near; apply/fh/locally_ball.
end_near; first exact/hl/locally_ball.
by have /flim_locally /= := fg; apply.
Qed.

Lemma flim_switch_2 {U : completeType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : ProperFilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Proof.
move=> fg fh; apply: complete_cauchy => _/posnumP[e] /=; rewrite !near_simpl.
near=> x x'=> /=; [near F2 have y|].
+ apply: (@ball_splitl _ (f x y)); first by near: y.
  apply: (@ball_split _ (f x' y)); first by near: y.
  by apply: (@ball_splitr _ (g y)); move: (y); [near: x'|near: x].
+ by end_near; apply/fh/locally_ball.
by split; end_near; have /flim_locally /= := fg; apply.
Qed.

(* Alternative version *)
(* Lemma flim_switch {U : completeType} *)
(*   F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) : *)
(*   [cvg f @ F1 in T2 -> U] -> (forall x, [cvg f x @ F2 in U]) -> *)
(*   [/\ [cvg [lim f @ F1] @ F2 in U], [cvg (fun x => [lim f x @ F2]) @ F1 in U] *)
(*   & [lim [lim f @ F1] @ F2] = [lim (fun x => [lim f x @ F2]) @ F1]]. *)
Lemma flim_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
move=> Hfg Hfh; have hcv := !! flim_switch_2 Hfg Hfh.
by exists [lim h @ F1 in U]; split=> //; apply: flim_switch_1 Hfg Hfh hcv.
Qed.

End Flim_switch.

(** ** Modules with a norm *)

Reserved Notation  "`|[ x ]|" (at level 0, x at level 99, format "`|[ x ]|").

Module NormedModule.

Record mixin_of (K : absRingType) (V : lmodType K) loc (m : @Uniform.mixin_of V loc) := Mixin {
  norm : V -> R ;
  ax1 : forall (x y : V), norm (x + y) <= norm x + norm y ;
  ax2 : forall (l : K) (x : V), norm (l *: x) <= abs l * norm x;
  ax3 : Uniform.ball m = ball_ norm;
  ax4 : forall x : V, norm x = 0 -> x = 0
}.

Section ClassDef.

Variable K : absRingType.

Record class_of (T : Type) := Class {
  base : GRing.Lmodule.class_of K T ;
  pointed_mixin : Pointed.point_of T ;
  locally_mixin : Filtered.locally_of T T ;
  topological_mixin : @Topological.mixin_of T locally_mixin ;
  uniform_mixin : @Uniform.mixin_of T locally_mixin;
  mixin : @mixin_of _ (@GRing.Lmodule.Pack K (Phant K) T base T) _ uniform_mixin
}.
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Definition base2 T (c : class_of T) :=
  @Uniform.Class _
    (@Topological.Class _
      (Filtered.Class
       (Pointed.Class (@base T c) (pointed_mixin c))
       (locally_mixin c))
      (topological_mixin c))
    (uniform_mixin c).
Local Coercion base2 : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phK T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0 um0 (m0 : @mixin_of _ (@GRing.Lmodule.Pack K (Phant K) T b0 T) l0 um0) :=
  fun bT b & phant_id (@GRing.Lmodule.class K phK bT) b =>
  fun ubT (ub : Uniform.class_of _) & phant_id (@Uniform.class ubT) ub =>
  fun   m & phant_id m0 m => Pack phK (@Class T b ub ub ub ub m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass xT.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filteredType := @Filtered.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.
Definition join_zmodType := @GRing.Zmodule.Pack uniformType xclass xT.
Definition join_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass xT.
End ClassDef.

Module Exports.

Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
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
Canonical join_zmodType.
Canonical join_lmodType.

Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ _ m _ _ id _ _ id _ id).
Notation NormedModMixin := Mixin.
Notation "[ 'normedModType' K 'of' T 'for' cT ]" := (@clone _ (Phant K) T cT _ idfun)
  (at level 0, format "[ 'normedModType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'normedModType' K 'of' T ]" := (@clone _ (Phant K) T _ _ id)
  (at level 0, format "[ 'normedModType'  K  'of'  T ]") : form_scope.

End Exports.

End NormedModule.

Export NormedModule.Exports.

Definition norm {K : absRingType} {V : normedModType K} : V -> R :=
  NormedModule.norm (NormedModule.class _).
Notation "`|[ x ]|" := (norm x) : ring_scope.

Section NormedModule1.
Context {K : absRingType} {V : normedModType K}.
Implicit Types (l : K) (x y : V) (eps : posreal).

Lemma ler_normm_add x y : `|[x + y]| <= `|[x]| + `|[y]|.
Proof. exact: NormedModule.ax1. Qed.

Lemma ler_normmZ l x : `|[l *: x]| <= `|l|%real * `|[x]|.
Proof. exact: NormedModule.ax2. Qed.

Notation ball_norm := (ball_ (@norm K V)).

Notation locally_norm := (locally_ ball_norm).

Lemma ball_normE : ball_norm = ball.
Proof. by rewrite -NormedModule.ax3. Qed.

Lemma normm0_eq0 x : `|[x]| = 0 -> x = 0.
Proof. exact: NormedModule.ax4. Qed.

Lemma normmN x : `|[- x]| = `|[x]|.
Proof.
gen have le_absN1 : x / `|[- x]| <= `|[x]|.
  by rewrite -scaleN1r (ler_trans (ler_normmZ _ _)) //= absrN1 mul1r.
by apply/eqP; rewrite eqr_le le_absN1 /= -{1}[x]opprK le_absN1.
Qed.

Lemma normmB x y : `|[x - y]| = `|[y - x]|.
Proof. by rewrite -normmN opprB. Qed.

Lemma normm0 : `|[0 : V]| = 0.
Proof.
apply/eqP; rewrite eqr_le; apply/andP; split.
  by rewrite -{1}(scale0r 0) (ler_trans (ler_normmZ _ _)) ?absr0 ?mul0r.
by rewrite -(ler_add2r `|[0 : V]|) add0r -{1}[0 : V]add0r ler_normm_add.
Qed.
Hint Resolve normm0.

Lemma normm_eq0 x : (`|[x]| == 0) = (x == 0).
Proof. by apply/eqP/eqP=> [/normm0_eq0|->//]. Qed.

Lemma normm_ge0 x : 0 <= `|[x]|.
Proof.
rewrite -(@pmulr_rge0 _ 2) // mulr2n mulrDl !mul1r.
by rewrite -{2}normmN (ler_trans _ (ler_normm_add _ _)) // subrr normm0.
Qed.

Lemma normm_gt0 x : (0 < `|[x]|) = (x != 0).
Proof. by rewrite ltr_def normm_eq0 normm_ge0 andbT. Qed.

Lemma normm_lt0 x : (`|[x]| < 0) = false.
Proof. by rewrite ltrNge normm_ge0. Qed.

Lemma normm_le0 x : (`|[x]| <= 0) = (x == 0).
Proof. by rewrite lerNgt normm_gt0 negbK. Qed.

Lemma absRE (x : R) : `|x|%real = `|x|%R.
Proof. by []. Qed.

Lemma ler_distm_dist x y : `| `|[x]| - `|[y]| | <= `|[x - y]|.
Proof.
wlog gt_xy : x y / `|[x]| >= `|[y]| => [hw|].
  by have [/hw//|/ltrW/hw] := lerP `|[y]| `|[x]|; rewrite absRE distrC normmB.
rewrite absRE ger0_norm ?subr_ge0 // ler_subl_addr.
by rewrite -{1}[x](addrNK y) ler_normm_add.
Qed.

Lemma closeE x y : close x y = (x = y).
Proof.
rewrite propeqE; split => [cl_xy|->//]; have [//|neq_xy] := eqVneq x y.
have dxy_gt0 : `|[x - y]| > 0 by rewrite normm_gt0 subr_eq0.
have dxy_ge0 := ltrW dxy_gt0.
have := cl_xy ((PosNum dxy_gt0)%:num / 2)%:pos.
rewrite -ball_normE /= -subr_lt0 ler_gtF //.
rewrite -[X in X - _]mulr1 -mulrBr mulr_ge0 //.
by rewrite subr_ge0 -(@ler_pmul2r _ 2) // mulVf // mul1r ler1n.
Qed.
Lemma eq_close x y : close x y -> x = y. by rewrite closeE. Qed.

Lemma locally_le_locally_norm x : flim (locally x) (locally_norm x).
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

Lemma locally_norm_ball_norm x (e : posreal) :
  locally_norm x (ball_norm x e%:num).
Proof. by exists e%:num. Qed.

Lemma locally_norm_ball x (eps : posreal) : locally_norm x (ball x eps%:num).
Proof. rewrite locally_locally_norm; by apply: locally_ball. Qed.

Lemma locally_ball_norm (x : V) (eps : posreal) : locally x (ball_norm x eps%:num).
Proof. rewrite -locally_locally_norm; apply: locally_norm_ball_norm. Qed.

Lemma ball_norm_triangle (x y z : V) (e1 e2 : R) :
  ball_norm x e1 y -> ball_norm y e2 z -> ball_norm x (e1 + e2) z.
Proof.
rewrite /ball_norm => H1 H2; rewrite (subr_trans y).
by rewrite (ler_lt_trans (ler_normm_add _ _)) ?ltr_add.
Qed.

Lemma ball_norm_center (x : V) (e : posreal) : ball_norm x e%:num x.
Proof. by rewrite /ball_norm subrr normm0. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm -opprB normmN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /ltr_le_trans; apply. Qed.

Lemma norm_close x y : close x y = (forall eps : posreal, ball_norm x eps%:num y).
Proof. by rewrite propeqE ball_normE. Qed.

Lemma ball_norm_eq x y : (forall eps : posreal, ball_norm x eps%:num y) -> x = y.
Proof. by rewrite -norm_close closeE. Qed.

Lemma flim_unique {F} {FF : ProperFilter F} :
  is_prop [set x : V | F --> x].
Proof. by move=> Fx Fy; rewrite -closeE; apply: flim_close. Qed.

Lemma locally_flim_unique (x y : V) : x --> y -> x = y.
Proof. by rewrite -closeE; apply: flim_close. Qed.

Lemma lim_id (x : V) : lim x = x.
Proof. by symmetry; apply: locally_flim_unique; apply/cvg_ex; exists x. Qed.

End NormedModule1.

Module Export LocallyNorm.
Definition locally_simpl := (locally_simpl,@locally_locally_norm,@filter_from_norm_locally).
End LocallyNorm.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @locally_normE,
   @filter_from_normE, @near_locally_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Section NormedModule2.

Context {T : Type} {K : absRingType} {V : normedModType K}.

Lemma flimi_unique {F} {FF : ProperFilter F} (f : T -> set V) :
  {near F, is_fun f} -> is_prop [set x : V | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE; apply: flimi_close. Qed.

Lemma flim_normP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, `|[y - y']| < eps.
Proof. by rewrite -filter_fromP /= !locally_simpl. Qed.

Lemma flim_normW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps : R, 0 < eps -> \forall y' \near F, `|[y - y']| <= eps) ->
  F --> y.
Proof.
move=> cv; apply/flim_normP => _/posnumP[e]; near=> x.
  by rewrite [e%:num]splitr ltr_spaddl //; near: x.
by end_near; apply: cv.
Qed.

Lemma flim_norm {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|[y - y']| < eps.
Proof. by move=> /flim_normP. Qed.

Lemma flim_bounded {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall M, M > `|[y]| -> \forall y' \near F, `|[y']|%real < M.
Proof.
move=> /flim_norm Fy M; rewrite -subr_gt0 => subM_gt0; have := Fy _ subM_gt0.
apply: filterS => y' yy'; rewrite -(@ltr_add2r _ (- `|[y]|)).
rewrite (ler_lt_trans _ yy') //.
by rewrite (ler_trans _ (ler_distm_dist _ _)) // absRE distrC ler_norm.
Qed.

End NormedModule2.
Hint Resolve normm_ge0.
Arguments flim_norm {_ _ F FF}.
Arguments flim_bounded {_ _ F FF}.

(** ** Matrices *)

Section matrix_normedMod.

Variables (K : absRingType) (m n : nat).

(* take m.+1, n.+1 because ball_normE is not provable for m = 0 or n = 0 *)
Definition mx_norm (x : 'M[K]_(m.+1, n.+1)) :=
  bigmaxr 0 [seq `|x ij.1 ij.2| | ij : 'I_m.+1 * 'I_n.+1].

Program Definition matrix_NormedModMixin :=
  @NormedModMixin _ _
    (@locally _ [filteredType 'M[K]_(m.+1, n.+1) of 'M[K]_(m.+1, n.+1)])
    (Uniform.mixin (Uniform.class _)) mx_norm _ _ _ _.
Next Obligation.
apply/bigmaxr_lerP=> [|i]; rewrite size_map -cardT mxvec_cast // => ltimn.
rewrite (nth_map (ord0, ord0)); last by rewrite -cardT mxvec_cast.
rewrite mxE; apply: ler_trans (ler_abs_add _ _) _.
do 2 ?[rewrite -(nth_map _ 0 (fun p => `|_ p.1 p.2|)) -?cardT ?mxvec_cast //].
by apply: ler_add; apply: bigmaxr_ler; rewrite size_map -cardT mxvec_cast.
Qed.
Next Obligation.
apply/bigmaxr_lerP => [|i]; rewrite size_map -cardT mxvec_cast // => ltimn.
rewrite (nth_map (ord0, ord0)); last by rewrite -cardT mxvec_cast.
rewrite mxE; apply: ler_trans (absrM _ _) _; apply: ler_pmul => //.
rewrite -(nth_map _ 0 (fun p => `|x p.1 p.2|)).
  by apply: bigmaxr_ler; rewrite size_map -cardT mxvec_cast.
by rewrite -cardT mxvec_cast.
Qed.
Next Obligation.
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
Next Obligation.
apply/matrixP => i j; rewrite mxE; apply/eqP.
rewrite -absr_eq0 eqr_le; apply/andP; split; last exact: absr_ge0.
have /(bigmaxr_ler 0) :
  (index (i, j) (enum [finType of 'I_m.+1 * 'I_n.+1]) <
   size [seq `|x ij.1 ij.2| | ij : 'I_m.+1 * 'I_n.+1])%N.
  by rewrite size_map index_mem mem_enum.
rewrite -{3}H; apply: ler_trans.
rewrite (nth_map (ord0, ord0)); last by rewrite index_mem mem_enum.
by rewrite nth_index // mem_enum.
Qed.

Canonical matrix_normedModType :=
  NormedModType K 'M[K]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_normedMod.

(** ** Pairs *)

Section prod_NormedModule.

Context {K : absRingType} {U V : normedModType K}.

Definition prod_norm (x : U * V) := maxr `|[x.1]| `|[x.2]|.

Lemma prod_norm_triangle : forall x y : U * V, prod_norm (x + y) <= prod_norm x + prod_norm y.
Proof.
by move=> [xu xv] [yu yv]; rewrite ler_maxl /=; apply/andP; split;
  apply: ler_trans (ler_normm_add _ _) _; apply: ler_add;
  rewrite ler_maxr lerr // orbC.
Qed.

Lemma prod_norm_scal (l : K) : forall (x : U * V), prod_norm (l *: x) <= abs l * prod_norm x.
Proof.
by move=> [xu xv]; rewrite /prod_norm /= ler_maxl; apply/andP; split;
  apply: ler_trans (ler_normmZ _ _) _; apply: ler_wpmul2l => //;
  rewrite ler_maxr lerr // orbC.
Qed.

Lemma ball_prod_normE : ball = ball_ prod_norm.
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
by rewrite /ball /= /prod_ball -!ball_normE /ball_ ltr_maxl; split=> /andP.
Qed.

Lemma prod_norm_eq0 (x : U * V) : prod_norm x = 0 -> x = 0.
Proof.
case: x => [xu xv]; rewrite /prod_norm /= => nx0.
suff /andP [/eqP -> /eqP ->] : (xu == 0) && (xv == 0) by [].
rewrite -!normm_eq0 !eqr_le !normm_ge0.
have : maxr `|[xu]| `|[xv]| <= 0 by rewrite nx0 lerr.
by rewrite ler_maxl => /andP [-> ->].
Qed.

End prod_NormedModule.

Definition prod_NormedModule_mixin (K : absRingType) (U V : normedModType K) :=
  @NormedModMixin K _ _ _ (@prod_norm K U V) prod_norm_triangle
  prod_norm_scal ball_prod_normE prod_norm_eq0.

Canonical prod_NormedModule (K : absRingType) (U V : normedModType K) :=
  NormedModType K (U * V) (@prod_NormedModule_mixin K U V).

Section NormedModule3.

Context {T : Type} {K : absRingType} {U : normedModType K}
                   {V : normedModType K}.

Lemma flim_norm2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, 0 < eps ->
   \forall y' \near F & z' \near G, `|[(y, z) - (y', z')]| < eps.
Proof. exact: flim_normP. Qed.

(* Lemma flim_norm_supP {F : set (set U)} {G : set (set V)} *)
(*   {FF : Filter F} {FG : Filter G} (y : U) (z : V): *)
(*   (F, G) --> (y, z) <-> *)
(*   forall eps : posreal, {near F & G, forall y' z', *)
(*           (`|[y - y']| < eps) /\ (`|[z - z']| < eps) }. *)
(* Proof. *)
(* rewrite flim_ballP; split => [] P eps. *)
(* - have [[A B] /=[FA GB] ABP] := P eps; exists (A, B) => -//[a b] [/= Aa Bb]. *)
(*   apply/andP; rewrite -ltr_maxl. *)
(*   have /= := (@sub_ball_norm_rev _ _ (_, _)). *)

Lemma flim_norm2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps : R, 0 < eps ->
   \forall y' \near F & z' \near G, `|[(y, z) - (y', z')]| < eps.
Proof. by rewrite flim_normP. Qed.

End NormedModule3.
Arguments flim_norm2 {_ _ _ F G FF FG}.

(** Rings with absolute values are normed modules *)

Section AbsRing_NormedModule.

Variable (K : absRingType).
Implicit Types (x y : K) (eps : R).

Lemma ball_absE : ball = ball_ (@abs K).
Proof. by []. Qed.

Definition AbsRing_NormedModMixin := @NormedModule.Mixin K _ _ _
  (abs : K^o -> R) ler_abs_add absrM ball_absE absr0_eq0.

Canonical AbsRing_NormedModType := NormedModType K K^o AbsRing_NormedModMixin.

End AbsRing_NormedModule.

(* Quick fix for non inferred instances *)
(* This does not fix everything, see below *)
Instance NormedModule_locally_filter (K : absRingType) (V : normedModType K)
  (p : V) :
  @ProperFilter (@NormedModule.sort K (Phant K) V)
  (@locally (@NormedModule.uniformType K (Phant K) V) _ p).
Proof. exact: locally_filter. Qed.

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : absRingType} {V : normedModType K}.

Lemma flim_add : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/=x y]; apply/flim_normP=> _/posnumP[e].
rewrite !near_simpl /=; near=> a b.
  rewrite opprD addrACA [e%:num]splitr (ler_lt_trans (ler_normm_add _ _)) //.
  by rewrite ltr_add //=; [near: a|near: b].
by split; end_near=> /=; apply: flim_norm.
Qed.


Lemma flim_scal : continuous (fun z : K * V => z.1 *: z.2).
Proof.
move=> [k x]; apply/flim_normP=> _/posnumP[e].
rewrite !near_simpl /=; near=> z.
  rewrite (@subr_trans _ (k *: z.2)).
  rewrite (splitr e%:num) (ler_lt_trans (ler_normm_add _ _)) //.
  rewrite ltr_add // -?(scalerBr, scalerBl).
    rewrite (ler_lt_trans (ler_normmZ _ _)) //.
    rewrite (ler_lt_trans (ler_pmul _ _ (_ : _ <= `|k|%real + 1) (lerr _)))
            ?ler_addl//.
    by rewrite -ltr_pdivl_mull // ?(ltr_le_trans ltr01) ?ler_addr //; near: z.
  rewrite (ler_lt_trans (ler_normmZ _ _)) //.
  rewrite (ler_lt_trans (ler_pmul _ _ (lerr _) (_ : _ <= `|[x]| + 1))) //.
    by rewrite ltrW //; near: z.
  rewrite -ltr_pdivl_mulr // ?(ltr_le_trans ltr01) ?ler_addr //.
  by near: z.
end_near; rewrite /= ?near_simpl.
- by apply: (flim_norm _ flim_snd); rewrite mulr_gt0 // ?invr_gt0 ltr_paddl.
- by apply: (flim_bounded _ flim_snd); rewrite ltr_addl.
- apply: (flim_norm (_ : K^o) flim_fst).
  by rewrite mulr_gt0// ?invr_gt0 ltr_paddl.
Qed.
Arguments flim_scal _ _ : clear implicits.

Lemma flim_scalr k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (flim_comp2 (flim_const _) flim_id (flim_scal (_, _))).
Qed.

Lemma flim_scall (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (flim_comp2 flim_id (flim_const _) (flim_scal (_, _))).
Qed.

Lemma flim_opp : continuous (@GRing.opp V).
Proof.
move=> x; rewrite -scaleN1r => P /flim_scalr /=.
rewrite !locally_nearE near_map.
by apply: filterS => x'; rewrite scaleN1r.
Qed.

End NVS_continuity.

Lemma flim_mult {K : absRingType} (x y : K) :
   z.1 * z.2 @[z --> (x, y)] --> x * y.
Proof. exact: (@flim_scal _ (AbsRing_NormedModType K)). Qed.


(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : absRingType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : Complete.class_of T :=
  @Complete.Class _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack :=
  fun bT b & phant_id (@NormedModule.class K phK bT) (b : NormedModule.class_of K T) =>
  fun mT m & phant_id (@Complete.class mT) (@Complete.Class T b m) =>
    Pack phK (@Class T b m) T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass xT.
Definition pointedType := @Pointed.Pack cT xclass xT.
Definition filteredType := @Filtered.Pack cT cT xclass xT.
Definition topologicalType := @Topological.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.
Definition completeType := @Complete.Pack cT xclass xT.
Definition join_zmodType := @GRing.Zmodule.Pack uniformType xclass xT.
Definition join_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass xT.
Definition normedModType := @NormedModule.Pack K phK cT xclass xT.
Definition join_uniformType := @Uniform.Pack normedModType xclass xT.
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
Canonical join_zmodType.
Canonical join_lmodType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Canonical join_uniformType.
Notation completeNormedModType K := (type (Phant K)).
Notation "[ 'completeNormedModType' K 'of' T ]" := (@pack _ (Phant K) T _ _ id _ _ id)
  (at level 0, format "[ 'completeNormedModType'  K  'of'  T ]") : form_scope.

End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

Section CompleteNormedModule1.

Context {K : absRingType} {V : completeNormedModType K}.

Lemma flim_lim {F} {FF : ProperFilter F} (l : V) :
  F --> l -> lim F = l.
Proof. by move=> Fl; have Fcv := cvgP Fl; apply: flim_unique. Qed.

Context {T : Type}.

Lemma flim_map_lim {F} {FF : ProperFilter F} (f : T -> V) l :
  f @ F --> l -> lim (f @ F) = l.
Proof. exact: flim_lim. Qed.

Lemma flimi_map_lim {F} {FF : ProperFilter F} (f : T -> V -> Prop) l :
  F (fun x => is_prop (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
move=> f_prop f_l; apply: get_unique => // l' f_l'.
exact: flimi_unique _ f_l' f_l.
Qed.

End CompleteNormedModule1.

(** * Extended Types *)

(** * The topology on natural numbers *)

(* :TODO: ultimately nat could be replaced by any lattice *)
Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Canonical eventually_filter_source X :=
   @Filtered.Source X _ nat (fun f => f @ \oo).

Global Instance eventually_filter : ProperFilter eventually.
Proof.
eapply @filter_from_proper; last by move=> i _; exists i.
apply: filter_fromT_filter; first by exists 0%N.
move=> i j; exists (maxn i j) => n //=.
by rewrite geq_max => /andP[ltin ltjn].
Qed.

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

Lemma filterP_strong T (F : set (set T)) {FF : Filter F} (P : set T) :
  (exists Q : set T, exists FQ  : F Q, forall x : T, Q x -> P x) <-> F P.
Proof.
split; last by exists P.
by move=> [Q [FQ QP]]; apply: (filterS QP).
Qed.

(* :TODO: add to mathcomp *)
Lemma ltr_distW (R : realDomainType) (x y e : R):
   (`|x - y|%R < e) -> y - e < x.
Proof. by rewrite ltr_distl => /andP[]. Qed.

(* :TODO: add to mathcomp *)
Lemma ler_distW (R : realDomainType) (x y e : R):
   (`|x - y|%R <= e) -> y - e <= x.
Proof. by rewrite ler_distl => /andP[]. Qed.

Lemma R_complete (F : set (set R)) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down (mem A)).
have /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup (mem D); first split.
- exists (x0 - 1); rewrite in_setE => A FA.
  apply/existsbP; near F have x; first exists x.
    by rewrite ler_distW 1?distrC 1?ltrW ?andbT ?in_setE //; near: x.
  end_near.
- exists (x0 + 1); apply/forallbP => x; apply/implyP; rewrite in_setE.
  move=> /(_ _ x01) /existsbP [y /andP[]]; rewrite in_setE.
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltr_subl_addr => /andP[/ltrW].
  by move=> /(ler_trans _) yx01 _ /yx01.
exists (sup (mem D)).
apply: (flim_normW (_ : R^o)) => /= _ /posnumP[eps]; near=> x.
  rewrite ler_distl sup_upper_bound //=.
    apply: sup_le_ub => //; first by case: D_has_sup.
    apply/forallbP => y; apply/implyP; rewrite in_setE.
    move=> /(_ (ball_ norm x eps%:num) _) /existsbP []; first by near: x.
    move=> z /andP[]; rewrite in_setE /ball_ ltr_distl ltr_subl_addr.
    by move=> /andP [/ltrW /(ler_trans _) le_xeps _ /le_xeps].
  rewrite in_setE /D /= => A FA; near F have y.
    apply/existsbP; exists y; apply/andP; split.
      by rewrite in_setE; near: y.
    rewrite ler_subl_addl -ler_subl_addr ltrW //.
    by suff: `|x - y| < eps%:num; [by rewrite ltr_norml => /andP[_] | near: y].
  end_near; near: x.
by end_near; rewrite /= !near_simpl; apply: nearP_dep; apply: F_cauchy.
Qed.

Canonical R_completeType := CompleteType R R_complete.
Canonical R_NormedModule := [normedModType R of R^o].
Canonical R_CompleteNormedModule := [completeNormedModType R of R^o].

Definition at_left x := within (fun u : R => u < x) (locally x).
Definition at_right x := within (fun u : R => x < u) (locally x).
(* :TODO: We should have filter notation ^- and ^+ for these *)

Global Instance at_right_proper_filter (x : R) : ProperFilter (at_right x).
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x + d%:num / 2))].
apply; last (by rewrite ltr_addl); rewrite /AbsRing_ball /=.
rewrite opprD !addrA subrr add0r absrN absRE normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter (at_left x).
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last (by rewrite ltr_subl_addl ltr_addr); rewrite /AbsRing_ball /=.
rewrite opprD !addrA subrr add0r opprK absRE normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

(** Continuity of norm *)

Lemma continuous_norm {K : absRingType} {V : normedModType K} :
  continuous (@norm _ V).
Proof.
move=> x; apply/(@flim_normP _ [normedModType R of R^o]) => _/posnumP[e] /=.
rewrite !near_simpl; apply/locally_normP; exists e%:num => // y Hy.
exact/(ler_lt_trans (ler_distm_dist _ _)).
Qed.

(* :TODO: yet, not used anywhere?! *)
Lemma flim_norm0 {U} {K : absRingType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|[f x]|) @ F --> (0 : R)
  -> f @ F --> (0 : V).
Proof.
move=> /(flim_norm (_ : R^o)) fx0; apply/flim_normP => _/posnumP[e].
rewrite near_simpl; have := fx0 _ [gt0 of e%:num]; rewrite near_simpl.
by apply: filterS => x; rewrite !sub0r !normmN [ `|[_]| ]ger0_norm.
Qed.

Lemma cvg_seq_bounded {K : absRingType} {V : normedModType K} (a : nat -> V) :
  [cvg a in V] -> {M : R | forall n, norm (a n) <= M}.
Proof.
move=> a_cvg; suff: exists M, forall n, norm (a n) <= M.
  by move=> /getPex; set M := get _; exists M.
pose M := `|[lim (a @ \oo)]| + 1.
have [] := !! flim_bounded _ a_cvg M; first by rewrite ltr_addl.
move=> N /= _ /(_ _ _) /ltrW a_leM.
exists (maxr M (\big[maxr/M]_(n < N) `|[a (val (rev_ord n))]|)) => /= n.
rewrite ler_maxr; have [nN|nN] := leqP N n; first by rewrite a_leM.
apply/orP; right => {a_leM}; elim: N n nN=> //= N IHN n.
rewrite leq_eqVlt => /orP[/eqP[->] |/IHN a_le];
by rewrite big_ord_recl subn1 /= ler_maxr ?a_le ?lerr ?orbT.
Qed.

(** Some open sets of [R] *)

Lemma open_lt (y : R) : open (< y).
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0; exists (y - x) => // z.
by rewrite /AbsRing_ball /= absrB ltr_distl addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt.

Lemma open_gt (y : R) : open (> y).
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /AbsRing_ball /= absrB ltr_distl opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt.

Lemma open_neq (y : R) : open (xpredC (eq_op^~ y)).
Proof.
rewrite (_ : xpredC _ = (< y) `|` (> y) :> set _) /=.
  by apply: openU => //; apply: open_lt.
rewrite predeqE => x /=; rewrite eqr_le !lerNgt negb_and !negbK orbC.
by symmetry; apply (rwP orP).
Qed.

(** Some closed sets of [R] *)

Lemma closed_le (y : R) : closed (<= y).
Proof.
rewrite (_ : (<= _) = ~` (> y) :> set _).
  by apply: closedN; exact: open_gt.
by rewrite predeqE => x /=; rewrite lerNgt; split => /negP.
Qed.

Lemma closed_ge (y : R) : closed (>= y).
Proof.
rewrite (_ : (>= _) = ~` (< y) :> set _).
  by apply: closedN; exact: open_lt.
by rewrite predeqE => x /=; rewrite lerNgt; split => /negP.
Qed.

Lemma closed_eq (y : R) : closed (eq^~ y).
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: closedN; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

(** Local properties in [R] *)

Lemma locally_interval (P : R -> Prop) (x : R) (a b : Rbar) :
  Rbar_lt a x -> Rbar_lt x b ->
  (forall (y : R), Rbar_lt a y -> Rbar_lt y b -> P y) ->
  locally x P.
Proof.
move => Hax Hxb Hp; case: (Rbar_lt_locally _ _ _ Hax Hxb) => d Hd.
exists d%:num => //= y; rewrite /AbsRing_ball /= absrB.
by move=> /Hd /andP[??]; apply: Hp.
Qed.

(** * Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : posreal, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
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

Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R):
  (\near x & y, P x y) ->
  \forall u \near x & v \near y,
      forall (t : R), 0 <= t <= 1 ->
      \forall z \near t, \forall a \near (x + z * (u - x))
                               & b \near (y + z * (v - y)), P a b.
Proof.
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
(*   set d1 := mkposreal _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mkposreal _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [posreal of d1 / 2] => //= pq Hpq. *)
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
Admitted.

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
(*   {d : posreal | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

(** * Some Topology on [Rbar] *)

(* NB: already defined in R_scope in Rbar.v *)
Notation "'+oo'" := p_infty : real_scope.
Notation "'-oo'" := m_infty : real_scope.

Definition Rbar_locally' (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally' a P
    | +oo => exists M : R, forall x, M < x -> P x
    | -oo => exists M : R, forall x, x < M -> P x
  end.
Definition Rbar_locally (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally a P
    | +oo => exists M : R, forall x, M < x -> P x
    | -oo => exists M : R, forall x, x < M -> P x
  end.

Canonical Rbar_eqType := EqType Rbar gen_eqMixin.
Canonical Rbar_choiceType := ChoiceType Rbar gen_choiceMixin.
Canonical Rbar_pointed := PointedType Rbar (+oo).
Canonical Rbar_filter := FilteredType R Rbar (Rbar_locally).

Global Instance Rbar_locally'_filter : forall x, ProperFilter (Rbar_locally' x).
Proof.
(* move=> [x| |] ; (constructor ; [idtac | constructor]). *)
(* - case => _/posnumP[eps] HP. *)
(*   apply: (HP (x + (eps : R) / 2)). *)
(*     rewrite /ball /= /AbsRing_ball opprD addrA subrr add0r absrN. *)
(*     rewrite !absRE normf_div !ger0_norm // ltr_pdivr_mulr //. *)
(*     by rewrite mulr_natr mulr2n ltr_addr. *)
(*   move/eqP; rewrite eq_sym addrC -subr_eq subrr => /eqP. *)
(*   by apply/eqP; rewrite ltr_eqF. *)
(* - now exists 1. *)
(* - move=> P Q [_/posnumP[dP] HP] [_/posnumP[dQ] HQ]. *)
(*   exists (Num.min (dP : R) (dQ : R)) => // y Hy H; split. *)
(*   + apply/(HP _ _ H)/sub_abs_ball; move/sub_ball_abs : Hy; rewrite mul1r /=. *)
(*     move/ltr_le_trans; apply; by rewrite ler_minl lerr. *)
(*   + apply/(HQ _ _ H)/sub_abs_ball; move/sub_ball_abs : Hy. *)
(*     rewrite mul1r /= => /ltr_le_trans; apply;  by rewrite ler_minl lerr orbT. *)
(* - move=> P Q H [_ /posnumP[dP] HP]. *)
(*   exists dP => // y Hy H'; by apply/H/HP. *)
(* - case=> N HP. *)
(*   apply: (HP (N + 1)). *)
(*   by rewrite ltr_addl. *)
(* - now exists 0. *)
(* - move=> P Q [MP HP] [MQ HQ]. *)
(*   exists (Num.max MP MQ) => y Hy; split. *)
(*   + apply: HP; by rewrite (ler_lt_trans _ Hy) // ler_maxr lerr. *)
(*   + apply: HQ; by rewrite (ler_lt_trans _ Hy) // ler_maxr lerr orbT. *)
(* - move=> P Q H [dP HP]. *)
(*   exists dP => y Hy; by apply/H/HP. *)
(* - case=> N HP. *)
(*   apply: (HP (N - 1)). *)
(*   by rewrite ltr_subl_addl ltr_addr. *)
(* - now exists 0. *)
(* - move=> P Q [MP HP] [MQ HQ]. *)
(*   exists (Num.min MP MQ) => y Hy; split. *)
(*   + apply/HP/(ltr_le_trans Hy); by rewrite ler_minl lerr. *)
(*   + apply/HQ/(ltr_le_trans Hy); by rewrite ler_minl lerr orbT. *)
(* - move=> P Q H [dP HP]. *)
(*   exists dP => y Hy; by apply/H/HP. *)
(* Qed. *)
Admitted.

Global Instance Rbar_locally_filter : forall x, ProperFilter (Rbar_locally x).
Proof.
case=> [x||].
by apply/locally_filter.
exact: (Rbar_locally'_filter +oo).
exact: (Rbar_locally'_filter -oo).
Qed.

(** Open sets in [Rbar] *)

Lemma open_Rbar_lt y : open (fun u : R => Rbar_lt u y).
Proof.
case: y => [y||] /=.
exact: open_lt.
by rewrite trueE; apply: openT.
by rewrite falseE; apply: open0.
Qed.

Lemma open_Rbar_gt y : open (fun u : R => Rbar_lt y u).
Proof.
case: y => [y||] /=.
exact: open_gt.
by rewrite falseE; apply: open0.
by rewrite trueE; apply: openT.
Qed.

Lemma open_Rbar_lt' x y : Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
case: x => [x|//|] xy; first exact: open_Rbar_lt.
case: y => [y||//] /= in xy *.
exists y => /= x ? //.
by exists 0.
Qed.

Lemma open_Rbar_gt' x y : Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof.
case: x => [x||] //=; do ?[exact: open_Rbar_gt];
  case: y => [y||] //=; do ?by exists 0.
by exists y => x yx //=.
Qed.

Lemma Rbar_locally'_le x : Rbar_locally' x --> Rbar_locally x.
Proof.
move: x => [x P [_/posnumP[e] HP] |x P|x P] //=.
by exists e%:num => // ???; apply: HP.
Qed.

Lemma Rbar_locally'_le_finite (x : R) : Rbar_locally' x --> locally x.
Proof.
by move=> P [_/posnumP[e] HP] //=; exists e%:num => // ???; apply: HP.
Qed.

(** * Some limits on real functions *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + (INR n + 1)^-1
    | +oo => INR n
    | -oo => - INR n
  end.

Lemma flim_Rbar_loc_seq x : Rbar_loc_seq x --> Rbar_locally' x.
Proof.
move=> P; rewrite /Rbar_loc_seq.
case: x => /= [x [_/posnumP[delta] Hp] |[delta Hp] |[delta Hp]].
(* - (* x \in R *) *)
(*   case: (nfloor_ex (delta^-1)) => [ | N [_ /RltP HN]]. *)
(*     by apply Rlt_le, Rinv_0_lt_compat, delta. *)
(*   exists N => // n Hn. *)
(*   apply: Hp => /=. *)
(*     rewrite /ball /= /AbsRing_ball. *)
(*     rewrite INRE (_ : n%:R + _ = n.+1%:R); last by rewrite -addn1 natrD. *)
(*     rewrite opprD addrA subrr add0r absrN absRE ger0_norm //. *)
(*     rewrite -(invrK (pos delta)) ltr_pinv; last 2 first. *)
(*       by rewrite inE ltr0n andbT unitfE. *)
(*       by rewrite !inE unitfE gtr_eqF /= invr_gt0. *)
(*     move: HN; rewrite RinvE // RplusE => /ltr_le_trans; apply. *)
(*     by rewrite -addn1 natrD ler_add // INRE // ler_nat. *)
(*   move/eqP. *)
(*   rewrite eq_sym addrC -subr_eq subrr eq_sym INRE. *)
(*   rewrite (_ : n%:R + 1 = n.+1%:R); last by rewrite -addn1 natrD. *)
(*   by rewrite invr_eq0 pnatr_eq0. *)
(* - (* x = +oo *) *)
(*   case: (nfloor_ex (Num.max 0 delta)) => [ | N [_ /RltP HN]]. *)
(*     by apply/RleP; rewrite ler_maxr lerr. *)
(*   exists N.+1 => // n. *)
(*   rewrite -(@ler_nat [numDomainType of R]) => Hn. *)
(*   apply: Hp. *)
(*   move: HN; rewrite RplusE INRE (_ : _ + 1 = N%:R + 1%:R) // -natrD addn1 => HN. *)
(*   move: (ltr_le_trans HN Hn); rewrite INRE; apply: ler_lt_trans. *)
(*   by rewrite ler_maxr lerr orbT. *)
(* - (* x = -oo *) *)
(*   case: (nfloor_ex (Num.max 0 (-delta))) => [ | N [_ /RltP HN]]. *)
(*     by apply/RleP; rewrite ler_maxr lerr. *)
(*   exists N.+1 => // n. *)
(*   rewrite -(@ler_nat [numDomainType of R]) => Hn. *)
(*   apply: Hp. *)
(*   move: HN; rewrite RplusE INRE (_ : _ + 1 = N%:R + 1%:R) // -natrD addn1 => HN. *)
(*   rewrite lter_oppl. *)
(*   move: (ltr_le_trans HN Hn); rewrite INRE; apply: ler_lt_trans. *)
(*   by rewrite ler_maxr lerr orbT. *)
(* Qed. *)
Admitted.

Lemma continuity_pt_locally f x : continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps (* TODO: express using ball?*)).
Proof.
(* split. *)
(* - move=> H eps. *)
(*   move: (H eps%:num [gt0 of eps%:num]) => {H} [d [H1 H2]]. *)
(*   rewrite /= /R_dist /D_x /no_cond in H2. *)
(*   exists (mkposreal _ H1) => // y H. *)
(*   case/boolP: (x == y) => [/eqP <-|xy]. *)
(*   + by rewrite RminusE subrr Rabs_R0. *)
(*   + apply/RltP/H2; split; [split => //; by apply/eqP|]. *)
(*     by move/sub_ball_abs : H; rewrite mul1r /= absrB => /RltP. *)
(* - move=> H eps He. *)
(*   move: (H (mkposreal _ He)) => {H} [_/posnumP[d] H]. *)
(*   exists d; split=>//. *)
(*   move=> h [Zh Hh]. *)
(*   apply/RltP/H. *)
(*   apply/(@sub_norm_ball_pos _ [normedModType R of R^o] x d)/RltP. *)
(*   by rewrite /ball_norm -normmB. *)
Admitted.

Lemma continuity_pt_flim (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof.
eapply iff_trans; first exact: continuity_pt_locally.
apply iff_sym.
have FF : Filter (f @ x) by typeclasses eauto.
case: (@flim_ballP _ (f @ x) FF (f x)) => {FF}H1 H2.
(* TODO: in need for lemmas and/or refactoring of already existing lemmas (ball vs. Rabs) *)
split => [{H2} /H1{H1} H1 eps|{H1} H].
- have {H1} [//|_/posnumP[x0] Hx0] := H1 eps%:num.
  exists x0%:num => // Hx0' /Hx0 /=.
  by rewrite ball_absE /= absrB; apply.
- apply H2 => _ /posnumP[eps]; move: (H eps) => {H} [_ /posnumP[x0] Hx0].
  exists x0%:num => // y /Hx0 /= {Hx0}Hx0.
  by rewrite ball_absE /= absrB.
Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_flim. Qed.

Lemma continuous_withinNx {U V : uniformType} (Ueqdec : forall x y : U, x = y \/ x <> y)
  (f : U -> V) x :
  {for x, continuous f} <-> f @ locally' x --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /locally' !near_simpl near_withinE.
  by rewrite /locally'; apply: flim_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not infered *)
rewrite !locally_nearE !near_map !near_locally in fxP *.
have /= := cfx P fxP.
(* TODO: make things appear in canonical form i.e. {near x, ...} *)
rewrite !near_simpl => /filterP [//= Q Qx QP].
apply/filterP; exists (fun y => y <> x -> Q y) => // y Qy.
by have [->|/Qy /QP //] := Ueqdec y x; apply: locally_singleton.
Qed.

Lemma continuity_pt_flim' f x :
  continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx //; exact: Req_dec. Qed.

Lemma continuity_pt_locally' f x :
  continuity_pt f x <->
  forall eps : R, 0 < eps -> locally' x (fun u => `|f x - f u| < eps)%R.
Proof.
by rewrite continuity_pt_flim' (@flim_normP _ [normedModType R of R^o]).
Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_flim; apply. Qed.

(** For Pierre-Yves : definition of sums *)

From mathcomp Require fintype bigop finmap.

Section totally.

Import fintype bigop finmap.
Local Open Scope fset_scope.
(* :TODO: when eventually is generalized to any lattice  by any lattice *)
(* totally can just be replaced by eventually *)
Definition totally {I : choiceType} : set (set {fset I}) :=
  filter_from setT (fun A => [set B | A `<=` B]).

Canonical totally_filter_source {I : choiceType} X :=
  @Filtered.Source X _ {fset I} (fun f => f @ totally).

Instance totally_filter {I : choiceType} : ProperFilter (@totally I).
Proof.
eapply filter_from_proper; last by move=> A _; exists A; rewrite fsubset_refl.
apply: filter_fromT_filter; first by exists fset0.
by move=> A B /=; exists (A `|` B) => P /=; rewrite fsubUset => /andP[].
Qed.

Definition partial_sum {I : choiceType} {R : zmodType}
  (x : I -> R) (A : {fset I}) : R := \sum_(i : A) x (val i).

Definition sum (I : choiceType) {K : absRingType} {R : normedModType K}
   (x : I -> R) : R := lim (partial_sum x).

End totally.
