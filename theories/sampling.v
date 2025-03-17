(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
Require Reals Interval.Tactic.
From mathcomp Require Import (canonicals) Rstruct Rstruct_topology.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype.
From mathcomp Require Import sequences realfun convex.
From mathcomp Require Import derive esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.
From mathcomp Require Import independence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**md**************************************************************************)
(* This file contains the formalization of a sampling theorem                 *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section product_probability2.
Local Open Scope ereal_scope.
Lemma product_probability2_setT :
  forall (d1 d2 : measure_display) (T1 : measurableType d1)
  (T2 : measurableType d2) (R : realType) (P1 : probability T1 R)
  (P2 : probability T2 R), (P1 \x^ P2) setT = 1%E.
Proof.
move=> ? ? ? ? ? P1 P2.
rewrite -setXTT product_measure2E// -[RHS]mul1e.
congr mule.
all: rewrite -[LHS]fineK ?fin_num_measure//.
all: congr EFin=> /=.
all: by rewrite probability_setT.
Qed.

HB.instance Definition _ (d1 d2 : measure_display) (T1 : measurableType d1)
  (T2 : measurableType d2) (R : realType) (P1 : probability T1 R)
  (P2 : probability T2 R):=
  Measure_isProbability.Build _ _ _ (P1 \x^ P2) (product_probability2_setT P1 P2).
End product_probability2.

From mathcomp Require Import real_interval.

Section bool_to_real.
Context d (T : measurableType d) (R : realType) (P : probability T R) (f : {mfun T >-> bool}).
Definition bool_to_real : T -> R := (fun x => x%:R) \o (f : T -> bool).

Lemma measurable_bool_to_real : measurable_fun [set: T] bool_to_real.
Proof.
rewrite /bool_to_real.
apply: measurableT_comp => //=.
exact: (@measurable_funPT _ _ _ _ f).
Qed.
(* HB.about isMeasurableFun.Build. *)
HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ bool_to_real measurable_bool_to_real.

HB.instance Definition _ := MeasurableFun.on bool_to_real.

(*Definition btr : {RV P >-> R} := bool_to_real.

HB.instance Definition _ := MeasurableFun.on btr.*)

End bool_to_real.

Section mfunM.
Context {d} (T : measurableType d) {R : realType}.

HB.instance Definition _ (f g : {mfun T >-> R}) :=
  @isMeasurableFun.Build d _ _ _ (f \* g)%R
    (measurable_funM (@measurable_funPT _ _ _ _ f)
                     ((@measurable_funPT _ _ _ _ g))).

End mfunM.

Section move.

Lemma sumr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\sum_(i <- l | Q i) f i) x = \sum_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ g _ h <- <-. Qed.

Lemma prodr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\prod_(i <- l | Q i) f i) x = \prod_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ h _ g <- <-. Qed.

Definition sumrfct_tuple {R : realType} d {T : measurableType d}
    n (s : n.-tuple {mfun T >-> R}) : T -> R :=
  \sum_(f <- s) f.

Lemma measurable_sumrfct_tuple {R : realType} d {T : measurableType d}
    n (s : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (sumrfct_tuple s).
Proof. by apply/measurable_EFinP => /=; exact/measurableT_comp. Qed.

HB.instance Definition _ {R : realType} d {T : measurableType d}
    n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (sumrfct_tuple s) (measurable_sumrfct_tuple s).

Definition sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) : T -> R :=
  \sum_(f <- s) f.

Lemma measurable_sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :
  measurable_fun setT (sumrfct s).
Proof.
by apply/measurable_EFinP => /=; apply/measurableT_comp => //.
Qed.

HB.instance Definition _ {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (sumrfct s) (measurable_sumrfct s).

End move.

Section move_to_bigop_nat_lemmas.
Context {T : Type}.
Implicit Types (A : set T).

Lemma bigcup_mkord_ord n (F : 'I_n.+1 -> set T) :
  \bigcup_(i < n.+1) F (inord i) = \big[setU/set0]_(i < n.+1) F i.
Proof.
rewrite bigcup_mkord; apply: eq_bigr => /= i _; congr F.
by apply/val_inj => /=;rewrite inordK.
Qed.

End move_to_bigop_nat_lemmas.

(* in master *)
Lemma preimage_set_systemU {aT rT : Type} {X : set aT} {f : aT -> rT} :
  {morph preimage_set_system X f : x y / x `|` y >-> x `|` y}.
Proof.
move=> F G; apply/seteqP; split=> A; rewrite /preimage_set_system /=.
  by case=> B + <- => -[? | ?]; [left | right]; exists B.
by case=> -[] B FGB <-; exists B=> //; [left | right].
Qed.

(* in master *)
Lemma preimage_set_system0 {aT rT : Type} {X : set aT} {f : aT -> rT} :
  preimage_set_system X f set0 = set0.
Proof. by apply/seteqP; split=> A // []. Qed.

(* in master *)
Lemma preimage_set_system_funcomp
  {aT arT rT : Type} {f : aT -> arT} {g : arT -> rT} {F : set_system rT} D :
  preimage_set_system D (g \o f) F =
  preimage_set_system D f (preimage_set_system setT g F).
Proof.
apply/seteqP; split=> A.
  case=> B FB <-.
  exists (g @^-1` B)=> //.
  exists B=> //.
  by rewrite setTI.
case=> B [] C FC <- <-.
exists C=> //.
rewrite !setTI.
by rewrite comp_preimage.
Qed.

Definition g_sigma_preimage d (rT : semiRingOfSetsType d) (aT : Type)
    (n : nat) (f : 'I_n -> aT -> rT) : set (set aT) :=
  <<s \big[setU/set0]_(i < n) preimage_set_system setT (f i) measurable >>.

Lemma g_sigma_preimage_comp d1 {T1 : semiRingOfSetsType d1} n
  {T : pointedType} (f1 : 'I_n -> T -> T1) [T3 : Type] (g : T3 -> T) :
g_sigma_preimage (fun i => (f1 i \o g)) =
preimage_set_system [set: T3] g (g_sigma_preimage f1).
Proof.
rewrite {1}/g_sigma_preimage.
rewrite -g_sigma_preimageE; congr (<<s _ >>).
destruct n as [|n].
  rewrite !big_ord0 /preimage_set_system/=.
  by apply/esym; rewrite -subset0 => t/= [].
rewrite predeqE => C; split.
- rewrite -bigcup_mkord_ord => -[i Ii [A mA <-{C}]].
  exists (f1 (Ordinal Ii) @^-1` A).
    rewrite -bigcup_mkord_ord; exists i => //.
    exists A => //; rewrite setTI// (_ : Ordinal _ = inord i)//.
    by apply/val_inj => /=;rewrite inordK.
  rewrite !setTI// -comp_preimage// (_ : Ordinal _ = inord i)//.
  by apply/val_inj => /=;rewrite inordK.
- move=> [A].
  rewrite -bigcup_mkord_ord => -[i Ii [B mB <-{A}]] <-{C}.
  rewrite -bigcup_mkord_ord.
  exists i => //.
  by exists B => //; rewrite !setTI -comp_preimage.
Qed.

HB.instance Definition _ (n : nat) (T : pointedType) :=
  isPointed.Build (n.-tuple T) (nseq n point).

Definition mtuple (n : nat) d (T : measurableType d) : Type := n.-tuple T.

HB.instance Definition _ (n : nat) d (T : measurableType d) :=
  Pointed.on (mtuple n T).

Lemma countable_range_bool d (T : measurableType d) (b : bool) :
  countable (range (@cst T _ b)).
Proof. exact: countableP. Qed.

HB.instance Definition _ d (T : measurableType d) b :=
  MeasurableFun_isDiscrete.Build d _ T _  (cst b) (countable_range_bool T b).

Definition measure_tuple_display : measure_display -> measure_display.
Proof. exact. Qed.

Section measurable_tuple.
Context {d} {T : measurableType d}.
Variable n : nat.

Let coors := (fun i x => @tnth n T x i).

Let tuple_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let tuple_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let tuple_bigcup (F : _^nat) :
  (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build (measure_tuple_display d)
    (mtuple n T) (g_sigma_preimage coors)
    (tuple_set0) (tuple_setC) (tuple_bigcup).

End measurable_tuple.

(* NB: not used *)
Definition cylinder d {T : measurableType d} m (A : set (m.-tuple T))
    (J : {fset 'I_m}%fset) : set (m.-tuple T) :=
  \big[setI/setT]_(i <- J) (@tnth _ T ^~ i) @^-1`
                           ((@tnth _ T ^~ i) @` A).

(* NB: not used *)
Definition Z d {T : measurableType d} m
    (J : {fset 'I_m}%fset) : set_system (m.-tuple T) :=
  [set B | exists A, B = cylinder A J].

Lemma measurable_tnth d (T : measurableType d) n (i : 'I_n) :
  measurable_fun [set: mtuple n T] (@tnth _ T ^~ i).
Proof.
move=> _ Y mY; rewrite setTI; apply: sub_sigma_algebra => /=.
rewrite -bigcup_seq/=; exists i => //=; first by rewrite mem_index_enum.
by exists Y => //; rewrite setTI.
Qed.

Section cons_measurable_fun.
Context d d1 (T : measurableType d) (T1 : measurableType d1).

Lemma cons_measurable_funP (n : nat) (h : T -> mtuple n T1) :
  measurable_fun setT h <->
  forall i : 'I_n,  measurable_fun setT ((@tnth _ T1 ^~ i) \o h).
Proof.
apply: (@iff_trans _ (g_sigma_preimage
  (fun i : 'I_n  => (@tnth _ T1 ^~ i) \o h) `<=` measurable)).
- rewrite g_sigma_preimage_comp; split=> [mf A [C HC <-]|f12].
    exact: mf.
  by move=> _ A mA; apply: f12; exists A.
- split=> [h12|mh].
    move=> i _ A mA.
    apply: h12.
    apply: sub_sigma_algebra.
    destruct n as [|n].
      by case: i => [] [].
    rewrite -bigcup_mkord_ord.
    exists i => //; first by red.
    exists A => //.
    rewrite !setTI.
    rewrite (_ : inord i = i)//.
    by apply/val_inj => /=; rewrite inordK.
  apply: smallest_sub; first exact: sigma_algebra_measurable.
  destruct n as [|n].
    by rewrite big_ord0.
  rewrite -bigcup_mkord_ord.
  apply: bigcup_sub => i Ii.
  move=> A [C mC <-].
  exact: mh.
Qed.

(* TODO: rename to measurable_cons *)
Lemma measurable_fun_cons (f : T -> T1) n (g : T -> mtuple n T1) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun x : T => [the mtuple n.+1 T1 of (f x) :: (g x)]).
Proof.
move=> mf mg; apply/cons_measurable_funP => /= i.
have [->|i0] := eqVneq i ord0.
  by rewrite (_ : _ \o _ = f).
have @j : 'I_n.
  apply: (@Ordinal _ i.-1).
  rewrite prednK//.
    have := ltn_ord i.
    by rewrite ltnS.
  by rewrite lt0n.
rewrite (_ : _ \o _ = (fun x => tnth (g x) j))//.
  apply: (@measurableT_comp _ _ _ _ _ _
    (fun x : mtuple n T1 => tnth x j) _ g) => //.
  exact: measurable_tnth.
apply/funext => t/=.
rewrite (_ : i = lift ord0 j) ?tnthS//.
apply/val_inj => /=.
by rewrite /bump/= add1n prednK// lt0n.
Qed.

End cons_measurable_fun.

Lemma behead_mktuple n {T : eqType} (t : n.+1.-tuple T) :
  behead t = [tuple (tnth t (lift ord0 i)) | i < n].
Proof.
destruct n as [|n].
  rewrite !tuple0.
  apply: size0nil.
  by rewrite size_behead size_tuple.
apply: (@eq_from_nth _ (tnth_default t ord0)).
  by rewrite size_behead !size_tuple.
move=> i ti.
rewrite nth_behead/= (nth_map ord0); last first.
  rewrite size_enum_ord.
  by rewrite size_behead size_tuple in ti.
rewrite (tnth_nth (tnth_default t ord0)).
congr nth.
rewrite /= /bump/= add1n; congr S.
apply/esym.
rewrite size_behead size_tuple in ti.
have := @nth_ord_enum _ ord0 (Ordinal ti).
by move=> ->.
Qed.

Lemma measurable_behead d (T : measurableType d) n :
  measurable_fun setT (fun x : mtuple n.+1 T => [tuple of behead x] : mtuple n T).
Proof.
red=> /=.
move=> _ Y mY.
rewrite setTI.
set bh := (bh in preimage bh).
have bhYE : (bh @^-1` Y) = [set x :: y | x in setT & y in Y].
  rewrite /bh.
  apply/seteqP; split=> x /=.
    move=> ?; exists (thead x)=> //.
    exists [tuple of behead x] => //=.
    by rewrite [in RHS](tuple_eta x).
  case=> x0 _ [] y Yy xE.
  suff->: [tuple of behead x] = y by [].
  apply/val_inj=> /=.
  by rewrite -xE.
have:= mY.
rewrite /measurable/= => + F [] sF.
pose F' := image_set_system setT bh F.
move=> /(_ F') /=.
have-> : F' Y = F (bh @^-1` Y) by rewrite /F' /image_set_system /= setTI.
move=> /[swap] H; apply; split; first exact: sigma_algebra_image.
move=> A; rewrite /= /F' /image_set_system /= setTI.
set X := (X in X A).
move => XA.
apply: H; rewrite big_ord_recl /=; right.
set X' := (X' in X' (preimage _ _)).
have-> : X' = preimage_set_system setT bh X.
  rewrite /X.
  rewrite (big_morph _ preimage_set_systemU preimage_set_system0).
  apply: eq_bigr=> i _.
  rewrite -preimage_set_system_funcomp.
  congr preimage_set_system.
  apply: funext=> t.
  rewrite (tuple_eta t) /bh /= tnthS.
  by congr tnth; apply/val_inj.
exists A=> //.
by rewrite setTI.
Qed.

Section pro1.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  (R : realType) (P1 : probability T1 R) (P2 : probability T2 R).

Definition pro1 := product_measure1 P1 P2.

HB.instance Definition _ := Measure.on pro1.

Lemma pro1_setT : pro1 setT = 1%E.
Proof.
rewrite /pro1 -setXTT product_measure1E// -[RHS]mule1.
by rewrite -{1}(@probability_setT _ _ _ P1) -(@probability_setT _ _ _ P2).
Qed.

HB.instance Definition _ :=
  Measure_isProbability.Build _ _ _ pro1 pro1_setT.
End pro1.

Section pro2.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  (R : realType) (P1 : probability T1 R) (P2 : probability T2 R).

Definition pro2 := product_measure2 P1 P2.

HB.instance Definition _ := Measure.on pro2.

Lemma pro2_setT : pro2 setT = 1%E.
Proof.
rewrite /pro2 -setXTT product_measure2E// -[RHS]mule1.
by rewrite -{1}(@probability_setT _ _ _ P1) -(@probability_setT _ _ _ P2).
Qed.

HB.instance Definition _ :=
  Measure_isProbability.Build _ _ _ pro2 pro2_setT.
End pro2.

Section pro.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Fixpoint mpro (n : nat) : set (mtuple n T) -> \bar R :=
  match n with
  | 0%N => \d_([::] : mtuple 0 T)
  | m.+1 => fun A => (P \x^ @mpro m)%E [set (thead x, [tuple of behead x]) | x in A]
  end.

Lemma mpro_measure n : @mpro n set0 = 0 /\ (forall A, (0 <= @mpro n A)%E)
  /\ semi_sigma_additive (@mpro n).
Proof.
elim: n => //= [|n ih].
  by repeat split => //; exact: measure_semi_sigma_additive.
pose build_Mpro := isMeasure.Build _ _ _ (@mpro n) ih.1 ih.2.1 ih.2.2.
pose Mpro : measure _ R := HB.pack (@mpro n) build_Mpro.
pose ppro : measure _ R := (P \x^ Mpro)%E.
split.
  rewrite image_set0 /product_measure2 /=.
  under eq_fun => x do rewrite ysection0 measure0 (_ : 0 = cst 0 x)//.
  rewrite (_ : @mpro n = Mpro)//.
  by rewrite integral_cst// mul0e.
split.
  by move => A; rewrite (_ : @mpro n = Mpro).
rewrite (_ : @mpro n = Mpro)// (_ : (P \x^ Mpro)%E = ppro)//.
move=> F mF dF mUF.
rewrite image_bigcup.
move=> [:save].
apply: measure_semi_sigma_additive.
- abstract: save.
  move=> i.
  pose f (t : n.+1.-tuple T) := (@thead n T t, [the mtuple _ T of behead t]).
  pose f' (x : T * mtuple n T) := [the mtuple n.+1 T of x.1 :: x.2].
  rewrite [X in measurable X](_ : _ = f' @^-1` F i); last first.
    apply/seteqP; split=> [x/= [t Fit] <-{x}|[x1 x2] /= Fif'].
    rewrite /f'/=.
    by rewrite (tuple_eta t) in Fit.
  exists (f' (x1, x2)) => //.
  rewrite /f' /= theadE//; congr pair.
  exact/val_inj.
  rewrite -[X in measurable X]setTI.
  suff: measurable_fun setT f' by exact.
  rewrite /= /f'.
  exact: measurable_fun_cons.
- (* TODO: lemma? *)
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : dF => /(_ i j Logic.I Logic.I ij).
  rewrite -!subset0 => ij0 /= [_ _] [[t Fit] [<- <-]]/=.
  move=> [u Fju [hut tut]].
  have := ij0 t; apply; split => //.
  suff: t = u by move=> ->.
  rewrite (tuple_eta t) (tuple_eta u) hut.
  by apply/val_inj => /=; rewrite tut.
- apply: bigcup_measurable => j _.
  exact: save.
Qed.

HB.instance Definition _ n := isMeasure.Build _ _ _ (@mpro n)
  (@mpro_measure n).1 (@mpro_measure n).2.1 (@mpro_measure n).2.2.

Lemma mpro_setT n : @mpro n setT = 1%E.
Proof.
elim: n => //=; first by rewrite diracT.
move=> n ih.
rewrite /product_measure2/ysection/=.
under eq_fun => x.
  rewrite [X in P X](_ : _ = [set: T]); last first.
    under eq_fun => y. rewrite [X in _ \in X](_ : _ = setT); last first.
      apply: funext=> z/=.
      apply: propT.
      exists (z.1 :: z.2) => //=.
      case: z => z1 z2/=.
      congr pair.
      exact/val_inj.
      over.
    by apply: funext => y/=; rewrite in_setT trueE.
  rewrite probability_setT.
  over.
by rewrite integral_cst// mul1e.
Qed.

HB.instance Definition _ n :=
  Measure_isProbability.Build _ _ _ (@mpro n) (@mpro_setT n).

Definition pro (n : nat) : probability (mtuple n T) R := @mpro n.

End pro.
Arguments pro {d T R} P n.

Notation "\X_ n P" := (pro P n) (at level 10, n, P at next level,
  format "\X_ n  P").

Lemma fubini2' :
forall [d1 d2 : measure_display] [T1 : measurableType d1]
  [T2 : measurableType d2] [R : realType]
  [m1 : {sigma_finite_measure set T1 -> \bar R}]
  [m2 : {sigma_finite_measure set T2 -> \bar R}] [f : T1 * T2 -> \bar R],
(m1 \x m2)%E.-integrable [set: Datatypes_prod__canonical__measure_Measurable T1 T2]
  f -> (\int[m2]_x fubini_G m1 f x = \int[(m1 \x^ m2)%E]_z f z)%E.
Proof.
move=> d1 d2 T1 T2 R m1 m2 f intf.
rewrite fubini2//.
apply: eq_measure_integral => //= A mA _.
apply: product_measure_unique => // B C mB mC.
rewrite /=.
by rewrite product_measure2E.
Qed.

Lemma fubini1' :
forall [d1 d2 : measure_display] [T1 : measurableType d1]
  [T2 : measurableType d2] [R : realType]
  [m1 : {sigma_finite_measure set T1 -> \bar R}]
  [m2 : {sigma_finite_measure set T2 -> \bar R}] [f : T1 * T2 -> \bar R],
(m1 \x m2)%E.-integrable [set: Datatypes_prod__canonical__measure_Measurable T1 T2]
  f -> (\int[m1]_x fubini_F m2 f x = \int[(m1 \x^ m2)%E]_z f z)%E.
Proof.
move=> d1 d2 T1 T2 R m1 m2 f intf.
rewrite fubini1//.
apply: eq_measure_integral => //= A mA _.
apply: product_measure_unique => // B C mB mC.
rewrite /=.
by rewrite product_measure2E.
Qed.

Lemma integrable_prodP :
forall [d1 d2 : measure_display] [T1 : measurableType d1] [T2 : measurableType d2]
  [R : realType] [m1 : {sigma_finite_measure set T1 -> \bar R}]
  [m2 : {sigma_finite_measure set T2 -> \bar R}] [f : T1 * T2 -> \bar R],
(m1 \x m2)%E.-integrable [set: Datatypes_prod__canonical__measure_Measurable T1 T2] f ->
(m1 \x^ m2)%E.-integrable [set: Datatypes_prod__canonical__measure_Measurable T1 T2] f.
Proof.
move=> d1 d2 T1 T2 R m1 m2 f /integrableP[mf intf]; apply/integrableP; split => //.
  rewrite -fubini2'//=.
    rewrite fubini2//=.
    apply/integrableP; split => //.
      by apply/measurableT_comp => //.
    by under eq_integral do rewrite abse_id.
  apply/integrableP; split => //.
    by apply/measurableT_comp => //.
  by under eq_integral do rewrite abse_id.
Qed.

Section proS.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.
Variable n : nat.

Definition phi := fun (w : T * mtuple n T) => [the mtuple _ _ of w.1 :: w.2].

Lemma mphi : measurable_fun [set: T * mtuple _ _] phi.
Proof. exact: measurable_fun_cons. Qed.

Definition psi := fun (w : mtuple n.+1 T) => (thead w, [the mtuple _ _ of behead w]).

Lemma mpsi : measurable_fun [set: mtuple _ _] psi.
Proof.
apply/measurable_fun_prod => /=.
  exact: measurable_tnth.
exact: measurable_behead.
Qed.

Lemma phiK : cancel phi psi.
Proof.
by move=> [x1 x2]; rewrite /psi /phi/=; congr pair => /=; exact/val_inj.
Qed.

Let psiK : cancel psi phi.
Proof. by move=> x; rewrite /psi /phi/= [RHS]tuple_eta. Qed.

Lemma integral_mpro (f : n.+1.-tuple T -> R) :
  (\X_n.+1 P).-integrable [set: mtuple n.+1 T] (EFin \o f) ->
  \int[\X_n.+1 P]_w (f w)%:E =
  \int[pro2 P (\X_n P)]_w (f (w.1 :: w.2))%:E.
Proof.
move=> /integrableP[mf intf].
rewrite -(@integral_pushforward _ _ _ _ R _ mphi _ setT
    (fun x : mtuple n.+1 T => (f x)%:E)); [|by []| |by []].
  apply: eq_measure_integral => A mA _.
  rewrite /=.
  rewrite /pushforward.
  rewrite /pro2.
  rewrite /phi/=.
  rewrite /preimage/=.
  congr (_ _).
  apply/seteqP; split => [x/= [t At <-/=]|x/= Ax].
    move: At.
    by rewrite {1}(tuple_eta t)//.
  exists (x.1 :: x.2) => //=.
  destruct x as [x1 x2] => //=.
  congr pair.
  exact/val_inj.
rewrite /=.
apply/integrable_prodP.
rewrite /=.
apply/integrableP; split => /=.
  apply: measurableT_comp => //=.
  exact: mphi.
apply: le_lt_trans (intf).
rewrite [leRHS](_ : _ = \int[\X_n.+1 P]_x
    ((((abse \o (@EFin R \o (f \o phi)))) \o psi) x)); last first.
  by apply: eq_integral => x _ /=; rewrite psiK.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite -[RHS](@integral_pushforward _ _ _ _ R _ mpsi _ setT
    (fun x : T * mtuple n T => ((abse \o (EFin \o (f \o phi))) x)))//.
- apply: eq_measure_integral => // A mA _.
  apply: product_measure_unique => // B C mB mC.
  rewrite /= /pushforward/=.
  rewrite -product_measure2E//=.
  congr (_ _).
  (* TODO: lemma *)
  apply/seteqP; split => [[x1 x2]/= [t [Bt Ct]] [<- <-//]|].
  move=> [x1 x2] [B1 C2] /=.
  exists (x1 :: x2) => //=.
    split=> //.
    rewrite [X in C X](_ : _ = x2)//.
    exact/val_inj.
  congr pair => //.
  exact/val_inj.
- apply/measurable_EFinP => //=.
  apply: measurableT_comp => //=.
  apply: measurableT_comp => //=.
    by apply/measurable_EFinP.
  exact: mphi.
- have : (\X_n.+1 P).-integrable [set: mtuple n.+1 T] (EFin \o f).
    exact/integrableP.
- apply: le_integrable => //=.
  + apply: measurableT_comp => //=; last exact: mpsi.
    apply/measurable_EFinP => //=.
    apply: measurableT_comp => //=.
    apply: measurableT_comp => //=; last exact: mphi.
    by apply/measurable_EFinP => //=.
  + move=> x _.
    by rewrite normr_id// psiK.
Qed.

End proS.

Section integrable_theory.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).
Implicit Type f g : T -> \bar R.

Let ltnP_sumbool (a b : nat) : {(a < b)%N} + {(a >= b)%N}.
Proof. by case: ltnP => _; [left|right]. Qed.

(* TODO: clean, move near integrable_sum, refactor *)
Lemma integrable_sum_ord n (t : 'I_n -> (T -> \bar R)) :
  (forall i, mu.-integrable D (t i)) ->
  mu.-integrable D (fun x => \sum_(i < n) t i x).
Proof.
move=> intt.
pose s0 := fun k => match ltnP_sumbool k n with
  | left kn => t (Ordinal kn)
  | right _ => cst 0%E
  end.
pose s := [tuple of map s0 (index_iota 0 n)].
suff: mu.-integrable D (fun x => (\sum_(i <- s) i x)%R).
  apply: eq_integrable => // i iT.
  rewrite big_map/=.
  rewrite big_mkord.
  apply: eq_bigr => /= j _.
  rewrite /s0.
  case: ltnP_sumbool => // jn.
  f_equal.
  exact/val_inj.
  have := ltn_ord j.
  by rewrite ltnNge jn.
apply: (@integrable_sum d T R mu D mD s) => /= h /mapP[/= k].
rewrite mem_index_iota leq0n/= => kn ->{h}.
have := intt (Ordinal kn).
rewrite /s0.
case: ltnP_sumbool => //.
by rewrite leqNgt kn.
Qed.

End integrable_theory.

(* TODO: clean, move near integrableD, refactor *)
Section integral_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : eqType) (f : I -> (T -> \bar R)).
Hypothesis intf : forall n, mu.-integrable D (f n).

Lemma integral_sum (s : seq I) :
  \int[mu]_(x in D) (\sum_(k <- s) f k x) =
  \sum_(k <- s) \int[mu]_(x in D) (f k x).
Proof.
elim: s => [|h t ih].
  under eq_integral do rewrite big_nil.
  by rewrite integral0 big_nil.
rewrite big_cons -ih -integralD//.
  by apply: eq_integral => x xD; rewrite big_cons.
rewrite [X in _.-integrable _ X](_ : _ =
    (fun x => (\sum_(h0 <- [seq f i | i <- t]) h0 x))); last first.
  by apply/funext => x; rewrite big_map.
apply: integrable_sum => //= g /mapP[i ti ->{g}].
exact: intf.
Qed.

End integral_sum.

(* TODO: integral_fune_lt_pinfty does not look useful a lemma *)

Lemma bounded_RV_integrable d (T : measurableType d) (R : realType)
    (P : probability T R) (X : T -> R) M :
  measurable_fun setT X ->
  (forall t, (0 <= X t <= M)%R) -> P.-integrable setT (EFin \o X).
Proof.
move=> mf XM.
apply: (@le_integrable _ T R _ _ measurableT _ (EFin \o cst M)).
- exact/measurable_EFinP.
- move=> t _ /=; rewrite lee_fin/=.
  rewrite !ger0_norm//.
  + by have /andP[] := XM t.
  + by rewrite (@le_trans _ _ (X t))//; have /andP[] := XM t.
  + by have /andP[] := XM t.
- exact: finite_measure_integrable_cst.
Qed.
Arguments bounded_RV_integrable {d T R P X} M.

Module with_interval.
Declare Scope bigQ_scope.
Import Reals.
Import Rstruct Rstruct_topology.
Import Interval.Tactic.

Section expR2_le8.
Let R := Rdefinitions.R.
Local Open Scope ring_scope.

Lemma expR2_le8 : expR 2 <= 8 :> R.
Proof.
rewrite (_ : 2 = 1 + 1)//.
rewrite exp.expRD -RmultE.
rewrite (_ : 8 = 8%R); last first.
  by rewrite !mulrS -!RplusE Rplus_0_r !RplusA !IZRposE/=.
rewrite (_ : 1 = INR 1%N)//=.
rewrite -RexpE.
apply/RleP.
by interval.
Qed.

End expR2_le8.
End with_interval.

Section taylor_ln_le.
Let R := Rdefinitions.R.
Local Open Scope ring_scope.

Lemma taylor_ln_le (x : R) : x \in `]0, 1[ -> (1 + x) * ln (1 + x) >= x + x^+2 / 3.
Proof.
move=> x01; rewrite -subr_ge0.
pose f (x : R^o) := (1 + x) * ln (1 + x) - (x + x ^+ 2 / 3).
have f0 : f 0 = 0 by rewrite /f expr0n /= mul0r !addr0 ln1 mulr0 subr0.
rewrite [leRHS](_ : _ = f x) // -f0.
evar (df0 : R -> R); evar (df : R -> R).
have idf (y : R^o) : 0 < 1 + y -> is_derive y (1:R) f (df y).
  move=> y1.
  rewrite (_ : df y = df0 y).
    apply: is_deriveB; last exact: is_deriveD.
    apply: is_deriveM=> //.
    apply: is_derive1_comp=> //.
    exact: is_derive1_ln.
  rewrite /df0.
  rewrite deriveD// derive_cst derive_id.
  rewrite /GRing.scale /= !(mulr0,add0r,mulr1).
  rewrite divff ?lt0r_neq0// opprD addrAC addrA subrr add0r.
  instantiate (df := fun y : R => - (3^-1 * (y + y)) + ln (1 + y)).
  reflexivity.
clear df0.
have y1cc y : y \in `[0, 1] -> 0 < 1 + y.
  rewrite in_itv /= => /andP [] y0 ?.
  by have y1: 0 < 1 + y by apply: (le_lt_trans y0); rewrite ltrDr.
have y1oo y : y \in `]0, 1[ -> 0 < 1 + y by move/subset_itv_oo_cc/y1cc.
have dfge0 y : y \in `]0, 1[ -> 0 <= df y.
  move=> y01.
  have:= y01.
  rewrite /df in_itv /= => /andP [] y0 y1.
  rewrite -lerBlDl opprK add0r -mulr2n -(mulr_natl _ 2) mulrA.
  rewrite [in leLHS](_ : y = 1 + y - 1); last by rewrite addrAC subrr add0r.
  pose iy:= Itv01 (ltW y0) (ltW y1).
  have y1E: 1 + y = @convex.conv _ R^o iy 1 2.
    rewrite convRE /= /onem mulr1 (mulr_natr _ 2) mulr2n.
    by rewrite addrACA (addrC (- y)) subrr addr0.
  rewrite y1E; apply: (le_trans _ (concave_ln _ _ _))=> //.
  rewrite -y1E addrAC subrr add0r convRE ln1 mulr0 add0r /=.
  rewrite mulrC ler_pM// ?(@ltW _ _ 0)// mulrC.
  rewrite ler_pdivrMr//.
  rewrite -[leLHS]expRK -[leRHS]expRK ler_ln ?posrE ?expR_gt0//.
  rewrite expRM/= powR_mulrn ?expR_ge0// lnK ?posrE//.
  rewrite !exprS expr0 mulr1 -!natrM mulnE /=.
  by rewrite with_interval.expR2_le8.
apply: (@ger0_derive1_homo R f 0 1 true false).
- by move=> y /y1oo /idf /@ex_derive.
- by move=> y /[dup] /y1oo /idf /@derive_val ->; exact: dfge0.
- by apply: derivable_within_continuous=> y /y1cc /idf /@ex_derive.
- by rewrite bound_itvE.
- exact: subset_itv_oo_cc.
- by have:= x01; rewrite in_itv=> /andP /= [] /ltW.
Qed.

End taylor_ln_le.

(* TODO: move to functions. *)
Lemma fct_prodE (I : Type) (T : pointedType) (M : comRingType) r (P : {pred I}) (f : I -> T -> M)
    (x : T) :
  (\prod_(i <- r | P i) f i) x = \prod_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

HB.instance Definition _ (n : nat) := isPointed.Build 'I_n.+1 ord0.

HB.instance Definition _ (n : nat) := @isMeasurable.Build default_measure_display
  'I_n.+1 discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Section tuple_sum.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition Tnth n (X : n.-tuple {mfun T >-> R}) (i : 'I_n) : mtuple n T -> R :=
  fun t => (tnth X i) (tnth t i).

Lemma measurable_Tnth n (X : n.-tuple {mfun T >-> R}) (i : 'I_n) :
  measurable_fun [set: mtuple n T] (Tnth X i).
Proof. by apply: measurableT_comp => //; exact: measurable_tnth. Qed.

HB.instance Definition _ n (X : n.-tuple {mfun T >-> R}) (i : 'I_n) :=
  isMeasurableFun.Build _ _ _ _ (Tnth X i) (measurable_Tnth X i).

Lemma measurable_tuple_sum n (X : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (\sum_(i < n) Tnth X i)%R.
Proof.
rewrite [X in measurable_fun _ X](_ : _
    = (fun x => \sum_(i < n) Tnth X i x)); last first.
  by apply/funext => x; rewrite fct_sumE.
apply: measurable_sum => i/=; apply/measurableT_comp => //.
exact: measurable_tnth.
Qed.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (\sum_(i < n) Tnth s i)%R (measurable_tuple_sum s).

Lemma measurable_tuple_prod m n (s : m.-tuple {mfun T >-> R}) (f : 'I_n -> 'I_m) :
  measurable_fun setT (\prod_(i < n) Tnth s (f i))%R.
Proof.
rewrite [X in measurable_fun _ X](_ : _
    = (fun x => \prod_(i < n) Tnth s (f i) x)); last first.
  by apply/funext => x; rewrite fct_prodE.
by apply: measurable_prod => /= i _; apply/measurableT_comp => //.
Qed.

HB.instance Definition _ m n (s : m.-tuple {mfun T >-> R}) (f : 'I_n -> 'I_m) :=
  isMeasurableFun.Build _ _ _ _ (\prod_(i < n) Tnth s (f i))%R (measurable_tuple_prod s f).

End tuple_sum.

Section properties_of_expectation.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma expectation_sum_pro n (X : n.-tuple {RV P >-> R}) M :
    (forall i t, (0 <= tnth X i t <= M)%R) ->
  'E_(\X_n P)[\sum_(i < n) Tnth X i] = \sum_(i < n) ('E_P[(tnth X i)]).
Proof.
elim: n X => [X|n IH X] /= XM.
  by rewrite !big_ord0 expectation_cst.
pose X0 := thead X.
have intX0 : P.-integrable [set: T] (EFin \o X0).
  apply: (bounded_RV_integrable M) => // t.
  exact: XM.
have {}intX Xi : Xi \in X -> P.-integrable [set: T] (EFin \o Xi).
  move=> /tnthP[i XiXi].
  apply: (bounded_RV_integrable M) => // t.
  rewrite XiXi.
  exact: XM.
rewrite big_ord_recl/=.
rewrite big_ord_recl/=.
pose X1 (x : mtuple n.+1 T) :=
  (\sum_(i < n) (tnth X (lift ord0 i)) (tnth x (lift ord0 i)))%R.
have mX1 : measurable_fun setT X1.
  apply: measurable_sum => /= i; apply: measurableT_comp => //.
  exact: measurable_tnth.
pose build_mX1 := isMeasurableFun.Build _ _ _ _ _ mX1.
pose Y1 : {mfun mtuple n.+1 T >-> R} := HB.pack X1 build_mX1.
pose X2 (x : mtuple n.+1 T) := (thead X) (thead x).
have mX2 : measurable_fun setT X2.
rewrite /X2 /=.
  by apply: measurableT_comp => //; exact: measurable_tnth.
pose build_mX2 := isMeasurableFun.Build _ _ _ _ _ mX2.
pose Y2 : {mfun mtuple n.+1 T >-> R} := HB.pack X2 build_mX2.
rewrite [X in 'E__[X]](_ : _ = Y2 \+ Y1); last first.
  rewrite /Y2 /Y1/=.
  rewrite /X2 /X1/=.
  apply/funext => t.
  rewrite !fctE.
  by rewrite fct_sumE.
rewrite expectationD; last 2 first.
  apply: (bounded_RV_integrable M) => // t.
  exact: XM.
  rewrite (_ : _ \o _ = fun x => (\sum_(i < n)
      (tnth X (lift ord0 i) (tnth x (lift ord0 i)))%:E)); last first.
    by apply/funext => t/=; rewrite sumEFin.
  apply: integrable_sum_ord => // i.
  have : measurable_fun setT (fun x : mtuple n.+1 T =>
      (tnth X (lift ord0 i) (tnth x (lift ord0 i)))).
    apply/measurableT_comp => //=.
    exact: measurable_tnth.
  by move/(bounded_RV_integrable M); exact.
congr (_ + _).
- rewrite /Y2 /X2/= unlock /expectation.
  (* \int[\X_n.+1 P]_w (thead X (thead w))%:E = \int[P]_w (tnth X ord0 w)%:E *)
  pose phi : mtuple n.+1 T -> T := (fun w => @tnth n.+1 T w ord0).
  have mphi : measurable_fun setT phi.
    exact: measurable_tnth.
  rewrite -(@integral_pushforward _ _ _ _ _ phi mphi _ setT
      (fun w => (tnth X ord0 w)%:E)); last 3 first.
    exact/measurable_EFinP.
    apply: (bounded_RV_integrable M).
      by [].
    move=> t.
    by apply: XM.
    by [].
  apply: eq_measure_integral => //= A mA _.
  rewrite /pushforward.
  rewrite /pro/= /phi.
  rewrite [X in (_ \x^ _) X = _](_ :
    [set (thead x, [tuple of behead x]) | x in (tnth (T:=T))^~ ord0 @^-1` A]
    = A `*` setT); last first.
    apply/seteqP; split => [[x1 x2]/= [t At [<- _]]//|].
    move=> [x1 x2]/= [Ax1 _].
    exists [the mtuple _ _ of x1 :: x2] => //=.
    by rewrite theadE; congr pair => //; exact/val_inj.
  by rewrite product_measure2E//= probability_setT mule1.
- rewrite /Y1 /X1/=.
  transitivity ((\sum_(i < n) 'E_ P [(tnth (behead X) i)] )%R); last first.
    apply: eq_bigr => /= i _.
    congr expectation.
    rewrite tnth_behead.
    congr (tnth X).
    apply/val_inj => /=.
    by rewrite /bump/= add1n/= inordK// ltnS.
  rewrite -IH; last first.
    move=> i t.
    rewrite tnth_behead.
    exact: XM.
  transitivity ('E_\X_n P[(fun x : mtuple n T =>
      (\sum_(i < n) tnth (behead X) i (tnth x i))%R)]).
    rewrite unlock /expectation.
    transitivity (\int[(pro2 P (\X_n P))]_w (\sum_(i < n) tnth X (lift ord0 i) (tnth w.2 i))%:E).
      rewrite integral_mpro//.
        apply: eq_integral => /= -[w1 w2] _.
        rewrite -!sumEFin.
        apply: eq_bigr => i _ /=.
        by rewrite tnthS//.
      rewrite (_ : _ \o _ = (fun w => (\sum_(i < n)
        (tnth X (lift ord0 i) (tnth w (lift ord0 i)))%:E))); last first.
        by apply/funext => t/=; rewrite sumEFin.
      apply: integrable_sum_ord => // i.
      have : measurable_fun setT (fun x : mtuple n.+1 T =>
          (tnth X (lift ord0 i) (tnth x (lift ord0 i)))).
        apply/measurableT_comp => //=.
        exact: measurable_tnth.
      by move/(bounded_RV_integrable M); exact.
    rewrite /pro2.
    rewrite -fubini2'/=; last first.
      rewrite [X in integrable _ _ X](_ : _ = (fun z => (\sum_(i < n)
          (tnth X (lift ord0 i) (tnth z.2 i))%:E))); last first.
        by apply/funext => t/=; rewrite sumEFin.
      apply: integrable_sum_ord => //= i.
      have : measurable_fun setT (fun x : T * mtuple n T => (tnth X (lift ord0 i) (tnth x.2 i))).
        apply/measurableT_comp => //=.
        apply: (@measurableT_comp _ _ _ _ _ _ (fun x : mtuple n _ => tnth x i) _ snd) => //=.
        exact: measurable_tnth.
      move/(@bounded_RV_integrable _ _ R (pro1 P (mpro P (n:=n)))%E _ M) => /=.
      apply => t.
      by apply: XM.
    apply: eq_integral => t _.
    rewrite /fubini_G.
    transitivity (\sum_(i < n)
      (\int[P]_x (tnth X (lift ord0 i) (tnth (x, t).2 i))%:E)).
      rewrite -[RHS]integral_sum//.
        by apply: eq_integral => x _; rewrite sumEFin.
      move=> /= i.
      exact: finite_measure_integrable_cst.
    rewrite -sumEFin.
    apply: eq_bigr => /= i _.
    rewrite integral_cst//.
    rewrite [X in _ * X]probability_setT mule1.
    rewrite tnth_behead//=.
    congr (tnth X _ _)%:E.
    apply/val_inj => /=.
    by rewrite inordK// ltnS.
  congr expectation.
  apply/funext => t.
  by rewrite fct_sumE.
Qed.

Lemma expectation_prod2 d1 d2 (T1 : measurableType d1) (T2 : measurableType d2)
  (P1 : probability T1 R) (P2 : probability T2 R)
  (X : {mfun T1 >-> R}) (Y : {mfun T2 >-> R}) :
  P1.-integrable setT (EFin \o X) ->
  P2.-integrable setT (EFin \o Y) ->
  let XY := fun (x : T1 * T2) => (X x.1 * Y x.2)%R in
  'E_(pro2 P1 P2)[XY] = 'E_P1[X] * 'E_P2[Y].
Proof.
move=> intX intY/=.
rewrite unlock /expectation/=. rewrite /pro2. rewrite -fubini1'/=; last first.
  apply/fubini1b.
  - apply/measurable_EFinP => //=.
    by apply: measurable_funM => //=; apply: measurableT_comp.
  - under eq_integral.
      move=> t _.
      under eq_integral.
        move=> x _.
        rewrite /= normrM EFinM muleC.
        over.
      rewrite /= integralZl//; last first.
        by move/integrable_abse : intX.
      over.
    rewrite /=.
    rewrite ge0_integralZr//; last 2 first.
      apply/measurable_EFinP => //.
      by apply/measurableT_comp => //.
      by apply: integral_ge0 => //.
    rewrite lte_mul_pinfty//.
      by apply: integral_ge0 => //.
      apply: integral_fune_fin_num => //.
      by move/integrable_abse : intY.
      by move/integrableP : intX => [].
rewrite /fubini_F/=.
under eq_integral => x _.
  under eq_integral => y _ do rewrite EFinM.
  rewrite integralZl//.
  rewrite -[X in _ * X]fineK ?integral_fune_fin_num//.
  over.
rewrite /=integralZr//.
by rewrite fineK// integral_fune_fin_num.
Qed.

End properties_of_expectation.

Section properties_of_independence.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma boundedM U (f g : U -> R) (A : set U) :
  [bounded f x | x in A] ->
  [bounded g x | x in A] ->
  [bounded (f x * g x)%R | x in A].
Proof.
move=> bF bG.
rewrite/bounded_near.
case: bF => M1 [M1real M1f].
case: bG => M2 [M2real M2g].
near=> M.
rewrite/globally/= => x xA.
rewrite normrM.
rewrite (@le_trans _ _ (`|M1 + 1| * `|M2 + 1|)%R)//.
rewrite ler_pM//.
  by rewrite M1f// (lt_le_trans _ (ler_norm _))// ltrDl.
by rewrite M2g// (lt_le_trans _ (ler_norm _))// ltrDl.
Unshelve. all: by end_near.
Qed.

Lemma expectation_prod_nondep n (X : n.-tuple {RV P >-> R}) M :
    (forall i t, (0 <= tnth X i t <= M)%R) ->
    (forall Xi, Xi \in X -> P.-integrable [set: T] (EFin \o Xi)) ->
  'E_(\X_n P)[ \prod_(i < n) Tnth X i] = \prod_(i < n) 'E_P[ (tnth X i) ].
Proof.
elim: n X => [X|n IH X] /= boundedX intX.
  by rewrite !big_ord0 expectation_cst.
rewrite unlock /expectation integral_mpro /pro2; last first.
  apply: (bounded_RV_integrable (M^+n.+1)%R) => //.
    exact: measurable_tuple_prod.
  move=> t; apply/andP; split.
    rewrite fct_prodE.
    rewrite prodr_ge0//= => i _.
    by have /andP[] := boundedX i (tnth t i).
  rewrite -[in leRHS](subn0 n.+1) -prodr_const_nat.
  rewrite fct_prodE big_mkord.
  by rewrite ler_prod// => i _; exact: boundedX.
under eq_fun.
  move=> x.
  rewrite big_ord_recl/=.
  rewrite /Tnth/= fctE tnth0.
  rewrite fct_prodE.
  under eq_bigr.
    move=> i _.
    rewrite tnthS.
    over.
  over.
rewrite /=.
rewrite -fubini1' /fubini_F/=; last first.
  apply: measurable_bounded_integrable => //=.
  - rewrite /product_measure1/=.
    apply: (@le_lt_trans _ _ 1); last exact: ltry.
    rewrite -(mule1 1) -{2}(@probability_setT _ _ _ P) -(integral_cst P _ 1)//.
    apply: ge0_le_integral => //=.
      exact: measurable_fun_xsection.
    by move=> x _; apply: probability_le1; exact: measurable_xsection.
  - apply: measurable_funM => //=.
      exact: measurableT_comp.
    apply: measurable_prod => //=i ?.
    apply: measurableT_comp => //=.
    apply: (@measurableT_comp _ _ _ _ _ _ (fun x : mtuple n T => @tnth n T x i) _ snd) => //=.
    exact: measurable_tnth.
  apply: boundedM.
    apply/ex_bound. exact: (@globally_properfilter _ _ point). (* TODO: need to automate globally_properfilter *)
    exists M; rewrite /globally/= => x _.
    have /andP[? ?] := boundedX ord0 x.1.
    by rewrite ger0_norm.
  apply/ex_bound; first exact: (@globally_properfilter _ _ point).
  exists (M^+n)%R. rewrite /globally/= => x _.
  rewrite normr_prod -[in leRHS](subn0 n) -prodr_const_nat.
  rewrite big_mkord ler_prod => //=i _.
  have /andP[? ?] := boundedX (lift ord0 i) (tnth x.2 i).
  by rewrite normr_ge0/= ger0_norm.
have ? : (mpro P (n:=n)).-integrable [set: mtuple n T]
    (fun x : mtuple n T => (\prod_(i < n) tnth X (lift ord0 i) (tnth x i))%:E).
  apply: (bounded_RV_integrable (M^+n)%R) => //=.
    apply: measurable_prod => /=i _.
    apply: measurableT_comp => //.
    exact: measurable_tnth.
  move=> t. apply/andP. split.
    by rewrite prodr_ge0//= => i _; have /andP[] := boundedX (lift ord0 i) (tnth t i).
  by rewrite -[in leRHS](subn0 n) -prodr_const_nat big_mkord ler_prod.
under eq_fun => x.
  under eq_fun => y do rewrite/= EFinM.
  rewrite integralZl//= -[X in _*X]fineK ?integral_fune_fin_num//=.
  over.
rewrite integralZr//; last by rewrite intX// (tuple_eta X) tnth0 mem_head.
rewrite big_ord_recl/=.
congr (_ * _).
rewrite fineK ?integral_fune_fin_num//=.
under eq_fun => x.
  under eq_bigr => i _.
    rewrite [X in tnth X]tuple_eta tnthS.
    over.
  over.
simpl.
rewrite [LHS](_ : _ = 'E_(\X_n P)[ \prod_(i < n) Tnth (behead_tuple X) i]); last first.
  rewrite [in RHS]unlock /expectation.
  apply: eq_integral => t _; congr EFin.
  by rewrite fct_prodE.
rewrite IH; last 2 first.
- by move=> i t; rewrite tnth_behead.
- by move=> Xi XiX; apply: intX; rewrite mem_behead.
apply: eq_bigr => /=i _.
rewrite unlock /expectation.
apply: eq_integral => x _.
congr EFin.
by rewrite [in RHS](tuple_eta X) tnthS.
Qed.

Section fset.
Local Open Scope fset_scope.
Lemma fset_bool : forall B : {fset bool},
    [\/ B == [fset true], B == [fset false], B == fset0 | B == [fset true; false]].
Proof.
move=> B.
have:= set_bool [set` B].
rewrite -!set_fset1 -set_fset0.
rewrite (_ : [set: bool] = [set` [fset true; false]]); last first.
  by apply/seteqP; split=> -[]; rewrite /= !inE eqxx.
by case=> /eqP /(congr1 (@fset_set _)) /[!set_fsetK] /eqP H;
   [apply: Or41|apply: Or42|apply: Or43|apply: Or44].
Qed.
End fset.

Lemma finite_prod n (F : 'I_n -> \bar R) :
  (forall i, 0 <= F i < +oo) -> \prod_(i < n) F i < +oo.
Proof.
move: F; elim: n => n; first by rewrite big_ord0 ltry.
move=> ih F Foo.
rewrite big_ord_recl lte_mul_pinfty//.
- by have /andP[] := Foo ord0.
- rewrite fin_numElt.
  have /andP[F0 ->] := Foo ord0.
  by rewrite (@lt_le_trans _ _ 0).
by rewrite ih.
Qed.

End properties_of_independence.


HB.about isMeasurableFun.
HB.mixin Record RV_isBernoulli d (T : measurableType d) (R : realType)
  (P : probability T R) (p : R) (X : T -> bool) of @isMeasurableFun d _ T bool X  := {
    bernoulliP : distribution P X = bernoulli p }.

#[short(type=bernoulliRV)]
HB.structure Definition BernoulliRV d (T : measurableType d) (R : realType)
    (P : probability T R) (p : R) :=
  {X of @RV_isBernoulli _ _ _ P p X}.
Arguments bernoulliRV {d T R}.

Section bernoulli.

Local Open Scope ereal_scope.
Let R := Rdefinitions.R.
Context d (T : measurableType d) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Lemma bernoulli_RV1 (X : bernoulliRV P p) :
  P [set i | X i == 1%R] = p%:E.
Proof.
have/(congr1 (fun f => f [set 1%:R])):= @bernoulliP _ _ _ _ _ X.
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= mem_set// mule1// diracE/= memNset//.
rewrite mule0 adde0.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_RV2 (X : bernoulliRV P p) :
  P [set i | X i == 0%R] = (`1-p)%:E.
Proof.
have/(congr1 (fun f => f [set 0%:R])):= @bernoulliP _ _ _ _ _ X.
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= memNset//.
rewrite mule0// diracE/= mem_set// add0e mule1.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_expectation (X : bernoulliRV P p) :
  'E_P[bool_to_real R X] = p%:E.
Proof.
rewrite unlock.
rewrite -(@ge0_integral_distribution _ _ _ _ _ _ X (EFin \o [eta GRing.natmul 1]))//; last first.
  by move=> y //=.
rewrite /bernoulli/=.
rewrite (@eq_measure_integral _ _ _ _ (bernoulli p)); last first.
   by move=> A mA _ /=; congr (_ _); exact: bernoulliP.
rewrite integral_bernoulli//=.
by rewrite -!EFinM -EFinD mulr0 addr0 mulr1.
Qed.

Lemma integrable_bernoulli (X : bernoulliRV P p) :
  P.-integrable [set: T] (EFin \o bool_to_real R X).
Proof.
apply/integrableP; split.
  by apply: measurableT_comp => //; exact: measurable_bool_to_real.
have -> : \int[P]_x `|(EFin \o bool_to_real R X) x| = 'E_P[bool_to_real R X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  by rewrite gee0_abs //= lee_fin.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma bool_RV_sqr (X : {RV P >-> bool}) :
  ((bool_to_real R X ^+ 2) = bool_to_real R X :> (T -> R))%R.
Proof.
apply: funext => x /=.
rewrite /GRing.exp /bool_to_real /GRing.mul/=.
by case: (X x) => /=; rewrite ?mulr1 ?mulr0.
Qed.

Lemma bernoulli_variance (X : bernoulliRV P p) :
  'V_P[bool_to_real R X] = (p * (`1-p))%:E.
Proof.
rewrite (@varianceE _ _ _ _ (bool_to_real R X));
  [|rewrite ?[X in _ \o X]bool_RV_sqr; exact: integrable_bernoulli..].
rewrite [X in 'E_P[X]]bool_RV_sqr !bernoulli_expectation//.
by rewrite expe2 -EFinD onemMr.
Qed.

Definition real_of_bool := map (bool_to_real R : bernoulliRV P p -> {mfun _ >-> _}).

Definition bernoulli_trial n (X : n.-tuple (bernoulliRV P p))
    : {RV (\X_n P) >-> R : realType} :=
  (\sum_(i < n) Tnth (real_of_bool X) i)%R.

(*
was wrong
Definition bernoulli_trial n (X : {dRV P >-> bool}^nat) : {RV (pro n P) >-> R} :=
  (\sum_(i<n) (bool_to_real R (X i)))%R. (* TODO: add HB instance measurablefun sum*)
*)

Lemma btr_ge0 (X : {RV P >-> bool}) t : (0 <= bool_to_real R X t)%R.
Proof. by []. Qed.

Lemma btr_le1 (X : {RV P >-> bool}) t : (bool_to_real R X t <= 1)%R.
Proof. by rewrite /bool_to_real/=; case: (X t). Qed.

Lemma expectation_bernoulli_trial n (X : n.-tuple (bernoulliRV P p)) :
  'E_(\X_n P)[bernoulli_trial X] = (n%:R * p)%:E.
Proof.
rewrite /bernoulli_trial.
(*=======
move=> bRV. rewrite /bernoulli_trial.
transitivity ('E_(\X_n P)[\sum_(i < n) Tnth (map (bool_to_real R) X) i]).
  congr expectation; apply/funext => t.
  rewrite /Tnth/=.
  rewrite !fct_sumE/=.
  apply: eq_bigr => /= i _.
  by rewrite /Tnth !tnth_map.
>>>>>>> 8b8db025 (rm tuple_sum)*)
rewrite (@expectation_sum_pro _ _ _ _ _ _ 1%R); last first.
  by move=> i t; rewrite tnth_map// btr_ge0 btr_le1.
transitivity (\sum_(i < n) p%:E).
  by apply: eq_bigr => k _; rewrite !tnth_map bernoulli_expectation.
by rewrite sumEFin big_const_ord iter_addr addr0 mulrC mulr_natr.
Qed.

Lemma bernoulli_trial_ge0 n (X : n.-tuple (bernoulliRV P p)) :
  (forall t, 0 <= bernoulli_trial X t)%R.
Proof.
move=> t.
rewrite /bernoulli_trial.
rewrite [leRHS]fct_sumE.
apply/sumr_ge0 => /= i _.
rewrite /Tnth.
by rewrite !tnth_map.
Qed.

Lemma bernoulli_trial_mmt_gen_fun n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  let X := bernoulli_trial X_ in
  'M_X t = \prod_(i < n) 'M_(bool_to_real R (tnth X_ i) : {RV P >-> _}) t.
Proof.
pose mmtX : 'I_n -> {RV P >-> R : realType} := fun i => expR \o t \o* bool_to_real R (tnth X_ i).
transitivity ('E_(\X_n P)[ \prod_(i < n) Tnth (mktuple mmtX) i ])%R.
  congr expectation => /=; apply: funext => x/=.
  rewrite fct_sumE.
  rewrite big_distrl/= expR_sum.
  rewrite [in RHS]fct_prodE.
  apply: eq_bigr => i _.
  by rewrite /Tnth !tnth_map /mmtX/= tnth_ord_tuple.
rewrite /mmtX.
rewrite (@expectation_prod_nondep _ _ _ _ _ _ (expR (`|t|))%R); last 2 first.
- move=> i ?.
  apply/andP. split.
    by rewrite tnth_mktuple/= expR_ge0.
  rewrite tnth_mktuple/=/bool_to_real/=.
  rewrite ler_expR -[leRHS]mul1r.
  have [t0|t0] := leP 0%R t.
    by rewrite ger0_norm// ler_pM//; case: (tnth X_ i _).
  rewrite (@le_trans _ _ 0%R)//.
  by rewrite mulr_ge0_le0// ltW.
- move=> _ /mapP[/= i _ ->].
  apply: (bounded_RV_integrable (expR `|t|)) => // t0.
  rewrite expR_ge0/= ler_expR/=.
  rewrite /bool_to_real/=.
  case: (tnth X_ i t0) => //=; rewrite ?mul1r ?mul0r//.
  by rewrite ler_norm.
apply: eq_bigr => /= i _.
congr expectation.
rewrite /=.
by rewrite tnth_map/= tnth_ord_tuple.
Qed.

Arguments sub_countable [T U].
Arguments card_le_finite [T U].

Lemma bernoulli_mmt_gen_fun (X : bernoulliRV P p) (t : R) :
  'M_(bool_to_real R X : {RV P >-> R : realType}) t = (p * expR t + (1-p))%:E.
Proof.
rewrite/mmt_gen_fun.
pose mmtX : {RV P >-> R : realType} := expR \o t \o* (bool_to_real R X).
set A := X @^-1` [set true].
set B := X @^-1` [set false].
have mA: measurable A by exact: measurable_sfunP.
have mB: measurable B by exact: measurable_sfunP.
have dAB: [disjoint A & B]
  by rewrite /disj_set /A /B preimage_true preimage_false setICr.
have TAB: setT = A `|` B by rewrite -preimage_setU -setT_bool preimage_setT.
rewrite unlock.
rewrite TAB integral_setU_EFin -?TAB//.
under eq_integral.
  move=> x /=.
  rewrite /A inE /bool_to_real /= => ->.
  rewrite mul1r.
  over.
rewrite integral_cst//.
under eq_integral.
  move=> x /=.
  rewrite /B inE /bool_to_real /= => ->.
  rewrite mul0r.
  over.
rewrite integral_cst//.
rewrite /A /B /preimage /=.
under eq_set do rewrite (propext (rwP eqP)).
rewrite bernoulli_RV1.
under eq_set do rewrite (propext (rwP eqP)).
rewrite bernoulli_RV2.
rewrite -EFinD; congr (_ + _)%:E; rewrite mulrC//.
by rewrite expR0 mulr1.
Qed.

(* wrong lemma *)
Lemma binomial_mmt_gen_fun n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  let X := bernoulli_trial X_ : {RV \X_n P >-> R : realType} in
  'M_X t = ((p * expR t + (1 - p))`^(n%:R))%:E.
Proof.
move: p01 => /andP[p0 p1] bX/=.
rewrite bernoulli_trial_mmt_gen_fun//.
under eq_bigr => i _ do rewrite bernoulli_mmt_gen_fun//.
rewrite big_const iter_mule mule1 cardT size_enum_ord -EFin_expe powR_mulrn//.
by rewrite addr_ge0// ?subr_ge0// mulr_ge0// expR_ge0.
Qed.

Lemma mmt_gen_fun_expectation n (X_ : n.-tuple (bernoulliRV P p)) (t : R) :
  (0 <= t)%R ->
  let X := bernoulli_trial X_ : {RV \X_n P >-> R : realType} in
  'M_X t <= (expR (fine 'E_(\X_n P)[X] * (expR t - 1)))%:E.
Proof.
move=> t_ge0/=.
have /andP[p0 p1] := p01.
rewrite binomial_mmt_gen_fun// lee_fin.
rewrite expectation_bernoulli_trial//.
rewrite addrCA -{2}(mulr1 p) -mulrN -mulrDr.
rewrite -mulrA (mulrC (n%:R)) expRM ge0_ler_powR// ?nnegrE ?expR_ge0//.
  by rewrite addr_ge0// mulr_ge0// subr_ge0 -expR0 ler_expR.
exact: expR_ge1Dx.
Qed.

Lemma end_thm24 n (X_ : n.-tuple (bernoulliRV P p)) (t delta : R) :
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(\X_n P)[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: bernoulli_trial_ge0.
- by rewrite mulr_ge0// expR_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpM2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expRM lnK// posrE addr_gt0.
Qed.

(* theorem 2.4 Rajani / thm 4.4.(2) mu-book *)
Theorem bernoulli_trial_inequality1 n (X_ : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(\X_n P)[X] in
  (\X_n P) [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => delta0.
set X := @bernoulli_trial n X_.
set mu := 'E_(\X_n P)[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltrDl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expR (fine mu * (expR t - 1)))%:E *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  by apply: mmt_gen_fun_expectation; rewrite ltW.
rewrite mulrC expRM -mulNr mulrA expRM.
exact: end_thm24.
Qed.

(* theorem 2.5 *)
Theorem bernoulli_trial_inequality2 n (X : n.-tuple (bernoulliRV P p)) (delta : R) :
  let X' := @bernoulli_trial n X in
  let mu := 'E_(\X_n P)[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  (\X_n P) [set i | X' i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> X' mu n0 /[dup] delta01 /andP[delta0 _].
apply: (@le_trans _ _ (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK; last rewrite posrE addr_gt0//.
  exact: bernoulli_trial_inequality1.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    by rewrite fine_ge0//; apply: expectation_ge0 => t; exact: bernoulli_trial_ge0.
  rewrite lerB//.
  apply: taylor_ln_le.
  by rewrite in_itv /=.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

(* TODO: move (to exp.v?) *)
Lemma norm_expR : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

(* Rajani thm 2.6 / mu-book thm 4.5.(2) *)
Theorem bernoulli_trial_inequality3 n (X : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta < 1)%R ->
  let X' := @bernoulli_trial n X : {RV \X_n P >-> R : realType} in
  let mu := 'E_(\X_n P)[X'] in
  (\X_n P) [set i | X' i <= (1 - delta) * fine mu]%R <= (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> /andP[delta0 delta1] /=.
set X' := @bernoulli_trial n X : {RV \X_n P >-> R : realType}.
set mu := 'E_(\X_n P)[X'].
have /andP[p0 p1] := p01.
apply: (@le_trans _ _ (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    (\X_n P) [set i | (X' i <= (1 - delta) * fine mu)%R] = (\X_n P) [set i | `|(expR \o t \o* X') i|%:E >= (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltrNr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltrBlDr ltrDl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ (((fine 'E_(\X_n P)[normr \o expR \o t \o* X']) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite EFinM lee_pdivlMr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ (\X_n P) (expR \o t \o* X' : {RV (\X_n P) >-> R : realType}) id (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - by apply: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_(\X_n P)[expR \o t \o* X'] = 'M_X' t by [].
      by rewrite binomial_mmt_gen_fun.
  apply: (@le_trans _ _ (((expR ((expR t - 1) * fine mu)) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_(\X_n P)[expR \o t \o* X'] = 'M_X' t by [].
    rewrite binomial_mmt_gen_fun.
    rewrite /mu /X' expectation_bernoulli_trial.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expRM powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      by rewrite addr_ge0 ?mulr_ge0// subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expRM.
    rewrite addrCA -{2}(mulr1 p) -mulrBr addrAC subrr sub0r mulrC mulNr.
    by apply: expR_ge1Dx.
  rewrite !lnK ?posrE ?subr_gt0//.
  rewrite -addrAC subrr sub0r -mulrA [X in (_ / X)%R]expRM lnK ?posrE ?subr_gt0//.
  rewrite -[in leRHS]powR_inv1 ?powR_ge0// powRM// ?expR_ge0 ?invr_ge0 ?powR_ge0//.
  by rewrite powRAC powR_inv1 ?powR_ge0// powRrM expRM.
rewrite lee_fin.
rewrite -mulrN -mulrA [in leRHS]mulrC expRM ge0_ler_powR// ?nnegrE.
- by rewrite fine_ge0// expectation_ge0// => x; exact: bernoulli_trial_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- by rewrite expR_ge0.
- rewrite -ler_ln ?posrE ?divr_gt0 ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_div ?posrE ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK//.
  rewrite /powR (*TODO: lemma ln of powR*) gt_eqF ?subr_gt0// expRK.
  (* requires analytical argument: see p.66 of mu's book *)
  Local Open Scope ring_scope.
  rewrite -(@ler_pM2r _ 2)// -mulrA mulVf// mulr1 mulrDl.
  rewrite -subr_le0 mulNr opprK.
  rewrite addrC !addrA.
  have->: delta ^+ 2 - delta * 2 = (1 - delta)^+2 - 1.
    rewrite sqrrB expr1n mul1r [RHS]addrC !addrA addNr add0r addrC -mulNrn.
    by rewrite -(mulr_natr (- delta) 2) mulNr.
  rewrite addrAC subr_le0.
  set f := fun (x : R) => x ^+ 2 + - (x * ln x) * 2.
  have @idf (x : R^o) : 0 < x -> {df | is_derive x 1 (f : R^o -> R^o) df}.
    move=> x0; evar (df : (R : Type)); exists df.
    apply: is_deriveD; first by [].
    apply: is_deriveM; last by [].
    apply: is_deriveN.
    apply: is_deriveM; first by [].
    exact: is_derive1_ln.
  suff: forall x : R, x \in `]0, 1[ -> f x <= 1.
    by apply; rewrite memB_itv0 in_itv /= delta0 delta1.
  move=> x x01.
  have->: 1 = f 1 by rewrite /f expr1n ln1 mulr0 oppr0 mul0r addr0.
  apply: (@ger0_derive1_homo _ f 0 1 false false)=> //.
  - move=> t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - move=> t /[!in_itv] /= /andP [] t0 t1.
    Local Arguments derive_val {R V W a v f df}.
    rewrite (derive_val (svalP (idf _ t0))) /=.
    clear idf.
    rewrite exp_derive derive_cst derive_id .
    rewrite scaler0 add0r /GRing.scale /= !mulr1 expr1.
    rewrite -mulrDr mulr_ge0// divff ?lt0r_neq0//.
    rewrite opprD addrA subr_ge0 -ler_expR.
    have:= t0; rewrite -lnK_eq => /eqP ->.
    by rewrite -[leLHS]addr0 -(subrr 1) addrCA expR_ge1Dx.
  - apply: derivable_within_continuous => t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - by apply: (subset_itvW_bound _ _ x01); rewrite bnd_simp.
  - by rewrite in_itv /= ltr01 lexx.
  - by move: x01; rewrite in_itv=> /= /andP [] _ /ltW.
Qed.
Local Open Scope ereal_scope.

(* Rajani -> corollary 2.7 / mu-book -> corollary 4.7 *)
Corollary bernoulli_trial_inequality4 n (X : n.-tuple (bernoulliRV P p)) (delta : R) :
  (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (0 < p)%R ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_(\X_n P)[X'] in
  (\X_n P) [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> /andP[d0 d1] n0 p0 /=.
set X' := @bernoulli_trial n X.
set mu := 'E_(\X_n P)[X'].
under eq_set => x.
  rewrite ler_normr.
  rewrite lerBrDl opprD opprK -{1}(mul1r (fine mu)) -mulrDl.
  rewrite -lerBDr -(lerN2 (- _)%R) opprK opprB.
  rewrite -{2}(mul1r (fine mu)) -mulrBl.
  rewrite -!lee_fin.
  over.
rewrite /=.
rewrite set_orb.
rewrite measureU; last 3 first.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply/measurable_EFinP.
  exact: measurableT_comp.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply/measurable_EFinP.
  exact: measurableT_comp.
- rewrite disjoints_subset => x /=.
  rewrite /mem /in_mem/= => X0; apply/negP.
  rewrite -ltNge.
  apply: (@lt_le_trans _ _ _ _ _ _ X0).
  rewrite !EFinM.
  rewrite lte_pmul2r//; first by rewrite lte_fin ltrD2l gt0_cp.
  by rewrite fineK /mu/X' expectation_bernoulli_trial// lte_fin  mulr_gt0 ?ltr0n.
rewrite mulr2n EFinD leeD//=.
- by apply: bernoulli_trial_inequality2; rewrite //d0 d1.
- have d01 : (0 < delta < 1)%R by rewrite d0.
  apply: (le_trans (@bernoulli_trial_inequality3 _ X delta d01)).
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  by rewrite /X' lee_fin; exact: bernoulli_trial_ge0.
Qed.

(* Rajani thm 3.1 / mu-book thm 4.7 *)
Theorem sampling n (X : n.-tuple (bernoulliRV P p)) (theta delta : R) :
  let X_sum := bernoulli_trial X in
  let X' x := (X_sum x) / n%:R in
  (0 < p)%R ->
  (0 < delta <= 1)%R -> (0 < theta < p)%R -> (0 < n)%nat ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  (\X_n P) [set i | `| X' i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X_sum X' p0 /andP[delta0 delta1] /andP[theta0 thetap] n0 tdn.
have E_X_sum: 'E_(\X_n P)[X_sum] = (p * n%:R)%:E.
  by rewrite /X_sum expectation_bernoulli_trial// mulrC.
have /andP[_ p1] := p01.
set epsilon := theta / p.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : (\X_n P) [set i | `| X' i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in (\X_n P) X <= _](_ : _ =
      [set i | `| X_sum i - p * n%:R | >= epsilon * p * n%:R]%R); last first.
    apply/seteqP; split => [t|t]/=.
      move/(@ler_wpM2r _ n%:R (ler0n _ _)) => /le_trans; apply.
      rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R)// -normrM mulrBl.
      by rewrite -mulrA mulVf ?mulr1// gt_eqF ?ltr0n.
    move/(@ler_wpM2r _ n%:R^-1); rewrite invr_ge0// ler0n => /(_ erefl).
    rewrite -(mulrA _ _ n%:R^-1) divff ?mulr1 ?gt_eqF ?ltr0n//.
    move=> /le_trans; apply.
    rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R^-1)// -normrM mulrBl.
    by rewrite -mulrA divff ?mulr1// gt_eqF// ltr0n.
  rewrite -mulrA.
  have -> : (p * n%:R)%R = fine (p * n%:R)%:E by [].
  rewrite -E_X_sum.
  exact: (@bernoulli_trial_inequality4 _ X epsilon).
have step2 : (\X_n P) [set i | `| X' i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA.
  rewrite /epsilon -mulrA mulVf ?gt_eqF// mulr1 -!mulrA !ler_wpM2l ?(ltW theta0)//.
  rewrite mulrCA ler_wpM2l ?(ltW theta0)//.
  rewrite [X in (_ * X)%R]mulrA mulVf ?gt_eqF// -[leLHS]mul1r [in leRHS]mul1r.
  by rewrite ler_wpM2r// invf_ge1.
suff : delta%:E >= (\X_n P) [set i | (`|X' i - p| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in (\X_n P) X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p| < theta)%R]); last first.
    apply/seteqP; split => [t|t]/=.
      by rewrite leNgt => /negP.
    by rewrite ltNge => /negP/negPn.
  have ? : measurable [set i | (`|X' i - p| < theta)%R].
    under eq_set => x do rewrite -lte_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_lt => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  rewrite probability_setC// lee_subel_addr//.
  rewrite -lee_subel_addl//; last by rewrite fin_num_measure.
  move=> /le_trans; apply.
  rewrite le_measure ?inE//.
    under eq_set => x do rewrite -lee_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_le => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  by move=> t/= /ltW.
(* NB: last step in the pdf *)
apply: (le_trans step2).
rewrite lee_fin -(mulr_natr _ 2) -ler_pdivlMr//.
rewrite -(@lnK _ (delta / 2)); last by rewrite posrE divr_gt0.
rewrite ler_expR mulNr lerNl -lnV; last by rewrite posrE divr_gt0.
rewrite invf_div ler_pdivlMr// mulrC.
rewrite -ler_pdivrMr; last by rewrite exprn_gt0.
by rewrite mulrAC.
Qed.

End bernoulli.
