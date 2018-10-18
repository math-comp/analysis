(* ==================================================================== *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import boolp classical_sets.

(* For gen_choiceType *)
(* ------- *) Require Import topology.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope quotient_scope.

(* -------------------------------------------------------------------- *)
Section PosNumMixin.
Context {F : idomainType} (p : pred F).

Hypothesis p_N0    : 0 \notin p.
Hypothesis p_1     : 1 \in p.
Hypothesis p_total : forall x, x != 0 -> (x \in p) || (-x \in p).
Hypothesis p_add   : {in p &, forall u v, u + v \in p}.
Hypothesis p_mul   : {in p &, forall u v, u * v \in p}.

Definition lt   (x y : F) := (y - x) \in p.
Definition le   (x y : F) := (x == y) || (lt x y).
Definition norm (x   : F) := if x \notin p then -x else x.

Local Lemma le0D x y : le 0 x -> le 0 y -> le 0 (x + y).
Proof.
rewrite /le /lt !subr0 => /orP[/eqP<-|px]; first by rewrite add0r.
case/orP => [/eqP<-|py]; first by rewrite addr0 px orbT.
by rewrite (p_add px py) orbT.
Qed.

Local Lemma le0M x y : le 0 x -> le 0 y -> le 0 (x * y).
Proof.
rewrite /le /lt !subr0 => /orP[/eqP<-|px]; first by rewrite mul0r eqxx.
case/orP=> [/eqP<-|py]; first by rewrite mulr0 eqxx.
by rewrite (p_mul px py) orbT.
Qed.

Local Lemma le_anti x : le 0 x -> le x 0 -> x = 0.
Proof.
rewrite /le /lt subr0 sub0r => /orP[/eqP<-//|px] /orP[/eqP<-//|pxN].
by apply/contraNeq: p_N0 => _; rewrite -[0](subrr x) p_add.
Qed.

Local Lemma sub_ge0  x y : le 0 (y - x) = le x y.
Proof. by rewrite /le /lt subr0 [0==_]eq_sym subr_eq0 eq_sym. Qed.

Local Lemma le_total x : le 0 x || le x 0.
Proof.
rewrite /le /lt [0==_]eq_sym orbCA !orbA orbb subr0 sub0r.
by case: eqP => //= /eqP /p_total.
Qed.

Local Lemma normN x : norm (- x) = norm x.
Proof.
have h v : v != 0 -> (v \in p) = (-v \notin p).
* move=> nz_v; apply/idP/idP => [pv|Npv].
  - by apply/contra: p_N0 => /(p_add pv); rewrite subrr.
  - by have := p_total nz_v; rewrite (negbTE Npv) orbF.
rewrite /norm !if_neg opprK; case: (x =P 0) => [->|/eqP nz_x].
* by rewrite oppr0 (negbTE p_N0).
by apply/esym; rewrite h // if_neg.
Qed.

Local Lemma ge0_norm x : le 0 x -> norm x = x.
Proof.
rewrite /norm /le /lt subr0.
by case/orP=> [/eqP<-|->//]; rewrite p_N0 oppr0.
Qed.

Local Lemma lt_def x y : lt x y = (y != x) && le x y.
Proof.
rewrite /le /lt eq_sym; case: eqP=> //= ->.
by rewrite subrr (negbTE p_N0).
Qed.

Definition PosNumMixin :=
  RealLeMixin le0D le0M le_anti sub_ge0 le_total normN ge0_norm lt_def.
End PosNumMixin.

(* -------------------------------------------------------------------- *)
Reserved Notation "\- f" (at level 40, left associativity).

Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition opp_fun_head t (f : U -> V) x := let: tt := t in - f x.
End LiftedZmod.

Local Notation "\- f" := (opp_fun_head tt f) : ring_scope.

(* -------------------------------------------------------------------- *)
Lemma equiv_refl_eq {T : Type} (e : equiv_rel T) (x y : T) :
  x = y -> e x y.
Proof. by move=> ->; apply: equiv_refl. Qed.

(* -------------------------------------------------------------------- *)
Local Reserved Notation "n %:E" (at level 2, left associativity, format "n %:E").
Local Reserved Notation "f ~ g" (at level 60, no associativity).
Local Reserved Notation "~%E"   (at level 0).

(* -------------------------------------------------------------------- *)
Delimit Scope eudoxus_scope with E.

(* ==================================================================== *)
Definition is_qzendo (k : int) (f : int -> int) :=
  forall m n, `|f (m + n) - (f m + f n)| < k.

Definition qzendo (k : int) :=
  [qualify a f : int -> int | `[<is_qzendo k f>]].

Fact qzendo_key k : pred_key (qzendo k). Proof. by []. Qed.
Canonical qzendo_keyed k := KeyedQualifier (qzendo_key k).

Notation "k .-qzendo" := (qzendo k)
  (at level 1, format "k .-qzendo") : form_scope.

(* -------------------------------------------------------------------- *)
Definition qzendoC (z : int) := fun x : int => x * z.

Local Notation "z %:E" := (qzendoC z).

(* ==================================================================== *)
Section QzEndoTheory.

Implicit Types (k kf kg : int) (f g : int -> int).

(* -------------------------------------------------------------------- *)
Lemma is_qzendoP k f :
  reflect
    (forall m n : int, `|f (m + n) - (f m + f n)| < k)
    (f \is a k.-qzendo).
Proof. by apply/asboolP. Qed.

Lemma is_qzendo_gt0 k f : f \is a k.-qzendo -> 0 < k.
Proof. by move/is_qzendoP => /(_ 0 0) /(ler_lt_trans _); apply. Qed.

Lemma is_qzendo_ge0 k f : f \is a k.-qzendo -> 0 <= k.
Proof. by move=> h; apply/ltrW/(is_qzendo_gt0 h). Qed.

Lemma qzendoC_is_additive z : additive (qzendoC z).
Proof. by move=> n m; rewrite /qzendoC; rewrite -mulrBl. Qed.

Canonical qzendoC_additive z := Additive (qzendoC_is_additive z).

Lemma additive_is_qzendo (f : {additive int -> int}):
  GRing.Additive.apply f \is a 1.-qzendo.
Proof.
apply/is_qzendoP => m n; rewrite [f (_ + _)]raddfD.
by rewrite opprD addrACA !subrr normr0.
Qed.

Lemma is_qzendoC c : c%:E \is a 1.-qzendo.
Proof. by apply: additive_is_qzendo. Qed.

Lemma is_qzendoD kf kg f g :
     f \is a kf.-qzendo
  -> g \is a kg.-qzendo
  -> f \+ g \is a (kf + kg).-qzendo.
Proof.
move=> /is_qzendoP bdf /is_qzendoP bdg.
apply/is_qzendoP => n m; rewrite addrACA opprD addrACA.
by apply/(ler_lt_trans (ler_norm_add _ _))/ltr_add.
Qed.

Lemma is_qzendoN k f : f \is a k.-qzendo -> \- f \is a k.-qzendo.
Proof.
move/is_qzendoP=> bdf; apply/is_qzendoP.
by move=> n m /=; rewrite -!opprD normrN.
Qed.

Lemma is_qzendoM kf kg f g :
     f \is a kf.-qzendo
  -> g \is a kg.-qzendo
  -> exists k, f \o g \is a k.-qzendo.
Proof.
move/is_qzendoP=> bdf; move/is_qzendoP=> bdg.
pose M : int := \sum_(0 <= i < `|kg|) (`|f i| + `|f (- i%:Z)|).
exists (M + kf *+ 2); apply/is_qzendoP => m n /=.
rewrite -[X in `|X - _|](subrK (f (g m + g n))).
rewrite -[X in `|X|]addrA (ler_lt_trans (ler_norm_add _ _)) //.
rewrite mulr2n addrA ltr_add //.
rewrite -[X in `|X|](subrK (f (g (m + n) - (g m + g n)))).
rewrite [X in _ < X]addrC (ler_lt_trans (ler_norm_add _ _)) ?ltr_le_add //.
+ by rewrite addrAC -{1}[g (m + n)](subrK (g m + g n)) -addrA -opprD.
rewrite {}/M; set k := g _ - _; rewrite (bigD1_seq `|k|%N) /=; first last.
+ by apply/iota_uniq.
+ rewrite mem_index_iota /k /= -ltz_nat !abszE.
  by apply/(ltr_le_trans (bdg _ _))/ler_norm.
rewrite !abszE ler_paddr ?sumr_ge0 //; case: (ger0P k) => _.
+ by apply/ler_addl.
+ by rewrite opprK; apply/ler_addr.
Qed.

End QzEndoTheory.

(* ==================================================================== *)
Section QZEndoBd.
Implicit Types (k : int) (f : int -> int).

Local Lemma qzendo_crossbdL k f :
  f \is a k.-qzendo -> forall m n : int,
    `|f (m * n) - m * f n| < (`|m| + 1) * k.
Proof.
move=> hf m n; elim/int_rec: m => [|m|m].
* rewrite !mul0r subr0 mul1r; move/is_qzendoP/(_ 0 0): hf.
  by rewrite addr0 opprD addrA subrr add0r normrN.
* rewrite -![`|_%:Z|]abszE !absz_nat => ihm.
  rewrite [in X in _ < X]intS -addrA mulrDl mul1r.
  have /is_qzendoP/(_ n (m%:Z * n)) lek := hf.
  apply/(ler_lt_trans _ (ltr_add lek ihm)).
  apply/(ler_trans _ (ler_norm_add _ _)).
  rewrite opprD addrA addrACA !addrA addrK.
  by rewrite intS !mulrDl !mul1r -addrA -opprD.
* rewrite !normrN -![`|_%:Z|]abszE !absz_nat !mulNr !opprK.
  move=> ihm; rewrite [in X in _ < X]intS mulrDl mul1r [1+_]addrC.
  have /is_qzendoP/(_ n (- (m.+1%:Z * n))) lek := hf.
  apply/(ler_lt_trans _ (ltr_add ihm lek)).
  apply/(ler_trans _ (ler_norm_sub _ _)).
  rewrite !opprD !opprK !addrA [X in `|X + _ + _|]addrAC.
  rewrite [X in n - X * n]intS mulrDl mul1r.
  rewrite opprD addrA subrr add0r subrr add0r.
  by rewrite addrC intS [1+_]addrC mulrDl mul1r.
Qed.

Lemma qzendo_crossbd k f :
  f \is a k.-qzendo -> forall m n : int,
    `|m * f n - n * f m| < (`|m| + `|n| + 2%:R) * k.
Proof.
move=> hf m n; rewrite (natrD _ 1 1) addrACA mulrDl.
have hL := qzendo_crossbdL hf m n.
have hR := qzendo_crossbdL hf n m.
apply/(ler_lt_trans _ (ltr_add hL hR)).
apply/(ler_trans _ (ler_norm_sub _ _)).
rewrite opprB [n * m]mulrC [in X in _ <= X]addrC.
by rewrite !addrA subrK distrC.
Qed.

Lemma qzendo_sublin k f :
  f \is a k.-qzendo ->
    exists A B : int, forall m : int, `|f m| < A * `|m| + B.
Proof.
move=> hf; exists (k + `|f 1|); exists (3%:R * k) => m.
have := qzendo_crossbd hf m 1; rewrite mul1r normr1 distrC.
rewrite -addrA -(natrD _ 1 2) -[(1+2)%N]/3 => h.
rewrite mulrDl addrAC [k*_]mulrC -mulrDl.
set M : int := `|f 1| * _; move: h; rewrite -(ltr_add2r M).
move/(ler_lt_trans _); apply; rewrite {}/M.
rewrite -normrM (ler_trans _ (ler_norm_add _ _)) //.
by rewrite [f 1 * _]mulrC subrK.
Qed.

End QZEndoBd.

(* ==================================================================== *)
Definition is_eqzendo (f : int -> int) :=
  exists k, f \is a k.-qzendo.

Definition eqzendo :=
  [qualify a f : int -> int | `[<is_eqzendo f>]].

Fact eqzendo_key : pred_key eqzendo. Proof. by []. Qed.
Canonical eqzendo_keyed := KeyedQualifier eqzendo_key.

(* ==================================================================== *)
Section EQzEndoTheory.

Implicit Types (k kf kg : int) (f g : int -> int).

(* -------------------------------------------------------------------- *)
Lemma is_eqzendoP f :
  reflect (exists k, f \is a k.-qzendo) (f \is a eqzendo).
Proof. by apply/asboolP. Qed.

(* -------------------------------------------------------------------- *)
Lemma is_eqzendoPP f :
  reflect
    (exists k : int, forall m n : int, `|f (m + n) - (f m + f n)| < k)
    (f \is a eqzendo).
Proof.
by apply: (iffP (is_eqzendoP f)) => -[k h]; exists k; apply/is_qzendoP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma qzendo_eqzendo k f :
  f \is a k.-qzendo -> f \is a eqzendo.
Proof. by move=> h; apply/is_eqzendoP; exists k. Qed.

Lemma is_eqzendoC c : c%:E \is a eqzendo.
Proof. by apply: (qzendo_eqzendo (is_qzendoC _)). Qed.

Lemma is_eqzendoD f g :
     f \is a eqzendo
  -> g \is a eqzendo
  -> f \+ g \is a eqzendo.
Proof.
move=> /is_eqzendoP[kf hf] /is_eqzendoP[kg hg].
by apply/(qzendo_eqzendo (is_qzendoD hf hg)).
Qed.

Lemma is_eqzendoN f : f \is a eqzendo -> \- f \is a eqzendo.
Proof.
by move=> /is_eqzendoP[kf hf]; apply/(qzendo_eqzendo (is_qzendoN hf)).
Qed.

Lemma is_eqzendoM f g :
     f \is a eqzendo
  -> g \is a eqzendo
  -> f \o g \is a eqzendo.
Proof.
move=> /is_eqzendoP[kf hf] /is_eqzendoP[kg hg].
by apply/is_eqzendoP/(is_qzendoM hf hg).
Qed.

End EQzEndoTheory.

(* ==================================================================== *)
Record qzEndo := QZEndo { qzendof :> int -> int; _ : qzendof \is a eqzendo }.

Canonical qzendo_subType := Eval hnf in [subType for qzendof].

Definition qzendo_eqMixin     := Eval hnf in [eqMixin of qzEndo by <:].
Canonical  qzendo_eqType      := Eval hnf in EqType qzEndo qzendo_eqMixin.
Definition qzendo_choiceMixin := [choiceMixin of qzEndo by <:].
Canonical  qzendo_choiceType  := Eval hnf in ChoiceType qzEndo qzendo_choiceMixin.

(* -------------------------------------------------------------------- *)
Section QZEqv.

Definition qzeqv (f g : qzEndo) :=
  `[<exists k : int, forall n : int, `|f n - g n| < k>].

Local Notation "~%E"   := qzeqv.
Local Notation "f ~ g" := (qzeqv f g).

Lemma qzeqvP (f g : qzEndo) :
  reflect
    (exists k : int, forall n : int, `|f n - g n| < k)
    (f ~ g).
Proof. by apply: asboolP. Qed.

Lemma qzeqv_is_equiv : equiv_class_of ~%E.
Proof. split.
+ by move=> f; apply/qzeqvP; exists 1 => n; rewrite subrr normr0.
+ suff sym f g: f ~ g -> g ~ f by move=> f g; apply/idP/idP => /sym.
  by case/qzeqvP=> [k hk]; apply/qzeqvP; exists k=> n; rewrite distrC.
+ move=> f g h /qzeqvP[k1 h1] /qzeqvP[k2 h2].
  apply/qzeqvP; exists (k1 + k2) => n.
  apply/(ler_lt_trans _ (ltr_add (h1 n) (h2 n))).
  apply/(ler_trans _ (ler_norm_add _ _)).
  by rewrite [f n - _]addrC addrACA addNr addr0.
Qed.

Lemma qzeqv_refl_eq (f g : qzEndo) : f =1 g -> f ~ g.
Proof.
move=> eq_fg; apply/qzeqvP; exists 1 => n.
by rewrite eq_fg subrr normr0.
Qed.

Canonical qzeqv_equiv := EquivRelPack qzeqv_is_equiv.
Canonical qzeqv_encModRel := defaultEncModRel ~%E.

Definition eudoxus := {eq_quot ~%E}.

Canonical eudoxus_quotType   := [quotType       of eudoxus].
Canonical eudoxus_eqType     := [eqType         of eudoxus].
Canonical eudoxus_choiceType := [choiceType     of eudoxus].
Canonical eudoxus_eqQuotType := [eqQuotType ~%E of eudoxus].

End QZEqv.

Local Notation "~%E"   := qzeqv.
Local Notation "f ~ g" := (qzeqv f g).

(* -------------------------------------------------------------------- *)
Definition edxoppf (f : qzEndo) : qzEndo :=
  QZEndo (is_eqzendoN (valP f)).

Definition edxaddf (f g : qzEndo) : qzEndo :=
  QZEndo (is_eqzendoD (valP f) (valP g)).

Definition edxmulf (f g : qzEndo) : qzEndo  :=
  QZEndo (is_eqzendoM (valP f) (valP g)).

Definition edxopp := lift_op1 eudoxus edxoppf.
Definition edxadd := lift_op2 eudoxus edxaddf.
Definition edxmul := lift_op2 eudoxus edxmulf.

(* -------------------------------------------------------------------- *)
Definition to_eudoxus :=
  lift_embed eudoxus (fun z : int => QZEndo (is_eqzendoC z)).

Canonical to_eudoxus_pi_morph := PiEmbed to_eudoxus.

(* -------------------------------------------------------------------- *)
Lemma pi_edxopp : {morph \pi_eudoxus : f / edxoppf f >-> edxopp f}.
Proof.
move=> f; unlock edxopp; apply/eqmodP/qzeqvP; rewrite /edxoppf /=.
set g := repr _; have: f ~ g by apply/eqmodP; rewrite reprK.
by case/qzeqvP=> k hk; exists k => n; rewrite -opprD normrN.
Qed.

Canonical pi_edxopp_morph := PiMorph1 pi_edxopp.

(* -------------------------------------------------------------------- *)
Lemma pi_edxadd : {morph \pi_eudoxus : f g / edxaddf f g >-> edxadd f g}.
Proof.
move=> f g; unlock edxadd; apply/eqmodP/qzeqvP; rewrite /edxaddf /=.
set f' := repr (_ f); set g' := repr (_ g).
have: g ~ g' by apply/eqmodP; rewrite reprK.
have: f ~ f' by apply/eqmodP; rewrite reprK.
move=> /qzeqvP[k1 h1] /qzeqvP[k2 h2]; exists (k1 + k2) => n.
rewrite opprD addrACA (ler_lt_trans _ (ltr_add (h1 n) (h2 n))) //.
by apply/ler_norm_add.
Qed.

Canonical pi_edxadd_morph := PiMorph2 pi_edxadd.

(* -------------------------------------------------------------------- *)
Lemma pi_edxmul : {morph \pi_eudoxus : f g / edxmulf f g >-> edxmul f g}.
Proof.
move=> f g; unlock edxmul; apply/eqmodP => /=.
set f' := repr (_ f); set g' := repr (_ g).
apply/(@equiv_trans _ _ (edxmulf f' g)); apply/qzeqvP=> /=.
+ have: f ~ f' by apply/eqmodP; rewrite reprK.
  by case/qzeqvP=> [k hk]; exists k.
have /qzeqvP[k hk]: g ~ g' by apply/eqmodP; rewrite reprK.
pose M : int := \sum_(0 <= j < `|k|) (`|f' j| + `|f' (- j%:Z)|).
case/is_eqzendoPP: (valP f') => /= kf hkf; exists (kf + M) => n.
rewrite -[X in `|X|](subrK (f' (g n - g' n))).
rewrite (ler_lt_trans (ler_norm_add _ _)) ?ltr_le_add //.
+ by rewrite addrAC -addrA -opprD -{1}[g n](subrK (g' n)).
rewrite {}/M (bigD1_seq `|g n - g' n|%N) /=; first last.
+ by apply/iota_uniq.
+ rewrite mem_index_iota /= -ltz_nat abszE.
  by apply/(ltr_le_trans (hk _))/ler_norm.
rewrite ler_paddr ?sumr_ge0 // !abszE; case: (ger0P (g n - g' n)) => _.
+ by rewrite ler_addl.
+ by rewrite opprK ler_addr.
Qed.

Canonical pi_edxmul_morph := PiMorph2 pi_edxmul.

(* -------------------------------------------------------------------- *)
Section EudoxusZModType.
Local Notation "n %:R" := (to_eudoxus n) : eudoxus_scope.
Local Notation "- f"   := (edxopp f    ) : eudoxus_scope.
Local Notation "f + g" := (edxadd f g  ) : eudoxus_scope.

(* -------------------------------------------------------------------- *)
Lemma edxzmod :
  [/\ associative edxadd
    , commutative edxadd
    , left_id (0%:R)%E edxadd
    & left_inverse (0%:R)%E edxopp edxadd].
Proof. split.
+ elim/quotW=> f; elim/quotW=> g; elim/quotW=> h /=.
  rewrite !piE; apply/eqmodP/qzeqv_refl_eq => n /=.
  by rewrite addrA.
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE.
  by apply/eqmodP/qzeqv_refl_eq => n /=; rewrite addrC.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/qzeqv_refl_eq.
  by move=> n /=; rewrite /qzendoC mulr0 add0r.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/qzeqv_refl_eq.
  by move=> n /=; rewrite addNr /qzendoC mulr0.
Qed.

Let edxaddA  := let: And4 h _ _ _ := edxzmod in h.
Let edxaddC  := let: And4 _ h _ _ := edxzmod in h.
Let edxadd0l := let: And4 _ _ h _ := edxzmod in h.
Let edxaddNl := let: And4 _ _ _ h := edxzmod in h.

Definition eudoxus_zmodMixin :=
  ZmodMixin edxaddA edxaddC edxadd0l edxaddNl.
Canonical eudoxus_zmodType :=
  Eval hnf in ZmodType eudoxus eudoxus_zmodMixin.
End EudoxusZModType.

(* -------------------------------------------------------------------- *)
Section EudoxusComRingType.
Local Notation "n %:R" := (to_eudoxus n) : eudoxus_scope.
Local Notation "f * g" := (edxmul f g  ) : eudoxus_scope.

Lemma edxcomring :
  [/\ associative edxmul
    , commutative edxmul
    , left_id (1%:R)%E edxmul
    , left_distributive edxmul +%R
    & (1%:R)%E != 0 ].
Proof. split.
+ elim/quotW=> f; elim/quotW=> g; elim/quotW=> h.
  by rewrite !piE /=; apply/eqmodP/qzeqv_refl_eq.
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE.
  case/is_eqzendoP: (valP f) => /= kf hf.
  case/is_eqzendoP: (valP g) => /= kg hg.
  have [Af [Bf subf]] := qzendo_sublin hf.
  have [Ag [Bg subg]] := qzendo_sublin hg.
  pose M := (6%:R + (Af + Bf) + (Ag + Bg)) * maxr kf kg.
  apply/eqmodP/qzeqvP; exists (maxr M (1 + `|f (g 0) - g (f 0)|)).
  move=> n; case: (n =P 0) => /= [->|/eqP nz_n].
  * by rewrite ltr_maxr ltz_add1r lerr orbT.
  rewrite ltr_maxr; apply/orP; left; rewrite {}/M.
  rewrite -(@ltr_pmul2l _ `|n|) ?normr_gt0 //.
  have /= h1 := qzendo_crossbd hf n (g n).
  have /= h2 := qzendo_crossbd hg (f n) n.
  have {h1 h2} /(ler_lt_trans (ler_norm_add _ _)) := ltr_add h1 h2.
  rewrite [g n * _]mulrC ![in X in X < _]addrA subrK -mulrBr normrM.
  move/ltr_le_trans; apply; set M := maxr _ _.
  set x1 := (X in X * _ + _); set x2 := (X in _ + X * _).
  have h1: x1 * kf <= (`|n| * (Ag + 1) + (Bg + 2%:R)) * M.
  * apply/ler_pmul; rewrite ?addr_ge0 ?(is_qzendo_ge0 hf) //; last first.
    - by rewrite /M ler_maxr lerr orTb.
    rewrite {}/x1 !addrA !ler_add2r mulrDr mulr1.
    by rewrite addrAC [X in X<=_]addrC ler_add2r mulrC 1?ltrW.
  have h2: x2 * kg <= (`|n| * (Af + 1) + (Bf + 2%:R)) * M.
  * apply/ler_pmul; rewrite ?addr_ge0 ?(is_qzendo_ge0 hg) //; last first.
    - by rewrite /M ler_maxr lerr orbT.
    rewrite {}/x2 !addrA !ler_add2r mulrDr mulr1.
    by rewrite addrAC ler_add2r mulrC 1?ltrW.
  apply/(ler_trans (ler_add h1 h2)); rewrite -mulrDl mulrA.
  apply/ler_wpmul2r; first by rewrite ler_maxr (is_qzendo_ge0 hf).
  rewrite addrACA -mulrDr => {M h1 h2 x1 x2}.
  set M := (X in _ + X <= _); set N := (X in `|n| * X).
  apply/(@ler_trans _ (`|n| * (N + M))).
  * rewrite mulrDr ler_add2l ler_pemull // ?addr_ge0 //.
    - move/(_ 0): subg; rewrite normr0 mulr0 add0r.
      by move/(ler_lt_trans _)/(ltrW); apply.
    - move/(_ 0): subf; rewrite normr0 mulr0 add0r.
      by move/(ler_lt_trans _)/(ltrW); apply.
    by rewrite -gtz0_ge1 normr_gt0.
  apply/ler_wpmul2l => //; rewrite {}/N {}/M.
  rewrite [X in X + _ <= _]addrACA [X in _ + X <= _]addrACA.
  rewrite [X in X <=  _]addrACA addrC [X in _ + X]addrACA.
  by rewrite [X in _ + X <= _]addrC -!addrA.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/qzeqv_refl_eq.
  by move=> n /=; rewrite /qzendoC mulr1.
+ elim/quotW=> f; elim/quotW=> g; elim/quotW=> h.
  by rewrite !piE /=; apply/eqmodP/qzeqv_refl_eq.
+ apply/eqP; rewrite !piE => /eqmodP/qzeqvP /= [k hk].
  have := (hk 0); rewrite /qzendoC normr0 => /ltrW ge0k.
  move/(_ (k+1)): hk; rewrite /qzendoC !(mulr0, mulr1).
  rewrite subr0 ger0_norm ?ler_paddr //.
  by apply/negP; rewrite -lerNgt ler_addl.
Qed.

Let edxmulA  := let: And5 h _ _ _ _ := edxcomring in h.
Let edxmulC  := let: And5 _ h _ _ _ := edxcomring in h.
Let edxmul1l := let: And5 _ _ h _ _ := edxcomring in h.
Let edxmulDl := let: And5 _ _ _ h _ := edxcomring in h.
Let edxmul10 := let: And5 _ _ _ _ h := edxcomring in h.

Definition eudoxus_ringMixin :=
  ComRingMixin edxmulA edxmulC edxmul1l edxmulDl edxmul10.

Canonical eudoxus_ringType := Eval hnf in RingType eudoxus eudoxus_ringMixin.
Canonical comRingType      := Eval hnf in ComRingType eudoxus edxmulC.
End EudoxusComRingType.
