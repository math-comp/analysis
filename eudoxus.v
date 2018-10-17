(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
Definition is_qzendo (f : int -> int) :=
  exists k : int, forall m n : int, `|f (m + n) - (f m + f n)| < k.

Definition qzEndo :=
  [qualify a f : int -> int | `[<is_qzendo f>]].

Fact qzendo_key : pred_key qzEndo. Proof. by []. Qed.
Canonical qzendo_keyed := KeyedQualifier qzendo_key.

Record qzendo := QZEndo { qzendof :> int -> int; _ : qzendof \is a qzEndo }.

Canonical qzendo_subType := Eval hnf in [subType for qzendof].

Definition qzendo_eqMixin     := Eval hnf in [eqMixin of qzendo by <:].
Canonical  qzendo_eqType      := Eval hnf in EqType qzendo qzendo_eqMixin.
Definition qzendo_choiceMixin := [choiceMixin of qzendo by <:].
Canonical  qzendo_choiceType  := Eval hnf in ChoiceType qzendo qzendo_choiceMixin.

(* -------------------------------------------------------------------- *)
Lemma is_qzendoP (f : int -> int) :
  reflect
    (exists k : int, forall m n : int, `|f (m + n) - (f m + f n)| < k)
    (f \is a qzEndo).
Proof. by apply/asboolP. Qed.

(* -------------------------------------------------------------------- *)
Definition qzendoC (z : int) := fun x : int => x * z.

Local Notation "z %:E" := (qzendoC z).

Lemma qzendoC_is_additive z : additive (qzendoC z).
Proof. by move=> n m; rewrite /qzendoC; rewrite -mulrBl. Qed.

Canonical qzendoC_additive z := Additive (qzendoC_is_additive z).

(* -------------------------------------------------------------------- *)
Section QZEndoMorph.
Implicit Types f g : int -> int.

Lemma additive_is_qzendo (f : {additive int -> int}):
  GRing.Additive.apply f \is a qzEndo.
Proof.
apply/is_qzendoP; exists 1 => n m.
by rewrite [f (_ + _)]raddfD opprD addrACA !subrr normr0.
Qed.

Lemma is_qzendoC c : c%:E \is a qzEndo.
Proof. by apply: additive_is_qzendo. Qed.

Lemma is_qzendoD f g :
  f \is a qzEndo -> g \is a qzEndo -> f \+ g \is a qzEndo.
Proof.
move=> /is_qzendoP[kf bdf] /is_qzendoP[kg bdg].
apply/is_qzendoP; exists (kf + kg) => n m /=.
rewrite addrACA opprD addrACA.
by apply/(ler_lt_trans (ler_norm_add _ _))/ltr_add.
Qed.

Lemma is_qzendoN f : f \is a qzEndo -> \- f \is a qzEndo.
Proof.
case/is_qzendoP=> kf bdf; apply/is_qzendoP; exists kf.
by move=> n m /=; rewrite -!opprD normrN.
Qed.

Lemma is_qzendoM f g :
  f \is a qzEndo -> g \is a qzEndo -> f \o g \is a qzEndo.
Proof.
case/is_qzendoP=> kf bdf; case/is_qzendoP=> kg bdg.
pose M : int := \sum_(0 <= i < `|kg|) (`|f i| + `|f (- i%:Z)|).
apply/is_qzendoP; exists (M + kf *+ 2) => m n /=.
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

End QZEndoMorph.

(* -------------------------------------------------------------------- *)
Section QZEqv.

Definition qzeqv (f g : qzendo) :=
  `[<exists k : int, forall n : int, `|f n - g n| < k>].

Local Notation "~%E"   := qzeqv.
Local Notation "f ~ g" := (qzeqv f g).

Lemma qzeqvP (f g : qzendo) :
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

Lemma qzeqv_refl_eq (f g : qzendo) : f =1 g -> f ~ g.
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
Definition edxoppf (f : qzendo) : qzendo :=
  QZEndo (is_qzendoN (valP f)).

Definition edxaddf (f g : qzendo) : qzendo :=
  QZEndo (is_qzendoD (valP f) (valP g)).

Definition edxmulf (f g : qzendo) : qzendo  :=
  QZEndo (is_qzendoM (valP f) (valP g)).

Definition edxopp := lift_op1 eudoxus edxoppf.
Definition edxadd := lift_op2 eudoxus edxaddf.
Definition edxmul := lift_op2 eudoxus edxmulf.

(* -------------------------------------------------------------------- *)
Definition to_eudoxus :=
  lift_embed eudoxus (fun z : int => QZEndo (is_qzendoC z)).

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
case/is_qzendoP: (valP f') => /= kf hkf; exists (kf + M) => n.
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
+ admit.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/qzeqv_refl_eq.
  by move=> n /=; rewrite /qzendoC mulr1.
+ admit.
+ apply/eqP; rewrite !piE => /eqmodP/qzeqvP /= [k hk].
  have := (hk 0); rewrite /qzendoC normr0 => /ltrW ge0k.
  move/(_ (k+1)): hk; rewrite /qzendoC !(mulr0, mulr1).
  rewrite subr0 ger0_norm ?ler_paddr //.
  by apply/negP; rewrite -lerNgt ler_addl.
Admitted.

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
