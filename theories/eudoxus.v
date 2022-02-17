(* ==================================================================== *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import boolp classical_sets.

(* For gen_choiceType *)
(* ------- *) Require Import topology.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Def Num.Theory.
Import Order.POrderTheory Order.TotalTheory.

Local Open Scope ring_scope.
Local Open Scope int_scope.
Local Open Scope classical_set_scope.
Local Open Scope quotient_scope.

(* -------------------------------------------------------------------- *)
Section PosNumMixin.
Context {F : idomainType} (p : pred F).

Hypothesis p_N0    : 0 \notin p.
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

Local Lemma cmp0_total x : le 0 x || le x 0.
Proof.
rewrite /le /lt [0==_]eq_sym orbCA !orbA orbb subr0 sub0r.
by case: eqP => //= /eqP /p_total.
Qed.

Local Lemma le_total x y : le x y || le y x.
Proof. Admitted.

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
  RealLeMixin le0D le0M le_anti sub_ge0 cmp0_total normN ge0_norm lt_def.
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
Proof. by move/is_qzendoP => /(_ 0 0) /(le_lt_trans _); apply. Qed.

Lemma is_qzendo_ge0 k f : f \is a k.-qzendo -> 0 <= k.
Proof. by move=> h; apply/ltW/(is_qzendo_gt0 h). Qed.

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
by apply/(le_lt_trans (ler_norm_add _ _))/ltr_add.
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
rewrite -[X in `|X|]addrA (le_lt_trans (ler_norm_add _ _)) //.
rewrite mulr2n addrA ltr_add //.
rewrite -[X in `|X|](subrK (f (g (m + n) - (g m + g n)))).
rewrite [X in _ < X]addrC (le_lt_trans (ler_norm_add _ _)) ?ltr_le_add //.
+ by rewrite addrAC -{1}[g (m + n)](subrK (g m + g n)) -addrA -opprD.
rewrite {}/M; set k := g _ - _; rewrite (bigD1_seq `|k|%N) /=.
+ rewrite mem_index_iota /k /= -ltz_nat !abszE.
  by apply/(lt_le_trans (bdg _ _))/ler_norm.
+ by apply/iota_uniq.
rewrite !abszE ler_paddr ?sumr_ge0 //; case: (ger0P k) => _.
+ by apply/ler_addl.
+ by rewrite opprK; apply/ler_addr.
Qed.

Lemma is_qzendo_nat k f :
     (forall m n : nat, `|f (m + n)%:Z - (f m + f n)| < k)
  -> (forall n : nat, - f(- n%:Z) = f n)
  -> f \is a k.-qzendo.
Proof.
move=> qzf fN; have h m n: `|f (m%:Z - n%:Z) - (f m + (f (- n%:Z)))| < k.
+ rewrite -[f (-_)]opprK fN opprB addrA; case: (ltnP m n) => [lt_mn|ge_nm].
  * have := qzf (n - m)%N m; rewrite subnK 1?ltnW // opprD addrCA addrA.
    by rewrite -fN opprK -subzn 1?ltnW // opprB.
  * have := qzf n (m - n)%N; rewrite addnC subnK //.
    by rewrite opprD -distrC -opprB opprK subzn.
apply/is_qzendoP; case=> [] m [] n; rewrite ?NegzE -?PoszD //.
+ by rewrite [_ + n%:Z]addrC [_ + f n]addrC.
+ rewrite opprD !fN -opprD -PoszD -[X in `|X + _|]opprK.
  by rewrite fN addrC distrC.
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
  apply/(le_lt_trans _ (ltr_add lek ihm)).
  apply/(le_trans _ (ler_norm_add _ _)).
  rewrite opprD addrA addrACA !addrA addrK.
  by rewrite intS !mulrDl !mul1r -addrA -opprD.
* rewrite !normrN -![`|_%:Z|]abszE !absz_nat !mulNr !opprK.
  move=> ihm; rewrite [in X in _ < X]intS mulrDl mul1r [1+_]addrC.
  have /is_qzendoP/(_ n (- (m.+1%:Z * n))) lek := hf.
  apply/(le_lt_trans _ (ltr_add ihm lek)).
  apply/(le_trans _ (ler_norm_sub _ _)).
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
apply/(le_lt_trans _ (ltr_add hL hR)).
apply/(le_trans _ (ler_norm_sub _ _)).
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
move/(le_lt_trans _); apply; rewrite {}/M.
rewrite -normrM (le_trans _ (ler_norm_add _ _)) //.
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

Lemma eqzendo_suplin f (D : int) :
     0 < D
  -> f \is a eqzendo
  -> (forall k : int, exists2 n : int, 0 < n & k < f n)
  -> exists2 N : int, 0 < N & forall m : int, 0 < m -> f (m * N) > (m + 1) * D.
Proof.
move=> ge0_D edf infp; case/is_eqzendoPP: edf => C edfC.
pose E : int := C + D; case: (infp (2%:R * E)) => N gt0_n gt_E_fN.
exists N => //; case=> // k gt0_k; apply/(@lt_trans _ _ ((k%:Z + 1) * E)).
+ rewrite ltr_pmul2l; first by rewrite addrC ltz_add1r.
  by rewrite ltr_addr (le_lt_trans _ (edfC 0 0)).
case: k gt0_k => // k _; rewrite [_+1]addrC -intS.
elim: k => [|k ihk]; first by rewrite mul1r.
move: k.+1 ihk => {k} k ihk; have := edfC (k%:Z * N) N.
rewrite ltr_norml => /andP[h _]; move: h.
rewrite ltr_subr_addl (_ : k%:Z * N + N = (k.+1)%:Z * N).
+ by rewrite intS mulrDl mul1r addrC.
move/(lt_trans _); apply; rewrite intS mulrDl mul1r addrC -addrA.
apply: ltr_add => //; rewrite ltr_subr_addl.
apply: (lt_trans _ gt_E_fN); rewrite mulr_natl mulr2n.
by rewrite ltr_add2r /E ltr_addl.
Qed.

Definition eqzlift (g : nat -> int) :=
  fun (x : int) => match x with Posz x => g x | Negz x => - (g x.+1) end.

Lemma eqzendo_nat (g : nat -> int) :
     (exists C : int, forall m n, `|g (m + n)%N - g m - g n| < C)
  -> eqzlift g \is a eqzendo.
Proof.
case=> C hC; apply/is_eqzendoP; exists C; apply/is_qzendoP=> m n.
wlog: m n / (m <= n) => [wlog|]; first case: (lerP m n) => [|/ltW] /wlog //.
+ by rewrite [n+m]addrC [X in _-X]addrC.
case: m n => [m|m] [n|n] //= _.
+ by rewrite opprD addrA; apply: hC.
+ rewrite [Negz m + n]/GRing.add /=; case: ltnP => /=.
  * move=> lt_mn; rewrite distrC addrAC addrC addrA.
    by rewrite -{1}[n](subnKC lt_mn); apply: hC.
  * move=> le_nm; rewrite -subSn // opprD opprK addrCA addrA.
    by rewrite -{1}[m.+1](@subnK n) 1?ltnW.
+ by rewrite -opprD normrN addrA -addSn -addnS; apply: hC.
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

Definition eqv {T : Type} (f g : T -> int) :=
  `[<exists k : int, forall n : T, `|f n - g n| < k>].

Definition qzeqv (f g : qzEndo) := eqv f g.

Local Notation "~%E"   := eqv.
Local Notation "f ~ g" := (eqv f g).

Lemma eqvP {T : Type} (f g : T -> int) :
  reflect
    (exists k : int, forall n : T, `|f n - g n| < k)
    (f ~ g).
Proof. by apply: asboolP. Qed.

Lemma qzeqvP (f g : qzEndo) :
  reflect
    (exists k : int, forall n : int, `|f n - g n| < k)
    (f ~ g).
Proof. by apply: asboolP. Qed.

Lemma eqv_is_equiv {T : Type} : equiv_class_of (@eqv T).
Proof. split.
+ by move=> f; apply/eqvP; exists 1 => n; rewrite subrr normr0.
+ suff sym (f g : T -> int): f ~ g -> g ~ f.
  - by move=> f g; apply/idP/idP => /sym.
  by case/eqvP => [k hk]; apply/eqvP; exists k=> n; rewrite distrC.
+ move=> f g h /eqvP[k1 h1] /eqvP[k2 h2].
  apply/eqvP; exists (k1 + k2) => n.
  apply/(le_lt_trans _ (ltr_add (h1 n) (h2 n))).
  apply/(le_trans _ (ler_norm_add _ _)).
  by rewrite [f n - _]addrC addrACA addNr addr0.
Qed.

Lemma qzeqv_is_equiv : equiv_class_of qzeqv.
Proof.
case: (@eqv_is_equiv int) => hr hs ht; split.
+ by apply: hr. + by apply: hs. + by apply: ht.
Qed.

Lemma eqv_refl_eq (f g : int -> int) : f =1 g -> f ~ g.
Proof.
move=> eq_fg; apply/eqvP; exists 1 => n.
by rewrite eq_fg subrr normr0.
Qed.

Canonical eqv_equiv T := EquivRelPack (@eqv_is_equiv T).
Canonical qzeqv_equiv := EquivRelPack qzeqv_is_equiv.
Canonical qzeqv_encModRel := defaultEncModRel qzeqv.

Definition eudoxus := {eq_quot qzeqv}.

Canonical eudoxus_quotType   := [quotType         of eudoxus].
Canonical eudoxus_eqType     := [eqType           of eudoxus].
Canonical eudoxus_choiceType := [choiceType       of eudoxus].
Canonical eudoxus_eqQuotType := [eqQuotType qzeqv of eudoxus].

Lemma eqv_refl {T : Type} : reflexive (@eqv T).
Proof. by apply: equiv_refl. Qed.

Lemma eqv_sym {T : Type} : symmetric (@eqv T).
Proof. by apply: equiv_sym. Qed.

Lemma eqv_symL {T : Type} (f g : T -> int) : f ~ g -> g ~ f.
Proof. by rewrite eqv_sym. Qed.

Lemma eqv_trans {T : Type} : transitive (@eqv T).
Proof. by apply: equiv_trans. Qed.
End QZEqv.

Local Notation "~%E"   := eqv.
Local Notation "f ~ g" := (eqv f g).

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
set g := repr _; have: qzeqv f g by apply/eqmodP; rewrite reprK.
by case/qzeqvP=> k hk; exists k => n; rewrite -opprD normrN.
Qed.

Canonical pi_edxopp_morph := PiMorph1 pi_edxopp.

(* -------------------------------------------------------------------- *)
Lemma pi_edxadd : {morph \pi_eudoxus : f g / edxaddf f g >-> edxadd f g}.
Proof.
move=> f g; unlock edxadd; apply/eqmodP/qzeqvP; rewrite /edxaddf /=.
set f' := repr (_ f); set g' := repr (_ g).
have: qzeqv g g' by apply/eqmodP; rewrite reprK.
have: qzeqv f f' by apply/eqmodP; rewrite reprK.
move=> /qzeqvP[k1 h1] /qzeqvP[k2 h2]; exists (k1 + k2) => n.
rewrite opprD addrACA (le_lt_trans _ (ltr_add (h1 n) (h2 n))) //.
by apply/ler_norm_add.
Qed.

Canonical pi_edxadd_morph := PiMorph2 pi_edxadd.

(* -------------------------------------------------------------------- *)
Lemma pi_edxmul : {morph \pi_eudoxus : f g / edxmulf f g >-> edxmul f g}.
Proof.
move=> f g; unlock edxmul; apply/eqmodP => /=.
set f' := repr (_ f); set g' := repr (_ g).
apply/(@equiv_trans _ _ (edxmulf f' g)); apply/qzeqvP=> /=.
+ have: qzeqv f f' by apply/eqmodP; rewrite reprK.
  by case/qzeqvP=> [k hk]; exists k.
have /qzeqvP[k hk]: qzeqv g g' by apply/eqmodP; rewrite reprK.
pose M : int := \sum_(0 <= j < `|k|) (`|f' j| + `|f' (- j%:Z)|).
case/is_eqzendoPP: (valP f') => /= kf hkf; exists (kf + M) => n.
rewrite -[X in `|X|](subrK (f' (g n - g' n))).
rewrite (le_lt_trans (ler_norm_add _ _)) ?ltr_le_add //.
+ by rewrite addrAC -addrA -opprD -{1}[g n](subrK (g' n)).
rewrite {}/M (bigD1_seq `|g n - g' n|%N) /=.
+ rewrite mem_index_iota /= -ltz_nat abszE.
  by apply/(lt_le_trans (hk _))/ler_norm.
+ by apply/iota_uniq.
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
  rewrite !piE; apply/eqmodP/eqv_refl_eq => n /=.
  by rewrite addrA.
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE.
  by apply/eqmodP/eqv_refl_eq => n /=; rewrite addrC.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/eqv_refl_eq.
  by move=> n /=; rewrite /qzendoC mulr0 add0r.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/eqv_refl_eq.
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
  by rewrite !piE /=; apply/eqmodP/eqv_refl_eq.
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE.
  case/is_eqzendoP: (valP f) => /= kf hf.
  case/is_eqzendoP: (valP g) => /= kg hg.
  have [Af [Bf subf]] := qzendo_sublin hf.
  have [Ag [Bg subg]] := qzendo_sublin hg.
  pose M := (6%:R + (Af + Bf) + (Ag + Bg)) * maxr kf kg.
  apply/eqmodP/qzeqvP; exists (maxr M (1 + `|f (g 0) - g (f 0)|)).
  move=> n; case: (n =P 0) => /= [->|/eqP nz_n].
  * by rewrite lt_maxr ltz_add1r lexx orbT.
  rewrite lt_maxr; apply/orP; left; rewrite {}/M.
  rewrite -(@ltr_pmul2l _ `|n|) ?normr_gt0 //.
  have /= h1 := qzendo_crossbd hf n (g n).
  have /= h2 := qzendo_crossbd hg (f n) n.
  have {h1 h2} /(le_lt_trans (ler_norm_add _ _)) := ltr_add h1 h2.
  rewrite [g n * _]mulrC ![in X in X < _]addrA subrK -mulrBr normrM.
  move/lt_le_trans; apply; set M := maxr _ _.
  set x1 := (X in X * _ + _); set x2 := (X in _ + X * _).
  have h1: x1 * kf <= (`|n| * (Ag + 1) + (Bg + 2%:R)) * M.
  * apply/ler_pmul; rewrite ?addr_ge0 ?(is_qzendo_ge0 hf) //; last first.
    - by rewrite /M le_maxr lexx orTb.
    rewrite {}/x1 !addrA !ler_add2r mulrDr mulr1.
    by rewrite addrAC [X in X<=_]addrC ler_add2r mulrC 1?ltW.
  have h2: x2 * kg <= (`|n| * (Af + 1) + (Bf + 2%:R)) * M.
  * apply/ler_pmul; rewrite ?addr_ge0 ?(is_qzendo_ge0 hg) //; last first.
    - by rewrite /M le_maxr lexx orbT.
    rewrite {}/x2 !addrA !ler_add2r mulrDr mulr1.
    by rewrite addrAC ler_add2r mulrC 1?ltW.
  apply/(le_trans (ler_add h1 h2)); rewrite -mulrDl mulrA.
  apply/ler_wpmul2r; first by rewrite le_maxr (is_qzendo_ge0 hf).
  rewrite addrACA -mulrDr => {M h1 h2 x1 x2}.
  set M := (X in _ + X <= _); set N := (X in `|n| * X).
  apply/(@le_trans _ _ (`|n| * (N + M))).
  * rewrite mulrDr ler_add2l ler_pemull // ?addr_ge0 //.
    - move/(_ 0): subg; rewrite normr0 mulr0 add0r.
      by move/(le_lt_trans _)/ltW; apply.
    - move/(_ 0): subf; rewrite normr0 mulr0 add0r.
      by move/(le_lt_trans _)/ltW; apply.
    by rewrite -gtz0_ge1 normr_gt0.
  apply/ler_wpmul2l => //; rewrite {}/N {}/M.
  rewrite [X in X + _ <= _]addrACA [X in _ + X <= _]addrACA.
  rewrite [X in X <=  _]addrACA addrC [X in _ + X]addrACA.
  by rewrite [X in _ + X <= _]addrC -!addrA.
+ elim/quotW=> f; rewrite !piE; apply/eqmodP/eqv_refl_eq.
  by move=> n /=; rewrite /qzendoC mulr1.
+ elim/quotW=> f; elim/quotW=> g; elim/quotW=> h.
  by rewrite !piE /=; apply/eqmodP/eqv_refl_eq.
+ apply/eqP; rewrite !piE => /eqmodP/qzeqvP /= [k hk].
  have := (hk 0); rewrite /qzendoC normr0 => /ltW ge0k.
  move/(_ (k+1)): hk; rewrite /qzendoC !(mulr0, mulr1).
  rewrite subr0 ger0_norm ?ler_paddr //.
  by apply/negP; rewrite -leNgt ler_addl.
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

Lemma edxnatrE n : n%:R = \pi_eudoxus (QZEndo (is_eqzendoC n)) :> eudoxus.
Proof.
rewrite !piE; elim: n => [|n ihn]; first by rewrite mulr0n !piE.
rewrite mulrS ihn !piE; apply/eqmodP/eqv_refl_eq => /=.
by move=> k; rewrite /qzendoC /= -mulrDr intS.
Qed.

End EudoxusComRingType.

(* ==================================================================== *)
Section EudoxusPos.
Local Lemma edxposf_spec (f : int -> int) (C : int) :
     f \is a eqzendo
  -> (forall k : int, exists2 n : int, 0 < n & k < f n)
  -> exists N : int, forall p : int, N < p -> C < f p.
Proof.
move=> edf posf; wlog: C / 0 < C => [wlog|].
+ case: (ltrP 0 C) => [gt0_C|le0_C]; first by apply: wlog.
  case: (wlog 1) => // N hN; exists N => p /hN.
  by move/(le_lt_trans _); apply; apply/(le_trans le0_C).
move=> gt0_C; case/is_eqzendoPP: {+}edf => D edfD.
have [|M gt0_M slf] := eqzendo_suplin _ (D := D) edf posf.
+ by apply: (le_lt_trans _ (edfD 0 0)).
pose g (p : int) := f (p - (p %% M)%Z).
pose E : int := \sum_(0 <= i < `|M|) `|f i|.
have bd_fBg p : `|f p - g p| < E + D.
+ rewrite /g {1 2}[p](divz_eq _ M) addrK (addrC E D).
  rewrite -[X in `|X|](subrK (f (p %% M)%Z)).
  apply/(le_lt_trans (ler_norm_add _ _))/ltr_le_add.
  * by rewrite -addrA -opprD.
  rewrite /E (bigD1_seq (absz (p %% M)%Z)) /=.
  * rewrite mem_index_iota /= -ltz_nat !abszE ger0_norm.
    - by rewrite modz_ge0 //gt_eqF.
    by rewrite gtr0_norm // ltz_pmod.
  * by apply: iota_uniq.
  * rewrite abszE [`|(_ %% _)%Z|]ger0_norm ?modz_ge0 ?gt_eqF //.
    by rewrite ler_addl sumr_ge0.
pose n : int := ((E + D + C) %/ D)%Z; exists (n * M) => p ltp.
have := bd_fBg p; rewrite ltr_norml => /andP[h _]; move: h.
rewrite ltr_subr_addl => /(lt_trans _); apply.
rewrite ltr_subr_addl /g {1}[p](divz_eq _ M) addrK.
apply/(le_lt_trans _ (slf _ _)); last first.
+ suff ltMp: M < p.
  - rewrite -(ltr_pmul2r gt0_M) mul0r -[X in _<X](addrK (p %% M)%Z).
    by rewrite -divz_eq subr_gt0 (lt_trans _ ltMp) // ltz_pmod.
  apply/(le_lt_trans _ (ltp))/ler_pemull; first by apply/ltW.
  rewrite lez_divRL 1?(le_lt_trans _ (edfD 0 0)) // mul1r.
  by rewrite addrAC ler_addr addr_ge0 ?sumr_ge0 // ltW.
apply/(@le_trans _ _ ((n+1) * D)); last first.
+ rewrite ler_pmul2r 1?(le_lt_trans _ (edfD 0 0)) //.
  by rewrite ler_add2r lez_divRL 1?ltW.
rewrite /n mulrDl mul1r addrAC ler_add2r divzDr //.
rewrite divzz gt_eqF 1?(le_lt_trans _ (edfD 0 0)) //=.
rewrite mulrDl mul1r -[X in _ <= X + _](addrK ((E + C) %% D)%Z).
rewrite -divz_eq -[X in _ <= X]addrA ler_addl addrC subr_ge0.
by rewrite ltW // ltz_pmod // (le_lt_trans _ (edfD 0 0)).
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma edxzero_spec (f : qzEndo) :
     (exists C : int, forall n, `|f n| < C)
  -> f ~ QZEndo (is_eqzendoC 0).
Proof.
case=> C hfC; apply/qzeqvP; rewrite /qzendoC.
by exists C => n /=; rewrite mulr0 subr0.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma edxcmp0_spec (f : int -> int) : f \is a eqzendo ->
  [\/ exists C : int, forall n, `|f n| < C
    , forall C : int, exists N : int, forall p : int, N < p -> C < f p
    | forall C : int, exists N : int, forall p : int, N < p -> f p < -C].
Proof.
move=> edzf; pose P := exists C : int, forall n : int, `|f n| < C.
case/asboolP: {+}P => [hP|hNP]; first by constructor 1.
pose Qpos := forall k : int, exists2 n : int, 0 < n & k < f n.
pose Qneg := forall k : int, exists2 n : int, 0 < n & f n < k.
case/asboolP: {+}Qpos => [hQpos|hNQpos].
+ by constructor 2 => C; apply: edxposf_spec.
case/asboolP: {+}Qneg => [hQneg|hNQneg].
+ constructor 3 => C; case: (edxposf_spec (f := \- f) C).
  * by apply/is_eqzendoN.
  * move=> k; case: (hQneg (-k))=> n gt0_n h.
    by exists n => //=; rewrite ltr_oppr.
  by move=> N hN; exists N => p /hN /=; rewrite ltr_oppr.
have: exists2 c : int, 0 < c & forall n : int, 0 < n -> f n < c.
+ move/asboolPn/existsp_asboolPn: hNQpos => [c hc].
  exists (maxr 0 c + 1); first by rewrite ltz_addr1 le_maxr lexx.
  move=> n gt0_n; rewrite ltz_addr1 le_maxr -(rwP orP); right.
  by rewrite leNgt -(rwP negP) => h; apply/hc; exists n.
have: exists2 c : int, 0 < c & forall n : int, 0 < n -> - c < f n.
+ move/asboolPn/existsp_asboolPn: hNQneg => [c hc].
  exists (maxr (1 - c) 1); first by rewrite lt_maxr ltr01 orbT.
  move=> n gt0_n; rewrite ltr_oppl lt_maxr -(rwP orP); left.
  rewrite ltr_oppl opprB ltr_subl_addr ltz_addr1.
  by rewrite leNgt -(rwP negP) => h; apply/hc; exists n.
case=> [cN gt0_cN hN] [cP gt0_cP hP].
have: exists2 C : int, 0 < C & forall n : int, 0 < n -> `|f n| < C.
+ exists (maxr cP cN); first by rewrite lt_maxr gt0_cP.
  move=> n gt0_n; rewrite ltr_norml ltr_oppl !lt_maxr.
  by rewrite hP //= andbT [X in _ || X]ltr_oppl hN // orbT.
case=> C gt0_C hC; case/is_eqzendoPP: edzf=> D hD.
have gt0_D: 0 < D by apply/(le_lt_trans _ (hD 0 0)).
absurd False => //; apply/hNP; exists (C + D + `|f 1|).
move=> n; case: (ltrP 0 n) => [gt0_n|le0_n].
+ rewrite -addrA (lt_trans (hC _ gt0_n)) // ltr_addl.
  by rewrite (lt_le_trans gt0_D) // ler_addl.
have: `|f (1 - n)| < C by apply: hC; rewrite subr_gt0.
rewrite -addrA -(ltr_add2r (D + `|f 1|)) => /(le_lt_trans _); apply.
rewrite addrCA; have := hD (1 - n) n; rewrite subrK.
rewrite -(ltr_add2r (`|f (1 - n)| + `|f 1|)).
move/ltW/(le_trans _); apply. set x := (X in _ <= X + _).
have := ler_norm_sub (f (1 - n)) (f 1); rewrite -(ler_add2l x).
move/(le_trans _); apply; apply/(le_trans _ (ler_norm_add _ _)).
rewrite [X in _ <= `|X|]addrC !addrA subrK.
by rewrite opprD addrCA addKr normrN.
Qed.

(* -------------------------------------------------------------------- *)
Definition edxposf (f : qzEndo) :=
  `[<forall k : int, exists2 n : int, 0 < n & k < f n>].

Definition edxpos := lift_fun1 eudoxus edxposf.

(* -------------------------------------------------------------------- *)
Lemma edxposfP (f : qzEndo) :
  reflect
    (forall k : int, exists2 n : int, 0 < n & k < f n)
    (edxposf f).
Proof. by apply/asboolP. Qed.

(* -------------------------------------------------------------------- *)
Lemma edxposfPE (f : qzEndo) : edxposf f ->
  forall C : int, exists N : int, forall p : int, N < p -> C < f p.
Proof.                          (* See edxposf_spec *)
move=> /edxposfP gt0_f; case: (edxcmp0_spec (valP f)) => //=.
+ case=> C lt_fC; suff: C < C by rewrite ltxx.
  move/(_ C): gt0_f => [n _ le_Cf]; rewrite (lt_trans le_Cf) //.
  by rewrite (le_lt_trans (ler_norm _)).
+ move=> /(_ 0) [N]; rewrite oppr0 => h.
  pose M : int := \sum_(0 <= i < `|N|.+1) `|f i|.
  move/(_ M): gt0_f => [] [] // n _; rewrite ltNge => /negP[].
  rewrite {}/M; case: (ltnP n `|N|.+1) => [lt_n_SN|].
  * rewrite (bigD1_seq n) 1?(iota_uniq, mem_iota) //=.
    by rewrite ler_paddr 1?ler_norm //= sumr_ge0.
  * rewrite -ltz_nat abszE => /(le_lt_trans (ler_norm _)) /h.
    by move/ltW/le_trans; apply; rewrite sumr_ge0.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma pi_edxpos_r (f g : qzEndo) : f ~ g -> edxposf f -> edxposf g.
Proof.
case/qzeqvP=> C bdC /edxposfP /edxposf_spec h.
apply/edxposfP => k; case/(_ (C + k) (valP _)): h.
move=> N hN; exists (maxr 0 N + 1); first by rewrite ltz_addr1 le_maxr.
set p : int := maxr _ _ + _; have := bdC p; rewrite distrC.
rewrite ltr_norml => /andP[h _]; move: h.
rewrite ltr_subr_addl => /(lt_trans _); apply.
rewrite ltr_subr_addl; apply: hN; rewrite ltz_addr1.
by rewrite le_maxr lexx orbT.
Qed.

(* -------------------------------------------------------------------- *)
Lemma pi_edxpos : {mono \pi_eudoxus : f / edxposf f >-> edxpos f}.
Proof.
move=> f; unlock edxpos; apply/idP/idP; apply: pi_edxpos_r;
  by rewrite -/(qzeqv _ _); apply/eqmodP; rewrite reprK.
Qed.

Canonical pi_edxpos_morph := PiMono1 pi_edxpos.

(* -------------------------------------------------------------------- *)
Lemma edxpos_order :
  [/\ 0 \notin edxpos
    , (forall x : eudoxus, x != 0 -> (x \in edxpos) || (-x \in edxpos))
    , {in edxpos &, forall u v : eudoxus, u + v \in edxpos}
    & {in edxpos &, forall u v : eudoxus, u * v \in edxpos} ].
Proof. split.
+ rewrite !piE; apply/edxposfP => /(_ 1) [n _] /=.
  by rewrite /qzendoC mulr0.
+ elim/quotW=> f; rewrite !piE /= => h.
  case: (edxcmp0_spec (valP f)) => /= [|hf|hNf]; first last.
  + apply/orP; right; apply/edxposfP => /= k; case: (hNf k).
    move=> N hN; exists (`|N| + 1); first by rewrite ltz_addr1.
    by rewrite ltr_oppr hN // ltz_addr1 ler_norm.
  + apply/orP; left; apply/edxposfP => /= k; case: (hf k).
    move=> N hN; exists (`|N| + 1); first by rewrite ltz_addr1.
    by rewrite hN // ltz_addr1 ler_norm.
  by move/edxzero_spec; rewrite -/(qzeqv _ _) (negbTE h).
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE /=.
  move=> /edxposfP hf /edxposfP hg; apply/edxposfP => k.
  case/(edxposf_spec `|k| (valP _)): hf => /= kf hkf.
  case/(edxposf_spec `|k| (valP _)): hg => /= kg hkg.
  exists (maxr 0 (maxr kf kg) + 1); first by rewrite ltz_addr1 le_maxr.
  apply/(@le_lt_trans _ _ (`|k| + `|k|)).
  * by apply/(le_trans (ler_norm _))/ler_addr.
  by rewrite ltr_add ?(hkf, hkg) // ltz_addr1 !le_maxr lexx !orbT.
+ elim/quotW=> f; elim/quotW=> g; rewrite !piE /=.
  move=> /edxposfP hf /edxposfP hg; apply/edxposfP => k.
  case/(edxposf_spec `|k | (valP _)): hf => /= kf hkf.
  case/(edxposf_spec `|kf| (valP _)): hg => /= kg hkg.
  exists (`|kg| + 1); first by rewrite ltz_addr1. 
  apply/(le_lt_trans (ler_norm _))/hkf.
  apply/(le_lt_trans (ler_norm _))/hkg.
  by rewrite ltz_addr1 ler_norm.
Qed.
End EudoxusPos.

(* ==================================================================== *)
Section EudoxusFieldType.

(*
Lemma eqvPd {T : Type} (f g : T -> int) : f ~ g <->
  exists C : int, forall n, exists2 a : int,
    `|a| < C & g n = f n + a.
Proof. split.
* case/eqvP=> C bdC; exists C => n; exists (g n - f n) => //.
  + by rewrite distrC. + by rewrite addrCA subrr addr0.
* case=> C bdC; apply/eqvP; exists C => n; case: (bdC n).
  by move=> a lt_aC ->; rewrite opprD addrA subrr add0r normrN.
Qed.


*)  
Lemma qzeqvDC (f : qzEndo) (c : int) : (f \o (fun x => x + c)) ~ f.
Proof.
case/is_eqzendoPP: (valP f) => /= C bdC; apply/eqvP; exists (C + `|f c|).
move=> k /=; move/(_ k c): bdC; rewrite -{1}(ltr_add2r `|f c| _ C).
by move/(le_lt_trans (ler_norm_add _ _)); rewrite opprD -!addrA addNr addr0.
Qed.

(*
Lemma qzeqvN (f : qzEndo) : f \o [eta -%R] ~ - (val f).
Proof.
case/is_eqzendoPP: (valP f) => /= C bdC.
apply/eqvP; exists (C + `|f 0|) => x; rewrite opprK /=.
move/(_ x (-x)): bdC; rewrite subrr distrC -{1}(ltr_add2r `|f 0| _ C).
by move/(ler_lt_trans (ler_norm_add _ _)); rewrite -addrA addNr addr0 addrC.
Qed.
*)

Lemma qzeqvD {T : Type} (El Er : T -> int) (f : qzEndo) :
  (fun x => f (El x + Er x)) ~ (fun x => f (El x) + f (Er x)).
Proof.
case/is_eqzendoPP: (valP f) => /= C bdC.
by apply/eqvP; exists C => n; apply: bdC.
Qed.

Lemma qzeqvN {T : Type} (E : T -> int) (f : qzEndo) :
  (fun x => f (- (E x))) ~ (fun x => - (f (E x))).
Proof. Admitted.

Lemma qzeqvD_split {T : Type} (f1 f2 g1 g2 : T -> int) :
  f1 ~ g1 -> f2 ~ g2 -> f1 \+ f2 ~ g1 \+ g2.
Proof. Admitted.

Lemma qzeqvN_split {T : Type} (f  g : T -> int) :
  f ~ g -> \- f ~ \-  g.
Proof. Admitted.

Lemma eqv_eq {T : Type} (g f : T -> int) : f =1 g -> f ~ g.
Proof. by move=> /funext ->. Qed.

Let D := (int * (int * int))%type.

Lemma L1 (f : qzEndo) :
    (fun x : D => f (x.1 - x.2.1 - x.2.2))
  ~ (fun x : D => f x.1 - f (x.2.1-1) - f (x.2.2-1)).
Proof.
apply: (@eqv_trans _ (fun x : D => f (x.1 - (x.2.1 + x.2.2)))).
+ by apply: eqv_eq => /= -[r [p q]] /=; rewrite opprD addrA.
apply: (eqv_trans (qzeqvD _ _ f)); rewrite eqv_sym.
apply: (@eqv_trans _ (fun x : D => f x.1 - (f (x.2.1-1) + f (x.2.2-1)))).
+ by apply: eqv_eq=> /= -[r [p q]] /=; rewrite opprD addrA.
apply/qzeqvD_split=> //; rewrite eqv_sym.
apply/(eqv_trans (qzeqvN _ f))/qzeqvN_split.
apply/(eqv_trans (qzeqvD _ _ f))/qzeqvD_split.
+ rewrite eqv_sym.
Admitted.

Lemma L2 (f : qzEndo) :
    (fun x : D => f (x.1 - x.2.1 - x.2.2))
  ~ (fun x : D => f (x.1-1) - f x.2.1 - f x.2.2).
Proof. Admitted.

Lemma eqv_eqzendo f g :
  f ~ g -> f \is a eqzendo -> g \is a eqzendo.
Proof.
move/eqvP=> [C hC] /is_eqzendoP[C' /is_qzendoP hC'].
apply/is_eqzendoP; exists (C *+ 3 + C'); apply/is_qzendoP=> m n.
apply: (le_lt_trans (@ler_dist_add _ _ (f (m + n)) _ _)).
rewrite mulrS -addrA ltr_add //; first by rewrite distrC hC.
apply: (le_lt_trans (@ler_dist_add _ _ (f m + f n) _ _)).
rewrite [X in _ < X]addrC ltr_add // opprD addrACA.
by apply: (le_lt_trans (ler_norm_add _ _)); rewrite ltr_add.
Qed.

Lemma edxinv_r (x : qzEndo) :
  edxposf x -> { y : eudoxus | y * \pi_eudoxus x = 1 }.
Proof.
move: x => f; wlog: f / forall n : nat, f (Negz n) = - (f n.+1) => [wlog gt0_f|].
  pose g := eqzlift (fun n => f n%:Z); have eq_fg: f ~ g.
    have /= := qzeqvN idfun f => /eqvP[C hC].
    apply/eqvP; exists `|C|.+1; case=> n /=.
      by rewrite subrr normr0.
    have /= := hC n.+1%:Z; rewrite NegzE => /lt_trans; apply.
    by apply: (le_lt_trans (ler_norm _)); rewrite ltz_nat.
  pose gh := QZEndo (eqv_eqzendo eq_fg (valP f)); case: (wlog gh) => //.
    by apply: (@pi_edxpos_r _ gh eq_fg gt0_f).
  move=> gI hV; exists gI; rewrite -[RHS]hV.
  by congr (_ * _); apply/eqmodP.
move=> fNE gt0_f; have h (p : nat) : exists n : nat, p%:Z <= f n.
  by move/edxposfP: gt0_f => /(_ p) [] [|//] n _ /ltW ?; exists n.
pose g p := (ex_minn (h p))%:Z.
have [N gt0_g]: { N | forall n, (N <= n)%N -> 0 < g n}.
  exists `|f 0|.+1 => n lt_f0_n; rewrite /g; case: ex_minnP.
  case=> //; rewrite leNgt => /negP[].
  by rewrite (le_lt_trans (ler_norm _)).
have comp_fg : forall n : nat, f (g n) >= n%:Z.
  by move=> n; rewrite /g; case: ex_minnP.
have hrg: forall r, (N <= r)%N -> f (g r - 1) < r%:Z <= f (g r).
  move=> r /gt0_g; rewrite /g; case: ex_minnP.
  move=> m le_m_fr hmin gt0_m; rewrite le_m_fr andbT.
  rewrite ltNge; apply/negP; rewrite -predn_int //.
  move/hmin; case: {le_m_fr hmin} m gt0_m => //=.
  by move=> m _; rewrite ltnn.
have h1: forall m n, (N <= m)%N -> (N <= n)%N ->
  0 < f (g (m + n)%N) - f (g m - 1) - f (g n - 1).
  move=> m n le_Nm le_Nn; rewrite -[X in X<_](subrr (m%:Z + n%:Z)).
  rewrite opprD !addrA ltr_sub //; last by case/andP: (hrg _ le_Nn).
  rewrite ler_lt_sub //; last by case/andP: (hrg _ le_Nm).
  suff: (N <= m + n)%N by move/hrg => /andP[].
  by apply: (leq_trans le_Nm); rewrite leq_addr.
have h2: forall m n, (N <= m)%N -> (N <= n)%N ->
  f (g (m + n)%N - 1) - f (g m) - f (g n) < 0.
  move=> m n le_Nm le_Nn; rewrite -[X in _<X](subrr (m%:Z + n%:Z)).
  rewrite opprD !addrA ltr_le_sub // ltr_le_sub //.
  suff: (N <= m + n)%N by move/hrg => /andP[].
  by apply: (leq_trans le_Nm); rewrite leq_addr.
suff hg: eqzlift (fun p => g (N + p)%N) \is a eqzendo.
  exists (\pi_eudoxus (QZEndo hg)).
  rewrite mulrC !piE; apply/eqmodP/qzeqvP=> /=.
  suff [C hC]: exists C : int, forall n, (N <= n)%N -> `|f (g n) - n%:Z| < C.
    have bdnat n: `|f (g (N + n)%N) - n%:Z| < C + N.
      rewrite -[X in `|X|](@subrK _ N%:Z).
      apply: (le_lt_trans (ler_norm_add _ _)); rewrite ltr_le_add //.
      by rewrite -addrA -opprD [(N+_)%N]addnC hC // leq_addl.
    exists (C + N%:Z) => n; rewrite /qzendoC mulr1; case: n => //= n.
    set x := (X in g X); rewrite NegzE (_ : f (- (g x)) = -(f (g x))).
      have := (gt0_g x (leq_addr _ _)); case: (g x) => //.
      by case=> // p _; rewrite -NegzE fNE.
    by rewrite -opprD normrN {}/x.
  have /eqvP[/= C hC] := qzeqvDC f (-1); exists `|C|.+1.
    move=> n le_Nn; rewrite ltr_norml (@lt_le_trans _ _ 0) /=.
    - by rewrite oppr_lt0.
    - by rewrite subr_ge0; have /andP[] := hrg _ le_Nn.
    rewrite (@le_lt_trans _ _ `|C|) //; last by rewrite ltz_nat ltnS.
    apply: (@le_trans _ _ (f (g n) - f (g n - 1))).
      by rewrite ler_sub //; have /andP[/ltW] := hrg _ le_Nn.
    have /ltW := hC (g n); rewrite distrC ler_norml => /andP[_].
    by move/le_trans; apply; rewrite ler_norm.
set gh := fun p => g (N + p)%N; apply: eqzendo_nat.
have [C hC]: exists C : int, forall (m n : nat),
    `|f (gh (n + m)%N - gh n - gh m)| < C.
  suff [C hC]: exists C : int, forall (m n : nat),
    (N <= m)%N -> (N <= n)%N -> `|f (g (n + m)%N - g n - g m)| < C.
  exists C.
(*
  + have bd1: exists C : int, forall (m n : nat),
      (N <= m)%N -> (N <= n)%N -> f (g (n + m)%N - g n - g m) > C.
    have /eqvP[C hC] := L1 f; exists (-C) => m n le_Mm le_Mn.
    move/(_ (g (n + m)%N, (g n, g m))): hC => /=; rewrite ltr_norml.
    case/andP=> [+ _] => /ltr_trans; apply; rewrite ltr_subl_addr.
    by rewrite ltr_spaddr //; apply: h1.
  + have bd2: exists C : int, forall (m n : nat),
      (N <= m)%N -> (N <= n)%N -> f (g (n + m)%N - g n - g m) < C.
    have /eqvP[C hC] := L2 f; exists C => m n le_Mm le_Mn.
    move/(_ (g (n + m)%N, (g n, g m))): hC => /=; rewrite ltr_norml.
    case/andP=> _ /(ltr_trans _); apply; rewrite ltr_subr_addr.
    by rewrite ltr_snaddr //; apply: h2.
  case: bd1 bd2 => {h1 h2} [C1 h1] [C2 h2]; pose C := Num.max `|C1| `|C2|.
  exists C; move=> m n le_Mm le_Mn; rewrite ltr_norml.
  rewrite andbC ltr_maxr orbC ltr_normr h2 //= ltr_oppl.
  by rewrite ltr_maxr ltr_normr ltr_opp2 h1 ?Monoid.simpm.



case/boolP: [exists p : 'I_N, g p <= 0]; last first.
  move/existsPn=> /= gt0_g_le; exists 0%N => n.
  rewrite leq0n; apply/esym; case: (leqP N n) => [/gt0_g//|lt_nN].
  by move/(_ (Ordinal lt_nN)): gt0_g_le; rewrite -ltrNge.
move=> ge0_g; have {}ge0_g: exists p, g p <= 0.
* by case/existsP: ge0_g=> /= x ge0_gx; exists (val x).
have bdN p: g p <= 0 -> (p <= N)%N.
* by apply: contraLR; rewrite -ltrNge -ltnNge => /ltnW /gt0_g.
exists (ex_maxn ge0_g bdN).+1 => n; case: ex_maxnP => m.
move=> le0_gm hmax; apply/idP/idP.
* move=> lt_mn; rewrite ltrNge; apply/negP.
  by move/hmax; rewrite leqNgt lt_mn.
* move/(ler_lt_trans le0_gm); apply: contraLR.
  by rewrite -lerNgt -ltnNge ltnS; apply: homo_g.



have homo_g: forall x y, (x <= y)%N -> (g x <= g y).
+ move=> x y le_xy; rewrite /g.
  case: ex_minnP=> m le_fm hm; case: ex_minnP=> n le_fn hn.
  by apply/hm/(ler_trans _ le_fn); rewrite lez_nat.
have hC: exists C : int, forall n m, `|g (n + m)%N - g n - g m| <= C.
+ have [N gt0_g]: exists N, forall n, (N <= n)%N = (0 < g n).
  - have [N gt0_g]: exists N, forall n, (N <= n)%N -> 0 < g n.
      exists `|f 0|.+1 => n lt_f0_n; rewrite /g; case: ex_minnP.
      case=> //; rewrite lerNgt => /negP[].
      by rewrite (ler_lt_trans (ler_norm _)).
    case/boolP: [exists p : 'I_N, g p <= 0]; last first.
      move/existsPn=> /= gt0_g_le; exists 0%N => n.
      rewrite leq0n; apply/esym; case: (leqP N n) => [/gt0_g//|lt_nN].
      by move/(_ (Ordinal lt_nN)): gt0_g_le; rewrite -ltrNge.
    move=> ge0_g; have {}ge0_g: exists p, g p <= 0.
    * by case/existsP: ge0_g=> /= x ge0_gx; exists (val x).
    have bdN p: g p <= 0 -> (p <= N)%N.
    * by apply: contraLR; rewrite -ltrNge -ltnNge => /ltnW /gt0_g.
    exists (ex_maxn ge0_g bdN).+1 => n; case: ex_maxnP => m.
    move=> le0_gm hmax; apply/idP/idP.
    * move=> lt_mn; rewrite ltrNge; apply/negP.
      by move/hmax; rewrite leqNgt lt_mn.
    * move/(ler_lt_trans le0_gm); apply: contraLR.
      by rewrite -lerNgt -ltnNge ltnS; apply: homo_g.
  have eq0_g n: (n < N)%N = (g n == 0).
  + by rewrite ltnNge gt0_g -lerNgt lez_nat leqn0.
  have hrg: forall r, (N <= r)%N -> f (g r - 1) < r%:Z <= f (g r).
  - move=> r; rewrite gt0_g /g; case: ex_minnP.
    move=> m le_m_fr hmin gt0_m; rewrite le_m_fr andbT.
    rewrite ltrNge; apply/negP; rewrite -predn_int //.
    move/hmin; case: {le_m_fr hmin} m gt0_m => //=.
    by move=> m _; rewrite ltnn.
  have h1: forall m n, (N <= m)%N -> (N <= n)%N ->
    0 < f (g (m + n)%N) - f (g m - 1) - f (g n - 1).
  - move=> m n le_Nm le_Nn; rewrite -[X in X<_](subrr (m%:Z + n%:Z)).
    rewrite opprD !addrA ltr_sub //; last by case/andP: (hrg _ le_Nn).
    rewrite ler_lt_sub //; last by case/andP: (hrg _ le_Nm).
    suff: (N <= m + n)%N by move/hrg => /andP[].
    by apply: (leq_trans le_Nm); rewrite leq_addr.
  have h2: forall m n, (N <= m)%N -> (N <= n)%N ->
    f (g (m + n)%N - 1) - f (g m) - f (g n) < 0.
  - move=> m n le_Nm le_Nn; rewrite -[X in _<X](subrr (m%:Z + n%:Z)).
    rewrite opprD !addrA ltr_le_sub //; last by case/andP: (hrg _ le_Nn).
    rewrite ltr_le_sub //; last by case/andP: (hrg _ le_Nm).
    suff: (N <= m + n)%N by move/hrg => /andP[].
    by apply: (leq_trans le_Nm); rewrite leq_addr.
  - have [C hC]: exists C : int, forall (m n : nat),
      `|f (g (n + m)%N - g n - g m)| < C.
    * have [C hC]: exists C : int, forall (m n : nat),
      (N <= m)%N -> (N <= n)%N -> `|f (g (n + m)%N - g n - g m)| < C.
      + have bd1: exists C : int, forall (m n : nat),
          (N <= m)%N -> (N <= n)%N -> f (g (n + m)%N - g n - g m) > C.
        have /eqvP[C hC] := L1 f; exists (-C) => m n le_Mm le_Mn.
        move/(_ (g (n + m)%N, (g n, g m))): hC => /=; rewrite ltr_norml.
        case/andP=> [+ _] => /ltr_trans; apply; rewrite ltr_subl_addr.
        by rewrite ltr_spaddr //; apply: h1.
      + have bd2: exists C : int, forall (m n : nat),
          (N <= m)%N -> (N <= n)%N -> f (g (n + m)%N - g n - g m) < C.
        have /eqvP[C hC] := L2 f; exists C => m n le_Mm le_Mn.
        move/(_ (g (n + m)%N, (g n, g m))): hC => /=; rewrite ltr_norml.
        case/andP=> _ /(ltr_trans _); apply; rewrite ltr_subr_addr.
        by rewrite ltr_snaddr //; apply: h2.
      case: bd1 bd2 => {h1 h2} [C1 h1] [C2 h2]; pose C := Num.max `|C1| `|C2|.
      exists C; move=> m n le_Mm le_Mn; rewrite ltr_norml.
      rewrite andbC ltr_maxr orbC ltr_normr h2 //= ltr_oppl.
      by rewrite ltr_maxr ltr_normr ltr_opp2 h1 ?Monoid.simpm.
    pose F i j : int := `|f (g (i + j)%N - g i - g j)|.
    pose C' : int := \sum_(0 <= i < N) g i; exists (`|C| + `|C'|).
    move=> m n; wlog: m n / (m <= n)%N => [wlog|le_mn].
    * case: (leqP m n) => [|/ltnW] /wlog //.
      by rewrite addnC addrAC.
    case: (ltnP m N) => [|le_Nm]; last first.
    * have le_Nn := leq_trans le_Nm le_mn.
      by rewrite ltr_paddr ?normr_ge0 // ltr_normr hC.
    rewrite eq0_g => /eqP->; rewrite subr0.
*)
Admitted.


Parameter (edxinv : eudoxus -> eudoxus).

Lemma edxfield :
     (forall x, x != 0 -> edxinv x * x = 1)
  /\ (edxinv 0 = 0).
Proof.
Admitted.

Definition eudoxus_fieldUnitMixin :=
  FieldUnitMixin edxfield.1 edxfield.2.
Canonical eudoxus_unitRing :=
  Eval hnf in UnitRingType eudoxus eudoxus_fieldUnitMixin.
Canonical eudoxus_comUnitRing :=
  Eval hnf in [comUnitRingType of eudoxus].

Local Fact eudoxus_field_axiom : GRing.Field.mixin_of eudoxus_unitRing.
Proof. exact. Qed.

Definition eudoxus_FieldIdomainMixin :=
  FieldIdomainMixin eudoxus_field_axiom.
Canonical eudoxus_iDomain :=
  Eval hnf in IdomainType eudoxus (FieldIdomainMixin eudoxus_field_axiom).
Canonical eudoxus_fieldType :=
  Eval hnf in FieldType eudoxus eudoxus_field_axiom.

End EudoxusFieldType.

(* ==================================================================== *)
Section EudoxusNum.
Let edxpos_N0    := let: And4 h _ _ _ := edxpos_order in h.
Let edxpos_total := let: And4 _ h _ _ := edxpos_order in h.
Let edxpos_add   := let: And4 _ _ h _ := edxpos_order in h.
Let edxpos_mul   := let: And4 _ _ _ h := edxpos_order in h.

Definition eudoxus_realLeMixin :=
  PosNumMixin edxpos_N0 edxpos_total edxpos_add edxpos_mul.

Canonical eudoxus_porderType :=
  Eval hnf in POrderType ring_display eudoxus eudoxus_realLeMixin.
Canonical eudoxus_latticeType :=
  Eval hnf in LatticeType eudoxus eudoxus_realLeMixin.
Canonical eudoxus_distrLatticeType :=
  Eval hnf in DistrLatticeType eudoxus eudoxus_realLeMixin.
Canonical eudoxus_orderType :=
  Eval hnf in OrderType eudoxus (le_total edxpos_N0 edxpos_total edxpos_add edxpos_mul).
Canonical rat_numDomainType :=
  Eval hnf in NumDomainType eudoxus eudoxus_realLeMixin.
Canonical eudoxus_normedZmodType :=
  Eval hnf in NormedZmodType eudoxus eudoxus eudoxus_realLeMixin.
Canonical eudoxus_numFieldType :=
  Eval hnf in [numFieldType of eudoxus].
Canonical eudoxus_realDomainType :=
  Eval hnf in [realDomainType of eudoxus].
Canonical eudoxus_realFieldType :=
  Eval hnf in [realFieldType of eudoxus].

Fact edx_ltrE (f g : eudoxus) : (f < g) = ((g - f) \in edxpos).
Proof. by []. Qed.

Fact eudoxus_archimedean :
  Num.archimedean_axiom [numDomainType of eudoxus].
Proof.
suff: forall f : eudoxus, exists ub : nat, f < ub%:R.
+ by move=> wlog f; case: ler0P.
elim/quotW=> /= f; have /is_eqzendoP[C /qzendo_sublin] /= := valP f.
case=> [A] [B] ltf; exists `|A|%N.+1; rewrite edx_ltrE /=.
rewrite edxnatrE !piE; apply/edxposfP => /=; rewrite /qzendoC => k.
have {ltf} ltf (m : int) : 0 < m -> f m < `|A| * m + B.
+ move=> gt0_m; apply/(le_lt_trans (ler_norm _)).
  apply/(lt_le_trans (ltf m)); rewrite ler_add2r.
  by rewrite gtr0_norm // ler_pmul2r // ler_norm.
exists (`|k + B| + 1); first by rewrite ltz_addr1.
rewrite ltr_subr_addl -ltr_subr_addr.
rewrite (lt_trans (ltf _ _)) ?ltz_addr1 //.
rewrite intS [1+_]addrC [in X in _ < X]mulrDr mulr1.
rewrite [`|A|*_]mulrC -addrA ler_lt_add //.
by rewrite ltr_subr_addl ltz_addr1 ler_norm.
Qed.

Canonical eudoxus_archiType :=
  Eval hnf in ArchiFieldType eudoxus eudoxus_archimedean.

End EudoxusNum.
