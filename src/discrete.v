(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun finset finmap bigop ssralg ssrnum ssrint.
Require Import tuple bigenough boolp reals.
Require (*--*) Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

Local Open Scope ring_scope.
Local Open Scope real_scope.

(* -------------------------------------------------------------------- *)
Lemma existsTP {T : choiceType} (P : T -> Prop) :
  { x : T | P x } + (forall x, ~ P x).
Proof.
case: (boolP (asbool (exists x : T, `[<P x>]))).
  move/exists_asboolP=> h; have/asboolP/asboolP := (xchooseP h).
  by move=> Ph; left; exists (xchoose h).
by move/asboolPn=> h; right=> x Px; apply/h; exists x; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Section PredSubtype.
Section Def.
Variable T : Type.
Variable E : pred T.

Record pred_sub : Type :=
  PSubSub { rsval : T; rsvalP : rsval \in E }.

Coercion rsval : pred_sub >-> T.

Canonical pred_sub_subType := Eval hnf in [subType for rsval].
End Def.

Definition pred_sub_eqMixin (T : eqType) (E : pred T) :=
  Eval hnf in [eqMixin of pred_sub E by <:].
Canonical pred_sub_eqType (T : eqType) (E : pred T) :=
  Eval hnf in EqType (@pred_sub T E) (pred_sub_eqMixin E).

Definition pred_sub_choiceMixin (T : choiceType) (E : pred T) :=
  Eval hnf in [choiceMixin of pred_sub E by <:].
Canonical pred_sub_choiceType (T : choiceType) (E : pred T) :=
  Eval hnf in ChoiceType (@pred_sub T E) (pred_sub_choiceMixin E).

Definition pred_sub_countMixin (T : countType) (E : pred T) :=
  Eval hnf in [countMixin of pred_sub E by <:].
Canonical pred_sub_countType (T : countType) (E : pred T) :=
  Eval hnf in CountType (@pred_sub T E) (pred_sub_countMixin E).
End PredSubtype.

Notation "[ 'psub' E ]" := (@pred_sub _ E)
  (format "[ 'psub'  E ]").

(* -------------------------------------------------------------------- *)
Section PIncl.
Variables (T : Type) (E F : pred T) (le : {subset E <= F}).

Definition pincl (x : [psub E]) : [psub F] :=
  PSubSub (le (valP x)).
End PIncl.

(* -------------------------------------------------------------------- *)
Section Countable.
Variable (T : Type) (E : pred T).

CoInductive countable : Type :=
  Countable
    (rpickle : [psub E] -> nat)
    (runpickle : nat -> option [psub E])
    of pcancel rpickle runpickle.

Definition rpickle (c : countable) :=
  let: Countable p _ _ := c in p.

Definition runpickle (c : countable) :=
  let: Countable _ p _ := c in p.

Lemma rpickleK c: pcancel (rpickle c) (runpickle c).
Proof. by case: c. Qed.
End Countable.

(* -------------------------------------------------------------------- *)
Section CountableTheory.
Lemma countable_countable (T : countType) (E : pred T) : countable E.
Proof. by exists pickle unpickle; apply/pickleK. Qed.

Section CanCountable.
Variables (T : Type) (U : countType) (E : pred T).
Variables (f : [psub E] -> U) (g : U -> [psub E]).

Lemma can_countable : cancel f g -> countable E.
Proof.
pose p := pickle \o f; pose u n := omap g (unpickle n).
move=> can_fg; apply (@Countable _ E p u) => x.
by rewrite {}/u {}/p /= pickleK /= can_fg.
Qed.
End CanCountable.

Section CountType.
Variables (T : eqType) (E : pred T) (c : countable E).

Definition countable_countMixin  := CountMixin (rpickleK c).
Definition countable_choiceMixin := CountChoiceMixin countable_countMixin.

Definition countable_choiceType :=
  ChoiceType [psub E] countable_choiceMixin.

Definition countable_countType :=
  CountType countable_choiceType countable_countMixin.
End CountType.
End CountableTheory.

Notation "[ 'countable' 'of' c ]" := (countable_countType c)
  (format "[ 'countable'  'of'  c ]").

(* -------------------------------------------------------------------- *)
Section Finite.
Variables (T : eqType).

CoInductive finite (E : pred T) : Type :=
| Finite s of uniq s & {subset E <= s}.
End Finite.

(* -------------------------------------------------------------------- *)
Section FiniteTheory.
Context {T : choiceType}.

Lemma finiteP (E : pred T) : (exists s : seq T, {subset E <= s}) -> finite E.
Proof.
move/asboolP/exists_asboolP=> h; have/asboolP := (xchooseP h).
move=> le_Eh; exists (undup (xchoose h)); rewrite ?undup_uniq //.
by move=> x /le_Eh; rewrite mem_undup.
Qed.

Lemma finiteNP (E : pred T): (forall s : seq T, ~ {subset E <= s}) ->
  (forall n, exists s : seq T, [/\ size s = n, uniq s & {subset s <= E}]).
Proof.
move=> finN n; have h: forall s : seq T, exists2 x, x \notin s & x \in E.
  move=> s; have /asboolPn/existsp_asboolPn := finN (filter (mem E) s).
  case=> x; rewrite mem_filter => /asboolPn/imply_asboolPn.
  by case=> xE /negP; rewrite topredE xE /= => Nxs; exists x.
elim: n => [|n [s] [<- uq_s sE]]; first by exists [::].
case: (h s)=> x sxN xE; exists (x :: s) => /=; rewrite sxN; split=> //.
by move=> y; rewrite in_cons => /orP[/eqP->//|/sE].
Qed.
End FiniteTheory.

(* -------------------------------------------------------------------- *)
Section FiniteCountable.
Variables (T : eqType) (E : pred T).

Lemma finite_countable : finite E -> countable E.
Proof.
case=> s uqs Es; pose t := pmap (fun x => (insub x : option [psub E])) s.
pose f x := index x t; pose g i := nth None [seq Some x | x <- t] i.
apply (@Countable _ E f g) => x; rewrite {}/f {}/g /=.
have x_in_t: x \in t; first case: x => x h.
  by rewrite {}/t mem_pmap_sub /= Es.
by rewrite (nth_map x) ?index_mem ?nth_index.
Qed.
End FiniteCountable.

(* -------------------------------------------------------------------- *)
Section CountSub.
Variables (T : eqType) (E F : pred T).

Lemma countable_sub: {subset E <= F} -> countable F -> countable E.
Proof.
move=> le_EF [f g fgK]; pose f' (x : [psub E]) := f (pincl le_EF x).
pose g' x := obind (insub (sT := [subType of [psub E]])) (omap val (g x)).
by exists f' g' => x; rewrite /f' /g' fgK /= valK.
Qed.
End CountSub.

(* -------------------------------------------------------------------- *)
Section CountableUnion.
Variables (T : eqType) (E : nat -> pred T).

Hypothesis cE : forall i, countable (E i).

Lemma cunion_countable : countable [pred x | `[exists i, x \in E i]].
Proof.
pose S := { i : nat & [countable of cE i] }; set F := [pred x | _].
have H: forall (x : [psub F]), exists i : nat, val x \in E i.
  by case=> x /= /existsbP[i] Eix; exists i.
have G: forall (x : S), val (tagged x) \in F.
  by case=> i [x /= Eix]; apply/existsbP; exists i.
pose f (x : [psub F]) : S := Tagged (fun i => [psub E i])
  (PSubSub (xchooseP (H x))).
pose g (x : S) := PSubSub (G x).
by have /can_countable: cancel f g by case=> x hx; apply/val_inj.
Qed.
End CountableUnion.

(* -------------------------------------------------------------------- *)
Section Summable.
Variables (T : choiceType) (R : realType) (f : T -> R).

Definition summable := exists (M : R), forall (J : {fset T}),
  \sum_(x : J) `|f (val x)| <= M.

Definition sum : R :=
  (* We need some ticked `image` operator *)
  let S := [pred x | `[exists J : {fset T}, x == \sum_(x : J) `|f (val x)|]] in
  if `[<summable>] then sup S else 0.

Lemma summableP : summable ->
  { M | 0 <= M & forall (J : {fset T}), \sum_(x : J) `|f (val x)| <= M }.
Proof.
move/asboolP/exists_asboolP=> h; have := (xchooseP h).
move: (xchoose _)=> {h} M /asboolP h; exists M => //.
by have := h fset0; rewrite big_pred0 // => -[x]; rewrite in_fset0.
Qed.
End Summable.

(* -------------------------------------------------------------------- *)
Section SummableCountable.
Variable (T : choiceType) (R : realType) (f : T -> R).

Goal summable f -> countable [pred x | f x != 0].
Proof.
case/summableP=> M ge0_M bM; pose E (p : nat) := [pred x | `|f x| > 1 / p.+1%:~R].
set F := [pred x | _]; have le: {subset F <= [pred x | `[exists p, x \in E p]]}.
  move=> x; rewrite !inE => nz_fx; apply/existsbP.
  case: (ltrP 1 `|f x|) => [lt_1Afx|]; first by exists 0%N; rewrite inE divr1.
  pose j := `|ifloor (1 / `|f x|)|%N; exists j; rewrite inE.
  rewrite ltr_pdivr_mulr ?ltr0z // -ltr_pdivr_mull ?normr_gt0 //.
  rewrite mulr1 /j div1r -addn1 /= PoszD intrD mulr1z.
  rewrite gez0_abs ?ifloor_ge0 ?invr_ge0 ?normr_ge0 //.
  by rewrite -floorE; apply floorS_gtr.
apply/(countable_sub le)/cunion_countable=> i /=.
case: (existsTP (fun s : seq T => {subset E i <= s}))=> /= [[s le_Eis]|].
  by apply/finite_countable/finiteP; exists s => x /le_Eis.
move/finiteNP; pose j := `|ifloor (M / i.+1%:R)|.+1.
pose K := (`|ifloor M|.+1 * i.+1)%N; move/(_ K)/existsp_asboolP/existsbP.
move=> h; have /asboolP[] := xchooseP h.
set s := xchoose h=> eq_si uq_s le_sEi; pose J := seq_fset s.
suff: \sum_(x : J) `|f (val x)| > M by rewrite ltrNge bM.
apply/(@ltr_le_trans _ (\sum_(x : J) 1 / i.+1%:~R)); last first.
  apply/ler_sum=> /= m _; apply/ltrW; suff: (val m \in E i) by apply.
  by apply/le_sEi/in_seq_fset/fsvalP.
rewrite sumr_const cardfsE undup_id // eq_si -mulr_natr -pmulrn.
rewrite mul1r natrM mulrCA mulVf ?mulr1 ?pnatr_eq0 //.
have /andP[_] := mem_rg1_floor M; rewrite floorE -addn1.
by rewrite natrD /= mulr1n pmulrn -{1}[ifloor _]gez0_abs // ifloor_ge0.
Qed.
End SummableCountable.

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (T : choiceType) (R : realType).

Structure distr := Distr {
  mu : T -> R;
  _  : forall x, 0 <= mu x;
  _  : summable mu;
  _  : sum mu <= 1
}.

Definition distr_of of phant T & phant R := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant T) (Phant R))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.
