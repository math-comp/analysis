(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import finmap boolp reals discrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Section Summable.
Variables (T : choiceType) (R : realType) (f : T -> R).

Definition summable := exists (M : R), forall (J : {fset T}),
  \sum_(x : J) `|f (val x)| <= M.

Lemma summableP : summable ->
  { M | 0 <= M & forall (J : {fset T}), \sum_(x : J) `|f (val x)| <= M }.
Proof.
move/asboolP/exists_asboolP=> h; have := (xchooseP h).
move: (xchoose _)=> {h} M /asboolP h; exists M => //.
by have := h fset0; rewrite big_pred0 // => -[x]; rewrite in_fset0.
Qed.
End Summable.

(* -------------------------------------------------------------------- *)
Section Sum.
Variables (T : choiceType) (R : realType).

Implicit Types f : T -> R.

Definition fpos f := fun x => `|Num.max 0 (f x)|.
Definition fneg f := fun x => `|Num.min 0 (f x)|.

Definition psum f : R :=
  (* We need some ticked `image` operator *)
  let S := [pred x | `[exists J : {fset T}, x == \sum_(x : J) `|f (val x)|]] in
  if `[<summable f>] then sup S else 0.

Definition sum f : R := psum (fpos f) - psum (fneg f).
End Sum.

(* -------------------------------------------------------------------- *)
Section SummableCountable.
Variable (T : choiceType) (R : realType) (f : T -> R).

Lemma summable_countn0 : summable f -> countable [pred x | f x != 0].
Proof.
case/summableP=> M ge0_M bM; pose E (p : nat) := [pred x | `|f x| > 1 / p.+1%:~R].
set F := [pred x | _]; have le: {subset F <= [pred x | `[exists p, x \in E p]]}.
  move=> x; rewrite !inE => nz_fx; apply/existsbP.
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
