(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete realseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

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

(* -------------------------------------------------------------------- *)
Section PosCnv.
Context {R : realType}.

Lemma ncvg_mono (u : nat -> R) :
    (* {mono u : x y / (x <= y)%N >-> u x <= u y *)
    (forall x y, (x <= y)%N -> u x <= u y)
  -> exists2 l, (\-inf < l)%E & ncvg u l.
Proof.
move=> mono_u; pose E := [pred x | `[exists n, x == u n]].
have nzE: nonempty E by exists (u 0%N); apply/imsetbP; exists 0%N.
case/boolP: `[< has_sup E >] => /asboolP; last first.
  move/has_supPn=> -/(_ nzE) h; exists \+inf => //; elim/nbh_pinfW => M /=.
  case/(_ M): h=> x /imsetbP[K -> lt_MuK]; exists K=> n le_Kn; rewrite inE.
  by apply/(ltr_le_trans lt_MuK)/mono_u.
move=> supE; exists (sup E)%:E => //; elim/nbh_finW=>e /= gt0_e.
case: (sup_adherent supE gt0_e)=> x /imsetbP[K ->] lt_uK.
exists K=> n le_Kn; rewrite inE distrC ger0_norm ?subr_ge0.
  by apply/sup_upper_bound/imsetbP=> //; exists n.
rewrite ltr_subl_addr addrC -ltr_subl_addr.
by rewrite (ltr_le_trans lt_uK) //; apply/mono_u.
Qed.

Lemma ncvg_mono_bnd (u : nat -> R) :
    (* {mono u : x y / (x <= y)%N >-> u x <= u y *)
    (forall x y, (x <= y)%N -> u x <= u y)
  -> nbounded u -> exists l, ncvg u l%:E.
Proof.
case/ncvg_mono=> -[x||] // _ cu bdu; first by exists x.
case/asboolP/nboundedP: bdu=> M gt0_M bdu.
case/(_ (NPInf M)): cu => K /= /(_ K (leqnn _)).
rewrite inE /= => /ltrW /ler_trans /(_ (ler_norm _)).
by move/ler_lt_trans/(_ (bdu _)); rewrite ltrr.
Qed.
End PosCnv.

(* -------------------------------------------------------------------- *)
Section SumTh.
Context {R : realType} (T : choiceType).

Implicit Type S : T -> R.

Lemma summable_sup (S : T -> R) : summable S -> has_sup
  [pred x | `[exists J : {fset T}, x == \sum_(j : J) `|S (val j)|]].
Proof.
case/summableP=> M _ hbd; apply/has_supP; split.
  by exists 0; apply/existsbP; exists fset0; rewrite big_fset0.
by exists M; apply/ubP=> y /existsbP[J /eqP->].
Qed.

Lemma eq_summable (S1 S2 : T -> R) :
  (S1 =1 S2) -> summable S1 -> summable S2.
Proof.
move=> eq_12 [M h]; exists M => J; rewrite (ler_trans _ (h J)) //.
rewrite ler_eqVlt; apply/orP; left; apply/eqP/eq_bigr.
by move=> /= K _; rewrite eq_12.
Qed.

Lemma eq_summableb (S1 S2 : T -> R) :
  (S1 =1 S2) -> `[< summable S2 >] = `[< summable S1 >].
Proof. by move=> eq_12; apply/asboolP/asboolP; apply/eq_summable. Qed.

Lemma eq_ppsum (F1 F2 : {fset T} -> R) : F1 =1 F2 ->
  sup [pred x | `[exists J, x == F1 J]] = sup [pred x | `[exists J, x == F2 J]].
Proof.
move=> eq_12; apply/eq_sup=> x; rewrite !inE.
by apply/existsbP/existsbP=> -[J /eqP->]; exists J; apply/eqP.
Qed.

Lemma eq_psum (F1 F2 : T -> R) : F1 =1 F2 -> psum F1 = psum F2.
Proof.
move=> eq_12; rewrite /psum (eq_summableb eq_12).
case: `[< summable F1 >] => //; apply/eq_sup.
move=> x; apply/imsetbP/imsetbP=> -[J ->]; exists J;
  by apply/eq_bigr=> /= K _; rewrite eq_12.
Qed.

Lemma le_summable (F1 F2 : T -> R) :
  (forall x, 0 <= F1 x <= F2 x) -> summable F2 -> summable F1.
Proof.
move=> le_F [M leM]; exists M => J; apply/(ler_trans _ (leM J)).
apply/ler_sum => /= j _; case/andP: (le_F (val j)) => h1 h2.
by rewrite !ger0_norm // (ler_trans h1 h2).
Qed.

Lemma le_psum (F1 F2 : T -> R) :
  (forall x, 0 <= F1 x <= F2 x) -> summable F2 -> psum F1 <= psum F2.
Proof.
move=> le_F smF2; have smF1: summable F1 by apply/(le_summable le_F).
rewrite /psum (asboolT smF1) (asboolT smF2); apply/le_sup; first last.
+ by apply/summable_sup.
+ by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
move=> x /imsetbP[J ->]; apply/downP; exists (\sum_(j : J) `|F2 (val j)|).
  by apply/imsetbP; exists J.
apply/ler_sum=> /= j _; case/andP: (le_F (val j)) => h1 h2.
by rewrite !ger0_norm // (ler_trans h1 h2).
Qed.

Lemma psum_out S : ~ summable S -> psum S = 0.
Proof. by move/asboolPn/negbTE=> smN; rewrite /psum smN. Qed.

Lemma psumE S : (forall x, 0 <= S x) -> summable S -> psum S =
  sup [pred x | `[exists J : {fset T}, x == \sum_(j : J) S (val j)]].
Proof.
move=> gt0_S smS; rewrite /psum (asboolT smS); apply/eq_ppsum=> /=.
by move=> J; apply/eq_bigr=> j _; rewrite ger0_norm.
Qed.

Lemma psum_absE S : summable S -> psum S =
  sup [pred x | `[exists J : {fset T}, x == \sum_(j : J) `|S (val j)|]].
Proof. by move=> smS; rewrite /psum (asboolT smS). Qed.

Lemma summable_seqP S :
  summable S <-> (exists2 M, 0 <= M &
    forall s : seq T, uniq s -> \sum_(x <- s) `|S x| <= M).
Proof.
split=> [/summableP|] [M gt0_M h]; exists M => //.
  by move=> s uq_s; have := h (seq_fset s); rewrite (big_seq_fset \`|S|).
by case=> J cJ; rewrite (big_fset_seq \`|_|) /=; apply/h/canonical_uniq.
Qed.

Lemma gerfin_psum S (J : {fset T}) :
  summable S -> \sum_(j : J) `|S (val j)| <= psum S.
Proof.
move=> smS; rewrite /psum (asboolT smS); apply/sup_upper_bound.
  by apply/summable_sup. by apply/imsetbP; exists J.
Qed.

Lemma gerfinseq_psum S (r : seq T) :
  uniq r -> summable S -> \sum_(j <- r) `|S j| <= psum S.
Proof.
move=> uq_r /gerfin_psum -/(_ (seq_fset r));
  by rewrite (big_seq_fset \`|S|).
Qed.
End SumTh.

(* -------------------------------------------------------------------- *)
Lemma max_sup {R : realType} x (E : pred R) :
  x \in [predI E & ub E] -> sup E = x.
Proof.
case/andP=> /= xE xubE; have nzE: nonempty E by exists x.
apply/eqP; rewrite eqr_le sup_le_ub ?sup_upper_bound //.
by apply/has_supP; split; exists x.
Qed.

(* -------------------------------------------------------------------- *)
Section FinSumTh.
Context {R : realType} (I : finType).

Lemma summable_fin (f : I -> R) : summable f.
Proof.
exists (\sum_(i : [fset i | i : I]) `|f (val i)|).
move=> J; apply: (big_fset_subset (F := \`|_|)).
  by move=> x; rewrite normr_ge0.
by move=> i _; apply/imfsetP; exists i.
Qed.

Lemma psum_fin (f : I -> R) : psum f = \sum_i `|f i|.
Proof.                          (* FIXME *)
pose S := \sum_(i : [fset i | i : I]) `|f (val i)|.
rewrite /psum (asboolT (summable_fin f)) (@max_sup _ S).
  rewrite inE /=; apply/andP; split; first apply/imsetbP.
    by exists [fset i | i : I]%fset.
  apply/ubP=> y /imsetbP[J ->]; apply/(big_fset_subset (F := \`|_|)).
    by move=> i; rewrite normr_ge0.
  by move=> j jJ; apply/in_imfset.
rewrite /S -(big_map val xpredT \`|f|); apply/eq_big_perm.
rewrite /index_enum -!enumT; apply/(perm_eq_trans _ enum_fsetT).
apply/uniq_perm_eq; rewrite ?map_inj_uniq ?enum_uniq //=.
  by apply/val_inj. by rewrite -enumT enum_uniq.
move=> i /=; rewrite mem_enum in_imfset //; apply/mapP.
have h: i \in [fset j | j : I] by rewrite in_imfset.
by exists (FSetSub h) => //; rewrite mem_enum.
Qed.
End FinSumTh.

(* -------------------------------------------------------------------- *)
Section PSumGe.
Context {R : realType} (T : choiceType).

Variable (S : T -> R).

Lemma ger_big_psum r : uniq r -> summable S ->
  \sum_(x <- r) `|S x| <= psum S.
Proof.
move=> uq_r smS; rewrite /psum (asboolT smS) sup_upper_bound //.
  by apply/summable_sup. apply/imsetbP; exists (seq_fset r).
by rewrite (big_seq_fset (fun i => `|S i|)).
Qed.

Lemma ger1_psum x : summable S -> `|S x| <= psum S.
Proof.
move=> smS; have h := @ger_big_psum [:: x] _ smS.
by rewrite (ler_trans _ (h _)) ?big_seq1.
Qed.

Lemma ge0_psum : 0 <= psum S.
Proof.                          (* FIXME: asbool_spec *)
case/boolP: `[< summable S >] => [|/asboolPn/psum_out ->//].
move/asboolP=> smS; have h := @ger_big_psum [::] _ smS.
by rewrite (ler_trans _ (h _)) ?big_nil.
Qed.
End PSumGe.

(* -------------------------------------------------------------------- *)
Section PSumNatGe.
Context {R : realType}.

Variable (S : nat -> R) (smS : summable S).

Lemma ger_big_ord_psum n : \sum_(i < n) `|S i| <= psum S.
Proof.
rewrite -(big_mkord predT (fun i => `|S i|)) /=.
by apply/ger_big_psum => //; rewrite iota_uniq.
Qed.
End PSumNatGe.

(* -------------------------------------------------------------------- *)
Section PSumCnv.
Context {R : realType}.

Variable (S : nat -> R).

Hypothesis ge0_S : (forall n, 0 <= S n).
Hypothesis smS   : summable S.

Lemma ptsum_homo x y : (x <= y)%N -> (\sum_(i < x) S i <= \sum_(i < y) S i).
Proof.
move=> le_xy; rewrite -!(big_mkord predT) -(subnKC le_xy) /=.
by rewrite /index_iota !subn0 iota_add big_cat /= ler_addl sumr_ge0.
Qed.

Lemma psummable_ptbounded : nbounded (fun n => \sum_(i < n) S i).
Proof.
apply/asboolP/nboundedP; exists (psum S + 1)%R.
  rewrite ltr_spaddr ?ltr01 1?(ler_trans (normr_ge0 (S 0%N))) //.
  by apply/ger1_psum.
move=> n; rewrite ltr_spaddr ?ltr01 // ger0_norm ?sumr_ge0 //.
apply/(ler_trans _ (ger_big_ord_psum _ n)) => //.
by apply/ler_sum=> /= i _; apply/ler_norm.
Qed.

Lemma ncvg_sum : ncvg (fun n => \sum_(i < n) S i) (psum S)%:E.
Proof.
set u := (fun n => _); apply: contrapLR smS => ncv _.
case: (ncvg_mono_bnd (u := u)) => //.
  by apply/ptsum_homo. by apply/psummable_ptbounded.
move=> x cvux; suff xE: x = (psum S) by rewrite xE in cvux.
apply/eqP; case: (x =P _) => // /eqP /ltr_total /orP[]; last first.
+ rewrite -lte_fin => /ncvg_gt /(_ cvux) [K /(_ _ (leqnn _))] /=.
  rewrite ltrNge (ler_trans _ (ger_big_ord_psum _ K)) //.
  by apply/ler_sum=> /= i _; apply/ler_norm.
move=> lt_xS; pose e := psum S - x.
  have ge0_e: 0 < e by rewrite subr_gt0.
case: (sup_adherent (summable_sup smS) ge0_e) => y.
case/imsetbP=> /= J ->; rewrite /e /psum (asboolT smS).
rewrite opprB addrCA subrr addr0 => lt_xSJ.
pose k := \max_(j : J) (val j); have lt_x_uSk: x < u k.+1.
  apply/(ltr_le_trans lt_xSJ); rewrite /u big_ord_mkfset.
  rewrite (eq_bigr (S \o val)) => /= [j _|]; first by rewrite ger0_norm.
  apply/big_fset_subset=> // j jJ; rewrite in_fsetT //.
  by rewrite (mem_iota _ k.+1) /= add0n ltnS (leq_bigmax (FSetSub jJ)).
have /= := ncvg_homo_le ptsum_homo cvux k.+1; rewrite -/(u _).
by move/ler_lt_trans/(_ lt_x_uSk); rewrite ltrr.
Qed.

Lemma sum_ncvg l :
  ncvg (fun n => \sum_(i < n) S i) l%:E -> summable S.
Proof using ge0_S. Abort.
End PSumCnv.

(* -------------------------------------------------------------------- *)
Section SummableAlg.
Context {R : realType} (T : choiceType).

Lemma summable0 : summable (fun _ : T => 0 : R).
Proof. by exists 0 => J; rewrite big1 ?normr0. Qed.

Lemma summableD (S1 S2 : T -> R) :
  summable S1 -> summable S2 -> summable (S1 \+ S2).
Proof.
case=> [M1 h1] [M2 h2]; exists (M1 + M2)%R => J /=.
pose M := \sum_(x : J) (`|S1 (val x)| + `|S2 (val x)|).
rewrite (@ler_trans _ M) // ?ler_sum // => [K _|].
  by rewrite ler_norm_add.
by rewrite /M big_split ler_add ?(h1, h2).
Qed.

Lemma summableN (S : T -> R) : summable S -> summable (\- S).
Proof.
case=> [M h]; exists M => J; rewrite (ler_trans _ (h J)) //.
rewrite ler_eqVlt; apply/orP; left; apply/eqP/eq_bigr.
by move=> /= K _; rewrite normrN.
Qed.

Lemma summablebN (S : T -> R) :
  `[< summable (\- S)>] = `[< summable S >].
Proof.
apply/asboolP/asboolP => /summableN //.
by apply/eq_summable => x /=; rewrite opprK.
Qed.

Lemma summablebDl (S1 S2 : T -> R) : summable S1 ->
  `[< summable (S1 \+ S2) >] = `[< summable S2 >].
Proof.
move=> sm1; apply/asboolP/asboolP; last by apply/(summableD sm1).
move=> sm12; apply/(@eq_summable _ _ ((S1 \+ S2) \- S1)).
  by move=> x /=; rewrite addrC addKr.
by apply/summableD/summableN.
Qed.

Lemma summablebDr (S1 S2 : T -> R) : summable S2 ->
  `[< summable (S1 \+ S2) >] = `[< summable S1 >].
Proof.
move=> sm1; rewrite (@eq_summableb _ _ (S2 \+ S1)) ?summablebDl //.
by move=> x /=; rewrite addrC.
Qed.

Lemma summableMl (S1 S2 : T -> R) :
  (exists2 M, 0 <= M & forall x, `|S1 x| <= M) -> summable S2 -> summable (S1 \* S2).
Proof.
case=> [M1 ge0_M1 h1] /summableP[M2 ge0_M2 h2].
exists (M1 * M2) => J; pose E := M1 * \sum_(j : J) `|S2 (val j)|.
rewrite (@ler_trans _ E) // {}/E 1?ler_wpmul2l //.
by rewrite mulr_sumr ler_sum => //= j _; rewrite normrM ler_wpmul2r.
Qed.

Lemma summableM (S1 S2 : T -> R) :
  summable S1 -> summable S2 -> summable (S1 \* S2).
Proof.                          (* FIXME: summableMl *)
move=> /summableP[M1 ge0_M1 h1] /summableP[M2 ge0_M2 h2].
exists (M1 * M2) => J; pose E := (\sum_(j : J) `|S1 (val j)|) * M2.
rewrite (@ler_trans _ E) //; last first.
  by rewrite /E ler_wpmul2r ?h1.
rewrite /E mulr_suml ler_sum => //= j _.
rewrite normrM ler_wpmul2l //; move/(_ J): h2.
rewrite (bigD1 j) //= => /(ler_trans _).
by apply; rewrite ler_addl sumr_ge0.
Qed.

Lemma summableZ (S : T -> R) c : summable S -> summable (c \*o S).
Proof.
case=> [M h]; exists (`|c| * M) => J; move/(_ J): h => /=.
move/(ler_wpmul2l (normr_ge0 c)); rewrite mulr_sumr.
move/(ler_trans _); apply; rewrite ler_eqVlt; apply/orP.
by left; apply/eqP/eq_bigr=> j _; rewrite normrM.
Qed.
End SummableAlg.

(* -------------------------------------------------------------------- *)
Section StdSum.
Context {R : realType} (T : choiceType).

Implicit Type S : T -> R.

Lemma psum0 : psum (fun _ : T => 0) = 0 :> R.
Proof.
rewrite /psum asboolT; first by apply/summable0.
set S := [pred x | _]; suff: S =1 (pred1 0).
  by move/eq_sup => ->; rewrite sup1.
move=> x; rewrite {}/S inE; apply/idP/idP => /=.
  by case/existsbP=> J /eqP-> /=; rewrite big1 // normr0.
by move=> /eqP->; apply/existsbP; exists fset0; rewrite big_fset0.
Qed.

Lemma psumN (S : T -> R) : psum (\- S) = psum S.
Proof.
case/boolP: `[< summable S >] => h; last first.
  by rewrite !psum_out ?oppr0 //; apply/asboolPn; rewrite ?summablebN.
rewrite /psum summablebN h; apply/eq_ppsum=> J /=.
by apply/eq_bigr=> j _; rewrite normrN.
Qed.

Lemma psumD S1 S2 :
    (forall x, 0 <= S1 x) -> (forall x, 0 <= S2 x)
  -> summable S1 -> summable S2
  -> psum (S1 \+ S2) = (psum S1 + psum S2)%R.
Proof.
(* Should use <-> with convergence *)
move=> ge0_S1 ge0_S2 sm1 sm2; have smD := summableD sm1 sm2.
rewrite !psumE //=; first by move=> x; rewrite addr_ge0.
Abort.
End StdSum.
