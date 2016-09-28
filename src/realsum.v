(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete realseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).
Local Notation simpm := Monoid.simpm.

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
Context {R : realType} {T : choiceType}.

Implicit Types f g : T -> R.

Definition fpos f := fun x => `|Num.max 0 (f x)|.
Definition fneg f := fun x => `|Num.min 0 (f x)|.

Lemma eq_fpos f g : f =1 g -> fpos f =1 fpos g.
Proof. by move=> eq_fg x; rewrite /fpos eq_fg. Qed.

Lemma eq_fneg f g : f =1 g -> fneg f =1 fneg g.
Proof. by move=> eq_fg x; rewrite /fneg eq_fg. Qed.

Lemma fpos0 x : fpos (fun _ : T => 0) x = 0 :> R.
Proof. by rewrite /fpos maxrr normr0. Qed.

Lemma fneg0 x : fneg (fun _ : T => 0) x = 0 :> R.
Proof. by rewrite /fneg minrr normr0. Qed.

Lemma fnegN f : fneg (\- f) =1 fpos f.
Proof. by move=> x; rewrite /fpos /fneg -{1}oppr0 -oppr_max normrN. Qed.

Lemma fposN f : fpos (\- f) =1 fneg f.
Proof. by move=> x; rewrite /fpos /fneg -{1}oppr0 -oppr_min normrN. Qed.

Lemma fposZ f c : 0 <= c -> fpos (c \*o f) =1 c \*o fpos f.
Proof.
move=> ge0_c x; rewrite /fpos /= -{1}(mulr0 c).
by rewrite -maxr_pmulr // normrM ger0_norm.
Qed.

Lemma fnegZ f c : 0 <= c -> fneg (c \*o f) =1 c \*o fneg f.
Proof.
move=> ge0_c x; rewrite /= -!fposN; have /=<- := (fposZ (\- f) ge0_c x).
by apply/eq_fpos=> y /=; rewrite mulrN.
Qed.

Lemma fpos_natrM f (n : T -> nat) x :
  fpos (fun x => (n x)%:R * f x) x = (n x)%:R * fpos f x.
Proof.
rewrite /fpos -[in RHS]normr_nat -normrM.
by rewrite maxr_pmulr ?ler0n // mulr0.
Qed.

Lemma fneg_natrM f (n : T -> nat) x :
  fneg (fun x => (n x)%:R * f x) x = (n x)%:R * fneg f x.
Proof.
rewrite -[in RHS]fposN -fpos_natrM -fposN.
by apply/eq_fpos=> y; rewrite mulrN.
Qed.

Lemma fneg_ge0 f x : (forall x, 0 <= f x) -> fneg f x = 0.
Proof. by move=> ?; rewrite /fneg minr_l ?normr0. Qed.

Lemma fpos_ge0 f x : (forall x, 0 <= f x ) -> fpos f x = f x.
Proof. by move=> ?; rewrite /fpos maxr_r ?ger0_norm. Qed.

Lemma ge0_fpos f x : 0 <= fpos f x.
Proof. by apply/normr_ge0. Qed.

Lemma ge0_fneg f x : 0 <= fneg f x.
Proof. by apply/normr_ge0. Qed.

Lemma le_fpos_norm f x : fpos f x <= `|f x|.
Proof.
rewrite /fpos ger0_norm ?(ler_maxr, lerr) //.
by rewrite ler_maxl normr_ge0 ler_norm.
Qed.

Lemma le_fpos f1 f2 : f1 <=1 f2 -> fpos f1 <=1 fpos f2.
Proof.
move=> le_f x; rewrite /fpos !ger0_norm ?ler_maxr ?lerr //.
by rewrite /Num.max; case: ifP => [|->/=]; first rewrite lerr.
Qed.

Lemma fposBfneg f x : fpos f x - fneg f x = f x.
Proof.
rewrite /fpos /fneg maxrC /Num.max /Num.min.
case: ifPn; rewrite normr0 (subr0, sub0r).
  by move/ger0_norm.
by rewrite -ltrNge => /ltr0_norm ->; rewrite opprK.
Qed.

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

Lemma psum_sup S : psum S =
  sup [pred x | `[exists J : {fset T}, x == \sum_(x : J) `|S (val x)|]].
Proof.
rewrite /psum; case: ifPn => // /asboolPn h.
rewrite sup_out //; set X := [pred r | _] => hs.
apply: h; exists (sup X) => J; apply/sup_upper_bound => //.
by apply/imsetbP; exists J.
Qed.

Lemma psum_sup_seq S : psum S =
  sup [pred x | `[<exists2 J : seq T,
    uniq J & x == \sum_(x <- J) `|S x|>]].
Proof.
rewrite psum_sup; apply/eq_sup => x; rewrite !inE; apply/imsetbP/idP.
  case=> J ->; apply/asboolP; exists (fset_keys J).
    by case: J => /= J /canonical_uniq.
  by rewrite (big_fset_seq \`|_|) /=.
case/asboolP=> J uqJ /eqP->; exists (seq_fset J).
by rewrite (big_seq_fset \`|_|).
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

Lemma eq_sum (F1 F2 : T -> R) : F1 =1 F2 -> sum F1 = sum F2.
Proof.
move=> eq_fg; rewrite /sum; congr (_ - _); apply/eq_psum.
  by apply/eq_fpos. by apply/eq_fneg.
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

Lemma psum_le S z :
  (forall J, uniq J -> \sum_(j <- J) `|S j| <= z) -> psum S <= z.
Proof.
move=> le_z; have: summable S; first (apply/summable_seqP; exists z).
+ by apply/(ler_trans _ (le_z [::] _)) => //; rewrite big_nil.
+ by move=> J uqJ; apply/le_z.
move/summable_sup=> [neS hsS]; rewrite psum_sup.
apply/sup_le_ub => //; apply/ubP=> r /imsetbP [J ->].
by rewrite (big_fset_seq \`|_|) le_z /=; case: J => J /= /canonical_uniq.
Qed.

Lemma lt_psum (F : T -> R) l :
  summable F -> l < psum F ->
    exists J : {fset T}, l < \sum_(j : J) `|F (val j)|.
Proof.
move=> smF; rewrite /psum (asboolT smF) => /lt_sup_imfset.
by case=> /= [|J lt_lJ _]; [apply/summable_sup | exists J].
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
Section PSumAsLim.
Context {R : realType} {T : choiceType}.

Variable (S : T -> R) (P : nat -> {fset T}).

Hypothesis ge0_S   : (forall x, 0 <= S x).
Hypothesis smS     : summable S.
Hypothesis homo_P  : forall n m, (n <= m)%N -> (P n `<=` P m).
Hypothesis cover_P : forall x, S x != 0 -> exists n, x \in P n.

Lemma psum_as_lim : psum S = nlim (fun n => \sum_(j : P n) (S (val j))).
Proof.
set v := fun n => _; have hm_v m n: (m <= n)%N -> v m <= v n.
  by move=> le_mn; apply/big_fset_subset/fsubsetP/homo_P.
have bd_v n : v n <= psum S.
  apply/(ler_trans _ (gerfin_psum _ smS))/ler_sum.
  by move=> J _; apply/ler_norm.
case: (ncvg_mono_bnd hm_v) => [|l cv].
  apply/asboolP/nboundedP; exists (psum S + 1) => //.
    by apply/(ler_lt_trans (ge0_psum S)); rewrite ltr_addl ltr01.
  move=> n; rewrite ger0_norm ?sumr_ge0 //.
  by rewrite (ler_lt_trans (bd_v n)) // ltr_addl ltr01.
have le_lS: l <= psum S by rewrite -lee_fin (ncvg_leC _ cv).
rewrite (nlimE cv) /= (rwP eqP) eqr_le le_lS andbT.
rewrite lerNgt; apply/negP=> {le_lS} /(lt_psum smS)[J].
rewrite (big_fset_seq \`|_|) /=; case: J => /= J.
move/canonical_uniq=> uqJ lt_jS; pose K := [seq x <- J | S x != 0].
have [n]: exists n, {subset K <= P n}; first rewrite {}/K.
  elim: {uqJ lt_jS} J => /= [|x J [n ih]]; first by exists 0%N.
  case: (S x =P 0) => /=; first by move=> _; exists n.
  move/eqP/cover_P=> [k Pk_x]; exists (maxn n k)=> y.
  rewrite inE => /orP[/eqP->|/=].
    by apply/fsubsetP/homo_P/leq_maxr: x Pk_x.
  by move/ih; apply/fsubsetP/homo_P/leq_maxl: y.
move=> le_K_Pn; have: l < v n; first apply/(ltr_le_trans lt_jS).
  rewrite (eq_bigr S) => [x _|]; first by rewrite ger0_norm.
  rewrite /v (bigID (fun x => S x == 0)) /= big1 => [x /eqP|] //.
  rewrite add0r -big_filter -/K -big_seq_fset ?filter_uniq //=.
  by apply/big_fset_subset => // x /in_seq_fset /le_K_Pn.
by apply/negP; rewrite -lerNgt -lee_fin ncvg_homo_le.
Qed.
End PSumAsLim.

(* -------------------------------------------------------------------- *)
Section SummableAlg.
Context {R : realType} (T : choiceType) (I : Type).

Lemma summable0 : summable (fun _ : T => 0 : R).
Proof. by exists 0 => J; rewrite big1 ?normr0. Qed.

(* -------------------------------------------------------------------- *)
Lemma summableD (S1 S2 : T -> R) :
  summable S1 -> summable S2 -> summable (S1 \+ S2).
Proof.
case=> [M1 h1] [M2 h2]; exists (M1 + M2)%R => J /=.
pose M := \sum_(x : J) (`|S1 (val x)| + `|S2 (val x)|).
rewrite (@ler_trans _ M) // ?ler_sum // => [K _|].
  by rewrite ler_norm_add.
by rewrite /M big_split ler_add ?(h1, h2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma summableN (S : T -> R) : summable S -> summable (\- S).
Proof.
case=> [M h]; exists M => J; rewrite (ler_trans _ (h J)) //.
rewrite ler_eqVlt; apply/orP; left; apply/eqP/eq_bigr.
by move=> /= K _; rewrite normrN.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summablebN (S : T -> R) :
  `[< summable (\- S)>] = `[< summable S >].
Proof.
apply/asboolP/asboolP => /summableN //.
by apply/eq_summable => x /=; rewrite opprK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summablebDl (S1 S2 : T -> R) : summable S1 ->
  `[< summable (S1 \+ S2) >] = `[< summable S2 >].
Proof.
move=> sm1; apply/asboolP/asboolP; last by apply/(summableD sm1).
move=> sm12; apply/(@eq_summable _ _ ((S1 \+ S2) \- S1)).
  by move=> x /=; rewrite addrC addKr.
by apply/summableD/summableN.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summablebDr (S1 S2 : T -> R) : summable S2 ->
  `[< summable (S1 \+ S2) >] = `[< summable S1 >].
Proof.
move=> sm1; rewrite (@eq_summableb _ _ (S2 \+ S1)) ?summablebDl //.
by move=> x /=; rewrite addrC.
Qed.

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
Lemma summableZ (S : T -> R) c : summable S -> summable (c \*o S).
Proof.
case=> [M h]; exists (`|c| * M) => J; move/(_ J): h => /=.
move/(ler_wpmul2l (normr_ge0 c)); rewrite mulr_sumr.
move/(ler_trans _); apply; rewrite ler_eqVlt; apply/orP.
by left; apply/eqP/eq_bigr=> j _; rewrite normrM.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_abs (S : T -> R) : summable \`|S| <-> summable S.
Proof.
have h J: \sum_(j <- J) `| `|S j| | = \sum_(j <- J) `|S j|.
  by apply/eq_bigr=> j _; rewrite normr_id.
split=> /summable_seqP[M ge0_M leM]; apply/summable_seqP;
  by exists M=> // => J /leM; rewrite h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_fpos (f : T -> R) :
  summable f -> summable (fpos f).
Proof.
move/summable_abs; apply/le_summable=> x.
by rewrite ge0_fpos /= le_fpos_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_fneg (f : T -> R) :
  summable f -> summable (fneg f).
Proof. by move/summableN/summable_fpos/(eq_summable (fposN _)). Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_condl (S : T -> R) (P : pred T) :
  summable S -> summable (fun x => (P x)%:R * S x).
Proof.
case/summable_seqP=> M ge0_M leM; apply/summable_seqP.
exists M => //; move=> J /leM /(ler_trans _); apply.
apply/ler_sum=> x _; case: (P x); rewrite (mul1r, mul0r) //.
by rewrite normr0 normr_ge0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_condr (S : T -> R) (P : pred T) :
  summable S -> summable (fun x => S x * (P x)%:R).
Proof.
move=> /(summable_condl P) /eq_summable; apply.
by move=> x /=; rewrite mulrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_of_bd (S : T -> R) (d : R) :
  (forall J, uniq J -> \sum_(x <- J) `|S x| <= d) ->
    summable S /\ psum S <= d.
Proof.
move=> leS; have ge0_d: 0 <= d.
  by apply/(ler_trans _ (leS [::] _)); rewrite // big_nil.
have smS: summable S by apply/summable_seqP; exists d.
split=> //; rewrite /psum (asboolT smS); apply/sup_le_ub.
  by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
apply/ubP=> _ /imsetbP[J ->]; rewrite (big_fset_seq \`|_|) /=.
by apply/leS; case: J => J /= /canonical_uniq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_sum (F : I -> T -> R) (P : pred I) r :
    (forall i, P i -> summable (F i))
  -> summable (fun x => \sum_(i <- r | P i) F i x).
Proof.
move=> sm_F; elim: r => [|i r ih].
  by apply/(eq_summable _ summable0) => x; rewrite big_nil.
pose G x := (F i x) * (P i)%:R + \sum_(i <- r | P i) F i x.
apply/(eq_summable (S1 := G)) => [x|].
  by rewrite {}/G big_cons; case: ifP=> Pi; rewrite !Monoid.simpm.
apply/summableD => //; case/boolP: (P i) => [|_].
  by move/sm_F; apply/eq_summable => x; rewrite mulr1.
by apply/(eq_summable _ summable0) => x; rewrite mulr0.
Qed.

End SummableAlg.

(* -------------------------------------------------------------------- *)
Section StdSum.
Context {R : realType} (T : choiceType) (I : Type).

Implicit Type S : T -> R.

(* -------------------------------------------------------------------- *)
Lemma psum0 : psum (fun _ : T => 0) = 0 :> R.
Proof.
rewrite /psum asboolT; first by apply/summable0.
set S := [pred x | _]; suff: S =1 (pred1 0).
  by move/eq_sup => ->; rewrite sup1.
move=> x; rewrite {}/S inE; apply/idP/idP => /=.
  by case/existsbP=> J /eqP-> /=; rewrite big1 // normr0.
by move=> /eqP->; apply/existsbP; exists fset0; rewrite big_fset0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psum_eq0 (f : T -> R) : (forall x, f x = 0) -> psum f = 0.
Proof. by move=> eq; rewrite (eq_psum eq) psum0. Qed.

(* -------------------------------------------------------------------- *)
Lemma eq0_psum (f : T -> R) :
  summable f -> psum f = 0 -> (forall x : T, f x = 0).
Proof.
move=> sm psum_eq0 x; apply/eqP; rewrite -normr_eq0.
rewrite eqr_le normr_ge0 andbT -psum_eq0.
apply/(ler_trans _ (gerfinseq_psum (r := [:: x]) _ sm)) => //.
by rewrite big_seq1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma neq0_psum (f : T -> R) : psum f <> 0 -> exists x : T, f x <> 0.
Proof.
by move=> nz_psum; apply/existsp_asboolPn/asboolPn => /psum_eq0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psum_abs (S : T -> R) : psum \`|S| = psum S.
Proof.
rewrite /psum; do 2! case: ifPn => //; first last.
+ by move/asboolP/summable_abs/asboolP=> ->.
+ by move/asboolPn/summable_abs/asboolPn=> /negbTE->.
move=> _ _; apply/eq_sup=> x; rewrite !inE; apply/idP/idP.
  case/existsbP=> J /eqP->; apply/existsbP; exists J.
  by apply/eqP/eq_bigr=> /= j _; rewrite normr_id.
case/existsbP=> J /eqP->; apply/existsbP; exists J.
by apply/eqP/eq_bigr=> /= j _; rewrite normr_id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq_psum_abs (S1 S2 : T -> R) :
  \`|S1| =1 \`|S2| -> psum S1 = psum S2.
Proof.
by move=> eqS; rewrite -[LHS]psum_abs -[RHS]psum_abs; apply/eq_psum.
Qed.

(* -------------------------------------------------------------------- *)
Lemma le_psum_abs (S1 S2 : T -> R) :
  (forall x, `|S1 x| <= `|S2 x|) -> summable S2 -> psum S1 <= psum S2.
Proof.
move=> leS smS2; rewrite -[X in X<=_]psum_abs -[X in _<=X]psum_abs.
by apply/le_psum/summable_abs => // x; rewrite normr_ge0 leS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma le_psum_condl (S : T -> R) (P : pred T) :
  summable S -> psum (fun x => (P x)%:R * S x) <= psum S.
Proof.
move=> smS; apply/le_psum_abs=> // x; rewrite normrM.
by apply/ler_pimull => //; rewrite normr_nat lern1 leq_b1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma le_psum_condr (S : T -> R) (P : pred T) :
  summable S -> psum (fun x => S x * (P x)%:R) <= psum S.
Proof.
move=> smS; apply/(ler_trans _ (le_psum_condl P smS)).
rewrite ler_eqVlt -(rwP orP); left; apply/eqP/eq_psum.
by move=> x /=; rewrite mulrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumN (S : T -> R) : psum (\- S) = psum S.
Proof.
case/boolP: `[< summable S >] => h; last first.
  by rewrite !psum_out ?oppr0 //; apply/asboolPn; rewrite ?summablebN.
rewrite /psum summablebN h; apply/eq_ppsum=> J /=.
by apply/eq_bigr=> j _; rewrite normrN.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumD S1 S2 :
    (forall x, 0 <= S1 x) -> (forall x, 0 <= S2 x)
  -> summable S1 -> summable S2
  -> psum (S1 \+ S2) = (psum S1 + psum S2)%R.
Proof.
move=> ge0_S1 ge0_S2 smS1 smS2; have smD := summableD smS1 smS2.
have ge0D: forall x, 0 <= S1 x + S2 x by move=> x; rewrite addr_ge0.
rewrite !psumE // (rwP eqP) eqr_le -(rwP andP); split.
  apply/sup_le_ub.
  + by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
  apply/ubP=> _ /imsetbP[J ->]; rewrite big_split /=.
  apply/ler_add; rewrite -psumE 1?(ler_trans _ (gerfin_psum J _)) //.
  + by apply/ler_sum=> j _ /=; apply/ler_norm.
  + by apply/ler_sum=> j _ /=; apply/ler_norm.
rewrite -ler_subr_addr; apply/sup_le_ub.
+ by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
apply/ubP=> _ /imsetbP[J1 ->]; rewrite ler_subr_addr addrC.
rewrite -ler_subr_addr; apply/sup_le_ub.
+ by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
apply/ubP=> _ /imsetbP[J2 ->]; rewrite ler_subr_addr addrC.
pose J := J1 `|` J2; rewrite -psumE ?(ler_trans _ (gerfin_psum J _)) //.
pose D := \sum_(j : J) (S1 (val j) + S2 (val j)).
apply/(@ler_trans _ D); last by apply/ler_sum=> i _; apply/ler_norm.
rewrite /D big_split /=; apply/ler_add; apply/big_fset_subset=> //.
+ by apply/fsubsetP/fsubsetUl. + by apply/fsubsetP/fsubsetUr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumZ S c : 0 <= c -> psum (c \*o S) = c * psum S.
Proof.
rewrite ler_eqVlt => /orP[/eqP<-|gt0_c].
  by rewrite mul0r psum_eq0 // => x /=; rewrite mul0r.
case/asboolP: (summable S) => [smS|NsmS]; last first.
  rewrite !psum_out ?mulr0 // => smZ; apply/NsmS.
  move/(summableZ c^-1): smZ; apply/eq_summable=> x /=.
  by rewrite mulKf // gtr_eqF.
have smZ := summableZ c smS; rewrite (rwP eqP) eqr_le.
apply/andP; split; first rewrite {1}/psum asboolT //.
  apply/sup_le_ub.
  + by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
  apply/ubP=> _ /imsetbP[J ->]; rewrite -ler_pdivr_mull //.
  rewrite mulr_sumr (ler_trans _ (gerfin_psum J _)) //.
  apply/ler_sum=> /= j _; rewrite normrM.
  by rewrite gtr0_norm // mulKf ?gtr_eqF.
rewrite -ler_pdivl_mull // {1}/psum asboolT //; apply/sup_le_ub.
+ by exists 0; apply/imsetbP; exists fset0; rewrite big_fset0.
apply/ubP=> _ /imsetbP[J ->]; rewrite ler_pdivl_mull //.
rewrite mulr_sumr; apply/(ler_trans _ (gerfin_psum J _))=> //.
by apply/ler_sum=> /= j _; rewrite normrM (gtr0_norm gt0_c).
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumZr S c :
  0 <= c -> psum (c \o* S) = psum S * c.
Proof.
move=> ge0_c; rewrite [RHS]mulrC -psumZ //.
by apply/eq_psum => x /=; rewrite mulrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psum_bigop (F : I -> T -> R) P r :
    (forall i x, 0 <= F i x) -> (forall i, summable (F i)) ->
  \sum_(i <- r | P i) psum (F i) =
    psum (fun x => \sum_(i <- r | P i) F i x).
Proof.
move=> ge0_F sm_F; elim: r => [|i r ih].
  by rewrite big_nil; apply/esym/psum_eq0 => x; rewrite big_nil.
rewrite big_cons ih; case: ifP => Pi; last first.
  by apply/eq_psum=> x /=; rewrite big_cons Pi.
rewrite -psumD //; first by move=> x; apply/sumr_ge0.
  by apply/summable_sum.
by apply/eq_psum=> x /=; rewrite big_cons Pi.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psumID S (P : pred T) :
  summable S -> psum S =
    psum (fun x => (P x)%:R * S x) + psum (fun x => (~~P x)%:R * S x).
Proof.
have h x: `|S x| = (P x)%:R * `|S x| + (~~P x)%:R * `|S x|.
  by case: (P x); rewrite !Monoid.simpm.
move=> smS; rewrite -[LHS]psum_abs (eq_psum h) psumD.
  by move=> x; rewrite mulr_ge0. by move=> x; rewrite mulr_ge0.
  by apply/summable_condl/summable_abs.
  by apply/summable_condl/summable_abs.
congr (_ + _); apply/eq_psum_abs=> x /=.
  by rewrite !normrM normr_nat normr_id.
  by rewrite !normrM normr_nat normr_id.
Qed.

(* -------------------------------------------------------------------- *)
Lemma psum_finseq S (r : seq.seq T) :
    uniq r -> {subset [pred x | S x != 0] <= r}
  -> psum S = \sum_(x <- r) `|S x|.
Proof.
move=> eq_r ler; set s := RHS; have h J: uniq J -> \sum_(x <- J) `|S x| <= s.
  move=> uqJ; rewrite (bigID (ssrbool.mem r)) /= addrC big1.
    move=> x xNr; apply/eqP; apply/contraR: xNr.
    by rewrite normr_eq0 => /ler.
  rewrite add0r {}/s -big_filter; set s := filter _ _.
  rewrite [X in _<=X](bigID (ssrbool.mem J)) /=.
  rewrite (eq_big_perm [seq x <- r | x \in J]) /=.
    apply/uniq_perm_eq; rewrite ?filter_uniq // => x.
    by rewrite !mem_filter andbC.
  by rewrite big_filter ler_addl sumr_ge0.
case/summable_of_bd: h => smS le_psum; apply/eqP.
by rewrite eqr_le le_psum /=; apply/gerfinseq_psum.
Qed.
End StdSum.

(* -------------------------------------------------------------------- *)
Section PSumReindex.
Context {R : realType} {T U : choiceType}.
Context (S : T -> R) (P : pred T) (h : U -> T).

Lemma reindex_psum :
    (forall x, S x != 0 -> x \in P)
  -> {on P, bijective h}
  -> psum S = psum (fun x : U => S (h x)).
Proof.                          (* FIXME: reindex_onto *)
move=> PS [hI] h1 h2; rewrite !psum_sup_seq; apply/eq_sup=> x.
rewrite !inE; apply/asboolP/asboolP=> -[J uqJ /eqP->]; last first.
  exists [seq h j | j <- J & S (h j) != 0].
    rewrite map_inj_in_uniq ?filter_uniq // => y1 y2.
    rewrite !mem_filter => /andP[nz_S1 _] /andP[nz_S2 _].
    by move/(can_in_inj h1) => -> //=; apply/PS.
  apply/eqP; rewrite big_map big_filter.
  rewrite (bigID (fun i => S (h i) == 0)) /= big1 ?add0r //.
  by move=> y /eqP->; rewrite normr0.
exists [seq hI j | j <- J & S j != 0].
rewrite map_inj_in_uniq ?filter_uniq // => y1 y2.
  rewrite !mem_filter => /andP[nz_S1 _] /andP[nz_S2 _].
  by move/(can_in_inj h2) => ->//; apply/PS.
apply/eqP; rewrite big_map big_filter.
rewrite (bigID (fun i => S i == 0)) /= big1 ?add0r.
  by move=> y /eqP->; rewrite normr0.
by apply/eq_bigr=> i /PS Pi; rewrite h2.
Qed.
End PSumReindex.

(* -------------------------------------------------------------------- *)
Section PSumPartition.
Context {R : realType} {T U : choiceType} (f : T -> U).

Let C y := `[exists x : T, f x == y].

Lemma partition_psum (S : T -> R) : summable S ->
  psum S = psum (fun y => psum (fun x => S x * (f x == y)%:R)).
Proof.                          (* FIXME: this proof is a joke *)
move=> smS; rewrite (rwP eqP) eqr_le -(rwP andP); split.
  pose F x y := `|S x| * (f x == y :> U)%:R.
  have smFy y: summable (F^~ y).
    by apply/summable_condr/summable_abs.
  set G := fun y : U => _; have: summable G.
    case/summable_seqP: smS => M ge0_M leM.
    apply/summable_seqP; exists M => // J uqJ; rewrite {}/G.
    rewrite (eq_bigr (fun y => psum (F^~ y))) => [y _|].
      rewrite ger0_norm ?ge0_psum //; apply/eq_psum_abs => x.
      by rewrite !normrM [`|_%:R|]ger0_norm ?(normr_id, ler0n).
    rewrite psum_bigop // => [y x|].
      by rewrite mulr_ge0 ?(normr_ge0, ler0n).
    apply/psum_le=> L uqL; pose G x := \sum_(j <- J | f x == j) `|S x|.
    rewrite (eq_bigr G) => [x _|]; first rewrite ger0_norm //.
    + by rewrite sumr_ge0 // => y _; rewrite mulr_ge0.
    + rewrite /G [RHS]big_mkcond /F /=; apply/eq_bigr=> y _.
      by case: ifPn => //; rewrite !simpm.
    rewrite {}/G /F; pose K := [seq x <- L | f x \in J].
    apply/(ler_trans _ (leM K _)); rewrite ?filter_uniq //.
    rewrite ler_eqVlt -(rwP orP); left; apply/eqP.
    rewrite /K big_filter [RHS]big_mkcond /=; apply/eq_bigr.
    move=> x _; case: ifPn => [fxJ|fxNJ].
      rewrite big_mkcond (bigD1_seq _ fxJ uqJ) /= eqxx.
      by rewrite big1 ?addr0 // => y; rewrite eq_sym => /negbTE=> ->.
    rewrite big_seq_cond big1 // => y; rewrite andbC.
    by case/andP=> /eqP<-; rewrite (negbTE fxNJ).
  move=> smG; apply/psum_le => J uqJ; pose K := undup (map f J).
  move/gerfinseq_psum: smG => /(_ K (undup_uniq _)).
  move/(ler_trans _); apply; rewrite {}/G.
  pose G x y := `|S x| * (f x == y)%:R.
  rewrite (eq_bigr (fun y => psum (G^~ y))).
    move=> y _; rewrite ger0_norm ?ge0_psum //.
    rewrite -psum_abs; apply/eq_psum=> x.
    by rewrite normrM [`|_%:R|]ger0_norm ?ler0n.
  rewrite psum_bigop => [y x|y|]; first by rewrite mulr_ge0.
    by apply/summable_condr/summable_abs.
  rewrite (eq_psum (F2 := fun x => `|S x * (f x \in K)%:R|)).
    move=> x; rewrite {}/G normrM [`|_%:R|]ger0_norm //.
    case/boolP: (f x \in K); last first.
      move=> fxNK; rewrite mulr0 big_seq big1 // => y.
      apply/contraTeq; rewrite mulf_eq0 pnatr_eq0 eqb0.
      by rewrite negb_or negbK => /andP[_ /eqP<-].
    move=> fxK; rewrite (bigD1_seq (f x)) ?undup_uniq //=.
    rewrite eqxx !mulr1 big1 ?addr0 // => y; rewrite eq_sym.
    by move/negbTE=> ->; rewrite mulr0.
  rewrite big_seq (eq_bigr (fun j => `|S j * (f j \in K)%:R|)) {}/G.
    by move=> x /(map_f f); rewrite -mem_undup => ->; rewrite mulr1.
  rewrite psum_abs; set G := (fun x : T => _ in X in _<=X).
  have: summable G by apply/summable_condr.
  move/gerfinseq_psum => /(_ _ uqJ) /(ler_trans _); apply.
  by rewrite -big_seq; apply/ler_sum => x _; rewrite normrM.
apply/psum_le=> J uqJ; pose F j := psum (fun x => `|S x| * (f x == j)%:R).
rewrite (eq_bigr F) => [y _|]; first rewrite ger0_norm ?ge0_psum //.
+ rewrite -psum_abs; apply/eq_psum => x; rewrite normrM.
  by rewrite [`|_%:R|]ger0_norm ?ler0n.
rewrite psum_bigop => [y x|y|].
+ by rewrite mulr_ge0 ?(normr_ge0, ler0n).
+ by apply/summable_condr/summable_abs.
apply/psum_le=> L uqL; pose K := [seq x <- L | f x \in J].
have /gerfinseq_psum: uniq K by rewrite filter_uniq.
move=> /(_ _ _ smS) /(ler_trans _); apply; rewrite big_filter.
rewrite ler_eqVlt -(rwP orP); left; apply/eqP.
rewrite [RHS]big_mkcond /=; apply/eq_bigr=> x _.
rewrite big_seq; case: ifPn => [fx_in_J|fx_Nin_J].
  rewrite -big_seq (bigD1_seq _ fx_in_J uqJ) /= eqxx mulr1.
  rewrite big1 ?addr0 ?normr_id // => y; rewrite eq_sym.
  by move/negbTE=> ->; rewrite mulr0.
rewrite big1 ?normr0 // => y; apply/contraTeq.
rewrite mulf_eq0 pnatr_eq0 eqb0 negb_or negbK.
by case/andP => _ /eqP<-.
Qed.

Lemma partition_psum_cond (S : T -> R) : summable S ->
  psum S = psum (fun y => (C y)%:R * psum (fun x => S x * (f x == y)%:R)).
Proof.
move=> smS; apply/(eq_trans (partition_psum smS)).
apply/eq_psum => y; case/boolP: (C y); rewrite !simpm //.
move=> NCy; rewrite psum_eq0 // => x; case: (_ =P y).
  by move/eqP=> fxE; move/existsbP: NCy; case; exists x.
by rewrite mulr0.
Qed.
End PSumPartition.

(* -------------------------------------------------------------------- *)
(* FIXME: MOVE ME                                                       *)
Section SupInterchange.
Context {R : realType} {T U : Type}.

Lemma interchange_sup (S : T -> U -> R) :
    (forall x, has_sup [pred r | `[exists y, r == S x y]])
  -> has_sup [pred r | `[exists x, r == sup [pred r | `[exists y, r == S x y]]]]
  -> sup [pred r | `[exists x, r == sup [pred r | `[exists y, r == S x y]]]]
  = sup [pred r | `[exists y, r == sup [pred r | `[exists x, r == S x y]]]].
Proof using Type. Admitted.
End SupInterchange.

(* -------------------------------------------------------------------- *)
Section PSumInterchange.
Context {R : realType} {T U : choiceType}.

Lemma interchange_psum (S : T -> U -> R) :
    (forall x, summable (S x))
  -> summable (fun x => psum (fun y => S x y))
  -> psum (fun x => psum (fun y => S x y)) = psum (fun y => psum (fun x => S x y)).
Proof using Type. Admitted.
End PSumInterchange.

(* -------------------------------------------------------------------- *)
Section SumTheory.
Context {R : realType} {T : choiceType}.

Implicit Types (S : T -> R).

Lemma psum_sum S : (forall x, 0 <= S x) -> psum S = sum S.
Proof.
move=> ge0_S; rewrite /sum [X in _-X]psum_eq0 ?subr0.
  by move=> x; rewrite fneg_ge0 //. 
by apply/eq_psum=> x; rewrite fpos_ge0.
Qed.

Lemma le_sum S1 S2 :
  summable S1 -> summable S2 -> (S1 <=1 S2) ->
    sum S1 <= sum S2.
Proof.
move=> smS1 smS2 leS; rewrite /sum ler_sub //.
  apply/le_psum/summable_fpos => // x.
  by rewrite ge0_fpos /= le_fpos.
apply/le_psum/summable_fneg => // x.
rewrite -!fposN ge0_fpos le_fpos // => y.
by rewrite ler_opp2.
Qed.

Lemma sum0 : sum (fun _ : T => 0) = 0 :> R.
Proof. by rewrite /sum !(eq_psum fpos0, eq_psum fneg0) !psum0 subr0. Qed.

Lemma sumN S : sum (\- S) = - sum S.
Proof. by rewrite /sum (eq_psum (fnegN _)) (eq_psum (fposN _)) opprB. Qed.

Lemma sumZ S c : sum (c \*o S) = c * sum S.
Proof.
rewrite (eq_sum (F2 := fun x => Num.sg c * (`|c| * S x))).
  by move=> x; rewrite mulrA -numEsg.
transitivity (Num.sg c * sum (`|c| \*o S)).
  case: sgrP => [_|gt0_c|lt0_c]; rewrite ?Monoid.simpm.
  + by rewrite (eq_sum (F2 := fun _ => 0)) ?sum0 // => x; rewrite !mul0r.
  + by apply/eq_sum=> x; rewrite mul1r.
  by rewrite mulN1r -sumN; apply/eq_sum=> x; rewrite !mulN1r.
rewrite {1}/sum !(eq_psum (fposZ _ _), eq_psum (fnegZ _ _)) //.
by rewrite !psumZ // -mulrBr mulrA -numEsg.
Qed.

Lemma sumID S (P : pred T) :
  summable S -> sum S =
    sum (fun x => (P x)%:R * S x) + sum (fun x => (~~ P x)%:R * S x).
Proof.
move=> sm_S; rewrite /sum addrACA -[in RHS]opprD; congr (_ - _).
+ rewrite (psumID P); first by apply/summable_fpos.
  by congr (_ + _); apply/eq_psum => x; rewrite fpos_natrM.
+ rewrite (psumID P); first by apply/summable_fneg.
  by congr (_ + _); apply/eq_psum => x; rewrite fneg_natrM.
Qed.

Lemma sum_finseq S (r : seq T) :
  uniq r -> {subset [pred x | S x != 0] <= r} ->
    sum S = \sum_(x <- r) S x.
Proof.
move=> eqr domS; rewrite /sum !(psum_finseq eqr).
+ move=> x; rewrite !inE => xPS; apply/domS; rewrite !inE.
  move: xPS; rewrite /fpos normr_eq0 /Num.max.
  by case: ifPn => //; rewrite eqxx.
+ move=> x; rewrite !inE => xPS; apply/domS; rewrite !inE.
  move: xPS; rewrite /fneg normr_eq0 /Num.min.
  by case: ifPn => //; rewrite eqxx.
rewrite -sumrB; apply/eq_bigr=> i _.
by rewrite !ger0_norm ?(ge0_fpos, ge0_fneg) ?fposBfneg.
Qed.

Lemma sum_seq1 S x : (forall y, S y != 0 -> x == y) -> sum S = S x.
Proof.
move=> domS; rewrite (sum_finseq (r := [:: x])) //.
  by move=> y; rewrite !inE => /domS /eqP->.
by rewrite big_seq1.
Qed.
End SumTheory.

Arguments sum_seq1 {R T} [S] x _.
