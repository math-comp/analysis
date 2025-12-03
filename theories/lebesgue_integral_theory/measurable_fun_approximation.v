(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference topology ereal tvs normedtype.
From mathcomp Require Import sequences real_interval function_spaces esum.
From mathcomp Require Import measure lebesgue_measure numfun realfun exp.
From mathcomp Require Import simple_functions.

(**md**************************************************************************)
(* # Approximation theorem for measurable functions                           *)
(*                                                                            *)
(* Applications: measurability of arithmetic of functions, Lusin's theorem.   *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* ```                                                                        *)
(*         dyadic_itv n k == the interval                                     *)
(*                           `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[           *)
(*             approx D f == nondecreasing sequence of functions that         *)
(*                           approximates f over D using dyadic intervals     *)
(*                           It uses the sets dyadic_approx and               *)
(*                           integer_approx.                                  *)
(*      nnsfun_approx D f == same as approx D f but as a nnsfun               *)
(*                           approximates f over D using dyadic intervals     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section dyadic_interval.
Variable R : realType.

Definition dyadic_itv n k : interval R :=
  `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[.

Local Notation I := dyadic_itv.

Lemma dyadic_itv_subU n k : [set` I n k] `<=`
  [set` I n.+1 k.*2] `|` [set` I n.+1 k.*2.+1].
Proof.
move=> r Hr; apply/orP; rewrite -itv_splitU ?bnd_simp/=; last first.
  by rewrite !ler_pM2r// !ler_nat leqW//=.
move: Hr; apply/subitvP; rewrite {r}!subitvE !bnd_simp exprSr -muln2.
rewrite ler_pdivrMr// mulrA divfK// -natrM lexx/=.
by rewrite ler_pdivlMr// mulrA divfK// -natrM ler_nat.
Qed.

Lemma bigsetU_dyadic_itv n : `[n%:R, n.+1%:R[%classic =
  \big[setU/set0]_(n * 2 ^ n.+1 <= k < n.+1 * 2 ^ n.+1) [set` I n.+1 k].
Proof.
rewrite predeqE => r; split => [/= /[!in_itv]/= /andP[nr rn1]|]; last first.
  rewrite -bigcup_seq => -[/= k] /[!mem_index_iota] nkn; apply: subitvP.
  rewrite subitvE !bnd_simp ler_pdivlMr// ler_pdivrMr//.
  by rewrite -natrX -2!natrM 2!ler_nat.
have ?: 0 <= r * 2 ^+ n.+1 by rewrite mulr_ge0// (le_trans _ nr).
rewrite -bigcup_seq /=; exists (truncn (r * 2 ^+ n.+1)).
  rewrite /= mem_index_iota truncn_ge_nat// truncn_lt_nat//.
  by rewrite !natrM natrX ler_pM2r// ltr_pM2r// nr.
rewrite /= in_itv/= ler_pdivrMr// ltr_pdivlMr//.
by rewrite -truncn_ge_nat// -truncn_lt_nat// !leqnn.
Qed.

Lemma dyadic_itv_image n T (f : T -> \bar R) x :
  (n%:R%:E <= f x < n.+1%:R%:E)%E ->
  exists k, (2 ^ n.+1 * n <= k < 2 ^ n.+1 * n.+1)%N /\
    f x \in EFin @` [set` I n.+1 k].
Proof.
move=> fxn; have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxn; case: (f x) => // /andP[].
have : f x \in EFin @` `[n%:R, n.+1%:R[%classic.
  rewrite inE /=; exists (fine (f x)); last by rewrite fineK.
  by rewrite in_itv /= -lee_fin -lte_fin (fineK fxfin).
rewrite (bigsetU_dyadic_itv n) inE /= => -[r]; rewrite -bigcup_seq => -[k /=].
rewrite mem_index_iota => nk Ir rfx.
by exists k; split; [rewrite !(mulnC (2 ^ n.+1)%N)|rewrite !inE /=; exists r].
Qed.

End dyadic_interval.

Section approximation.
Context d (T : measurableType d) (R : realType).
Variables (D : set T) (mD : measurable D).
Variables (f : T -> \bar R) (mf : measurable_fun D f).

Local Notation I := (@dyadic_itv R).

Definition dyadic_approx n k := if (k < n * 2 ^ n)%N then
  D `&` [set x | f x \in EFin @` [set` I n k]] else set0.

Definition integer_approx n := D `&` [set x | n%:R%:E <= f x]%E.

Local Notation A := dyadic_approx.
Local Notation B := integer_approx.

Definition approx : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * \1_(A n k) x + n%:R * \1_(B n) x.

(* technical properties of the sets A and B *)
Let mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]//; rewrite -preimage_comp.
by apply: mf => //; apply/measurable_image_EFin; exact: measurable_itv.
Qed.

Let trivIsetA n : trivIset setT (A n).
Proof.
apply/trivIsetP => i j _ _ ineqj.
rewrite /A; case: ltnP => ni; last by rewrite set0I.
case: ltnP => nj; last by rewrite setI0.
rewrite predeqE/= => t; rewrite !inE; split=> // -[[Dt [r rI rE]] [_ [s + sE]]].
have {s sE}[->/(conj rI)/andP]: s%:E = r%:E by rewrite rE sE.
rewrite -{rI}in_itvI /Order.meet /= /Order.join /= /Order.meet /= !orbT !andbT.
rewrite le_total joinEtotal meetEtotal -maxr_pMl// -minr_pMl// in_itv/=.
case/andP => [/le_lt_trans/[apply]]; rewrite ltr_pM2r//.
rewrite /maxr /minr !ltr_nat ltnS -!fun_if ltr_nat ltnS.
by case: ltngtP ineqj => //=; case: ltngtP.
Qed.

Let f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> fx0 i0; rewrite indicE memNset// /A ltn_ord => -[Dx/=] /[1!inE]/= -[r].
rewrite in_itv/= fx0 => /[swap] -[->].
by rewrite ler_pdivrMr// mul0r lern0 (negbTE i0).
Qed.

Let fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> fxn; rewrite indicE /A ltn_ord memNset// => -[Dx/=] /[1!inE]/= -[r].
rewrite in_itv/= => /andP[_ h] rfx; move: fxn; rewrite -rfx lee_fin; apply/negP.
by rewrite -ltNge (lt_le_trans h)// ler_pdivrMr// -natrX -natrM ler_nat ltn_ord.
Qed.

Let disj_A0 x n (i k : 'I_(n * 2 ^ n)) : i != k -> x \in A n k ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> ik /[1!inE] xAn1k; rewrite indicE memNset// => xAi.
have /trivIsetP/(_ _ _ Logic.I Logic.I ik)/= := @trivIsetA n.
by rewrite predeqE => /(_ x)[+ _]; exact.
Qed.
Arguments disj_A0 {x n i} k.

Let mB n : measurable (B n). Proof. exact: emeasurable_fun_c_infty. Qed.

Let foo_B1 x n : D x -> f x = +oo%E -> \1_(B n) x = 1 :> R.
Proof. by move=> Dx fxoo; rewrite indicE mem_set// /B/= fxoo leey. Qed.

Let f0_B0 x n : f x = 0%:E -> n != 0%N -> \1_(B n) x = 0 :> R.
Proof.
by move=> h /negbTE n0; rewrite indicE memNset// /B/= h lee_fin lern0 n0 => -[].
Qed.

Let fgtn_B0 x n : (f x < n%:R%:E)%E -> \1_(B n) x = 0 :> R.
Proof. by move=> h; rewrite indicE memNset// => -[_/=]; rewrite leNgt h. Qed.

Let f0_approx0 n x : f x = 0%E -> approx n x = 0.
Proof.
move=> fx0; rewrite /approx; have [->|n0] := eqVneq n O.
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0// mulr0 addr0 big1// => i _.
have [->|i0] := eqVneq (nat_of_ord i) 0%N; first by rewrite mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Let fpos_approx_neq0 x : D x -> (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx n x != 0.
Proof.
move=> Dx /andP[fx_gt0 fxoo].
have fxfin : f x \is a fin_num by rewrite gt0_fin_numE.
rewrite -(fineK fxfin) lte_fin in fx_gt0; near=> n.
rewrite /approx paddr_eq0 ?psumr_eq0 ?sumr_ge0//.
apply/negP => /andP[/allP An0]; rewrite mulf_eq0 => /orP[|].
  by apply/negP; near: n; exists 1%N => //= m /=; rewrite lt0n pnatr_eq0.
rewrite pnatr_eq0 eqb0 notin_setE /B => /not_andP[] // /negP.
rewrite -ltNge => fxn.
have K : (truncn (fine (f x) * 2 ^+ n) < n * 2 ^ n)%N.
  rewrite truncn_lt_nat; last by rewrite mulr_ge0// ltW.
  by rewrite natrM natrX ltr_pM2r// -lte_fin (fineK fxfin).
have /[!mem_index_enum]/(_ isT) := An0 (Ordinal K).
rewrite implyTb indicE mem_set ?mulr1; last first.
  rewrite /A K /= inE; split=> //=; exists (fine (f x)); last by rewrite fineK.
  by rewrite in_itv/= ler_pdivrMr// ltr_pdivlMr// truncn_itv// mulr_ge0// ltW.
apply/negP; rewrite mulf_eq0 -exprVn negb_or expf_neq0//= andbT.
rewrite pnatr_eq0 -lt0n truncn_gt0 -ler_pdivrMr// ltW//; near: n.
exact: near_infty_natSinv_expn_lt (PosNum fx_gt0).
Unshelve. all: by end_near. Qed.

Let f_ub_approx n x : (f x < n%:R%:E)%E ->
  approx n x == 0 \/ exists k,
    [/\ (0 < k < n * 2 ^ n)%N,
       x \in A n k, approx n x = k%:R / 2 ^+ n &
       f x \in EFin @` [set` I n k]].
Proof.
move=> fxn; rewrite /approx fgtn_B0 // mulr0 addr0.
set lhs := (X in X == 0); have [|] := eqVneq lhs 0; first by left.
rewrite {}/lhs psumr_eq0; last by move=> i _; rewrite mulr_ge0.
move=> /allPn[/= k _].
rewrite mulf_eq0 negb_or mulf_eq0 negb_or -andbA => /and3P[k_neq0 _].
rewrite pnatr_eq0 eqb0 negbK => xAnk; right.
rewrite (bigD1 k) //= indicE xAnk mulr1 big1 ?addr0; last first.
  by move=> i ik; rewrite (disj_A0 k)// mulr0.
exists k; split => //; first by rewrite lt0n -(@pnatr_eq0 R) k_neq0/=.
by move: xAnk; rewrite inE /A ltn_ord /= inE /= => -[/[swap] Dx].
Qed.

Let notinD_approx0 x n : ~ D x -> approx n x = 0 :> R.
Proof.
move=> Dx; rewrite /approx big1; last first.
  by move=> i _; rewrite indicE memNset ?mulr0// /A; case: ifPn => [? []|_].
by rewrite indicE memNset// ?mulr0 ?addr0// => -[].
Qed.

Lemma nd_approx : nondecreasing_seq approx.
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x.
have [Dx|Dx] := pselect (D x); last by rewrite ?notinD_approx0.
have [fxn|fxn] := ltP (f x) n%:R%:E.
  rewrite {2}/approx fgtn_B0 ?mulr0 ?addr0; last first.
    by rewrite (lt_trans fxn) // lte_fin ltr_nat.
  have [/eqP ->|[k [/andP[k0 kn] xAnk -> _]]] := f_ub_approx fxn.
    by apply: sumr_ge0 => i _; rewrite mulr_ge0.
  move: (xAnk); rewrite inE {1}/A kn => -[_] /=.
  rewrite inE => -[r] /dyadic_itv_subU[|] rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //= indicE.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite inE /A k2n; split => //=; rewrite inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0.
    by rewrite exprS invfM mulrA -muln2 natrM mulfK.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //= indicE.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite /A /= k2n inE; split => //=; rewrite inE/=; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) // mulr0.
    by rewrite ler_pdivlMr// exprSr mulrA divfK// -natrM muln2 ler_nat.
have /orP[{}fxn|{}fxn] :
    ((n%:R%:E <= f x < n.+1%:R%:E) || (n.+1%:R%:E <= f x))%E.
  - by move: fxn; case: leP => /= [_ _|_ ->//]; rewrite orbT.
  - have [k [k1 k2]] := dyadic_itv_image fxn.
    have xBn : x \in B n by rewrite /B /= inE /=; case/andP : fxn => ->.
    rewrite /approx indicE xBn mulr1 big1 ?add0r; last first.
      by move=> /= i _; rewrite fgen_A0 ?mulr0//; case/andP : fxn.
    rewrite fgtn_B0 ?mulr0 ?addr0; last by case/andP : fxn.
    have kn2 : (k < n.+1 * 2 ^ n.+1)%N by case/andP : k1 => _; rewrite mulnC.
    rewrite (bigD1 (Ordinal kn2)) //=.
    have xAn1k : x \in A n.+1 k by rewrite inE /A kn2.
    rewrite indicE xAn1k mulr1 big1 ?addr0; last first.
      by move=> i /= ikn2; rewrite (disj_A0 (Ordinal kn2)) // mulr0.
    by rewrite -natrX ler_pdivlMr// mulrC -natrM ler_nat; case/andP : k1.
- have xBn : x \in B n by rewrite /B inE /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx indicE xBn mulr1.
  have xBn1 : x \in B n.+1 by rewrite /B /= inE.
  rewrite indicE xBn1 mulr1 big1 ?add0r.
    by rewrite big1 ?add0r ?ler_nat// => /= i _; rewrite fgen_A0// mulr0.
  by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn)// lee_fin ler_nat.
Qed.

Lemma cvg_approx x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  (f x < +oo)%E -> approx^~ x @ \oo --> fine (f x).
Proof.
move=> Dx fxoo; have fxfin : f x \is a fin_num by rewrite ge0_fin_numE// f0.
apply/(@cvgrPdist_lt _ R^o) => _/posnumP[e].
have [fx0|fx0] := eqVneq (f x) 0%E.
  by near=> n; rewrite f0_approx0// fx0 /= subrr normr0.
have /(fpos_approx_neq0 Dx)[m _ Hm] : (0 < f x < +oo)%E by rewrite lt0e fx0 f0.
near=> n.
have mn : (m <= n)%N by near: n; exists m.
have : fine (f x) < n%:R.
  near: n; exists (truncn (fine (f x))).+2 => //= p /= fxp.
  by rewrite (lt_trans (truncnS_gt _))// ltr_nat.
rewrite -lte_fin (fineK fxfin) => fxn.
have [approx_nx0|[k [/andP[k0 kn2n] ? ->]]] := f_ub_approx fxn.
  by have := Hm _ mn; rewrite approx_nx0.
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[k1 k2] rfx.
rewrite (@le_lt_trans _ _ (1 / 2 ^+ n)) //.
  rewrite ler_norml; apply/andP; split.
    rewrite lerBrDl -mulrBl -lee_fin (fineK fxfin) -rfx lee_fin.
    by rewrite (le_trans _ k1)// ler_pM2r// lerBlDl lerDr.
  by rewrite lerBlDr -mulrDl -lee_fin nat1r fineK// ltW// -rfx lte_fin.
by near: n; exact: near_infty_natSinv_expn_lt.
Unshelve. all: by end_near. Qed.

Lemma le_approx k x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  ((approx k x)%:E <= f x)%E.
Proof.
move=> Dx; have [fixoo|] := ltP (f x) (+oo%E); last first.
  by rewrite leye_eq => /eqP ->; rewrite leey.
have nd_ag : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; exact/lefP/nd_approx.
have fi0 y : D y -> (0 <= f y)%E by move=> ?; exact: f0.
have cvg_af := cvg_approx fi0 Dx fixoo.
have is_cvg_af : cvgn (approx ^~ x) by apply/cvg_ex; eexists; exact: cvg_af.
have {is_cvg_af} := nondecreasing_cvgn_le nd_ag is_cvg_af k.
rewrite -lee_fin => /le_trans; apply.
rewrite -(@fineK _ (f x)); last by rewrite ge0_fin_numE// f0.
by move/(cvg_lim (@Rhausdorff R)) : cvg_af => ->.
Qed.

Lemma dvg_approx x : D x -> f x = +oo%E -> ~ cvgn (approx^~ x : _ -> R^o).
Proof.
move=> Dx fxoo; have approx_x n : approx n x = n%:R.
  rewrite /approx foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo leey.
move=> /cvg_ex[/= l /cvgrPdist_lt/(_ _ ltr01) [n _]].
move=> /(_ ((truncn l).+2 + n) (leq_addl _ _)); apply/negP.
rewrite -leNgt approx_x distrC natrD addrAC ger0_norm ler_wpDr//.
  by rewrite lerBrDl -natr1 lerD// ltW// truncnS_gt.
by rewrite subr_ge0 -natr1 ler_wpDr// ltW// truncnS_gt.
Qed.

Lemma ecvg_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o approx^~x @ \oo --> f x.
Proof.
move=> Dx; have := leey (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx := dvg_approx Dx fxoo.
  have : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx mn => /lefP; exact.
  move/nondecreasing_dvgn_lt => /(_ dvg_approx).
  by rewrite fxoo => ?; apply/cvgeryP.
rewrite -(@fineK _ (f x)); first exact: (cvg_comp _ _ (cvg_approx f0 Dx fxoo)).
by rewrite ge0_fin_numE// f0.
Qed.

Let k2n_ge0 n (k : nat) : 0 <= k%:R * 2 ^- n :> R.
Proof. by []. Qed.

Definition nnsfun_approx : {nnsfun T >-> R}^nat := fun n => locked (add_nnsfun
  (sum_nnsfun
    (fun k => if (k < (n * 2 ^ n))%N then
        scale_nnsfun (indic_nnsfun _ (mA n k)) (k2n_ge0 n k)
      else nnsfun0) (n * 2 ^ n)%N)
  (scale_nnsfun (indic_nnsfun _ (mB n)) (ler0n _ n))).

Import HBNNSimple.

Lemma nnsfun_approxE n : nnsfun_approx n = approx n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite /nnsfun_approx; unlock; rewrite /=.
rewrite sum_nnsfunE; congr (_ + _).
by apply: eq_bigr => i _; case: ltnP => [//|]; rewrite leqNgt ltn_ord.
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o nnsfun_approx^~x @ \oo --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof.
move=> m n mn; rewrite (nnsfun_approxE n) (nnsfun_approxE m).
exact: nd_approx.
Qed.

#[deprecated(since="mathcomp-analysis 1.8.0", note="use `nnsfun_approx`, `cvg_nnsfun_approx`, and `nd_nnsfun_approx` instead")]
Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : {nnsfun T >-> R}^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~ x @ \oo --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|].
by move=> x Dx; exact: cvg_nnsfun_approx.
Qed.

End approximation.

Section approximation_sfun.
Context d (T : measurableType d) (R : realType) (f : T -> \bar R).
Variables (D : set T) (mD : measurable D) (mf : measurable_fun D f).

Import HBSimple.
(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FImFun T R (cst x) := FImFun.on (cst x).

Import HBNNSimple.
(* NB: already instantiated in lebesgue_integral.v *)
HB.instance Definition _ x : @NonNegFun T R (cst x%:num) :=
  NonNegFun.on (cst x%:num).

Lemma approximation_sfun :
  exists g : {sfun T >-> R}^nat, (forall x, D x -> EFin \o g ^~ x @ \oo --> f x).
Proof.
pose fp_ := nnsfun_approx mD (measurable_funepos mf).
pose fn_ := nnsfun_approx mD (measurable_funeneg mf).
exists (fun n => fp_ n \+ cst (-1) \* fn_ n) => x /=.
rewrite [X in X @ \oo --> _](_ : _ =
    EFin \o fp_^~ x \+ (-%E \o EFin \o fn_^~ x))%E; last first.
  by apply/funext => n/=; rewrite EFinD mulN1r.
by move=> Dx; rewrite (funeposneg f); apply: cvgeD;
  [exact: add_def_funeposneg|apply: cvg_nnsfun_approx|apply:cvgeN; apply: cvg_nnsfun_approx].
Qed.

End approximation_sfun.

Section emeasurable_fun_arith.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).

Import HBSimple.

Lemma emeasurable_funD D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \+ g).
Proof.
move=> mf mg mD.
have Cnoom : measurable (~` [set -oo] : set (\bar R)) by apply: measurableC.
have Cpoom : measurable (~` [set +oo] : set (\bar R)) by apply: measurableC.
have mfg :  measurable (D `&` [set x | f x +? g x]).
  suff -> : [set x | f x +? g x] =
              (f @^-1` (~` [set +oo]) `|` g @^-1` (~` [set -oo])) `&`
              (f @^-1` (~` [set -oo]) `|` g @^-1` (~` [set +oo])).
     by rewrite setIIr; apply: measurableI;
        rewrite setIUr; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /adde_def !(negb_and, negb_or).
   by rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
wlog fg : D mD mf mg mfg / forall x, D x -> f x +? g x => [hwlogD|]; last first.
   have [f_ f_cvg] := approximation_sfun mD mf.
   have [g_ g_cvg] := approximation_sfun mD mg.
   apply: (emeasurable_fun_cvg (fun n x => (f_ n x + g_ n x)%:E)) => //.
     by move=> n; exact/measurable_EFinP/measurable_funTS/measurable_funD.
  move=> x Dx; under eq_fun do rewrite EFinD.
  exact: cvgeD (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NAnoo: A mD mf mg mA / ~ (A -oo) => [hwlogA|].
  have [] := pselect (A -oo); last exact: hwlogA.
  move=> /(@setD1K _ -oo)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case=>/=].
  have -> : (f \+ g) @^-1` [set -oo] = f @^-1` [set -oo] `|` g @^-1` [set -oo].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
     - by rewrite adde_eq_ninfty => /orP[] /eqP ->; [left|right].
     - by move=> ->.
     - by move=> ->; rewrite addeC.
   by rewrite setIUr; apply: measurableU; [apply: mf|apply: mg].
have-> : D `&` (f \+ g) @^-1` A =
       (D `&` [set x | f x +? g x]) `&` (f \+ g) @^-1` A.
  rewrite -setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //.
  by case: (f x) (g x) Afgx => [rf||] [rg||].
have Dfg : D `&` [set x | f x +? g x] `<=` D by apply: subIset; left.
apply: hwlogD => //.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite -setIA setIid.
- by move=> ? [].
Qed.

Lemma emeasurable_sum D I s (h : I -> (T -> \bar R)) :
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
elim: s => [|s t ih] mf.
  by under eq_fun do rewrite big_nil; exact: measurable_cst.
under eq_fun do rewrite big_cons //=; apply: emeasurable_funD => //.
exact: ih.
Qed.

Lemma emeasurable_fsum D (I : choiceType) (A : set I)
    (h : I -> (T -> \bar R)) : finite_set A ->
    (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i \in A) h i x).
Proof.
move=> fs mh; under eq_fun do rewrite fsbig_finite//.
exact: emeasurable_sum.
Qed.

Lemma ge0_emeasurable_sum D (h : nat -> (T -> \bar R)) (P : pred nat) :
    (forall k x, D x -> P k -> 0 <= h k x) ->
    (forall k, P k -> measurable_fun D (h k)) ->
  measurable_fun D (fun x => \sum_(i <oo | i \in P) h i x).
Proof.
move=> h0 mh mD; move: (mD); apply/measurable_restrictT => //.
rewrite [X in measurable_fun _ X](_ : _ =
  (fun x => \sum_(0 <= i <oo | i \in P) (h i \_ D) x)); last first.
  apply/funext => x/=; rewrite /patch; case: ifPn => // xD.
  by rewrite eseries0.
rewrite [X in measurable_fun _ X](_ : _ =
    (fun x => limn_esup (fun n => \sum_(0 <= i < n | P i) (h i) \_ D x))); last first.
  apply/funext=> x; rewrite is_cvg_limn_esupE//.
  apply: is_cvg_nneseries_cond => n _ Pn; rewrite patchE.
  by case: ifPn => // xD; rewrite h0//; exact/set_mem.
apply: measurable_fun_limn_esup => k.
under eq_fun do rewrite big_mkcond.
apply: emeasurable_sum => n.
have [|] := boolP (n \in P); last by rewrite /in_mem/= => /negbTE ->.
rewrite /in_mem/= => Pn; rewrite Pn.
by apply/(measurable_restrictT _ _).1 => //; exact: mh.
Qed.

Lemma emeasurable_funB D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \- g).
Proof.
by move=> mf mg mD; apply: emeasurable_funD => //; exact: measurableT_comp.
Qed.

Lemma emeasurable_funM D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \* g).
Proof.
move=> mf mg mD.
have m0 : measurable ([set 0] : set (\bar R)) by [].
have mC0 : measurable ([set~ 0] : set (\bar R)) by apply: measurableC.
have mCoo : measurable (~` [set -oo; +oo] : set (\bar R)).
  exact/measurableC/measurableU.
have mfg : measurable (D `&` [set x | f x *? g x]).
  suff -> : [set x | f x *? g x] =
              (f @^-1` (~` [set 0]) `|` g @^-1` (~` [set -oo; +oo])) `&`
              (g @^-1` (~` [set 0]) `|` f @^-1` (~` [set -oo; +oo])).
     by rewrite setIIr; apply: measurableI;
        rewrite setIUr; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /mule_def/=.
   rewrite !(rwP2 eqP idP, rwP2 negP idP, rwP2 orP idP, rwP2 andP idP).
   by case: (f x) (g x) => [?||] [?||]//=; rewrite ?(orbT, andbT, orbF).
wlog fg : D mD mf mg mfg / forall x, D x -> f x *? g x => [hwlogM|]; last first.
  have [f_ f_cvg] := approximation_sfun mD mf.
  have [g_ g_cvg] := approximation_sfun mD mg.
  apply: (emeasurable_fun_cvg (fun n x => (f_ n x * g_ n x)%:E)) => // [n|x Dx].
    by apply/measurable_EFinP/measurable_funM; exact: measurable_funTS.
  exact: cvgeM (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NA0: A mD mf mg mA / ~ (A 0) => [hwlogA|].
  have [] := pselect (A 0); last exact: hwlogA.
  move=> /(@setD1K _ 0)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case=>/=].
  have -> : (fun x => f x * g x) @^-1` [set 0] =
           f @^-1` [set 0] `|` g @^-1` [set 0].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
       by rewrite mule_eq0 => /orP[] /eqP->; [left|right].
     by move=> ->; rewrite mul0e.
     by move=> ->; rewrite mule0.
  by rewrite setIUr; apply: measurableU; [exact: mf|exact: mg].
have-> : D `&` (fun x => f x * g x) @^-1` A =
       (D `&` [set x | f x *? g x]) `&` (fun x => f x * g x) @^-1` A.
  rewrite -setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //; apply: neq0_mule_def.
  by apply: contra_notT NA0; rewrite negbK => /eqP <-.
have Dfg : D `&` [set x | f x *? g x] `<=` D by apply: subIset; left.
apply: hwlogM => //.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite -setIA setIid.
- by move=> ? [].
Qed.

Lemma measurable_funeM D (f : T -> \bar R) (k : \bar R) :
  measurable_fun D f -> measurable_fun D (fun x => k * f x)%E.
Proof. by move=> mf; exact/(emeasurable_funM _ mf). Qed.

End emeasurable_fun_arith.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_sum`")]
Notation emeasurable_fun_sum := emeasurable_sum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_fsum`")]
Notation emeasurable_fun_fsum := emeasurable_fsum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `ge0_emeasurable_sum`")]
Notation ge0_emeasurable_fun_sum := ge0_emeasurable_sum (only parsing).

Section measurable_sum.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> R).

Lemma measurable_sum D I s (h : I -> T -> R) :
  (forall i, measurable_fun D (h i)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
move=> mh; apply/measurable_EFinP.
rewrite (_ : _ \o _ = (fun t => \sum_(i <- s) (h i t)%:E)); last first.
  by apply/funext => t/=; rewrite -sumEFin.
by apply/emeasurable_sum => i; exact/measurable_EFinP.
Qed.

Lemma measurable_prod D (I : eqType) (s : seq I) (h : I -> T -> R) :
  (forall i, i \in s -> measurable_fun D (h i)) ->
  measurable_fun D (fun x => \prod_(i <- s) h i x).
Proof.
elim: s => [mh|x y ih mh].
  by under eq_fun do rewrite big_nil//=; exact: measurable_cst.
under eq_fun do rewrite big_cons//=; apply: measurable_funM => //.
- by apply: mh; rewrite mem_head.
- by apply: ih => n ny; apply: mh; rewrite inE orbC ny.
Qed.

End measurable_sum.

Section emeasurable_comparison.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variables (D : set T) (mD : measurable D).
Implicit Types f g : T -> \bar R.

Lemma measurable_lte f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x < g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_gt0.
by apply: emeasurable_fun_o_infty => //; exact: emeasurable_funB.
Qed.

Lemma measurable_lee f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_le0.
by apply: emeasurable_fun_infty_c => //; exact: emeasurable_funB.
Qed.

Lemma measurable_eqe f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x = g x]).
Proof.
move=> mf mg; rewrite set_eq_le setIIr.
by apply: measurableI; exact: measurable_lee.
Qed.

Lemma measurable_neqe f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x != g x]).
Proof.
move=> mf mg; rewrite set_neq_lt setIUr.
by apply: measurableU; exact: measurable_lte.
Qed.

End emeasurable_comparison.
#[deprecated(since="mathcomp-analysis 1.11.0", note="renamed to `measurable_lte`")]
Notation emeasurable_fun_lt := measurable_lte (only parsing).
#[deprecated(since="mathcomp-analysis 1.11.0", note="renamed to `measurable_lee`")]
Notation emeasurable_fun_le := measurable_lee (only parsing).
#[deprecated(since="mathcomp-analysis 1.11.0", note="renamed to `measurable_eqe`")]
Notation emeasurable_fun_eq := measurable_eqe (only parsing).
#[deprecated(since="mathcomp-analysis 1.11.0", note="renamed to `measurable_neqe`")]
Notation emeasurable_fun_neq := measurable_neqe (only parsing).

Section emeasurable_fun_comparison.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).
Local Open Scope ereal_scope.

Lemma measurable_fun_lte D f g : measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x < g x).
Proof.
move=> mf mg mD; apply: (measurable_fun_bool true) => //.
exact: measurable_lte.
Qed.

Lemma measurable_fun_lee D f g : measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x <= g x).
Proof.
move=> mf mg mD; apply: (measurable_fun_bool true) => //.
exact: measurable_lee.
Qed.

Lemma measurable_fun_eqe D f g : measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x == g x).
Proof.
move=> mf mg.
rewrite (_ : (fun x => f x == g x) = (fun x => (f x <= g x) && (g x <= f x))).
  by apply: measurable_and; exact: measurable_fun_lee.
by under eq_fun do rewrite eq_le.
Qed.

End emeasurable_fun_comparison.

Lemma measurable_poweR (R : realType) r :
  measurable_fun [set: \bar R] (poweR ^~ r).
Proof.
under eq_fun do rewrite poweRE.
rewrite -/(measurable_fun _ _).
apply: measurable_fun_ifT => //=.
  apply/measurable_EFinP => //=.
  apply: measurable_fun_ifT => //=.
    apply: (measurable_fun_bool true).
    rewrite setTI (_ : _ @^-1` _ = EFin @` setT).
      by apply: measurable_image_EFin; exact: measurableT.
    apply/seteqP; split => [x finx|x [s sx <-//]]/=.
    by exists (fine x) => //; rewrite fineK.
  exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)).
apply: measurable_fun_ifT => //=; first exact: measurable_fun_eqe.
apply: measurable_fun_ifT => //=; first exact: measurable_fun_eqe.
apply/measurable_EFinP => //=.
exact: (@measurableT_comp _ _ _ _ _ _ (@powR R ^~ r)).
Qed.

Section measurable_comparison.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> R).

Lemma measurable_fun_le D f g :
  d.-measurable D -> measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mD mf mg; under eq_set => x do rewrite -lee_fin.
by apply: measurable_lee => //; exact: measurableT_comp.
Qed.

End measurable_comparison.

Section lusin.
Hint Extern 0 (hausdorff_space _) => (exact: Rhausdorff) : core.
Local Open Scope ereal_scope.
Context (rT : realType) (A : set rT).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.
Hypothesis mA : measurable A.
Hypothesis finA : mu A < +oo.

Import HBSimple.

Let lusin_simple (f : {sfun R >-> rT}) (eps : rT) : (0 < eps)%R ->
  exists K, [/\ compact K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps]; have [N /card_fset_set rfN] := fimfunP f.
pose Af x : set R := A `&` f @^-1` [set x].
have mAf x : measurable (Af x) by exact: measurableI.
have finAf x : mu (Af x) < +oo.
  by rewrite (le_lt_trans _ finA)// le_measure// ?inE//; exact: subIsetl.
have eNpos : (0 < eps%:num / N.+1%:R)%R by [].
have dK' x := lebesgue_regularity_inner (mAf x) (finAf x) eNpos.
pose dK x : set R := projT1 (cid (dK' x)); pose J i : set R := Af i `\` dK i.
have dkP x := projT2 (cid (dK' x)).
have mdK i : measurable (dK i).
  by apply: closed_measurable; apply: compact_closed => //; case: (dkP i).
have mJ i : measurable (J i) by apply: measurableD => //; exact: measurableI.
have dKsub z : dK z `<=` f @^-1` [set z].
  by case: (dkP z) => _ /subset_trans + _; apply => ? [].
exists (\bigcup_(i in range f) dK i); split.
- by rewrite -bigsetU_fset_set//; apply: bigsetU_compact=>// i _; case: (dkP i).
- by move=> z [y _ dy]; have [_ /(_ _ dy) []] := dkP y.
- have -> : A `\` \bigcup_(i in range f) dK i = \bigcup_(i in range f) J i.
    rewrite -bigcupDr /= ?eqEsubset; last by exists (f point), point.
    split => z; first by move=> /(_ (f z)) [//| ? ?]; exists (f z).
    case => ? [? _ <-] [[zab /= <- nfz]] ? [r _ <-]; split => //.
    by move: nfz; apply: contra_not => /[dup] /dKsub ->.
  apply: (@le_lt_trans _ _ (\sum_(i \in range f) mu (J i))).
    by apply: content_sub_fsum => //; exact: fin_bigcup_measurable.
  apply: le_lt_trans.
    apply: (@lee_fsum _ _ _ _ (fun=> (eps%:num / N.+1%:R)%:E * 1%:E)) => //.
    by move=> i ?; rewrite mule1; apply: ltW; have [_ _] := dkP i.
  rewrite /=-ge0_mule_fsumr // -esum_fset // finite_card_sum // -EFinM lte_fin.
  by rewrite rfN -mulrA gtr_pMr // mulrC ltr_pdivrMr // mul1r ltr_nat.
- suff : closed (\bigcup_(i in range f) dK i) /\
    {within \bigcup_(i in range f) dK i, continuous f} by case.
  rewrite -bigsetU_fset_set //.
  apply: (@big_ind _ (fun U => closed U /\ {within U, continuous f})).
  + by split; [exact: closed0 | exact: continuous_subspace0].
  + by move=> ? ? [? ?][? ?]; split; [exact: closedU|exact: withinU_continuous].
  + move=> i _; split; first by apply: compact_closed; have [] := dkP i.
    apply: (continuous_subspaceW (dKsub i)).
    apply: (@subspace_eq_continuous _ _ _ (fun=> i)).
      by rewrite /from_subspace => ? /set_mem ->.
    by apply: continuous_subspaceT => ?; exact: cvg_cst.
Qed.

Let measurable_almost_continuous' (f : rT -> rT) (eps : rT) :
  (0 < eps)%R -> measurable_fun A f -> exists K,
  [/\ measurable K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps] mf; pose f' := EFin \o f.
have mf' : measurable_fun A f' by exact/measurable_EFinP.
have [/= g_ gf'] := @approximation_sfun _ R rT _ _ mA mf'.
pose e2n n := ((eps%:num / 2) / (2 ^ n.+1)%:R)%R.
have e2npos n : (0 < e2n n)%R by rewrite divr_gt0.
have gK' n := @lusin_simple (g_ n) (e2n n) (e2npos n).
pose gK n := projT1 (cid (gK' n)); have gKP n := projT2 (cid (gK' n)).
pose K := \bigcap_i gK i; have mgK n : measurable (gK n).
  by apply: closed_measurable; apply: compact_closed => //; have [] := gKP n.
have mK : measurable K by exact: bigcap_measurable.
have Kab : K `<=` A by move=> z /(_ O I); have [_ + _ _] := gKP O; apply.
have []// := @pointwise_almost_uniform _ rT R mu g_ f K (eps%:num / 2).
- by move=> n; apply: measurable_funTS.
- by rewrite (@le_lt_trans _ _ (mu A))// le_measure// ?inE.
- by move=> z Kz; have /fine_fcvg := gf' z (Kab _ Kz); rewrite -fmap_comp compA.
move=> D [/= mD Deps KDf]; exists (K `\` D); split => //.
- exact: measurableD.
- exact: subset_trans Kab.
- rewrite setDDr; apply: le_lt_trans => /=.
    by apply: measureU2 => //; apply: measurableI => //; apply: measurableC.
  rewrite [_%:num]splitr EFinD; apply: lee_ltD => //=; first 2 last.
  + by rewrite (@le_lt_trans _ _ (mu D)) ?le_measure ?inE//; exact: measurableI.
  + rewrite ge0_fin_numE// (@le_lt_trans _ _ (mu A))// le_measure ?inE//.
    exact: measurableD.
  rewrite setDE setC_bigcap setI_bigcupr.
  apply: (@le_trans _ _(\sum_(k <oo) mu (A `\` gK k))).
  apply: measure_sigma_subadditive => //; [|apply: bigcup_measurable => + _].
      by move=> k /=; apply: measurableD => //; apply: mgK.
    by move=> k /=; apply: measurableD => //; apply: mgK.
  apply: (@le_trans _ _(\sum_(k <oo) (e2n k)%:E)); last exact: epsilon_trick0.
  by apply: lee_nneseries => // k _; apply: ltW; have [] := gKP k.
apply: (@uniform_limit_continuous_subspace _ _ _ (g_ @ \oo)) => //.
near_simpl; apply: nearW => // n; apply: (@continuous_subspaceW _ _ _ (gK n)).
  by move=> z [+ _]; apply.
by have [] := projT2 (cid (gK' n)).
Qed.

Lemma measurable_almost_continuous (f : rT -> rT) (eps : rT) :
  (0 < eps)%R -> measurable_fun A f -> exists K,
  [/\ compact K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps] mf; have e2pos : (0 < eps%:num/2)%R by [].
have [K [mK KA ? ?]] := measurable_almost_continuous' e2pos mf.
have Kfin : mu K < +oo by rewrite (le_lt_trans _ finA)// le_measure ?inE.
have [D /= [cD DK KDe]] := lebesgue_regularity_inner mK Kfin e2pos.
exists D; split => //; last exact: (continuous_subspaceW DK).
  exact: (subset_trans DK).
have -> : A `\` D = (A `\` K) `|` (K `\` D).
  rewrite eqEsubset; split => z.
    by case: (pselect (K z)) => // ? [? ?]; [right | left].
  case; case=> az nz; split => //; [by move: z nz {az}; apply/subsetC|].
  exact: KA.
apply: le_lt_trans.
  apply: measureU2; apply: measurableD => //; apply: closed_measurable.
  by apply: compact_closed; first exact: Rhausdorff.
by rewrite [_ eps]splitr EFinD lteD.
Qed.

End lusin.
