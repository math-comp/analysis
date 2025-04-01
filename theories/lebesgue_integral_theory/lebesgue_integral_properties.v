(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference topology ereal tvs normedtype.
From mathcomp Require Import sequences real_interval function_spaces esum.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import simple_functions lebesgue_integral_definition.

(**md**************************************************************************)
(* # Basic Properties of the Lebesgue Integral                                *)
(*                                                                            *)
(* This file contains a formalization of the basic properties of the Lebesgue *)
(* integral: the approximation theorem, the monotone convergence theorem,     *)
(* Fatou's lemma, the linearity properties of the integral, etc.              *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* About the naming convention: Lemmas about the Lebesgue integral often      *)
(* appear in two flavors, depending on whether they are about non-negative    *)
(* functions or about integrable functions. Lemmas about non-negative         *)
(* functions are prefixed with `ge0_`, lemmas about integrable functions are  *)
(* not.                                                                       *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ````                                                                       *)
(*         dyadic_itv n k == the interval                                     *)
(*                           `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[           *)
(*             approx D f == nondecreasing sequence of functions that         *)
(*                           approximates f over D using dyadic intervals     *)
(*                           It uses the sets dyadic_approx and               *)
(*                           integer_approx.                                  *)
(*      nnsfun_approx D f == same as approx D f but as a nnsfun               *)
(*                           approximates f over D using dyadic intervals     *)
(*     mu.-integrable D f == f is measurable over D and the integral of f     *)
(*                           w.r.t. D is < +oo                                *)
(* ````                                                                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "mu .-integrable" (at level 2, format "mu .-integrable").

Section eq_measure_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (D : set T).
Implicit Types m : {measure set T -> \bar R}.

Import HBNNSimple.

Let eq_measure_integral0 m2 m1 (f : T -> \bar R) :
  (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  [set sintegral m1 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]] `<=`
  [set sintegral m2 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]].
Proof.
move=> m12 _ [h hfD <-] /=; exists h => //; apply: eq_fsbigr => r _.
have [hrD|hrD] := pselect (h @^-1` [set r] `<=` D); first by rewrite m12.
suff : r = 0%R by move=> ->; rewrite !mul0e.
apply: contra_notP hrD => /eqP r0 t/= htr.
have := hfD t.
rewrite /patch/=; case: ifPn; first by rewrite inE.
move=> tD.
move: r0; rewrite -htr => ht0.
by rewrite le_eqVlt eqe (negbTE ht0)/= lte_fin// ltNge// fun_ge0.
Qed.

Lemma eq_measure_integral m2 m1 (f : T -> \bar R) :
    (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  \int[m1]_(x in D) f x = \int[m2]_(x in D) f x.
Proof.
move=> m12; rewrite /integral funepos_restrict funeneg_restrict.
by congr (ereal_sup _ - ereal_sup _); rewrite eqEsubset; split;
  apply: eq_measure_integral0 => A /m12 // /[apply].
Qed.

End eq_measure_integral.
Arguments eq_measure_integral {d T R D} m2 {m1 f}.

Section integral_measure_zero.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Let sintegral_measure_zero (f : T -> R) : sintegral mzero f = 0.
Proof. by rewrite sintegralE big1// => r _ /=; rewrite /mzero mule0. Qed.

Import HBNNSimple.

Lemma integral_measure_zero (D : set T) (f : T -> \bar R) :
  \int[mzero]_(x in D) f x = 0.
Proof.
have h g : (forall x, 0 <= g x) -> [set sintegral mzero h |
    h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= g x]] = [set 0].
  move=> g0; apply/seteqP; split => [_ [h/= Dt <-]|x -> /=].
    by rewrite sintegral_measure_zero.
  by exists (cst_nnsfun _ (@NngNum _ 0 (lexx _))).
rewrite integralE !ge0_integralE//= h ?ereal_sup1; last first.
  by move=> r; rewrite erestrict_ge0.
by rewrite h ?ereal_sup1 ?subee// => r; rewrite erestrict_ge0.
Qed.

End integral_measure_zero.

Section domain_change.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma integral_mkcond D f : \int[mu]_(x in D) f x = \int[mu]_x (f \_ D) x.
Proof. by rewrite /integral patch_setT. Qed.

Import HBNNSimple.

Lemma integralT_nnsfun (h : {nnsfun T >-> R}) :
  \int[mu]_x (h x)%:E = sintegral mu h.
Proof. by rewrite integral_nnsfun// patch_setT. Qed.

Lemma integral_mkcondr D P f :
  \int[mu]_(x in D `&` P) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite integral_mkcond [RHS]integral_mkcond patch_setI. Qed.

Lemma integral_mkcondl D P f :
  \int[mu]_(x in P `&` D) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite setIC integral_mkcondr. Qed.

End domain_change.
Arguments integral_mkcond {d T R mu} D f.

Lemma integral_set0 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : T -> \bar R) :
  (\int[mu]_(x in set0) f x = 0)%E.
Proof.
rewrite integral_mkcond integral0_eq// => x _.
by rewrite /restrict; case: ifPn => //; rewrite in_set0.
Qed.

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R)
          (g : {nnsfun T >-> R}^nat).
Hypothesis f0 : forall x, 0 <= f x.
Hypothesis mf : measurable_fun setT f.

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~x).
Hypothesis gf : forall x, EFin \o g^~ x @ \oo --> f x.
Local Open Scope ereal_scope.

Lemma nd_ge0_integral_lim : \int[mu]_x f x = limn (sintegral mu \o g).
Proof.
rewrite ge0_integralTE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: lime_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ubound; exists (g n) => //= => x.
  have <- : limn (EFin \o g ^~ x) = f x by exact/cvg_lim/gf.
  have : EFin \o g ^~ x @ \oo --> ereal_sup (range (EFin \o g ^~ x)).
    by apply: ereal_nondecreasing_cvgn => p q pq /=; rewrite lee_fin; exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ubound; exists n.
have := leey (\int[mu]_x (f x)).
rewrite [in X in X -> _]le_eqVlt => /predU1P[|] mufoo; last first.
  have : \int[mu]_x (f x) \is a fin_num by rewrite ge0_fin_numE// integral_ge0.
  rewrite ge0_integralTE// => /ub_ereal_sup_adherent h.
  apply/lee_addgt0Pr => _/posnumP[e].
  have {h} [/= _ [G Gf <-]] := h _ [gt0 of e%:num].
  rewrite EFinN lteBlDr// => fGe.
  have : forall x, cvgn (g^~ x) -> (G x <= limn (g ^~ x))%R.
    move=> x cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _))// gxfx.
  move=> /(nd_sintegral_lim_lemma mu nd_g)/(leeD2r e%:num%:E).
  exact/le_trans/ltW.
suff : limn (sintegral mu \o g) = +oo.
  by move=> ->; rewrite -ge0_integralTE// mufoo.
apply/eqyP => r r0.
have [G [Gf rG]] : exists h : {nnsfun T >-> R},
    (forall x, (h x)%:E <= f x) /\ (r%:E <= sintegral mu h).
  have : r%:E < \int[mu]_x (f x).
    move: (mufoo) => /eqyP/(_ _ (addr_gt0 r0 r0)).
    by apply: lt_le_trans => //; rewrite lte_fin ltrDr.
  rewrite ge0_integralTE// => /ereal_sup_gt[x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, cvgn (g^~ x) -> (G x <= limn (g^~ x))%R.
  move=> x cg; rewrite -lee_fin -(EFin_lim cg).
  by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _)) // gxfx.
by move/(nd_sintegral_lim_lemma mu nd_g) => Gg; rewrite (le_trans rG).
Unshelve. all: by end_near. Qed.

End nondecreasing_integral_limit.

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
rewrite -bigcup_seq /=; exists (trunc (r * 2 ^+ n.+1)).
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
have K : (trunc (fine (f x) * 2 ^+ n) < n * 2 ^ n)%N.
  rewrite truncn_lt_nat; last by rewrite mulr_ge0// ltW.
  by rewrite natrM natrX ltr_pM2r// -lte_fin (fineK fxfin).
have /[!mem_index_enum]/(_ isT) := An0 (Ordinal K).
rewrite implyTb indicE mem_set ?mulr1; last first.
  rewrite /A K /= inE; split=> //=; exists (fine (f x)); last by rewrite fineK.
  by rewrite in_itv/= ler_pdivrMr// ltr_pdivlMr// trunc_itv// mulr_ge0// ltW.
apply/negP; rewrite mulf_eq0 -exprVn negb_or expf_neq0//= andbT.
rewrite pnatr_eq0 -lt0n trunc_gt0 -ler_pdivrMr// ltW//; near: n.
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
  near: n; exists (trunc (fine (f x))).+2 => //= p /= fxp.
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
move=> /(_ ((trunc l).+2 + n) (leq_addl _ _)); apply/negP.
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
rewrite -(@fineK _ (f x)); first exact: (cvg_comp (cvg_approx f0 Dx fxoo)).
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

Section ge0_linearityZ.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> \bar R.
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.

Import HBNNSimple.

Lemma ge0_integralZl_EFin k : (0 <= k)%R ->
  \int[mu]_(x in D) (k%:E * f1 x) = k%:E * \int[mu]_(x in D) f1 x.
Proof.
rewrite integral_mkcond erestrict_scale [in RHS]integral_mkcond => k0.
set h1 := f1 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
pose g := nnsfun_approx measurableT mh1.
pose kg := fun n => scale_nnsfun (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ _ mu (fun x => k%:E * h1 x) kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu (scale_nnsfun (g n) k0))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (g n))).
    rewrite limeMl //; last first.
      by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx.
    by rewrite -(nd_ge0_integral_lim mu h10)// => [x m n mn|x];
      [exact/lefP/nd_nnsfun_approx|exact: cvg_nnsfun_approx].
  by under eq_fun do rewrite (sintegralrM mu k (g _)).
- by move=> t; rewrite mule_ge0.
- by move=> x m n mn; rewrite /kg ler_pM//; exact/lefP/nd_nnsfun_approx.
- move=> x.
  rewrite [X in X @ \oo --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
  exact/cvgeMl/cvg_nnsfun_approx.
Qed.

End ge0_linearityZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `ge0_integralZl_EFin` instead")]
Notation ge0_integralM_EFin := ge0_integralZl_EFin (only parsing).

Section ge0_linearityD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Import HBNNSimple.

Lemma ge0_integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
rewrite !(integral_mkcond D) erestrictD.
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
pose g1 := nnsfun_approx measurableT mh1.
pose g2 := nnsfun_approx measurableT mh2.
pose g12 := fun n => add_nnsfun (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ _ mu _ g12); last 3 first.
  - by move=> x; rewrite adde_ge0.
  - by apply: nondecreasing_seqD => // x m n mn;
      [exact/lefP/nd_nnsfun_approx|exact/lefP/nd_nnsfun_approx].
  - move=> x; rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E))//.
    apply: cvgeD => //; [|exact: cvg_nnsfun_approx..].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: h10|exact: h20].
under [_ \o _]eq_fun do rewrite sintegralD.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g2)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite limeD//; [
  by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx..|].
by rewrite ge0_adde_def => //; rewrite inE; apply: lime_ge; solve[
  (by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx) ||
  (by apply: nearW => n; exact: sintegral_ge0)].
Qed.

Lemma ge0_le_integral : (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> f12; rewrite !(integral_mkcond D).
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
have h12 x : h1 x <= h2 x by apply: lee_restrict.
pose g1 := nnsfun_approx measurableT mh1.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact: cvg_nnsfun_approx.
apply: lime_le.
  by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_nnsfun_approx.
near=> n; rewrite ge0_integralTE//; apply: ereal_sup_ubound => /=.
exists (g1 n) => // t; rewrite (le_trans _ (h12 _))//.
have := leey (h1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite leey.
have h1tfin : h1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (h10 t)).
have /= := @cvg_nnsfun_approx _ _ _ _ measurableT _ mh1 (fun x _ => h10 x) t Logic.I.
rewrite -(fineK h1tfin) => /fine_cvgP[ft_near].
set u_ := (X in X --> _) => u_h1.
have <- : lim u_ = fine (h1 t) by exact/cvg_lim.
rewrite lee_fin; apply: nondecreasing_cvgn_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_nnsfun_approx.
by apply/cvg_ex; eexists; exact: u_h1.
Unshelve. all: by end_near. Qed.

End ge0_linearityD.

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
      by move=> ? /set_mem ->.
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
pose e2n n := (eps%:num / 2) / (2 ^ n.+1)%:R.
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

Section emeasurable_fun.
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
   apply/predeqP=> x; rewrite /preimage/= /mule_def !(negb_and, negb_or).
   rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP).
   rewrite !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
   rewrite eqe_absl leey andbT (orbC (g x == +oo)).
   by rewrite eqe_absl leey andbT (orbC (f x == +oo)).
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

End emeasurable_fun.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_sum`")]
Notation emeasurable_fun_sum := emeasurable_sum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_fsum`")]
Notation emeasurable_fun_fsum := emeasurable_fsum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `ge0_emeasurable_sum`")]
Notation ge0_emeasurable_fun_sum := ge0_emeasurable_sum (only parsing).

Section emeasurable_fun_cmp.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variables (D : set T) (mD : measurable D).
Implicit Types f g : T -> \bar R.

Lemma emeasurable_fun_lt f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x < g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_gt0.
by apply: emeasurable_fun_o_infty => //; exact: emeasurable_funB.
Qed.

Lemma emeasurable_fun_le f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_le0.
by apply: emeasurable_fun_infty_c => //; exact: emeasurable_funB.
Qed.

Lemma emeasurable_fun_eq f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x = g x]).
Proof.
move=> mf mg; rewrite set_eq_le setIIr.
by apply: measurableI; apply: emeasurable_fun_le.
Qed.

Lemma emeasurable_fun_neq f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x != g x]).
Proof.
move=> mf mg; rewrite set_neq_lt setIUr.
by apply: measurableU; exact: emeasurable_fun_lt.
Qed.

End emeasurable_fun_cmp.

Section measurable_fun.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> R).

Lemma measurable_sum D I s (h : I -> (T -> R)) :
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
move=> mh; apply/measurable_EFinP.
rewrite (_ : _ \o _ = (fun t => \sum_(i <- s) (h i t)%:E)); last first.
  by apply/funext => t/=; rewrite -sumEFin.
by apply/emeasurable_sum => i; exact/measurable_EFinP.
Qed.

Lemma measurable_fun_le D f g :
  d.-measurable D -> measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mD mf mg; under eq_set => x do rewrite -lee_fin.
by apply: emeasurable_fun_le => //; exact: measurableT_comp.
Qed.

End measurable_fun.

Section ge0_integral_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_sum (s : seq I) :
  \int[mu]_(x in D) (\sum_(k <- s) f k x) =
  \sum_(k <- s) \int[mu]_(x in D) (f k x).
Proof.
elim: s => [|h t ih].
  by (under eq_fun do rewrite big_nil); rewrite big_nil integral0.
rewrite big_cons /= -ih -ge0_integralD//.
- by apply: eq_integral => x Dx; rewrite big_cons.
- by move=> *; exact: f0.
- by move=> *; apply: sume_ge0 => // k _; exact: f0.
- exact: emeasurable_sum.
Qed.

End ge0_integral_sum.

Section ge0_integral_fsum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : choiceType) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_fsum (A : set I) : finite_set A ->
  \int[mu]_(x in D) (\sum_(k \in A) f k x) =
  \sum_(k \in A) \int[mu]_(x in D) f k x.
Proof.
move=> fs; rewrite fsbig_finite//= -ge0_integral_sum//.
by apply: eq_integral => x xD; rewrite fsbig_finite.
Qed.

End ge0_integral_fsum.

Section monotone_convergence_theorem.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g' : (T -> \bar R)^nat).
Hypothesis mg' : forall n, measurable_fun D (g' n).
Hypothesis g'0 : forall n x, D x -> 0 <= g' n x.
Hypothesis nd_g' : forall x, D x -> nondecreasing_seq (g'^~ x).
Let f' := fun x => limn (g'^~ x).

Let g n := (g' n \_ D).

Let g0 n x : 0 <= g n x. Proof. exact/erestrict_ge0/g'0. Qed.

Let mg n : measurable_fun setT (g n).
Proof. exact/(measurable_restrictT _ _).1. Qed.

Let nd_g x : nondecreasing_seq (g^~ x).
Proof.
by move=> m n mn; rewrite /g/patch; case: ifP => // /set_mem /nd_g' ->.
Qed.

Let f := fun x => limn (g^~ x).

Let is_cvg_g t : cvgn (g^~ t).
Proof.
by move=> ?; apply: ereal_nondecreasing_is_cvgn => m n ?; exact/nd_g.
Qed.

Local Definition g2' n : (T -> R)^nat := approx setT (g n).
Local Definition g2 n : {nnsfun T >-> R}^nat := nnsfun_approx measurableT (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : {nnsfun T >-> R}^nat :=
  fun k => bigmax_nnsfun (g2^~ k) k.

Import HBNNSimple.

Let is_cvg_g2 n t : cvgn (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvgn => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Let nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!bigmax_nnsfunE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax2 => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
   by rewrite !nnsfun_approxE; exact/lefP/nd_approx.
rewrite (bigmaxD1 ord_max)// le_max; apply/orP; right.
rewrite [leRHS](eq_bigl (fun i => nat_of_ord i < n)%N).
  by rewrite (big_ord_narrow (leqnSn n)).
move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Let is_cvg_max_g2 t : cvgn (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvgn => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Let max_g2_g k x : ((max_g2 k x)%:E <= g k x)%O.
Proof.
rewrite bigmax_nnsfunE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  by apply/bigmax_leP; split => //; apply: g0D.
rewrite (big_morph _ (@EFin_max R) erefl) //.
apply: le_bigmax2 => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx _ _ _)) => //; exact/nd_g/ltnW.
Qed.

Let lim_max_g2_f t : limn (EFin \o max_g2 ^~ t) <= f t.
Proof. by apply: lee_lim => //=; near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Let lim_g2_max_g2 t n : limn (EFin \o g2 n ^~ t) <= limn (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //.
near=> k; rewrite /= bigmax_nnsfunE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (bigmax_sup (Ordinal nk)).
Unshelve. all: by end_near. Qed.

Let cvg_max_g2_f t : EFin \o max_g2 ^~ t @ \oo --> f t.
Proof.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f _)) // (cvg_lim _ g_l).
have := leey l; rewrite [in X in X -> _]le_eqVlt => /predU1P[->|loo].
  by rewrite leey.
rewrite -(cvg_lim _ g_l) //= lime_le => //.
near=> n.
have := leey (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
  have h := @dvg_approx _ _ _ setT _ t Logic.I fntoo.
  have g2oo : limn (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/cvgeryP.
    under [in X in X --> _]eq_fun do rewrite nnsfun_approxE.
    have : {homo (approx setT (g n))^~ t : n0 m / (n0 <= m)%N >-> (n0 <= m)%R}.
      exact/lef_at/nd_approx.
    by move/nondecreasing_dvgn_lt => /(_ h).
  have -> : limn (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo leye_eq => /eqP.
  by rewrite leey.
- have approx_g_g := @cvg_approx _ _ _ setT _ t (fun t _ => g0 n t) Logic.I fntoo.
  suff : limn (EFin \o g2 n ^~ t) = g n t.
    by move=> <-; exact: (le_trans _ (lim_g2_max_g2 t n)).
  have /cvg_lim <- // : EFin \o (approx setT (g n)) ^~ t @ \oo --> g n t.
    move/cvg_comp : approx_g_g; apply.
    by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
  rewrite (_ : _ \o _ = EFin \o approx setT (g n) ^~ t)// funeqE => m.
  by rewrite [in RHS]/= -nnsfun_approxE.
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int[mu]_(x in D) (f' x) = limn (fun n => \int[mu]_(x in D) (g' n x)).
Proof.
rewrite integral_mkcond.
under [in RHS]eq_fun do rewrite integral_mkcond -/(g _).
have -> : f' \_ D = f.
  apply/funext => x; rewrite /f /f' /g /patch /=; case: ifPn => //=.
  by rewrite lim_cst.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => \int[mu]_x g n x).
    move=> m n mn; apply: ge0_le_integral => //.
    by move=> *; exact: nd_g.
  have ub n : \int[mu]_x g n x <= \int[mu]_x f x.
    apply: ge0_le_integral => //.
    - move=> x _; apply: lime_ge => //.
      by apply: nearW => k; exact/g0.
    - apply: emeasurable_fun_cvg mg _ => x _.
      exact: ereal_nondecreasing_is_cvgn.
    - move=> x Dx; apply: lime_ge => //.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: lime_le => //; [exact:ereal_nondecreasing_is_cvgn|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ _ mu _ max_g2) //; last 2 first.
  - move=> t; apply: lime_ge => //.
    by apply: nearW => n; exact: g0.
  - by move=> t m n mn; exact/lefP/nd_max_g2.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvgn => // n m nm; apply: ge0_le_integral => //.
  by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralTE//.
  by apply: ereal_sup_ubound; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  \int[mu]_(x in D) g' n x @[n \oo] --> \int[mu]_(x in D) f' x.
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvgn => m n mn.
by apply: ge0_le_integral => // t Dt; [exact: g'0|exact: g'0|exact: nd_g'].
Qed.

End monotone_convergence_theorem.

Section integral_nneseries.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma integral_nneseries : \int[mu]_(x in D) (\sum_(n <oo) f n x) =
                           \sum_(n <oo) (\int[mu]_(x in D) (f n x)).
Proof.
rewrite monotone_convergence //.
- by rewrite -lim_mkord; under eq_fun do rewrite ge0_integral_sum// big_mkord.
- by move=> n; exact: emeasurable_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_nneseries.

(**md Generalization of `ge0_integralZl_EFin` to a constant potentially $+\infty$
   using the monotone convergence theorem: *)
Section ge0_integralZ.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.
Implicit Type k : \bar R.

Lemma ge0_integralZl k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (k * f x) = k * \int[mu]_(x in D) (f x).
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralZl_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by apply: measurable_funeM.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g ^~ x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => limn (g^~ x).
transitivity (\int[mu]_(x in D) limn (g^~ x)).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0 (f x).
  - rewrite gt0_mulye//; apply/cvgeyPgey; near=> M.
    have M0 : (0 <= M)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|_|//]; last first.
      by exists 1%N => // m /= m0; rewrite mulry gtr0_sg// ?ltr0n// mul1e leey.
    near=> n; rewrite lee_fin -ler_pdivrMr//.
    near: n; exists (trunc (M / r)).+1 => // m /= Mrm.
    by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
  - rewrite lt0_mulye//; apply/cvgeNyPleNy; near=> M;
    have M0 : (M <= 0)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|//|_]; last first.
      by exists 1%N => // m /= m0; rewrite mulrNy gtr0_sg// ?ltr0n// mul1e leNye.
    near=> n; rewrite lee_fin -ler_ndivrMr//.
    near: n; exists (trunc (M / r)).+1 => // m /= Mrm.
    by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
  - rewrite -fx0 mule0 /g -fx0.
    under eq_fun do rewrite mule0/=. (*TODO: notation broken*)
    exact: cvg_cst.
rewrite (monotone_convergence mu mD mg g0 nd_g).
under eq_fun do rewrite /g ge0_integralZl_EFin//.
have : 0 <= \int[mu]_(x in D) f x by exact: integral_ge0.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  by rewrite mule0; under eq_fun do rewrite mule0; rewrite lim_cst.
rewrite gt0_mulye//; apply/cvg_lim => //; apply/cvgeyPgey; near=> M.
have M0 : (0 <= M)%R by [].
near=> n; have [ifoo|] := ltP (\int[mu]_(x in D) f x) +oo; last first.
  rewrite leye_eq => /eqP ->; rewrite mulry muleC gt0_mulye ?leey//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (\int[mu]_(x in D) f x)); last first.
  by rewrite fin_numElt ifoo (le_lt_trans _ if_gt0).
rewrite -lee_pdivrMr//; last first.
  by move: if_gt0 ifoo; case: (\int[mu]_(x in D) f x).
near: n.
exists (trunc (M * (fine (\int[mu]_(x in D) f x))^-1)).+1 => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
by rewrite lee_fin ltW// truncnS_gt.
Unshelve. all: by end_near. Qed.

Lemma ge0_integralZr k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (f x * k) = \int[mu]_(x in D) (f x) * k.
Proof.
move=> f0 k0; under eq_integral do rewrite muleC.
by rewrite ge0_integralZl// muleC.
Qed.

End ge0_integralZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `ge0_integralZl` instead")]
Notation ge0_integralM := ge0_integralZl (only parsing).

Section integral_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Implicit Type A : set T.

Import HBNNSimple.

Lemma integral_indic A : measurable A ->
  \int[mu]_(x in D) (\1_A x)%:E = mu (A `&` D).
Proof.
move=> mA; rewrite (_ : \1_A = indic_nnsfun R mA)// integral_nnsfun//=.
by rewrite restrict_indic sintegral_indic//; exact: measurableI.
Qed.

End integral_indic.

Section integralZl_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralZl_indic (f : R -> set T) (k : R) :
    ((k < 0)%R -> f k = set0) -> measurable (f k) ->
  \int[m]_(x in D) (k * \1_(f k) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f k) x)%:E.
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite integral0_eq//; last by move=> x _; rewrite fk0// indic0 mulr0.
  by rewrite integral0_eq ?mule0// => x _; rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl//; exact/measurable_EFinP.
Qed.

Import HBNNSimple.

Lemma integralZl_indic_nnsfun (f : {nnsfun T >-> R}) (k : R) :
  \int[m]_(x in D) (k * \1_(f @^-1` [set k]) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f @^-1` [set k]) x)%:E.
Proof.
rewrite (@integralZl_indic (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

End integralZl_indic.
Arguments integralZl_indic {d T R m D} mD f.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl_indic` instead")]
Notation integralM_indic := integralZl_indic (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl_indic_nnsfun` instead")]
Notation integralM_indic_nnsfun := integralZl_indic_nnsfun (only parsing).

Section integral_mscale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (k : {nonneg R}) (f : T -> \bar R).

Let integral_mscale_indic E : measurable E ->
  \int[mscale k m]_(x in D) (\1_E x)%:E =
  k%:num%:E * \int[m]_(x in D) (\1_E x)%:E.
Proof. by move=> ?; rewrite !integral_indic. Qed.

Import HBNNSimple.

Let integral_mscale_nnsfun (h : {nnsfun T >-> R}) :
  \int[mscale k m]_(x in D) (h x)%:E = k%:num%:E * \int[m]_(x in D) (h x)%:E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralZl//; last 2 first.
  - by apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> x _; rewrite lee_fin.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/measurable_EFinP; do 2 apply/measurableT_comp => //.
  - by move=> n x _; rewrite EFinM mule_ge0// nnfun_muleindic_ge0.
apply: eq_fsbigr => r _; rewrite ge0_integralZl//.
- by rewrite !integralZl_indic_nnsfun//= integral_mscale_indic// muleCA.
- exact/measurable_EFinP/measurableT_comp.
- by move=> t _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma ge0_integral_mscale (mf : measurable_fun D f) :
    (forall x, D x -> 0 <= f x) ->
  \int[mscale k m]_(x in D) f x = k%:num%:E * \int[m]_(x in D) f x.
Proof.
move=> f0; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[mscale k m]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //=; exact: cvg_nnsfun_approx.
  - by move=> n; apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite (_ : \int[m]_(x in D) _ =
    limn (fun n => \int[m]_(x in D) (f_ n x)%:E)); last first.
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite -limeMl//.
  by congr (limn _); apply/funext => n /=; rewrite integral_mscale_nnsfun.
apply/ereal_nondecreasing_is_cvgn => a b ab; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> x _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

End integral_mscale.

Section fatou.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : (T -> \bar R)^nat).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int[mu]_(x in D) limn_einf (f^~ x) <=
              limn_einf (fun n => \int[mu]_(x in D) f n x).
Proof.
pose g n := fun x => einfs (f ^~ x) n.
have mg := measurable_fun_einfs mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
under eq_integral do rewrite limn_einf_lim.
rewrite limn_einf_lim monotone_convergence //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: ge0_le_integral => //; [exact: g0| exact: mg| exact: g0| exact: mg|].
  move=> x Dx; apply: le_ereal_inf => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N ->
      \int[mu]_(x in D) g n x <= einfs (fun k => \int[mu]_(x in D) f k x) n.
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: ge0_le_integral => //; [exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lbound; exists k.
  exact.
Qed.

End fatou.

Section integralN.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integralN D (f : T -> \bar R) :
  \int[mu]_(x in D) f^\+ x +? (- \int[mu]_(x in D) f^\- x) ->
  \int[mu]_(x in D) - f x = - \int[mu]_(x in D) f x.
Proof.
have [f_fin _|] := boolP (\int[mu]_(x in D) f^\- x \is a fin_num).
  rewrite integralE// [in RHS]integralE// fin_num_oppeD ?fin_numN// oppeK addeC.
  by rewrite funenegN funeposN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -leeNy_eq; apply/negP.
  by rewrite -ltNge (lt_le_trans _ (integral_ge0 _ _)).
rewrite nfoo adde_defEninfty -leye_eq -ltNge ltey_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE [in RHS]integralE funeposN nfoo [in RHS]addeC/= funenegN.
  by rewrite addye// eqe_oppLR/= (andP (eqbLR (fin_numE _) f_fin)).2.
by rewrite integralE// [in RHS]integralE// funeposN funenegN nfoo pfoo.
Qed.

Lemma integral_ge0N (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) - f x = - \int[mu]_(x in D) f x.
Proof.
move=> f0; rewrite integralN // (eq_integral _ _ (ge0_funenegE _))// integral0.
by rewrite oppe0 fin_num_adde_defl.
Qed.

End integralN.

Section integral_cst.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Variables (f : T -> \bar R) (D : set T) (mD : measurable D).

Lemma sintegral_EFin_cst (x : {nonneg R}) :
  sintegral mu (cst x%:num \_ D) = x%:num%:E * mu D.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; x%:num])/=.
- have [->|x0] := eqVneq x%:num 0%R; first by rewrite setUid fsbig_set1 !mul0e.
  rewrite fsbigU0//=; last by move=> y [->]/esym; apply/eqP.
  rewrite !fsbig_set1 mul0e add0e preimage_restrict//.
  by rewrite ifN ?set0U ?setIidl//= notin_setE => /esym; exact/eqP.
- by move=> y [t _ <-] /=; rewrite /patch; case: ifPn; [right|left].
- by move=> y [_ /=/preimage10->]; rewrite measure0 mule0.
Qed.

Import HBNNSimple.

Local Lemma integral_cstr r : \int[mu]_(x in D) r%:E = r%:E * mu D.
Proof.
wlog r0 : r / (0 <= r)%R.
  move=> h; have [|r0] := leP 0%R r; first exact: h.
  rewrite -[in RHS](opprK r) EFinN mulNe -h ?oppr_ge0; last exact: ltW.
  rewrite -integral_ge0N//; last by move=> t ?; rewrite /= lee_fin oppr_ge0 ltW.
  by under [RHS]eq_integral do rewrite /= opprK.
rewrite (eq_integral (EFin \o cst_nnsfun T (NngNum r0)))//.
by rewrite integral_nnsfun// sintegral_EFin_cst.
Qed.

Local Lemma integral_csty : mu D != 0 -> \int[mu]_(x in D) (cst +oo) x = +oo.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => limn (g^~ t)) = cst +oo.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/cvgeryP/cvgryPge => M; exists (trunc M).+1 => //= m/= Mn.
  by rewrite (le_trans (ltW (truncnS_gt _)))// ler_nat.
rewrite monotone_convergence //.
- under [in LHS]eq_fun do rewrite integral_cstr.
  apply/cvg_lim => //; apply/cvgeyPge => M.
  have [muDoo|muDoo] := ltP (mu D) +oo; last first.
    exists 1%N => // m /= m0; move: muDoo; rewrite leye_eq => /eqP ->.
    by rewrite mulry gtr0_sg ?mul1e ?leey// ltr0n.
  exists (trunc (M / fine (mu D))).+1 => // m /=.
  rewrite -lez_nat => MDm; rewrite -(@fineK _ (mu D)) ?ge0_fin_numE//.
  rewrite -lee_pdivrMr; last by rewrite fine_gt0// lt0e muD0 measure_ge0.
  by rewrite lee_fin (le_trans (ltW (truncnS_gt _)))// ler_nat.
- by move=> n; exact: measurable_cst.
- by move=> n x Dx; rewrite lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.

Local Lemma integral_cstNy : mu D != 0 -> \int[mu]_(x in D) (cst -oo) x = -oo.
Proof.
by move=> ?; rewrite (eq_integral (\- cst +oo)) ?integral_ge0N/= ?integral_csty.
Qed.

End integral_cst.

Section ge0_transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (mu : {measure set X -> \bar R}).
Let mphi_mixin := isMeasurableFun.Build _ _ _ _ _ mphi.
Let mphi_pack : {mfun _ >-> _} := HB.pack phi mphi_mixin.

Import HBNNSimple.

Lemma ge0_integral_pushforward D (f : Y -> \bar R) :
  measurable D -> measurable_fun D f -> {in D, forall y, 0 <= f y} ->
  \int[pushforward mu mphi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD mf f0.
have mphiD : measurable (phi @^-1` D).
  by rewrite -(setTI (_ @^-1` _)); exact: (measurable_funP mphi_pack).
pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[pushforward mu mphi]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - apply: eq_integral => y /[!inE] yD; apply/esym/cvg_lim => //.
    by apply: cvg_nnsfun_approx=> // *; apply: f0; rewrite inE.
  - by move=> n; exact/measurable_EFinP/measurable_funP.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite [X in limn X](_ : _ =
    (fun n => \int[mu]_(x in phi @^-1` D) (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; do 2 apply: measurableT_comp=> //.
      exact: (measurable_funP mphi_pack).
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  apply: eq_integral => x /[!inE] phiDx /=; apply/cvg_lim => //.
  by apply: cvg_nnsfun_approx=> // y Dy; apply: f0; rewrite inE.
apply/funext => n.
have mfnphi r : measurable (f_ n @^-1` [set r] \o phi).
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k \in range (f_ n))
    \int[mu]_(x in phi @^-1` D) (k * \1_((f_ n @^-1` [set k]) \o phi) x)%:E).
  under eq_integral do rewrite fimfunE -fsumEFin//.
  rewrite ge0_integral_fsum//; last 2 first.
  - by move=> y; exact/measurable_EFinP/measurable_funM.
  - by move=> y x _; rewrite nnfun_muleindic_ge0.
  apply: eq_fsbigr => r _; rewrite integralZl_indic_nnsfun// integral_indic//=.
  rewrite (integralZl_indic _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _); rewrite [RHS]integral_indic.
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_fsum//.
- by apply: eq_integral => x _; rewrite fsumEFin// -fimfunE.
- by move=> r; exact/measurable_EFinP/measurable_funM.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

End ge0_transfer.

Section integral_dirac.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (a : T) (R : realType).
Variables (D : set T) (mD : measurable D).

Import HBNNSimple.

Let ge0_integral_dirac (f : T -> \bar R) (mf : measurable_fun D f)
    (f0 : forall x, D x -> 0 <= f x) :
  D a -> \int[\d_a]_(x in D) (f x) = f a.
Proof.
move=> Da; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[\d_ a]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => x /set_mem Dx; apply/esym/cvg_lim => //; apply: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
apply/funext => n.
under eq_integral do rewrite fimfunE// -fsumEFin//.
rewrite ge0_integral_fsum//.
- under eq_fsbigr do rewrite integralZl_indic_nnsfun//.
  rewrite /= (fsbigD1 (f_ n a))//=; last by exists a.
  rewrite integral_indic//= diracE mem_set// mule1.
  rewrite fsbig1 ?adde0// => r /= [_ rfna].
  rewrite integral_indic//= diracE memNset ?mule0//=.
  by apply/not_andP; left; exact/nesym.
- by move=> r; exact/measurable_EFinP/measurableT_comp.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma integral_dirac (f : T -> \bar R) (mf : measurable_fun D f) :
  \int[\d_ a]_(x in D) f x = \d_a D * f a.
Proof.
have [/[!inE] aD|aD] := boolP (a \in D).
  rewrite integralE ge0_integral_dirac//; last exact/measurable_funepos.
  rewrite ge0_integral_dirac//; last exact/measurable_funeneg.
  by rewrite [in RHS](funeposneg f) diracE mem_set// mul1e.
rewrite diracE (negbTE aD) mul0e -(integral_measure_zero D f)//.
apply: eq_measure_integral => //= S mS DS; rewrite /dirac indicE memNset//.
by move=> /DS/mem_set; exact/negP.
Qed.

End integral_dirac.

Section integral_measure_sum_nnsfun.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m_ : {measure set T -> \bar R}^nat) (N : nat).
Let m := msum m_ N.

Let integral_measure_sum_indic (E D : set T) (mE : measurable E)
    (mD : measurable D) :
  \int[m]_(x in E) (\1_D x)%:E = \sum_(n < N) \int[m_ n]_(x in E) (\1_D x)%:E.
Proof.
rewrite integral_indic//= /msum/=; apply: eq_bigr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Let integralT_measure_sum (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n < N) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n < N) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_sum_indic//.
  by rewrite ge0_sume_distrr// => n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= exchange_big/=; apply: eq_bigr => i _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

Lemma integral_measure_sum_nnsfun (D : set T) (mD : measurable D)
  (f : {nnsfun T >-> R}) :
  \int[m]_(x in D) (f x)%:E = \sum_(n < N) \int[m_ n]_(x in D) (f x)%:E.
Proof.
rewrite integral_mkcond.
transitivity (\int[m]_x (proj_nnsfun f mD x)%:E).
  by apply: eq_integral => t _ /=; rewrite /patch mindicE;
    case: ifPn => // tD; rewrite ?mulr1 ?mulr0.
rewrite integralT_measure_sum; apply: eq_bigr => i _.
rewrite [RHS]integral_mkcond; apply: eq_integral => t _.
rewrite /= /patch /mindic indicE.
by case: (boolP (t \in D)) => tD; rewrite ?mulr1 ?mulr0.
Qed.

End integral_measure_sum_nnsfun.

Section integral_measure_add_nnsfun.
Import HBNNSimple.

Lemma integral_measure_add_nnsfun d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  (\int[measure_add m1 m2]_(x in D) (f x)%:E =
   \int[m1]_(x in D) (f x)%:E + \int[m2]_(x in D) (f x)%:E)%E.
Proof.
rewrite /measureD integral_measure_sum_nnsfun// 2!big_ord_recl/= big_ord0.
by rewrite adde0.
Qed.

End integral_measure_add_nnsfun.

Section integral_mfun_measure_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.

Import HBNNSimple.

Lemma ge0_integral_measure_sum (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
    (forall x, D x -> 0 <= f x) -> measurable_fun D f -> forall N,
  \int[msum m_ N]_(x in D) f x = \sum_(n < N) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf; pose f_ := nnsfun_approx mD mf.
elim => [|N ih]; first by rewrite big_ord0 msum_mzero integral_measure_zero.
rewrite big_ord_recr/= -ih.
rewrite (_ : _ m_ N.+1 = measure_add (msum m_ N) (m_ N)); last first.
  by apply/funext => A; rewrite measure_addE /msum/= big_ord_recr.
have mf_ n : measurable_fun D (fun x => (f_ n x)%:E).
  exact/measurable_funTS/measurable_EFinP.
have f_ge0 n x : D x -> 0 <= (f_ n x)%:E by move=> Dx; rewrite lee_fin.
have cvg_f_ (m : {measure set T -> \bar R}) :
    cvgn (fun x => \int[m]_(x0 in D) (f_ x x0)%:E).
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: ge0_le_integral => //; [exact: f_ge0|exact: f_ge0|].
  by move=> t Dt; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n =>
    \int[measure_add (msum m_ N) (m_ N)]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//; last first.
    by move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => t /[!inE] Dt; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n =>
  \int[msum m_ N]_(x in D) (f_ n x)%:E + \int[m_ N]_(x in D) (f_ n x)%:E)).
  by congr (limn _); apply/funext => n; by rewrite integral_measure_add_nnsfun.
rewrite limeD//; do?[exact: cvg_f_]; last first.
  by apply: ge0_adde_def; rewrite inE; apply: lime_ge => //; do?[exact: cvg_f_];
      apply: nearW => n;  apply: integral_ge0 => //; exact: f_ge0.
by congr (_ + _); (rewrite -monotone_convergence//; [
    apply: eq_integral => t /[!inE] Dt; apply/cvg_lim => //; exact: cvg_nnsfun_approx |
    move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx]).
Qed.

End integral_mfun_measure_sum.

Lemma ge0_integral_measure_add d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> measurable_fun D f ->
  (\int[measure_add m1 m2]_(x in D) f x =
   \int[m1]_(x in D) f x + \int[m2]_(x in D) f x)%E.
Proof.
move=> f0 mf; rewrite /measureD ge0_integral_measure_sum// 2!big_ord_recl/=.
by rewrite big_ord0 adde0.
Qed.

Section integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Let integral_measure_series_indic (D : set T) (mD : measurable D) :
  \int[m]_x (\1_D x)%:E = \sum_(n <oo) \int[m_ n]_x (\1_D x)%:E.
Proof.
rewrite integral_indic// setIT /m/= /mseries; apply: eq_eseriesr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Lemma integral_measure_series_nnsfun (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n <oo) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n <oo) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_series_indic// nneseriesZl//.
  by move=> n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= -nneseries_sum; last first.
  move=> r j _.
  have [r0|r0] := leP 0%R r.
    by rewrite mule_ge0//; apply: integral_ge0 => // t _; rewrite lee_fin.
  rewrite integral0_eq ?mule0// => x _.
  by rewrite preimage_nnfun0// indicE in_set0.
apply: eq_eseriesr => k _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

End integral_measure_series.

Section ge0_integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Import HBNNSimple.

Lemma ge0_integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall t, D t -> 0 <= f t) ->
  measurable_fun D f ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  suff : forall n, \sum_(k < n) \int[m_ k]_(x in D) f x <= \int[m]_(x in D) f x.
    move=> n; apply: lime_le => //.
      by apply: is_cvg_ereal_nneg_natsum => k _; exact: integral_ge0.
    by apply: nearW => x; rewrite big_mkord.
  move=> n.
  rewrite [X in _ <= X](_ : _ = \sum_(k < n) \int[m_ k]_(x in D) f x +
                                \int[mseries m_ n]_(x in D) f x); last first.
    transitivity (\int[measure_add (msum m_ n) (mseries m_ n)]_(x in D) f x).
      congr (\int[_]_(_ in D) _); apply/funext => A.
      rewrite measure_addE/= /msum -(big_mkord xpredT (m_ ^~ A)).
      exact: nneseries_split.
    by rewrite ge0_integral_measure_add// -ge0_integral_measure_sum.
  by apply: leeDl; exact: integral_ge0.
rewrite ge0_integralE//=; apply: ub_ereal_sup => /= _ [g /= gf] <-.
rewrite -integralT_nnsfun (integral_measure_series_nnsfun _ mD).
apply: lee_nneseries => [n _ _|n _].
  by apply: integral_ge0 => // x _; rewrite lee_fin.
rewrite [leRHS]integral_mkcond; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP.
- by move=> x _; rewrite erestrict_ge0.
- exact/(measurable_restrictT _ mD).
Qed.

End ge0_integral_measure_series.

Section subset_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_setU (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun (A `|` B) f ->
  (forall x, (A `|` B) x -> 0 <= f x) -> [disjoint A & B] ->
  \int[mu]_(x in A `|` B) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB.
transitivity (\int[mu]_(x in A `|` B) ((f \_ A) x + (f \_ B) x)).
  apply: eq_integral => x; rewrite inE => -[xA|xB].
    rewrite /patch mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xB.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
  rewrite /patch addeC mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xA.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
rewrite ge0_integralD//; last 5 first.
  - exact: measurableU.
  - by move=> x _; apply: erestrict_ge0 => y Ay; apply: f0; left.
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
  - by move=> x _; apply: erestrict_ge0 => y By; apply: f0; right.
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
by rewrite -integral_mkcondl setIC setUK -integral_mkcondl setKU.
Qed.

Lemma ge0_subset_integral (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun B f -> (forall x, B x -> 0 <= f x) ->
  A `<=` B -> \int[mu]_(x in A) f x <= \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB; rewrite -(setDUK AB) ge0_integral_setU//; last 4 first.
  - exact: measurableD.
  - by rewrite setDUK.
  - by move=> x; rewrite setDUK//; exact: f0.
  - by rewrite disj_set2E setDIK.
by apply: leeDl; apply: integral_ge0 => x [Bx _]; exact: f0.
Qed.

Lemma ge0_integral_bigsetU (I : eqType) (F : I -> set T) (f : T -> \bar R)
    (s : seq I) : (forall n, measurable (F n)) -> uniq s ->
  trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) f x = \sum_(i <- s) \int[mu]_(x in F i) f x.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf f0.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons ge0_integral_setU//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
  + by move=> x UFx; apply: f0; rewrite /D big_cons; right.
- exact: bigsetU_measurable.
- by move: mf; rewrite /D big_cons.
- by move: f0; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> (0 < a)%R ->
  a%:E * mu (D `&` [set x | `|g x| >= a%:E]) <= \int[mu]_(x in D) `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | a%:E <= `|g x|]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) `|g x|)).
  rewrite -integral_cstr//; apply: ge0_le_integral => //.
  - by move=> x _ /=; exact/ltW.
  - by apply: measurableT_comp => //; exact: measurable_funS mg.
  - by move=> x /= [].
by apply: ge0_subset_integral => //; exact: measurableT_comp.
Qed.

End subset_integral.
#[deprecated(since="mathcomp-analysis 1.0.1", note="use `ge0_integral_setU` instead")]
Notation integral_setU := ge0_integral_setU (only parsing).

Section integral_setU_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_setU_EFin (A B : set T) (f : T -> R) :
  measurable A -> measurable B ->
  measurable_fun (A `|` B) f ->
  [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) (f x)%:E = \int[mu]_(x in A) (f x)%:E +
                                       \int[mu]_(x in B) (f x)%:E.
Proof.
move=> mA mB ABf AB.
rewrite integralE/=.
rewrite ge0_integral_setU//; last exact/measurable_funepos/measurable_EFinP.
rewrite ge0_integral_setU//; last exact/measurable_funeneg/measurable_EFinP.
rewrite [X in _ = X + _]integralE/=.
rewrite [X in _ = _ + X]integralE/=.
set ap : \bar R := \int[mu]_(x in A) _; set an : \bar R := \int[mu]_(x in A) _.
set bp : \bar R := \int[mu]_(x in B) _; set bn : \bar R := \int[mu]_(x in B) _.
rewrite oppeD 1?addeACA//.
by rewrite ge0_adde_def// inE integral_ge0.
Qed.

Lemma integral_bigsetU_EFin (I : eqType) (F : I -> set T) (f : T -> R)
    (s : seq I) :
  (forall i, d.-measurable (F i)) ->
  uniq s -> trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D (EFin \o f) ->
  \int[mu]_(x in D) (f x)%:E = \sum_(i <- s) \int[mu]_(x in F i) (f x)%:E.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons integral_setU_EFin//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
- exact: bigsetU_measurable.
- by move/measurable_EFinP : mf; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

End integral_setU_EFin.

HB.lock Definition integrable {d} {T : measurableType d} {R : realType}
    (mu : set T -> \bar R) D f :=
  `[< measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E >].
Canonical integrable_unlockable := Unlockable integrable.unlock.

Lemma integrableP d T R mu D f :
  reflect (measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E)
    (@integrable d T R mu D f).
Proof. by rewrite unlock; apply/(iffP (asboolP _)). Qed.

Lemma measurable_int d T R mu D f :
  @integrable d T R mu D f -> measurable_fun D f.
Proof. by rewrite unlock => /asboolP[]. Qed.
Arguments measurable_int {d T R} mu {D f}.

Section integrable_theory.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).
Implicit Type f g : T -> \bar R.

Notation mu_int := (integrable mu D).

Lemma integrable0 : mu_int (cst 0).
Proof.
apply/integrableP; split=> //; under eq_integral do rewrite (gee0_abs (lexx 0)).
by rewrite integral0.
Qed.

Lemma eq_integrable f g : {in D, f =1 g} -> mu_int f -> mu_int g.
Proof.
move=> fg /integrableP[mf fi]; apply/integrableP; split.
  exact: eq_measurable_fun mf.
rewrite (le_lt_trans _ fi)//; apply: ge0_le_integral=> //.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
by move=> x Dx; rewrite fg// inE.
Qed.

Lemma le_integrable f g : measurable_fun D f ->
  (forall x, D x -> `|f x| <= `|g x|) -> mu_int g -> mu_int f.
Proof.
move=> mf fg /integrableP[mfg goo]; apply/integrableP; split => //.
by apply: le_lt_trans goo; apply: ge0_le_integral => //; exact: measurableT_comp.
Qed.

Lemma integrableN f : mu_int f -> mu_int (-%E \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split; last first.
  by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; exact: measurableT_comp.
Qed.

Lemma integrableZl (k : R) f : mu_int f -> mu_int (fun x => k%:E * f x).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurable_funeM.
under eq_fun do rewrite abseM.
by rewrite ge0_integralZl// ?lte_mul_pinfty//; exact: measurableT_comp.
Qed.

Lemma integrableZr (k : R) f : mu_int f -> mu_int (f \* cst k%:E).
Proof.
by move=> mf; apply: eq_integrable (integrableZl k mf) => // x; rewrite muleC.
Qed.

Lemma integrableD f g : mu_int f -> mu_int g -> mu_int (f \+ g).
Proof.
move=> /integrableP[mf foo] /integrableP[mg goo]; apply/integrableP; split.
  exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int[mu]_(x in D) (`|f x| + `|g x|))).
  apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; exact: emeasurable_funD.
  - by move=> ? ?; apply: adde_ge0.
  - by apply: emeasurable_funD; apply: measurableT_comp.
  - by move=> *; exact: lee_abs_add.
by rewrite ge0_integralD //; [exact: lte_add_pinfty|
  exact: measurableT_comp|exact: measurableT_comp].
Qed.

Lemma integrable_sum (s : seq (T -> \bar R)) :
  (forall h, h \in s -> mu_int h) -> mu_int (fun x => \sum_(h <- s) h x).
Proof.
elim: s => [_|h s ih hs].
  by under eq_fun do rewrite big_nil; exact: integrable0.
under eq_fun do rewrite big_cons; apply: integrableD => //.
- by apply: hs; rewrite in_cons eqxx.
- by apply: ih => k ks; apply: hs; rewrite in_cons ks orbT.
Qed.

Lemma integrableB f g : mu_int f -> mu_int g -> mu_int (f \- g).
Proof. by move=> fi gi; exact/(integrableD fi)/integrableN. Qed.

Lemma integrable_add_def f : mu_int f ->
  \int[mu]_(x in D) f^\+ x +? - \int[mu]_(x in D) f^\- x.
Proof.
move=> /integrableP[mf]; rewrite -[fun x => _]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
- exact: measurable_funepos.
- exact: measurable_funeneg.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite leeDl// integral_ge0.
- by rewrite inE (@le_lt_trans _ _ 0)// leeNl oppe0 integral_ge0.
Qed.

Lemma integrable_funepos f : mu_int f -> mu_int f^\+.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funepos.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funepos.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDl.
Qed.

Lemma integrable_funeneg f : mu_int f -> mu_int f^\-.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funeneg.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funeneg.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDr.
Qed.

Lemma integral_funeneg_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\- x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funeneg.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funenegE.
    by move: fx0; rewrite -{1}oppe0 -leeNr => /max_idPl ->.
  rewrite gee0_abs// funenegE.
  by move: (fx0); rewrite -{1}oppe0 -leeNl => /max_idPr ->.
Qed.

Lemma integral_funepos_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\+ x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funepos.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funeposE.
    by move: (fx0) => /max_idPr ->; rewrite -leeNr oppe0.
  by rewrite gee0_abs// funeposE; move: (fx0) => /max_idPl ->.
Qed.

Lemma integrable_neg_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\- x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funeneg.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDr.
Qed.

Lemma integrable_pos_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\+ x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funepos.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDl.
Qed.

Lemma integrableMr (h : T -> R) g :
  measurable_fun D h -> [bounded h x | x in D] ->
  mu_int g -> mu_int ((EFin \o h) \* g).
Proof.
move=> mh [M [Mreal Mh]] gi; apply/integrableP; split.
  by apply: emeasurable_funM => //; [exact: measurableT_comp|
                                     exact: measurable_int gi].
under eq_integral do rewrite abseM.
have: \int[mu]_(x in D) (`|M + 1|%:E * `|g x|) < +oo.
  rewrite ge0_integralZl ?lte_mul_pinfty//; first by case/integrableP : gi.
  by apply: measurableT_comp => //; exact: measurable_int gi.
apply/le_lt_trans/ge0_le_integral => //.
- apply/emeasurable_funM; last exact/measurableT_comp/(measurable_int _ gi).
  exact/measurable_EFinP/measurableT_comp.
- apply/emeasurable_funM => //; apply/measurableT_comp => //.
  exact: measurable_int gi.
- move=> x Dx; rewrite lee_wpmul2r//= lee_fin Mh//=.
  by rewrite (lt_le_trans _ (ler_norm _))// ltrDl.
Qed.

Lemma integrableMl f (h : T -> R) :
  mu_int f -> measurable_fun D h -> [bounded h x | x in D] ->
  mu_int (f \* (EFin \o h)).
Proof.
move=> fi mh mg; rewrite /is_true -(integrableMr mh mg fi).
by apply/congr1/funext => ?; rewrite muleC.
Qed.

Lemma integrable_restrict (E : set T) (mE : d.-measurable E) f :
  integrable mu (E `&` D) f <-> integrable mu E (f \_ D).
Proof.
split; move=> /integrableP[mf intfoo]; apply/integrableP; split.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
Qed.

Lemma le_integral f g : mu_int f -> mu_int g ->
  {in D, forall x, f x <= g x} -> \int[mu]_(x in D) f x <= \int[mu]_(x in D) g x.
Proof.
move=> intf intg fg; rewrite integralE [leRHS]integralE leeB//.
- apply: ge0_le_integral => //.
  + by move/integrableP : intf => [+ _]; exact: measurable_funepos.
  + by move/integrableP : intg => [+ _]; exact: measurable_funepos.
  + by move=> x /mem_set; exact: funepos_le.
- apply: ge0_le_integral => //.
  + by move/integrableP : intg => [+ _]; exact: measurable_funeneg.
  + by move/integrableP : intf => [+ _]; exact: measurable_funeneg.
  + by move=> x /mem_set; exact: funeneg_le.
Qed.

End integrable_theory.
Notation "mu .-integrable" := (integrable mu) : type_scope.
Arguments eq_integrable {d T R mu D} mD f.

Section integrable_theory_finite_measure.
Context {R : realType} d (T : measurableType d).
Variable mu : {finite_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integrable_indic A : measurable A ->
  mu.-integrable [set: T] (fun x : T => (\1_A x)%:E).
Proof.
move=> mA; apply/integrableP; split; first exact/measurable_EFinP.
rewrite (eq_integral (fun x => (\1_A x)%:E)); last first.
  by move=> t _; rewrite gee0_abs// lee_fin.
rewrite integral_indic// setIT.
rewrite (@le_lt_trans _ _ (mu setT)) ?le_measure ?inE//.
by rewrite ?ltry ?fin_num_fun_lty//; exact: fin_num_measure.
Qed.

End integrable_theory_finite_measure.

Section sequence_measure.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Lemma integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall n, integrable (m_ n) D f) ->
  measurable_fun D f ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x | < +oo%E ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x | < +oo%E ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> fi mf fmoo fpoo; rewrite integralE.
rewrite ge0_integral_measure_series//; last exact/measurable_funepos.
rewrite ge0_integral_measure_series//; last exact/measurable_funeneg.
transitivity (\sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\+ x)%E)%:E -
              \sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\- x))%:E).
  by congr (_ - _); apply: eq_eseriesr => n _; rewrite fineK//;
    [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
have fineKn : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_neg_fin_num.
have fineKp : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_pos_fin_num.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -esumB//; last 4 first.
  - by rewrite /= /summable -nneseries_esum// -fineKp.
  - by rewrite /summable /= -nneseries_esum// -fineKn; exact: fmoo.
  - by move=> n _; exact/fine_ge0/integral_ge0.
  - by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -summable_eseries_esum; last first.
  apply: (@le_lt_trans _ _ (\esum_(i in (fun=> true))
     `|(fine (\int[m_ i]_(x in D) f x))%:E|)).
    by apply: le_esum => k _; rewrite -EFinB -fineB// -?integralE//;
      [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
  rewrite -nneseries_esum; last by [].
  apply: (@le_lt_trans _ _
      (\sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E| +
       \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|)).
    rewrite -nneseriesD//; apply: lee_nneseries => // n _.
    rewrite integralE fineB// ?EFinB.
    - exact: (le_trans (lee_abs_sub _ _)).
    - exact: integrable_pos_fin_num.
    - exact: integrable_neg_fin_num.
  apply: lte_add_pinfty; first by rewrite -fineKp.
  by rewrite -fineKn; exact: fmoo.
by apply: eq_eseriesr => k _; rewrite !fineK// -?integralE//;
  [exact: integrable_neg_fin_num|exact: integrable_pos_fin_num].
Qed.

End sequence_measure.

Section integrable_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_bigcup (F : (set _)^nat) (f : T -> \bar R) :
  (forall k, measurable (F k)) ->
  let D := \bigcup_k F k in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset setT F ->
  \int[mu]_(x in D) f x = \sum_(i <oo) \int[mu]_(x in F i) f x.
Proof.
move=> mF D mf f0 tF.
pose f_ N := f \_ (\big[setU/set0]_(0 <= i < N) F i).
have lim_f_ t : f_ ^~ t @ \oo --> (f \_ D) t.
  rewrite [X in _ --> X](_ : _ = ereal_sup (range (f_ ^~ t))); last first.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite /restrict; case: ifPn => [|_].
        rewrite in_setE => -[n _ Fnt]; apply: ereal_sup_ubound; exists n.+1=>//.
        by rewrite /f_ big_mkord patchT// in_setE big_ord_recr/=; right.
      rewrite (@le_trans _ _ (f_ O t))// ?ereal_sup_ubound//.
      by rewrite /f_ patchN// big_mkord big_ord0 inE/= in_set0.
    apply: ub_ereal_sup => x [n _ <-].
    by rewrite /f_ restrict_lee// big_mkord; exact: bigsetU_bigcup.
  apply: ereal_nondecreasing_cvgn => a b ab.
  rewrite /f_ !big_mkord restrict_lee //; last exact: subset_bigsetU.
  by move=> x Dx; apply: f0 => //; exact: bigsetU_bigcup Dx.
transitivity (\int[mu]_x limn (f_ ^~ x)).
  rewrite integral_mkcond; apply: eq_integral => x _.
  by apply/esym/cvg_lim => //; exact: lim_f_.
rewrite monotone_convergence//; last 3 first.
  - move=> n; apply/(measurable_restrictT f) => //.
      by apply: bigsetU_measurable => k _; exact: mF.
    move: mf; apply/measurable_funS =>//; first exact: bigcup_measurable.
    by rewrite big_mkord; exact: bigsetU_bigcup.
  - move=> n x _; apply: erestrict_ge0 => y; rewrite big_mkord => Dy; apply: f0.
    exact: bigsetU_bigcup Dy.
  - move=> x _ a b ab; apply: restrict_lee.
      by move=> y; rewrite big_mkord => Dy; apply: f0; exact: bigsetU_bigcup Dy.
    by rewrite 2!big_mkord; apply: subset_bigsetU.
transitivity (limn (fun N => \int[mu]_(x in \big[setU/set0]_(i < N) F i) f x)).
  by apply/congr_lim/funext => n; rewrite /f_ [in RHS]integral_mkcond big_mkord.
apply/congr_lim/funext => /= n.
rewrite -(big_mkord xpredT) ge0_integral_bigsetU ?big_mkord//.
- exact: iota_uniq.
- exact: sub_trivIset tF.
- move: mf; apply: measurable_funS => //; first exact: bigcup_measurable.
  exact: bigsetU_bigcup.
- by move=> y Dy; apply: f0; exact: bigsetU_bigcup Dy.
Qed.

Lemma integrableS (E D : set T) (f : T -> \bar R) :
  measurable E -> measurable D -> D `<=` E ->
  mu.-integrable E f -> mu.-integrable D f.
Proof.
move=> mE mD DE /integrableP[mf ifoo]; apply/integrableP; split.
  exact: measurable_funS mf.
apply: le_lt_trans ifoo; apply: ge0_subset_integral => //.
exact: measurableT_comp.
Qed.

Lemma integrable_mkcond D f : measurable D ->
  mu.-integrable D f <-> mu.-integrable setT (f \_ D).
Proof.
move=> mD.
rewrite unlock; apply: asbool_equiv; rewrite [in X in X <-> _]integral_mkcond.
under [in X in X <-> _]eq_integral do rewrite restrict_abse.
split => [|] [mf foo].
- by split; [exact/(measurable_restrictT _ _).1| exact: le_lt_trans foo].
- by split; [exact/(measurable_restrictT _ _).2| exact: le_lt_trans foo].
Qed.

End integrable_lemmas.
Arguments integrable_mkcond {d T R mu D} f.

Section ge0_cvgn_integral.
Local Open Scope ereal_scope.
Context {R : realType}.
Variable mu : {measure set (@measurableTypeR R) -> \bar R}.
Variable f : R -> R.
Hypothesis f0 : (forall x, 0 <= f x)%R.
Hypothesis mf : measurable_fun setT f.

Let ge0_integral_ereal_sup :
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E =
  ereal_sup [set \int[mu]_(x in `[0%R, i.+1%:R]) (f x)%:E | i in [set: nat]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ub_ereal_sup => /=_ [n _ <-].
  apply: ge0_subset_integral => //=.
  - by apply/measurable_EFinP; exact: measurable_funS mf.
  - by move=> ? _; rewrite lee_fin f0.
  - exact: subset_itvl.
rewrite itv0y_bigcup0S.
rewrite seqDU_bigcup_eq ge0_integral_bigcup//; last 3 first.
- by move=> ?; apply: measurableD => //; exact: bigsetU_measurable.
- exact/measurable_funTS/measurable_EFinP.
- by move=> x; rewrite lee_fin f0.
apply: lime_le => /=.
  apply: is_cvg_nneseries => n _ _.
  by apply: integral_ge0 => k _; exact: f0.
apply: nearW => n.
rewrite -ge0_integral_bigsetU//=; first last.
- by move=> ? _; rewrite lee_fin ?expR_ge0.
- exact/measurable_EFinP/measurableT_comp.
- exact: (sub_trivIset (@subsetT _ _)).
- exact: iota_uniq.
- by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
rewrite big_mkord -bigsetU_seqDU.
move: n => [|n].
  rewrite big_ord0 integral_set0.
  apply: ereal_sup_le.
  exists (\int[mu]_(x in `[0%R, 1%:R]) (f x)%:E) => //.
  apply: integral_ge0.
  by move=> ? _; rewrite lee_fin f0.
rewrite [X in \int[_]_(_ in X) _](_ : _ = `[0%R, n.+1%:R]%classic); last first.
  rewrite eqEsubset; split => x/=; rewrite in_itv/=.
    rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
    move=> [k /= kSn].
    rewrite in_itv/= => /andP[-> xSk]/=.
    by rewrite (le_trans xSk)// ler_nat.
  move=> /andP[x0 Snx].
  rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
  exists n => //=.
  by rewrite in_itv/= x0 Snx.
apply: ereal_sup_le.
exists (\int[mu]_(x in `[0%R, n.+1%:R]) (f x)%:E); first by exists n.
apply: ge0_subset_integral => //= [|? _]; last by rewrite lee_fin f0.
exact/measurable_EFinP/measurableT_comp.
Qed.

Lemma ge0_cvgn_integral :
  \int[mu]_(x in `[0%R, n%:R]) (f x)%:E @[n --> \oo] -->
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E.
Proof.
rewrite -cvg_shiftS/= ge0_integral_ereal_sup//.
apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n.
apply: (@ge0_subset_integral _ _ _ mu) => //.
- by apply: measurable_funTS; exact: measurableT_comp.
- by move => ? _; exact: f0.
- by apply: subset_itvl; rewrite bnd_simp ler_nat.
Qed.

End ge0_cvgn_integral.

Lemma finite_measure_integrable_cst d (T : measurableType d) (R : realType)
    (mu : {finite_measure set T -> \bar R}) k :
  mu.-integrable [set: T] (EFin \o cst k).
Proof.
apply/integrableP; split; first exact/measurable_EFinP.
have [k0|k0] := leP 0 k.
- under eq_integral do rewrite /= ger0_norm//.
  rewrite integral_cstr//= lte_mul_pinfty// fin_num_fun_lty//.
  exact: fin_num_measure.
- under eq_integral do rewrite /= ltr0_norm//.
  rewrite integral_cstr//= lte_mul_pinfty//.
    by rewrite lee_fin lerNr oppr0 ltW.
  by rewrite fin_num_fun_lty//; exact: fin_num_measure.
Qed.

Section integrable_ae.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : T -> \bar R.
Hypotheses fint : mu.-integrable D f.

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite (_ : E = D `&` f @^-1` [set -oo; +oo]).
    by apply: (measurable_int _ fint) => //; exact: measurableU.
  rewrite /E predeqE => t; split=> [[/eqP]|[Dt [|]/= ->//]].
  by rewrite eqe_absl leey andbT /preimage/= => /orP[|]/eqP; tauto.
have [ET|ET] := eqVneq E setT.
  have foo t : `|f t| = +oo by have [] : E t by rewrite ET.
  suff: \int[mu]_(x in D) `|f x| = +oo.
    by case: (integrableP _ _ _ fint) => _; rewrite ltey => /eqP.
  by rewrite -(integral_csty mD muD0)//; exact: eq_integral.
suff: mu E = 0.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt].
  by rewrite fin_num_abs => /negP; rewrite -leNgt leye_eq => /eqP.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M M0 muM] : exists2 M, (0 <= M)%R &
    forall n, n%:R%:E * mu (E `&` D) <= M%:E.
  exists (fine (\int[mu]_(x in D) `|f x|)); first exact/fine_ge0/integral_ge0.
  move=> n; rewrite -integral_indic// -ge0_integralZl//; last first.
    exact: measurableT_comp.
  rewrite fineK//; last first.
    case: (integrableP _ _ _ fint) => _ foo.
    by rewrite ge0_fin_numE// integral_ge0.
  apply: ge0_le_integral => //.
  - exact/measurable_EFinP/measurableT_comp.
  - by apply: measurableT_comp => //; exact: measurable_int fint.
  - move=> x Dx; rewrite /= indicE.
    have [|xE] := boolP (x \in E); last by rewrite mule0.
    by rewrite /E inE /= => -[->]; rewrite leey.
apply/eqP/negPn/negP => /eqP muED0; move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite leye_eq => /eqP ->; exists 1%N; rewrite mul1e leye_eq.
exists (trunc (M * (fine (mu (E `&` D)))^-1)).+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  by rewrite fin_numElt muEDoo (lt_le_trans _ (measure_ge0 _ _)).
rewrite lte_fin -ltr_pdivrMr; first by rewrite truncnS_gt.
rewrite -lte_fin fineK.
  rewrite lt0e measure_ge0 andbT.
  suff: E `&` D = E by move=> ->; exact/eqP.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section linearityZ.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Let mesf : measurable_fun D f. Proof. exact: measurable_int intf. Qed.

Lemma integralZl r :
  \int[mu]_(x in D) (r%:E * f x) = r%:E * \int[mu]_(x in D) f x.
Proof.
have /orP[r0|r0] := le_total r 0%R.
- rewrite [in LHS]integralE// le0_funeposM// le0_funenegM//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _)) ?oppr_ge0//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _)) ?oppr_ge0//.
  rewrite !EFinN addeC !mulNe oppeK -muleBr ?integrable_add_def//.
  by rewrite [in RHS]integralE.
- rewrite [in LHS]integralE// ge0_funeposM// ge0_funenegM//=.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _) r0)//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _) r0)//.
  by rewrite -muleBr 1?[in RHS]integralE// integrable_add_def.
Qed.

Lemma integralZr r :
  \int[mu]_(x in D) (f x * r%:E) = (\int[mu]_(x in D) f x) * r%:E.
Proof. by rewrite muleC -integralZl; under eq_integral do rewrite muleC. Qed.

End linearityZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl` instead")]
Notation integralM := integralZl (only parsing).

Section linearityD_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> R.
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : mu.-integrable D g1.
Hypothesis if2 : mu.-integrable D g2.

Let mf1 : measurable_fun D g1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D g2. Proof. exact: measurable_int if2. Qed.

Lemma integralD_EFin :
  \int[mu]_(x in D) (g1 \+ g2) x =
  \int[mu]_(x in D) g1 x + \int[mu]_(x in D) g2 x.
Proof.
suff: \int[mu]_(x in D) ((g1 \+ g2)^\+ x) + \int[mu]_(x in D) (g1^\- x) +
        \int[mu]_(x in D) (g2^\- x) =
      \int[mu]_(x in D) ((g1 \+ g2)^\- x) + \int[mu]_(x in D) (g1^\+ x) +
        \int[mu]_(x in D) (g2^\+ x).
  move=> h; rewrite [in LHS]integralE.
  move/eqP : h; rewrite -[in eqbRHS]addeA [in eqbRHS]addeC.
  have g12pos :
      \int[mu]_(x in D) (g1^\+ x) + \int[mu]_(x in D) (g2^\+ x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funepos_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  have g12neg :
      \int[mu]_(x in D) (g1^\- x) + \int[mu]_(x in D) (g2^\- x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty// ; exact: integral_funeneg_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        exact: integral_funepos_lt_pinfty (integrableD _ _ _).
      apply: adde_ge0; last exact: integral_ge0.
      by apply: adde_ge0; apply: integral_ge0.
    - exact/fin_num_adde_defr/g12pos.
  rewrite -[X in X - _ == _]addeA [X in X - _ == _]addeC -[eqbLHS]addeA.
  rewrite [eqbLHS]addeC eq_sym.
  rewrite -(sube_eq g12pos) ?fin_num_adde_defl// => /eqP g12E.
  rewrite -{}[LHS]g12E fin_num_oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funeneg_lt_pinfty if2.
    exact: integral_ge0.
  by rewrite addeACA (integralE _ _ g1) (integralE _ _ g2).
have : (g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in eqbRHS]addeC -sube_eq; last 2 first.
    by rewrite funeposE !funenegE -!fine_max.
    by rewrite !funeposE funenegE -!fine_max.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite !funeposE -!fine_max.
    by rewrite funeposE !funenegE -!fine_max.
  apply/eqP.
  rewrite -[LHS]/((g1^\+ \+ g2^\+ \- (g1^\- \+ g2^\-)) x) -funeD_posD.
  by rewrite -[RHS]/((_ \- _) x) -funeD_Dpos.
move/(congr1 (fun y => \int[mu]_(x in D) (y x) )).
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funeneg.
    exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact: measurable_funeneg.
rewrite (ge0_integralD mu mD); last 4 first.
  - by [].
  - exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact/measurable_funeneg.
move=> g12E; rewrite {}[LHS]g12E.
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; exact: adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funepos.
    exact/measurable_funeneg/emeasurable_funD.
  - by [].
  - exact: measurable_funepos.
rewrite (ge0_integralD mu mD) //; last exact: measurable_funepos.
exact/measurable_funeneg/emeasurable_funD.
Qed.

End linearityD_EFin.

Lemma integralB_EFin d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R)
  (mD : measurable D) :
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  (\int[mu]_(x in D) ((f1 x)%:E - (f2 x)%:E) =
    (\int[mu]_(x in D) (f1 x)%:E - \int[mu]_(x in D) (f2 x)%:E))%E.
Proof.
move=> if1 if2; rewrite (integralD_EFin mD if1); last first.
  by rewrite (_ : _ \o _ = (fun x => - (f2 x)%:E))%E; [exact: integrableN|by []].
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Lemma le_abse_integral d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R)
  (mD : measurable D) : measurable_fun D f ->
  (`| \int[mu]_(x in D) (f x) | <= \int[mu]_(x in D) `|f x|)%E.
Proof.
move=> mf.
rewrite integralE (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: integral_ge0.
rewrite gee0_abs; last exact: integral_ge0.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: measurable_funepos | exact: measurable_funeneg].
Qed.

Lemma abse_integralP d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R) :
    measurable D -> measurable_fun D f ->
  (`| \int[mu]_(x in D) f x | < +oo <-> \int[mu]_(x in D) `|f x| < +oo)%E.
Proof.
move=> mD mf; split => [|] foo; last first.
  exact: (le_lt_trans (le_abse_integral mu mD mf) foo).
under eq_integral do rewrite -/((abse \o f) _) fune_abse.
rewrite ge0_integralD//;[|exact/measurable_funepos|exact/measurable_funeneg].
move: foo; rewrite integralE/= -fin_num_abs fin_numB => /andP[fpoo fnoo].
by rewrite lte_add_pinfty// ltey_eq ?fpoo ?fnoo.
Qed.

Lemma integral_fin_num_abs d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> R) :
  measurable D -> measurable_fun D f ->
  (\int[mu]_(x in D) `|(f x)%:E| < +oo)%E =
  ((\int[mu]_(x in D) (f x)%:E)%E \is a fin_num).
Proof.
move=> mD mf; rewrite fin_num_abs; case H : LHS; apply/esym.
- by move: H => /abse_integralP ->//; exact/measurable_EFinP.
- apply: contraFF H => /abse_integralP; apply => //.
  exact/measurable_EFinP.
Qed.

Section integral_patch.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma __deprecated__integral_setI_indic (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  \int[mu]_(x in E `&` D) f x = \int[mu]_(x in E) (f x * (\1_D x)%:E).
Proof.
move=> mE; rewrite integral_mkcondr.
by under eq_integral do rewrite epatch_indic.
Qed.

Lemma __deprecated__integralEindic (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f x * (\1_D x)%:E).
Proof. by rewrite -__deprecated__integral_setI_indic// setIid. Qed.

Lemma integralEpatch (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f \_ D) x.
Proof. by rewrite -[in LHS](setIid D) integral_mkcondr. Qed.

End integral_patch.
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integral_mkcondr` instead")]
Notation integral_setI_indic := __deprecated__integral_setI_indic (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integralEpatch` instead")]
Notation integralEindic := __deprecated__integralEindic (only parsing).

Section ae_eq_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Local Notation ae_eq := (ae_eq mu).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  ae_eq D f (cst 0) -> \int[mu]_(x in D) `|f x|%E  = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose Df_neq0 := D `&` [set x | f x != 0].
have mDf_neq0 : measurable Df_neq0 by exact: emeasurable_neq.
pose f' : T -> R := indic Df_neq0.
have le_f_M t : D t -> `|f t| <= M%:E * (f' t)%:E.
  move=> Dt; rewrite /f' indicE; have [|] := boolP (t \in Df_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  by rewrite notin_setE=> /not_andP[//|/negP/negPn/eqP ->]; rewrite abse0 mule0.
have : 0 <= \int[mu]_(x in D) `|f x|  <= `|M|%:E * mu Df_neq0.
  rewrite integral_ge0//= /Df_neq0 -{2}(setIid D) setIAC -integral_indic//.
  rewrite -/Df_neq0 -ge0_integralZl//; last exact: measurableT_comp.
  apply: ge0_le_integral => //.
  - exact: measurableT_comp.
  - by apply: emeasurable_funM => //; exact: measurableT_comp.
  - move=> x Dx; rewrite (le_trans (le_f_M _ Dx))// lee_fin /f' indicE.
    by case: (_ \in _) => //; rewrite ?mulr1 ?mulr0// ler_norm.
have -> : mu Df_neq0 = 0.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
by rewrite mule0 -eq_le => /eqP.
Qed.

Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable_fun D f -> \int[mu]_(x in D) `|f x| = 0 <-> ae_eq D f (cst 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists (D `&` [set x | f x != 0]); split;
    [exact: emeasurable_neq| |by move=> t /= /not_implyP [Dt /eqP ft0]].
  have muDf a : (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x|]) = 0.
    move=> a0; apply/eqP; rewrite -measure_le0.
    by have := le_integral_abse mu mD mf a0; rewrite iDf0 pmule_rle0 ?lte_fin.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[Dt ft0]|[n _ /= [Dt nft]]].
      have [ftoo|ftoo] := eqVneq `|f t| +oo.
        by exists 0%N => //; split => //=; rewrite ftoo /= leey.
      pose m := trunc (fine `|f t|)^-1.
      have ftfin : `|f t|%E \is a fin_num by rewrite ge0_fin_numE// ltey.
      exists m => //; split => //=.
      rewrite -(@fineK _ `|f t|) // lee_fin invf_ple; last 2 first.
        exact: ltr0n.
        by apply/fine_gt0; rewrite lt0e abse_ge0 abse_eq0 ft0 ltey.
      by rewrite (le_trans (ltW (truncnS_gt _))).
    by split => //; apply: contraTN nft => /eqP ->; rewrite abse0 -ltNge.
  transitivity (limn (fun n => mu (D `&` [set x | `|f x| >= n.+1%:R^-1%:E]))).
    apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
    - move=> i; apply: emeasurable_fun_c_infty => //.
      exact: measurableT_comp.
    - apply: bigcupT_measurable => i.
      by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
    - move=> m n mn; apply/subsetPset; apply: setIS => t /=.
      by apply: le_trans; rewrite lee_fin lef_pV2 // ?ler_nat // posrE.
  by rewrite (_ : (fun _ => _) = cst 0) ?lim_cst//= funeqE => n /=; rewrite muDf.
pose f_ := fun n x => mine `|f x| n%:R%:E.
have -> : (fun x => `|f x|) = (fun x => limn (f_^~ x)).
  rewrite funeqE => x; apply/esym/cvg_lim => //; apply/cvg_ballP => _/posnumP[e].
  near=> n; rewrite /ball /= /ereal_ball /= /f_.
  have [->|fxoo] := eqVneq `|f x|%E +oo.
    rewrite -[contract +oo](@divff _ (1 + n%:R)) ?nat1r//=.
    rewrite (@ger0_norm _ n%:R)// nat1r -mulrBl -natrB// subSnn ger0_norm//.
    by rewrite div1r; near: n; exact: near_infty_natSinv_lt.
  have fxn : `|f x| <= n%:R%:E.
    rewrite -(@fineK _ `|f x|); last by rewrite ge0_fin_numE// ltey.
    rewrite lee_fin; near: n; exists (Num.bound (fine `|f x|)) => //= n/=.
    by rewrite -(ler_nat R); apply: le_trans; exact/ltW/archi_boundP.
  by rewrite min_l// subrr normr0.
transitivity (limn (fun n => \int[mu]_(x in D) (f_ n x) )).
  apply/esym/cvg_lim => //; apply: cvg_monotone_convergence => //.
  - by move=> n; apply: measurable_mine => //; exact: measurableT_comp.
  - by move=> n t Dt; rewrite /f_ lexI abse_ge0 //= lee_fin.
  - move=> t Dt m n mn; rewrite /f_ lexI.
    have [ftm|ftm] := leP `|f t|%E m%:R%:E.
      by rewrite lexx /= (le_trans ftm)// lee_fin ler_nat.
    by rewrite (ltW ftm) /= lee_fin ler_nat.
have ae_eq_f_ n : ae_eq D (f_ n) (cst 0).
  case: Df0 => N [mN muN0 DfN].
  exists N; split => // t /= /not_implyP[Dt fnt0].
  apply: DfN => /=; apply/not_implyP; split => //.
  apply: contra_not fnt0 => ft0.
  by rewrite /f_ ft0 /= normr0 min_l// lee_fin.
have f_bounded n x : D x -> `|f_ n x| <= n%:R%:E.
  move=> Dx; rewrite /f_; have [|_] := leP `|f x| n%:R%:E.
    by rewrite abse_id.
  by rewrite gee0_abs// lee_fin.
have if_0 n : \int[mu]_(x in D) `|f_ n x| = 0.
  apply: (@ae_eq_integral_abs_bounded _ _ _ n%:R) => //.
    by apply: measurable_mine => //; exact: measurableT_comp.
  exact: f_bounded.
rewrite (_ : (fun _ => _) = cst 0) // ?lim_cst// funeqE => n.
by rewrite -(if_0 n); apply: eq_integral => x _; rewrite gee0_abs// /f_.
Unshelve. all: by end_near. Qed.

Lemma integral_abs_eq0 D (N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> N `<=` D -> measurable_fun D f ->
  mu N = 0 -> \int[mu]_(x in N) `|f x| = 0.
Proof.
move=> mN mD ND mf muN0; rewrite integralEpatch//.
rewrite (eq_integral (abse \o (f \_ N))); last first.
  by move=> t _; rewrite restrict_abse.
apply/ae_eq_integral_abs => //.
  apply/measurable_restrict => //; rewrite setIidr//.
  exact: (measurable_funS mD).
exists N; split => // t /= /not_implyP[_].
by rewrite patchE; case: ifPn => //; rewrite inE.
Qed.

Lemma negligible_integrable (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  mu N = 0 -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> mN mD mf muN0.
pose mCN := measurableC mN.
have /integrableP intone : mu.-integrable D (f \_ N).
  apply/integrableP; split.
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  rewrite (eq_integral ((abse \o f) \_ N)); last first.
    by move=> t _; rewrite restrict_abse.
  rewrite -integral_mkcondr (@integral_abs_eq0 D)//; first exact: measurableI.
  by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
have h1 : mu.-integrable D f <-> mu.-integrable D (f \_ ~` N).
  split=> [/integrableP intf|/integrableP intCf].
    apply/integrableP; split.
      by apply/measurable_restrict => //; exact: measurable_funS mf.
    rewrite (eq_integral ((abse \o f) \_ ~` N)); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr; case: intf => _; apply: le_lt_trans.
    by apply: ge0_subset_integral => //=; [exact:measurableI|
                                           exact:measurableT_comp].
  apply/integrableP; split => //; rewrite (funID N f).
  have ? : measurable_fun D (f \_ ~` N).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  have ? : measurable_fun D (f \_ N).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  apply: (@le_lt_trans _ _
    (\int[mu]_(x in D) (`|(f \_ ~` N) x| + `|(f \_ N) x|))).
    apply: ge0_le_integral => //.
    - by apply: measurableT_comp => //; exact: emeasurable_funD.
    - by move=> ? ?; apply: adde_ge0.
    - by apply: emeasurable_funD; exact: measurableT_comp.
    - by move=> *; rewrite lee_abs_add.
  rewrite ge0_integralD//; [|exact: measurableT_comp|exact: measurableT_comp].
  by apply: lte_add_pinfty; [case: intCf|case: intone].
have h2 : mu.-integrable (D `\` N) f <-> mu.-integrable D (f \_ ~` N).
  split=> [/integrableP intCf|/integrableP intCf]; apply/integrableP.
    split.
      by apply/measurable_restrict => //; exact: measurable_funS mf.
    rewrite (eq_integral ((abse \o f) \_ ~` N)); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr //; case: intCf => _; apply: le_lt_trans.
    apply: ge0_subset_integral => //=; [exact: measurableI|exact: measurableD|].
    by apply: measurableT_comp => //; apply: measurable_funS mf => // ? [].
  split.
    move=> mDN A mA; rewrite setDE (setIC D) -setIA; apply: measurableI => //.
    exact: mf.
  rewrite integral_mkcondr/=.
  under eq_integral do rewrite restrict_abse.
  by case: intCf.
by apply: (iff_trans h1); exact: iff_sym.
Qed.

Lemma ge0_negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf f0 muN0.
rewrite {1}(funID N f) ge0_integralD//; last 4 first.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - apply/measurable_restrict => //; first exact/measurableC.
    exact: measurable_funS mf.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - by apply/measurable_restrict => //; exact: measurable_funS mf.
rewrite -integral_mkcondr [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite -integral_mkcondr (eq_integral (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite (@integral_abs_eq0 D)//; first exact: measurableI.
by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) ->
  ae_eq D f g -> \int[mu]_(x in D) (f x) = \int[mu]_(x in D) (g x).
Proof.
move=> mD mf mg f0 g0 [N [mN N0 subN]].
rewrite integralEpatch// [RHS]integralEpatch//.
rewrite (ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) f0.
rewrite [RHS](ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) g0.
apply: eq_integral => x;rewrite in_setD => /andP[_ xN].
apply: contrapT; rewrite !patchE; case: ifPn => xD //.
move: xN; rewrite notin_setE; apply: contra_not => fxgx; apply: subN => /=.
by apply/not_implyP; split => //; exact/set_mem.
Qed.

Lemma ae_eq_integral (D : set T) (g f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  ae_eq D f g -> \int[mu]_(x in D) f x = \int[mu]_(x in D) g x.
Proof.
move=> mD mf mg /ae_eq_funeposneg[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: measurable_funepos|
                                       exact: measurable_funepos].
by apply: ge0_ae_eq_integral => //; [exact: measurable_funeneg|
                                     exact: measurable_funeneg].
Qed.

End ae_eq_integral.
Arguments ae_eq_integral {d T R mu D} g.

Local Open Scope ereal_scope.

Lemma integral_cst d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) : d.-measurable D ->
  forall r, \int[mu]_(x in D) (cst r) x = r * mu D.
Proof.
move=> mD; have [D0 r|D0 [r| |]] := eqVneq (mu D) 0.
  by rewrite (ae_eq_integral (cst 0))// ?integral0 ?D0 ?mule0//; exact: ae_eq0.
- by rewrite integral_cstr.
- by rewrite integral_csty// gt0_mulye// lt0e D0/=.
- by rewrite integral_cstNy// gt0_mulNye// lt0e D0/=.
Qed.
Add Search Blacklist "integral_cstr" "integral_csty" "integral_cstNy".

Lemma le_integral_comp_abse d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R})  (D : set T) (mD : measurable D)
    (g : T -> \bar R) a (f : \bar R -> \bar R) (mf : measurable_fun setT f)
    (f0 : forall r, 0 <= r -> 0 <= f r)
    (f_nd : {in `[0, +oo[%classic &, {homo f : x y / x <= y}}) :
  measurable_fun D g -> (0 < a)%R ->
  (f a%:E) * mu (D `&` [set x | (`|g x| >= a%:E)%E]) <= \int[mu]_(x in D) f `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | (a%:E <= `|g x|)%E]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) f `|g x|)).
  rewrite -integral_cst//; apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite f0 // lee_fin ltW.
  - by move=> x _ /=; rewrite f0.
  - apply: measurableT_comp => //; apply: measurableT_comp => //.
    exact: measurable_funS mg.
  - by move=> x /= [Dx]; apply: f_nd;
      rewrite inE /= in_itv /= andbT// lee_fin ltW.
apply: ge0_subset_integral => //; last by move=> x _ /=; rewrite f0.
by apply: measurableT_comp => //; exact: measurableT_comp.
Qed.

Local Close Scope ereal_scope.

Section ae_measurable_fun.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Hypothesis cmu : measure_is_complete mu.
Variables (D : set T) (f g : T -> \bar R).

Lemma ae_measurable_fun : ae_eq mu D f g ->
  measurable_fun D f -> measurable_fun D g.
Proof.
move=> [N [mN N0 subN]] mf B mB mD.
apply: (measurability (ErealGenOInfty.measurableE R)) => // _ [_ [x ->] <-].
rewrite [X in measurable X](_ : _ = D `&` ~` N `&` (f @^-1` `]x%:E, +oo[)
    `|` (D `&` N `&` g @^-1` `]x%:E, +oo[)); last first.
  apply/seteqP; split=> [y /= [Dy gyxoo]|y /= [[[Dy Ny] fyxoo]|]].
  - have [->|fgy] := eqVneq (f y) (g y).
      have [yN|yN] := boolP (y \in N).
        by right; split => //; rewrite inE in yN.
      by left; split => //; rewrite notin_setE in yN.
    by right; split => //; split => //; apply: subN => /= /(_ Dy); exact/eqP.
  - split => //; have [<-//|fgy] := eqVneq (f y) (g y).
    by exfalso; apply/Ny/subN => /= /(_ Dy); exact/eqP.
  - by move=> [[]].
apply: measurableU.
- rewrite setIAC; apply: measurableI; last exact/measurableC.
  exact/mf/emeasurable_itv.
- by apply: cmu; exists N; split => //; rewrite setIAC; apply: subIset; right.
Qed.

End ae_measurable_fun.

Section integralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Let mf1 : measurable_fun D f1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D f2. Proof. exact: measurable_int if2. Qed.

Lemma integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
pose A := D `&` [set x | f1 x \is a fin_num].
pose B := D `&` [set x | f2 x \is a fin_num].
have mA : measurable A by exact: emeasurable_fin_num.
have mB : measurable B by exact: emeasurable_fin_num.
have mAB : measurable (A `&` B) by apply: measurableI.
pose g1 := (fine \o f1 \_ (A `&` B))%R.
pose g2 := (fine \o f2 \_ (A `&` B))%R.
have ig1 : mu.-integrable D (EFin \o g1).
  rewrite (_ : _ \o _ = f1 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if1=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g1 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite 2!in_setI => /andP[/andP[xA f1xfin] _] /=.
  by rewrite fineK//; rewrite inE in f1xfin.
have mg1 := measurable_int _ ig1.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if2=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g2 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite in_setI => /andP[_]; rewrite in_setI => /andP[xB f2xfin] /=.
  by rewrite fineK//; rewrite inE in f2xfin.
have mg2 := measurable_int _ ig2.
transitivity (\int[mu]_(x in D) (EFin \o (g1 \+ g2)%R) x).
  apply: ae_eq_integral => //.
  - exact: emeasurable_funD.
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    exact: emeasurable_funD.
  - apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=.
    rewrite EFinD /g1 /g2 /restrict /=; have [|] := boolP (x \in A `&` B).
      by rewrite in_setI => /andP[xA xB] /=; rewrite !fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx)/= notin_setE/=.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// integralD_EFin//.
  congr (_ + _); apply: ae_eq_integral => //.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g1 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE/=.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g2 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE.
Qed.

End integralD.

Section integralB.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralB : \int[mu]_(x in D) (f1 \- f2) x =
                  \int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x.
Proof.
rewrite -[in RHS](@integralN _ _ _ _ _ f2); last exact: integrable_add_def.
by rewrite -[in RHS]integralD//; exact: integrableN.
Qed.

End integralB.

Section transfer.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variable phi : X -> Y.
Hypothesis mphi : measurable_fun [set: X] phi.
Variable mu : {measure set X -> \bar R}.
Variables D : set Y.
Variables f : Y -> \bar R.
Hypotheses (mf : measurable_fun [set: Y] f)
  (intf : mu.-integrable (phi @^-1` D) (f \o phi)).
Let mf_mixin := isMeasurableFun.Build _ _ _ _ _ mf.
Let mf_pack := MeasurableFun.Pack (MeasurableFun.Class mf_mixin).

Lemma integrable_pushforward :
  measurable D -> (pushforward mu mphi).-integrable D f.
Proof.
move=> mD; apply/integrableP; split; first exact: (measurable_funP mf_pack).
move/integrableP : (intf) => [_]; apply: le_lt_trans.
rewrite ge0_integral_pushforward//.
by apply: measurableT_comp => //; exact: measurable_funTS.
Qed.

Local Open Scope ereal_scope.

Lemma integral_pushforward : measurable D ->
  \int[pushforward mu mphi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD.
rewrite integralE.
under [X in X - _]eq_integral do rewrite funepos_comp.
under [X in _ - X]eq_integral do rewrite funeneg_comp.
rewrite -[X in _ = X - _]ge0_integral_pushforward//; last first.
  exact/measurable_funepos/measurable_funTS.
rewrite -[X in _ = _ - X]ge0_integral_pushforward//; last first.
  exact/measurable_funeneg/measurable_funTS.
rewrite -integralB//=; last first.
- by apply: integrable_funeneg => //=; exact: integrable_pushforward.
- by apply: integrable_funepos => //=; exact: integrable_pushforward.
- by apply/eq_integral => x _; rewrite /= [in LHS](funeposneg f).
Qed.

End transfer.

Section integral_measure_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (m1 m2 : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Variable f : T -> \bar R.
Hypothesis intf1 : m1.-integrable D f.
Hypothesis intf2 : m2.-integrable D f.
Hypothesis mf : measurable_fun D f.

Lemma integral_measure_add : \int[measure_add m1 m2]_(x in D) f x =
  \int[m1]_(x in D) f x + \int[m2]_(x in D) f x.
Proof.
transitivity (\int[m1]_(x in D) (f^\+ \- f^\-) x +
              \int[m2]_(x in D) (f^\+ \- f^\-) x); last first.
  by congr +%E; apply: eq_integral => x _; rewrite [in RHS](funeposneg f).
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite addeACA -ge0_integral_measure_add//; last first.
  by apply: measurable_funepos; exact: measurable_int intf1.
rewrite -oppeD; last by rewrite ge0_adde_def// inE integral_ge0.
rewrite -ge0_integral_measure_add// 1?integralE//.
by apply: measurable_funeneg; exact: measurable_int intf1.
Qed.

End integral_measure_add.

Section negligible_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> mu.-integrable D f ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf muN0; rewrite [f]funeposneg ?integralB //; first last.
- exact: integrable_funeneg.
- exact: integrable_funepos.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funeneg.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funepos.
- exact: measurableD.
congr (_ - _); apply: ge0_negligible_integral => //; apply: (measurable_int mu).
  exact: integrable_funepos.
exact: integrable_funeneg.
Qed.

Lemma null_set_integral (N : set T) (f : T -> \bar R) :
  measurable N -> mu.-integrable N f ->
  mu N = 0 -> \int[mu]_(x in N) f x = 0.
Proof.
by move=> mN intf ?; rewrite (negligible_integral mN mN)// setDv integral_set0.
Qed.

End negligible_integral.
Add Search Blacklist "ge0_negligible_integral".

Section integrable_fune.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Local Open Scope ereal_scope.

Lemma integral_fune_lt_pinfty (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x < +oo.
Proof.
move=> intf; rewrite (funeposneg f) integralB//;
  [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite lte_add_pinfty ?integral_funepos_lt_pinfty// lteNl ltNye_eq.
by rewrite integrable_neg_fin_num.
Qed.

Lemma integral_fune_fin_num (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x \is a fin_num.
Proof.
move=> h; apply/fin_numPlt; rewrite integral_fune_lt_pinfty// andbC/= -/(- +oo).
rewrite lteNl -integralN; first exact/integral_fune_lt_pinfty/integrableN.
by rewrite fin_num_adde_defl// fin_numN integrable_neg_fin_num.
Qed.

End integrable_fune.

Section integral_counting.
Local Open Scope ereal_scope.
Variable R : realType.

Lemma counting_dirac (A : set nat) :
  counting A = \sum_(n <oo) \d_ n A :> \bar R.
Proof.
have -> : \sum_(n <oo) \d_ n A = \esum_(i in A) \d_ i A :> \bar R.
  rewrite nneseries_esum// (_ : [set _ | _] = setT); last exact/seteqP.
  rewrite [in LHS](esumID A)// !setTI [X in _ + X](_ : _ = 0) ?adde0//.
  by apply: esum1 => i Ai; rewrite /= /dirac indicE memNset.
rewrite /counting/=; case: ifPn => /asboolP finA.
  by rewrite -finite_card_dirac.
by rewrite infinite_card_dirac.
Qed.

Lemma summable_integral_dirac (a : nat -> \bar R) : summable setT a ->
  \sum_(n <oo) `|\int[\d_ n]_x a x| < +oo.
Proof.
move=> sa.
apply: (@le_lt_trans _ _ (\sum_(i <oo) `|fine (a i)|%:E)).
  apply: lee_nneseries => // n _; rewrite integral_dirac//.
  move: (@summable_pinfty _ _ _ _ sa n Logic.I).
  by case: (a n) => //= r _; rewrite indicE/= mem_set// mul1r.
move: (sa); rewrite /summable -fun_true -nneseries_esum//; apply: le_lt_trans.
by apply lee_nneseries => // n _ /=; case: (a n) => //; rewrite leey.
Qed.

Lemma integral_count (a : nat -> \bar R) : summable setT a ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
- by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
- move=> n; apply/integrableP; split=> [//|].
  by rewrite integral_dirac//= diracT mul1e (summable_pinfty sa).
- by apply: summable_integral_dirac => //; exact: summable_funeneg.
- by apply: summable_integral_dirac => //; exact: summable_funepos.
Qed.

Lemma ge0_integral_count (a : nat -> \bar R) : (forall k, 0 <= a k) ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@ge0_integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
Qed.

End integral_counting.

Section subadditive_countable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integrable_abse (D : set T) (f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D (abse \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurableT_comp.
by under eq_integral do rewrite abse_id.
Qed.

Lemma integrable_summable (F : (set T)^nat) (g : T -> \bar R):
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  summable [set: nat] (fun i => \int[mu]_(x in F i) g x).
Proof.
move=> tF mF fi.
rewrite /summable -(_ : [set _ | true] = setT); last exact/seteqP.
rewrite -nneseries_esum//.
have [mf {fi}] := integrableP _ _ _ fi.
rewrite ge0_integral_bigcup//; last exact: measurableT_comp.
apply: le_lt_trans; apply: lee_lim.
- exact: is_cvg_ereal_nneg_natsum_cond.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ _; exact: integral_ge0.
- apply: nearW => n; apply: lee_sum => m _; apply: le_abse_integral => //.
  apply: measurable_funS mf => //; [exact: bigcup_measurable|].
  exact: bigcup_sup.
Qed.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int[mu]_(x in \bigcup_i F i) g x = \sum_(i <oo) \int[mu]_(x in F i) g x)%E.
Proof.
move=> tF mF fi.
have ? : \int[mu]_(x in \bigcup_i F i) g x \is a fin_num.
  rewrite fin_numElt -(lte_absl _ +oo).
  apply: le_lt_trans (integrableP _ _ _ fi).2; apply: le_abse_integral => //.
    exact: bigcupT_measurable.
  exact: measurable_int fi.
transitivity (\int[mu]_(x in \bigcup_i F i) g^\+ x -
              \int[mu]_(x in \bigcup_i F i) g^\- x)%E.
  rewrite -integralB.
  - by apply: eq_integral => t Ft; rewrite [in LHS](funeposneg g).
  - exact: bigcupT_measurable.
  - by apply: integrable_funepos => //; exact: bigcupT_measurable.
  - by apply: integrable_funeneg => //; exact: bigcupT_measurable.
transitivity (\sum_(i <oo) (\int[mu]_(x in F i) g^\+ x -
                            \int[mu]_(x in F i) g^\- x)); last first.
  by apply: eq_eseriesr => // i; rewrite [RHS]integralE.
transitivity ((\sum_(i <oo) \int[mu]_(x in F i) g^\+ x) -
              (\sum_(i <oo) \int[mu]_(x in F i) g^\- x))%E.
  rewrite ge0_integral_bigcup//; last first.
    by apply: measurable_funepos; case/integrableP : fi.
  rewrite ge0_integral_bigcup//.
  by apply: measurable_funeneg; case/integrableP : fi.
rewrite [X in X - _]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite [X in _ - X]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite set_true -esumB//=; last 4 first.
  - apply: integrable_summable => //; apply: integrable_funepos => //.
    exact: bigcup_measurable.
  - apply: integrable_summable => //; apply: integrable_funeneg => //.
    exact: bigcup_measurable.
  - by move=> n _; exact: integral_ge0.
  - by move=> n _; exact: integral_ge0.
rewrite summable_eseries; last first.
  under [X in summable _ X]eq_fun do rewrite -integralE.
  by rewrite fun_true; exact: integrable_summable.
by congr (_ - _)%E; rewrite nneseries_esum// set_true.
Qed.

End subadditive_countable.

Section ae_ge0_le_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ae_ge0_le_integral : {ae mu, forall x, D x -> f1 x <= f2 x} ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> [N [mN muN f1f2N]]; rewrite (ge0_negligible_integral _ _ _ _ muN)//.
rewrite [leRHS](ge0_negligible_integral _ _ _ _ muN)//.
apply: ge0_le_integral; first exact: measurableD.
- by move=> t [Dt _]; exact: f10.
- exact: measurable_funS mf1.
- by move=> t [Dt _]; exact: f20.
- exact: measurable_funS mf2.
- by move=> t [Dt Nt]; move/subsetCl : f1f2N; exact.
Qed.

End ae_ge0_le_integral.

Section integral_bounded.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integral_le_bound (D : set T) (f : T -> \bar R) (M : \bar R) :
  measurable D -> measurable_fun D f -> 0 <= M ->
  {ae mu, forall x, D x -> `|f x| <= M} ->
  \int[mu]_(x in D) `|f x| <= M * mu D.
Proof.
move=> mD mf M0 dfx; rewrite -integral_cst => //.
by apply: ae_ge0_le_integral => //; exact: measurableT_comp.
Qed.

End integral_bounded.
Arguments integral_le_bound {d T R mu D f} M.

Section integral_ae_eq.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Let integral_measure_lt (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  mu (D `&` [set x | g x < f x]) = 0.
Proof.
move=> itf itg fg; pose E j := D `&` [set x | f x - g x >= j.+1%:R^-1%:E].
have msf := measurable_int _ itf.
have msg := measurable_int _ itg.
have mE j : measurable (E j).
  rewrite /E; apply: emeasurable_fun_le => //.
  by apply/(emeasurable_funD msf)/measurableT_comp => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite -measure_le0.
  have fg0 : \int[mu]_(x in E j) (f \- g) x = 0.
    rewrite integralB//; last 2 first.
      by apply: integrableS itf => //; exact: subIsetl.
      by apply: integrableS itg => //; exact: subIsetl.
    rewrite fg//; last apply: subIsetl.
    rewrite subee// fin_num_abs (le_lt_trans (le_abse_integral _ _ _))//.
      by apply: measurable_funS msg => //; first exact: subIsetl.
    apply: le_lt_trans (integrableP _ _ _ itg).2.
    apply: ge0_subset_integral => //; first exact: measurableT_comp msg.
    exact: subIsetl.
  suff : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    by rewrite fg0 mule0.
  apply: (@le_trans _ _ (j.+1%:R%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)).
    by rewrite integral_cst// muleA -EFinM divff// mul1e.
  rewrite lee_pmul//; first exact: integral_ge0.
  apply: ge0_le_integral => //; [| |by move=> x []].
  - by move=> x [_/=]; exact: le_trans.
  - apply: emeasurable_funB.
    + by apply: measurable_funS msf => //; exact: subIsetl.
    + by apply: measurable_funS msg => //; exact: subIsetl.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x [Dx /= ifg]; split => //.
  by move: ifg; apply: le_trans; rewrite lee_fin lef_pV2// ?posrE// ler_nat.
rewrite set_lte_bigcup.
have /cvg_lim h1 : (mu \o E) x @[x --> \oo]--> 0.
  by apply: cvg_near_cst; exact: nearW.
have := @nondecreasing_cvg_mu _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
by move/cvg_lim => h2; rewrite setI_bigcupr -h2// h1.
Qed.

Lemma integral_ae_eq (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> measurable_fun D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  ae_eq mu D f g.
Proof.
move=> fi mg fg; have mf := measurable_int _ fi; have gi : mu.-integrable D g.
  apply/integrableP; split => //; apply/abse_integralP => //; rewrite -fg//.
  by apply/abse_integralP => //; case/integrableP : fi.
have mugf : mu (D `&` [set x | g x < f x]) = 0 by apply: integral_measure_lt.
have mufg : mu (D `&` [set x | f x < g x]) = 0.
  by apply: integral_measure_lt => // E ED mE; rewrite fg.
have h : ~` [set x | D x -> f x = g x] = D `&` [set x | f x != g x].
  apply/seteqP; split => [x/= /not_implyP[? /eqP]//|x/= [Dx fgx]].
  by apply/not_implyP; split => //; exact/eqP.
apply/negligibleP.
  by rewrite h; apply: emeasurable_fun_neq.
rewrite h set_neq_lt setIUr measureU//.
- by rewrite [X in X + _]mufg add0e [LHS]mugf.
- exact: emeasurable_fun_lt.
- exact: emeasurable_fun_lt.
- apply/seteqP; split => [x [[Dx/= + [_]]]|//].
  by move=> /lt_trans => /[apply]; rewrite ltxx.
Qed.

End integral_ae_eq.

Section lebesgue_measure_integral.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma integral_Sset1 (f : R -> \bar R) A (r : R) : A `<=` [set r] ->
  (\int[mu]_(x in A) f x = 0)%E.
Proof.
move=> Ar; have [->|->] := subset_set1 Ar; first by rewrite integral_set0.
rewrite (eq_integral (cst (f r)))/=; last by move=> x; rewrite inE/= => ->.
by rewrite integral_cst//= lebesgue_measure_set1 mule0.
Qed.

Lemma integral_set1 (f : R -> \bar R) (r : R) : \int[mu]_(x in [set r]) f x = 0.
Proof. exact: (integral_Sset1 _ (@subset_refl _ _)). Qed.

Lemma ge0_integral_closed_ball c (r : R) (r0 : (0 < r)%R) (f : R -> \bar R) :
  measurable_fun (closed_ball c r : set R) f ->
  (forall x, x \in closed_ball c r -> 0 <= f x) ->
  \int[mu]_(x in closed_ball c r) f x = \int[mu]_(x in ball c r) f x.
Proof.
move=> mf f0.
rewrite closed_ball_ball//= ge0_integral_setU//=; last 4 first.
  by apply: measurableU => //; exact: measurable_ball.
  by move: mf; rewrite closed_ball_ball.
  by move=> x xcr; rewrite f0// closed_ball_ball// inE.
  apply/disj_setPLR => x [->|]/=; rewrite /ball/=.
    by apply/eqP; rewrite (addrC _ r) -subr_eq -addrA addrC subrK eqNr gt_eqF.
  by move=> /[swap] ->; rewrite opprD addNKr normrN gtr0_norm// ltxx.
rewrite ge0_integral_setU//=.
- by rewrite !integral_set1//= add0e adde0.
- exact: measurable_ball.
- apply: measurable_funS mf; first exact: measurable_closed_ball.
  by move=> x; rewrite closed_ball_ball//; left.
- by move=> x H; rewrite f0// closed_ball_ball// inE/=; left.
- by apply/disj_setPRL => x /[swap] ->; rewrite /ball/= subKr gtr0_norm// ltxx.
Qed.

Lemma integral_setD1_EFin (f : R -> R) r (D : set R) :
  measurable (D `\ r) -> measurable_fun (D `\ r) f ->
  \int[mu]_(x in D `\ r) (f x)%:E = \int[mu]_(x in D) (f x)%:E.
Proof.
move=> mD mfl; have [Dr|NDr] := pselect (D r); last by rewrite not_setD1.
rewrite -[in RHS](@setD1K _ r D)// integral_setU_EFin//=.
- by rewrite integral_set1// add0e.
- by apply/measurable_funU => //; split => //; exact: measurable_fun_set1.
- by rewrite disj_set2E setDIK.
Qed.

Lemma integral_itv_bndo_bndc (a : itv_bound R) (r : R) (f : R -> R) :
  measurable_fun [set` Interval a (BLeft r)] f ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x)%:E =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x)%:E.
Proof.
move=> mf; have [ar|ar] := leP a (BLeft r).
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1r.
- by rewrite !set_itv_ge// -leNgt// ltW.
Qed.

Lemma integral_itv_obnd_cbnd (r : R) (b : itv_bound R) (f : R -> R) :
  measurable_fun [set` Interval (BRight r) b] f ->
   \int[mu]_(x in [set` Interval (BRight r) b]) (f x)%:E =
   \int[mu]_(x in [set` Interval (BLeft r) b]) (f x)%:E.
Proof.
move=> mf; have [rb|rb] := leP (BRight r) b.
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1l.
- by rewrite !set_itv_ge// -leNgt -?ltBRight_leBLeft// ltW.
Qed.

Lemma integral_itv_bndoo (x y : R) (f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in `]x, y[) (f z)%:E.
Proof.
have [xy|yx _|-> _] := ltgtP x y; last 2 first.
- rewrite !set_itv_ge ?integral_set0//=.
  + by rewrite bnd_simp le_gtF// ltW.
  + by move: b0 b1 => [|] [|]; rewrite bnd_simp ?lt_geF// le_gtF// ltW.
- by move: b0 b1 => [|] [|]; rewrite !set_itvE ?integral_set0 ?integral_set1.
move=> mf.
transitivity (\int[mu]_(z in [set` Interval (BSide b0 x) (BLeft y)]) (f z)%:E).
  case: b1 => //; rewrite -integral_itv_bndo_bndc//.
  by case: b0 => //; exact: measurable_fun_itv_obnd_cbnd.
by case: b0 => //; rewrite -integral_itv_obnd_cbnd.
Qed.

Lemma eq_integral_itv_bounded (x y : R) (g f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f -> measurable_fun `]x, y[ g ->
  {in `]x, y[, f =1 g} ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (g z)%:E.
Proof.
move=> mf mg fg.
rewrite integral_itv_bndoo// (@integral_itv_bndoo _ _ g)//.
by apply: eq_integral => z; rewrite inE/= => zxy; congr EFin; exact: fg.
Qed.

End lebesgue_measure_integral.
Arguments integral_Sset1 {R f A} r.
