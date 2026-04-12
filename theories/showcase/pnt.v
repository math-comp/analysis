From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import archimedean mathcomp_extra unstable.
From mathcomp Require Import classical_sets boolp topology measure_function.
From mathcomp Require Import set_interval normed_module.
From mathcomp Require Import pseudometric_normed_Zmodule measurable_function.
From mathcomp Require Import measurable_realfun measurable_structure .
From mathcomp Require Import derive lebesgue_measure lebesgue_integral ftc.
From mathcomp Require Import ereal sequences reals realfun real_interval.
Import Order.POrderTheory GRing.Theory Num.Theory.

(**md**************************************************************************)
(* # The Prime Number Theorem                                                 *)
(*                                                                            *)
(* This file aims at formalizing Daboussi's proof of the prime number theorem.*)
(* The main theorem proved so far is the divergence of the sum of the         *)
(* reciprocals of the prime numbers.                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*             prime_seq == the sequence of prime numbers                     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Local Open Scope set_scope.
Local Open Scope nat_scope.

Section prime_seq.

Let next_prime_subproof n : {i : 'I_(n`! - n).+1 | prime (n.+1 + i)}.
Proof.
suff: [exists i : 'I_(n`! - n).+1, prime (n.+1 + (tnth (ord_tuple _) i))].
  rewrite (existsb_tnth (fun x : 'I_(n`! - n).+1 => prime (n.+1 + x))).
  move=> /(nth_find ord0) ni.
  by eexists; apply: ni.
apply/existsP/not_existsP => noprime.
set q := pdiv n`!.+1.
have qprime : prime q by apply/pdiv_prime/fact_gt0.
have [qlei|iltq] := leqP q n.
  have /dvdn_fact : 0 < q <= n by rewrite pdiv_gt0.
  by rewrite (@dvdn_add_eq _ _ 1) ?Euclid_dvd1// addn1 pdiv_dvd.
have qlt : q - n.+1 < (n`! - n).+1.
  by rewrite -subSn// subSS -subSn ?fact_geq//; exact/leq_sub2r/pdiv_leq.
apply: (noprime (Ordinal qlt)).
by rewrite tnth_ord_tuple subnKC// ltnW.
Qed.

Definition next_prime n : nat :=
  n.+1 + [arg min_(i < val (next_prime_subproof n) | prime (n.+1 + i)) val i].

Lemma prime_next_prime n : prime (next_prime n).
Proof.
by rewrite /next_prime; case: arg_minnP => //; case: next_prime_subproof.
Qed.

Lemma next_prime_min (i j : nat) : i < j < next_prime i -> ~~ prime j.
Proof.
rewrite /next_prime.
case: arg_minnP => [|k kP kmin]; first by case: next_prime_subproof.
move=> /andP[ij].
rewrite -(ltn_subLR _ ij) => jk.
have jlt := ltn_trans jk (ltn_ord k).
rewrite -[j](subnKC ij); apply/negP => jP.
move: (kmin (Ordinal jlt) jP) => /= /(leq_trans jk).
by rewrite ltnn.
Qed.

Lemma next_prime_lt n : n < next_prime n.
Proof.
rewrite /next_prime.
case: arg_minnP => [|i _ _]; first by case: next_prime_subproof.
exact: leq_addr.
Qed.

Definition prime_seq n : nat := iter n next_prime 2.

Lemma leq_prime_seq : {mono prime_seq : m n / m <= n}.
Proof.
move=> m n.
apply: (@Order.NatMonotonyTheory.incn_inP _ nat predT) => // {m n} [n /= _ _].
exact: next_prime_lt.
Qed.

Lemma mem_prime_seq (p : nat) : p \in range prime_seq = prime p.
Proof.
apply/idP/idP => [|primep].
  by rewrite inE => -[] [|n] _ <- //=; apply: prime_next_prime.
case: (@Order.TotalTheory.arg_maxP _ _ 'I_p.+1 ord0
    (fun m => prime_seq m <= p) prime_seq) => /= [|n pgepsi pptargmax].
  exact: prime_gt1.
have pltpsni1: p < prime_seq n.+1.
  move: (valP n). rewrite leq_eqVlt => /orP [|nltp].
    rewrite eqSS => /eqP ->.
    exact/mono_leq_infl/leq_prime_seq.
  have := contra (pptargmax (Ordinal nltp)).
  rewrite [(_ <= _)%O](leq_prime_seq (Ordinal nltp) n) ltnn => /(_ erefl).
  by rewrite ltnNge.
move: pgepsi.
rewrite leq_eqVlt => /predU1P[<-|psnltp]; first by rewrite inE.
have := @next_prime_min (prime_seq n) p; rewrite psnltp pltpsni1 => /(_ erefl).
by rewrite primep.
Qed.

End prime_seq.

Section dvg_sum_inv_prime_seq.

Let P (k N : nat) :=
  [set n : 'I_N.+1 | all (fun p => p < prime_seq k) (primes n)]%SET.
Let G (k N : nat) := ~: P k N.

Let cardPcardG k N : #|G k N| + #|P k N| = N.+1.
Proof.
rewrite addnC.
have : (P k N) :|: (G k N) = [set : 'I_N.+1]%SET by rewrite finset.setUCr.
rewrite -cardsUI finset.setICr cards0.
by rewrite -[X in _ + _ = X]card_ord addn0 -cardsT => ->.
Qed.

Let cardG (R : realType) (k N : nat) :
  (\sum_(k <= k0 <oo) ((prime_seq k0)%:R^-1 : R)%:E < (2^-1)%:E)%E
  -> N > 0 -> (#|G k N|%:R < (N%:R / 2) :> R)%R.
Proof.
set E := fun i => [set n : 'I_N.+1 | (prime_seq i) \in (primes n)].
set Parts := fun i => [set ([set x in [seq (insubd ord0 x : 'I_N.+1) |
  x <- iota ((val y).+1 - (prime_seq i)) (prime_seq i)]]
  : {set 'I_N.+1}) | y in (E i)]%SET.
move=> Rklthalf Nneq0.
suff cardEi : forall i, k <= i ->
    (#|E i|%:R <= N%:R / (prime_seq i)%:R :>R)%R => [|i klti].
  have -> : G k N = \bigcup_(k <= i < N.+1) E i.
    apply/eqP; rewrite finset.eqEsubset; apply/andP; split; last first.
      apply/fintype.subsetP => x.
      rewrite big_geq_mkord => /bigcupP[i /= klei].
      rewrite inE => pidvdx.
      rewrite !inE -has_predC; apply/hasP; exists (prime_seq i) => //=.
      by rewrite -leqNgt leq_prime_seq.
    apply/fintype.subsetP => /= x.
    rewrite !inE -has_predC => /hasP[p/=].
    rewrite mem_primes => /andP[+ /andP[xneq0 pdvdx]].
    rewrite -mem_prime_seq inE => /= -[i _ peqpi].
    move: peqpi pdvdx => <- {p} pidvdx.
    rewrite -leqNgt => pklepi.
    rewrite big_geq_mkord; apply/bigcupP.
    have ileqN : i < N.+1.
      apply: (leq_ltn_trans _ (ltn_ord x)).
      apply: (leq_trans _ (dvdn_leq xneq0 pidvdx)).
      exact/mono_leq_infl/leq_prime_seq.
    exists (Ordinal ileqN) => /=; first by rewrite -leq_prime_seq.
    by rewrite inE mem_primes xneq0 pidvdx/= andbT -mem_prime_seq inE.
  apply: (le_lt_trans (ler_wpMn2l ler01 (card_big_setU _ _ E))).
  apply: (@le_lt_trans _ _ (N%:R * \sum_(k <= i < N.+1) (prime_seq i)%:R^-1)%R).
    rewrite mulr_sumr raddf_sum /= ler_sum_nat// => i /andP[+ _].
    exact: cardEi.
  rewrite -lte_fin.
  apply: (@le_lt_trans _ _ (N%:R%:E * \sum_(k <= i <oo) (prime_seq i)%:R^-1%:E)%E).
    rewrite EFinM lee_pmul ?lee_fin//; first by rewrite sumr_ge0.
    rewrite raddf_sum; apply: nneseries_lim_ge => n _ _.
    by rewrite lee_fin invr_ge0.
  rewrite EFinM -lte_pdivrMl ?ltr0n// muleA -EFinM mulVf ?mul1e//.
  by rewrite pnatr_eq0 -lt0n.
rewrite ler_pdivlMr.
  rewrite ltr0n.
  have : prime_seq i \in range prime_seq by rewrite inE.
  by rewrite mem_prime_seq; apply: prime_gt0.
have Eigtpi x3 : x3 \in E i -> prime_seq i - x3.+1 = 0.
  have OnotinE : ord0 \notin E i => [|x3inEi]; first by rewrite /E inE.
  apply/eqP; rewrite subn_eq0; apply/leqW/dvdn_leq.
    case: x3 x3inEi => /= x3; have [-> N1lt0|//] := posnP x3.
    by rewrite /E inE.
  move: x3inEi; rewrite /E inE mem_primes -mem_prime_seq mem_range.
  by case: (x3 > 0).
have: finset.trivIset (Parts i).
  apply/finset.trivIsetP => _ _ /imsetP [] x xinEi -> /imsetP [] y yinEi ->.
  wlog : x y xinEi yinEi / x <= y.
    move: (leq_total x y) => /orP [xley Hw| ylex Hw].
      exact: (Hw x y).
    by rewrite eq_sym disjoint_sym; apply: (Hw y x).
  rewrite -[x <= y]/(x <= y)%O.
  rewrite le_eqVlt => /predU1P[->|xy _]; first by rewrite eqxx.
  rewrite -setI_eq0 -finset.subset0.
  apply/fintype.subsetP => x0.
  rewrite finset.in_setI !inE => /andP[] /mapP[]/= x1 x1x -> /mapP[]/= x2 x2y.
  move=> /(congr1 val); rewrite !val_insubd; move: x1x x2y.
  rewrite !mem_iota !addnCB (Eigtpi x) // (Eigtpi y) // !addn0 !ltnS.
  have xiN (a : 'I_N.+1) (b : nat) : b <= a -> b <= N.
    by move/leq_trans; apply; rewrite -ltnS.
  move=> /andP [] _ /[dup] + /xiN -> /andP [] + /xiN -> x1eqx2.
  rewrite -x1eqx2 => /(leq_trans _)/[apply].
  rewrite -(leq_add2r (prime_seq i)) addnCB Eigtpi// addn0.
  rewrite -(@leq_sub2rE x) ?leq_addr// subDnCA// subnn addn0 (subSn (ltW xy)).
  rewrite ltnNge dvdn_leq// ?subn_gt0//.
  have dvdni z : z \in E i -> prime_seq i %| z.
    by rewrite inE mem_primes => /andP[] _ /andP[].
  by apply: dvdn_sub; apply: dvdni.
set i1toN := [set : 'I_N.+1] :\ ord0.
have cardNeqN: #|i1toN| = N.
  rewrite /i1toN. apply/eqP.
  rewrite -(eqn_add2r (ord0 \in [set :'I_N.+1]%SET)). apply/eqP.
  have ord0inI: ord0 \in [set: 'I_N.+1]%SET by rewrite inE.
  rewrite [in RHS]ord0inI [N + 1]addn1 addnC.
  by rewrite -(cardsD1 ord0 [set: 'I_N.+1]) cardsT card_ord.
rewrite -[X in (_ <= X%:R)%R]cardNeqN /finset.trivIset => /eqP.
have cardeltPi: forall X, X \in Parts i -> #|X| = (prime_seq i) => [X|].
  rewrite /(Parts i) => /finset.imsetP [] x xinEi -> {X}.
  rewrite cardsE.
  suff /card_uniqP -> : uniq ([seq insubd ord0 x0 |
      x0 <- iota ((\val x).+1 - prime_seq i) (prime_seq i)] : seq 'I_N.+1).
    by rewrite size_map size_iota.
  apply/(uniqP ord0) => x1 y1 /=.
  rewrite !inE size_map size_iota => x1lt y1lt.
  rewrite !(nth_map 0) ?size_iota //.
  rewrite !nth_iota => // /(congr1 val). rewrite !val_insubd /=.
  rewrite [X in X < _]addBnA.
  - by rewrite -subn_eq0; apply/eqP/Eigtpi.
  - exact: ltnW.
  rewrite -(@prednK (prime_seq i - x1)) ?subn_gt0// !subSS.
  rewrite (leq_ltn_trans _ (ltn_ord x)); first exact: sub_ord_proof.
  rewrite [X in X < _]addBnA.
  - by rewrite -subn_eq0; apply/eqP/Eigtpi.
  - exact: ltnW.
  rewrite -(@prednK (prime_seq i - y1)) ?subn_gt0 // !subSS.
  suff -> : x - (prime_seq i - y1).-1 < N.+1 by apply: addnI.
  exact/(leq_ltn_trans _ (ltn_ord x))/sub_ord_proof.
under eq_bigr do rewrite cardeltPi//.
rewrite sum_nat_const.
suff -> : #|Parts i| = #|E i|.
  suff Pisubi1toN : finset.cover (Parts i) \subset i1toN => [eqcard|].
    suff: #|E i| * prime_seq i <= #|i1toN| by rewrite -natrM ler_nat.
      exact: (leq_trans (eq_leq eqcard) (subset_leq_card Pisubi1toN)).
  rewrite /(Parts i) cover_imset. apply/bigcupsP => i0 i0inEi.
  apply/fintype.subsetP => x.
  case: (boolP (x == ord0)) => [/eqP ->|xneq0 _]; last first.
    by rewrite /i1toN inE !inE xneq0.
  rewrite inE /in_mem /= => /mapP /= [] x0.
  rewrite mem_iota subnK => [|/andP [] x0b1 x0b2].
    by rewrite -subn_eq0; apply/eqP /Eigtpi.
  have x0b3: x0 < N.+1 => [|/(congr1 val)].
    exact: (leq_ltn_trans _ (ltn_ord i0)).
  rewrite val_insubd x0b3 => /= /eqP.
  suff xpos: x0 > 0  by rewrite ltn_eqF.
  apply: (leq_ltn_trans (leq0n (i0.+1 - prime_seq i).-1)).
  rewrite -(ltn_add2r 1) !addn1 prednK // subn_gt0 ltnS.
  rewrite dvdn_leq //; last first.
    move: i0inEi.
    by rewrite /E inE mem_primes -mem_prime_seq mem_range; case: (i0 > 0).
  case: i0 i0inEi x0b1 x0b2 => /= i0.
  case: (posnP i0) => // -> N1lt0.
  by rewrite /E inE.
rewrite /(Parts i) card_in_imset // /injective => x1 x2.
wlog: x1 x2 / x1 <= x2 => [Hw|x1lex2 x1inEi x2inEi enseq].
  move: (leq_total x1 x2) => /orP [] => // [|x2lex1 x1inEi x2inEi /eqP].
    exact: (Hw x1 x2).
  rewrite eq_sym => /eqP enseq.
  apply/eqP. rewrite eq_sym. apply/eqP.
  exact: (Hw x2 x1).
apply: le_anti. apply/andP. split; first exact: x1lex2.
have: x2 \in [set x in [seq insubd ord0 x0
    | x0 <- iota ((\val x1).+1 - prime_seq i) (prime_seq i)]].
  rewrite enseq inE /in_mem /=. apply/mapP => /=.
  exists x2; last by apply: val_inj; rewrite !val_insubd ltn_ord.
  rewrite mem_iota subnK; first by rewrite -subn_eq0; apply/eqP /Eigtpi.
  by rewrite ltnSn -ltnS ltn_subrL prime_gt0 // -mem_prime_seq mem_range.
rewrite inE /in_mem /= => /mapP /= [] x3.
rewrite mem_iota subnK => [|/andP [] x3b1 x3b2 /(congr1 val)].
  by rewrite -subn_eq0; apply/eqP /Eigtpi.
have x3b3: x3 < N.+1 by apply: (leq_ltn_trans _ (ltn_ord x1)).
rewrite val_insubd x3b3 /= => x2eqx3. move: x3b2.
by rewrite ltnS -x2eqx3.
Qed.

Let cardP (k : nat) : #|P k (2 ^ (k.*2 + 2))| <= (2 ^ (k.*2 + 1)).+1.
Proof.
set N := 2 ^ (k.*2 + 2).
pose P' k N := P k N :\ ord0.
set A := k.-tuple bool.
set B := 'I_(2 ^ (k + 1)).+1.
pose a n i := odd (logn (prime_seq i) n).
have eqseq : forall n k, n < k ->
    [seq i <- [seq prime_seq i | i <- index_iota 0 k]  | i  \in primes n]
    = primes n.
  move=> + k0; case=> [|n nlek]; first by rewrite filter_pred0.
  apply: lt_sorted_eq => [||elt].
  - apply: lt_sorted_filter.
    rewrite sorted_map.
    apply: (@sub_sorted _ ltn); last exact: iota_ltn_sorted.
    by rewrite ltEnat => i j /=; rewrite (leqW_mono leq_prime_seq).
  - exact: sorted_primes.
  rewrite mem_filter andb_idr// mem_primes -mem_prime_seq => /andP[].
  rewrite inE => -[] i _ <- /andP[] _ /dvdn_leq/wrap[]// idn.
  apply: map_f; rewrite mem_iota leq0n/= add0n subn0.
  exact/(leq_ltn_trans _ nlek)/(leq_trans _ idn)/mono_leq_infl/leq_prime_seq.
have binB (n : 'I_N.+1) :
    (\prod_(i < k) (prime_seq i) ^ (logn (prime_seq i) n)./2) <
    (2 ^ (k + 1)).+1.
  have [->/=|nneq0] := eqVneq n ord0.
    under eq_bigr do rewrite logn0 -divn2 div0n expn0.
    by rewrite big1_eq -[X in _ < X]addn1 -[X in X < _]add0n ltn_add2r expn_gt0.
  rewrite -ltn_sqr expn_prod.
  under eq_bigr do rewrite -expnM muln2 halfK.
  apply: (@leq_ltn_trans
      (\prod_(i < k) prime_seq i ^ (logn (prime_seq i) n))).
    apply: leq_prod => i _. rewrite leq_exp2l; last exact: leq_subr.
    by apply: prime_gt1; rewrite -mem_prime_seq inE.
  apply: (@leq_ltn_trans n); last first.
    apply: (ltn_trans (ltn_ord n)); rewrite /N.
    rewrite -[X in X ^ 2]addn1 sqrnD exp1n addn1 -expnM mulnDl.
    rewrite muln1 -expnS addn1 mul1n [in X in _ < X]mulnC.
    by rewrite mul2n -addn1 leq_add2l// expn_gt0.
  rewrite [X in _ <= X]prod_prime_decomp ?lt0n// prime_decompE big_map /=.
  rewrite -(big_mkord predT (fun i =>
    (prime_seq i) ^ logn (prime_seq i) n)) -(big_map prime_seq predT
    (fun i => i ^ logn i n)) /=.
  rewrite (bigID (mem (primes n))) /=.
  rewrite [X in _ * X]big1 => [[//|][//|] i ip|].
    apply/eqP; rewrite -(expn0 i.+2) eqn_exp2l//.
    by move: ip; rewrite -logn_gt0 lt0n negbK.
  rewrite muln1 -big_filter.
  have [nltk|klen] := ltnP n k; first by rewrite (eqseq n).
  rewrite -[in X in _ <= X](eqseq n n.+1); first exact: ltnSn.
  rewrite -[X in index_iota _ X.+1](subnKC (leq_trans klen (ltnSn n))).
  rewrite -addnS -subSn//.
  rewrite !big_filter /index_iota !subn0 iotaD map_cat big_cat add0n /=.
  by apply/leq_pmulr/prodn_gt0 => i; exact: pfactor_gt0.
set f : 'I_N.+1 -> A * B := fun n => ([tuple a n i  | i < k], Ordinal (binB n)).
set g : A * B -> nat := fun c => let (a, b) := c in
  b ^ 2 * \prod_(i < k) (prime_seq i) ^ (tnth a i).
have finj x y : x \in P' k N -> y \in P' k N -> f x = f y -> x = y.
  move=> xinPkN yinPkN /(congr1 g).
  suff: forall x, x \in P' k N -> g (f x) = x.
    by move=> /[dup] /(_ _ xinPkN) -> /(_ _ yinPkN) ->; apply: val_inj.
  move=> {yinPkN y} {}x {}xinPkN /=.
  rewrite expn_prod.
  under eq_bigr do rewrite -expnM muln2 halfK.
  rewrite -big_split /=.
  under eq_bigr => i _.
    rewrite -expnD tnth_mktuple /a subnK.
      by case: (boolP (odd (logn (prime_seq i) x))); first exact: odd_gt0.
    over.
  have [xeq0|xneq0] := eqVneq x ord0.
    by move: xeq0 xinPkN => ->; rewrite /P' !inE.
  rewrite [RHS]prod_prime_decomp ?lt0n// prime_decompE big_map /=.
  rewrite [in LHS](bigID (fun i : 'I_k => prime_seq i \in primes x)) /=.
  under [X in _ * X = _]eq_bigr => i.
    rewrite mem_primes lognE => /negbTE ->.
    rewrite expn0; over.
  rewrite big1_eq muln1 -(big_map _ (fun i => prime_seq i \in primes x)
    (fun i => prime_seq i ^ logn (prime_seq i) x))
    -(big_map _ _ (fun j => j ^ logn j x)) -big_filter.
  apply: congr_big => //.
  rewrite -map_comp functions.compE.
  apply: lt_sorted_eq => [||elt].
  - apply: lt_sorted_filter.
    rewrite map_comp sorted_map -[X in map _ X]filter_predT val_enum_ord.
    apply: (@sub_sorted _ ltn); last exact: iota_ltn_sorted.
    rewrite ltEnat => i j /=.
    by rewrite (leqW_mono leq_prime_seq).
  - exact: sorted_primes.
  rewrite mem_filter; apply: andb_idr.
  move: xinPkN; rewrite /P' /P inE => /andP[_].
  rewrite inE => /allP primesxlepk eltinprimesx.
  have [] : prime elt /\ elt < prime_seq k.
    split; last exact: primesxlepk.
    by apply/(@allP _ _ (primes x)) => //; exact: all_prime_primes.
  rewrite -mem_prime_seq inE => /= -[i _ <-] pilepk.
  rewrite map_comp; apply: map_f.
  rewrite -[X in map _ X]filter_predT val_enum_ord mem_iota /= add0n.
  by rewrite -(leqW_mono leq_prime_seq).
have -> : P k N = P' k N :|: [set ord0].
  by rewrite /P' finset.setUC finset.setD1K // inE.
rewrite finset.setUC cardsU1 [in X in X + _]/P' !inE /= add1n ltnS.
rewrite -(card_in_imset finj).
have imfleqAB :
    #|[set f x  | x in P' k N]| <= #|finset.setX [set: A] (~: [set ord0 : B])|.
  apply/subset_leq_card/fintype.subsetP => y.
  rewrite !inE => /imsetP [] x xinPkN -> /=.
  apply: (contra_not_neq (@congr1 _ _ val _ _)) => /=.
  apply/eqP; rewrite -lt0n; apply: prodn_gt0 => i.
  by rewrite expn_gt0 prime_gt0//= -mem_prime_seq inE.
apply: (leq_trans imfleqAB).
rewrite cardsX cardsE card_tuple card_bool cardsC1 card_ord.
by rewrite -expnD addnA addnn.
Qed.

Theorem dvg_sum_inv_prime_seq (R : realType) :
  (\sum_(0 <= i < n) (((prime_seq i)%:R : R)^-1)%:E)%R @[n --> \oo] --> +oo%E.
Proof.
set un := fun i => (((prime_seq i)%:R : R)^-1)%:E.
set Sn := fun n => (\sum_(0 <= i < n) (un i))%R.
have unpos n : 0 <= n -> true -> (0 <= un n)%E => [_ _|].
  by rewrite /un lee_fin invr_ge0 ler0n.
have := is_cvg_nneseries unpos.
have := leey (limn Sn).
rewrite le_eqVlt => /predU1P[-> //|].
have := nneseries_ge0 unpos.
move leqlimnSn : (limn Sn) => l.
case: l leqlimnSn => // l leqlimnSn _ _ /subsetP llimnSn.
have /llimnSn : `](l - (1/2))%:E, (l + (1/2))%:E[ \in nbhs (l%:E).
  rewrite inE; exists (1/2)%R => /=; first exact: divr_gt0.
  exact/subset_ball_prop_in_itv.
rewrite inE => -[] k /= _ /subsetP/(_ k).
set N := 2 ^ (k.*2 + 2).
set PN := P k N.
set GN := G k N.
rewrite inE /= leqnn set_interval.set_itvoo inE /= EFinB EFinD -leqlimnSn.
move=> /(_ erefl) /andP[+ _].
rewrite lte_subel_addl; first by rewrite leqlimnSn.
rewrite -lteBlDr; first exact/sum_fin_numP.
rewrite (nneseries_split _ k); first by move=> k0 _; exact: unpos.
rewrite /Sn add0n addrAC subee; first exact/sum_fin_numP.
rewrite add0e div1r => Rklthalf.
suff: N.+1 < N.+1 by rewrite ltnn.
rewrite -[X in X < _](cardPcardG k N).
have Neq : N./2 + (2 ^ (k.*2 + 1)).+1 = N.+1.
  by rewrite /N 2!addnS expnS mul2n doubleK addnn.
rewrite -[X in _ < X]Neq -addSn.
apply: leq_add; last exact: cardP.
rewrite -(ltr_nat R).
have -> : (N./2%:R = N%:R / 2 :> R)%R.
  by rewrite /N addnS expnS [in LHS]mul2n doubleK natrM mulrC mulKf.
by apply: (@cardG R) => //; rewrite /N expn_gt0.
Qed.

End dvg_sum_inv_prime_seq.

Lemma Abel_discrete (R : comPzRingType) (a b : nat -> R) (n p : nat) :
  p < n -> let A n := (\sum_(0 <= k < n.+1) a k)%R in
  (\sum_(p.+1 <= k < n.+1) (a k) * (b k) = A n * b n - A p * b p.+1
    + \sum_(p.+1 <= k < n) A k * (b k - b k.+1))%R.
Proof.
move=> ngtp A.
rewrite big_nat_cond.
under eq_bigr => k /andP [] /andP [] pk _ _.
  rewrite (_ : a k = (A k - A k.-1)%R) ?mulrBl.
    by rewrite /A (ltn_predK pk) // big_nat_recr //= [RHS]addrC addKr.
  over.
rewrite -big_nat_cond.
under [in RHS]eq_bigr do rewrite mulrBr.
rewrite !big_split !sumrN /= [X in (_ - X)%R]big_add1 -pred_Sn.
under [X in (_ - X)%R]eq_bigr do rewrite -pred_Sn.
by rewrite [RHS](AC (2*2) ((3*1)*(2*4)))/= -big_nat_recr//= -opprD -big_ltn.
Qed.

Local Notation "\int_( x 'in' D ) F" := (\int[lebesgue_measure]_(x in D) F)%R
  (at level 36, F at level 36, x, D at level 50).

Lemma Abel_continuous (R : realType) (x y : R^o) (f : R^o -> R^o)
    (a : nat -> R) : (0 <= y <= x)%R -> derivable_oo_LRcontinuous f y x ->
  {within `[y, x] : set R^o, continuous f^`()} ->
  let A := fun x : R => (\sum_(0 <= n < `|floor x|.+1) a n)%R in
  (\sum_(`|floor y|.+1 <= n < `|floor x|.+1) a n * f n%:R =
  A x * f x - A y * f y - \int_(t in `[y, x]) (A t * f^`() t))%R.
Proof.
move=> /andP [] y0 /[dup] /(le_trans y0) x0 /[dup] yx.
rewrite le_eqVlt => /orP[/eqP <-|yx'] fderivable fC1 A.
  by rewrite big_geq// subrr set_itv1 Rintegral_set1 subr0.
have x0' := le_lt_trans y0 yx'. 
set p := `|floor y|; set q := `|floor x|.
have floory0: (0 <= floor y)%R by rewrite floor_ge0.
have floorx0: (0 <= floor x)%R by rewrite floor_ge0.
have py : (p%:R <= y)%R.
  by rewrite -mulrz_nat natz gez0_abs ?floor_ge0// floor_le. 
have yp : (y < p.+1%:R)%R.
  by rewrite -natr1 -mulrz_nat natz -intrD1 gez0_abs// floorD1_gt.
have qx : (q%:R <= x)%R.
  by rewrite -mulrz_nat natz gez0_abs ?floor_ge0// floor_le. 
have xq : (x < q.+1%:R)%R.
  by rewrite -natr1 -mulrz_nat natz -intrD1 gez0_abs// floorD1_gt.
have AteqAn: forall n t, (n%:R <= t < n.+1%:R)%R -> A t = A n%:R.
  move=> n t /andP [] tb1 tb2.
  have: floor t = n.
    apply /floor_def /andP. split=> //.
    by rewrite -natz natr1 mulrz_nat.
  suff: @floor R n%:R = n by rewrite /A => -> ->.
  by apply /(@intr_inj R) /eqP; rewrite -[_ == _]intrEfloor.
have pleq: p <= q by apply: lez_abs2 => //; apply: le_floor.
have fi:  lebesgue_measure.-integrable `[y, x] (EFin \o f^`()).
  by apply: continuous_compact_integrable => //; apply: segment_compact.
have fcontinuous: {in `]y, x[ : set R^o, continuous f}.
  rewrite -continuous_open_subspace //. apply: derivable_within_continuous.
  by case: fderivable.
have tfct1t2 : forall t1 t2, (y <= t1)%R -> (t1 <= t2)%R -> (t2 <= x)%R ->
    \int_(x in `[t1, t2]) f^`() x = (f t2 - f t1)%R.
  move=> t1 t2 ylet1.
  rewrite /Rintegral le_eqVlt => /orP [/eqP ->|t1ltt2 t2lex].
    by rewrite subrr set_itv1 (integral_Sset1 t2).
  rewrite (@continuous_FTC2 _ _ f)//.
    by apply/(continuous_subspaceW _ fC1)/subset_itv; rewrite bnd_simp.
  split.
  - apply: (@in1_subset_itv _ _ _ `]y, x[%R); last first.
      by case: fderivable.
    by apply: subset_itv; rewrite bnd_simp.
  - move: ylet1. rewrite le_eqVlt => /orP [/eqP <-|yltn].
      by case: fderivable.
    apply/cvg_at_right_filter/fcontinuous.
    rewrite inE/= in_itv/=. apply/andP. split=> //.
    exact: (lt_le_trans t1ltt2).
  - move: t2lex. rewrite le_eqVlt => /orP [/eqP ->|t2ltx].
      by case: fderivable.
    apply: cvg_at_left_filter. apply: fcontinuous.
    rewrite inE/= in_itv/=. apply/andP. split=> //.
    exact: (le_lt_trans ylet1).
move: pleq. rewrite leq_eqVlt => /orP [/eqP|] pq.
  rewrite pq big_geq; first exact: ltnSn.
  suff AteqAx t : t \in `[y, x] -> A t = A x.
    rewrite (AteqAx y); first by rewrite set_itvcc inE/= lexx.
    under eq_Rintegral => t tyx do rewrite AteqAx//.
    by rewrite RintegralZl//= -!mulrBr tfct1t2// subrr// mulr0.
  rewrite inE/= in_itv/= => /andP[] yt tx.
  rewrite !(AteqAn p)// ?[X in X.+1]pq; apply/andP; split=> //.
  - exact: (le_trans py yt).
  - exact: (le_lt_trans tx xq).
  - exact: (le_trans py yx).
have ->: ((\sum_(p.+1 <= n < q.+1) a n * f n%:R)%R =
    (A q%:R * f q%:R - A p%:R * f p.+1%:R)%R -
    (\sum_(p.+1 <= n < q)  A n%:R * (f n.+1%:R - f n%:R)))%R.
  rewrite -sumrN /A !floor_nat Abel_discrete//. congr (_ + _)%R.
  by under [RHS]eq_bigr do rewrite floor_nat -mulrN opprB.
rewrite big_nat.
under eq_bigr => i /andP [] plti iltq.
  have yi : (y <= i%:R)%R by apply/(le_trans (ltW yp)); rewrite ler_nat.
  have ix : (i.+1%:R <= x)%R by apply: (le_trans _ qx); rewrite ler_nat.
  rewrite -tfct1t2// ?ler_nat//.
  have {}fi: lebesgue_measure.-integrable `[i%:R, i.+1%:R] (EFin \o f^`()).
    apply: (integrableS _ _ _ fi) => //.
    by apply: subset_itv => //=; rewrite bnd_simp.
  rewrite -RintegralZl// -Rintegral_itv_bndo_bndc.
    apply: eq_integrable; first exact: measurable_itv.
      by move=> t _ /=; rewrite EFinM.
    apply: integrableZl; first exact: measurable_itv.
    apply: (integrableS _ _ _ fi) => //.
    by apply: subset_itv => //=; rewrite bnd_simp.
  under eq_Rintegral => t.
    rewrite set_itvco inE/= => /AteqAn <-.
    over.
  over.
rewrite -big_nat => /=.
have Afi: lebesgue_measure.-integrable (`[y, x] : set R^o)
    (EFin \o (fun x0 : R^o => A x0 * f^`() x0)%R).
  have /setIidl <-: `[y, x] `<=` `[p%:R, q.+1%:R[.
    by apply: subset_itv; rewrite bnd_simp/=.
  rewrite -[p%:R]mulrz_nat -[q.+1%:R]mulrz_nat itvzz_bnd_bigcupD1.
    by rewrite ler_nat; apply/ltnW/(ltn_trans pq).
  rewrite setI_bigcupr bigcup_mkord.
  apply: integrable_bigsetU => i _; first exact: measurableI.
  apply: eq_integrable; first exact: measurableI.
    move=> t; rewrite inE/= => -[_]; rewrite in_itv/=.
    by rewrite -!natrD !mulrz_nat addnS EFinM => /AteqAn ->.
  apply: integrableZl; first exact: measurableI.
  by apply: (integrableS _ _ _ fi) => //; apply: measurableI.
rewrite /Rintegral big_nat sum_fine => [i /andP[] pi iq//|].
  apply: integrable_fin_num => //.
  apply: (integrableS _ _ _ Afi) => //.
  apply: subset_itv; rewrite bnd_simp.
    by apply/ltW/(lt_le_trans yp); rewrite ler_nat.
  by apply: (le_trans _ qx); rewrite ler_nat.
rewrite -big_nat -integral_bigsetU_EFin //=; first exact: iota_uniq.
- apply /trivIsetP => i j _ _ /eqP ineqj. rewrite -subset0 => z/=.
  rewrite !in_itv/= => -[] /andP[] iz zi /andP[] jz zj.
  move: (le_lt_trans iz zj) (le_lt_trans jz zi).
  by rewrite !ltr_nat => ij ji; apply/ineqj/anti_leq/andP; split.
- apply: measurable_int.
  apply: (integrableS _ _ _ Afi) => //.
    exact: bigsetU_measurable.
  rewrite (big_addn 0) big_mkord.
  rewrite -(bigcup_mkord _ (fun i => `[(i + p.+1)%:R, (i + p.+1).+1%:R[)).
  apply: bigcup_sub => i/=; rewrite ltn_subRL addnC => ipq.
  apply: subset_itv; rewrite bnd_simp.
    by apply/ltW/(lt_le_trans yp); rewrite ler_nat leq_addl.
  by apply: (le_trans _ qx); rewrite ler_nat.
rewrite (big_addn 0) big_mkord.
rewrite -(bigcup_mkord _ (fun i => `[(i + p.+1)%:R, (i + p.+1).+1%:R[)).
under eq_bigcupr do
  rewrite addnC -addnS -mulrz_nat -[(_ + _.+1)%:R]mulrz_nat !natrD.
rewrite -(absz_nat (q - p.+1)) -natz natrB//.
rewrite -itvzz_bnd_bigcupD1; first by rewrite ler_nat.
rewrite !mulrz_nat -![fine _]/(Rintegral _ _ _).
have itvyq: `[y, p.+1%:R[ `|` `[p.+1%:R, q%:R[ = `[y, q%:R[.
  by rewrite -itv_bndbnd_setU// bnd_simp// ?ler_nat// ltW.
have itvyx: `[y, x[ = `[y, p.+1%:R[ `|` `[p.+1%:R, q%:R[ `|` `[q%:R, x[.
  rewrite itvyq -itv_bndbnd_setU// bnd_simp.
  by apply/ltW/(lt_le_trans yp); rewrite ler_nat.
have ->:
  (\int_(t in `[y, x]) (A t * f^`() t) =
    \int_(t in `[y, p.+1%:R[) (A t * f^`() t) +
    \int_(t in `[p.+1%:R, q%:R[) (A t * f^`() t) +
    \int_(t in `[q%:R, x[) (A t * f^`() t))%R.
  rewrite /Rintegral -integral_itv_bndo_bndc.
    apply: (measurable_int (@lebesgue_measure R)).
    apply: (integrableS _ _ _ Afi) => //.
    by apply: subset_itv; rewrite bnd_simp//.
  rewrite itvyx -![fine _]/(Rintegral _ _ _) !Rintegral_setU //=.
  - exact: measurableU.
  - rewrite -itvyx.
    apply: (integrableS _ _ _ Afi) => //.
    by apply: subset_itv; rewrite bnd_simp//.
  - apply /disj_setPS => z.
    rewrite itvyq => /= -[] /andP [] _ zq /andP [] qz _.
    suff: (z < z)%R by rewrite ltxx.
    exact: (lt_le_trans zq qz).
  - rewrite itvyq.
    apply: (integrableS _ _ _ Afi) => //.
    by apply: subset_itv; rewrite bnd_simp//.
  - apply /disj_setPS => z /= [] /andP [] _ zp /andP [] pz _.
    suff: (z < z)%R by rewrite ltxx.
    exact: (lt_le_trans zp pz).
under [in RHS]eq_Rintegral => t.
  rewrite inE/= in_itv/= => /andP [] /(le_trans py) pt tp.
  rewrite (AteqAn p) ?pt//.
  over.
under [X in (_ = _ - (_ + _ + X))%R]eq_Rintegral => t.
  rewrite inE/= in_itv/= => /andP [] qt tx.
  rewrite (AteqAn q); first by rewrite qt; apply: (lt_trans tx).
  over.
rewrite !RintegralZl //=.
- apply: (integrableS _ _ _ fi) => //.
  apply: subset_itv; rewrite bnd_simp//=.
  by apply: (le_trans _ qx); rewrite ler_nat.
- apply: (integrableS _ _ _ fi) => //.
  apply: subset_itv; rewrite bnd_simp//=.
  by apply: (le_trans (ltW yp)); rewrite ler_nat.
rewrite /Rintegral [in RHS]integral_itv_bndo_bndc.
  apply: (measurable_int (@lebesgue_measure R)).
  apply: (integrableS _ _ _ fi) => //.
  apply: subset_itv; rewrite bnd_simp//=.
  by apply: (le_trans _ qx); rewrite ler_nat.
rewrite [X in (A q%:R * fine X)%R]integral_itv_bndo_bndc.
  apply: (measurable_int (@lebesgue_measure R)).
  apply: (integrableS _ _ _ fi) => //.
  apply: subset_itv; rewrite bnd_simp//=.
  by apply: (le_trans (ltW yp)); rewrite ler_nat.
rewrite -![fine _]/(Rintegral _ _ _) !tfct1t2 //.
- exact: ltW.
- by apply: (le_trans _ qx); rewrite ler_nat.
- by apply: (le_trans (ltW yp)); rewrite ler_nat.
rewrite (AteqAn q x) ?qx// (AteqAn p y) ?py// !opprD !mulrBr !opprB !addrA.
by rewrite (AC 7 ((1*7)*(3*2)*6*4*5))/= !subrr !add0r.
Qed.
