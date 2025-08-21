From mathcomp Require Import all_ssreflect classical_sets
boolp topology ssralg ereal ssrnum.
From mathcomp Require Import sequences reals interval
rat all_analysis archimedean ssrint.
Import Order.OrdinalOrder Num.Theory Order.POrderTheory
finset GRing.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Local Open Scope set_scope.
Local Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint prime_search (i j : nat) : nat :=
  match j with
  | 0 => i`!.+1
  | j'.+1 => if prime (i`!.+1 - j) then i`!.+1 - j else prime_search i j'
  end.

Fixpoint prime_seq (n : nat) : nat :=
  match n with
  | 0 => 2
  | i.+1 => let k := prime_seq i in prime_search k (k`! - k)
  end.

Lemma leq_prime_seq: {mono prime_seq : m n / m <= n}.
Proof.
move=> m n.
apply: (@Order.NatMonotonyTheory.incn_inP _ nat predT) => // {m n} [n /= _ _].
have prgtid i : forall j, i < i`!.+1 - j -> prime_search i j > i.
  elim=> /= [_|n0 HR]; first exact: (leq_ltn_trans (fact_geq i) (ltnSn i`!)).
  case: (prime (i`!.+1 - n0.+1)) => [// | ilt].
  exact/HR/(leq_trans _ (leq_sub2l i`!.+1 (leqnSn n0))).
set k := prime_seq n. set pk := prime_search k (k`! - k).
apply: prgtid. rewrite subnBAC; last exact: leqnSn.
  by rewrite -ltn_subLR// subnn subSnn.
exact: fact_geq. 
Qed.

Lemma mem_prime_seq (p : nat) : p \in range prime_seq = prime p.
Proof.
apply/idP/idP => [|primep].
  rewrite inE => -[] [|n] _ <- //.
  set i := prime_seq n. 
  suff find_prime: forall (j : nat),
      (forall k : nat, j < k <= i`! - i -> ~ prime (i`!.+1 - k))
      -> prime (prime_search i j).
    apply: (find_prime (i`! - i)) => k /andP [] kb1 kb2.
    have := (leq_ltn_trans kb2 kb1).
    by rewrite ltnn.
  elim=> [/= nprimeltq|n0 HR NoPrimeBefore /=]; last first.
    case: ifP => // noprime. apply: HR => k.
    case: (ltnP n0.+1 k) => [n01ltk|klen0] /andP [] ? ?.
      by apply: NoPrimeBefore; rewrite n01ltk.
    suff ->: k = n0.+1 by rewrite noprime.
    by apply: eqP; rewrite eqn_leq klen0.
  set q := pdiv (i`!.+1).
  have qprime: prime q by apply/pdiv_prime /fact_gt0.
  move: (pdiv_leq (ltn0Sn i`!)). rewrite leq_eqVlt => /orP [/eqP <- //|].
  case: (leqP q i) => [qlei|iltq qlt]; last first.
    move: (nprimeltq (i`!.+1 - q)).
    rewrite subn_gt0 qlt /= (@leq_sub2lE _ i.+1) => [/(_ iltq)|].
      by rewrite subKn// ltnW.
    exact: fact_geq.
  have /dvdn_fact : 0 < q <= i by rewrite pdiv_gt0.
  by rewrite (@dvdn_add_eq _ _ 1) ?Euclid_dvd1 // addn1; apply: pdiv_dvd.
case: (@Order.TotalTheory.arg_maxP _ _ 'I_p.+1 ord0
    (fun m => prime_seq m <= p) prime_seq) => /= [|n pgepsi pptargmax].
  exact: prime_gt1.
have pltpsni1: p < prime_seq n.+1.
  move: (valP n). rewrite leq_eqVlt => /orP [|nltp].
    rewrite eqSS => /eqP ->.
    exact/mono_ext/leq_prime_seq.
  move: (contra (pptargmax (Ordinal nltp))).
  rewrite [(_ <= _)%O](leq_prime_seq (Ordinal nltp) n) ltnn => /(_ erefl).
  by rewrite ltnNge.
suff NoPrime k : prime_seq n < k < prime_seq n.+1 -> ~~ prime k => [|/=].
  move: pgepsi.
  rewrite leq_eqVlt => /orP [/eqP <-|psnltp]; first by rewrite inE.
  move: (NoPrime p). rewrite psnltp pltpsni1 => /(_ erefl).
  by rewrite primep.
set psn := prime_seq n.
rewrite -[X in X < _](subKn (fact_geq psn)).
elim: (psn`! - psn) => /= [|n0 HR].
  rewrite subn0 ltnS => /andP [] kb1 kb2.
  have := (leq_ltn_trans kb2 kb1).
  by rewrite ltnn.
case: (boolP (prime (psn`! - n0))) => [_ /andP [] kb1| noprime /andP []].
  case: (ltnP n0 psn`!) => [n0ltpsnf|]; last first.
    rewrite -subn_eq0 subSS => /eqP ->.
    by rewrite ltn0.
  rewrite subSn// ltnS => kb2.
  have := (leq_ltn_trans kb2 kb1).
  by rewrite ltnn.
case: (leqP k (psn`! - n0)); last by move=> kb1 _ kb2; apply: HR; rewrite kb1.
rewrite leq_eqVlt => /orP [/eqP -> _ _ // | kb1].
rewrite -subSn; last first.
  rewrite -(@ltn_sub2rE n0) // subnn.
  exact: (leq_ltn_trans _ kb1).
rewrite subSS => kb2.
have := (leq_ltn_trans kb2 kb1).
by rewrite ltnn.
Qed. 

Definition P (k N : nat) := 
  [set n : 'I_N.+1 |all (fun p => p < prime_seq k) (primes n)]%SET.
Definition G (k N : nat) := ~: (P k N).

Lemma cardPcardG : forall k N, #|G k N| + #|P k N| = N.+1.
Proof.
move=> k N. rewrite addnC.
have: (P k N) :|: (G k N) = [set : 'I_N.+1]%SET by rewrite finset.setUCr.
rewrite -cardsUI finset.setICr cards0.
by rewrite -[X in _ + _ = X]card_ord addn0 -cardsT => ->.
Qed.

Lemma cardG (R : realType) (k N : nat) :
  (\big[+%R/0%R]_(k <= k0 <oo) ((prime_seq k0)%:R^-1 : R)%:E < (2^-1)%:E)%E
  -> k <= N.+1 -> ~~ odd N -> N > 0 -> (#|G k N| < (N./2)).
Proof.
set E := fun i => [set n : 'I_N.+1 | (prime_seq i) \in (primes n)].
set Parts := fun i => [set ([set x in [seq (insubd ord0 x : 'I_N.+1) |
  x <- (iota ((val y).+1 - (prime_seq i)) (prime_seq i))]]
  : {set 'I_N.+1}) | y in (E i)]%SET.
move=> Rklthalf kleqN1 evenN Nneq0.
suff cardEi: forall i, k <= i ->
    ((#|E i|)%:R <= (N%:R / (prime_seq i)%:R):>R)%R => [|i klti].
  have -> : G k N = (\bigcup_(k <= i < N.+1) E i).
    apply/eqP. rewrite finset.eqEsubset. apply/andP. split; last first.
      apply/fintype.subsetP => x.
      rewrite big_geq_mkord => /bigcupP [] i /andP [] _ klei.
      rewrite inE => pidvdx.
      rewrite !inE -has_predC. apply/hasP. exists (prime_seq i) => //=.
      by rewrite -leqNgt leq_prime_seq.
    apply/fintype.subsetP => x.
    rewrite !inE -has_predC => /hasP [] p /=.
    rewrite mem_primes => /andP [] + /andP [] xneq0 pdvdx.
    rewrite -mem_prime_seq inE => /= -[] i _ peqpi.
    move: peqpi pdvdx => <- {p} pidvdx.
    rewrite -leqNgt => pklepi.
    rewrite big_geq_mkord. apply/bigcupP.
    have ileqN : i < N.+1.
      apply: (leq_ltn_trans _ (ltn_ord x)).
      apply: (leq_trans _ (dvdn_leq xneq0 pidvdx)).
      exact/mono_ext/leq_prime_seq.
    exists (Ordinal ileqN) => /=; first by rewrite -leq_prime_seq.
    rewrite inE mem_primes. apply/andP. split; last exact/andP.
    by rewrite -mem_prime_seq inE.
  apply: (leq_ltn_trans (card_big_setU _ _ E)).
  rewrite -(ltr_nat R).
  apply: (@le_lt_trans _ _
      (N%:R * (\sum_(k <= i < N.+1) ((prime_seq i)%:R^-1)%R)%R)%R).
    rewrite mulr_sumr raddf_sum /=. apply: ler_sum_nat => i /andP [] + _.
    exact: cardEi.
  have SnleqlimSn: ((\sum_(k <= i < N.+1)  (prime_seq i)%:R^-1)%:E <=
      \big[+%R/0%R]_(k <= i <oo) ((prime_seq i)%:R^-1 : R)%:E)%E.
    rewrite (nneseries_split _ (N.+1 - k)) => [|i leqi]; last first.
      by rewrite lee_fin invr_ge0.
    rewrite subnKC // raddf_sum. apply/leeDl /nneseries_ge0 => n _ _.
    by rewrite lee_fin invr_ge0.
  rewrite -lte_fin.
  apply: (@le_lt_trans _ _
      (N%:R%:E * \big[+%R/0%R]_(k <= i <oo)  ((prime_seq i)%:R^-1)%:E)%E).
    rewrite EFinM. apply: lee_pmul => //; rewrite lee_fin//.
    by apply: sumr_ge0 => i _; rewrite invr_ge0.
  rewrite -divn2 natf_div ?dvdn2// EFinM -lte_pdivrMl ?ltr0n//.
  by rewrite muleA -EFinM mulVf ?mul1e// pnatr_eq0 -lt0n.
rewrite ler_pdivlMr; last first.
  rewrite ltr0n. have: prime_seq i \in range prime_seq by rewrite inE.
  by rewrite mem_prime_seq; apply: prime_gt0.
have Eigtpi x3 : x3 \in E i -> prime_seq i - x3.+1 = 0.
  have OnotinE: ord0 \notin E i => [|x3inEi]; first by rewrite /E inE.
  apply/eqP. rewrite subn_eq0. apply/leqW/dvdn_leq.
    case: x3 x3inEi => /= x3. case: (posnP x3) => // -> N1lt0.
    by rewrite /E inE. 
  move: x3inEi. rewrite /E inE mem_primes -mem_prime_seq mem_range.
  by case: (x3 > 0).
have: finset.trivIset (Parts i).
  apply/finset.trivIsetP => A B /imsetP [] x xinEi + /imsetP [] y yinEi.
  wlog xley: x y xinEi yinEi A B / x <= y.
    move: (leq_total x y) => /orP [xley Hw| ylex Hw Adef Bdef].
      exact: (Hw x y).
    by rewrite eq_sym disjoint_sym; apply: (Hw y x).
  case: (eqVneq x y) => [-> <- ->| xneqy]; first by rewrite eqxx.
  rewrite -setI_eq0 => -> -> AneqB /=. rewrite -finset.subset0.
  apply/fintype.subsetP. rewrite /sub_mem => x0.
  rewrite finset.in_setI => /andP. rewrite finset.inE => -[].
  rewrite finset.inE => /mapP -[] x1 x1iniota -> /mapP -[] x2 x2iniota
    /(congr1 val).
  rewrite !val_insubd. move: x1iniota x2iniota.
  rewrite !mem_iota !addnCB (Eigtpi x) // (Eigtpi y) // !addn0 !ltnS.
  move=> /andP [] x1ge x1lt /andP [] x2ge x2lt.
  rewrite (leq_trans x1lt (ltn_ord x)) (leq_trans x2lt (ltn_ord y)) => x12.
  have: y.+1 - (prime_seq i) >= x.+1.
    rewrite -(leq_add2r (prime_seq i)) -(@leq_sub2rE x.+1); last first.
      by rewrite addnCB (Eigtpi y) // addn0. 
    rewrite addnCB (Eigtpi y) // addn0 -addnBAC // subnn add0n subSS.
    apply: dvdn_leq; first by rewrite subn_gt0 ltn_neqAle; apply/andP.
    suff pidvdEi x3 : x3 \in E i -> prime_seq i %| x3.
      by apply: dvdn_sub; apply: (pidvdEi _).
    by rewrite /E inE mem_primes -mem_prime_seq mem_range; case: (x3 > 0).
  move=> /(fun H => leq_trans H x2ge) /(leq_ltn_trans x1lt).
  by rewrite x12 ltnn.
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
  rewrite [X in X < _]addBnA; last first.
  - exact: ltnW.
  - by rewrite -subn_eq0; apply/eqP/Eigtpi.
  rewrite -(@prednK (prime_seq i - x1)) ?subn_gt0// !subSS.
  rewrite (leq_ltn_trans _ (ltn_ord x)); last exact: sub_ord_proof.
  rewrite [X in X < _]addBnA; last first.
  - exact: ltnW.
  - by rewrite -subn_eq0; apply/eqP/Eigtpi.
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
  rewrite mem_iota subnK => [/andP [] x0b1 x0b2|]; last first.
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
  rewrite mem_iota subnK; last by rewrite -subn_eq0; apply/eqP /Eigtpi.
  by rewrite ltnSn -ltnS ltn_subrL prime_gt0 // -mem_prime_seq mem_range.
rewrite inE /in_mem /= => /mapP /= [] x3.
rewrite mem_iota subnK => [/andP [] x3b1 x3b2 /(congr1 val)|]; last first.
  by rewrite -subn_eq0; apply/eqP /Eigtpi.
have x3b3: x3 < N.+1 by apply: (leq_ltn_trans _ (ltn_ord x1)).
rewrite val_insubd x3b3 /= => x2eqx3. move: x3b2.
by rewrite ltnS -x2eqx3.
Qed.

Lemma cardP (R : realType) (k : nat) :
  #|P k (2 ^ (2 * k + 2))| <= (2 ^ (2 * k + 1)).+1.
Proof.
set N := 2 ^ (2 * k + 2).
set P' := fun k N => P k N :\ ord0.
set A := k.-tuple bool.
set B := 'I_(2 ^ (k + 1)).+1.
set a := fun n i => odd (logn (prime_seq i) n).
have eqseq: forall n k, n < k ->
    [seq i <- [seq prime_seq i  | i <- index_iota 0 k]  | i  \in primes n]
    = primes n.
  move=> + k0; case=> [|n nlek]; first by rewrite filter_pred0.
  apply: lt_sorted_eq => [||elt].
  - apply: lt_sorted_filter.
    rewrite sorted_map.
    apply: (@sub_sorted _ ltn); last exact: iota_ltn_sorted.
    rewrite ltEnat => i j /=.
    by rewrite (leqW_mono leq_prime_seq). 
  - exact: sorted_primes.
  rewrite mem_filter. apply: andb_idr => eltinprimesn.
  suff: prime elt /\ elt < prime_seq k0.
    rewrite -mem_prime_seq inE => /= -[] [] i _ <- pilepk.
    rewrite map_comp. apply: map_f.
    by rewrite map_id_in // mem_iota /= add0n subn0 -(leqW_mono leq_prime_seq).
  split.
    by apply/(@allP _ _ (primes n.+1)); first exact: all_prime_primes.
  apply: (@leq_ltn_trans n.+1). 
    apply: dvdn_leq => //.
    move: eltinprimesn.
    by rewrite mem_primes => /andP [] _ /andP [].
  apply: (@leq_ltn_trans k0.-1); first by rewrite ltn_predRL.
  rewrite -(ltn_add2r 1) !addn1 (ltn_predK nlek) ltnS.
  exact/mono_ext/leq_prime_seq.
have binB (n : 'I_N.+1) : 
    (\prod_(i < k) (prime_seq i) ^ (logn (prime_seq i) n)./2) <
    (2 ^ (k + 1)).+1.
  case: (boolP (n == ord0)) => [/eqP -> /=|nneq0].
    under eq_bigr do rewrite logn0 -divn2 div0n expn0. 
    rewrite big1_eq -[X in _ < X]addn1 -[X in X < _]add0n ltn_add2r expn_gt0.
    by apply/orP; left.
  rewrite -ltn_sqr expn_prod.
  under eq_bigr do rewrite -expnM muln2 halfK.
  apply: (@leq_ltn_trans
      (\prod_(i < k) prime_seq i ^ (logn (prime_seq i) n))).
    apply: leq_prod => i _. rewrite leq_exp2l; first exact: leq_subr.
    by apply: prime_gt1; rewrite -mem_prime_seq inE.
  apply: (@leq_ltn_trans n); last first.
    apply: (ltn_trans (ltn_ord n)). rewrite /N.
    rewrite -[X in X ^ 2]addn1 sqrnD exp1n addn1 -expnM mulnDl.
    rewrite muln1 -expnS addn1 mul1n [in X in _ < X]mulnC.
    rewrite -(ltn_sub2rE _ (ltnSn N)).
    rewrite -addnBAC; last by rewrite ltnSn.
    by rewrite subnn add0n expn_gt0; apply/orP; left.
  rewrite [X in _ <= X]prod_prime_decomp ?lt0n// prime_decompE big_map /=.
  rewrite -(big_mkord predT (fun i =>
    (prime_seq i) ^ logn (prime_seq i) n)) -(big_map prime_seq predT
    (fun i => i ^ logn i n)) /=.
  rewrite (bigID (fun i : nat => i \in primes n)) /=.
  rewrite [X in _ * X]big1 => [|i inotinprimesn]; last first.
    case: (boolP ((i == 0) || (i == 1))) => [/orP [] /eqP -> //|].
    move=> /norP [] ineq0 ineq1.
    rewrite -(expn0 i). apply/eqP.
    rewrite eqn_exp2l.
      apply/eqP. move: inotinprimesn.
      by rewrite -logn_gt0 lt0n => /negPn /eqP.
    rewrite ltn_neqAle. apply/andP. split; first by rewrite eq_sym.
    by rewrite lt0n.
  rewrite muln1 -big_filter.
  case: (boolP (n < k)) => [nltk|]; first by rewrite (eqseq n).
  rewrite -leqNgt => klen.
  rewrite -[in X in _ <= X](eqseq n n.+1); last exact: ltnSn.
  rewrite -[X in index_iota _ X.+1](subnKC (leq_trans klen (ltnSn n))).
  rewrite -addnS -subSn //.
  rewrite !big_filter /index_iota !subn0 iotaD map_cat big_cat add0n /=.
  apply/leq_pmulr/prodn_gt0 => i.
  exact: pfactor_gt0.
set f : 'I_N.+1 -> A * B := fun n =>
  ([tuple a n i  | i < k], Ordinal (binB n)).
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
  under eq_bigr => i _. rewrite -expnD tnth_mktuple /a subnK. over.
    by case: (boolP (odd (logn (prime_seq i) x))); first exact: odd_gt0.
  case: (boolP (x == ord0)) => [/eqP xeq0|xneq0].
    by move: xeq0 xinPkN => ->; rewrite /P' !inE.
  rewrite [RHS]prod_prime_decomp ?lt0n// prime_decompE big_map /=.
  rewrite [in LHS](bigID (fun i : 'I_k => prime_seq i \in primes x)) /=.
  under [X in _ * X = _]eq_bigr => i.
    rewrite mem_primes lognE -eqbF_neg => /eqP ->.
    by rewrite expn0; over.
  rewrite big1_eq muln1 -(big_map _ (fun i => prime_seq i \in primes x)
    (fun i => prime_seq i ^ logn (prime_seq i) x)) -(big_map _ _
    (fun j => j ^ logn j x)) -big_filter.
  apply: congr_big => //.
  rewrite -map_comp functions.compE. 
  apply: lt_sorted_eq => [||elt].
  - apply: lt_sorted_filter.
    rewrite map_comp sorted_map -[X in map _ X]filter_predT val_enum_ord.
    apply: (@sub_sorted _ ltn); last exact: iota_ltn_sorted.
    rewrite ltEnat => i j /=.
    by rewrite (leqW_mono leq_prime_seq). 
  - exact: sorted_primes.
  rewrite mem_filter. apply: andb_idr.
  move: xinPkN. rewrite /P' /P inE => /andP [] _.
  rewrite inE => /allP primesxlepk eltinprimesx.
  have []: prime elt /\ elt < prime_seq k.
    split; last exact: primesxlepk.
    by apply/(@allP _ _ (primes x)); first exact: all_prime_primes.
  rewrite -mem_prime_seq inE => /= -[] i _ <- pilepk.
  rewrite map_comp. apply: map_f.
  rewrite -[X in map _ X]filter_predT val_enum_ord mem_iota /= add0n.
  by rewrite -(leqW_mono leq_prime_seq).
have -> : P k N = P' k N :|: [set ord0].
  by rewrite /P' finset.setUC finset.setD1K // inE.
rewrite finset.setUC cardsU1 [in X in X + _]/P' !inE /= add1n ltnS. 
rewrite -(card_in_imset finj).
have imfleqAB:
    #|[set f x  | x in P' k N]| <= #|finset.setX [set: A] (~: [set ord0 : B])|.
  apply/subset_leq_card/fintype.subsetP => y.
  rewrite !inE => /imsetP [] x xinPkN -> /=. apply/eqP.
  apply: (contra_not (@congr1 _ _ val _ _)) => /=.
  apply/eqP. rewrite -lt0n. apply: prodn_gt0 => i.
  rewrite expn_gt0. apply/orP. left. apply: prime_gt0.
  by rewrite -mem_prime_seq inE.
apply: (leq_trans imfleqAB).
rewrite cardsX cardsE card_tuple card_bool cardsC1 card_ord.
by rewrite -expnD addnA addnn mul2n.
Qed.

Theorem DivergenceSumInversePrimeNumbers (R : realType) :
  (\sum_(0 <= i < n) (((prime_seq i)%:R:R)^-1)%:E)%R @[n --> \oo] --> +oo%E.
Proof.
set un := fun i => (((prime_seq i)%:R : R)^-1)%:E.
set Sn := fun n => (\sum_(0 <= i < n) (un i))%R.
have unpos n: 0 <= n -> true -> (0%R <= un n)%E => [_ _|].
  by rewrite /un lee_fin invr_ge0 ler0n.
have := (is_cvg_nneseries unpos).
have := (leey (limn Sn)).
rewrite le_eqVlt => /orP [/eqP -> //|].
have := (nneseries_ge0 unpos).
move leqlimnSn: (limn Sn) => l.
case: l leqlimnSn => // l leqlimnSn _ _ /subsetP llimnSn. 
have /llimnSn : `](l - (1/2)%R)%:E, (l + (1/2)%R)%:E[ \in nbhs (l%:E).
  rewrite inE. exists (1/2)%R => /=; first exact: divr_gt0.
  exact/subset_ball_prop_in_itv.
rewrite inE => -[] k /= _ /subsetP/(_ k).
set N := 2^(2*k + 2).
set PN := P k N.
set GN := G k N.
rewrite inE /= leqnn set_interval.set_itvoo inE /= EFinB EFinD -leqlimnSn.
move=> /(_ erefl) /andP [] + _.
rewrite lte_subel_addl; last by rewrite leqlimnSn.
rewrite -lteBlDr; last exact/sum_fin_numP.
rewrite (nneseries_split _ k); last first => [k0 _|]; first exact: unpos.
rewrite /Sn add0n addrAC subee; last exact/sum_fin_numP.
rewrite add0e => Rklthalf.
suff: N.+1 < N.+1 by rewrite ltnn.
rewrite -[X in X < _](cardPcardG k N). 
have Neq: N./2 + (2 ^ (2 * k + 1)).+1 = N.+1.
  rewrite addnC addSn /N -divn2.
  rewrite -[X in _ %/ X]expn1 -expnB //; last by rewrite addn2.
  rewrite -addnBA /subn //= addnn.
  by rewrite -mul2n -expnS -[X in 2 ^ X]addn1 -addnA /addn.
rewrite -[X in _ < X]Neq -addSn.
apply: leq_add; last exact: cardP.
apply: (@cardG R); first by move: Rklthalf; rewrite /un div1r.
- rewrite /N. apply/leqW/(leq_trans (ltnW (ltn_expl k (ltnSn 1)))).
  by rewrite leq_exp2l // mul2n -addnn -[X in X <= _]addn0 -addnA leq_add2l.
- by rewrite /N addn2 expnS mul2n odd_double.
- by rewrite /N expn_gt0; apply/orP; left.
Qed.
