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

Fixpoint prime_research (i j : nat) : nat :=
    match j with
    | 0 => i`!.+1
    | j'.+1 => if prime (i`!.+1 - j) then i`!.+1 - j else prime_research i j'
    end.

Fixpoint prime_seq (n : nat) : nat :=
    match n with
    | 0 => 2
    | i.+1 => let k := prime_seq i in prime_research k (k`! - k)
    end.

Lemma prime_seq_incr: {mono prime_seq : m n / m <= n}.
Proof.
move=> m n.
apply: (@Order.NatMonotonyTheory.incn_inP _ nat predT) => // {m n} [n /= _ _].
have prgtid : forall (i j : nat), i < i`!.+1 - j -> prime_research i j > i
    => [i|].
    elim=> /= [_|n0 HR]. 
        exact: (leq_ltn_trans (fact_geq i) (ltnSn i`!)).
    case: (prime (i`!.+1 - n0.+1)) => [// | ilt].
    apply: HR.
    exact: (leq_trans _ (leq_sub2l i`!.+1 (leqnSn n0))).
set k := prime_seq n. set pk := prime_research k (k`! - k).
apply: prgtid. rewrite subnBAC; last exact: leqnSn.
    rewrite -ltn_subLR => [|//].
    by rewrite subnn subSnn.
exact: fact_geq. 
Qed.

Lemma mono_ext: forall f, {mono f : m n / m <= n} -> forall n : nat, f n >= n.
Proof.
move=> f fincr. elim=> [//| n HR].
apply: (leq_ltn_trans HR).
rewrite ltn_neqAle fincr (inj_eq (incn_inj fincr)).
rewrite -ltn_neqAle.
exact: ltnSn.
Qed.

Lemma mem_prime_seq (p : nat) : p \in range prime_seq = prime p.
Proof.
apply /idP /idP => [|primep].
    rewrite inE => -[] + _ <- => -[// | /= n].
    set i := prime_seq n. 
    suff find_prime: forall (j : nat),
        (forall k : nat, j < k <= i`! - i -> ~ prime (i`!.+1 - k))
        -> prime (prime_research i j).
        apply: (find_prime (i`! - i)) => k /andP [] kb1 kb2.
        suff: k < k by rewrite ltnn.
        exact: (leq_ltn_trans kb2).
    elim=> [/= nprimeltq|n0 HR NoPrimeBefore /=]; last first.
        case: ifP => // noprime. apply: HR => k.
        case: (ltnP n0.+1 k) => [n01ltk|klen0] /andP [] ? ?.
            by apply: NoPrimeBefore; rewrite n01ltk.
        suff ->: k = n0.+1 by rewrite noprime.
        by apply: eqP; rewrite eqn_leq klen0.
    set q := pdiv (i`!.+1).
    have qprime: prime q by apply /pdiv_prime /fact_gt0.
    move: (pdiv_leq (ltn0Sn i`!)). rewrite leq_eqVlt => /orP [/eqP <- //|].
    case: (leqP q i) => [qlei|iltq qlt]; last first.
        move: (nprimeltq (i`!.+1 - q)).
        rewrite subn_gt0 qlt /= (@leq_sub2lE _ i.+1) => [/(_ iltq)|].
            by rewrite subKn; last exact: ltnW qlt.
        exact: fact_geq.
    have /dvdn_fact : 0 < q <= i by rewrite pdiv_gt0.
    by rewrite (@dvdn_add_eq _ _ 1) ?Euclid_dvd1 // addn1; apply: pdiv_dvd.
case: (@Order.TotalTheory.arg_maxP _ _ 'I_p.+1 ord0
    (fun m => prime_seq m <= p) prime_seq) => /= [|n pgepsi pptargmax].
    exact: prime_gt1.
have pltpsni1: p < prime_seq n.+1.
    move: (valP n). rewrite leq_eqVlt => /orP [|nltp].
        rewrite eqSS => /eqP ->.
        exact /mono_ext /prime_seq_incr.
    move: (contra (pptargmax (Ordinal nltp))).
    rewrite [(_ <= _)%O](prime_seq_incr (Ordinal nltp) n) ltnn => /(_ erefl).
    by rewrite ltnNge.
suff NoPrime : forall k : nat, prime_seq n < k < prime_seq n.+1 -> ~~ prime k
    => [|k /=].
    move: pgepsi.
    rewrite leq_eqVlt => /orP [/eqP <-|psnltp]; first by rewrite inE.
    move: (NoPrime p). rewrite psnltp pltpsni1 => /(_ erefl).
    by rewrite primep.
set psn := prime_seq n.
rewrite -[X in X < _](subKn (fact_geq psn)).
elim: (psn`! - psn) => /= [|n0 HR].
    rewrite subn0 => /andP [] kb1 kb2.
    have: k < k by apply: (leq_ltn_trans _ kb1).
    by rewrite ltnn.
case: (boolP (prime (psn`! - n0))) => [_ /andP [] kb1| noprime /andP []].
    case: (ltnP n0 psn`!) => [n0ltpsnf|]; last first.
        rewrite -subn_eq0 subSS => /eqP ->.
        by rewrite ltn0.
    rewrite subSn => [kb2|//].
    have: k < k by apply: (leq_ltn_trans _ kb1).
    by rewrite ltnn.
case: (leqP k (psn`! - n0)) => [|kb1 _ kb2].
    rewrite leq_eqVlt => /orP [/eqP -> _ _ // | kb1].
    rewrite -subSn; last first.
        rewrite -(@ltn_sub2rE n0) // subnn.
        exact: (leq_ltn_trans _ kb1).
    rewrite subSS => kb2.
    have: psn`! - n0 < psn`! - n0 by apply: (leq_ltn_trans kb2).
    by rewrite ltnn.
by apply: HR; rewrite kb1.
Qed. 

Lemma card_big_setU
    (I : Type) (T : finType) (r : seq I) (P : {pred I}) (F : I -> {set T}) :
    #|\bigcup_(i <- r | P i)  F i| <= \sum_(i <- r | P i) #|F i|.
Proof.
elim: r => [|a l HI]; first by rewrite !big_nil cards0.
rewrite !big_cons. case: (P a); last exact: HI.
apply: (leq_trans (leq_card_setU (F a) _)).
by rewrite leq_add2l.
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
        apply /eqP. rewrite finset.eqEsubset. apply /andP. split; last first.
            apply /fintype.subsetP => x.
            rewrite big_geq_mkord => /bigcupP [] i /andP [] _ klei.
            rewrite inE => pidvdx.
            rewrite !inE -has_predC. apply /hasP. exists (prime_seq i) => //=.
            by rewrite -leqNgt prime_seq_incr.
        apply /fintype.subsetP => x.
        rewrite !inE -has_predC => /hasP [] p /=.
        rewrite mem_primes => /andP [] + /andP [] xneq0 pdvdx.
        rewrite -mem_prime_seq inE => /= -[] i _ peqpi.
        move: peqpi pdvdx => <- {p} pidvdx.
        rewrite -leqNgt => pklepi.
        rewrite big_geq_mkord. apply /bigcupP.
        have ileqN : i < N.+1.
            apply: (leq_ltn_trans _ (ltn_ord x)).
            apply: (leq_trans _ (dvdn_leq xneq0 pidvdx)).
            exact /mono_ext /prime_seq_incr.
        exists (Ordinal ileqN) => /=; first by rewrite -prime_seq_incr.
        rewrite inE mem_primes. apply /andP. split; last exact /andP.
        by rewrite -mem_prime_seq inE.
    apply: (leq_ltn_trans (card_big_setU _ _ E)).
    rewrite -(ltr_nat R). apply: (@le_lt_trans _ _
        (N%:R * (\sum_(k <= i < N.+1) ((prime_seq i)%:R^-1)%R)%R)%R).
        rewrite mulr_sumr raddf_sum /=. apply: ler_sum_nat => i /andP [] + _.
        exact: cardEi.
    have SnleqlimSn: ((\sum_(k <= i < N.+1)  (prime_seq i)%:R^-1)%:E <=
        \big[+%R/0%R]_(k <= i <oo) ((prime_seq i)%:R^-1 : R)%:E)%E.
        rewrite (nneseries_split _ (N.+1 - k)) => [|i leqi]; last first.
            by rewrite lee_fin invr_ge0.
        rewrite subnKC // raddf_sum. apply /leeDl /nneseries_ge0 => n _ _.
        by rewrite lee_fin invr_ge0.
    rewrite -lte_fin. apply: (@le_lt_trans _ _
        (N%:R%:E * \big[+%R/0%R]_(k <= i <oo)  ((prime_seq i)%:R^-1)%:E)%E).
        rewrite EFinM. apply: lee_pmul => //; first by rewrite lee_fin.
        rewrite lee_fin. apply: sumr_ge0 => i _.
        by rewrite invr_ge0.
    rewrite -divn2 natf_div; last by rewrite dvdn2.
    rewrite EFinM -lte_pdivrMl; last by rewrite ltr0n.
    rewrite muleA -EFinM mulVf; first by rewrite mul1e.
    by rewrite pnatr_eq0 -lt0n.
rewrite ler_pdivlMr; last first.
    rewrite ltr0n. have: prime_seq i \in range prime_seq by rewrite inE.
    by rewrite mem_prime_seq; apply: prime_gt0.
have Eigtpi : forall x3, x3 \in E i -> prime_seq i - x3.+1 = 0.
        have OnotinE: ord0 \notin E i => [|x3 x3inEi]; first by rewrite /E inE.
        apply /eqP. rewrite subn_eq0.
        apply /leqW /dvdn_leq.
            case: x3 x3inEi => /= x3. case: (posnP x3) => // -> N1lt0.
            by rewrite /E inE. 
        move: x3inEi. rewrite /E inE.
        by rewrite mem_primes -mem_prime_seq mem_range; case: (x3 > 0).
have: finset.trivIset (Parts i).
    apply /finset.trivIsetP => A B /imsetP [] x xinEi + /imsetP [] y yinEi.
    wlog xley: x y xinEi yinEi A B / x <= y.
        move: (leq_total x y) => /orP [xley Hw| ylex Hw Adef Bdef].
            exact: (Hw x y).
        by rewrite eq_sym disjoint_sym; apply: (Hw y x).
    case: (eqVneq x y) => [-> <- ->| xneqy]; first by rewrite eqxx.
    rewrite -setI_eq0 => -> -> AneqB /=. rewrite -finset.subset0.
    apply /fintype.subsetP. rewrite /sub_mem => x0.
    rewrite finset.in_setI => /andP. rewrite finset.inE => -[].
    rewrite finset.inE => /mapP -[] x1 x1iniota ->
        /mapP -[] x2 x2iniota /(congr1 val).
    rewrite !val_insubd. move: x1iniota x2iniota.
    rewrite !mem_iota !addnCB (Eigtpi x) // (Eigtpi y) // !addn0
        => /andP [] x1ge x1lt /andP [] x2ge x2lt.
    have -[] : x1 < N.+1 /\ x2 < N.+1 => [|x1ltN x2ltN /=].
        split; first exact: (leq_ltn_trans _ (ltn_ord x)).
        exact: (leq_ltn_trans _ (ltn_ord y)).
    rewrite !ifT => // x1eqx2.
    have: y.+1 - (prime_seq i) >= x.+1.
        rewrite -(leq_add2r (prime_seq i)) -(@leq_sub2rE x.+1); last first.
            by rewrite addnCB (Eigtpi y) // addn0. 
        rewrite addnCB (Eigtpi y) // addn0 -addnBAC // subnn add0n subSS.
        apply: dvdn_leq; first by rewrite subn_gt0 ltn_neqAle; apply /andP.
        have pidvdEi : forall x3, x3 \in E i -> prime_seq i %| x3 => [x3|].
            rewrite /E inE mem_primes -mem_prime_seq mem_range.
            by case: (x3 > 0).
        apply: dvdn_sub; first exact: (pidvdEi y).
        exact: (pidvdEi x).
    suff ympiltx : y.+1 - (prime_seq i) < x.+1 by rewrite ltn_geF.
    apply: (leq_ltn_trans _ x1lt).
    by rewrite x1eqx2 in x2ge *.
set i1toN := [set : 'I_N.+1] :\ ord0.
have cardNeqN: #|i1toN| = N.
    rewrite /i1toN. apply /eqP.
    rewrite -(eqn_add2r (ord0 \in [set :'I_N.+1]%SET)). apply /eqP.
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
    apply /(uniqP ord0) => x1 y1 /=.
    rewrite !inE size_map size_iota => x1lt y1lt.
    rewrite !(nth_map 0) ?size_iota //.
    rewrite !nth_iota => // /(congr1 val). rewrite !val_insubd /=.
    rewrite [X in X < _]addBnA; last first.
    - exact: ltnW.
    - by rewrite -subn_eq0; apply /eqP; apply: Eigtpi.
    rewrite -(@prednK (prime_seq i - x1)); last by rewrite subn_gt0.
    rewrite !subSS.
        rewrite (leq_ltn_trans _ (ltn_ord x)); last exact: sub_ord_proof.
    rewrite [X in X < _]addBnA; last first.
    - exact: ltnW.
    - by rewrite -subn_eq0; apply /eqP /Eigtpi.
    rewrite -(@prednK (prime_seq i - y1)) ?subn_gt0 // !subSS.
    suff -> : x - (prime_seq i - y1).-1 < N.+1 by apply: addnI.
    apply: (leq_ltn_trans _ (ltn_ord x)).
    exact: sub_ord_proof.
under eq_bigr => I IinPi. rewrite cardeltPi => //. over.
rewrite sum_nat_const.
suff -> : #|Parts i| = #|E i|.
    suff Pisubi1toN : finset.cover (Parts i) \subset i1toN => [eqcard|].
        suff: #|E i| * prime_seq i <= #|i1toN| by rewrite -natrM ler_nat.
        exact: (leq_trans (eq_leq eqcard) (subset_leq_card Pisubi1toN)).
    rewrite /(Parts i) cover_imset. apply /bigcupsP => i0 i0inEi.
    apply /fintype.subsetP => x.
    case: (boolP (x == ord0)) => [/eqP ->|xneq0 _]; last first.
        by rewrite /i1toN inE !inE xneq0.
    rewrite inE /in_mem /= => /mapP /= [] x0.
    rewrite mem_iota subnK => [/andP [] x0b1 x0b2|]; last first.
        by rewrite -subn_eq0; apply /eqP /Eigtpi.
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
    apply /eqP. rewrite eq_sym. apply /eqP.
    move: x2lex1 x2inEi x1inEi enseq. exact: (Hw x2 x1).
apply: le_anti. apply /andP. split. exact: x1lex2.
have: x2 \in [set x in [seq insubd ord0 x0
    | x0 <- iota ((\val x1).+1 - prime_seq i) (prime_seq i)]].
    rewrite enseq inE /in_mem /=. apply /mapP => /=.
    exists x2; last by apply: val_inj; rewrite !val_insubd ltn_ord.
    rewrite mem_iota subnK; last by rewrite -subn_eq0; apply /eqP /Eigtpi.
    rewrite ltnSn -ltnS ltn_subrL prime_gt0 //.
    by rewrite -mem_prime_seq mem_range.
rewrite inE /in_mem /= => /mapP /= [] x3.
rewrite mem_iota subnK => [/andP [] x3b1 x3b2 /(congr1 val)|]; last first.
    by rewrite -subn_eq0; apply /eqP /Eigtpi.
have x3b3: x3 < N.+1 by apply: (leq_ltn_trans _ (ltn_ord x1)).
rewrite val_insubd x3b3 /= => x2eqx3. move: x3b2.
by rewrite ltnS -x2eqx3.
Qed.

(* CES TROIS LEMMES SONT UTILES... MAIS PAS DANS NOTRE PREUVE !! *)

Lemma coprimeMr_bigprod
    (I : Type) (r : seq I) (P : {pred I}) (F : I -> nat) (a : I) (l : seq I) :
    all (coprime (F a)) [seq F i | i <- [seq i <- l | P i]] ->
    coprime (F a) (\prod_(j <- l | P j) F j).
Proof.
elim: l => /= [_|a0 l HI].
    by rewrite big_nil coprimen1.
rewrite big_cons. case: (P a0) => //.
rewrite map_cons => /= /andP [] cpaa0 allcoprimea.
rewrite coprimeMr. apply /andP. split => //.
exact: HI.
Qed.

Lemma Gauss_dvd_bigprod
    (I : eqType) (r : seq I) (P : {pred I}) (F : I -> nat) (n : nat) :
    pairwise coprime [seq F i | i <- [seq i <- r | P i]] ->
    reflect (forall i, i \in r -> P i -> F i %| n)
    (\prod_(i <- r | P i) F i %| n).
Proof.
elim: r => /= [_|a l HI].
    rewrite big_nil dvd1n. apply: ReflectT => i.
    by rewrite in_nil.
rewrite big_cons.
case: (boolP (P a)) => [Pa|]; last first.
    rewrite -eqbF_neg => /eqP nPa pairwisecoprime.
    apply: (equivP (HI pairwisecoprime)).
    split; last first => [Fidvdn i iinl|Fidvdn i].
        apply: Fidvdn. rewrite in_cons.
        by apply /orP; right.
    rewrite in_cons => /orP [/eqP ->|]; first by rewrite nPa.
    exact: Fidvdn.
rewrite map_cons pairwise_cons => /andP [] allcoprimea pairwisecoprime.
rewrite Gauss_dvd; last exact: coprimeMr_bigprod.
apply: (equivP (andPP idP (HI pairwisecoprime))).
split => [[] Fadvdn Fidvdn i|Fidvdn].
    by rewrite in_cons => /orP [/eqP ->|]; last exact: Fidvdn.
split => [|i iinl].
    apply: Fidvdn => //; first exact: mem_head.
by apply: Fidvdn; rewrite in_cons; apply /orP; right.
Qed.

Lemma Gauss_dvd_bigprod_ord (k : nat) (F : nat -> nat) (n : nat) :
    pairwise coprime [seq F i | i <- iota 0 k] ->
    reflect (forall i, i < k -> F i %| n) (\prod_(i < k) F i %| n).
Proof.
move=> pairwisecoprime. apply: (equivP (Gauss_dvd_bigprod _ _)).
    move: pairwisecoprime.
    by rewrite -val_enum_ord -map_comp functions.compE.
split => [Fidvdn i ilek|Fidvdn i iord _]; last exact: Fidvdn.
exact: (Fidvdn (Ordinal ilek)).
Qed.

Lemma exmnMn_bigprod
    (I : eqType) (r : seq I) (P : {pred I}) (F : I -> nat) (n : nat) :
    (\prod_(i <- r | P i) F i) ^ n = \prod_(i <- r | P i) (F i) ^ n.
Proof.
elim: r => [|a l]; first by rewrite !big_nil exp1n.
rewrite !big_cons. case: (P a) => <- //.
by rewrite expnMn.
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
    = primes n => [n k0|].
    case: n => [|n nlek]; first by rewrite filter_pred0.
    apply: lt_sorted_eq => [||elt].
    - apply: lt_sorted_filter.
        rewrite sorted_map.
        apply: (@sub_sorted _ ltn); last exact: iota_ltn_sorted.
        rewrite ltEnat => i j /=.
        by rewrite (leqW_mono prime_seq_incr). 
    - exact: sorted_primes.
    rewrite mem_filter. apply: andb_idr => eltinprimesn.
    suff: prime elt /\ elt < prime_seq k0 => [[]|].
        rewrite -mem_prime_seq inE => /= -[] i _ <- pilepk.
        rewrite map_comp. apply: map_f.
        rewrite map_id_in // mem_iota /= add0n subn0.
        by rewrite -(leqW_mono prime_seq_incr).
    split.
        by apply /(@allP _ _ (primes n.+1)); first exact: all_prime_primes.
    apply: (@leq_ltn_trans n.+1). 
        apply: dvdn_leq => //.
        move: eltinprimesn.
        by rewrite mem_primes => /andP [] _ /andP [].
    apply: (@leq_ltn_trans k0.-1); first by rewrite ltn_predRL.
    rewrite -(ltn_add2r 1) !addn1 (ltn_predK nlek) ltnS.
    exact /mono_ext /prime_seq_incr.
have binB: forall n : 'I_N.+1,
    (\prod_(i < k) (prime_seq i) ^ (logn (prime_seq i) n)./2) <
    (2 ^ (k + 1)).+1
    => [n|].
    case: (boolP (n == ord0)) => [/eqP -> /=|nneq0].
        under eq_bigr => i _. rewrite logn0 -divn2 div0n expn0. over.
        rewrite big1_eq -[X in _ < X]addn1 -[X in X < _]add0n.
        by rewrite ltn_add2r expn_gt0; apply /orP; left.
    rewrite -ltn_sqr exmnMn_bigprod.
    under eq_bigr => i _. rewrite -expnM muln2 halfK. over.
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
        by rewrite subnn add0n expn_gt0; apply /orP; left.
    rewrite [X in _ <= X]prod_prime_decomp; last by rewrite lt0n.
    rewrite prime_decompE big_map /=.
    rewrite -(big_mkord predT (fun i =>
        (prime_seq i) ^ logn (prime_seq i) n)) -(big_map prime_seq predT
        (fun i => i ^ logn i n)) /=.
    rewrite (bigID (fun i : nat => i \in primes n)) /=.
    rewrite [X in _ * X]big1 => [|i inotinprimesn]; last first.
        case: (boolP ((i == 0) || (i == 1)))
            => [/orP [] /eqP -> //| /norP [] ineq0 ineq1].
        rewrite -(expn0 i). apply /eqP.
        rewrite eqn_exp2l.
            apply /eqP. move: inotinprimesn.
            by rewrite -logn_gt0 lt0n => /negPn /eqP.
        rewrite ltn_neqAle. apply /andP. split; first by rewrite eq_sym.
        by rewrite lt0n.
    rewrite muln1 -big_filter.
    case: (boolP (n < k)) => [nltk|]; first by rewrite (eqseq n).
    rewrite -leqNgt => klen.
    rewrite -[in X in _ <= X](eqseq n n.+1); last exact: ltnSn.
    rewrite -[X in index_iota _ X.+1](subnKC (leq_trans klen (ltnSn n))).
    rewrite -addnS -subSn //.
    rewrite !big_filter /index_iota !subn0 iotaD map_cat big_cat add0n /=.
    apply /leq_pmulr /prodn_gt0 => i.
    exact: pfactor_gt0.
set f : 'I_N.+1 -> A * B := fun n =>
    ([tuple a n i  | i < k], Ordinal (binB n)).
set g : A * B -> nat := fun c => let (a, b) := c in
    b ^ 2 * \prod_(i < k) (prime_seq i) ^ (tnth a i).
have finj: forall x y, x \in P' k N -> y \in P' k N -> f x = f y -> x = y
    => [x y xinPkN yinPkN /(congr1 g)|].
    suff: forall x, x \in P' k N -> g (f x) = x
        => [gfid|{yinPkN y} {}x {}xinPkN /=].
        rewrite (gfid x) // (gfid y) //.
        exact: val_inj.
    rewrite exmnMn_bigprod.
    under eq_bigr => i _. rewrite -expnM muln2 halfK. over.
    rewrite -big_split /=.
    under eq_bigr => i _. rewrite -expnD tnth_mktuple /a subnK. over.
        by case: (boolP (odd (logn (prime_seq i) x))); first exact: odd_gt0.
    case: (boolP (x == ord0)) => [/eqP xeq0|xneq0].
        by move: xeq0 xinPkN => ->; rewrite /P' !inE.
    rewrite [RHS]prod_prime_decomp; last by rewrite lt0n.
    rewrite prime_decompE big_map /=.
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
        by rewrite (leqW_mono prime_seq_incr). 
    - exact: sorted_primes.
    rewrite mem_filter. apply: andb_idr.
    move: xinPkN. rewrite /P' /P inE => /andP [] _.
    rewrite inE => /allP primesxlepk eltinprimesx.
    have []: prime elt /\ elt < prime_seq k.
        split; last exact: primesxlepk.
        by apply /(@allP _ _ (primes x)); first exact: all_prime_primes.
    rewrite -mem_prime_seq inE => /= -[] i _ <- pilepk.
    rewrite map_comp. apply: map_f.
    rewrite -[X in map _ X]filter_predT val_enum_ord mem_iota /= add0n.
    by rewrite -(leqW_mono prime_seq_incr).
have -> : P k N = P' k N :|: [set ord0].
    by rewrite /P' finset.setUC finset.setD1K // inE.
rewrite finset.setUC cardsU1 [in X in X + _]/P' !inE /= add1n ltnS. 
rewrite -(card_in_imset finj).
have imfleqAB:
    #|[set f x  | x in P' k N]| <= #|finset.setX [set: A] (~: [set ord0 : B])|.
    apply /subset_leq_card /fintype.subsetP => y.
    rewrite !inE => /imsetP [] x xinPkN -> /=. apply /eqP.
    apply: (contra_not (@congr1 _ _ val _ _)) => /=.
    apply /eqP. rewrite -lt0n. apply: prodn_gt0 => i.
    rewrite expn_gt0. apply /orP. left. apply: prime_gt0.
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
have unpos: forall n : nat, 0 <= n -> true -> (0%R <= un n)%E => [n _ _|].
    by rewrite /un lee_fin invr_ge0 ler0n.
have: cvgn Sn by apply: is_cvg_nneseries.
have: (limn Sn <= +oo)%E by apply: leey.
rewrite le_eqVlt => /orP [/eqP -> //|].
have: (0%:E <= limn Sn)%E by apply: nneseries_ge0.
move leqlimnSn: (limn Sn) => l.
case: l leqlimnSn => // l leqlimnSn _ _ /subsetP llimnSn. 
have /llimnSn : `](l - (1/2)%R)%:E, (l + (1/2)%R)%:E[ \in nbhs (l%:E).
    rewrite inE. exists (1/2)%R => /=.
        exact: divr_gt0.
    exact /subset_ball_prop_in_itv.
rewrite inE => -[] k /= + nbhslim. apply: True_ind.
set N := 2^(2*k + 2).
set PN := P k N. set GN := G k N.
move: nbhslim => /subsetP nbhslim. move: (nbhslim k).
rewrite inE /= leqnn => /(_ erefl). rewrite set_interval.set_itvoo inE /=.
rewrite EFinB EFinD -leqlimnSn => /andP [] + _.
rewrite lte_subel_addl; last first.
    by rewrite leqlimnSn.
rewrite -lteBlDr; last first.
    exact /sum_fin_numP.
rewrite (nneseries_split _ k); last first => [k0 _|].
    exact: unpos.
rewrite /Sn add0n addrAC subee; last first.
    exact /sum_fin_numP.
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
apply: (@cardG R).
- by move: Rklthalf; rewrite /un div1r.
- rewrite /N. apply /leqW /(leq_trans (ltnW (ltn_expl k (ltnSn 1)))).
    rewrite leq_exp2l // mul2n -addnn -[X in X <= _]addn0.
    by rewrite -addnA leq_add2l.
- by rewrite /N addn2 expnS mul2n odd_double.
by rewrite /N expn_gt0; apply /orP; left.
Qed.

Lemma Abel_discrete0 (R : comPzRingType) (a b : nat -> R) (n : nat) : n > 0 ->
    let A := fun n => (\sum_(0 <= k < n.+1) a k)%R in
    (\sum_(0 <= k < n.+1) (a k) * (b k) = a 0 * b 0 - A 0 * b 1 + A n * b n +
    \sum_(1 <= k < n) A k * (b k - b k.+1))%R.
Proof.
move=> ngt0 A. 
rewrite big_nat_recl // [in LHS](pred_Sn n).
rewrite -(big_add1 _ _ _ _ predT (fun i => (a i * b i)%R)).
have telesum: forall k, k > 0 -> (a k = A k - A k.-1)%R => [k kgt0|].
    rewrite /A (ltn_predK kgt0) // big_nat_recl // -addrA.
    rewrite -sumrN -big_split /= telescope_sumr // addrC -addrA.
    by rewrite [X in (_ + X)%E]addrC subrr addr0.
rewrite big_nat_cond.
under eq_bigr => j /andP [] /andP [] jinseq _ _.
    rewrite (telesum j) // mulrBl. over.
rewrite big_split sumrN /= [X in (_ - X)%R]big_add1 -pred_Sn.
under [X in (_ - X)%R]eq_bigr => i _. rewrite -pred_Sn. over.
rewrite -!big_nat_cond.
rewrite -[in X in (_ - X)%R](prednK ngt0) [in X in (_ - X)%R]big_nat_recl //.
rewrite big_nat_recr //=.
rewrite -(big_add1 _ _ _ _ predT (fun i => (A i * b i.+1)%R)).
rewrite opprD [in LHS](AC (1*(2*2)) ((1*4)*3*(2*5))) /=.
rewrite -sumrN -big_split /=.
under eq_bigr => i _. rewrite -mulrBr. over.
by [].
Qed.

Lemma Abel_discretep (R : comPzRingType) (a b : nat -> R) (n p : nat) :
    n > p -> let A := fun n => (\sum_(0 <= k < n.+1) a k)%R in
    (\sum_(p <= k < n.+1) (a k) * (b k) = a p * b p - A p * b p.+1 +
    A n * b n + \sum_(p.+1 <= k < n) A k * (b k - b k.+1))%R.
Proof.
move=> ngtp A.
rewrite big_nat_recl; last exact: ltnW.
rewrite [in LHS](pred_Sn n) -(big_add1 _ _ _ _ predT (fun i => (a i * b i)%R)).
have telesum: forall k, k > 0 -> (a k = A k - A k.-1)%R => [k kgt0|].
    rewrite /A (ltn_predK kgt0) // big_nat_recl // -addrA.
    rewrite -sumrN -big_split /= telescope_sumr // addrC -addrA.
    by rewrite [X in (_ + X)%E]addrC subrr addr0.
rewrite big_nat_cond.
under eq_bigr => j /andP [] /andP [] jinseq _ _.
    rewrite (telesum j); last exact: (leq_ltn_trans _ jinseq).
    rewrite mulrBl. over.
rewrite big_split sumrN /= [X in (_ - X)%R]big_add1 -pred_Sn.
under [X in (_ - X)%R]eq_bigr => i _. rewrite -pred_Sn. over.
rewrite -!big_nat_cond.
rewrite -[in X in (_ - X)%R](prednK (leq_ltn_trans (leq0n p) ngtp)).
rewrite [in X in (_ - X)%R]big_nat_recl; last first.
    by rewrite -ltnS (prednK (leq_ltn_trans (leq0n p) ngtp)) ngtp.
rewrite big_nat_recr //=.
rewrite -(big_add1 _ _ _ _ predT (fun i => (A i * b i.+1)%R)).
rewrite opprD [in LHS](AC (1*(2*2)) ((1*4)*3*(2*5))) /=.
rewrite -sumrN -big_split /=.
under eq_bigr => i _. rewrite -mulrBr. over.
by [].
Qed.

Lemma measurable_fun_bigsetU [d1 d2 : measure_display] [T1 : sigmaRingType d1]
    [T2 : sigmaRingType d2] [I : eqType] [F : I -> set T1] (f : T1 -> T2)
    (s : seq I) : {in s, forall i, d1.-measurable (F i)} ->
    measurable_fun (\big[setU/set0]_(i <- s) F i) f <->
    {in s, forall i, measurable_fun (F i) f}.
Proof.
elim: s => [_|a l HR].
    split => [_ i|_].
        by rewrite in_nil.
    rewrite big_nil.
    exact: measurable_fun_set0.
rewrite forall_cons => -[] Fameas Fimeas. split.
    rewrite big_cons measurable_funU //.
        by rewrite HR // forall_cons.
    rewrite big_seq. apply: bigsetU_measurable.
    apply /(@allPP _ (fun x => `[< d1.-measurable (F x) >])) => [x|].
        exact: asboolP.
    apply /(@allPP _ _ _ (fun x => d1.-measurable (F x))) => // x.
    exact: asboolP.
rewrite big_cons measurable_funU //.
    by rewrite forall_cons HR.
rewrite big_seq. apply: bigsetU_measurable.
apply /(@allPP _ (fun x => `[< d1.-measurable (F x) >])) => [x|].
    exact: asboolP.
apply /(@allPP _ _ _ (fun x => d1.-measurable (F x))) => // x.
exact: asboolP.
Qed.

Notation "\int_( x 'in' D ) F" := (\int[lebesgue_measure]_(x in D) F)
    (at level 36, F at level 36, x, D at level 50).

Lemma Abel_continuous (R : realType) (x y : R^o) (f : R^o -> R^o)
    (a : nat -> R) : (0 < y < x)%R -> derivable_oo_continuous_bnd f y x ->
    {within `[y, x] : set R^o, continuous f^`()} ->
    let A := fun x : R => (\sum_(0 <= n < `|floor x|.+1) a n)%R in
    ((\sum_(`|floor y|.+1 <= n < `|floor x|.+1) a n * f n%:R)%R%:E =
    (A x * f x - A y * f y)%:E - \int_(t in `[y, x]) (A t * f^`() t)%:E)%E.
Proof.
move=> /andP [] ypos xgty fderivable fC1 A.
set p := `|floor y|; set q := `|floor x|.
have pleq: p <= q.
    rewrite /p /q. apply: lez_abs2; first by rewrite floor_ge0; apply: ltW.
    by rewrite le_floor //; apply: ltW.
move: pleq. rewrite leq_eqVlt => /orP [/eqP peqq|pltq].
    rewrite peqq big_geq; last exact: ltnSn.
    have AteqAx: forall t, t \in `[y, x] -> A t = A x => [t|].
        have floorypos: (0 <= floor y)%R by rewrite floor_ge0; apply: ltW.
        rewrite set_itvcc inE /= => /andP [] /le_floor flyleflt.
        have floortpos: (0 <= floor t)%R by apply: (le_trans floorypos).
        move: flyleflt => /(lez_abs2 floorypos). move: peqq.
        rewrite /p /q => -> flxleflt /le_floor /(lez_abs2 floortpos) fltleflx.
        suff: `|floor t| = `|floor x| by rewrite /A => ->.
        by apply /eqP; rewrite eq_le; apply /andP; split.
    have ->: A y = A x.
        apply: AteqAx. rewrite set_itvcc inE /=.
        apply /andP. split; last exact: ltW.
        exact: lexx.
    rewrite -mulrBr.
    rewrite (@eq_integral _ _ _ lebesgue_measure _
        (fun t => ((A x)%:E * (f^`() t)%:E)%E))
        => /= [|t tininterval]; last by rewrite (AteqAx t tininterval).
    rewrite integralZl //=; last first.
        apply: continuous_compact_integrable => //.
        exact: segment_compact.
    rewrite EFinM -muleBr // (continuous_FTC2 _ _ fderivable) //.
    by rewrite EFinB subee // mule0.
have ->: ((\sum_(p.+1 <= n < q.+1)  a n * f n%:R)%R =
    (\sum_(p.+1 <= n < q)  A n%:R * (f n%:R - f n.+1%:R))%R +
    (A q%:R * f q%:R - A p%:R * f p.+1%:R)%R)%E.
    apply: (addrI (a p * f p%:R)%R).
    rewrite big_add1 -pred_Sn.
    rewrite -(big_nat_recl _ _ (fun i => (a i * f i%:R)%R)); last exact: ltnW.
    rewrite Abel_discretep //.
    rewrite [in LHS](AC 4 (1*(4*(3*2)))) /A /=.
    have flneqn: forall n : nat, `|floor (n%:R : R)| = n => [n|].
        apply: (can_inj absz_nat).
        rewrite gez0_abs; last by rewrite real_floor_ge0.
        by apply /(@intr_inj R) /eqP; rewrite -[_ == _]intrEfloor.
    rewrite !flneqn.
    under [X in (_ = _ + (X + _))%E]eq_bigr => i _. rewrite flneqn. over.
    by [].
have fcontinuous: {in `]y, x[ : set R^o, continuous f}.
    rewrite -continuous_open_subspace //. apply: derivable_within_continuous.
    by case: fderivable.
have tfct1t2 : forall t1 t2, (y <= t1)%R -> (t1 <= t2)%R -> (t2 <= x)%R ->
    ((f t2 - f t1)%:E = \int_(x in `[t1, t2]) (f^`() x)%:E)%E
    => [t1 t2 ylet1 |].
    rewrite le_eqVlt => /orP [/eqP ->|t1ltt2 t2lex].
        by rewrite subrr set_itv1 (integral_Sset1 t2).
    rewrite (@continuous_FTC2 _ _ f) //.
        apply: (continuous_subspaceW _ fC1) => t.
        rewrite !set_itvcc => /= /andP [] tb1 tb2.
        apply /andP. split; first exact: (le_trans ylet1).
        exact: (le_trans tb2).
    split.
    - apply: (@in1_subset_itv _ _ _ `]y, x[%R); last first.
        - by case: fderivable.
        - rewrite !set_itvoo => t /= /andP [] tb1 tb2. apply /andP. split.
            - exact: (le_lt_trans ylet1).
            - exact: (lt_le_trans tb2).
    - move: ylet1. rewrite le_eqVlt => /orP [/eqP <-|yltn].
        - by case: fderivable.
        - apply /cvg_at_right_filter /fcontinuous.
            rewrite inE set_itvoo /=. apply /andP. split => //.
            exact: (lt_le_trans t1ltt2).
    - move: t2lex. rewrite le_eqVlt => /orP [/eqP ->|t2ltx].
        - by case: fderivable.
        - apply: cvg_at_left_filter. apply: fcontinuous.
            rewrite inE set_itvoo /=. apply /andP. split => //. 
            exact: (le_lt_trans ylet1).
have tfcnn1 : forall n : nat, (y <= n%:R)%R -> (n.+1%:R <= x)%R ->
    ((f n%:R - f n.+1%:R)%:E = - \int_(x in `[n%:R, n.+1%:R]) (f^`() x)%:E)%E
    => [n ylen n1lex|].
    rewrite -tfct1t2 //; first by rewrite -opprB.
    by rewrite ler_nat.
have AteqAn: forall n t, (n%:R <= t < n.+1%:R)%R -> A t = A n%:R
    => [n t /andP [] tb1 tb2|].
    have: floor t = n.
        apply /floor_def /andP. split => //.
        by rewrite -natz natr1 mulrz_nat.
    suff: floor n%:R = n => [|t0]; first by rewrite /A => -> ->.
    by apply /(@intr_inj t0) /eqP; rewrite -[_ == _]intrEfloor.
rewrite EFinD -sumEFin big_nat.
have ylei: forall i, p < i -> (y <= i%:R)%R => [i plti|].
    move: plti. rewrite -(ler_nat R). apply: le_trans.
    apply: (le_trans (ltW (floorD1_gt y))).
    rewrite -addn1 /p natrD natr_absz intrD. apply: lerD => //.
    by rewrite ler_int; apply: lez_abs.
have i1lex: forall i, i < q -> (i.+1%:R <= x)%R => [i iltq|].
    move: iltq. rewrite -(ler_nat R) => i1leq.
    apply: (le_trans i1leq).
    apply: (le_trans _ (floor_le_tmp x)).
    rewrite /q natr_absz ler_int le_eqVlt. apply /orP. left.
    apply /eqP. apply /gez0_abs. rewrite floor_ge0. apply: ltW.
    exact: (lt_trans ypos).
have qlex: (q%:R <= x)%R.
    rewrite -[X in (X%:R <= _)%R]prednK; last exact: (leq_ltn_trans _ pltq).
    apply: i1lex. rewrite ltn_predL.
    exact: (leq_ltn_trans _ pltq).
have measfii1: forall i, p < i -> i < q ->
    measurable_fun (`]i%:R, i.+1%:R[ : set R^o) (fun z => (A i%:R * f^`() z)%R)
    => [i plti iltq|].
    apply: open_continuous_measurable_fun => // x0.
    rewrite inE => x0ininterval.
    apply: (@continuousM _ _ _ _ (x0 : R^o)).
        exact: (@cst_continuous _ _ ((A i%:R) : R^o)).
    apply: (within_continuous_continuous xgty) => //=.
    exact: (subset_itvW _ _ (ylei i plti) (i1lex i iltq)).
have measfxii1: forall i, p < i -> i < q ->
    measurable_fun (`]i%:R, i.+1%:R[ : set R^o) (fun z => (A z * f^`() z)%R)
    => [i plti iltq|].
    apply: (eq_measurable_fun (fun z => (A i%:R * f^`() z)%R))
        => [x0|]; last exact: measfii1.
    rewrite set_itvoo inE => /= /andP [] x0b1 x0b2.
    rewrite (AteqAn i) //. apply /andP. split => //.
    exact: ltW.
under eq_bigr => i /andP [] plti iltq. rewrite EFinM tfcnn1.
    rewrite muleN -integralZl //=.
    rewrite (eq_integral_itv_bounded _ _
        (measfii1 i plti iltq) (measfxii1 i plti iltq)).
    over.
- move=> x0 x0ininterval. move: (subset_itv_oo_co x0ininterval) => x0ini.
    by rewrite (AteqAn i).
- apply: continuous_compact_integrable.
    - exact: segment_compact.
    - apply: (continuous_subspaceW _ fC1) => t.
        rewrite !set_itvcc => /= /andP [] tb1 tb2.
        apply /andP. split; first exact: (le_trans (ylei i plti)).
        exact: (le_trans _ (i1lex i iltq)).
- exact: ylei.
- exact: i1lex.
under eq_bigr => i /andP [] plti iltq. rewrite integral_itv_bndoo. over.
    exact: measfxii1.
rewrite sumeN => [|i j]; last first.
    rewrite !unfold_in => /andP [] plti iltq _.
    apply /fin_num_adde_defr /integral_fune_fin_num => //.
    apply: (@eq_integrable _ _ _ lebesgue_measure _ _
        (fun x => (A i%:R * f^`() x)%:E)) => // [x0|].
        rewrite set_itvoo inE => /= /andP [] x0b1 x0b2.
        rewrite (AteqAn i) //. apply /andP. split => //.
        exact: ltW.
    apply: (@integrableS _ _ _ lebesgue_measure
        (`[i%:R, i.+1%:R] : set R^o)) => //; first exact: subset_itvW.
    apply: continuous_compact_integrable => [|x0].
        exact: segment_compact.
    apply: continuousM; first exact: (@cst_continuous _ _ (A i%:R : R^o)).
    apply: (continuous_subspaceW _ fC1) => {}x0.
    rewrite !set_itvcc => /= /andP [] x0b1 x0b2. apply /andP. split.
        exact: (le_trans (ylei i plti)).
    exact: (le_trans _ (i1lex i iltq)).
under eq_bigr => i /andP [] plti iltq. rewrite integral_itv_obnd_cbnd. over.
    exact: measfxii1.
rewrite -big_nat => /=.
have p1qitvU: \big[setU/set0]_(p.+1 <= i < q)  `[i%:R, i.+1%:R[ =
    (`[p.+1%:R, q%:R[ : set R^o).
    rewrite seteqP. split => x0.
        rewrite set_itvco /= -bigcup_seq_cond => -[] i /= /andP [].
        rewrite mem_index_iota => /andP [] plti iltq _ /andP [] x0b1 x0b2.
        apply /andP. split; last by apply: (lt_le_trans x0b2); rewrite ler_nat.
        move: plti. rewrite -(ler_nat R) => p1lei.
        exact: (le_trans p1lei).
    rewrite set_itvco => /= /andP [] p1ltx0 x0ltq.
    rewrite -bigcup_seq_cond. exists `|floor x0| => /=; last first.
        apply /andP. split.
            apply: (le_trans _ (floor_le_tmp x0)).
            rewrite /q natr_absz ler_int le_eqVlt. apply /orP. left.
            apply /eqP /gez0_abs. rewrite floor_ge0.
            exact: (le_trans _ p1ltx0).
        rewrite -natr1 natr_absz intrD1.
        suff ->: `|floor x0|%R = floor x0 by apply: floorD1_gt.
        rewrite -[RHS]gez0_abs //.
        rewrite floor_ge0. apply: (le_trans _ p1ltx0).
        exact: ler0n.
    apply /andP. split => //.
    rewrite mem_index_iota. apply /andP. split; last first.
        rewrite -(ltr_nat R). apply: (le_lt_trans _ x0ltq).
        apply: (le_trans _ (floor_le_tmp x0)).
        rewrite /q natr_absz ler_int le_eqVlt. apply /orP. left.
        apply /eqP /gez0_abs. rewrite floor_ge0.
        exact: (le_trans _ p1ltx0).
    move: p1ltx0. rewrite -natr1 -lerBrDr => plex0m1.
    rewrite -(ltr_nat R). apply: (le_lt_trans plex0m1).
    rewrite ltrBlDr natr_absz intrD1.
    suff ->: `|floor x0|%R = floor x0 by apply: floorD1_gt.
    rewrite -[RHS]gez0_abs //.
    rewrite floor_ge0.
    move: plex0m1. rewrite lerBrDr natr1 => p1ltx0.
    apply: (le_trans _ p1ltx0).
    exact: ler0n.
have measfp1q: measurable_fun (`[p.+1%:R, q%:R[ : set R^o)
    (fun x0 : g_sigma_algebraType R.-ocitv.-measurable => (A x0 * f^`() x0)%R).
    rewrite -p1qitvU measurable_fun_bigsetU => // i.
    rewrite mem_index_iota => /andP [] plti iltq.
    rewrite -setU1itv; last by move: (ltnSn i); rewrite -(ltr_nat R).
    rewrite measurable_funU //. split; first exact: measurable_fun_set1.
    exact: measfxii1.
have measfyp1: measurable_fun (`[y, p.+1%:R[ : set R^o)
    (fun x => (A x * f^`() x)%R).
    apply: (eq_measurable_fun (fun x0 => (A p%:R * f^`() x0)%R)) => [x0|].
        rewrite set_itvco inE => /= /andP [] x0b1 x0b2.
        rewrite (AteqAn p) //. apply /andP. split => //.
        apply: (le_trans _ x0b1). rewrite /p.
        apply: (le_trans _ (floor_le_tmp y)).
        rewrite natr_absz ler_int le_eqVlt. apply /orP. left.
        apply /eqP /gez0_abs. rewrite floor_ge0.
        exact: ltW.
    rewrite -setU1itv; last first.
        rewrite /p -natr1 natr_absz intrD1.
        suff ->: `|floor y|%R = floor y by apply: floorD1_gt.
        rewrite -[RHS]gez0_abs // floor_ge0.
        exact: ltW.
    rewrite measurable_funU //. split; first exact: measurable_fun_set1.
    apply: open_continuous_measurable_fun => // x0.
    rewrite set_itvoo inE => /andP [] x0b1 x0b2.
    apply: (@continuousM _ _ _ _ (x0 : R^o)).
        exact: (@cst_continuous _ _ ((A p%:R) : R^o)).
    apply: (within_continuous_continuous xgty fC1).
    apply /andP. split => //. 
    apply: (lt_le_trans x0b2).
    exact: i1lex.
have measfqx: measurable_fun (`[q%:R, x[ : set R^o)
    (fun x => (A x * f^`() x)%R).
    apply: (eq_measurable_fun (fun x0 => (A q%:R * f^`() x0)%R)) => [x0|].
        rewrite set_itvco inE => /= /andP [] x0b1 x0b2.
        rewrite (AteqAn q) //. apply /andP. split => //.
        apply: (lt_trans x0b2). rewrite /q.
        rewrite -natr1 natr_absz intrD1.
        suff ->: `|floor x|%R = floor x by apply: floorD1_gt.
        rewrite -[RHS]gez0_abs // floor_ge0.
        exact: (le_trans (ltW ypos) (ltW xgty)).
    move: qlex. rewrite le_eqVlt => /orP [/eqP <-|qltx].
        by rewrite set_itvco0; apply: measurable_fun_set0.
    rewrite -setU1itv // measurable_funU //.
    split; first exact: measurable_fun_set1.
    apply: open_continuous_measurable_fun => // x0.
    rewrite set_itvoo inE => /andP [] x0b1 x0b2.
    apply: (@continuousM _ _ _ _ (x0 : R^o)).
        exact: (@cst_continuous _ _ ((A q%:R) : R^o)).
    apply: (within_continuous_continuous xgty fC1).
    apply /andP. split => //. 
    apply: (le_lt_trans _ x0b1).
    exact: ylei.
rewrite -integral_bigsetU_EFin //=; last first.
- apply: measurableT_comp; first exact: EFin_measurable.
    by rewrite p1qitvU; apply: measfp1q.
- apply /trivIsetP => i j _ _ ineqj. rewrite -subset0 => x0.
    wlog iltj: i j ineqj / i < j => [Hw|]; last first.
        rewrite !set_itvco => /= -[] /andP [] iltx0 x0lti1 /andP [] jltx0 x0ltj1.
        suff: (x0 < x0)%R by rewrite ltxx.
        apply /(lt_le_trans x0lti1) /(le_trans _ jltx0).
        by rewrite ler_nat.
    move: ineqj. rewrite neq_ltn => /orP [iltj|jlti].
        apply: Hw => //. move: iltj.
        by rewrite ltn_neqAle => /andP [].
    rewrite setIC. apply: Hw => //. move: jlti.
    by rewrite ltn_neqAle => /andP [].
- exact: iota_uniq.
rewrite p1qitvU.
have itvyx: `[y, x[ = `[y, p.+1%:R[ `|` `[p.+1%:R, q%:R[ `|` `[q%:R, x[.
    rewrite -!itv_bndbnd_setU //.
    - exact: ylei.
    - exact: ylei.
    - by move: pltq; rewrite -(ler_nat R).
have itvyq: `[y, p.+1%:R[ `|` `[p.+1%:R, q%:R[ = `[y, q%:R[.
    rewrite seteqP !set_itvco. split => x0 /= => [[] /andP [] x0b1 x0b2|].
    - apply /andP. split => //. apply: (lt_le_trans x0b2).
        by rewrite ler_nat.
    - apply /andP. split => //.
        exact: (le_trans (ylei p.+1 (ltnSn p)) x0b1).
    - case: (boolP (x0 < p.+1%:R)%R) => [_ /andP [] ylex0 _|].
        - by left; rewrite ylex0.
        - by rewrite -real_leNgt => //= -> /andP [] _ x0ltq; right.
have ->: (\int_(t in `[p.+1%:R, q%:R[) (A t * f^`() t)%:E =
    (- \int_(t in `[y, p.+1%:R[) (A t * f^`() t)%:E) +
    \int_(t in `[y, x[) (A t * f^`() t)%:E -
    \int_(t in `[q%:R, x[) (A t * f^`() t)%:E)%E.
    rewrite itvyx !integral_setU_EFin //=.
    - rewrite [in RHS](AC (1*3*1) ((2*1)*3*(4*5))) /= !subee.
        - by rewrite add0e adde0.
        - apply: integral_fune_fin_num => //.
            apply: (@eq_integrable _ _ _ lebesgue_measure _ _
                (fun x0 => (A q%:R * f^`() x0)%:E)) => // [x0|].
                rewrite set_itvco inE => /= /andP [] x0b1 x0b2.
                rewrite (AteqAn q) //. apply /andP. split => //.
                apply: (lt_trans x0b2). rewrite /q.
                rewrite -natr1 natr_absz intrD1.
                suff ->: `|floor x|%R = floor x by apply: floorD1_gt.
                rewrite -[RHS]gez0_abs // floor_ge0.
                exact /ltW /(lt_trans ypos xgty).
            apply: (@integrableS _ _ _ lebesgue_measure `[q%:R, x])
                => // [x0|].
                rewrite set_itvco set_itvcc => /= /andP [] x0b1 x0b2.
                apply /andP. split => //.
                exact: ltW.
            apply: continuous_compact_integrable => [|x0].
                exact: segment_compact.
            apply: continuousM.
                exact: (@cst_continuous _ _ ((A q%:R) : R^o)).
            apply: (continuous_subspaceW _ fC1) => // {}x0.
            rewrite !set_itvcc => /= /andP [] x0b1 x0b2.
            apply /andP. split => //. apply: (le_trans _ x0b1).
            exact: ylei.
        - apply: integral_fune_fin_num => //.
            apply: (@eq_integrable _ _ _ lebesgue_measure _ _
                (fun x0 => (A p%:R * f^`() x0)%:E)) => // [x0|].
                rewrite set_itvco inE => /= /andP [] x0b1 x0b2.
                rewrite (AteqAn p) //. apply /andP. split => //.
                apply: (le_trans _ x0b1). rewrite /p.
                apply: (le_trans _ (floor_le_tmp y)).
                rewrite natr_absz ler_int le_eqVlt. apply /orP. left.
                apply /eqP /gez0_abs. rewrite floor_ge0.
                exact: ltW.
            apply: (@integrableS _ _ _ lebesgue_measure `[y, p.+1%:R])
                => // [x0|].
                rewrite set_itvco set_itvcc => /= /andP [] x0b1 x0b2.
                apply /andP. split => //.
                exact: ltW.
            apply: continuous_compact_integrable => [|x0].
                exact: segment_compact.
            apply: continuousM.
                exact: (@cst_continuous _ _ ((A p%:R) : R^o)).
            apply: (continuous_subspaceW _ fC1) => // {}x0.
            rewrite !set_itvcc => /= /andP [] x0b1 x0b2.
            apply /andP. split => //.
            exact /(le_trans x0b2) /i1lex.
    - by rewrite measurable_funU.
    - apply /disj_setPS
        => x0 /= [] /andP [] ylex0 x0ltp1 /andP [] p1lex0 x0ltq.
        suff: (x0 < x0)%R by rewrite ltxx.
        exact: (lt_le_trans x0ltp1 p1lex0).
    - by rewrite itvyq.
    - by rewrite !measurable_funU // itvyq.
- apply /disj_setPS => x0.
    rewrite itvyq => /= -[] /andP [] _ x0ltq /andP [] qlex0 _.
    suff: (x0 < x0)%R by rewrite ltxx.
    exact: (lt_le_trans x0ltq qlex0).
rewrite (@eq_integral _ _ _ lebesgue_measure _
    (fun t => ((A p%:R)%:E * (f^`() t)%:E)%E)) => /= [|t]; last first.
    rewrite set_itvco inE => /= /andP [] ylet tltp1.
    rewrite (AteqAn p) //. apply /andP. split => //.
    apply: (le_trans _ ylet).  rewrite /p.
    apply: (le_trans _ (floor_le_tmp y)).
    rewrite natr_absz ler_int le_eqVlt. apply /orP. left.
    apply /eqP /gez0_abs. rewrite floor_ge0.
    exact: ltW.
rewrite [X in (_ + _ - X)%E](@eq_integral _ _ _ lebesgue_measure _
    (fun t => ((A q%:R)%:E * (f^`() t)%:E)%E)) => /= [|t]; last first.
    rewrite set_itvco inE => /= /andP [] ylet tltp1.
    rewrite (AteqAn q) //. apply /andP. split => //.
    apply: (lt_trans tltp1). rewrite /q.
    rewrite -natr1 natr_absz intrD1.
    suff ->: `|floor x|%R = floor x by apply: floorD1_gt.
    rewrite -[RHS]gez0_abs // floor_ge0.
    exact /ltW /(lt_trans ypos xgty).
rewrite !integralZl //=; last first.
- apply: (@integrableS _ _ _ lebesgue_measure `[y, p.+1%:R]) => // [x0|].
    - rewrite set_itvco set_itvcc => /= /andP [] x0b1 x0b2.
        apply /andP. split => //.
        exact: ltW.
    - apply: continuous_compact_integrable  => [|x0].
        - exact: segment_compact.
        - apply: (continuous_subspaceW _ fC1) => // {}x0.
            rewrite !set_itvcc => /= /andP [] x0b1 x0b2.
            apply /andP. split => //. apply: (le_trans x0b2).
            exact: i1lex.
- apply: (@integrableS _ _ _ lebesgue_measure `[q%:R, x]) => // [x0|].
    - rewrite set_itvco set_itvcc => /= /andP [] x0b1 x0b2.
        apply /andP. split => //.
        exact: ltW.
    - apply: continuous_compact_integrable => [|x0].
        - exact: segment_compact.
        - apply: (continuous_subspaceW _ fC1) => // {}x0.
            rewrite !set_itvcc => /= /andP [] x0b1 x0b2.
            apply /andP. split => //. apply: (le_trans _ x0b1).
            exact: ylei.
rewrite !integral_itv_bndo_bndc; last first.
- rewrite -setU1itv; last first.
    - rewrite /p -natr1 natr_absz intrD1.
        suff ->: `|floor y|%R = floor y by apply: floorD1_gt.
        rewrite -[RHS]gez0_abs // floor_ge0.
        exact: ltW.
    - rewrite measurable_funU //. split; first exact: measurable_fun_set1.
        apply: open_continuous_measurable_fun => // x0.
        rewrite set_itvoo inE => /andP [] x0b1 x0b2.
        apply: (within_continuous_continuous xgty fC1).
        apply /andP. split => //. 
        apply: (lt_le_trans x0b2).
        exact: i1lex.
- by rewrite itvyx !measurable_funU // itvyq.
- move: qlex.
    rewrite le_eqVlt => /orP [/eqP <-|qltx].
        by rewrite set_itvco0; apply: measurable_fun_set0.
    rewrite -setU1itv // measurable_funU //.
    split; first exact: measurable_fun_set1.
    apply: open_continuous_measurable_fun => // x0.
    rewrite set_itvoo inE => /andP [] x0b1 x0b2.
    apply: (within_continuous_continuous xgty fC1).
    apply /andP. split => //. 
    apply: (le_lt_trans _ x0b1).
    exact: ylei.
rewrite -!tfct1t2 //; last first.
- exact: i1lex.
- exact: ylei.
- exact: ylei.
rewrite -!EFinM !mulrBr !EFinB. rewrite ![in LHS]oppeB //; last first.
    exact: fin_num_adde_defl.
rewrite oppeD // oppeD //.
rewrite [in LHS](AC (3*2*2) (4*2*3*(7*1)*(6*5))) /=.
rewrite subee // subee // !adde0.
rewrite -(AteqAn _ x); last first.
    rewrite /q -natr1 natr_absz intrD1.
    suff ->: `|floor x|%R = floor x by apply: floor_itv.
    rewrite -[RHS]gez0_abs // floor_ge0.
    exact /ltW /(lt_trans ypos xgty).
rewrite -(AteqAn _ y) //.
rewrite /p -natr1 natr_absz intrD1.
suff ->: `|floor y|%R = floor y by apply: floor_itv.
rewrite -[RHS]gez0_abs // floor_ge0.
exact: ltW.
Qed.

Lemma ltr_powR (R : realType) (a : R) : (1 < a)%R -> {homo powR a : x y / (x < y)%R}.
Proof.
move=> a1 x y xy.
by rewrite /powR gt_eqF ?(lt_trans _ a1)// ltr_expR ltr_pM2r ?ln_gt0.
Qed.

Lemma Gauss_dvdl_bigprod (I : eqType) (r : seq I) (P : {pred I}) (F : I -> nat) (m n : nat) : (forall i, P i -> coprime m (F i)) -> (m %| n * \prod_(i <- r | P i) F i) = (m %| n).
Proof.
elim: r => [|a l HI allcoprimem].
    by rewrite big_nil muln1.
rewrite big_cons.
case: (boolP (P a)) => [Pa|_]; last exact: HI.
by rewrite [X in _ * X]mulnC mulnA (Gauss_dvdl _ (allcoprimem a Pa)) HI.
Qed.

Lemma sumlogpleCx (R : realType) (x : R) : (x >= 1)%R ->
    ((\sum_(1 <= p < `|floor x|.+1 | prime p) ln p%:R)%R <= 4 * ln 2 * x)%R.
move=> xge1.
set theta := fun x : R =>
    (\sum_(1 <= p < `|floor x|.+1 | prime p) ln p%:R)%R : R.
set k := `|floor (ln x / ln 2)|.+1.
set y := 2 ^ k.
have: (2 ^ k.-1 <= x < y%:R)%R => [|/andP [] xb1 xb2].
    apply /andP. split.
        rewrite /k -pred_Sn -powR_intmul // gez0_abs; last first.
            rewrite floor_ge0. apply: divr_ge0.
                exact: ln_ge0.
            by apply: ln_ge0; rewrite ler1n.
        apply: (le_trans (ler_powR _ (floor_le_tmp _))).
            by rewrite ler1n.
        rewrite -[X in (X <= _)%R]lnK; last by rewrite posrE; apply: powR_gt0.
        rewrite ln_powR -mulrA mulVf; last exact /lt0r_neq0 /ln_gt0 /ltr1n.
        rewrite mulr1 lnK // posrE.
        exact: (lt_le_trans _ xge1).
    rewrite /y /k -[X in _ ^ X]addn1 natrX -powR_mulrn // natrD.
    have ->: `|floor (ln x / ln 2)|%:R = (floor (ln x / ln 2))%:~R => [t|].
    rewrite -mulrz_nat natz gez0_abs // floor_ge0.
        apply: divr_ge0; first exact: ln_ge0.
        by apply: ln_ge0; rewrite ler1n.
    rewrite intrD1.
    apply: (le_lt_trans _ (ltr_powR (ltr1n _ 2) (floorD1_gt _))).
    rewrite -[X in (_ <= X)%R]lnK; last by rewrite posrE; apply: powR_gt0.
    rewrite ln_powR -mulrA mulVf; last exact /lt0r_neq0 /ln_gt0 /ltr1n.
    rewrite mulr1 lnK // posrE.
    exact: (lt_le_trans _ xge1).
have yle2x: (y%:R <= 2 * x)%R.
    by rewrite /y -[X in 2 ^ X]prednK // expnS natrM ler_wpM2l // natrX exprnP.
have theta_incr (x0 y0 : R) : (1 <= x0)%R -> (x0 <= y0)%R ->
    (theta x0 <= theta y0)%R => [x0ge1 x0ley0|].
    have flx0lefly0: `|floor x0|.+1 <= `|floor y0|.+1.
        rewrite ltnS. apply: lez_abs2; last exact: le_floor.
        by rewrite floor_ge0; apply: (le_trans _ x0ge1).
    rewrite /theta (big_cat_nat _ flx0lefly0) //= lerDl.
    apply: sumr_ge0 => p primep. apply: ln_ge0. rewrite ler1n.
    exact: prime_gt0.
apply: (le_trans (theta_incr x y%:R xge1 (ltW xb2))).
apply: (@le_trans _ _ (2 * ln 2 * y%:R)%R); last first.
    rewrite mulrC -ler_pdivlMr; last first.
        apply: mulr_gt0 => //. 
        exact /ln_gt0 /ltr1n.
    rewrite -mulrA -mulf_div [X in (_ * (X / _))%R]mulrC.
    rewrite -[X in (_ / _ * X)%R]mulrA -natr1 -natr1 -addrA -!mulr2n.
    rewrite -[X in (X / _ * _)%R]mulr_natr -[X in (X * _)%R]mulrA.
    rewrite !divff ?lt0r_neq0 //; first by rewrite !mulr1.
    exact /ln_gt0 /ltr1n.
suff theta2n_m_thetan_le_2nln2: forall n,
    (2 * n%:R * ln 2 >= theta (2 * n%:R) - theta n%:R)%R => [|n].
    have: (theta (y %/ 2 ^ k)%:R = 0)%R.
        rewrite /y divnn expn_gt0 /= /theta floor1 absz1 big_nat_cond big1 //
        => i /andP [] /andP [] igt0 ilt2 primei.
        move: (prime_gt1 primei) => igt1.
        by have: 2 < 2 by apply: (leq_trans _ ilt2); rewrite ltnS.
    rewrite -[X in (X <= _)%R]subr0 => <-.
    rewrite -[X in theta X%:R]divn1 -[X in (y %/ X)%:R](expn0 2) -opprB.
    rewrite -(telescope_sumr (fun i => theta (y %/ 2 ^ i)%:R)) // -sumrN.
    under eq_bigr => i _. rewrite opprB. over.
    suff: ((\sum_(0 <= i < k) (1 / (2 ^ i)%:R)%R) * ln 2 * y%:R <=
        (2 * ln 2 * y%:R : R))%R.
        apply: le_trans. rewrite !mulr_suml !big_nat.
        apply: ler_sum => i /andP [] _ iltk2.
        rewrite [X in (_ <= X)%R](AC 4 (1*4*2*3)) /= mul1r -natr_div; last first.
        - by rewrite unitrE divff // pnatr_eq0 -lt0n expn_gt0; apply /orP; left.
        - by rewrite dvdn_Pexp2l //; apply: ltnW.
        rewrite -[X in (theta X%:R - _)%R](@divnK 2); last first.
            rewrite /y -expnB //; last by rewrite ltnW.
            by apply: (dvdn_exp _ (dvdnn 2)); rewrite subn_gt0.
        rewrite mulnC -divnMA -expnSr -[X in (X%:R * ln 2)%R](@divnK 2).
            by rewrite [in X in (_ <= X)%R]mulnC -divnMA -expnSr natrM.
        rewrite /y -expnB //; last by rewrite ltnW.
        by apply: (dvdn_exp _ (dvdnn 2)); rewrite subn_gt0.
    rewrite -!mulrA. apply: ler_wpM2r.
        apply: mulr_ge0; first by apply /ln_ge0 /ltW; rewrite mulr2n ltrDl.
        exact /ltW /(le_lt_trans (le_trans _ xge1) xb2).
    under eq_bigr => i _.
        rewrite natrX -[X in X / _](expr1n _ i) -expr_div_n. over.
    suff ->: (\sum_(0 <= i < k) (1 / 2) ^+ i = (2 - 1 / 2 ^ k.-1 : R))%R.
        by rewrite gerBl; apply /divr_ge0 /exprz_ge0.
    apply: (@mulfI _ (1/2 - 1)).
        apply: ltr0_neq0.
        by rewrite subr_lt0 ltr_pdivrMr // mulr_natr mulr2n ltrDl.
    rewrite big_mkord -subrX1 mulrBr !mulrBl !mul1r mulVf; last first.
        exact: lt0r_neq0.
    rewrite opprB [RHS]addrC -[X in (X - _ / _)%R]mul1r -mulrBl.
    rewrite -[X in (X - 2^-1)%R](@mulfV _ 2); last exact: lt0r_neq0.
    rewrite -[X in (2 / 2 - X)%R]div1r -mulrBl -[in X in (X / 2)%R]natr1.
    rewrite -addrA subrr addr0 -[X in (_ = _ + (_ - X)%R)%R]natr1 opprD.
    rewrite [X in (_ / _ + X)%R]addrA subrr add0r div1r -invrM; last first.
    - by rewrite unitrE divff //; apply: lt0r_neq0.
    - by rewrite unitrE divff //; apply /lt0r_neq0 /exprz_gt0.
    by rewrite -exprnP -exprSr exprVn prednK.
rewrite -ler_expR -ln_powR lnK; last by rewrite posrE powR_gt0.
have flnlefl2n: `|floor (n%:R : R)|.+1 <= `|floor (2 * n%:R : R)|.+1.
    rewrite ltnS. apply: lez_abs2; first by rewrite floor_ge0.
    exact /le_floor /ler_peMl /ler1n.
rewrite /theta (big_cat_nat _ flnlefl2n) //=.
have flneqn: forall n, `|floor (n%:R : R)| = n => [n0|].
    apply: (can_inj absz_nat).
    rewrite gez0_abs; last by rewrite real_floor_ge0.
    by apply /(@intr_inj R) /eqP; rewrite -[_ == _]intrEfloor.
rewrite -natrM !flneqn [X in expR X](AC 3 (2*(1*3))) /= subrr addr0.
rewrite -(big_morph_in _ _ _ _ (@lnM _) (ln1 _))
    => [|x0 y0||i primei]; rewrite ?posrE //; last first.
- by rewrite ltr0n prime_gt0.
- exact: mulr_gt0.
rewrite lnK; last first.
    rewrite posrE. apply: prodr_gt0 => i primei.
    by rewrite ltr0n prime_gt0.
apply: (@le_trans _ _ 'C(2 * n, n)%:R); last first.
    rewrite powR_mulrn // -natrX ler_nat -[X in X ^ _]addn1.
    rewrite expnDn. under eq_bigr => i _. rewrite !exp1n !muln1. over.
    have nlt2n1: n < (2 * n).+1 by rewrite ltnS leq_pmull.
    by rewrite (bigD1_ord (Ordinal nlt2n1)) //= leq_addr.
rewrite -natr_prod ler_nat bin_ffactd ffact_prod -(big_mkord predT).
rewrite [in X in _ <= X](bigID (fun i => prime (2 * n - i))) /=.
have pp2nmidvd: \prod_(0 <= i < n | prime (2 * n - i))  (2 * n - i) %| (2 * n) ^_ n.
    rewrite ffact_prod.
    apply /Gauss_dvd_bigprod => [|i]; last first.
        rewrite mem_index_iota => /andP [] _ iltn prime_fi.
        rewrite (Euclid_dvd_prod _ _ _ prime_fi) big_has.
        by apply /hasP; exists (Ordinal iltn).
    apply /(pairwiseP 0) => i j /= ilt jlt iltj.
    rewrite prime_coprime; last first.
        have: nth 0 [seq 2 * n - i0  | i0 <- index_iota 0 n  &
            prime (2 * n - i0)] i \in [seq 2 * n - i0  | i0 <-
            index_iota 0 n  & prime (2 * n - i0)].
            exact: mem_nth.
        by rewrite -filter_map mem_filter => /andP [].
    rewrite dvdn_prime2; last first.
    - have: nth 0 [seq 2 * n - i0  | i0 <- index_iota 0 n  & prime
        (2 * n - i0)] j \in [seq 2 * n - i0  | i0 <- index_iota 0
        n  & prime (2 * n - i0)].
        - exact: mem_nth.
        - by rewrite -filter_map mem_filter => /andP [].
    - have: nth 0 [seq 2 * n - i0  | i0 <- index_iota 0 n  & prime
        (2 * n - i0)] i \in [seq 2 * n - i0  | i0 <- index_iota 0
        n  & prime (2 * n - i0)].
        - exact: mem_nth.
        - by rewrite -filter_map mem_filter => /andP [].
    have /uniqP nthinj: uniq [seq 2 * n - i0  | i0 <- index_iota 0
        n  & prime (2 * n - i0)].
        rewrite map_inj_in_uniq => [|i0 j0].
            exact /filter_uniq /iota_uniq.
        rewrite !mem_filter !mem_index_iota => /andP [] _ /andP []
            _ i0ltn /andP [] _ /andP [] _ j0ltn /eqP.
        rewrite eqn_sub2lE => [/eqP //||].
            exact: (leq_trans (ltnW _) (leq_pmull _ (ltn0Sn _))).
        exact: (leq_trans (ltnW _) (leq_pmull _ (ltn0Sn _))).
    apply /eqP. move: (nthinj 0 i j ilt jlt) => nthinj2.
    apply /(contra_not nthinj2) /eqP. rewrite neq_ltn. 
    by apply /orP; left.
have ->: \prod_(0 <= i < n | ~~ prime (2 * n - i))  (2 * n - i) =
    (2 * n) ^_ n %/ \prod_(0 <= i < n | prime (2 * n - i)) (2 * n - i).
    apply /eqP. rewrite eqn_div; last exact pp2nmidvd.
        rewrite [X in _ * X]big_nat_cond big_nat_cond mulnC -bigID /=.
        by rewrite -big_nat ffact_prod big_mkord.
    rewrite big_nat_cond.
    apply: prodn_cond_gt0 => i /andP [] /andP [] _ iltn _.
    by rewrite subn_gt0; apply: (leq_trans iltn (leq_pmull _ (ltn0Sn _))).
rewrite muln_divA // mulKn; last first.
    rewrite big_nat_cond.
    apply: prodn_cond_gt0 => i /andP [] /andP [] _ iltn _.
    by rewrite subn_gt0; apply: (leq_trans iltn (leq_pmull _ (ltn0Sn _))).
rewrite (leq_divRL _ _ (fact_gt0 n)).
apply: dvdn_leq; first by rewrite ffact_gt0; apply: (leq_pmull _ (ltn0Sn _)).
suff eqprod: \prod_(n.+1 <= i < (2 * n).+1 | prime i) i =
    \prod_(0 <= i < n | prime (2 * n - i)) (2 * n - i).
    rewrite mulnC -dvdn_divRL; last by rewrite eqprod.
    rewrite -(@Gauss_dvdl_bigprod _ (index_iota n.+1 (2 * n).+1)
        (fun i => (n.+1 <= i < (2 * n).+1) && prime i) id)
        => [|i /andP [] /andP [] nlti _ primei].
        rewrite -big_nat_cond divnK; last by rewrite eqprod.
        by rewrite -bin_ffact; apply /dvdn_mull /dvdnn.
    rewrite coprime_sym (prime_coprime _ primei) -[X in _ %| X]mul1n.
    rewrite fact_prod big_nat Gauss_dvdl_bigprod
        => [|m /andP [] mgt0 mltn1]; first by rewrite Euclid_dvd1.
    rewrite (prime_coprime _ primei). apply: (contraNN (dvdn_leq mgt0)).
    by rewrite -ltnNge; apply: (leq_trans _ nlti).
rewrite big_add1 -pred_Sn big_nat_rev /= -[X in index_iota X _]add0n.
rewrite big_addn [in X in index_iota _ X]mul2n -addnn.
rewrite (subDnAC _ (leqnn n)) subnn add0n.
have inlt3n: forall i, 0 <= i < n -> i + n < n + 2 * n
    => [i /andP [] _ iltn|].
    rewrite addnC ltn_add2l. 
    exact: (leq_trans iltn (leq_pmull _ (ltn0Sn _))).
rewrite big_mkcond /=.
under eq_big_seq => i. rewrite mem_index_iota => iinbounds.
    rewrite (subnSK (inlt3n i iinbounds)) subnDAC.
    rewrite (subDnCA _ (leqnn n)) subnn addn0. over.
by rewrite -big_mkcond.
Qed.

Lemma Mertens2 (R : realType) (x : R) : (x > 1)%R -> let R0 := fun t =>
    (\sum_(2 <= p < `|floor x|.+1 | prime p) (ln p%:R / p%:R) - ln t)%R in
    let a0 := (1 - (ln (ln 2))%:E +
    \int_(t in `[2%R, +oo[) (R0 t / (t * (ln t) `^ 2))%:E)%E in let C0 := 10%:R in
    ((\sum_(2 <= p < `|floor x|.+1 | prime p) p%:R^-1)%:E <=
    (ln (ln x))%:E + a0 + (C0 / ln x)%:E)%E.
Proof.
move=> xge1.
set u := fun n => if prime n then (ln n%:R / n%:R)%R else 0%R : R.
set f := fun t => (ln t)^-1 : R.
set R0 := fun t =>
    (\sum_(2 <= p < `|floor x|.+1 | prime p) (ln p%:R / p%:R) - ln t)%R.
rewrite [in X in let _ := _ in X]big_mkcond big_nat /=.
set a := (1 - (ln (ln 2))%:E +
    \int_(t in `[2%R, +oo[) (R0 t / (t * (ln t) `^ 2))%:E)%E.
set C := 10%:R.
under eq_bigr => p /andP [] pgt1 _.
    rewrite -[X in if _ then X else _]mulr1.
    rewrite -[X in (_ * X)%R](@divff _ (ln p%:R)); last first.
        by apply /lt0r_neq0 /ln_gt0; rewrite ltr1n.
    rewrite mulrA [X in (X / _)%R]mulrC -(mul0r (ln p%:R)^-1).
    rewrite -(fun_if (fun x => x / ln p%:R)). over.
have <-: `|floor (1 : R)|.+1 = 2 by rewrite floor1 absz1.
rewrite -big_nat. rewrite (@Abel_continuous _ _ _ f u); last first.
- admit.
- rewrite /derivable_oo_continuous_bnd //=; split => [t /andP [] tge1 tlex||].
    - move=> //= t0.