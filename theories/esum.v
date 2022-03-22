(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
Require Import boolp reals mathcomp_extra ereal classical_sets signed topology.
Require Import sequences functions cardinality.

(******************************************************************************)
(*                      Summation over classical sets                         *)
(*                                                                            *)
(* This file provides a definition of sum over classical sets and a few       *)
(* lemmas in particular for the case of sums of non-negative terms.           *)
(*                                                                            *)
(*            fsets S == the set of finite sets (fset) included in S          *)
(* \esum_(i in I) f i == summation of non-negative extended real numbers over *)
(*                       classical sets; I is a classical set and f is a      *)
(*                       function whose codomain is included in the extended  *)
(*                       reals; it is 0 if I = set0 and sup(\sum_A a) where A *)
(*                       is a finite set included in I o.w.                   *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\esum_ ( i 'in' P ) F"
  (at level 41, F at level 41, format "\esum_ ( i  'in'  P )  F").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section set_of_fset_in_a_set.
Variable (T : choiceType).
Implicit Type S : set T.

Definition fsets S : set {fset T} := [set F | [set` F] `<=` S].

Lemma fsets_set0 S : fsets S fset0. Proof. by []. Qed.

Lemma fsets_self (F : {fset T}) : fsets [set x | x \in F] F.
Proof. by []. Qed.

Lemma fsetsP S (F : {fset T}) : [set` F] `<=` S <-> fsets S F.
Proof. by []. Qed.

Lemma fsets0 : fsets set0 = [set fset0].
Proof.
rewrite predeqE => A; split => [|->]; last exact: fsets_set0.
by rewrite /fsets /= subset0 => /eqP; rewrite set_fset_eq0 => /eqP.
Qed.

End set_of_fset_in_a_set.

Section esum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition esum S a := ereal_sup [set \sum_(x <- A) a x | A in fsets S].

Local Notation "\esum_ ( i 'in' P ) A" := (esum P (fun i => A)).

Lemma esum_set0 a : \esum_(i in set0) a i = 0.
Proof.
rewrite /esum fsets0 [X in ereal_sup X](_ : _ = [set 0%E]) ?ereal_sup1//.
rewrite predeqE => x; split; first by move=> [_ /= ->]; rewrite big_seq_fset0.
by move=> -> /=; exists fset0 => //; rewrite big_seq_fset0.
Qed.

End esum.

Notation "\esum_ ( i 'in' P ) F" := (esum P (fun i => F)) : ring_scope.

Section esum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> \bar R).

Lemma esum_ge0 (S : set T) a : (forall x, S x -> 0 <= a x) -> 0 <= \esum_(i in S) a i.
Proof.
move=> a0.
by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
Qed.

Lemma esum_fset (F : {fset T}) a : (forall i, i \in F -> 0 <= a i) ->
  \esum_(i in [set` F]) a i = \sum_(i <- F) a i.
Proof.
move=> f0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' F'F <-]; apply/lee_sum_nneg_subfset.
  exact/fsetsP.
by move=> t; rewrite inE => /andP[_ /f0].
Qed.

Lemma sum_fset_set (A : set T) a : finite_set A ->
  (forall i, A i -> 0 <= a i) ->
  \sum_(i <- fset_set A) a i = \esum_(i in A) a i.
Proof.
move=> Afin a0; rewrite -esum_fset => [|i]; rewrite ?fset_setK//.
by rewrite in_fset_set ?inE//; apply: a0.
Qed.

End esum_realType.

Lemma esum_ge [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) x :
  (exists2 X : {fset T}, fsets I X & x <= \sum_(i <- X) a i) ->
  x <= \esum_(i in I) a i.
Proof. by move=> [X IX /le_trans->//]; apply: ereal_sup_ub => /=; exists X. Qed.

Lemma esum0 [R : realFieldType] [I : choiceType] (D : set I) (a : I -> \bar R) :
  (forall i, D i -> a i = 0) -> \esum_(i in D) a i = 0.
Proof.
move=> a0; rewrite /esum (_ : [set _ | _ in _] = [set 0]) ?ereal_sup1//.
apply/seteqP; split=> x //= => [[X XI] <-|->].
  by rewrite big_seq_cond big1// => i /andP[Xi _]; rewrite a0//; apply: XI.
by exists fset0; rewrite ?big_seq_fset0.
Qed.

Lemma le_esum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i <= b i) ->
  \esum_(i in I) a i <= \esum_(i in I) b i.
Proof.
move=> le_ab; rewrite ub_ereal_sup => //= _ [X XI] <-; rewrite esum_ge//.
exists X => //; rewrite big_seq_cond [x in _ <= x]big_seq_cond lee_sum => // i.
by rewrite andbT => /XI /le_ab.
Qed.

Lemma eq_esum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i = b i) ->
  \esum_(i in I) a i = \esum_(i in I) b i.
Proof. by move=> e; apply/eqP; rewrite eq_le !le_esum// => i Ii; rewrite e. Qed.

Lemma esumD [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> 0 <= a i) -> (forall i, I i -> 0 <= b i) ->
  \esum_(i in I) (a i + b i) = \esum_(i in I) a i + \esum_(i in I) b i.
Proof.
move=> ag0 bg0; apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ub_ereal_sup//= => x [X XI] <-; rewrite big_split/=.
  by rewrite lee_add// ereal_sup_ub//=; exists X.
wlog : a b ag0 bg0 / \esum_(i in I) a i \isn't a fin_num => [saoo|]; last first.
  move=> /fin_numPn[->|/[dup] aoo ->]; first by rewrite /adde/= lee_ninfty.
  rewrite (@le_trans _ _ +oo)//; first by rewrite /adde/=; case: esum.
  rewrite lee_pinfty_eq; apply/eqP/eq_infty => y; rewrite esum_ge//.
  have : y%:E < \esum_(i in I) a i by rewrite aoo// lte_pinfty.
  move=> /ereal_sup_gt[_ [X XI] <-] /ltW yle; exists X => //=.
  rewrite (le_trans yle)// big_split lee_addl// big_seq_cond sume_ge0 => // i.
  by rewrite andbT => /XI; apply: bg0.
  case: (boolP (\esum_(i in I) a i \is a fin_num)) => sa; last exact: saoo.
case: (boolP (\esum_(i in I) b i \is a fin_num)) => sb; last first.
  by rewrite addeC (eq_esum (fun _ _ => addeC _ _)) saoo.
rewrite -lee_subr_addr// ub_ereal_sup//= => _ [X XI] <-.
have saX : \sum_(i <- X) a i \is a fin_num.
  apply: contraTT sa => /fin_numPn[] sa.
    suff : \sum_(i <- X) a i >= 0 by rewrite sa.
    by rewrite big_seq_cond sume_ge0 => // i; rewrite ?andbT => /XI/ag0.
  apply/fin_numPn; right; apply/eqP; rewrite -lee_pinfty_eq esum_ge//.
  by exists X; rewrite // sa.
rewrite lee_subr_addr// addeC -lee_subr_addr// ub_ereal_sup//= => _ [Y YI] <-.
rewrite lee_subr_addr// addeC esum_ge//; exists (X `|` Y)%fset.
  by move=> i/=; rewrite inE => /orP[/XI|/YI].
rewrite big_split/= lee_add//=.
  rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUl.
  by move=> x; rewrite !inE/= => /andP[/negPf->]/= => /YI/ag0.
rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUr.
by move=> x; rewrite !inE/= => /andP[/negPf->]/orP[]// => /XI/bg0.
Qed.

Lemma esum_mkcond [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) :
  \esum_(i in I) a i = \esum_(i in [set: T]) if i \in I then a i else 0.
Proof.
apply/eqP; rewrite eq_le !ub_ereal_sup//= => _ [X XI] <-; rewrite -?big_mkcond//=.
  rewrite big_fset_condE/=; set Y := [fset _ | _ in X & _]%fset.
  rewrite ereal_sup_ub//; exists Y => //= i /=.
  by rewrite 2!inE/= => /andP[_]; rewrite inE.
rewrite ereal_sup_ub//; exists X => //; rewrite -big_mkcond/=.
rewrite big_seq_cond [RHS]big_seq_cond; apply: eq_bigl => i.
by case: (boolP (i \in X)) => //= /XI Ii; apply/mem_set.
Qed.

Lemma esum_mkcondr [R : realType] [T : choiceType] (I J : set T) (a : T -> \bar R) :
  \esum_(i in I `&` J) a i = \esum_(i in I) if i \in J then a i else 0.
Proof.
rewrite esum_mkcond [RHS]esum_mkcond; apply: eq_esum=> i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma esum_mkcondl [R : realType] [T : choiceType] (I J : set T) (a : T -> \bar R) :
  \esum_(i in I `&` J) a i = \esum_(i in J) if i \in I then a i else 0.
Proof.
rewrite esum_mkcond [RHS]esum_mkcond; apply: eq_esum=> i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma esumID (R : realType) (I : choiceType) (B : set I) (A : set I)
  (F : I -> \bar R) :
  (forall i, A i -> F i >= 0) ->
  \esum_(i in A) F i = (\esum_(i in A `&` B) F i) +
                        (\esum_(i in A `&` ~` B) F i).
Proof.
move=> F0; rewrite !esum_mkcondr -esumD; do ?by move=> i /F0; case: ifP.
by apply: eq_esum=> i; rewrite in_setC; case: ifP; rewrite /= (adde0, add0e).
Qed.
Arguments esumID {R I}.

Lemma esum_sum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (r : seq T2) (P : pred T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, I i -> P j -> 0 <= a i j) ->
  \esum_(i in I) \sum_(j <- r | P j) a i j =
  \sum_(j <- r | P j) \esum_(i in I) a i j.
Proof.
move=> a_ge0; elim: r => [|j r IHr]; rewrite ?(big_nil, big_cons)// -?IHr.
  by rewrite esum0// => i; rewrite big_nil.
case: (boolP (P j)) => Pj; last first.
  by apply: eq_esum => i Ii; rewrite big_cons (negPf Pj).
have aj_ge0 i : I i -> a i j >= 0 by move=> ?; apply: a_ge0.
rewrite -esumD//; last by move=> i Ii; apply: sume_ge0 => *; apply: a_ge0.
by apply: eq_esum => i Ii; rewrite big_cons Pj.
Qed.

Lemma esum_esum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (J : T1 -> set T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, 0 <= a i j) ->
  \esum_(i in I) \esum_(j in J i) a i j = \esum_(k in I `*`` J) a k.1 k.2.
Proof.
move=> a_ge0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ub_ereal_sup => /= _ [X IX] <-.
  under eq_bigr do rewrite esum_mkcond.
  rewrite -esum_sum; last by move=> i j _ _; case: ifP.
  under eq_esum do rewrite -big_mkcond/=.
  apply: ub_ereal_sup => /= _ [Y _ <-]; apply: ereal_sup_ub => /=.
  exists [fset z | z in X `*` Y & z.2 \in J z.1]%fset => //=.
    move=> z/=; rewrite !inE/= -andbA => /and3P[Xz1 Yz2 zJ].
    by split; [exact: IX | rewrite inE in zJ].
  rewrite (exchange_big_dep xpredT)//= pair_big_dep_cond/=.
  apply: eq_fbigl => -[/= k1 k2]; rewrite !inE -andbA.
  apply/idP/imfset2P => /= [/and3P[kX kY kJ]|].
    exists k1; rewrite ?(andbT, inE)//=.
    by exists k2; rewrite ?(andbT, inE)//= kY kJ.
  by move=> [{}k1 + [{}k2 + [-> ->]]]; rewrite !inE andbT => -> /andP[-> ->].
apply: ub_ereal_sup => _ /= [X/= XIJ] <-; apply: esum_ge.
pose X1 := [fset x.1 | x in X]%fset.
pose X2 := [fset x.2 | x in X]%fset.
exists X1; first by move=> x/= /imfsetP[z /= zX ->]; have [] := XIJ z.
apply: (@le_trans _ _ (\sum_(i <- X1) \sum_(j <- X2 | j \in J i) a i j)).
  rewrite pair_big_dep_cond//=; set Y := Imfset.imfset2 _ _ _ _.
  rewrite [leRHS](big_fsetID _ (mem X))/=.
  rewrite (_ : [fset x | x in Y & x \in X] = Y `&` X)%fset; last first.
     by apply/fsetP => x; rewrite 2!inE.
  rewrite (fsetIidPr _); first by rewrite lee_addl// sume_ge0.
  apply/fsubsetP => -[i j] Xij; apply/imfset2P.
    exists i => //=; rewrite ?inE ?andbT//=.
    by apply/imfsetP; exists (i, j).
  exists j => //; rewrite !inE/=; have /XIJ[/= _ Jij] := Xij.
  by apply/andP; split; rewrite ?inE//; apply/imfsetP; exists (i, j).
rewrite big_mkcond [leRHS]big_mkcond.
apply: lee_sum => i Xi; rewrite ereal_sup_ub => //=.
exists [fset j in X2 | j \in J i]%fset; last by rewrite -big_fset_condE.
by move=> j/=; rewrite !inE => /andP[_]; rewrite inE.
Qed.

Lemma lee_sum_fset_nat (R : realDomainType)
    (f : (\bar R)^nat) (F : {fset nat}) n (P : pred nat) :
    (forall i, P i -> 0%E <= f i) ->
    [set` F] `<=` `I_n ->
  \sum_(i <- F | P i) f i <= \sum_(0 <= i < n | P i) f i.
Proof.
move=> f0 Fn; rewrite [leRHS](bigID (mem F))/=.
suff -> : \sum_(0 <= i < n | P i && (i \in F)) f i = \sum_(i <- F | P i) f i.
  by rewrite lee_addl ?sume_ge0// => i /andP[/f0].
rewrite -big_filter -[RHS]big_filter; apply: perm_big.
rewrite uniq_perm ?filter_uniq ?index_iota ?iota_uniq ?fset_uniq//.
move=> i; rewrite ?mem_filter.
case: (boolP (P i)) => //= Pi; case: (boolP (i \in F)) => //= Fi.
by rewrite mem_iota leq0n add0n subn0/=; apply: Fn.
Qed.
Arguments lee_sum_fset_nat {R f} F n P.

Lemma lee_sum_fset_lim (R : realType) (f : (\bar R)^nat) (F : {fset nat})
    (P : pred nat) :
  (forall i, P i -> 0%E <= f i) ->
  \sum_(i <- F | P i) f i <= \sum_(i <oo | P i) f i.
Proof.
move=> f0; pose n := (\max_(k <- F) k).+1.
rewrite (le_trans (lee_sum_fset_nat F n _ _ _))//; last first.
  exact: ereal_nneg_series_lim_ge.
move=> k /= kF; rewrite /n big_seq_fsetE/=.
by rewrite -[k]/(val [`kF]%fset) ltnS leq_bigmax.
Qed.
Arguments lee_sum_fset_lim {R f} F P.

Lemma ereal_pseries_esum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \esum_(i in [set x | P x]) a i.
Proof.
move=> a0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: (ereal_lim_le (is_cvg_ereal_nneg_series_cond a0)); apply: nearW => n.
  apply: ereal_sup_ub => /=; exists [fset val i | i in 'I_n & P i]%fset.
    by move=> /= k /imfsetP[/= i]; rewrite inE => + ->.
  rewrite big_imfset/=; last by move=> ? ? ? ? /val_inj.
  by rewrite big_filter big_enum_cond/= big_mkord.
apply: ub_ereal_sup => _ [/= F /fsetsP PF <-].
rewrite -(big_rmcond_in P)/=; last by move=> i /PF ->.
by apply: lee_sum_fset_lim.
Qed.

Lemma reindex_esum (R : realType) (T T' : choiceType)
    (P : set T) (Q : set T') (e : T -> T') (a : T' -> \bar R) :
    set_bij P Q e ->
    (forall i, P i -> 0 <= a (e i)) ->
  \esum_(j in Q) a j = \esum_(i in P) a (e i).
Proof.
elim/choicePpointed: T => T in e P *.
  rewrite !emptyE => /Pbij[{}e ->] _.
  by rewrite -[in LHS](image_eq e) image_set0 !esum_set0.
elim/choicePpointed: T' => T' in a e Q *; first by have := no (e point).
move=> /(@pPbij _ _ _)[{}e ->] a_ge0.
gen have le_esum : T T' a P Q e a_ge0 /
    \esum_(j in Q) a j <= \esum_(i in P) a (e i); last first.
  apply/eqP; rewrite eq_le le_esum//=.
  rewrite [leRHS](_ : _ = \esum_(j in Q) a (e (e^-1%FUN j))); last first.
    by apply: eq_esum => i Qi; rewrite invK ?inE.
  by rewrite le_esum => //= i Qi; rewrite a_ge0//; apply: funS.
rewrite ub_ereal_sup => //= _ [X XQ <-]; rewrite ereal_sup_ub => //=.
exists (e^-1 @` X)%fset; first by move=> _ /imfsetP[t' /= /XQ Qt' ->]; apply: funS.
rewrite big_imfset => //=; last first.
  by move=> x y /XQ Qx /XQ Qy /(congr1 e); rewrite !invK ?inE.
by apply: eq_big_seq => i /XQ Qi; rewrite invK ?inE.
Qed.
Arguments reindex_esum {R T T'} P Q e a.

Lemma esum_image (R : realType) (T T' : choiceType)
    (P : set T) (e : T -> T') (a : T' -> \bar R) :
    set_inj P e -> (forall i, P i -> 0 <= a (e i)) ->
  \esum_(j in e @` P) a j = \esum_(i in P) a (e i).
Proof. by move=> /inj_bij; apply: reindex_esum. Qed.
Arguments esum_image {R T T'} P e a.

Lemma esum_pred_image (R : realType) (T : choiceType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) :
    (forall n, P n -> 0 <= a (e n)) ->
    set_inj P e ->
  \esum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof. by move=> a0 einj; rewrite esum_image// ereal_pseries_esum. Qed.
Arguments esum_pred_image {R T} a e P.

Lemma esum_set_image  [R : realType] [T : choiceType] [a : T -> \bar R]
    [e : nat -> T] [P : set nat] :
    (forall n : nat, P n -> 0 <= a (e n)) ->
  set_inj P e ->
  \esum_(i in [set e x | x in P]) a i = \sum_(i <oo | i \in P) a (e i).
Proof.
move=> a0 einj; rewrite esum_image// ereal_pseries_esum ?set_mem_set//.
by move=> n; rewrite inE => /a0.
Qed.
Arguments esum_set_image {R T} a e P.

Section esum_bigcup.
Variables (R : realType) (T : choiceType) (K : set nat).
Implicit Types (J : nat -> set T) (a : T -> \bar R).

Lemma esum_bigcupT J a : trivIset setT J -> (forall x, 0 <= a x) ->
  \esum_(i in \bigcup_(k in K) (J k)) a i =
  \esum_(i in K) \esum_(j in J i) a j.
Proof.
move=> tJ a0; rewrite esum_esum//; apply: reindex_esum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2]; rewrite ?inE/=.
  move=> [K1 J1] [K2 J2] j12; congr (_, _) => //.
  by apply: (@tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

Lemma esum_bigcup J a : trivIset [set i | a @` J i != [set 0]] J ->
    (forall x : T, (\bigcup_(k in K) J k) x -> 0 <= a x) ->
  \esum_(i in \bigcup_(k in K) J k) a i = \esum_(k in K) \esum_(j in J k) a j.
Proof.
move=> Jtriv a_ge0.
pose J' i := if a @` J i == [set 0] then set0 else J i.
pose a' x := if x \in \bigcup_(k in K) J k then a x else 0.
have a'E k x : K k -> J k x -> a' x = a x.
  move=> Kk Jkx; rewrite /a'; case: ifPn; rewrite ?(inE, notin_set)//=.
  by case; exists k.
have a'_ge0 x : a' x >= 0 by rewrite /a'; case: ifPn; rewrite // ?inE => /a_ge0.
transitivity (\esum_(i in \bigcup_(k in K) J' k) a' i).
  rewrite esum_mkcond [RHS]esum_mkcond /a'; apply: eq_esum => x _.
  do 2!case: ifPn; rewrite ?(inE, notin_set)//= => J'x Jx.
  apply: contra_not_eq J'x => Nax.
  move: Jx => [k kK Jkx]; exists k=> //; rewrite /J'/=; case: ifPn=> //=.
  move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[+ _].
  by apply: contra_neq_not Nax; apply; exists x.
rewrite esum_bigcupT//; last first.
  move=> i j _ _ [x []]; rewrite /J'/=.
  case: eqVneq => //= Ai0 Jix; case: eqVneq => //= Aj0 Jjx.
  by have := Jtriv i j Ai0 Aj0; apply; exists x.
apply: eq_esum => i Ki.
rewrite esum_mkcond [RHS]esum_mkcond; apply: eq_esum => x _.
do 2!case: ifPn; rewrite ?(inE, notin_set)//=.
- by move=> /a'E->//.
- by rewrite /J'; case: ifPn => //.
move=> Jix; rewrite /J'; case: ifPn=> //=.
by move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[->]//; exists x.
Qed.

End esum_bigcup.

Arguments esum_bigcupT {R T K} J a.
Arguments esum_bigcup {R T K} J a.
