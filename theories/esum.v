(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
Require Import boolp reals mathcomp_extra ereal classical_sets posnum topology.
Require Import sequences functions numfun cardinality.

(******************************************************************************)
(*                      Summation over classical sets                         *)
(*                                                                            *)
(* This file provides a definition of sum over classical sets and a few       *)
(* lemmas in particular for the case of sums of non-negative terms.           *)
(*                                                                            *)
(*              fsets S == the set of finite sets (fset) included in S        *)
(* \nnesum_(i in I) f i == summation of non-negative extended real numbers    *)
(*                         over classical sets; I is a classical set and f is *)
(*                         a function whose codomain is included in the       *)
(*                         extended reals; it is 0 if I = set0 and            *)
(*                         sup(\sum_A a) where A is a finite set included in  *)
(*                         I o.w                                              *)
(*   \esum_(i in I) f i := \nnesum_(i in I) f^\+ i - \nnesum_(i in I) f^\- i  *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\nnesum_ ( i 'in' P ) F"
  (at level 41, F at level 41, format "\nnesum_ ( i  'in'  P )  F").
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

Section nnesum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition nnesum S a := ereal_sup [set \sum_(x <- A) a x | A in fsets S].

Local Notation "\nnesum_ ( i 'in' P ) A" := (nnesum P (fun i => A)).

Lemma nnesum_set0 a : \nnesum_(i in set0) a i = 0.
Proof.
rewrite /nnesum fsets0 [X in ereal_sup X](_ : _ = [set 0%E]) ?ereal_sup1//.
rewrite predeqE => x; split; first by move=> [_ /= ->]; rewrite big_seq_fset0.
by move=> -> /=; exists fset0 => //; rewrite big_seq_fset0.
Qed.

End nnesum.

Notation "\nnesum_ ( i 'in' P ) F" := (nnesum P (fun i => F)) : ring_scope.

Section nnesum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> \bar R).

Lemma nnesum_ge0 (S : set T) a : (forall x, S x -> 0 <= a x) -> 0 <= \nnesum_(i in S) a i.
Proof.
move=> a0.
by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
Qed.

Lemma nnesum_fset (F : {fset T}) a : (forall i, i \in F -> 0 <= a i) ->
  \nnesum_(i in [set` F]) a i = \sum_(i <- F) a i.
Proof.
move=> f0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' F'F <-]; apply/lee_sum_nneg_subfset.
  exact/fsetsP.
by move=> t; rewrite inE => /andP[_ /f0].
Qed.

Lemma sum_fset_set (A : set T) a : finite_set A ->
  (forall i, A i -> 0 <= a i) ->
  \sum_(i <- fset_set A) a i = \nnesum_(i in A) a i.
Proof.
move=> Afin a0; rewrite -nnesum_fset => [|i]; rewrite ?fset_setK//.
by rewrite in_fset_set ?inE//; apply: a0.
Qed.

End nnesum_realType.

Lemma nnesum_ge [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) x :
  (exists2 X : {fset T}, fsets I X & x <= \sum_(i <- X) a i) ->
  x <= \nnesum_(i in I) a i.
Proof. by move=> [X IX /le_trans->//]; apply: ereal_sup_ub => /=; exists X. Qed.

Lemma nnesum0 [R : realFieldType] [I : choiceType] (D : set I) (a : I -> \bar R) :
  (forall i, D i -> a i = 0) -> \nnesum_(i in D) a i = 0.
Proof.
move=> a0; rewrite /nnesum (_ : [set _ | _ in _] = [set 0]) ?ereal_sup1//.
apply/seteqP; split=> x //= => [[X XI] <-|->].
  by rewrite big_seq_cond big1// => i /andP[Xi _]; rewrite a0//; apply: XI.
by exists fset0; rewrite ?big_seq_fset0.
Qed.

Lemma le_nnesum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i <= b i) ->
  \nnesum_(i in I) a i <= \nnesum_(i in I) b i.
Proof.
move=> le_ab; rewrite ub_ereal_sup => //= _ [X XI] <-; rewrite nnesum_ge//.
exists X => //; rewrite big_seq_cond [x in _ <= x]big_seq_cond lee_sum => // i.
by rewrite andbT => /XI /le_ab.
Qed.

Lemma eq_nnesum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i = b i) ->
  \nnesum_(i in I) a i = \nnesum_(i in I) b i.
Proof. by move=> e; apply/eqP; rewrite eq_le !le_nnesum// => i Ii; rewrite e. Qed.

Section esum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition esum S a := nnesum S a^\+ - nnesum S a^\-.

Lemma esumE S a : esum S a = nnesum S a^\+ - nnesum S a^\-. Proof. by []. Qed.

End esum.

Notation "\esum_ ( i 'in' P ) F" := (esum P (fun i => F)) : ring_scope.

(* TODO: move *)
Lemma oppeB (R : numDomainType) (x y : \bar R) : y \is a fin_num -> - (x - y) = - x + y.
Proof. by move=> yfin; rewrite oppeD ?oppeK// fin_numN. Qed.

Lemma fin_numElt' (R : realDomainType) (x : \bar R) :
  (x \is a fin_num) = (`| x | != +oo).
Proof. by rewrite fin_numElt -(lte_absl _ +oo) lt_neqAle lee_pinfty andbT. Qed.
(* /TODO: move *)

Section esum_lemmas.
Variables (R : realType) (T : choiceType).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma ge0_esumE D f : (forall x, D x -> 0 <= f x) ->
  \esum_(x in D) f x = \nnesum_(x in D) f x.
Proof.
move=> Sa; rewrite /esum [X in _ - X](_ : _ = 0) ?sube0; last first.
  by rewrite nnesum0// => x Sx; rewrite -[LHS]/(f^\- x) (ge0_funennpE Sa)// inE.
by apply: eq_nnesum => t St; rewrite -[LHS]/(f^\+ t) (ge0_funenngE Sa)// inE.
Qed.

Lemma esum_fset (F : {fset T}) f : (forall i, i \in F -> 0 <= f i) ->
  \esum_(i in [set` F]) f i = \sum_(i <- F) f i.
Proof. by move=> f0; rewrite ge0_esumE// nnesum_fset. Qed.

Lemma esum_ge0 (S : set T) f : (forall x, S x -> 0 <= f x) -> 0 <= \esum_(i in S) f i.
Proof. by move=> g0; rewrite ge0_esumE// nnesum_ge0. Qed.

Lemma eq_esum (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i = b i) -> \esum_(i in I) a i = \esum_(i in I) b i.
Proof.
by move=> ab; rewrite !esumE; congr (_ - _); apply eq_nnesum => t It/=;
  rewrite /funenng /funennp ab.
Qed.

End esum_lemmas.

Lemma nnesumD [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> 0 <= a i) -> (forall i, I i -> 0 <= b i) ->
  \nnesum_(i in I) (a i + b i) = \nnesum_(i in I) a i + \nnesum_(i in I) b i.
Proof.
move=> ag0 bg0; apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ub_ereal_sup//= => x [X XI] <-; rewrite big_split/=.
  by rewrite lee_add// ereal_sup_ub//=; exists X.
wlog : a b ag0 bg0 / \nnesum_(i in I) a i \isn't a fin_num => [saoo|]; last first.
  move=> /fin_numPn[->|/[dup] aoo ->]; first by rewrite /adde/= lee_ninfty.
  rewrite (@le_trans _ _ +oo)//; first by rewrite /adde/=; case: nnesum.
  rewrite lee_pinfty_eq; apply/eqP/eq_infty => y; rewrite nnesum_ge//.
  have : y%:E < \nnesum_(i in I) a i by rewrite aoo// lte_pinfty.
  move=> /ereal_sup_gt[_ [X XI] <-] /ltW yle; exists X => //=.
  rewrite (le_trans yle)// big_split lee_addl// big_seq_cond sume_ge0 => // i.
  by rewrite andbT => /XI; apply: bg0.
  case: (boolP (\nnesum_(i in I) a i \is a fin_num)) => sa; last exact: saoo.
case: (boolP (\nnesum_(i in I) b i \is a fin_num)) => sb; last first.
  by rewrite addeC (eq_nnesum (fun _ _ => addeC _ _)) saoo.
rewrite -lee_subr_addr// ub_ereal_sup//= => _ [X XI] <-.
have saX : \sum_(i <- X) a i \is a fin_num.
  apply: contraTT sa => /fin_numPn[] sa.
    suff : \sum_(i <- X) a i >= 0 by rewrite sa.
    by rewrite big_seq_cond sume_ge0 => // i; rewrite ?andbT => /XI/ag0.
  apply/fin_numPn; right; apply/eqP; rewrite -lee_pinfty_eq nnesum_ge//.
  by exists X; rewrite // sa.
rewrite lee_subr_addr// addeC -lee_subr_addr// ub_ereal_sup//= => _ [Y YI] <-.
rewrite lee_subr_addr// addeC nnesum_ge//; exists (X `|` Y)%fset.
  by move=> i/=; rewrite inE => /orP[/XI|/YI].
rewrite big_split/= lee_add//=.
  rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUl.
  by move=> x; rewrite !inE/= => /andP[/negPf->]/= => /YI/ag0.
rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUr.
by move=> x; rewrite !inE/= => /andP[/negPf->]/orP[]// => /XI/bg0.
Qed.

Lemma nnesum_mkcond [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) :
  \nnesum_(i in I) a i = \nnesum_(i in [set: T]) if i \in I then a i else 0.
Proof.
apply/eqP; rewrite eq_le !ub_ereal_sup//= => _ [X XI] <-; rewrite -?big_mkcond//=.
  rewrite big_fset_condE/=; set Y := [fset _ | _ in X & _]%fset.
  rewrite ereal_sup_ub//; exists Y => //= i /=.
  by rewrite 2!inE/= => /andP[_]; rewrite inE.
rewrite ereal_sup_ub//; exists X => //; rewrite -big_mkcond/=.
rewrite big_seq_cond [RHS]big_seq_cond; apply: eq_bigl => i.
by case: (boolP (i \in X)) => //= /XI Ii; apply/mem_set.
Qed.

Lemma esum_mkcond [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) :
  \esum_(i in I) a i = \esum_(i in [set: T]) if i \in I then a i else 0.
Proof.
rewrite !esumE; congr (_ - _).
  rewrite nnesum_mkcond// /funenng; apply eq_nnesum => t _ /=.
  by case: ifPn => //; rewrite maxxx.
rewrite nnesum_mkcond// /funennp; apply eq_nnesum => t _ /=.
by case: ifPn => //; rewrite oppe0 maxxx.
Qed.

Lemma nnesum_mkcondr [R : realType] [T : choiceType] (I J : set T) (a : T -> \bar R) :
  \nnesum_(i in I `&` J) a i = \nnesum_(i in I) if i \in J then a i else 0.
Proof.
rewrite nnesum_mkcond [RHS]nnesum_mkcond; apply: eq_nnesum=> i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma nnesum_mkcondl [R : realType] [T : choiceType] (I J : set T) (a : T -> \bar R) :
  \nnesum_(i in I `&` J) a i = \nnesum_(i in J) if i \in I then a i else 0.
Proof.
rewrite nnesum_mkcond [RHS]nnesum_mkcond; apply: eq_nnesum=> i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma nnesumID (R : realType) (I : choiceType) (B : set I) (A : set I)
  (F : I -> \bar R) :
  (forall i, A i -> F i >= 0) ->
  \nnesum_(i in A) F i = (\nnesum_(i in A `&` B) F i) +
                        (\nnesum_(i in A `&` ~` B) F i).
Proof.
move=> F0; rewrite !nnesum_mkcondr -nnesumD; do ?by move=> i /F0; case: ifP.
by apply: eq_nnesum=> i; rewrite in_setC; case: ifP; rewrite /= (adde0, add0e).
Qed.
Arguments nnesumID {R I}.

Lemma nnesum_sum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (r : seq T2) (P : pred T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, I i -> P j -> 0 <= a i j) ->
  \nnesum_(i in I) \sum_(j <- r | P j) a i j =
  \sum_(j <- r | P j) \nnesum_(i in I) a i j.
Proof.
move=> a_ge0; elim: r => [|j r IHr]; rewrite ?(big_nil, big_cons)// -?IHr.
  by rewrite nnesum0// => i; rewrite big_nil.
case: (boolP (P j)) => Pj; last first.
  by apply: eq_nnesum => i Ii; rewrite big_cons (negPf Pj).
have aj_ge0 i : I i -> a i j >= 0 by move=> ?; apply: a_ge0.
rewrite -nnesumD//; last by move=> i Ii; apply: sume_ge0 => *; apply: a_ge0.
by apply: eq_nnesum => i Ii; rewrite big_cons Pj.
Qed.

Lemma nnesum_nnesum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (J : T1 -> set T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, 0 <= a i j) ->
  \nnesum_(i in I) \nnesum_(j in J i) a i j = \nnesum_(k in I `*`` J) a k.1 k.2.
Proof.
move=> a_ge0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ub_ereal_sup => /= _ [X IX] <-.
  under eq_bigr do rewrite nnesum_mkcond.
  rewrite -nnesum_sum; last by move=> i j _ _; case: ifP.
  under eq_nnesum do rewrite -big_mkcond/=.
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
apply: ub_ereal_sup => _ /= [X/= XIJ] <-; apply: nnesum_ge.
pose X1 := [fset x.1 | x in X]%fset.
pose X2 := [fset x.2 | x in X]%fset.
exists X1; first by move=> x/= /imfsetP[z /= zX ->]; have [] := XIJ z.
apply: (@le_trans _ _ (\sum_(i <- X1) \sum_(j <- X2 | j \in J i) a i j)).
  rewrite pair_big_dep_cond//=; set Y := Imfset.imfset2 _ _ _ _.
  rewrite [X in _ <= X](big_fsetID _ (mem X))/=.
  rewrite (_ : [fset x | x in Y & x \in X] = Y `&` X)%fset; last first.
     by apply/fsetP => x; rewrite 2!inE.
  rewrite (fsetIidPr _); first by rewrite lee_addl// sume_ge0.
  apply/fsubsetP => -[i j] Xij; apply/imfset2P.
    exists i => //=; rewrite ?inE ?andbT//=.
    by apply/imfsetP; exists (i, j).
  exists j => //; rewrite !inE/=; have /XIJ[/= _ Jij] := Xij.
  by apply/andP; split; rewrite ?inE//; apply/imfsetP; exists (i, j).
rewrite big_mkcond [X in _ <= X]big_mkcond.
apply: lee_sum => i Xi; rewrite ereal_sup_ub => //=.
exists [fset j in X2 | j \in J i]%fset; last by rewrite -big_fset_condE.
by move=> j/=; rewrite !inE => /andP[_]; rewrite inE.
Qed.

Lemma esum_esum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (J : T1 -> set T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, 0 <= a i j) ->
  \esum_(i in I) \esum_(j in J i) a i j = \esum_(k in I `*`` J) a k.1 k.2.
Proof.
move=> a0; rewrite [RHS]ge0_esumE // -nnesum_nnesum//.
rewrite ge0_esumE; last by move=> x Ix; rewrite ge0_esumE//; exact: nnesum_ge0.
by apply eq_nnesum => x Ix; rewrite ge0_esumE.
Qed.

Lemma lee_sum_fset_nat (R : realDomainType)
    (f : (\bar R)^nat) (F : {fset nat}) n (P : pred nat) :
    (forall i, P i -> 0%E <= f i) ->
    [set` F] `<=` `I_n ->
  \sum_(i <- F | P i) f i <= \sum_(0 <= i < n | P i) f i.
Proof.
move=> f0 Fn; rewrite [X in _ <= X](bigID (mem F))/=.
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

Lemma ereal_pseries_nnesum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \nnesum_(i in [set x | P x]) a i.
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

Lemma ereal_pseries_esum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \esum_(i in [set x | P x]) a i.
Proof. by move=> a0; rewrite ge0_esumE// ereal_pseries_nnesum. Qed.

Lemma reindex_nnesum (R : realType) (T T' : choiceType)
    (P : set T) (Q : set T') (e : T -> T') (a : T' -> \bar R) :
    set_bij P Q e ->
    (forall i, P i -> 0 <= a (e i)) ->
  \nnesum_(j in Q) a j = \nnesum_(i in P) a (e i).
Proof.
elim/choicePpointed: T => T in e P *.
  rewrite !emptyE => /Pbij[{}e ->] _.
  by rewrite -[in LHS](image_eq e) image_set0 !nnesum_set0.
elim/choicePpointed: T' => T' in a e Q *; first by have := no (e point).
move=> /(@pPbij _ _ _)[{}e ->] a_ge0.
gen have le_nnesum : T T' a P Q e a_ge0 /
    \nnesum_(j in Q) a j <= \nnesum_(i in P) a (e i); last first.
  apply/eqP; rewrite eq_le le_nnesum//=.
  rewrite [X in _ <= X](_ : _ = \nnesum_(j in Q) a (e (e^-1%FUN j))); last first.
    by apply: eq_nnesum => i Qi; rewrite invK ?inE.
  by rewrite le_nnesum => //= i Qi; rewrite a_ge0//; apply: funS.
rewrite ub_ereal_sup => //= _ [X XQ <-]; rewrite ereal_sup_ub => //=.
exists (e^-1 @` X)%fset; first by move=> _ /imfsetP[t' /= /XQ Qt' ->]; apply: funS.
rewrite big_imfset => //=; last first.
  by move=> x y /XQ Qx /XQ Qy /(congr1 e); rewrite !invK ?inE.
by apply: eq_big_seq => i /XQ Qi; rewrite invK ?inE.
Qed.
Arguments reindex_nnesum {R T T'} P Q e a.

Lemma reindex_esum (R : realType) (T T' : choiceType)
    (P : set T) (Q : set T') (e : T -> T') (a : T' -> \bar R) :
    set_bij P Q e ->
    (forall i, P i -> 0 <= a (e i)) ->
  \esum_(j in Q) a j = \esum_(i in P) a (e i).
Proof.
move=> PQe a0; rewrite ge0_esumE//; last first.
  by move=> y Qy; case: PQe => _ _ /(_ _ Qy) /= [x Px <-]; exact: a0.
by rewrite (reindex_nnesum P Q e)// ge0_esumE.
Qed.
Arguments reindex_esum {R T T'} P Q e a.

Lemma nnesum_image (R : realType) (T T' : choiceType)
    (P : set T) (e : T -> T') (a : T' -> \bar R) :
    set_inj P e -> (forall i, P i -> 0 <= a (e i)) ->
  \nnesum_(j in e @` P) a j = \nnesum_(i in P) a (e i).
Proof. by move=> /inj_bij; apply: reindex_nnesum. Qed.
Arguments nnesum_image {R T T'} P e a.

Lemma nnesum_pred_image (R : realType) (T : choiceType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) :
    (forall n, P n -> 0 <= a (e n)) ->
    set_inj P e ->
  \nnesum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof. by move=> a0 einj; rewrite nnesum_image// ereal_pseries_nnesum. Qed.
Arguments nnesum_pred_image {R T} a e P.

Lemma esum_pred_image (R : realType) (T : choiceType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) :
    (forall n, P n -> 0 <= a (e n)) ->
    set_inj P e ->
  \esum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof.
by move=> a0 Pe; rewrite -nnesum_pred_image// ge0_esumE// => _ [n Pn] <-; exact/a0.
Qed.
Arguments esum_pred_image {R T} a e P.

Lemma nnesum_set_image  [R : realType] [T : choiceType] [a : T -> \bar R]
    [e : nat -> T] [P : set nat] :
    (forall n : nat, P n -> 0 <= a (e n)) ->
  set_inj P e ->
  \nnesum_(i in [set e x | x in P]) a i = \sum_(i <oo | i \in P) a (e i).
Proof.
move=> a0 einj; rewrite nnesum_image// ereal_pseries_nnesum ?set_mem_set//.
by move=> n; rewrite inE => /a0.
Qed.
Arguments nnesum_set_image {R T} a e P.

Lemma esum_set_image  [R : realType] [T : choiceType] [a : T -> \bar R]
    [e : nat -> T] [P : set nat] :
    (forall n : nat, P n -> 0 <= a (e n)) ->
  set_inj P e ->
  \esum_(i in [set e x | x in P]) a i = \sum_(i <oo | i \in P) a (e i).
Proof.
move=> a0 Pe.
by rewrite -nnesum_set_image// ge0_esumE// => x [n Pn <-]; exact: a0.
Qed.
Arguments esum_set_image {R T} a e P.

Section nnesum_bigcup.
Variables (R : realType) (T : choiceType) (K : set nat).
Implicit Types (J : nat -> set T) (a : T -> \bar R).

Lemma nnesum_bigcupT J a : trivIset setT J -> (forall x, 0 <= a x) ->
  \nnesum_(i in \bigcup_(k in K) (J k)) a i =
  \nnesum_(i in K) \nnesum_(j in J i) a j.
Proof.
move=> tJ a0; rewrite nnesum_nnesum//; apply: reindex_nnesum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2]; rewrite ?inE/=.
  move=> [K1 J1] [K2 J2] j12; congr (_, _) => //.
  by apply: (@tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

Lemma nnesum_bigcup J a : trivIset [set i | a @` J i != [set 0]] J ->
    (forall x : T, (\bigcup_(k in K) J k) x -> 0 <= a x) ->
  \nnesum_(i in \bigcup_(k in K) J k) a i = \nnesum_(k in K) \nnesum_(j in J k) a j.
Proof.
move=> Jtriv a_ge0.
pose J' i := if a @` J i == [set 0] then set0 else J i.
pose a' x := if x \in \bigcup_(k in K) J k then a x else 0.
have a'E k x : K k -> J k x -> a' x = a x.
  move=> Kk Jkx; rewrite /a'; case: ifPn; rewrite ?(inE, notin_set)//=.
  by case; exists k.
have a'_ge0 x : a' x >= 0 by rewrite /a'; case: ifPn; rewrite // ?inE => /a_ge0.
transitivity (\nnesum_(i in \bigcup_(k in K) J' k) a' i).
  rewrite nnesum_mkcond [RHS]nnesum_mkcond /a'; apply: eq_nnesum => x _.
  do 2!case: ifPn; rewrite ?(inE, notin_set)//= => J'x Jx.
  apply: contra_not_eq J'x => Nax.
  move: Jx => [k kK Jkx]; exists k=> //; rewrite /J'/=; case: ifPn=> //=.
  move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[+ _].
  by apply: contra_neq_not Nax; apply; exists x.
rewrite nnesum_bigcupT//; last first.
  move=> i j _ _ [x []]; rewrite /J'/=.
  case: eqVneq => //= Ai0 Jix; case: eqVneq => //= Aj0 Jjx.
  by have := Jtriv i j Ai0 Aj0; apply; exists x.
apply: eq_nnesum => i Ki.
rewrite nnesum_mkcond [RHS]nnesum_mkcond; apply: eq_nnesum => x _.
do 2!case: ifPn; rewrite ?(inE, notin_set)//=.
- by move=> /a'E->//.
- by rewrite /J'; case: ifPn => //.
move=> Jix; rewrite /J'; case: ifPn=> //=.
by move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[->]//; exists x.
Qed.

Lemma esum_bigcupT J a : trivIset setT J -> (forall x, 0 <= a x) ->
  \esum_(i in \bigcup_(k in K) (J k)) a i =
  \esum_(i in K) \esum_(j in J i) a j.
Proof.
move=> tJ a0; rewrite ge0_esumE; last by move=> t _; exact: a0.
rewrite nnesum_bigcupT// ge0_esumE; last by move=> n Kx; rewrite esum_ge0.
by apply eq_nnesum => n Kn; rewrite ge0_esumE.
Qed.

Lemma esum_bigcup J a : trivIset [set i | a @` J i != [set 0]] J ->
    (forall x : T, (\bigcup_(k in K) J k) x -> 0 <= a x) ->
  \esum_(i in \bigcup_(k in K) J k) a i = \esum_(k in K) \esum_(j in J k) a j.
Proof.
move=> tJ a0; rewrite ge0_esumE// nnesum_bigcup// ge0_esumE; last first.
  move=> x Kx; rewrite ge0_esumE//; last first.
    by move=> t Jxt; apply: a0; exists x.
  by apply: nnesum_ge0 => t Jxt; apply: a0; exists x.
by apply eq_nnesum => /= n Kn; rewrite ge0_esumE// => x Jnx; apply: a0; exists n.
Qed.

End nnesum_bigcup.
Arguments nnesum_bigcupT {R T K} J a.
Arguments esum_bigcupT {R T K} J a.
Arguments esum_bigcup {R T K} J a.

Lemma nnesum_set1 [R : realType] [T : choiceType] (t : T) (a : T -> \bar R) :
  (forall t, 0 <= a t)%E ->
  \nnesum_(i in [set t]) a i = a t.
Proof.
move=> a0; rewrite (_ : [set t] = [set` [fset t]%fset])//; last first.
  by apply/seteqP; split=> [x <-|x]; rewrite /= ?inE// => /eqP.
by rewrite nnesum_fset// big_seq_fset1.
Qed.

Section esummable.
Variables (R : realType) (T : choiceType).
Implicit Types (D : set T) (f g : T -> \bar R).

Definition esummable D f := \esum_(x in D) `| f x | < +oo.

Lemma esummableE D f : esummable D f = (\esum_(x in D) `| f x | \is a fin_num).
Proof.
rewrite /esummable fin_numElt; apply/idP/idP => [->|/andP[]//].
by rewrite andbT (lt_le_trans (lte_ninfty 0))// ge0_esumE// nnesum_ge0.
Qed.

Lemma esummable_funenng D f : esummable D f -> esummable D f^\+.
Proof.
apply: le_lt_trans; rewrite !ge0_esumE//; apply le_nnesum => t Dt.
by rewrite -/((abse \o f) t) fune_abse gee0_abs// lee_addl.
Qed.

Lemma esummable_funennp D f : esummable D f -> esummable D f^\-.
Proof.
apply: le_lt_trans; rewrite !ge0_esumE//; apply le_nnesum => t Dt.
by rewrite -/((abse \o f) t) fune_abse gee0_abs// lee_addr.
Qed.

Lemma esummableD D f g : esummable D f -> esummable D g -> esummable D (f \+ g).
Proof.
move=> Df Dg; apply: le_lt_trans (lte_add_pinfty Df Dg).
rewrite ![in X in _ <= X]ge0_esumE// -nnesumD// ge0_esumE//.
by apply le_nnesum => t Dt; apply: lee_abs_add.
Qed.

Lemma esummableN D f : esummable D f = esummable D (\- f).
Proof.
by rewrite /esummable; congr (_ < +oo); apply: eq_esum => t Dt; rewrite abseN.
Qed.

Lemma esummableB D f g : esummable D f -> esummable D g -> esummable D (f \- g).
Proof. by move=> Df; rewrite esummableN; apply: esummableD. Qed.

Lemma esummable_pinfty D f : esummable D f ->
  forall x, D x -> `| f x | != +oo.
Proof.
move=> Dfoo x Dx; rewrite -lee_pinfty_eq -ltNge.
apply: le_lt_trans Dfoo.
rewrite ge0_esumE// (nnesumID [set x])// setI1 mem_set// nnesum_set1// lee_addl//.
by rewrite nnesum_ge0.
Qed.

Lemma esummableP D f : esummable D f <->
  \esum_(x in D) f^\+ x < +oo /\ \esum_(x in D) f^\- x < +oo.
Proof.
split=> [Df|[Dfp Dfm]].
  by split; apply: le_lt_trans Df; rewrite ge0_esumE// ge0_esumE//;
    apply: le_nnesum => t Dt; rewrite -[X in _ <= X]/((abse \o f) t) fune_abse
    ?lee_addl ?lee_addr.
apply: le_lt_trans (lte_add_pinfty Dfp Dfm).
rewrite [in X in _ <= X]ge0_esumE// [in X in _ <= X]ge0_esumE//.
rewrite -nnesumD// ge0_esumE//; apply: le_nnesum => // t Dt.
by rewrite -[X in X <= _]/((abse \o f) t) fune_abse.
Qed.

End esummable.

Section esum_arith.
Variables (R : realType) (T : choiceType).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma esumB D f g : esummable D f -> esummable D g ->
  (forall i, D i -> 0 <= f i) -> (forall i, D i -> 0 <= g i) ->
  \esum_(i in D) (f i - g i) = \esum_(i in D) f i - \esum_(i in D) g i.
Proof.
move=> Df Dg f0 g0.
have /eqP : \esum_(i in D) (f \- g)^\+ i + \esum_(i in D) g i =
    \esum_(i in D) (f \- g)^\- i + \esum_(i in D) f i.
  rewrite !ge0_esumE// -!nnesumD//; apply eq_nnesum => i Di.
  rewrite /funenng /funennp.
  have [fg|fg] := leP 0 (f i - g i).
    rewrite max_r 1?lee_oppl ?oppe0// add0e subeK//.
    by rewrite fin_numElt' (esummable_pinfty Dg).
  rewrite add0e max_l; last by rewrite lee_oppr oppe0 ltW.
  rewrite oppeB//; last by rewrite fin_numElt' (esummable_pinfty Dg).
  by rewrite -addeA addeCA addeA subeK// fin_numElt' (esummable_pinfty Df).
rewrite [X in _ == X -> _]addeC -sube_eq; last 2 first.
  - rewrite fin_numD; apply/andP; split; last first.
      by move: Dg; rewrite esummableE (@eq_esum _ _ _ _ g)// => t Tt; rewrite gee0_abs// g0.
    rewrite (@eq_esum _ _ _ _ (abse \o (f \- g)^\+))//.
      by rewrite -esummableE; apply/esummable_funenng/esummableB.
    by move=> t Dt; rewrite /= gee0_abs.
  - rewrite adde_defC fin_num_adde_def//.
    by rewrite (@eq_esum _ _ _ _ (abse \o f))// -?esummableE// => i Di; rewrite /= gee0_abs// f0.
rewrite -addeA addeCA.
rewrite eq_sym [X in _ == X -> _]addeC -sube_eq; last 2 first.
  - by rewrite (@eq_esum _ _ _ _ (abse \o f))// -?esummableE// => i Di; rewrite /= gee0_abs// f0.
  - rewrite fin_num_adde_def//.
    by rewrite (@eq_esum _ _ _ _ (abse \o g))// -?esummableE// => i Di; rewrite /= gee0_abs// g0.
by move=> /eqP ->; rewrite esumE !ge0_esumE.
Qed.

End esum_arith.
