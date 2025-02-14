(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals ereal itv.
From mathcomp Require Import topology sequences normedtype numfun.

(**md**************************************************************************)
(* # Summation over classical sets                                            *)
(*                                                                            *)
(* This file provides a definition of sum over classical sets and a few       *)
(* lemmas in particular for the case of sums of non-negative terms.           *)
(*                                                                            *)
(* ```                                                                        *)
(*            fsets S == the set of finite sets (fset) included in S          *)
(* \esum_(i in I) f i == summation of non-negative extended real numbers over *)
(*                       classical sets; I is a classical set and f is a      *)
(*                       function whose codomain is included in the extended  *)
(*                       reals; it is 0 if I = set0 and sup(\sum_A a) where A *)
(*                       is a finite set included in I o.w.                   *)
(*       summable D f := \esum_(x in D) `| f x | < +oo                        *)
(* ```                                                                        *)
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

Definition fsets S : set (set T) := [set F | finite_set F /\ F `<=` S].

Lemma fsets_set0 S : fsets S set0. Proof. by split. Qed.

Lemma fsets_self (F : set T) : finite_set F -> fsets F F.
Proof. by move=> finF; split. Qed.

Lemma fsets0 : fsets set0 = [set set0].
Proof.
rewrite predeqE => A; split => [|->]; last exact: fsets_set0.
by rewrite /fsets/= subset0 => -[].
Qed.

End set_of_fset_in_a_set.

Section esum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition esum S a := ereal_sup [set \sum_(x \in A) a x | A in fsets S].

Local Notation "\esum_ ( i 'in' P ) A" := (esum P (fun i => A)).

Lemma esum_set0 a : \esum_(i in set0) a i = 0.
Proof.
rewrite /esum fsets0 [X in ereal_sup X](_ : _ = [set 0%E]) ?ereal_sup1//.
apply/seteqP; split=> [x [_ /= ->]|x]; first by rewrite fsbig_set0.
by move=> -> /=; exists set0 => //; rewrite fsbig_set0.
Qed.

End esum.

Notation "\esum_ ( i 'in' P ) F" := (esum P (fun i => F)) : ring_scope.

Section esum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> \bar R).

Lemma esum_ge0 (S : set T) a :
  (forall x, S x -> 0 <= a x) -> 0 <= \esum_(i in S) a i.
Proof.
move=> a0; apply: ereal_sup_ubound.
by exists set0; [exact: fsets_set0|rewrite fsbig_set0].
Qed.

Lemma esum_fset (F : set T) a : finite_set F ->
    (forall i, i \in F -> 0 <= a i) ->
  \esum_(i in F) a i = \sum_(i \in F) a i.
Proof.
move=> finF f0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: ereal_sup_ubound; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' [finF' F'F] <-].
apply/lee_fsum_nneg_subset => //; first exact/subsetP.
by  move=> t; rewrite inE/= => /andP[_] /f0.
Qed.

Lemma esum_set1 t a : 0 <= a t -> \esum_(i in [set t]) a i = a t.
Proof.
by move=> ?; rewrite esum_fset// ?fset_set1// ?fsbig_set1// => t' /[!inE] ->.
Qed.

End esum_realType.

Lemma esum1 [R : realFieldType] [I : choiceType] (D : set I) (a : I -> \bar R) :
  (forall i, D i -> a i = 0) -> \esum_(i in D) a i = 0.
Proof.
move=> a0; rewrite /esum (_ : [set _ | _ in _] = [set 0]) ?ereal_sup1//.
apply/seteqP; split=> x //= => [[X [finX XI]] <-|->].
  by rewrite fsbig1// => i /XI/a0.
by exists set0; rewrite ?fsbig_set0//; exact: fsets_set0.
Qed.

Lemma esum_ge [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) x :
  (exists2 X : set T, fsets I X & x <= \sum_(i \in X) a i) ->
  x <= \esum_(i in I) a i.
Proof. by move=> [X IX /le_trans->//]; apply: ereal_sup_ubound; exists X. Qed.

Lemma le_esum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i <= b i) ->
  \esum_(i in I) a i <= \esum_(i in I) b i.
Proof.
move=> le_ab; rewrite ub_ereal_sup => //= _ [X [finX XI]] <-; rewrite esum_ge//.
by exists X => //; apply: lee_fsum => // t /XI /le_ab.
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
  rewrite ub_ereal_sup//= => x [X [finX XI]] <-; rewrite fsbig_split//=.
  by rewrite leeD// ereal_sup_ubound//=; exists X.
wlog : a b ag0 bg0 / \esum_(i in I) a i \isn't a fin_num => [saoo|]; last first.
  move=> /fin_numPn[->|/[dup] aoo ->]; first by rewrite leNye.
  rewrite (@le_trans _ _ +oo)//; first by rewrite /adde/=; case: esum.
  rewrite leye_eq; apply/eqP/eq_infty => y; rewrite esum_ge//.
  have : y%:E < \esum_(i in I) a i by rewrite aoo// ltry.
  move=> /ereal_sup_gt[_ [X [finX XI]] <-] /ltW yle; exists X => //=.
  rewrite (le_trans yle)// fsbig_split// leeDl// fsume_ge0// => // i.
  by move=> /XI; exact: bg0.
case: (boolP (\esum_(i in I) a i \is a fin_num)) => sa; last exact: saoo.
case: (boolP (\esum_(i in I) b i \is a fin_num)) => sb; last first.
  by rewrite addeC (eq_esum (fun _ _ => addeC _ _)) saoo.
rewrite -leeBrDr// ub_ereal_sup//= => _ [X [finX XI]] <-.
have saX : \sum_(i \in X) a i \is a fin_num.
  apply: contraTT sa => /fin_numPn[] sa.
    suff : \sum_(i \in X) a i >= 0 by rewrite sa.
    by rewrite fsume_ge0// => i /XI/ag0.
  apply/fin_numPn; right; apply/eqP; rewrite -leye_eq esum_ge//.
  by exists X; rewrite // sa.
rewrite leeBrDr// addeC -leeBrDr// ub_ereal_sup//= => _ [Y [finY YI]] <-.
rewrite leeBrDr// addeC esum_ge//; exists (X `|` Y).
  by split; [rewrite finite_setU|rewrite subUset].
rewrite fsbig_split ?finite_setU//= leeD// lee_fsum_nneg_subset ?finite_setU//=.
- exact/subsetP/subsetUl.
- by move=> x; rewrite !inE in_setU andb_orr andNb => /andP[_] /[!inE] /YI/ag0.
- exact/subsetP/subsetUr.
- move=> x; rewrite !inE in_setU andb_orr andNb/= orbF.
  by move=> /andP[_] /[!inE] /XI/bg0.
Qed.

Lemma esum_mkcond [R : realType] [T : choiceType] (I : set T)
    (a : T -> \bar R) :
  \esum_(i in I) a i = \esum_(i in [set: T]) if i \in I then a i else 0.
Proof.
apply/eqP; rewrite eq_le !ub_ereal_sup//= => _ [X [finX XI]] <-.
  rewrite -big_mkcond/= big_fset_condE/=; set Y := [fset _ | _ in _ & _]%fset.
  rewrite ereal_sup_ubound//=; exists [set` Y].
    by split => // i/=; rewrite !inE/= => /andP[_]; rewrite inE.
  by rewrite fsbig_finite// set_fsetK.
rewrite ereal_sup_ubound//; exists X => //; apply: eq_fsbigr => x /[!inE] Xx.
by rewrite ifT// inE; exact: XI.
Qed.

Lemma esum_mkcondr [R : realType] [T : choiceType] (I J : set T)
    (a : T -> \bar R) :
  \esum_(i in I `&` J) a i = \esum_(i in I) if i \in J then a i else 0.
Proof.
rewrite esum_mkcond [RHS]esum_mkcond; apply: eq_esum=> i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma esum_mkcondl [R : realType] [T : choiceType] (I J : set T)
    (a : T -> \bar R) :
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
  by rewrite esum1// => i; rewrite big_nil.
case: ifPn => Pj; last first.
  by apply: eq_esum => i Ii; rewrite big_cons (negPf Pj).
have aj_ge0 i : I i -> a i j >= 0 by move=> ?; apply: a_ge0.
rewrite -esumD//; last by move=> i Ii; apply: sume_ge0 => *; apply: a_ge0.
by apply: eq_esum => i Ii; rewrite big_cons Pj.
Qed.

Lemma esum_esum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (J : T1 -> set T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, I i -> J i j -> 0 <= a i j) ->
  \esum_(i in I) \esum_(j in J i) a i j = \esum_(k in I `*`` J) a k.1 k.2.
Proof.
move=> a_ge0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ub_ereal_sup => /= _ [X [finX XI]] <-.
  under eq_fsbigr do rewrite esum_mkcond.
  rewrite fsbig_finite//= big_seq -esum_sum; last first.
    move=> i j _ /[!in_fset_set]// /[!inE] /XI Ij.
    by case: ifPn => // /[!inE] /a_ge0-/(_ Ij).
  under eq_esum do rewrite -big_seq -big_mkcond/=.
  apply: ub_ereal_sup => /= _ [Y [finY _] <-]; apply: ereal_sup_ubound => /=.
  set XYJ := [set z | z \in X `*` Y /\ z.2 \in J z.1].
  have ? : finite_set XYJ.
    apply: sub_finite_set (finite_setX finX finY) => z/=.
    by rewrite /XYJ/= in_setX => -[/andP[] /[!inE]].
  exists XYJ => /=; first by split => //= z; rewrite /XYJ/= 2!inE=> -[[/XI]].
  rewrite [in RHS]fsbig_finite//= (exchange_big_dep xpredT)// pair_big_dep_cond.
  rewrite fsbig_finite//; apply: eq_fbigl => -[/= x y]; rewrite in_fset_set//.
  apply/idP/imfset2P.
    rewrite /XYJ !inE/= !inE/= -andA => -[Xx [Yy Jxy]].
    exists x; first by rewrite !inE in_fset_set// mem_set.
    by exists y => //; rewrite !inE mem_set// in_fset_set// mem_set.
  move=> [t1]; rewrite !inE andbT/= in_fset_set// inE => Xt1.
  by move=> [t2]; rewrite !inE in_fset_set /XYJ//= =>/andP[/[!inE] ? ?] [-> ->].
apply: ub_ereal_sup => _ /= [X/= [finX XIJ]] <-; apply: esum_ge.
exists X.`1; first by split=> [|x [y /XIJ[]//]]; exact: finite_set_fst.
apply: (@le_trans _ _
    (\sum_(i <- fset_set X.`1) \sum_(j <- fset_set X.`2 | j \in J i) a i j)).
  rewrite pair_big_dep_cond//=; set Y := Imfset.imfset2 _ _ _ _.
  rewrite [leRHS](big_fsetID _ (mem X))/=.
  rewrite (_ : [fset x | x in Y & x \in X] = Y `&` fset_set X)%fset; last first.
    by apply/fsetP => x; rewrite 2!inE/= in_fset_set.
  rewrite (fsetIidPr _).
    rewrite fsbig_finite// leeDl// big_seq sume_ge0//=.
    move=> [x y] /imfsetP[[x1 y1]] /[!inE] /andP[] /imfset2P[x2]/= /[!inE].
    rewrite andbT in_fset_set; last exact: finite_set_fst.
    move=> /[!inE] x2X [y2] /[!inE] /andP[] /[!in_fset_set]; last first.
      exact: finite_set_snd.
    move=> /[!inE] y2X y2J [-> ->] _ [-> ->]; rewrite a_ge0//.
    by move: x2X => [y3 /XIJ []].
  apply/fsubsetP => -[i j]; rewrite in_fset_set// inE => Xij; apply/imfset2P.
  exists i => /=.
    rewrite !inE/= in_fset_set//; last exact: finite_set_fst.
    by rewrite andbT mem_set//; move/fst_set_fst : Xij.
  exists j => //; rewrite !inE/= in_fset_set; last exact: finite_set_snd.
  rewrite mem_set/=; last by move/snd_set_snd : Xij.
  by rewrite mem_set//; move/XIJ : Xij => [].
rewrite -fsbig_finite; last exact: finite_set_fst.
apply lee_fsum=> [|i Xi]; first exact: finite_set_fst.
rewrite ereal_sup_ubound //=; have ? : finite_set (X.`2 `&` J i).
  by apply: finite_setI; left; exact: finite_set_snd.
exists (X.`2 `&` J i) => //.
rewrite [in RHS]big_fset_condE/= fsbig_finite//; apply/eq_fbigl => j.
by rewrite in_fset_set// !inE/= in_setI in_fset_set//; exact: finite_set_snd.
Qed.

Lemma lee_sum_fset_nat (R : realDomainType)
    (f : (\bar R)^nat) (F : {fset nat}) n (P : pred nat) :
    (forall i, P i -> 0%E <= f i) ->
    [set` F] `<=` `I_n ->
  \sum_(i <- F | P i) f i <= \sum_(0 <= i < n | P i) f i.
Proof.
move=> f0 Fn; rewrite [leRHS](bigID (mem F))/=.
suff -> : \sum_(0 <= i < n | P i && (i \in F)) f i = \sum_(i <- F | P i) f i.
  by rewrite leeDl ?sume_ge0// => i /andP[/f0].
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
  by apply: nneseries_lim_ge => i _; exact: f0.
move=> k /= kF; rewrite /n big_seq_fsetE/=.
by rewrite -[k]/(val [`kF]%fset) ltnS leq_bigmax.
Qed.
Arguments lee_sum_fset_lim {R f} F P.

Lemma nneseries_esum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \esum_(i in [set x | P x]) a i.
Proof.
move=> a0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: (lime_le (is_cvg_nneseries_cond (fun n _ => a0 n))); apply: nearW => n.
  apply: ereal_sup_ubound; exists [set` [fset val i | i in 'I_n & P i]%fset].
    split; first exact: finite_fset.
    by move=> /= k /imfsetP[/= i]; rewrite inE => + ->.
  rewrite fsbig_finite//= set_fsetK big_imfset/=; last first.
    by move=> ? ? ? ? /val_inj.
  by rewrite big_filter big_enum_cond/= big_mkord.
apply: ub_ereal_sup => _ [/= F [finF PF] <-].
rewrite fsbig_finite//= -(big_rmcond_in P)/=; first exact: lee_sum_fset_lim.
by move=> k; rewrite in_fset_set// inE => /PF ->.
Qed.

Lemma reindex_esum (R : realType) (T T' : choiceType)
    (P : set T) (Q : set T') (e : T -> T') (a : T' -> \bar R) :
    set_bij P Q e ->
  \esum_(j in Q) a j = \esum_(i in P) a (e i).
Proof.
elim/choicePpointed: T => T in e P *.
  rewrite !emptyE => /Pbij[{}e ->].
  by rewrite -[in LHS](image_eq e) image_set0 !esum_set0.
elim/choicePpointed: T' => T' in a e Q *; first by have := no (e point).
move=> /(@pPbij _ _ _)[{}e ->].
gen have le_esum : T T' a P Q e /
    \esum_(j in Q) a j <= \esum_(i in P) a (e i); last first.
  apply/eqP; rewrite eq_le le_esum//=.
  rewrite [leRHS](_ : _ = \esum_(j in Q) a (e (e^-1%FUN j))); last first.
    by apply: eq_esum => i Qi; rewrite invK ?inE.
  by rewrite le_esum => //= i Qi; rewrite a_ge0//; exact: funS.
rewrite ub_ereal_sup => //= _ [X [finX XQ] <-]; rewrite ereal_sup_ubound => //=.
exists [set` (e^-1 @` (fset_set X))%fset].
  split=> [|t /= /imfsetP[t'/=]]; first exact: finite_fset.
  by rewrite in_fset_set// inE => /XQ Qt' ->; exact: funS.
rewrite fsbig_finite//= set_fsetK big_imfset => //=; last first.
  move=> x y; rewrite !in_fset_set// !inE => /XQ ? /XQ ? /(congr1 e).
  by rewrite !invK ?inE.
by rewrite -fsbig_finite//; apply: eq_fsbigr=> x /[!inE]/XQ ?; rewrite invK ?inE.
Qed.
Arguments reindex_esum {R T T'} P Q e a.

Section nneseries_interchange.
Local Open Scope ereal_scope.

Let nneseries_esum_prod (R : realType) (a : nat -> nat -> \bar R)
  (P Q : pred nat) : (forall i j, 0 <= a i j) ->
  \sum_(i <oo | P i) \sum_(j <oo | Q j) a i j =
  \esum_(i in P `*` Q) a i.1 i.2.
Proof.
move=> a0; rewrite -(@esum_esum _ _ _ P (fun=> Q))//.
rewrite nneseries_esum//; last by move=> n _; exact: nneseries_ge0.
rewrite (_ : [set x | P x] = P); last by apply/seteqP; split.
by apply eq_esum => i Pi; rewrite nneseries_esum.
Qed.

Lemma nneseries_interchange (R : realType) (a : nat -> nat -> \bar R)
  (P Q : pred nat) : (forall i j, 0 <= a i j) ->
  \sum_(i <oo | P i) \sum_(j <oo | Q j) a i j =
  \sum_(j <oo | Q j) \sum_(i <oo | P i) a i j.
Proof.
move=> a0; rewrite !nneseries_esum_prod//.
rewrite (reindex_esum (Q `*` P) _ (fun x => (x.2, x.1)))//; split=> //=.
by move=> [i j] [/=].
by move=> [i1 i2] [j1 j2] /= _ _ [] -> ->.
by move=> [i1 i2] [Pi1 Qi2] /=; exists (i2, i1).
Qed.

End nneseries_interchange.

Lemma esum_image (R : realType) (T T' : choiceType)
    (P : set T) (e : T -> T') (a : T' -> \bar R) :
    set_inj P e ->
  \esum_(j in e @` P) a j = \esum_(i in P) a (e i).
Proof. by move=> /inj_bij; apply: reindex_esum. Qed.
Arguments esum_image {R T T'} P e a.

Lemma esum_pred_image (R : realType) (T : choiceType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) :
    (forall n, P n -> 0 <= a (e n)) ->
    set_inj P e ->
  \esum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof. by move=> a0 einj; rewrite esum_image// nneseries_esum. Qed.
Arguments esum_pred_image {R T} a e P.

Lemma esum_set_image  [R : realType] [T : choiceType] [a : T -> \bar R]
    [e : nat -> T] [P : set nat] :
    (forall n : nat, P n -> 0 <= a (e n)) ->
  set_inj P e ->
  \esum_(i in [set e x | x in P]) a i = \sum_(i <oo | i \in P) a (e i).
Proof.
move=> a0 einj; rewrite esum_image// nneseries_esum ?set_mem_set//.
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
  move=> Kk Jkx; rewrite /a'; case: ifPn; rewrite ?(inE, notin_setE)//=.
  by case; exists k.
have a'_ge0 x : a' x >= 0 by rewrite /a'; case: ifPn; rewrite // ?inE => /a_ge0.
transitivity (\esum_(i in \bigcup_(k in K) J' k) a' i).
  rewrite esum_mkcond [RHS]esum_mkcond /a'; apply: eq_esum => x _.
  do 2!case: ifPn; rewrite ?(inE, notin_setE)//= => J'x Jx.
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
do 2!case: ifPn; rewrite ?(inE, notin_setE)//=.
- by move=> /a'E->//.
- by rewrite /J'; case: ifPn => //.
move=> Jix; rewrite /J'; case: ifPn=> //=.
by move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[->]//; exists x.
Qed.

End esum_bigcup.

Arguments esum_bigcupT {R T K} J a.
Arguments esum_bigcup {R T K} J a.

Lemma nneseries_sum_bigcup {R : realType} (T : choiceType) (F : (set T)^nat)
    (f : T -> \bar R) : trivIset [set: nat] F -> (forall i, 0 <= f i)%E ->
  (\esum_(i in \bigcup_n F n) f i = \sum_(0 <= i <oo) (\esum_(j in F i) f j))%E.
Proof.
move=> tF f0; rewrite esum_bigcupT// nneseries_esum//; last first.
  by move=> k _; exact: esum_ge0.
by rewrite fun_true; apply: eq_esum => /= i _.
Qed.

Definition summable (T : choiceType) (R : realType) (D : set T)
  (f : T -> \bar R) := (\esum_(x in D) `| f x | < +oo)%E.

Section summable_lemmas.
Local Open Scope ereal_scope.
Variables (T : choiceType) (R : realType).
Implicit Types (D : set T) (f : T -> \bar R).

Lemma summable_pinfty D f : summable D f -> forall x, D x -> `| f x | < +oo.
Proof.
move=> Dfoo x Dx; apply: le_lt_trans Dfoo.
rewrite (esumID [set x])// setI1 mem_set// esum_set1// leeDl//.
exact: esum_ge0.
Qed.

Lemma summableE D f : summable D f = (\esum_(x in D) `| f x | \is a fin_num).
Proof.
rewrite /summable fin_numElt; apply/idP/idP => [->|/andP[]//].
by rewrite andbT (lt_le_trans (ltNyr 0))//; exact: esum_ge0.
Qed.

Lemma summableD D f g : summable D f -> summable D g -> summable D (f \+ g).
Proof.
move=> Df Dg; apply: le_lt_trans (lte_add_pinfty Df Dg).
by rewrite -esumD//; apply le_esum => t Dt; exact: lee_abs_add.
Qed.

Lemma summableN D f : summable D f = summable D (\- f).
Proof.
by rewrite /summable; congr (_ < +oo); apply: eq_esum => t Dt; rewrite abseN.
Qed.

Lemma summableB D f g : summable D f -> summable D g -> summable D (f \- g).
Proof. by move=> Df; rewrite summableN; exact: summableD. Qed.

Lemma summable_funepos D f : summable D f -> summable D f^\+.
Proof.
apply: le_lt_trans; apply le_esum => t Dt.
by rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDl.
Qed.

Lemma summable_funeneg D f : summable D f -> summable D f^\-.
Proof.
apply: le_lt_trans; apply le_esum => t Dt.
by rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDr.
Qed.

End summable_lemmas.

Import numFieldNormedType.Exports.

Section summable_nat.
Local Open Scope ereal_scope.
Variable R : realType.

Lemma summable_fine_sum r (P : pred nat) (f : nat -> \bar R) : summable P f ->
  (\sum_(0 <= k < r | P k) fine (f k))%R = fine (\sum_(0 <= k < r | P k) f k).
Proof.
move=> Pf; elim: r => [|r ih]; first by rewrite !big_nil.
rewrite big_mkcond/= big_nat_recr// [in RHS]big_mkcond/= big_nat_recr//=.
rewrite -!big_mkcond/= ih; case: ifPn => Pr => //; last by rewrite adde0 addr0.
rewrite fineD//; last first.
  by rewrite fin_num_abs (summable_pinfty Pf).
by apply/sum_fin_numP => i ir Pi; rewrite fin_num_abs (summable_pinfty Pf).
Qed.

Lemma summable_cvg (P : pred nat) (f : (\bar R)^nat) :
  (forall i, P i -> 0 <= f i)%E -> summable P f ->
  cvg ((fun n => \sum_(0 <= k < n | P k) fine (f k))%R @ \oo).
Proof.
move=> f0 Pf; apply: nondecreasing_is_cvgn.
  by apply: nondecreasing_series => n _ Pn; exact/fine_ge0/f0.
exists (fine (\sum_(i <oo | P i) `|f i|)) => x /= [n _ <-].
rewrite summable_fine_sum// -lee_fin fineK//; last first.
  by apply/sum_fin_numP => i ni Pi; rewrite fin_num_abs (summable_pinfty Pf).
rewrite fineK//; last first.
  rewrite nneseries_esum// fin_numElt; apply/andP; split.
    by rewrite (@lt_le_trans _ _ 0)// ?lte_ninfty//; exact: esum_ge0.
  by apply: le_lt_trans Pf; apply le_esum.
apply: le_trans (nneseries_lim_ge n _) => //; apply: lee_sum => i _.
by rewrite lee_abs.
Qed.

Lemma summable_nneseries_lim (P : pred nat) (f : (\bar R)^nat) :
    (forall i, P i -> 0 <= f i)%E -> summable P f ->
  \sum_(i <oo | P i) f i =
  (lim ((fun n => (\sum_(0 <= k < n | P k) fine (f k))%R) @ \oo))%:E.
Proof.
move=> f0 Pf; pose A_ n := (\sum_(0 <= k < n | P k) fine (f k))%R.
transitivity (lim (EFin \o A_ @ \oo)).
  apply/congr_lim/funext => /= n; rewrite /A_ /= -sumEFin.
  apply eq_bigr => i Pi/=; rewrite fineK//.
  by rewrite fin_num_abs (@summable_pinfty _ _ P).
by rewrite EFin_lim//; apply: summable_cvg.
Qed.

Lemma summable_eseries (f : nat -> \bar R) (P : pred nat) : summable P f ->
  \sum_(i <oo | P i) (f i) =
  \sum_(i <oo | P i) f^\+ i - \sum_(i <oo | P i) f^\- i.
Proof.
move=> Pf.
pose A_ n := (\sum_(0 <= k < n | P k) fine (f^\+ k))%R.
pose B_ n := (\sum_(0 <= k < n | P k) fine (f^\- k))%R.
pose C_ n := fine (\sum_(0 <= k < n | P k) f k).
pose A := lim (A_ @ \oo).
pose B := lim (B_ @ \oo).
suff: ((fun n => C_ n - (A - B)) @ \oo --> (0 : R^o))%R.
  move=> CAB.
  rewrite [X in  X - _]summable_nneseries_lim//; last exact/summable_funepos.
  rewrite [X in _ - X]summable_nneseries_lim//; last exact/summable_funeneg.
  rewrite -EFinB; apply/cvg_lim => //; apply/fine_cvgP; split; last first.
    by apply: (@cvg_sub0 _ _ _ _ _ _ (cst (A - B)%R) _ CAB) => //; exact: cvg_cst.
  apply: nearW => n; rewrite fin_num_abs; apply: le_lt_trans Pf => /=.
  by rewrite -nneseries_esum// (le_trans (lee_abs_sum _ _ _))// nneseries_lim_ge.
have : ((fun x => A_ x - B_ x) @ \oo --> A - B)%R.
  apply: cvgD.
  - by apply: summable_cvg => //; exact/summable_funepos.
  - by apply: cvgN; apply: summable_cvg => //; exact/summable_funeneg.
move=> /cvgrPdist_lt cvgAB; apply/cvgrPdist_lt => e e0.
move: cvgAB => /(_ _ e0) [N _/= hN] /=.
near=> n.
rewrite distrC subr0.
have -> : (C_ = A_ \- B_)%R.
  apply/funext => k.
  rewrite /= /A_ /C_ /B_ -sumrN -big_split/= -summable_fine_sum//.
  apply eq_bigr => i Pi; rewrite -fineB//.
  - by rewrite [in LHS](funeposneg f).
  - by rewrite fin_num_abs (@summable_pinfty _ _ P) //; exact/summable_funepos.
  - by rewrite fin_num_abs (@summable_pinfty _ _ P) //; exact/summable_funeneg.
by rewrite distrC; apply: hN; near: n; exists N.
Unshelve. all: by end_near. Qed.

Lemma summable_eseries_esum  (f : nat -> \bar R) (P : pred nat) :
  summable P f -> \sum_(i <oo | P i) f i = esum P f^\+ - esum P f^\-.
Proof.
move=> Pfoo.
by rewrite -nneseries_esum// -nneseries_esum// [LHS]summable_eseries.
Qed.

End summable_nat.

Section esumB.
Local Open Scope ereal_scope.
Variables (R : realType) (T : choiceType).
Implicit Types (D : set T) (f g : T -> \bar R).

Let esum_posneg D f := esum D f^\+ - esum D f^\-.

Let ge0_esum_posneg D f : (forall x, D x -> 0 <= f x) ->
  esum_posneg D f = \esum_(x in D) f x.
Proof.
move=> Sa; rewrite /esum_posneg [X in _ - X](_ : _ = 0) ?sube0; last first.
  by rewrite esum1// => x Sx; rewrite -[LHS]/(f^\- x) (ge0_funenegE Sa)// inE.
apply: eq_esum => t St; rewrite funeposE; apply/max_idPl; exact: Sa.
Qed.

Lemma esumB D f g : summable D f -> summable D g ->
  (forall i, D i -> 0 <= f i) -> (forall i, D i -> 0 <= g i) ->
  \esum_(i in D) (f \- g)^\+ i - \esum_(i in D) (f \- g)^\- i =
  \esum_(i in D) f i - \esum_(i in D) g i.
Proof.
move=> Df Dg f0 g0.
have /eqP : esum D (f \- g)^\+ + esum_posneg D g =
            esum D (f \- g)^\- + esum_posneg D f.
  rewrite !ge0_esum_posneg// -!esumD//.
  apply eq_esum => i Di; rewrite funeposE funenegE.
  have [fg|fg] := leP 0 (f i - g i).
    rewrite max_r 1?leeNl ?oppe0// add0e subeK//.
    by rewrite fin_num_abs (summable_pinfty Dg).
  rewrite add0e max_l; last by rewrite leeNr oppe0 ltW.
  rewrite fin_num_oppeB//; last by rewrite fin_num_abs (summable_pinfty Dg).
  by rewrite -addeA addeCA addeA subeK// fin_num_abs (summable_pinfty Df).
rewrite [X in _ == X -> _]addeC -sube_eq; last 2 first.
  - rewrite fin_numD; apply/andP; split.
      rewrite (@eq_esum _ _ _ _ (abse \o (f \- g)^\+))//.
        by rewrite -summableE; exact/summable_funepos/summableB.
      by move=> t Dt; rewrite /= gee0_abs.
    move: Dg; rewrite summableE (@eq_esum _ _ _ _ g)//.
      by rewrite ge0_esum_posneg// => t Tt; rewrite gee0_abs// g0.
    by move=> t Tt; rewrite gee0_abs// g0.
  - rewrite fin_num_adde_defr// ge0_esum_posneg//.
    rewrite (@eq_esum _ _ _ _ (abse \o f))// -?summableE// => i Di.
    by rewrite /= gee0_abs// f0.
rewrite -addeA addeCA eq_sym [X in _ == X -> _]addeC -sube_eq; last 2 first.
  - rewrite ge0_esum_posneg//.
    rewrite (@eq_esum _ _ _ _ (abse \o f))// -?summableE// => i Di.
    by rewrite /= gee0_abs// f0.
  - rewrite fin_num_adde_defl// ge0_esum_posneg//.
    rewrite (@eq_esum _ _ _ _ (abse \o g))// -?summableE// => i Di.
    by rewrite /= gee0_abs// g0.
by rewrite ge0_esum_posneg// ge0_esum_posneg// => /eqP ->.
Qed.

End esumB.
