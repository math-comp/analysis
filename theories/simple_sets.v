(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum nngnum topology.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences measure csum cardinality lebesgue_measure.

(******************************************************************************)
(*                                                                            *)
(* Elements from the original formalization of the Lebesgue measure           *)
(*                                                                            *)
(*            itv_diff i j == i \ j where i and j are intervals assuming      *)
(*                            ~ j <= i                                        *)
(*              lt_itv i j == total ordering of intervals: the left bound of  *)
(*                            i is smaller than the one of j, and if it is    *)
(*                            equal then the right bound of i is smaller than *)
(*                            the one of j                                    *)
(*              le_itv i j := (i = j) \/ lt_itv i j                           *)
(*              itv_cplt s == complement of the list of intervals s           *)
(*                 ccitv n == the centered closed interval [-n, n]            *)
(*      sorted_decompose s == turns a *sorted* list of intervals s into a     *)
(*                            list of non-overlapping intervals with the same *)
(*                            cover                                           *)
(*             decompose s == turn a list of intervals into a sequence of     *)
(*                            non-overlapping intervals with the same cover   *)
(*             Module Sset == simple sets form an algebra of sets             *)
(*             [sset of s] == the finite union of the list of intervals s     *)
(*                            (a "simple set")                                *)
(*             hlengthUitv == (lemma) hlength is additive on intervals        *)
(*               slength A == measure of the set A when it is a simple set,   *)
(*                            and 0 o.w.                                      *)
(*        nth_interval f k == kth interval in the sequence f of lists of      *)
(*                            intervals                                       *)
(*    slength_sigma_finite == (lemma) slength is sigma-finite                 *)
(*                                                                            *)
(* The main proof is the proof that slength is sigma-additive. We list up the *)
(* several lemmas that make up this:                                          *)
(*   slength_additive == slength is additive                                  *)
(*   slength_sigma_subadditive_finite_itv == slength is sigma-subadditive     *)
(*     on finite intervals                                                    *)
(*   slength_sigma_additive_finite_itv == slength is additive on finite       *)
(*     intervals                                                              *)
(*   slength_sigma_subadditive_infinite_itv == slength is sigma-subadditive   *)
(*     on infinite intervals                                                  *)
(*   slength_sigma_subadditive_itv == slength is sigma-subadditive on         *)
(*     intervals                                                              *)
(*   slength_sigma_additive_itv == slength is sigma-additive on intervals     *)
(*   slength_semi_sigma_additive == slength is sigma-additive on simple sets  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "[ 'sset' 'of' s ]"
  (at level 0, format "[ 'sset'  'of'  s ]").

Section itv_diff.
Variable R : realType.
Implicit Types i j : interval R.

(* assumes ~ j <= i *)
Definition itv_diff i j := if ~~ neitv (itv_meet i j) then i
  else
    let: Interval i1 i2 := i in let: Interval j1 j2 := j in
    if (j1 <= i1)%O then
      (if (j2 <= i2)%O then Interval j2 i2 else 0%O)
    else
      (if (j2 <= i2)%O then 0%O else Interval i1 j1).

Lemma set_itv_diff i j :
  (~~ (j <= i)%O) || ((j <= i)%O && (j.1 == i.1)) ->
  [set` itv_diff i j] = [set` i] `\` [set` j].
Proof.
move=> ji.
rewrite /itv_diff; case: ifPn => [ij0|/negPn ij0].
  by apply/esym/setDidPl; rewrite -set_itv_meet; apply/eqP; move/negPn : ij0.
move: i j => [i1 i2] [j1 j2] /= in ji ij0 *.
have [ji1|ji1] := leP j1 i1.
- have [ji2|ji2] := leP j2 i2.
  + rewrite eqEsubset; split=> x /=.
    * rewrite itv_boundlr => /andP[j2x xi2]; split=> /=.
        rewrite itv_boundlr xi2 andbT (@le_trans _ _ j2) // leNgt.
        apply/negP => j2j1; apply/negP : ij0; rewrite joinEtotal meetEtotal.
        by rewrite maxElt ltNge ji1 /= minElt ltNge ji2 /= neitvE /= -leNgt ltW.
      rewrite itv_boundlr => /andP[j1x xj2].
      by have := le_trans xj2 j2x; rewrite lte_bnd ltxx.
    * case; rewrite !itv_boundlr => /andP[i1x xi2] /negP; rewrite xi2 andbT.
      by apply: contraNle; rewrite (le_trans ji1).
  + rewrite set_itvE; apply/esym; rewrite setD_eq0 => x /=; rewrite !itv_boundlr.
    by move=> /andP[i1x xi2]; rewrite (le_trans ji1)// (le_trans xi2)// ltW.
- have [ji2|ji2] := leP j2 i2.
    case/orP: ji => [|/andP[ji]]; last by rewrite gt_eqF.
    by rewrite itv_leEmeet [in X in X -> _]/= (join_l (ltW _))// meet_l// eqxx.
  rewrite eqEsubset; split=> x /=.
  * rewrite itv_boundlr => /andP[i1x xj1]; split.
      rewrite itv_boundlr i1x /= leNgt; apply/negP => i2j1; apply/negP : ij0.
      rewrite meetEtotal minElt ji2 joinEtotal maxElt ji1 neitvE /=.
      by rewrite -leNgt (le_trans _ xj1) // (le_trans (ltW i2j1)).
    rewrite itv_boundlr => /andP[j1x xj2].
    by have := le_trans xj1 j1x; rewrite lte_bnd ltxx.
  * move=> -[]; rewrite itv_boundlr => /andP[i1x xi2].
    rewrite itv_boundlr => /negP; rewrite negb_and -2!ltNge => /orP[xj1|j2x].
      by rewrite itv_boundlr i1x.
    by have := lt_trans (le_lt_trans xi2 ji2) j2x; rewrite ltxx.
Qed.

Lemma set_itv_diffxx i : [set` itv_diff i i] = set0.
Proof. by rewrite set_itv_diff ?setDv// lexx eqxx. Qed.

End itv_diff.

Section simple_sets.
Variable R : numDomainType.
Implicit Types (s : seq (interval R)) (i : interval R).

Definition sset s := \big[setU/set0]_(x <- s) [set` x].

Local Notation "[ 'sset' 'of' s ]" := (sset s).

Lemma ssetE s : [sset of s] = \big[setU/set0]_(x <- s) [set` x].
Proof. by []. Qed.

Lemma sset_cons i s : [sset of i :: s] = [set` i] `|` [sset of s].
Proof. by rewrite ssetE big_cons -ssetE. Qed.

Lemma sset_nil : [sset of @nil (interval R)] = set0.
Proof. by rewrite ssetE big_nil. Qed.

Lemma sset_cons1 i : [sset of [:: i]] = [set` i].
Proof. by rewrite sset_cons sset_nil setU0. Qed.

Lemma sset_bigcup s : [sset of s] = \bigcup_(i in [set j | j \in s]) [set` i].
Proof. by rewrite bigcup_set. Qed.

Lemma ssetP s x :
  [sset of s] x <-> (\bigcup_(i in [set j | j \in s]) [set` i]) x.
Proof. by rewrite -sset_bigcup. Qed.

Lemma sseti s1 s2 : s1 =i s2 -> [sset of s1] = [sset of s2].
Proof.
move=> s12; rewrite 2!sset_bigcup eqEsubset; split => x [i];
  rewrite /mkset => + ix; by [rewrite s12 => ?; exists i |
                             rewrite -s12 => ?; exists i].
Qed.

Lemma sset_filter_neitv s : [sset of [seq x <- s | neitv x]] = [sset of s].
Proof.
elim: s => // h t ih /=; case: ifPn => [h0|].
  by rewrite sset_cons ih -sset_cons.
by rewrite negbK => h0; rewrite sset_cons ih (eqP h0) set0U.
Qed.

End simple_sets.
Notation "[ 'sset' 'of' s ]" := (sset s).

Notation bnd1eta := (fun (i : interval _) => i.1).
Notation bnd2eta := (fun (i : interval _) => i.2).

Section itv_cplt.
Variable R : realType.
Implicit Types s : seq (interval R).

Definition itv_cplt s : seq (interval R) :=
  let a' := -oo%O :: map bnd2eta s in
  let b' := rcons (map bnd1eta s) +oo%O in
  map (uncurry (@Interval _)) (zip a' b').

Lemma itv_cplt_nil : [sset of itv_cplt [::]] = setT.
Proof. by rewrite /itv_cplt ssetE big_seq1 set_itvE. Qed.

Lemma itv_cpltE_subset s : ~` [sset of s] `<=` [sset of itv_cplt s].
Proof.
elim: s => [x _|[a1 b1] t ih x]; first by rewrite itv_cplt_nil.
rewrite sset_cons setCU => -[] x_notin_h /ih {}ih.
set a := map bnd1eta (Interval a1 b1 :: t).
set b := map bnd2eta (Interval a1 b1 :: t).
rewrite (_ : itv_cplt _ = Interval -oo%O a1 ::
  map (uncurry (@Interval _)) (zip b (rcons (behead a) +oo%O))) //.
rewrite sset_cons.
have : ([set` Interval -oo%O a1] `|` [set` Interval b1 +oo%O]) x.
  by rewrite set_itvC in x_notin_h.
case=> [xa1|xb1]; [by left|right].
have {ih} /ssetP[j] : [sset of map (uncurry (@Interval _))
  (zip (-oo%O :: behead b) (rcons (behead a) +oo%O))] x by [].
rewrite {1}/mkset => + jx; rewrite {}/b {}/a.
move: t => [|[a2 b2] t /=]; first by rewrite sset_cons1.
rewrite inE => /orP[/eqP jb2|jb2].
  apply/ssetP; exists (Interval b1 a2); first by rewrite /mkset inE eqxx.
  by rewrite /= itv_splitI xb1 /=; move: jx; rewrite jb2.
by apply/ssetP; exists j => //; rewrite /mkset inE jb2 orbT.
Qed.

Local Lemma sorted_itv_cpltE_subset s :
  sorted <=%O (map bnd2eta s) -> sorted <=%O (map bnd1eta s) ->
  [sset of itv_cplt s] `<=` ~` [sset of s].
Proof.
set a := map bnd1eta s; set b := map bnd2eta s.
move=> sorted_b sorted_a x.
move=> /ssetP[/= j] /mapP[[b' a']] /(nthP (+oo%O, -oo%O)) => -[n].
rewrite size_zip /= size_rcons 2!size_map minnn ltnS => ns.
rewrite nth_zip; last by rewrite size_rcons /= !size_map.
move=> -[nb' na'] jba'.
move=> xj /ssetP[] i si xi.
have [k [ks ik]] : exists k, (k < size s)%N /\
    i = Interval (nth -oo%O a k) (nth +oo%O b k).
  move/(nthP 0%O) : si => [k ks ki].
  exists k; split => //.
  by rewrite /a /b !(nth_map 0%O) // ki; case: i {xi ki}.
move: xi; rewrite ik /= itv_boundlr => /andP[akx xbk].
move: xj; rewrite jba' /= itv_boundlr => /andP[b'x xa'].
rewrite -/a in na'.
rewrite -/b in nb'.
have [kn|nk] := leP k n.
  case: n => [|n] in ns na' nb' kn *.
    move: kn; rewrite lex0 => /eqP k0.
    rewrite {ns ks} /= in nb' jba' b'x xa'.
    rewrite -{}nb' {b'x b'} in jba'.
    rewrite -na' /= in xa'.
    rewrite k0 /a /= in akx.
    rewrite {jba' k0 na' xbk ik k sorted_a sorted_b a' b j}.
    rewrite {}/a in xa'.
    case: s => [//|s0 s1] in si akx xa' *.
    by have := le_trans xa' akx; rewrite lte_bnd ltxx.
  rewrite /= in nb'.
  have : (n <= (size s).-1)%N by move: ns; clear -si; case: s si.
  rewrite leq_eqVlt => /predU1P[k's1|k's1].
    move: na'; rewrite nth_rcons size_map k's1 prednK //; last first.
      by move: ns; clear -si; case: s si.
    rewrite ltnn eqxx => ka'.
    have : (BRight x <= BLeft x)%O.
      rewrite (le_trans xbk) // (le_trans _ b'x) //= -nb'.
      apply: (sorted_leq_nth le_trans) => //.
      - by rewrite inE /b size_map.
      - by rewrite inE size_map.
      - by rewrite -ltnS k's1 prednK // (leq_ltn_trans _ ks).
    by rewrite lte_bnd ltxx.
  move: kn; rewrite le_eqVlt => /orP[kn|kn].
    have : (BRight x <= BLeft x)%O.
      rewrite (@le_trans _ _ (nth -oo%O a k)) // (le_trans xa') // -na'.
      by rewrite nth_rcons size_map -(eqP kn) ks.
    by rewrite lte_bnd ltxx.
  suff: (BRight x <= BLeft x)%O by rewrite lte_bnd ltxx.
  rewrite (@le_trans _ _ (nth +oo%O b k)) // (le_trans _ b'x) //= -nb'.
  by apply: (sorted_leq_nth le_trans) => //; rewrite inE ?/b size_map.
suff: (BRight x <= BLeft x)%O by rewrite lte_bnd ltxx.
rewrite (le_trans xa') //= (le_trans _ akx) //.
rewrite -na' nth_rcons size_map (ltn_trans nk ks).
apply: (sorted_leq_nth le_trans) => //; last exact: ltnW.
- by rewrite inE size_map (ltn_trans nk).
- by rewrite inE size_map.
Qed.

Lemma itv_cpltE s : sorted <=%O (map bnd2eta s) -> sorted <=%O (map bnd1eta s) ->
  [sset of itv_cplt s] = ~` [sset of s].
Proof.
by rewrite eqEsubset; split; [exact: sorted_itv_cpltE_subset |
                              exact: itv_cpltE_subset].
Qed.

Definition itv_cplt_ne s := [seq x <- itv_cplt s | neitv x].

Lemma itv_cplt_neE s :
  sorted <=%O (map bnd2eta s) -> sorted <=%O (map bnd1eta s) ->
  [sset of itv_cplt_ne s] = ~` [sset of s].
Proof. by move=> s_a s_b; rewrite /itv_cplt_ne sset_filter_neitv itv_cpltE. Qed.

End itv_cplt.

Section lt_itv.
Variable R : realFieldType.
Implicit Types i j : interval R.

Definition lt_itv i j := (i.1 < j.1)%O || ((i.1 == j.1) && (i.2 < j.2)%O).

Definition le_itv i j := (i == j) || (lt_itv i j).

Lemma le_itv_bnd1 i j : le_itv i j -> (i.1 <= j.1)%O.
Proof.
rewrite /le_itv => /predU1P[->//|]; rewrite /lt_itv.
by move=> /orP[/ltW//|/andP[/eqP->//]].
Qed.

Lemma le_itv_bnd2 i j : le_itv i j -> neitv j ->
  disjoint_itv i j -> (i.2 <= j.2)%O.
Proof.
move: i j => [i1 i2] [j1 j2] /=.
rewrite /le_itv /lt_itv /= => /predU1P[[-> -> //]|] /=.
case: ltgtP => // [i1j1 _ j0 ij|->{i1} /ltW //].
rewrite leNgt; apply/negP => j2i2.
move/eqP : ij; apply/eqP.
by rewrite -set_itv_meet /= (join_r (ltW _))// (meet_r (ltW _)).
Qed.

Lemma lt_itvxx i : lt_itv i i = false.
Proof. by rewrite /lt_itv 2!ltxx andbF. Qed.

Lemma lt_itv_def i j : lt_itv i j = (j != i) && le_itv i j.
Proof.
rewrite /le_itv andb_orr eq_sym andNb /=; apply/idP/idP => [ij|/andP[]//].
by rewrite andbC ij /=; apply: contraPN ij => /eqP ->; rewrite lt_itvxx.
Qed.

Lemma le_itv_refl : reflexive le_itv.
Proof. by case=> a b; rewrite /le_itv eqxx. Qed.

Lemma le_itv_anti : antisymmetric le_itv.
Proof.
move=> /= [a b] [c d]; rewrite /le_itv => /andP[/orP[/eqP[-> -> //]|]].
rewrite /lt_itv /= => /orP[ac /orP[/eqP//|]|/andP[/eqP ac bd]].
  by rewrite ltNge (ltW ac) /= eq_sym lt_eqF.
by rewrite ac eqxx ltxx /= ltNge (ltW bd) orbF => /eqP.
Qed.

Lemma lt_itv_trans : transitive lt_itv.
Proof.
move=> [k1 k2] [i1 i2] [j1 j2]; rewrite /lt_itv /=.
case: (ltgtP i1 k1) => // [ik1 _| <-{k1} ik2]; last first.
  by case: (ltgtP i1 j1) => // _; apply: lt_trans.
by case: (ltgtP k1 j1) => // [kj1 _|<-]; [rewrite (lt_trans ik1) | rewrite ik1].
Qed.

Lemma le_itv_trans : transitive le_itv.
Proof.
move=> j i k; rewrite /le_itv.
move=> /orP[/eqP -> //|ij] /orP[/eqP <-|jk]; first by rewrite orbC ij.
by rewrite (lt_itv_trans ij jk) orbT.
Qed.

Definition le_itv_porderMixin :=
  LePOrderMixin lt_itv_def le_itv_refl le_itv_anti le_itv_trans.
Fact le_itv_display (disp : unit) : unit. Proof. exact. Qed.
Definition le_itv_porderType (disp : unit) :=
  POrderType (le_itv_display disp) (interval R) le_itv_porderMixin.

Lemma le_lt_trans_itv j i k : le_itv i j -> lt_itv j k -> lt_itv i k.
Proof. exact: (@le_lt_trans _ (le_itv_porderType _)). Qed.

Lemma lt_le_trans_itv j i k : lt_itv i j -> le_itv j k -> lt_itv i k.
Proof. exact: (@lt_le_trans _ (le_itv_porderType _)). Qed.

Lemma ltW_itv i j : lt_itv i j -> le_itv i j.
Proof. exact: (@ltW _ (le_itv_porderType _)). Qed.

Lemma total_le_itv : total le_itv.
Proof.
move=> [i1 i2] [j1 j2]; rewrite /le_itv/lt_itv/=; case/boolP: (_ == _) => ij//=.
case: (ltgtP i1 j1) => //=; rewrite ?orbT // => ij1.
by rewrite ij1; case: ltgtP => //=; rewrite ?orbT// => ->; rewrite eqxx.
Qed.

Definition le_itv_orderMixin :=
  LeOrderMixin lt_itv_def (fun _ _ => erefl) (fun _ _ => erefl)
               le_itv_anti le_itv_trans total_le_itv.
Fail Canonical le_itv_latticeType := LatticeType (interval R) le_itv_orderMixin.

Lemma lt_itv_lt i j : lt_itv i j -> disjoint_itv i j ->
  forall x y, x \in i -> y \in j -> x < y.
Proof.
move: i j => [a b] [c d]; rewrite /lt_itv; case: (ltgtP a c) => // [ac _|<-{c}].
- move=> /disjoint_neitv/negPn/eqP ij0 x y.
  rewrite 2!itv_boundlr => /andP[ax xb] /andP[cy yd].
  have [bc|cb] := leP b c; first by have := le_trans xb (le_trans bc cy).
  rewrite ltNge; apply/negP => yx.
  move: ij0; rewrite predeqE => /(_ y)[+ _]; apply.
  apply/itv_meet_mem; rewrite 2!itv_boundlr.
  by rewrite (le_trans (ltW ac)) //= (le_trans _ xb) // yd andbT cy.
- move=> /= ?; rewrite /disjoint_itv/disj_set -set_itv_meet => abd.
  move=> x y; rewrite 2!itv_boundlr => /andP[ax xb] /andP[ay yd].
  rewrite ltNge; apply/negP => yx.
  move/negPn : abd => /negP; apply; apply/neitvP => /=.
  by rewrite joinxx ltxI (le_lt_trans ax)// (le_lt_trans ay).
Qed.

Lemma le_itv_lt i j : le_itv i j -> disjoint_itv i j ->
  forall x y, x \in i -> y \in j -> x < y.
Proof.
move: i j => [i1 i2] [j1 j2].
move/orP => [/eqP[<-{j1} <-{j2}]|]; last exact: lt_itv_lt.
have [i1i2|i1i2 _ x y] := ltP i1 i2; last by rewrite itv_ge // -leNgt.
by move=> /disjoint_neitv/neitvP /=; rewrite meetxx joinxx.
Qed.

Let lt_itv_subset i j k (r : R) : r \in i -> r \in k -> r \notin j ->
  lt_itv i j -> lt_itv j k ->
  (i <= j)%O \/ (j <= i)%O.
Proof.
move: i j k => [a1 a2] [b1 b2] [c1 c2] + + + ab bc; move: bc ab => /=.
rewrite /lt_itv /=; case: (ltgtP b1 c1) => //= [b1c1 _|<-{c1} b2c2]; last first.
  case : (ltgtP a1 b1) => //= [a1b1 _|<-{b1} a2b2]; last first.
    rewrite 2!itv_boundlr => /andP[a1x xa2] /andP[_ xc2] _; left.
    by rewrite itv_leEmeet/= joinxx (meet_l (ltW _)).
  rewrite 3!itv_boundlr => /andP[a1x xa2] /andP[b1x xc2].
  rewrite negb_and -2!ltNge => xb1b2; right.
  rewrite itv_leEmeet /= (join_l (ltW _))//.
  case/orP: xb1b2 => [|?]; first by move/(le_lt_trans b1x); rewrite ltxx.
  by rewrite meet_l // (le_trans _ xa2) //= ltW.
case : (ltgtP a1 b1) => // [a1b1 _|-> // a2b2].
  rewrite 3!itv_boundlr => /andP[a1x xa2] /andP[c1x xc2].
  rewrite negb_and -2!ltNge => xb1b2; right.
  rewrite itv_leEmeet /= (join_l (ltW _))//; case/orP: xb1b2 => [xb1|b2x].
    by have := lt_trans (lt_le_trans b1c1 c1x) xb1; rewrite ltxx.
  by rewrite meet_l//= (le_trans _ xa2) // ltW.
rewrite 3!itv_boundlr => /andP[b1x xa2] _ _; left.
by rewrite itv_leEmeet/= joinxx (meet_l (ltW _)).
Qed.

Lemma le_itv_subset i j k (r : R) : r \in i -> r \in k -> r \notin j ->
  le_itv i j -> le_itv j k ->
  (i <= j)%O \/ (j <= i)%O.
Proof.
move=> xa xc xb /orP[/eqP <- _|ab]; [by left|].
move/orP => [/eqP bc|]; last exact: (lt_itv_subset _ xc).
by move: xb; rewrite bc xc.
Qed.

End lt_itv.
Arguments lt_itv {R}.
Arguments le_itv {R}.
Arguments lt_itv_trans {R}.
Arguments le_itv_trans {R}.
Arguments total_le_itv {R}.
Arguments le_itv_refl {R}.
Arguments le_itv_anti {R}.

Section cover_trivIset.
Variable R : realFieldType.

Lemma perm_subset_set_itv_nth (D : set nat) (s s' : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D -> perm_eq s s' ->
  [set [set` nth 0%O s i] | i in D] `<=`
    [set [set` nth 0%O s' i] | i in D].
Proof.
move=> sD ss' A [i Di iA].
have [/(mem_nth 0%O)|si] := ltnP i (size s); last first.
  move: iA; rewrite nth_default // => <-.
  by exists i => //; rewrite nth_default // -(perm_size ss').
move/perm_mem : (ss') => ->.
move/(nthP 0%O) => [j js' ji]; exists j; last by rewrite ji.
by apply sD; rewrite (perm_size ss').
Qed.

Lemma perm_set_itv_nth (D : set nat) (s s' : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D -> perm_eq s s' ->
  [set [set` nth 0%O s i] | i in D] =
    [set [set` nth 0%O s' i] | i in D].
Proof.
move=> sD ss'; rewrite eqEsubset; split; apply perm_subset_set_itv_nth => //.
by rewrite -(perm_size ss').
by rewrite perm_sym.
Qed.

Lemma cover_set_itv_nth_sort (D : set nat) (s : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D ->
  cover D (fun n => [set` nth 0%O s n]) =
  cover D (fun n => [set` nth 0%O (sort le_itv s) n]).
Proof.
move=> sD; apply: eqcover_r; apply: perm_set_itv_nth => //.
by rewrite perm_sym perm_sort.
Qed.

Lemma cover_set_itv_nthE (s : seq (interval R)) (D : set nat) :
  [set k | (k < size s)%N] `<=` D ->
  cover D (fun n => [set` nth 0%O s n]) = \big[setU/set0]_(i <- s) [set` i].
Proof.
move=> sD; rewrite eqEsubset; split => [r [i Di ri]|r].
- rewrite -bigcup_set; exists (nth 0%O s i) => //; apply/mem_nth.
  by rewrite ltnNge; apply: contraPN ri => si; rewrite nth_default.
- rewrite -bigcup_set => -[/= i /(nthP 0%O)[k ks <-{i} kr]]; exists k => //.
  exact: sD.
Qed.

Lemma trivIset_itv_meet (s : seq (interval R)) (i : interval R) :
  trivIset setT (fun n => [set` nth 0%O s n]) ->
  trivIset setT (fun n => [set` nth 0%O [seq itv_meet i j | j <- s] n]).
Proof.
move=> tJ.
rewrite -(@trivIset_restr _ _ _ [set k | (k < size s)%N]) //; last first.
  move=> k _ /negP; rewrite -leqNgt => Jk.
  by rewrite nth_default ?size_map// set_itvE.
apply/trivIsetP => a b aJ bJ ab.
rewrite (nth_map 0%O) // (nth_map 0%O) // !set_itv_meet setIACA setIid.
by move/trivIsetP : tJ => -> //; rewrite setI0.
Qed.

Lemma trivIset_sort (s : seq (interval R)) (D : set nat) :
  [set k | (k < size s)%N] `<=` D ->
  trivIset D (fun i => [set` nth 0%O s i]) ->
  trivIset D (fun i => [set` nth 0%O (sort le_itv s) i]).
Proof.
move=> sD ts; rewrite trivIset_set_itv_nth ?set_itvE//.
apply (@perm_eq_trivIset _ [seq [set` i] | i <- s]).
- by apply: subset_trans _ sD => /= i; rewrite size_map.
- by rewrite perm_map // perm_sym perm_sort.
- by rewrite -(@trivIset_set_itv_nth _ 0%O) ?set_itvE.
Qed.

End cover_trivIset.


Lemma sset_sort_le_itv (R : realType) (s : seq (interval R)) :
  [sset of sort le_itv s] = [sset of s].
Proof. exact/sseti/mem_sort. Qed.

Section lt_itv_diff.
Variable R : realType.
Implicit Types i j : interval R.

Let lt_itv_diff i j : lt_itv i j -> ~~ (j <= i)%O -> ~~ (i <= j)%O ->
  lt_itv (itv_diff i j) j.
Proof.
rewrite /itv_diff; case: ifPn => //; move: i j => [a b] [c d] /=.
rewrite /lt_itv /=; case: ltgtP => [ab _ _ ji ijb|//|/= <-{c} ij0 bd _ abd].
  have [db|db] /= := leP d b; last by rewrite ab.
  by move: ji; rewrite itv_leEmeet /= (join_l (ltW _))// meet_l// eqxx.
rewrite leNgt bd /=.
by move: abd; rewrite itv_leEmeet /= joinxx (meet_l (ltW _)) // eqxx.
Qed.

Lemma le_itv_diff i j : le_itv i j -> ~~ (j <= i)%O -> ~~ (i <= j)%O ->
  le_itv (itv_diff i j) j.
Proof.
rewrite /le_itv => /orP[/eqP <-{j}|]; first by rewrite lexx.
by move=> ab sba sab; apply/orP; right; exact: lt_itv_diff.
Qed.

Let lt_itv_itv_diff k i j : ~~ (j <= i)%O -> disjoint_itv k i ->
  lt_itv i j -> lt_itv k i -> lt_itv k j ->
  lt_itv k (itv_diff i j).
Proof.
move: k i j => [k1 k2] [a1 a2] [b1 b2] /=; rewrite /lt_itv /=.
case: (ltgtP a1 b1) => [a1b1 ba + _| // | <-{b1}].
  have a2b2 : (a2 < b2)%O.
    rewrite ltNge; apply: contra ba => b2a2.
    by rewrite itv_leEmeet /= (join_l (ltW _))// meet_l.
  move: ba a1b1; case: (ltgtP k1 a1) => [k1a1 _ a1b1 ya _ _|//|
                                        <-{a1} ba a1b1 ya /= k2a2 _].
    rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite k1a1.
    by rewrite leNgt a1b1 /= leNgt a2b2 /= k1a1.
  rewrite /itv_diff; case: ifPn => [_|/negPn ab0]; first by rewrite ltxx eqxx.
  rewrite leNgt a1b1 /= leNgt a2b2 /= ltxx eqxx /= ltNge.
  apply: contraPN ya => b1k2 /disjoint_neitv/neitvP; apply => /=.
  by rewrite joinxx (meet_l (ltW k2a2)) (lt_le_trans a1b1).
case: (ltgtP k1 a1) => [k1a1 ab ya /= a2b2 _ _|//|
                       <-{a1} ab ya /= a2b2 k2a2 k2b2].
  rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite k1a1.
  by rewrite lexx leNgt a2b2 /= (lt_le_trans k1a1) // bound_lex1.
rewrite /itv_diff; case: ifPn => [_|/negPn ab0]; first by rewrite ltxx eqxx.
rewrite lexx leNgt a2b2 /= (ltNge k2) bound_le0x andbF orbF ltNge.
apply: contraPN ab0; rewrite ge_pinfty => /eqP k1oo.
by rewrite neitvE /= k1oo join_r // neitv_lt_bnd.
Qed.

Let le_itv_itv_diff0 i j : [set` i] = set0 -> le_itv i (itv_diff i j).
Proof.
move=> i0.
by rewrite /itv_diff /neitv /= set_itv_meet i0 set0I negbK eqxx /le_itv eqxx.
Qed.

Lemma le_itv_itv_diff k i j : ~~ (j <= i)%O -> disjoint_itv k i ->
  le_itv i j -> le_itv k i -> le_itv k j ->
  le_itv k (itv_diff i j).
Proof.
move=> ji ki => /predU1P[ij|ij]; first by rewrite ij lexx in ji.
move=> /predU1P[ya|ya /predU1P[kj|kj]].
- move: ki; rewrite {}ya {k} => ii.
  have [a0 _|a0 _] := eqVneq [set` i] set0; first exact: le_itv_itv_diff0.
  by move: ii; rewrite /disjoint_itv/disj_set setIid (negbTE a0).
- by move: ya; rewrite kj => /(lt_itv_trans _ _ _ ij); rewrite lt_itvxx.
- by apply/orP; right; exact: lt_itv_itv_diff.
Qed.

End lt_itv_diff.

Section lt_itv_disjoint.
Variable R : realType.

Lemma neitv_sorted_disj h (t : seq (interval R)) :
  all neitv t -> sorted le_itv (h :: t) -> path disjoint_itv h t ->
  (forall c, c \in t -> disjoint_itv h c).
Proof.
elim: t h => [h t0 _ _ c //|
             b t ih a t0 /= /andP[lt_ab lt_bt] /andP[dis_ab dis_bt] c].
rewrite inE => /orP[/eqP ->{c} //|ct]; apply: ih => //.
- by move: t0; rewrite /= => /andP[].
- by rewrite (mask_second b) (sorted_mask (@le_itv_trans _)) //= lt_ab.
- case: t => [//|d t] in t0 lt_bt dis_bt ct *.
  move: dis_bt; rewrite [in X in X -> _]/= => /andP[dis_bd dis_dt].
  rewrite /= {}dis_dt andbT.
  have {}lt_ab := le_itv_lt lt_ab dis_ab.
  move/andP : lt_bt => [+ _] => /le_itv_lt/(_ dis_bd) lt_bd.
  apply/lt_disjoint => x y xa yd.
  have /neitvP nb : neitv b by move: t0 => /= /andP[].
  by rewrite (@lt_trans _ _ (miditv b) _ _ (lt_ab _ _ _ _) (lt_bd _ _ _ _))//
    mem_miditv.
Qed.

Lemma neitv_sorted_disj_trivIset h (t : seq (interval R)) :
  all neitv t -> sorted le_itv (h :: t) -> path disjoint_itv h t ->
  trivIset setT (fun i => [set` nth 0%O (h :: t) i]).
Proof.
elim: t h => //= [h t0 _ _|
                 b t ih a /andP[b0 t0] /andP[lt_ab lt_bt] /andP[dis_ab dis_bt]].
  apply/trivIsetP => i j _ _ ij.
  case: i => [|i] /= in ij *.
    case: j => [|j] //= in ij *.
    by rewrite nth_nil set_itvE setI0.
  by rewrite nth_nil set_itvE set0I.
apply/trivIsetP => i j _ _; move: i j => [|i] [|j] //= ?.
- have [jbt|btj] := ltP j (size (b :: t)).
    apply/eqP/(@neitv_sorted_disj _ (b :: t)) => //=;
      by [rewrite b0|rewrite lt_ab|rewrite dis_ab|rewrite mem_nth].
  by rewrite nth_default // set_itvE setI0.
- have [ibt|bti] := ltP i (size (b :: t)).
    rewrite setIC.
    apply/eqP/(@neitv_sorted_disj _ (b :: t)) => //=;
      by [rewrite b0|rewrite lt_ab|rewrite dis_ab|rewrite mem_nth].
  by rewrite nth_default // set_itvE set0I.
- by have /trivIsetP := ih b t0 lt_bt dis_bt; apply.
Qed.

Lemma trivIset_disj_itv h (t : seq (interval R)) :
  trivIset setT (fun i => [set` nth 0%O (h :: t) i]) ->
  path disjoint_itv h t.
Proof.
elim: t h => // t1 t2 ih h /= /trivIsetP tsht1t2.
apply/andP; split.
  by move: (tsht1t2 O 1%N Logic.I Logic.I erefl) => /= /eqP.
apply ih => //; apply/trivIsetP => i j _ _ ij.
by move: (tsht1t2 i.+1 j.+1 Logic.I Logic.I); apply.
Qed.

Lemma sorted_le_itv_bound (s : seq (interval R)) :
  all neitv s -> sorted le_itv s -> path disjoint_itv (head 0%O s) (behead s) ->
  sorted <=%O (map bnd2eta s) /\ sorted <=%O (map bnd1eta s).
Proof.
elim: s => // -[h1 h2] [//|[t11 t12] t2] ih /= ne ht Hdis; split.
  apply/andP; split.
    case/andP : ht => + _.
    move/orP => -[/eqP[_ <-]//|].
    rewrite /lt_itv /=; case: ltgtP => //= [|_ /ltW] // h11t11 _.
    move/andP : Hdis => [H _].
    rewrite leNgt; apply/negP => t12h2.
    move: H; apply/negP/set0P.
    have : neitv (Interval t11 t12) by move/and3P : ne => [_].
    move=> /set0P[x t11t12x].
    exists x; split => //=.
    rewrite itv_boundlr.
    move: t11t12x; rewrite /= itv_boundlr => /andP[t11x xt12].
    by rewrite (le_trans (ltW _) t11x) // (le_trans xt12) // ltW.
  apply: (proj1 (ih _ _ _)).
  - by move/andP : ne => [].
  - by case/andP : ht => ? ht.
  - by rewrite /=; move/andP : Hdis => // -[].
apply/andP; split.
- move/andP : ht => -[] /orP[/eqP[<-//]|].
  by rewrite /lt_itv /=; case: ltgtP.
- apply: (proj2 (ih _ _ _)).
  + by move/andP : ne => [].
  + by case/andP : ht.
  + by rewrite /=; move/andP : Hdis => // -[].
Qed.

End lt_itv_disjoint.

Section decomposition.
Variable R : realType.
Implicit Types (i j : interval R) (s t : seq (interval R)).

Program Definition decompose' s
    (f : forall t, (size t < size s)%N -> seq (interval R)) :=
  match s with
  | [::] => [::] | [:: i] => [:: i]
  | [:: i, j & tl] => if (i <= j)%O then f (j :: tl) _ else
                    if (j <= i)%O then f (i :: tl) _ else
                    itv_diff i j :: f (j :: tl) _
  end.
Next Obligation. by move=> s _ i j tl <-. Qed.
Next Obligation. by move=> s _ i j tl <-. Qed.
Next Obligation. by move=> s _ i j tl <-. Qed.

Lemma decompose'_ext s
  (f g : forall t, (size t < size s)%N -> seq (interval R)) :
    (forall t (h : (size t < size s)%N), f t h = g t h) ->
  decompose' f = decompose' g.
Proof.
move=> fg; congr decompose'.
by apply functional_extensionality_dep => ?; apply functional_extensionality_dep.
Qed.

Lemma wf_size : well_founded (fun t s => (size t < size s)%N).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => s t /ssrnat.ltP. Qed.

Definition sorted_decompose : seq (interval R) -> seq (interval R) :=
  Fix wf_size (fun _ => _ _) decompose'.

Lemma sorted_decompose_nil : sorted_decompose [::] = [::].
Proof. by rewrite /sorted_decompose Fix_eq //=; exact decompose'_ext. Qed.

Lemma sorted_decompose_one i : sorted_decompose [:: i] = [:: i].
Proof. rewrite /sorted_decompose Fix_eq //=; exact: decompose'_ext. Qed.

Lemma sorted_decompose_two i j t : sorted_decompose [:: i, j & t] =
  if (i <= j)%O then sorted_decompose (j :: t) else
  if (j <= i)%O then sorted_decompose (i :: t) else
  itv_diff i j :: sorted_decompose (j :: t).
Proof.
rewrite {1}/sorted_decompose Fix_eq; last exact: decompose'_ext.
by move: i j => [? ?] [? ?] //=; case: ifPn => //; case: ifPn.
Qed.

Lemma sorted_decompose_eq0 s : (sorted_decompose s == [::]) = (s == [::]).
Proof.
apply/idP/idP => [/eqP //|/eqP ->]; last by rewrite sorted_decompose_nil.
move Hn : (size s) => n.
elim: n s Hn => [[]//|n ih [//|i [|j t] [tn]]].
  by rewrite sorted_decompose_one.
rewrite sorted_decompose_two; case: ifPn => [_ /ih|ij].
  by move=> /(_ tn).
by case: ifPn => // ji /ih => /(_ tn).
Qed.

Lemma cover_sorted_decompose s :
  sorted le_itv s -> [sset of sorted_decompose s] = [sset of s].
Proof.
move sn : (size s) => n; elim: n s sn => [|n ih [//|i [|j t]]].
  by case=> // _ _; rewrite sorted_decompose_nil.
  by move=> _ _; rewrite sorted_decompose_one.
move=> [tn] /= /andP[le_ij le_jt]; rewrite sorted_decompose_two.
  case: ifPn => ij.
  rewrite /= ih // 3!sset_cons setUA; congr setU.
  by rewrite setUC; apply/esym/setUidPl/subitvP.
case: ifPn => ji.
  rewrite /= ih //; last first.
    by rewrite (mask_second j) (sorted_mask le_itv_trans) //= le_ij.
  by rewrite 3!sset_cons setUA; congr setU; apply/esym/setUidPl/subitvP.
rewrite (sset_cons _ (sorted_decompose (j :: t))) ih //.
rewrite [in RHS]sset_cons sset_cons !setUA; congr (_ `|` _).
rewrite set_itv_diff // ?ji// eqEsubset; split.
- by move=> k [[]|]; [left|right].
- move=> x [ix|jx] /=; last by right.
  by case: (x \in j) => //=; [right|left].
Qed.

Let neitv_diff i j :
  neitv i -> neitv j -> ~~ (i <= j)%O -> ~~ (j <= i)%O ->
  neitv (itv_diff i j).
Proof.
move: i j => [a b] [c d]; rewrite !neitvE /itv_diff !itv_leEmeet /= => ab cd.
rewrite neitvE /=.
rewrite -leNgt; case: ifPn => //=; rewrite -ltNge; case: (leP c a) => ca.
  rewrite ltxI ab /= => ad; case: (leP d b) => db /=; last by rewrite eqxx.
  by  rewrite lt_neqAle db andbT => + _; apply: contra => /eqP ->.
by rewrite ltxI cd andbT; case: (leP d b) => //=; rewrite eqxx.
Qed.

Lemma sorted_decompose_nonempty s : all neitv s -> all neitv (sorted_decompose s).
Proof.
move sn : (size s) => n; elim: n s sn => [|n ih [//|i [|j t]] ].
  by move=> s /size0nil ->{} _; rewrite sorted_decompose_nil.
  by move=> _ i0; rewrite sorted_decompose_one.
move=> [tn] /= /and3P[i0 j0 ne]; rewrite sorted_decompose_two.
case: ifPn => ij; first by rewrite ih //= ne andbT.
case: ifPn => ji; first by rewrite ih //= ne andbT.
apply/allP => k; rewrite inE => /orP[/eqP ->|]; first exact: neitv_diff.
by move: k; apply/allP; rewrite ih //= ne andbT.
Qed.

Let sorted_disj_itv i j t (ijt : sorted le_itv [:: i, j & t])
  (ij : ~~ (i <= j)%O) (ji : ~~ (j <= i)%O) :
  forall j0, j0 \in j :: t -> disjoint_itv (itv_diff i j) j0.
Proof.
move=> c cjtl.
apply/eqP; rewrite set_itv_diff ?ji//.
move: cjtl; rewrite inE => /orP[/eqP ->|ctl].
  by rewrite setDE -setIA setICl setI0.
rewrite predeqE => x; split => // -[].
rewrite setDE => -[] ix/negP jx cx.
have jc : le_itv j c.
  move: ctl; rewrite -sub1seq.
  move/subseq_path_in => /(_ le_itv j) /=; rewrite andbT; apply => //.
    by move=> ? ? ? ? ? ?; exact: le_itv_trans.
  by move: ijt => /= /andP[].
have le_ij : le_itv i j by move: ijt; rewrite /= => /andP[].
move/negP in ji; apply: ji.
have [|//] := le_itv_subset ix cx jx le_ij jc.
by rewrite (negbTE ij).
Qed.

Lemma path_disj_itv_sorted_decompose s : sorted le_itv s ->
  forall i, (forall j, j \in s -> disjoint_itv i j) ->
  path disjoint_itv i (sorted_decompose s).
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j t]] []].
  by move=> _ /size0nil ->{} _ t tc; rewrite sorted_decompose_nil.
  by move=> _ _ t tc; rewrite sorted_decompose_one /= tc ?mem_head // eqxx.
case: n => [//|n] in ih * => -[] tn ijt k disj_k.
rewrite sorted_decompose_two; case: ifPn => ij.
  rewrite ih //= ?tn//; first by case/andP : ijt.
  by move=> c cjt; rewrite disj_k // inE cjt orbT.
case: ifPn => // ji.
  rewrite ih//; first by rewrite /= tn.
    by rewrite (mask_second j) (sorted_mask le_itv_trans).
  by move=> c; rewrite inE => citl; rewrite disj_k // !inE orbCA citl orbT.
rewrite /=; apply/andP; split.
  apply/eqP; rewrite set_itv_diff ?ji// setDE setIA.
  by rewrite (eqP (disj_k _ _)) ?set0I // mem_head.
rewrite ih //; first by rewrite /= tn.
  exact/(subseq_sorted le_itv_trans _ ijt)/subseq_cons.
exact: sorted_disj_itv.
Qed.

Lemma path_disj_itv_sorted_decompose_head_behead s : sorted le_itv s ->
  path disjoint_itv (head 0%O (sorted_decompose s))
                    (behead (sorted_decompose s)).
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j t]] []].
  by move=> _ /size0nil ->{} _; rewrite sorted_decompose_nil.
  by move=> ic _; rewrite sorted_decompose_one /=.
case: n => [//|n] in ih *=> -[] tn ijt.
rewrite sorted_decompose_two; case: ifPn => ij.
  by rewrite ih//; [rewrite /= tn | case/andP : ijt].
case: ifPn => // ji.
  rewrite ih //; first by rewrite /= tn.
  by rewrite (mask_second j) (sorted_mask le_itv_trans).
rewrite /= path_disj_itv_sorted_decompose //; first by move: ijt => /= /andP[].
exact: sorted_disj_itv.
Qed.

Lemma all_sorted_decompose s y : sorted le_itv s ->
  all (fun x => le_itv y x && disjoint_itv y x) s ->
  all (fun x => le_itv y x && disjoint_itv y x) (sorted_decompose s).
Proof.
move: y.
have [n] := ubnP (size s); elim: n s => // n ih.
case; first by move=> _ k _ _; rewrite sorted_decompose_nil.
move=> i [|j t]; first by move=> m k _; rewrite sorted_decompose_one /= andbT.
move=> /=; rewrite ltnS => tn y /andP[le_ij le_jt].
move=> /and3P[/andP[yi iy] /andP[yj jy] yt'].
rewrite sorted_decompose_two; case: ifPn => [ij|ij].
  apply ih => //; apply/allP => z.
  rewrite inE => /orP[/eqP -> //| zt]; rewrite ?yj//.
  by move/allP : yt'; apply.
case: ifPn => ji.
  apply ih => //.
  - by rewrite (mask_second j) (sorted_mask le_itv_trans) //= le_ij.
  - apply/allP => z; rewrite inE => /orP[/eqP -> //|zt]; rewrite ?yi//.
    by move/allP : yt' ; apply.
apply/allP => z; rewrite inE => /orP[/eqP ->{z}|zbt]; last first.
  have : all (fun x => le_itv y x && (disjoint_itv y x))
             (sorted_decompose (j :: t)).
    apply ih => //; apply/allP => u.
    rewrite inE => /orP[/eqP -> //|ut]; rewrite ?yj//.
      by move/allP : yt'; apply.
    by move/allP; apply.
rewrite le_itv_itv_diff //= /disjoint_itv set_itv_diff ?ji//.
apply/eqP; apply: (@subsetI_eq0 _ _ [set` y] _ [set` i]) => //.
- by move=> x [].
- exact/eqP.
Qed.

Lemma sorted_sorted_decompose s : sorted le_itv s ->
  sorted le_itv (sorted_decompose s).
Proof.
have [n] := ubnP (size s); elim: n s => // n ih.
case; first by move=> _ _; rewrite sorted_decompose_nil.
move=> a [|b t]; first by move=> _ _; rewrite sorted_decompose_one.
rewrite ltnS => abtn abt.
rewrite sorted_decompose_two.
case: ifPn => ab.
  apply ih => //.
  by move: abt => /= /andP[].
case: ifPn => [ba|ba/=].
  by rewrite ih // (mask_second b) (sorted_mask le_itv_trans).
have bt : sorted le_itv (sorted_decompose (b :: t)).
  by apply ih => //; move: abt => /= /andP[].
rewrite path_min_sorted //.
have bt' : sorted le_itv (b :: t).
  by move: abt => /= /andP[].
have : all (fun x => le_itv (itv_diff a b) x && (disjoint_itv (itv_diff a b) x))
           (b :: t).
  rewrite /= le_itv_diff //=; last first.
    by move: abt => /= => /andP[].
  apply/andP; split.
    by apply/eqP; rewrite set_itv_diff ?ba// setDE -setIA setICl setI0.
  apply/allP => z zt.
  apply/andP; split.
    rewrite (@le_itv_trans _ b) //.
      apply le_itv_diff => //.
      by move: abt => /= /andP[].
    move: abt => /= /andP[_ bt''].
    by move/order_path_min : bt'' => /(_ le_itv_trans) /allP; apply.
  rewrite /disjoint_itv set_itv_diff ?ba//.
  apply/negPn/negP => /set0P[x] -[[] ].
  move=> xa bx zx.
  move: a b z => [a1 a2] [b1 b2] [z1 z2] in zt zx abtn abt ab ba bt bt' bx xa *.
  apply: bx => /=.
  rewrite /= !itv_boundlr in xa zx *.
  case/andP : zx => zx1 zx2.
  rewrite (le_trans _ zx1) //=; last first.
     have : le_itv (Interval b1 b2) (Interval z1 z2).
       have : path le_itv (Interval b1 b2) t by [].
       by move/order_path_min => /(_ le_itv_trans)/allP; apply.
     by rewrite /le_itv /lt_itv /= => /orP[/eqP[ <- //]|/=]; case: ltgtP.
   rewrite leNgt; apply/negP => b2x.
   case/andP : xa => xa1 xa2.
   move/negP : ba; apply.
   rewrite itv_leEmeet/= meet_l; last by rewrite (le_trans (ltW b2x)).
   rewrite join_l//.
   move: abt; rewrite /= /le_itv => /andP[/orP[/eqP[<- //]| /=]].
   by rewrite /lt_itv /=; case: ltgtP.
move/(@all_sorted_decompose (b :: t) (itv_diff a b) bt').
by apply: sub_all => z /andP[].
Qed.

Lemma trivIset_sorted_decompose s : sorted le_itv s -> all neitv s ->
  trivIset setT (fun k => [set` nth 0%O (sorted_decompose s) k]).
Proof.
move=> sorteds sne.
have [/size0nil -> |] := eqVneq (size (sorted_decompose s)) 0%N.
  by apply/trivIsetP => /= i j _ _ ij; rewrite nth_nil setitv0 set0I.
rewrite size_eq0 => s0.
rewrite -(cons_head_beheadE 0%O s0); apply: neitv_sorted_disj_trivIset.
- have := sorted_decompose_nonempty sne.
  by rewrite -(cons_head_beheadE 0%O s0) /= => /andP[].
- by rewrite cons_head_beheadE// sorted_sorted_decompose.
- suff: path disjoint_itv 0%O
      (head 0%O (sorted_decompose s) :: behead (sorted_decompose s)).
    by move => /andP[].
  rewrite cons_head_beheadE// path_disj_itv_sorted_decompose => // i si.
  by apply/eqP; rewrite setitv0 set0I.
Qed.

Definition decompose s := sorted_decompose (sort le_itv [seq x <- s | neitv x]).

Lemma decompose_set0 (s : seq (interval R)) :
  [sset of s] = set0 -> forall i, i \in decompose s -> [set` i] = set0.
Proof.
move=> s0 i si; rewrite predeqE => x; split => // xi.
have : [sset of decompose s] = [sset of s].
  rewrite /decompose cover_sorted_decompose.
    by rewrite sset_sort_le_itv sset_filter_neitv.
  exact: (sort_sorted total_le_itv).
by rewrite s0 =>/eqP; apply/negP/set0P; exists x; rewrite sset_bigcup; exists i.
Qed.

Lemma itv_cplt_decomposeE s :
  [sset of itv_cplt_ne (decompose s)] = ~` [sset of s].
Proof.
have [sne ssorted sdisj] : [/\ all neitv (decompose s),
    sorted le_itv (decompose s) &
    path disjoint_itv (head 0%O (decompose s)) (behead (decompose s))].
  split.
  - rewrite sorted_decompose_nonempty // all_sort; apply/allP => i.
    by rewrite mem_filter => /andP[].
  - exact/sorted_sorted_decompose/(sort_sorted total_le_itv).
  - apply/path_disj_itv_sorted_decompose_head_behead.
    exact/(sort_sorted total_le_itv).
have [sdec1 sdec2] := sorted_le_itv_bound sne ssorted sdisj(*TODO*).
rewrite itv_cplt_neE // cover_sorted_decompose.
  by rewrite sset_sort_le_itv // sset_filter_neitv.
exact: (sort_sorted total_le_itv).
Qed.

Definition is_decomposition s : seq (interval R) -> Prop :=
  fun x => [/\ sorted le_itv x,
           path disjoint_itv (head 0%O x) (behead x) &
           [sset of x] = [sset of s] ].

Lemma is_decomposition_decompose s : is_decomposition s (decompose s).
Proof.
split.
- exact/sorted_sorted_decompose/(sort_sorted total_le_itv).
- apply: path_disj_itv_sorted_decompose_head_behead.
  exact/(sort_sorted total_le_itv).
- rewrite (cover_sorted_decompose (sort_sorted total_le_itv _)).
  by rewrite sset_sort_le_itv sset_filter_neitv.
Qed.

Lemma mem_decompose (j : interval R) s (r : R) : j \in s -> [set` j] r ->
  exists j', j' \in decompose s /\ [set` j'] r.
Proof.
move=> js jr.
have : [sset of s] r by rewrite sset_bigcup; exists j.
have [_ _] := is_decomposition_decompose s.
by move=> <-; rewrite sset_bigcup => -[j' sj' j'r]; exists j'.
Qed.

Lemma trivIset_decompose s :
  trivIset setT (fun k => [set` nth 0%O (decompose s) k]).
Proof.
have [->|s0] := eqVneq (decompose s) [::].
  by apply/trivIsetP => i j _ _ ?; rewrite nth_nil set_itvE set0I.
rewrite -(cons_head_beheadE 0%O s0); apply: neitv_sorted_disj_trivIset.
- apply/allP => /= j /mem_behead; rewrite /decompose.
  set s' := sort _ _.
  have /sorted_decompose_nonempty/allP sne : all neitv s'.
    by rewrite all_sort all_filter; apply/allP => i ia /=; exact: implybb.
  by move/sne.
- by rewrite cons_head_beheadE //; have [] := is_decomposition_decompose s.
- by have [] := is_decomposition_decompose s.
Qed.

Lemma decompose_nonempty s : all neitv (decompose s).
Proof.
rewrite /decompose; apply/sorted_decompose_nonempty.
by rewrite all_sort; apply/allP => i; rewrite mem_filter => /andP[].
Qed.

Lemma decompose_nil : decompose [::] = [::].
Proof. by rewrite /decompose /= sortE /= sorted_decompose_nil. Qed.

End decomposition.
Arguments decompose {R}.


Module Sset.
Section is_sset.
Variable R : realType.
Implicit Types A B : set R.

Definition is_sset A : Prop := exists s, A = [sset of s].

Lemma is_sset0 : is_sset set0. Proof. by exists fset0; rewrite sset_nil. Qed.

Lemma is_ssetU A B : is_sset A -> is_sset B -> is_sset (A `|` B).
Proof.
move=> [a aA] [b bB]; exists (a ++ b)%fset.
rewrite eqEsubset; split => [r [Ar|Br]|r].
  move: Ar; rewrite aA => /ssetP[/= j ja jr].
  by apply/ssetP; exists j => //; rewrite /mkset mem_cat ja.
  move: Br; rewrite bB => /ssetP[/= j jb jr].
  by apply/ssetP; exists j => //; rewrite /mkset mem_cat jb orbT.
move/ssetP => [j]; rewrite /mkset mem_cat => /orP[ja|jb] jr.
by left; rewrite aA; apply/ssetP; exists j.
by right; rewrite bB; apply/ssetP; exists j.
Qed.

Lemma is_ssetC A : is_sset A -> is_sset (~` A).
Proof.
move=> [a aA]; set s := itv_cplt_ne (decompose a).
exists [fset x | x in s]%fset; rewrite (@sseti _ _ s).
  by rewrite itv_cplt_decomposeE aA.
by move=> i; rewrite inE.
Qed.

End is_sset.

Section algebra_of_sets_instance.
Variable R : realType.

HB.instance Definition sset_algebraOfSets :=
  @isAlgebraOfSets.Build (Real.sort R) (Pointed.class R) (@is_sset R)
  (@is_sset0 R) (@is_ssetU R) (@is_ssetC R).

Definition sset_algebraOfSetsType := [the algebraOfSetsType of (Real.sort R)].

Lemma is_sset_itv (i : interval R) : is_sset [set` i].
Proof. by exists [:: i]; rewrite sset_cons1. Qed.

Lemma is_sset_sset (s : seq (interval R)) : is_sset [sset of s].
Proof. by  exists s. Qed.

End algebra_of_sets_instance.
End Sset.
Notation sset_algebraOfSetsType := Sset.sset_algebraOfSetsType.

Section le_disj_itv.
Variable R : realType.
Implicit Types i j : interval R.

Lemma le_itv_disj_bnd2_bnd1 i j : neitv i -> neitv j -> le_itv i j ->
  disjoint_itv i j -> (i.2 <= j.1)%O.
Proof.
move=> i0 j0 le_ij dis_ij; rewrite leNgt; apply/negP => j1i2.
move: (dis_ij); apply/negP.
move: (le_ij) => /predU1P[<-|lt_ij]; first by rewrite disjoint_itvxx.
rewrite /disjoint_itv/disj_set -set_itv_meet (IntervalE i) (IntervalE j).
have : (i.1 <= j.1)%O by exact: le_itv_bnd1.
rewrite /lt_itv le_eqVlt => /predU1P[i1j1|i1j1] /=.
  move: lt_ij; rewrite /lt_itv {}i1j1 ltxx eqxx/= => {}i2j2.
  by apply/neitvP => /=; rewrite join_l// meet_l//; exact/ltW.
by rewrite (join_r (ltW i1j1)) meet_l//; [exact/neitvP|exact: le_itv_bnd2].
Qed.

Let le_itv_disj_bndNinfty i j : neitv i -> neitv j -> le_itv i j ->
  disjoint_itv i j -> j.1 != -oo%O /\ i.2 != +oo%O.
Proof.
move=> i0 j0 ij disj_ij.
have i2j1 := le_itv_disj_bnd2_bnd1 i0 j0 ij disj_ij.
split; apply: contraTN i2j1 => /eqP ->.
- by move/neitvP: i0; rewrite -ltNge; exact: le_lt_trans.
- by move/neitvP: j0; rewrite -ltNge => /lt_le_trans; apply; rewrite bound_lex1.
Qed.

Lemma le_itv_disj_bnd2r i j : neitv i -> neitv j -> le_itv i j ->
  disjoint_itv i j -> exists b r, i.2 = BSide b r.
Proof.
move=> i0 j0 les ts.
move i2E : (i.2) => i2; case: i2 => [b i2|[]] in i2E *; first by exists b, i2.
- have := @neitv_bnd2 _ [:: i]; rewrite all_seq1 => /(_ i0 i).
  by rewrite mem_seq1 eqxx => /(_ isT); rewrite i2E eqxx.
- have [] := le_itv_disj_bndNinfty i0 j0 les ts.
  by rewrite i2E.
Qed.

Lemma le_itv_disj_bnd1r i j : neitv i -> neitv j -> le_itv i j ->
  disjoint_itv i j -> exists b a, j.1 = BSide b a.
Proof.
move=> i0 j0 sle str.
move i1E : (j.1) => i1; case: i1 => [b i1|[]] in i1E *; first by exists b, i1.
- have [] := le_itv_disj_bndNinfty i0 j0 sle str.
  by rewrite i1E.
- have := @neitv_bnd1 _ [:: j]; rewrite all_seq1 => /(_ j0 j).
  by rewrite mem_seq1 eqxx => /(_ isT); rewrite i1E eqxx.
Qed.

Lemma le_itv_disj_contiguous i j : neitv i -> neitv j -> le_itv i j ->
  disjoint_itv i j -> is_interval ([set` i] `|` [set` j]) -> contiguous_itv i j.
Proof.
move=> ine jne ij dij itvij.
rewrite /contiguous_itv eq_le le_itv_disj_bnd2_bnd1//=.
have [b [x bx]] := le_itv_disj_bnd2r ine jne ij dij.
have [c [y cy]] := le_itv_disj_bnd1r ine jne ij dij.
set m := (x + y) / 2.
rewrite leNgt bx cy; apply/negP => xy.
have xyW : x <= y.
  by move: b c {cy bx} xy => [] [] /=; rewrite lte_bnd // => /ltW.
have xys : Interval (BSide b x) (BSide c y) \in itv_cplt [:: i; j].
  rewrite /itv_cplt; apply/mapP; exists (BSide b x, BSide c y) => //.
  apply/(nthP (+oo%O, -oo%O)); exists 1%N; first by rewrite size_zip.
  by rewrite !nth_zip //= -bx -cy.
have : m \in [sset of itv_cplt [:: i; j]].
  rewrite sset_bigcup inE; exists (Interval (BSide b x) (BSide c y)) => //=.
  by rewrite /m -/(miditv (Interval (BSide b x) (BSide c y))) mem_miditv.
rewrite itv_cpltE /= ?andbT; [|exact: le_itv_bnd2|exact: le_itv_bnd1].
rewrite inE; apply; rewrite sset_cons sset_cons1.
set midi := miditv i; set midj := miditv j.
move: itvij => /(_ midi midj); apply.
- by left; rewrite /= mem_miditv //; exact/neitvP.
- by right; rewrite /= mem_miditv //; exact/neitvP.
- move/neitvP in ine; move/neitvP in jne.
  have := miditv_bnd2 ine b; rewrite bx BSide_leE -/midi => midix.
  have := miditv_bnd1 jne c; rewrite cy BSide_leE -/midj => midjy.
  by rewrite (le_trans midix) /= ?midf_le// (le_trans _ midjy) //= midf_le.
Qed.

End le_disj_itv.

Section hlength_setU.
Local Open Scope ereal_scope.
Variable R : realType.
Implicit Types (i j : interval R) (A B : set R).

Lemma Rhull_setU2 A B : B !=set0 -> A `&` B = set0 ->
  is_interval A -> is_interval B -> lt_itv (Rhull A) (Rhull B) ->
  (Rhull (A `|` B)).2 = (Rhull B).2.
Proof.
move=> B0 AB0 iA iB AB /=.
have [|] := asboolP (has_ubound (A `|` B)) => uAB; last first.
  rewrite asboolF //; apply: contra_not uAB => -[x Bx].
  exists x => z [Az|Bz]; last exact: Bx.
  case: B0 => b0 Bb0; rewrite (@le_trans _ _ b0) //; last exact: Bx.
  apply/ltW/(lt_itv_lt AB) => //; [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
have uB : has_ubound B.
  by case: uAB => x ABx; exists x => y By; apply ABx; right.
rewrite (asboolT uB) // sup_setU //; last first.
  move=> a b Aa Bb.
  apply/ltW/(lt_itv_lt AB) => //; [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
congr (BSide (~~ `[< _ >]) _).
rewrite propeqE; split; last by right.
case => // AsB.
exfalso; move/set0P : B0 => /negP; apply; apply/eqP.
rewrite predeqE => x; split => // Bx.
have : (sup B < x)%R.
  apply: (lt_itv_lt AB) => //; [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
by apply/negP; rewrite -leNgt; exact: sup_ub.
Qed.

Lemma Rhull_setU1 A B : A !=set0 -> A `&` B = set0 ->
  is_interval A -> is_interval B -> lt_itv (Rhull A) (Rhull B) ->
  (Rhull (A `|` B)).1 = (Rhull A).1.
Proof.
move=> A0 AB0 iA iB AB /=.
have [|] := asboolP (has_lbound (A `|` B)) => uAB; last first.
  rewrite asboolF //.
  apply: contra_not uAB => -[x Ax].
  exists x => y [Ay|By]; first exact: Ax.
  case: A0 => a0 Aa0.
  rewrite (@le_trans _ _ a0) //; first exact: Ax.
  apply/ltW/(lt_itv_lt AB); [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
have lA : has_lbound A.
  case: uAB => x ABx.
  by exists x => y Ay; apply ABx; left.
rewrite (asboolT lA) // inf_setU //; last first.
  move=> a b Aa Bb.
  apply/ltW/(lt_itv_lt AB) => //; [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
congr (BSide (`[< _ >]) _).
rewrite propeqE; split; last by left.
case => // AsB.
exfalso; move: A0 => [a0 A0].
have : (a0 < inf A)%R.
  apply: (lt_itv_lt AB) => //; [|exact: sub_Rhull|exact: sub_Rhull].
  by rewrite disj_itv_Rhull.
by apply/negP; rewrite -leNgt; apply inf_lb.
Qed.

Lemma hlength_itvU A B : A `&` B = set0 -> is_interval A -> is_interval B ->
  is_interval (A `|` B) -> hlength (A `|` B) = hlength A + hlength B.
Proof.
move=> AB0 iA iB iAUB.
have [->|/set0P A0] := eqVneq A set0; first by rewrite set0U hlength0 add0e.
have [->|/set0P B0] := eqVneq B set0; first by rewrite setU0 hlength0 adde0.
wlog : A B A0 B0 AB0 iA iB iAUB / lt_itv (Rhull A) (Rhull B).
  move=> H; have [AB|AB] := eqVneq (Rhull A) (Rhull B).
      move/(congr1 (fun i => [set` i])) : AB AB0.
      rewrite RhullK ?inE// RhullK ?inE// => ->.
      by rewrite setIid => /eqP; move/set0P : B0 => /negbTE ->.
  have /orP[|] := total_le_itv (Rhull A) (Rhull B).
    by rewrite /le_itv (negbTE AB) orFb; exact: H.
  rewrite /le_itv eq_sym (negbTE AB) orFb => {}AB.
  by rewrite setUC H // 1?addeC// 1?setIC// 1?setU // setUC.
move=> AB.
have : contiguous_itv (Rhull A) (Rhull B).
  apply le_itv_disj_contiguous => //; do 1?
    [by apply/set0P; rewrite RhullK// ?inE].
  by rewrite ltW_itv.
  by rewrite disj_itv_Rhull.
  by rewrite RhullK ?inE// RhullK ?inE.
rewrite /contiguous_itv => /eqP A2B1.
rewrite /hlength A2B1 Rhull_setU2// Rhull_setU1// [in RHS]addeC ![in RHS]addeA.
congr (_ - _)%E; rewrite subeK //.
case: (Rhull B).1 => [b b1|[]] // in A2B1 *.
- exfalso; move/set0P : A0 => /negP; apply; rewrite -(@RhullK _ A) ?inE //.
  by apply/eqP/neitvP/negP; rewrite A2B1 -leNgt.
- suff: exists b r, (Rhull A).2 = BSide b r.
    by move=> [b [r Abr]]; rewrite -A2B1 Abr.
  apply: (@le_itv_disj_bnd2r _ (Rhull A) (Rhull B)) => //; do 1?
    [by apply/set0P; rewrite RhullK// ?inE].
  + exact/ltW_itv.
  + by rewrite disj_itv_Rhull.
Qed.

Lemma hlengthUitv (A : set R) (s : seq (interval R)) :
  is_interval A ->
  cover setT (fun n => [set` nth 0%O s n]) = A ->
  trivIset setT (fun n => [set` nth 0%O s n]) ->
  hlength A = \sum_(i <- s) hlength [set` i].
Proof.
move=> Aitv AE ts.
have Fmap (s' : seq (interval R)) :
    (fun n => [set` nth 0%O s' n]) =
      (fun n => nth 0%O [seq [set` j] | j <- s'] n).
  apply/funext => i; have [is'|is'] := ltnP i (size s').
    by rewrite (nth_map 0%O).
  by rewrite !nth_default ?size_map// set_itvE.
wlog : s ts AE / sorted le_itv s => [hwlog|].
  have /permPl pss := perm_sort le_itv s.
  rewrite -(perm_big _ pss); apply: hwlog; [exact: trivIset_sort|
    by rewrite -cover_set_itv_nth_sort|exact: (sort_sorted total_le_itv)].
elim: (s : seq _) => [|j {}s IHs]/= in A Aitv ts AE *.
  rewrite /cover bigcup0 in AE; last by move=> i _; rewrite nth_nil set_itvE.
  by rewrite !big_nil/= in AE * => _; rewrite -AE hlength0.
rewrite (path_sortedE le_itv_trans) => /andP[/allP/= j_small s_sorted].
set K := \big[setU/set0]_(j <- s) [set` j].
have K_itv : is_interval K.
  move=> x z Kx Kz y /andP[xy yz].
  have: A y.
    apply: (Aitv x z); rewrite ?xy//;
      by rewrite -AE cover_set_itv_nthE// big_cons; right.
  rewrite -AE /= cover_set_itv_nthE// big_cons=> -[]//.
  move=> jy; move: Kx; rewrite /K.
  rewrite -bigcup_set => -[k/= ks kx].
  suff: (x > y)%R by case: ltgtP xy.
  apply: (le_itv_lt (j_small k ks)) => //.
  have /(nthP 0%O)[ik ik_small <-] := ks.
  rewrite /disjoint_itv; apply/eqP.
  by have /trivIsetP-/(_ 0%N ik.+1 I I isT) := ts.
transitivity (hlength [set` j] + hlength K); last first.
  rewrite big_cons; congr (_ + _)%E; rewrite IHs// ?cover_set_itv_nthE//.
  by move=> i0 i1 _ _ /(ts i0.+1 i1.+1 I I)[].
rewrite -AE cover_set_itv_nthE// big_cons /= hlength_itvU//.
- rewrite big_distrr/= big1_seq => //= i /(nthP 0%O)[ii ii_lt <-].
  by apply: contraTeq isT => /set0P-/(ts 0%N ii.+1 I I).
- exact: interval_is_interval.
- by move: AE; rewrite cover_set_itv_nthE// big_cons => ->.
Qed.

Lemma cover_hlength_set_itv (I J : seq (interval R)) :
  cover setT (fun n => [set` nth 0%O I n]) =
    cover setT (fun n => [set` nth 0%O J n]) ->
  trivIset setT (fun n => [set` nth 0%O J n]) ->
  forall i, i \in I ->
  hlength [set` i] = \sum_(j <- J) hlength [set` itv_meet i j].
Proof.
move=> IJ tJ i iI.
have h : [set` i] = \big[setU/set0]_(j <- J) ([set` i] `&` [set` j]).
  rewrite -big_distrr /= (big_nth 0%O) big_mkord.
  move/esym: (IJ).
  rewrite -(@cover_restr _ _ _ [set k | (k < size J)%N]) //; last first.
    by move=> k _ /negP; rewrite -leqNgt => Jk; rewrite nth_default // set_itvE.
  rewrite /cover bigcup_mkord => ->; apply/esym; rewrite setIidPl.
  move: iI => /(nthP 0%O)[k kI <-].
  exact: (@bigcup_sup _ _ k setT (fun n => [set` nth 0%O I n])).
rewrite h (@hlengthUitv _ [seq (itv_meet i j) | j <- J]) // ?big_map//.
- by rewrite -h; apply: interval_is_interval.
- rewrite -(@cover_restr _ _ _ [set k | (k < size J)%N]) //; last first.
    move=> k _ /negP; rewrite -leqNgt => Jk.
    by rewrite nth_default ?size_map// set_itvE.
  rewrite /cover bigcup_mkord (big_nth 0%O) big_mkord.
  by apply eq_bigr => k _; rewrite (nth_map 0%O) // set_itv_meet.
- exact: trivIset_itv_meet.
Qed.

Lemma hlengthUset (I J : seq (interval R)) :
  cover setT (fun n => [set` nth 0%O I n]) =
    cover setT (fun n => [set` nth 0%O J n]) ->
  trivIset setT (fun n => [set` nth 0%O I n]) ->
  trivIset setT (fun n => [set` nth 0%O J n]) ->
  \sum_(i <- I) hlength [set` i] = \sum_(i <- J) hlength [set` i].
Proof.
move=> IJ tI tJ.
rewrite big_seq [RHS]big_seq.
(under eq_bigr) => [i /(cover_hlength_set_itv IJ tJ) ->|]; first over.
rewrite /= exchange_big /=; apply/esym.
(under eq_bigr) => [j /(cover_hlength_set_itv (esym IJ) tI) ->|]; first over.
rewrite -big_seq; apply eq_bigr => j _; rewrite -big_seq.
by under eq_bigr do rewrite itv_meetC.
Qed.

End hlength_setU.

Lemma le_sum_measure_bigcup (R : realType)
   (F : (set (sset_algebraOfSetsType R))^nat)
   (l : {additive_measure set (sset_algebraOfSetsType R) -> \bar R}) :
   (forall k, measurable (F k)) -> measurable (\bigcup_n F n) -> trivIset setT F
  -> forall n, (\sum_(k < n) l (F k) <= l (\bigcup_k F k))%E.
Proof.
move=> mS US tS n.
have : \big[setU/set0]_(i < n) F i `<=` \bigcup_i F i.
  by move=> /= r; rewrite -bigcup_set => -[/= k _ Skr]; exists k.
move: (@bigsetU_measurable _ _ (enum 'I_n) xpredT _ (fun k _ => mS k)).
rewrite [in X in X -> _]big_enum => mU /(le_measure l) /=.
rewrite !inE /=.
by move=> /(_ mU US); apply: le_trans; rewrite measure_bigsetU.
Qed.


Section slength_definition.
Variable R : realType.
Implicit Types i : interval R.

Definition slength (A : set R) : \bar R :=
  let s := xget [::] [set s | A = [sset of s] ] in
  \sum_(i <- decompose s) hlength [set` i].

Lemma slength_ge0 (X : set (sset_algebraOfSetsType R)) : (0 <= slength X)%E.
Proof.
rewrite /slength; case: xgetP => [/= x _ _|_]; last first.
  by rewrite decompose_nil big_nil.
by apply/sume_ge0 => i _; apply hlength_ge0.
Qed.

Lemma slength0 : slength set0 = 0%E.
Proof.
rewrite /slength; case: xgetP => [|_]; last by rewrite decompose_nil big_nil.
move=> /= x _ /esym/decompose_set0 x0; rewrite big_seq big1//.
by move=> i /x0 ->; rewrite hlength0.
Qed.

Lemma slength_itv i : slength ([set` i]) = hlength ([set` i]).
Proof.
have [->|i0] := eqVneq [set` i] set0.
  by rewrite slength0 hlength0.
rewrite /slength; case: xgetP => [/= s _ si|]; last first.
  by move=> /(_ [fset i]%fset) /=; rewrite ssetE big_seq_fset1.
rewrite -[RHS]/((hlength \o (fun i => [set` i])) i).
rewrite -[RHS](big_seq1 adde_monoid i).
apply: hlengthUset.
+ do 2 rewrite cover_set_itv_nthE//.
  move: (is_decomposition_decompose s) => [_ _ cover_s].
  by rewrite -!ssetE cover_s -si ssetE big_seq1.
+ apply: (trivIset_sorted_decompose (sort_sorted total_le_itv _)).
  by apply/allP => j; rewrite mem_sort /= mem_filter => /andP[].
+ apply/trivIsetP => -[|a] [|b] //=;
    by rewrite nth_nil set_itvE ?(setI0,set0I).
Qed.

End slength_definition.
Arguments slength {R}.
Arguments slength0 {R}.

Section addressing_sequence_of_simple_sets.
Variables (R : realType) (s : (seq (interval R))^nat).
Hypothesis s0 : forall n, size (s n) != O. (* no empty intervals *)

(* indirect address *)
Fixpoint indaddr (b p : nat) : nat * nat :=
  if p isn't p'.+1 then (b, O) else
    if (p'.+1 < size (s b))%N then (b, p'.+1) else
      indaddr b.+1 (p' - (size (s b)).-1)%N.

Lemma indaddrE b p : indaddr b p =
 if (p < size (s b))%N then (b, p) else indaddr b.+1 (p - size (s b))%N.
Proof.
case: p => [|p] /= in b *; first by rewrite lt0n s0.
case: ifPn => //; rewrite -leqNgt => sbp1.
by rewrite -{2}(@prednK (size (s b))) // lt0n.
Qed.

(* direct address *)
(* x.2 < size (s x.1) *)
Definition diraddr (x : nat * nat) := (\sum_(x < x.1) size (s x) + x.2)%N.

Lemma indaddrK (b p : nat) : (p < size (s b))%N ->
 diraddr (indaddr b p) = diraddr (b, p).
Proof.
elim: b p => [p s0p|b ih p psb1].
  by rewrite indaddrE s0p.
by rewrite indaddrE psb1.
Qed.

Lemma diraddrK (n p k : nat) : (p < size (s (n + k)))%N ->
  indaddr k (diraddr (n + k, p)%N - \sum_(i < k) size (s i)) = (n + k, p)%N.
Proof.
elim: n p k => [p k ps0|n ih p k psn1].
  by rewrite add0n {1}/diraddr (addnC _ p) addnK indaddrE ps0.
rewrite indaddrE ifF; last first.
  apply/negbTE.
  rewrite -leqNgt /diraddr (addnC _ p) (addnC _ k).
  rewrite -(big_mkord xpredT (size \o s)) /index_iota subn0 iotaD big_cat.
  rewrite -{2}(subn0 k) big_mkord add0n.
  rewrite [n.+1]lock /= -lock (addnC (\sum_(i < k) size (s i))%N) addnA addnK.
  by rewrite /= big_cons addnCA leq_addr.
rewrite {1}addSnnS.
rewrite (_ : _ - _ = diraddr (n + k.+1, p)%N - \sum_(i < k.+1) size (s i))%N.
  by rewrite ih ?addSnnS // -addSnnS.
by rewrite big_ord_recr /= subnDA.
Qed.

Definition nth_interval (n : nat) : interval R :=
  let: (b, k) := indaddr O n in nth 0%O (s b) k.

Lemma nth_interval_diraddr (n p : nat) : (p < size (s n))%N ->
  nth_interval (diraddr (n, p)) = nth 0%O (s n) p.
Proof.
move=> psn.
rewrite /nth_interval (_ : indaddr _ _ = (n, p)) //.
by move: (@diraddrK n p O); rewrite addn0 big_ord0 subn0 => ->.
Qed.

Lemma map_nth_interval (n : nat) :
  [seq nth_interval (diraddr (n, i)) | i <- iota 0 (size (s n))] = s n.
Proof.
apply(@eq_from_nth _ 0%O).
  by rewrite size_map size_iota.
move=> i; rewrite size_map size_iota => isn.
rewrite [in LHS](nth_map 0%O) ?size_iota// -[in RHS]nth_interval_diraddr //.
by rewrite nth_iota.
Qed.

Lemma map_nth_interval_diraddr n k : flatten [seq s i | i <- iota k n] =
  [seq nth_interval i | i <- iota (diraddr (k, O))
    (\sum_(x < (k + n)) size (s x) - \sum_(x < k) size (s x))].
Proof.
have [m nm] := ubnP n; elim: m => // m ih in n k nm *.
destruct n as [|n].
  by rewrite /= addn0 subnn.
rewrite /= ih //.
rewrite -map_nth_interval map_comp -map_cat; congr map.
rewrite {1}/diraddr [in LHS]/= -iotaDl.
rewrite -/(diraddr (k, O)) {2}/diraddr big_ord_recr /= addnAC -/(diraddr _).
rewrite -iotaD; congr iota.
rewrite addnC addSnnS subnDA subnK //.
have lem a b : (\sum_(i < a) size (s i) <= \sum_(x < a + b) size (s x))%N.
  rewrite -[X in (_ <= X)%N](big_mkord xpredT (fun x => size (s x))).
  rewrite /index_iota subn0 iotaD big_cat.
  by rewrite -[in X in (_ <= X)%N](subn0 a) -/(index_iota _ _) big_mkord leq_addr.
rewrite leq_subRL.
  by rewrite -(big_ord_recr k (size \o s)) /= -addSnnS lem.
by rewrite lem.
Qed.

Lemma flatten_map_nth_interval n :
  exists u, flatten [seq s i | i <- iota 0 n] =
       [seq nth_interval i | i <- iota 0 n] ++ u.
Proof.
exists [seq nth_interval i | i <- iota n (diraddr (n, O) - n)].
rewrite -map_cat -iotaD /diraddr addn0 (addnC n) subnK; last first.
  rewrite -{1}(muln1 n) -{1}(subn0 n) -sum_nat_const_nat big_mkord leq_sum //.
  by move=> a _; rewrite lt0n.
rewrite map_nth_interval_diraddr big_ord0 subn0 add0n /diraddr big_ord0 /=.
by rewrite addn0.
Qed.

End addressing_sequence_of_simple_sets.

Lemma bigcup_bigU_bigcup (R : realType) (f : (seq (interval R))^nat) :
  (forall n, size (f n) != O) ->
  \bigcup_k \big[setU/set0]_(i <- f k) [set` i] =
  \bigcup_k [set` nth_interval f k].
Proof.
move=> f0; rewrite eqEsubset; split => r.
  move=> -[n Hn]; rewrite -bigcup_set => -[/= I].
  move=> /(nthP 0%O)[p pn <-{I}] rnp.
  exists (diraddr f (n, p)) => //.
  by rewrite nth_interval_diraddr.
move=> [n _] ; rewrite /nth_interval.
move Hx : (indaddr _ _ _) => x.
destruct x as [x1 x2] => rx2.
exists x1 => //.
rewrite -bigcup_set.
exists (nth 0%O (f x1) x2) => //.
rewrite /mkset; apply/(nthP 0%O); exists x2 => //.
rewrite ltnNge; apply: contraPN rx2 => /(nth_default 0%O) -> /=.
by rewrite in_itv.
Qed.

Lemma sum_nth_interval_sum_sum (R : realType) (f : (seq (interval R))^nat)
  (l : set R -> \bar R) :
    (forall x, 0 <= l x)%E -> (forall n, size (f n) != O) ->
  (\sum_(k <oo) l [set` nth_interval f k] <=
   \sum_(k <oo) \sum_(x <- f k) l [set` x])%E.
Proof.
move=> l_ge0 f0; apply: lee_lim.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ _; apply: l_ge0.
- apply: is_cvg_ereal_nneg_natsum_cond => n _ _; apply: sume_ge0 => i _.
  exact: l_ge0.
- near=> n.
  rewrite 2!big_mkord.
  have -> : (\sum_(k < n) \sum_(x <- f k) l [set` x] =
            \sum_(k <- flatten (map f (iota 0 n))) l [set` k])%E.
    rewrite big_flatten /= big_map -[in RHS](subn0 n) -/(index_iota _ _).
    by rewrite big_mkord.
  have -> : (\sum_(k < n) l [set` nth_interval f k] =
            \sum_(k <- map (nth_interval f) (iota 0 n)) l [set` k])%E.
    by rewrite big_map -[in RHS](subn0 n) -/(index_iota _ _) big_mkord.
  have [s' ->] := flatten_map_nth_interval f0 n.
  rewrite big_cat /= lee_addl //.
  by apply: sume_ge0 => I _; apply: l_ge0.
Unshelve. all: by end_near. Qed.

Section slength_sigma_finite.
Variable R : realType.
Implicit Types (i : interval R) (n : nat).

Definition ccitv n : interval R := `[ (-(n%:R))%R, n%:R].

Lemma slength_ccitv n : slength [set` ccitv n] = n.*2%:R%:E.
Proof.
rewrite slength_itv hlength_itv /= lte_fin -{1}(add0r (-n%:R)) ltr_subl_addl.
rewrite -natrD ltr0n addnn double_gt0 lt0n; case: ifPn => [n0|/negPn/eqP->//].
by rewrite -addnn natrD 2!EFinN oppeK.
Qed.

Lemma slength_ccitv_sym b r n :
  slength ([set` Interval (BSide b r) +oo%O] `&` [set` ccitv n]) =
  slength ([set` Interval -oo%O (BSide b (- r))] `&` [set` ccitv n]).
Proof.
rewrite -2!set_itv_meet 2!slength_itv 2!hlength_itv /= 2!lte_fin; case: ifPn.
- rewrite ltUx => /andP[rn _]; case: ifPn.
  + rewrite ltxI => /andP[_ _]; congr (_%:E); rewrite opprK addrC.
    congr (_ + _)%R; rewrite joinEtotal meetEtotal /maxr /minr {rn}.
    have [rn|rn|rn] := ltgtP r (- n%:~R).
    * by rewrite ifF // ?opprK //; apply/negbTE; rewrite -leNgt -ler_oppr ltW.
    * by rewrite ifT // ltr_oppl.
    * by rewrite {2}rn opprK ltxx rn opprK.
   + rewrite ltxI negb_and -2!leNgt ler_oppl opprK (leNgt _ r) rn /=.
     rewrite -subr_le0 opprK -natrD lern0 addnn double_eq0 => /eqP n0.
     move: rn; rewrite {}n0 => r0; rewrite add0e mulr0n join_r ?opprK//.
     by rewrite oppr0 ltW.
- case: ifPn => //.
  rewrite ltxI => /andP[]; rewrite -ltr_oppl opprK => rn _.
  rewrite -leNgt lexU leNgt rn /= -subr_le0 opprK -natrD lern0 addnn double_eq0.
  move=> /eqP n0; move: rn.
  by rewrite {}n0 => r0; rewrite adde0 meet_r // ler_oppr mulr0n oppr0 ltW.
Qed.

Lemma slength_sigma_finite :
  sigma_finite setT (slength : set (sset_algebraOfSetsType R) -> \bar R).
Proof.
exists ((fun i => [set` i]) \o ccitv).
  rewrite predeqE => /= r; split => // _; have [r0|r0] := leP 0 r.
  - exists (absz (ceil r)) => //=.
    rewrite itv_boundlr/= 2!lte_bnd (le_trans _ r0)/= ?oppr_le0 ?ler0n//.
    by rewrite natr_absz ger0_norm ?ceil_ge0// ceil_ge.
  - exists (absz (floor r)) => //=.
    rewrite itv_boundlr/= 2!lte_bnd (le_trans (ltW r0)) ?ler0n// andbT.
    by rewrite natr_absz ltr0_norm ?floor_lt0// mulrNz opprK floor_le.
move=> n; split.
  rewrite /measurable/= /measurable/= /measurable/=.
(*  by exists [fset (ccitv n)]%fset; rewrite ssetE big_seq_fset1.*)
  admit.
by rewrite slength_itv hlength_itv /= -(fun_if EFin) lte_pinfty.
Admitted.

End slength_sigma_finite.

Section slength_additive.
Variable R : realType.
Implicit Types i : interval R.

Local Lemma slength_additive_seq (s : seq (interval R)) :
  trivIset setT (fun k => [set` nth 0%O s k]) ->
  slength [sset of s] = (\sum_(j <- s) slength [set` j])%E.
Proof.
move=> ts.
rewrite {1}/slength; case: xgetP => [/= s' _ Xs'|/(_ s)]; last first.
  by rewrite /=; tauto.
apply/esym; under eq_bigr do rewrite slength_itv; apply/esym.
apply: hlengthUset => //.
- do 2 rewrite cover_set_itv_nthE//.
  have [_ _ cover_s'] := is_decomposition_decompose s'.
  by rewrite -ssetE cover_s' -Xs'.
- apply/(trivIset_sorted_decompose (sort_sorted total_le_itv _))/allP => j.
  by rewrite mem_sort /= mem_filter => /andP[].
Qed.

Lemma slength_additive :
  additive (slength : set (sset_algebraOfSetsType R) -> \bar R).
Proof.
rewrite -semi_additiveE; apply/additive2P; first by rewrite slength0.
(* move=> A B /= [a Aa] [b Bb] AB0. *)
(* pose a' := decompose a; pose b' := decompose b. *)
(* have ABE : A `|` B = [sset of a' ++ b']. *)
(*   rewrite Aa Bb. *)
(*   have [_ _ <-] := is_decomposition_decompose a. *)
(*   have [_ _ <-] := is_decomposition_decompose b. *)
(*   by rewrite [in RHS]ssetE big_cat. *)
(* have tAB : trivIset setT (fun k => [set` nth 0%O (a' ++ b') k]). *)
(*   apply/trivIsetP => k1 k2 _ _. *)
(*   wlog : k1 k2 / (k1 < k2)%N. *)
(*     move=> h; rewrite eqn_leq negb_and -2!ltnNge => /orP[k2k1|k1k2]. *)
(*       by rewrite setIC h // lt_eqF. *)
(*     by rewrite h // lt_eqF. *)
(*   move=> k1k2 _. *)
(*   have [k2a'b'|a'b'k2] := ltnP k2 (size (a' ++ b')); last first. *)
(*     by rewrite setIC nth_default // set_itvE set0I. *)
(*   have [k2a'|a'k2] := ltnP k2 (size a'). *)
(*     rewrite nth_cat (ltn_trans k1k2) // nth_cat k2a'. *)
(*     have /trivIsetP := @trivIset_decompose _ a. *)
(*     by apply => //; rewrite ltn_eqF. *)
(*   have [k1a'|a'k1] := ltnP k1 (size a'). *)
(*     rewrite nth_cat k1a' nth_cat ltnNge a'k2 /=; apply: subsetI_eq0 AB0. *)
(*     - rewrite Aa; have [_ _ <-] := is_decomposition_decompose a. *)
(*       rewrite sset_bigcup => r ra'. *)
(*       by exists (nth 0%O a' k1) => //; exact/mem_nth. *)
(*     - rewrite Bb; have [_ _ <-] := is_decomposition_decompose b. *)
(*       rewrite sset_bigcup => r rb'. *)
(*       exists (nth 0%O b' (k2 - size a')) => //. *)
(*       by apply/mem_nth; rewrite ltn_subLR // -size_cat. *)
(*   rewrite nth_cat ltnNge a'k1 /= nth_cat ltnNge a'k2 /=. *)
(*   have /trivIsetP := @trivIset_decompose _ b. *)
(*   apply => //; rewrite -(eqn_add2r (size a')) (subnK a'k1) (subnK a'k2). *)
(*   by rewrite ltn_eqF. *)
(* rewrite ABE slength_additive_seq // (_ : A = [sset of a']); last first. *)
(*   rewrite /a' /decompose. *)
(*   rewrite (cover_sorted_decompose (sort_sorted total_le_itv _)) //. *)
(*   by rewrite sset_sort_le_itv sset_filter_neitv. *)
(* rewrite slength_additive_seq; last first. *)
(*   apply/trivIsetP => i j _ _ ij. *)
(*   move/trivIsetP : tAB => /(_ i j Logic.I Logic.I ij). *)
(*   rewrite nth_cat; case: ifPn => [ia'|]; last first. *)
(*     by rewrite -leqNgt => a'i; rewrite (nth_default _ a'i) set_itvE set0I. *)
(*   rewrite nth_cat; case: ifPn => [//|]. *)
(*   by rewrite -leqNgt => b'i; rewrite (nth_default _ b'i) set_itvE setI0. *)
(* rewrite (_ : B = [sset of b']); last first. *)
(*   rewrite (cover_sorted_decompose (sort_sorted total_le_itv _)) //. *)
(*   by rewrite sset_sort_le_itv sset_filter_neitv. *)
(* rewrite slength_additive_seq ?big_cat//. *)
(* apply/trivIsetP => i j _ _ ij. *)
(* move/trivIsetP : tAB => /(_ (size a' + i)%N (size a' + j)%N Logic.I Logic.I). *)
(* rewrite eqn_add2l => /(_ ij). *)
(* rewrite nth_cat -ltn_subRL subnn ltn0 addnC addnK. *)
(* by rewrite nth_cat -ltn_subRL subnn ltn0 addnC addnK. *)
Admitted.

Lemma semi_additive_slength :
  semi_additive (slength : set (sset_algebraOfSetsType R) -> _).
Proof. by rewrite semi_additiveE; exact: slength_additive. Qed.

(* Lemma semi_additive2_slength : *)
(*   semi_additive2 (slength : set (sset_algebraOfSetsType R) -> _). *)
(* Proof. Admitted. *)

Definition slength_additive_measure :
    {additive_measure set (sset_algebraOfSetsType R) -> \bar R} :=
  AdditiveMeasure.Pack _ (AdditiveMeasure.Axioms slength0
    (@slength_ge0 _) semi_additive_slength).
Canonical slength_additive_measure.

Corollary le_slengthU_sumslength (A : seq (set R)) :
  (forall a : set R, a \in A -> Sset.is_sset a) ->
  (slength (\big[setU/set0]_(a <- A) a) <= \sum_(a <- A) (slength a))%E.
Proof.
move=> mA.
do 2 rewrite (big_nth set0) big_mkord.
apply: (Boole_inequality [additive_measure of
         (slength : set (sset_algebraOfSetsType R) -> _)]) => /= k.
have [kA|kA] := ltnP k (size A).
(*   case: k kA=> [? |k kA]; first exact/mA/mem_nth. *)
(*   exact/mA/mem_nth. *)
(* by rewrite nth_default. *)
(* Qed. *)
Admitted.

End slength_additive.

(* NB: really useful? *)
Lemma is_cvg_sum_slength (R : realType)
    (F : (set (sset_algebraOfSetsType R))^nat) (P : pred nat) m :
  (forall k, P k -> measurable (F k)) ->
    cvg (fun n => (\sum_(m <= k < n | P k) slength (F k))%E).
Proof.
move=> mF; apply: is_cvg_ereal_nneg_natsum_cond => n mn Pn.
exact/slength_ge0.
Qed.

Lemma sum_slength_neitv (R : realType) (j : (interval R)^nat) :
  ((fun n => \sum_(0 <= k < n) slength [set` j k]) =
   (fun n => \sum_(0 <= k < n | neitv (j k)) slength [set` j k]))%E.
Proof.
rewrite funeqE => n; rewrite 2!big_mkord (bigID (fun k : 'I_n => neitv (j k))).
rewrite /= addeC big1 ?add0e // => k; rewrite neitvE => jk1jk2.
rewrite [X in slength X](_ : _ = set0) ?slengt0//.
by apply/eqP/negPn; rewrite -/(neitv _) neitvE.
Qed.

Lemma measurable_sset_itv (R : realType) (i : interval R) :
  measurable ([set` i] : set (sset_algebraOfSetsType R)).
(* Proof. exact/Sset.is_sset_itv. Qed. *)
Admitted.

Section slength_sigma_additive_on_intervals.
Variable R : realType.
Implicit Types i : interval R.
Local Open Scope ereal_scope.

Lemma slength_sigma_subadditive_finite_itv i (j : (interval R)^nat)
    (P : pred nat) :
  hlength [set` i] < +oo ->
  P `<=` neitv \o j ->
  [set` i] `<=` \bigcup_(k in P) [set` j k] ->
  slength [set` i] <=\sum_(k <oo | P k) slength [set` j k].
Proof.
move=> iNoo jne ij.
set l := lim _; have := lee_pinfty l.
rewrite le_eqVlt => /predU1P[->|loo]; first by rewrite lee_pinfty.
have [jfin|] := pselect (forall k, P k -> hlength [set` j k] < +oo); last first.
  move/existsNP => -[k /not_implyP[Pk] /negP].
  rewrite -leNgt lee_pinfty_eq => /eqP jkoo.
  by rewrite /l (ereal_nneg_series_pinfty _ Pk) // ?lee_pinfty// ?slength_itv//.
have [->|] := eqVneq [set` i] set0.
  by rewrite slength0 ereal_nneg_series_lim_ge0// => k _.
move=> i0.
have [ri1 ri2] := hlength_finite_fin_num i0 iNoo.
set a := fine i.1; set b := fine i.2.
have [ab|ba] := ltP a b; last first.
  rewrite slength_itv hlength_itv ltNge -{1}(fineK ri1) -{1}(fineK ri2).
  by rewrite -/a -/b lee_fin ba /= ereal_nneg_series_lim_ge0// => k _.
suff baj : forall e : {posnum R},
    b%:E - a%:E <= \sum_(k <oo | P k) slength [set` j k] + e%:num%:E.
  rewrite (@le_trans _ _ (b%:E - a%:E)) //.
    rewrite slength_itv hlength_itv -(fineK ri1) -(fineK ri2).
    by rewrite -/a -/b lte_fin ab.
  by apply lee_adde => e; exact: baj.
move=> e.
set a' := (a + e%:num/4%:R)%R.
set b' := (b - e%:num/4%:R)%R.
have a'b'i : {subset `[a', b'] <= i}.
  apply/subset_itvP => r; rewrite /= in_itv /= => /andP[a'r rb'].
  rewrite (IntervalE i).
  apply: ereal_mem_Interval.
  rewrite -(fineK ri1) -(fineK ri2) -/a -/b 2!lte_fin; apply/andP; split.
    by rewrite (lt_le_trans _ a'r) // /a' ltr_addl.
  by rewrite (le_lt_trans rb') // /b' ltr_subl_addl ltr_addr.
set a_ := fun k => fine (j k).1; set b_ := fun k => fine (j k).2.
set a'_ := (fun k => a_ k - e%:num / (2 ^ k.+3)%:R)%R.
set b'_ := (fun k => b_ k + e%:num / (2 ^ k.+3)%:R)%R.
have ia_b_ : [set` i] `<=` \bigcup_(k in P) `] (a'_ k) , (b'_ k) [%classic.
  move/subset_trans : ij; apply => r [k Pk].
  have [->//|jk0] := eqVneq [set` j k] set0.
  rewrite (IntervalE (j k)) => /Interval_ereal_mem /andP[jk1r rjk2].
  have [jk1 jk2] := hlength_finite_fin_num jk0 (jfin _ Pk).
  exists k => //=; rewrite in_itv /=; apply/andP; split.
    rewrite -lte_fin (lt_le_trans _ jk1r) // /a'_ /a_ EFinB lte_subl_addr//.
    rewrite -{2}(fineK jk1) // -EFinD lte_fin.
    by rewrite ltr_addl divr_gt0 // ltr0n expn_gt0.
  rewrite -lte_fin (le_lt_trans rjk2) // /b'_ /b_ -{1}(fineK jk2) //.
  by rewrite lte_fin ltr_addl divr_gt0 // ltr0n expn_gt0.
have a'b'a'_b'_ :
    [set x | x \in `[a', b']] `<=` \bigcup_(k in P) `](a'_ k), (b'_ k)[%classic.
  by move/subset_itvP : a'b'i => /subset_trans; apply.
have [F [HF HF_]] : exists F : {fset nat}, `[a', b']%classic `<=`
    \bigcup_(k in [set x | (x \in F) && (P x)]) `] (a'_ k), (b'_ k) [%classic /\
  [set x | x \in F] `<=` P.
  have h k : P k -> open `](a'_ k), (b'_ k)[%classic.
    by move=> _; exact: interval_open.
  have := @segment_compact _ a' b'.
  (* NB: Borel-Lebesgue theorem *)
  rewrite compact_cover => /(_ _ _ _ h a'b'a'_b'_) => -[F FP a'b'F]; exists F.
  split; last by move=> x /FP; rewrite inE.
  move=> r /a'b'F[k Fk kr]; exists k => //=.
  by rewrite Fk /=; move/FP : Fk; rewrite inE.
set F' := [fset k in F | neitv `](a'_ k), (b'_ k)[]%fset.
have HF' : (`[a', b'] `<=` \bigcup_(k in [set` F']) `](a'_ k), (b'_ k)[)%classic.
  move/subset_trans : HF; apply.
  move=> r [k /andP[kF Pk]].
  have [-> //|a'b'k0 a'b'kr] := eqVneq `](a'_ k), (b'_ k)[%classic set0.
  by exists k => //; rewrite /mkset /F' !inE /= /neitv /= a'b'k0 andbT.
have : b'%:E - a'%:E <= \sum_(k <oo | P k) slength [set` j k] + (e%:num / 2)%:E.
  have [a'b'|b'a'] := ltP a' b'; last first.
    rewrite (@le_trans _ _ 0%:E) //; first by rewrite sube_le0 lee_fin.
    rewrite adde_ge0 // ?lee_fin//.
    by apply: ereal_nneg_series_lim_ge0 => k _; exact/slength_ge0.
  rewrite (@le_trans _ _ (slength `[a', b']%classic)) //.
    by rewrite slength_itv hlength_itv /= lte_fin a'b'.
  have F'_ringOfSets x : x \in [seq `](a'_ k), (b'_ k)[%classic | k <- F'] ->
      Sset.is_sset x.
    move=> /mapP[/= p pF' ->{x}]; exists [:: `](a'_ p), (b'_ p)[ ].
    by rewrite sset_cons1.
  rewrite (@le_trans _ _
      (slength (\big[setU/set0]_(k <- F') `] (a'_ k), (b'_ k) [%classic))) //.
    apply/le_measure => //.
    - (* by rewrite inE /=; exact/Sset.is_sset_itv. *)
      admit.
      rewrite inE /=; apply: bigsetU_measurable => n _.
    - (* exact/Sset.is_sset_itv. *)
      admit.
    by move/subset_trans : HF'; apply; rewrite bigcup_set.
  rewrite (@le_trans _ _ (\sum_(k <- F') (b'_ k - a'_ k)%:E)) //.
    move: (@le_slengthU_sumslength _ [seq `](a'_ k), (b'_ k)[%classic | k <- F']
      F'_ringOfSets).
    rewrite big_map => /le_trans; apply.
    rewrite big_map /F' 2!big_fset /= ; apply: lee_sum => k /neitvP.
    rewrite lte_bnd => a'b'k0.
    by rewrite slength_itv hlength_itv /= lte_fin a'b'k0.
  apply: (le_trans _
      (@epsilon_trick _ (slength \o pred_set \o j) _ P _)) => //; last first.
  rewrite [X in X <= _](_ : _ =
      \sum_(k <- F') (b_ k - a_ k + (e%:num / (2 ^ k.+2)%:R))%:E); last first.
    apply eq_bigr => /= k ?; rewrite /a'_ /b'_; congr (_ %:E).
    rewrite opprB addrA addrC 2!addrA (addrC _ (b_ k)) -addrA; congr (_ + _)%R.
    by rewrite -mulrDl -mulr2n -mulr_natl expnS natrM -mulf_div divff // mul1r.
  under eq_bigr do rewrite EFinD.
  rewrite big_split /=.
  (* TODO: lemma? *)
  have cvggeo :
      (fun n => \sum_(i < n) (e%:num / (2 ^ i.+2)%:R)%:E) --> (e%:num / 2)%:E.
    rewrite (_ : (fun n => _) =
        EFin \o series (fun k => e%:num / (2 ^ (k + 2))%:R)); last first.
      rewrite funeqE => n; rewrite /series /=.
      rewrite (@big_morph _ _ EFin 0%:E adde) // big_mkord.
      by under eq_bigr do rewrite -[in X in (_ ^X)%:R]addn2.
    apply: cvg_comp; last apply cvg_refl.
    have := @cvg_geometric_series_half _ e%:num 1.
    by rewrite expr1.
  have ? : cvg (fun n => \sum_(k < n | P k) (e%:num / (2 ^ k.+2)%:R)%:E).
    under eq_fun do rewrite -(big_mkord P (fun k => (e%:num / (2 ^ k.+2)%:R)%:E)).
    by apply: is_cvg_ereal_nneg_series => n _; rewrite lee_fin divr_ge0// ler0n.
  apply (@le_trans _ _ (\sum_(k <oo | P k) slength [set` j k] +
      \sum_(k <oo | P k) (e%:num / (2 ^ k.+2)%:R)%:E)); last first.
    rewrite -ereal_limD //; last 3 first.
      by apply: is_cvg_sum_slength => k Pk; exact: measurable_sset_itv.
      by under eq_fun do rewrite big_mkord.
      have /andP[l0 le2] :
          0 <= \sum_(k <oo | P k) (e%:num / (2 ^ k.+2)%:R)%:E <= (e%:num / 2)%:E.
        apply/andP; split.
          rewrite (@ereal_nneg_series_lim_ge0 _
            (fun k => (e%:num / (2 ^ k.+2)%:R)%:E)) // => n _.
          by apply divr_ge0 => //; rewrite ler0n.
        move/cvg_lim : (cvggeo) => <- //=.
        apply lee_lim => //.
          by under eq_fun do rewrite big_mkord.
          under eq_fun do rewrite -(big_mkord xpredT (fun k => (e%:num / (2 ^ k.+2)%:R)%:E)).
          by apply: is_cvg_ereal_nneg_series => n _; rewrite lee_fin divr_ge0 // ler0n.
        near=> n.
        rewrite (big_mkord P (fun k => (e%:num / (2 ^ k.+2)%:R)%:E)).
        move: (@lee_sum_nneg R _ (enum 'I_n) xpredT P (fun k => (e%:num / (2 ^ k.+2)%:R)%:E)).
        rewrite big_enum big_enum_cond; apply => k _ _.
        by apply divr_ge0 => //; rewrite ler0n.
      apply: fin_num_adde_def => //.
      rewrite fin_numE gt_eqF /=; last first.
        by rewrite (lt_le_trans _ l0) // lte_ninfty.
      by rewrite lt_eqF // (le_lt_trans le2) // lte_pinfty.
    rewrite (_ : (fun x => _) = (fun x => \sum_(0 <= k < x | P k)
      (slength [set` j k] + (e%:num / 2 / (2 ^ k.+1)%:R)%:E))) //.
    rewrite funeqE => n; rewrite big_split => /=; congr (_ + _).
    by apply eq_bigr => m Pm; rewrite expnS natrM invfM -mulrA.
  have sum_F'_P f : \sum_(k <- F') f k = \sum_(k <- F' | P k) f k.
    apply eq_fbigl_cond => // k; apply/idP/idP => /=.
      rewrite !inE andbT => /andP[/= kF -> /=].
      by rewrite andbT kF /=; apply/HF_.
    by rewrite !inE andbT => /andP[].
  apply: lee_add; last first.
    set f := fun n => \sum_(k < n | P k) (e%:num / (2 ^ n.+2)%:R)%:E.
    rewrite (@le_trans _ _ (\sum_(k <oo | P k) (e%:num / (2 ^ k.+2)%:R)%:E)) //.
    rewrite sum_F'_P.
    by apply: lee_sum_fset_lim => n _; apply divr_ge0 => //; rewrite ler0n.
  rewrite [X in X <= _](_ : _ = \sum_(k <- F') slength [set` j k]); last first.
    apply eq_fbigr => k /imfsetP[/= p]; rewrite !inE => /andP[pF a'b'p0 ->{k} ?].
    rewrite /b_ /a_ slength_itv hlength_itv.
    have [? ?] : ((j p).1 : \bar R) \is a fin_num /\
                 ((j p).2 : \bar R) \is a fin_num.
      apply hlength_finite_fin_num; first by apply: jne => //; exact: HF_.
      by apply jfin => //; exact: HF_.
    rewrite EFinB fineK// fineK//.
    have /jne/neitvP/ltW/le_bnd_ereal : P p := HF_ _ pF.
    by rewrite le_eqVlt => /predU1P[->|->//]; rewrite ltxx subee.
  by rewrite sum_F'_P; apply: lee_sum_fset_lim => k _; exact/slength_ge0.
have -> : b'%:E - a'%:E = b%:E - a%:E - (e%:num / 2)%:E.
  rewrite /a' /b' (EFinD a) oppeD// (EFinB b) -addeA.
  rewrite (addeCA (- (e%:num / 4%:R)%:E)) addeA; congr (_ + _).
  rewrite -oppeD//; congr oppe; rewrite -EFinD; congr (_%:E).
  by rewrite -mulrDl -mulr2n -mulr_natl (natrM _ 2 2) -mulf_div divff // mul1r.
rewrite lee_subl_addr// => /le_trans; apply; rewrite le_eqVlt; apply/orP; left.
rewrite -addeA; apply/eqP; congr (_ + _).
by rewrite -EFinD -mulrDl -mulr2n -mulr_natr -mulrA divff ?mulr1.
(* Unshelve. all: by end_near. Qed. *)
Admitted.

Lemma slength_sigma_additive_finite_itv i (j : (interval R)^nat) :
  [set` i] = \bigcup_k [set` j k] ->
  trivIset setT (pred_set \o j) ->
  hlength [set` i] < +oo ->
  slength [set` i] = \sum_(k <oo) slength [set` j k].
Proof.
move=> ij tj iNoo.
apply/eqP; rewrite eq_le; apply/andP; split.
  pose P := neitv \o j.
  have : [set` i] `<=` \bigcup_(k in [set x | neitv (j x)]) [set` j k].
    suff: [set` i] = \bigcup_(k in [set x | neitv (j x)]) [set` j k].
      by move=> ->.
    rewrite ij; apply/predeqP => r; split => [[x _ jxr]|[x]].
      by exists x => //; rewrite /mkset; apply/set0P; exists r.
    by exists x.
  move/(@slength_sigma_subadditive_finite_itv _ j P iNoo (fun x => id)).
  move/le_trans; apply; apply: lee_lim.
  (* + by apply: is_cvg_sum_slength => n jn0; exact/Sset.is_sset_itv. *)
  + admit.
  (* + by apply: is_cvg_sum_slength => n _; exact/Sset.is_sset_itv. *)
  + admit.
  + near=> n.
    rewrite 2!big_mkord.
    move: (@lee_sum_nneg R _ (enum 'I_n) xpredT (neitv \o j)
      (slength \o pred_set \o j)).
    rewrite /= big_enum_cond big_enum; apply.
    by move=> x _ _; exact/slength_ge0.
apply: ereal_lim_le.
  (* by apply: is_cvg_sum_slength => n _; exact/Sset.is_sset_itv. *)
  admit.
near=> n.
rewrite [X in X <= _](_ : _ = slength (\big[setU/set0]_(k < n) [set` j k])) //.
  apply: le_measure.
  (* - by rewrite inE /=; apply: bigsetU_measurable => k _; exact/Sset.is_sset_itv. *)
  - admit.
  (* - by rewrite inE /=; exact/Sset.is_sset_itv. *)
  - admit.
  - by rewrite ij -bigcup_set /= => r [k /= _ jkr]; exists k.
rewrite big_mkord; apply/esym.
apply/(@measure_bigsetU _ _ (@slength_additive_measure R) (pred_set \o j)) => //.
(* by move=> // k; exists [:: j k]; rewrite sset_cons1. *)
admit.
(* Unshelve. all: by end_near. Qed. *)
Admitted.

Lemma slength_sigma_subadditive_infinite_itv
    i (j : (interval R)^nat) (P : pred nat) :
  hlength ([set` i]) = +oo ->
  (forall k, P k -> neitv (j k)) ->
  [set` i] `<=` \bigcup_(k in P) [set` j k] ->
  slength [set` i] <= \sum_(k <oo | P k) slength [set` j k].
Proof.
move=> ioo jne ij; suff h : forall M, (M > 0)%R -> \forall n \near \oo,
    M%:E <= \sum_(0 <= k < n | P k) slength [set` j k].
  rewrite slength_itv ioo lee_pinfty_eq; apply/eqP.
  by apply/cvg_lim => //; apply/ereal_cvgPpinfty => M M0; exact: h.
set iIccitv := fun n => [set` i] `&` [set` ccitv R n].
have len_iIccitv_dvg M : (M > 0)%R ->
    exists n, (n >= 1)%N /\ M%:E < slength (iIccitv n).
  move=> M0.
  move/pinfty_hlength : ioo => [[b [r iroo]]|ioo]; last first.
    have ? : (0 < `|ceil M|)%N by rewrite absz_gt0 gt_eqF // ceil_gt0.
    exists `|ceil M|%N; split=> //; rewrite /iIccitv ioo set_itvE setTI.
    rewrite slength_ccitv lte_fin (le_lt_trans (ceil_ge _)) // -muln2 natrM.
    rewrite natr_absz gtr0_norm ?ceil_gt0// ltr_pmulr ?ltr1n// ltr0z.
    by rewrite ceil_gt0.
  rewrite /iIccitv.
  wlog : i {ij iIccitv} b r {iroo} / i = Interval -oo%O (BSide b r).
    move=> h; move: iroo => [->|iroo]; first exact: h.
    have [N [N0 MN]] := h _ b (- r)%R erefl.
    by exists N; split => //; rewrite iroo slength_ccitv_sym.
  move=> ->{i}.
  have [r0|r0] := ler0P r.
    exists (`|ceil (`| r | + M) |%N.+1); split => //.
    rewrite -set_itv_meet slength_itv hlength_itv /= lte_fin ltxI gtr_opp //.
    rewrite andbT ltr_oppl opprK meet_l ?(le_trans r0)//.
    rewrite -addn1 natrD natr_absz ger0_norm ?ceil_ge0// ?(addr_ge0 _ (ltW _))//.
    case: ifPn => [_|].
      rewrite lte_fin -ltr_subl_addl ltr_spaddr//.
      by rewrite (le_trans _ (ceil_ge _))// addrC ler_add2r ler0_norm.
    rewrite ltr_spaddr//.
    by rewrite (le_trans _ (ceil_ge _)) // (ler_paddr (ltW _))// ler0_norm.
  move=> [:crM]; exists (`|ceil (`| r | + M)|%N); split.
    abstract: crM.
    by rewrite absz_gt0 gt_eqF // ceil_gt0 // -(addr0 0%R) ler_lt_add.
  rewrite -set_itv_meet slength_itv hlength_itv /= lte_fin ltxI gtr_opp ?ltr0n//.
  rewrite ltr_oppl opprK andbT.
  rewrite natr_absz ger0_norm ?ceil_ge0// ?(addr_ge0 _ (ltW _))// gtr0_norm//.
  rewrite meet_l; last first.
    by rewrite (le_trans (ceil_ge _)) // ler_int le_ceil // ler_addl ltW.
  case: ifPn => [_|/negP].
    rewrite lte_fin -{1}(add0r M) ltr_le_add//.
    by rewrite (le_trans (ceil_ge _)) // ler_int le_ceil // ler_addr ltW.
  rewrite -oppr_lt0 in r0.
  by rewrite (lt_le_trans r0)// ler0z ceil_ge0// addr_ge0// ?ltW// -oppr_lt0.
move=> M M0.
have {len_iIccitv_dvg}[N [N0 MN]] := len_iIccitv_dvg _ M0.
set jIccitv := fun N k => [set` j k] `&` [set` ccitv R N].
have len_jIccitv_dvg :
    \forall n \near \oo, M%:E <= \sum_(k < n | P k) slength (jIccitv N k).
  have iUj n : iIccitv n `<=` \bigcup_(k in P) jIccitv n k.
    by move/(@setSI _ [set` ccitv R n]) : ij; rewrite setI_bigcupl.
  apply lte_lim => //.
  + apply: (@lee_sum_nneg_ord _ (slength \o jIccitv N)) => n Pn.
    by apply: slength_ge0; rewrite /jIN -set_itv_meet; exact/Sset.is_sset_itv.
  + under eq_fun do rewrite -(big_mkord P (slength \o jIccitv N)).
    apply: is_cvg_ereal_nneg_series => n _.
    by apply: slength_ge0; rewrite /jIN -set_itv_meet; exact/Sset.is_sset_itv.
  + rewrite (lt_le_trans MN) // /iIccitv -set_itv_meet.
    under [in lim _]eq_fun do rewrite -(big_mkord P (slength \o jIccitv N)).
    rewrite [X in _ <= X](_ : _ = (\sum_(k <oo | P k)
        slength [set` itv_meet (j k) (ccitv R N)])); last first.
      congr (lim _); rewrite funeqE => /= n.
      by under eq_bigr do rewrite /jIccitv -set_itv_meet.
    rewrite (_ : (fun n => _) =
      (fun n => \sum_(k < n | P k && (neitv (itv_meet (j k) (ccitv R N))))
      slength [set` itv_meet (j k) (ccitv R N)])%E); last first.
      rewrite funeqE => /= n; rewrite big_mkord.
      rewrite (bigID (fun k : 'I_n => neitv (itv_meet (j k) (ccitv R N)))) /=.
      rewrite addeC big1 ?add0e // => k /andP[?].
      by rewrite negbK => /eqP ->; rewrite slength0.
    under [in lim _]eq_fun do
      rewrite -(big_mkord (fun k => P k && (neitv (itv_meet (j k) (ccitv R N))))
      (fun k => slength [set` itv_meet (j k) (ccitv R N)])).
    apply: (@slength_sigma_subadditive_finite_itv _
        (fun k => itv_meet (j k) (ccitv R N))
        (fun k => P k && (neitv (itv_meet (j k) (ccitv R N))))) => //.
    + rewrite (@le_lt_trans _ _ (hlength [set` ccitv R N])) //.
      by apply le_hlength; rewrite set_itv_meet; apply subIset; right.
    + by rewrite -slength_itv slength_ccitv lte_pinfty.
    + by move=> k /andP[].
    + apply: (@subset_trans _
          (\bigcup_(k in P) [set` itv_meet (j k) (ccitv R N)])).
        move=> x; rewrite set_itv_meet => /iUj [k ? Hk]; exists k => //.
        by rewrite set_itv_meet.
      move=> r [k Pk kr]; exists k => //; rewrite Pk /=; apply/set0P.
      by exists r.
have [m _ Hm] :
    \forall n \near \oo, M%:E <= \sum_(k < n | P k) slength [set` j k].
  case: len_jIccitv_dvg => m [mN]; exists m => // p /= mp.
  have /le_trans := mN _ mp; apply; apply: lee_sum => /= q _.
  rewrite /jIccitv; apply: le_measure => //.
  (* - by rewrite inE /=; apply: measurableI => //; exact/Sset.is_sset_itv. *)
  - admit.
  (* - by rewrite inE /=; exact/Sset.is_sset_itv. *)
  - admit.
near=> n; rewrite big_mkord.
by have /Hm mn : (m <= n)%N by near: n; exists m.
(* Unshelve. all: by end_near. Qed. *)
Admitted.

Lemma slength_sigma_subadditive_itv i (j : (interval R)^nat) (P : pred nat) :
  (forall k, P k -> neitv (j k)) ->
  [set` i] `<=` \bigcup_(k in P) [set` j k] ->
  slength ([set` i]) <= \sum_(k <oo | P k) slength [set` j k].
Proof.
move=> jne ij; have := lee_pinfty (hlength [set` i]).
rewrite le_eqVlt => /predU1P[|] ioo; by [
  exact: slength_sigma_subadditive_infinite_itv |
  exact: slength_sigma_subadditive_finite_itv].
Qed.

Lemma slength_sigma_additive_itv i (j : (interval R)^nat) :
  [set` i] = \bigcup_k [set` j k] -> trivIset setT (pred_set \o j) ->
  slength ([set` i]) = \sum_(k <oo) slength [set` j k].
Proof.
move=> ij tj; have := lee_pinfty (hlength [set` i]).
rewrite le_eqVlt => /predU1P[ioo|iNoo]; last first.
  exact: slength_sigma_additive_finite_itv.
rewrite slength_itv ioo sum_slength_neitv; apply/esym/eqP.
rewrite -lee_pinfty_eq -ioo -slength_itv.
apply: slength_sigma_subadditive_itv => // r.
by rewrite ij => -[n _ jnr]; exists n => //=; apply/set0P; exists r.
Qed.

End slength_sigma_additive_on_intervals.

Section slength_measure.
Variable R : realType.
Implicit Types (i : interval R) (f : (seq (interval R))^nat).
Local Open Scope ereal_scope.

Definition nil_cons0 f := fun k => if size (f k) == O then [:: 0%O] else f k.

Lemma nil_cons0P (f : (seq (interval R))^nat) n : size (nil_cons0 f n) != O.
Proof. by rewrite /nil_cons0; case: ifPn. Qed.

Lemma nil_cons0_bigU f k : \big[setU/set0]_(x <- f k) [set` x] =
  \big[setU/set0]_(x <- nil_cons0 f k) [set` x].
Proof.
rewrite /nil_cons0; case: (f k) => /= [|h t]; last by rewrite big_cons.
by rewrite big_nil big_seq1 set_itvE.
Qed.

Lemma nil_cons0_bigcup_bigU f : \bigcup_k \big[setU/set0]_(x <- f k) [set` x] =
  \bigcup_k \big[setU/set0]_(x <- nil_cons0 f k) [set` x].
Proof. by congr bigcup; rewrite funeqE => j; exact: nil_cons0_bigU. Qed.

Lemma nil_cons0_sum f k :
  \sum_(x <- f k) slength [set` x] = \sum_(x <- nil_cons0 f k) slength [set` x].
Proof.
rewrite /nil_cons0; case: (f k) => //=.
by rewrite big_nil big_seq1 set_itvE slength0.
Qed.

Lemma nil_cons0_lim f : \sum_(k <oo) \sum_(x <- f k) slength [set` x] =
  \sum_(k <oo) \sum_(x <- nil_cons0 f k) slength [set` x].
Proof.
rewrite (_ : (fun n => \sum_(0 <= k < n) (\sum_(x <- f k) slength [set` x])) =
  (fun n => \sum_(0 <= k < n) (\sum_(x <- nil_cons0 f k) slength [set` x]))) //.
by rewrite funeqE => n; apply eq_bigr => j _; rewrite nil_cons0_sum.
Qed.


Local Lemma le_slength_itv_sumI (F : (set R)^nat) f :
  (forall k, F k = [sset of f k]) ->
  forall i, [set` i] `<=` \bigcup_k (F k) ->
  slength ([set` i]) <= \sum_(k <oo) slength ([set` i] `&` F k).
Proof.
move=> Fs i iF.
have {iF}iiF : [set` i] `<=` \bigcup_k ([set` i] `&` F k).
  by move=> r ir; move/iF : (ir) => [k _ Skr]; exists k.
pose df := decompose \o f.
pose idf := fun k => [seq itv_meet i x | x <- df k].
have {iiF} :
    [set` i] `<=` \bigcup_k (\big[setU/set0]_(x <- idf k) [set` x]).
  move/subset_trans : iiF; apply => r [n _].
  rewrite [in X in X -> _]Fs ssetE big_distrr /= => sir.
  exists n => //; rewrite /idf big_map.
  under eq_bigr do rewrite set_itv_meet.
  move: sir; rewrite -bigcup_set => -[/= j jsn [ir jr]].
  have [k [ksn kr]] := mem_decompose jsn jr.
  by rewrite -bigcup_set; exists k.
rewrite nil_cons0_bigcup_bigU bigcup_bigU_bigcup //; last exact: nil_cons0P.
move=> iiF.
rewrite (_ : (fun _ => _) = (fun n => \sum_(0 <= k < n)
    \sum_(x <- idf k) slength [set` x])); last first.
  rewrite funeqE => k; apply eq_bigr => {}k _.
  have -> : forall n, [set` i] `&` F n = \big[setU/set0]_(x <- idf n) [set` x].
    move=> n; rewrite big_map;have [_ _] := is_decomposition_decompose (f n).
    rewrite {1}ssetE -[decompose _]/(df n) -(Fs n) => <-.
    by rewrite big_distrr /=; under eq_bigr do rewrite -set_itv_meet.
  rewrite (big_nth 0%O) big_mkord.
  rewrite (@measure_bigsetU _ _ (@slength_additive_measure R)
      (fun n => [set` nth 0%O (idf k) n])) //; last 2 first.
    (* by move=> m; apply: Sset.is_sset_itv. *)
    admit.
    exact/trivIset_itv_meet/trivIset_decompose.
  by rewrite (big_nth 0%O) big_mkord.
rewrite nil_cons0_lim.
rewrite (le_trans _ (@sum_nth_interval_sum_sum _ (nil_cons0 idf) slength _ _))//.
- rewrite sum_slength_neitv slength_sigma_subadditive_itv => //.
  by apply: (subset_trans iiF) => r [k _ kr]; exists k => //; apply/set0P; exists r.
- exact: nil_cons0P.
(* Unshelve. all: by end_near. Qed. *)
Admitted.

Lemma slength_semi_sigma_additive :
  semi_sigma_additive (slength : set (sset_algebraOfSetsType R) -> \bar R).
Proof.
move=> F mF tF mUF.
suff -> : slength (\bigcup_k F k) = \sum_(k <oo) slength (F k).
  exact/is_cvg_sum_slength.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: (ereal_lim_le (is_cvg_sum_slength _)) => //.
  by near=> n; rewrite big_mkord; exact: le_sum_measure_bigcup.
(* have [seq_of Fseq_of] := @choice _ _ (fun k s => F k = [sset of s]) mF. *)
(* have [j [Fj tj]] : exists j : seq (interval R), \bigcup_k (F k) = [sset of j] /\ *)
(*     trivIset setT (fun k => [set` nth 0%O j k]). *)
(*   have [j Fj] := mUF. *)
(*   exists (decompose j); split; last exact: trivIset_decompose. *)
(*   by rewrite Fj; have [_ _ ->] := is_decomposition_decompose j. *)
(* rewrite Fj ssetE (big_nth 0%O) big_mkord. *)
(* rewrite (@measure_bigsetU _ _ (@slength_additive_measure R) *)
(*     (fun n => [set` nth 0%O j n])) //; last first. *)
(*   by move=> i; exact/measurable_sset_itv. *)
(* rewrite (@le_trans _ _ (\sum_(0 <= n < size j) *)
(*          \sum_(k <oo) slength ([set` nth 0%O j n] `&` F k))) //. *)
(*   rewrite big_mkord; apply: lee_sum => n _. *)
(*   rewrite (@le_slength_itv_sumI F seq_of) // Fj ssetE (big_nth 0%O). *)
(*   rewrite big_mkord => r jnr. *)
(*   by rewrite -bigcup_set; exists n => //=; rewrite mem_index_enum. *)
(* rewrite (@le_trans _ _ (\sum_(n <oo) *)
(*   \sum_(0 <= k < size j) slength ([set` nth 0%O j k] `&` F n))) //. *)
(*   rewrite (@ereal_pseries_sum_nat _ (size j)) //. *)
(*   by move=> a b; exact: slength_ge0. *)
(* apply: lee_lim. *)
(* - apply: is_cvg_ereal_nneg_series => n _. *)
(*   by apply: sume_ge0 => /= i _; apply: slength_ge0. *)
(* - by apply/is_cvg_sum_slength => ? _; exact/mF. *)
(* - near=> n; apply: lee_sum => /= k _. *)
(*   have Fkj : F k = \bigcup_i ([set` nth 0%O j i] `&` F k). *)
(*     rewrite -setI_bigcupl setIC; apply/esym/setIidPl. *)
(*     rewrite (_ : \bigcup_ _ _ = [sset of j]). *)
(*       by rewrite -Fj; apply: bigcup_sup. *)
(*     rewrite ssetE (big_nth 0%O) big_mkord (bigcup_splitn (size j)). *)
(*     rewrite bigcup0 ?setU0// => i _. *)
(*     by rewrite nth_default ?set_itvE// leq_addr. *)
(*   rewrite {2}Fkj big_mkord le_sum_measure_bigcup//. *)
(*   + by move=> i; apply: measurableI => //; exact/measurable_sset_itv. *)
(*   + by rewrite -Fkj. *)
(*   + by under eq_fun do rewrite setIC; exact: trivIset_setI. *)
(* Unshelve. all: by end_near. Qed. *)
Admitted.

End slength_measure.
