(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum topology.
Require Import sequences cardinality.

(******************************************************************************)
(*                     Summations over classical sets                         *)
(*                                                                            *)
(* This file provides a definition of sum over classical sets and a few       *)
(* lemmas in particular for the case of sums of non-negative terms.           *)
(*                                                                            *)
(* The contents of this file should not be considered as definitive because   *)
(* it supports on-going developments (such as the Lebesgue measure) and we    *)
(* anticipate revisions.                                                      *)
(*                                                                            *)
(* \csum_(i in I) f i == summation of non-negative extended real numbers over *)
(*            classical sets; I is a classical set and f is a function whose  *)
(*            codomain is included in the extended reals; it is 0 if I = set0 *)
(*            and sup(\sum_F a) where F is a finite set included in I o.w.    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\csum_ ( i 'in' P ) F"
  (at level 41, F at level 41, format "\csum_ ( i  'in'  P )  F").

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

Definition fsets S : set {fset T} := [set F | [set x | x \in F] `<=` S].

Lemma fsets_set0 S : fsets S fset0. Proof. by []. Qed.

Lemma fsets_self (F : {fset T}) : fsets [set x | x \in F] F.
Proof. by []. Qed.

Lemma fsetsP S (F : {fset T}) : [set x | x \in F] `<=` S <-> fsets S F.
Proof. by []. Qed.

Lemma fsets0 : fsets set0 = [set fset0].
Proof.
rewrite predeqE => A; split => [|->]; last exact: fsets_set0.
by rewrite /fsets /= subset0 => /eqP; rewrite eq_set0_fset0 => /eqP.
Qed.

End set_of_fset_in_a_set.

Lemma fsets_img (aT rT : choiceType) (S : set aT) (F : {fset aT}) (e : aT -> rT) :
  fsets S F -> fsets (e @` S) (e @` F)%fset.
Proof.
by rewrite /fsets => FS t /= /imfsetP[/= i iF ->{t}]; exists i => //; apply/FS.
Qed.

Definition fsets_ord (P : pred nat) n := [fset i in 'I_n | P i]%fset.

Lemma fsets_ord_nat (P : pred nat) n :
  fsets P (@nat_of_ord _ @` fsets_ord P n)%fset.
Proof. by move=> /= i /imfsetP[/= a] /imfsetP[/= b Pb] ->{a} ->{i}. Qed.

Lemma fsets_ord_subset (T : pointedType) (F : {fset T})
    (e : nat -> T) (P : pred nat) : injective e ->
  [set x | x \in F] `<=` e @` P ->
  exists n, (F `<=` e @` (@nat_of_ord _ @` fsets_ord P n))%fset.
Proof.
move=> ie FeP.
have [/eqP F0|F0] := boolP (F == fset0); first by exists O; rewrite F0.
have [n Fn] : exists n, forall x, x \in F -> forall i, e i = x -> (i <= n)%N.
  have [eF eFE] : set_finite (e @^-1` [set x | x \in F]).
    by apply: set_finite_preimage; [move=> ? ? ? ?; exact/ie|exists F].
  have : eF != fset0.
    rewrite -eq_set0_fset0 -eFE; apply/set0P.
    move: F0; rewrite -eq_set0_fset0 => /set0P[t tF].
    by have [i Pi eit] := FeP _ tF; exists i; rewrite /preimage /mkset eit.
  move/fset_nat_maximum => [i [ieF eFi]]; exists i => t tF j eji; apply eFi.
  by move/predeqP : eFE => /(_ j) /iffLR; apply; rewrite /preimage /mkset eji.
exists n.+1; apply/fsubsetP => x Fx; apply/imfsetP => /=.
have [j Pj ejx] := FeP _ Fx; exists j => //; apply/imfsetP => /=.
have jn : (j < n.+1)%N by rewrite ltnS (Fn x).
by exists (Ordinal jn) => //; apply/imfsetP => /=; exists (Ordinal jn).
Qed.

Section csum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition csum S a :=
  ereal_sup [set \sum_(i <- F) a i | F in fsets S].

Local Notation "\csum_ ( i 'in' P ) F" := (csum P (fun i => F)).

Lemma csum0 a : \csum_(i in set0) a i = 0.
Proof.
rewrite /csum fsets0 [X in ereal_sup X](_ : _ = [set 0%E]) ?ereal_sup1//.
rewrite predeqE => x; split; first by move=> [_ /= ->]; rewrite big_seq_fset0.
by move=> -> /=; exists fset0 => //; rewrite big_seq_fset0.
Qed.

End csum.

Notation "\csum_ ( i 'in' P ) F" := (csum P (fun i => F)) : ring_scope.

Section csum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> \bar R).

Lemma csum_ge0 (S : set T) a : (forall x, 0 <= a x) -> 0 <= \csum_(i in S) a i.
Proof.
move=> a0.
by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
Qed.

Lemma csum_fset (F : {fset T}) a : (forall i, i \in F -> 0 <= a i) ->
  \csum_(i in [set x | x \in F]) a i = \sum_(i <- F) a i.
Proof.
move=> f0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' F'F <-]; apply/lee_sum_nneg_subfset.
  exact/fsetsP.
by move=> t; rewrite inE => /andP[_ /f0].
Qed.

End csum_realType.

Lemma csum_image (R : realType) (T : pointedType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) : (forall n, P n -> 0 <= a (e n)) ->
    injective e ->
  \csum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof.
move=> a0 ie; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: (ereal_lim_le (is_cvg_ereal_nneg_series_cond a0)).
  near=> n; apply: ereal_sup_ub.
  exists (e @` (@nat_of_ord _ @` fsets_ord P n))%fset.
    exact/fsets_img/fsets_ord_nat.
  rewrite big_imfset /=; last by move=> x y _ _ /ie.
  rewrite big_imfset /=; last by move=> x y _ _/ord_inj.
  by rewrite big_fset /= big_enum_cond big_mkord.
apply: ub_ereal_sup => _ [/= F /fsetsP ePF <-].
have [n /fsubsetP FPn] := fsets_ord_subset ie ePF.
apply (ereal_lim_ge (is_cvg_ereal_nneg_series_cond a0)); near=> m.
rewrite (_ : \sum_(_ <=_ < _ |_ ) _ =
    \sum_(i <- e @` (@nat_of_ord _ @` fsets_ord P m)) a i)%fset; last first.
  rewrite big_imfset /=; last by move=> i j _ _ /ie.
  rewrite big_imfset /=; last by move=> i j _ _ /ord_inj.
  by rewrite big_mkord big_imfset //= big_filter big_enum_cond.
apply: lee_sum_nneg_subfset => [x xF|t].
  have /imfsetP[j /imfsetP[j' /=]] := FPn _ xF; rewrite !inE /= => Pj' jj' xej.
  apply/imfsetP => /=; exists j => //; apply/imfsetP => /=.
  have nm : (n <= m)%N by near: m; exists n.
  by exists (widen_ord nm j') => //=; rewrite !inE.
rewrite inE /= => /andP[tF /imfsetP[/= i /imfsetP[i' /=]]].
by rewrite !inE /= => Pi' ->{i} -> _; apply a0.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_pseries_csum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \csum_(i in [set x | P x]) a i.
Proof.
move=> a0; rewrite -(@csum_image _ _ _ id) //; congr csum.
by rewrite predeqE => /= n; split => [[m Pm <-//]|Pn]; exists n.
Qed.

Section csum_bigcup.
Variables (R : realType) (T : pointedType) (K : set nat) (J : nat -> set T).
Hypotheses (tJ : trivIset setT J).
Let KJ := \bigcup_(k in K) (J k).
Variable a : T -> \bar R.
Hypothesis a0 : forall x, 0 <= a x.

Let tJ' : forall i j : nat, i != j -> J i `&` J j = set0.
Proof. by move=> i j ij; move: tJ => /trivIsetP; apply. Qed.

Local Lemma csum_bigcup_le :
  \csum_(t in KJ) a t <= \csum_(k in K) \csum_(t in J k) a t.
Proof.
apply ub_ereal_sup => /= _ [F KJF <-].
pose FJ := fun k => [fset x in F | x \in J k]%fset.
have dFJ : forall i j, i != j -> [disjoint FJ i & FJ j]%fset.
  move=> i j ij; rewrite fdisjoint_cset; apply/eqP.
  by apply: subsetI_eq0 (tJ' ij) => t /imfsetP[t0 /=];
    rewrite !inE => /andP[_]; rewrite inE => ? ->.
pose KFJ := [set k | K k /\ FJ k != fset0].
have [L LKFJ] : set_finite KFJ.
  suff : set_finite [set k | FJ k != fset0] by apply: subset_set_finite => t [].
  suff : surjective [set x | x \in F] [set k | FJ k != fset0]
                    (fun t => xget 0%N [set n | t \in J n]).
    by move/surjective_set_finite; apply; exists F.
  move=> i /fset0Pn[t]; rewrite /FJ !inE => /andP[/= tF tJi].
  exists t; split => //; case: xgetP; last by move/(_ i).
  move=> j _ tJj; apply/eqP/negPn/negP => /(@tJ' i j).
  by rewrite predeqE => /(_ t)[+ _]; apply; rewrite /= !inE in tJi tJj.
have LK : [set i | i \in L] `<=` K.
  by move=> /= i iL; move/predeqP : LKFJ => /(_ i) /iffRL /(_ iL) [].
have -> : \sum_(i <- F) a i = \sum_(k <- L) \sum_(i <- FJ k) a i.
  suff -> : F = (\big[fsetU/fset0]_(x <- L) FJ x)%fset.
    by apply/partition_disjoint_bigfcup; exact: dFJ.
  apply/fsetP => t; apply/idP/idP => [tF|/bigfcupP[i]]; last first.
    by rewrite andbT => iM; rewrite /FJ !inE => /andP[].
  have [i Ki Jit] := KJF _ tF.
  apply/bigfcupP ; exists i; rewrite ?andbT; last by rewrite !inE tF in_setE.
  move/predeqP : LKFJ => /(_ i) /iffLR; apply; split => //.
  apply/negP => /eqP/fsetP/(_ t).
  by rewrite !inE => /negbT/negP; apply; rewrite tF in_setE.
apply: (@le_trans _ _ (\sum_(k <- L) \csum_(j in J k) a j)).
  apply: lee_sum => i _.
  apply: ereal_sup_ub; exists (FJ i) => //; apply/fsetsP => t.
  by rewrite /FJ /mkset !inE /= => /andP[_]; rewrite in_setE.
by apply ereal_sup_ub; exists L => //; exact/subfsetsP.
Qed.

Local Notation "L \_ i" := (nth O%N L i) (at level 3).

Local Lemma le_csum_bigcup :
  \csum_(i in K) \csum_(j in J i) a j <= \csum_(i in KJ) a i.
Proof.
apply ub_ereal_sup => /= _ [L LK <-].
have [/eqP ->|L0] := boolP (L == fset0); first by rewrite big_nil csum_ge0.
have /gee0P[->|[r r0 csumIar]] := csum_ge0 KJ a0; first by rewrite lee_pinfty.
apply: lee_adde => e; rewrite -lee_subl_addr //.
suff : \sum_(i < #|` L |) \csum_(j in J (L \_ i)) a j - e%:num%:E <=
       \csum_(j in KJ) a j.
  by apply: le_trans; apply: lee_add2r; rewrite (big_nth O) big_mkord lee_sum.
set P := fun (Fj : {fset T}%fset) (j : 'I_#|`L|) =>
  [set x | x \in Fj] `<=` J (L \_ j) /\
  \csum_(j in J (L \_ j)) a j - (e%:num / #|` L |%:R)%:E < \sum_(s <- Fj) a s.
have [Fj csumFj] : exists F, forall j, P (F j) j.
  suff : forall j, exists Fj, P Fj j.
    by case/(@choice _ _ (fun i F => P F i)) => Fj ?; exists Fj.
  move=> j; rewrite /P /csum; set es := ereal_sup _.
  have [esoo|esfin] : es = +oo \/ es \is a fin_num.
    suff : 0 <= es by case: es => // [s s0|]; [right|left].
    by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
  - move: csumIar; rewrite /csum; set es' := ereal_sup _ => es'r.
    suff : es <= es' by rewrite esoo es'r.
    apply: le_ereal_sup => x [F FJ Fax]; exists F => //.
    move/subset_trans : FJ; apply => t Jt; exists (L \_ j) => //.
    by apply: LK; rewrite /mkset mem_nth.
  - have eL0 : (0 < e%:num / #|` L |%:R)%R.
      by rewrite divr_gt0 // ltr0n cardfs_gt0.
    have [x [[F JLjF Faix] ese]] := ub_ereal_sup_adherent (PosNum eL0) esfin.
    by exists F; split => //; rewrite Faix.
pose F := \big[fsetU/fset0]_(i < #|`L|) Fj i.
apply: (@le_trans _ _ (\sum_(i <- F) a i)); last first.
  apply ereal_sup_ub; exists F => //.
  apply/fsetsP => t /bigfcupP[/= i _] /(proj1 (csumFj i)) Jt.
  by exists (L \_ i) => //; apply: LK; rewrite /mkset mem_nth.
rewrite (_ : \sum_(_ <- _) _ =
             \sum_(i < #|`L|) \sum_(j <- Fj i) a j); last first.
  have tFj : (forall i j : 'I_#|`L|, i != j -> [disjoint Fj i & Fj j])%fset.
    move=> i j ij; rewrite -fsetI_eq0.
    suff : (Fj i `&` Fj j)%fset == fset0 by [].
    rewrite -eq_set0_fset0.
    have Jij : J (L \_ i) `&` J (L \_ j) = set0.
      apply: tJ' => //; apply: contra ij => /eqP /(congr1 (index^~ L)).
      by rewrite index_uniq // index_uniq // => /ord_inj ->.
    apply/eqP; rewrite predeqE => t; split => //; rewrite /mkset inE => /andP[].
    by move=> /(proj1 (csumFj i)) ? /(proj1 (csumFj j)) ?; rewrite -Jij; split.
  pose IL := [fset i | i in 'I_#|`L|]%fset.
  have -> : F = (\bigcup_(i <- IL) Fj i)%fset by rewrite big_imfset // big_enum.
  transitivity (\sum_(i <- IL) \sum_(j <- Fj i) a j); last first.
    by rewrite /IL big_imfset //= big_enum.
  by apply partition_disjoint_bigfcup; exact: tFj.
rewrite (_ : e%:num = \sum_(i < #|`L|) (e%:num / #|`L|%:R))%R; last first.
  rewrite big_const iter_addr addr0 card_ord -mulr_natr.
  by rewrite -mulrA mulVr ?mulr1 // unitfE pnatr_eq0 cardfs_eq0.
rewrite -EFinN (@big_morph _ _ _ 0%R _ _ _ (@opprD R)) ?oppr0 //.
rewrite (@big_morph _ _ _ 0 _ _ _ EFinD) // -big_split /=.
by apply: lee_sum => /= i _; exact: (ltW (proj2 (csumFj i))).
Qed.

Lemma csum_bigcup : \csum_(i in \bigcup_(k in K) (J k)) a i =
                    \csum_(i in K) \csum_(j in J i) a j.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: csum_bigcup_le | exact: le_csum_bigcup].
Qed.

End csum_bigcup.
