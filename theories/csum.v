(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum topology.
Require Import sequences cardinality.

(******************************************************************************)
(*                     Summations over general sets (WIP)                     *)
(*                                                                            *)
(* This file provides a definition of sum over general sets as well as lemmas *)
(* in particular for the case of sums of non-negative terms. The contents of  *)
(* this file should not be considered as definitive because it essentially    *)
(* supports on-going developments (including Lebesgue integral) and is        *)
(* therefore likely to undergo revisions.                                     *)
(*                                                                            *)
(* \gsum_(i in I) f i == summation of non-negative extended real numbers over *)
(*             general sets; I is a classical set and f is a function whose   *)
(*             codomain is included in the extended reals; it is 0 if I = set0*)
(*             and o.w. sup(\sum_F a) where F is a finite set included in I   *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\gsum_ ( i 'in' P ) F"
  (at level 41, F at level 41, format "\gsum_ ( i  'in'  P )  F").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO: move to sequences.v *)
Lemma ereal_pseries_pred0 (R : realType) (P : pred nat) (f : nat -> {ereal R}) :
  P =1 xpred0 -> \sum_(i <oo | P i) f i = 0%:E.
Proof.
move=> P0; rewrite (_ : (fun _ => _) = fun=> 0%:E) ?lim_cst// funeqE => n.
by rewrite big1 // => i; rewrite P0.
Qed.

(* NB: worth putting near ub_ereal_sup_adherent_img? *)
Lemma ub_ereal_sup_adherent_img (R : realFieldType) (T : choiceType)
    (P : T -> Prop) (f : T -> {ereal R}) (e : {posnum R}) c :
  ereal_sup (f @` P) = c%:E -> exists t, P t /\ c%:E - e%:num%:E < f t.
Proof.
move=> fPc; have [x [[t Pt ftx] fPex]] := ub_ereal_sup_adherent e fPc.
by exists t; split => //; rewrite ftx -fPc.
Qed.

(* about the set of fset's included in a set *)
Section set_of_fset_in_a_set.
Variable (T : choiceType).
Implicit Type S : set T.

Definition fsets S : set {fset T} := [set F | [set x | x \in F] `<=` S].

Lemma fsets_set0 S : fsets S fset0. Proof. by []. Qed.

Lemma fsets_self (F : {fset T}) : fsets [set x | x \in F] F.
Proof. by []. Qed.

Lemma fsetsP S (F : {fset T}) : [set x | x \in F] `<=` S <-> fsets S F.
Proof. by []. Qed.

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

Section gsum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> {ereal R}).

Definition gsum S a := if S == set0 then 0%:E else
  ereal_sup [set \sum_(i <- F) a i | F in fsets S].

Local Notation "\gsum_ ( i 'in' P ) F" := (gsum P (fun i => F)).

Lemma gsum0 a : \gsum_(i in set0) a i = 0%:E.
Proof. by rewrite /gsum eqxx. Qed.

Lemma gsumE S a : S !=set0 ->
  \gsum_(t in S) a t = ereal_sup [set \sum_(i <- F) a i | F in fsets S].
Proof. by move=> /set0P/negbTE S_neq0; rewrite /gsum S_neq0. Qed.

End gsum.

Notation "\gsum_ ( i 'in' P ) F" := (gsum P (fun i => F)) : ring_scope.

Section gsum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> {ereal R}).

Lemma gsum_ge0 (S : set T) a : (forall x, 0%:E <= a x) ->
  0%:E <= \gsum_(i in S) a i.
Proof.
move=> a0; rewrite /gsum; case: ifPn => // _.
by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
Qed.

Lemma gsum_fset (F : {fset T}) a : (forall i, i \in F -> 0%:E <= a i) ->
  \gsum_(i in [set x | x \in F]) a i = \sum_(i <- F) a i.
Proof.
move=> f0; rewrite /gsum; case: ifPn => [|F0].
  by rewrite eq_set0_fset0 => /eqP ->; rewrite big_seq_fset0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' F'F <-]; apply/lee_sum_nneg_subfset.
  exact/fsetsP.
by move=> t; rewrite inE => /andP[_ /f0].
Qed.

End gsum_realType.

Lemma gsum_image (R : realType) (T : pointedType) (a : T -> {ereal R})
    (e : nat -> T) (P : pred nat) : (forall n, P n -> 0%:E <= a (e n)) ->
    injective e ->
  \gsum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof.
move=> a0 ie; have [/eqP eP0|/set0P eP0] := boolP (e @` P == set0).
  rewrite eP0 gsum0 (ereal_pseries_pred0 (a \o e)) // => n.
  move/image_set0_set0: eP0; rewrite predeqE => /(_ n); rewrite -propeqE.
  by rewrite /set0 -falseE => /is_true_inj.
rewrite (gsumE _ eP0); apply/eqP; rewrite eq_le; apply/andP; split; last first.
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

Lemma gsum_nat_lim (R : realType) (a : nat -> {ereal R}) (P : pred nat) :
  (forall n, P n -> 0%:E <= a n) ->
  \gsum_(i in P) a i = \sum_(i <oo | P i) a i.
Proof.
move=> a0; rewrite -(@gsum_image _ _ _ id) //; congr gsum.
by rewrite predeqE => /= n; split => [Pn|[m Pm <-//]]; exists n.
Qed.

Section gsum_bigcup.
Variables (R : realType) (T : pointedType) (K : set nat) (J : nat -> set T).
Hypotheses (J0 : forall k, J k !=set0) (tJ : trivIset setT J).
Let KJ := \bigcup_(k in K) (J k).
Variable a : T -> {ereal R}.
Hypothesis a0 : forall x, 0%:E <= a x.

Let tJ' : forall i j : nat, i != j -> J i `&` J j = set0.
Proof. by move=> i j ij; move: tJ => /trivIsetP; apply. Qed.

Local Lemma gsum_bigcup_le : K !=set0 -> KJ !=set0 ->
  \gsum_(t in KJ) a t <= \gsum_(k in K) (fun j => \gsum_(t in J j) a t) k.
Proof.
move=> K0 KJ0; rewrite gsumE //; apply ub_ereal_sup => /= _ [F KJF <-].
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
  move=> i /fset0Pn[t]; rewrite /FJ !inE => /andP[/= Ft tJi].
  exists t; split => //; case: xgetP; last by move/(_ i).
  move=> j _ tJj; apply/eqP/negPn/negP => /(@tJ' i j).
  rewrite predeqE => /(_ t)[+ _]; apply.
  by rewrite /= !inE in tJi tJj.
have LK : [set i | i \in L] `<=` K.
  by move=> /= i iL; move/predeqP : LKFJ => /(_ i) /iffRL /(_ iL) [].
have -> : (\sum_(i <- F) a i = \sum_(k <- L) (\sum_(i <- FJ k) a i)%E)%E.
  suff -> : F = (\big[fsetU/fset0]_(x <- L) (FJ x))%fset.
    by apply/partition_disjoint_bigfcup; exact: dFJ.
  apply/fsetP => t; apply/idP/idP => [tF|/bigfcupP[i]]; last first.
    by rewrite andbT => iM; rewrite /FJ !inE => /andP[].
  have [i Ki Jit] := KJF _ tF.
  apply/bigfcupP ; exists i; rewrite ?andbT.
    move/predeqP : LKFJ => /(_ i) /iffLR; apply; split => //.
    apply/negP => /eqP/fsetP/(_ t).
    by rewrite !inE => /negbT/negP; apply; rewrite tF in_setE.
  by rewrite /FJ !inE tF in_setE.
apply: (@le_trans _ _ (\sum_(k <- L) (\gsum_(j in J k) a j))%E).
  apply: lee_sum => i _; rewrite gsumE //.
  apply: ereal_sup_ub; exists (FJ i) => //; apply/fsetsP => t.
  by rewrite /FJ /mkset !inE /= => /andP[_]; rewrite in_setE.
by rewrite gsumE //; apply ereal_sup_ub; exists L => //; exact/subfsetsP.
Qed.

Local Notation "L \_ i" := (nth O%N L i) (at level 3).

Local Lemma le_gsum_bigcup : K !=set0 -> KJ !=set0 ->
  \gsum_(i in K) (fun k => \gsum_(j in J k) a j) i <= \gsum_(i in KJ) a i.
Proof.
move=> K0 UJ_neq0.
rewrite gsumE //; apply ub_ereal_sup => /= _ [L LK <-].
have [/eqP ->|L0] := boolP (L == fset0); first by rewrite big_nil gsum_ge0.
have /gee0P[->|[r r0 gsumIar]] := gsum_ge0 KJ a0; first by rewrite lee_pinfty.
apply lee_adde => e; rewrite -lee_subl_addr.
suff : \sum_(i < #|` L |) (\gsum_(j in J (L \_ i)) a j) - e%:num%:E <=
       \gsum_(j in KJ) a j.
  by apply: le_trans; apply: lee_add2r; rewrite (big_nth O) big_mkord lee_sum.
set P := fun (Fj : {fset T}%fset) (j : 'I_#|`L|) =>
  [set x | x \in Fj] `<=` J (L \_ j) /\
  \gsum_(j in J (L \_ j)) a j - (e%:num / #|` L |%:R)%:E < \sum_(s <- Fj) a s.
have [Fj csumFj] : exists F, forall j, P (F j) j.
  suff : forall j, exists Fj, P Fj j.
    by case/(@choice _ _ (fun i F => P F i)) => Fj ?; exists Fj.
  move=> j; rewrite /P gsumE //.
  set es := ereal_sup _.
  have [esoo|[c c0 esc]] : es = +oo \/ exists2 r : R, (r >= 0)%R & es = r%:E.
    suff : 0%:E <= es by move/gee0P.
    by apply ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
  - move: gsumIar; rewrite gsumE //; set es' := ereal_sup _ => es'r.
    suff : es <= es' by rewrite esoo es'r.
    apply: le_ereal_sup => x [F FJ Fx]; exists F => //.
    move/subset_trans : FJ; apply => t Jt; exists (L \_ j) => //.
    by apply : LK; rewrite /mkset mem_nth.
  - have eL0 : (0 < e%:num / #|` L |%:R)%R.
      by rewrite divr_gt0 // ltr0n cardfs_gt0.
    rewrite (_ : _ / _ = (PosNum eL0)%:num) // esc.
    exact: ub_ereal_sup_adherent_img.
pose F := \big[fsetU/fset0]_(i < #|`L|) Fj i.
apply: (@le_trans _ _ (\sum_(i <- F) a i)); last first.
  rewrite gsumE //; apply ereal_sup_ub; exists F => //.
  apply/fsetsP => t /bigfcupP[/= i _] /(proj1 (csumFj i)) Jt.
  by exists (L \_ i) => //; apply: LK; rewrite /mkset mem_nth.
rewrite (_ : \sum_(_ <- _) _ =
             \sum_(i < #|`L|) (\sum_(j <- Fj i) a j)%E); last first.
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
  have -> : F = (\bigcup_(i <- IL) Fj i)%fset
    by rewrite /IL big_imfset //= big_enum.
  transitivity (\sum_(i <- IL) (\sum_(j <- Fj i) a j)%E); last first.
    by rewrite /IL big_imfset //= big_enum.
  by apply partition_disjoint_bigfcup; exact: tFj.
rewrite (_ : e%:num = \sum_(i < #|`L|) (e%:num / #|`L|%:R))%R; last first.
  rewrite big_const iter_addr addr0 card_ord -mulr_natr.
  by rewrite -mulrA mulVr ?mulr1 // unitfE pnatr_eq0 cardfs_eq0.
rewrite -NERFin (@big_morph _ _ _ 0 _ _ _ (@opprD R)) ?oppr0 //.
rewrite (@big_morph _ _ _ 0%:E _ _ _ addERFin) // -big_split /=.
by apply: lee_sum => /= i _; exact: (ltW (proj2 (csumFj i))).
Qed.

Lemma gsum_bigcup : \gsum_(i in \bigcup_(k in K) (J k)) a i =
                    \gsum_(i in K) (fun k => \gsum_(j in J k) a j) i.
Proof.
have [/eqP ->|/set0P K0] := boolP (K == set0).
  by rewrite bigcup_set0 2!gsum0.
have /set0P KJ0 : KJ != set0.
  by move: K0 => [k Kk]; have [t Jkt] := J0 k; apply/set0P; exists t, k.
apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: gsum_bigcup_le | exact: le_gsum_bigcup].
Qed.

End gsum_bigcup.
