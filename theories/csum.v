(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum topology.
Require Import sequences cardinality.

(******************************************************************************)
(*               About functions of extended real numbers (WIP)               *)
(*                                                                            *)
(* This file provides some tools to deal with functions of extended real      *)
(* real numbers. The contents of this file should not be considered as        *)
(* definitive because they support on-going developments (including Lebesgue  *)
(* integral) and will therefore undergo much revision.                        *)
(*                                                                            *)
(*    f ^\+ == the function formed by the non-negative outputs of f (from a   *)
(*             type to the type of extended eral numbers) and 0 otherwise     *)
(*    f ^\+ == the function formed by the non-positive outputs of f and 0 o.w.*)
(*  f \|_ D == the restriction of f on the domain D (and 0 o.w.)              *)
(* csum I f == summation of non-negative extended reals over countable sets;  *)
(*             I is a classical set and f a function with codomain included   *)
(*             in the extended reals; it is 0 if I = set0 and o.w.            *)
(*             sup(\sum_F a) where F is a finite set included in I            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "f ^\+" (at level 1, format "f ^\+").
Reserved Notation "f ^\-" (at level 1, format "f ^\-").
Reserved Notation "f \|_ D" (at level 10).

Section funpos.

Local Notation "0" := 0%:E : ereal_scope.
Local Notation "1" := 1%:E : ereal_scope.
Local Open Scope ereal_scope.

Definition funepos T (R : realDomainType) (f : T -> {ereal R}) :=
   fun x => Order.max (f x) 0%E.
Definition funeneg T (R : realDomainType) (f : T -> {ereal R}) :=
   fun x => Order.max (- f x)%E 0%E.
Local Notation "f ^\+" := (funepos f).
Local Notation "f ^\-" := (funeneg f).

Definition fer T (R : realDomainType) (f : T -> {ereal R}) (D : set T) :=
  fun x => if `[<D x>] then f x else 0%E.
Local Notation "f \|_ D" := (fer f D).

Lemma ferK T (R : realDomainType) (f : T -> {ereal R}) (D1 D2 : set T) :
  f \|_ D1 \|_ D2 = f \|_ (D1 `&` D2).
Proof.
by apply/funext=> x; rewrite /fer/= asbool_and; do 3?[case: asbool => //].
Qed.

Lemma mem_fer T (R : realDomainType) (f : T -> {ereal R}) (D : set T) x :
  D x -> f \|_ D x = f x.
Proof. by move=> Dx; rewrite /fer; case: asboolP. Qed.

Lemma memNfer T (R : realDomainType) (f : T -> {ereal R}) (D : set T) x :
  ~ D x -> f \|_ D x = 0%E.
Proof. by move=> Dx; rewrite /fer; case: asboolP. Qed.

Lemma ferN0  T (R : realDomainType) (f : T -> {ereal R}) :
  f \|_ [set x | f x != 0%E] = f.
Proof. by apply/funext => x; rewrite /fer asboolb; case: eqVneq => [->|]. Qed.

Lemma funEeposneg T (R : realDomainType) (f : T -> {ereal R}) :
  f = (fun x => f^\+ x - f^\- x)%E.
Proof.
apply/funext => x; rewrite /funepos /funeneg !maxEle !leEereal/=.
case: f => [r||]/=; rewrite ?oppr_le0 ?real0//=.
by case: ltgtP; rewrite /= ?sub0r ?subr0 ?oppr0 ?opprK// => ->.
Qed.

Lemma normfunEeposneg T (R : realDomainType) (f : T -> {ereal R}) :
  (fun x => `|f x|)%E = (fun x => f^\+ x + f^\- x)%E.
Proof.
apply/funext => x; rewrite /funepos /funeneg !maxEle !leEereal/=.
case: f => [r||]/=; rewrite ?oppr_le0 ?real0//=.
by case: sgrP => //=; rewrite ?addr0 ?sub0r.
Qed.

Lemma funepos_ge0 T (R : realDomainType) (f : T -> {ereal R}) :
  (forall x, 0 <= f^\+ x)%E.
Proof. by move=> x; rewrite /funepos; case: (leP (f x)) => //= /ltW. Qed.

Lemma funeneg_ge0 T (R : realDomainType) (f : T -> {ereal R}) :
  (forall x, 0 <= f^\- x)%E.
Proof. by move=> x; rewrite /funeneg; case: (leP (- f x)%E) => //= /ltW. Qed.

Lemma funeposEgt0 T (R : realDomainType) (f : T -> {ereal R}) :
  (f^\+ = f \|_ [set x | 0 < f x])%E.
Proof.
by apply/funext => x; rewrite /fer /funepos/= maxEle asboolb; case: ltgtP.
Qed.

Lemma funeposEge0 T (R : realDomainType) (f : T -> {ereal R}) :
  (f^\+ = f \|_ [set x | 0 <= f x])%E.
Proof.
by apply/funext => x; rewrite /fer /funepos/= maxEle asboolb; case: ltgtP.
Qed.

Lemma funenegElt0 T (R : realDomainType) (f : T -> {ereal R}) :
  (f^\- = fun x => - f \|_ [set x | f x < 0] x)%E.
Proof.
apply/funext => x; rewrite /fer /funeneg/= maxEle asboolb leEereal ltEereal.
case: f => //= [r||]; rewrite ?(oppr0, real0)//.
by rewrite oppr_le0; case: leP; rewrite //= oppr0.
Qed.

Lemma funenegEle0 T (R : realDomainType) (f : T -> {ereal R}) :
  (f^\- = fun x => - f \|_ [set x | f x <= 0] x)%E.
Proof.
by rewrite funenegElt0 funeqE => x; rewrite /fer !asboolb/=; case: ltgtP => // ->.
Qed.

Hint Resolve funepos_ge0 funeneg_ge0 : core.
End funpos.

Notation "f ^\+" := (funepos f) : ereal_scope.
Notation "f ^\-" := (funeneg f) : ereal_scope.
Notation "f \|_ D" := (fer f D) : ring_scope.

Lemma ub_ereal_sup_adherent2 (R : realFieldType) (T : choiceType)
  (P : T -> Prop) (f : T -> {ereal R}) (e : {posnum R}) c :
  ereal_sup [set y | exists2 F, P F & (f F = y)%E] = c%:E ->
  exists F, P F /\ (c%:E - e%:num%:E < f F)%E.
Proof.
set S : set {ereal R} := (X in ereal_sup X) => Sc.
have : ~ ubound S (ereal_sup S - e%:num%:E)%E.
  move/ub_ereal_sup; apply/negP.
  by rewrite -ltNge Sc lte_subl_addr lte_fin ltr_addl.
move/asboolP; rewrite asbool_neg; case/existsp_asboolPn => /= x.
rewrite not_implyE => -[[A AJj <-{x}] AS].
by exists A; split => //; rewrite ltNge; apply/negP; rewrite subERFin -Sc.
Qed.

Definition csum (R : realFieldType) (T : choiceType) (S : set T)
    (a : T -> {ereal R}) :=
  if S == set0 then 0%:E else
  ereal_sup [set (\sum_(i <- F) a i)%E |
               F in [set F : {fset T} | [set i | i \in F] `<=` S]].

Lemma csum0 (R : realFieldType) (T : choiceType) (a : T -> {ereal R}) :
  csum set0 a = 0%:E.
Proof. by rewrite /csum eqxx. Qed.

Lemma csum_ge0 (R : realType) (T : choiceType) (a : T -> {ereal R})
    (a0 : forall x, (0%:E <= a x)%E) (I : set T) :
  (0%:E <= csum I a)%E.
Proof.
rewrite /csum; case: ifPn => // _.
by apply: ereal_sup_ub; exists fset0 => //; rewrite big_nil.
Qed.

Lemma csum_fset (R : realType) (T : choiceType) (S : {fset T})
    (f : T -> {ereal R}) : (forall i, 0%:E <= f i)%E ->
  csum [set x | x \in S] f = (\sum_(i <- S) f i)%E.
Proof.
move=> f0; rewrite /csum; case: ifPn => [|S0].
  by rewrite eq_set0_fset0 => /eqP ->; rewrite big_seq_fset0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists S.
by apply ub_ereal_sup => /= ? -[F FS <-]; exact/lee_sum_nneg_subfset.
Qed.

Lemma csum_countable (R : realType) (T : pointedType) (a : T -> {ereal R})
  (e : nat -> T) (P : pred nat) : (forall n, 0%:E <= a n)%E -> injective e ->
  csum [set e i | i in P] a = lim (fun n => (\sum_(i < n | P i) a (e i))%E).
Proof.
move=> a0 ie; rewrite /csum; case: ifPn => [/eqP/image_set0_set0 P0|S0].
  rewrite (_ : (fun _ => _) = fun=> 0%:E) ?lim_cst// funeqE => n.
  by rewrite big1 // => i Pi; move: P0; rewrite predeqE => /(_ i) [] /(_ Pi).
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le.
    by apply: (@is_cvg_ereal_nneg_series_cond _ (a \o e)) => *; exact: a0.
  near=> n; apply: ereal_sup_ub.
  exists (e @` [fset (nat_of_ord i) | i in 'I_n & P i])%fset.
    by move=> t /imfsetP[m /imfsetP[j]]; rewrite !inE /= => jP -> ->; exists j.
  rewrite big_imfset //=; last by move=> x y _ _ /ie.
  rewrite big_imfset /=; last by move=> x y _ _; exact: ord_inj.
  by rewrite big_filter big_enum_cond.
apply: ub_ereal_sup => _ [/= F FS <-].
have [/eqP ->|F0] := boolP (F == fset0).
  rewrite big_nil ereal_lim_ge //.
    by apply: (@is_cvg_ereal_nneg_series_cond _ (a \o e)) => *; exact: a0.
  by near=> n; apply: sume_ge0 => *; exact: a0.
have [n FnS] : exists n, (F `<=` [fset e (nat_of_ord i) | i in 'I_n & P i])%fset.
  have [n Fn] : exists n, forall x, x \in F -> forall i, e i = x -> (i <= n)%N.
    have [eF eFE] : set_finite (e @^-1` [set x | x \in F]).
      apply: set_finite_preimage; last by exists F.
      by move=> ? ? ? ?; exact/ie.
    have : eF != fset0.
      rewrite -eq_set0_fset0 -eFE; apply/set0P.
      have : F != fset0 by [].
      rewrite -eq_set0_fset0 => /set0P[t tF].
      by move: (tF) => /FS[i Pi eit]; exists i; rewrite /preimage /mkset eit.
    move/fset_nat_maximum => [i [ieF eFi]]; exists i => t tF j eji; apply eFi.
    by move/predeqP : eFE => /(_ j) /iffLR; apply; rewrite /preimage /mkset eji.
  exists n.+1; apply/fsubsetP => x Fx; apply/imfsetP => /=.
  have [j Pj ejx] := FS _ Fx.
  by exists (inord j); rewrite ?inE inordK // ltnS (Fn _ Fx).
apply ereal_lim_ge.
  by apply: (@is_cvg_ereal_nneg_series_cond _ (a \o e)) => *; exact: a0.
near=> m.
rewrite -(big_enum_cond _ 'I_m) -[X in (_ <= X)%E]big_filter /=.
rewrite [X in (_ <= X)%E](_ : _ =
    \sum_(i <- [fset e (nat_of_ord j) | j in 'I_m & P j]%fset) a i)%E; last first.
  by rewrite big_imfset //= => i j _ _ /ie/ord_inj.
apply: lee_sum_nneg_subfset => // x xF; apply/imfsetP.
have nm : (n <= m)%N by near: m; exists n.
move/fsubsetP : FnS => /(_ _ xF) => /imfsetP[/= j ? ejx].
by exists (widen_ord nm j).
Grab Existential Variables. all: end_near. Qed.

Lemma csum_csum (R : realType) (T : pointedType) (K : set nat)
    (J : nat -> set T) (a : T -> {ereal R}) :
  (forall x, 0%:E <= a x)%E -> (forall k, J k != set0) -> trivIset setT J ->
  csum (\bigcup_(k in K) (J k)) a = csum K (fun k => csum (J k) a).
Proof.
move=> a0.
have [/eqP ->|K0] := boolP (K == set0); first by rewrite bigcup_set0 2!csum0.
move=> J0 /trivIsetP tJ; set I := \bigcup_(k in K) (J k).
have /set0P I0 : I !=set0.
  by move/set0P : K0 => [k Kk]; have /set0P[t Jkt] := J0 k; exists t, k.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite {1}/csum (negbTE I0); apply ub_ereal_sup => /= _ [F FI <-].
  pose FJ := fun k => [fset x in F | x \in J k]%fset.
  have tFJ : forall i j, i != j -> [disjoint FJ i & FJ j]%fset.
    (* TODO: use fdisjoint_cset *)
    move=> i j ij; rewrite -fsetI_eq0; apply/eqP/fsetP => t; apply/idP/idP=> //.
    apply/negP; rewrite inE => /andP[]; rewrite !inE /= => /andP[Ft].
    rewrite in_setE => tJi /andP[_]; rewrite in_setE => tJj.
    by have /(congr1 (@^~ t))/= := tJ _ _ Logic.I Logic.I ij; rewrite /set0 mksetE => <-.
  pose KFJ := [set k | K k /\ FJ k != fset0].
(* TODO:  pose g := fun t => xget 0%N [set n | t \in J n].
  have : [set k | FJ k != fset0] = [set k | k \in (g @` F)%fset].
    rewrite predeqE => i; split.
      move/fset0Pn => [t]; rewrite !inE /= => /andP[tF tJi].
      apply/imfsetP; exists t => //; rewrite /g.
      (* utiliser les prop de triviset *) *)
  have : set_finite KFJ.
    suff suppFJ : set_finite [set k | FJ k != fset0].
      have KFJsuppF : KFJ `<=` [set k | FJ k != fset0] by move=> t [].
      by have [] := set_finite_subset KFJsuppF _.
    pose g := fun t => xget 0%N [set n | t \in J n].
    have sur_g : surjective [set x | x \in F] [set k | FJ k != fset0] g.
      move=> i /fset0Pn[t]; rewrite /FJ !inE /= => /andP[Ft tJi].
      exists t; split => //; rewrite /g; case: xgetP; last by move/(_ i).
      move=> j _ tJj; apply/eqP/negPn/negP => /(tJ i j Logic.I Logic.I).
      rewrite predeqE => /(_ t)[+ _]; apply.
      by rewrite /= !inE in tJi tJj.
    by apply: (proj1 (surjective_set_finite sur_g _)); exists F.
  move=> [L LKFJ].
  have LK : [set i | i \in L] `<=` K.
    by move=> /= i iL; move/predeqP : LKFJ => /(_ i) /iffRL /(_ iL) [].
  have -> : (\sum_(i <- F) a i = \sum_(k <- L) (\sum_(i <- FJ k) a i)%E)%E.
    suff -> : F = (\big[fsetU/fset0]_(x <- L) (FJ x))%fset.
      by apply/partition_disjoint_bigfcup; exact: tFJ.
    apply/fsetP => t; apply/idP/idP => [tF|/bigfcupP[i]]; last first.
      by rewrite andbT => iM; rewrite /FJ !inE => /andP[].
    have := FI _ tF; move=> -[i Ki Jit].
    apply/bigfcupP ; exists i; rewrite ?andbT.
      move/predeqP : LKFJ => /(_ i) /iffLR; apply; split => //.
      apply/negP => /eqP/fsetP/(_ t).
      by rewrite !inE /= => /negbT /negP; apply; rewrite tF /= in_setE.
    by rewrite /FJ !inE /= tF in_setE.
  apply: (@le_trans _ _ (\sum_(k <- L) (csum (J k) a))%E).
    apply: lee_sum => i _; rewrite /csum (negbTE (J0 _)).
    apply: ereal_sup_ub; exists (FJ i) => // t.
    by rewrite /FJ /mkset !inE /= => /andP[_]; rewrite in_setE.
  rewrite [in X in (_ <= X)%E]/csum (negbTE K0); apply ereal_sup_ub.
  by exists L.
rewrite {1}[in X in (X <= _)%E]/csum (negbTE K0).
apply ub_ereal_sup => /= _ [L LK <-].
have [/eqP ->|L0] := boolP (L == fset0); first by rewrite big_nil csum_ge0.
have /gee0P[->|[r r0 csumIar]] := csum_ge0 a0 I; first by rewrite lee_pinfty.
apply lee_adde => e; rewrite -lee_subl_addr.
suff : (\sum_(i < #|` L |) csum (J (nth O L i)) a - (e)%:num%:E <= csum I a)%E.
  by apply: le_trans; apply: lee_add2r; rewrite (big_nth O) big_mkord lee_sum.
set P := (fun (Fj : {fset T}%fset) (j : 'I_#|`L|) =>
  [set x | x \in Fj] `<=` J (nth 0%N L j) /\
  (csum (J (nth 0%N L j)) a - (e%:num / #|` L |%:R)%:E < \sum_(s <- Fj) a s))%E.
have [Fj csumFj] : exists F, forall j, P (F j) j.
  suff : forall j, exists Fj, P Fj j.
    by case/(@choice _ _ (fun i F => P F i)) => Fj ?; exists Fj.
  move=> j; rewrite /P /csum (negbTE (J0 _)); set es := ereal_sup _.
  have [esoo|[c c0 esc]] : es = +oo%E \/ exists2 r, r >= 0 & es = r%:E.
    suff : (0%:E <= es)%E by move/gee0P.
    by apply ereal_sup_ub; exists fset0 => //; rewrite big_nil.
  - move: csumIar; rewrite /csum (negbTE I0); set es' := ereal_sup _ => es'r.
    suff : (es <= es')%E by rewrite esoo es'r.
    apply: le_ereal_sup => x [F FJ Fx]; exists F => //.
    move/subset_trans : FJ; apply => t Jt.
    by exists (nth 0%N L j) => //; apply LK; rewrite /mkset mem_nth.
  - have eL0 : 0 < e%:num / #|` L |%:R by rewrite divr_gt0 // ltr0n cardfs_gt0.
    rewrite (_ : e%:num / _ = (PosNum eL0)%:num) // esc.
    exact: ub_ereal_sup_adherent2.
pose F := \big[fsetU/fset0]_(i < #|`L|) Fj i.
apply: (@le_trans _ _ (\sum_(i <- F) a i)%E); last first.
  rewrite /csum (negbTE I0); apply ereal_sup_ub; exists F => //.
  move=> t /bigfcupP[/= i _] /(proj1 (csumFj i)) Jt.
  by exists (nth 0%N L i) => //; apply LK; rewrite /mkset mem_nth.
apply: (@le_trans _ _ (\sum_(i < #|`L|) (\sum_(j <- Fj i) a j)%E)%E); last first.
  have tFj : (forall i j : 'I_#|`L|, i != j -> [disjoint Fj i & Fj j])%fset.
    move=> i j ij; rewrite -fsetI_eq0.
    suff : (Fj i `&` Fj j)%fset == fset0 by [].
    rewrite -eq_set0_fset0.
    have Jij : J (nth 0%N L i) `&` J (nth 0%N L j) = set0.
      apply: tJ => //; apply: contra ij => /eqP /(congr1 (index^~ L)).
      by rewrite index_uniq // index_uniq // => /ord_inj ->.
    apply/eqP; rewrite predeqE => t; split => //; rewrite /mkset inE => /andP[].
    by move=> /(proj1 (csumFj i)) ? /(proj1 (csumFj j)) ?; rewrite -Jij; split.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/esym.
  pose IL := [fset i | i in 'I_#|`L|]%fset.
  have -> : F = (\bigcup_(i <- IL) Fj i)%fset
    by rewrite /IL big_imfset //= big_enum.
  transitivity ((\sum_(i <- IL) (\sum_(j <- Fj i) a j)%E)%E); last first.
    by rewrite /IL big_imfset //= big_enum.
  by apply partition_disjoint_bigfcup; exact: tFj.
rewrite (_ : e%:num = \sum_(i < #|`L|) (e%:num / #|`L|%:R)); last first.
  rewrite big_const iter_addr addr0 card_ord -mulr_natr.
  by rewrite -mulrA mulVr ?mulr1 // unitfE pnatr_eq0 cardfs_eq0.
rewrite -NERFin (@big_morph _ _ _ 0 _ _ _ (@opprD R)) ?oppr0 //.
rewrite (@big_morph _ _ _ 0%:E _ _ _ addERFin) // -big_split /=.
by apply: lee_sum => /= i _; exact: (ltW (proj2 (csumFj i))).
Qed.
