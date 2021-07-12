(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets posnum topology normedtype sequences measure.

(******************************************************************************)
(*                     WIP about Simple Functions                             *)
(*                                                                            *)
(* This file contains a tentative definition of simple functions and of their *)
(* integration with the proof that the latter is semi-linear for non-negative *)
(* simple functions.                                                          *)
(*                                                                            *)
(*         sfun == type of simple functions                                   *)
(*     sfun_cst == constant simple function                                   *)
(*   sfun_scale == scaling of simple functions                                *)
(* sfun_add f g == addition of simple functions                               *)
(*       nnsfun == type of non-negative simple functions                      *)
(*    sintegral == integral of a simple function                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* NB: PR in progress *)
Lemma bigcup_mkset_cond (T : choiceType) U (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcup_(t in [set x | (x \in s) && P x]) (f t) = \big[setU/set0]_(t <- s | P t) (f t).
Proof.
elim: s => [/=|h s ih]; first by rewrite mkset_nil bigcup_set0 big_nil.
rewrite big_cons -ih predeqE => u; split=> [[t /andP[]]|].
- rewrite inE => /orP[/eqP ->{t} -> fhu|ts Pt ftu]; first by left.
  case: ifPn => Ph; first by right; exists t => //; apply/andP; split.
  by exists t => //; apply/andP; split.
- case: ifPn => [Ph [fhu|[t /andP[ts Pt] ftu]]|Ph [t /andP[ts Pt ftu]]].
  + by exists h => //; apply/andP; split => //; rewrite mem_head.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
Qed.
(* /NB: PR in progress *)

Section additive_lemmas.
Variables (T : measurableType) (R : realType) (m : {measure set T -> \bar R}).

Lemma additive_ord n (F : 'I_n -> set T) :
  (forall i : 'I_n, measurable (F i)) -> trivIset setT F ->
  m (\big[setU/set0]_(i < n) F i) = (\sum_(i < n) m (F i))%E.
Proof.
move=> mF tF.
pose F' i := if (i < n)%N =P true is ReflectT ni then F (Ordinal ni) else set0.
rewrite [X in m X](_ : _ = \big[setU/set0]_(i < n) F' i); last first.
  rewrite (bigID (fun i => F i == set0))/= big1 ?set0U//; last by move=> ? /eqP.
  rewrite big_mkcond; apply eq_bigr => // i _.
  rewrite /F'; case: eqP => [?|]; last by rewrite ltn_ord.
  by case: ifPn => [Fi0|/negPn/eqP <-]; congr F; exact/val_inj.
move: (@measure_additive _ _ (measure_additive_measure m)) => ->; last 2 first.
  - by move=> i; rewrite /F'; case: eqP => // _; exact: measurable0.
  - apply/trivIsetP => i j _ _ ij; rewrite /F'.
    case: eqP => ni; last by rewrite set0I.
    case: eqP => nj; last by rewrite setI0.
    by move/trivIsetP : tF; apply.
rewrite [in RHS](bigID (fun i => F i == set0)) /=.
rewrite [in RHS]big1 ?add0e//; last by move=> ? /eqP ->; rewrite measure0.
rewrite [in RHS]big_mkcond /=; apply eq_bigr => i _.
rewrite /F'; case: eqP => [?|]; last by rewrite ltn_ord.
rewrite -(measure0 (measure_additive_measure m)).
by case: ifPn => [Fi0|/negPn/eqP <-]; congr (m (F _)); exact/val_inj.
Qed.

Lemma additive_ord_cond n (F : 'I_n -> set T) P :
  (forall i : 'I_n, measurable (F i)) -> trivIset setT F ->
  m (\big[setU/set0]_(i < n | P i) F i) = (\sum_(i < n | P i) m (F i))%E.
Proof.
move=> mF tF; rewrite big_mkcond additive_ord.
- by rewrite [in RHS]big_mkcond /=; apply eq_bigr => i _; case: ifPn.
- by move=> i; case: ifPn => // _; exact: measurable0.
- apply/trivIsetP => i j _ _ ij; case: ifPn => // Pi; last by rewrite set0I.
  case: ifPn => Pj; last by rewrite setI0.
  by move/trivIsetP : tF; apply.
Qed.

Lemma additive_set (I : finType) (F : I -> set T) (P : {set I}) :
  (forall i : I, measurable (F i)) -> trivIset setT F ->
  m (\big[setU/set0]_(i in P) F i) = (\sum_(i in P) m (F i))%E.
Proof.
move=> mF tF.
have [/eqP ->|/set0Pn[k kP]] := boolP (P == finset.set0).
  by rewrite 2!big_set0 measure0.
rewrite big_tnth /= additive_ord_cond //; first by rewrite [in RHS]big_tnth.
apply/trivIsetP => /= i j _ _ ij; move/trivIsetP : tF; apply => //.
apply: contra ij.
by rewrite 2!(tnth_nth k) nth_uniq // index_enum_uniq.
Qed.

End additive_lemmas.

Module SFun.
Section sfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f :> T -> R ;
  codom : seq R ;
  uniq_codom : uniq codom ;
  fcodom : forall t, f t \in codom ;
  pi := fun k : 'I_(size codom) => f @^-1` [set codom`_k] ;
  mpi : forall k, measurable (pi k) }.
Definition ssize f := size (codom f).
End sfun.
Module Exports.
Notation sfun := SFun.t.
Notation ssize := ssize.
End Exports.
End SFun.
Export SFun.Exports.
Arguments SFun.pi {T} {R} _.
Coercion SFun.f : sfun >-> Funclass.

Section simple_function_partition.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.
Let pi := SFun.pi f.

Lemma trivIset_sfun (A : set 'I_n) : trivIset A pi.
Proof.
apply/trivIsetP => /=; rewrite -/n => i j _ _ ij.
suff ij0 : [set (SFun.codom f)`_i] `&` [set (SFun.codom f)`_j] = set0.
  by rewrite /pi /SFun.pi -preimage_setI ij0 preimage_set0.
apply/eqP/negPn/negP => /set0P[r []]; rewrite /set1 /= => ->{r} /eqP.
by rewrite nth_uniq => //; [exact/negP | exact: SFun.uniq_codom].
Qed.

Lemma bigcup_sfun : \big[setU/set0]_(i < n) pi i = setT.
Proof.
rewrite predeqE => t; split => // _; rewrite -bigcup_mkset -preimage_bigcup.
have /(nthP 0)[i ni fit] := SFun.fcodom f t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

End simple_function_partition.

Section sfun_lemmas.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.

Local Lemma ltn_pidx x : (index (f x) (SFun.codom f) < n)%N.
Proof. by rewrite index_mem SFun.fcodom. Qed.

Definition pidx x := Ordinal (ltn_pidx x).

Lemma nth_pidx x : (SFun.codom f)`_(pidx x) = f x.
Proof. by rewrite nth_index //; exact: SFun.fcodom. Qed.

Lemma pi_pidx x : SFun.pi f (pidx x) x.
Proof. by rewrite /SFun.pi /preimage /set1 /mkset nth_pidx. Qed.

Lemma pi_nth i x : SFun.pi f i x -> (SFun.codom f)`_i = f x.
Proof. by []. Qed.

End sfun_lemmas.

Section sfun_cst.
Variables (T : measurableType) (R : realType) (r : R).
Let a := [:: r].

Local Lemma sfun_cst_uniq : uniq a. Proof. by []. Qed.

Local Lemma sfun_cst_fcodom (t : T) : (cst r) t \in a.
Proof. by rewrite inE eqxx. Qed.

Local Lemma sfun_cst_mpi : let pi := fun k : 'I_1 => (@cst T R r) @^-1` [set a`_k] in
  (forall k : 'I_1, measurable (pi k)).
Proof.
move=> pi k; rewrite (_ : pi _ = setT); last first.
  by rewrite predeqE => t; split => // _; rewrite (ord1 k).
exact: measurableT.
Qed.

Definition sfun_cst : sfun T R :=
  @SFun.mk T R (cst r) a sfun_cst_uniq sfun_cst_fcodom sfun_cst_mpi.

Lemma ssize_sfun_cst : ssize sfun_cst = 1%N.
Proof. by []. Qed.

End sfun_cst.

Section simple_function_scale.
Variables (T : measurableType) (R : realType) (r : R) (f : sfun T R).
Let n := ssize f.
Let a : seq R := if r == 0 then [:: 0] else [seq r * x | x <- SFun.codom f].

Local Lemma sfun_scale_uniq : uniq a.
Proof.
have [/eqP r0|r0] := boolP (r == 0).
  by rewrite /a r0 eqxx.
rewrite /a (negbTE r0) map_inj_uniq; first exact: SFun.uniq_codom.
by apply: mulrI; rewrite unitfE.
Qed.

Local Lemma sfun_scale_fcodom t : (fun x => r * f x) t \in a.
Proof.
have [/eqP r0|r0] := boolP (r == 0); first by rewrite r0 mul0r /a r0 eqxx inE.
by rewrite /a (negbTE r0); apply/mapP; exists (f t) => //; exact: SFun.fcodom.
Qed.

Local Lemma sfun_scale_mpi (k : 'I_(size a)) : measurable ((fun x => r * f x) @^-1` [set a`_k]).
Proof.
have [/eqP r0|r0] := boolP (r == 0).
  move: k.
  rewrite /a r0 eqxx /= => k; rewrite (_ : mkset _ = setT); first exact: measurableT.
  by rewrite predeqE => t; split => // _; rewrite /set1 /mkset (ord1 k) mul0r.
move=> [:k'n].
have @k' : 'I_(ssize f).
  apply: (@Ordinal _ k); abstract: k'n.
  by rewrite /ssize /= (leq_trans (ltn_ord k)) // /a (negbTE r0) size_map.
rewrite (_ : _ @^-1` _ = SFun.pi f k'); first exact: SFun.mpi.
rewrite predeqE => t; split => //.
  rewrite /a /preimage /set1 /mkset {1}(negbTE r0).
  by rewrite  (nth_map 0) //; apply: mulrI; rewrite unitfE.
rewrite /SFun.pi /preimage /set1 /mkset => ->.
by rewrite /a {1}(negbTE r0) (nth_map 0).
Qed.

Definition sfun_scale : sfun T R :=
  SFun.mk sfun_scale_uniq sfun_scale_fcodom  sfun_scale_mpi.

End simple_function_scale.

Section simple_function_addition.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.
Let a : seq R := undup [seq x + y | x <- SFun.codom f, y <- SFun.codom g].

Let fga t : (f \+ g) t \in a.
Proof.
rewrite /a mem_undup; apply/allpairsP; exists (f t, g t) => /=.
by split => //; [exact: SFun.fcodom | exact: SFun.fcodom].
Qed.

Let mfg (k : 'I_(size a)) : measurable ((f \+ g) @^-1` [set a`_k]).
Proof.
rewrite (_ : _ @^-1` _ =
    \bigcup_(x in [set x : 'I_n * 'I_p | a`_k == (SFun.codom f)`_x.1 + (SFun.codom g)`_x.2])
    (SFun.pi f x.1 `&` SFun.pi g x.2)); last first.
  rewrite predeqE => t; split=> [fgt|[[i j] /= /eqP -> [] -> ->]//].
  exists (pidx f t, pidx g t) => /=.
    by rewrite !nth_pidx -fgt.
  by split => //; exact: pi_pidx.
rewrite (_ : \bigcup_(_ in _) _ =
    \big[setU/set0]_(z <- [seq (x, y) | x <- enum 'I_n, y <- enum 'I_p] |
                     a`_k == (SFun.codom f)`_z.1 + (SFun.codom g)`_z.2)
    (SFun.pi f z.1 `&` SFun.pi g z.2)); last first.
  rewrite -bigcup_mkset_cond predeqE => t; split=> [[[i j] /= afg [/= ft gt]]|].
    exists (pidx f t, pidx g t) => /=; last by split; exact: pi_pidx.
    apply/andP; split => //=.
      apply/flattenP;  exists [seq (pidx f t, x) | x <- enum 'I_p].
        by apply/mapP; exists (pidx f t) => //; rewrite mem_enum.
      by apply/mapP; exists (pidx g t) => //; rewrite mem_enum.
    by rewrite (eqP afg) !nth_pidx (pi_nth ft) (pi_nth gt).
  by case => /= -[i j] /= /andP[H aij] [? ?]; exists (i, j).
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; apply SFun.mpi.
Qed.

Definition sfun_add : sfun T R := SFun.mk (undup_uniq _) fga mfg.

Definition sfun_add_pidx (c : 'I_(ssize sfun_add)) :=
  [set x in finset.setX [set: 'I_n] [set: 'I_p] |
   (SFun.codom f)`_x.1 + (SFun.codom g)`_x.2 == (SFun.codom sfun_add)`_c]%SET.

Lemma pi_sfun_addE (c : 'I_(ssize sfun_add)) : SFun.pi sfun_add c =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_add_pidx c) (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
rewrite predeqE => t; split.
- move=> fgtc.
  rewrite -bigcup_mkset_cond; exists (pidx f t, pidx g t) => //=.
    by rewrite mem_index_enum /= 4!inE /= 2!nth_pidx (pi_nth fgtc).
  by split; exact: pi_pidx.
- rewrite -bigcup_mkset_cond => -[[/= i j]].
  rewrite mem_index_enum /= !inE /= => /eqP ijc [fit gjt].
  by rewrite {1}/SFun.pi /preimage /= /set1 /mkset -ijc; congr (_ + _).
Qed.

Lemma sfun_add_pi_cover :
  \bigcup_(c < ssize sfun_add) sfun_add_pidx c = finset.setX [set: 'I_n] [set: 'I_p].
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP => /=.
have : (SFun.codom f)`_k + (SFun.codom g)`_l \in undup [seq x0 + y | x0 <- SFun.codom f, y <- SFun.codom g].
  rewrite mem_undup; apply/flattenP.
  exists [seq (SFun.codom f)`_k + y | y <- SFun.codom g].
    by apply/mapP; exists (SFun.codom f)`_k => //; apply/(nthP 0); exists k.
  by apply/mapP; exists (SFun.codom g)`_l => //; apply/(nthP 0); exists l.
move=> /(nthP 0)[x Hx] xkl.
have xfg : (x < ssize sfun_add)%N by rewrite (leq_trans Hx).
by exists (Ordinal xfg) => //; rewrite !inE /= xkl.
Qed.

Lemma trivIset_sfunI :
  trivIset setT (fun i : 'I_n * 'I_p => SFun.pi f i.1 `&` SFun.pi g i.2).
Proof.
apply/trivIsetP => /= -[k l] [k' l'] _ _ /=.
rewrite xpair_eqE negb_and => /orP[kk'|ll'].
  rewrite setIACA (_ : SFun.pi f k `&` _ = set0) ?set0I//.
  by move/trivIsetP : (@trivIset_sfun _ _ f setT) => /(_ k k' Logic.I Logic.I kk').
rewrite setIACA (_ : SFun.pi g l `&` _ = set0) ?setI0//.
by move/trivIsetP : (@trivIset_sfun _ _ g setT) => /(_ l l' Logic.I Logic.I ll').
Qed.

Lemma measure_sfun_add_pi (mu : {measure set T -> \bar R}) (c : 'I_(ssize sfun_add)) :
  mu (SFun.pi sfun_add c) =
  (\sum_(kl in sfun_add_pidx c) mu (SFun.pi f kl.1 `&` SFun.pi g kl.2))%E.
Proof.
rewrite pi_sfun_addE (additive_set mu _ _ trivIset_sfunI) //=.
by move=> -[i j]; apply: measurableI; exact: SFun.mpi.
Qed.

End simple_function_addition.

Module NNSFun.
Section nnsfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f : sfun T R ;
  ge0 : forall k, 0 <= (SFun.codom f)`_k }.
End nnsfun.
Module Exports.
Notation nnsfun := NNSFun.t.
End Exports.
End NNSFun.
Export NNSFun.Exports.
Coercion NNSFun.f : nnsfun >-> sfun.

Section simple_function_scale_lemmas.
Variables (T : measurableType) (R : realType) (r : R) (f : nnsfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma ssize_sfun_scale0 : ssize (sfun_scale 0 f) = 1%N.
Proof. by rewrite /ssize /= eqxx. Qed.

Lemma ssize_sfun_scale_neq0 : r != 0 -> ssize (sfun_scale r f) = ssize f.
Proof. by move=> r0; rewrite /ssize /= (negbTE r0) size_map. Qed.

End simple_function_scale_lemmas.

Section simple_function_integral.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.
Let A := SFun.pi f.
Let a := SFun.codom f.

Definition sintegral (m : {measure set T -> \bar R}) : \bar R :=
  (\sum_(k < n) (a`_k)%:E * m (A k))%E.

End simple_function_integral.

Section sintegralK.
Variables (T : measurableType) (R : realType) (r : R) (f : nnsfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma sintegralK : sintegral (sfun_scale r f) m = (r%:E * sintegral f m)%E.
Proof.
have [/eqP ->|r0] := boolP (r == 0).
  rewrite mul0e /sintegral big1 // => i _; rewrite /= eqxx /=.
  case: (m (SFun.pi _ _)) => [x| |]; move: i; rewrite ssize_sfun_scale0 => i.
  by rewrite (ord1 i) /= mul0r.
  by rewrite (ord1 i) /= eqxx.
  by rewrite (ord1 i) /= eqxx.
rewrite /sintegral.
pose cast := cast_ord (ssize_sfun_scale_neq0 f r0).
rewrite [LHS](eq_bigr (fun k : 'I_(ssize (sfun_scale r f)) =>
  (r * (SFun.codom f)`_(cast k))%:E * m (SFun.pi f (cast k)))%E); last first.
  move=> i _; congr (_%:E * m _)%E.
    rewrite /= (negbTE r0) (nth_map 0) //.
    by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
  rewrite predeqE => x; split.
    rewrite /SFun.pi /= /set1 /= {1}(negbTE r0) (nth_map 0); last first.
      by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
    by move/mulrI; apply; rewrite unitfE.
  rewrite /SFun.pi /set1 /= => ->.
  rewrite {1}(negbTE r0) (nth_map 0) //.
  by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
rewrite sume_distrr; last first.
  move=> i _; rewrite mule_ge0 //; first exact: NNSFun.ge0.
  by apply: measure_ge0; apply: SFun.mpi.
pose castK := cast_ord (esym (ssize_sfun_scale_neq0 f r0)).
rewrite (@reindex _ _ _ [finType of 'I_(ssize (sfun_scale r f))]
    [finType of 'I_(ssize f)] castK); last first.
  exists cast => i.
    by rewrite /cast /castK /= cast_ordKV.
  by rewrite /cast /castK /= cast_ordK.
apply eq_bigr => i _.
by rewrite /cast /castK cast_ordKV mulEFin muleA.
Qed.

End sintegralK.

Section sintegralD.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).
Variables (m : {measure set T -> \bar R}).
Let n := ssize f.
Let p := ssize g.

Lemma sintegralD : sintegral (sfun_add f g) m = (sintegral f m + sintegral g m)%E.
Proof.
transitivity (\sum_(i < n) \sum_(l < p)
  ((SFun.codom f)`_i + (SFun.codom g)`_l)%:E * m (SFun.pi f i `&` SFun.pi g l))%E.
  rewrite /sintegral.
  under eq_bigr do rewrite measure_sfun_add_pi.
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g))) (\sum_(x in sfun_add_pidx i)
    ((SFun.codom f)`_x.1 + (SFun.codom g)`_x.2)%:E * m (SFun.pi f x.1 `&` SFun.pi g x.2)))%E.
    apply eq_bigr => i _; rewrite sume_distrr //; last first.
      by move=> kl _; rewrite measure_ge0 //; apply: measurableI; exact: SFun.mpi.
    by apply eq_bigr => x; rewrite !inE 2!andTb => /eqP ->.
  rewrite [in RHS]pair_big.
  transitivity (\sum_(p0 in setX [set: 'I_n] [set: 'I_p])
    (((SFun.codom f)`_p0.1 + (SFun.codom g)`_p0.2)%:E * m (SFun.pi f p0.1 `&` SFun.pi g p0.2)))%E; last first.
    by apply/eq_bigl => // -[/= k l]; rewrite !inE.
  rewrite -sfun_add_pi_cover partition_disjoint_bigcup // => i j ij.
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[-[/= k l]].
  rewrite !inE /= => /andP[/eqP ->].
  by rewrite (nth_uniq _ _ _ (undup_uniq _)) //; exact/negP.
rewrite /sintegral -/n -/p [RHS]addeC.
have ggf : forall k, m (SFun.pi g k) = (\sum_(i < n) m (SFun.pi g k `&` SFun.pi f i))%E.
  move=> k; rewrite -[in LHS](setIT (SFun.pi g k)) -(bigcup_sfun f) big_distrr /=.
  rewrite additive_ord //; last exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; exact: SFun.mpi.
under [X in _ = (X + _)%E]eq_bigr do rewrite ggf; rewrite {ggf}.
transitivity
  (\sum_(i < p) (\sum_(j < n) ((SFun.codom g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f j)) +
   \sum_(k < n) ((SFun.codom f)`_k)%:E * m (SFun.pi f k))%E; last first.
  congr adde; apply eq_bigr => i _.
  rewrite sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; exact: SFun.mpi.
have ffg : forall k, m (SFun.pi f k) = (\sum_(l < p) m (SFun.pi f k `&` SFun.pi g l))%E.
  move=> k; rewrite -[in LHS](setIT (SFun.pi f k)) -(bigcup_sfun g) big_distrr /=.
  rewrite additive_ord //; last exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; exact: SFun.mpi.
under [X in _ = (_ + X)%E]eq_bigr do rewrite ffg; rewrite {ffg}.
transitivity (\sum_(i < p) \sum_(i0 < n) ((SFun.codom g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f i0) +
  \sum_(i < n) \sum_(l < p) ((SFun.codom f)`_i)%:E * m (SFun.pi f i `&` SFun.pi g l))%E; last first.
  congr adde; apply eq_bigr => i _.
  rewrite sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; exact: SFun.mpi.
rewrite [X in _ = (X + _)%E]exchange_big.
rewrite -big_split; apply eq_bigr => i _.
rewrite -big_split; apply eq_bigr => j _.
rewrite [in RHS]setIC.
rewrite addEFin ge0_muleDl; try exact: NNSFun.ge0.
by rewrite addeC.
Qed.

End sintegralD.
