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
  fcodom : f @` setT = [set x | x \in codom] ;
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

Lemma SFunfcodom t : f t \in SFun.codom f.
Proof.
have := SFun.fcodom f.
rewrite predeqE.
move=> /(_ (f t))[+ _].
by apply; exists t.
Qed.

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
have /(nthP 0)[i ni fit] := SFunfcodom t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

End simple_function_partition.

Section sfun_lemmas1.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.

Local Lemma ltn_pidx x : (index (f x) (SFun.codom f) < n)%N.
Proof. by rewrite index_mem SFunfcodom. Qed.

Definition pidx x := Ordinal (ltn_pidx x).

Lemma nth_pidx x : (SFun.codom f)`_(pidx x) = f x.
Proof. by rewrite nth_index //; exact: SFunfcodom. Qed.

Lemma pi_pidx x : SFun.pi f (pidx x) x.
Proof. by rewrite /SFun.pi /preimage /set1 /mkset nth_pidx. Qed.

Lemma pi_nth i x : SFun.pi f i x -> (SFun.codom f)`_i = f x.
Proof. by []. Qed.

Lemma sfun_ge0  : (forall t, 0 <= f t) -> forall k : 'I_(ssize f), 0 <= (SFun.codom f)`_k.
Proof.
case: f => /= f_ c uc fc mpi f0 k.
have : [set x | x \in c] (c`_k).
  by apply/(nthP 0); exists k.
by rewrite -fc => -[x _ <-]; exact: f0.
Qed.

End sfun_lemmas1.

Section sfun_lemmas2.
Variables (T : measurableType) (R : realType).

Local Lemma sfun_ext_helper (f g : sfun T R) : f =1 g ->
  {subset SFun.codom f <= SFun.codom g}.
Proof.
move=> fg r rf.
have := SFun.fcodom g; rewrite predeqE => /(_ r)[+ _].
apply => /=.
have := SFun.fcodom f; rewrite predeqE => /(_ r)[_].
by move/(_ rf) => [t _ <-]; exists t.
Qed.

Lemma sfun_ext (f g : sfun T R) : f =1 g -> perm_eq (SFun.codom f) (SFun.codom g).
Proof.
move=> fg; apply: uniq_perm; try exact: SFun.uniq_codom.
by move=> r; apply/idP/idP; exact: sfun_ext_helper.
Qed.

Lemma sfun_size (f g : sfun T R) : f =1 g -> ssize f = ssize g.
Proof.
move/sfun_ext => fg.
by rewrite /ssize; apply: perm_size.
Qed.

End sfun_lemmas2.

Section sfun_cst.
Variables (T : measurableType) (point : T). (*NB: measurablePointedType? *)
Variables (R : realType) (r : R).
Let s := [:: r].
Let f : T -> R := cst r.

Local Lemma sfun_cst_uniq : uniq s. Proof. by []. Qed.

Local Lemma sfun_cst_fcodom : f @` setT = [set x | x \in s].
Proof.
rewrite predeqE => r'; split; first by move=> [t _ <-]; rewrite /s /= inE.
by rewrite /s /= inE => /eqP ->{r'}; exists point.
Qed.

Let pi := fun k : 'I_1 => f @^-1` [set s`_k].

Local Lemma sfun_cst_mpi (k : 'I_1) : measurable (pi k).
Proof.
rewrite (_ : pi _ = setT); first exact: measurableT.
by rewrite predeqE => t; split => // _; rewrite (ord1 k).
Qed.

Local Lemma sfun_cst_mpi0 (k : 'I_1) : pi k !=set0.
Proof.
by rewrite /pi /s (ord1 k) /= /mkset /set1 /mkset; exists point.
Qed.

Definition sfun_cst :=  SFun.mk sfun_cst_uniq sfun_cst_fcodom sfun_cst_mpi.

Lemma ssize_sfun_cst : ssize sfun_cst = 1%N. Proof. by []. Qed.

End sfun_cst.

Section simple_function_scale.
Variables (T : measurableType) (point : T). (*NB: measurablePointedType? *)
Variables (R : realType) (r : R) (f : sfun T R).
Let n := ssize f.
Let s := if r == 0 then [:: 0] else [seq r * x | x <- SFun.codom f].
Let g := fun x => r * f x.

Local Lemma sfun_scale_uniq : uniq s.
Proof.
have [/eqP r0|r0] := boolP (r == 0); first by rewrite /s r0 eqxx.
rewrite /s (negbTE r0) map_inj_uniq; first exact: SFun.uniq_codom.
by apply: mulrI; rewrite unitfE.
Qed.

Local Lemma sfun_scale_fcodom : g @` setT = [set x | x \in s].
Proof.
rewrite predeqE => r'; split.
  case => t _ <-{r'}.
  rewrite /mkset /s.
  have [/eqP r0|r0] := boolP (r == 0);first by rewrite /g r0 mul0r inE.
  by apply/mapP; exists (f t) => //; exact: SFunfcodom.
rewrite /= /s.
have [/eqP r0|r0 /mapP[r'']] := boolP (r == 0).
  by rewrite inE => /eqP ->{r'}; exists point => //; rewrite /g r0 mul0r.
have := SFun.fcodom f.
rewrite predeqE => /(_ r'') /= [_ /[apply]] [t] _ <-{r''} ->{r'}.
by exists t.
Qed.

Let pi := fun k => g @^-1` [set s`_k].

Local Lemma sfun_scale_mpi (k : 'I_(size s)) : measurable (pi k).
Proof.
have [/eqP r0|r0] := boolP (r == 0).
  move: k.
  rewrite /pi /s r0 eqxx /= => k; rewrite (_ : mkset _ = setT); first exact: measurableT.
  by rewrite predeqE => t; split => // _; rewrite /set1 /mkset (ord1 k) /g r0 mul0r.
move=> [:k'n].
have @k' : 'I_n.
  apply: (@Ordinal _ k); abstract: k'n.
  by rewrite /ssize /= (leq_trans (ltn_ord k)) // /s (negbTE r0) size_map.
rewrite /pi (_ : _ @^-1` _ = SFun.pi f k'); first exact: SFun.mpi.
rewrite predeqE => t; split => //.
  rewrite /s /preimage /set1 /mkset {1}(negbTE r0).
  by rewrite (nth_map 0) //; apply: mulrI; rewrite unitfE.
rewrite /SFun.pi /preimage /set1 /mkset /g => ->.
by rewrite /s {1}(negbTE r0) (nth_map 0).
Qed.

Definition sfun_scale := SFun.mk sfun_scale_uniq sfun_scale_fcodom sfun_scale_mpi.

End simple_function_scale.

Section simple_function_scale_lemmas.
Variables (T : measurableType) (point : T) (R : realType) (r : R) (f : sfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma ssize_sfun_scale0 : ssize (sfun_scale point 0 f) = 1%N.
Proof. by rewrite /ssize /= eqxx. Qed.

Lemma ssize_sfun_scale_neq0 : r != 0 -> ssize (sfun_scale point r f) = ssize f.
Proof. by move=> r0; rewrite /ssize /= (negbTE r0) size_map. Qed.

Lemma sfun_scale0 : sfun_scale point 0 f = sfun_cst point 0.
Proof.
Abort.

End simple_function_scale_lemmas.

Section simple_function_addition.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.
Let a := seq.filter (fun z => (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0)
  [seq (x, y) | x <- SFun.codom f, y <- SFun.codom g].
Let s : seq R := undup (map (fun z => z.1 + z.2) a).

Let fga : (f \+ g) @` setT = [set x | x \in s].
Proof.
rewrite predeqE => r; split.
- rewrite /= => -[t _] <-.
  rewrite /s mem_undup.
  apply/mapP; exists (f t, g t) => //.
  rewrite mem_filter /=; apply/andP; split.
    rewrite /mkset /set1 /mkset.
    by apply/set0P; exists t.
  apply/allpairsP.
  by exists (f t, g t); split => //; apply SFunfcodom.
- rewrite /= /s mem_undup.
  move/mapP => [[i j]].
  rewrite mem_filter /= => /andP[/set0P[t []]].
  rewrite /mkset /set1 /mkset => fti gtj.
  move=> /allpairsP[[i' j']] /= [fi' gj'] [? ?]; subst i' j' => ->.
  by exists t => //; rewrite fti gtj.
Qed.

Definition sfun_add_pidx (k : 'I_(size s)) :=
  [set x : 'I_n * 'I_p | ((SFun.codom f)`_x.1 + (SFun.codom g)`_x.2 == s`_k) &&
    (SFun.pi f x.1 `&` SFun.pi g x.2 != set0)]%SET.

Local Lemma sfun_add_preimageE (k : 'I_(size s)) : (f \+ g) @^-1` [set s`_k] =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_add_pidx k)
    (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity (\big[setU/set0]_(x : 'I_n * 'I_p |
     (SFun.codom f)`_x.1 + (SFun.codom g)`_x.2 == s`_k)
    (SFun.pi f x.1 `&` SFun.pi g x.2)); last first.
  rewrite /sfun_add_pidx big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => /= -[i j] _ /=.
  rewrite inE /=.
  case: ifPn => //= _.
  case: ifPn => //.
  by rewrite negbK => /eqP.
rewrite -bigcup_mkset_cond.
rewrite predeqE => t; split=> [fgt|].
  exists (pidx f t, pidx g t) => /=.
    by rewrite !nth_pidx -fgt // mem_index_enum eqxx.
  by split => //; exact: pi_pidx.
move=> [[i j]] /=.
by rewrite mem_index_enum /= => /eqP <- [-> ->].
Qed.

Local Lemma sfun_add_bigcupIE (k : 'I_(size s)) :
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_add_pidx k)
    (SFun.pi f x.1 `&` SFun.pi g x.2) =
  \big[setU/set0]_(z <- [seq (x, y) | x <- enum 'I_n, y <- enum 'I_p] |
                     z \in sfun_add_pidx k)
    (SFun.pi f z.1 `&` SFun.pi g z.2).
Proof.
rewrite -[in RHS]bigcup_mkset_cond -bigcup_mkset_cond.
rewrite predeqE => t; split=> [[[i j] /=]|].
  rewrite !inE /= => /andP[] _ /andP[] /eqP afg fg0 [/= ft gt].
  exists (pidx f t, pidx g t) => /=; last by split; exact: pi_pidx.
  apply/andP; split => //=.
    apply/flattenP;  exists [seq (pidx f t, x) | x <- enum 'I_p].
      by apply/mapP; exists (pidx f t) => //; rewrite mem_enum.
    by apply/mapP; exists (pidx g t) => //; rewrite mem_enum.
  rewrite !inE /= !nth_pidx.
  rewrite -afg (pi_nth ft) (pi_nth gt) eqxx /=.
  by apply/set0P; exists t; split; exact: pi_pidx.
case => /= -[i j] /= /andP[H aij] [? ?]; exists (i, j) => //.
by rewrite /= mem_index_enum.
Qed.

Lemma sfun_add_pi_cover0 : \bigcup_(c < size s) sfun_add_pidx c =
  [set x : {: 'I_n * 'I_p}|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET.
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP/idP => /=.
- move=> [i] _.
  by rewrite inE /= => /eqP/eqP/andP[].
- move=> kl.
  have [i kli] : exists i : 'I_(size s), (SFun.codom f)`_k + (SFun.codom g)`_l = s`_i.
    have : (SFun.codom f)`_k + (SFun.codom g)`_l \in [set of f \+ g].
      rewrite inE /=.
      move/set0P : kl => [t [/pi_nth kt /pi_nth lt]].
      by exists t => //; rewrite -kt -lt.
    by rewrite fga inE /= => /(nthP 0)[x xa H]; exists (Ordinal xa).
  by exists i => //; rewrite inE /= kli eqxx.
Qed.

Let mfg (k : 'I_(size s)) : measurable ((f \+ g) @^-1` [set s`_k]).
Proof.
rewrite sfun_add_preimageE sfun_add_bigcupIE.
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; apply SFun.mpi.
Qed.

Definition sfun_add := SFun.mk (undup_uniq _) fga mfg.

End simple_function_addition.

Section simple_function_addition_lemmas.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.

Lemma pi_sfun_addE (c : 'I_(ssize (sfun_add f g))) : SFun.pi (sfun_add f g) c =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_add_pidx c) (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity ((sfun_add f g) @^-1` [set (SFun.codom (sfun_add f g))`_c]) => //.
by rewrite sfun_add_preimageE.
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

Lemma measure_sfun_add_pi (mu : {measure set T -> \bar R}) (c : 'I_(ssize (sfun_add f g))) :
  mu (SFun.pi (sfun_add f g) c) =
  (\sum_(kl in sfun_add_pidx c) mu (SFun.pi f kl.1 `&` SFun.pi g kl.2))%E.
Proof.
rewrite pi_sfun_addE (additive_set mu _ _ trivIset_sfunI) //=.
by move=> -[i j]; apply: measurableI; exact: SFun.mpi.
Qed.

End simple_function_addition_lemmas.

Module NNSFun.
Section nnsfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f : sfun T R ;
  ge0 : forall k : 'I_(ssize f), 0 <= (SFun.codom f)`_k }.
End nnsfun.
Module Exports.
Notation nnsfun := t.
End Exports.
End NNSFun.
Export NNSFun.Exports.
Coercion NNSFun.f : nnsfun >-> sfun.

Section nnsfun_lemmas.
Variables (T : measurableType) (R : realType).

Lemma NNSFun_ge0  (f : nnsfun T R) (x : T) : 0 <= f x.
Proof.
have : (f @` @setT T) (f x) by exists x.
rewrite (SFun.fcodom f) /mkset => /(nthP 0)[k kf <-].
by have := NNSFun.ge0 (Ordinal kf).
Qed.

Definition mk_nnsfun (f : sfun T R) (H : forall t, 0 <= f t) : nnsfun T R :=
  NNSFun.mk (sfun_ge0 H).

End nnsfun_lemmas.

Section simple_function_integral.
Variables (T : measurableType) (R : realType) (m : {measure set T -> \bar R})
  (f : sfun T R).
Let n := ssize f.
Let A := SFun.pi f.
Let a := SFun.codom f.

Definition sintegral : \bar R := (\sum_(k < n) (a`_k)%:E * m (A k))%E.

Lemma sintegralE : sintegral =
  (\sum_(x <- SFun.codom f) x%:E * m (f @^-1` [set x]))%E.
Proof.
rewrite big_tnth; apply eq_bigr => i _; congr (_%:E * m _)%E.
  by apply set_nth_default; rewrite /= ltn_ord.
rewrite /A /SFun.pi; congr (_ @^-1` _); rewrite predeqE => r; split;
  by rewrite /mkset /set1 /mkset => ->; apply set_nth_default; rewrite ltn_ord.
Qed.

End simple_function_integral.

Lemma sintegral_ge0 (T : measurableType) (R : realType) (f : nnsfun T R)
  (m : {measure set T -> \bar R}) :
  (0 <= sintegral m f)%E.
Proof.
rewrite /sintegral; apply: sume_ge0 => t _; apply: mule_ge0; first exact: NNSFun.ge0.
exact/measure_ge0/SFun.mpi.
Qed.

Section sintegralK.
Variables (T : measurableType) (point : T) (*NB: measurablePointedType? *).
Variables (R : realType) (m : {measure set T -> \bar R}).
Variables (r : R) (f : nnsfun T R).

Lemma sintegralK : sintegral m (sfun_scale point r f) = (r%:E * sintegral m f)%E.
Proof.
have [/eqP ->|r0] := boolP (r == 0).
  rewrite mul0e /sintegral big1 // => i _; rewrite /= eqxx /=.
  case: (m (SFun.pi _ _)) => [x| |]; move: i; rewrite ssize_sfun_scale0 => i.
  by rewrite (ord1 i) /= mul0r.
  by rewrite (ord1 i) /= eqxx.
  by rewrite (ord1 i) /= eqxx.
rewrite /sintegral.
pose cast := cast_ord (ssize_sfun_scale_neq0 point f r0).
rewrite [LHS](eq_bigr (fun k : 'I_(ssize (sfun_scale point r f)) =>
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
pose castK := cast_ord (esym (ssize_sfun_scale_neq0 point f r0)).
rewrite (@reindex _ _ _ [finType of 'I_(ssize (sfun_scale point r f))]
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

Lemma sintegralD : sintegral m (sfun_add f g) = (sintegral m f + sintegral m g)%E.
Proof.
transitivity (\sum_(i < n) \sum_(l < p)
  ((SFun.codom f)`_i + (SFun.codom g)`_l)%:E * m (SFun.pi f i `&` SFun.pi g l))%E.
  rewrite /sintegral.
  under eq_bigr do rewrite measure_sfun_add_pi.
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g))) (\sum_(x in sfun_add_pidx i)
    ((SFun.codom f)`_x.1 + (SFun.codom g)`_x.2)%:E * m (SFun.pi f x.1 `&` SFun.pi g x.2)))%E.
    apply eq_bigr => i _; rewrite sume_distrr //; last first.
      by move=> kl _; rewrite measure_ge0 //; apply: measurableI; exact: SFun.mpi.
    by apply eq_bigr => x; rewrite !inE => /andP[] /eqP ->.
  rewrite [in RHS]pair_big.
  transitivity (\sum_(p0 in setX [set: 'I_n] [set: 'I_p])
    (((SFun.codom f)`_p0.1 + (SFun.codom g)`_p0.2)%:E * m (SFun.pi f p0.1 `&` SFun.pi g p0.2)))%E; last first.
    by apply/eq_bigl => // -[/= k l]; rewrite !inE.
  transitivity (
  (\sum_(p0 in [set x : 'I_n * 'I_p|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET )
      ((SFun.codom f)`_p0.1 + (SFun.codom g)`_p0.2)%:E * m (SFun.pi f p0.1 `&` SFun.pi g p0.2))%E); last first.
    rewrite big_mkcond; apply eq_big => //.
      by move=> x; rewrite !inE.
    move=> [x y] _.
    case: ifPn => //.
    rewrite inE negbK => /eqP ->.
    by rewrite measure0 mule0.
  rewrite -sfun_add_pi_cover0.
  rewrite partition_disjoint_bigcup // => i j ij.
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[-[/= k l]].
  rewrite inE /= => /andP[]; rewrite 2!inE.
  move/andP => []/eqP -> _.
  move/andP => [+ _].
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

(* TODO: move *)
Lemma eq_preimage (aT rT : Type) (f g : aT -> rT) (A : set rT) :
  f =1 g -> f @^-1` A = g @^-1` A.
Proof.
by move=> fg; rewrite predeqE => r; split; rewrite /preimage /mkset fg.
Qed.

Section le_sintegral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (m : {measure set T -> \bar R}).

Lemma eq_sintegral (f g : sfun T R) : f =1 g -> sintegral m f = sintegral m g.
Proof.
move=> fg.
rewrite 2!sintegralE (perm_big (SFun.codom g)); last exact: sfun_ext.
by apply: eq_bigr => r _; congr (_ * m _)%E; exact: eq_preimage.
Qed.

(* TODO: order structure on functions *)
Lemma le_sintegral (f g : nnsfun T R) :
  (forall x, f x <= g x) -> (sintegral m f <= sintegral m g)%E.
Proof.
move=> fg.
pose gNf' := sfun_add g (sfun_scale point (-1) f).
have gNf0 : forall x, 0 <= gNf' x.
  by move=> x /=; rewrite mulN1r subr_ge0.
pose gNf := mk_nnsfun gNf0.
have gfgf : g =1 sfun_add f gNf.
  by move=> x; rewrite /= addrCA mulN1r subrr addr0.
by rewrite (eq_sintegral gfgf) sintegralD lee_addl // sintegral_ge0.
Qed.

End le_sintegral.

Definition nondecreasing_seq_fun (T : measurableType) (R : realType) (f : (T -> R)^nat) :=
  (forall x, {homo f^~x : m n / (m <= n)%N >-> (m <= n)}).

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (R : realType) (m : {measure set T -> \bar R}).
Variables (f : (nnsfun T R)^nat) (F : nnsfun T R).
Hypothesis f_nndecr : nondecreasing_seq_fun f.
Hypothesis fF : forall x : T, F x = lim (f^~ x : nat -> R^o).

Lemma sintegral_nondecreasing_limit :
  sintegral m F = lim (sintegral m \o f).
Proof.
Abort.

End sintegral_nondecreasing_limit.
