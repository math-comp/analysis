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
(*     integral == integral of a nonnegtive measurable function               *)
(*   integrable == the integral is < +oo                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: PR? *)
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
rewrite predeqE => t; split => // _; rewrite -bigcup_set -preimage_bigcup.
have /(nthP 0)[i ni fit] := SFunfcodom t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

Lemma measurable_preimage_set1 (r : R) : measurable (f @^-1` [set r]).
Proof.
have [[k fkr]|] := pselect (exists k : 'I_(ssize f), (SFun.codom f)`_k = r).
  have := SFun.mpi k.
  by rewrite /SFun.pi fkr.
move/forallNP => fr.
rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
rewrite predeqE => t; split => //=.
rewrite /set1 /mkset => ftr.
have : f t \in SFun.codom f by apply SFunfcodom.
move/(nthP 0) => [i fi] fift.
have := fr (Ordinal fi).
by rewrite fift.
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
rewrite -bigcup_set_cond.
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
rewrite -[in RHS]bigcup_set_cond -bigcup_set_cond.
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
  ge0 : forall t, 0 <= f t }.
End nnsfun.
Module Exports.
Notation nnsfun := t.
End Exports.
End NNSFun.
Export NNSFun.Exports.
Coercion NNSFun.f : nnsfun >-> sfun.

Section nnsfun_lemmas.
Variables (T : measurableType) (R : realType).

Lemma NNSFun_ge0 (f : nnsfun T R) (k : 'I_(ssize f)) : 0 <= (SFun.codom f)`_k.
Proof. by apply: sfun_ge0; exact: NNSFun.ge0. Qed.

Lemma SFuncodom_ge0 (f : nnsfun T R) (r : R) : (r \in SFun.codom f) -> (0 <= r%:E)%E.
Proof. by move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNSFun_ge0 (Ordinal fi)). Qed.

End nnsfun_lemmas.

Section nnsfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Hypothesis r0 : 0 <= r.
Let sfun_cst_ge0 (t : T) : 0 <= sfun_cst point r t. Proof. by []. Qed.

Definition nnsfun_cst := NNSFun.mk sfun_cst_ge0.
End nnsfun_cst.

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
rewrite /sintegral; apply: sume_ge0 => t _; apply: mule_ge0; first exact: NNSFun_ge0.
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
  by rewrite (ord1 i) mul0e.
  by rewrite (ord1 i) /= mul0e.
  by rewrite (ord1 i) /= mul0e.
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
  move=> i _; rewrite mule_ge0 //; first exact: NNSFun_ge0.
  by apply: measure_ge0; exact: SFun.mpi.
pose castK := cast_ord (esym (ssize_sfun_scale_neq0 point f r0)).
rewrite (@reindex _ _ _ [finType of 'I_(ssize (sfun_scale point r f))]
    [finType of 'I_(ssize f)] castK); last first.
  by exists cast => i; by rewrite /cast /castK /= ?(cast_ordKV,cast_ordK).
by apply eq_bigr => i _; rewrite /cast /castK cast_ordKV mulEFin muleA.
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
rewrite addEFin ge0_muleDl; try exact: NNSFun_ge0.
by rewrite addeC.
Qed.

End sintegralD.

(* TODO: move *)
Definition nondecreasing_seq_fun (T : measurableType) d (R : porderType d) (f : (T -> R)^nat) :=
  (forall x, nondecreasing_seq (f^~x)).

(* TODO: move *)
Lemma eq_preimage (aT rT : Type) (f g : aT -> rT) (A : set rT) :
  f =1 g -> f @^-1` A = g @^-1` A.
Proof.
by move=> fg; rewrite predeqE => r; split; rewrite /preimage /mkset fg.
Qed.

(* TODO: move *)
Lemma setTP (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.

(* NB: equivalent of lte_lim for realFieldType *)
Lemma lt_lim (R : realFieldType) (u : (R^o)^nat) (M : R) :
  nondecreasing_seq u -> cvg u -> M < lim u ->
  \forall n \near \oo, M <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|] := pselect (exists n, M <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
move/forallNP => Mu.
have {}Mu : forall x, M > u x by move=> x; rewrite ltNge; apply/negP.
have : lim u <= M by apply lim_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Grab Existential Variables. all: end_near. Qed.

Lemma nondecreasing_dvg_lt (R : realType) (u_ : R^o ^nat) : nondecreasing_seq u_ -> ~ cvg u_ ->
  forall M, exists n, forall m, (m >= n)%N -> M <= u_ m.
Proof.
move=> nu du M; apply/not_existsP; apply: contra_not du => Mu.
apply: (@nondecreasing_is_cvg _ _ M) => // n.
have := Mu n => /existsNP[m] /not_implyP [nm] /negP; rewrite -ltNge => /ltW.
by apply: le_trans; apply: nu.
Qed.

Lemma ereal_cvgZ (R : realFieldType) (f : (\bar R)^nat) (a : \bar R) c :
  f --> a -> (fun n => c%:E * f n)%E --> (c%:E * a)%E.
Proof.
rewrite (_ : (fun n => c%:E * f n)%E = (mule c%:E) \o f) // => /cvg_comp; apply.
exact: mule_continuous.
Qed.

Lemma elimZ (R : realType) (f : (\bar R)^nat) c : cvg f ->
  lim (fun n => c%:E * f n)%E = (c%:E * lim f)%E.
Proof. by move=> cf; apply/cvg_lim => //; apply: ereal_cvgZ. Qed.

Lemma is_cvg_ereal_cvgZ (R : realFieldType) (f : (\bar R)^nat) c :
  cvg f -> cvg (fun n => c%:E * f n)%E.
Proof.
move=> /cvg_ex[l fl]; apply/cvg_ex; eexists.
by apply: ereal_cvgZ => //; exact: fl.
Qed.

Lemma ereal_lim_sum (R : realType) (I : Type) (r : seq I) (f : I -> (\bar R)^nat) (l : I -> \bar R) (P : pred I) :
  (forall n x, P x -> 0 <= f x n)%E ->
  (forall k, f k --> l k) ->
  (fun n : nat => \sum_(k <- r | P k) f k n)%E --> (\sum_(k <- r | P k) l k)%E.
Proof.
elim: r => [h fl|a b ih h fl].
  rewrite !big_nil.
  rewrite (_ : (fun _ => _) = (fun=> 0%E)).
    exact: cvg_cst.
  by under eq_fun do rewrite big_nil.
rewrite big_cons.
rewrite (_ : (fun _ => _) = (fun n : nat => (if P a then f a n + \sum_(k <- b | P k) f k n else \sum_(k <- b | P k) f k n )%E)); last first.
  by under eq_fun do rewrite big_cons.
case: ifPn => Pa.
  apply: ereal_cvgD => //.
    apply ge0_adde_def; rewrite !inE.
    (* TODO: lemma? *)
    rewrite -(cvg_lim _ (fl a)) //; apply: ereal_lim_ge.
      by apply/cvg_ex; exists (l a); exact: (fl a).
    by near=> n; apply h => //.
    apply sume_ge0 => t Pt.
    rewrite -(cvg_lim _ (fl t)) //; apply: ereal_lim_ge.
      by apply/cvg_ex; exists (l t); exact: (fl t).
    by near=> n; apply h => //.
  by apply ih => //.
by apply ih => //.
Grab Existential Variables. all: end_near. Qed.

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
pose gNf := NNSFun.mk gNf0.
have gfgf : g =1 sfun_add f gNf.
  by move=> x; rewrite /= addrCA mulN1r subrr addr0.
by rewrite (eq_sintegral gfgf) sintegralD lee_addl // sintegral_ge0.
Qed.

Lemma is_cvg_sintegral (f : (nnsfun T R)^nat) :
  nondecreasing_seq_fun f -> cvg (fun n => sintegral m (f n)).
Proof.
move=> f_ndecr; apply/cvg_ex; eexists.
apply/nondecreasing_seq_ereal_cvg => a b ab.
by apply: le_sintegral => // x; exact: f_ndecr.
Qed.

End le_sintegral.

Section preimage_setI.
Variables (T : measurableType) (R : realType) (g : nnsfun T R).

Lemma gSxE (S : set T) (x : R) :
  [set t | [set x] (g t * (t \in S)%:R)] =
    ((S `&` (g @^-1` [set x])) `|` (~` S `&` (fun _ => x = 0))).
Proof.
rewrite (_ : (fun t : T => _) = (fun t => if t \in S then g t = x else x = 0)); last first.
  rewrite predeqE => t; split;
    by have [tS|tS] := boolP (t \in S); rewrite !(mulr1,mulr0).
rewrite (_ : (fun t : T => _) = ((S `&` (g @^-1` [set x])) `|` (~` S `&` (fun _ => x = 0)))) //.
rewrite predeqE => t; split.
  case: ifPn => [tS <-|tS].
    by left; split => //; rewrite -in_setE.
  by right; split => //; apply: contraNnot tS; rewrite in_setE.
case: ifPn => [tS [[_ <-//]|[]] |tS [[]|[]//]].
- by rewrite in_setE in tS.
- by rewrite -in_setE (negbTE tS).
Qed.

Local Obligation Tactic := idtac.

Definition preimgI_codom (S : set T) :=
  let s := [seq x <- SFun.codom g | (g @^-1` [set x]) `&` S != set0] in
  if (0 \in s) || (S == setT) then s else rcons s 0.

Program Definition preimgI_sfun (S : set T) (mS : measurable S) : sfun T R :=
  @SFun.mk _ _ (fun x => g x * (x \in S)%:R)
  (preimgI_codom S) _ _ _.
Next Obligation.
move=> S _.
rewrite /preimgI_codom.
set s := seq.filter _ _ => /=.
have [_|] := ifPn.
  by rewrite filter_uniq // SFun.uniq_codom.
rewrite negb_or => /andP[s0 _].
by rewrite rcons_uniq s0 /= filter_uniq // SFun.uniq_codom.
Qed.
Next Obligation.
move=> S _.
rewrite /preimgI_codom.
set s := seq.filter _ _ => /=.
rewrite predeqE => x; split => [[t _ <-{x}]|] /=.
  have [tS|tS] /= := boolP (t \in S).
    rewrite mulr1.
    have [_|_] := ifPn.
      rewrite mem_filter SFunfcodom andbT; apply/set0P.
      by exists t => //; split => //=; rewrite -in_setE.
    rewrite mem_rcons inE; apply/orP; right.
    rewrite mem_filter SFunfcodom andbT; apply/set0P.
    by exists t; split => //=; rewrite -in_setE.
  rewrite mulr0.
  have [/orP[//|/eqP]|] := ifPn.
    by rewrite predeqE => /(_ t)[_]/(_ Logic.I); rewrite -in_setE (negbTE tS).
  by rewrite negb_or => /andP[s0 ST]; rewrite mem_rcons inE eqxx.
have [_|] := ifPn.
  rewrite mem_filter => /andP[/set0P[t [/= gtx]]].
  by rewrite -in_setE => St xg; exists t => //; rewrite St mulr1.
rewrite negb_or => /andP[s0 ST]; rewrite mem_rcons inE => /orP[/eqP ->{x}|].
  suff [t St] : exists t, t \notin S.
    by exists t => //; rewrite (negbTE St) mulr0.
  by move/setTP : ST => [t St]; exists t; apply/negP; rewrite in_setE.
rewrite mem_filter => /andP[+ _] => /set0P[t [gtx]].
by rewrite -in_setE => tS;exists t => //; rewrite tS mulr1.
Qed.
Next Obligation.
move=> S mS.
rewrite /preimgI_codom.
set s := seq.filter _ _ => /=.
have sg : (size s <= ssize g)%N by rewrite size_filter count_size.
have [|] := ifPn.
  move=> /orP[s0 k|/eqP ST k].
  - have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.codom g)`_k'.
      have : s`_k \in SFun.codom g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite gSxE.
    apply: measurableU.
      apply: measurableI => //.
      have := @SFun.mpi _ _ g k'.
      by rewrite /SFun.pi /= -kk'.
    apply: measurableI.
      exact: measurableC.
    have [sk0|sk0] := pselect (s`_k = 0).
      by rewrite (_ : (fun _ => _) = setT) ?predeqE//; exact: measurableT.
    by rewrite (_ : (fun _ => _) = set0) ?predeqE//; exact: measurable0.
  - (*copipe*) have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.codom g)`_k'.
      have : s`_k \in SFun.codom g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite [X in _ X](_ : _ = [set t | [set s`_k] (g t)]).
      have := @SFun.mpi _ _ g k'.
      by rewrite /SFun.pi /= -kk'.
    rewrite predeqE => t.
    rewrite /mkset /set1 /mkset.
    by rewrite (_ : _ \in _) ?mulr1// in_setE ST.
rewrite negb_or => /andP[s0 ST] k.
rewrite gSxE.
have [ks|ks] := boolP (k == size s :> nat).
  rewrite nth_rcons (eqP ks) ltnn eqxx.
  apply: measurableU.
    have [/eqP H|/set0P[t [St g0t]]] := boolP ((S `&` g @^-1` [set 0]) == set0).
      by rewrite H; exact: measurable0.
    have : 0 \in s.
      rewrite mem_filter; apply/andP; split.
        by apply/set0P; exists t.
      by rewrite -g0t SFunfcodom.
    by rewrite (negbTE s0).
  apply: measurableI => //.
    by apply measurableC.
  rewrite (_ : (fun _ => _) = setT); first exact: measurableT.
  by rewrite predeqE.
have [k' kk'] : exists k' : 'I_(ssize g), (rcons s 0)`_k = (SFun.codom g)`_k'.
  have @k' : 'I_(size s).
    apply: (@Ordinal _ k).
    rewrite ltn_neqAle ks /=.
    by rewrite -ltnS -(size_rcons s 0) ltn_ord.
  have : s`_k' \in s.
    apply/(nthP 0).
    by exists k'.
  rewrite mem_filter => /andP[_].
  move/(nthP 0) => [i ig] gisk'.
  exists (Ordinal ig) => //=.
  rewrite nth_rcons ifT //.
  rewrite ltn_neqAle ks /=.
  rewrite -ltnS -(size_rcons s 0).
  by rewrite ltn_ord.
apply: measurableU.
  apply: measurableI => //.
  have := @SFun.mpi _ _ g k'.
  by rewrite /SFun.pi /= -kk'.
apply: measurableI.
  exact: measurableC.
have [sk0|sk0] := pselect ((rcons s 0)`_k = 0).
  by rewrite (_ : (fun _ => _) = setT) ?predeqE//; exact: measurableT.
by rewrite (_ : (fun _ => _) = set0) ?predeqE//; exact: measurable0.
Qed.

End preimage_setI.

Section sintegral_nondecreasing_limit_lemma.
Variables (T : measurableType) (point : T).
Variables (R : realType) (mu : {measure set T -> \bar R}).
Variables (f : (nnsfun T R)^nat).
Hypothesis f_ndecr : nondecreasing_seq_fun f.
Variables (g : nnsfun T R).
Hypothesis gf : forall x : T, cvg (fun x0 : nat => f x0 x : R^o) -> g x <= lim (f^~ x : nat -> R^o).

Lemma nondecreasing_sintegral_lim_lemma :
  (sintegral mu g <= lim (sintegral mu \o f))%E.
Proof.
suff h : forall c, 0 < c < 1 ->
  (c%:E * sintegral mu g <= lim (sintegral mu \o f))%E.
  apply/lee_addgt0Pr => //; first exact: sintegral_ge0.
  apply: ereal_lim_ge; first exact: is_cvg_sintegral.
  near=> n; exact: sintegral_ge0.
move=> c /andP[c0 c1].
pose S_ n := [set x : T | c * g x <= f n x].
have S_ndecr : nondecreasing_seq S_.
  by move=> n m nm; apply/subsetPset => x /= /le_trans; apply; exact: f_ndecr.
have S_total : \bigcup_n S_ n = @setT T.
  rewrite predeqE => x; split => // _.
  have := NNSFun.ge0 g x; rewrite le_eqVlt => /orP[/eqP gx0|gx0].
    by exists O => //; rewrite /S_ /= -gx0 mulr0 NNSFun.ge0.
  have [cf|df] := pselect (cvg (f^~ x : nat -> R^o)).
    have fcg : lim (f^~ x : nat -> R^o) > c * g x.
      by rewrite (lt_le_trans _ (gf cf)) // gtr_pmull.
    have [n fcgn] : exists n, f n x >= c * g x.
      move: (@lt_lim _ (f^~ x) (c * g x) (f_ndecr x) cf fcg) => [n _ nf].
      by exists n; apply: nf => /=.
    by exists n => //; rewrite /S_ /= ltW.
  have [n ncgf] := nondecreasing_dvg_lt (f_ndecr x) df (c * g x).
  by exists n => //; rewrite /S_ /= ncgf.
have mS_ n : measurable (S_ n).
  rewrite /S_.
  rewrite [X in _ X](_ : _ =
    \big[setU/set0]_(y <- SFun.codom g)
      \big[setU/set0]_(x <- SFun.codom (f n) | c * y <= x)
          (((fun x => g x) @^-1` [set y]) `&` ((f n @^-1` [set x])))); last first.
    rewrite predeqE => t; split.
      rewrite /= => cgf.
      rewrite -bigcup_set.
      exists (g t).
        by apply: SFunfcodom.
      rewrite -bigcup_set_cond.
      exists (f n t) => //.
      by apply/andP; split => //; apply SFunfcodom.
    rewrite -bigcup_set => -[r /= gr].
    by rewrite -bigcup_set_cond => -[r' /andP[r'f crr']] [/= -> ->].
  apply bigsetU_measurable => x _.
  apply bigsetU_measurable => y xcy.
  by apply: measurableI; exact: measurable_preimage_set1.
pose g1 (n : nat) := preimgI_sfun g (mS_ n).
have h13 : forall n, forall x, (f n x >= c * g1 n x).
  move=> n x; rewrite /g1 /=; have [xSn|xSn] := boolP (x \in _).
    by rewrite mulr1; rewrite in_setE in xSn.
  by rewrite 2!mulr0 NNSFun.ge0.
have g10 : forall n x, 0 <= g1 n x.
  move=> n x; rewrite /g1 /=.
  by rewrite mulr_ge0 //; [exact: NNSFun.ge0 | rewrite ler0n].
have g10' : forall n x, 0 <= (sfun_scale point c (NNSFun.mk (g10 n))) x.
  by move=> n x; rewrite mulr_ge0 //; [exact: ltW | exact: NNSFun.ge0].
have h14 : forall n, (sintegral mu (f n) >= c%:E * sintegral mu (g1 n))%E.
  move=> n; rewrite -(sintegralK point mu c (NNSFun.mk (g10 n))).
  apply: (@le_sintegral _ point _ mu (NNSFun.mk (g10' n)) (f n)) => x /=.
  by rewrite h13.
suff <- : lim (fun n => sintegral mu (g1 n)) = sintegral mu g.
  have cg1 : cvg (fun n : nat => sintegral mu (g1 n)).
    apply: (@is_cvg_sintegral _ point _ mu (fun n => NNSFun.mk (g10 n))) => //=.
    (* TODO: lemma *)
    move=> t n m nm.
    rewrite ler_pmul // ?NNSFun.ge0// ?ler0n// ler_nat.
    have [/=|//] := boolP (t \in S_ n).
    rewrite in_setE => Snt.
    by have := S_ndecr n m nm => /subsetPset /(_ _ Snt); rewrite -in_setE => ->.
  rewrite -elimZ //.
  apply: lee_lim => //; [exact: is_cvg_ereal_cvgZ | exact: is_cvg_sintegral |].
  by near=> n; exact: h14.
suff : (fun n => sintegral mu (g1 n)) --> sintegral mu g by apply/cvg_lim.
have H : forall n, sintegral mu (g1 n) =
  (\sum_(k < ssize g) ((SFun.codom g)`_k)%:E * mu ((g @^-1` [set (SFun.codom g)`_k]) `&` S_ n))%E.
  move=> n.
  rewrite sintegralE.
  transitivity (\sum_(x <- SFun.codom g) x%:E * mu (g1 n @^-1` [set x]))%E.
    rewrite (_ : SFun.codom _ = preimgI_codom g (S_ n)) //.
    rewrite /preimgI_codom /=.
    case: ifPn.
      case/orP => [|ST].
        rewrite mem_filter /= => /andP[]; rewrite /set1 /mkset /= => /set0P[t [ gt0 St]] g0.
        rewrite big_filter big_mkcond; apply eq_bigr => r _.
        case: ifPn => // /negPn/eqP I0.
        rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0//.
        rewrite predeqE => t0; split => //=.
        have [t0S|] := boolP (t0 \in _).
          rewrite mulr1 => gt0r.
          rewrite -I0; split => //.
          by rewrite in_setE in t0S.
        move=> t0S; rewrite mulr0 => r0; subst r.
        by move: I0; rewrite predeqE => /(_ t)[+ _]; apply.
      rewrite big_filter big_mkcond; apply eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 //.
      rewrite predeqE => t; split => //=; rewrite /set1 /mkset.
      rewrite (eqP ST).
      have [tT|] := boolP (t \in _).
        rewrite mulr1 => gtr.
        rewrite -I0; split => //.
        by rewrite (eqP ST).
      have : setT t by [].
      by rewrite -in_setE => ->.
    rewrite negb_or => /andP[H1 H2].
    rewrite -cats1 big_cat /= big_cons big_nil mul0e !adde0.
    rewrite big_filter big_mkcond; apply eq_bigr => r _.
    case: ifPn => // /negPn/eqP I0.
    have [/eqP ->|r0] := boolP (r == 0).
      by rewrite mul0e.
    rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 //.
    rewrite predeqE => t; split => //=; rewrite /set1 /mkset.
    have [tT|] := boolP (t \in _).
      rewrite mulr1 => gtr.
      rewrite -I0; split => //.
      by rewrite in_setE in tT.
    rewrite mulr0 => ? /esym/eqP.
    by rewrite (negbTE r0).
  rewrite big_tnth; apply eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0) //=.
  have [/eqP gi0|gi0] := boolP ((SFun.codom g)`_i == 0).
    by rewrite gi0 // 2!mul0e.
  congr (_%:E * mu _)%E.
  rewrite predeqE => t; split => /=.
    rewrite /mkset /set1 /mkset /=.
    have [tSn|tSn] := boolP (_ \in S_ n).
      rewrite mulr1 => <-.
      split => //.
      by rewrite -in_setE.
    rewrite mulr0 => /esym/eqP.
    by rewrite (negbTE gi0).
  move=> -[/=].
  rewrite /set1 /mkset => ->.
  rewrite -in_setE => ->.
  by rewrite mulr1.
rewrite (_ : (fun n : nat => sintegral mu (g1 n)) =
  (fun n : nat => (\sum_(k < ssize g) ((SFun.codom g)`_k)%:E * mu (g @^-1` [set (SFun.codom g)`_k] `&` S_ n))%E)); last first.
  by rewrite funeqE => n; rewrite H.
rewrite sintegralE.
rewrite (_ :
  (fun n => \sum_(k < ssize g) ((SFun.codom g)`_k)%:E * mu (g @^-1` [set (SFun.codom g)`_k] `&` S_ n))%E =
  (fun n => \sum_(x <- SFun.codom g) x%:E * mu (g @^-1` [set x] `&` S_ n))%E); last first.
  rewrite funeqE => n.
  rewrite [in RHS]big_tnth /=.
  apply/eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0) //=; congr (_%:E * mu (_ `&` _))%E.
  by apply set_nth_default.
  rewrite predeqE => t /=.
  rewrite /set1 /mkset.
  rewrite -propeqE.
  f_equal.
  by apply set_nth_default.
rewrite big_seq.
under [in X in X --> _]eq_fun do rewrite big_seq.
apply: ereal_lim_sum => k.
  move=> x xg.
  apply: mule_ge0; first by move/SFuncodom_ge0 : xg.
  by apply: measure_ge0; apply: measurableI => //; exact: measurable_preimage_set1.
suff : (fun n => mu (g @^-1` [set k] `&` S_ n)) --> mu (g @^-1` [set k]).
  exact: ereal_cvgZ.
rewrite (_ : mu (g @^-1` [set k]) = mu (\bigcup_n (g @^-1` [set k] `&` S_ n))); last first.
  congr (mu _).
  by rewrite -bigcup_distrr S_total setIT.
rewrite (_ : (fun _ => _) = (mu \o (fun i => (g @^-1` [set k] `&` S_ i)))); last first.
  done.
apply: cvg_mu_inc => //.
  by move=> i; apply: measurableI => //; exact: measurable_preimage_set1.
apply measurable_bigcup.
  by move=> i; apply: measurableI => //; exact: measurable_preimage_set1.
move => n m nm.
apply: setIS.
by move/S_ndecr : nm => /subsetPset.
Grab Existential Variables. all: end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (point : T).
Variables (R : realType) (mu : {measure set T -> \bar R}).
Variables (f : (nnsfun T R)^nat).
Hypothesis f_ndecr : nondecreasing_seq_fun f.
Variables (F : nnsfun T R).
Hypothesis fF : forall x : T, (f^~ x : nat -> R^o) --> (F x : R^o).
Let fF' : forall x : T, lim (f^~ x : nat -> R^o) = (F x : R^o).
Proof. by move=> x; apply/cvg_lim => //; apply: fF. Qed.

Lemma nondecreasing_sintegral_lim : sintegral mu F = lim (sintegral mu \o f).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have : nondecreasing_seq (sintegral mu \o f).
    by move=> m n mn; apply (le_sintegral point) => // x; exact: f_ndecr.
  move=> /nondecreasing_seq_ereal_cvg/cvg_lim -> //.
  apply: ub_ereal_sup => x [n _ <-{x}] /=.
  apply le_sintegral => // x.
  rewrite -fF'.
  apply: (@nondecreasing_cvg_le _ (f^~ x : nat -> R^o)) => //.
  by apply/cvg_ex; exists (F x); exact: fF.
by apply: nondecreasing_sintegral_lim_lemma => // x; rewrite -fF'.
Qed.

End sintegral_nondecreasing_limit.

Section integral_integrable.
Variables (T : measurableType) (point : T) (R : realType) (mu : {measure set T -> \bar R}).

(* expect a nonnegative measurable function f *)
Definition integral (f : T -> \bar R) :=
  ereal_sup [set sintegral mu g | g in
    [set g : nnsfun T R | (forall x, (g x)%:E <= f x)%E] ].

Lemma integral_ge0 (f : T -> \bar R) : (forall x, 0 <= f x)%E -> (0 <= integral f)%E.
Proof.
move=> f0; apply: ereal_sup_ub => /=.
exists (@nnsfun_cst T point R 0 (lexx _)) => //.
rewrite /sintegral /= big1 //= => k _.
rewrite (_ : _%:E = 0%E) ?mul0e//; congr EFin.
by move: k => [[|]].
Qed.

Definition integrable (f : T -> \bar R) := (integral f < +oo)%E.

End integral_integrable.

(* TODO: move *)
Lemma EFin_lim (R : realType) (r : R) (f : nat -> R^o) : nondecreasing_seq f ->
 cvg f ->
 (r%:E <= lim (@EFin _ \o f)%E)%E -> r <= lim f.
Proof.
move=> ndecr_f cf rf.
rewrite -lee_fin (le_trans rf) // ereal_lim_le //.
  move/cvg_ex : cf => [l fl]; apply/cvg_ex; exists l%:E => //=.
  exact: (continuous_cvg _ _ fl).
near=> n; rewrite /= lee_fin lim_ge //.
near=> m; apply: ndecr_f.
by near: m; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma eq_oo (R : realType) (x : \bar R) : (forall A, 0 < A -> (A%:E <= x)%E) <-> x = +oo%E.
Proof.
split=> [Ax|-> // A A0]; last by rewrite lee_pinfty.
apply/eqP; rewrite eq_le lee_pinfty /= leNgt; apply/negP.
move: x Ax => [x Ax _|//|]; last by move/(_ 1 ltr01).
move/not_forallP : Ax; apply.
exists (`|x| + 1).
apply/not_implyP; split.
  by rewrite -(addr0 0) ler_lt_add.
rewrite lee_fin => x1x.
have := le_trans x1x (ler_norm x).
apply/negP.
by rewrite -ltNge ltr_addl.
Qed.

Definition cvg_realFieldType_ereal (T : measurableType) (R : realFieldType)
    (g : (T -> R)^nat) (f : T -> \bar R) := forall x,
  if pselect (cvg (g^~ x : nat -> R^o)) then
    @EFin _ \o g^~ x --> f x
  else
    f x = +oo%E.

Section nondecreasing_integral_limit.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R).

(* PR in progress (lebesgue_measure) *)
Parameter measurableRbar : set (set \bar R).
Parameter measurableRbar0 : measurableRbar set0.
Parameter measurableRbarC : forall A, measurableRbar A -> measurableRbar (~` A).
Parameter measurableRbar_bigcup : forall U : (set \bar R)^nat, (forall i, measurableRbar (U i)) ->
    measurableRbar (\bigcup_i (U i)).
Definition Rbar_isMeasurable : isMeasurable \bar R :=
  isMeasurable.Build _ measurableRbar0 measurableRbarC measurableRbar_bigcup.
HB.instance (\bar (Real.sort R)) Rbar_isMeasurable.
(* /PR in progress (lebesgue_measure) *)

Hypothesis f0 : forall x, (0 <= f x)%E.
Hypothesis mf : measurable_fun setT f.
Variables (g : (nnsfun T R)^nat).
Hypothesis g_ndecr : nondecreasing_seq_fun g.
Hypothesis fF : cvg_realFieldType_ereal g f.

Lemma nondecreasing_integral_lim : integral mu f = lim (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n.
  rewrite /integral.
  apply: ereal_sup_ub; exists (g n) => //= x.
  have := fF x.
  case: pselect => cg /=; last by move=> ->; rewrite lee_pinfty.
  move=> gf.
  have <- : lim (@EFin _ \o (g^~ x)) = f x by exact/cvg_lim.
  have : (@EFin _ \o g^~ x) --> ereal_sup [set of @EFin _ \o g^~ x].
    apply: nondecreasing_seq_ereal_cvg => p q pq /=; rewrite lee_fin.
    exact: g_ndecr.
  by move/cvg_lim => -> //; apply ereal_sup_ub => /=; exists n.
have := lee_pinfty (integral mu f).
rewrite le_eqVlt => /orP[/eqP mufoo|]; last first.
  move mufr : (integral mu f) => r.
  move: r mufr => [r mufr _|//|mufr]; last first.
    by move: (integral_ge0 point mu f0); rewrite mufr.
  rewrite -mufr.
  move/ub_ereal_sup_adherent : mufr; rewrite -/(integral _ _) => h.
  apply: lee_adde => e.
  have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite lte_subl_addr => fGe.
  have : forall x, cvg (g^~ x : _ -> R^o) -> (G x) <= lim (g^~ x : _ -> R^o).
    move=> x cg.
    have : ((G x)%:E <= lim (@EFin _ \o g^~ x))%E.
      have := @fF x.
      case: pselect => // {}cg /= /cvg_lim gf.
      by rewrite (le_trans (Gf x)) // gf.
    exact: EFin_lim.
  move/(@nondecreasing_sintegral_lim_lemma _ point _ mu _ g_ndecr _).
  by move/(lee_add2r e%:num%:E)/(le_trans (ltW fGe)).
suff : lim (sintegral mu \o g) = +oo%E by move=> ->; rewrite mufoo.
apply eq_oo => A A0.
have [G [Gf AG]] : exists h : nnsfun T R, (forall x, ((h x)%:E <= f x)%E) /\
                                     (A%:E <= sintegral mu h)%E.
  move: (mufoo).
  rewrite /integral.
  move/eq_oo.
  have A20 : 0 < A + A by rewrite addr_gt0.
  move/(_ _ A20) => A2.
  have {} : (A%:E < ereal_sup [set sintegral mu g0 | g0 in [set h : nnsfun T R | (forall x, (h x)%:E <= f x)]])%E.
    by rewrite (lt_le_trans _ A2) // lte_fin ltr_addr.
  move/ereal_sup_gt => [x [/= [G Gf Gx Ax]]].
  exists G; split => //.
  by rewrite (le_trans (ltW Ax)) // Gx.
have : forall x, cvg (g^~ x : _ -> R^o) -> (G x) <= lim (g^~ x : _ -> R^o).
 (* TODO: same code above in this script *)
  move=> x cg.
  have : ((G x)%:E <= lim (@EFin _ \o g^~ x))%E.
    have := @fF x.
    case: pselect => // {}cg /= /cvg_lim gf.
    by rewrite (le_trans (Gf x)) // gf.
  exact: EFin_lim.
move/(@nondecreasing_sintegral_lim_lemma _ point _ mu _ g_ndecr) => Gg.
by rewrite (le_trans AG).
Grab Existential Variables. all: end_near. Qed.

End nondecreasing_integral_limit.
