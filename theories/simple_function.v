(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval.
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
(*     sfun_cst == constant simple functions                                  *)
(*   sfun_scale == scaling of simple functions                                *)
(* sfun_add f g == addition of simple functions                               *)
(*       nnsfun == type of non-negative simple functions                      *)
(*    sintegral == integral of a simple function                              *)
(*     integral == integral of a nonnegative measurable function              *)
(*   integrable == the integral is < +oo                                      *)
(*                                                                            *)
(* sample theorems: approximation theorem, monotone convergence theorem, etc. *)
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

(* TODO: move *)
Lemma setTP (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.

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

Lemma notin_setE T (A : set T) x : x \notin A = (~ A x) :> Prop.
Proof.
by rewrite propeqE; split => [/asboolP//|]; apply: contra_notN; rewrite in_setE.
Qed.

Require Import nngnum.

Section charac_sfun.
Variables (T : measurableType) (point : T) (R : realType) (r : R) (A : set T).
Hypothesis mA : measurable A.

Local Definition charac_sfun' (x : T) : R := r * (x \in A)%:R.

Definition charac_codom : seq R := if r == 0 then [:: 0] else if A == setT then [:: r] else if
A == set0 then [:: 0] else [:: 0; r].

Lemma charac_uniq : uniq charac_codom.
Proof.
have [/eqP r0|r0] := boolP (r == 0).
  by rewrite /charac_codom r0 eqxx.
rewrite /charac_codom (negbTE r0) /=.
case: ifPn => // /setTP[t At].
case: ifPn => // _.
by rewrite /= andbT inE eq_sym.
Qed.

Lemma charac_fcodom : charac_sfun' @` setT = [set x | x \in charac_codom].
Proof.
rewrite predeqE => x; split => [[t _]|] /=.
  rewrite /charac_sfun'.
  have [tA|tA] := boolP (t \in A).
    rewrite mulr1 => <-.
    rewrite /charac_codom.
    case: ifPn => r0.
      by rewrite inE.
    case: ifPn => [|] _.
      by rewrite mem_head.
    case: ifPn.
      move/eqP => A0.
      by move: tA; rewrite A0 in_setE.
    move=> _.
    by rewrite inE mem_head orbT.
  rewrite mulr0 => <-.
  rewrite /charac_codom.
  case: ifPn => _.
    by rewrite mem_head.
  rewrite ifF; last first.
    apply/negbTE.
    apply/setTP.
    exists t.
    apply: contraNnot tA.
    by rewrite in_setE.
  by case: ifPn => _; rewrite inE eqxx.
rewrite /charac_codom.
case: ifPn => r0.
 rewrite inE => /eqP ->{x}.
 rewrite /charac_sfun'.
 exists point => //.
 by rewrite (eqP r0) mul0r.
case: ifPn => AT.
  rewrite !inE => /eqP ->{x}.
  rewrite /charac_sfun'.
  exists point => //.
  rewrite (_ : _ \in _) ?mulr1//.
  by rewrite in_setE (eqP AT).
case: ifPn => [/eqP A0|].
  rewrite inE => /eqP ->{x}.
  rewrite /charac_sfun'.
  exists point => //.
  rewrite A0.
  rewrite (_ : _ \in _ = false) ?mulr0 //.
  apply/negbTE.
  by rewrite notin_setE.
move=> A0.
rewrite !inE => /orP[|] /eqP ->{x}.
  rewrite /charac_sfun'.
  move/setTP : AT => [t At].
  exists t => //.
  rewrite (_ : _ \in _ = false) ?mulr0//.
  apply/negbTE.
  apply: contra_notN At.
  by rewrite in_setE.
rewrite /charac_sfun'.
move/set0P : A0 => -[t At].
exists t => //.
rewrite (_ : _ \in _) ?mulr1//.
by rewrite in_setE.
Qed.

Let pi := fun k : 'I_(size charac_codom) => charac_sfun' @^-1` [set charac_codom`_k].

Lemma charac_mpi : forall k, measurable (pi k).
Proof.
move=> k.
rewrite /pi.
have [r0|r0] := boolP (r == 0).
  rewrite (_ : _ @^-1` _ = setT).
    exact: measurableT.
  rewrite predeqE => t; split => // _ /=.
  rewrite /set1 /mkset /charac_sfun' /charac_codom.
  case: k => [[|k]] //=.
    move=> H.
    by rewrite r0 (eqP r0) /= mul0r.
  move=> H.
  exfalso.
  move: H.
  apply/negP.
  rewrite -leqNgt.
  by rewrite /charac_codom r0.
have [AT|AT] := boolP (A == setT).
  case: k => [[|m]] /=; last first.
    move=> H.
    exfalso.
    move: H.
    apply/negP.
    rewrite -leqNgt.
    by rewrite /charac_codom (negbTE r0) AT.
  move=> ?.
  set X := (X in measurable X).
  rewrite (_ : X = A) // /X.
  rewrite predeqE => t; split => [|At] /=.
    rewrite /mkset /= /charac_codom /= (negbTE r0) AT /=.
    rewrite /charac_sfun'.
    have [tA _|tA] := boolP (_ \in _).
      by rewrite -in_setE.
    rewrite mulr0 => /esym/eqP.
    by rewrite (negbTE r0).
  rewrite /set1 /mkset /= /charac_sfun'.
  rewrite -in_setE in At.
  by rewrite At mulr1 /charac_codom (negbTE r0) AT.
have [A0|A0] := boolP (A == set0).
  rewrite /charac_codom.
  rewrite (_ : _ @^-1` _ = setT).
    exact: measurableT.
  rewrite predeqE => t; split => //= _.
  case: k => [[|m]] /=; last first.
    move=> H.
    exfalso.
    move: H.
    apply/negP.
    rewrite -leqNgt.
    by rewrite /charac_codom (negbTE r0) (negbTE AT) A0.
  move=> ?.
  rewrite /set1 /mkset /= /charac_sfun' (negbTE r0) (negbTE AT) A0.
  rewrite (_ : _ \in _ = false) ?mulr0//.
  apply/negbTE.
  by rewrite notin_setE (eqP A0).
rewrite /charac_sfun' /charac_codom /=.
rewrite [X in measurable X](_ : _ = if k == O :> nat then ~` A else A).
  case: ifPn => _ //.
  exact: measurableC.
case: k => [[|[|m]]] //=; last first.
  move=> H.
  exfalso.
  move: H.
  apply/negP.
  rewrite -leqNgt.
  by rewrite /charac_codom (negbTE r0) (negbTE AT) (negbTE A0).
- move=> ?.
  rewrite (negbTE r0) (negbTE AT) (negbTE A0) /=.
  rewrite /mkset predeqE => t; split => //.
    rewrite /charac_sfun' /= /set1 /=.
    rewrite -(in_setE A).
    case: (_ \in _) => //.
    rewrite mulr0 => /esym/eqP.
    by rewrite (negbTE r0).
  rewrite /set1 /=.
  rewrite -in_setE => ->.
  by rewrite mulr1.
- move=> ?.
  rewrite /charac_sfun' /= /set1 /mkset /=.
  rewrite (negbTE r0) (negbTE AT) (negbTE A0) /=.
  rewrite /mkset predeqE => t; split => //.
  have [tA|tA _] := boolP (t \in A).
    rewrite mulr1 => /eqP.
    by rewrite (negbTE r0).
  by rewrite /setC /= -notin_setE.
- move=> At.
  have [|tA] := boolP (t \in A).
    by rewrite in_setE.
  by rewrite mulr0.
Qed.

Definition charac_sfun := SFun.mk charac_uniq charac_fcodom charac_mpi.

End charac_sfun.

Section simple_function_binary.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.
Let a := seq.filter (fun z => (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0)
  [seq (x, y) | x <- SFun.codom f, y <- SFun.codom g].
Let s (op : R -> R -> R) : seq R := undup (map (fun z => op z.1 z.2) a).

Let fga (op : R -> R -> R) : (fun x => op (f x) (g x)) @` setT = [set x | x \in s op].
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

Definition sfun_bin_pidx (op : R -> R -> R) (k : 'I_(size (s op))) :=
  [set x : 'I_n * 'I_p | (op (SFun.codom f)`_x.1 (SFun.codom g)`_x.2 == (s op)`_k) &&
    (SFun.pi f x.1 `&` SFun.pi g x.2 != set0)]%SET.

Local Lemma sfun_bin_preimageE (op : R -> R -> R) (k : 'I_(size (s op))) : (fun x => op (f x) (g x)) @^-1` [set (s op)`_k] =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx k)
    (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity (\big[setU/set0]_(x : 'I_n * 'I_p |
     op (SFun.codom f)`_x.1 (SFun.codom g)`_x.2 == (s op)`_k)
    (SFun.pi f x.1 `&` SFun.pi g x.2)); last first.
  rewrite /sfun_bin_pidx big_mkcond [in RHS]big_mkcond.
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

Local Lemma sfun_bin_bigcupIE (op : R -> R -> R)(k : 'I_(size (s op))) :
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx k)
    (SFun.pi f x.1 `&` SFun.pi g x.2) =
  \big[setU/set0]_(z <- [seq (x, y) | x <- enum 'I_n, y <- enum 'I_p] |
                     z \in sfun_bin_pidx k)
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

Lemma sfun_bin_pi_cover0 (op : R -> R -> R) :
  \bigcup_(c < size (s op)) sfun_bin_pidx c =
  [set x : {: 'I_n * 'I_p}|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET.
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP/idP => /=.
- move=> [i] _.
  by rewrite inE /= => /eqP/eqP/andP[].
- move=> kl.
  have [i kli] : exists i : 'I_(size (s op)), op (SFun.codom f)`_k (SFun.codom g)`_l = (s op)`_i.
    have : op (SFun.codom f)`_k (SFun.codom g)`_l \in [set of (fun x => op (f x) (g x))].
      rewrite inE /=.
      move/set0P : kl => [t [/pi_nth kt /pi_nth lt]].
      by exists t => //; rewrite -kt -lt.
    by rewrite fga inE /= => /(nthP 0)[x xa H]; exists (Ordinal xa).
  by exists i => //; rewrite inE /= kli eqxx.
Qed.

Let mfg (op : R -> R -> R) (k : 'I_(size (s op))) : measurable ((fun x => op (f x) (g x)) @^-1` [set (s op)`_k]).
Proof.
rewrite sfun_bin_preimageE sfun_bin_bigcupIE.
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; apply SFun.mpi.
Qed.

Definition sfun_add := SFun.mk (undup_uniq _) (fga (fun x y => x + y)) (@mfg (fun x y => x + y)).

Definition sfun_max := SFun.mk (undup_uniq _) (fga (fun x y => maxr x y)) (@mfg (fun x y => maxr x y)).

End simple_function_binary.

Section simple_function_addition_lemmas.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.

Lemma pi_sfun_addE (c : 'I_(ssize (sfun_add f g))) : SFun.pi (sfun_add f g) c =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx c) (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity ((sfun_add f g) @^-1` [set (SFun.codom (sfun_add f g))`_c]) => //.
by rewrite sfun_bin_preimageE.
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

Lemma measure_sfun_bin_pi (mu : {measure set T -> \bar R}) (c : 'I_(ssize (sfun_add f g))) :
  mu (SFun.pi (sfun_add f g) c) =
  (\sum_(kl in sfun_bin_pidx c) mu (SFun.pi f kl.1 `&` SFun.pi g kl.2))%E.
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

(*Section nnsfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Hypothesis r0 : 0 <= r.
Let sfun_cst_ge0 (t : T) : 0 <= sfun_cst point r t. Proof. by []. Qed.

Definition nnsfun_cst := NNSFun.mk sfun_cst_ge0.
End nnsfun_cst.*)

Section charac_sfun.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}) (A : set T).
Hypothesis mA : measurable A.

Lemma charac_ge0 : forall t, 0 <= charac_sfun point r%:nngnum mA t.
Proof.
move=> t.
by rewrite /charac_sfun /= /charac_sfun' mulr_ge0 //.
Qed.

Definition charac_nnsfun := NNSFun.mk charac_ge0.

End charac_sfun.

Section nnsfun_add.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Local Lemma nnsfun_add_ge0 : forall x, 0 <= sfun_add f g x.
Proof. by move=> x; rewrite addr_ge0 //; apply: NNSFun.ge0. Qed.

Definition nnsfun_add := NNSFun.mk nnsfun_add_ge0.

End nnsfun_add.

Section nnsfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).

Local Lemma nnsfun_cst_ge0 : forall x, 0 <= sfun_cst point r%:nngnum x.
Proof. by move=> ?. Qed.

Definition nnsfun_cst := NNSFun.mk nnsfun_cst_ge0.

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
rewrite ge0_sume_distrr; last first.
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
  under eq_bigr do rewrite measure_sfun_bin_pi.
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g))) (\sum_(x in sfun_bin_pidx i)
    ((SFun.codom f)`_x.1 + (SFun.codom g)`_x.2)%:E * m (SFun.pi f x.1 `&` SFun.pi g x.2)))%E.
    apply eq_bigr => i _; rewrite ge0_sume_distrr //; last first.
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
  rewrite -(sfun_bin_pi_cover0 _ _ (fun x y => x + y)).
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
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; exact: SFun.mpi.
have ffg : forall k, m (SFun.pi f k) = (\sum_(l < p) m (SFun.pi f k `&` SFun.pi g l))%E.
  move=> k; rewrite -[in LHS](setIT (SFun.pi f k)) -(bigcup_sfun g) big_distrr /=.
  rewrite additive_ord //; last exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; exact: SFun.mpi.
under [X in _ = (_ + X)%E]eq_bigr do rewrite ffg; rewrite {ffg}.
transitivity (\sum_(i < p) \sum_(i0 < n) ((SFun.codom g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f i0) +
  \sum_(i < n) \sum_(l < p) ((SFun.codom f)`_i)%:E * m (SFun.pi f i `&` SFun.pi g l))%E; last first.
  congr adde; apply eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; exact: SFun.mpi.
rewrite [X in _ = (X + _)%E]exchange_big.
rewrite -big_split; apply eq_bigr => i _.
rewrite -big_split; apply eq_bigr => j _.
rewrite [in RHS]setIC.
rewrite addEFin ge0_muleDl; try exact: NNSFun_ge0.
by rewrite addeC.
Qed.

End sintegralD.

Module FunOrder.
Section FunOrder.
Variables (aT : Type) (d : unit) (T : porderType d).
Implicit Types f g h : aT -> T.

Lemma fun_display : unit. Proof. exact: tt. Qed.

Definition lef f g := `[< forall x, (f x <= g x)%O >].
Local Notation "f <= g" := (lef f g).

Definition ltf f g := `[< (forall x, (f x <= g x)%O) /\ exists x, f x != g x >].
Local Notation "f < g" := (ltf f g).

Lemma ltf_def f g : (f < g) = (g != f) && (f <= g).
Proof.
apply/idP/andP => [fg|[gf fg]]; [split|apply/asboolP; split; [exact/asboolP|]].
- by apply/eqP => gf; move: fg => /asboolP[fg] [x /eqP]; apply; rewrite gf.
- apply/asboolP => x; rewrite le_eqVlt; move/asboolP : fg => [fg [y gfy]].
  by have [//|gfx /=] := boolP (f x == g x); rewrite lt_neqAle gfx /= fg.
- apply/not_existsP => h.
  have : f =1 g by move=> x; have /negP/negPn/eqP := h x.
  by rewrite -funeqE; apply/nesym/eqP.
Qed.

Fact lef_refl : reflexive lef. Proof. by move=> f; apply/asboolP => x. Qed.

Fact lef_anti : antisymmetric lef.
Proof.
move=> f g => /andP[/asboolP fg /asboolP gf]; rewrite funeqE => x.
by apply/eqP; rewrite eq_le fg gf.
Qed.

Fact lef_trans : transitive lef.
Proof.
move=> g f h /asboolP fg /asboolP gh; apply/asboolP => x.
by rewrite (le_trans (fg x)).
Qed.

Definition porderMixin :=
  @LePOrderMixin _ lef ltf ltf_def lef_refl lef_anti lef_trans.

Canonical porderType := POrderType fun_display (aT -> T) porderMixin.

End FunOrder.
Module Exports.
Canonical porderType.
End Exports.
End FunOrder.
Export FunOrder.Exports.

Lemma lef_at (aT : Type) d (T : porderType d) (f : (aT -> T)^nat) x :
  nondecreasing_seq f -> {homo (f^~ x) : n m / (n <= m)%N >-> (n <= m)%O}.
Proof. by move=> nf m n mn; have /asboolP := nf _ _ mn; exact. Qed.

Lemma lefP (aT : Type) d (T : porderType d) (f g : aT -> T) :
  reflect (forall x, (f x <= g x)%O) (f <= g)%O.
Proof. by apply: (iffP idP) => [fg|fg]; [exact/asboolP | apply/asboolP]. Qed.

(* NB: PR in progress *)
Lemma lt_lim (R : realFieldType) (u : (R^o)^nat) (M : R) :
  nondecreasing_seq u -> cvg u -> M < lim u ->
  \forall n \near \oo, M <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, M <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have {}Mu : forall x, M > u x by move=> x; rewrite ltNge; apply/negP.
have : lim u <= M by apply lim_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Grab Existential Variables. all: end_near. Qed.

(* NB: see also cvgPpinfty *)
Lemma nondecreasing_dvg_lt_old (R : realType) (u_ : R^o ^nat) :
  nondecreasing_seq u_ -> ~ cvg u_ ->
  forall M, exists n, forall m, (m >= n)%N -> M <= u_ m.
Proof.
move=> nu du M; apply/not_existsP; apply: contra_not du => Mu.
apply: (@nondecreasing_is_cvg _ _ M) => // n.
have := Mu n => /existsNP[m] /not_implyP [nm] /negP; rewrite -ltNge => /ltW.
exact: (le_trans (nu _ _ nm)).
Qed.

Lemma nondecreasing_dvg_lt (R : realType) (u_ : R^o ^nat) :
  nondecreasing_seq u_ -> ~ cvg u_ -> u_ --> +oo.
Proof.
move=> nu du; apply: contrapT => /cvgPpinfty uoo; apply: du.
move : uoo => /existsNP[l h]; apply: (@nondecreasing_is_cvg _ _ l) => // n.
rewrite leNgt; apply/negP => lun; apply: h; near=> m.
by rewrite (le_trans (ltW lun)) //; apply: nu; near: m; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_lim_sum (R : realType) (I : Type) (r : seq I) (f : I -> (\bar R)^nat)
    (l : I -> \bar R) (P : pred I) :
  (forall n x, P x -> 0 <= f x n)%E ->
  (forall k, f k --> l k) ->
  (fun n => \sum_(k <- r | P k) f k n)%E --> (\sum_(k <- r | P k) l k)%E.
Proof.
elim: r => [_ fl|a b ih f0 fl].
  rewrite !big_nil [X in X --> _](_ : _ = fun=> 0%E); first exact: cvg_cst.
  by under eq_fun do rewrite big_nil.
rewrite big_cons; under eq_fun do rewrite big_cons.
case: ifPn => Pa; last exact: ih.
apply: ereal_cvgD => //; last exact: ih.
have P0l : forall i, P i -> (0 <= l i)%E.
  move=> i Pi; rewrite -(cvg_lim _ (fl i)) // ereal_lim_ge //.
  - by apply/cvg_ex; exists (l i); exact: (fl i).
  - by apply: nearW => // n; exact: f0.
by apply ge0_adde_def; rewrite !inE ?P0l// sume_ge0.
Grab Existential Variables. all: end_near. Qed.
(* /NB: PR in progress *)

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

Section le_sintegral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (m : {measure set T -> \bar R}).

Lemma eq_sintegral (f g : sfun T R) : f =1 g -> sintegral m f = sintegral m g.
Proof.
move=> fg.
rewrite 2!sintegralE (perm_big (SFun.codom g)); last exact: sfun_ext.
apply: eq_bigr => r _.
by move: fg; rewrite -funeqE => ->.
Qed.

Lemma le_sintegral (f g : nnsfun T R) :
  ((f : T -> R) <= g)%O -> (sintegral m f <= sintegral m g)%E.
Proof.
move=> fg.
pose gNf' := sfun_add g (sfun_scale point (-1) f).
have gNf0 : forall x, 0 <= gNf' x.
  move=> x /=.
  by rewrite mulN1r subr_ge0; apply/lefP.
pose gNf := NNSFun.mk gNf0.
have gfgf : g =1 sfun_add f gNf.
  by move=> x; rewrite /= addrCA mulN1r subrr addr0.
by rewrite (eq_sintegral gfgf) sintegralD lee_addl // sintegral_ge0.
Qed.

Lemma is_cvg_sintegral (f : (nnsfun T R)^nat) :
  nondecreasing_seq (f : (T -> R)^nat) -> cvg (fun n => sintegral m (f n)).
Proof.
move=> f_ndecr; apply/cvg_ex; eexists.
apply/nondecreasing_seq_ereal_cvg => a b ab.
by apply: le_sintegral => //; apply/f_ndecr.
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
Variable (f : (nnsfun T R)^nat).
Hypothesis f_ndecr : nondecreasing_seq (f : (T -> R)^nat).
Variable (g : nnsfun T R).
Hypothesis gf :
  forall x : T, cvg (f^~ x : _ -> R^o) -> g x <= lim (f^~ x : _ -> R^o).

Local Definition fgeg c : (set T)^nat := fun n => [set x | c * g x <= f n x].

Local Lemma fgeg_ndecr c : {homo fgeg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; apply/subsetPset => x /le_trans; apply; move: x.
exact/lefP/f_ndecr.
Qed.

Local Lemma le_fgeg c : {homo
  (fun p x => g x * (x \in fgeg c p)%:R) : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; apply/asboolP => t; rewrite ler_pmul // ?NNSFun.ge0// ler_nat.
have [/=|//] := boolP (t \in fgeg c n); rewrite in_setE => cnt.
by have := fgeg_ndecr c nm => /subsetPset/(_ _ cnt); rewrite -in_setE => ->.
Qed.

Local Lemma fgeg_total c : c < 1 -> \bigcup_n fgeg c n = setT.
Proof.
move=> c1; rewrite predeqE => x; split => // _.
have := NNSFun.ge0 g x; rewrite le_eqVlt => /orP[/eqP gx0|gx0].
  by exists O => //; rewrite /fgeg /= -gx0 mulr0 NNSFun.ge0.
have [cf|df] := pselect (cvg (f^~ x : _ -> R^o)).
  have fcg : lim (f^~ x : nat -> R^o) > c * g x.
    by rewrite (lt_le_trans _ (gf cf)) // gtr_pmull.
  have [n fcgn] : exists n, f n x >= c * g x.
    move: (@lt_lim _ (f^~ x) (c * g x) (lef_at x f_ndecr) cf fcg) => [n _ nf].
    by exists n; apply: nf => /=.
  by exists n => //; rewrite /fgeg /= ltW.
have := nondecreasing_dvg_lt (lef_at x f_ndecr) df.
move=> /cvgPpinfty/(_ (c * g x))[n _ cgf].
by exists n => //; apply: cgf => /=.
Qed.

Local Lemma measurable_fgeg c n : measurable (fgeg c n).
Proof.
rewrite /fgeg [X in _ X](_ : _ =
  \big[setU/set0]_(y <- SFun.codom g)
    \big[setU/set0]_(x <- SFun.codom (f n) | c * y <= x)
        ((g @^-1` [set y]) `&` (f n @^-1` [set x]))); last first.
  rewrite predeqE => t; split.
    rewrite /= => cgf.
    rewrite -bigcup_set.
    exists (g t); first exact: SFunfcodom.
    rewrite -bigcup_set_cond; exists (f n t) => //.
    by apply/andP; split => //; exact: SFunfcodom.
  rewrite -bigcup_set => -[r /= gr].
  by rewrite -bigcup_set_cond => -[r' /andP[r'f crr']] [/= -> ->].
apply bigsetU_measurable => x _.
apply bigsetU_measurable => y xcy.
by apply: measurableI; exact: measurable_preimage_set1.
Qed.

(* lemma 1.6 *)
Lemma nondecreasing_sintegral_lim_lemma :
  (sintegral mu g <= lim (sintegral mu \o f))%E.
Proof.
suff ? : forall c, 0 < c < 1 ->
    (c%:E * sintegral mu g <= lim (sintegral mu \o f))%E.
  by apply/lee_mul01Pr => //; exact: sintegral_ge0.
move=> c /andP[c0 c1].
pose g1' n := preimgI_sfun g (measurable_fgeg c n).
have g1'_ge0 n x : 0 <= g1' n x by rewrite /g1' mulr_ge0 ?NNSFun.ge0.
pose g1 n := NNSFun.mk (g1'_ge0 n).
have fgecg1 n x : c * g1 n x <= f n x.
  rewrite /g1 /=; have [xSn|xSn] := boolP (x \in _).
    by rewrite mulr1; rewrite in_setE in xSn.
  by rewrite 2!mulr0 NNSFun.ge0.
have cg1_ge0 n x : 0 <= (sfun_scale point c (g1 n)) x.
  by rewrite mulr_ge0 //; [exact: ltW | exact: NNSFun.ge0].
have {fgecg1}int_fgecg1 n : (c%:E * sintegral mu (g1 n) <= sintegral mu (f n))%E.
  rewrite -(sintegralK point mu c (g1 n)).
  apply: (@le_sintegral _ point _ mu (NNSFun.mk (cg1_ge0 n)) (f n)) => /=.
  by apply/lefP => x /=; rewrite fgecg1.
suff {int_fgecg1}<- : lim (fun n => sintegral mu (g1 n)) = sintegral mu g.
  have is_cvg_g1 : cvg (fun n => sintegral mu (g1 n)).
    by apply: is_cvg_sintegral => //=; exact: le_fgeg.
  rewrite -elimZ //.
  apply: lee_lim => //; [exact: is_cvg_ereal_cvgZ | exact: is_cvg_sintegral |].
  by apply: nearW; exact: int_fgecg1.
suff : (fun n => sintegral mu (g1 n)) --> sintegral mu g by apply/cvg_lim.
rewrite [X in X --> _](_ : _ = (fun n => (\sum_(k < ssize g)
    ((SFun.codom g)`_k)%:E *
    mu (g @^-1` [set (SFun.codom g)`_k] `&` fgeg c n))%E)); last first.
  rewrite funeqE => n.
  rewrite sintegralE.
  transitivity (\sum_(x <- SFun.codom g) x%:E * mu (g1 n @^-1` [set x]))%E.
    rewrite (_ : SFun.codom (g1 n) = preimgI_codom g (fgeg c n)) //.
    rewrite /preimgI_codom /=; case: ifPn=> [|_].
    - case/orP => [|/eqP cnT].
      + rewrite mem_filter /= => /andP[].
        rewrite /set1 /mkset /= => /set0P[t [ gt0 cnt]] g0.
        rewrite big_filter big_mkcond; apply eq_bigr => r _.
        case: ifPn => // /negPn/eqP I0.
        rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0//.
        rewrite predeqE => x; split => //=.
        have [xcn|xcn] := boolP (x \in _).
          by rewrite mulr1 => gxr; rewrite -I0; split => //; rewrite -in_setE.
        rewrite mulr0 => r0.
        by move: I0; rewrite predeqE => /(_ t)[+ _]; apply; rewrite -r0.
      + rewrite big_filter big_mkcond; apply eq_bigr => r _.
        case: ifPn => // /negPn/eqP I0.
        rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 //.
        rewrite predeqE => x; split => //=; rewrite /set1 /mkset cnT.
        have [xT|] := boolP (x \in _).
          by rewrite mulr1 => gxr; rewrite -I0 cnT.
        have : setT x by [].
        by rewrite -in_setE => ->.
    - rewrite -cats1 big_cat /= big_cons big_nil mul0e !adde0.
      rewrite big_filter big_mkcond; apply eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      have [/eqP ->|r0] := boolP (r == 0); first by rewrite mul0e.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 //.
      rewrite predeqE => x; split => //=; rewrite /set1 /mkset.
      have [xT|_ ] := boolP (x \in _).
        by rewrite mulr1 => gxr; rewrite -I0; split => //; rewrite -in_setE.
      by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  rewrite big_tnth; apply eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0) //=.
  have [/eqP gi0|gi0] := boolP ((SFun.codom g)`_i == 0).
    by rewrite gi0 // 2!mul0e.
  congr (_%:E * mu _)%E.
  rewrite predeqE => x; split => /=.
  - rewrite /mkset /set1 /mkset /=.
    have [xcn|_] := boolP (_ \in fgeg c n).
      by rewrite mulr1 => <-; split => //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE gi0).
  - move=> -[] /=.
    rewrite /set1 /mkset => ->.
    rewrite -in_setE => ->.
    by rewrite mulr1.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(x <- SFun.codom g) x%:E *
    mu (g @^-1` [set x] `&` fgeg c n))%E); last first.
  rewrite funeqE => n; rewrite [in RHS]big_tnth /=.
  apply/eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0) //=; congr (_%:E * mu (_ `&` _))%E.
    exact: set_nth_default.
  rewrite predeqE => t /=; rewrite /set1 /mkset -propeqE.
  by congr (_ = _); exact: set_nth_default.
rewrite sintegralE big_seq.
under [in X in X --> _]eq_fun do rewrite big_seq.
have measurable_g1Ifgeg : forall k i, measurable (g @^-1` [set k] `&` fgeg c i).
  by move=> k i; apply: measurableI;
    [exact: measurable_preimage_set1|exact: measurable_fgeg].
apply: ereal_lim_sum => k.
  move=> x xg; apply: mule_ge0; first by move/SFuncodom_ge0 : xg.
  exact: measure_ge0.
suff : (fun n => mu (g @^-1` [set k] `&` fgeg c n)) --> mu (g @^-1` [set k]).
  exact: ereal_cvgZ.
rewrite [X in _ --> X](_ : _ = mu (\bigcup_n (g @^-1` [set k] `&` fgeg c n))); last first.
  by rewrite -bigcup_distrr fgeg_total// setIT.
apply: cvg_mu_inc => //.
  exact: measurable_bigcup.
move=> n m nm; apply/subsetPset; apply: setIS.
by move/(fgeg_ndecr c) : nm => /subsetPset.
Grab Existential Variables. all: end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (point : T).
Variables (R : realType) (mu : {measure set T -> \bar R}).
Variable (f_ : (nnsfun T R)^nat).
Hypothesis f_ndecr : nondecreasing_seq (f_ : (T -> R)^nat).
Variable (f : nnsfun T R).
Hypothesis f_f : forall x, (f_^~ x : _ -> R^o) --> (f x : R^o).
Let limf_ : forall x, lim (f_^~ x : _ -> R^o) = (f x : R^o).
Proof. by move=> x; apply/cvg_lim => //; exact: f_f. Qed.

(* theorem 1.5 *)
Lemma nondecreasing_sintegral_lim : sintegral mu f = lim (sintegral mu \o f_).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nondecreasing_sintegral_lim_lemma => // x; rewrite -limf_.
have : nondecreasing_seq (sintegral mu \o f_).
  by move=> m n mn; apply (le_sintegral point) => //; apply/f_ndecr.
move=> /nondecreasing_seq_ereal_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=.
apply le_sintegral => //; apply/lefP => x.
rewrite -limf_.
apply: (@nondecreasing_cvg_le _ (f_^~ x : _ -> R^o)) => //.
  exact: (lef_at x f_ndecr).
by apply/cvg_ex; exists (f x); exact: f_f.
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
exists (@nnsfun_cst T point R (Nonneg.NngNum _ (ler0n _ O))) => //.
rewrite /sintegral /= big1 //= => k _.
rewrite (_ : _%:E = 0%E) ?mul0e//; congr EFin.
by move: k => [[|]].
Qed.

Lemma integral0 : integral (fun=> 0%E) = 0%E.
Proof.
pose cst0 : nnsfun T R := nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).
rewrite /integral /=; apply/eqP; rewrite eq_le; apply/andP; split.
  apply/ub_ereal_sup => /= x [f /= f0 <-].
  have /eq_sintegral -> : f =1 cst0.
    move=> t /=.
    apply/eqP; rewrite eq_le; apply/andP; split.
      exact: f0.
    exact: NNSFun.ge0.
  by rewrite /= sintegralE /= big_cons big_nil adde0 mul0e.
apply/ereal_sup_ub => /=; exists cst0 => //.
by rewrite /= sintegralE /= big_cons big_nil adde0 mul0e.
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

(* TODO: document *)
Definition cvg_seq_fun_real (T : measurableType) (R : realFieldType)
    (g : (T -> R)^nat) (f : T -> \bar R) := forall x,
  if pselect (cvg (g^~ x : nat -> R^o)) then
    @EFin _ \o g^~ x --> f x
  else
    f x = +oo%E.

(* NB: PR in progess *)
Section set_of_itv.
Variable (R : numDomainType).
Implicit Type i j : interval R.
Implicit Type x y : R.
Implicit Type a : itv_bound R.

Definition set_of_itv i : set R := [set x | x \in i].

Lemma set_of_itv_mem i x : set_of_itv i x <-> x \in i.
Proof. by move: i => [[[]i1|[]] [[]i2|[]]]. Qed.

End set_of_itv.
(* /NB: PR in progess *)

Section nondecreasing_integral_limit.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R).

(* PR in progress (lebesgue_measure) *)
Parameter measurableR : set (set R).
Parameter measurableR0 : measurableR set0.
Parameter measurableRC : forall A, measurableR A -> measurableR (~` A).
Parameter measurableR_bigcup : forall U : (set R)^nat, (forall i, measurableR (U i)) ->
    measurableR (\bigcup_i (U i)).
Definition R_isMeasurable : isMeasurable R :=
  isMeasurable.Build _ measurableR0 measurableRC measurableR_bigcup.
HB.instance (Real.sort R) R_isMeasurable.
Parameters measurable_itv : forall (i : interval R), measurable (set_of_itv i).

Parameter measurableRbar : set (set \bar R).
Parameter measurableRbar0 : measurableRbar set0.
Parameter measurableRbarC : forall A, measurableRbar A -> measurableRbar (~` A).
Parameter measurableRbar_bigcup : forall U : (set \bar R)^nat, (forall i, measurableRbar (U i)) ->
    measurableRbar (\bigcup_i (U i)).
Definition Rbar_isMeasurable : isMeasurable \bar R :=
  isMeasurable.Build _ measurableRbar0 measurableRbarC measurableRbar_bigcup.
HB.instance (\bar (Real.sort R)) Rbar_isMeasurable.

Parameter measurable_EFin : forall (A : set R), measurable A -> measurable (@EFin _ @` A).
Parameter measurable_coo : forall (y : \bar R), measurable [set x | (y <= x)%E].

(* /PR in progress (lebesgue_measure) *)

Hypothesis f0 : forall x, (0 <= f x)%E.
Hypothesis mf : measurable_fun setT f.
Variable (g : (nnsfun T R)^nat).
Hypothesis g_ndecr : nondecreasing_seq (g : (T -> R)^nat).
Hypothesis gf : cvg_seq_fun_real g f.

(* theorem 2.3 *)
Lemma nondecreasing_integral_lim : integral mu f = lim (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n.
  rewrite /integral.
  apply: ereal_sup_ub; exists (g n) => //= x.
  have := gf x.
  case: pselect => cg /=; last by move=> ->; rewrite lee_pinfty.
  move=> gxfx.
  have <- : lim (@EFin _ \o (g^~ x)) = f x by exact/cvg_lim.
  have : (@EFin _ \o g^~ x) --> ereal_sup [set of @EFin _ \o g^~ x].
    apply: nondecreasing_seq_ereal_cvg => p q pq /=; rewrite lee_fin.
    by move: x {cg gxfx}; apply/lefP/g_ndecr.
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
      have := @gf x.
      case: pselect => // {}cg /= /cvg_lim gxfx.
      by rewrite (le_trans (Gf x)) // gxfx.
    by apply: EFin_lim => //; exact: (lef_at x g_ndecr).
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
    have := @gf x.
    case: pselect => // {}cg /= /cvg_lim gxfx.
    by rewrite (le_trans (Gf x)) // gxfx.
  by apply: EFin_lim => //; exact: (lef_at x g_ndecr).
move/(@nondecreasing_sintegral_lim_lemma _ point _ mu _ g_ndecr) => Gg.
by rewrite (le_trans AG).
Grab Existential Variables. all: end_near. Qed.

End nondecreasing_integral_limit.

Section nnsfun_sum.
Variables (T : measurableType) (point : T) (R : realType) (f : (nnsfun T R)^nat).

Definition nnsfun_sum n :=
  \big[(@nnsfun_add T R)/(nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)))]_(i < n) f i.

Lemma nnsfun_sumE n t : nnsfun_sum n t = \sum_(i < n) (f i t).
Proof.
rewrite /nnsfun_sum.
by elim/big_ind2 : _ => // x g y h <- <-.
Qed.

End nnsfun_sum.

(* TODO: move *)
Lemma preimage_comp T1 T2 rT (g : T1 -> rT) (f : T2 -> rT) (C : set T1) :
  f @^-1` [set g x | x in C] = [set x | f x \in g @` C].
Proof.
rewrite predeqE => t; split => /=.
  by move=> -[r Cr <-]; rewrite inE;  exists r.
by rewrite inE => -[r Cr <-]; exists r.
Qed.

(* TODO: move *)
Lemma measurable_fcoo (R : realType) (T : measurableType) (f : T -> \bar R)
    (y : \bar R) :
  measurable_fun setT f -> measurable [set x | (y <= f x)%E].
Proof.
move=> mf.
rewrite (_ : [set x | (y <= f x)%E] = f @^-1` [set x | (y <= x)%E]) //.
rewrite -[X in measurable X]setIT.
exact/mf/measurable_coo.
Qed.

(* TODO: move? *)
Lemma floor1 (R : realType) : floor (1 : R) = 1.
Proof. by rewrite /floor Rfloor1 (_ : 1 = 1%:R) // Rtointn. Qed.

Lemma floor_neq0 (R : realType) (r : R) : 1 <= r -> floor r != 0.
Proof.
by move/le_floor => r1; rewrite gt_eqF // (lt_le_trans _ r1) // floor1.
Qed.

(* NB: see also near_infty_natSinv_lt *)
Lemma near_infty_natSinv_expn_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, 1 / 2 ^+ n < e%:num.
Proof.
near=> n.
rewrite -(@ltr_pmul2r _ (2 ^+ n)) // -?natrX ?ltr0n ?expn_gt0//.
rewrite mul1r mulVr ?unitfE ?gt_eqF// ?ltr0n ?expn_gt0//.
rewrite -(@ltr_pmul2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // natrX upper_nthrootP //.
near: n; eexists; last by move=> m; exact.
by [].
Grab Existential Variables. all: end_near. Qed.

Section approximation.
Variables (T : measurableType) (point : T) (R : realType).
Variable f : T -> \bar R.
Hypothesis mf : measurable_fun setT f.

Let I n k : interval R := `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[.

Local Lemma I_subU n k : set_of_itv (I n k) `<=`
  set_of_itv (I n.+1 k.*2) `|` set_of_itv (I n.+1 k.*2.+1).
Proof.
move=> r /set_of_itv_mem; rewrite in_itv /= => /andP[Ir rI].
have [rk|rk] := ltP r (k.*2.+1%:R * (2%:R ^- n.+1)).
- left; apply/set_of_itv_mem.
  rewrite in_itv /= rk andbT (le_trans _ Ir)// -muln2 natrM exprS.
  rewrite invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2) divrr ?unitfE//.
  by rewrite mulr1.
- right; apply/set_of_itv_mem.
  rewrite in_itv /= rk /= (lt_le_trans rI)// -doubleS -muln2 natrM exprS.
  rewrite invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2) divrr ?unitfE//.
  by rewrite mulr1.
Qed.

Local Lemma n1_bigsetU n : set_of_itv `[n%:R, n.+1%:R[ =
  \big[setU/set0]_(n * 2 ^ n.+1 <= k < n.+1 * 2 ^ n.+1) set_of_itv (I n.+1 k).
Proof.
rewrite predeqE => r; split => [/set_of_itv_mem|].
- rewrite in_itv /= => /andP[nr rn1]; rewrite -bigcup_set /=.
  exists `|floor (r * 2 ^+ n.+1)|%N.
    rewrite /= mem_index_iota; apply/andP; split.
      rewrite -ltez_nat gez0_abs ?floor_ge0; last first.
        by rewrite mulr_ge0 -?natrX ?ler0n// (le_trans _ nr).
      apply: (@le_trans _ _ (floor (n * 2 ^ n.+1)%:R)); last first.
        apply: le_floor.
        by rewrite natrM natrX ler_pmul2r// -natrX ltr0n expn_gt0.
      by rewrite -(@ler_int R) -RfloorE -Rfloor_natz.
    rewrite -ltz_nat gez0_abs; last first.
      by rewrite floor_ge0 mulr_ge0// -?natrX ?ler0n// (le_trans _ nr).
    rewrite -(@ltr_int R) (le_lt_trans (floor_le _)) //.
    by rewrite PoszM intrM -natrX ltr_pmul2r // ltr0n expn_gt0.
  apply/set_of_itv_mem; rewrite in_itv /=; apply/andP; split.
    rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
    rewrite (le_trans _ (floor_le _)) // -(@gez0_abs (floor _)) // floor_ge0.
    by rewrite mulr_ge0 // ?(le_trans _ nr)// -natrX ler0n.
  rewrite ltr_pdivl_mulr; last by rewrite -natrX ltr0n expn_gt0.
  rewrite (lt_le_trans (lt_succ_Rfloor _))// RfloorE -[in X in _ <= X]addn1.
  rewrite natrD ler_add2r // -(@gez0_abs (floor _)) // floor_ge0.
  by rewrite mulr_ge0// -?natrX ?ler0n// (le_trans _ nr).
- rewrite -bigcup_set => -[/= k].
  rewrite mem_index_iota => /andP[nk kn] /set_of_itv_mem.
  rewrite in_itv /= => /andP[knr rkn].
  apply/set_of_itv_mem; rewrite in_itv /=; apply/andP; split.
    rewrite (le_trans _ knr) // ler_pdivl_mulr// -?natrX ?ltr0n ?expn_gt0//.
    by rewrite -natrM ler_nat.
  rewrite (lt_le_trans rkn) // ler_pdivr_mulr.
    by rewrite -natrX -natrM ler_nat.
  by rewrite -natrX ltr0n expn_gt0.
Qed.

Local Lemma n1_I n x : (n%:R%:E <= f x < n.+1%:R%:E)%E ->
  exists k, (2 ^ n.+1 * n <= k < 2 ^ n.+1 * n.+1)%N /\
    f x \in @EFin _ @` set_of_itv (I n.+1 k).
Proof.
move=> fxn.
have fxE : (real_of_extended (f x))%:E = f x.
  rewrite -EFin_real_of_extended// fin_numE.
  by move: fxn; case: (f x) => // /andP[].
have : f x \in @EFin _ @` set_of_itv `[n%:R, n.+1%:R[.
  rewrite in_setE /=; exists (real_of_extended (f x)) => //.
  by apply/set_of_itv_mem; rewrite in_itv /= -lee_fin -lte_fin !fxE.
rewrite (n1_bigsetU n) inE /= => -[r].
rewrite -bigcup_set => -[k /=].
rewrite mem_index_iota => ? Ir rfx.
exists k; split; first by rewrite !(mulnC (2 ^ n.+1)%N).
by rewrite !inE /=; exists r.
Qed.

Let A n k := if (k < n * 2 ^ n)%N then
  [set x | f x \in @EFin _ @` set_of_itv (I n k)] else set0.

Local Lemma mA n k : measurable (A n k).
Proof.
rewrite /A.
case: ifPn => [kn|]; last by move=> _; exact: measurable0.
rewrite [X in measurable X](_ : _ =
    f @^-1` (@EFin _ @` set_of_itv (I n k)) `&` setT); last first.
  rewrite setIT.
  by rewrite preimage_comp.
exact/mf/measurable_EFin/measurable_itv.
Qed.

Local Lemma trivIsetA n : trivIset setT (A n).
Proof.
apply/trivIsetP => i j _ _.
wlog : i j / (i < j)%N.
  move=> h; rewrite neq_lt => /orP[ij|ji].
    by apply h => //; rewrite lt_eqF.
  by rewrite setIC; apply h => //; rewrite lt_eqF.
move=> ij _.
rewrite /A; case: ifPn => /= ni; last by rewrite set0I.
case: ifPn => /= nj; last by rewrite setI0.
rewrite predeqE => t; split => // -[/=].
rewrite inE => -[r /set_of_itv_mem]; rewrite in_itv /= => /andP[r1 r2] rft.
rewrite inE => -[r' /set_of_itv_mem]; rewrite in_itv /= => /andP[r'1 r'2].
rewrite -rft => -[rr']; rewrite {}rr' {r'} in r'1 r'2.
have := le_lt_trans r'1 r2.
by rewrite ltr_pmul2r ?invr_gt0 ?exprn_gt0// ltr_nat ltnS leqNgt ij.
Qed.

Let B n := [set x | n%:R%:E <= f x ]%E.

Local Lemma  mB n : measurable (B n).
Proof. exact: measurable_fcoo. Qed.

Definition approx_fun : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * (x \in A n k)%:R
  + n%:R * (x \in B n)%:R.

Local Lemma f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E ->
  i != O :> nat -> x \in A n i = false.
Proof.
move=> fx0 i0; apply/negbTE.
rewrite notin_setE /A.
case: ifPn => [/= in2n|]; last by move=> _.
rewrite inE /= => -[r] /set_of_itv_mem; rewrite in_itv /= => /andP[r1 r2].
rewrite fx0 => -[r0]; subst r.
move: r1.
rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
by rewrite mul0r lern0; exact/negP.
Qed.

Local Lemma f0_B0 x (n : nat) : f x = 0%:E -> n != 0%N -> (x \in B n) = false.
Proof.
move=> fx0 n0; apply/negP.
rewrite in_setE /B /=; apply/negP.
by rewrite -ltNge fx0 lte_fin ltr0n lt0n.
Qed.

Local Lemma f0_approx_fun0 n x : f x = 0%E -> approx_fun n x = 0.
Proof.
move=> fx0; rewrite /approx_fun.
have [/eqP ->|n0] := boolP (n == O).
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0 // mulr0 addr0 big1 // => /= i _.
have [i0|i0] := boolP (i == O :> nat).
  by rewrite (eqP i0) mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Local Lemma f_ub_B0 x n : (f x < (n%:R)%:E)%E -> (x \in B n) = false.
Proof.
move=> fxn.
by apply/negbTE/negP; rewrite inE /=; apply/negP; rewrite -ltNge.
Qed.

Local Lemma fpos_approx_fun_neq0 x : (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx_fun n x != 0.
Proof.
move=> /andP[fx_gt0 fxoo].
have fxE : (real_of_extended (f x))%:E = f x.
  rewrite -EFin_real_of_extended// fin_numE.
  by move: fxoo fx_gt0; case: (f x).
rewrite -fxE lte_fin in fx_gt0.
near=> n.
rewrite /approx_fun; apply/negP; rewrite paddr_eq0; last 2 first.
  - apply: sumr_ge0.
    by move=> i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
  - by rewrite mulr_ge0 // ?ler0n.
move/andP.
rewrite psumr_eq0; last first.
  by move=> i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
case => /allP /= An0.
rewrite mulf_eq0 => /orP[|].
  by apply/negP; near: n; exists 1%N => //= m /=; rewrite lt0n pnatr_eq0.
rewrite pnatr_eq0 => /eqP.
have [//|] := boolP (x \in B n).
rewrite /B /= notin_setE /= => /negP.
rewrite -ltNge => fxn _.
have K : (`|floor (real_of_extended (f x) * 2 ^+ n)| < n * 2 ^ n)%N.
  rewrite -ltz_nat gez0_abs; last first.
    by rewrite floor_ge0 mulr_ge0 // -?natrX// ?ler0n// ltW.
  rewrite -(@ltr_int R); rewrite (le_lt_trans (floor_le _)) // PoszM intrM.
  by rewrite -natrX ltr_pmul2r ?ltr0n ?expn_gt0// -lte_fin fxE.
have xAnK : x \in A n (Ordinal K).
  rewrite inE /A ifT //= inE /=; exists (real_of_extended (f x)) => //.
  apply/set_of_itv_mem; rewrite in_itv /=; apply/andP; split.
    rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
    rewrite (le_trans _ (floor_le _)) // -(@gez0_abs (floor _)) // floor_ge0.
    by rewrite mulr_ge0 // ?ltW// -natrX ltr0n expn_gt0.
  rewrite ltr_pdivl_mulr // -?natrX ?ltr0n ?expn_gt0//.
  rewrite (lt_le_trans (lt_succ_Rfloor _))// RfloorE -[in X in _ <= X]addn1.
  rewrite natrD ler_add2r // -{1}(@gez0_abs (floor _)) // floor_ge0.
  by rewrite mulr_ge0// -?natrX ?ler0n// ltW.
have := An0 (Ordinal K).
rewrite mem_index_enum => /(_ isT).
apply/negP.
rewrite xAnK mulr1 /= mulf_neq0 //; last first.
  by rewrite gt_eqF// invr_gt0 -natrX ltr0n expn_gt0.
rewrite pnatr_eq0 //= -lt0n absz_gt0 floor_neq0//.
rewrite -ler_pdivr_mulr -?natrX ?ltr0n ?expn_gt0//.
rewrite natrX; apply/ltW; near: n.
exact: near_infty_natSinv_expn_lt (PosNum fx_gt0).
Grab Existential Variables. all: end_near. Qed.


Local Lemma f_ub_approx_fun n x : (f x < n%:R%:E)%E ->
  approx_fun n x == 0 \/ exists k,
    [/\ (0 < k < n * 2 ^ n)%N,
       x \in A n k, approx_fun n x = k%:R / 2 ^+ n &
       f x \in @EFin _ @` set_of_itv (I n k)].
Proof.
move=> fxn; rewrite /approx_fun f_ub_B0 // mulr0 addr0.
set lhs := (X in X == 0); have [|] := boolP (lhs == 0); first by left.
rewrite {}/lhs psumr_eq0; last first.
  by move=> i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
move/allPn => [/= k _].
rewrite mulf_eq0 negb_or mulf_eq0 negb_or -andbA => /and3P[k_neq0 _].
rewrite pnatr_eq0 eqb0 negbK => xAnk.
right.
rewrite (bigD1 k) //= xAnk mulr1 big1 ?addr0; last first.
  move=> i ik.
  have /trivIsetP := @trivIsetA n => /(_ _ _ Logic.I Logic.I ik).
  have [xAni|] := boolP (x \in A n i); last by rewrite mulr0.
  rewrite 2!in_setE in xAnk, xAni.
  by rewrite predeqE => /(_ x)[+ _] => /(_ (conj xAni xAnk)).
exists k; split => //.
  by rewrite lt0n ltn_ord andbT -(@pnatr_eq0 R).
by move: xAnk; rewrite inE /A ltn_ord /= inE /= => -[r Ir rfx]; exists r.
Qed.

Lemma ndecr_approx_fun : nondecreasing_seq approx_fun.
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x.
have [fxn|fxn] := ltP (f x) n%:R%:E.
  rewrite {2}/approx_fun.
  rewrite f_ub_B0 ?mulr0 ?addr0; last first.
    by rewrite (lt_trans fxn) // lte_fin ltr_nat.
  have [/eqP ->|] := f_ub_approx_fun fxn.
    apply: sumr_ge0 => i _; rewrite mulr_ge0 // ?divr_ge0// ?ler0n//.
    by rewrite exprn_ge0.
  case=> k [/andP[k0 kn] xAnk -> _].
  move: (xAnk); rewrite inE {1}/A kn /= in_setE => -[r].
  move/set_of_itv_mem/I_subU => -[|] /set_of_itv_mem rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.
      rewrite in_setE /A k2n /=.
      by rewrite inE /=; exists r => //.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      move=> i ik2n.
      suff : x \in A n.+1 i = false by move=> -> ; rewrite mulr0.
      apply/negbTE/negP => xAi.
      have /trivIsetP/(_ _ _ Logic.I Logic.I ik2n)/= := @trivIsetA n.+1 .
      rewrite predeqE => /(_ x)[+ _].
      rewrite 2!in_setE in xAn1k, xAi.
      by move/(_ (conj xAi xAn1k)).
    rewrite exprS invrM ?unitfE// ?expf_neq0// -muln2 natrM -mulrA (mulrCA 2).
    by rewrite divrr ?mulr1 ?unitfE.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite in_setE /A k2n /= inE /=; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      move=> i ik2n.
      suff : x \in A n.+1 i = false by move=> ->; rewrite mulr0.
      apply/negbTE/negP => xAi.
      have /trivIsetP/(_ _ _ Logic.I Logic.I ik2n)/= := @trivIsetA n.+1.
      rewrite predeqE => /(_ x)[+ _].
      rewrite 2!in_setE in xAn1k, xAi.
      by move/(_ (conj xAi xAn1k)).
    rewrite -[X in X <= _]mulr1 -[X in _ * X <= _](@divrr _ 2%:R) ?unitfE//.
    rewrite mulf_div -natrM muln2 -natrX -natrM -expnSr natrX.
    by rewrite ler_pmul2r ?invr_gt0 ?exprn_gt0// ler_nat.
have /orP[{}fxn|{}fxn] : (n%:R%:E <= f x < n.+1%:R%:E)%E || (n.+1%:R%:E <= f x)%E.
  - by move: fxn; case: leP => /= [_ _|_ ->//]; rewrite orbT.
  - have [k [k1 k2]] := n1_I fxn.
    have xBn : x \in B n by rewrite /B /= inE /=; case/andP : fxn.
    rewrite /approx_fun xBn mulr1 big1 ?add0r; last first.
      move=> /= i _.
      suff : x \in A n i = false by move=> ->; rewrite mulr0.
      apply/negbTE.
      rewrite /A notin_setE ltn_ord /= inE => -[r' /set_of_itv_mem r'Ini r'fx].
      move: xBn; rewrite /B inE /= -{}r'fx lee_fin; apply/negP; rewrite -ltNge.
      move: r'Ini; rewrite /I in_itv/= => /andP[_].
      move/lt_le_trans; apply.
      rewrite ler_pdivr_mulr // -?natrX ?ltr0n ?expn_gt0//.
      by rewrite -natrM ler_nat.
    have -> : x \in B n.+1 = false.
      apply/negbTE; rewrite /B /= notin_setE /= leNgt.
      by case/andP : fxn => _ ->.
    rewrite mulr0 addr0.
    have kn2 : (k < n.+1 * 2 ^ n.+1)%N by case/andP : k1 => _; rewrite mulnC.
    rewrite (bigD1 (Ordinal kn2)) //=.
    have xAn1k : x \in A n.+1 k.
      rewrite in_setE /A.
      have fxE : (real_of_extended (f x))%:E = f x.
        rewrite -EFin_real_of_extended// fin_numE.
        by move: fxn; case: (f x) => // /andP[].
      case: ifPn => /= [knn|/negP//].
      rewrite inE /=.
      exists (real_of_extended (f x)) => //.
      by move: k2; rewrite inE /= => -[r Ir <-].
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      move=> i /= ikn2.
      suff : x \in A n.+1 i = false by move=> ->; rewrite mulr0.
      apply/negbTE/negP => xAi.
      have /trivIsetP := @trivIsetA n.+1 => /(_ _ _ Logic.I Logic.I ikn2)/=.
      rewrite predeqE => /(_ x)[+ _].
      rewrite 2!in_setE in xAn1k, xAi.
      by move/(_ (conj xAi xAn1k)).
    rewrite -natrX ler_pdivl_mulr ?ltr0n // ?expn_gt0// mulrC -natrM ler_nat.
    by case/andP : k1.
- have xBn : x \in B n.
    by rewrite /B /= in_setE /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx_fun xBn mulr1.
  have xBn1 : x \in B n.+1.
    by rewrite /B /= in_setE /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite xBn1 mulr1.
  rewrite big1 ?add0r; last first.
    move=> /= i _.
    suff : x \in A n i = false by move=> ->; rewrite mulr0.
    apply/negbTE.
    rewrite /A ltn_ord.
    apply/negP.
    rewrite in_setE /= inE /= => -[r /set_of_itv_mem].
    rewrite in_itv /= => /andP[r1 r2] rfx.
    move: fxn.
    rewrite -rfx lee_fin.
    apply/negP.
    rewrite -ltNge (lt_le_trans r2) // -natrX ler_pdivr_mulr ?ltr0n ?expn_gt0//.
    by rewrite -natrM ler_nat (ltn_trans (ltn_ord i)) // ltn_pmul2r// expn_gt0.
  rewrite big1 ?add0r ?ler_nat // => /= i _.
  suff : x \in A n.+1 i = false by move=> ->; rewrite mulr0.
  apply/negbTE.
  rewrite /A ltn_ord.
  rewrite notin_setE /= inE /= => -[r /set_of_itv_mem].
  rewrite in_itv/= => /andP[r1 r2] rfx.
  move: fxn; rewrite -rfx lee_fin; apply/negP.
  rewrite -ltNge (lt_le_trans r2)// -natrX ler_pdivr_mulr ?ltr0n ?expn_gt0//.
  by rewrite -natrM ler_nat (leq_trans (ltn_ord i)).
Qed.

Lemma cvg_approx_fun x (f0 : forall x, (0 <= f x)%E) : (f x < +oo)%E ->
  (fun n => approx_fun n x : R^o) --> (real_of_extended (f x) : R^o).
Proof.
move=> fxoo.
have /EFin_real_of_extended fxE : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split.
    by rewrite gt_eqF // (lt_le_trans _ (f0 x)) // lte_ninfty.
  by rewrite lt_eqF.
apply/cvg_distP => _/posnumP[e].
rewrite near_map.
have [/eqP fx0|fx0] := boolP (f x == 0%E).
  by near=> n; rewrite f0_approx_fun0 // fx0 /= subrr normr0.
have /fpos_approx_fun_neq0 [m _ Hm] : (0 < f x < +oo)%E.
  by rewrite fxoo andbT lt_neqAle eq_sym fx0 /= f0.
near=> n.
have mn : (m <= n)%N by near: n; exists m.
have : real_of_extended (f x) < n%:R.
  near: n.
  exists `|floor (real_of_extended (f x))|.+1%N => //= p /=.
  rewrite -(@ler_nat R); apply: lt_le_trans.
  rewrite -addn1 natrD.
  rewrite [X in X + 1](_ : _  = (floor (real_of_extended (f x)))%:~R); last first.
    by rewrite -[in RHS](@gez0_abs (floor _)) // floor_ge0 //; exact/le0R/f0.
  by rewrite -RfloorE lt_succ_Rfloor.
rewrite -lte_fin -fxE => fxn.
have [approx_fun_nx0|] := f_ub_approx_fun fxn.
  by have := Hm _ mn; rewrite approx_fun_nx0.
move=> [k [/andP[k0 kn2n] ? ->]].
rewrite inE /= => -[r /set_of_itv_mem].
rewrite in_itv /= => /andP[k1 k2] rfx.
rewrite (@le_lt_trans _ _ (1 / 2 ^+ n)) //.
  rewrite ler_norml; apply/andP; split.
    rewrite ler_subr_addl -mulrBl -lee_fin -fxE -rfx lee_fin.
    rewrite (le_trans _ k1) // ler_pmul2r ?invr_gt0 -?natrX ?ltr0n ?expn_gt0//.
    by rewrite -(@natrB _ _ 1) // ler_nat subn1 leq_pred.
  rewrite ler_subl_addr -mulrDl -lee_fin -(natrD _ 1) add1n -fxE ltW//.
  by rewrite -rfx lte_fin.
by near: n; exact: near_infty_natSinv_expn_lt.
Grab Existential Variables. all: end_near. Qed.

Lemma dvg_approx_fun x : f x = +oo%E -> ~ cvg (fun n => approx_fun n x : R^o).
Proof.
move=> fxoo.
have approx_fun_x : forall n, approx_fun n x = n%:R.
  move=> n; rewrite /approx_fun.
  have -> : x \in B n by rewrite /B inE /= fxoo lee_pinfty.
  rewrite mulr1 big1 ?add0r// => /= i _.
  have -> : x \in A n i = false.
    (* TODO: lemma? *)
    rewrite /A (ltn_ord i) /=.
    apply/negbTE.
    rewrite notin_setE /= inE /= => -[? _].
    by rewrite fxoo.
  by rewrite mulr0.
case/cvg_ex => /= l.
have [l0|l0] := @leP _ R 0 l.
- move/cvg_distP => /(_ _ ltr01).
  rewrite near_map => -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /=.
  move/(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP.
  rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ger0_norm // (le_trans (ceil_ge _)) //.
  by rewrite -(@gez0_abs (ceil _)) // ceil_ge0.
- move/cvg_distP => /(_ _ ltr01).
  rewrite near_map => -[n _].
  move=> /(_ (`|floor l|.+1 + n)%N) /=.
  move/(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP.
  rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n//.
  rewrite ler0_norm //; last by rewrite ltW.
  rewrite (@le_trans _ _ (- floor l)%:~R) //.
    by rewrite mulrNz ler_oppl opprK floor_le.
  by rewrite -(@lez0_abs (floor _)) // floor_le0 // ltW.
Qed.

Lemma cvg_seq_fun_real_approx_fun (f0 : forall x, (0 <= f x)%E) :
  cvg_seq_fun_real approx_fun f.
Proof.
move=> x.
have := lee_pinfty (f x); rewrite le_eqVlt => /orP[/eqP|] fxoo.
  case: pselect => //= H.
  by have := dvg_approx_fun fxoo; tauto.
have h := cvg_approx_fun f0 fxoo.
have /EFin_real_of_extended fxE : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split.
    by rewrite gt_eqF // (lt_le_trans _ (f0 _)) // lte_ninfty.
  by rewrite lt_eqF.
have approx_fun_f : (fun n => (approx_fun n x)%:E) --> f x.
  by rewrite fxE; move/(@cvg_comp _ _ _ _ (@EFin _)) : h; exact.
case: pselect => // abs; exfalso.
by apply/abs/cvg_ex; exists (real_of_extended (f x)).
Grab Existential Variables. all: end_near. Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition approx_nnsfun : (nnsfun T R)^nat := fun n => nnsfun_add
  (nnsfun_sum point
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => charac_nnsfun point (Nonneg.NngNum _ (k2n_ge0 (Ordinal h))) (mA n k)
      | right _ => nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0))
     end) (n * 2 ^ n)%N)
  (charac_nnsfun point (Nonneg.NngNum _ (ler0n _ n)) (mB n)).

Lemma approx_nnsfunE n : approx_nnsfun n = approx_fun n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite nnsfun_sumE; congr (_ + _).
by apply eq_bigr => // i _; case: Bool.bool_dec => // /negP; rewrite ltn_ord.
Qed.

Lemma ndecr_approx_nnsfun : nondecreasing_seq (approx_nnsfun : (T -> R)^nat).
Proof. by move=> m n mn; rewrite !approx_nnsfunE; exact: ndecr_approx_fun. Qed.

Lemma cvg_seq_fun_real_approx_nnsfun (f0 : forall t, (0 <= f t)%E) :
  cvg_seq_fun_real approx_nnsfun f.
Proof.
under eq_fun do rewrite approx_nnsfunE.
exact: cvg_seq_fun_real_approx_fun.
Qed.

Lemma approximation (f0 : forall t, (0 <= f t)%E) : exists f_ : (nnsfun T R)^nat,
  nondecreasing_seq (f_ : (T -> R)^nat) /\
  cvg_seq_fun_real f_ f.
Proof.
by exists approx_nnsfun; split; [exact: ndecr_approx_nnsfun |
                            exact: cvg_seq_fun_real_approx_nnsfun].
Qed.

End approximation.

Section nnsfun_scale.
Variables (T : measurableType) (point : T).
Variables (R : realType) (r : R) (f : nnsfun T R).
Variable k : R.
Hypothesis k0 : 0 <= k.

Local Lemma nnsfun_scale_ge0 x : 0 <= sfun_scale point k f x.
Proof. by rewrite mulr_ge0 //; apply: NNSFun.ge0. Qed.

Definition nnsfun_scale := NNSFun.mk nnsfun_scale_ge0.

End nnsfun_scale.

Section semi_linearity.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f g : T -> \bar R).
Hypothesis f0 : forall x, (0 <= f x)%E.
Hypothesis mf : measurable_fun setT f.
Hypothesis g0 : forall x, (0 <= g x)%E.
Hypothesis mg : measurable_fun setT g.

Lemma integralK k : 0 <= k ->
  integral mu (fun x => k%:E * f x)%E = (k%:E * integral mu f)%E.
Proof.
rewrite le_eqVlt => /orP[/eqP <-|k0].
  under eq_fun do rewrite mul0e.
  by rewrite mul0e integral0.
have [f_ [f_ndecr cf]] := approximation point mf f0.
pose kf := fun n => nnsfun_scale point (f_ n) (ltW k0).
rewrite (@nondecreasing_integral_lim _ point _ mu (fun x => k%:E * f x)%E _ kf); last 3 first.
  - by move=> t; rewrite mule_ge0 //; exact: ltW.
  - move=> m n mn; apply/lefP => x.
    by rewrite ler_pmul //;[exact: ltW|exact: NNSFun.ge0|exact/lefP/f_ndecr].
  - (* TODO: lemma? *) move=> t.
    have := cf t.
    case: pselect => /= [cft|cft ftoo].
      case: pselect => [/= ckft /(@ereal_cvgZ _ _ _ k)|ckft]; first exact: cvg_trans.
      by exfalso; apply: ckft; apply: is_cvgZr.
    case: pselect => h /=.
      exfalso.
      apply: cft; move: h.
      by rewrite is_cvgZrE // gt_eqF.
    (* NB: lemma? *)
    by rewrite ftoo /mule /= gt_eqF// lte_fin k0.
rewrite (_ : sintegral mu \o _ = fun n => sintegral mu (sfun_scale point k (f_ n))) //.
rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (f_ n))%E); last first.
  by rewrite funeqE => n; rewrite sintegralK.
rewrite elimZ; last exact: is_cvg_sintegral.
by rewrite -(nondecreasing_integral_lim point mu f0).
Qed.

Lemma integralD : integral mu (f \+ g)%E = (integral mu f + integral mu g)%E.
Proof.
have [f_ [f_ndecr cf]] := approximation point mf f0.
have [g_ [g_ndecr cg]] := approximation point mg g0.
pose fg := fun n => nnsfun_add (f_ n) (g_ n).
rewrite (@nondecreasing_integral_lim _ point _ _ _ _ fg); last 3 first.
  by move=> x; rewrite adde_ge0.
  (* TODO: lemma *)
  move=> m n mn; apply/lefP => t.
  by apply: ler_add; [exact/lefP/f_ndecr | exact/lefP/g_ndecr].
  (* TODO: lemma *)
  move=> t.
  have := cf t.
  case: pselect => [cf_ /= f_f|cf_ /= ftoo].
    have := cg t.
    case: pselect => [cg_ /= g_g|g_dvg /= gtoo].
      have : cvg (fun n => f_ n t + g_ n t : R^o) by exact: is_cvgD.
      case: pselect => //= _ _.
      rewrite [X in X --> _](_ : _ = (fun n => (@EFin _ \o f_^~ t) n + (@EFin _ \o g_^~ t) n)%E) //.
      by apply: ereal_cvgD => //; apply: ge0_adde_def => /=; rewrite inE.
    case: pselect => [cf_g_|_]/=.
      exfalso; apply: g_dvg.
      by move: cf_g_; rewrite is_cvgDrE.
    by rewrite gtoo addeC addooe // gt_eqF // (lt_le_trans _ (f0 t)) // lte_ninfty.
  case: pselect => [cf_g_ /=|/= _].
    have [cg_|cg_] := pselect (cvg (fun n => g_ n t : R^o)).
      exfalso; apply: cf_.
      by move: cf_g_; rewrite is_cvgDlE.
    exfalso.
    move/cvg_ex : (cf_g_) => [l f_g_l].
    have /cvgPpinfty/(_ (l + 1))[n _ nl] := nondecreasing_dvg_lt (lef_at t f_ndecr) cf_.
    have /cvgPpinfty/(_ 0)[m _ ml] := nondecreasing_dvg_lt (lef_at t g_ndecr) cg_.
    have f_g_nd : {homo (fun n : nat => f_ n t + g_ n t) : n m / (n <= m)%N >-> n <= m}.
      (* NB: use nondecreasing_seq_fun? *)
      (* TODO: lemma? *)
      move=> a b ab.
      by apply: ler_add; [exact/lefP/f_ndecr | exact/lefP/g_ndecr].
    have := nondecreasing_cvg_le f_g_nd cf_g_ (maxn n m).
    rewrite (cvg_lim _ f_g_l) //.
    apply/negP.
    rewrite -ltNge (@lt_le_trans _ _ (l + 1 + 0)) //.
      by rewrite addr0 ltr_addl.
    rewrite ler_add //.
      by apply: nl => /=; rewrite leq_maxl.
    by apply ml => /=; rewrite leq_maxr.
  by rewrite ftoo addooe // gt_eqF// (lt_le_trans _ (g0 t))// lte_ninfty.
rewrite (_ : sintegral mu \o _ = fun n => sintegral mu (f_ n) + sintegral mu (g_ n))%E; last first.
  by rewrite funeqE /= => n /=; rewrite sintegralD.
rewrite (nondecreasing_integral_lim point _ f0 f_ndecr cf).
rewrite (nondecreasing_integral_lim point _ g0 g_ndecr cg).
rewrite ereal_limD //; try exact: is_cvg_sintegral.
rewrite ge0_adde_def => //; rewrite inE.
- apply: ereal_lim_ge.
  exact: is_cvg_sintegral.
  by apply: nearW => n; exact: sintegral_ge0.
- apply: ereal_lim_ge.
  exact: is_cvg_sintegral.
  by apply: nearW => n; exact: sintegral_ge0.
Qed.

Lemma le_integral : (forall x : T, f x <= g x)%E -> (integral mu f <= integral mu g)%E.
Proof.
move=> fg.
have [f_ [f_ndecr cf]] := approximation point mf f0.
rewrite (nondecreasing_integral_lim point _ f0 f_ndecr cf).
apply: ereal_lim_le; first exact: is_cvg_sintegral.
near=> n; apply ereal_sup_ub => /=; exists (f_ n) => // t.
rewrite (le_trans _ (fg t)) //.
have := cf t.
case: pselect => [/= cf_ f_ft|/= _ ->]; last by rewrite lee_pinfty.
have := lee_pinfty (f t).
rewrite le_eqVlt => /orP[/eqP ->|ftoo]; first by rewrite lee_pinfty.
have /EFin_real_of_extended ftE : f t \is a fin_num.
  rewrite fin_numE gt_eqF/= ?lt_eqF//.
  by rewrite (lt_le_trans _ (f0 t))// lte_ninfty.
move: f_ft; rewrite ftE => /ereal_cvg_real[ft_near f_ft].
set u_ := (X in X --> _) in f_ft.
have <- : lim (u_ : R^o^nat) = real_of_extended (f t) by apply/cvg_lim.
rewrite lee_fin.
apply: nondecreasing_cvg_le => // a b ab.
by rewrite /u_ /=; exact/lefP/f_ndecr.
Grab Existential Variables. all: end_near. Qed.

End semi_linearity.

Lemma ereal_nondecreasing_is_cvg (R : realType)
  (u_ : (\bar R) ^nat) :
  {homo u_ : n m / (n <= m)%N >-> (n <= m)%O} ->
  cvg u_.
Proof.
move=> u_ndecr.
apply/cvg_ex.
eexists.
by apply: nondecreasing_seq_ereal_cvg.
Qed.

Section nnsfun_max.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Local Lemma nnsfun_max_ge0 : forall x, 0 <= sfun_max f g x.
Proof.
move=> x /=.
(* NB: lemma? *)
by rewrite /maxr; case: ifPn => _; exact: NNSFun.ge0.
Qed.

Definition nnsfun_max := NNSFun.mk nnsfun_max_ge0.

End nnsfun_max.

Section nnsfun_bigmax.
Variables (T : measurableType) (point : T) (R : realType) (f : (nnsfun T R)^nat).

Definition nnsfun_bigmax n := \big[(@nnsfun_max T R)/(nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)))]_(i < n) f i.

Lemma nnsfun_bigmaxE n t : nnsfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof.
rewrite /nnsfun_bigmax.
by elim/big_ind2 : _ => // x g y h <- <-.
Qed.

End nnsfun_bigmax.

(* PR in progress *)
Module Bigmax.
Section bigmax.
Variables (d : unit) (T : orderType d).

Local Notation max := Order.max.

Lemma bigmax_mkcond I r (P : pred I) (F : I -> T) x :
  \big[max/x]_(i <- r | P i) F i =
     \big[max/x]_(i <- r) (if P i then F i else x).
Proof.
elim: r x => [x|i r ih x]; first by rewrite 2!big_nil.
rewrite 2!big_cons; case: ifPn => Pi; rewrite ih//.
elim: r {ih} => [|j r ih]; first by rewrite big_nil maxxx.
by rewrite big_cons {1}ih maxCA.
Qed.

Lemma bigmax_split I r (P : pred I) (F1 F2 : I -> T) x :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
  max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof.
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?maxxx //.
by rewrite maxCA -!maxA maxCA.
Qed.

Lemma bigmax_idl I r (P : pred I) (F : I -> T) x :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof.
rewrite -big_filter; elim: [seq i <- r | P i] => [|i l ihl].
  by rewrite big_nil maxxx.
by rewrite big_cons maxCA -ihl.
Qed.

Lemma bigmaxID I r (a P : pred I) (F : I -> T) x :
  \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
    (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof.
under [in X in max X _]eq_bigl do rewrite andbC.
under [in X in max _ X]eq_bigl do rewrite andbC.
rewrite -!(big_filter _ (fun _ => _ && _)) !filter_predI !big_filter.
rewrite ![in RHS](bigmax_mkcond _ _ F) !big_filter -bigmax_split.
have eqmax : forall i, P i ->
  max (if a i then F i else x) (if ~~ a i then F i else x) = max (F i) x.
  by move=> i _; case: (a i) => //=; rewrite maxC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -maxA -bigmax_idl ihl.
Qed.

Lemma bigmax_seq1 I (i : I) (F : I -> T) x :
  \big[max/x]_(j <- [:: i]) F j = max (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigmax_pred1_eq (I : finType) (i : I) (F : I -> T) x :
  \big[max/x]_(j | j == i) F j = max (F i) x.
Proof.
have [e1 <- _ [e_enum _]] := big_enumP (pred1 i).
by rewrite (perm_small_eq _ e_enum) enum1 ?bigmax_seq1.
Qed.

Lemma bigmax_pred1 (I : finType) i (P : pred I) (F : I -> T) x :
  P =1 pred1 i -> \big[max/x]_(j | P j) F j = max (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigmax_pred1_eq. Qed.

Lemma bigmaxD1 (I : finType) j (P : pred I) (F : I -> T) x :
  P j -> \big[max/x]_(i | P i) F i
    = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof.
move=> Pj; rewrite (bigmaxID _ (pred1 j)) [in RHS]bigmax_idl maxA.
by congr max; apply: bigmax_pred1 => i; rewrite /= andbC; case: eqP => //->.
Qed.

Lemma ler_bigmax_cond (I : finType) (P : pred I) (F : I -> T) x i0 :
  P i0 -> (F i0 <= \big[max/x]_(i | P i) F i)%O.
Proof. by move=> Pi0; rewrite (bigmaxD1 _ _ Pi0) le_maxr lexx. Qed.

Lemma ler_bigmax (I : finType) (F : I -> T) (i0 : I) x :
  (F i0 <= \big[max/x]_i F i)%O.
Proof. exact: ler_bigmax_cond. Qed.

Lemma bigmax_lerP (I : finType) (P : pred I) m (F : I -> T) x :
  reflect (x <= m /\ forall i, P i -> F i <= m)%O
    (\big[max/x]_(i | P i) F i <= m)%O.
Proof.
apply: (iffP idP) => [|[lexm leFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite le_maxl =>->.
rewrite bigmax_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; apply: ler_bigmax_cond.
Qed.

Lemma bigmax_sup (I : finType) i0 (P : pred I) m (F : I -> T) x :
  P i0 -> (m <= F i0)%O -> (m <= \big[max/x]_(i | P i) F i)%O.
Proof. by move=> Pi0 ?; apply: le_trans (ler_bigmax_cond _ _ Pi0). Qed.

Lemma bigmax_ltrP (I : finType) (P : pred I) m (F : I -> T) x :
  reflect (x < m /\ forall i, P i -> F i < m)%O
    (\big[max/x]_(i | P i) F i < m)%O.
Proof.
apply: (iffP idP) => [|[ltxm ltFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite lt_maxl =>->.
rewrite bigmax_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; apply: ler_bigmax_cond.
Qed.

Lemma bigmax_gerP (I : finType) (P : pred I) m (F : I -> T) x :
  reflect (m <= x \/ exists2 i, P i & m <= F i)%O
  (m <= \big[max/x]_(i | P i) F i)%O.
Proof.
apply: (iffP idP) => [|[lemx|[i Pi lemFi]]]; last 2 first.
- by rewrite bigmax_idl le_maxr lemx.
- by rewrite (bigmaxD1 _ _ Pi) le_maxr lemFi.
rewrite leNgt => /bigmax_ltrP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -leNgt; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -leNgt; right; exists i.
Qed.

Lemma bigmax_eq_arg (I : finType) i0 (P : pred I) (F : I -> T) x :
  P i0 -> (forall i, P i -> x <= F i)%O ->
  \big[max/x]_(i | P i) F i = F [arg max_(i > i0 | P i) F i]%O.
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le ler_bigmax_cond // andbT.
by apply/bigmax_lerP; split => //; exact: PxF.
Qed.

Lemma bigmax_gtrP (I : finType) (P : pred I) m (F : I -> T) x :
  reflect (m < x \/ exists2 i, P i & m < F i)%O
  (m < \big[max/x]_(i | P i) F i)%O.
Proof.
apply: (iffP idP) => [|[ltmx|[i Pi ltmFi]]]; last 2 first.
- by rewrite bigmax_idl lt_maxr ltmx.
- by rewrite (bigmaxD1 _ _ Pi) lt_maxr ltmFi.
rewrite ltNge => /bigmax_lerP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -ltNge; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -ltNge; right; exists i.
Qed.

Lemma eq_bigmax (I : finType) i0 (P : pred I) (F : I -> T) x :
  P i0 -> (forall i, P i -> x <= F i)%O ->
  {i0 | i0 \in I & \big[max/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists. Qed.

(* TODO: PR *)
Lemma le_bigmax (I : finType) (P : pred I) (F G : I -> T) x :
  (forall i, P i -> F i <= G i)%O ->
  (\big[max/x]_(i | P i) F i <= \big[max/x]_(i | P i) G i)%O.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_maxr 2!le_maxl ba fe /= andbT; have [//|/= af] := leP f a.
by rewrite (le_trans ba) // (le_trans _ fe) // ltW.
Qed.

End bigmax.
Module Exports.
Arguments bigmax_mkcond {d T I r}.
Arguments bigmaxID {d T I r}.
Arguments bigmax_pred1 {d T I} i {P F}.
Arguments bigmaxD1 {d T I} j {P F}.
Arguments ler_bigmax_cond {d T I P F}.
Arguments bigmax_eq_arg {d T I} i0 {P F}.
Arguments eq_bigmax {d T I} i0 {P F}.
End Exports.
End Bigmax.
Export Bigmax.Exports.
(* /PR in progress *)

Lemma nondecreasing_seqP' (d : unit) (T : porderType d) (u_ : T ^nat) :
  nondecreasing_seq u_ -> (forall n, u_ n <= u_ n.+1)%O.
Proof. by move=> u_ndecr -[|n]; exact: u_ndecr. Qed.

Section monotone_convergence_theorem.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f_ : (T -> \bar R)^nat).
Hypothesis mf_ : forall n, measurable_fun setT (f_ n).
Hypothesis f_0 : forall n x, (0 <= f_ n x)%E.
Hypothesis f_ndecr : nondecreasing_seq (f_ : (T -> \bar R)^nat).
Let f := fun x => lim (f_^~ x).

Lemma is_cvg_f_ t : cvg (f_^~ t).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn.
by have /lefP := f_ndecr mn; exact.
Qed.

Definition f2' n : (T -> R)^nat := approx_fun (f_ n).

Definition g_' : (T -> R)^nat := fun k t => \big[maxr/0]_(i < k) (f2' i k) t.

Definition f2 n : (nnsfun T R)^nat := approx_nnsfun point (mf_ n).

Definition g_ : (nnsfun T R)^nat := fun k => nnsfun_bigmax point (fun i => f2 i k) k.

Lemma g_E : g_ = g_' :> (T -> R)^nat.
Proof.
rewrite funeqE => n; rewrite funeqE => t.
rewrite /g_ nnsfun_bigmaxE /g_'; apply eq_bigr => i _.
by rewrite /f2; rewrite approx_nnsfunE.
Qed.

Lemma g_decr : nondecreasing_seq (g_ : (T -> R)^nat).
Proof.
apply: nondecreasing_seqP => n; apply/lefP => t.
rewrite /g_ /= 2!nnsfun_bigmaxE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) f2 i n.+1 t)) //.
  apply: Bigmax.le_bigmax => i _.
  apply/(@nondecreasing_seqP' _ _ (fun n => f2 i n t)) => a b ab.
  rewrite /f2.
  rewrite !approx_nnsfunE.
  have := (ndecr_approx_fun (f_ i) ab).
  move/lefP.
  exact.
rewrite (Bigmax.bigmaxD1 ord_max) // le_maxr; apply/orP; right.
rewrite [X in _ <= X](eq_bigl (fun i => nat_of_ord i < n)%N); last first.
  move=> i /=.
  rewrite ltnNge; apply/idP/idP; apply: contra => ni.
    by apply/eqP/val_inj/eqP; rewrite eqn_leq /= ni andbT -ltnS.
  by rewrite (eqP ni).
rewrite (big_ord_narrow (leqnSn n)).
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_bigl.
Qed.

Lemma is_cvg_g_ t : cvg (fun k : nat => (g_ k t)%:E).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn.
rewrite lee_fin.
by have /lefP := g_decr mn; exact.
Qed.

Local Notation maxe := (Order.join).

(* TODO: move *)
Lemma maxEFin (a b : R) : (maxr a b)%:E = maxe a%:E b%:E.
Proof.
have [ab|ba] := leP a b.
  by rewrite join_r.
by rewrite join_l // lee_fin ltW.
Qed.

(* TODO: move *)
Lemma le_approx_fun (i k : nat) (x : T) : (i < k)%N ->
  ((approx_fun (f_ i) k x)%:E <= f_ i x)%E.
Proof.
move=> ik.
have := lee_pinfty (f_ i x).
rewrite le_eqVlt => /orP[/eqP ->|fixoo].
  by rewrite lee_pinfty.
have H1 : {homo (fun k => approx_fun (f_ i) k x) : n m / (n <= m)%N >-> n <= m}.
  move=> m n mn.
  have /lefP := ndecr_approx_fun (f_ i) mn.
  exact.
have fi0 : forall x, (0 <= f_ i x)%E.
  by move=> y; apply f_0.
have H3 := cvg_approx_fun fi0 fixoo.
have H2 : cvg (fun k => approx_fun (f_ i) k x : R^o).
  apply/cvg_ex.
  by eexists; exact: H3.
have := nondecreasing_cvg_le H1 H2 k.
rewrite -lee_fin.
move/le_trans; apply.
rewrite (@EFin_real_of_extended _ (f_ i x)); last first.
  rewrite fin_numE andbC lt_eqF//= gt_eqF // (lt_le_trans _ (f_0 i x)) //.
  by rewrite lte_ninfty.
rewrite lee_fin.
by move/cvg_lim : H3 => -> //.
Qed.

Lemma g_f (k : nat) (x : T) : ((g_ k x)%:E <= f_ k x)%E.
Proof.
rewrite /g_ nnsfun_bigmaxE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) f_ k x)).
  rewrite (@big_morph _ _ (@EFin R) 0%:E maxe) //; last first.
    by move=> a b; rewrite maxEFin.
  apply Bigmax.le_bigmax => i _.
  rewrite /f2 approx_nnsfunE /=.
  rewrite (@le_trans _ _ (f_ i x)) //; last first.
    have := f_ndecr (ltnW (ltn_ord i)).
    move/lefP.
    exact.
  by apply: le_approx_fun.
exact/Bigmax.bigmax_lerP.
Qed.

Lemma cvg_seq_fun_real_g_f : cvg_seq_fun_real g_ f.
Proof.
have H1 : forall t, (lim (fun n => (g_ n t)%:E) <= lim (fun n => f_ n t))%E.
  move=> t.
  apply: lee_lim.
  exact: is_cvg_g_.
  exact: is_cvg_f_.
  near=> n.
  exact: g_f.
have H2 : forall t n, (lim (fun k => (f2 n k t)%:E) <= lim (fun k => (g_ k t)%:E))%E.
  move=> t n.
  apply: lee_lim.
  apply: ereal_nondecreasing_is_cvg => a b ab.
  rewrite lee_fin /f2 !approx_nnsfunE.
  have := ndecr_approx_fun (f_ n) ab.
  move/lefP.
  exact.
  exact: is_cvg_g_.
  near=> k.
  rewrite /g_ nnsfun_bigmaxE lee_fin.
  have nk : (n < k)%N by near: k; exists n.+1.
  by apply: (@Bigmax.bigmax_sup _ _ _ (Ordinal nk) _ _ (fun i => f2 i k t)).
move=> t.
case: pselect => [_|abs] /=; last first.
  apply/eqP/negPn/negP => ftoo.
  have [r ftr{ftoo}] : exists r, f t = r%:E.
    move ftr : (f t) => r.
    move: r => [r| |] in ftoo ftr *.
    by exists r.
    by rewrite ftr in ftoo.
    have : (0 <= f t)%E.
      rewrite /f.
      apply: ereal_lim_ge => //.
        exact: is_cvg_f_.
      exact: nearW.
    by rewrite ftr.
  have /cvgPpinfty/(_ (r + 1))[n _ nrg_] := nondecreasing_dvg_lt (lef_at t g_decr) abs.
  have := H1 t.
  rewrite -/(f t) ftr => lim_g_r.
  have : ((r + 1)%:E <= lim (fun n : nat => (g_ n t)%:E))%E.
    apply: ereal_lim_ge.
    exact: is_cvg_g_.
    near=> m.
    rewrite lee_fin.
    apply: nrg_.
    near: m.
    by exists n.
  apply/negP.
  rewrite -ltNge.
  by rewrite (le_lt_trans lim_g_r) // lte_fin ltr_addl.
have := @is_cvg_g_ t.
move=> /cvg_ex[l g_l].
suff : l == f t by move=> /eqP <- //.
rewrite eq_le; apply/andP; split.
  rewrite /f.
  rewrite (le_trans _ (H1 t)) //.
  by rewrite (cvg_lim _ g_l).
rewrite /f.
have := lee_pinfty l; rewrite le_eqVlt => /orP[/eqP ->|loo].
  by rewrite lee_pinfty.
rewrite -(cvg_lim _ g_l) //=.
apply: ereal_lim_le.
  exact: is_cvg_f_.
near=> n.
have := lee_pinfty (f_ n t); rewrite le_eqVlt => /orP[/eqP|] fntoo.
  have h := dvg_approx_fun fntoo.
  have K1 : lim (fun k : nat => (f2 n k t)%:E) = +oo%E.
    apply/cvg_lim => //.
    apply/dvg_ereal_cvg.
    rewrite /f2.
    rewrite [X in X --> _](_ : _ = (fun k => approx_fun (f_ n) k t)); last first.
      rewrite funeqE => m.
      by rewrite approx_nnsfunE.
    exact: (nondecreasing_dvg_lt (lef_at t (ndecr_approx_fun (f_ n ))) h).
  have -> : lim (fun k : nat => (g_ k t)%:E) = +oo%E.
    have := H2 t n.
    by rewrite K1 lee_pinfty_eq => /eqP.
  by rewrite lee_pinfty.
have := cvg_approx_fun (f_0 n) fntoo.
move=> approx_fun_f_f_.
have := H2 t n.
suff : lim (fun k : nat => (f2 n k t)%:E) = f_ n t by move=> ->.
have : @EFin _ \o (approx_fun (f_ n))^~ t --> (f_ n t).
  move/(@cvg_comp _ _ _ _ (@EFin _)) : approx_fun_f_f_.
  apply.
  have [r ftr] : exists r, f_ n t = r%:E.
    (* copipe *)
    move ftr : (f_ n t) => r.
    move: r => [r| |] in fntoo ftr *.
    by exists r.
    by rewrite ftr in fntoo.
    have : (0 <= f_ n t)%E := f_0 n t.
    by rewrite ftr.
  by rewrite ftr /=.
move/cvg_lim => <- //.
rewrite /f2.
have ->// : (fun k : nat => (approx_nnsfun point (mf_ n) k t)%:E) = EFin (R:=R) \o (approx_fun (f_ n))^~ t.
rewrite funeqE => k.
by rewrite approx_nnsfunE.
Grab Existential Variables. all: end_near. Qed.

Lemma monotone_convergence_helper : exists g_ : (nnsfun T R)^nat, [/\
  nondecreasing_seq (g_ : (T -> R)^nat), cvg_seq_fun_real g_ f &
  (forall k x, (g_ k x)%:E <= f_ k x)%E ].
Proof.
by exists g_; split; [exact: g_decr | exact: cvg_seq_fun_real_g_f | exact: g_f].
Qed.

Lemma monotone_convergence :
  integral mu f = lim (fun n => integral mu (f_ n)).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have int_f_ndecr : nondecreasing_seq (fun n => integral mu (f_ n)).
    by move=> m n mn; apply: le_integral => // t; apply/lefP/f_ndecr.
  have ub : forall n, (integral mu (f_ n) <= integral mu f)%E.
    move=> n.
    apply: le_integral => // t.
   apply: ereal_lim_ge => //; first exact/ereal_nondecreasing_is_cvg/(lef_at t f_ndecr).
    near=> m.
    have nm : (n <= m)%N by near: m; exists n.
    exact/lefP/f_ndecr.
  apply: ereal_lim_le => //; first exact: ereal_nondecreasing_is_cvg.
  exact: nearW.
have [g_ [g_ndecr g_f g_f_]] := monotone_convergence_helper.
rewrite (@nondecreasing_integral_lim _ point _ mu _ _ g_) //; last first.
  move=> t.
  apply: ereal_lim_ge => //; first exact/ereal_nondecreasing_is_cvg/(lef_at t f_ndecr).
  exact: nearW.
apply: lee_lim.
  exact: is_cvg_sintegral.
  apply: ereal_nondecreasing_is_cvg => //.
  by move=> n m nm; apply le_integral => // t; exact/lefP/f_ndecr.
by apply: nearW => n; apply: ereal_sup_ub; by exists (g_ n).
Grab Existential Variables. all: end_near. Qed.

End monotone_convergence_theorem.
