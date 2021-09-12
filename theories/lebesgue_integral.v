(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets posnum topology normedtype sequences measure.

(******************************************************************************)
(*                         Lebesgue Integral (WIP)                            *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue integral. It starts     *)
(* with simple functions and their integral, provides basic operations        *)
(* (addition, etc.), and proves the properties of their integral              *)
(* (semi-linearity, non-decreasingness). It then defines the integral of      *)
(* measurable functions, proves the approximation theorem, the properties of  *)
(* their integral (semi-linearity, non-decreasingness), the monotone          *)
(* convergence theorem, and Fatou's lemma.                                    *)
(*                                                                            *)
(* References:                                                                *)
(* - Daniel Li, Construction de l'intégrale de Lebesgue, 2011                 *)
(*                                                                            *)
(* Acknowledgment: This work is partly based on MathComp-Analysis meetings    *)
(*                                                                            *)
(*                f ^\+ == the function formed by the non-negative outputs of *)
(*                         f (from a type to the type of extended real        *)
(*                         numbers) and 0 otherwise                           *)
(*                f ^\- == the function formed by the non-positive outputs of *)
(*                         f and 0 o.w.                                       *)
(*                 sfun == type of simple functions                           *)
(*             sfun_cst == constant simple functions                          *)
(*           sfun_scale == scaling of simple functions                        *)
(*        sfun_proj f A == restriction of the simple function f to the domain *)
(*                         A, and 0 elsewhere                                 *)
(*         sfun_add f g == addition of simple functions                       *)
(*         sfun_max f g == max of simple functions                            *)
(*               nnsfun == type of non-negative simple functions              *)
(*     sintegral mu D f == integral of the simple function f over the domain  *)
(*                         D with measure mu                                  *)
(*       nnintegral D f == integral of a nonnegative measurable function f    *)
(*                         over the domain D                                  *)
(*         integral D f == integral of a measurable function over the         *)
(*                         domain D                                           *)
(*       integrable D f == the integral of f w.r.t. D is < +oo                *)
(*      point_cvg D g f == the pointwise convergence of the sequence of       *)
(*                         real-valued functions g towards the extended       *)
(*                         real-valued function f                             *)
(*       dyadic_itv n k == the interval                                       *)
(*                         `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* this comes from the branch "integral sketch" *)
Reserved Notation "f ^\+" (at level 1, format "f ^\+").
Reserved Notation "f ^\-" (at level 1, format "f ^\-").
Reserved Notation "f \|_ D" (at level 10).

(* TODO: PR *)
Definition maxe {R : realDomainType} (x y : \bar R) : \bar R := Order.join x y.

Lemma maxEFin (R : realDomainType) (a b : R) : (maxr a b)%:E = maxe a%:E b%:E.
Proof.
rewrite /maxe; have [ab|ba] := leP a b; first by rewrite join_r.
by rewrite join_l // lee_fin ltW.
Qed.

Definition norme (R : realDomainType) (x : \bar R) := (if 0 <= x then x else - x)%E.

Section funpos.
Local Open Scope ereal_scope.

Definition funenng T (R : realDomainType) (f : T -> \bar R) := fun x => maxe (f x) 0.
Definition funennp T (R : realDomainType) (f : T -> \bar R) := fun x => maxe (- f x) 0.
End funpos.

Notation "f ^\+" := (funenng f).
Notation "f ^\-" := (funennp f).

Lemma ge0_funenngE (T : Type) (R : realDomainType) (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> (forall x, D x -> f^\+ x = f x). (*TODO: notation*)
Proof. by move=> f0 x Dx; rewrite /funenng /maxe join_l ?f0. Qed.

Lemma ge0_funennpE (T : Type) (R : realDomainType) (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> (forall x, D x -> f^\- x = 0%E).
Proof. by move=> f0 x ?; rewrite /funennp /maxe join_r// lee_oppl oppe0 f0. Qed.

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
  cdom : seq R ;
  uniq_cdom : uniq cdom ;
  full_cdom : f @` setT = [set x | x \in cdom] ;
  pi := fun k : 'I_(size cdom) => f @^-1` [set cdom`_k] ;
  mpi : forall k, measurable (pi k) }.
Definition ssize f := size (cdom f).
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

Lemma SFunfcdom t : f t \in SFun.cdom f.
Proof.
have := SFun.full_cdom f.
rewrite predeqE => /(_ (f t))[+ _].
by apply; exists t.
Qed.

Lemma trivIset_sfun (A : set 'I_n) : trivIset A pi.
Proof.
apply/trivIsetP => /=; rewrite -/n => i j _ _ ij.
suff ij0 : [set (SFun.cdom f)`_i] `&` [set (SFun.cdom f)`_j] = set0.
  by rewrite /pi /SFun.pi -preimage_setI ij0 preimage_set0.
apply/eqP/negPn/negP => /set0P[r []]; rewrite /set1 /= => ->{r} /eqP.
by rewrite nth_uniq => //; [exact/negP | exact: SFun.uniq_cdom].
Qed.

Lemma bigcup_sfun : \big[setU/set0]_(i < n) pi i = setT.
Proof.
rewrite predeqE => t; split => // _; rewrite -bigcup_set -preimage_bigcup.
have /(nthP 0)[i ni fit] := SFunfcdom t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

Lemma measurable_preimage_set1 (r : R) : measurable (f @^-1` [set r]).
Proof.
have [[k fkr]|/forallNP fr] :=
    pselect (exists k : 'I_(ssize f), (SFun.cdom f)`_k = r).
  by have := SFun.mpi k; rewrite /SFun.pi fkr.
rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
rewrite predeqE => t; split => //= ftr.
have /(nthP 0)[i fi fift] := SFunfcdom t.
by have := fr (Ordinal fi); rewrite fift.
Qed.

End simple_function_partition.

Section sfun_lemmas1.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.

Local Lemma ltn_pidx x : (index (f x) (SFun.cdom f) < n)%N.
Proof. by rewrite index_mem SFunfcdom. Qed.

Definition pidx x := Ordinal (ltn_pidx x).

Lemma nth_pidx x : (SFun.cdom f)`_(pidx x) = f x.
Proof. by rewrite nth_index //; exact: SFunfcdom. Qed.

Lemma pi_pidx x : SFun.pi f (pidx x) x.
Proof. by rewrite /SFun.pi /preimage mksetE nth_pidx. Qed.

Lemma pi_nth i x : SFun.pi f i x -> (SFun.cdom f)`_i = f x.
Proof. by []. Qed.

Lemma sfun_ge0  : (forall t, 0 <= f t) -> forall k : 'I_(ssize f), 0 <= (SFun.cdom f)`_k.
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
  {subset SFun.cdom f <= SFun.cdom g}.
Proof.
move=> fg r rf.
have := SFun.full_cdom g; rewrite predeqE => /(_ r)[+ _].
apply => /=.
have := SFun.full_cdom f; rewrite predeqE => /(_ r)[_].
by move/(_ rf) => [t _ <-]; exists t.
Qed.

Lemma sfun_ext (f g : sfun T R) : f =1 g -> perm_eq (SFun.cdom f) (SFun.cdom g).
Proof.
move=> fg; apply: uniq_perm; try exact: SFun.uniq_cdom.
by move=> r; apply/idP/idP; exact: sfun_ext_helper.
Qed.

Lemma sfun_size (f g : sfun T R) : f =1 g -> ssize f = ssize g.
Proof.
move/sfun_ext => fg.
by rewrite /ssize; apply: perm_size.
Qed.

End sfun_lemmas2.

(*TODO: measurablePointedType? *)
Section simple_function_constant.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Let cdom := [:: r].
Let f : T -> R := cst r.

Local Lemma sfun_cst_uniq : uniq cdom. Proof. by []. Qed.

Local Lemma sfun_cst_full_cdom : f @` setT = [set x | x \in cdom].
Proof.
rewrite /cdom predeqE => r'; split; first by move=> [t _ <- /=]; rewrite inE.
by rewrite /= inE => /eqP ->{r'}; exists point.
Qed.

Let pi := fun k : 'I_1 => f @^-1` [set cdom`_k].

Local Lemma sfun_cst_mpi (k : 'I_1) : measurable (pi k).
Proof.
rewrite (_ : pi _ = setT); first exact: measurableT.
by rewrite predeqE => t; split => // _; rewrite (ord1 k).
Qed.

Definition sfun_cst :=  SFun.mk sfun_cst_uniq sfun_cst_full_cdom sfun_cst_mpi.

Lemma ssize_sfun_cst : ssize sfun_cst = 1%N. Proof. by []. Qed.

End simple_function_constant.

Section simple_function_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variable (f : sfun T R).
Let n := ssize f.
Let cdom := if r == 0 then [:: 0] else [seq r * x | x <- SFun.cdom f].
Let g := fun x => r * f x.

Local Lemma sfun_scale_uniq : uniq cdom.
Proof.
have [/eqP r0|r0] := boolP (r == 0); first by rewrite /cdom r0 eqxx.
rewrite /cdom (negbTE r0) map_inj_uniq; first exact: SFun.uniq_cdom.
by apply: mulrI; rewrite unitfE.
Qed.

Local Lemma sfun_scale_full_cdom : g @` setT = [set x | x \in cdom].
Proof.
rewrite predeqE => r'; split.
  case => t _ <-{r'}; rewrite mksetE /cdom.
  have [/eqP r0|r0] := boolP (r == 0);first by rewrite /g r0 mul0r inE.
  by apply/mapP; exists (f t) => //; exact: SFunfcdom.
rewrite /= /cdom; have [/eqP r0|r0 /mapP[r'']] := boolP (r == 0).
  by rewrite inE => /eqP ->{r'}; exists point => //; rewrite /g r0 mul0r.
have := SFun.full_cdom f.
by rewrite predeqE => /(_ r'') /= [_ /[apply]] [t] _ <-{r''} ->{r'}; exists t.
Qed.

Let pi := fun k => g @^-1` [set cdom`_k].

Local Lemma sfun_scale_mpi (k : 'I_(size cdom)) : measurable (pi k).
Proof.
have [/eqP r0|r0] := boolP (r == 0).
  move: k; rewrite /pi /cdom r0 eqxx /= => k.
  rewrite (_ : mkset _ = setT); first exact: measurableT.
  by rewrite predeqE => t; split => // _; rewrite mksetE ord1 /g r0 mul0r.
move=> [:k'n]; have @k' : 'I_n.
  apply: (@Ordinal _ k); abstract: k'n.
  by rewrite /ssize /= (leq_trans (ltn_ord k)) // /cdom (negbTE r0) size_map.
rewrite /pi (_ : _ @^-1` _ = SFun.pi f k'); first exact: SFun.mpi.
rewrite predeqE => t; split.
  rewrite /cdom /preimage mksetE {1}(negbTE r0) (nth_map 0) //.
  by apply: mulrI; rewrite unitfE.
rewrite /SFun.pi /preimage mksetE /= /g => ->.
by rewrite /cdom {1}(negbTE r0) (nth_map 0).
Qed.

Definition sfun_scale :=
  SFun.mk sfun_scale_uniq sfun_scale_full_cdom sfun_scale_mpi.

End simple_function_scale.

(* TODO: PR? *)
Lemma setTP (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.

(* NB: PR? *)
Lemma notin_setE T (A : set T) x : x \notin A = (~ A x) :> Prop.
Proof.
by rewrite propeqE; split => [/asboolP//|]; apply: contra_notN; rewrite in_setE.
Qed.

Section simple_function_scale_lemmas.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variable (f : sfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma ssize_sfun_scale0 : ssize (sfun_scale point 0 f) = 1%N.
Proof. by rewrite /ssize /= eqxx. Qed.

Lemma ssize_sfun_scale_neq0 : r != 0 -> ssize (sfun_scale point r f) = ssize f.
Proof. by move=> r0; rewrite /ssize /= (negbTE r0) size_map. Qed.

Lemma sfun_scale0 : sfun_scale point 0 f = sfun_cst point 0.
Proof.
Abort.

End simple_function_scale_lemmas.

Section simple_function_projection.
Variables (T : measurableType) (point : T) (R : realType) (f : sfun T R).
Variable (A : set T).
Hypothesis mA : measurable A.

Let g (x : T) : R := f x * (x \in A)%:R.

Let cdom : seq R :=
  let s := [seq y <- SFun.cdom f | f @^-1` [set y] `&` A != set0] in
  if 0 \in s then s else if A == setT then s else
  if A == set0 then [:: 0] else 0 :: s.

Local Lemma sfun_proj_cdom_subset a : a != 0 -> a \in cdom -> a \in SFun.cdom f.
Proof.
move=> a0; rewrite /cdom.
case: ifPn => _; first by rewrite mem_filter => /andP[].
case: ifPn => _; first by rewrite mem_filter => /andP[].
case: ifPn => _; first by rewrite inE (negbTE a0).
by rewrite inE (negbTE a0) /= mem_filter => /andP[].
Qed.

Local Lemma sfun_proj_uniq : uniq cdom.
Proof.
rewrite /cdom; case: ifPn => f0; first exact/filter_uniq/SFun.uniq_cdom.
case: ifPn => [_|/setTP[t At]]; first exact/filter_uniq/SFun.uniq_cdom.
case: ifPn => //= /set0P[t' At']; rewrite (filter_uniq _ (SFun.uniq_cdom f)).
by rewrite andbT.
Qed.

Local Lemma sfun_proj_full_cdom : g @` setT = [set x | x \in cdom].
Proof.
rewrite predeqE => x; split => [[t _]|] /=.
  rewrite /g; have [|tA] := boolP (t \in A).
    rewrite in_setE => tA; rewrite mulr1 => <-; rewrite /cdom.
    case: ifPn => r0.
      by rewrite mem_filter SFunfcdom andbT; apply/set0P; exists t.
    case: ifPn => [_|/setTP[t' At']].
      by rewrite mem_filter SFunfcdom andbT; apply/set0P; exists t.
    case: ifPn => [/eqP A0|_]; first by move: tA; rewrite A0.
    rewrite inE mem_filter SFunfcdom andbT; apply/orP; right; apply/set0P.
    by exists t.
  rewrite mulr0 => <-; rewrite /cdom.
  case: ifPn => // f0; rewrite ifF; first by case: ifPn => _; rewrite inE eqxx.
  by apply/negbTE/setTP; exists t; apply: contraNnot tA; rewrite in_setE.
rewrite /cdom; case: ifPn => [f0|f0].
  rewrite mem_filter => /andP[/set0P[t [/= ftx At]]] fx.
  by exists t => //; rewrite /g; move: At; rewrite -in_setE => ->; rewrite mulr1.
case: ifPn => AT.
  rewrite mem_filter => /andP[/set0P[t [fxt At]]] fx.
  by exists t => //; rewrite /g; move: At; rewrite -in_setE => ->; rewrite mulr1.
case: ifPn => [/eqP A0|A0].
  rewrite inE => /eqP ->{x}; rewrite /g; exists point => //.
  rewrite A0 (_ : _ \in _ = false) ?mulr0 //; apply/negbTE.
  by rewrite notin_setE.
rewrite !inE => /orP[/eqP ->{x}|].
  rewrite /g; move/setTP : AT => [t At]; exists t => //.
  rewrite (_ : _ \in _ = false) ?mulr0//.
  by apply/negbTE; apply: contra_notN At; rewrite in_setE.
rewrite mem_filter => /andP[/set0P[t [fxt At]]] fx.
by rewrite /g; exists t => //;rewrite (_ : _ \in _) ?mulr1// in_setE.
Qed.

Let pi := fun k : 'I_(size cdom) => g @^-1` [set cdom`_k].

Lemma sfun_proj_mpi k : measurable (pi k).
Proof.
rewrite /pi; set a := cdom`_k.
have [/eqP a0|a0] := boolP (a == 0).
  rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A) `|` ~` A); last first.
    rewrite predeqE => t; split.
      rewrite /g /= /set1 mksetE; have [tA|tA _] := boolP (t \in A).
        by rewrite mulr1 => <-; left; split => //; rewrite -in_setE.
      by right; rewrite /setC /=; rewrite notin_setE in tA.
    move=> [[<- At]|At].
      rewrite /= /mkset /set1 /= /g.
      by move: At; rewrite -in_setE => ->; rewrite mulr1.
    rewrite /= /g.
    move: At; rewrite /setC /=; rewrite -notin_setE => /negbTE => ->.
    by rewrite mulr0.
  apply: measurableU; last by apply: measurableC.
    apply: measurableI => //.
    have [fa|fa] := boolP (a \in SFun.cdom f).
      move: fa => /(nthP 0)[i fi fia].
      rewrite -fia (_ : _ @^-1` _ = SFun.pi f (Ordinal fi)) //.
      exact: SFun.mpi.
    rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
    rewrite predeqE => t; split => // fta; move/negP : fa; apply.
    by rewrite -fta; exact: SFunfcdom.
rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A)); last first.
  rewrite predeqE => t; split.
    rewrite /g /= /set1 mksetE /=; have [tA|tA] := boolP (t \in A).
      by rewrite mulr1 => <-; split => //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE a0).
  move=> [<- At]; rewrite /g /= /mkset /set1 /=.
  by move: At; rewrite -in_setE => ->; rewrite mulr1.
apply: measurableI => //; have /(nthP 0)[i fi fia] : a \in SFun.cdom f.
  by apply: sfun_proj_cdom_subset => //; apply/(nthP 0); exists k.
by rewrite -fia (_ : _ @^-1` _ = SFun.pi f (Ordinal fi)) //; exact: SFun.mpi.
Qed.

Definition sfun_proj :=
  SFun.mk sfun_proj_uniq sfun_proj_full_cdom sfun_proj_mpi.

End simple_function_projection.

Section simple_function_point.
Variables (T : measurableType) (point : T) (R : realType) (r : R) (A : set T).
Hypothesis mA : measurable A.

Definition sfun_point := sfun_proj point (sfun_cst point r) mA.

End simple_function_point.

Section simple_function_binary.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.
Let a := [seq z <- [seq (x, y) | x <- SFun.cdom f, y <- SFun.cdom g] |
  (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0 ].
Let s (op : R -> R -> R) : seq R := undup [seq op z.1 z.2 | z <- a].

Local Lemma sfun_bin_full_cdom (op : R -> R -> R) :
  (fun x => op (f x) (g x)) @` setT = [set x | x \in s op].
Proof.
rewrite predeqE => r; split.
- rewrite /= => -[t _] <-; rewrite /s mem_undup.
  apply/mapP; exists (f t, g t) => //; rewrite mem_filter /=; apply/andP; split.
    by rewrite /mkset /set1 /mkset; apply/set0P; exists t.
  by apply/allpairsP; exists (f t, g t); split => //; apply: SFunfcdom.
- rewrite /= /s mem_undup => /mapP[[i j]].
  rewrite mem_filter /= => /andP[/set0P[t []]].
  rewrite /mkset /set1 /mkset => fti gtj.
  move=> /allpairsP[[i' j']] /= [fi' gj'] [? ?]; subst i' j' => ->.
  by exists t => //; rewrite fti gtj.
Qed.

Definition sfun_bin_pidx (op : R -> R -> R) (k : 'I_(size (s op))) :=
  [set x : 'I_n * 'I_p | (op (SFun.cdom f)`_x.1 (SFun.cdom g)`_x.2 == (s op)`_k)
    && (SFun.pi f x.1 `&` SFun.pi g x.2 != set0)]%SET.

Local Lemma sfun_bin_bigcupIE (op : R -> R -> R)(k : 'I_(size (s op))) :
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx k)
    (SFun.pi f x.1 `&` SFun.pi g x.2) =
  \big[setU/set0]_(z <- [seq (x, y) | x <- enum 'I_n, y <- enum 'I_p] |
                     z \in sfun_bin_pidx k)
    (SFun.pi f z.1 `&` SFun.pi g z.2).
Proof.
rewrite -[in RHS]bigcup_set_cond -bigcup_set_cond.
rewrite predeqE => t; split=> [[[i j] /=]|]; last first.
  case => /= -[i j] /= /andP[H aij] [? ?]; exists (i, j) => //.
  by rewrite /= mem_index_enum.
rewrite !inE /= => /andP[] _ /andP[] /eqP afg fg0 [/= ft gt].
exists (pidx f t, pidx g t) => /=; last by split; exact: pi_pidx.
apply/andP; split => //=.
  apply/flattenP;  exists [seq (pidx f t, x) | x <- enum 'I_p].
    by apply/mapP; exists (pidx f t) => //; rewrite mem_enum.
  by apply/mapP; exists (pidx g t) => //; rewrite mem_enum.
rewrite !inE /= !nth_pidx -afg (pi_nth ft) (pi_nth gt) eqxx /=.
by apply/set0P; exists t; split; exact: pi_pidx.
Qed.

Local Lemma sfun_bin_preimageE (op : R -> R -> R) (k : 'I_(size (s op))) :
  (fun x => op (f x) (g x)) @^-1` [set (s op)`_k]
  = \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx k)
      (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity (\big[setU/set0]_(x : 'I_n * 'I_p |
     op (SFun.cdom f)`_x.1 (SFun.cdom g)`_x.2 == (s op)`_k)
    (SFun.pi f x.1 `&` SFun.pi g x.2)); last first.
  rewrite /sfun_bin_pidx big_mkcond [in RHS]big_mkcond.
  apply eq_bigr => /= -[i j] _ /=; rewrite inE /=.
  by case: ifPn => //= _; case: ifPn => //; rewrite negbK => /eqP.
rewrite -bigcup_set_cond predeqE => t; split=> [fgt|].
  exists (pidx f t, pidx g t) => /=.
    by rewrite !nth_pidx -fgt // mem_index_enum eqxx.
  by split => //; exact: pi_pidx.
by move=> [[i j]] /=; rewrite mem_index_enum /= => /eqP <- [-> ->].
Qed.

Local Lemma sfun_bin_mpi (op : R -> R -> R) (k : 'I_(size (s op))) :
  measurable ((fun x => op (f x) (g x)) @^-1` [set (s op)`_k]).
Proof.
rewrite sfun_bin_preimageE sfun_bin_bigcupIE.
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; apply SFun.mpi.
Qed.

Definition sfun_add := SFun.mk (undup_uniq _)
  (sfun_bin_full_cdom (fun x y => x + y)) (@sfun_bin_mpi (fun x y => x + y)).

Definition sfun_max := SFun.mk (undup_uniq _)
  (sfun_bin_full_cdom maxr) (@sfun_bin_mpi maxr).

Lemma sfun_bin_pi_cover0 (op : R -> R -> R) :
  \bigcup_(c < size (s op)) sfun_bin_pidx c =
  [set x : {: 'I_n * 'I_p}|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET.
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP/idP => /=.
- move=> [i] _.
  by rewrite inE /= => /eqP/eqP/andP[].
- move=> kl.
  have [i kli] : exists i : 'I_(size (s op)), op (SFun.cdom f)`_k (SFun.cdom g)`_l = (s op)`_i.
    have : op (SFun.cdom f)`_k (SFun.cdom g)`_l \in [set of (fun x => op (f x) (g x))].
      rewrite inE /=.
      move/set0P : kl => [t [/pi_nth kt /pi_nth lt]].
      by exists t => //; rewrite -kt -lt.
    by rewrite sfun_bin_full_cdom inE /= => /(nthP 0)[x xa H]; exists (Ordinal xa).
  by exists i => //; rewrite inE /= kli eqxx.
Qed.

End simple_function_binary.

Section simple_function_addition_lemmas.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.

Lemma pi_sfun_addE (c : 'I_(ssize (sfun_add f g))) : SFun.pi (sfun_add f g) c
  = \big[setU/set0]_(x : 'I_n * 'I_p | x \in sfun_bin_pidx c)
      (SFun.pi f x.1 `&` SFun.pi g x.2).
Proof.
transitivity ((sfun_add f g) @^-1` [set (SFun.cdom (sfun_add f g))`_c]) => //.
by rewrite sfun_bin_preimageE.
Qed.

Lemma trivIset_sfunI (D : set T) :
  trivIset setT (fun i : 'I_n * 'I_p => SFun.pi f i.1 `&` SFun.pi g i.2 `&` D).
Proof.
apply/trivIsetP => /= -[k l] [k' l'] _ _ /=.
rewrite xpair_eqE negb_and => /orP[kk'|ll'].
  rewrite setIACA (_ : SFun.pi f k `&` _ `&` _ = set0) ?set0I//.
  rewrite setIACA (_ : SFun.pi f k `&` _ = set0) ?set0I//.
  by move/trivIsetP : (@trivIset_sfun _ _ f setT) => /(_ k k' Logic.I Logic.I kk').
rewrite setIACA (_ : SFun.pi f k `&` _ `&` _ = set0) ?set0I//.
rewrite setIACA (_ : SFun.pi g l `&` _ = set0) ?setI0//.
by move/trivIsetP : (@trivIset_sfun _ _ g setT) => /(_ l l' Logic.I Logic.I ll').
Qed.

Lemma measure_sfun_bin_pi (mu : {measure set T -> \bar R}) (D : set T)
  (mD : measurable D) (c : 'I_(ssize (sfun_add f g))) :
  mu (SFun.pi (sfun_add f g) c `&` D) =
  (\sum_(kl in sfun_bin_pidx c) mu (SFun.pi f kl.1 `&` SFun.pi g kl.2 `&` D))%E.
Proof.
rewrite pi_sfun_addE big_distrl /=.
rewrite (additive_set mu _ _ (@trivIset_sfunI D)) //=.
by move=> -[i j]; apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
Qed.

End simple_function_addition_lemmas.

Module NNSFun.
Section nnsfun.
Variables (T : measurableType) (R : realType).
Record t := mk {f : sfun T R ; ge0 : forall t, 0 <= f t }.
End nnsfun.
Module Exports.
Notation nnsfun := t.
End Exports.
End NNSFun.
Export NNSFun.Exports.
Coercion NNSFun.f : nnsfun >-> sfun.

Hint Resolve NNSFun.ge0 : core.

Section nnsfun_lemmas.
Variables (T : measurableType) (R : realType).

Lemma NNSFun_ge0 (f : nnsfun T R) (k : 'I_(ssize f)) : 0 <= (SFun.cdom f)`_k.
Proof. exact: sfun_ge0. Qed.

Lemma SFuncdom_ge0 (f : nnsfun T R) (r : R) :
  (r \in SFun.cdom f) -> (0 <= r%:E)%E.
Proof.
by move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNSFun_ge0 (Ordinal fi)).
Qed.

End nnsfun_lemmas.

(*Hint Extern 0 (0%E <= ((SFun.cdom _)`__)%:E)%E => solve [apply: NNSFun_ge0] : core.*)

Require Import nngnum.

Section non_negative_simple_function_point.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).
Variables (A : set T).
Hypothesis mA : measurable A.

Local Lemma nnsfun_point_ge0 : forall t, 0 <= sfun_point point r%:nngnum mA t.
Proof. by move=> t /=; rewrite mulr_ge0. Qed.

Definition nnsfun_point := NNSFun.mk nnsfun_point_ge0.

End non_negative_simple_function_point.

Section non_negative_simple_function_constant.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).

Local Lemma nnsfun_cst_ge0 : forall x, 0 <= sfun_cst point r%:nngnum x.
Proof. by move=> ?. Qed.

Definition nnsfun_cst := NNSFun.mk nnsfun_cst_ge0.

End non_negative_simple_function_constant.

Section nnsfun_scale.
Variables (T : measurableType) (point : T).
Variables (R : realType) (r : R) (f : nnsfun T R).
Variable k : R.
Hypothesis k0 : 0 <= k.

Local Lemma nnsfun_scale_ge0 x : 0 <= sfun_scale point k f x.
Proof. by rewrite mulr_ge0. Qed.

Definition nnsfun_scale := NNSFun.mk nnsfun_scale_ge0.

End nnsfun_scale.

Section non_negative_simple_function_add.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Local Lemma nnsfun_add_ge0 : forall x, 0 <= sfun_add f g x.
Proof. by move=> x; rewrite addr_ge0. Qed.

Definition nnsfun_add := NNSFun.mk nnsfun_add_ge0.

End non_negative_simple_function_add.

Section nnsfun_max.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Local Lemma nnsfun_max_ge0 : forall x, 0 <= sfun_max f g x.
Proof. by move=> x /=; rewrite /maxr; case: ifPn. Qed.

Definition nnsfun_max := NNSFun.mk nnsfun_max_ge0.

End nnsfun_max.

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

Section nnsfun_bigmax.
Variables (T : measurableType) (point : T) (R : realType) (f : (nnsfun T R)^nat).

Definition nnsfun_bigmax n := \big[(@nnsfun_max T R)/(nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)))]_(i < n) f i.

Lemma nnsfun_bigmaxE n t : nnsfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof.
rewrite /nnsfun_bigmax.
by elim/big_ind2 : _ => // x g y h <- <-.
Qed.

End nnsfun_bigmax.

Section simple_function_integral.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (f : sfun T R).
Let n := ssize f.
Let A := SFun.pi f.
Let a := SFun.cdom f.
Local Open Scope ereal_scope.

Definition sintegral : \bar R := \sum_(k < n) (a`_k)%:E * mu (A k `&` D).

Lemma sintegralE : sintegral =
  \sum_(x <- SFun.cdom f) x%:E * mu (f @^-1` [set x] `&` D).
Proof.
rewrite big_tnth; apply eq_bigr => i _; congr (_%:E * mu _).
  by apply set_nth_default; rewrite /= ltn_ord.
rewrite /A /SFun.pi; congr (_ @^-1` _ `&` _); rewrite predeqE => r; split;
  by rewrite /set1 mksetE => ->; apply set_nth_default; rewrite ltn_ord.
Qed.

End simple_function_integral.

Lemma sintegral_ge0 (T : measurableType) (R : realType) (D : set T)
  (mD : measurable D) (f : nnsfun T R) (m : {measure set T -> \bar R}) :
  (0 <= sintegral m D f)%E.
Proof.
rewrite /sintegral; apply: sume_ge0 => t _; apply: mule_ge0 => //.
  exact: NNSFun_ge0.
by apply/measure_ge0/measurableI => //; exact/SFun.mpi.
Qed.

Section sintegralK.
Variables (T : measurableType) (point : T) (*NB: measurablePointedType? *).
Variables (R : realType) (m : {measure set T -> \bar R}).
Variables (r : R) (D : set T) (mD : measurable D) (f : nnsfun T R).

Lemma sintegralK : sintegral m D (sfun_scale point r f) = (r%:E * sintegral m D f)%E.
Proof.
have [/eqP ->|r0] := boolP (r == 0).
  rewrite mul0e /sintegral big1 // => i _; rewrite /= eqxx /=.
  case: (m (SFun.pi _ _ `&` _)) => [x| |]; move: i; rewrite ssize_sfun_scale0 => i.
  by rewrite (ord1 i) mul0e.
  by rewrite (ord1 i) /= mul0e.
  by rewrite (ord1 i) /= mul0e.
rewrite /sintegral.
pose cast := cast_ord (ssize_sfun_scale_neq0 point f r0).
rewrite [LHS](eq_bigr (fun k : 'I_(ssize (sfun_scale point r f)) =>
  (r * (SFun.cdom f)`_(cast k))%:E * m (SFun.pi f (cast k) `&` D))%E); last first.
  move=> i _; congr (_%:E * m _)%E.
    rewrite /= (negbTE r0) (nth_map 0) //.
    by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
  rewrite predeqE => x; split.
    rewrite /SFun.pi /= /set1 /= {1}(negbTE r0) (nth_map 0); last first.
      by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
    move=> [/mulrI fxi Dx]; split => //.
    by apply: fxi; rewrite unitfE.
  rewrite /SFun.pi /set1 /= => -[fxi Dx]; split => //.
  rewrite /= fxi {1}(negbTE r0) (nth_map 0) //.
  by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
rewrite ge0_sume_distrr; last first.
  move=> i _; rewrite mule_ge0 //; first exact: NNSFun_ge0.
  by apply: measure_ge0; apply/measurableI => //; exact/SFun.mpi.
pose castK := cast_ord (esym (ssize_sfun_scale_neq0 point f r0)).
rewrite (@reindex _ _ _ [finType of 'I_(ssize (sfun_scale point r f))]
    [finType of 'I_(ssize f)] castK); last first.
  by exists cast => i; by rewrite /cast /castK /= ?(cast_ordKV,cast_ordK).
by apply eq_bigr => i _; rewrite /cast /castK cast_ordKV mulEFin muleA.
Qed.

End sintegralK.

Section sintegralD.
Variables (T : measurableType) (R : realType) (D : set T).
Variables (mD : measurable D) (f g : nnsfun T R).
Variables (m : {measure set T -> \bar R}).
Let n := ssize f.
Let p := ssize g.

Lemma sintegralD : sintegral m D (sfun_add f g) = (sintegral m D f + sintegral m D g)%E.
Proof.
transitivity (\sum_(i < n) \sum_(l < p)
  ((SFun.cdom f)`_i + (SFun.cdom g)`_l)%:E * m (SFun.pi f i `&` SFun.pi g l `&` D))%E.
  rewrite /sintegral.
  under eq_bigr do rewrite (@measure_sfun_bin_pi _ _ _ _ _ D mD).
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g))) (\sum_(x in sfun_bin_pidx i)
    ((SFun.cdom f)`_x.1 + (SFun.cdom g)`_x.2)%:E * m (SFun.pi f x.1 `&` SFun.pi g x.2 `&` D)))%E.
    apply eq_bigr => i _; rewrite ge0_sume_distrr //; last first.
      move=> kl _; rewrite measure_ge0 //; apply: measurableI => //.
      by apply: measurableI; exact: SFun.mpi.
    by apply eq_bigr => x; rewrite !inE => /andP[] /eqP ->.
  rewrite [in RHS]pair_big.
  transitivity (\sum_(p0 in setX [set: 'I_n] [set: 'I_p])
    (((SFun.cdom f)`_p0.1 + (SFun.cdom g)`_p0.2)%:E * m (SFun.pi f p0.1 `&` SFun.pi g p0.2 `&` D)))%E; last first.
    by apply/eq_bigl => // -[/= k l]; rewrite !inE.
  transitivity (
  (\sum_(p0 in [set x : 'I_n * 'I_p|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET )
      ((SFun.cdom f)`_p0.1 + (SFun.cdom g)`_p0.2)%:E * m (SFun.pi f p0.1 `&` SFun.pi g p0.2 `&` D))%E); last first.
    rewrite big_mkcond; apply eq_big => //.
      by move=> x; rewrite !inE.
    move=> [x y] _.
    case: ifPn => //.
    rewrite inE negbK => /eqP ->.
    by rewrite set0I measure0 mule0.
  rewrite -(sfun_bin_pi_cover0 _ _ (fun x y => x + y)).
  rewrite partition_disjoint_bigcup // => i j ij.
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[-[/= k l]].
  rewrite inE /= => /andP[]; rewrite 2!inE.
  move/andP => []/eqP -> _.
  move/andP => [+ _].
  by rewrite (nth_uniq _ _ _ (undup_uniq _)) //; exact/negP.
rewrite /sintegral -/n -/p [RHS]addeC.
have ggf : forall k, m (SFun.pi g k `&` D) = (\sum_(i < n) m (SFun.pi g k `&` SFun.pi f i `&` D))%E.
  move=> k; rewrite -[in LHS](setIT (SFun.pi g k `&` D)) -(bigcup_sfun f) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
under [X in _ = (X + _)%E]eq_bigr do rewrite ggf; rewrite {ggf}.
transitivity
  (\sum_(i < p) (\sum_(j < n) ((SFun.cdom g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f j `&` D)) +
   \sum_(k < n) ((SFun.cdom f)`_k)%:E * m (SFun.pi f k `&` D))%E; last first.
  congr adde; apply eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
have ffg : forall k, m (SFun.pi f k `&` D) = (\sum_(l < p) m (SFun.pi f k `&` SFun.pi g l `&` D))%E.
  move=> k; rewrite -[in LHS](setIT (SFun.pi f k `&` D)) -(bigcup_sfun g) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; apply/measurableI; exact: SFun.mpi.
under [X in _ = (_ + X)%E]eq_bigr do rewrite ffg; rewrite {ffg}.
transitivity (\sum_(i < p) \sum_(j < n) ((SFun.cdom g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f j `&` D) +
  \sum_(i < n) \sum_(l < p) ((SFun.cdom f)`_i)%:E * m (SFun.pi f i `&` SFun.pi g l `&` D))%E; last first.
  congr adde; apply eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
rewrite [X in _ = (X + _)%E]exchange_big.
rewrite -big_split; apply eq_bigr => i _.
rewrite -big_split; apply eq_bigr => j _.
rewrite -[in RHS](setIC (SFun.pi f i)).
by rewrite addEFin ge0_muleDl //;
  [rewrite addeC|exact: NNSFun_ge0|exact: NNSFun_ge0].
Qed.

End sintegralD.

(* TODO: PR? *)
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



(* TODO: PR *)
Lemma ereal_cvgZ (R : realFieldType) (f : (\bar R)^nat) (a : \bar R) c :
  f --> a -> (fun n => c%:E * f n)%E --> (c%:E * a)%E.
Proof.
rewrite (_ : (fun n => c%:E * f n)%E = (mule c%:E) \o f) // => /cvg_comp; apply.
exact: mule_continuous.
Qed.

Lemma is_cvg_ereal_cvgZ (R : realFieldType) (f : (\bar R)^nat) c :
  cvg f -> cvg (fun n => c%:E * f n)%E.
Proof.
move=> /cvg_ex[l fl]; apply/cvg_ex; eexists.
by apply: ereal_cvgZ => //; exact: fl.
Qed.

Lemma ereal_limZ (R : realFieldType) (f : (\bar R)^nat) c : cvg f ->
  lim (fun n => c%:E * f n)%E = (c%:E * lim f)%E.
Proof. by move=> cf; apply/cvg_lim => //; apply: ereal_cvgZ. Qed.

Lemma ereal_cvgN (R : realFieldType) {T : topologicalType} (F : set (set T)) {FF : Filter F} (f : T -> \bar R) a :
  f @ F --> a -> ((fun n => - f n)%E @ F) --> (- a)%E.
Proof. by move=> ?; apply: continuous_cvg => //; exact: oppe_continuous. Qed.

Lemma ereal_limN (R : realFieldType) (f : (\bar R)^nat) : cvg f ->
  lim (fun n => - f n)%E = (- lim f)%E.
Proof.
move=> cf; rewrite -mulN1e -ereal_limZ //.
rewrite (_ : (fun _ => _) = (fun n => -1%:E * f n)%E) // funeqE => n.
by rewrite mulN1e.
Qed.

Lemma ereal_nondecreasing_is_cvg (R : realType) (u_ : (\bar R) ^nat) :
  {homo u_ : n m / (n <= m)%N >-> (n <= m)%O} -> cvg u_.
Proof.
by move=> u_ndecr; apply/cvg_ex; eexists; exact: nondecreasing_seq_ereal_cvg.
Qed.

Lemma nonincreasing_seq_ereal_cvg (R : realType) (u_ : (\bar R)^nat) :
  nonincreasing_seq u_ -> u_ --> ereal_inf (u_ @` setT).
Proof.
move=> u_nincr.
rewrite /ereal_inf.
rewrite [X in X --> _](_ : _ = (fun n => - (- u_ n)))%E; last first.
  by rewrite funeqE => n; rewrite oppeK.
apply: ereal_cvgN.
rewrite [X in _ --> X](_ : _ = ereal_sup [set of (fun n => - u_ n)%E]); last first.
  congr ereal_sup.
  rewrite predeqE => x; split=> [[_ [n _ <-]] <-|[n _] <-]; first by exists n.
  by exists (u_ n) => //; exists n.
(* NB: duplicate nondecreasing_opp for \bar R? *)
apply: nondecreasing_seq_ereal_cvg => /=.
by move=> m n mn; rewrite lee_oppr oppeK u_nincr.
Qed.

Lemma ereal_nonincreasing_is_cvg (R : realType) (u_ : (\bar R) ^nat) :
  nonincreasing_seq u_ -> cvg u_.
Proof.
by move=> u_nincr; apply/cvg_ex; eexists; apply: nonincreasing_seq_ereal_cvg.
Qed.




Section le_sintegral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (m : {measure set T -> \bar R}).

Lemma eq_sintegral (D : set T) (f g : sfun T R) : {in D, f =1 g} ->
  sintegral m D f = sintegral m D g.
Proof.
move=> fg.
rewrite 2!sintegralE (bigID (fun x => f @^-1` [set x] `&` D == set0)) /= big1 ?add0e; last first.
  by move=> r /eqP ->; rewrite measure0 mule0.
apply/esym; rewrite (bigID (fun x => g @^-1` [set x] `&` D == set0)) /= big1 ?add0e; last first.
  by move=> r /eqP ->; rewrite measure0 mule0.
rewrite -big_filter -[in RHS]big_filter.
set lhs := seq.filter _ _; set rhs := seq.filter _ _.
rewrite (perm_big rhs); last first.
  rewrite /lhs /rhs.
  apply uniq_perm; try by rewrite filter_uniq // SFun.uniq_cdom.
  move=> r; rewrite !mem_filter; apply/andP/andP=> -[/set0P[t /= [gt Dt rg]]]; split => //.
  - by apply/set0P; exists t => //; split => //; rewrite mksetE fg// in_setE.
  - have := SFun.full_cdom f; rewrite predeqE => /(_ r)[].
    rewrite mksetE -fg in gt; last by rewrite in_setE.
    have H : [set of f] r by exists t.
    by move/(_ H).
  - by apply/set0P; exists t => //; split => //; rewrite mksetE /= -fg // in_setE.
  - have := SFun.full_cdom g; rewrite predeqE => /(_ r)[].
    rewrite mksetE fg in gt; last by rewrite in_setE.
    have H : [set of g] r by exists t.
    by move/(_ H).
rewrite [in LHS]big_filter [in RHS]big_filter; apply eq_bigr => // r rfD0.
congr (_ * m _)%E; rewrite predeqE => t; split => [|] [<- Dt].
- by split => //; rewrite mksetE fg// in_setE.
- by split => //; rewrite mksetE -fg// in_setE.
Qed.

Lemma le_sintegral (D : set T) (mD : measurable D) (f g : nnsfun T R) :
  (forall x, D x -> f x <= g x) -> (sintegral m D f <= sintegral m D g)%E.
Proof.
move=> fg.
pose gNf' := sfun_proj point (sfun_add g (sfun_scale point (-1) f)) mD.
have gNf0 : forall x, 0 <= gNf' x.
  move=> x /=; rewrite /= mulN1r.
  have [xD|xD] := boolP (x \in D); last by rewrite mulr0.
  by rewrite mulr1 subr_ge0; apply/fg; rewrite -in_setE.
pose gNf := NNSFun.mk gNf0.
have gfgf : {in D, g =1 sfun_add f gNf}.
  by move=> x /= ->; rewrite mulr1 addrCA mulN1r subrr addr0.
by rewrite (eq_sintegral gfgf) sintegralD// lee_addl // sintegral_ge0.
Qed.

Lemma is_cvg_sintegral (D : set T) (mD : measurable D) (f : (nnsfun T R)^nat) :
  (forall x, D x -> nondecreasing_seq (f^~ x)) ->
  cvg (fun n => sintegral m D (f n)).
Proof.
move=> nd_f; apply/cvg_ex; eexists.
apply/nondecreasing_seq_ereal_cvg => a b ab.
by apply: le_sintegral => // => x Dx; apply/nd_f.
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

Definition preimgI_cdom (S : set T) :=
  let s := [seq x <- SFun.cdom g | (g @^-1` [set x]) `&` S != set0] in
  if (0 \in s) || (S == setT) then s else rcons s 0.

Program Definition preimgI_sfun (S : set T) (mS : measurable S) : sfun T R :=
  @SFun.mk _ _ (fun x => g x * (x \in S)%:R) (preimgI_cdom S) _ _ _.
Next Obligation.
move=> S _; rewrite /preimgI_cdom; set s := seq.filter _ _ => /=.
have [_|] := ifPn; first by rewrite filter_uniq // SFun.uniq_cdom.
rewrite negb_or => /andP[s0 _].
by rewrite rcons_uniq s0 /= filter_uniq // SFun.uniq_cdom.
Qed.
Next Obligation.
move=> S _; rewrite /preimgI_cdom; set s := seq.filter _ _ => /=.
rewrite predeqE => x; split => [[t _ <-{x}]|] /=.
  have [tS|tS] /= := boolP (t \in S).
    rewrite mulr1; have [_|_] := ifPn.
      rewrite mem_filter SFunfcdom andbT; apply/set0P.
      by exists t => //; split => //=; rewrite -in_setE.
    rewrite mem_rcons inE; apply/orP; right.
    rewrite mem_filter SFunfcdom andbT; apply/set0P.
    by exists t; split => //=; rewrite -in_setE.
  rewrite mulr0; have [/orP[//|/eqP]|] := ifPn.
    by rewrite predeqE => /(_ t)[_]/(_ Logic.I); rewrite -in_setE (negbTE tS).
  by rewrite negb_or => /andP[s0 ST]; rewrite mem_rcons inE eqxx.
have [_|] := ifPn.
  rewrite mem_filter => /andP[/set0P[t [/= gtx]]].
  by rewrite -in_setE => St xg; exists t => //; rewrite St mulr1.
rewrite negb_or => /andP[s0 ST]; rewrite mem_rcons inE => /orP[/eqP ->{x}|].
  suff [t St] : exists t, t \notin S by exists t => //; rewrite (negbTE St) mulr0.
  by move/setTP : ST => [t St]; exists t; apply/negP; rewrite in_setE.
rewrite mem_filter => /andP[+ _] => /set0P[t [gtx]].
by rewrite -in_setE => tS;exists t => //; rewrite tS mulr1.
Qed.
Next Obligation.
move=> S mS; rewrite /preimgI_cdom; set s := seq.filter _ _ => /=.
have sg : (size s <= ssize g)%N by rewrite size_filter count_size.
have [/orP[s0 k|/eqP ST k]|] := ifPn.
  - have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.cdom g)`_k'.
      have : s`_k \in SFun.cdom g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite gSxE.
    apply: measurableU.
      apply: measurableI => //.
      by have := @SFun.mpi _ _ g k'; rewrite /SFun.pi /= -kk'.
    apply: measurableI; first exact: measurableC.
    have [sk0|sk0] := pselect (s`_k = 0).
      by rewrite (_ : (fun _ => _) = setT) ?predeqE//; exact: measurableT.
    by rewrite (_ : (fun _ => _) = set0) ?predeqE//; exact: measurable0.
  - (*copipe*) have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.cdom g)`_k'.
      have : s`_k \in SFun.cdom g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite [X in _ X](_ : _ = [set t | [set s`_k] (g t)]).
      by have := @SFun.mpi _ _ g k'; rewrite /SFun.pi /= -kk'.
    rewrite predeqE => t.
    by rewrite /set1 mksetE (_ : _ \in _) ?mulr1// in_setE ST.
rewrite negb_or => /andP[s0 ST] k.
rewrite gSxE; have [ks|ks] := boolP (k == size s :> nat).
  rewrite nth_rcons (eqP ks) ltnn eqxx.
  apply: measurableU.
    have [/eqP H|/set0P[t [St g0t]]] := boolP ((S `&` g @^-1` [set 0]) == set0).
      by rewrite H; exact: measurable0.
    suff : 0 \in s by rewrite (negbTE s0).
    rewrite mem_filter; apply/andP; split; first by apply/set0P; exists t.
    by rewrite -g0t SFunfcdom.
  apply: measurableI; first exact: measurableC.
  by rewrite (_ : (fun _ => _) = setT) ?predeqE //; exact: measurableT.
have [k' kk'] : exists k' : 'I_(ssize g), (rcons s 0)`_k = (SFun.cdom g)`_k'.
  have @k' : 'I_(size s).
    apply: (@Ordinal _ k).
    by rewrite ltn_neqAle ks /= -ltnS -(size_rcons s 0) ltn_ord.
  have : s`_k' \in s by apply/(nthP 0); exists k'.
  rewrite mem_filter => /andP[_].
  move=> /(nthP 0)[i ig] gisk'; exists (Ordinal ig) => //=.
  by rewrite nth_rcons ifT // ltn_neqAle ks /= -ltnS -(size_rcons s 0) ltn_ord.
apply: measurableU.
  apply: measurableI => //.
  by have := @SFun.mpi _ _ g k'; rewrite /SFun.pi /= -kk'.
apply: measurableI; first exact: measurableC.
have [sk0|sk0] := pselect ((rcons s 0)`_k = 0).
  by rewrite (_ : (fun _ => _) = setT) ?predeqE//; exact: measurableT.
by rewrite (_ : (fun _ => _) = set0) ?predeqE//; exact: measurable0.
Qed.

End preimage_setI.

Section sintegral_nondecreasing_limit_lemma.
Variables (T : measurableType) (point : T).
Variables (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~ x).
Variable (f : nnsfun T R).
Hypothesis gf : forall x, D x -> cvg (g^~ x : _ -> R^o) ->
  f x <= lim (g^~ x : _ -> R^o).

Local Definition fleg c : (set T)^nat :=
  fun n => [set x | c * (f x) <= g n x] `&` D.

Local Lemma nd_fleg c : {homo fleg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; rewrite /fleg; apply/subsetPset => x [/[swap] Dx] /= cfg.
by split => //=; move: cfg => /le_trans; apply; exact: nd_g.
Qed.

Local Lemma le_ffleg c : {homo
  (fun p x => f x * (x \in fleg c p)%:R) : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; apply/asboolP => t; rewrite ler_pmul // ler_nat.
have [/=|//] := boolP (t \in fleg c n); rewrite in_setE => cnt.
by have := nd_fleg c nm => /subsetPset/(_ _ cnt); rewrite -in_setE => ->.
Qed.

Local Lemma bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = D.
Proof.
move=> c1; rewrite predeqE => x; split=> [|Dx].
 by move=> -[n _]; rewrite /fleg /= => -[].
have := NNSFun.ge0 f x; rewrite le_eqVlt => /orP[/eqP gx0|gx0].
  exists O => //; rewrite /fleg /=; split => //=.
  by rewrite -gx0 mulr0 NNSFun.ge0.
have [cf|df] := pselect (cvg (g^~ x : _ -> R^o)).
  have cfg : lim (g^~ x : _ -> R^o) > c * f x.
    by rewrite (lt_le_trans _ (gf Dx cf)) // gtr_pmull.
  suff [n cfgn] : exists n, g n x >= c * f x by exists n.
  move/(@lt_lim _ _ _ (nd_g Dx) cf) : cfg => [n _ nf].
  by exists n; apply: nf => /=.
have /cvgPpinfty/(_ (c * f x))[n _ ncfgn]:= nondecreasing_dvg_lt (nd_g Dx) df.
by exists n => //; rewrite /fleg /=; split => //=; apply: ncfgn => /=.
Qed.

Local Lemma measurable_fgeg c n : measurable (fleg c n).
Proof.
rewrite /fleg; apply: measurableI => //.
rewrite [X in _ X](_ : _ = \big[setU/set0]_(y <- SFun.cdom f)
    \big[setU/set0]_(x <- SFun.cdom (g n) | c * y <= x)
      ((f @^-1` [set y]) `&` (g n @^-1` [set x]))); last first.
  rewrite predeqE => t; split.
    rewrite /= => fgcn; rewrite -bigcup_set.
    exists (f t); first exact: SFunfcdom.
    rewrite -bigcup_set_cond; exists (g n t) => //.
    by apply/andP; split => //; exact: SFunfcdom.
  rewrite -bigcup_set => -[r /= rf].
  by rewrite /fleg -bigcup_set_cond => -[? /andP[? ?]] [/= -> ->].
apply bigsetU_measurable => r _.
apply bigsetU_measurable => r' crr'.
by apply: measurableI; exact: measurable_preimage_set1.
Qed.

(* lemma 1.6 *)
Lemma nd_sintegral_lim_lemma : (sintegral mu D f <= lim (sintegral mu D \o g))%E.
Proof.
suff ? : forall c, 0 < c < 1 ->
    (c%:E * sintegral mu D f <= lim (sintegral mu D \o g))%E.
  by apply/lee_mul01Pr => //; apply: sintegral_ge0.
move=> c /andP[c0 c1].
pose g1' n := preimgI_sfun f (measurable_fgeg c n).
have g1'_ge0 n x : 0 <= g1' n x by rewrite /g1' mulr_ge0.
pose g1 n := NNSFun.mk (g1'_ge0 n).
have cg1leg n x : D x -> c * g1 n x <= g n x.
  move=> Dx; rewrite /g1 /= /fleg /=; have [|] := boolP (x \in _).
    by rewrite in_setE => -[/=]; rewrite mulr1.
  by rewrite 2!mulr0 NNSFun.ge0.
have cg1_ge0 n x : 0 <= (sfun_scale point c (g1 n)) x.
  by rewrite mulr_ge0 // ltW.
have {cg1leg}cg1g n : (c%:E * sintegral mu D (g1 n) <= sintegral mu D (g n))%E.
  rewrite -(sintegralK point mu c mD (g1 n)).
  apply: (@le_sintegral _ _ _ _ _ _ (NNSFun.mk (cg1_ge0 n))) => //=.
  by move=> x Dx; rewrite /fleg /= cg1leg.
suff {cg1g}<- : lim (fun n => sintegral mu D (g1 n)) = sintegral mu D f.
  have is_cvg_g1 : cvg (fun n => sintegral mu D (g1 n)).
    apply: is_cvg_sintegral => //= x Dx m n mn.
    by have /lefP/(_ x) := le_ffleg c mn.
  rewrite -ereal_limZ // lee_lim//.
  - exact: is_cvg_ereal_cvgZ.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu D (g1 n)) --> sintegral mu D f by apply/cvg_lim.
rewrite [X in X --> _](_ : _ = (fun n => (\sum_(k < ssize f) ((SFun.cdom f)`_k)%:E *
    mu (f @^-1` [set (SFun.cdom f)`_k] `&` fleg c n `&` D))%E)); last first.
  rewrite funeqE => n; rewrite sintegralE.
  transitivity (\sum_(x <- SFun.cdom f) x%:E * mu (g1 n @^-1` [set x] `&` D))%E.
    rewrite (_ : SFun.cdom (g1 n) = preimgI_cdom f (fleg c n)) // /preimgI_cdom /=.
    case: ifPn=> [/orP[|/eqP cnT]|_].
    - rewrite mem_filter /= => /andP[].
      rewrite /set1 /mkset /= => /set0P[t [ft0 cnt]] f0.
      rewrite big_filter big_mkcond; apply eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0// predeqE => x; split => //=.
      move=> [/[swap] Dx].
      have [xcn|xcn] := boolP (x \in _).
        by rewrite mulr1 => gxr; rewrite -I0; split => //; rewrite -in_setE.
      rewrite mulr0 => r0.
      by move: I0; rewrite predeqE => /(_ t)[+ _]; apply; rewrite -r0.
    - rewrite big_filter big_mkcond; apply eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x; split => //=.
      move=> [/[swap] Dx]; rewrite /set1 /mkset cnT; have [xT|] := boolP (x \in _).
        by rewrite mulr1 => gxr; rewrite -I0 cnT.
      by rewrite notin_setE => /(_ Logic.I).
    - rewrite -cats1 big_cat /= big_cons big_nil mul0e !adde0.
      rewrite big_filter big_mkcond; apply eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      have [/eqP ->|r0] := boolP (r == 0); first by rewrite mul0e.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x; split => //=.
      move=> [/[swap] Dx]; rewrite /set1 /mkset; have [xT|_ ] := boolP (x \in _).
        by rewrite mulr1 => gxr; rewrite -I0; split => //; rewrite -in_setE.
      by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  rewrite big_tnth; apply eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0) //=.
  have [/eqP fi0|fi0] := boolP ((SFun.cdom f)`_i == 0); first by rewrite fi0 // 2!mul0e.
  congr (_%:E * mu _)%E; rewrite predeqE => x; split => [|[]] /=.
  - rewrite /mkset /set1 /mkset /= => -[/[swap] Dx].
    have [xcn|_] := boolP (_ \in fleg _ _).
      by rewrite mulr1 => <-; split => //; split=> //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE fi0).
  - rewrite /set1 /mkset => -[fxi]; rewrite -in_setE => cnx Dx; split => //.
    by rewrite fxi cnx mulr1.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(x <- SFun.cdom f) x%:E *
    mu (f @^-1` [set x] `&` fleg c n `&` D))%E); last first.
  rewrite funeqE => n; rewrite [in RHS]big_tnth /=; apply/eq_bigr => i _.
  rewrite [in LHS](set_nth_default 0) //=; congr (_%:E * mu (_ `&` _ `&` _))%E.
    exact: set_nth_default.
  rewrite predeqE => t /=; rewrite /set1 mksetE -propeqE.
  by congr (_ = _); exact: set_nth_default.
rewrite sintegralE big_seq.
under [in X in X --> _]eq_fun do rewrite big_seq.
have measurable_ffleg k i : measurable (f @^-1` [set k] `&` fleg c i `&` D).
  apply: measurableI => //; apply: measurableI;
    [exact: measurable_preimage_set1|exact: measurable_fgeg].
apply: ereal_lim_sum => [r n /SFuncdom_ge0 r0|r rf].
  by rewrite mule_ge0// measure_ge0.
apply: ereal_cvgZ.
rewrite [X in _ --> X](_ : _ = mu (\bigcup_n (f @^-1` [set r] `&` fleg c n `&` D))); last first.
  by rewrite -bigcup_distrl -bigcup_distrr bigcup_fleg// -setIA setIid.
apply: cvg_mu_inc => //; first exact: measurable_bigcup.
move=> n m nm; apply/subsetPset; apply: setSI; apply: setIS.
by move/(nd_fleg c) : nm => /subsetPset.
Grab Existential Variables. all: end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (point : T).
Variables (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~ x).
Variable (f : nnsfun T R).
Hypothesis gf : forall x, D x -> (g^~ x : _ -> R^o) --> (f x : R^o).
Let limg : forall x, D x -> lim (g^~ x : _ -> R^o) = (f x : R^o).
Proof. by move=> x Dx; apply/cvg_lim => //; exact: gf. Qed.

Lemma nd_sintegral_lim : sintegral mu D f = lim (sintegral mu D \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x Dx; rewrite -limg.
have : nondecreasing_seq (sintegral mu D \o g).
  by move=> m n mn; apply (le_sintegral point) => // x Dx; exact/nd_g.
move=> /nondecreasing_seq_ereal_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=.
apply le_sintegral => // x Dx.
rewrite -limg // (nondecreasing_cvg_le (nd_g Dx)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Lemma ger0_le0_eq0 (R : numDomainType) (x : R) : (0 <= x) -> (x <= 0) = (x == 0).
Proof. by move=> x0; rewrite eq_le x0 andbT. Qed.

Lemma gee0_le0_eq0 (R : realDomainType) (x : \bar R) : ((0 <= x) -> (x <= 0) = (x == 0))%E.
Proof. by move=> x0; rewrite eq_le x0 andbT. Qed.

Section integral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).

(* expect a nonnegative measurable function f *)
Definition nnintegral (D : set T) (f : T -> \bar R) :=
  ereal_sup [set sintegral mu D g | g in
    [set g : nnsfun T R | (forall x, D x -> (g x)%:E <= f x)%E] ].

Lemma nnintegral_ge0 (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> (0 <= nnintegral D f)%E.
Proof.
move=> f0; apply: ereal_sup_ub => /=.
exists (@nnsfun_cst T point R (Nonneg.NngNum _ (ler0n _ O))).
  by move=> x /= Dx; exact: f0.
rewrite /sintegral /= big1 //= => k _.
by rewrite (_ : _%:E = 0%E) ?mul0e//; move: k => [[|]].
Qed.

Lemma eq_nnintegral (D : set T) (g f : T -> \bar R) :
  (forall x, D x -> f x = g x) -> nnintegral D f = nnintegral D g.
Proof.
move=> fg; rewrite /nnintegral; congr ereal_sup; rewrite eqEsubset; split.
  by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite -fg// hf.
by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite fg// hf.
Qed.
Arguments eq_nnintegral {D} _ {f} _.

Lemma nnintegral0 (D : set T) : nnintegral D (fun=> 0%E) = 0%E.
Proof.
pose cst0 : nnsfun T R := nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub => /=; exists cst0 => //=.
  by rewrite sintegralE /= big_cons big_nil adde0 mul0e.
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, D x -> f x = 0.
  by move=> y ?; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin NNSFun.ge0.
rewrite /sintegral big1 //= => i _.
(* NB: improve? *)
have [/eqP ->|/set0P[t [fit Dt]]] := boolP (SFun.pi f i `&` D == set0).
  by rewrite measure0 mule0.
by rewrite (pi_nth fit) f0 // mul0e.
Qed.

Definition integrable (D : set T) (f : T -> \bar R) :=
  (nnintegral D (fun x => norme (f x)) < +oo)%E.

(* expect the function f to be mu integrable *)
Definition integral (D : set T) (f : T -> \bar R) :=
  (nnintegral D (f ^\+) - nnintegral D (f ^\-))%E.

Lemma ge0_integralE (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E ->
  integral D f = nnintegral D f.
Proof.
move=> f0; rewrite /integral; rewrite (eq_nnintegral f (ge0_funenngE f0)).
by rewrite (eq_nnintegral (cst 0%E) (ge0_funennpE f0)) nnintegral0 sube0.
Qed.

End integral.

(* TODO: PR? *)
Lemma EFin_lim (R : realType) (f : nat -> R^o) : cvg f -> lim (@EFin _ \o f)%E = (lim f)%:E.
Proof.
move=> cf; apply: cvg_lim => //; move/cvg_ex : cf => [l fl].
by apply (@cvg_comp _ _ _ _ (@EFin _) _ _ _ fl); rewrite (cvg_lim _ fl).
Qed.

(* TODO: PR? *)
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

(* TODO: PR? *)
Lemma nondecreasing_seqD (T : Type) (R : numDomainType) (D : set T) (f g : (T -> R)^nat) :
  (forall x, D x -> nondecreasing_seq (f^~x)) ->
  (forall x, D x -> nondecreasing_seq (g^~x)) ->
  (forall x, D x -> nondecreasing_seq ((f \+ g)^~x)).
Proof.
move=> ndf ndg t Dt m n mn.
by apply: ler_add; [exact/ndf | exact/ndg].
Qed.

Section pointwise_convergence.
Variables (T : Type) (R : realFieldType).
Implicit Types (g : (T -> R^o)^nat) (f : T -> \bar R).

Definition point_cvg (D : set T) g f := forall x, D x ->
  if pselect (cvg (g^~ x)) then @EFin _ \o g^~ x --> f x
  else f x = +oo%E.

Lemma is_point_cvgZr D g f k : 0 <= k ->
  point_cvg D g f -> point_cvg D (k \*: g) (fun x => k%:E * f x)%E.
Proof.
rewrite le_eqVlt => /orP[/eqP <-{k} _ t Dt|k0 cf t Dt].
  rewrite (_ : (fun _ => _) = cst 0); last first.
    by rewrite funeqE => x /=; rewrite scale0r.
  case: pselect => [/= _|/= h]; last by exfalso; apply h; apply: is_cvg_cst.
  by rewrite mul0e [X in X --> _](_ : _ = cst 0%E) //; exact: cvg_cst.
have := cf t Dt; case: pselect => /= [cft|cft ftoo].
  case: pselect => [/= cgt /(@ereal_cvgZ _ _ _ k)|cgt]; first exact: cvg_trans.
  by exfalso; apply: cgt; apply: is_cvgZr.
case: pselect => h /=; last by rewrite ftoo mulr_pinfty gtr0_sg // mul1e.
by exfalso; apply: cft; move: h; rewrite is_cvgZrE // gt_eqF.
Qed.
End pointwise_convergence.

Section pointwise_convergence_realType.
Variables (T : Type) (R : realType).
Implicit Types (g : (T -> R^o)^nat) (f : T -> \bar R).

Lemma point_cvgD (D : set T) g1 g2 f1 f2 :
  (forall x, D x -> 0 <= f1 x)%E -> (forall x, D x -> 0 <= f2 x)%E ->
  (forall x, D x -> nondecreasing_seq (g1^~x)) ->
  (forall x, D x -> nondecreasing_seq (g2^~x)) ->
  point_cvg D g1 f1 -> point_cvg D g2 f2 -> point_cvg D (g1 \+ g2) (f1 \+ f2)%E.
Proof.
move=> f10 f20 f_nd g_nd cf cg t Dt; have := cf t Dt.
case: pselect => [cg1 /= gf1|cg1 /= ftoo].
  have := cg t; case: pselect => [cg2 /= gf2|g_dvg /= gtoo].
    have : cvg (g1^~ t \+ g2^~ t) by exact: is_cvgD.
    case: pselect => //= _ _.
    rewrite [X in X --> _](_ : _ = (@EFin _ \o g1^~ t) \+ (@EFin _ \o g2^~ t))%E//.
    apply: ereal_cvgD => //=; last exact: gf2.
    by apply: ge0_adde_def => /=; rewrite inE ?f10// f20.
  case: pselect => [cg12|_]/=.
    by exfalso; apply: g_dvg; move: cg12; rewrite is_cvgDrE.
  by rewrite gtoo// addeC addooe// gt_eqF// (lt_le_trans _ (f10 _ Dt))// lte_ninfty.
case: pselect => [cg12 /=|/= _]; last first.
  by rewrite ftoo// addooe // gt_eqF// (lt_le_trans _ (f20 _ Dt))// lte_ninfty.
have [cg2|cg2] := pselect (cvg (g2^~ t)).
  by exfalso; apply: cg1; move: cg12; rewrite is_cvgDlE.
exfalso;  move/cvg_ex : (cg12) => [l g12l].
have /cvgPpinfty/(_ (l + 1))[n _ nl] := nondecreasing_dvg_lt (f_nd _ Dt) cg1.
have /cvgPpinfty/(_ 0)[m _ ml] := nondecreasing_dvg_lt (g_nd _ Dt) cg2.
have := nondecreasing_cvg_le (nondecreasing_seqD f_nd g_nd Dt) cg12 (maxn n m).
rewrite (cvg_lim _ g12l) //; apply/negP.
rewrite -ltNge (@lt_le_trans _ _ (l + 1 + 0))//; first by rewrite addr0 ltr_addl.
by rewrite ler_add //; [apply: nl => /=; rewrite leq_maxl|
                        apply: ml => /=; rewrite leq_maxr].
Qed.

End pointwise_convergence_realType.

(* NB: see PR 371 *)
Section set_of_itv.
Variable (R : numDomainType).
Implicit Type i j : interval R.
Implicit Type x y : R.
Implicit Type a : itv_bound R.

Definition set_of_itv i : set R := [set x | x \in i].

Lemma set_of_itv_mem i x : set_of_itv i x <-> x \in i.
Proof. by move: i => [[[]i1|[]] [[]i2|[]]]. Qed.

End set_of_itv.
(* /NB: see PR 371 *)

Section nondecreasing_integral_limit.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).

(* see PR 371 *)
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
Parameter measurable_Rbar_c_infty : forall (y : \bar R), measurable [set x | (y <= x)%E].

(* /see PR 371 *)

Hypothesis f0 : forall x, D x -> (0 <= f x)%E.
Hypothesis mf : measurable_fun D f.
Variable (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Hypothesis gf : point_cvg D g f.

Lemma nd_ge0_integral_lim : integral mu D f = lim (sintegral mu D \o g).
Proof.
rewrite ge0_integralE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x Dx.
  have := gf Dx; case: pselect => [cg gfx|cg ->] /=; last first.
    by case: (x \in D); rewrite ?(mulr0,mule0,mulr1,mule1)// lee_pinfty.
  have <- : lim (@EFin _ \o (g^~ x)) = f x by exact/cvg_lim.
  have : (@EFin _ \o g^~ x) --> ereal_sup [set of @EFin _ \o g^~ x].
    apply: nondecreasing_seq_ereal_cvg => p q pq /=; rewrite lee_fin.
    exact/nd_g.
  by move/cvg_lim => -> //; apply ereal_sup_ub => /=; exists n.
have := lee_pinfty (nnintegral mu D f); rewrite le_eqVlt => /orP[/eqP mufoo|]; last first.
  move mufr : (nnintegral mu D f) => r.
  move: r mufr => [r mufr _|//|mufr]; last first.
    by move: (nnintegral_ge0 point mu f0); rewrite mufr.
  rewrite -mufr.
  move/ub_ereal_sup_adherent : mufr; rewrite -/(integral _ _) => h.
  apply: lee_adde => e.
  have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite lte_subl_addr => fGe.
  have : forall x, D x -> cvg (g^~ x : _ -> R^o) -> (G x) <= lim (g^~ x : _ -> R^o).
    move=> x Dx cg; rewrite -lee_fin -EFin_lim //=.
    have := gf Dx; case: pselect => // {}cg /= /cvg_lim gxfx.
    by rewrite (le_trans (Gf _ Dx)) // gxfx.
  move/(@nd_sintegral_lim_lemma _ point _ mu _ mD _ nd_g).
  by move/(lee_add2r e%:num%:E)/(le_trans (ltW fGe)).
suff : lim (sintegral mu D \o g) = +oo%E by move=> ->; rewrite mufoo.
apply/eq_oo => A A0.
have [G [Gf AG]] : exists h : nnsfun T R, (forall x, D x -> (h x)%:E <= f x)%E /\
                                     (A%:E <= sintegral mu D h)%E.
  move: (mufoo).
  rewrite /integral => /eq_oo.
  have A20 : 0 < A + A by rewrite addr_gt0.
  move/(_ _ A20) => A2.
  have {} : (A%:E < ereal_sup [set sintegral mu D g0 | g0 in
       [set h : nnsfun T R | (forall x, D x -> (h x)%:E <= f x)]])%E.
    by rewrite (lt_le_trans _ A2) // lte_fin ltr_addr.
  move/ereal_sup_gt => [x [/= [G Gf Gx Ax]]].
  by exists G; split => //; rewrite (le_trans (ltW Ax)) // Gx.
have : forall x, D x -> cvg (g^~ x : _ -> R^o) -> (G x) <= lim (g^~ x : _ -> R^o).
 (* TODO: same code above in this script *)
  move=> x Dx cg.
  rewrite -lee_fin -EFin_lim //.
  have := gf Dx; case: pselect => // {}cg /= /cvg_lim gxfx.
  by rewrite (le_trans (Gf _ Dx)) // gxfx.
move/(@nd_sintegral_lim_lemma _ point _ mu _ mD _ nd_g) => Gg.
by rewrite (le_trans AG).
Grab Existential Variables. all: end_near. Qed.

End nondecreasing_integral_limit.

(* TODO: PR? *)
Lemma preimage_comp T1 T2 rT (g : T1 -> rT) (f : T2 -> rT) (C : set T1) :
  f @^-1` [set g x | x in C] = [set x | f x \in g @` C].
Proof.
rewrite predeqE => t; split => /=.
  by move=> -[r Cr <-]; rewrite inE;  exists r.
by rewrite inE => -[r Cr <-]; exists r.
Qed.

(* NB: also in PR 317 *)
Lemma measurable_fun_c_infty (R : realType) (T : measurableType) (D : set T) (f : T -> \bar R)
    (y : \bar R) :
  measurable D ->
  measurable_fun D f -> measurable ([set x | (y <= f x)%E] `&` D).
Proof.
move=> mD mf.
rewrite (_ : [set x | (y <= f x)%E] = f @^-1` [set x | (y <= x)%E]) //.
exact/mf/measurable_Rbar_c_infty.
Qed.
(* /NB: also in PR 317 *)

(* TODO: PR in progress *)
Lemma floor1 (R : realType) : floor (1 : R) = 1.
Proof. by rewrite /floor Rfloor1 (_ : 1 = 1%:R) // Rtointn. Qed.

Lemma floor_neq0 (R : realType) (r : R) : 1 <= r -> floor r != 0.
Proof.
by move/le_floor => r1; rewrite gt_eqF // (lt_le_trans _ r1) // floor1.
Qed.
(* /PR in progress *)

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

Section dyadic_interval.
Variable R : realType.

Definition dyadic_itv n k : interval R := `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[.

Local Notation I := dyadic_itv.

Lemma dyadic_itv_subU n k : set_of_itv (I n k) `<=`
  set_of_itv (I n.+1 k.*2) `|` set_of_itv (I n.+1 k.*2.+1).
Proof.
move=> r /set_of_itv_mem; rewrite in_itv /= => /andP[Ir rI].
have [rk|rk] := ltP r (k.*2.+1%:R * (2%:R ^- n.+1)); [left|right].
- apply/set_of_itv_mem; rewrite in_itv /= rk andbT (le_trans _ Ir)// -muln2.
  rewrite natrM exprS invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2).
  by rewrite divrr ?unitfE// mulr1.
- apply/set_of_itv_mem; rewrite in_itv /= rk /= (lt_le_trans rI)// -doubleS.
  rewrite -muln2 natrM exprS invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2).
  by rewrite divrr ?unitfE// mulr1.
Qed.

Lemma bigsetU_dyadic_itv n : set_of_itv `[n%:R, n.+1%:R[ =
  \big[setU/set0]_(n * 2 ^ n.+1 <= k < n.+1 * 2 ^ n.+1) set_of_itv (I n.+1 k).
Proof.
rewrite predeqE => r; split => [/set_of_itv_mem|].
- rewrite in_itv /= => /andP[nr rn1]; rewrite -bigcup_set /=.
  exists `|floor (r * 2 ^+ n.+1)|%N.
    rewrite /= mem_index_iota; apply/andP; split.
      rewrite -ltez_nat gez0_abs ?floor_ge0; last first.
        by rewrite mulr_ge0 -?natrX ?ler0n// (le_trans _ nr).
      apply: (@le_trans _ _ (floor (n * 2 ^ n.+1)%:R)); last first.
        by apply: le_floor; rewrite natrM natrX ler_pmul2r// -natrX ltr0n expn_gt0.
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

Lemma dyadic_itv_image n T (f : T -> \bar R) x : (n%:R%:E <= f x < n.+1%:R%:E)%E ->
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
rewrite (bigsetU_dyadic_itv n) inE /= => -[r].
rewrite -bigcup_set => -[k /=].
rewrite mem_index_iota => ? Ir rfx.
exists k; split; first by rewrite !(mulnC (2 ^ n.+1)%N).
by rewrite !inE /=; exists r.
Qed.

End dyadic_interval.

Section approximation.
Variables (T : measurableType) (point : T) (R : realType).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Local Notation I := (@dyadic_itv R).

Let A n k := (if (k < n * 2 ^ n)%N then
  [set x | f x \in @EFin _ @` set_of_itv (I n k)] else set0) `&` D.

Let B n := [set x | n%:R%:E <= f x ]%E `&` D.

Definition approx_fun : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * (x \in A n k)%:R
  + n%:R * (x \in B n)%:R.

(* technical properties of the sets A and B *)
Local Lemma mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]; last by rewrite set0I; exact: measurable0.
by rewrite -preimage_comp; exact/mf/measurable_EFin/measurable_itv.
Qed.

Local Lemma trivIsetA n : trivIset setT (A n).
Proof.
rewrite /A.
under [in X in trivIset _ X]eq_fun do rewrite setIC.
apply/trivIset_setI/trivIsetP => i j _ _.
wlog : i j / (i < j)%N.
  move=> h; rewrite neq_lt => /orP[ij|ji].
    by apply: h => //; rewrite lt_eqF.
  by rewrite setIC; apply h => //; rewrite lt_eqF.
move=> ij _.
rewrite /A; case: ifPn => /= ni; last by rewrite set0I.
case: ifPn => /= nj; last by rewrite setI0.
rewrite predeqE => t; split => // -[/=].
rewrite inE => -[r /set_of_itv_mem]; rewrite in_itv /= => /andP[r1 r2] rft.
rewrite inE => -[s /set_of_itv_mem]; rewrite in_itv /= => /andP[s1 s2].
rewrite -rft => -[sr]; rewrite {}sr {s} in s1 s2.
have := le_lt_trans s1 r2.
by rewrite ltr_pmul2r ?invr_gt0 ?exprn_gt0// ltr_nat ltnS leqNgt ij.
Qed.

Local Lemma f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  x \in A n i = false.
Proof.
move=> fx0 i0; apply/negbTE; rewrite notin_setE /A ltn_ord /=.
move=> -[/[swap] Dx] /=.
rewrite inE /= => -[r] /set_of_itv_mem; rewrite in_itv /= => /andP[r1 r2].
rewrite fx0 => -[r0]; move: r1 r2; rewrite {}r0 {r} => + r2.
rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
by rewrite mul0r lern0; exact/negP.
Qed.

Local Lemma fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  x \in A n i = false.
Proof.
move=> fxn; apply/negbTE; rewrite /A ltn_ord.
rewrite notin_setE => -[/[swap] Dx] /=; apply/negP.
rewrite notin_setE /= => -[r /set_of_itv_mem].
rewrite in_itv /= => /andP[r1 r2] rfx.
move: fxn; rewrite -rfx lee_fin; apply/negP.
rewrite -ltNge (lt_le_trans r2)// -natrX ler_pdivr_mulr ?ltr0n ?expn_gt0//.
by rewrite -natrM ler_nat (leq_trans (ltn_ord i)).
Qed.

Local Lemma disj_A0 x n (i k : 'I_(n * 2 ^ n)) : i != k ->
  x \in A n k -> (x \in A n i) = false.
Proof.
move=> ik xAn1k; apply/negbTE/negP => xAi.
have /trivIsetP/(_ _ _ Logic.I Logic.I ik)/= := @trivIsetA n.
rewrite predeqE => /(_ x)[+ _].
by rewrite 2!in_setE in xAn1k, xAi; move/(_ (conj xAi xAn1k)).
Qed.
Arguments disj_A0 {x n i} k.

Local Lemma notinD_A0 x n k : ~ D x -> (x \in A n k) = false.
Proof. by move=> Dx; apply/negP; rewrite inE => -[]. Qed.

Local Lemma  mB n : measurable (B n).
Proof. exact: measurable_fun_c_infty. Qed.

Local Lemma foo_B1 x n : D x -> f x = +oo%E -> x \in B n.
Proof.
by move=> Dx fxoo; rewrite /B inE /=; split => //=; rewrite /= fxoo lee_pinfty.
Qed.

Local Lemma f0_B0 x n : f x = 0%:E -> n != 0%N -> (x \in B n) = false.
Proof.
move=> fx0 n0; apply/negP; rewrite in_setE /B /= => -[/[swap] Dx] /=; apply/negP.
by rewrite -ltNge fx0 lte_fin ltr0n lt0n.
Qed.

Local Lemma fgtn_B0 x n : (f x < n%:R%:E)%E -> (x \in B n) = false.
Proof.
move=> fxn; apply/negbTE/negP; rewrite inE /= => -[/[swap] Dx] /=.
by apply/negP; rewrite -ltNge.
Qed.

Local Lemma notinD_B0 x n : ~ D x -> (x \in B n) = false.
Proof. by move=> Dx; apply/negP; rewrite inE => -[]. Qed.

Local Lemma f0_approx_fun0 n x : f x = 0%E -> approx_fun n x = 0.
Proof.
move=> fx0; rewrite /approx_fun; have [/eqP ->|n0] := boolP (n == O).
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0 // mulr0 addr0 big1 // => /= i _.
have [/eqP ->|i0] := boolP (i == O :> nat); first by rewrite mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Local Lemma fpos_approx_fun_neq0 x : D x -> (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx_fun n x != 0.
Proof.
move=> Dx /andP[fx_gt0 fxoo].
have fxE : (real_of_extended (f x))%:E = f x.
  rewrite -EFin_real_of_extended// fin_numE.
  by move: fxoo fx_gt0; case: (f x).
rewrite -fxE lte_fin in fx_gt0.
near=> n.
rewrite /approx_fun; apply/negP; rewrite paddr_eq0; last 2 first.
  - by apply: sumr_ge0 => i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
  - by rewrite mulr_ge0 // ?ler0n.
move/andP.
rewrite psumr_eq0; last first.
  by move=> i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
case => /allP /= An0.
rewrite mulf_eq0 => /orP[|].
  by apply/negP; near: n; exists 1%N => //= m /=; rewrite lt0n pnatr_eq0.
rewrite pnatr_eq0 => /eqP.
have [//|] := boolP (x \in B n).
rewrite notin_setE /B /setI /= => /not_andP[] // /negP.
rewrite -ltNge => fxn _.
have K : (`|floor (real_of_extended (f x) * 2 ^+ n)| < n * 2 ^ n)%N.
  rewrite -ltz_nat gez0_abs; last first.
    by rewrite floor_ge0 mulr_ge0 // -?natrX// ?ler0n// ltW.
  rewrite -(@ltr_int R); rewrite (le_lt_trans (floor_le _)) // PoszM intrM.
  by rewrite -natrX ltr_pmul2r ?ltr0n ?expn_gt0// -lte_fin fxE.
have xAnK : x \in A n (Ordinal K).
  rewrite inE /A; split => //.
  rewrite ifT //= inE /=; exists (real_of_extended (f x)) => //.
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
move=> fxn; rewrite /approx_fun fgtn_B0 // mulr0 addr0.
set lhs := (X in X == 0); have [|] := boolP (lhs == 0); first by left.
rewrite {}/lhs psumr_eq0; last first.
  by move=> i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
move/allPn => [/= k _].
rewrite mulf_eq0 negb_or mulf_eq0 negb_or -andbA => /and3P[k_neq0 _].
rewrite pnatr_eq0 eqb0 negbK => xAnk.
right.
rewrite (bigD1 k) //= xAnk mulr1 big1 ?addr0; last first.
  by move=> i ik; rewrite (disj_A0 k)// mulr0.
exists k; split => //.
  by rewrite lt0n ltn_ord andbT -(@pnatr_eq0 R).
move: xAnk; rewrite inE /A ltn_ord /= inE /= => -[/[swap] Dx].
by rewrite /=; rewrite inE /=.
Qed.

Lemma nd_approx_fun : nondecreasing_seq approx_fun.
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x.
have [Dx|Dx] := pselect (D x); last first.
  rewrite /approx_fun.
  rewrite big1; last by move=> i _; rewrite notinD_A0 // mulr0.
  rewrite notinD_B0// ?mulr0 addr0.
  rewrite big1; last by move=> i _; rewrite notinD_A0 // mulr0.
  by rewrite notinD_B0// ?mulr0 addr0.
have [fxn|fxn] := ltP (f x) n%:R%:E.
  rewrite {2}/approx_fun fgtn_B0 ?mulr0 ?addr0; last first.
    by rewrite (lt_trans fxn) // lte_fin ltr_nat.
  have [/eqP ->|[k [/andP[k0 kn] xAnk -> _]]] := f_ub_approx_fun fxn.
    by apply: sumr_ge0 => i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
  move: (xAnk); rewrite inE {1}/A => -[/[swap] _] /=; rewrite kn /= in_setE => -[r].
  move=> /set_of_itv_mem/dyadic_itv_subU[|] /set_of_itv_mem rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite in_setE; split => //; rewrite k2n /= inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0//.
    rewrite exprS invrM ?unitfE// ?expf_neq0// -muln2 natrM -mulrA (mulrCA 2).
    by rewrite divrr ?mulr1 ?unitfE.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite in_setE /A; split => //; rewrite k2n /= inE /=; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) // mulr0.
    rewrite -[X in X <= _]mulr1 -[X in _ * X <= _](@divrr _ 2%:R) ?unitfE//.
    rewrite mulf_div -natrM muln2 -natrX -natrM -expnSr natrX.
    by rewrite ler_pmul2r ?invr_gt0 ?exprn_gt0// ler_nat.
have /orP[{}fxn|{}fxn] : ((n%:R%:E <= f x < n.+1%:R%:E) || (n.+1%:R%:E <= f x))%E.
  - by move: fxn; case: leP => /= [_ _|_ ->//]; rewrite orbT.
  - have [k [k1 k2]] := dyadic_itv_image fxn.
    have xBn : x \in B n.
      rewrite /B /= inE; split => //.
      by case/andP : fxn.
    rewrite /approx_fun xBn mulr1 big1 ?add0r; last first.
      by move=> /= i _; rewrite fgen_A0 ?mulr0//; case/andP : fxn.
    rewrite fgtn_B0 ?mulr0 ?addr0; last by case/andP : fxn.
    have kn2 : (k < n.+1 * 2 ^ n.+1)%N by case/andP : k1 => _; rewrite mulnC.
    rewrite (bigD1 (Ordinal kn2)) //=.
    have xAn1k : x \in A n.+1 k.
      rewrite in_setE /A.
      have fxE : (real_of_extended (f x))%:E = f x.
        rewrite -EFin_real_of_extended// fin_numE.
        by move: fxn; case: (f x) => // /andP[].
      by rewrite kn2.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i /= ikn2; rewrite (disj_A0 (Ordinal kn2)) // mulr0.
    rewrite -natrX ler_pdivl_mulr ?ltr0n // ?expn_gt0// mulrC -natrM ler_nat.
    by case/andP : k1.
- have xBn : x \in B n.
    rewrite /B /= in_setE /=; split => //.
    by rewrite /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx_fun xBn mulr1.
  have xBn1 : x \in B n.+1.
    by rewrite /B /= in_setE.
  rewrite xBn1 mulr1.
  rewrite big1 ?add0r; last first.
    by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn) // lee_fin ler_nat.
  rewrite big1 ?add0r ?ler_nat // => /= i _.
  by rewrite fgen_A0 // mulr0.
Qed.

Lemma cvg_approx_fun x (f0 : forall x, D x -> (0 <= f x)%E) : D x -> (f x < +oo)%E ->
  (approx_fun^~ x : _ -> R^o) --> (real_of_extended (f x) : R^o).
Proof.
move=> Dx fxoo.
have /EFin_real_of_extended fxE : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
apply/cvg_distP => _/posnumP[e].
rewrite near_map.
have [/eqP fx0|fx0] := boolP (f x == 0%E).
  by near=> n; rewrite f0_approx_fun0 // fx0 /= subrr normr0.
have /(fpos_approx_fun_neq0 Dx) [m _ Hm] : (0 < f x < +oo)%E.
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

Lemma dvg_approx_fun x : D x -> f x = +oo%E -> ~ cvg (approx_fun^~ x : _ -> R^o).
Proof.
move=> Dx fxoo.
have approx_fun_x n : approx_fun n x = n%:R.
  rewrite /approx_fun foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo lee_pinfty.
case/cvg_ex => /= l.
have [l0|l0] := leP 0%R l.
- move=> /cvg_distP/(_ _ ltr01).
  rewrite near_map => -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /=.
  move/(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ger0_norm // (le_trans (ceil_ge _)) //.
  by rewrite -(@gez0_abs (ceil _)) // ceil_ge0.
- move/cvg_distP => /(_ _ ltr01).
  rewrite near_map => -[n _].
  move=> /(_ (`|floor l|.+1 + n)%N) /=.
  move/(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n//.
  rewrite ler0_norm //; last by rewrite ltW.
  rewrite (@le_trans _ _ (- floor l)%:~R) //.
    by rewrite mulrNz ler_oppl opprK floor_le.
  by rewrite -(@lez0_abs (floor _)) // floor_le0 // ltW.
Qed.

Lemma point_cvg_approx_fun (f0 : forall x, D x -> (0 <= f x)%E) :
  point_cvg D approx_fun f.
Proof.
move=> x Dx; have := lee_pinfty (f x); rewrite le_eqVlt => /orP[/eqP|] fxoo.
  by case: pselect => //= H; have := dvg_approx_fun Dx fxoo; tauto.
have h := cvg_approx_fun f0 Dx fxoo.
have /EFin_real_of_extended fxE : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
have approx_fun_f : (fun n => (approx_fun n x)%:E) --> f x.
  by rewrite fxE; move/(@cvg_comp _ _ _ _ (@EFin _)) : h; exact.
case: pselect => // abs; exfalso.
by apply/abs/cvg_ex; exists (real_of_extended (f x)).
Grab Existential Variables. all: end_near. Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition nnsfun_approx : (nnsfun T R)^nat := fun n => nnsfun_add
  (nnsfun_sum point
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => nnsfun_point point (Nonneg.NngNum _ (k2n_ge0 (Ordinal h))) (mA n k)
      | right _ => nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0))
     end) (n * 2 ^ n)%N)
  (nnsfun_point point (Nonneg.NngNum _ (ler0n _ n)) (mB n)).

Lemma nnsfun_approxE n : nnsfun_approx n = approx_fun n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite nnsfun_sumE; congr (_ + _).
apply: eq_bigr => i _; case: Bool.bool_dec => //.
by move/negP; rewrite ltn_ord.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof. by move=> m n mn; rewrite !nnsfun_approxE; exact: nd_approx_fun. Qed.

Lemma point_cvg_nnsfun_approx (f0 : forall t, D t -> (0 <= f t)%E) :
  point_cvg D nnsfun_approx f.
Proof.
by under eq_fun do rewrite nnsfun_approxE; exact: point_cvg_approx_fun.
Qed.

Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : (nnsfun T R)^nat, nondecreasing_seq (g : (T -> R)^nat) /\ point_cvg D g f.
Proof.
by exists nnsfun_approx; split; [exact: nd_nnsfun_approx |
                            exact: point_cvg_nnsfun_approx].
Qed.

End approximation.

(* TODO: move? *)
Section le_approx_fun.
Variables (T : measurableType) (R : realType).
Variables (D : set T) (g : (T -> \bar R)^nat).
Hypothesis g0 : forall n x, D x -> (0 <= g n x)%E.

Lemma le_approx_fun (i k : nat) (x : T) : D x -> (i < k)%N ->
  ((approx_fun D (g i) k x)%:E <= g i x)%E.
Proof.
move=> Dx ik; have [gixoo|] := ltP (g i x) (+oo%E); last first.
  by rewrite lee_pinfty_eq => /eqP ->; rewrite lee_pinfty.
have nd_ag : {homo ((approx_fun D (g i))^~ x) : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; apply/lefP/nd_approx_fun.
have gi0 : forall x, D x -> (0 <= g i x)%E by move=> ?; apply: g0.
have cvg_ag := cvg_approx_fun gi0 Dx gixoo.
have is_cvg_ag : cvg ((approx_fun D (g i))^~ x : _ -> R^o).
  by apply/cvg_ex; eexists; exact: cvg_ag.
have {is_cvg_ag} := nondecreasing_cvg_le nd_ag is_cvg_ag k.
rewrite -lee_fin => /le_trans; apply.
rewrite (@EFin_real_of_extended _ (g i x)); last first.
  by rewrite fin_numE andbC lt_eqF// gt_eqF// (lt_le_trans _ (g0 i Dx)) ?lte_ninfty.
by move/cvg_lim : cvg_ag => ->.
Qed.
End le_approx_fun.

Section semi_linearity.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, (D x -> 0 <= f1 x)%E.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, (D x -> 0 <= f2 x)%E.
Hypothesis mf2 : measurable_fun D f2.

Lemma ge0_integralK k : 0 <= k ->
  integral mu D (fun x => k%:E * f1 x)%E = (k%:E * integral mu D f1)%E.
Proof.
move=> k0.
have [g [nd_g gf1]] := approximation point mD mf1 f10.
pose kg := fun n => nnsfun_scale point (g n) k0.
rewrite (@nd_ge0_integral_lim _ point _ mu _ mD (fun x => k%:E * f1 x)%E _ kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu D (sfun_scale point k (g n))) //.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu D (g n))%E).
    rewrite ereal_limZ; last first.
      by apply: is_cvg_sintegral => // x Dx m n mn; apply/(lef_at x nd_g).
    rewrite -(nd_ge0_integral_lim point mu mD f10) // => x Dx.
    exact/(lef_at x nd_g).
  by under eq_fun do rewrite (sintegralK point mu k mD).
- by move=> t Dt; rewrite mule_ge0// f10.
- move=> x Dx m n mn.
  by rewrite ler_pmul //; exact/lefP/nd_g.
- exact: is_point_cvgZr.
Qed.

Lemma ge0_integralD : integral mu D (f1 \+ f2)%E = (integral mu D f1 + integral mu D f2)%E.
Proof.
have [g1 [nd_g1 gf1]] := approximation point mD mf1 f10.
have [g2 [nd_g2 gf2]] := approximation point mD mf2 f20.
pose g12 := fun n => nnsfun_add (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ point _ _ _ _ _ _ g12) //; last 3 first.
  - by move=> x Dx; rewrite adde_ge0 => //; [exact: f10|exact: f20].
  - apply: nondecreasing_seqD => // x Dx.
    exact/(lef_at x nd_g1).
    exact/(lef_at x nd_g2).
  - apply: point_cvgD => // x Dx.
    exact/(lef_at x nd_g1).
    exact/(lef_at x nd_g2).
rewrite (_ : _ \o _ = fun n => sintegral mu D (g1 n) + sintegral mu D (g2 n))%E; last first.
  by rewrite funeqE => n /=; rewrite sintegralD.
rewrite (nd_ge0_integral_lim point _ _ _ (fun x _ => lef_at x nd_g1)) //.
rewrite (nd_ge0_integral_lim point _ _ _ (fun x _ => lef_at x nd_g2)) //.
rewrite ereal_limD //.
  by apply: is_cvg_sintegral => // x Dx; apply/(lef_at x nd_g1).
  by apply: is_cvg_sintegral => // x Dx; apply/(lef_at x nd_g2).
rewrite ge0_adde_def => //; rewrite inE; apply: ereal_lim_ge.
by apply: is_cvg_sintegral => // x Dx; apply/(lef_at x nd_g1).
by apply: nearW => n; exact: sintegral_ge0.
by apply: is_cvg_sintegral => // x Dx; apply/(lef_at x nd_g2).
by apply: nearW => n; exact: sintegral_ge0.
Qed.

Lemma ge0_le_integral : (forall x, D x -> (f1 x <= f2 x)%E) -> (integral mu D f1 <= integral mu D f2)%E.
Proof.
move=> f12.
have [g1 [nd_g1 gf1]] := approximation point mD mf1 f10.
rewrite (nd_ge0_integral_lim point _ _ f10 (fun x _ => lef_at x nd_g1) gf1)//.
apply: ereal_lim_le.
  by apply: is_cvg_sintegral => // t Dt; apply/(lef_at t nd_g1).
near=> n; rewrite ge0_integralE//.
apply ereal_sup_ub => /=; exists (g1 n) => // t Dt.
rewrite (le_trans _ (f12 _ Dt)) //.
have := gf1 _ Dt.
case: pselect => [/= cg1 gf1t|/= _ ->]; last by rewrite lee_pinfty.
have := lee_pinfty (f1 t); rewrite le_eqVlt => /orP[/eqP ->|ftoo]; first by rewrite lee_pinfty.
have /EFin_real_of_extended ftE : f1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (f10 Dt))// lte_ninfty.
move: gf1t; rewrite ftE => /ereal_cvg_real[ft_near].
set u_ := (X in X --> _) => u_f1.
have <- : lim (u_ : _ -> R^o) = real_of_extended (f1 t) by apply/cvg_lim.
rewrite lee_fin.
apply: nondecreasing_cvg_le => // a b ab.
by rewrite /u_ /=; exact/lefP/nd_g1.
Grab Existential Variables. all: end_near. Qed.

End semi_linearity.

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

Section monotone_convergence_theorem.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (g : (T -> \bar R)^nat).
Hypothesis mg : forall n, measurable_fun D (g n).
Hypothesis g0 : forall n x, D x -> (0 <= g n x)%E.
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Let f := fun x => lim (g^~ x).

Let is_cvg_g t : D t -> cvg (g^~ t).
Proof.
by move=> Dt; apply: ereal_nondecreasing_is_cvg => m n mn; apply/nd_g.
Qed.

Local Definition g2' n : (T -> R)^nat := approx_fun D (g n).
Local Definition g2 n : (nnsfun T R)^nat := nnsfun_approx point mD (mg n).

Local Definition max_g2' : (T -> R)^nat := fun k t => \big[maxr/0]_(i < k) (g2' i k) t.
Local Definition max_g2 : (nnsfun T R)^nat := fun k => nnsfun_bigmax point (g2^~ k) k.

Local Lemma max_g2E : max_g2 = max_g2' :> (T -> R)^nat.
Proof.
rewrite funeq2E => n t; rewrite nnsfun_bigmaxE; apply eq_bigr => i _.
by rewrite nnsfun_approxE.
Qed.

Local Lemma nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => t; rewrite 2!nnsfun_bigmaxE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 t)) //.
  apply: Bigmax.le_bigmax => i _.
  have [_] := (@nondecreasing_seqP _ _ ((g2 i)^~ t)).
  apply => // a b ab; rewrite !nnsfun_approxE.
  exact/lefP/(nd_approx_fun D (g i) ab).
rewrite (Bigmax.bigmaxD1 ord_max) // le_maxr; apply/orP; right.
rewrite [X in _ <= X](eq_bigl (fun i => nat_of_ord i < n)%N); last first.
  move=> i /=; rewrite neq_lt /= (ltNge n i); apply/orP/idP => [[//|]|]; last by left.
  by rewrite -ltNge => /(leq_trans (ltn_ord i)); rewrite ltnn.
by rewrite (big_ord_narrow (leqnSn n)).
Qed.

Let is_cvg_max_g2 t : cvg (fun k => (max_g2 k t)%:E).
Proof.
by apply: ereal_nondecreasing_is_cvg => m n mn; rewrite lee_fin; apply/lefP/nd_max_g2.
Qed.

Lemma max_g2_g k x : D x -> ((max_g2 k x)%:E <= g k x)%O.
Proof.
move=> Dx; rewrite nnsfun_bigmaxE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x))%E; last first.
  by apply/Bigmax.bigmax_lerP; split => //; apply: g0.
rewrite (@big_morph _ _ (@EFin R) 0%:E maxe) //; last by move=> a b; rewrite maxEFin.
apply Bigmax.le_bigmax => i _.
rewrite nnsfun_approxE /= (le_trans (le_approx_fun _ _ _)) //.
by apply: nd_g => //; exact/ltnW.
Qed.

Lemma point_cvg_max_g2_f : point_cvg D max_g2 f.
Proof.
have max_g2_g t : D t -> (lim (fun n => (max_g2 n t)%:E) <= lim (g^~ t))%E.
  move=> Dt; apply: lee_lim => //.
    exact: is_cvg_g.
  by near=> n; move: t Dt; exact/max_g2_g.
have g2_max_g2 t n : (lim (fun k => (g2 n k t)%:E) <= lim (fun k => (max_g2 k t)%:E))%E.
  apply: lee_lim => //.
    apply: ereal_nondecreasing_is_cvg => a b ab.
    by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx_fun.
  near=> k; rewrite nnsfun_bigmaxE lee_fin.
  have nk : (n < k)%N by near: k; exists n.+1.
  exact: (@Bigmax.bigmax_sup _ _ _ (Ordinal nk)).
move=> t Dt.
case: pselect => [_|abs] /=; last first.
  apply/eqP/negPn/negP => ftoo.
  have [r ftr{ftoo}] : exists r, f t = r%:E.
    move ftr : (f t) => r.
    move: r => [r| |] in ftoo ftr *.
    - by exists r.
    - by rewrite ftr in ftoo.
    - suff : (0 <= f t)%E by rewrite ftr.
      apply: ereal_lim_ge => //; first exact/is_cvg_g.
      by apply: nearW => n; apply g0.
  have /cvgPpinfty/(_ (r + 1))[n _ nrg_] := nondecreasing_dvg_lt (lef_at t nd_max_g2) abs.
  have := max_g2_g t; rewrite -/(f t) ftr => lim_max_g2_r.
  have : ((r + 1)%:E <= lim (fun n => (max_g2 n t)%:E))%E.
    apply: ereal_lim_ge => //; near=> m; rewrite lee_fin.
    by apply: nrg_; near: m; exists n.
  apply/negP; rewrite -ltNge.
  by rewrite (le_lt_trans (lim_max_g2_r Dt)) // lte_fin ltr_addl.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (max_g2_g _ Dt)) // (cvg_lim _ g_l).
rewrite /f.
have := lee_pinfty l; rewrite le_eqVlt => /orP[/eqP ->|loo]; first by rewrite lee_pinfty.
rewrite -(cvg_lim _ g_l) //= ereal_lim_le => //.
  exact/is_cvg_g.
near=> n.
have := lee_pinfty (g n t); rewrite le_eqVlt => /orP[/eqP|] fntoo.
- have h := dvg_approx_fun Dt fntoo.
  have g2oo : lim (fun k => (g2 n k t)%:E) = +oo%E.
    apply/cvg_lim => //; apply/dvg_ereal_cvg.
    rewrite [X in X --> _](_ : _ = (approx_fun D (g n))^~ t); last first.
      by under eq_fun do rewrite nnsfun_approxE.
    apply: nondecreasing_dvg_lt; last exact: h.
    by apply/lef_at; apply/nd_approx_fun.
  suff -> : lim (fun k => (max_g2 k t)%:E) = +oo%E by rewrite lee_pinfty.
  by have := g2_max_g2 t n; rewrite g2oo lee_pinfty_eq => /eqP.
- have := cvg_approx_fun (g0 n) Dt fntoo.
  move=> approx_fun_g_g.
  have := g2_max_g2 t n.
  suff : lim (fun k => (g2 n k t)%:E) = g n t by move=> ->.
  have /cvg_lim <- // : @EFin _ \o (approx_fun D (g n))^~ t --> g n t.
    move/(@cvg_comp _ _ _ _ (@EFin _)) : approx_fun_g_g; apply.
    suff [r ftr] : exists r, g n t = r%:E by rewrite ftr.
    (* copipe *)
    move ftr : (g n t) => r.
    move: r => [r| |] in fntoo ftr *.
    - by exists r.
    - by rewrite ftr in fntoo.
    - by have : (0 <= g n t)%E := g0 n Dt; rewrite ftr.
   have ->// : (fun k => (g2 n k t)%:E) = EFin (R:=R) \o (approx_fun D (g n))^~ t.
  by under eq_fun do rewrite nnsfun_approxE.
Grab Existential Variables. all: end_near. Qed.

Lemma monotone_convergence :
  integral mu D f = lim (fun n => integral mu D (g n)).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => integral mu D (g n)).
    move=> m n mn; apply: ge0_le_integral => //.
     by move=> x Dx; apply g0.
     by move=> x Dx; apply g0.
     by move=> x Dx; apply/nd_g.
  have ub n : (integral mu D (g n) <= integral mu D f)%E.
    apply: ge0_le_integral => //.
    - by move=> x Dx; apply g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      by apply: nearW => k; apply/g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      near=> m.
      have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: ereal_lim_le => //; [exact: ereal_nondecreasing_is_cvg|exact: nearW].
rewrite (@nd_ge0_integral_lim _ point _ mu _ _ _ _ max_g2) //; last 3 first.
  - move=> t Dt; apply: ereal_lim_ge => //; first exact/is_cvg_g.
    by apply: nearW => n; apply: g0.
  - by move=> t Dt m n mn; apply/lefP/nd_max_g2.
  - exact: point_cvg_max_g2_f.
apply: lee_lim.
- apply: is_cvg_sintegral => //.
    by move=> t Dt m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvg => // n m nm; apply ge0_le_integral => //.
  + by move=> *; apply: g0.
  + by move=> *; apply: g0.
  + by move=> *; apply/nd_g.
- apply: nearW => n.
  rewrite ge0_integralE//; last by move=> *; apply: g0.
  by apply: ereal_sup_ub; exists (max_g2 n) => // t; exact: max_g2_g.
Grab Existential Variables. all: end_near. Qed.

End monotone_convergence_theorem.

(* NB: see PR 371 *)
Definition lim_ereal_inf (R : realType) (u_ : (\bar R) ^nat) :=
  lim (fun n => ereal_inf [set u_ k | k in [set p | p >= n]%N]).

Definition lim_ereal_sup (R : realType) (u_ : (\bar R) ^nat) :=
  lim (fun n => ereal_sup [set u_ k | k in [set p | p >= n]%N]).

Lemma measurable_fun_ereal_inf (R : realType) (T : measurableType) (point : T)
  (mu : {measure set T -> \bar R}) (f : (T -> \bar R) ^nat)
  (mf : forall n, measurable_fun setT (f n)) (f0 : forall n x, setT n -> (0 <= f n x)%E)
  (n : nat) :
  measurable_fun setT (fun x => ereal_inf [set f k x | k in [set k | n <= k]%N]).
Admitted.
(* /NB: see PR 371 *)

Section fatou.
Variables (T : measurableType) (point : T) (R : realType).
Variable mu : {measure set T -> \bar R}.
Let D := @setT T.
Let mD : measurable D := measurableT.
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> (0 <= f n x)%E.

Lemma fatou : (integral mu D (fun x => lim_ereal_inf (f^~ x)) <=
  lim_ereal_inf (fun n => integral mu D (f n)))%E.
Proof.
pose g n := fun x => ereal_inf [set f k x | k in [set k | k >= n]%N].
have mg n :=  measurable_fun_ereal_inf point mu mf f0 n.
have g0 n : forall x, D x -> (0 <= g n x)%E.
  by move=> x Dx; apply lb_ereal_inf => _ [m /= nm <-]; exact: f0.
rewrite (monotone_convergence point) //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p np <-].
  by exists p => //; rewrite (leq_trans mn).
apply lee_lim.
- apply/cvg_ex; eexists; apply/nondecreasing_seq_ereal_cvg => a b ab.
  apply: (ge0_le_integral point) => //.
  - exact: g0.
  - exact: g0.
  - move=> x Dx.
    apply: le_ereal_inf => _ [n /= bn <-].
    by exists n => //; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/nondecreasing_seq_ereal_cvg => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N -> (integral mu D (g n) <=
    ereal_inf [set integral mu D (f k) | k in [set p | n <= p]%N])%E.
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply (ge0_le_integral point); [exact: mD|exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lb; exists k.
  exact.
Qed.

End fatou.
