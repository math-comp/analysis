(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets posnum topology normedtype sequences measure.
Require Import nngnum lebesgue_measure.

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
(*       dyadic_itv n k == the interval                                       *)
(*                         `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[             *)
(*       integrable D f == the integral of f w.r.t. D is < +oo                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "f ^\+" (at level 1, format "f ^\+").
Reserved Notation "f ^\-" (at level 1, format "f ^\-").
Reserved Notation "f \|_ D" (at level 10).

(******************************************************************************)
(*                         lemmas waiting to be PRed                          *)
(******************************************************************************)

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
  rewrite big_mkcond; apply: eq_bigr => // i _.
  rewrite /F'; case: eqP => [?|]; last by rewrite ltn_ord.
  by case: ifPn => [Fi0|/negPn/eqP <-]; congr F; exact/val_inj.
move: (@measure_bigcup _ _ (measure_additive_measure m)) => ->; last 2 first.
  - by move=> i; rewrite /F'; case: eqP => // _; exact: measurable0.
  - apply/trivIsetP => i j _ _ ij; rewrite /F'.
    case: eqP => ni; last by rewrite set0I.
    case: eqP => nj; last by rewrite setI0.
    by move/trivIsetP : tF; apply.
rewrite [in RHS](bigID (fun i => F i == set0)) /=.
rewrite [in RHS]big1 ?add0e//; last by move=> ? /eqP ->; rewrite measure0.
rewrite [in RHS]big_mkcond /=; apply: eq_bigr => i _.
rewrite /F'; case: eqP => [?|]; last by rewrite ltn_ord.
rewrite -(measure0 (measure_additive_measure m)).
by case: ifPn => [Fi0|/negPn/eqP <-]; congr (m (F _)); exact/val_inj.
Qed.

Lemma additive_ord_cond n (F : 'I_n -> set T) P :
  (forall i : 'I_n, measurable (F i)) -> trivIset setT F ->
  m (\big[setU/set0]_(i < n | P i) F i) = (\sum_(i < n | P i) m (F i))%E.
Proof.
move=> mF tF; rewrite big_mkcond additive_ord.
- by rewrite [in RHS]big_mkcond /=; apply: eq_bigr => i _; case: ifPn.
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
have [->|/set0Pn[k kP]] := eqVneq P finset.set0.
  by rewrite 2!big_set0 measure0.
rewrite big_tnth /= additive_ord_cond //; first by rewrite [in RHS]big_tnth.
apply/trivIsetP => /= i j _ _ ij; move/trivIsetP : tF; apply => //.
apply: contra ij.
by rewrite 2!(tnth_nth k) nth_uniq // index_enum_uniq.
Qed.

End additive_lemmas.

Lemma setTP (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.

Lemma notin_setE T (A : set T) x : x \notin A = (~ A x) :> Prop.
Proof.
by rewrite propeqE; split => [/asboolP//|]; apply: contra_notN; rewrite in_setE.
Qed.

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

Definition maxe {R : realDomainType} (x y : \bar R) : \bar R := Order.join x y.

Lemma maxEFin (R : realDomainType) (a b : R) : (maxr a b)%:E = maxe a%:E b%:E.
Proof.
rewrite /maxe; have [ab|ba] := leP a b; first by rewrite join_r.
by rewrite join_l // lee_fin ltW.
Qed.

Lemma EFin_lim (R : realType) (f : nat -> R) : cvg f ->
  lim (@EFin _ \o f) = (lim f)%:E.
Proof.
move=> cf; apply: cvg_lim => //.
move/cvg_ex : cf => [l fl].
apply: (@cvg_comp _ _ _ _ (@EFin _) _ _ _ fl); rewrite (cvg_lim _ fl) //.
exact: Rhausdorff.
Qed.

Lemma eq_pinfty (R : realType) (x : \bar R) :
  (forall A, 0 < A -> (A%:E <= x)%E) <-> x = +oo%E.
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
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

Lemma nondecreasing_seqD (T : Type) (R : numDomainType) (D : set T)
    (f g : (T -> R)^nat) :
  (forall x, D x -> nondecreasing_seq (f^~x)) ->
  (forall x, D x -> nondecreasing_seq (g^~x)) ->
  (forall x, D x -> nondecreasing_seq ((f \+ g)^~x)).
Proof.
move=> ndf ndg t Dt m n mn.
by apply: ler_add; [exact/ndf | exact/ndg].
Qed.

Lemma preimage_comp T1 T2 rT (g : T1 -> rT) (f : T2 -> rT) (C : set T1) :
  f @^-1` [set g x | x in C] = [set x | f x \in g @` C].
Proof.
rewrite predeqE => t; split => /=.
  by move=> -[r Cr <-]; rewrite inE;  exists r.
by rewrite /preimage /= inE => -[r Cr <-]; exists r.
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

(******************************************************************************)
(*                        /lemmas waiting to be PRed                          *)
(******************************************************************************)

Section funpos.
Local Open Scope ereal_scope.

Definition funenng T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (f x) 0.
Definition funennp T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (- f x) 0.
End funpos.

Notation "f ^\+" := (funenng f).
Notation "f ^\-" := (funennp f).

Section funpos_lemmas.
Variables (T : Type) (R : realDomainType) (D : set T).
Implicit Types (f : T -> \bar R).
Local Open Scope ereal_scope.

Lemma ge0_funenngE f :
  (forall x, D x -> 0 <= f x) -> forall x, D x -> f^\+ x = f x.
Proof. by move=> f0 x Dx; rewrite /funenng /maxe join_l ?f0. Qed.

Lemma ge0_funennpE f :
  (forall x, D x -> 0 <= f x) -> forall x, D x -> f^\- x = 0.
Proof. by move=> f0 x ?; rewrite /funennp /maxe join_r// lee_oppl oppe0 f0. Qed.

Lemma le0_funenngE f :
  (forall x, D x -> f x <= 0) -> forall x, D x -> f^\+ x = 0.
Proof. by move=> f0 x Dx; rewrite /funenng /maxe join_r ?f0. Qed.

Lemma le0_funennpE f :
  (forall x, D x -> f x <= 0) -> forall x, D x -> f^\- x = - f x.
Proof. by move=> f0 x ?; rewrite /funennp /maxe join_l // lee_oppr oppe0 f0. Qed.

Lemma funennpN f : (fun x : T => - f x)^\- = f^\+.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp oppeK. Qed.

Lemma funenngN f : (fun x : T => - f x)^\+ = f^\-.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp. Qed.

End funpos_lemmas.

Module SFun.
Section sfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f :> T -> R ;
  rng : seq R ;
  uniq_rng : uniq rng ;
  full_rng : f @` setT = [set x | x \in rng] ;
  pi := fun k : 'I_(size rng) => f @^-1` [set rng`_k] ;
  mpi : forall k, measurable (pi k) }.
Definition ssize f := size (rng f).
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

Lemma sfun_img_rng t : f t \in SFun.rng f.
Proof.
have := SFun.full_rng f.
rewrite predeqE => /(_ (f t))[+ _].
by apply; exists t.
Qed.

Lemma trivIset_sfun (A : set 'I_n) : trivIset A pi.
Proof.
apply/trivIsetP => /=; rewrite -/n => i j _ _ ij.
suff ij0 : [set (SFun.rng f)`_i] `&` [set (SFun.rng f)`_j] = set0.
  by rewrite /pi /SFun.pi -preimage_setI ij0 preimage_set0.
apply/eqP/negPn/negP => /set0P[r []]; rewrite /set1 /= => ->{r} /eqP.
by rewrite nth_uniq => //; [exact/negP | exact: SFun.uniq_rng].
Qed.

Lemma bigcup_sfun : \big[setU/set0]_(i < n) pi i = setT.
Proof.
rewrite predeqE => t; split => // _; rewrite -bigcup_set -preimage_bigcup.
have /(nthP 0)[i ni fit] := sfun_img_rng t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

Lemma measurable_preimage_set1 (r : R) : measurable (f @^-1` [set r]).
Proof.
have [[k fkr]|/forallNP fr] :=
    pselect (exists k : 'I_(ssize f), (SFun.rng f)`_k = r).
  by have := SFun.mpi k; rewrite /SFun.pi fkr.
rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
rewrite predeqE => t; split => //= ftr.
have /(nthP 0)[i fi fift] := sfun_img_rng t.
by have := fr (Ordinal fi); rewrite fift.
Qed.

End simple_function_partition.

Section sfun_lemmas1.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.

Local Lemma ltn_pidx x : (index (f x) (SFun.rng f) < n)%N.
Proof. by rewrite index_mem sfun_img_rng. Qed.

Definition pidx x := Ordinal (ltn_pidx x).

Lemma nth_pidx x : (SFun.rng f)`_(pidx x) = f x.
Proof. by rewrite nth_index //; exact: sfun_img_rng. Qed.

Lemma pi_pidx x : SFun.pi f (pidx x) x.
Proof. by rewrite /SFun.pi /preimage mksetE nth_pidx. Qed.

Lemma pi_nth i x : SFun.pi f i x -> (SFun.rng f)`_i = f x.
Proof. by []. Qed.

Lemma sfun_ge0 : (forall t, 0 <= f t) ->
  forall k : 'I_(ssize f), 0 <= (SFun.rng f)`_k.
Proof.
case: f => /= f_ c uc fc mpi f0 k.
have : [set x | x \in c] (c`_k) by apply/(nthP 0); exists k.
by rewrite -fc => -[x _ <-]; exact: f0.
Qed.

End sfun_lemmas1.

Section sfun_lemmas2.
Variables (T : measurableType) (R : realType).
Implicit Types f g : sfun T R.

Local Lemma sfun_eq_subset f g : f =1 g -> {subset SFun.rng f <= SFun.rng g}.
Proof.
move=> fg r rf.
have := SFun.full_rng g; rewrite predeqE => /(_ r)[+ _].
apply => /=.
have := SFun.full_rng f; rewrite predeqE => /(_ r)[_].
by move/(_ rf) => [t _ <-]; exists t.
Qed.

Lemma sfun_eq_perm f g : f =1 g -> perm_eq (SFun.rng f) (SFun.rng g).
Proof.
move=> fg; apply: uniq_perm; try exact: SFun.uniq_rng.
move=> r; apply/idP/idP; exact: sfun_eq_subset.
Qed.

Lemma sfun_size f g : f =1 g -> ssize f = ssize g.
Proof. by move/sfun_eq_perm => fg; rewrite /ssize; apply: perm_size. Qed.

End sfun_lemmas2.

Section simple_function_constant.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Let rng := [:: r].
Let f : T -> R := cst r.

Local Lemma sfun_cst_uniq : uniq rng. Proof. by []. Qed.

Local Lemma sfun_cst_full_rng : f @` setT = [set x | x \in rng].
Proof.
rewrite /rng predeqE => r'; split; first by move=> [t _ <- /=]; rewrite inE.
by rewrite /= inE => /eqP ->{r'}; exists point.
Qed.

Let pi := fun k : 'I_1 => f @^-1` [set rng`_k].

Local Lemma sfun_cst_mpi (k : 'I_1) : measurable (pi k).
Proof.
rewrite (_ : pi _ = setT); first exact: measurableT.
by rewrite predeqE => t; split => // _; rewrite (ord1 k).
Qed.

Definition sfun_cst :=  SFun.mk sfun_cst_uniq sfun_cst_full_rng sfun_cst_mpi.

Lemma ssize_sfun_cst : ssize sfun_cst = 1%N. Proof. by []. Qed.

End simple_function_constant.

Section simple_function_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variable (f : sfun T R).
Let n := ssize f.
Let rng := if r == 0 then [:: 0] else [seq r * x | x <- SFun.rng f].
Let g := fun x => r * f x.

Local Lemma sfun_scale_uniq : uniq rng.
Proof.
have [r0|r0] := eqVneq r 0; first by rewrite /rng r0 eqxx.
rewrite /rng (negbTE r0) map_inj_uniq; first exact: SFun.uniq_rng.
by apply: mulrI; rewrite unitfE.
Qed.

Local Lemma sfun_scale_full_rng : g @` setT = [set x | x \in rng].
Proof.
rewrite predeqE => r'; split.
  case => t _ <-{r'}; rewrite mksetE /rng.
  have [r0|r0] := eqVneq r 0;first by rewrite /g r0 mul0r inE.
  by apply/mapP; exists (f t) => //; exact: sfun_img_rng.
rewrite /= /rng; have [r0|r0 /mapP[r'']] := eqVneq r 0.
  by rewrite inE => /eqP ->{r'}; exists point => //; rewrite /g r0 mul0r.
have := SFun.full_rng f.
by rewrite predeqE => /(_ r'') /= [_ /[apply]] [t] _ <-{r''} ->{r'}; exists t.
Qed.

Let pi := fun k => g @^-1` [set rng`_k].

Local Lemma sfun_scale_mpi (k : 'I_(size rng)) : measurable (pi k).
Proof.
have [r0|r0] := eqVneq r 0.
  move: k; rewrite /pi /rng r0 eqxx /= => k.
  rewrite [_ @^-1` _](_ : mkset _ = setT); first exact: measurableT.
  by rewrite predeqE => t; split => // _; rewrite mksetE ord1 /g r0 mul0r.
move=> [:k'n]; have @k' : 'I_n.
  apply: (@Ordinal _ k); abstract: k'n.
  by rewrite /ssize /= (leq_trans (ltn_ord k)) // /rng (negbTE r0) size_map.
rewrite /pi (_ : _ @^-1` _ = SFun.pi f k'); first exact: SFun.mpi.
rewrite predeqE => t; split.
  rewrite /rng /preimage mksetE {1}(negbTE r0) (nth_map 0) //.
  by apply: mulrI; rewrite unitfE.
rewrite /SFun.pi /preimage mksetE /= /g => ->.
transitivity ([seq r * x | x <- SFun.rng f]`_k).
  by rewrite (nth_map 0).
by congr (_ `_ _); rewrite /rng (negbTE r0).
Qed.

Definition sfun_scale :=
  SFun.mk sfun_scale_uniq sfun_scale_full_rng sfun_scale_mpi.

End simple_function_scale.

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

Let rng : seq R :=
  let s := [seq y <- SFun.rng f | f @^-1` [set y] `&` A != set0] in
  if 0 \in s then s else if A == setT then s else
  if A == set0 then [:: 0] else 0 :: s.

Local Lemma sfun_proj_rng_subset a : a != 0 -> a \in rng -> a \in SFun.rng f.
Proof.
move=> a0; rewrite /rng.
case: ifPn => _; first by rewrite mem_filter => /andP[].
case: ifPn => _; first by rewrite mem_filter => /andP[].
case: ifPn => _; first by rewrite inE (negbTE a0).
by rewrite inE (negbTE a0) /= mem_filter => /andP[].
Qed.

Local Lemma sfun_proj_uniq : uniq rng.
Proof.
rewrite /rng; case: ifPn => f0; first exact/filter_uniq/SFun.uniq_rng.
case: ifPn => [_|/setTP[t At]]; first exact/filter_uniq/SFun.uniq_rng.
case: ifPn => //= /set0P[t' At']; rewrite (filter_uniq _ (SFun.uniq_rng f)).
by rewrite andbT.
Qed.

Local Lemma sfun_proj_full_rng : g @` setT = [set x | x \in rng].
Proof.
rewrite predeqE => x; split => [[t _]|] /=.
  rewrite /g; have [|tA] := boolP (t \in A).
    rewrite in_setE => tA; rewrite mulr1 => <-; rewrite /rng.
    case: ifPn => r0.
      by rewrite mem_filter sfun_img_rng andbT; apply/set0P; exists t.
    case: ifPn => [_|/setTP[t' At']].
      by rewrite mem_filter sfun_img_rng andbT; apply/set0P; exists t.
    case: ifPn => [/eqP A0|_]; first by move: tA; rewrite A0.
    rewrite inE mem_filter sfun_img_rng andbT; apply/orP; right; apply/set0P.
    by exists t.
  rewrite mulr0 => <-; rewrite /rng.
  case: ifPn => // f0; rewrite ifF; first by case: ifPn => _; rewrite inE eqxx.
  by apply/negbTE/setTP; exists t; apply: contraNnot tA; rewrite in_setE.
rewrite /rng; case: ifPn => [f0|f0].
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

Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Lemma sfun_proj_mpi k : measurable (pi k).
Proof.
rewrite /pi; set a := rng`_k.
have [a0|a0] := eqVneq a 0.
  rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A) `|` ~` A); last first.
    rewrite predeqE => t; split.
      rewrite /g /= /preimage /=; have [tA|tA _] := boolP (t \in A).
        by rewrite mulr1 => <-; left; split => //; rewrite -in_setE.
      by right; rewrite /setC /=; rewrite notin_setE in tA.
    move=> [[<- At]|At].
      rewrite /= /preimage /= /g.
      by move: At; rewrite -in_setE => ->; rewrite mulr1.
    rewrite /= /g /preimage /=.
    move: At; rewrite /setC /=; rewrite -notin_setE => /negbTE => ->.
    by rewrite mulr0.
  apply: measurableU; last by apply: measurableC.
    apply: measurableI => //.
    have [fa|fa] := boolP (a \in SFun.rng f).
      move: fa => /(nthP 0)[i fi fia].
      rewrite -fia (_ : _ @^-1` _ = SFun.pi f (Ordinal fi)) //.
      exact: SFun.mpi.
    rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
    rewrite predeqE => t; split => // fta; move/negP : fa; apply.
    by rewrite -fta; exact: sfun_img_rng.
rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A)); last first.
  rewrite predeqE => t; split.
    rewrite /g /preimage /=; have [tA|tA] := boolP (t \in A).
      by rewrite mulr1 => <-; split => //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE a0).
  move=> [<- At]; rewrite /g /preimage /=.
  by move: At; rewrite -in_setE => ->; rewrite mulr1.
apply: measurableI => //; have /(nthP 0)[i fi fia] : a \in SFun.rng f.
  by apply: sfun_proj_rng_subset => //; apply/(nthP 0); exists k.
by rewrite -fia (_ : _ @^-1` _ = SFun.pi f (Ordinal fi)) //; exact: SFun.mpi.
Qed.

Definition sfun_proj :=
  SFun.mk sfun_proj_uniq sfun_proj_full_rng sfun_proj_mpi.

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
Let a := [seq z <- [seq (x, y) | x <- SFun.rng f, y <- SFun.rng g] |
  (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0 ].
Let s (op : R -> R -> R) : seq R := undup [seq op z.1 z.2 | z <- a].

Local Lemma sfun_bin_full_rng (op : R -> R -> R) :
  (fun x => op (f x) (g x)) @` setT = [set x | x \in s op].
Proof.
rewrite predeqE => r; split.
- rewrite /= => -[t _] <-; rewrite /s mem_undup.
  apply/mapP; exists (f t, g t) => //; rewrite mem_filter /=; apply/andP; split.
    by rewrite /mkset /set1 /mkset; apply/set0P; exists t.
  by apply/allpairsP; exists (f t, g t); split => //; apply: sfun_img_rng.
- rewrite /= /s mem_undup => /mapP[[i j]].
  rewrite mem_filter /= => /andP[/set0P[t []]].
  rewrite /mkset /set1 /mkset => fti gtj.
  move=> /allpairsP[[i' j']] /= [fi' gj'] [? ?]; subst i' j' => ->.
  by exists t => //; rewrite fti gtj.
Qed.

Definition sfun_bin_pidx (op : R -> R -> R) (k : 'I_(size (s op))) :=
  [set x : 'I_n * 'I_p | (op (SFun.rng f)`_x.1 (SFun.rng g)`_x.2 == (s op)`_k)
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
     op (SFun.rng f)`_x.1 (SFun.rng g)`_x.2 == (s op)`_k)
    (SFun.pi f x.1 `&` SFun.pi g x.2)); last first.
  rewrite /sfun_bin_pidx big_mkcond [in RHS]big_mkcond.
  apply: eq_bigr => /= -[i j] _ /=; rewrite inE /=.
  by case: ifPn => //= _; case: ifPn => //; rewrite negbK => /eqP.
rewrite -bigcup_set_cond predeqE => t; split=> [fgt|].
  exists (pidx f t, pidx g t) => /=.
    by rewrite !nth_pidx -fgt // mem_index_enum eqxx.
  by split => //; exact: pi_pidx.
by move=> [[i j]] /=; rewrite mem_index_enum /= /preimage /= => /eqP <- [-> ->].
Qed.

Local Lemma sfun_bin_mpi (op : R -> R -> R) (k : 'I_(size (s op))) :
  measurable ((fun x => op (f x) (g x)) @^-1` [set (s op)`_k]).
Proof.
rewrite sfun_bin_preimageE sfun_bin_bigcupIE.
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; exact: SFun.mpi.
Qed.

Definition sfun_add := SFun.mk (undup_uniq _)
  (sfun_bin_full_rng (fun x y => x + y)) (@sfun_bin_mpi (fun x y => x + y)).

Definition sfun_max := SFun.mk (undup_uniq _)
  (sfun_bin_full_rng maxr) (@sfun_bin_mpi maxr).

Lemma sfun_bin_pi_cover0 (op : R -> R -> R) :
  \bigcup_(c < size (s op)) sfun_bin_pidx c =
  [set x : {: 'I_n * 'I_p}|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET.
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP/idP => /=.
- move=> [i] _.
  by rewrite inE /= => /eqP/eqP/andP[].
- move=> kl.
  suff [i kli] : exists i : 'I_(size (s op)),
      op (SFun.rng f)`_k (SFun.rng g)`_l = (s op)`_i.
    by exists i => //; rewrite inE /= kli eqxx.
  have : op (SFun.rng f)`_k (SFun.rng g)`_l \in
         [set of (fun x => op (f x) (g x))].
    rewrite inE /=; move/set0P : kl => [t [/pi_nth kt /pi_nth lt]].
    by exists t => //; rewrite -kt -lt.
  by rewrite sfun_bin_full_rng inE /= => /(nthP 0)[x xa H]; exists (Ordinal xa).
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
transitivity ((sfun_add f g) @^-1` [set (SFun.rng (sfun_add f g))`_c]) => //.
by rewrite sfun_bin_preimageE.
Qed.

Lemma trivIset_sfunI (D : set T) :
  trivIset setT (fun i : 'I_n * 'I_p => SFun.pi f i.1 `&` SFun.pi g i.2 `&` D).
Proof.
apply/trivIsetP => /= -[a b] [c d] _ _ /=.
rewrite xpair_eqE negb_and => /orP[ac|bd].
  rewrite setIACA (_ : SFun.pi f a `&` _ `&` _ = set0) ?set0I//.
  rewrite setIACA (_ : SFun.pi f a `&` _ = set0) ?set0I//.
  by move/trivIsetP: (@trivIset_sfun _ _ f setT) => /(_ _ _ Logic.I Logic.I ac).
rewrite setIACA (_ : SFun.pi f a `&` _ `&` _ = set0) ?set0I//.
rewrite setIACA (_ : SFun.pi g b `&` _ = set0) ?setI0//.
by move/trivIsetP : (@trivIset_sfun _ _ g setT) => /(_ _ _ Logic.I Logic.I bd).
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

Lemma NNSFun_ge0 (f : nnsfun T R) (k : 'I_(ssize f)) : 0 <= (SFun.rng f)`_k.
Proof. exact: sfun_ge0. Qed.

Lemma SFuncdom_ge0 (f : nnsfun T R) (r : R) :
  (r \in SFun.rng f) -> (0 <= r%:E)%E.
Proof.
by move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNSFun_ge0 (Ordinal fi)).
Qed.

End nnsfun_lemmas.

(*Hint Extern 0 (0%E <= ((SFun.cdom _)`__)%:E)%E => solve [apply: NNSFun_ge0] : core.*)

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
Proof. by rewrite /nnsfun_sum; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnsfun_sum.

Section nnsfun_bigmax.
Variables (T : measurableType) (point : T) (R : realType) (f : (nnsfun T R)^nat).

Definition nnsfun_bigmax n :=
  \big[(@nnsfun_max T R)/(nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)))]_(i < n) f i.

Lemma nnsfun_bigmaxE n t : nnsfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /nnsfun_bigmax; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnsfun_bigmax.

Section simple_function_integral.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (f : sfun T R).
Let n := ssize f.
Let A := SFun.pi f.
Let a := SFun.rng f.
Local Open Scope ereal_scope.

Definition sintegral : \bar R := \sum_(k < n) (a`_k)%:E * mu (A k `&` D).

Lemma sintegralE : sintegral =
  \sum_(x <- SFun.rng f) x%:E * mu (f @^-1` [set x] `&` D).
Proof.
rewrite big_tnth; apply: eq_bigr => i _; congr (_%:E * mu _).
  by apply: set_nth_default; rewrite /= ltn_ord.
rewrite /A /SFun.pi; congr (_ @^-1` _ `&` _); rewrite predeqE => r; split;
  by rewrite /set1 mksetE => ->; apply: set_nth_default; rewrite ltn_ord.
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

Section sintegralM.
Variables (T : measurableType) (point : T).
Variables (R : realType) (m : {measure set T -> \bar R}).
Variables (r : R) (D : set T) (mD : measurable D) (f : nnsfun T R).
Local Open Scope ereal_scope.

Lemma sintegralM :
  sintegral m D (sfun_scale point r f) = r%:E * sintegral m D f.
Proof.
have [->|r0] := eqVneq r 0%R.
  rewrite mul0e /sintegral big1 // => i _; rewrite /= eqxx /=.
  case: (m (_ `&` _)) => [x| |]; move: i; rewrite ssize_sfun_scale0 => i.
  - by rewrite (ord1 i) mul0e.
  - by rewrite (ord1 i) /= mul0e.
  - by rewrite (ord1 i) /= mul0e.
rewrite /sintegral.
pose cast := cast_ord (ssize_sfun_scale_neq0 point f r0).
rewrite [LHS](eq_bigr (fun k : 'I_(ssize (sfun_scale point r f)) =>
  (r * (SFun.rng f)`_(cast k))%:E * m (SFun.pi f (cast k) `&` D))); last first.
  move=> i _; congr (_%:E * m _).
    rewrite /= (negbTE r0) (nth_map 0%R) // (leq_trans (ltn_ord i)) //.
    by rewrite ssize_sfun_scale_neq0.
  rewrite predeqE => x; split.
    rewrite /SFun.pi /= /set1 /= {1}(negbTE r0) (nth_map 0%R); last first.
      by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
    by move=> [/mulrI fxi Dx]; split => //; apply: fxi; rewrite unitfE.
  rewrite /SFun.pi /set1 /= => -[fxi Dx]; split => //.
  rewrite /= /preimage /= fxi {1}(negbTE r0) (nth_map 0%R) //.
  by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
rewrite ge0_sume_distrr; last first.
  move=> i _; rewrite mule_ge0 //; first exact: NNSFun_ge0.
  by apply: measure_ge0; apply/measurableI => //; exact/SFun.mpi.
pose castK := cast_ord (esym (ssize_sfun_scale_neq0 point f r0)).
rewrite (reindex castK); last first.
  by exists cast => i; by rewrite /cast /castK /= ?(cast_ordKV,cast_ordK).
by apply: eq_bigr => i _; rewrite /cast /castK cast_ordKV mulEFin muleA.
Qed.

End sintegralM.

Section sintegralD.
Variables (T : measurableType) (R : realType) (D : set T).
Variables (mD : measurable D) (f g : nnsfun T R).
Variable m : {measure set T -> \bar R}.
Let n := ssize f.
Let p := ssize g.
Local Open Scope ereal_scope.

Lemma sintegralD :
  sintegral m D (sfun_add f g) = sintegral m D f + sintegral m D g.
Proof.
transitivity (\sum_(i < n) \sum_(l < p)
  ((SFun.rng f)`_i + (SFun.rng g)`_l)%:E * m (SFun.pi f i `&` SFun.pi g l `&` D)).
  rewrite /sintegral; under eq_bigr do rewrite (measure_sfun_bin_pi _ mD).
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g)))
    (\sum_(x in sfun_bin_pidx i)
      ((SFun.rng f)`_x.1 + (SFun.rng g)`_x.2)%:E *
      m (SFun.pi f x.1 `&` SFun.pi g x.2 `&` D))).
    apply: eq_bigr => i _; rewrite ge0_sume_distrr //; last first.
      move=> kl _; rewrite measure_ge0 //; apply: measurableI => //.
      by apply: measurableI; exact: SFun.mpi.
    by apply: eq_bigr => x; rewrite !inE => /andP[] /eqP ->.
  rewrite [in RHS]pair_big /=.
  rewrite [in RHS](eq_bigl [pred x | x \in setX [set: _] [set: _]]); last first.
    by move=> [k l]; rewrite !inE.
  transitivity (\sum_(x in [set x|SFun.pi f x.1 `&` SFun.pi g x.2 != set0]%SET)
      ((SFun.rng f)`_x.1 + (SFun.rng g)`_x.2)%:E *
      m (SFun.pi f x.1 `&` SFun.pi g x.2 `&` D)); last first.
    rewrite big_mkcond; apply: eq_big => //; first by move=> x; rewrite !inE.
    move=> [x y] _; case: ifPn => //; rewrite inE negbK => /eqP -> /=.
    by rewrite set0I measure0 mule0.
  rewrite -(sfun_bin_pi_cover0 _ _ (fun x y => x + y)%R).
  rewrite partition_disjoint_bigcup //= => i j ij.
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[[k l]].
  rewrite inE /= => /andP[]; rewrite 2!inE => /andP[/eqP -> _] /andP[+ _].
  by rewrite (nth_uniq _ _ _ (undup_uniq _)) //; exact/negP.
rewrite /sintegral -/n -/p [RHS]addeC.
have ggf k : m (SFun.pi g k `&` D) =
    \sum_(i < n) m (SFun.pi g k `&` SFun.pi f i `&` D).
  rewrite -[in LHS](setIT (SFun.pi g k `&` D)) -(bigcup_sfun f) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
under [X in _ = X + _]eq_bigr do rewrite ggf.
transitivity (\sum_(i < p) (\sum_(j < n)
     ((SFun.rng g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f j `&` D)) +
   \sum_(k < n) ((SFun.rng f)`_k)%:E * m (SFun.pi f k `&` D)); last first.
  congr adde; apply: eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
have ffg k : m (SFun.pi f k `&` D) =
             \sum_(l < p) m (SFun.pi f k `&` SFun.pi g l `&` D).
  rewrite -[in LHS](setIT (SFun.pi f k `&` D)) -(bigcup_sfun g) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_sfun.
  by move=> i; apply: measurableI => //; apply/measurableI; exact: SFun.mpi.
under [X in _ = _ + X]eq_bigr do rewrite ffg.
transitivity (\sum_(i < p) \sum_(j < n)
    ((SFun.rng g)`_i)%:E * m (SFun.pi g i `&` SFun.pi f j `&` D) +
    \sum_(i < n) \sum_(l < p)
    ((SFun.rng f)`_i)%:E * m (SFun.pi f i `&` SFun.pi g l `&` D)); last first.
  congr adde; apply: eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
rewrite [X in _ = X + _]exchange_big.
rewrite -big_split; apply: eq_bigr => i _.
rewrite -big_split; apply: eq_bigr => j _.
rewrite -[in RHS](setIC (SFun.pi f i)).
by rewrite addEFin ge0_muleDl //;
  [rewrite addeC|exact: NNSFun_ge0|exact: NNSFun_ge0].
Qed.

End sintegralD.

Section le_sintegral.
Variables (T : measurableType) (point : T) (R : realType).
Variable m : {measure set T -> \bar R}.
Implicit Types D : set T.

Lemma eq_sintegral D (f g : sfun T R) : {in D, f =1 g} ->
  sintegral m D f = sintegral m D g.
Proof.
move=> fg.
rewrite 2!sintegralE (bigID (fun x => f @^-1` [set x] `&` D == set0)) /=.
rewrite big1 ?add0e; last by move=> r /eqP ->; rewrite measure0 mule0.
apply/esym; rewrite (bigID (fun x => g @^-1` [set x] `&` D == set0)) /=.
rewrite big1 ?add0e; last by move=> r /eqP ->; rewrite measure0 mule0.
rewrite -big_filter -[in RHS]big_filter.
set lhs := seq.filter _ _; set rhs := seq.filter _ _.
rewrite (perm_big rhs); last first.
  rewrite /lhs /rhs.
  apply: uniq_perm; do 1? [by rewrite filter_uniq // SFun.uniq_rng].
  move=> r; rewrite !mem_filter; apply/andP/andP=> -[/set0P[t /= [gt Dt rg]]].
    split.
    - apply/set0P; exists t => //; split => //; rewrite /preimage /= fg//.
      by rewrite in_setE.
    - have := SFun.full_rng f; rewrite predeqE => /(_ r)[].
      rewrite /preimage /= -fg in gt; last by rewrite in_setE.
      have H : [set of f] r by exists t.
      by move/(_ H).
  split.
    - apply/set0P; exists t => //; split => //; rewrite /preimage /= -fg //.
      by rewrite in_setE.
    - have := SFun.full_rng g; rewrite predeqE => /(_ r)[].
      rewrite /preimage /= fg in gt; last by rewrite in_setE.
      have H : [set of g] r by exists t.
      by move/(_ H).
rewrite [in LHS]big_filter [in RHS]big_filter; apply: eq_bigr => // r rfD0.
congr (_ * m _)%E; rewrite predeqE => t; split => [|] [<- Dt].
- by split => //; rewrite /preimage /= fg// in_setE.
- by split => //; rewrite /preimage /= -fg// in_setE.
Qed.

Lemma le_sintegral D (mD : measurable D) (f g : nnsfun T R) :
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

Lemma is_cvg_sintegral D (mD : measurable D) (f : (nnsfun T R)^nat) :
  (forall x, D x -> nondecreasing_seq (f^~ x)) ->
  cvg (fun n => sintegral m D (f n)).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/nondecreasing_ereal_cvg => a b ab.
by apply: le_sintegral => // => x Dx; apply/nd_f.
Qed.

End le_sintegral.

Section preimage_setI.
Variables (T : measurableType) (R : realType) (g : nnsfun T R).

Lemma gSxE (S : set T) (x : R) :
  [set t | [set x] (g t * (t \in S)%:R)] =
    ((S `&` (g @^-1` [set x])) `|` (~` S `&` (fun _ => x = 0))).
Proof.
rewrite (_ : (fun t : T => _) =
             (fun t => if t \in S then g t = x else x = 0)); last first.
  rewrite predeqE => t; split;
    by have [tS|tS] := boolP (t \in S); rewrite !(mulr1,mulr0).
rewrite (_ : (fun t : T => _) =
        ((S `&` (g @^-1` [set x])) `|` (~` S `&` (fun _ => x = 0)))) //.
rewrite predeqE => t; split.
  case: ifPn => [tS <-|tS].
    by left; split => //; rewrite -in_setE.
  by right; split => //; apply: contraNnot tS; rewrite in_setE.
case: ifPn => [tS [[_ <-//]|[]] |tS [[]|[]//]].
- by rewrite in_setE in tS.
- by rewrite -in_setE (negbTE tS).
Qed.

Local Obligation Tactic := idtac.

Definition preimgI_rng (S : set T) :=
  let s := [seq x <- SFun.rng g | (g @^-1` [set x]) `&` S != set0] in
  if (0 \in s) || (S == setT) then s else rcons s 0.

Program Definition preimgI_sfun (S : set T) (mS : measurable S) : sfun T R :=
  @SFun.mk _ _ (fun x => g x * (x \in S)%:R) (preimgI_rng S) _ _ _.
Next Obligation.
move=> S _; rewrite /preimgI_rng; set s := seq.filter _ _ => /=.
have [_|] := ifPn; first by rewrite filter_uniq // SFun.uniq_rng.
rewrite negb_or => /andP[s0 _].
by rewrite rcons_uniq s0 /= filter_uniq // SFun.uniq_rng.
Qed.
Next Obligation.
move=> S _; rewrite /preimgI_rng; set s := seq.filter _ _ => /=.
rewrite predeqE => x; split => [[t _ <-{x}]|] /=.
  have [tS|tS] /= := boolP (t \in S).
    rewrite mulr1; have [_|_] := ifPn.
      rewrite mem_filter sfun_img_rng andbT; apply/set0P.
      by exists t => //; split => //=; rewrite -in_setE.
    rewrite mem_rcons inE; apply/orP; right.
    rewrite mem_filter sfun_img_rng andbT; apply/set0P.
    by exists t; split => //=; rewrite -in_setE.
  rewrite mulr0; have [/orP[//|/eqP]|] := ifPn.
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
move=> S mS; rewrite /preimgI_rng; set s := seq.filter _ _ => /=.
have sg : (size s <= ssize g)%N by rewrite size_filter count_size.
have [/orP[s0 k|/eqP ST k]|] := ifPn.
  - have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.rng g)`_k'.
      have : s`_k \in SFun.rng g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite /preimage /= gSxE.
    apply: measurableU.
      apply: measurableI => //.
      by have := @SFun.mpi _ _ g k'; rewrite /SFun.pi /= -kk'.
    apply: measurableI; first exact: measurableC.
    have [sk0|sk0] := pselect (s`_k = 0).
      by rewrite (_ : (fun _ => _) = setT) ?predeqE//; exact: measurableT.
    by rewrite (_ : (fun _ => _) = set0) ?predeqE//; exact: measurable0.
  - have [k' kk'] : exists k' : 'I_(ssize g), s`_k = (SFun.rng g)`_k'.
      have : s`_k \in SFun.rng g.
        have : s`_k \in s by apply/(nthP 0); exists k.
        by rewrite mem_filter => /andP[].
      by move=> /(nthP 0)[i ig <-]; exists (Ordinal ig).
    rewrite [X in _ X](_ : _ = [set t | [set s`_k] (g t)]).
      by have := @SFun.mpi _ _ g k'; rewrite /SFun.pi /= -kk'.
    rewrite predeqE => t.
    by rewrite /= /set1 /preimage /= (_ : _ \in _) ?mulr1// in_setE ST.
rewrite negb_or => /andP[s0 ST] k.
rewrite /preimage /= gSxE; have [ks|ks] := eqVneq (nat_of_ord k) (size s).
  rewrite nth_rcons ks ltnn eqxx; apply: measurableU.
    have [->|/set0P[t [St g0t]]] := eqVneq (S `&` g @^-1` [set 0]) set0.
      exact: measurable0.
    suff : 0 \in s by rewrite (negbTE s0).
    rewrite mem_filter; apply/andP; split; first by apply/set0P; exists t.
    by rewrite -g0t sfun_img_rng.
  apply: measurableI; first exact: measurableC.
  by rewrite (_ : (fun _ => _) = setT) ?predeqE //; exact: measurableT.
have [k' kk'] : exists k' : 'I_(ssize g), (rcons s 0)`_k = (SFun.rng g)`_k'.
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
Hypothesis gf : forall x, D x -> cvg (g^~ x) -> f x <= lim (g^~ x).

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
have := NNSFun.ge0 f x; rewrite le_eqVlt => /predU1P[|] gx0.
  exists O => //; rewrite /fleg /=; split => //=.
  by rewrite -gx0 mulr0 NNSFun.ge0.
have [cf|df] := pselect (cvg (g^~ x)).
  have cfg : lim (g^~ x) > c * f x.
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
rewrite [X in _ X](_ : _ = \big[setU/set0]_(y <- SFun.rng f)
    \big[setU/set0]_(x <- SFun.rng (g n) | c * y <= x)
      ((f @^-1` [set y]) `&` (g n @^-1` [set x]))); last first.
  rewrite predeqE => t; split.
    rewrite /= => fgcn; rewrite -bigcup_set.
    exists (f t); first exact: sfun_img_rng.
    rewrite -bigcup_set_cond; exists (g n t) => //.
    by apply/andP; split => //; exact: sfun_img_rng.
  rewrite -bigcup_set => -[r /= rf].
  by rewrite /fleg -bigcup_set_cond => -[? /andP[? ?]] [/= -> ->].
apply: bigsetU_measurable => r _.
apply: bigsetU_measurable => r' crr'.
by apply: measurableI; exact: measurable_preimage_set1.
Qed.

Local Open Scope ereal_scope.

(* lemma 1.6 *)
Lemma nd_sintegral_lim_lemma : sintegral mu D f <= lim (sintegral mu D \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu D f <= lim (sintegral mu D \o g).
  by apply/lee_mul01Pr => //; apply: sintegral_ge0.
move=> c /andP[c0 c1].
pose g1' n := preimgI_sfun f (measurable_fgeg c n).
have g1'_ge0 n x : (0 <= g1' n x)%R by rewrite /g1' mulr_ge0.
pose g1 n := NNSFun.mk (g1'_ge0 n).
have cg1leg n x : D x -> (c * g1 n x <= g n x)%R.
  move=> Dx; rewrite /g1 /= /fleg /=; have [|] := boolP (x \in _).
    by rewrite in_setE => -[/=]; rewrite mulr1.
  by rewrite 2!mulr0 NNSFun.ge0.
have cg1_ge0 n x : (0 <= (sfun_scale point c (g1 n)) x)%R.
  by rewrite mulr_ge0 // ltW.
have {cg1leg}cg1g n : c%:E * sintegral mu D (g1 n) <= sintegral mu D (g n).
  rewrite -(sintegralM point mu c mD (g1 n)).
  apply: (@le_sintegral _ _ _ _ _ _ (NNSFun.mk (cg1_ge0 n))) => //=.
  by move=> x Dx; rewrite /fleg /= cg1leg.
suff {cg1g}<- : lim (fun n => sintegral mu D (g1 n)) = sintegral mu D f.
  have is_cvg_g1 : cvg (fun n => sintegral mu D (g1 n)).
    apply: is_cvg_sintegral => //= x Dx m n mn.
    by have /lefP/(_ x) := le_ffleg c mn.
  rewrite -ereal_limrM // lee_lim//.
  - exact: ereal_is_cvgrM.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu D (g1 n)) --> sintegral mu D f by apply/cvg_lim.
rewrite [X in X --> _](_ : _ =
    (fun n => \sum_(k < ssize f) ((SFun.rng f)`_k)%:E *
    mu (f @^-1` [set (SFun.rng f)`_k] `&` fleg c n `&` D))); last first.
  rewrite funeqE => n; rewrite sintegralE.
  transitivity (\sum_(x <- SFun.rng f) x%:E * mu (g1 n @^-1` [set x] `&` D)).
    rewrite (_ : SFun.rng (g1 n) = preimgI_rng f (fleg c n))// /preimgI_rng/=.
    case: ifPn=> [/orP[|/eqP cnT]|_].
    - rewrite mem_filter /= => /andP[].
      rewrite /preimage /= => /set0P[t [ft0 cnt]] f0.
      rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0// predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /preimage /=; have [xcn|xcn] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite -in_setE.
      rewrite mulr0 => r0.
      by move: I0; rewrite predeqE => /(_ t)[+ _]; apply; rewrite -r0.
    - rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /preimage /= cnT; have [xT|] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite cnT.
      by rewrite notin_setE => /(_ Logic.I).
    - rewrite -cats1 big_cat /= big_cons big_nil mul0e !adde0.
      rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      have [->|r0] := eqVneq r 0%R; first by rewrite mul0e.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /preimage /=; have [xT|_ ] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite -in_setE.
      by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  rewrite big_tnth; apply: eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0%R) //=.
  have [fi0|fi0] := eqVneq ((SFun.rng f)`_i) 0%R.
    by rewrite fi0 // 2!mul0e.
  congr (_%:E * mu _); rewrite predeqE => x; split => [|[]] /=.
  - rewrite /preimage /= => -[/[swap] Dx].
    have [xcn|_] := boolP (_ \in fleg _ _).
      by rewrite mulr1 => <-; split => //; split=> //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE fi0).
  - rewrite /preimage /= => -[fxi]; rewrite -in_setE => cnx Dx; split => //.
    by rewrite fxi cnx mulr1.
rewrite [X in X --> _](_ : _ = fun n => \sum_(x <- SFun.rng f) x%:E *
    mu (f @^-1` [set x] `&` fleg c n `&` D)); last first.
  rewrite funeqE => n; rewrite [in RHS]big_tnth /=; apply/eq_bigr => i _.
  rewrite [in LHS](set_nth_default 0%R) //=; congr (_%:E * mu (_ `&` _ `&` _)).
    exact: set_nth_default.
  rewrite predeqE => t /=; rewrite /preimage /= -propeqE.
  by congr (_ = _); exact: set_nth_default.
rewrite sintegralE big_seq.
under [in X in X --> _]eq_fun do rewrite big_seq.
have measurable_ffleg k i : measurable (f @^-1` [set k] `&` fleg c i `&` D).
  apply: measurableI => //; apply: measurableI;
    [exact: measurable_preimage_set1|exact: measurable_fgeg].
apply: ereal_lim_sum => [r n /SFuncdom_ge0 r0|r rf].
  by rewrite mule_ge0// measure_ge0.
apply: ereal_cvgrM => //.
rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n `&` D))); last first.
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
Hypothesis gf : forall x, D x -> (g^~x) --> f x.

Let limg : forall x, D x -> lim (g^~x) = f x.
Proof. by move=> x Dx; apply/cvg_lim; [exact: Rhausdorff| exact: gf]. Qed.

Lemma nd_sintegral_lim : sintegral mu D f = lim (sintegral mu D \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x Dx; rewrite -limg.
have : nondecreasing_seq (sintegral mu D \o g).
  by move=> m n mn; apply: (le_sintegral point) => // x Dx; exact/nd_g.
move=> /nondecreasing_ereal_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=.
apply: le_sintegral => // x Dx.
rewrite -limg // (nondecreasing_cvg_le (nd_g Dx)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Lemma sub0e (R : numDomainType) (x : \bar R) : (0 - x = - x)%E.
Proof. by move: x => [x| |] //; rewrite -subEFin sub0r. Qed.

Section integral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).
Implicit Type D : set T.
Local Open Scope ereal_scope.

Definition nnintegral D (f : T -> \bar R) :=
  ereal_sup [set sintegral mu D g | g in
    [set g : nnsfun T R | forall x, D x -> (g x)%:E <= f x]].

Lemma nnintegral_ge0 D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) -> 0 <= nnintegral D f.
Proof.
move=> f0; apply: ereal_sup_ub => /=.
exists (@nnsfun_cst T point R (Nonneg.NngNum _ (ler0n _ O))).
  by move=> x /= Dx; exact: f0.
rewrite /sintegral /= big1 //= => k _.
by rewrite (_ : _%:E = 0%E) ?mul0e//; move: k => [[|]].
Qed.

Lemma eq_nnintegral D (g f : T -> \bar R) :
  (forall x, D x -> f x = g x) -> nnintegral D f = nnintegral D g.
Proof.
move=> fg; rewrite /nnintegral; congr ereal_sup; rewrite eqEsubset; split.
  by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite -fg// hf.
by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite fg// hf.
Qed.
Arguments eq_nnintegral {D} _ {f} _.

Lemma nnintegral0 D : nnintegral D (fun=> 0) = 0.
Proof.
pose cst0 : nnsfun T R := nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub => /=; exists cst0 => //=.
  by rewrite sintegralE /= big_cons big_nil adde0 mul0e.
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, D x -> f x = 0%R.
  by move=> y ?; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin NNSFun.ge0.
rewrite /sintegral big1 //= => i _.
(* NB: improve? *)
have [->|/set0P[t [fit Dt]]] := eqVneq (SFun.pi f i `&` D) set0.
  by rewrite measure0 mule0.
by rewrite (pi_nth fit) f0 // mul0e.
Qed.

Definition integral D (f : T -> \bar R) :=
  nnintegral D (f ^\+) - nnintegral D (f ^\-).

Lemma ge0_integralE D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) -> integral D f = nnintegral D f.
Proof.
move=> f0; rewrite /integral; rewrite (eq_nnintegral f (ge0_funenngE f0)).
by rewrite (eq_nnintegral (cst 0) (ge0_funennpE f0)) nnintegral0 sube0.
Qed.

Lemma ge0_integralN D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> integral D (fun x => - f x) = - integral D f.
Proof.
move=> f0.
rewrite /integral (eq_nnintegral (cst 0) (ge0_funennpE f0)).
by rewrite nnintegral0 sube0 sub0e funennpN.
Qed.

Lemma ge0_integral D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) -> 0 <= integral D f.
Proof. by move=> f0; rewrite ge0_integralE// nnintegral_ge0. Qed.

End integral.

Section nondecreasing_integral_limit.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).

Hypothesis f0 : forall x, D x -> (0 <= f x)%E.
Hypothesis mf : measurable_fun D f.
Variable (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Hypothesis gf : forall x, D x -> @EFin _ \o g^~x --> f x.

Lemma nd_ge0_integral_lim : integral mu D f = lim (sintegral mu D \o g).
Proof.
rewrite ge0_integralE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x Dx.
  have <- : lim (@EFin _ \o g^~ x) = f x.
    by apply/cvg_lim => //; apply: gf.
  have : (@EFin _ \o g^~ x) --> ereal_sup [set of @EFin _ \o g^~ x].
    apply: nondecreasing_ereal_cvg => p q pq /=; rewrite lee_fin.
    exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ub => /=; exists n.
have := lee_pinfty (nnintegral mu D f).
rewrite le_eqVlt => /predU1P[mufoo|]; last first.
  move mufr : (nnintegral mu D f) => r.
  move: r mufr => [r mufr _|//|mufr]; last first.
    by move: (nnintegral_ge0 point mu f0); rewrite mufr.
  rewrite -mufr.
  move/ub_ereal_sup_adherent : mufr; rewrite -/(integral _ _) => h.
  apply: lee_adde => e.
  have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite lte_subl_addr => fGe.
  have : forall x, D x -> cvg (g^~ x) -> G x <= lim (g^~ x).
    move=> x Dx cg; rewrite -lee_fin -EFin_lim //=.
    have := gf Dx => /cvg_lim gxfx.
    by rewrite (le_trans (Gf _ Dx)) // gxfx.
  move/(@nd_sintegral_lim_lemma _ point _ mu _ mD _ nd_g).
  by move/(lee_add2r e%:num%:E)/(le_trans (ltW fGe)).
suff : lim (sintegral mu D \o g) = +oo%E by move=> ->; rewrite mufoo.
apply/eq_pinfty => A A0.
have [G [Gf AG]] : exists h : nnsfun T R, (forall x, D x -> (h x)%:E <= f x)%E /\
                                     (A%:E <= sintegral mu D h)%E.
  move: (mufoo).
  rewrite /integral => /eq_pinfty.
  have A20 : 0 < A + A by rewrite addr_gt0.
  move/(_ _ A20) => A2.
  have {} : (A%:E < ereal_sup [set sintegral mu D g0 | g0 in
       [set h : nnsfun T R | (forall x, D x -> (h x)%:E <= f x)]])%E.
    by rewrite (lt_le_trans _ A2) // lte_fin ltr_addr.
  move/ereal_sup_gt => [x [/= [G Gf Gx Ax]]].
  by exists G; split => //; rewrite (le_trans (ltW Ax)) // Gx.
have : forall x, D x -> cvg (g^~ x) -> G x <= lim (g^~ x).
  move=> x Dx cg; rewrite -lee_fin -EFin_lim //.
  have := gf Dx => /cvg_lim gxfx.
  by rewrite (le_trans (Gf _ Dx)) // gxfx.
move/(@nd_sintegral_lim_lemma _ point _ mu _ mD _ nd_g) => Gg.
by rewrite (le_trans AG).
Grab Existential Variables. all: end_near. Qed.

End nondecreasing_integral_limit.

Section dyadic_interval.
Variable R : realType.

Definition dyadic_itv n k : interval R :=
  `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[.

Local Notation I := dyadic_itv.

Lemma dyadic_itv_subU n k : [set` I n k] `<=`
  [set` I n.+1 k.*2] `|` [set` I n.+1 k.*2.+1].
Proof.
move=> r /=; rewrite in_itv /= => /andP[Ir rI].
have [rk|rk] := ltP r (k.*2.+1%:R * (2%:R ^- n.+1)); [left|right].
- rewrite in_itv /= rk andbT (le_trans _ Ir)// -muln2.
  rewrite natrM exprS invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2).
  by rewrite divrr ?unitfE// mulr1.
- rewrite in_itv /= rk /= (lt_le_trans rI)// -doubleS.
  rewrite -muln2 natrM exprS invrM ?unitfE// ?expf_neq0// -mulrA (mulrCA 2).
  by rewrite divrr ?unitfE// mulr1.
Qed.

Lemma bigsetU_dyadic_itv n : `[n%:R, n.+1%:R[%classic =
  \big[setU/set0]_(n * 2 ^ n.+1 <= k < n.+1 * 2 ^ n.+1) [set` I n.+1 k].
Proof.
rewrite predeqE => r; split => [|].
- rewrite /= in_itv /= => /andP[nr rn1]; rewrite -bigcup_set /=.
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
  rewrite /= in_itv /=; apply/andP; split.
    rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
    rewrite (le_trans _ (floor_le _)) // -(@gez0_abs (floor _)) // floor_ge0.
    by rewrite mulr_ge0 // ?(le_trans _ nr)// -natrX ler0n.
  rewrite ltr_pdivl_mulr; last by rewrite -natrX ltr0n expn_gt0.
  rewrite (lt_le_trans (lt_succ_Rfloor _))// RfloorE -[in X in _ <= X]addn1.
  rewrite natrD ler_add2r // -(@gez0_abs (floor _)) // floor_ge0.
  by rewrite mulr_ge0// -?natrX ?ler0n// (le_trans _ nr).
- rewrite -bigcup_set => -[/= k].
  rewrite mem_index_iota => /andP[nk kn].
  rewrite in_itv /= => /andP[knr rkn].
  rewrite in_itv /=; apply/andP; split.
    rewrite (le_trans _ knr) // ler_pdivl_mulr// -?natrX ?ltr0n ?expn_gt0//.
    by rewrite -natrM ler_nat.
  rewrite (lt_le_trans rkn) // ler_pdivr_mulr.
    by rewrite -natrX -natrM ler_nat.
  by rewrite -natrX ltr0n expn_gt0.
Qed.

Lemma dyadic_itv_image n T (f : T -> \bar R) x :
  (n%:R%:E <= f x < n.+1%:R%:E)%E ->
  exists k, (2 ^ n.+1 * n <= k < 2 ^ n.+1 * n.+1)%N /\
    f x \in @EFin _ @` [set` I n.+1 k].
Proof.
move=> fxn.
have fxE : (real_of_extended (f x))%:E = f x.
  rewrite -EFin_real_of_extended// fin_numE.
  by move: fxn; case: (f x) => // /andP[].
have : f x \in @EFin _ @` `[n%:R, n.+1%:R[%classic.
  rewrite in_setE /=; exists (real_of_extended (f x)) => //.
  by rewrite in_itv /= -lee_fin -lte_fin !fxE.
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
  [set x | f x \in @EFin _ @` [set` I n k]] else set0) `&` D.

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
  by rewrite setIC; apply: h => //; rewrite lt_eqF.
move=> ij _.
rewrite /A; case: ifPn => /= ni; last by rewrite set0I.
case: ifPn => /= nj; last by rewrite setI0.
rewrite predeqE => t; split => // -[/=].
rewrite inE => -[r /=]; rewrite in_itv /= => /andP[r1 r2] rft.
rewrite inE => -[s /=]; rewrite in_itv /= => /andP[s1 s2].
rewrite -rft => -[sr]; rewrite {}sr {s} in s1 s2.
have := le_lt_trans s1 r2.
by rewrite ltr_pmul2r ?invr_gt0 ?exprn_gt0// ltr_nat ltnS leqNgt ij.
Qed.

Local Lemma f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  x \in A n i = false.
Proof.
move=> fx0 i0; apply/negbTE; rewrite notin_setE /A ltn_ord /=.
move=> -[/[swap] Dx] /=.
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[r1 r2].
rewrite fx0 => -[r0]; move: r1 r2; rewrite {}r0 {r} => + r2.
rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
by rewrite mul0r lern0; exact/negP.
Qed.

Local Lemma fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  x \in A n i = false.
Proof.
move=> fxn; apply/negbTE; rewrite /A ltn_ord.
rewrite notin_setE => -[/[swap] Dx] /=; apply/negP.
rewrite notin_setE /= => -[r /=].
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
Proof. exact: emeasurable_fun_c_infty. Qed.

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
(* /technical properties of the sets A and B *)

Local Lemma f0_approx_fun0 n x : f x = 0%E -> approx_fun n x = 0.
Proof.
move=> fx0; rewrite /approx_fun; have [->|n0] := eqVneq n O.
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0 // mulr0 addr0 big1 // => /= i _.
have [->|i0] := eqVneq (nat_of_ord i) 0%N; first by rewrite mul0r mul0r.
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
  - apply: sumr_ge0 => i _.
    by rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
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
  rewrite in_itv /=; apply/andP; split.
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
apply/orP; right; rewrite natrX; apply/ltW; near: n.
exact: near_infty_natSinv_expn_lt (PosNum fx_gt0).
Grab Existential Variables. all: end_near. Qed.

Local Lemma f_ub_approx_fun n x : (f x < n%:R%:E)%E ->
  approx_fun n x == 0 \/ exists k,
    [/\ (0 < k < n * 2 ^ n)%N,
       x \in A n k, approx_fun n x = k%:R / 2 ^+ n &
       f x \in @EFin _ @` [set` I n k]].
Proof.
move=> fxn; rewrite /approx_fun fgtn_B0 // mulr0 addr0.
set lhs := (X in X == 0); have [|] := eqVneq lhs 0; first by left.
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
by move: xAnk; rewrite inE /A ltn_ord /= inE /= => -[/[swap] Dx].
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
  move: (xAnk); rewrite inE {1}/A => -[/[swap] _] /=.
  rewrite kn /= in_setE => -[r] /dyadic_itv_subU[|] rnk rfx.
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
have /orP[{}fxn|{}fxn] :
    ((n%:R%:E <= f x < n.+1%:R%:E) || (n.+1%:R%:E <= f x))%E.
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
  rewrite xBn1 mulr1 big1 ?add0r.
    by rewrite big1 ?add0r ?ler_nat // => /= i _; rewrite fgen_A0 // mulr0.
  by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn)// lee_fin ler_nat.
Qed.

Lemma cvg_approx_fun x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  (f x < +oo)%E -> (approx_fun^~ x) --> real_of_extended (f x).
Proof.
move=> Dx fxoo.
have /EFin_real_of_extended fxE : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
apply/(@cvg_distP _ [normedModType R of R^o]) => _/posnumP[e].
rewrite near_map.
have [fx0|fx0] := eqVneq (f x) 0%E.
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
  rewrite (_ : `| _ |%:R  = (floor (real_of_extended (f x)))%:~R); last first.
    by rewrite -[in RHS](@gez0_abs (floor _)) // floor_ge0 //; exact/le0R/f0.
  by rewrite -RfloorE lt_succ_Rfloor.
rewrite -lte_fin -fxE => fxn.
have [approx_fun_nx0|] := f_ub_approx_fun fxn.
  by have := Hm _ mn; rewrite approx_fun_nx0.
move=> [k [/andP[k0 kn2n] ? ->]].
rewrite inE /= => -[r /=].
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

Lemma dvg_approx_fun x : D x -> f x = +oo%E ->
  ~ cvg (approx_fun^~ x : _ -> R^o).
Proof.
move=> Dx fxoo.
have approx_fun_x n : approx_fun n x = n%:R.
  rewrite /approx_fun foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo lee_pinfty.
case/cvg_ex => /= l.
have [l0|l0] := leP 0%R l.
- move=> /cvg_distP/(_ _ ltr01); rewrite near_map => -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ger0_norm // (le_trans (ceil_ge _)) //.
  by rewrite -(@gez0_abs (ceil _)) // ceil_ge0.
- move/cvg_distP => /(_ _ ltr01); rewrite near_map => -[n _].
  move=> /(_ (`|floor l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_fun_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n//.
  rewrite ler0_norm //; last by rewrite ltW.
  rewrite (@le_trans _ _ (- floor l)%:~R) //.
    by rewrite mulrNz ler_oppl opprK floor_le.
  by rewrite -(@lez0_abs (floor _)) // floor_le0 // ltW.
Qed.

Lemma ecvg_approx_fun (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> @EFin _ \o approx_fun^~x --> f x.
Proof.
move=> Dx; have := lee_pinfty (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx_fun := dvg_approx_fun Dx fxoo.
  have : {homo (approx_fun^~x) : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx_fun mn => /lefP; exact.
  move/nondecreasing_dvg_lt => /(_ dvg_approx_fun).
  by rewrite fxoo; exact/dvg_ereal_cvg.
have /EFin_real_of_extended -> : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
exact: (cvg_comp (cvg_approx_fun f0 Dx fxoo)).
Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition nnsfun_approx : (nnsfun T R)^nat := fun n => nnsfun_add
  (nnsfun_sum point
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => nnsfun_point point (Nonneg.NngNum _ (k2n_ge0 (Ordinal h)))
                                    (mA n k)
      | right _ => nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0))
     end) (n * 2 ^ n)%N)
  (nnsfun_point point (Nonneg.NngNum _ (ler0n _ n)) (mB n)).

Lemma nnsfun_approxE n : nnsfun_approx n = approx_fun n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite nnsfun_sumE; congr (_ + _).
apply: eq_bigr => i _; case: Bool.bool_dec => //.
by move/negP; rewrite ltn_ord.
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> @EFin _ \o nnsfun_approx^~x --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx_fun.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof. by move=> m n mn; rewrite !nnsfun_approxE; exact: nd_approx_fun. Qed.

Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : (nnsfun T R)^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> @EFin _ \o g^~x --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|exact: cvg_nnsfun_approx].
Qed.

End approximation.

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
have is_cvg_ag : cvg ((approx_fun D (g i))^~x).
  by apply/cvg_ex; eexists; exact: cvg_ag.
have {is_cvg_ag} := nondecreasing_cvg_le nd_ag is_cvg_ag k.
rewrite -lee_fin => /le_trans; apply.
rewrite (@EFin_real_of_extended _ (g i x)); last first.
  rewrite fin_numE andbC lt_eqF// gt_eqF//.
  by rewrite (lt_le_trans _ (g0 i Dx)) ?lte_ninfty.
by move/(cvg_lim (@Rhausdorff R)) : cvg_ag => ->.
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

Lemma ge0_integralM k : 0 <= k ->
  integral mu D (fun x => k%:E * f1 x)%E = (k%:E * integral mu D f1)%E.
Proof.
move=> k0.
have [g [nd_g gf1]] := approximation point mD mf1 f10.
pose kg := fun n => nnsfun_scale point (g n) k0.
rewrite (@nd_ge0_integral_lim _ point _ mu _ mD (fun x => k%:E * f1 x)%E _ kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu D (sfun_scale point k (g n))) //.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu D (g n))%E).
    rewrite ereal_limrM //; last first.
      by apply: is_cvg_sintegral => // x Dx m n mn; apply/(lef_at x nd_g).
    rewrite -(nd_ge0_integral_lim point mu mD f10) // => x Dx.
    exact/(lef_at x nd_g).
  by under eq_fun do rewrite (sintegralM point mu k mD).
- by move=> t Dt; rewrite mule_ge0// f10.
- move=> x Dx m n mn.
  by rewrite ler_pmul //; exact/lefP/nd_g.
- move=> x Dx.
  rewrite [X in X --> _](_ : _ = (fun n => k%:E * (g n x)%:E))%E.
    apply: ereal_cvgrM => //.
    exact: gf1.
  by rewrite funeqE.
Qed.

Lemma ge0_integralD :
  integral mu D (f1 \+ f2)%E = (integral mu D f1 + integral mu D f2)%E.
Proof.
have [g1 [nd_g1 gf1]] := approximation point mD mf1 f10.
have [g2 [nd_g2 gf2]] := approximation point mD mf2 f20.
pose g12 := fun n => nnsfun_add (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ point _ _ _ _ _ _ g12) //; last 3 first.
  - by move=> x Dx; rewrite adde_ge0 => //; [exact: f10|exact: f20].
  - by apply: nondecreasing_seqD => // x Dx;
      [exact/(lef_at x nd_g1)|exact/(lef_at x nd_g2)].
  - move=> x Dx.
    rewrite [X in X --> _](_ : _ = (fun n => (g1 n x)%:E + (g2 n x)%:E))%E.
      apply: ereal_cvgD => //; [|exact: gf1|exact: gf2].
      by apply: ge0_adde_def => //; rewrite !inE; [exact: f10|exact: f20].
    by rewrite funeqE.
rewrite (_ : _ \o _ =
    fun n => sintegral mu D (g1 n) + sintegral mu D (g2 n))%E; last first.
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

Lemma ge0_le_integral : (forall x, D x -> (f1 x <= f2 x)%E) ->
  (integral mu D f1 <= integral mu D f2)%E.
Proof.
move=> f12.
have [g1 [nd_g1 gf1]] := approximation point mD mf1 f10.
rewrite (nd_ge0_integral_lim point _ _ f10 (fun x _ => lef_at x nd_g1) gf1)//.
apply: ereal_lim_le.
  by apply: is_cvg_sintegral => // t Dt; apply/(lef_at t nd_g1).
near=> n; rewrite ge0_integralE//.
apply: ereal_sup_ub => /=; exists (g1 n) => // t Dt.
rewrite (le_trans _ (f12 _ Dt)) //.
have := gf1 _ Dt.
have := lee_pinfty (f1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite lee_pinfty.
have /EFin_real_of_extended ftE : f1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (f10 Dt))// lte_ninfty.
have := gf1 _ Dt; rewrite ftE => /ereal_cvg_real[ft_near].
set u_ := (X in X --> _) => u_f1 g1f1.
have <- : lim u_ = real_of_extended (f1 t).
  by apply/cvg_lim => //; exact: Rhausdorff.
rewrite lee_fin; apply: nondecreasing_cvg_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_g1.
by apply/cvg_ex; eexists; exact: u_f1.
Grab Existential Variables. all: end_near. Qed.

End semi_linearity.

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

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => \big[maxr/0]_(i < k) (g2' i k) t.
Local Definition max_g2 : (nnsfun T R)^nat :=
  fun k => nnsfun_bigmax point (g2^~ k) k.

Local Lemma max_g2E : max_g2 = max_g2' :> (T -> R)^nat.
Proof.
rewrite funeq2E => n t; rewrite nnsfun_bigmaxE; apply: eq_bigr => i _.
by rewrite nnsfun_approxE.
Qed.

Local Lemma nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => t; rewrite 2!nnsfun_bigmaxE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 t)) //.
  apply: le_bigmax => i _.
  have [_] := (@nondecreasing_seqP _ _ ((g2 i)^~ t)).
  apply => // a b ab; rewrite !nnsfun_approxE.
  exact/lefP/(nd_approx_fun D (g i) ab).
rewrite (bigmaxD1 ord_max) // le_maxr; apply/orP; right.
rewrite [X in _ <= X](eq_bigl (fun i => nat_of_ord i < n)%N); last first.
  move=> i /=; rewrite neq_lt /= (ltNge n i); apply/orP/idP => [[//|]|].
    by rewrite -ltNge => /(leq_trans (ltn_ord i)); rewrite ltnn.
  by left.
by rewrite (big_ord_narrow (leqnSn n)).
Qed.

Let is_cvg_max_g2 t : cvg (fun k => (max_g2 k t)%:E).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Lemma max_g2_g k x : D x -> ((max_g2 k x)%:E <= g k x)%O.
Proof.
move=> Dx; rewrite nnsfun_bigmaxE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x))%E; last first.
  by apply/bigmax_lerP; split => //; apply: g0.
rewrite (@big_morph _ _ (@EFin R) 0%:E maxe) //; last first.
  by move=> a b; rewrite maxEFin.
apply: le_bigmax => i _.
rewrite nnsfun_approxE /= (le_trans (le_approx_fun _ _ _)) //.
by apply: nd_g => //; exact/ltnW.
Qed.

Lemma cvg_max_g2_f : forall t, D t -> @EFin _ \o (max_g2^~t) --> f t.
Proof.
have max_g2_g t : D t -> (lim (fun n => (max_g2 n t)%:E) <= lim (g^~ t))%E.
  move=> Dt; apply: lee_lim => //.
    exact: is_cvg_g.
  by near=> n; move: t Dt; exact/max_g2_g.
have g2_max_g2 t n :
    (lim (fun k => (g2 n k t)%:E) <= lim (fun k => (max_g2 k t)%:E))%E.
  apply: lee_lim => //.
    apply: ereal_nondecreasing_is_cvg => a b ab.
    by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx_fun.
  near=> k; rewrite nnsfun_bigmaxE lee_fin.
  have nk : (n < k)%N by near: k; exists n.+1.
  exact: (@bigmax_sup _ _ _ (Ordinal nk)).
move=> t Dt.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (max_g2_g _ Dt)) // (cvg_lim _ g_l).
rewrite /f.
have := lee_pinfty l; rewrite le_eqVlt => /predU1P[->|loo].
  by rewrite lee_pinfty.
rewrite -(cvg_lim _ g_l) //= ereal_lim_le => //.
  exact/is_cvg_g.
near=> n.
have := lee_pinfty (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
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
   have ->// : (fun k => (g2 n k t)%:E) = @EFin R \o (approx_fun D (g n))^~ t.
  by under eq_fun do rewrite nnsfun_approxE.
Grab Existential Variables. all: end_near. Qed.

Lemma monotone_convergence :
  integral mu D f = lim (fun n => integral mu D (g n)).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => integral mu D (g n)).
    move=> m n mn; apply: ge0_le_integral => //.
     by move=> x Dx; exact: g0.
     by move=> x Dx; exact: g0.
     by move=> x Dx; exact: nd_g.
  have ub n : (integral mu D (g n) <= integral mu D f)%E.
    apply: ge0_le_integral => //.
    - by move=> x Dx; exact: g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      by apply: nearW => k; apply/g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      near=> m.
      have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: ereal_lim_le => //;[exact: ereal_nondecreasing_is_cvg|exact: nearW].
rewrite (@nd_ge0_integral_lim _ point _ mu _ _ _ _ max_g2) //; last 3 first.
  - move=> t Dt; apply: ereal_lim_ge => //; first exact/is_cvg_g.
    by apply: nearW => n; apply: g0.
  - by move=> t Dt m n mn; apply/lefP/nd_max_g2.
  - by move=> x Dx; exact: cvg_max_g2_f.
apply: lee_lim.
- apply: is_cvg_sintegral => //.
    by move=> t Dt m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvg => // n m nm; apply: ge0_le_integral => //.
  + by move=> *; apply: g0.
  + by move=> *; apply: g0.
  + by move=> *; apply/nd_g.
- apply: nearW => n.
  rewrite ge0_integralE//; last by move=> *; apply: g0.
  by apply: ereal_sup_ub; exists (max_g2 n) => // t; exact: max_g2_g.
Grab Existential Variables. all: end_near. Qed.

End monotone_convergence_theorem.

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
have mg :=  measurable_fun_ereal_inf mf.
have g0 n : forall x, D x -> (0 <= g n x)%E.
  by move=> x Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
rewrite (monotone_convergence point) //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/nondecreasing_ereal_cvg => a b ab.
  apply: (ge0_le_integral point) => //.
  - exact: g0.
  - exact: g0.
  - move=> x Dx.
    apply: le_ereal_inf => _ [n /= bn <-].
    by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/nondecreasing_ereal_cvg => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N -> (integral mu D (g n) <=
    ereal_inf [set integral mu D (f k) | k in [set p | n <= p]%N])%E.
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: (ge0_le_integral point); [exact: mD|exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lb; exists k.
  exact.
Qed.

End fatou.

(* TODO: move to ereal.v *)
Lemma lee_norm_add (R : realDomainType) (x y : \bar R) :
  (norme (x + y) <= norme x + norme y)%E.
Proof.
move: x y => [x| |] [y| |] //.
by rewrite /norme /= -addEFin lee_fin ler_norm_add.
Qed.

Lemma gee0_norm (R : realDomainType) (x : \bar R) : (0 <= x)%E -> norme x = x.
Proof.
move: x => [x| |] //; rewrite lee_fin => x0; apply/eqP.
by rewrite eqe ger0_norm.
Qed.

Lemma ge0_fin_numE (R : realDomainType) (x : \bar R) :
  (0 <= x)%E -> (x \is a fin_num) = (x < +oo)%E.
Proof.
by move: x => [x| |] => // x0; rewrite fin_numE -lee_pinfty_eq -ltNge andbb.
Qed.

Lemma lte_mul_pinfty (R' : realDomainType) x (y : \bar R') :
  (0 <= x)%R -> (y < +oo)%E -> (x%:E * y < +oo)%E.
Proof.
move: y => [y| |] // x0 _; first by rewrite -mulEFin lte_pinfty.
rewrite mulrinfty; move: x0; rewrite le_eqVlt => /predU1P[<-|x0].
- by rewrite sgr0 mul0e lte_pinfty.
- by rewrite gtr0_sg // mul1e.
Qed.

Lemma sube_eq (R : numDomainType) (x y z : \bar R) : x \is a fin_num ->
  (y +? z)%E -> (x - z == y)%E = (x == y + z)%E.
Proof.
by move: x y z => [x| |] [y| |] [z| |] // _ _; rewrite !eqe subr_eq.
Qed.
(* /TODO: move to ereal.v *)

Section integrable.
Variables (T : measurableType) (point : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Definition integrable (D : set T) (f : T -> \bar R) :=
  measurable_fun D f /\
  (integral mu D (fun x => norme (f x)) < +oo)%E.

Definition Rintegral (D : set T) (f : T -> \bar R) :=
  real_of_extended (integral mu D f).

Lemma le_integrable (D : set T) (f1 f2 : T -> \bar R) :
  measurable D -> measurable_fun D f1 ->
  (forall x, D x -> norme (f1 x) <= norme (f2 x))%E ->
  integrable D f2 -> integrable D f1.
Proof.
move=> mD mf1 f1f2 [mf2 f2oo]; split => //; rewrite (le_lt_trans _ f2oo) //.
apply: ge0_le_integral => //.
- by move=> t Dt; exact: norme_ge0.
- by apply: measurable_fun_comp => //; exact: measurable_fun_norme.
- by move=> t Dt; exact: norme_ge0.
Qed.

Lemma integrableD (f1 f2 : T -> R) : measurable (@setT T) ->
  integrable setT (@EFin _ \o f1) -> integrable setT (@EFin _ \o f2) ->
  integrable setT (fun x => (f1 x)%:E + (f2 x)%:E)%E.
Proof.
move=> mD [mf1 f1oo] [mf2 f2oo].
split.
  apply: measurable_fun_comp; first exact: measurable_fun_EFin.
  by rewrite -/(f1 \+ f2); apply: measurable_funD => //; exact: EFin_measurable_fun.
apply: (@le_lt_trans _ _ (integral mu setT (fun x => norme (f1 x)%:E + norme (f2 x)%:E)%E)).
  apply ge0_le_integral => //.
  - by move=> t _; apply: norme_ge0.
  - apply: measurable_fun_comp; first exact: measurable_fun_norme.
    apply: measurable_fun_comp; first exact: measurable_fun_EFin.
    by apply: measurable_funD; exact: EFin_measurable_fun.
  - by move=> x _; apply: adde_ge0; rewrite lee_fin.
  - by move=> x _; exact: lee_norm_add.
rewrite ge0_integralD //.
- exact: lte_add_pinfty.
- by move=> x _; exact: norme_ge0.
- by apply: measurable_fun_comp => //; exact: measurable_fun_norme.
- by move=> x _; exact: norme_ge0.
- by apply: measurable_fun_comp => //; exact: measurable_fun_norme.
Qed.

End integrable.

(* TODO: move *)
Lemma ge0_integralB (R : realType) (T : measurableType) (point : T)
  (mu : {measure set T -> \bar R}) (D : set T := setT) (f1 f2 : T -> R) :
  measurable D -> measurable_fun D f1 -> measurable_fun D f2 ->
  (forall t, D t -> (0 <= f1 t - f2 t)%R) ->
  (forall t, D t -> (0 <= f2 t)%R) ->
  integral mu D (@EFin _ \o f1) \is a fin_num ->
  integral mu D (@EFin _ \o f2) \is a fin_num ->
  integral mu D (fun x => (f1 x)%:E - (f2 x)%:E)%E =
    (integral mu D (@EFin _ \o f1) - integral mu D (@EFin _ \o f2))%E.
Proof.
move=> mD mf1 mf2 f120 f20 f1fin_num f2fin_num.
apply/esym/eqP; rewrite sube_eq; [|exact: f1fin_num|exact: fin_num_adde_def].
rewrite -ge0_integralD //.
+ apply/eqP; congr (integral _ _).
  by rewrite funeqE => t /=; by rewrite -addEFin subrK.
+ apply: measurable_fun_comp; first exact: measurable_fun_EFin.
  apply: measurable_funD => //; first exact: measurable_funN.
- by apply: measurable_fun_comp => //; exact: measurable_fun_EFin.
Qed.

Lemma continuous_is_cvg {T : Type} {V U : topologicalType} [F : set (set T)]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma lim_ereal_inf_EFin (T : Type) (R : realType) (f : (T -> R)^nat) :
  (forall t, cvg (f^~t : _ -> R^o)) ->
  (fun t => lim_ereal_inf (@EFin _ \o f^~t)) = (fun t => (lim (f^~t))%:E).
Proof.
move=> cf; rewrite funeqE => t.
rewrite -EFin_lim //; apply/eqP.
rewrite is_cvg_lim_ereal_infE //.
apply: continuous_is_cvg; last exact: cf.
by move=> l ftl.
Qed.

Lemma esqueeze0 (R : realType) T (f g : T -> \bar R) (a : filter_on T) :
  (\forall x \near a, 0 <= f x <= g x)%E -> g @ a --> 0%E -> f @ a --> 0%E.
Proof.
move=> fg /cvg_ballP lga; apply/cvg_ballP => _/posnumP[e].
rewrite near_map.
near=> n; have : ball 0%E e%:num (g n).
  by near: n; have := lga _ (posnum_gt0 e); rewrite near_simpl.
rewrite /ball /= /ereal_ball /= mul0r 2!sub0r !normrN ger0_norm; last first.
  rewrite -contract0 le_contract.
  by near: n; apply: filterS fg => t /andP[f0]; apply: le_trans.
rewrite ger0_norm; last first.
  by rewrite -contract0 le_contract; near: n; apply: filterS fg => t /andP[].
apply: le_lt_trans; rewrite le_contract //.
by near: n; apply: filterS fg => t /andP[].
Grab Existential Variables. all: end_near. Qed.

Lemma lim_ereal_inf_shift (R : realType) (u : (\bar R)^nat) (k : \bar R) :
  k \is a fin_num ->
  lim_ereal_inf (fun x => k + u x)%E = (k + lim_ereal_inf u)%E.
Proof.
move=> kfin_num; apply/cvg_lim => //.
apply: cvg_trans; last first.
  apply: (@ereal_cvgD _ (cst k) (einfs u) k (lim (einfs u))).
  - by rewrite adde_defC fin_num_adde_def.
  - exact: cvg_cst.
  - exact: is_cvg_einfs.
suff : (einfs (fun n => k + u n) = (fun n => k + einfs u n))%E by move=> ->.
rewrite funeqE => n.
rewrite /einfs /=; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite addeC -lee_subl_addr_new//; apply: lb_ereal_inf => /= _ [m /= mn] <-.
  rewrite lee_subl_addr_new//; apply: ereal_inf_lb.
  by exists m => //; rewrite addeC.
- apply: lb_ereal_inf => /= _ [m /= mn] <-.
  by rewrite lee_add2l//; apply: ereal_inf_lb; exists m => /=.
Qed.

Lemma lim_ereal_sup_le0_cvg0 (R : realType) (u : (\bar R)^nat) :
  (lim_ereal_sup u <= 0)%E -> (forall n, 0 <= u n)%E -> u --> 0%E.
Proof.
move=> supu0 u0.
have usupu n : (0 <= u n <= esups u n)%E.
  by rewrite u0 /=; apply/ereal_sup_ub; exists n => /=.
have : esups u --> 0%E.
  have /cvg_ex[l esupl] : cvg (esups u) by exact: is_cvg_esups.
  have <- : lim_ereal_sup u = 0%E.
    apply/eqP; rewrite eq_le supu0; apply: (ereal_lim_ge (@is_cvg_esups _ _)).
    apply: nearW => m.
    have /le_trans : (0 <= einfs u m)%E.
      by apply: lb_ereal_inf => _ [p /= pm] <-; exact: u0.
    apply; apply: ereal_inf_sup_sdrop.
  move: (esupl) => /cvg_lim => /(_ (@ereal_hausdorff R)).
  by rewrite /lim_ereal_sup => ->.
by apply: esqueeze0; rewrite near_simpl; exact: nearW.
Qed.
(* /TODO: move *)

(* NB* this is work in progress *)
Section dominated_convergence_theorem.
Variables (T : measurableType) (point : T) (R : realType).
Variables mu : {measure set T -> \bar R}.
Let D : set T := setT.
Variable f_ : (T -> R)^nat.
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Variable f : T -> R.
Hypothesis f_f : (*{ae mu,*) forall x, f_^~x --> f x(*}*).
Variable g : T -> R.
Hypothesis ig : integrable mu D (fun x => (g x)%:E).
Hypothesis normfg : forall n, (*{ae mu,*) forall x, D x -> `|f_ n x| <= g x(*}*).

Let g0 : forall x, D x -> 0 <= g x.
Proof. by move=> x Dx; rewrite (le_trans _ (@normfg O _ Dx)). Qed.

Lemma dominated_integrable : integrable mu D (@EFin _ \o f).
Proof.
split.
  apply: measurable_fun_comp; first exact: measurable_fun_EFin.
  exact: (measurable_fun_cvg mf_).
have fg x : D x -> `| f x | <= g x.
  move=> Dx.
  have : (`|f_ n x|) @[n --> \oo] --> `|f x|.
    by apply: (@cvg_norm _ [normedModType R of R^o]); exact: f_f.
  move=> /(@cvg_lim _) <- //; last exact: Rhausdorff.
  apply: lim_le => //.
    apply: (@is_cvg_norm _ [normedModType R of R^o]).
    by apply/cvg_ex; eexists; exact: f_f.
  by apply: nearW => n; apply: normfg.
move: ig => [mg].
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurableT.
- by move=> x Dx; apply: norme_ge0.
- apply: measurable_fun_comp; first exact: measurable_fun_norme.
  apply: measurable_fun_comp; first exact: measurable_fun_EFin.
  exact: (measurable_fun_cvg mf_).
- by move=> x Dx; exact: norme_ge0.
- by move=> x Dx /=; rewrite lee_fin (ger0_norm (g0 Dx)); exact: fg.
Qed.

Let g_ n x := `|f_ n x - f x|.

Let cvg_g_ x : (g_^~x : _ -> R^o) --> (0 : R^o).
Proof.
apply/cvg_distP => _/posnumP[e]; rewrite near_map.
have /(@cvg_distP _ [pseudoMetricNormedZmodType R of R^o]) := (@f_f x).
move/(_ e%:num (posnum_gt0 e)) => [k _ h].
near=> m; rewrite distrC /g_ subr0 distrC normr_id; apply: h.
by near: m; exists k.
Grab Existential Variables. all: end_near. Qed.

Let gg_ n x : D x -> 0 <= 2 * g x - g_ n x.
Proof.
move=> Dx; rewrite subr_ge0 mulr_natl mulr2n /g_.
rewrite (le_trans (ler_norm_sub _ _))// ler_add// ?normfg//.
have f_fx : (`|f_ n x|) @[n --> \oo] --> (`|f x| : R^o).
  by apply: (@cvg_norm _ [normedModType R of R^o]); exact: f_f.
move/(@cvg_lim [topologicalType of R^o]) : (f_fx) => <-//.
apply: lim_le.
  by apply/cvg_ex; eexists; exact: f_fx.
by apply: nearW => k; apply: normfg.
Qed.

Let mgg n : measurable_fun setT (fun x : T => (2 * g x - g_ n x)%:E).
Proof.
apply: measurable_fun_comp; first exact: measurable_fun_EFin.
apply: measurable_funD.
  by apply: measurable_funK; case: ig => + _; exact: EFin_measurable_fun.
apply/measurable_funN/measurable_fun_comp; first exact: measurable_fun_normr.
apply: measurable_funD => //; apply: measurable_funN.
exact: (measurable_fun_cvg mf_).
Qed.

Local Open Scope ereal_scope.

Let gg_ge0 n x : D x -> 0 <= (2 * g x - g_ n x)%:E.
Proof. by move=> Dx; rewrite lee_fin gg_. Qed.

Lemma dominated : lim (fun n => integral mu D (@EFin _ \o g_ n)) = 0.
Proof.
have := fatou point mu mgg gg_ge0.
rewrite [X in X <= _ -> _](_ : _ =
    integral mu D (fun x => (2 * g x)%:E)); last first.
  rewrite lim_ereal_inf_EFin /=; last first.
    move=> t; apply: is_cvgB; first exact: is_cvg_cst.
    by apply/cvg_ex; eexists; exact: cvg_g_.
  congr (integral mu _ _); rewrite funeqE => t; congr (_%:E).
  rewrite -[fun _ => _]/(cst (2 * g t)%R \- (g_^~t)).
  rewrite (@limB _ [normedModType R of R^o]); [|exact: is_cvg_cst|].
  - rewrite lim_cst // (_ : lim _ = 0%R) ?subr0//.
    by apply/cvg_lim => //; exact: cvg_g_.
  - by apply/cvg_ex; eexists; apply/cvg_g_.
have i2g : integral mu D (@EFin _ \o (fun x => (2 * g x)%R)) < +oo.
  rewrite /comp /=; under eq_fun do rewrite mulEFin.
  rewrite ge0_integralM//; [|exact: measurableT|by case: ig].
  rewrite lte_mul_pinfty//; case: ig => _.
  rewrite (_ : (fun x : T => _) = (fun x => (g x)%:E)) //.
  by rewrite funeqE => t; rewrite gee0_norm // lee_fin g0.
rewrite [X in _ <= X -> _](_ : _ = integral mu setT (fun x => (2 * g x)%:E) + -
    lim_ereal_sup (fun n => integral mu setT (@EFin _ \o g_ n))); last first.
  rewrite (_ : (fun n => _) = (fun n => integral mu setT (fun x => (2 * g x)%:E) +
      integral mu setT (fun x => (- g_ n x)%:E)))%E; last first.
    rewrite funeqE => n; under eq_fun do rewrite subEFin.
    rewrite ge0_integralB //.
    - rewrite [X in _ = _ + X](_ : _ = (- integral mu D (@EFin _ \o g_ n))) //.
      by rewrite -ge0_integralN// => t Dt; rewrite lee_fin.
    - exact: measurableT.
    - by apply: measurable_funK; case: ig => + _; exact: EFin_measurable_fun.
    - apply: measurable_fun_comp; first exact: measurable_fun_normr.
      by apply: measurable_funB => //; exact: (measurable_fun_cvg mf_).
    - by move=> t Dt; rewrite -lee_fin gg_ge0.
    - by move=> t Dt; rewrite /g_ normr_ge0.
    - rewrite ge0_fin_numE//.
      by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
    - suff : integrable mu D (@EFin _ \o g_ n).
        case=> _ g_oo; rewrite ge0_fin_numE; last first.
          by rewrite ge0_integral// => x Dx; rewrite lee_fin /g_ normr_ge0.
        move: g_oo; rewrite (_ : (fun x : T => _) = (fun x => (g_ n x)%:E)) //.
        by rewrite funeqE => x /=; rewrite ger0_norm.
      have integrable_normfn : integrable mu D (fun x => `|f_ n x|%:E).
        apply: le_integrable ig => //.
        - exact: measurableT.
        - apply: measurable_fun_comp; first exact: measurable_fun_EFin.
          by apply: measurable_fun_comp => //; exact: measurable_fun_normr.
        - move=> x Dx; rewrite lee_fin normr_id.
          by rewrite (le_trans (normfg _ Dx))// ler_norm.
      suff : integrable mu D (fun x : T => `|f_ n x|%:E + `|f x|%:E)%E.
        apply: le_integrable => //.
        - exact: measurableT.
          apply: measurable_fun_comp; first exact: measurable_fun_EFin.
          apply: measurable_fun_comp; first exact: measurable_fun_normr.
          by apply: measurable_funB => //; exact: (measurable_fun_cvg mf_).
        - move=> x Dx; rewrite lee_fin normr_id.
          by rewrite (le_trans (ler_norm_sub _ _))// ler_norm.
      apply: integrableD; [by []|exact: measurableT|by []|].
      apply: le_integrable dominated_integrable => //; first exact: measurableT.
      - apply: measurable_fun_comp; first exact: measurable_fun_EFin.
        apply: measurable_fun_comp; first exact: measurable_fun_normr.
        exact: (measurable_fun_cvg mf_).
      - by move=> x Dx; rewrite /= lee_fin normr_id.
  rewrite lim_ereal_inf_shift; last first.
    rewrite ge0_fin_numE//.
    by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
  rewrite -lim_ereal_infN; congr (_ + lim_ereal_inf _)%E.
  rewrite funeqE => n /=.
  by rewrite -ge0_integralN // => x Dx; rewrite lee_fin /g_.
rewrite addeC -lee_subl_addr_new; last first.
  rewrite ge0_fin_numE//.
  by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
rewrite subee; last first.
  rewrite ge0_fin_numE//.
  by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
rewrite lee_oppr oppe0 => lim_ge0.
apply/cvg_lim/lim_ereal_sup_le0_cvg0 => // n.
rewrite ge0_integralE //.
  by apply: nnintegral_ge0 => // x Dx; rewrite lee_fin.
by move=> *; rewrite lee_fin.
Qed.

End dominated_convergence_theorem.
