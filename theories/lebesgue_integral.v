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
(* convergence theorem, and Fatou's lemma. Finally, it proves the linearity   *)
(* property of the integral and the dominated convergence theorem.            *)
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
(*          img_idx f x == the index of the image f x in the range of the     *)
(*                         simple function f, this index has type 'I_(ssize f)*)
(*             sfun_cst == constant simple functions                          *)
(*           sfun_scale == scaling of simple functions                        *)
(*       sfun_proj f mA == restriction of the simple function f to the domain *)
(*                         A, and 0 elsewhere; mA is a proof that A is        *)
(*                         measurable                                         *)
(*        sfun_ind r mA == the indicator function that is r over the          *)
(*                         measurable set A and 0 elsewere; mA is a proof     *)
(*                         that A is measurable                               *)
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
(*       integrable D f == f is measurable over D and the integral of f       *)
(*                         w.r.t. D is < +oo                                  *)
(*         xsection A x == with A : set (T1 * T2) and x : T1 is the x-section *)
(*                         of A                                               *)
(*         ysection A y == with A : set (T1 * T2) and y : T2 is the y-section *)
(*                         of A                                               *)
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

Lemma continuous_is_cvg {T : Type} {V U : topologicalType} [F : set (set T)]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma mulrEBr (R : realDomainType) (r : R) (y z : \bar R) :
  (y +? (- z))%E -> (r%:E * (y - z))%E = (r%:E * y - r%:E * z)%E.
Proof. by move=> yz; rewrite mulrEDr ?muleN. Qed.

Lemma eqe_absl (R : realDomainType) (x y : \bar R) :
  ((`|x| == y) = ((x == y) || (x == - y)) && (0 <= y))%E.
Proof.
move: x y => [x| |] [y| |] //=; rewrite? lee_pinfty//.
by rewrite !eqe eqr_norml lee_fin.
Qed.

(* PR in progress *)
Lemma fin_numElt (R : realDomainType) (x : \bar R) :
  (x \is a fin_num) = (-oo < x < +oo)%E.
Proof. by rewrite fin_numE -lee_pinfty_eq -lee_ninfty_eq -2!ltNge. Qed.

Lemma fin_numPlt (R : realDomainType) (x : \bar R) :
  reflect (-oo < x < +oo)%E (x \is a fin_num).
Proof. by rewrite fin_numElt; exact: idP. Qed.

Lemma ereal_squeeze (R : realType) (f g h : (\bar R)^nat) :
  (\forall x \near \oo, (f x <= g x <= h x)%E) -> forall (l : \bar R),
  f --> l -> h --> l -> g --> l.
Proof.
move=> [p _ pfgh] [l| |] fl hl.
- move: fl hl => /ereal_cvg_real[ffin fl] /ereal_cvg_real[hfin hl].
  have {ffin hfin}[[m _ mf] [k _ kh]] := (ffin, hfin).
  apply/ereal_cvg_real; split.
    near=> n; have : (n >= maxn (maxn m k) p)%N.
      by near: n; exists (maxn (maxn m k) p).
    rewrite 2!geq_max -andbA => /and3P[mn kn pn].
    have := mf _ mn; rewrite !fin_numElt => /andP[oofn fnoo].
    have := kh _ kn; rewrite !fin_numElt => /andP[oohn hnoo].
    have := pfgh _ pn => /andP[fg gh].
    by rewrite (lt_le_trans oofn)//= (le_lt_trans gh).
  apply (@squeeze _ _ (fine \o f) _ (fine \o h) eventually_filterType) => //=.
  near=> n; have : (n >= maxn (maxn m k) p)%N.
    by near: n; exists (maxn (maxn m k) p).
  rewrite 2!geq_max -andbA => /and3P[mn kn pn].
  have [[ffin hfin] /andP[fg gh]] := (mf _ mn, kh _ kn, pfgh _ pn).
  rewrite -!lee_fin (fineK ffin) (fineK hfin) fineK// ?fg ?gh//.
  move: ffin; rewrite !fin_numElt => /andP[oofn fnoo].
  move: hfin; rewrite !fin_numElt => /andP[oohn hnoo].
  by rewrite (lt_le_trans oofn)//= (le_lt_trans gh).
- apply/ereal_cvgPpinfty => M M0.
  move/ereal_cvgPpinfty : fl => /(_ _ M0)[m _  Mf].
  near=> k; have : (k >= maxn p m)%N by near: k; exists (maxn p m).
  rewrite geq_max => /andP[pk km].
  have := Mf _ km => /le_trans; apply.
  by have /andP[] := pfgh _ pk.
- apply/ereal_cvgPninfty => M M0.
  move/ereal_cvgPninfty : hl => /(_ _ M0)[m _  Mh].
  near=> k; have : (k >= maxn p m)%N by near: k; exists (maxn p m).
  rewrite geq_max => /andP[pk km].
  have := Mh _ km; apply: le_trans.
  by have /andP[] := pfgh _ pk.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_sub0 (R : realFieldType) (f : (\bar R)^nat) (k : \bar R) :
  k \is a fin_num ->
  (fun x => f x - k)%E --> 0%E -> f --> k.
Proof.
move=> kfin fk.
have /ereal_cvgD/(_ fk) : (0%E +? k)%E by rewrite adde_defC fin_num_adde_def.
rewrite add0e /= => /(_ (cst k)).
rewrite [X in (_ -> X --> _) -> _](_ : _ = f); last first.
  by rewrite funeqE => x; rewrite subeK.
by apply => //; exact: cvg_cst.
Qed.

Lemma cvg_abse (R : realFieldType) (f : (\bar R)^nat) :
  (abse \o f) --> 0%E -> f --> 0%E.
Proof.
move=> /cvg_ballP f0; apply/cvg_ballP => _/posnumP[e].
have := f0 _ (posnum_gt0 e); rewrite !near_map => -[n _ {}f0].
near=> m; have /f0 : (n <= m)%N by near: m; exists n.
rewrite /ball /= /ereal_ball !contract0 !sub0r !normrN; apply: le_lt_trans.
have [fm0|fm0] := leP 0%E (f m); first by rewrite gee0_abs.
by rewrite (lte0_abs fm0) contractN normrN.
Grab Existential Variables. all: end_near. Qed.
(* /PR in progress *)

(* PR in progress *)
Lemma setM_bigcupr T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  A `*` \bigcup_(i in P) F i = \bigcup_(i in P) (A `*` F i).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [/= Ax [n Pn Fny]]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma setM_bigcupl T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  \bigcup_(i in P) F i `*` A = \bigcup_(i in P) (F i `*` A).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [[n Pn Fnx] Ax]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma setMS T1 T2 (C : set T1) (A B : set T2) : A `<=` B -> C `*` A `<=` C `*` B.
Proof. by move=> AB [x y] [/= Cx Ay]; split => //; exact: AB. Qed.

Lemma setSM T1 T2 (C : set T1) (A B : set T2) : A `<=` B -> A `*` C `<=` B `*` C.
Proof. by move=> AB [x y] [/= Cx Ay]; split => //; exact: AB. Qed.
(* /PR in progress *)

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

Lemma in_set0 T (x : T) : (x \in set0) = false.
Proof. by have [|//] := boolP (x \in set0); rewrite in_setE. Qed.

Lemma in_setT T (x : T) : (x \in setT) = true.
Proof.
by have [//|] := boolP (x \in setT); rewrite notin_setE => /(_ Logic.I).
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

Lemma EFin_lim (R : realType) (f : nat -> R) : cvg f ->
  lim (EFin \o f) = (lim f)%:E.
Proof.
move=> cf; apply: cvg_lim => //.
move/cvg_ex : cf => [l fl].
apply: (@cvg_comp _ _ _ _ EFin _ _ _ fl); rewrite (cvg_lim _ fl) //.
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

(* TODO: move near ge0_adde_def *)
Lemma ltpinfty_adde_def (R : numDomainType) :
  {in [pred x | (x < +oo)%E] &, forall x y : \bar R, (x +? y)%E}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma adde_defN (R : numDomainType) (x y : \bar R) :
  (x +? - y)%E = (- x +? y)%E.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_defEninfty (R : numDomainType) (x : \bar R) :
  ((x +? -oo) = (x != +oo))%E.
Proof. by case: x. Qed.

Lemma adde_defEpinfty (R : numDomainType) (x : \bar R) :
  ((x +? +oo) = (x != -oo))%E.
Proof. by case: x. Qed.

Lemma lte_pinfty_eq (R : realDomainType) (x : \bar R) :
  ((x < +oo) = ((x \is a fin_num) || (x == -oo)))%E.
Proof. by case: x => // x //=; exact: lte_pinfty. Qed.

Lemma gte_ninfty_eq (R : realDomainType) (x : \bar R) :
  ((-oo < x) = ((x \is a fin_num) || (x == +oo)))%E.
Proof. by case: x => // x //=; exact: lte_pinfty. Qed.

Lemma ge0_fin_numE (R : realDomainType) (x : \bar R) :
  (0 <= x)%E -> (x \is a fin_num) = (x < +oo)%E.
Proof.
by move: x => [x| |] => // x0; rewrite fin_numElt lte_ninfty.
Qed.

(* NB: lte_add_pinfty *)
Lemma lte_mul_pinfty (R : realDomainType) (x y : \bar R) :
  (0 <= x)%E -> x \is a fin_num -> (y < +oo)%E -> (x * y < +oo)%E.
Proof.
move: x y => [x| |] [y| |] // x0 xfin _; first by rewrite -mulEFin lte_pinfty.
rewrite mulrinfty; move: x0; rewrite lee_fin le_eqVlt => /predU1P[<-|x0].
- by rewrite sgr0 mul0e lte_pinfty.
- by rewrite gtr0_sg // mul1e.
Qed.

Lemma lt0R (R : numDomainType) (x : \bar R) :
  (0 < x < +oo)%E -> (0 < fine x)%R.
Proof.
by move: x => [x| |] //=; rewrite ?ltxx ?andbF// lte_fin => /andP[].
Qed.

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
Implicit Types (f : T -> \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma funenng_ge0 f x : 0 <= f^\+ x.
Proof. by rewrite /funenng /= le_maxr lexx orbT. Qed.

Lemma funennp_ge0 f x : 0 <= f^\- x.
Proof. by rewrite /funennp le_maxr lexx orbT. Qed.

Lemma funenngN f : (fun x => - f x)^\+ = f^\-.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp. Qed.

Lemma funennpN f : (fun x => - f x)^\- = f^\+.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp oppeK. Qed.

Lemma ge0_funenngE f : (forall x, D x -> 0 <= f x) -> {in D, f^\+ =1 f}.
Proof. by move=> f0 x ?; apply/max_idPl/f0; rewrite -in_setE. Qed.

Lemma ge0_funennpE f : (forall x, D x -> 0 <= f x) -> {in D, f^\- =1 cst 0}.
Proof.
by move=> f0 x ?; apply/max_idPr; rewrite lee_oppl oppe0 f0// -in_setE.
Qed.

Lemma le0_funenngE f : (forall x, D x -> f x <= 0) -> {in D, f^\+ =1 cst 0}.
Proof. by move=> f0 x ?; apply/max_idPr/f0; rewrite -in_setE. Qed.

Lemma le0_funennpE f :
  (forall x, D x -> f x <= 0) -> {in D, f^\- =1 (fun x => - f x)}.
Proof.
by move=> f0 x ?; apply/max_idPl; rewrite lee_oppr oppe0 f0// -in_setE.
Qed.

Lemma gt0_funenngM r f : (0 < r)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => r%:E * (f^\+ x)).
Proof. by move=> ?; rewrite funeqE => x; rewrite /funenng maxeMr// mule0. Qed.

Lemma gt0_funennpM r f : (0 < r)%R ->
  (fun x => r%:E * f x)^\- = (fun x => r%:E * (f^\- x)).
Proof.
by move=> r0; rewrite funeqE => x; rewrite /funennp -muleN maxeMr// mule0.
Qed.

Lemma lt0_funenngM r f : (r < 0)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => - r%:E * (f^\- x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite NEFin mulNe.
by rewrite funenngN gt0_funennpM -1?ltr_oppr ?oppr0.
Qed.

Lemma lt0_funennpM r f : (r < 0)%R ->
  (fun x => r%:E * f x)^\- = (fun x => - r%:E * (f^\+ x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite NEFin mulNe.
by rewrite funennpN gt0_funenngM -1?ltr_oppr ?oppr0.
Qed.

Lemma fune_abse f : abse \o f = f^\+ \+ f^\-.
Proof.
rewrite funeqE => x /=; have [fx0|/ltW fx0] := leP (f x) 0.
- rewrite lee0_abs// /funenng /funennp.
  move/max_idPr : (fx0) => ->; rewrite add0e.
  by move: fx0; rewrite -{1}oppr0 NEFin lee_oppr => /max_idPl ->.
- rewrite gee0_abs// /funenng /funennp.
  move/max_idPl : (fx0) => ->.
  by move: fx0; rewrite -{1}oppr0 NEFin lee_oppl => /max_idPr ->; rewrite adde0.
Qed.

Lemma funenngnnp f : f = (fun x => f^\+ x - f^\- x)%E.
Proof.
rewrite funeqE => x; rewrite /funenng /funennp.
have [|/ltW] := leP (f x) 0%E.
  by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite oppeK add0e.
by rewrite -{1}oppe0 -lee_oppl => /max_idPr ->; rewrite sube0.
Qed.

Lemma add_def_funennpg f x : (f^\+ x +? - f^\- x)%E.
Proof.
rewrite /funennp /funenng; case: (f x) => [r| |].
- by rewrite !maxEFin.
- by rewrite /maxe /= lte_ninfty.
- by rewrite /maxe /= lte_ninfty.
Qed.

Lemma funeD_Dnng f g : (f \+ g) =1 (fun x => (f \+ g)^\+ x - (f \+ g)^\- x).
Proof.
move=> x; rewrite /funenng /funennp.
have [|/ltW] := leP 0 (f x + g x).
- by rewrite -{1}oppe0 -lee_oppl => /max_idPr ->; rewrite sube0.
- by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite oppeK add0e.
Qed.

Lemma funeD_nngD f g : (f \+ g) =1 (fun x => (f^\+ \+ g^\+) x - (f^\- \+ g^\-) x).
Proof.
move=> x; rewrite /funenng /funennp.
have [|fx0] := leP 0 (f x); last rewrite add0e.
- rewrite -{1}oppe0 lee_oppl => /max_idPr ->; have [|/ltW] := leP 0 (g x).
    by rewrite -{1}oppe0 lee_oppl => /max_idPr ->; rewrite adde0 sube0.
  by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite adde0 sub0e oppeK.
- move/ltW : (fx0); rewrite -{1}oppe0 lee_oppr => /max_idPl ->.
  have [|] := leP 0 (g x); last rewrite add0e.
    by rewrite -{1}oppe0 lee_oppl => /max_idPr ->; rewrite adde0 oppeK addeC.
  move gg' : (g x) => g'; move: g' gg' => [g' gg' g'0|//|goo _].
  + move/ltW : (g'0); rewrite -{1}oppe0 -lee_oppr => /max_idPl => ->.
    by rewrite oppeD// 2!oppeK.
  + by rewrite /maxe /=; case: (f x) fx0.
Qed.

End funpos_lemmas.
(*Hint Extern 0 (0 <= _ ^\+ _)%E => solve [apply: funennp_ge0] : core.
Hint Extern 0 (0 <= _ ^\+ _)%E => solve [apply: funenng_ge0] : core.*)

Section funpos_measurable.
Variables (T : measurableType) (R : realType).

Lemma emeasurable_fun_funenng (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D f^\+.
Proof.
by move=> mD mf; apply: emeasurable_fun_max => //; apply: measurable_fun_cst.
Qed.

Lemma emeasurable_fun_funennp (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D f^\-.
Proof.
move=> mD mf; apply: emeasurable_fun_max => //; last exact: measurable_fun_cst.
apply: measurable_fun_comp => //; apply: emeasurable_fun_minus.
exact: measurableT.
Qed.

End funpos_measurable.

Module PreSFun.
Section presfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f :> T -> R ;
  rng : seq R ;
  uniq_rng : uniq rng ;
  full_rng : f @` setT = [set x | x \in rng] }.
Definition ssize f := size (rng f).
Definition spi f := fun k : 'I_(ssize f) => f @^-1` [set (rng f)`_k].
End presfun.
Module Exports.
Notation presfun := PreSFun.t.
Notation ssize := ssize.
Notation srng := rng.
Notation spi := spi.
End Exports.
End PreSFun.
Export PreSFun.Exports.
Arguments PreSFun.spi {T} {R} _.
Coercion PreSFun.f : presfun >-> Funclass.

Section presfun_partition.
Variables (T : measurableType) (R : realType) (f : presfun T R).
Let n := ssize f.

Lemma mem_img_srng t : f t \in srng f.
Proof.
have := PreSFun.full_rng f; rewrite predeqE => /(_ (f t))[+ _].
by apply; exists t.
Qed.

Lemma trivIset_spi (A : set 'I_n) : trivIset A (spi f).
Proof.
apply/trivIsetP => /= i j _ _ ij.
suff ij0 : [set (srng f)`_i] `&` [set (srng f)`_j] = set0.
  by rewrite -preimage_setI ij0 preimage_set0.
apply/eqP/negPn/negP => /set0P[r []] => ->{r} /eqP.
by rewrite nth_uniq => //; [exact/negP|exact: PreSFun.uniq_rng].
Qed.

Lemma bigsetU_spi : \big[setU/set0]_(i < n) spi f i = setT.
Proof.
rewrite predeqE => t; split => // _; rewrite -bigcup_set -preimage_bigcup.
have /(nthP 0)[i ni fit] := mem_img_srng t.
by exists (Ordinal ni) => //=; rewrite mem_index_enum.
Qed.

End presfun_partition.

Section presfun_lemmas1.
Variables (T : measurableType) (R : realType) (f : presfun T R).
Implicit Types (x : T) (i : 'I_(ssize f)).

Let ltn_idx_size x : (index (f x) (srng f) < ssize f)%N.
Proof. by rewrite index_mem mem_img_srng. Qed.

Definition img_idx x := Ordinal (ltn_idx_size x).

Lemma nth_img_idx x : (srng f)`_(img_idx x) = f x.
Proof. by rewrite nth_index //; exact: mem_img_srng. Qed.

Lemma spi_img_idx x : spi f (img_idx x) x.
Proof. by rewrite /spi /preimage mksetE nth_img_idx. Qed.

Lemma spi_nth i x : spi f i x -> (srng f)`_i = f x.
Proof. by []. Qed.

Lemma presfun_ge0 : (forall x, 0 <= f x) -> forall i, 0 <= (srng f)`_i.
Proof.
case: f => f' /= s us fs f0 i.
have : [set` s] s`_i by apply/(nthP 0); exists i.
by rewrite -fs => -[x _ <-]; exact: f0.
Qed.

End presfun_lemmas1.

Section presfun_lemmas2.
Variables (T : measurableType) (R : realType).
Implicit Types f g : presfun T R.

Let presfun_eq_subset f g : f =1 g -> {subset srng f <= srng g}.
Proof.
move=> fg r rf; have := PreSFun.full_rng g; rewrite predeqE => /(_ r)[+ _].
apply; have := PreSFun.full_rng f; rewrite predeqE => /(_ r)[_].
by move/(_ rf) => [t _ <-]; exists t.
Qed.

Lemma presfun_eq_perm f g : f =1 g -> perm_eq (srng f) (srng g).
Proof.
move=> fg; apply: uniq_perm; [exact:PreSFun.uniq_rng|exact:PreSFun.uniq_rng|].
move=> r; apply/idP/idP; exact: presfun_eq_subset.
Qed.

Lemma presfun_size f g : f =1 g -> ssize f = ssize g.
Proof. by move/presfun_eq_perm => fg; apply: perm_size. Qed.

End presfun_lemmas2.

Section presfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Definition sfun_cst_rng := [:: r].
Definition sfun_cst_f : T -> R := cst r.
Local Notation rng := sfun_cst_rng.
Local Notation f := sfun_cst_f.

Let presfun_cst_uniq : uniq rng. Proof. by []. Qed.

Let presfun_cst_full_rng : f @` setT = [set x | x \in rng].
Proof.
rewrite /rng predeqE => r'; split; first by move=> [t _ <- /=]; rewrite inE.
by rewrite /= inE => /eqP ->{r'}; exists point.
Qed.

Definition presfun_cst := PreSFun.mk presfun_cst_uniq presfun_cst_full_rng.

End presfun_cst.

Section presfun_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variable f : presfun T R.
Definition sfun_scale_rng :=
  if r == 0 then [:: 0] else [seq r * x | x <- srng f].
Definition sfun_scale_f := fun x => r * f x.
Local Notation rng := sfun_scale_rng.
Local Notation g := sfun_scale_f.

Let presfun_scale_uniq : uniq rng.
Proof.
have [r0|r0] := eqVneq r 0; first by rewrite /rng r0 eqxx.
rewrite /rng (negbTE r0) map_inj_uniq; first exact: PreSFun.uniq_rng.
by apply: mulrI; rewrite unitfE.
Qed.

Let presfun_scale_full_rng : g @` setT = [set x | x \in rng].
Proof.
rewrite predeqE => r1; split.
  case=> t _ <-{r1}; rewrite mksetE /rng.
  have [r0|r0] := eqVneq r 0; first by rewrite /g r0 mul0r inE.
  by apply/mapP; exists (f t) => //; exact: mem_img_srng.
rewrite /= /rng; have [r0|r0 /mapP[r2]] := eqVneq r 0.
  by rewrite inE => /eqP ->{r1}; exists point => //; rewrite /g r0 mul0r.
have := PreSFun.full_rng f.
by rewrite predeqE => /(_ r2) /= [_ /[apply]] [t] _ <-{r2} ->{r1}; exists t.
Qed.

Definition presfun_scale := PreSFun.mk presfun_scale_uniq presfun_scale_full_rng.

End presfun_scale.

Section presfun_proj.
Variables (T : measurableType) (R : realType) (f : presfun T R).
Variable A : set T.
Let s := [seq y <- srng f | f @^-1` [set y] `&` A != set0].
Definition sfun_proj_rng := if (0 \in s) || (A == setT) then s else 0 :: s.
Definition sfun_proj_f x := f x * (x \in A)%:R.
Local Notation rng := sfun_proj_rng.
Local Notation g := sfun_proj_f.

Lemma set_sfun_proj_f (x : R) : [set t | [set x] (sfun_proj_f t)] =
    ((A `&` (g @^-1` [set x])) `|` (~` A `&` (fun _ => x = 0))).
Proof.
rewrite [LHS](_ : _ = (fun t => if t \in A then g t = x else x = 0)); last first.
  by rewrite predeqE => t; split; rewrite /sfun_proj_f /=;
    have [tS|tS] := boolP (t \in A); rewrite !(mulr1,mulr0).
rewrite predeqE => t; split.
  case: ifPn => [tA <-|tA].
    by left; split => //; rewrite -in_setE.
  by right; split => //; apply: contraNnot tA; rewrite in_setE.
case: ifPn => [tA [[_ <-//]|[]] |tA [[]|[]//]].
- by rewrite in_setE in tA.
- by rewrite -in_setE (negbTE tA).
Qed.

Lemma presfun_proj_rng_subset a : a != 0 -> a \in rng -> a \in srng f.
Proof.
move=> a0; rewrite /rng.
case: ifPn => [_|]; first by rewrite mem_filter => /andP[].
rewrite negb_or => /andP[s0 AT].
by rewrite inE (negbTE a0)/= /s mem_filter => /andP[].
Qed.

Let presfun_proj_uniq : uniq rng.
Proof.
rewrite /rng; case: ifPn => [_|]; first exact/filter_uniq/PreSFun.uniq_rng.
rewrite negb_or => /andP[/= -> _ /=].
by rewrite (filter_uniq _ (PreSFun.uniq_rng f)).
Qed.

Let presfun_proj_full_rng : g @` setT = [set x | x \in rng].
Proof.
rewrite predeqE => x; split => [[t _] <-{x}|] /=.
- rewrite /g; have [|tA] := boolP (t \in A).
  + rewrite mulr1 in_setE => tA; rewrite /rng.
    case: ifPn => [_|].
      by rewrite mem_filter mem_img_srng andbT; apply/set0P; exists t.
    rewrite negb_or => /andP[s0 /setTP[t1 At1]].
    rewrite inE mem_filter mem_img_srng andbT; apply/orP; right; apply/set0P.
    by exists t.
  + rewrite mulr0; rewrite /rng; case: ifPn => [/orP[//|/eqP AT]|].
       by move: tA; rewrite AT notin_setE => /(_ Logic.I).
    by rewrite negb_or => /andP[s0 AT]; rewrite mem_head.
- rewrite /rng; case: ifPn => [_|].
    rewrite mem_filter => /andP[/set0P[t [/= ftx At]]] fx.
    exists t => //; rewrite /g; move: At; rewrite -in_setE => ->.
    by rewrite mulr1.
  rewrite negb_or => /andP[s0 AT]; rewrite inE => /orP[/eqP ->|].
    rewrite /g; move/setTP : AT => [t At]; exists t => //.
    by move: At; rewrite -notin_setE => /negbTE ->; rewrite mulr0.
  rewrite mem_filter => /andP[/set0P[t [fxt At]]] fx.
  rewrite /g; exists t => //; move: At; rewrite -in_setE => ->.
  by rewrite mulr1.
Qed.

Definition presfun_proj := PreSFun.mk presfun_proj_uniq presfun_proj_full_rng.

Lemma srng_presfun_proj : srng presfun_proj = rng.
Proof. by []. Qed.

Lemma presfun_projE x : presfun_proj x = f x * (x \in A)%:R.
Proof. by []. Qed.

End presfun_proj.

Section presfun_ind.
Variables (T : measurableType) (point : T) (R : realType) (r : R) (A : set T).

Definition presfun_ind := presfun_proj (presfun_cst point r) A.

End presfun_ind.

Section presfun_bin.
Variables (T : measurableType) (R : realType) (f g : presfun T R).
Implicit Types op : R -> R -> R.
Let n := ssize f.
Let p := ssize g.
Let u := [seq z <- [seq (x, y) | x <- srng f, y <- srng g] |
          (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0 ].
Let s op := undup [seq op z.1 z.2 | z <- u].

Let presfun_bin_full_rng op : (fun x => op (f x) (g x)) @` setT = [set` s op].
Proof.
rewrite predeqE => r; split => /=.
- move=> -[t _] <-; rewrite /s mem_undup.
  apply/mapP; exists (f t, g t) => //; rewrite mem_filter /=; apply/andP; split.
    by rewrite /mkset /set1 /mkset; apply/set0P; exists t.
  by apply/allpairsP; exists (f t, g t); split => //; apply: mem_img_srng.
- rewrite /s mem_undup => /mapP[[i j]].
  rewrite mem_filter /= => /andP[/set0P[t []]].
  rewrite /mkset /set1 /mkset => fti gtj.
  move=> /allpairsP[[i' j']] /= [fi' gj'] [? ?]; subst i' j' => ->.
  by exists t => //; rewrite fti gtj.
Qed.

Definition presfun_bin_idx op (k : 'I_(size (s op))) :=
  [set x : 'I_n * 'I_p | (op (srng f)`_x.1 (srng g)`_x.2 == (s op)`_k) &&
                         (spi f x.1 `&` spi g x.2 != set0)]%SET.

Lemma bigsetU_presfun_bin op (k : 'I_(size (s op))) :
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in presfun_bin_idx k)
    (spi f x.1 `&` spi g x.2) =
  \big[setU/set0]_(z <- [seq (x, y) | x <- enum 'I_n, y <- enum 'I_p] |
                        z \in presfun_bin_idx k)
    (spi f z.1 `&` spi g z.2).
Proof.
rewrite -[in RHS]bigcup_set_cond -bigcup_set_cond.
rewrite predeqE => t; split=> [[[i j] /=]|]; last first.
  case => /= -[i j] /= /andP[H aij] [fit gjt]; exists (i, j) => //=.
  by rewrite mem_index_enum.
rewrite !inE /= => /andP[] _ /andP[] /eqP afg fg0 [/= ft gt].
exists (img_idx f t, img_idx g t) => /=; last by split; exact: spi_img_idx.
apply/andP; split => /=.
  apply/flattenP; exists [seq (img_idx f t, x) | x <- enum 'I_p].
    by apply/mapP; exists (img_idx f t) => //; rewrite mem_enum.
  by apply/mapP; exists (img_idx g t) => //; rewrite mem_enum.
rewrite !inE /= !nth_img_idx -afg (spi_nth ft) (spi_nth gt) eqxx /=.
by apply/set0P; exists t; split; exact: spi_img_idx.
Qed.

Lemma preimage_presfun_bin op (k : 'I_(size (s op))) :
  (fun x => op (f x) (g x)) @^-1` [set (s op)`_k] =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in presfun_bin_idx k)
      (spi f x.1 `&` spi g x.2).
Proof.
transitivity (\big[setU/set0]_(x : 'I_n * 'I_p |
     op (srng f)`_x.1 (srng g)`_x.2 == (s op)`_k)
    (spi f x.1 `&` spi g x.2)); last first.
  rewrite /presfun_bin_idx big_mkcond [in RHS]big_mkcond.
  apply: eq_bigr => /= -[i j] _ /=; rewrite inE /=.
  by case: ifPn => //= _; case: ifPn => //; rewrite negbK => /eqP.
rewrite -bigcup_set_cond predeqE => t; split=> [fgt|].
  exists (img_idx f t, img_idx g t) => /=.
    by rewrite !nth_img_idx -fgt // mem_index_enum eqxx.
  by split => //; exact: spi_img_idx.
by move=> [[i j]] /=; rewrite mem_index_enum /= /preimage /= => /eqP <- [-> ->].
Qed.

Definition presfun_add := PreSFun.mk (undup_uniq _)
  (presfun_bin_full_rng (fun x y => x + y)).

Definition presfun_max := PreSFun.mk (undup_uniq _)
  (presfun_bin_full_rng maxr).

Lemma presfun_bin_pi_cover op : \bigcup_(c < size (s op)) presfun_bin_idx c =
  [set x : {: 'I_n * 'I_p} | spi f x.1 `&` spi g x.2 != set0]%SET.
Proof.
apply/setP => -[k l]; rewrite !inE /=; apply/bigcupP/idP => /=.
- by move=> [i] _; rewrite inE /= => /eqP/eqP/andP[].
- move=> kl; set fg := op (srng f)`_k (srng g)`_l.
  suff [i kli] : exists i : 'I_(size (s op)), fg = (s op)`_i.
    by exists i => //; rewrite inE /= -/fg kli eqxx.
  have : fg \in [set of (fun x => op (f x) (g x))].
    rewrite inE /=; move/set0P : kl => [t [/spi_nth kt /spi_nth lt]].
    by exists t => //; rewrite -kt -lt.
  rewrite presfun_bin_full_rng inE /= => /(nthP 0)[x xa sfg].
  by exists (Ordinal xa).
Qed.

Lemma trivIset_presfun (D : set T) :
  trivIset setT (fun i : 'I_n * 'I_p => spi f i.1 `&` spi g i.2 `&` D).
Proof.
apply/trivIsetP => /= -[a b] [c d] _ _ /=.
rewrite xpair_eqE negb_and => /orP[ac|bd].
  rewrite setIACA (_ : spi f a `&` _ `&` _ = set0) ?set0I//.
  rewrite setIACA (_ : spi f a `&` _ = set0) ?set0I//.
  by move/trivIsetP: (@trivIset_spi _ _ f setT) => /(_ _ _ Logic.I Logic.I ac).
rewrite setIACA (_ : spi f a `&` _ `&` _ = set0) ?set0I//.
rewrite setIACA (_ : spi g b `&` _ = set0) ?setI0//.
by move/trivIsetP : (@trivIset_spi _ _ g setT) => /(_ _ _ Logic.I Logic.I bd).
Qed.

End presfun_bin.

Section presfun_add_lemmas.
Variables (T : measurableType) (R : realType) (f g : presfun T R).
Let n := ssize f.
Let p := ssize g.

Lemma spi_presfun_add (i : 'I_(ssize (presfun_add f g))) :
  spi (presfun_add f g) i =
  \big[setU/set0]_(x : 'I_n * 'I_p | x \in presfun_bin_idx i)
    (spi f x.1 `&` spi g x.2).
Proof.
transitivity ((presfun_add f g) @^-1` [set (srng (presfun_add f g))`_i]) => //.
by rewrite preimage_presfun_bin.
Qed.

End presfun_add_lemmas.

Module NNPreSFun.
Section nnpresfun.
Variables (T : measurableType) (R : realType).
Record t := mk {f : presfun T R ; ge0 : forall t, 0 <= f t }.
End nnpresfun.
Module Exports.
Notation nnpresfun := t.
End Exports.
End NNPreSFun.
Export NNPreSFun.Exports.
Coercion NNPreSFun.f : nnpresfun >-> presfun.

Hint Resolve NNPreSFun.ge0 : core.

Section nnpresunf_ind.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).
Variables (A : set T).

Let nnpresfun_point_ge0 t : 0 <= presfun_ind point r%:nngnum A t.
Proof. by rewrite mulr_ge0. Qed.

Definition nnpresfun_ind := NNPreSFun.mk nnpresfun_point_ge0.

Lemma nnpresfun_indE x : nnpresfun_ind x = r%:nngnum * (x \in A)%:R.
Proof. by rewrite /= /sfun_proj_f /= /sfun_cst_f /= /cst /=. Qed.

End nnpresunf_ind.

Section nnpresunf_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).

Let nnpresfun_cst_ge0 x : 0 <= presfun_cst point r%:nngnum x. Proof. by []. Qed.

Definition nnpresfun_cst := NNPreSFun.mk nnpresfun_cst_ge0.

End nnpresunf_cst.

Section nnpresfun_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variables (f : nnpresfun T R) (k : R) (k0 : 0 <= k).

Let nnpresfun_scale_ge0 x : 0 <= presfun_scale point k f x.
Proof. by rewrite mulr_ge0. Qed.

Definition nnpresfun_scale := NNPreSFun.mk nnpresfun_scale_ge0.

End nnpresfun_scale.

Section nnpresfun_add.
Variables (T : measurableType) (R : realType) (f g : nnpresfun T R).

Let nnpresfun_add_ge0 x : 0 <= presfun_add f g x.
Proof. by rewrite addr_ge0. Qed.

Definition nnpresfun_add := NNPreSFun.mk nnpresfun_add_ge0.

End nnpresfun_add.

Section nnpresfun_max.
Variables (T : measurableType) (R : realType) (f g : nnpresfun T R).

Let nnpresfun_max_ge0 x : 0 <= presfun_max f g x.
Proof. by rewrite /= /maxr; case: ifPn. Qed.

Definition nnpresfun_max := NNPreSFun.mk nnpresfun_max_ge0.

End nnpresfun_max.

Section nnpresfun0.
Variables (T : measurableType) (point : T) (R : realType).

Definition nnpresfun0 : nnpresfun T R :=
  nnpresfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).

End nnpresfun0.

Section nnpresfun_sum.
Variables (T : measurableType) (point : T) (R : realType).
Variable f : (nnpresfun T R)^nat.

Definition nnpresfun_sum n :=
  \big[(@nnpresfun_add T R)/(nnpresfun0 point R)]_(i < n) f i.

Lemma nnpresfun_sumE n t : nnpresfun_sum n t = \sum_(i < n) (f i t).
Proof. by rewrite /nnpresfun_sum; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnpresfun_sum.

Section nnpresfun_bigmax.
Variables (T : measurableType) (point : T) (R : realType).
Variable f : (nnpresfun T R)^nat.

Definition nnpresfun_bigmax n :=
  \big[(@nnpresfun_max T R)/(nnpresfun0 point R)]_(i < n) f i.

Lemma nnpresfun_bigmaxE n t :
  nnpresfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /nnpresfun_bigmax; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnpresfun_bigmax.

Module SFun.
Section sfun.
Variables (T : measurableType) (R : realType).
Record t := mk {
  f :> presfun T R ;
  mpi : forall k, measurable (spi f k) }.
End sfun.
Module Exports.
Notation sfun := SFun.t.
End Exports.
End SFun.
Export SFun.Exports.
Coercion SFun.f : sfun >-> PreSFun.t.

Arguments SFun.mk {T R} _ _.

Section sfun_lemmas.
Variables (T : measurableType) (R : realType) (f : sfun T R).
Let n := ssize f.

Lemma measurable_preimage_set1 (r : R) : measurable (f @^-1` [set r]).
Proof.
have [[k fkr]|/forallNP fr] := pselect (exists k : 'I_(ssize f), (srng f)`_k = r).
  by have := SFun.mpi k; rewrite /spi fkr.
rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
rewrite predeqE => t; split => //= ftr.
have /(nthP 0)[i fi fift] := mem_img_srng f t.
by have := fr (Ordinal fi); rewrite fift.
Qed.

End sfun_lemmas.

Section sfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Let rng := sfun_cst_rng r.
Let f (t : T) := sfun_cst_f r t.
Let pi := fun k : 'I_1 => f @^-1` [set rng`_k].

Let sfun_cst_mpi k : measurable (pi k).
Proof.
rewrite (_ : pi _ = setT); first exact: measurableT.
by rewrite predeqE => t; split => // _; rewrite (ord1 k).
Qed.

Definition sfun_cst := SFun.mk (presfun_cst point r) sfun_cst_mpi.

End sfun_cst.

Section sfun_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variable (f : sfun T R).
Let n := ssize f.
Let rng := sfun_scale_rng r f.
Let g := sfun_scale_f r f.
Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Let sfun_scale_mpi k : measurable (pi k).
Proof.
have [r0|r0] := eqVneq r 0.
  move: k; rewrite /pi /rng /sfun_scale_rng r0 eqxx /= => k.
  rewrite [_ @^-1` _](_ : mkset _ = setT); first exact: measurableT.
  rewrite predeqE => t; split => // _; rewrite mksetE ord1 /g.
  by rewrite /sfun_scale_f r0 mul0r.
move=> [:k'n]; have @k' : 'I_n.
  apply: (@Ordinal _ k); abstract: k'n.
  rewrite /ssize /= (leq_trans (ltn_ord k)) // /rng.
  by rewrite /sfun_scale_rng (negbTE r0) size_map.
rewrite /pi /= (_ : _ @^-1` _ = spi f k'); first exact: SFun.mpi.
rewrite predeqE => t; split.
  rewrite /rng /sfun_scale_rng /preimage mksetE {1}(negbTE r0) (nth_map 0) //.
  by apply: mulrI; rewrite unitfE.
rewrite /spi /preimage mksetE /= /g /sfun_scale_f => ->.
transitivity ([seq r * x | x <- srng f]`_k); first by rewrite (nth_map 0).
by congr (_ `_ _); rewrite /rng /sfun_scale_rng (negbTE r0).
Qed.

Definition sfun_scale := SFun.mk (presfun_scale point r f) sfun_scale_mpi.

End sfun_scale.

Section sfun_scale_lemmas.
Variables (T : measurableType) (point : T) (R : realType) (r : R) (f : sfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma ssize_sfun_scale0 : ssize (sfun_scale point 0 f) = 1%N.
Proof. by rewrite /ssize /= /sfun_scale_rng /= eqxx. Qed.

Lemma ssize_sfun_scale_neq0 : r != 0 -> ssize (sfun_scale point r f) = ssize f.
Proof. by move=> r0; rewrite /ssize /= /sfun_scale_rng (negbTE r0) size_map. Qed.

End sfun_scale_lemmas.

Section sfun_proj.
Variables (T : measurableType) (point : T) (R : realType) (f : sfun T R).
Variables (A : set T) (mA : measurable A).
Let g (x : T) : R := sfun_proj_f f A x.
Let rng := sfun_proj_rng f A.
Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Lemma sfun_proj_mpi k : measurable (pi k).
Proof.
rewrite /pi; set a := rng`_k; have [a0|a0] := eqVneq a 0.
- rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A) `|` ~` A); last first.
    rewrite predeqE => t; split.
      rewrite /g /= /sfun_proj_f /= /preimage /=.
      have [tA|tA _] := boolP (t \in A).
        by rewrite mulr1 => <-; left; split => //; rewrite -in_setE.
      by right; rewrite /setC /=; rewrite notin_setE in tA.
    move=> [[<- At]|At].
      rewrite /= /preimage /= /g /sfun_proj_f /=.
      by move: At; rewrite -in_setE => ->; rewrite mulr1.
    rewrite /= /g /sfun_proj_f /preimage /=.
    move: At; rewrite /setC /=; rewrite -notin_setE => /negbTE => ->.
    by rewrite mulr0.
  apply: measurableU; last by apply: measurableC.
  apply: measurableI => //.
  have [fa|fa] := boolP (a \in srng f).
    move: fa => /(nthP 0)[i fi fia].
    rewrite -fia (_ : _ @^-1` _ = spi f (Ordinal fi)) //.
    exact: SFun.mpi.
  rewrite (_ : _ @^-1` _ = set0); first exact: measurable0.
  rewrite predeqE => t; split => // fta; move/negP : fa; apply.
  by rewrite -fta; exact: mem_img_srng.
rewrite (_ : _ @^-1` _ = (f @^-1` [set a] `&` A)); last first.
  rewrite predeqE => t; split.
    rewrite /g /sfun_proj_f /preimage /=; have [tA|tA] := boolP (t \in A).
      by rewrite mulr1 => <-; split => //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE a0).
  move=> [<- At]; rewrite /g /sfun_proj_f /preimage /=.
  by move: At; rewrite -in_setE => ->; rewrite mulr1.
apply: measurableI => //; have /(nthP 0)[i fi fia] : a \in srng f.
  apply: (@presfun_proj_rng_subset _ _ f A a a0) => //; apply/(nthP 0).
  by exists k.
by rewrite -fia (_ : _ @^-1` _ = spi f (Ordinal fi)) //; exact: SFun.mpi.
Qed.

Definition sfun_proj := SFun.mk (presfun_proj f A) sfun_proj_mpi.

Lemma sfun_projE x : sfun_proj x = f x * (x \in A)%:R.
Proof. by []. Qed.

End sfun_proj.

Section sfun_ind.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variables (A : set T) (mA : measurable A).

Definition sfun_ind := sfun_proj (sfun_cst point r) mA.

Lemma sfun_indE x : sfun_ind x = r * (x \in A)%:R.
Proof. by rewrite /= /sfun_proj_f /= /sfun_cst_f /= /cst /=. Qed.

End sfun_ind.

Section sfun_bin.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.
Let u := [seq z <- [seq (x, y) | x <- srng f, y <- srng g] |
  (f @^-1` [set z.1]) `&` (g @^-1` [set z.2]) != set0 ].
Let s (op : R -> R -> R) : seq R := undup [seq op z.1 z.2 | z <- u].

Local Lemma sfun_bin_mpi (op : R -> R -> R) (k : 'I_(size (s op))) :
  measurable ((fun x => op (f x) (g x)) @^-1` [set (s op)`_k]).
Proof.
rewrite preimage_presfun_bin bigsetU_presfun_bin.
by apply: bigsetU_measurable => -[i j] aij; apply: measurableI; exact: SFun.mpi.
Qed.

Definition sfun_add := SFun.mk (presfun_add f g)
  (@sfun_bin_mpi (fun x y => x + y)).

Definition sfun_max := SFun.mk (presfun_max f g)
  (@sfun_bin_mpi maxr).

End sfun_bin.

Section sfun_add_lemmas.
Variables (T : measurableType) (R : realType) (f g : sfun T R).
Let n := ssize f.
Let p := ssize g.

Lemma measure_sfun_bin_pi (mu : {measure set T -> \bar R}) (D : set T)
  (mD : measurable D) (c : 'I_(ssize (sfun_add f g))) :
  mu (spi (sfun_add f g) c `&` D) =
  (\sum_(kl in presfun_bin_idx c) mu (spi f kl.1 `&` spi g kl.2 `&` D))%E.
Proof.
rewrite spi_presfun_add big_distrl /=.
rewrite (additive_set mu _ _ (@trivIset_presfun _ _ _ _ D)) //=.
by move=> -[i j]; apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
Qed.

End sfun_add_lemmas.

Lemma measurable_sfun (T : measurableType) (R : realType) (f : sfun T R)
    (D : set T) :
  measurable D -> measurable_fun D f.
Proof.
move=> mD; apply: (measurability mD (RGenOpenRays.measurableE  R)).
move=> _ [/= _ [r ->] <-]; rewrite [X in measurable X](_ : _ =
  \bigcup_(i in [set j | (srng f)`_j > r]) (f @^-1` [set (srng f)`_i] `&` D)).
  rewrite -setI_bigcupl; apply: measurableI => //.
  by apply: bigcup_measurable => k /= rfk; exact: measurable_preimage_set1.
rewrite predeqE => t; split=> [[]|[n /= fnr []]].
  rewrite /preimage /= in_itv/= andbT => rft Dt.
  by exists (img_idx f t) => /=; rewrite nth_img_idx.
by rewrite /preimage /= => -> Dt; split => //; rewrite in_itv /= andbT.
Qed.

Section simple_function_integral.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (f : presfun T R).
Let n := ssize f.
Let A := spi f.
Let a := srng f.
Local Open Scope ereal_scope.

Definition sintegral : \bar R := \sum_(k < n) (a`_k)%:E * mu (A k `&` D).

Lemma sintegralE : sintegral =
  \sum_(x <- srng f) x%:E * mu (f @^-1` [set x] `&` D).
Proof.
rewrite big_tnth; apply: eq_bigr => i _; congr (_%:E * mu _).
  by apply: set_nth_default; rewrite /= ltn_ord.
rewrite /A /spi; congr (_ @^-1` _ `&` _); rewrite predeqE => r; split;
  by rewrite /set1 mksetE => ->; apply: set_nth_default; rewrite ltn_ord.
Qed.

End simple_function_integral.

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

Lemma NNSFun_ge0 (T : measurableType) (R : realType) (f : nnsfun T R)
  (t : 'I_(ssize f)) : 0 <= (srng f)`_t.
Proof. by case: f t => // f h /= t; apply: presfun_ge0. Qed.

Lemma NNSFuncdom_ge0 (T : measurableType) (R : realType) (f : nnsfun T R)
  (r : R) : r \in srng f -> (0 <= r%:E)%E.
Proof.
by move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNSFun_ge0 (Ordinal fi)).
Qed.

Lemma sintegral_ge0 (T : measurableType) (R : realType) (D : set T)
  (mD : measurable D) (f : nnsfun T R) (m : {measure set T -> \bar R}) :
  (0 <= sintegral m D f)%E.
Proof.
rewrite /sintegral; apply: sume_ge0 => t _; apply: mule_ge0 => //.
  exact: NNSFun_ge0.
by apply/measure_ge0/measurableI => //; exact/SFun.mpi.
Qed.

Section nnsfun_cst.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).

Let nnsfun_cst_ge0 x : 0 <= sfun_cst point r%:nngnum x. Proof. by []. Qed.

Definition nnsfun_cst := NNSFun.mk nnsfun_cst_ge0.

End nnsfun_cst.

Section nnsfun0.
Variables (T : measurableType) (point : T) (R : realType).

Definition nnsfun0 : nnsfun T R :=
  nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).

End nnsfun0.

Section nnsfun_proj.
Variables (T : measurableType) (R : realType) (f : nnsfun T R).
Variables (A : set T) (mA : measurable A).

Let nnsfun_proj_ge0 x : 0 <= sfun_proj f mA x.
Proof. exact: mulr_ge0. Qed.

Definition nnsfun_proj := NNSFun.mk nnsfun_proj_ge0.

Lemma nnsfun_projE x : nnsfun_proj x = f x * (x \in A)%:R.
Proof. by []. Qed.

End nnsfun_proj.

Section nnsfun_ind.
Variables (T : measurableType) (point : T) (R : realType) (r : {nonneg R}).
Variables (A : set T) (mA : measurable A).

Let nnsfun_ge0 t : 0 <= sfun_ind point r%:nngnum mA t.
Proof. by rewrite mulr_ge0. Qed.

Definition nnsfun_ind := NNSFun.mk nnsfun_ge0.

Lemma nnsfun_indE x : nnsfun_ind x = r%:nngnum * (x \in A)%:R.
Proof. by rewrite /= /sfun_proj_f /= /sfun_cst_f /= /cst /=. Qed.

End nnsfun_ind.

Section nnsfun_scale.
Variables (T : measurableType) (point : T) (R : realType) (r : R).
Variables (f : nnsfun T R) (k : R) (k0 : 0 <= k).

Let nnsfun_scale_ge0 x : 0 <= sfun_scale point k f x.
Proof. by rewrite mulr_ge0. Qed.

Definition nnsfun_scale := NNSFun.mk nnsfun_scale_ge0.

End nnsfun_scale.

Section nnsfun_add.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Let nnsfun_add_ge0 x : 0 <= sfun_add f g x. Proof. by rewrite addr_ge0. Qed.

Definition nnsfun_add := NNSFun.mk nnsfun_add_ge0.

End nnsfun_add.

Section nnsfun_sum.
Variables (T : measurableType) (point : T) (R : realType).
Variable f : (nnsfun T R)^nat.

Definition nnsfun_sum n :=
  \big[(@nnsfun_add T R)/(nnsfun0 point R)]_(i < n) f i.

Lemma nnsfun_sumE n t : nnsfun_sum n t = \sum_(i < n) (f i t).
Proof. by rewrite /nnsfun_sum; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnsfun_sum.

Section nnsfun_max.
Variables (T : measurableType) (R : realType) (f g : nnsfun T R).

Local Lemma nnsfun_max_ge0 x : 0 <= sfun_max f g x.
Proof. by rewrite /= /maxr; case: ifPn. Qed.

Definition nnsfun_max := NNSFun.mk nnsfun_max_ge0.

End nnsfun_max.

Section nnsfun_bigmax.
Variables (T : measurableType) (point : T) (R : realType).
Variable (f : (nnsfun T R)^nat).

Definition nnsfun_bigmax n :=
  \big[(@nnsfun_max T R)/(nnsfun0 point R)]_(i < n) f i.

Lemma nnsfun_bigmaxE n t : nnsfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /nnsfun_bigmax; elim/big_ind2 : _ => // x g y h <- <-. Qed.

End nnsfun_bigmax.

Section sintegralM.
Variables (T : measurableType) (point : T) (R : realType).
Variable (m : {measure set T -> \bar R}).
Variables (r : R) (D : set T) (mD : measurable D) (f : nnsfun T R).
Local Open Scope ereal_scope.

Lemma sintegralM :
  sintegral m D (sfun_scale point r f) = r%:E * sintegral m D f.
Proof.
have [->|r0] := eqVneq r 0%R.
  rewrite mul0e /sintegral big1 // => i _; rewrite /= /sfun_scale_rng eqxx /=.
  case: (m (_ `&` _)) => [x| |]; move: i; rewrite ssize_sfun_scale0 => i.
  - by rewrite (ord1 i) mul0e.
  - by rewrite (ord1 i) /= mul0e.
  - by rewrite (ord1 i) /= mul0e.
rewrite /sintegral.
pose cast := cast_ord (ssize_sfun_scale_neq0 point f r0).
rewrite [LHS](eq_bigr (fun k : 'I_(ssize (sfun_scale point r f)) =>
    (r * (srng f)`_(cast k))%:E * m (spi f (cast k) `&` D))); last first.
  move=> i _; congr (_%:E * m _).
    rewrite /= /sfun_scale_rng (negbTE r0) (nth_map 0%R) //.
    by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
  rewrite predeqE => x; split.
    rewrite /spi /= /set1 /sfun_scale_rng /= {1}(negbTE r0) (nth_map 0%R).
      by move=> [/mulrI fxi Dx]; split => //; apply: fxi; rewrite unitfE.
    by rewrite (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
  rewrite /spi /set1 /= => -[fxi Dx]; split => //.
  rewrite /= /preimage /= /sfun_scale_f fxi /sfun_scale_rng {1}(negbTE r0).
  by rewrite (nth_map 0%R) // (leq_trans (ltn_ord i)) // ssize_sfun_scale_neq0.
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
  ((srng f)`_i + (srng g)`_l)%:E * m (spi f i `&` spi g l `&` D)).
  rewrite /sintegral; under eq_bigr do rewrite (measure_sfun_bin_pi _ mD).
  transitivity (\sum_(i : 'I_(ssize (sfun_add f g)))
    (\sum_(x in presfun_bin_idx i) ((srng f)`_x.1 + (srng g)`_x.2)%:E *
      m (spi f x.1 `&` spi g x.2 `&` D))).
    apply: eq_bigr => i _; rewrite ge0_sume_distrr //; last first.
      move=> kl _; rewrite measure_ge0 //; apply: measurableI => //.
      by apply: measurableI; exact: SFun.mpi.
    by apply: eq_bigr => x; rewrite !inE => /andP[] /eqP ->.
  rewrite [in RHS]pair_big /=.
  rewrite [in RHS](eq_bigl [pred x | x \in setX [set: _] [set: _]]); last first.
    by move=> [k l]; rewrite !inE.
  transitivity (\sum_(x in [set x|spi f x.1 `&` spi g x.2 != set0]%SET)
      ((srng f)`_x.1 + (srng g)`_x.2)%:E *
      m (spi f x.1 `&` spi g x.2 `&` D)); last first.
    rewrite big_mkcond; apply: eq_big => //; first by move=> x; rewrite !inE.
    move=> [x y] _; case: ifPn => //; rewrite inE negbK => /eqP -> /=.
    by rewrite set0I measure0 mule0.
  rewrite -(presfun_bin_pi_cover _ _ (fun x y => x + y)%R).
  rewrite partition_disjoint_bigcup //= => i j ij.
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[[k l]].
  rewrite inE /= => /andP[]; rewrite 2!inE => /andP[/eqP -> _] /andP[+ _].
  by rewrite (nth_uniq _ _ _ (undup_uniq _)) //; exact/negP.
rewrite /sintegral -/n -/p [RHS]addeC.
have ggf k : m (spi g k `&` D) = \sum_(i < n) m (spi g k `&` spi f i `&` D).
  rewrite -[in LHS](setIT (spi g k `&` D)) -(bigsetU_spi f) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_spi.
  by move=> i; apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
under [X in _ = X + _]eq_bigr do rewrite ggf.
transitivity (\sum_(i < p) (\sum_(j < n)
     ((srng g)`_i)%:E * m (spi g i `&` spi f j `&` D)) +
   \sum_(k < n) ((srng f)`_k)%:E * m (spi f k `&` D)); last first.
  congr adde; apply: eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
have ffg k : m (spi f k `&` D) = \sum_(l < p) m (spi f k `&` spi g l `&` D).
  rewrite -[in LHS](setIT (spi f k `&` D)) -(bigsetU_spi g) big_distrr /=.
  under eq_bigr do rewrite setIAC.
  rewrite additive_ord //; last first.
    under [in X in trivIset setT X]eq_fun do rewrite setIAC.
    exact/trivIset_setI/trivIset_spi.
  by move=> i; apply: measurableI => //; apply/measurableI; exact: SFun.mpi.
under [X in _ = _ + X]eq_bigr do rewrite ffg.
transitivity (\sum_(i < p) \sum_(j < n)
    ((srng g)`_i)%:E * m (spi g i `&` spi f j `&` D) +
    \sum_(i < n) \sum_(l < p)
    ((srng f)`_i)%:E * m (spi f i `&` spi g l `&` D)); last first.
  congr adde; apply: eq_bigr => i _.
  rewrite ge0_sume_distrr // => j _; rewrite measure_ge0 //.
  by apply: measurableI => //; apply: measurableI; exact: SFun.mpi.
rewrite [X in _ = X + _]exchange_big.
rewrite -big_split; apply: eq_bigr => i _.
rewrite -big_split; apply: eq_bigr => j _.
rewrite -[in RHS](setIC (spi f i)).
by rewrite addEFin ge0_muleDl //;
  [rewrite addeC|exact: NNSFun_ge0|exact: NNSFun_ge0].
Qed.

End sintegralD.

Section le_sintegral.
Variables (T : measurableType) (point : T) (R : realType).
Variable m : {measure set T -> \bar R}.
Implicit Types D : set T.

Lemma eq_sintegral D (f g : presfun T R) : {in D, f =1 g} ->
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
  apply: uniq_perm; do 1? [by rewrite filter_uniq // PreSFun.uniq_rng].
  move=> r; rewrite !mem_filter; apply/andP/andP=> -[/set0P[t /= [gt Dt rg]]].
    split.
    - apply/set0P; exists t => //; split => //; rewrite /preimage /= fg//.
      by rewrite in_setE.
    - have := PreSFun.full_rng f; rewrite predeqE => /(_ r)[].
      rewrite /preimage /= -fg in gt; last by rewrite in_setE.
      have H : [set of f] r by exists t.
      by move/(_ H).
  split.
    - apply/set0P; exists t => //; split => //; rewrite /preimage /= -fg //.
      by rewrite in_setE.
    - have := PreSFun.full_rng g; rewrite predeqE => /(_ r)[].
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
pose gNf' := sfun_proj (sfun_add g (sfun_scale point (-1) f)) mD.
have gNf0 : forall x, 0 <= gNf' x.
  move=> x /=; rewrite /sfun_proj_f /= /sfun_scale_f /= mulN1r.
  have [xD|xD] := boolP (x \in D); last by rewrite mulr0.
  by rewrite mulr1 subr_ge0; apply/fg; rewrite -in_setE.
pose gNf := NNSFun.mk gNf0.
have gfgf : {in D, g =1 sfun_add f gNf}.
  move=> x /=; rewrite /sfun_proj_f /= => ->.
  by rewrite /sfun_scale_f mulr1 addrCA mulN1r subrr addr0.
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
rewrite [X in _ X](_ : _ = \big[setU/set0]_(y <- srng f)
    \big[setU/set0]_(x <- srng (g n) | c * y <= x)
      ((f @^-1` [set y]) `&` (g n @^-1` [set x]))); last first.
  rewrite predeqE => t; split.
    rewrite /= => fgcn; rewrite -bigcup_set.
    exists (f t); first exact: mem_img_srng.
    rewrite -bigcup_set_cond; exists (g n t) => //.
    by apply/andP; split => //; exact: mem_img_srng.
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
pose g1 n := nnsfun_proj f (measurable_fgeg c n).
have cg1g n : c%:E * sintegral mu D (g1 n) <= sintegral mu D (g n).
  rewrite -(sintegralM point mu c mD (g1 n)).
  apply: (@le_sintegral _ _ _ _ _ _ (nnsfun_scale point (g1 n) (ltW c0))) => //=.
  have : forall m x, D x -> (c * g1 m x <= g m x)%R.
    move=> m x Dx; rewrite /g1 nnsfun_projE /fleg /=; have [|] := boolP (x \in _).
      by rewrite in_setE => -[/=]; rewrite mulr1.
    by rewrite 2!mulr0 NNSFun.ge0.
  exact.
suff {cg1g}<- : lim (fun n => sintegral mu D (g1 n)) = sintegral mu D f.
  have is_cvg_g1 : cvg (fun n => sintegral mu D (g1 n)).
    apply: is_cvg_sintegral => //= x Dx m n mn.
    by have /lefP/(_ x) := le_ffleg c mn.
  rewrite -ereal_limrM // lee_lim//.
  - exact: ereal_is_cvgrM.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu D (g1 n)) --> sintegral mu D f by apply/cvg_lim.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(k < ssize f) ((srng f)`_k)%:E *
    mu (f @^-1` [set (srng f)`_k] `&` fleg c n `&` D))); last first.
  rewrite funeqE => n; rewrite sintegralE.
  transitivity (\sum_(x <- srng f) x%:E * mu (g1 n @^-1` [set x] `&` D)).
    rewrite (_ : srng (g1 n) = sfun_proj_rng f (fleg c n))//=.
    rewrite /sfun_proj_rng /=; case: ifPn=> [/orP[|/eqP cnT]|_].
    - rewrite mem_filter /= => /andP[].
      rewrite /preimage /= => /set0P[t [ft0 cnt]] f0.
      rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0// predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /sfun_proj_f /=; have [xcn|xcn] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite -in_setE.
      rewrite mulr0 => r0.
      by move: I0; rewrite predeqE => /(_ t)[+ _]; apply; rewrite -r0.
    - rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /sfun_proj_f /preimage /= cnT; have [xT|] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite cnT.
      by rewrite notin_setE => /(_ Logic.I).
    - rewrite /= big_cons mul0e add0e.
      rewrite big_filter big_mkcond; apply: eq_bigr => r _.
      case: ifPn => // /negPn/eqP I0.
      have [->|r0] := eqVneq r 0%R; first by rewrite mul0e.
      rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
      split => //=; move=> [/[swap] Dx].
      rewrite /sfun_proj_f /preimage /=; have [xT|_ ] := boolP (x \in _).
        rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
        by split => //; rewrite -in_setE.
      by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  rewrite big_tnth; apply: eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0%R) //=.
  have [fi0|fi0] := eqVneq ((srng f)`_i) 0%R; first by rewrite fi0 // 2!mul0e.
  congr (_%:E * mu _); rewrite predeqE => x; split => [|[]] /=.
  - rewrite /sfun_proj_f /preimage /= => -[/[swap] Dx].
    have [xcn|_] := boolP (_ \in fleg _ _).
      by rewrite mulr1 => <-; split => //; split=> //; rewrite -in_setE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE fi0).
  - rewrite /sfun_proj_f /preimage /= => -[fxi]; rewrite -in_setE => cnx Dx.
    by split => //; rewrite fxi cnx mulr1.
rewrite [X in X --> _](_ : _ = fun n => \sum_(x <- srng f) x%:E *
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
apply: ereal_lim_sum => [r n /NNSFuncdom_ge0 r0|r rf].
  by rewrite mule_ge0// measure_ge0.
apply: ereal_cvgrM => //.
rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n `&` D))); last first.
  by rewrite -setI_bigcupl -setI_bigcupr bigcup_fleg// -setIA setIid.
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

Section integral.
Variables (T : measurableType) (point : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).
Implicit Type D : set T.
Local Open Scope ereal_scope.

Definition nnintegral D (f : T -> \bar R) :=
  ereal_sup [set sintegral mu D g | g in
    [set g : nnsfun T R | forall x, D x -> (g x)%:E <= f x]].

Lemma nnintegral_sfun D (mD : measurable D) (f : nnsfun T R) :
  nnintegral D (EFin \o f) = sintegral mu D f.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gf <-]; exact: le_sintegral.
by apply: ereal_sup_ub => /=; exists f.
Qed.

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
  {in D, f =1 g} -> nnintegral D f = nnintegral D g.
Proof.
move=> fg; rewrite /nnintegral; congr ereal_sup; rewrite eqEsubset; split.
  by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite -fg// ?hf// in_setE.
by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite fg// ?hf// in_setE.
Qed.
Arguments eq_nnintegral {D} _ {f} _.

Lemma nnintegral0 D : nnintegral D (cst 0) = 0.
Proof.
pose cst0 : nnsfun T R := nnsfun_cst point (Nonneg.NngNum _ (ler0n _ 0)).
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub => /=; exists cst0 => //=.
  by rewrite sintegralE /= big_cons big_nil adde0 mul0e.
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, D x -> f x = 0%R.
  by move=> y ?; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin NNSFun.ge0.
rewrite /sintegral big1 //= => i _.
(* NB: improve? *)
have [->|/set0P[t [fit Dt]]] := eqVneq (spi f i `&` D) set0.
  by rewrite measure0 mule0.
by rewrite (spi_nth fit) f0 // mul0e.
Qed.

Definition integral D (f : T -> \bar R) :=
  nnintegral D (f ^\+) - nnintegral D (f ^\-).

Lemma eq_integral D (f g : T -> \bar R) : {in D, f =1 g} ->
  integral D f = integral D g.
Proof.
move=> fg; rewrite /integral (eq_nnintegral g^\+); last first.
  by move=> x Dx; rewrite /funenng (fg _ Dx).
rewrite [X in _ - X = _](eq_nnintegral g^\-)// => x Dx.
by rewrite /funennp (fg _ Dx).
Qed.

Lemma ge0_integralE D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) -> integral D f = nnintegral D f.
Proof.
move=> f0; rewrite /integral (eq_nnintegral _ (ge0_funenngE f0)).
by rewrite (eq_nnintegral _ (ge0_funennpE f0)) nnintegral0 sube0.
Qed.

Lemma integralE D (f : T -> \bar R) : integral D f =
  integral D (f ^\+) - integral D (f ^\-).
Proof.
rewrite [in LHS]/integral.
rewrite -ge0_integralE; last by move=> ? _; exact: funenng_ge0.
by rewrite -ge0_integralE // => ? _; exact: funennp_ge0.
Qed.

Lemma integral0 D : integral D (cst 0) = 0.
Proof.
rewrite /integral (_ : _^\+ = cst 0) ?nnintegral0; last first.
  by rewrite funeqE => t; rewrite (@ge0_funenngE _ _ setT)// in_setE.
rewrite (_ : _^\- = cst 0) ?nnintegral0 ?subee//.
by rewrite funeqE => t; rewrite (@ge0_funennpE _ _ setT)// in_setE.
Qed.

Lemma ge0_integral D (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) -> 0 <= integral D f.
Proof. by move=> f0; rewrite ge0_integralE// nnintegral_ge0. Qed.

Lemma integral_nnsfun D (mD : measurable D)
  (f : nnsfun T R) : integral D (EFin \o f) = sintegral mu D f.
Proof.
by rewrite -nnintegral_sfun// ge0_integralE// => x _; rewrite lee_fin.
Qed.

End integral.

Section nondecreasing_integral_limit.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).

Hypothesis f0 : forall x, D x -> (0 <= f x)%E.
Hypothesis mf : measurable_fun D f.
Variable (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Hypothesis gf : forall x, D x -> EFin \o g^~x --> f x.

Lemma nd_ge0_integral_lim : integral mu D f = lim (sintegral mu D \o g).
Proof.
rewrite ge0_integralE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x Dx.
  have <- : lim (EFin \o g^~ x) = f x.
    by apply/cvg_lim => //; apply: gf.
  have : (EFin \o g^~ x) --> ereal_sup [set of EFin \o g^~ x].
    apply: nondecreasing_ereal_cvg => p q pq /=; rewrite lee_fin.
    exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ub => /=; exists n.
have := lee_pinfty (nnintegral mu D f).
rewrite le_eqVlt => /predU1P[mufoo|mufoo]; last first.
  have /ub_ereal_sup_adherent : nnintegral mu D f \is a fin_num.
    by rewrite ge0_fin_numE // (nnintegral_ge0 point mu f0).
  rewrite -/(integral _ _) => h; apply: lee_adde => e.
  have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite NEFin lte_subl_addr// => fGe.
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
  move: (mufoo) => /eq_pinfty.
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
    f x \in EFin @` [set` I n.+1 k].
Proof.
move=> fxn; have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxn; case: (f x) => // /andP[].
have : f x \in EFin @` `[n%:R, n.+1%:R[%classic.
  rewrite in_setE /=; exists (fine (f x)).
    by rewrite in_itv /= -lee_fin -lte_fin (fineK fxfin).
  by rewrite fineK.
rewrite (bigsetU_dyadic_itv n) inE /= => -[r].
rewrite -bigcup_set => -[k /=].
rewrite mem_index_iota => nk Ir rfx.
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
  [set x | f x \in EFin @` [set` I n k]] else set0) `&` D.

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

Local Lemma mB n : measurable (B n).
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
have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxoo fx_gt0; case: (f x).
rewrite -(fineK fxfin) lte_fin in fx_gt0.
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
have K : (`|floor (fine (f x) * 2 ^+ n)| < n * 2 ^ n)%N.
  rewrite -ltz_nat gez0_abs; last first.
    by rewrite floor_ge0 mulr_ge0 // -?natrX// ?ler0n// ltW.
  rewrite -(@ltr_int R); rewrite (le_lt_trans (floor_le _)) // PoszM intrM.
  by rewrite -natrX ltr_pmul2r ?ltr0n ?expn_gt0// -lte_fin (fineK fxfin).
have xAnK : x \in A n (Ordinal K).
  rewrite inE /A; split => //.
  rewrite ifT //= inE /=; exists (fine (f x)); last by rewrite fineK.
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
       f x \in EFin @` [set` I n k]].
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
    have xAn1k : x \in A n.+1 k by rewrite in_setE /A kn2.
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
  (f x < +oo)%E -> (approx_fun^~ x) --> fine (f x).
Proof.
move=> Dx fxoo.
have fxfin : f x \is a fin_num.
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
have : fine (f x) < n%:R.
  near: n.
  exists `|floor (fine (f x))|.+1%N => //= p /=.
  rewrite -(@ler_nat R); apply: lt_le_trans.
  rewrite -addn1 natrD (_ : `| _ |%:R  = (floor (fine (f x)))%:~R); last first.
    by rewrite -[in RHS](@gez0_abs (floor _)) // floor_ge0 //; exact/le0R/f0.
  by rewrite -RfloorE lt_succ_Rfloor.
rewrite -lte_fin (fineK fxfin) => fxn.
have [approx_fun_nx0|] := f_ub_approx_fun fxn.
  by have := Hm _ mn; rewrite approx_fun_nx0.
move=> [k [/andP[k0 kn2n] ? ->]].
rewrite inE /= => -[r /=].
rewrite in_itv /= => /andP[k1 k2] rfx.
rewrite (@le_lt_trans _ _ (1 / 2 ^+ n)) //.
  rewrite ler_norml; apply/andP; split.
    rewrite ler_subr_addl -mulrBl -lee_fin (fineK fxfin) -rfx lee_fin.
    rewrite (le_trans _ k1)// ler_pmul2r ?invr_gt0 -?natrX ?ltr0n ?expn_gt0//.
    by rewrite -(@natrB _ _ 1) // ler_nat subn1 leq_pred.
  rewrite ler_subl_addr -mulrDl -lee_fin -(natrD _ 1) add1n.
  by rewrite fineK// ltW// -rfx lte_fin.
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
  D x -> EFin \o approx_fun^~x --> f x.
Proof.
move=> Dx; have := lee_pinfty (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx_fun := dvg_approx_fun Dx fxoo.
  have : {homo (approx_fun^~x) : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx_fun mn => /lefP; exact.
  move/nondecreasing_dvg_lt => /(_ dvg_approx_fun).
  by rewrite fxoo; exact/dvg_ereal_cvg.
rewrite -(@fineK _ (f x)); first exact: (cvg_comp (cvg_approx_fun f0 Dx fxoo)).
by rewrite fin_numElt fxoo andbT (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition nnsfun_approx : (nnsfun T R)^nat := fun n => nnsfun_add
  (nnsfun_sum point
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => nnsfun_ind point (Nonneg.NngNum _ (k2n_ge0 (Ordinal h))) (mA n k)
      | right _ => nnsfun0 point R
     end) (n * 2 ^ n)%N)
  (nnsfun_ind point (Nonneg.NngNum _ (ler0n _ n)) (mB n)).

Lemma nnsfun_approxE n : nnsfun_approx n = approx_fun n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite nnsfun_sumE; congr (_ + _).
apply: eq_bigr => i _; case: Bool.bool_dec => //.
by move/negP; rewrite ltn_ord.
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o nnsfun_approx^~x --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx_fun.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof. by move=> m n mn; rewrite !nnsfun_approxE; exact: nd_approx_fun. Qed.

Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : (nnsfun T R)^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~x --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|exact: cvg_nnsfun_approx].
Qed.

End approximation.

Section approximation_sfun.
Variables (T : measurableType) (point : T) (R : realType).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma approximation_sfun :
  exists g : (sfun T R)^nat, (forall x, D x -> EFin \o g^~x --> f x).
Proof.
have fp0 : (forall x, D x -> 0 <= f^\+ x)%E by move=> x Dx; apply: funenng_ge0.
have mfp : measurable_fun D f^\+.
  by apply: emeasurable_fun_max => //; exact: measurable_fun_cst.
have fn0 : (forall x, D x -> 0 <= f^\- x)%E by move=> x Dx; apply: funennp_ge0.
have mfn : measurable_fun D f^\-.
  apply: emeasurable_fun_max => //; first exact: emeasurable_funN.
  exact: measurable_fun_cst.
have [fp_ [fp_nd fp_cvg]] := approximation point mD mfp fp0.
have [fn_ [fn_nd fn_cvg]] := approximation point mD mfn fn0.
exists (fun n => sfun_add (fp_ n) (sfun_scale point (-1) (fn_ n))) => x Dx /=.
rewrite [X in X --> _](_ : _ =
    (EFin \o fp_^~ x \+ (-%E \o EFin \o fn_^~ x))%E); last first.
  rewrite funeqE => n /=; rewrite -addEFin//; congr (_%:E).
  by rewrite /sfun_scale_f mulN1r.
rewrite (funenngnnp f); apply: ereal_cvgD.
- exact: add_def_funennpg.
- exact: fp_cvg.
- apply: ereal_cvgN.
  exact: fn_cvg.
Qed.

End approximation_sfun.

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
rewrite -(@fineK _ (g i x)); last first.
  by rewrite fin_numElt gixoo andbT (lt_le_trans _ (g0 i Dx)) ?lte_ninfty.
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

Lemma ge0_integralM_EFin k : 0 <= k ->
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
  rewrite [X in X --> _](_ : _ = (fun n => k%:E * (g n x)%:E))%E ?funeqE//.
  by apply: ereal_cvgrM => //; exact: gf1.
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
have f1tfin : f1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (f10 Dt))// lte_ninfty.
have := gf1 _ Dt.
rewrite -(fineK f1tfin) => /ereal_cvg_real[ft_near].
set u_ := (X in X --> _) => u_f1 g1f1.
have <- : lim u_ = fine (f1 t).
  by apply/cvg_lim => //; exact: Rhausdorff.
rewrite lee_fin; apply: nondecreasing_cvg_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_g1.
by apply/cvg_ex; eexists; exact: u_f1.
Grab Existential Variables. all: end_near. Qed.

End semi_linearity.

Section emeasurable_fun.
Variables (T : measurableType) (point : T) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma emeasurable_funD D f g : measurable D ->
  (forall x, D x -> (f x +? g x)%E) ->
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x + g x)%E.
Proof.
move=> mD fg mf mg.
have [f_ f_cvg] := approximation_sfun point mD mf.
have [g_ g_cvg] := approximation_sfun point mD mg.
apply: (@emeasurable_fun_cvg _ _ _ (fun n x => (f_ n x + g_ n x)%:E)) => //.
  move=> n; apply: measurable_fun_comp_EFin.
  by apply: measurable_funD => //; exact: measurable_sfun.
move=> x Dx.
under eq_fun do rewrite addEFin.
by apply: ereal_cvgD; [exact: fg|exact: f_cvg|exact: g_cvg].
Qed.

Lemma emeasurable_funB D f g : measurable D ->
  (forall x, D x -> (f x +? - g x)%E) ->
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x - g x)%E.
Proof.
by move=> mD fg mf mg; apply: emeasurable_funD => //; exact: emeasurable_funN.
Qed.

End emeasurable_fun.

Section measurable_fun_sum.
Variables (T : measurableType) (point : T) (R : realType) (D : set T).
Variables (f : (T -> \bar R)^nat).
Hypotheses (mD : measurable D) (mf : forall n, measurable_fun D (f n)).
Hypotheses (f0 : (forall n x, D x -> 0 <= f n x)%E).

Lemma measurable_fun_sum n : measurable_fun D (fun x => \sum_(0 <= i < n) f i x)%E.
Proof.
elim: n => [|n ih].
  by under eq_fun do rewrite big_mkord //= big_ord0; exact: measurable_fun_cst.
under eq_fun do rewrite big_nat_recr //=; apply: emeasurable_funD => // => x Dx.
apply: ge0_adde_def => //; rewrite inE; last exact: f0.
by apply: sume_ge0 => // => m _; exact: f0.
Qed.

End measurable_fun_sum.

Section ge0_integral_sum.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypotheses (mf : forall n, measurable_fun D (f n)) (f0 : (forall n x, D x -> 0 <= f n x)%E).

Lemma ge0_integral_sum n :
  (integral mu D (fun x => \sum_(0 <= k < n) f k x) = \sum_(k < n) integral mu D (f k))%E.
Proof.
elim: n => [|n ih].
  rewrite big_ord0; under eq_fun do rewrite big_mkord big_ord0.
  by rewrite integral0.
rewrite big_ord_recr /= -ih -ge0_integralD//.
- by apply: eq_integral => x Dx; rewrite big_nat_recr.
- by move=> x Dx; apply: sume_ge0 => // k _; exact: f0.
- exact: measurable_fun_sum.
- by move=> x Dx; exact: f0.
Qed.

End ge0_integral_sum.

Section monotone_convergence_theorem.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (g : (T -> \bar R)^nat).
Hypothesis mg : forall n, measurable_fun D (g n).
Hypothesis g0 : forall n x, D x -> (0 <= g n x)%E.
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Let f := fun x => lim (g^~ x).

Let is_cvg_g t : D t -> cvg (g^~ t).
Proof. by move=> ?; apply: ereal_nondecreasing_is_cvg => m n ?; apply/nd_g. Qed.

Local Definition g2' n : (T -> R)^nat := approx_fun D (g n).
Local Definition g2 n : (nnsfun T R)^nat := nnsfun_approx point mD (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => \big[maxr/0]_(i < k) (g2' i k) t.
Local Definition max_g2 : (nnsfun T R)^nat :=
  fun k => nnsfun_bigmax point (g2^~ k) k.

Local Lemma max_g2E : max_g2 = max_g2' :> (T -> R)^nat.
Proof.
rewrite funeq2E => n t; rewrite nnsfun_bigmaxE.
by under eq_bigr do rewrite nnsfun_approxE.
Qed.

Let is_cvg_g2 n t : cvg (EFin \o (fun x : nat => g2 n x t)).
Proof.
apply: ereal_nondecreasing_is_cvg => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx_fun.
Qed.

Local Lemma nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => t; rewrite 2!nnsfun_bigmaxE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 t)) //.
  apply: le_bigmax => i _; apply: (nondecreasing_seqP (g2 i ^~ t)).2 => a b ab.
  by rewrite !nnsfun_approxE; exact/lefP/(nd_approx_fun D (g i) ab).
rewrite (bigmaxD1 ord_max)// le_maxr; apply/orP; right.
rewrite [X in _ <= X](eq_bigl (fun i => nat_of_ord i < n)%N); last first.
  move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
  by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
by rewrite (big_ord_narrow (leqnSn n)).
Qed.

Let is_cvg_max_g2 t : cvg (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Local Lemma max_g2_g k x : D x -> ((max_g2 k x)%:E <= g k x)%O.
Proof.
move=> Dx; rewrite nnsfun_bigmaxE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x))%E; last first.
  by apply/bigmax_lerP; split => //; apply: g0.
rewrite (@big_morph _ _ EFin 0%:E maxe) //; last by move=> *; rewrite maxEFin.
apply: le_bigmax => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx_fun _ _ _))// nd_g// ltnW.
Qed.

Local Lemma lim_max_g2_f t : D t -> (lim (EFin \o max_g2 ^~ t) <= f t)%E.
Proof.
move=> Dt; apply: lee_lim => //; first exact: is_cvg_g.
by near=> n; exact/max_g2_g.
Grab Existential Variables. all: end_near. Qed.

Local Lemma lim_g2_max_g2 t n : (lim (EFin\o g2 n ^~ t) <= lim (EFin \o max_g2 ^~ t))%E.
Proof.
apply: lee_lim => //.
near=> k; rewrite /= nnsfun_bigmaxE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (@bigmax_sup _ _ _ (Ordinal nk)).
Grab Existential Variables. all: end_near. Qed.

Local Lemma cvg_max_g2_f t : D t -> EFin \o max_g2 ^~ t --> f t.
Proof.
move=> Dt; have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f Dt)) // (cvg_lim _ g_l).
have := lee_pinfty l; rewrite le_eqVlt => /predU1P[->|loo].
  by rewrite lee_pinfty.
rewrite -(cvg_lim _ g_l) //= ereal_lim_le => //; first exact/is_cvg_g.
near=> n.
have := lee_pinfty (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
- have h := dvg_approx_fun Dt fntoo.
  have g2oo : lim (EFin \o g2 n ^~ t) = +oo%E.
    apply/cvg_lim => //; apply/dvg_ereal_cvg.
    under [X in X --> _]eq_fun do rewrite nnsfun_approxE.
    exact/(nondecreasing_dvg_lt _ h)/lef_at/nd_approx_fun.
  have -> : lim (EFin \o max_g2 ^~ t) = +oo%E.
    by have := lim_g2_max_g2 t n; rewrite g2oo lee_pinfty_eq => /eqP.
  by rewrite lee_pinfty.
- have approx_fun_g_g := cvg_approx_fun (g0 n) Dt fntoo.
  have <- : lim (EFin \o g2 n ^~ t) = g n t.
    have /cvg_lim <- // : EFin \o (approx_fun D (g n))^~ t --> g n t.
      move/(@cvg_comp _ _ _ _ EFin) : approx_fun_g_g; apply.
      by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
    rewrite (_ : _ \o _ = EFin \o (approx_fun D (g n))^~ t)// funeqE => m.
    by rewrite [in RHS]/= -(nnsfun_approxE point).
  exact: (le_trans _ (lim_g2_max_g2 t n)).
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
  by apply: ereal_lim_le => //; [exact: ereal_nondecreasing_is_cvg|exact: nearW].
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

Section integral_series.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypotheses (mf : forall n, measurable_fun D (f n)) (f0 : forall n x, D x -> (0 <= f n x)%E).

Lemma integral_sum :
  integral mu D (fun x => \sum_(n <oo) f n x) = \sum_(n <oo) (integral mu D (f n)).
Proof.
rewrite monotone_convergence //.
- rewrite -lim_mkord (_ : (fun n => _) = (fun n => (\sum_(k < n) integral mu D (f k))%E))//.
  by rewrite funeqE => n; exact: ge0_integral_sum.
- by move=> n; exact: measurable_fun_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_series.

(* NB: not used *)
Lemma EFin_itv2 (R : realType) (r : R) :
  [set s | s%:E < r%:E]%E = `]-oo, r[%classic.
Proof.
by rewrite predeqE => s; split => [|]; rewrite /preimage /= ?lte_fin;
  [move=> rs; rewrite in_itv /= rs | rewrite in_itv /=].
Qed.

(* NB: not used *)
Lemma preimage_setC1 (T : Type) (d : unit) (rT : porderType d) (f : T -> rT)
    (y : rT) :
  f @^-1` [set~ y] = [set x | f x != y].
Proof.
rewrite predeqE => t; split => /=.
  by rewrite /preimage /= => /eqP.
by move=> fty; apply/eqP.
Qed.

(* TODO: move *)
Lemma lim_ereal_inf_EFin (T : Type) (R : realType) (f : (T -> R)^nat) :
  (forall t, cvg (f^~t : _ -> R^o)) ->
  (fun t => lim_ereal_inf (EFin \o f^~t)) = (fun t => (lim (f^~t))%:E).
Proof.
move=> cf; rewrite funeqE => t.
rewrite -EFin_lim //; apply/eqP.
rewrite is_cvg_lim_ereal_infE //.
apply: continuous_is_cvg; last exact: cf.
by move=> l ftl.
Qed.

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
- rewrite addeC -lee_subl_addr//; apply: lb_ereal_inf => /= _ [m /= mn] <-.
  rewrite lee_subl_addr//; apply: ereal_inf_lb.
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
    apply; apply: einfs_le_esups.
  move: (esupl) => /cvg_lim => /(_ (@ereal_hausdorff R)).
  by rewrite /lim_ereal_sup => ->.
by apply: (@ereal_squeeze _ (cst 0%E)) => //; [exact: nearW|exact: cvg_cst].
Qed.
(* /TODO: move *)

(* generalization of ge0_integralM_EFin to a constant potentially +oo
   using the monotone convergence theorem *)
Section ge0_integralM.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma ge0_integralM (k : \bar R) : (forall x, D x -> (0 <= f x)%E) ->
  (0 <= k)%E -> integral mu D (fun x => k * f x)%E = (k * integral mu D f)%E.
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralM_EFin.
pose g : (T -> \bar R)^nat := (fun n x => n%:R%:E * f x)%E.
have mg n : measurable_fun D (g n) by exact: emeasurable_funeM.
have g0 n x : D x -> (0 <= g n x)%E.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g^~x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => lim (g^~ x).
transitivity (integral mu D (fun x => lim (g^~ x))).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0%E (f x).
  - rewrite gt0_mulpinfty//; apply/ereal_cvgPpinfty => M M0.
    rewrite /g; case: (f x) fx0 => [r|_|//]; last first.
      exists 1%N => // m /= m0.
      by rewrite mulrinfty gtr0_sg// ?mul1e ?lee_pinfty// ltr0n.
    rewrite lte_fin => r0.
    near=> n; rewrite lee_fin -ler_pdivr_mulr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    by rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0// divr_ge0// ltW.
  - rewrite lt0_mulpinfty//; apply/ereal_cvgPninfty => M M0.
    rewrite /g; case: (f x) fx0 => [r|//|_]; last first.
      exists 1%N => // m /= m0.
      by rewrite mulrinfty gtr0_sg// ?ltr0n// mul1e ?lee_ninfty.
    rewrite lte_fin => r0.
    near=> n; rewrite lee_fin -ler_ndivr_mulr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0// -mulrNN.
    by rewrite mulr_ge0// ler_oppr oppr0 ltW// invr_lt0.
  - rewrite -fx0 mule0 /g -fx0 [X in X @ _ --> _](_ : _ = cst 0%E).
      exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite mule0.
rewrite (monotone_convergence point mu mD mg g0 nd_g).
rewrite (_ : (fun n => _) = (fun n => n%:R%:E * integral mu D f)%E); last first.
  by rewrite funeqE => n; rewrite ge0_integralM_EFin.
have : (0 <= integral mu D f)%E by exact: ge0_integral.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  rewrite mule0 (_ : (fun n => _) = cst 0%E) ?lim_cst//.
  by under eq_fun do rewrite mule0.
rewrite gt0_mulpinfty//; apply/cvg_lim => //; apply/ereal_cvgPpinfty => M M0.
near=> n; have [ifoo|] := ltP (integral mu D f) +oo%E; last first.
  rewrite lee_pinfty_eq => /eqP ->;  rewrite mulrinfty muleC.
  rewrite gt0_mulpinfty ?lee_pinfty//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (integral mu D f)); last first.
  by rewrite fin_numElt ifoo andbT (le_lt_trans _ if_gt0)// lee_ninfty.
rewrite -lee_pdivr_mulr//; last first.
  by move: if_gt0 ifoo; case: (integral mu D f).
near: n.
exists `|ceil (M * (fine (integral mu D f))^-1)|%N => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
rewrite lee_fin natr_absz ger0_norm ?ceil_ge//.
rewrite ceil_ge0// mulr_ge0 => //; first exact: ltW.
by rewrite invr_ge0; apply: le0R; exact: ge0_integral.
Grab Existential Variables. all: end_near. Qed.

End ge0_integralM.

Section fatou.
Variables (T : measurableType) (point : T) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> (0 <= f n x)%E.

Lemma fatou : (integral mu D (fun x => lim_ereal_inf (f^~ x)) <=
  lim_ereal_inf (fun n => integral mu D (f n)))%E.
Proof.
pose g n := fun x => ereal_inf [set f k x | k in [set k | k >= n]%N].
have mg :=  measurable_fun_ereal_inf mD mf.
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

Section integralN.
Variables (T : measurableType) (point : T) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integralN D (f : T -> \bar R) : integral mu D f^\+ +? (- integral mu D f^\-) ->
  integral mu D (-%E \o f) = - integral mu D f.
Proof.
have [f_fin _|] := boolP (integral mu D f^\- \is a fin_num).
  rewrite integralE// [in RHS]integralE// oppeD ?fin_numN// oppeK addeC.
  by rewrite funennpN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -lee_ninfty_eq; apply/negP.
  rewrite -ltNge (lt_le_trans _ (ge0_integral _ _ _))// ?lte_ninfty// => *.
  exact: funennp_ge0.
rewrite nfoo adde_defEninfty.
rewrite -lee_pinfty_eq -ltNge lte_pinfty_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE// [in RHS]integralE// nfoo [in RHS]addeC oppeD//.
  by rewrite funennpN.
by rewrite integralE// [in RHS]integralE// funenngN funennpN nfoo pfoo.
Qed.

Lemma ge0_integralN (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> integral mu D (-%E \o f) = - integral mu D f.
Proof.
move=> f0; rewrite integralN // (eq_integral _ (ge0_funennpE _))// integral0//.
by rewrite oppe0 fin_num_adde_def.
Qed.

End integralN.

Section integral_cst.
Variables (T : measurableType) (point : T) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma sintegral_cst (x : {nonneg R}) :
  sintegral mu D (nnpresfun_cst point x) = (x%:nngnum%:E * mu D)%E.
Proof.
rewrite sintegralE/= big_cons big_nil adde0; congr (_ * _)%E.
by rewrite [X in mu (X `&` _)](_ : _ = setT) ?setTI// predeqE.
Qed.

Lemma integral_cst (x : R) : (0 <= x)%R ->
  integral mu D (EFin \o cst x) = (x%:E * mu D)%E.
Proof.
move=> x0; rewrite ge0_integralE//.
rewrite (_ : cst x = nnsfun_cst point (Nonneg.NngNum _ x0)) //. (*TODO: implicts of NNgnum*)
by rewrite nnintegral_sfun// sintegral_cst/=.
Qed.

Lemma integral_cst_pinfty : mu D != 0%E -> integral mu D (cst +oo%E) = +oo%E.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => lim (g^~ t)) = cst +oo%E.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/dvg_ereal_cvg/cvgPpinfty=> M; exists `|ceil M|%N => //= m.
  rewrite /= -(ler_nat R); apply: le_trans.
  by rewrite (le_trans (ceil_ge _))// natr_absz ler_int ler_norm.
rewrite monotone_convergence //.
- rewrite /g (_ : (fun n => _) = (fun n => n%:R%:E * mu D))%E; last first.
    by rewrite funeqE => n; rewrite -integral_cst.
  apply/cvg_lim => //; apply/ereal_cvgPpinfty => M M0.
  have [muDoo|muDoo] := ltP (mu D) +oo%E; last first.
    exists 1%N => // m /= m0.
    move: muDoo; rewrite lee_pinfty_eq => /eqP ->.
    by rewrite mulrinfty gtr0_sg ?mul1e ?lee_pinfty// ltr0n.
  exists `|ceil (M / fine (mu D))|%N => // m /=.
  rewrite -(ler_nat R) => MDm.
  rewrite -(@fineK _ (mu D)); last by rewrite ge0_fin_numE// measure_ge0.
  rewrite -lee_pdivr_mulr; last first.
    apply: lt0R.
    by rewrite muDoo andbT lt_neqAle measure_ge0// andbT eq_sym.
  rewrite lee_fin.
  apply: le_trans MDm.
  by rewrite natr_absz (le_trans (ceil_ge _))// ler_int ler_norm.
- by move=> n; exact: measurable_fun_cst.
- by move=> n x Dx; rewrite /cst lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.
End integral_cst.

Section integral_ind.
Variables (T : measurableType) (point : T) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma sintegral_ind (x : {nonneg R}) (E : set T) (mE : measurable E) :
  sintegral mu D (nnpresfun_ind point x E) = (x%:nngnum%:E * mu (D `&` E))%E.
Proof.
rewrite sintegralE.
rewrite srng_presfun_proj.
rewrite /sfun_proj_rng.
rewrite /=.
rewrite (_ : sfun_cst_f x%:nngnum @^-1` [set x%:nngnum] = setT) ?setTI; last first.
  by rewrite predeqE.
have set0T : (set0 == setT :> set T) = false.
  by apply/negbTE/negP => /eqP; rewrite predeqE => /(_ point)[_]; apply.
have [/eqP ->|E0]/= := boolP (E == set0).
  by rewrite set0T big_cons mul0e add0e big_nil setI0 measure0 mule0.
case: ifPn => [/orP[|/eqP ->]|].
- by rewrite inE => /eqP <-; rewrite big_cons mul0e add0e big_nil mul0e.
- rewrite big_cons big_nil adde0 setIC; congr (_ * mu (_ `&` _))%E.
  rewrite predeqE => t; split => // _.
  rewrite /sfun_proj_f /=.
  by rewrite /preimage /= /sfun_cst_f /= /cst /= in_setT mulr1.
- rewrite negb_or => /andP[]; rewrite inE => x0 ET.
  rewrite !big_cons big_nil adde0 mul0e add0e.
  rewrite setIC; congr (_ * mu (_ `&` _))%E.
  rewrite /preimage /= predeqE => t.
  rewrite /sfun_proj_f /=.
  rewrite /sfun_cst_f /=.
  rewrite /cst /=.
  rewrite -(in_setE E).
  case: (t \in E); first by rewrite mulr1.
  by rewrite mulr0; split => // /eqP; rewrite (negbTE x0).
Qed.

Lemma integral_ind (x : {nonneg R}) (E : set T) (mE : measurable E) :
  integral mu D (EFin \o nnsfun_ind point x mE) =
    (x%:nngnum%:E * mu (D `&` E))%E.
Proof.
rewrite ge0_integralE//; last by move=> t Dt; rewrite lee_fin.
by rewrite nnintegral_sfun// sintegral_ind.
Qed.

End integral_ind.

Section simple_function_integral2.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (f : sfun T R).
Let n := ssize f.
Let A := spi f.
Let a := srng f.
Local Open Scope ereal_scope.

(* TODO: rename *)
Lemma sintegralE2 : sintegral mu D f =
  \sum_(k < n) (a`_k)%:E * sintegral mu D (presfun_ind point 1%R (spi f k)).
Proof.
rewrite {1}/sintegral; apply: eq_bigr => k _; congr (_ * _)%E.
rewrite sintegral_ind ?mul1e 1?setIC//.
by apply SFun.mpi.
Qed.

End simple_function_integral2.

Section integral_ind_lemmas.
Variables (T : measurableType) (point : T) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}).

Lemma sintegral_ind_cst (x : {nonneg R}) (E : set T) (mE : measurable E) :
  sintegral mu setT (nnsfun_ind point x mE) = sintegral mu E (nnsfun_cst point x).
Proof.
by rewrite sintegral_ind// sintegral_cst setTI.
Qed.

End integral_ind_lemmas.

Section integrable.
Variables (T : measurableType) (point : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Definition integrable (D : set T) (f : T -> \bar R) :=
  measurable_fun D f /\
  (integral mu D (fun x => `|f x|) < +oo)%E.

Definition Rintegral (D : set T) (f : T -> \bar R) := fine (integral mu D f).

Lemma le_integrable (D : set T) (f1 f2 : T -> \bar R) :
  measurable D -> measurable_fun D f1 ->
  (forall x, D x -> `|f1 x| <= `|f2 x|)%E ->
  integrable D f2 -> integrable D f1.
Proof.
move=> mD mf1 f1f2 [mf2 f2oo]; split => //; rewrite (le_lt_trans _ f2oo) //.
apply: ge0_le_integral => //.
- by move=> t Dt; exact: abse_ge0.
- apply: measurable_fun_comp => //; apply: measurable_fun_abse.
  exact: measurableT.
- by move=> t Dt; exact: abse_ge0.
Qed.

Lemma integrableN (D : set T) (f1 : T -> R) : measurable D ->
  integrable D (EFin \o f1) ->
  integrable D (-%E \o EFin \o f1).
Proof.
move=> mD [mf1 f1oo].
split.
  rewrite /comp; apply: measurable_fun_comp => //.
  by apply: emeasurable_fun_minus; exact: measurableT.
rewrite /comp.
by under eq_fun do rewrite abseN.
Qed.

Lemma integrableK (D : set T) (k : R) (f1 : T -> R) : measurable D ->
  integrable D (EFin \o f1) ->
  integrable D (fun x => k%:E * (f1 x)%:E)%E.
Proof.
move=> mD [mf1 f1oo].
split.
  exact: emeasurable_funeM.
under eq_fun do rewrite abseM.
rewrite (ge0_integralM point mu mD).
- by rewrite lte_mul_pinfty// abse_ge0.
- apply: measurable_fun_comp => //.
  by apply: measurable_fun_abse; exact: measurableT.
- by move=> x Dx; rewrite lee_fin.
- by rewrite lee_fin.
Qed.

Lemma integrableD (D : set T) (f1 f2 : T -> R) : measurable D ->
  integrable D (EFin \o f1) -> integrable D (EFin \o f2) ->
  integrable D (fun x => (f1 x)%:E + (f2 x)%:E)%E.
Proof.
move=> mD [mf1 f1oo] [mf2 f2oo].
split; first exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (integral mu D
    (fun x => `|(f1 x)%:E| + `|(f2 x)%:E|)%E)).
  apply ge0_le_integral => //; first by move=> t _; apply: abse_ge0.
  - apply: measurable_fun_comp.
      by apply: measurable_fun_abse; exact: measurableT.
    exact: emeasurable_funD.
  - by move=> x _; apply: adde_ge0; rewrite lee_fin.
  - by move=> x _; exact: lee_abs_add.
rewrite ge0_integralD //.
- exact: lte_add_pinfty.
- by move=> x _; exact: abse_ge0.
- apply: measurable_fun_comp => //.
  by apply: measurable_fun_abse; exact: measurableT.
- by move=> x _; exact: abse_ge0.
- apply: measurable_fun_comp => //.
  by apply: measurable_fun_abse; exact: measurableT.
Qed.

Lemma integrableB (D : set T) (f1 f2 : T -> R) : measurable D ->
  integrable D (EFin \o f1) -> integrable D (EFin \o f2) ->
  integrable D (fun x => (f1 x)%:E - (f2 x)%:E)%E.
Proof. by move=> mD if1 if2; apply/(integrableD mD if1)/integrableN. Qed.

Lemma integrable_add_def (D : set T) f : measurable D -> integrable D f ->
  (integral mu D f^\+ +? - integral mu D f^\-)%E.
Proof.
move=> mD [mf]; rewrite -[(fun x => _)]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 4 first.
  by move=> x _; exact: funenng_ge0.
  exact: emeasurable_fun_funenng.
  by move=> x _; exact: funennp_ge0.
  exact: emeasurable_fun_funennp.
apply: ltpinfty_adde_def.
- apply: le_lt_trans foo.
  by rewrite lee_addl// ge0_integral// => x _; exact: funennp_ge0.
- rewrite inE (@le_lt_trans _ _ 0%E)// ?lte_pinfty//.
  by rewrite lee_oppl oppe0 ge0_integral// => x _; exact: funennp_ge0.
Qed.

End integrable.

Section integrable_ae.
Variables (T : measurableType) (point : T) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Hypothesis fint : integrable mu D f.

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0%E.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ]%E.
have mE : measurable E.
  rewrite [X in measurable X](_ : _ = f @^-1` [set -oo; +oo]%E `&` D).
    by apply: fint.1 => //; apply: measurableU; exact: emeasurable_set1.
  rewrite predeqE => t; split=> [[/eqP ftoo Dt]|[]].
    split => //.
    by move: ftoo; rewrite /preimage /= eqe_absl => /andP[/orP[|]/eqP]; tauto.
  by rewrite /preimage /= => -[|]; rewrite /E /= => ->.
have [ET|ET] := eqVneq E setT.
  have foo : (forall t, `|f t| = +oo)%E by move=> t; have [] : E t by rewrite ET.
  move: fint.2.
  suff: integral mu D (abse \o f) = +oo%E by move=> ->; rewrite ltxx.
   rewrite (_ : abse \o f = cst +oo)%E ?integral_cst_pinfty //.
  by rewrite funeqE => t; rewrite /= foo.
suff: mu E = 0%E.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt ftfin]; split => //.
  apply/eqP; rewrite eqe_absl lee_pinfty andbT.
  by move/negP : ftfin; rewrite fin_numE negb_and 2!negbK orbC.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M [M0 muM]] : exists2 M, 0 <= M &
                    (forall n, n%:R%:E * mu (E `&` D) <= M%:E)%E.
  exists (fine (integral mu D (abse \o f))).
    by apply/le0R/ge0_integral => // x Dx; exact: abse_ge0.
  move=> n.
  pose N : sfun T R := sfun_ind point n%:R mE.
  have <- : integral mu D (EFin \o N) = (n%:R%:E * mu (E `&` D))%E.
    by rewrite integral_ind //= 1?setIC.
  rewrite fineK//; last first.
    case: fint => _ foo; rewrite ge0_fin_numE//.
    by apply: ge0_integral => // t Dt; rewrite abse_ge0.
  apply: ge0_le_integral => //.
  - by move=> t Dt; rewrite lee_fin.
  - by apply: measurable_fun_comp_EFin;exact: measurable_sfun.
  - by move=> t Dt; apply: abse_ge0.
  - move=> x Dx; rewrite /N /=.
    rewrite /sfun_proj_f /= /sfun_cst_f /=.
    have [xE|xE] := boolP (x \in E).
      by move: xE; rewrite /E inE /= => -[->]; rewrite lee_pinfty.
    by rewrite mulr0 abse_ge0.
apply/eqP/negPn/negP => /eqP muED0.
move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo%E; last first.
  rewrite lee_pinfty_eq => /eqP ->.
  by exists 1%N; rewrite mul1e lee_pinfty_eq.
exists `|ceil (M * (fine (mu (E `&` D)))^-1)|%N.+1.
apply/negP; rewrite -ltNge.
rewrite -[X in (_ * X)%E](@fineK _ (mu (E `&` D))); last first.
  rewrite fin_numElt muEDoo andbT.
  by rewrite (lt_le_trans _ (measure_ge0 _ _))// ?lte_ninfty//; exact: measurableI.
rewrite lte_fin -ltr_pdivr_mulr.
  rewrite -addn1 natrD natr_absz ger0_norm.
    by rewrite (le_lt_trans (ceil_ge _))// ltr_addl.
  by rewrite ceil_ge0// divr_ge0//; apply/le0R/measure_ge0; exact: measurableI.
rewrite -lte_fin fineK.
  rewrite lt_neqAle measure_ge0// ?andbT; last exact: measurableI.
  suff: E `&` D = E by move=> ->; apply/eqP/nesym.
  by rewrite predeqE => t; split; case.
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section linearityM.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 : T -> \bar R).
Hypothesis if1 : integrable mu D f1.

Lemma integralM (r : R) :
  integral mu D (fun x => r%:E * f1 x)%E = (r%:E * integral mu D f1)%E.
Proof.
have [r0|r0|->] := ltgtP r 0; last first.
  by under eq_fun do rewrite mul0e; rewrite mul0e integral0.
- rewrite [in LHS]integralE// gt0_funenngM// gt0_funennpM//.
  rewrite (ge0_integralM_EFin _ _ _ _ _ (ltW r0)) //; last 2 first.
    by move=> x Dx; exact: funenng_ge0.
    by apply: emeasurable_fun_funenng => //; case: if1.
  rewrite (ge0_integralM_EFin _ _ _ _ _ (ltW r0)) //; last 2 first.
    by move=> x Dx; exact: funenng_ge0.
    by apply: emeasurable_fun_funennp => //; case: if1.
  rewrite -mulrEBr 1?[in RHS]integralE//.
  by apply: integrable_add_def; case: if1.
- rewrite [in LHS]integralE// lt0_funenngM// lt0_funennpM//.
  rewrite ge0_integralM_EFin //; last 3 first.
    by move=> x Dx; exact: funenng_ge0.
    by apply: emeasurable_fun_funennp => //; case: if1.
    by rewrite -ler_oppr oppr0 ltW.
  rewrite ge0_integralM_EFin //; last 3 first.
    by move=> x Dx; exact: funenng_ge0.
    by apply: emeasurable_fun_funenng => //; case: if1.
    by rewrite -ler_oppr oppr0 ltW.
  rewrite -mulNe -NEFin opprK addeC NEFin mulNe -mulrEBr; last first.
    by apply: integrable_add_def; case: if1.
  by rewrite [in RHS]integralE.
Qed.

End linearityM.

Section integrable.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (g1 : T -> \bar R).
Hypothesis ig1 : integrable mu D g1.

(* TODO: wip *)
Lemma integral_funennp_lt_pinfty : (integral mu D g1^\- < +oo)%E.
Proof.
move: ig1 => [mg1]; apply: le_lt_trans; apply ge0_le_integral => //.
- by move=> x Dx; exact: funennp_ge0.
- by apply: emeasurable_fun_funennp => //; exact: emeasurable_funN.
- by move=> x Dx; exact: abse_ge0.
- move=> x Dx; have [g1x0|/ltW g1x0] := leP (g1 x) 0%E.
    rewrite lee0_abs// /funennp.
    by move: g1x0; rewrite -{1}oppe0 -lee_oppr => /max_idPl ->.
  rewrite gee0_abs// /funennp.
  by move: (g1x0); rewrite -{1}oppe0 -lee_oppl => /max_idPr ->.
Qed.

Lemma integral_funenng_lt_pinfty : (integral mu D g1^\+ < +oo)%E.
Proof.
move: ig1 => [mg1]; apply: le_lt_trans; apply ge0_le_integral => //.
- by move=> x Dx; exact: funenng_ge0.
- by apply: emeasurable_fun_funenng => //; exact: emeasurable_funN.
- by move=> x Dx; exact: abse_ge0.
- move=> x Dx; have [g1x0|/ltW g1x0] := leP (g1 x) 0%E.
    rewrite lee0_abs// /funenng.
    by move: (g1x0) => /max_idPr ->; rewrite -lee_oppr oppe0.
  by rewrite gee0_abs// /funenng; move: (g1x0) => /max_idPl ->.
Qed.

End integrable.

Section linearity.
Variables (T : measurableType) (point : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> R).
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : integrable mu D g1.
Hypothesis if2 : integrable mu D g2.

Lemma integralD_EFin :
  integral mu D (g1 \+ g2)%E = (integral mu D g1 + integral mu D g2)%E.
Proof.
suff: (integral mu D (g1 \+ g2)^\+ + integral mu D g1^\- + integral mu D g2^\-
   = integral mu D (g1 \+ g2)^\- + integral mu D g1^\+ + integral mu D g2^\+)%E.
  move=> H.
  rewrite [in LHS](integralE point).
  move/eqP : H.
  rewrite -[in X in _ == X]addeA [in X in _ == X]addeC.
  have g12nng : (integral mu D g1^\+ + integral mu D g2^\+)%E \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funenng_lt_pinfty.
    apply adde_ge0.
      by apply: ge0_integral => // x _; exact: funenng_ge0.
    by apply: ge0_integral => // x _; exact: funenng_ge0.
  have g12nnp : (integral mu D g1^\- + integral mu D g2^\-)%E \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; apply: integral_funennp_lt_pinfty.
    apply adde_ge0.
      by apply: ge0_integral => // x _; exact: funenng_ge0.
    by apply: ge0_integral => // x _; exact: funenng_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        have : integrable mu D (g1 \+ g2)%E by exact: integrableD.
        exact: integral_funenng_lt_pinfty.
      apply: adde_ge0; last first.
        by apply: ge0_integral => // x _; exact: funennp_ge0.
      apply: adde_ge0.
        by apply: ge0_integral => // x _; exact: funenng_ge0.
      by apply: ge0_integral => // x _; exact: funennp_ge0.
    - by rewrite adde_defC fin_num_adde_def.
  rewrite -(addeA (integral mu D (g1 \+ g2)%E^\+)).
  rewrite (addeC (integral mu D (g1 \+ g2)%E^\+)).
  rewrite -addeA (addeC (integral mu D g1^\- + integral mu D g2^\-)%E).
  rewrite eq_sym -(sube_eq g12nng); last first.
    by rewrite fin_num_adde_def.
  move/eqP => <-.
  rewrite oppeD; last first.
    rewrite ge0_fin_numE.
      by apply: integral_funennp_lt_pinfty if2.
    by apply: ge0_integral => // x _; exact: funennp_ge0.
  rewrite -addeA (addeCA (integral mu D g2^\+)).
  by rewrite addeA -(integralE point _ _ g1) -(integralE point _ _ g2).
have : ((g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+)%E.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in X in _ == X]addeC -sube_eq; last 2 first.
    by rewrite /funenng /funennp /g1 /g2 /= !maxEFin.
    by rewrite /funenng /funennp /g1 /g2 /= !maxEFin.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite /funenng /funennp !maxEFin.
    by rewrite /funenng /funennp !maxEFin.
  by rewrite -funeD_nngD funeD_Dnng.
move/(congr1 (integral mu D)).
rewrite (ge0_integralD point mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0 //; [exact: funenng_ge0|exact: funennp_ge0].
  - rewrite /funennp /funenng /g1 /g2 /=.
    under eq_fun do rewrite 2!maxEFin; rewrite -/(measurable_fun _ _).
    apply: emeasurable_funD => //.
    apply: measurable_fun_comp_EFin.
      apply: EFin_measurable_fun.
      rewrite /comp.
      under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
      apply: emeasurable_fun_funenng => //.
      apply: measurable_fun_comp_EFin.
      apply: measurable_funD => //.
        by apply: EFin_measurable_fun; case: if1.
      by apply: EFin_measurable_fun; case: if2.
    apply: measurable_fun_comp_EFin.
    apply: EFin_measurable_fun.
    rewrite /comp.
    under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
    apply: emeasurable_fun_funenng => //.
    apply: measurable_fun_comp_EFin.
    apply: measurable_funN => //.
    by apply: EFin_measurable_fun; case: if1.
  - by move=> x _; exact: funennp_ge0.
  - by apply: emeasurable_fun_funennp => //; case: if2.
rewrite (ge0_integralD point mu mD); last 4 first.
  - by move=> x _; exact: funenng_ge0.
  - apply: emeasurable_fun_funenng => //.
    rewrite /g1 /g2 /comp.
    apply: measurable_fun_comp_EFin.
    apply: measurable_funD => //.
      by apply: EFin_measurable_fun; case: if1.
    by apply: EFin_measurable_fun; case: if2.
  - by move=> x _; exact: funennp_ge0.
  - apply: emeasurable_fun_funenng => //.
    rewrite /g1 /comp.
    under eq_fun do rewrite -NEFin; rewrite -/(measurable_fun _ _).
    apply: measurable_fun_comp_EFin; apply: measurable_funN => //.
    by apply: EFin_measurable_fun; case: if1.
move=> ->.
rewrite (ge0_integralD point mu mD); last 4 first.
  - by move=> x _; apply: adde_ge0; [exact:funenng_ge0|exact:funenng_ge0].
  - rewrite /g1 /g2 /= /comp /= /funennp /funenng.
    under eq_fun do rewrite -NEFin.
    under eq_fun do rewrite 2!maxEFin; rewrite -/(measurable_fun _ _).
    apply: measurable_fun_comp_EFin; apply: measurable_funD => //.
      apply: EFin_measurable_fun.
      rewrite /comp.
      under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
      apply: emeasurable_fun_funenng => //.
      apply: measurable_fun_comp_EFin; apply: measurable_funN => //.
      apply: measurable_funD => //.
        by apply: EFin_measurable_fun; case: if1.
      by apply: EFin_measurable_fun; case: if2.
     apply: EFin_measurable_fun.
     rewrite /comp /=.
     under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
     apply: emeasurable_fun_funenng => //.
     by case: if1.
  - by move=> x _; exact: funenng_ge0.
  - by apply: emeasurable_fun_funenng => //; case: if2.
rewrite (ge0_integralD point mu mD) //.
- by move=> x _; exact: funennp_ge0.
- apply: emeasurable_fun_funennp => //.
  rewrite /g1 /g2 /comp /=.
  apply: measurable_fun_comp_EFin; apply: measurable_funD => //.
    by apply: EFin_measurable_fun; case: if1.
  by apply: EFin_measurable_fun; case: if2.
- by move=> x _; exact: funenng_ge0.
  by apply: emeasurable_fun_funenng => //; case: if1.
Qed.

End linearity.

Lemma integralB_EFin (R : realType) (T : measurableType) (point : T)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R) :
  measurable D ->
  integrable mu D (EFin \o f1) -> integrable mu D (EFin \o f2) ->
  integral mu D (fun x => (f1 x)%:E - (f2 x)%:E)%E =
    (integral mu D (EFin \o f1) - integral mu D (EFin \o f2))%E.
Proof.
move=> mD if1 if2.
rewrite (integralD_EFin point mD if1); last exact: integrableN.
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Lemma le_abse_integral (T : measurableType) (point : T) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f ->
  (`|integral mu D f| <= integral mu D (abse \o f))%E.
Proof.
move=> mD mf.
rewrite (integralE point) (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  by apply: ge0_integral => // t _; exact: funenng_ge0.
rewrite gee0_abs; last by apply: ge0_integral => // t _; exact: funennp_ge0.
rewrite -ge0_integralD // -?fune_abse//; [
  by move=> t _; exact: funenng_ge0 | exact: emeasurable_fun_funenng |
  by move=> t _; exact: funennp_ge0 | exact: emeasurable_fun_funennp].
Qed.

(* NB: this is work in progress *)
Section dominated_convergence_theorem.
Variables (T : measurableType) (point : T) (R : realType).
Variables mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f_ : (T -> R)^nat.
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Variable f : T -> R.
Hypothesis f_f : (*{ae mu,*) forall x, f_^~x --> f x(*}*).
Variable g : T -> R.
Hypothesis ig : integrable mu D (fun x => (g x)%:E).
Hypothesis normfg : forall n, (*{ae mu,*) forall x, D x -> `|f_ n x| <= g x(*}*).

Let g0 : forall x, D x -> 0 <= g x.
Proof. by move=> x Dx; rewrite (le_trans _ (@normfg O _ Dx)). Qed.

Lemma dominated_integrable : integrable mu D (EFin \o f).
Proof.
split.
  apply: measurable_fun_comp; last exact: (measurable_fun_cvg mD mf_).
  by apply: measurable_fun_EFin; exact: measurableT.
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
- by move=> x Dx; apply: abse_ge0.
- apply: measurable_fun_comp.
    by apply: measurable_fun_abse; exact: measurableT.
  by apply: measurable_fun_comp_EFin; exact: (measurable_fun_cvg mD mf_).
- by move=> x Dx; exact: abse_ge0.
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

Let mgg n : measurable_fun D (fun x => (2 * g x - g_ n x)%:E).
Proof.
apply: measurable_fun_comp_EFin.
apply: measurable_funD => //.
  apply: measurable_funrM; case: ig => + _ //.
  exact: EFin_measurable_fun.
apply/measurable_funN/measurable_fun_comp => //.
  by apply: measurable_fun_normr; exact: measurableT.
apply: measurable_funD => //; apply: measurable_funN => //.
exact: (measurable_fun_cvg mD mf_).
Qed.

Local Open Scope ereal_scope.

Let gg_ge0 n x : D x -> 0 <= (2 * g x - g_ n x)%:E.
Proof. by move=> Dx; rewrite lee_fin gg_. Qed.

Lemma dominated_cvg0 : (fun n => integral mu D (EFin \o g_ n)) --> 0.
Proof.
have := fatou point mu mD mgg gg_ge0.
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
have i2g : integral mu D (EFin \o (fun x => (2 * g x)%R)) < +oo.
  rewrite /comp /=; under eq_fun do rewrite mulEFin.
  rewrite integralM // lte_mul_pinfty// ?lee_fin//; case: ig => _.
  apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply eq_integral => t Dt; rewrite gee0_abs // lee_fin g0// -in_setE.
rewrite [X in _ <= X -> _](_ : _ = integral mu D (fun x => (2 * g x)%:E) + -
    lim_ereal_sup (fun n => integral mu D (EFin \o g_ n))); last first.
  rewrite (_ : (fun n => _) = (fun n => integral mu D (fun x => (2 * g x)%:E) +
      integral mu D (fun x => (- g_ n x)%:E)))%E; last first.
    rewrite funeqE => n; under eq_fun do rewrite subEFin.
    rewrite (integralB_EFin point mD).
    - rewrite [X in _ = _ + X](_ : _ = (- integral mu D (EFin \o g_ n))) //.
      by rewrite -ge0_integralN // => t Dt; rewrite lee_fin.
    - rewrite [X in integrable mu D X](_ : _ = (fun x => 2%:E * (g x)%:E))%E; last by [].
      exact: integrableK.
    - have integrable_normfn : integrable mu D (fun x => `|f_ n x|%:E).
        apply: le_integrable ig => //.
        - apply: measurable_fun_comp_EFin; apply: measurable_fun_comp => //.
          by apply: measurable_fun_normr; exact: measurableT.
        - move=> x Dx; rewrite lee_fin normr_id.
          by rewrite (le_trans (normfg _ Dx))// ler_norm.
      suff : integrable mu D (fun x : T => `|f_ n x|%:E + `|f x|%:E)%E.
        apply: le_integrable => //.
        - apply: measurable_fun_comp_EFin; apply: measurable_fun_comp => //.
          by apply: measurable_fun_normr; exact: measurableT.
          by apply: measurable_funB => //; exact: (measurable_fun_cvg mD mf_).
        - move=> x Dx; rewrite lee_fin normr_id.
          by rewrite (le_trans (ler_norm_sub _ _))// ler_norm.
      apply: integrableD; [by []| by []|by []|].
      apply: le_integrable dominated_integrable => //.
      - apply: measurable_fun_comp_EFin; apply: measurable_fun_comp => //.
        by apply: measurable_fun_normr; exact: measurableT.
        exact: (measurable_fun_cvg mD mf_).
      - by move=> x Dx; rewrite /= lee_fin normr_id.
  rewrite lim_ereal_inf_shift; last first.
    rewrite ge0_fin_numE//.
    by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
  rewrite -lim_ereal_infN; congr (_ + lim_ereal_inf _)%E.
  by rewrite funeqE => n /=; rewrite -ge0_integralN// => x Dx; rewrite lee_fin.
rewrite addeC -lee_subl_addr; last first.
  rewrite ge0_fin_numE//.
  by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
rewrite subee; last first.
  rewrite ge0_fin_numE//.
  by rewrite ge0_integral // => x Dx; rewrite lee_fin mulr_ge0// g0.
rewrite lee_oppr oppe0 => lim_ge0.
apply/lim_ereal_sup_le0_cvg0 => // n.
by rewrite ge0_integral// => x _; rewrite lee_fin.
Qed.

Lemma dominated_cvg :
  (fun n => integral mu D (EFin \o f_ n)) --> integral mu D (EFin \o f).
Proof.
have h n : `|integral mu D (EFin \o f_ n) - integral mu D (EFin \o f)|
    <= integral mu D (EFin \o g_ n).
  rewrite -(integralB_EFin point mD _ dominated_integrable); last first.
    apply: le_integrable ig => //.
      exact: measurable_fun_comp_EFin.
    by move=> x Dx /=; rewrite (ger0_norm (g0 Dx)) lee_fin normfg.
  apply: le_abse_integral => //; apply: measurable_fun_comp_EFin.
  by apply: measurable_funB => //; exact: measurable_fun_cvg.
suff: (fun n => `|integral mu D (EFin \o f_ n) -
             integral mu D (EFin \o f)|) --> 0.
   move/cvg_abse/cvg_sub0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   case: dominated_integrable => ?; apply: le_lt_trans.
   exact: (le_trans _ (le_abse_integral point mu _ _)).
apply: (@ereal_squeeze _ (cst 0) _ (fun n => integral mu D (EFin \o g_ n))).
- by apply: nearW => n; rewrite abse_ge0/=.
- exact: cvg_cst.
- exact: dominated_cvg0.
Qed.

End dominated_convergence_theorem.

Section section.
Variables (T1 T2 : Type).
Implicit Types (A : set (T1 * T2)) (x : T1) (y : T2).

Definition xsection A x := [set y | (x, y) \in A].

Definition ysection A y := [set x | (x, y) \in A].

Lemma xsection0 x : xsection set0 x = set0.
Proof. by rewrite predeqE /xsection => y; split => //=; rewrite in_setE. Qed.

Lemma ysection0 y : ysection set0 y = set0.
Proof. by rewrite predeqE /ysection => x; split => //=; rewrite in_setE. Qed.

Lemma in_xsectionM X1 X2 x : x \in X1 -> xsection (X1 `*` X2) x = X2.
Proof.
move=> xX1; rewrite /xsection predeqE => y /=; split; rewrite inE.
  by move=> [].
by move=> X2y; split => //=; rewrite -in_setE.
Qed.

Lemma in_ysectionM X1 X2 y : y \in X2 -> ysection (X1 `*` X2) y = X1.
Proof.
move=> yX2; rewrite /ysection predeqE => x /=; split; rewrite inE.
  by move=> [].
by move=> X1x; split => //=; rewrite -in_setE.
Qed.

Lemma notin_xsectionM X1 X2 x : x \notin X1 -> xsection (X1 `*` X2) x = set0.
Proof.
move=> xX1; rewrite /xsection /= predeqE => y; split => //.
by rewrite /xsection/= inE => -[]; rewrite -in_setE (negbTE xX1).
Qed.

Lemma notin_ysectionM X1 X2 y : y \notin X2 -> ysection (X1 `*` X2) y = set0.
Proof.
move=> yX2; rewrite /xsection /= predeqE => x; split => //.
by rewrite /ysection/= inE => -[_]; rewrite -in_setE (negbTE yX2).
Qed.

Lemma xsection_bigcup (F : nat -> set (T1 * T2)) x :
  xsection (\bigcup_n F n) x = \bigcup_n xsection (F n) x.
Proof.
rewrite predeqE /xsection => y; split => [|[n _]] /=; rewrite in_setE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite in_setE.
by move=> Fnxy; rewrite in_setE; exists n.
Qed.

Lemma ysection_bigcup (F : nat -> set (T1 * T2)) y :
  ysection (\bigcup_n F n) y = \bigcup_n ysection (F n) y.
Proof.
rewrite predeqE /ysection => x; split => [|[n _]] /=; rewrite in_setE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite in_setE.
by move=> Fnxy; rewrite in_setE; exists n.
Qed.

Lemma trivIset_xsection (F : nat -> set (T1 * T2)) x : trivIset setT F ->
  trivIset setT (fun n => xsection (F n) x).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /xsection /= predeqE => y; split => //= -[]; rewrite !in_setE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma trivIset_ysection (F : nat -> set (T1 * T2)) y : trivIset setT F ->
  trivIset setT (fun n => ysection (F n) y).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /ysection /= predeqE => x; split => //= -[]; rewrite !in_setE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma le_xsection x : {homo xsection ^~ x : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY y; rewrite /xsection /= 2!in_setE => /XY. Qed.

Lemma le_ysection y : {homo ysection ^~ y : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY x; rewrite /ysection /= 2!in_setE => /XY. Qed.

Lemma xsectionD X Y x : xsection (X `\` Y) x = xsection X x `\` xsection Y x.
Proof.
rewrite predeqE /xsection /= => y; split; last by rewrite 3!in_setE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!in_setE.
Qed.

Lemma ysectionD X Y y : ysection (X `\` Y) y = ysection X y `\` ysection Y y.
Proof.
rewrite predeqE /ysection /= => x; split; last by rewrite 3!in_setE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!in_setE.
Qed.

End section.

Section measurable_section.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Implicit Types (A : set (T1 * T2)) (x : T1).

Lemma mem_set_pair1 x y A :
  (y \in [set y' | (x, y') \in A]) = ((x, y) \in A).
Proof.
apply/idP/idP => [|]; first by rewrite in_setE.
by rewrite 2!in_setE /= in_setE.
Qed.

Lemma mem_set_pair2 x y A :
  (x \in [set x' | (x', y) \in A]) = ((x, y) \in A).
Proof.
apply/idP/idP => [|]; first by rewrite in_setE.
by rewrite 2!in_setE /= in_setE.
Qed.

Lemma measurable_xsection A x : measurable A -> measurable (xsection A x).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o sfun_ind (point1, point2) 1 mA.
have mf : measurable_fun setT f.
  exact/measurable_fun_comp_EFin/measurable_sfun/measurableT.
have _ : (fun y => (y \in xsection A x)%:R%:E) = f \o (fun y => (x, y)).
  rewrite funeqE => y /=; rewrite /xsection /f.
  by rewrite [sfun_ind]lock /= -lock sfun_indE mul1r mem_set_pair1.
have -> : xsection A x = (fun y => f (x, y)) @^-1` [set 1%E].
  rewrite predeqE => y; split; rewrite /xsection /preimage /= /f.
    by rewrite [sfun_ind]lock /= -lock sfun_indE mul1r => ->.
  rewrite [sfun_ind]lock /= -lock sfun_indE mul1r.
  by case: (_ \in _) => //= -[] /eqP; rewrite eq_sym oner_eq0.
rewrite -(setIT (_ @^-1` _)).
by apply: measurable_fun_prod1 => //; exact: emeasurable_set1.
Qed.

Lemma measurable_ysection A y : measurable A -> measurable (ysection A y).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o sfun_ind (point1, point2) 1 mA.
have mf : measurable_fun setT f.
  exact/measurable_fun_comp_EFin/measurable_sfun/measurableT.
have _ : (fun x => (x \in ysection A y)%:R%:E) = f \o (fun x => (x, y)).
  rewrite funeqE => x /=; rewrite /ysection /f.
  by rewrite [sfun_ind]lock /= -lock sfun_indE mul1r mem_set_pair2.
have -> : ysection A y = (fun x => f (x, y)) @^-1` [set 1%E].
  rewrite predeqE => x; split; rewrite /ysection /preimage /= /f.
    by rewrite [sfun_ind]lock /= -lock sfun_indE mul1r => ->.
  rewrite [sfun_ind]lock /= -lock sfun_indE mul1r.
  by case: (_ \in _) => //= -[] /eqP; rewrite eq_sym oner_eq0.
rewrite -(setIT (_ @^-1` _)).
by apply: measurable_fun_prod2 => //; exact: emeasurable_set1.
Qed.

End measurable_section.

Section ndseq_closed_B.
Variables (T1 T2 : measurableType) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (point2 : T2) (m2 : {measure set T2 -> \bar R}).
Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma xsection_ndseq_closed_B : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: measurable_bigcup => n; have [] := BF n.
have phiF x : (fun i => phi (F i) x) --> phi (\bigcup_i F i) x.
  rewrite /phi /= xsection_bigcup; apply: cvg_mu_inc => //.
  - by move=> n; apply: measurable_xsection; case: (BF n).
  - by apply: measurable_bigcup => i; apply: measurable_xsection; case: (BF i).
  - move=> m n mn; apply/subsetPset => y; rewrite /xsection/= !in_setE.
    by have /subsetPset FmFn := ndF _ _ mn; exact: FmFn.
apply: (@emeasurable_fun_cvg _ _ _ (phi \o F) _ measurableT).
- by move=> i; have [] := BF i.
- by move=> x _; exact: phiF.
Qed.
End xsection.

Section ysection.
Variables (point1 : T1) (m1 : {measure set T1 -> \bar R}).
Let psi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma ysection_ndseq_closed_B : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: measurable_bigcup => n; have [] := BF n.
have psiF x : (fun i => psi (F i) x) --> psi (\bigcup_i F i) x.
  rewrite /psi /= ysection_bigcup; apply: cvg_mu_inc => //.
  - by move=> n; apply: measurable_ysection; case: (BF n).
  - by apply: measurable_bigcup => i; apply: measurable_ysection; case: (BF i).
  - move=> m n mn; apply/subsetPset => y; rewrite /ysection/= !in_setE.
    by have /subsetPset FmFn := ndF _ _ mn; exact: FmFn.
apply: (@emeasurable_fun_cvg _ _ _ (psi \o F) _ measurableT).
- by move=> i; have [] := BF i.
- by move=> x _; exact: psiF.
Qed.
End ysection.

End ndseq_closed_B.

(* TODO: move to measure.v *)
Section measure_restr.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).

Definition measure_restr' (X : set _) : \bar R := mu (X `&` D).

Local Lemma measure_restr'0 : measure_restr' set0 = 0%E.
Proof. by rewrite /measure_restr' set0I measure0. Qed.

Local Lemma measure_restr'_ge0 (A : set _) : measurable A -> (0 <= measure_restr' A)%E.
Proof.
by move=> mA; rewrite /measure_restr'; apply: measure_ge0; exact: measurableI.
Qed.

Local Lemma measure_restr'_sigma_additive : semi_sigma_additive measure_restr'.
Proof.
move=> F mF tF mU; pose F' i := F i `&` D.
have mF' i : measurable (F' i) by exact: measurableI.
have tF' : trivIset setT F'.
  apply/trivIsetP => i j _ _ ij; move/trivIsetP : tF => /(_ i j Logic.I Logic.I ij).
  by rewrite /F' setIACA => ->; rewrite set0I.
have h := @measure_sigma_additive _ _ mu _ mF' tF'.
by rewrite /measure_restr' setI_bigcupl.
Qed.

Definition measure_restr : {measure set _ -> \bar R} :=
  Measure.Pack _ (Measure.Axioms
    measure_restr'0 measure_restr'_ge0 measure_restr'_sigma_additive).

Lemma measure_restrE A : measure_restr A = mu (A `&` D).
Proof. by []. Qed.

End measure_restr.

Section measurable_prod_subset.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (m2' : {measure set T2 -> \bar R}).
Variables (D : set T2) (mD : measurable D).
Let m2 := measure_restr m2' mD.
Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_prod_subset_xsection (m2_bounded : exists M, forall X, measurable X -> (m2 X < M%:E)%E) :
  @measurable (prod_measurableType T1 T2) `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in @measurable T1 & A2 in @measurable T2].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setIM].
have CT : C setT.
  exists setT; first exact: measurableT.
  by exists setT; [exact: measurableT|rewrite setMTT].
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : phi (X1 `*` X2) = (fun x => m2 X2 * (sfun_ind point1 1 mX1 x)%:E)%E.
    rewrite funeqE => x.
    rewrite sfun_indE mul1r /m2 measure_restrE.
    rewrite /phi /m2 [measure_restr]lock /= -lock measure_restrE.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionM.
    by rewrite mule0 notin_xsectionM// set0I measure0.
  apply: emeasurable_funeM; first exact: measurableT.
  apply: measurable_fun_comp_EFin.
  by apply: measurable_sfun; exact: measurableT.
have monoB : is_monotone_class B.
  split; first exact: CB.
  - move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
    have -> : phi (X `\` Y) = (fun x => phi X x - phi Y x)%E.
      rewrite funeqE => x; rewrite /phi.
      rewrite [m2]lock /= -lock xsectionD measureD; last 3 first.
        - exact: measurable_xsection.
        - exact: measurable_xsection.
        - move: m2_bounded => [M m2M].
          rewrite (lt_le_trans (m2M (xsection X x) _))// ?lee_pinfty//.
          exact: measurable_xsection.
      by rewrite setIidr//; exact: le_xsection.
    apply: emeasurable_funB => //; first exact: measurableT.
    move=> x _; rewrite /phi adde_defC fin_num_adde_def//.
    rewrite ge0_fin_numE ?measure_ge0//; last exact: measurable_xsection.
    case: m2_bounded => M m2M.
    rewrite (lt_le_trans (m2M (xsection X x) _))// ?lee_pinfty//.
    exact: measurable_xsection.
  - exact: xsection_ndseq_closed_B.
exact: monotone_class_subset.
Qed.
End xsection.

Section ysection.
Variables (m1' : {measure set T1 -> \bar R}).
Variables (D : set T1) (mD : measurable D).
Let m1 := measure_restr m1' mD.
Let psi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma measurable_prod_subset_ysection (m1_bounded : exists M, forall X, measurable X -> (m1 X < M%:E)%E) :
  @measurable (prod_measurableType T1 T2) `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in @measurable T1 & A2 in @measurable T2].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setIM].
have CT : C setT.
  exists setT; first exact: measurableT.
  by exists setT; [exact: measurableT|rewrite setMTT].
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : psi (X1 `*` X2) = (fun x => m1 X1 * (sfun_ind point2 1 mX2 x)%:E)%E.
    rewrite funeqE => y.
    rewrite sfun_indE mul1r /m1 measure_restrE.
    rewrite /psi /m1 [measure_restr]lock /= -lock measure_restrE.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionM.
    by rewrite mule0 notin_ysectionM// set0I measure0.
  apply: emeasurable_funeM; first exact: measurableT.
  apply: measurable_fun_comp_EFin.
  by apply: measurable_sfun; exact: measurableT.
have monoB : is_monotone_class B.
  split; first exact: CB.
  - move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
    have -> : psi (X `\` Y) = (fun x => psi X x - psi Y x)%E.
      rewrite funeqE => y; rewrite /psi.
      rewrite [m1]lock /= -lock ysectionD measureD; last 3 first.
        - exact: measurable_ysection.
        - exact: measurable_ysection.
        - move: m1_bounded => [M m1M].
          rewrite (lt_le_trans (m1M (ysection X y) _))// ?lee_pinfty//.
          exact: measurable_ysection.
      by rewrite setIidr//; exact: le_ysection.
    apply: emeasurable_funB => //; first exact: measurableT.
    move=> x _; rewrite /psi adde_defC fin_num_adde_def//.
    rewrite ge0_fin_numE ?measure_ge0//; last exact: measurable_ysection.
    case: m1_bounded => M m1M.
    rewrite (lt_le_trans (m1M (ysection X x) _))// ?lee_pinfty//.
    exact: measurable_ysection.
  - exact: ysection_ndseq_closed_B.
exact: monotone_class_subset.
Qed.
End ysection.

End measurable_prod_subset.

(* TODO: move *)
Lemma strace_measurable (T : measurableType) (A : set T) : measurable A ->
  strace measurable A `<=` measurable.
Proof. by move=> mA=> _ [C mC <-]; apply: measurableI. Qed.

Section measurable_fun_xsection.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m2 : {measure set T2 -> \bar R}).
Hypothesis sf_m2 : sigma_finite setT m2.
Implicit Types A : set (T1 * T2).

Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection A : A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A.
suff : @measurable (prod_measurableType T1 T2) `<=` B.
  by move=> + A mA; move/(_ A); rewrite -in_setE => /(_ mA)[].
move/sigma_finiteP : sf_m2 => [F F_T [F_nd F_oo]].
move=> X mX.
have -> : X = \bigcup_n (X `&` (setT `*` F n)).
  by rewrite -setI_bigcupr -setM_bigcupr -F_T setMTT setIT.
apply: (xsection_ndseq_closed_B point2).
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setMS.
  exact/subsetPset/F_nd.
move=> n.
rewrite -/B.
pose m2' : {measure set _ -> \bar R} := measure_restr m2 (F_oo n).1.
have m2'_bounded : exists M, forall X, measurable X -> (m2' X < M%:E)%E.
  exists (fine (m2' (F n)) + 1) => Y mY.
  rewrite [in X in (_ < X)%E]addEFin (le_lt_trans _ (lte_addl _ _))//; last first.
    by rewrite lte_fin.
  rewrite fineK; last first.
    rewrite ge0_fin_numE.
      by rewrite /m2' measure_restrE setIid//; have [] := F_oo n.
    by rewrite measure_ge0//; have [] := F_oo n.
  rewrite /m2' !measure_restrE setIid; apply: le_measure => //.
  - by rewrite in_setE /=; apply: measurableI => //; have [] := F_oo n.
  - by rewrite in_setE /=; have [] := F_oo n.
  - by apply: subIset; right.
pose phi' A := m2' \o xsection A.
pose B' := [set A | measurable A /\ measurable_fun setT (phi' A)].
have subset_B' : @measurable (prod_measurableType T1 T2) `<=` B'.
  exact: measurable_prod_subset_xsection.
split=> [|Y mY].
  apply: measurableI => //; apply: measurableM => //; first exact: measurableT.
  by have [] := F_oo n.
have := subset_B' X mX.
rewrite /B' /= => -[_] /(_ Y mY).
have ->// : phi' X = (fun x => m2 [set y | (x, y) \in X `&` setT `*` F n]).
rewrite funeqE => x /=; congr (m2 _).
rewrite predeqE => y; split => [[]|].
  by rewrite /xsection /= in_setE => Xxy Fny; rewrite in_setE.
by rewrite /xsection /= !in_setE => -[] Xxy /= [_].
Qed.

End measurable_fun_xsection.

Section measurable_fun_ysection.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}).
Hypothesis sf_m1 : sigma_finite setT m1.
Implicit Types A : set (T1 * T2).

Let phi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection A : A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A.
suff : @measurable (prod_measurableType T1 T2) `<=` B.
  by move=> + A mA; move/(_ A); rewrite -in_setE => /(_ mA)[].
move/sigma_finiteP : sf_m1 => [F F_T [F_nd F_oo]].
move=> X mX.
have -> : X = \bigcup_n (X `&` (F n `*` setT)).
  by rewrite -setI_bigcupr -setM_bigcupl -F_T setMTT setIT.
apply: (ysection_ndseq_closed_B point1).
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSM.
  exact/subsetPset/F_nd.
move=> n.
rewrite -/B.
pose m1' : {measure set _ -> \bar R} := measure_restr m1 (F_oo n).1.
have m1'_bounded : exists M, forall X, measurable X -> (m1' X < M%:E)%E.
  exists (fine (m1' (F n)) + 1) => Y mY.
  rewrite [in X in (_ < X)%E]addEFin (le_lt_trans _ (lte_addl _ _))//; last first.
    by rewrite lte_fin.
  rewrite fineK; last first.
    rewrite ge0_fin_numE.
      by rewrite /m1' measure_restrE setIid//; have [] := F_oo n.
    by rewrite measure_ge0//; have [] := F_oo n.
  rewrite /m1' !measure_restrE setIid; apply: le_measure => //.
  - by rewrite in_setE /=; apply: measurableI => //; have [] := F_oo n.
  - by rewrite in_setE /=; have [] := F_oo n.
  - by apply: subIset; right.
pose psi' A := m1' \o ysection A.
pose B' := [set A | measurable A /\ measurable_fun setT (psi' A)].
have subset_B' : @measurable (prod_measurableType T1 T2) `<=` B'.
  exact: measurable_prod_subset_ysection.
split=> [|Y mY].
  apply: measurableI => //; apply: measurableM => //; last exact: measurableT.
  by have [] := F_oo n.
have := subset_B' X mX.
rewrite /B' /= => -[_] /(_ Y mY).
have ->// : psi' X = (fun y => m1 [set x | (x, y) \in X `&` F n `*` setT]).
rewrite funeqE => y /=; congr (m1 _).
rewrite predeqE => x; split => [[]|].
  by rewrite /ysection /= in_setE => Xxy Fny; rewrite in_setE.
by rewrite /ysection /= !in_setE => -[] Xxy /= [].
Qed.

End measurable_fun_ysection.

Section product_measure1.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Let m A := integral m1 setT (m2 \o xsection A).

Let m0 : m set0 = 0%E.
Proof.
rewrite /m (_ : _ \o _ = cst 0)%E ?integral0// funeqE => x /=.
by rewrite xsection0 measure0.
Qed.

Let m_ge0 A : measurable A -> (0 <= m A)%E.
Proof.
by move=> ?; apply: ge0_integral => // *; exact/measure_ge0/measurable_xsection.
Qed.

Let m_sigma_additive : semi_sigma_additive m.
Proof.
move=> F mF tF mUF.
have -> : m (\bigcup_n F n) = \sum_(n <oo) (m (F n)).
  transitivity (integral m1 setT (fun x => \sum_(n <oo) m2 (xsection (F n) x))).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => x.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= xsection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_xsection tF)).
    by move=> i; apply: measurable_xsection.
  rewrite integral_sum //; first exact: measurableT.
  - by move=> n; apply: measurable_fun_xsection => //; rewrite in_setE.
  - by move=> n x _; exact/measure_ge0/measurable_xsection.
suff /cvg_ex[l cl] : cvg (fun n => (\sum_(i < n) m (F i))%E).
  by move: (cl) => /cvg_lim; rewrite -lim_mkord => ->.
under eq_fun do rewrite -(big_mkord xpredT (m \o F)).
apply: is_cvg_ereal_nneg_natsum => n _; apply: ge0_integral => // x _.
exact/measure_ge0/measurable_xsection.
Qed.

Definition product_measure1 : {measure set (T1 * T2) -> \bar R} :=
  Measure.Pack _ (Measure.Axioms m0 m_ge0 m_sigma_additive).

End product_measure1.

Section product_measure2.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm1 : sigma_finite setT m1).
Implicit Types A : set (T1 * T2).

Let m A := integral m2 setT (m1 \o ysection A).

Let m0 : m set0 = 0%E.
Proof.
rewrite /m (_ : _ \o _ = cst 0)%E ?integral0// funeqE => x /=.
by rewrite ysection0 measure0.
Qed.

Local Lemma m_ge0 A : measurable A -> (0 <= m A)%E.
Proof.
by move=> ?; apply: ge0_integral => // *; exact/measure_ge0/measurable_ysection.
Qed.

Local Lemma m_sigma_additive : semi_sigma_additive m.
Proof.
move=> F mF tF mUF.
have -> : m (\bigcup_n F n) = \sum_(n <oo) (m (F n)).
  transitivity (integral m2 setT (fun y => \sum_(n <oo) m1 (ysection (F n) y))).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => y.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= ysection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_ysection tF)).
    by move=> i; apply: measurable_ysection.
  rewrite integral_sum //; first exact: measurableT.
  - by move=> n; apply: measurable_fun_ysection => //; rewrite in_setE.
  - by move=> n x _; exact/measure_ge0/measurable_ysection.
suff /cvg_ex[l cl] : cvg (fun n => (\sum_(i < n) m (F i))%E).
  by move: (cl) => /cvg_lim; rewrite -lim_mkord => ->.
under eq_fun do rewrite -(big_mkord xpredT (m \o F)).
apply: is_cvg_ereal_nneg_natsum => n _; apply: ge0_integral => // x _.
exact/measure_ge0/measurable_ysection.
Qed.

Definition product_measure2 : {measure set (T1 * T2) -> \bar R} :=
  Measure.Pack _ (Measure.Axioms m0 m_ge0 m_sigma_additive).

End product_measure2.

Section product_measure.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Let m A := integral m1 setT (m2 \o xsection A).

Lemma product_measureE (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 ->
  product_measure1 point1 point2 m1 sm2 (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
move=> mA1 mA2; rewrite /product_measure1 /= /m.
rewrite (_ : _ \o _ = (fun x => m2 A2 * (nnsfun_ind point1 1%:nng mA1 x)%:E)%E); last first.
  rewrite funeqE => x; rewrite nnsfun_indE mul1r.
  by have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionM// mule1|rewrite mule0 notin_xsectionM].
rewrite ge0_integralM //.
- rewrite muleC; congr (_ * _)%E.
  rewrite integral_nnsfun//; last exact: measurableT.
  by rewrite sintegral_ind //= mul1e setTI.
- exact: measurableT.
- exact/measurable_fun_comp_EFin/measurable_sfun/measurableT.
- by move=> x _; rewrite lee_fin.
- exact: measure_ge0.
Qed.

End product_measure.

Section fubini_tonelli.
Variables (T1 T2 : measurableType) (point1 : T1) (point2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).

Section fubini_tonelli_functions.
Variable (f : T1 * T2 -> \bar R).

Definition fubini_tonelli_F (x : T1) := integral m2 setT (fun y => f (x, y)).
Definition fubini_tonelli_G (y : T2) := integral m1 setT (fun x => f (x, y)).
End fubini_tonelli_functions.

Section fubini_tonelli_sfun1.
Let f (A : set (T1 * T2)) : nnpresfun (prod_measurableType T1 T2) R :=
  nnpresfun_ind (point1, point2) 1%:nng A.

Let F A : T1 -> _ := fubini_tonelli_F (EFin \o f A).
Let G A : T2 -> _ := fubini_tonelli_G (EFin \o f A).

Let F0 (A : set (T1 * T2)) x : (0 <= F A x)%E.
Proof. by apply: ge0_integral => // y _; rewrite lee_fin. Qed.

Let G0 (A : set (T1 * T2)) x : (0 <= G A x)%E.
Proof. by apply: ge0_integral => // y _; rewrite lee_fin. Qed.

Let FE (A : set (T1 * T2)) (mA : measurable A) : F A = m2 \o xsection A.
Proof.
rewrite funeqE => x.
rewrite /F -[RHS]mul1e [X in _ = (X * _)%E](_ : _ = (1%:nng%:nngnum)%:E)//.
rewrite -(sintegral_cst point2 m2) -sintegral_ind_cst.
  exact: measurable_xsection.
move=> msAx.
rewrite /fubini_tonelli_F ge0_integralE //; last by move=> y _;rewrite lee_fin.
rewrite -nnintegral_sfun//; last exact: measurableT.
apply: eq_nnintegral => y _.
rewrite /f [nnpresfun_ind]lock [nnsfun_ind]lock /= -2!lock.
rewrite nnsfun_indE nnpresfun_indE; congr ((_ * _)%:E).
have [|] /= := boolP (y \in xsection _ _).
  by rewrite in_setE /xsection /= => ->.
by rewrite /xsection /= notin_setE /= => /negP/negbTE ->.
Qed.

Let GE (A : set (T1 * T2)) (mA : measurable A) : G A = m1 \o ysection A.
Proof.
rewrite funeqE => y.
rewrite /G -[RHS]mul1e [X in _ = (X * _)%E](_ : _ = (1%:nng%:nngnum)%:E)//.
rewrite -(sintegral_cst point1 m1) -sintegral_ind_cst.
  exact: measurable_ysection.
move=> msAy.
rewrite /fubini_tonelli_G ge0_integralE //; last by move=> x _;rewrite lee_fin.
rewrite -nnintegral_sfun//; last exact: measurableT.
apply: eq_nnintegral => x _.
rewrite /f [nnpresfun_ind]lock [nnsfun_ind]lock /= -2!lock.
rewrite nnsfun_indE nnpresfun_indE.
congr ((_ * _)%:E).
have [|] /= := boolP (x \in ysection _ _).
  by rewrite !in_setE /ysection /= => ->.
by rewrite /ysection /= notin_setE /= => /negP/negbTE ->.
Qed.

Let mF (A : set (T1 * T2)) (mA : measurable A) : measurable_fun setT (F A).
Proof.
rewrite FE//.
by apply: measurable_fun_xsection => //; rewrite in_setE.
Qed.

Let mG (A : set (T1 * T2)) (mA : measurable A) : measurable_fun setT (G A).
Proof.
rewrite GE//.
by apply: measurable_fun_ysection => //; rewrite in_setE.
Qed.

Let m : {measure set (T1 * T2) -> \bar R} := product_measure1 point1 point2 m1 sf_m2.

(* par definition de la mesure produit *)
Let mE (A : set (T1 * T2)) (mA : measurable A) : m A = integral m1 setT (F A).
Proof.
rewrite /m /product_measure1 /= /F /fubini_tonelli_F.
congr (integral m1 setT _).
rewrite funeqE => x.
by rewrite -FE /F /fubini_tonelli_F.
Qed.

Let m' : {measure set (T1 * T2) -> \bar R} := product_measure2 point1 point2 m2 sf_m1.

Let m'E (A1 : set T1) (A2 : set T2) (mA1 : measurable A1) (mA2 : measurable A2) :
  m' (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
have mA1A2 : measurable (A1 `*` A2) by exact: measurableM.
transitivity (integral m2 setT (m1 \o ysection (A1 `*` A2))) => //.
transitivity (integral m2 setT (fun y => m1 A1 * (nnsfun_ind point2 (1%R)%:nng mA2 y)%:E))%E.
  congr (integral m2 setT _); rewrite funeqE => y.
  rewrite nnsfun_indE mul1r /mkset /=.
  have [yA2|yA2] := boolP (y \in A2).
    by rewrite mule1 in_ysectionM.
  by rewrite mule0 notin_ysectionM// measure0.
rewrite ge0_integralM//; last 4 first.
  - exact: measurableT.
  - by apply: measurable_fun_comp_EFin; apply: measurable_sfun; exact: measurableT.
  - by move=> y _; rewrite lee_fin.
  - exact: measure_ge0.
congr (_ * _)%E; rewrite integral_ind; last exact: measurableT.
by rewrite setTI mul1e.
Qed.

Lemma fubini_tonelli_sfun1_F (A : set (T1 * T2)) (mA : measurable A) :
  sintegral m setT (f A) = integral m1 setT (F A).
Proof.
rewrite sintegral_ind// mul1e /=; apply: eq_integral => x _.
by rewrite setTI FE.
Qed.

Lemma fubini_tonelli_sfun1_G (A : set (T1 * T2)) (mA : measurable A) :
  sintegral m' setT (f A) = integral m2 setT (G A).
Proof.
rewrite sintegral_ind// mul1e /=; apply: eq_integral => x _.
by rewrite setTI GE.
Qed.

End fubini_tonelli_sfun1.

End fubini_tonelli.
