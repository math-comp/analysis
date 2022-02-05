(* -*- company-coq-local-symbols: (("\\int" . ?∫) ("\\int_" . ?∫) ("'d" . ?𝑑) ("^\\+" . ?⁺) ("^\\-" . ?⁻)); -*- *)
(* intersection U+2229; union U+222A, set U+2205 *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets posnum functions cardinality.
Require Import reals ereal topology normedtype sequences measure.
Require Import nngnum lebesgue_measure csum.

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
(* properties of the integral, the dominated convergence theorem and Fubini's *)
(* theorem.                                                                   *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* Acknowledgment: This work is partly based on MathComp-Analysis meetings    *)
(*                                                                            *)
(*                  f ^\+ == the function formed by the non-negative outputs  *)
(*                           of f (from a type to the type of extended real   *)
(*                           numbers) and 0 otherwise                         *)
(*                           rendered as f ⁺ with company-coq (U+207A)        *)
(*                  f ^\- == the function formed by the non-positive outputs  *)
(*                           of f and 0 o.w.                                  *)
(*                           rendered as f ⁻ with company-coq (U+207B)        *)
(*            presfun T R == type of simple functions w.o. measurability      *)
(*                           hypothesis                                       *)
(*                           we define constant, indicator, scaled,           *)
(*                           projections presfun functions, as well as        *)
(*                           sum, product, max of presfun functions           *)
(*                ssize f == size of the range of the simple function f       *)
(*              spimg f i == preimage of the ith image of the simple          *)
(*                           function f                                       *)
(*            img_idx f x == the index of (f x) in the range of the simple    *)
(*                           function f, this index has type 'I_(ssize f)     *)
(*       sintegral mu D f == integral of the simple function f over the       *)
(*                           domain D with measure mu                         *)
(*               sfun T R == type of simple functions                         *)
(*                           we define constant, indicator, scaled,           *)
(*                           projection, sum, max of simple functions         *)
(*             nnsfun T R == type of non-negative simple functions            *)
(*         nnintegral D f == integral of a nonnegative measurable function f  *)
(*                         over the domain D                                  *)
(* \int_ D (f x) 'd mu[x] == integral of a measurable function over the       *)
(*                           domain D with measure mu; this notation is       *)
(*                           rendered as ∫ D (f x) 𝑑 mu[x] with company-coq   *)
(*                           (U+222B and U+1D451)                             *)
(*    \int (f x) 'd mu[x] := \int_ set (f x) 'd mu[x]; this notation is       *)
(*                           rendered as ∫ (f x) 𝑑 mu[x] with company-coq     *)
(*         dyadic_itv n k == the interval                                     *)
(*                           `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[           *)
(*             approx A f == nondecreasing sequence of functions that         *)
(*                           approximates f  using dyadic intervals           *)
(*       Rintegral mu D f := fine (\int_ D f 'd mu).                          *)
(*     mu.-integrable D f == f is measurable over D and the integral of f     *)
(*                           w.r.t. D is < +oo                                *)
(*           xsection A x == with A : set (T1 * T2) and x : T1 is the         *)
(*                           x-section of A                                   *)
(*           ysection A y == with A : set (T1 * T2) and y : T2 is the         *)
(*                           y-section of A                                   *)
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
Reserved Notation "'\int_' D f ''d' mu [ x ]" (at level 10, D, f at next level,
  format "'\int_'  D  f  ''d'  mu [ x ]").
Reserved Notation "'\int' f ''d' mu [ x ]" (at level 10, f at next level,
  format "'\int'  f  ''d'  mu [ x ]").
Reserved Notation "mu .-integrable" (at level 2, format "mu .-integrable").

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

Lemma mulr_ge0_gt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 <= y ->
  (0 < x * y) = (0 < x) && (0 < y).
Proof.
rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mul0r ltxx.
rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite mulr0 ltxx andbC.
by apply/idP/andP=> [|_]; rewrite pmulr_rgt0.
Qed.

Local Open Scope ereal_scope.

Lemma adde_gt0 (R : numDomainType) (x y : \bar R) : 0 < x -> 0 < y -> 0 < x + y.
Proof.
by move: x y => [x| |] [y| |] //; rewrite !lte_fin; exact: addr_gt0.
Qed.

Lemma padde_eq0 (R : numDomainType) (x y : \bar R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: paddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma nadde_eq0 (R : numDomainType) (x y : \bar R) :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: naddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma mule_ge0_gt0 (R : realDomainType) (x y : \bar R) : 0 <= x -> 0 <= y ->
  (0 < x * y) = (0 < x) && (0 < y).
Proof.
move: x y => [x| |] [y| |] //; rewrite ?lee_fin.
- by move=> x0 y0; rewrite !lte_fin; exact: mulr_ge0_gt0.
- rewrite le_eqVlt => /predU1P[<-|x0] _; first by rewrite mul0e ltxx.
  by rewrite lte_pinfty andbT mulrpinfty gtr0_sg// mul1e lte_fin x0 lte_pinfty.
- move=> _; rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mule0 ltxx andbC.
  by rewrite lte_pinfty/= mulpinftyr gtr0_sg// mul1e lte_fin x0 lte_pinfty.
- by move=> _ _; rewrite mule_pinfty_pinfty lte_pinfty.
Qed.
Local Close Scope ereal_scope.

Local Open Scope ereal_scope.
Lemma esum_seq_ninfty (R : numDomainType)
    (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
Admitted. (*PR in progress*)

Lemma esum_seq_pinfty (R : numDomainType)
    (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
Admitted. (*PR in progress *)
Local Close Scope ereal_scope.

Lemma seq_psume_eq0 (R : realDomainType) (I : choiceType) (r : seq I)
    (P : pred I) (F : I -> \bar R) : (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i <- r | P i) F i == 0)%E = all (fun i => P i ==> (F i == 0%E)) r.
Proof.
move=> F0; apply/eqP/allP => PF0; last first.
  rewrite big_seq_cond big1// => i /andP[ir Pi].
  by have := PF0 _ ir; rewrite Pi implyTb => /eqP.
move=> i ir; apply/implyP => Pi; apply/eqP.
have H1 : {in r, forall i, P i ==> (F i \is a fin_num)}.
  move=> j jr; apply/implyP => Pj; rewrite fin_numElt; apply/andP; split.
    by rewrite (lt_le_trans _ (F0 _ Pj))// lte_ninfty.
  rewrite ltNge; apply/eqP; rewrite lee_pinfty_eq; apply/eqP/negP => /eqP Fjoo.
  have H1 : forall i, P i -> F i != -oo%E.
    by move=> k Pk; rewrite gt_eqF// (lt_le_trans _ (F0 _ Pk))// lte_ninfty.
  have /esum_seq_pinfty : exists i, [/\ i \in r, P i & F i = +oo%E] by exists j.
  by move=> /(_ H1); rewrite PF0.
have ? : \sum_(i <- r | P i) (fine \o F) i == 0.
  apply/eqP/EFin_inj; rewrite big_seq_cond -sumEFin.
  rewrite (eq_bigr (fun i0 => F i0)); last first.
    move=> j /andP[jr Pj] /=; rewrite fineK//.
    by have := H1 _ jr; rewrite Pj implyTb.
  by rewrite -big_seq_cond PF0.
have H3 : all (fun i => P i ==> ((fine \o F) i == 0)) r.
  by rewrite -psumr_eq0// => j Pj/=; apply/le0R/F0.
move/allP : H3 => /(_ _ ir); rewrite Pi implyTb => /= => /eqP Fi0.
rewrite -(@fineK _ (F i))//; last by have := H1 _ ir; rewrite Pi implyTb.
by rewrite Fi0.
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

(* NB: not used anymore *)
Lemma elim_inf_EFin (T : Type) (R : realType) (D : set T) (f : (T -> R)^nat) :
  (forall t, D t -> cvg (f^~t : _ -> R^o)) ->
  (forall t, D t -> elim_inf (EFin \o f^~t) = (lim (f ^~ t))%:E).
Proof.
move=> cf t Dt; rewrite -EFin_lim; last exact: cf.
rewrite is_cvg_elim_infE //.
by apply: continuous_is_cvg; [move=> l ftl|exact: cf].
Qed.

Lemma elim_inf_shift (R : realType) (u : (\bar R)^nat) (k : \bar R) :
  k \is a fin_num -> elim_inf (fun x => k + u x)%E = (k + elim_inf u)%E.
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

Lemma elim_sup_le0_cvg0 (R : realType) (u : (\bar R)^nat) :
  (elim_sup u <= 0)%E -> (forall n, 0 <= u n)%E -> u --> 0%E.
Proof.
move=> supu0 u0; have usupu n : (0 <= u n <= esups u n)%E.
  by rewrite u0 /=; apply/ereal_sup_ub; exists n => /=.
have : esups u --> 0%E.
  have /cvg_ex[l esupl] : cvg (esups u) by exact: is_cvg_esups.
  have <- : elim_sup u = 0%E.
    apply/eqP; rewrite eq_le supu0; apply: (ereal_lim_ge (@is_cvg_esups _ _)).
    apply: nearW => m.
    have /le_trans : (0 <= einfs u m)%E.
      by apply: lb_ereal_inf => _ [p /= pm] <-; exact: u0.
    apply; apply: einfs_le_esups.
  move: (esupl) => /cvg_lim => /(_ (@ereal_hausdorff R)).
  by rewrite /elim_sup => ->.
by apply: (@ereal_squeeze _ (cst 0%E)) => //; [exact: nearW|exact: cvg_cst].
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
Unshelve. all: by end_near. Qed.

(* TODO: move near ge0_adde_def *)
Lemma ltpinfty_adde_def (R : numDomainType) :
  {in [pred x | (x < +oo)%E] &, forall x y : \bar R, (x +? y)%E}.
Proof. by move=> [x| |] [y| |]. Qed.

(* NB: not used *)
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

Canonical mule_monoid (R : numDomainType) :=
  @Monoid.MulLaw _ _ (@mule R) (@mul0e R) (@mule0 R).

(* NB: lte_add_pinfty *)
Lemma lte_mul_pinfty (R : realDomainType) (x y : \bar R) :
  (0 <= x)%E -> x \is a fin_num -> (y < +oo)%E -> (x * y < +oo)%E.
Proof.
move: x y => [x| |] [y| |] // x0 xfin _; first by rewrite -EFinM lte_pinfty.
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

Notation "f ^\+" := (funenng f) : ereal_scope.
Notation "f ^\-" := (funennp f) : ereal_scope.

Section funpos_lemmas.
Local Open Scope ereal_scope.
Variables (T : Type) (R : realDomainType) (D : set T).
Implicit Types (f g : T -> \bar R) (r : R).

Lemma funenng_ge0 f x : 0 <= f^\+ x.
Proof. by rewrite /funenng /= le_maxr lexx orbT. Qed.

Lemma funennp_ge0 f x : 0 <= f^\- x.
Proof. by rewrite /funennp le_maxr lexx orbT. Qed.

Lemma funenngN f : (\- f)^\+ = f^\-.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp. Qed.

Lemma funennpN f : (\- f)^\- = f^\+.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp oppeK. Qed.

Lemma funenng_restrict f : (f \|_ D)^\+ = (f^\+) \|_ D.
Proof.
by apply/funext => x; rewrite /patch/_^\+; case: ifP; rewrite //= maxxx.
Qed.

Lemma funennp_restrict f : (f \|_ D)^\- = (f^\-) \|_ D.
Proof.
by apply/funext => x; rewrite /patch/_^\-; case: ifP; rewrite //= oppr0 maxxx.
Qed.

Lemma erestrict0 : (cst 0 : T -> \bar R) \|_ D = cst 0.
Proof. by apply/funext => x; rewrite /patch/=; case: ifP. Qed.

Lemma erestrictD f g : (f \+ g) \|_ D = f \|_ D \+ g \|_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?adde0. Qed.

Lemma erestrictN f : (\- f) \|_ D = \- f \|_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?oppe0. Qed.

Lemma erestrictB f g : (f \- g) \|_ D = f \|_ D \- g \|_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?sube0. Qed.

Lemma erestrictM f g : (f \* g) \|_ D = f \|_ D \* g \|_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?mule0. Qed.

Lemma erestrict_scale k f :
  (fun x => k%:E * f x) \|_ D = (fun x => k%:E * (f \|_ D) x).
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?mule0. Qed.

Lemma ge0_funenngE f : (forall x, D x -> 0 <= f x) -> {in D, f^\+ =1 f}.
Proof. by move=> f0 x; rewrite inE => Dx; apply/max_idPl/f0. Qed.

Lemma ge0_funennpE f : (forall x, D x -> 0 <= f x) -> {in D, f^\- =1 cst 0}.
Proof.
by move=> f0 x; rewrite inE => Dx; apply/max_idPr; rewrite lee_oppl oppe0 f0.
Qed.

Lemma le0_funenngE f : (forall x, D x -> f x <= 0) -> {in D, f^\+ =1 cst 0}.
Proof. by move=> f0 x; rewrite inE => Dx; exact/max_idPr/f0. Qed.

Lemma le0_funennpE f : (forall x, D x -> f x <= 0) -> {in D, f^\- =1 \- f}.
Proof.
by move=> f0 x; rewrite inE => Dx; apply/max_idPl; rewrite lee_oppr oppe0 f0.
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
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funenngN gt0_funennpM -1?ltr_oppr ?oppr0.
Qed.

Lemma lt0_funennpM r f : (r < 0)%R ->
  (fun x => r%:E * f x)^\- = (fun x => - r%:E * (f^\+ x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funennpN gt0_funenngM -1?ltr_oppr ?oppr0.
Qed.

Lemma fune_abse f : abse \o f = f^\+ \+ f^\-.
Proof.
rewrite funeqE => x /=; have [fx0|/ltW fx0] := leP (f x) 0.
- rewrite lee0_abs// /funenng /funennp.
  move/max_idPr : (fx0) => ->; rewrite add0e.
  by move: fx0; rewrite -{1}oppr0 EFinN lee_oppr => /max_idPl ->.
- rewrite gee0_abs// /funenng /funennp.
  move/max_idPl : (fx0) => ->.
  by move: fx0; rewrite -{1}oppr0 EFinN lee_oppl => /max_idPr ->; rewrite adde0.
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

Lemma funeD_Dnng f g : f \+ g = (f \+ g)^\+ \- (f \+ g)^\-.
Proof.
apply/funext => x; rewrite /funenng /funennp; have [|/ltW] := leP 0 (f x + g x).
- by rewrite -{1}oppe0 -lee_oppl => /max_idPr ->; rewrite sube0.
- by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite oppeK add0e.
Qed.

Lemma funeD_nngD f g : f \+ g = (f^\+ \+ g^\+) \- (f^\- \+ g^\-).
Proof.
apply/funext => x; rewrite /funenng /funennp.
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
Hint Extern 0 (is_true (0 <= _ ^\+ _)%E) => solve [apply: funenng_ge0] : core.
Hint Extern 0 (is_true (0 <= _ ^\- _)%E) => solve [apply: funennp_ge0] : core.

Section funpos_measurable.
Variables (T : measurableType) (R : realType).

Lemma emeasurable_fun_funenng (D : set T) (f : T -> \bar R) :
  measurable_fun D f -> measurable_fun D f^\+%E.
Proof. by move=> mf; apply: emeasurable_fun_max => //; apply: measurable_fun_cst. Qed.

Lemma emeasurable_fun_funennp (D : set T) (f : T -> \bar R) :
   measurable_fun D f -> measurable_fun D f^\-%E.
Proof.
move=> mf; apply: emeasurable_fun_max => //; last exact: measurable_fun_cst.
by apply: measurable_fun_comp => //; apply: emeasurable_fun_minus.
Qed.

End funpos_measurable.

Lemma measurable_restrict {aT rT : measurableType} D (f : aT -> rT) :
   measurable D -> measurable_fun D f ->
   measurable_fun setT (f \|_ D).
Proof.
move=> mD mf _ /= X mX; rewrite setTI preimage_restrict.
by apply/measurableU/mf => //; case: ifP => // _; apply: measurableC.
Qed.

Lemma restrict_ge0 {aT} {rT : numFieldType} (D : set aT) (f : aT -> rT) :
  (forall x, D x -> 0 <= f x) -> forall x, 0 <= (f \|_ D) x.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma erestrict_ge0 {aT} {rT : numFieldType} (D : set aT) (f : aT -> \bar rT) :
  (forall x, D x -> (0 <= f x)%E) -> forall x, (0 <= (f \|_ D) x)%E.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma ler_restrict {aT} {rT : numFieldType} (D : set aT) (f g : aT -> rT) :
  (forall x, D x -> f x <= g x) -> forall x, (f \|_ D) x <= (g \|_ D) x.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma lee_restrict {aT} {rT : numFieldType} (D : set aT) (f g : aT -> \bar rT) :
  (forall x, D x -> f x <= g x)%E -> forall x, ((f \|_ D) x <= (g \|_ D) x)%E.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R := (x \in A)%:R.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

Lemma indicE {T} {R : ringType} (A : set T) (x : T) :
  indic A x = (x \in A)%:R :> R.
Proof. by []. Qed.

Lemma indicT {T} {R : ringType} : \1_[set: T] = cst (1 : R).
Proof. by apply/funext=> x; rewrite indicE in_setT. Qed.

Lemma indic_restrict {T : pointedType} {R : numFieldType} (A : set T) :
  indic A = 1 \|_ A :> (T -> R).
Proof. by apply/funext => x; rewrite indicE /patch; case: ifP. Qed.

Lemma restrict_indic T (R : numFieldType) (E A : set T) :
  (\1_E \|_ A) = \1_(E `&` A) :> (T -> R).
Proof.
apply/funext => x; rewrite /restrict 2!indicE.
case: ifPn => [|] xA; first by rewrite in_setI xA andbT.
by rewrite in_setI (negbTE xA) andbF.
Qed.

Lemma preimage_indic (T : Type) (R : numDomainType) (D : set T) (B : set R) :
  \1_D @^-1` B = if 1 \in B then (if 0 \in B then setT else D)
                            else (if 0 \in B then ~` D else set0).
Proof.
rewrite /preimage/= /indic; apply/seteqP; split => x;
  case: ifPn => B1; case: ifPn => B0 //=.
- have [|] := boolP (x \in D); first by rewrite inE.
  by rewrite notin_set in B0.
- have [|] := boolP (x \in D); last by rewrite notin_set.
  by rewrite notin_set in B1.
- by have [xD|xD] := boolP (x \in D);
    [rewrite notin_set in B1|rewrite notin_set in B0].
- by have [xD|xD] := boolP (x \in D); [rewrite inE in B1|rewrite inE in B0].
- have [xD|] := boolP (x \in D); last by rewrite notin_set.
  by rewrite inE in B1.
- have [|xD] := boolP (x \in D); first by rewrite inE.
  by rewrite inE in B0.
Qed.

HB.mixin Record FiniteImage aT rT (f : aT -> rT) := {
  fimfunP : finite_set [set of f]
}.
HB.structure Definition FImFun aT rT := {f of @FiniteImage aT rT f}.

Reserved Notation "{ 'fimfun' aT >-> T }"
  (at level 0, format "{ 'fimfun'  aT  >->  T }").
Reserved Notation "[ 'fimfun' 'of' f ]"
  (at level 0, format "[ 'fimfun'  'of'  f ]").
Notation "{ 'fimfun' aT >-> T }" := (@FImFun.type aT T) : form_scope.
Notation "[ 'fimfun' 'of' f ]" := [the {fimfun _ >-> _} of f] : form_scope.
Hint Resolve fimfunP : core.

Lemma fimfun_inP {aT rT} (f : {fimfun aT >-> rT}) (D : set aT) :
  finite_set (f @` D).
Proof. by apply: (@sub_finite_set _ _ [set of f]) => // y [x]; exists x. Qed.

HB.mixin Record IsMeasurableFun (aT : measurableType) (rT : realType) (f : aT -> rT) := {
  measurable_funP : measurable_fun setT f
}.
Hint Resolve fimfun_inP : core.

HB.structure Definition MeasurableFun aT rT := {f of @IsMeasurableFun aT rT f}.
Reserved Notation "{ 'mfun' aT >-> T }"
  (at level 0, format "{ 'mfun'  aT  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").
Notation "{ 'mfun'  aT >-> T }" := (@MeasurableFun.type aT T) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
Hint Resolve measurable_funP : core.

HB.structure Definition SimpleFun (aT (*rT*) : measurableType) (rT : realType) :=
  {f of @IsMeasurableFun aT rT f & @FiniteImage aT rT f}.
Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").
Notation "{ 'sfun'  aT >-> T }" := (@SimpleFun.type aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Lemma measurable_sfunP {aT : measurableType} {rT : realType} (f : {mfun aT >-> rT}) (y : rT) :
  measurable (f @^-1` [set y]).
Proof.
by rewrite -[f @^-1` _]setTI; apply: measurable_funP => //; apply: measurable_set1.
Qed.

HB.mixin Record IsNonNegFun (aT : Type) (rT : numDomainType) (f : aT -> rT) := {
  fun_ge0 : forall x, 0 <= f x
}.
HB.structure Definition NonNegFun aT rT := {f of @IsNonNegFun aT rT f}.
Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Notation "{ 'nnfun'  aT >-> T }" := (@NonNegFun.type aT T) : form_scope.
Notation "[ 'nnfun' 'of' f ]" := [the {nnfun _ >-> _} of f] : form_scope.
Hint Extern 0 (is_true (0 <= _)) => solve [apply: fun_ge0] : core.

HB.structure Definition NonNegSimpleFun (aT : measurableType) (rT : realType) :=
  {f of @SimpleFun _ _ f & @NonNegFun aT rT f}.
Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Notation "{ 'nnsfun'  aT >-> T }" := (@NonNegSimpleFun.type aT T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

(* TODO: this is similar to emeasurable_fun_max, move to lebesgue_measure.v *)
Lemma measurable_fun_max (T : measurableType) (R : realType) D (f g : T -> R) :
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (f \max g).
Proof.
move=> mf mg mD; apply (measurability (RGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite [X in measurable X](_ : _ =
    (D `&` f @^-1` `[x, +oo[) `|` (D `&` g @^-1` `[x, +oo[)); last first.
  rewrite predeqE => t /=; split.
    by rewrite /= !in_itv /= !andbT le_maxr => -[Dx /orP[|]];    tauto.
  by move=> [|]; rewrite /= !in_itv/= !andbT le_maxr;
    move=> [Dx ->]//; rewrite orbT.
by apply: measurableU; [exact/mf/measurable_itv|exact/mg/measurable_itv].
Qed.

Section fimfun_pred.
Context {aT rT : Type}.
Definition fimfun_key : pred_key (mem [set f : aT -> rT | finite_set [set of f]]).
Proof. exact. Qed.
Definition fimfun := KeyedPred fimfun_key.
End fimfun_pred.

Section fimfun.
Context {aT rT : Type}.
Notation T := {fimfun aT >-> rT}.
Notation fimfun := (@fimfun aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in fimfun).
Definition fimfun_Sub_subproof := @FiniteImage.Build aT rT f (set_mem fP).
#[local] HB.instance Definition _ := fimfun_Sub_subproof.
Definition fimfun_Sub := [fimfun of f].
End Sub.

Lemma fimfun_rect (K : T -> Type) :
  (forall f (Pf : f \in fimfun), K (fimfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf]]]/=.
by suff -> : Pf = (set_mem (@mem_set _ [set f | _] f Pf)) by apply: Ksub.
Qed.

Lemma fimfun_valP f (Pf : f \in fimfun) : fimfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

Canonical fimfun_subType := SubType T _ _ fimfun_rect fimfun_valP.
End fimfun.

Lemma fimfuneqP aT rT (f g : {fimfun aT >-> rT}) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

Definition fimfuneqMixin aT (rT : eqType) :=
  [eqMixin of {fimfun aT >-> rT} by <:].
Canonical fimfuneqType aT (rT : eqType) :=
  EqType {fimfun aT >-> rT} (fimfuneqMixin aT rT).
Definition fimfunchoiceMixin aT (rT : choiceType) :=
  [choiceMixin of {fimfun aT >-> rT} by <:].
Canonical fimfunchoiceType aT (rT : choiceType) :=
  ChoiceType {fimfun aT >-> rT} (fimfunchoiceMixin aT rT).

Lemma finite_image_cst {aT rT : Type} (x : rT) : finite_set [set of cst x : aT -> rT].
Proof.
elim/Ppointed: aT => aT; rewrite ?emptyE ?image_set0//.
suff -> : cst x @` [set: aT] = [set x] by apply: finite_set1.
by apply/predeqP => y; split=> [[t' _ <-]//|->//] /=; exists point.
Qed.

Definition fun_cmul {U : Type} {R : ringType} (k : R) (f : U -> R) x := k * f x.
Notation "k *\ f" := (fun_cmul k f) (at level 40, format "k  *\  f") : ring_scope.

Lemma cst_fimfun_subproof aT rT x : @FiniteImage aT rT (cst x).
Proof. by split; exact: finite_image_cst. Qed.
HB.instance Definition _ aT rT x := @cst_fimfun_subproof aT rT x.
Definition cst_fimfun {aT rT} x := [the {fimfun aT >-> rT} of cst x].

Lemma fimfun_cst aT rT x : @cst_fimfun aT rT x =1 cst x. Proof. by []. Qed.

Lemma comp_fimfun_subproof aT rT sT
   (f : {fimfun aT >-> rT}) (g : rT -> sT) : @FiniteImage aT sT (g \o f).
Proof. by split; rewrite -(image_comp f g); apply: finite_image. Qed.
HB.instance Definition _ aT rT sT f g := @comp_fimfun_subproof aT rT sT f g.

Section zmod.
Context (aT : Type) (rT : zmodType).
Lemma fimfun_zmod_closed : zmod_closed (@fimfun aT rT).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; apply: (finite_image11 (fun x y => x - y)).
Qed.
Canonical fimfun_add := AddrPred fimfun_zmod_closed.
Canonical fimfun_zmod := ZmodPred fimfun_zmod_closed.
Definition fimfun_zmodMixin := [zmodMixin of {fimfun aT >-> rT} by <:].
Canonical fimfun_zmodType := ZmodType {fimfun aT >-> rT} fimfun_zmodMixin.

Implicit Types (f g : {fimfun aT >-> rT}).

Lemma fimfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma fimfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma fimfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma fimfun0 : (0 : {fimfun aT >-> rT}) = cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma fimfun_sum I r (P : {pred I}) (f : I -> {fimfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

HB.instance Definition _ f g := FImFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := FImFun.copy (\- f) (- f).
HB.instance Definition _ f g := FImFun.copy (f \- g) (f - g).
End zmod.

Section ring.
Context (aT : pointedType) (rT : ringType).

Lemma fimfun_mulr_closed : mulr_closed (@fimfun aT rT).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; apply: (finite_image11 (fun x y => x * y)).
Qed.
Canonical fimfun_ring := SubringPred fimfun_mulr_closed.
Definition fimfun_ringMixin := [ringMixin of {fimfun aT >-> rT} by <:].
Canonical fimfun_ringType := RingType {fimfun aT >-> rT} fimfun_ringMixin.

Implicit Types (f g : {fimfun aT >-> rT}).

Lemma fimfunM f g : f * g = f \* g :> (_ -> _). Proof. by []. Qed.
Lemma fimfun1 : (1 : {fimfun aT >-> rT}) = cst 1 :> (_ -> _). Proof. by []. Qed.
Lemma fimfun_prod I r (P : {pred I}) (f : I -> {fimfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma fimfunX f n : f ^+ n = (fun x => f x ^+ n) :> (_ -> _).
Proof. by apply/funext => x; elim: n => [|n IHn]//; rewrite !exprS fimfunM/= IHn. Qed.

Lemma indic_fimfun_subproof X : @FiniteImage aT rT \1_X.
Proof.
split; apply: (finite_subfset [fset 0; 1]%fset) => x [tt /=].
by rewrite !inE indicE; case: (_ \in _) => _ <-; rewrite ?eqxx ?orbT.
Qed.
HB.instance Definition _ X := indic_fimfun_subproof X.
Definition indic_fimfun (X : set aT) := [the {fimfun aT >-> rT} of \1_X].

HB.instance Definition _ k f := FImFun.copy (k *\ f) (cst_fimfun k * f).
Definition scale_fimfun k f := [the {fimfun aT >-> rT} of k *\ f].

End ring.
Arguments indic_fimfun {aT rT} _.

Section comring.
Context (aT : pointedType) (rT : comRingType).
Definition fimfun_comRingMixin := [comRingMixin of {fimfun aT >-> rT} by <:].
Canonical fimfun_comRingType := ComRingType {fimfun aT >-> rT} fimfun_comRingMixin.

Implicit Types (f g : {fimfun aT >-> rT}).
HB.instance Definition _ f g := FImFun.copy (f \* g) (f * g).
End comring.

Lemma fimfunE T (R : ringType) (f : {fimfun T >-> R}) x :
  f x = \sum_(y <- fset_set [set of f]) (y * \1_(f @^-1` [set y]) x).
Proof.
have fxfA: f x \in fset_set (f @` setT) by rewrite in_fset_set// inE; exists x.
rewrite (big_fsetD1 (f x))//= indicE (@id (_ \in _)) ?mulr1 ?inE//=.
rewrite big_seq_cond ?big1 ?addr0// => y; rewrite ?andbT !inE eq_sym.
move=> /andP[fxNy yA]; rewrite indicE [_ \in _]negbTE ?mulr0// notin_set.
by move=> fxy; rewrite -fxy eqxx in fxNy.
Qed.

Lemma fimfunEord T (R : ringType) (f : {fimfun T >-> R})
    (s := fset_set (f @` setT)) :
  forall x, f x = \sum_(i < #|`s|) (s`_i * \1_(f @^-1` [set s`_i]) x).
Proof. by move=> x; rewrite fimfunE /s // (big_nth 0) big_mkord. Qed.

Lemma trivIset_preimage1 {aT rT} D (f : aT -> rT) :
  trivIset D (fun x => f @^-1` [set x]).
Proof. by move=> y z _ _ [x [<- <-]]. Qed.

Lemma trivIset_preimage1_in {aT} {rT : choiceType} (D : set rT) (A : set aT) (f : aT -> rT) :
  trivIset D (fun x => A `&` f @^-1` [set x]).
Proof. by move=> y z _ _ [x [[_ <-] [_ <-]]]. Qed.

Section fimfun_bin.
Variables (T : measurableType) (R : numDomainType) (f g : {fimfun T >-> R}).

Lemma max_fimfun_subproof : @FiniteImage T R (f \max g).
Proof. by split; apply: (finite_image11 maxr). Qed.
HB.instance Definition _ := max_fimfun_subproof.

End fimfun_bin.

HB.factory Record FiniteDecomp (T : pointedType) (R : ringType) (f : T -> R) := {
  fimfunE : exists (r : seq R) (A_ : R -> set T),
    forall x, f x = \sum_(y <- r) (y * \1_(A_ y) x)
}.
HB.builders Context T R A f of @FiniteDecomp T R f.
  Lemma finite_subproof: @FiniteImage T R f.
  Proof.
  split; have [r [A_ fE]] := fimfunE.
  suff -> : f = \sum_(y <- r) cst_fimfun y * indic_fimfun (A_ y) by [].
  by apply/funext=> x; rewrite fE fimfun_sum.
  Qed.
  HB.instance Definition _ := finite_subproof.
HB.end.

Section mfun_pred.
Context {aT : measurableType} {rT : realType}.
Definition mfun_key : pred_key (mem [set f : aT -> rT | measurable_fun setT f]).
Proof. exact. Qed.
Definition mfun := KeyedPred mfun_key.
End mfun_pred.

Section mfun.
Context {aT : measurableType} {rT : realType}.
Notation T := {mfun aT >-> rT}.
Notation mfun := (@mfun aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in mfun).
Definition mfun_Sub_subproof := @IsMeasurableFun.Build aT rT f (set_mem fP).
#[local] HB.instance Definition _ := mfun_Sub_subproof.
Definition mfun_Sub := [mfun of f].
End Sub.

Lemma mfun_rect (K : T -> Type) :
  (forall f (Pf : f \in mfun), K (mfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf]]]/=.
by suff -> : Pf = (set_mem (@mem_set _ [set f | _] f Pf)) by apply: Ksub.
Qed.

Lemma mfun_valP f (Pf : f \in mfun) : mfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

Canonical mfun_subType := SubType T _ _ mfun_rect mfun_valP.

Lemma mfuneqP (f g : {mfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

Definition mfuneqMixin := [eqMixin of {mfun aT >-> rT} by <:].
Canonical mfuneqType := EqType {mfun aT >-> rT} mfuneqMixin.
Definition mfunchoiceMixin := [choiceMixin of {mfun aT >-> rT} by <:].
Canonical mfunchoiceType := ChoiceType {mfun aT >-> rT} mfunchoiceMixin.

Lemma cst_mfun_subproof x : @IsMeasurableFun aT rT (cst x).
Proof. by split; apply: measurable_fun_cst. Qed.
HB.instance Definition _ x := @cst_mfun_subproof x.
Definition cst_mfun x := [the {mfun aT >-> rT} of cst x].

Lemma mfun_cst x : @cst_mfun x =1 cst x. Proof. by []. Qed.

End mfun.

Section ring.
Context (aT : measurableType) (rT : realType).

Lemma mfun_subring_closed : subring_closed (@mfun aT rT).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- exact: measurable_fun_cst.
- exact: measurable_funB.
- exact: measurable_funM.
Qed.
Canonical mfun_add := AddrPred mfun_subring_closed.
Canonical mfun_zmod := ZmodPred mfun_subring_closed.
Canonical mfun_subring := SubringPred mfun_subring_closed.
Definition mfun_zmodMixin := [zmodMixin of {mfun aT >-> rT} by <:].
Canonical mfun_zmodType := ZmodType {mfun aT >-> rT} mfun_zmodMixin.
Definition mfun_ringMixin := [ringMixin of {mfun aT >-> rT} by <:].
Canonical mfun_ringType := RingType {mfun aT >-> rT} mfun_ringMixin.
Definition mfun_comRingMixin := [comRingMixin of {mfun aT >-> rT} by <:].
Canonical mfun_comRingType := ComRingType {mfun aT >-> rT} mfun_comRingMixin.

Implicit Types (f g : {mfun aT >-> rT}).

Lemma mfun0 : (0 : {mfun aT >-> rT}) =1 cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma mfun1 : (1 : {mfun aT >-> rT}) =1 cst 1 :> (_ -> _). Proof. by []. Qed.
Lemma mfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma mfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma mfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma mfunM f g : f * g = f \* g :> (_ -> _). Proof. by []. Qed.
Lemma mfun_sum I r (P : {pred I}) (f : I -> {mfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma mfun_prod I r (P : {pred I}) (f : I -> {mfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma mfunX f n : f ^+ n = (fun x => f x ^+ n) :> (_ -> _).
Proof. by apply/funext=> x; elim: n => [|n IHn]//; rewrite !exprS mfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).

Definition mindic (D : set aT) of measurable D : aT -> rT := \1_D.
Lemma mindicE (D : set aT) (mD : measurable D) :
  mindic mD = (fun x => (x \in D)%:R).
Proof. by rewrite /mindic funeqE => t; rewrite indicE. Qed.
HB.instance Definition _ (D : set aT) (mD : measurable D) :
   @FImFun aT rT (mindic mD) := FImFun.on (mindic mD).
Lemma indic_mfun_subproof (D : set aT) (mD : measurable D) :
  @IsMeasurableFun aT rT (mindic mD).
Proof.
split=> mA /= B mB; rewrite preimage_indic.
case: ifPn => B1; case: ifPn => B0 //.
- by rewrite setIT.
- exact: measurableI.
- by apply: measurableI => //; apply: measurableC.
- by rewrite setI0.
Qed.
HB.instance Definition _ D mD := @indic_mfun_subproof D mD.

Definition indic_mfun (D : set aT) (mD : measurable D) :=
  [the {mfun aT >-> rT} of mindic mD].

HB.instance Definition _ k f := MeasurableFun.copy (k *\ f) (cst_mfun k * f).
Definition scale_mfun k f := [the {mfun aT >-> rT} of k *\ f].

Lemma max_mfun_subproof f g : @IsMeasurableFun aT rT (f \max g).
Proof. by split; apply: measurable_fun_max. Qed.
HB.instance Definition _ f g := max_mfun_subproof f g.
Definition max_mfun f g := [the {mfun aT >-> _} of f \max g].

End ring.
Arguments indic_mfun {aT rT} _.

Section sfun_pred.
Context {aT : measurableType} {rT : realType}.
Definition sfun_key : pred_key (mem
  [set f : aT -> rT | measurable_fun setT f /\ finite_set (f @` setT)]).
Proof. exact. Qed.
Definition sfun := KeyedPred sfun_key.
End sfun_pred.

Section sfun.
Context {aT : measurableType} {rT : realType}.
Notation T := {sfun aT >-> rT}.
Notation sfun := (@sfun aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in sfun).
Definition sfun_Sub1_subproof := @IsMeasurableFun.Build aT rT f (set_mem fP).1.
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof := @FiniteImage.Build aT rT f (set_mem fP).2.
#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : T -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]/=; pose Pf := conj Pf1 Pf2.
(* have -> : Pf1 = (set_mem (@mem_set _ [set f | _] f Pf).1) by []. *)
(* have -> : Pf = (set_mem (@mem_set _ [set f | _] f Pf)) by []. *)
(* apply: Ksub. *)
(* Qed. *)
Admitted.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

Canonical sfun_subType := SubType T _ _ sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

Definition sfuneqMixin := [eqMixin of {sfun aT >-> rT} by <:].
Canonical sfuneqType := EqType {sfun aT >-> rT} sfuneqMixin.
Definition sfunchoiceMixin := [choiceMixin of {sfun aT >-> rT} by <:].
Canonical sfunchoiceType := ChoiceType {sfun aT >-> rT} sfunchoiceMixin.

(* TODO: BUG: HB *)
(* HB.instance Definition _ (x : rT) := @cst_mfun_subproof aT rT x. *)
Definition cst_sfun x := [the {sfun aT >-> rT} of cst x].
(* TODO: should this be sfun_cst and the lemma below sfun_cstE? *)

Lemma sfun_cst x : @cst_sfun x =1 cst x. Proof. by []. Qed.

End sfun.

(* a better way to refactor function stuffs *)
Lemma fctD (T : pointedType) (K : ringType) (f g : T -> K) : f + g = f \+ g.
Proof. by []. Qed.
Lemma fctN (T : pointedType) (K : ringType) (f : T -> K) : - f = \- f.
Proof. by []. Qed.
Lemma fctM (T : pointedType) (K : ringType) (f g : T -> K) : f * g = f \* g.
Proof. by []. Qed.
Lemma fctZ (T : pointedType) (K : ringType) (L : lmodType K) k (f : T -> L) :
   k *: f = k \*: f.
Proof. by []. Qed.
Arguments cst _ _ _ _ /.
Definition fctWE := (fctD, fctN, fctM, fctZ).

Section ring.
Context (aT : measurableType) (rT : realType).

Lemma sfun_subring_closed : subring_closed (@sfun aT rT).
Proof.
split=> [|f g|f g]; rewrite !inE/=; split;
  do 1? by[apply: measurable_funP | apply: fimfunP].
Admitted.

Canonical sfun_add := AddrPred sfun_subring_closed.
Canonical sfun_zmod := ZmodPred sfun_subring_closed.
Canonical sfun_subring := SubringPred sfun_subring_closed.
Definition sfun_zmodMixin := [zmodMixin of {sfun aT >-> rT} by <:].
Canonical sfun_zmodType := ZmodType {sfun aT >-> rT} sfun_zmodMixin.
Definition sfun_ringMixin := [ringMixin of {sfun aT >-> rT} by <:].
Canonical sfun_ringType := RingType {sfun aT >-> rT} sfun_ringMixin.
Definition sfun_comRingMixin := [comRingMixin of {sfun aT >-> rT} by <:].
Canonical sfun_comRingType := ComRingType {sfun aT >-> rT} sfun_comRingMixin.

Implicit Types (f g : {sfun aT >-> rT}).

Lemma sfun0 : (0 : {sfun aT >-> rT}) =1 cst 0. Proof. by []. Qed.
Lemma sfun1 : (1 : {sfun aT >-> rT}) =1 cst 1. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunM f g : f * g =1 f \* g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfunX f n : f ^+ n =1 (fun x => f x ^+ n).
Proof. by move=> x; elim: n => [|n IHn]//; rewrite !exprS sfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).

Definition indic_sfun (D : set aT) (mD : measurable D) :=
  [the {sfun aT >-> rT} of mindic rT mD].

HB.instance Definition _ k f := MeasurableFun.copy (k *\ f) (cst_sfun k * f).
Definition scale_sfun k f := [the {sfun aT >-> rT} of k *\ f].

HB.instance Definition _ f g := max_mfun_subproof f g.
Definition max_sfun f g := [the {sfun aT >-> _} of f \max g].

End ring.
Arguments indic_sfun {aT rT} _.

Lemma fset_set_comp (T1 : Type) (T2 T3 : choiceType) (D : set T1)
    (f : {fimfun T1 >-> T2}) (g : T2 -> T3) :
  fset_set [set (g \o f) x | x in D] =
  [fset g x | x in fset_set [set f x | x in D]]%fset.
Proof. by rewrite -(image_comp f g) fset_set_image. Qed.

(* about preimages *)
Lemma notin_setI_preimage T R D (f : T -> R) i :
  i \notin f @` D -> D `&` f @^-1` [set i] = set0.
Proof.
by rewrite notin_set/=; apply: contra_notP => /eqP/set0P[t [Dt fit]]; exists t.
Qed.

Lemma eq_setI_preimage T (R : Type) D (g f : T -> R) A :
  {in D, f =1 g} -> D `&` f @^-1` A = D `&` g @^-1` A.
Proof.
by move=> fg; apply/seteqP; rewrite /preimage; split => x [Dx/= Ax]; split=> //;
  rewrite (fg, =^~fg)// inE.
Qed.
Arguments eq_setI_preimage {T R D} g.

Lemma preimage_in_nnfun0 T (R : realDomainType) (D : set T) (f : {nnfun T >-> R })
  t : t < 0 -> D `&` f @^-1` [set t] = set0.
Proof.
move=> t0; apply/seteqP; split => // x; rewrite /preimage/= => -[Dt fxt].
by move: t0; rewrite ltNge => /negP; apply; rewrite -fxt; apply/fun_ge0.
Qed.

Lemma preimage_nnfun0 T (R : realDomainType) (f : {nnfun T >-> R })
  t : t < 0 -> f @^-1` [set t] = set0.
Proof. by move=> t0; rewrite -[LHS]setTI preimage_in_nnfun0. Qed.

Lemma preimage_cst T (R : eqType) (x y : R) :
  @cst T _ x @^-1` [set y] = if x == y then setT else set0.
Proof.
apply/seteqP; rewrite /preimage; split => [z/= <-//|]; first by rewrite eqxx.
by move=> z/=; case: ifPn => [/eqP|].
Qed.

Lemma preimage_cstM T (R : realFieldType) (x y : R) (f : T -> R) :
  x != 0 -> (cst x \* f) @^-1` [set y] = f @^-1` [set y / x].
Proof.
move=> x0; apply/seteqP; rewrite /preimage; split => [z/= <-|z/= ->].
  by rewrite mulrAC divrr ?mul1r// unitfE.
by rewrite mulrCA divrr ?mulr1// unitfE.
Qed.

Lemma preimage_add_in T (R : numDomainType) (D : set T) (f g : T -> R) z :
  D `&` (f \+ g) @^-1` [set z] = \bigcup_(a in f @` D)
    ((D `&` f @^-1` [set a]) `&` (D `&` g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= [Dx fgz]|x [_ /= [y _ <-]] []].
  have : z - f x \in g @` D.
    by rewrite inE /=; exists x=> //; rewrite -fgz addrC addKr.
  rewrite inE /= => -[x' _ gzf]; exists (z - g x')%R => /=.
    by exists x => //; rewrite gzf opprB addrC subrK.
  rewrite /preimage /=; split; first by rewrite gzf opprB addrC subrK.
  by split=> //; rewrite gzf opprB addrC subrK -fgz addrC addKr.
rewrite /preimage /= => [[Dx fxfy] [_ gzf]].
by split=>//; rewrite gzf -fxfy addrC subrK.
Qed.

Lemma preimage_add T (R : numDomainType) (f g : T -> R) z :
  (f \+ g) @^-1` [set z] = \bigcup_(a in f @` setT)
    ((f @^-1` [set a]) `&` (g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= [fgz]|x [_ /= [y _ <-]] []].
  have : z - f x \in g @` setT.
    by rewrite inE /=; exists x=> //; rewrite -fgz addrC addKr.
  rewrite inE /= => -[x' _ gzf]; exists (z - g x')%R => /=.
    by exists x => //; rewrite gzf opprB addrC subrK.
  rewrite /preimage /=; split; first by rewrite gzf opprB addrC subrK.
  by rewrite gzf opprB addrC subrK -fgz addrC addKr.
rewrite /preimage /= => [fxfy gzf].
by rewrite gzf -fxfy addrC subrK.
Qed.

Lemma finite_set_times_preimage (I : Type) (P : set I) (R : Type) (zero : R)
  (times : Monoid.mul_law zero) (g : I -> R) (F : I -> R) :
  finite_set (P `&` F @^-1` [set~ zero]) ->
  finite_set (P `&` (fun i => times (g i) (F i)) @^-1` [set~ zero]).
Proof.
apply: sub_finite_set => i [Pi aFi].
by split => //; apply: contra_not aFi => ->; rewrite Monoid.simpm.
Qed.

Lemma finite_set_preimage_setM1 (R : numDomainType) (m : R -> R -> \bar R) :
  finite_set ((fun r => m r.1 r.2) @^-1` [set~ 0%E]) ->
  finite_set ((fun r => (r.1%:E * m r.1 r.2)%E) @^-1` [set~ 0%E]).
Proof.
apply: sub_finite_set => x; rewrite /preimage/=.
by apply: contra_not => ->; rewrite mule0.
Qed.

Lemma finite_set_preimage_setM2 (R : numDomainType) (m : R -> R -> \bar R) :
  finite_set ((fun r => m r.1 r.2) @^-1` [set~ 0%E]) ->
  finite_set ((fun r => (r.2%:E * m r.1 r.2)%E) @^-1` [set~ 0%E]).
Proof.
apply: sub_finite_set => x; rewrite /preimage/=.
by apply: contra_not => ->; rewrite mule0.
Qed.

Lemma finite_set_measure_preimage_in (T : measurableType) (R : realType)
    (D : set T) (f : {nnsfun T >-> R}) (h : R -> R)
    (mu : {measure set T -> \bar R}) : bijective h ->
  finite_set ((fun x => mu (D `&` f @^-1` [set h x])) @^-1` [set~ 0%E]).
Proof.
case=> h1 hh1 h1h.
have : finite_set [set (h1 \o f) x | x in D].
  have [n H] := @fimfunP _ _ f.
  exists n; rewrite /=; apply: card_eq_trans H; rewrite -image_comp.
(*   apply (@inj_card_eq _ _ _ h1) => x y _ _. *)
(*   by apply: bij_inj; exists h. *)
(* apply: sub_finite_set => r/= mu0. *)
(* apply/not_exists2P => k; apply: mu0. *)
(* rewrite (_ : _ `&` _ = set0) ?measure0//. *)
(* apply/seteqP; split=> // t [Dt/= ftr]. *)
(* have [//|] := k t. *)
(* by rewrite ftr hh1. *)
Admitted.
Arguments finite_set_measure_preimage_in {T R D} _ _.

Lemma finite_set_measure_preimage (T : measurableType) (R : realType)
    (f : {nnsfun T >-> R}) (h : R -> R)
    (mu : {measure set T -> \bar R}) : bijective h ->
  finite_set ((fun x => mu (f @^-1` [set h x])) @^-1` [set~ 0%E]).
Proof.
case=> h1 hh1 h1h.
have : finite_set [set (h1 \o f) x | x in setT].
  have [n H] := @fimfunP _ _ f.
  exists n; rewrite /=; apply: card_eq_trans H; rewrite -image_comp.
  apply (@inj_card_eq _ _ _ h1) => x y _ _.
  by apply: bij_inj; exists h.
apply: sub_finite_set => r/= mu0.
apply/not_exists2P => k; apply: mu0 => /=.
rewrite -[RHS](measure0 [additive_measure of mu])/=.
congr (mu _).
apply/seteqP; split=> // t /=; have [//|] := k t.
by rewrite /preimage/=; apply: contra_not => ->; rewrite hh1.
Qed.
Arguments finite_set_measure_preimage {T R} _ _.

Lemma finite_set_measure_preimage_in1 (T : measurableType) (R : realType)
    (D : set T)  (f : {nnsfun T >-> R}) (mu : {measure set T -> \bar R}) :
  finite_set ((fun x => mu (D `&` f @^-1` [set x])) @^-1` [set~ 0%E]).
Proof. by apply: (finite_set_measure_preimage_in _ id); exists id. Qed.

Lemma finite_set_measure_preimage1 (T : measurableType) (R : realType)
     (f : {nnsfun T >-> R}) (mu : {measure set T -> \bar R}) :
  finite_set ((fun x => mu (f @^-1` [set x])) @^-1` [set~ 0%E]).
Proof. by apply: (finite_set_measure_preimage _ id); exists id. Qed.
(* /about preimages *)

Section nnsfun_functions.
Variables (T : measurableType) (R : realType).

Lemma cst_nnfun_subproof (x : {nonneg R}) : @IsNonNegFun T R (cst x%:nngnum).
Proof. by split=> //= _; apply: Nonneg.nngnum_ge0. Qed.
HB.instance Definition _ x := @cst_nnfun_subproof x.

Definition cst_nnsfun (r : {nonneg R}) := [the {nnsfun T >-> R} of cst r%:nngnum].

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%R%:nng.

Lemma indic_nnfun_subproof (D : set T) : @IsNonNegFun T R (\1_D).
Proof. by split=> //=; rewrite /indic. Qed.
HB.instance Definition _ D := @indic_nnfun_subproof D.

HB.instance Definition _ D (mD : measurable D) :
   @NonNegFun T R (mindic R mD) := NonNegFun.on (mindic R mD).

End nnsfun_functions.
Arguments nnsfun0 {T R}.

Section nnfun_bin.
Variables (T : Type) (R : numDomainType) (f g : {nnfun T >-> R}).

Lemma add_nnfun_subproof : @IsNonNegFun T R (f \+ g).
Proof. by split => x; rewrite addr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := add_nnfun_subproof.

Lemma mul_nnfun_subproof : @IsNonNegFun T R (f \* g).
Proof. by split => x; rewrite mulr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := mul_nnfun_subproof.

Lemma max_nnfun_subproof : @IsNonNegFun T R (f \max g).
Proof. by split => x /=; rewrite /maxr; case: ifPn => _; apply: fun_ge0. Qed.
HB.instance Definition _ := max_nnfun_subproof.

End nnfun_bin.

Section nnsfun_bin.
Variables (T : measurableType) (R : realType) (f g : {nnsfun T >-> R}).

HB.instance Definition _ := MeasurableFun.on (f \+ g).
Definition add_nnsfun := [the {nnsfun T >-> R} of f \+ g].

HB.instance Definition _ := MeasurableFun.on (f \* g).
Definition mul_nnsfun := [the {nnsfun T >-> R} of f \* g].

HB.instance Definition _ := MeasurableFun.on (f \max g).
Definition max_nnsfun := [the {nnsfun T >-> R} of f \max g].

Definition indic_nnsfun A (mA : measurable A) := [the {nnsfun T >-> R} of mindic R mA].

End nnsfun_bin.
Arguments add_nnsfun {T R} _ _.
Arguments mul_nnsfun {T R} _ _.
Arguments max_nnsfun {T R} _ _.

(*Section nnsfun_bin.
Variables (T : measurableType) (R : realType) (f g : {nnsfun [set: T] >-> R}).

Lemma add_mfun_subproof : @IsMeasurableFun T _ setT (f \+ g).
Proof. by split; apply: measurable_funD. Qed.
HB.instance Definition _ := add_mfun_subproof.
Definition nnsfun_add := [the {nnsfun setT >-> R} of f \+ g].

Lemma mul_mfun_subproof : @IsMeasurableFun T _ setT (f \* g).
Proof. by split; apply: measurable_funM. Qed.
HB.instance Definition _ := mul_mfun_subproof.
Definition nnsfun_mul := [the {nnsfun setT >-> _} of f \* g].

Lemma max_mfun_subproof : @IsMeasurableFun T _ setT (f \max g).
Proof. by split; apply: measurable_fun_max. Qed.
HB.instance Definition _ := max_mfun_subproof.
Definition nnsfun_max := [the {nnsfun setT >-> _} of f \max g].

End nnsfun_bin.
Arguments nnsfun_add {T R} _ _.
Arguments nnsfun_max {T R} _ _.*)

Section nnsfun_iter.
Variables (T : measurableType) (R : realType) (D : set T).
Variable f : {nnsfun T >-> R}^nat.

Definition sum_nnsfun n := \big[add_nnsfun/nnsfun0]_(i < n) f i.

Lemma sum_nnsfunE n t : sum_nnsfun n t = \sum_(i < n) (f i t).
Proof. by rewrite /sum_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

Definition bigmax_nnsfun n := \big[max_nnsfun/nnsfun0]_(i < n) f i.

Lemma bigmax_nnsfunE n t : bigmax_nnsfun n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /bigmax_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

End nnsfun_iter.

Lemma Iiota (n : nat) : [set` iota 0 n] = `I_n.
Proof. by apply/seteqP; split => [|] ?; rewrite /= mem_iota add0n. Qed.

Definition fst_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T1} :=
  [fset x.1 | x in A]%fset.
Definition snd_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T2} :=
  [fset x.2 | x in A]%fset.
Notation "A .`1" := (fst_fset A) : fset_scope.
Notation "A .`2" := (snd_fset A) : fset_scope.

Lemma finite_set_snd (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite_set A -> finite_set A.`2.
Proof.
move=> /finite_fsetP[B A_B]; apply/finite_fsetP; exists (B.`2)%fset.
apply/seteqP; split=> [y/= [x]|_/= /imfsetP[[x1 x2]/= +] ->]; rewrite A_B;
  by [move=> xyB; apply/imfsetP; exists (x, y)|move=> ?; exists x1].
Qed.

Lemma finite_set_fst (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite_set A -> finite_set A.`1.
Proof.
move=> /finite_fsetP[B A_B]; apply/finite_fsetP; exists (B.`1)%fset.
by apply/seteqP; split=> [x/= [y]|_/= /imfsetP[[x1 x2]/= +] ->]; rewrite A_B;
  [move=> xyB; apply/imfsetP; exists (x, y)|move=> ?; exists x2].
Qed.

(* NB: this generalizes trivIset_setI{l,r} *)
Lemma trivIset_setIl0 (T I : Type) (D : set I) (F : I -> set T) (G : I -> set T) :
  trivIset D F -> trivIset D (fun i => G i `&` F i).
Proof.
by move=> tF i j Di Dj [x [[Gix Fix] [Gjx Fjx]]]; apply tF => //; exists x.
Qed.

Lemma trivIset_setIr0 (T I : Type) (D : set I) (F : I -> set T) (G : I -> set T) :
  trivIset D F -> trivIset D (fun i => F i `&` G i).
Proof.
by move=> tF i j Di Dj [x [[Fix Gix] [Fjx Gjx]]]; apply tF => //; exists x.
Qed.

(* dependent version of setM, see also voir csum_csum dans measure.v *)
Reserved Notation "A `*d` B"  (at level 46, left associativity).
Definition setM_depr T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | A1 z.1 /\ A2 z.1 z.2].
Notation "A `*d` B" := (setM_depr A B) : classical_set_scope.

Lemma finite_setM_depr (T T' : choiceType) (A : set T) (B : T -> set T') :
  finite_set A -> (forall x, finite_set (B x)) -> finite_set (A `*d` B).
Proof.
move=> /finite_fsetP[A' AA'] finB.
have [B' BB'] : exists B' : T -> {fset T'}, forall t, B t = [set` B' t].
  have {}finB x : exists B' : {fset T'}, B x = [set` B'].
    by have /finite_fsetP := finB x.
  by move/choice : finB => [B' ?]; exists B'.
apply/finite_fsetP; exists [fset ((x, y) : T * T')%type | x in A', y in B' x]%fset.
apply/predeqP => x; split.
  move=> [Ax1 Bx2] /=; apply/imfset2P.
  exists x.1 => /=; first by move: Ax1; rewrite AA'.
  exists x.2; first by move: Bx2; rewrite BB'.
  by case: x Ax1 Bx2.
by move=> /imfset2P[x1/= x1A' [x2 x2B'] ->{x}]; split=> /=; [rewrite AA'|rewrite BB'].
Qed.

Reserved Notation "A `d*` B"  (at level 46, left associativity).
Definition setM_depl T1 T2 (A1 : T2 -> set T1) (A2 : set T2) := [set z | A1 z.2 z.1 /\ A2 z.2].
Notation "A `d*` B" := (setM_depl A B) : classical_set_scope.

Lemma finite_setM_depl (T T' : choiceType) (A : T' -> set T) (B : set T') :
  (forall x, finite_set (A x)) -> finite_set B -> finite_set (A `d*` B).
Proof.
move=> finA /finite_fsetP[B' BB'].
have [A' AA'] : exists A' : T' -> {fset T}, forall t, A t = [set` A' t].
  have {}finA x : exists A' : {fset T}, A x = [set` A'].
    by have /finite_fsetP := finA x.
  by move/choice : finA => [A' ?]; exists A'.
apply/finite_fsetP; exists [fset ((x, y) : T * T')%type | y in B', x in A' y]%fset.
apply/predeqP => x; split.
  move=> [Ax1x2 Bx2] /=; apply/imfset2P.
  exists x.2 => /=; first by move: Bx2; rewrite BB'.
  exists x.1; first by move: Ax1x2; rewrite AA'.
  by case: x Ax1x2 Bx2.
by move=> /imfset2P[x1/= x1A' [x2 x2B'] ->{x}]; split=> /=; [rewrite AA'|rewrite BB'].
Qed.

(* about sum over finite support *)
Reserved Notation "\big [ op / idx ]_ ( i '\in' A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  '\in'  A ) '/  '  F ']'").
Notation "\big [ op / idx ]_ ( i '\in' A ) F" :=
  (\big[op/idx]_(i <- fset_set (A `&` ((fun i => F) @^-1` [set~ idx]))) F)
    (only parsing) : big_scope.

Lemma finite_index_key : unit. Proof. exact: tt. Qed.
Definition finite_support {I : choiceType} {T : Type} (idx : T) (D : set I)
    (F : I -> T) : seq I :=
  locked_with finite_index_key (fset_set (D `&` F @^-1` [set~ idx] : set I)).
Notation "\big [ op / idx ]_ ( i '\in' D ) F" :=
    (\big[op/idx]_(i <- finite_support idx D (fun i => F)) F)
  : big_scope.

Lemma in_finite_support (T : Type) (J : choiceType) (i : T) (P : set J)
    (F : J -> T) : finite_set (P `&` F @^-1` [set~ i]) ->
  finite_support i P F =i P `&` F @^-1` [set~ i].
Proof. by move=> finF j; rewrite /finite_support unlock in_fset_set. Qed.

Lemma finite_support_uniq (T : Type) (J : choiceType) (i : T) (P : set J)
    (F : J -> T) : uniq (finite_support i P F).
Proof. by rewrite /finite_support unlock; exact: fset_uniq. Qed.
Hint Resolve finite_support_uniq : core.

Lemma no_finite_support (T : Type) (J : choiceType) (i : T) (P : set J)
    (F : J -> T) : infinite_set (P `&` F @^-1` [set~ i]) ->
  finite_support i P F = [::].
Proof.
move=> infinF; rewrite /finite_support unlock.
by rewrite /fset_set/=; case: pselect => //.
Qed.

Lemma eq_preimage {I T : Type} (D : set I) (A : set T) (F G : I -> T) :
  {in D, F =1 G} -> D `&` F @^-1` A = D `&` G @^-1` A.
Proof.
move=> eqFG; apply/predeqP => i.
by split=> [] [Di FAi]; split; rewrite /preimage//= (eqFG,=^~eqFG) ?inE.
Qed.

Lemma eq_finite_support {I : choiceType} {T : Type} (idx : T) (D : set I)
    (F G : I -> T) : {in D, F =1 G} ->
  finite_support idx D F = finite_support idx D G.
Proof.
by move=> eqFG; rewrite /finite_support !unlock// (eq_preimage _ eqFG).
Qed.

Variant finite_support_spec R (T : choiceType)
  (P : set T) (F : T -> R) (idx : R) : seq T -> Type :=
| NoFiniteSupport of infinite_set (P `&` F @^-1` [set~ idx]) :
    finite_support_spec P F idx [::]
| FiniteSupport (X : {fset T}) of [set` X] `<=` P
   & (forall i, P i -> i \notin X -> F i = idx)
   & [set` X] = (P `&` F @^-1` [set~ idx]) :
    finite_support_spec P F idx X.

Lemma finite_supportP R (T : choiceType) (P : set T) (F : T -> R) (idx : R) :
  finite_support_spec P F idx (finite_support idx P F).
Proof.
rewrite /finite_support unlock/= /fset_set.
case: pselect=> // Xfin; last by constructor.
case: cid => //= X eqX; constructor; rewrite -?eqX//.
move=> i Pi NXi /=; have : (P `\` [set` X]) i by split=> //=; apply/negP.
by rewrite -eqX /= => -[_]; apply: contra_notP.
Qed.

Reserved Notation "\sum_ ( i '\in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
    format "'[' \sum_ ( i  '\in'  A ) '/  '  F ']'").
Notation "\sum_ ( i '\in' A ) F" := (\big[+%R/0%R]_(i \in A) F) : ring_scope.
Notation "\sum_ ( i '\in' A ) F" := (\big[+%E/0%E]_(i \in A) F) : ereal_scope.

Section fsbig0.
Variables (R : Type) (idx : R) (op : R -> R -> R).

Lemma eq_fsbigl (T : choiceType) (f : T -> R) (P Q : set T) :
  P = Q -> \big[op/idx]_(x \in P) f x = \big[op/idx]_(x \in Q) f x.
Proof. by move=> ->. Qed.
End fsbig0.

Lemma eq_fsbigr (R : Type) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (f g : T -> R) (P : set T) :
  {in P, f =1 g} -> (\big[op/idx]_(x \in P) f x = \big[op/idx]_(x \in P) g x).
Proof.
move=> fg; rewrite (eq_finite_support _ fg); apply: eq_big_seq => x.
by case: finite_supportP => //= X XP _ gidx xX; rewrite fg // ?inE; apply/XP.
Qed.

Lemma fsbigTE (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (A : {fset T}) (f : T -> R) :
    (forall i, i \notin A -> f i = idx) ->
  \big[op/idx]_(i \in [set: T]) f i = \big[op/idx]_(i <- A) f i.
Proof.
elim/Peq: R => R in idx op f *.
move=> Af; have Afin : finite_set (f @^-1` [set~ idx]).
  by apply: (finite_subfset A) => x; apply: contra_notT => /Af.
rewrite [in RHS](big_fsetID _ [pred x | f x == idx])/=.
rewrite [X in _ = op X _]big_fset [X in _ = op X _]big1 ?Monoid.simpm//; last first.
  by move=> i /= /eqP.
apply eq_fbigl => r.
rewrite in_finite_support// ?setTI// /preimage/=; apply/idP/idP => /=.
  rewrite !inE/=; apply: contra_notP => /negP.
  by rewrite negb_and negbK => /orP[|/eqP//]; exact: Af.
by rewrite !inE/= => /andP[_ /eqP].
Qed.
Arguments fsbigTE {R idx op T} A f.

Lemma fsbig_mkcond (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (A : set T) (f : T -> R) :
  \big[op/idx]_(i \in A) f i = \big[op/idx]_(i \in [set: T]) if i \in A then f i else idx.
Proof.
elim/Peq: R => R in idx op f *.
rewrite -big_mkcond/= -[in RHS]big_filter; apply: perm_big.
rewrite uniq_perm ?filter_uniq//= => i; rewrite mem_filter.
set g := fun i => if i \in A then f i else idx.
have gAf : setT `&` g @^-1` [set~ idx] = (A `&` [eta f] @^-1` [set~ idx]).
  rewrite setTI; apply/predeqP => x; split; rewrite /preimage/g/=.
    by case: ifPn; rewrite (inE, notin_set).
  by case: ifPn; rewrite (inE, notin_set) => ? [].
case: finite_supportP => //.
  rewrite -gAf; case: finite_supportP=> //=; first by rewrite ?inE andbF.
  by move=> X _ gidx <-//.
move=> X XA fidx XE; case: finite_supportP; rewrite gAf -?XE//=.
move=> Y _ gidx /predeqP/=/(_ _)/propext YX.
by apply/idP/andP => [|[]]; rewrite YX// inE => Xi; split=> //; apply: XA.
Qed.

Lemma fsbig_mkcondr (R : Type) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (I J : set T) (a : T -> R) :
  \big[op/idx]_(i \in I `&` J) a i = \big[op/idx]_(i \in I) if i \in J then a i else idx.
Proof.
rewrite fsbig_mkcond [RHS]fsbig_mkcond; apply: eq_fsbigr => i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma fsbig_mkcondl (R : Type) (idx : R) (op : Monoid.com_law idx)
     (T : choiceType) (I J : set T) (a : T -> R) :
  \big[op/idx]_(i \in I `&` J) a i = \big[op/idx]_(i \in J) if i \in I then a i else idx.
Proof.
rewrite fsbig_mkcond [RHS]fsbig_mkcond; apply: eq_fsbigr => i _.
by rewrite in_setI; case: (i \in I) (i \in J) => [] [].
Qed.

Lemma bigfs (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (r : seq T) (P : {pred T}) (f : T -> R) : uniq r ->
    (forall i, P i -> i \notin r -> f i = idx) ->
  \big[op/idx]_(i <- r | P i) f i = \big[op/idx]_(i \in [set` P]) f i.
Proof.
move=> r_uniq fidx; rewrite fsbig_mkcond.
rewrite (fsbigTE [fset x | x in r]%fset); last first.
  by move=> i; rewrite inE/= mem_setE; case: ifP=> // + /fidx->.
rewrite -big_mkcond; under [RHS]eq_bigl do rewrite mem_setE.
by apply: perm_big; rewrite uniq_perm// => i; rewrite !inE.
Qed.

Lemma fsbigE (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (A : set T) (r : seq T) (f : T -> R) :
    uniq r ->
    [set` r] `<=` A ->
    (forall i, A i -> i \notin r -> f i = idx) ->
  \big[op/idx]_(i \in A) f i = \big[op/idx]_(i <- r | i \in A) f i.
Proof.
move=> r_uniq rQ fidx; rewrite [RHS]bigfs ?set_mem_set//=.
by move=> i; rewrite inE; apply: fidx.
Qed.
Arguments fsbigE {R idx op T A}.

Lemma fsbig_seq (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (r : seq I) (F : I -> R) :
  uniq r ->
  \big[op/idx]_(a <- r) F a = \big[op/idx]_(a \in [set` r]) F a.
Proof.
move=> ur; rewrite (fsbigE r)//=; last by move=> + ->.
by rewrite mem_setE big_seq_cond big_mkcondr.
Qed.

Lemma fsbig1 (R : Type) (idx : R) (op : Monoid.law idx) (I : choiceType)
    (P : set I) (F : I -> R) :
  (forall i, P i -> F i = idx) -> \big[op/idx]_(i \in P) F i = idx.
Proof.
move=> PF0; rewrite big1_seq// => i/=; case: finite_supportP=> //=.
by move=> X XP _ _ Xi; rewrite PF0//; apply/XP.
Qed.

Lemma fsbig_dflt (R : Type) (idx : R) (op : Monoid.law idx) (I : choiceType)
    (P : set I) (F : I -> R) :
  infinite_set (P `&` F @^-1` [set~ idx])-> \big[op/idx]_(i \in P) F i = idx.
Proof. by case: finite_supportP; rewrite ?big_nil// => X _ _ <-. Qed.

Lemma fsbig_widen (T : choiceType) [R : Type] [idx : R]
    (op : Monoid.com_law(*NB: was Monoid.law*) idx) (P D : set T) (f : T -> R) :
    P `<=` D ->
    D `\` P `<=` f @^-1` [set idx] ->
  \big[op/idx]_(i \in P) f i = \big[op/idx]_(i \in D) f i.
Proof.
move=> PD DPf; rewrite fsbig_mkcond [RHS]fsbig_mkcond.
apply: eq_fsbigr => x _; case: ifPn; rewrite (inE, notin_set) => Px.
  by rewrite ifT// inE; apply: PD.
by case: ifP => //; rewrite inE => Dx; rewrite DPf.
Qed.
Arguments fsbig_widen {T R idx op} P D f.

Lemma fsbig_fwiden (T : choiceType) [R : eqType] [idx : R]
    (op : Monoid.com_law(*NB: was Monoid.law*) idx)
    (r : seq T) (P : set T) (f : T -> R) :
  P `<=` [set` r] ->
  uniq r ->
  [set i | i \in r] `\` P `<=` f @^-1` [set idx] ->
  \big[op/idx]_(i \in P) f i = \big[op/idx]_(i <- r) f i.
Proof. by move=> *; rewrite (fsbig_widen _ [set` r])// [RHS]fsbig_seq. Qed.
Arguments fsbig_fwiden {T R idx op} r P f.

Lemma fsbig_set0 (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
  (F : T -> R) : \big[op/idx]_(x \in set0) F x = idx.
Proof. by rewrite (fsbigE [::])// big_nil. Qed.

Lemma fsbig_set1 (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType) x
  (F : T -> R) : \big[op/idx]_(y \in [set x]) F y = F x.
Proof.
rewrite (fsbigE [:: x])//= ?big_cons ?big_nil ?ifT ?inE ?Monoid.simpm//.
  by move=> y /=; rewrite inE => /eqP.
by move=> i ->; rewrite inE eqxx.
Qed.

#[deprecated(note="Use fsbigID instead")]
Lemma full_fsbigID (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (B : set I) (A : set I) (F : I -> R) :
  finite_set (A `&` F @^-1` [set~ idx]) ->
  \big[op/idx]_(i \in A) F i = op (\big[op/idx]_(i \in A `&` B) F i)
                                  (\big[op/idx]_(i \in A `&` ~` B) F i).
Proof.
move=> finF; rewrite (big_fsetID _ [pred i | i \in B])/=; congr (op _ _).
  rewrite [locked_with _ _]unlock.
  apply: eq_fbigl => i /=; apply/idP/idP.
    rewrite !inE/= => /andP[+ Bi].
    rewrite in_fset_set// inE => -[Ai Fi].
    rewrite unlock in_fset_set ?inE// setIAC; first by rewrite inE in Bi.
    exact/finite_setIl.
  rewrite unlock in_fset_set; last by rewrite setIAC; exact/finite_setIl.
  rewrite inE => -[[Ai Bi] Fi0]; rewrite !inE/=; apply/andP; split; last first.
    by rewrite inE.
  by rewrite in_fset_set// inE.
rewrite [locked_with _ _]unlock.
apply: eq_fbigl => i/=; apply/idP/idP.
  rewrite inE/= inE/= => /andP[+ Bi].
  rewrite in_fset_set// inE => -[Ai Fi].
  rewrite unlock in_fset_set ?inE//; last first.
    by rewrite setIAC; exact/finite_setIl.
  by split=> //; split=> //; rewrite notin_set in Bi.
rewrite unlock in_fset_set; last first.
  by rewrite setIAC; apply/finite_setIl.
rewrite inE => -[[Ai Bi] Fi0].
rewrite !inE/=; apply/andP; split; last by rewrite notin_set.
by rewrite in_fset_set ?inE.
Qed.
Arguments full_fsbigID {R idx op I} B.

Lemma fsbigID (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (B : set I) (A : set I) (F : I -> R) :
    finite_set A ->
  \big[op/idx]_(i \in A) F i = op (\big[op/idx]_(i \in A `&` B) F i)
                                  (\big[op/idx]_(i \in A `&` ~` B) F i).
Proof. by move=> Afin; apply: full_fsbigID; apply: finite_setIl. Qed.
Arguments fsbigID {R idx op I} B.

Lemma fsbigD1 (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (i : I) (A : set I) (F : I -> R) :
     finite_set A -> A i ->
  \big[op/idx]_(j \in A) F j = op (F i) (\big[op/idx]_(j \in A `\ i) F j).
Proof. by move=> *; rewrite (fsbigID [set i]) ?setI1 ?ifT ?inE ?fsbig_set1. Qed.
Arguments fsbigD1 {R idx op I} i A F.

Lemma full_fsbig_distrr (R : Type) (zero : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times) (I : choiceType) (a : R) (P : set I)
    (F : I -> R) :
  finite_set (P `&` F @^-1` [set~ zero]) (*NB: not needed in the integral case*)->
  times a (\big[plus/zero]_(i \in P) F i) =
  \big[plus/zero]_(i \in P) times a (F i).
Proof.
move=> finF; elim/Peq : R => R in zero times plus a F finF *.
have [->|a0] := eqVneq a zero.
  by rewrite Monoid.mul0m fsbig1//; move=> i _; rewrite Monoid.mul0m.
rewrite big_distrr [RHS](full_fsbigID (F @^-1` [set zero])); last first.
  exact: finite_set_times_preimage.
rewrite [X in plus X _](_ : _ = zero) ?Monoid.simpm; last first.
  by rewrite fsbig1// => i [_ ->]; rewrite Monoid.simpm.
apply/esym/fsbig_fwiden => //.
  by move=> x [Px Fx0]; rewrite /= in_finite_support// inE.
move=> i []; rewrite /preimage/= in_finite_support //.
by rewrite !inE => -[Pi]; rewrite /preimage/= => Fi0; tauto.
Qed.

Lemma fsbig_distrr (R : Type) (zero : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times) (I : choiceType) (a : R) (P : set I)
    (F : I -> R) :
  finite_set P (*NB: not needed in the integral case*) ->
  times a (\big[plus/zero]_(i \in P) F i) =
  \big[plus/zero]_(i \in P) times a (F i).
Proof. by move=> Pf; apply: full_fsbig_distrr; apply: finite_setIl. Qed.

Lemma mulr_fsumr (R : idomainType) (I : choiceType) a (P : set I) (F : I -> R) :
   a * (\sum_(i \in P) F i) = \sum_(i \in P) a * F i.
Proof.
have [->|aN0] := eqVneq a 0; first by rewrite mul0r big1// => i; rewrite mul0r.
case: (pselect (finite_set (P `&` F @^-1` [set~ 0]))) => PFfin.
  exact: full_fsbig_distrr.
rewrite !fsbig_dflt ?mulr0//; apply: contra_not PFfin; apply: sub_finite_set.
by move=> x [Px /eqP Fx0]; split=> //=; apply/eqP; rewrite mulf_neq0.
Qed.

Lemma mulr_fsuml (R : idomainType) (I : choiceType) a (P : set I) (F : I -> R) :
   (\sum_(i \in P) F i) * a = \sum_(i \in P) (F i * a).
Proof. by rewrite mulrC mulr_fsumr; under eq_fsbigr do rewrite mulrC. Qed.

Lemma fsbig_ord R (idx : R) (op : Monoid.com_law idx) n (F : nat -> R) :
  \big[op/idx]_(a < n) F a = \big[op/idx]_(a \in `I_n) F a.
Proof.
rewrite -(big_mkord xpredT) [LHS]fsbig_seq ?iota_uniq//.
by apply: eq_fsbigl; rewrite -Iiota /index_iota subn0.
Qed.

Lemma fsbig_finite (R : Type) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (D : set T) (F : T -> R) : finite_set D ->
  \big[op/idx]_(x \in D) F x = \big[op/idx]_(x <- fset_set D) F x.
Proof.
elim/Peq: R => R in idx op F * => Dfin.
by apply: fsbig_fwiden; rewrite ?fset_setK// setDv.
Qed.

Section fsbig2.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

(* Lemma reindex_inside I F P ...  : finite_set (P `&` F @` [set~ id]) -> ... *)
Lemma reindex_fsbig {I J : choiceType} (h : I -> J) P Q
    (F : J -> R) : set_bij P Q h ->
  \big[op/idx]_(j \in Q) F j = \big[op/idx]_(i \in P) F (h i).
Proof.
elim/choicePpointed: I => I in h P *.
  rewrite !emptyE => /Pbij[{}h ->].
  by rewrite -[in LHS](image_eq h) image_set0 !fsbig_set0.
elim/choicePpointed: J => J in F h Q *; first by have := no (h point).
move=> /(@pPbij _ _ _)[{}h ->].
pose A := P `&` (F \o h) @^-1` [set~ idx].
pose B := Q `&` F @^-1` [set~ idx].
have /(@pPbij _ _ _)[g gh] : set_bij A B h.
  apply: splitbij_sub; rewrite /A /B /preimage //=.
    by move=> x [Px Fhx]; split=> //; apply: funS.
  by move=> x [Qx Fx]; split; rewrite ?invK ?inE//; apply: funS.
case: finite_supportP; rewrite ?big_nil//=.
  case: finite_supportP; rewrite ?big_nil//=.
  move=> X XP _ XE []; rewrite -/B -(image_eq g) /A.
  by apply: finite_image; rewrite -XE.
move=> Y YQ Fidx YE; case: finite_supportP.
  move=> []; rewrite -/A -(image_eq [bij of g^-1%FUN]).
  by apply: finite_image; rewrite /B -YE.
move=> X XP Fhidx XE; suff -> : Y = (h @` X)%fset.
  by rewrite big_imfset// => ? ? ? ? /inj; apply; rewrite inE; apply: XP.
have BY j : (B j) = (j \in Y) by rewrite -[RHS]/([set` Y] j) YE.
have AX i : (A i) = (i \in X) by rewrite -[RHS]/([set` X] i) XE.
rewrite gh; apply/fsetP=> j; apply/idP/imfsetP => [Yj | [i iX ->]]; last first.
  by rewrite -BY; apply: funS; rewrite AX.
by exists (g^-1%FUN j); rewrite ?invK ?inE ?BY// -AX; apply: funS; rewrite BY.
Qed.

Lemma fsbig_image {I J : choiceType} P (h : I -> J) (F : J -> R) : set_inj P h ->
  \big[op/idx]_(j \in h @` P) F j = \big[op/idx]_(i \in P) F (h i).
Proof. by move=> /inj_bij; apply: reindex_fsbig. Qed.

(* Lemma reindex_inside I F P ...  : finite_set (P `&` F @` [set~ id]) -> ... *)
#[deprecated(note="use reindex_fsbig, fsbig_image or reindex_fsbigT instead")]
Lemma reindex_inside {I J : choiceType} P Q (h : I -> J) (F : J -> R) :
  bijective h -> P `<=` h @` Q -> Q `<=` h @^-1` P ->
  \big[op/idx]_(j \in P) F j = \big[op/idx]_(i \in Q) F (h i).
Proof.
move=> hbij PQ QP; apply: reindex_fsbig; split=> //.
by move=> x y _ _ /(bij_inj hbij).
Qed.

Lemma reindex_fsbigT {I J : choiceType} (h : I -> J) (F : J -> R) :
  bijective h ->
  \big[op/idx]_(j \in [set: J]) F j = \big[op/idx]_(i \in [set: I]) F (h i).
Proof.
move=> hbij; apply: reindex_inside => // x _ /=.
by case: hbij => h1 hh1 h1h; exists (h1 x).
Qed.

End fsbig2.
Arguments reindex_fsbig {R idx op I J} _ _ _.
Arguments fsbig_image {R idx op I J} _ _.
Arguments reindex_inside {R idx op I J} _ _.
Arguments reindex_fsbigT {R idx op I J} _ _.
#[deprecated(note="use reindex_fsbigT instead")]
Notation reindex_inside_setT := reindex_fsbigT.

Lemma ge0_mule_fsumr (T : choiceType) (R : realDomainType) (x : \bar R)
    (F : T -> \bar R) (P : set T) : (forall i : T, 0 <= F i)%E ->
  (x * (\sum_(i \in P) F i) = \sum_(i \in P) x * F i)%E.
Proof.
move=> F0; have [->{x}|x0] := eqVneq x 0%E.
  by rewrite mul0e big1// => ? _; rewrite mul0e.
rewrite ge0_sume_distrr//; apply: eq_fbigl => y.
rewrite !unlock; congr (_ \in fset_set _).
apply/seteqP; rewrite /preimage; split=> [|] z/= [Pz Fz0];
  split=> //; apply: contra_not Fz0.
by move=> /eqP; rewrite mule_eq0 (negbTE x0)/= => /eqP.
by move=> ->; rewrite mule0.
Qed.

Lemma ge0_mule_fsuml (T : choiceType) (R : realDomainType) (x : \bar R)
    (F : T -> \bar R) (P : set T) : (forall i : T, 0 <= F i)%E ->
  ((\sum_(i \in P) F i) * x = \sum_(i \in P) F i * x)%E.
Proof.
move=> F0; rewrite muleC ge0_mule_fsumr//.
by apply: eq_fsbigr => i; rewrite muleC.
Qed.

Lemma fsbigN1 (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T1 T2 : choiceType) (Q : set T2) (f : T1 -> T2 -> R) (x : T1) :
  \big[op/idx]_(y \in Q) f x y != idx -> exists2 y, Q y & f x y != idx.
Proof.
apply: contra_neqP => /forall2NP Qf; apply/fsbig1 => y Qy.
by case: (Qf y) => // /negP/negPn/eqP->.
Qed.

Lemma fsume_ge0 (R : numDomainType) (I : choiceType) (P : set I)
    (F : I -> \bar R) :
  (forall i, P i -> (0 <= F i)%E) -> (0 <= \sum_(i \in P) F i)%E.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sume_ge0// => i /XP/PF.
Qed.

Lemma fsume_le0 (R : numDomainType) (T : choiceType) (f : T -> \bar R) (P : set T) :
  (forall t, P t -> (f t <= 0)%E) -> (\sum_(i \in P) f i <= 0)%E.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sume_le0// => i /XP/PF.
Qed.

Lemma fsume_gt0 (R : realDomainType) (I : choiceType) (P : set I)
    (F : I -> \bar R) :
  (0 < \sum_(i \in P) F i)%E -> exists2 i, P i & (0 < F i)%E.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsume_le0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma fsume_lt0 (R : realDomainType) (I : choiceType) (P : set I)
    (F : I -> \bar R) :
  (\sum_(i \in P) F i < 0)%E -> exists2 i, P i & (F i < 0)%E.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsume_ge0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma pfsume_eq0 (R : realDomainType) (I : choiceType) (P : set I)
    (F : I -> \bar R) :
  finite_set P ->
  (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i \in P) F i = 0)%E -> (forall i, P i -> F i = 0%E).
Proof.
move=> Pfin F0 /eqP; apply: contraTP => /existsPNP[i Pi /eqP Fi0].
rewrite (fsbigD1 i)//= padde_eq0 ?F0 ?negb_and ?Fi0//.
by rewrite fsume_ge0// => j [/F0->].
Qed.

Lemma fsbig_setU {T} {I : choiceType} (A : set I) (F : I -> set T) :
  finite_set A ->
  \big[setU/set0]_(i \in A) F i = \bigcup_(i in A) F i.
Proof. by move=> Afin; rewrite fsbig_finite// bigcup_fset_set. Qed.

(*
Lemma pair_fsum (T1 T2 : choiceType) (R : realDomainType)
    (f : T1 -> T2 -> \bar R) (P : set T1) (Q : set T2) :
    (forall x y, 0 <= f x y)%E ->
  (\sum_(x \in P) \sum_(y \in Q) f x y = \sum_(x \in P `*` Q) f x.1 x.2)%E.
Proof.
move=> f0.
apply/esym.
case: finite_supportP => [|].
case: finite_supportP => [infPQ|].
  rewrite big_nil.
  case: finite_supportP => [infPQ'|]; first by rewrite big_nil.
  move=> /= X XPQ PQXf XE; exfalso; apply: infPQ.
  (* finite_set (P `&` (fun x : T1 => (\sum_(y \in Q) f x y)%E) @^-1` [set~ 0%E]) *)
  apply/finite_fsetP; exists (X.`1)%fset; apply/seteqP; split.
    move=> x [Px]; rewrite /preimage/= => Qf.
    have [y Qy fxy] := fsbigNidx Qf.
    suff : (x, y) \in [set` X].
      by rewrite !inE /mkset => xyX; apply/imfsetP => /=; exists (x, y).
    by rewrite XE inE.
  move=> x /imfsetP[z/= zX ->{x}].
  have {zX} : z \in [set` X] by rewrite inE /mkset.
  rewrite XE inE => -[[Pz Qz]]; rewrite /preimage/= => fz0; split => //.
  apply: contra_not fz0 => /eqP.
  have H1 : finite_set (Q `&` [eta f z.1] @^-1` [set~ 0%E]).
    have /finite_set_snd := finite_fset X.
    apply: sub_finite_set => b [Qb]; rewrite /= /preimage/= => fz1b.
    exists z.1.
    suff : (z.1, b) \in [set` X] by rewrite inE.
    by rewrite XE !inE.
  by move=> /eqP/pfsume_eq0 => /(_ H1) ->.
move=> X XP PXQf XE.
pose S (x : T1) (z : {fset T2}) := [/\
    [set` z] = Q `&` (fun y => (f x y)%E) @^-1` [set~ 0%E],
    [set` z] `<=` Q &
    (forall y, Q y -> y \notin z -> f x y = 0%E)].
have : {Y : T1 -> {fset T2} & forall t1, S t1 (Y t1)}.
  admit.
move=> [Y HS].
transitivity (\sum_(x <- X) \sum_(y <- Y x) f x y)%E.
  apply eq_fbigr => x xX _.
  rewrite (fsbigE (Y x))//=.
    admit.
  by have [HY YQ QYf] := HS x.
  move=> y Qy yYx.
  have [_ _ QYf] := HS x.
  by apply QYf => //.
case: finite_supportP.
  move=> abs; exfalso; apply: abs.
  admit.
move=> Z ZPQ Zf ZE.
rewrite pair_big_dep_cond/=; apply: eq_fbigl => /= -[x y].
apply/idP/idP.
  move=> /imfset2P[/= t1].
  rewrite !inE/= andbT /= => Ht1.
  have {Ht1} : t1 \in [set` X] by rewrite inE.
  rewrite XE inE => -[Pt1 Ht1] [t2].
  rewrite !inE/= andbT => Ht2.
  have {Ht2} : t2 \in [set` Y t1] by rewrite inE.
(*  rewrite HY inE => -[Qt2 Ht2] [->{x} ->{y}].
  suff : (t1, t2) \in [set` Z].
    by rewrite inE.
  by rewrite ZE !inE; split => //.
move=> Hz.
have {Hz} : (x, y) \in [set` Z].
  by rewrite inE.
rewrite ZE.
rewrite !inE => -[] [/= Px Qy]; rewrite {1}/preimage/= => fxy0.
apply/imfset2P; exists x => /=.
  rewrite !inE/= andbT.
  suff : x \in [set` X].
    by rewrite inE.
  rewrite XE inE; split => //.
  rewrite /preimage/=.
  apply: contra_not fxy0.
  move/pfsume_eq0.
  apply => //.
  (* finite_set (Q `&` [eta f x] @^-1` [set~ 0%E]) *)
  admit.
exists y => //; rewrite !inE/= andbT.
suff: y \in [set` Y x].
  by rewrite inE.
rewrite HY.
rewrite inE.
by split => //.
Qed.*) Abort.

Lemma pair_fsum (T1 T2 : choiceType) (R : realDomainType)
    (f : T1 -> T2 -> \bar R) (P : set T1) (Q : set T2) :
    (forall x y, 0 <= f x y)%E ->
  (\sum_(x \in P) \sum_(y \in Q) f x y = \sum_(x \in P `*` Q) f x.1 x.2)%E.
Proof.
move=> f0.
case: finite_supportP => [infPQ|].
  rewrite big_nil; case: finite_supportP => [infPQ'|]; first by rewrite big_nil.
  move=> /= X XPQ PQXf XE; exfalso; apply: infPQ.
  apply/finite_fsetP; exists (X.`1)%fset; apply/seteqP; split.
    move=> x [Px]; rewrite /preimage/= => Qf.
    have [y Qy fxy] := fsbigNidx Qf.
    suff : (x, y) \in [set` X].
      rewrite !inE /mkset => xyX.
      by apply/imfsetP => /=; exists (x, y).
    by rewrite XE inE.
  move=> x /imfsetP[z/= zX ->{x}].
  have {zX} : z \in [set` X] by rewrite inE /mkset.
  rewrite XE inE => -[[Pz Qz]]; rewrite /preimage/= => fz0.
  split=> //.
  apply: contra_not fz0 => /eqP.
  rewrite seq_psume_eq0// => /allP.
  move=> /(_ z.2).
  rewrite in_finite_support//; last first.
    (* finite_set (Q `&` [eta f z.1] @^-1` [set~ 0%E]) *)
    have := finite_fset X.
    move/finite_set_snd.
    apply: sub_finite_set => b [Qb]; rewrite /= /preimage/= => fz1b.
    exists z.1.
    suff : (z.1, b) \in [set` X].
      by rewrite inE.
    by rewrite XE !inE; split => //.
  rewrite !inE.
  have [a|] := pselect (z.2 \in [eta f z.1] @^-1` [set~ 0%E]).
    move=> /(_ _)/eqP; apply; split => //.
    by rewrite inE in a.
  by rewrite inE /preimage /= => /contrapT.
move=> X XP PXQf XE.
rewrite pair_big_dep_cond/=; apply: eq_fbigl => /= -[x y].
have H1 : finite_set (P `*` Q `&` (fun x0 : T1 * T2 => f x0.1 x0.2) @^-1` [set~ 0%E]).
  admit.
have H2 t1 : finite_set (Q `&` [eta f t1] @^-1` [set~ 0%E]).
  admit.
apply/idP/idP.
  move=> /imfset2P[/= t1].
  rewrite !inE/= in_finite_support; last first.
    exact: H1.
  rewrite andbT => t1X.
  have {t1X} : t1 \in [set` X] by rewrite inE.
  rewrite XE inE => -[Pt1 Ht1] [t2].
  rewrite !inE/= in_finite_support/=; last first.
    exact: H2.
  rewrite andbT inE => -[Qt2 Ht2] [->{x} ->{y}].
  by split => //.
rewrite in_finite_support; last first.
  exact: H1.
rewrite !inE => -[] [/= Px Qy]; rewrite {1}/preimage/= => fxy0.
apply/imfset2P; exists x => /=.
  rewrite !inE/= andbT.
  suff : x \in [set` X].
    by rewrite inE.
 rewrite XE inE; split => //.
  rewrite /preimage/=.
  apply: contra_not fxy0 => /eqP.
  rewrite seq_psume_eq0// => /allP.
  move=> /(_ y).
  rewrite in_finite_support/=; last first.
    exact: H2.
  rewrite !inE.
  have [a|] := pselect (y \in [eta f x] @^-1` [set~ 0%E]).
    move=> /(_ _)/eqP; apply; split => //.
    by rewrite inE in a.
  by rewrite inE /preimage /= => /contrapT.
exists y => //; rewrite !inE/= andbT unlock/= in_fset_set; last first.
 exact: H2.
by rewrite inE.
Abort.
*)
(* Lemma pair_fsum (T1 T2 : choiceType) (R : realDomainType) *)
(*     (f : T1 -> T2 -> \bar R) (P : set T1) (Q : set T2) : *)
(*     finite_set ((fun z => f z.1 z.2) @^-1` [set~ 0%E]) -> *)
(*     (forall x y, 0 <= f x y)%E (*TODO: this should not be required*)-> *)
(*   (\sum_(x \in P) \sum_(y \in Q) f x y = \sum_(x \in P `*` Q) f x.1 x.2)%E. *)
(* Proof. *)
(* move=> finf f0. *)
(* have H1 x : finite_set (f x @^-1` [set~ 0%E]). *)
(*   by apply: sub_finite_set (finite_set_snd finf) => y fxy; exists x. *)
(* have H2 : finite_set (P `&` (fun x => \sum_(y \in Q) f x y) @^-1` [set~ 0])%E. *)
(*   apply/finite_setIr; apply: sub_finite_set (finite_set_fst finf) => x. *)
(*   rewrite /preimage/= => h. *)
(*   apply/existsNP; apply: contra_not h => H. *)
(*   by rewrite big1. *)
(* rewrite pair_big_dep_cond/=; apply: eq_fbigl => /= -[x y]. *)
(* apply/idP/idP. *)
(*   move=> /imfset2P[/= t1]. *)
(*   rewrite !inE/= in_finite_support//. *)
(*   rewrite andbT; rewrite inE => -[Pt1 Ht1] [t2]. *)
(*   rewrite !inE/= in_finite_support/=; last exact/finite_setIr. *)
(*   rewrite ![locked_with _ _]unlock/= andbT in_fset_set; last exact/finite_setIr. *)
(*   rewrite inE => -[Qt2 Ht2] [->{x} ->{y}]. *)
(*   by rewrite inE. *)
(* rewrite in_finite_support; last exact/finite_setIr. *)
(* rewrite !inE => -[] [/= Px Qy]; rewrite {1}/preimage/= => fxy0. *)
(* (*kkk*) *)
(* apply/imfset2P; exists x => /=. *)
(*   rewrite !inE/= andbT in_finite_support// inE//; split => //. *)
(*   rewrite /preimage/=. *)
(*   apply: contra_not fxy0 => /eqP. *)
(*   rewrite seq_psume_eq0// => /allP. *)
(*   move=> /(_ y). *)
(*   rewrite in_finite_support//; last exact/finite_setIr. *)
(*   rewrite !inE. *)
(*   have [a|] := pselect (y \in [eta f x] @^-1` [set~ 0%E]). *)
(*     move=> /(_ _)/eqP; apply; split => //. *)
(*     by rewrite inE in a. *)
(*   by rewrite inE /preimage /= => /contrapT. *)
(* exists y => //; rewrite !inE/= andbT unlock/= in_fset_set; last first. *)
(*   exact/finite_setIr. *)
(* by rewrite inE. *)
(* Qed. *)

Lemma fset_setM {T1 T2 : choiceType} (A : set T1) (B : set T2) :
    finite_set A -> finite_set B ->
  fset_set (A `*` B) = (fset_set A `*` fset_set B)%fset.
Proof.
move=> Afin Bfin; have ABfin : finite_set (A `*` B) by apply: finite_setX.
apply/fsetP => i; apply/idP/idP; rewrite !(inE, in_fset_set)//=.
  by move=> [/mem_set-> /mem_set->].
by move=> /andP[]; rewrite !inE.
Qed.

Lemma pair_fsum (T1 T2 : choiceType) (R : realDomainType)
    (f : T1 -> T2 -> \bar R) (P : set T1) (Q : set T2) :
    finite_set P -> finite_set Q ->
  (\sum_(x \in P) \sum_(y \in Q) f x y = \sum_(x \in P `*` Q) f x.1 x.2)%E.
Proof.
move=> Pfin Qfin; have PQfin : finite_set (P `*` Q) by apply: finite_setX.
rewrite !fsbig_finite//=; under eq_bigr do rewrite fsbig_finite//=.
rewrite pair_big_dep_cond/= fset_setM//.
apply: eq_fbigl => -[i j] //=; apply/imfset2P/idP; rewrite inE //=.
  by move=> [x + [y + [-> ->]]]; rewrite 4!inE/= !andbT/= => -> ->.
move=> /andP[Pi Qi]; exists i; rewrite 2?inE ?andbT//.
by exists j; rewrite 2?inE ?andbT.
Qed.

Lemma exchange_fsum (T : choiceType) (R : realDomainType) (P Q : set T)
     (f : T -> T -> \bar R) :
    finite_set P -> finite_set Q ->
  (\sum_(i \in P) \sum_(j \in Q) f i j = \sum_(j \in Q) \sum_(i \in P) f i j)%E.
Proof.
move=> Pfin Qfin; rewrite 2?pair_fsum//; pose swap (x : T * T) := (x.2, x.1).
apply: (reindex_fsbig swap).
split=> [? [? ?]//|[? ?] [? ?] /set_mem[? ?] /set_mem[? ?] [-> ->]//|].
by move=> [i j] [? ?]; exists (j, i).
Qed.

Lemma fsum_split (T : choiceType) (R : numDomainType) (P : set T) (f g : T -> \bar R) :
  finite_set P ->
  (\sum_(x \in P) (f x + g x) = \sum_(x \in P) f x + \sum_(x \in P) g x)%E.
Proof. by move=> Pfin; rewrite !fsbig_finite//= big_split. Qed.

(* \sum_(a \in [set: R]) ... *)
(* /about fsum *)

(* Lemma finite_setM_mulr_preimage (R : numDomainType) (m : R -> R -> \bar R) : *)
(*   finite_set ((fun r => m r.1 r.2) @^-1` [set~ 0%E]) -> *)
(*   finite_set ((fun r => r.1%:E * m r.1 r.2) @^-1` [set~ 0])%E. *)
(* Proof. *)
(* apply: sub_finite_set => x; rewrite /preimage/=. *)
(* by apply: contra_not => ->; rewrite mule0. *)
(* Qed. *)

(* Lemma finite_set_image (I : choiceType) (T : Type) (F : I -> T) (A : set I) : *)
(*   finite_set (F @` A) -> finite_set ((fun i => A `&` F @^-1` [set i]) @^-1` [set~ set0]). *)
(* Proof. *)
(* apply: sub_finite_set => y. *)
(* rewrite /preimage/= => /eqP/set0P[z [Dz /= gzy]]. *)
(* by exists z. *)
(* Qed. *)

(* Lemma finite_set_measure (T : measurableType) (R : realType) *)
(*   (m : {measure set T -> \bar R})(I : choiceType) (A : set I) (F : I -> set T) : *)
(*   finite_set (A `&` F @^-1` [set~ set0]) -> *)
(*   finite_set (A `&` (fun i => m (F i)) @^-1` [set~ 0%E]). *)
(* Proof. *)
(* apply: sub_finite_set => i [Ai/= Fi0]; split=> //. *)
(* by apply: contra_not Fi0 => ->; rewrite measure0. *)
(* Qed. *)


Lemma imageT {aT rT : Type} (f : aT -> rT) (a : aT) : [set of f] (f a).
Proof. by apply: imageP. Qed.

Hint Extern 0 ((?f @` _) (?f _)) =>
   solve [apply: imageP; assumption] : core.
Hint Extern 0 ((?f @` setT) _) => solve [apply: imageT] : core.

Lemma preimage0 {T R} {f : T -> R} {A : set R} :
  A `&` [set of f] `<=` set0 -> f @^-1` A = set0.
Proof. by rewrite -subset0 => + x Afx => /(_ (f x))[]; split. Qed.

Lemma preimage10 {T R} {f : T -> R} {x} : ~ [set of f] x -> f @^-1` [set x] = set0.
Proof. by move=> fx; rewrite preimage0// => y [->]. Qed.

Hint Extern 0 (is_true (0 <= (_ : {measure set _ -> \bar _}) _)%E) =>
  solve [apply: measure_ge0] : core.

Lemma measure_negligible [R : realFieldType] [T : ringOfSetsType]
    (mu : {measure set T -> \bar R}) [A : set T] :
  measurable A -> mu.-negligible A -> mu A = 0%E.
Proof. by move=> mA /negligibleP ->. Qed.

Section simple_fun_raw_integral.
Local Open Scope ereal_scope.
Variables (T : Type) (R : numDomainType).

Section def.
Variable (mu : set T -> \bar R) (f : T -> R).
Let s := fset_set (f @` setT).

Definition sintegral := \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).

Lemma sintegralET :
  sintegral = \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).
Proof. by []. Qed.

(* discard ? *)
Lemma sintegralEord : sintegral =
   \sum_(k < #|` fset_set (f @` setT)|) (s`_k)%:E * mu (f @^-1` [set s`_k]).
Proof. (*by rewrite /sintegral (big_nth 0%R) big_mkord. Qed.*) Abort.

End def.

End simple_fun_raw_integral.

Hint Extern 0 (is_true (0 <= (_ : {measure set _ -> \bar _}) _)%E) =>
  solve [apply: measure_ge0] : core.

Section sintegral_nnsfun.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Lemma sintegralE f :
  sintegral mu f = \sum_(x \in [set of f]) x%:E * mu (f @^-1` [set x]).
Proof.
rewrite (fsbig_widen [set of f] setT)//= => x [_ Nfx] /=.
by rewrite preimage10 ?measure0 ?mule0.
Qed.

Lemma mule_ge0_dep (x : R) (A : R -> \bar R) :
  (forall x, 0 <= A x) -> ((x < 0)%R -> A x = 0) -> 0 <= x%:E * A x.
Proof.
move=> A0 xA /=.
have [x0|x0] := ltP x 0%R; first by rewrite (xA x0) mule0.
by rewrite mule_ge0.
Qed.
Arguments mule_ge0_dep {x} _.

Lemma mulem_ge0 x (A : R -> set T) :
  ((x < 0)%R -> A x = set0) -> (0 <= x%:E * mu (A x))%E.
Proof.
by move=> xA; rewrite (@mule_ge0_dep _ (mu \o _))//= => /xA ->; rewrite measure0.
Qed.
Arguments mulem_ge0 {x} _.

Lemma mulem_ge0' (f : {nnsfun T >-> R}) x : (0 <= x%:E * mu (f @^-1` [set x]))%E.
Proof.
apply: (mulem_ge0 (fun x => f @^-1` [set x])).
exact: preimage_nnfun0.
Qed.

Lemma sintegralEnnsfun (f : {nnsfun T >-> R}) : sintegral mu f =
  (\sum_(x \in [set r | r > 0]%R) (x%:E * mu (f @^-1` [set x])))%E.
Proof.
rewrite (fsbig_widen _ setT) ?sintegralET//.
move=> x [_ /=]; case: ltgtP => //= [xlt0 _|<-]; last by rewrite mul0e.
rewrite preimage10 ?measure0 ?mule0//= => -[t _].
by apply/eqP; apply: contra_ltN xlt0 => /eqP<-.
Qed.

End sintegral_nnsfun.
Arguments mulem_ge0 {T R mu x} _.

(*Lemma sintegral0 (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}) D pt :
  sintegral mu D (cst_fimfun pt D 0%R) = 0%E.*)
Lemma sintegral0 (T : measurableType) (R : realType)
  (mu : {measure set T -> \bar R}) : sintegral mu (cst 0) = 0%E.
Proof.
rewrite sintegralE big1// => r _; rewrite preimage_cst.
have [->|r0] := eqVneq r 0%R; first by rewrite mul0e.
by rewrite (measure0 (measure_additive_measure mu)) mule0.
Qed.

Lemma eq_sintegral (T : measurableType) (R : numDomainType) (mu : set T -> \bar R) f g :
   f =1 g -> sintegral mu f = sintegral mu g.
Proof. by move=> /funext->. Qed.

Lemma sintegral_ge0 (T : measurableType) (R : realType)
  (f : {nnsfun T >-> _}) (m : {measure set T -> \bar R}) :
  (0 <= sintegral m f)%E.
Proof.
rewrite sintegralE; apply: sume_ge0 => t _.
have [t0|t0] := leP 0 t.
  by rewrite mule_ge0// measure_ge0//; exact/measurable_sfunP.
by rewrite preimage_nnfun0// measure0 ?mule0.
Qed.

(* TODO: too long? *)
Lemma sintegral_indic (T : measurableType) (R : realType)
    (mu : {measure set T -> \bar R}) (E : set T) (mE : measurable E) :
  sintegral mu \1_E = mu E.
Proof.
(* rewrite sintegralE (fsbigID ([set 1%R] : set R))//=; last first. *)
(*   (* TODO: deserves a lemma? *) *)
(*   rewrite setTI; have := @fimfunP _ _ (indic_nnsfun R mE). *)
(*   apply: sub_finite_set => r; rewrite /preimage/= => h. *)
(*   have [|rE] := boolP (r \in \1_E @` setT). *)
(*     by rewrite inE => -[t] _ tr; exists t. *)
(*   rewrite (_ : [set _ | _ ] = set0) in h; last first. *)
(*     apply/seteqP; split=>// t/= Etr. *)
(*     by move: rE; rewrite notin_set/=; apply; exists t. *)
(*   by move: h; rewrite measure0// mule0. *)
(* rewrite !setTI fsbig_set1 mul1e fsbig1 ?adde0; last first. *)
(*   move=> r /= r1; have [->|/eqP r0] := eqVneq r 0%R; first by rewrite mul0e. *)
(*   rewrite preimage_indic memNset; last exact/nesym. *)
(*   by rewrite memNset ?measure0 ?mule0//; exact/nesym. *)
(* congr (mu _). *)
(* by rewrite preimage_indic mem_set// memNset//=; apply/nesym/eqP/oner_neq0. *)
Admitted.

Section sintegralrM.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable (m : {measure set T -> \bar R}).
Variables (r : R) (f : {nnsfun T >-> R}).

Lemma sintegralrM :
  sintegral m (cst r \* f)%R = r%:E * sintegral m f.
Proof.
have [->|r0] := eqVneq r 0%R.
  rewrite mul0e (_ : (_ \* _)%R = cst 0%R) ?sintegral0// funeqE => x /=.
  by rewrite mul0r.
rewrite !sintegralET.
transitivity (\sum_(x \in [set: R]) x%:E * m (f @^-1` [set x / r])).
  by apply: eq_fsbigr => x; rewrite preimage_cstM.
transitivity (\sum_(x \in [set: R]) r%:E * (x%:E * m (f @^-1` [set x]))).
  rewrite (reindex_fsbigT (fun x => r * x)%R)//; last first.
    by exists ( *%R r ^-1)%R; [exact: mulKf|exact: mulVKf].
  by apply: eq_fsbigr => x; rewrite mulrAC divrr ?unitfE// mul1r muleA EFinM.
by rewrite ge0_mule_fsumr// => x; exact: mulem_ge0'.
Qed.

End sintegralrM.

Hint Extern 0 (measurable [set _]) =>
  solve [apply: measurable_set1] : core.

Section nnsfun_cover.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (f : {nnsfun T >-> R}).

Lemma nnsfun_cover :
  \big[setU/set0]_(i \in [set of f]) (f @^-1` [set i]) = setT.
Proof. by rewrite fsbig_setU//= -subTset => x _; exists (f x). Qed.

Lemma nnsfun_coverT :
  \big[setU/set0]_(i \in [set: R]) (f @^-1` [set i]) = setT.
Proof.
by rewrite -(fsbig_widen [set of f]) ?nnsfun_cover//= => x [_ /= /preimage10->].
Qed.

End nnsfun_cover.

Hint Extern 0 (measurable (_ @^-1` [set _])) =>
  solve [apply: measurable_sfunP] : core.

Lemma measurable_sfun_inP  {aT : measurableType} {rT : realType}
   (f : {mfun aT >-> rT}) D (y : rT) :
  measurable D -> measurable (D `&` f @^-1` [set y]).
Proof. by move=> Dm; apply: measurableI. Qed.

Hint Extern 0 (measurable (_ `&` _ @^-1` [set _])) =>
  solve [apply: measurable_sfun_inP; assumption] : core.

Hint Extern 0 (finite_set _) => solve [apply: fimfunP] : core.

Section measure_fsbig.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (m : {measure set T -> \bar R}).

Lemma measure_fsbig (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A ->
  (forall i, A i -> measurable (F i)) -> trivIset A F ->
  m (\big[setU/set0]_(i \in A) F i) = \sum_(i \in A) m (F i).
Proof.
move=> Afin Fm Ft; rewrite !fsbig_finite//=.
by rewrite -!bigcup_fset_set// measure_fin_bigcup.
Qed.

(* Lemma additive_nnsfun_in (D : set T) (mD : measurable D) (g f : {nnsfun T >-> R}) x : *)
(*   \sum_(i \in [set: R]) m (D `&` f @^-1` [set x] `&` (D `&` g @^-1` [set i])) = *)
(*   m (D `&` f @^-1` [set x] `&` \big[setU/set0]_(i \in [set: R]) (D `&` g @^-1` [set i])). *)
(* Proof. *)
(* rewrite -measure_fsbig. *)
(* - congr (m _); rewrite -[in LHS]full_fsbig_distrr//= setTI. *)
(*   exact/finite_set_image/fimfun_inP. *)
(* - rewrite setTI; apply: sub_finite_set (@fimfunP _ _ g) => r. *)
(*   by move=> /eqP/set0P[y] [_ [Dy fty]]; exists y. *)
(* - by move=> i; apply: measurableI. *)
(* - exact/trivIset_setIl0/trivIset_preimage1_in. *)
(* Qed. *)

Lemma additive_nnsfun (g f : {nnsfun T >-> R}) x :
  \sum_(i \in [set of g]) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in [set of g]) (g @^-1` [set i])).
Proof.
rewrite -?measure_fsbig//.
- by rewrite !fsbig_finite//= big_distrr//.
- by move=> i Ai; apply: measurableI => //.
- exact/trivIset_setI/trivIset_preimage1.
Qed.

Lemma additive_nnsfunT (g f : {nnsfun T >-> R}) x :
  \sum_(i \in [set: R]) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in [set: R]) (g @^-1` [set i])).
Proof.
rewrite -!(fsbig_widen [set of g] setT) ?additive_nnsfun//=.
- by move=> y [_ /preimage10]/=.
- by move=> y [_ /= /preimage10->]; rewrite setI0.
Qed.

End measure_fsbig.

Section sintegralD.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (D : set T).
Variables (mD : measurable D) (f g : {nnsfun T >-> R}).
Variable m : {measure set T -> \bar R}.

Lemma sintegralD :
  sintegral m (f \+ g)%R = sintegral m f + sintegral m g.
Proof.
rewrite !sintegralE; set F := f @` _; set G := g @` _; set FG := _ @` _.
pose pf x := f @^-1` [set x]; pose pg y := g @^-1` [set y]. 
transitivity (\sum_(z \in FG) z%:E * \sum_(a \in F) m (pf a `&` pg (z - a)%R)).
  apply: eq_fsbigr => z _; rewrite preimage_add -fsbig_setU// measure_fsbig//.
    by move=> x Fx; apply: measurableI.
  by move=> _ _ [i _ <-] [j _ <-] [k /= [[<- _] [<- _]]].
under eq_fsbigr do rewrite ge0_mule_fsumr//; rewrite exchange_fsum//.
transitivity (\sum_(x \in F) \sum_(y \in G) (x + y)%:E * m (pf x `&` pg y)).
  apply eq_fsbigr => _ /set_mem [i _ <-]; pose x := f i.
  rewrite /pf /pg (fsbig_widen G setT)//=; last first.
    by move=> y [_ /= /preimage10->]; rewrite setI0 measure0 mule0.
  rewrite (fsbig_widen FG setT)//=; last first.
    move=> z [_ /= FGz].
    rewrite measure_negligible ?mule0//; first exact: measurableI.
    exists set0; split=> //= {x}i /= [<-] /(canLR (@addrNK _ _)).
    by apply: contra_not FGz => <-; exists i; rewrite //= addrC.
  under [RHS]eq_fsbigr => y do rewrite -[y as y in [set y]](addrK x) (addrC y).
  by apply: reindex_fsbigT; exists (+%R (- x)); [apply: addKr| apply: addNKr].
transitivity (\sum_(x \in F) \sum_(y \in G) x%:E * m (pf x `&` pg y) +
              \sum_(x \in F) \sum_(y \in G) y%:E * m (pf x `&` pg y)).
  rewrite -fsum_split//; apply: eq_fsbigr => _ /set_mem [i _ <-].
  rewrite -fsum_split//; apply: eq_fsbigr => _ /set_mem [j _ <-].
  by rewrite EFinD ge0_muleDl// ?lee_fin.
congr (_ + _)%E; [|rewrite exchange_fsum//]; apply: eq_fsbigr => x _.
  by rewrite -ge0_mule_fsumr// additive_nnsfun nnsfun_cover setIT.
rewrite -ge0_mule_fsumr//; under eq_fsbigr do rewrite setIC.
by rewrite additive_nnsfun nnsfun_cover setIT.
Qed.

End sintegralD.

Section le_sintegral.
Variables (T : measurableType) (R : realType).
Variable m : {measure set T -> \bar R}.
Variables (f g : {nnsfun T >-> R}).
Hypothesis fg : forall x, f x <= g x.

Let fgnn : @IsNonNegFun T R (g \- f).
Proof. by split=> x; rewrite subr_ge0 fg. Qed.
#[local] HB.instance Definition _ := fgnn.

Lemma le_sintegral : (sintegral m f <= sintegral m g)%E.
Proof.
have gfgf : g =1 f \+ (g \- f) by move=> x /=; rewrite addrC subrK.
by rewrite (eq_sintegral m gfgf) sintegralD// lee_addl // sintegral_ge0.
Qed.

End le_sintegral.

Lemma is_cvg_sintegral (T : measurableType) (R : realType)
  (m : {measure set T -> \bar R})
  (f : {nnsfun T >-> R}^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) ->
  cvg (fun n => sintegral m (f n)).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
by apply: le_sintegral => // => x; apply/nd_f.
Qed.

Definition proj_nnsfun (T : measurableType) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Definition scale_nnsfun (T : measurableType) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (Nonneg.NngNum _ k0)) f.

Section sintegral_nondecreasing_limit_lemma.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat).
Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Variable f : {nnsfun T >-> R}.
Hypothesis gf : forall x, cvg (g^~ x) -> f x <= lim (g^~ x).

Let fleg c : (set T)^nat := fun n => [set x | c * f x <= g n x].

Let nd_fleg c : {homo fleg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; rewrite /fleg; apply/subsetPset => x /= cfg.
move: cfg => /le_trans; apply; exact: nd_g.
Qed.

Let mfleg c n : measurable (fleg c n).
Proof.
rewrite /fleg.
rewrite [X in _ X](_ : _ = \big[setU/set0]_(y \in [set: R])
    \big[setU/set0]_(x \in [set x | c * y <= x])
      (f @^-1` [set y] `&` (g n @^-1` [set x]))).
  apply: bigsetU_measurable => r _; apply: bigsetU_measurable => r' crr'.
  by apply: measurableI; apply/measurable_sfunP.
rewrite predeqE => t; split => [/= cfgn|].
- rewrite -bigcup_set; exists (f t).
    rewrite //=.
    (*first exact: mem_srng.*) admit.
  rewrite -bigcup_set_cond; exists (g n t) => //.
    apply/andP; split => //.
    (*; exact: mem_srng.*) admit.
  rewrite /preimage/=.
  admit.
Admitted.

Let g1 c n : {nnsfun T >-> R} := proj_nnsfun f (mfleg c n).

Let le_ffleg c : {homo (fun p x => g1 c p x): m n / (m <= n)%N >-> (m <= n)%O}.
Proof.
move=> m n mn; apply/asboolP => t.
rewrite /g1/= ler_pmul//.
rewrite 2!mindicE/= ler_nat; have [|//] := boolP (t \in fleg c m).
rewrite inE => cnt.
by have := nd_fleg c mn => /subsetPset/(_ _ cnt) cmt; rewrite mem_set.
Qed.

Let bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = setT.
Proof.
move=> c1; rewrite predeqE => x; split=> [[n _] []//|].
have := @fun_ge0 _ _ f x; rewrite le_eqVlt => /predU1P[|] gx0.
  exists O => //; rewrite /fleg /=.
  by rewrite -gx0 mulr0 fun_ge0.
have [cf|df] := pselect (cvg (g^~ x)).
  have cfg : lim (g^~ x) > c * f x.
    by rewrite (lt_le_trans _ (gf cf)) // gtr_pmull.
  suff [n cfgn] : exists n, g n x >= c * f x by exists n.
  move/(@lt_lim _ _ _ (nd_g x) cf) : cfg => [n _ nf].
  by exists n; apply: nf => /=.
have /cvgPpinfty/(_ (c * f x))[n _ ncfgn]:= nondecreasing_dvg_lt (nd_g x) df.
by exists n => //; rewrite /fleg /=; apply: ncfgn => /=.
Qed.

Local Open Scope ereal_scope.

(*Lemma sum_srng_g1_f c n :
  \sum_(x <- srng (g1 c n)) x%:E * mu (g1 c n @^-1` [set x] `&` D) =
  \sum_(x <- srng f) x%:E * mu (g1 c n @^-1` [set x] `&` D).
Proof.
rewrite srng_presfun_proj.
rewrite /sfun_proj_rng /=.
case: ifPn=> [/orP[|/eqP cnT]|_]. (* xxx *)
- rewrite mem_filter /= => /andP[].
  rewrite /preimage /= => /set0P[t [ft0 cnt]] f0.
  rewrite big_filter big_mkcond; apply: eq_bigr => r _.
  case: ifPn => // /negPn/eqP I0.
  rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0// predeqE => x.
  split => //=; move=> [/[swap] Dx].
  rewrite presfun_projE /=; have [xcn|xcn] := boolP (x \in _).
    rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
    by split => //; rewrite inE in xcn.
  rewrite mulr0 => r0.
  by move: I0; rewrite predeqE => /(_ t)[+ _]; apply; rewrite -r0.
- rewrite big_filter big_mkcond; apply: eq_bigr => r _.
  case: ifPn => // /negPn/eqP I0.
  rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
  split => //=; move=> [/[swap] Dx].
  rewrite /preimage /= presfun_projE /= cnT; have [xT|] := boolP (x \in _).
    rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
    by split => //; rewrite cnT.
  by rewrite notin_set => /(_ Logic.I).
- rewrite /= big_cons mul0e add0e.
  rewrite big_filter big_mkcond; apply: eq_bigr => r _.
  case: ifPn => // /negPn/eqP I0.
  have [->|r0] := eqVneq r 0%R; first by rewrite mul0e.
  rewrite [X in mu X](_ : _ = set0) ?measure0 ?mule0 // predeqE => x.
  split => //=; move=> [/[swap] Dx].
  rewrite /preimage /= presfun_projE; have [xT|_ ] := boolP (x \in _).
    rewrite mulr1 => gxr; move: I0; rewrite predeqE => /(_ x)[+ _]; apply.
    by split => //; rewrite inE in xT.
  by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
Qed.*)

(* lemma 1.6 *)
Lemma nd_sintegral_lim_lemma : sintegral mu f <= lim (sintegral mu \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu f <= lim (sintegral mu \o g).
  by apply/lee_mul01Pr => //; apply: sintegral_ge0.
move=> c /andP[c0 c1].
have cg1g n : c%:E * sintegral mu (g1 c n) <= sintegral mu (g n).
  rewrite -(sintegralrM mu c (g1 c n)).
  rewrite (_ : (_ \* _)%R = scale_nnsfun (g1 c n) (ltW c0)) //.
  apply: le_sintegral => //.
  have : forall m x, (c * g1 c m x <= g m x)%R.
    move=> m x; rewrite /g1.
    rewrite /proj_nnsfun/= mindicE.
    have [|] := boolP (x \in _).
      by rewrite inE => -[/=]; rewrite mulr1.
    by rewrite 2!mulr0 fun_ge0.
  by move=> h t; have := h n t.
suff {cg1g}<- : lim (fun n => sintegral mu (g1 c n)) = sintegral mu f.
  have is_cvg_g1 : cvg (fun n => sintegral mu (g1 c n)).
    apply: is_cvg_sintegral => //= x m n mn.
    by have /lefP/(_ x) := le_ffleg c mn.
  rewrite -ereal_limrM // lee_lim//.
  - exact: ereal_is_cvgrM.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu (g1 c n)) --> sintegral mu f by apply/cvg_lim.
(*rewrite [X in X --> _](_ : _ = fun n => \sum_(k < ssize f) ((srng f)`_k)%:E *
    mu (f @^-1` [set (srng f)`_k] `&` fleg c n `&`)); last first.
  rewrite funeqE => n; rewrite sintegralE sum_srng_g1_f.
  rewrite big_tnth; apply: eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0%R) //=.
  have [fi0|fi0] := eqVneq ((srng f)`_i) 0%R; first by rewrite fi0 // 2!mul0e.
  congr (_ * mu _); rewrite predeqE => x; split => [|[]] /=.
  - rewrite /preimage /= presfun_projE => -[/[swap]x].
    have [xcn|_] := boolP (_ \in fleg _ _).
      by rewrite mulr1 => <-; split => //; split=> //; rewrite inE in xcn.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE fi0).
  - rewrite /sfun_proj_f /preimage /= => -[fxi] cnxx.
    by rewrite presfun_projE; split => //; rewrite fxi mem_set// mulr1.
rewrite [X in X --> _](_ : _ = fun n => \sum_(x <- srng f) x%:E *
    mu (f @^-1` [set x] `&` fleg c n `&`)); last first.
  rewrite funeqE => n; rewrite [in RHS]big_tnth /=; apply/eq_bigr => i _.
  rewrite [in LHS](set_nth_default 0%R) //=; congr (_%:E * mu (_ `&` _ `&` _)).
    exact: set_nth_default.
  rewrite predeqE => t /=; rewrite /preimage /= -propeqE.
  by congr (_ = _); exact: set_nth_default.
rewrite sintegralE big_seq.
under [in X in X --> _]eq_fun do rewrite big_seq.
have measurable_ffleg k i : measurable (f @^-1` [set k] `&` fleg c i `&`).
  by apply: measurableI => //; apply: measurableI;
    [exact: sfun_measurable_preimage_set1|exact: mfleg].
apply: ereal_lim_sum => [r n /NNSFuncdom_ge0 r0|r rf].
  by rewrite mule_ge0// measure_ge0.
apply: ereal_cvgrM => //.
rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n `&`))); last first.
  by rewrite -setI_bigcupl -setI_bigcupr bigcup_fleg// -setIA setIid.
apply: cvg_mu_inc => //; first exact: measurable_bigcup.
move=> n m nm; apply/subsetPset; apply: setSI; apply: setIS.
by move/(nd_fleg c) : nm => /subsetPset.
Unshelve. all: by end_near. Qed.*)
Admitted.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat).
Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Variable f : {nnsfun T >-> R}.
Hypothesis gf : forall x, g ^~ x --> f x.

Let limg : forall x, lim (g^~x) = f x.
Proof. by move=> x; apply/cvg_lim; [exact: Rhausdorff| exact: gf]. Qed.

Lemma nd_sintegral_lim : sintegral mu f = lim (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x; rewrite -limg.
have : nondecreasing_seq (sintegral mu \o g).
  by move=> m n mn; apply: le_sintegral => // x; exact/nd_g.
move=> /ereal_nondecreasing_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=.
apply: le_sintegral => // x.
rewrite -limg // (nondecreasing_cvg_le (nd_g x)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Definition mrestrict (T : measurableType) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :
  f\|_A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

Section integral.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.
Implicit Types (f g : T -> \bar R).

Definition nnintegral f := ereal_sup [set sintegral mu h |
  h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= f x]].

Lemma nnintegral_nnsfun (h : {nnsfun T >-> R}) :
  nnintegral (EFin \o h) = sintegral mu h.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gh <-]; rewrite le_sintegral.
by apply: ereal_sup_ub => /=; exists h.
Qed.

Lemma nnintegral_ge0 f : (forall x, 0 <= f x) -> 0 <= nnintegral f.
Proof.
by move=> f0; apply: ereal_sup_ub; exists nnsfun0; last by rewrite sintegral0.
Qed.

Lemma eq_nnintegral g f : f =1 g -> nnintegral f = nnintegral g.
Proof. by move=> /funext->. Qed.

Lemma nnintegral0 : nnintegral (cst 0) = 0.
Proof.
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub; exists nnsfun0; last by rewrite sintegral0.
  by [].
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, f x = 0%R.
  by move=> y; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin//.
by rewrite (@eq_sintegral _ _ mu f (@nnsfun0 T R)) ?sintegral0//=.
Qed.

Variables (D : set T) (mD : measurable D).

Definition integral f (g := f \|_ D) := nnintegral (g ^\+) - nnintegral (g ^\-).

Local Notation "\int_ f 'd x" := (integral (fun x => f))
  (at level 10, f at next level, format "'\int_'  f  ''d'  x").

Lemma eq_integral f g : {in D, f =1 g} -> \int_ (f x) 'd x = \int_ (g x) 'd x.
Proof. by rewrite /integral => /eq_restrictP->. Qed.

Lemma ge0_integralE f : (forall x, D x -> 0 <= f x) ->
  integral f = nnintegral (f \|_ D).
Proof.
move=> f0; rewrite /integral funennp_restrict funenng_restrict.
  have /eq_restrictP-> := ge0_funenngE f0.
have /eq_restrictP-> := ge0_funennpE f0.
by rewrite erestrict0 nnintegral0 sube0.
Qed.

(* Local Lemma ge0_integralE f : (forall x, D x -> 0 <= f x) -> *)
(*   \int_ (f x) 'd x = nnintegral (f \|_ D). *)
(* Proof. *)
(* (* move=> f0; rewrite /integral (@eq_nnintegral _ _ (ge0_funenngE f0)). *) *)
(* (* by rewrite (@eq_nnintegral _ _ (ge0_funennpE f0)) nnintegral0 sube0. *) *)
(* (* Qed. *) *)
(* Admitted. *)

Lemma integralE f :
  \int_ (f x) 'd x = \int_ (f ^\+ x) 'd x - \int_ (f ^\- x) 'd x.
Proof.
rewrite [in LHS]/integral funenng_restrict funennp_restrict.
by rewrite -ge0_integralE // -ge0_integralE.
Qed.

Lemma integral0 : \int_ (cst 0 x) 'd x = 0.
Proof. by rewrite ge0_integralE// erestrict0 nnintegral0. Qed.

Lemma integral_ge0 f : (forall x, D x -> 0 <= f x) -> 0 <= \int_ (f x) 'd x.
Proof.
move=> f0; rewrite ge0_integralE// nnintegral_ge0// => x.
by rewrite /patch; case: ifP; rewrite // inE => /f0->.
Qed.

Lemma integral_nnsfun (h : {nnsfun T >-> R}) :
  \int_ ((EFin \o h) x) 'd x = sintegral mu (h \|_ D).
Proof.
rewrite mrestrict -nnintegral_nnsfun// -mrestrict ge0_integralE ?comp_patch//.
by move=> x Dx /=; rewrite lee_fin; exact: fun_ge0.
Qed.

End integral.
Notation "\int_ D f 'd mu [ x ]" := (integral mu D (fun x => f)) : ereal_scope.
Notation "\int F 'd mu [ x ]" := (\int_ setT F 'd mu[x])%E : ereal_scope.

Section domain_change.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).

Lemma integral_mkcond D f : \int_D f x 'd mu[x] = \int (f \|_ D) x 'd mu [x].
Proof. by rewrite /integral patch_setT. Qed.

Lemma integralT_nnsfun (h : {nnsfun T >-> R}) :
  \int ((EFin \o h) x) 'd mu[x] = sintegral mu h.
Proof. by rewrite integral_nnsfun// patch_setT. Qed.

Lemma integral_mkcondr D P f :
  \int_(D `&` P) f x 'd mu[x] = \int_D (f \|_ P) x 'd mu [x].
Proof. by rewrite integral_mkcond [RHS]integral_mkcond patch_setI. Qed.

Lemma integral_mkcondl D P f :
  \int_(P `&` D) f x 'd mu[x] = \int_D (f \|_ P) x 'd mu [x].
Proof. by rewrite setIC integral_mkcondr. Qed.

Lemma ge0_integralTE f : (forall x, 0 <= f x) ->
  \int f x 'd mu [x] = nnintegral mu f.
Proof. by move=> f0; rewrite ge0_integralE// patch_setT. Qed.

End domain_change.

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (f : T -> \bar R).
Hypothesis f0 : forall x, 0 <= f x.
Hypothesis mf : measurable_fun setT f.
Variable g : {nnsfun T >-> R}^nat.
Hypothesis nd_g : forall x, nondecreasing_seq (g^~x).
Hypothesis gf : forall x, EFin \o g^~x --> f x.
Local Open Scope ereal_scope.

Lemma nd_ge0_integral_lim : \int f x 'd mu [ x] = lim (sintegral mu \o g).
Proof.
rewrite ge0_integralTE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x.
  have <- : lim (EFin \o g^~ x) = f x by apply/cvg_lim => //; apply: gf.
  have : (EFin \o g^~ x) --> ereal_sup [set of EFin \o g^~ x].
    apply: ereal_nondecreasing_cvg => p q pq /=; rewrite lee_fin.
    exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ub; exists n.
have := lee_pinfty (nnintegral mu f).
rewrite le_eqVlt => /predU1P[mufoo|mufoo]; last first.
  have /ub_ereal_sup_adherent h : nnintegral mu f \is a fin_num.
    by rewrite ge0_fin_numE // (nnintegral_ge0 mu f0).
  apply: lee_adde => e; have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite EFinN lte_subl_addr// => fGe.
  have : forall x, cvg (g^~ x) -> (G x <= lim (g^~ x))%R.
    move=> x cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _))// gxfx.
  move/(@nd_sintegral_lim_lemma _ _ mu _ nd_g).
  by move/(lee_add2r e%:num%:E)/(le_trans (ltW fGe)).
suff : lim (sintegral mu \o g) = +oo by move=> ->; rewrite mufoo.
apply/eq_pinfty => r r0.
have [G [Gf rG]] : exists h : {nnsfun T >-> R}, (forall x, (h x)%:E <= f x) /\
                                     (r%:E <= sintegral mu h).
  move: (mufoo) => /eq_pinfty.
  have r20 : (0 < r + r)%R by rewrite addr_gt0.
  move/(_ _ r20) => r2.
  have {} : r%:E < ereal_sup [set sintegral mu g0 | g0 in
       [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= f x)]].
    by rewrite (lt_le_trans _ r2) // lte_fin ltr_addr.
  move/ereal_sup_gt => [x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, cvg (g^~ x) -> (G x <= lim (g^~ x))%R.
  move=> x cg; rewrite -lee_fin -(EFin_lim cg).
  by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _)) // gxfx.
move/(@nd_sintegral_lim_lemma _ _ mu _ nd_g) => Gg.
by rewrite (le_trans rG).
Unshelve. all: by end_near. Qed.

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
  rewrite inE /=; exists (fine (f x)).
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
Variables (T : measurableType) (R : realType).
Variables (f : T -> \bar R).
Variables (D : set T) (mD : measurable D).
Hypothesis mf : measurable_fun D f.

Local Notation I := (@dyadic_itv R).

Let A n k := (if (k < n * 2 ^ n)%N then
  D `&` [set x | f x \in EFin @` [set` I n k]] else set0).

Let B n := D `&` [set x | n%:R%:E <= f x ]%E.

Definition approx : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * (x \in A n k)%:R +
  n%:R * (x \in B n)%:R.

(* technical properties of the sets A and B *)
Local Lemma mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]//; rewrite -preimage_comp.
by apply/mf => //; exact/measurable_EFin/measurable_itv.
Qed.

Local Lemma trivIsetA n : trivIset setT (A n).
Proof.
rewrite /A.
(*under [in X in trivIset _ X]eq_fun do rewrite setIC.*)
apply/ (*trivIset_setI/*) trivIsetP => i j _ _.
wlog : i j / (i < j)%N.
  move=> h; rewrite neq_lt => /orP[ij|ji].
    by apply: h => //; rewrite lt_eqF.
  by rewrite setIC; apply: h => //; rewrite lt_eqF.
move=> ij _.
rewrite /A; case: ifPn => /= ni; last by rewrite set0I.
case: ifPn => /= nj; last by rewrite setI0.
rewrite predeqE => t; split => // -[/=] [_].
rewrite inE => -[r /=]; rewrite in_itv /= => /andP[r1 r2] rft [_].
rewrite inE => -[s /=]; rewrite in_itv /= => /andP[s1 s2].
rewrite -rft => -[sr]; rewrite {}sr {s} in s1 s2.
have := le_lt_trans s1 r2.
by rewrite ltr_pmul2r ?invr_gt0 ?exprn_gt0// ltr_nat ltnS leqNgt ij.
Qed.

Local Lemma f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  x \in A n i = false.
Proof.
move=> fx0 i0; apply/negbTE; rewrite notin_set /A ltn_ord /= => -[_].
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[r1 r2].
rewrite fx0 => -[r0]; move: r1 r2; rewrite {}r0 {r} => + r2.
rewrite ler_pdivr_mulr; last by rewrite -natrX ltr0n expn_gt0.
by rewrite mul0r lern0; exact/negP.
Qed.

Local Lemma fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  x \in A n i = false.
Proof.
move=> fxn; apply/negbTE; rewrite /A ltn_ord.
rewrite notin_set => /= -[_]; apply/negP.
rewrite notin_set /= => -[r /=].
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
by rewrite 2!inE in xAn1k, xAi; move/(_ (conj xAi xAn1k)).
Qed.
Arguments disj_A0 {x n i} k.

Local Lemma mB n : measurable (B n).
Proof. exact: emeasurable_fun_c_infty. Qed.

Local Lemma foo_B1 x n : D x -> f x = +oo%E -> x \in B n.
Proof.
by move=> Dx fxoo; rewrite /B inE /=; split => //=; rewrite /= fxoo lee_pinfty.
Qed.

Local Lemma f0_B0 x n : f x = 0%:E -> n != 0%N -> (x \in B n) = false.
Proof.
move=> fx0 n0; apply/negP; rewrite inE /B /= => -[Dx] /=; apply/negP.
by rewrite -ltNge fx0 lte_fin ltr0n lt0n.
Qed.

Local Lemma fgtn_B0 x n : (f x < n%:R%:E)%E -> (x \in B n) = false.
Proof.
move=> fxn; apply/negbTE/negP; rewrite inE /= => -[Dx] /=.
by apply/negP; rewrite -ltNge.
Qed.

Local Lemma f0_approx0 n x : f x = 0%E -> approx n x = 0.
Proof.
move=> fx0; rewrite /approx; have [->|n0] := eqVneq n O.
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0 // mulr0 addr0 big1 // => /= i _.
have [->|i0] := eqVneq (nat_of_ord i) 0%N; first by rewrite mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Local Lemma fpos_approx_neq0 x : D x -> (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx n x != 0.
Proof.
move=> Dx /andP[fx_gt0 fxoo].
have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxoo fx_gt0; case: (f x).
rewrite -(fineK fxfin) lte_fin in fx_gt0.
near=> n.
rewrite /approx; apply/negP; rewrite paddr_eq0; last 2 first.
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
rewrite notin_set /B /setI /= => /not_andP[] // /negP.
rewrite -ltNge => fxn _.
have K : (`|floor (fine (f x) * 2 ^+ n)| < n * 2 ^ n)%N.
  rewrite -ltz_nat gez0_abs; last first.
    by rewrite floor_ge0 mulr_ge0 // -?natrX// ?ler0n// ltW.
  rewrite -(@ltr_int R); rewrite (le_lt_trans (floor_le _)) // PoszM intrM.
  by rewrite -natrX ltr_pmul2r ?ltr0n ?expn_gt0// -lte_fin (fineK fxfin).
have xAnK : x \in A n (Ordinal K).
  rewrite inE /A /= K; split => //=.
  rewrite inE /=; exists (fine (f x)); last by rewrite fineK.
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
Unshelve. all: by end_near. Qed.

Local Lemma f_ub_approx n x : (f x < n%:R%:E)%E ->
  approx n x == 0 \/ exists k,
    [/\ (0 < k < n * 2 ^ n)%N,
       x \in A n k, approx n x = k%:R / 2 ^+ n &
       f x \in EFin @` [set` I n k]].
Proof.
move=> fxn; rewrite /approx fgtn_B0 // mulr0 addr0.
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

Local Lemma notinD_A0 x n k : ~ D x -> (x \in A n k) = false.
Proof.
move=> Dx; apply/negP.
rewrite /A; case: ifPn => [kn2n|_].
  by rewrite inE => -[].
by rewrite inE => -[].
Qed.

Local Lemma notinD_B0 x n : ~ D x -> (x \in B n) = false.
Proof. by move=> Dx; apply/negP; rewrite inE => -[]. Qed.

Lemma nd_approx : nondecreasing_seq approx.
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x.
have [Dx|Dx] := pselect (D x); last first.
  rewrite /approx big1; last by move=> i _; rewrite notinD_A0 // mulr0.
  rewrite notinD_B0// ?mulr0 addr0.
  rewrite big1; last by move=> i _; rewrite notinD_A0 // mulr0.
  by rewrite notinD_B0// ?mulr0 addr0.
have [fxn|fxn] := ltP (f x) n%:R%:E.
  rewrite {2}/approx fgtn_B0 ?mulr0 ?addr0; last first.
    by rewrite (lt_trans fxn) // lte_fin ltr_nat.
  have [/eqP ->|[k [/andP[k0 kn] xAnk -> _]]] := f_ub_approx fxn.
    by apply: sumr_ge0 => i _; rewrite mulr_ge0// ?divr_ge0// ?ler0n// exprn_ge0.
  move: (xAnk); rewrite inE {1}/A kn => -[_] /=.
  rewrite inE => -[r] /dyadic_itv_subU[|] rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite inE /A k2n; split => //=; rewrite inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0//.
    rewrite exprS invrM ?unitfE// ?expf_neq0// -muln2 natrM -mulrA (mulrCA 2).
    by rewrite divrr ?mulr1 ?unitfE.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite /A /= k2n inE; split => //=; rewrite inE/=; exists r.
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
    rewrite /approx xBn mulr1 big1 ?add0r; last first.
      by move=> /= i _; rewrite fgen_A0 ?mulr0//; case/andP : fxn.
    rewrite fgtn_B0 ?mulr0 ?addr0; last by case/andP : fxn.
    have kn2 : (k < n.+1 * 2 ^ n.+1)%N by case/andP : k1 => _; rewrite mulnC.
    rewrite (bigD1 (Ordinal kn2)) //=.
    have xAn1k : x \in A n.+1 k by rewrite inE /A kn2.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i /= ikn2; rewrite (disj_A0 (Ordinal kn2)) // mulr0.
    rewrite -natrX ler_pdivl_mulr ?ltr0n // ?expn_gt0// mulrC -natrM ler_nat.
    by case/andP : k1.
- have xBn : x \in B n.
    rewrite /B /= inE /=; split => //.
    by rewrite /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx xBn mulr1.
  have xBn1 : x \in B n.+1.
    by rewrite /B /= inE.
  rewrite xBn1 mulr1 big1 ?add0r.
    by rewrite big1 ?add0r ?ler_nat // => /= i _; rewrite fgen_A0 // mulr0.
  by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn)// lee_fin ler_nat.
Qed.

Lemma cvg_approx x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  (f x < +oo)%E -> (approx^~ x) --> fine (f x).
Proof.
move=> Dx fxoo; have fxfin : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
apply/(@cvg_distP _ [normedModType R of R^o]) => _/posnumP[e].
rewrite near_map.
have [fx0|fx0] := eqVneq (f x) 0%E.
  by near=> n; rewrite f0_approx0 // fx0 /= subrr normr0.
have /(fpos_approx_neq0 Dx) [m   _ Hm] : (0 < f x < +oo)%E.
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
have [approx_nx0|] := f_ub_approx fxn.
  by have := Hm _ mn; rewrite approx_nx0.
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
Unshelve. all: by end_near. Qed.

Lemma le_approx k x (f0 : forall x, (0 <= f x)%E) : D x ->
  ((approx k x)%:E <= f x)%E.
Proof.
move=> Dx; have [fixoo|] := ltP (f x) (+oo%E); last first.
  by rewrite lee_pinfty_eq => /eqP ->; rewrite lee_pinfty.
have nd_ag : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; exact/lefP/nd_approx.
have fi0 : forall x, D x -> (0 <= f x)%E by move=> *; exact: f0.
have cvg_af := cvg_approx fi0 Dx fixoo.
have is_cvg_af : cvg (approx ^~ x).
  by apply/cvg_ex; eexists; exact: cvg_af.
have {is_cvg_af} := nondecreasing_cvg_le nd_ag is_cvg_af k.
rewrite -lee_fin => /le_trans; apply.
rewrite -(@fineK _ (f x)); last first.
  by rewrite fin_numElt fixoo andbT (lt_le_trans _ (f0 _)) ?lte_ninfty.
by move/(cvg_lim (@Rhausdorff R)) : cvg_af => ->.
Qed.

Lemma dvg_approx x : D x -> f x = +oo%E -> ~ cvg (approx^~ x : _ -> R^o).
Proof.
move=> Dx fxoo; have approx_x n : approx n x = n%:R.
  rewrite /approx foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo lee_pinfty.
case/cvg_ex => /= l.
have [l0|l0] := leP 0%R l.
- move=> /cvg_distP/(_ _ ltr01); rewrite near_map => -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ger0_norm // (le_trans (ceil_ge _)) //.
  by rewrite -(@gez0_abs (ceil _)) // ceil_ge0.
- move/cvg_distP => /(_ _ ltr01); rewrite near_map => -[n _].
  move=> /(_ (`|floor l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [X in _ <= X]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n//.
  rewrite ler0_norm //; last by rewrite ltW.
  rewrite (@le_trans _ _ (- floor l)%:~R) //.
    by rewrite mulrNz ler_oppl opprK floor_le.
  by rewrite -(@lez0_abs (floor _)) // floor_le0 // ltW.
Qed.

Lemma ecvg_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o approx^~x --> f x.
Proof.
move=> Dx; have := lee_pinfty (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx := dvg_approx Dx fxoo.
  have : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx mn => /lefP; exact.
  move/nondecreasing_dvg_lt => /(_ dvg_approx).
  by rewrite fxoo; exact/dvg_ereal_cvg.
rewrite -(@fineK _ (f x)); first exact: (cvg_comp (cvg_approx f0 Dx fxoo)).
by rewrite fin_numElt fxoo andbT (lt_le_trans _ (f0 _ _)) // lte_ninfty.
Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition nnsfun_approx : {nnsfun T >-> R}^nat := fun n => locked (add_nnsfun
  (sum_nnsfun
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => (*nnsfun_ind pt (Nonneg.NngNum _ (k2n_ge0 (Ordinal h))) (mA n k)*)
          scale_nnsfun (indic_nnsfun _ (mA n k)) (k2n_ge0 (Ordinal h))
      | right _ => nnsfun0
     end) (n * 2 ^ n)%N)
  (*(nnsfun_ind pt (Nonneg.NngNum _ (ler0n _ n)) (mB n))*)
  (scale_nnsfun (indic_nnsfun _ (mB n)) (ler0n _ n))).

Lemma nnsfun_approxE n : nnsfun_approx n = approx n :> (T -> R).
Proof.
rewrite funeqE => t /=.
rewrite /nnsfun_approx; unlock.
rewrite /=.
rewrite sum_nnsfunE; congr (_ + _).
by apply: eq_bigr => i _; case: Bool.bool_dec => [h|/negP];
  [|rewrite ltn_ord].
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o nnsfun_approx^~x --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof.
by move=> m n mn; rewrite (nnsfun_approxE n) (nnsfun_approxE m); exact: nd_approx.
Qed.

Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : {nnsfun T >-> R}^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~x --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|].
move=> x Dx.
by apply: cvg_nnsfun_approx.
Qed.

End approximation.

Section semi_linearity0.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.

Lemma ge0_integralM_EFin k : (0 <= k)%R ->
  \int_ D (k%:E * f1 x) 'd mu[x] = k%:E * \int_ D (f1 x) 'd mu[x].
Proof.
rewrite integral_mkcond erestrict_scale [in RHS]integral_mkcond.
move=> k0; set h1 := f1 \|_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply: measurable_restrict.
have [g [nd_g gh1]] := approximation measurableT mh1 (fun x _ => h10 x).
pose kg := fun n => scale_nnsfun (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ mu (fun x => k%:E * h1 x) _ kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu (scale_nnsfun (g n) k0))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (g n))).
    rewrite ereal_limrM //; last first.
      by apply: is_cvg_sintegral => // x m n mn; apply/(lef_at x nd_g).
    rewrite -(nd_ge0_integral_lim mu h10) // => x.
      exact/(lef_at x nd_g).
    by apply: gh1.
  by under eq_fun do rewrite (sintegralrM mu k (g _)).
- by move=> t; rewrite mule_ge0// h10.
- by move=> x m n mn; rewrite /kg ler_pmul//; exact/lefP/nd_g.
- move=> x.
  rewrite [X in X --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
  by apply: ereal_cvgrM => //; exact: gh1.
Qed.

End semi_linearity0.

Lemma nondecreasing_seqD' (T : Type) (R : numDomainType) (f g : (T -> R)^nat) :
  (forall x, nondecreasing_seq (f^~x)) ->
  (forall x, nondecreasing_seq (g^~x)) ->
  (forall x, nondecreasing_seq ((f \+ g)^~x)).
Proof. by move=> ndf ndg t m n mn; apply: ler_add; [exact/ndf|exact/ndg]. Qed.

Section semi_linearity.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ge0_integralD : \int_ D ((f1 \+ f2) x) 'd mu[x] =
  \int_ D (f1 x) 'd mu[x] + \int_ D (f2 x) 'd mu[x].
Proof.
rewrite !(integral_mkcond _ D) erestrictD.
set h1 := f1 \|_ D; set h2 := f2 \|_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply: measurable_restrict.
have mh2 : measurable_fun setT h2 by apply: measurable_restrict.
have [g1 [nd_g1 gh1]] := approximation measurableT mh1 (fun x _ => h10 x).
have [g2 [nd_g2 gh2]] := approximation measurableT mh2 (fun x _ => h20 x).
pose g12 := fun n => add_nnsfun (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ mu _ _ g12) //; last 3 first.
  - by move=> x; rewrite adde_ge0.
  - apply: nondecreasing_seqD' => // x;
      [exact/(lef_at x nd_g1)|exact/(lef_at x nd_g2)].
  - move=> x Dx.
    rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E)) ?funeqE//.
    apply: ereal_cvgD => //; [|exact: gh1|exact: gh2].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: h10|exact: h20].
rewrite (_ : _ \o _ =
    fun n => sintegral mu (g1 n) + sintegral mu (g2 n)); last first.
  by rewrite funeqE => n /=; rewrite sintegralD.
rewrite (nd_ge0_integral_lim _ _ (fun x => lef_at x nd_g1)) //; last first.
  by move=> x; exact: gh1.
rewrite (nd_ge0_integral_lim _ _ (fun x => lef_at x nd_g2)) //; last first.
  by move=> x; exact: gh2.
rewrite ereal_limD //.
  by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g1).
  by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g2).
rewrite ge0_adde_def => //; rewrite inE; apply: ereal_lim_ge.
- by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g1).
- by apply: nearW => n; exact: sintegral_ge0.
- by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g2).
- by apply: nearW => n; exact: sintegral_ge0.
Qed.

Lemma ge0_le_integral : (forall x, D x -> f1 x <= f2 x) ->
  \int_ D (f1 x) 'd mu[x] <= \int_ D (f2 x) 'd mu[x].
Proof.
move=> f12; rewrite !(integral_mkcond _ D).
set h1 := f1 \|_ D; set h2 := f2 \|_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply: measurable_restrict.
have mh2 : measurable_fun setT h2 by apply: measurable_restrict.
have h12 x : h1 x <= h2 x by apply: lee_restrict.
have [g1 [nd_g1 gh1]] := approximation measurableT mh1 (fun x _ => h10 _).
rewrite (nd_ge0_integral_lim _ h10 (fun x => lef_at x nd_g1) (fun x => gh1 x Logic.I))//.
apply: ereal_lim_le.
  by apply: is_cvg_sintegral => // t Dt; exact/(lef_at t nd_g1).
near=> n; rewrite ge0_integralTE//; apply: ereal_sup_ub => /=.
exists (g1 n) => // t; rewrite (le_trans _ (h12 _)) //.
have := gh1 t Logic.I.
have := lee_pinfty (h1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite lee_pinfty.
have h1tfin : h1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (h10 t))// lte_ninfty.
have := gh1 t Logic.I(*TODO: come back to this*).
rewrite -(fineK h1tfin) => /ereal_cvg_real[ft_near].
set u_ := (X in X --> _) => u_h1 g1h1.
have <- : lim u_ = fine (h1 t) by apply/cvg_lim => //; exact: Rhausdorff.
rewrite lee_fin; apply: nondecreasing_cvg_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_g1.
by apply/cvg_ex; eexists; exact: u_h1.
Unshelve. all: by end_near. Qed.

End semi_linearity.

Lemma emeasurable_funN (T : measurableType) (R : realType) D (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D (fun x => - f x)%E.
Proof.
move=> mD mf.
apply: measurable_fun_comp => //.
exact: emeasurable_fun_minus.
Qed.

Section approximation_sfun.
Variables (T : measurableType) (R : realType).
Variables (f : T -> \bar R).
Variables (D : set T) (mD : measurable D) (mf : measurable_fun D f).

Lemma approximation_sfun :
  exists g : {sfun T >-> R}^nat, (forall x, D x -> EFin \o g^~x --> f x).
Proof.
have fp0 : (forall x, 0 <= f^\+ x)%E by [].
have mfp : measurable_fun D f^\+%E.
  by apply: emeasurable_fun_max => //; exact: measurable_fun_cst.
have fn0 : (forall x, 0 <= f^\- x)%E by [].
have mfn : measurable_fun D f^\-%E.
  by apply: emeasurable_fun_max => //;
    [exact: emeasurable_funN | exact: measurable_fun_cst].
have [fp_ [fp_nd fp_cvg]] := approximation mD mfp (fun x _ => fp0 x).
have [fn_ [fn_nd fn_cvg]] := approximation mD mfn (fun x _ => fn0 x).
exists (fun n => [the {sfun T >-> R} of fp_ n \+ cst (-1) \* fn_ n]) => x /=.
rewrite [X in X --> _](_ : _ =
    EFin \o fp_^~ x \+ (-%E \o EFin \o fn_^~ x))%E; last first.
  by apply/funext => n/=; rewrite EFinD mulN1r.
by move=> Dx; rewrite (funenngnnp f); apply: ereal_cvgD;
  [exact: add_def_funennpg|apply: fp_cvg|apply:ereal_cvgN; apply: fn_cvg].
Qed.

End approximation_sfun.

Section emeasurable_fun.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma emeasurable_funD D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \+ g).
Proof.
move=> mf mg mD.
have noom : measurable ([set -oo] : set (\bar R)) by apply: emeasurable_set1.
have poom : measurable ([set +oo] : set (\bar R)) by apply: emeasurable_set1.
have Cnoom : measurable (~` [set -oo] : set (\bar R)) by apply: measurableC.
have Cpoom : measurable (~` [set +oo] : set (\bar R)) by apply: measurableC.
have mfg :  measurable (D `&` [set x | f x +? g x]).
  suff -> : [set x | f x +? g x] =
              (f @^-1` (~` [set +oo]) `|` g @^-1` (~` [set -oo])) `&`
              (f @^-1` (~` [set -oo]) `|` g @^-1` (~` [set +oo])).
     by rewrite setIIr; apply: measurableI;
        rewrite setIUr; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /adde_def !(negb_and, negb_or).
   by rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
wlog fg : D mD mf mg mfg / forall x, D x -> f x +? g x => [hwlogD|]; last first.
   have [f_ f_cvg] := approximation_sfun mD mf.
   have [g_ g_cvg] := approximation_sfun mD mg.
   apply: (@emeasurable_fun_cvg _ _ _ (fun n x => (f_ n x + g_ n x)%:E)) => //.
    move=> n; apply/EFin_measurable_fun.
    by apply: (@measurable_funS _ _ setT) => //; exact: measurable_funD.
  move=> x Dx; under eq_fun do rewrite EFinD.
  by apply: ereal_cvgD; [exact: fg|exact: f_cvg|exact: g_cvg].
move=> A mA; wlog NAnoo: A mD mf mg mA / ~ (A -oo) => [hwlogA|].
  have [] := pselect (A -oo); last exact: hwlogA.
  move=> /(@setD1K _ -oo)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last first.
    by apply: hwlogA=> //; [exact: measurableD|case => /=].
  have -> : (f \+ g) @^-1` [set -oo] = f @^-1` [set -oo] `|` g @^-1` [set -oo].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
     - by rewrite adde_eq_ninfty => /orP[] /eqP->; [left|right].
     - by move->.
     - by move->; rewrite addeC.
   by rewrite setIUr; apply: measurableU; [apply: mf|apply: mg].
have-> : D `&` (f \+ g) @^-1` A =
       (D `&` [set x | f x +? g x]) `&` (f \+ g) @^-1` A.
  rewrite -setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //.
  by case: (f x) (g x) Afgx => [rf||] [rg||].
have Dfg : D `&` [set x | f x +? g x] `<=` D by apply: subIset; left.
apply: hwlogD => //.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite -setIA setIid.
- by move=> ? [].
Qed.

Lemma emeasurable_funB D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \- g).
Proof.
by move=> mf mg mD; apply: emeasurable_funD => //; exact: emeasurable_funN.
Qed.

Lemma emeasurable_funM D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \* g).
Proof.
move=> mf mg mD.
have m0 : measurable ([set 0] : set (\bar R)) by apply: emeasurable_set1.
have mC0 : measurable ([set~ 0] : set (\bar R)) by apply: measurableC.
have mCoo : measurable (~` [set -oo; +oo] : set (\bar R)).
  by apply/measurableC/measurableU; exact/emeasurable_set1.
have mfg : measurable (D `&` [set x | f x *? g x]).
  suff -> : [set x | f x *? g x] =
              (f @^-1` (~` [set 0]) `|` g @^-1` (~` [set -oo; +oo])) `&`
              (g @^-1` (~` [set 0]) `|` f @^-1` (~` [set -oo; +oo])).
     by rewrite setIIr; apply: measurableI;
        rewrite setIUr; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /mule_def !(negb_and, negb_or).
   rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP).
   rewrite !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
   rewrite eqe_absl lee_pinfty andbT (orbC (g x == +oo)).
   by rewrite eqe_absl lee_pinfty andbT (orbC (f x == +oo)).
wlog fg : D mD mf mg mfg / forall x, D x -> f x *? g x => [hwlogM|]; last first.
  have [f_ f_cvg] := approximation_sfun mD mf.
  have [g_ g_cvg] := approximation_sfun mD mg.
  apply: (@emeasurable_fun_cvg _ _ _ (fun n x => (f_ n x * g_ n x)%:E)) => //.
    move=> n; apply/EFin_measurable_fun.
    by apply: measurable_funM => //; exact: (@measurable_funS _ _ setT).
  move=> x Dx; under eq_fun do rewrite EFinM.
  by apply: ereal_cvgM; [exact: fg|exact: f_cvg|exact: g_cvg].
move=> A mA; wlog NA0: A mD mf mg mA / ~ (A 0) => [hwlogA|].
  have [] := pselect (A 0); last exact: hwlogA.
  move=> /(@setD1K _ 0)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last first.
    apply: hwlogA=> //; last by case => /=.
    exact: measurableD.
  have -> : (fun x => f x * g x) @^-1` [set 0] = f @^-1` [set 0] `|` g @^-1` [set 0].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
       by rewrite mule_eq0 => /orP[] /eqP->; [left|right].
     by move=> ->; rewrite mul0e.
     by move=> ->; rewrite mule0.
   by rewrite setIUr; apply: measurableU; [apply: mf|apply: mg].
have-> : D `&` (fun x => f x * g x) @^-1` A =
       (D `&` [set x | f x *? g x]) `&` (fun x => f x * g x) @^-1` A.
  rewrite -setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //; apply: neq0_mule_def.
  by apply: contra_notT NA0; rewrite negbK => /eqP <-.
have Dfg : D `&` [set x | f x *? g x] `<=` D by apply: subIset; left.
apply: hwlogM => //.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite -setIA setIid.
- by move=> ? [].
Qed.

Lemma emeasurable_funeM D (f : T -> \bar R) (k : \bar R) :
  measurable_fun D f -> measurable_fun D (fun x => k * f x)%E.
Proof.
move=> mf; rewrite (_ : (fun x => k * f x) = (cst k) \* f)//.
exact/(emeasurable_funM _ mf)/measurable_fun_cst.
Qed.

(*NB: little need to recover this one, this is a combination
of emeasurable_funM and more basic lemmas*)
(*Lemma emeasurable_funM_presfun_ind1 D N f :
  measurable N -> measurable D -> measurable_fun D f ->
  measurable_fun D (f \* (EFin \o presfun_ind1 pt N)).
Proof.
move=> mN mD mf; apply: emeasurable_funM => //.
by apply: measurable_fun_comp => //; exact: measurable_fun_presfun_ind1.
Qed.*)

End emeasurable_fun.

Section measurable_fun_sum.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (D : set T).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).

Lemma measurable_fun_sum s : measurable_fun D (fun x => \sum_(i <- s) f i x).
Proof.
elim: s => [|h t ih].
  by under eq_fun do rewrite big_nil; exact: measurable_fun_cst.
under eq_fun do rewrite big_cons //=; apply: emeasurable_funD => // => x Dx.
Qed.

End measurable_fun_sum.

Section ge0_integral_sum.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_sum (s : seq I) :
  \int_ D (\sum_(k <- s) f k x) 'd mu[x] =
  \sum_(k <- s) \int_ D (f k x) 'd mu[x].
Proof.
elim: s => [|h t ih].
  by (under eq_fun do rewrite big_nil); rewrite big_nil integral0.
rewrite big_cons /= -ih -ge0_integralD//.
- by apply: eq_integral => x Dx; rewrite big_cons.
- by move=> *; apply: f0.
- by move=> *; apply: sume_ge0 => // k _; exact: f0.
- exact: measurable_fun_sum.
Qed.

End ge0_integral_sum.

Section monotone_convergence_theorem.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable g' : (T -> \bar R)^nat.
Hypothesis mg' : forall n, measurable_fun D (g' n).
Hypothesis g'0 : forall n x, D x -> 0 <= g' n x.
Hypothesis nd_g' : forall x, D x -> nondecreasing_seq (g'^~ x).
Let f' := fun x => lim (g'^~ x).

Let g n := (g' n \|_ D).

Let g0 n x : 0 <= g n x. Proof. exact/erestrict_ge0/g'0. Qed.

Let mg n : measurable_fun setT (g n). Proof. exact: measurable_restrict. Qed.

Let nd_g x : nondecreasing_seq (g^~ x).
Proof.
by move=> m n mn; rewrite /g/patch; case: ifP => // /set_mem /nd_g' ->.
Qed.

Let f := fun x => lim (g^~ x).

Let is_cvg_g t : cvg (g^~ t).
Proof. by move=> ?; apply: ereal_nondecreasing_is_cvg => m n ?; apply/nd_g. Qed.

Local Definition g2' n : (T -> R)^nat := approx (g n) setT.
Local Definition g2 n : {nnsfun T >-> R}^nat := nnsfun_approx measurableT (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : {nnsfun T >-> R}^nat :=
  fun k =>  bigmax_nnsfun (g2^~ k) k.

Local Lemma max_g2E : max_g2 = max_g2' :> (T -> R)^nat.
Proof.
rewrite funeq2E => n t; rewrite bigmax_nnsfunE.
by under eq_bigr do rewrite nnsfun_approxE.
Qed.

Let is_cvg_g2 n t : cvg (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvg => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Local Lemma nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!bigmax_nnsfunE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
   rewrite !nnsfun_approxE.
   by apply/lefP/nd_approx.
rewrite (bigmaxD1 ord_max)// le_maxr; apply/orP; right.
 rewrite [X in (_ <= X)%R](eq_bigl (fun i => nat_of_ord i < n)%N); last first.
   move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
   by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
by rewrite (big_ord_narrow (leqnSn n)).
Qed.

Let is_cvg_max_g2 t : cvg (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Local Lemma max_g2_g k x : ((max_g2 k x)%:E <= g k x)%O.
Proof.
rewrite bigmax_nnsfunE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  apply/bigmax_lerP; split => //; apply: g0D.
rewrite (@big_morph _ _ EFin 0%:E maxe) //; last by move=> *; rewrite maxEFin.
apply: le_bigmax => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx _ _ _)) => //; exact/nd_g/ltnW.
Qed.

Local Lemma lim_max_g2_f t : lim (EFin \o max_g2 ^~ t) <= f t.
Proof.
by apply: lee_lim => //; near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Local Lemma lim_g2_max_g2 t n :
  lim (EFin\o g2 n ^~ t) <= lim (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //; near=> k; rewrite /= bigmax_nnsfunE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (@bigmax_sup _ _ _ (Ordinal nk)).
Unshelve. all: by end_near. Qed.

Local Lemma cvg_max_g2_f t : EFin \o max_g2 ^~ t --> f t.
Proof.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f _)) // (cvg_lim _ g_l).
have := lee_pinfty l; rewrite le_eqVlt => /predU1P[->|loo].
  by rewrite lee_pinfty.
rewrite -(cvg_lim _ g_l) //= ereal_lim_le => //.
near=> n.
have := lee_pinfty (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
- have h := @dvg_approx _ _ _ setT t Logic.I fntoo.
  have g2oo : lim (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/dvg_ereal_cvg.
    under [X in X --> _]eq_fun do rewrite nnsfun_approxE.
    have : {homo (approx (g n) [set: T])^~ t : n0 m / (n0 <= m)%N >-> (n0 <= m)%R}.
      exact/lef_at/nd_approx.
    by move/nondecreasing_dvg_lt => /(_ h).
  have -> : lim (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo lee_pinfty_eq => /eqP.
  by rewrite lee_pinfty.
- have approx_g_g := @cvg_approx _ _ _ setT t (fun t _ => g0 n t) Logic.I fntoo.
  have <- : lim (EFin \o g2 n ^~ t) = g n t.
    have /cvg_lim <- // : EFin \o (approx (g n) setT)^~ t --> g n t.
      move/cvg_comp : approx_g_g; apply.
      by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
    rewrite (_ : _ \o _ = EFin \o (approx (g n) setT)^~ t)// funeqE => m.
    by rewrite [in RHS]/= -nnsfun_approxE.
  exact: (le_trans _ (lim_g2_max_g2 t n)).
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int_ D (f' x) 'd mu[x] = lim (fun n => \int_ D (g' n x) 'd mu[x]).
Proof.
rewrite integral_mkcond.
under [in RHS]eq_fun do rewrite integral_mkcond -/(g _).
have -> : f' \|_ D = f.
  apply/funext => x; rewrite /f /f' /g /patch /=; case: ifPn => //=.
  by rewrite lim_cst.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => \int (g n x) 'd mu[x]).
    move=> m n mn; apply: ge0_le_integral => //.
    by move=> *; exact: nd_g.
  have ub n : \int (g n x) 'd mu[x] <= \int (f x) 'd mu[x].
    apply: ge0_le_integral => //.
    - by move=> x _; apply: ereal_lim_ge => //; apply: nearW => k; exact/g0.
    - apply: emeasurable_fun_cvg mg _ => x _.
      by apply: ereal_nondecreasing_is_cvg.
    - move=> x Dx; apply: ereal_lim_ge => //.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: ereal_lim_le => //; [exact:ereal_nondecreasing_is_cvg|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ mu _ _ max_g2) //; last 3 first.
  - move=> t; apply: ereal_lim_ge => //.
    by apply: nearW => n; exact: g0.
  - by move=> t m n mn; exact/lefP/nd_max_g2.
  - by move=> x; apply: cvg_max_g2_f.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvg => // n m nm; apply: ge0_le_integral => //.
  by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralTE//.
  by apply: ereal_sup_ub; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  (fun n => \int_ D (g' n x) 'd mu[x]) --> \int_ D (f' x) 'd mu[x].
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvg => m n mn.
by apply ge0_le_integral => // t Dt; [exact: g'0|exact: g'0|exact: nd_g'].
Qed.

End monotone_convergence_theorem.

Section integral_series.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma integral_sum :
  \int_ D (\sum_(n <oo) f n x) 'd mu[x] = \sum_(n <oo) (\int_ D (f n x) 'd mu[x]).
Proof.
rewrite monotone_convergence //.
- rewrite -lim_mkord.
  rewrite (_ : (fun _ => _) = (fun n => (\sum_(k < n) \int_ D (f k x) 'd mu[x])))//.
  by rewrite funeqE => n; rewrite ge0_integral_sum// big_mkord.
- by move=> n; exact: measurable_fun_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_series.

(* generalization of ge0_integralM_EFin to a constant potentially +oo
   using the monotone convergence theorem *)
Section ge0_integralM.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma ge0_integralM (k : \bar R) : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int_ D (k * f x)%E 'd mu[x] = k * \int_ D (f x) 'd mu[x].
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralM_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by apply: emeasurable_funeM.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g^~x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => lim (g^~ x).
transitivity (\int_ D (lim (g^~ x)) 'd mu[x]).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0 (f x).
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
  - rewrite -fx0 mule0 /g -fx0 [X in X @ _ --> _](_ : _ = cst 0).
      exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite mule0.
rewrite (monotone_convergence mu mD mg g0 nd_g).
rewrite (_ : (fun _ => _) = (fun n => n%:R%:E * \int_ D (f x) 'd mu[x])); last first.
  by rewrite funeqE => n; exact: ge0_integralM_EFin.
have : 0 <= \int_ D (f x) 'd mu[x] by apply: integral_ge0.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  rewrite mule0 (_ : (fun _ => _) = cst 0) ?lim_cst//.
  by under eq_fun do rewrite mule0.
rewrite gt0_mulpinfty//; apply/cvg_lim => //; apply/ereal_cvgPpinfty => M M0.
near=> n; have [ifoo|] := ltP (\int_ D (f x) 'd mu[x]) +oo; last first.
  rewrite lee_pinfty_eq => /eqP ->;  rewrite mulrinfty muleC.
  rewrite gt0_mulpinfty ?lee_pinfty//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (\int_ D (f x) 'd mu[x])); last first.
  by rewrite fin_numElt ifoo andbT (le_lt_trans _ if_gt0)// lee_ninfty.
rewrite -lee_pdivr_mulr//; last first.
  by move: if_gt0 ifoo; case: (\int_ D (f x) 'd mu[x]).
near: n.
exists `|ceil (M * (fine (\int_ D (f x) 'd mu[x]))^-1)|%N => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
rewrite lee_fin natr_absz ger0_norm ?ceil_ge//.
rewrite ceil_ge0// mulr_ge0 => //; first exact: ltW.
by rewrite invr_ge0; apply: le0R; exact: integral_ge0.
Unshelve. all: by end_near. Qed.

End ge0_integralM.

Section fatou.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int_ D (elim_inf (f^~ x)) 'd mu[x] <=
              elim_inf (fun n => \int_ D (f n x) 'd mu[x]).
Proof.
pose g n := fun x => ereal_inf [set f k x | k in [set k | k >= n]%N].
have mg := measurable_fun_ereal_inf mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
rewrite (monotone_convergence) //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: (ge0_le_integral) => //; [exact: g0|exact: g0|].
  move=> x Dx; apply: le_ereal_inf => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N -> \int_ D (g n x) 'd mu[x] <=
    ereal_inf [set \int_ D (f k x) 'd mu[x] | k in [set p | n <= p]%N].
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: ge0_le_integral => //; [exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lb; exists k.
  exact.
Qed.

End fatou.

Section integralN.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma integralN D (f : T -> \bar R) :
  \int_ D (f^\+ x) 'd mu[x] +? (- \int_ D (f^\- x) 'd mu[x]) ->
  \int_ D ((-%E \o f) x) 'd mu[x] = - \int_ D (f x) 'd mu[x].
Proof.
have [f_fin _|] := boolP (\int_ D (f^\- x) 'd mu[x] \is a fin_num).
  rewrite integralE// [in RHS]integralE// oppeD ?fin_numN// oppeK addeC.
  by rewrite funennpN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -lee_ninfty_eq; apply/negP.
  by rewrite -ltNge (lt_le_trans _ (integral_ge0 _ _))// ?lte_ninfty.
rewrite nfoo adde_defEninfty.
rewrite -lee_pinfty_eq -ltNge lte_pinfty_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE// [in RHS]integralE// nfoo [in RHS]addeC oppeD//.
  by rewrite funennpN.
by rewrite integralE// [in RHS]integralE// funenngN funennpN nfoo pfoo.
Qed.

Lemma integral_ge0N (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int_ D ((-%E \o f) x) 'd mu[x] = - \int_ D (f x) 'd mu[x].
Proof.
move=> f0; rewrite integralN // (eq_integral _ (ge0_funennpE _))// integral0//.
by rewrite oppe0 fin_num_adde_def.
Qed.

End integralN.

Lemma restrict_set0 T (R : numFieldType) (f : T -> R) : f \|_ set0 = cst 0.
Proof. by apply/funext => x; rewrite /restrict in_set0. Qed.

Section integral_cst.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma sintegral_cst (x : {nonneg R}) :
  sintegral mu (cst x%:nngnum \|_ D) = x%:nngnum%:E * mu D.
Proof.
(* rewrite /sintegral (fsbigID [set x%:nngnum])/=; last first. *)
(*   rewrite setTI; have := @fimfunP _ _ (proj_nnsfun (cst_nnsfun T x) mD). *)
(*   apply: sub_finite_set => y. *)
(*   have [->|y0] := eqVneq y 0%R; first by rewrite /preimage/= mul0e. *)
(*   rewrite /preimage/=. *)
(*   have [|/set0P[z Dz]] := eqVneq D set0. *)
(*     move=> {1}->; rewrite restrict_set0/=. *)
(*     rewrite (_ : [set _ | _] = set0) ?measure0 ?mule0//. *)
(*     by apply/seteqP; split => // z/= /esym; exact/eqP. *)
(*   have [yx _|yx] := eqVneq y x%:nngnum; last first. *)
(*     rewrite (_ : [set _ | _] = set0) ?measure0 ?mule0//. *)
(*     apply/seteqP; split=> // u/=. *)
(*     by rewrite /restrict; case: ifPn => [|] _ /esym; exact/eqP. *)
(*   by exists z=> //; rewrite mindicE mem_set// mulr1. *)
(* rewrite !setTI fsbig_set1 fsbig1 ?adde0; last first. *)
(*   move=> r/= /eqP rx; rewrite preimage_restrict/=. *)
(*   case: ifPn; first by rewrite inE/= => <-; rewrite !mul0e. *)
(*   by rewrite set0U preimage_cst eq_sym (negbTE rx) setI0 measure0 mule0. *)
(* rewrite preimage_restrict /=. *)
(* case: ifPn; first by rewrite inE/= => <-; rewrite !mul0e. *)
(* by rewrite notin_set/= => x0; rewrite set0U preimage_cst eqxx/= setIT. *)
Admitted.

Lemma integral_cst (r : R) : (0 <= r)%R ->
  \int_ D ((EFin \o cst r) x) 'd mu[x] = r%:E * mu D.
Proof.
move=> r0; rewrite ge0_integralE//.
rewrite (_ : cst r = cst_nnsfun _ (Nonneg.NngNum _ r0)) //.
rewrite (restrict_comp EFin)// mrestrict nnintegral_nnsfun//.
by rewrite -mrestrict sintegral_cst.
Qed.

Lemma integral_cst_pinfty : mu D != 0 -> \int_ D ((cst +oo) x) 'd mu[x] = +oo.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => lim (g^~ t)) = cst +oo.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/dvg_ereal_cvg/cvgPpinfty=> M; exists `|ceil M|%N => //= m.
  rewrite /= -(ler_nat R); apply: le_trans.
  by rewrite (le_trans (ceil_ge _))// natr_absz ler_int ler_norm.
rewrite monotone_convergence //.
- rewrite /g (_ : (fun _ => _) = (fun n => n%:R%:E * mu D)); last first.
    by rewrite funeqE => n; rewrite -integral_cst.
  apply/cvg_lim => //; apply/ereal_cvgPpinfty => M M0.
  have [muDoo|muDoo] := ltP (mu D) +oo; last first.
    exists 1%N => // m /= m0.
    move: muDoo; rewrite lee_pinfty_eq => /eqP ->.
    by rewrite mulrinfty gtr0_sg ?mul1e ?lee_pinfty// ltr0n.
  exists `|ceil (M / fine (mu D))|%N => // m /=.
  rewrite -(ler_nat R) => MDm.
  rewrite -(@fineK _ (mu D)); last by rewrite ge0_fin_numE// measure_ge0.
  rewrite -lee_pdivr_mulr; last first.
    by apply: lt0R; rewrite muDoo andbT lt_neqAle measure_ge0// andbT eq_sym.
  rewrite lee_fin.
  apply: le_trans MDm.
  by rewrite natr_absz (le_trans (ceil_ge _))// ler_int ler_norm.
- by move=> n; exact: measurable_fun_cst.
- by move=> n x Dx; rewrite /cst lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.
End integral_cst.

Section integral_ind.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integral_indic (E : set T) : measurable E ->
  \int_ D ((@EFin R \o \1_E) x) 'd mu[x] = mu (E `&` D).
Proof.
move=> mE.
rewrite (_ : \1_E = indic_nnsfun R mE)//.
rewrite integral_nnsfun//= restrict_indic sintegral_indic//.
exact: measurableI.
Qed.

(* TODO: use \int_ *)
(*Lemma sintegral_nnpresfun_ind (x : {nonneg R}) (E : set T) :
  measurable E ->
  sintegral mu D (nnpresfun_ind pt x E) = x%:nngnum%:E * mu (E `&` D).
Proof.
move=> mE; rewrite sintegralE /= srng_presfun_ind.
case: ifPn => [/eqP x0|x0].
  by rewrite x0 big_cons big_nil 2!mul0e add0e.
case: ifPn => [/eqP E0|E0].
  by rewrite big_cons mul0e big_nil E0 set0I measure0 mule0 adde0.
case: ifPn => [/eqP ET|ET].
  rewrite big_cons big_nil adde0 ET setTI.
  rewrite (_ : presfun_ind pt x%:nngnum setT @^-1` _ = setT) ?setTI//.
  by rewrite predeqE => t; rewrite /preimage /= presfun_indE in_setT mulr1.
rewrite 2!big_cons mul0e add0e big_nil adde0; congr (_ * mu (_ `&` _)).
rewrite predeqE => t; split => [|Et].
  rewrite /preimage /= presfun_indE.
  have [tE|tE] := boolP (t \in E); first by rewrite inE in tE.
  by rewrite mulr0 => /esym/eqP; rewrite (negbTE x0n).
by rewrite /preimage /= presfun_indE mem_set// mulr1.
Qed.*)

(*Lemma sintegral_scale_nnsfun (k : R) (E : set T) (f : nnsfun T R)
  (k0 : (0 <= k)%R) : measurable E ->
  sintegral mu D (scale_nnsfun pt f k0) = k%:E * sintegral mu D f.
Proof.
move=> mE; rewrite sintegralE srng_sfun_scale /sfun_scale_rng.
case: ifPn => [/eqP k_eq0|k_neq0].
  by rewrite big_cons big_nil adde0 mul0e k_eq0 mul0e.
rewrite big_map sintegralE [in RHS]big_seq ge0_sume_distrr; last first.
  move=> r rf; rewrite mule_ge0 //; first exact: (NNSFuncdom_ge0 rf).
  by apply: measure_ge0; apply: measurableI => //; exact: sfun_measurable_preimage_set1.
rewrite -big_seq; apply: eq_bigr => r _.
rewrite EFinM muleA; congr (_ * mu (_ `&` D)).
rewrite predeqE => x; split.
  by rewrite /preimage /= sfun_scaleE => /mulrI; apply; rewrite unitfE.
by rewrite /preimage /= => <-; rewrite sfun_scaleE.
Qed.*)

(* TODO: too long *)
(*Lemma sintegral_presfun_proj (A : set T) (E : set T) (mE : measurable E)
    (g : {nnsfun T >-> R}) : E `<=` A ->
  sintegral mu (proj_nnsfun g mE) = sintegral mu g.
Proof.
 srng_presfun_proj /sfun_proj_rng.
case: ifPn=> [/orP[|/eqP ET]|].
- rewrite mem_filter => /andP[g0E0 g0].
  rewrite big_filter big_mkcond /=; apply: eq_bigr => r _.
  case: ifPn => [grR0|].
    have [->|r0] := eqVneq r 0%R; first by rewrite !mul0e.
    congr (_ * mu _)%E.
    rewrite predeqE => t; split=> [|[]].
      rewrite /preimage /= presfun_projE.
      have [|tE] := boolP (t \in E).
        by rewrite inE => tE; rewrite mulr1 => -[] ->.
      by rewrite mulr0 => -[] /esym/eqP; rewrite (negbTE r0).
    rewrite /preimage /= => gtr Et.
    by split; [rewrite presfun_projE mem_set// mulr1|exact: EA].
  by rewrite negbK => /eqP ->; rewrite measure0 mule0.
- rewrite big_filter big_mkcond /=; apply: eq_bigr => r _.
  rewrite ET setIT; case: ifPn => [gr0|].
    congr (_ * mu _); rewrite predeqE => y; split.
      by rewrite /preimage /= presfun_projE in_setT mulr1 => -[].
    have [|] := boolP (y \in A).
      by rewrite inE /preimage /= presfun_projE in_setT mulr1.
    rewrite notin_set.
    by move: EA; rewrite ET subTset => -> /(_ Logic.I).
  by rewrite negbK => /eqP ->; rewrite measure0 mule0.
- rewrite negb_or => /andP[].
  rewrite mem_filter negb_and negbK => /orP[/eqP g0E ET|g0 ET].
    rewrite big_cons mul0e add0e big_filter big_mkcond /=.
    apply: eq_bigr => r _; case: ifPn => [grE0|].
      have [->|r0] := eqVneq r 0%R; first by rewrite 2!mul0e.
      congr (_ * mu _); rewrite predeqE => y; split.
        rewrite /preimage /= presfun_projE.
        have [|yE] := boolP (y \in E).
          by rewrite mulr1 inE; tauto.
        by rewrite mulr0 => -[] /esym/eqP; rewrite (negbTE r0).
      rewrite /preimage /= => -[gyr Ey].
      by rewrite presfun_projE mem_set// mulr1; split => //; exact: EA.
    by rewrite negbK => /eqP ->; rewrite measure0 mule0.
  rewrite big_cons mul0e add0e big_filter big_mkcond; apply: eq_bigr => r _.
  case: ifPn => [grE0|].
    have [->|r0] := eqVneq r 0%R; first by rewrite 2!mul0e.
    congr (_ * mu _); rewrite predeqE => y; split.
      rewrite /preimage /= presfun_projE.
      have [|yE] := boolP (y \in E).
        by rewrite inE => yE; rewrite mulr1; tauto.
    by rewrite mulr0 => -[] /esym/eqP; rewrite (negbTE r0).
  rewrite /preimage /= presfun_projE => -[->] Ey.
  by rewrite mem_set// mulr1; split => //; exact: EA.
by rewrite negbK => /eqP ->; rewrite measure0 mule0.
Qed.

Lemma sintegral_proj_nnsfun (A : set T) (E : set T) (mE : measurable E)
    (g : nnsfun T R) : E `<=` A ->
  sintegral mu A (proj_nnsfun g mE) = sintegral mu E g.
Proof. by move=> EA; rewrite sintegral_presfun_proj. Qed.

Lemma integral_EFin_nnpresfun_ind (r : {nonneg R}) (E : set T) :
  measurable E ->
  \int_ D ((EFin \o nnpresfun_ind pt r E) x) 'd mu[x] =
  r%:nngnum%:E * mu (E `&` D).
Proof.
move=> mE.
rewrite integral_ge0E//; last by move=> t Dt; rewrite lee_fin.
transitivity (nnintegral mu D (EFin \o nnsfun_ind pt r mE)).
  apply eq_nnintegral => x xD.
  by rewrite /= presfun_indE sfun_indE.
rewrite nnintegral_nnsfun// -sintegral_nnpresfun_ind//; apply eq_sintegral.
by move=> x xD; rewrite nnsfun_indE presfun_indE.
Qed.

Lemma integral_EFin_sfun_ind (r : R) (E : set T) (mE : measurable E) :
  \int_ D ((EFin \o sfun_ind pt r mE) x) 'd mu[x] = r%:E * mu (E `&` D).
Proof.
have [r0|r0] := leP 0%R r.
  transitivity (\int_ D ((EFin \o nnpresfun_ind pt (Nonneg.NngNum _ r0) E) x) 'd mu[x]).
    by apply: eq_integral => x Dx /=; rewrite sfun_indE presfun_indE.
  by rewrite integral_EFin_nnpresfun_ind.
rewrite -oppr0 -ltr_oppr in r0.
transitivity (\int_ D ((-%E \o (EFin \o nnpresfun_ind pt (Nonneg.NngNum _ (ltW r0)) E)) x) 'd mu[x]).
  by apply: eq_integral => t tD /=; rewrite sfun_indE EFinN /= presfun_indE /= mulNr opprK.
rewrite integral_ge0N//; last by move=> t Dt; rewrite lee_fin.
by rewrite integral_EFin_nnpresfun_ind//= EFinN mulNe oppeK.
Qed.
*)

End integral_ind.

Section subset_integral.
Variables (T : measurableType) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integral_setU (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) :
  measurable_fun (A `|` B) f ->
  (forall x, (A `|` B) x -> 0 <= f x)%E ->
  [disjoint A & B] ->
  (\int_ (A `|` B) (f x) 'd mu[x] = \int_ A (f x) 'd mu[x] + \int_ B (f x) 'd mu[x])%E.
Proof.
move=> mf f0 AB.
transitivity (\int_ (A `|` B) ((f \|_ A) x + (f \|_ B) x) 'd mu[x])%E.
  apply eq_integral => x; rewrite inE => -[xA|xB].
    rewrite /patch mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xB.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
  rewrite /patch addeC mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xA.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
rewrite ge0_integralD//; last 5 first.
  - exact: measurableU.
  - by move=> x _; apply: erestrict_ge0 => y Ay; apply: f0; left.
  - have : measurable_fun A f.
      by apply: measurable_funS mf; [exact: measurableU|exact: subsetUl].
    by move/(measurable_restrict mA); apply: measurable_funS.
  - by move=> x _; apply: erestrict_ge0 => y By; apply: f0; right.
  - have : measurable_fun B f.
      by apply: measurable_funS mf; [exact: measurableU|exact: subsetUr].
    by move/(measurable_restrict mB); apply: measurable_funS.
by rewrite -integral_mkcondl setIC setUK -integral_mkcondl setKU.
Qed.

Lemma subset_integral (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) :
  measurable_fun B f ->
  (forall x, B x -> 0 <= f x)%E ->
  A `<=` B -> (\int_ A (f x) 'd mu[x] <= \int_ B (f x) 'd mu[x])%E.
Proof.
move=> mf f0 AB.
rewrite -(setDUK AB) integral_setU//; last 4 first.
  - exact: measurableD.
  - by rewrite setDUK//.
  - by move=> x; rewrite setDUK//; exact: f0.
  - by rewrite disj_set2E setDIK.
by apply: lee_addl; apply: integral_ge0 => x [Bx _]; apply: f0.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> 0 < a ->
  (a%:E * mu (D `&` [set x | (`|g x| >= a%:E)%E]) <= \int_ D `|g x| 'd mu[x])%E.
Proof.
move=> mg a0.
have ? : measurable (D `&` [set x | (a%:E <= `|g x|)%E]).
  by apply: emeasurable_fun_c_infty => //; exact: measurable_fun_comp.
apply: (@le_trans _ _ (\int_ (D `&` [set x | `|g x| >= a%:E]) `|g x|%E 'd mu[x])%E).
  apply: (@le_trans _ _ (\int_ (D `&` [set x | `|g x| >= a%:E]) (cst a%:E x) 'd mu[x])%E).
    by rewrite integral_cst// ltW.
  apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite ltW.
  - exact: measurable_fun_cst.
  - by apply: measurable_fun_comp => //; apply: measurable_funS mg.
  - by move=> x /= [].
by apply: subset_integral => //; exact: measurable_fun_comp.
Qed.

End subset_integral.

(*Section simple_function_integral2.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}) (D : set T) (f : sfun T R).
Let n := ssize f.
Let A := spimg f.
Let a := srng f.

Lemma sfunE x :
  (f x = \sum_(k < n) (a`_k) * presfun_ind1 pt (A k) x)%R.
Proof.
rewrite (bigD1 (img_idx f x))// big1/= ?addr0 /=.
  rewrite presfun_ind1E mem_set// ?mulr1 ?nth_index ?mem_srng//.
  exact/mem_spimg.
by move=> i ifx; rewrite presfun_ind1E memNset ?mulr0//; exact/memNspimg.
Qed.

End simple_function_integral2.*)

(*Section simple_function_integral3.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : nnsfun T R).
Let n := ssize f.
Let A := spimg f.
Let a := srng f.

(* TODO: not used?! *)
Lemma integral_nnsfun_presfun_ind1 : \int_ D (f x)%:E 'd mu[x] =
  \sum_(k < n) (a`_k)%:E * \int_ D (presfun_ind1 pt (A k) x)%:E 'd mu[x].
Proof.
rewrite integral_nnsfun//; apply eq_bigr => i _; congr (_ * _)%E; rewrite -/(A i).
by rewrite integral_indic//; exact: measurable_spimg.
Qed.

End simple_function_integral3.*)

Section Rintegral.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable (mu : {measure set T -> \bar R}).
Implicit Types D : set T.

Definition Rintegral D (f : T -> \bar R) := fine (\int_ D (f x) 'd mu[x]).

End Rintegral.

Section integrable.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable mu : {measure set T -> \bar R}.
Implicit Types (f : T -> \bar R).
Variables (D : set T) (mD : measurable D).

Definition integrable f :=
  measurable_fun D f /\ (\int_ D `|f x| 'd mu[x] < +oo).

Lemma eq_integrable f1 f2 : {in D , f1 =1 f2} ->
  integrable f1 -> integrable f2.
Proof.
move=> f12 [mf1 if1]; split; first exact: eq_measurable_fun mf1.
rewrite (le_lt_trans _ if1)//; apply ge0_le_integral=> //.
  by apply: measurable_fun_comp => //; exact: eq_measurable_fun mf1.
  by apply: measurable_fun_comp => //; exact: eq_measurable_fun mf1.
by move=> x Dx; rewrite f12// inE.
Qed.

Lemma le_integrable (f1 f2 : T -> \bar R) :
  measurable_fun D f1 -> (forall x, D x -> `|f1 x| <= `|f2 x|) ->
  integrable f2 -> integrable f1.
Proof.
move=> mf1 f1f2 [mf2 f2oo]; split => //; rewrite (le_lt_trans _ f2oo) //.
by apply: ge0_le_integral => //; exact: measurable_fun_comp.
Qed.

Lemma integrableN (f : T -> \bar R) : integrable f -> integrable (-%E \o f).
Proof.
move=> [mf foo]; split; last by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; apply: measurable_fun_comp => //; exact: emeasurable_fun_minus.
Qed.

Lemma integrableK (k : R) (f : T -> \bar R) :
  integrable f -> integrable (fun x => k%:E * f x).
Proof.
move=> [mf foo]; split; first exact: emeasurable_funeM.
under eq_fun do rewrite abseM.
rewrite ge0_integralM// ?lte_mul_pinfty//.
exact: measurable_fun_comp.
Qed.

Lemma integrableD (f1 f2 : T -> \bar R) :
  integrable f1 -> integrable f2 -> integrable (f1 \+ f2).
Proof.
move=> [mf1 f1oo] [mf2 f2oo]; split; first exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int_ D (`|f1 x| + `|f2 x|) 'd mu[x])).
  apply ge0_le_integral => //.
  - by apply: measurable_fun_comp => //; exact: emeasurable_funD.
  - by move=> *; exact: adde_ge0.
  - by apply: emeasurable_funD; apply: measurable_fun_comp.
  - by move=> *; exact: lee_abs_add.
rewrite ge0_integralD //; first exact: lte_add_pinfty.
- exact: measurable_fun_comp.
- exact: measurable_fun_comp.
Qed.

Lemma integrableB (f1 f2 : T -> \bar R) :
  integrable f1 -> integrable f2 -> integrable (f1 \- f2).
Proof.
by move=> if1 if2; apply/(integrableD if1); exact/integrableN.
Qed.

Lemma integrable_add_def f : integrable f ->
  \int_ D (f^\+ x) 'd mu[x] +? - \int_ D (f^\- x) 'd mu[x].
Proof.
move=>  [mf]; rewrite -[(fun x => _)]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
  - exact: emeasurable_fun_funenng.
  - exact: emeasurable_fun_funennp.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite lee_addl// integral_ge0.
- rewrite inE (@le_lt_trans _ _ 0)// ?lte_pinfty// lee_oppl oppe0.
  by rewrite integral_ge0.
Qed.

Lemma integral_funennp_lt_pinfty f : integrable f ->
  \int_ D (f^\- x) 'd mu[x] < +oo.
Proof.
move=> [mf]; apply: le_lt_trans; apply ge0_le_integral => //.
- by apply: emeasurable_fun_funennp => //; exact: emeasurable_funN.
- exact: measurable_fun_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funennp.
    by move: fx0; rewrite -{1}oppe0 -lee_oppr => /max_idPl ->.
  rewrite gee0_abs// /funennp.
  by move: (fx0); rewrite -{1}oppe0 -lee_oppl => /max_idPr ->.
Qed.

Lemma integral_funenng_lt_pinfty f : integrable f ->
  \int_ D (f^\+ x) 'd mu[x] < +oo.
Proof.
move=> [mf]; apply: le_lt_trans; apply ge0_le_integral => //.
- by apply: emeasurable_fun_funenng => //; exact: emeasurable_funN.
- exact: measurable_fun_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funenng.
    by move: (fx0) => /max_idPr ->; rewrite -lee_oppr oppe0.
  by rewrite gee0_abs// /funenng; move: (fx0) => /max_idPl ->.
Qed.

End integrable.

Notation "mu .-integrable" := (integrable mu) : type_scope.

Section integrable_ae.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Hypotheses (mD : measurable D) (fint : mu.-integrable D f).

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite [X in measurable X](_ : _ = D `&` f @^-1` [set -oo; +oo]).
    by apply: fint.1 => //; apply: measurableU; exact: emeasurable_set1.
  rewrite predeqE => t; split=> [[/eqP ftoo Dt]|[Dt]].
    split => //.
    by move: ftoo; rewrite /preimage /= eqe_absl => /andP[/orP[|]/eqP]; tauto.
  by rewrite /preimage /= => -[|]; rewrite /E /= => ->.
have [ET|ET] := eqVneq E setT.
  have foo t : `|f t| = +oo by have [] : E t by rewrite ET.
  move: fint.2.
  suff: \int_ D `|f x| 'd mu[x] = +oo by move=> ->; rewrite ltxx.
  rewrite (_ : (fun _ => _) = cst +oo) ?integral_cst_pinfty //.
  by rewrite funeqE => t; rewrite /= foo.
suff: mu E = 0.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt ftfin]; split => //.
  apply/eqP; rewrite eqe_absl lee_pinfty andbT.
  by move/negP : ftfin; rewrite fin_numE negb_and 2!negbK orbC.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M M0 muM] : exists2 M, (0 <= M)%R &
                    (forall n, n%:R%:E * mu (E `&` D) <= M%:E).
  exists (fine (\int_ D `|f x| 'd mu[x])); first exact/le0R/integral_ge0.
  move=> n.
(*  pose N : sfun T R := sfun_ind pt n%:R mE.
  have <- : \int_ D ((EFin \o N) x) 'd mu[x] = n%:R%:E * mu (E `&` D).
    by rewrite integral_EFin_sfun_ind //= 1?setIC.
  rewrite fineK//; last first.
    by case: fint => _ foo; rewrite ge0_fin_numE//; exact: integral_ge0.
  apply: ge0_le_integral => //.
  - by move=> *; rewrite lee_fin /N sfun_indE.
  - by apply/EFin_measurable_fun; exact: measurable_sfun.
  - move=> x Dx; rewrite /N /= sfun_indE.
    have [|xE] := boolP (x \in E); last by rewrite mulr0.
    by rewrite /E inE /= => -[->]; rewrite lee_pinfty.*) admit.
apply/eqP/negPn/negP => /eqP muED0.
move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite lee_pinfty_eq => /eqP ->; exists 1%N; rewrite mul1e lee_pinfty_eq.
exists `|ceil (M * (fine (mu (E `&` D)))^-1)|%N.+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  rewrite fin_numElt muEDoo andbT.
  by rewrite (lt_le_trans _ (measure_ge0 _ _))// ?lte_ninfty//.
rewrite lte_fin -ltr_pdivr_mulr.
  rewrite -addn1 natrD natr_absz ger0_norm.
    by rewrite (le_lt_trans (ceil_ge _))// ltr_addl.
  by rewrite ceil_ge0// divr_ge0//; apply/le0R/measure_ge0; exact: measurableI.
rewrite -lte_fin fineK.
  rewrite lt_neqAle measure_ge0// ?andbT.
  suff: E `&` D = E by move=> ->; apply/eqP/nesym.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Admitted.

End integrable_ae.

Section linearityM.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Lemma integralM r : \int_ D (r%:E * f x) 'd mu[x] = r%:E * \int_ D (f x) 'd mu[x].
Proof.
have [r0|r0|->] := ltgtP r 0%R; last first.
  by under eq_fun do rewrite mul0e; rewrite mul0e integral0.
- rewrite [in LHS]integralE// gt0_funenngM// gt0_funennpM//.
  rewrite (ge0_integralM_EFin _ _ _ _ (ltW r0)) //; last first.
    by apply: emeasurable_fun_funenng => //; case: intf.
  rewrite (ge0_integralM_EFin _ _ _ _ (ltW r0)) //; last first.
    by apply: emeasurable_fun_funennp => //; case: intf.
  rewrite -muleBr 1?[in RHS]integralE//.
  by apply: integrable_add_def; case: intf.
- rewrite [in LHS]integralE// lt0_funenngM// lt0_funennpM//.
  rewrite ge0_integralM_EFin //; last 2 first.
    + by apply: emeasurable_fun_funennp => //; case: intf.
    + by rewrite -ler_oppr oppr0 ltW.
  rewrite ge0_integralM_EFin //; last 2 first.
    + by apply: emeasurable_fun_funenng => //; case: intf.
    + by rewrite -ler_oppr oppr0 ltW.
  rewrite -mulNe -EFinN opprK addeC EFinN mulNe -muleBr //; last first.
    by apply: integrable_add_def; case: intf.
  by rewrite [in RHS]integralE.
Qed.

End linearityM.

Section linearity.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> R).
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : mu.-integrable D g1.
Hypothesis if2 : mu.-integrable D g2.

Lemma integralD_EFin :
  \int_ D ((g1 \+ g2) x) 'd mu[x] =
  \int_ D (g1 x) 'd mu[x] + \int_ D (g2 x) 'd mu[x].
Proof.
suff: \int_ D ((g1 \+ g2)^\+ x) 'd mu[x] + \int_ D (g1^\- x) 'd mu[x] + \int_ D (g2^\- x) 'd mu[x] =
      \int_ D ((g1 \+ g2)^\- x) 'd mu[x] + \int_ D (g1^\+ x) 'd mu[x] + \int_ D (g2^\+ x) 'd mu[x].
  move=> h; rewrite [in LHS]integralE.
  move/eqP : h; rewrite -[in X in _ == X]addeA [in X in _ == X]addeC.
  have g12nng : \int_ D (g1^\+ x) 'd mu[x] + \int_ D (g2^\+ x) 'd mu[x] \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funenng_lt_pinfty.
    by apply adde_ge0; exact: integral_ge0.
  have g12nnp : \int_ D (g1^\- x) 'd mu[x] + \int_ D (g2^\- x) 'd mu[x] \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; apply: integral_funennp_lt_pinfty.
    by apply adde_ge0; exact: integral_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        have : mu.-integrable D (g1 \+ g2) by apply: integrableD.
        exact: integral_funenng_lt_pinfty.
      apply: adde_ge0; last exact: integral_ge0.
      by apply: adde_ge0; exact: integral_ge0.
    - by rewrite adde_defC fin_num_adde_def.
  rewrite -(addeA (\int_ D ((g1 \+ g2)^\+ x) 'd mu[x])).
  rewrite (addeC (\int_ D ((g1 \+ g2)^\+ x) 'd mu[x])).
  rewrite -addeA (addeC (\int_ D (g1^\- x) 'd mu[x] + \int_ D (g2^\- x) 'd mu[x])).
  rewrite eq_sym -(sube_eq g12nng); last by rewrite fin_num_adde_def.
  move/eqP => <-.
  rewrite oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funennp_lt_pinfty if2.
    exact: integral_ge0.
  rewrite -addeA (addeCA (\int_ D (g2^\+ x) 'd mu[x])).
  by rewrite addeA -(integralE _ _ g1) -(integralE _ _ g2).
have : (g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in X in _ == X]addeC -sube_eq; last 2 first.
    by rewrite /funenng /funennp /g1 /g2 /= !maxEFin.
    by rewrite /funenng /funennp /g1 /g2 /= !maxEFin.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite /funenng /funennp !maxEFin.
    by rewrite /funenng /funennp !maxEFin.
  apply/eqP.
  rewrite -[LHS]/((g1^\+ \+ g2^\+ \- (g1^\- \+ g2^\-)) x) -funeD_nngD.
  by rewrite -[RHS]/((_ \- _) x) -funeD_Dnng.
move/(congr1 (fun y => \int_ D (y x) 'd mu[x])).
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0.
  - rewrite /funennp /funenng /g1 /g2 /=.
    under eq_fun do rewrite 2!maxEFin; rewrite -/(measurable_fun _ _).
    apply: emeasurable_funD => //.
      under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
      apply: emeasurable_fun_funenng => //;
      apply/EFin_measurable_fun/measurable_funD => //.
        by case: if1 => /EFin_measurable_fun.
      by case: if2 => /EFin_measurable_fun.
    under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
    apply: emeasurable_fun_funenng => //.
    apply/EFin_measurable_fun/measurable_funN => //.
    by case: if1 => /EFin_measurable_fun.
  - by [].
  - by apply: emeasurable_fun_funennp => //; case: if2.
rewrite (ge0_integralD mu mD); last 4 first.
  - by [].
  - apply: emeasurable_fun_funenng => //=.
    apply/EFin_measurable_fun/measurable_funD => //.
      by case: if1 => /EFin_measurable_fun.
    by case: if2 => /EFin_measurable_fun.
  - by [].
  - apply: emeasurable_fun_funenng => //.
    rewrite /g1 /comp.
    under eq_fun do rewrite -EFinN; rewrite -/(measurable_fun _ _).
    apply/EFin_measurable_fun; apply: measurable_funN => //.
    by case: if1 => /EFin_measurable_fun.
move=> ->.
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; exact: adde_ge0.
  - rewrite /g1 /g2 /= /comp /= /funennp /funenng.
    under eq_fun do rewrite -EFinN.
    under eq_fun do rewrite 2!maxEFin; rewrite -/(measurable_fun _ _).
    apply: emeasurable_funD => //.
      under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
      apply: emeasurable_fun_funenng => //.
      apply/EFin_measurable_fun/measurable_funN => //.
      apply: measurable_funD => //.
        by case: if1 => /EFin_measurable_fun.
      by case: if2 => /EFin_measurable_fun.
     under eq_fun do rewrite -maxEFin; rewrite -/(measurable_fun _ _).
     by apply: emeasurable_fun_funenng => //; case: if1.
  - by [].
  - by apply: emeasurable_fun_funenng => //; case: if2.
rewrite (ge0_integralD mu mD) //.
- apply: emeasurable_fun_funennp => //.
  by apply: emeasurable_funD => //; [case: if1|case: if2].
- by apply: emeasurable_fun_funenng => //; case: if1.
Qed.

End linearity.

Lemma integralB_EFin (R : realType) (T : measurableType)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R)
  (mD : measurable D) :
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  (\int_ D ((f1 x)%:E - (f2 x)%:E) 'd mu[x] =
    (\int_ D ((EFin \o f1) x) 'd mu[x] - \int_ D ((EFin \o f2) x) 'd mu[x]))%E.
Proof.
move=> if1 if2; rewrite (integralD_EFin mD if1); last first.
  by rewrite (_ : _ \o _ = (fun x => - (f2 x)%:E))%E; [exact: integrableN|by []].
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Lemma le_abse_integral (T : measurableType) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R)
  (mD : measurable D) : measurable_fun D f ->
  (`| \int_ D (f x) 'd mu[x]| <= \int_ D `|f x| 'd mu[x])%E.
Proof.
move=> mf.
rewrite integralE (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: integral_ge0.
rewrite gee0_abs; last exact: integral_ge0.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: emeasurable_fun_funenng | exact: emeasurable_fun_funennp].
Qed.

Section integral_presfun_ind1.
Variables (T : measurableType) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integral_presfun_ind1_setI (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  (\int_ (E `&` D) (f x) 'd mu[x] = \int_ E f x * (\1_D x)%:E 'd mu[x])%E.
Proof.
move=> mE; rewrite integral_mkcondr.
apply: eq_integral => x xE; rewrite /patch indicE.
by case: ifP; rewrite ?mule1// mule0.
Qed.

Lemma integral_presfun_ind1 (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (\int_ D (f x) 'd mu[x] = \int_ D f x * (\1_D x)%:E 'd mu[x])%E.
Proof. by rewrite -integral_presfun_ind1_setI// setIid. Qed.

End integral_presfun_ind1.

Section ae_eq.
Variables (T : measurableType) (R : realType) (pt : T).
Variable (mu : {measure set T -> \bar R}).

Definition ae_eq (D : set T) (f g : T -> \bar R) :=
  {ae mu, forall x, D x -> f x = g x}.

Lemma ae_eq_comp (D : set T) h (f g : T -> \bar R) :
  ae_eq D f g -> ae_eq D (h \o f) (h \o g).
Proof.
move=> [N [mN N0 subN]]; exists N; split => //.
by apply: subset_trans subN; apply: subsetC => x /= /[apply] ->.
Qed.

Lemma ae_eq_funenng_funennp (D : set T) (f g : T -> \bar R) :
  ae_eq D f g <-> (ae_eq D f^\+ g^\+ /\ ae_eq D f^\- g^\-)%E.
Proof.
split=> [[N [mN N0 DfgN]]|[[A [mA A0 DfgA] [B [mB B0 DfgB]]]]].
  by split; exists N; split => // x Dfgx; apply: DfgN => /=;
    apply: contra_not Dfgx => /= /[apply]; rewrite /funenng /funennp => ->.
exists (A `|` B); rewrite null_set_setU//; split=> //; first exact: measurableU.
move=> x /= /not_implyP[Dx fgx]; apply: contrapT => /not_orP[Ax Bx].
have [fgpx|fgnx] : (f^\+ x <> g^\+ x \/ f^\- x <> g^\- x)%E.
  apply: contrapT => /not_orP[/contrapT fgpx /contrapT fgnx].
  by apply: fgx; rewrite (funenngnnp f) (funenngnnp g) fgpx fgnx.
- by apply: Ax; exact/DfgA/not_implyP.
- by apply: Bx; exact/DfgB/not_implyP.
Qed.

Lemma ae_eq_sym D (a b : T -> \bar R) : ae_eq D a b -> ae_eq D b a.
Proof.
move=> [N1 [mN1 N10 subN1]]; exists N1; split => // x /= Dba; apply: subN1 => /=.
by apply: contra_not Dba => [+ Dx] => ->.
Qed.

Lemma ae_eq_trans D (a b c : T -> \bar R) :
  ae_eq D a b -> ae_eq D b c -> ae_eq D a c.
Proof.
move=> [N1 [mN1 N10 abN1]] [N2 [mN2 N20 bcN2]]; exists (N1 `|` N2); split => //.
- exact: measurableU.
- by rewrite null_set_setU.
- rewrite -(setCK N1) -(setCK N2) -setCI; apply: subsetC => x [N1x N2x] /= Dx.
  move/subsetC : abN1 => /(_ _ N1x); rewrite setCK /= => ->//.
  by move/subsetC : bcN2 => /(_ _ N2x); rewrite setCK /= => ->.
Qed.

Lemma ae_eq_sub D (a b c d : T -> \bar R) :
  ae_eq D a b -> ae_eq D c d -> ae_eq D (fun x => a x - c x)%E (fun x => b x - d x)%E.
Proof.
move=> [N1 [mN1 N10 abN1]] [N2 [mN2 N20 bcN2]]; exists (N1 `|` N2); split => //.
- exact: measurableU.
- by rewrite null_set_setU.
- rewrite -(setCK N1) -(setCK N2) -setCI; apply: subsetC => x [N1x N2x] /= Dx.
  move/subsetC : abN1 => /(_ _ N1x); rewrite setCK /= => ->//.
  by move/subsetC : bcN2 => /(_ _ N2x); rewrite setCK /= => ->.
(* TODO: same as trans *)
Qed.

Lemma ae_eq_mul2r D (a b c : T -> \bar R) :
  ae_eq D a b -> ae_eq D (fun x => a x * c x)%E (fun x => b x * c x)%E.
Proof.
move=> [N1 [mN1 N10 abN1]]; exists N1; split => // x /= /not_implyP[Dx].
move=> acbc; apply abN1 => /=; apply/not_implyP; split => //.
by apply: contra_not acbc => ->.
Qed.

Lemma ae_eq_mul2l D (a b c : T -> \bar R) :
  ae_eq D a b -> ae_eq D (fun x => c x * a x)%E (fun x => c x * b x)%E.
Proof.
move=> /ae_eq_mul2r-/(_ c); under eq_fun do rewrite muleC.
by under [in X in ae_eq _ _ X -> _]eq_fun do rewrite muleC.
Qed.

Lemma ae_eq_mul1l D (b c : T -> \bar R) :
  ae_eq D b (cst 1%E) -> ae_eq D c (fun x => c x * b x)%E.
Proof.
move=> /ae_eq_mul2l-/(_ c)/ae_eq_sym.
by under [in X in ae_eq _ X _ -> _]eq_fun do rewrite mule1.
Qed.

Lemma ae_eq_mul D (a b c : T -> \bar R) :
  ae_eq D a b -> ae_eq D (fun x => a x * c x)%E (fun x => b x * c x)%E.
Proof.
move=> [N1 [mN1 N10 abN1]]; exists N1; split => // x /= /not_implyP[Dx].
move=> acbc; apply abN1 => /=; apply/not_implyP; split => //.
by apply: contra_not acbc => ->.
Qed.

Lemma ae_eq_abse D (a b : T -> \bar R) :
  ae_eq D a b -> ae_eq D (abse \o a) (abse \o b).
Proof.
move=> [N [mN N0 subN]]; exists N; split => //; apply: subset_trans subN.
by apply: subsetC => x /= /[apply] ->.
Qed.

End ae_eq.

Section ae_eq_integral.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Local Notation ae_eq := (ae_eq mu).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  ae_eq D f (cst 0) -> \int_ D `|f x|%E 'd mu[x] = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose f_neq0 := D `&` [set x | f x != 0].
have mf_neq0 : measurable f_neq0 by apply: emeasurable_neq.
pose sfun_f : {nnfun _ >-> R} := indic_nnsfun R mf_neq0.
have le_f_M : forall x, D x -> `|f x| <= M%:E * (sfun_f x)%:E.
  move=> t Dt; rewrite /sfun_f/= /mindic/= indicE.
  have [|] := boolP (t \in f_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  rewrite notin_set /f_neq0 => /not_andP[//|/= /negP].
  by rewrite negbK => /eqP ->; rewrite abse0 mule0.
have f_neq0_eq0 : (mu f_neq0 = 0)%E.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
have : 0 <= \int_ D `|f x| 'd mu[x] <= `|M|%:E * mu f_neq0.
  apply/andP; split; first exact: integral_ge0.
  rewrite /f_neq0 -{2}(setIid D) setIAC.
  rewrite -integral_indic// -/f_neq0.
  rewrite -ge0_integralM//; last 3 first.
    - apply: measurable_fun_comp=> //.
      apply: (@measurable_funS _ _ setT) => //.
      by rewrite (_ : \1_ _ = mindic R mf_neq0)//.
    - by move=> x Dx; rewrite lee_fin.
    - by rewrite lee_fin.
  apply: ge0_le_integral => //.
  - by apply: measurable_fun_comp.
  - by move=> x Dx; rewrite mule_ge0// ?lee_fin//.
  - apply: emeasurable_funM; first exact: measurable_fun_cst.
    apply: measurable_fun_comp => //.
    apply: (@measurable_funS _ _ setT)=> //.
    by rewrite (_ : \1_ _ = mindic R mf_neq0)//.
  - move=> x Dx.
    rewrite (le_trans (le_f_M _ Dx))// lee_fin.
    rewrite /sfun_f/= mindicE indicE.
    by case: (_ \in _) => //; rewrite ?mulr1 ?mulr0// ler_norm.
by rewrite f_neq0_eq0 mule0 -eq_le => /eqP.
Qed.

(* TODO: too long *)
Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable_fun D f -> \int_ D `|f x| 'd mu[x] = 0 <-> ae_eq D f (cst 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists (D `&` [set x | f x != 0]); split; [exact: emeasurable_neq| |]; last first.
    by move=> t /= /not_implyP [Dt /eqP ft0].
  have muDf : forall a, (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x |]) = 0.
    move=> a a0; apply/eqP; rewrite eq_le measure_ge0 ?andbT; last first.
    move: (@le_integral_abse _ _ mu _ mD _ _ mf a0).
    by rewrite -lee_pdivl_mull// iDf0 mule0 setIC.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[Dt ft0]|[n _ /= [Dt nft]]].
      have [ftoo|ftoo] := eqVneq `|f t| +oo%E.
        by exists 0%N => //; split => //=; rewrite ftoo /= lee_pinfty.
      pose m := `|ceil (fine `|f t|)^-1|%N.
      have ftfin : `|f t|%E \is a fin_num.
        by rewrite fin_numE gt_eqF //= (lt_le_trans _ (abse_ge0 _))// lte_ninfty.
      exists m => //; split => //=.
      rewrite -(@fineK _ `|f t|) // lee_fin -ler_pinv; last 2 first.
        - rewrite inE unitfE fine_eq0 // abse_eq0 ft0/=; apply/lt0R.
          rewrite lt_neqAle abse_ge0 andbT -ge0_fin_numE//.
          by rewrite ftfin andbT eq_sym abse_eq0.
        - by rewrite inE unitfE invr_eq0 pnatr_eq0 /= invr_gt0.
      rewrite invrK /m -addn1 natrD natr_absz ger0_norm; last first.
        by rewrite ceil_ge0// invr_ge0; exact/le0R.
      apply: (@le_trans _ _ ((fine `|f t|)^-1 + 1)%R); first by rewrite ler_addl.
      by rewrite ler_add2r// ceil_ge.
    split => //; apply: contraTN nft => /eqP ->.
    by rewrite abse0 -ltNge lte_fin invr_gt0.
  transitivity (lim (fun n => mu (D `&` [set x | `|f x| >= n.+1%:R^-1%:E]))).
    apply/esym/cvg_lim => //; apply: cvg_mu_inc.
    - move=> i; apply: emeasurable_fun_c_infty => //.
      exact: measurable_fun_comp.
    - apply: measurable_bigcup => i.
      by apply: emeasurable_fun_c_infty => //; exact: measurable_fun_comp.
    - move=> m n mn; apply/subsetPset; apply: setIS => t /=.
      by apply: le_trans; rewrite lee_fin lef_pinv // ?ler_nat // posrE.
  by rewrite (_ : (fun _ => _) = cst 0) ?lim_cst//= funeqE => n /=; rewrite muDf.
pose f_ := fun n x => mine `|f x| n%:R%:E.
have -> : (fun x => `|f x|) = (fun x => lim (f_^~ x)).
  rewrite funeqE => x;apply/esym/cvg_lim => //; apply/cvg_ballP => _/posnumP[e].
  rewrite near_map; near=> n; rewrite /ball /= /ereal_ball /= /f_.
  have [->|fxoo] := eqVneq `|f x|%E +oo.
    rewrite /= (@ger0_norm _ n%:R)// ger0_norm; last first.
      rewrite subr_ge0 ler_pdivr_mulr ?mul1r ?ler_addr//.
      by rewrite {1}(_ : 1 = 1%:R)%R // -natrD add1n.
    rewrite -{1}(@divrr _ (1 + n%:R)%R) ?unitfE; last first.
      by rewrite gt_eqF// {1}(_ : 1 = 1%:R)%R // -natrD add1n.
    rewrite -mulrBl addrK ltr_pdivr_mulr; last first.
      by rewrite {1}(_ : 1 = 1%:R)%R // -natrD add1n.
    rewrite mulrDr mulr1 ltr_spsaddl// -ltr_pdivr_mull// mulr1.
    near: n.
    exists `|ceil (1 + e%:num^-1)|%N => // n /=.
    rewrite -(@ler_nat R); apply: lt_le_trans.
    rewrite natr_absz ger0_norm ?ceil_ge ?ceil_ge0//.
    by rewrite (lt_le_trans _ (ceil_ge _))// ltr_addr.
  have fxn : `|f x| <= n%:R%:E.
    rewrite -(@fineK _ `|f x|); last first.
      by rewrite fin_numE fxoo andbT gt_eqF// (lt_le_trans _ (abse_ge0 _))// ?lte_ninfty.
    rewrite lee_fin.
    near: n.
    exists `|ceil (fine (`|f x|))|%N => // n /=.
    rewrite -(@ler_nat R); apply: le_trans.
    by rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0//; exact/le0R.
  by rewrite min_l// subrr normr0.
transitivity (lim (fun n => \int_ D (f_ n x) 'd mu[x])).
  apply/esym/cvg_lim => //; apply: cvg_monotone_convergence => //.
  - move=> n; apply: emeasurable_fun_min => //; first exact: measurable_fun_comp.
    exact: measurable_fun_cst.
  - by move=> n t Dt; rewrite /f_ lexI abse_ge0 //= lee_fin.
  - move=> t Dt m n mn; rewrite /f_ lexI.
    have [ftm|ftm] := leP `|f t|%E m%:R%:E.
      by rewrite lexx /= (le_trans ftm)// lee_fin ler_nat.
    by rewrite (ltW ftm) /= lee_fin ler_nat.
have ae_eq_f_ n : ae_eq D (f_ n) (cst 0).
  case: Df0 => N [mN muN0 DfN].
  exists N; split => // t /= /not_implyP[Dt fnt0].
  apply: DfN => /=; apply/not_implyP; split => //.
  apply: contra_not fnt0 => ft0.
  by rewrite /f_ ft0 /= normr0 min_l// lee_fin.
have f_bounded n x : D x -> `|f_ n x| <= n%:R%:E.
  move=> Dx; rewrite /f_; have [|_] := leP `|f x| n%:R%:E.
    by rewrite abse_id.
  by rewrite gee0_abs// lee_fin.
have if_0 n : \int_ D `|f_ n x| 'd mu[x] = 0.
  apply: (@ae_eq_integral_abs_bounded _ _ _ n%:R) => //.
    apply: emeasurable_fun_min => //;
      [exact: measurable_fun_comp|exact: measurable_fun_cst].
  exact: f_bounded.
rewrite (_ : (fun _ => _) = (cst 0)) // ?lim_cst// funeqE => n.
rewrite (_ : (fun x => f_ n x) = abse \o f_ n); first exact: if_0.
rewrite funeqE => x /=; rewrite gee0_abs// /f_.
by have [|_] := leP `|f x| n%:R%:E; [by []|rewrite lee_fin].
Unshelve. all: by end_near. Qed.

Lemma integral_abs_eq0 D (N : set T) (mN : measurable N) (f : T -> \bar R) :
  measurable D -> N `<=` D -> mu N = 0 ->
  measurable_fun D f -> \int_ N `|f x| 'd mu[x] = 0.
Proof.
move=> mD ND muN0 mf.
rewrite integral_presfun_ind1//.
rewrite (_ : (fun _ => _) = (fun x => `|f x * (\1_N x)%:E|)); last first.
  rewrite funeqE => t; rewrite abseM //=; congr (_ * _).
  by rewrite ger0_norm.
apply/ae_eq_integral_abs => //.
  apply: emeasurable_funM => //.
  apply: (@measurable_funS _ _ D) => //.
  apply/EFin_measurable_fun.
  apply: (@measurable_funS _ _ setT) => //.
  by rewrite (_ : \1_N = mindic R mN).
exists N; split => // t /= /not_implyP[_].
rewrite indicE.
by have [|] := boolP (t \in N); rewrite ?inE ?mule0.
Qed.

(* TODO: rename; move? *)
Lemma presfun_cplt (N : set T) (mN : measurable N) (f : T -> \bar R) :
  let oneCN := [the {nnsfun T >-> R} of mindic R (measurableC mN)] in
  let oneN := [the {nnsfun T >-> R} of mindic R mN] in
  f = (fun x => f x * (oneCN x)%:E) \+ (fun x => f x * (oneN x)%:E).
Proof.
move=> oneCN oneN; rewrite funeqE => x.
rewrite /oneCN /oneN/= /mindic !indicE.
have [xN|xN] := boolP (x \in N).
  by rewrite mule1 in_setC xN mule0 add0e.
by rewrite in_setC xN mule0 adde0 mule1.
Qed.

Lemma negligible_integrable (D N : set T) (mN : measurable N) (f : T -> \bar R)
  (mD : measurable D) :
  mu N = 0 -> measurable_fun D f -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> muN0 mf.
pose mCN := measurableC mN.
pose oneCN : {nnsfun T >-> R} := [the {nnsfun T >-> R} of mindic R mCN]. (* \1_(~` N) *)
pose oneN : {nnsfun T >-> R} := [the {nnsfun T >-> R} of mindic R mN]. (* \1_N *)
have intone : mu.-integrable D (fun x => f x * (oneN x)%:E).
  split.
    apply: emeasurable_funM=> //; apply/EFin_measurable_fun => //.
    exact: (@measurable_funS _ _ setT).
  (*; first exact: emeasurable_funM_presfun_ind1  xxxx.*)
  (* NB: too long *)
  rewrite (_ : (fun _ => _) = (fun x => `|f x| * (\1_N x)%:E)).
    rewrite -integral_presfun_ind1_setI// (@integral_abs_eq0 D)// ?lte_pinfty//.
    - exact: measurableI.
    - apply: (subset_measure0 _ _ _ muN0) => //.
      exact: measurableI.
  rewrite funeqE => x; rewrite abseM.
  by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
have h1 : mu.-integrable D f <-> mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intf|intCf].
    split.
      apply: emeasurable_funM=> //; apply/EFin_measurable_fun => //.
      exact: (@measurable_funS _ _ setT).
    (* NB: too long *)
    rewrite (_ : (fun _ => _) = (fun x => `|f x| * (\1_(~` N) x)%:E)); last first.
      rewrite funeqE => x; rewrite abseM.
      by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
    rewrite -integral_presfun_ind1_setI//.
    case: intf => _; apply: le_lt_trans.
    by apply: subset_integral => //; [exact: measurableI|exact: measurable_fun_comp].
  split => //; rewrite (presfun_cplt mN f) -/oneCN -/oneN.
  have ? : measurable_fun D (fun x : T => f x * (oneCN x)%:E).
    apply: emeasurable_funM=> //.
    by apply/EFin_measurable_fun; apply: (@measurable_funS _ _ setT).
  have ? : measurable_fun D (fun x : T => f x * (oneN x)%:E).
    apply: emeasurable_funM=> //.
    by apply/EFin_measurable_fun; apply: (@measurable_funS _ _ setT).
  apply: (@le_lt_trans _ _ (\int_ D (`|f x * (oneCN x)%:E| + `|f x * (oneN x)%:E|) 'd mu[x])).
    apply: ge0_le_integral => //.
    - by apply: measurable_fun_comp => //; apply: emeasurable_funD => //.
    - by move=> *; rewrite adde_ge0.
    - apply: emeasurable_funD=> //.
        by apply: measurable_fun_comp => //.
      by apply: measurable_fun_comp => //.
    - by move=> *; rewrite lee_abs_add.
  rewrite ge0_integralD//; last 2 first.
    - by apply: measurable_fun_comp => //.
    - by apply: measurable_fun_comp => //.
  by apply: lte_add_pinfty; [case: intCf|case: intone].
have h2 : mu.-integrable (D `\` N) f <-> mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intCf|intCf].
    split.
      apply: emeasurable_funM=> //; apply/EFin_measurable_fun => //.
      exact: (@measurable_funS _ _ setT).
    (* NB: too long *)
    rewrite (_ : (fun _ => _) = (fun x => `|f x| * (\1_(~` N) x)%:E)); last first.
      rewrite funeqE => x; rewrite abseM.
      by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
    rewrite -integral_presfun_ind1_setI //.
    case: intCf => _; apply: le_lt_trans.
    apply: subset_integral=> //; [exact: measurableI|exact: measurableD|].
    apply: measurable_fun_comp => //.
    by apply: measurable_funS mf => // ? [].
  split.
    move=> mDN A mA.
    rewrite setDE (setIC D) -setIA; apply: measurableI => //.
    exact: mf.
  case: intCf => _ intCf.
  rewrite integral_presfun_ind1_setI//.
  rewrite (_ : (fun _ => _) = (fun x => `|f x| * (\1_(~` N) x)%:E))// in intCf.
  rewrite funeqE => x; rewrite abseM.
  by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
apply (iff_trans h1).
exact: iff_sym.
Qed.

Lemma negligible_integral (D N : set T) (f : T -> \bar R)
  (mN : measurable N) (mD : measurable D) :
  (forall x, D x -> 0 <= f x)%E ->
  mu N = 0 -> measurable_fun D f ->
  \int_ D (f x) 'd mu[x] = \int_ (D `\` N) (f x) 'd mu[x].
Proof.
move=> f0 muN0 mf.
rewrite {1}(presfun_cplt mN f) ge0_integralD//; last 4 first.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
  - apply: emeasurable_funM=> //.
    apply/EFin_measurable_fun=> //.
    by apply: (@measurable_funS _ _ setT)=> //.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
  - apply: emeasurable_funM=> //.
    apply/EFin_measurable_fun=> //.
    by apply: (@measurable_funS _ _ setT)=> //.
rewrite -integral_presfun_ind1_setI//; last exact: measurableC.
rewrite -integral_presfun_ind1_setI// [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite (@eq_integral _ _ mu _ _ (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite (@integral_abs_eq0 D)//; first exact: measurableI.
- by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R)
  (mD : measurable D) : measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) -> ae_eq D f g ->
  \int_ D (f x) 'd mu[x] = \int_ D (g x) 'd mu[x].
Proof.
move=> mf mg f0 g0 [N [mN N0 subN]].
rewrite integral_presfun_ind1// [RHS]integral_presfun_ind1//.
rewrite (negligible_integral mN)//; last 2 first.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
  - apply: emeasurable_funM => //; apply/EFin_measurable_fun.
    by apply: (@measurable_funS _ _ setT) => //; rewrite (_ : \1_D = mindic R mD).
rewrite [RHS](negligible_integral mN)//; last 2 first.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: g0|rewrite lee_fin].
  - apply: emeasurable_funM => //; apply/EFin_measurable_fun.
    by apply: (@measurable_funS _ _ setT) => //; rewrite (_ : \1_D = mindic R mD).
- apply: eq_integral => x.
  rewrite in_setD => /andP[_ xN1].
  apply: contrapT; rewrite indicE; have [xD|xD] := boolP (x \in D).
    rewrite !mule1.
    rewrite notin_set in xN1.
    apply: contra_not xN1 => fxgx; apply subN => /=.
    apply/not_implyP; split => //.
    by rewrite inE in xD.
  by rewrite !mule0.
Qed.

Lemma ae_eq_integral (D : set T) (f g : T -> \bar R)
  (mD : measurable D) : measurable_fun D f -> measurable_fun D g ->
  ae_eq D f g -> integral mu D f = integral mu D g.
Proof.
move=> mf mg /ae_eq_funenng_funennp[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funenng|
                                      exact: emeasurable_fun_funenng].
by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funennp|
                                    exact: emeasurable_fun_funennp].
Qed.

Lemma ae_eq_ind1 (N : set T) : measurable N -> mu N = 0 ->
  ae_eq setT (fun x : T => (\1_(~` N) x)%:E) (cst 1).
Proof.
exists N; split => // x /= /not_implyP[_]; rewrite indicE.
by have [|xN] := boolP (x \in N); [rewrite inE|rewrite in_setC xN].
Qed.

End ae_eq_integral.

Lemma integrableM_ind1 (T : measurableType) (R : realType)
    (mu : {measure set T -> \bar R}) (D N : set T) (f : T -> \bar R) :
  measurable D -> measurable N ->
  mu.-integrable D f ->
  mu.-integrable D (fun x => f x * (\1_N x)%:E)%E.
Proof.
move=> mD mN iTf.
have ? : measurable_fun D (fun x : T => (f x * (\1_N x)%:E)%E).
  apply: emeasurable_funM => //; first by case: iTf.
  apply/EFin_measurable_fun; rewrite (_ : \1_N = [the {nnsfun T >-> R} of mindic R mN])//.
  by apply: (@measurable_funS _ _ setT).
split=> //.
rewrite integralE// lte_pinfty_eq; apply/orP; left.
rewrite fin_numB; apply/andP; split.
  rewrite ge0_fin_numE; last exact: integral_ge0.
  case: iTf => mf; apply: le_lt_trans.
  apply: ge0_le_integral => //.
  - by apply: emeasurable_fun_funenng => //; apply: measurable_fun_comp.
  - exact: measurable_fun_comp.
  - move=> x Dx /=.
    (* TODO: lemma *)
    rewrite /funenng indicE.
    have [xN|xN] := boolP (x \in N).
      by rewrite mule1 le_maxl lexx abse_ge0.
    by rewrite mule0 abse0 maxxx.
rewrite ge0_fin_numE; last exact: integral_ge0.
case: iTf => mf; apply: le_lt_trans.
apply: ge0_le_integral => //.
- apply: emeasurable_fun_funenng => //; apply: emeasurable_funN => //.
  by apply: measurable_fun_comp.
- exact: measurable_fun_comp.
- move=> x Dx /=.
  (* TODO: lemma *)
  rewrite /funennp /= indicE /=.
  have [xN|xN] := boolP (x \in N).
    by rewrite mule1 le_maxl abse_ge0// andbT (le_trans _ (abse_ge0 _))// oppe_le0.
  by rewrite mule0 abse0 oppe0 maxxx.
Qed.

Section integralD.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralD : \int_ D ((f1 \+ f2) x) 'd mu[x] =
  \int_ D (f1 x) 'd mu[x] + \int_ D (f2 x) 'd mu[x].
Proof.
pose A := D `&` [set x | f1 x \is a fin_num].
pose B := D `&` [set x | f2 x \is a fin_num].
have mA : measurable A by apply emeasurable_fin_num => //; case: if1.
have mB : measurable B by apply emeasurable_fin_num => //; case: if2.
have mAB : measurable (A `&` B) by apply: measurableI.
pose g1 x := (fine (f1 x) * \1_(A `&` B) x)%R.
pose g2 x := (fine (f2 x) * \1_(A `&` B) x)%R.
have ig1 : mu.-integrable D (EFin \o g1).
  rewrite (_ : _ \o _ = f1 \* (EFin \o \1_(A `&` B))) //.
    exact: integrableM_ind1.
  rewrite funeqE /g1 => x /=.
  rewrite indicE; have [|] := boolP (x \in A `&` B); last by rewrite mulr0 mule0.
  rewrite !in_setI => /andP[/andP[]].
  rewrite inE /= => f1xfin xD /andP[].
  rewrite inE /= => f2xfin _.
  rewrite mule1 mulr1 fineK//.
  by rewrite inE in xD.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \* (EFin \o \1_(A `&` B))) //.
    exact: integrableM_ind1.
  rewrite funeqE /g2 /= => x /=.
  rewrite indicE; have [|] := boolP (x \in A `&` B); last by rewrite mulr0 mule0.
  rewrite !in_setI => /andP[/andP[]].
  rewrite inE/= => xD f1xfin /andP[].
  rewrite inE /= => _ f2xfin.
  rewrite mule1 mulr1 fineK//.
  by rewrite inE in f2xfin.
transitivity (\int_ D ((EFin \o (g1 \+ g2)%R) x) 'd mu[x]).
  apply ae_eq_integral => //.
  - by apply: emeasurable_funD => //; [case: if1|case: if2].
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    by apply: emeasurable_funD => //; [case: ig1|case: ig2].
  - have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split.
    + exact: measurableU.
    + by rewrite null_set_setU.
    + rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /g2 EFinD 2!EFinM fineK// fineK// indicE.
      have [|] := boolP (x \in A `&` B); first by rewrite 2!mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx)/= notin_set/=.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// integralD_EFin//.
  congr (_ + _).
  + apply ae_eq_integral => //; [by case: ig1|by case: if1|].
    have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split.
    * exact: measurableU.
    * by rewrite null_set_setU.
    * rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /= EFinM fineK// indicE.
      have [|] := boolP (x \in A `&` B); first by rewrite mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx) /= notin_set.
  + apply ae_eq_integral => //;[by case: ig2|by case: if2|].
    have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split.
    * exact: measurableU.
    * by rewrite null_set_setU.
    * rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /= EFinM fineK// indicE.
      have [|] := boolP (x \in A `&` B); first by rewrite mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx) /= notin_set.
Qed.

End integralD.

Section integralB.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralB : \int_ D ((f1 \- f2) x) 'd mu[x] =
                  \int_ D (f1 x) 'd mu[x] - \int_ D (f2 x) 'd mu[x].
Proof.
rewrite -[in RHS](@integralN _ _ _ _ f2); last exact: integrable_add_def.
by rewrite -[in RHS]integralD//; exact: integrableN.
Qed.

End integralB.

Section ae_measurable_fun.
Variables (T : measurableType) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Hypothesis cmu : measure_is_complete mu.
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma ae_measurable_fun D f g :
  ae_eq mu D f g -> measurable_fun D f -> measurable_fun D g.
Proof.
move=> [N [mN N0 subN]] mf B mB mD.
apply: (measurability (ErealGenOInfty.measurableE R)) => // _ [_ [x ->] <-].
rewrite [X in measurable X](_ : _ = D `&` ~` N `&` (f @^-1` `]x, +oo[)
    `|` (D `&` N `&` g @^-1` `]x, +oo[)); last first.
  rewrite /preimage.
  apply/seteqP; split=> [y /= [Dy gyxoo]|y /= [[[Dy Ny] fyxoo]|]].
  - have [->|fgy] := eqVneq (f y) (g y).
      have [yN|yN] := boolP (y \in N).
        by right; split => //; rewrite inE in yN.
      by left; split => //; rewrite notin_set in yN.
    by right; split => //; split => //; apply: subN => /= /(_ Dy); exact/eqP.
  - split => //; have [<-//|fgy] := eqVneq (f y) (g y).
    by exfalso; apply/Ny/subN => /= /(_ Dy); exact/eqP.
  - by move=> [[]].
apply: measurableU.
- rewrite setIAC; apply: measurableI; last exact/measurableC.
  exact/mf/emeasurable_itv_bnd_pinfty.
- by apply: cmu; exists N; split => //; rewrite setIAC; apply: subIset; right.
Qed.

End ae_measurable_fun.

(* TODO: move *)
Lemma abse_continuous (R : realFieldType) : continuous (@abse R).
Proof.
case=> [r|A /= [r [rreal rA]]|A /= [r [rreal rA]]]/=.
- exact/(cvg_comp (@norm_continuous _ [normedModType R of R^o] r)).
- by exists r; split => // y ry; apply: rA; rewrite (lt_le_trans ry)// lee_abs.
- exists (- r)%R; rewrite realN; split => // y; rewrite EFinN -lte_oppr => yr.
  by apply: rA; rewrite (lt_le_trans yr)// -abseN lee_abs.
Qed.

Lemma cvg_abse (T : topologicalType) (R : realFieldType) (F : set (set T)) f
    (a : \bar R) : Filter F ->
  f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Proof. by move=> FF; apply: continuous_cvg => //; apply: abse_continuous. Qed.

Lemma is_cvg_abse (T : topologicalType) (R : realFieldType) (F : set (set T))
    (f : T -> \bar R) : Filter F ->
  cvg (f @ F) -> cvg ((abse \o f : T -> \bar R) @ F).
Proof. move=> FF; have := cvgP _ (cvg_abse FF _); apply. Qed.

Lemma ereal_cvgB (R : realFieldType) (f g : (\bar R)^nat) a b :
  (a +? - b -> f --> a -> g --> b -> f \- g --> a - b)%E.
Proof. by move=> ab fa gb; apply: ereal_cvgD => //; exact: ereal_cvgN. Qed.

Lemma ereal_cvg_sub0' (R : realFieldType) (f : (\bar R)^nat) (k : \bar R) :
  k \is a fin_num -> f --> k -> (fun x => f x - k)%E --> 0%E.
Proof.
move: k => [k _ fk| |]//.
rewrite -(@subee _ k%:E)//.
apply: ereal_cvgB => //.
exact: cvg_cst.
Qed.

Section dominated_convergence_lemma.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f_ : (T -> \bar R)^nat.
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Variable f : T -> \bar R.
Hypothesis f_f : forall x, D x -> f_ ^~ x --> f x.
Variable g : T -> \bar R.
Hypothesis fing : forall x, D x -> g x \is a fin_num.
Hypothesis ig : mu.-integrable D g.
Hypothesis absfg : forall n x, D x -> `|f_ n x| <= g x.

Let g0 x : D x -> 0 <= g x.
Proof. by move=> Dx; rewrite (le_trans _ (@absfg O _ Dx))// lee_fin. Qed.

Let mf : measurable_fun D f.
Proof. exact: (emeasurable_fun_cvg mf_ f_f). Qed.

Local Lemma dominated_integrable : mu.-integrable D f.
Proof.
split => //; have Dfg x : D x -> `| f x | <= g x.
  move=> Dx; have /(@cvg_lim _) <- // : `|f_ n x| @[n --> \oo] --> `|f x|.
    by apply: cvg_abse => //; exact: f_f.
  apply: ereal_lim_le => //.
  - by apply: is_cvg_abse; apply/cvg_ex; eexists; exact: f_f.
  - by apply: nearW => n; apply: absfg.
move: ig => [mg]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- exact: measurable_fun_comp.
- by move=> x Dx /=; rewrite (gee0_abs (g0 Dx)); exact: Dfg.
Qed.

Let g_ n x := `|f_ n x - f x|.

Let cvg_g_ x : D x -> g_ ^~ x --> 0.
Proof.
move=> Dx; rewrite -abse0; apply: cvg_abse.
move: (f_f Dx); case: (f x) => [r|/=|/=].
- by apply: ereal_cvg_sub0' => //; rewrite -hfx; exact: f_f.
- have gx1 : (0 < fine (g x) + 1)%R .
    by rewrite (@le_lt_trans _ _ (fine (g x))) ?ltr_addl//; exact/le0R/g0.
  move/ereal_cvgPpinfty/(_ _ gx1) => [n _]/(_ _ (leqnn n)) h.
  have : (fine (g x) + 1)%:E <= g x.
    by rewrite (le_trans h)// (le_trans _ (absfg n Dx))// lee_abs.
  case: (g x) (fing Dx) => [r _| |]//.
  by rewrite lee_fin /= leNgt ltr_addl// ltr01.
- have gx1 : (- (fine (g x) + 1) < 0)%R.
    by rewrite ltr_oppl oppr0 ltr_spaddr//; exact/le0R/g0.
  move/ereal_cvgPninfty/(_ _ gx1) => [n _]/(_ _ (leqnn n)) h.
  have : (fine (g x) + 1)%:E <= g x.
    move: h; rewrite EFinN lee_oppr => /le_trans ->//.
    by rewrite (le_trans _ (absfg n Dx))// -abseN lee_abs.
  case: (g x) (fing Dx) => [r _| |]//.
  by rewrite lee_fin /= leNgt ltr_addl// ltr01.
Qed.

Let gg_ n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof.
move=> Dx; rewrite subre_ge0; last by rewrite fin_numM// fing.
rewrite -(fineK (fing Dx)) -EFinM mulr_natl mulr2n /g_.
rewrite (le_trans (lee_abs_sub _ _))// [in X in _ <= X]EFinD lee_add//.
  by rewrite fineK// ?fing// absfg.
have f_fx : `|(f_ n x)| @[n --> \oo] --> `|f x| by apply: cvg_abse; exact: f_f.
move/cvg_lim : (f_fx) => <-//.
apply: ereal_lim_le; first by apply/cvg_ex; eexists; exact: f_fx.
by apply: nearW => k; rewrite fineK ?fing//; apply: absfg.
Qed.

Let mgg n : measurable_fun D (fun x => 2%:E * g x - g_ n x).
Proof.
apply/emeasurable_funB => //; first by apply: emeasurable_funeM; case: ig.
by apply/measurable_fun_comp => //; exact: emeasurable_funB.
Qed.

Let gg_ge0 n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof. by move=> Dx; rewrite gg_. Qed.

Local Lemma dominated_cvg0 : (fun n => \int_ D (g_ n x) 'd mu[x]) --> 0.
Proof.
have := fatou mu mD mgg gg_ge0.
rewrite [X in X <= _ -> _](_ : _ = \int_ D (2%:E * g x) 'd mu[x]); last first.
  apply: eq_integral => t; rewrite inE => Dt.
  rewrite elim_inf_shift//; last by rewrite fin_numM// fing.
  rewrite is_cvg_elim_infE//; last first.
    by apply: ereal_is_cvgN; apply/cvg_ex; eexists; exact: cvg_g_.
  rewrite [X in _ + X](_ : _ = 0) ?adde0//; apply/cvg_lim => //.
  by rewrite -(oppe0); apply: ereal_cvgN; exact: cvg_g_.
have i2g : \int_ D (2%:E * g x) 'd mu[x] < +oo.
  rewrite integralM// lte_mul_pinfty// ?lee_fin//; case: ig => _.
  apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply eq_integral => t Dt; rewrite gee0_abs// g0//; rewrite inE in Dt.
have ? : \int_ D (2%:E * g x) 'd mu[x] \is a fin_num.
  by rewrite ge0_fin_numE// integral_ge0// => x Dx; rewrite mule_ge0 ?lee_fin ?g0.
rewrite [X in _ <= X -> _](_ : _ = \int_ D (2%:E * g x) 'd mu[x] + -
    elim_sup (fun n => \int_ D (g_ n x) 'd mu[x])); last first.
  rewrite (_ : (fun _ => _) = (fun n => \int_ D (2%:E * g x) 'd mu[x] +
      \int_ D (- g_ n x) 'd mu[x])); last first.
    rewrite funeqE => n; rewrite integralB//.
    - by rewrite -integral_ge0N// => x Dx//; rewrite /g_.
    - exact: integrableK.
    - have integrable_normfn : mu.-integrable D (abse \o f_ n).
        apply: le_integrable ig => //.
        - exact: measurable_fun_comp.
        - by move=> x Dx /=; rewrite abse_id (le_trans (absfg _ Dx))// lee_abs.
      suff: mu.-integrable D (fun x => `|f_ n x| + `|f x|).
        apply: le_integrable => //.
        - by apply: measurable_fun_comp => //; exact: emeasurable_funB.
        - move=> x Dx.
          by rewrite /g_ abse_id (le_trans (lee_abs_sub _ _))// lee_abs.
      apply: integrableD; [by []| by []|].
      apply: le_integrable dominated_integrable => //.
      - exact: measurable_fun_comp.
      - by move=> x Dx; rewrite /= abse_id.
  rewrite elim_inf_shift // -elim_infN; congr (_ + elim_inf _).
  by rewrite funeqE => n /=; rewrite -integral_ge0N// => x Dx; rewrite /g_.
rewrite addeC -lee_subl_addr// subee// lee_oppr oppe0 => lim_ge0.
by apply/elim_sup_le0_cvg0 => // n; rewrite integral_ge0// => x _; rewrite /g_.
Qed.

Local Lemma dominated_cvg :
  (fun n => \int_ D (f_ n x) 'd mu[x]) --> \int_ D (f x) 'd mu[x].
Proof.
have h n : `| \int_ D (f_ n x) 'd mu[x] - \int_ D (f x) 'd mu[x] |
    <= \int_ D (g_ n x) 'd mu[x].
  rewrite -(integralB _ _ dominated_integrable)//; last first.
    by apply: le_integrable ig => // x Dx /=; rewrite (gee0_abs (g0 Dx)) absfg.
  by apply: le_abse_integral => //; exact: emeasurable_funB.
suff: (fun n => `| \int_ D (f_ n x) 'd mu[x] - \int_ D (f x) 'd mu[x]|) --> 0.
   move/ereal_cvg_abs0/ereal_cvg_sub0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   case: dominated_integrable => ?; apply: le_lt_trans.
   by apply: (le_trans _ (@le_abse_integral _ _ mu D f mD _)).
apply: (@ereal_squeeze _ (cst 0) _ (fun n => \int_ D (g_ n x) 'd mu[x])).
- by apply: nearW => n; rewrite abse_ge0//=; exact: h.
- exact: cvg_cst.
- exact: dominated_cvg0.
Qed.

End dominated_convergence_lemma.

Section dominated_convergence_theorem.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType).
Variables mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f_ : (T -> \bar R)^nat.
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Variable f : T -> \bar R.
Hypothesis mf : measurable_fun D f.
Hypothesis f_f : {ae mu, forall x, D x -> f_ ^~ x --> f x}.
Variable g : T -> \bar R.
Hypothesis ig : mu.-integrable D g.
Hypothesis absfg : {ae mu, forall x n, D x -> `|f_ n x| <= g x}.

Let g_ n x := `|f_ n x - f x|.

Let ind1 N x : \bar R := (\1_(D `\` N) x)%:E.

Theorem dominated_convergence : [/\ mu.-integrable D f,
  (fun n => \int_ D (g_ n x) 'd mu[x]) --> 0 &
  (fun n => \int_ D (f_ n x) 'd mu[x]) --> \int_ D (f x) 'd mu[x]].
Proof.
have [N1 [mN1 N10 subN1]] := f_f.
have [N2 [mN2 N20 subN2]] := absfg.
have [N3 [mN3 N30 subN3]] := integrable_ae mD ig.
pose N := N1 `|` N2 `|` N3.
have mN : measurable N by apply: measurableU => //; exact: measurableU.
have N0 : mu N = 0.
  by rewrite null_set_setU// ?null_set_setU//; exact: measurableU.
pose u := f \* ind1 N.
pose v := g \* ind1 N.
pose u_ := fun n => f_ n \* ind1 N.
have u_u x : D x -> u_ ^~ x --> u x.
  move=> Dx; rewrite /u_ /u /ind1 indicE in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N).
    rewrite mule0/= [X in X --> _](_ : _ = cst 0)//; first exact: cvg_cst.
    by apply/funext => n; rewrite mule0.
  rewrite mule1 [X in X --> _](_ : _ = f_ ^~ x); last first.
    by apply/funext => n; rewrite mule1.
  apply: contraPP (xN) => h.
  apply/negP; rewrite negbK inE; left; left.
  by apply: subN1 => /= /(_ Dx); apply: contra_not h => h.
have u_v n x : D x -> `|u_ n x| <= v x.
  move=> Dx; rewrite /u_ /v /ind1 indicE in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N); first by rewrite mule0/= normr0 mule0.
  rewrite !mule1; apply: contrapT => fg.
  move: xN; apply/negP; rewrite negbK inE; left; right.
  by apply: subN2 => /= /(_ n Dx).
have ? : measurable_fun D (\1_(D `\` N) : T -> R).
  apply: (@measurable_funS _ _ setT) => //.
  by rewrite (_ : \1_ _ = mindic R (measurableD mD mN)).
have mu_ n : measurable_fun D (u_ n).
  by apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
have iv : mu.-integrable D v.
  split.
    apply: emeasurable_funM => //; first by case: ig.
    by apply: measurable_fun_comp => //.
  case: ig => _; apply: le_lt_trans; apply: ge0_le_integral => //.
    apply: measurable_fun_comp => //; apply: emeasurable_funM => //.
      by case: ig.
    by apply: measurable_fun_comp => //.
    apply: measurable_fun_comp => //.
    by case: ig.
  move=> x Dx; rewrite /v /ind1 indicE in_setD mem_set//=.
  by case: (x \in N); rewrite ?mule1// mule0 abse0.
have finv x : D x -> v x \is a fin_num.
  move=> Dx.
  rewrite /v /ind1 indicE in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N); first by rewrite mule0.
  rewrite mule1.
  apply: contrapT => fing.
  move: xN; apply/negP; rewrite negbK inE; right.
  by apply: subN3 => /= /(_ Dx).
split.
- split => //.
  have : mu.-integrable D u.
    exact: (@dominated_integrable _ _ _ _ _ u_ _ u _ v).
  move=> [?]; apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/ae_eq_integral => //.
    exact: measurable_fun_comp.
    exact: measurable_fun_comp.
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x Nx Dx.
  by rewrite /= /u /= /ind1 indicE in_setD mem_set//= memNset// mule1.
- have := @dominated_cvg0 _ _ _ _ mD _ mu_ _ u_u _ finv iv u_v.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //.
  apply/funext => n; apply ae_eq_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_funB => //.
    by apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
  + by rewrite /g_; apply: measurable_fun_comp => //; exact: emeasurable_funB.
  + exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /u_ /u /ind1 indicE in_setD mem_set//= memNset// !mule1.
- have := @dominated_cvg _ _ _ _ mD _ mu_ _ u_u _ finv iv u_v.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //; last first.
    apply/funext => n; apply ae_eq_integral => //.
    exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /u_ /u /ind1 indicE in_setD mem_set//= memNset// !mule1.
  set Y := (X in _ -> _ --> X); rewrite [X in _ --> X -> _](_ : _ = Y) //.
  apply ae_eq_integral => //.
    by apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
  by rewrite /u_ /u /ind1 indicE in_setD mem_set//= memNset// !mule1.
Qed.

End dominated_convergence_theorem.

(* TODO: move to measure.v *)
Section measure_restr.
Variables (T : measurableType) (R : realType) (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).

Definition measure_restr' (X : set _) : \bar R := mu (X `&` D).

Local Lemma measure_restr'0 : measure_restr' set0 = 0%E.
Proof. by rewrite /measure_restr' set0I measure0. Qed.

Local Lemma measure_restr'_ge0 (A : set _) : (0 <= measure_restr' A)%E.
Proof.
by rewrite /measure_restr'; apply: measure_ge0; exact: measurableI.
Qed.

Local Lemma measure_restr'_sigma_additive : semi_sigma_additive measure_restr'.
Proof.
move=> F mF tF mU; pose F' i := F i `&` D.
have mF' i : measurable (F' i) by apply: measurableI.
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

(******************************************************************************)
(* * product measure                                                          *)
(******************************************************************************)

(* NB: not used *)
Lemma integrable_funenng (T1 T2 : measurableType) (R : realType) (pt2 : T2)
  (m2 : {measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) x :
  m2.-integrable setT (fun y => f (x, y)) ->
  m2.-integrable setT (fun y => f^\+ (x, y))%E.
Proof.
move=> [mfx fxoo]; split; first exact/emeasurable_fun_funenng.
apply: le_lt_trans fxoo; apply: ge0_le_integral => //.
- by apply: measurable_fun_comp => //; exact: emeasurable_fun_funenng.
- by apply: measurable_fun_comp.
- by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

(* NB: not used *)
(*Lemma integrable_funennp (T1 T2 : measurableType) (R : realType) (pt2 : T2)
  (m2 : {measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) x :
  m2.-integrable setT (fun y => f (x, y)) ->
  m2.-integrable setT (fun y => f^\- (x, y)).
Proof.
move=> [mfx fxoo]; split; first exact/emeasurable_fun_funennp.
apply: le_lt_trans fxoo; apply: ge0_le_integral => //.
- by apply: measurable_fun_comp => //; exact: emeasurable_fun_funennp.
- by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.
*)
Section section.
Variables (T1 T2 : Type).
Implicit Types (A : set (T1 * T2)) (x : T1) (y : T2).

Definition xsection A x := [set y | (x, y) \in A].

Definition ysection A y := [set x | (x, y) \in A].

Lemma xsection0 x : xsection set0 x = set0.
Proof. by rewrite predeqE /xsection => y; split => //=; rewrite inE. Qed.

Lemma ysection0 y : ysection set0 y = set0.
Proof. by rewrite predeqE /ysection => x; split => //=; rewrite inE. Qed.

Lemma in_xsectionM X1 X2 x : x \in X1 -> xsection (X1 `*` X2) x = X2.
Proof.
move=> xX1; rewrite /xsection predeqE => y /=; split; rewrite inE.
  by move=> [].
by move=> X2y; split => //=; rewrite inE in xX1.
Qed.

Lemma in_ysectionM X1 X2 y : y \in X2 -> ysection (X1 `*` X2) y = X1.
Proof.
move=> yX2; rewrite /ysection predeqE => x /=; split; rewrite inE.
  by move=> [].
by move=> X1x; split => //=; rewrite inE in yX2.
Qed.

Lemma notin_xsectionM X1 X2 x : x \notin X1 -> xsection (X1 `*` X2) x = set0.
Proof.
move=> xX1; rewrite /xsection /= predeqE => y; split => //.
by rewrite /xsection/= inE => -[] /=; rewrite notin_set in xX1.
Qed.

Lemma notin_ysectionM X1 X2 y : y \notin X2 -> ysection (X1 `*` X2) y = set0.
Proof.
move=> yX2; rewrite /xsection /= predeqE => x; split => //.
by rewrite /ysection/= inE => -[_]; rewrite notin_set in yX2.
Qed.

Lemma xsection_bigcup (F : nat -> set (T1 * T2)) x :
  xsection (\bigcup_n F n) x = \bigcup_n xsection (F n) x.
Proof.
rewrite predeqE /xsection => y; split => [|[n _]] /=; rewrite inE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite inE.
by move=> Fnxy; rewrite inE; exists n.
Qed.

Lemma ysection_bigcup (F : nat -> set (T1 * T2)) y :
  ysection (\bigcup_n F n) y = \bigcup_n ysection (F n) y.
Proof.
rewrite predeqE /ysection => x; split => [|[n _]] /=; rewrite inE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite inE.
by move=> Fnxy; rewrite inE; exists n.
Qed.

Lemma trivIset_xsection (F : nat -> set (T1 * T2)) x : trivIset setT F ->
  trivIset setT (fun n => xsection (F n) x).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /xsection /= predeqE => y; split => //= -[]; rewrite !inE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma trivIset_ysection (F : nat -> set (T1 * T2)) y : trivIset setT F ->
  trivIset setT (fun n => ysection (F n) y).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /ysection /= predeqE => x; split => //= -[]; rewrite !inE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma le_xsection x : {homo xsection ^~ x : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY y; rewrite /xsection /= 2!inE => /XY. Qed.

Lemma le_ysection y : {homo ysection ^~ y : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY x; rewrite /ysection /= 2!inE => /XY. Qed.

Lemma xsectionD X Y x : xsection (X `\` Y) x = xsection X x `\` xsection Y x.
Proof.
rewrite predeqE /xsection /= => y; split; last by rewrite 3!inE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!inE.
Qed.

Lemma ysectionD X Y y : ysection (X `\` Y) y = ysection X y `\` ysection Y y.
Proof.
rewrite predeqE /ysection /= => x; split; last by rewrite 3!inE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!inE.
Qed.

End section.

Section measurable_section.
Variables (T1 T2 : measurableType) (R : realType).
Implicit Types (A : set (T1 * T2)) (x : T1).

Lemma mem_set_pair1 x y A :
  (y \in [set y' | (x, y') \in A]) = ((x, y) \in A).
Proof. by apply/idP/idP => [|]; [rewrite inE|rewrite !inE /= inE]. Qed.

Lemma mem_set_pair2 x y A :
  (x \in [set x' | (x', y) \in A]) = ((x, y) \in A).
Proof. by apply/idP/idP => [|]; [rewrite inE|rewrite 2!inE /= inE]. Qed.

Lemma measurable_xsection A x : measurable A -> measurable (xsection A x).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o indic_nnsfun R mA.
have mf : measurable_fun setT f by apply/EFin_measurable_fun/measurable_funP.
have _ : (fun y => (y \in xsection A x)%:R%:E) = f \o (fun y => (x, y)).
  rewrite funeqE => y /=; rewrite /xsection /f.
  by rewrite /= /mindic indicE/= mem_set_pair1.
have -> : xsection A x = (fun y => f (x, y)) @^-1` [set 1%E].
  rewrite predeqE => y; split; rewrite /xsection /preimage /= /f.
    by rewrite /= /mindic indicE/= => ->.
  rewrite /= /mindic indicE.
  by case: (_ \in _) => //= -[] /eqP; rewrite eq_sym oner_eq0.
rewrite -(setTI (_ @^-1` _)).
by apply: measurable_fun_prod1 => //; exact: emeasurable_set1.
Qed.

Lemma measurable_ysection A y : measurable A -> measurable (ysection A y).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o indic_nnsfun R mA.
have mf : measurable_fun setT f by apply/EFin_measurable_fun/measurable_funP.
have _ : (fun x => (x \in ysection A y)%:R%:E) = f \o (fun x => (x, y)).
  rewrite funeqE => x /=; rewrite /ysection /f.
  by rewrite /= /mindic indicE mem_set_pair2.
have -> : ysection A y = (fun x => f (x, y)) @^-1` [set 1%E].
  rewrite predeqE => x; split; rewrite /ysection /preimage /= /f.
    by rewrite /= /mindic indicE => ->.
  rewrite /= /mindic indicE.
  by case: (_ \in _) => //= -[] /eqP; rewrite eq_sym oner_eq0.
rewrite -(setTI (_ @^-1` _)).
by apply: measurable_fun_prod2 => //; exact: emeasurable_set1.
Qed.

End measurable_section.

Section ndseq_closed_B.
Variables (T1 T2 : measurableType) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (pt2 : T2) (m2 : {measure set T2 -> \bar R}).
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
  - move=> m n mn; apply/subsetPset => y; rewrite /xsection/= !inE.
    by have /subsetPset FmFn := ndF _ _ mn; exact: FmFn.
apply: (@emeasurable_fun_cvg _ _ _ (phi \o F) _ _) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: phiF.
Qed.
End xsection.

Section ysection.
Variables (m1 : {measure set T1 -> \bar R}).
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
  - move=> m n mn; apply/subsetPset => y; rewrite /ysection/= !inE.
    by have /subsetPset FmFn := ndF _ _ mn; exact: FmFn.
apply: (@emeasurable_fun_cvg _ _ _ (psi \o F) _ _) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: psiF.
Qed.
End ysection.

End ndseq_closed_B.

Section measurable_prod_subset.
Variables (T1 T2 : measurableType) (R : realType).
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
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT.
  by exists setT => //; exists setT => //; rewrite setMTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : phi (X1 `*` X2) = (fun x => m2 X2 * (\1_X1 x)%:E)%E.
    rewrite funeqE => x.
    rewrite indicE /m2 measure_restrE.
    rewrite /phi /m2 [measure_restr]lock /= -lock measure_restrE.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionM.
    by rewrite mule0 notin_xsectionM// set0I measure0.
  apply: emeasurable_funeM => //; apply/EFin_measurable_fun.
  by rewrite (_ : \1_ _ = mindic R mX1).
have monoB : is_monotone_class setT B.
  split => //.
  - exact: CB.
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
    exact: emeasurable_funB.
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

Lemma measurable_prod_subset_ysection
    (m1_bounded : exists M, forall X, measurable X -> (m1 X < M%:E)%E) :
  @measurable (prod_measurableType T1 T2) `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in @measurable T1 & A2 in @measurable T2].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setMTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : psi (X1 `*` X2) = (fun x => m1 X1 * (\1_X2 x)%:E)%E.
    rewrite funeqE => y.
    rewrite /m1 measure_restrE indicE.
    rewrite /psi /m1 [measure_restr]lock /= -lock measure_restrE.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionM.
    by rewrite mule0 notin_ysectionM// set0I measure0.
  apply: emeasurable_funeM => //; apply/EFin_measurable_fun.
  by rewrite (_ : \1_ _ = mindic R mX2).
have monoB : is_monotone_class setT B.
  split=> //.
  - exact: CB.
  - move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
    have -> : psi (X `\` Y) = (fun x => psi X x - psi Y x)%E.
      rewrite funeqE => y; rewrite /psi.
      rewrite [m1]lock /= -lock ysectionD measureD; last 3 first.
        + exact: measurable_ysection.
        + exact: measurable_ysection.
        + move: m1_bounded => [M m1M].
          rewrite (lt_le_trans (m1M (ysection X y) _))// ?lee_pinfty//.
          exact: measurable_ysection.
      by rewrite setIidr//; exact: le_ysection.
    exact: emeasurable_funB.
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
Variables (T1 T2 : measurableType) (R : realType).
Variables (m2 : {measure set T2 -> \bar R}).
Hypothesis sf_m2 : sigma_finite setT m2.
Implicit Types A : set (T1 * T2).

Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection A : A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A.
suff : @measurable (prod_measurableType T1 T2) `<=` B.
  by move=> + A; rewrite inE => /[apply] -[].
move/sigma_finiteP : sf_m2 => [F F_T [F_nd F_oo]].
move=> X mX.
have -> : X = \bigcup_n (X `&` (setT `*` F n)).
  by rewrite -setI_bigcupr -setM_bigcupr -F_T setMTT setIT.
apply: xsection_ndseq_closed_B.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSM => //.
  exact/subsetPset/F_nd.
move=> n.
rewrite -/B.
pose m2' : {measure set _ -> \bar R} := measure_restr m2 (F_oo n).1.
have m2'_bounded : exists M, forall X, measurable X -> (m2' X < M%:E)%E.
  exists (fine (m2' (F n)) + 1) => Y mY.
  rewrite [in X in (_ < X)%E]EFinD (le_lt_trans _ (lte_addl _ _))//; last first.
    by rewrite lte_fin.
  rewrite fineK; last first.
    rewrite ge0_fin_numE.
      by rewrite /m2' measure_restrE setIid//; have [] := F_oo n.
    by rewrite measure_ge0//; have [] := F_oo n.
  rewrite /m2' !measure_restrE setIid; apply: le_measure => //.
    by rewrite inE /=; apply: measurableI => //; have [] := F_oo n.
  by rewrite inE /=; have [] := F_oo n.
pose phi' A := m2' \o xsection A.
pose B' := [set A | measurable A /\ measurable_fun setT (phi' A)].
have subset_B' : @measurable (prod_measurableType T1 T2) `<=` B'.
  exact: measurable_prod_subset_xsection.
split=> [|Y mY].
  apply: measurableI => //; apply: measurableM => //.
  by have [] := F_oo n.
have := subset_B' X mX.
rewrite /B' /= => -[_] /(_ Y mY).
have ->// : phi' X = (fun x => m2 [set y | (x, y) \in X `&` setT `*` F n]).
rewrite funeqE => x /=; congr (m2 _).
rewrite predeqE => y; split => [[]|].
  by rewrite /xsection /= inE => Xxy Fny; rewrite inE.
by rewrite /xsection /= !inE => -[] Xxy /= [_].
Qed.

End measurable_fun_xsection.

Section measurable_fun_ysection.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}).
Hypothesis sf_m1 : sigma_finite setT m1.
Implicit Types A : set (T1 * T2).

Let phi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection A : A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A.
suff : @measurable (prod_measurableType T1 T2) `<=` B.
  by move=> + A; rewrite inE => /[apply] -[].
move/sigma_finiteP : sf_m1 => [F F_T [F_nd F_oo]].
move=> X mX.
have -> : X = \bigcup_n (X `&` (F n `*` setT)).
  by rewrite -setI_bigcupr -setM_bigcupl -F_T setMTT setIT.
apply: ysection_ndseq_closed_B.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSM => //.
  exact/subsetPset/F_nd.
move=> n.
rewrite -/B.
pose m1' : {measure set _ -> \bar R} := measure_restr m1 (F_oo n).1.
have m1'_bounded : exists M, forall X, measurable X -> (m1' X < M%:E)%E.
  exists (fine (m1' (F n)) + 1) => Y mY.
  rewrite [in X in (_ < X)%E]EFinD (le_lt_trans _ (lte_addl _ _))//; last first.
    by rewrite lte_fin.
  rewrite fineK; last first.
    rewrite ge0_fin_numE.
      by rewrite /m1' measure_restrE setIid//; have [] := F_oo n.
    by rewrite measure_ge0//; have [] := F_oo n.
  rewrite /m1' !measure_restrE setIid; apply: le_measure => //.
    by rewrite inE /=; apply: measurableI => //; have [] := F_oo n.
  by rewrite inE /=; have [] := F_oo n.
pose psi' A := m1' \o ysection A.
pose B' := [set A | measurable A /\ measurable_fun setT (psi' A)].
have subset_B' : @measurable (prod_measurableType T1 T2) `<=` B'.
  exact: measurable_prod_subset_ysection.
split=> [|Y mY].
  apply: measurableI => //; apply: measurableM => //.
  by have [] := F_oo n.
have := subset_B' X mX.
rewrite /B' /= => -[_] /(_ Y mY).
have ->// : psi' X = (fun y => m1 [set x | (x, y) \in X `&` F n `*` setT]).
rewrite funeqE => y /=; congr (m1 _).
rewrite predeqE => x; split => [[]|].
  by rewrite /ysection /= inE => Xxy Fny; rewrite inE.
by rewrite /ysection /= !inE => -[] Xxy /= [].
Qed.

End measurable_fun_ysection.

Section product_measure1.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Let m A := \int ((m2 \o xsection A) x) 'd m1[x].

Let m0 : m set0 = 0%E.
Proof.
rewrite /m (_ : _ \o _ = cst 0)%E ?integral0// funeqE => x /=.
by rewrite xsection0 measure0.
Qed.

Let m_ge0 A : (0 <= m A)%E.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_xsection.
Qed.

Let m_sigma_additive : semi_sigma_additive m.
Proof.
move=> F mF tF mUF.
have -> : m (\bigcup_n F n) = \sum_(n <oo) (m (F n)).
  transitivity (\int (\sum_(n <oo) m2 (xsection (F n) x)) 'd m1[x]).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => x.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= xsection_bigcup.
    (*apply: (@measure_sigma_additive _ _ _ _ _ (trivIset_xsection tF)).
    by move=> i; apply: measurable_xsection.*) admit.
  rewrite integral_sum //.
  - by move=> n; apply: measurable_fun_xsection => //; rewrite inE.
(*  - by move=> n x _; exact/measure_ge0/measurable_xsection.*)
suff /cvg_ex[l cl] : cvg (fun n => (\sum_(i < n) m (F i))%E).
  (*by move: (cl) => /cvg_lim; rewrite -lim_mkord => ->.*) admit.
under eq_fun do rewrite -(big_mkord xpredT (m \o F)).
by apply: is_cvg_ereal_nneg_natsum => n _; apply: integral_ge0 => // x _.
(*exact/measure_ge0/measurable_xsection.*)
Admitted.

Definition product_measure1 : {measure set (T1 * T2) -> \bar R} :=
  Measure.Pack _ (Measure.Axioms m0 m_ge0 m_sigma_additive).

End product_measure1.

Section product_measure1E.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Lemma product_measure1E (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 ->
  product_measure1 m1 sm2 (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
move=> mA1 mA2; rewrite /product_measure1 /=.
rewrite (_ : (fun _ => _) = (fun x => m2 A2 * (\1_A1 x)%:E)%E); last first.
  rewrite funeqE => x; rewrite indicE.
  by have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionM// mule1|rewrite mule0 notin_xsectionM].
rewrite ge0_integralM //.
- by rewrite muleC integral_indic// setIT.
- apply: measurable_fun_comp => //.
  by rewrite (_ : \1_ _ = mindic R mA1).
- by move=> x _; rewrite lee_fin.
Qed.

End product_measure1E.

Section product_measure_unique.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).

Definition product_measure_unique (m' : {measure set (T1 * T2) -> \bar R}) :
  (forall A1 A2, measurable A1 -> measurable A2 -> m' (A1 `*` A2) = m1 A1 * m2 A2)%E ->
  forall X : set (T1 * T2), measurable X -> product_measure1 m1 sf_m2 X = m' X.
Proof.
move=> m'E.
pose m := product_measure1 m1 sf_m2.
move/sigma_finiteP : sf_m1 => [F1 F1_T [F1_nd F1_oo]].
move/sigma_finiteP : sf_m2 => [F2 F2_T [F2_nd F2_oo]].
have UF12T : \bigcup_k (F1 k `*` F2 k) = setT.
  rewrite -setMTT F1_T F2_T.
  rewrite predeqE => -[x y]; split.
    by move=> [n _ []/= F1nx F2nx]; split; exists n.
  move=> [/= [n _ F1nx] [k _ F2ky]]; exists (maxn n k) => //; split => /=.
    by move: x F1nx; apply/subsetPset/F1_nd; rewrite leq_maxl.
  by move: y F2ky; apply/subsetPset/F2_nd; rewrite leq_maxr.
have mF1F2 : forall i : nat, measurable (F1 i `*` F2 i) /\ (m (F1 i `*` F2 i) < +oo)%E.
  move=> k; split.
    by apply: measurableM; [have [] := F1_oo k|have [] := F2_oo k].
  rewrite product_measure1E //; last 2 first.
    by have [] := F1_oo k.
    by have [] := F2_oo k.
  rewrite lte_mul_pinfty//.
  + by rewrite ge0_fin_numE//; have [] := F1_oo k.
  + by have [] := F2_oo k.
have sf_m : sigma_finite setT m by exists (fun n => F1 n `*` F2 n).
pose C : set (set (T1 * T2)) :=
  [set C | exists A1, measurable A1 /\ exists A2, measurable A2 /\ C = A1 `*` A2 ].
have CI : setI_closed C.
  move=> /= _ _ [X1 [mX1 [X2 [mX2 ->]]]] [Y1 [mY1 [Y2 [mY2 ->]]]].
  rewrite -setMI.
  exists (X1 `&` Y1); split; first exact: measurableI.
  by exists (X2 `&` Y2); split => //; exact: measurableI.
move=> X mX.
apply: (@measure_unique R (prod_measurableType T1 T2) C (fun n => F1 n `*` F2 n)) => //.
- rewrite measurable_prod_measurableType //.
  congr (s<< _ >>).
  rewrite predeqE; split => [[A1 mA1 [A2 mA2 <-]]|[A1 [mA1 [A2 [mA2 ->]]]]].
    by exists A1; split => //; exists A2; split.
  by exists A1 => //; exists A2.
- move=> n; rewrite /C /=.
  exists (F1 n); split; first by have [] := F1_oo n.
  by exists (F2 n); split => //; have [] := F2_oo n.
- by move=> A [A1 [mA1 [A2 [mA2 ->]]]]; rewrite m'E// product_measure1E.
- move=> k.
  rewrite product_measure1E //; last 2 first.
    by have [] := F1_oo k.
    by have [] := F2_oo k.
  rewrite lte_mul_pinfty//.
  + rewrite ge0_fin_numE//.
    by have [] := F1_oo k.
  + by have [] := F2_oo k.
(*
apply: (@measure_unique_new R (prod_measurableType T1 T2) C _ _ (fun n => F1 n `*` F2 n)) => //.
- move=> A [A1 [mA1 [A2 [mA2 ->]]]]; exact: measurableM.
- move=> n; rewrite /C /=.
  exists (F1 n); split; first by have [] := F1_oo n.
  exists (F2 n); split; first by have [] := F2_oo n.
  by split => //.
- move=> a b ab; apply/subsetPset; apply: setSM.
  by apply/subsetPset; apply F2_nd.
  by apply/subsetPset; apply F1_nd.
- move=> A [A1 [mA1 [A2 [mA2 ->]]]].
  rewrite m'E//.
  by rewrite product_measure1E//.
- move=> k.
  rewrite product_measure1E //; last 2 first.
    by have [] := F1_oo k.
    by have [] := F2_oo k.
  rewrite lte_mul_pinfty//.
  + by rewrite measure_ge0//; have [] := F1_oo k.
  + rewrite ge0_fin_numE//.
    by have [] := F1_oo k.
    by rewrite measure_ge0//; have [] := F1_oo k.
  + by have [] := F2_oo k.
- move: mX.
  rewrite measurable_prod_measurableType.
  rewrite /C.
  apply: subset_g_salgebra.
  move=> x [x1 mx1 [x2 mx2 <-{x}]].
  exists x1; split => //.
  exists x2; split => //.
*)
Qed.

End product_measure_unique.

Section product_measure2.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm1 : sigma_finite setT m1).
Implicit Types A : set (T1 * T2).

Let m A := \int ((m1 \o ysection A) x) 'd m2[x].

Let m0 : m set0 = 0%E.
Proof.
rewrite /m (_ : _ \o _ = cst 0)%E ?integral0// funeqE => x /=.
by rewrite ysection0 measure0.
Qed.

Local Lemma m_ge0 A : 0 <= m A.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_ysection.
Qed.

Local Lemma m2_sigma_additive : semi_sigma_additive m.
Proof.
move=> F mF tF mUF.
have -> : m (\bigcup_n F n) = \sum_(n <oo) (m (F n)).
  transitivity (\int (\sum_(n <oo) m1 (ysection (F n) y)) 'd m2[y]).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => y.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= ysection_bigcup.
(*    apply: (measure_sigma_additive _ (trivIset_ysection tF)).
    by move=> i; apply: measurable_ysection.*) admit.
  by rewrite integral_sum // => n; apply: measurable_fun_ysection => //; rewrite inE.
suff /cvg_ex[l cl] : cvg (fun n => (\sum_(i < n) m (F i))%E).
  (*by move: (cl) => /cvg_lim; rewrite -lim_mkord => ->.*) admit.
under eq_fun do rewrite -(big_mkord xpredT (m \o F)).
by apply: is_cvg_ereal_nneg_natsum => n _; apply: integral_ge0 => // x _.
Admitted.

Definition product_measure2 : {measure set (T1 * T2) -> \bar R} :=
  Measure.Pack _ (Measure.Axioms m0 m_ge0 m2_sigma_additive).

End product_measure2.

Section product_measure2E.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm1 : sigma_finite setT m1.

Lemma product_measure2E (A1 : set T1) (A2 : set T2)
    (mA1 : measurable A1) (mA2 : measurable A2) :
  product_measure2 m2 sm1 (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
have mA1A2 : measurable (A1 `*` A2) by apply: measurableM.
transitivity (\int ((m1 \o ysection (A1 `*` A2)) y) 'd m2[y])%E => //.
rewrite (_ : _ \o _ = (fun y => m1 A1 * (\1_A2 y)%:E))%E.
  rewrite ge0_integralM//; last 2 first.
    - apply: measurable_fun_comp => //.
      by rewrite (_ : \1_ _ = mindic R mA2).
    - by move=> y _; rewrite lee_fin.
  by rewrite integral_indic ?setIT ?mul1e.
rewrite funeqE => y; rewrite indicE.
have [yA2|yA2] := boolP (y \in A2); first by rewrite mule1 /= in_ysectionM.
by rewrite mule0 /= notin_ysectionM// measure0.
Qed.

End product_measure2E.

Section fubini_tonelli.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).

Let m : {measure set (T1 * T2) -> \bar R} := product_measure1 m1 sf_m2.

Let m' : {measure set (T1 * T2) -> \bar R} := product_measure2 m2 sf_m1.

Section fubini_tonelli_functions.
Variable f : T1 * T2 -> \bar R.
Local Open Scope ereal_scope.

Definition fubini_F x := \int (f (x, y)) 'd m2[y].
Definition fubini_G y := \int (f (x, y)) 'd m1[x].
End fubini_tonelli_functions.

Section sfun1_fubini_tonelli.
Variables (A : set (T1 * T2)) (mA : measurable A).
Implicit Types A : set (T1 * T2).
Let f : (prod_measurableType T1 T2) -> R := \1_A.
Local Open Scope ereal_scope.

Let F := fubini_F (EFin \o f).
Let G := fubini_G (EFin \o f).

Lemma sfun1_fubini_tonelli_F_ge0 x : (0 <= F x)%E.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma sfun1_fubini_tonelli_G_ge0 x : (0 <= G x)%E.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma sfun1_fubini_tonelli_FE : F = m2 \o xsection A.
Proof.
rewrite funeqE => x; rewrite /= -(setTI (xsection _ _)).
rewrite -integral_indic//; last exact: measurable_xsection.
rewrite /F /fubini_F -(setTI (xsection _ _)).
rewrite integral_presfun_ind1_setI; [|exact: measurable_xsection|by []].
apply eq_integral => y _ /=.
rewrite /f indicT mul1e !indicE.
have [|] /= := boolP (y \in xsection _ _).
  by rewrite inE /xsection /= => ->.
by rewrite /xsection /= notin_set /= => /negP/negbTE ->.
Qed.

Lemma sfun1_fubini_tonelli_GE : G = m1 \o ysection A.
Proof.
rewrite funeqE => y; rewrite /= -(setTI (ysection _ _)).
rewrite -integral_indic//; last exact: measurable_ysection.
rewrite /F /fubini_F -(setTI (ysection _ _)).
rewrite integral_presfun_ind1_setI; [|exact: measurable_ysection|by []].
rewrite /G /fubini_G.
apply: eq_integral => x _ /=.
rewrite /f indicT mul1e 2!indicE.
have [|] /= := boolP (x \in ysection _ _).
  by rewrite inE /xsection /= => ->.
by rewrite /xsection /= notin_set /= => /negP/negbTE ->.
Qed.

Lemma sfun1_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
by rewrite sfun1_fubini_tonelli_FE//; apply: measurable_fun_xsection => //; rewrite inE.
Qed.

Lemma sfun1_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
by rewrite sfun1_fubini_tonelli_GE//; apply: measurable_fun_ysection => //; rewrite inE.
Qed.

(* par definition de la mesure produit *)
Let mE : m A = \int (F x) 'd m1[x].
Proof. by rewrite /m /product_measure1 /= sfun1_fubini_tonelli_FE. Abort.

Lemma sfun1_fubini_tonelli1 :
  \int ((EFin \o f) z) 'd m[z] = \int (F x) 'd m1[x].
Proof.
by rewrite /f integral_indic// setIT sfun1_fubini_tonelli_FE.
Qed.

Lemma sfun1_fubini_tonelli2 :
  \int ((EFin \o f) z) 'd m'[z] = \int (G y) 'd m2[y].
Proof.
by rewrite /f integral_indic// setIT sfun1_fubini_tonelli_GE.
Qed.

Lemma sfun1_fubini_tonelli : \int (F x) 'd m1[x] = \int (G y) 'd m2[y].
Proof.
rewrite -sfun1_fubini_tonelli1// -sfun1_fubini_tonelli2//.
rewrite integral_indic // integral_indic // setIT.
by apply: product_measure_unique => // A1 A2 mA1 mA2; rewrite product_measure2E.
Qed.

End sfun1_fubini_tonelli.

Section sfun_fubini_tonelli.
Variable f : {nnsfun [the measurableType of T1 * T2 : Type] >-> R}.
(*Let n := ssize f.
Let A := spimg f.
Let a := srng f.*)

Let F := fubini_F (EFin \o f).
Let G := fubini_G (EFin \o f).

(*TODO: fix implicits of eq_integral*)

(*
Lemma sfun_fubini_tonelli_FE :
  F = (fun x => (\sum_(k < n) (a`_k)%:E * m2 (xsection (A k) x))%E).
Proof.
rewrite funeqE => x; rewrite /F /fubini_F [in LHS]/=.
under eq_fun do rewrite (sfunE (pt1, pt2) f) -sumEFin.
rewrite integral_ge0_sum //; last 2 first.
  - move=> i; apply/EFin_measurable_fun => //; apply: measurable_funrM => //.
    exact/measurable_fun_prod1/measurable_fun_presfun_ind1.
  - move=> i y _; rewrite lee_fin; apply: mulr_ge0 => //; first exact: NNSFun_ge0.
    by rewrite presfun_ind1E.
apply eq_bigr => i _.
under eq_fun do rewrite EFinM.
rewrite ge0_integralM//; last 3 first.
  - exact/EFin_measurable_fun/measurable_fun_prod1/measurable_fun_presfun_ind1.
  - by move=> y _; rewrite lee_fin presfun_ind1E.
  - by rewrite lee_fin; exact: NNSFun_ge0.
congr (_ * _)%E.
rewrite -/((m2 \o xsection (A i)) x) -sfun1_fubini_tonelli_FE //.
exact: measurable_spimg.
Qed.*)

Lemma sfun_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
(*rewrite sfun_fubini_tonelli_FE//; apply: measurable_fun_sum => //.
- move=> i; apply: emeasurable_funeM => //.
  by apply: measurable_fun_xsection => //; rewrite inE /A.
Qed.*) Admitted.

(*Lemma sfun_fubini_tonelli_GE :
  G = (fun y => (\sum_(k < n) (a`_k)%:E * m1 (ysection (A k) y))%E).
Proof.
rewrite funeqE => y; rewrite /G /fubini_G [in LHS]/=.
under eq_fun do rewrite (sfunE (pt1, pt2) f) -sumEFin.
rewrite integral_ge0_sum //; last 2 first.
  - move=> i; apply/EFin_measurable_fun => //; apply: measurable_funrM => //.
    exact/measurable_fun_prod2/measurable_fun_presfun_ind1.
  - move=> i x _; rewrite lee_fin; apply: mulr_ge0 => //; first exact: NNSFun_ge0.
    by rewrite presfun_ind1E.
apply eq_bigr => i _; under eq_fun do rewrite EFinM.
rewrite ge0_integralM//; last 3 first.
  - exact/EFin_measurable_fun/measurable_fun_prod2/measurable_fun_presfun_ind1.
  - by move=> x _; rewrite lee_fin presfun_ind1E.
  - by rewrite lee_fin; exact: NNSFun_ge0.
congr (_ * _)%E.
rewrite -/((m1 \o ysection (A i)) y) -sfun1_fubini_tonelli_GE//.
exact: measurable_spimg.
Qed.*)

Lemma sfun_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
(*rewrite sfun_fubini_tonelli_GE//; apply: measurable_fun_sum => //.
- move=> i; apply: emeasurable_funeM => //.
  by apply: measurable_fun_ysection => //; rewrite inE /A.
Qed.*) Admitted.

Lemma sfun_fubini_tonelli1 : (\int ((EFin \o f) z) 'd m[z] = \int (F x) 'd m1[x])%E.
Proof.
(*have EFinf : EFin \o f = (fun x => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E).
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite EFinf integral_ge0_sum //; last 2 first.
  - move=> /= i.
    apply/EFin_measurable_fun/measurable_funrM => //.
    by apply/measurable_fun_presfun_ind1 => //; exact: measurable_spimg.
  - move=> i xy _; apply: mule_ge0; rewrite lee_fin// ?presfun_ind1E//.
    exact: NNSFun_ge0.
under eq_bigr.
  move=> i _.
  rewrite ge0_integralM//; last 3 first.
    - apply/EFin_measurable_fun/measurable_fun_presfun_ind1 => //.
      exact/measurable_spimg.
    - by move=> /= x _; rewrite presfun_ind1E lee_fin.
    - exact: NNSFun_ge0.
  over.
rewrite /=.
under eq_bigr.
  move=> i _; rewrite sfun1_fubini_tonelli1; last exact/measurable_spimg.
  over.
under eq_bigr.
  move=> i _.
  rewrite -ge0_integralM//; last 3 first.
    - by apply: sfun1_measurable_fun_fubini_tonelli_F; exact/measurable_spimg.
    - by move=> /= x _; exact: sfun1_fubini_tonelli_F_ge0.
    - exact: NNSFun_ge0.
  over.
rewrite -integral_ge0_sum //; last 2 first.
  - move=> /= i; apply: emeasurable_funeM => //.
    by apply: sfun1_measurable_fun_fubini_tonelli_F; exact: measurable_spimg.
  - move=> i xy _.
    by apply: mule_ge0 => //; [exact: NNSFun_ge0|exact: sfun1_fubini_tonelli_F_ge0].
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_FE; apply eq_bigr => i _; congr (_ * _)%E.
rewrite -[RHS]/((m2 \o xsection (A i)) x) -sfun1_fubini_tonelli_FE //.
exact: measurable_spimg.
Qed.*) Admitted.

Lemma sfun_fubini_tonelli2 : (\int ((EFin \o f) z) 'd m'[z] = \int (G y) 'd m2[y])%E.
Proof.
(*have EFinf : EFin \o f = (fun x => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E).
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite EFinf integral_ge0_sum //; last 2 first.
  - move=> /= i; apply/EFin_measurable_fun/measurable_funrM => //.
    by apply/measurable_fun_presfun_ind1 => //; exact/measurable_spimg.
  - move=> i xy _; apply: mule_ge0; rewrite lee_fin// ?presfun_ind1E//.
    exact: NNSFun_ge0.
under eq_bigr.
  move=> i _.
  rewrite ge0_integralM//; last 3 first.
    - apply/EFin_measurable_fun => //; apply/measurable_fun_presfun_ind1 => //.
      exact/measurable_spimg.
    - by move=> /= x _; rewrite lee_fin// presfun_ind1E.
    - exact: NNSFun_ge0.
  over.
rewrite /=.
under eq_bigr.
  move=> i _;rewrite sfun1_fubini_tonelli2; last exact: measurable_spimg.
  over.
under eq_bigr.
  move=> i _.
  rewrite -ge0_integralM//; last 3 first.
    - by apply: sfun1_measurable_fun_fubini_tonelli_G; exact: measurable_spimg.
    - by move=> /= x _; exact: sfun1_fubini_tonelli_G_ge0.
    - exact: NNSFun_ge0.
  over.
rewrite -integral_ge0_sum //; last 2 first.
  - move=> /= i; apply: emeasurable_funeM => //.
    by apply: sfun1_measurable_fun_fubini_tonelli_G; exact: measurable_spimg.
  - move=> i xy _.
    by apply: mule_ge0 => //; [exact: NNSFun_ge0|exact: sfun1_fubini_tonelli_G_ge0].
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_GE; apply eq_bigr => i _; congr (_ * _)%E.
rewrite -[RHS]/((m1 \o ysection (A i)) x) -sfun1_fubini_tonelli_GE //.
exact/measurable_spimg.
Qed.*) Admitted.

Lemma sfun_fubini_tonelli :
  (\int ((EFin \o f) z) 'd m[z] = \int ((EFin \o f) z) 'd m'[z])%E.
Proof.
(*rewrite (_ : _ \o _ = (fun x : T1 * T2 => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E)); last first.
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite integral_ge0_sum //; last 2 first.
  - move=> /= i; apply/EFin_measurable_fun/measurable_funrM => //.
    by apply/measurable_fun_presfun_ind1 => //; exact: measurable_spimg.
  - move=> i xy _; apply: mule_ge0; rewrite lee_fin// ?presfun_ind1E//.
    exact: NNSFun_ge0.
under eq_bigr.
  move=> i _.
  rewrite ge0_integralM//; last 3 first.
    - apply/EFin_measurable_fun/measurable_fun_presfun_ind1 => //.
      exact/measurable_spimg.
    - by move=> /= x _; rewrite lee_fin presfun_ind1E.
    - exact: NNSFun_ge0.
  over.
rewrite /=.
under eq_bigr.
  move=> i _.
  rewrite sfun1_fubini_tonelli1; last exact/measurable_spimg.
  rewrite sfun1_fubini_tonelli; last exact/measurable_spimg.
  rewrite -sfun1_fubini_tonelli2; last exact/measurable_spimg.
  over.
apply/esym.
rewrite integral_ge0_sum //; last 2 first.
  - move=> /= i.
    apply/EFin_measurable_fun/measurable_funrM => //.
    by apply/measurable_fun_presfun_ind1 => //; exact: measurable_spimg.
  - move=> i xy _; apply: mule_ge0.
      rewrite lee_fin; exact: NNSFun_ge0.
    by rewrite presfun_ind1E lee_fin.
apply: eq_bigr => i _.
rewrite ge0_integralM//.
- by apply/EFin_measurable_fun/measurable_fun_presfun_ind1 => //; exact: measurable_spimg.
- by move=> /= x _; rewrite presfun_ind1E lee_fin.
- exact: NNSFun_ge0.
Qed.
*)
Admitted.

End sfun_fubini_tonelli.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.
Hypothesis f0 : forall x, 0 <= f x.
Let T12 := [the measurableType of T1 * T2 : Type].

Let F := fubini_F f.
Let G := fubini_G f.

Let F_ (g : {nnsfun T12 >-> R}^nat) n x :=
  \int ((EFin \o g n) (x, y)) 'd m2[y].
Let G_ (g : {nnsfun T12 >-> R}^nat) n y :=
  \int ((EFin \o g n) (x, y)) 'd m1[x].

Lemma measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
apply: (@emeasurable_fun_cvg _ _ _ (F_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> x _.
  rewrite /F_ /F /fubini_F.
  rewrite [in X in _ --> X](_ : (fun _ => _) =
      (fun y => lim (EFin \o g ^~ (x, y)))); last first.
    by rewrite funeqE => y; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - move=> n.
    by apply/EFin_measurable_fun => //; apply/measurable_fun_prod1.
  - by move=> n y _; rewrite lee_fin//; apply: fun_ge0.
  - by move=> y _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
apply: (@emeasurable_fun_cvg _ _ _ (G_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- move=> y _.
  rewrite /G_ /G /fubini_G.
  rewrite [in X in _ --> X](_ : (fun _ => _) =
      (fun x => lim (EFin \o g ^~ (x, y)))); last first.
    by rewrite funeqE => x; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - move=> n.
    by apply/EFin_measurable_fun => //; exact/measurable_fun_prod2.
  - by move=> n x _; rewrite lee_fin; exact: fun_ge0.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma fubini_tonelli1 : \int (f z) 'd m[z] = \int (F x) 'd m1[x].
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
have F_F x : F x = lim (F_ g ^~ x).
  rewrite /F /fubini_F.
  rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) (x, y)) 'd m2[y]))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> n /= y _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) z) 'd m[z])).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ = lim
    (fun n => \int (\int ((EFin \o g n) (x, y)) 'd m2[y]) 'd m1[x])).
  by congr (lim _); rewrite funeqE => n; rewrite sfun_fubini_tonelli1.
rewrite [RHS](_ : _ = lim (fun n => \int (F_ g n x) 'd m1[x]))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- by move=> n x _; apply integral_ge0 => // y _ /=; rewrite lee_fin; exact: fun_ge0.
- move=> x /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> y _; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod1.
  + by move=> *; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod1.
  + by move=> y _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

Lemma fubini_tonelli2 : \int (f z) 'd m[z] = \int (G y) 'd m2[y].
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
have G_G y : G y = lim (G_ g ^~ y).
  rewrite /G /fubini_G.
  rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) (x, y)) 'd m1[x]))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod2.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> x /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) z) 'd m[z])).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ = lim
    (fun n => \int (\int ((EFin \o g n) (x, y)) 'd m1[x]) 'd m2[y])).
  congr (lim _); rewrite funeqE => n.
  by rewrite sfun_fubini_tonelli sfun_fubini_tonelli2.
rewrite [RHS](_ : _ = lim (fun n => \int (G_ g n y) 'd m2[y]))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- by move=> n y _; apply integral_ge0 => // x _ /=; rewrite lee_fin; exact: fun_ge0.
- move=> y /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod2.
  + by move=> *; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod2.
  + by move=> x _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

End fubini_tonelli.

End fubini_tonelli.

Section fubini.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.

Let m : {measure set (T1 * T2) -> \bar R} := product_measure1 m1 sf_m2.

Lemma fubini1a : m.-integrable setT f <->
  \int (\int `|f (x, y)| 'd m2[y]) 'd m1[x] < +oo.
Proof.
split=> [[_ ioo]|ioo].
- rewrite -(@fubini_tonelli1 _ _ _ _ _ sf_m1(*NB: this argument should disappear with the lemma is deadmitted*) sf_m2 (abse \o f))//.
  + exact: measurable_fun_comp.
  + by move=> /=.
- by split=> //; rewrite fubini_tonelli1//; exact: measurable_fun_comp.
Qed.

Lemma fubini1b : m.-integrable setT f <->
  \int (\int `|f (x, y)| 'd m1[x]) 'd m2[y] < +oo.
Proof.
split=> [[_ ioo]|ioo].
- rewrite -(@fubini_tonelli2 _ _ _ _ _ sf_m1 sf_m2 (abse \o f))//=.
  exact: measurable_fun_comp.
- by split=> //; rewrite fubini_tonelli2//; exact: measurable_fun_comp.
Qed.

Let measurable_fun1 : measurable_fun setT (fun x => \int `|f (x, y)| 'd m2[y]).
Proof.
apply: (@measurable_fun_fubini_tonelli_F _ _ _ _ _ _ sf_m2 (abse \o f)) => //=.
exact: sf_m1.
exact: measurable_fun_comp.
Qed.

Let measurable_fun2 : measurable_fun setT (fun y => \int `|f (x, y)| 'd m1[x]).
Proof.
apply: (@measurable_fun_fubini_tonelli_G _ _ _ _ _ _ sf_m2 (abse \o f)) => //=.
exact: measurable_fun_comp.
Qed.

Hypothesis imf : m.-integrable setT f.

Lemma ae_integrable1 :
  {ae m1, forall x, m2.-integrable setT (fun y => f (x, y))}.
Proof.
move/fubini1a : imf => foo.
have : m1.-integrable setT (fun x => \int `|f (x, y)| 'd m2[y]).
  split => //; rewrite (le_lt_trans _ foo)//; apply: ge0_le_integral => //.
  - exact: measurable_fun_comp.
  - by move=> *; exact: integral_ge0.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT) [N [mN N0 subN]].
exists N; split => //.
apply/(subset_trans _ subN)/subsetC => x /= /(_ Logic.I) im2f.
by split; [exact/measurable_fun_prod1|by move/fin_numPlt : im2f => /andP[]].
Qed.

Lemma ae_integrable2 :
  {ae m2, forall y, m1.-integrable setT (fun x => f (x, y))}.
Proof.
move/fubini1b : imf => foo.
have : m2.-integrable setT (fun y => \int `|f (x, y)| 'd m1[x]).
  split => //; rewrite (le_lt_trans _ foo)//; apply: ge0_le_integral => //.
  - exact: measurable_fun_comp.
  - by move=> *; exact: integral_ge0.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT) [N [mN N0 subN]].
exists N; split => //.
apply/(subset_trans _ subN)/subsetC => x /= /(_ Logic.I) im1f.
by split; [exact/measurable_fun_prod2|move/fin_numPlt : im1f => /andP[]].
Qed.

Let F := fubini_F m2 f.

Let Fplus x := \int (f^\+ (x, y)) 'd m2[y].
Let Fminus x := \int (f^\- (x, y)) 'd m2[y].

Let FE : F = Fplus \- Fminus. Proof. apply/funext=> x; exact: integralE. Qed.

Let measurable_Fplus : measurable_fun setT Fplus.
Proof.
apply: measurable_fun_fubini_tonelli_F => //.
exact: sf_m1.
exact: emeasurable_fun_funenng.
Qed.

Let measurable_Fminus : measurable_fun setT Fminus.
Proof.
apply: measurable_fun_fubini_tonelli_F => //.
exact: sf_m1.
exact: emeasurable_fun_funennp.
Qed.

Lemma measurable_fubini_F : measurable_fun setT F.
Proof.
rewrite FE.
apply: emeasurable_funB.
exact: measurable_Fplus.
exact: measurable_Fminus.
Qed.

Let integrable_Fplus : m1.-integrable setT Fplus.
Proof.
split=> //; have := fubini1a.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> x _; exact: integral_ge0.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funenng => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funenng => //; exact: measurable_fun_prod1.
  - apply: measurable_fun_comp => //.
    by apply/measurable_fun_prod1.
  - by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Fminus : m1.-integrable setT Fminus.
Proof.
split=> //; have := fubini1a.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod1.
  + apply: measurable_fun_comp => //.
    exact: measurable_fun_prod1.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma integrable_fubini_F : m1.-integrable setT F.
Proof.
by rewrite FE; apply: integrableB => //.
(*exact: integrable_Fplus.
exact: integrable_Fminus.*)
Qed.

Let G := fubini_G m1 f.

Let Gplus y := \int (f^\+ (x, y)) 'd m1[x].
Let Gminus y := \int (f^\- (x, y)) 'd m1[x].

Let GE : G = Gplus \- Gminus. Proof. apply/funext=> x; exact: integralE. Qed.

Let measurable_Gplus : measurable_fun setT Gplus.
Proof.
apply: measurable_fun_fubini_tonelli_G => //.
exact: sf_m2.
exact: emeasurable_fun_funenng.
Qed.

Let measurable_Gminus : measurable_fun setT Gminus.
Proof.
apply: measurable_fun_fubini_tonelli_G => //.
exact: sf_m2.
exact: emeasurable_fun_funennp.
Qed.

Lemma measurable_fubini_G : measurable_fun setT G.
Proof.
rewrite GE; apply: emeasurable_funB => //.
(*exact: measurable_Gplus.
exact: measurable_Gminus.*)
Qed.

Let integrable_Gplus : m2.-integrable setT Gplus.
Proof.
split=> //; have := fubini1b.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funenng => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funenng => //; exact: measurable_fun_prod2.
  - apply: measurable_fun_comp => //.
    by exact: measurable_fun_prod2.
  - by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Gminus : m2.-integrable setT Gminus.
Proof.
split=> //; have := fubini1b.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funennp => //; exact: measurable_fun_prod2.
  + apply: measurable_fun_comp => //.
    exact: measurable_fun_prod2.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma fubini1 : \int (F x) 'd m1[x] = \int (f z) 'd m[z].
Proof.
rewrite FE integralB//.
  rewrite [in RHS]integralE//.
  rewrite fubini_tonelli1//; last exact: emeasurable_fun_funenng.
  by rewrite fubini_tonelli1//; exact: emeasurable_fun_funennp.
(*exact: integrable_Fplus.
exact: integrable_Fminus.*)
Qed.

Lemma fubini2 : \int (G x) 'd m2[x] = \int (f z) 'd m[z].
Proof.
rewrite GE integralB//.
  rewrite [in RHS]integralE//.
  rewrite fubini_tonelli2//; last exact: emeasurable_fun_funenng.
  by rewrite fubini_tonelli2//; exact: emeasurable_fun_funennp.
(*exact: integrable_Gplus.
exact: integrable_Gminus.*)
Qed.

End fubini.
