(* -*- company-coq-local-symbols: (("\\int" . ?∫) ("\\int_" . ?∫) ("'d" . ?𝑑) ("^\\+" . ?⁺) ("^\\-" . ?⁻)); -*- *)
(* intersection U+2229; union U+222A, set U+2205 *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import mathcomp_extra boolp classical_sets posnum functions cardinality.
Require Import topology normedtype sequences measure nngnum lebesgue_measure.

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

(* PR in progress *)
Notation "f \- g" := (fun x => f x - g x)%E : ereal_scope.
(* /PR in progress *)

(* PR: in progress *)
Lemma fin_numB (R : numDomainType) (x y : \bar R) :
  (x - y \is a fin_num)%E = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.
(* /PR: in progress *)

Lemma continuous_is_cvg {T : Type} {V U : topologicalType} [F : set (set T)]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma trivIset_setIr T I D (F : I -> set T) X :
  trivIset D F -> trivIset D (fun i => F i `&` X).
Proof. by under eq_fun do rewrite setIC; exact: trivIset_setI. Qed.

Lemma bigsetU_bigcup2 (T : Type) (A B : set T) :
  \big[setU/set0]_(i < 2) bigcup2 A B i = A `|` B.
Proof. by rewrite !big_ord_recl big_ord0 setU0. Qed.


(* PR in progress *)
Local Open Scope ereal_scope.
Lemma mule_eqpinfty (R : realDomainType) (x y : \bar R) :
  (x * y == +oo) = [|| ((x > 0) && (y == +oo)), ((x < 0) && (y == -oo)),
                      ((x == +oo) && (y > 0)) | ((x == -oo) && (y < 0))].
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_fin,andbF,andbT,orbF,eqxx,andbT)//=.
- by rewrite mulrpinfty; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP x 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulrninfty; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP x 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulpinftyr; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP y 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_pinfty_pinfty lte_pinfty.
- by rewrite mule_pinfty_ninfty.
- by rewrite mulninftyr; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP y 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_ninfty_pinfty.
- by rewrite lte_ninfty.
Qed.

Lemma mule_eqninfty (R : realDomainType) (x y : \bar R) :
  (x * y == -oo) = [|| ((x > 0) && (y == -oo)), ((x < 0) && (y == +oo)),
                      ((x == -oo) && (y > 0)) | ((x == +oo) && (y < 0))].
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_fin,andbF,andbT,orbF,eqxx,andbT)//=.
- by rewrite mulrpinfty; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP x 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulrninfty; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP x 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulpinftyr; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP y 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_pinfty_pinfty.
- by rewrite mule_pinfty_ninfty lte_pinfty lte_ninfty.
- by rewrite mulninftyr; have [/ltr0_sg ->|/gtr0_sg ->|->] := ltgtP y 0%R;
    rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_ninfty_pinfty lte_pinfty lte_ninfty.
Qed.
Local Close Scope ereal_scope.

Lemma fine_eq0 (R : numDomainType) (x : \bar R) : x \is a fin_num ->
  (fine x == 0) = (x == 0%E).
Proof. by move: x => [//| |] /=; rewrite fin_numE. Qed.

Lemma abse_eq0 (R : numDomainType) (x : \bar R) : (`|x|%E == 0%E) = (x == 0%E).
Proof. by move: x => [| |] //= r; rewrite !eqe normr_eq0. Qed.
(* /PR in progress *)

Lemma adde_gt0 (R : numDomainType) (x y : \bar R) : (0 < x -> 0 < y -> 0 < x + y)%E.
Proof.
by move: x y => [x| |] [y| |] //; rewrite !lte_fin; exact: addr_gt0.
Qed.

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
move: (@measure_bigsetU _ _ (measure_additive_measure m)) => ->; last 2 first.
  - by move=> i; rewrite /F'; case: eqP.
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
- by move=> i; case: ifPn.
- apply/trivIsetP => i j _ _ ij; case: ifPn => // Pi; last by rewrite set0I.
  case: ifPn => Pj; last by rewrite setI0.
  by move/trivIsetP : tF; apply.
Qed.

Lemma additive_fset (I : choiceType) (A : {fset I}) (F : I -> set T) :
  (forall i, measurable (F i)) -> trivIset setT F ->
  m (\big[setU/set0]_(i <- A) F i) = (\sum_(i <- A) m (F i))%E.
Proof.
move=> mF tF; have [->|/fset0Pn[y yA]] := eqVneq A fset0.
  by rewrite !big_nil measure0.
rewrite (big_nth y) big_mkord additive_ord//.
  by rewrite [RHS](big_nth y) big_mkord.
move=> i j _ _ ij; apply/val_inj/eqP.
by rewrite -(nth_uniq y (ltn_ord i) (ltn_ord j) (fset_uniq A)); exact/eqP/tF.
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

(* TODO: move *)
Lemma setTPn (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
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

Notation "f ^\+" := (funenng f).
Notation "f ^\-" := (funennp f).

Section funpos_lemmas.
Local Open Scope ereal_scope.
Variables (T : Type) (R : realDomainType) (D : set T).
Implicit Types (f : T -> \bar R) (r : R).

Lemma funenng_ge0 f x : 0 <= f^\+ x.
Proof. by rewrite /funenng /= le_maxr lexx orbT. Qed.

Lemma funennp_ge0 f x : 0 <= f^\- x.
Proof. by rewrite /funennp le_maxr lexx orbT. Qed.

Lemma funenngN f : (fun x => - f x)^\+ = f^\-.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp. Qed.

Lemma funennpN f : (fun x => - f x)^\- = f^\+.
Proof. by rewrite funeqE => x /=; rewrite /funenng /funennp oppeK. Qed.

Lemma ge0_funenngE f : (forall x, D x -> 0 <= f x) -> {in D, f^\+ =1 f}.
Proof. by move=> f0 x; rewrite inE => Dx; apply/max_idPl/f0. Qed.

Lemma ge0_funennpE f : (forall x, D x -> 0 <= f x) -> {in D, f^\- =1 cst 0}.
Proof.
by move=> f0 x; rewrite inE => Dx; apply/max_idPr; rewrite lee_oppl oppe0 f0.
Qed.

Lemma le0_funenngE f : (forall x, D x -> f x <= 0) -> {in D, f^\+ =1 cst 0}.
Proof. by move=> f0 x; rewrite inE => Dx; exact/max_idPr/f0. Qed.

Lemma le0_funennpE f :
  (forall x, D x -> f x <= 0) -> {in D, f^\- =1 (fun x => - f x)}.
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
  measurable D -> measurable_fun D f -> measurable_fun D f^\+.
Proof.
by move=> mD mf; apply: emeasurable_fun_max => //; apply: measurable_fun_cst.
Qed.

Lemma emeasurable_fun_funennp (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D f^\-.
Proof.
move=> mD mf; apply: emeasurable_fun_max => //; last exact: measurable_fun_cst.
by apply: measurable_fun_comp => //; apply: emeasurable_fun_minus.
Qed.

End funpos_measurable.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R := (x \in A)%:R.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

HB.mixin Record FiniteImage aT rT (x0 : aT) (A : set aT) (f : aT -> rT) := {
  fimfunP : finite_set (f @` A)
}.
HB.structure Definition FImFun aT rT x0 A := {f of @FiniteImage aT rT x0 A f}.

Reserved Notation "{ 'fimfun' x0 , A >-> T }"
  (at level 0, format "{ 'fimfun'  x0 ,  A  >->  T }").
Reserved Notation "[ 'fimfun' 'of' f ]"
  (at level 0, format "[ 'fimfun'  'of'  f ]").
Notation "{ 'fimfun' x0 ,  A >-> T }" := (@FImFun.type _ T x0 A) : form_scope.
Notation "[ 'fimfun' 'of' f ]" := [the {fimfun _, _ >-> _} of f] : form_scope.
Hint Resolve fimfunP : core.

Section fimfun_pred.
Context {aT rT : Type} (x0 : aT) (A : set aT).
Definition fimfun_key : pred_key (mem [set f : aT -> rT | finite_set (f @` A)]).
Proof. exact. Qed.
Definition fimfun := KeyedPred fimfun_key.
End fimfun_pred.

Section fimfun.
Context {aT rT : Type} (x0 : aT) (A : set aT).
Notation T := {fimfun x0, A >-> rT}.
Notation fimfun := (@fimfun aT rT A).
Section Sub.
Context (f : aT -> rT) (fP : f \in fimfun).
Definition fimfun_Sub_subproof := @FiniteImage.Build aT rT x0 A f (set_mem fP).
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

Lemma fimfuneqP aT rT x0 (A : set aT) (f g : {fimfun x0, A >-> rT}) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

Definition fimfuneqMixin aT (rT : eqType) x0 (A : set aT) :=
  [eqMixin of {fimfun x0, A >-> rT} by <:].
Canonical fimfuneqType aT (rT : eqType) x0 (A : set aT) :=
  EqType {fimfun x0, A >-> rT} (fimfuneqMixin rT x0 A).
Definition fimfunchoiceMixin aT (rT : choiceType) x0 (A : set aT) :=
  [choiceMixin of {fimfun x0, A >-> rT} by <:].
Canonical fimfunchoiceType aT (rT : choiceType) x0 (A : set aT) :=
  ChoiceType {fimfun x0, A >-> rT} (fimfunchoiceMixin rT x0 A).

Lemma finite_image_cst {aT rT} (x : rT) (A : set aT) : finite_set (cst x @` A).
Proof.
have [->|/set0P[t At]] := eqVneq A set0; first by rewrite image_set0.
suff -> : cst x @` A = [set x] by apply: finite_set1.
by apply/predeqP => y; split=> [[t' _ <-]//|->//] /=; exists t.
Qed.

Definition fun_cmul {U : Type} {R : ringType} (k : R) (f : U -> R) x := k * f x.
Notation "k *\ f" := (fun_cmul k f) (at level 40, format "k  *\  f") : ring_scope.

Lemma cst_fimfun_subproof aT rT x0 (A : set aT) x : @FiniteImage aT rT x0 A (cst x).
Proof.
split; have [->|/set0P[t At]] := eqVneq A set0; first by rewrite image_set0.
suff -> : cst x @` A = [set x] by apply: finite_set1.
by apply/predeqP => y; split=> [[t' _ <-]//|->//] /=; exists t.
Qed.
HB.instance Definition _ aT rT x0 A x := @cst_fimfun_subproof aT rT x0 A x.
Definition cst_fimfun {aT rT} x0 (A : set aT) x := [the {fimfun x0, A >-> rT} of cst x].

Lemma fimfun_cst aT rT x0 A x : @cst_fimfun aT rT x0 A x =1 cst x. Proof. by []. Qed.

Lemma comp_fimfun_subproof aT rT sT x0 (A : set aT)
   (f : {fimfun x0, A >-> rT}) (g : rT -> sT) : @FiniteImage aT sT x0 A (g \o f).
Proof. by split; rewrite -image_comp; apply: finite_image. Qed.
HB.instance Definition _ aT rT sT x0 A f g := @comp_fimfun_subproof aT rT sT x0 A f g.

Section zmod.
Context (aT : Type) (rT : zmodType) (x0 : aT) (A : set aT).
Lemma fimfun_zmod_closed : zmod_closed (@fimfun aT rT A).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; apply: (finite_image11 (fun x y => x - y)).
Qed.
Canonical fimfun_add := AddrPred fimfun_zmod_closed.
Canonical fimfun_zmod := ZmodPred fimfun_zmod_closed.
Definition fimfun_zmodMixin := [zmodMixin of {fimfun x0, A >-> rT} by <:].
Canonical fimfun_zmodType := ZmodType {fimfun x0, A >-> rT} fimfun_zmodMixin.

Implicit Types (f g : {fimfun x0, A >-> rT}).

Lemma fimfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma fimfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma fimfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma finfun0 : (0 : {fimfun x0, A >-> rT}) =1 cst 0. Proof. by []. Qed.
Lemma fimfun_sum I r (P : {pred I}) (f : I -> {fimfun x0, A >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
End zmod.

Section ring.
Context (aT : Type) (rT : ringType) (x0 : aT) (A : set aT).
#[local] Canonical aT_eqType := EqType aT gen_eqMixin.
#[local] Canonical aT_choiceType := ChoiceType aT gen_choiceMixin.
#[local] Canonical aT_pointedType := PointedType aT x0.

Lemma fimfun_mulr_closed : mulr_closed (@fimfun aT rT A).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; apply: (finite_image11 (fun x y => x * y)).
Qed.
Canonical fimfun_ring := SubringPred fimfun_mulr_closed.
Definition fimfun_ringMixin := [ringMixin of {fimfun x0, A >-> rT} by <:].
Canonical fimfun_ringType := RingType {fimfun x0, A >-> rT} fimfun_ringMixin.

Implicit Types (f g : {fimfun x0, A >-> rT}).

Lemma fimfunM f g : f * g =1 f \* g. Proof. by []. Qed.
Lemma fimfun1 : (1 : {fimfun x0, A >-> rT}) =1 cst 1. Proof. by []. Qed.
Lemma fimfun_prod I r (P : {pred I}) (f : I -> {fimfun x0, A >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma fimfunX f n : f ^+ n =1 (fun x => f x ^+ n).
Proof. by move=> x; elim: n => [|n IHn]//; rewrite !exprS fimfunM/= IHn. Qed.

Lemma indic_fimfun_subproof X : @FiniteImage aT rT x0 A \1_X.
Proof.
split; apply: (finite_subfset [fset 0; 1]%fset) => x [t At /=].
by rewrite !inE /indic; case: (_ \in _) => <-; rewrite ?eqxx ?orbT.
Qed.
HB.instance Definition _ X := indic_fimfun_subproof X.
Definition indic_fimfun (X : set aT) := [the {fimfun x0, A >-> rT} of \1_X].

Lemma indicT : \1_[set: aT] = cst (1 : rT).
Proof. by apply/funext=> x; rewrite /indic in_setT. Qed.

HB.instance Definition _ k f := FImFun.copy (k *\ f) (cst_fimfun x0 A k * f).
Definition scale_fimfun k f := [the {fimfun x0, A >-> rT} of k *\ f].

End ring.
Arguments indic_fimfun {aT rT x0 A} _.

Section comring.
Context (aT : Type) (rT : comRingType) (x0 : aT) (A : set aT).
#[local] Canonical aT_eqType' := EqType aT gen_eqMixin.
#[local] Canonical aT_choiceType' := ChoiceType aT gen_choiceMixin.
#[local] Canonical aT_pointedType' := PointedType aT x0.
Definition fimfun_comRingMixin := [comRingMixin of {fimfun x0, A >-> rT} by <:].
Canonical fimfun_comRingType := ComRingType {fimfun x0, A >-> rT} fimfun_comRingMixin.
End comring.

Lemma fimfunE T x0 (R : ringType) (A : set T) (f : {fimfun x0, A >-> R}) x :
  x \in A -> f x = \sum_(y <- fset_set (f @` A)) (y * \1_(A `&` f @^-1` [set y]) x).
Proof.
move=> /set_mem xA; have fxfA: f x \in fset_set (f @` A).
  by rewrite in_fset_set// inE//=; exists x => //; apply: set_mem.
rewrite (big_fsetD1 (f x))//= /indic (@id (_ \in _)) ?mulr1 ?inE//=.
rewrite big_seq_cond ?big1 ?addr0// => y; rewrite ?andbT !inE eq_sym.
move=> /andP[fxNy yA]; rewrite [_ \in _]negbTE ?mulr0// notin_set.
by move=> [_ fxy]; rewrite -fxy eqxx in fxNy.
Qed.

Lemma fimfunEord T x0 (R : ringType) (A : set T) (f : {fimfun x0, A >-> R})
  (s := fset_set (f @` A)) :
  forall x, x \in A -> f x = \sum_(i < #|`s|) (s`_i * \1_(A `&` f @^-1` [set s`_i]) x).
Proof. by move=> x xA; rewrite fimfunE /s // (big_nth 0) big_mkord. Qed.

Lemma trivIset_preimage1 {aT rT} (f : aT -> rT) (A : set rT) :
  trivIset setT (fun x => f @^-1` [set x]).
Proof. by move=> y z _ _ [x [<- <-]]. Qed.

Lemma trivIset_preimage1_in {aT} {rT : choiceType} (f : aT -> rT) (A : set aT) :
  trivIset setT (fun x => A `&` f @^-1` [set x]).
Proof. by move=> y z _ _ [x [[_ <-] [_ <-]]]. Qed.

HB.factory Record FiniteDecomp (T : Type) (R : ringType) (x0 : T) (A : set T) (f : T -> R) := {
  fimfunE : exists (r : seq R) (A_ : R -> set T),
    forall x, f x = \sum_(y <- r) (y * \1_(A_ y) x)
}.
HB.builders Context T R x0 A f of @FiniteDecomp T R x0 A f.
  Lemma finite_subproof: @FiniteImage T R x0 A f.
  Proof.
  split; have [r [A_ fE]] := fimfunE.
  suff -> : f = \sum_(y <- r) cst_fimfun x0 A y * indic_fimfun (A_ y) by [].
  by apply/funext=> x; rewrite fE fimfun_sum.
  Qed.
  HB.instance Definition _ := finite_subproof.
HB.end.

HB.mixin Record IsMeasurableFun (aT (*rT*) : measurableType) (rT : realType) (A : set aT) (f : aT -> rT) := {
  measurable_funP : measurable_fun A f
}.
HB.structure Definition MeasurableFun aT rT A := {f of @IsMeasurableFun aT rT A f}.
Reserved Notation "{ 'mfun' A >-> T }"
  (at level 0, format "{ 'mfun'   A  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").
Notation "{ 'mfun'  A >-> T }" := (@MeasurableFun.type _ T A) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
Hint Resolve measurable_funP : core.

HB.structure Definition SimpleFun (aT (*rT*) : measurableType) (rT : realType) (A : set aT) :=
  {f of @IsMeasurableFun aT rT A f & @FiniteImage aT rT mpoint A f}.
Reserved Notation "{ 'sfun' A >-> T }"
  (at level 0, format "{ 'sfun'   A  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").
Notation "{ 'sfun'  A >-> T }" := (@SimpleFun.type _ T A) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.
Hint Resolve measurable_funP : core.

Lemma measurable_sfunP {aT : measurableType} {rT : realType} {A : set aT} (f : {mfun A >-> _}) :
  forall y : rT, measurable (A `&` f @^-1` [set y]).
Proof. by move=> y; apply: measurable_funP; apply: measurable_set1. Qed.

HB.mixin Record IsNonNegFun (aT : Type) (rT : numDomainType)
   (A : set aT) (f : aT -> rT) := {
  fun_ge0 : forall x, A x -> 0 <= f x
}.
HB.structure Definition NonNegFun aT rT A := {f of @IsNonNegFun aT rT A f}.
Reserved Notation "{ 'nnfun' A >-> T }"
  (at level 0, format "{ 'nnfun'   A  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Notation "{ 'nnfun'  A >-> T }" := (@NonNegFun.type _ T A) : form_scope.
Notation "[ 'nnfun' 'of' f ]" := [the {nnfun _ >-> _} of f] : form_scope.

HB.structure Definition NonNegSimpleFun (aT : measurableType) (rT : realType) A :=
  {f of @SimpleFun _ _ A f & @NonNegFun aT rT A f}.
Reserved Notation "{ 'nnsfun' A >-> T }"
  (at level 0, format "{ 'nnsfun'   A  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Notation "{ 'nnsfun'  A >-> T }" := (@NonNegSimpleFun.type _ T A) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.


Section simple_fun_raw_integral.
Local Open Scope ereal_scope.
Variables (T : Type) (R : numDomainType).

Section def.
Variable (mu : set T -> \bar R) (D : set T) (f : T -> R).
Let s := fset_set (f @` D).

Definition sintegral := \sum_(x <- s) x%:E * mu (D `&` f @^-1` [set x]).

Lemma sintegralE : sintegral = \sum_(x <- s) x%:E * mu (D `&` f @^-1` [set x]).
Proof. by []. Qed.

(* discard ? *)
Lemma sintegralEord : sintegral =
   \sum_(k < #|` fset_set (f @` D)|) (s`_k)%:E * mu (D `&` f @^-1` [set s`_k]).
Proof. by rewrite /sintegral (big_nth 0%R) big_mkord. Qed.

End def.

Lemma sintegral0 mu D pt : sintegral mu D (cst_fimfun pt D 0%R) = 0%E.
Proof.
rewrite sintegralE/=; have [->|/set0P[x Dx]] := eqVneq D set0.
  by rewrite image_set0 fset_set0 big_seq_fset0.
rewrite (_ : [set _ | _ in _] = [set 0%R]) ?fset_set1 ?big_seq_fset1 ?mul0e//.
by apply/predeqP=> y; split=> [[]|->]//; exists x.
Qed.

End simple_fun_raw_integral.

Lemma eq_sintegral (T : measurableType) (R : realFieldType) D
    (mu : {measure set T -> \bar R}) f g :
  {in D, f =1 g} -> sintegral mu D f = sintegral mu D g.
Proof.
move=> fg; rewrite 2!sintegralE; have -> : f @` D = g @` D.
  by apply/eq_imagel => x Dx; rewrite fg ?inE.
apply: eq_bigr => y _; congr (_ * mu _)%E.
by apply/predeqP => x; split=> -[Dx <-]; split=> //; rewrite (fg, =^~fg) ?inE.
Qed.

(*  I stopped here *)


(*
Module NNPreSFun.
Record t (T : measurableType) (R : realType) :=
  mk {f : presfun T R ; ge0 : forall t, 0 <= f t }.
Module Exports.
Notation nnpresfun := t.
End Exports.
End NNPreSFun.
Export NNPreSFun.Exports.
Coercion NNPreSFun.f : nnpresfun >-> presfun.
Arguments NNPreSFun.mk {T R} _ _.

Hint Resolve NNPreSFun.ge0 : core.

Lemma NNPreSFun_ge0 (T : measurableType) (R : realType) (f : nnpresfun T R)
  (t : 'I_(ssize f)) : 0 <= (srng f)`_t.
Proof. by case: f t => // f f0 /= t; apply: presfun_ge0. Qed.

Lemma NNPreSFuncdom_ge0 (T : measurableType) (R : realType) (f : nnpresfun T R)
  (r : R) : r \in srng f -> (0 <= r%:E)%E.
Proof. by  move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNPreSFun_ge0 (Ordinal fi)). Qed.

Section nnpresfun_functions.
Variables (T : measurableType) (R : realType).

Program Definition nnpresfun_cst (pt : T) (r : {nonneg R}) :=
  NNPreSFun.mk (presfun_cst pt r%:nngnum) _.
Next Obligation. by move=> pt r t; rewrite presfun_cstE. Qed.

Definition nnpresfun0 (pt : T) : nnpresfun T R := nnpresfun_cst pt 0%R%:nng.

Program Definition nnpresfun_scale (pt : T) (f : nnpresfun T R) (k : R)
  (k0 : 0 <= k) := NNPreSFun.mk (presfun_scale pt k f) _.
Next Obligation. by move=> pt f k k0 t; rewrite presfun_scaleE mulr_ge0. Qed.

Program Definition nnpresfun_proj (f : nnpresfun T R) (A : set T) :=
  NNPreSFun.mk (presfun_proj f A) _.
Next Obligation. by move=> f A t; rewrite presfun_projE mulr_ge0. Qed.

Program Definition nnpresfun_ind (pt : T) (r : {nonneg R}) (A : set T) :=
  NNPreSFun.mk (presfun_ind pt r%:nngnum A) _.
Next Obligation. by move=> pt r A t; rewrite presfun_indE mulr_ge0. Qed.

End nnpresfun_functions.
Arguments nnpresfun0 {T R}.

Section nnpresfun_bin.
Variables (T : measurableType) (R : realType) (f g : nnpresfun T R).

Program Definition nnpresfun_add := NNPreSFun.mk (presfun_add f g) _.
Next Obligation. by move=> t; rewrite addr_ge0. Qed.

Program Definition nnpresfun_max := NNPreSFun.mk (presfun_max f g) _.
Next Obligation. by move=> t; rewrite /= /maxr; case: ifPn. Qed.

End nnpresfun_bin.
Arguments nnpresfun_add {T R} _ _.
Arguments nnpresfun_max {T R} _ _.

Section nnpresfun_iter.
Variables (T : measurableType) (pt : T) (R : realType).
Variable f : (nnpresfun T R)^nat.

Definition nnpresfun_sum n := \big[nnpresfun_add/(nnpresfun0 pt)]_(i < n) f i.

Lemma nnpresfun_sumE n t : nnpresfun_sum n t = \sum_(i < n) (f i t).
Proof.
rewrite /nnpresfun_sum; elim/big_ind2 : _ => [|_ g _ h <- <-//|//].
by rewrite /= presfun_cstE.
Qed.

Definition nnpresfun_bigmax n :=
  \big[nnpresfun_max/(nnpresfun0 pt)]_(i < n) f i.

Lemma nnpresfun_bigmaxE n t :
  nnpresfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof.
rewrite /nnpresfun_bigmax; elim/big_ind2 : _ => [|x g y h <- <-//|//].
by rewrite /= presfun_cstE.
Qed.

End nnpresfun_iter.

Module SFun.
Record t (T : measurableType) (R : realType) :=
  mk {f :> presfun T R ; _ : forall k, measurable (spimg f k) }.
Module Exports.
Notation sfun := SFun.t.
End Exports.
End SFun.
Export SFun.Exports.
Coercion SFun.f : sfun >-> PreSFun.t.
Arguments SFun.mk {T R} _ _.

Section sfun_lemmas.
Variables (T : measurableType) (R : realType) (f : sfun T R).

Lemma measurable_spimg k : measurable (spimg f k).
Proof. by case: f k. Qed.

Local Hint Extern 0 (measurable (spimg _ _)) => solve [apply: measurable_spimg] : core.

Lemma measurable_sfun (D : set T) : measurable D -> measurable_fun D f.
Proof. exact/measurable_presfun. Qed.

Lemma sfun_measurable_preimage_set1 (r : R) : measurable (f @^-1` [set r]).
Proof. exact/presfun_measurable_preimage_set1. Qed.

End sfun_lemmas.
Hint Extern 0 (measurable (spimg _ _)) => solve [apply: measurable_spimg] : core.

Section sfun_cst.
Variables (T : measurableType) (pt : T) (R : realType) (r : R).
Let rng := sfun_cst_rng r.
Let f (t : T) := sfun_cst_f r t.
Let pi := fun k : 'I_1 => f @^-1` [set rng`_k].

Let sfun_cst_mpi (k : 'I_(ssize (presfun_cst pt r))) :
  measurable (spimg (presfun_cst pt r) k).
Proof.
rewrite (_ : spimg _ _ = setT)// predeqE => t; split => // _.
rewrite /spimg /preimage /= presfun_cstE srng_presfun_cst.
rewrite ssize_presfun_cst in k *.
by rewrite (ord1 k).
Qed.

Definition sfun_cst := SFun.mk (presfun_cst pt r) sfun_cst_mpi.

Lemma sfun_cstE x : sfun_cst x = r.
Proof. by rewrite /sfun_cst /= presfun_cstE. Qed.

End sfun_cst.

Section sfun_ind1.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (A : set T) (mA : measurable A).
Let g (x : T) : R := sfun_ind1_f R (*TODO: implicits of sfun_ind1?*)A x.
Let rng := sfun_ind1_rng R A.
Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Lemma sfun_ind1_spimg (k : 'I_(ssize (presfun_ind1 pt A))) :
  measurable (spimg (presfun_ind1 (R := R) pt A) k).
Proof.
rewrite /spimg srng_presfun_ind1; apply: measurable_presfun_ind1 => //.
exact: measurable_set1.
Qed.

Definition sfun_ind1 := SFun.mk _ sfun_ind1_spimg.

Lemma sfun_ind1E x : sfun_ind1 x = (x \in A)%:R.
Proof. by rewrite /sfun_ind1 /= presfun_ind1E. Qed.

End sfun_ind1.
Arguments sfun_ind1 {T R} _ {A} _.

Section sfun_scale.
Variables (T : measurableType) (pt : T) (R : realType) (r : R).
Variable (f : sfun T R).
Let n := ssize f.
Let rng := sfun_scale_rng r f.
Let g := sfun_scale_f r f.
Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Let sfun_scale_spimg (k : 'I_(ssize (presfun_scale pt r f))) :
  measurable (spimg (presfun_scale pt r f) k).
Proof.
Proof.
have [r0|r0] := eqVneq r 0.
  rewrite [spimg _ _](_ : mkset _ = setT)//= predeqE => t; split => //= _.
  rewrite presfun_scaleE srng_presfun_scale.
  move: k; rewrite ssize_presfun_scale /sfun_scale_rng r0 eqxx /= => k.
  by rewrite mul0r (ord1 k).
move=> [:k'n]; have @k' : 'I_n.
  apply: (@Ordinal _ k); abstract: k'n.
  rewrite /ssize /= (leq_trans (ltn_ord k)) // /rng.
  by rewrite ssize_presfun_scale /sfun_scale_rng (negbTE r0) size_map.
rewrite (_ : spimg _ _ = spimg f k') //; first exact: measurable_spimg.
rewrite predeqE => t; split.
  rewrite /spimg /preimage /= presfun_scaleE srng_presfun_scale.
  rewrite /sfun_scale_rng (negbTE r0) (nth_map 0) //.
  by apply: mulrI; rewrite unitfE.
rewrite /spimg /preimage /= presfun_scaleE srng_presfun_scale => ->.
transitivity ([seq r * x | x <- srng f]`_k); first by rewrite (nth_map 0).
by congr (_ `_ _); rewrite /rng /sfun_scale_rng (negbTE r0).
Qed.

Definition sfun_scale := locked (SFun.mk (presfun_scale pt r f) sfun_scale_spimg).

Lemma sfun_scaleE x : sfun_scale x = r * f x.
Proof. by rewrite /sfun_scale; unlock => /=; rewrite presfun_scaleE. Qed.

Lemma ssize_sfun_scale : ssize sfun_scale = size (sfun_scale_rng r f).
Proof. by rewrite /sfun_scale; unlock => /=; rewrite ssize_presfun_scale. Qed.

Lemma srng_sfun_scale : srng sfun_scale = sfun_scale_rng r f.
Proof. by rewrite /sfun_scale; unlock => /=; rewrite srng_presfun_scale. Qed.

End sfun_scale.

Section sfun_scale_lemmas.
Variables (T : measurableType) (pt : T) (R : realType) (r : R) (f : sfun T R).
Variables (m : {measure set T -> \bar R}).

Lemma ssize_sfun_scale0 : ssize (sfun_scale pt 0 f) = 1%N.
Proof. by rewrite ssize_sfun_scale /sfun_scale_rng /= eqxx. Qed.

Lemma ssize_sfun_scale_neq0 : r != 0 -> ssize (sfun_scale pt r f) = ssize f.
Proof.
by move=> r0; rewrite ssize_sfun_scale /sfun_scale_rng /= (negbTE r0) size_map.
Qed.

End sfun_scale_lemmas.

Section sfun_proj.
Variables (T : measurableType) (pt : T) (R : realType) (f : sfun T R).
Variables (A : set T) (mA : measurable A).
Let g (x : T) : R := sfun_proj_f f A x.
Let rng := sfun_proj_rng f A.
Let pi := fun k : 'I_(size rng) => g @^-1` [set rng`_k].

Lemma sfun_proj_spimg (k : 'I_(ssize (presfun_proj f A))) :
  measurable (spimg (presfun_proj f A) k).
Proof.
rewrite /pi; set a := rng`_k; have [a0|a0] := eqVneq a 0.
- rewrite (_ : spimg _ _ = (f @^-1` [set a] `&` A) `|` ~` A); last first.
    rewrite predeqE => t; split;
        rewrite /spimg /preimage /= presfun_projE srng_presfun_proj /=.
      have [tA|tA _] := boolP (t \in A).
        by rewrite mulr1 => ->; left; split => //; rewrite inE in tA.
      by right; rewrite /setC /=; rewrite notin_set in tA.
    move=> [[-> At]|]; first by rewrite mem_set// mulr1.
    by rewrite /setC /=; rewrite -notin_set => /negbTE => ->; rewrite mulr0.
  apply: measurableU; last by apply: measurableC.
  apply: measurableI => //.
  have [fa|fa] := boolP (a \in srng f).
    move: fa => /(nthP 0)[i fi fia].
    by rewrite -fia (_ : _ @^-1` _ = spimg f (Ordinal fi)).
  rewrite (_ : _ @^-1` _ = set0)// predeqE => t; split => // fta.
  by move/negP : fa; apply; rewrite -fta; exact: mem_srng.
rewrite (_ : spimg _ _ = (f @^-1` [set a] `&` A)); last first.
  rewrite predeqE => t; split;
      rewrite /spimg /preimage /= presfun_projE srng_presfun_proj /=.
    have [tA|tA] := boolP (t \in A).
      by rewrite mulr1 => ->; split => //; rewrite inE in tA.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE a0).
  by move=> [-> At]; rewrite mem_set// mulr1.
apply: measurableI => //; rewrite -[X in measurable X]setIT.
by apply: measurable_sfun => //; exact: measurable_set1.
Qed.

Definition sfun_proj := SFun.mk (presfun_proj f A) sfun_proj_spimg.

Lemma sfun_projE x : sfun_proj x = f x * (x \in A)%:R.
Proof. by rewrite /sfun_proj /= presfun_projE. Qed.

End sfun_proj.

Section sfun_ind.
Variables (T : measurableType) (pt : T) (R : realType) (r : R).
Variables (A : set T) (mA : measurable A).

Definition sfun_ind := sfun_scale pt r (sfun_ind1 pt mA).

Lemma sfun_indE x : sfun_ind x = r * (x \in A)%:R.
Proof. by rewrite /sfun_ind sfun_scaleE sfun_ind1E. Qed.

End sfun_ind.*)

Definition srng (T : Type) (R : ringType) x0 (D : set T)
  (f : {fimfun x0, D >-> R}) := fset_set (f @` D).
Definition ssize (T : Type) (R : ringType) x0 (D : set T)
  (f : {fimfun x0, D >-> R}) := #|` srng f|.
Definition spimg (T : Type) (R : ringType) x0 (D : set T)
  (f : {fimfun x0, D >-> R}) k := f @^-1` [set (srng f)`_k].

Lemma seq_of_finite_set (T : eqType) (A : set T) : finite_set A ->
  exists s : seq T , A =i [set x | x \in s] /\ uniq s.
Proof.
move=> /finite_seqP[s As]; exists (undup s); split; last exact: undup_uniq.
by move=> x;apply/idP/idP; rewrite 2!inE /= As mem_undup.
Qed.

Lemma mem_srng (T : measurableType) (R : realType) (f : {sfun [set: T] >-> R}) t
  : f t \in srng f.
Proof. by rewrite in_fset_set// inE; by exists t. Qed.

Section sfun_bin.
Variables (T : measurableType) (R : realType) (f g : {sfun [set: T] >-> R}).
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
  by apply/allpairsP; exists (f t, g t); split => //=; exact: mem_srng.
- rewrite /s mem_undup => /mapP[[i j]].
  rewrite mem_filter /= => /andP[/set0P[t []]].
  rewrite /mkset /set1 /mkset => fti gtj.
  move=> /allpairsP[[i' j']] /= [fi' gj'] [? ?]; subst i' j' => ->.
  by exists t => //; rewrite fti gtj.
Qed.

End sfun_bin.

(*Module NNSFun.
Record t (T : measurableType) (R : realType) :=
  mk {f : sfun T R ; ge0 : forall t, 0 <= f t }.
Module Exports.
Notation nnsfun := t.
End Exports.
End NNSFun.
Export NNSFun.Exports.
Coercion NNSFun.f : nnsfun >-> sfun.
Arguments NNSFun.mk {T R} _ _.

Hint Resolve NNSFun.ge0 : core.
*)

(* TODO: at least, rename *)
Lemma NNSFuncdom_ge0 (T : measurableType) (R : realType) (D : set T)
  (mD : measurable D) (f : {nnsfun D >-> R}) (r : R) : r \in srng f -> 0 <= r.
Proof.
rewrite in_fset_set; last exact/fimfunP.
by rewrite inE /= => -[x Dx <-]; exact/fun_ge0.
Qed.

(*
Lemma NNSFun_ge0 (T : measurableType) (R : realType) (D : set T)
    (mD : measurable D) (f : {nnsfun D >-> R}) (t : 'I_(ssize f)) :
  0 <= (srng f)`_t.
Proof.
by move=> /(nthP 0)[i fi <-]; rewrite lee_fin (NNSFun_ge0 (Ordinal fi)).
Qed.
*)

Lemma sintegral_ge0 (T : measurableType) (R : realType) (D : set T)
  (f : {nnsfun D >-> _}) (m : {measure set T -> \bar R}) :
  measurable D ->
  (0 <= sintegral m D f)%E.
Proof.
move=> mD; rewrite sintegralE; rewrite big_seq; apply: sume_ge0 => t tfD.
rewrite mule_ge0//; last exact/measure_ge0/measurable_sfunP.
by rewrite lee_fin; exact: (@NNSFuncdom_ge0 _ _ _ mD f).
Qed.

Section nnsfun_functions.
Variables (T : measurableType) (R : realType).

Lemma cst_nnfun_subproof (D : set T) (x : {nonneg R}) :
  @IsNonNegFun T R D (cst x%:nngnum).
Proof. by split=> t ?. Qed.
HB.instance Definition _ D x := @cst_nnfun_subproof D x.

Lemma cst_mfun_subproof (x : {nonneg R}) :
  @IsMeasurableFun T _ setT (cst x%:nngnum).
Proof. by split; exact: measurable_fun_cst. Qed.
HB.instance Definition _ x := @cst_mfun_subproof x.

Definition nnsfun_cst (r : {nonneg R}) :=
  [the {nnsfun setT >-> R} of cst r%:nngnum].
(*Program Definition nnsfun_cst (pt : T) (r : {nonneg R}) :=
  NNSFun.mk (sfun_cst pt r%:nngnum) _.
Next Obligation. by move=> pt r t; rewrite presfun_cstE. Qed.*)

Definition nnsfun0 : {nnsfun setT >-> R} := nnsfun_cst 0%R%:nng.

Lemma indic1_nnfun_subproof (D : set T) : @IsNonNegFun T R D (\1_D).
Proof. by split=> t ?. Qed.
HB.instance Definition _ D := @indic1_nnfun_subproof D.

Lemma indic1_mfun_subproof (D : set T) :
  measurable D -> measurable_fun setT (\1_D : _ -> R)
(*  @IsMeasurableFun T _ setT (\1_D : _ -> R)*).
Proof.
move=> mD B mB; rewrite setTI (_ : _ @^-1` _ = if 1 \in B then
    if 0 \in B then setT else D
  else if 0 \in B then ~` D else set0); last first.
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
by case: ifPn => B1; case: ifPn => B0 //; exact: measurableC.
Qed.

(*Program Definition nnsfun_ind1 (pt : T) (A : set T)
  (mA : measurable A) := NNSFun.mk (sfun_ind1 (R := R) pt mA) _.
Next Obligation. by move=> pt A mA t; rewrite sfun_ind1E. Qed.*)

(*Program Definition nnsfun_scale (pt : T) (f : nnsfun T R) (k : R) (k0 : 0 <= k)
  := NNSFun.mk (sfun_scale pt k f) _.
Next Obligation. by move=> pt f k k0 t; rewrite sfun_scaleE mulr_ge0. Qed.

Program Definition nnsfun_proj (f : nnsfun T R) (A : set T)
  (mA : measurable A) := NNSFun.mk (sfun_proj f mA) _.
Next Obligation. by move=> f A mA t; rewrite sfun_projE mulr_ge0. Qed.

Program Definition nnsfun_ind (pt : T) (r : {nonneg R}) (A : set T)
  (mA : measurable A) := NNSFun.mk (sfun_ind pt r%:nngnum mA) _.
Next Obligation.
by move=> pt r A mA t; rewrite /nnsfun_proj /= sfun_indE mulr_ge0.
Qed.

(* TODO: subsumed by presfun_indE? *)
Lemma nnsfun_indE (pt : T) (r : {nonneg R}) (A : set T) (mA : measurable A) x :
  nnsfun_ind pt r mA x = r%:nngnum * (x \in A)%:R.
Proof. by rewrite /nnsfun_ind; unlock; rewrite sfun_indE. Qed.*)

End nnsfun_functions.
Arguments nnsfun0 {T R}.

(* TODO: move to topology.v? *)
Reserved Notation "f \max g" (at level 50, left associativity).
Definition max_fun T (R : numDomainType) (f g : T -> R) x := maxr (f x) (g x).
Notation "f \max g" := (max_fun f g) : ring_scope.
Arguments max_fun {T R} _ _ _ /.

(* TODO: move to lebesgue_measure.v? *)
(* NB: this is similar to emeasurable_fun_max *)
Lemma measurable_fun_max (T : measurableType) (R : realType) D (f g : T -> R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (f \max g).
Proof.
move=> mD mf mg; apply: (measurability mD (RGenCInfty.measurableE R)) => //.
move=> _ [_ [x ->] <-]; rewrite [X in measurable X](_ : _ =
    (D `&` f @^-1` `[x, +oo[) `|` (D `&` g @^-1` `[x, +oo[)); last first.
  rewrite predeqE => t /=; split.
    by rewrite !preimage_itv /= !in_itv /= !andbT le_maxr => -[Dx /orP[|]];
      tauto.
  by move=> [|]; rewrite !preimage_itv /= !in_itv/= !andbT le_maxr;
    move=> [Dx ->]//; rewrite orbT.
by apply: measurableU; [exact/mf/measurable_itv|exact/mg/measurable_itv].
Qed.

Section nnfun_bin.
Variables (T : Type) (R : numDomainType) (D : set T) (f g : {nnfun D >-> R}).

Lemma add_nnfun_subproof : @IsNonNegFun T R D (f \+ g).
Proof. by split => x Dx; rewrite addr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := add_nnfun_subproof.

Lemma mul_nnfun_subproof : @IsNonNegFun T R D (f \* g).
Proof. by split => x Dx; rewrite mulr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := mul_nnfun_subproof.

Lemma max_nnfun_subproof : @IsNonNegFun T R D (f \max g).
Proof. by split => x Dx /=; rewrite /maxr; case: ifPn => _; apply: fun_ge0. Qed.
HB.instance Definition _ := max_nnfun_subproof.

End nnfun_bin.

Section fimfun_bin.
Variables (T : measurableType) (R : realType) (D : set T).
Variables (f g : {fimfun mpoint, D >-> R}).

Lemma add_fimfun_subproof : @FiniteImage T R mpoint D (f \+ g).
Proof. by split; apply: finite_image11. Qed.
HB.instance Definition _ := add_fimfun_subproof.

Lemma mul_fimfun_subproof : @FiniteImage T R mpoint D (f \* g).
Proof. by split; apply: finite_image11. Qed.
HB.instance Definition _ := mul_fimfun_subproof.

Lemma max_fimfun_subproof : @FiniteImage T R mpoint D (f \max g).
Proof. by split; apply: finite_image11. Qed.
HB.instance Definition _ := max_fimfun_subproof.

End fimfun_bin.

Section nnsfun_bin.
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
Arguments nnsfun_max {T R} _ _.

Section nnsfun_iter.
Variables (T : measurableType) (pt : T) (R : realType).
Variable f : {nnsfun @setT T >-> R}^nat.

Definition nnsfun_sum n := \big[nnsfun_add/nnsfun0]_(i < n) f i.

Lemma nnsfun_sumE n t : nnsfun_sum n t = \sum_(i < n) (f i t).
Proof. by rewrite /nnsfun_sum; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

Definition nnsfun_bigmax n := \big[nnsfun_max/nnsfun0]_(i < n) f i.

Lemma nnsfun_bigmaxE n t : nnsfun_bigmax n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /nnsfun_bigmax; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

End nnsfun_iter.

Lemma fset_set_comp (T1 : Type) (T2 T3 : choiceType) x0 (D : set T1)
    (f : {fimfun x0, D >-> T2}) (g : T2 -> T3) :
  fset_set [set (g \o f) x | x in D] =
  [fset g x | x in fset_set [set f x | x in D]]%fset.
Proof.
apply/fsetP => z; rewrite in_fset_set; last first.
  by rewrite -(image_comp f g); exact: finite_image.
apply/idP/idP => [|/imfsetP[r /=]].
  rewrite inE /= => -[x Dx <-{z}]; apply/imfsetP => /=; exists (f x) => //.
  by rewrite in_fset_set ?inE/=; [exists x|exact/fimfunP].
rewrite in_fset_set; last exact/fimfunP.
by rewrite inE => /= -[x Dx <-{r} ->{z}]; rewrite inE; exists x.
Qed.

Section sintegralrM.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variable (m : {measure set T -> \bar R}).
Variables (r : R) (D : set T) (mD : measurable D) (f : {nnsfun D >-> R}).

Lemma sintegralrM :
  sintegral m D (cst r \* f)%R = r%:E * sintegral m D f.
Proof.
have [->|r0] := eqVneq r 0%R.
  rewrite mul0e (_ : (_ \* _)%R = cst 0%R) ?sintegral0// funeqE => x /=.
  by rewrite mul0r.
rewrite sintegralE (fset_set_comp _ (fun x => r * x)%R).
rewrite big_imfset/=; last by move=> x y /= _ _ /mulfI; exact.
rewrite [in RHS]sintegralE [in RHS]big_seq ge0_sume_distrr; last first.
  move=> i ifD; rewrite mule_ge0// ?measure_ge0//; last exact/measurable_sfunP.
  by rewrite lee_fin; exact: (@NNSFuncdom_ge0 _ _ _ mD f).
rewrite -big_seq; apply eq_bigr => i _; rewrite muleA -EFinM.
congr (_ * m (_ `&` _)); apply/seteqP; rewrite /preimage /cst.
by split => x /=; [move/mulfI; exact|move=> <-].
Qed.

End sintegralrM.

Section sintegralD.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (D : set T).
Variables (mD : measurable D) (f g : {nnsfun @setT T >-> R}).
Variable m : {measure set T -> \bar R}.
Let n := ssize f.
Let p := ssize g.

Lemma sintegralD :
  sintegral m D (f \+ g)%R = sintegral m D f + sintegral m D g.
Proof.
rewrite [in LHS]/sintegral.
transitivity (\sum_(x <- fset_set [set of (f \+ g)%R]) x%:E * m (D `&` (f \+ g)%R @^-1` [set x])).
  admit.
transitivity (\sum_(x <- fset_set [set of f]) x%:E * m (D `&` f @^-1` [set x]) +
  \sum_(x <- fset_set [set of g]) x%:E * m (D `&` g @^-1` [set x])); last first.
  admit.
have fgE z : (f \+ g)%R @^-1` [set z] = [set x | f x + g x = z]%R by [].
have {fgE}fgE z : (f \+ g)%R @^-1` [set z] =
    \bigcup_(a in f @` setT) (f @^-1` [set a] `&` g @^-1` [set (z - a)%R]).
  rewrite fgE; apply/seteqP; split=> [x /= fgz|x [_ /= [x' _ <-]] []].
    have : (z - f x)%R \in [set of g].
      by rewrite inE /=; exists x=> //; rewrite -fgz (addrC (f x)) addrK.
    rewrite inE /= => -[x' _ gzf]; exists (z - g x')%R => /=.
      by exists x => //; rewrite gzf opprB addrC subrK.
    rewrite /preimage /=; split; first by rewrite gzf opprB addrC subrK.
    by rewrite gzf opprB addrC subrK -fgz (addrC (f x)) addrK.
  by rewrite /preimage /= => fxfx' gzf; rewrite gzf -fxfx' addrC subrK.
under eq_bigr do rewrite fgE.
rewrite {fgE}.
transitivity (\sum_(z <- fset_set [set of (f \+ g)%R]) z%:E *
    \sum_(a <- fset_set [set of f]) m
      (D `&` (f @^-1` [set a] `&` g @^-1` [set (z - a)%R]))).
  apply: eq_bigr => r _; congr (_ * _).
  rewrite setI_bigcupr -additive_fset//; last 2 first.
     - move=> r'; rewrite -(setIid D) -setIACA; apply: measurableI;
         apply: measurableI => //; rewrite -(setTI (_ @^-1` _));
         exact/measurable_sfunP.
     - apply/trivIset_setI/trivIsetP => i j _ _ ij; rewrite setIACA.
       by have /trivIsetP/(_ _ _ Logic.I Logic.I ij) -> :=
         @trivIset_preimage1 _ _ f setT; rewrite set0I.
  by rewrite bigcup_fset_set//; exact/fimfunP.
under eq_bigr.
  move=> i _.
  rewrite ge0_sume_distrr; last first.
    by move=> j _; apply: measure_ge0; apply: measurableI => //;
      apply: measurableI; rewrite -(setTI (_ @^-1` _)); exact/measurable_sfunP.
  over.
xxx
transitivity (\sum_(i < n) \sum_(l < p)
    ((srng f)`_i + (srng g)`_l)%:E * m (spimg f i `&` spimg g l `&` D)).
  rewrite /sintegral.
  under eq_bigr do rewrite measure_spimg_add//.
  transitivity (
    \sum_(i : 'I_(ssize (sfun_add f g))) \sum_(x in presfun_bin_idx i)
      ((srng f)`_x.1 + (srng g)`_x.2)%:E * m (spimg f x.1 `&` spimg g x.2 `&` D)).
    apply: eq_bigr => i _; rewrite ge0_sume_distrr //; last first.
      move=> kl _; rewrite measure_ge0 //; apply: measurableI => //.
      exact: measurableI.
    by apply: eq_bigr => x; rewrite !inE => /andP[] /eqP ->.
  rewrite [in RHS]pair_big /=.
  rewrite [in RHS](eq_bigl [pred x | x \in setX [set: _] [set: _]]); last first.
    by move=> [k l]; rewrite !inE.
  transitivity (\sum_(x in [set x|spimg f x.1 `&` spimg g x.2 != set0]%SET)
      ((srng f)`_x.1 + (srng g)`_x.2)%:E *
      m (spimg f x.1 `&` spimg g x.2 `&` D)); last first.
    rewrite big_mkcond; apply: eq_big => //; first by move=> x; rewrite !inE.
    move=> [x y] _; case: ifPn => //; rewrite inE negbK => /eqP -> /=.
    by rewrite set0I measure0 mule0.
  rewrite -(presfun_bin_idx_cover _ _ (fun x y => x + y)%R).
  rewrite partition_disjoint_bigcup //= => i j ij.
  (* NB: lemma? *)
  rewrite -setI_eq0; apply/negPn/negP => /set0Pn[[k l]].
  rewrite inE /= => /andP[]; rewrite 2!inE => /andP[/eqP -> _] /andP[+ _].
  by rewrite (nth_uniq _ _ _ (undup_uniq _)) //; exact/negP.
transitivity (\sum_(i < n) \sum_(l < p)
             ((srng f)`_i)%:E * m (spimg f i `&` spimg g l `&` D) +
             \sum_(i < p) \sum_(j < n)
             ((srng g)`_i)%:E * m (spimg g i `&` spimg f j `&` D)).
  rewrite [X in _ = _ + X]exchange_big /=.
  rewrite -big_split; apply: eq_bigr => i _ /=.
  rewrite -big_split; apply: eq_bigr => j _ /=.
  rewrite -[in RHS](setIC (spimg f i))/=.
  by rewrite EFinD ge0_muleDl //; [exact: NNSFun_ge0|exact: NNSFun_ge0].
congr (_ + _).
- apply eq_bigr => k _; rewrite -ge0_sume_distrr//; last first.
    move=> i; rewrite measure_ge0 //.
    by apply: measurableI => //; exact: measurableI.
  congr (_ * _); rewrite -additive_ord//.
  + by rewrite -big_distrl/= -big_distrr/= bigsetU_spimg setIT.
  + by move=> i; apply: measurableI => //; exact: measurableI.
  + exact/trivIset_setIr/trivIset_setI/trivIset_spimg.
- apply eq_bigr => k _; rewrite -ge0_sume_distrr//; last first.
    move=> i; rewrite measure_ge0 //.
    by apply: measurableI => //; exact: measurableI.
  rewrite -additive_ord//.
  + by rewrite -big_distrl/= -big_distrr/= bigsetU_spimg setIT.
  + by move=> i; apply: measurableI => //; exact: measurableI.
  + exact/trivIset_setIr/trivIset_setI/trivIset_spimg.
Qed.

End sintegralD.

Section le_sintegral.
Variables (T : measurableType) (R : realType) (pt : T).
Variable m : {measure set T -> \bar R}.
Implicit Types D : set T.

Lemma le_sintegral D (mD : measurable D) (f g : nnsfun T R) :
  (forall x, D x -> f x <= g x) -> (sintegral m D f <= sintegral m D g)%E.
Proof.
move=> fg.
pose gNf' := sfun_proj (sfun_add g (sfun_scale pt (-1) f)) mD.
have gNf0 : forall x, 0 <= gNf' x.
  move=> x /=; rewrite presfun_projE /= sfun_scaleE /= mulN1r.
  have [xD|xD] := boolP (x \in D); last by rewrite mulr0.
  by rewrite mulr1 subr_ge0; apply/fg; rewrite inE in xD.
pose gNf := NNSFun.mk _ gNf0.
have gfgf : {in D, g =1 sfun_add f gNf}.
  move=> x /=; rewrite presfun_projE /= => ->.
  by rewrite sfun_scaleE mulr1 addrCA mulN1r subrr addr0.
by rewrite (eq_sintegral m gfgf) sintegralD// lee_addl // sintegral_ge0.
Qed.

Lemma is_cvg_sintegral D (mD : measurable D) (f : (nnsfun T R)^nat) :
  (forall x, D x -> nondecreasing_seq (f ^~ x)) ->
  cvg (fun n => sintegral m D (f n)).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
by apply: le_sintegral => // => x Dx; apply/nd_f.
Qed.

End le_sintegral.

Section sintegral_nondecreasing_limit_lemma.
Variables (T : measurableType) (R : realType) (pt : T).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~ x).
Variable f : nnsfun T R.
Hypothesis gf : forall x, D x -> cvg (g^~ x) -> f x <= lim (g^~ x).

Let fleg c : (set T)^nat := fun n => [set x | c * f x <= g n x] `&` D.

Let nd_fleg c : {homo fleg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; rewrite /fleg; apply/subsetPset => x [/[swap] Dx] /= cfg.
by split => //=; move: cfg => /le_trans; apply; exact: nd_g.
Qed.

Let mfleg c n : measurable (fleg c n).
Proof.
rewrite /fleg; apply: measurableI => //.
rewrite [X in _ X](_ : _ = \big[setU/set0]_(y <- srng f)
    \big[setU/set0]_(x <- srng (g n) | c * y <= x)
      (f @^-1` [set y] `&` g n @^-1` [set x])).
  apply: bigsetU_measurable => r _; apply: bigsetU_measurable => r' crr'.
  by apply: measurableI; exact: sfun_measurable_preimage_set1.
rewrite predeqE => t; split => [/= cfgn|].
- rewrite -bigcup_set; exists (f t); first exact: mem_srng.
  rewrite -bigcup_set_cond; exists (g n t) => //.
  by apply/andP; split => //; exact: mem_srng.
- rewrite -bigcup_set => -[r /= rf].
  by rewrite /fleg -bigcup_set_cond => -[? /andP[? ?]] [/= -> ->].
Qed.

Let g1 c n := nnsfun_proj f (mfleg c n).

Let le_ffleg c : {homo (fun p x => g1 c p x): m n / (m <= n)%N >-> (m <= n)%O}.
Proof.
move=> m n mn; apply/asboolP => t; rewrite 2!presfun_projE ler_pmul//.
have [/=|] := boolP (t \in fleg c m); last by rewrite ler_nat.
rewrite inE => cnt.
by have := nd_fleg c mn => /subsetPset/(_ _ cnt) cmt; rewrite mem_set.
Qed.

Let bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = D.
Proof.
move=> c1; rewrite predeqE => x; split=> [[n _] []//|Dx].
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

Local Open Scope ereal_scope.

Lemma sum_srng_g1_f c n :
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
Qed.

(* lemma 1.6 *)
Lemma nd_sintegral_lim_lemma : sintegral mu D f <= lim (sintegral mu D \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu D f <= lim (sintegral mu D \o g).
  by apply/lee_mul01Pr => //; apply: sintegral_ge0.
move=> c /andP[c0 c1].
have cg1g n : c%:E * sintegral mu D (g1 c n) <= sintegral mu D (g n).
  rewrite -(sintegralrM pt mu c mD (g1 c n)).
  apply: (@le_sintegral _ _ _ _ _ _ (nnsfun_scale pt (g1 c n) (ltW c0))) => //=.
  have : forall m x, D x -> (c * g1 c m x <= g m x)%R.
    move=> m x Dx; rewrite /g1 presfun_projE /fleg /=; have [|] := boolP (x \in _).
      by rewrite inE => -[/=]; rewrite mulr1.
    by rewrite 2!mulr0 NNSFun.ge0.
  by move=> h t Dt; have := h n t Dt; rewrite sfun_scaleE.
suff {cg1g}<- : lim (fun n => sintegral mu D (g1 c n)) = sintegral mu D f.
  have is_cvg_g1 : cvg (fun n => sintegral mu D (g1 c n)).
    apply: is_cvg_sintegral => //= x Dx m n mn.
    by have /lefP/(_ x) := le_ffleg c mn; rewrite !presfun_projE.
  rewrite -ereal_limrM // lee_lim//.
  - exact: ereal_is_cvgrM.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu D (g1 c n)) --> sintegral mu D f by apply/cvg_lim.
rewrite [X in X --> _](_ : _ = fun n => \sum_(k < ssize f) ((srng f)`_k)%:E *
    mu (f @^-1` [set (srng f)`_k] `&` fleg c n `&` D)); last first.
  rewrite funeqE => n; rewrite sintegralE sum_srng_g1_f.
  rewrite big_tnth; apply: eq_bigr => i _.
  rewrite /tnth [in LHS](set_nth_default 0%R) //=.
  have [fi0|fi0] := eqVneq ((srng f)`_i) 0%R; first by rewrite fi0 // 2!mul0e.
  congr (_ * mu _); rewrite predeqE => x; split => [|[]] /=.
  - rewrite /preimage /= presfun_projE => -[/[swap] Dx].
    have [xcn|_] := boolP (_ \in fleg _ _).
      by rewrite mulr1 => <-; split => //; split=> //; rewrite inE in xcn.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE fi0).
  - rewrite /sfun_proj_f /preimage /= => -[fxi] cnx Dx.
    by rewrite presfun_projE; split => //; rewrite fxi mem_set// mulr1.
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
  by apply: measurableI => //; apply: measurableI;
    [exact: sfun_measurable_preimage_set1|exact: mfleg].
apply: ereal_lim_sum => [r n /NNSFuncdom_ge0 r0|r rf].
  by rewrite mule_ge0// measure_ge0.
apply: ereal_cvgrM => //.
rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n `&` D))); last first.
  by rewrite -setI_bigcupl -setI_bigcupr bigcup_fleg// -setIA setIid.
apply: cvg_mu_inc => //; first exact: measurable_bigcup.
move=> n m nm; apply/subsetPset; apply: setSI; apply: setIS.
by move/(nd_fleg c) : nm => /subsetPset.
Unshelve. all: by end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Variables (T : measurableType) (R : realType) (pt : T).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g : (nnsfun T R)^nat).
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~ x).
Variable f : nnsfun T R.
Hypothesis gf : forall x, D x -> g ^~ x --> f x.

Let limg : forall x, D x -> lim (g^~x) = f x.
Proof. by move=> x Dx; apply/cvg_lim; [exact: Rhausdorff| exact: gf]. Qed.

Lemma nd_sintegral_lim : sintegral mu D f = lim (sintegral mu D \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x Dx; rewrite -limg.
have : nondecreasing_seq (sintegral mu D \o g).
  by move=> m n mn; apply: (le_sintegral pt) => // x Dx; exact/nd_g.
move=> /ereal_nondecreasing_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=.
apply: le_sintegral => // x Dx.
rewrite -limg // (nondecreasing_cvg_le (nd_g Dx)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Section integral.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variable mu : {measure set T -> \bar R}.
Implicit Types (D : set T) (f g : T -> \bar R).

Definition nnintegral D f := ereal_sup [set sintegral mu D h |
  h in [set h : nnsfun T R | forall x, D x -> (h x)%:E <= f x]].

Lemma nnintegral_nnsfun D (h : nnsfun T R) : measurable D ->
  nnintegral D (EFin \o h) = sintegral mu D h.
Proof.
move=> mD; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gh <-]; exact: le_sintegral.
by apply: ereal_sup_ub => /=; exists h.
Qed.

Lemma nnintegral_ge0 D f : (forall x, D x -> 0 <= f x) -> 0 <= nnintegral D f.
Proof.
move=> f0; apply: ereal_sup_ub; exists (nnsfun0 pt); last by rewrite sintegral0.
by move=> x Dx; rewrite presfun_cstE; exact: f0.
Qed.

Lemma eq_nnintegral D g f : {in D, f =1 g} -> nnintegral D f = nnintegral D g.
Proof.
move=> fg; rewrite /nnintegral; congr ereal_sup; rewrite eqEsubset; split.
  by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite -fg// ?hf// inE.
by move=> _ /= [h hf <-]; exists h => // x Dx; rewrite fg// ?hf// inE.
Qed.
Arguments eq_nnintegral {D} _ {f} _.

Lemma nnintegral0 D : nnintegral D (cst 0) = 0.
Proof.
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub; exists (nnsfun0 pt); last by rewrite sintegral0.
  by move=> x Dx; rewrite presfun_cstE.
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, D x -> f x = 0%R.
  by move=> y ?; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin NNSFun.ge0.
rewrite (@eq_sintegral _ _ mu D f (nnsfun0 pt)) ?sintegral0//=.
by move=> y yD; rewrite f0 ?presfun_cstE//; rewrite inE in yD.
Qed.

Definition integral D f := nnintegral D (f ^\+) - nnintegral D (f ^\-).

Local Notation "\int_ D f 'd x" := (integral D (fun x => f))
  (at level 10, D, f at next level, format "'\int_'  D  f  ''d'  x").

Lemma eq_integral D f g : {in D, f =1 g} ->
  \int_ D (f x) 'd x = \int_ D (g x) 'd x.
Proof.
move=> fg; rewrite /integral (eq_nnintegral g^\+); last first.
  by move=> x /fg Dx; rewrite /funenng Dx.
by rewrite [X in _ - X = _](eq_nnintegral g^\-)// /funennp => x /fg ->.
Qed.

Lemma ge0_integralE D f : (forall x, D x -> 0 <= f x) ->
  \int_ D (f x) 'd x = nnintegral D f.
Proof.
move=> f0; rewrite /integral (eq_nnintegral _ (ge0_funenngE f0)).
by rewrite (eq_nnintegral _ (ge0_funennpE f0)) nnintegral0 sube0.
Qed.

Lemma integralE D f :
  \int_ D (f x) 'd x = \int_ D (f ^\+ x) 'd x - \int_ D (f ^\- x) 'd x.
Proof.
by rewrite [in LHS]/integral -ge0_integralE // -ge0_integralE.
Qed.

Lemma integral0 D : \int_ D (cst 0 x) 'd x = 0.
Proof. by rewrite ge0_integralE// nnintegral0. Qed.

Lemma ge0_integral D f : (forall x, D x -> 0 <= f x) -> 0 <= \int_ D (f x) 'd x.
Proof. by move=> f0; rewrite ge0_integralE// nnintegral_ge0. Qed.

Lemma integral_nnsfun D (h : nnsfun T R) : measurable D ->
  \int_ D ((EFin \o h) x) 'd x = sintegral mu D h.
Proof.
by move=> ?; rewrite -nnintegral_nnsfun// ge0_integralE// => x _; rewrite lee_fin.
Qed.

End integral.

Notation "\int_ D f 'd mu [ x ]" := (integral mu D (fun x => f)).
Notation "\int F 'd mu [ x ]" := (\int_ setT F 'd mu[x]).

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis f0 : forall x, D x -> 0 <= f x.
Hypothesis mf : measurable_fun D f.
Variable g : (nnsfun T R)^nat.
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~x).
Hypothesis gf : forall x, D x -> EFin \o g^~x --> f x.

Lemma nd_ge0_integral_lim : \int_ D (f x) 'd mu[x] = lim (sintegral mu D \o g).
Proof.
rewrite ge0_integralE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x Dx.
  have <- : lim (EFin \o g^~ x) = f x by apply/cvg_lim => //; apply: gf.
  have : (EFin \o g^~ x) --> ereal_sup [set of EFin \o g^~ x].
    apply: ereal_nondecreasing_cvg => p q pq /=; rewrite lee_fin.
    exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ub; exists n.
have := lee_pinfty (nnintegral mu D f).
rewrite le_eqVlt => /predU1P[mufoo|mufoo]; last first.
  have /ub_ereal_sup_adherent h : nnintegral mu D f \is a fin_num.
    by rewrite ge0_fin_numE // (nnintegral_ge0 pt mu f0).
  apply: lee_adde => e; have {h}[/= _ [[G Gf <-]]] := h e.
  rewrite EFinN lte_subl_addr// => fGe.
  have : forall x, D x -> cvg (g^~ x) -> (G x <= lim (g^~ x))%R.
    move=> x Dx cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := gf Dx; rewrite (le_trans (Gf _ Dx))// gxfx.
  move/(@nd_sintegral_lim_lemma _ _ pt mu _ mD _ nd_g).
  by move/(lee_add2r e%:num%:E)/(le_trans (ltW fGe)).
suff : lim (sintegral mu D \o g) = +oo by move=> ->; rewrite mufoo.
apply/eq_pinfty => r r0.
have [G [Gf rG]] : exists h : nnsfun T R, (forall x, D x -> (h x)%:E <= f x) /\
                                     (r%:E <= sintegral mu D h).
  move: (mufoo) => /eq_pinfty.
  have r20 : (0 < r + r)%R by rewrite addr_gt0.
  move/(_ _ r20) => r2.
  have {} : r%:E < ereal_sup [set sintegral mu D g0 | g0 in
       [set h : nnsfun T R | (forall x, D x -> (h x)%:E <= f x)]].
    by rewrite (lt_le_trans _ r2) // lte_fin ltr_addr.
  move/ereal_sup_gt => [x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, D x -> cvg (g^~ x) -> (G x <= lim (g^~ x))%R.
  move=> x Dx cg; rewrite -lee_fin -(EFin_lim cg).
  by have /cvg_lim gxfx := gf Dx; rewrite (le_trans (Gf _ Dx)) // gxfx.
move/(@nd_sintegral_lim_lemma _ _ pt mu _ mD _ nd_g) => Gg.
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
Variables (T : measurableType) (pt : T) (R : realType).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Local Notation I := (@dyadic_itv R).

Let A n k := (if (k < n * 2 ^ n)%N then
  [set x | f x \in EFin @` [set` I n k]] else set0) `&` D.

Let B n := [set x | n%:R%:E <= f x ]%E `&` D.

Definition approx : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * (x \in A n k)%:R +
  n%:R * (x \in B n)%:R.

(* technical properties of the sets A and B *)
Local Lemma mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]; last by rewrite set0I.
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
move=> fx0 i0; apply/negbTE; rewrite notin_set /A ltn_ord /=.
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
rewrite notin_set => -[/[swap] Dx] /=; apply/negP.
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
move=> fx0 n0; apply/negP; rewrite inE /B /= => -[/[swap] Dx] /=; apply/negP.
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
  move: (xAnk); rewrite inE {1}/A => -[/[swap] _] /=.
  rewrite kn /= inE => -[r] /dyadic_itv_subU[|] rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite inE; split => //; rewrite k2n /= inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0//.
    rewrite exprS invrM ?unitfE// ?expf_neq0// -muln2 natrM -mulrA (mulrCA 2).
    by rewrite divrr ?mulr1 ?unitfE.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite inE /A; split => //; rewrite k2n /= inE /=; exists r.
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
move=> Dx fxoo.
have fxfin : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
apply/(@cvg_distP _ [normedModType R of R^o]) => _/posnumP[e].
rewrite near_map.
have [fx0|fx0] := eqVneq (f x) 0%E.
  by near=> n; rewrite f0_approx0 // fx0 /= subrr normr0.
have /(fpos_approx_neq0 Dx) [m _ Hm] : (0 < f x < +oo)%E.
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

Lemma le_approx k x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  ((approx k x)%:E <= f x)%E.
Proof.
move=> Dx; have [fixoo|] := ltP (f x) (+oo%E); last first.
  by rewrite lee_pinfty_eq => /eqP ->; rewrite lee_pinfty.
have nd_ag : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; exact/lefP/nd_approx.
have fi0 : forall x, D x -> (0 <= f x)%E by move=> ?; exact: f0.
have cvg_af := cvg_approx fi0 Dx fixoo.
have is_cvg_af : cvg (approx ^~ x).
  by apply/cvg_ex; eexists; exact: cvg_af.
have {is_cvg_af} := nondecreasing_cvg_le nd_ag is_cvg_af k.
rewrite -lee_fin => /le_trans; apply.
rewrite -(@fineK _ (f x)); last first.
  by rewrite fin_numElt fixoo andbT (lt_le_trans _ (f0 _ Dx)) ?lte_ninfty.
by move/(cvg_lim (@Rhausdorff R)) : cvg_af => ->.
Qed.

Lemma dvg_approx x : D x -> f x = +oo%E -> ~ cvg (approx^~ x : _ -> R^o).
Proof.
move=> Dx fxoo.
have approx_x n : approx n x = n%:R.
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
by rewrite fin_numElt fxoo andbT (lt_le_trans _ (f0 _ Dx)) // lte_ninfty.
Qed.

Local Lemma k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by rewrite mulr_ge0 // invr_ge0 // -natrX ler0n. Qed.

Definition nnsfun_approx : (nnsfun T R)^nat := fun n => locked (nnsfun_add
  (nnsfun_sum pt
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => nnsfun_ind pt (Nonneg.NngNum _ (k2n_ge0 (Ordinal h))) (mA n k)
      | right _ => nnsfun0 pt
     end) (n * 2 ^ n)%N)
  (nnsfun_ind pt (Nonneg.NngNum _ (ler0n _ n)) (mB n))).

Lemma nnsfun_approxE n : nnsfun_approx n = approx n :> (T -> R).
Proof.
rewrite funeqE => t /=.
rewrite /nnsfun_approx; unlock.
rewrite /=.
rewrite nnsfun_sumE.
rewrite nnsfun_indE; congr (_ + _).
by apply: eq_bigr => i _; case: Bool.bool_dec => [h|/negP];
  [rewrite nnsfun_indE|rewrite ltn_ord].
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
  exists g : (nnsfun T R)^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~x --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|exact: cvg_nnsfun_approx].
Qed.

End approximation.

Section semi_linearity.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ge0_integralM_EFin k : (0 <= k)%R ->
  \int_ D (k%:E * f1 x) 'd mu[x] = k%:E * \int_ D (f1 x) 'd mu[x].
Proof.
move=> k0; have [g [nd_g gf1]] := approximation pt mf1 f10.
pose kg := fun n => nnsfun_scale pt (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ pt mu _ mD (fun x => k%:E * f1 x) _ kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu D (sfun_scale pt k (g n)))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu D (g n))).
    rewrite ereal_limrM //; last first.
      by apply: is_cvg_sintegral => // x Dx m n mn; apply/(lef_at x nd_g).
    rewrite -(nd_ge0_integral_lim pt mu mD f10) // => x Dx.
    exact/(lef_at x nd_g).
  by under eq_fun do rewrite (sintegralrM pt mu k mD).
- by move=> t Dt; rewrite mule_ge0// f10.
- by move=> x Dx m n mn; rewrite /kg !sfun_scaleE ler_pmul//; exact/lefP/nd_g.
- move=> x Dx.
  rewrite [X in X --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
    by apply: ereal_cvgrM => //; exact: gf1.
  by move=> t; rewrite /= sfun_scaleE.
Qed.

Lemma ge0_integralD : \int_ D ((f1 \+ f2) x) 'd mu[x] =
  \int_ D (f1 x) 'd mu[x] + \int_ D (f2 x) 'd mu[x].
Proof.
have [g1 [nd_g1 gf1]] := approximation pt mf1 f10.
have [g2 [nd_g2 gf2]] := approximation pt mf2 f20.
pose g12 := fun n => nnsfun_add (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ pt _ _ _ _ _ g12) //; last 3 first.
  - by move=> x Dx; rewrite adde_ge0 => //; [exact: f10|exact: f20].
  - by apply: nondecreasing_seqD => // x Dx;
      [exact/(lef_at x nd_g1)|exact/(lef_at x nd_g2)].
  - move=> x Dx.
    rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E)) ?funeqE//.
    apply: ereal_cvgD => //; [|exact: gf1|exact: gf2].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: f10|exact: f20].
rewrite (_ : _ \o _ =
    fun n => sintegral mu D (g1 n) + sintegral mu D (g2 n)); last first.
  by rewrite funeqE => n /=; rewrite sintegralD.
rewrite (nd_ge0_integral_lim pt _ _ _ (fun x _ => lef_at x nd_g1)) //.
rewrite (nd_ge0_integral_lim pt _ _ _ (fun x _ => lef_at x nd_g2)) //.
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
move=> f12.
have [g1 [nd_g1 gf1]] := approximation pt mf1 f10.
rewrite (nd_ge0_integral_lim pt _ _ f10 (fun x _ => lef_at x nd_g1) gf1)//.
apply: ereal_lim_le.
  by apply: is_cvg_sintegral => // t Dt; exact/(lef_at t nd_g1).
near=> n; rewrite ge0_integralE//; apply: ereal_sup_ub => /=.
exists (g1 n) => // t Dt; rewrite (le_trans _ (f12 _ Dt)) //.
have := gf1 _ Dt.
have := lee_pinfty (f1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite lee_pinfty.
have f1tfin : f1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (f10 Dt))// lte_ninfty.
have := gf1 _ Dt.
rewrite -(fineK f1tfin) => /ereal_cvg_real[ft_near].
set u_ := (X in X --> _) => u_f1 g1f1.
have <- : lim u_ = fine (f1 t) by apply/cvg_lim => //; exact: Rhausdorff.
rewrite lee_fin; apply: nondecreasing_cvg_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_g1.
by apply/cvg_ex; eexists; exact: u_f1.
Unshelve. all: by end_near. Qed.

End semi_linearity.

(* PR in progress *)
Section mul_def_lemmas.
Local Open Scope ereal_scope.
Variable (R : numDomainType).
Implicit Types x y : \bar R.

Lemma fin_num_mule_def x y : x \is a fin_num -> y \is a fin_num -> x *? y.
Proof.
move: x y => [x| |] [y| |] finx finy//.
by rewrite /mule_def negb_or 2!negb_and/= 2!orbT.
Qed.

Lemma mule_defP x y : x != 0 -> y \isn't a fin_num -> x *? y.
Proof.
by move: x y => [x| |] [y| |]// x0 _; rewrite /mule_def (negbTE x0).
Qed.

Lemma neq0_mule_def x y :  x * y != 0 -> x *? y.
Proof.
move: x y => [x| |] [y| |] //; first by rewrite fin_num_mule_def.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_defP.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_defP.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_defC mule_defP.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_defC mule_defP.
Qed.

End mul_def_lemmas.
(* /PR in progress *)

Lemma emeasurable_funN (T : measurableType) (pt : T) (R : realType) D (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D (fun x => - f x)%E.
Proof.
move=> mD mf.
apply: measurable_fun_comp => //.
exact: emeasurable_fun_minus.
Qed.

Section approximation_sfun.
Variables (T : measurableType) (pt : T) (R : realType).
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma approximation_sfun :
  exists g : (sfun T R)^nat, (forall x, D x -> EFin \o g^~x --> f x).
Proof.
have fp0 : (forall x, D x -> 0 <= f^\+ x)%E by [].
have mfp : measurable_fun D f^\+.
  by apply: emeasurable_fun_max => //; exact: measurable_fun_cst.
have fn0 : (forall x, D x -> 0 <= f^\- x)%E by [].
have mfn : measurable_fun D f^\-.
  apply: emeasurable_fun_max => //; first exact: emeasurable_funN.
  exact: measurable_fun_cst.
have [fp_ [fp_nd fp_cvg]] := approximation pt mfp fp0.
have [fn_ [fn_nd fn_cvg]] := approximation pt mfn fn0.
exists (fun n => sfun_add (fp_ n) (sfun_scale pt (-1) (fn_ n))) => x Dx /=.
rewrite [X in X --> _](_ : _ =
    (EFin \o fp_^~ x \+ (-%E \o EFin \o fn_^~ x))%E); last first.
  by rewrite funeqE => n /=; rewrite -EFinD// sfun_scaleE mulN1r.
rewrite (funenngnnp f); apply: ereal_cvgD.
- exact: add_def_funennpg.
- exact: fp_cvg.
- apply: ereal_cvgN.
  exact: fn_cvg.
Qed.

End approximation_sfun.

Section emeasurable_fun.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma emeasurable_funD D f g : measurable D ->
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \+ g).
Proof.
move=> mD mf mg.
have noom : measurable ([set -oo] : set (\bar R)) by exact: emeasurable_set1.
have poom : measurable ([set +oo] : set (\bar R)) by exact: emeasurable_set1.
have Cnoom : measurable (~` [set -oo] : set (\bar R)) by apply: measurableC.
have Cpoom : measurable (~` [set +oo] : set (\bar R)) by apply: measurableC.
have mfg :  measurable ([set x | f x +? g x] `&` D).
  suff -> : [set x | f x +? g x] =
              (f @^-1` (~` [set +oo]) `|` g @^-1` (~` [set -oo])) `&`
              (f @^-1` (~` [set -oo]) `|` g @^-1` (~` [set +oo])).
     by rewrite setIIl; apply: measurableI;
        rewrite setIUl; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /adde_def !(negb_and, negb_or).
   by rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
wlog fg : D mD mf mg mfg / forall x, D x -> f x +? g x => [hwlogD|]; last first.
  have [f_ f_cvg] := approximation_sfun pt mD mf.
  have [g_ g_cvg] := approximation_sfun pt mD mg.
  apply: (@emeasurable_fun_cvg _ _ _ (fun n x => (f_ n x + g_ n x)%:E)) => //.
    move=> n; apply/EFin_measurable_fun.
    by apply: measurable_funD => //; exact: measurable_sfun.
  move=> x Dx; under eq_fun do rewrite EFinD.
  by apply: ereal_cvgD; [exact: fg|exact: f_cvg|exact: g_cvg].
move=> A mA; wlog NAnoo: A mD mf mg mA / ~ (A -oo) => [hwlogA|].
  have [] := pselect (A -oo); last exact: hwlogA.
  move=> /(@setD1K _ -oo)<-; rewrite preimage_setU setIUl.
  apply: measurableU; last first.
    by apply: hwlogA=> //; [exact: measurableD|case => /=].
  have -> : (f \+ g) @^-1` [set -oo] = f @^-1` [set -oo] `|` g @^-1` [set -oo].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
     - by rewrite adde_eq_ninfty => /orP[] /eqP->; [left|right].
     - by move->.
     - by move->; rewrite addeC.
   by rewrite setIUl; apply: measurableU; [apply: mf|apply: mg].
have-> : (f \+ g) @^-1` A `&` D =
       (f \+ g) @^-1` A `&` ([set x | f x +? g x] `&` D).
  rewrite setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //.
  by case: (f x) (g x) Afgx => [rf||] [rg||].
have Dfg : [set x | f x +? g x] `&` D `<=` D by apply: subIset; right.
apply: hwlogD => //.
- apply: (measurable_funS mD) => //; do ?exact: measurableI.
- apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite setIA setIid.
- by move=> ? [].
Qed.

Lemma emeasurable_funB D f g : measurable D ->
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \- g).
Proof.
by move=> mD mf mg; apply: emeasurable_funD => //; exact: emeasurable_funN.
Qed.

Lemma emeasurable_funM D f g : measurable D ->
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \* g).
Proof.
move=> mD mf mg.
have m0 : measurable ([set 0] : set (\bar R)) by exact: emeasurable_set1.
have mC0 : measurable ([set~ 0] : set (\bar R)) by apply: measurableC.
have mCoo : measurable (~` [set -oo; +oo] : set (\bar R)).
  by apply/measurableC/measurableU; exact/emeasurable_set1.
have mfg :  measurable ([set x | f x *? g x] `&` D).
  suff -> : [set x | f x *? g x] =
              (f @^-1` (~` [set 0]) `|` g @^-1` (~` [set -oo; +oo])) `&`
              (g @^-1` (~` [set 0]) `|` f @^-1` (~` [set -oo; +oo])).
     by rewrite setIIl; apply: measurableI;
        rewrite setIUl; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /mule_def !(negb_and, negb_or).
   rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP).
   rewrite !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
   rewrite eqe_absl lee_pinfty andbT (orbC (g x == +oo)).
   by rewrite eqe_absl lee_pinfty andbT (orbC (f x == +oo)).
wlog fg : D mD mf mg mfg / forall x, D x -> f x *? g x => [hwlogM|]; last first.
  have [f_ f_cvg] := approximation_sfun pt mD mf.
  have [g_ g_cvg] := approximation_sfun pt mD mg.
  apply: (@emeasurable_fun_cvg _ _ _ (fun n x => (f_ n x * g_ n x)%:E)) => //.
    move=> n; apply/EFin_measurable_fun.
    by apply: measurable_funM => //; exact: measurable_sfun.
  move=> x Dx; under eq_fun do rewrite EFinM.
  by apply: ereal_cvgM; [exact: fg|exact: f_cvg|exact: g_cvg].
move=> A mA; wlog NA0: A mD mf mg mA / ~ (A 0) => [hwlogA|].
  have [] := pselect (A 0); last exact: hwlogA.
  move=> /(@setD1K _ 0)<-; rewrite preimage_setU setIUl.
  apply: measurableU; last first.
    apply: hwlogA=> //; last by case => /=.
    exact: measurableD.
  have -> : (fun x => f x * g x) @^-1` [set 0] = f @^-1` [set 0] `|` g @^-1` [set 0].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
       by rewrite mule_eq0 => /orP[] /eqP->; [left|right].
     by move=> ->; rewrite mul0e.
     by move=> ->; rewrite mule0.
   by rewrite setIUl; apply: measurableU; [apply: mf|apply: mg].
have-> : (fun x => f x * g x) @^-1` A `&` D =
       (fun x => f x * g x) @^-1` A `&` ([set x | f x *? g x] `&` D).
  rewrite setIA; congr (_ `&` _).
  apply/seteqP; split=> x; rewrite /preimage/=; last by case.
  move=> Afgx; split=> //; apply: neq0_mule_def.
  by apply: contra_notT NA0; rewrite negbK => /eqP <-.
have Dfg : [set x | f x *? g x] `&` D `<=` D by apply: subIset; right.
apply: hwlogM => //.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by apply: (measurable_funS mD) => //; do ?exact: measurableI.
- by rewrite setIA setIid.
- by move=> ? [].
Qed.

Lemma emeasurable_funeM D (f : T -> \bar R) (k : \bar R) : measurable D ->
  measurable_fun D f -> measurable_fun D (fun x => k * f x)%E.
Proof.
move=> mD mf; rewrite (_ : (fun x => k * f x) = (cst k) \* f)//.
exact/(emeasurable_funM mD _ mf)/measurable_fun_cst.
Qed.

Lemma emeasurable_funM_presfun_ind1 D N f :
  measurable N -> measurable D -> measurable_fun D f ->
  measurable_fun D (f \* (EFin \o presfun_ind1 pt N)).
Proof.
move=> mN mD mf; apply: emeasurable_funM => //.
by apply: measurable_fun_comp => //; exact: measurable_fun_presfun_ind1.
Qed.

End emeasurable_fun.

Section measurable_fun_sum.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variables (D : set T) (mD : measurable D).
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
Variables (T : measurableType) (pt : T) (R : realType).
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
- by move=> x Dx; apply f0.
- by move=> x Dx; apply: sume_ge0 => // k _; exact: f0.
- exact: measurable_fun_sum.
Qed.

End ge0_integral_sum.

Section monotone_convergence_theorem.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable g : (T -> \bar R)^nat.
Hypothesis mg : forall n, measurable_fun D (g n).
Hypothesis g0 : forall n x, D x -> 0 <= g n x.
Hypothesis nd_g : forall x, D x -> nondecreasing_seq (g^~ x).
Let f := fun x => lim (g^~ x).

Let is_cvg_g t : D t -> cvg (g^~ t).
Proof. by move=> ?; apply: ereal_nondecreasing_is_cvg => m n ?; apply/nd_g. Qed.

Local Definition g2' n : (T -> R)^nat := approx D (g n).
Local Definition g2 n : (nnsfun T R)^nat := nnsfun_approx pt (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : (nnsfun T R)^nat :=
  fun k => nnsfun_bigmax pt (g2^~ k) k.

Local Lemma max_g2E : max_g2 = max_g2' :> (T -> R)^nat.
Proof.
rewrite funeq2E => n t; rewrite nnsfun_bigmaxE.
by under eq_bigr do rewrite nnsfun_approxE.
Qed.

Let is_cvg_g2 n t : cvg (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvg => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Local Lemma nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!nnsfun_bigmaxE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
  by rewrite !nnsfun_approxE; exact/lefP/(nd_approx D (g i) ab).
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

Local Lemma max_g2_g k x : D x -> ((max_g2 k x)%:E <= g k x)%O.
Proof.
move=> Dx; rewrite nnsfun_bigmaxE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  by apply/bigmax_lerP; split => //; apply: g0.
rewrite (@big_morph _ _ EFin 0%:E maxe) //; last by move=> *; rewrite maxEFin.
apply: le_bigmax => i _; rewrite nnsfun_approxE /=.
rewrite (le_trans (le_approx _ _ _)) => //.
- by move=> t; exact: g0.
- exact/nd_g/ltnW.
Qed.

Local Lemma lim_max_g2_f t : D t -> lim (EFin \o max_g2 ^~ t) <= f t.
Proof.
move=> Dt; apply: lee_lim => //; first exact: is_cvg_g.
by near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Local Lemma lim_g2_max_g2 t n :
  lim (EFin\o g2 n ^~ t) <= lim (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //; near=> k; rewrite /= nnsfun_bigmaxE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (@bigmax_sup _ _ _ (Ordinal nk)).
Unshelve. all: by end_near. Qed.

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
- have h := dvg_approx Dt fntoo.
  have g2oo : lim (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/dvg_ereal_cvg.
    under [X in X --> _]eq_fun do rewrite nnsfun_approxE.
    exact/(nondecreasing_dvg_lt _ h)/lef_at/nd_approx.
  have -> : lim (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo lee_pinfty_eq => /eqP.
  by rewrite lee_pinfty.
- have approx_g_g := cvg_approx (g0 n) Dt fntoo.
  have <- : lim (EFin \o g2 n ^~ t) = g n t.
    have /cvg_lim <- // : EFin \o approx D (g n)^~ t --> g n t.
      move/cvg_comp : approx_g_g; apply.
      by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
    rewrite (_ : _ \o _ = EFin \o approx D (g n) ^~ t)// funeqE => m.
    by rewrite [in RHS]/= -(nnsfun_approxE pt).
  exact: (le_trans _ (lim_g2_max_g2 t n)).
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int_ D (f x) 'd mu[x] = lim (fun n => \int_ D (g n x) 'd mu[x]).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => \int_ D (g n x) 'd mu[x]).
    move=> m n mn; apply: ge0_le_integral => //.
    - by move=> *; exact: g0.
    - by move=> *; exact: g0.
    - by move=> *; exact: nd_g.
  have ub n : \int_ D (g n x) 'd mu[x] <= \int_ D (f x) 'd mu[x].
    apply: ge0_le_integral => //.
    - by move=> *; exact: g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      by apply: nearW => k; exact/g0.
    - move=> x Dx; apply: ereal_lim_ge => //; first exact/is_cvg_g.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: ereal_lim_le => //; [exact:ereal_nondecreasing_is_cvg|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ pt mu _ _ _ _ max_g2) //; last 3 first.
  - move=> t Dt; apply: ereal_lim_ge => //; first exact/is_cvg_g.
    by apply: nearW => n; exact: g0.
  - by move=> t Dt m n mn; exact/lefP/nd_max_g2.
  - by move=> x Dx; exact: cvg_max_g2_f.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t Dt m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvg => // n m nm; apply: ge0_le_integral => //.
  + by move=> *; exact: g0.
  + by move=> *; exact: g0.
  + by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralE//; last by move=> *; exact: g0.
  by apply: ereal_sup_ub; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  (fun n => \int_ D (g n x) 'd mu[x]) --> \int_ D (f x) 'd mu[x].
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvg => m n mn.
by apply ge0_le_integral => // t Dt; [exact: g0|exact: g0|exact: nd_g].
Qed.

End monotone_convergence_theorem.

Section integral_series.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
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
Variables (T : measurableType) (pt : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma ge0_integralM (k : \bar R) : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int_ D (k * f x)%E 'd mu[x] = k * \int_ D (f x) 'd mu[x].
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralM_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by exact: emeasurable_funeM.
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
rewrite (monotone_convergence pt mu mD mg g0 nd_g).
rewrite (_ : (fun _ => _) = (fun n => n%:R%:E * \int_ D (f x) 'd mu[x])); last first.
  by rewrite funeqE => n; rewrite ge0_integralM_EFin.
have : 0 <= \int_ D (f x) 'd mu[x] by exact: ge0_integral.
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
by rewrite invr_ge0; apply: le0R; exact: ge0_integral.
Unshelve. all: by end_near. Qed.

End ge0_integralM.

Section fatou.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int_ D (elim_inf (f^~ x)) 'd mu[x] <=
              elim_inf (fun n => \int_ D (f n x) 'd mu[x]).
Proof.
pose g n := fun x => ereal_inf [set f k x | k in [set k | k >= n]%N].
have mg :=  measurable_fun_ereal_inf mD mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
rewrite (monotone_convergence pt) //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: (ge0_le_integral pt) => //; [exact: g0|exact: g0|].
  move=> x Dx; apply: le_ereal_inf => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N -> \int_ D (g n x) 'd mu[x] <=
    ereal_inf [set \int_ D (f k x) 'd mu[x] | k in [set p | n <= p]%N].
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: (ge0_le_integral pt); [exact: mD|exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lb; exists k.
  exact.
Qed.

End fatou.

Section integralN.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType).
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
  by rewrite -ltNge (lt_le_trans _ (ge0_integral _ _ _))// ?lte_ninfty.
rewrite nfoo adde_defEninfty.
rewrite -lee_pinfty_eq -ltNge lte_pinfty_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE// [in RHS]integralE// nfoo [in RHS]addeC oppeD//.
  by rewrite funennpN.
by rewrite integralE// [in RHS]integralE// funenngN funennpN nfoo pfoo.
Qed.

Lemma ge0_integralN (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int_ D ((-%E \o f) x) 'd mu[x] = - \int_ D (f x) 'd mu[x].
Proof.
move=> f0; rewrite integralN // (eq_integral _ (ge0_funennpE _))// integral0//.
by rewrite oppe0 fin_num_adde_def.
Qed.

End integralN.

Section integral_cst.
Local Open Scope ereal_scope.
Variables (T : measurableType) (pt : T) (R : realType) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma sintegral_cst (x : {nonneg R}) :
  sintegral mu D (nnpresfun_cst pt x) = x%:nngnum%:E * mu D.
Proof.
rewrite sintegralE/= srng_presfun_cst big_cons big_nil adde0; congr (_ * _)%E.
rewrite [X in mu (X `&` _)](_ : _ = setT) ?setTI// predeqE => t.
by rewrite /preimage /= presfun_cstE.
Qed.

Lemma integral_cst (r : R) : (0 <= r)%R ->
  \int_ D ((EFin \o cst r) x) 'd mu[x] = r%:E * mu D.
Proof.
move=> r0; rewrite ge0_integralE//.
rewrite (_ : cst r = nnsfun_cst pt (Nonneg.NngNum _ r0)) //.
(*TODO: implicts of NNgnum?*)
  by rewrite nnintegral_nnsfun// sintegral_cst.
by rewrite /nnsfun_cst /= funeqE => t; rewrite presfun_cstE.
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
Variables (T : measurableType) (pt : T) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

(* TODO: use \int_ *)
Lemma sintegral_nnpresfun_ind (x : {nonneg R}) (E : set T) :
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
  by rewrite mulr0 => /esym/eqP; rewrite (negbTE x0).
by rewrite /preimage /= presfun_indE mem_set// mulr1.
Qed.

Lemma sintegral_nnsfun_scale (k : R) (E : set T) (f : nnsfun T R)
  (k0 : (0 <= k)%R) : measurable E ->
  sintegral mu D (nnsfun_scale pt f k0) = k%:E * sintegral mu D f.
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
Qed.

(* TODO: tool long *)
Lemma sintegral_presfun_proj (A : set T) (E : set T) (mE : measurable E)
    (g : presfun T R) : E `<=` A ->
  sintegral mu A (presfun_proj g E) = sintegral mu E g.
Proof.
move=> EA; rewrite 2!sintegralE srng_presfun_proj /sfun_proj_rng.
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

Lemma sintegral_nnsfun_proj (A : set T) (E : set T) (mE : measurable E)
    (g : nnsfun T R) : E `<=` A ->
  sintegral mu A (nnsfun_proj g mE) = sintegral mu E g.
Proof. by move=> EA; rewrite sintegral_presfun_proj. Qed.

Lemma integral_EFin_nnpresfun_ind (r : {nonneg R}) (E : set T) :
  measurable E ->
  \int_ D ((EFin \o nnpresfun_ind pt r E) x) 'd mu[x] =
  r%:nngnum%:E * mu (E `&` D).
Proof.
move=> mE.
rewrite ge0_integralE//; last by move=> t Dt; rewrite lee_fin.
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
rewrite ge0_integralN//; last by move=> t Dt; rewrite lee_fin.
by rewrite integral_EFin_nnpresfun_ind//= EFinN mulNe oppeK.
Qed.

Lemma integral_EFin_presfun_ind1 (E : set T) :
  measurable E ->
  \int_ D ((EFin \o presfun_ind1 pt E) x) 'd mu[x] = mu (E `&` D).
Proof.
move=> mE.
transitivity (\int_ D ((EFin \o presfun_ind pt 1%R E) x) 'd mu[x]).
  apply eq_integral => x xD.
  by rewrite /= presfun_ind1E presfun_indE mul1r.
by rewrite integral_EFin_nnpresfun_ind// mul1e.
Qed.

End integral_ind.

Section subset_integral.
Variables (T : measurableType) (pt : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma subset_integral (A B : set T) (f : T -> \bar R) :
  (forall x, B x -> 0 <= f x)%E -> measurable A ->
  A `<=` B -> (\int_ A (f x) 'd mu[x] <= \int_ B (f x) 'd mu[x])%E.
Proof.
move=> f0 mA AB.
rewrite ge0_integralE//; last by move=> x /AB; exact: f0.
rewrite ge0_integralE//; apply: le_ereal_sup => _ /= -[] g gf <-.
exists (nnsfun_proj g mA).
  move=> t Bt; rewrite presfun_projE.
  have [tA|tA] := boolP (t \in A).
    by rewrite mulr1 gf//; rewrite inE in tA.
  by rewrite mulr0 f0.
by rewrite sintegral_presfun_proj.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> 0 < a ->
  (a%:E * mu ([set x | (`|g x| >= a%:E)%E] `&` D) <= \int_ D `|g x| 'd mu[x])%E.
Proof.
move=> mg a0.
have ? : measurable ([set x | (a%:E <= `|g x|)%E] `&` D).
  by apply: emeasurable_fun_c_infty => //; exact: measurable_fun_comp.
apply: (@le_trans _ _ (\int_ ([set x | (`|g x| >= a%:E)%E] `&` D) `|g x|%E 'd mu[x])).
  apply: (@le_trans _ _ (\int_ ([set x | (`|g x| >= a%:E)%E] `&` D) (cst a%:E x) 'd mu[x])).
    by rewrite integral_cst// ltW.
  apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite ltW.
  - exact: measurable_fun_cst.
  - by move=> x /= [].
by apply: subset_integral => //; apply: subIset; right.
Qed.

End subset_integral.

Section simple_function_integral2.
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

End simple_function_integral2.

Section simple_function_integral3.
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
by rewrite integral_EFin_presfun_ind1//; exact: measurable_spimg.
Qed.

End simple_function_integral3.

Section Rintegral.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variable (mu : {measure set T -> \bar R}).
Implicit Types D : set T.

Definition Rintegral D (f : T -> \bar R) := fine (\int_ D (f x) 'd mu[x]).

End Rintegral.

Section integrable.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variable mu : {measure set T -> \bar R}.
Implicit Types (D : set T) (f : T -> \bar R).

Definition integrable D f :=
  measurable_fun D f /\ (\int_ D `|f x| 'd mu[x] < +oo).

Lemma eq_integrable D f1 f2 : measurable D -> {in D , f1 =1 f2} ->
  integrable D f1 -> integrable D f2.
Proof.
move=> mD f12 [mf1 if1]; split; first exact: eq_measurable_fun mf1.
rewrite (le_lt_trans _ if1)//; apply ge0_le_integral=> //.
  by apply: measurable_fun_comp => //; exact: eq_measurable_fun mf1.
by move=> x Dx; rewrite f12// inE.
Qed.

Lemma le_integrable D (f1 f2 : T -> \bar R) :
  measurable D -> measurable_fun D f1 -> (forall x, D x -> `|f1 x| <= `|f2 x|) ->
  integrable D f2 -> integrable D f1.
Proof.
move=> mD mf1 f1f2 [mf2 f2oo]; split => //; rewrite (le_lt_trans _ f2oo) //.
by apply: ge0_le_integral => //; exact: measurable_fun_comp.
Qed.

Lemma integrableN D (f : T -> \bar R) : measurable D ->
  integrable D f -> integrable D (-%E \o f).
Proof.
move=> mD [mf foo]; split; last by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; apply: measurable_fun_comp => //; exact: emeasurable_fun_minus.
Qed.

Lemma integrableK D (k : R) (f : T -> \bar R) : measurable D ->
  integrable D f -> integrable D (fun x => k%:E * f x).
Proof.
move=> mD [mf foo]; split; first exact: emeasurable_funeM.
under eq_fun do rewrite abseM.
rewrite (ge0_integralM pt mu mD)// ?lte_mul_pinfty//.
exact: measurable_fun_comp.
Qed.

Lemma integrableD D (f1 f2 : T -> \bar R) : measurable D ->
  integrable D f1 -> integrable D f2 -> integrable D (f1 \+ f2).
Proof.
move=> mD  [mf1 f1oo] [mf2 f2oo]; split; first exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int_ D (`|f1 x| + `|f2 x|) 'd mu[x])).
  apply ge0_le_integral => //.
  - by apply: measurable_fun_comp => //; exact: emeasurable_funD.
  - by move=> *; exact: adde_ge0.
  - by move=> *; exact: lee_abs_add.
rewrite ge0_integralD //; first exact: lte_add_pinfty.
- exact: measurable_fun_comp.
- exact: measurable_fun_comp.
Qed.

Lemma integrableB D (f1 f2 : T -> \bar R) : measurable D ->
  integrable D f1 -> integrable D f2 -> integrable D (f1 \- f2).
Proof.
by move=> mD if1 if2; apply/(integrableD mD if1); exact/integrableN.
Qed.

Lemma integrable_add_def D f : measurable D -> integrable D f ->
  \int_ D (f^\+ x) 'd mu[x] +? - \int_ D (f^\- x) 'd mu[x].
Proof.
move=> mD [mf]; rewrite -[(fun x => _)]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
  - exact: emeasurable_fun_funenng.
  - exact: emeasurable_fun_funennp.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite lee_addl// ge0_integral.
- rewrite inE (@le_lt_trans _ _ 0)// ?lte_pinfty// lee_oppl oppe0.
  by rewrite ge0_integral.
Qed.

Lemma integral_funennp_lt_pinfty D f : measurable D -> integrable D f ->
  \int_ D (f^\- x) 'd mu[x] < +oo.
Proof.
move=> mD [mf]; apply: le_lt_trans; apply ge0_le_integral => //.
- by apply: emeasurable_fun_funennp => //; exact: emeasurable_funN.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funennp.
    by move: fx0; rewrite -{1}oppe0 -lee_oppr => /max_idPl ->.
  rewrite gee0_abs// /funennp.
  by move: (fx0); rewrite -{1}oppe0 -lee_oppl => /max_idPr ->.
Qed.

Lemma integral_funenng_lt_pinfty D f : measurable D ->  integrable D f ->
  \int_ D (f^\+ x) 'd mu[x] < +oo.
Proof.
move=> mD [mf]; apply: le_lt_trans; apply ge0_le_integral => //.
- by apply: emeasurable_fun_funenng => //; exact: emeasurable_funN.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funenng.
    by move: (fx0) => /max_idPr ->; rewrite -lee_oppr oppe0.
  by rewrite gee0_abs// /funenng; move: (fx0) => /max_idPl ->.
Qed.

End integrable.

Notation "mu .-integrable" := (integrable mu) : type_scope.

Section integrable_ae.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T) (f : T -> \bar R).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Hypotheses (mD : measurable D) (fint : mu.-integrable D f).

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite [X in measurable X](_ : _ = f @^-1` [set -oo; +oo] `&` D).
    by apply: fint.1 => //; apply: measurableU; exact: emeasurable_set1.
  rewrite predeqE => t; split=> [[/eqP ftoo Dt]|[]].
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
  exists (fine (\int_ D `|f x| 'd mu[x])); first exact/le0R/ge0_integral.
  move=> n.
  pose N : sfun T R := sfun_ind pt n%:R mE.
  have <- : \int_ D ((EFin \o N) x) 'd mu[x] = n%:R%:E * mu (E `&` D).
    by rewrite integral_EFin_sfun_ind //= 1?setIC.
  rewrite fineK//; last first.
    by case: fint => _ foo; rewrite ge0_fin_numE//; exact: ge0_integral.
  apply: ge0_le_integral => //.
  - by move=> *; rewrite lee_fin /N sfun_indE.
  - by apply/EFin_measurable_fun; exact: measurable_sfun.
  - move=> x Dx; rewrite /N /= sfun_indE.
    have [|xE] := boolP (x \in E); last by rewrite mulr0.
    by rewrite /E inE /= => -[->]; rewrite lee_pinfty.
apply/eqP/negPn/negP => /eqP muED0.
move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite lee_pinfty_eq => /eqP ->; exists 1%N; rewrite mul1e lee_pinfty_eq.
exists `|ceil (M * (fine (mu (E `&` D)))^-1)|%N.+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  rewrite fin_numElt muEDoo andbT.
  rewrite (lt_le_trans _ (measure_ge0 _ _))// ?lte_ninfty//.
  exact: measurableI.
rewrite lte_fin -ltr_pdivr_mulr.
  rewrite -addn1 natrD natr_absz ger0_norm.
    by rewrite (le_lt_trans (ceil_ge _))// ltr_addl.
  by rewrite ceil_ge0// divr_ge0//; apply/le0R/measure_ge0; exact: measurableI.
rewrite -lte_fin fineK.
  rewrite lt_neqAle measure_ge0// ?andbT; last exact: measurableI.
  suff: E `&` D = E by move=> ->; apply/eqP/nesym.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section linearityM.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Lemma integralM r : \int_ D (r%:E * f x) 'd mu[x] = r%:E * \int_ D (f x) 'd mu[x].
Proof.
have [r0|r0|->] := ltgtP r 0%R; last first.
  by under eq_fun do rewrite mul0e; rewrite mul0e integral0.
- rewrite [in LHS]integralE// gt0_funenngM// gt0_funennpM//.
  rewrite (ge0_integralM_EFin _ _ _ _ _ (ltW r0)) //; last first.
    by apply: emeasurable_fun_funenng => //; case: intf.
  rewrite (ge0_integralM_EFin _ _ _ _ _ (ltW r0)) //; last first.
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
Variables (T : measurableType) (R : realType) (pt : T).
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
  move=> h; rewrite [in LHS](integralE pt).
  move/eqP : h; rewrite -[in X in _ == X]addeA [in X in _ == X]addeC.
  have g12nng : \int_ D (g1^\+ x) 'd mu[x] + \int_ D (g2^\+ x) 'd mu[x] \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funenng_lt_pinfty.
    by apply adde_ge0; exact: ge0_integral.
  have g12nnp : \int_ D (g1^\- x) 'd mu[x] + \int_ D (g2^\- x) 'd mu[x] \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; apply: integral_funennp_lt_pinfty.
    by apply adde_ge0; exact: ge0_integral.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funennp_lt_pinfty.
        have : mu.-integrable D (g1 \+ g2) by exact: integrableD.
        exact: integral_funenng_lt_pinfty.
      apply: adde_ge0; last exact: ge0_integral.
      by apply: adde_ge0; exact: ge0_integral.
    - by rewrite adde_defC fin_num_adde_def.
  rewrite -(addeA (\int_ D ((g1 \+ g2)^\+ x) 'd mu[x])).
  rewrite (addeC (\int_ D ((g1 \+ g2)^\+ x) 'd mu[x])).
  rewrite -addeA (addeC (\int_ D (g1^\- x) 'd mu[x] + \int_ D (g2^\- x) 'd mu[x])).
  rewrite eq_sym -(sube_eq g12nng); last by rewrite fin_num_adde_def.
  move/eqP => <-.
  rewrite oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funennp_lt_pinfty if2.
    exact: ge0_integral.
  rewrite -addeA (addeCA (\int_ D (g2^\+ x) 'd mu[x])).
  by rewrite addeA -(integralE pt _ _ g1) -(integralE pt _ _ g2).
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
rewrite (ge0_integralD pt mu mD); last 4 first.
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
rewrite (ge0_integralD pt mu mD); last 4 first.
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
rewrite (ge0_integralD pt mu mD); last 4 first.
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
rewrite (ge0_integralD pt mu mD) //.
- apply: emeasurable_fun_funennp => //.
  by apply: emeasurable_funD => //; [case: if1|case: if2].
- by apply: emeasurable_fun_funenng => //; case: if1.
Qed.

End linearity.

Lemma integralB_EFin (R : realType) (T : measurableType) (pt : T)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R) :
  measurable D ->
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  \int_ D ((f1 x)%:E - (f2 x)%:E)%E 'd mu[x] =
    (\int_ D ((EFin \o f1) x) 'd mu[x] - \int_ D ((EFin \o f2) x) 'd mu[x])%E.
Proof.
move=> mD if1 if2; rewrite (integralD_EFin pt mD if1); last first.
  by rewrite (_ : _ \o _ = (fun x => - (f2 x)%:E))%E; [exact: integrableN|by []].
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Lemma le_abse_integral (T : measurableType) (R : realType) (pt : T)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f ->
  (`| \int_ D (f x) 'd mu[x]| <= \int_ D `|f x| 'd mu[x])%E.
Proof.
move=> mD mf.
rewrite (integralE pt) (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: ge0_integral.
rewrite gee0_abs; last exact: ge0_integral.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: emeasurable_fun_funenng | exact: emeasurable_fun_funennp].
Qed.

Section integral_presfun_ind1.
Variables (T : measurableType) (pt : T) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integral_presfun_ind1_setI (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  \int_ (E `&` D) (f x) 'd mu[x] = \int_ E (f x * (presfun_ind1 pt D x)%:E)%E 'd mu[x].
Proof.
move=> mE; rewrite /integral; congr (_ - _)%E.
  apply/eqP; rewrite eq_le; apply/andP; split.
    apply/le_ereal_sup => _ /= [g gf <-].
    exists (nnsfun_proj g (measurableI _ _ mE mD)); last first.
      rewrite /= sintegral_presfun_proj//; first exact: measurableI.
    move=> x Ex; have [xD|xD] := boolP (x \in D).
      rewrite /funenng presfun_ind1E xD mule1 presfun_projE in_setI xD andbT.
      by rewrite mem_set// mulr1 gf//; rewrite inE in xD.
    rewrite /funenng presfun_ind1E (negbTE xD) mule0 /=.
    by rewrite presfun_projE in_setI (negbTE xD) andbF mulr0 /maxe ltxx.
  apply/le_ereal_sup => _ /= [g gf <-]; exists g.
    move=> x [Ex Dx]; rewrite (le_trans (gf x _))//.
    by rewrite /funenng presfun_ind1E mem_set// mule1.
  rewrite -[LHS](@sintegral_presfun_proj _ _ _ E)//; last exact: measurableI.
  apply: eq_sintegral => x xE.
  rewrite presfun_projE//.
  have [xD|xD] := boolP (x \in D); first by rewrite in_setI xE xD mulr1.
  rewrite in_setI xE/= (negbTE xD) mulr0.
  apply/esym/eqP; rewrite eq_le NNSFun.ge0 andbT -lee_fin.
  rewrite (le_trans (gf _ _))//= /funenng ?presfun_ind1E ?(negbTE xD) ?mule0 /maxe ?ltxx//.
  by rewrite inE in xE.
(* NB: same as before modulo funenng/p and oppr0/oppe0 *)
apply/eqP; rewrite eq_le; apply/andP; split.
  apply/le_ereal_sup => _ /= [g gf <-].
    exists (nnsfun_proj g (measurableI _ _ mE mD)); last first.
      rewrite /= sintegral_presfun_proj//; first exact: measurableI.
    move=> x xE; have [xD|xD] := boolP (x \in D).
      rewrite /funennp presfun_ind1E xD mule1 presfun_projE in_setI xD andbT.
      by rewrite mem_set// mulr1 gf//; rewrite inE in xD.
    rewrite /funennp presfun_ind1E (negbTE xD) mule0 /=.
    by rewrite presfun_projE in_setI (negbTE xD) andbF mulr0 oppr0 /maxe ltxx.
  apply/le_ereal_sup => _ /= [g gf <-]; exists g.
    by move=> x [Ex Dx]; rewrite (le_trans (gf x _))// /funennp presfun_ind1E mem_set// mule1.
  rewrite -[LHS](@sintegral_presfun_proj _ _ _ E)//; last exact: measurableI.
  apply: eq_sintegral => x xE.
  rewrite presfun_projE//.
  have [xD|xD] := boolP (x \in D); first by rewrite in_setI xE xD mulr1.
  rewrite in_setI xE/= (negbTE xD) mulr0.
  apply/esym/eqP; rewrite eq_le NNSFun.ge0 andbT -lee_fin.
  rewrite (le_trans (gf _ _))//= /funennp ?presfun_ind1E ?(negbTE xD) ?mule0 /maxe ?oppe0 ?ltxx//.
  by rewrite inE in xE.
Qed.

Lemma integral_presfun_ind1 (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int_ D (f x) 'd mu[x] = \int_ D (f x * (presfun_ind1 pt D x)%:E)%E 'd mu[x].
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
  ae_eq D f g <-> ae_eq D f^\+ g^\+ /\ ae_eq D f^\- g^\-.
Proof.
split=> [[N [mN N0 DfgN]]|[[A [mA A0 DfgA] [B [mB B0 DfgB]]]]].
  by split; exists N; split => // x Dfgx; apply: DfgN => /=;
    apply: contra_not Dfgx => /= /[apply]; rewrite /funenng /funennp => ->.
exists (A `|` B); rewrite null_set_setU//; split=> //; first exact: measurableU.
move=> x /= /not_implyP[Dx fgx]; apply: contrapT => /not_orP[Ax Bx].
have [fgpx|fgnx] : f^\+ x <> g^\+ x \/ f^\- x <> g^\- x.
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
Variables (T : measurableType) (R : realType) (pt : T).
Variable (mu : {measure set T -> \bar R}).

Local Notation ae_eq := (ae_eq mu).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  ae_eq D f (cst 0) -> \int_ D `|f x|%E 'd mu[x] = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose f_neq0 := [set x | f x != 0] `&` D.
have mf_neq0 : measurable f_neq0 by exact: emeasurable_neq.
pose sfun_f : presfun T R := presfun_ind1 pt f_neq0.
have le_f_M : forall x, D x -> `|f x| <= M%:E * (sfun_f x)%:E.
  move=> t Dt; rewrite /sfun_f presfun_ind1E.
  have [|] := boolP (t \in f_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  rewrite notin_set /f_neq0 => /not_andP[/= /negP|//].
  by rewrite negbK => /eqP ->; rewrite abse0 mule0.
have f_neq0_eq0 : (mu f_neq0 = 0)%E.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
have : 0 <= \int_ D `|f x| 'd mu[x] <= `|M|%:E * mu f_neq0.
  apply/andP; split; first exact: ge0_integral.
  rewrite (_ : `|M| = `|M|%:nng%:nngnum)%R // /f_neq0.
  rewrite -[in X in _ <= X](setIid D) setIA -(integral_EFin_nnpresfun_ind pt) //.
  apply: ge0_le_integral => //.
  - by move=> n; exact: measurable_fun_comp.
  - by move=> t Dt /=; rewrite presfun_indE lee_fin.
  - move=> t Dt /=; rewrite presfun_indE.
    have [|] := boolP (t \in _).
      rewrite mulr1 /= => _; rewrite ger0_norm; first exact: fM.
      by rewrite -lee_fin (le_trans _ (fM _ Dt)).
    rewrite notin_set => /not_andP[|//].
    by rewrite mulr0 /= => /negP/negPn => /eqP ->; rewrite abse0.
by rewrite f_neq0_eq0 mule0 -eq_le => /eqP.
Qed.

(* TODO: too long *)
Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable_fun D f -> \int_ D `|f x| 'd mu[x] = 0 <-> ae_eq D f (cst 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists ([set x | f x != 0] `&` D); split; [exact: emeasurable_neq| |]; last first.
    by move=> t /= /not_implyP [Dt /eqP ft0].
  have muDf : forall a, (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x |]) = 0.
    move=> a a0; apply/eqP; rewrite eq_le measure_ge0 ?andbT; last first.
      rewrite setIC; apply: emeasurable_fun_c_infty => //.
      exact: measurable_fun_comp.
    move: (@le_integral_abse _ pt _ mu _ mD _ _ mf a0).
    by rewrite -lee_pdivl_mull// iDf0 mule0 setIC.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[ft0 /= Dt]|[n _ /= [Dt nft]]].
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
    - move=> i; rewrite setIC; apply: emeasurable_fun_c_infty => //.
      exact: measurable_fun_comp.
    - apply: measurable_bigcup => i; rewrite setIC.
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
move=> mD ND muN0 mf; rewrite (integral_presfun_ind1 pt)//.
rewrite (_ : (fun _ => _) = (fun x => `|f x * (presfun_ind1 pt N x)%:E|)); last first.
  rewrite funeqE => t; rewrite abseM //=; congr (_ * _).
  by rewrite ger0_norm// presfun_ind1E.
apply/ae_eq_integral_abs => //.
  apply: (measurable_funS _ _ ND) => //; apply: emeasurable_funM => //.
  by apply: measurable_fun_comp => //; exact: measurable_fun_presfun_ind1.
exists N; split => // t /= /not_implyP[_]; rewrite presfun_ind1E /=.
by have [|] := boolP (t \in N); rewrite ?inE ?mule0.
Qed.

(* TODO: move? *)
Lemma presfun_cplt (N : set T) (mN : measurable N) (f : T -> \bar R) :
  let oneCN := presfun_ind1 pt (~` N) in
  let oneN := presfun_ind1 pt N in
  f = (fun x => f x * (oneCN x)%:E) \+ (fun x => f x * (oneN x)%:E).
Proof.
move=> oneCN oneN; rewrite funeqE => x; rewrite !presfun_ind1E.
have [xN|xN] := boolP (x \in N).
  by rewrite mule1 in_setC xN mule0 add0e.
by rewrite in_setC xN mule0 adde0 mule1.
Qed.

Lemma negligible_integrable (D N : set T) (mN : measurable N) (f : T -> \bar R) :
  measurable D ->
  mu N = 0 -> measurable_fun D f -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> mD muN0 mf.
pose mCN := measurableC mN.
pose oneCN : presfun T R := presfun_ind1 pt (~` N).
pose oneN : presfun T R := presfun_ind1 pt N.
have intone : mu.-integrable D (fun x => f x * (oneN x)%:E).
  split; first exact: emeasurable_funM_presfun_ind1.
  (* NB: too long *)
  rewrite (_ : (fun _ => _) = (fun x => `|f x| * (presfun_ind1 pt N x)%:E)).
    rewrite -integral_presfun_ind1_setI// (@integral_abs_eq0 D)// ?lte_pinfty//.
    - exact: measurableI.
    - apply: (subset_measure0 _ _ _ muN0) => //.
      exact: measurableI.
  rewrite funeqE => x; rewrite abseM presfun_ind1E.
  by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
have h1 : mu.-integrable D f <-> mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intf|intCf].
    split.
      exact: emeasurable_funM_presfun_ind1.
    (* NB: too long *)
    rewrite (_ : (fun _ => _) = (fun x => `|f x| * (presfun_ind1 pt (~` N) x)%:E)); last first.
      rewrite funeqE => x; rewrite abseM presfun_ind1E.
      by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
    rewrite -integral_presfun_ind1_setI//.
    case: intf => _; apply: le_lt_trans.
    apply: subset_integral => //.
    exact: measurableI.
  split => //; rewrite (presfun_cplt mN f) -/oneCN -/oneN.
  apply: (@le_lt_trans _ _ (\int_ D (`|f x * (oneCN x)%:E| + `|f x * (oneN x)%:E|) 'd mu[x])).
    apply: ge0_le_integral => //.
    - apply: measurable_fun_comp => //; apply: emeasurable_funD => //.
      + exact: emeasurable_funM_presfun_ind1.
      + exact: emeasurable_funM_presfun_ind1.
    - by move=> *; exact: adde_ge0.
    - by move=> *; exact: lee_abs_add.
  rewrite ge0_integralD//; last 2 first.
    - by apply: measurable_fun_comp => //; exact: emeasurable_funM_presfun_ind1.
    - by apply: measurable_fun_comp => //; exact: emeasurable_funM_presfun_ind1.
  by apply: lte_add_pinfty; [case: intCf|case: intone].
have h2 : mu.-integrable (D `\` N) f <-> mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intCf|intCf].
    split; first exact: emeasurable_funM_presfun_ind1.
    (* NB: too long *)
    rewrite (_ : (fun _ => _) = (fun x => `|f x| * (presfun_ind1 pt (~` N) x)%:E)); last first.
      rewrite funeqE => x; rewrite abseM presfun_ind1E.
      by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
    rewrite -integral_presfun_ind1_setI //.
    case: intCf => _; apply: le_lt_trans.
    by apply: subset_integral => //; exact: measurableI.
  split.
    move=> A mA.
    rewrite setDE (setIC D) setICA (setIC (~` N)); apply: measurableI => //.
    exact: mf.
  case: intCf => _ intCf.
  rewrite (integral_presfun_ind1_setI pt)//.
  rewrite (_ : (fun _ => _) = (fun x => `|f x| * (presfun_ind1 pt (~` N) x)%:E))// in intCf.
  rewrite funeqE => x; rewrite abseM presfun_ind1E.
  by congr (_ * _); rewrite gee0_abs// lee_fin ler0n.
apply (iff_trans h1).
exact: iff_sym.
Qed.

Lemma negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D ->
  (forall x, D x -> 0 <= f x)%E ->
  mu N = 0 -> measurable_fun D f ->
  \int_ D (f x) 'd mu[x] = \int_ (D `\` N) (f x) 'd mu[x].
Proof.
move=> mN mD f0 muN0 mf.
rewrite {1}(presfun_cplt mN f) ge0_integralD//; last 4 first.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin presfun_ind1E].
  - by apply: emeasurable_funM_presfun_ind1 => //; exact: measurableC.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin presfun_ind1E].
  - exact: emeasurable_funM_presfun_ind1.
rewrite -(integral_presfun_ind1_setI pt)//; last exact: measurableC.
rewrite -(integral_presfun_ind1_setI pt)// [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite (@eq_integral _ _ mu _ _ (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite (@integral_abs_eq0 D)//; first exact: measurableI.
- by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) -> ae_eq D f g ->
  \int_ D (f x) 'd mu[x] = \int_ D (g x) 'd mu[x].
Proof.
move=> mD mf mg f0 g0 [N [mN N0 subN]].
rewrite (integral_presfun_ind1 pt)// [RHS](integral_presfun_ind1 pt)//.
rewrite (negligible_integral mN)//; last 2 first.
  - by move=> x; rewrite presfun_ind1E; have [xD|xD] := boolP (x \in D);
      [rewrite mule1 f0//; rewrite inE in xD|rewrite mule0].
  - exact: emeasurable_funM_presfun_ind1.
rewrite [RHS](negligible_integral mN)//; last 2 first.
  - move=> x; rewrite presfun_ind1E; have [xD|xD] := boolP (x \in D).
      by rewrite mule1 g0//; rewrite inE in xD.
    by rewrite mule0.
  - exact: emeasurable_funM_presfun_ind1.
- apply: eq_integral => x.
  rewrite in_setD => /andP[_ xN1].
  apply: contrapT; rewrite presfun_ind1E; have [xD|xD] := boolP (x \in D).
    rewrite !mule1.
    rewrite notin_set in xN1.
    apply: contra_not xN1 => fxgx; apply subN => /=.
    apply/not_implyP; split => //.
    by rewrite inE in xD.
  by rewrite !mule0.
Qed.

Lemma ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  ae_eq D f g -> integral mu D f = integral mu D g.
Proof.
move=> mD mf mg /ae_eq_funenng_funennp[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funenng|
                                      exact: emeasurable_fun_funenng].
by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funennp|
                                    exact: emeasurable_fun_funennp].
Qed.

Lemma ae_eq_ind1 (N : set T) : measurable N -> mu N = 0 ->
  ae_eq setT (fun x : T => (presfun_ind1 pt (~` N) x)%:E) (cst 1).
Proof.
exists N; split => // x /= /not_implyP[_].
rewrite presfun_ind1E.
by have [|xN] := boolP (x \in N); [rewrite inE|rewrite in_setC xN].
Qed.

End ae_eq_integral.

Lemma integrableM_ind1 (T : measurableType) (R : realType) (pt : T)
    (mu : {measure set T -> \bar R}) (D N : set T) (f : T -> \bar R) :
  measurable D -> measurable N ->
  mu.-integrable D f ->
  mu.-integrable D (fun x => f x * (presfun_ind1 pt N x)%:E)%E.
Proof.
move=> mD mN iTf; split.
  by apply: emeasurable_funM_presfun_ind1 => //; case: iTf.
rewrite integralE// lte_pinfty_eq; apply/orP; left.
rewrite fin_numB; apply/andP; split.
  rewrite ge0_fin_numE; last exact: ge0_integral.
  case: iTf => mf; apply: le_lt_trans.
  apply: ge0_le_integral => //.
  - apply: emeasurable_fun_funenng => //; apply: measurable_fun_comp => //.
    by apply: emeasurable_funM_presfun_ind1 => //; case: iTf.
  - move=> x Dx /=.
    (* TODO: lemma *)
    rewrite /funenng presfun_ind1E.
    have [xN|xN] := boolP (x \in N).
      by rewrite mule1 le_maxl lexx abse_ge0.
    by rewrite mule0 abse0 maxxx.
rewrite ge0_fin_numE; last exact: ge0_integral.
case: iTf => mf; apply: le_lt_trans.
apply: ge0_le_integral => //.
- apply: emeasurable_fun_funenng => //; apply: emeasurable_funN => //.
  apply: measurable_fun_comp => //.
  by apply: emeasurable_funM_presfun_ind1 => //; case: iTf.
- move=> x Dx /=.
  (* TODO: lemma *)
  rewrite /funennp presfun_ind1E.
  have [xN|xN] := boolP (x \in N).
    by rewrite mule1 le_maxl abse_ge0// andbT (le_trans _ (abse_ge0 _))// oppe_le0.
  by rewrite mule0 abse0 oppe0 maxxx.
Qed.

Section integralD.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralD : \int_ D ((f1 \+ f2) x) 'd mu[x] =
  \int_ D (f1 x) 'd mu[x] + \int_ D (f2 x) 'd mu[x].
Proof.
pose A := [set x | f1 x \is a fin_num] `&` D.
pose B := [set x | f2 x \is a fin_num] `&` D.
have mA : measurable A by apply emeasurable_fin_num => //; case: if1.
have mB : measurable B by apply emeasurable_fin_num => //; case: if2.
have mAB : measurable (A `&` B) by apply: measurableI.
pose g1 x := (fine (f1 x) * presfun_ind1 pt (A `&` B) x)%R.
pose g2 x := (fine (f2 x) * presfun_ind1 pt (A `&` B) x)%R.
have ig1 : mu.-integrable D (EFin \o g1).
  rewrite (_ : _ \o _ = f1 \* (EFin \o presfun_ind1 pt (A `&` B))) //.
    exact: integrableM_ind1.
  rewrite funeqE /g1 => x /=; rewrite !presfun_ind1E.
  have [|] := boolP (x \in A `&` B); last by rewrite mulr0 mule0.
  rewrite !in_setI => /andP[/andP[]].
  rewrite inE /= => f1xfin xD /andP[].
  rewrite inE /= => f2xfin _.
  by rewrite mule1 mulr1 fineK.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \* (EFin \o presfun_ind1 pt (A `&` B))) //.
    exact: integrableM_ind1.
  rewrite funeqE /g2 /= => x /=; rewrite !presfun_ind1E.
  have [|] := boolP (x \in A `&` B); last by rewrite mulr0 mule0.
  rewrite !in_setI => /andP[/andP[]].
  rewrite inE/= => f1xfin => xD /andP[].
  rewrite inE /= => f2xfin _.
  by rewrite mule1 mulr1 fineK.
transitivity (\int_ D ((EFin \o (g1 \+ g2)%R) x) 'd mu[x]).
  apply ae_eq_integral => //.
  - by apply: emeasurable_funD => //; [case: if1|case: if2].
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    by apply: emeasurable_funD => //; [case: ig1|case: ig2].
  - have [N1 [mN1 N10 subN1]] := integrable_ae pt mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae pt mD if2.
    exists (N1 `|` N2); split.
    + exact: measurableU.
    + by rewrite null_set_setU.
    + rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /g2 EFinD 2!EFinM fineK// fineK// !presfun_ind1E.
      have [|] := boolP (x \in A `&` B); first by rewrite 2!mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx) orbF /= notin_set.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// (integralD_EFin pt)//.
  congr (_ + _).
  + apply ae_eq_integral => //; [by case: ig1|by case: if1|].
    have [N1 [mN1 N10 subN1]] := integrable_ae pt mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae pt mD if2.
    exists (N1 `|` N2); split.
    * exact: measurableU.
    * by rewrite null_set_setU.
    * rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /= EFinM fineK// !presfun_ind1E.
      have [|] := boolP (x \in A `&` B); first by rewrite mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx) orbF /= notin_set.
  + apply ae_eq_integral => //;[by case: ig2|by case: if2|].
    have [N1 [mN1 N10 subN1]] := integrable_ae pt mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae pt mD if2.
    exists (N1 `|` N2); split.
    * exact: measurableU.
    * by rewrite null_set_setU.
    * rewrite -(setCK N1) -(setCK N2) -setCI.
      apply: subsetC => x [N1x N2x] /= Dx.
      move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
      move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
      rewrite /g1 /= EFinM fineK// !presfun_ind1E.
      have [|] := boolP (x \in A `&` B); first by rewrite mule1.
      by rewrite in_setI negb_and => /orP[|];
        rewrite in_setI negb_and /= (mem_set Dx) orbF /= notin_set.
Qed.

End integralD.

Section integralB.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralB : \int_ D ((f1 \- f2) x) 'd mu[x] =
                  \int_ D (f1 x) 'd mu[x] - \int_ D (f2 x) 'd mu[x].
Proof.
rewrite -[in RHS](@integralN _ pt _ _ _ f2); last exact: integrable_add_def.
by rewrite -[in RHS]integralD//; exact: integrableN.
Qed.

End integralB.

Section ae_measurable_fun.
Variables (T : measurableType) (R : realType) (pt : T).
Variables (mu : {measure set T -> \bar R}).
Hypothesis cmu : measure_is_complete mu.
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma ae_measurable_fun D f g : measurable D ->
  ae_eq mu D f g -> measurable_fun D f -> measurable_fun D g.
Proof.
move=> mD [N [mN N0 subN]] mf B mB.
apply: (measurability mD (ErealGenOInfty.measurableE R)) => // _ [_ [x ->] <-].
rewrite [X in measurable X](_ : _ = (f @^-1` `]x, +oo[ `&` D `&` ~` N)
    `|` (g @^-1` `]x, +oo[ `&` D `&` N)); last first.
  rewrite /preimage.
  apply/seteqP; split=> [y /= [gyxoo Dy]|y /= [[[fyxoo Dy] Ny]|[]//]].
  - have [->|fgy] := eqVneq (f y) (g y).
      have [yN|yN] := boolP (y \in N).
        by right; split => //; rewrite inE in yN.
      by left; split => //; rewrite notin_set in yN.
    by right; split => //; apply: subN => /= /(_ Dy); exact/eqP.
  - split => //; have [<-//|fgy] := eqVneq (f y) (g y).
    by exfalso; apply/Ny/subN => /= /(_ Dy); exact/eqP.
apply: measurableU.
- apply: measurableI; last exact/measurableC.
  exact/mf/emeasurable_itv_bnd_pinfty.
- by apply: cmu; exists N; split => //; apply: subIset; right.
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
Variables (T : measurableType) (R : realType) (pt : T).
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
Proof. exact: (emeasurable_fun_cvg mD mf_ f_f). Qed.

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
have := fatou pt mu mD mgg gg_ge0.
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
  by rewrite ge0_fin_numE// ge0_integral// => x Dx; rewrite mule_ge0 ?lee_fin ?g0.
rewrite [X in _ <= X -> _](_ : _ = \int_ D (2%:E * g x) 'd mu[x] + -
    elim_sup (fun n => \int_ D (g_ n x) 'd mu[x])); last first.
  rewrite (_ : (fun _ => _) = (fun n => \int_ D (2%:E * g x) 'd mu[x] +
      \int_ D (- g_ n x) 'd mu[x])); last first.
    rewrite funeqE => n; rewrite (integralB pt mD).
    - by rewrite -ge0_integralN// => x Dx//; rewrite /g_.
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
      apply: integrableD; [by []| by []|by []|].
      apply: le_integrable dominated_integrable => //.
      - exact: measurable_fun_comp.
      - by move=> x Dx; rewrite /= abse_id.
  rewrite elim_inf_shift // -elim_infN; congr (_ + elim_inf _).
  by rewrite funeqE => n /=; rewrite -ge0_integralN// => x Dx; rewrite /g_.
rewrite addeC -lee_subl_addr// subee// lee_oppr oppe0 => lim_ge0.
by apply/elim_sup_le0_cvg0 => // n; rewrite ge0_integral// => x _; rewrite /g_.
Qed.

Local Lemma dominated_cvg :
  (fun n => \int_ D (f_ n x) 'd mu[x]) --> \int_ D (f x) 'd mu[x].
Proof.
have h n : `| \int_ D (f_ n x) 'd mu[x] - \int_ D (f x) 'd mu[x] |
    <= \int_ D (g_ n x) 'd mu[x].
  rewrite -(integralB pt mD _ dominated_integrable); last first.
    by apply: le_integrable ig => // x Dx /=; rewrite (gee0_abs (g0 Dx)) absfg.
  by apply: le_abse_integral => //; exact: emeasurable_funB.
suff: (fun n => `| \int_ D (f_ n x) 'd mu[x] - \int_ D (f x) 'd mu[x]|) --> 0.
   move/ereal_cvg_abs0/ereal_cvg_sub0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   case: dominated_integrable => ?; apply: le_lt_trans.
   by apply: (le_trans _ (@le_abse_integral _ _ pt mu D f mD _)).
apply: (@ereal_squeeze _ (cst 0) _ (fun n => \int_ D (g_ n x) 'd mu[x])).
- by apply: nearW => n; rewrite abse_ge0//=; exact: h.
- exact: cvg_cst.
- exact: dominated_cvg0.
Qed.

End dominated_convergence_lemma.

Section dominated_convergence_theorem.
Local Open Scope ereal_scope.
Variables (T : measurableType) (R : realType) (pt : T).
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

Let ind1 N x : \bar R := (presfun_ind1 pt (D `\` N) x)%:E.

Theorem dominated_convergence : [/\ mu.-integrable D f,
  (fun n => \int_ D (g_ n x) 'd mu[x]) --> 0 &
  (fun n => \int_ D (f_ n x) 'd mu[x]) --> \int_ D (f x) 'd mu[x]].
Proof.
have [N1 [mN1 N10 subN1]] := f_f.
have [N2 [mN2 N20 subN2]] := absfg.
have [N3 [mN3 N30 subN3]] := integrable_ae pt mD ig.
pose N := N1 `|` N2 `|` N3.
have mN : measurable N by apply: measurableU => //; exact: measurableU.
have N0 : mu N = 0.
  by rewrite null_set_setU// ?null_set_setU//; exact: measurableU.
pose u := f \* ind1 N.
pose v := g \* ind1 N.
pose u_ := fun n => f_ n \* ind1 N.
have u_u x : D x -> u_ ^~ x --> u x.
  move=> Dx; rewrite /u_ /u /ind1 presfun_ind1E in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N).
    rewrite mule0/= [X in X --> _](_ : _ = cst 0)//; first exact: cvg_cst.
    by apply/funext => n; rewrite mule0.
  rewrite mule1 [X in X --> _](_ : _ = f_ ^~ x); last first.
    by apply/funext => n; rewrite mule1.
  apply: contraPP (xN) => h.
  apply/negP; rewrite negbK inE; left; left.
  by apply: subN1 => /= /(_ Dx); apply: contra_not h => h.
have u_v n x : D x -> `|u_ n x| <= v x.
  move=> Dx; rewrite /u_ /v /ind1 presfun_ind1E in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N); first by rewrite mule0/= normr0 mule0.
  rewrite !mule1; apply: contrapT => fg.
  move: xN; apply/negP; rewrite negbK inE; left; right.
  by apply: subN2 => /= /(_ n Dx).
have mu_ n : measurable_fun D (u_ n).
  apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
  by apply: measurable_fun_presfun_ind1 => //; exact: measurableD.
have iv : mu.-integrable D v.
  split.
    apply: emeasurable_funM => //; first by case: ig.
    apply: measurable_fun_comp => //.
    by apply: measurable_fun_presfun_ind1 => //; exact: measurableD.
  case: ig => _; apply: le_lt_trans; apply: ge0_le_integral => //.
    apply: measurable_fun_comp => //; apply: emeasurable_funM => //.
      by case: ig.
    apply: measurable_fun_comp => //.
    by apply: measurable_fun_presfun_ind1 => //; exact: measurableD.
  move=> x Dx; rewrite /v /ind1 presfun_ind1E in_setD mem_set//=.
  by case: (x \in N); rewrite ?mule1// mule0 abse0.
have finv x : D x -> v x \is a fin_num.
  move=> Dx.
  rewrite /v /ind1 presfun_ind1E in_setD mem_set//=.
  have [xN|xN] := boolP (x \in N); first by rewrite mule0.
  rewrite mule1.
  apply: contrapT => fing.
  move: xN; apply/negP; rewrite negbK inE; right.
  by apply: subN3 => /= /(_ Dx).
split.
- split => //.
  have : mu.-integrable D u.
    exact: (@dominated_integrable _ _ pt _ _ _ u_ _ u _ v).
  move=> [?]; apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/ae_eq_integral => //.
    exact: measurable_fun_comp.
    exact: measurable_fun_comp.
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x Nx Dx.
  by rewrite /= /u /= /ind1 presfun_ind1E in_setD mem_set//= memNset// mule1.
- have := @dominated_cvg0 _ _ pt _ _ mD _ mu_ _ u_u _ finv iv u_v.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //.
  apply/funext => n; apply ae_eq_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_funB => //.
    apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
    by apply: measurable_fun_presfun_ind1 => //; exact: measurableD.
  + by rewrite /g_; apply: measurable_fun_comp => //; exact: emeasurable_funB.
  + exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /u_ /u /ind1 presfun_ind1E in_setD mem_set//= memNset// !mule1.
- have := @dominated_cvg _ _ pt _ _ mD _ mu_ _ u_u _ finv iv u_v.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //; last first.
    apply/funext => n; apply ae_eq_integral => //.
    exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /u_ /u /ind1 presfun_ind1E in_setD mem_set//= memNset// !mule1.
  set Y := (X in _ -> _ --> X); rewrite [X in _ --> X -> _](_ : _ = Y) //.
  apply ae_eq_integral => //.
    apply: emeasurable_funM => //; apply: measurable_fun_comp => //.
    by apply: measurable_fun_presfun_ind1 => //; exact: measurableD.
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
  by rewrite /u_ /u /ind1 presfun_ind1E in_setD mem_set//= memNset// !mule1.
Qed.

End dominated_convergence_theorem.

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

(******************************************************************************)
(* * product measure                                                          *)
(******************************************************************************)

(* NB: not used *)
Lemma integrable_funenng (T1 T2 : measurableType) (R : realType) (pt2 : T2)
  (m2 : {measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) x :
  m2.-integrable setT (fun y => f (x, y)) ->
  m2.-integrable setT (fun y => f^\+ (x, y)).
Proof.
move=> [mfx fxoo]; split; first exact/emeasurable_fun_funenng.
apply: le_lt_trans fxoo; apply: ge0_le_integral => //.
- by apply: measurable_fun_comp => //; exact: emeasurable_fun_funenng.
- by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

(* NB: not used *)
Lemma integrable_funennp (T1 T2 : measurableType) (R : realType) (pt2 : T2)
  (m2 : {measure set T2 -> \bar R}) (f : T1 * T2 -> \bar R) x :
  m2.-integrable setT (fun y => f (x, y)) ->
  m2.-integrable setT (fun y => f^\- (x, y)).
Proof.
move=> [mfx fxoo]; split; first exact/emeasurable_fun_funennp.
apply: le_lt_trans fxoo; apply: ge0_le_integral => //.
- by apply: measurable_fun_comp => //; exact: emeasurable_fun_funennp.
- by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
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
pose f : T1 * T2 -> \bar R := EFin \o sfun_ind (pt1, pt2) 1 mA.
have mf : measurable_fun setT f.
  exact/EFin_measurable_fun/measurable_sfun.
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
pose f : T1 * T2 -> \bar R := EFin \o sfun_ind (pt1, pt2) 1 mA.
have mf : measurable_fun setT f.
  exact/EFin_measurable_fun/measurable_sfun.
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
Variables (pt1 : T1) (m1 : {measure set T1 -> \bar R}).
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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
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
  have -> : phi (X1 `*` X2) = (fun x => m2 X2 * (sfun_ind pt1 1 mX1 x)%:E)%E.
    rewrite funeqE => x.
    rewrite sfun_indE mul1r /m2 measure_restrE.
    rewrite /phi /m2 [measure_restr]lock /= -lock measure_restrE.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionM.
    by rewrite mule0 notin_xsectionM// set0I measure0.
  by apply: emeasurable_funeM => //; exact/EFin_measurable_fun/measurable_sfun.
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
  have -> : psi (X1 `*` X2) = (fun x => m1 X1 * (sfun_ind pt2 1 mX2 x)%:E)%E.
    rewrite funeqE => y.
    rewrite sfun_indE mul1r /m1 measure_restrE.
    rewrite /psi /m1 [measure_restr]lock /= -lock measure_restrE.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionM.
    by rewrite mule0 notin_ysectionM// set0I measure0.
  by apply: emeasurable_funeM => //; exact/EFin_measurable_fun/measurable_sfun.
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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
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
apply: (xsection_ndseq_closed_B pt2).
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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
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
apply: (ysection_ndseq_closed_B pt1).
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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Let m A := \int ((m2 \o xsection A) x) 'd m1[x].

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
  transitivity (\int (\sum_(n <oo) m2 (xsection (F n) x)) 'd m1[x]).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => x.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= xsection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_xsection tF)).
    by move=> i; apply: measurable_xsection.
  rewrite integral_sum //.
  - by move=> n; apply: measurable_fun_xsection => //; rewrite inE.
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

Section product_measure1E.
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm2 : sigma_finite setT m2).
Implicit Types A : set (T1 * T2).

Lemma product_measure1E (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 ->
  product_measure1 pt1 pt2 m1 sm2 (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
move=> mA1 mA2; rewrite /product_measure1 /=.
rewrite (_ : (fun _ => _) = (fun x => m2 A2 * (nnsfun_ind pt1 1%:nng mA1 x)%:E)%E); last first.
  rewrite funeqE => x; rewrite nnsfun_indE mul1r.
  by have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionM// mule1|rewrite mule0 notin_xsectionM].
rewrite ge0_integralM //.
- rewrite muleC; congr (_ * _)%E.
  by rewrite integral_EFin_sfun_ind// setIT mul1e.
- exact/EFin_measurable_fun/measurable_sfun.
- by move=> x _; rewrite lee_fin.
- exact: measure_ge0.
Qed.

End product_measure1E.

Section product_measure_unique.
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).

Definition product_measure_unique (m' : {measure set (T1 * T2) -> \bar R}) :
  (forall A1 A2, measurable A1 -> measurable A2 -> m' (A1 `*` A2) = m1 A1 * m2 A2)%E ->
  forall X : set (T1 * T2), measurable X -> product_measure1 pt1 pt2 m1 sf_m2 X = m' X.
Proof.
move=> m'E.
pose m := product_measure1 pt1 pt2 m1 sf_m2.
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
  + by rewrite measure_ge0//; have [] := F1_oo k.
  + rewrite ge0_fin_numE//.
    by have [] := F1_oo k.
    by rewrite measure_ge0//; have [] := F1_oo k.
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
apply: (@measure_unique R (prod_measurableType T1 T2) C _ _ (fun n => F1 n `*` F2 n)) => //.
- rewrite measurable_prod_measurableType //.
  congr (s<< _ >>).
  rewrite predeqE; split => [[A1 mA1 [A2 mA2 <-]]|[A1 [mA1 [A2 [mA2 ->]]]]].
    by exists A1; split => //; exists A2; split.
  by exists A1 => //; exists A2.
- move=> n; rewrite /C /=.
  exists (F1 n); split; first by have [] := F1_oo n.
  by exists (F2 n); split => //; have [] := F2_oo n.
- move=> a b ab; apply/subsetPset; apply: setSM.
  by apply/subsetPset; apply F2_nd.
  by apply/subsetPset; apply F1_nd.
- by move=> A [A1 [mA1 [A2 [mA2 ->]]]]; rewrite m'E// product_measure1E.
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
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis (sm1 : sigma_finite setT m1).
Implicit Types A : set (T1 * T2).

Let m A := \int ((m1 \o ysection A) x) 'd m2[x].

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
  transitivity (\int (\sum_(n <oo) m1 (ysection (F n) y)) 'd m2[y]).
    rewrite /m; congr (integral _ _ _); rewrite funeqE => y.
    rewrite -lim_mkord; apply/esym/cvg_lim => //=; rewrite /= ysection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_ysection tF)).
    by move=> i; apply: measurable_ysection.
  rewrite integral_sum //.
  - by move=> n; apply: measurable_fun_ysection => //; rewrite inE.
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

Section product_measure2E.
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm1 : sigma_finite setT m1.

Lemma product_measure2E (A1 : set T1) (A2 : set T2)
    (mA1 : measurable A1) (mA2 : measurable A2) :
  product_measure2 pt1 pt2 m2 sm1 (A1 `*` A2) = (m1 A1 * m2 A2)%E.
Proof.
have mA1A2 : measurable (A1 `*` A2) by exact: measurableM.
transitivity (\int ((m1 \o ysection (A1 `*` A2)) y) 'd m2[y]) => //.
rewrite (_ : _ \o _ = (fun y => m1 A1 * (presfun_ind1 pt2 A2 y)%:E))%E.
  rewrite ge0_integralM//; last 3 first.
    - exact/EFin_measurable_fun/measurable_fun_presfun_ind1.
    - by move=> y _; rewrite lee_fin presfun_ind1E.
    - exact: measure_ge0.
  by rewrite integral_EFin_presfun_ind1 ?setIT ?mul1e.
rewrite funeqE => y; rewrite presfun_ind1E.
have [yA2|yA2] := boolP (y \in A2); first by rewrite mule1 /= in_ysectionM.
by rewrite mule0 /= notin_ysectionM// measure0.
Qed.

End product_measure2E.

Section fubini_tonelli.
Variables (T1 T2 : measurableType) (pt1 : T1) (pt2 : T2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).

Let m : {measure set (T1 * T2) -> \bar R} := product_measure1 pt1 pt2 m1 sf_m2.

Let m' : {measure set (T1 * T2) -> \bar R} := product_measure2 pt1 pt2 m2 sf_m1.

Section fubini_tonelli_functions.
Variable f : T1 * T2 -> \bar R.

Definition fubini_F x := \int (f (x, y)) 'd m2[y].
Definition fubini_G y := \int (f (x, y)) 'd m1[x].
End fubini_tonelli_functions.

Section sfun1_fubini_tonelli.
Variables (A : set (T1 * T2)) (mA : measurable A).
Implicit Types A : set (T1 * T2).
Let f : presfun (prod_measurableType T1 T2) R := presfun_ind1 (pt1, pt2) A.

Let F := fubini_F (EFin \o f).
Let G := fubini_G (EFin \o f).

Lemma sfun1_fubini_tonelli_F_ge0 x : (0 <= F x)%E.
Proof. by apply: ge0_integral => // y _; rewrite lee_fin presfun_ind1E. Qed.

Lemma sfun1_fubini_tonelli_G_ge0 x : (0 <= G x)%E.
Proof. by apply: ge0_integral => // y _; rewrite lee_fin presfun_ind1E. Qed.

Lemma sfun1_fubini_tonelli_FE : F = m2 \o xsection A.
Proof.
rewrite funeqE => x; rewrite /= -(setTI (xsection _ _)).
rewrite -(integral_EFin_presfun_ind1 pt2)//; last exact: measurable_xsection.
rewrite /F /fubini_F -(setTI (xsection _ _)).
rewrite (integral_presfun_ind1_setI pt2); [|exact: measurable_xsection|by []].
apply eq_integral => y _ /=.
rewrite /f !presfun_ind1E [in RHS]mem_set// mul1e.
have [|] /= := boolP (y \in xsection _ _).
  by rewrite inE /xsection /= => ->.
by rewrite /xsection /= notin_set /= => /negP/negbTE ->.
Qed.

Lemma sfun1_fubini_tonelli_GE : G = m1 \o ysection A.
Proof.
rewrite funeqE => y; rewrite /= -(setTI (ysection _ _)).
rewrite -(integral_EFin_presfun_ind1 pt1)//; last exact: measurable_ysection.
rewrite /F /fubini_F -(setTI (ysection _ _)).
rewrite (integral_presfun_ind1_setI pt1); [|exact: measurable_ysection|by []].
apply eq_integral => x _ /=.
rewrite /f !presfun_ind1E [in RHS]mem_set// mul1e.
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
by rewrite /f integral_EFin_presfun_ind1// setIT sfun1_fubini_tonelli_FE.
Qed.

Lemma sfun1_fubini_tonelli2 :
  \int ((EFin \o f) z) 'd m'[z] = \int (G y) 'd m2[y].
Proof.
by rewrite /f integral_EFin_presfun_ind1// setIT sfun1_fubini_tonelli_GE.
Qed.

Lemma sfun1_fubini_tonelli : \int (F x) 'd m1[x] = \int (G y) 'd m2[y].
Proof.
rewrite -sfun1_fubini_tonelli1// -sfun1_fubini_tonelli2//.
rewrite integral_EFin_presfun_ind1 // integral_EFin_presfun_ind1 // setIT.
by apply: product_measure_unique => // A1 A2 mA1 mA2; rewrite product_measure2E.
Qed.

End sfun1_fubini_tonelli.

Section sfun_fubini_tonelli.
Variable f : nnsfun (prod_measurableType T1 T2) R.
Let n := ssize f.
Let A := spimg f.
Let a := srng f.

Let F := fubini_F (EFin \o f).
Let G := fubini_G (EFin \o f).

(*TODO: fix implicits of eq_integral*)

Lemma sfun_fubini_tonelli_FE :
  F = (fun x => (\sum_(k < n) (a`_k)%:E * m2 (xsection (A k) x))%E).
Proof.
rewrite funeqE => x; rewrite /F /fubini_F [in LHS]/=.
under eq_fun do rewrite (sfunE (pt1, pt2) f) -sumEFin.
rewrite ge0_integral_sum //; last 2 first.
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
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
rewrite sfun_fubini_tonelli_FE//; apply: measurable_fun_sum => //.
- move=> i; apply: emeasurable_funeM => //.
  by apply: measurable_fun_xsection => //; rewrite inE /A.
Qed.

Lemma sfun_fubini_tonelli_GE :
  G = (fun y => (\sum_(k < n) (a`_k)%:E * m1 (ysection (A k) y))%E).
Proof.
rewrite funeqE => y; rewrite /G /fubini_G [in LHS]/=.
under eq_fun do rewrite (sfunE (pt1, pt2) f) -sumEFin.
rewrite ge0_integral_sum //; last 2 first.
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
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
rewrite sfun_fubini_tonelli_GE//; apply: measurable_fun_sum => //.
- move=> i; apply: emeasurable_funeM => //.
  by apply: measurable_fun_ysection => //; rewrite inE /A.
Qed.

Lemma sfun_fubini_tonelli1 : \int ((EFin \o f) z) 'd m[z] = \int (F x) 'd m1[x].
Proof.
have EFinf : EFin \o f = (fun x => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E).
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite EFinf ge0_integral_sum //; last 2 first.
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
rewrite -ge0_integral_sum //; last 2 first.
  - move=> /= i; apply: emeasurable_funeM => //.
    by apply: sfun1_measurable_fun_fubini_tonelli_F; exact: measurable_spimg.
  - move=> i xy _.
    by apply: mule_ge0 => //; [exact: NNSFun_ge0|exact: sfun1_fubini_tonelli_F_ge0].
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_FE; apply eq_bigr => i _; congr (_ * _)%E.
rewrite -[RHS]/((m2 \o xsection (A i)) x) -sfun1_fubini_tonelli_FE //.
exact: measurable_spimg.
Qed.

Lemma sfun_fubini_tonelli2 : \int ((EFin \o f) z) 'd m'[z] = \int (G y) 'd m2[y].
Proof.
have EFinf : EFin \o f = (fun x => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E).
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite EFinf ge0_integral_sum //; last 2 first.
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
rewrite -ge0_integral_sum //; last 2 first.
  - move=> /= i; apply: emeasurable_funeM => //.
    by apply: sfun1_measurable_fun_fubini_tonelli_G; exact: measurable_spimg.
  - move=> i xy _.
    by apply: mule_ge0 => //; [exact: NNSFun_ge0|exact: sfun1_fubini_tonelli_G_ge0].
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_GE; apply eq_bigr => i _; congr (_ * _)%E.
rewrite -[RHS]/((m1 \o ysection (A i)) x) -sfun1_fubini_tonelli_GE //.
exact/measurable_spimg.
Qed.

Lemma sfun_fubini_tonelli :
  \int ((EFin \o f) z) 'd m[z] = \int ((EFin \o f) z) 'd m'[z].
Proof.
rewrite (_ : _ \o _ = (fun x : T1 * T2 => (\sum_(k < ssize f) ((srng f)`_k)%:E *
    (presfun_ind1 (pt1, pt2) (A k) x)%:E)%E)); last first.
  by rewrite funeqE => t; rewrite sumEFin /= (sfunE (pt1, pt2) f).
rewrite ge0_integral_sum //; last 2 first.
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
rewrite ge0_integral_sum //; last 2 first.
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

End sfun_fubini_tonelli.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.
Hypothesis f0 : forall x, setT x -> 0 <= f x.

Let F := fubini_F f.
Let G := fubini_G f.

Let F_ (g : (nnsfun (prod_measurableType T1 T2) R)^nat) n x :=
  \int ((EFin \o g n) (x, y)) 'd m2[y].
Let G_ (g : (nnsfun (prod_measurableType T1 T2) R)^nat) n y :=
  \int ((EFin \o g n) (x, y)) 'd m1[x].

Lemma measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
have [g [g_nd /= g_f]] := approximation (pt1, pt2) mf f0.
apply: (@emeasurable_fun_cvg _ _ _ (F_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> x _.
  rewrite /F_ /F /fubini_F.
  rewrite [in X in _ --> X](_ : (fun _ => _) =
      (fun y => lim (EFin \o g ^~ (x, y)))); last first.
    by rewrite funeqE => y; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - move=> n.
    by apply/EFin_measurable_fun => //; exact/measurable_fun_prod1/measurable_sfun.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
have [g [g_nd /= g_f]] := approximation (pt1, pt2) mf f0.
apply: (@emeasurable_fun_cvg _ _ _ (G_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- move=> y _.
  rewrite /G_ /G /fubini_G.
  rewrite [in X in _ --> X](_ : (fun _ => _) =
      (fun x => lim (EFin \o g ^~ (x, y)))); last first.
    by rewrite funeqE => x; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - move=> n.
    by apply/EFin_measurable_fun => //; exact/measurable_fun_prod2/measurable_sfun.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma fubini_tonelli1 : \int (f z) 'd m[z] = \int (F x) 'd m1[x].
Proof.
have [g [g_nd /= g_f]] := approximation (pt1, pt2) mf f0.
have F_F x : F x = lim (F_ g ^~ x).
  rewrite /F /fubini_F.
  rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) (x, y)) 'd m2[y]))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1/measurable_sfun.
    - by move=> n /= y _; rewrite lee_fin.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) z) 'd m[z])).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_sfun.
    - by move=> n /= x _; rewrite lee_fin.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ = lim
    (fun n => \int (\int ((EFin \o g n) (x, y)) 'd m2[y]) 'd m1[x])).
  by congr (lim _); rewrite funeqE => n; rewrite sfun_fubini_tonelli1.
rewrite [RHS](_ : _ = lim (fun n => \int (F_ g n x) 'd m1[x]))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- by move=> n x _; apply ge0_integral => // y _ /=; rewrite lee_fin.
- move=> x /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> y _; rewrite lee_fin.
  + exact/EFin_measurable_fun/measurable_fun_prod1/measurable_sfun.
  + by move=> *; rewrite lee_fin.
  + by move=> y _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

Lemma fubini_tonelli2 : \int (f z) 'd m[z] = \int (G y) 'd m2[y].
Proof.
have [g [g_nd /= g_f]] := approximation (pt1, pt2) mf f0.
have G_G y : G y = lim (G_ g ^~ y).
  rewrite /G /fubini_G.
  rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) (x, y)) 'd m1[x]))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod2/measurable_sfun.
    - by move=> n /= x _; rewrite lee_fin.
    - by move=> x /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int ((EFin \o g n) z) 'd m[z])).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_sfun.
    - by move=> n /= x _; rewrite lee_fin.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ = lim
    (fun n => \int (\int ((EFin \o g n) (x, y)) 'd m1[x]) 'd m2[y])).
  congr (lim _); rewrite funeqE => n.
  by rewrite sfun_fubini_tonelli sfun_fubini_tonelli2.
rewrite [RHS](_ : _ = lim (fun n => \int (G_ g n y) 'd m2[y]))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- by move=> n y _; apply ge0_integral => // x _ /=; rewrite lee_fin.
- move=> y /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin.
  + exact/EFin_measurable_fun/measurable_fun_prod2/measurable_sfun.
  + by move=> *; rewrite lee_fin.
  + by move=> x _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

End fubini_tonelli.

End fubini_tonelli.

Section fubini.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (R : realType) (pt1 : T1) (pt2 : T2).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sf_m1 : sigma_finite setT m1) (sf_m2 : sigma_finite setT m2).
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.

Let m : {measure set (T1 * T2) -> \bar R} := product_measure1 pt1 pt2 m1 sf_m2.

Lemma fubini1a : m.-integrable setT f <->
  \int (\int `|f (x, y)| 'd m2[y]) 'd m1[x] < +oo.
Proof.
split=> [[_ ioo]|ioo].
- rewrite -(@fubini_tonelli1 _ _ pt1 pt2 _ m1 _ sf_m2 (abse \o f))//.
  + exact: measurable_fun_comp.
  + by move=> /=.
- by split=> //; rewrite fubini_tonelli1//; exact: measurable_fun_comp.
Qed.

Lemma fubini1b : m.-integrable setT f <->
  \int (\int `|f (x, y)| 'd m1[x]) 'd m2[y] < +oo.
Proof.
split=> [[_ ioo]|ioo].
- rewrite -(@fubini_tonelli2 _ _ pt1 pt2 _ _ _ sf_m1 sf_m2 (abse \o f))//=.
  exact: measurable_fun_comp.
- by split=> //; rewrite fubini_tonelli2//; exact: measurable_fun_comp.
Qed.

Let measurable_fun1 : measurable_fun setT (fun x => \int `|f (x, y)| 'd m2[y]).
Proof.
apply: (@measurable_fun_fubini_tonelli_F _ _ _ _ _ _ sf_m2 (abse \o f)) => //=.
exact: measurable_fun_comp.
Qed.

Let measurable_fun2 : measurable_fun setT (fun y => \int `|f (x, y)| 'd m1[x]).
Proof.
apply: (@measurable_fun_fubini_tonelli_G _ _ _ _ _ _ sf_m1 (abse \o f)) => //=.
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
  - by move=> *; exact: ge0_integral.
  - by move=> *; rewrite gee0_abs//; exact: ge0_integral.
move/integrable_ae => /(_ pt1 measurableT) [N [mN N0 subN]].
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
  - by move=> *; exact: ge0_integral.
  - by move=> *; rewrite gee0_abs//; exact: ge0_integral.
move/integrable_ae => /(_ pt2 measurableT) [N [mN N0 subN]].
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
by apply: measurable_fun_fubini_tonelli_F => //; exact: emeasurable_fun_funenng.
Qed.

Let measurable_Fminus : measurable_fun setT Fminus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: emeasurable_fun_funennp.
Qed.

Lemma measurable_fubini_F : measurable_fun setT F.
Proof. by rewrite FE; exact: emeasurable_funB. Qed.

Let integrable_Fplus : m1.-integrable setT Fplus.
Proof.
split=> //; have := fubini1a.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> x _; exact: ge0_integral.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funenng => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funenng => //; exact: measurable_fun_prod1.
  - by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Fminus : m1.-integrable setT Fminus.
Proof.
split=> //; have := fubini1a.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: ge0_integral.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod1.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma integrable_fubini_F : m1.-integrable setT F.
Proof. by rewrite FE; exact: integrableB. Qed.

Let G := fubini_G m1 f.

Let Gplus y := \int (f^\+ (x, y)) 'd m1[x].
Let Gminus y := \int (f^\- (x, y)) 'd m1[x].

Let GE : G = Gplus \- Gminus. Proof. apply/funext=> x; exact: integralE. Qed.

Let measurable_Gplus : measurable_fun setT Gplus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: emeasurable_fun_funenng.
Qed.

Let measurable_Gminus : measurable_fun setT Gminus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: emeasurable_fun_funennp.
Qed.

Lemma measurable_fubini_G : measurable_fun setT G.
Proof. by rewrite GE; exact: emeasurable_funB. Qed.

Let integrable_Gplus : m2.-integrable setT Gplus.
Proof.
split=> //; have := fubini1b.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: ge0_integral.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funenng => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funenng => //; exact: measurable_fun_prod2.
  - by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Gminus : m2.-integrable setT Gminus.
Proof.
split=> //; have := fubini1b.1 imf.
apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: ge0_integral.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funennp => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funennp => //; exact: measurable_fun_prod2.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma fubini1 : \int (F x) 'd m1[x] = \int (f z) 'd m[z].
Proof.
rewrite FE integralB// [in RHS]integralE//.
rewrite fubini_tonelli1//; last exact: emeasurable_fun_funenng.
by rewrite fubini_tonelli1//; exact: emeasurable_fun_funennp.
Qed.

Lemma fubini2 : \int (G x) 'd m2[x] = \int (f z) 'd m[z].
Proof.
rewrite GE integralB// [in RHS]integralE//.
rewrite fubini_tonelli2//; last exact: emeasurable_fun_funenng.
by rewrite fubini_tonelli2//; exact: emeasurable_fun_funennp.
Qed.

End fubini.


