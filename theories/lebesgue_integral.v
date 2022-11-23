(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun.

(******************************************************************************)
(*                            Lebesgue Integral                               *)
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
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(*        {nnfun T >-> R} == type of non-negative functions                   *)
(*       {fimfun T >-> R} == type of functions with a finite image            *)
(*         {sfun T >-> R} == type of simple functions                         *)
(*       {nnsfun T >-> R} == type of non-negative simple functions            *)
(*           cst_nnsfun r == constant simple function                         *)
(*                nnsfun0 := cst_nnsfun 0                                     *)
(*         sintegral mu f == integral of the function f with the measure mu   *)
(*  \int[mu]_(x in D) f x == integral of the measurable function f over the   *)
(*                           domain D with measure mu                         *)
(*         \int[mu]_x f x := \int[mu]_(x in setT) f x                         *)
(*         dyadic_itv n k == the interval                                     *)
(*                           `[(k%:R * 2 ^- n), (k.+1%:R * 2 ^- n)[           *)
(*             approx D f == nondecreasing sequence of functions that         *)
(*                           approximates f over D using dyadic intervals     *)
(*       Rintegral mu D f := fine (\int[mu]_(x in D) f x).                    *)
(*     mu.-integrable D f == f is measurable over D and the integral of f     *)
(*                           w.r.t. D is < +oo                                *)
(*            ae_eq D f g == f is equal to g almost everywhere                *)
(* product_measure1 m1 s2 == product measure over T1 * T2, m1 is a measure    *)
(*                           measure over T1, s2 is a proof that a measure m2 *)
(*                           over T2 is sigma-finite                          *)
(* product_measure2 s2 m2 == product_measure1 mutatis mutandis                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "\int [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, mu at level 10, i, D at level 50,
  format "'[' \int [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\int [ mu ]_ i F"
  (at level 36, F at level 36, mu at level 10, i at level 0,
    right associativity, format "'[' \int [ mu ]_ i '/  '  F ']'").
Reserved Notation "mu .-integrable" (at level 2, format "mu .-integrable").
#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable_set1] : core.

HB.mixin Record IsMeasurableFun d (aT : measurableType d) (rT : realType) (f : aT -> rT) := {
  measurable_funP : measurable_fun setT f
}.
#[global] Hint Resolve fimfun_inP : core.

HB.structure Definition MeasurableFun d aT rT := {f of @IsMeasurableFun d aT rT f}.
Reserved Notation "{ 'mfun' aT >-> T }"
  (at level 0, format "{ 'mfun'  aT  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").
Notation "{ 'mfun' aT >-> T }" := (@MeasurableFun.type _ aT T) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
#[global] Hint Resolve measurable_funP : core.

HB.structure Definition SimpleFun d (aT (*rT*) : measurableType d) (rT : realType) :=
  {f of @IsMeasurableFun d aT rT f & @FiniteImage aT rT f}.
Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").
Notation "{ 'sfun' aT >-> T }" := (@SimpleFun.type _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Lemma measurable_sfunP {d} {aT : measurableType d} {rT : realType} (f : {mfun aT >-> rT}) (y : rT) :
  measurable (f @^-1` [set y]).
Proof. by rewrite -[f @^-1` _]setTI; exact: measurable_funP. Qed.

HB.mixin Record IsNonNegFun (aT : Type) (rT : numDomainType) (f : aT -> rT) := {
  fun_ge0 : forall x, 0 <= f x
}.
HB.structure Definition NonNegFun aT rT := {f of @IsNonNegFun aT rT f}.
Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Notation "{ 'nnfun' aT >-> T }" := (@NonNegFun.type aT T) : form_scope.
Notation "[ 'nnfun' 'of' f ]" := [the {nnfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: fun_ge0] : core.

HB.structure Definition NonNegSimpleFun d (aT : measurableType d) (rT : realType) :=
  {f of @SimpleFun d _ _ f & @NonNegFun aT rT f}.
Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Notation "{ 'nnsfun' aT >-> T }" := (@NonNegSimpleFun.type _ aT T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section ring.
Context (aT : pointedType) (rT : ringType).

Lemma fimfun_mulr_closed : mulr_closed (@fimfun aT rT).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; apply: (finite_image11 (fun x y => x * y)).
Qed.
Canonical fimfun_mul := MulrPred fimfun_mulr_closed.
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
Proof.
by apply/funext => x; elim: n => [|n IHn]//; rewrite !exprS fimfunM/= IHn.
Qed.

Lemma indic_fimfun_subproof X : @FiniteImage aT rT \1_X.
Proof.
split; apply: (finite_subfset [fset 0; 1]%fset) => x [tt /=].
by rewrite !inE indicE; case: (_ \in _) => _ <-; rewrite ?eqxx ?orbT.
Qed.
HB.instance Definition _ X := indic_fimfun_subproof X.
Definition indic_fimfun (X : set aT) := [the {fimfun aT >-> rT} of \1_X].

HB.instance Definition _ k f := FImFun.copy (k \o* f) (f * cst_fimfun k).
Definition scale_fimfun k f := [the {fimfun aT >-> rT} of k \o* f].

End ring.
Arguments indic_fimfun {aT rT} _.

Section comring.
Context (aT : pointedType) (rT : comRingType).
Definition fimfun_comRingMixin := [comRingMixin of {fimfun aT >-> rT} by <:].
Canonical fimfun_comRingType :=
  ComRingType {fimfun aT >-> rT} fimfun_comRingMixin.

Implicit Types (f g : {fimfun aT >-> rT}).
HB.instance Definition _ f g := FImFun.copy (f \* g) (f * g).
End comring.

Lemma fimfunE T (R : ringType) (f : {fimfun T >-> R}) x :
  f x = \sum_(y \in range f) (y * \1_(f @^-1` [set y]) x).
Proof.
rewrite (fsbigD1 (f x))// /= indicE mem_set// mulr1 fsbig1 ?addr0//.
by move=> y [fy /= /nesym yfx]; rewrite indicE memNset ?mulr0.
Qed.

Lemma fimfunEord T (R : ringType) (f : {fimfun T >-> R})
    (s := fset_set (f @` setT)) :
  forall x, f x = \sum_(i < #|`s|) (s`_i * \1_(f @^-1` [set s`_i]) x).
Proof.
move=> x; rewrite fimfunE fsbig_finite//= (big_nth 0)/= big_mkord.
exact: eq_bigr.
Qed.

Lemma trivIset_preimage1 {aT rT} D (f : aT -> rT) :
  trivIset D (fun x => f @^-1` [set x]).
Proof. by move=> y z _ _ [x [<- <-]]. Qed.

Lemma trivIset_preimage1_in {aT} {rT : choiceType} (D : set rT) (A : set aT)
  (f : aT -> rT) : trivIset D (fun x => A `&` f @^-1` [set x]).
Proof. by move=> y z _ _ [x [[_ <-] [_ <-]]]. Qed.

Section fimfun_bin.
Context d (T : measurableType d) (R : numDomainType).
Variables f g : {fimfun T >-> R}.

Lemma max_fimfun_subproof : @FiniteImage T R (f \max g).
Proof. by split; apply: (finite_image11 maxr). Qed.
HB.instance Definition _ := max_fimfun_subproof.

End fimfun_bin.

HB.factory Record FiniteDecomp (T : pointedType) (R : ringType) (f : T -> R) :=
  { fimfunE : exists (r : seq R) (A_ : R -> set T),
      forall x, f x = \sum_(y <- r) (y * \1_(A_ y) x) }.
HB.builders Context T R f of @FiniteDecomp T R f.
  Lemma finite_subproof: @FiniteImage T R f.
  Proof.
  split; have [r [A_ fE]] := fimfunE.
  suff -> : f = \sum_(y <- r) cst_fimfun y * indic_fimfun (A_ y) by [].
  by apply/funext=> x; rewrite fE fimfun_sum.
  Qed.
  HB.instance Definition _ := finite_subproof.
HB.end.

Section mfun_pred.
Context {d} {aT : measurableType d} {rT : realType}.
Definition mfun : {pred aT -> rT} := mem [set f | measurable_fun setT f].
Definition mfun_key : pred_key mfun. Proof. exact. Qed.
Canonical mfun_keyed := KeyedPred mfun_key.
End mfun_pred.

Section mfun.
Context {d} {aT : measurableType d} {rT : realType}.
Notation T := {mfun aT >-> rT}.
Notation mfun := (@mfun _ aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in mfun).
Definition mfun_Sub_subproof := @IsMeasurableFun.Build d aT rT f (set_mem fP).
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

Lemma cst_mfun_subproof x : @IsMeasurableFun d aT rT (cst x).
Proof. by split; apply: measurable_fun_cst. Qed.
HB.instance Definition _ x := @cst_mfun_subproof x.
Definition cst_mfun x := [the {mfun aT >-> rT} of cst x].

Lemma mfun_cst x : @cst_mfun x =1 cst x. Proof. by []. Qed.

End mfun.

Section ring.
Context d (aT : measurableType d) (rT : realType).

Lemma mfun_subring_closed : subring_closed (@mfun _ aT rT).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- exact: measurable_fun_cst.
- exact: measurable_funB.
- exact: measurable_funM.
Qed.
Canonical mfun_add := AddrPred mfun_subring_closed.
Canonical mfun_zmod := ZmodPred mfun_subring_closed.
Canonical mfun_mul := MulrPred mfun_subring_closed.
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
  @IsMeasurableFun d aT rT (mindic mD).
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

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst_mfun k).
Definition scale_mfun k f := [the {mfun aT >-> rT} of k \o* f].

Lemma max_mfun_subproof f g : @IsMeasurableFun d aT rT (f \max g).
Proof. by split; apply: measurable_fun_max. Qed.
HB.instance Definition _ f g := max_mfun_subproof f g.
Definition max_mfun f g := [the {mfun aT >-> _} of f \max g].

End ring.
Arguments indic_mfun {d aT rT} _.

Lemma measurable_fun_indic d (T : measurableType d) (R : realType)
    (D A : set T) : measurable A ->
  measurable_fun D (\1_A : T -> R).
Proof.
by move=> mA; apply/measurable_funTS; rewrite (_ : \1__ = mindic R mA).
Qed.

Section sfun_pred.
Context {d} {aT : measurableType d} {rT : realType}.
Definition sfun : {pred _ -> _} := [predI @mfun _ aT rT & fimfun].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_mfun : {subset sfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_fimfun : {subset sfun <= fimfun}. Proof. by move=> x /andP[]. Qed.
End sfun_pred.

Section sfun.
Context {d} {aT : measurableType d} {rT : realType}.
Notation T := {sfun aT >-> rT}.
Notation sfun := (@sfun _ aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @IsMeasurableFun.Build d aT rT f (set_mem (sub_sfun_mfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT rT f (set_mem (sub_sfun_fimfun fP)).
#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : T -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = (set_mem (sub_sfun_mfun Pf)) by [].
have -> : Pf2 = (set_mem (sub_sfun_fimfun Pf)) by [].
exact: Ksub.
Qed.

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

Lemma cst_sfunE x : @cst_sfun x =1 cst x. Proof. by []. Qed.

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
Context d (aT : measurableType d) (rT : realType).

Lemma sfun_subring_closed : subring_closed (@sfun d aT rT).
Proof.
by split=> [|f g|f g]; rewrite ?inE/= ?rpred1//;
   move=> /andP[/= mf ff] /andP[/= mg fg]; rewrite !(rpredB, rpredM).
Qed.

Canonical sfun_add := AddrPred sfun_subring_closed.
Canonical sfun_zmod := ZmodPred sfun_subring_closed.
Canonical sfun_mul := MulrPred sfun_subring_closed.
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

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst_sfun k).
Definition scale_sfun k f := [the {sfun aT >-> rT} of k \o* f].

HB.instance Definition _ f g := max_mfun_subproof f g.
Definition max_sfun f g := [the {sfun aT >-> _} of f \max g].

End ring.
Arguments indic_sfun {d aT rT} _.

Lemma fset_set_comp (T1 : Type) (T2 T3 : choiceType) (D : set T1)
    (f : {fimfun T1 >-> T2}) (g : T2 -> T3) :
  fset_set [set (g \o f) x | x in D] =
  [fset g x | x in fset_set [set f x | x in D]]%fset.
Proof. by rewrite -(image_comp f g) fset_set_image. Qed.

Lemma preimage_nnfun0 T (R : realDomainType) (f : {nnfun T >-> R}) t :
  t < 0 -> f @^-1` [set t] = set0.
Proof.
move=> t0.
by apply/preimage10 => -[x _]; apply: contraPnot t0 => <-; rewrite le_gtF.
Qed.

Lemma preimage_cstM T (R : realFieldType) (x y : R) (f : T -> R) :
  x != 0 -> (cst x \* f) @^-1` [set y] = f @^-1` [set y / x].
Proof.
move=> x0; apply/seteqP; rewrite /preimage; split => [z/= <-|z/= ->].
  by rewrite mulrAC divrr ?mul1r// unitfE.
by rewrite mulrCA divrr ?mulr1// unitfE.
Qed.

Lemma preimage_add T (R : numDomainType) (f g : T -> R) z :
  (f \+ g) @^-1` [set z] = \bigcup_(a in f @` setT)
    ((f @^-1` [set a]) `&` (g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= fgz|x [_ /= [y _ <-]] []].
  have : z - f x \in g @` setT.
    by rewrite inE /=; exists x=> //; rewrite -fgz addrC addKr.
  rewrite inE /= => -[x' _ gzf]; exists (z - g x')%R => /=.
    by exists x => //; rewrite gzf opprB addrC subrK.
  rewrite /preimage /=; split; first by rewrite gzf opprB addrC subrK.
  by rewrite gzf opprB addrC subrK -fgz addrC addKr.
rewrite /preimage /= => [fxfy gzf].
by rewrite gzf -fxfy addrC subrK.
Qed.

Section nnsfun_functions.
Context d (T : measurableType d) (R : realType).

Lemma cst_nnfun_subproof (x : {nonneg R}) : @IsNonNegFun T R (cst x%:num).
Proof. by split=> /=. Qed.
HB.instance Definition _ x := @cst_nnfun_subproof x.

Definition cst_nnsfun (r : {nonneg R}) := [the {nnsfun T >-> R} of cst r%:num].

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%R%:nng.

Lemma indic_nnfun_subproof (D : set T) : @IsNonNegFun T R (\1_D).
Proof. by split=> //=; rewrite /indic. Qed.
HB.instance Definition _ D := @indic_nnfun_subproof D.

HB.instance Definition _ D (mD : measurable D) :
   @NonNegFun T R (mindic R mD) := NonNegFun.on (mindic R mD).

End nnsfun_functions.
Arguments nnsfun0 {d T R}.

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
Context d (T : measurableType d) (R : realType).
Variables f g : {nnsfun T >-> R}.

HB.instance Definition _ := MeasurableFun.on (f \+ g).
Definition add_nnsfun := [the {nnsfun T >-> R} of f \+ g].

HB.instance Definition _ := MeasurableFun.on (f \* g).
Definition mul_nnsfun := [the {nnsfun T >-> R} of f \* g].

HB.instance Definition _ := MeasurableFun.on (f \max g).
Definition max_nnsfun := [the {nnsfun T >-> R} of f \max g].

Definition indic_nnsfun A (mA : measurable A) := [the {nnsfun T >-> R} of mindic R mA].

End nnsfun_bin.
Arguments add_nnsfun {d T R} _ _.
Arguments mul_nnsfun {d T R} _ _.
Arguments max_nnsfun {d T R} _ _.

Section nnsfun_iter.
Context d (T : measurableType d) (R : realType) (D : set T).
Variable f : {nnsfun T >-> R}^nat.

Definition sum_nnsfun n := \big[add_nnsfun/nnsfun0]_(i < n) f i.

Lemma sum_nnsfunE n t : sum_nnsfun n t = \sum_(i < n) (f i t).
Proof. by rewrite /sum_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

Definition bigmax_nnsfun n := \big[max_nnsfun/nnsfun0]_(i < n) f i.

Lemma bigmax_nnsfunE n t : bigmax_nnsfun n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /bigmax_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

End nnsfun_iter.

Section nnsfun_cover.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable f : {nnsfun T >-> R}.

Lemma nnsfun_cover :
  \big[setU/set0]_(i \in range f) (f @^-1` [set i]) = setT.
Proof. by rewrite fsbig_setU//= -subTset => x _; exists (f x). Qed.

Lemma nnsfun_coverT :
  \big[setU/set0]_(i \in [set: R]) (f @^-1` [set i]) = setT.
Proof.
by rewrite -(fsbig_widen (range f)) ?nnsfun_cover//= => x [_ /= /preimage10->].
Qed.

End nnsfun_cover.

#[global] Hint Extern 0 (measurable (_ @^-1` [set _])) =>
  solve [apply: measurable_sfunP] : core.

Lemma measurable_sfun_inP {d} {aT : measurableType d} {rT : realType}
   (f : {mfun aT >-> rT}) D (y : rT) :
  measurable D -> measurable (D `&` f @^-1` [set y]).
Proof. by move=> Dm; apply: measurableI. Qed.

#[global] Hint Extern 0 (measurable (_ `&` _ @^-1` [set _])) =>
  solve [apply: measurable_sfun_inP; assumption] : core.

#[global] Hint Extern 0 (finite_set _) => solve [apply: fimfunP] : core.

Section measure_fsbig.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m : {measure set T -> \bar R}.

Lemma measure_fsbig (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A ->
  (forall i, A i -> measurable (F i)) -> trivIset A F ->
  m (\big[setU/set0]_(i \in A) F i) = \sum_(i \in A) m (F i).
Proof.
move=> Afin Fm Ft.
by rewrite fsbig_finite// -measure_fin_bigcup// -bigsetU_fset_set.
Qed.

Lemma additive_nnsfunr (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in range g) (g @^-1` [set i])).
Proof.
rewrite -?measure_fsbig//.
- by rewrite !fsbig_finite//= big_distrr//.
- by move=> i Ai; apply: measurableI => //.
- exact/trivIset_setIl/trivIset_preimage1.
Qed.

Lemma additive_nnsfunl (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (g @^-1` [set i] `&` (f @^-1` [set x])) =
  m (\big[setU/set0]_(i \in range g) (g @^-1` [set i]) `&` f @^-1` [set x]).
Proof. by under eq_fsbigr do rewrite setIC; rewrite setIC additive_nnsfunr. Qed.

End measure_fsbig.

Section mulem_ge0.
Local Open Scope ereal_scope.

Let mulef_ge0 (R : realDomainType) x (f : R -> \bar R) :
  0 <= f x -> ((x < 0)%R -> f x = 0) -> 0 <= x%:E * f x.
Proof.
move=> A0 xA /=; have [x0|x0] := ltP x 0%R; first by rewrite (xA x0) mule0.
by rewrite mule_ge0.
Qed.

Lemma nnfun_muleindic_ge0 d (T : measurableType d) (R : realDomainType)
  (f : {nnfun T >-> R}) r z : 0 <= r%:E * (\1_(f @^-1` [set r]) z)%:E.
Proof.
apply: (@mulef_ge0 _ _ (fun r => (\1_(f @^-1` [set r]) z)%:E)).
  by rewrite lee_fin// indicE.
by move=> r0; rewrite preimage_nnfun0// indic0.
Qed.

Lemma mulemu_ge0 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) x (A : R -> set T) :
  ((x < 0)%R -> A x = set0) -> 0 <= x%:E * mu (A x).
Proof.
by move=> xA; rewrite (@mulef_ge0 _ _ (mu \o _))//= => /xA ->; rewrite measure0.
Qed.
Global Arguments mulemu_ge0 {d T R mu x} A.

Lemma nnsfun_mulemu_ge0 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : {nnsfun T >-> R}) x :
  0 <= x%:E * mu (f @^-1` [set x]).
Proof.
by apply: (mulemu_ge0 (fun x => f @^-1` [set x])); exact: preimage_nnfun0.
Qed.
End mulem_ge0.

(**********************************)
(* Definition of Simple Integrals *)
(**********************************)

Section simple_fun_raw_integral.
Local Open Scope ereal_scope.
Variables (T : Type) (R : numDomainType) (mu : set T -> \bar R) (f : T -> R).

Definition sintegral := \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).

Lemma sintegralET :
  sintegral = \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).
Proof. by []. Qed.

End simple_fun_raw_integral.

#[global] Hint Extern 0 (is_true (0 <= (_ : {measure set _ -> \bar _}) _)%E) =>
  solve [apply: measure_ge0] : core.

Section sintegral_lemmas.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma sintegralE f :
  sintegral mu f = \sum_(x \in range f) x%:E * mu (f @^-1` [set x]).
Proof.
rewrite (fsbig_widen (range f) setT)//= => x [_ Nfx] /=.
by rewrite preimage10// measure0 mule0.
Qed.

Lemma sintegral0 : sintegral mu (cst 0%R) = 0.
Proof.
rewrite sintegralE fsbig1// => r _; rewrite preimage_cst.
by case: ifPn => [/[!inE] <-|]; rewrite ?mul0e// measure0 mule0.
Qed.

Lemma sintegral_ge0 (f : {nnsfun T >-> R}) : 0 <= sintegral mu f.
Proof. by rewrite sintegralE fsume_ge0// => r _; exact: nnsfun_mulemu_ge0. Qed.

Lemma sintegral_indic (A : set T) : sintegral mu \1_A = mu A.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; 1%R]) => //; last 2 first.
  - exact: image_indic_sub.
  - by move=> t [[] -> /= /preimage10->]; rewrite measure0 mule0.
have N01 : (0 <> 1:> R)%R by move=> /esym/eqP; rewrite oner_eq0.
rewrite fsbigU//=; last by move=> t [->]//.
rewrite !fsbig_set1 mul0e add0e mul1e.
by rewrite preimage_indic ifT ?inE// ifN ?notin_set.
Qed.

(* NB: not used *)
Lemma sintegralEnnsfun (f : {nnsfun T >-> R}) : sintegral mu f =
  (\sum_(x \in [set r | r > 0]%R) (x%:E * mu (f @^-1` [set x])))%E.
Proof.
rewrite (fsbig_widen _ setT) ?sintegralET//.
move=> x [_ /=]; case: ltgtP => //= [xlt0 _|<-]; last by rewrite mul0e.
rewrite preimage10 ?measure0 ?mule0//= => -[t _].
by apply/eqP; apply: contra_ltN xlt0 => /eqP<-.
Qed.

End sintegral_lemmas.

Lemma eq_sintegral d (T : measurableType d) (R : numDomainType)
     (mu : set T -> \bar R) g f :
   f =1 g -> sintegral mu f = sintegral mu g.
Proof. by move=> /funext->. Qed.
Arguments eq_sintegral {d T R mu} g.

Section sintegralrM.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (r : R) (f : {nnsfun T >-> R}).

Lemma sintegralrM : sintegral m (cst r \* f)%R = r%:E * sintegral m f.
Proof.
have [->|r0] := eqVneq r 0%R.
  by rewrite mul0e (eq_sintegral (cst 0%R)) ?sintegral0// => x/=; rewrite mul0r.
rewrite !sintegralET.
transitivity (\sum_(x \in [set: R]) x%:E * m (f @^-1` [set x / r])).
  by apply: eq_fsbigr => x; rewrite preimage_cstM.
transitivity (\sum_(x \in [set: R]) r%:E * (x%:E * m (f @^-1` [set x]))).
  rewrite (reindex_fsbigT (fun x => r * x)%R)//; last first.
    by exists ( *%R r ^-1)%R; [exact: mulKf|exact: mulVKf].
  by apply: eq_fsbigr => x; rewrite mulrAC divrr ?unitfE// mul1r muleA EFinM.
by rewrite ge0_mule_fsumr// => x; exact: nnsfun_mulemu_ge0.
Qed.

End sintegralrM.

Section sintegralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f g : {nnsfun T >-> R}).

Lemma sintegralD : sintegral m (f \+ g)%R = sintegral m f + sintegral m g.
Proof.
rewrite !sintegralE; set F := f @` _; set G := g @` _; set FG := _ @` _.
pose pf x := f @^-1` [set x]; pose pg y := g @^-1` [set y].
transitivity (\sum_(z \in FG) z%:E * \sum_(a \in F) m (pf a `&` pg (z - a)%R)).
  apply: eq_fsbigr => z _; rewrite preimage_add -fsbig_setU// measure_fsbig//.
    by move=> x Fx; apply: measurableI.
  exact/trivIset_setIr/trivIset_preimage1.
under eq_fsbigr do rewrite ge0_mule_fsumr//; rewrite exchange_fsbig//.
transitivity (\sum_(x \in F) \sum_(y \in G) (x + y)%:E * m (pf x `&` pg y)).
  apply: eq_fsbigr => x _; rewrite /pf /pg (fsbig_widen G setT)//=; last first.
    by move=> y [_ /= /preimage10->]; rewrite setI0 measure0 mule0.
  rewrite (fsbig_widen FG setT)//=; last first.
    move=> z [_ /= FGz]; rewrite [X in m X](_ : _ = set0) ?measure0 ?mule0//.
    rewrite -subset0 => //= {x}i /= [<-] /(canLR (@addrNK _ _)).
    by apply: contra_not FGz => <-; exists i; rewrite //= addrC.
  rewrite (reindex_fsbigT (+%R x))//=.
  by apply: eq_fsbigr => y; rewrite addrC addrK.
transitivity (\sum_(x \in F) \sum_(y \in G) x%:E * m (pf x `&` pg y) +
              \sum_(x \in F) \sum_(y \in G) y%:E * m (pf x `&` pg y)).
  do 2![rewrite -fsbig_split//; apply: eq_fsbigr => _ /set_mem [? _ <-]].
  by rewrite EFinD ge0_muleDl// ?lee_fin.
congr (_ + _)%E; last rewrite exchange_fsbig//; apply: eq_fsbigr => x _.
  by rewrite -ge0_mule_fsumr// additive_nnsfunr nnsfun_cover setIT.
by rewrite -ge0_mule_fsumr// additive_nnsfunl nnsfun_cover setTI.
Qed.

End sintegralD.

Section le_sintegral.
Context d (T : measurableType d) (R : realType) (m : {measure set T -> \bar R}).
Variables f g : {nnsfun T >-> R}.
Hypothesis fg : forall x, f x <= g x.

Let fgnn : @IsNonNegFun T R (g \- f).
Proof. by split=> x; rewrite subr_ge0 fg. Qed.
#[local] HB.instance Definition _ := fgnn.

Lemma le_sintegral : (sintegral m f <= sintegral m g)%E.
Proof.
have gfgf : g =1 f \+ (g \- f) by move=> x /=; rewrite addrC subrK.
by rewrite (eq_sintegral _ _ gfgf) sintegralD// lee_addl // sintegral_ge0.
Qed.

End le_sintegral.

Lemma is_cvg_sintegral d (T : measurableType d) (R : realType)
  (m : {measure set T -> \bar R}) (f : {nnsfun T >-> R}^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) -> cvg (sintegral m \o f).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
by apply: le_sintegral => // => x; exact/nd_f.
Qed.

Definition proj_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Definition mrestrict d (T : measurableType d) (R : realType) (f : {nnsfun T >-> R})
  A (mA : measurable A) : f \_ A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

Definition scale_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (NngNum k0)) f.

Section sintegral_nondecreasing_limit_lemma.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat) (f : {nnsfun T >-> R}).
Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, cvg (g^~ x) -> f x <= lim (g^~ x).

Let fleg c : (set T)^nat := fun n => [set x | c * f x <= g n x].

Let nd_fleg c : {homo fleg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; rewrite /fleg; apply/subsetPset => x /= cfg.
by move: cfg => /le_trans; apply; exact: nd_g.
Qed.

Let mfleg c n : measurable (fleg c n).
Proof.
rewrite /fleg [X in _ X](_ : _ = \big[setU/set0]_(y <- fset_set (range f))
    \big[setU/set0]_(x <- fset_set (range (g n)) | c * y <= x)
      (f @^-1` [set y] `&` (g n @^-1` [set x]))).
  apply: bigsetU_measurable => r _; apply: bigsetU_measurable => r' crr'.
  exact/measurableI/measurable_sfunP.
rewrite predeqE => t; split => [/= cfgn|].
- rewrite -bigcup_set; exists (f t); first by rewrite /= in_fset_set//= mem_set.
  rewrite -bigcup_set_cond; exists (g n t) => //=.
  by rewrite in_fset_set// mem_set.
- rewrite bigsetU_fset_set// => -[r [x _ fxr]].
  rewrite bigsetU_fset_set_cond// => -[r' [[x' _ gnx'r'] crr']].
  by rewrite /preimage/= => -[-> ->].
Qed.

Let g1 c n : {nnsfun T >-> R} := proj_nnsfun f (mfleg c n).

Let le_ffleg c : {homo (fun p x => g1 c p x): m n / (m <= n)%N >-> (m <= n)%O}.
Proof.
move=> m n mn; apply/asboolP => t; rewrite /g1/= ler_pmul// 2!mindicE/= ler_nat.
have [|//] := boolP (t \in fleg c m); rewrite inE => cnt.
by have := nd_fleg c mn => /subsetPset/(_ _ cnt) cmt; rewrite mem_set.
Qed.

Let bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = setT.
Proof.
move=> c1; rewrite predeqE => x; split=> // _.
have := @fun_ge0 _ _ f x; rewrite le_eqVlt => /predU1P[|] gx0.
  by exists O => //; rewrite /fleg /=; rewrite -gx0 mulr0 fun_ge0.
have [cf|df] := pselect (cvg (g^~ x)).
  have cfg : lim (g^~ x) > c * f x.
    by rewrite (lt_le_trans _ (gf cf)) // gtr_pmull.
  suff [n cfgn] : exists n, g n x >= c * f x by exists n.
  move/(@lt_lim _ _ _ (nd_g x) cf) : cfg => [n _ nf].
  by exists n; apply: nf => /=.
have /cvgryPge/(_ (c * f x))[n _ ncfgn]:= nondecreasing_dvg_lt (nd_g x) df.
by exists n => //; rewrite /fleg /=; apply: ncfgn => /=.
Qed.

Local Open Scope ereal_scope.

Lemma nd_sintegral_lim_lemma : sintegral mu f <= lim (sintegral mu \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu f <= lim (sintegral mu \o g).
  by apply/lee_mul01Pr => //; exact: sintegral_ge0.
move=> c /andP[c0 c1].
have cg1g n : c%:E * sintegral mu (g1 c n) <= sintegral mu (g n).
  rewrite -sintegralrM (_ : (_ \* _)%R = scale_nnsfun (g1 c n) (ltW c0)) //.
  apply: le_sintegral => // t.
  suff : forall m x, (c * g1 c m x <= g m x)%R by move=> /(_ n t).
  move=> m x; rewrite /g1 /proj_nnsfun/= mindicE.
  by have [|] := boolP (_ \in _); [rewrite inE mulr1|rewrite 2!mulr0 fun_ge0].
suff {cg1g}<- : lim (fun n => sintegral mu (g1 c n)) = sintegral mu f.
  have is_cvg_g1 : cvg (fun n => sintegral mu (g1 c n)).
    by apply: is_cvg_sintegral => //= x m n /(le_ffleg c)/lefP/(_ x).
  rewrite -limeMl // lee_lim//; first exact: is_cvgeMl.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : (fun n => sintegral mu (g1 c n)) --> sintegral mu f by apply/cvg_lim.
rewrite [X in X --> _](_ : _ = fun n => \sum_(x <- fset_set (range f))
    x%:E * mu (f @^-1` [set x] `&` fleg c n)); last first.
  rewrite funeqE => n; rewrite sintegralE.
  transitivity (\sum_(x \in range f) x%:E * mu (g1 c n @^-1` [set x])).
    apply: eq_fbigl => r.
    do 2 (rewrite in_finite_support; last exact/finite_setIl).
    apply/idP/idP.
      rewrite in_setI => /andP[]; rewrite inE/= => -[x _]; rewrite mindicE.
      have [_|xcn] := boolP (_ \in _).
        by rewrite mulr1 => <-; rewrite !inE/= => ?; split => //; exists x.
      by rewrite mulr0 => /esym ->; rewrite !inE/= mul0e.
    rewrite in_setI => /andP[]; rewrite inE => -[x _ <-].
    rewrite !inE/= => h; split=> //; move: h; rewrite mindicE => /eqP.
    rewrite mule_eq0 negb_or => /andP[_]; set S := (X in mu X) => mS0.
    suff : S !=set0 by move=> [y yx]; exists y.
    by apply/set0P; apply: contra mS0 => /eqP ->; rewrite measure0.
  rewrite fsbig_finite//=; apply: eq_fbigr => r.
  rewrite in_fset_set// inE => -[t _ ftr _].
  have [->|r0] := eqVneq r 0%R; first by rewrite 2!mul0e.
  congr (_ * mu _); apply/seteqP; split => x.
    rewrite /preimage/= mindicE.
    have [|_] := boolP (_ \in _); first by rewrite mulr1 inE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  by rewrite /preimage/= => -[fxr cnx]; rewrite mindicE mem_set// mulr1.
rewrite sintegralE fsbig_finite//=.
apply: cvg_nnesum=> [r _|r _].
  near=> A; apply: (mulemu_ge0 (fun x => f @^-1` [set x] `&` fleg c A)) => r0.
  by rewrite preimage_nnfun0// set0I.
apply: cvgeMl => //=; rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n))); last first.
  by rewrite -setI_bigcupr bigcup_fleg// setIT.
have ? k i : measurable (f @^-1` [set k] `&` fleg c i) by exact: measurableI.
apply: nondecreasing_cvg_mu; [by []|exact: bigcupT_measurable|].
move=> n m nm; apply/subsetPset; apply: setIS.
by move/(nd_fleg c) : nm => /subsetPset.
Unshelve. all: by end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat) (f : {nnsfun T >-> R}).
Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, g ^~ x --> f x.

Let limg x : lim (g^~x) = f x.
Proof. by apply/cvg_lim; [exact: Rhausdorff| exact: gf]. Qed.

Lemma nd_sintegral_lim : sintegral mu f = lim (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x; rewrite -limg.
have : nondecreasing_seq (sintegral mu \o g).
  by move=> m n mn; apply: le_sintegral => // x; exact/nd_g.
move=> /ereal_nondecreasing_cvg/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=; apply: le_sintegral => // x.
rewrite -limg // (nondecreasing_cvg_le (nd_g x)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Section integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (f g : T -> \bar R) (D : set T).

Let nnintegral mu f := ereal_sup [set sintegral mu h |
  h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= f x]].

Definition integral mu D f (g := f \_ D) :=
  nnintegral mu (g ^\+) - nnintegral mu (g ^\-).

Variable (mu : {measure set T -> \bar R}).

Let nnintegral_ge0 f : (forall x, 0 <= f x) -> 0 <= nnintegral mu f.
Proof.
by move=> f0; apply: ereal_sup_ub; exists nnsfun0; last by rewrite sintegral0.
Qed.

Let eq_nnintegral g f : f =1 g -> nnintegral mu f = nnintegral mu g.
Proof. by move=> /funext->. Qed.

Let nnintegral0 : nnintegral mu (cst 0) = 0.
Proof.
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply/ereal_sup_ub; exists nnsfun0; last by rewrite sintegral0.
  by [].
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, f x = 0%R.
  by move=> y; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin//.
by rewrite (eq_sintegral (@nnsfun0 _ T R)) ?sintegral0.
Qed.

Let nnintegral_nnsfun (h : {nnsfun T >-> R}) :
  nnintegral mu (EFin \o h) = sintegral mu h.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gh <-]; rewrite le_sintegral.
by apply: ereal_sup_ub => /=; exists h.
Qed.

Local Notation "\int_ ( x 'in' D ) F" := (integral mu D (fun x => F))
  (at level 36, F at level 36, x, D at level 50,
  format "'[' \int_ ( x  'in'  D ) '/  '  F ']'").

Lemma eq_integral D g f : {in D, f =1 g} ->
  \int_(x in D) f x = \int_(x in D) g x.
Proof. by rewrite /integral => /eq_restrictP->. Qed.

Lemma ge0_integralE D f : (forall x, D x -> 0 <= f x) ->
  \int_(x in D) f x = nnintegral mu (f \_ D).
Proof.
move=> f0; rewrite /integral funeneg_restrict funepos_restrict.
have /eq_restrictP-> := ge0_funeposE f0.
have /eq_restrictP-> := ge0_funenegE f0.
by rewrite erestrict0 nnintegral0 sube0.
Qed.

Lemma ge0_integralTE f : (forall x, 0 <= f x) ->
  \int_(x in setT) f x = nnintegral mu f.
Proof. by move=> f0; rewrite ge0_integralE// patch_setT. Qed.

Lemma integralE D f :
  \int_(x in D) f x = \int_(x in D) (f ^\+ x) - \int_(x in D) f ^\- x.
Proof.
by rewrite [in LHS]/integral funepos_restrict funeneg_restrict -!ge0_integralE.
Qed.

Lemma integral0 D : \int_(x in D) (cst 0 x) = 0.
Proof. by rewrite ge0_integralE// erestrict0 nnintegral0. Qed.

Lemma integral_ge0 D f : (forall x, D x -> 0 <= f x) -> 0 <= \int_(x in D) f x.
Proof.
move=> f0; rewrite ge0_integralE// nnintegral_ge0// => x.
by rewrite /patch; case: ifP; rewrite // inE => /f0->.
Qed.

Lemma integral_nnsfun D (mD : measurable D) (h : {nnsfun T >-> R}) :
  \int_(x in D) (h x)%:E = sintegral mu (h \_ D).
Proof.
rewrite mrestrict -nnintegral_nnsfun// -mrestrict ge0_integralE ?comp_patch//.
by move=> x Dx /=; rewrite lee_fin; exact: fun_ge0.
Qed.

End integral.

Notation "\int [ mu ]_ ( x 'in' D ) f" :=
  (integral mu D (fun x => f)) : ereal_scope.
Notation "\int [ mu ]_ x f" :=
  ((integral mu setT (fun x => f)))%E : ereal_scope.
Arguments eq_integral {d T R mu D} g.

Section eq_measure_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (D : set T).
Implicit Types m : {measure set T -> \bar R}.

Let eq_measure_integral0 m2 m1 (f : T -> \bar R) :
  (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  [set sintegral m1 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]] `<=`
  [set sintegral m2 h | h in
    [set h : {nnsfun T >-> R} | (forall x, (h x)%:E <= (f \_ D) x)]].
Proof.
move=> m12 _ [h hfD <-] /=; exists h => //; apply: eq_fsbigr => r _.
have [hrD|hrD] := pselect (h @^-1` [set r] `<=` D); first by rewrite m12.
suff : r = 0%R by move=> ->; rewrite !mul0e.
apply: contra_notP hrD => /eqP r0 t/= htr.
have := hfD t.
rewrite /patch/=; case: ifPn; first by rewrite inE.
move=> tD.
move: r0; rewrite -htr => ht0.
by rewrite le_eqVlt eqe (negbTE ht0)/= lte_fin// ltNge// fun_ge0.
Qed.

Lemma eq_measure_integral m2 m1 (f : T -> \bar R) :
    (forall A, measurable A -> A `<=` D -> m1 A = m2 A) ->
  \int[m1]_(x in D) f x = \int[m2]_(x in D) f x.
Proof.
move=> m12; rewrite /integral funepos_restrict funeneg_restrict.
by congr (ereal_sup _ - ereal_sup _)%E; rewrite eqEsubset; split;
  apply: eq_measure_integral0 => A /m12 // /[apply].
Qed.

End eq_measure_integral.
Arguments eq_measure_integral {d T R D} m2 {m1 f}.

Section integral_measure_zero.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Let sintegral_measure_zero (f : T -> R) : sintegral mzero f = 0.
Proof. by rewrite sintegralE big1// => r _ /=; rewrite /mzero mule0. Qed.

Lemma integral_measure_zero (D : set T) (f : T -> \bar R) :
  \int[mzero]_(x in D) f x = 0.
Proof.
have h g : (forall x, 0 <= g x) -> [set sintegral mzero h |
    h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= g x]] = [set 0].
  move=> g0; apply/seteqP; split => [_ [h/= Dt <-]|x -> /=].
    by rewrite sintegral_measure_zero.
  by exists (cst_nnsfun _ (@NngNum _ 0 (lexx _))).
rewrite integralE !ge0_integralE//= h ?ereal_sup1; last first.
  by move=> r; rewrite erestrict_ge0.
by rewrite h ?ereal_sup1 ?subee// => r; rewrite erestrict_ge0.
Qed.

End integral_measure_zero.

Section domain_change.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma integral_mkcond D f : \int[mu]_(x in D) f x = \int[mu]_x (f \_ D) x.
Proof. by rewrite /integral patch_setT. Qed.

Lemma integralT_nnsfun (h : {nnsfun T >-> R}) :
  \int[mu]_x (h x)%:E = sintegral mu h.
Proof. by rewrite integral_nnsfun// patch_setT. Qed.

Lemma integral_mkcondr D P f :
  \int[mu]_(x in D `&` P) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite integral_mkcond [RHS]integral_mkcond patch_setI. Qed.

Lemma integral_mkcondl D P f :
  \int[mu]_(x in P `&` D) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite setIC integral_mkcondr. Qed.

End domain_change.
Arguments integral_mkcond {d T R mu} D f.

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R)
          (g : {nnsfun T >-> R}^nat).
Hypothesis f0 : forall x, 0 <= f x.
Hypothesis mf : measurable_fun setT f.
Hypothesis nd_g : forall x, nondecreasing_seq (g^~x).
Hypothesis gf : forall x, EFin \o g^~x --> f x.
Local Open Scope ereal_scope.

Lemma nd_ge0_integral_lim : \int[mu]_x f x = lim (sintegral mu \o g).
Proof.
rewrite ge0_integralTE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: lime_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ub; exists (g n) => //= => x.
  have <- : lim (EFin \o g ^~ x) = f x by apply/cvg_lim => //; exact: gf.
  have : (EFin \o g ^~ x) --> ereal_sup (range (EFin \o g ^~ x)).
    by apply: ereal_nondecreasing_cvg => p q pq /=; rewrite lee_fin; exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ub; exists n.
have := leey (\int[mu]_x (f x)).
rewrite le_eqVlt => /predU1P[|] mufoo; last first.
  have : \int[mu]_x (f x) \is a fin_num.
    by rewrite ge0_fin_numE//; exact: integral_ge0.
  rewrite ge0_integralTE// => /ub_ereal_sup_adherent h.
  apply: lee_adde => e; have {h} [/= _ [G Gf <-]] := h _ [gt0 of e%:num].
  rewrite EFinN lte_subl_addr// => fGe.
  have : forall x, cvg (g^~ x) -> (G x <= lim (g ^~ x))%R.
    move=> x cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _))// gxfx.
  move=> /(nd_sintegral_lim_lemma mu nd_g)/(lee_add2r e%:num%:E).
  by apply: le_trans; exact: ltW.
suff : lim (sintegral mu \o g) = +oo.
  by move=> ->; rewrite -ge0_integralTE// mufoo.
apply/eqyP => r r0.
have [G [Gf rG]] : exists h : {nnsfun T >-> R},
    (forall x, (h x)%:E <= f x) /\ (r%:E <= sintegral mu h).
  have : r%:E < \int[mu]_x (f x).
    move: (mufoo) => /eqyP/(_ _ (addr_gt0 r0 r0)).
    by apply: lt_le_trans => //; rewrite lte_fin ltr_addr.
  rewrite ge0_integralTE// => /ereal_sup_gt[x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, cvg (g^~ x) -> (G x <= lim (g^~ x))%R.
  move=> x cg; rewrite -lee_fin -(EFin_lim cg).
  by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _)) // gxfx.
by move/(nd_sintegral_lim_lemma mu nd_g) => Gg; rewrite (le_trans rG).
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
rewrite predeqE => r; split => [/= /[!in_itv]/= /andP[nr rn1]|].
- rewrite -bigcup_set /=; exists `|floor (r * 2 ^+ n.+1)|%N.
    rewrite /= mem_index_iota; apply/andP; split.
      rewrite -ltez_nat gez0_abs ?floor_ge0; last first.
        by rewrite mulr_ge0// (le_trans _ nr).
      apply: (@le_trans _ _ (floor (n * 2 ^ n.+1)%:R)); last first.
        by apply: le_floor; rewrite natrM natrX ler_pmul2r.
      by rewrite floor_natz intz.
    rewrite -ltz_nat gez0_abs; last first.
      by rewrite floor_ge0 mulr_ge0// (le_trans _ nr).
    rewrite -(@ltr_int R) (le_lt_trans (floor_le _))//.
    by rewrite PoszM intrM -natrX ltr_pmul2r.
  rewrite /= in_itv /=; apply/andP; split.
    rewrite ler_pdivr_mulr// (le_trans _ (floor_le _))//.
    by rewrite -(@gez0_abs (floor _))// floor_ge0 mulr_ge0// (le_trans _ nr).
  rewrite ltr_pdivl_mulr// (lt_le_trans (lt_succ_floor _))//.
  rewrite -[in leRHS]natr1 ler_add2r// -(@gez0_abs (floor _))// floor_ge0.
  by rewrite mulr_ge0// (le_trans _ nr).
- rewrite -bigcup_set => -[/= k] /[!mem_index_iota] /andP[nk kn].
  rewrite in_itv /= => /andP[knr rkn]; rewrite in_itv /=; apply/andP; split.
    by rewrite (le_trans _ knr)// ler_pdivl_mulr// -natrX -natrM ler_nat.
  by rewrite (lt_le_trans rkn)// ler_pdivr_mulr// -natrX -natrM ler_nat.
Qed.

Lemma dyadic_itv_image n T (f : T -> \bar R) x :
  (n%:R%:E <= f x < n.+1%:R%:E)%E ->
  exists k, (2 ^ n.+1 * n <= k < 2 ^ n.+1 * n.+1)%N /\
    f x \in EFin @` [set` I n.+1 k].
Proof.
move=> fxn; have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxn; case: (f x) => // /andP[].
have : f x \in EFin @` `[n%:R, n.+1%:R[%classic.
  rewrite inE /=; exists (fine (f x)); last by rewrite fineK.
  by rewrite in_itv /= -lee_fin -lte_fin (fineK fxfin).
rewrite (bigsetU_dyadic_itv n) inE /= => -[r]; rewrite -bigcup_set => -[k /=].
rewrite mem_index_iota => nk Ir rfx.
by exists k; split; [rewrite !(mulnC (2 ^ n.+1)%N)|rewrite !inE /=; exists r].
Qed.

End dyadic_interval.

Section approximation.
Context d (T : measurableType d) (R : realType).
Variables (D : set T) (mD : measurable D).
Variables (f : T -> \bar R) (mf : measurable_fun D f).

Local Notation I := (@dyadic_itv R).

Let A n k := if (k < n * 2 ^ n)%N then
  D `&` [set x | f x \in EFin @` [set` I n k]] else set0.

Let B n := D `&` [set x | n%:R%:E <= f x]%E.

Definition approx : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * (x \in A n k)%:R +
  n%:R * (x \in B n)%:R.

(* technical properties of the sets A and B *)
Let mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]//; rewrite -preimage_comp.
by apply: mf => //; apply/measurable_EFin; apply: measurable_itv.
Qed.

Let trivIsetA n : trivIset setT (A n).
Proof.
apply/trivIsetP => i j _ _.
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
by rewrite ltr_pmul2r// ltr_nat ltnS leqNgt ij.
Qed.

Let f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  x \in A n i = false.
Proof.
move=> fx0 i0; apply/negbTE; rewrite notin_set /A ltn_ord /= => -[_].
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[r1 r2].
rewrite fx0 => -[r0]; move: r1 r2; rewrite {}r0 {r} => + r2.
by rewrite ler_pdivr_mulr// mul0r lern0; exact/negP.
Qed.

Let fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  x \in A n i = false.
Proof.
move=> fxn; apply/negbTE; rewrite /A ltn_ord.
rewrite notin_set => /= -[_]; apply/negP.
rewrite notin_set /= => -[r /=].
rewrite in_itv /= => /andP[r1 r2] rfx.
move: fxn; rewrite -rfx lee_fin; apply/negP.
rewrite -ltNge (lt_le_trans r2)// -natrX ler_pdivr_mulr//.
by rewrite -natrM ler_nat (leq_trans (ltn_ord i)).
Qed.

Let disj_A0 x n (i k : 'I_(n * 2 ^ n)) : i != k ->
  x \in A n k -> (x \in A n i) = false.
Proof.
move=> ik xAn1k; apply/negbTE/negP => xAi.
have /trivIsetP/(_ _ _ Logic.I Logic.I ik)/= := @trivIsetA n.
rewrite predeqE => /(_ x)[+ _].
by rewrite 2!inE in xAn1k, xAi; move/(_ (conj xAi xAn1k)).
Qed.
Arguments disj_A0 {x n i} k.

Let mB n : measurable (B n).
Proof. exact: emeasurable_fun_c_infty. Qed.

Let foo_B1 x n : D x -> f x = +oo%E -> x \in B n.
Proof.
by move=> Dx fxoo; rewrite /B inE /=; split => //=; rewrite /= fxoo leey.
Qed.

Let f0_B0 x n : f x = 0%:E -> n != 0%N -> (x \in B n) = false.
Proof.
move=> fx0 n0; apply/negP; rewrite inE /B /= => -[Dx] /=; apply/negP.
by rewrite -ltNge fx0 lte_fin ltr0n lt0n.
Qed.

Let fgtn_B0 x n : (f x < n%:R%:E)%E -> (x \in B n) = false.
Proof.
move=> fxn; apply/negbTE/negP; rewrite inE /= => -[Dx] /=.
by apply/negP; rewrite -ltNge.
Qed.

Let f0_approx0 n x : f x = 0%E -> approx n x = 0.
Proof.
move=> fx0; rewrite /approx; have [->|n0] := eqVneq n O.
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0 // mulr0 addr0 big1 // => /= i _.
have [->|i0] := eqVneq (nat_of_ord i) 0%N; first by rewrite mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Let fpos_approx_neq0 x : D x -> (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx n x != 0.
Proof.
move=> Dx /andP[fx_gt0 fxoo].
have fxfin : f x \is a fin_num.
  by rewrite fin_numE; move: fxoo fx_gt0; case: (f x).
rewrite -(fineK fxfin) lte_fin in fx_gt0.
near=> n.
rewrite /approx; apply/negP; rewrite paddr_eq0//; last exact: sumr_ge0.
move/andP; rewrite psumr_eq0// => -[]/allP /= An0.
rewrite mulf_eq0 => /orP[|].
  by apply/negP; near: n; exists 1%N => //= m /=; rewrite lt0n pnatr_eq0.
rewrite pnatr_eq0 => /eqP.
have [//|] := boolP (x \in B n).
rewrite notin_set /B /setI /= => /not_andP[] // /negP.
rewrite -ltNge => fxn _.
have K : (`|floor (fine (f x) * 2 ^+ n)| < n * 2 ^ n)%N.
  rewrite -ltz_nat gez0_abs; last by rewrite floor_ge0 mulr_ge0// ltW.
  rewrite -(@ltr_int R); rewrite (le_lt_trans (floor_le _)) // PoszM intrM.
  by rewrite -natrX ltr_pmul2r// -lte_fin (fineK fxfin).
have xAnK : x \in A n (Ordinal K).
  rewrite inE /A /= K; split => //=.
  rewrite inE /=; exists (fine (f x)); last by rewrite fineK.
  rewrite in_itv /=; apply/andP; split.
    rewrite ler_pdivr_mulr// (le_trans _ (floor_le _))//.
    by rewrite -(@gez0_abs (floor _))// floor_ge0 mulr_ge0// ltW.
  rewrite ltr_pdivl_mulr// (lt_le_trans (lt_succ_floor _))//.
  rewrite -[in leRHS]natr1 ler_add2r// -{1}(@gez0_abs (floor _))//.
  by rewrite floor_ge0// mulr_ge0// ltW.
have /[!mem_index_enum]/(_ isT) := An0 (Ordinal K).
apply/negP.
rewrite xAnK mulr1 /= mulf_neq0// pnatr_eq0//= -lt0n absz_gt0 floor_neq0//.
rewrite -ler_pdivr_mulr//; apply/orP; right; apply/ltW; near: n.
exact: near_infty_natSinv_expn_lt (PosNum fx_gt0).
Unshelve. all: by end_near. Qed.

Let f_ub_approx n x : (f x < n%:R%:E)%E ->
  approx n x == 0 \/ exists k,
    [/\ (0 < k < n * 2 ^ n)%N,
       x \in A n k, approx n x = k%:R / 2 ^+ n &
       f x \in EFin @` [set` I n k]].
Proof.
move=> fxn; rewrite /approx fgtn_B0 // mulr0 addr0.
set lhs := (X in X == 0); have [|] := eqVneq lhs 0; first by left.
rewrite {}/lhs psumr_eq0; last by move=> i _; rewrite mulr_ge0.
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

Let notinD_A0 x n k : ~ D x -> (x \in A n k) = false.
Proof.
by move=> Dx; apply/negP; rewrite /A; case: ifPn => [?|_]; rewrite !inE => -[].
Qed.

Let notinD_B0 x n : ~ D x -> (x \in B n) = false.
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
    exact: sumr_ge0.
  move: (xAnk); rewrite inE {1}/A kn => -[_] /=.
  rewrite inE => -[r] /dyadic_itv_subU[|] rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite inE /A k2n; split => //=; rewrite inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0.
    rewrite exprS invrM ?unitfE// -muln2 natrM -mulrA (mulrCA 2).
    by rewrite divrr ?mulr1 ?unitfE.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //=.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite /A /= k2n inE; split => //=; rewrite inE/=; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) // mulr0.
    rewrite -[leLHS]mulr1 -[X in _ * X <= _](@divrr _ 2%:R) ?unitfE//.
    rewrite mulf_div -natrM muln2 -natrX -natrM -expnSr natrX.
    by rewrite ler_pmul2r// ler_nat.
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
    by rewrite -natrX ler_pdivl_mulr// mulrC -natrM ler_nat; case/andP : k1.
- have xBn : x \in B n.
    by rewrite /B /= inE /= /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx xBn mulr1.
  have xBn1 : x \in B n.+1 by rewrite /B /= inE.
  rewrite xBn1 mulr1 big1 ?add0r.
    by rewrite big1 ?add0r ?ler_nat// => /= i _; rewrite fgen_A0// mulr0.
  by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn)// lee_fin ler_nat.
Qed.

Lemma cvg_approx x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  (f x < +oo)%E -> (approx^~ x) --> fine (f x).
Proof.
move=> Dx fxoo; have fxfin : f x \is a fin_num.
  rewrite fin_numE; apply/andP; split; last by rewrite lt_eqF.
  by rewrite gt_eqF // (lt_le_trans _ (f0 _ Dx)).
apply/(@cvgrPdist_lt _ [normedModType R of R^o]) => _/posnumP[e].
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
  rewrite -natr1 (_ : `| _ |%:R  = (floor (fine (f x)))%:~R); last first.
    by rewrite -[in RHS](@gez0_abs (floor _))// floor_ge0//; exact/fine_ge0/f0.
  by rewrite lt_succ_floor.
rewrite -lte_fin (fineK fxfin) => fxn.
have [approx_nx0|[k [/andP[k0 kn2n] ? ->]]] := f_ub_approx fxn.
  by have := Hm _ mn; rewrite approx_nx0.
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[k1 k2] rfx.
rewrite (@le_lt_trans _ _ (1 / 2 ^+ n)) //.
  rewrite ler_norml; apply/andP; split.
    rewrite ler_subr_addl -mulrBl -lee_fin (fineK fxfin) -rfx lee_fin.
    rewrite (le_trans _ k1)// ler_pmul2r// -(@natrB _ _ 1) // ler_nat subn1.
    by rewrite leq_pred.
  by rewrite ler_subl_addr -mulrDl -lee_fin nat1r fineK// ltW// -rfx lte_fin.
by near: n; exact: near_infty_natSinv_expn_lt.
Unshelve. all: by end_near. Qed.

Lemma le_approx k x (f0 : forall x, (0 <= f x)%E) : D x ->
  ((approx k x)%:E <= f x)%E.
Proof.
move=> Dx; have [fixoo|] := ltP (f x) (+oo%E); last first.
  by rewrite leye_eq => /eqP ->; rewrite leey.
have nd_ag : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; exact/lefP/nd_approx.
have fi0 y : D y -> (0 <= f y)%E by move=> ?; exact: f0.
have cvg_af := cvg_approx fi0 Dx fixoo.
have is_cvg_af : cvg (approx ^~ x) by apply/cvg_ex; eexists; exact: cvg_af.
have {is_cvg_af} := nondecreasing_cvg_le nd_ag is_cvg_af k.
rewrite -lee_fin => /le_trans; apply.
rewrite -(@fineK _ (f x)); last first.
  by rewrite fin_numElt fixoo andbT (lt_le_trans _ (f0 _)).
by move/(cvg_lim (@Rhausdorff R)) : cvg_af => ->.
Qed.

Lemma dvg_approx x : D x -> f x = +oo%E -> ~ cvg (approx^~ x : _ -> R^o).
Proof.
move=> Dx fxoo; have approx_x n : approx n x = n%:R.
  rewrite /approx foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo leey.
case/cvg_ex => /= l; have [l0|l0] := leP 0%R l.
- move=> /cvgrPdist_lt/(_ _ ltr01) -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [leRHS]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ger0_norm // (le_trans (ceil_ge _)) //.
  by rewrite -(@gez0_abs (ceil _)) // ceil_ge0.
- move/cvgrPdist_lt => /(_ _ ltr01) -[n _].
  move=> /(_ (`|floor l|.+1 + n)%N) /= /(_ (leq_addl _ _)).
  rewrite approx_x.
  apply/negP; rewrite -leNgt distrC (le_trans _ (ler_sub_norm_add _ _)) //.
  rewrite normrN ler_subr_addl addSnnS [leRHS]ger0_norm ?ler0n//.
  rewrite natrD ler_add// ?ler1n// ler0_norm //; last by rewrite ltW.
  rewrite (@le_trans _ _ (- floor l)%:~R) //.
    by rewrite mulrNz ler_oppl opprK floor_le.
  by rewrite -(@lez0_abs (floor _)) // floor_le0 // ltW.
Qed.

Lemma ecvg_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o approx^~x --> f x.
Proof.
move=> Dx; have := leey (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx := dvg_approx Dx fxoo.
  have : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx mn => /lefP; exact.
  move/nondecreasing_dvg_lt => /(_ dvg_approx).
  by rewrite fxoo => ?; apply/cvgeryP.
rewrite -(@fineK _ (f x)); first exact: (cvg_comp (cvg_approx f0 Dx fxoo)).
by rewrite fin_numElt fxoo andbT (lt_le_trans _ (f0 _ _)).
Qed.

Let k2n_ge0 n (k : 'I_(n * 2 ^ n)) : 0 <= k%:R * 2 ^- n :> R.
Proof. by []. Qed.

Definition nnsfun_approx : {nnsfun T >-> R}^nat := fun n => locked (add_nnsfun
  (sum_nnsfun
    (fun k => match Bool.bool_dec (k < (n * 2 ^ n))%N true with
      | left h => scale_nnsfun (indic_nnsfun _ (mA n k)) (k2n_ge0 (Ordinal h))
      | right _ => nnsfun0
     end) (n * 2 ^ n)%N)
  (scale_nnsfun (indic_nnsfun _ (mB n)) (ler0n _ n))).

Lemma nnsfun_approxE n : nnsfun_approx n = approx n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite /nnsfun_approx; unlock; rewrite /=.
rewrite sum_nnsfunE; congr (_ + _).
by apply: eq_bigr => i _; case: Bool.bool_dec => [h|/negP]; [|rewrite ltn_ord].
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o nnsfun_approx^~x --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof.
 move=> m n mn; rewrite (nnsfun_approxE n) (nnsfun_approxE m).
exact: nd_approx.
Qed.

Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : {nnsfun T >-> R}^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~x --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|].
move=> x Dx; exact: cvg_nnsfun_approx.
Qed.

End approximation.

Section semi_linearity0.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> \bar R.
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.

Lemma ge0_integralM_EFin k : (0 <= k)%R ->
  \int[mu]_(x in D) (k%:E * f1 x) = k%:E * \int[mu]_(x in D) f1 x.
Proof.
rewrite integral_mkcond erestrict_scale [in RHS]integral_mkcond => k0.
set h1 := f1 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply/(measurable_restrict _ mD).
have [g [nd_g gh1]] := approximation measurableT mh1 (fun x _ => h10 x).
pose kg := fun n => scale_nnsfun (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ _ mu (fun x => k%:E * h1 x) kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu (scale_nnsfun (g n) k0))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (g n))).
    rewrite limeMl //; last first.
      by apply: is_cvg_sintegral => // x m n mn; apply/(lef_at x nd_g).
    by rewrite -(nd_ge0_integral_lim mu h10) // => x;
      [exact/(lef_at x nd_g)|exact: gh1].
  by under eq_fun do rewrite (sintegralrM mu k (g _)).
- by move=> t; rewrite mule_ge0.
- by move=> x m n mn; rewrite /kg ler_pmul//; exact/lefP/nd_g.
- move=> x.
  rewrite [X in X --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
  by apply: cvgeMl => //; exact: gh1.
Qed.

End semi_linearity0.

Section semi_linearity.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ge0_integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
rewrite !(integral_mkcond D) erestrictD.
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply/(measurable_restrict _ mD).
have mh2 : measurable_fun setT h2 by apply/(measurable_restrict _ mD).
have [g1 [nd_g1 gh1]] := approximation measurableT mh1 (fun x _ => h10 x).
have [g2 [nd_g2 gh2]] := approximation measurableT mh2 (fun x _ => h20 x).
pose g12 := fun n => add_nnsfun (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ _ mu _ g12) //; last 3 first.
  - by move=> x; rewrite adde_ge0.
  - by apply: nondecreasing_seqD => // x;
      [exact/(lef_at x nd_g1)|exact/(lef_at x nd_g2)].
  - move=> x; rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E))//.
    apply: cvgeD => //; [|exact: gh1|exact: gh2].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: h10|exact: h20].
rewrite (_ : _ \o _ =
    fun n => sintegral mu (g1 n) + sintegral mu (g2 n)); last first.
  by rewrite funeqE => n /=; rewrite sintegralD.
rewrite (nd_ge0_integral_lim _ _ (fun x => lef_at x nd_g1)) //; last first.
  by move=> x; exact: gh1.
rewrite (nd_ge0_integral_lim _ _ (fun x => lef_at x nd_g2)) //; last first.
  by move=> x; exact: gh2.
rewrite limeD //.
  by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g1).
  by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g2).
rewrite ge0_adde_def => //; rewrite inE; apply: lime_ge.
- by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g1).
- by apply: nearW => n; exact: sintegral_ge0.
- by apply: is_cvg_sintegral => // x Dx; exact/(lef_at x nd_g2).
- by apply: nearW => n; exact: sintegral_ge0.
Qed.

Lemma ge0_le_integral : (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> f12; rewrite !(integral_mkcond D).
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by apply/(measurable_restrict _ mD).
have mh2 : measurable_fun setT h2 by apply/(measurable_restrict _ mD).
have h12 x : h1 x <= h2 x by apply: lee_restrict.
have [g1 [nd_g1 /(_ _ Logic.I)gh1]] :=
  approximation measurableT mh1 (fun x _ => h10 _).
rewrite (nd_ge0_integral_lim _ h10 (fun x => lef_at x nd_g1) gh1)//.
apply: lime_le.
  by apply: is_cvg_sintegral => // t Dt; exact/(lef_at t nd_g1).
near=> n; rewrite ge0_integralTE//; apply: ereal_sup_ub => /=.
exists (g1 n) => // t; rewrite (le_trans _ (h12 _)) //.
have := gh1 t.
have := leey (h1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite leey.
have h1tfin : h1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (h10 t)).
have := gh1 t.
rewrite -(fineK h1tfin) => /fine_cvgP[ft_near].
set u_ := (X in X --> _) => u_h1 g1h1.
have <- : lim u_ = fine (h1 t) by apply/cvg_lim => //; exact: Rhausdorff.
rewrite lee_fin; apply: nondecreasing_cvg_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_g1.
by apply/cvg_ex; eexists; exact: u_h1.
Unshelve. all: by end_near. Qed.

End semi_linearity.

Lemma emeasurable_funN d (T : measurableType d) (R : realType) D (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D (fun x => - f x)%E.
Proof.
by move=> mD mf; apply: measurable_fun_comp => //; exact: emeasurable_fun_minus.
Qed.

Section approximation_sfun.
Context d (T : measurableType d) (R : realType) (f : T -> \bar R).
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
by move=> Dx; rewrite (funeposneg f); apply: cvgeD;
  [exact: add_def_funeposneg|apply: fp_cvg|apply:cvgeN; exact: fn_cvg].
Qed.

End approximation_sfun.

Section emeasurable_fun.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).

Lemma emeasurable_funD D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \+ g).
Proof.
move=> mf mg mD.
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
   apply: (emeasurable_fun_cvg (fun n x => (f_ n x + g_ n x)%:E)) => //.
     by move=> n; apply/EFin_measurable_fun/measurable_funTS/measurable_funD.
  move=> x Dx; under eq_fun do rewrite EFinD.
  exact: cvgeD (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NAnoo: A mD mf mg mA / ~ (A -oo) => [hwlogA|].
  have [] := pselect (A -oo); last exact: hwlogA.
  move=> /(@setD1K _ -oo)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case=>/=].
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

Lemma emeasurable_fun_sum D I s (h : I -> (T -> \bar R)) :
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
elim: s => [|s t ih] mf.
  by under eq_fun do rewrite big_nil; exact: measurable_fun_cst.
under eq_fun do rewrite big_cons //=; apply: emeasurable_funD => //.
exact: ih.
Qed.

Lemma emeasurable_fun_fsum D (I : choiceType) (A : set I)
    (h : I -> (T -> \bar R)) : finite_set A ->
    (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i \in A) h i x).
Proof.
move=> fs mh.
rewrite (_ : (fun x => _) = (fun x => \sum_(i <- fset_set A) h i x)).
  exact: emeasurable_fun_sum.
by apply/funext => t; rewrite fsbig_finite.
Qed.

Lemma ge0_emeasurable_fun_sum D (h : nat -> (T -> \bar R)) :
  (forall k x, 0 <= h k x) -> (forall k, measurable_fun D (h k)) ->
  measurable_fun D (fun x => \sum_(i <oo) h i x).
Proof.
move=> h0 mh; rewrite [X in measurable_fun _ X](_ : _ =
    (fun x => lim_esup (fun n => \sum_(0 <= i < n) h i x))); last first.
  apply/funext=> x; rewrite is_cvg_lim_esupE//.
  exact: is_cvg_ereal_nneg_natsum.
by apply: measurable_fun_lim_esup => k; exact: emeasurable_fun_sum.
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
have m0 : measurable ([set 0] : set (\bar R)) by [].
have mC0 : measurable ([set~ 0] : set (\bar R)) by apply: measurableC.
have mCoo : measurable (~` [set -oo; +oo] : set (\bar R)).
  exact/measurableC/measurableU.
have mfg : measurable (D `&` [set x | f x *? g x]).
  suff -> : [set x | f x *? g x] =
              (f @^-1` (~` [set 0]) `|` g @^-1` (~` [set -oo; +oo])) `&`
              (g @^-1` (~` [set 0]) `|` f @^-1` (~` [set -oo; +oo])).
     by rewrite setIIr; apply: measurableI;
        rewrite setIUr; apply: measurableU; do ?[apply: mf|apply: mg].
   apply/predeqP=> x; rewrite /preimage/= /mule_def !(negb_and, negb_or).
   rewrite !(rwP2 eqP idP) !(rwP2 negP idP) !(rwP2 orP idP).
   rewrite !(rwP2 negP idP) !(rwP2 orP idP) !(rwP2 andP idP).
   rewrite eqe_absl leey andbT (orbC (g x == +oo)).
   by rewrite eqe_absl leey andbT (orbC (f x == +oo)).
wlog fg : D mD mf mg mfg / forall x, D x -> f x *? g x => [hwlogM|]; last first.
  have [f_ f_cvg] := approximation_sfun mD mf.
  have [g_ g_cvg] := approximation_sfun mD mg.
  apply: (emeasurable_fun_cvg (fun n x => (f_ n x * g_ n x)%:E)) => //.
    move=> n; apply/EFin_measurable_fun.
    by apply: measurable_funM => //; exact: measurable_funTS.
  move=> x Dx; under eq_fun do rewrite EFinM.
  exact: cvgeM (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NA0: A mD mf mg mA / ~ (A 0) => [hwlogA|].
  have [] := pselect (A 0); last exact: hwlogA.
  move=> /(@setD1K _ 0)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case => /=].
  have -> : (fun x => f x * g x) @^-1` [set 0] =
           f @^-1` [set 0] `|` g @^-1` [set 0].
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

Lemma measurable_funeM D (f : T -> \bar R) (k : \bar R) :
  measurable_fun D f -> measurable_fun D (fun x => k * f x)%E.
Proof.
move=> mf; rewrite (_ : (fun x => k * f x) = (cst k) \* f)//.
exact/(emeasurable_funM _ mf)/measurable_fun_cst.
Qed.

End emeasurable_fun.

Section ge0_integral_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : Type) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_sum (s : seq I) :
  \int[mu]_(x in D) (\sum_(k <- s) f k x) =
  \sum_(k <- s) \int[mu]_(x in D) (f k x).
Proof.
elim: s => [|h t ih].
  by (under eq_fun do rewrite big_nil); rewrite big_nil integral0.
rewrite big_cons /= -ih -ge0_integralD//.
- by apply: eq_integral => x Dx; rewrite big_cons.
- by move=> *; exact: f0.
- by move=> *; apply: sume_ge0 => // k _; exact: f0.
- exact: emeasurable_fun_sum.
Qed.

End ge0_integral_sum.

Section ge0_integral_fsum.
Local Open Scope ereal_scope.
Variables (d : measure_display) (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : choiceType) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_fsum (A : set I) : finite_set A ->
  \int[mu]_(x in D) (\sum_(k \in A) f k x) =
  \sum_(k \in A) \int[mu]_(x in D) f k x.
Proof.
move=> fs; rewrite fsbig_finite//= -ge0_integral_sum//.
by apply eq_integral => x xD; rewrite fsbig_finite.
Qed.

End ge0_integral_fsum.

Section monotone_convergence_theorem.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g' : (T -> \bar R)^nat).
Hypothesis mg' : forall n, measurable_fun D (g' n).
Hypothesis g'0 : forall n x, D x -> 0 <= g' n x.
Hypothesis nd_g' : forall x, D x -> nondecreasing_seq (g'^~ x).
Let f' := fun x => lim (g'^~ x).

Let g n := (g' n \_ D).

Let g0 n x : 0 <= g n x. Proof. exact/erestrict_ge0/g'0. Qed.

Let mg n : measurable_fun setT (g n).
Proof. exact/(measurable_restrict _ mD). Qed.

Let nd_g x : nondecreasing_seq (g^~ x).
Proof.
by move=> m n mn; rewrite /g/patch; case: ifP => // /set_mem /nd_g' ->.
Qed.

Let f := fun x => lim (g^~ x).

Let is_cvg_g t : cvg (g^~ t).
Proof. by move=> ?; apply: ereal_nondecreasing_is_cvg => m n ?; apply/nd_g. Qed.

Local Definition g2' n : (T -> R)^nat := approx setT (g n).
Local Definition g2 n : {nnsfun T >-> R}^nat := nnsfun_approx measurableT (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : {nnsfun T >-> R}^nat :=
  fun k => bigmax_nnsfun (g2^~ k) k.

Let is_cvg_g2 n t : cvg (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvg => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Let nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!bigmax_nnsfunE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax2 => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
   by rewrite !nnsfun_approxE; exact/lefP/nd_approx.
rewrite (bigmaxD1 ord_max)// le_maxr; apply/orP; right.
rewrite [leRHS](eq_bigl (fun i => nat_of_ord i < n)%N).
  by rewrite (big_ord_narrow (leqnSn n)).
move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Let is_cvg_max_g2 t : cvg (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvg => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Let max_g2_g k x : ((max_g2 k x)%:E <= g k x)%O.
Proof.
rewrite bigmax_nnsfunE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  by apply/bigmax_leP; split => //; apply: g0D.
rewrite (@big_morph _ _ EFin 0%:E maxe) //; last by move=> *; rewrite maxEFin.
apply: le_bigmax2 => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx _ _ _)) => //; exact/nd_g/ltnW.
Qed.

Let lim_max_g2_f t : lim (EFin \o max_g2 ^~ t) <= f t.
Proof.
apply: lee_lim => //=; [apply: is_cvg_max_g2|apply: is_cvg_g|].
by near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Let lim_g2_max_g2 t n : lim (EFin\o g2 n ^~ t) <= lim (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //; [apply: is_cvg_g2|apply: is_cvg_max_g2|].
near=> k; rewrite /= bigmax_nnsfunE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (bigmax_sup (Ordinal nk)).
Unshelve. all: by end_near. Qed.

Let cvg_max_g2_f t : EFin \o max_g2 ^~ t --> f t.
Proof.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f _)) // (cvg_lim _ g_l).
have := leey l; rewrite le_eqVlt => /predU1P[->|loo]; first by rewrite leey.
rewrite -(cvg_lim _ g_l) //= lime_le => //; first exact: is_cvg_g.
near=> n.
have := leey (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
  have h := @dvg_approx _ _ _ setT _ t Logic.I fntoo.
  have g2oo : lim (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/cvgeryP.
    under [in X in X --> _]eq_fun do rewrite nnsfun_approxE.
    have : {homo (approx setT (g n))^~ t : n0 m / (n0 <= m)%N >-> (n0 <= m)%R}.
      exact/lef_at/nd_approx.
    by move/nondecreasing_dvg_lt => /(_ h).
  have -> : lim (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo leye_eq => /eqP.
  by rewrite leey.
- have approx_g_g := @cvg_approx _ _ _ setT _ t (fun t _ => g0 n t) Logic.I fntoo.
  suff : lim (EFin \o g2 n ^~ t) = g n t.
    by move=> <-; exact: (le_trans _ (lim_g2_max_g2 t n)).
  have /cvg_lim <- // : EFin \o (approx setT (g n)) ^~ t --> g n t.
    move/cvg_comp : approx_g_g; apply.
    by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
  rewrite (_ : _ \o _ = EFin \o approx setT (g n) ^~ t)// funeqE => m.
  by rewrite [in RHS]/= -nnsfun_approxE.
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int[mu]_(x in D) (f' x) = lim (fun n => \int[mu]_(x in D) (g' n x)).
Proof.
rewrite integral_mkcond.
under [in RHS]eq_fun do rewrite integral_mkcond -/(g _).
have -> : f' \_ D = f.
  apply/funext => x; rewrite /f /f' /g /patch /=; case: ifPn => //=.
  by rewrite lim_cst.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => \int[mu]_x g n x).
    move=> m n mn; apply: ge0_le_integral => //.
    by move=> *; exact: nd_g.
  have ub n : \int[mu]_x g n x <= \int[mu]_x f x.
    apply: ge0_le_integral => //.
    - move=> x _; apply: lime_ge => //; first exact: is_cvg_g.
      by apply: nearW => k; exact/g0.
    - apply: emeasurable_fun_cvg mg _ => x _.
      exact: ereal_nondecreasing_is_cvg.
    - move=> x Dx; apply: lime_ge => //; first exact: is_cvg_g.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: lime_le => //; [exact:ereal_nondecreasing_is_cvg|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ _ mu _ max_g2) //; last 2 first.
  - move=> t; apply: lime_ge => //; first exact: is_cvg_g.
    by apply: nearW => n; exact: g0.
  - by move=> t m n mn; exact/lefP/nd_max_g2.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvg => // n m nm; apply: ge0_le_integral => //.
  by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralTE//.
  by apply: ereal_sup_ub; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  (fun n => \int[mu]_(x in D) g' n x) --> \int[mu]_(x in D) f' x.
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvg => m n mn.
by apply: ge0_le_integral => // t Dt; [exact: g'0|exact: g'0|exact: nd_g'].
Qed.

End monotone_convergence_theorem.

Section integral_nneseries.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma integral_nneseries : \int[mu]_(x in D) (\sum_(n <oo) f n x) =
                           \sum_(n <oo) (\int[mu]_(x in D) (f n x)).
Proof.
rewrite monotone_convergence //.
- rewrite -lim_mkord (_ : (fun _ => _) =
    (fun n => (\sum_(k < n) \int[mu]_(x in D) f k x)))//.
  by rewrite funeqE => n; rewrite ge0_integral_sum// big_mkord.
- by move=> n; exact: emeasurable_fun_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_nneseries.

(* generalization of ge0_integralM_EFin to a constant potentially +oo
   using the monotone convergence theorem *)
Section ge0_integralM.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.

Lemma ge0_integralM (k : \bar R) : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (k * f x)%E = k * \int[mu]_(x in D) (f x).
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralM_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by apply: measurable_funeM.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g^~x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => lim (g^~ x).
transitivity (\int[mu]_(x in D) lim (g^~ x)).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0 (f x).
  - rewrite gt0_mulye//; apply/cvgeyPgey; near=> M.
    have M0 : (0 <= M)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|_|//]; last first.
      exists 1%N => // m /= m0.
      by rewrite mulry gtr0_sg// ?mul1e ?leey// ltr0n.
    near=> n; rewrite lee_fin -ler_pdivr_mulr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    by rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0// divr_ge0// ?ltW.
  - rewrite lt0_mulye//; apply/cvgeNyPleNy; near=> M;
    have M0 : (M <= 0)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|//|_]; last first.
      exists 1%N => // m /= m0.
      by rewrite mulrNy gtr0_sg// ?ltr0n// mul1e ?leNye.
    near=> n; rewrite lee_fin -ler_ndivr_mulr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0// -mulrNN.
    by rewrite mulr_ge0// ler_oppr oppr0// ltW// invr_lt0.
  - rewrite -fx0 mule0 /g -fx0 [X in X @ _ --> _](_ : _ = cst 0).
      exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite mule0.
rewrite (monotone_convergence mu mD mg g0 nd_g).
rewrite (_ : (fun _ => _) = (fun n => n%:R%:E * \int[mu]_(x in D) (f x))); last first.
  by rewrite funeqE => n; exact: ge0_integralM_EFin.
have : 0 <= \int[mu]_(x in D) (f x) by exact: integral_ge0.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  rewrite mule0 (_ : (fun _ => _) = cst 0) ?lim_cst//.
  by under eq_fun do rewrite mule0.
rewrite gt0_mulye//; apply/cvg_lim => //; apply/cvgeyPgey; near=> M.
have M0 : (0 <= M)%R by [].
near=> n; have [ifoo|] := ltP (\int[mu]_(x in D) (f x)) +oo; last first.
  rewrite leye_eq => /eqP ->; rewrite mulry muleC gt0_mulye ?leey//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (\int[mu]_(x in D) f x)); last first.
  by rewrite fin_numElt ifoo andbT (le_lt_trans _ if_gt0).
rewrite -lee_pdivr_mulr//; last first.
  by move: if_gt0 ifoo; case: (\int[mu]_(x in D) f x).
near: n.
exists `|ceil (M * (fine (\int[mu]_(x in D) f x))^-1)|%N => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
rewrite lee_fin natr_absz ger0_norm ?ceil_ge// ceil_ge0//.
by rewrite mulr_ge0// ?invr_ge0//; apply/fine_ge0/integral_ge0.
Unshelve. all: by end_near. Qed.

End ge0_integralM.

Section integral_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integral_indic (E : set T) : measurable E ->
  \int[mu]_(x in D) (\1_E x)%:E = mu (E `&` D).
Proof.
move=> mE; rewrite (_ : \1_E = indic_nnsfun R mE)// integral_nnsfun//=.
by rewrite restrict_indic sintegral_indic//; exact: measurableI.
Qed.

End integral_indic.

Section integralM_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralM_indic (f : R -> set T) (k : R) :
    ((k < 0)%R -> f k = set0) -> measurable (f k) ->
  \int[m]_(x in D) (k * \1_(f k) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f k) x)%:E.
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    by move=> x _; rewrite fk0// indic0 mulr0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralM//.
- exact/EFin_measurable_fun/measurable_fun_indic.
- by move=> y _; rewrite lee_fin.
Qed.

Lemma integralM_indic_nnsfun (f : {nnsfun T >-> R}) (k : R) :
  \int[m]_(x in D) (k * \1_(f @^-1` [set k]) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f @^-1` [set k]) x)%:E.
Proof.
rewrite (@integralM_indic (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

End integralM_indic.
Arguments integralM_indic {d T R m D} mD f.

Section integral_mscale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (k : {nonneg R}) (f : T -> \bar R).

Let integral_mscale_indic E : measurable E ->
  \int[mscale k m]_(x in D) (\1_E x)%:E =
  k%:num%:E * \int[m]_(x in D) (\1_E x)%:E.
Proof. by move=> ?; rewrite !integral_indic. Qed.

Let integral_mscale_nnsfun (h : {nnsfun T >-> R}) :
  \int[mscale k m]_(x in D) (h x)%:E = k%:num%:E * \int[m]_(x in D) (h x)%:E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - move=> r.
    exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralM//; last 2 first.
  - exact/EFin_measurable_fun/measurable_funTS.
  - by move=> x _; rewrite lee_fin.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun/measurable_funrM/measurable_funrM.
    exact/measurable_fun_indic.
  - by move=> n x _; rewrite EFinM mule_ge0// nnfun_muleindic_ge0.
apply eq_fsbigr => r _; rewrite ge0_integralM//.
- by rewrite !integralM_indic_nnsfun//= integral_mscale_indic// muleCA.
- exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
- by move=> t _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma ge0_integral_mscale (mf : measurable_fun D f) :
    (forall x, D x -> 0 <= f x) ->
  \int[mscale k m]_(x in D) f x = k%:num%:E * \int[m]_(x in D) f x.
Proof.
move=> f0; have [f_ [ndf_ f_f]] := approximation mD mf f0.
transitivity (lim (fun n => \int[mscale k m]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//=.
  - by apply eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //=; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun/measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b /ndf_ /lefP; rewrite lee_fin.
rewrite (_ : \int[m]_(x in D) _ =
    lim (fun n => \int[m]_(x in D) (f_ n x)%:E)); last first.
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun/measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b /ndf_ /lefP; rewrite lee_fin.
rewrite -limeMl//.
  by congr (lim _); apply/funext => n /=; rewrite integral_mscale_nnsfun.
apply/ereal_nondecreasing_is_cvg => a b ab; apply ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/EFin_measurable_fun/measurable_funTS.
- by move=> x _; rewrite lee_fin.
- exact/EFin_measurable_fun/measurable_funTS.
  by move=> x _; rewrite lee_fin; move/ndf_ : ab => /lefP.
Qed.

End integral_mscale.

Section fatou.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : (T -> \bar R)^nat).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int[mu]_(x in D) lim_einf (f^~ x) <=
              lim_einf (fun n => \int[mu]_(x in D) f n x).
Proof.
pose g n := fun x => einfs (f ^~ x) n.
have mg := measurable_fun_einfs mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
rewrite monotone_convergence //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: ge0_le_integral => //; [exact: g0| exact: mg| exact: g0| exact: mg|].
  move=> x Dx; apply: le_ereal_inf => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvg => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N ->
      \int[mu]_(x in D) g n x <= einfs (fun k => \int[mu]_(x in D) f k x) n.
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: ge0_le_integral => //; [exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lb; exists k.
  exact.
Qed.

End fatou.

Section integralN.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integralN D (f : T -> \bar R) :
  \int[mu]_(x in D) f^\+ x +? (- \int[mu]_(x in D) f^\- x) ->
  \int[mu]_(x in D) - f x = - \int[mu]_(x in D) f x.
Proof.
have [f_fin _|] := boolP (\int[mu]_(x in D) f^\- x \is a fin_num).
  rewrite integralE// [in RHS]integralE// oppeD ?fin_numN// oppeK addeC.
  by rewrite funenegN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -leeNy_eq; apply/negP.
  by rewrite -ltNge (lt_le_trans _ (integral_ge0 _ _)).
rewrite nfoo adde_defEninfty -leye_eq -ltNge ltey_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE// [in RHS]integralE// nfoo [in RHS]addeC oppeD//.
  by rewrite funenegN.
by rewrite integralE// [in RHS]integralE// funeposN funenegN nfoo pfoo.
Qed.

Lemma integral_ge0N (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) - f x = - \int[mu]_(x in D) f x.
Proof.
move=> f0; rewrite integralN // (eq_integral _ _ (ge0_funenegE _))// integral0.
by rewrite oppe0 fin_num_adde_def.
Qed.

End integralN.

Section integral_cst.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Variables (f : T -> \bar R) (D : set T) (mD : measurable D).

Lemma sintegral_cst (x : {nonneg R}) :
  sintegral mu (cst x%:num \_ D) = x%:num%:E * mu D.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; x%:num])/=; last 2 first.
- by move=> y [t _ <-] /=; rewrite /patch; case: ifPn; [right|left].
- by move=> y [_ /=/preimage10->]; rewrite measure0 mule0.
have [->|x0] := eqVneq x%:num 0%R; first by rewrite setUid fsbig_set1 !mul0e.
rewrite fsbigU0//=; last by move=> y [->]/esym; apply/eqP.
rewrite !fsbig_set1 mul0e add0e preimage_restrict//.
by rewrite ifN ?set0U ?setIidl//= notin_set; apply/eqP; rewrite eq_sym.
Qed.

Lemma integral_cst (r : R) : \int[mu]_(x in D) (EFin \o cst r) x = r%:E * mu D.
Proof.
wlog r0 : r / (0 <= r)%R.
  move=> h; have [|r0] := leP 0%R r; first exact: h.
  rewrite -[in RHS](opprK r) EFinN mulNe -h ?oppr_ge0; last exact: ltW.
  rewrite -integral_ge0N//; last by move=> t ?; rewrite /= lee_fin oppr_ge0 ltW.
  by under [RHS]eq_integral do rewrite /= opprK.
rewrite (eq_integral (EFin \o cst_nnsfun T (NngNum r0)))//.
by rewrite integral_nnsfun// sintegral_cst.
Qed.

Lemma integral_cst_pinfty : mu D != 0 -> \int[mu]_(x in D) (cst +oo) x = +oo.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => lim (g^~ t)) = cst +oo.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/cvgeryP/cvgryPge => M; exists `|ceil M|%N => //= m.
  rewrite /= -(ler_nat R); apply: le_trans.
  by rewrite (le_trans (ceil_ge _))// natr_absz ler_int ler_norm.
rewrite monotone_convergence //.
- rewrite /g (_ : (fun _ => _) = (fun n => n%:R%:E * mu D)); last first.
    by rewrite funeqE => n; rewrite -integral_cst.
  apply/cvg_lim => //; apply/cvgeyPge => M.
  have [muDoo|muDoo] := ltP (mu D) +oo; last first.
    exists 1%N => // m /= m0; move: muDoo; rewrite leye_eq => /eqP ->.
    by rewrite mulry gtr0_sg ?mul1e ?leey// ltr0n.
  exists `|ceil (M / fine (mu D))|%N => // m /=.
  rewrite -(ler_nat R) => MDm.
  rewrite -(@fineK _ (mu D)); last by rewrite ge0_fin_numE//.
  rewrite -lee_pdivr_mulr; last first.
    by apply: fine_gt0; rewrite muDoo lt_neqAle measure_ge0// !andbT eq_sym.
  rewrite lee_fin; apply: le_trans MDm.
  by rewrite natr_absz (le_trans (ceil_ge _))// ler_int ler_norm.
- by move=> n; exact: measurable_fun_cst.
- by move=> n x Dx; rewrite lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.

End integral_cst.

Section transfer.
Local Open Scope ereal_scope.
Variables (d1 d2 : _) (X : measurableType d1) (Y : measurableType d2).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (R : realType) (mu : {measure set X -> \bar R}).

Lemma integral_pushforward (f : Y -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[pushforward mu mphi]_y f y = \int[mu]_x (f \o phi) x.
Proof.
move=> mf f0.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity (lim (fun n => \int[pushforward mu mphi]_x (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; apply/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => \int[mu]_x (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; apply: measurable_fun_comp; first exact: measurable_fun_EFin.
      by apply: measurable_fun_comp => //; exact: measurable_sfun.
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
  by apply: eq_integral => x _ /=; apply/cvg_lim => //; exact: f_f.
apply/funext => n.
have mfnphi r : measurable (f_ n @^-1` [set r] \o phi).
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k \in range (f_ n))
    \int[mu]_x (k * \1_((f_ n @^-1` [set k]) \o phi) x)%:E).
  under eq_integral do rewrite fimfunE -fsumEFin//.
  rewrite ge0_integral_fsum//; last 2 first.
    - move=> y; apply/EFin_measurable_fun; apply: measurable_funM.
        exact: measurable_fun_cst.
      by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) y)).
    - by move=> y x _; rewrite nnfun_muleindic_ge0.
  apply eq_fsbigr => r _; rewrite integralM_indic_nnsfun// integral_indic//=.
  rewrite (integralM_indic _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _); rewrite [RHS](@integral_indic).
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_fsum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun; apply: measurable_funM.
      exact: measurable_fun_cst.
    by rewrite (_ : \1_ _ = mindic R (mfnphi r)).
  - by move=> r x _; rewrite nnfun_muleindic_ge0.
by apply eq_integral => x _; rewrite fsumEFin// -fimfunE.
Qed.

End transfer.

Section integral_dirac.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (a : T) (R : realType).
Variables (D : set T) (mD : measurable D).

Let ge0_integral_dirac (f : T -> \bar R) (mf : measurable_fun D f)
    (f0 : forall x, D x -> 0 <= f x) :
  D a -> \int[\d_a]_(x in D) (f x) = f a.
Proof.
move=> Da; have [f_ [ndf_ f_f]] := approximation mD mf f0.
transitivity (lim (fun n => \int[\d_ a]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - apply: eq_integral => x Dx; apply/esym/cvg_lim => //; apply: f_f.
    by rewrite inE in Dx.
  - by move=> n; apply/EFin_measurable_fun; exact/measurable_funTS.
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: f_f.
apply/funext => n.
under eq_integral do rewrite fimfunE// -fsumEFin//.
rewrite ge0_integral_fsum//.
- under eq_fsbigr; first by move=> r _; rewrite integralM_indic_nnsfun//; over.
  rewrite /= (fsbigD1 (f_ n a))//=; last by exists a.
  rewrite integral_indic//= diracE mem_set// mule1.
  rewrite fsbig1 ?adde0// => r /= [_ rfna].
  rewrite integral_indic//= diracE memNset ?mule0//=.
  by apply/not_andP; left; exact/nesym.
- by move=> r; exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma integral_dirac (f : T -> \bar R) (mf : measurable_fun D f) :
  \int[\d_ a]_(x in D) f x = (\1_D a)%:E * f a.
Proof.
have [/[!inE] aD|aD] := boolP (a \in D).
  rewrite integralE ge0_integral_dirac//; last exact/emeasurable_fun_funepos.
  rewrite ge0_integral_dirac//; last exact/emeasurable_fun_funeneg.
  by rewrite [in RHS](funeposneg f) indicE mem_set// mul1e.
rewrite indicE (negbTE aD) mul0e -(integral_measure_zero D f)//.
apply: eq_measure_integral => //= S mS DS; rewrite /dirac indicE memNset// => /DS.
by rewrite notin_set in aD.
Qed.

End integral_dirac.

Section integral_measure_sum_nnsfun.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m_ : {measure set T -> \bar R}^nat) (N : nat).
Let m := msum m_ N.

Let integral_measure_sum_indic (E D : set T) (mE : measurable E)
    (mD : measurable D) :
  \int[m]_(x in E) (\1_D x)%:E = \sum_(n < N) \int[m_ n]_(x in E) (\1_D x)%:E.
Proof.
rewrite integral_indic//= /msum/=; apply eq_bigr => i _.
by rewrite integral_indic// setIT.
Qed.

Let integralT_measure_sum (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n < N) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - move=> r /=; apply: measurable_fun_comp => //.
    exact/measurable_funrM/measurable_fun_indic.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n < N) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply eq_fsbigr => r _.
  rewrite integralM_indic_nnsfun// integral_measure_sum_indic//.
  by rewrite ge0_sume_distrr// => n _; apply integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= exchange_big/=; apply eq_bigr => i _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

Lemma integral_measure_sum_nnsfun (D : set T) (mD : measurable D)
  (f : {nnsfun T >-> R}) :
  \int[m]_(x in D) (f x)%:E = \sum_(n < N) \int[m_ n]_(x in D) (f x)%:E.
Proof.
rewrite integral_mkcond.
transitivity (\int[m]_x (proj_nnsfun f mD x)%:E).
  by apply: eq_integral => t _ /=; rewrite /patch mindicE;
    case: ifPn => // tD; rewrite ?mulr1 ?mulr0.
rewrite integralT_measure_sum; apply eq_bigr => i _.
rewrite [RHS]integral_mkcond; apply: eq_integral => t _.
rewrite /= /patch /mindic indicE.
by case: (boolP (t \in D)) => tD; rewrite ?mulr1 ?mulr0.
Qed.

End integral_measure_sum_nnsfun.

Lemma integral_measure_add_nnsfun d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  (\int[measure_add m1 m2]_(x in D) (f x)%:E =
   \int[m1]_(x in D) (f x)%:E + \int[m2]_(x in D) (f x)%:E)%E.
Proof.
rewrite /measureD integral_measure_sum_nnsfun// 2!big_ord_recl/= big_ord0.
by rewrite adde0.
Qed.

Section integral_mfun_measure_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.

Lemma ge0_integral_measure_sum (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
    (forall x, D x -> 0 <= f x) -> measurable_fun D f -> forall N,
  \int[msum m_ N]_(x in D) f x = \sum_(n < N) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf.
have [f_ [f_nd f_f]] := approximation mD mf f0.
elim => [|N ih]; first by rewrite big_ord0 msum_mzero integral_measure_zero.
rewrite big_ord_recr/= -ih.
rewrite (_ : _ m_ N.+1 = measure_add [the measure _ _ of msum m_ N] (m_ N)); last first.
  by apply/funext => A; rewrite measure_addE /msum/= big_ord_recr.
have mf_ n : measurable_fun D (fun x => (f_ n x)%:E).
  exact/measurable_funTS/EFin_measurable_fun.
have f_ge0 n x : D x -> 0 <= (f_ n x)%:E by move=> Dx; rewrite lee_fin.
have cvg_f_ (m : {measure set T -> \bar R}) : cvg (fun x => \int[m]_(x0 in D) (f_ x x0)%:E).
  apply: ereal_nondecreasing_is_cvg => a b ab.
  apply ge0_le_integral => //; [exact: f_ge0|exact: f_ge0|].
  by move=> t Dt; rewrite lee_fin; apply/lefP/f_nd.
transitivity (lim (fun n =>
    \int[measure_add [the measure _ _ of msum m_ N] (m_ N)]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//; last first.
    by move=> t Dt a b ab; rewrite lee_fin; exact/lefP/f_nd.
  by apply eq_integral => t /[!inE] Dt; apply/esym/cvg_lim => //; exact: f_f.
transitivity (lim (fun n =>
  \int[msum m_ N]_(x in D) (f_ n x)%:E + \int[m_ N]_(x in D) (f_ n x)%:E)).
  by congr (lim _); apply/funext => n; by rewrite integral_measure_add_nnsfun.
rewrite limeD//; do?[exact: cvg_f_]; last first.
  by apply: ge0_adde_def; rewrite inE; apply: lime_ge => //; do?[exact: cvg_f_];
      apply: nearW => n;  apply: integral_ge0 => //; exact: f_ge0.
by congr (_ + _); (rewrite -monotone_convergence//; [
    apply eq_integral => t /[!inE] Dt; apply/cvg_lim => //; exact: f_f |
    move=> t Dt a b ab; rewrite lee_fin; exact/lefP/f_nd]).
Qed.

End integral_mfun_measure_sum.

Lemma integral_measure_add d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x)%E -> measurable_fun D f ->
  (\int[measure_add m1 m2]_(x in D) f x =
   \int[m1]_(x in D) f x + \int[m2]_(x in D) f x)%E.
Proof.
move=> f0 mf; rewrite /measureD ge0_integral_measure_sum// 2!big_ord_recl/=.
by rewrite big_ord0 adde0.
Qed.

Section integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Let integral_measure_series_indic (D : set T) (mD : measurable D) :
  \int[m]_x (\1_D x)%:E = \sum_(n <oo) \int[m_ n]_x (\1_D x)%:E.
Proof.
rewrite integral_indic// setIT /m/= /mseries; apply: eq_eseries => i _.
by rewrite integral_indic// setIT.
Qed.

Lemma integral_measure_series_nnsfun (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n <oo) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - move=> r /=; apply: measurable_fun_comp => //.
    exact/measurable_funrM/measurable_fun_indic.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n <oo) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply eq_fsbigr => r _.
  rewrite integralM_indic_nnsfun// integral_measure_series_indic// nneseriesrM//.
  by move=> n _; apply integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= -nneseries_sum; last first.
  move=> r j _.
  have [r0|r0] := leP 0%R r.
    by rewrite mule_ge0//; apply integral_ge0 => // t _; rewrite lee_fin.
  rewrite (eq_integral (cst 0)) ?integral0 ?mule0// => t _.
  by rewrite preimage_nnfun0// indicE in_set0.
apply: eq_eseries => k _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

End integral_measure_series.

Section ge0_integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Lemma ge0_integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall t, D t -> 0 <= f t) ->
  measurable_fun D f ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  suff : forall n, \sum_(k < n) \int[m_ k]_(x in D) f x <= \int[m]_(x in D) f x.
    move=> n; apply: lime_le => //.
      by apply: is_cvg_ereal_nneg_natsum => k _; exact: integral_ge0.
    by apply: nearW => x; rewrite big_mkord.
  move=> n.
  rewrite [X in _ <= X](_ : _ = (\sum_(k < n) \int[m_ k]_(x in D) f x
    + \int[mseries m_ n]_(x in D) f x)); last first.
    transitivity (\int[measure_add [the measure _ _ of msum m_ n]
                                   [the measure _ _ of mseries m_ n]]_(x in D) f x).
      congr (\int[_]_(_ in D) _); apply/funext => A.
      by rewrite measure_addE; exact: nneseries_split.
    rewrite integral_measure_add//; congr (_ + _).
    by rewrite -ge0_integral_measure_sum.
  by apply: lee_addl; exact: integral_ge0.
rewrite ge0_integralE//=; apply: ub_ereal_sup => /= _ [g /= gf] <-.
rewrite -integralT_nnsfun (integral_measure_series_nnsfun _ mD).
apply: lee_nneseries => n _.
  by apply integral_ge0 => // x _; rewrite lee_fin.
rewrite [leRHS]integral_mkcond; apply ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/EFin_measurable_fun.
- by move=> x _; rewrite erestrict_ge0.
- exact/(measurable_restrict _ mD).
Qed.

End ge0_integral_measure_series.

Section subset_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_setU (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun (A `|` B) f ->
  (forall x, (A `|` B) x -> 0 <= f x) -> [disjoint A & B] ->
  \int[mu]_(x in A `|` B) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB.
transitivity (\int[mu]_(x in A `|` B) ((f \_ A) x + (f \_ B) x)).
  apply: eq_integral => x; rewrite inE => -[xA|xB].
    rewrite /patch mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xB.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
  rewrite /patch addeC mem_set// ifF ?adde0//; apply/negbTE/negP; rewrite inE => xA.
    by move: AB; rewrite disj_set2E => /eqP; apply/eqP/set0P; exists x.
rewrite ge0_integralD//; last 5 first.
  - exact: measurableU.
  - by move=> x _; apply: erestrict_ge0 => y Ay; apply: f0; left.
  - have : measurable_fun A f.
      by apply: measurable_funS mf; [exact: measurableU|exact: subsetUl].
    by apply/(measurable_restrict _ _ _ _).1 => //; exact: measurableU.
  - by move=> x _; apply: erestrict_ge0 => y By; apply: f0; right.
  - have : measurable_fun B f.
      by apply: measurable_funS mf; [exact: measurableU|exact: subsetUr].
    by apply/(measurable_restrict _ _ _ _).1 => //; exact: measurableU.
by rewrite -integral_mkcondl setIC setUK -integral_mkcondl setKU.
Qed.

Lemma subset_integral (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun B f -> (forall x, B x -> 0 <= f x) ->
  A `<=` B -> \int[mu]_(x in A) f x <= \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB; rewrite -(setDUK AB) integral_setU//; last 4 first.
  - exact: measurableD.
  - by rewrite setDUK.
  - by move=> x; rewrite setDUK//; exact: f0.
  - by rewrite disj_set2E setDIK.
by apply: lee_addl; apply: integral_ge0 => x [Bx _]; exact: f0.
Qed.

Lemma integral_set0 (f : T -> \bar R) : \int[mu]_(x in set0) f x = 0.
Proof.
rewrite integral_mkcond (eq_integral (cst 0)) ?integral0// => x _.
by rewrite /restrict; case: ifPn => //; rewrite in_set0.
Qed.

Lemma ge0_integral_bigsetU (F : (set T)^nat) (f : T -> \bar R) n :
  (forall n, measurable (F n)) ->
  let D := \big[setU/set0]_(i < n) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset `I_n F ->
  \int[mu]_(x in D) f x = \sum_(i < n) \int[mu]_(x in F i) f x.
Proof.
move=> mF.
elim: n => [|n ih] D mf f0 tF; first by rewrite /D 2!big_ord0 integral_set0.
rewrite /D big_ord_recr/= integral_setU//; last 4 first.
  - exact: bigsetU_measurable.
  - by move: mf; rewrite /D big_ord_recr.
  - by move: f0; rewrite /D big_ord_recr.
  - apply/eqP; move: (trivIset_bigsetUI tF (ltnSn n) (leqnn n)).
    rewrite [in X in X -> _](eq_bigl xpredT)// => i.
    by rewrite (leq_trans (ltn_ord i)).
rewrite ih ?big_ord_recr//.
- apply: measurable_funS mf => //; first exact: bigsetU_measurable.
  by rewrite /D big_ord_recr /=; apply: subsetUl.
- by move=> t Dt; apply: f0; rewrite /D big_ord_recr/=; left.
- by apply: sub_trivIset tF => x; exact: leq_trans.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> (0 < a)%R ->
  a%:E * mu (D `&` [set x | (`|g x| >= a%:E)%E]) <= \int[mu]_(x in D) `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | (a%:E <= `|g x|)%E]).
  by apply: emeasurable_fun_c_infty => //; exact: measurable_fun_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) `|g x|)).
  rewrite -integral_cst//; apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite ltW.
  - exact/EFin_measurable_fun/measurable_fun_cst.
  - by apply: measurable_fun_comp => //; exact: measurable_funS mg.
  - by move=> x /= [].
by apply: subset_integral => //; exact: measurable_fun_comp.
Qed.

End subset_integral.

Section Rintegral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Definition Rintegral (D : set T) (f : T -> R) :=
  fine (\int[mu]_(x in D) (f x)%:E).

End Rintegral.

Notation "\int [ mu ]_ ( x 'in' D ) f" := (Rintegral mu D (fun x => f)) : ring_scope.
Notation "\int [ mu ]_ x f" := (Rintegral mu setT (fun x => f)) : ring_scope.

Section integrable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Definition integrable (mu : set T -> \bar R) D f :=
  measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo).

Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).
Implicit Type f g : T -> \bar R.

Notation mu_int := (integrable mu D).

Lemma integrable0 : mu_int (cst 0).
Proof.
split; first exact: measurable_fun_cst.
under eq_integral do rewrite (gee0_abs (lexx 0)).
by rewrite integral0.
Qed.

Lemma eq_integrable f g : {in D, f =1 g} -> mu_int f -> mu_int g.
Proof.
move=> fg [mf fi]; split; first exact: eq_measurable_fun mf.
rewrite (le_lt_trans _ fi)//; apply: ge0_le_integral=> //.
  by apply: measurable_fun_comp => //; exact: eq_measurable_fun mf.
  by apply: measurable_fun_comp => //; exact: eq_measurable_fun mf.
by move=> x Dx; rewrite fg// inE.
Qed.

Lemma le_integrable f g : measurable_fun D f ->
  (forall x, D x -> `|f x| <= `|g x|) -> mu_int g -> mu_int f.
Proof.
move=> mf fg [mfg goo]; split => //; rewrite (le_lt_trans _ goo) //.
by apply: ge0_le_integral => //; exact: measurable_fun_comp.
Qed.

Lemma integrableN f : mu_int f -> mu_int (-%E \o f).
Proof.
move=> [mf foo]; split; last by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; apply: measurable_fun_comp =>//; exact: emeasurable_fun_minus.
Qed.

Lemma integrablerM (k : R) f : mu_int f -> mu_int (fun x => k%:E * f x).
Proof.
move=> [mf foo]; split; first exact: measurable_funeM.
under eq_fun do rewrite abseM.
by rewrite ge0_integralM// ?lte_mul_pinfty//; exact: measurable_fun_comp.
Qed.

Lemma integrableMr (k : R) f : mu_int f -> mu_int (f \* cst k%:E).
Proof.
by move=> mf; apply: eq_integrable (integrablerM k mf) => // x; rewrite muleC.
Qed.

Lemma integrableD f g : mu_int f -> mu_int g -> mu_int (f \+ g).
Proof.
move=> [mf foo] [mg goo]; split; first exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int[mu]_(x in D) (`|f x| + `|g x|))).
  apply: ge0_le_integral => //.
  - by apply: measurable_fun_comp => //; exact: emeasurable_funD.
  - by apply: emeasurable_funD; apply: measurable_fun_comp.
  - by move=> *; exact: lee_abs_add.
by rewrite ge0_integralD //; [exact: lte_add_pinfty|
  exact: measurable_fun_comp|exact: measurable_fun_comp].
Qed.

Lemma integrableB f g : mu_int f -> mu_int g -> mu_int (f \- g).
Proof. by move=> fi gi; exact/(integrableD fi)/integrableN. Qed.

Lemma integrable_add_def f : mu_int f ->
  \int[mu]_(x in D) f^\+ x +? - \int[mu]_(x in D) f^\- x.
Proof.
move=>  [mf]; rewrite -[fun x => _]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
  - exact: emeasurable_fun_funepos.
  - exact: emeasurable_fun_funeneg.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite lee_addl// integral_ge0.
- by rewrite inE (@le_lt_trans _ _ 0)// lee_oppl oppe0 integral_ge0.
Qed.

Lemma integrable_funepos f : mu_int f -> mu_int f^\+.
Proof.
move=> [Df foo]; split; first exact: emeasurable_fun_funepos.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurable_fun_comp => //; exact: emeasurable_fun_funepos.
- exact/measurable_fun_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// lee_addl.
Qed.

Lemma integrable_funeneg f : mu_int f -> mu_int f^\-.
Proof.
move=> [Df foo]; split; first exact: emeasurable_fun_funeneg.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurable_fun_comp => //; exact: emeasurable_fun_funeneg.
- exact/measurable_fun_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// lee_addr.
Qed.

Lemma integral_funeneg_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\- x < +oo.
Proof.
move=> [mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- by apply: emeasurable_fun_funeneg => //; exact: emeasurable_funN.
- exact: measurable_fun_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funeneg.
    by move: fx0; rewrite -{1}oppe0 -lee_oppr => /max_idPl ->.
  rewrite gee0_abs// /funeneg.
  by move: (fx0); rewrite -{1}oppe0 -lee_oppl => /max_idPr ->.
Qed.

Lemma integral_funepos_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\+ x < +oo.
Proof.
move=> [mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- by apply: emeasurable_fun_funepos => //; exact: emeasurable_funN.
- exact: measurable_fun_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// /funepos.
    by move: (fx0) => /max_idPr ->; rewrite -lee_oppr oppe0.
  by rewrite gee0_abs// /funepos; move: (fx0) => /max_idPl ->.
Qed.

Lemma integrable_neg_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\- x \is a fin_num.
Proof.
move=> fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/emeasurable_fun_funeneg.
- exact/measurable_fun_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) lee_addr.
Qed.

Lemma integrable_pos_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\+ x \is a fin_num.
Proof.
move=> fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/emeasurable_fun_funepos.
- exact/measurable_fun_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) lee_addl.
Qed.

End integrable.
Notation "mu .-integrable" := (integrable mu) : type_scope.
Arguments eq_integrable {d T R mu D} mD f.

Section sequence_measure.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Lemma integral_measure_series (D : set T) (mD : measurable D) (f : T -> \bar R) :
  (forall n, integrable (m_ n) D f) ->
  measurable_fun D f ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x | < +oo%E ->
  \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x | < +oo%E ->
  \int[m]_(x in D) f x = \sum_(n <oo) \int[m_ n]_(x in D) f x.
Proof.
move=> fi mf fmoo fpoo; rewrite integralE.
rewrite ge0_integral_measure_series//; last exact/emeasurable_fun_funepos.
rewrite ge0_integral_measure_series//; last exact/emeasurable_fun_funeneg.
transitivity (\sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\+ x))%:E -
              \sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\- x))%:E).
  by congr (_ - _); apply eq_eseries => n _; rewrite fineK//;
    [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
have fineKn : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|.
  apply eq_eseries => n _; congr abse; rewrite fineK//.
  exact: integrable_neg_fin_num.
have fineKp : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E|.
  apply eq_eseries => n _; congr abse; rewrite fineK//.
  exact: integrable_pos_fin_num.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -esumB//; last 4 first.
  - by rewrite /= /summable -nneseries_esum// -fineKp.
  - by rewrite /summable /= -nneseries_esum// -fineKn; exact: fmoo.
  - by move=> n _; exact/fine_ge0/integral_ge0.
  - by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -summable_nneseries_esum; last first.
  rewrite /summable.
  apply: (@le_lt_trans _ _ (\esum_(i in (fun=> true))
     `|(fine (\int[m_ i]_(x in D) f x))%:E|)).
    apply: le_esum => k _; rewrite -EFinB -fineB// -?integralE//;
      [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
  rewrite -nneseries_esum; last by [].
  apply: (@le_lt_trans _ _ (\sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E| +
                            \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|)).
    rewrite -nneseriesD//; apply lee_nneseries => // n _.
    rewrite integralE fineB// ?EFinB.
    - exact: (le_trans (lee_abs_sub _ _)).
    - exact: integrable_pos_fin_num.
    - exact: integrable_neg_fin_num.
  apply: lte_add_pinfty; first by rewrite -fineKp.
  by rewrite -fineKn; exact: fmoo.
by apply eq_eseries => k _; rewrite !fineK// -?integralE//;
  [exact: integrable_neg_fin_num|exact: integrable_pos_fin_num].
Qed.

End sequence_measure.

Section integrable_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_bigcup (F : (set _)^nat) (f : T -> \bar R) :
  (forall k, measurable (F k)) ->
  let D := \bigcup_k F k in
  mu.-integrable D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset setT F ->
  \int[mu]_(x in D) f x = \sum_(i <oo) \int[mu]_(x in F i) f x.
Proof.
move=> mF D fi f0 tF; pose f_ N := f \_ (\big[setU/set0]_(0 <= i < N) F i).
have lim_f_ t : f_ ^~ t --> (f \_ D) t.
  rewrite [X in _ --> X](_ : _ = ereal_sup (range (f_ ^~ t))); last first.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite /restrict; case: ifPn => [|_].
        rewrite in_setE => -[n _ Fnt]; apply: ereal_sup_ub; exists n.+1 => //.
        by rewrite /f_ big_mkord patchT// in_setE big_ord_recr/=; right.
      rewrite (@le_trans _ _ (f_ O t))// ?ereal_sup_ub//.
      by rewrite /f_ patchN// big_mkord big_ord0 inE/= in_set0.
    apply: ub_ereal_sup => x [n _ <-].
    by rewrite /f_ restrict_lee// big_mkord; exact: bigsetU_bigcup.
  apply: ereal_nondecreasing_cvg => a b ab.
  rewrite /f_ !big_mkord restrict_lee //; last exact: subset_bigsetU.
  by move=> x Dx; apply: f0 => //; exact: bigsetU_bigcup Dx.
transitivity (\int[mu]_x lim (f_ ^~ x)).
  rewrite integral_mkcond; apply: eq_integral => x _.
  by apply/esym/cvg_lim => //; exact: lim_f_.
rewrite monotone_convergence//; last 3 first.
  - move=> n; apply/(measurable_restrict f) => //.
      by apply: bigsetU_measurable => k _; exact: mF.
    case: fi => + _; apply/measurable_funS =>//; first exact: bigcup_measurable.
    by rewrite big_mkord; exact: bigsetU_bigcup.
  - move=> n x _; apply: erestrict_ge0 => y; rewrite big_mkord => Dy; apply: f0.
    exact: bigsetU_bigcup Dy.
  - move=> x _ a b ab; apply: restrict_lee.
      by move=> y; rewrite big_mkord => Dy; apply: f0; exact: bigsetU_bigcup Dy.
    by rewrite 2!big_mkord; apply: subset_bigsetU.
transitivity (lim (fun N => \int[mu]_(x in \big[setU/set0]_(i < N) F i) f x)).
  congr (lim _); rewrite funeqE => n.
  by rewrite /f_ [in RHS]integral_mkcond big_mkord.
congr (lim _); rewrite funeqE => /= n; rewrite ge0_integral_bigsetU ?big_mkord//.
- case: fi => + _; apply: measurable_funS => //; first exact: bigcup_measurable.
  exact: bigsetU_bigcup.
- by move=> y Dy; apply: f0; exact: bigsetU_bigcup Dy.
- exact: sub_trivIset tF.
Qed.

Lemma integrableS (E D : set T) (f : T -> \bar R) :
  measurable E -> measurable D -> D `<=` E ->
  mu.-integrable E f -> mu.-integrable D f.
Proof.
move=> mE mD DE [mf ifoo]; split; first exact: measurable_funS mf.
apply: le_lt_trans ifoo; apply: subset_integral => //.
exact: measurable_fun_comp.
Qed.

Lemma integrable_mkcond D f : measurable D ->
  mu.-integrable D f <-> mu.-integrable setT (f \_ D).
Proof.
move=> mD; rewrite /integrable [in X in X <-> _]integral_mkcond.
under [in X in X <-> _]eq_integral do rewrite restrict_abse.
split => [|] [mf foo].
- by split; [exact/(measurable_restrict _ _ _ _).1|
             exact: le_lt_trans foo].
- by split; [exact/(measurable_restrict _ _ measurableT _).2|
             exact: le_lt_trans foo].
Qed.

End integrable_lemmas.
Arguments integrable_mkcond {d T R mu D} f.

Section integrable_ae.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : T -> \bar R).
Hypotheses fint : mu.-integrable D f.

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite [X in measurable X](_ : _ = D `&` f @^-1` [set -oo; +oo]).
    by apply: fint.1 => //; exact: measurableU.
  rewrite predeqE => t; split=> [[/eqP ftoo Dt]|[Dt]].
    split => //.
    by move: ftoo; rewrite /preimage /= eqe_absl => /andP[/orP[|]/eqP]; tauto.
  by rewrite /preimage /= => -[|]; rewrite /E /= => ->.
have [ET|ET] := eqVneq E setT.
  have foo t : `|f t| = +oo by have [] : E t by rewrite ET.
  move: fint.2.
  suff: \int[mu]_(x in D) `|f x| = +oo by move=> ->; rewrite ltxx.
  by rewrite -(integral_cst_pinfty mD muD0)//; exact: eq_integral.
suff: mu E = 0.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt ftfin]; split => //.
  apply/eqP; rewrite eqe_absl leey andbT.
  by move/negP : ftfin; rewrite fin_numE negb_and 2!negbK orbC.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M M0 muM] : exists2 M, (0 <= M)%R &
    forall n, n%:R%:E * mu (E `&` D) <= M%:E.
  exists (fine (\int[mu]_(x in D) `|f x|)); first exact/fine_ge0/integral_ge0.
  move=> n.
  rewrite -integral_indic// -ge0_integralM//; last 2 first.
    - by apply: measurable_fun_comp=> //; exact/measurable_fun_indic.
    - by move=> *; rewrite lee_fin.
  rewrite fineK//; last first.
    by case: fint => _ foo; rewrite ge0_fin_numE//; exact: integral_ge0.
  apply: ge0_le_integral => //.
  - by move=> *; rewrite lee_fin /indic.
  - exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by apply: measurable_fun_comp => //; case: fint.
  - move=> x Dx; rewrite /= indicE.
    have [|xE] := boolP (x \in E); last by rewrite mule0.
    by rewrite /E inE /= => -[->]; rewrite leey.
apply/eqP/negPn/negP => /eqP muED0.
move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite leye_eq => /eqP ->; exists 1%N; rewrite mul1e leye_eq.
exists `|ceil (M * (fine (mu (E `&` D)))^-1)|%N.+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  by rewrite fin_numElt muEDoo andbT (lt_le_trans _ (measure_ge0 _ _)).
rewrite lte_fin -ltr_pdivr_mulr.
  rewrite -natr1 natr_absz ger0_norm.
    by rewrite (le_lt_trans (ceil_ge _))// ltr_addl.
  by rewrite ceil_ge0// divr_ge0//; apply/le0R/measure_ge0; exact: measurableI.
rewrite -lte_fin fineK.
  rewrite lt_neqAle measure_ge0// ?andbT.
  suff: E `&` D = E by move=> ->; apply/eqP/nesym.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section linearityM.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Lemma integralM r :
  \int[mu]_(x in D) (r%:E * f x) = r%:E * \int[mu]_(x in D) f x.
Proof.
have [r0|r0|->] := ltgtP r 0%R; last first.
  by under eq_fun do rewrite mul0e; rewrite mul0e integral0.
- rewrite [in LHS]integralE// gt0_funeposM// gt0_funenegM//.
  rewrite (ge0_integralM_EFin _ _ _ _ (ltW r0)) //; last first.
    by apply: emeasurable_fun_funepos => //; case: intf.
  rewrite (ge0_integralM_EFin _ _ _ _ (ltW r0)) //; last first.
    by apply: emeasurable_fun_funeneg => //; case: intf.
  rewrite -muleBr 1?[in RHS]integralE//.
  by apply: integrable_add_def; case: intf.
- rewrite [in LHS]integralE// lt0_funeposM// lt0_funenegM//.
  rewrite ge0_integralM_EFin //; last 2 first.
    + by apply: emeasurable_fun_funeneg => //; case: intf.
    + by rewrite -ler_oppr oppr0 ltW.
  rewrite ge0_integralM_EFin //; last 2 first.
    + by apply: emeasurable_fun_funepos => //; case: intf.
    + by rewrite -ler_oppr oppr0 ltW.
  rewrite -mulNe -EFinN opprK addeC EFinN mulNe -muleBr //; last first.
    by apply: integrable_add_def; case: intf.
  by rewrite [in RHS]integralE.
Qed.

End linearityM.

Section linearity.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f1 f2 : T -> R).
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : mu.-integrable D g1.
Hypothesis if2 : mu.-integrable D g2.

Lemma integralD_EFin :
  \int[mu]_(x in D) (g1 \+ g2) x =
  \int[mu]_(x in D) g1 x + \int[mu]_(x in D) g2 x.
Proof.
suff: \int[mu]_(x in D) ((g1 \+ g2)^\+ x) + \int[mu]_(x in D) (g1^\- x) +
        \int[mu]_(x in D) (g2^\- x) =
      \int[mu]_(x in D) ((g1 \+ g2)^\- x) + \int[mu]_(x in D) (g1^\+ x) +
        \int[mu]_(x in D) (g2^\+ x).
  move=> h; rewrite [in LHS]integralE.
  move/eqP : h; rewrite -[in eqRHS]addeA [in eqRHS]addeC.
  have g12pos :
      \int[mu]_(x in D) (g1^\+ x) + \int[mu]_(x in D) (g2^\+ x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funepos_lt_pinfty.
    by apply: adde_ge0; exact: integral_ge0.
  have g12neg :
      \int[mu]_(x in D) (g1^\- x) + \int[mu]_(x in D) (g2^\- x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty// ; exact: integral_funeneg_lt_pinfty.
    by apply: adde_ge0; exact: integral_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        have : mu.-integrable D (g1 \+ g2) by apply: integrableD.
        exact: integral_funepos_lt_pinfty.
      apply: adde_ge0; last exact: integral_ge0.
      by apply: adde_ge0; exact: integral_ge0.
    - by rewrite adde_defC fin_num_adde_def.
  rewrite -(addeA (\int[mu]_(x in D) (g1 \+ g2)^\+ x)).
  rewrite (addeC (\int[mu]_(x in D) (g1 \+ g2)^\+ x)).
  rewrite -addeA (addeC (\int[mu]_(x in D) g1^\- x + \int[mu]_(x in D) g2^\- x)).
  rewrite eq_sym -(sube_eq g12pos); last by rewrite fin_num_adde_def.
  move/eqP => <-.
  rewrite oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funeneg_lt_pinfty if2.
    exact: integral_ge0.
  rewrite -addeA (addeCA (\int[mu]_(x in D) (g2^\+ x) )).
  by rewrite addeA -(integralE _ _ g1) -(integralE _ _ g2).
have : (g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in eqRHS]addeC -sube_eq; last 2 first.
    by rewrite /funepos /funeneg /g1 /g2 /= !maxEFin.
    by rewrite /funepos /funeneg /g1 /g2 /= !maxEFin.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite /funepos /funeneg !maxEFin.
    by rewrite /funepos /funeneg !maxEFin.
  apply/eqP.
  rewrite -[LHS]/((g1^\+ \+ g2^\+ \- (g1^\- \+ g2^\-)) x) -funeD_posD.
  by rewrite -[RHS]/((_ \- _) x) -funeD_Dpos.
move/(congr1 (fun y => \int[mu]_(x in D) (y x) )).
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0.
  - apply: emeasurable_funD.
      by apply/emeasurable_fun_funepos/emeasurable_funD; [case: if1|case: if2].
    by apply: emeasurable_fun_funeneg; case: if1.
  - by [].
  - by apply: emeasurable_fun_funeneg; case: if2.
rewrite (ge0_integralD mu mD); last 4 first.
  - by [].
  - by apply/emeasurable_fun_funepos/emeasurable_funD; [case: if1|case: if2].
  - by [].
  - by apply/emeasurable_fun_funepos/emeasurable_funN => //; case: if1.
move=> ->.
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; exact: adde_ge0.
  - apply: emeasurable_funD.
      by apply/emeasurable_fun_funeneg/emeasurable_funD; [case: if1|case: if2].
    by apply: emeasurable_fun_funepos; case: if1.
  - by [].
  - by apply: emeasurable_fun_funepos; case: if2.
rewrite (ge0_integralD mu mD) //.
- by apply/emeasurable_fun_funeneg/emeasurable_funD => //; [case: if1|case: if2].
- by apply: emeasurable_fun_funepos; case: if1.
Qed.

End linearity.

Lemma integralB_EFin d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f1 f2 : T -> R)
  (mD : measurable D) :
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  (\int[mu]_(x in D) ((f1 x)%:E - (f2 x)%:E) =
    (\int[mu]_(x in D) (f1 x)%:E - \int[mu]_(x in D) (f2 x)%:E))%E.
Proof.
move=> if1 if2; rewrite (integralD_EFin mD if1); last first.
  by rewrite (_ : _ \o _ = (fun x => - (f2 x)%:E))%E; [exact: integrableN|by []].
by rewrite -integralN//; exact: integrable_add_def.
Qed.

Lemma le_abse_integral d (R : realType) (T : measurableType d)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R)
  (mD : measurable D) : measurable_fun D f ->
  (`| \int[mu]_(x in D) (f x) | <= \int[mu]_(x in D) `|f x|)%E.
Proof.
move=> mf.
rewrite integralE (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: integral_ge0.
rewrite gee0_abs; last exact: integral_ge0.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: emeasurable_fun_funepos | exact: emeasurable_fun_funeneg].
Qed.

Section integral_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_setI_indic (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  \int[mu]_(x in E `&` D) f x = \int[mu]_(x in E) (f x * (\1_D x)%:E).
Proof.
move=> mE; rewrite integral_mkcondr; apply: eq_integral => x xE.
by rewrite indic_restrict /patch; case: ifPn; rewrite ?mule1 ?mule0.
Qed.

Lemma integralEindic (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f x * (\1_D x)%:E).
Proof. by rewrite -integral_setI_indic// setIid. Qed.

End integral_indic.

Section ae_eq.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Implicit Types f g h i : T -> \bar R.

Definition ae_eq f g := {ae mu, forall x, D x -> f x = g x}.

Lemma ae_eq_comp (j : \bar R -> \bar R) f g :
  ae_eq f g -> ae_eq (j \o f) (j \o g).
Proof.
move=> [N [mN N0 subN]]; exists N; split => //.
by apply: subset_trans subN; apply: subsetC => x /= /[apply] ->.
Qed.

Lemma ae_eq_funeposneg f g : ae_eq f g <-> ae_eq f^\+ g^\+ /\ ae_eq f^\- g^\-.
Proof.
split=> [[N [mN N0 DfgN]]|[[A [mA A0 DfgA] [B [mB B0 DfgB]]]]].
  by split; exists N; split => // x Dfgx; apply: DfgN => /=;
    apply: contra_not Dfgx => /= /[apply]; rewrite /funepos /funeneg => ->.
exists (A `|` B); rewrite null_set_setU//; split=> //; first exact: measurableU.
move=> x /= /not_implyP[Dx fgx]; apply: contrapT => /not_orP[Ax Bx].
have [fgpx|fgnx] : f^\+ x <> g^\+ x \/ f^\- x <> g^\- x.
  apply: contrapT => /not_orP[/contrapT fgpx /contrapT fgnx].
  by apply: fgx; rewrite (funeposneg f) (funeposneg g) fgpx fgnx.
- by apply: Ax; exact/DfgA/not_implyP.
- by apply: Bx; exact/DfgB/not_implyP.
Qed.

Lemma ae_eq_sym f g : ae_eq f g -> ae_eq g f.
Proof.
move=> [N1 [mN1 N10 subN1]]; exists N1; split => // x /= Dba; apply: subN1 => /=.
by apply: contra_not Dba => [+ Dx] => ->.
Qed.

Lemma ae_eq_trans f g h : ae_eq f g -> ae_eq g h -> ae_eq f h.
Proof.
move=> [N1 [mN1 N10 abN1]] [N2 [mN2 N20 bcN2]]; exists (N1 `|` N2); split => //.
- exact: measurableU.
- by rewrite null_set_setU.
- rewrite -(setCK N1) -(setCK N2) -setCI; apply: subsetC => x [N1x N2x] /= Dx.
  move/subsetC : abN1 => /(_ _ N1x); rewrite setCK /= => ->//.
  by move/subsetC : bcN2 => /(_ _ N2x); rewrite setCK /= => ->.
Qed.

Lemma ae_eq_sub f g h i : ae_eq f g -> ae_eq h i -> ae_eq (f \- h) (g \- i).
Proof.
move=> [N1 [mN1 N10 abN1]] [N2 [mN2 N20 bcN2]]; exists (N1 `|` N2); split => //.
- exact: measurableU.
- by rewrite null_set_setU.
- rewrite -(setCK N1) -(setCK N2) -setCI; apply: subsetC => x [N1x N2x] /= Dx.
  move/subsetC : abN1 => /(_ _ N1x); rewrite setCK /= => ->//.
  by move/subsetC : bcN2 => /(_ _ N2x); rewrite setCK /= => ->.
Qed.

Lemma ae_eq_mul2r f g h : ae_eq f g -> ae_eq (f \* h) (g \* h).
Proof.
move=> [N1 [mN1 N10 abN1]]; exists N1; split => // x /= /not_implyP[Dx].
move=> acbc; apply: abN1 => /=; apply/not_implyP; split => //.
by apply: contra_not acbc => ->.
Qed.

Lemma ae_eq_mul2l f g h : ae_eq f g -> ae_eq (h \* f) (h \* g).
Proof.
move=> /ae_eq_mul2r-/(_ h); under eq_fun do rewrite muleC.
by under [in X in ae_eq _ X -> _]eq_fun do rewrite muleC.
Qed.

Lemma ae_eq_mul1l f g : ae_eq f (cst 1) -> ae_eq g (g \* f).
Proof.
move=> /ae_eq_mul2l-/(_ g)/ae_eq_sym.
by under [in X in ae_eq X _ -> _]eq_fun do rewrite mule1.
Qed.

Lemma ae_eq_mul f g h : ae_eq f g -> ae_eq (f \* h) (g \* h).
Proof.
move=> [N1 [mN1 N10 abN1]]; exists N1; split => // x /= /not_implyP[Dx].
move=> acbc; apply: abN1 => /=; apply/not_implyP; split => //.
by apply: contra_not acbc => ->.
Qed.

Lemma ae_eq_abse f g : ae_eq f g -> ae_eq (abse \o f) (abse \o g).
Proof.
move=> [N [mN N0 subN]]; exists N; split => //; apply: subset_trans subN.
by apply: subsetC => x /= /[apply] ->.
Qed.

End ae_eq.

Section ae_eq_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Local Notation ae_eq := (ae_eq mu).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  ae_eq D f (cst 0) -> \int[mu]_(x in D) `|f x|%E  = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose Df_neq0 := D `&` [set x | f x != 0].
have mDf_neq0 : measurable Df_neq0 by exact: emeasurable_neq.
pose f' : T -> R := indic Df_neq0.
have le_f_M t : D t -> `|f t| <= M%:E * (f' t)%:E.
  move=> Dt; rewrite /f' indicE; have [|] := boolP (t \in Df_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  by rewrite notin_set=> /not_andP[//|/negP/negPn/eqP ->]; rewrite abse0 mule0.
have : 0 <= \int[mu]_(x in D) `|f x|  <= `|M|%:E * mu Df_neq0.
  rewrite integral_ge0//= /Df_neq0 -{2}(setIid D) setIAC -integral_indic//.
  rewrite -/Df_neq0 -ge0_integralM//; last 2 first.
    - by apply: measurable_fun_comp=> //; exact: measurable_fun_indic.
    - by move=> x ?; rewrite lee_fin.
  apply: ge0_le_integral => //.
  - exact: measurable_fun_comp.
  - by move=> x Dx; rewrite mule_ge0// lee_fin.
  - apply: emeasurable_funM; first exact: measurable_fun_cst.
    by apply: measurable_fun_comp => //; exact: measurable_fun_indic.
  - move=> x Dx.
    rewrite (le_trans (le_f_M _ Dx))// lee_fin /f' indicE.
    by case: (_ \in _) => //; rewrite ?mulr1 ?mulr0// ler_norm.
have -> : mu Df_neq0 = 0.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
by rewrite mule0 -eq_le => /eqP.
Qed.

Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable_fun D f -> \int[mu]_(x in D) `|f x|  = 0 <-> ae_eq D f (cst 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists (D `&` [set x | f x != 0]); split; [exact: emeasurable_neq| |]; last first.
    by move=> t /= /not_implyP [Dt /eqP ft0].
  have muDf a : (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x |]) = 0.
    move=> a0; apply/eqP; rewrite eq_le measure_ge0 ?andbT; last first.
    move: (@le_integral_abse _ _ _ mu _ mD _ _ mf a0).
    by rewrite -lee_pdivl_mull// iDf0 mule0 setIC.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[Dt ft0]|[n _ /= [Dt nft]]].
      have [ftoo|ftoo] := eqVneq `|f t| +oo%E.
        by exists 0%N => //; split => //=; rewrite ftoo /= leey.
      pose m := `|ceil (fine `|f t|)^-1|%N.
      have ftfin : `|f t|%E \is a fin_num.
        by rewrite fin_numE gt_eqF //= (lt_le_trans _ (abse_ge0 _)).
      exists m => //; split => //=.
      rewrite -(@fineK _ `|f t|) // lee_fin -ler_pinv; last 2 first.
        - rewrite inE unitfE fine_eq0 // abse_eq0 ft0/=; apply/fine_gt0.
          by rewrite lt_neqAle abse_ge0 -ge0_fin_numE// eq_sym abse_eq0 ft0.
        - by rewrite inE unitfE invr_eq0 pnatr_eq0 /= invr_gt0.
      rewrite invrK /m -natr1 natr_absz ger0_norm ?ceil_ge0//.
      apply: (@le_trans _ _ ((fine `|f t|)^-1 + 1)%R); first by rewrite ler_addl.
      by rewrite ler_add2r// ceil_ge.
    by split => //; apply: contraTN nft => /eqP ->; rewrite abse0 -ltNge.
  transitivity (lim (fun n => mu (D `&` [set x | `|f x| >= n.+1%:R^-1%:E]))).
    apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
    - move=> i; apply: emeasurable_fun_c_infty => //.
      exact: measurable_fun_comp.
    - apply: bigcupT_measurable => i.
      by apply: emeasurable_fun_c_infty => //; exact: measurable_fun_comp.
    - move=> m n mn; apply/subsetPset; apply: setIS => t /=.
      by apply: le_trans; rewrite lee_fin lef_pinv // ?ler_nat // posrE.
  by rewrite (_ : (fun _ => _) = cst 0) ?lim_cst//= funeqE => n /=; rewrite muDf.
pose f_ := fun n x => mine `|f x| n%:R%:E.
have -> : (fun x => `|f x|) = (fun x => lim (f_^~ x)).
  rewrite funeqE => x; apply/esym/cvg_lim => //; apply/cvg_ballP => _/posnumP[e].
  near=> n; rewrite /ball /= /ereal_ball /= /f_.
  have [->|fxoo] := eqVneq `|f x|%E +oo.
    rewrite /= (@ger0_norm _ n%:R)// ger0_norm; last first.
      by rewrite subr_ge0 ler_pdivr_mulr ?mul1r ?ler_addr.
    rewrite -{1}(@divrr _ (1 + n%:R)%R) ?unitfE; last first.
      by rewrite gt_eqF// {1}(_ : 1 = 1%:R)%R // natrS.
    rewrite -mulrBl addrK ltr_pdivr_mulr; last first.
      by rewrite {1}(_ : 1 = 1%:R)%R // natrS.
    rewrite mulrDr mulr1 ltr_spsaddl// -ltr_pdivr_mull// mulr1.
    near: n.
    exists `|ceil (1 + e%:num^-1)|%N => // n /=.
    rewrite -(@ler_nat R); apply: lt_le_trans.
    rewrite natr_absz ger0_norm ?ceil_ge ?ceil_ge0//.
    by rewrite (lt_le_trans _ (ceil_ge _))// ltr_addr.
  have fxn : `|f x| <= n%:R%:E.
    rewrite -(@fineK _ `|f x|); last first.
      by rewrite fin_numE fxoo andbT gt_eqF// (lt_le_trans _ (abse_ge0 _)).
    rewrite lee_fin.
    near: n.
    exists `|ceil (fine (`|f x|))|%N => // n /=.
    rewrite -(@ler_nat R); apply: le_trans.
    by rewrite natr_absz ger0_norm ?ceil_ge// ceil_ge0.
  by rewrite min_l// subrr normr0.
transitivity (lim (fun n => \int[mu]_(x in D) (f_ n x) )).
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
have if_0 n : \int[mu]_(x in D) `|f_ n x|  = 0.
  apply: (@ae_eq_integral_abs_bounded _ _ _ n%:R) => //.
    by apply: emeasurable_fun_min => //;
      [exact: measurable_fun_comp|exact: measurable_fun_cst].
  exact: f_bounded.
rewrite (_ : (fun _ => _) = (cst 0)) // ?lim_cst// funeqE => n.
rewrite (_ : (fun x => f_ n x) = abse \o f_ n); first exact: if_0.
rewrite funeqE => x /=; rewrite gee0_abs// /f_.
by have [|_] := leP `|f x| n%:R%:E; [by []|rewrite lee_fin].
Unshelve. all: by end_near. Qed.

Lemma integral_abs_eq0 D (N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> N `<=` D -> measurable_fun D f ->
  mu N = 0 -> \int[mu]_(x in N) `|f x| = 0.
Proof.
move=> mN mD ND mf muN0; rewrite integralEindic//.
rewrite (eq_integral (fun x => `|f x * (\1_N x)%:E|)); last first.
  by move=> t _; rewrite abseM (@gee0_abs _ (\1_N t)%:E)// lee_fin.
apply/ae_eq_integral_abs => //.
  apply: emeasurable_funM => //; first exact: (measurable_funS mD).
  exact/EFin_measurable_fun/measurable_fun_indic.
exists N; split => // t /= /not_implyP[_]; rewrite indicE.
by have [|] := boolP (t \in N); rewrite ?inE ?mule0.
Qed.

Lemma funID (N : set T) (mN : measurable N) (f : T -> \bar R) :
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

Lemma negligible_integrable (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  mu N = 0 -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> mN mD mf muN0.
pose mCN := measurableC mN.
pose oneCN : {nnsfun T >-> R} := [the {nnsfun T >-> R} of mindic R mCN].
pose oneN : {nnsfun T >-> R} := [the {nnsfun T >-> R} of mindic R mN].
have intone : mu.-integrable D (fun x => f x * (oneN x)%:E).
  split.
    apply: emeasurable_funM=> //; apply/EFin_measurable_fun.
    exact: measurable_funTS.
  rewrite (eq_integral (fun x => `|f x| * (\1_N x)%:E)); last first.
    by move=> t _; rewrite abseM (@gee0_abs _ (\1_N t)%:E) // lee_fin.
  rewrite -integral_setI_indic// (@integral_abs_eq0 D)//.
  - exact: measurableI.
  - by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
have h1 : mu.-integrable D f <-> mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intf|intCf].
    split.
      apply: emeasurable_funM=> //; apply/EFin_measurable_fun => //.
      exact: measurable_funTS.
    rewrite (eq_integral (fun x => `|f x| * (\1_(~` N) x)%:E)); last first.
      by move=> t _; rewrite abseM (@gee0_abs _ (\1_(~` N) t)%:E) // lee_fin.
    rewrite -integral_setI_indic//; case: intf => _; apply: le_lt_trans.
    by apply: subset_integral => //; [exact:measurableI|exact:measurable_fun_comp].
  split => //; rewrite (funID mN f) -/oneCN -/oneN.
  have ? : measurable_fun D (fun x : T => f x * (oneCN x)%:E).
    by apply: emeasurable_funM=> //; exact/EFin_measurable_fun/measurable_funTS.
  have ? : measurable_fun D (fun x : T => f x * (oneN x)%:E).
    apply: emeasurable_funM => //.
    exact/EFin_measurable_fun/measurable_funTS.
  apply: (@le_lt_trans _ _
    (\int[mu]_(x in D) (`|f x * (oneCN x)%:E| + `|f x * (oneN x)%:E|))).
    apply: ge0_le_integral => //.
    - by apply: measurable_fun_comp => //; exact: emeasurable_funD.
    - by apply: emeasurable_funD; exact: measurable_fun_comp.
    - by move=> *; rewrite lee_abs_add.
  rewrite ge0_integralD//;
    [|exact: measurable_fun_comp|exact: measurable_fun_comp].
  by apply: lte_add_pinfty; [case: intCf|case: intone].
have h2 : mu.-integrable (D `\` N) f <->
    mu.-integrable D (fun x => f x * (oneCN x)%:E).
  split=> [intCf|intCf].
    split.
      apply: emeasurable_funM=> //; apply/EFin_measurable_fun => //.
      exact: measurable_funTS.
    rewrite (eq_integral (fun x => `|f x| * (\1_(~` N) x)%:E)); last first.
      by move=> t _; rewrite abseM (@gee0_abs _ (\1_(~` N) t)%:E)// lee_fin.
    rewrite -integral_setI_indic //; case: intCf => _; apply: le_lt_trans.
    apply: subset_integral=> //; [exact: measurableI|exact: measurableD|].
    by apply: measurable_fun_comp => //; apply: measurable_funS mf => // ? [].
  split.
    move=> mDN A mA; rewrite setDE (setIC D) -setIA; apply: measurableI => //.
    exact: mf.
  rewrite integral_setI_indic//.
  case: intCf => _; rewrite (eq_integral (fun x => `|f x| * (\1_(~` N) x)%:E))//.
  by move=> t _; rewrite abseM (@gee0_abs _ (\1_(~` N) t)%:E)// lee_fin.
by apply: (iff_trans h1); exact: iff_sym.
Qed.

Lemma negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf f0 muN0.
rewrite {1}(funID mN f) ge0_integralD//; last 4 first.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
  - apply: emeasurable_funM=> //; apply/EFin_measurable_fun=> //.
    exact: measurable_funTS.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
  - apply: emeasurable_funM=> //; apply/EFin_measurable_fun=> //.
    exact: measurable_funTS.
rewrite -integral_setI_indic//; last exact: measurableC.
rewrite -integral_setI_indic// [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite (eq_integral (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite (@integral_abs_eq0 D)//; first exact: measurableI.
by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) ->
  ae_eq D f g -> \int[mu]_(x in D) (f x)  = \int[mu]_(x in D) (g x).
Proof.
move=> mD mf mg f0 g0 [N [mN N0 subN]].
rewrite integralEindic// [RHS]integralEindic//.
rewrite (negligible_integral mN)//; last 2 first.
  - apply: emeasurable_funM => //.
    exact/EFin_measurable_fun/measurable_fun_indic.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: f0|rewrite lee_fin].
rewrite [RHS](negligible_integral mN)//; last 2 first.
  - apply: emeasurable_funM => //.
    exact/EFin_measurable_fun/measurable_fun_indic.
  - by move=> x Dx; apply: mule_ge0 => //; [exact: g0|rewrite lee_fin].
- apply: eq_integral => x;rewrite in_setD => /andP[_ xN].
  apply: contrapT; rewrite indicE; have [|?] := boolP (x \in D).
    rewrite inE => Dx; rewrite !mule1.
    move: xN; rewrite notin_set; apply: contra_not => fxgx; apply: subN => /=.
    exact/not_implyP.
  by rewrite !mule0.
Qed.

Lemma ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  ae_eq D f g -> integral mu D f = integral mu D g.
Proof.
move=> mD mf mg /ae_eq_funeposneg[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funepos|
                                      exact: emeasurable_fun_funepos].
by apply: ge0_ae_eq_integral => //; [exact: emeasurable_fun_funeneg|
                                    exact: emeasurable_fun_funeneg].
Qed.

End ae_eq_integral.

Section ae_measurable_fun.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Hypothesis cmu : measure_is_complete mu.
Variables (D : set T) (f g : T -> \bar R).

Lemma ae_measurable_fun : ae_eq mu D f g ->
  measurable_fun D f -> measurable_fun D g.
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

Section integralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
pose A := D `&` [set x | f1 x \is a fin_num].
pose B := D `&` [set x | f2 x \is a fin_num].
have mA : measurable A by apply: emeasurable_fin_num => //; case: if1.
have mB : measurable B by apply: emeasurable_fin_num => //; case: if2.
have mAB : measurable (A `&` B) by apply: measurableI.
pose g1 := (fine \o f1 \_ (A `&` B))%R.
pose g2 := (fine \o f2 \_ (A `&` B))%R.
have ig1 : mu.-integrable D (EFin \o g1).
  rewrite (_ : _ \o _ = f1 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if1=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g1 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite 2!in_setI => /andP[/andP[xA f1xfin] _] /=.
  by rewrite fineK//; rewrite inE in f1xfin.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if2=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g2 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite in_setI => /andP[_]; rewrite in_setI => /andP[xB f2xfin] /=.
  by rewrite fineK//; rewrite inE in f2xfin.
transitivity (\int[mu]_(x in D) (EFin \o (g1 \+ g2)%R) x).
  apply: ae_eq_integral => //.
  - by apply: emeasurable_funD => //; [case: if1|case: if2].
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    by apply: emeasurable_funD => //; [case: ig1|case: ig2].
  - have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split; [exact: measurableU|by rewrite null_set_setU|].
    rewrite -(setCK N1) -(setCK N2) -setCI.
    apply: subsetC => x [N1x N2x] /= Dx.
    move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
    move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
    rewrite /g1 /g2 /restrict /=; have [|] := boolP (x \in A `&` B).
      by rewrite in_setI => /andP[xA xB] /=; rewrite EFinD !fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx)/= notin_set/=.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// integralD_EFin//.
  congr (_ + _).
  + apply: ae_eq_integral => //; [by case: ig1|by case: if1|].
    have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split; [exact: measurableU|by rewrite null_set_setU|].
    rewrite -(setCK N1) -(setCK N2) -setCI.
    apply: subsetC => x [N1x N2x] /= Dx.
    move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
    move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
    rewrite /g1 /= /restrict.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_set.
  + apply: ae_eq_integral => //;[by case: ig2|by case: if2|].
    have [N1 [mN1 N10 subN1]] := integrable_ae mD if1.
    have [N2 [mN2 N20 subN2]] := integrable_ae mD if2.
    exists (N1 `|` N2); split; [exact: measurableU|by rewrite null_set_setU|].
    rewrite -(setCK N1) -(setCK N2) -setCI.
    apply: subsetC => x [N1x N2x] /= Dx.
    move/subsetC : subN1 => /(_ x N1x); rewrite setCK /= => /(_ Dx) f1x.
    move/subsetC : subN2 => /(_ x N2x); rewrite setCK /= => /(_ Dx) f2x.
    rewrite /g2 /= /restrict.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_set.
Qed.

End integralD.

Section integralB.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T).
Variables (mD : measurable D) (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Lemma integralB : \int[mu]_(x in D) (f1 \- f2) x =
                  \int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x.
Proof.
rewrite -[in RHS](@integralN _ _ _ _ _ f2); last exact: integrable_add_def.
by rewrite -[in RHS]integralD//; exact: integrableN.
Qed.

End integralB.

Section integrable_fune.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Local Open Scope ereal_scope.

Lemma integral_fune_lt_pinfty (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x < +oo.
Proof.
move=> intf; rewrite (funeposneg f) integralB//;
  [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite lte_add_pinfty ?integral_funepos_lt_pinfty// lte_oppl ltNye_eq.
by rewrite integrable_neg_fin_num.
Qed.

Lemma integral_fune_fin_num (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x \is a fin_num.
Proof.
move=> h; apply/fin_numPlt; rewrite integral_fune_lt_pinfty// andbC/= -/(- +oo).
rewrite lte_oppl -integralN; first exact/integral_fune_lt_pinfty/integrableN.
by rewrite fin_num_adde_def// fin_numN integrable_neg_fin_num.
Qed.

End integrable_fune.

Section integral_counting.
Local Open Scope ereal_scope.
Variables (R : realType).

Lemma counting_dirac (A : set nat) : counting R A = \sum_(n <oo) \d_ n A.
Proof.
have -> : \sum_(n <oo) \d_ n A = \esum_(i in A) \d_ i A :> \bar R.
  rewrite nneseries_esum// (_ : [set _ | _] = setT); last exact/seteqP.
  rewrite [in LHS](esumID A)// !setTI [X in _ + X](_ : _ = 0) ?adde0//.
  by apply esum1 => i Ai; rewrite /= /dirac indicE memNset.
rewrite /counting/=; case: ifPn => /asboolP finA.
  by rewrite -finite_card_dirac.
by rewrite infinite_card_dirac.
Qed.

Lemma summable_integral_dirac (a : nat -> \bar R) : summable setT a ->
  \sum_(n <oo) `|\int[\d_ n]_x a x| < +oo.
Proof.
move=> sa.
apply: (@le_lt_trans _ _ (\sum_(i <oo) `|fine (a i)|%:E)).
  apply lee_nneseries => // n _; rewrite integral_dirac//.
  move: (@summable_pinfty _ _ _ _ sa n Logic.I).
  by case: (a n) => //= r _; rewrite indicE/= mem_set// mul1r.
move: (sa); rewrite /summable (_ : [set: nat] = (fun=> true))//; last exact/seteqP.
rewrite -nneseries_esum//; apply: le_lt_trans.
by apply lee_nneseries => // n _ /=; case: (a n) => //; rewrite leey.
Qed.

Lemma integral_count (a : nat -> \bar R) : summable setT a ->
  \int[counting R]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => [the measure _ _ of \d_ n]) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@integral_measure_series _ _ R (fun n => [the measure _ _ of \d_ n]) setT)//=.
- apply: eq_eseries => i _; rewrite integral_dirac//=.
  by rewrite indicE mem_set// mul1e.
- move=> n; split; first by [].
  by rewrite integral_dirac//= indicE mem_set// mul1e; exact: (summable_pinfty sa).
- by apply: summable_integral_dirac => //; exact: summable_funeneg.
- by apply: summable_integral_dirac => //; exact: summable_funepos.
Qed.

End integral_counting.

Section subadditive_countable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integrable_abse (D : set T) : measurable D ->
  forall f : T -> \bar R, mu.-integrable D f -> mu.-integrable D (abse \o f).
Proof.
move=> mD f [mf fi]; split; first exact: measurable_fun_comp.
apply: le_lt_trans fi; apply: ge0_le_integral => //.
- by apply: measurable_fun_comp => //; exact: measurable_fun_comp.
- exact: measurable_fun_comp.
- by move=> t Dt //=; rewrite abse_id.
Qed.

Lemma integrable_summable (F : (set T)^nat) (g : T -> \bar R):
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  summable [set: nat] (fun i => \int[mu]_(x in F i) g x).
Proof.
move=> tF mF fi.
rewrite /summable -(_ : [set _ | true] = setT); last exact/seteqP.
rewrite -nneseries_esum//.
case: (fi) => _; rewrite ge0_integral_bigcup//; last first.
  by apply: integrable_abse => //; exact: bigcup_measurable.
apply: le_lt_trans; apply: lee_lim.
- exact: is_cvg_ereal_nneg_natsum_cond.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ _; exact: integral_ge0.
- apply: nearW => n; apply: lee_sum => m _; apply: le_abse_integral => //.
  by apply: measurable_funS fi.1 => //; [exact: bigcup_measurable|
                                        exact: bigcup_sup].
Qed.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int[mu]_(x in \bigcup_i F i) g x = \sum_(i <oo) \int[mu]_(x in F i) g x)%E.
Proof.
move=> tF mF fi.
have ? : \int[mu]_(x in \bigcup_i F i) g x \is a fin_num.
  rewrite fin_numElt -(lte_absl _ +oo).
  apply: le_lt_trans fi.2; apply: le_abse_integral => //.
    exact: bigcupT_measurable.
  exact: fi.1.
transitivity (\int[mu]_(x in \bigcup_i F i) g^\+ x -
              \int[mu]_(x in \bigcup_i F i) g^\- x)%E.
  rewrite -integralB; last 3 first.
    - exact: bigcupT_measurable.
    - by apply: integrable_funepos => //; exact: bigcupT_measurable.
    -by apply: integrable_funeneg => //; exact: bigcupT_measurable.
  by apply eq_integral => t Ft; rewrite [in LHS](funeposneg g).
transitivity (\sum_(i <oo) (\int[mu]_(x in F i) g^\+ x -
                            \int[mu]_(x in F i) g^\- x)); last first.
  by apply: eq_eseries => // i; rewrite [RHS]integralE.
transitivity ((\sum_(i <oo) \int[mu]_(x in F i) g^\+ x) -
              (\sum_(i <oo) \int[mu]_(x in F i) g^\- x))%E.
  rewrite ge0_integral_bigcup//; last first.
    by apply: integrable_funepos => //; exact: bigcupT_measurable.
  by rewrite ge0_integral_bigcup//; apply: integrable_funepos => //;
    [exact: bigcupT_measurable|exact: integrableN].
rewrite [X in X - _]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite [X in _ - X]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite set_true -esumB//=; last 4 first.
  - apply: integrable_summable => //; apply: integrable_funepos => //.
    exact: bigcup_measurable.
  - apply: integrable_summable => //; apply: integrable_funepos => //.
    exact: bigcup_measurable.
  - exact: integrableN.
  - by move=> n _; exact: integral_ge0.
  - by move=> n _; exact: integral_ge0.
rewrite summable_nneseries; last first.
  rewrite (_ : (fun i : nat => _) = (fun i => \int[mu]_(x in F i) g x)); last first.
    by apply/funext => i; rewrite -integralE.
  rewrite -(_ : [set: nat] = (fun=> true)); last exact/seteqP.
  exact: integrable_summable.
by congr (_ - _)%E; rewrite nneseries_esum// set_true.
Qed.

End subadditive_countable.

Section dominated_convergence_lemma.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f_ : (T -> \bar R)^nat) (f : T -> \bar R) (g : T -> \bar R).
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Hypothesis f_f : forall x, D x -> f_ ^~ x --> f x.
Hypothesis fing : forall x, D x -> g x \is a fin_num.
Hypothesis ig : mu.-integrable D g.
Hypothesis absfg : forall n x, D x -> `|f_ n x| <= g x.

Let g0 x : D x -> 0 <= g x.
Proof. by move=> Dx; rewrite (le_trans _ (@absfg O _ Dx))// lee_fin. Qed.

Let mf : measurable_fun D f.
Proof. exact: (emeasurable_fun_cvg _ _ mf_ f_f). Qed.

Local Lemma dominated_integrable : mu.-integrable D f.
Proof.
split => //; have Dfg x : D x -> `| f x | <= g x.
  move=> Dx; have /(@cvg_lim _) <- // : `|f_ n x| @[n --> \oo] --> `|f x|.
    by apply: cvg_abse => //; exact: f_f.
  apply: lime_le => //.
  - by apply: is_cvg_abse; apply/cvg_ex; eexists; exact: f_f.
  - by apply: nearW => n; exact: absfg.
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
- by move=> f_r; apply/cvge_sub0.
- move/cvgeyPge/(_ (fine (g x) + 1)%R) => [n _]/(_ _ (leqnn n))/= h.
  have : (fine (g x) + 1)%:E <= g x.
    by rewrite (le_trans h)// (le_trans _ (absfg n Dx))// lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lte_addl ?lte01.
- move/cvgeNyPle/(_ (- (fine (g x) + 1))%R) => [n _]/(_ _ (leqnn n)) h.
  have : (fine (g x) + 1)%:E <= g x.
    move: h; rewrite EFinN lee_oppr => /le_trans ->//.
    by rewrite (le_trans _ (absfg n Dx))// -abseN lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lte_addl ?lte01.
Qed.

Let gg_ n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof.
move=> Dx; rewrite subre_ge0; last by rewrite fin_numM// fing.
rewrite -(fineK (fing Dx)) -EFinM mulr_natl mulr2n /g_.
rewrite (le_trans (lee_abs_sub _ _))// [in leRHS]EFinD lee_add//.
  by rewrite fineK// ?fing// absfg.
have f_fx : `|(f_ n x)| @[n --> \oo] --> `|f x| by apply: cvg_abse; exact: f_f.
move/cvg_lim : (f_fx) => <-//.
apply: lime_le; first by apply/cvg_ex; eexists; exact: f_fx.
by apply: nearW => k; rewrite fineK ?fing//; apply: absfg.
Qed.

Let mgg n : measurable_fun D (fun x => 2%:E * g x - g_ n x).
Proof.
apply/emeasurable_funB => //; first by apply: measurable_funeM; case: ig.
by apply/measurable_fun_comp => //; exact: emeasurable_funB.
Qed.

Let gg_ge0 n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof. by move=> Dx; rewrite gg_. Qed.

Local Lemma dominated_cvg0 : [sequence \int[mu]_(x in D) g_ n x]_n --> 0.
Proof.
have := fatou mu mD mgg gg_ge0.
rewrite [X in X <= _ -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x) ); last first.
  apply: eq_integral => t; rewrite inE => Dt.
  rewrite lim_einf_shift//; last by rewrite fin_numM// fing.
  rewrite is_cvg_lim_einfE//; last first.
    by apply: is_cvgeN; apply/cvg_ex; eexists; exact: cvg_g_.
  rewrite [X in _ + X](_ : _ = 0) ?adde0//; apply/cvg_lim => //.
  by rewrite -(oppe0); apply: cvgeN; exact: cvg_g_.
have i2g : \int[mu]_(x in D) (2%:E * g x)  < +oo.
  rewrite integralM// lte_mul_pinfty// ?lee_fin//; case: ig => _.
  apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => t Dt; rewrite gee0_abs// g0//; rewrite inE in Dt.
have ? : \int[mu]_(x in D) (2%:E * g x)  \is a fin_num.
  by rewrite ge0_fin_numE// integral_ge0// => ? ?; rewrite mule_ge0 ?lee_fin ?g0.
rewrite [X in _ <= X -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x)  + -
    lim_esup (fun n => \int[mu]_(x in D) g_ n x)); last first.
  rewrite (_ : (fun _ => _) = (fun n => \int[mu]_(x in D) (2%:E * g x)  +
      \int[mu]_(x in D) - g_ n x)); last first.
    rewrite funeqE => n; rewrite integralB//.
    - by rewrite -integral_ge0N// => x Dx//; rewrite /g_.
    - exact: integrablerM.
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
  rewrite lim_einf_shift // -lim_einfN; congr (_ + lim_einf _).
  by rewrite funeqE => n /=; rewrite -integral_ge0N// => x Dx; rewrite /g_.
rewrite addeC -lee_subl_addr// subee// lee_oppr oppe0 => lim_ge0.
by apply/lim_esup_le_cvg => // n; rewrite integral_ge0// => x _; rewrite /g_.
Qed.

Local Lemma dominated_cvg :
  (fun n => \int[mu]_(x in D) f_ n x) --> \int[mu]_(x in D) f x.
Proof.
have h n : `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x |
    <= \int[mu]_(x in D) g_ n x.
  rewrite -(integralB _ _ dominated_integrable)//; last first.
    by apply: le_integrable ig => // x Dx /=; rewrite (gee0_abs (g0 Dx)) absfg.
  by apply: le_abse_integral => //; exact: emeasurable_funB.
suff: (fun n => `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x |) --> 0.
   move/cvg_abse0P/cvge_sub0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   case: dominated_integrable => ?; apply: le_lt_trans.
   by apply: (le_trans _ (@le_abse_integral _ _ _ mu D f mD _)).
apply: (@squeeze_cvge _ _ _ _ (cst 0) _ (fun n => \int[mu]_(x in D) g_ n x)).
- by apply: nearW => n; rewrite abse_ge0//=; exact: h.
- exact: cvg_cst.
- exact: dominated_cvg0.
Qed.

End dominated_convergence_lemma.
Arguments dominated_integrable {d T R mu D} _ f_ f g.

Section dominated_convergence_theorem.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f_ : (T -> \bar R)^nat) (f : T -> \bar R) (g : T -> \bar R).
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Hypothesis mf : measurable_fun D f.
Hypothesis f_f : {ae mu, forall x, D x -> f_ ^~ x --> f x}.
Hypothesis ig : mu.-integrable D g.
Hypothesis f_g : {ae mu, forall x n, D x -> `|f_ n x| <= g x}.

Let g_ n x := `|f_ n x - f x|.

Theorem dominated_convergence : [/\ mu.-integrable D f,
  [sequence \int[mu]_(x in D) (g_ n x)]_n --> 0 &
  [sequence \int[mu]_(x in D) (f_ n x)]_n --> \int[mu]_(x in D) (f x) ].
Proof.
have [N1 [mN1 N10 subN1]] := f_f.
have [N2 [mN2 N20 subN2]] := f_g.
have [N3 [mN3 N30 subN3]] := integrable_ae mD ig.
pose N := N1 `|` N2 `|` N3.
have mN : measurable N by apply: measurableU => //; exact: measurableU.
have N0 : mu N = 0.
  by rewrite null_set_setU// ?null_set_setU//; exact: measurableU.
pose f' := f \_ (D `\` N); pose g' := g \_ (D `\` N).
pose f_' := fun n => f_ n \_ (D `\` N).
have f_f' x : D x -> f_' ^~ x --> f' x.
  move=> Dx; rewrite /f_' /f' /restrict in_setD mem_set//=.
  have [/= xN|/= xN] := boolP (x \in N); first exact: cvg_cst.
  apply: contraPP (xN) => h; apply/negP; rewrite negbK inE; left; left.
  by apply: subN1 => /= /(_ Dx); exact: contra_not h.
have f_g' n x : D x -> `|f_' n x| <= g' x.
  move=> Dx; rewrite /f_' /g' /restrict in_setD mem_set//=.
  have [/=|/= xN] := boolP (x \in N); first by rewrite normr0.
  apply: contrapT => fg; move: xN; apply/negP; rewrite negbK inE; left; right.
  by apply: subN2 => /= /(_ n Dx).
have mu_ n : measurable_fun D (f_' n).
  apply/(measurable_restrict (f_ n) (measurableD mD mN) _ _).1 => //.
  by apply: measurable_funS (mf_ _) => // x [].
have ig' : mu.-integrable D g'.
  apply: (integrableS measurableT) => //.
  apply/(integrable_mkcond g (measurableD mD mN)).1.
  by apply: integrableS ig => //; exact: measurableD.
have finv x : D x -> g' x \is a fin_num.
  move=> Dx; rewrite /g' /restrict in_setD// mem_set//=.
  have [//|xN /=] := boolP (x \in N).
  apply: contrapT => fing; move: xN; apply/negP; rewrite negbK inE; right.
  by apply: subN3 => /= /(_ Dx).
split.
- have if' : mu.-integrable D f' by exact: (dominated_integrable _ f_' _ g').
  split => //.
  move: if' => [?]; apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/ae_eq_integral => //;
    [exact: measurable_fun_comp|exact: measurable_fun_comp|].
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x Nx Dx.
  by rewrite /f' /restrict mem_set.
- have := @dominated_cvg0 _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //.
  apply/funext => n; apply: ae_eq_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_funB => //.
    apply/(measurable_restrict _ (measurableD _ _) _ _).1 => //.
    by apply: (measurable_funS mD) => // x [].
  + by rewrite /g_; apply: measurable_fun_comp => //; exact: emeasurable_funB.
  + exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /f' /restrict mem_set.
- have := @dominated_cvg _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X --> _); rewrite [X in X --> _ -> _](_ : _ = X) //; last first.
    apply/funext => n; apply ae_eq_integral => //.
    exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /restrict mem_set.
  set Y := (X in _ -> _ --> X); rewrite [X in _ --> X -> _](_ : _ = Y) //.
  apply: ae_eq_integral => //.
    apply/(measurable_restrict _ (measurableD _ _) _ _).1 => //.
    by apply: (measurable_funS mD) => // x [].
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
  by rewrite /f' /restrict mem_set.
Qed.

End dominated_convergence_theorem.

(******************************************************************************)
(* * product measure                                                          *)
(******************************************************************************)

Section measurable_section.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2).
Implicit Types (A : set (T1 * T2)).

Variable R : realType.

Lemma measurable_xsection A x : measurable A -> measurable (xsection A x).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o indic_nnsfun R mA.
have mf : measurable_fun setT f by exact/EFin_measurable_fun/measurable_funP.
have _ : (fun y => (y \in xsection A x)%:R%:E) = f \o (fun y => (x, y)).
  by apply/funext => y/=; rewrite mem_xsection.
have -> : xsection A x = (fun y => f (x, y)) @^-1` [set 1%E].
  apply/funext => y/=; rewrite -(in_setE (xsection A x)) mem_xsection.
  rewrite /f/= mindicE//; apply/propext; split=> [->//|[]].
  by case: (_ \in _)=> // /esym/eqP; rewrite oner_eq0.
by rewrite -(setTI (_ @^-1` _)); exact: measurable_fun_prod1.
Qed.

Lemma measurable_ysection A y : measurable A -> measurable (ysection A y).
Proof.
move=> mA.
pose f : T1 * T2 -> \bar R := EFin \o indic_nnsfun R mA.
have mf : measurable_fun setT f by apply/EFin_measurable_fun/measurable_funP.
have _ : (fun x => (x \in ysection A y)%:R%:E) = f \o (fun x => (x, y)).
  by apply/funext => x/=; rewrite mem_ysection.
have -> : ysection A y = (fun x => f (x, y)) @^-1` [set 1%E].
  apply/funext => x/=; rewrite -(in_setE (ysection A y)) mem_ysection.
  rewrite /f/= mindicE//; apply/propext; split=> [->//|[]].
  by case: (_ \in _)=> // /esym/eqP; rewrite oner_eq0.
by rewrite -(setTI (_ @^-1` _)); exact: measurable_fun_prod2.
Qed.

End measurable_section.

Section ndseq_closed_B.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (pt2 : T2) (m2 : {measure set T2 -> \bar R}).
Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma xsection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have phiF x : (fun i => phi (F i) x) --> phi (\bigcup_i F i) x.
  rewrite /phi /= xsection_bigcup; apply: nondecreasing_cvg_mu.
  - by move=> n; apply: measurable_xsection; case: (BF n).
  - by apply: bigcupT_measurable => i; apply: measurable_xsection; case: (BF i).
  - by move=> m n mn; exact/subsetPset/le_xsection/subsetPset/ndF.
apply: (emeasurable_fun_cvg (phi \o F)) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: phiF.
Qed.
End xsection.

Section ysection.
Variables (m1 : {measure set T1 -> \bar R}).
Let psi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma ysection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have psiF x : (fun i => psi (F i) x) --> psi (\bigcup_i F i) x.
  rewrite /psi /= ysection_bigcup; apply: nondecreasing_cvg_mu.
  - by move=> n; apply: measurable_ysection; case: (BF n).
  - by apply: bigcupT_measurable => i; apply: measurable_ysection; case: (BF i).
  - by move=> m n mn; exact/subsetPset/le_ysection/subsetPset/ndF.
apply: (emeasurable_fun_cvg (psi \o F)) => //.
- by move=> i; have [] := BF i.
- by move=> x _; exact: psiF.
Qed.
End ysection.

End ndseq_closed_B.

Section measurable_prod_subset.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variable (m2 : {measure set T2 -> \bar R}) (D : set T2) (mD : measurable D).
Let m2D := mrestr m2 mD.
HB.instance Definition _ := Measure.on m2D.
Let phi A := m2D \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_prod_subset_xsection
    (m2D_bounded : exists M, forall X, measurable X -> (m2D X < M%:E)%E) :
  measurable `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in measurable & A2 in measurable].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setMTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : phi (X1 `*` X2) = (fun x => m2D X2 * (\1_X1 x)%:E)%E.
    rewrite funeqE => x; rewrite indicE /phi /m2/= /mrestr.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionM.
    by rewrite mule0 notin_xsectionM// set0I measure0.
  exact/measurable_funeM/EFin_measurable_fun/measurable_fun_indic.
suff monoB : monotone_class setT B by exact: monotone_class_subset.
split => //; [exact: CB| |exact: xsection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
have -> : phi (X `\` Y) = (fun x => phi X x - phi Y x)%E.
  rewrite funeqE => x; rewrite /phi/= xsectionD// /m2D measureD.
  - by rewrite setIidr//; exact: le_xsection.
  - exact: measurable_xsection.
  - exact: measurable_xsection.
  - move: m2D_bounded => [M m2M].
    rewrite (lt_le_trans (m2M (xsection X x) _))// ?leey//.
    exact: measurable_xsection.
exact: emeasurable_funB.
Qed.

End xsection.

Section ysection.
Variable (m1 : {measure set T1 -> \bar R}) (D : set T1) (mD : measurable D).
Let m1D := mrestr m1 mD.
HB.instance Definition _ := Measure.on m1D.
Let psi A := m1D \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma measurable_prod_subset_ysection
    (m1_bounded : exists M, forall X, measurable X -> (m1D X < M%:E)%E) :
  measurable `<=` B.
Proof.
rewrite measurable_prod_measurableType.
set C := [set A1 `*` A2 | A1 in measurable & A2 in measurable].
have CI : setI_closed C.
  move=> X Y [X1 mX1 [X2 mX2 <-{X}]] [Y1 mY1 [Y2 mY2 <-{Y}]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setMTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableM.
  have -> : psi (X1 `*` X2) = (fun x => m1D X1 * (\1_X2 x)%:E)%E.
    rewrite funeqE => y; rewrite indicE /psi /m1/= /mrestr.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionM.
    by rewrite mule0 notin_ysectionM// set0I measure0.
  exact/measurable_funeM/EFin_measurable_fun/measurable_fun_indic.
suff monoB : monotone_class setT B by exact: monotone_class_subset.
split => //; [exact: CB| |exact: ysection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
have -> : psi (X `\` Y) = (fun x => psi X x - psi Y x)%E.
  rewrite funeqE => y; rewrite /psi/= ysectionD// /m1D measureD.
  - by rewrite setIidr//; exact: le_ysection.
  - exact: measurable_ysection.
  - exact: measurable_ysection.
  - move: m1_bounded => [M m1M].
    rewrite (lt_le_trans (m1M (ysection X y) _))// ?leey//.
    exact: measurable_ysection.
exact: emeasurable_funB.
Qed.

End ysection.

End measurable_prod_subset.

Section measurable_fun_xsection.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m2 : {measure set T2 -> \bar R}).
Hypothesis sf_m2 : sigma_finite setT m2.
Implicit Types A : set (T1 * T2).

Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection A :
  A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A; rewrite inE => /[apply] -[].
move/sigma_finiteP : sf_m2 => [F F_T [F_nd F_oo]] X mX.
have -> : X = \bigcup_n (X `&` (setT `*` F n)).
  by rewrite -setI_bigcupr -setM_bigcupr -F_T setMTT setIT.
apply: xsection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSM => //.
  exact/subsetPset/F_nd.
move=> n; rewrite -/B; have [? ?] := F_oo n.
pose m2Fn := [the measure _ _ of mrestr m2 (F_oo n).1].
have m2Fn_bounded : exists M, forall X, measurable X -> (m2Fn X < M%:E)%E.
  exists (fine (m2Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0//= /mrestr/= setIid.
  rewrite /= /mrestr/= setIid; apply: le_measure => //; rewrite inE//.
  exact: measurableI.
pose phi' A := m2Fn \o xsection A.
pose B' := [set A | measurable A /\ measurable_fun setT (phi' A)].
have subset_B' : measurable `<=` B' by exact: measurable_prod_subset_xsection.
split=> [|Y mY]; first by apply: measurableI => //; exact: measurableM.
have [_ /(_ Y mY)] := subset_B' X mX.
have ->// : phi' X = (fun x => m2 [set y | (x, y) \in X `&` setT `*` F n]).
rewrite funeqE => x /=; congr (m2 _); rewrite predeqE => y; split => [[]|].
  by rewrite /xsection /= inE => Xxy Fny; rewrite inE.
by rewrite /xsection /= !inE => -[] Xxy /= [_].
Qed.

End measurable_fun_xsection.

Section measurable_fun_ysection.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}).
Hypothesis sf_m1 : sigma_finite setT m1.
Implicit Types A : set (T1 * T2).

Let phi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection A : A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A; rewrite inE => /[apply] -[].
move : sf_m1 => /sigma_finiteP[F F_T [F_nd F_oo]] X mX.
have -> : X = \bigcup_n (X `&` (F n `*` setT)).
  by rewrite -setI_bigcupr -setM_bigcupl -F_T setMTT setIT.
apply: ysection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSM => //.
  exact/subsetPset/F_nd.
move=> n; have [? ?] := F_oo n; rewrite -/B.
pose m1Fn := [the measure _ _ of mrestr m1 (F_oo n).1].
have m1Fn_bounded : exists M, forall X, measurable X -> (m1Fn X < M%:E)%E.
  exists (fine (m1Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0// /m1Fn/= /mrestr setIid.
  rewrite /m1Fn/= /mrestr setIid; apply: le_measure => //; rewrite inE//=.
  exact: measurableI.
pose psi' A := m1Fn \o ysection A.
pose B' := [set A | measurable A /\ measurable_fun setT (psi' A)].
have subset_B' : measurable `<=` B'.
  exact: measurable_prod_subset_ysection.
split=> [|Y mY]; first by apply: measurableI => //; exact: measurableM.
have [_ /(_ Y mY)] := subset_B' X mX.
have ->// : psi' X = (fun y => m1 [set x | (x, y) \in X `&` F n `*` setT]).
rewrite funeqE => y /=; congr (m1 _); rewrite predeqE => x; split => [[]|].
  by rewrite /ysection /= inE => Xxy Fny; rewrite inE.
by rewrite /ysection /= !inE => -[] Xxy/= [].
Qed.

End measurable_fun_ysection.

Definition product_measure1 d1 d2
    (T1 : measurableType d1) (T2 : measurableType d2) (R : realType)
    (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R})
    (sm2 : sigma_finite setT m2) :=
  (fun A => \int[m1]_x (m2 \o xsection A) x)%E.

Section product_measure1.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm2 : sigma_finite setT m2.
Implicit Types A : set (T1 * T2).

Notation pm1 := (product_measure1 m1 sm2).

Let pm10 : pm1 set0 = 0.
Proof.
rewrite /pm1 (eq_integral (cst 0)) ?integral0//= => x _.
by rewrite xsection0 measure0.
Qed.

Let pm1_ge0 A : 0 <= pm1 A.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_xsection.
Qed.

Let pm1_sigma_additive : semi_sigma_additive pm1.
Proof.
move=> F mF tF mUF; have -> : pm1 (\bigcup_n F n) = \sum_(n <oo) pm1 (F n).
  transitivity (\int[m1]_x \sum_(n <oo) m2 (xsection (F n) x)).
    apply: eq_integral => x _; apply/esym/cvg_lim => //=.
    rewrite xsection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_xsection tF)).
    by move=> ?; exact: measurable_xsection.
  by rewrite integral_nneseries // => n; apply: measurable_fun_xsection => // /[!inE].
apply/cvg_closeP; split; last by rewrite closeE.
by apply: is_cvg_nneseries => *; exact: integral_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ pm1
  pm10 pm1_ge0 pm1_sigma_additive.

End product_measure1.

Section product_measure1E.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm2 : sigma_finite setT m2.
Implicit Types A : set (T1 * T2).

Lemma product_measure1E (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 ->
  product_measure1 m1 sm2 (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
move=> mA1 mA2 /=; rewrite /product_measure1 /=.
rewrite (_ : (fun _ => _) = fun x => m2 A2 * (\1_A1 x)%:E); last first.
  rewrite funeqE => x; rewrite indicE.
  by have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionM// mule1|rewrite mule0 notin_xsectionM].
rewrite ge0_integralM//.
- by rewrite muleC integral_indic// setIT.
- by apply: measurable_fun_comp => //; exact/measurable_fun_indic.
- by move=> x _; rewrite lee_fin.
Qed.

End product_measure1E.

Section product_measure_unique.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sm1 : sigma_finite setT m1) (sm2 : sigma_finite setT m2).

Lemma product_measure_unique
    (m' : {measure set [the semiRingOfSetsType _ of (T1 * T2)%type] -> \bar R}) :
    (forall A1 A2, measurable A1 -> measurable A2 ->
      m' (A1 `*` A2) = m1 A1 * m2 A2) ->
  forall X : set (T1 * T2), measurable X -> product_measure1 m1 sm2 X = m' X.
Proof.
move=> m'E; pose m := product_measure1 m1 sm2.
move/sigma_finiteP : sm1 => [F1 F1_T [F1_nd F1_oo]].
move/sigma_finiteP : sm2 => [F2 F2_T [F2_nd F2_oo]].
have UF12T : \bigcup_k (F1 k `*` F2 k) = setT.
  rewrite -setMTT F1_T F2_T predeqE => -[x y]; split.
    by move=> [n _ []/= ? ?]; split; exists n.
  move=> [/= [n _ F1nx] [k _ F2ky]]; exists (maxn n k) => //; split.
  - by move: x F1nx; apply/subsetPset/F1_nd; rewrite leq_maxl.
  - by move: y F2ky; apply/subsetPset/F2_nd; rewrite leq_maxr.
have mF1F2 n : measurable (F1 n `*` F2 n) /\ m (F1 n `*` F2 n) < +oo.
  have [? ?] := F1_oo n; have [? ?] := F2_oo n.
  split; first exact: measurableM.
  by rewrite /m product_measure1E // lte_mul_pinfty// ge0_fin_numE.
have sm : sigma_finite setT m by exists (fun n => F1 n `*` F2 n).
pose C : set (set (T1 * T2)) := [set C |
  exists A1, measurable A1 /\ exists A2, measurable A2 /\ C = A1 `*` A2].
have CI : setI_closed C.
  move=> /= _ _ [X1 [mX1 [X2 [mX2 ->]]]] [Y1 [mY1 [Y2 [mY2 ->]]]].
  rewrite -setMI; exists (X1 `&` Y1); split; first exact: measurableI.
  by exists (X2 `&` Y2); split => //; exact: measurableI.
move=> X mX; apply: (measure_unique C (fun n => F1 n `*` F2 n)) => //.
- rewrite measurable_prod_measurableType //; congr (<<s _ >>).
  rewrite predeqE; split => [[A1 mA1 [A2 mA2 <-]]|[A1 [mA1 [A2 [mA2 ->]]]]].
    by exists A1; split => //; exists A2; split.
  by exists A1 => //; exists A2.
- move=> n; rewrite /C /=; exists (F1 n); split; first by have [] := F1_oo n.
  by exists (F2 n); split => //; have [] := F2_oo n.
- by move=> A [A1 [mA1 [A2 [mA2 ->]]]]; rewrite m'E//= product_measure1E.
- move=> k; have [? ?] := F1_oo k; have [? ?] := F2_oo k.
  by rewrite /= product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

End product_measure_unique.

Definition product_measure2 d1 d2
    (T1 : measurableType d1) (T2 : measurableType d2) (R : realType)
    (m1 : {measure set T1 -> \bar R}) (sm1 : sigma_finite setT m1)
    (m2 : {measure set T2 -> \bar R}) :=
  (fun A => \int[m2]_x (m1 \o ysection A) x)%E.

Section product_measure2.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm1 : sigma_finite setT m1.
Implicit Types A : set (T1 * T2).

Notation pm2 := (product_measure2 sm1 m2).

Let pm20 : pm2 set0 = 0.
Proof.
rewrite /pm2 (eq_integral (cst 0)) ?integral0//= => y _.
by rewrite ysection0 measure0.
Qed.

Let pm2_ge0 A : 0 <= pm2 A.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_ysection.
Qed.

Let pm2_sigma_additive : semi_sigma_additive pm2.
Proof.
move=> F mF tF mUF.
have -> : pm2 (\bigcup_n F n) = \sum_(n <oo) pm2 (F n).
  transitivity (\int[m2]_y \sum_(n <oo) m1 (ysection (F n) y)).
    apply: eq_integral => y _; apply/esym/cvg_lim => //=.
    rewrite ysection_bigcup.
    apply: (measure_sigma_additive _ (trivIset_ysection tF)).
    by move=> ?; apply: measurable_ysection.
  rewrite integral_nneseries // => n; apply: measurable_fun_ysection => //.
  by rewrite inE.
apply/cvg_closeP; split; last by rewrite closeE.
by apply: is_cvg_nneseries => *; exact: integral_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ pm2
  pm20 pm2_ge0 pm2_sigma_additive.

End product_measure2.

Section product_measure2E.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypothesis sm1 : sigma_finite setT m1.

Lemma product_measure2E (A1 : set T1) (A2 : set T2)
    (mA1 : measurable A1) (mA2 : measurable A2) :
  product_measure2 sm1 m2 (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
have mA1A2 : measurable (A1 `*` A2) by apply: measurableM.
transitivity (\int[m2]_y (m1 \o ysection (A1 `*` A2)) y) => //.
rewrite (_ : _ \o _ = fun y => m1 A1 * (\1_A2 y)%:E).
  rewrite ge0_integralM//; last 2 first.
    - by apply: measurable_fun_comp => //; exact/measurable_fun_indic.
    - by move=> y _; rewrite lee_fin.
  by rewrite integral_indic ?setIT ?mul1e.
rewrite funeqE => y; rewrite indicE.
have [yA2|yA2] := boolP (y \in A2); first by rewrite mule1 /= in_ysectionM.
by rewrite mule0 /= notin_ysectionM// measure0.
Qed.

End product_measure2E.

Section fubini_functions.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Variable f : T1 * T2 -> \bar R.

Definition fubini_F x := \int[m2]_y f (x, y).
Definition fubini_G y := \int[m1]_x f (x, y).

End fubini_functions.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sm1 : sigma_finite setT m1) (sm2 : sigma_finite setT m2).

Let m := product_measure1 m1 sm2.
Let m' := product_measure2 sm1 m2.
HB.instance Definition _ := Measure.on m.
HB.instance Definition _ := Measure.on m'.

Section indic_fubini_tonelli.
Variables (A : set (T1 * T2)) (mA : measurable A).
Implicit Types A : set (T1 * T2).
Let f : (T1 * T2) -> R := \1_A.

Let F := fubini_F m2 (EFin \o f).
Let G := fubini_G m1 (EFin \o f).

Lemma indic_fubini_tonelli_F_ge0 x : 0 <= F x.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma indic_fubini_tonelli_G_ge0 x : 0 <= G x.
Proof. by apply: integral_ge0 => // y _; rewrite lee_fin. Qed.

Lemma indic_fubini_tonelli_FE : F = m2 \o xsection A.
Proof.
rewrite funeqE => x; rewrite /= -(setTI (xsection _ _)).
rewrite -integral_indic//; last exact: measurable_xsection.
rewrite /F /fubini_F -(setTI (xsection _ _)).
rewrite integral_setI_indic; [|exact: measurable_xsection|by []].
by apply: eq_integral => y _ /=; rewrite indicT mul1e /f !indicE mem_xsection.
Qed.

Lemma indic_fubini_tonelli_GE : G = m1 \o ysection A.
Proof.
rewrite funeqE => y; rewrite /= -(setTI (ysection _ _)).
rewrite -integral_indic//; last exact: measurable_ysection.
rewrite /F /fubini_F -(setTI (ysection _ _)).
rewrite integral_setI_indic; [|exact: measurable_ysection|by []].
by apply: eq_integral => x _ /=; rewrite indicT mul1e /f 2!indicE mem_ysection.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
rewrite indic_fubini_tonelli_FE//; apply: measurable_fun_xsection => //.
by rewrite inE.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
rewrite indic_fubini_tonelli_GE//; apply: measurable_fun_ysection => //.
by rewrite inE.
Qed.

Let mE : m A = \int[m1]_x F x.
Proof. by rewrite /m /product_measure1 /= indic_fubini_tonelli_FE. Qed.

Lemma indic_fubini_tonelli1 : \int[m]_z (f z)%:E = \int[m1]_x F x.
Proof. by rewrite /f integral_indic// setIT indic_fubini_tonelli_FE. Qed.

Lemma indic_fubini_tonelli2 : \int[m']_z (f z)%:E = \int[m2]_y G y.
 by rewrite /f integral_indic// setIT indic_fubini_tonelli_GE. Qed.

Lemma indic_fubini_tonelli : \int[m1]_x F x = \int[m2]_y G y.
Proof.
rewrite -indic_fubini_tonelli1// -indic_fubini_tonelli2//.
rewrite integral_indic // integral_indic // setIT/=.
by apply: product_measure_unique => //= ? ? ? ?; rewrite /m' product_measure2E.
Qed.

End indic_fubini_tonelli.

Section sfun_fubini_tonelli.
Variable f : {nnsfun [the measurableType _ of T1 * T2 : Type] >-> R}.

Let F := fubini_F m2 (EFin \o f).
Let G := fubini_G m1 (EFin \o f).

Lemma sfun_fubini_tonelli_FE : F = fun x =>
  \sum_(k \in range f) k%:E * m2 (xsection (f @^-1` [set k]) x).
Proof.
rewrite funeqE => x; rewrite /F /fubini_F [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/EFin_measurable_fun => //; apply: measurable_funrM => //.
    exact/measurable_fun_prod1/measurable_fun_indic.
  - by move=> r y _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralM//; last by rewrite lee_fin.
- by rewrite -/((m2 \o xsection _) x) -indic_fubini_tonelli_FE.
- exact/EFin_measurable_fun/measurable_fun_prod1/measurable_fun_indic.
- by move=> y _; rewrite lee_fin.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
rewrite sfun_fubini_tonelli_FE//; apply: emeasurable_fun_fsum => // r.
by apply/measurable_funeM/measurable_fun_xsection => // /[!inE].
Qed.

Lemma sfun_fubini_tonelli_GE : G = fun y =>
  \sum_(k \in range f) k%:E * m1 (ysection (f @^-1` [set k]) y).
Proof.
rewrite funeqE => y; rewrite /G /fubini_G [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/EFin_measurable_fun => //; apply: measurable_funrM => //.
    exact/measurable_fun_prod2/measurable_fun_indic.
  - by move=> r x _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralM//; last by rewrite lee_fin.
- by rewrite -/((m1 \o ysection _) y) -indic_fubini_tonelli_GE.
- exact/EFin_measurable_fun/measurable_fun_prod2/measurable_fun_indic.
- by move=> x _; rewrite lee_fin.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
rewrite sfun_fubini_tonelli_GE//; apply: emeasurable_fun_fsum => // r.
by apply/measurable_funeM/measurable_fun_ysection => // /[!inE].
Qed.

Let EFinf x : (f x)%:E =
    \sum_(k \in range f) k%:E * (\1_(f @^-1` [set k]) x)%:E.
Proof. by rewrite fsumEFin //= fimfunE. Qed.

Lemma sfun_fubini_tonelli1 : \int[m]_z (f z)%:E = \int[m1]_x F x.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - move=> r.
    exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m1]_x (k%:E * (fubini_F m2 (EFin \o \1_(f @^-1` [set k])) x))).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralM//; last 3 first.
    - exact/EFin_measurable_fun/measurable_fun_indic.
    - by move=> /= x _; rewrite lee_fin.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli1// -ge0_integralM//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_F.
  - by move=> /= x _; exact: indic_fubini_tonelli_F_ge0.
rewrite -ge0_integral_fsum //; last 2 first.
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_F.
  - move=> r x _; rewrite /fubini_F.
    have [r0|r0] := leP 0%R r.
      by rewrite mule_ge0//; exact: indic_fubini_tonelli_F_ge0.
    rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => y _.
    by rewrite preimage_nnfun0//= indicE in_set0.
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_FE.
by apply: eq_fsbigr => ? _; rewrite indic_fubini_tonelli_FE.
Qed.

Lemma sfun_fubini_tonelli2 : \int[m']_z (f z)%:E = \int[m2]_y G y.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - move=> i.
    exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m2]_x (k%:E * (fubini_G m1 (EFin \o \1_(f @^-1` [set k])) x))).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralM//; last 3 first.
    - exact/EFin_measurable_fun/measurable_fun_indic.
    - by move=> /= x _; rewrite lee_fin.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli2// -ge0_integralM//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_G.
  - by move=> /= x _; exact: indic_fubini_tonelli_G_ge0.
rewrite -ge0_integral_fsum //; last 2 first.
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_G.
  - move=> r x _; rewrite /fubini_G.
    have [r0|r0] := leP 0%R r.
      by rewrite mule_ge0//; exact: indic_fubini_tonelli_G_ge0.
    rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => y _.
    by rewrite preimage_nnfun0//= indicE in_set0.
apply: eq_integral => x _; rewrite sfun_fubini_tonelli_GE.
by apply: eq_fsbigr => i _; rewrite indic_fubini_tonelli_GE.
Qed.

Lemma sfun_fubini_tonelli : \int[m]_z (f z)%:E = \int[m']_z (f z)%:E.
Proof.
under eq_integral do rewrite EFinf.
under [RHS]eq_integral do rewrite EFinf.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i.
    exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by move=> r z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f) k%:E *
    \int[m']_z ((EFin \o \1_(f @^-1` [set k])) z)).
  apply: eq_fsbigr => i; rewrite inE => -[t _ <-].
  rewrite ge0_integralM//; last 3 first.
    - exact/EFin_measurable_fun/measurable_fun_indic.
    - by move=> /= x _; rewrite lee_fin.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli1// indic_fubini_tonelli//.
  by rewrite -indic_fubini_tonelli2.
apply/esym; rewrite ge0_integral_fsum //; last 2 first.
  - move=> i.
    exact/EFin_measurable_fun/measurable_funrM/measurable_fun_indic.
  - by move=> r z _; exact: nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[x _ <-].
rewrite ge0_integralM//; last by rewrite lee_fin.
- exact/EFin_measurable_fun/measurable_fun_indic.
- by move=> /= y _; rewrite lee_fin.
Qed.

End sfun_fubini_tonelli.

Section fubini_tonelli.
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.
Hypothesis f0 : forall x, 0 <= f x.
Let T := [the measurableType _ of T1 * T2 : Type].

Let F := fubini_F m2 f.
Let G := fubini_G m1 f.

Let F_ (g : {nnsfun T >-> R}^nat) n x := \int[m2]_y (g n (x, y))%:E.
Let G_ (g : {nnsfun T >-> R}^nat) n y := \int[m1]_x (g n (x, y))%:E.

Lemma measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
apply: (emeasurable_fun_cvg (F_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> x _.
  rewrite /F_ /F /fubini_F [in X in _ --> X](_ : (fun _ => _) =
      fun y => lim (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => y; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/EFin_measurable_fun => //; exact/measurable_fun_prod1.
  - by move=> n y _; rewrite lee_fin//; exact: fun_ge0.
  - by move=> y _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
apply: (emeasurable_fun_cvg (G_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- move=> y _; rewrite /G_ /G /fubini_G [in X in _ --> X](_ : (fun _ => _) =
      fun x => lim (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => x; apply/esym/cvg_lim => //; exact: g_f.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/EFin_measurable_fun => //; exact/measurable_fun_prod2.
  - by move=> n x _; rewrite lee_fin; exact: fun_ge0.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/g_nd.
Qed.

Lemma fubini_tonelli1 : \int[m]_z f z = \int[m1]_x F x.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
have F_F x : F x = lim (F_ g ^~ x).
  rewrite /F /fubini_F.
  rewrite [RHS](_ : _ = lim (fun n => \int[m2]_y (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> n /= y _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int[m]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ =
    lim (fun n => \int[m1]_x (\int[m2]_y (EFin \o g n) (x, y)))).
  by congr (lim _); rewrite funeqE => n; rewrite sfun_fubini_tonelli1.
rewrite [RHS](_ : _ = lim (fun n => \int[m1]_x F_ g n x))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> n x _; apply: integral_ge0 => // y _ /=; rewrite lee_fin.
  exact: fun_ge0.
- move=> x /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> y _; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod1.
  + by move=> *; rewrite lee_fin; exact: fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod1.
  + by move=> y _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

Lemma fubini_tonelli2 : \int[m]_z f z = \int[m2]_y G y.
Proof.
have [g [g_nd /= g_f]] := approximation measurableT mf (fun x _ => f0 x).
have G_G y : G y = lim (G_ g ^~ y).
  rewrite /G /fubini_G.
  rewrite [RHS](_ : _ = lim (fun n => \int[m1]_x (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod2.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> x /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [RHS](_ : _ = lim (fun n => \int[m]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/EFin_measurable_fun.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b; rewrite lee_fin => /g_nd/lefP; exact.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: g_f.
rewrite [LHS](_ : _ = lim
    (fun n => \int[m2]_y (\int[m1]_x (EFin \o g n) (x, y)))).
  congr (lim _); rewrite funeqE => n.
  by rewrite sfun_fubini_tonelli sfun_fubini_tonelli2.
rewrite [RHS](_ : _ = lim (fun n => \int[m2]_y G_ g n y))//.
rewrite -monotone_convergence //; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- by move=> n y _; apply: integral_ge0 => // x _ /=; rewrite lee_fin fun_ge0.
- move=> y /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod2.
  + by move=> *; rewrite lee_fin fun_ge0.
  + exact/EFin_measurable_fun/measurable_fun_prod2.
  + by move=> x _; rewrite lee_fin; move/g_nd : ab => /lefP; exact.
Qed.

End fubini_tonelli.

End fubini_tonelli.
Arguments fubini_tonelli1 {d1 d2 T1 T2 R m1 m2} sm2 f.
Arguments fubini_tonelli2 {d1 d2 T1 T2 R m1 m2} sm1 sm2 f.
Arguments measurable_fun_fubini_tonelli_F {d1 d2 T1 T2 R m2} sm2 f.
Arguments measurable_fun_fubini_tonelli_G {d1 d2 T1 T2 R m1} sm1 f.

Section fubini.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sm1 : sigma_finite setT m1) (sm2 : sigma_finite setT m2).
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.

Let m := product_measure1 m1 sm2.
HB.instance Definition _ := Measure.on m.

Lemma fubini1a :
  m.-integrable setT f <-> \int[m1]_x \int[m2]_y `|f (x, y)| < +oo.
Proof.
split=> [[_]|] ioo.
- by rewrite -(fubini_tonelli1 _ (abse \o f))//=; exact: measurable_fun_comp.
- by split=> //; rewrite fubini_tonelli1//; exact: measurable_fun_comp.
Qed.

Lemma fubini1b :
  m.-integrable setT f <-> \int[m2]_y \int[m1]_x `|f (x, y)| < +oo.
Proof.
split=> [[_]|] ioo.
- by rewrite -(fubini_tonelli2 _ _ (abse \o f))//=; exact: measurable_fun_comp.
- by split=> //; rewrite fubini_tonelli2//; exact: measurable_fun_comp.
Qed.

Let measurable_fun1 : measurable_fun setT (fun x => \int[m2]_y `|f (x, y)|).
Proof.
apply: (measurable_fun_fubini_tonelli_F _ (abse \o f)) => //=.
exact: measurable_fun_comp.
Qed.

Let measurable_fun2 : measurable_fun setT (fun y => \int[m1]_x `|f (x, y)|).
Proof.
apply: (measurable_fun_fubini_tonelli_G _ (abse \o f)) => //=.
exact: measurable_fun_comp.
Qed.

Hypothesis imf : m.-integrable setT f.

Lemma ae_integrable1 :
  {ae m1, forall x, m2.-integrable setT (fun y => f (x, y))}.
Proof.
have : m1.-integrable setT (fun x => \int[m2]_y `|f (x, y)|).
  split => //; rewrite (le_lt_trans _  (fubini1a.1 imf))// ge0_le_integral //.
  - exact: measurable_fun_comp.
  - by move=> *; exact: integral_ge0.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT) [N [mN N0 subN]]; exists N; split => //.
apply/(subset_trans _ subN)/subsetC => x /= /(_ Logic.I) im2f.
by split; [exact/measurable_fun_prod1|by move/fin_numPlt : im2f => /andP[]].
Qed.

Lemma ae_integrable2 :
  {ae m2, forall y, m1.-integrable setT (fun x => f (x, y))}.
Proof.
have : m2.-integrable setT (fun y => \int[m1]_x `|f (x, y)|).
  split => //; rewrite (le_lt_trans _ (fubini1b.1 imf))// ge0_le_integral //.
  - exact: measurable_fun_comp.
  - by move=> *; exact: integral_ge0.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT) [N [mN N0 subN]]; exists N; split => //.
apply/(subset_trans _ subN)/subsetC => x /= /(_ Logic.I) im1f.
by split; [exact/measurable_fun_prod2|move/fin_numPlt : im1f => /andP[]].
Qed.

Let F := fubini_F m2 f.

Let Fplus x := \int[m2]_y f^\+ (x, y).
Let Fminus x := \int[m2]_y f^\- (x, y).

Let FE : F = Fplus \- Fminus. Proof. apply/funext=> x; exact: integralE. Qed.

Let measurable_Fplus : measurable_fun setT Fplus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: emeasurable_fun_funepos.
Qed.

Let measurable_Fminus : measurable_fun setT Fminus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: emeasurable_fun_funeneg.
Qed.

Lemma measurable_fubini_F : measurable_fun setT F.
Proof.
rewrite FE.
by apply: emeasurable_funB; [exact: measurable_Fplus|exact: measurable_Fminus].
Qed.

Let integrable_Fplus : m1.-integrable setT Fplus.
Proof.
split=> //; apply: le_lt_trans (fubini1a.1 imf); apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> x _; exact: integral_ge0.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funepos => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funepos => //; exact: measurable_fun_prod1.
  - by apply: measurable_fun_comp => //; exact/measurable_fun_prod1.
  - by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Fminus : m1.-integrable setT Fminus.
Proof.
split=> //; apply: le_lt_trans (fubini1a.1 imf); apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funeneg => //.
    exact: measurable_fun_prod1.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //; apply: emeasurable_fun_funeneg => //.
    exact: measurable_fun_prod1.
  + by apply: measurable_fun_comp => //; exact: measurable_fun_prod1.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma integrable_fubini_F : m1.-integrable setT F.
Proof. by rewrite FE; exact: integrableB. Qed.

Let G := fubini_G m1 f.

Let Gplus y := \int[m1]_x f^\+ (x, y).
Let Gminus y := \int[m1]_x f^\- (x, y).

Let GE : G = Gplus \- Gminus. Proof. apply/funext=> x; exact: integralE. Qed.

Let measurable_Gplus : measurable_fun setT Gplus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: emeasurable_fun_funepos.
Qed.

Let measurable_Gminus : measurable_fun setT Gminus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: emeasurable_fun_funeneg.
Qed.

Lemma measurable_fubini_G : measurable_fun setT G.
Proof. by rewrite GE; exact: emeasurable_funB. Qed.

Let integrable_Gplus : m2.-integrable setT Gplus.
Proof.
split=> //; apply: le_lt_trans (fubini1b.1 imf); apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funepos => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  - apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funepos => //; exact: measurable_fun_prod2.
  - by apply: measurable_fun_comp => //; exact: measurable_fun_prod2.
  - by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addl.
Qed.

Let integrable_Gminus : m2.-integrable setT Gminus.
Proof.
split=> //; apply: le_lt_trans (fubini1b.1 imf); apply: ge0_le_integral => //.
- exact: measurable_fun_comp.
- by move=> *; exact: integral_ge0.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: emeasurable_fun_funeneg => //.
    exact: measurable_fun_prod2.
  apply: ge0_le_integral => //.
  + apply: measurable_fun_comp => //.
    by apply: emeasurable_fun_funeneg => //; exact: measurable_fun_prod2.
  + by apply: measurable_fun_comp => //; exact: measurable_fun_prod2.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse lee_addr.
Qed.

Lemma fubini1 : \int[m1]_x F x = \int[m]_z f z.
Proof.
rewrite FE integralB// [in RHS]integralE//.
rewrite fubini_tonelli1//; last exact: emeasurable_fun_funepos.
by rewrite fubini_tonelli1//; exact: emeasurable_fun_funeneg.
Qed.

Lemma fubini2 : \int[m2]_x G x = \int[m]_z f z.
Proof.
rewrite GE integralB// [in RHS]integralE//.
rewrite fubini_tonelli2//; last exact: emeasurable_fun_funepos.
by rewrite fubini_tonelli2//; exact: emeasurable_fun_funeneg.
Qed.

Theorem Fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite fubini1 -fubini2. Qed.

End fubini.
