(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import fsbigop interval_inference ereal topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun function_spaces.

(**md**************************************************************************)
(* # Lebesgue Integral                                                        *)
(*                                                                            *)
(* This file contains a formalization of the Lebesgue integral. It starts     *)
(* with simple functions and their integral, provides basic operations        *)
(* (addition, etc.), and proves the properties of their integral (linearity,  *)
(* non-decreasingness). It then defines the integral of measurable functions, *)
(* proves the approximation theorem, the properties of their integral         *)
(* (linearity, non-decreasingness), the monotone convergence theorem, and     *)
(* Fatou's lemma. Finally, it proves the linearity properties of the          *)
(* integral, the dominated convergence theorem and Fubini's theorem, etc.     *)
(* This file is further completed by related, standard lemmas such as the     *)
(* Hardy–Littlewood maximal inequality and Lebesgue's differentiation         *)
(* theorem.                                                                   *)
(*                                                                            *)
(* Main notation:                                                             *)
(* | Coq notation          |  | Meaning                         |             *)
(* |----------------------:|--|:--------------------------------              *)
(* | \int[mu]_(x in D) f x |==| $\int_D f(x)\mathbf{d}\mu(x)$                 *)
(* | \int[mu]_x f x        |==| $\int f(x)\mathbf{d}\mu(x)$                   *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* About the local naming convention: Lemmas about the Lebesgue integral      *)
(* often appears in two flavors, depending on whether they are about non-     *)
(* negative functions or about integrable functions. Lemmas about non-        *)
(* negative functions are prefixed with ge0_, lemmas about integrable         *)
(* functions are not.                                                         *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ````                                                                       *)
(*       {mfun aT >-> rT} == type of measurable functions                     *)
(*                           aT and rT are sigmaRingType's.                   *)
(*             f \in mfun == holds for f : {mfun _ >-> _}                     *)
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
(*                           It uses the sets dyadic_approx and               *)
(*                           integer_approx.                                  *)
(*      nnsfun_approx D f == same as approx D f but as a nnsfun               *)
(*                           approximates f over D using dyadic intervals     *)
(*       Rintegral mu D f := fine (\int[mu]_(x in D) f x).                    *)
(*     mu.-integrable D f == f is measurable over D and the integral of f     *)
(*                           w.r.t. D is < +oo                                *)
(*               m1 \x m2 == product measure over T1 * T2, m1 is a measure    *)
(*                           measure over T1, and m2 is a sigma finite        *)
(*                           measure over T2                                  *)
(*              m1 \x^ m2 == product measure over T1 * T2, m2 is a measure    *)
(*                           measure over T1, and m1 is a sigma finite        *)
(*                           measure over T2                                  *)
(* locally_integrable D f == the real number-valued function f is locally     *)
(*                           integrable on D                                  *)
(*               iavg f A := "average" of the real-valued function f over     *)
(*                           the set A                                        *)
(*             HL_maximal == the Hardy–Littlewood maximal operator            *)
(*                           input: real number-valued function               *)
(*                           output: extended real number-valued function     *)
(*             davg f x r == "deviated average" of the real-valued function   *)
(*                           f over ball x r                                  *)
(*       lim_sup_davg f x := lime_sup (davg f x) 0                            *)
(*        lebesgue_pt f x == Lebesgue point at x of the real-valued           *)
(*                           function f                                       *)
(*   nicely_shrinking x E == the sequence of sets E is nicely shrinking to x  *)
(* ````                                                                       *)
(*                                                                            *)
(* About the use of simple functions:                                         *)
(* Because of a limitation of HB <= 1.8.0, we need some care to be able to    *)
(* use simple functions.                                                      *)
(* The structure SimpleFun (resp. NonNegSimpleFun) is located inside the      *)
(* module HBSimple (resp. HBNNSimple).                                        *)
(* As a consequence, we need to import HBSimple (resp. HBNNSimple) to use the *)
(* coercion from simple functions (resp. non-negative simple functions) to    *)
(* Coq functions.                                                             *)
(* Also, assume that f (e.g., cst, indic) is equipped with the structure of   *)
(* MeasurableFun. For f to be equipped with the structure of SimpleFun        *)
(* (resp. NonNegSimpleFun), one need locally to import HBSimple (resp.        *)
(* HBNNSimple) and to instantiate FiniteImage (resp. NonNegFun) locally.      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
From mathcomp Require Import mathcomp_extra.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "\int [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, mu at level 10, i, D at level 50,
  format "'[' \int [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\int [ mu ]_ i F"
  (at level 36, F at level 36, mu at level 10, i at level 0,
    right associativity, format "'[' \int [ mu ]_ i '/  '  F ']'").
Reserved Notation "mu .-integrable" (at level 2, format "mu .-integrable").
Reserved Notation "m1 '\x' m2" (at level 40, left associativity).
Reserved Notation "m1 '\x^' m2" (at level 40, left associativity).

#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable_set1] : core.

HB.mixin Record isMeasurableFun d d' (aT : sigmaRingType d) (rT : sigmaRingType d')
    (f : aT -> rT) := {
  measurable_funPT : measurable_fun [set: aT] f
}.
HB.structure Definition MeasurableFun d d' aT rT :=
  {f of @isMeasurableFun d d' aT rT f}.
Arguments measurable_funPT {d d' aT rT} s.

Reserved Notation "{ 'mfun' aT >-> T }"
  (at level 0, format "{ 'mfun'  aT  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").
Notation "{ 'mfun' aT >-> T }" := (@MeasurableFun.type _ _ aT T) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (measurable_fun [set: _] _) =>
  solve [apply: measurable_funPT] : core.

Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").

Lemma measurable_funP {d d' : measure_display}
  {aT : measurableType d} {rT : sigmaRingType d'}
  (D : set aT) (s : {mfun aT >-> rT}) : measurable_fun D s.
Proof.
move=> mD Y mY; apply: measurableI => //.
by rewrite -(setTI (_ @^-1` _)); exact: measurable_funPT.
Qed.
Arguments measurable_funP {d d' aT rT D} s.
(*#[global] Hint Extern 0 (measurable_fun _ _) =>
  solve [apply: measurable_funPT] : core.*)

Module HBSimple.

HB.structure Definition SimpleFun d (aT : sigmaRingType d) (rT : realType) :=
  {f of @isMeasurableFun d _ aT rT f & @FiniteImage aT rT f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Lemma measurable_sfunP {d d'} {aT : measurableType d} {rT : measurableType d'}
  (f : {mfun aT >-> rT}) (Y : set rT) : measurable Y -> measurable (f @^-1` Y).
Proof. by move=> mY; rewrite -[f @^-1` _]setTI; exact: measurable_funP. Qed.

HB.mixin Record isNonNegFun (aT : Type) (rT : numDomainType) (f : aT -> rT) := {
  fun_ge0 : forall x, 0 <= f x
}.
HB.structure Definition NonNegFun aT rT := {f of @isNonNegFun aT rT f}.
Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Notation "{ 'nnfun' aT >-> T }" := (@NonNegFun.type aT T) : form_scope.
Notation "[ 'nnfun' 'of' f ]" := [the {nnfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: fun_ge0] : core.

Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").

Module HBNNSimple.
Import HBSimple.

HB.structure Definition NonNegSimpleFun
    d (aT : sigmaRingType d) (rT : realType) :=
  {f of @SimpleFun d _ _ f & @NonNegFun aT rT f}.

End HBNNSimple.

Notation "{ 'nnsfun' aT >-> T }" := (@HBNNSimple.NonNegSimpleFun.type _ aT%type T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section mfun_pred.
Context {d d'} {aT : sigmaRingType d} {rT : sigmaRingType d'}.
Definition mfun : {pred aT -> rT} := mem [set f | measurable_fun setT f].
Definition mfun_key : pred_key mfun. Proof. exact. Qed.
Canonical mfun_keyed := KeyedPred mfun_key.
End mfun_pred.

Section mfun.
Context {d d'} {aT : sigmaRingType d} {rT : sigmaRingType d'}.
Notation T := {mfun aT >-> rT}.
Notation mfun := (@mfun _ _ aT rT).

Section Sub.
Context (f : aT -> rT) (fP : f \in mfun).
Definition mfun_Sub_subproof := @isMeasurableFun.Build d _ aT rT f (set_mem fP).
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

HB.instance Definition _ := isSub.Build _ _ T mfun_rect mfun_valP.

Lemma mfuneqP (f g : {mfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {mfun aT >-> rT} by <:].

HB.instance Definition _ x := isMeasurableFun.Build d _ aT rT (cst x)
  (@measurable_cst _ _ aT rT setT x).

End mfun.

Section mfun_realType.
Context {rT : realType}.

HB.instance Definition _ := @isMeasurableFun.Build _ _ _ rT
  (@normr rT rT) (@normr_measurable rT setT).

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ (@expR rT) (@measurable_expR rT).

End mfun_realType.

Section mfun_measurableType.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  {d3} {T3 : measurableType d3}.
Variables (f : {mfun T2 >-> T3}) (g : {mfun T1 >-> T2}).

Lemma measurableT_comp_subproof : measurable_fun setT (f \o g).
Proof. exact: measurableT_comp. Qed.

HB.instance Definition _ := isMeasurableFun.Build _ _ _ _ (f \o g)
  measurableT_comp_subproof.

End mfun_measurableType.

Section ring.
Context d (aT : measurableType d) (rT : realType).

Lemma mfun_subring_closed : subring_closed (@mfun _ _ aT rT).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- exact: measurable_cst.
- exact: measurable_funB.
- exact: measurable_funM.
Qed.
HB.instance Definition _ := GRing.isSubringClosed.Build _
  (@mfun d default_measure_display aT rT) mfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of {mfun aT >-> rT} by <:].

Implicit Types (f g : {mfun aT >-> rT}).

Lemma mfun0 : (0 : {mfun aT >-> rT}) =1 cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma mfun1 : (1 : {mfun aT >-> rT}) =1 cst 1 :> (_ -> _). Proof. by []. Qed.
Lemma mfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma mfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma mfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma mfunM f g : f * g = f \* g :> (_ -> _). Proof. by []. Qed.
Lemma mfunMn f n : (f *+ n) = (fun x => f x *+ n) :> (_ -> _).
Proof. by apply/funext=> x; elim: n => //= n; rewrite !mulrS !mfunD /= => ->. Qed.
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
(* TODO: fix this: HB.instance Definition _ f (n : nat) := MeasurableFun.copy (fun x => f x *+ n) (f *+ n). *)

Definition mindic (D : set aT) of measurable D : aT -> rT := \1_D.

Lemma mindicE (D : set aT) (mD : measurable D) :
  mindic mD = (fun x => (x \in D)%:R).
Proof. by rewrite /mindic funeqE => t; rewrite indicE. Qed.

HB.instance Definition _ D mD := @isMeasurableFun.Build _ _ aT rT (mindic mD)
  (@measurable_indic _ aT rT setT D mD).

Definition indic_mfun (D : set aT) (mD : measurable D) : {mfun aT >-> rT} :=
  mindic mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst k).
Definition scale_mfun k f : {mfun aT >-> rT} := k \o* f.

Lemma max_mfun_subproof f g : @isMeasurableFun d _ aT rT (f \max g).
Proof. by split; apply: measurable_maxr. Qed.

HB.instance Definition _ f g := max_mfun_subproof f g.

Definition max_mfun f g : {mfun aT >-> _} := f \max g.

End ring.
Arguments indic_mfun {d aT rT} _.
(* TODO: move earlier?*)
#[global] Hint Extern 0  (measurable_fun _ (\1__ : _ -> _)) =>
  (exact: measurable_indic ) : core.

Section sfun_pred.
Context {d} {aT : sigmaRingType d} {rT : realType}.
Definition sfun : {pred _ -> _} := [predI @mfun _ _ aT rT & fimfun].
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
  @isMeasurableFun.Build d _ aT rT f (set_mem (sub_sfun_mfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT rT f (set_mem (sub_sfun_fimfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : T -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_sfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_sfun_fimfun Pf) by [].
exact: Ksub.
Qed.

Import HBSimple.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> rT} by <:].

(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FImFun aT rT (cst x) := FImFun.on (cst x).

Definition cst_sfun x : {sfun aT >-> rT} := cst x.

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

HB.instance Definition _ := GRing.isSubringClosed.Build _ sfun
  sfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of {sfun aT >-> rT} by <:].

Implicit Types (f g : {sfun aT >-> rT}).

Import HBSimple.

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

Import HBSimple.
(* NB: already instantiated in lebesgue_integral.v *)
HB.instance Definition _ (D : set aT) (mD : measurable D) :
   @FImFun aT rT (mindic _ mD) := FImFun.on (mindic _ mD).

Definition indic_sfun (D : set aT) (mD : measurable D) : {sfun aT >-> rT} :=
  mindic rT mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst_sfun k).
Definition scale_sfun k f : {sfun aT >-> rT} := k \o* f.

HB.instance Definition _ f g := max_mfun_subproof f g.
Definition max_sfun f g : {sfun aT >-> _} := f \max g.

End ring.
Arguments indic_sfun {d aT rT} _.

Lemma preimage_nnfun0 T (R : realDomainType) (f : {nnfun T >-> R}) t :
  t < 0 -> f @^-1` [set t] = set0.
Proof.
move=> t0.
by apply/preimage10 => -[x _]; apply: contraPnot t0 => <-; rewrite le_gtF.
Qed.

Lemma preimage_cstM T (R : realFieldType) (x y : R) (f : T -> R) :
  x != 0 -> (cst x \* f) @^-1` [set y] = f @^-1` [set y / x].
Proof.
move=> x0; apply/seteqP.
by split=> [z/= <-|z/= ->]; rewrite [x * _]mulrC (mulfK, divfK).
Qed.

Lemma preimage_add T (R : numDomainType) (f g : T -> R) z :
  (f \+ g) @^-1` [set z] = \bigcup_(a in f @` setT)
    ((f @^-1` [set a]) `&` (g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= fgz|x [_ /= [y _ <-]] [fxfy gzf]]; last first.
  by rewrite gzf -fxfy addrC subrK.
exists (z - g x); first by exists x; rewrite // -fgz addrK.
by split; rewrite 1?subKr // -fgz addrK.
Qed.

Section simple_bounded.
Context d (T : sigmaRingType d) (R : realType).

Import HBSimple.

Lemma simple_bounded (f : {sfun T >-> R}) : bounded_fun f.
Proof.
have /finite_seqP[r fr] := fimfunP f.
exists (fine (\big[maxe/-oo%E]_(i <- r) `|i|%:E)).
split; rewrite ?num_real// => x mx z _; apply/ltW/(le_lt_trans _ mx).
have ? : f z \in r by have := imageT f z; rewrite fr.
rewrite -[leLHS]/(fine `|f z|%:E) fine_le//.
  (* TODO: generalize the statement of bigmaxe_fin_num *)
  have := @bigmaxe_fin_num _ (map normr r) `|f z|.
  by rewrite big_map => ->//; apply/mapP; exists (f z).
by rewrite (bigmax_sup_seq _ _ (lexx _)).
Qed.

End simple_bounded.

Section nnsfun_functions.
Context d (T : measurableType d) (R : realType).

Import HBNNSimple.

Lemma cst_nnfun_subproof (x : {nonneg R}) : forall t : T, 0 <= cst x%:num t.
Proof. by move=> /=. Qed.
HB.instance Definition _ x := @isNonNegFun.Build T R (cst x%:num)
  (cst_nnfun_subproof x).

(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FImFun T R (cst x) := FImFun.on (cst x).

Definition cst_nnsfun (r : {nonneg R}) : {nnsfun T >-> R} := cst r%:num.

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%R%:nng.

Lemma indic_nnfun_subproof (D : set T) : forall x, 0 <= (\1_D) x :> R.
Proof. by []. Qed.

HB.instance Definition _ D := @isNonNegFun.Build T R \1_D
  (indic_nnfun_subproof D).

HB.instance Definition _ D (mD : measurable D) :
   @NonNegFun T R (mindic R mD) := NonNegFun.on (mindic R mD).

End nnsfun_functions.
Arguments nnsfun0 {d T R}.

Section nnfun_bin.
Variables (T : Type) (R : numDomainType) (f g : {nnfun T >-> R}).

Lemma add_nnfun_subproof : @isNonNegFun T R (f \+ g).
Proof. by split => x; rewrite addr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := add_nnfun_subproof.

Lemma mul_nnfun_subproof : @isNonNegFun T R (f \* g).
Proof. by split => x; rewrite mulr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := mul_nnfun_subproof.

Lemma max_nnfun_subproof : @isNonNegFun T R (f \max g).
Proof. by split => x /=; rewrite /maxr; case: ifPn => _; apply: fun_ge0. Qed.
HB.instance Definition _ := max_nnfun_subproof.

End nnfun_bin.

Section nnsfun_bin.
Context d (T : measurableType d) (R : realType).
Variables f g : {nnsfun T >-> R}.

Import HBNNSimple.

HB.instance Definition _ := MeasurableFun.on (f \+ g).
Definition add_nnsfun : {nnsfun T >-> R} := f \+ g.

HB.instance Definition _ := MeasurableFun.on (f \* g).
Definition mul_nnsfun : {nnsfun T >-> R} := f \* g.

HB.instance Definition _ := MeasurableFun.on (f \max g).
Definition max_nnsfun : {nnsfun T >-> R} := f \max g.

Definition indic_nnsfun A (mA : measurable A) : {nnsfun T >-> R} := mindic R mA.

End nnsfun_bin.
Arguments add_nnsfun {d T R} _ _.
Arguments mul_nnsfun {d T R} _ _.
Arguments max_nnsfun {d T R} _ _.

Section nnsfun_iter.
Context d (T : measurableType d) (R : realType) (D : set T).
Variable f : {nnsfun T >-> R}^nat.

Definition sum_nnsfun n := \big[add_nnsfun/nnsfun0]_(i < n) f i.

Import HBNNSimple.

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

Import HBNNSimple.

Lemma nnsfun_cover : \big[setU/set0]_(i \in range f) (f @^-1` [set i]) = setT.
Proof. by rewrite fsbig_setU//= -subTset => x _; exists (f x). Qed.

Lemma nnsfun_coverT : \big[setU/set0]_(i \in [set: R]) f @^-1` [set i] = setT.
Proof.
by rewrite -(fsbig_widen (range f)) ?nnsfun_cover//= => x [_ /preimage10].
Qed.

End nnsfun_cover.

(* FIXME: shouldn't we avoid calling [done] in a hint? *)
#[global] Hint Extern 0 (measurable (_ @^-1` [set _])) =>
  solve [apply: measurable_sfunP; exact: measurable_set1] : core.

Lemma measurable_sfun_inP {d} {aT : measurableType d} {rT : realType}
   (f : {mfun aT >-> rT}) D (y : rT) :
  measurable D -> measurable (D `&` f @^-1` [set y]).
Proof. by move=> Dm; exact: measurableI. Qed.

#[global] Hint Extern 0 (measurable (_ `&` _ @^-1` [set _])) =>
  solve [apply: measurable_sfun_inP; assumption] : core.

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

Import HBNNSimple.

Lemma additive_nnsfunr (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in range g) (g @^-1` [set i])).
Proof.
rewrite -?measure_fsbig//.
- by rewrite !fsbig_finite//= big_distrr.
- by move=> i Ai; apply: measurableI.
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
case: (ltP x 0%R) => [x_lt0 ? ->|x_ge0 fx_ge0 _] //; last exact: mule_ge0.
by rewrite mule0.
Qed.

Lemma nnfun_muleindic_ge0 d (T : sigmaRingType d) (R : realDomainType)
  (f : {nnfun T >-> R}) r z : 0 <= r%:E * (\1_(f @^-1` [set r]) z)%:E.
Proof.
apply: (@mulef_ge0 _ _ (fun r => (\1_(f @^-1` [set r]) z)%:E)).
  by rewrite lee_fin// indicE.
by move=> r0; rewrite preimage_nnfun0// indic0.
Qed.

Lemma mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) x (A : R -> set T) :
  ((x < 0)%R -> A x = set0) -> 0 <= x%:E * mu (A x).
Proof.
by move=> xA; rewrite (@mulef_ge0 _ _ (mu \o _))//= => /xA ->; rewrite measure0.
Qed.
Global Arguments mulemu_ge0 {d T R mu x} A.

Import HBNNSimple.

Lemma nnsfun_mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : {nnsfun T >-> R}) x :
  0 <= x%:E * mu (f @^-1` [set x]).
Proof.
by apply: (mulemu_ge0 (fun x => f @^-1` [set x])); exact: preimage_nnfun0.
Qed.

End mulem_ge0.

(** Definition of Simple Integrals *)

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
Context d (T : sigmaRingType d) (R : realType).
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

Import HBNNSimple.

Lemma sintegral_ge0 (f : {nnsfun T >-> R}) : 0 <= sintegral mu f.
Proof. by rewrite sintegralE fsume_ge0// => r _; exact: nnsfun_mulemu_ge0. Qed.

Lemma sintegral_indic (A : set T) : sintegral mu \1_A = mu A.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; 1%R]) => //=; last 2 first.
  - exact: image_indic_sub.
  - by move=> t [[] -> /= /preimage10->]; rewrite measure0 mule0.
have N01 : (0 <> 1:> R)%R by apply/eqP; rewrite eq_sym oner_eq0.
rewrite fsbigU//=; last by move=> t [->].
rewrite !fsbig_set1 mul0e add0e mul1e.
by rewrite preimage_indic ifT ?inE// ifN ?notin_setE.
Qed.

(* NB: not used *)
Lemma sintegralEnnsfun (f : {nnsfun T >-> R}) : sintegral mu f =
  (\sum_(x \in [set r | r > 0]%R) (x%:E * mu (f @^-1` [set x])))%E.
Proof.
rewrite (fsbig_widen _ setT) ?sintegralET//.
move=> x [_ /=]; case: ltgtP => //= [xlt0 _|<-]; last by rewrite mul0e.
rewrite preimage10 ?measure0 ?mule0//= => -[t _ xE].
by apply/negP: xlt0; rewrite -leNgt -xE.
Qed.

End sintegral_lemmas.

Lemma eq_sintegral d (T : sigmaRingType d) (R : numDomainType)
    (mu : set T -> \bar R) g f :
  f =1 g -> sintegral mu f = sintegral mu g.
Proof. by move=> /funext->. Qed.
Arguments eq_sintegral {d T R mu} g.

Section sintegralrM.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (r : R) (f : {nnsfun T >-> R}).

Import HBNNSimple.

Lemma sintegralrM : sintegral m (cst r \* f)%R = r%:E * sintegral m f.
Proof.
have [->|r0] := eqVneq r 0%R.
  by rewrite mul0e (eq_sintegral (cst 0%R)) ?sintegral0// => x/=; rewrite mul0r.
rewrite !sintegralET ge0_mule_fsumr; last exact: nnsfun_mulemu_ge0.
rewrite (reindex_fsbigT ( *%R r))/=; last first.
  by exists ( *%R r^-1); [exact: mulKf|exact: mulVKf].
by apply: eq_fsbigr => x; rewrite preimage_cstM// [_ / r]mulrC mulKf// muleA.
Qed.

End sintegralrM.

Section sintegralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f g : {nnsfun T >-> R}).

Import HBNNSimple.

Lemma sintegralD : sintegral m (f \+ g)%R = sintegral m f + sintegral m g.
Proof.
rewrite !sintegralE; set F := f @` _; set G := g @` _; set FG := _ @` _.
pose pf x := f @^-1` [set x]; pose pg y := g @^-1` [set y].
transitivity (\sum_(z \in FG) z%:E * \sum_(a \in F) m (pf a `&` pg (z - a)%R)).
  apply: eq_fsbigr => z _; rewrite preimage_add -fsbig_setU// measure_fsbig//.
    by move=> x Fx; exact: measurableI.
  exact/trivIset_setIr/trivIset_preimage1.
under eq_fsbigr do rewrite ge0_mule_fsumr//; rewrite exchange_fsbig//=.
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

Import HBNNSimple.

Hypothesis fg : forall x, f x <= g x.

Let fgnn : @isNonNegFun T R (g \- f).
Proof. by split=> x; rewrite subr_ge0 fg. Qed.
#[local] HB.instance Definition _ := fgnn.

Lemma le_sintegral : (sintegral m f <= sintegral m g)%E.
Proof.
have gfgf : g =1 f \+ (g \- f) by move=> x /=; rewrite addrC subrK.
by rewrite (eq_sintegral _ _ gfgf) sintegralD// leeDl // sintegral_ge0.
Qed.

End le_sintegral.

Section is_cvg_sintegral.
Import HBNNSimple.

Lemma is_cvg_sintegral d (T : measurableType d) (R : realType)
  (m : {measure set T -> \bar R}) (f : {nnsfun T >-> R}^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) -> cvgn (sintegral m \o f).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
by apply: le_sintegral => // => x; exact/nd_f.
Qed.

End is_cvg_sintegral.

Definition proj_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Section mrestrict.
Import HBNNSimple.

Definition mrestrict d (T : measurableType d) (R : realType) (f : {nnsfun T >-> R})
  A (mA : measurable A) : f \_ A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

End mrestrict.

Definition scale_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (NngNum k0)) f.

Section sintegral_nondecreasing_limit_lemma.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat) (f : {nnsfun T >-> R}).

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, cvgn (g^~ x) -> f x <= limn (g^~ x).

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
- rewrite -bigcup_seq; exists (f t); first by rewrite /= in_fset_set//= mem_set.
  rewrite -bigcup_seq_cond; exists (g n t) => //=.
  by rewrite in_fset_set// mem_set.
- rewrite bigsetU_fset_set// => -[r [x _ fxr]].
  rewrite bigsetU_fset_set_cond// => -[r' [[x' _ gnx'r'] crr']].
  by rewrite /preimage/= => -[-> ->].
Qed.

Let g1 c n : {nnsfun T >-> R} := proj_nnsfun f (mfleg c n).

Let le_ffleg c : {homo (fun p x => g1 c p x): m n / (m <= n)%N >-> (m <= n)%O}.
Proof.
move=> m n mn; apply/asboolP => t; rewrite /g1/= ler_pM// 2!mindicE/= ler_nat.
have [|//] := boolP (t \in fleg c m); rewrite inE => cnt.
by have := nd_fleg c mn => /subsetPset/(_ _ cnt) cmt; rewrite mem_set.
Qed.

Let bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = setT.
Proof.
move=> c1; rewrite predeqE => x; split=> // _.
have := @fun_ge0 _ _ f x; rewrite le_eqVlt => /predU1P[|] gx0.
  by exists O => //; rewrite /fleg /=; rewrite -gx0 mulr0 fun_ge0.
have [cf|df] := pselect (cvgn (g^~ x)).
  have cfg : limn (g^~ x) > c * f x.
    by rewrite (lt_le_trans _ (gf cf)) // gtr_pMl.
  suff [n cfgn] : exists n, g n x >= c * f x by exists n.
  move/(@lt_lim _ _ _ (nd_g x) cf) : cfg => [n _ nf].
  by exists n; apply: nf => /=.
have /cvgryPge/(_ (c * f x))[n _ ncfgn]:= nondecreasing_dvgn_lt (nd_g x) df.
by exists n => //; rewrite /fleg /=; apply: ncfgn => /=.
Qed.

Local Open Scope ereal_scope.

Lemma nd_sintegral_lim_lemma : sintegral mu f <= limn (sintegral mu \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu f <= limn (sintegral mu \o g).
  by apply/lee_mul01Pr => //; exact: sintegral_ge0.
move=> c /andP[c0 c1].
have cg1g n : c%:E * sintegral mu (g1 c n) <= sintegral mu (g n).
  rewrite -sintegralrM (_ : (_ \* _)%R = scale_nnsfun (g1 c n) (ltW c0)) //.
  apply: le_sintegral => // t.
  suff : forall m x, (c * g1 c m x <= g m x)%R by move=> /(_ n t).
  move=> m x; rewrite /g1 /proj_nnsfun/= mindicE.
  by have [|] := boolP (_ \in _); [rewrite inE mulr1|rewrite 2!mulr0 fun_ge0].
suff {cg1g}<- : limn (fun n => sintegral mu (g1 c n)) = sintegral mu f.
  have is_cvg_g1 : cvgn (fun n => sintegral mu (g1 c n)).
    by apply: is_cvg_sintegral => //= x m n /(le_ffleg c)/lefP/(_ x).
  rewrite -limeMl // lee_lim//; first exact: is_cvgeMl.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - by apply: nearW; exact: cg1g.
suff : sintegral mu (g1 c n) @[n \oo] --> sintegral mu f by apply/cvg_lim.
rewrite [X in X @ \oo --> _](_ : _ = fun n => \sum_(x <- fset_set (range f))
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

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, g ^~ x @ \oo --> f x.

Let limg x : limn (g^~ x) = f x.
Proof. by apply/cvg_lim => //; exact: gf. Qed.

Lemma nd_sintegral_lim : sintegral mu f = limn (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x; rewrite -limg.
have : nondecreasing_seq (sintegral mu \o g).
  by move=> m n mn; apply: le_sintegral => // x; exact/nd_g.
move=> /ereal_nondecreasing_cvgn/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=; apply: le_sintegral => // x.
rewrite -limg // (nondecreasing_cvgn_le (nd_g x)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Section integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (f g : T -> \bar R) (D : set T).

Import HBNNSimple.

Let nnintegral mu f := ereal_sup [set sintegral mu h |
  h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= f x]].

Definition integral mu D f (g := f \_ D) :=
  nnintegral mu (g ^\+) - nnintegral mu (g ^\-).

Variable (mu : {measure set T -> \bar R}).

Let nnintegral_ge0 f : (forall x, 0 <= f x) -> 0 <= nnintegral mu f.
Proof.
by move=> f0; apply: ereal_sup_ubound; exists nnsfun0 => //; exact: sintegral0.
Qed.

Let eq_nnintegral g f : f =1 g -> nnintegral mu f = nnintegral mu g.
Proof. by move=> /funext->. Qed.

Let nnintegral0 : nnintegral mu (cst 0) = 0.
Proof.
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply/ereal_sup_ubound; exists nnsfun0; [|exact: sintegral0].
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, f x = 0%R.
  by move=> y; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin//.
by rewrite (eq_sintegral (@nnsfun0 _ T R)) ?sintegral0.
Qed.

Let nnintegral_nnsfun (h : {nnsfun T >-> R}) :
  nnintegral mu (EFin \o h) = sintegral mu h.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gh <-]; rewrite le_sintegral.
by apply: ereal_sup_ubound => /=; exists h.
Qed.

Local Notation "\int_ ( x 'in' D ) F" := (integral mu D (fun x => F)%E)
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

Lemma integral0_eq D f :
  (forall x, D x -> f x = 0) -> \int_(x in D) f x = 0.
Proof.
move=> f0; under eq_integral; first by move=> x /[1!inE] /f0 ->; over.
by rewrite integral0.
Qed.

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
  (integral mu D (fun x => f)%E) : ereal_scope.
Notation "\int [ mu ]_ x f" :=
  ((integral mu setT (fun x => f)%E))%E : ereal_scope.
Arguments eq_integral {d T R mu D} g.

Section eq_measure_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (D : set T).
Implicit Types m : {measure set T -> \bar R}.

Import HBNNSimple.

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

Import HBNNSimple.

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

Import HBNNSimple.

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

Lemma integral_set0 d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : T -> \bar R) :
  (\int[mu]_(x in set0) f x = 0)%E.
Proof.
rewrite integral_mkcond integral0_eq// => x _.
by rewrite /restrict; case: ifPn => //; rewrite in_set0.
Qed.

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R)
          (g : {nnsfun T >-> R}^nat).
Hypothesis f0 : forall x, 0 <= f x.
Hypothesis mf : measurable_fun setT f.

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~x).
Hypothesis gf : forall x, EFin \o g^~ x @ \oo --> f x.
Local Open Scope ereal_scope.

Lemma nd_ge0_integral_lim : \int[mu]_x f x = limn (sintegral mu \o g).
Proof.
rewrite ge0_integralTE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: lime_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ubound; exists (g n) => //= => x.
  have <- : limn (EFin \o g ^~ x) = f x by apply/cvg_lim => //; exact: gf.
  have : EFin \o g ^~ x @ \oo --> ereal_sup (range (EFin \o g ^~ x)).
    by apply: ereal_nondecreasing_cvgn => p q pq /=; rewrite lee_fin; exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ubound; exists n.
have := leey (\int[mu]_x (f x)).
rewrite [in X in X -> _]le_eqVlt => /predU1P[|] mufoo; last first.
  have : \int[mu]_x (f x) \is a fin_num by rewrite ge0_fin_numE// integral_ge0.
  rewrite ge0_integralTE// => /ub_ereal_sup_adherent h.
  apply/lee_addgt0Pr => _/posnumP[e].
  have {h} [/= _ [G Gf <-]] := h _ [gt0 of e%:num].
  rewrite EFinN lteBlDr// => fGe.
  have : forall x, cvgn (g^~ x) -> (G x <= limn (g ^~ x))%R.
    move=> x cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _))// gxfx.
  move=> /(nd_sintegral_lim_lemma mu nd_g)/(leeD2r e%:num%:E).
  by apply: le_trans; exact: ltW.
suff : limn (sintegral mu \o g) = +oo.
  by move=> ->; rewrite -ge0_integralTE// mufoo.
apply/eqyP => r r0.
have [G [Gf rG]] : exists h : {nnsfun T >-> R},
    (forall x, (h x)%:E <= f x) /\ (r%:E <= sintegral mu h).
  have : r%:E < \int[mu]_x (f x).
    move: (mufoo) => /eqyP/(_ _ (addr_gt0 r0 r0)).
    by apply: lt_le_trans => //; rewrite lte_fin ltrDr.
  rewrite ge0_integralTE// => /ereal_sup_gt[x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, cvgn (g^~ x) -> (G x <= limn (g^~ x))%R.
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
move=> r Hr; apply/orP; rewrite -itv_splitU ?bnd_simp/=; last first.
  by rewrite !ler_pM2r// !ler_nat leqW//=.
move: Hr; apply/subitvP; rewrite {r}!subitvE !bnd_simp exprSr -muln2.
rewrite ler_pdivrMr// mulrA divfK// -natrM lexx/=.
by rewrite ler_pdivlMr// mulrA divfK// -natrM ler_nat.
Qed.

Lemma bigsetU_dyadic_itv n : `[n%:R, n.+1%:R[%classic =
  \big[setU/set0]_(n * 2 ^ n.+1 <= k < n.+1 * 2 ^ n.+1) [set` I n.+1 k].
Proof.
rewrite predeqE => r; split => [/= /[!in_itv]/= /andP[nr rn1]|]; last first.
  rewrite -bigcup_seq => -[/= k] /[!mem_index_iota] nkn; apply: subitvP.
  rewrite subitvE !bnd_simp ler_pdivlMr// ler_pdivrMr//.
  by rewrite -natrX -2!natrM 2!ler_nat.
have ?: 0 <= r * 2 ^+ n.+1 by rewrite mulr_ge0// (le_trans _ nr).
rewrite -bigcup_seq /=; exists (trunc (r * 2 ^+ n.+1)).
  rewrite /= mem_index_iota -trunc_ge_nat// -trunc_lt_nat//.
  by rewrite !natrM natrX ler_pM2r// ltr_pM2r// nr.
rewrite /= in_itv/= ler_pdivrMr// ltr_pdivlMr//.
by rewrite trunc_ge_nat// trunc_lt_nat// !leqnn.
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
rewrite (bigsetU_dyadic_itv n) inE /= => -[r]; rewrite -bigcup_seq => -[k /=].
rewrite mem_index_iota => nk Ir rfx.
by exists k; split; [rewrite !(mulnC (2 ^ n.+1)%N)|rewrite !inE /=; exists r].
Qed.

End dyadic_interval.

Section approximation.
Context d (T : measurableType d) (R : realType).
Variables (D : set T) (mD : measurable D).
Variables (f : T -> \bar R) (mf : measurable_fun D f).

Local Notation I := (@dyadic_itv R).

Definition dyadic_approx n k := if (k < n * 2 ^ n)%N then
  D `&` [set x | f x \in EFin @` [set` I n k]] else set0.

Definition integer_approx n := D `&` [set x | n%:R%:E <= f x]%E.

Local Notation A := dyadic_approx.
Local Notation B := integer_approx.

Definition approx : (T -> R)^nat := fun n x =>
  \sum_(k < n * 2 ^ n) k%:R * 2 ^- n * \1_(A n k) x + n%:R * \1_(B n) x.

(* technical properties of the sets A and B *)
Let mA n k : measurable (A n k).
Proof.
rewrite /A; case: ifPn => [kn|_]//; rewrite -preimage_comp.
by apply: mf => //; apply/measurable_image_EFin; exact: measurable_itv.
Qed.

Let trivIsetA n : trivIset setT (A n).
Proof.
apply/trivIsetP => i j _ _ ineqj.
rewrite /A; case: ltnP => ni; last by rewrite set0I.
case: ltnP => nj; last by rewrite setI0.
rewrite predeqE/= => t; rewrite !inE; split=> // -[[Dt [r rI rE]] [_ [s + sE]]].
have {s sE}[->/(conj rI)/andP]: s%:E = r%:E by rewrite rE sE.
rewrite -{rI}in_itvI /Order.meet /= /Order.join /= /Order.meet /= !orbT !andbT.
rewrite le_total joinEtotal meetEtotal -maxr_pMl// -minr_pMl// in_itv/=.
case/andP => [/le_lt_trans/[apply]]; rewrite ltr_pM2r//.
rewrite /maxr /minr !ltr_nat ltnS -!fun_if ltr_nat ltnS.
by case: ltngtP ineqj => //=; case: ltngtP.
Qed.

Let f0_A0 n (i : 'I_(n * 2 ^ n)) x : f x = 0%:E -> i != O :> nat ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> fx0 i0; rewrite indicE memNset// /A ltn_ord => -[Dx/=] /[1!inE]/= -[r].
rewrite in_itv/= fx0 => /[swap] -[->].
by rewrite ler_pdivrMr// mul0r lern0 (negbTE i0).
Qed.

Let fgen_A0 n x (i : 'I_(n * 2 ^ n)) : (n%:R%:E <= f x)%E ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> fxn; rewrite indicE /A ltn_ord memNset// => -[Dx/=] /[1!inE]/= -[r].
rewrite in_itv/= => /andP[_ h] rfx; move: fxn; rewrite -rfx lee_fin; apply/negP.
by rewrite -ltNge (lt_le_trans h)// ler_pdivrMr// -natrX -natrM ler_nat ltn_ord.
Qed.

Let disj_A0 x n (i k : 'I_(n * 2 ^ n)) : i != k -> x \in A n k ->
  \1_(A n i) x = 0 :> R.
Proof.
move=> ik /[1!inE] xAn1k; rewrite indicE memNset// => xAi.
have /trivIsetP/(_ _ _ Logic.I Logic.I ik)/= := @trivIsetA n.
by rewrite predeqE => /(_ x)[+ _]; exact.
Qed.
Arguments disj_A0 {x n i} k.

Let mB n : measurable (B n). Proof. exact: emeasurable_fun_c_infty. Qed.

Let foo_B1 x n : D x -> f x = +oo%E -> \1_(B n) x = 1 :> R.
Proof. by move=> Dx fxoo; rewrite indicE mem_set// /B/= fxoo leey. Qed.

Let f0_B0 x n : f x = 0%:E -> n != 0%N -> \1_(B n) x = 0 :> R.
Proof.
by move=> h /negbTE n0; rewrite indicE memNset// /B/= h lee_fin lern0 n0 => -[].
Qed.

Let fgtn_B0 x n : (f x < n%:R%:E)%E -> \1_(B n) x = 0 :> R.
Proof. by move=> h; rewrite indicE memNset// => -[_/=]; rewrite leNgt h. Qed.

Let f0_approx0 n x : f x = 0%E -> approx n x = 0.
Proof.
move=> fx0; rewrite /approx; have [->|n0] := eqVneq n O.
  by rewrite mul0n mul0r addr0 big_ord0.
rewrite f0_B0// mulr0 addr0 big1// => i _.
have [->|i0] := eqVneq (nat_of_ord i) 0%N; first by rewrite mul0r mul0r.
by rewrite f0_A0 // mulr0.
Qed.

Let fpos_approx_neq0 x : D x -> (0%E < f x < +oo)%E ->
  \forall n \near \oo, approx n x != 0.
Proof.
move=> Dx /andP[fx_gt0 fxoo].
have fxfin : f x \is a fin_num by rewrite gt0_fin_numE.
rewrite -(fineK fxfin) lte_fin in fx_gt0; near=> n.
rewrite /approx paddr_eq0//; last 2 first.
  by apply: sumr_ge0 => i _; rewrite mulr_ge0.
  by rewrite mulr_ge0.
rewrite psumr_eq0//; last by move=> i _; rewrite mulr_ge0.
apply/negP => /andP[/allP An0]; rewrite mulf_eq0 => /orP[|].
  by apply/negP; near: n; exists 1%N => //= m /=; rewrite lt0n pnatr_eq0.
rewrite pnatr_eq0 eqb0 notin_setE /B => /not_andP[] // /negP.
rewrite -ltNge => fxn.
have K : (trunc (fine (f x) * 2 ^+ n) < n * 2 ^ n)%N.
  rewrite -trunc_lt_nat; last by rewrite mulr_ge0// ltW.
  by rewrite natrM natrX ltr_pM2r// -lte_fin (fineK fxfin).
have /[!mem_index_enum]/(_ isT) := An0 (Ordinal K).
rewrite implyTb indicE mem_set ?mulr1; last first.
  rewrite /A K /= inE; split=> //=; exists (fine (f x)); last by rewrite fineK.
  by rewrite in_itv/= ler_pdivrMr// ltr_pdivlMr// trunc_itv// mulr_ge0// ltW.
apply/negP; rewrite mulf_eq0 -exprVn negb_or expf_neq0//= andbT.
rewrite pnatr_eq0 -lt0n trunc_gt0 -ler_pdivrMr// ltW//; near: n.
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
move=> /allPn[/= k _].
rewrite mulf_eq0 negb_or mulf_eq0 negb_or -andbA => /and3P[k_neq0 _].
rewrite pnatr_eq0 eqb0 negbK => xAnk; right.
rewrite (bigD1 k) //= indicE xAnk mulr1 big1 ?addr0; last first.
  by move=> i ik; rewrite (disj_A0 k)// mulr0.
exists k; split => //; first by rewrite lt0n -(@pnatr_eq0 R) k_neq0/=.
by move: xAnk; rewrite inE /A ltn_ord /= inE /= => -[/[swap] Dx].
Qed.

Let notinD_approx0 x n : ~ D x -> approx n x = 0 :> R.
Proof.
move=> Dx; rewrite /approx big1; last first.
  by move=> i _; rewrite indicE memNset ?mulr0// /A; case: ifPn => [? []|_].
by rewrite indicE memNset// ?mulr0 ?addr0// => -[].
Qed.

Lemma nd_approx : nondecreasing_seq approx.
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x.
have [Dx|Dx] := pselect (D x); last by rewrite ?notinD_approx0.
have [fxn|fxn] := ltP (f x) n%:R%:E.
  rewrite {2}/approx fgtn_B0 ?mulr0 ?addr0; last first.
    by rewrite (lt_trans fxn) // lte_fin ltr_nat.
  have [/eqP ->|[k [/andP[k0 kn] xAnk -> _]]] := f_ub_approx fxn.
    by apply: sumr_ge0 => i _; rewrite mulr_ge0.
  move: (xAnk); rewrite inE {1}/A kn => -[_] /=.
  rewrite inE => -[r] /dyadic_itv_subU[|] rnk rfx.
  - have k2n : (k.*2 < n.+1 * 2 ^ n.+1)%N.
      rewrite expnS mulnCA mul2n ltn_double (ltn_trans kn) //.
      by rewrite ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //= indicE.
    have xAn1k : x \in A n.+1 k.*2.
      by rewrite inE /A k2n; split => //=; rewrite inE; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) ?mulr0.
    by rewrite exprS invfM mulrA -muln2 natrM mulfK.
  - have k2n : (k.*2.+1 < n.+1 * 2 ^ n.+1)%N.
      move: kn; rewrite -ltn_double -(ltn_add2r 1) 2!addn1 => /leq_trans; apply.
      by rewrite -muln2 -mulnA -expnSr ltn_mul2r expn_gt0 /= ltnS.
    rewrite (bigD1 (Ordinal k2n)) //= indicE.
    have xAn1k : x \in A n.+1 k.*2.+1.
      by rewrite /A /= k2n inE; split => //=; rewrite inE/=; exists r.
    rewrite xAn1k mulr1 big1 ?addr0; last first.
      by move=> i ik2n; rewrite (disj_A0 (Ordinal k2n)) // mulr0.
    by rewrite ler_pdivlMr// exprSr mulrA divfK// -natrM muln2 ler_nat.
have /orP[{}fxn|{}fxn] :
    ((n%:R%:E <= f x < n.+1%:R%:E) || (n.+1%:R%:E <= f x))%E.
  - by move: fxn; case: leP => /= [_ _|_ ->//]; rewrite orbT.
  - have [k [k1 k2]] := dyadic_itv_image fxn.
    have xBn : x \in B n by rewrite /B /= inE /=; case/andP : fxn => ->.
    rewrite /approx indicE xBn mulr1 big1 ?add0r; last first.
      by move=> /= i _; rewrite fgen_A0 ?mulr0//; case/andP : fxn.
    rewrite fgtn_B0 ?mulr0 ?addr0; last by case/andP : fxn.
    have kn2 : (k < n.+1 * 2 ^ n.+1)%N by case/andP : k1 => _; rewrite mulnC.
    rewrite (bigD1 (Ordinal kn2)) //=.
    have xAn1k : x \in A n.+1 k by rewrite inE /A kn2.
    rewrite indicE xAn1k mulr1 big1 ?addr0; last first.
      by move=> i /= ikn2; rewrite (disj_A0 (Ordinal kn2)) // mulr0.
    by rewrite -natrX ler_pdivlMr// mulrC -natrM ler_nat; case/andP : k1.
- have xBn : x \in B n by rewrite /B inE /= (le_trans _ fxn) // lee_fin ler_nat.
  rewrite /approx indicE xBn mulr1.
  have xBn1 : x \in B n.+1 by rewrite /B /= inE.
  rewrite indicE xBn1 mulr1 big1 ?add0r.
    by rewrite big1 ?add0r ?ler_nat// => /= i _; rewrite fgen_A0// mulr0.
  by move=> /= i _; rewrite fgen_A0 ?mulr0// (le_trans _ fxn)// lee_fin ler_nat.
Qed.

Lemma cvg_approx x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  (f x < +oo)%E -> approx^~ x @ \oo --> fine (f x).
Proof.
move=> Dx fxoo; have fxfin : f x \is a fin_num by rewrite ge0_fin_numE// f0.
apply/(@cvgrPdist_lt _ R^o) => _/posnumP[e].
have [fx0|fx0] := eqVneq (f x) 0%E.
  by near=> n; rewrite f0_approx0 // fx0 /= subrr normr0.
have /(fpos_approx_neq0 Dx)[m _ Hm] : (0 < f x < +oo)%E by rewrite lt0e fx0 f0.
near=> n.
have mn : (m <= n)%N by near: n; exists m.
have : fine (f x) < n%:R.
  near: n.
  exists `|floor (fine (f x))|.+1%N => //= p /=.
  rewrite -(@ler_nat R); apply: lt_le_trans.
  rewrite -natr1 (_ : `| _ |%:R  = (floor (fine (f x)))%:~R); last first.
    by rewrite -[in RHS](@gez0_abs (floor _))// floor_ge0//; exact/fine_ge0/f0.
  by rewrite intrD1 lt_succ_floor.
rewrite -lte_fin (fineK fxfin) => fxn.
have [approx_nx0|[k [/andP[k0 kn2n] ? ->]]] := f_ub_approx fxn.
  by have := Hm _ mn; rewrite approx_nx0.
rewrite inE /= => -[r /=]; rewrite in_itv /= => /andP[k1 k2] rfx.
rewrite (@le_lt_trans _ _ (1 / 2 ^+ n)) //.
  rewrite ler_norml; apply/andP; split.
    rewrite lerBrDl -mulrBl -lee_fin (fineK fxfin) -rfx lee_fin.
    by rewrite (le_trans _ k1)// ler_pM2r// lerBlDl lerDr.
  by rewrite lerBlDr -mulrDl -lee_fin nat1r fineK// ltW// -rfx lte_fin.
by near: n; exact: near_infty_natSinv_expn_lt.
Unshelve. all: by end_near. Qed.

Lemma le_approx k x (f0 : forall x, D x -> (0 <= f x)%E) : D x ->
  ((approx k x)%:E <= f x)%E.
Proof.
move=> Dx; have [fixoo|] := ltP (f x) (+oo%E); last first.
  by rewrite leye_eq => /eqP ->; rewrite leey.
have nd_ag : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
  by move=> m n mn; exact/lefP/nd_approx.
have fi0 y : D y -> (0 <= f y)%E by move=> ?; exact: f0.
have cvg_af := cvg_approx fi0 Dx fixoo.
have is_cvg_af : cvgn (approx ^~ x) by apply/cvg_ex; eexists; exact: cvg_af.
have {is_cvg_af} := nondecreasing_cvgn_le nd_ag is_cvg_af k.
rewrite -lee_fin => /le_trans; apply.
rewrite -(@fineK _ (f x)); last by rewrite ge0_fin_numE// f0.
by move/(cvg_lim (@Rhausdorff R)) : cvg_af => ->.
Qed.

Lemma dvg_approx x : D x -> f x = +oo%E -> ~ cvgn (approx^~ x : _ -> R^o).
Proof.
move=> Dx fxoo; have approx_x n : approx n x = n%:R.
  rewrite /approx foo_B1// mulr1 big1 ?add0r// => /= i _.
  by rewrite fgen_A0 // ?mulr0 // fxoo leey.
case/cvg_ex => /= l; have [l0|l0] := leP 0%R l.
- move=> /cvgrPdist_lt/(_ _ ltr01) -[n _].
  move=> /(_ (`|ceil l|.+1 + n)%N) /= /(_ (leq_addl _ _)); apply/negP.
  rewrite -leNgt approx_x distrC (le_trans _ (lerB_normD _ _))// normrN.
  rewrite lerBrDl addSnnS natrD [leRHS]ger0_norm// lerD ?ler1n// natr_absz.
  by rewrite !ger0_norm ?le_ceil// -ceil_ge0; apply: lt_le_trans l0.
- move=> /cvgrPdist_lt/(_ _ ltr01)[n _].
  move=> /(_ (`|floor l|.+1 + n)%N)/(_ (leq_addl _ _)); apply/negP.
  rewrite approx_x -leNgt distrC (le_trans _ (lerB_normD _ _))// normrN.
  rewrite lerBrDl addSnnS natrD [leRHS]ger0_norm// lerD ?ler1n// natr_absz.
  by rewrite !ltr0_norm -?floor_lt0// mulrNz lerN2 ge_floor.
Qed.

Lemma ecvg_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o approx^~x @ \oo --> f x.
Proof.
move=> Dx; have := leey (f x); rewrite le_eqVlt => /predU1P[|] fxoo.
have dvg_approx := dvg_approx Dx fxoo.
  have : {homo approx ^~ x : n m / (n <= m)%N >-> n <= m}.
    by move=> m n mn; have := nd_approx mn => /lefP; exact.
  move/nondecreasing_dvgn_lt => /(_ dvg_approx).
  by rewrite fxoo => ?; apply/cvgeryP.
rewrite -(@fineK _ (f x)); first exact: (cvg_comp (cvg_approx f0 Dx fxoo)).
by rewrite ge0_fin_numE// f0.
Qed.

Let k2n_ge0 n (k : nat) : 0 <= k%:R * 2 ^- n :> R.
Proof. by []. Qed.

Definition nnsfun_approx : {nnsfun T >-> R}^nat := fun n => locked (add_nnsfun
  (sum_nnsfun
    (fun k => if (k < (n * 2 ^ n))%N then
        scale_nnsfun (indic_nnsfun _ (mA n k)) (k2n_ge0 n k)
      else nnsfun0) (n * 2 ^ n)%N)
  (scale_nnsfun (indic_nnsfun _ (mB n)) (ler0n _ n))).

Import HBNNSimple.

Lemma nnsfun_approxE n : nnsfun_approx n = approx n :> (T -> R).
Proof.
rewrite funeqE => t /=; rewrite /nnsfun_approx; unlock; rewrite /=.
rewrite sum_nnsfunE; congr (_ + _).
by apply: eq_bigr => i _; case: ltnP => [//|]; rewrite leqNgt ltn_ord.
Qed.

Lemma cvg_nnsfun_approx (f0 : forall x, D x -> (0 <= f x)%E) x :
  D x -> EFin \o nnsfun_approx^~x @ \oo --> f x.
Proof.
by move=> Dx; under eq_fun do rewrite nnsfun_approxE; exact: ecvg_approx.
Qed.

Lemma nd_nnsfun_approx : nondecreasing_seq (nnsfun_approx : (T -> R)^nat).
Proof.
move=> m n mn; rewrite (nnsfun_approxE n) (nnsfun_approxE m).
exact: nd_approx.
Qed.

#[deprecated(since="mathcomp-analysis 1.8.0", note="use `nnsfun_approx`, `cvg_nnsfun_approx`, and `nd_nnsfun_approx` instead")]
Lemma approximation : (forall t, D t -> (0 <= f t)%E) ->
  exists g : {nnsfun T >-> R}^nat, nondecreasing_seq (g : (T -> R)^nat) /\
                        (forall x, D x -> EFin \o g^~ x @ \oo --> f x).
Proof.
exists nnsfun_approx; split; [exact: nd_nnsfun_approx|].
by move=> x Dx; exact: cvg_nnsfun_approx.
Qed.

End approximation.

Section ge0_linearityZ.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> \bar R.
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.

Import HBNNSimple.

Lemma ge0_integralZl_EFin k : (0 <= k)%R ->
  \int[mu]_(x in D) (k%:E * f1 x) = k%:E * \int[mu]_(x in D) f1 x.
Proof.
rewrite integral_mkcond erestrict_scale [in RHS]integral_mkcond => k0.
set h1 := f1 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
pose g := nnsfun_approx measurableT mh1.
pose kg := fun n => scale_nnsfun (g n) k0.
rewrite (@nd_ge0_integral_lim _ _ _ mu (fun x => k%:E * h1 x) kg).
- rewrite (_ : _ \o _ = fun n => sintegral mu (scale_nnsfun (g n) k0))//.
  rewrite (_ : (fun _ => _) = (fun n => k%:E * sintegral mu (g n))).
    rewrite limeMl //; last first.
      by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx.
    by rewrite -(nd_ge0_integral_lim mu h10)// => [x m n mn|x];
      [exact/lefP/nd_nnsfun_approx|exact: cvg_nnsfun_approx].
  by under eq_fun do rewrite (sintegralrM mu k (g _)).
- by move=> t; rewrite mule_ge0.
- by move=> x m n mn; rewrite /kg ler_pM//; exact/lefP/nd_nnsfun_approx.
- move=> x.
  rewrite [X in X @ \oo --> _](_ : _ = (fun n => k%:E * (g n x)%:E)) ?funeqE//.
  by apply: cvgeMl => //; exact: cvg_nnsfun_approx.
Qed.

End ge0_linearityZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `ge0_integralZl_EFin` instead")]
Notation ge0_integralM_EFin := ge0_integralZl_EFin (only parsing).

Section ge0_linearityD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Import HBNNSimple.

Lemma ge0_integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
rewrite !(integral_mkcond D) erestrictD.
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
pose g1 := nnsfun_approx measurableT mh1.
pose g2 := nnsfun_approx measurableT mh2.
pose g12 := fun n => add_nnsfun (g1 n) (g2 n).
rewrite (@nd_ge0_integral_lim _ _ _ mu _ g12); last 3 first.
  - by move=> x; rewrite adde_ge0.
  - by apply: nondecreasing_seqD => // x m n mn;
      [exact/lefP/nd_nnsfun_approx|exact/lefP/nd_nnsfun_approx].
  - move=> x; rewrite (_ : _ \o _ = (fun n => (g1 n x)%:E + (g2 n x)%:E))//.
    apply: cvgeD => //; [|exact: cvg_nnsfun_approx..].
    by apply: ge0_adde_def => //; rewrite !inE; [exact: h10|exact: h20].
under [_ \o _]eq_fun do rewrite sintegralD.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g2)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact/cvg_nnsfun_approx.
rewrite limeD//; [
  by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx..|].
by rewrite ge0_adde_def => //; rewrite inE; apply: lime_ge; solve[
  (by apply: is_cvg_sintegral => // x m n mn; exact/lefP/nd_nnsfun_approx) ||
  (by apply: nearW => n; exact: sintegral_ge0)].
Qed.

Lemma ge0_le_integral : (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> f12; rewrite !(integral_mkcond D).
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x by apply: erestrict_ge0.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
have h12 x : h1 x <= h2 x by apply: lee_restrict.
pose g1 := nnsfun_approx measurableT mh1.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact: cvg_nnsfun_approx.
apply: lime_le.
  by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_nnsfun_approx.
near=> n; rewrite ge0_integralTE//; apply: ereal_sup_ubound => /=.
exists (g1 n) => // t; rewrite (le_trans _ (h12 _))//.
have := leey (h1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite leey.
have h1tfin : h1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (h10 t)).
have /= := @cvg_nnsfun_approx _ _ _ _ measurableT _ mh1 (fun x _ => h10 x) t Logic.I.
rewrite -(fineK h1tfin) => /fine_cvgP[ft_near].
set u_ := (X in X --> _) => u_h1.
have <- : lim u_ = fine (h1 t) by exact/cvg_lim.
rewrite lee_fin; apply: nondecreasing_cvgn_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_nnsfun_approx.
by apply/cvg_ex; eexists; exact: u_h1.
Unshelve. all: by end_near. Qed.

End ge0_linearityD.

Section approximation_sfun.
Context d (T : measurableType d) (R : realType) (f : T -> \bar R).
Variables (D : set T) (mD : measurable D) (mf : measurable_fun D f).

Import HBSimple.
(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FImFun T R (cst x) := FImFun.on (cst x).

Import HBNNSimple.
(* NB: already instantiated in lebesgue_integral.v *)
HB.instance Definition _ x : @NonNegFun T R (cst x%:num) :=
  NonNegFun.on (cst x%:num).

Lemma approximation_sfun :
  exists g : {sfun T >-> R}^nat, (forall x, D x -> EFin \o g ^~ x @ \oo --> f x).
Proof.
pose fp_ := nnsfun_approx mD (measurable_funepos mf).
pose fn_ := nnsfun_approx mD (measurable_funeneg mf).
exists (fun n => fp_ n \+ cst (-1) \* fn_ n) => x /=.
rewrite [X in X @ \oo --> _](_ : _ =
    EFin \o fp_^~ x \+ (-%E \o EFin \o fn_^~ x))%E; last first.
  by apply/funext => n/=; rewrite EFinD mulN1r.
by move=> Dx; rewrite (funeposneg f); apply: cvgeD;
  [exact: add_def_funeposneg|apply: cvg_nnsfun_approx|apply:cvgeN; apply: cvg_nnsfun_approx].
Qed.

End approximation_sfun.

Section lusin.
Hint Extern 0 (hausdorff_space _) => (exact: Rhausdorff) : core.
Local Open Scope ereal_scope.
Context (rT : realType) (A : set rT).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.
Hypothesis mA : measurable A.
Hypothesis finA : mu A < +oo.

Import HBSimple.

Let lusin_simple (f : {sfun R >-> rT}) (eps : rT) : (0 < eps)%R ->
  exists K, [/\ compact K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps]; have [N /card_fset_set rfN] := fimfunP f.
pose Af x : set R := A `&` f @^-1` [set x].
have mAf x : measurable (Af x) by exact: measurableI.
have finAf x : mu (Af x) < +oo.
  by rewrite (le_lt_trans _ finA)// le_measure// ?inE//; exact: subIsetl.
have eNpos : (0 < eps%:num / N.+1%:R)%R by [].
have dK' x := lebesgue_regularity_inner (mAf x) (finAf x) eNpos.
pose dK x : set R := projT1 (cid (dK' x)); pose J i : set R := Af i `\` dK i.
have dkP x := projT2 (cid (dK' x)).
have mdK i : measurable (dK i).
  by apply: closed_measurable; apply: compact_closed => //; case: (dkP i).
have mJ i : measurable (J i) by apply: measurableD => //; exact: measurableI.
have dKsub z : dK z `<=` f @^-1` [set z].
  by case: (dkP z) => _ /subset_trans + _; apply => ? [].
exists (\bigcup_(i in range f) dK i); split.
- by rewrite -bigsetU_fset_set//; apply: bigsetU_compact=>// i _; case: (dkP i).
- by move=> z [y _ dy]; have [_ /(_ _ dy) []] := dkP y.
- have -> : A `\` \bigcup_(i in range f) dK i = \bigcup_(i in range f) J i.
    rewrite -bigcupDr /= ?eqEsubset; last by exists (f point), point.
    split => z; first by move=> /(_ (f z)) [//| ? ?]; exists (f z).
    case => ? [? _ <-] [[zab /= <- nfz]] ? [r _ <-]; split => //.
    by move: nfz; apply: contra_not => /[dup] /dKsub ->.
  apply: (@le_lt_trans _ _ (\sum_(i \in range f) mu (J i))).
    by apply: content_sub_fsum => //; exact: fin_bigcup_measurable.
  apply: le_lt_trans.
    apply: (@lee_fsum _ _ _ _ (fun=> (eps%:num / N.+1%:R)%:E * 1%:E)) => //.
    by move=> i ?; rewrite mule1; apply: ltW; have [_ _] := dkP i.
  rewrite /=-ge0_mule_fsumr // -esum_fset // finite_card_sum // -EFinM lte_fin.
  by rewrite rfN -mulrA gtr_pMr // mulrC ltr_pdivrMr // mul1r ltr_nat.
- suff : closed (\bigcup_(i in range f) dK i) /\
    {within \bigcup_(i in range f) dK i, continuous f} by case.
  rewrite -bigsetU_fset_set //.
  apply: (@big_ind _ (fun U => closed U /\ {within U, continuous f})).
  + by split; [exact: closed0 | exact: continuous_subspace0].
  + by move=> ? ? [? ?][? ?]; split; [exact: closedU|exact: withinU_continuous].
  + move=> i _; split; first by apply: compact_closed; have [] := dkP i.
    apply: (continuous_subspaceW (dKsub i)).
    apply: (@subspace_eq_continuous _ _ _ (fun=> i)).
      by move=> ? /set_mem ->.
    by apply: continuous_subspaceT => ?; exact: cvg_cst.
Qed.

Let measurable_almost_continuous' (f : rT -> rT) (eps : rT) :
  (0 < eps)%R -> measurable_fun A f -> exists K,
  [/\ measurable K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps] mf; pose f' := EFin \o f.
have mf' : measurable_fun A f' by exact/measurable_EFinP.
have [/= g_ gf'] := @approximation_sfun _ R rT _ _ mA mf'.
pose e2n n := (eps%:num / 2) / (2 ^ n.+1)%:R.
have e2npos n : (0 < e2n n)%R by rewrite divr_gt0.
have gK' n := @lusin_simple (g_ n) (e2n n) (e2npos n).
pose gK n := projT1 (cid (gK' n)); have gKP n := projT2 (cid (gK' n)).
pose K := \bigcap_i gK i; have mgK n : measurable (gK n).
  by apply: closed_measurable; apply: compact_closed => //; have [] := gKP n.
have mK : measurable K by exact: bigcap_measurable.
have Kab : K `<=` A by move=> z /(_ O I); have [_ + _ _] := gKP O; apply.
have []// := @pointwise_almost_uniform _ rT R mu g_ f K (eps%:num / 2).
- by move=> n; apply: measurable_funTS.
- by rewrite (@le_lt_trans _ _ (mu A))// le_measure// ?inE.
- by move=> z Kz; have /fine_fcvg := gf' z (Kab _ Kz); rewrite -fmap_comp compA.
move=> D [/= mD Deps KDf]; exists (K `\` D); split => //.
- exact: measurableD.
- exact: subset_trans Kab.
- rewrite setDDr; apply: le_lt_trans => /=.
    by apply: measureU2 => //; apply: measurableI => //; apply: measurableC.
  rewrite [_%:num]splitr EFinD; apply: lee_ltD => //=; first 2 last.
  + by rewrite (@le_lt_trans _ _ (mu D)) ?le_measure ?inE//; exact: measurableI.
  + rewrite ge0_fin_numE// (@le_lt_trans _ _ (mu A))// le_measure ?inE//.
    exact: measurableD.
  rewrite setDE setC_bigcap setI_bigcupr.
  apply: (@le_trans _ _(\sum_(k <oo) mu (A `\` gK k))).
  apply: measure_sigma_subadditive => //; [|apply: bigcup_measurable => + _].
      by move=> k /=; apply: measurableD => //; apply: mgK.
    by move=> k /=; apply: measurableD => //; apply: mgK.
  apply: (@le_trans _ _(\sum_(k <oo) (e2n k)%:E)); last exact: epsilon_trick0.
  by apply: lee_nneseries => // k _; apply: ltW; have [] := gKP k.
apply: (@uniform_limit_continuous_subspace _ _ _ (g_ @ \oo)) => //.
near_simpl; apply: nearW => // n; apply: (@continuous_subspaceW _ _ _ (gK n)).
  by move=> z [+ _]; apply.
by have [] := projT2 (cid (gK' n)).
Qed.

Lemma measurable_almost_continuous (f : rT -> rT) (eps : rT) :
  (0 < eps)%R -> measurable_fun A f -> exists K,
  [/\ compact K, K `<=` A, mu (A `\` K) < eps%:E &
  {within K, continuous f}].
Proof.
move: eps=> _/posnumP[eps] mf; have e2pos : (0 < eps%:num/2)%R by [].
have [K [mK KA ? ?]] := measurable_almost_continuous' e2pos mf.
have Kfin : mu K < +oo by rewrite (le_lt_trans _ finA)// le_measure ?inE.
have [D /= [cD DK KDe]] := lebesgue_regularity_inner mK Kfin e2pos.
exists D; split => //; last exact: (continuous_subspaceW DK).
  exact: (subset_trans DK).
have -> : A `\` D = (A `\` K) `|` (K `\` D).
  rewrite eqEsubset; split => z.
    by case: (pselect (K z)) => // ? [? ?]; [right | left].
  case; case=> az nz; split => //; [by move: z nz {az}; apply/subsetC|].
  exact: KA.
apply: le_lt_trans.
  apply: measureU2; apply: measurableD => //; apply: closed_measurable.
  by apply: compact_closed; first exact: Rhausdorff.
by rewrite [_ eps]splitr EFinD lteD.
Qed.

End lusin.

Section emeasurable_fun.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> \bar R).

Import HBSimple.

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
     by move=> n; exact/measurable_EFinP/measurable_funTS/measurable_funD.
  move=> x Dx; under eq_fun do rewrite EFinD.
  exact: cvgeD (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NAnoo: A mD mf mg mA / ~ (A -oo) => [hwlogA|].
  have [] := pselect (A -oo); last exact: hwlogA.
  move=> /(@setD1K _ -oo)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case=>/=].
  have -> : (f \+ g) @^-1` [set -oo] = f @^-1` [set -oo] `|` g @^-1` [set -oo].
     apply/seteqP; split=> x /= => [/eqP|[]]; rewrite /preimage/=.
     - by rewrite adde_eq_ninfty => /orP[] /eqP ->; [left|right].
     - by move=> ->.
     - by move=> ->; rewrite addeC.
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

Lemma emeasurable_sum D I s (h : I -> (T -> \bar R)) :
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
elim: s => [|s t ih] mf.
  by under eq_fun do rewrite big_nil; exact: measurable_cst.
under eq_fun do rewrite big_cons //=; apply: emeasurable_funD => //.
exact: ih.
Qed.

Lemma emeasurable_fsum D (I : choiceType) (A : set I)
    (h : I -> (T -> \bar R)) : finite_set A ->
    (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i \in A) h i x).
Proof.
move=> fs mh; under eq_fun do rewrite fsbig_finite//.
exact: emeasurable_sum.
Qed.

Lemma ge0_emeasurable_sum D (h : nat -> (T -> \bar R)) (P : pred nat) :
    (forall k x, D x -> P k -> 0 <= h k x) ->
    (forall k, P k -> measurable_fun D (h k)) ->
  measurable_fun D (fun x => \sum_(i <oo | i \in P) h i x).
Proof.
move=> h0 mh mD; move: (mD); apply/measurable_restrictT => //.
rewrite [X in measurable_fun _ X](_ : _ =
  (fun x => \sum_(0 <= i <oo | i \in P) (h i \_ D) x)); last first.
  apply/funext => x/=; rewrite /patch; case: ifPn => // xD.
  by rewrite eseries0.
rewrite [X in measurable_fun _ X](_ : _ =
    (fun x => limn_esup (fun n => \sum_(0 <= i < n | P i) (h i) \_ D x))); last first.
  apply/funext=> x; rewrite is_cvg_limn_esupE//.
  apply: is_cvg_nneseries_cond => n _ Pn; rewrite patchE.
  by case: ifPn => // xD; rewrite h0//; exact/set_mem.
apply: measurable_fun_limn_esup => k.
under eq_fun do rewrite big_mkcond.
apply: emeasurable_sum => n.
have [|] := boolP (n \in P); last by rewrite /in_mem/= => /negbTE ->.
rewrite /in_mem/= => Pn; rewrite Pn.
by apply/(measurable_restrictT _ _).1 => //; exact: mh.
Qed.

Lemma emeasurable_funB D f g :
  measurable_fun D f -> measurable_fun D g -> measurable_fun D (f \- g).
Proof.
by move=> mf mg mD; apply: emeasurable_funD => //; exact: measurableT_comp.
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
    move=> n; apply/measurable_EFinP.
    by apply: measurable_funM => //; exact: measurable_funTS.
  move=> x Dx; under eq_fun do rewrite EFinM.
  exact: cvgeM (fg _ _) (f_cvg _ _) (g_cvg _ _).
move=> A mA; wlog NA0: A mD mf mg mA / ~ (A 0) => [hwlogA|].
  have [] := pselect (A 0); last exact: hwlogA.
  move=> /(@setD1K _ 0)<-; rewrite preimage_setU setIUr.
  apply: measurableU; last by apply: hwlogA=> //; [exact: measurableD|case=>/=].
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
Proof. by move=> mf; exact/(emeasurable_funM _ mf). Qed.

End emeasurable_fun.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_sum`")]
Notation emeasurable_fun_sum := emeasurable_sum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `emeasurable_fsum`")]
Notation emeasurable_fun_fsum := emeasurable_fsum (only parsing).
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to `ge0_emeasurable_sum`")]
Notation ge0_emeasurable_fun_sum := ge0_emeasurable_sum (only parsing).

Section emeasurable_fun_cmp.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variables (D : set T) (mD : measurable D).
Implicit Types f g : T -> \bar R.

Lemma emeasurable_fun_lt f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x < g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_gt0.
by apply: emeasurable_fun_o_infty => //; exact: emeasurable_funB.
Qed.

Lemma emeasurable_fun_le f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mf mg; under eq_set do rewrite -sube_le0.
by apply: emeasurable_fun_infty_c => //; exact: emeasurable_funB.
Qed.

Lemma emeasurable_fun_eq f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x = g x]).
Proof.
move=> mf mg; rewrite set_eq_le setIIr.
by apply: measurableI; apply: emeasurable_fun_le.
Qed.

Lemma emeasurable_fun_neq f g : measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x != g x]).
Proof.
move=> mf mg; rewrite set_neq_lt setIUr.
by apply: measurableU; exact: emeasurable_fun_lt.
Qed.

End emeasurable_fun_cmp.

Section measurable_fun.
Context d (T : measurableType d) (R : realType).
Implicit Types (D : set T) (f g : T -> R).

Lemma measurable_sum D I s (h : I -> (T -> R)) :
  (forall n, measurable_fun D (h n)) ->
  measurable_fun D (fun x => \sum_(i <- s) h i x).
Proof.
move=> mh; apply/measurable_EFinP.
rewrite (_ : _ \o _ = (fun t => \sum_(i <- s) (h i t)%:E)); last first.
  by apply/funext => t/=; rewrite -sumEFin.
by apply/emeasurable_sum => i; exact/measurable_EFinP.
Qed.

Lemma measurable_fun_le D f g :
  d.-measurable D -> measurable_fun D f -> measurable_fun D g ->
  measurable (D `&` [set x | f x <= g x]).
Proof.
move=> mD mf mg; under eq_set => x do rewrite -lee_fin.
by apply: emeasurable_fun_le => //; exact: measurableT_comp.
Qed.

End measurable_fun.

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
- exact: emeasurable_sum.
Qed.

End ge0_integral_sum.

Section ge0_integral_fsum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (I : choiceType) (f : I -> (T -> \bar R)).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma ge0_integral_fsum (A : set I) : finite_set A ->
  \int[mu]_(x in D) (\sum_(k \in A) f k x) =
  \sum_(k \in A) \int[mu]_(x in D) f k x.
Proof.
move=> fs; rewrite fsbig_finite//= -ge0_integral_sum//.
by apply: eq_integral => x xD; rewrite fsbig_finite.
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
Let f' := fun x => limn (g'^~ x).

Let g n := (g' n \_ D).

Let g0 n x : 0 <= g n x. Proof. exact/erestrict_ge0/g'0. Qed.

Let mg n : measurable_fun setT (g n).
Proof. exact/(measurable_restrictT _ _).1. Qed.

Let nd_g x : nondecreasing_seq (g^~ x).
Proof.
by move=> m n mn; rewrite /g/patch; case: ifP => // /set_mem /nd_g' ->.
Qed.

Let f := fun x => limn (g^~ x).

Let is_cvg_g t : cvgn (g^~ t).
Proof.
by move=> ?; apply: ereal_nondecreasing_is_cvgn => m n ?; exact/nd_g.
Qed.

Local Definition g2' n : (T -> R)^nat := approx setT (g n).
Local Definition g2 n : {nnsfun T >-> R}^nat := nnsfun_approx measurableT (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : {nnsfun T >-> R}^nat :=
  fun k => bigmax_nnsfun (g2^~ k) k.

Import HBNNSimple.

Let is_cvg_g2 n t : cvgn (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvgn => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Let nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!bigmax_nnsfunE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax2 => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
   by rewrite !nnsfun_approxE; exact/lefP/nd_approx.
rewrite (bigmaxD1 ord_max)// le_max; apply/orP; right.
rewrite [leRHS](eq_bigl (fun i => nat_of_ord i < n)%N).
  by rewrite (big_ord_narrow (leqnSn n)).
move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Let is_cvg_max_g2 t : cvgn (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvgn => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Let max_g2_g k x : ((max_g2 k x)%:E <= g k x)%O.
Proof.
rewrite bigmax_nnsfunE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  by apply/bigmax_leP; split => //; apply: g0D.
rewrite (big_morph _ (@EFin_max R) erefl) //.
apply: le_bigmax2 => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx _ _ _)) => //; exact/nd_g/ltnW.
Qed.

Let lim_max_g2_f t : limn (EFin \o max_g2 ^~ t) <= f t.
Proof. by apply: lee_lim => //=; near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Let lim_g2_max_g2 t n : limn (EFin \o g2 n ^~ t) <= limn (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //.
near=> k; rewrite /= bigmax_nnsfunE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (bigmax_sup (Ordinal nk)).
Unshelve. all: by end_near. Qed.

Let cvg_max_g2_f t : EFin \o max_g2 ^~ t @ \oo --> f t.
Proof.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f _)) // (cvg_lim _ g_l).
have := leey l; rewrite [in X in X -> _]le_eqVlt => /predU1P[->|loo].
  by rewrite leey.
rewrite -(cvg_lim _ g_l) //= lime_le => //.
near=> n.
have := leey (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
  have h := @dvg_approx _ _ _ setT _ t Logic.I fntoo.
  have g2oo : limn (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/cvgeryP.
    under [in X in X --> _]eq_fun do rewrite nnsfun_approxE.
    have : {homo (approx setT (g n))^~ t : n0 m / (n0 <= m)%N >-> (n0 <= m)%R}.
      exact/lef_at/nd_approx.
    by move/nondecreasing_dvgn_lt => /(_ h).
  have -> : limn (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo leye_eq => /eqP.
  by rewrite leey.
- have approx_g_g := @cvg_approx _ _ _ setT _ t (fun t _ => g0 n t) Logic.I fntoo.
  suff : limn (EFin \o g2 n ^~ t) = g n t.
    by move=> <-; exact: (le_trans _ (lim_g2_max_g2 t n)).
  have /cvg_lim <- // : EFin \o (approx setT (g n)) ^~ t @ \oo --> g n t.
    move/cvg_comp : approx_g_g; apply.
    by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
  rewrite (_ : _ \o _ = EFin \o approx setT (g n) ^~ t)// funeqE => m.
  by rewrite [in RHS]/= -nnsfun_approxE.
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int[mu]_(x in D) (f' x) = limn (fun n => \int[mu]_(x in D) (g' n x)).
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
    - move=> x _; apply: lime_ge => //.
      by apply: nearW => k; exact/g0.
    - apply: emeasurable_fun_cvg mg _ => x _.
      exact: ereal_nondecreasing_is_cvgn.
    - move=> x Dx; apply: lime_ge => //.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: lime_le => //; [exact:ereal_nondecreasing_is_cvgn|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ _ mu _ max_g2) //; last 2 first.
  - move=> t; apply: lime_ge => //.
    by apply: nearW => n; exact: g0.
  - by move=> t m n mn; exact/lefP/nd_max_g2.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvgn => // n m nm; apply: ge0_le_integral => //.
  by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralTE//.
  by apply: ereal_sup_ubound; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  \int[mu]_(x in D) g' n x @[n \oo] --> \int[mu]_(x in D) f' x.
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvgn => m n mn.
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
- by rewrite -lim_mkord; under eq_fun do rewrite ge0_integral_sum// big_mkord.
- by move=> n; exact: emeasurable_sum.
- by move=> n x Dx; apply: sume_ge0 => m _; exact: f0.
- by move=> x Dx m n mn; apply: lee_sum_nneg_natr => // k _ _; exact: f0.
Qed.

End integral_nneseries.

(**md Generalization of `ge0_integralZl_EFin` to a constant potentially $+\infty$
   using the monotone convergence theorem: *)
Section ge0_integralZ.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f : T -> \bar R).
Hypothesis mf : measurable_fun D f.
Implicit Type k : \bar R.

Lemma ge0_integralZl k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (k * f x) = k * \int[mu]_(x in D) (f x).
Proof.
move=> f0; move: k => [k|_|//]; first exact: ge0_integralZl_EFin.
pose g : (T -> \bar R)^nat := fun n x => n%:R%:E * f x.
have mg n : measurable_fun D (g n) by apply: measurable_funeM.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: mule_ge0; [rewrite lee_fin|exact:f0].
have nd_g x : D x -> nondecreasing_seq (g ^~ x).
  by move=> Dx m n mn; rewrite lee_wpmul2r ?f0// lee_fin ler_nat.
pose h := fun x => limn (g^~ x).
transitivity (\int[mu]_(x in D) limn (g^~ x)).
  apply: eq_integral => x Dx; apply/esym/cvg_lim => //.
  have [fx0|fx0|fx0] := ltgtP 0 (f x).
  - rewrite gt0_mulye//; apply/cvgeyPgey; near=> M.
    have M0 : (0 <= M)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|_|//]; last first.
      by exists 1%N => // m /= m0; rewrite mulry gtr0_sg// ?ltr0n// mul1e leey.
    near=> n; rewrite lee_fin -ler_pdivrMr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    rewrite natr_absz ger0_norm ?ceil_ge//.
    by rewrite -(ceil0 R) ceil_le// divr_ge0// ltW.
  - rewrite lt0_mulye//; apply/cvgeNyPleNy; near=> M;
    have M0 : (M <= 0)%R by [].
    rewrite /g; case: (f x) fx0 => [r r0|//|_]; last first.
      by exists 1%N => // m /= m0; rewrite mulrNy gtr0_sg// ?ltr0n// mul1e leNye.
    near=> n; rewrite lee_fin -ler_ndivrMr//.
    near: n; exists `|ceil (M / r)|%N => // m /=.
    rewrite -(ler_nat R); apply: le_trans.
    by rewrite pmulrn abszE ceil_ge_int ler_norm.
  - rewrite -fx0 mule0 /g -fx0.
    under eq_fun do rewrite mule0/=. (*TODO: notation broken*)
    exact: cvg_cst.
rewrite (monotone_convergence mu mD mg g0 nd_g).
under eq_fun do rewrite /g ge0_integralZl_EFin//.
have : 0 <= \int[mu]_(x in D) f x by exact: integral_ge0.
rewrite le_eqVlt => /predU1P[<-|if_gt0].
  by rewrite mule0; under eq_fun do rewrite mule0; rewrite lim_cst.
rewrite gt0_mulye//; apply/cvg_lim => //; apply/cvgeyPgey; near=> M.
have M0 : (0 <= M)%R by [].
near=> n; have [ifoo|] := ltP (\int[mu]_(x in D) f x) +oo; last first.
  rewrite leye_eq => /eqP ->; rewrite mulry muleC gt0_mulye ?leey//.
  by near: n; exists 1%N => // n /= n0; rewrite gtr0_sg// ?lte_fin// ltr0n.
rewrite -(@fineK _ (\int[mu]_(x in D) f x)); last first.
  by rewrite fin_numElt ifoo (le_lt_trans _ if_gt0).
rewrite -lee_pdivrMr//; last first.
  by move: if_gt0 ifoo; case: (\int[mu]_(x in D) f x).
near: n.
exists `|ceil (M * (fine (\int[mu]_(x in D) f x))^-1)|%N => //.
move=> n /=; rewrite -(@ler_nat R) -lee_fin; apply: le_trans.
rewrite lee_fin natr_absz ger0_norm ?ceil_ge//.
by rewrite -(ceil0 R) ceil_le// divr_ge0//; exact/fine_ge0/integral_ge0.
Unshelve. all: by end_near. Qed.

Lemma ge0_integralZr k : (forall x, D x -> 0 <= f x) ->
  0 <= k -> \int[mu]_(x in D) (f x * k) = \int[mu]_(x in D) (f x) * k.
Proof.
move=> f0 k0; under eq_integral do rewrite muleC.
by rewrite ge0_integralZl// muleC.
Qed.

End ge0_integralZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `ge0_integralZl` instead")]
Notation ge0_integralM := ge0_integralZl (only parsing).

Section integral_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Implicit Type A : set T.

Import HBNNSimple.

Lemma integral_indic A : measurable A ->
  \int[mu]_(x in D) (\1_A x)%:E = mu (A `&` D).
Proof.
move=> mA; rewrite (_ : \1_A = indic_nnsfun R mA)// integral_nnsfun//=.
by rewrite restrict_indic sintegral_indic//; exact: measurableI.
Qed.

End integral_indic.

Section integralZl_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralZl_indic (f : R -> set T) (k : R) :
    ((k < 0)%R -> f k = set0) -> measurable (f k) ->
  \int[m]_(x in D) (k * \1_(f k) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f k) x)%:E.
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite integral0_eq//; last by move=> x _; rewrite fk0// indic0 mulr0.
  by rewrite integral0_eq ?mule0// => x _; rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl//; first exact/measurable_EFinP.
by move=> y _; rewrite lee_fin.
Qed.

Import HBNNSimple.

Lemma integralZl_indic_nnsfun (f : {nnsfun T >-> R}) (k : R) :
  \int[m]_(x in D) (k * \1_(f @^-1` [set k]) x)%:E =
  k%:E * \int[m]_(x in D) (\1_(f @^-1` [set k]) x)%:E.
Proof.
rewrite (@integralZl_indic (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

End integralZl_indic.
Arguments integralZl_indic {d T R m D} mD f.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl_indic` instead")]
Notation integralM_indic := integralZl_indic (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl_indic_nnsfun` instead")]
Notation integralM_indic_nnsfun := integralZl_indic_nnsfun (only parsing).

Section integral_mscale.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (k : {nonneg R}) (f : T -> \bar R).

Let integral_mscale_indic E : measurable E ->
  \int[mscale k m]_(x in D) (\1_E x)%:E =
  k%:num%:E * \int[m]_(x in D) (\1_E x)%:E.
Proof. by move=> ?; rewrite !integral_indic. Qed.

Import HBNNSimple.

Let integral_mscale_nnsfun (h : {nnsfun T >-> R}) :
  \int[mscale k m]_(x in D) (h x)%:E = k%:num%:E * \int[m]_(x in D) (h x)%:E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralZl//; last 2 first.
  - by apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> x _; rewrite lee_fin.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/measurable_EFinP; do 2 apply/measurableT_comp => //.
  - by move=> n x _; rewrite EFinM mule_ge0// nnfun_muleindic_ge0.
apply: eq_fsbigr => r _; rewrite ge0_integralZl//.
- by rewrite !integralZl_indic_nnsfun//= integral_mscale_indic// muleCA.
- exact/measurable_EFinP/measurableT_comp.
- by move=> t _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma ge0_integral_mscale (mf : measurable_fun D f) :
    (forall x, D x -> 0 <= f x) ->
  \int[mscale k m]_(x in D) f x = k%:num%:E * \int[m]_(x in D) f x.
Proof.
move=> f0; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[mscale k m]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //=; exact: cvg_nnsfun_approx.
  - by move=> n; apply: measurableT_comp => //; exact: measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite (_ : \int[m]_(x in D) _ =
    limn (fun n => \int[m]_(x in D) (f_ n x)%:E)); last first.
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => x /[!inE] xD; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  - by move=> n; exact/measurable_EFinP/measurable_funTS.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ a b ab; rewrite lee_fin//; exact/lefP/nd_nnsfun_approx.
rewrite -limeMl//.
  by congr (limn _); apply/funext => n /=; rewrite integral_mscale_nnsfun.
apply/ereal_nondecreasing_is_cvgn => a b ab; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP/measurable_funTS.
- by move=> x _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

End integral_mscale.

Section fatou.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : (T -> \bar R)^nat).
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int[mu]_(x in D) limn_einf (f^~ x) <=
              limn_einf (fun n => \int[mu]_(x in D) f n x).
Proof.
pose g n := fun x => einfs (f ^~ x) n.
have mg := measurable_fun_einfs mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: lb_ereal_inf => _ [m /= nm <-]; exact: f0.
under eq_integral do rewrite limn_einf_lim.
rewrite limn_einf_lim monotone_convergence //; last first.
  move=> x Dx m n mn /=; apply: le_ereal_inf => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: ge0_le_integral => //; [exact: g0| exact: mg| exact: g0| exact: mg|].
  move=> x Dx; apply: le_ereal_inf => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: le_ereal_inf => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N ->
      \int[mu]_(x in D) g n x <= einfs (fun k => \int[mu]_(x in D) f k x) n.
    move=> n p np; apply: lb_ereal_inf => /= _ [k /= nk <-].
    apply: ge0_le_integral => //; [exact: g0|exact: mg|exact: f0|].
    by move=> x Dx; apply: ereal_inf_lbound; exists k.
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
  rewrite integralE// [in RHS]integralE// fin_num_oppeD ?fin_numN// oppeK addeC.
  by rewrite funenegN funeposN.
rewrite fin_numE negb_and 2!negbK => /orP[nfoo|/eqP nfoo].
  exfalso; move/negP : nfoo; apply; rewrite -leeNy_eq; apply/negP.
  by rewrite -ltNge (lt_le_trans _ (integral_ge0 _ _)).
rewrite nfoo adde_defEninfty -leye_eq -ltNge ltey_eq => /orP[f_fin|/eqP pfoo].
  rewrite integralE [in RHS]integralE funeposN nfoo [in RHS]addeC/= funenegN.
  by rewrite addye// eqe_oppLR/= (andP (eqbLR (fin_numE _) f_fin)).2.
by rewrite integralE// [in RHS]integralE// funeposN funenegN nfoo pfoo.
Qed.

Lemma integral_ge0N (D : set T) (f : T -> \bar R) :
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) - f x = - \int[mu]_(x in D) f x.
Proof.
move=> f0; rewrite integralN // (eq_integral _ _ (ge0_funenegE _))// integral0.
by rewrite oppe0 fin_num_adde_defl.
Qed.

End integralN.

Section integral_cst.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).
Variables (f : T -> \bar R) (D : set T) (mD : measurable D).

Lemma sintegral_EFin_cst (x : {nonneg R}) :
  sintegral mu (cst x%:num \_ D) = x%:num%:E * mu D.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; x%:num])/=.
- have [->|x0] := eqVneq x%:num 0%R; first by rewrite setUid fsbig_set1 !mul0e.
  rewrite fsbigU0//=; last by move=> y [->]/esym; apply/eqP.
  rewrite !fsbig_set1 mul0e add0e preimage_restrict//.
  by rewrite ifN ?set0U ?setIidl//= notin_setE => /esym; exact/eqP.
- by move=> y [t _ <-] /=; rewrite /patch; case: ifPn; [right|left].
- by move=> y [_ /=/preimage10->]; rewrite measure0 mule0.
Qed.

Import HBNNSimple.

Local Lemma integral_cstr r : \int[mu]_(x in D) r%:E = r%:E * mu D.
Proof.
wlog r0 : r / (0 <= r)%R.
  move=> h; have [|r0] := leP 0%R r; first exact: h.
  rewrite -[in RHS](opprK r) EFinN mulNe -h ?oppr_ge0; last exact: ltW.
  rewrite -integral_ge0N//; last by move=> t ?; rewrite /= lee_fin oppr_ge0 ltW.
  by under [RHS]eq_integral do rewrite /= opprK.
rewrite (eq_integral (EFin \o cst_nnsfun T (NngNum r0)))//.
by rewrite integral_nnsfun// sintegral_EFin_cst.
Qed.

Local Lemma integral_csty : mu D != 0 -> \int[mu]_(x in D) (cst +oo) x = +oo.
Proof.
move=> muD0; pose g : (T -> \bar R)^nat := fun n => cst n%:R%:E.
have <- : (fun t => limn (g^~ t)) = cst +oo.
  rewrite funeqE => t; apply/cvg_lim => //=.
  apply/cvgeryP/cvgryPge => M; exists `|ceil M|%N => //= m.
  by rewrite /= pmulrn ceil_ge_int// -lez_nat abszE; apply/le_trans/ler_norm.
rewrite monotone_convergence //.
- under [in LHS]eq_fun do rewrite integral_cstr.
  apply/cvg_lim => //; apply/cvgeyPge => M.
  have [muDoo|muDoo] := ltP (mu D) +oo; last first.
    exists 1%N => // m /= m0; move: muDoo; rewrite leye_eq => /eqP ->.
    by rewrite mulry gtr0_sg ?mul1e ?leey// ltr0n.
  exists `|ceil (M / fine (mu D))|%N => // m /=.
  rewrite -lez_nat abszE => MDm; rewrite -(@fineK _ (mu D)) ?ge0_fin_numE//.
  rewrite -lee_pdivrMr; last by rewrite fine_gt0// lt0e muD0 measure_ge0.
  by rewrite lee_fin pmulrn ceil_ge_int// (le_trans _ MDm)// ler_norm.
- by move=> n; exact: measurable_cst.
- by move=> n x Dx; rewrite lee_fin.
- by move=> t Dt n m nm; rewrite /g lee_fin ler_nat.
Qed.

Local Lemma integral_cstNy : mu D != 0 -> \int[mu]_(x in D) (cst -oo) x = -oo.
Proof.
by move=> ?; rewrite (eq_integral (\- cst +oo)) ?integral_ge0N/= ?integral_csty.
Qed.

End integral_cst.

Section ge0_transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (phi : X -> Y) (mphi : measurable_fun setT phi).
Variables (mu : {measure set X -> \bar R}).
Let mphi_mixin := isMeasurableFun.Build _ _ _ _ _ mphi.
Let mphi_pack : {mfun _ >-> _} := HB.pack phi mphi_mixin.

Import HBNNSimple.

Lemma ge0_integral_pushforward D (f : Y -> \bar R) :
  measurable D -> measurable_fun D f -> {in D, forall y, 0 <= f y} ->
  \int[pushforward mu mphi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD mf f0.
have mphiD : measurable (phi @^-1` D).
  by rewrite -(setTI (_ @^-1` _)); exact: (measurable_funP mphi_pack).
pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[pushforward mu mphi]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - apply: eq_integral => y /[!inE] yD; apply/esym/cvg_lim => //.
    by apply: cvg_nnsfun_approx=> // *; apply: f0; rewrite inE.
  - by move=> n; apply/measurable_EFinP; exact: measurable_funP.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite [X in limn X](_ : _ =
    (fun n => \int[mu]_(x in phi @^-1` D) (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; do 2 apply: measurableT_comp=> //.
      exact: (measurable_funP mphi_pack).
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  apply: eq_integral => x /[!inE] phiDx /=; apply/cvg_lim => //.
  by apply: cvg_nnsfun_approx=> // y Dy; apply: f0; rewrite inE.
apply/funext => n.
have mfnphi r : measurable (f_ n @^-1` [set r] \o phi).
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k \in range (f_ n))
    \int[mu]_(x in phi @^-1` D) (k * \1_((f_ n @^-1` [set k]) \o phi) x)%:E).
  under eq_integral do rewrite fimfunE -fsumEFin//.
  rewrite ge0_integral_fsum//; last 2 first.
    - by move=> y; apply/measurable_EFinP; exact: measurable_funM.
    - by move=> y x _; rewrite nnfun_muleindic_ge0.
  apply: eq_fsbigr => r _; rewrite integralZl_indic_nnsfun// integral_indic//=.
  rewrite (integralZl_indic _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _); rewrite [RHS]integral_indic.
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/measurable_EFinP; exact: measurable_funM.
  - by move=> r x _; rewrite nnfun_muleindic_ge0.
by apply: eq_integral => x _; rewrite fsumEFin// -fimfunE.
Qed.

End ge0_transfer.

Section integral_dirac.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (a : T) (R : realType).
Variables (D : set T) (mD : measurable D).

Import HBNNSimple.

Let ge0_integral_dirac (f : T -> \bar R) (mf : measurable_fun D f)
    (f0 : forall x, D x -> 0 <= f x) :
  D a -> \int[\d_a]_(x in D) (f x) = f a.
Proof.
move=> Da; pose f_ := nnsfun_approx mD mf.
transitivity (limn (fun n => \int[\d_ a]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => x /set_mem Dx; apply/esym/cvg_lim => //; apply: cvg_nnsfun_approx.
  - by move=> n; apply/measurable_EFinP; exact/measurable_funTS.
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
apply/funext => n.
under eq_integral do rewrite fimfunE// -fsumEFin//.
rewrite ge0_integral_fsum//.
- under eq_fsbigr do rewrite integralZl_indic_nnsfun//.
  rewrite /= (fsbigD1 (f_ n a))//=; last by exists a.
  rewrite integral_indic//= diracE mem_set// mule1.
  rewrite fsbig1 ?adde0// => r /= [_ rfna].
  rewrite integral_indic//= diracE memNset ?mule0//=.
  by apply/not_andP; left; exact/nesym.
- by move=> r; exact/measurable_EFinP/measurableT_comp.
- by move=> r x _; rewrite nnfun_muleindic_ge0.
Qed.

Lemma integral_dirac (f : T -> \bar R) (mf : measurable_fun D f) :
  \int[\d_ a]_(x in D) f x = \d_a D * f a.
Proof.
have [/[!inE] aD|aD] := boolP (a \in D).
  rewrite integralE ge0_integral_dirac//; last exact/measurable_funepos.
  rewrite ge0_integral_dirac//; last exact/measurable_funeneg.
  by rewrite [in RHS](funeposneg f) diracE mem_set// mul1e.
rewrite diracE (negbTE aD) mul0e -(integral_measure_zero D f)//.
apply: eq_measure_integral => //= S mS DS; rewrite /dirac indicE memNset//.
by move=> /DS/mem_set; exact/negP.
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
rewrite integral_indic//= /msum/=; apply: eq_bigr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Let integralT_measure_sum (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n < N) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n < N) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_sum_indic//.
  by rewrite ge0_sume_distrr// => n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= exchange_big/=; apply: eq_bigr => i _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
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
rewrite integralT_measure_sum; apply: eq_bigr => i _.
rewrite [RHS]integral_mkcond; apply: eq_integral => t _.
rewrite /= /patch /mindic indicE.
by case: (boolP (t \in D)) => tD; rewrite ?mulr1 ?mulr0.
Qed.

End integral_measure_sum_nnsfun.

Section integral_measure_add_nnsfun.
Import HBNNSimple.

Lemma integral_measure_add_nnsfun d (T : measurableType d) (R : realType)
    (m1 m2 : {measure set T -> \bar R}) (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  (\int[measure_add m1 m2]_(x in D) (f x)%:E =
   \int[m1]_(x in D) (f x)%:E + \int[m2]_(x in D) (f x)%:E)%E.
Proof.
rewrite /measureD integral_measure_sum_nnsfun// 2!big_ord_recl/= big_ord0.
by rewrite adde0.
Qed.

End integral_measure_add_nnsfun.

Section integral_mfun_measure_sum.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.

Import HBNNSimple.

Lemma ge0_integral_measure_sum (D : set T) (mD : measurable D)
    (f : T -> \bar R) :
    (forall x, D x -> 0 <= f x) -> measurable_fun D f -> forall N,
  \int[msum m_ N]_(x in D) f x = \sum_(n < N) \int[m_ n]_(x in D) f x.
Proof.
move=> f0 mf; pose f_ := nnsfun_approx mD mf.
elim => [|N ih]; first by rewrite big_ord0 msum_mzero integral_measure_zero.
rewrite big_ord_recr/= -ih.
rewrite (_ : _ m_ N.+1 = measure_add (msum m_ N) (m_ N)); last first.
  by apply/funext => A; rewrite measure_addE /msum/= big_ord_recr.
have mf_ n : measurable_fun D (fun x => (f_ n x)%:E).
  exact/measurable_funTS/measurable_EFinP.
have f_ge0 n x : D x -> 0 <= (f_ n x)%:E by move=> Dx; rewrite lee_fin.
have cvg_f_ (m : {measure set T -> \bar R}) :
    cvgn (fun x => \int[m]_(x0 in D) (f_ x x0)%:E).
  apply: ereal_nondecreasing_is_cvgn => a b ab.
  apply: ge0_le_integral => //; [exact: f_ge0|exact: f_ge0|].
  by move=> t Dt; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n =>
    \int[measure_add (msum m_ N) (m_ N)]_(x in D) (f_ n x)%:E)).
  rewrite -monotone_convergence//; last first.
    by move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => t /[!inE] Dt; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n =>
  \int[msum m_ N]_(x in D) (f_ n x)%:E + \int[m_ N]_(x in D) (f_ n x)%:E)).
  by congr (limn _); apply/funext => n; by rewrite integral_measure_add_nnsfun.
rewrite limeD//; do?[exact: cvg_f_]; last first.
  by apply: ge0_adde_def; rewrite inE; apply: lime_ge => //; do?[exact: cvg_f_];
      apply: nearW => n;  apply: integral_ge0 => //; exact: f_ge0.
by congr (_ + _); (rewrite -monotone_convergence//; [
    apply: eq_integral => t /[!inE] Dt; apply/cvg_lim => //; exact: cvg_nnsfun_approx |
    move=> t Dt a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx]).
Qed.

End integral_mfun_measure_sum.

Lemma ge0_integral_measure_add d (T : measurableType d) (R : realType)
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
rewrite integral_indic// setIT /m/= /mseries; apply: eq_eseriesr => i _.
by rewrite integral_indic// setIT.
Qed.

Import HBNNSimple.

Lemma integral_measure_series_nnsfun (D : set T) (mD : measurable D)
    (f : {nnsfun T >-> R}) :
  \int[m]_x (f x)%:E = \sum_(n <oo) \int[m_ n]_x (f x)%:E.
Proof.
under eq_integral do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum//; last 2 first.
  - by move=> r /=; apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> r t _; rewrite EFinM nnfun_muleindic_ge0.
transitivity (\sum_(i \in range f)
    (\sum_(n <oo) i%:E * \int[m_ n]_x (\1_(f @^-1` [set i]) x)%:E)).
  apply: eq_fsbigr => r _.
  rewrite integralZl_indic_nnsfun// integral_measure_series_indic// nneseriesZl//.
  by move=> n _; apply: integral_ge0 => t _; rewrite lee_fin.
rewrite fsbig_finite//= -nneseries_sum; last first.
  move=> r j _.
  have [r0|r0] := leP 0%R r.
    by rewrite mule_ge0//; apply: integral_ge0 => // t _; rewrite lee_fin.
  rewrite integral0_eq ?mule0// => x _.
  by rewrite preimage_nnfun0// indicE in_set0.
apply: eq_eseriesr => k _.
rewrite integralT_nnsfun sintegralE fsbig_finite//=; apply: eq_bigr => r _.
by congr (_ * _); rewrite integral_indic// setIT.
Qed.

End integral_measure_series.

Section ge0_integral_measure_series.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m_ : {measure set T -> \bar R}^nat.
Let m := mseries m_ O.

Import HBNNSimple.

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
  rewrite [X in _ <= X](_ : _ = \sum_(k < n) \int[m_ k]_(x in D) f x +
                                \int[mseries m_ n]_(x in D) f x); last first.
    transitivity (\int[measure_add (msum m_ n) (mseries m_ n)]_(x in D) f x).
      congr (\int[_]_(_ in D) _); apply/funext => A.
      rewrite measure_addE/= /msum -(big_mkord xpredT (m_ ^~ A)).
      exact: nneseries_split.
    by rewrite ge0_integral_measure_add// -ge0_integral_measure_sum.
  by apply: leeDl; exact: integral_ge0.
rewrite ge0_integralE//=; apply: ub_ereal_sup => /= _ [g /= gf] <-.
rewrite -integralT_nnsfun (integral_measure_series_nnsfun _ mD).
apply: lee_nneseries => [n _ _|n _].
  by apply: integral_ge0 => // x _; rewrite lee_fin.
rewrite [leRHS]integral_mkcond; apply: ge0_le_integral => //.
- by move=> x _; rewrite lee_fin.
- exact/measurable_EFinP.
- by move=> x _; rewrite erestrict_ge0.
- exact/(measurable_restrictT _ mD).
Qed.

End ge0_integral_measure_series.

Section subset_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma ge0_integral_setU (A B : set T) (mA : measurable A) (mB : measurable B)
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
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
  - by move=> x _; apply: erestrict_ge0 => y By; apply: f0; right.
  - apply/measurable_restrict => //; first exact: measurableU.
    apply: measurable_funS mf; [exact: measurableU|exact: subIsetl].
by rewrite -integral_mkcondl setIC setUK -integral_mkcondl setKU.
Qed.

Lemma ge0_subset_integral (A B : set T) (mA : measurable A) (mB : measurable B)
    (f : T -> \bar R) : measurable_fun B f -> (forall x, B x -> 0 <= f x) ->
  A `<=` B -> \int[mu]_(x in A) f x <= \int[mu]_(x in B) f x.
Proof.
move=> mf f0 AB; rewrite -(setDUK AB) ge0_integral_setU//; last 4 first.
  - exact: measurableD.
  - by rewrite setDUK.
  - by move=> x; rewrite setDUK//; exact: f0.
  - by rewrite disj_set2E setDIK.
by apply: leeDl; apply: integral_ge0 => x [Bx _]; exact: f0.
Qed.

Lemma ge0_integral_bigsetU (I : eqType) (F : I -> set T) (f : T -> \bar R)
    (s : seq I) : (forall n, measurable (F n)) -> uniq s ->
  trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  \int[mu]_(x in D) f x = \sum_(i <- s) \int[mu]_(x in F i) f x.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf f0.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons ge0_integral_setU//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
  + by move=> x UFx; apply: f0; rewrite /D big_cons; right.
- exact: bigsetU_measurable.
- by move: mf; rewrite /D big_cons.
- by move: f0; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

Lemma le_integral_abse (D : set T) (mD : measurable D) (g : T -> \bar R) a :
  measurable_fun D g -> (0 < a)%R ->
  a%:E * mu (D `&` [set x | `|g x| >= a%:E]) <= \int[mu]_(x in D) `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | a%:E <= `|g x|]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) `|g x|)).
  rewrite -integral_cstr//; apply: ge0_le_integral => //.
  - by move=> x _ /=; exact/ltW.
  - by apply: measurableT_comp => //; exact: measurable_funS mg.
  - by move=> x /= [].
by apply: ge0_subset_integral => //; exact: measurableT_comp.
Qed.

End subset_integral.
#[deprecated(since="mathcomp-analysis 1.0.1", note="use `ge0_integral_setU` instead")]
Notation integral_setU := ge0_integral_setU (only parsing).

Section integral_setU_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma integral_setU_EFin (A B : set T) (f : T -> R) :
  measurable A -> measurable B ->
  measurable_fun (A `|` B) f ->
  [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) (f x)%:E = \int[mu]_(x in A) (f x)%:E +
                                       \int[mu]_(x in B) (f x)%:E.
Proof.
move=> mA mB ABf AB.
rewrite integralE/=.
rewrite ge0_integral_setU//; last exact/measurable_funepos/measurable_EFinP.
rewrite ge0_integral_setU//; last exact/measurable_funeneg/measurable_EFinP.
rewrite [X in _ = X + _]integralE/=.
rewrite [X in _ = _ + X]integralE/=.
set ap : \bar R := \int[mu]_(x in A) _; set an : \bar R := \int[mu]_(x in A) _.
set bp : \bar R := \int[mu]_(x in B) _; set bn : \bar R := \int[mu]_(x in B) _.
rewrite oppeD 1?addeACA//.
by rewrite ge0_adde_def// inE integral_ge0.
Qed.

Lemma integral_bigsetU_EFin (I : eqType) (F : I -> set T) (f : T -> R)
    (s : seq I) :
  (forall i, d.-measurable (F i)) ->
  uniq s -> trivIset [set` s] F ->
  let D := \big[setU/set0]_(i <- s) F i in
  measurable_fun D (EFin \o f) ->
  \int[mu]_(x in D) (f x)%:E = \sum_(i <- s) \int[mu]_(x in F i) (f x)%:E.
Proof.
move=> mF; elim: s => [|h t ih] us tF D mf.
  by rewrite /D 2!big_nil integral_set0.
rewrite /D big_cons integral_setU_EFin//.
- rewrite big_cons ih//.
  + by move: us => /= /andP[].
  + by apply: sub_trivIset tF => /= i /= it; rewrite inE it orbT.
  + apply: measurable_funS mf => //; first exact: bigsetU_measurable.
    by rewrite /D big_cons; exact: subsetUr.
- exact: bigsetU_measurable.
- by move/measurable_EFinP : mf; rewrite /D big_cons.
- apply/eqP; rewrite big_distrr/= big_seq big1// => i it.
  move/trivIsetP : tF; apply => //=; rewrite ?mem_head//.
  + by rewrite inE it orbT.
  + by apply/eqP => hi; move: us => /=; rewrite hi it.
Qed.

End integral_setU_EFin.

Section Rintegral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Definition Rintegral (D : set T) (f : T -> R) :=
  fine (\int[mu]_(x in D) (f x)%:E).

End Rintegral.

Notation "\int [ mu ]_ ( x 'in' D ) f" :=
  (Rintegral mu D (fun x => f)%R) : ring_scope.
Notation "\int [ mu ]_ x f" :=
  (Rintegral mu setT (fun x => f)%R) : ring_scope.

HB.lock Definition integrable {d} {T : measurableType d} {R : realType}
    (mu : set T -> \bar R) D f :=
  `[< measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E >].
Canonical integrable_unlockable := Unlockable integrable.unlock.

Lemma integrableP d T R mu D f :
  reflect (measurable_fun D f /\ (\int[mu]_(x in D) `|f x| < +oo)%E)
    (@integrable d T R mu D f).
Proof. by rewrite unlock; apply/(iffP (asboolP _)). Qed.

Lemma measurable_int d T R mu D f :
  @integrable d T R mu D f -> measurable_fun D f.
Proof. by rewrite unlock => /asboolP[]. Qed.
Arguments measurable_int {d T R} mu {D f}.

Section integrable_theory.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D).
Implicit Type f g : T -> \bar R.

Notation mu_int := (integrable mu D).

Lemma integrable0 : mu_int (cst 0).
Proof.
apply/integrableP; split=> //; under eq_integral do rewrite (gee0_abs (lexx 0)).
by rewrite integral0.
Qed.

Lemma eq_integrable f g : {in D, f =1 g} -> mu_int f -> mu_int g.
Proof.
move=> fg /integrableP[mf fi]; apply/integrableP; split.
  exact: eq_measurable_fun mf.
rewrite (le_lt_trans _ fi)//; apply: ge0_le_integral=> //.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
  by apply: measurableT_comp => //; exact: eq_measurable_fun mf.
by move=> x Dx; rewrite fg// inE.
Qed.

Lemma le_integrable f g : measurable_fun D f ->
  (forall x, D x -> `|f x| <= `|g x|) -> mu_int g -> mu_int f.
Proof.
move=> mf fg /integrableP[mfg goo]; apply/integrableP; split => //.
by apply: le_lt_trans goo; apply: ge0_le_integral => //; exact: measurableT_comp.
Qed.

Lemma integrableN f : mu_int f -> mu_int (-%E \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split; last first.
  by rewrite /comp; under eq_fun do rewrite abseN.
by rewrite /comp; exact: measurableT_comp.
Qed.

Lemma integrableZl (k : R) f : mu_int f -> mu_int (fun x => k%:E * f x).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurable_funeM.
under eq_fun do rewrite abseM.
by rewrite ge0_integralZl// ?lte_mul_pinfty//; exact: measurableT_comp.
Qed.

Lemma integrableZr (k : R) f : mu_int f -> mu_int (f \* cst k%:E).
Proof.
by move=> mf; apply: eq_integrable (integrableZl k mf) => // x; rewrite muleC.
Qed.

Lemma integrableD f g : mu_int f -> mu_int g -> mu_int (f \+ g).
Proof.
move=> /integrableP[mf foo] /integrableP[mg goo]; apply/integrableP; split.
  exact: emeasurable_funD.
apply: (@le_lt_trans _ _ (\int[mu]_(x in D) (`|f x| + `|g x|))).
  apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; exact: emeasurable_funD.
  - by move=> ? ?; apply: adde_ge0.
  - by apply: emeasurable_funD; apply: measurableT_comp.
  - by move=> *; exact: lee_abs_add.
by rewrite ge0_integralD //; [exact: lte_add_pinfty|
  exact: measurableT_comp|exact: measurableT_comp].
Qed.

Lemma integrable_sum (s : seq (T -> \bar R)) :
  (forall h, h \in s -> mu_int h) -> mu_int (fun x => \sum_(h <- s) h x).
Proof.
elim: s => [_|h s ih hs].
  by under eq_fun do rewrite big_nil; exact: integrable0.
under eq_fun do rewrite big_cons; apply: integrableD => //.
- by apply: hs; rewrite in_cons eqxx.
- by apply: ih => k ks; apply: hs; rewrite in_cons ks orbT.
Qed.

Lemma integrableB f g : mu_int f -> mu_int g -> mu_int (f \- g).
Proof. by move=> fi gi; exact/(integrableD fi)/integrableN. Qed.

Lemma integrable_add_def f : mu_int f ->
  \int[mu]_(x in D) f^\+ x +? - \int[mu]_(x in D) f^\- x.
Proof.
move=> /integrableP[mf]; rewrite -[fun x => _]/(abse \o f) fune_abse => foo.
rewrite ge0_integralD // in foo; last 2 first.
- exact: measurable_funepos.
- exact: measurable_funeneg.
apply: ltpinfty_adde_def.
- by apply: le_lt_trans foo; rewrite leeDl// integral_ge0.
- by rewrite inE (@le_lt_trans _ _ 0)// leeNl oppe0 integral_ge0.
Qed.

Lemma integrable_funepos f : mu_int f -> mu_int f^\+.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funepos.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funepos.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDl.
Qed.

Lemma integrable_funeneg f : mu_int f -> mu_int f^\-.
Proof.
move=> /integrableP[Df foo]; apply/integrableP; split.
  exact: measurable_funeneg.
apply: le_lt_trans foo; apply: ge0_le_integral => //.
- by apply/measurableT_comp => //; exact: measurable_funeneg.
- exact/measurableT_comp.
- by move=> t Dt; rewrite -/((abse \o f) t) fune_abse gee0_abs// leeDr.
Qed.

Lemma integral_funeneg_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\- x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funeneg.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funenegE.
    by move: fx0; rewrite -{1}oppe0 -leeNr => /max_idPl ->.
  rewrite gee0_abs// funenegE.
  by move: (fx0); rewrite -{1}oppe0 -leeNl => /max_idPr ->.
Qed.

Lemma integral_funepos_lt_pinfty f : mu_int f ->
  \int[mu]_(x in D) f^\+ x < +oo.
Proof.
move=> /integrableP[mf]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurable_funepos.
- exact: measurableT_comp.
- move=> x Dx; have [fx0|/ltW fx0] := leP (f x) 0.
    rewrite lee0_abs// funeposE.
    by move: (fx0) => /max_idPr ->; rewrite -leeNr oppe0.
  by rewrite gee0_abs// funeposE; move: (fx0) => /max_idPl ->.
Qed.

Lemma integrable_neg_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\- x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funeneg.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDr.
Qed.

Lemma integrable_pos_fin_num f :
  mu_int f -> \int[mu]_(x in D) f^\+ x \is a fin_num.
Proof.
move=> /integrableP fi.
rewrite fin_numElt; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0) ?lte_ninfty//; exact: integral_ge0.
case: fi => mf; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact/measurable_funepos.
- exact/measurableT_comp.
- by move=> x Dx; rewrite -/((abse \o f) x) (fune_abse f) leeDl.
Qed.

Lemma integrableMr (h : T -> R) g :
  measurable_fun D h -> [bounded h x | x in D] ->
  mu_int g -> mu_int ((EFin \o h) \* g).
Proof.
move=> mh [M [Mreal Mh]] gi; apply/integrableP; split.
  by apply: emeasurable_funM => //; [exact: measurableT_comp|
                                     exact: measurable_int gi].
under eq_integral do rewrite abseM.
have: \int[mu]_(x in D) (`|M + 1|%:E * `|g x|) < +oo.
  rewrite ge0_integralZl ?lte_mul_pinfty//; first by case/integrableP : gi.
  by apply: measurableT_comp => //; exact: measurable_int gi.
apply/le_lt_trans/ge0_le_integral => //.
- apply/emeasurable_funM; last exact/measurableT_comp/(measurable_int _ gi).
  exact/measurable_EFinP/measurableT_comp.
- apply/emeasurable_funM => //; apply/measurableT_comp => //.
  exact: measurable_int gi.
- move=> x Dx; rewrite lee_wpmul2r//= lee_fin Mh//=.
  by rewrite (lt_le_trans _ (ler_norm _))// ltrDl.
Qed.

Lemma integrableMl f (h : T -> R) :
  mu_int f -> measurable_fun D h -> [bounded h x | x in D] ->
  mu_int (f \* (EFin \o h)).
Proof.
move=> fi mh mg; rewrite /is_true -(integrableMr mh mg fi).
by apply/congr1/funext => ?; rewrite muleC.
Qed.

Lemma integrable_restrict (E : set T) (mE : d.-measurable E) f :
  integrable mu (E `&` D) f <-> integrable mu E (f \_ D).
Proof.
split; move=> /integrableP[mf intfoo]; apply/integrableP; split.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
- exact/measurable_restrict.
- by move: intfoo; rewrite integral_mkcondr/= restrict_abse.
Qed.

Lemma le_integral f g : mu_int f -> mu_int g ->
  {in D, forall x, f x <= g x} -> \int[mu]_(x in D) f x <= \int[mu]_(x in D) g x.
Proof.
move=> intf intg fg; rewrite integralE [leRHS]integralE leeB//.
- apply: ge0_le_integral => //.
  + by move/integrableP : intf => [+ _]; exact: measurable_funepos.
  + by move/integrableP : intg => [+ _]; exact: measurable_funepos.
  + by move=> x /mem_set; exact: funepos_le.
- apply: ge0_le_integral => //.
  + by move/integrableP : intg => [+ _]; exact: measurable_funeneg.
  + by move/integrableP : intf => [+ _]; exact: measurable_funeneg.
  + by move=> x /mem_set; exact: funeneg_le.
Qed.

End integrable_theory.
Notation "mu .-integrable" := (integrable mu) : type_scope.
Arguments eq_integrable {d T R mu D} mD f.

Section integrable_theory_finite_measure.
Context {R : realType} d (T : measurableType d).
Variable mu : {finite_measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integrable_indic A : measurable A ->
  mu.-integrable [set: T] (fun x : T => (\1_A x)%:E).
Proof.
move=> mA; apply/integrableP; split; first exact/measurable_EFinP.
rewrite (eq_integral (fun x => (\1_A x)%:E)); last first.
  by move=> t _; rewrite gee0_abs// lee_fin.
rewrite integral_indic// setIT.
rewrite (@le_lt_trans _ _ (mu setT)) ?le_measure ?inE//.
by rewrite ?ltry ?fin_num_fun_lty//; exact: fin_num_measure.
Qed.

End integrable_theory_finite_measure.

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
rewrite ge0_integral_measure_series//; last exact/measurable_funepos.
rewrite ge0_integral_measure_series//; last exact/measurable_funeneg.
transitivity (\sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\+ x)%E)%:E -
              \sum_(n <oo) (fine (\int[m_ n]_(x in D) f^\- x))%:E).
  by congr (_ - _); apply: eq_eseriesr => n _; rewrite fineK//;
    [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
have fineKn : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\- x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_neg_fin_num.
have fineKp : \sum_(n <oo) `|\int[m_ n]_(x in D) f^\+ x| =
          \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E|.
  apply: eq_eseriesr => n _; congr abse; rewrite fineK//.
  exact: integrable_pos_fin_num.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite nneseries_esum; last by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -esumB//; last 4 first.
  - by rewrite /= /summable -nneseries_esum// -fineKp.
  - by rewrite /summable /= -nneseries_esum// -fineKn; exact: fmoo.
  - by move=> n _; exact/fine_ge0/integral_ge0.
  - by move=> n _; exact/fine_ge0/integral_ge0.
rewrite -summable_eseries_esum; last first.
  apply: (@le_lt_trans _ _ (\esum_(i in (fun=> true))
     `|(fine (\int[m_ i]_(x in D) f x))%:E|)).
    by apply: le_esum => k _; rewrite -EFinB -fineB// -?integralE//;
      [exact: integrable_pos_fin_num|exact: integrable_neg_fin_num].
  rewrite -nneseries_esum; last by [].
  apply: (@le_lt_trans _ _
      (\sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\+ x))%:E| +
       \sum_(n <oo) `|(fine (\int[m_ n]_(x in D) f^\- x))%:E|)).
    rewrite -nneseriesD//; apply: lee_nneseries => // n _.
    rewrite integralE fineB// ?EFinB.
    - exact: (le_trans (lee_abs_sub _ _)).
    - exact: integrable_pos_fin_num.
    - exact: integrable_neg_fin_num.
  apply: lte_add_pinfty; first by rewrite -fineKp.
  by rewrite -fineKn; exact: fmoo.
by apply: eq_eseriesr => k _; rewrite !fineK// -?integralE//;
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
  measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  trivIset setT F ->
  \int[mu]_(x in D) f x = \sum_(i <oo) \int[mu]_(x in F i) f x.
Proof.
move=> mF D mf f0 tF.
pose f_ N := f \_ (\big[setU/set0]_(0 <= i < N) F i).
have lim_f_ t : f_ ^~ t @ \oo --> (f \_ D) t.
  rewrite [X in _ --> X](_ : _ = ereal_sup (range (f_ ^~ t))); last first.
    apply/eqP; rewrite eq_le; apply/andP; split.
      rewrite /restrict; case: ifPn => [|_].
        rewrite in_setE => -[n _ Fnt]; apply: ereal_sup_ubound; exists n.+1=>//.
        by rewrite /f_ big_mkord patchT// in_setE big_ord_recr/=; right.
      rewrite (@le_trans _ _ (f_ O t))// ?ereal_sup_ubound//.
      by rewrite /f_ patchN// big_mkord big_ord0 inE/= in_set0.
    apply: ub_ereal_sup => x [n _ <-].
    by rewrite /f_ restrict_lee// big_mkord; exact: bigsetU_bigcup.
  apply: ereal_nondecreasing_cvgn => a b ab.
  rewrite /f_ !big_mkord restrict_lee //; last exact: subset_bigsetU.
  by move=> x Dx; apply: f0 => //; exact: bigsetU_bigcup Dx.
transitivity (\int[mu]_x limn (f_ ^~ x)).
  rewrite integral_mkcond; apply: eq_integral => x _.
  by apply/esym/cvg_lim => //; exact: lim_f_.
rewrite monotone_convergence//; last 3 first.
  - move=> n; apply/(measurable_restrictT f) => //.
      by apply: bigsetU_measurable => k _; exact: mF.
    move: mf; apply/measurable_funS =>//; first exact: bigcup_measurable.
    by rewrite big_mkord; exact: bigsetU_bigcup.
  - move=> n x _; apply: erestrict_ge0 => y; rewrite big_mkord => Dy; apply: f0.
    exact: bigsetU_bigcup Dy.
  - move=> x _ a b ab; apply: restrict_lee.
      by move=> y; rewrite big_mkord => Dy; apply: f0; exact: bigsetU_bigcup Dy.
    by rewrite 2!big_mkord; apply: subset_bigsetU.
transitivity (limn (fun N => \int[mu]_(x in \big[setU/set0]_(i < N) F i) f x)).
  by apply/congr_lim/funext => n; rewrite /f_ [in RHS]integral_mkcond big_mkord.
apply/congr_lim/funext => /= n.
rewrite -(big_mkord xpredT) ge0_integral_bigsetU ?big_mkord//.
- exact: iota_uniq.
- exact: sub_trivIset tF.
- move: mf; apply: measurable_funS => //; first exact: bigcup_measurable.
  exact: bigsetU_bigcup.
- by move=> y Dy; apply: f0; exact: bigsetU_bigcup Dy.
Qed.

Lemma integrableS (E D : set T) (f : T -> \bar R) :
  measurable E -> measurable D -> D `<=` E ->
  mu.-integrable E f -> mu.-integrable D f.
Proof.
move=> mE mD DE /integrableP[mf ifoo]; apply/integrableP; split.
  exact: measurable_funS mf.
apply: le_lt_trans ifoo; apply: ge0_subset_integral => //.
exact: measurableT_comp.
Qed.

Lemma integrable_mkcond D f : measurable D ->
  mu.-integrable D f <-> mu.-integrable setT (f \_ D).
Proof.
move=> mD.
rewrite unlock; apply: asbool_equiv; rewrite [in X in X <-> _]integral_mkcond.
under [in X in X <-> _]eq_integral do rewrite restrict_abse.
split => [|] [mf foo].
- by split; [exact/(measurable_restrictT _ _).1| exact: le_lt_trans foo].
- by split; [exact/(measurable_restrictT _ _).2| exact: le_lt_trans foo].
Qed.

End integrable_lemmas.
Arguments integrable_mkcond {d T R mu D} f.

Section ge0_cvgn_integral.
Local Open Scope ereal_scope.
Context {R : realType}.
Variable mu : {measure set (@measurableTypeR R) -> \bar R}.
Variable f : R -> R.
Hypothesis f0 : (forall x, 0 <= f x)%R.
Hypothesis mf : measurable_fun setT f.

Let ge0_integral_ereal_sup :
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E =
  ereal_sup [set \int[mu]_(x in `[0%R, i.+1%:R]) (f x)%:E | i in [set: nat]].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ub_ereal_sup => /=_ [n _ <-].
  apply: ge0_subset_integral => //=.
  - by apply/measurable_EFinP; exact: measurable_funS mf.
  - by move=> ? _; rewrite lee_fin f0.
  - exact: subset_itvl.
rewrite itv0y_bigcup0S.
rewrite seqDU_bigcup_eq ge0_integral_bigcup//; last 3 first.
- by move=> ?; apply: measurableD => //; exact: bigsetU_measurable.
- by apply: measurable_funTS; exact/measurable_EFinP.
- by move=> x; rewrite lee_fin f0//.
apply: lime_le => /=.
  apply: is_cvg_nneseries => n _ _.
  by apply: integral_ge0 => k _; exact: f0.
apply: nearW => n.
rewrite -ge0_integral_bigsetU//=; first last.
- by move=> ? _; rewrite lee_fin ?expR_ge0.
- by apply/measurable_EFinP; exact: measurableT_comp.
- exact: (@sub_trivIset _ _ _ [set: nat]).
- exact: iota_uniq.
- by move=> k; apply: measurableD => //; exact: bigsetU_measurable.
rewrite big_mkord -bigsetU_seqDU.
move: n => [|n].
  rewrite big_ord0 integral_set0.
  apply: ereal_sup_le.
  exists (\int[mu]_(x in `[0%R, 1%:R]) (f x)%:E) => //.
  apply: integral_ge0.
  by move=> ? _; rewrite lee_fin f0.
rewrite [X in \int[_]_(_ in X) _](_ : _ = `[0%R, n.+1%:R]%classic); last first.
  rewrite eqEsubset; split => x/=; rewrite in_itv/=.
    rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
    move=> [k /= kSn].
    rewrite in_itv/= => /andP[-> xSk]/=.
    by rewrite (le_trans xSk)// ler_nat.
  move=> /andP[x0 Snx].
  rewrite -(bigcup_mkord _ (fun k => `[0%R, k.+1%:R]%classic)).
  exists n => //=.
  by rewrite in_itv/= x0 Snx.
apply: ereal_sup_le.
exists (\int[mu]_(x in `[0%R, n.+1%:R]) (f x)%:E); first by exists n.
apply: ge0_subset_integral => //=.
  by apply/measurable_EFinP; exact: measurableT_comp.
by move=> ? _; rewrite lee_fin f0.
Qed.

Lemma ge0_cvgn_integral :
  \int[mu]_(x in `[0%R, n%:R]) (f x)%:E @[n --> \oo] -->
  \int[mu]_(x in `[0%R, +oo[) (f x)%:E.
Proof.
rewrite -cvg_shiftS/= ge0_integral_ereal_sup//.
apply/ereal_nondecreasing_cvgn/nondecreasing_seqP => n.
apply: (@ge0_subset_integral _ _ _ mu) => //.
- by apply: measurable_funTS; exact: measurableT_comp.
- by move => ? _; exact: f0.
- by apply: subset_itvl; rewrite bnd_simp ler_nat.
Qed.

End ge0_cvgn_integral.

Lemma finite_measure_integrable_cst d (T : measurableType d) (R : realType)
    (mu : {finite_measure set T -> \bar R}) k :
  mu.-integrable [set: T] (EFin \o cst k).
Proof.
apply/integrableP; split; first exact/measurable_EFinP.
have [k0|k0] := leP 0 k.
- under eq_integral do rewrite /= ger0_norm//.
  rewrite integral_cstr//= lte_mul_pinfty// fin_num_fun_lty//.
  exact: fin_num_measure.
- under eq_integral do rewrite /= ltr0_norm//.
  rewrite integral_cstr//= lte_mul_pinfty//.
    by rewrite lee_fin lerNr oppr0 ltW.
  by rewrite fin_num_fun_lty//; exact: fin_num_measure.
Qed.

Section integrable_ae.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : T -> \bar R.
Hypotheses fint : mu.-integrable D f.

Lemma integrable_ae : {ae mu, forall x, D x -> f x \is a fin_num}.
Proof.
have [muD0|muD0] := eqVneq (mu D) 0.
  by exists D; split => // t /= /not_implyP[].
pose E := [set x | `|f x| = +oo /\ D x ].
have mE : measurable E.
  rewrite (_ : E = D `&` f @^-1` [set -oo; +oo]).
    by apply: (measurable_int _ fint) => //; exact: measurableU.
  rewrite /E predeqE => t; split=> [[/eqP]|[Dt [|]/= ->//]].
  by rewrite eqe_absl leey andbT /preimage/= => /orP[|]/eqP; tauto.
have [ET|ET] := eqVneq E setT.
  have foo t : `|f t| = +oo by have [] : E t by rewrite ET.
  suff: \int[mu]_(x in D) `|f x| = +oo.
    by case: (integrableP _ _ _ fint) => _; rewrite ltey => /eqP.
  by rewrite -(integral_csty mD muD0)//; exact: eq_integral.
suff: mu E = 0.
  move=> muE0; exists E; split => // t /= /not_implyP[Dt].
  by rewrite fin_num_abs => /negP; rewrite -leNgt leye_eq => /eqP.
have [->|/set0P E0] := eqVneq E set0; first by rewrite measure0.
have [M M0 muM] : exists2 M, (0 <= M)%R &
    forall n, n%:R%:E * mu (E `&` D) <= M%:E.
  exists (fine (\int[mu]_(x in D) `|f x|)); first exact/fine_ge0/integral_ge0.
  move=> n; rewrite -integral_indic// -ge0_integralZl//; last 2 first.
    - exact: measurableT_comp.
    - by move=> *; rewrite lee_fin.
  rewrite fineK//; last first.
    case: (integrableP _ _ _ fint) => _ foo.
    by rewrite ge0_fin_numE// integral_ge0.
  apply: ge0_le_integral => //.
  - by move=> *; rewrite lee_fin /indic.
  - exact/measurable_EFinP/measurableT_comp.
  - by apply: measurableT_comp => //; exact: measurable_int fint.
  - move=> x Dx; rewrite /= indicE.
    have [|xE] := boolP (x \in E); last by rewrite mule0.
    by rewrite /E inE /= => -[->]; rewrite leey.
apply/eqP/negPn/negP => /eqP muED0; move/not_forallP : muM; apply.
have [muEDoo|] := ltP (mu (E `&` D)) +oo; last first.
  by rewrite leye_eq => /eqP ->; exists 1%N; rewrite mul1e leye_eq.
exists `|ceil (M * (fine (mu (E `&` D)))^-1)|%N.+1.
apply/negP; rewrite -ltNge.
rewrite -[X in _ * X](@fineK _ (mu (E `&` D))); last first.
  by rewrite fin_numElt muEDoo (lt_le_trans _ (measure_ge0 _ _)).
rewrite lte_fin -ltr_pdivrMr.
  rewrite pmulrn floor_lt_int intS ltz1D abszE.
  by apply: le_trans (ler_norm _); rewrite ceil_floor//= lerDl.
rewrite -lte_fin fineK.
  rewrite lt0e measure_ge0 andbT.
  suff: E `&` D = E by move=> ->; exact/eqP.
  by rewrite predeqE => t; split=> -[].
by rewrite ge0_fin_numE// measure_ge0//; exact: measurableI.
Qed.

End integrable_ae.

Section linearityZ.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable (f : T -> \bar R).
Hypothesis intf : mu.-integrable D f.

Let mesf : measurable_fun D f. Proof. exact: measurable_int intf. Qed.

Lemma integralZl r :
  \int[mu]_(x in D) (r%:E * f x) = r%:E * \int[mu]_(x in D) f x.
Proof.
have /orP[r0|r0] := le_total r 0%R.
- rewrite [in LHS]integralE// le0_funeposM// le0_funenegM//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _)) ?oppr_ge0//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _)) ?oppr_ge0//.
  rewrite !EFinN addeC !mulNe oppeK -muleBr ?integrable_add_def//.
  by rewrite [in RHS]integralE.
- rewrite [in LHS]integralE// ge0_funeposM// ge0_funenegM//=.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funepos _) r0)//.
  rewrite (ge0_integralZl_EFin _ _ _ (measurable_funeneg _) r0)//.
  by rewrite -muleBr 1?[in RHS]integralE// integrable_add_def.
Qed.

Lemma integralZr r :
  \int[mu]_(x in D) (f x * r%:E) = (\int[mu]_(x in D) f x) * r%:E.
Proof. by rewrite muleC -integralZl; under eq_integral do rewrite muleC. Qed.

End linearityZ.
#[deprecated(since="mathcomp-analysis 0.6.4", note="use `integralZl` instead")]
Notation integralM := integralZl (only parsing).

Section linearityD_EFin.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables f1 f2 : T -> R.
Let g1 := EFin \o f1.
Let g2 := EFin \o f2.
Hypothesis if1 : mu.-integrable D g1.
Hypothesis if2 : mu.-integrable D g2.

Let mf1 : measurable_fun D g1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D g2. Proof. exact: measurable_int if2. Qed.

Lemma integralD_EFin :
  \int[mu]_(x in D) (g1 \+ g2) x =
  \int[mu]_(x in D) g1 x + \int[mu]_(x in D) g2 x.
Proof.
suff: \int[mu]_(x in D) ((g1 \+ g2)^\+ x) + \int[mu]_(x in D) (g1^\- x) +
        \int[mu]_(x in D) (g2^\- x) =
      \int[mu]_(x in D) ((g1 \+ g2)^\- x) + \int[mu]_(x in D) (g1^\+ x) +
        \int[mu]_(x in D) (g2^\+ x).
  move=> h; rewrite [in LHS]integralE.
  move/eqP : h; rewrite -[in eqbRHS]addeA [in eqbRHS]addeC.
  have g12pos :
      \int[mu]_(x in D) (g1^\+ x) + \int[mu]_(x in D) (g2^\+ x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty//; exact: integral_funepos_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  have g12neg :
      \int[mu]_(x in D) (g1^\- x) + \int[mu]_(x in D) (g2^\- x) \is a fin_num.
    rewrite ge0_fin_numE//.
      by rewrite lte_add_pinfty// ; exact: integral_funeneg_lt_pinfty.
    by rewrite adde_ge0// integral_ge0.
  rewrite -sube_eq; last 2 first.
    - rewrite ge0_fin_numE.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        apply: lte_add_pinfty; last exact: integral_funeneg_lt_pinfty.
        exact: integral_funepos_lt_pinfty (integrableD _ _ _).
      apply: adde_ge0; last exact: integral_ge0.
      by apply: adde_ge0; apply: integral_ge0.
    - exact/fin_num_adde_defr/g12pos.
  rewrite -[X in X - _ == _]addeA [X in X - _ == _]addeC -[eqbLHS]addeA.
  rewrite [eqbLHS]addeC eq_sym.
  rewrite -(sube_eq g12pos) ?fin_num_adde_defl// => /eqP g12E.
  rewrite -{}[LHS]g12E fin_num_oppeD; last first.
    rewrite ge0_fin_numE; first exact: integral_funeneg_lt_pinfty if2.
    exact: integral_ge0.
  by rewrite addeACA (integralE _ _ g1) (integralE _ _ g2).
have : (g1 \+ g2)^\+ \+ g1^\- \+ g2^\- = (g1 \+ g2)^\- \+ g1^\+ \+ g2^\+.
  rewrite funeqE => x.
  apply/eqP; rewrite -2!addeA [in eqbRHS]addeC -sube_eq; last 2 first.
    by rewrite funeposE !funenegE -!fine_max.
    by rewrite !funeposE funenegE -!fine_max.
  rewrite addeAC eq_sym -sube_eq; last 2 first.
    by rewrite !funeposE -!fine_max.
    by rewrite funeposE !funenegE -!fine_max.
  apply/eqP.
  rewrite -[LHS]/((g1^\+ \+ g2^\+ \- (g1^\- \+ g2^\-)) x) -funeD_posD.
  by rewrite -[RHS]/((_ \- _) x) -funeD_Dpos.
move/(congr1 (fun y => \int[mu]_(x in D) (y x) )).
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; rewrite adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funeneg.
    exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact: measurable_funeneg.
rewrite (ge0_integralD mu mD); last 4 first.
  - by [].
  - exact/measurable_funepos/emeasurable_funD.
  - by [].
  - exact/measurable_funeneg.
move=> g12E; rewrite {}[LHS]g12E.
rewrite (ge0_integralD mu mD); last 4 first.
  - by move=> x _; exact: adde_ge0.
  - apply: emeasurable_funD; last exact: measurable_funepos.
    exact/measurable_funeneg/emeasurable_funD.
  - by [].
  - exact: measurable_funepos.
rewrite (ge0_integralD mu mD) //; last exact: measurable_funepos.
exact/measurable_funeneg/emeasurable_funD.
Qed.

End linearityD_EFin.

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

Lemma le_abse_integral d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R)
  (mD : measurable D) : measurable_fun D f ->
  (`| \int[mu]_(x in D) (f x) | <= \int[mu]_(x in D) `|f x|)%E.
Proof.
move=> mf.
rewrite integralE (le_trans (lee_abs_sub _ _))// gee0_abs; last first.
  exact: integral_ge0.
rewrite gee0_abs; last exact: integral_ge0.
by rewrite -ge0_integralD // -?fune_abse//;
  [exact: measurable_funepos | exact: measurable_funeneg].
Qed.

Lemma EFin_normr_Rintegral d (T : measurableType d) {R : realType}
  (mu : {measure set T -> \bar R}) (A : set T) (f : T -> R) : measurable A ->
  mu.-integrable A (EFin \o f) ->
  `| \int[mu]_(x in A) f x |%:E = `| \int[mu]_(x in A) (f x)%:E |%E.
Proof.
move=> mA /integrableP[mf intfoo]; rewrite -[RHS]fineK.
- rewrite /= fine_abse// fin_num_abs.
  exact: (le_lt_trans (le_abse_integral _ _ _)).
- rewrite abse_fin_num fin_num_abs.
  exact: (le_lt_trans (le_abse_integral _ _ _)).
Qed.

Lemma abse_integralP d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> \bar R) :
    measurable D -> measurable_fun D f ->
  (`| \int[mu]_(x in D) f x | < +oo <-> \int[mu]_(x in D) `|f x| < +oo)%E.
Proof.
move=> mD mf; split => [|] foo; last first.
  exact: (le_lt_trans (le_abse_integral mu mD mf) foo).
under eq_integral do rewrite -/((abse \o f) _) fune_abse.
rewrite ge0_integralD//;[|exact/measurable_funepos|exact/measurable_funeneg].
move: foo; rewrite integralE/= -fin_num_abs fin_numB => /andP[fpoo fnoo].
by rewrite lte_add_pinfty// ltey_eq ?fpoo ?fnoo.
Qed.

Lemma integral_fin_num_abs d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) (f : T -> R) :
  measurable D -> measurable_fun D f ->
  (\int[mu]_(x in D) `|(f x)%:E| < +oo)%E =
  ((\int[mu]_(x in D) (f x)%:E)%E \is a fin_num).
Proof.
move=> mD mf; rewrite fin_num_abs; case H : LHS; apply/esym.
- by move: H => /abse_integralP ->//; exact/measurable_EFinP.
- apply: contraFF H => /abse_integralP; apply => //.
  exact/measurable_EFinP.
Qed.

Section integral_patch.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma __deprecated__integral_setI_indic (E D : set T) (mD : measurable D) (f : T -> \bar R) :
  measurable E ->
  \int[mu]_(x in E `&` D) f x = \int[mu]_(x in E) (f x * (\1_D x)%:E).
Proof.
move=> mE; rewrite integral_mkcondr.
by under eq_integral do rewrite epatch_indic.
Qed.

Lemma __deprecated__integralEindic (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f x * (\1_D x)%:E).
Proof. by rewrite -__deprecated__integral_setI_indic// setIid. Qed.

Lemma integralEpatch (D : set T) (mD : measurable D) (f : T -> \bar R) :
  \int[mu]_(x in D) f x = \int[mu]_(x in D) (f \_ D) x.
Proof. by rewrite -[in LHS](setIid D) integral_mkcondr. Qed.

End integral_patch.
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integral_mkcondr` instead")]
Notation integral_setI_indic := __deprecated__integral_setI_indic (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="use `integralEpatch` instead")]
Notation integralEindic := __deprecated__integralEindic (only parsing).

Section ae_eq_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Let ae_eq_integral_abs_bounded (D : set T) (mD : measurable D) (f : T -> \bar R)
    M : measurable_fun D f -> (forall x, D x -> `|f x| <= M%:E) ->
  (\forall x \ae mu, D x -> f x = 0) -> \int[mu]_(x in D) `|f x|%E  = 0.
Proof.
move=> mf fM [N [mA mN0 Df0N]].
pose Df_neq0 := D `&` [set x | f x != 0].
have mDf_neq0 : measurable Df_neq0 by exact: emeasurable_neq.
pose f' : T -> R := indic Df_neq0.
have le_f_M t : D t -> `|f t| <= M%:E * (f' t)%:E.
  move=> Dt; rewrite /f' indicE; have [|] := boolP (t \in Df_neq0).
    by rewrite inE => -[_ _]; rewrite mule1 fM.
  by rewrite notin_setE=> /not_andP[//|/negP/negPn/eqP ->]; rewrite abse0 mule0.
have : 0 <= \int[mu]_(x in D) `|f x|  <= `|M|%:E * mu Df_neq0.
  rewrite integral_ge0//= /Df_neq0 -{2}(setIid D) setIAC -integral_indic//.
  rewrite -/Df_neq0 -ge0_integralZl//; last 2 first.
    - exact: measurableT_comp.
    - by move=> x ?; rewrite lee_fin.
  apply: ge0_le_integral => //.
  - exact: measurableT_comp.
  - by move=> x Dx; rewrite mule_ge0// lee_fin.
  - by apply: emeasurable_funM => //; exact: measurableT_comp.
  - move=> x Dx; rewrite (le_trans (le_f_M _ Dx))// lee_fin /f' indicE.
    by case: (_ \in _) => //; rewrite ?mulr1 ?mulr0// ler_norm.
have -> : mu Df_neq0 = 0.
  apply: (subset_measure0 _ _ _ mN0) => //.
  apply: subset_trans Df0N => /= x [/= f0 Dx] /=.
  by apply/not_implyP; split => //; exact/eqP.
by rewrite mule0 -eq_le => /eqP.
Qed.

Lemma ae_eq_integral_abs (D : set T) (mD : measurable D) (f : T -> \bar R) :
    measurable_fun D f ->
  \int[mu]_(x in D) `|f x| = 0 <-> (\forall x \ae mu, D x -> f x = 0).
Proof.
move=> mf; split=> [iDf0|Df0].
  exists (D `&` [set x | f x != 0]); split;
    [exact: emeasurable_neq| |by move=> t /= /not_implyP [Dt /eqP ft0]].
  have muDf a : (0 < a)%R -> mu (D `&` [set x | a%:E <= `|f x|]) = 0.
    move=> a0; apply/eqP; rewrite -measure_le0.
    by have := le_integral_abse mu mD mf a0; rewrite iDf0 pmule_rle0 ?lte_fin.
  rewrite [X in mu X](_ : _ =
     \bigcup_n (D `&` [set x | `|f x| >= n.+1%:R^-1%:E])); last first.
    rewrite predeqE => t; split=> [[Dt ft0]|[n _ /= [Dt nft]]].
      have [ftoo|ftoo] := eqVneq `|f t| +oo.
        by exists 0%N => //; split => //=; rewrite ftoo /= leey.
      pose m := `|ceil (fine `|f t|)^-1|%N.
      have ftfin : `|f t|%E \is a fin_num by rewrite ge0_fin_numE// ltey.
      exists m => //; split => //=.
      rewrite -(@fineK _ `|f t|) // lee_fin invf_ple; last 2 first.
      - exact: ltr0n.
      - by apply/fine_gt0; rewrite lt0e abse_ge0 abse_eq0 ft0 ltey.
      rewrite /m -natr1 natr_absz ger0_norm; last first.
        by rewrite -(ceil0 R) ceil_le.
      by rewrite intrD1 ceil_ge_int lerDl.
    by split => //; apply: contraTN nft => /eqP ->; rewrite abse0 -ltNge.
  transitivity (limn (fun n => mu (D `&` [set x | `|f x| >= n.+1%:R^-1%:E]))).
    apply/esym/cvg_lim => //; apply: nondecreasing_cvg_mu.
    - move=> i; apply: emeasurable_fun_c_infty => //.
      exact: measurableT_comp.
    - apply: bigcupT_measurable => i.
      by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
    - move=> m n mn; apply/subsetPset; apply: setIS => t /=.
      by apply: le_trans; rewrite lee_fin lef_pV2 // ?ler_nat // posrE.
  by rewrite (_ : (fun _ => _) = cst 0) ?lim_cst//= funeqE => n /=; rewrite muDf.
pose f_ := fun n x => mine `|f x| n%:R%:E.
have -> : (fun x => `|f x|) = (fun x => limn (f_^~ x)).
  rewrite funeqE => x; apply/esym/cvg_lim => //; apply/cvg_ballP => _/posnumP[e].
  near=> n; rewrite /ball /= /ereal_ball /= /f_.
  have [->|fxoo] := eqVneq `|f x|%E +oo.
    rewrite -[contract +oo](@divff _ (1 + n%:R)%R) ?nat1r//=.
    rewrite (@ger0_norm _ n%:R)// nat1r -mulrBl -natrB// subSnn ger0_norm//.
    by rewrite div1r; near: n; exact: near_infty_natSinv_lt.
  have fxn : `|f x| <= n%:R%:E.
    rewrite -(@fineK _ `|f x|); last by rewrite ge0_fin_numE// ltey.
    rewrite lee_fin; near: n; exists (Num.bound (fine `|f x|)) => //= n/=.
    by rewrite -(ler_nat R); apply: le_trans; exact/ltW/archi_boundP.
  by rewrite min_l// subrr normr0.
transitivity (limn (fun n => \int[mu]_(x in D) (f_ n x) )).
  apply/esym/cvg_lim => //; apply: cvg_monotone_convergence => //.
  - by move=> n; apply: measurable_mine => //; exact: measurableT_comp.
  - by move=> n t Dt; rewrite /f_ lexI abse_ge0 //= lee_fin.
  - move=> t Dt m n mn; rewrite /f_ lexI.
    have [ftm|ftm] := leP `|f t|%E m%:R%:E.
      by rewrite lexx /= (le_trans ftm)// lee_fin ler_nat.
    by rewrite (ltW ftm) /= lee_fin ler_nat.
have ae_eq_f_ n : (f_ n) = (cst 0) %[ae mu in D].
  case: Df0 => N [mN muN0 DfN].
  exists N; split => // t /= /not_implyP[Dt fnt0].
  apply: DfN => /=; apply/not_implyP; split => //.
  apply: contra_not fnt0 => ft0.
  by rewrite /f_ ft0 /= normr0 min_l// lee_fin.
have f_bounded n x : D x -> `|f_ n x| <= n%:R%:E.
  move=> Dx; rewrite /f_; have [|_] := leP `|f x| n%:R%:E.
    by rewrite abse_id.
  by rewrite gee0_abs// lee_fin.
have if_0 n : \int[mu]_(x in D) `|f_ n x| = 0.
  apply: (@ae_eq_integral_abs_bounded _ _ _ n%:R) => //.
    by apply: measurable_mine => //; exact: measurableT_comp.
  exact: f_bounded.
rewrite (_ : (fun _ => _) = cst 0) // ?lim_cst// funeqE => n.
by rewrite -(if_0 n); apply: eq_integral => x _; rewrite gee0_abs// /f_.
Unshelve. all: by end_near. Qed.

Lemma integral_abs_eq0 D (N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> N `<=` D -> measurable_fun D f ->
  mu N = 0 -> \int[mu]_(x in N) `|f x| = 0.
Proof.
move=> mN mD ND mf muN0; rewrite integralEpatch//.
rewrite (eq_integral (abse \o (f \_ N))); last first.
  by move=> t _; rewrite restrict_abse.
apply/ae_eq_integral_abs => //.
  apply/measurable_restrict => //; rewrite setIidr//.
  exact: (measurable_funS mD).
exists N; split => // t /= /not_implyP[_].
by rewrite patchE; case: ifPn => //; rewrite inE.
Qed.

Lemma negligible_integrable (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  mu N = 0 -> mu.-integrable D f <-> mu.-integrable (D `\` N) f.
Proof.
move=> mN mD mf muN0.
pose mCN := measurableC mN.
have /integrableP intone : mu.-integrable D (f \_ N).
  apply/integrableP; split.
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  rewrite (eq_integral ((abse \o f) \_ N)); last first.
    by move=> t _; rewrite restrict_abse.
  rewrite -integral_mkcondr (@integral_abs_eq0 D)//; first exact: measurableI.
  by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
have h1 : mu.-integrable D f <-> mu.-integrable D (f \_ ~` N).
  split=> [/integrableP intf|/integrableP intCf].
    apply/integrableP; split.
      by apply/measurable_restrict => //; exact: measurable_funS mf.
    rewrite (eq_integral ((abse \o f) \_ ~` N)); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr; case: intf => _; apply: le_lt_trans.
    by apply: ge0_subset_integral => //=; [exact:measurableI|
                                           exact:measurableT_comp].
  apply/integrableP; split => //; rewrite (funID N f).
  have ? : measurable_fun D (f \_ ~` N).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  have ? : measurable_fun D (f \_ N).
    by apply/measurable_restrict => //; exact: measurable_funS mf.
  apply: (@le_lt_trans _ _
    (\int[mu]_(x in D) (`|(f \_ ~` N) x| + `|(f \_ N) x|))).
    apply: ge0_le_integral => //.
    - by apply: measurableT_comp => //; exact: emeasurable_funD.
    - by move=> ? ?; apply: adde_ge0.
    - by apply: emeasurable_funD; exact: measurableT_comp.
    - by move=> *; rewrite lee_abs_add.
  rewrite ge0_integralD//; [|exact: measurableT_comp|exact: measurableT_comp].
  by apply: lte_add_pinfty; [case: intCf|case: intone].
have h2 : mu.-integrable (D `\` N) f <-> mu.-integrable D (f \_ ~` N).
  split=> [/integrableP intCf|/integrableP intCf]; apply/integrableP.
    split.
      by apply/measurable_restrict => //; exact: measurable_funS mf.
    rewrite (eq_integral ((abse \o f) \_ ~` N)); last first.
      by move=> t _; rewrite restrict_abse.
    rewrite -integral_mkcondr //; case: intCf => _; apply: le_lt_trans.
    apply: ge0_subset_integral => //=; [exact: measurableI|exact: measurableD|].
    by apply: measurableT_comp => //; apply: measurable_funS mf => // ? [].
  split.
    move=> mDN A mA; rewrite setDE (setIC D) -setIA; apply: measurableI => //.
    exact: mf.
  rewrite integral_mkcondr/=.
  under eq_integral do rewrite restrict_abse.
  by case: intCf.
by apply: (iff_trans h1); exact: iff_sym.
Qed.

Lemma ge0_negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> measurable_fun D f ->
  (forall x, D x -> 0 <= f x) ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf f0 muN0.
rewrite {1}(funID N f) ge0_integralD//; last 4 first.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - apply/measurable_restrict => //; first exact/measurableC.
    exact: measurable_funS mf.
  - by move=> x Dx; rewrite patchE; case: ifPn => // _; exact: f0.
  - by apply/measurable_restrict => //; exact: measurable_funS mf.
rewrite -integral_mkcondr [X in _ + X = _](_ : _ = 0) ?adde0//.
rewrite -integral_mkcondr (eq_integral (abse \o f)); last first.
  move=> x; rewrite in_setI => /andP[xD xN].
  by rewrite /= gee0_abs// f0//; rewrite inE in xD.
rewrite (@integral_abs_eq0 D)//; first exact: measurableI.
by apply: (subset_measure0 _ _ _ muN0) => //; exact: measurableI.
Qed.

Lemma ge0_ae_eq_integral (D : set T) (f g : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  (forall x, D x -> 0 <= f x) -> (forall x, D x -> 0 <= g x) ->
  f = g %[ae mu in D] -> \int[mu]_(x in D) (f x) = \int[mu]_(x in D) (g x).
Proof.
move=> mD mf mg f0 g0 [N [mN N0 subN]].
rewrite integralEpatch// [RHS]integralEpatch//.
rewrite (ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) f0.
rewrite [RHS](ge0_negligible_integral mN)//; last 2 first.
  - by apply/measurable_restrict => //; rewrite setIidr.
  - by move=> x Dx; rewrite /= patchE (mem_set Dx) g0.
apply: eq_integral => x;rewrite in_setD => /andP[_ xN].
apply: contrapT; rewrite !patchE; case: ifPn => xD //.
move: xN; rewrite notin_setE; apply: contra_not => fxgx; apply: subN => /=.
by apply/not_implyP; split => //; exact/set_mem.
Qed.

Lemma ae_eq_integral (D : set T) (g f : T -> \bar R) :
  measurable D -> measurable_fun D f -> measurable_fun D g ->
  f = g %[ae mu in D] -> \int[mu]_(x in D) f x = \int[mu]_(x in D) g x.
Proof.
move=> mD mf mg /ae_eq_funeposneg[Dfgp Dfgn].
rewrite integralE// [in RHS]integralE//; congr (_ - _).
  by apply: ge0_ae_eq_integral => //; [exact: measurable_funepos|
                                       exact: measurable_funepos].
by apply: ge0_ae_eq_integral => //; [exact: measurable_funeneg|
                                     exact: measurable_funeneg].
Qed.

End ae_eq_integral.
Arguments ae_eq_integral {d T R mu D} g.

Local Open Scope ereal_scope.

Lemma integral_cst d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (D : set T) : d.-measurable D ->
  forall r, \int[mu]_(x in D) (cst r) x = r * mu D.
Proof.
move=> mD; have [D0 r|D0 [r| |]] := eqVneq (mu D) 0.
  by rewrite (ae_eq_integral (cst 0))// ?integral0 ?D0 ?mule0//; exact: ae_eq0.
- by rewrite integral_cstr.
- by rewrite integral_csty// gt0_mulye// lt0e D0/=.
- by rewrite integral_cstNy// gt0_mulNye// lt0e D0/=.
Qed.
Add Search Blacklist "integral_cstr" "integral_csty" "integral_cstNy".

Lemma le_integral_comp_abse d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R})  (D : set T) (mD : measurable D)
    (g : T -> \bar R) a (f : \bar R -> \bar R) (mf : measurable_fun setT f)
    (f0 : forall r, 0 <= r -> 0 <= f r)
    (f_nd : {in `[0, +oo[%classic &, {homo f : x y / x <= y}}) :
  measurable_fun D g -> (0 < a)%R ->
  (f a%:E) * mu (D `&` [set x | (`|g x| >= a%:E)%E]) <= \int[mu]_(x in D) f `|g x|.
Proof.
move=> mg a0; have ? : measurable (D `&` [set x | (a%:E <= `|g x|)%E]).
  by apply: emeasurable_fun_c_infty => //; exact: measurableT_comp.
apply: (@le_trans _ _ (\int[mu]_(x in D `&` [set x | `|g x| >= a%:E]) f `|g x|)).
  rewrite -integral_cst//; apply: ge0_le_integral => //.
  - by move=> x _ /=; rewrite f0 // lee_fin ltW.
  - by move=> x _ /=; rewrite f0.
  - apply: measurableT_comp => //; apply: measurableT_comp => //.
    exact: measurable_funS mg.
  - by move=> x /= [Dx]; apply: f_nd;
      rewrite inE /= in_itv /= andbT// lee_fin ltW.
apply: ge0_subset_integral => //; last by move=> x _ /=; rewrite f0.
by apply: measurableT_comp => //; exact: measurableT_comp.
Qed.

Local Close Scope ereal_scope.

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
rewrite [X in measurable X](_ : _ = D `&` ~` N `&` (f @^-1` `]x%:E, +oo[)
    `|` (D `&` N `&` g @^-1` `]x%:E, +oo[)); last first.
  apply/seteqP; split=> [y /= [Dy gyxoo]|y /= [[[Dy Ny] fyxoo]|]].
  - have [->|fgy] := eqVneq (f y) (g y).
      have [yN|yN] := boolP (y \in N).
        by right; split => //; rewrite inE in yN.
      by left; split => //; rewrite notin_setE in yN.
    by right; split => //; split => //; apply: subN => /= /(_ Dy); exact/eqP.
  - split => //; have [<-//|fgy] := eqVneq (f y) (g y).
    by exfalso; apply/Ny/subN => /= /(_ Dy); exact/eqP.
  - by move=> [[]].
apply: measurableU.
- rewrite setIAC; apply: measurableI; last exact/measurableC.
  exact/mf/emeasurable_itv.
- by apply: cmu; exists N; split => //; rewrite setIAC; apply: subIset; right.
Qed.

End ae_measurable_fun.

Section integralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f1 f2 : T -> \bar R).
Hypotheses (if1 : mu.-integrable D f1) (if2 : mu.-integrable D f2).

Let mf1 : measurable_fun D f1. Proof. exact: measurable_int if1. Qed.
Let mf2 : measurable_fun D f2. Proof. exact: measurable_int if2. Qed.

Lemma integralD : \int[mu]_(x in D) (f1 x + f2 x) =
  \int[mu]_(x in D) f1 x + \int[mu]_(x in D) f2 x.
Proof.
pose A := D `&` [set x | f1 x \is a fin_num].
pose B := D `&` [set x | f2 x \is a fin_num].
have mA : measurable A by exact: emeasurable_fin_num.
have mB : measurable B by exact: emeasurable_fin_num.
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
have mg1 := measurable_int _ ig1.
have ig2 : mu.-integrable D (EFin \o g2).
  rewrite (_ : _ \o _ = f2 \_ (A `&` B)) //.
    apply: (integrableS measurableT)=>//; apply/(integrable_mkcond _ _).1 => //.
    by apply: integrableS if2=>//; rewrite -setIAC -setIA; apply: subIset; left.
  rewrite /g2 funeqE => x //=; rewrite !/restrict; case: ifPn => //.
  rewrite in_setI => /andP[_]; rewrite in_setI => /andP[xB f2xfin] /=.
  by rewrite fineK//; rewrite inE in f2xfin.
have mg2 := measurable_int _ ig2.
transitivity (\int[mu]_(x in D) (EFin \o (g1 \+ g2)%R) x).
  apply: ae_eq_integral => //.
  - exact: emeasurable_funD.
  - rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))//.
    exact: emeasurable_funD.
  - apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=.
    rewrite EFinD /g1 /g2 /restrict /=; have [|] := boolP (x \in A `&` B).
      by rewrite in_setI => /andP[xA xB] /=; rewrite !fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx)/= notin_setE/=.
- rewrite (_ : _ \o _ = (EFin \o g1) \+ (EFin \o g2))// integralD_EFin//.
  congr (_ + _); apply: ae_eq_integral => //.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g1 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE/=.
  + apply: (filterS2 _ _ (integrable_ae mD if1) (integrable_ae mD if2)).
    move=> x + + Dx => /(_ Dx) f1fin /(_ Dx) f2fin /=; rewrite /g2 /restrict /=.
    have [/=|] := boolP (x \in A `&` B); first by rewrite fineK.
    by rewrite in_setI negb_and => /orP[|];
      rewrite in_setI negb_and /= (mem_set Dx) /= notin_setE.
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

Section transfer.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variable phi : X -> Y.
Hypothesis mphi : measurable_fun [set: X] phi.
Variable mu : {measure set X -> \bar R}.
Variables D : set Y.
Variables f : Y -> \bar R.
Hypotheses (mf : measurable_fun [set: Y] f)
  (intf : mu.-integrable (phi @^-1` D) (f \o phi)).
Let mf_mixin := isMeasurableFun.Build _ _ _ _ _ mf.
Let mf_pack := MeasurableFun.Pack (MeasurableFun.Class mf_mixin).

Lemma integrable_pushforward :
  measurable D -> (pushforward mu mphi).-integrable D f.
Proof.
move=> mD; apply/integrableP; split; first exact: (measurable_funP mf_pack).
move/integrableP : (intf) => [_]; apply: le_lt_trans.
rewrite ge0_integral_pushforward//.
by apply: measurableT_comp => //; exact: measurable_funTS.
Qed.

Local Open Scope ereal_scope.

Lemma integral_pushforward : measurable D ->
  \int[pushforward mu mphi]_(y in D) f y =
  \int[mu]_(x in phi @^-1` D) (f \o phi) x.
Proof.
move=> mD.
rewrite integralE.
under [X in X - _]eq_integral do rewrite funepos_comp.
under [X in _ - X]eq_integral do rewrite funeneg_comp.
rewrite -[X in _ = X - _]ge0_integral_pushforward//; last first.
  exact/measurable_funepos/measurable_funTS.
rewrite -[X in _ = _ - X]ge0_integral_pushforward//; last first.
  exact/measurable_funeneg/measurable_funTS.
rewrite -integralB//=; last first.
- by apply: integrable_funeneg => //=; exact: integrable_pushforward.
- by apply: integrable_funepos => //=; exact: integrable_pushforward.
- by apply/eq_integral => x _; rewrite /= [in LHS](funeposneg f).
Qed.

End transfer.

Section integral_measure_add.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
  (m1 m2 : {measure set T -> \bar R}) (D : set T).
Hypothesis mD : measurable D.
Variable f : T -> \bar R.
Hypothesis intf1 : m1.-integrable D f.
Hypothesis intf2 : m2.-integrable D f.
Hypothesis mf : measurable_fun D f.

Lemma integral_measure_add : \int[measure_add m1 m2]_(x in D) f x =
  \int[m1]_(x in D) f x + \int[m2]_(x in D) f x.
Proof.
transitivity (\int[m1]_(x in D) (f^\+ \- f^\-) x +
              \int[m2]_(x in D) (f^\+ \- f^\-) x); last first.
  by congr +%E; apply: eq_integral => x _; rewrite [in RHS](funeposneg f).
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite integralB//; [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite addeACA -ge0_integral_measure_add//; last first.
  by apply: measurable_funepos; exact: measurable_int intf1.
rewrite -oppeD; last by rewrite ge0_adde_def// inE integral_ge0.
rewrite -ge0_integral_measure_add// 1?integralE//.
by apply: measurable_funeneg; exact: measurable_int intf1.
Qed.

End integral_measure_add.

Section negligible_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}).

Lemma negligible_integral (D N : set T) (f : T -> \bar R) :
  measurable N -> measurable D -> mu.-integrable D f ->
  mu N = 0 -> \int[mu]_(x in D) f x = \int[mu]_(x in D `\` N) f x.
Proof.
move=> mN mD mf muN0; rewrite [f]funeposneg ?integralB //; first last.
- exact: integrable_funeneg.
- exact: integrable_funepos.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funeneg.
- apply: (integrableS mD) => //; first exact: measurableD.
  exact: integrable_funepos.
- exact: measurableD.
congr (_ - _); apply: ge0_negligible_integral => //; apply: (measurable_int mu).
  exact: integrable_funepos.
exact: integrable_funeneg.
Qed.

Lemma null_set_integral (N : set T) (f : T -> \bar R) :
  measurable N -> mu.-integrable N f ->
  mu N = 0 -> \int[mu]_(x in N) f x = 0.
Proof.
by move=> mN intf ?; rewrite (negligible_integral mN mN)// setDv integral_set0.
Qed.

End negligible_integral.
Add Search Blacklist "ge0_negligible_integral".

Section integrable_fune.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Local Open Scope ereal_scope.

Lemma integral_fune_lt_pinfty (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x < +oo.
Proof.
move=> intf; rewrite (funeposneg f) integralB//;
  [|exact: integrable_funepos|exact: integrable_funeneg].
rewrite lte_add_pinfty ?integral_funepos_lt_pinfty// lteNl ltNye_eq.
by rewrite integrable_neg_fin_num.
Qed.

Lemma integral_fune_fin_num (f : T -> \bar R) :
  mu.-integrable D f -> \int[mu]_(x in D) f x \is a fin_num.
Proof.
move=> h; apply/fin_numPlt; rewrite integral_fune_lt_pinfty// andbC/= -/(- +oo).
rewrite lteNl -integralN; first exact/integral_fune_lt_pinfty/integrableN.
by rewrite fin_num_adde_defl// fin_numN integrable_neg_fin_num.
Qed.

End integrable_fune.


Section integral_counting.
Local Open Scope ereal_scope.
Variable R : realType.

Lemma counting_dirac (A : set nat) :
  counting A = \sum_(n <oo) \d_ n A :> \bar R.
Proof.
have -> : \sum_(n <oo) \d_ n A = \esum_(i in A) \d_ i A :> \bar R.
  rewrite nneseries_esum// (_ : [set _ | _] = setT); last exact/seteqP.
  rewrite [in LHS](esumID A)// !setTI [X in _ + X](_ : _ = 0) ?adde0//.
  by apply: esum1 => i Ai; rewrite /= /dirac indicE memNset.
rewrite /counting/=; case: ifPn => /asboolP finA.
  by rewrite -finite_card_dirac.
by rewrite infinite_card_dirac.
Qed.

Lemma summable_integral_dirac (a : nat -> \bar R) : summable setT a ->
  \sum_(n <oo) `|\int[\d_ n]_x a x| < +oo.
Proof.
move=> sa.
apply: (@le_lt_trans _ _ (\sum_(i <oo) `|fine (a i)|%:E)).
  apply: lee_nneseries => // n _; rewrite integral_dirac//.
  move: (@summable_pinfty _ _ _ _ sa n Logic.I).
  by case: (a n) => //= r _; rewrite indicE/= mem_set// mul1r.
move: (sa); rewrite /summable -fun_true -nneseries_esum//; apply: le_lt_trans.
by apply lee_nneseries => // n _ /=; case: (a n) => //; rewrite leey.
Qed.

Lemma integral_count (a : nat -> \bar R) : summable setT a ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
- by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
- move=> n; apply/integrableP; split=> [//|].
  by rewrite integral_dirac//= diracT mul1e (summable_pinfty sa).
- by apply: summable_integral_dirac => //; exact: summable_funeneg.
- by apply: summable_integral_dirac => //; exact: summable_funepos.
Qed.

Lemma ge0_integral_count (a : nat -> \bar R) : (forall k, 0 <= a k) ->
  \int[counting]_t (a t) = \sum_(k <oo) (a k).
Proof.
move=> sa.
transitivity (\int[mseries (fun n => \d_ n) O]_t a t).
  congr (integral _ _ _); apply/funext => A.
  by rewrite /= counting_dirac.
rewrite (@ge0_integral_measure_series _ _ R (fun n => \d_ n) setT)//=.
by apply: eq_eseriesr=> i _; rewrite integral_dirac//= diracT mul1e.
Qed.

End integral_counting.

Section subadditive_countable.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable (mu : {measure set T -> \bar R}).

Lemma integrable_abse (D : set T) (f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D (abse \o f).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  exact: measurableT_comp.
by under eq_integral do rewrite abse_id.
Qed.

Lemma integrable_summable (F : (set T)^nat) (g : T -> \bar R):
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  summable [set: nat] (fun i => \int[mu]_(x in F i) g x).
Proof.
move=> tF mF fi.
rewrite /summable -(_ : [set _ | true] = setT); last exact/seteqP.
rewrite -nneseries_esum//.
have [mf {fi}] := integrableP _ _ _ fi.
rewrite ge0_integral_bigcup//; last exact: measurableT_comp.
apply: le_lt_trans; apply: lee_lim.
- exact: is_cvg_ereal_nneg_natsum_cond.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ _; exact: integral_ge0.
- apply: nearW => n; apply: lee_sum => m _; apply: le_abse_integral => //.
  apply: measurable_funS mf => //; [exact: bigcup_measurable|].
  exact: bigcup_sup.
Qed.

Lemma integral_bigcup (F : (set _)^nat) (g : T -> \bar R) :
  trivIset setT F -> (forall k, measurable (F k)) ->
  mu.-integrable (\bigcup_k F k) g ->
  (\int[mu]_(x in \bigcup_i F i) g x = \sum_(i <oo) \int[mu]_(x in F i) g x)%E.
Proof.
move=> tF mF fi.
have ? : \int[mu]_(x in \bigcup_i F i) g x \is a fin_num.
  rewrite fin_numElt -(lte_absl _ +oo).
  apply: le_lt_trans (integrableP _ _ _ fi).2; apply: le_abse_integral => //.
    exact: bigcupT_measurable.
  exact: measurable_int fi.
transitivity (\int[mu]_(x in \bigcup_i F i) g^\+ x -
              \int[mu]_(x in \bigcup_i F i) g^\- x)%E.
  rewrite -integralB.
  - by apply: eq_integral => t Ft; rewrite [in LHS](funeposneg g).
  - exact: bigcupT_measurable.
  - by apply: integrable_funepos => //; exact: bigcupT_measurable.
  - by apply: integrable_funeneg => //; exact: bigcupT_measurable.
transitivity (\sum_(i <oo) (\int[mu]_(x in F i) g^\+ x -
                            \int[mu]_(x in F i) g^\- x)); last first.
  by apply: eq_eseriesr => // i; rewrite [RHS]integralE.
transitivity ((\sum_(i <oo) \int[mu]_(x in F i) g^\+ x) -
              (\sum_(i <oo) \int[mu]_(x in F i) g^\- x))%E.
  rewrite ge0_integral_bigcup//; last first.
    by apply: measurable_funepos; case/integrableP : fi.
  rewrite ge0_integral_bigcup//.
  by apply: measurable_funeneg; case/integrableP : fi.
rewrite [X in X - _]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite [X in _ - X]nneseries_esum; last by move=> n _; exact: integral_ge0.
rewrite set_true -esumB//=; last 4 first.
  - apply: integrable_summable => //; apply: integrable_funepos => //.
    exact: bigcup_measurable.
  - apply: integrable_summable => //; apply: integrable_funeneg => //.
    exact: bigcup_measurable.
  - by move=> n _; exact: integral_ge0.
  - by move=> n _; exact: integral_ge0.
rewrite summable_eseries; last first.
  under [X in summable _ X]eq_fun do rewrite -integralE.
  by rewrite fun_true; exact: integrable_summable.
by congr (_ - _)%E; rewrite nneseries_esum// set_true.
Qed.

End subadditive_countable.

Section dominated_convergence_lemma.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variables (f_ : (T -> \bar R)^nat) (f : T -> \bar R) (g : T -> \bar R).
Hypothesis mf_ : forall n, measurable_fun D (f_ n).
Hypothesis f_f : forall x, D x -> f_ ^~ x @ \oo --> f x.
Hypothesis fing : forall x, D x -> g x \is a fin_num.
Hypothesis ig : mu.-integrable D g.
Hypothesis absfg : forall n x, D x -> `|f_ n x| <= g x.

Let g0 x : D x -> 0 <= g x.
Proof. by move=> Dx; rewrite (le_trans _ (@absfg O _ Dx))// lee_fin. Qed.

Let mf : measurable_fun D f.
Proof. exact: (emeasurable_fun_cvg _ _ mf_ f_f). Qed.

Local Lemma dominated_integrable : mu.-integrable D f.
Proof.
apply/integrableP; split => //; have Dfg x : D x -> `| f x | <= g x.
  move=> Dx; have /(@cvg_lim _) <- // : `|f_ n x| @[n --> \oo] --> `|f x|.
    by apply: cvg_abse => //; exact: f_f.
  apply: lime_le => //.
  - by apply: is_cvg_abse; apply/cvg_ex; eexists; exact: f_f.
  - by apply: nearW => n; exact: absfg.
move: ig => /integrableP[mg]; apply: le_lt_trans; apply: ge0_le_integral => //.
- exact: measurableT_comp.
- exact: measurableT_comp.
- by move=> x Dx /=; rewrite (gee0_abs (g0 Dx)); exact: Dfg.
Qed.

Let g_ n x := `|f_ n x - f x|.

Let cvg_g_ x : D x -> g_ ^~ x @ \oo --> 0.
Proof.
move=> Dx; rewrite -abse0; apply: cvg_abse.
move: (f_f Dx); case: (f x) => [r|/=|/=].
- by move=> f_r; exact/sube_cvg0.
- move/cvgeyPge/(_ (fine (g x) + 1)%R) => [n _]/(_ _ (leqnn n))/= h.
  have : (fine (g x) + 1)%:E <= g x.
    by rewrite (le_trans h)// (le_trans _ (absfg n Dx))// lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lteDl ?lte01.
- move/cvgeNyPle/(_ (- (fine (g x) + 1))%R) => [n _]/(_ _ (leqnn n)) h.
  have : (fine (g x) + 1)%:E <= g x.
    move: h; rewrite EFinN leeNr => /le_trans ->//.
    by rewrite (le_trans _ (absfg n Dx))// -abseN lee_abs.
  by case: (g x) (fing Dx) => [r _| |]//; rewrite leNgt EFinD lteDl ?lte01.
Qed.

Let gg_ n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof.
move=> Dx; rewrite subre_ge0; last by rewrite fin_numM// fing.
rewrite -(fineK (fing Dx)) -EFinM mulr_natl mulr2n /g_.
rewrite (le_trans (lee_abs_sub _ _))// [in leRHS]EFinD leeD//.
  by rewrite fineK// ?fing// absfg.
have f_fx : `|(f_ n x)| @[n --> \oo] --> `|f x| by apply: cvg_abse; exact: f_f.
move/cvg_lim : (f_fx) => <-//.
apply: lime_le; first by apply/cvg_ex; eexists; exact: f_fx.
by apply: nearW => k; rewrite fineK ?fing//; apply: absfg.
Qed.

Let mgg n : measurable_fun D (fun x => 2%:E * g x - g_ n x).
Proof.
apply/emeasurable_funB => //; [by apply/measurable_funeM/(measurable_int _ ig)|].
by apply/measurableT_comp => //; exact: emeasurable_funB.
Qed.

Let gg_ge0 n x : D x -> 0 <= 2%:E * g x - g_ n x.
Proof. by move=> Dx; rewrite gg_. Qed.

Local Lemma dominated_cvg0 : [sequence \int[mu]_(x in D) g_ n x]_n @ \oo --> 0.
Proof.
have := fatou mu mD mgg gg_ge0.
rewrite [X in X <= _ -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x) ); last first.
  apply: eq_integral => t; rewrite inE => Dt.
  rewrite limn_einf_shift//; last by rewrite fin_numM// fing.
  rewrite is_cvg_limn_einfE//; last first.
    by apply: is_cvgeN; apply/cvg_ex; eexists; exact: cvg_g_.
  rewrite [X in _ + X](_ : _ = 0) ?adde0//; apply/cvg_lim => //.
  by rewrite -oppe0; apply: cvgeN; exact: cvg_g_.
have i2g : \int[mu]_(x in D) (2%:E * g x)  < +oo.
rewrite integralZl// lte_mul_pinfty// ?lee_fin//; case: (integrableP _ _ _ ig) => _.
  apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply: eq_integral => t Dt; rewrite gee0_abs// g0//; rewrite inE in Dt.
have ? : \int[mu]_(x in D) (2%:E * g x)  \is a fin_num.
  by rewrite ge0_fin_numE// integral_ge0// => ? ?; rewrite mule_ge0 ?lee_fin ?g0.
rewrite [X in _ <= X -> _](_ : _ = \int[mu]_(x in D) (2%:E * g x)  + -
    limn_esup (fun n => \int[mu]_(x in D) g_ n x)); last first.
  rewrite (_ : (fun _ => _) = (fun n => \int[mu]_(x in D) (2%:E * g x)  +
      \int[mu]_(x in D) - g_ n x)); last first.
    rewrite funeqE => n; rewrite integralB//.
    - by rewrite -integral_ge0N// => x Dx//; rewrite /g_.
    - exact: integrableZl.
    - have integrable_normfn : mu.-integrable D (abse \o f_ n).
        apply: le_integrable ig => //; first exact: measurableT_comp.
        by move=> x Dx /=; rewrite abse_id (le_trans (absfg _ Dx))// lee_abs.
      suff: mu.-integrable D (fun x => `|f_ n x| + `|f x|).
        apply: le_integrable => //.
        - by apply: measurableT_comp => //; exact: emeasurable_funB.
        - move=> x Dx.
          by rewrite /g_ abse_id (le_trans (lee_abs_sub _ _))// lee_abs.
      apply: integrableD; [by []| by []|].
      apply: le_integrable dominated_integrable => //.
      - exact: measurableT_comp.
      - by move=> x Dx; rewrite /= abse_id.
  rewrite limn_einf_shift // -limn_einfN; congr (_ + limn_einf _).
  by rewrite funeqE => n /=; rewrite -integral_ge0N// => x Dx; rewrite /g_.
rewrite addeC -leeBlDr// subee// leeNr oppe0 => lim_ge0.
by apply/limn_esup_le_cvg => // n; rewrite integral_ge0// => x _; rewrite /g_.
Qed.

Local Lemma dominated_cvg :
  \int[mu]_(x in D) f_ n x @[n \oo] --> \int[mu]_(x in D) f x.
Proof.
have h n : `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x |
    <= \int[mu]_(x in D) g_ n x.
  rewrite -(integralB _ _ dominated_integrable)//; last first.
    by apply: le_integrable ig => // x Dx /=; rewrite (gee0_abs (g0 Dx)) absfg.
  by apply: le_abse_integral => //; exact: emeasurable_funB.
suff: `| \int[mu]_(x in D) f_ n x - \int[mu]_(x in D) f x | @[n \oo] --> 0.
   move/cvg_abse0P/sube_cvg0; apply.
   rewrite fin_numElt (_ : -oo = - +oo)// -lte_absl.
   move: dominated_integrable => /integrableP[?]; apply: le_lt_trans.
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
Hypothesis f_f : {ae mu, forall x, D x -> f_ ^~ x @ \oo --> f x}.
Hypothesis ig : mu.-integrable D g.
Hypothesis f_g : {ae mu, forall x n, D x -> `|f_ n x| <= g x}.

Let g_ n x := `|f_ n x - f x|.

Theorem dominated_convergence : [/\ mu.-integrable D f,
  [sequence \int[mu]_(x in D) (g_ n x)]_n @ \oo --> 0 &
  [sequence \int[mu]_(x in D) (f_ n x)]_n @ \oo --> \int[mu]_(x in D) (f x) ].
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
have f_f' x : D x -> f_' ^~ x @ \oo --> f' x.
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
  apply/measurable_restrict => //; first exact: measurableD.
  exact: measurable_funS (mf_ _).
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
- have /integrableP if' : mu.-integrable D f'.
    exact: (dominated_integrable _ f_' _ g').
  apply/integrableP; split => //.
  move: if' => [?]; apply: le_lt_trans.
  rewrite le_eqVlt; apply/orP; left; apply/eqP/ae_eq_integral => //;
    [exact: measurableT_comp|exact: measurableT_comp|].
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x Nx Dx.
  by rewrite /f' /restrict mem_set.
- have := @dominated_cvg0 _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X @ \oo --> _).
  rewrite [X in X @ \oo --> _ -> _](_ : _ = X) //.
  apply/funext => n; apply: ae_eq_integral => //.
  + apply: measurableT_comp => //; apply: emeasurable_funB => //.
    apply/measurable_restrict => //; first exact: measurableD.
    exact: (measurable_funS mD).
  + by rewrite /g_; apply: measurableT_comp => //; exact: emeasurable_funB.
  + exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /f' /restrict mem_set.
- have := @dominated_cvg _ _ _ _ _ mD _ _ _ mu_ f_f' finv ig' f_g'.
  set X := (X in _ -> X @ \oo --> _).
  rewrite [X in X @ \oo --> _ -> _](_ : _ = X) //; last first.
    apply/funext => n; apply: ae_eq_integral => //.
    exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
    by rewrite /f_' /restrict mem_set.
  set Y := (X in _ -> _ --> X); rewrite [X in _ --> X -> _](_ : _ = Y) //.
  apply: ae_eq_integral => //.
    apply/measurable_restrict => //; first exact: measurableD.
    exact: (measurable_funS mD).
  exists N; split => //; rewrite -(setCK N); apply: subsetC => x /= Nx Dx.
  by rewrite /f' /restrict mem_set.
Qed.

End dominated_convergence_theorem.

Section Rintegral.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (D A B : set T) (f : T -> R).

Lemma eq_Rintegral D g f : {in D, f =1 g} ->
  \int[mu]_(x in D) f x = \int[mu]_(x in D) g x.
Proof. by move=> fg; congr fine; apply: eq_integral => /= x xD; rewrite fg. Qed.

Lemma Rintegral_mkcond D f : \int[mu]_(x in D) f x = \int[mu]_x (f \_ D) x.
Proof.
rewrite {1}/Rintegral integral_mkcond/=.
by under eq_integral do rewrite restrict_EFin.
Qed.

Lemma Rintegral_mkcondr D P f :
  \int[mu]_(x in D `&` P) f x = \int[mu]_(x in D) (f \_ P) x.
Proof.
rewrite {1}/Rintegral integral_mkcondr.
by under eq_integral do rewrite restrict_EFin.
Qed.

Lemma Rintegral_mkcondl D P f :
  \int[mu]_(x in P `&` D) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite setIC Rintegral_mkcondr. Qed.

Lemma RintegralZl D f r : measurable D -> mu.-integrable D (EFin \o f) ->
  \int[mu]_(x in D) (r * f x) = r * \int[mu]_(x in D) f x.
Proof.
move=> mD intf; rewrite (_ : r = fine r%:E)// -fineM//; last first.
  exact: integral_fune_fin_num.
by congr fine; under eq_integral do rewrite EFinM; exact: integralZl.
Qed.

Lemma RintegralZr D f r : measurable D -> mu.-integrable D (EFin \o f) ->
  \int[mu]_(x in D) (f x * r) = \int[mu]_(x in D) f x * r.
Proof.
move=> mD intf; rewrite mulrC -RintegralZl//.
by under eq_Rintegral do rewrite mulrC.
Qed.

Lemma Rintegral_ge0 D f : (forall x, D x -> 0 <= f x) ->
  0 <= \int[mu]_(x in D) f x.
Proof. by move=> f0; rewrite fine_ge0// integral_ge0. Qed.

Lemma le_normr_integral D f : measurable D -> mu.-integrable D (EFin \o f) ->
  `|\int[mu]_(t in D) f t| <= \int[mu]_(t in D) `|f t|.
Proof.
move=> mA /integrableP[mf ifoo].
rewrite -lee_fin; apply: le_trans.
  apply: (le_trans _ (le_abse_integral mu mA mf)).
  rewrite /abse.
  have [/fineK <-//|] := boolP (\int[mu]_(x in D) (EFin \o f) x \is a fin_num)%E.
  by rewrite fin_numEn => /orP[|] /eqP ->; rewrite leey.
rewrite /Rintegral.
move: ifoo.
rewrite -ge0_fin_numE; last exact: integral_ge0.
move/fineK ->.
by apply: ge0_le_integral => //=; do 2 apply: measurableT_comp => //;
  exact/measurable_EFinP.
Qed.

Lemma Rintegral_setU (A B : set T) (f : T -> R) :
    d.-measurable A -> d.-measurable B ->
    mu.-integrable (A `|` B) (EFin \o f) -> [disjoint A & B] ->
  \int[mu]_(x in (A `|` B)) f x = \int[mu]_(x in A) f x + \int[mu]_(x in B) f x.
Proof.
move=> mA mB mf AB; rewrite /Rintegral integral_setU_EFin//; last first.
  exact/measurable_EFinP/(measurable_int mu).
have mAf :  mu.-integrable A (EFin \o f).
  by  apply: integrableS mf => //; exact: measurableU.
have mBf :  mu.-integrable B (EFin \o f).
  by apply: integrableS mf => //; exact: measurableU.
move/integrableP : mAf => [mAf itAfoo].
move/integrableP : mBf => [mBf itBfoo].
rewrite fineD//.
- by rewrite fin_num_abs (le_lt_trans _ itAfoo)//; exact: le_abse_integral.
- by rewrite fin_num_abs (le_lt_trans _ itBfoo)//; exact: le_abse_integral.
Qed.

Lemma Rintegral_set0 f : \int[mu]_(x in set0) f x = 0.
Proof. by rewrite /Rintegral integral_set0. Qed.

Lemma Rintegral_cst D : d.-measurable D ->
  forall r, \int[mu]_(x in D) (cst r) x = r * fine (mu D).
Proof.
move=> mD r; rewrite /Rintegral/= integral_cst//.
have := leey (mu D); rewrite le_eqVlt => /predU1P[->/=|muy]; last first.
  by rewrite fineM// ge0_fin_numE.
rewrite mulr_infty/=; have [_|r0|r0] := sgrP r.
- by rewrite mul0e/= mulr0.
- by rewrite mul1e/= mulr0.
- by rewrite mulN1e/= mulr0.
Qed.

Lemma le_Rintegral D f1 f2 : measurable D ->
  mu.-integrable D (EFin \o f1) ->
  mu.-integrable D (EFin \o f2) ->
  (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> mD mf1 mf2 f12; rewrite /Rintegral fine_le//.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf1.
  by apply/measurable_EFinP; case/integrableP : mf1.
- rewrite -integral_fin_num_abs//; first by case/integrableP : mf2.
  by apply/measurable_EFinP; case/integrableP : mf2.
- by apply/le_integral => // x xD; rewrite lee_fin f12//; exact/set_mem.
Qed.

Lemma RintegralB D f1 f2 : measurable D ->
  mu.-integrable D (EFin \o f1) -> mu.-integrable D (EFin \o f2) ->
  \int[mu]_(x in D) (f1 x - f2 x) =
  \int[mu]_(x in D) f1 x - \int[mu]_(x in D) f2 x.
Proof.
move=> mD if1 if2.
by rewrite /Rintegral integralB_EFin// fineB//; exact: integral_fune_fin_num.
Qed.

End Rintegral.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `Rintegral_setU`")]
Notation Rintegral_setU_EFin := Rintegral_setU (only parsing).

Section ae_ge0_le_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis f20 : forall x, D x -> 0 <= f2 x.
Hypothesis mf2 : measurable_fun D f2.

Lemma ae_ge0_le_integral : {ae mu, forall x, D x -> f1 x <= f2 x} ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> [N [mN muN f1f2N]]; rewrite (ge0_negligible_integral _ _ _ _ muN)//.
rewrite [leRHS](ge0_negligible_integral _ _ _ _ muN)//.
apply: ge0_le_integral; first exact: measurableD.
- by move=> t [Dt _]; exact: f10.
- exact: measurable_funS mf1.
- by move=> t [Dt _]; exact: f20.
- exact: measurable_funS mf2.
- by move=> t [Dt Nt]; move/subsetCl : f1f2N; exact.
Qed.

End ae_ge0_le_integral.

Section integral_bounded.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma integral_le_bound (D : set T) (f : T -> \bar R) (M : \bar R) :
  measurable D -> measurable_fun D f -> 0 <= M ->
  {ae mu, forall x, D x -> `|f x| <= M} ->
  \int[mu]_(x in D) `|f x| <= M * mu D.
Proof.
move=> mD mf M0 dfx; rewrite -integral_cst => //.
by apply: ae_ge0_le_integral => //; exact: measurableT_comp.
Qed.

End integral_bounded.
Arguments integral_le_bound {d T R mu D f} M.

Section integral_ae_eq.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (mu : {measure set T -> \bar R}).

Let integral_measure_lt (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> mu.-integrable D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  mu (D `&` [set x | g x < f x]) = 0.
Proof.
move=> itf itg fg; pose E j := D `&` [set x | f x - g x >= j.+1%:R^-1%:E].
have msf := measurable_int _ itf.
have msg := measurable_int _ itg.
have mE j : measurable (E j).
  rewrite /E; apply: emeasurable_fun_le => //.
  by apply/(emeasurable_funD msf)/measurableT_comp => //; case: mg.
have muE j : mu (E j) = 0.
  apply/eqP; rewrite -measure_le0.
  have fg0 : \int[mu]_(x in E j) (f \- g) x = 0.
    rewrite integralB//; last 2 first.
      by apply: integrableS itf => //; exact: subIsetl.
      by apply: integrableS itg => //; exact: subIsetl.
    rewrite fg//; last apply: subIsetl.
    rewrite subee// fin_num_abs (le_lt_trans (le_abse_integral _ _ _))//.
      by apply: measurable_funS msg => //; first exact: subIsetl.
    apply: le_lt_trans (integrableP _ _ _ itg).2.
    apply: ge0_subset_integral => //; first exact: measurableT_comp msg.
    exact: subIsetl.
  suff : mu (E j) <= j.+1%:R%:E * \int[mu]_(x in E j) (f \- g) x.
    by rewrite fg0 mule0.
  apply: (@le_trans _ _ (j.+1%:R%:E * \int[mu]_(x in E j) j.+1%:R^-1%:E)).
    by rewrite integral_cst// muleA -EFinM divff// mul1e.
  rewrite lee_pmul//; first exact: integral_ge0.
  apply: ge0_le_integral => //; [| |by move=> x []].
  - by move=> x [_/=]; exact: le_trans.
  - apply: emeasurable_funB.
    + by apply: measurable_funS msf => //; exact: subIsetl.
    + by apply: measurable_funS msg => //; exact: subIsetl.
have nd_E : {homo E : n0 m / (n0 <= m)%N >-> (n0 <= m)%O}.
  move=> i j ij; apply/subsetPset => x [Dx /= ifg]; split => //.
  by move: ifg; apply: le_trans; rewrite lee_fin lef_pV2// ?posrE// ler_nat.
rewrite set_lte_bigcup.
have /cvg_lim h1 : (mu \o E) x @[x --> \oo]--> 0.
  by apply: cvg_near_cst; exact: nearW.
have := @nondecreasing_cvg_mu _ _ _ mu E mE (bigcupT_measurable E mE) nd_E.
by move/cvg_lim => h2; rewrite setI_bigcupr -h2// h1.
Qed.

Lemma integral_ae_eq (D : set T) (mD : measurable D) (g f : T -> \bar R) :
  mu.-integrable D f -> measurable_fun D g ->
  (forall E, E `<=` D -> measurable E ->
    \int[mu]_(x in E) f x = \int[mu]_(x in E) g x) ->
  ae_eq mu D f g.
Proof.
move=> fi mg fg; have mf := measurable_int _ fi; have gi : mu.-integrable D g.
  apply/integrableP; split => //; apply/abse_integralP => //; rewrite -fg//.
  by apply/abse_integralP => //; case/integrableP : fi.
have mugf : mu (D `&` [set x | g x < f x]) = 0 by apply: integral_measure_lt.
have mufg : mu (D `&` [set x | f x < g x]) = 0.
  by apply: integral_measure_lt => // E ED mE; rewrite fg.
have h : ~` [set x | D x -> f x = g x] = D `&` [set x | f x != g x].
  apply/seteqP; split => [x/= /not_implyP[? /eqP]//|x/= [Dx fgx]].
  by apply/not_implyP; split => //; exact/eqP.
apply/negligibleP.
  by rewrite h; apply: emeasurable_fun_neq.
rewrite h set_neq_lt setIUr measureU//.
- by rewrite [X in X + _]mufg add0e [LHS]mugf.
- exact: emeasurable_fun_lt.
- exact: emeasurable_fun_lt.
- apply/seteqP; split => [x [[Dx/= + [_]]]|//].
  by move=> /lt_trans => /[apply]; rewrite ltxx.
Qed.

End integral_ae_eq.

(** Product measure *)

Section ndseq_closed_B.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Types A : set (T1 * T2).

Section xsection.
Variables (pt2 : T2) (m2 : T1 -> {measure set T2 -> \bar R}).
(* the generalization from m2 : {measure set T2 -> \bar R} to
   T1 -> {measure set T2 -> \bar R} is needed to develop the theory
   of kernels; the original type was sufficient for the development
   of the theory of integration  *)
Let phi A x := m2 x (xsection A x).
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma xsection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have phiF x : phi (F i) x @[i \oo] --> phi (\bigcup_i F i) x.
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
Variable m1 : {measure set T1 -> \bar R}.
Let psi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (psi A)].

Lemma ysection_ndseq_closed : ndseq_closed B.
Proof.
move=> F ndF; rewrite /B /= => BF; split.
  by apply: bigcupT_measurable => n; have [] := BF n.
have psiF x : psi (F i) x @[i \oo] --> psi (\bigcup_i F i) x.
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
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
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
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setXTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableX.
  have -> : phi (X1 `*` X2) = (fun x => m2D X2 * (\1_X1 x)%:E)%E.
    rewrite funeqE => x; rewrite indicE /phi /m2/= /mrestr.
    have [xX1|xX1] := boolP (x \in X1); first by rewrite mule1 in_xsectionX.
    by rewrite mule0 notin_xsectionX// set0I measure0.
  exact/measurable_funeM/measurable_EFinP.
suff lsystemB : lambda_system setT B by exact: lambda_system_subset.
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
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setXI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setXTT.
have CB : C `<=` B.
  move=> X [X1 mX1 [X2 mX2 <-{X}]]; split; first exact: measurableX.
  have -> : psi (X1 `*` X2) = (fun x => m1D X1 * (\1_X2 x)%:E)%E.
    rewrite funeqE => y; rewrite indicE /psi /m1/= /mrestr.
    have [yX2|yX2] := boolP (y \in X2); first by rewrite mule1 in_ysectionX.
    by rewrite mule0 notin_ysectionX// set0I measure0.
  exact/measurable_funeM/measurable_EFinP.
suff lsystemB : lambda_system setT B by exact: lambda_system_subset.
split => //; [exact: CB| |exact: ysection_ndseq_closed].
move=> X Y XY [mX mphiX] [mY mphiY]; split; first exact: measurableD.
rewrite (_ : psi _ = (psi X \- psi Y)%E); first exact: emeasurable_funB.
rewrite funeqE => y; rewrite /psi/= ysectionD// /m1D measureD.
- by rewrite setIidr//; exact: le_ysection.
- exact: measurable_ysection.
- exact: measurable_ysection.
- have [M m1M] := m1_bounded.
  rewrite (lt_le_trans (m1M (ysection X y) _))// ?leey//.
  exact: measurable_ysection.
Qed.

End ysection.

End measurable_prod_subset.

Section measurable_fun_xsection.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let phi A := m2 \o xsection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection A : measurable A -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A => /[apply] -[].
have /sigma_finiteP [F [F_T F_nd F_oo]] := sigma_finiteT m2 => X mX.
have -> : X = \bigcup_n (X `&` (setT `*` F n)).
  by rewrite -setI_bigcupr -setX_bigcupr -F_T setXTT setIT.
apply: xsection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSX => //.
  exact/subsetPset/F_nd.
move=> n; rewrite -/B; have [? ?] := F_oo n.
pose m2Fn := mrestr m2 (F_oo n).1.
have m2Fn_bounded : exists M, forall X, measurable X -> (m2Fn X < M%:E)%E.
  exists (fine (m2Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0//= /m2Fn /mrestr setIid.
  by rewrite /m2Fn /mrestr/= setIid le_measure// inE//; exact: measurableI.
pose phi' A := m2Fn \o xsection A.
pose B' := [set A | measurable A /\ measurable_fun setT (phi' A)].
have subset_B' : measurable `<=` B' by exact: measurable_prod_subset_xsection.
split=> [|_ Y mY]; first by apply: measurableI => //; exact: measurableX.
have [_ /(_ measurableT Y mY)] := subset_B' X mX.
have ->// : phi' X = m2 \o xsection (X `&` setT `*` F n).
by apply/funext => x/=; rewrite /phi' setTX xsectionI xsection_preimage_snd.
Qed.

End measurable_fun_xsection.

Section measurable_fun_ysection.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let phi A := m1 \o ysection A.
Let B := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_ysection A : measurable A -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` B by move=> + A => /[apply] -[].
have /sigma_finiteP[F [F_T F_nd F_oo]] := sigma_finiteT m1 => X mX.
have -> : X = \bigcup_n (X `&` (F n `*` setT)).
  by rewrite -setI_bigcupr -setX_bigcupl -F_T setXTT setIT.
apply: ysection_ndseq_closed.
  move=> m n mn; apply/subsetPset; apply: setIS; apply: setSX => //.
  exact/subsetPset/F_nd.
move=> n; have [? ?] := F_oo n; rewrite -/B.
pose m1Fn := mrestr m1 (F_oo n).1.
have m1Fn_bounded : exists M, forall X, measurable X -> (m1Fn X < M%:E)%E.
  exists (fine (m1Fn (F n)) + 1) => Y mY.
  rewrite [in ltRHS]EFinD lte_spadder// fineK; last first.
    by rewrite ge0_fin_numE ?measure_ge0// /m1Fn/= /mrestr setIid.
  by rewrite /m1Fn/= /mrestr setIid le_measure// inE//=; exact: measurableI.
pose psi' A := m1Fn \o ysection A.
pose B' := [set A | measurable A /\ measurable_fun setT (psi' A)].
have subset_B' : measurable `<=` B' by exact: measurable_prod_subset_ysection.
split=> [|_ Y mY]; first by apply: measurableI => //; exact: measurableX.
have [_ /(_ measurableT Y mY)] := subset_B' X mX.
have ->// : psi' X = m1 \o (ysection (X `&` F n `*` setT)).
by apply/funext => y/=; rewrite /psi' setXT ysectionI// ysection_preimage_fst.
Qed.

End measurable_fun_ysection.

Section product_measures.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Context (m1 : set T1 -> \bar R) (m2 : set T2 -> \bar R).

Definition product_measure1 := (fun A => \int[m1]_x (m2 \o xsection A) x)%E.
Definition product_measure2 := (fun A => \int[m2]_x (m1 \o ysection A) x)%E.

End product_measures.

Notation "m1 '\x' m2" := (product_measure1 m1 m2) : ereal_scope.
Notation "m1 '\x^' m2" := (product_measure2 m1 m2) : ereal_scope.

Section product_measure1.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let pm10 : (m1 \x m2) set0 = 0.
Proof. by rewrite [LHS]integral0_eq// => x/= _; rewrite xsection0. Qed.

Let pm1_ge0 A : 0 <= (m1 \x m2) A.
Proof. by apply: integral_ge0 => // *. Qed.

Let pm1_sigma_additive : semi_sigma_additive (m1 \x m2).
Proof.
move=> F mF tF mUF.
rewrite [X in _ --> X](_ : _ = \sum_(n <oo) (m1 \x m2) (F n)).
  by apply/cvg_closeP; split; [exact: is_cvg_nneseries|rewrite closeE].
rewrite -integral_nneseries//; last by move=> n; exact: measurable_fun_xsection.
apply: eq_integral => x _; apply/esym/cvg_lim => //=; rewrite xsection_bigcup.
apply: (measure_sigma_additive _ (trivIset_xsection tF)) => ?.
exact: measurable_xsection.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (m1 \x m2)
  pm10 pm1_ge0 pm1_sigma_additive.

End product_measure1.

Section product_measure1E.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Lemma product_measure1E (A1 : set T1) (A2 : set T2) :
  measurable A1 -> measurable A2 -> (m1 \x m2) (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
move=> mA1 mA2 /=; rewrite /product_measure1 /=.
rewrite (eq_integral (fun x => (\1_A1 x)%:E * m2 A2)); last first.
  by move=> x _; rewrite indicE; have [xA1|xA1] /= := boolP (x \in A1);
    [rewrite in_xsectionX// mul1e|rewrite mul0e notin_xsectionX].
rewrite ge0_integralZr//; last by move=> x _; rewrite lee_fin.
- by rewrite integral_indic// setIT.
- exact: measurableT_comp.
Qed.

End product_measure1E.

Section product_measure_unique.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.

Let product_measure_sigma_finite : sigma_finite setT (m1 \x m2).
Proof.
have /sigma_finiteP[F [TF ndF Foo]] := sigma_finiteT m1.
have /sigma_finiteP[G [TG ndG Goo]] := sigma_finiteT m2.
exists (fun n => F n `*` G n).
 rewrite -setXTT TF TG predeqE => -[x y]; split.
    move=> [/= [n _ Fnx] [k _ Gky]]; exists (maxn n k) => //; split.
    - by move: x Fnx; exact/subsetPset/ndF/leq_maxl.
    - by move: y Gky; exact/subsetPset/ndG/leq_maxr.
  by move=> [n _ []/= ? ?]; split; exists n.
move=> k; have [? ?] := Foo k; have [? ?] := Goo k.
split; first exact: measurableX.
by rewrite product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

HB.instance Definition _ := Measure_isSigmaFinite.Build _ _ _ (m1 \x m2)
  product_measure_sigma_finite.

Lemma product_measure_unique
    (m' : {measure set (T1 * T2) -> \bar R}) :
    (forall A B, measurable A -> measurable B -> m' (A `*` B) = m1 A * m2 B) ->
  forall X : set (T1 * T2), measurable X -> (m1 \x m2) X = m' X.
Proof.
move=> m'E.
have /sigma_finiteP[F [TF ndF Foo]] := sigma_finiteT m1.
have /sigma_finiteP[G [TG ndG Goo]] := sigma_finiteT m2.
have UFGT : \bigcup_k (F k `*` G k) = setT.
  rewrite -setXTT TF TG predeqE => -[x y]; split.
    by move=> [n _ []/= ? ?]; split; exists n.
  move=> [/= [n _ Fnx] [k _ Gky]]; exists (maxn n k) => //; split.
  - by move: x Fnx; exact/subsetPset/ndF/leq_maxl.
  - by move: y Gky; exact/subsetPset/ndG/leq_maxr.
pose C : set (set (T1 * T2)) :=
  [set C | exists A, measurable A /\ exists B, measurable B /\ C = A `*` B].
have CI : setI_closed C.
  move=> /= _ _ [X1 [mX1 [X2 [mX2 ->]]]] [Y1 [mY1 [Y2 [mY2 ->]]]].
  rewrite -setXI; exists (X1 `&` Y1); split; first exact: measurableI.
  by exists (X2 `&` Y2); split => //; exact: measurableI.
move=> X mX; apply: (measure_unique C (fun n => F n `*` G n)) => //.
- rewrite measurable_prod_measurableType //; congr (<<s _ >>).
  rewrite predeqE; split => [[A mA [B mB <-]]|[A [mA [B [mB ->]]]]].
    by exists A; split => //; exists B.
  by exists A => //; exists B.
- move=> n; rewrite /C /=; exists (F n); split; first by have [] := Foo n.
  by exists (G n); split => //; have [] := Goo n.
- by move=> A [A1 [mA1 [A2 [mA2 ->]]]]; rewrite m'E//= product_measure1E.
- move=> k; have [? ?] := Foo k; have [? ?] := Goo k.
  by rewrite /= product_measure1E// lte_mul_pinfty// ge0_fin_numE.
Qed.

End product_measure_unique.

Section product_measure2.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {measure set T2 -> \bar R}.
Implicit Types A : set (T1 * T2).

Let pm20 : (m1 \x^ m2) set0 = 0.
Proof.
by rewrite /(_ \x^ _) integral0_eq// => y/= _; rewrite ysection0 measure0.
Qed.

Let pm2_ge0 A : 0 <= (m1 \x^ m2) A.
Proof.
by apply: integral_ge0 => // *; exact/measure_ge0/measurable_ysection.
Qed.

Let pm2_sigma_additive : semi_sigma_additive (m1 \x^ m2).
Proof.
move=> F mF tF mUF.
rewrite [X in _ --> X](_ : _ = \sum_(n <oo) (m1 \x^ m2) (F n)).
  apply/cvg_closeP; split; last by rewrite closeE.
  by apply: is_cvg_nneseries => *; exact: integral_ge0.
rewrite -integral_nneseries//; last first.
  by move=> n; apply: measurable_fun_ysection => //; rewrite inE.
apply: eq_integral => y _; apply/esym/cvg_lim => //=; rewrite ysection_bigcup.
apply: (measure_sigma_additive _ (trivIset_ysection tF)) => ?.
exact: measurable_ysection.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (m1 \x^ m2)
  pm20 pm2_ge0 pm2_sigma_additive.

End product_measure2.

Section product_measure2E.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {measure set T2 -> \bar R}.

Lemma product_measure2E (A1 : set T1) (A2 : set T2)
    (mA1 : measurable A1) (mA2 : measurable A2) :
  (m1 \x^ m2) (A1 `*` A2) = m1 A1 * m2 A2.
Proof.
have mA1A2 : measurable (A1 `*` A2) by apply: measurableX.
transitivity (\int[m2]_y (m1 \o ysection (A1 `*` A2)) y) => //.
rewrite (_ : _ \o _ = fun y => m1 A1 * (\1_A2 y)%:E).
  rewrite ge0_integralZl//.
  - by rewrite integral_indic ?setIT ?mul1e.
  - exact: measurableT_comp.
  - by move=> y _; rewrite lee_fin.
rewrite funeqE => y; rewrite indicE.
have [yA2|yA2] := boolP (y \in A2); first by rewrite mule1 /= in_ysectionX.
by rewrite mule0 /= notin_ysectionX.
Qed.

End product_measure2E.

Section simple_density_L1.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (E : set T) (mE : measurable E).

Local Open Scope ereal_scope.

Lemma measurable_bounded_integrable (f : T -> R^o)  :
  mu E < +oo -> measurable_fun E f ->
  [bounded f x | x in E] -> mu.-integrable E (EFin \o f).
Proof.
move=> Afin mfA bdA; apply/integrableP; split; first exact/measurable_EFinP.
have [M [_ mrt]] := bdA; apply: le_lt_trans.
  apply: (integral_le_bound (`|M| + 1)%:E) => //; first exact: measurableT_comp.
  by apply: aeW => z Az; rewrite lee_fin mrt// ltr_pwDr// ler_norm.
by rewrite lte_mul_pinfty.
Qed.

Import HBSimple.

Let sfun_dense_L1_pos (f : T -> \bar R) :
  mu.-integrable E f -> (forall x, E x -> 0 <= f x) ->
  exists g_ : {sfun T >-> R}^nat,
    [/\ forall n, mu.-integrable E (EFin \o g_ n),
        forall x, E x -> EFin \o g_^~ x @ \oo --> f x &
        (fun n => \int[mu]_(z in E) `|f z - (g_ n z)%:E|) @ \oo --> 0].
Proof.
move=> intf fpos; case/integrableP: (intf) => mfE _.
pose g_ n := nnsfun_approx mE mfE n.

Import HBNNSimple.

have [] // := @dominated_convergence _ _ _ mu _ mE (fun n => EFin \o g_ n) f f.
- by move=> ?; exact/measurable_EFinP/measurable_funTS.
- apply: aeW => ? ?; under eq_fun => ? do rewrite /g_ nnsfun_approxE.
  exact: ecvg_approx.
- apply: aeW => /= ? ? ?; rewrite ger0_norm // /g_ nnsfun_approxE.
  exact: le_approx.
move=> _ /= fg0 gfcvg; exists g_; split.
- move=> n; apply: (le_integrable mE _ _ intf).
    exact/measurable_EFinP/measurable_funTS.
  move=> ? ?; rewrite /g_ !gee0_abs ?lee_fin ?fpos//.
  by rewrite /= nnsfun_approxE le_approx.
- exact: cvg_nnsfun_approx.
- by apply: cvg_trans fg0; under eq_fun => ? do under eq_fun => t do
     rewrite EFinN -[_ - _]oppeK fin_num_oppeB // abseN addeC.
Qed.

Lemma approximation_sfun_integrable (f : T -> \bar R):
  mu.-integrable E f ->
  exists g_ : {sfun T >-> R}^nat,
    [/\ forall n, mu.-integrable E (EFin \o g_ n),
        forall x, E x -> EFin \o g_^~ x @ \oo --> f x &
        (fun n => \int[mu]_(z in E) `|f z - (g_ n z)%:E|) @ \oo --> 0].
Proof.
move=> intf.
have [//|p_ [intp pf pl1]] := sfun_dense_L1_pos (integrable_funepos mE intf).
have [//|n_ [intn nf nl1]] := sfun_dense_L1_pos (integrable_funeneg mE intf).
exists (fun n => p_ n - n_ n)%R; split.
- move=> n; rewrite /comp; under eq_fun => ? do rewrite sfunB /= EFinB.
  by apply: integrableB => //; [exact: intp | exact: intn].
- move=> ? ?; rewrite /comp; under eq_fun => ? do rewrite sfunB /= EFinB.
  rewrite [f]funeposneg; apply: cvgeB => //;[|exact: pf|exact:nf].
  exact: add_def_funeposneg.
have fpn z n : f z - ((p_ n - n_ n) z)%:E =
    (f^\+ z - (p_ n z)%:E) - (f^\- z - (n_ n z)%:E).
  rewrite sfunB EFinB fin_num_oppeB // {1}[f]funeposneg -addeACA.
  by congr (_ _); rewrite fin_num_oppeB.
case/integrableP: (intf) => mf _.
have mfpn n : mu.-integrable E (fun z => f z - ((p_ n - n_ n) z)%:E).
  under eq_fun => ? do rewrite fpn; apply: integrableB => //.
    by apply: integrableB => //; [exact: integrable_funepos | exact: intp].
  by apply: integrableB => //; [exact: integrable_funeneg | exact: intn].
apply/fine_cvgP; split => //.
  near=> N; case/integrableP: (mfpn N) => _; rewrite ge0_fin_numE //.
  exact: integral_ge0.
apply/cvg_ballP=> _/posnumP[eps]; have e2p : (0 < eps%:num/2)%R by [].
case/fine_cvgP: pl1 => + /cvg_ballP/(_ _ e2p); apply: filter_app2.
case/fine_cvgP: nl1 => + /cvg_ballP/(_ _ e2p); apply: filter_app2.
near=> n; rewrite /ball /=; do 3 rewrite distrC subr0.
move=> finfn ne2 finfp pe2; rewrite [_%:num]splitr.
rewrite (le_lt_trans _ (ltrD pe2 ne2))// (le_trans _ (ler_normD _ _))//.
under [fun z => _ (f^\+ z + _)]eq_fun => ? do rewrite EFinN.
under [fun z => _ (f^\- z + _)]eq_fun => ? do rewrite EFinN.
have mfp : mu.-integrable E (fun z => `|f^\+ z - (p_ n z)%:E|).
  apply/integrable_abse/integrableB => //; first exact: integrable_funepos.
  exact: intp.
have mfn : mu.-integrable E (fun z => `|f^\- z - (n_ n z)%:E|).
  apply/integrable_abse/integrableB => //; first exact: integrable_funeneg.
  exact: intn.
rewrite -[x in (_ <= `|x|)%R]fineD // -integralD //.
move: finfn finfp => _ _.
rewrite !ger0_norm ?fine_ge0 ?integral_ge0 ?fine_le//.
- by apply: integral_fune_fin_num => //; exact/integrable_abse/mfpn.
- by apply: integral_fune_fin_num => //; exact: integrableD.
- apply: ge0_le_integral => //.
  + by apply: measurableT_comp => //; case/integrableP: (mfpn n).
  + by move=> x Ex; rewrite adde_ge0.
  + by apply: emeasurable_funD; [move: mfp | move: mfn]; case/integrableP.
  + by move=> ? ?; rewrite fpn; exact: lee_abs_sub.
  + by move=> x Ex; rewrite adde_ge0.
Unshelve. all: by end_near. Qed.
End simple_density_L1.

Section continuous_density_L1.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.
Local Open Scope ereal_scope.

Lemma compact_finite_measure (A : set R^o) : compact A -> mu A < +oo.
Proof.
move=> /[dup]/compact_measurable => mA /compact_bounded[N [_ N1x]].
have AN1 : (A `<=` `[- (`|N| + 1), `|N| + 1])%R.
  by move=> z Az; rewrite set_itvcc /= -ler_norml N1x// ltr_pwDr// ler_norm.
rewrite (le_lt_trans (le_measure _ _ _ AN1)) ?inE//=.
by rewrite lebesgue_measure_itv/= lte_fin gtrN// EFinD ltry.
Qed.

Lemma continuous_compact_integrable (f : R -> R^o) (A : set R^o) :
  compact A -> {within A, continuous f} -> mu.-integrable A (EFin \o f).
Proof.
move=> cptA ctsfA; apply: measurable_bounded_integrable.
- exact: compact_measurable.
- exact: compact_finite_measure.
- by apply: subspace_continuous_measurable_fun => //; exact: compact_measurable.
- have /compact_bounded[M [_ mrt]] := continuous_compact ctsfA cptA.
  by exists M; split; rewrite ?num_real // => ? ? ? ?; exact: mrt.
Qed.

Import HBSimple.

Lemma approximation_continuous_integrable (E : set _) (f : rT -> rT):
  measurable E -> mu E < +oo -> mu.-integrable E (EFin \o f) ->
  exists g_ : (rT -> rT)^nat,
    [/\ forall n, continuous (g_ n),
        forall n, mu.-integrable E (EFin \o g_ n) &
        \int[mu]_(z in E) `|(f z - g_ n z)%:E| @[n --> \oo] --> 0].
Proof.
move=> mE Efin intf.
have mf : measurable_fun E f by case/integrableP : intf => /measurable_EFinP.
suff apxf eps : exists h : rT -> rT, (eps > 0)%R ->
    [/\ continuous h,
        mu.-integrable E (EFin \o h) &
        \int[mu]_(z in E) `|(f z - h z)%:E| < eps%:E].
  pose g_ n := projT1 (cid (apxf n.+1%:R^-1)); exists g_; split.
  - by move=> n; have [] := projT2 (cid (apxf n.+1%:R^-1)).
  - by move=> n; have [] := projT2 (cid (apxf n.+1%:R^-1)).
  apply/cvg_ballP => eps epspos.
  have /cvg_ballP/(_ eps epspos)[N _ Nball] := @cvge_harmonic rT.
  exists N => //; apply: (subset_trans Nball) => n.
  rewrite /ball /= /ereal_ball contract0 !sub0r !normrN => /(lt_trans _); apply.
  rewrite ?ger0_norm; first last.
  - by rewrite -le_expandLR // ?inE ?normr0// expand0 integral_ge0.
  - by rewrite -le_expandLR // ?inE ?normr0// expand0.
  have [] := projT2 (cid (apxf n.+1%:R^-1)) => // _ _ ipaxfn.
  by rewrite -lt_expandRL ?contractK// inE contract_le1.
have [|] := ltP 0%R eps; last by exists point.
move: eps => _/posnumP[eps].
have [g [gfe2 ig]] : exists g : {sfun R >-> rT},
    \int[mu]_(z in E) `|(f z - g z)%:E| < (eps%:num / 2)%:E /\
    mu.-integrable E (EFin \o g).
  have [g_ [intG ?]] := approximation_sfun_integrable mE intf.
  move/fine_fcvg/cvg_ballP/(_ (eps%:num / 2)) => -[] // n _ Nb; exists (g_ n).
  have fg_fin_num : \int[mu]_(z in E) `|(f z - g_ n z)%:E| \is a fin_num.
    rewrite integral_fune_fin_num// integrable_abse//.
    by under eq_fun do rewrite EFinB; apply: integrableB => //; exact: intG.
  split; last exact: intG.
  have /= := Nb _ (leqnn n); rewrite /ball/= sub0r normrN -fine_abse// -lte_fin.
  by rewrite fineK ?abse_fin_num// => /le_lt_trans; apply; exact: lee_abs.
have mg : measurable_fun E g by exact: measurable_funTS.
have [M Mpos Mbd] : (exists2 M, 0 < M & forall x, `|g x| <= M)%R.
  have [M [_ /= bdM]] := simple_bounded g.
  exists (`|M| + 1)%R; first exact: ltr_pwDr.
  by move=> x; rewrite bdM// ltr_pwDr// ler_norm.
have [] // := @measurable_almost_continuous _ _ mE _ g (eps%:num / 2 / (M *+ 2)).
  by rewrite divr_gt0// mulrn_wgt0.
move=> A [cptA AE /= muAE ctsAF].
have [] := continuous_bounded_extension _ _ Mpos ctsAF.
- exact: pseudometric_normal.
- by apply: compact_closed => //; exact: Rhausdorff.
- by move=> ? ?; exact: Mbd.
have mA : measurable A := compact_measurable cptA.
move=> h [gh ctsh hbdM]; have mh : measurable_fun E h.
  by apply: subspace_continuous_measurable_fun=> //; exact: continuous_subspaceT.
have intg : mu.-integrable E (EFin \o h).
  apply: measurable_bounded_integrable => //.
  exists M; split; rewrite ?num_real // => x Mx y _ /=.
  by rewrite (le_trans _ (ltW Mx)).
exists h; split => //; rewrite [eps%:num]splitr; apply: le_lt_trans.
  pose fgh x := `|(f x - g x)%:E| + `|(g x - h x)%:E|.
  apply: (@ge0_le_integral _ _ _ mu _ mE _ fgh) => //.
  - apply: (measurable_funS mE) => //; do 2 apply: measurableT_comp => //.
    exact: measurable_funB.
  - by move=> z _; rewrite adde_ge0.
  - apply: measurableT_comp => //; apply: measurable_funD;
      apply: (measurable_funS mE (@subset_refl _ E));
      (apply: measurableT_comp => //);
      exact: measurable_funB.
  - move=> x _; rewrite -(subrK (g x) (f x)) -(addrA (_ + _)%R) lee_fin.
    by rewrite ler_normD.
rewrite integralD//; first last.
- by apply: integrable_abse; under eq_fun do rewrite EFinB; apply: integrableB.
- by apply: integrable_abse; under eq_fun do rewrite EFinB; apply: integrableB.
rewrite EFinD lteD// -(setDKU AE) ge0_integral_setU => //; first last.
- by rewrite /disj_set setDKI.
- rewrite setDKU //; do 2 apply: measurableT_comp => //.
  exact: measurable_funB.
- exact: measurableD.
rewrite (@ae_eq_integral _ _ _ mu A (cst 0)) //; first last.
- by apply: aeW => z Az; rewrite (gh z) ?inE// subrr abse0.
- apply: (measurable_funS mE) => //; do 2 apply: measurableT_comp => //.
  exact: measurable_funB.
rewrite integral0 adde0.
apply: (le_lt_trans (integral_le_bound (M *+ 2)%:E _ _ _ _)) => //.
- exact: measurableD.
- apply: (measurable_funS mE) => //; apply: measurableT_comp => //.
  exact: measurable_funB.
- by rewrite lee_fin mulrn_wge0// ltW.
- apply: aeW => z [Ez _]; rewrite /= lee_fin mulr2n.
  by rewrite (le_trans (ler_normB _ _))// lerD.
by rewrite -lte_pdivlMl ?mulrn_wgt0// muleC -EFinM.
Qed.

End continuous_density_L1.

Section fubini_functions.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Variable f : T1 * T2 -> \bar R.

Definition fubini_F x := \int[m2]_y f (x, y).
Definition fubini_G y := \int[m1]_x f (x, y).

End fubini_functions.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.

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
apply/funext => x/=.
rewrite -[RHS]mul1e -integral_cst//; last exact: measurable_xsection.
rewrite /F /fubini_F /f [in RHS]integral_mkcond.
by apply: eq_integral => y _ /=; rewrite patchE mem_xsection indicE; case: ifPn.
Qed.

Lemma indic_fubini_tonelli_GE : G = m1 \o ysection A.
Proof.
apply/funext => x/=.
rewrite -[RHS]mul1e -integral_cst//; last exact: measurable_ysection.
rewrite /G /fubini_G /f [in RHS]integral_mkcond.
by apply: eq_integral => y _ /=; rewrite patchE mem_ysection indicE; case: ifPn.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
by rewrite indic_fubini_tonelli_FE//; exact: measurable_fun_xsection.
Qed.

Lemma indic_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
by rewrite indic_fubini_tonelli_GE//; exact: measurable_fun_ysection.
Qed.

Lemma indic_fubini_tonelli1 : \int[m1 \x m2]_z (f z)%:E = \int[m1]_x F x.
Proof. by rewrite /f integral_indic// setIT indic_fubini_tonelli_FE. Qed.

Lemma indic_fubini_tonelli2 : \int[m1 \x^ m2]_z (f z)%:E = \int[m2]_y G y.
Proof. by rewrite /f integral_indic// setIT indic_fubini_tonelli_GE. Qed.

Lemma indic_fubini_tonelli : \int[m1]_x F x = \int[m2]_y G y.
Proof.
rewrite -indic_fubini_tonelli1// -indic_fubini_tonelli2// integral_indic//=.
rewrite integral_indic//= !setIT.
by apply: product_measure_unique => //= ? ? ? ?; rewrite product_measure2E.
Qed.

End indic_fubini_tonelli.

Section sfun_fubini_tonelli.
Variable f : {nnsfun T1 * T2 >-> R}.

Import HBNNSimple.

Let F := fubini_F m2 (EFin \o f).
Let G := fubini_G m1 (EFin \o f).

Lemma sfun_fubini_tonelli_FE : F = fun x =>
  \sum_(k \in range f) k%:E * m2 (xsection (f @^-1` [set k]) x).
Proof.
rewrite funeqE => x; rewrite /F /fubini_F [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/measurable_EFinP/measurableT_comp => //=.
    exact: measurableT_comp.
  - by move=> r y _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralZl//; last by rewrite lee_fin.
- by rewrite -/((m2 \o xsection _) x) -indic_fubini_tonelli_FE.
- exact/measurable_EFinP/measurableT_comp.
- by move=> y _; rewrite lee_fin.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_F : measurable_fun [set: T1] F.
Proof.
rewrite sfun_fubini_tonelli_FE//; apply: emeasurable_fsum => // r.
exact/measurable_funeM/measurable_fun_xsection.
Qed.

Lemma sfun_fubini_tonelli_GE : G = fun y =>
  \sum_(k \in range f) k%:E * m1 (ysection (f @^-1` [set k]) y).
Proof.
rewrite funeqE => y; rewrite /G /fubini_G [in LHS]/=.
under eq_fun do rewrite fimfunE -fsumEFin//.
rewrite ge0_integral_fsum //; last 2 first.
  - move=> i; apply/measurable_EFinP/measurableT_comp => //=.
    exact: measurableT_comp.
  - by move=> r x _; rewrite EFinM nnfun_muleindic_ge0.
apply: eq_fsbigr => i; rewrite inE => -[/= t _ <-{i}].
under eq_fun do rewrite EFinM.
rewrite ge0_integralZl//; last by rewrite lee_fin.
- by rewrite -/((m1 \o ysection _) y) -indic_fubini_tonelli_GE.
- exact/measurable_EFinP/measurableT_comp.
- by move=> x _; rewrite lee_fin.
Qed.

Lemma sfun_measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
rewrite sfun_fubini_tonelli_GE//; apply: emeasurable_fsum => // r.
exact/measurable_funeM/measurable_fun_ysection.
Qed.

Let EFinf x : (f x)%:E =
  \sum_(k \in range f) k%:E * (\1_(f @^-1` [set k]) x)%:E.
Proof. by rewrite fsumEFin //= fimfunE. Qed.

Lemma sfun_fubini_tonelli1 : \int[m1 \x m2]_z (f z)%:E = \int[m1]_x F x.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - by move=> r; exact/measurable_EFinP/measurableT_comp.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m1]_x (k%:E * fubini_F m2 (EFin \o \1_(f @^-1` [set k])) x)).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralZl//; last 3 first.
    - exact/measurable_EFinP.
    - by move=> /= x _; rewrite lee_fin.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli1// -ge0_integralZl//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_F.
  - by move=> /= x _; exact: indic_fubini_tonelli_F_ge0.
rewrite -ge0_integral_fsum; last by [].
  - apply: eq_integral => x _; rewrite sfun_fubini_tonelli_FE.
    by under eq_fsbigr do rewrite indic_fubini_tonelli_FE//.
  - by [].
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_F.
move=> r x _; rewrite /fubini_F.
have [r0|r0] := leP 0%R r.
  by rewrite mule_ge0//; exact: indic_fubini_tonelli_F_ge0.
rewrite integral0_eq ?mule0// => y _.
by rewrite preimage_nnfun0//= indicE in_set0.
Qed.

Lemma sfun_fubini_tonelli2 : \int[m1 \x^ m2]_z (f z)%:E = \int[m2]_y G y.
Proof.
under [LHS]eq_integral
  do rewrite EFinf; rewrite ge0_integral_fsum //; last 2 first.
  - by move=> i; exact/measurable_EFinP/measurableT_comp.
  - by move=> r /= z _; exact: nnfun_muleindic_ge0.
transitivity (\sum_(k \in range f)
  \int[m2]_x (k%:E * (fubini_G m1 (EFin \o \1_(f @^-1` [set k])) x))).
  apply: eq_fsbigr => i; rewrite inE => -[z _ <-{i}].
  rewrite ge0_integralZl//; last 3 first.
    - exact/measurable_EFinP.
    - by move=> /= x _; rewrite lee_fin.
    - by rewrite lee_fin.
  rewrite indic_fubini_tonelli2// -ge0_integralZl//; last by rewrite lee_fin.
  - exact: indic_measurable_fun_fubini_tonelli_G.
  - by move=> /= x _; exact: indic_fubini_tonelli_G_ge0.
rewrite -ge0_integral_fsum; last by [].
  - apply: eq_integral => x _; rewrite sfun_fubini_tonelli_GE.
    by under eq_fsbigr do rewrite indic_fubini_tonelli_GE//.
  - by [].
  - by move=> r; apply/measurable_funeM/indic_measurable_fun_fubini_tonelli_G.
move=> r y _; rewrite /fubini_G.
have [r0|r0] := leP 0%R r.
  by rewrite mule_ge0//; exact: indic_fubini_tonelli_G_ge0.
rewrite integral0_eq ?mule0// => x _.
by rewrite preimage_nnfun0//= indicE in_set0.
Qed.

Lemma sfun_fubini_tonelli :
  \int[m1 \x m2]_z (f z)%:E = \int[m1 \x^ m2]_z (f z)%:E.
Proof.
apply: eq_measure_integral => /= A Ameasurable _.
by apply: product_measure_unique => //= *; rewrite product_measure2E.
Qed.

End sfun_fubini_tonelli.

Section fubini_tonelli.
Variable f : T1 * T2 -> \bar R.
Hypothesis mf : measurable_fun setT f.
Hypothesis f0 : forall x, 0 <= f x.
Let T : measurableType _ := (T1 * T2)%type.

Let F := fubini_F m2 f.
Let G := fubini_G m1 f.

Import HBNNSimple.

Let F_ (g : {nnsfun T >-> R}^nat) n x := \int[m2]_y (g n (x, y))%:E.
Let G_ (g : {nnsfun T >-> R}^nat) n y := \int[m1]_x (g n (x, y))%:E.

Lemma measurable_fun_fubini_tonelli_F : measurable_fun setT F.
Proof.
pose g := nnsfun_approx measurableT mf.
apply: (emeasurable_fun_cvg (F_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> x _.
  rewrite /F_ /F /fubini_F [in X in _ --> X](_ : (fun _ => _) =
      fun y => limn (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => y; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP => //; exact/measurableT_comp.
  - by move=> n y _; rewrite lee_fin//; exact: fun_ge0.
  - by move=> y _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma measurable_fun_fubini_tonelli_G : measurable_fun setT G.
Proof.
pose g := nnsfun_approx measurableT mf.
apply: (emeasurable_fun_cvg (G_ g)) => //.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- move=> y _; rewrite /G_ /G /fubini_G [in X in _ --> X](_ : (fun _ => _) =
      fun x => limn (EFin \o g ^~ (x, y))); last first.
    by rewrite funeqE => x; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
  apply: cvg_monotone_convergence => //.
  - by move=> n; apply/measurable_EFinP => //; exact/measurableT_comp.
  - by move=> n x _; rewrite lee_fin; exact: fun_ge0.
  - by move=> x _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli1 : \int[m1 \x m2]_z f z = \int[m1]_x F x.
Proof.
pose g := nnsfun_approx measurableT mf.
have F_F x : F x = limn (F_ g ^~ x).
  rewrite [RHS](_ : _ = limn (fun n => \int[m2]_y (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/measurable_EFinP/measurableT_comp.
    - by move=> n /= y _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [RHS](_ : _ = limn (fun n => \int[m1 \x m2]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/measurable_EFinP.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [LHS](_ : _ =
    limn (fun n => \int[m1]_x (\int[m2]_y (EFin \o g n) (x, y)))).
  set r := fun _ => _; set l := fun _ => _; have -> // : l = r.
  by apply/funext  => n; rewrite /l /r sfun_fubini_tonelli1.
rewrite [RHS](_ : _ = limn (fun n => \int[m1]_x F_ g n x))//.
rewrite -monotone_convergence => [|//|||]; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_F.
- move=> n x _; apply: integral_ge0 => // y _ /=; rewrite lee_fin.
  exact: fun_ge0.
- move=> x /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> y _; rewrite lee_fin; exact: fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> *; rewrite lee_fin; exact: fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> y _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli2 : \int[m1 \x m2]_z f z = \int[m2]_y G y.
Proof.
pose g := nnsfun_approx measurableT mf.
have G_G y : G y = limn (G_ g ^~ y).
  rewrite /G /fubini_G.
  rewrite [RHS](_ : _ = limn (fun n => \int[m1]_x (EFin \o g n) (x, y)))//.
  rewrite -monotone_convergence//; last 3 first.
    - by move=> n; exact/measurable_EFinP/measurableT_comp.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> x /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [RHS](_ : _ = limn (fun n => \int[m1 \x m2]_z (EFin \o g n) z)).
  rewrite -monotone_convergence //; last 3 first.
    - by move=> n; exact/measurable_EFinP.
    - by move=> n /= x _; rewrite lee_fin; exact: fun_ge0.
    - by move=> y /= _ a b ab; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  by apply: eq_integral => /= x _; apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
rewrite [LHS](_ : _ = limn
    (fun n => \int[m2]_y (\int[m1]_x (EFin \o g n) (x, y)))).
  set r := fun _ => _; set l := fun _ => _; have -> // : l = r.
  by apply/funext => n; rewrite /l /r sfun_fubini_tonelli sfun_fubini_tonelli2.
rewrite [RHS](_ : _ = limn (fun n => \int[m2]_y G_ g n y))//.
rewrite -monotone_convergence => [|//|||]; first exact: eq_integral.
- by move=> n; exact: sfun_measurable_fun_fubini_tonelli_G.
- by move=> n y _; apply: integral_ge0 => // x _ /=; rewrite lee_fin fun_ge0.
- move=> y /= _ a b ab; apply: ge0_le_integral => //.
  + by move=> x _; rewrite lee_fin fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> *; rewrite lee_fin fun_ge0.
  + exact/measurable_EFinP/measurableT_comp.
  + by move=> x _; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
Qed.

Lemma fubini_tonelli :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite -fubini_tonelli1// fubini_tonelli2. Qed.

End fubini_tonelli.

End fubini_tonelli.
Arguments fubini_tonelli1 {d1 d2 T1 T2 R m1 m2} f.
Arguments fubini_tonelli2 {d1 d2 T1 T2 R m1 m2} f.
Arguments fubini_tonelli {d1 d2 T1 T2 R m1 m2} f.
Arguments measurable_fun_fubini_tonelli_F {d1 d2 T1 T2 R m2} f.
Arguments measurable_fun_fubini_tonelli_G {d1 d2 T1 T2 R m1} f.

Section fubini.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variable m1 : {sigma_finite_measure set T1 -> \bar R}.
Variable m2 : {sigma_finite_measure set T2 -> \bar R}.
Variable f : T1 * T2 -> \bar R.

Lemma integrable12ltyP : measurable_fun setT f ->
  (m1 \x m2).-integrable setT f <-> \int[m1]_x \int[m2]_y `|f (x, y)| < +oo.
Proof.
move=> mf; split=> [/integrableP[_]|] ioo; [|apply/integrableP; split=> [//|]].
- by rewrite -(fubini_tonelli1 (abse \o f))//=; exact: measurableT_comp.
- by rewrite fubini_tonelli1//; exact: measurableT_comp.
Qed.

Lemma integrable21ltyP : measurable_fun setT f ->
  (m1 \x m2).-integrable setT f <-> \int[m2]_y \int[m1]_x `|f (x, y)| < +oo.
Proof.
move=> mf; split=> [/integrableP[_]|] ioo; [|apply/integrableP; split=> [//|]].
- by rewrite -(fubini_tonelli2 (abse \o f))//=; exact: measurableT_comp.
- by rewrite fubini_tonelli2//; exact: measurableT_comp.
Qed.

Let measurable_fun1 : measurable_fun setT f ->
  measurable_fun setT (fun x => \int[m2]_y `|f (x, y)|).
Proof.
move=> mf; apply: (measurable_fun_fubini_tonelli_F (abse \o f)) => //=.
exact: measurableT_comp.
Qed.

Let measurable_fun2 : measurable_fun setT f ->
  measurable_fun setT (fun y => \int[m1]_x `|f (x, y)|).
Proof.
move=> mf; apply: (measurable_fun_fubini_tonelli_G (abse \o f)) => //=.
exact: measurableT_comp.
Qed.

Hypothesis imf : (m1 \x m2).-integrable setT f.
Let mf : measurable_fun setT f. Proof. exact: measurable_int imf. Qed.

Lemma ae_integrable1 :
  {ae m1, forall x, m2.-integrable setT (fun y => f (x, y))}.
Proof.
have : m1.-integrable setT (fun x => \int[m2]_y `|f (x, y)|).
  apply/integrableP; split; first exact/measurable_fun1.
  rewrite (le_lt_trans _  ((integrable12ltyP mf).1 imf))// ge0_le_integral //.
  - by apply: measurableT_comp => //; exact: measurable_fun1.
  - by move=> *; exact: integral_ge0.
  - exact: measurable_fun1.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT); apply: filterS => x /= /(_ I) im2f.
apply/integrableP; split; first exact/measurableT_comp.
by move/fin_numPlt : im2f => /andP[].
Qed.

Lemma ae_integrable2 :
  {ae m2, forall y, m1.-integrable setT (fun x => f (x, y))}.
Proof.
have : m2.-integrable setT (fun y => \int[m1]_x `|f (x, y)|).
  apply/integrableP; split; first exact/measurable_fun2.
  rewrite (le_lt_trans _ ((integrable21ltyP mf).1 imf))// ge0_le_integral //.
  - by apply: measurableT_comp => //; exact: measurable_fun2.
  - by move=> *; exact: integral_ge0.
  - exact: measurable_fun2.
  - by move=> *; rewrite gee0_abs//; exact: integral_ge0.
move/integrable_ae => /(_ measurableT); apply: filterS => x /= /(_ I) im2f.
apply/integrableP; split; first exact/measurableT_comp.
by move/fin_numPlt : im2f => /andP[].
Qed.

Let F := fubini_F m2 f.

Let Fplus x := \int[m2]_y f^\+ (x, y).
Let Fminus x := \int[m2]_y f^\- (x, y).

Let FE : F = Fplus \- Fminus.
Proof.
apply/funext=> x; rewrite [LHS]integralE.
under eq_integral do rewrite funepos_comp/=.
by under [X in _ - X = _]eq_integral do rewrite funeneg_comp/=.
Qed.

Let measurable_Fplus : measurable_fun setT Fplus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: measurable_funepos.
Qed.

Let measurable_Fminus : measurable_fun setT Fminus.
Proof.
by apply: measurable_fun_fubini_tonelli_F => //; exact: measurable_funeneg.
Qed.

Lemma measurable_fubini_F : measurable_fun setT F.
Proof.
rewrite FE.
by apply: emeasurable_funB; [exact: measurable_Fplus|exact: measurable_Fminus].
Qed.

Let integrable_Fplus : m1.-integrable setT Fplus.
Proof.
apply/integrableP; split=> //.
apply: le_lt_trans ((integrable12ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|..].
- by apply: measurableT_comp; last apply: measurable_Fplus.
- by move=> x _; exact: integral_ge0.
- exact: measurable_fun1.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funepos.
  apply: ge0_le_integral => //.
  - apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funepos.
  - by apply: measurableT_comp => //; exact/measurableT_comp.
  - by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDl.
Qed.

Let integrable_Fminus : m1.-integrable setT Fminus.
Proof.
apply/integrableP; split=> //.
apply: le_lt_trans ((integrable12ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|..].
- exact: measurableT_comp.
- by move=> *; exact: integral_ge0.
- exact: measurable_fun1.
- move=> x _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  + by apply: measurableT_comp => //; exact: measurableT_comp.
  + by move=> y _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDr.
Qed.

Lemma integrable_fubini_F : m1.-integrable setT F.
Proof. by rewrite FE; exact: integrableB. Qed.

Let G := fubini_G m1 f.

Let Gplus y := \int[m1]_x f^\+ (x, y).
Let Gminus y := \int[m1]_x f^\- (x, y).

Let GE : G = Gplus \- Gminus.
Proof.
apply/funext=> x; rewrite [LHS]integralE.
under eq_integral do rewrite funepos_comp/=.
by under [X in _ - X = _]eq_integral do rewrite funeneg_comp/=.
Qed.

Let measurable_Gplus : measurable_fun setT Gplus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: measurable_funepos.
Qed.

Let measurable_Gminus : measurable_fun setT Gminus.
Proof.
by apply: measurable_fun_fubini_tonelli_G => //; exact: measurable_funeneg.
Qed.

Lemma measurable_fubini_G : measurable_fun setT G.
Proof. by rewrite GE; exact: emeasurable_funB. Qed.

Let integrable_Gplus : m2.-integrable setT Gplus.
Proof.
apply/integrableP; split=> //; apply: le_lt_trans ((integrable21ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|exact: measurableT_comp|..].
- by move=> *; exact: integral_ge0.
- exact: measurable_fun2.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funepos.
  apply: ge0_le_integral => //.
  - apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funepos.
  - by apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDl.
Qed.

Let integrable_Gminus : m2.-integrable setT Gminus.
Proof.
apply/integrableP; split=> //; apply: le_lt_trans ((integrable21ltyP mf).1 imf).
apply: ge0_le_integral; [by []|by []|exact: measurableT_comp|..].
- by move=> *; exact: integral_ge0.
- exact: measurable_fun2.
- move=> y _; apply: le_trans.
    apply: le_abse_integral => //; apply: measurableT_comp => //.
    exact: measurable_funeneg.
  apply: ge0_le_integral => //.
  + apply: measurableT_comp => //.
    by apply: measurableT_comp => //; exact: measurable_funeneg.
  + by apply: measurableT_comp => //; exact: measurableT_comp.
  + by move=> x _; rewrite gee0_abs// -/((abse \o f) (x, y)) fune_abse leeDr.
Qed.

Lemma fubini1 : \int[m1]_x F x = \int[m1 \x m2]_z f z.
Proof.
rewrite FE integralB; [|by[]|exact: integrable_Fplus|exact: integrable_Fminus].
by rewrite [in RHS]integralE ?fubini_tonelli1//;
  [exact: measurable_funeneg|exact: measurable_funepos].
Qed.

Lemma fubini2 : \int[m2]_x G x = \int[m1 \x m2]_z f z.
Proof.
rewrite GE integralB; [|by[]|exact: integrable_Gplus|exact: integrable_Gminus].
by rewrite [in RHS]integralE ?fubini_tonelli2//;
  [exact: measurable_funeneg|exact: measurable_funepos].
Qed.

Theorem Fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite fubini1 -fubini2. Qed.

End fubini.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `integrable12ltyP`")]
Notation fubini1a := integrable12ltyP (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `integrable21ltyP`")]
Notation fubini1b := integrable21ltyP (only parsing).

Section sfinite_fubini.
Local Open Scope ereal_scope.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).
Variables (m1 : {sfinite_measure set X -> \bar R}).
Variables (m2 : {sfinite_measure set Y -> \bar R}).
Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
Hypothesis mf : measurable_fun setT f.

Lemma sfinite_Fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof.
pose s1 := sfinite_measure_seq m1.
pose s2 := sfinite_measure_seq m2.
rewrite [LHS](eq_measure_integral (mseries s1 0)); last first.
  by move=> A mA _; rewrite /=; exact: sfinite_measure_seqP.
transitivity (\int[mseries s1 0]_x \int[mseries s2 0]_y f (x, y)).
  apply: eq_integral => x _; apply: eq_measure_integral => ? ? _.
  exact: sfinite_measure_seqP.
transitivity (\sum_(n <oo) \int[s1 n]_x \sum_(m <oo) \int[s2 m]_y f (x, y)).
  rewrite ge0_integral_measure_series; [|by []| |]; last 2 first.
    by move=> t _; exact: integral_ge0.
    rewrite [X in measurable_fun _ X](_ : _ =
        fun x => \sum_(n <oo) \int[s2 n]_y f (x, y)); last first.
      apply/funext => x.
      by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
    apply: ge0_emeasurable_sum; first by move=> k x *; exact: integral_ge0.
    by move=> k _; exact: measurable_fun_fubini_tonelli_F.
  apply: eq_eseriesr => n _; apply: eq_integral => x _.
  by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[s1 n]_x \int[s2 m]_y f (x, y)).
  apply: eq_eseriesr => n _; rewrite integral_nneseries => [//|//||].
    by move=> m; exact: measurable_fun_fubini_tonelli_F.
  by move=> m x _; exact: integral_ge0.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[s2 m]_y \int[s1 n]_x f (x, y)).
  apply: eq_eseriesr => n _; apply: eq_eseriesr => m _.
  by rewrite fubini_tonelli//; exact: finite_measure_sigma_finite.
transitivity (\sum_(n <oo) \int[mseries s2 0]_y \int[s1 n]_x f (x, y)).
  apply: eq_eseriesr => n _; rewrite ge0_integral_measure_series => [//|//||].
    by move=> y _; exact: integral_ge0.
  exact: measurable_fun_fubini_tonelli_G.
transitivity (\int[mseries s2 0]_y \sum_(n <oo) \int[s1 n]_x f (x, y)).
  rewrite integral_nneseries => [//|//||].
    by move=> n; apply: measurable_fun_fubini_tonelli_G.
  by move=> n y _; exact: integral_ge0.
transitivity (\int[mseries s2 0]_y \int[mseries s1 0]_x f (x, y)).
  apply: eq_integral => y _.
  by rewrite ge0_integral_measure_series//; exact/measurableT_comp.
transitivity (\int[m2]_y \int[mseries s1 0]_x f (x, y)).
  by apply: eq_measure_integral => A mA _ /=; rewrite sfinite_measure_seqP.
apply: eq_integral => y _; apply: eq_measure_integral => A mA _ /=.
by rewrite sfinite_measure_seqP.
Qed.

End sfinite_fubini.
Arguments sfinite_Fubini {d d' X Y R} m1 m2 f.

Section lebesgue_differentiation_continuous.
Context (rT : realType).
Let mu : measure _ _ := @lebesgue_measure rT.
Let R  : measurableType _ := measurableTypeR rT.

Let ballE (x : R) (r : {posnum rT}) :
  ball x r%:num = `](x - r%:num), (x + r%:num)[%classic :> set rT.
Proof.
rewrite -ball_normE /ball_ set_itvoo.
by under eq_set => ? do rewrite ltr_distlC.
Qed.

Lemma lebesgue_differentiation_continuous (f : R -> rT^o) (A : set R) (x : R) :
  open A -> mu.-integrable A (EFin \o f) -> {for x, continuous f} -> A x ->
  (fun r => (r *+ 2)^-1 * \int[mu]_(z in ball x r) f z) @ 0^'+ -->
  (f x : R^o).
Proof.
have ball_itvr r : 0 < r -> `[x - r, x + r] `\` ball x r = [set x + r; x - r].
  move: r => _/posnumP[r].
  rewrite -setU1itv ?bnd_simp ?lerBlDr -?addrA ?ler_wpDr//.
  rewrite -setUitv1 ?bnd_simp ?ltrBlDr -?addrA ?ltr_pwDr//.
  rewrite setUA setUC setUA setDUl !ballE setDv setU0 setDidl// -subset0.
  by move=> z /= [[]] ->; rewrite in_itv/= ltxx// andbF.
have ball_itv2 r : 0 < r -> ball x r = `[x - r, x + r] `\` [set x + r; x - r].
  move: r => _/posnumP[r].
  rewrite -ball_itvr // setDD setIC; apply/esym/setIidPl.
  by rewrite ballE set_itvcc => ?/=; rewrite in_itv => /andP [/ltW -> /ltW ->].
have ritv r : 0 < r -> mu `[x - r, x + r]%classic = (r *+ 2)%:E.
  move=> /gt0_cp rE; rewrite /= lebesgue_measure_itv/= lte_fin.
  rewrite ler_ltD // ?rE // -EFinD; congr (_ _).
  by rewrite opprB addrAC [_ - _]addrC addrA subrr add0r.
move=> oA intf ctsfx Ax.
apply: cvg_zero.
apply/cvgrPdist_le => eps epos; apply: filter_app (@nbhs_right_gt rT 0).
move/cvgrPdist_le/(_ eps epos)/at_right_in_segment : ctsfx; apply: filter_app.
apply: filter_app (open_itvcc_subset oA Ax).
have mA : measurable A := open_measurable oA.
near=> r => xrA; rewrite addrfctE opprfctE => feps rp.
have cptxr : compact `[x - r, x + r] := @segment_compact _ _ _.
rewrite distrC subr0.
have -> : \int[mu]_(z in ball x r) f z = \int[mu]_(z in `[x - r, x + r]) f z.
  rewrite ball_itv2 //; congr (fine _); rewrite -negligible_integral //.
  - by apply/measurableU; exact: measurable_set1.
  - exact: (integrableS mA).
  - by rewrite measureU0//; exact: lebesgue_measure_set1.
have r20 : 0 <= (r *+ 2)^-1 by rewrite invr_ge0 mulrn_wge0.
have -> : f x = (r *+ 2)^-1 * \int[mu]_(z in `[x - r, x + r]) cst (f x) z.
  rewrite Rintegral_cst// ritv//= mulrA mulrAC mulVf ?mul1r//.
  by apply: lt0r_neq0; rewrite mulrn_wgt0.
have intRf : mu.-integrable `[x - r, x + r] (EFin \o f).
  exact: (@integrableS _ _ _ mu _ _ _ _ _ xrA intf).
rewrite /= -mulrBr -fineB; first last.
- rewrite integral_fune_fin_num// continuous_compact_integrable// => ?.
  exact: cvg_cst.
- by rewrite integral_fune_fin_num.
rewrite -integralB_EFin //; first last.
  by apply: continuous_compact_integrable => // ?; exact: cvg_cst.
under [fun _ => _ + _ ]eq_fun => ? do rewrite -EFinD.
have int_fx : mu.-integrable `[x - r, x + r] (fun z => (f z - f x)%:E).
  under [fun z => (f z - _)%:E]eq_fun => ? do rewrite EFinB.
  rewrite integrableB// continuous_compact_integrable// => ?.
  exact: cvg_cst.
rewrite normrM ger0_norm // -fine_abse //; first last.
  by rewrite integral_fune_fin_num.
suff : (\int[mu]_(z in `[(x - r)%R, (x + r)%R]) `|f z - f x|%:E <=
    (r *+ 2 * eps)%:E)%E.
  move=> intfeps; apply: le_trans.
    apply: (ler_pM r20 _ (le_refl _)); first exact: fine_ge0.
    apply: fine_le; last apply: le_abse_integral => //.
    - by rewrite abse_fin_num integral_fune_fin_num.
    - by rewrite integral_fune_fin_num// integrable_abse.
    - by case/integrableP : int_fx.
  rewrite ler_pdivrMl ?mulrn_wgt0 // -[_ * _]/(fine (_%:E)).
  by rewrite fine_le// integral_fune_fin_num// integrable_abse.
apply: le_trans.
- apply: (@integral_le_bound _ _ _ _ _ (fun z => (f z - f x)%:E) eps%:E) => //.
  + by case/integrableP: int_fx.
  + exact: ltW.
  + by apply: aeW => ? ?; rewrite /= lee_fin distrC feps.
by rewrite ritv //= -EFinM lee_fin mulrC.
Unshelve. all: by end_near. Qed.

End lebesgue_differentiation_continuous.

Section locally_integrable.
Context {R : realType}.
Implicit Types (D : set R) (f g : R -> R).
Local Open Scope ereal_scope.

Local Notation mu := lebesgue_measure.

Definition locally_integrable D f := [/\ measurable_fun D f, open D &
  forall K, K `<=` D -> compact K -> \int[mu]_(x in K) `|f x|%:E < +oo].

Lemma open_integrable_locally D f : open D ->
  mu.-integrable D (EFin \o f) -> locally_integrable D f.
Proof.
move=> oD /integrableP[mf foo]; split => //; first exact/measurable_EFinP.
move=> K KD cK; rewrite (le_lt_trans _ foo)// ge0_subset_integral//=.
- exact: compact_measurable.
- exact: open_measurable.
- apply/measurable_EFinP; apply: measurableT_comp => //.
  exact/measurable_EFinP.
Qed.

Lemma locally_integrableN D f :
  locally_integrable D f -> locally_integrable D (\- f)%R.
Proof.
move=> [mf oD foo]; split => //; first exact: measurableT_comp.
by move=> K KD cK; under eq_integral do rewrite normrN; exact: foo.
Qed.

Lemma locally_integrableD D f g :
  locally_integrable D f -> locally_integrable D g ->
  locally_integrable D (f \+ g)%R.
Proof.
move=> [mf oD foo] [mg _ goo]; split => //; first exact: measurable_funD.
move=> K KD cK.
suff : lebesgue_measure.-integrable K ((EFin \o f) \+ (EFin \o g)).
  by case/integrableP.
apply: integrableD => //=; first exact: compact_measurable.
- apply/integrableP; split; last exact: foo.
  apply/measurable_EFinP; apply: measurable_funS mf => //.
  exact: open_measurable.
- apply/integrableP; split; last exact: goo.
  apply/measurable_EFinP; apply: measurable_funS mg => //.
  exact: open_measurable.
Qed.

Lemma locally_integrableB D f g :
  locally_integrable D f -> locally_integrable D g ->
  locally_integrable D (f \- g)%R.
Proof.
by move=> lf lg; apply: locally_integrableD => //; exact: locally_integrableN.
Qed.

Lemma locally_integrable_indic D (A : set R) :
  open D -> measurable A -> locally_integrable D \1_A.
Proof.
move=> oU mA; split => // K KD_ cK.
apply: (@le_lt_trans _ _ (\int[mu]_(x in K) cst 1 x)).
  apply: ge0_le_integral => //=; first exact: compact_measurable.
  - by do 2 apply: measurableT_comp => //.
  - move=> y Kx; rewrite indicE.
    by case: (y \in A) => /=; rewrite ?(normr1,normr0,lexx,lee01).
by rewrite integral_cst//= ?mul1e; [exact: compact_finite_measure|
                                    exact: compact_measurable].
Qed.

Lemma locally_integrableS (A B : set R) f :
  measurable A -> measurable B -> A `<=` B ->
  locally_integrable setT (f \_ B) -> locally_integrable setT (f \_ A).
Proof.
move=> mA mB AB [mfB oT ifB].
have ? : measurable_fun [set: R] (f \_ A).
  apply/(measurable_restrictT _ _).1 => //; apply: (measurable_funS _ AB) => //.
  exact/(measurable_restrictT _ _).2.
split => // K KT cK; apply: le_lt_trans (ifB _ KT cK).
apply: ge0_le_integral => //=; first exact: compact_measurable.
- apply/measurable_EFinP; apply/measurableT_comp => //.
  exact/measurable_funTS.
- apply/measurable_EFinP; apply/measurableT_comp => //.
  exact/measurable_funTS.
- move=> x Kx; rewrite lee_fin !patchE.
  case: ifPn => xA; case: ifPn => xB //; last by rewrite normr0.
  move: AB => /(_ x).
  by move/set_mem : xA => /[swap] /[apply] /mem_set; rewrite (negbTE xB).
Qed.

Lemma integrable_locally_restrict f (A : set R) : measurable A ->
  mu.-integrable A (EFin \o f) -> locally_integrable [set: R] (f \_ A).
Proof.
move=> mA intf; split.
- move/integrableP : intf => [mf _].
  by apply/(measurable_restrictT _ _).1 => //; exact/measurable_EFinP.
- exact: openT.
- move=> K _ cK.
  move/integrableP : intf => [mf].
  rewrite integral_mkcond/=.
  under eq_integral do rewrite restrict_EFin restrict_normr.
  apply: le_lt_trans.
  apply: ge0_subset_integral => //=; first exact: compact_measurable.
  apply/measurable_EFinP/measurableT_comp/measurable_EFinP => //=.
  move/(measurable_restrictT _ _).1 : mf => /=.
  by rewrite restrict_EFin; exact.
Qed.

End locally_integrable.

Section iavg.
Context {R : realType}.
Implicit Types (D A : set R) (f g : R -> R).
Local Open Scope ereal_scope.

Local Notation mu := lebesgue_measure.

Definition iavg f A := (fine (mu A))^-1%:E * \int[mu]_(y in A) `| (f y)%:E |.

Lemma iavg0 f : iavg f set0 = 0.
Proof. by rewrite /iavg integral_set0 mule0. Qed.

Lemma iavg_ge0 f A : 0 <= iavg f A.
Proof.
by rewrite /iavg mule_ge0 ?integral_ge0// lee_fin invr_ge0// fine_ge0.
Qed.

Lemma iavg_restrict f D A : measurable D -> measurable A ->
  iavg (f \_ D) A = ((fine (mu A))^-1)%:E * \int[mu]_(y in D `&` A) `|f y|%:E.
Proof.
move=> mD mA; rewrite /iavg setIC [in RHS]integral_mkcondr/=; congr *%E.
apply: eq_integral => /= y yx1.
by rewrite [in RHS]restrict_EFin/= restrict_normr.
Qed.

Lemma iavgD f g A : measurable A -> mu A < +oo ->
  measurable_fun A f -> measurable_fun A g ->
  iavg (f \+ g)%R A <= iavg f A + iavg g A.
Proof.
move=> mA Aoo mf mg; have [r0|r0] := eqVneq (mu A) 0.
  by rewrite /iavg r0/= invr0 !mul0e adde0.
rewrite -muleDr//=; last by rewrite ge0_adde_def// inE integral_ge0.
rewrite lee_pmul2l//; last first.
  by rewrite lte_fin invr_gt0// fine_gt0// Aoo andbC/= lt0e r0/=.
rewrite -ge0_integralD//=; [|by do 2 apply: measurableT_comp..].
apply: ge0_le_integral => //=.
- by do 2 apply: measurableT_comp => //; exact: measurable_funD.
- by move=> /= x _; rewrite adde_ge0.
- by apply: measurableT_comp => //; apply: measurable_funD => //;
    exact: measurableT_comp.
- by move=> /= x _; exact: ler_normD.
Qed.

End iavg.

Section hardy_littlewood.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Types (D : set R) (f : R -> R).
Local Open Scope ereal_scope.

Definition HL_maximal f (x : R) : \bar R :=
  ereal_sup [set iavg f (ball x r) | r in `]0, +oo[%classic%R].

Local Notation HL := HL_maximal.

Lemma HL_maximal_ge0 f D : locally_integrable D f ->
  forall x, 0 <= HL (f \_ D) x.
Proof.
move=> Df x; apply: ereal_sup_le => //=.
pose k := \int[mu]_(x in D `&` ball x 1) `|f x|%:E.
exists ((fine (mu (ball x 1)))^-1%:E * k); last first.
  rewrite mule_ge0 ?integral_ge0//.
  by rewrite lee_fin// invr_ge0// fine_ge0.
exists 1%R; first by rewrite in_itv/= ltr01.
rewrite iavg_restrict//; last exact: measurable_ball.
by case: Df => _ /open_measurable.
Qed.

Lemma HL_maximalT_ge0 f : locally_integrable setT f -> forall x, 0 <= HL f x.
Proof. by move=> + x => /HL_maximal_ge0 /(_ x); rewrite patch_setT. Qed.

Let locally_integrable_ltbally (f : R -> R) (x r : R) :
  locally_integrable setT f -> \int[mu]_(y in ball x r) `|(f y)%:E| < +oo.
Proof.
move=> [mf _ locf]; have [r0|r0] := leP r 0%R.
  by rewrite (ball0 _ _).2// integral_set0.
rewrite (le_lt_trans _ (locf (closed_ball x r) _ (closed_ballR_compact _)))//.
apply: ge0_subset_integral => //; first exact: measurable_ball.
- by apply: measurable_closed_ball; exact/ltW.
- apply: measurable_funTS; apply/measurableT_comp => //=.
  exact: measurableT_comp.
- exact: subset_closed_ball.
Qed.

Lemma lower_semicontinuous_HL_maximal f :
  locally_integrable setT f -> lower_semicontinuous (HL f).
Proof.
move=> [mf ? locf]; apply/lower_semicontinuousP => a.
have [a0|a0] := lerP 0 a; last first.
  rewrite [X in open X](_ : _ = setT); first exact: openT.
  by apply/seteqP; split=> // x _; exact: (lt_le_trans _ (HL_maximalT_ge0 _ _)).
rewrite openE /= => x /= /ereal_sup_gt[_ [r r0] <-] afxr.
rewrite /= in_itv /= andbT in r0.
rewrite /iavg in afxr; set k := \int[_]_(_ in _) _ in afxr.
apply: nbhs_singleton; apply: nbhs_interior; rewrite nbhsE /=.
have k_gt0 : 0 < k.
  rewrite lt0e integral_ge0// andbT; apply/negP => /eqP k0.
  by move: afxr; rewrite k0 mule0 lte_fin ltNge a0.
move: a0; rewrite le_eqVlt => /predU1P[a0|a0].
  move: afxr; rewrite -{a}a0 => xrk.
  near (0%R : R)^'+ => d.
  have xrdk : 0 < (fine (mu (ball x (r + d))))^-1%:E * k.
    rewrite mule_gt0// lte_fin invr_gt0// fine_gt0//.
    rewrite lebesgue_measure_ball; last by rewrite addr_ge0// ltW.
    by rewrite ltry andbT lte_fin pmulrn_lgt0// addr_gt0.
  exists (ball x d).
    by split; [exact: ball_open|exact: ballxx].
  move=> y; rewrite /ball/= => xyd.
  have ? : ball x r `<=` ball y (r + d).
    move=> /= z; rewrite /ball/= => xzr; rewrite -(subrK x y) -(addrA (y - x)%R).
    by rewrite (le_lt_trans (ler_normD _ _))// [ltLHS]addrC ltrD// distrC.
  have ? : k <= \int[mu]_(y in ball y (r + d)) `|(f y)%:E|.
    apply: ge0_subset_integral =>//; [exact:measurable_ball|
                                      exact:measurable_ball|].
    exact/measurable_funTS/measurableT_comp/measurableT_comp.
  have : iavg f (ball y (r + d)) <= HL f y.
    apply: ereal_sup_ubound => /=; exists (r + d)%R => //.
    by rewrite in_itv/= andbT addr_gt0.
  apply/lt_le_trans/(lt_le_trans xrdk); rewrite /iavg.
  do 2 (rewrite lebesgue_measure_ball; last by rewrite addr_ge0// ltW).
  rewrite lee_wpmul2l// lee_fin invr_ge0// fine_ge0// lee_fin pmulrn_rge0//.
  by rewrite addr_gt0.
have ka_pos : fine k / a \is Num.pos.
  by rewrite posrE divr_gt0// fine_gt0 // k_gt0/= locally_integrable_ltbally.
have k_fin_num : k \is a fin_num.
  by rewrite ge0_fin_numE ?locally_integrable_ltbally ?integral_ge0.
have kar : (0 < 2^-1 * (fine k / a) - r)%R.
  move: afxr; rewrite -{1}(fineK k_fin_num) -lte_pdivrMr; last first.
    by rewrite fine_gt0// k_gt0/= ltey_eq k_fin_num.
  rewrite (lebesgue_measure_ball _ (ltW r0))//.
  rewrite -!EFinM !lte_fin -invf_div ltf_pV2 ?posrE ?pmulrn_lgt0//.
  rewrite /= -[in X in X -> _]mulr_natl -ltr_pdivlMl//.
  by rewrite -[in X in X -> _]subr_gt0.
near (0%R : R)^'+ => d.
have axrdk : a%:E < (fine (mu (ball x (r + d))))^-1%:E * k.
  rewrite lebesgue_measure_ball//; last by rewrite addr_ge0// ltW.
  rewrite -(fineK k_fin_num) -lte_pdivrMr; last first.
    by rewrite fine_gt0// k_gt0/= locally_integrable_ltbally.
  rewrite -!EFinM !lte_fin -invf_div ltf_pV2//; last first.
    by rewrite posrE fine_gt0// ltry andbT lte_fin pmulrn_lgt0// addr_gt0.
  rewrite -mulr_natl -ltr_pdivlMl// -ltrBrDl.
  by near: d; exact: nbhs_right_lt.
exists (ball x d).
  by split; [exact: ball_open|exact: ballxx].
move=> y; rewrite /ball/= => xyd.
have ? : ball x r `<=` ball y (r + d).
  move=> /= z; rewrite /ball/= => xzr; rewrite -(subrK x y) -(addrA (y - x)%R).
  by rewrite (le_lt_trans (ler_normD _ _))// [ltLHS]addrC ltrD// distrC.
have ? : k <= \int[mu]_(z in ball y (r + d)) `|(f z)%:E|.
  apply: ge0_subset_integral => //; [exact: measurable_ball|
                                     exact: measurable_ball|].
  exact/measurable_funTS/measurableT_comp/measurableT_comp.
have afxrdi : a%:E < (fine (mu (ball x (r + d))))^-1%:E *
    \int[mu]_(z in ball y (r + d)) `|(f z)%:E|.
  apply/(lt_le_trans axrdk)/lee_wpmul2l => //.
  by rewrite lee_fin invr_ge0 fine_ge0.
have /lt_le_trans : a%:E < iavg f (ball y (r + d)).
  apply: (lt_le_trans afxrdi); rewrite /iavg.
  do 2 (rewrite lebesgue_measure_ball; last by rewrite addr_ge0// ltW).
  rewrite lee_wpmul2l ?lexx// lee_fin invr_ge0// fine_ge0//= lee_fin.
  by rewrite pmulrn_rge0// addr_gt0.
apply; apply: ereal_sup_ubound => /=.
by exists (r + d)%R => //; rewrite in_itv/= andbT addr_gt0.
Unshelve. all: by end_near. Qed.

Lemma measurable_HL_maximal f :
  locally_integrable setT f -> measurable_fun setT (HL f).
Proof.
move=> lf; apply: lower_semicontinuous_measurable.
exact: lower_semicontinuous_HL_maximal.
Qed.

Let norm1 D f := \int[mu]_(y in D) `|(f y)%:E|.

Lemma maximal_inequality f c :
  locally_integrable setT f -> (0 < c)%R ->
  mu [set x | HL f x > c%:E] <= (3 / c)%:E * norm1 setT f.
Proof.
move=> /= locf c0.
rewrite lebesgue_regularity_inner_sup//; last first.
  rewrite -[X in measurable X]setTI; apply: emeasurable_fun_o_infty => //.
  exact: measurable_HL_maximal.
apply: ub_ereal_sup => /= x /= [K [cK Kcmf <-{x}]].
have r_proof x : HL f x > c%:E -> {r | (0 < r)%R & iavg f (ball x r) > c%:E}.
  move=> /ereal_sup_gt/cid2[y /= /cid2[r]].
  by rewrite in_itv/= andbT => rg0 <-{y} Hc; exists r.
pose r_ x :=
  if pselect (HL f x > c%:E) is left H then s2val (r_proof _ H) else 1%R.
have r_pos (x : R) : (0 < r_ x)%R.
  by rewrite /r_; case: pselect => //= cMfx; case: (r_proof _ cMfx).
have cMfx_int x : c%:E < HL f x ->
    \int[mu]_(y in ball x (r_ x)) `|(f y)|%:E > c%:E * mu (ball x (r_ x)).
  move=> cMfx; rewrite /r_; case: pselect => //= => {}cMfx.
  case: (r_proof _ cMfx) => /= r r0.
  have ? : 0 < (fine (mu (ball x r)))%:E.
    rewrite lte_fin fine_gt0// (lebesgue_measure_ball _ (ltW r0))// ltry.
    by rewrite lte_fin mulrn_wgt0.
  rewrite /iavg -(@lte_pmul2r _ (fine (mu (ball x r)))%:E)//.
  rewrite muleAC -[in X in _ < X]EFinM mulVf ?gt_eqF// mul1e fineK//.
  by rewrite ge0_fin_numE// (lebesgue_measure_ball _ (ltW r0)) ltry.
set B := fun r => ball r (r_ r).
have {}Kcmf : K `<=` cover [set i | HL f i > c%:E] (fun i => ball i (r_ i)).
  by move=> r /Kcmf /= cMfr; exists r => //; exact: ballxx.
have {Kcmf}[D Dsub Kcover] : finite_subset_cover [set i | c%:E < HL f i]
    (fun i => ball i (r_ i)) K.
  move: cK; rewrite compact_cover => /(_ _ _ _ _ Kcmf); apply.
  by move=> /= x cMfx; exact/ball_open/r_pos.
have KDB : K `<=` cover [set` D] B.
  by apply: (subset_trans Kcover) => /= x [r Dr] rx; exists r.
have is_ballB i : is_ball (B i) by exact: is_ball_ball.
have Bset0 i : B i !=set0 by exists i; exact: ballxx.
have [E [uE ED tEB DE]] := @vitali_lemma_finite_cover _ _ B is_ballB Bset0 D.
rewrite (@le_trans _ _ (3%:E * \sum_(i <- E) mu (B i)))//.
  have {}DE := subset_trans KDB DE.
  apply: (le_trans (@content_subadditive _ _ _ mu K
      (fun i => 3 *` B (nth 0%R E i)) (size E) _ _ _)) => //.
  - by move=> k ?; rewrite scale_ballE//; exact: measurable_ball.
  - by apply: closed_measurable; apply: compact_closed => //; exact: Rhausdorff.
  - apply: (subset_trans DE); rewrite /cover bigcup_seq.
    by rewrite (big_nth 0%R)//= big_mkord.
  - rewrite ge0_sume_distrr//= (big_nth 0%R) big_mkord; apply: lee_sum => i _.
    rewrite scale_ballE// !lebesgue_measure_ball ?mulr_ge0 ?(ltW (r_pos _))//.
    by rewrite -mulrnAr EFinM.
rewrite !EFinM -muleA lee_wpmul2l//=.
apply: (@le_trans _ _ (\sum_(i <- E) c^-1%:E * \int[mu]_(y in B i) `|f y|%:E)).
  rewrite [in leLHS]big_seq [in leRHS]big_seq; apply: lee_sum => r /ED /Dsub /[!inE] rD.
  by rewrite -lee_pdivrMl ?invr_gt0// invrK /B/=; exact/ltW/cMfx_int.
rewrite -ge0_sume_distrr; last by move=> x _; rewrite integral_ge0.
rewrite lee_wpmul2l//; first by rewrite lee_fin invr_ge0 ltW.
rewrite -ge0_integral_bigsetU//=.
- apply/ge0_subset_integral => //.
  + by apply/bigsetU_measurable => ? ?; exact: measurable_ball.
  + by apply/measurableT_comp/measurableT_comp; last case: locf.
- by move=> n; exact: measurable_ball.
- apply: measurableT_comp => //; apply: measurable_funTS.
  by apply: measurableT_comp => //; case: locf.
Qed.

End hardy_littlewood.

Section davg.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types f g : R -> R.

Definition davg f x (r : R) := iavg (center (f x) \o f) (ball x r).

Lemma davg0 f x (r : R) : (r <= 0)%R -> davg f x r = 0.
Proof. by move=> r0; rewrite /davg/= (ball0 _ _).2//= iavg0. Qed.

Lemma davg_ge0 f x (r : R) : 0 <= davg f x r. Proof. exact: iavg_ge0. Qed.

Lemma davgD f g (x r : R) :
  measurable_fun (ball x r) f -> measurable_fun (ball x r) g ->
  davg (f \+ g)%R x r <= (davg f x \+ davg g x) r.
Proof.
move=> mf mg; rewrite (le_trans _ (iavgD _ _ _ _)) //.
- rewrite le_eqVlt; apply/orP; left; apply/eqP => /=; congr iavg.
  by apply/funext => e /=; rewrite opprD addrACA.
- exact: measurable_ball.
- have [r0|r0] := leP r 0%R; first by rewrite (ball0 _ _).2// measure0.
  by rewrite (lebesgue_measure_ball _ (ltW r0)) ltry.
- exact: measurable_funB.
- exact: measurable_funB.
Qed.

Lemma near_davg f (a : itv_bound R) x (u : R) : (x < u)%R -> (a < BRight x)%E ->
  \forall r \near 0^'+,
    davg f x r = davg (f \_ [set` Interval a (BRight u)]) x r.
Proof.
move=> xu; move: a => [b a /=|[_|//]].
- move=> ax; near=> r.
  have fauf : {in ball x r : set R,
      f \_ [set` Interval (BSide b a) (BRight u)] =1 f}.
    move=> y.
    rewrite ball_itv/= inE/= => yxr; rewrite patchE/= mem_set//=.
    apply: subset_itvW yxr.
      rewrite lerBrDl -lerBrDr.
      by near: r; apply: nbhs_right_ltW; rewrite subr_gt0.
    rewrite -lerBrDl.
    by near: r; apply: nbhs_right_le; rewrite subr_gt0.
  congr *%E; apply: eq_integral => y yxr /=.
  by rewrite fauf// fauf// inE; exact: ballxx.
- near=> r.
  have foouf : {in (ball x r : set R), f \_ `]-oo, u] =1 f}.
    move=> y.
    rewrite ball_itv/= inE/= => yxr; rewrite patchE/= mem_set//=.
    move: yxr; rewrite !in_itv/= => /andP[_ /ltW/le_trans]; apply.
    rewrite -lerBrDl.
    by near: r; apply: nbhs_right_ltW; rewrite subr_gt0.
  congr *%E; apply: eq_integral => y yxr /=.
  by rewrite foouf// foouf// inE; exact: ballxx.
Unshelve. all: by end_near. Qed.

Section continuous_cvg_davg.
Context f (x : R) (U : set R).
Hypotheses (xU : open_nbhs x U) (mU : measurable U) (mUf : measurable_fun U f)
           (fx : {for x, continuous f}).

Let continuous_integralB_fin_num :
  \forall t \near 0%R,
    \int[mu]_(y in ball x t) `|(f y)%:E - (f x)%:E| \is a fin_num.
Proof.
move: fx => /cvgrPdist_le /= fx'.
near (0%R:R)^'+ => e.
have e0 : (0 < e)%R by near: e; exact: nbhs_right_gt.
have [r /= r0 {}fx'] := fx' _ e0.
have [d/= d0 dxU] := open_subball xU.1 xU.2.
near=> t; rewrite ge0_fin_numE ?integral_ge0//.
have [t0|t0] := leP t 0%R; first by rewrite ((ball0 _ _).2 t0) integral_set0.
have xtU : ball x t `<=` U by apply: dxU => //=.
rewrite (@le_lt_trans _ _ (\int[mu]_(y in ball x t) e%:E))//; last first.
  rewrite integral_cst//=; last exact: measurable_ball.
  by rewrite (lebesgue_measure_ball _ (ltW t0)) ltry.
apply: ge0_le_integral => //=; first exact: measurable_ball.
- by do 2 apply: measurableT_comp => //=; apply: measurable_funB;
    [exact: measurable_funS mUf|exact: measurable_cst].
- by move=> y _; rewrite lee_fin.
- move=> y xry; rewrite lee_fin distrC fx'//=; apply: (lt_le_trans xry).
  by near: t; exact: nbhs0_ltW.
Unshelve. all: by end_near. Qed.

Let continuous_davg_fin_num :
  \forall A \near 0%R, davg f x A \is a fin_num.
Proof.
have [e /= e0 exf] := continuous_integralB_fin_num.
move: fx => /cvgrPdist_le fx'.
near (0%R:R)^'+ => r.
have r0 : (0 < r)%R by near: r; exact: nbhs_right_gt.
have [d /= d0 {}fx'] := fx' _ e0.
near=> t; have [t0|t0] := leP t 0%R; first by rewrite davg0.
by rewrite fin_numM// exf/=.
Unshelve. all: by end_near. Qed.

Lemma continuous_cvg_davg : davg f x r @[r --> 0%R] --> 0.
Proof.
apply/fine_cvgP; split; first exact: continuous_davg_fin_num.
apply/cvgrPdist_le => e e0.
move: fx => /cvgrPdist_le /= fx'.
have [r /= r0 {}fx'] := fx' _ e0.
have [d /= d0 dfx] := continuous_davg_fin_num.
have [l/= l0 lxU] := open_subball xU.1 xU.2.
near=> t.
have [t0|t0] := leP t 0%R; first by rewrite /= davg0//= subrr normr0 ltW.
rewrite sub0r normrN /= ger0_norm; last by rewrite fine_ge0// davg_ge0.
rewrite -lee_fin fineK//; last by rewrite dfx//= sub0r normrN gtr0_norm.
rewrite /davg/= /iavg/= lee_pdivrMl//; last first.
  by rewrite fine_gt0// lebesgue_measure_ball// ?ltry ?lte_fin ?mulrn_wgt0 ?ltW.
rewrite (@le_trans _ _ (\int[mu]_(y in ball x t) e%:E))//.
  apply: ge0_le_integral => //=.
  - exact: measurable_ball.
  - do 2 apply: measurableT_comp => //=; apply: measurable_funB => //.
    by apply: measurable_funS mUf => //; apply: lxU => //=.
  - by move=> y xty; rewrite lee_fin ltW.
  - move=> y xty; rewrite lee_fin distrC fx'//; apply: (lt_le_trans xty).
    by near: t; exact: nbhs0_ltW.
rewrite integral_cst//=; last exact: measurable_ball.
by rewrite muleC fineK// (lebesgue_measure_ball _ (ltW t0)).
Unshelve. all: by end_near. Qed.

End continuous_cvg_davg.

End davg.

Section lim_sup_davg.
Context {R : realType}.
Local Open Scope ereal_scope.
Implicit Types f g : R -> R.

Definition lim_sup_davg f x := lime_sup (davg f x) 0.

Local Notation "f ^*" := (lim_sup_davg f).

Lemma lim_sup_davg_ge0 f x : 0 <= f^* x.
Proof. by apply: limf_esup_ge0 => // => y; exact: iavg_ge0. Qed.

Lemma lim_sup_davg_le f g x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> measurable_fun U g ->
  (f \+ g)%R^* x <= (f^* \+ g^*) x.
Proof.
move=> xU mY mf /= mg; apply: le_trans (lime_supD _); last first.
  by rewrite ge0_adde_def// inE; exact: lim_sup_davg_ge0.
have [e/= e0 exU] := open_subball xU.1 xU.2.
apply: lime_sup_le; near=> r => y; rewrite neq_lt => /orP[y0|y0 ry].
  by rewrite !davg0 ?adde0// ltW.
apply: davgD.
  apply: measurable_funS mf => //; apply: exU => //=.
  by rewrite (lt_le_trans ry)//; near: r; exact: nbhs_right_le.
apply: measurable_funS mg => //; apply: exU => //=.
by rewrite (lt_le_trans ry)//; near: r; exact: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma continuous_lim_sup_davg f x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> {for x, continuous f} ->
  f^* x = 0.
Proof.
move=> xU mU mUf ctsf.
by have /lim_lime_sup := continuous_cvg_davg xU mU mUf ctsf.
Qed.

Lemma lim_sup_davgB f g x (U : set R) : open_nbhs x U -> measurable U ->
  measurable_fun U f -> {for x, continuous g} ->
  locally_integrable [set: R] g -> (f \- g)%R^* x = f^* x.
Proof.
move=> xU mU mUf cg locg; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite [leRHS](_ : _ = f^* x + (\- g)%R^* x).
    apply: (lim_sup_davg_le xU) => //.
    apply/(measurable_comp measurableT) => //.
    by case: locg => + _ _; exact: measurable_funS.
  rewrite (@continuous_lim_sup_davg (- g)%R _ _ xU mU); first by rewrite adde0.
  - apply/(measurable_comp measurableT) => //.
    by case: locg => + _ _; apply: measurable_funS.
  + by move=> y; exact/continuousN/cg.
- rewrite [leRHS](_ : _ = ((f \- g)%R^* \+ g^*) x)//.
    rewrite {1}(_ : f = f \- g + g)%R; last by apply/funext => y; rewrite subrK.
    apply: (lim_sup_davg_le xU mU).
      apply: measurable_funB; [exact: mUf|].
      by case: locg => + _ _; exact: measurable_funS.
    by case: locg => + _ _; exact: measurable_funS.
  rewrite [X in _ + X](@continuous_lim_sup_davg _ _ _ xU mU); [by rewrite adde0| |by[]].
  by case: locg => + _ _; exact: measurable_funS.
Qed.

Local Notation mu := (@lebesgue_measure R).

Let is_cvg_ereal_sup_davg f x :
  cvg (ereal_sup [set davg f x y | y in ball 0%R e `\ 0%R] @[e --> 0^'+]).
Proof.
apply: nondecreasing_at_right_is_cvge; near=> e => y z.
rewrite !in_itv/= => /andP[y0 ye] /andP[z0 ze] yz.
apply: le_ereal_sup => _ /= -[b [yb b0]] <-.
by exists b => //; split => //; exact: le_ball yb.
Unshelve. all: by end_near. Qed.

Lemma lim_sup_davgT_HL_maximal f (x : R) : locally_integrable setT f ->
  f^* x <= HL_maximal f x + `|f x|%:E.
Proof.
move=> [mf _ locf]; rewrite /lim_sup_davg lime_sup_lim; apply: lime_le.
  exact: is_cvg_ereal_sup_davg.
near=> e.
apply: ub_ereal_sup => _ [b [eb] /= b0] <-.
suff : forall r, davg f x r <= HL_maximal f x + `|f x|%:E by exact.
move=> r.
apply: (@le_trans _ _ ((fine (mu (ball x r)))^-1%:E *
    \int[mu]_(y in ball x r) (`|(f y)%:E| + `|(f x)%:E|))).
  - rewrite /davg lee_wpmul2l//.
      by rewrite lee_fin invr_ge0 fine_ge0.
    apply: ge0_le_integral => //.
    + exact: measurable_ball.
    + do 2 apply: measurableT_comp => //=; apply: measurable_funB => //.
      exact: measurableT_comp.
    + by move=> *; rewrite adde_ge0.
    + apply: emeasurable_funD => //; do 2 apply: measurableT_comp => //.
      exact: measurable_funS mf.
  by move=> /= y xry; rewrite -EFinD lee_fin// ler_normB.
rewrite [leLHS](_ : _ = (fine (mu (ball x r)))^-1%:E *
  (\int[mu]_(y in ball x r) `|(f y)%:E| +
   \int[mu]_(y in ball x r) `|(f x)%:E|)); last first.
  congr *%E; rewrite ge0_integralD//=; first exact: measurable_ball.
  by do 2 apply: measurableT_comp => //; exact: measurable_funS mf.
have [r0|r0] := lerP r 0.
  rewrite (ball0 _ _).2// !integral_set0 adde0 mule0 adde_ge0//.
  by apply: HL_maximalT_ge0; split => //; exact: openT.
rewrite muleDr//; last by rewrite ge0_adde_def// inE integral_ge0.
rewrite leeD//.
  by apply: ereal_sup_ubound => /=; exists r => //; rewrite in_itv/= r0.
under eq_integral do rewrite -(mule1 `| _ |).
rewrite ge0_integralZl//; last exact: measurable_ball.
rewrite integral_cst//; last exact: measurable_ball.
rewrite mul1e muleCA !(lebesgue_measure_ball _ (ltW r0)).
rewrite [X in _ * (_ * X)](_ : _ = mu (ball x r))//.
rewrite (lebesgue_measure_ball _ (ltW r0))//.
by rewrite /= -EFinM mulVf ?mulr1// mulrn_eq0/= gt_eqF.
Unshelve. all: by end_near. Qed.

End lim_sup_davg.

Definition lebesgue_pt {R : realType} (f : R -> R) (x : R) :=
  davg f x r @[r --> (0%R:R)^'+] --> 0%E.

Lemma continuous_lebesgue_pt {R : realType} (f : R -> R) x (U : set R) :
  open_nbhs x U -> measurable U -> measurable_fun U f ->
  {for x, continuous f} -> lebesgue_pt f x.
Proof.
move=> xU mU mUf xf; rewrite /lebesgue_pt -[X in _ --> X](@davg0 _ f x 0)//.
apply: cvg_at_right_filter; rewrite davg0//.
exact: (continuous_cvg_davg xU mU mUf).
Qed.

Lemma lebesgue_pt_restrict {R : realType} (f : R -> R) (a : itv_bound R) x u :
  (x < u)%R -> (a < BRight x)%E ->
  lebesgue_pt f x -> lebesgue_pt (f \_ [set` Interval a (BRight u)]) x.
Proof.
by move=> xu ax; apply: cvg_trans; apply: near_eq_cvg; exact: near_davg.
Qed.

Section lebesgue_measure_integral.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma integral_Sset1 (f : R -> \bar R) A (r : R) : A `<=` [set r] ->
  (\int[mu]_(x in A) f x = 0)%E.
Proof.
move=> Ar; have [->|->] := subset_set1 Ar; first by rewrite integral_set0.
rewrite (eq_integral (cst (f r)))/=; last by move=> x; rewrite inE/= => ->.
by rewrite integral_cst//= lebesgue_measure_set1 mule0.
Qed.

Lemma integral_set1 (f : R -> \bar R) (r : R) : \int[mu]_(x in [set r]) f x = 0.
Proof. exact: (integral_Sset1 _ (@subset_refl _ _)). Qed.

Lemma ge0_integral_closed_ball c (r : R) (r0 : (0 < r)%R) (f : R -> \bar R) :
  measurable_fun (closed_ball c r : set R) f ->
  (forall x, x \in closed_ball c r -> 0 <= f x) ->
  \int[mu]_(x in closed_ball c r) f x = \int[mu]_(x in ball c r) f x.
Proof.
move=> mf f0.
rewrite closed_ball_ball//= ge0_integral_setU//=; last 4 first.
  by apply: measurableU => //; exact: measurable_ball.
  by move: mf; rewrite closed_ball_ball.
  by move=> x xcr; rewrite f0// closed_ball_ball// inE.
  apply/disj_setPLR => x [->|]/=; rewrite /ball/=.
    by apply/eqP; rewrite (addrC _ r) -subr_eq -addrA addrC subrK eqNr gt_eqF.
  by move=> /[swap] ->; rewrite opprD addrA subrr sub0r normrN gtr0_norm// ltxx.
rewrite ge0_integral_setU//=.
- by rewrite !integral_set1//= add0e adde0.
- exact: measurable_ball.
- apply: measurable_funS mf; first exact: measurable_closed_ball.
  by move=> x; rewrite closed_ball_ball//; left.
- by move=> x H; rewrite f0// closed_ball_ball// inE/=; left.
- apply/disj_setPRL => x /[swap] ->.
  by rewrite /ball/= opprB addrCA subrr addr0 gtr0_norm// ltxx.
Qed.

Lemma integral_setD1_EFin (f : R -> R) r (D : set R) :
  measurable (D `\ r) -> measurable_fun (D `\ r) f ->
  \int[mu]_(x in D `\ r) (f x)%:E = \int[mu]_(x in D) (f x)%:E.
Proof.
move=> mD mfl; have [Dr|NDr] := pselect (D r); last by rewrite not_setD1.
rewrite -[in RHS](@setD1K _ r D)// integral_setU_EFin//=.
- by rewrite integral_set1// add0e.
- by apply/measurable_funU => //; split => //; exact: measurable_fun_set1.
- by rewrite disj_set2E setDIK.
Qed.

Lemma integral_itv_bndo_bndc (a : itv_bound R) (r : R) (f : R -> R) :
  measurable_fun [set` Interval a (BLeft r)] f ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x)%:E =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x)%:E.
Proof.
move=> mf; have [ar|ar] := leP a (BLeft r).
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1r.
- by rewrite !set_itv_ge// -leNgt// ltW.
Qed.

Lemma integral_itv_obnd_cbnd (r : R) (b : itv_bound R) (f : R -> R) :
  measurable_fun [set` Interval (BRight r) b] f ->
   \int[mu]_(x in [set` Interval (BRight r) b]) (f x)%:E =
   \int[mu]_(x in [set` Interval (BLeft r) b]) (f x)%:E.
Proof.
move=> mf; have [rb|rb] := leP (BRight r) b.
- by rewrite -[RHS](@integral_setD1_EFin _ r) ?setDitv1l.
- by rewrite !set_itv_ge// -leNgt -?ltBRight_leBLeft// ltW.
Qed.

Lemma integral_itv_bndoo (x y : R) (f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in `]x, y[) (f z)%:E.
Proof.
have [xy|yx _|-> _] := ltgtP x y; last 2 first.
- rewrite !set_itv_ge ?integral_set0//=.
  + by rewrite bnd_simp le_gtF// ltW.
  + by move: b0 b1 => [|] [|]; rewrite bnd_simp ?lt_geF// le_gtF// ltW.
- by move: b0 b1 => [|] [|]; rewrite !set_itvE ?integral_set0 ?integral_set1.
move=> mf.
transitivity (\int[mu]_(z in [set` Interval (BSide b0 x) (BLeft y)]) (f z)%:E).
  case: b1 => //; rewrite -integral_itv_bndo_bndc//.
  by case: b0 => //; exact: measurable_fun_itv_obnd_cbnd.
by case: b0 => //; rewrite -integral_itv_obnd_cbnd.
Qed.

Lemma eq_integral_itv_bounded (x y : R) (g f : R -> R) (b0 b1 : bool) :
  measurable_fun `]x, y[ f -> measurable_fun `]x, y[ g ->
  {in `]x, y[, f =1 g} ->
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (f z)%:E =
  \int[mu]_(z in [set` Interval (BSide b0 x) (BSide b1 y)]) (g z)%:E.
Proof.
move=> mf mg fg.
rewrite integral_itv_bndoo// (@integral_itv_bndoo _ _ g)//.
by apply: eq_integral => z; rewrite inE/= => zxy; congr EFin; exact: fg.
Qed.

End lebesgue_measure_integral.
Arguments integral_Sset1 {R f A} r.

Section Rintegral_lebesgue_measure.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Implicit Type f : R -> R.

Lemma Rintegral_itv_bndo_bndc (a : itv_bound R) (r : R) f :
  mu.-integrable [set` Interval a (BLeft r)] (EFin \o f) ->
   \int[mu]_(x in [set` Interval a (BLeft r)]) (f x) =
   \int[mu]_(x in [set` Interval a (BRight r)]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itv_bndo_bndc//.
by apply/measurable_EFinP; exact: (measurable_int mu).
Qed.

Lemma Rintegral_itv_obnd_cbnd (r : R) (b : itv_bound R) f :
  mu.-integrable [set` Interval (BRight r) b] (EFin \o f) ->
  \int[mu]_(x in [set` Interval (BRight r) b]) (f x) =
  \int[mu]_(x in [set` Interval (BLeft r) b]) (f x).
Proof.
move=> mf; rewrite /Rintegral integral_itv_obnd_cbnd//.
by apply/measurable_EFinP; exact: (measurable_int mu).
Qed.

Lemma Rintegral_set1 f (r : R) : \int[mu]_(x in [set r]) f x = 0.
Proof. by rewrite /Rintegral integral_set1. Qed.

Lemma Rintegral_itvB f (a b : itv_bound R) x :
  mu.-integrable [set` (Interval a b)] (EFin \o f) ->
  (a <= BRight x)%O -> (BRight x <= b)%O ->
  \int[mu]_(t in [set` Interval a b]) f t -
  \int[mu]_(t in [set` Interval a (BRight x)]) f t =
  \int[mu]_(x in [set` Interval (BRight x) b]) f x.
Proof.
move=> itf; rewrite le_eqVlt => /predU1P[ax|ax xb].
  rewrite ax => _; rewrite [in X in _ - X]set_itv_ge ?bnd_simp//.
  by rewrite Rintegral_set0 subr0.
rewrite (@itv_bndbnd_setU _ _ _ (BLeft x)); last 2 first.
  by case: a ax {itf} => -[].
  by rewrite (le_trans _ xb)// bnd_simp.
rewrite Rintegral_setU//=.
- rewrite addrAC Rintegral_itv_bndo_bndc//; last first.
    apply: integrableS itf => //; apply: subset_itvl.
    by rewrite (le_trans _ xb)// bnd_simp.
  rewrite subrr add0r Rintegral_itv_obnd_cbnd//.
  by apply: integrableS itf => //; exact/subset_itvr/ltW.
- by rewrite -itv_bndbnd_setU -?ltBRight_leBLeft// ltW.
- apply/disj_setPS => y [/=]; rewrite 2!in_itv/= => /andP[_ yx] /andP[].
  by rewrite leNgt yx.
Qed.

End Rintegral_lebesgue_measure.

Section lebesgue_differentiation.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types f : R -> R.

Local Notation "f ^*" := (lim_sup_davg f).

Let lebesgue_differentiation_suff (E : set R) f :
  (forall a, (0 < a)%R -> mu.-negligible (E `&` [set x | a%:E < f^* x])) ->
  {ae mu, forall x : R, E x -> lebesgue_pt f x}.
Proof.
move=> Ef; have {Ef} : mu.-negligible (E `&` [set x | 0 < f^* x]).
  suff -> : E `&` [set x | 0 < f^* x] =
            E `&` \bigcup_n [set x | n.+1%:R^-1%:E < f^* x].
    rewrite setI_bigcupr;  apply: negligible_bigcup => k/=.
    by apply: Ef; rewrite invr_gt0.
  apply/seteqP; split; last first.
    by move=> r [Er] [k ?] /=; split => //; exact: le_lt_trans q.
  move=> x /= [Ex] fx0; split => //.
  have [fxoo|fxoo] := eqVneq (f^* x) +oo.
    by exists 1%N => //=; rewrite fxoo ltry.
  near \oo => m; exists m => //=.
  rewrite -(@fineK _ (f^* x)) ?gt0_fin_numE ?ltey// lte_fin.
  rewrite invf_plt ?posrE//; last by rewrite fine_gt0// ltey fx0.
  set r := _^-1; rewrite (@le_lt_trans _ _ `|ceil r|.+1%:R)//.
    by rewrite (le_trans _ (abs_ceil_ge _))// ler_norm.
  by rewrite ltr_nat ltnS; near: m; exact: nbhs_infty_gt.
apply: negligibleS => z /= /not_implyP[Ez H]; split => //.
rewrite ltNge; apply: contra_notN H.
rewrite le_eqVlt ltNge limf_esup_ge0/= ?orbF//; last first.
  by move=> x; exact: iavg_ge0.
move=> /eqP fz0.
suff: lime_inf (davg f z) 0 = 0 by exact: lime_sup_inf_at_right.
apply/eqP; rewrite eq_le -[X in _ <= X <= _]fz0 lime_inf_sup/= fz0.
by apply: lime_inf_ge0 => x; exact: iavg_ge0.
Unshelve. all: by end_near. Qed.

Let lebesgue_differentiation_bounded f :
  let B k : set R^o := ball 0%R k.+1.*2%:R in
  let f_ k := f \_ (B k) in
  (forall k, mu.-integrable setT (EFin \o f_ k)) ->
  forall k, {ae mu, forall x, B k x -> lebesgue_pt (f_ k) x}.
Proof.
move=> B f_ intf_ k; apply: lebesgue_differentiation_suff => e e0.
have mE : measurable (B k) by exact: measurable_ball.
have ex_g_ : exists g_ : (R -> R)^nat,
  [/\ (forall n, continuous (g_ n)),
      (forall n, mu.-integrable (B k) (EFin \o g_ n)) &
      \int[mu]_(z in B k) `|f_ k z - g_ n z|%:E @[n --> \oo] --> 0 ].
  apply: approximation_continuous_integrable => //=.
    by rewrite lebesgue_measure_ball//= ltry.
  exact: integrableS (intf_ _).
have {ex_g_} ex_gn n : exists gn : R -> R,
    [/\ continuous gn,
        mu.-integrable (B k) (EFin \o gn) &
        \int[mu]_(z in B k) `|f_ k z - gn z|%:E <= n.+1%:R^-1%:E].
  case: ex_g_ => g_ [cg intg] /fine_cvgP[] [m _ fgfin] /cvgrPdist_le.
  move=> /(_ n.+1%:R^-1 ltac:(by []))[p _] /(_ _ (leq_addr m p)).
  rewrite sub0r normrN -lee_fin => /= fg0.
  exists (g_ (p + m)%N); split => //.
  rewrite (le_trans _ fg0)// ger0_norm ?fine_ge0 ?integral_ge0// fineK//.
  by rewrite fgfin//= leq_addl.
pose g_ n : R -> R := sval (cid (ex_gn n)).
have cg_ n : continuous (g_ n) by rewrite /g_ /sval /=; case: cid => // x [].
have intg n : mu.-integrable (B k) (EFin \o g_ n).
  by rewrite /g_ /sval /=; case: cid => // x [].
have ifg_ub n : \int[mu]_(z in B k) `|f_ k z - g_ n z|%:E <= n.+1%:R^-1%:E.
  by rewrite /g_ /sval /=; case: cid => // x [].
pose g_B n := g_ n \_ (B k).
have cg_B n : {in B k, continuous (g_B n)}.
  move=> x xBk; rewrite /g_B patch_indic/=.
  by apply: cvgM => //; [exact: cg_|exact: cvg_indic].
pose f_g_Be n : set _ := [set x | `| (f_ k \- g_B n) x |%:E >= (e / 2)%:E].
pose HLf_g_Be n : set _ :=
  [set x | HL_maximal (f_ k \- g_B n)%R x > (e / 2)%:E].
pose Ee := \bigcap_n (B k `&` (HLf_g_Be n `|` f_g_Be n)).
case/integrableP: (intf_ k) => mf intf.
have mfg n : measurable_fun setT (f_ k \- g_ n)%R.
  apply: measurable_funB; first by move/measurable_EFinP : mf.
  by apply: continuous_measurable_fun; exact: cg_.
have locg_B n : locally_integrable [set: R] (g_B n).
  split; [|exact: openT|].
  - apply/(measurable_restrictT _ _).1 => //.
    exact: measurable_funS (continuous_measurable_fun (cg_ n)).
  - move=> K _ cK.
    rewrite (@le_lt_trans _ _ (\int[mu]_(x in K) `|g_ n x|%:E))//; last first.
      have : {within K, continuous (g_ n)} by apply: continuous_subspaceT.
      by move/(continuous_compact_integrable cK) => /integrableP[_ /=].
    apply: ge0_le_integral => //=.
    + exact: compact_measurable.
    + do 2 apply: measurableT_comp => //; apply/measurable_restrict => //.
        exact: compact_measurable.
      exact: measurable_funS (continuous_measurable_fun (cg_ n)).
    + do 2 apply: measurableT_comp => //; apply: measurable_funTS.
      exact: continuous_measurable_fun.
    + move=> /= x Kx; rewrite /g_B patchE; case: ifPn => //=.
      by rewrite normr0 lee_fin.
have locf_g_B n : locally_integrable setT (f_ k \- g_B n)%R.
  apply: locally_integrableB => //; split.
  - by move/measurable_EFinP : mf.
  - exact: openT.
  - move=> K _ cK; rewrite (le_lt_trans _ intf)//=.
    apply: ge0_subset_integral => //.
    + exact: compact_measurable.
    + by do 2 apply: measurableT_comp => //; move/measurable_EFinP : mf.
have mEHL i : measurable (HLf_g_Be i).
  rewrite /HLf_g_Be -[X in measurable X]setTI.
  apply: emeasurable_fun_o_infty => //.
  by apply: measurable_HL_maximal; exact: locf_g_B.
have mfge i : measurable (f_g_Be i).
  rewrite /f_g_Be -[X in measurable X]setTI.
  apply: emeasurable_fun_c_infty => //.
  by do 2 apply: measurableT_comp => //; case: (locf_g_B i).
have mEe : measurable Ee.
  apply: bigcapT_measurable => i.
  by apply: measurableI; [exact: measurable_ball|exact: measurableU].
have davgfEe : B k `&` [set x | (f_ k)^* x > e%:E] `<=` Ee.
  suff: forall n, B k `&` [set x | e%:E < (f_ k)^* x] `<=`
                  B k `&` (HLf_g_Be n `|` f_g_Be n).
    by move=> suf r /= /suf hr n _; exact: hr.
  move=> n; rewrite [X in X `<=`_](_ : _ =
      B k `&` [set x | e%:E < (f_ k \- g_B n)%R^* x]); last first.
    apply/seteqP; split => [x [Ex] /=|x [Ex] /=].
      rewrite (@lim_sup_davgB _ _ _ _ (B k))//.
      by split; [exact: ball_open|exact: Ex].
      by move/measurable_EFinP : mf; apply: measurable_funS.
      by apply: cg_B; rewrite inE.
    rewrite (@lim_sup_davgB _ _ _ _ (B k))//.
    by split; [exact: ball_open|exact: Ex].
    by move/measurable_EFinP : mf; apply: measurable_funS.
    by apply: cg_B; rewrite inE.
  move=> r /= [Er] efgnr; split => //.
  have {}efgnr := lt_le_trans efgnr (lim_sup_davgT_HL_maximal r (locf_g_B n)).
  have [|h] := ltP (e / 2)%:E (HL_maximal (f_ k \- g_B n)%R r); first by left.
  right; move: efgnr.
  rewrite {1}(splitr e) EFinD -lteBrDl// => /ltW/le_trans; apply.
  by rewrite leeBlDl// leeD.
suff: mu Ee = 0 by exists Ee.
have HL_null n : mu (HLf_g_Be n) <= (3 / (e / 2))%:E * n.+1%:R^-1%:E.
  rewrite (le_trans (maximal_inequality _ _ )) ?divr_gt0//.
  rewrite lee_pmul2l ?lte_fin ?divr_gt0//.
  set h := (fun x => `|(f_ k \- g_ n) x|%:E) \_ (B k).
  rewrite (@eq_integral _ _ _ mu setT h)//=.
    by rewrite -integral_mkcond/=; exact: ifg_ub.
  move=> x _; rewrite /h restrict_EFin restrict_normr/= /g_B /f_ !patchE.
  by case: ifPn => /=; [rewrite patchE => ->|rewrite subrr].
have fgn_null n : mu [set x | `|(f_ k \- g_B n) x|%:E >= (e / 2)%:E] <=
                     (e / 2)^-1%:E * n.+1%:R^-1%:E.
  rewrite lee_pdivlMl ?invr_gt0 ?divr_gt0// -[X in mu X]setTI.
  apply: le_trans.
    apply: (@le_integral_comp_abse _ _ _ mu _ measurableT
        (EFin \o (f_ k \- g_B n)%R) (e / 2) id) => //=.
      by apply: measurableT_comp => //; case: (locf_g_B n).
    by rewrite divr_gt0.
  set h := (fun x => `|(f_ k \- g_ n) x|%:E) \_ (B k).
  rewrite (@eq_integral _ _ _ mu setT h)//=.
    by rewrite -integral_mkcond/=; exact: ifg_ub.
  move=> x _; rewrite /h restrict_EFin restrict_normr/= /g_B /f_ !patchE.
  by case: ifPn => /=; [rewrite patchE => ->|rewrite subrr].
apply/eqP; rewrite eq_le measure_ge0 andbT.
apply/lee_addgt0Pr => r r0; rewrite add0e.
have incl n : Ee `<=` B k `&` (HLf_g_Be n `|` f_g_Be n) by move=> ?; apply.
near \oo => n.
rewrite (@le_trans _ _ (mu (B k `&` (HLf_g_Be n `|` f_g_Be n))))//.
  rewrite le_measure// inE//; apply: measurableI; first exact: measurable_ball.
  by apply: measurableU => //; [exact: mEHL|exact: mfge].
rewrite (@le_trans _ _ ((4 / (e / 2))%:E * n.+1%:R^-1%:E))//.
  rewrite (@le_trans _ _ (mu (HLf_g_Be n `|` f_g_Be n)))//.
    rewrite le_measure// inE//.
      apply: measurableI => //.
      by apply: measurableU => //; [exact: mEHL|exact: mfge].
    by apply: measurableU => //; [exact: mEHL|exact: mfge].
  rewrite (le_trans (measureU2 _ _ _))//=; [exact: mEHL|exact: mfge|].
  apply: le_trans; first by apply: leeD; [exact: HL_null|exact: fgn_null].
  rewrite -muleDl// lee_pmul2r// -EFinD lee_fin -{2}(mul1r (_^-1)).
  by rewrite -mulrDl natr1.
rewrite -lee_pdivlMl ?divr_gt0// -EFinM lee_fin -(@invrK _ r).
rewrite -invfM lef_pV2 ?posrE ?divr_gt0// -(@natr1 _ n) -lerBlDr.
by near: n; exact: nbhs_infty_ger.
Unshelve. all: by end_near. Qed.

Lemma lebesgue_differentiation f : locally_integrable setT f ->
  {ae mu, forall x, lebesgue_pt f x}.
Proof.
move=> locf.
pose B k : set R^o := ball 0%R (k.+1.*2)%:R.
pose fk k := f \_ (B k).
have mfk k : mu.-integrable setT (EFin \o fk k).
  case: locf => mf _ intf.
  apply/integrableP; split => /=.
    by apply/measurable_EFinP/(measurable_restrictT _ _).1 => //=;
      [exact: measurable_ball|exact: measurable_funS mf].
  rewrite (_ : (fun x => _) = (EFin \o normr \o f) \_ (B k)); last first.
    by apply/funext => x; rewrite restrict_EFin/= restrict_normr.
  rewrite -integral_mkcond/= -ge0_integral_closed_ball//.
    by rewrite intf//; exact: closed_ballR_compact.
  by apply: measurable_funTS; do 2 apply: measurableT_comp.
have suf k : {ae mu, forall x, B k x -> lebesgue_pt (fk k) x}.
  exact: lebesgue_differentiation_bounded.
pose E k : set _ := sval (cid (suf k)).
rewrite /= in E.
have HE k : mu (E k) = 0 /\ ~` [set x | B k x -> lebesgue_pt (fk k) x] `<=` E k.
  by rewrite /E /sval; case: cid => // A [].
suff: ~` [set x | lebesgue_pt f x] `<=`
      \bigcup_k (~` [set x | B k x -> lebesgue_pt (fk k) x]).
  move/(@negligibleS _ _ _ mu); apply => /=.
  by apply: negligible_bigcup => k /=; exact: suf.
move=> x /= fx; rewrite -setC_bigcap => h; apply: fx.
have fE y k r : (ball 0%R k.+1%:R) y -> (r < 1)%R ->
    forall t, ball y r t -> f t = fk k t.
  rewrite /ball/= sub0r normrN => yk1 r1 t.
  rewrite ltr_distlC => /andP[xrt txr].
  rewrite /fk patchE mem_set// /B /ball/= sub0r normrN.
  have [t0|t0] := ger0P.
    rewrite (lt_le_trans txr)// -lerBrDr.
    rewrite (le_trans (ler_norm _))// (le_trans (ltW yk1))//.
    by rewrite lerBrDr -addnn natrD lerD2 (le_trans (ltW r1))// ler1n.
  rewrite -opprB ltrNl in xrt.
  rewrite (lt_le_trans xrt)// lerBlDl (le_trans (ltW r1))//.
  rewrite -lerBlDl addrC -lerBrDr (le_trans (ler_norm _))// normrN.
  by rewrite (le_trans (ltW yk1))// lerBrDr natr1 ler_nat -muln2 ltn_Pmulr.
have := h `|ceil x|.+1%N Logic.I.
have Bxx : B `|ceil x|.+1 x.
  rewrite /B /ball/= sub0r normrN (le_lt_trans (abs_ceil_ge _))// ltr_nat.
  by rewrite -addnn addSnnS ltn_addl.
move=> /(_ Bxx)/fine_cvgP[davg_fk_fin_num davg_fk0].
have f_fk_ceil : \forall t \near 0^'+,
  \int[mu]_(y in ball x t) `|(f y)%:E - (f x)%:E| =
  \int[mu]_(y in ball x t) `|fk `|ceil x|.+1 y - fk `|ceil x|.+1 x|%:E.
  near=> t.
  apply: eq_integral => /= y /[1!inE] xty.
  rewrite -(fE x _ t)//; last first.
    by rewrite /ball/= sub0r normrN (le_lt_trans (abs_ceil_ge _))// ltr_nat.
  rewrite -(fE x _ t)//; last first.
    by apply: ballxx; near: t; exact: nbhs_right_gt.
  by rewrite /ball/= sub0r normrN (le_lt_trans (abs_ceil_ge _))// ltr_nat.
apply/fine_cvgP; split=> [{davg_fk0}|{davg_fk_fin_num}].
- move: davg_fk_fin_num => -[M /= M0] davg_fk_fin_num.
  apply: filter_app f_fk_ceil; near=> t => Ht.
  by rewrite /davg /iavg Ht davg_fk_fin_num//= sub0r normrN gtr0_norm.
- move/cvgrPdist_le in davg_fk0; apply/cvgrPdist_le => e e0.
  have [M /= M0 {}davg_fk0] := davg_fk0 _ e0.
  apply: filter_app f_fk_ceil; near=> t; move=> Ht.
  by rewrite /davg /iavg Ht// davg_fk0//= sub0r normrN gtr0_norm.
Unshelve. all: by end_near. Qed.

End lebesgue_differentiation.

Section density.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.

Lemma lebesgue_density (A : set R) : measurable A ->
  {ae mu, forall x, mu (A `&` ball x r) * (fine (mu (ball x r)))^-1%:E
                      @[r --> 0^'+] --> (\1_A x)%:E}.
Proof.
move=> mA; have := lebesgue_differentiation (locally_integrable_indic openT mA).
apply: filter_app; first exact: (ae_filter_ringOfSetsType mu).
apply: aeW => /= x Ax.
apply: (sube_cvg0 _ _).1 => //.
move: Ax; rewrite /lebesgue_pt /davg /= -/mu => Ax.
have : (fine (mu (ball x r)))^-1%:E *
       `|\int[mu]_(y in ball x r) (\1_A y - \1_A x)%:E | @[r --> 0^'+] --> 0.
  apply: (@squeeze_cvge _ _ _ R (cst 0) _ _ _ _ _ Ax) => //; [|exact: cvg_cst].
  near=> a.
  apply/andP; split; first by rewrite mule_ge0// lee_fin invr_ge0// fine_ge0.
  rewrite lee_pmul2l//; last first.
    rewrite lte_fin invr_gt0// fine_gt0//.
    by rewrite lebesgue_measure_ball// ltry andbT lte_fin mulrn_wgt0.
  apply: le_abse_integral => //; first exact: measurable_ball.
  by apply/measurable_EFinP; exact: measurable_funB.
set f := (f in f r @[r --> 0^'+] --> _ -> _).
rewrite (_ : f = fun r => (fine (mu (ball x r)))^-1%:E *
   `|mu (A `&` ball x r) - (\1_A x)%:E * mu (ball x r)|); last first.
  apply/funext => r; rewrite /f integralB_EFin//=; last 3 first.
    - exact: measurable_ball.
    - apply/integrableP; split.
        exact/measurable_EFinP/measurable_indic.
      under eq_integral do rewrite /= ger0_norm//=.
      rewrite integral_indic//=; last exact: measurable_ball.
      rewrite -/mu (@le_lt_trans _ _ (mu (ball x r)))// ?le_measure// ?inE.
      + by apply: measurableI => //; exact: measurable_ball.
      + exact: measurable_ball.
      + have [r0|r0] := ltP r 0%R.
          by rewrite ((ball0 _ _).2 (ltW r0))// /mu measure0.
        by rewrite lebesgue_measure_ball//= ?ltry.
    - apply/integrableP; split; first exact/measurable_EFinP/measurable_cst.
      rewrite /= integral_cst//=; last exact: measurable_ball.
      have [r0|r0] := ltP r 0%R.
        by rewrite ((ball0 _ _).2 (ltW r0))// /mu measure0 mule0.
      by rewrite lebesgue_measure_ball//= ?ltry.
  rewrite integral_indic//=; last exact: measurable_ball.
  by rewrite -/mu integral_cst//; exact: measurable_ball.
rewrite indicE; have [xA xrA0|xA] := boolP (x \in A); last first.
  apply: iffRL; apply/propeqP; apply: eq_cvg => r.
  by rewrite -mulNrn mulr0n adde0 mul0e sube0 gee0_abs// muleC.
have {xrA0} /cvgeN : (fine (mu (ball x r)))^-1%:E *
    (mu (ball x r) - mu (A `&` ball x r)) @[r --> 0^'+] --> 0.
  move: xrA0; apply: cvg_trans; apply: near_eq_cvg; near=> r.
  rewrite mul1e lee0_abs; last first.
    rewrite sube_le0 le_measure// ?inE/=; last exact: measurable_ball.
    by apply: measurableI => //; exact: measurable_ball.
  rewrite oppeB//; first by rewrite addeC.
  rewrite fin_num_adde_defl// fin_numN ge0_fin_numE//.
  by rewrite lebesgue_measure_ball// ltry.
rewrite oppe0; apply: cvg_trans; apply: near_eq_cvg; near=> r.
rewrite -mulNrn mulr1n muleBr//; last first.
  by rewrite fin_num_adde_defr// ge0_fin_numE// lebesgue_measure_ball//= ?ltry.
rewrite (_ : (fine (mu (ball x r)))^-1%:E * mu (ball x r) = 1); last first.
  rewrite -[X in _ * X](@fineK _ (mu (ball x r)))//; last first.
    by rewrite lebesgue_measure_ball//= ?ltry.
  by rewrite -EFinM mulVf// lebesgue_measure_ball//= gt_eqF// mulrn_wgt0.
by rewrite oppeB// addeC EFinN muleC.
Unshelve. all: by end_near. Qed.

End density.

Section nicely_shrinking.
Context {R : realType}.
Implicit Types (x : R) (E : (set R)^nat).
Local Notation mu := lebesgue_measure.

Definition nicely_shrinking x E :=
  (forall n, measurable (E n)) /\
  exists Cr : R * {posnum R}^nat, [/\ Cr.1 > 0,
    (Cr.2 n)%:num @[n --> \oo] --> 0,
    (forall n, E n `<=` ball x (Cr.2 n)%:num) &
    (forall n, mu (ball x (Cr.2 n)%:num) <= Cr.1%:E * mu (E n))%E].

Lemma nicely_shrinking_gt0 x E : nicely_shrinking x E ->
  forall n, (0 < mu (E n))%E.
Proof.
move=> [mE [[C r_]]] [/= C_gt0 _ _ + ] n => /(_ n).
rewrite lebesgue_measure_ball// -lee_pdivrMl//.
apply: lt_le_trans.
by rewrite mule_gt0// lte_fin invr_gt0.
Qed.

Lemma nicely_shrinking_lty x E : nicely_shrinking x E ->
  forall n, (mu (E n) < +oo)%E.
Proof.
move=> [mE [[C r_]]] [/= C_gt0 _ + _] n => /(_ n) Er_.
rewrite (@le_lt_trans _ _ (lebesgue_measure (ball x (r_ n)%:num)))//.
  by rewrite le_measure// inE; [exact: mE|exact: measurable_ball].
by rewrite lebesgue_measure_ball// ltry.
Qed.

End nicely_shrinking.

Section nice_lebesgue_differentiation.
Local Open Scope ereal_scope.
Context {R : realType}.
Variable E : R -> (set R)^nat.
Hypothesis hE : forall x, nicely_shrinking x (E x).
Local Notation mu := lebesgue_measure.

Lemma nice_lebesgue_differentiation (f : R -> R) :
  locally_integrable setT f -> forall x, lebesgue_pt f x ->
  (fine (mu (E x n)))^-1%:E * \int[mu]_(y in E x n) (f y)%:E
    @[n --> \oo] --> (f x)%:E.
Proof.
move=> locf x fx; apply: (sube_cvg0 _ _).1 => //=; apply/cvg_abse0P.
pose r_ x : {posnum R} ^nat := (sval (cid (hE x).2)).2.
pose C := (sval (cid (hE x).2)).1.
have C_gt0 : (0 < C)%R by rewrite /C /sval/=; case: cid => -[? ?] [].
have r_0 y : (r_ y n)%:num @[n --> \oo] --> (0%R : R).
  by rewrite /r_ /sval/=; case: cid => -[? ?] [].
have E_r_ n : E x n `<=` ball x (r_ x n)%:num.
  by rewrite /r_ /sval/=; case: cid => -[? ?] [].
have muEr_ n : mu (ball x (r_ x n)%:num) <= C%:E * mu (E x n).
  by rewrite /C /r_ /sval/=; case: cid => -[? ?] [].
apply: (@squeeze_cvge _ _ _ _ (cst 0) _
  (fun n => C%:E * davg f x (r_ x n)%:num)); last 2 first.
  exact: cvg_cst.
  move/cvge_at_rightP: fx => /(_ (fun r => (r_ x r)%:num)) fx.
  by rewrite -(mule0 C%:E); apply: cvgeM => //;[exact: mule_def_fin |
    exact: cvg_cst | apply: fx; split => //; exact: r_0].
near=> n.
apply/andP; split => //=.
apply: (@le_trans _ _ ((fine (mu (E x n)))^-1%:E *
                       `| \int[mu]_(y in E x n) ((f y)%:E + (- f x)%:E) |)).
  have fxE : (- f x)%:E =
             (fine (mu (E x n)))^-1%:E * \int[mu]_(y in E x n) (- f x)%:E.
    rewrite integral_cst//=; last exact: (hE _).1.
    rewrite muleCA -[X in _ * (_ * X)](@fineK _ (mu (E x n))); last first.
      by rewrite ge0_fin_numE// (nicely_shrinking_lty (hE x)).
    rewrite -EFinM mulVf ?mulr1// neq_lt fine_gt0 ?orbT//.
    by rewrite (nicely_shrinking_gt0 (hE x))//= (nicely_shrinking_lty (hE x)).
  rewrite [in leLHS]fxE -muleDr//; last first.
    rewrite integral_cst//=; last exact: (hE _).1.
    rewrite fin_num_adde_defl// fin_numM// gt0_fin_numE.
      by rewrite (nicely_shrinking_lty (hE x)).
    by rewrite (nicely_shrinking_gt0 (hE x)).
  rewrite abseM gee0_abs; last by rewrite lee_fin// invr_ge0// fine_ge0.
  rewrite lee_pmul//; first by rewrite lee_fin// invr_ge0// fine_ge0.
  rewrite integralD//=.
  - exact: (hE x).1.
  - apply/integrableP; split.
      by apply/measurable_EFinP; case: locf => + _ _; exact: measurable_funS.
    rewrite (@le_lt_trans _ _
      (\int[mu]_(y in closed_ball x (r_ x n)%:num) `|(f y)%:E|))//.
      apply: ge0_subset_integral => //.
      + exact: (hE _).1.
      + exact: measurable_closed_ball.
      + apply: measurableT_comp => //; apply/measurable_EFinP => //.
        by case: locf => + _ _; exact: measurable_funS.
      + by apply: (subset_trans (E_r_ n)) => //; exact: subset_closed_ball.
    by case: locf => _ _; apply => //; exact: closed_ballR_compact.
  apply/integrableP; split; first exact: measurable_cst.
  rewrite integral_cst //=; last exact: (hE _).1.
  by rewrite lte_mul_pinfty// (nicely_shrinking_lty (hE x)).
rewrite muleA lee_pmul//.
- by rewrite lee_fin invr_ge0// fine_ge0.
- rewrite -(@invrK _ C) -EFinM -invfM lee_fin lef_pV2//; last 2 first.
    rewrite posrE fine_gt0// (nicely_shrinking_gt0 (hE x))//=.
    by rewrite (nicely_shrinking_lty (hE x)).
    rewrite posrE mulr_gt0// ?invr_gt0// fine_gt0//.
    by rewrite lebesgue_measure_ball// ltry andbT lte_fin mulrn_wgt0.
  rewrite lter_pdivrMl // -lee_fin EFinM fineK; last first.
    by rewrite lebesgue_measure_ball// ltry andbT lte_fin mulrn_wgt0.
  rewrite fineK; last by rewrite ge0_fin_numE// (nicely_shrinking_lty (hE x)).
  exact: muEr_.
- apply: le_trans.
  + apply: le_abse_integral => //; first exact: (hE x).1.
    apply/measurable_EFinP; apply/measurable_funB => //.
    by case: locf => + _ _; exact: measurable_funS.
  + apply: ge0_subset_integral => //; first exact: (hE x).1.
    exact: measurable_ball.
  + apply/measurable_EFinP; apply: measurableT_comp => //.
    apply/measurable_funB => //.
    by case: locf => + _ _; exact: measurable_funS.
Unshelve. all: by end_near. Qed.

End nice_lebesgue_differentiation.
