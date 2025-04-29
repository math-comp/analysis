(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop interval_inference ereal.
From mathcomp Require Import topology tvs normedtype sequences real_interval.
From mathcomp Require Import esum measure lebesgue_measure numfun realfun.
From mathcomp Require Import function_spaces.

(**md**************************************************************************)
(* # Simple functions                                                         *)
(*                                                                            *)
(* This file contains a formalization of simple functions and with basic      *)
(* properties (addition, etc.).                                               *)
(*                                                                            *)
(* About the use of simple functions:                                         *)
(* Because of a limitation of HB <= 1.8.0, we need some care to be able to    *)
(* use simple functions.                                                      *)
(* The structure SimpleFun (resp. NonNegSimpleFun) is located inside the      *)
(* module HBSimple (resp. HBNNSimple).                                        *)
(* As a consequence, we need to import HBSimple (resp. HBNNSimple) to use the *)
(* coercion from simple functions (resp. non-negative simple functions) to    *)
(* Rocq functions.                                                            *)
(* Also, assume that f (e.g., cst, indic) is equipped with the structure of   *)
(* MeasurableFun. For f to be equipped with the structure of SimpleFun        *)
(* (resp. NonNegSimpleFun), one need locally to import HBSimple (resp.        *)
(* HBNNSimple) and to instantiate FiniteImage (resp. NonNegFun) locally.      *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ````                                                                       *)
(*       {mfun aT >-> rT} == type of measurable functions                     *)
(*                           aT and rT are sigmaRingType's.                   *)
(*             f \in mfun == holds for f : {mfun _ >-> _}                     *)
(*         {sfun T >-> R} == type of simple functions                         *)
(*       {nnsfun T >-> R} == type of non-negative simple functions            *)
(*              mindic mD := \1_D where mD is a proof that D is measurable    *)
(*          indic_mfun mD := mindic mD                                        *)
(*         scale_mfun k f := k \o* f                                          *)
(*           max_mfun f g := f \max g                                         *)
(*          indic_sfun mD := mindic _ mD                                      *)
(*             cst_sfun r == constant simple function                         *)
(*           max_sfun f g := f \max f                                         *)
(*           cst_nnsfun r == constant simple function                         *)
(*                nnsfun0 := cst_nnsfun 0                                     *)
(*         add_nnsfun f g := f \+ g                                           *)
(*         mul_nnsfun f g := f \* g                                           *)
(*         max_nnsfun f g := f \max g                                         *)
(*       proj_nssfun f mA == projection of the function f to the set A        *)
(*                            mA is a proof that A is measurable              *)
(*       scale_nnsfun k f == scales f by the non-negative real number k       *)
(*         sum_nnsfun f n := \big[add_nnsfun/nnsfun0]_(i < n) f i             *)
(*      bigmax_nnsfun f n := \big[max_nnsfun/nnsfun0]_(i < n) f i             *)
(* ````                                                                       *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'mfun' aT >-> T }"
  (at level 0, format "{ 'mfun'  aT  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").
Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

#[global]
Hint Extern 0 (measurable [set _]) => solve [apply: measurable_set1] : core.

HB.mixin Record isMeasurableFun d d' (aT : sigmaRingType d) (rT : sigmaRingType d')
    (f : aT -> rT) := {
  measurable_funPT : measurable_fun [set: aT] f
}.
HB.structure Definition MeasurableFun d d' aT rT :=
  {f of @isMeasurableFun d d' aT rT f}.
Arguments measurable_funPT {d d' aT rT} s.

Notation "{ 'mfun' aT >-> T }" := (@MeasurableFun.type _ _ aT T) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (measurable_fun [set: _] _) =>
  solve [apply: measurable_funPT] : core.

Lemma measurable_funP {d d' : measure_display}
  {aT : measurableType d} {rT : sigmaRingType d'}
  (D : set aT) (s : {mfun aT >-> rT}) : measurable_fun D s.
Proof.
move=> mD Y mY; apply: measurableI => //.
by rewrite -(setTI (_ @^-1` _)); exact: measurable_funPT.
Qed.
Arguments measurable_funP {d d' aT rT D} s.

Module HBSimple.

HB.structure Definition SimpleFun d (aT : sigmaRingType d) (rT : realType) :=
  {f of @isMeasurableFun d _ aT rT f & @FiniteImage aT rT f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Lemma measurable_sfunP {d d'} {aT : measurableType d} {rT : measurableType d'}
  (f : {mfun aT >-> rT}) (Y : set rT) : measurable Y -> measurable (f @^-1` Y).
Proof. by move=> mY; rewrite -[f @^-1` _]setTI; exact: measurable_funP. Qed.

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
by rewrite (unstable.bigmax_sup_seq _ _ (lexx _)).
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

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%:nng.

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

Definition scale_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (NngNum k0)) f.

Definition proj_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Section mrestrict.
Import HBNNSimple.

Lemma mrestrict d (T : measurableType d) (R : realType) (f : {nnsfun T >-> R})
  A (mA : measurable A) : f \_ A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

End mrestrict.

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
