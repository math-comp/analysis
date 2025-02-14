(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets fsbigop.
From mathcomp Require Import functions cardinality set_interval itv reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import function_spaces.

(**md**************************************************************************)
(* # Numerical functions                                                      *)
(*                                                                            *)
(* This file provides definitions and lemmas about numerical functions.       *)
(*                                                                            *)
(* ```                                                                        *)
(*    {nnfun T >-> R} == type of non-negative functions                       *)
(*              f ^\+ == the function formed by the non-negative outputs      *)
(*                       of f (from a type to the type of extended real       *)
(*                       numbers) and 0 otherwise                             *)
(*                       rendered as f ⁺ with company-coq (U+207A)            *)
(*              f ^\- == the function formed by the non-positive outputs      *)
(*                       of f and 0 o.w.                                      *)
(*                       rendered as f ⁻ with company-coq (U+207B)            *)
(*              \1_ A == indicator function 1_A                               *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.mixin Record isNonNegFun (aT : Type) (rT : numDomainType) (f : aT -> rT) := {
  fun_ge0 : forall x, (0 <= f x)%R
}.
HB.structure Definition NonNegFun aT rT := {f of @isNonNegFun aT rT f}.
Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Notation "{ 'nnfun' aT >-> T }" := (@NonNegFun.type aT T) : form_scope.
Notation "[ 'nnfun' 'of' f ]" := [the {nnfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: fun_ge0] : core.

Section fimfun_bin.
Context (T : Type) (R : numDomainType).
Variables f g : {fimfun T >-> R}.

Lemma max_fimfun_subproof : @FiniteImage T R (f \max g).
Proof. by split; apply: (finite_image11 maxr). Qed.
HB.instance Definition _ := max_fimfun_subproof.

End fimfun_bin.

Reserved Notation "f ^\+" (at level 1, format "f ^\+").
Reserved Notation "f ^\-" (at level 1, format "f ^\-").

Section restrict_lemmas.
Context {aT : Type} {rT : numFieldType}.
Implicit Types (f g : aT -> rT) (D : set aT).

Lemma restrict_set0 f : f \_ set0 = cst 0.
Proof. by rewrite patch_set0. Qed.

Lemma restrict_ge0 D f :
  (forall x, D x -> 0 <= f x) -> forall x, 0 <= (f \_ D) x.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma ler_restrict D f g :
  (forall x, D x -> f x <= g x) -> forall x, (f \_ D) x <= (g \_ D) x.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma restrict_normr D f : (normr \o f) \_ D = normr \o (f \_ D).
Proof.
by apply/funext => t; rewrite /= !patchE; case: ifPn =>// tD; rewrite ger0_norm.
Qed.

End restrict_lemmas.

Lemma erestrict_ge0 {aT} {rT : numFieldType} (D : set aT) (f : aT -> \bar rT) :
  (forall x, D x -> (0 <= f x)%E) -> forall x, (0 <= (f \_ D) x)%E.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma lee_restrict {aT} {rT : numFieldType} (D : set aT) (f g : aT -> \bar rT) :
  (forall x, D x -> f x <= g x)%E -> forall x, ((f \_ D) x <= (g \_ D) x)%E.
Proof. by move=> f0 x; rewrite /patch; case: ifP => // /set_mem/f0->. Qed.

Lemma restrict_lee {aT} {rT : numFieldType} (D E : set aT) (f : aT -> \bar rT) :
  (forall x, E x -> 0 <= f x)%E ->
  D `<=` E -> forall x, ((f \_ D) x <= (f \_ E) x)%E.
Proof.
move=> f0 ED x; rewrite /restrict; case: ifPn => [xD|xD].
  by rewrite mem_set//; apply: ED; rewrite in_setE in xD.
by case: ifPn => // xE; apply: f0; rewrite in_setE in xE.
Qed.

Section erestrict_lemmas.
Local Open Scope ereal_scope.
Variables (T : Type) (R : realDomainType) (D : set T).
Implicit Types (f g : T -> \bar R) (r : R).

Lemma erestrict_set0 f : f \_ set0 = cst 0.
Proof. by rewrite patch_set0. Qed.

Lemma erestrict0 : (cst 0 : T -> \bar R) \_ D = cst 0.
Proof. by apply/funext => x; rewrite /patch/=; case: ifP. Qed.

Lemma erestrictD f g : (f \+ g) \_ D = f \_ D \+ g \_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?adde0. Qed.

Lemma erestrictN f : (\- f) \_ D = \- f \_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?oppe0. Qed.

Lemma erestrictB f g : (f \- g) \_ D = f \_ D \- g \_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?sube0. Qed.

Lemma erestrictM f g : (f \* g) \_ D = f \_ D \* g \_ D.
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?mule0. Qed.

Lemma erestrict_scale k f :
  (fun x => k%:E * f x) \_ D = (fun x => k%:E * (f \_ D) x).
Proof. by apply/funext=> x; rewrite /patch/=; case: ifP; rewrite ?mule0. Qed.

End erestrict_lemmas.

HB.lock
Definition funepos T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (f x) 0.
HB.lock
Definition funeneg T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (oppe (f x)) 0.

Notation "f ^\+" := (funepos f) : ereal_scope.
Notation "f ^\-" := (funeneg f) : ereal_scope.

Section funposneg_lemmas.
Local Open Scope ereal_scope.
Variables (T U : Type) (R : realDomainType) (D : set T).
Implicit Types (f g : T -> \bar R) (h : U -> T) (r : R).

Lemma funeposE f x : f^\+ x = maxe (f x) 0.
Proof. by rewrite unlock. Qed.

Lemma funenegE f x : f^\- x = maxe (- f x) 0.
Proof. by rewrite unlock. Qed.

Lemma funepos_ge0 f x : 0 <= f^\+ x.
Proof. by rewrite funeposE le_max lexx orbT. Qed.

Lemma funeneg_ge0 f x : 0 <= f^\- x.
Proof. by rewrite funenegE le_max lexx orbT. Qed.

Lemma funeposN f : (\- f)^\+ = f^\-.
Proof. by apply/funext => x; rewrite funeposE funenegE. Qed.

Lemma funenegN f : (\- f)^\- = f^\+.
Proof. by apply/funext => x; rewrite funeposE funenegE oppeK. Qed.

Lemma funepos_comp f h : (f \o h)^\+ = f^\+ \o h.
Proof. by rewrite !unlock. Qed.

Lemma funeneg_comp f h : (f \o h)^\- = f^\- \o h.
Proof. by rewrite !unlock. Qed.

Lemma funepos_restrict f : (f \_ D)^\+ = (f^\+) \_ D.
Proof.
by apply/funext => x; rewrite /patch !funeposE; case: ifP; rewrite //= maxxx.
Qed.

Lemma funeneg_restrict f : (f \_ D)^\- = (f^\-) \_ D.
Proof.
apply/funext => x; rewrite /patch !funenegE.
by case: ifP; rewrite //= oppr0 maxxx.
Qed.

Lemma ge0_funeposE f : (forall x, D x -> 0 <= f x) -> {in D, f^\+ =1 f}.
Proof. by move=> f0 x; rewrite inE funeposE => Dx; apply/max_idPl/f0. Qed.

Lemma ge0_funenegE f : (forall x, D x -> 0 <= f x) -> {in D, f^\- =1 cst 0}.
Proof.
move=> f0 x; rewrite inE funenegE => Dx; apply/max_idPr.
by rewrite leeNl oppe0 f0.
Qed.

Lemma le0_funeposE f : (forall x, D x -> f x <= 0) -> {in D, f^\+ =1 cst 0}.
Proof. by move=> f0 x; rewrite inE funeposE => Dx; exact/max_idPr/f0. Qed.

Lemma le0_funenegE f : (forall x, D x -> f x <= 0) -> {in D, f^\- =1 \- f}.
Proof.
move=> f0 x; rewrite inE funenegE => Dx; apply/max_idPl.
by rewrite leeNr oppe0 f0.
Qed.

Lemma ge0_funeposM r f : (0 <= r)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => r%:E * (f^\+ x)).
Proof.
move=> ?; rewrite funeqE => x.
by rewrite !funeposE maxe_pMr// mule0.
Qed.

Lemma ge0_funenegM r f : (0 <= r)%R ->
  (fun x => r%:E * f x)^\- = (fun x => r%:E * (f^\- x)).
Proof.
by move=> r0; rewrite funeqE => x; rewrite !funenegE -muleN maxe_pMr// mule0.
Qed.

Lemma le0_funeposM r f : (r <= 0)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => - r%:E * (f^\- x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funeposN ge0_funenegM ?oppr_ge0.
Qed.

Lemma le0_funenegM r f : (r <= 0)%R ->
  (fun x => r%:E * f x)^\- = (fun x => - r%:E * (f^\+ x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funenegN ge0_funeposM ?oppr_ge0.
Qed.

Lemma fune_abse f : abse \o f = f^\+ \+ f^\-.
Proof.
rewrite funeqE => x /=; have [fx0|/ltW fx0] := leP (f x) 0.
- rewrite lee0_abs// funeposE funenegE.
  move/max_idPr : (fx0) => ->; rewrite add0e.
  by move: fx0; rewrite -{1}oppe0 leeNr => /max_idPl ->.
- rewrite gee0_abs// funeposE funenegE; move/max_idPl : (fx0) => ->.
  by move: fx0; rewrite -{1}oppe0 leeNl => /max_idPr ->; rewrite adde0.
Qed.

Lemma funeposneg f : f = (fun x => f^\+ x - f^\- x).
Proof.
rewrite funeqE => x; rewrite funeposE funenegE; have [|/ltW] := leP (f x) 0.
  by rewrite -{1}oppe0 -leeNr => /max_idPl ->; rewrite oppeK add0e.
by rewrite -{1}oppe0 -leeNl => /max_idPr ->; rewrite sube0.
Qed.

Lemma add_def_funeposneg f x : (f^\+ x +? - f^\- x).
Proof.
by rewrite funenegE funeposE; case: (f x) => [r| |];
  [rewrite -fine_max/=|rewrite /maxe /= ltNyr|rewrite /maxe /= ltNyr].
Qed.

Lemma funeD_Dpos f g : f \+ g = (f \+ g)^\+ \- (f \+ g)^\-.
Proof.
apply/funext => x; rewrite funeposE funenegE; have [|/ltW] := leP 0 (f x + g x).
- by rewrite -{1}oppe0 -leeNl => /max_idPr ->; rewrite sube0.
- by rewrite -{1}oppe0 -leeNr => /max_idPl ->; rewrite oppeK add0e.
Qed.

Lemma funeD_posD f g : f \+ g = (f^\+ \+ g^\+) \- (f^\- \+ g^\-).
Proof.
apply/funext => x; rewrite !funeposE !funenegE.
have [|fx0] := leP 0 (f x); last rewrite add0e.
- rewrite -{1}oppe0 leeNl => /max_idPr ->; have [|/ltW] := leP 0 (g x).
    by rewrite -{1}oppe0 leeNl => /max_idPr ->; rewrite adde0 sube0.
  by rewrite -{1}oppe0 -leeNr => /max_idPl ->; rewrite adde0 sub0e oppeK.
- move/ltW : (fx0); rewrite -{1}oppe0 leeNr => /max_idPl ->.
  have [|] := leP 0 (g x); last rewrite add0e.
    by rewrite -{1}oppe0 leeNl => /max_idPr ->; rewrite adde0 oppeK addeC.
  move gg' : (g x) => g'; move: g' gg' => [g' gg' g'0|//|goo _].
  + move/ltW : (g'0); rewrite -{1}oppe0 -leeNr => /max_idPl => ->.
    by rewrite fin_num_oppeD// 2!oppeK.
  + by rewrite /maxe /=; case: (f x) fx0.
Qed.

Lemma funepos_le f g :
  {in D, forall x, f x <= g x} -> {in D, forall x, f^\+ x <= g^\+ x}.
Proof.
move=> fg x Dx; rewrite !funeposE /maxe; case: ifPn => fx; case: ifPn => gx //.
- by rewrite leNgt.
- by move: fx; rewrite -leNgt => /(lt_le_trans gx); rewrite ltNge fg.
- exact: fg.
Qed.

Lemma funeneg_le f g :
  {in D, forall x, f x <= g x} -> {in D, forall x, g^\- x <= f^\- x}.
Proof.
move=> fg x Dx; rewrite !funenegE /maxe; case: ifPn => gx; case: ifPn => fx //.
- by rewrite leNgt.
- by move: gx; rewrite -leNgt => /(lt_le_trans fx); rewrite lteN2 ltNge fg.
- by rewrite leeN2; exact: fg.
Qed.

End funposneg_lemmas.
#[global]
Hint Extern 0 (is_true (0%R <= _ ^\+ _)%E) => solve [apply: funepos_ge0] : core.
#[global]
Hint Extern 0 (is_true (0%R <= _ ^\- _)%E) => solve [apply: funeneg_ge0] : core.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R := (x \in A)%:R.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

Section indic_lemmas.
Context (T : Type) (R : ringType).
Implicit Types A D : set T.

Lemma indicE A (x : T) : \1_A x = (x \in A)%:R :> R. Proof. by []. Qed.

Lemma indicT : \1_[set: T] = cst (1 : R).
Proof. by apply/funext=> x; rewrite indicE in_setT. Qed.

Lemma indic0 : \1_(@set0 T) = cst (0 : R).
Proof. by apply/funext=> x; rewrite indicE in_set0. Qed.

Lemma indicI A B : \1_(A `&` B) = \1_A \* \1_B :> (_ -> R).
Proof. by apply/funext=> u/=; rewrite !indicE in_setI -natrM mulnb. Qed.

Lemma image_indic D A :
  \1_D @` A = (if A `\` D != set0 then [set 0] else set0) `|`
              (if A `&` D != set0 then [set 1 : R] else set0).
Proof.
rewrite /indic; apply/predeqP => x; split => [[t At /= <-]|].
  by rewrite /indic; case: (boolP (t \in D)); rewrite ?(inE, notin_setE) => Dt;
     [right|left]; rewrite ifT//=; apply/set0P; exists t.
by move=> []; case: ifPn; rewrite ?negbK// => /set0P[t [At Dt]] ->;
   exists t => //; case: (boolP (t \in D)); rewrite ?(inE, notin_setE).
Qed.

Lemma preimage_indic (D : set T) (B : set R) :
  \1_D @^-1` B = if 1 \in B then (if 0 \in B then setT else D)
                            else (if 0 \in B then ~` D else set0).
Proof.
rewrite /preimage/= /indic; apply/seteqP; split => x;
  case: ifPn => B1; case: ifPn => B0 //=.
- have [|] := boolP (x \in D); first by rewrite inE.
  by rewrite notin_setE in B0.
- have [|] := boolP (x \in D); last by rewrite notin_setE.
  by rewrite notin_setE in B1.
- by have [xD|xD] := boolP (x \in D);
    [rewrite notin_setE in B1|rewrite notin_setE in B0].
- by have [xD|xD] := boolP (x \in D); [rewrite inE in B1|rewrite inE in B0].
- have [xD|] := boolP (x \in D); last by rewrite notin_setE.
  by rewrite inE in B1.
- have [|xD] := boolP (x \in D); first by rewrite inE.
  by rewrite inE in B0.
Qed.

Lemma image_indic_sub D A : \1_D @` A `<=` ([set 0; 1] : set R).
Proof.
by rewrite image_indic; do ![case: ifP=> //= _] => // t []//= ->; [left|right].
Qed.

Lemma fimfunE (f : {fimfun T >-> R}) x :
  f x = \sum_(y \in range f) (y * \1_(f @^-1` [set y]) x).
Proof.
rewrite (fsbigD1 (f x))// /= indicE mem_set// mulr1 fsbig1 ?addr0//.
by move=> y [fy /= /nesym yfx]; rewrite indicE memNset ?mulr0.
Qed.

Lemma fimfunEord (f : {fimfun T >-> R})
    (s := fset_set (f @` setT)) :
  forall x, f x = \sum_(i < #|`s|) (s`_i * \1_(f @^-1` [set s`_i]) x).
Proof.
move=> x; rewrite fimfunE fsbig_finite//= (big_nth 0)/= big_mkord.
exact: eq_bigr.
Qed.

End indic_lemmas.

Lemma patch_indic T {R : numFieldType} (f : T -> R) (D : set T) :
  f \_ D = (f \* \1_D)%R.
Proof.
apply/funext => x /=; rewrite patchE /= indicE.
by case: ifPn => _; rewrite ?(mulr1, mulr0).
Qed.

Lemma epatch_indic T (R : numDomainType) (f : T -> \bar R) (D : set T) :
  (f \_ D = f \* (EFin \o \1_D))%E.
Proof.
apply/funext => x; rewrite patchE/= indicE.
by case: ifPn => /=; rewrite ?mule1// mule0.
Qed.

Lemma xsection_indic (R : ringType) T1 T2 (A : set (T1 * T2)) x :
  xsection A x = (fun y => (\1_A (x, y) : R)) @^-1` [set 1].
Proof.
apply/seteqP; split => [y/mem_set/=|y/=]; rewrite indicE.
  by rewrite mem_xsection => ->.
by rewrite /xsection/=; case: (_ \in _) => //= /esym/eqP /[!oner_eq0].
Qed.

Lemma ysection_indic (R : ringType) T1 T2 (A : set (T1 * T2)) y :
  ysection A y = (fun x => (\1_A (x, y) : R)) @^-1` [set 1].
Proof.
apply/seteqP; split => [x/mem_set/=|x/=]; rewrite indicE.
  by rewrite mem_ysection => ->.
by rewrite /ysection/=; case: (_ \in _) => //= /esym/eqP /[!oner_eq0].
Qed.

Lemma indic_restrict {T : pointedType} {R : numFieldType} (A : set T) :
  \1_A = (1 : T -> R) \_ A.
Proof. by apply/funext => x; rewrite indicE /patch; case: ifP. Qed.

Lemma restrict_indic T (R : numFieldType) (E A : set T) :
  ((\1_E : T -> R) \_ A) = \1_(E `&` A).
Proof.
apply/funext => x; rewrite /restrict 2!indicE.
case: ifPn => [|] xA; first by rewrite in_setI xA andbT.
by rewrite in_setI (negbTE xA) andbF.
Qed.

Lemma cvg_indic {R : realFieldType} (x : R^o) k :
  x \in (ball 0 k : set R^o) ->
  \1_(ball 0 k : set R^o) y @[y --> x] --> (\1_(ball 0 k) x : R).
Proof.
move=> xB; apply/(@cvgrPdist_le _ R^o) => /= e e0; near=> t.
rewrite !indicE xB/= mem_set//=; first by rewrite subrr normr0// ltW.
near: t.
rewrite inE /ball /= sub0r normrN in xB.
exists ((k - `|x|)/2) => /=; first by rewrite divr_gt0// subr_gt0.
rewrite /ball_/= => z /= h; rewrite /ball/= sub0r normrN.
rewrite -(subrK x z) (le_lt_trans (ler_normD _ _))//.
rewrite -ltrBrDr distrC (lt_le_trans h)//.
by rewrite ler_pdivrMr//= ler_pMr// ?subr_gt0// ler1n.
Unshelve. all: by end_near. Qed.

Section ring.
Context (aT : pointedType) (rT : ringType).

Lemma fimfun_mulr_closed : mulr_closed (@fimfun aT rT).
Proof.
split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst.
by move=> fA gA; exact: (finite_image11 (fun x y => x * y)).
Qed.

HB.instance Definition _ :=
   @GRing.isMulClosed.Build _ (@fimfun aT rT) fimfun_mulr_closed.
HB.instance Definition _ := [SubZmodule_isSubRing of {fimfun aT >-> rT} by <:].

Implicit Types f g : {fimfun aT >-> rT}.

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

Definition indic_fimfun (X : set aT) : {fimfun aT >-> rT} := \1_X.

HB.instance Definition _ k f := FImFun.copy (k \o* f) (f * cst_fimfun k).

Definition scale_fimfun k f : {fimfun aT >-> rT} := k \o* f.

End ring.
Arguments indic_fimfun {aT rT} _.

Section comring.
Context (aT : pointedType) (rT : comRingType).
HB.instance Definition _ := [SubRing_isSubComRing of {fimfun aT >-> rT} by <:].

Implicit Types (f g : {fimfun aT >-> rT}).
HB.instance Definition _ f g := FImFun.copy (f \* g) (f * g).
End comring.

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

Section Tietze.
Context {X : topologicalType} {R : realType}.

Hypothesis normalX : normal_space X.

Lemma urysohn_ext_itv A B x y :
  closed A -> closed B -> A `&` B = set0 -> x < y ->
  exists f : X -> R, [/\ continuous f,
    f @` A `<=` [set x], f @` B `<=` [set y] & range f `<=` `[x, y]].
Proof.
move=> cA cB A0 xy; move/normal_separatorP : normalX => urysohn_ext.
have /(@uniform_separatorP _ R)[f [cf f01 f0 f1]] := urysohn_ext R _ _ cA cB A0.
pose g : X -> R := line_path x y \o f; exists g; split; rewrite /g /=.
  move=> t; apply: continuous_comp; first exact: cf.
  apply: (@continuousD R R^o).
    apply: continuousM; last exact: cvg_cst.
    by apply: (@continuousB R R^o) => //; exact: cvg_cst.
  by apply: continuousM; [exact: cvg_id|exact: cvg_cst].
- by rewrite -image_comp => z /= [? /f0 -> <-]; rewrite line_path0.
- by rewrite -image_comp => z /= [? /f1 -> <-]; rewrite line_path1.
- rewrite -image_comp; apply: (subset_trans (image_subset _ f01)).
  by rewrite range_line_path.
Qed.

Context (A : set X).
Hypothesis clA : closed A.

Local Lemma tietze_step' (f : X -> R) (M : R) :
  0 < M -> {within A, continuous f} ->
  (forall x, A x -> `|f x| <= M) ->
  exists g : X -> R, [/\ continuous g,
     (forall x, A x -> `|f x - g x| <= 2/3 * M) &
     (forall x, `|g x| <= 1/3 * M)].
Proof.
move: M => _/posnumP[M] ctsf fA1.
have [] := @urysohn_ext_itv (A `&` f @^-1` `]-oo, -(1/3) * M%:num])
    (A `&` f @^-1` `[1/3 * M%:num,+oo[) (-(1/3) * M%:num) (1/3 * M%:num).
- by rewrite closed_setSI//; exact: closed_comp.
- by rewrite closed_setSI//; apply: closed_comp => //; exact: interval_closed.
- rewrite setIACA -preimage_setI eqEsubset; split => z // [_ []].
  rewrite !set_itvE/= => /[swap] /le_trans /[apply].
  by rewrite leNgt mulNr gtrN// mulr_gt0// divr_gt0.
- by rewrite mulNr gtrN// mulr_gt0//.
move=> g [ctsg gL3 gR3 grng]; exists g; split => //; first last.
  by move=> x; rewrite ler_norml -mulNr; apply: grng; exists x.
move=> x Ax; have := fA1 _ Ax; rewrite 2!ler_norml => /andP[Mfx fxM].
have [xL|xL] := leP (f x) (-(1/3) * M%:num).
  have: [set g x | x in A `&` f@^-1` `]-oo, -(1/3) * M%:num]] (g x) by exists x.
  move/gL3=> ->; rewrite !mulNr opprK; apply/andP; split.
    by rewrite -lerBlDr -opprD -2!mulrDl natr1 divrr ?unitfE// mul1r.
  rewrite -lerBrDr -2!mulrBl -(@natrB _ 2 1)// (le_trans xL)//.
  by rewrite ler_pM2r// ltW// gtrN// divr_gt0.
have [xR|xR] := lerP (1/3 * M%:num) (f x).
  have : [set g x | x in A `&` f@^-1` `[1/3 * M%:num, +oo[] (g x).
    by exists x => //; split => //; rewrite /= in_itv //= xR.
  move/gR3 => ->; apply/andP; split.
    rewrite lerBrDl -2!mulrBl (le_trans _ xR)// ler_pM2r//.
    by rewrite ler_wpM2r ?invr_ge0 ?ler0n// lerBlDl natr1 ler1n.
  by rewrite lerBlDl -2!mulrDl nat1r divrr ?mul1r// unitfE.
have /andP[ng3 pg3] : -(1/3) * M%:num <= g x <= 1/3 * M%:num.
  by apply: grng; exists x.
rewrite ?(intrD _ 1 1) !mulrDl; apply/andP; split.
  by rewrite opprD lerB// -mulNr ltW.
by rewrite (lerD (ltW _))// lerNl -mulNr.
Qed.

Let tietze_step (f : X -> R) M :
  {g : X -> R^o | {within A, continuous f} -> 0 < M ->
    (forall x, A x -> `|f x| <= M) -> [/\ continuous g,
      forall x, A x -> `|f x - g x| <= 2/3 * M :>R
      & forall x, `|g x| <= 1/3 * M ]}.
Proof.
apply: cid.
have [|?] := pselect ({within A, continuous f}); last by exists point.
have [|?] := ltP 0 M; last by exists point.
have [|?] := pselect (forall x, A x -> `|f x| <= M); last by exists point.
by move=> bd pm cf; have [g ?] := tietze_step' pm cf bd; exists g.
Qed.

Let onem_twothirds : 1 - 2/3 = 1/3 :> R.
Proof. by apply/eqP; rewrite subr_eq/= -mulrDl nat1r divrr// unitfE. Qed.

Lemma continuous_bounded_extension (f : X -> R^o) M :
  0 < M -> {within A, continuous f} -> (forall x, A x -> `|f x| <= M) ->
  exists g, [/\ {in A, f =1 g}, continuous g & forall x, `|g x| <= M].
Proof.
move: M => _/posnumP[M] Af fbd; pose M2d3 n := geometric M%:num (2/3) n.
have MN0 n : 0 < M2d3 n by rewrite /M2d3 /geometric /mk_sequence.
pose f_ := fix F n :=
  if n is n.+1 then F n - projT1 (tietze_step (F n) (M2d3 n)) else f.
pose g_ n := projT1 (tietze_step (f_ n) (M2d3 n)).
have fgE n : f_ n - f_ n.+1 = g_ n by rewrite /= opprB addrC subrK.
have twothirds1 : `|2/3| < 1 :> R.
  by rewrite gtr0_norm//= ltr_pdivrMr// mul1r ltr_nat.
have f_geo n : {within A, continuous f_ n} /\
    (forall x, A x -> `|f_ n x| <= geometric M%:num (2/3) n).
  elim: n => [|n [ctsN bdN]]; first by split=> //= x ?; rewrite expr0 mulr1 fbd.
  have [cg bdNS bd2] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdN.
  split=> [x|]; first by apply: cvgB; [exact:ctsN|exact/continuous_subspaceT/cg].
  by move=> x Ax; rewrite (le_trans (bdNS _ Ax))// /M2d3/= mulrCA -exprS.
have g_cts n : continuous (g_ n).
  by have [? ?] := f_geo n; case: (projT2 (tietze_step (f_ n) _) _ (MN0 n)).
have g_bd n : forall x, `|g_ n x| <= geometric ((1/3) * M%:num) (2/3) n.
  have [ctsN bdfN] := f_geo n; rewrite /geometric /= -[_ * M%:num * _]mulrA.
  by have [_ _] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdfN.
pose h_ : nat -> arrow_uniform_type X R^o := @series {uniform X -> _} g_.
have cvgh' : cvg (h_ @ \oo).
  apply/cauchy_cvgP/cauchy_ballP => eps epos; near_simpl.
  suff : \forall x & x' \near \oo, (x' <= x)%N -> ball (h_ x) eps (h_ x').
    move=>/[dup]; rewrite {1}near_swap; apply: filter_app2; near=> n m.
    by have /orP[mn /(_ mn)/ball_sym + _| ? _] := leq_total n m; apply.
  near=> n m; move=> /= MN; rewrite /ball /= /h_ => t; rewrite /ball /=.
  rewrite -[X in `|X|]/((series g_ n - series g_ m) t) sub_series MN fct_sumE.
  rewrite (le_lt_trans (ler_norm_sum _ _ _))//.
  rewrite (le_lt_trans (ler_sum _ (fun i _ => g_bd i t)))// -mulr_sumr.
  rewrite -(subnKC MN) geometric_partial_tail.
  pose L := (1/3) * M%:num * ((2/3) ^+ m / (1 - (2/3))).
  apply: (@le_lt_trans _ _ L); first by rewrite ler_pM2l // geometric_le_lim.
  rewrite /L onem_twothirds.
  rewrite [_ ^+ _ * _ ^-1]mulrC mulrA -[x in x < _]ger0_norm; last by [].
  near: m; near_simpl; move: eps epos.
  by apply: (cvgr0_norm_lt (fun _ => _ : R^o)); exact: cvg_geometric.
have cvgh : {uniform, h_ @ \oo --> lim (h_ @ \oo)}.
  by move=> ?; rewrite /= uniform_nbhsT; exact: cvgh'.
exists (lim (h_ @ \oo)); split.
- move=> t /set_mem At; have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) :=
    [elaborate pointwise_uniform_cvg _ cvgh].
  rewrite -fmap_comp /comp /h_ => <-; apply/esym/(@cvg_lim _ (@Rhausdorff R)).
  apply: (@cvg_zero R R^o); apply: norm_cvg0; under eq_fun => n.
    rewrite distrC /series /cst /= -mulN1r fct_sumE mulr_sumr.
    under [fun _ : nat => _]eq_fun => ? do rewrite mulN1r -fgE opprB.
    rewrite telescope_sumr //= addrCA subrr addr0.
    over.
  apply/norm_cvg0P/cvgr0Pnorm_lt => eps epos.
  have /(_ _ epos)  := @cvgr0_norm_lt R _ _ _ eventually_filter (_ : nat -> R^o)
    (cvg_geometric M%:num twothirds1).
  apply: filter_app; near_simpl; apply: nearW => n /le_lt_trans; apply.
  by rewrite (le_trans ((f_geo n).2 _ _)) // ler_norm.
- apply: (@uniform_limit_continuous X _ (h_ @ \oo) (lim (h_ @ \oo))) =>//.
  near_simpl; apply: nearW; elim.
    by rewrite /h_ /series /= big_geq// => ?; exact: cvg_cst.
  move=> n; rewrite /h_ /series /= big_nat_recr /= // => IH t.
  by apply: continuousD; [exact: IH|exact: g_cts].
- move=> t.
  have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) :=
    [elaborate pointwise_uniform_cvg _ cvgh].
  rewrite -fmap_comp /comp /h_ => <-.
  under [fun _ : nat => _]eq_fun => ? do rewrite /series /= fct_sumE.
  have cvg_gt : cvgn [normed series (g_^~ t)].
    apply: (series_le_cvg _ _ (g_bd ^~ t) (is_cvg_geometric_series _)) => //.
    by move=> n; rewrite mulr_ge0.
  rewrite (le_trans (lim_series_norm _))//; apply: le_trans.
    exact/(lim_series_le cvg_gt _ (g_bd ^~ t))/is_cvg_geometric_series.
  rewrite (cvg_lim _ (cvg_geometric_series _))//; last exact: Rhausdorff.
  by rewrite onem_twothirds mulrAC divrr ?mul1r// unitfE.
Unshelve. all: by end_near. Qed.

End Tietze.
