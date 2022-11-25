(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions cardinality mathcomp_extra.
Require Import signed reals ereal topology normedtype sequences.

(******************************************************************************)
(* This file provides definitions and lemmas about numerical functions.       *)
(*                                                                            *)
(*              f ^\+ == the function formed by the non-negative outputs      *)
(*                       of f (from a type to the type of extended real       *)
(*                       numbers) and 0 otherwise                             *)
(*                       rendered as f ⁺ with company-coq (U+207A)            *)
(*              f ^\- == the function formed by the non-positive outputs      *)
(*                       of f and 0 o.w.                                      *)
(*                       rendered as f ⁻ with company-coq (U+207B)            *)
(*              \1_ A == indicator function 1_A                               *)
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

Section funposneg.
Local Open Scope ereal_scope.

Definition funepos T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (f x) 0.
Definition funeneg T (R : realDomainType) (f : T -> \bar R) :=
  fun x => maxe (- f x) 0.

End funposneg.

Notation "f ^\+" := (funepos f) : ereal_scope.
Notation "f ^\-" := (funeneg f) : ereal_scope.

Section funposneg_lemmas.
Local Open Scope ereal_scope.
Variables (T : Type) (R : realDomainType) (D : set T).
Implicit Types (f g : T -> \bar R) (r : R).

Lemma funepos_ge0 f x : 0 <= f^\+ x.
Proof. by rewrite /funepos /= le_maxr lexx orbT. Qed.

Lemma funeneg_ge0 f x : 0 <= f^\- x.
Proof. by rewrite /funeneg le_maxr lexx orbT. Qed.

Lemma funeposN f : (\- f)^\+ = f^\-. Proof. exact/funext. Qed.

Lemma funenegN f : (\- f)^\- = f^\+.
Proof. by apply/funext => x; rewrite /funeneg oppeK. Qed.

Lemma funepos_restrict f : (f \_ D)^\+ = (f^\+) \_ D.
Proof.
by apply/funext => x; rewrite /patch/_^\+; case: ifP; rewrite //= maxxx.
Qed.

Lemma funeneg_restrict f : (f \_ D)^\- = (f^\-) \_ D.
Proof.
by apply/funext => x; rewrite /patch/_^\-; case: ifP; rewrite //= oppr0 maxxx.
Qed.

Lemma ge0_funeposE f : (forall x, D x -> 0 <= f x) -> {in D, f^\+ =1 f}.
Proof. by move=> f0 x; rewrite inE => Dx; apply/max_idPl/f0. Qed.

Lemma ge0_funenegE f : (forall x, D x -> 0 <= f x) -> {in D, f^\- =1 cst 0}.
Proof.
by move=> f0 x; rewrite inE => Dx; apply/max_idPr; rewrite lee_oppl oppe0 f0.
Qed.

Lemma le0_funeposE f : (forall x, D x -> f x <= 0) -> {in D, f^\+ =1 cst 0}.
Proof. by move=> f0 x; rewrite inE => Dx; exact/max_idPr/f0. Qed.

Lemma le0_funenegE f : (forall x, D x -> f x <= 0) -> {in D, f^\- =1 \- f}.
Proof.
by move=> f0 x; rewrite inE => Dx; apply/max_idPl; rewrite lee_oppr oppe0 f0.
Qed.

Lemma gt0_funeposM r f : (0 < r)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => r%:E * (f^\+ x)).
Proof. by move=> ?; rewrite funeqE => x; rewrite /funepos maxeMr// mule0. Qed.

Lemma gt0_funenegM r f : (0 < r)%R ->
  (fun x => r%:E * f x)^\- = (fun x => r%:E * (f^\- x)).
Proof.
by move=> r0; rewrite funeqE => x; rewrite /funeneg -muleN maxeMr// mule0.
Qed.

Lemma lt0_funeposM r f : (r < 0)%R ->
  (fun x => r%:E * f x)^\+ = (fun x => - r%:E * (f^\- x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funeposN gt0_funenegM -1?ltr_oppr ?oppr0.
Qed.

Lemma lt0_funenegM r f : (r < 0)%R ->
  (fun x => r%:E * f x)^\- = (fun x => - r%:E * (f^\+ x)).
Proof.
move=> r0; rewrite -[in LHS](opprK r); under eq_fun do rewrite EFinN mulNe.
by rewrite funenegN gt0_funeposM -1?ltr_oppr ?oppr0.
Qed.

Lemma fune_abse f : abse \o f = f^\+ \+ f^\-.
Proof.
rewrite funeqE => x /=; have [fx0|/ltW fx0] := leP (f x) 0.
- rewrite lee0_abs// /funepos /funeneg.
  move/max_idPr : (fx0) => ->; rewrite add0e.
  by move: fx0; rewrite -{1}oppr0 EFinN lee_oppr => /max_idPl ->.
- rewrite gee0_abs// /funepos /funeneg; move/max_idPl : (fx0) => ->.
  by move: fx0; rewrite -{1}oppr0 EFinN lee_oppl => /max_idPr ->; rewrite adde0.
Qed.

Lemma funeposneg f : f = (fun x => f^\+ x - f^\- x).
Proof.
rewrite funeqE => x; rewrite /funepos /funeneg; have [|/ltW] := leP (f x) 0.
  by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite oppeK add0e.
by rewrite -{1}oppe0 -lee_oppl => /max_idPr ->; rewrite sube0.
Qed.

Lemma add_def_funeposneg f x : (f^\+ x +? - f^\- x).
Proof.
by rewrite /funeneg /funepos; case: (f x) => [r| |];
  [rewrite !maxEFin|rewrite /maxe /= ltNyr|rewrite /maxe /= ltNyr].
Qed.

Lemma funeD_Dpos f g : f \+ g = (f \+ g)^\+ \- (f \+ g)^\-.
Proof.
apply/funext => x; rewrite /funepos /funeneg; have [|/ltW] := leP 0 (f x + g x).
- by rewrite -{1}oppe0 -lee_oppl => /max_idPr ->; rewrite sube0.
- by rewrite -{1}oppe0 -lee_oppr => /max_idPl ->; rewrite oppeK add0e.
Qed.

Lemma funeD_posD f g : f \+ g = (f^\+ \+ g^\+) \- (f^\- \+ g^\-).
Proof.
apply/funext => x; rewrite /funepos /funeneg.
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

End funposneg_lemmas.
#[global]
Hint Extern 0 (is_true (0 <= _ ^\+ _)%E) => solve [apply: funepos_ge0] : core.
#[global]
Hint Extern 0 (is_true (0 <= _ ^\- _)%E) => solve [apply: funeneg_ge0] : core.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R := (x \in A)%:R.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

Lemma indicE {T} {R : ringType} (A : set T) (x : T) :
  indic A x = (x \in A)%:R :> R.
Proof. by []. Qed.

Lemma indicT {T} {R : ringType} : \1_[set: T] = cst (1 : R).
Proof. by apply/funext=> x; rewrite indicE in_setT. Qed.

Lemma indic0 {T} {R : ringType} : \1_(@set0 T) = cst (0 : R).
Proof. by apply/funext=> x; rewrite indicE in_set0. Qed.

Lemma indic_restrict {T : pointedType} {R : numFieldType} (A : set T) :
  \1_A = 1 \_ A :> (T -> R).
Proof. by apply/funext => x; rewrite indicE /patch; case: ifP. Qed.

Lemma restrict_indic T (R : numFieldType) (E A : set T) :
  (\1_E \_ A) = \1_(E `&` A) :> (T -> R).
Proof.
apply/funext => x; rewrite /restrict 2!indicE.
case: ifPn => [|] xA; first by rewrite in_setI xA andbT.
by rewrite in_setI (negbTE xA) andbF.
Qed.

Lemma preimage_indic (T : Type) (R : ringType) (D : set T) (B : set R) :
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

Lemma image_indic T (R : ringType) (D A : set T) :
  \1_D @` A = (if A `\` D != set0 then [set 0] else set0) `|`
              (if A `&` D != set0 then [set 1 : R] else set0).
Proof.
rewrite /indic; apply/predeqP => x; split => [[t At /= <-]|].
  by rewrite /indic; case: (boolP (t \in D)); rewrite ?(inE, notin_set) => Dt;
     [right|left]; rewrite ifT//=; apply/set0P; exists t.
by move=> []; case: ifPn; rewrite ?negbK// => /set0P[t [At Dt]] ->;
   exists t => //; case: (boolP (t \in D)); rewrite ?(inE, notin_set).
Qed.

Lemma image_indic_sub T (R : ringType) (D A : set T) :
  \1_D @` A `<=` [set (0 : R); 1].
Proof.
by rewrite image_indic; do ![case: ifP=> //= _] => // t []//= ->; [left|right].
Qed.
