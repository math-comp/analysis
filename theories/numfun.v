(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets fsbigop.
From mathcomp Require Import functions cardinality set_interval.
Require Import signed reals ereal topology normedtype sequences.

(******************************************************************************)
(* This file provides definitions and lemmas about numerical functions.       *)
(*                                                                            *)
(*    {nnfun T >-> R} == type of non-negative functions                       *)
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
  [rewrite -fine_max/=|rewrite /maxe /= ltNyr|rewrite /maxe /= ltNyr].
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
    by rewrite fin_num_oppeD// 2!oppeK.
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

Section indic_lemmas.
Context (T : Type) (R : ringType).
Implicit Types A D : set T.

Lemma indicE A (x : T) : \1_A x = (x \in A)%:R :> R. Proof. by []. Qed.

Lemma indicT : \1_[set: T] = cst (1 : R).
Proof. by apply/funext=> x; rewrite indicE in_setT. Qed.

Lemma indic0 : \1_(@set0 T) = cst (0 : R).
Proof. by apply/funext=> x; rewrite indicE in_set0. Qed.

Lemma preimage_indic D (B : set R) :
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

Lemma image_indic D A :
  \1_D @` A = (if A `\` D != set0 then [set 0] else set0) `|`
              (if A `&` D != set0 then [set 1 : R] else set0).
Proof.
rewrite /indic; apply/predeqP => x; split => [[t At /= <-]|].
  by rewrite /indic; case: (boolP (t \in D)); rewrite ?(inE, notin_set) => Dt;
     [right|left]; rewrite ifT//=; apply/set0P; exists t.
by move=> []; case: ifPn; rewrite ?negbK// => /set0P[t [At Dt]] ->;
   exists t => //; case: (boolP (t \in D)); rewrite ?(inE, notin_set).
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

End indic_lemmas.

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
  \1_A = 1 \_ A :> (T -> R).
Proof. by apply/funext => x; rewrite indicE /patch; case: ifP. Qed.

Lemma restrict_indic T (R : numFieldType) (E A : set T) :
  (\1_E \_ A) = \1_(E `&` A) :> (T -> R).
Proof.
apply/funext => x; rewrite /restrict 2!indicE.
case: ifPn => [|] xA; first by rewrite in_setI xA andbT.
by rewrite in_setI (negbTE xA) andbF.
Qed.

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
Context {X : topologicalType} {R : realType} (A : set X).
Hypothesis clA : closed A.
Hypothesis urysohn_ext : forall A B x y,
  closed A -> closed B -> A `&` B = set0 -> x <= y ->
  exists (f : X -> R^o), [/\ continuous f, 
    f @` A = [set x], f @` B = [set y] & range f `<=` `[x,y]].

Let three0 : 0 < 3 :> R.
Proof. by rewrite (_ : 0 = 0%:R) // ltr_nat. Qed.

Let threen0 : 3 != 0 :> R.
Proof. exact: lt0r_neq0. Qed.

Let thirds : -1/3 < 1/3 :>R.
Proof. by rewrite ltr_pmul2r ?gtr_opp// invr_gt0. Qed.

Local Lemma tietze_step' (f : X -> R^o) (M : R) :
  0 < M -> {within A, continuous f} ->
  (forall x, A x -> `|f x| <= M) ->
  exists (g : X -> R^o), [/\ continuous g, 
     (forall x, A x -> `|f x - g x| <= 2/3*M :>R) & 
     (forall x, `|g x| <= 1/3*M)].
Proof.
move=> mpos ctsf fA1.
have [] := @urysohn_ext 
    (A `&` f@^-1` `]-oo,-1/3 *M]) (A `&` f@^-1` `[1/3 * M,+oo[) 
    (-1/3 * M) (1/3 * M).
- by rewrite closed_setSI; apply: closed_comp => //.
- by rewrite closed_setSI; apply: closed_comp => //; exact: interval_closed.
- rewrite setIACA -preimage_setI eqEsubset; split => z // [_ []]. 
  rewrite ?set_itvE => /[swap] /le_trans /[apply]; rewrite ler_pmul2r //.
  by move=> W; move: thirds => /=; rewrite real_ltNge ?num_real // W.
- by rewrite ler_pmul2r //; exact: ltW.
move=> g [ctsg gL3 gR3 grng]; exists g; split => //; first last.
  by move=> x; rewrite ler_norml -?mulNr; apply: grng; exists x.
move=> x Ax; move: (fA1 _ Ax); rewrite ?ler_norml => /andP [? ?].
case xL : (f x <= -1/3 * M).
  have : [set g x | x in A `&` f@^-1` `]-oo, -1/3 * M]] (g x) by exists x.
  rewrite gL3 => ->; rewrite ?mulNr opprK; apply/andP; split.
    rewrite -ler_subl_addr -opprD -?mulrDl.
    by rewrite (_ : 2+1 = 3) ?divrr ?unitfE ?mul1r // addrC.
  rewrite -ler_subr_addr -?mulNr -?mulrDl (_ : 2-1 = 1).
    by apply: (le_trans xL); rewrite ler_pmul2r //; apply: ltW.
  by rewrite (_ : 2 = (1+1)) // -addrA subrr addr0.
case xR : (1/3 *M <= f x).
  have : [set g x | x in A `&` f@^-1` `[1/3 *M, +oo[] (g x).
    by exists x => //; split => //; rewrite /= in_itv //= xR.
  rewrite gR3 => ->; apply/andP; split.
    rewrite -ler_subl_addr opprK -?mulNr // -?mulrDl.
    rewrite (_ : 1*-2 = -(1 + 1)) // opprD -addrA.
    rewrite [-_ + _]addrC -addrA subrr addr0.
    by apply: (le_trans _ xR); rewrite ler_pmul2r //; apply: ltW.
  by rewrite -ler_subr_addr opprK -?mulrDl addrC divrr ?mul1r ?unitfE //.
have /andP [/ltW nf3 /ltW pf3] : -1/3 *M < f x < 1/3 *M.
  by apply/andP; split; rewrite real_ltNge ?num_real //= ?xL ?xR.
have /andP [ng3 pg3] : -1/3 * M <= g x <= 1/3 * M by apply: grng; exists x.
apply/andP; split; rewrite (_ : 2 = 1 + 1) // ?mulrDl.
  by rewrite ?opprD; apply: ler_sub; rewrite // -?mulNr.
by apply: ler_add; rewrite // ler_oppl -?mulNr.
Qed.

Let tietze_step (f : X -> R^o) M : 
  {g : X -> R^o | {within A, continuous f} -> 0 < M -> 
    (forall x, A x -> `|f x| <= M) -> [/\ continuous g, 
      (forall x, A x -> `|f x - g x| <= 2/3*M :>R)
      & (forall x, `|g x| <= 1/3*M)]}.
Proof.
apply: cid.
case : (pselect ({within A, continuous f})); last by move => ?; exists point.
case : (pselect (0 < M)); last by move => ?; exists point.
case : (pselect (forall x, A x -> `|f x| <=M)); last by move => ?; exists point.
by move=> bd pm cf; have [g ?] := tietze_step' pm cf bd; exists g.
Qed.

Let twothirds_pos : 0 < 2/3 :>R.
Proof. exact: divr_gt0 => //. Qed.

Let onethird_pos : 0 < 1/3 :>R.
Proof. exact: divr_gt0 => //. Qed.

Let twothirds := PosNum twothirds_pos.
Let onethird := PosNum onethird_pos.

Lemma continuous_bounded_extension (f : X -> R^o) M :
  (0 < M) -> {within A, continuous f} -> (forall x, A x -> `|f x| <= M) ->
  exists g, [/\ {in A, f =1 g}, continuous g & forall x, `|g x| <= M].
Proof.
move: M => _/posnumP[M] ? fbd; pose M2d3 n := geometric M%:num twothirds%:num n.
have MN0 n : 0 < M2d3 n by rewrite /M2d3/geometric/mk_sequence.
pose f_ := fix F n := 
  if n is n.+1 then (F n - projT1 (tietze_step (F n) (M2d3 n))) else f.
pose g_ n := projT1 (tietze_step (f_ n) (M2d3 n)).
have fgE n : f_ n - f_ n.+1 = g_ n.
  by rewrite /= opprB addrC -addrA [-_ + _] addrC subrr addr0.
have twothirds1 : `|twothirds%:num| < 1 :> R.
 by rewrite ger0_norm // ltr_pdivr_mulr // mul1r (_ : 3 = 1 + 2) // ltr_addr.
have f_geo n : {within A, continuous f_ n} /\
    (forall x, A x -> `|f_ n x| <= geometric M%:num twothirds%:num n).
  elim: n; first by split => // ? ?; rewrite /= expr0 mulr1; exact: fbd.
  move=> n [ctsN bdN].
  have [cg bdNS bd2] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdN; split.
    by move=> x; apply: cvgB; [exact: ctsN | exact/continuous_subspaceT/cg].
  rewrite /geometric /= exprS mulrA [M%:num * (_/_)] mulrC.
  by rewrite  -[_ * M%:num * _]mulrA; exact: bdNS.
have g_cts n : continuous (g_ n).
  by have [? ?] := f_geo n; case: (projT2 (tietze_step (f_ n) _) _ (MN0 n)).
have g_bd n : forall x, 
    `|g_ n x| <= geometric (onethird%:num * M%:num) (twothirds%:num) n.
  have [ctsN bdfN] := f_geo n; rewrite /geometric /= -[_ * M%:num * _]mulrA.
  by have [] := projT2 (tietze_step (f_ n) _) _ (MN0 n) _.
pose h_ : nat -> [completeType of {uniform X -> _}] := 
  @series [zmodType of {uniform X -> _}] g_.
have cvgh' : cvg (h_ @ \oo).
  apply/cauchy_cvgP/cauchy_ballP => eps epos; near_simpl.
  suff : \forall x & x' \near \oo, (x' <= x)%N -> ball (h_ x) eps (h_ x').
    move=>/[dup]; rewrite {1}near_swap; apply: filter_app2; near=> n m.
    by have /orP [mn /(_ mn)/ball_sym + _| ? _] := leq_total n m; apply. 
  near=> n m; move=> /= MN; rewrite /ball /= /ball /= /h_ => t; rewrite /ball /=. 
  rewrite (_: series g_ n t - series g_ m t = (series g_ n - series g_ m) t) //.
  rewrite /= sub_series MN fct_sumE; apply: (le_lt_trans (ler_norm_sum _ _ _)).
  apply: (le_lt_trans (ler_sum _ (fun i _ => g_bd i t))); rewrite -mulr_sumr.
  rewrite -(subnKC MN) geometric_partial_tail.
  pose L := onethird%:num * M%:num * ((twothirds%:num)^+m / (1-twothirds%:num)).
  apply: (@le_lt_trans _ _ L).
    by rewrite ler_pmul2l //; apply: geometric_le_lim. 
  rewrite /L; have -> : (1-twothirds%:num = onethird%:num).
    rewrite -(@divrr _ 3) /= ?unitfE // -mulrBl; congr(_ _ _); apply/eqP.
    by rewrite subr_eq.
  rewrite [_^+_ * _^-1]mulrC mulrA -[x in x < _]ger0_norm; last done.
  near: m; near_simpl; move: eps epos. 
  apply: (@cvgr0_norm_lt _ _ _ _ _ (fun m => _:R^o)); exact: cvg_geometric.
have cvgh : {uniform, h_ @ \oo --> lim (h_ @ \oo)}. 
  by move=> ?; rewrite /= ?uniform_nbhsT; apply: cvgh'.
exists (lim (h_ @ \oo)); split.
- move=> t /set_mem At; have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) :=
    !! pointwise_uniform_cvg _ cvgh.
  rewrite -fmap_comp /comp /h_ => <-; apply: esym. 
  apply: (@cvg_lim _ (@Rhausdorff R)). 
  apply: (@cvg_zero R [pseudoMetricNormedZmodType R of R^o]). 
  apply: norm_cvg0; under eq_fun => n. 
    rewrite distrC /series /cst /= -mulN1r fct_sumE mulr_sumr.
    under [fun (_ : nat) => _]eq_fun => ? do rewrite mulN1r -fgE opprB.
    rewrite telescope_sumr //= addrC -addrA [-_ + _]addrC subrr addr0.
    over.
  apply/norm_cvg0P/cvgr0Pnorm_lt => eps epos.
  have /(_ _ epos)  := @cvgr0_norm_lt R _ _ _ eventually_filter (_ : nat -> R^o)
    (cvg_geometric (M%:num :R^o) twothirds1).
  apply: filter_app; near_simpl; apply: nearW => n /le_lt_trans; apply.
  (apply: le_trans; first by case: (f_geo n) => _; apply); exact: ler_norm.
- apply: (@uniform_limit_continuous X _ (h_ @\oo) (lim (h_ @ \oo))) =>//.
  near_simpl; apply: nearW; elim.
    by rewrite /h_ /=/series /= ?big_geq // => ?; exact: cvg_cst.
  move=> n; rewrite /h_ /series /= big_nat_recr /= // => IH t.
  rewrite [_ + g_ _]/GRing.add /=; apply: cvgD; first exact: (IH t).
  exact: g_cts.
- move=> t.
  have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) := !! pointwise_uniform_cvg _ cvgh.
  rewrite -fmap_comp /comp /h_ => <-.
  under [fun (_:nat) => _]eq_fun => ? do rewrite /series /= fct_sumE.
  have ? : cvg ([normed series (g_^~ t)] : nat -> R^o).
    apply: (series_le_cvg _ _ (fun n => g_bd n t) ).
    - by move=> ?; done.
    - by move=> ?; rewrite /geometric /mk_sequence //.
    - exact: is_cvg_geometric_series.
  apply: le_trans; first exact: lim_series_norm. 
  apply: le_trans; first apply: (lim_series_le _ _ (fun n => g_bd n t)) => //.
    exact: is_cvg_geometric_series.
  rewrite (cvg_lim _ (cvg_geometric_series _)) => //.
  have /eqP -> : 1 - twothirds%:num == onethird%:num.
    by rewrite subr_eq -mulrDl divrr// unitfE.
  rewrite mulrAC divrr ?mul1r // unitfE //.
Unshelve. all: by end_near. Qed.

End Tietze.
