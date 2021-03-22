
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(*Require Import ssrsearch.*)
From mathcomp Require Import ssreflect ssrfun ssrbool fieldext falgebra vector.
From mathcomp Require Import ssrnat eqtype choice fintype bigop order ssralg ssrnum ssrfun.
From mathcomp Require Import complex.
From mathcomp Require Import boolp reals ereal derive.
Require Import classical_sets posnum topology normedtype landau.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.
Import numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I need to import ComplexField to use its lemmas on RComplex,
I don't want the canonical lmodtype structure on C,
Therefore this is based on a fork of real-closed *)
Section ComplexNumfieldType.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].

Local Canonical complex_pointedType := [pointedType of C for [pointedType of C^o]].
Local Canonical complex_filteredType :=
  [filteredType C of C for [filteredType C of C^o]].
Local Canonical complex_topologicalType :=
  [topologicalType of C for [topologicalType of C^o]].
Local Canonical complex_uniformType := [uniformType of C for [uniformType of C^o]].

Local Canonical complex_pseudoMetricType :=
  [pseudoMetricType [numDomainType of C] of C for [pseudoMetricType [numDomainType of C]  of C^o]].
(* missing join ? is [numDomainType of C] ok here ? *)

Local Canonical complex_lmodType := [lmodType C of C for [lmodType C of C^o]].
Local Canonical complex_lalgType := [lalgType C of C for [lalgType C of C^o]].
Local Canonical complex_algType := [algType C of C for [algType C of C^o]].
Local Canonical complex_comAlgType := [comAlgType C of C].
Local Canonical complex_unitAlgType := [unitAlgType C of C].
Local Canonical complex_comUnitAlgType := [comUnitAlgType C of C].
Local Canonical complex_vectType := [vectType C of C for [vectType C of C^o]].
Local Canonical complex_FalgType := [FalgType C of C].
Local Canonical complex_fieldExtType :=
  [fieldExtType C of C for [fieldExtType C of C^o]].
Local Canonical complex_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType C of C for [pseudoMetricNormedZmodType C of C^o]].
Local Canonical complex_normedModType :=
  [normedModType C of C for [normedModType C of C^o]]. 

(* TODO : joins*)  

End ComplexNumfieldType.


Section complex_extras.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].

(*Adapting lemma eq_complex from complex.v, which was done in boolean style*)
Lemma eqE_complex : forall (x y : C), (x = y) = ((Re x = Re y) /\ (Im x = Im y)).
Proof.
move=> [a b] [c d]; apply : propositional_extensionality ; split.
by move=> -> ; split.
by case=> //= -> ->.
Qed.

Lemma Re0 : Re 0 = 0 :> R.  
Proof. by []. Qed.  

Lemma Im0 : Im 0 = 0 :> R.
Proof. by []. Qed.

Lemma ReIm_eq0 (x : C) : (x = 0) = ((Re x = 0) /\ (Im x = 0)).
Proof. by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex. Qed.

Lemma scalei_muli (z : C) : 'i * z = 'i *: z.
Proof. by []. Qed.

Lemma iE : 'i%C = 'i :> C.
Proof. by []. Qed.

Lemma scalecM : forall (w  v : C), (v *: w = v * w).
Proof. by []. Qed.

Lemma normc0 : normc 0 = 0 :> R  .
Proof. by rewrite /normc //= expr0n //= add0r sqrtr0. Qed.

Lemma normcN (x : C) : normc (- x) = normc x.
Proof. by case: x => a b /=; rewrite 2!sqrrN. Qed.

Lemma normcr (x : R) : normc (x%:C) = normr x.
Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.

Lemma normcR (x : C) : (normc x)%:C = normr x.
Proof. by rewrite /normr /=. Qed.

Lemma normc_i (x : R) : normc (x*i) = normr x.
Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

Lemma normc1 : normc (1 ) = 1 :> R.
Proof. by rewrite /normc/= expr0n addr0 expr1n sqrtr1. Qed.

Lemma normcN1 : normc (-1%:C) = 1 :> R.
Proof. by rewrite /normc/=  oppr0 expr0n addr0 -signr_odd expr0 sqrtr1. Qed.


Lemma realCD (x y : R) : (x + y)%:C = x%:C + y%:C.
Proof.
(*realC_additive*)
rewrite -!complexr0 eqE_complex //=; by split; last by rewrite addr0.
Qed.

Lemma realCB (x y : R) : (x - y)%:C = x%:C - y%:C.
Proof.
by rewrite -!complexr0 eqE_complex //=; split; rewrite ?subr0.
Qed.

Lemma Inv_realC (x : R) : x%:C^-1 = (x^-1)%:C.
Proof.
have [/eqP->|x0] := boolP (x == 0); first by rewrite !invr0.
apply/eqP; rewrite eq_complex /= mul0r oppr0 eqxx andbT expr0n addr0.
by rewrite expr2 invrM ?unitfE // mulrA divrr ?unitfE // div1r.
Qed.

Lemma CimV : ('i%C)^-1 = (-1 *i) :> C.
Proof. by rewrite complexiE invCi. Qed.

Lemma invcM (x y : C) : (x * y)^-1 = x^-1 * y^-1.
Proof.
have [/eqP->|x0] := boolP (x == 0); first by rewrite !(invr0,mul0r).
have [/eqP->|y0] := boolP (y == 0); first by rewrite !(invr0,mulr0).
by rewrite invrM // mulrC.
Qed.

Lemma Im_mul (x : R) : x *i = x%:C * 'i%C.
Proof. by simpc. Qed.

Lemma normcD (x y : C) : normc (x + y) <= normc x + normc y.
Proof. by rewrite -lecR realCD; apply: lec_normD. Qed.

Lemma normc_ge0 (x : C) : 0 <= normc x.
Proof. case: x => ? ?; exact: sqrtr_ge0. Qed.

Lemma normc_gt0 (v : C) : (0 < normc v) = (v != 0).
Proof.
rewrite lt_neqAle normc_ge0 andbT; apply/idP/idP; apply/contra.
by move/eqP ->; rewrite normc0.
by rewrite eq_sym => /eqP/eq0_normc ->.
Qed.

Lemma mulrnc (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma realCM (a b :R) : a%:C * b%:C = (a * b)%:C.
Proof. by rewrite eqE_complex /= !mulr0 mul0r addr0 subr0. Qed.

Lemma complexA: forall (h : C), h%:A = h.
Proof. by move => h; rewrite scalecM mulr1. Qed.

Lemma lecM (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma normc_natmul (k : nat) : normc k%:R = k%:R :> R.
Proof.
by rewrite mulrnc /= mul0rn expr0n addr0 sqrtr_sqr ger0_norm // ler0n.
Qed.

Lemma normc_mulrn (x : C) k : normc (x *+ k) = (normc x) *+ k.
Proof.
by rewrite -mulr_natr normcM -[in RHS]mulr_natr normc_natmul.
Qed.

Lemma gt0_normc (r : C) : 0 < r -> r = (normc r)%:C.
Proof.
move=> r0; have rr : r \is Num.real by rewrite realE (ltW r0).
rewrite /normc (complexE r) /=; simpc.
rewrite (ger0_Im (ltW r0)) expr0n addr0 sqrtr_sqr gtr0_norm ?complexr0 //.
by move: r0; rewrite {1}(complexE r) /=; simpc => /andP[/eqP].
Qed.

Lemma gt0_realC (r : C) : 0 < r -> r = (Re r)%:C.
Proof.
by move=> r0; rewrite eqE_complex /=; split; last by apply: ger0_Im; apply: ltW.
Qed.

Lemma ltc0E  (k : R): (0 < k%:C) = (0 < k).
Proof.  by simpc. Qed.

Lemma ltc0P  (k : R): (0 < k%:C) <-> (0 < k).
Proof.  by simpc. Qed.

Lemma ltcP  (k t: R): (t%:C < k%:C) <-> (t < k).
Proof. by simpc. Qed.

Lemma lecP  (k t: R): (t%:C <= k%:C) <-> (t <= k).
Proof. by simpc. Qed.

Lemma complex_pos (r : {posnum C}) :  0 < (Re r%:num).
Proof.  by rewrite -ltc0E -gt0_realC. Qed.

(* (*TBA algC *) *)
Lemma realC_gt0 (d : C) :  0 < d -> (0 < Re d :> R).
Proof. by rewrite ltcE => /andP [] //. Qed.

Lemma Creal_gtE (c d : C) :  c < d -> (complex.Re c < complex.Re d).
Proof. rewrite ltcE => /andP [] //. Qed.

Canonical complex_Re_posnum (x : {posnum C}) := PosNum (complex_pos x).

Lemma realC_pos_gt0 (r : {posnum R}) :  0 < (r%:num)%:C.
Proof. by rewrite ltcR. Qed.

Canonical realC_posnum (x : {posnum R}) := PosNum (realC_pos_gt0 x).

Lemma realC_norm (b : R) : `|b%:C| = `|b|%:C.
Proof. by rewrite normc_def /= expr0n addr0 sqrtr_sqr. Qed.

Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (r s : R) : (r *i == s *i) = (r == s).
Proof. by apply/idP/idP => [/eqP[] ->//|/eqP ->]. Qed.

Lemma neqCr0 (r : R) : (r%:C != 0) = (r != 0).
Proof. by apply/negP/negP; rewrite ?eqCr. Qed.


Lemma realCV (*name ?*) (h: R) : h != 0 -> (h^-1)%:C = h%:C^-1.
Proof.
rewrite eqE_complex //=; split; last by rewrite mul0r oppr0.
by rewrite expr0n //= addr0 -exprVn expr2 mulrA mulrV ?unitfE ?mul1r //=.
Qed.


Lemma real_normc_ler (x y : R) :
  `|x| <= normc (x +i* y).
Proof.
rewrite /normc /= -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=; last by apply: num_real.
by rewrite ler_addl ?sqr_ge0.
Qed.

Lemma im_normc_ler (x y : R) :
  `|y| <= normc (x +i* y).
Proof.
rewrite /normc /= -ler_sqr ?nnegrE ?normr_ge0 ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 ?real_normK //=; last by apply: num_real.
by rewrite ler_addr ?sqr_ge0.
Qed.

End complex_extras.

Section Rcomplex.


Canonical Rcomplex_lmodType (R : rcfType) :=
  LmodType R (Rcomplex R) (complex_real_lmodMixin R).

Lemma scalecAl (R : rcfType) (h : R) (x y : Rcomplex R) : h *: (x * y) = h *: x * y.
Proof.
by move: h x y => h [a b] [c d]; simpc; rewrite -!mulrA -mulrBr -mulrDr.
Qed.


Canonical Rcomplex_lalgType (R : rcfType) := LalgType R (Rcomplex R) (@scalecAl R).

Definition Rcomplex_normedZmodMixin (R: realType) :=
  @Num.NormedMixin R (Rcomplex_zmodType R) _ _ (@normcD R) (@eq0_normc R)
                   (@normc_mulrn R) (@normcN R).

Canonical Rcomplex_normedZmodType (R: realType) :=
  NormedZmodType R (Rcomplex R) (Rcomplex_normedZmodMixin R).

Definition Rcomplex_pseudoMetricMixin (R: realType) :=
  (@pseudoMetric_of_normedDomain R (Rcomplex_normedZmodType R)).


Canonical Rcomplex_pointedType (R: realType) :=
  [pointedType of (Rcomplex R) for [pointedType of R[i]^o]].

Canonical Rcomplex_filteredType (R: realType) :=
  [filteredType (Rcomplex R) of (Rcomplex R) for [filteredType R[i]^o of R[i]^o]].

Canonical Rcomplex_topologicalType (R: realType) :=
  [topologicalType of (Rcomplex R) for [topologicalType of R[i]^o]].

Program Definition Rcomplex_uniformMixin (R: realType):
  Uniform.mixin_of (nbhs (U := Rcomplex R) ) :=
  (@UniformMixin (Rcomplex R) (nbhs (U := Rcomplex R))
  (entourage_ ((ball_ (@normc R))))  _ _ _ _ _).
Obligation 1.  Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5.
move => R; rewrite /nbhs /= /nbhs_ /nbhs_ball_ /filter_from /entourage_ /= /filter_from /=.
apply/funext => x //=.
apply/funext => P /=; rewrite propeqE; split.
 move => [r /[dup] /realC_gt0 r0 /gt0_realC rr] H.
 rewrite /entourage_ /filter_from /=.
 exists (fun xy => (normc ( xy.1 - xy.2) < Re r)).
 exists (Re r) => //.
 by move=> z /= h; apply: (H z);  rewrite /= rr ltcR.
move => [B [] r r0] H /= H'; exists r%:C; first by rewrite ltcR.
move => z h; apply: H' => /=; apply: H => /=.
by rewrite -ltcR /=.
Qed.

Canonical Rcomplex_uniformType (R: realType) :=
  UniformType (Rcomplex R) (Rcomplex_uniformMixin R).

Canonical Rcomplex_pseudoMetricType (R: realType) :=
  PseudoMetricType (Rcomplex R) (Rcomplex_pseudoMetricMixin R).


Lemma Rcomplex_ball_ball_ (R: realType):
  @ball _ (Rcomplex_pseudoMetricType R ) = ball_ (fun x => `| x |).
Proof. by []. Qed.

Definition Rcomplex_pseudoMetricNormedZmodMixin (R: realType):=
  PseudoMetricNormedZmodule.Mixin (Rcomplex_ball_ball_ (R: realType)).

Canonical Rcomplex_pseudoMetricNormedZmodType (R: realType) :=
  PseudoMetricNormedZmodType R (Rcomplex R)
                       (Rcomplex_pseudoMetricNormedZmodMixin R).

Lemma RnormcZ  (R: realType) (l : R) : forall (x : Rcomplex R),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Definition Rcomplex_normedModMixin (R: realType):=
  @NormedModMixin R (Rcomplex_pseudoMetricNormedZmodType R)  _ (@RnormcZ R).

Canonical Rcomplex_normedModType (R: realType):=
  NormedModType R (Rcomplex R) (Rcomplex_normedModMixin R).

End Rcomplex.


Lemma filter_compE ( T U V : topologicalType)
      (f : T -> U) (g : V -> T)
      (F : set ( set V)) :
   (f @ (g @ F))= (f \o g @ F).
Proof. by []. Qed. 
    
Lemma within_continuous_withinNx
  (R C : numFieldType) (U : normedModType C) (f : U -> R) :
  {for (0 : U), continuous f} ->
  (forall x,  f x = 0 -> x = 0) -> f @ nbhs' (0 :U) --> nbhs'  (0 : R).
Proof.
  move => cf f0 A /=. 
  rewrite !/nbhs /= /nbhs /= /nbhs' /within /= !nearE =>  [].   Admitted.

Notation  "f %:Rfun" :=
  (f : (Rcomplex_normedModType _) -> (Rcomplex_normedModType _))
  (at level 5,  format "f %:Rfun")  : complex_scope.

Notation  "v %:Rc" :=   (v : (Rcomplex _))
                          (at level 5, format "v %:Rc")  : complex_scope.

Section algebraic_lemmas.
Variable (R: realType).
Notation C := R[i].
Notation Rcomplex := (Rcomplex R).

Lemma normcZ (l : R) : forall (x : Rcomplex),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma realCZ (a : R) : forall (b : Rcomplex),  a%:C * b = a *: b.
Proof. by move => [x y]; rewrite /(_ *: _) /=; simpc. Qed.

Lemma realC_alg (a : R) :  a *: (1%:Rc) = a%:C.
Proof.
apply/eqP; rewrite eq_complex; apply/andP.
by split; simpl; apply/eqP; rewrite ?mulr1 ?mulr0.
Qed.

Lemma scalecr: forall w: C, forall r : R, r *: (w: Rcomplex) = r%:C *: w .
Proof.
Proof. by move=> [a b] r; rewrite eqE_complex //=; split; simpc. Qed.

Lemma scalecV (h: R) (v: Rcomplex):
  h != 0 -> v != 0 -> (h *: v)^-1 = h^-1 *: v^-1. (* scaleCV *)
Proof.
by move=> h0 v0; rewrite scalecr invrM // ?unitfE ?eqCr // mulrC scalecr realCV.
Qed.

Lemma complex0 : 0%:C = 0 :> C.
Proof. rewrite eqE_complex //=. Qed.


End algebraic_lemmas.


(* Section complex_topological.
Variable R : realType.
Local Notation C := R[i].

Canonical complex_pointedType :=
  [pointedType of C for pointed_of_zmodule [zmodType of C]].
Canonical complex_filteredType :=
  [filteredType C of C for filtered_of_normedZmod  [normedZmodType C of C]].
Canonical complex_topologicalType  :=
  TopologicalType C
  (topologyOfEntourageMixin
    (uniformityOfBallMixin
      (@nbhs_ball_normE _ [normedZmodType C of C])
      (pseudoMetric_of_normedDomain [normedZmodType C of C]))).
Canonical numFieldType_uniformType := UniformType C
  (uniformityOfBallMixin (@nbhs_ball_normE _ [normedZmodType C of C])
    (pseudoMetric_of_normedDomain [normedZmodType C of C])).
Canonical numFieldType_pseudoMetricTyp
  := @PseudoMetric.Pack [numDomainType of C] C (@PseudoMetric.Class [numDomainType of C] C
       (Uniform.class [uniformType of C])
   (@pseudoMetric_of_normedDomain [numDomainType of C] [normedZmodType C of C])).

Canonical complex_lmodType  :=
  [lmodType R[i] of R[i] for [lmodType R[i] of R[i]^o]].

Canonical complex_lalgType := [lalgType C of C for [lalgType C of C^o]].
Canonical complex_algType := [algType C of C for [algType C of C^o]].
Canonical complex_comAlgType := [comAlgType C of C].
Canonical complex_unitAlgType := [unitAlgType C of C].
Canonical complex_comUnitAlgType := [comUnitAlgType C of C].
Canonical complex_vectType := [vectType C of C for [vectType C of C^o]].
Canonical complex_FalgType := [FalgType C of C].
Canonical complex_fieldExtType :=
  [fieldExtType C of C for [fieldExtType C of C^o]].

Canonical complex_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType C of C for
  [pseudoMetricNormedZmodType C of [numFieldType of C^o]]].
Canonical complex_normedModType :=
  [normedModType C of C for [normedModType C of C^o]].

End complex_topological. *)

Section Holomorphe_der.
Variable R : realType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Notation Rc := (Rcomplex R).

Lemma is_cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
 (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
 cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. by move => /cvg_ex [l H0] ; apply: cvgP; apply: cvgZr; apply: H0. Qed.

Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
  (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
  cvg(f @ F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof. by move => cv; apply/esym/cvg_lim => //; apply: cvgZr. Qed.

Definition holomorphic (f : C-> C ) (c : C) :=
  cvg ((fun h => h^-1 *: (f (c + h) - f c)) @ (nbhs' (0:C))).

Lemma holomorphicP (f : C -> C)  (c: C) : holomorphic f c <-> derivable f c 1.
Proof.
rewrite /holomorphic /derivable.
suff -> : (fun h : C => h^-1 *: ((f(c + h) - f c))) =
         ((fun h : C => h^-1 *: ((f \o shift c) (h *: 1) - f c))) by [].
 by apply: funext =>h; rewrite complexA [X in f X]addrC.
Qed.

Definition Rdifferentiable (f : C -> C) (c : C) := (differentiable f%:Rfun c%:Rc).

(* No Rmodule structure on C if we can avoid,
so the following line shouldn't type check. *)
Fail Definition Rderivable_fromcomplex_false (f : C -> C) (c v: C) :=
  cvg (fun (h : R) =>  h^-1 *: (f (c +h *: v) - f c)) @ (nbhs' (0:R)).

Definition realC : R -> C := (fun r => r%:C).

Lemma continuous_realC: continuous realC.
Proof.
move => x A /= [] r /[dup] /realC_gt0 Rer0 /gt0_realC rRe H; exists (Re r); first by [].
by move => z /= nz; apply: (H (realC z)); rewrite /= -realCB realC_norm rRe ltcR.
Qed. 

Lemma Rdiff1 (f : C -> C) c :
          lim ( (fun h : C =>  h^-1 *: ((f (c + h) - f c) ) )
                 @ (realC @  (nbhs' 0)))
         = 'D_1 (f%:Rfun) c%:Rc :> C.
Proof.
rewrite /derive.
have -> : (fun h : C =>  h^-1 *: ((f (c + h) - f c))) @ (realC @  (nbhs' 0)) =
         (fun h : C =>  h^-1 *: ((f (c + h) - f c)))
                 \o realC @  (nbhs' (0 : R)) by [].
suff -> : ( (fun h : C => h^-1 *: (f (c + h) - f c)) \o realC)
= (fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: (1%:Rc)) - f c) ) :> (R -> C) .
   by []. (*TODO : very long*)
apply: funext => h /=.
by  rewrite Inv_realC /= -!scalecr realC_alg [X in f X]addrC.
Qed.


Lemma Rdiffi (f : C -> C) c:
         lim ( (fun h : C => h^-1 *: ((f (c + h * 'i) - f c)))
                 @ (realC @ (nbhs' (0 ))))
         = 'D_('i) (f%:Rfun)  c%:Rc :> C.
Proof.
rewrite /derive.
have -> :
  ((fun h : (R[i]) => h^-1 *: (f (c + h * 'i) - f c)) @ (realC @ nbhs' 0))
  = ((fun h : (R[i]) => h^-1 *: (f (c + h * 'i) - f c)) \o realC) @ nbhs' 0 by [].
suff -> :  (fun h : (R[i]) => h^-1 * (f (c + h * 'i) - f c)) \o
realC  = fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: ('i%:Rc)) - f c).
  by [].
apply: funext => h /=.
by rewrite Inv_realC -scalecM -!scalecr realCZ [X in f X]addrC.
Qed.

(* should be generalized to equivalent norms *)
(* but there is no way to state it for now *)
Lemma littleoCo (E : normedModType C) (h e : E -> C) (x : E) :
   [o_x (e : E -> C) of (h : E -> C)] =
   [o_x (e : E -> Rc) of (h : E -> Rc)].
Proof.
suff heP : (h : E -> C) =o_x (e : E -> C) <->
           (h : E -> Rc) =o_x (e : E -> Rc).
  have [ho|hNo] := asboolP ((h : E -> C) =o_x (e : E -> C)).
    by rewrite !littleoE// -!eqoP// -heP.
  by rewrite !littleoE0// -!eqoP// -heP.
rewrite !eqoP; split => small _/posnumP[eps]; near=> y.
  rewrite -lecR/= !normcR rmorphM/=.
  by near: y; apply: small.
rewrite -[_%:num]ger0_norm// -!normcR -rmorphM/= lecR.
by near: y; apply: small; rewrite normc_gt0//.
Grab Existential Variables. all: by end_near. Qed.

(*extremely long with modified filteredType *)

Definition CauchyRiemannEq (f : C -> C) c :=
  'i *'D_1 f%:Rfun c%:Rc =  'D_('i) f%:Rfun c%:Rc.

Lemma holo_differentiable (f : C -> C) (c : C) :
  holomorphic f c -> Rdifferentiable f c.
Proof.
move=> /holomorphicP /derivable1_diffP /diff_locallyP => -[cdiff holo].
have lDf : linear ('d f c : Rc -> Rc) by move=> t u v; rewrite !scalecr linearP.
pose df : Rc -> Rc := Linear lDf.
have cdf : continuous df by [].
have eqdf : f%:Rfun \o +%R^~ c = cst (f c) + df +o_ (0 : Rc) id
  by rewrite holo littleoCo.
by apply/diff_locallyP; rewrite (diff_unique cdf eqdf).
Qed.

(*The equality between 'i as imaginaryC from ssrnum and 'i is not transparent:
 neq0ci is part of ssrnum and uneasy to find *)

Lemma holo_CauchyRiemann (f : C -> C ) c: holomorphic f c -> CauchyRiemannEq f c.
Proof.
move=> /cvg_ex; rewrite //= /CauchyRiemannEq. rewrite -Rdiff1 -Rdiffi.
set quotC : C -> C := fun h : R[i] => h^-1 *: (f (c + h) - f c).
set quotR : C -> C:= fun h => h^-1 *: (f (c + h * 'i) - f c) .
move => /= [l H].
have -> :  quotR @ (realC @ nbhs' 0) =  (quotR \o realC) @ nbhs' 0 by [].
have realC'0:  realC @ nbhs' 0 --> nbhs' 0.
 apply: within_continuous_withinNx; first by apply: continuous_realC.
 by move => /= x /complexI.
have HR0:(quotC \o (realC) @ nbhs' 0)  --> l.
 by apply: cvg_comp; last by exact: H.
have lem : quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 : R))) --> l.
  apply: cvg_comp; last by exact: H.
  rewrite (filter_compE _ realC); apply: cvg_comp; first by exact: realC'0.
  apply: within_continuous_withinNx; first by apply: scalel_continuous.
  move => x /eqP; rewrite mulIr_eq0 ; last by apply/rregP; apply: neq0Ci.
  by move/eqP.
have HRcomp:  cvg (quotC \o *%R^~ 'i%R @ (realC @ (nbhs' (0 : R)))) .
  by apply/cvg_ex;  simpl; exists l.
have ->: lim (quotR @ (realC @ (nbhs' (0 : R))))
  = 'i *: lim (quotC \o ( fun h => h *'i) @ (realC @ (nbhs' (0 : R)))).
  have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR.
  move => h /= ;rewrite /quotC /quotR /=.
  rewrite invcM scalerA mulrC -mulrA mulVf ?mulr1 ?neq0Ci //.
  by move => /funext <-; rewrite (limin_scaler _ 'i HRcomp).
rewrite scalecM.
suff: lim (quotC @ (realC @ (nbhs' (0 : R))))
      = lim (quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 : R)))) by move => -> .
suff -> : lim (quotC @ (realC @ (nbhs' (0 : R)))) = l.
  by apply/eqP; rewrite eq_sym; apply/eqP; apply: (cvg_map_lim _ lem).
by apply: cvg_map_lim.
Qed.


(*TBA normedType- Cyril's suggestion *)
Lemma nbhs'0_le  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| <= e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
rewrite -ball_normE /= sub0r normrN => le_nxe _ .
by rewrite ltW.
Qed.

Lemma nbhs0_le  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| <= e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
rewrite -ball_normE /= sub0r normrN => le_nxe _ .
by rewrite ltW.
Qed.

Lemma nbhs'0_lt  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma nbhs0_lt  (K : numFieldType) (V : normedModType K) e :
   0 < e -> \forall x \near (nbhs' (0 : V)), `|x| < e.
Proof.
move=> e_gt0; apply/nbhs_ballP; exists e => // x.
by rewrite -ball_normE /= sub0r normrN.
Qed.

Lemma normc_ge_Im (x : R[i]) : `|complex.Im x|%:C <= `|x|.
Proof.
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // ler_addr sqr_ge0.
Qed.



Lemma Diff_CR_holo (f : C -> C)  (c: C):
   (Rdifferentiable f c) /\
  (CauchyRiemannEq f c)
  -> (holomorphic f c).
Proof.
move => [] /= /[dup] H /diff_locallyP  => [[derc diff]] CR.
apply/holomorphicP/derivable1_diffP/diff_locallyP.
pose Df := (fun h : C => h *: ('D_1 f%:Rfun c : C)).
have lDf : linear Df by move =>  t u v /=; rewrite /Df scalerDl scalerA scalecM.
pose df := Linear lDf.
have cdf : continuous df by apply: scalel_continuous.
have lem : Df = 'd (f%:Rfun) (c : Rc). (* issue with notation *)
  apply: funext => z; rewrite  /Df.
  set x := Re z; set y := Im z.
  have zeq : z = x *: 1 %:Rc + y *: 'i%:Rc.
  by rewrite [LHS]complexE /= realC_alg scalecr scalecM [in RHS]mulrC.
  rewrite [X in 'd _ _ X]zeq addrC linearP linearZ /= -!deriveE //.
  rewrite -CR (scalecAl y) -scalecM !scalecr /=.
  rewrite -(scalerDl  (('D_1 f%:Rfun (c : Rc)) : C) _  (real_complex R x)).
  by rewrite addrC -!scalecr -realC_alg -zeq.
have holo:  f \o  shift c = cst (f c) + df +o_ ( 0 : C) id.
  by rewrite diff /= lem -littleoCo.
by rewrite (diff_unique cdf holo).
Qed.

Lemma holomorphic_Rdiff (f : C -> C) (c : C) :
  (Rdifferentiable f c) /\ (CauchyRiemannEq f c) <-> (holomorphic f c).
Proof.
  split => H; first by apply: Diff_CR_holo.
  split; first by apply: holo_differentiable.
  by apply: holo_CauchyRiemann.
Qed.

End Holomorphe_der.
