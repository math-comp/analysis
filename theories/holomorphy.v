
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(*Require Import ssrsearch.*)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import complex.
From mathcomp Require Import boolp reals ereal derive.
Require Import classical_sets posnum topology normedtype landau.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def complex.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I need to import ComplexField to use its lemmas on RComplex,
I don't want the canonical lmodtype structure on C,
Therefore this is based on a fork of real-closed *)

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

Lemma scalei_muli (z : C^o) : 'i * z = 'i *: z.
Proof. by []. Qed.

Lemma iE : 'i%C = 'i :> C.
Proof. by []. Qed.

Lemma scalecM : forall (w  v : C^o), (v *: w = v * w).
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

Lemma complexA: forall (h : C^o), h%:A = h.
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

Lemma ltr0c  (k : R): (0 < k%:C) = (0 < k).
Proof.  by simpc. Qed.


Lemma complex_pos (r : {posnum C}) :  0 < (Re r%:num).
Proof.  by rewrite -ltr0c -gt0_realC. Qed.

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
Canonical Rcomplex_eqType (R : eqType) := [eqType of Rcomplex R].
Canonical Rcomplex_countType (R : countType) := [countType of Rcomplex R].
Canonical Rcomplex_choiceType (R : choiceType) := [choiceType of Rcomplex R].
Canonical Rcomplex_zmodType (R : rcfType) := [zmodType of Rcomplex R].
Canonical Rcomplex_ringType (R : rcfType) := [ringType of Rcomplex R].
Canonical Rcomplex_comRingType (R : rcfType) := [comRingType of Rcomplex R].
Canonical Rcomplex_unitRingType (R : rcfType) := [unitRingType of Rcomplex R].
Canonical Rcomplex_comUnitRingType (R : rcfType) := [comUnitRingType of Rcomplex R].
Canonical Rcomplex_idomainType (R : rcfType) := [idomainType of Rcomplex R].
Canonical Rcomplex_fieldType (R : rcfType) := [fieldType of Rcomplex R].
Canonical Rcomplex_lmodType (R : rcfType) :=
  LmodType R (Rcomplex R) (complex_lmodMixin R).


Lemma scalecAl (R : rcfType) (h : R) (x y : Rcomplex R) : h *: (x * y) = h *: x * y.
Proof.
by move: h x y => h [a b] [c d]; simpc; rewrite -!mulrA -mulrBr -mulrDr.
Qed.


Canonical C_RLalg  (R : rcfType):= LalgType R (Rcomplex R) (@scalecAl R).

(* Variable (R : rcfType) (x : (Rcomplex R)). Check (x%:A). *)

(*Variable (R: realFieldType).
Fail Check [FalgType R of (R[i])].*)
(* Constructing a FieldExt R structure on R[i] necessitates a Falgstructure,
and thus a finite dimensional vector space structure *)

Canonical Rcomplex_pointedType  (R: realType) := PointedType (Rcomplex R) 0.
Canonical Rcomplex_filteredType (R: realType) :=
  FilteredType (Rcomplex R) (Rcomplex R) (nbhs_ball_ (ball_ (@normc R))).

Definition Rcomplex_normedZmodMixin (R: realType) :=
  @Num.NormedMixin R (Rcomplex_zmodType R) _ _ (@normcD R) (@eq0_normc R)
                   (@normc_mulrn R) (@normcN R).

Canonical Rcomplex_normedZmodType (R: realType) :=
  NormedZmodType R (Rcomplex R) (Rcomplex_normedZmodMixin R).

Definition Rcomplex_pseudoMetricMixin (R: realType) :=
  (@pseudoMetric_of_normedDomain R (Rcomplex_normedZmodType R)).

Definition Rcomplex_topologicalMixin (R: realType):=
  topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE R (Rcomplex_normedZmodType R) )
      (Rcomplex_pseudoMetricMixin R)).

Canonical Rcomplex_topologicalType (R: realType) :=
  TopologicalType (Rcomplex R) (Rcomplex_topologicalMixin R).

Definition Rcomplex_uniformMixin (R: realType):=
  uniformityOfBallMixin (@nbhs_ball_normE R (Rcomplex_normedZmodType R) )
                        (Rcomplex_pseudoMetricMixin R).

Canonical Rcomplex_uniformType (R: realType) :=
  UniformType (Rcomplex R) (Rcomplex_uniformMixin R).

Canonical Rcomplex_pseudoMetricType (R: realType) :=
  PseudoMetricType (Rcomplex_normedZmodType R) (Rcomplex_pseudoMetricMixin R).


Lemma Rcomplex_ball_ball_ (R: realType):
  @ball _ (Rcomplex_pseudoMetricType R ) = ball_ (fun x => `| x |).
Proof. by []. Qed.

Definition Rcomplex_pseudoMetricNormedZmodMixin (R: realType):=
  PseudoMetricNormedZmodule.Mixin (Rcomplex_ball_ball_ (R: realType)).

Canonical Rcomplex_pseudoMetricNormedZmodType (R: realType) :=
  PseudoMetricNormedZmodType R (Rcomplex_normedZmodType R)
                       (Rcomplex_pseudoMetricNormedZmodMixin R).

Lemma RnormcZ  (R: realType) (l : R) : forall (x : Rcomplex R),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Definition Rcomplex_normedModMixin (R: realType):=
  @NormedModMixin R (Rcomplex_pseudoMetricNormedZmodType R)  _ (@RnormcZ R).

Canonical Rcomplex_normedModType (R: realType):=
  NormedModType R _ (Rcomplex_normedModMixin R).

End Rcomplex.



Notation  "f %:Rfun" :=
  (f : (Rcomplex_normedModType _) -> (Rcomplex_normedModType _))
  (at level 5,  format "f %:Rfun")  : complex_scope.

Notation  "v %:Rc" :=   (v : (Rcomplex _))
                          (at level 5, format "v %:Rc")  : complex_scope.


Section complex_numfield_topological.
Variable (R: realType).
Notation C := R[i].


Canonical complex_lmodType (R: realType) :=
  [lmodType R[i] of R[i] for [lmodType R[i] of R[i]^o]].
(* why ?? *)
Variable (c : C). Check (c *: (c : complex_lmodType R)).

Canonical complex_lalgType := [lalgType C of C for [lalgType C of C^o]].
Canonical complex_algType := [algType C of C for [algType C of C^o]].
Canonical complex_comAlgType := [comAlgType C of C].
Canonical complex_unitAlgType := [unitAlgType C of C].
Canonical complex_comUnitAlgType := [comUnitAlgType C of C].
Canonical complex_vectType := [vectType C of C for [vectType C of C^o]].
Canonical complex_FalgType := [FalgType C of C].
Canonical complex_fieldExtType :=
  [fieldExtType C of C for [fieldExtType C of C^o]].


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


Canonical complex_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType C of C for
  [pseudoMetricNormedZmodType C of [numFieldType of C]]].
Canonical complex_normedModType :=
  [normedModType C of C for [normedModType C of C^o]].


End complex_numfield_topological.


Section algebraic_lemmas.
Variable (R: realType). 
Notation C := R[i].
Notation Rcomplex := (Rcomplex R).

(* TODO: find better names and clear the redudancies between lemmas *)

Lemma normcZ (l : R) : forall (x : Rcomplex),
    normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma realCZ (a : R) : forall (b : Rcomplex),  a%:C * b = a *: b.
Proof. move => [x y]; rewrite /(real_complex R) /scalec.
Admitted.

Lemma realC_alg (a : R) :  a *: (1%:Rc) = a%:C.
Proof.
apply/eqP; rewrite eq_complex; apply/andP.
by split; simpl; apply/eqP; rewrite ?mulr1 ?mulr0.
Qed.

Lemma scalecr: forall w: C^o, forall r : R, r *: (w: Rcomplex) = r%:C *: w . (*TODO *)
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

Section topological_lemmas.
Variable R : realType.
(* Local Notation sqrtr := Num.sqrt. *)
Notation C := R[i].
Notation Rc := (Rcomplex R).

(*a few lemmas showing by hand the equivalence of topology *)
Lemma complex_limP (F : set (set C))  (l : C):
  (F --> (l: C)) <-> (F --> l%:Rc).
Proof.
split; move => /= H A /=.
  move/(nbhs_ex (x:=l : Rcomplex_normedModType R)) =>  [[r r0] /=].
  rewrite -ball_normE /= => Br.
  have : nbhs (l: C^o) A.
    exists r%:C; first by rewrite /= ltcR.
    by move => y /=; rewrite /= ltcR; apply: Br.
  by move/(H A).
move/(nbhs_ex (x:=l : C^o))=>  [[[r ri] r0] /=].
move: r0; rewrite ltcE /= => /andP [/eqP ri0 r0] //.
rewrite /ball /= ri0 complexr0 /= => Br.
have : nbhs l%:Rc A.
  by exists r; last by move => y /=; rewrite -ltcR; apply: Br.
by move/(H A).
Qed.

Lemma complex_cvgP (F : set (set C)) (FF: Filter F) :
  [cvg F in [topologicalType of Rc]] <->
   [cvg F in [topologicalType of C]].
Proof.
split; move/cvg_ex => /= [l H].
apply: (cvgP (l : C^o)).
  by apply/complex_limP.
by apply: (cvgP (l%:Rc)); apply/complex_limP.
Qed.


Lemma complex_liminP (F : set (set C)) (FF: ProperFilter F):
   [lim F in [topologicalType of Rc]] =
   [lim F in [topologicalType of C]].
Proof.
case: (EM ([cvg F in [topologicalType of C]])).
  move/cvg_ex=> /= [l Fl].
  rewrite (norm_cvg_lim (l := l)) //.
  by apply: (@norm_cvg_lim _ (Rcomplex_normedModType R)); apply/complex_limP.
move => dvg; pose copy := dvg ;move/dvgP: copy => ->.
by move/complex_cvgP/dvgP: dvg => ->.
Qed.
End topological_lemmas.


(*TBA topology.v for readibility *) 
Lemma cvg_compE ( T U V : topologicalType)
      (f : T -> U) (g : V -> T)
      (F : set ( set V)) :
  cvg (f @ (g @ F)) <-> cvg (f \o g @ F).
Proof.
  by [].
Qed.

Lemma lim_compE ( T U V : topologicalType)
      (f : T -> U) (g : V -> T)
      (F : set ( set V)) :
  lim (f @ (g @ F)) = lim (f \o g @ F).
Proof.
  by [].
Qed.

Section Holomorphe_der.
Variable R : realType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Notation Rc := (Rcomplex R).
(* Local Notation Re := (@complex.Re R). *)
(* Local Notation Im := (@complex.Im R). *)

(*TODO : introduce Rcomplex at top, and use notation Rdifferentiable everywhere *)
(* TODO: default notations are _*_ on C and _*: on Rcomplex*)

Lemma is_cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
 (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
 cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. by move => /cvg_ex [l H0] ; apply: cvgP; apply: cvgZr; apply: H0. Qed.

Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
  (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
  cvg(f @ F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof. by move => cv; apply/esym/cvg_lim => //; apply: cvgZr. Qed.

Definition holomorphic (f : C -> C^o) (c : C) :=
  cvg ((fun h => h^-1 *: (f (c + h) - f c)) @ (nbhs' 0)). (* TODO *)

Lemma holomorphicP (f : C -> C^o)  (c: C) : holomorphic f c <-> derivable f c 1.
Proof.
rewrite /holomorphic /derivable.
suff -> : (fun h : C => h^-1 *: ((f(c + h) - f c))) =
                    ((fun h : C => h^-1 *: ((f \o shift c) (h *: 1) - f c))) by [].              
by apply: funext =>h; rewrite complexA [X in f X]addrC.
Qed.




Definition Rdifferentiable (f : C -> C) (c : C) := (differentiable f%:Rfun c%:Rc).
 

(* No Rmodule structure on C if we can avoid,
so the following line shouldn't type check. *)
Fail Definition Rderivable_fromcomplex_false (f : C -> C^o) (c v: C) :=
  cvg (fun (h : R^o) =>  h^-1 *: (f (c +h *: v) - f c)) @ (nbhs' 0).

Definition realC : R -> C := (fun r => r%:C ).


Lemma Rdiff1 (f : C -> C^o) c:
          lim ( (fun h : C => h^-1 *: ((f (c +  h) - f c)))
                 @ (realC@ (nbhs' (0:R^o))))
         = 'D_1 (f%:Rfun) c%:Rc.
Proof.
rewrite /derive lim_compE.
suff -> :  (fun h  => h^-1 * (f (c +  h) - f c)) \o
realC = fun h : R => h^-1 *: ((f%:Rfun \o shift c) (h *: (1%:Rc)) - f c).
  by rewrite complex_liminP /=.
apply: funext => h /=.
by rewrite Inv_realC -scalecM -!scalecr realC_alg [X in f X]addrC.
Qed.


Lemma Rdiffi (f : C^o -> C^o) c:
         lim ( (fun h => h^-1 *: ((f (c + h * 'i) - f c)))
                 @ (realC @ (nbhs' 0)))
         = 'D_('i) (f%:Rfun)  c%:Rc.
Proof.
rewrite /derive lim_compE.
suff -> :  (fun h => h^-1 * (f (c + h * 'i) - f c)) \o
realC  = fun (h :R) => h^-1 *: ((f%:Rfun \o shift c) (h *: ('i%:Rc)) - f c).
  by rewrite complex_liminP /=.
apply: funext => h /=.
by rewrite Inv_realC -scalecM -!scalecr realCZ [X in f X]addrC.
Qed. (* TODO : slow *)

(* todo : faire des réécritures par conversion dans le script de preuve *)


Definition CauchyRiemanEq (f : C -> C) c :=
  'i *'D_1 (f%:Rfun) c%:Rc =  'D_('i) (f%:Rfun)  c%:Rc.

Lemma holo_differentiable (f : C -> C) (c : C) :
  holomorphic f c -> Rdifferentiable f c.
Proof. 
move=> /holomorphicP /derivable1_diffP /diff_locallyP => [[diffc /= /eqaddoP holo]].
pose df := 'd f c. simpl in (type of df). 
Fail Check  (diff_unique (df := 'd f c : Rc -> Rc)).
apply/diff_locallyP; split. (* TODO : diff_unique *) Check ('d f c). 
  move => /= v; apply/complex_limP. admit.
apply/eqaddoP => eps eps0; rewrite nearE /=.
have lec_eps0 : 0 < eps%:C by simpc.
move:(holo eps%:C lec_eps0); rewrite /= nearE => [[r /= r0]] H.
exists (Re r); first by exact: realC_gt0.
move => v /=. rewrite sub0r normcN => nvr.
Admitted.

Lemma holo_derivable (f : C -> C^o) c : (* TODO *)
  holomorphic f c -> (forall v : C, derivable (f%:Rfun) c v).
Proof.
move=> /cvg_ex; rewrite /type_of_filter /=.
move => [l H] v /=; rewrite /derivable /=.
set quotR := (X in (X @ _)).
simpl in (type of quotR).
pose mulrv := fun h =>  h%:C * v.
pose quotC h : C := h^-1 *: (f (c + h) - f c).
case (v =P 0) =>  [eqv0|/eqP vneq0].
  have -> :  quotR = 0.
    apply: funext => h; rewrite  /quotR  /= eqv0.
    by rewrite scaler0 add0r /= subrr /= scaler0 //=.
  by apply: cvgP; apply: (cvg_cst).
apply: (cvgP ((v * l)%:Rc)).
have eqnear0: {near nbhs' 0, (v \*o quotC) \o mulrv =1 (quotR)}.
(* as we need to perform computation for h != 0, we cannot prove fun equality directly *)
  exists 1 => // h _ neq0h; rewrite /quotC /quotR /realC /mulrv //=.
  rewrite invrM ?unitfE //; last by rewrite neqCr0 ?unitfE.
  rewrite mulrA (mulrA v) mulrV ?unitfE // mul1r /=.
  by rewrite -!realCZ realCV // [X in f X]addrC. 
have subsetfilters : quotR @ nbhs' (0 : R^o) `=>` (v \*o quotC) \o mulrv @ nbhs' 0.
by apply: (near_eq_cvg eqnear0).
apply: cvg_trans subsetfilters _.
suff: v \*o quotC \o mulrv @ nbhs' 0 -->  (v * l : Rc) by move/cvg_trans; apply. 
apply: (cvg_comp (G := nbhs' (0 : C))); last first. 
 Check  (cvgMr H). admit.
rewrite /mulrv => //= A [r leq0r /= ballrA]; exists ( normc r / normc v ).
 by  rewrite /= mulr_gt0 // ?normc_gt0 ?gt_eqF //= ?invr_gt0 ?normc_gt0.
move=> b ; rewrite /ball_ /= sub0r normrN => ballrb neqb0.
have ballCrb : (@ball_ _ _ (fun x => `|x|) 0 r (mulrv b)).
  rewrite /ball_ /= sub0r normrN /mulrv normrM.
  rewrite ltr_pdivl_mulr in ballrb; last by rewrite normc_gt0.
  by rewrite -(ger0_norm (ltW leq0r)) realC_norm realCM ltcR.
  by apply: (ballrA (mulrv b) ballCrb); apply: mulf_neq0 ; rewrite ?eqCr.
Admitted.

(*The fact that the topological structure is only available on C^o
makes iterations of C^o apply *)

(*The equality between 'i as imaginaryC from ssrnum and 'i is not transparent:
 neq0ci is part of ssrnum and uneasy to find *)

Lemma holo_CauchyRieman (f : C -> C^o) c: holomorphic f c -> CauchyRiemanEq f c.
Proof. (* To be cleaned *)
move=> /cvg_ex; rewrite /type_of_filter //= /CauchyRiemanEq -Rdiff1 -Rdiffi.
set quotC : C -> C^o := fun h : R[i] => h^-1 *: (f (c + h) - f c). 
set quotR : C -> C^o:= fun h => h^-1 *: (f (c + h * 'i) - f c) .
move => [l H].
have -> :  quotR @ (realC @ nbhs' 0) =  (quotR \o (realC)) @ nbhs' 0 by [].
have HR0:(quotC \o (realC) @ nbhs' 0)  --> l.
  apply: cvg_comp; last by exact: H.
  move => A [[r ri]];  rewrite /= ltcE=> /andP /= [/eqP -> r0]; rewrite complexr0 => ball.
  exists r; first by [].
  move=> a /=; rewrite sub0r normrN => ar aneq0.
  apply: ball; last by rewrite eqCr.
  by simpl; rewrite sub0r normrN ltcR normcr.
have lem : quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 : R^o))) --> l.
  apply: cvg_comp; last by exact: H.
  move => A /= [ [r ri] ].
  rewrite /= ltcE=> /andP /= [/eqP -> r0]; rewrite complexr0 => ball.
  exists r; first by [].
  move => a /= ; rewrite sub0r normrN => ar aneq0; apply: ball.
    simpl; rewrite sub0r normrN normrM /=.
    have ->: `|'i| = 1 by move => T;  simpc; rewrite expr0n expr1n /= add0r sqrtr1.
    by rewrite mulr1 ltcR normcr.
  apply: mulf_neq0; last by rewrite neq0Ci.
  by rewrite eqCr.
have HRcomp:  cvg (quotC \o *%R^~ 'i%R @ (realC @ (nbhs' (0 :R)))) .
  by apply/cvg_ex;  simpl; exists l.
have ->: lim (quotR @ (realC @ (nbhs' (0:R))))
  = 'i *: lim (quotC \o ( fun h => h *'i) @ (realC @ (nbhs' (0 :R)))).
  have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR.
  move => h /= ;rewrite /quotC /quotR /=.
  rewrite invcM scalerA mulrC -mulrA mulVf.
    by rewrite mulr1.
    by rewrite neq0Ci.
by move => /funext <-; rewrite (limin_scaler _ 'i HRcomp).
rewrite scalecM.
suff: lim (quotC @ (realC @ (nbhs' (0: R))))
      = lim (quotC \o  *%R^~ 'i%R @ (realC @ (nbhs' (0 :R)))) by move => -> .
suff -> : lim (quotC @ (realC @ (nbhs' (0 : R)))) = l.
  by apply/eqP; rewrite eq_sym; apply/eqP; apply: (cvg_map_lim _ lem).
by apply: (cvg_map_lim).
Qed.

End Holomorphe_der.




Section CR_holo.
Variable R : realType.
(* Local Notation sqrtr := Num.sqrt. *)
Notation C := R[i].
Notation Rc := (Rcomplex R).

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



Lemma Diff_CR_holo (f : C^o -> C^o)  (c: C):
   (Rdifferentiable f c) /\
  (CauchyRiemanEq f c)
  -> (holomorphic f c).
Proof.
move => [] /= H; have derf := H ; move: H.
move/diff_locally /eqaddoP => der.
(* TODO : diff_locally to be renamed diff_nbhs *)
rewrite /CauchyRiemanEq => CR.
rewrite /holomorphic; apply: (cvgP (('D_1 f%:Rfun c) : C^o)).
apply/(cvg_distP (('D_1 f%:Rfun c) : C^o)).
move => eps eps_lt0 /=.
pose er := Re eps.
have eq_ereps := gt0_realC eps_lt0.
have er_lt0 : 0 < er/2 by rewrite mulr_gt0 // realC_gt0 //.
move /(_ (er/2) er_lt0): der; rewrite /= nearE.
move => /(@nbhs_ex _  _ (0 : Rcomplex_normedModType R)) [[d d0]] /= der.
rewrite nearE /= nbhs_filterE.
exists d%:C; first by rewrite /= ltcR.
move=> z /=; rewrite sub0r normrN => lt_nzd z0.
have ltr_nzd : (normc z) < d by rewrite -ltcR.
have -> : eps  =  `|z|^-1 * `|z| * eps.
  rewrite [X in X*_]mulrC mulfV; first by rewrite  ?mul1r.
  by apply/eqP => /normr0_eq0; move/eqP: z0.  (*ugly*)
rewrite -mulrA ltr_pdivl_mull ?normr_gt0 // -normrM mulrDr mulrN.
rewrite scalecM mulrA mulfV // mul1r.
move /(_ z): der; rewrite -ball_normE /= sub0r normrN => /(_ ltr_nzd).
rewrite -[`|(_)z|]/(`|_ z + _ z|) /=. (* TODO *)
set b := ((cst (f c)) : C -> Rc).
rewrite -[(- (b + _)) z]/(- ( f c + _ z))  /= mulrC opprD.
set x := Re z; set y := Im z.
have zeq : z = x *: 1 %:Rc + y *: 'i%:Rc.
  by rewrite [LHS]complexE /= realC_alg scalecr scalecM [in RHS]mulrC.
rewrite [X in 'd _ _ X]zeq addrC linearP linearZ /= -!deriveE //.
rewrite -CR (scalecAl y) (* why scalec *) -scalecM !scalecr.
rewrite -(scalerDl  (('D_1 f%:Rfun c%:Rc): C^o) x%:C). (*clean, do it in Rcomplex *)
rewrite addrAC -!scalecr -realC_alg -zeq. (*clean*)
rewrite addrC  [X in (-_ + X)]addrC [X in f X]addrC -[X in `|_ + X|]opprK -opprD.
rewrite normrN scalecM -lecR => H.
rewrite /normr /=; apply: le_lt_trans; first by exact H.
rewrite eq_ereps realCM ltcR /normr /= ltr_pmul2l ?normc_gt0 //.
rewrite /er -[X in (_ < X)]mulr1 ltr_pmul2l //= ?invf_lt1 ?ltr1n //.
rewrite -ltr0c -eq_ereps //.
Qed.



Lemma holomorphic_Rdfiff (f : C -> C^o) (c : C) :
  (Rdifferentiable f c) /\ (CauchyRiemanEq f c) <-> (holomorphic f c).
Proof.
  split => H; first by apply: Diff_CR_holo.
  split; first by apply: holo_differentiable.
  by apply: holo_CauchyRieman.
Qed.

End CR_holo.
