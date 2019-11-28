(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop order ssralg ssrnum.
From mathcomp Require Import complex.
From mathcomp Require Import boolp reals ereal derive.
Require Import classical_sets posnum topology normedtype landau integral.

(*Pour distinguer fonctions mesurables et integrables,
utiliser des structures comme posrel. *)
Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section complex_extras.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Re := (@complex.Re R).
Local Notation Im := (@complex.Im R).

(*Adapting lemma eq_complex from complex.v, which was done in boolean style*)
Lemma eqE_complex : forall (x y : C), (x = y) = ((Re x = Re y) /\ (Im x = Im y)).
Proof.
move => [a b] [c d]; apply : propositional_extensionality ; split.
by move => -> ; split.
by  case => //= -> ->.
Qed.

Lemma Re0 : Re 0 = 0 :> R.
Proof. by []. Qed.

Lemma Im0 : Im 0 = 0 :> R.
Proof. by []. Qed.

Lemma ReIm_eq0 (x : C) : (x = 0) = ((Re x = 0) /\ (Im x = 0)).
Proof. by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex. Qed.

Lemma scalei_muli : forall z : C^o, 'i * z = 'i *: z.
Proof. by []. Qed.

Lemma iE : 'i%C = 'i :> C.
Proof. by []. Qed.

Lemma scaleC_mul : forall (w  v : C^o), (v *: w = v * w).
Proof. by []. Qed.

Lemma normc0 : normc 0 = 0 :> R  .
Proof. by rewrite /normc //= expr0n //= add0r sqrtr0. Qed.

Lemma normcN (x : C) : normc (- x) = normc x.
Proof. by case: x => a b /=; rewrite 2!sqrrN. Qed.

Lemma normc_r (x : R) : normc (x%:C) = normr x.
Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.

Lemma normc_i (x : R) : normc (x*i) = normr x.
Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

Lemma normcN1 : normc (-1%:C) = 1 :> R.
Proof. by rewrite /normc/=  oppr0 expr0n addr0 -signr_odd expr0 sqrtr1. Qed.

Lemma realtocomplex_additive (x y : R) : (x + y)%:C = x%:C + y%:C.
Proof.
(*real_complex_additive*)
rewrite -!complexr0 eqE_complex //=; by split; last by rewrite addr0.
Qed.

Lemma real_complex_inv (x : R) : x%:C^-1 = (x^-1)%:C.
Proof.
(* Search _ (rmorphism _). *)
have [/eqP->|x0] := boolP (x == 0); first by rewrite !invr0.
apply/eqP; rewrite eq_complex /= mul0r oppr0 eqxx andbT expr0n addr0.
by rewrite expr2 invrM ?unitfE // mulrA divrr ?unitfE // div1r.
Qed.

Lemma Im_inv : ('i%C)^-1 = (-1 *i) :> C.
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
Proof. by rewrite -lecR realtocomplex_additive; apply: lec_normD. Qed.

Lemma normcZ (l : R) : forall (x : C), normc (l *: x) = `|l| * (normc x).
Proof.
by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma scalecr : forall w : C^o, forall r : R, (r *: w = r%:C *: w).
Proof. by move=> [a b] r; rewrite eqE_complex //=; split; simpc. Qed.

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

Lemma real_norm (b : R) : `|b%:C| = `|b|%:C.
Proof. by rewrite normc_def /= expr0n addr0 sqrtr_sqr. Qed.

Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (r s : R) : (r *i == s *i) = (r == s).
Proof. by apply/idP/idP => [/eqP[] ->//|/eqP ->]. Qed.

Lemma scale_inv (h : R) (v : C) : h != 0 -> v != 0 -> (h *: v)^-1 = h^-1 *: v^-1.
Proof.
by move=> h0 v0; rewrite scalecr invrM // ?unitfE ?eqCr // mulrC scalecr real_complex_inv.
Qed.

End complex_extras.

Section C_Rnormed.
Variable R : rcfType.

 (* Uniform.mixin_of takes a locally but does not expect a TopologicalType,
which is inserted in the Uniform.class_of *)
 (* Whereas NormedModule.mixin_of asks for a Uniform.mixin_of loc *)

(*Context (K : absRingType). Nor working with any K, how to close the real scope ? Do it before ?  *)

Program Definition uniformmixin_of_normaxioms (V : lmodType R) (norm : V -> R)
  (ax1 : forall x y : V, norm (x + y) <= norm x + norm y)
  (ax2 : forall (l : R) (x : V), norm (l *: x) = `|l| * (norm x))
  (ax4 : forall x : V, norm x = 0 -> x = 0 ) : Uniform.mixin_of _ (locally_ (ball_ norm)) :=
  @Uniform.Mixin _ V (locally_ (ball_ norm))  (ball_ norm) _ _ _ _.
Next Obligation.
move => V norm _ H _; rewrite /ball_ => x e.
rewrite subrr.
suff -> : norm 0 = 0 by [].
have -> : 0 = 0 *: x by rewrite scale0r.
by rewrite H normr0 mul0r.
Qed.
Next Obligation.
move => V norm _ H _ ; rewrite /ball_ => x e e0.
have -> : x - e = (-1) *: (e - x) by rewrite -opprB scaleN1r.
by rewrite (H (-1) (e - x)) normrN1 mul1r.
Qed.
Next Obligation.
move => V norm H _ _ ; rewrite /ball_ => x y z e1 e2 normxy normyz.
by rewrite (subr_trans y) (le_lt_trans (H  _ _)) ?ltr_add.
Qed.
Next Obligation. by []. Qed.

(*C as a R-lmodule *)
(*Definition C_RlmodMixin := (complex_lmodMixin R).
(*LmodType is hard to use, not findable through Search
 and not checkable as abbreviation is not applied enough*)
Definition C_RlmodType := @LmodType R C C_RlmodMixin.*)
(*Are we sure that the above is canonical *)

Local Notation C := R[i].

Definition C_pointedType := PointedType C 0.
Canonical C_pointedType.
Definition C_filteredType := FilteredType C C (locally_ (ball_ (@normc R))).
Canonical C_filteredType.

(*Definition C_RtopologicalType := TopologicalType C_filteredType C_RtopologicalMixin.*)
(*Definition C_RtopologicalType := TopologicalType C C_RtopologicalMixin.*)
(*Definition C_RuniformType := @UniformType C_RtopologicalType C_RuniformMixin.*)
(*Definition C_RuniformType := UniformType C_RtopologicalType C_RuniformMixin.*)
(*Definition C_RnormedZmodType := NormedZmodType R C^o C_RnormedMixin.*)

Definition Rcomplex := R[i].
Canonical Rcomplex_eqType := [eqType of Rcomplex].
Canonical Rcomplex_choiceType := [choiceType of Rcomplex].
Canonical Rcomplex_zmodType := [zmodType of Rcomplex].
Canonical Rcomplex_lmodType := [lmodType R of Rcomplex].
Canonical Rcomplex_pointedType := [pointedType of Rcomplex].
Canonical Rcomplex_filteredType := [filteredType Rcomplex of Rcomplex].
Definition Rcomplex_uniformMixin :=
  @uniformmixin_of_normaxioms [lmodType R of Rcomplex] (@normc R) (@normcD _) (@normcZ _) (@eq0_normc _).
Definition Rcomplex_topologicalMixin := topologyOfBallMixin Rcomplex_uniformMixin.
Canonical Rcomplex_topologicalType :=
  TopologicalType Rcomplex Rcomplex_topologicalMixin.
Canonical Rcomplex_uniformType := UniformType Rcomplex Rcomplex_uniformMixin.
Definition Rcomplex_normedMixin :=
  @Num.NormedMixin _ _ _ _ (@normcD R) (@eq0_normc _) (@normc_mulrn _) (@normcN _).
Canonical Rcomplex_normedZmodType := NormedZmodType R Rcomplex Rcomplex_normedMixin.

Lemma Rcomplex_ball_ball_ :
  @ball _ [uniformType R of Rcomplex] = ball_ (fun x => `| x |).
Proof. by []. Qed.

Definition Rcomplex_uniformNormedZmodMixin :=
  UniformNormedZmodule.Mixin Rcomplex_ball_ball_.
Canonical Rcomplex_uniformNormedZmodType :=
  UniformNormedZmodType R Rcomplex Rcomplex_uniformNormedZmodMixin.

Definition Rcomplex_normedModMixin :=
  @NormedModMixin R [uniformNormedZmodType R of Rcomplex] _ (@normcZ _).
Canonical Rcomplex_normedModType :=
  NormedModType R Rcomplex Rcomplex_normedModMixin.

Lemma scalecAl (h : R) (x y : Rcomplex_normedModType) : h *: (x * y) = h *: x * y.
Proof.
by move: h x y => h [a b] [c d]; simpc; rewrite -!mulrA -mulrBr -mulrDr.
Qed.

Definition C_RLalg := LalgType R Rcomplex scalecAl.

End C_Rnormed.

Section cauchyetoile.
Variable R : rcfType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Re := (@complex.Re R).
Local Notation Im := (@complex.Im R).

(*Important: C is a lmodType R while C^o is a lmodType C*)

(*Section C_absRing.*)
(* This is now replaced by  complex_numFieldType and numFieldType_normedModType.*)

(*
  Definition C_AbsRingMixin := @AbsRingMixin (complex_ringType R_rcfType)
                 (@normc R_rcfType) normc0 normcN1 normcD (@normcM R_rcfType )
                             (@eq0_normc R_rcfType).
  Definition C_absRingType :=  AbsRingType C C_AbsRingMixin.
  Canonical C_absRingType.
  Definition C_topologicalType := [topologicalType of C for C_absRingType].
  Canonical C_topologicalType.
  Definition C_uniformType := [uniformType of C for C_absRingType].
  Canonical C_uniformType.
  Definition Co_pointedType := [pointedType of C^o for C_absRingType].
  Definition Co_filteredType := [filteredType C^o of C^o for C_absRingType].
  Definition Co_topologicalType := [topologicalType of C^o for C_absRingType].

  Canonical Zmod_topologicalType ( K : absRingType)
            (V : normedModType K):=
    [topologicalType of [zmodType of V]].

  Definition Co_uniformType := [uniformType of C^o for C_absRingType].
  Definition Co_normedType := AbsRing_NormedModType C_absRingType.
  Canonical C_normedType := [normedModType C^o of C for Co_normedType].
  (*C is convertible to C^o *)

  Canonical R_normedType := [normedModType R of R for  [normedModType R of R^o]].

  Canonical absRing_normedType (K : absRingType) := [normedModType K^o
of K for (AbsRing_NormedModType K)].

*)


(* NB: not used *)
Lemma flim_translim (T : topologicalType) (F G: set (set T)) (l :T) :
   F `=>` G -> (G --> l) -> (F --> l).
Proof. move => FG Gl. apply : flim_trans; [exact : FG | exact : Gl]. Qed.

Lemma cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
 (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
 cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. by move => /cvg_ex [l H0] ; apply: cvgP; apply: lim_scaler; apply: H0. Qed.

Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
  (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
  cvg(f @ F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof. by move => cv; apply/esym/flim_lim; apply: lim_scaler. Qed.

Section Holomorphe.

Print differentiable_def.
(* used in derive.v, what does center means*)
(*CoInductive
differentiable_def (K : absRingType) (V W : normedModType K) (f : V -> W)
(x : filter_on V) (phF : phantom (set (set V)) x) : Prop :=
    DifferentiableDef : continuous 'd f x /\ f = (cst (f (lim x)) + 'd f x) \o
                center (lim x) +o_x center (lim x) -> differentiable_def f phF *)
(*Diff is defined from any normedmodule of any absringtype,
 so C is a normedmodul on itself *)
(*Vague idea that this should work, as we see C^o as a vector space on C and not R*)

(*Important : differentiable in derive.v, means continuoulsy differentiable,
not just that the limit exists. *)
(*derivable concerns only the existence of the derivative *)

Definition holomorphic (f : C^o -> C^o) (c : C^o) :=
  cvg ((fun (h : C^o) => h^-1 *: ((f \o shift c) h - f c)) @ (locally' (0:C^o))).

Definition complex_realfun (f : C^o -> C^o) : Rcomplex_normedModType R -> Rcomplex_normedModType R := f.
Arguments complex_realfun _ _ /.

(* NB: not used *)
Definition complex_Rnormed_absring : Rcomplex_normedModType R -> C^o := id.

Definition CauchyRiemanEq_R2 (f : Rcomplex_normedModType R -> Rcomplex_normedModType R) c :=
  let u := (fun c => Re (f c)) : Rcomplex_normedModType R -> R^o  in
  let v:= (fun c => Im (f c)) : Rcomplex_normedModType R -> R^o in
  'D_1%:C u c = 'D_'i v c /\ 'D_1%:C v c = - 'D_'i u c.

(* NB: not used *)
Definition deriveC (V W : normedModType C) (f : V -> W) c v :=
  lim ((fun (h : C^o) => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' 0).

Definition CauchyRiemanEq (f : C -> C) z :=
  'i * lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 1%:C) - f z)) @ (locally' (0:R^o))) =
  lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 'i%C) - f z)) @ (locally' (0:R^o))).
(*this could be done for scale also ... *)

(*I needed filter_of_filterE to make things easier -
looked a long time of it as I was looking for a [filter of lim]*
 instead of a [filter of filter]*)

(*There should be a lemma analogous to [filter of lim] to ease the search  *)
Search "normedType".
(* Canonical C_normedType := [normedModType C of C for  [normedModType C of C^o]]. *)

Definition Rderivable (V W : normedModType R) (f : V -> W) := derivable f.

(*The topological structure on R is given by R^o *)
Lemma holo_derivable (f : (Rcomplex R)^o -> (Rcomplex R)^o) c :
  holomorphic f c -> (forall v : C, Rderivable (complex_realfun f) c v).
Proof.
move=> /cvg_ex [l H]; rewrite /Rderivable /derivable => v /=.
rewrite /type_of_filter /= in l H.
set ff : Rcomplex_normedModType R -> Rcomplex_normedModType R := f.
set quotR := (X in (X @ _)).
pose mulv (h : R) := (h *: v).
pose quotC (h : C) : C^o := h^-1 *: ((f \o shift c) h - f c).
(* here f : C -> C does not work - as if we needed C^o still for the normed structure*)
case: (EM (v = 0)) => [eqv0|/eqP vneq0].
- apply (cvgP (l := (0:Rcomplex R))).
  have eqnear0 : {near locally' (0:R^o), 0 =1 quotR}.
    by exists 1=> // h _ _ ; rewrite /quotR /shift eqv0 /= scaler0 add0r addrN scaler0.
  apply: flim_trans.
  + exact (flim_eq_loc eqnear0).
  + exact: cst_continuous.
    (*WARNING : lim_cst from normedtype applies only to endofunctions
     That should NOT be the case, as one could use it insteas of cst_continuous *)
- apply (cvgP (l := v *: l : Rcomplex R)).
  have eqnear0 : {near (locally' (0 : R^o)), (v \*: quotC) \o mulv =1 quotR}.
    exists 1 => // h _ neq0h //=; rewrite /quotC /quotR /mulv scale_inv //.
    rewrite scalerAl scalerCA -scalecAl mulrA -(mulrC v) mulfV // mul1r.
    by apply: (scalerI neq0h); rewrite !scalerA //= (divff neq0h).
  have subsetfilters : quotR @ locally' (0:R^o) `=>` (v \*: quotC) \o mulv @ locally' (0:R^o).
    exact: (flim_eq_loc eqnear0).
  apply: flim_trans subsetfilters _.
  suff : v \*: quotC \o mulv @ locally' (0:R^o) `=>` locally (v *: l).
    move/flim_trans; apply.
    (* locally (v *: l) `=>` [filter of v *: ]l *)
    move=> a -[x x0 Hx].
    exists x%:C; first by rewrite ltcR.
    by move=> /= y yx; apply Hx; rewrite /ball_ -ltcR.
  apply: (@flim_comp _ _ _ _ _ _ (locally' (0:C^o))).
  + move => //= A [r [leq0r ballrA]].
    exists (normc r / normc v).
    * rewrite mulr_gt0 //.
      by rewrite normc_gt0 gt_eqF.
      by rewrite invr_gt0 normc_gt0.
    * move=> b; rewrite /ball_ sub0r normrN => ballrb neqb0.
      have ballCrb : (@ball_ _ _ (fun x => `|x|) 0 r (mulv b)).
        rewrite  /ball_ sub0r normrN /mulv scalecr normrM.
        rewrite ltr_pdivl_mulr in ballrb; last by rewrite normc_gt0.
        rewrite -ltcR in ballrb.
        rewrite -(ger0_norm (ltW leq0r)) (le_lt_trans _ ballrb) // rmorphM /=.
        by rewrite le_eqVlt; apply/orP; left; apply/eqP; rewrite real_norm.
      have bneq0C : (b%:C != 0%:C) by move: neqb0; apply: contra; rewrite eqCr.
      by apply: (ballrA (mulv b) ballCrb); rewrite /mulv (@scaler_eq0 _ (C_RLalg R)); exact/norP.
  + suff : v \*: quotC @ locally' (0 : (Rcomplex R)^o) -->  v *: l by [].
    by apply: lim_scaler; rewrite /quotC.
Qed.

Lemma holo_CauchyRieman (f : C^o -> C^o) c : holomorphic f c -> CauchyRiemanEq f c.
Proof.
move=> H; rewrite /CauchyRiemanEq.
pose quotC := fun h : C => h^-1 *: ((f \o shift c) h - f c).
pose quotR := fun h : R => h^-1 *: ((f \o shift c) (h *: 1%:C ) - f c).
pose quotiR := fun h : R => h^-1 *: ((f \o shift c) (h *: 'i%C) - f c).
have eqnear0x : {near (locally' (0:R^o)), quotC \o (fun h => h *: 1%:C) =1 quotR}.
  exists 1; first by [].
  by move => h  _ _ //=; simpc; rewrite /quotC /quotR real_complex_inv -scalecr; simpc.
pose subsetfiltersx := flim_eq_loc eqnear0x.
have -> : lim (quotR @ (locally' (0:R^o))) = lim (quotC @ (locally' (0:C^o))).
  apply: (@flim_map_lim _ (Rcomplex_normedModType R)).
    exact: Proper_locally'_numFieldType.
  suff: quotR @ (locally' (0:R^o)) `=>` quotC @ (locally' (0:C^o)).
    move/flim_trans; apply.
    have : cvg (quotC @ locally' (0:C^o)) by [].
    move/flim_trans; apply.
    move=> /= s [x x0 xs]; exists x%:C; first by rewrite ltcR.
    by move=> y xy; apply xs; move: xy; rewrite /ball_ -ltcR.
  apply: flim_trans.
  - exact : (subsetfiltersx (locally'_filter (0:R^o))).
  - move=> {subsetfiltersx eqnear0x}.
    apply: (@flim_comp _ _ _ _ _ _ (locally' (0:(Rcomplex R)^o))).
    + move => s //= [r r0 rs].
      exists (normc r); first by rewrite normc_gt0 gt_eqF.
      move=> h rh h0; simpc; apply: (rs h%:C); last by rewrite eqCr.
      by move: rh; rewrite /ball_ !sub0r !normrN -ltcR real_norm {2}(gt0_normc r0).
    + by [].
have eqnear0y : {near (locally' (0:R^o)), 'i \*:quotC \o ( fun h => h *: 'i%C) =1 quotiR}.
  exists 1 ; first by [] ; move => h _ _ //= ;  simpc.
  rewrite /quotC /quotiR (Im_mul h) invcM.
  rewrite scalerA real_complex_inv Im_inv !scalecr; simpc; rewrite (Im_mul h).
  by rewrite !real_complexE.
pose subsetfiltersy := (flim_eq_loc eqnear0y).
have properlocally' : ProperFilter (locally'(0:C^o)).
  exact: Proper_locally'_numFieldType.
have <- : lim ((quotiR : R -> (numFieldType_normedModType (complex_numFieldType R)) (*TODO: IMP*)) @ (locally' (0:R^o))) =
    'i * lim (quotC @ (locally' (0:C^o))).
  have -> : 'i * lim (quotC @ (locally' (0:C^o))) =  lim ('i \*: quotC @ (locally' (0:C^o))).
    by rewrite scalei_muli limin_scaler. (* exact: H. *)
  apply: flim_map_lim.
    exact: Proper_locally'_numFieldType.
  suff : quotiR @ (locally' (0:R^o)) `=>` ('i \*: quotC @ (locally' (0:C^o))).
    move=> H1 ; apply: flim_trans.
    exact: H1.
    apply : cvg_scaler; exact : H.
  apply: flim_trans.
  - by apply : (subsetfiltersy (locally'_filter 0)).
  - move => {subsetfiltersx eqnear0x}.
    unshelve apply : flim_comp.
    + exact (locally' (0:C^o)).
    + move => A //= [r leq0r] absringrA.
      exists (normc r); first by rewrite normc_gt0 gt_eqF.
      move=> y ry y0.
      apply absringrA.
        move: ry; rewrite /ball_ !sub0r !normrN -ltcR {2}(gt0_normc leq0r) //.
        rewrite scalecr normrM (_ : `|'i| = 1) ?mulr1 // ?real_norm //.
        by rewrite normc_def /= expr0n expr1n add0r sqrtr1.
      rewrite scalecr scaler_eq0 negb_or; apply/andP; split.
        by rewrite eqCr.
      by apply/eqP; case => /eqP; rewrite oner_eq0.
    + by rewrite filter_of_filterE.
rewrite -/quotiR /lim_in /=; congr (get _).
rewrite funeqE => i; rewrite propeqE; split => /flim_trans; apply.
  move=> s [x x0 ix]; exists x%:C; first by rewrite ltcR.
  by move=> y y0; apply ix; move: y0; rewrite /ball_ -ltcR.
move=> s [x x0 ix]; exists (normc x); first by rewrite normc_gt0 gt_eqF.
move=> y y0; apply ix; by move: y0; rewrite /ball_ -ltcR {2}(gt0_normc x0).
Qed.

(* Local Notation "''D_' v f" := (derive f ^~ v). *)
(* Local Notation "''D_' v f c" := (derive f c v). *)

Lemma Diff_CR_holo (f : C -> C) :
  (forall c v : C, derivable (f : Rcomplex_normedModType R -> Rcomplex_normedModType R) c v) /\
    (forall c, CauchyRiemanEq f c) ->
  (forall c, (holomorphic f c)).
 (*sanity check : derivable (f : C ->C) does not type check  *)
Proof.
move => [der CR] c.
(* Before 270: first attempt with littleo but requires to mix
 littleo on filter on different types. Check now*)
suff :  exists l, forall h : C,
      f (c + h) = f c + h * l + (('o_ (0 : [filteredType C^o of C^o]) id) : _ -> numFieldType_normedModType (complex_numFieldType R) (*IMP*)) h.
  admit.
(*This should be a lemma *)
move: (der c 1%:C ); simpl => /cvg_ex [lr /flim_lim //= Dlr].
move: (der c 'i); simpl  => /cvg_ex [li /flim_lim //= Dli].
simpl in (type of lr); simpl in (type of Dlr).
simpl in (type of li); simpl in (type of Dli).
move : (CR c) ; rewrite /CauchyRiemanEq //=  (Dlr) (Dli) => CRc.
pose l:= ((lr + lr*'i)) ; exists l; move  => [a b].
move: (der (c + a%:C)  'i); simpl => /cvg_ex [//= la /flim_lim //= Dla].
move: (der (c + a%:C) 'i) => /derivable_locallyxP.
have Htmp : ProperFilter ((fun h : R => h^-1 *: (f (h *: 'i%C + (c + a%:C)) - f (c + a%:C))) @ locally' (0:R^o)).
  by apply filtermap_proper_filter; apply Proper_locally'_numFieldType.
move: (Dla Htmp) => {}Dla.
rewrite /derive //= Dla => oR.
have -> : (a +i* b) = (a%:C + b*: 'i%C) by simpc.
rewrite addrA oR.
(*have fun a => la = cst(lr) + o_0(a). *)
move: (der c 1%:C); simpl => /derivable_locallyxP ; rewrite /derive //= Dlr => oC.
(* rewrite [a%:C]/(a *: 1%:C). *)
have -> : a%:C = (a *: 1%:C) by simpc.
rewrite oC. Print real_complex.
rewrite /type_of_filter /= in la Dla oR *.
have lem : ('o_ (0 : [filteredType R^o of R^o]) (@real_complex _ : _ -> numFieldType_normedModType (complex_numFieldType R) (*IMP*))) =
           (fun a => (la - lr : C^o)).
move => s0.  Check eqoE.
Fail suff :   (fun _ : R => la - lr) = 'a_o_[filter of locally (0:R)] (real_complex R).
(* admit.
move => s1.

apply: eqoE. (*eqoE and eqoP are not working*) apply: eqoE. apply: eqoE.*)

(* (*another attempt*) *)
(* rewrite /holomorphic cvg_ex.  *)
(* move: (der c 1%:C ); simpl => /cvg_ex [lr //= Dlr].  *)
(* move: (der c 'i); simpl  => /cvg_ex [li //= Dli]. *)
(* simpl in (type of lr); simpl in (type of Dlr). *)
(* simpl in (type of li); simpl in (type of Dli). *)
(* move : (CR c) ; rewrite /CauchyRiemanEq //=  (flim_lim Dlr) (flim_lim Dli) => CRc. *)
(* pose l:= ((lr + lr*'i)) ; exists l; move => A //= [r leq0r] normrA. *)
(* pose r':= r/(sqrtr 2). *)
(* have lrl : l / (1 + 'i*1) = lr. admit.   *)
(* exists r ; first by [].     *)
(* move => [a b] ballab abneq0 //=.  *)
(* suff :   normc (l- (a +i* b)^-1 *: ((f (a +i* b + c) - f c) : C^o)) <= r.      *)
(* admit. *)
(* have : locally lr A. exists r'. *)
(* - by rewrite mulr_gt0 //= invr_gt0 sqrtr_gt0.  *)
(* - move => t; rewrite /ball_ -lrl.admit. *)
(*   (*we should have a tactic rewriting in any way that fits *) *)
(* move => /Dlr //=. *)
(* move : (Dli A) => //=.
  *)
Admitted.

Theorem CauchyRiemann (f : C^o -> C^o) c : (holomorphic f c) <->
  (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c).
Proof.
Admitted.

End Holomorphe.
