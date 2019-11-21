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
(* Obligation Tactic := idtac. *)

Section cauchyetoile.
Variable R : rcfType.

 Local Notation sgr := Num.sg.
 Local Notation sqrtr := Num.sqrt.
 Local Notation C := R[i].

 Notation Re:= (@complex.Re R).
 Notation Im:= (@complex.Im R).

  
 (*Adapting lemma eq_complex from complex.v, 
 which was done in boolean style*)
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

 Lemma ReIm_eq0 (x : C) : (x=0) = ((Re x = 0)/\(Im x = 0)).
 Proof.
  by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex.  
 Qed.

 Lemma normc0 : normc 0 = 0 :> R  .
 Proof. 
  by rewrite /normc //= expr0n //= add0r sqrtr0.
 Qed.

 Lemma normcN ( x : C) : normc (-x) = (normc x).
 Admitted.

 Lemma normc_r (x : R) : normc (x%:C) = normr (x).
 Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.


 Lemma normc_i (x : R) : normc (x*i) = normr (x).
 Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

 Lemma normcN1 : normc (-1%:C) = 1 :> R.
 Proof.  
  by rewrite /normc/=  oppr0 expr0n addr0 -signr_odd expr0 sqrtr1.
 Qed.

 Lemma realtocomplex_additive : forall x y : R, (x + y)%:C = x%:C + y%:C. 
 Proof.
  (*real_complex_additive*)
  move => x y ; rewrite -!complexr0 eqE_complex //=.
  by split ; last by rewrite addr0.  
 Qed.

 Lemma real_complex_inv : forall x : R, x%:C^-1 = (x^-1)%:C.
 Proof.
 Search _ (rmorphism _).
 Admitted. 

 Lemma Im_inv : ('i%C)^-1 = (-1*i) :> C.
 Proof. Admitted.  

 Lemma invcM : forall x y : C, (x*y)^-1 = x^-1 * y^-1.
 (*Maybe another lemma is doing that, or invrM *)
 Proof. Admitted.

Lemma scale_inv : forall (h : R)  (v : C), (h*:v)^-1 = h^-1 *: v^-1.
 (*Maybe another lemma is doing that, or invrM *)
 Proof. Admitted.
 

 Lemma Im_mul : forall x : R, (x*i) = (x%:C * 'i%C). 
 Proof. by move => x ; simpc. Qed.
  
 Lemma normcD : forall ( x y : C), normc (x+y) <= (normc x + normc y).
 Proof.
  by move => x y ; rewrite -lecR realtocomplex_additive ; apply :lec_normD .
 Qed. 

 Lemma normcZ :  forall (l : R) (x : C), normc (l *: x) = `|l| * (normc x).
 Proof.
  move => l [a b] ;  rewrite /normc //= !exprMn. 
  rewrite -mulrDr sqrtrM ; last by rewrite sqr_ge0.
  by rewrite sqrtr_sqr.
 Qed.

 Lemma scalecr : forall w : C^o, forall r : R, (r *: w = r%:C *: w). 
 Proof. by move => [a b ] r; rewrite eqE_complex //=; split; simpc. Qed.

Lemma normc_ge0 (x : C) : 0 <= normc x.
Proof. case: x => ? ?; exact: sqrtr_ge0. Qed.

Lemma mulrnc (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Section C_Rnormed.
 
 (* Uniform.mixin_of takes a locally but does not expect a TopologicalType, which is inserted in the Uniform.class_of *)
 (* Whereas NormedModule.mixin_of asks for a Uniform.mixin_of loc *)

(*Context (K : absRingType). Nor working with any K, how to close the real scope ? Do it before ?  *) 

 
 Program Definition uniformmixin_of_normaxioms (V : lmodType R) (norm : V -> R)
         (ax1 : forall x y : V, norm (x + y) <= norm x + norm y)
         ( ax2 : forall (l : R) (x : V), norm (l *: x) = `|l| * (norm x))
         ( ax4 : forall x : V, norm x = 0 -> x = 0 ) : Uniform.mixin_of _ (locally_ (ball_ norm))
  := @Uniform.Mixin _ V (locally_ (ball_ norm))  (ball_ norm) _ _ _ _.
 Next Obligation.
 move => V norm _ H _ ; rewrite /ball_ => x e.  
 have -> :  x - x = 0 . by rewrite addrN.
 suff -> : norm 0 = 0 by [].
 have -> : 0 = 0 *: x by rewrite scale0r.
  by rewrite H normr0 mul0r.  
 Qed.
 Next Obligation.
  move => V norm _ H _ ; rewrite /ball_ => x e e0.
  have -> : x - e = (-1) *: (e-x) by rewrite -opprB scaleN1r. 
  by rewrite (H (-1) (e-x)) normrN1 mul1r. 
 Qed.
 Next Obligation.
  move => V norm H _ _ ; rewrite /ball_ => x y z e1 e2 normxy normyz.
  by rewrite (subr_trans y) (order.Order.POrderTheory.le_lt_trans (H  _ _)) ?ltr_add.
 Qed.
 Next Obligation. by []. Qed. 

 (*C as a R-lmodule *)
 Definition C_RlmodMixin := (complex_lmodMixin R). (*R instead of R_rcfType is not working *)
(*LmodType is hard to use, not findable through Search and not checkable as abbreviation is not applied enough*)
 Definition C_RlmodType := @LmodType R C C_RlmodMixin.
 Definition C_pointedType := PointedType C 0.
 Canonical C_pointedType.
 Definition C_filteredType := FilteredType C C (locally_ (ball_ (@normc R))).
 Canonical C_filteredType.
 (*Are we sure that the above is canonical *)
 

 Program Definition C_RuniformMixin :=
   @uniformmixin_of_normaxioms (complex_lmodType R) (@normc R) normcD normcZ (@eq0_normc R).
 Definition C_RtopologicalMixin := topologyOfBallMixin C_RuniformMixin.
(* Definition C_RtopologicalType := TopologicalType C_filteredType C_RtopologicalMixin.*)
Canonical C_RtopologicalType := TopologicalType C C_RtopologicalMixin.
(* Definition C_RuniformType := @UniformType C_RtopologicalType C_RuniformMixin.*)
Canonical C_RuniformType := UniformType C C_RuniformMixin.

Lemma normc_natmul (x : C) k : normc (x *+ k) = (normc x) *+ k.
Proof.
elim: k => [|k ih]; first by rewrite !mulr0n normc0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite -ih; exact/normcD.
have [/eqP->|x0] := boolP (normc x == 0).
  by rewrite mul0rn add0r normc_ge0.
case: x x0 ih; rewrite /normc => a b x0.
Admitted.

Program Definition C_RnormedMixin :=
  @Num.NormedMixin _ _ _ _ normcD (@eq0_normc _) normc_natmul normcN.
Canonical C_RnormedType := NormedZmodType R C^o C_RnormedMixin.

Lemma normc_ball :
  @ball _ [uniformType R of C^o] = ball_ (fun x => `| x |).
Proof. by []. Qed.

Definition normc_UniformNormedZmodMixin :=
  UniformNormedZmodule.Mixin normc_ball.
Canonical normc_uniformNormedZmodType :=
  UniformNormedZmoduleType R C^o normc_UniformNormedZmodMixin. (* TODO: warning *)

Definition C_RnormedModMixin := @NormedModMixin R normc_uniformNormedZmodType _ normcZ.
Canonical C_RnormedModType :=
  NormedModType R normc_uniformNormedZmodType C_RnormedModMixin.

(*
 Program Definition C_RnormedMixin
  := @NormedModMixin R_absRingType C_RlmodType _ C_RuniformMixin (@normc R) normcD normcZ _  (@eq0_normc R) .
 Next Obligation. by []. Qed. 

 Definition C_RnormedType : normedModType R := @NormedModType R C_RuniformType C_RnormedMixin.
*)

 Lemma scalecAl : forall (h : R) ( x y : C_RnormedType),
   h *: ( x * y) = h *: x * y. 
 Proof. move => h [a b] [c d]. simpc. Admitted.


 Definition C_RLalg := LalgType R C_RlmodType scalecAl. 

End C_Rnormed.
 

Section C_absRing.

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
  
  Canonical absRing_normedType (K : absRingType) := [normedModType K^o of K for (AbsRing_NormedModType K)].

*)

(*  Lemma abs_normE : forall ( K : absRingType) (x : K), `|x|%real = `|[x]|.
  Proof.  by []. Qed.*)

  (*Delete absCE and adapt from abs_normE *)
(*  Lemma absCE : forall x : C, `|x|%real = (normc x).
  Proof. by []. Qed.*)

(*  Lemma normCR : forall x : R, `|[x%:C]| = `|x|%real.
  Proof. Admitted.*)
  
(*  Lemma absring_real_complex : forall r: R, forall x : R, AbsRing_ball 0 r x ->
   (AbsRing_ball 0%:C r x%:C).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE.
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_r. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.


  Lemma absring_real_Im :  forall r: R, forall x : R, AbsRing_ball 0 r x ->
                                            (AbsRing_ball  0%:C r x*i).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE. 
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_i. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.*)

  Lemma scalei_muli : forall z : C^o,  ('i * z) = ('i *: z).
  Proof.
    by []. 
  Qed.

  Lemma iE : 'i%C = 'i :> C.
  Proof. by []. Qed.

  Lemma scaleC_mul : forall (w  v : C^o), (v *: w = v * w).  
  Proof. by []. Qed. 

End C_absRing.

Section Holomorphe.

Print differentiable_def. 
(* used in derive.v, what does center means*)
(*CoInductive
differentiable_def (K : absRingType) (V W : normedModType K) (f : V -> W) 
(x : filter_on V) (phF : phantom (set (set V)) x) : Prop :=
    DifferentiableDef : continuous 'd f x /\ f = (cst (f (lim x)) + 'd f x) \o
                center (lim x) +o_x center (lim x) -> differentiable_def f phF *)
(*Diff is defined from any normedmodule of any absringtype,
 so C is a normedmodul on itsself *)
(*Vague idea that this should work, as we see C^o as a vector space on C and not R*)


(*Important : differentiable in derive.v, means continuoulsy differentiable, 
not just that the limit exists. *)
(*derivable concerns only the existence of the derivative *)

 Definition holomorphic (f : C^o -> C^o) (c: C^o) :=
  cvg ((fun (h:C^o)=> h^-1 *: ((f \o shift c) (h) - f c)) @ (locally' 0)).

 Definition complex_realfun (f : C^o -> C^o) : C_RnormedType -> C_RnormedType := f.
 Arguments complex_realfun _ _ /.

 Definition complex_Rnormed_absring : C_RnormedType -> C^o := id.

 Definition CauchyRiemanEq_R2 (f : C_RnormedType -> C_RnormedType) c :=
  let u := (fun c => Re ( f c)): C_RnormedModType -> R^o  in 
  let v:= (fun c => Im (f c)) :  C_RnormedModType -> R^o in
  (* ('D_(1%:C) u = 'D_('i) v) /\ ('D_('i) u = 'D_(1%:C) v). *)
  (((derive u c (1%:C)) = 
         (derive v c ('i))) /\ ((derive v c (1%:C)) = -(derive u c ('i)))).


 Definition deriveC (V W : normedModType C)(f : V -> W) c v :=
  lim ((fun (h: C^o) => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' 0).

 Definition CauchyRiemanEq (f : C -> C) z :=
  'i * lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 1%:C) - f z)) @ (@locally' [topologicalType of R^o] 0)) =
   lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 'i%C) - f z)) @ (@locally' [topologicalType of R^o] 0)).

  
 Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
 Proof. exact: (inj_eq (@complexI _)). Qed.

 Lemma eqCI (r s : R) : (r*i == s*i) = (r == s).
 Proof.  Admitted.


(*Lemma lim_trans (T : topologicalType) (F : set (set T))  
(G : set (set T)) (l : T) : ( F `=>` G ) -> (G --> l) -> ( F --> l). 
  move => FG Gl A x.
  Search "lim" "trans". 
 *)

 Lemma flim_translim (T : topologicalType) (F G: set (set T)) (l :T) :
   F `=>` G -> (G --> l) -> (F --> l). 
 Proof.
  move => FG Gl. apply : flim_trans.
   exact : FG.   
   exact : Gl. 
 Qed.


 Lemma cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
    cvg (f @ F) -> cvg ((k \*: f) @ F ).
 Proof. 
    by move => /cvg_ex [l H0] ; apply: cvgP; apply: lim_scaler; apply: H0. 
 Qed.

(* Lemma cvg_proper_top  (T : topologicalType) (F : set (set  U)) (FF : Filter F) : *)
(*   cvg F  -> ProperFilter F.   *)


 Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
      cvg(f@F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
 Proof.
  move => cv. 
  symmetry.
  by apply: flim_lim; apply: lim_scaler .  
 Qed.

(*this could be done for scale also ... *)

(*I needed filter_of_filterE to make things easier - 
looked a long time of it as I was looking for a [filter of lim]*
 instead of a [filter of filter]*)

(*There whould be a lemma analogous to [filter of lim] to ease the search  *)
Lemma holo_derivable  (f : C^o -> C^o) c :  holomorphic f c
         -> (forall v:C , derivable (complex_realfun f) c v).
Proof.
  move => /cvg_ex [l H]; rewrite /derivable => v. 
  rewrite /type_of_filter /= in l H.
  set ff : C_RnormedType -> C_RnormedType :=  f.
  set quotR := (X in (X @ _)).
  pose mulv (h :R):= (h *:v). 
  pose quotC (h : C) : C^o := h^-1 *: ((f \o shift c) (h) - f c).
  (* here f : C -> C does not work - 
as if we needed C^o still for the normed structure*)
  case : (EM (v = 0)). 
  - move => eqv0 ; apply (@cvgP _ _ _ (0:C)). 
    have eqnear0 : {near locally' (0:R), 0 =1 quotR}.
      exists 1 => // h _ _ ; rewrite /quotR /shift eqv0. simpl.
      by rewrite scaler0 add0r addrN scaler0.
      (*addrN is too hard to find through Search *)
    apply: flim_translim.
    - exact (flim_eq_loc eqnear0).
    - by apply : cst_continuous.
    (*WARNING : lim_cst from normedtype applies only to endofunctions
     That should NOT be the case, as one could use it insteas of cst_continuous *)
  - move/eqP => vneq0 ; apply : (cvgP (l := v *: l)). (*chainage avant et suff *) 
    have eqnear0 : {near (locally' (0 : R)), (v \*: quotC) \o mulv =1 quotR}.
      exists 1 => // h _ neq0h //=; rewrite /quotC /quotR /mulv scale_inv.  
      rewrite scalerAl scalerCA -scalecAl mulrA -(mulrC v) mulfV. 
      rewrite mul1r; apply: (scalerI (neq0h)).
        by rewrite !scalerA //= (divff neq0h).  
        by []. 
    have subsetfilters: quotR @ locally' 0 `=>` (v \*: quotC) \o mulv @locally' 0.
    by exact: (flim_eq_loc eqnear0).
    apply: flim_trans subsetfilters _.
    unshelve apply : flim_comp.
    - exact  (locally' (0:C)).
    - move => //= A [r [leq0r ballrA]].
      exists (r / (`|[v]|)).
      - apply : mulr_gt0 ; first by []. 
        by rewrite invr_gt0 normm_gt0.
      - move => b; rewrite /AbsRing_ball /ball_ sub0r absRE normrN => ballrb neqb0.
        have ballCrb : (AbsRing_ball 0 r (mulv b)). 
         rewrite  /AbsRing_ball /ball_ sub0r absrN /mulv scalecr absrM abs_normE.  
         rewrite -ltr_pdivl_mulr.
         - by rewrite normCR.
        by rewrite abs_normE normm_gt0. 
      have bneq0C : (b%:C != 0%:C) by move: neqb0; apply: contra; rewrite eqCr.
      by apply: (ballrA (mulv b) ballCrb); rewrite scaler_eq0; apply/norP; split.
    suff : v \*: quotC @ locally' (0 : C) -->  v *: l by []. 
    by apply: lim_scaler ; rewrite /quotC.
Qed.      

Lemma holo_CauchyRieman (f : C^o -> C^o) c: (holomorphic f c) -> (CauchyRiemanEq f c). 
Proof.
  move => H; rewrite /CauchyRiemanEq.
  pose quotC := (fun h : C => h^-1 *: ((f \o shift c) (h) - f c)).
  pose quotR := (fun h : R => h^-1 *: ((f \o shift c) (h *: 1%:C ) - f c)).
  pose quotiR := (fun (h : R) => h^-1 *: ((f \o shift c) (h *: 'i%C) - f c)).
  have eqnear0x : {near (locally' 0), quotC \o ( fun h => h *: 1%:C) =1 quotR}.
     exists 1 ; first by [] ; move => h  _ _ //=; simpc.
       by rewrite /quotC /quotR real_complex_inv -scalecr; simpc.
  pose subsetfiltersx := (flim_eq_loc eqnear0x).
  have -> : lim (quotR @ (locally' 0))
           = lim (quotC @ (locally' 0)).  
  apply: flim_map_lim.  
  suff: quotR @ (locally' 0) `=>` (quotC @ (locally' 0)). 
    move => H1; apply: (flim_translim H1) ;  exact H. (*can't apply a view*)
    apply :  flim_trans.   
    - exact : (subsetfiltersx (locally'_filter 0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : flim_comp. 
    (*just showing that linear maps preserve balls 
     - general lemma ? *)
       - exact (locally' 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc.      
         apply :  (absringrA h%:C).
          - by apply : absring_real_complex.
          - by rewrite eqCr .
  by [].
  have eqnear0y : {near (locally' 0), 'i \*:quotC  \o ( fun h => h *: 'i%C)  =1 quotiR }.
    exists 1 ; first by [] ; move => h _ _ //= ;  simpc.
    rewrite /quotC /quotiR (Im_mul h) invcM.   
    rewrite scalerA real_complex_inv Im_inv !scalecr; simpc ; rewrite (Im_mul h).
    by rewrite !real_complexE.
  pose subsetfiltersy := (flim_eq_loc eqnear0y). 
  have properlocally' : ProperFilter (locally'(0:C)).
  (*This should be Canonical *)
  split.
   - rewrite /locally' /within => [[r leq0r] ballrwithin]; apply: (ballrwithin ((r/2)%:C) _). 
     rewrite /AbsRing_ball /ball_ absCE sub0r normcN //= .
     rewrite expr0n //= addr0 sqrtr_sqr //= ger0_norm.
     rewrite ltr_pdivr_mulr ; last by [] .
     rewrite ltr_pmulr ; last by  [].
     by apply: ltr_spaddl. (* 1 < 2 *)
     by apply : divr_ge0; apply ltrW. 
     have : (r / 2 != 0) by apply: mulf_neq0 ;apply: lt0r_neq0.
     have -> : (0 = 0%:C) by move => K //=. 
     by apply: contra=> /eqP /complexI /eqP.
     (* une vue permet d'abord d'utiliser une implication sur le terme 
      en tête sans avoir à l 'introduire*)  
   - by apply: locally'_filter.
  have <- : lim (quotiR @ (locally' 0))
           = 'i * lim (quotC @ (locally' 0)).
    have -> : 'i * lim (quotC @ (locally' 0)) 
           =  lim ('i \*: quotC @ (locally' 0)). 
      rewrite  scalei_muli  limin_scaler; first by [].  
      by exact: H.
    apply: flim_map_lim.
         suff: quotiR @ (locally' 0)
                   `=>` ('i \*: quotC @ (locally' 0)).
         move => H1 ; apply: flim_translim.
         - exact: H1.
         - by apply : cvg_scaler; exact : H. 
    apply: flim_trans.   
    - apply : (subsetfiltersy (locally'_filter 0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : flim_comp. 
       - exact (locally' 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0; simpc. 
         apply: (absringrA). 
          - by apply : absring_real_Im.
          - by rewrite eqCI.
      rewrite filter_of_filterE.
    by []. 
 by [].
Qed.



(* Local Notation "''D_' v f" := (derive f ^~ v). *)
(* Local Notation "''D_' v f c" := (derive f c v). *)

Print derive. 
 Lemma Diff_CR_holo (f : C -> C) : (*This does not work pointwise *)
   (forall c v : C, derivable ( f : C_RnormedType -> C_RnormedType) c v)
   /\ (forall c, CauchyRiemanEq f c) ->(forall c, (holomorphic f c)).
 (*sanity check : derivable (f : C ->C) does not type check  *)
 Proof.
   move => [der CR] c. 
   (* (* first attempt with littleo but requires to mix littleo on filter on different types ...*) *)
   suff :  exists l, forall h : C_absRingType,
         f (c + h) = f c + h * l + 'o_[filter of locally (0 : C)] id  h.
   admit.
   move: (der c 1%:C ); simpl => /cvg_ex [lr /flim_lim //= Dlr].
   move: (der c 'i); simpl  => /cvg_ex [li /flim_lim //= Dli].
   simpl in (type of lr); simpl in (type of Dlr).
   simpl in (type of li); simpl in (type of Dli).
   move : (CR c) ; rewrite /CauchyRiemanEq //=  (Dlr) (Dli) => CRc.
   pose l:= ((lr + lr*'i)) ; exists l; move  => [a b].
   move: (der (c + a%:C)  'i); simpl => /cvg_ex [//= la /flim_lim //= Dla].
   move: (der (c + a%:C) 'i) => /derivable_locallyxP.
   rewrite /derive //= Dla => oR.
   have -> : (a +i* b) = (a%:C + b*: 'i%C) by simpc.
   rewrite addrA oR.
   (*have fun a => la = cst(lr) + o_0(a). *)
   move: (der c 1%:C); simpl => /derivable_locallyxP ; rewrite /derive //= Dlr => oC.
   (* rewrite [a%:C]/(a *: 1%:C). *)
   have -> : a%:C = (a *: 1%:C) by simpc.
   rewrite oC. Print real_complex. 
   have lem : (fun a =>( la - lr)) = 'o_[ filter of locally (0:R)] (@real_complex R) .
   (*tried : la - lr = 'o_[ filter of locally (0:R)] (@real_complex R) a :> C^o *)
   move => s0.  Check eqoE.
   suff :   (fun _ : R => la - lr) = 'a_o_[filter of locally (0:R)] (real_complex R).
   admit.
   move => s1. 
    
   
   apply: eqoE. (*eqoE and eqoP are not working*) apply: eqoE. apply: eqoE. 
   (* struggling with o *)
   Search "o" in landau.

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
 
Theorem CauchyRiemann (f : C^o -> C^o) c:  ((holomorphic f c))
          <-> (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c). 
Proof.
Admitted.




End Holomorphe.
