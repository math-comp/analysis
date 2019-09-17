(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
From mathcomp Require Import complex.  
From mathcomp Require Import boolp reals Rstruct Rbar derive. 
Require Import classical_sets posnum topology normedtype landau integral. 


(*TODO : Definition integrale sur chemin et segment, holomorhpe, ouvert étoilé *)
(* TODO : cloner depuis integrale et commiter. Admettre la mesure sur R  *)


(*Pour distinguer fonctions mesurables et integrables, utiliser des structures comme posrel. *)
Import GRing.Theory Num.Theory ComplexField Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.


 Set Implicit Arguments.
 Unset Strict Implicit.
 Unset Printing Implicit Defensive.
(* Obligation Tactic := idtac. *)

 Local Notation sgr := Num.sg.
 Local Notation sqrtr := Num.sqrt.
 Local Notation C := R[i].

 Notation Re:= (complex.Re).
 Notation Im:= (complex.Im).

  
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

 Lemma ReIm_eq0 (x : C) : (x=0) = ((Re x = 0)/\(Im x = 0)).
 Proof.
  by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex.  
 Qed.

 Lemma normc0 : normc 0 = 0 :> R  .
 Proof. 
  by rewrite /normc //= expr0n //= add0r sqrtr0.
 Qed.

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
  move => x y ; rewrite -!complexr0 eqE_complex //=.
  by split ; last by rewrite addr0.  
 Qed.

 

 Lemma real_complex_inv : forall x : R, x%:C^-1 = (x^-1)%:C.  
 Proof. Admitted. 

 Lemma Im_inv : ('i%C)^-1 = (-1*i) :> C.
 Proof. Admitted.  

 Lemma invcM : forall x y : C, (x*y)^-1 = x^-1 * y^-1. (*Maybe another lemma is doing that, or invrM *)
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
 Proof. by move => [a b ] r ; rewrite  eqE_complex //= ; split ;  simpc. Qed.

 
Section C_Rnormed.
 
 (* Uniform.mixin_of takes a locally but does not expect a TopologicalType, which is inserted in the Uniform.class_of *)
 (* Whereas NormedModule.mixin_of asks for a Uniform.mixin_of loc *)

(*Context (K : absRingType). Nor working with any K, how to close the real scope ? Do it before ?  *) 

 
 Program Definition uniformmixin_of_normaxioms (V : lmodType R) (norm : V -> R)
         (ax1 : forall x y : V, norm (x + y) <= norm x + norm y)
         ( ax2 : forall (l : R) (x : V), norm (l *: x) = `|l| * (norm x))
         ( ax4 : forall x : V, norm x = 0 -> x = 0 ) : Uniform.mixin_of (locally_ (ball_ norm))
  := @Uniform.Mixin V (locally_ (ball_ norm))  (ball_ norm) _ _ _ _.
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
  by rewrite (subr_trans y) (ler_lt_trans (H  _ _)) ?ltr_add.
 Qed.
 Next Obligation. by []. Qed. 

 (*C as a R-lmodule *)
 Definition C_RlmodMixin := (complex_lmodMixin R_rcfType). (*R instead of R_rcfType is not working *)
 (*LmodType is hard to use, not findable through Search and not checkable as abbreviation is not applied enough*) 
 Definition C_RlmodType := @LmodType R C C_RlmodMixin.
 Definition C_pointedType := PointedType C 0.
 Canonical C_pointedType.
 Definition C_filteredType := FilteredType C C (locally_ (ball_ (@normc R_rcfType))).
 Canonical C_filteredType.
 (*Are we sure that the above is canonical *)

 Program Definition C_RuniformMixin := @uniformmixin_of_normaxioms C_RlmodType (@normc R_rcfType) normcD normcZ (@eq0_normc R_rcfType).
 Definition C_RtopologicalMixin := topologyOfBallMixin C_RuniformMixin.
 Definition C_RtopologicalType := TopologicalType C_filteredType C_RtopologicalMixin.
 Definition C_RuniformType := @UniformType C_RtopologicalType C_RuniformMixin.


 Program Definition C_RnormedMixin
  := @NormedModMixin R_absRingType C_RlmodType _ C_RuniformMixin (@normc R_rcfType) normcD normcZ _  (@eq0_normc R_rcfType) .
 Next Obligation. by []. Qed. 


 Definition C_RnormedType : normedModType R := @NormedModType R C_RuniformType C_RnormedMixin.
End C_Rnormed.
Section C_absRing.

  Definition C_AbsRingMixin := @AbsRingMixin (complex_ringType R_rcfType) (@normc R_rcfType) normc0 normcN1 normcD (@normcM R_rcfType ) (@eq0_normc R_rcfType).

  
  
  Definition C_absRingType :=  AbsRingType C C_AbsRingMixin.
  Canonical C_absRingType.
  Definition C_topologicalType := [topologicalType of C for C_absRingType].
  Canonical C_topologicalType.
  Definition C_uniformType := [uniformType of C for C_absRingType].
  Canonical C_uniformType.
  Definition Co_pointedType := [pointedType of C^o for C_absRingType].
  (*Canonical Co_pointedType.*) 
  Locate Ro_pointedType. 
  Definition Co_filteredType := [filteredType C^o of C^o for C_absRingType].
  Definition Co_topologicalType := [topologicalType of C^o for C_absRingType].
  Definition Co_uniformType := [uniformType of C^o for C_absRingType].
  Definition Co_normedType := AbsRing_NormedModType C_absRingType.
  (*Canonical Co_normedType.*)
  (*Why is this Canonical, when the normed type on Ro is defined for R of the reals ? *)

  Lemma absCE :  forall x : C, `|x|%real = normc x.
  Proof.  by []. Qed.


  Lemma absring_real_complex : forall r: R, forall x : R, AbsRing_ball 0 r x -> (@AbsRing_ball C_absRingType 0%:C r x%:C).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE.
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_r. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.


  Lemma absring_real_Im :  forall r: R, forall x : R, AbsRing_ball 0 r x -> (@AbsRing_ball C_absRingType 0%:C r x*i).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE. 
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_i. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.

  Lemma scalei_muli : forall z : C^o,  ('i * z) = ('i *: z).
  Proof.
    by []. 
  Qed.

  Lemma iE : 'i%C = 'i :> C.
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
(*Diff is defined from any normedmodule of any absringtype, so C is a normedmodul on itsself *)
(*Vague idea that this should work, as we see C^o as a vector space on C and not R*)


(*Important : differentiable in derive.v, means continuoulsy differentiable, not just that the limit exists. *)
(*derivable concerns only the existence of the derivative *)

Definition holomorphic (f : Co_normedType -> Co_normedType) c := forall v,
cvg ((fun h => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' (0 : Co_normedType)).

Definition complex_realfun (f : C^o -> C^o) : C_RnormedType -> C_RnormedType := f.

Definition complex_Rnormed_absring : C_RnormedType -> C^o := id. (* Coercion ? *) (*Avec C tout seul au lieu de C_absRIng ça devrait passer *) 


(* Variable ( h : C_RnormedType -> C_RnormedType) (x : C_RnormedType).  *)

(* Check ('D_x h 0). (*This has a weird type *) *)
 
Definition CauchyRiemanEq_R2 (f : C_RnormedType -> C_RnormedType) c :=
  let u := (fun c => Re ( f c)): C_RnormedType -> R^o  in 
  let v:= (fun c => Im (f c)) :  C_RnormedType -> R^o in
  (* ('D_(1%:C) u = 'D_('i) v) /\ ('D_('i) u = 'D_(1%:C) v). *)
  (((derive u c (1%:C)) = 
         (derive v c ('i))) /\ ((derive v c (1%:C)) = -(derive u c ('i)))).


Definition deriveC (V W : normedModType C)(f : V -> W) c v :=
  lim ((fun h => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' (0 : C^o)).


Definition CauchyRiemanEq (f : C -> C) z:=
  'i * lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 1%:C) - f z)) @ locally' (0 : R^o)) =
   lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 'i%C) - f z)) @ locally' (0 : R^o)).

  
Lemma eqCr (R : rcfType) (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (R : rcfType) (r s : R) : (r*i == s*i) = (r == s).
Proof. Admitted.


(*Lemma lim_trans (T : topologicalType) (F : set (set T))  (G : set (set T)) (l : T) : ( F `=>` G ) -> (G --> l) -> ( F --> l). 
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


Lemma cvg_scaler (K : absRingType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
    cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. 
  by move => /cvg_ex [l H0] ; apply : cvgP ; apply :(@lim_scaler _ _ _ F _ f k l).
Qed.

About lim_scaler. 


Lemma limin_scaler (K : absRingType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (FF :Filter F) (f : T -> V) (k : K) :
      cvg(f@F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof.
  move => /cvg_ex [l H].
  (*rewrite (flim_lim H). *)
(*   The LHS of (flim_lim H) *)
(*     (lim (f @ F)) *)
(* matches but type classes inference fails *)
(*   Check (flim_lim (@lim_scaler K V T F FF f k l H)). *)
 Admitted. 


(*this could be done for scale also ... *)

(*I needed filter_of_filterE to make things easier - looked a long time of it as I was lookin for a [filter of lim]* instead of a [filter of filter]*)

(*There whould be a lemma analogous to [filter of lim] to ease the search  *)

(* 

Lemma filter_of_filterE {T : Type} (F : set (set T)) : [filter of F] = F.
Proof. by []. Qed.

Lemma locally_filterE {T : Type} (F : set (set T)) : locally F = F.
Proof. by []. Qed.

Module Export LocallyFilter.
Definition locally_simpl := (@filter_of_filterE, @locally_filterE).
End LocallyFilter.

Definition flim {T : Type} (F G : set (set T)) := G `<=` F.
Notation "F `=>` G" := (flim F G) : classical_set_scope.
Lemma flim_refl T (F : set (set T)) : F `=>` F.
Proof. exact. Qed.

Lemma flim_trans T (G F H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Notation "F --> G" := (flim [filter of F] [filter of G]) : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filteredType U) :=
  fun F : set (set U) => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T [filter of F]) : classical_set_scope.
Notation lim F := [lim F in [filteredType _ of @type_of_filter _ [filter of F]]].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := [cvg F in [filteredType _ of @type_of_filter _ [filter of F]]].
*)



Lemma holo_derivable  (f : C^o -> C^o) c :  ((holomorphic f c))
                                            -> (forall v : C, derivable (complex_realfun f) c v).
Proof.
 move => H; rewrite /derivable => v. 
  move : (H v) => /cvg_ex [l H0] {H}. (* eapply*)
  apply : (cvgP (l := l)).
  - have eqnear0 : {near (@locally' R_topologicalType  0),
     (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h *: (complex_Rnormed_absring v)) - f c))
       \o (real_complex R) =1
     (fun h0 : R_absRingType => h0^-1 *: ((complex_realfun f \o shift c) (h0 *: v )
     - complex_realfun f c)) }.
    exists 1 ; first by [] ;  move => h _ neq0h //=; rewrite real_complex_inv -scalecr.    
    by apply : (scalerI (neq0h)) ; rewrite !scalerA //= (divff neq0h) !scale1r //= -scalecr. 
  pose subsetfilters:= (flim_eq_loc eqnear0).  
  apply :  (@flim_trans _ ( (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h *: (complex_Rnormed_absring v)) - f c)) \o (real_complex R) @ (@locally' R_topologicalType  0))).
  exact : (subsetfilters (@locally'_filter R_topologicalType  0)).
- unshelve apply : flim_comp.
  exact (locally' 0%:C).
- move => //= A  [r [leq0r ballrA]] ; exists r ; first by []. 
  move => b ballrb neqb0.   
  have ballCrb : (AbsRing_ball 0%:C r b%:C).
   by apply : absring_real_complex.
  have bneq0C : (b%:C != 0%:C) by move : neqb0 ; apply : contra ; rewrite eqCr.
  by apply : (ballrA b%:C ballCrb bneq0C).
by []. 
Qed.

Lemma holo_CauchyRieman (f : C^o -> C^o) c : (holomorphic f c) -> (CauchyRiemanEq f c). 
Proof.
  move => H. (* move : (H 1%:C) => /cvg_ex [l H0] {H}. *)
  (* move :  l H0 ; rewrite filter_of_filterE => l H0. *)
  pose quotC := (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h * 1%:C) - f c)).
  pose quotR := (fun h : R_absRingType => h^-1 *: ((f \o shift c) (h *: 1%:C ) - f c)).
  pose quotiR := (fun (h : R) => h^-1 *: ((f \o shift c) (h *: 'i%C) - f c)).
  have eqnear0x : {near (@locally' R_topologicalType 0), quotC \o ( fun h => h *: 1%:C)  =1 quotR }.
     exists 1 ; first by [] ; move => h  _ _ //= ;  simpc.
     by rewrite /quotC /quotR real_complex_inv -scalecr ; simpc. 
  pose subsetfiltersx := (flim_eq_loc eqnear0x).
  rewrite /CauchyRiemanEq.
  have -> : lim (quotR @ (@locally' R_topologicalType 0))
           = lim (quotC @ (@locally' C_topologicalType 0) ).  
  apply:  (@flim_map_lim _ _ _ (@locally' R_topologicalType 0) _ _ (lim (quotC @ (@locally' C_topologicalType 0) ))).
  suff :  quotR @ (@locally' R_topologicalType 0) `=>` (quotC @ (@locally' C_topologicalType 0)).
          by move => H1 ; apply :  (flim_translim H1) ;  exact : H.   
  apply :  flim_trans.   
    - exact : (subsetfiltersx (@locally'_filter R_topologicalType  0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : flim_comp. 
    (*just showing that linear maps preserve balls - general lemma ? *)
       - exact  (@locally' C_topologicalType 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc.      
         apply :  (absringrA h%:C).
          - by apply : absring_real_complex.
          - by rewrite eqCr .
  by [].
  have eqnear0y : {near (@locally' R_topologicalType 0), 'i \*:quotC  \o ( fun h => h *: 'i%C)  =1
                   quotiR }.
    exists 1 ; first by [] ; move => h _ _ //= ;  simpc . rewrite /quotC /quotiR (Im_mul h) invcM.   
    rewrite scalerA real_complex_inv Im_inv !scalecr; simpc ; rewrite (Im_mul h).
  by rewrite !real_complexE.
  pose subsetfiltersy := (flim_eq_loc eqnear0y).
  have <- : lim (quotiR  @ (@locally' R_topologicalType 0))
           = 'i * lim (quotC @ (@locally' C_topologicalType 0)).
    have -> : 'i * lim (quotC @ (@locally' C_topologicalType 0))
           =  lim ('i \*: quotC @ (@locally' C_topologicalType 0)). 
      rewrite  scalei_muli ; rewrite  (limin_scaler _ ('i) ).
       - by [].
       - exact : H.       
    apply :  (@flim_map_lim _ _ _ (@locally' R_topologicalType 0) _ _ (lim ('i \*:quotC @ (@locally' C_topologicalType 0) ))).
    suff :  quotiR @ (@locally' R_topologicalType 0)
                   `=>` ('i \*: quotC @ (@locally' C_topologicalType 0)).
      move => H1 ; apply : (flim_translim H1) .
      by apply :(@cvg_scaler _ _ _ _ _ quotC ('i) ) ; exact : H. 
    apply :  flim_trans.   
    - apply : (subsetfiltersy (@locally'_filter R_topologicalType  0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : flim_comp. 
       - exact  (@locally' C_topologicalType 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc. 
         apply :  (absringrA h*i).
          - by apply : absring_real_Im.
          - by rewrite eqCI.
      rewrite filter_of_filterE.
    by []. 
 by [].
Qed.


 Lemma Diff_CR_holo (f : C^o -> C^o) c:
   (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c) ->
   ((holomorphic f c)) . 
 Proof.
   move => [der CR] v.
   move : (der v); move => /cvg_ex {der} [l der].
    apply : (@cvgP _ _ _ l).
    move =>  //= A loclA.
    have lem :   locally ((fun h : R => h^-1 *: (complex_realfun f (h *: v + c) - complex_realfun f c))
                            @ (@locally' R_topologicalType 0)) A by exact : (der A loclA).  
    move : loclA ; move =>[r leq0r] absrA ;  exists r ; first by [].
     - move => [x y] ballrh neq0h //=.
       move : lem ;  move => //=. 
Admitted.
  
Theorem CauchyRiemann (f : C^o -> C^o) c:  ((holomorphic f c))
          <-> (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c). 
Proof.
Admitted.




End Holomorphe.
