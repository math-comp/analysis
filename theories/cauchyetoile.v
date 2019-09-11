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

(*Why is R_rcftype not implicit*)
Local Notation C := R[i].

Check 0 = 0 :> C.

Check (complex_ringType R_rcfType).
(*The fact that the above is canonical in complex.v is not exported ? *)
(* Re and Im are not the rpojections of complex, but belong to some numclosedfield. Why ?? *)
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


Check real_complex_additive.

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

Check complex_real.
 
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

(* C as a uniformtype *)
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

(*
Section C_as_R2.
(*C as a R-lmodule *)
Definition C_lmodMixin := (complex_lmodMixin R_rcfType).
(*LmodType is hard to use, not findable through Search and not checkable as abbreviation is not applied enough*)
Definition C_lmodType := @LmodType R_rcfType C C_lmodMixin.
Canonical C_lmodType. 
(* C as a R-normedmodule *)
(* Module NormedModule.

Record mixin_of (K : absRingType) (V : lmodType K) loc (m : @Uniform.mixin_of V loc) := Mixin {
  norm : V -> R ;
  ax1 : forall (x y : V), norm (x + y) <= norm x + norm y ;
  ax2 : forall (l : K) (x : V), norm (l *: x) = abs l * norm x;
  ax3 : Uniform.ball m = ball_ norm;
  ax4 : forall x : V, norm x = 0 -> x = 0
}.
 *)

(* We define its uniform structure as a product uniform structure *)
Print complex.


Definition C_rball (x : C) (eps : R) y :=
  ball (Re x) eps (Re y) /\ ball (Im x) eps (Im y).

Lemma C_rball_center x (eps : R) : 0 < eps -> C_rball x eps x.
Proof. by move => /posnumP[e]; split. Qed.

Lemma C_rball_sym x y (eps : R) : C_rball x eps y -> C_rball y eps x.
Proof. by move=> [bxy1 bxy2]; split; apply: ball_sym. Qed.

Lemma C_ball_triangle x y z (e1 e2 : R) :
  C_rball x e1 y -> C_rball y e2 z -> C_rball x (e1 + e2) z.
Proof.
by move=> [bxy1 bxy2] [byz1 byz2]; split; eapply ball_triangle; eassumption.
Qed.
Print Filtered.locally_op.
(* Filtered.locally_of = fun U T : Type => T -> set (set U)*)
Print locally_. 
(*locally_ = 
fun (T T' : Type) (ball : T -> R -> set T') (x : T) => filter_from [set x0 | 0 < x0] (ball x) *)

Lemma C_rlocally : locally =  locally_ C_rball. (*Before that we need a topological structure on C to infer locally from. *)
(*To complex, let us develop a more general theory in the section before *)
  (*More explicit about typing *)
Proof.
  (* I dont understand locally *)
rewrite predeq2E => -[x y] P .  split. rewrite /locally.  => [[[A B] /=[xX yY] XYP] |]. ; last first.
  by move=> [_ /posnumP[eps] epsP]; exists (ball x eps%:num, ball y eps%:num) => /=.
move: xX yY => /locallyP [_ /posnumP[ex] eX] /locallyP [_ /posnumP[ey] eY].
exists (minr ex%:num ey%:num) => // -[x' y'] [/= xx' yy'].
apply: XYP; split=> /=.
  by apply/eX/(ball_ler _ xx'); rewrite ler_minl lerr.
by apply/eY/(ball_ler _ yy'); rewrite ler_minl lerr orbT.
Qed.

Definition prod_uniformType_mixin :=
  Uniform.Mixin prod_ball_center prod_ball_sym prod_ball_triangle prod_locally.

(*Building a normed structure on C necessitates a Uniform structure which necessitates a topological structure *)
(*We go reverse and define induced uniform structure and toppological structure from normed structure *)

End C_as_R2. *)

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

About derivable.

Print locally'.
Definition holomorphic (f : Co_normedType -> Co_normedType) c := forall v,
cvg ((fun h => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' (0 : Co_normedType)).

Definition complex_realfun (f : C^o -> C^o) : C_RnormedType -> C_RnormedType := f.

Definition complex_Rnormed_absring : C_RnormedType -> C^o := id. (* Coercion ? *) (*Avec C tout seul au lieu de C_absRIng ça devrait passer *) 


(* Variable ( h : C_RnormedType -> C_RnormedType) (x : C_RnormedType).  *)

(* Check ('D_x h 0). (*This has a weird type *) *)
 
Definition CauchyRiemanEq (f : C_RnormedType -> C_RnormedType)  :=
  let u := (fun c => Re ( f c)): C_RnormedType -> R^o  in
  let v:= (fun c => Im (f c)) :  C_RnormedType -> R^o in
  ('D_(1%:C) u = 'D_('i) v) /\ ('D_('i) u = 'D_(1%:C) v).

Lemma eqCr (R : rcfType) (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.


(*Lemma lim_trans (T : topologicalType) (F : set (set T))  (G : set (set T)) (l : T) : ( F `=>` G ) -> (G --> l) -> ( F --> l). 
  move => FG Gl A x.
  Search "lim" "trans". 
 *)

Theorem CauchyRiemann (f : C^o -> C^o) c:  (holomorphic f c)
          <-> (forall v, derivable (complex_realfun f) c v) /\(CauchyRiemanEq f). 
Proof.
split.
- move => H ; split => v. 
  rewrite /derivable.
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
- move => //= A  [r [H1 H2]] ; exists r ; first by [].
  move => b ballrb neqb0.  
  have H4 : (AbsRing_ball 0%:C r b%:C). rewrite /AbsRing_ball /ball_ absCE.
   rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_r. 
   move : ballrb ; rewrite /AbsRing_ball /ball_ absRE.
   by rewrite addrC addr0 normrN. 
  have H5 : (b%:C != 0%:C) by move : neqb0 ; apply : contra ; rewrite eqCr.
  by apply : (H2 b%:C H4 H5).
by [].
- split.   
 -  
 -  admit.   
Admitted.




End Holomorphe.







Module real_integral (M: INTEGRAL). 
Import M.

Parameter borel_real : sigma_algebra R.
Definition R_measurable := Measurable.Pack  borel_real.
(* Notation AbsRingType T m := (@pack T _ m _ _ id _ id). *)
(* Canonical R_absRingType := AbsRingType R R_AbsRingMixin. *)
Canonical R_measurableType := @Measurable.Pack R borel_real. 


Inductive borel_top (T : topologicalType) : set (set T) :=
  | borel_open : forall A, open A -> borel_top  A
  | borel_union : forall ( F : nat -> set T ),
                 (forall n , borel_top (F n)) ->
                 borel_top ( \bigcup_n (F n))

  | borel_compl : forall A, borel_top (~`A) -> borel_top A.


Lemma borel_measurable : forall A : set R,  borel_top A ->  @measurable R_measurable A.
Admitted.

Variable lebesgue : set R -> Rbar. 


Record path (T : topologicalType) := Path {
  base : R -> T ;
  cont : forall x : R, `|x| <= 1 -> (base @ x --> base x ) }.

Check base. 
 (*Local Coercion base T : path T >-> (R -> T). J'arrive pas à faire une coercion *) 

Definition segment01 := fun (x : R) => is_true (`|x| <= 1 ).

Definition integral_path  (T : topologicalType) (p : path T) (f : T -> Rbar) := integral lebesgue  (segment01)  (Basics.compose f (base p)). 
  

End real_integral.