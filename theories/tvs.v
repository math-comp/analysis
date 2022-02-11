(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice div.
From mathcomp Require Import seq fintype bigop order interval ssralg ssrnum rat.
From mathcomp Require Import matrix finmap.
Require Import boolp reals classical_sets posnum topology.


(* Duality theory in topological vector spaces. Goal is to prove
Mackey-arens theorem and charaterization of reflexive spaces in terms
of barrelledness and weak quasi-completeness, and then move on to
distribution theory. Results at on pseudometric spaces at the end of
topology.v will need to me moved at the end of tvs.v, and pseudometric
will depend on tvs. *)

(* TODO : move here the canconical topological structure on K from K^o *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Context (R : numFieldType) (U : lmodType R) (V : lmodType R).
Variables (f g : U -> V ). 
Check (f + g).
Fail Check (l + l'). 

Module Tvs.


Record mixin_of   (K :  numFieldType) (T : lmodType K)
                (nbhsT : T -> set (set T))
                (m : Uniform.mixin_of nbhsT):=   Mixin {
        add_cont : forall x,  cvg_to ((fun y : T * T => (y.1 + y.2)) @ (filter_prod (nbhsT x.1) (nbhsT x.2))) (nbhsT (x.1 + x.2))  ;
        scale_cont : forall kx, cvg_to ((fun kx : K^o * T =>  kx.1 *: kx.2) @  (filter_prod (nbhs kx.1) (nbhsT kx.2))) (nbhsT (kx.1 *: kx.2));
        ax : forall P,  ((Uniform.entourage m P) <-> (exists z, exists V, nbhsT z V  /\ ( P = [set xy | V (xy.1 - xy.2) ])))  } . 
  
Section ClassDef.
Variable K: numFieldType.

(* add locally convex immediatly ?  *)
 

Record class_of  (T : Type) := Class {
    base : GRing.Lmodule.class_of K T ;    
    pointed_mixin : Pointed.point_of T ;
    nbhs_mixin : Filtered.nbhs_of T T ;
    topological_mixin : @Topological.mixin_of T nbhs_mixin ;
    uniform_mixin : @Uniform.mixin_of T nbhs_mixin;
    mixin : @mixin_of K (GRing.Lmodule.Pack (Phant K) base) _ uniform_mixin } . 

Local Coercion base : class_of >-> GRing.Lmodule.class_of.
(*why do we need base2 ? *)

Definition base2 T c := @Uniform.Class _
      (@Topological.Class _
        (Filtered.Class
         (Pointed.Class (@base T c) (pointed_mixin c))
         (nbhs_mixin c))
        (topological_mixin c))
      (uniform_mixin c) .

Local Coercion base2 : class_of >-> Uniform.class_of.


Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack phK  c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Local Coercion mixin : class_of >-> mixin_of.

Definition pack  (b0 : GRing.Lmodule.class_of K T) nbhsT um0
  (m0 : @mixin_of K (@GRing.Lmodule.Pack K (Phant K) T b0) nbhsT um0) := 
  fun bT (b : GRing.Lmodule.class_of K T)
      & phant_id (@GRing.Lmodule.class K (Phant K) bT) b =>
  fun uT (u : Uniform.class_of T) & phant_id (@Uniform.class uT) u =>
  fun (m : @mixin_of K (GRing.Lmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phK T (@Class T b u u u u m).


Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass. 
Definition uniformType := @Uniform.Pack cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition uniform_zmodType := @GRing.Zmodule.Pack uniformType xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition uniform_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass.


End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical uniform_zmodType.

Notation tvsType K := (type (Phant K)).
Notation TvsType T m := (@pack _ T _ m _ _ idfun _ idfun).
Notation TvsMixin := Mixin.
Notation "[ 'tvsType' K 'of' T 'for' cT ]" := (@clone K T cT _ idfun)
  (at level 0, format "[ 'tvsType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'tvsType' K 'of' T ]" := (@clone K T _ _ id)
  (at level 0, format "[ 'tvsType'  K  'of'  T ]") : form_scope.

End Exports.

End Tvs.

Export Tvs.Exports.

Section Linear3.
Context {R : comRingType} {U V : lmodType R}.

(* Section linear_pred. *)
(* Definition linear_pred : {pred U -> V} := mem [set f | linear f]. *)
(* Definition linear_key : pred_key linear_pred. *)
(* Proof. exact. Qed. *)

(* Canonical linear_keyed := KeyedPred linear_key. *)
(* End linear_pred. *)


(* Section Sub. *)
(* Context (f : U -> V) (fP : f \in linear_pred). *)

(* Definition linear_sub_subproof := Linear fP. *)
(* Canonical linear_sub_subproof. *)

(* Definition linear_Sub := [linear of f]. *)
(* End Sub. *)

(* Lemma linear_rect (K : {linear U -> V} -> Type) : *)
(*   (forall f (Pf : f \in linear_red), K (linear_Sub Pf)) -> forall f : { linear U -> V} , K f. *)
(* Proof. *)
(* move=> Ksub f.   [f [[Pf]]]/=. *)
(* by suff -> : Pf = (set_mem (@mem_set _ [set f | _] f Pf)) by apply: Ksub. *)
(* Qed. *)

(* Lemma fimfun_valP f (Pf : f \in fimfun) : fimfun_Sub Pf = f :> (_ -> _). *)
(* Proof. by []. Qed. *)

(* Canonical fimfun_subType := SubType T _ _ fimfun_rect fimfun_valP. *)
(* End fimfun. *)

(* Lemma fimfuneqP aT rT (f g : {fimfun aT >-> rT}) : *)
(*   f = g <-> f =1 g. *)
(* Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed. *)

(* Definition fimfuneqMixin aT (rT : eqType) := *)
(*   [eqMixin of {fimfun aT >-> rT} by <:]. *)
(* Canonical fimfuneqType aT (rT : eqType) := *)
(*   EqType {fimfun aT >-> rT} (fimfuneqMixin aT rT). *)
(* Definition fimfunchoiceMixin aT (rT : choiceType) := *)
(*   [choiceMixin of {fimfun aT >-> rT} by <:]. *)
(* Canonical fimfunchoiceType aT (rT : choiceType) := *)
(*   ChoiceType {fimfun aT >-> rT} (fimfunchoiceMixin aT rT). *)

(* Lemma finite_image_cst {aT rT : Type} (x : rT) : finite_set [set of cst x : aT -> rT]. *)
(* Proof. *)
(* elim/Ppointed: aT => aT; rewrite ?emptyE ?image_set0//. *)
(* suff -> : cst x @` [set: aT] = [set x] by apply: finite_set1. *)
(* by apply/predeqP => y; split=> [[t' _ <-]//|->//] /=; exists point. *)
(* Qed. *)

(* Definition fun_cmul {U : Type} {R : ringType} (k : R) (f : U -> R) x := k * f x. *)
(* Notation "k *\ f" := (fun_cmul k f) (at level 40, format "k  *\  f") : ring_scope. *)

(* Lemma cst_fimfun_subproof aT rT x : @FiniteImage aT rT (cst x). *)
(* Proof. by split; exact: finite_image_cst. Qed. *)
(* HB.instance Definition _ aT rT x := @cst_fimfun_subproof aT rT x. *)
(* Definition cst_fimfun {aT rT} x := [the {fimfun aT >-> rT} of cst x]. *)

(* Lemma fimfun_cst aT rT x : @cst_fimfun aT rT x =1 cst x. Proof. by []. Qed. *)

(* Lemma comp_fimfun_subproof aT rT sT *)
(*    (f : {fimfun aT >-> rT}) (g : rT -> sT) : @FiniteImage aT sT (g \o f). *)
(* Proof. by split; rewrite -(image_comp f g); apply: finite_image. Qed. *)
(* HB.instance Definition _ aT rT sT f g := @comp_fimfun_subproof aT rT sT f g. *)

(* Section zmod. *)
(* Context (aT : Type) (rT : zmodType). *)
(* Lemma fimfun_zmod_closed : zmod_closed (@fimfun aT rT). *)
(* Proof. *)
(* split=> [|f g]; rewrite !inE/=; first exact: finite_image_cst. *)
(* by move=> fA gA; apply: (finite_image11 (fun x y => x - y)). *)
(* Qed. *)
(* Canonical fimfun_add := AddrPred fimfun_zmod_closed. *)
(* Canonical fimfun_zmod := ZmodPred fimfun_zmod_closed. *)
(* Definition fimfun_zmodMixin := [zmodMixin of {fimfun aT >-> rT} by <:]. *)
(* Canonical fimfun_zmodType := ZmodType {fimfun aT >-> rT} fimfun_zmodMixin. *)

(* Implicit Types (f g : {fimfun aT >-> rT}). *)

(* Lemma fimfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed. *)
(* Lemma fimfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed. *)
(* Lemma fimfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed. *)
(* Lemma fimfun0 : (0 : {fimfun aT >-> rT}) = cst 0 :> (_ -> _). Proof. by []. Qed. *)
(* Lemma fimfun_sum I r (P : {pred I}) (f : I -> {fimfun aT >-> rT}) (x : aT) : *)
(*   (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x. *)
(* Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed. *)

(* HB.instance Definition _ f g := FImFun.copy (f \+ g) (f + g). *)
(* HB.instance Definition _ f g := FImFun.copy (\- f) (- f). *)
(* HB.instance Definition _ f g := FImFun.copy (f \- g) (f - g). *)
(* End zmod. *)

(* Context (R : comRingType) (U : lmodType R) (V : lmodType R). *)

Lemma opp_fun_additive (l : {linear U -> V}) : additive  (fun x => (- (l x))).
by move => x y //=; rewrite linearB opprD.   
Qed.

Lemma opp_fun_linear (l : {linear U -> V}):  linear (fun x => - (l x)).
Proof.
by move => t u v; rewrite linearP opprD scalerN.
Qed. 


Lemma add_fun_linear (l l' : {linear U -> V}):  linear (l \+ l').
Proof.
by  move => t u v; rewrite linearP. 
Qed.


Lemma linfun_eqP  (f g : {linear U ->  V}) :
  f = g <-> f =1 g.
Proof. split=> [->//|fg].  Admitted.  



Program Definition linear_zmodMixin := 
  @ZmodMixin {linear U -> V} (@GRing.null_fun_linear R U V _ _)
             (fun l => Linear (opp_fun_linear l)) (fun f g =>  Linear (add_fun_linear f g)) _ _ _ _. 
Next Obligation. by move=> f g h; apply/linfun_eqP => x /=; rewrite addrA. Qed. 
Next Obligation. by move=> f g; apply/linfun_eqP => x /=; rewrite addrC. Qed.
Next Obligation. by move => f; apply/linfun_eqP => x /=; rewrite add0r. Qed. 
Next Obligation. by move => f; apply/linfun_eqP => x /=; rewrite addNr. Qed. 
Canonical linear_zmodType := ZmodType {linear U -> V} (linear_zmodMixin).

Lemma scale_fun_linear (r : R) (l : {linear U -> V}) : linear ( fun x => r *: l x).
Proof.
by move => t u v; rewrite linearP scalerDr scalerA scalerA mulrC.
Qed.     

Program Definition linear_lmodMixin
  := @LmodMixin R [zmodType of {linear U -> V}] (fun k f => Linear (scale_fun_linear k  f)) _ _ _ _.
Next Obligation. by move=> a b l /=; apply/linfun_eqP => x /=; rewrite scalerA. Qed.
Next Obligation. by move => l; apply/linfun_eqP => x /=; rewrite scale1r. Qed. 
Next Obligation. by  move => l f g; apply/linfun_eqP => x /=; rewrite scalerDr. Qed.
Next Obligation. by move => l a b; apply/linfun_eqP => x /=; rewrite scalerDl. Qed.


Canonical linear_lmodType  :=
  LmodType _ {linear U -> V} (linear_lmodMixin).

Lemma linear_sumE  n (f : 'I_n -> {linear U -> V}) (x : U) :
  (\sum_(i < n) f i) x = \sum_(i < n) f i x.
Proof.
elim: n f => [|n H] f;
  by rewrite !(big_ord0,big_ord_recr) //= -[LHS]/(_ x + _ x) H.
Qed.


(*TODO : do the same for scalar *)
(* TODO : do it by subtyping *)
End Linear3.

Section Duals.

Variable (K : numFieldType).

Notation " E '`'" := {linear E -> K^o} (at level 10) .   

Variable (E : tvsType K) (l l' : E`). 
Check (l + l'). 
End Duals.
