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


(* TBD after merge of lebesgue_measure *)

Section mem_set.
 Hint Resolve Prop_irrelevance : core.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
  
Coercion set_type T (A : set T) := {x : T | x \in A}.

Definition SigSub {T} {pT : predType T} {P : pT} x : x \in P -> {x | x \in P} :=
  exist (fun x => x \in P) x.

Lemma set0fun {P T : Type} : @set0 T -> P. Proof. by case=> x; rewrite inE. Qed.

Context {T : Type}. Implicit Type (A : set T).

Lemma mem_set {A} {u : T} : A u -> u \in A. Proof. by rewrite inE. Qed.
Lemma set_mem {A} {u : T} : u \in A -> A u. Proof. by rewrite inE. Qed.
Lemma mem_setT (u : T)    : u \in [set: T]. Proof. by rewrite inE. Qed.
Lemma mem_setK {A} {u : T} : cancel (@mem_set A u) set_mem.
Proof. by []. Qed.
Lemma set_memK {A} {u : T} : cancel (@set_mem A u) mem_set. Proof. by []. Qed. 
End mem_set.
(* End TBD *)

Section Linear3.
Context {R : comRingType} {U V : lmodType R} (s : R -> V -> V)
        (s_law : GRing.Scale.law s).


Section linear_pred.
  
Definition linear_pred : {pred U -> V} := mem [set f | lmorphism_for (GRing.Scale.op s_law) f].
(* Definition linear_pred : {pred U -> V} := mem [set f | linear f].   *)
(* Fails [set f | linear f] f does not reduce to lmorphism_for s f *)
Definition linear_key : pred_key linear_pred.
Proof. exact. Qed.

Canonical linear_keyed := KeyedPred linear_key.
End linear_pred.


Section Sub.
Context (f : U -> V) (fP : f \in linear_pred).
Definition linear_sub_subproof := @Linear (set_mem fP).
Canonical linear_sub_subproof.
Definition linear_Sub := [linear of f].
End Sub.

Lemma linear_rect (K : {linear U -> V |(GRing.Scale.op s_law) } -> Type) :
  (forall f (Pf : f \in linear_pred), K (linear_Sub Pf))
  -> forall f : {linear U -> V | (GRing.Scale.op s_law)} , K f.
Proof.
move=> Ksub [f c]. 
suff -> : c = (set_mem (@mem_set _ [set f | _] f c)) by apply: Ksub.
by rewrite mem_setK. 
Qed.

Lemma linear_valP f (Pf : f \in linear_pred) : linear_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

Canonical linear_subType :=
  SubType {linear U -> V | (GRing.Scale.op s_law)} _ _  linear_rect linear_valP.


Lemma lineareqP (f g : {linear U -> V | (GRing.Scale.op s_law)}) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.


(* NB : delete the redundant definitions at the end of topology *)
Definition lineareqMixin :=
  [eqMixin of {linear U -> V | (GRing.Scale.op s_law)} by <:].
Canonical lineareqType :=
  EqType {linear U -> V | (GRing.Scale.op s_law)} lineareqMixin.
Definition linearchoiceMixin :=
  [choiceMixin of {linear U -> V | (GRing.Scale.op s_law)} by <:].
Canonical linearchoiceType :=
  ChoiceType {linear U -> V | (GRing.Scale.op s_law)} linearchoiceMixin.
(* End NB *)


Section lmod.

(* TBD when mathcomp_extra is merged *)
Reserved Notation "f \* g" (at level 40, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f"  (at level 35, f at level 35).
Reserved Notation "f \max g" (at level 50, left associativity).

Definition opp_fun T (R : zmodType) (f : T -> R) x := (- f x)%R.
Notation "\- f" := (opp_fun f) : ring_scope . 
Arguments opp_fun {T R} _ _ /.

Definition mul_fun T (R : ringType) (f g : T -> R) x := (f x * g x)%R.
Notation "f \* g" := (mul_fun f g) : ring_scope.
Arguments mul_fun {T R} _ _ _ /.
(* End TBD *)


(* Lemma linear_zmod_closed : zmod_closed linear_pred. *)
(* Proof. *)
(*   split=> [|f g]; rewrite !inE/=; split. *)
(*   - apply: GRing.null_fun_is_additive. *)
(*   - apply: GRing.null_fun_is_scalable. *)
(*   - move => a b /=.   admit.  *)
(*   - move=> k a /=.  admit.  *)
(* Admitted. *)

Lemma linear_lmod_closed : submod_closed linear_pred.
Proof.
  split=> [|t g]; rewrite !inE/=. split.
  - apply: GRing.null_fun_is_additive.
  - apply: GRing.null_fun_is_scalable.
  - move=> h [Ag Sg] /set_mem [Ah Sh]; apply/mem_set => /=; split.
    * move => a b. rewrite [_ + _]/(_ \+ _) [_ *: _]/(_ \*: _) /=.
      by rewrite Ag Ah scalerBr addrACA opprD. 
    * rewrite [_ + _]/(_ \+ _) [_ *: _]/(_ \*: _) => r u. 
      rewrite Sg Sh /= /GRing.Scale.op. (*argh*)
Admitted.


Canonical linear_add := AddrPred linear_lmod_closed.
Canonical linear_zmod := ZmodPred linear_lmod_closed.
Definition linear_zmodMixin :=
  [zmodMixin of {linear U -> V | (GRing.Scale.op s_law)} by <:].
Canonical linear_zmodType :=
  ZmodType {linear U -> V | (GRing.Scale.op s_law)} linear_zmodMixin.

Canonical linear_lmod := SubmodPred linear_lmod_closed.
Definition linear_lmodMixin :=
  [lmodMixin of {linear U -> V | (GRing.Scale.op s_law)} by <:].
Canonical linear_lmodType :=
  LmodType R {linear U -> V | (GRing.Scale.op s_law)} linear_lmodMixin.

Implicit Types (f g : {linear U -> V |GRing.Scale.op s_law }).

Lemma linfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma linfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma linfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma linfun0 : (0 : {linear U -> V | GRing.Scale.op s_law}) = cst 0 :> (_ -> _).
Proof. by []. Qed.

Lemma linfun_sum I r (P : {pred I}) (f : I -> {linear U -> V | GRing.Scale.op s_law}) (x : U) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

(* Definition linfunD_copy f g := copy (f \+ g) (f + g). *)
(* Canonical linfunD_copy. *)
(* Definition linfunN_copy f g := copy (\- f) (- f). *)
(* Definition linfunB_copy f g := copy (f \- g) (f - g). *)
End lmod.
End Linear3.

Module zmodbyhand.
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

Lemma linfun_eqP: forall  (f g : {linear U ->  V}),
  f = g <-> f =1 g.
Proof. move=> [f Lf] [g Lg]; split=> [->//|fg].  Admitted.  


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
End zmodbyhand.
(* Section scalar. *)
(* Context {K : numFieldType} {U : lmodType K}. *)
  
(* Definition scalar_zmodMixin := @linear_zmodMixin K U K^o.  *)
(* Canonical scalar_zmodType := ZmodType {scalar U} (scalar_zmodMixin).  *)
(* End scalar. *)

Section Duals.

Variable (K : numFieldType).

Notation " E '`'" := {linear E -> K^o} (at level 10) .
(* Notation " E '`'" := {scalar E} (at level 10) .    *)

Variable (E : tvsType K) (l l' : E`). 
Check (l + l'). 

End Duals.
