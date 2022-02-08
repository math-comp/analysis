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

Section Duals.

Variable (K : numFieldType).
  
  
Notation " E '`'" := (E -> K) (at level 10) .   

Variables (E F : tvsType K) (l l' : E`). 
Check (l + l'). 

End Duals.
