(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From HB Require Import structures.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
Add Search Blacklist "__canonical__".
Add Search Blacklist "__functions_".
Add Search Blacklist "_factory_".
Add Search Blacklist "_mixin_".

(**md**************************************************************************)
(* # Theory of functions                                                      *)
(*                                                                            *)
(* This file provides a theory of functions $f : A\to B$ whose domain $A$     *)
(* and codomain $B$ are represented by sets.                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*          set_fun A B f == f : aT -> rT is a function with domain           *)
(*                           A : set aT and codomain B : set rT               *)
(*         set_surj A B f == f is surjective                                  *)
(*          set_inj A B f == f is injective                                   *)
(*          set_bij A B f == f is bijective                                   *)
(*                                                                            *)
(*          {fun A >-> B} == type of functions f : aT -> rT from A : set aT   *)
(*                           to B : set rT                                    *)
(*                           `funS f` is a proof of `set_fun A B f`.          *)
(*       {oinv aT >-> rT} == type of functions with a partial inverse         *)
(*      {oinvfun A >-> B} == combination of {fun A >-> B} and                 *)
(*                           {oinv aT >-> rT}                                 *)
(*        {inv aT >-> rT} == type of functions with an inverse                *)
(*                  f ^-1 == inverse of f : {inv aT >-> rT}                   *)
(*       {invfun A >-> B} == combination of {fun A >-> B} and {inv aT >-> rT} *)
(*         {surj A >-> B} == type of surjective functions                     *)
(*      {surjfun A >-> B} == combination of {fun A >-> B} and {surj A >-> B}  *)
(*    {splitsurj A >-> B} == type of surjective functions with an inverse     *)
(* {splitsurjfun A >-> B} == combination of {fun A >-> B} and                 *)
(*                           {splitsurj A >-> B}                              *)
(*         {inj A >-> rT} == type of injective functions                      *)
(*       {injfun A >-> B} == combination of {fun A >-> B} and {inj A >-> rT}  *)
(*     {splitinj A >-> B} == type of injective functions with an inverse      *)
(*  {splitinjfun A >-> B} == combination of {fun A >-> B} and                 *)
(*                           {splitinj A >-> B}                               *)
(*          {bij A >-> B} == combination of {injfun A >-> B} and              *)
(*                           {surjfun A >-> B}                                *)
(*     {splitbij A >-> B} == combination of {splitinj A >-> B} and            *)
(*                           {splitsurj A >-> B}                              *)
(*                'inj_ f == proof of {in A &, injective f} where f has type  *)
(*                           {splitinj A >-> _}                               *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*           [fun f in A] == the function f from the set A to the set f @` A  *)
(*                           with f : aT -> rT and A : set aT                 *)
(*                           This is a notation for funin A f, which is an HB *)
(*                           alias.                                           *)
(*            'split_ d f == partial injection from aT : Type to rT : Type,   *)
(*                           f : aT -> rT, and d : rT -> aT                   *)
(*                           This is a notation for split_ d f which is an HB *)
(*                           alias.                                           *)
(*                  split := 'split_(fun=> point)                             *)
(*             @to_setT T == function that associates to x : T a dependent    *)
(*                           pair of x with a proof that x belongs to setT    *)
(*                           (i.e., the type set_type [set: T])               *)
(*                incl AB == identity function from T to T, where AB is a     *)
(*                           proof of A `<=` B, with A, B : set T             *)
(*                inclT A := incl (@subsetT _ _)                              *)
(*              eqincl AB == identity function from T to T, where AB is a     *)
(*                           proof of A = B, with A, B : set T                *)
(*              mkfun fAB == builds a function {fun A >-> B} given a function *)
(*                           f : aT -> rT and a proof fAB that                *)
(*                           {homo f : x / A x >-> B x}                       *)
(*           @set_val T A == injection from set_type A to T, where A has      *)
(*                           type set T                                       *)
(*             @ssquash T == function of type                                 *)
(*                           {splitsurj [set: T] >-> [set: $| T |]}           *)
(*        @finset_val T X == function that turns an element x : X             *)
(*                           (with X : {fset T}) into a dependent pair of x   *)
(*                           with a proof that x belongs to X                 *)
(*                           (i.e., the type set_type [set` X])               *)
(*        @val_finset T X == function of type [set` X] -> X with X : {fset T} *)
(*                           that cancels finset_val                          *)
(*         glue XY AB f g == function that behaves as f over X, as g over Y   *)
(*                           XY is a proof that sets X and Y are disjoint,    *)
(*                           AB is a proof that sets A and B are disjoint,    *)
(*                           A and B are intended to be the ranges of f and g *)
(*           'pinv_ d A f == inverse of the function [fun f in A] over        *)
(*                           f @` A, function d outside of f @` A             *)
(*                           This is a notation for pinv_ which is defined as *)
(*                           the inverse of a partial injection ('split_).    *)
(*                   pinv := 'pinv_(fun=> point)                              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Function restriction                                                    *)
(* ```                                                                        *)
(*            patch d A f == "partial function" that behaves as the function  *)
(*                           f over the set A and as the function d otherwise *)
(*           restrict D f := patch (fun=> point) D f                          *)
(*                 f \_ D := restrict D f                                     *)
(*               sigL A f == "left restriction"; given a set A : set U and a  *)
(*                           function f : U -> V, returns the corresponding   *)
(*                           function of type set_type A -> V                 *)
(*               sigR A f == "right restriction"; given a set B : set V and a *)
(*                           function f : {fun [set: U] >-> B}, returns the   *)
(*                           corresponding function of type U -> set_type B   *)
(*            sigLR A B f == the function of type set_type A -> set_type B    *)
(*                           corresponding to f : {fun A >-> B}               *)
(*                valL_ v == function cancelled by sigL A, with A : set U and *)
(*                           v : V                                            *)
(*                 valR f == the function of type U -> V corresponding to     *)
(*                           f : U -> set_type B, with B : set V              *)
(*               valR_fun == the function of type {fun [set: U] >-> B}        *)
(*                           corresponding to f : U -> set_type B, with       *)
(*                           B : set V                                        *)
(*              valLR v f == the function of type U -> V corresponding to     *)
(*                           f : set_type A -> set_type B (where v : V),      *)
(*                           i.e., 'valL_ v \o valR_fun                       *)
(*       valLfun_ v A B f := [fun of valL_ f] with f : {fun [set: A] >-> B}   *)
(*                   valL := 'valL_ point                                     *)
(*             valLRfun v := 'valLfun_ v \o valR_fun                          *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(* Section function_space == canonical ringType and lmodType                  *)
(*                           structures for functions whose range is          *)
(*                           a ringType, comRingType, or lmodType.            *)
(*                   fctE == multi-rule for fct                               *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \_ D" (at level 10).
Reserved Notation "'{' 'fun' A '>->' B '}'"
  (format "'{' 'fun'  A  '>->'  B '}'").
Reserved Notation "'{' 'oinv' T '>->' U '}'"
  (format "'{' 'oinv'  T  '>->'  U '}'").
Reserved Notation "'{' 'inv' T '>->' U '}'"
  (format "'{' 'inv'  T  '>->'  U '}'").
Reserved Notation "'{' 'oinvfun' T '>->' U '}'"
  (format "'{' 'oinvfun'  T  '>->'  U '}'").
Reserved Notation "'{' 'invfun' T '>->' U '}'"
  (format "'{' 'invfun'  T  '>->'  U '}'").
Reserved Notation "'{' 'inj' A '>->' T '}'"
  (format "'{' 'inj'  A  '>->'  T '}'").
Reserved Notation "'{' 'splitinj' A '>->' T '}'"
  (format "'{' 'splitinj'  A  '>->'  T '}'").
Reserved Notation "'{' 'surj' A '>->' B '}'"
  (format "'{' 'surj'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitsurj' A '>->' B '}'"
  (format "'{' 'splitsurj'  A  '>->'  B '}'").
Reserved Notation "'{' 'injfun' A '>->' B '}'"
  (format "'{' 'injfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'surjfun' A '>->' B '}'"
  (format "'{' 'surjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitinjfun' A '>->' B '}'"
  (format "'{' 'splitinjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitsurjfun' A '>->' B '}'"
  (format "'{' 'splitsurjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'bij' A '>->' B '}'"
  (format "'{' 'bij'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitbij' A '>->' B '}'"
  (format "'{' 'splitbij'  A  '>->'  B '}'").

Reserved Notation "[ 'fun' 'of' f ]" (format "[ 'fun'  'of'  f ]").
Reserved Notation "[ 'oinv' 'of' f ]" (format "[ 'oinv'  'of'  f ]").
Reserved Notation "[ 'inv' 'of' f ]" (format "[ 'inv'  'of'  f ]").
Reserved Notation "[ 'oinv' 'of' f ]" (format "[ 'oinv'  'of'  f ]").
Reserved Notation "[ 'inv' 'of' f ]" (format "[ 'inv'  'of'  f ]").
Reserved Notation "[ 'inj' 'of' f ]" (format "[ 'inj'  'of'  f ]").
Reserved Notation "[ 'splitinj' 'of' f ]" (format "[ 'splitinj'  'of'  f ]").
Reserved Notation "[ 'surj' 'of' f ]" (format "[ 'surj'  'of'  f ]").
Reserved Notation "[ 'splitsurj' 'of' f ]" (format "[ 'splitsurj'  'of'  f ]").
Reserved Notation "[ 'injfun' 'of' f ]" (format "[ 'injfun'  'of'  f ]").
Reserved Notation "[ 'surjfun' 'of' f ]" (format "[ 'surjfun'  'of'  f ]").
Reserved Notation "[ 'splitinjfun' 'of' f ]"
  (format "[ 'splitinjfun'  'of'  f ]").
Reserved Notation "[ 'splitsurjfun' 'of' f ]"
  (format "[ 'splitsurjfun'  'of'  f ]").
Reserved Notation "[ 'bij' 'of' f ]" (format "[ 'bij'  'of'  f ]").
Reserved Notation "[ 'splitbij' 'of' f ]" (format "[ 'splitbij'  'of'  f ]").

Reserved Notation "''oinv_' f" (at level 8, f at level 2, format "''oinv_' f").
Reserved Notation "''funS_' f" (at level 8, f at level 2, format "''funS_' f").
Reserved Notation "''mem_fun_' f"
  (at level 8, f at level 2, format  "''mem_fun_' f").
Reserved Notation "''oinvK_' f"
  (at level 8, f at level 2, format "''oinvK_' f").
Reserved Notation "''oinvS_' f"
  (at level 8, f at level 2, format "''oinvS_' f").
Reserved Notation "''oinvP_' f"
  (at level 8, f at level 2, format "''oinvP_' f").
Reserved Notation "''oinvT_' f"
  (at level 8, f at level 2, format "''oinvT_' f").
Reserved Notation "''invK_' f"
  (at level 8, f at level 2, format "''invK_' f").
Reserved Notation "''invS_' f"
  (at level 8, f at level 2, format "''invS_' f").
Reserved Notation "''funoK_' f"
  (at level 8, f at level 2, format "''funoK_' f").
Reserved Notation "''inj_' f"
  (at level 8, f at level 2, format "''inj_' f").
Reserved Notation "''funK_' f"
  (at level 8, f at level 2, format "''funK_' f").
Reserved Notation "''totalfun_' A"
  (at level 8, A at level 2, format "''totalfun_' A").
Reserved Notation "''surj_' f"
  (at level 8, f at level 2, format "''surj_' f").
Reserved Notation "''split_' a"
  (at level 8, a at level 2, format "''split_' a").
Reserved Notation "''bijTT_'  f"
  (at level 8, f at level 2, format "''bijTT_' f").
Reserved Notation "''bij_' f" (at level 8, f at level 2, format "''bij_' f").
Reserved Notation "''valL_' v" (at level 8, v at level 2, format "''valL_' v").
Reserved Notation "''valLfun_' v"
  (at level 8, v at level 2, format "''valLfun_' v").
Reserved Notation "''pinv_' dflt"
  (at level 8, dflt at level 2, format "''pinv_' dflt").
Reserved Notation "''pPbij_' dflt"
  (at level 8, dflt at level 2, format "''pPbij_' dflt").
Reserved Notation "''pPinj_' dflt"
  (at level 8, dflt at level 2, format "''pPinj_' dflt").
Reserved Notation "''injpPfun_' dflt"
  (at level 8, dflt at level 2, format "''injpPfun_' dflt").
Reserved Notation "''funpPinj_' dflt"
  (at level 8, dflt at level 2, format "''funpPinj_' dflt").

Local Open Scope classical_set_scope.

Section MainProperties.
Context {aT rT}  (A : set aT) (B : set rT) (f : aT -> rT).
Definition set_fun := {homo f : x / A x >-> B x}.
Definition set_surj := B `<=` f @` A.
Definition set_inj := {in A &, injective f}.
Definition set_bij := [/\ set_fun, set_inj & set_surj].
End MainProperties.

HB.mixin Record isFun {aT rT} (A : set aT) (B : set rT) (f : aT -> rT) :=
  { funS : set_fun A B f }.
HB.structure Definition Fun {aT rT} (A : set aT) (B : set rT) :=
  { f of isFun _ _ A B f }.
Notation "{ 'fun' A >-> B }" := (@Fun.type _ _ A B) : form_scope.
Notation "[ 'fun'  'of'  f ]" := [the {fun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv {aT rT} (f : aT -> rT) := { oinv : rT -> option aT }.
HB.structure Definition OInversible aT rT := {f of OInv aT rT f}.
Notation "{ 'oinv' aT >-> rT }" := (@OInversible.type aT rT) : type_scope.
Notation "[ 'oinv'  'of'  f ]" := [the {oinv _ >-> _} of f : _ -> _] :
  form_scope.
Definition phant_oinv aT rT (f : {oinv aT >-> rT})
  of phantom (_ -> _) f := @oinv _ _ f.
Notation "''oinv_' f" := (@phant_oinv _ _ _ (Phantom (_ -> _) f%FUN)).

HB.structure Definition OInvFun aT rT A B :=
  {f of OInv aT rT f & isFun aT rT A B f}.
Notation "{ 'oinvfun' A >-> B }" := (@OInvFun.type _ _ A B) : type_scope.
Notation "[ 'oinvfun'  'of'  f ]" :=
  [the {oinvfun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv_Inv {aT rT} (f : aT -> rT) of OInv _ _ f := {
  inv : rT -> aT;
  oliftV : olift inv = 'oinv_f
}.

HB.factory Record Inv {aT rT} (f : aT -> rT) := { inv : rT -> aT  }.
HB.builders Context {aT rT} (f : aT -> rT) of Inv _ _ f.
  HB.instance Definition _ := OInv.Build _ _ f (olift inv).
  HB.instance Definition _ := OInv_Inv.Build _ _ f erefl.
HB.end.

HB.structure Definition Inversible aT rT := {f of Inv aT rT f}.
Notation "{ 'inv' aT >->  rT }" := (@Inversible.type aT rT) : type_scope.
Notation "[ 'inv'  'of'  f ]" := [the {inv _ >-> _} of f : _ -> _] : form_scope.
Definition phant_inv aT rT (f : {inv aT >-> rT}) of phantom (_ -> _) f :=
  @inv _ _ f.
Notation "f ^-1" := (@inv _ _ f%function) (only printing) : function_scope.
Notation "f ^-1" :=
  (@phant_inv _ _ _ (Phantom (_ -> _) f%function)) : function_scope.
(* TODO: remove the following notations in fun_scope *)
Notation "f ^-1" := (@inv _ _ f%FUN) (only printing) : fun_scope.
Notation "f ^-1" := (@phant_inv _ _ _ (Phantom (_ -> _) f%FUN)) : fun_scope.

HB.structure Definition InvFun aT rT A B :=
  {f of Inv aT rT f & isFun aT rT A B f}.
Notation "{ 'invfun' A >-> B }" := (@InvFun.type _ _ A B) : type_scope.
Notation "[ 'invfun'  'of'  f ]" :=
  [the {invfun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv_CanV {aT rT} {A : set aT} {B : set rT}
  (f : aT -> rT) of OInv _ _ f := {
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    oinvK : {in B, ocancel 'oinv_f f};
  }.

HB.factory Record OCanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) := {
    oinv; oinvS : {homo oinv : x / B x >-> (some @` A) x};
          oinvK : {in B, ocancel oinv f};
  }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
   of OCanV _ _ A B f.
 HB.instance Definition _ := OInv.Build _ _ f oinv.
 HB.instance Definition _ := OInv_CanV.Build _ _ A B f oinvS oinvK.
HB.end.

HB.structure Definition Surject {aT rT A B} := {f of @OCanV aT rT A B f}.
Notation "{ 'surj' A >-> B }" := (@Surject.type _ _ A B) : type_scope.
Notation "[ 'surj'  'of'  f ]" :=
  [the {surj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SurjFun aT rT A B :=
  {f of @Surject aT rT A B f & @Fun _ _ A B f}.
Notation "{ 'surjfun' A >-> B }" := (@SurjFun.type _ _ A B) : type_scope.
Notation "[ 'surjfun'  'of'  f ]" :=
  [the {surjfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitSurj aT rT A B :=
  {f of @Surject aT rT A B f & @Inv _ _ f}.
Notation "{ 'splitsurj' A >-> B }" := (@SplitSurj.type _ _ A B) : type_scope.
Notation "[ 'splitsurj'  'of'  f ]" :=
  [the {splitsurj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitSurjFun aT rT A B :=
   {f of @SplitSurj aT rT A B f & @Fun _ _ A B f}.
Notation "{ 'splitsurjfun' A >-> B }" :=
  (@SplitSurjFun.type _ _ A B) : type_scope.
Notation "[ 'splitsurjfun'  'of'  f ]" :=
  [the {splitsurjfun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv_Can aT rT (A : set aT) (f : aT -> rT) of OInv _ _ f :=
  { funoK : {in A, pcancel f 'oinv_f} }.

HB.structure Definition Inject aT rT A :=
  {f of OInv aT rT f & OInv_Can aT rT A f}.
Notation "{ 'inj' A >-> rT }" := (@Inject.type _ rT A) : type_scope.
Notation "[ 'inj'  'of'  f ]" := [the {inj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition InjFun {aT rT} (A : set aT) (B : set rT) :=
   { f of @Fun _ _ A B f & @Inject _ _ A f }.
Notation "{ 'injfun' A >-> B }" := (@InjFun.type _ _ A B) : type_scope.
Notation "[ 'injfun'  'of'  f ]" :=
  [the {injfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitInj aT rT (A : set aT) :=
  {f of @Inv aT rT f & @Inject aT rT A f}.
Notation "{ 'splitinj' A >-> rT }" := (@SplitInj.type _ rT A) : type_scope.
Notation "[ 'splitinj'  'of'  f ]" :=
  [the {splitinj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitInjFun aT rT (A : set aT) (B : set rT) :=
  {f of @SplitInj _ rT A f & @isFun _ _ A B f}.
Notation "{ 'splitinjfun' A >-> B }" := (@SplitInjFun.type _ _ A B) : type_scope.
Notation "[ 'splitinjfun'  'of'  f ]" :=
  [the {splitinjfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition Bij {aT rT} {A : set aT} {B : set rT} :=
   {f of @InjFun _ _ A B f & @SurjFun _ _ A B f}.
Notation "{ 'bij' A >-> B }" := (@Bij.type _ _ A B) : type_scope.
Notation "[ 'bij'  'of'  f ]" := [the {bij _ >-> _} of f] : form_scope.

HB.structure Definition SplitBij {aT rT} {A : set aT} {B : set rT} :=
   {f of @SplitInjFun _ _ A B f & @SplitSurjFun _ _ A B f}.
Notation "{ 'splitbij' A >-> B }" := (@SplitBij.type _ _ A B) : type_scope.
Notation "[ 'splitbij'  'of'  f ]" := [the {splitbij _ >-> _} of f] : form_scope.

(* Hint View for move / Inversible.sort inv | 2. *)
(* Hint View for apply / Inversible.sort inv | 2. *)

Module ShortFunSyntax.
Notation "A ~> B" := {fun A >-> B} (at level 70) : type_scope.
Notation "aT <=> rT" := {oinv aT >-> rT} (at level 70) : type_scope.
Notation "A <~ B" := {oinvfun A >-> B} (at level 70) : type_scope.
Notation "aT <<=> rT" := {inv aT >-> rT} (at level 70) : type_scope.
Notation "A <<~ B" := {invfun A >-> B} (at level 70) : type_scope.
Notation "A =>> B" := {surj A >-> B} (at level 70) : type_scope.
Notation "A ~>> B" := {surjfun A >-> B} (at level 70) : type_scope.
Notation "A ==>> B" := {splitsurj A >-> B} (at level 70) : type_scope.
Notation "A ~~>> B" := {splitsurjfun A >-> B} (at level 70) : type_scope.
Notation "A >=> rT" := {inj A >-> rT} (at level 70) : type_scope.
Notation "A >~> B" := {injfun A >-> B} (at level 70) : type_scope.
Notation "A >>=> rT" := {splitinj A >-> rT} (at level 70) : type_scope.
Notation "A >>~> B" := {splitinjfun A >-> B} (at level 70) : type_scope.
Notation "A <~> B" := {bij A >-> B} (at level 70) : type_scope.
Notation "A <<~> B" := {splitbij A >-> B} (at level 70) : type_scope.
End ShortFunSyntax.

(**md**************************************************************************)
(* ## Theory                                                                  *)
(******************************************************************************)

Definition phant_funS aT rT (A : set aT) (B : set rT)
  (f : {fun A >-> B}) of phantom (_ -> _) f := @funS _ _ _ _ f.
Notation "'funS_  f" := (phant_funS (Phantom (_ -> _) f))
  (at level 8, f at level 2) : form_scope.
#[global] Hint Extern 0 (set_fun _ _ _) => solve [apply: funS] : core.
#[global] Hint Extern 0 (prop_in1 _ _) => solve [apply: funS] : core.

Definition fun_image_sub aT rT (A : set aT) (B : set rT) (f : {fun A >-> B}) :=
  image_subP.2 (@funS _ _ _ _ f).
Arguments fun_image_sub {aT rT A B}.
#[global] Hint Extern 0 (_ @` _ `<=` _) => solve [apply: fun_image_sub] : core.

Definition mem_fun aT rT (A : set aT) (B : set rT) (f : {fun A >-> B}) :=
  homo_setP.2 (@funS _ _ _ _ f).
#[global] Hint Extern 0 (prop_in1 _ _) => solve [apply: mem_fun] : core.

Definition phant_mem_fun aT rT (A : set aT) (B : set rT)
  (f : {fun A >-> B}) of phantom (_ -> _) f := homo_setP.2 (@funS _ _ _ _ f).
Notation "'mem_fun_  f" := (phant_mem_fun (Phantom (_ -> _) f))
  (at level 8, f at level 2) : form_scope.

Lemma some_inv {aT rT} (f : {inv aT >-> rT}) x : Some (f^-1 x) = 'oinv_f x.
Proof. by rewrite -oliftV. Qed.

Definition phant_oinvK aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvK _ _ _ _ f.
Notation "'oinvK_ f" := (phant_oinvK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvK : core.

Definition phant_oinvS aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvS _ _ _ _ f.
Notation "'oinvS_ f" := (phant_oinvS (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvS : core.

Variant oinv_spec {aT} {rT} {A : set aT} {B : set rT} (f : {surj A >-> B}) y :
   rT -> option aT -> Type :=
  OInvSpec (x : aT) of A x & f x = y : oinv_spec f y (f x) (Some x).

Lemma oinvP aT rT (A : set aT) (B : set rT) (f : {surj A >-> B}) y :
  B y -> oinv_spec f y y ('oinv_f y).
Proof.
move=> By; have :='oinvK_f (mem_set By).
by have /cid2 [x Ax <-] := 'oinvS_f By => <-; constructor.
Qed.

Definition phant_oinvP aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvP _ _ _ _ f.
Notation "'oinvP_ f" := (phant_oinvP (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvP : core.

Lemma oinvT {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}} x :
  B x -> 'oinv_f x.
Proof. by move=> /'oinvS_f [a Aa <-]. Qed.
Definition phant_oinvT aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvT _ _ _ _ f.
Notation "'oinvT_ f" := (phant_oinvT (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvT : core.

Lemma invK {aT rT} {A : set aT} {B : set rT} {f : {splitsurj A >-> B}} :
   {in B, cancel f^-1 f}.
Proof. by move=> x Bx; rewrite -[x in RHS]'oinvK_f// -some_inv/=. Qed.
Definition phant_invK aT rT (A : set aT) (B : set rT)
   (f : {splitsurj A >-> B}) of phantom (_ -> _) f := @invK _ _ _ _ f.
Notation "'invK_ f" := (phant_invK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve invK : core.

Lemma invS {aT rT} {A : set aT} {B : set rT} {f : {splitsurj A >-> B}} :
  {homo f^-1 : x / B x >-> A x}.
Proof. by move=> x /'oinvS_f/= [a Aa]; rewrite -some_inv => -[<-]. Qed.
Definition phant_invS aT rT (A : set aT) (B : set rT)
   {f : {splitsurjfun A >-> B}} of phantom (_ -> _) f := @invS _ _ _ _ f.
Notation "'invS_ f" := (phant_invS (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve invS : core.

Definition phant_funoK aT rT (A : set aT) (f : {inj A >-> rT})
  of phantom (_ -> _) f := @funoK _ _ _ f.
Notation "'funoK_ f" := (phant_funoK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve funoK : core.

Definition inj {aT rT : nonPropType} {A : set aT} {f : {inj A >-> rT}} :
   {in A &, injective f} := pcan_in_inj funoK.
Definition phant_inj aT rT (A : set aT) (f : {inj A >-> rT}) of
   phantom (_ -> _) f := @inj _ _ _ f.
Notation "'inj_ f" := (phant_inj (Phantom (_ -> _) f)) : form_scope.

Definition inj_hint {aT rT} {A : set aT} {f : {inj A >-> rT}} :
   {in A &, injective f} := inj.
#[global] Hint Extern 0 {in _ &, injective _} => solve [apply: inj_hint] : core.
#[global] Hint Extern 0 (set_inj _ _) => solve [apply: inj_hint] : core.

Lemma injT {aT rT} {f : {inj [set: aT] >-> rT}} : injective f.
Proof. by apply: in2TT; apply: inj. Qed.
#[global] Hint Extern 0 (injective _) => solve [apply: injT] : core.

Lemma funK {aT rT : Type} {A : set aT} {s : {splitinj A >-> rT}} :
  {in A, cancel s s^-1}.
Proof. by move=> x Ax; apply: Some_inj; rewrite some_inv funoK. Qed.

Definition phant_funK aT rT (A : set aT) (f : {splitinj A >-> rT})
  of phantom (_ -> _) f := @funK _ _ _ f.
Notation "'funK_  f" := (phant_funK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve funK : core.

(** Structure Equality *)

Lemma funP {aT rT} {A : set aT} {B : set rT} (f g : {fun A >-> B}) :
  f = g <-> f =1 g.
Proof.
case: f g => [f [[ffun]]] [g [[gfun]]]/=; split=> [[->//]|/funext eqfg].
rewrite eqfg in ffun *; congr {| Fun.sort := _; Fun.class := {|
  Fun.functions_isFun_mixin := {|isFun.funS := _|}|}|}.
exact: Prop_irrelevance.
Qed.

(** Preliminary Builders *)

HB.factory Record Inv_Can {aT rT} {A : set aT} (f : aT -> rT) of Inv _ _ f :=
  { funK : {in A, cancel f f^-1} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Inv_Can _ _ A f.
  Local Lemma funoK: {in A, pcancel f 'oinv_f}.
  Proof. by rewrite -oliftV/=; apply: can_in_pcan; apply: funK. Qed.
  HB.instance Definition _ := OInv_Can.Build _ _ A f funoK.
HB.end.

HB.factory Record Inv_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
     of Inv aT rT f := {
  invS : {homo f^-1 : x / B x >-> A x};
  invK : {in B, cancel f^-1 f};
}.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
    of Inv_CanV _ _ A B f.
  #[local] Lemma oinvK : {in B, ocancel 'oinv_f f}.
  Proof. by move=> x Bx; rewrite -some_inv/= invK. Qed.
  #[local] Lemma oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x}.
  Proof. by move=> x /invS Af'x; exists (f^-1 x); rewrite // -some_inv. Qed.
  HB.instance Definition _ := OInv_CanV.Build _ _ _ _ f oinvS oinvK.
HB.end.

(** Trivial instances *)

Section OInverse.
Context {aT rT : Type} {A : set aT} {B : set rT}.

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  OInv.Build _ _ 'oinv_f (omap f).

Lemma oinvV {f : {oinv aT >-> rT}} : 'oinv_('oinv_f) = omap f.
Proof. by []. Qed.

HB.instance Definition _ (f : {surj A >-> B}) :=
  isFun.Build rT (option aT) B (some @` A) 'oinv_f oinvS.

Lemma surjoinv_inj_subproof (f : {surj A >-> B}) : OInv_Can _ _ B 'oinv_f.
Proof.
split=> x Bx/=; rewrite -[x in RHS]('oinvK_f Bx).
by have := 'oinvT_f (set_mem Bx); case: 'oinv_f.
Qed.
HB.instance Definition _ f := surjoinv_inj_subproof f.

Lemma injoinv_surj_subproof (f : {injfun A >-> B}) :
  OInv_CanV _ _ B (some @` A) 'oinv_f.
Proof.
split=> [_|_ /set_mem] [a Aa <-]/=; last by rewrite funoK ?inE.
by exists (f a) => //; apply: funS.
Qed.
HB.instance Definition _ (f : {injfun A >-> B}) := injoinv_surj_subproof f.

HB.instance Definition _ {f : {bij A >-> B}} := InjFun.on 'oinv_f.

End OInverse.

Section Inverse.
Context {aT rT : Type} {A : set aT} {B : set rT}.

HB.instance Definition _ (f : {inv aT >-> rT}) := Inv.Build rT aT f^-1 f.
HB.instance Definition _ (f : {inv aT >-> rT}) := Inversible.copy inv f^-1.

Lemma invV (f : {inv aT >-> rT}) : f^-1^-1 = f. Proof. by []. Qed.

HB.instance Definition _ (f : {splitsurj A >-> B}) :=
  isFun.Build rT aT B A f^-1 invS.
HB.instance Definition _ (f : {splitsurj A >-> B}) := Fun.copy inv f^-1.
HB.instance Definition _ {f : {splitsurj A >-> B}} :=
  Inv_Can.Build _ _ _ f^-1 'invK_f.
HB.instance Definition _ (f : {splitinjfun A >-> B}) :=
  Inv_CanV.Build _ _ _ _ f^-1 funS funK.
HB.instance Definition _ {f : {splitbij A >-> B}} := InjFun.on f^-1.

End Inverse.

Section Some.
Context {T} {A : set T}.

HB.instance Definition _ := OInv.Build _ _ (@Some T) id.

Lemma oinv_some : 'oinv_(@Some T) = id. Proof. by []. Qed.

Lemma some_can_subproof : @OInv_Can _ _ A (@Some T). Proof. by split. Qed.
HB.instance Definition _ := some_can_subproof.

Lemma some_canV_subproof : OInv_CanV _ _ A (some @` A) (@Some T).
Proof. by split=> [x|x /set_mem] [a Aa <-]//=; exists a. Qed.
HB.instance Definition _  := some_canV_subproof.

Lemma some_fun_subproof : isFun _ _ A (some @` A) (@Some T).
Proof. by split=> x; exists x. Qed.
HB.instance Definition _ := some_fun_subproof.

End Some.

Section OApply.
Context {aT rT} {A : set aT} {B : set rT} {b0 : rT}.
Local Notation oapp f := (oapp f b0).

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  Inv.Build _ _ (oapp f) 'oinv_f.

Lemma inv_oapp {f : {oinv aT >-> rT}} : (oapp f)^-1 = 'oinv_f.
Proof. by []. Qed.
Lemma oinv_oapp  {f : {oinv aT >-> rT}} : 'oinv_(oapp f) = olift 'oinv_f.
Proof. by rewrite -inv_oapp. Qed.
Lemma inv_oappV {f : {inv aT >-> rT}} : olift f^-1 = (oapp f)^-1.
Proof. by rewrite inv_oapp -oliftV. Qed.

Lemma oapp_can_subproof (f : {inj A >-> rT}) : Inv_Can _ _ (some @` A) (oapp f).
Proof. by split=> x /set_mem[a Aa <-]/=; rewrite inv_oapp funoK ?inE. Qed.
HB.instance Definition _ f := oapp_can_subproof f.

Lemma oapp_surj_subproof (f : {surj A >-> B}) : Inv_CanV _ _ (some @` A) B (oapp f).
Proof.
by split=> [b|b /set_mem] Bb/=; rewrite inv_oapp; case: oinvP => // x; exists x.
Qed.
HB.instance Definition _  f := oapp_surj_subproof f.

Lemma oapp_fun_subproof (f : {fun A >-> B}) : isFun _ _ (some @` A) B (oapp f).
Proof. by split=> x [a Aa <-] /=; apply: funS. Qed.
HB.instance Definition _ f := oapp_fun_subproof f.
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {splitbij A >-> B}) := Fun.on (oapp f).

End OApply.

Section OBind.
Context {aT rT} {A : set aT} {B : set (option rT)}.
Local Notation b f := (oapp f None).
Local Notation orT := (option rT).

HB.instance Definition _ {f : {oinv aT >-> orT}} :=
  Inv.Build _ _ (obind f) 'oinv_f.

Lemma inv_obind {f : {oinv aT >-> orT}} : (obind f)^-1 = 'oinv_f.
Proof. by []. Qed.
Lemma oinv_obind {f : {oinv aT >-> orT}} : 'oinv_(obind f) = olift 'oinv_f.
Proof. by []. Qed.
Lemma inv_obindV {f : {inv aT >-> orT}} : (obind f)^-1 = olift f^-1.
Proof. by rewrite inv_obind -oliftV. Qed.

HB.instance Definition _ (f : {fun A >-> B}) := Fun.copy (obind f) (b f).
HB.instance Definition _ (f : {inj A >-> orT}) := Inject.copy (obind f) (b f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (obind f).
HB.instance Definition _ (f : {surj A >-> B}) := Surject.copy (obind f) (b f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (obind f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (obind f).
End OBind.

Section Composition.
Context {aT rT sT} {A : set aT} {B : set rT} {C : set sT}.

Local Lemma comp_fun_subproof (f : {fun A >-> B}) (g : {fun B >-> C}) :
  isFun _ _ A C (g \o f).
Proof. by split => x /'funS_f; apply: funS. Qed.
HB.instance Definition _ f g := comp_fun_subproof f g.

Section OInv.
Context {f : {oinv aT >-> rT}} {g : {oinv rT >-> sT}}.
HB.instance Definition _ := OInv.Build _ _ (g \o f) (obind 'oinv_f \o 'oinv_g).
Lemma oinv_comp : 'oinv_(g \o f) = (obind 'oinv_f) \o 'oinv_g.
Proof. by []. Qed.
End OInv.

Section OInv.
Context {f : {inv aT >-> rT}} {g : {inv rT >-> sT}}.
Lemma some_comp_inv : olift (f^-1 \o g^-1) = 'oinv_(g \o f).
Proof. by rewrite funeqE => x; rewrite oinv_comp -!oliftV. Qed.
HB.instance Definition _ := OInv_Inv.Build aT sT (g \o f) some_comp_inv.
Lemma inv_comp : (g \o f)^-1 = f^-1 \o g^-1. Proof. by []. Qed.
End OInv.

Lemma comp_can_subproof (f : {injfun A >-> B}) (g : {inj B >-> sT}) :
  OInv_Can aT sT A (g \o f).
Proof. by split=> x Ax; rewrite oinv_comp/= funoK ?mem_fun//= funoK. Qed.
HB.instance Definition _ f g := comp_can_subproof f g.

HB.instance Definition _ (f : {injfun A >-> B}) (g : {injfun B >-> C}) :=
  Inject.on (g \o f).
HB.instance Definition _ (f : {splitinjfun A >-> B})
  (g : {splitinj B >-> sT}) := Inject.on (g \o f).
HB.instance Definition _ (f : {splitinjfun A >-> B})
  (g : {splitinjfun B >-> C}) := Inject.on (g \o f).
End Composition.

Section Composition.
Context {aT rT sT} {A : set aT} {B : set rT} {C : set sT}.

Lemma comp_surj_subproof (f : {surj A >-> B}) (g : {surj B >-> C}) :
  OInv_CanV _ _ A C (g \o f).
Proof.
split; first exact: funS.
apply: (@ocan_in_comp _ _ _ (mem B)) oinvK oinvK.
by move=> ? /set_mem; rewrite pred_oapp_set inE; apply: funS.
Qed.

HB.instance Definition _ f g := comp_surj_subproof f g.
HB.instance Definition _ (f : {splitsurj A >-> B}) (g : {splitsurj B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {surjfun A >-> B}) (g : {surjfun B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {splitsurjfun A >-> B})
  (g : {splitsurjfun B >-> C}) := Surject.on (g \o f).
HB.instance Definition _ (f : {bij A >-> B}) (g : {bij B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {splitbij A >-> B}) (g : {splitbij B >-> C}) :=
  Surject.on (g \o f).

End Composition.

Section totalfun.
Context {aT rT : Type}.
Definition totalfun_ (A : set aT) (f : aT -> rT) := f.
Context {A : set aT}.
Local Notation totalfun := (totalfun_ A).
HB.instance Definition _ (f : aT -> rT) :=
  isFun.Build _ _ A setT (totalfun f) (fun _ _ => I).
HB.instance Definition _ (f : {inj A >-> rT}) := Inject.on (totalfun f).
HB.instance Definition _ (f : {splitinj A >-> rT}) := SplitInj.on (totalfun f).
HB.instance Definition _ (f : {surj A >-> [set: rT]}) :=
  Surject.on (totalfun f).
HB.instance Definition _ (f : {splitsurj A >-> [set: rT]}) :=
  SplitSurj.on (totalfun f).
End totalfun.
Notation "''totalfun_' A" := (totalfun_ A) : form_scope.
Notation totalfun := (totalfun_ setT).

Section Olift.
Context {aT rT} {A : set aT} {B : set rT}.

HB.instance Definition _ {f : {oinv aT >-> rT}} := OInversible.copy (olift f)
  (Some \o f).

Lemma oinv_olift  {f : {oinv aT >-> rT}} : 'oinv_(olift f) = obind 'oinv_f.
Proof. by []. Qed.

HB.instance Definition _ (f : {inj A >-> rT}) :=
  Inject.copy (olift f) (Some \o ('totalfun_A f)).
HB.instance Definition _ (f : {surj A >-> B}) :=
  Surject.copy (olift f) (Some \o f).
HB.instance Definition _ (f : {fun A >-> B}) := Fun.copy (olift f) (Some \o f).
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (olift f).

End Olift.

Section Map.
Context {aT rT} {A : set aT} {B : set rT}.
Local Notation m f := (obind (olift f)).

HB.instance Definition _ (f : {fun A >-> B}) := Fun.copy (omap f) (m f).

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  Inv.Build _ _ (omap f) (obind 'oinv_f).

Lemma inv_omap {f : {oinv aT >-> rT}} : (omap f)^-1 = obind 'oinv_f.
Proof. by []. Qed.
Lemma oinv_omap {f : {oinv aT >-> rT}} : 'oinv_(omap f) = olift (obind 'oinv_f).
Proof. by []. Qed.
Lemma omapV {f : {inv aT >-> rT}} : omap f^-1 = (omap f)^-1.
Proof. by rewrite inv_omap -oliftV. Qed.

HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {inj A >-> rT}) := Inject.copy (omap f) (m f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {surj A >-> B}) := Surject.copy (omap f) (m f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (omap f).
End Map.

(** Builders *)

HB.factory Record CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; invS : {homo inv : x / B x >-> A x}; invK : {in B, cancel inv f}; }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of CanV _ _ A B f.
 HB.instance Definition _ := Inv.Build _ _ f inv.
 HB.instance Definition _ := Inv_CanV.Build _ _ _ _ f invS invK.
HB.end.

HB.factory Record OInv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
  @OInv _ _ f :=
  {
    funS :  {homo f : x / A x >-> B x};
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    funoK : {in A, pcancel f 'oinv_f};
    oinvK : {in B, ocancel 'oinv_f f};
  }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OInv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT _ _ f funS.
  HB.instance Definition _ := OInv_Can.Build aT rT _ f funoK.
  HB.instance Definition _ := OInv_CanV.Build aT rT _ _ f oinvS oinvK.
HB.end.

HB.factory Record OCan2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
   { oinv; funS :  {homo f : x / A x >-> B x};
           oinvS : {homo oinv : x / B x >-> (some @` A) x};
           funoK : {in A, pcancel f oinv};
           oinvK : {in B, ocancel oinv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OCan2 _ _ A B f.
  HB.instance Definition _ := OInv.Build aT rT f oinv.
  HB.instance Definition _ := OInv_Can2.Build aT rT _ _ f funS oinvS funoK oinvK.
HB.end.


HB.factory Record Can {aT rT} {A : set aT} (f : aT -> rT) :=
  { inv; funK : {in A, cancel f inv} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Can _ _ A f. (* bug if swap f and A *)
 HB.instance Definition _ := Inv.Build _ _ f inv.
 HB.instance Definition _ := Inv_Can.Build _ _ _ f funK.
HB.end.

HB.factory Record Inv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   Inv _ _ f :=
   { funS : {homo f : x / A x >-> B x};
     invS : {homo f^-1 : x / B x >-> A x};
     funK : {in A, cancel f f^-1};
     invK : {in B, cancel f^-1 f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Inv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT A B f funS.
  HB.instance Definition _ := Inv_Can.Build aT rT A f funK.
  HB.instance Definition _ := @Inv_CanV.Build aT rT A B f invS invK.
HB.end.

HB.factory Record Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; funS : {homo f : x / A x >-> B x};
         invS : {homo inv : x / B x >-> A x};
         funK : {in A, cancel f inv};
         invK : {in B, cancel inv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Can2 _ _ A B f.
  HB.instance Definition _ := Inv.Build aT rT f inv.
  HB.instance Definition _ := Inv_Can2.Build aT rT A B f funS invS funK invK.
HB.end.

HB.factory Record SplitInjFun_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitInjFun _ _ A B f :=
  { invS : {homo f^-1 : x / B x >-> A x}; injV : {in B &, injective f^-1} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of SplitInjFun_CanV _ _ A B f.
  Let mem_inv := homo_setP.2 invS.
  Local Lemma invK : {in B, cancel f^-1 f}.
  Proof. by move=> x Bx; apply: injV; rewrite ?funK ?(mem_fun, mem_inv). Qed.
  HB.instance Definition _ := Inv_CanV.Build aT rT A B f invS invK.
HB.end.

HB.factory Record BijTT {aT rT} (f : aT -> rT) := { bij : bijective f }.
HB.builders Context {aT rT} f of BijTT aT rT f.
  Local Lemma exg : {g | cancel f g /\ cancel g f}.
  Proof. by apply: cid; case: bij => g; exists g. Qed.
  HB.instance Definition _ := Can2.Build aT rT setT setT f
    (fun x y => y) (fun x y => y)
    (in1W (projT2 exg).1) (in1W (projT2 exg).2).
HB.end.

(** Fun in *)

Section surj_oinv.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fsurj : set_surj A B f).

Let surjective_oinv (y : rT) :=
  if pselect (B y) is left By then some (projT1 (cid2 (fsurj By))) else None.

Lemma surjective_oinvK : {in B, ocancel surjective_oinv f}.
Proof.
by rewrite /surjective_oinv => x /set_mem ?; case: pselect => // ?; case: cid2.
Qed.

Lemma surjective_oinvS : set_fun B (some @` A) surjective_oinv.
Proof.
move=> y By /=; rewrite /surjective_oinv; case: pselect => // By'.
by case: cid2 => //= x Ax fxy; exists x.
Qed.
End surj_oinv.
Coercion surjective_ocanV {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
    (fS : set_surj A B f) :=
  OCanV.Build aT rT A B f (surjective_oinvS fS) (surjective_oinvK fS).

Section Psurj.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fsurj : set_surj A B f).

#[local] HB.instance Definition _ : OCanV _ _ A B f := fsurj.
Definition surjection_of_surj := [surj of f].

Lemma Psurj : {s : {surj A >-> B} | f = s}. Proof. by exists [surj of f]. Qed.
End Psurj.
Coercion surjection_of_surj : set_surj >-> Surject.type.

Lemma oinv_surj {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
   (fS : set_surj A B f) y :
 'oinv_fS y = if pselect (B y) is left By then some (projT1 (cid2 (fS y By))) else None.
Proof. by []. Qed.

Lemma surj {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}} : set_surj A B f.
Proof. by move=> b /'oinvP_f[x Ax _]; exists x. Qed.

Definition phant_surj aT rT (A : set aT) (B : set rT) (f : {surj A >-> B})
  of phantom (_ -> _) f := @surj _ _ _ _ f.
Notation "'surj_  f" := (phant_surj (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (set_surj _ _ _) => solve [apply: surj] : core.

Section funin_surj.
Context {aT rT : Type}.

Definition funin (A : set aT) (f : aT -> rT) := f.

Context {A : set aT} {B : set rT} (f : aT -> rT).

Lemma set_fun_image : set_fun A (f @` A) f.
Proof. exact/image_subP. Qed.

HB.instance Definition _ :=
  @isFun.Build _ _ _ _ (funin A f) set_fun_image.

HB.instance Definition _ : OCanV _ _ A (f @` A) (funin A f) :=
   ((fun _ => id) : set_surj A (f @` A) f).

End funin_surj.
Notation "[ 'fun' f 'in' A ]" := (funin A f)
  (at level 0, f at next level,
   format "[ 'fun'  f  'in'  A ]") : function_scope.
#[global] Hint Resolve set_fun_image : core.

(** Partial injection *)

Section split.
Context {aT rT} (A : set aT) (B : set rT).
Definition split_ (dflt : rT -> aT) (f : aT -> rT) := f.

Context (dflt : rT -> aT).
Local Notation split := (split_ dflt).

HB.instance Definition _ (f : {fun A >-> B}) := Fun.on (split f).

Section oinv.
Context (f : {oinv aT >-> rT}).
Let g y := odflt (dflt y) ('oinv_f y).
HB.instance Definition _  := Inv.Build _ _ (split f) g.
Lemma splitV : (split f)^-1 = g. Proof. by []. Qed.
End oinv.
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (split f).

Lemma splitis_inj_subproof (f : {inj A >-> rT}) : Inv_Can _ _ A (split f).
Proof. by split=> x Ax; rewrite splitV funoK. Qed.
HB.instance Definition _ f := splitis_inj_subproof f.
HB.instance Definition _ (f : {injfun A >-> B}) := Inject.on (split f).

Lemma splitid (f : {splitinjfun A >-> B}) : (split f)^-1 = f^-1.
Proof. by apply/funext => x; apply: Some_inj; rewrite splitV -oliftV. Qed.

Lemma splitsurj_subproof (f : {surj A >-> B}) : Inv_CanV _ _ A B (split f).
Proof. by split=> [+|+ /set_mem] => b Bb; rewrite splitV; case: oinvP. Qed.

HB.instance Definition _ f := splitsurj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> B}) := Surject.on (split f).
HB.instance Definition _ (f : {bij A >-> B}) := Surject.on (split f).

End split.
Notation "''split_' a" := (split_ a) : form_scope.
Notation split := 'split_(fun=> point).

(** More Builders *)

HB.factory Record Inj {aT rT} (A : set aT) (f : aT -> rT) :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} A (f : aT -> rT) of Inj _ _ A f.
  HB.instance Definition _ := OInversible.copy f [fun f in A].
  Lemma funoK : {in A, pcancel f 'oinv_f}.
  Proof.
  move=> x /set_mem Ax; rewrite oinv_surj.
  case: pselect => //=; last by case; exists x.
  by move=> ?; case: cid2 => //= y Ay /inj; rewrite !inE => ->.
  Qed.
  HB.instance Definition _ := OInv_Can.Build _ _ _ f funoK.
HB.end.

HB.factory Record SurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   @SurjFun _ _ A B f := { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SurjFun_Inj _ _ A B f.
  Let g := f.
  HB.instance Definition _ := Inj.Build _ _ A g inj.
  Let fcan : OInv_Can aT rT A f.
  Proof.
  split=> x /set_mem Ax; apply: 'inj_(omap g); rewrite ?mem_fun ?inE//=.
  by rewrite /g -oinvV/= funoK// ?mem_fun ?inE.
  Qed.
 HB.instance Definition _ := fcan.
HB.end.

HB.factory Record SplitSurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitSurjFun _ _ A B f :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SplitSurjFun_Inj _ _ A B f.
  Local Lemma funK : {in A, cancel f f^-1%FUN}.
  Proof.  by move=> x Ax; apply: inj; rewrite ?invK ?mem_fun. Qed.
  HB.instance Definition _ := Inv_Can.Build aT rT _ f funK.
HB.end.

Section Inverses.
Context aT rT {A : set aT} {B : set rT}.
HB.instance Definition _ (f : {inj A >-> rT}) :=
  SurjFun_Inj.Build _ _ _ _ [fun f in A] 'inj_f.
End Inverses.

(**md**************************************************************************)
(* ## Simple Factories                                                        *)
(******************************************************************************)

Section Pinj.
Context {aT rT} {A : set aT} {f : aT -> rT} (finj : {in A &, injective f}).
#[local] HB.instance Definition _ := Inj.Build _ _ _ f finj.
Lemma Pinj : {i : {inj A >-> rT} | f = i}. Proof. by exists [inj of f]. Qed.
End Pinj.

Section Pfun.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
  (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := isFun.Build _ _ _ _ g ffun.
Lemma Pfun : {i : {fun A >-> B} | f = i}. Proof. by exists [fun of g]. Qed.
End Pfun.

Section injPfun.
Context {aT rT} {A : set aT} {B : set rT} {f : {inj A >-> rT}}
   (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Inject.on g.
#[local] HB.instance Definition _ := isFun.Build _ _ A B g ffun.
Lemma injPfun : {i : {injfun A >-> B} | f = i :> (_ -> _)}.
Proof. by exists [injfun of g]. Qed.
End injPfun.

Section funPinj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}
  (finj : {in A &, injective f}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on g.
#[local] HB.instance Definition _ := Inj.Build _ _ _ g finj.
Lemma funPinj : {i : {injfun A >-> B} | f = i}.
Proof. by exists [injfun of g]; apply/funP. Qed.
End funPinj.

Section funPsurj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}
        (fsurj : set_surj A B f).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on g.
#[local] HB.instance Definition _ : OCanV _ _ A B g := fsurj.
Lemma funPsurj : {s : {surjfun A >-> B} | f = s}.
Proof. by exists [surjfun of g]; apply/funP. Qed.
End funPsurj.

Section surjPfun.
Context {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}}
   (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Surject.on g.
#[local] HB.instance Definition _ := isFun.Build _ _ A B g ffun.
Lemma surjPfun : {s : {surjfun A >-> B} | f = s :> (_ -> _)}.
Proof. by exists [surjfun of g]. Qed.
End surjPfun.

Section Psplitinj.
Context {aT rT} {A : set aT} {f : aT -> rT} {g} (funK : {in A, cancel f g}).
#[local] HB.instance Definition _ := Can.Build _ _ A f funK.
Lemma Psplitinj : {i : {splitinj A >-> rT} | f = i}.
Proof. by exists [splitinj of f]. Qed.
End Psplitinj.

Section funPsplitinj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}.
Context {g} (funK : {in A, cancel f g}).
Let f' : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on f'.
#[local] HB.instance Definition _ := Can.Build _ _ A f' funK.
Lemma funPsplitinj : {i : {splitinjfun A >-> B} | f = i}.
Proof. by exists [splitinjfun of f']; apply/funP. Qed.
End funPsplitinj.

Lemma PsplitinjT {aT rT} {f : aT -> rT} {g} : cancel f g ->
  {i : {splitinj [set: aT] >-> rT} | f = i}.
Proof. by move/in1W/Psplitinj. Qed.

Section funPsplitsurj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}.
Context {g : {fun B >-> A}} (funK : {in B, cancel g f}).
Let f' : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on f'.
#[local] HB.instance Definition _ := CanV.Build _ _ A B f' funS funK.
Lemma funPsplitsurj : {s : {splitsurjfun A >-> B} | f = s :> (_ -> _)}.
Proof. by exists [splitsurjfun of f']. Qed.
End funPsplitsurj.

Lemma PsplitsurjT {aT rT} {f : aT -> rT} {g} : cancel g f ->
  {s : {splitsurjfun [set: aT] >-> [set: rT]} | f = s}.
Proof.
by move/in1W/(@funPsplitsurj _ _ _ _ [fun of totalfun f] [fun of totalfun g]).
Qed.

(**md**************************************************************************)
(* ## Instances                                                               *)
(******************************************************************************)

(** The identity is a split bijection *)

HB.instance Definition _ T A := @Can2.Build T T A A idfun idfun
   (fun x y => y) (fun x y => y) (fun _ _ => erefl) (fun _ _ => erefl).

(** Iteration preserves Fun, Injectivity, and Surjectivity *)
Section iter_inv.

Context {aT} {A : set aT}.

Local Lemma iter_fun_subproof n (f : {fun A >-> A}) : isFun _ _ A A (iter n f).
Proof.
split => x; elim: n => // n /[apply] ?; apply/(fun_image_sub f).
by exists (iter n f x).
Qed.

HB.instance Definition _ n f := iter_fun_subproof n f.

Section OInv.
Context {f : {oinv aT >-> aT}}.
HB.instance Definition _ n := OInv.Build _ _ (iter n f)
  (iter n (obind 'oinv_f) \o some).
Lemma oinv_iter n : 'oinv_(iter n f) = iter n (obind 'oinv_f) \o some.
Proof. by []. Qed.
End OInv.

Section OInv.
Context {f : {inv aT >-> aT}}.
Lemma some_iter_inv n : olift (iter n f^-1) = 'oinv_(iter n f).
Proof.
elim: n => // n IH; rewrite iterfSr olift_comp IH ?oinv_iter -compA.
rewrite (_ : Some \o f^-1 = 'oinv_f); first by rewrite iterfSr; congr (_ \o _).
by apply/funeqP => ? /=; rewrite some_inv.
Qed.
HB.instance Definition _ n := OInv_Inv.Build _ _ (iter n f) (some_iter_inv n).
Lemma inv_iter n : (iter n f)^-1 = iter n f^-1. Proof. by []. Qed.
End OInv.

Lemma iter_can_subproof n (f : {injfun A >-> A}) : OInv_Can aT aT A (iter n f).
Proof.
split=> x Ax; rewrite oinv_iter /=; elim: n=> // n IH.
by rewrite iterfSr /= funoK //; exact: mem_fun.
Qed.

HB.instance Definition _ f g := iter_can_subproof f g.
HB.instance Definition _ n (f : {injfun A >-> A}) := Inject.on (iter n f).
HB.instance Definition _ n (f : {splitinjfun A >-> A}) := Inject.on (iter n f).
End iter_inv.

Section iter_surj.
Context {aT} {A : set aT}.

Lemma iter_surj_subproof n (f : {surj A >-> A}) : OInv_CanV _ _ A A (iter n f).
Proof.
split; first exact: funS.
elim: n=> // n IH; rewrite oinv_iter iterfSr iterfS.
apply: (@ocan_in_comp _ _ _ (mem A)) => //; last exact: oinvK.
elim: n {IH} => // n IH x Ax; move: (IH _ Ax); rewrite pred_oapp_set ?inE.
case=> y Ay /= ynf; case: (@oinvS _ _ _ _ f _ Ay) => z ? zfinv; exists z => //.
by rewrite zfinv /= -ynf.
Qed.

HB.instance Definition _ n f := iter_surj_subproof n f.
HB.instance Definition _ n (f : {splitsurj A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {surjfun A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {splitsurjfun A >-> A}) :=
  Surject.on (iter n f).
HB.instance Definition _ n (f : {bij A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {splitbij A >-> A}) := Surject.on (iter n f).

End iter_surj.

(** Unbind *)

Section Unbind.
Context {aT rT} {A : set aT} {B : set rT} (dflt : aT -> rT).
Definition unbind (f : aT -> option rT) x := odflt (dflt x) (f x).

Lemma unbind_fun_subproof (f : {fun A >-> some @` B}) : isFun _ _ A B (unbind f).
Proof. by rewrite /unbind; split=> x /'funS_f [y Bu <-]. Qed.
HB.instance Definition _ f := unbind_fun_subproof f.

Section Oinv.
Context (f : {oinv aT >-> option rT}).
HB.instance Definition _ := OInv.Build _ _ (unbind f) ('oinv_f \o some).

Lemma oinv_unbind : 'oinv_(unbind f) = 'oinv_f \o some. Proof. by []. Qed.
End Oinv.
HB.instance Definition _ (f : {oinvfun A >-> some @` B}) := Fun.on (unbind f).

Section Inv.
Context (f : {inv aT >-> option rT}).
Lemma inv_unbind_subproof : olift (f^-1 \o some) = 'oinv_(unbind f).
Proof. by rewrite olift_comp oliftV. Qed.
HB.instance Definition _ := OInv_Inv.Build _ _ (unbind f) inv_unbind_subproof.

Lemma inv_unbind : (unbind f)^-1 = f^-1 \o some. Proof. by []. Qed.
End Inv.
HB.instance Definition _ (f : {invfun A >-> some @` B}) := Fun.on (unbind f).

Lemma unbind_inj_subproof (f : {injfun A >-> some @` B}) :
   @OInv_Can _ _ A (unbind f).
Proof.
split=> x Ax; rewrite oinv_unbind /unbind/=; have <- := 'funoK_f Ax.
by have [y By /= <-] := 'funS_f (set_mem Ax).
Qed.
HB.instance Definition _ f := unbind_inj_subproof f.
HB.instance Definition _ (f : {splitinjfun A >-> some @` B}) :=
  Inject.on (unbind f).

Lemma unbind_surj_subproof (f : {surj A >-> some @` B}) :
   @OInv_CanV _ _ A B (unbind f).
Proof.
split=> [b|b /set_mem] Bb; rewrite oinv_unbind /unbind/=.
  by case: oinvP => [|a]; [exists b | exists a].
by case: oinvP => [|a Aa /= ->]; first by exists b.
Qed.
HB.instance Definition _ f := unbind_surj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {splitsurj A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {splitsurjfun A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {bij A >-> some @` B}) := Surject.on (unbind f).
HB.instance Definition _ (f : {splitbij A >-> some @` B}) := Bij.on (unbind f).

End Unbind.

(** Odflt *)

Section Odflt.
Context {T} {A : set T} (x : T).

Lemma odflt_unbind : odflt x = unbind (fun=> x) idfun. Proof. by []. Qed.

HB.instance Definition _ := Inv.Build _ _ (odflt x) some.

HB.instance Definition _ := SplitBij.copy (odflt x)
  [the {splitbij some @` A >-> A} of @unbind (option T) T (fun=> x) idfun].

End Odflt.

(** Subtypes *)

Section SubType.
Context {T : Type} {P : pred T} (sT : subType P) (x0 : sT).

HB.instance Definition _ := OInv.Build sT T val insub.

Lemma oinv_val : 'oinv_val = insub. Proof. by []. Qed.

Lemma val_bij_subproof : OInv_Can2 sT T setT [set` P] val.
Proof.
apply: (OInv_Can2.Build _ _ _ _ val (fun x  _ => valP x)
        _ (in1W valK) (in1W (insubK _))).
by move=> x Px /=; exists (Sub x Px) => //; rewrite oinv_val insubT.
Qed.
HB.instance Definition _ := val_bij_subproof.

HB.instance Definition _ := Bij.copy insub 'oinv_val.
HB.instance Definition _ := SplitBij.copy (insubd x0)
   (odflt x0 \o 'split_(fun=> val x0) insub).

Lemma inv_insubd : (insubd x0)^-1 = val. Proof. by []. Qed.

End SubType.

(** To setT *)

Definition to_setT {T} (x : T) : [set: T] :=
  @SigSub _ _ _ x (mem_set I : x \in setT).
HB.instance Definition _ T := Can.Build T [set: T] setT to_setT
  ((fun _ _ => erefl) : {in setT, cancel to_setT val}).
HB.instance Definition _ T := isFun.Build T _ setT setT to_setT (fun _ _ => I).
HB.instance Definition _ T :=
  SplitInjFun_CanV.Build T _ _ _ to_setT (fun x y => I) inj.
Definition setTbij {T} := [splitbij of @to_setT T].

Lemma inv_to_setT T : (@to_setT T)^-1 = val. Proof. by []. Qed.

(** Subfun *)

Section subfun.
Context {T} {A B : set T}.

Definition subfun (AB : A `<=` B) (a : A) : B :=
  SigSub (mem_set (AB _ (set_valP a))).

Lemma subfun_inj {AB : A `<=` B} : injective (subfun AB).
Proof. by move=> x y /(congr1 val)/= /val_inj. Qed.

HB.instance Definition _ (AB : A `<=` B) :=
  SurjFun.copy (subfun AB) [fun subfun AB in setT].
HB.instance Definition _  (AB : A `<=` B) :=
  SurjFun_Inj.Build A B setT (subfun AB @` setT) (subfun AB) (in2W subfun_inj).

End subfun.

Section subfun_eq.
Context {T} {A B : set T}.

Lemma subfun_imageT (AB : A `<=` B) (BA : B `<=` A) : subfun AB @` setT = setT.
Proof.
by apply/seteqP; split=> x //= _; exists (subfun BA x) => //; exact/val_inj.
Qed.

Lemma subfun_inv_subproof (AB : A = B) :
  olift (subfun (subsetCW AB)) = 'oinv_(subfun (subsetW AB)).
Proof.
set g := subfun _; set f := subfun _; apply/funext => x /=.
apply: 'inj_(oapp f x) => //=.
- by rewrite inE/=; eexists.
- by rewrite inE/=; apply: 'oinvS_f; exists (g x) => //; apply/val_inj.
rewrite oinvK ?inE//=; first exact/val_inj.
by exists (g x) => //; apply/val_inj.
Qed.
(* Add a Inj_Can factory *)
HB.instance Definition _ (AB : A = B) :=
  OInv_Inv.Build A B (subfun (subsetW AB)) (subfun_inv_subproof AB).

End subfun_eq.

Section seteqfun.
Context {T : Type}.

Definition seteqfun {A B : set T} (AB : A = B) := subfun (subsetW AB).

Context {A B : set T} (AB : A = B).
HB.instance Definition _ := Inv.Build A B (seteqfun AB) (seteqfun (esym AB)).

Lemma seteqfun_can2_subproof : Inv_Can2 A B setT setT (seteqfun AB).
Proof. by split; rewrite /seteqfun//; move=> x _; apply/val_inj. Qed.
HB.instance Definition _ := seteqfun_can2_subproof.

End seteqfun.

(** Inclusion *)

Section incl.
Context  {T} {A B : set T}.
Definition incl (AB : A `<=` B) := @id T.

HB.instance Definition _ (AB : A `<=` B) := Inv.Build _ _ (incl AB) id.
HB.instance Definition _ (AB : A `<=` B) := isFun.Build _ _ A B (incl AB) AB.
HB.instance Definition _ (AB : A `<=` B) :=
  Inv_Can.Build _ _ A (incl AB) (fun _ _ => erefl).

Definition eqincl (AB : A = B) := incl (subsetW AB).
HB.instance Definition _ AB := Inversible.on (eqincl AB).
Lemma eqincl_surj AB : Inv_Can2 _ _ A B (eqincl AB).
Proof. by split=> // x; rewrite /eqincl /incl/= /(_^-1)/inv/= AB. Qed.
HB.instance Definition _ AB := eqincl_surj AB.

End incl.
Notation inclT A := (incl (@subsetT _ _)).

(** Ad hoc function *)

Section mkfun.
Context {aT} {rT} {A : set aT} {B : set rT}.
Notation isfun f := {homo f : x / A x >-> B x}.
Definition mkfun f (fAB : isfun f) := f.
HB.instance Definition _ f fAB := @isFun.Build _ _ A B (@mkfun f fAB) fAB.
Definition mkfun_fun f fAB := [fun of @mkfun f fAB].
HB.instance Definition _ (f : {inj A >-> rT}) fAB := Inject.on (@mkfun f fAB).
HB.instance Definition _ (f : {splitinj A >-> rT}) fAB :=
  SplitInj.on (@mkfun f fAB).
HB.instance Definition _ (f : {surj A >-> B}) fAB :=
  Surject.on (@mkfun f fAB).
HB.instance Definition _ (f : {splitsurj A >-> B}) fAB :=
  SplitSurj.on (@mkfun f fAB).
End mkfun.

(** set_val *)

Section set_val.
Context {T} {A : set T}.
Definition set_val : A -> T := eqincl (set_mem_set A) \o val.
HB.instance Definition _ := Bij.on set_val.
Lemma oinv_set_val : 'oinv_set_val = insub. Proof. by []. Qed.
Lemma set_valE : set_val = val. Proof. by []. Qed.
End set_val.

#[global]
Hint Extern 0 (is_true (set_val _ \in _)) => solve [apply: valP] : core.

(** Squash *)

HB.instance Definition _ T := CanV.Build T $|T| setT setT squash (fun _ _ => I)
                              (in1W unsquashK).
HB.instance Definition _ T := SplitInj.copy (@unsquash T) squash^-1%FUN.
Definition ssquash {T} := [splitsurj of @squash T].

(** pickle and unpickle *)

HB.instance Definition _ (T : countType) :=
  Inj.Build _ _ setT (@choice.pickle T) (in2W (pcan_inj choice.pickleK)).
HB.instance Definition _ (T : countType) :=
  isFun.Build _ _ setT setT (@choice.pickle T) (fun _ _ => I).

(** set0fun *)

Lemma set0fun_inj {P T} : injective (@set0fun P T).
Proof. by case=> x x0; have := set_mem x0. Qed.

HB.instance Definition _ P T :=
  Inj.Build (@set0 T) P setT set0fun (in2W set0fun_inj).
HB.instance Definition _ P T :=
  isFun.Build _ _ setT setT (@set0fun P T) (fun _ _ => I).

(** cast_ord *)

HB.instance Definition _ {m n} {eq_mn : m = n} :=
  Can2.Build 'I_m 'I_n setT setT (cast_ord eq_mn)
    (fun _ _ => I) (fun _ _ => I)
    (in1W (cast_ordK _)) (in1W (cast_ordKV _)).

(** enum_val & enum_rank *)

HB.instance Definition _ (T : finType) :=
  Can2.Build T _ setT setT enum_rank (fun _ _ => I) (fun _ _ => I)
                                    (in1W enum_rankK) (in1W enum_valK).

HB.instance Definition _ (T : finType) :=
  Can2.Build _ T setT setT enum_val (fun _ _ => I) (fun _ _ => I)
                                    (in1W enum_valK) (in1W enum_rankK).

(** Finset val *)

Definition finset_val {T : choiceType} {X : {fset T}} (x : X) : [set` X] :=
  exist (fun x => x \in [set` X]) (val x) (mem_set (valP x)).
Definition val_finset {T : choiceType} {X : {fset T}} (x : [set` X]) : X :=
  [` set_mem (valP x)]%fset.

Lemma finset_valK {T : choiceType} {X : {fset T}} :
  cancel (@finset_val T X) val_finset.
Proof. by move=> x; apply/val_inj. Qed.

Lemma val_finsetK {T : choiceType} {X : {fset T}} :
  cancel (@val_finset T X) finset_val.
Proof. by move=> x; apply/val_inj. Qed.

HB.instance Definition _  {T : choiceType} {X : {fset T}} :=
  Can2.Build X _ setT setT finset_val (fun _ _ => I) (fun _ _ => I)
             (in1W finset_valK) (in1W val_finsetK).
HB.instance Definition _  {T : choiceType} {X : {fset T}} :=
  Can2.Build _ X setT setT val_finset (fun _ _ => I) (fun _ _ => I)
             (in1W val_finsetK) (in1W finset_valK).

(** 'I_n and `I_n *)

HB.instance Definition _ n := Can2.Build _ _ setT setT (@ordII n)
   (fun _ _ => I) (fun _ _ => I) (in1W ordIIK) (in1W IIordK).
HB.instance Definition _ n := SplitBij.copy (@IIord n) (ordII^-1).

(**md**************************************************************************)
(* ## Glueing                                                                 *)
(******************************************************************************)

Definition glue {T T'} {X Y : set T} {A B : set T'}
  of [disjoint X & Y] & [disjoint A & B] :=
  fun (f g : T -> T') (u : T) => if u \in X then f u else g u.

Section Glue12.
Context {T T'} {X Y : set T} {A B : set T'}.
Context {XY : [disjoint X & Y]} {AB : [disjoint A & B]}.
Local Notation gl := (glue XY AB).

Definition glue1 (f g : T -> T') : {in X, gl f g =1 f}.
Proof. by move=> x; rewrite /glue => ->. Qed.

Definition glue2 (f g : T -> T') : {in Y, gl f g =1 g}.
Proof.
move=> x /set_mem Yx; rewrite /glue; case: ifPn => // /set_mem Xx.
by move: XY => /disj_setPS/(_ x (conj Xx Yx)).
Qed.
End Glue12.

Section Glue.
Context {T T'} {X Y : set T} {A B : set T'}.
Context {XY : [disjoint X & Y]} {AB : [disjoint A & B]}.
Local Notation gl := (glue XY AB).

Lemma glue_fun_subproof (f : {fun X >-> A}) (g : {fun Y >-> B}) :
  isFun T T' (X `|` Y) (A `|` B) (gl f g).
Proof.
by split=> x []xP; [left; rewrite glue1|right; rewrite glue2];
   rewrite ?inE//; apply: funS.
Qed.
HB.instance Definition _ f g := glue_fun_subproof f g.

HB.instance Definition _ (f g : {oinv T >-> T'}) :=
  OInv.Build _ _ (gl f g) (glue AB (eqbRL disj_set_some XY) 'oinv_f 'oinv_g).

HB.instance Definition _  (f : {oinvfun X >-> A}) (g : {oinvfun Y >-> B}) :=
  OInversible.on (gl f g).

Lemma oinv_glue (f : {oinv T >-> T'}) (g : {oinv T >-> T'}) :
  'oinv_(gl f g) = glue AB (eqbRL disj_set_some XY) 'oinv_f 'oinv_g.
Proof. by []. Qed.

Lemma some_inv_glue_subproof (f g : {inv T >-> T'}) :
  some \o (glue AB XY f^-1 g^-1) = 'oinv_(gl f g).
Proof.
by apply/funext => y; rewrite oinv_glue /glue /= [LHS]fun_if !some_inv.
Qed.

HB.instance Definition _ (f g : {inv T >-> T'}) :=
  OInv_Inv.Build T T' (gl f g) (some_inv_glue_subproof f g).

HB.instance Definition _ (f : {invfun X >-> A}) (g : {invfun Y >-> B}) :=
  Inversible.on (gl f g).

Lemma inv_glue (f : {invfun X >-> A}) (g : {invfun Y >-> B}) :
  (gl f g)^-1 = glue AB XY f^-1 g^-1.
Proof. by []. Qed.

Lemma glueo_can_subproof (f : {injfun X >-> A}) (g : {injfun Y >-> B}) :
  OInv_Can _ _ (X `|` Y) (gl f g).
Proof.
split=> x; rewrite inE => -[] xP; rewrite oinv_glue.
  by rewrite [glue _ _ _ _ x]glue1 ?inE// glue1 ?funoK ?inE//; apply: funS.
by rewrite [glue _ _ _ _ x]glue2 ?inE// glue2 ?funoK ?inE//; apply: funS.
Qed.
HB.instance Definition _ f g := glueo_can_subproof f g.

HB.instance Definition _ (f : {splitinjfun X >-> A})
  (g : {splitinjfun Y >-> B}) := Inject.on (gl f g).

Lemma glue_canv_subproof (f : {surj X >-> A}) (g : {surj Y >-> B}) :
  OInv_CanV _ _ (X `|` Y) (A `|` B) (gl f g).
Proof.
split=> [z|y /set_mem [] yP]; rewrite oinv_glue.
- by move=> [] zP /=; [rewrite glue1|rewrite glue2]; rewrite ?inE//;
     case: oinvP=> // x xX _; exists x => //; [left|right].
- by rewrite glue1 ?inE//; case: oinvP=> //= x xX _; rewrite glue1 ?inE.
- by rewrite glue2 ?inE//; case: oinvP=> //= x xX _; rewrite glue2 ?inE.
Qed.
HB.instance Definition _ f g := glue_canv_subproof f g.
HB.instance Definition _ (f : {surjfun X >-> A}) (g : {surjfun Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitsurj X >-> A}) (g : {splitsurj Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitsurjfun X >-> A}) (g : {splitsurjfun Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {bij X >-> A}) (g : {bij Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitbij X >-> A}) (g : {splitbij Y >-> B}) :=
  Surject.on (gl f g).

End Glue.

(** Z-module addition is a bijection *)

Section addition.
Context {V : zmodType} (x : V).

HB.instance Definition _ := Inv.Build V V (+%R x) (+%R (- x)).

Lemma inv_addr : (+%R x)^-1 = (+%R (- x)). Proof. by []. Qed.

Lemma addr_can2_subproof : Inv_Can2 V V setT setT (+%R x).
Proof. by split => // y _; rewrite inv_addr ?GRing.addKr ?GRing.addNKr. Qed.
HB.instance Definition _ := addr_can2_subproof.

End addition.

(** Z-module opposite is a bijection *)

Section addition.
Context {V : zmodType} (x : V).
Local Open Scope ring_scope.
(* TODO: promote -%R to empty scope in mathcomp/HB *)

HB.instance Definition _ := Inv.Build V V (-%R) (-%R).

Lemma inv_oppr : (-%R)^-1%FUN = (-%R). Proof. by []. Qed.

Lemma oppr_can2_subproof : Inv_Can2 V V setT setT (-%R).
Proof. by split => // y _; rewrite inv_oppr ?GRing.opprK. Qed.
HB.instance Definition _ := oppr_can2_subproof.

End addition.

(** emtpyType *)

Section empty.
Context {T : emptyType} {T' : Type} {X : set T}.
Implicit Type Y : set T'.

HB.instance Definition _ := OInv.Build _ _ (@any T T') (fun=> None).

Lemma empty_can_subproof : OInv_Can T T' X any.
Proof. by split=> x; rewrite empty_eq0 inE. Qed.
HB.instance Definition _ := empty_can_subproof.

Lemma empty_fun_subproof Y : isFun T T' X Y any.
Proof. by split=> x; rewrite empty_eq0. Qed.
HB.instance Definition _ Y := empty_fun_subproof Y.

Lemma empty_canv_subproof : OInv_CanV T T' X set0 any. Proof. by split. Qed.
HB.instance Definition _ := empty_canv_subproof.

End empty.

(**md**************************************************************************)
(* ## Theory of surjection                                                    *)
(******************************************************************************)

Section surj_lemmas.
Variables aT rT : Type.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma surj_id A : set_surj A A (@idfun aT). Proof. exact: surj. Qed.

Lemma surj_set0 B f : set_surj set0 B f -> B = set0.
Proof. by move=> Bf; rewrite predeqE => u; split => // /Bf [t []]. Qed.

Lemma surjE f A B : set_surj A B f = (B `<=` f @` A). Proof. by []. Qed.

Lemma surj_image_eq B A f : f @` A `<=` B -> set_surj A B f -> f @` A = B.
Proof. by move=> fAB; rewrite eqEsubset => BfA. Qed.

Lemma subl_surj A A' B f : A `<=` A' -> set_surj A B f -> set_surj A' B f.
Proof. by move=> /(@image_subset _ _ f)/(subset_trans _); apply. Qed.

Lemma subr_surj A B B' f : B' `<=` B -> set_surj A B f -> set_surj A B' f.
Proof. exact: subset_trans. Qed.

Lemma can_surj g f (A : set aT) (B : set rT) :
    {in B, cancel g f} -> g @` B `<=` A ->
  set_surj A B f.
Proof.
move=> gK gBA y By; suff : A (g y) by exists (g y); rewrite ?gK ?inE.
by have := image_subP.1 gBA y; apply.
Qed.

Lemma surj_epi sT A B (f : aT -> rT) (g g' : rT -> sT) :
  set_surj A B f -> {in A, g \o f =1 g' \o f} -> {in B, g =1 g'}.
Proof.
move=> fS eqfg y /set_mem By; suff: B `<=` [set y | g y = g' y] by exact.
by apply: subset_trans fS _ => _ [a /mem_set Aa <-] /=; rewrite [LHS]eqfg.
Qed.

Lemma epiP A B (f : aT -> rT) : set_surj A B f <->
  forall sT (g g' : rT -> sT), {in A, g \o f =1 g' \o f} -> {in B, g =1 g'}.
Proof.
split=> [*| f_epi y By]; first exact: (@surj_epi _ A B f).
have -> // := f_epi _ [set f x | x in A] setT; last exact: mem_set.
by move=> x /set_mem xA; apply/propT; exists x.
Qed.

End surj_lemmas.
Arguments can_surj {aT rT} g [f A B].
Arguments surj_epi {aT rT sT} A {B} f {g}.

Lemma surj_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g:
  set_surj A B f -> set_surj B C g -> set_surj A C (g \o f).
Proof. by move=> fS gS; apply: 'surj_(gS \o fS). Qed.

Lemma image_eq {aT rT} {A : set aT} {B : set rT} (f : {surjfun A >-> B}) : f @` A = B.
Proof. exact: surj_image_eq. Qed.

Lemma oinv_image_sub {aT rT : Type} {A : set aT} {B : set rT}
    (f : {surj A >-> B}) {C : set rT} :
  C `<=` B -> 'oinv_f @` C `<=` some @` (f @^-1` C).
Proof.
move=> CB x [/= y Cy <-]; case: 'oinvP_f => [|a Aa fay]; first exact: CB.
by exists a => //; rewrite fay.
Qed.
Arguments oinv_image_sub {aT rT A B} f {C} _.

Lemma oinv_Iimage_sub {aT rT : Type} {A : set aT} (f : {inj A >-> rT}) {C : set rT} :
  C `<=` f @` A -> some @` (A `&` f @^-1` C) `<=` 'oinv_f @` C.
Proof. by move=> ? _ [a [? ?] <-]; exists (f a) => //; rewrite funoK ?inE. Qed.
Arguments oinv_Iimage_sub {aT rT A} f {C} _.

Lemma oinv_sub_image {aT rT} {A : set aT} {B : set rT} {f : {bij A >-> B}}
   {C : set rT} (CB : C `<=` B) : 'oinv_f @` C = some @` (A `&` f @^-1` C).
Proof.
apply/seteqP; split; last by apply: oinv_Iimage_sub; rewrite image_eq.
rewrite some_setI subsetI; split; last by apply: oinv_image_sub.
by apply: (subset_trans (image_subset CB)); rewrite image_eq.
Qed.
Arguments oinv_sub_image {aT rT A B} f {C} _.

Lemma preimageEoinv {aT rT} {B : set rT} {f : {bij [set: aT] >-> B}}
   {C : set rT} (CB : C `<=` B) : some @` (f @^-1` C) = 'oinv_f @` C.
Proof. by rewrite oinv_sub_image// setTI. Qed.
Arguments preimageEoinv {aT rT B} f {C} _.

Lemma inv_image_sub {aT rT : Type} {A : set aT} {B : set rT}
    (f : {splitsurj A >-> B}) {C : set rT} :
  C `<=` B -> f^-1 @` C `<=` f @^-1` C.
Proof. by move=> CB x [/= y Cy <-]; rewrite invK// mem_set//; apply: CB. Qed.
Arguments inv_image_sub {aT rT A B} f {C} _.

Lemma inv_Iimage_sub {aT rT : Type} {A : set aT} (f : {splitinj A >-> rT}) {C : set rT} :
  C `<=` f @` A ->  A `&` f @^-1` C `<=` f^-1 @` C.
Proof. by move=> CB x [Ax Cfx]; exists (f x) => //; rewrite funK// mem_set. Qed.
Arguments inv_Iimage_sub {aT rT A} f {C} _.

Lemma inv_sub_image {aT rT} {A : set aT} {B : set rT} {f : {splitbij A >-> B}}
    {C : set rT} (CB : C `<=` B) :
  f^-1 @` C = A `&` f @^-1` C.
Proof.
by apply: image_some_inj; rewrite image_comp [Some \o _]oliftV oinv_sub_image.
Qed.
Arguments inv_sub_image {aT rT A B} f {C} _.

Lemma preimageEinv {aT rT} {B : set rT} {f : {splitbij [set: aT] >-> B}}
    {C : set rT} (CB : C `<=` B) : f @^-1` C = f^-1 @` C.
Proof. by rewrite inv_sub_image// setTI. Qed.
Arguments preimageEinv {aT rT B} f {C} _.

Lemma reindex_bigcup {aT rT I} (f : aT -> I) (P : set aT) (Q : set I)
    (F : I -> set rT) : set_fun P Q f -> set_surj P Q f ->
  \bigcup_(x in Q) F x = \bigcup_(x in P) F (f x).
Proof.
by move=> /image_subP fPQ /(surj_image_eq fPQ)<-; rewrite bigcup_image.
Qed.
Arguments reindex_bigcup {aT rT I} f P Q.

Lemma reindex_bigcap {aT rT I} (f : aT -> I) (P : set aT) (Q : set I)
    (F : I -> set rT) : set_fun P Q f -> set_surj P Q f ->
  \bigcap_(x in Q) F x = \bigcap_(x in P) F (f x).
Proof.
by move=> /image_subP fPQ /(surj_image_eq fPQ)<-; rewrite bigcap_image.
Qed.
Arguments reindex_bigcap {aT rT I} f P Q.

Lemma bigcap_bigcup T I J (D : set I) (E : set J) (F : I -> J -> set T) :
  J ->
  \bigcap_(i in D) \bigcup_(j in E) F i j =
  \bigcup_(f in set_fun D E) \bigcap_(i in D) F i (f i).
Proof.
move=> j; apply/seteqP; split=> x.
  move=> /(_ _ _)/cid2 ff.
  have /(all_sig2_cond j) (i : I) : i \in D -> {x0 : J | E x0 & F i x0 x}.
    by move=> /set_mem; apply: ff.
  by move=> [f /(_ _ (mem_set _))Ef /(_ _ (mem_set _))Ff]; exists f.
by move=> [f fDE fF i Fi]; exists (f i); [apply: fDE|apply: fF].
Qed.

(** Injections *)

Lemma trivIset_inj T I (D : set I) (F : I -> set T) :
  (forall i, D i -> F i !=set0) -> trivIset D F -> set_inj D F.
Proof.
move=> FN0 Ftriv i j; rewrite !inE => Di Dj Fij.
by apply: Ftriv Di (Dj) _; rewrite Fij setIid; apply: FN0.
Qed.

(** Bijections *)

Section set_bij_lemmas.
Context {aT rT : Type} {A : set aT} {B : set rT} {f : aT -> rT}.
Definition fun_set_bij of set_bij A B f := f.
Context (fbij : set_bij A B f).
Local Notation g := (fun_set_bij fbij).

Lemma set_bij_inj : {in A &, injective f}. Proof. by case: fbij. Qed.

Lemma set_bij_homo : {homo f : x / A x >-> B x}.  Proof. by case: fbij. Qed.

Lemma set_bij_sub : f @` A `<=` B. Proof. exact/image_subP/set_bij_homo. Qed.

Lemma set_bij_surj : set_surj A B f. Proof. by case: fbij. Qed.

HB.instance Definition _ : OCanV _ _ _ _ g := set_bij_surj.
HB.instance Definition _ := isFun.Build _ _ A B g set_bij_homo.
HB.instance Definition _ := SurjFun_Inj.Build _ _ A B g set_bij_inj.

End set_bij_lemmas.
Coercion fun_set_bij : set_bij >-> Funclass.

Coercion set_bij_bijfun aT rT (A : set aT) (B : set rT) (f : aT -> rT)
    (fS : set_bij A B f) := Bij.on (fun_set_bij fS).

Section Pbij.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fbij : set_bij A B f).
#[local] HB.instance Definition _ : @Bij _ _ A B f := fbij.
Definition bij_of_set_bijection := [bij of f].
Lemma Pbij : {s : {bij A >-> B} | f = s}. Proof. by exists [bij of f]. Qed.
End Pbij.
Coercion bij_of_set_bijection : set_bij >-> Bij.type.

Lemma bij {aT rT} {A : set aT} {B : set rT} {f : {bij A >-> B}} : set_bij A B f.
Proof. split=> //. Qed.
Definition phant_bij aT rT (A : set aT) (B : set rT) (f : {bij A >-> B}) of
  phantom (_ -> _) f := @bij _ _ _ _ f.
Notation "''bij_' f" := (phant_bij (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (set_bij _ _ _) => solve [apply: bij] : core.

Section PbijTT.
Context {aT rT} {f : aT -> rT} (fbijTT : bijective f).
#[local] HB.instance Definition _ := @BijTT.Build _ _ f fbijTT.
Definition bijection_of_bijective := [splitbij of f].
Lemma PbijTT : {s : {splitbij [set: aT] >-> [set: rT]} | f = s}.
Proof. by exists [splitbij of f]. Qed.
End PbijTT.

Lemma setTT_bijective aT rT (f : aT -> rT) :
  set_bij [set: aT] [set: rT] f = bijective f.
Proof.
apply/propext; split=> [[]|/PbijTT[{}f ->]].
  move=> _ fI /(_ _ I)-/(_ _)/cid2-/all_sig2[g _ gK].
  by exists g => // x; apply: fI; rewrite ?inE.
by split=> // [x y _ _ /'inj_f//|y _]; exists (f^-1 y) => //; rewrite funK.
Qed.

Lemma bijTT {aT rT}  {f : {bij [set: aT] >-> [set: rT]}} : bijective f.
Proof. by rewrite -setTT_bijective. Qed.
Definition phant_bijTT aT rT (f : {bij [set: aT] >-> [set: rT]})
   of phantom (_ -> _) f := @bijTT _ _ f.
Notation "''bijTT_'  f" := (phant_bijTT (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (bijective _) => solve [apply: bijTT] : core.

(**md**************************************************************************)
(* ## Patching and restrictions                                               *)
(******************************************************************************)

Section patch.
Context {aT rT : Type} (d : aT -> rT) (A : set aT).
Definition patch (f : aT -> rT) u := if u \in A then f u else d u.

Lemma patchT f : {in A, patch f =1 f}. Proof. by rewrite /patch => x ->. Qed.
Lemma patchN f : {in [predC A], patch f =1 d}.
Proof. by rewrite /patch => x /negPf/= ->. Qed.
Lemma patchC f : {in ~` A, patch f =1 d}.
Proof. by move=> u /set_mem/= NAu; rewrite patchN ?inE//= notin_setE. Qed.

HB.instance Definition _ f :=
  SurjFun.copy (patch f) [fun patch f in A].

Section inj.
Context (f : {inj A >-> rT}).
Let g := patch f.
Lemma patch_inj_subproof : Inj aT rT A g.
Proof. by split=> x y xA yA; rewrite /g !patchT//; apply: inj. Qed.
HB.instance Definition _ := patch_inj_subproof.
HB.instance Definition _ := Inject.copy (patch f) [fun g in A].
End inj.

End patch.
Notation restrict := (patch (fun=> point)).
Notation "f \_ D" := (restrict D f) : function_scope.

Lemma patchE aT (rT : pointedType) (f : aT -> rT) (B : set aT) x :
  (f \_ B) x = if x \in B then f x else point.
Proof. by []. Qed.

Lemma patch_pred {I T} (D : {pred I}) (d f : I -> T) :
  patch d D f = fun i => if D i then f i else d i.
Proof. by apply/funext => i; rewrite /patch mem_setE. Qed.

Lemma preimage_restrict (aT : Type) (rT : pointedType)
     (f : aT -> rT) (D : set aT) (B : set rT) :
  (f \_ D) @^-1` B = (if point \in B then ~` D else set0) `|` D `&` f @^-1` B.
Proof.
rewrite /preimage/= /patch; apply/predeqP => x /=; split.
  case: ifPn; rewrite ?(inE, notin_setE); first by right.
  by move=> NDx Bp; rewrite ifT ?inE//=; left.
move=> [|[Dx Bfx]]; last by rewrite ifT ?inE.
by case: ifP; rewrite // inE => Bp NDx; case: ifPn; rewrite // inE.
Qed.

Lemma comp_patch {aT rT sT : Type} (g : aT -> rT) D (f : aT -> rT) (h : rT -> sT) :
  h \o patch g D f = patch (h \o g) D (h \o f).
Proof. by apply/funext => x; rewrite /patch/=; case: ifP. Qed.

Lemma patch_setI {aT rT : Type} (g : aT -> rT) D D' (f : aT -> rT) :
   patch g (D `&` D') f = patch g D (patch g D' f).
Proof.
apply/funext => x; rewrite /patch/= in_setI.
by case: (x \in D) (x \in D') => [] [].
Qed.

Lemma patch_set0 {aT rT : Type} (g : aT -> rT) (f : aT -> rT) :
  patch g set0 f = g.
Proof. by apply/funext => x; rewrite /patch in_set0. Qed.

Lemma patch_setT {aT rT : Type} (g : aT -> rT) (f : aT -> rT) :
  patch g setT f = f.
Proof. by apply/funext => x; rewrite /patch in_setT. Qed.

Lemma restrict_comp {aT} {rT sT : pointedType} (h : rT -> sT) (f : aT -> rT) D :
  h point = point -> (h \o f) \_ D = h \o (f \_ D).
Proof. by move=> hp; apply/funext => x; rewrite /patch/=; case: ifP. Qed.
Arguments restrict_comp {aT rT sT} h f D.

Lemma trivIset_restr (T I : Type) (D D' : set I) (F : I -> set T) :
    trivIset D' (F \_ D) = trivIset (D `&` D') F.
Proof.
apply/propext; split=> FDtriv i j.
  move=> [Di D'i] [Dj D'j] [x [Fix Fjx]]; apply: FDtriv => //.
  by exists x; split => /=; rewrite ?patchT ?in_setE.
move=> D'i D'j [x []]; rewrite /patch.
do 2![case: ifPn => //]; rewrite !in_setE => Di Dj Fix Fjx.
by apply: FDtriv => //; exists x.
Qed.

(**md**************************************************************************)
(* ## Restriction of domain and codomain                                      *)
(******************************************************************************)

Section RestrictionLeft.
Context {U V : Type} (v : V) {A : set U} {B : set V}.

Local Notation restrict := (patch (fun=> v) A).

Definition sigL (f : U -> V) : A -> V := f \o set_val.

Lemma sigL_isfun (f : {fun A >-> B}) : isFun _ _ [set: A] B (sigL f).
Proof. by split=> x _; apply: funS. Qed.
HB.instance Definition _ (f : {fun A >-> B}) := sigL_isfun f.

Definition sigLfun (f : {fun A >-> B}) := [fun of sigL f].
Definition valL_ (f : A -> V) : U -> V := ((@oapp _ _)^~ v) f \o 'oinv_set_val.

Lemma valL_isfun (f : {fun [set: A] >-> B}) :
  isFun _ _ A B (valL_ (f : _ -> _)).
Proof. by split=> x Ax; apply: funS. Qed.
HB.instance Definition _ (f : {fun [set: A] >-> B}) := valL_isfun f.
Definition valLfun_ (f : {fun [set: A] >-> B}) := [fun of valL_ f].

Lemma sigLE (f : U -> V) x (xA : x \in A) :
  sigL f (SigSub xA) = f x.
Proof. done. Qed.

Lemma eq_sigLP (f g : U -> V):
  {in A, f =1 g} <-> sigL f = sigL g.
Proof.
split=> [eq_f_g | Rfg u uA]; first by apply/funext => -[x]; apply: eq_f_g.
by have := congr1 (@^~ (exist _ u uA)) Rfg.
Qed.

Lemma eq_sigLfunP (f g : {fun A >-> B}) :
  {in A, f =1 g} <-> sigLfun f = sigLfun g.
Proof. by rewrite eq_sigLP funP funeqP. Qed.

Lemma sigLK : valL_ \o sigL = restrict.
Proof.
rewrite funeq2E => f u; rewrite /valL_ /sigL /restrict.
by rewrite oinv_set_val/=; case: ifPn => uA; [rewrite insubT|rewrite insubN].
Qed.

Lemma valLK : cancel valL_ sigL.
Proof.
move=> f; rewrite /valL_ /sigL /restrict oinv_set_val.
apply/funext=> a /=; have aA : set_val a \in A by apply: valP.
by rewrite insubT//=; congr f; apply/val_inj.
Qed.

Lemma valLfunK : cancel valLfun_ sigLfun.
Proof. by move=> f; apply/funP/funeqP; exact: valLK. Qed.

Lemma sigL_valL : sigL \o valL_ = id.
Proof. exact/funext/valLK. Qed.

Lemma sigL_valLfun : sigLfun \o valLfun_ = id.
Proof. exact/funext/valLfunK. Qed.

Lemma sigL_restrict : sigL \o restrict = sigL.
Proof.
rewrite funeq2E => f -[u Au] /=.
by rewrite /sigL /restrict /valL_ /patch /= Au.
Qed.

Lemma image_sigL  : range sigL = setT.
Proof.
rewrite eqEsubset; split=> //= f _; exists (valL_ f)=>//.
exact: valLK.
Qed.

Lemma eq_restrictP (f g : U -> V): {in A, f =1 g} <-> restrict f = restrict g.
Proof. by rewrite eq_sigLP -sigLK/=; split => [->//|/(can_inj valLK)]. Qed.

End RestrictionLeft.
Arguments sigL {U V} A f u /.
Arguments sigLE {U V} A f x.
Arguments valL_ {U V} v {A} f u /.
Notation "''valL_' v" := (valL_ v) : form_scope.
Notation "''valLfun_' v" := (valLfun_ v) : form_scope.
Notation valL := (valL_ point).

Section RestrictionRight.
Context {U V : Type} {A : set V}.

Definition sigR (f : {fun [set: U] >-> A}) (u : U) : A :=
  SigSub (mem_set ('funS_f I) : f u \in A).
HB.instance Definition _ f := Fun.copy (sigR f) (totalfun _).

Definition valR (f : U -> A) := set_val \o totalfun f.
HB.instance Definition _ f := Fun.on (valR f).

Definition valR_fun (f : U -> A) : {fun [set: U] >-> A} := [fun of valR f].

Lemma sigRK (f : {fun [set: U] >-> A}) : valR (sigR f) = f.
Proof. by []. Qed.

Lemma sigR_funK (f : {fun [set: U] >-> A}) : valR_fun (sigR f) = f.
Proof. by apply/funP/funeqP; apply: sigRK. Qed.

Lemma valRP (f : U -> A) x : A (valR f x). Proof. exact: set_valP. Qed.

Lemma valRK : cancel valR_fun sigR.
Proof. by move=> f; apply/funext => x; apply/val_inj. Qed.

End RestrictionRight.
Arguments sigR {U V A} f u /.

Section RestrictionLeftInv.
Context {U V : Type} (v : V) {A : set U} {B : set V}.
Local Notation rl := (sigL A).
Local Notation rr := sigR.
Local Notation el := 'valL_v.
Local Notation er := valR.

HB.instance Definition _ (f : {oinv U >-> V}) :=
  @OInv.Build _ _ (rl f) (obind insub \o 'oinv_f).
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (rl f).

Lemma oinv_sigL (f : {oinv U >-> V}) : 'oinv_(rl f) = obind insub \o 'oinv_f.
Proof. by []. Qed.

Lemma sigL_inj_subproof (f : {inj A >-> V}) : @OInv_Can _ _ setT (rl f).
Proof.
by split=> x _; rewrite oinv_sigL/= funoK//= [insub _]'funoK_val ?inE.
Qed.
HB.instance Definition _ f := sigL_inj_subproof f.
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (rl f).

Lemma sigL_surj_subproof (f : {surj A >-> B}) : @OInv_CanV _ _ setT B (rl f).
Proof.
split=> [b|b /set_mem] Bb; rewrite ?oinv_sigL/=.
   have [x /mem_set Ax <-]/= := 'oinvS_f Bb; exists (SigSub Ax) => //=.
   case: insubP => [a Aa/= eqx|]; last by rewrite Ax.
   by congr Some; apply/val_inj.
by rewrite /rl/= oapp_comp/= -oinv_val -inv_omap/= invK ?oinvK ?mem_fun ?inE.
Qed.
HB.instance Definition _ f := sigL_surj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (rl f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (rl f).

HB.instance Definition _ (f : {oinvfun [set: V] >-> A}) :=
  @OInv.Build _ _ (rr f) (rl 'oinv_f).

Lemma oinv_sigR (f : {oinvfun [set: V] >-> A}) :
  'oinv_(rr f) = (rl 'oinv_f).
Proof. by []. Qed.

Lemma sigR_inj_subproof (f : {injfun [set: V] >-> A}) :
   @OInv_Can _ _ setT (rr f).
Proof. by split=> x _; rewrite oinv_sigR/= set_valE/= funoK ?inE. Qed.
HB.instance Definition _ f := sigR_inj_subproof f.

Lemma sigR_surj_subproof (f : {surjfun [set: V] >-> A}) :
  @OInv_CanV _ _ setT setT (rr f).
Proof.
split=> a _; rewrite ?oinv_sigL/=.
  by have [x _ xeq] := 'oinvS_f (set_valP a); exists x.
apply/val_inj=> /=; rewrite oinv_sigR/=.
by case: oinvP=> //=; apply: set_valP.
Qed.
HB.instance Definition _ f := sigR_surj_subproof f.

Lemma sigR_some_inv (f : {invfun [set: V] >-> A}) :
  olift (rl f^-1) = 'oinv_(rr f).
Proof. by rewrite oinv_sigR olift_comp oliftV. Qed.
HB.instance Definition _ (f : {bij [set: V] >-> A}) := Fun.on (rr f).

HB.instance Definition _ (f : {invfun [set: V] >-> A}) :=
   @OInv_Inv.Build _ _ (rr f) (rl f^-1) (sigR_some_inv f).

Lemma inv_sigR (f : {invfun [set: V] >-> A}) : (rr f)^-1 = (rl f^-1).
Proof. by []. Qed.

HB.instance Definition _ (f : {splitinjfun [set: V] >-> A}) := Inject.on (rr f).
(* HB Bug, if Fun.on instead of Surject.on *)
HB.instance Definition _ (f : {splitsurjfun [set: V] >-> A}) := Surject.on (rr f).
HB.instance Definition _ (f : {splitbij [set: V] >-> A}) := Fun.on (rr f).

Lemma sigL_some_inv (f : {splitbij A >-> [set: V]}) :
  olift (rr [fun of f^-1]) = 'oinv_(rl f).
Proof.
apply/funext=> x /=; rewrite oinv_sigL /= /sigR/= /olift/=.
case: oinvP => //= u Au _; rewrite insubT ?inE// => memAu.
by congr (Some _); apply/val_inj=> /=; rewrite funK.
Qed.
HB.instance Definition _ (f : {splitbij A >-> [set: V]}) :=
  OInv_Inv.Build _ _ (rl f) (sigL_some_inv f).

Lemma inv_sigL  (f : {splitbij A >-> [set: V]}) :
  (rl f)^-1 = (rr [fun of f^-1]).
Proof. by []. Qed.

HB.instance Definition _ (f : {oinv A >-> V}) :=
  @OInv.Build _ _ (el f) (omap set_val \o 'oinv_f).
HB.instance Definition _ (f : {oinvfun [set: A] >-> B}) := Fun.on (el f).

Lemma oinv_valL (f : {oinv A >-> V}) :
  'oinv_(el f) = omap set_val \o 'oinv_f.
Proof. by []. Qed.

Lemma oapp_comp_x {aT rT sT} (f : aT -> rT) (g : rT -> sT) (x : rT) y :
  oapp (g \o f) (g x) y = g (oapp f x y).
Proof. by case: y. Qed.

Lemma valL_inj_subproof (f : {inj [set: A] >-> V}) : @OInv_Can _ _ A (el f).
Proof.
split=> x /set_mem xA; rewrite oinv_valL/= -oapp_comp_x.
by case: oinvP=> //= a _ _; rewrite funoK ?inE.
Qed.
HB.instance Definition _ f := valL_inj_subproof f.
HB.instance Definition _ (f : {injfun [set: A] >-> B}) := Inject.on (el f).

Lemma valL_surj_subproof (f : {surj [set: A] >-> B}) : @OInv_CanV _ _ A B (el f).
Proof.
split=> [b|b /set_mem] Bb; rewrite ?oinv_valL/=.
  by case: oinvP => // => a; exists (set_val a) => //; apply: set_valP.
by case: oinvP => //= a _ _; rewrite funoK// inE.
Qed.
HB.instance Definition _ f := valL_surj_subproof f.
HB.instance Definition _ (f : {surjfun [set: A] >-> B}) := Surject.on (el f).
HB.instance Definition _ (f : {bij [set: A] >-> B}) := Surject.on (el f).

Lemma valL_some_inv (f : {inv A >-> V}) : olift (er f^-1) = 'oinv_(el f).
Proof. by rewrite oinv_valL/= olift_comp -oliftV. Qed.
HB.instance Definition _ (f : {inv A >-> V}) :=
  OInv_Inv.Build _ _ (el f) (valL_some_inv f).
HB.instance Definition _ (f : {invfun [set: A] >-> B}) := Fun.on (el f).

Lemma inv_valL (f : {inv A >-> V}) : (el f)^-1 = er f^-1.
Proof. by []. Qed.

HB.instance Definition _ (f : {splitinj [set: A] >-> V}) := Inject.on (el f).
HB.instance Definition _ (f : {splitinjfun [set: A] >-> B}) := Fun.on (el f).
(* HB Bug, if Fun.on instead of Surject.on *)
HB.instance Definition _ (f : {splitsurj [set: A] >-> B}) := Surject.on (el f).
HB.instance Definition _ (f : {splitsurjfun [set: A] >-> B}) := Fun.on (el f).
HB.instance Definition _ (f : {splitbij [set: A] >-> B}) := Fun.on (el f).

Lemma sigL_injP (f : U -> V) :
  injective (rl f) <-> {in A &, injective f}.
Proof.
split=> [f_inj x y Ax Ay|/Pinj[{}f-> //]]; last first.
by move=> eqfxy; suff [->] : SigSub Ax = SigSub Ay by []; apply: f_inj.
Qed.

Lemma sigL_surjP (f : U -> V) :
  set_surj [set: A] B (rl f) <-> set_surj A B f.
Proof.
split=> [fsurj b Bb/=|/Psurj[{}f->]//].
by have [a _ <-] := fsurj _ Bb; exists (set_val a) => //; apply: set_valP.
Qed.

Lemma sigL_funP (f : U -> V) :
  set_fun [set: A] B (rl f) <-> set_fun A B f.
Proof.
split=> [ffun u Au/=|/Pfun[{}f->]//].
exact: (ffun (SigSub (mem_set Au))).
Qed.

Lemma sigL_bijP (f : U -> V) :
  set_bij [set: A] B (rl f) <-> set_bij A B f.
Proof.
split=> [[F /in2TT I S]|/Pbij[{}f->]//].
by split; [exact/sigL_funP|exact/sigL_injP|exact/sigL_surjP].
Qed.

Lemma valL_injP (f : A -> V) : {in A &, injective (el f)} <-> injective f.
Proof. by rewrite -sigL_injP valLK. Qed.

Lemma valL_surjP (f : A -> V) :
  set_surj A B (el f) <-> set_surj setT B f.
Proof. by rewrite -sigL_surjP valLK. Qed.

Lemma valLfunP (f : A -> V) :
  set_fun A B (el f) <-> set_fun setT B f.
Proof. by rewrite -sigL_funP valLK. Qed.

Lemma valL_bijP (f : A -> V) :
  set_bij A B (el f) <-> set_bij setT B f.
Proof. by rewrite -sigL_bijP valLK. Qed.

End RestrictionLeftInv.

Section ExtentionLeftInv.
Context {U V : Type} {A : set U} {B : set V}.
Local Notation el := 'valL_None.
Local Notation er := valR.

HB.instance Definition _ (f : {oinv V >-> A}) :=
  @OInv.Build _ _ (er f) (el 'oinv_f).

Lemma oinv_valR (f : {oinv V >-> A}) : 'oinv_(er f) = (el 'oinv_f).
Proof. by []. Qed.

Lemma valR_inj_subproof (f : {inj [set: V] >-> A}) :
   @OInv_Can _ _ setT (er f).
Proof. by split=> x _; rewrite /er oinv_valR/= funoK/= ?funoK ?inE. Qed.
HB.instance Definition _ f := valR_inj_subproof f.

Lemma valR_surj_subproof (f : {surj [set: V] >-> [set: A]}) :
  @OInv_CanV _ _ setT A (er f).
Proof.
split=> [a|a /set_mem] Aa; rewrite ?oinv_valR/= oinv_set_val.
  by rewrite insubT ?inE// => memaA /=; case: oinvP => //= x; exists x.
rewrite insubT ?inE// => memaA/=; case: oinvP => //= x _.
by rewrite /er/= /totalfun => ->.
Qed.
HB.instance Definition _ f := valR_surj_subproof f.
HB.instance Definition _ (f : {bij [set: V] >-> [set: A]}) := Fun.on (er f).

End ExtentionLeftInv.

Section Restrictions2.
Context {U V : Type} (v : V) {A : set U} {B : set V}.

Local Notation valL := 'valL_v.
Local Notation valLfun := 'valLfun_v.

Definition sigLR := sigR \o (@sigLfun U V A B).

HB.instance Definition _ (f : {fun A >-> B}) :=
  Fun.copy (sigLR f) (totalfun _).

Definition valLR : (A -> B) -> U -> V := valL \o valR_fun.
Definition valLRfun : (A -> B) -> {fun A >-> B} := valLfun \o valR_fun.

Lemma valLRE (f : A -> B) : valLR f = valL (valR f). Proof. by []. Qed.
Lemma valLRfunE (f : A -> B) : valLRfun f = [fun of valLR f]. Proof. by []. Qed.

Lemma sigL2K (f : {fun A >-> B}) : {in A, valLR (sigLR f) =1 f}.
Proof. by apply/eq_sigLP; rewrite valLK sigR_funK. Qed.

Lemma valLRK : cancel valLRfun sigLR.
Proof. by move=> f; rewrite /sigLR /valLR /= valLfunK valRK. Qed.

Lemma valLRfun_inj : injective valLRfun.
Proof. by move=> f g eqefg; rewrite -[LHS]valLRK eqefg valLRK. Qed.

HB.instance Definition _ (f : {oinvfun A >-> B}) := OInversible.on (sigLR f).
HB.instance Definition _ (f : {injfun A >-> B}) := Inject.on (sigLR f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Surject.on (sigLR f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (sigLR f).

HB.instance Definition _ (f : {oinv A >-> B}) := OInvFun.on (valLR f).
HB.instance Definition _ (f : {inj [set: A] >-> B}) := Inject.on (valLR f).
HB.instance Definition _ (f : {surj [set: A] >-> [set: B]}) := Surject.on (valLR f).
HB.instance Definition _ (f : {bij [set: A] >-> [set: B]}) := Fun.on (valLR f).

Lemma sigLR_injP (f : {fun A >-> B}) :
  injective (sigLR f) <-> {in A &, injective f}.
Proof.
split=> [f_inj x y Ax Ay|/funPinj[{}f-> //]]; last first.
move=> eqfxy; suff [->] : SigSub Ax = SigSub Ay by [].
by apply: f_inj; apply/val_inj.
Qed.

Lemma valLR_injP (f : A -> B) :
  {in A &, injective (valLR f)} <-> injective f.
Proof. by rewrite -sigLR_injP valLRK. Qed.

Lemma sigLR_surjP (f : {fun A >-> B}) :
  set_surj setT setT (sigLR f) <-> set_surj A B f.
Proof.
split=> [fsurj b Bb/=|/funPsurj[{}f->]//].
have [x _ /(congr1 val)/= <-] := fsurj (SigSub (mem_set Bb)) I.
by exists (set_val x) => //; apply: set_valP.
Qed.

Lemma valLR_surjP (f : A -> B) :
  set_surj A B (valLR f) <-> set_surj setT setT f.
Proof. by rewrite -sigLR_surjP valLRK. Qed.

Lemma sigLR_bijP (f : U -> V) :
  set_bij A B f <->
  exists (fAB : {homo f : x / A x >-> B x}),
    bijective (sigLR [fun of mkfun fAB]).
Proof.
split=> [[F I S]|[fAB]].
  exists F; rewrite -setTT_bijective.
  by split; [|apply: in2W; apply/sigLR_injP|apply/sigLR_surjP].
rewrite -setTT_bijective /set_bij.
set g := [fun of mkfun fAB] => -[_ /in2TT I S]; pose h : _ -> _ := g.
rewrite -[f]/h {}/h; move: g => g in I S *.
by split; [apply/image_subP|apply/sigLR_injP|apply/sigLR_surjP].
Qed.

Lemma sigLRfun_bijP f : bijective (sigLR f) <-> set_bij A B f.
Proof.
rewrite sigLR_bijP; split=> [fbij|[fAB]]; [exists funS|];
by rewrite (_ : [fun of _] = f)//; apply/funP.
Qed.

Lemma valLR_bijP f : set_bij A B (valLR f) <-> bijective f.
Proof. by rewrite -sigLRfun_bijP valLRK. Qed.

End Restrictions2.

Section set_bij_basic_lemmas.
Context {aT rT : Type}.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma eq_set_bijRL A B f g : {in A, f =1 g} -> set_bij A B f -> set_bij A B g.
Proof. by move=> /eq_sigLP + /sigL_bijP => -> /sigL_bijP. Qed.

Lemma eq_set_bijLR A B f g : {in A, f =1 g} -> set_bij A B g -> set_bij A B f.
Proof. by move=> /eq_sigLP + /sigL_bijP => <- /sigL_bijP. Qed.

Lemma eq_set_bij A B f g : {in A, f =1 g} -> set_bij A B f = set_bij A B g.
Proof.
by move=> eqfg; apply/propeqP; split; [apply: eq_set_bijRL | apply: eq_set_bijLR].
Qed.

Lemma bij_omap A B f :
  set_bij (some @` A) (some @` B) (omap f) <-> set_bij A B f.
Proof.
split=> [/Pbij[b mapfb]|/Pbij[{}f->//]].
suff -> : f = unbind f (b \o some) :> (_ -> _) by [].
by apply/funext=> x; rewrite -mapfb.
Qed.

Lemma bij_olift A B f : set_bij A (some @` B) (olift f) <-> set_bij A B f.
Proof.
split=> [/Pbij[b liftfb]|/Pbij[{}f->//]].
suff -> : f = unbind f b :> (_ -> _) by [].
by apply/funext=> x; rewrite -liftfb.
Qed.

End set_bij_basic_lemmas.

Lemma bij_sub_sym {aT rT} {A C : set aT} {B D : set rT}
    (f : {bij A >-> B}) : C `<=` A -> D `<=` B ->
  set_bij D (some @` C) 'oinv_f <-> set_bij C D f.
Proof.
move=> CA DB; gen have oinv_bij : aT rT A C B D CA DB f /
    set_bij C D f -> set_bij D (some @` C) 'oinv_f; last first.
  split=> bij_oinv; last exact: oinv_bij.
  by apply/bij_omap; rewrite -oinvV; apply: oinv_bij => //; apply: image_subset.
move=> /Pbij[fC ffC]; suff /eq_set_bij-> : {in D, 'oinv_f =1 'oinv_fC} by [].
move=> x xD; apply: 'inj_(oapp f x); rewrite ?mem_fun//=.
- by apply/subsetP : x xD.
- by have := mem_set ((image_subset CA) _ ('oinvS_fC (set_mem xD))).
by rewrite oinvK ?ffC ?oinvK// ?(subsetP.2 _ _ xD).
Qed.

Lemma splitbij_sub_sym {aT rT} {A C : set aT} {B D : set rT}
    (f : {splitbij A >-> B}) : C `<=` A -> D `<=` B ->
  set_bij D C f^-1 <-> set_bij C D f.
Proof. by move=> CA DB; rewrite -bij_sub_sym// -oliftV bij_olift. Qed.

Section set_bij_lemmas.
Context {aT rT : Type}.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma set_bij00 T U (f : T -> U) : set_bij set0 set0 f.
Proof. by split=> [_ []//|x y|//]; rewrite inE. Qed.
Hint Resolve set_bij00 : core.

Lemma inj_bij A f : {in A &, injective f} -> set_bij A (f @` A) f.
Proof. by move=> /Pinj[{}f->]; apply: 'bij_[fun f in A]. Qed.

Lemma bij_subl A B C D (f : {bij A >-> B}) : C `<=` A -> f @` C = D ->
  set_bij C D f.
Proof. by move=> /homo_setP CA <-; split=> // x y /CA + /CA +; apply: inj. Qed.

End set_bij_lemmas.

Section set_bij_lemmas.
Context {aT rT : Type}.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma bij_subr A B C D (f : {bij A >-> B}) : C = A `&` (f @^-1` D) -> D `<=` B ->
  set_bij C D f.
Proof.
move=> -> DB; apply/bij_sub_sym=> //; apply: bij_subl => //=.
by rewrite oinv_sub_image.
Qed.

Lemma bij_sub A B C D (f : {bij A >-> B}) : C `<=` A -> D `<=` B ->
    {homo f : x / C x >-> D x} ->
    {homo 'oinv_f : x / D x >-> (some @` C) x} ->
  set_bij C D f.
Proof.
move=> CA DB fCD fDC; apply: bij_subl => //; apply/seteqP; split.
  by apply/image_subP.
move=> y /[dup]/[dup] Dy /DB By /fDC [x Cx]/= xfy; exists x => //; move: xfy.
by case: oinvP => // a Aa _ [->].
Qed.

Lemma splitbij_sub A B C D (f : {splitbij A >-> B}) : C `<=` A -> D `<=` B ->
    {homo f : x / C x >-> D x} ->
    {homo f^-1 : x / D x >-> C x} ->
  set_bij C D f.
Proof.
move=> CA DB /(bij_sub CA DB) /[swap] fDC; apply=> x Dx.
by rewrite -some_inv/=; exists (f^-1 x) => //; apply: fDC.
Qed.

Lemma can2_bij A B (f : {fun A >-> B}) (g : {fun B >-> A}) :
  {in A, cancel f g} -> {in B, cancel g f} -> set_bij A B f.
Proof. by move=> /can_in_inj finj /can_surj gK; split => //; apply: gK. Qed.

Lemma bij_sub_setUrl A B B' f : [disjoint B & B'] ->
  set_bij A (B `|` B') f -> set_bij (A `\` f @^-1` B') B f.
Proof.
move=> /disj_setPS BB' /Pbij[{}f->]; apply: bij_subr; last exact: subsetUl.
apply/seteqP; split=> x /= [Ax Bfx]; split=> //; first by have [] := 'funS_f Ax.
by move=> B'fx; apply: (BB' (f x)).
Qed.

Lemma bij_sub_setUrr A B B' f : [disjoint B & B'] ->
  set_bij A (B `|` B') f -> set_bij (A `\` f @^-1` B) B' f.
Proof. by rewrite setUC disj_set_sym; apply: bij_sub_setUrl. Qed.

Lemma bij_sub_setUll A A' B f : [disjoint A & A'] ->
  set_bij (A `|` A') B f -> set_bij A (B `\` f @` A') f.
Proof.
move=> /disj_setPS AA' /Pbij[{}f->].
apply: bij_sub => [|? []//||]; first exact: subsetUl.
  move=> x Ax /=; split; first by apply: funS; left.
  move=> [y] A'y /inj; rewrite !inE/= =>yx; apply: (AA' x).
  by split=> //; rewrite -yx //; [right|left].
move=> z [Bz /= /not_exists2P /contrapT] A'fxz.
case: oinvP=> // x AA'x fxz; exists x => //.
by have := A'fxz x; rewrite fxz => -[|//]; case: AA'x.
Qed.

Lemma bij_sub_setUlr A A' B f : [disjoint A & A'] ->
  set_bij (A `|` A') B f -> set_bij A' (B `\` f @` A) f.
Proof. by rewrite setUC disj_set_sym; apply: bij_sub_setUll. Qed.

End set_bij_lemmas.

Lemma bij_II_D1 T n (A : set T) (f : nat -> T) :
  set_bij `I_n.+1 A f -> set_bij `I_n (A `\ f n) f.
Proof.
rewrite IIS -image_set1; apply: bij_sub_setUll.
by apply/disj_setPS => i [/= /[swap]->]; rewrite ltnn.
Qed.

Lemma set_bij_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g :
  set_bij A B f -> set_bij B C g -> set_bij A C (g \o f).
Proof. by move=> /Pbij[{}f->] /Pbij[{}g->]; apply: 'bij_(g \o f). Qed.

Section pointed_inverse.
Context {T U} (dflt : U -> T) (A : set T).
Implicit Types (f : T -> U) (i : {inj A >-> U}).

Definition pinv_ f := ('split_dflt [fun f in A])^-1.
Local Notation pinv := pinv_.
HB.instance Definition _ f := Inv.Build _ _ (pinv f) f.
HB.instance Definition _ f := Fun.on (pinv f).
HB.instance Definition _ f := SplitInjFun.on (pinv f).
HB.instance Definition _ i := SplitBij.on (pinv i).

Lemma pinvK f : {in f @` A, cancel (pinv f) f}.
Proof. exact: 'funK_(pinv f). Qed.

Lemma pinvKV f : {in A &, injective f} -> {in A, cancel f (pinv f)}.
Proof. by move=> /Pinj[{}f->]; apply: funK. Qed.

Lemma injpinv_surj f : {in A &, injective f} ->
  set_surj (f @` A) A (pinv f).
Proof. by move=> /Pinj[{}f->]; apply: surj. Qed.

Lemma injpinv_image f : {in A &, injective f} ->
  pinv f @` (f @` A) = A.
Proof. by move=> /Pinj[{}f->]; rewrite image_eq. Qed.

Lemma injpinv_bij f : {in A &, injective f} ->
  set_bij (f @` A) A (pinv f).
Proof. by move=> /Pinj[{}f->]; apply: bij. Qed.

Lemma surjpK B f : set_surj A B f -> {in B, cancel (pinv f) f}.
Proof. by move=> /homo_setP BfA; move=> x /BfA xfA; rewrite pinvK. Qed.

Lemma surjpinv_image_sub B f : set_surj A B f -> pinv f @` B `<=` A.
Proof. by move=> fsurj; apply: (subset_trans (image_subset fsurj)). Qed.

Lemma surjpinv_inj B f : set_surj A B f -> {in B &, injective (pinv f)}.
Proof. by move=> /homo_setP/sub_in2; apply. Qed.

Lemma surjpinv_bij B f (g := pinv f) : set_surj A B f ->
  set_bij B (g @` B) g.
Proof. by move=> f_surj; split=> //; apply: surjpinv_inj. Qed.

Lemma bijpinv_bij B f : set_bij A B f -> set_bij B A (pinv f).
Proof. by move=> /Pbij[{}f->]; have /= := 'bij_(pinv f); rewrite image_eq. Qed.

Section pPbij.
Context {B: set U} {f : T -> U} (fbij : set_bij A B f).
Lemma pPbij_ : {s : {splitbij A >-> B} | f = s}.
Proof.
pose h := [splitbij of 'split_dflt [fun fbij in A]]; have : f = h by [].
by move: h; rewrite /= (image_eq fbij) => h; exists h.
Qed.
End pPbij.

Section pPinj.
Context {f : T -> U} (finj : {in A &, injective f}).
Lemma pPinj_ : {i : {splitinj A >-> U} | f = i}.
Proof.
by move: finj => /Pinj[g ->]; exists [splitinj of 'split_dflt [fun g in A]].
Qed.
End pPinj.

Section injpPfun.
Context {B : set U} {f : {inj A >-> U}} (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := SplitInj.copy g ('split_dflt [fun g in A]).
#[local] HB.instance Definition _ := isFun.Build _ _ _ _ g ffun.
Lemma injpPfun_ : {i : {splitinjfun A >-> B} | f = i :> (_ -> _)}.
Proof. by exists [splitinjfun of g]. Qed.
End injpPfun.

Section funpPinj.
Context {B : set U} {f : {fun A >-> B}} (finj : {in A &, injective f}).
Lemma funpPinj_ : {i : {splitinjfun A >-> B} | f = i :> (_ -> _)}.
Proof. by move: finj 'funS_f => /pPinj_[g ->]/injpPfun_. Qed.
End funpPinj.

End pointed_inverse.
Notation "''pinv_' dflt" := (pinv_ dflt) : form_scope.
Notation pinv := 'pinv_(fun=> point).
Notation "''pPbij_' dflt" := (pPbij_ dflt) : form_scope.
Notation pPbij := 'pPbij_(fun=> point).
Notation selfPbij := 'pPbij_id.
Notation "''pPinj_' dflt" := (pPinj_ dflt) : form_scope.
Notation pPinj := 'pPinj_(fun=> point).
Notation "''injpPfun_' dflt" := (injpPfun_ dflt) : form_scope.
Notation injpPfun := 'injpPfun_(fun=> point).
Notation "''funpPinj_' dflt" := (funpPinj_ dflt) : form_scope.
Notation funpPinj := 'funpPinj_(fun=> point).

Section function_space.
Local Open Scope ring_scope.
Import GRing.Theory.

Definition cst {T T' : Type} (x : T') : T -> T' := fun=> x.

Lemma preimage_cst {aT rT : Type} (a : aT) (A : set aT) :
  @cst rT _ a @^-1` A = if a \in A then setT else set0.
Proof.
apply/seteqP; rewrite /preimage; split; first by move=> *; rewrite mem_set.
by case: ifPn => [/[!inE] ?//|_]; exact: sub0set.
Qed.

Obligation Tactic := idtac.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @GRing.isZmodule.Build (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g)
     _ _ _ _.
Next Obligation. by move=> T M f g h; rewrite funeqE=> x /=; rewrite addrA. Qed.
Next Obligation. by move=> T M f g; rewrite funeqE=> x /=; rewrite addrC. Qed.
Next Obligation. by move=> T M f; rewrite funeqE=> x /=; rewrite add0r. Qed.
Next Obligation. by move=> T M f; rewrite funeqE=> x /=; rewrite addNr. Qed.
HB.instance Definition _ (T : Type) (M : zmodType) := fct_zmodMixin T M.

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @GRing.Zmodule_isRing.Build (T -> M) (cst 1) (fun f g => f \* g) _ _ _ _ _ _.
Next Obligation. by move=> T M f g h; rewrite funeqE=> x /=; rewrite mulrA. Qed.
Next Obligation. by move=> T M f; rewrite funeqE=> x /=; rewrite mul1r. Qed.
Next Obligation. by move=> T M f; rewrite funeqE=> x /=; rewrite mulr1. Qed.
Next Obligation. by move=> T M f g h; rewrite funeqE=> x/=; rewrite mulrDl. Qed.
Next Obligation. by move=> T M f g h; rewrite funeqE=> x/=; rewrite mulrDr. Qed.
Next Obligation.
by move=> T M ; apply/eqP; rewrite funeqE => /(_ point) /eqP; rewrite oner_eq0.
Qed.
HB.instance Definition _ (T : pointedType) (M : ringType) := fct_ringMixin T M.

Program Definition fct_comRingType (T : pointedType) (M : comRingType) :=
  GRing.Ring_hasCommutativeMul.Build (T -> M) _.
Next Obligation.
by move=> T M f g; rewrite funeqE => x; rewrite /GRing.mul/= mulrC.
Qed.
HB.instance Definition _ (T : pointedType) (M : comRingType) :=
  fct_comRingType T M.

Section fct_lmod.
Variables (U : Type) (R : ringType) (V : lmodType R).
Program Definition fct_lmodMixin := @GRing.Zmodule_isLmodule.Build R (U -> V)
  (fun k f => k \*: f) _ _ _ _.
Next Obligation. by move=> k f v; rewrite funeqE=> x; exact: scalerA. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite scale1r. Qed.
Next Obligation.
by move=> f g h; rewrite funeqE => x /=; rewrite scalerDr.
Qed.
Next Obligation.
by move=> f g h; rewrite funeqE => x /=; rewrite scalerDl.
Qed.
HB.instance Definition _ := fct_lmodMixin.
End fct_lmod.

Lemma fct_sumE (I T : Type) (M : zmodType) r (P : {pred I}) (f : I -> T -> M)
    (x : T) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

Lemma mul_funC (T : Type) {R : comSemiRingType} (f : T -> R) (r : R) :
  r \*o f = r \o* f.
Proof. by apply/funext => x/=; rewrite mulrC. Qed.

End function_space.

Section function_space_lemmas.
Local Open Scope ring_scope.
Import GRing.Theory.

Lemma addrfctE (T : Type) (K : zmodType) (f g : T -> K) :
  f + g = (fun x => f x + g x).
Proof. by []. Qed.

Lemma sumrfctE (T : Type) (K : zmodType) (s : seq (T -> K)) :
  \sum_(f <- s) f = (fun x => \sum_(f <- s) f x).
Proof. by apply/funext => x;elim/big_ind2 : _ => // _ a _ b <- <-. Qed.

Lemma opprfctE (T : Type) (K : zmodType) (f : T -> K) : - f = (fun x => - f x).
Proof. by []. Qed.

Lemma mulrfctE (T : pointedType) (K : ringType) (f g : T -> K) :
  f * g = (fun x => f x * g x).
Proof. by []. Qed.

Lemma scalrfctE (T : pointedType) (K : ringType) (L : lmodType K)
    k (f : T -> L) :
  k *: f = (fun x : T => k *: f x).
Proof. by []. Qed.

Lemma cstE (T T': Type) (x : T) : cst x = fun _: T' => x.
Proof. by []. Qed.

Lemma exprfctE (T : pointedType) (K : ringType) (f : T -> K) n :
  f ^+ n = (fun x => f x ^+ n).
Proof. by elim: n => [|n h]; rewrite funeqE=> ?; rewrite ?expr0 ?exprS ?h. Qed.

Lemma compE (T1 T2 T3 : Type) (f : T1 -> T2) (g : T2 -> T3) :
  g \o f = fun x => g (f x).
Proof. by []. Qed.

Definition fctE :=
  (cstE, compE, opprfctE, addrfctE, mulrfctE, scalrfctE, exprfctE).

Lemma natmulfctE (U : pointedType) (K : ringType) (f : U -> K) n :
  f *+ n = (fun x => f x *+ n).
Proof. by elim: n => [//|n h]; rewrite funeqE=> ?; rewrite !mulrSr h. Qed.

End function_space_lemmas.

Lemma inv_funK T (R : unitRingType) (f : T -> R) : f\^-1\^-1%R = f.
Proof. by apply/funeqP => x; rewrite /inv_fun/= GRing.invrK. Qed.
