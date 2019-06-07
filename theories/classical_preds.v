From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "-projection-no-head-constant".


(* todo: define classical predtypes, named sets, so as to have an infix \in in Prop, in scope classical_stuff *)
(* possible pb: clash with mathcomp..., and painful duplication. *)


(******************************************************************************)
(* Predicates, i.e., packaged functions to Prop.                              *)
(* - ppred T, the basic type for predicates over a type T, is simply an alias *)
(* for T -> Prop.                                                             *)
(* See ssrbool for more comment: we are just trying to duplicate the various  *)
(* machineries here.                                                          *)
(******************************************************************************)
Definition ppred T := T -> Prop.

Identity Coercion fun_of_ppred : ppred >-> Funclass.

Definition prel T := T -> ppred T.

Identity Coercion fun_of_prel : prel >-> Funclass.

Notation xppred0 := (fun _ => False).
Notation xppredT := (fun _ => True).
Notation xppredI := (fun (p1 p2 : ppred _) x => p1 x /\ p2 x).
Notation xppredU := (fun (p1 p2 : ppred _) x => p1 x \/ p2 x).
Notation xppredC := (fun (p : ppred _) x => ~ p x).
Notation xppredD := (fun (p1 p2 : ppred _) x => ~ p2 x /\ p1 x).
Notation xpreim := (fun f (p : ppred _) x => p (f x)).
Notation xprelU := (fun (r1 r2 : prel _) x y => r1 x y \/ r2 x y).


(* First, the applicative and collective versions, and the related notations *)
Section PropPredicates.

Variables T : Type.

Definition subppred (p1 p2 : ppred T) := forall x, p1 x -> p2 x.

Definition subprel (r1 r2 : prel T) := forall x y, r1 x y -> r2 x y.

Definition simpl_ppred := simpl_fun T Prop.
Definition applicative_ppred := ppred T.
Definition collective_ppred := ppred T.

Definition SimplPpred (p : ppred T) : simpl_ppred := SimplFun p.

Coercion ppred_of_simpl (p : simpl_ppred) : ppred T := fun_of_simpl p.
Coercion applicative_ppred_of_simpl (p : simpl_ppred) : applicative_ppred :=
  fun_of_simpl p.
Coercion collective_ppred_of_simpl (p : simpl_ppred) : collective_ppred :=
  fun x => (let: SimplFun f := p in fun _ => f x) x.
(* Note: applicative_of_simpl is convertible to ppred_of_simpl, while *)
(* collective_of_simpl is not. *)

Definition ppred0 := SimplPpred xppred0.
Definition ppredT := SimplPpred xppredT.
Definition ppredI p1 p2 := SimplPpred (xppredI p1 p2).
Definition ppredU p1 p2 := SimplPpred (xppredU p1 p2).
Definition ppredC p := SimplPpred (xppredC p).
Definition ppredD p1 p2 := SimplPpred (xppredD p1 p2).
Definition ppreim rT f (d : ppred rT) := SimplPpred (xpreim f d).

Definition simpl_prel := simpl_fun T (ppred T).

Definition SimplPrel (r : prel T) : simpl_prel := [fun x => r x].

Coercion prel_of_simpl_prel (r : simpl_prel) : prel T := fun x y => r x y.

Definition prelU r1 r2 := SimplPrel (xprelU r1 r2).

Lemma subprelUl r1 r2 : subprel r1 (prelU r1 r2).
Proof. by move=> *; left. Qed.

Lemma subprelUr r1 r2 : subprel r2 (prelU r1 r2).
Proof. by move=> *; right. Qed.

Variant mem_ppred := Mem of ppred T.

Definition isMem pT toppred mem := mem = (fun p : pT => Mem [eta toppred p]).

Structure ppredType := PpredType {
  ppred_sort :> Type;
  toppred : ppred_sort -> ppred T;
  _ : {mem | isMem toppred mem}
}.

Definition mkPpredType pT toP := PpredType (exist (@isMem pT toP) _ (erefl _)).

Canonical ppredPpredType := Eval hnf in @mkPpredType (ppred T) id.
Canonical simplPpredType := Eval hnf in mkPpredType ppred_of_simpl.
Canonical PropfunPpredType := Eval hnf in @mkPpredType (T -> Prop) id.

Coercion ppred_of_mem mp : ppred_sort ppredPpredType := let: Mem p := mp in [eta p].
Canonical memPpredType := Eval hnf in mkPpredType ppred_of_mem.

Definition clone_ppred U :=
  fun pT & ppred_sort pT -> U =>
  fun a mP (pT' := @PpredType U a mP) & phant_id pT' pT => pT'.

End PropPredicates.

Arguments ppred0 [T].
Arguments ppredT [T].
Prenex Implicits ppred0 ppredT ppredI ppredU ppredC ppredD ppreim prelU.

(* Short delimiter for Prop, but we cannot bind?*)
Delimit Scope prop_scope with P.
Open Scope prop_scope.

Notation "[ 'ppred' : T | E ]" := (SimplPpred ((fun _ : T => E) : ppred T))
  (at level 0, format "[ 'ppred' :  T  |  E ]") : fun_scope.
Notation "[ 'ppred' x | E ]" := (SimplPpred ((fun x => E) : ppred _))
  (at level 0, x ident, format "[ 'ppred'  x  |  E ]") : fun_scope.

Notation "[ 'ppred' x | E1 & E2 ]" := [ppred x | E1 /\ E2 ]
  (at level 0, x ident, format "[ 'ppred'  x  |  E1  &  E2 ]") : fun_scope.
Notation "[ 'ppred' x : T | E ]" := (SimplPpred ((fun x : T => E) : ppred T))
  (at level 0, x ident, only parsing) : fun_scope.
Notation "[ 'ppred' x : T | E1 /\ E2 ]" := [ppred x : T | E1 /\ E2 ]
  (at level 0, x ident, only parsing) : fun_scope.
Notation "[ 'prel' x y | E ]" := (SimplPrel ((fun x y => E) : prel _))
  (at level 0, x ident, y ident, format "[ 'prel'  x  y  |  E ]") : fun_scope.

Notation "[ 'prel' x y : T | E ]" := (SimplPrel ((fun x y : T => E) : prel T))
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'ppredType' 'of' T ]" := (@clone_ppred _ T _ id _ _ id)
  (at level 0, format "[ 'ppredType'  'of'  T ]") : form_scope.

(* Skiping the trick to use types as a synonym for their collective predicates.*)

(* These must be defined outside a Section because "cooking" kills the        *)
(* nosimpl tag.                                                               *)
Definition pmem T (pT : ppredType T) : pT -> mem_ppred T :=
  nosimpl (let: @PpredType _ _ _ (exist mem _) := pT return pT -> _ in mem).
Definition in_pmem T x mp := nosimpl ppred_of_mem T mp x.

Prenex Implicits pmem.

Coercion ppred_of_pmem_pred T mp := [ppred x : T | in_pmem x mp].


Definition eq_pmem T p1 p2 := forall x : T, in_pmem x p1 = in_pmem x p2.
Definition sub_pmem T p1 p2 := forall x : T, in_pmem x p1 -> in_pmem x p2.

(* why this? *)
Typeclasses Opaque eq_pmem.

Lemma sub_prefl T (p : mem_ppred T) : sub_pmem p p. Proof. by []. Qed.
Arguments sub_prefl {T p}.

Notation "x \in A" := (in_pmem x (pmem A)) : prop_scope.
Notation "x \in A" := (in_pmem x (pmem A)) : prop_scope.
Notation "x \notin A" := (~ (x \in A)) : prop_scope.
Notation "A =i B" := (eq_pmem (pmem A) (pmem B)) : type_scope.
Notation "{ 'subset' A <= B }" := (sub_pmem (pmem A) (pmem B))
  (at level 0, A, B at level 69,
   format "{ '[hv' 'subset'  A '/   '  <=  B ']' }") : type_scope.
Notation "[ 'pmem' A ]" := (ppred_of_simpl (ppred_of_pmem_pred (pmem A)))
  (at level 0, only parsing) : fun_scope.
Notation "[ 'prel' 'of' fA ]" := (fun x => [pmem (fA x)])
  (at level 0, format "[ 'prel'  'of'  fA ]") : fun_scope.
Notation "[ 'ppredI' A & B ]" := (ppredI [pmem A] [pmem B])
  (at level 0, format "[ 'ppredI'  A  &  B ]") : fun_scope.
Notation "[ 'ppredU' A & B ]" := (ppredU [pmem A] [pmem B])
  (at level 0, format "[ 'ppredU'  A  &  B ]") : fun_scope.
Notation "[ 'ppredD' A & B ]" := (ppredD [pmem A] [pmem B])
  (at level 0, format "[ 'ppredD'  A  &  B ]") : fun_scope.
Notation "[ 'ppredC' A ]" := (ppredC [pmem A])
  (at level 0, format "[ 'ppredC'  A ]") : fun_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [pmem A])
  (at level 0, format "[ 'preim'  f  'of'  A ]") : fun_scope.

Notation "[ 'ppred' x 'in' A ]" := [ppred x | x \in A]
  (at level 0, x ident, format "[ 'ppred'  x  'in'  A ]") : fun_scope.
Notation "[ 'ppred' x 'in' A | E ]" := [ppred x | x \in A & E]
  (at level 0, x ident, format "[ 'ppred'  x  'in'  A  |  E ]") : fun_scope.
Notation "[ 'ppred' x 'in' A | E1 & E2 ]" := [ppred x | x \in A & E1 && E2 ]
  (at level 0, x ident,
   format "[ 'ppred'  x  'in'  A  |  E1  &  E2 ]") : fun_scope.
Notation "[ 'prel' x y 'in' A & B | E ]" :=
  [prel x y | (x \in A) && (y \in B) && E]
  (at level 0, x ident, y ident,
   format "[ 'prel'  x  y  'in'  A  &  B  |  E ]") : fun_scope.
Notation "[ 'prel' x y 'in' A & B ]" := [prel x y | (x \in A) && (y \in B)]
  (at level 0, x ident, y ident,
   format "[ 'prel'  x  y  'in'  A  &  B ]") : fun_scope.
Notation "[ 'prel' x y 'in' A | E ]" := [prel x y in A & A | E]
  (at level 0, x ident, y ident,
   format "[ 'prel'  x  y  'in'  A  |  E ]") : fun_scope.
Notation "[ 'prel' x y 'in' A ]" := [prel x y in A & A]
  (at level 0, x ident, y ident,
   format "[ 'prel'  x  y  'in'  A ]") : fun_scope.

(* skipping the finer-grained control machineries (manifest, etc.) for now. *)

(* skipping the keyed predicates *)

(* skipping ... *) 

