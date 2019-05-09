(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology normedtype
  landau.
  (* TODO: bouger les structures sur les fonctions en dehors de landau *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Definition fct_sequence (T : Type) := nat -> (T -> Rbar).

Definition increasing (T : Type) (D : set T) (f_ : fct_sequence T) :=
  forall n, (forall x, D x -> f_ n x <= f_ n.+1 x :> R).

Module Type INTEGRAL.

Parameter integrable :
  forall (T : Type) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), bool.

Parameter integral :
  forall (T : Type) (m : set T -> Rbar) (D : set T) (f : T -> Rbar), Rbar.

(* section sur les fonctions positives ou infinies *)
Section pos_fct.
Variable T : Type.
Variable m : set T -> Rbar.
Variable D : set T.

(* TODO: we have to restrict linearity to integrable functions *)
Axiom integral_is_linear : linear_for *%R (integral m D : (T -> R^o) -> R).

Canonical integral_linear := Linear integral_is_linear.

(* TODO: structure d'ordre sur les functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
pour pouvoir utiliser la notation {homo ...}
pour reecrire integral_ler *)

Axiom integral_ler : forall (f g : T -> R),
  (forall x, f x <= g x) -> integral m D f <= integral m D g :> R.

(* voir necessite de la condition de positivite (sur wikipedia) *)
Axiom cvg_monotone : forall (f_ : fct_sequence T),
  increasing D f_ ->
  let f := fun t => lim (f_ ^~ t) in
  (* TODO: la fonction f est mesurable *)
  integral m D f = [lim (fun n => integral m D (f_ n)) in [filteredType R of Rbar]].
(* NB: this is wrong because les fonctions en argument ne sont pas a
valeur dans Rbar *)

(* TODO: fix the lim notation so as to avoid [filteredType R of Rbar] *)

(* theorem de convergence dominee *)
Axiom cvg_domin : forall (f_ : fct_sequence T), bool.

(* lemma de Fatou *)
Axiom Fatou : false.

End pos_fct.

(* section sur les functions quelconques a valeur finie *)
Section fin_fct.

End fin_fct.

End INTEGRAL.
