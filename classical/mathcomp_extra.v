(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint.
From mathcomp Require Import archimedean rat finset interval.

(**md**************************************************************************)
(* # MathComp extra                                                           *)
(*                                                                            *)
(* This files contains lemmas and definitions recently added in mathcomp,     *)
(* in order to be able to compile analysis with older versions of mathcomp.   *)
(*                                                                            *)
(* ```                                                                        *)
(*               proj i f == f i, where f : forall i, T i                     *)
(*             dfwith f x == fun j => x if j = i, and f j otherwise           *)
(*                           given x : T i                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(**************************)
(* MathComp 2.3 additions *)
(**************************)

Module Order.
Import Order.
Definition default_display : disp_t.
Proof. exact: Disp tt tt. Defined.
End Order.

Definition proj {I} {T : I -> Type} i (f : forall i, T i) := f i.

Section DFunWith.
Variables (I : eqType) (T : I -> Type) (f : forall i, T i).

Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.

Lemma dfwithin i x : dfwith x i = x.
Proof. by rewrite /dfwith; case: eqP => // ii; rewrite eq_axiomK. Qed.

Lemma dfwithout i (x : T i) j : i != j -> dfwith x j = f j.
Proof. by rewrite /dfwith; case: eqP. Qed.

Variant dfwith_spec i (x : T i) : forall j, T j -> Type :=
  | DFunWithin : dfwith_spec x x
  | DFunWithout j : i != j -> dfwith_spec x (f j).

Lemma dfwithP i (x : T i) (j : I) : dfwith_spec x (dfwith x j).
Proof.
by case: (eqVneq i j) => [<-|nij];
   [rewrite dfwithin|rewrite dfwithout//]; constructor.
Qed.

Lemma projK i (x : T i) : cancel (@dfwith i) (proj i).
Proof. by move=> z; rewrite /proj dfwithin. Qed.

End DFunWith.
Arguments dfwith {I T} f i x.

(**************************)
(* MathComp 2.4 additions *)
(**************************)

(**************************)
(* MathComp 2.5 additions *)
(**************************)

Section ssralg.
Lemma subrKC {V : zmodType} (x y : V) : x + (y - x) = y.
Proof. by rewrite addrC subrK. Qed.
End ssralg.

Lemma sumr_le0 (R : numDomainType) I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> F i <= 0)%R -> (\sum_(i <- r | P i) F i <= 0)%R.
Proof. by move=> F0; elim/big_rec : _ => // i x Pi; apply/ler_wnDl/F0. Qed.

(* to appear in coq-mathcomp-finmap > 2.2.1 *)
Lemma card_fset_sum1 (T : choiceType) (A : {fset T}) :
  #|` A| = (\sum_(i <- A) 1)%N.
Proof. by rewrite big_seq_fsetE/= sum1_card cardfE. Qed.
