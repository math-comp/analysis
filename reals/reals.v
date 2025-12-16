(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

(**md**************************************************************************)
(* # An axiomatization of real numbers $\mathbb{R}$                           *)
(*                                                                            *)
(* This file provides a classical axiomatization of real numbers as a         *)
(* discrete real archimedean field with in particular a theory of floor and   *)
(* ceil.                                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*     realType == type of real numbers                                       *)
(*                 The HB class is Real.                                      *)
(*        sup A == where A : set R with R : realType, the supremum of A when  *)
(*                 it exists, 0 otherwise                                     *)
(*        inf A := - sup (- A)                                                *)
(* ```                                                                        *)
(*                                                                            *)
(* The mixin corresponding to realType extends an archiFieldType with two     *)
(* properties:                                                                *)
(* - when sup A exists, it is an upper bound of A (lemma sup_upper_bound)     *)
(* - when sup A exists, there exists an element x in A such that              *)
(*   sup A - eps < x for any 0 < eps (lemma sup_adherent)                     *)
(*                                                                            *)
(* ```                                                                        *)
(*         Rint == the set of real numbers that can be written as z%:~R,      *)
(*                 i.e., as an integer                                        *)
(*     Rtoint r == r when r is an integer, 0 otherwise                        *)
(*  floor_set x := [set y | Rtoint y /\ y <= x]                               *)
(*     Rfloor x == the floor of x as a real number                            *)
(*     range1 x := [set y |x <= y < x + 1]                                    *)
(*      Rceil x == the ceil of x as a real number, i.e., - Rfloor (- x)       *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*     @rational R == set of rational numbers of type R : realType            *)
(*   @irrational R == the complement of rational R                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets set_interval.

Declare Scope real_scope.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
From mathcomp Require Import unstable.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section subr_image.
Variable R : numDomainType.
Implicit Types (E : set R) (x : R).

Lemma has_ub_lbN E : has_ubound E <-> has_lbound (-%R @` E).
Proof.
rewrite has_lb_ubN image_comp /comp /=.
by under eq_fun do rewrite opprK; rewrite image_id.
Qed.

Lemma has_lbound0 : has_lbound (@set0 R). Proof. by exists 0. Qed.

Lemma has_ubound0 : has_ubound (@set0 R). Proof. by exists 0. Qed.

Lemma ubound0 : ubound (@set0 R) = setT.
Proof. by rewrite predeqE => r; split => // _. Qed.

Lemma lboundT : lbound [set: R] = set0.
Proof.
rewrite predeqE => r; split => // /(_ (r - 1) Logic.I).
by rewrite addrC -subr_ge0 addrK ler0N1.
Qed.

End subr_image.

Section has_bound_lemmas.
Variable R : realDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma has_ub_image_norm E : has_ubound (Num.norm @` E) -> has_ubound E.
Proof.
case => M /ubP uM; exists `|M|; apply/ubP => r rS.
by rewrite (le_trans (ler_norm _))// (le_trans (uM _ _))//; exact: ler_norm.
Qed.

Lemma has_inf_supN E : has_sup (-%R @` E) <-> has_inf E.
Proof.
split=> [ [NEn0 [x /ub_lbN xubE]]  | [En0 [x /lb_ubN xlbe]] ].
by split; [apply/nonemptyN|rewrite -[E]setNK; exists (- x)].
by split; [apply/nonemptyN|exists (- x)].
Qed.

Lemma has_supPn {E} : E !=set0 ->
  ~ has_sup E <-> (forall x, exists2 y, E y & x < y).
Proof.
move=> nzE; split=> [/asboolPn|/has_ubPn h [_]] //.
by rewrite asbool_and (asboolT nzE) /= => /asboolP/has_ubPn.
Qed.

End has_bound_lemmas.

(* -------------------------------------------------------------------- *)

HB.mixin Record ArchimedeanField_isReal R of Num.ArchiRealField R := {
  sup_upper_bound_subdef : forall E : set R,
    has_sup E -> ubound E (supremum 0 E) ;
  sup_adherent_subdef : forall (E : set R) (eps : R),
    0 < eps -> has_sup E -> exists2 e : R, E e & (supremum 0 E - eps) < e
}.

#[short(type=realType)]
HB.structure Definition Real := {R of ArchimedeanField_isReal R
  & Num.ArchiRealField R & Num.RealClosedField R}.

Bind Scope ring_scope with Real.sort.

(* -------------------------------------------------------------------- *)
Definition sup {R : realType} := @supremum _ R 0.
Definition inf {R : realType} (E : set R) := - sup (-%R @` E).

(* -------------------------------------------------------------------- *)
Lemma sup_upper_bound {R : realType} (E : set R):
  has_sup E -> ubound E (sup E).
Proof. exact: sup_upper_bound_subdef. Qed.

Lemma sup_adherent {R : realType} (E : set R) (eps : R) : 0 < eps ->
  has_sup E -> exists2 e : R, E e & (sup E - eps) < e.
Proof. exact: sup_adherent_subdef. Qed.

(* -------------------------------------------------------------------- *)
Section IsInt.
Context {R : realFieldType}.

Definition Rint_pred := fun x : R => `[< exists z, x == z%:~R >].
Arguments Rint_pred _ /.
Definition Rint := [qualify a x | Rint_pred x].

Lemma Rint_def x : (x \is a Rint) = (`[< exists z, x == z%:~R >]).
Proof. by []. Qed.

Lemma RintP x : reflect (exists z, x = z%:~R) (x \in Rint).
Proof.
by apply/(iffP idP) => [/asboolP[z /eqP]|[z]] ->; [|apply/asboolP]; exists z.
Qed.

Lemma RintC z : z%:~R \is a Rint.
Proof. by apply/RintP; exists z. Qed.

Lemma Rint0 : 0 \is a Rint.
Proof. by rewrite -[0](mulr0z 1) RintC. Qed.

Lemma Rint1 : 1 \is a Rint.
Proof. by rewrite -[1]mulr1z RintC. Qed.

Hint Resolve Rint0 Rint1 RintC : core.

Lemma Rint_subring_closed : subring_closed Rint.
Proof.
split=> // _ _ /RintP[x ->] /RintP[y ->]; apply/RintP.
by exists (x - y); rewrite rmorphB. by exists (x * y); rewrite rmorphM.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build R Rint_pred
  Rint_subring_closed.

Lemma Rint_ler_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x + 1 <= y) = (x < y).
Proof.
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{2}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) lezD1.
Qed.

Lemma Rint_ltr_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x < y + 1) = (x <= y).
Proof.
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{3}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) ltzD1.
Qed.

End IsInt.
Arguments Rint_pred _ _ /.

(* -------------------------------------------------------------------- *)
Section ToInt.
Context {R : realType}.

Implicit Types x y : R.

Definition Rtoint (x : R) : int :=
  if insub x : {? x | x \is a Rint} is Some Px then
    xchoose (asboolP _ (tagged Px))
  else 0.

Lemma RtointK (x : R): x \is a Rint -> (Rtoint x)%:~R = x.
Proof.
move=> Ix; rewrite /Rtoint insubT /= [RHS](eqP (xchooseP (asboolP _ Ix))).
by congr _%:~R; apply/eq_xchoose.
Qed.

Lemma Rtointz (z : int): Rtoint z%:~R = z.
Proof. by apply/eqP; rewrite -(@eqr_int R) RtointK ?rpred_int. Qed.

Lemma Rtointn (n : nat): Rtoint n%:R = n%:~R.
Proof. by rewrite -{1}mulrz_nat Rtointz. Qed.

Lemma inj_Rtoint : {in Rint &, injective Rtoint}.
Proof. by move=> x y Ix Iy /= /(congr1 (@intmul R 1)); rewrite !RtointK. Qed.

Lemma RtointN x : x \is a Rint -> Rtoint (- x) = - Rtoint x.
Proof.
move=> Ir; apply/eqP.
by rewrite -(@eqr_int R) RtointK // ?rpredN // mulrNz RtointK.
Qed.

End ToInt.

(* -------------------------------------------------------------------- *)

Section RealDerivedOps.
Variable R : realType.

Implicit Types x y : R.
Definition floor_set x := [set y : R | (y \is a Rint) && (y <= x)].

Definition Rfloor x : R := (Num.floor x)%:~R.

Definition range1 (x : R) := [set y | x <= y < x + 1].

Definition Rceil x : R := (Num.ceil x)%:~R.

End RealDerivedOps.

(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType).

Implicit Types E : set R.
Implicit Types x : R.

Lemma sup_out E : ~ has_sup E -> sup E = 0. Proof. exact: supremum_out. Qed.

Lemma sup0 : sup (@set0 R) = 0. Proof. exact: supremum0. Qed.

Lemma sup1 x : sup [set x] = x. Proof. exact: supremum1. Qed.

Lemma ub_le_sup {E} : has_ubound E -> ubound E (sup E).
Proof.
move=> ubE; apply/ubP=> x x_in_E; move: (x) (x_in_E).
by apply/ubP/sup_upper_bound=> //; split; first by exists x.
Qed.

Lemma sup_ub_strict E : has_ubound E ->
  ~ E (sup E) -> E `<=` [set r | r < sup E].
Proof.
move=> ubE EsupE r Er; rewrite /mkset lt_neqAle ub_le_sup // andbT.
by apply/negP => /eqP supEr; move: EsupE; rewrite -supEr.
Qed.

Lemma sup_total {E} x : has_sup E -> down E x \/ sup E <= x.
Proof.
move=> has_supE; rewrite orC.
case: (lerP (sup E) x)=> hx /=; [by left|right].
have /sup_adherent/(_  has_supE) : 0 < sup E - x by rewrite subr_gt0.
by case=> e Ee; rewrite subKr => /ltW hlte; apply/downP; exists e.
Qed.

Lemma ge_sup {E} x : E !=set0 -> (ubound E) x -> sup E <= x.
Proof.
move=> hasE leEx; set y := sup E; pose z := (x + y) / 2%:R.
have Dz: 2%:R * z = x + y by rewrite mulrC divfK// pnatr_eq0.
have ubE : has_sup E by split => //; exists x.
have [/downP [t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(lerD2l x) -Dz -mulr2n -[leRHS]mulr_natl.
  rewrite ler_pM2l ?ltr0Sn //; apply/(le_trans lezt).
  by move/ubP : leEx; exact.
rewrite -(lerD2r y) -Dz -mulr2n -[leLHS]mulr_natl.
by rewrite ler_pM2l ?ltr0Sn.
Qed.

Lemma sup_setU (A B : set R) : has_sup B ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof.
move=> [B0 [l Bl]] AB; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ge_sup => [|x [Ax|]]; first by apply: subset_nonempty B0 => ?; right.
  by case: B0 => b Bb; rewrite (le_trans (AB _ _ Ax Bb))// ub_le_sup//; exists l.
- by move=> Bx; rewrite ub_le_sup //; exists l.
- apply: ge_sup => // b Bb; apply: ub_le_sup; last by right.
  by exists l => x [Ax|Bx]; [rewrite (le_trans (AB _ _ Ax Bb)) // Bl|exact: Bl].
Qed.

Lemma sup_gt (S : set R) (x : R) : S !=set0 ->
  (x < sup S -> exists2 y, S y & x < y)%R.
Proof.
move=> S0; rewrite not_exists2P => + g; apply/negP; rewrite -leNgt.
by apply: ge_sup => // y Sy; move: (g y) => -[// | /negP]; rewrite leNgt.
Qed.

End RealLemmas.
#[deprecated(since="mathcomp-analysis 1.14.0", note="Renamed `ub_le_sup`.")]
Notation sup_ubound := ub_le_sup (only parsing).
#[deprecated(since="mathcomp-analysis 1.14.0", note="Renamed `ge_sup`.")]
Notation sup_le_ub := ge_sup (only parsing).

Section sup_sum.
Context {R : realType}.

Lemma sup_sumE (A B : set R) :
  has_sup A -> has_sup B -> sup [set x + y | x in A & y in B] = sup A + sup B.
Proof.
move=> /[dup] supA [[a Aa] ubA] /[dup] supB [[b Bb] ubB].
have ABsup : has_sup [set x + y | x in A & y in B].
  split; first by exists (a + b), a => //; exists b.
  case: ubA ubB => p up [q uq]; exists (p + q) => ? [r Ar [s Bs] <-].
  by apply: lerD; [exact: up | exact: uq].
apply: le_anti; apply/andP; split.
  apply: ge_sup; first by case: ABsup.
  by move=> ? [p Ap [q Bq] <-]; apply: lerD; exact: ub_le_sup.
rewrite leNgt -subr_gt0; apply/negP.
set eps := (_ + _ - _) => epos.
have e2pos : 0 < eps / 2%:R by rewrite divr_gt0// ltr0n.
have [r Ar supBr] := sup_adherent e2pos supA.
have [s Bs supAs] := sup_adherent e2pos supB.
have := ltrD supBr supAs.
rewrite -addrACA -opprD -splitr subKr; apply/negP; rewrite -leNgt.
by apply: sup_upper_bound => //; exists r => //; exists s.
Qed.

Lemma inf_sumE (A B : set R) :
  has_inf A -> has_inf B -> inf [set x + y | x in A & y in B] = inf A + inf B.
Proof.
move/has_inf_supN => ? /has_inf_supN ?; rewrite /inf.
rewrite [X in - sup X = _](_ : _ =
    [set x + y | x in [set - x | x in A ] & y in [set - x | x in B]]).
  by rewrite sup_sumE // -opprD.
rewrite eqEsubset; split => /= t [] /= x []a Aa.
  case => b Bb <- <-; exists (- a); first by exists a.
  by exists (- b); [exists b|rewrite opprD].
move=> <- [y] [b Bb] <- <-; exists (a + b); last by rewrite opprD.
by exists a => //; exists b.
Qed.

End sup_sum.

(* -------------------------------------------------------------------- *)
Section InfTheory.

Variables (R : realType).

Implicit Types E : set R.
Implicit Types x : R.

Lemma inf_adherent E (eps : R) : 0 < eps ->
  has_inf E -> exists2 e, E e & e < inf E + eps.
Proof.
move=> + /has_inf_supN supNE => /sup_adherent /(_ supNE)[e NEx egtsup].
exists (- e); first by case: NEx => x Ex <-{}; rewrite opprK.
by rewrite ltrNl -mulN1r mulrDr !mulN1r opprK.
Qed.

Lemma inf_out E : ~ has_inf E -> inf E = 0.
Proof.
move=> ninfE; rewrite -oppr0 -(@sup_out _ (-%R @` E)) => // supNE; apply: ninfE.
exact/has_inf_supN.
Qed.

Lemma inf0 : inf (@set0 R) = 0.
Proof. by rewrite /inf image_set0 sup0 oppr0. Qed.

Lemma inf1 x : inf [set x] = x.
Proof. by rewrite /inf image_set1 sup1 opprK. Qed.

Lemma ge_inf E : has_lbound E -> lbound E (inf E).
Proof. by move/has_lb_ubN/ub_le_sup/ub_lbN; rewrite setNK. Qed.

Lemma inf_lb_strict E : has_lbound E ->
  ~ E (inf E) -> E `<=` [set r | inf E < r].
Proof.
move=> lE EinfE r Er; rewrite /mkset lt_neqAle ge_inf// andbT.
by apply/negP => /eqP infEr; move: EinfE; rewrite infEr.
Qed.

Lemma lb_le_inf E x : nonempty E -> (lbound E) x -> x <= inf E.
Proof.
by move=> /(nonemptyN E) En0 /lb_ubN /(ge_sup En0); rewrite lerNr.
Qed.

Lemma has_infPn E : nonempty E ->
  ~ has_inf E <-> (forall x, exists2 y, E y & y < x).
Proof.
move=> nzE; split=> [/asboolPn|/has_lbPn h [_] //].
by rewrite asbool_and (asboolT nzE) /= => /asboolP/has_lbPn.
Qed.

Lemma inf_setU (A B : set R) : has_inf A ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof.
move=> hiA AB; congr (- _).
rewrite image_setU setUC sup_setU //; first exact/has_inf_supN.
by move=> _ _ [] b Bb <-{} [] a Aa <-{}; rewrite lerNl opprK; apply AB.
Qed.

Lemma inf_lt (S : set R) (x : R) : S !=set0 ->
  (inf S < x -> exists2 y, S y & y < x)%R.
Proof.
move=> /nonemptyN S0; rewrite /inf ltrNl => /sup_gt => /(_ S0)[r [r' Sr']].
by move=> <-; rewrite ltrNr opprK => r'x; exists r'.
Qed.

End InfTheory.
#[deprecated(since="mathcomp-analysis 1.14.0", note="Renamed `ge_inf`.")]
Notation inf_lbound := ge_inf (only parsing).

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma has_sup_floor_set x : has_sup (floor_set x).
Proof.
split; [exists (- (Num.bound (-x))%:~R) | exists (Num.bound x)%:~R].
  rewrite /floor_set/mkset rpredN rpred_int /= lerNl.
  case: (ger0P (-x)) => [/archi_boundP/ltW//|].
  by move/ltW/le_trans; apply; rewrite ler0z.
apply/ubP=> y /andP[_] /le_trans; apply.
case: (ger0P x)=> [/archi_boundP/ltW|] //.
by move/ltW/le_trans; apply; rewrite ler0z.
Qed.

Lemma sup_in_floor_set x : (floor_set x) (sup (floor_set x)).
Proof.
have /(sup_adherent ltr01) [y Fy] := has_sup_floor_set x.
have /sup_upper_bound /ubP /(_ _ Fy) := has_sup_floor_set x.
rewrite le_eqVlt=> /orP[/eqP<-//| lt_yFx].
rewrite ltrBlDr -ltrBlDl => lt1_FxBy.
pose e := sup (floor_set x) - y; have := has_sup_floor_set x.
move/sup_adherent=> -/(_ e) []; first by rewrite subr_gt0.
move=> z Fz; rewrite /= subKr => lt_yz.
have /sup_upper_bound /ubP /(_ _ Fz) := has_sup_floor_set x.
rewrite -(lerD2r (-y)) => /le_lt_trans /(_ lt1_FxBy).
case/andP: Fy Fz lt_yz=> /RintP[yi -> _].
case/andP=> /RintP[zi -> _]; rewrite -rmorphB /= ltrz1 ltr_int.
rewrite lt_neqAle => /andP[ne_yz le_yz].
rewrite -[_-_]gez0_abs ?subr_ge0 // ltz_nat ltnS leqn0.
by rewrite absz_eq0 subr_eq0 eq_sym (negbTE ne_yz).
Qed.

Lemma isint_Rfloor x : Rfloor x \is a Rint.
Proof. by rewrite inE; exists (Num.floor x). Qed.

Lemma RfloorE x : Rfloor x = (Num.floor x)%:~R.
Proof. by []. Qed.

Lemma mem_rg1_floor x : (range1 (Num.floor x)%:~R) x.
Proof. by rewrite /range1 /mkset intrD1 floor_le_tmp floorD1_gt. Qed.

Lemma mem_rg1_Rfloor x : (range1 (Rfloor x)) x.
Proof. exact: mem_rg1_floor. Qed.

Lemma Rfloor_le x : Rfloor x <= x.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma lt_succ_Rfloor x : x < Rfloor x + 1.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma range1z_inj x (m1 m2 : int) :
  (range1 m1%:~R) x -> (range1 m2%:~R) x -> m1 = m2.
Proof.
move=> /andP[m1x x_m1] /andP[m2x x_m2].
wlog suffices: m1 m2 m1x {x_m1 m2x} x_m2 / (m1 <= m2).
  by move=> ih; apply/eqP; rewrite eq_le !ih.
rewrite -(lerD2r 1) lezD1 -(@ltr_int R) intrD.
exact/(le_lt_trans m1x).
Qed.

Lemma range1rr x : (range1 x) x.
Proof. by rewrite /range1/mkset lexx /= ltrDl ltr01. Qed.

Lemma range1zP (m : int) x : Rfloor x = m%:~R <-> (range1 m%:~R) x.
Proof.
split=> [<-|h]; first exact/mem_rg1_Rfloor.
by congr intmul; apply/floor_def; rewrite -intrD1.
Qed.

Lemma Rfloor_natz (z : int) : Rfloor z%:~R = z%:~R :> R.
Proof. by apply/range1zP/range1rr. Qed.

Lemma Rfloor0 : Rfloor 0 = 0 :> R. Proof. by rewrite /Rfloor floor0. Qed.

Lemma Rfloor1 : Rfloor 1 = 1 :> R. Proof. by rewrite /Rfloor floor1. Qed.

Lemma le_Rfloor : {homo (@Rfloor R) : x y / x <= y}.
Proof. by move=> x y /Num.Theory.le_floor; rewrite ler_int. Qed.

Lemma Rfloor_ge_int x (n : int) : (n%:~R <= x)= (n%:~R <= Rfloor x).
Proof. by rewrite ler_int floor_ge_int_tmp. Qed.

Lemma Rfloor_lt_int x (z : int) : (x < z%:~R) = (Rfloor x < z%:~R).
Proof. by rewrite ltr_int -floor_lt_int. Qed.

Lemma Rfloor_le0 x : x <= 0 -> Rfloor x <= 0.
Proof. by move=> ?; rewrite -Rfloor0 le_Rfloor. Qed.

Lemma Rfloor_lt0 x : x < 0 -> Rfloor x < 0.
Proof. by move=> x0; rewrite (le_lt_trans _ x0) // Rfloor_le. Qed.

Lemma ltr_add_invr (y x : R) : y < x -> exists k, y + k.+1%:R^-1 < x.
Proof.
move=> yx; exists (Num.truncn (x - y)^-1).
by rewrite -ltrBrDl invf_plt 1?posrE 1?subr_gt0// truncnS_gt.
Qed.

End FloorTheory.

Section CeilTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma isint_Rceil x : Rceil x \is a Rint.
Proof. by rewrite /Rceil RintC. Qed.

Lemma Rceil0 : Rceil 0 = 0 :> R.
Proof. by rewrite /Rceil ceil0. Qed.

Lemma Rceil_ge x : x <= Rceil x.
Proof. by rewrite Num.Theory.ceil_ge ?num_real. Qed.

Lemma le_Rceil : {homo (@Rceil R) : x y / x <= y}.
Proof. by move=> x y ?; rewrite /Rceil ler_int le_ceil_tmp. Qed.

Lemma Rceil_ge0 x : 0 <= x -> 0 <= Rceil x.
Proof. by move=> x0; rewrite /Rceil ler0z -(ceil0 R) le_ceil_tmp. Qed.

Lemma RceilE x : Rceil x = (Num.ceil x)%:~R.
Proof. by []. Qed.

#[deprecated(since="mathcomp-analysis 1.3.0", note="use `Num.Theory.ceil_le` instead")]
Lemma le_ceil : {homo @Num.ceil R : x y / x <= y}.
Proof. exact: le_ceil_tmp. Qed.

End CeilTheory.

(* -------------------------------------------------------------------- *)
Section Sup.
Context {R : realType}.
Implicit Types A B : set R.

Lemma le_down A : A `<=` down A.
Proof. by move=> x xA; apply/downP; exists x. Qed.

Lemma downK A : down (down A) = down A.
Proof.
rewrite predeqE => x; split; last by move=> Ax; apply/downP; exists x.
case/downP => y /downP[z Az yz xy].
by apply/downP; exists z => //; rewrite (le_trans xy).
Qed.

Lemma has_sup_down A : has_sup (down A) <-> has_sup A.
Proof.
split=> -[nzA nzubA].
  case: nzA => x /downP[y yS le_xy]; split; first by exists y.
  case: nzubA=> u /ubP ubA; exists u; apply/ubP=> z zS.
  by apply/ubA; apply/downP; exists z.
case: nzA => x xA; split; first by exists x; apply/le_down.
case: nzubA => u /ubP ubA; exists u; apply/ubP=> y /downP [].
by move=> z zA /le_trans; apply; apply/ubA.
Qed.

Lemma sup_le A B : A `<=` down B -> nonempty A -> has_sup B ->
  sup A <= sup B.
Proof.
move=> le_AB nz_A hs_B; have hs_A: has_sup A.
  split=> //; case: hs_B => _ [x ubx].
  exists x; apply/ubP=> y /le_AB /downP[z zB le_yz].
  by apply/(le_trans le_yz); move/ubP: ubx; apply.
rewrite leNgt -subr_gt0; apply/negP => lt_sup.
case: (sup_adherent lt_sup hs_A )=> x /le_AB xdB.
rewrite subKr => lt_Bx; case/downP: xdB => z zB.
move/(lt_le_trans lt_Bx); rewrite ltNge.
by move/ubP : (sup_upper_bound hs_B) => ->.
Qed.

Lemma inf_le A B : -%R @` B `<=` down (-%R @` A) -> nonempty B -> has_inf A ->
  inf A <= inf B.
Proof.
move=> SBA AB Ai; rewrite lerNl opprK sup_le// ?has_inf_supN//.
exact/nonemptyN.
Qed.

Lemma sup_down A : sup (down A) = sup A.
Proof.
have [supA|supNA] := pselect (has_sup A); last first.
  by rewrite !sup_out // => /has_sup_down.
have supDA : has_sup (down A) by apply/has_sup_down.
apply/eqP; rewrite eq_le !sup_le //.
- by rewrite downK; exact: le_down.
- by case: supA.
- by case: supA => -[x xA] _; exists x; apply/le_down.
Qed.

Lemma lt_sup_imfset {T : Type} (F : T -> R) l :
  has_sup [set y | exists x, y = F x] ->
  l < sup [set y | exists x, y = F x] ->
  exists2 x, l < F x & F x <= sup [set y | exists x, y = F x].
Proof.
set P := [set y | _] => hs; rewrite -subr_gt0.
move=> /sup_adherent/(_ hs)[_ [x ->]]; rewrite subKr=> lt_lFx.
by exists x => //; move/ubP : (sup_upper_bound hs) => -> //; exists x.
Qed.

Lemma lt_inf_imfset {T : Type} (F : T -> R) l :
  has_inf [set y | exists x, y = F x] ->
  inf [set y | exists x, y = F x] < l ->
  exists2 x, F x < l & inf [set y | exists x, y = F x] <= F x.
Proof.
set P := [set y | _]; move=> hs; rewrite -subr_gt0.
move=> /inf_adherent/(_ hs)[_ [x ->]]; rewrite addrC subrK => ltFxl.
by exists x => //; rewrite (ge_inf hs.2)//; exists x.
Qed.

End Sup.
#[deprecated(since="mathcomp-analysis 1.14.0", note="Renamed `inf_le`.")]
Notation le_inf := inf_le (only parsing).
#[deprecated(since="mathcomp-analysis 1.14.0", note="Renamed `sup_le`.")]
Notation le_sup := sup_le (only parsing).

Lemma int_lbound_has_minimum (B : set int) i : B !=set0 -> lbound B i ->
  exists j, B j /\ forall k, B k -> j <= k.
Proof.
move=> [i0 Bi0] lbBi; have [n i0in] : exists n, i0 - i = n%:Z.
  by exists `|i0 - i|%N; rewrite gez0_abs // subr_ge0; exact: lbBi.
elim: n i lbBi i0in => [i lbBi /eqP|n ih i lbBi i0in1].
  by rewrite subr_eq0 => /eqP i0i; exists i0; split =>// k Bk; rewrite i0i lbBi.
have i0i1n : i0 - (i + 1) = n by rewrite opprD addrA i0in1 -addn1 PoszD addrK.
have [?|/not_forallP] := pselect (lbound B (i + 1)); first exact: (ih (i + 1)).
move=> /contrapT[x /not_implyP[Bx i1x]]; exists x; split => // k Bk.
rewrite (le_trans _ (lbBi _ Bk)) //.
by move/negP : i1x; rewrite -ltNge ltzD1.
Qed.

Lemma nat_has_minimum (A : set nat) : A !=set0 ->
  exists j, A j /\ forall k, A k -> (j <= k)%N.
Proof.
move=> A0.
pose B : set int := [set x%:~R | x in A].
have B0 : B !=set0 by apply: image_nonempty.
have: lbound B 0 by move=> _ [b0 Bb0 <-]; rewrite ler0z.
move/(int_lbound_has_minimum B0) => [_ [[i Ai <-]]] Bi.
exists i; split=> // k Bk.
by have := Bi k%:~R; rewrite ler_int; apply; exists k.
Qed.

Section rat_in_itvoo.

Let bound_div (R : archiRealFieldType) (x y : R) : nat :=
  if y < 0 then 0%N else Num.bound (y / x).

Let archi_bound_divP (R : archiRealFieldType) (x y : R) :
  0 < x -> y < x *+ bound_div x y.
Proof.
move=> x0; have [y0|y0] := leP 0 y; last by rewrite /bound_div y0 mulr0n.
rewrite /bound_div (ltNge y 0) y0/= -mulr_natl -ltr_pdivrMr//.
by rewrite archi_boundP// (divr_ge0 _(ltW _)).
Qed.

Lemma rat_in_itvoo (R : archiRealFieldType) (x y : R) :
  x < y -> exists q, ratr q \in `]x, y[.
Proof.
move=> xy; move: (xy); rewrite -subr_gt0.
move=> /(archi_bound_divP 1); set n := bound_div _ _ => nyx.
have [m1 m1nx] : exists m1, m1.+1%:~R > x *+ n.
  have := archi_bound_divP (x *+ n) ltr01; set p := bound_div _ _ => nxp.
  have [x0|x0] := ltP 0 x.
    exists p.-1; rewrite prednK // lt0n; apply: contraPN nxp => /eqP ->.
    by apply/negP; rewrite -leNgt mulrn_wge0 // ltW.
  by exists 0%N; rewrite (le_lt_trans _ ltr01) // mulrn_wle0.
have [m2 m2nx] : exists m2, m2.+1%:~R > - x *+ n.
  have := archi_bound_divP (- x *+ n) ltr01; set p := bound_div _ _ => nxp.
  have [x0|x0] := ltP 0 x.
    by exists O; rewrite (le_lt_trans _ ltr01) // nmulrn_rle0// oppr_lt0.
  exists p.-1; rewrite prednK // -(ltr_nat R) (le_lt_trans _ nxp) //.
  by rewrite mulrn_wge0 // oppr_ge0.
have : exists m, -(m2.+1 : int) <= m <= m1.+1 /\ m%:~R - 1 <= x *+ n < m%:~R.
  have m2m1 : - (m2.+1 : int) < m1.+1.
    by rewrite -(ltr_int R) (lt_trans _ m1nx)// rmorphN /= ltrNl // -mulNrn.
  pose B := [set m : int | m%:~R > x *+ n].
  have m1B : B m1.+1 by [].
  have m2B : lbound B (- m2.+1%:~R).
    move=> i; rewrite /B /= -(opprK (x *+ n)) -ltrNl -mulNrn => nxi.
    rewrite -(mulN1r m2.+1%:~R) mulN1r -lerNl.
    by have := lt_trans nxi m2nx; rewrite intz -mulrNz ltr_int => /ltW.
  have [m [Bm infB]] := int_lbound_has_minimum (ex_intro _ _ m1B) m2B.
  have mN1B : ~ B (m - 1).
    by move=> /infB; apply/negP; rewrite -ltNge ltrBlDr ltzD1.
  exists m; split; [apply/andP; split|apply/andP; split] => //.
  - by move: m2B; rewrite /lbound /= => /(_ _ Bm); rewrite intz.
  - exact: infB.
  - by rewrite leNgt; apply/negP; rewrite /B /= intrD in mN1B.
move=> [m [/andP[m2m mm1] /andP[mnx nxm]]].
have [/andP[a b] c] : x *+ n < m%:~R <= 1 + x *+ n /\ 1 + x *+ n < y *+ n.
  split; [apply/andP; split|] => //; first by rewrite -lerBlDl.
  by move: nyx; rewrite mulrnDl -ltrBrDr mulNrn.
have n_gt0 : n != 0%N by apply: contraTN nyx => /eqP ->; rewrite mulr0n ltr10.
exists (m%:Q / n%:Q); rewrite in_itv /= fmorph_div/= ratr_nat ratr_int.
rewrite ltr_pdivlMr ?ltr_pdivrMr ?ltr0n ?lt0n// !mulr_natr nxm/=.
apply: (le_lt_trans b c).
Qed.

End rat_in_itvoo.

Section rational.
Context {R : realType}.

Definition rational : set R := ratr @` [set: rat].

Lemma rationalP (r : R) :
  rational r <-> exists (a : int) (b : nat), r = a%:~R / b%:R.
Proof.
split=> [[q _ <-{r}]|[a [b ->]]]; last first.
  by exists (a%:~R / b%:R); rewrite // fmorph_div/= ratr_nat ratr_int.
have [n d nd] := ratP q; exists n, d.+1.
by rewrite fmorph_div/= ratr_nat ratr_int.
Qed.

Definition irrational : set R := ~` rational.

Lemma irrationalE : irrational = \bigcap_(q : rat) ~` (ratr @` [set q]).
Proof.
apply/seteqP; split => [r/= rE q _/=|r/= rE [q] _ qr]; last first.
  by apply: (rE q Logic.I) => /=; exists q.
by apply: contra_not rE => -[_ -> <-{r}]; exists q.
Qed.

End rational.
