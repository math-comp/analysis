(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import Reals. (*can't get rid of this because it is used in normedtype *)
From mathcomp  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg .
From mathcomp Require Import bigop ssralg ssrint div ssrnum rat poly.
(* From mathcomp *)
(*      Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg. *)
From mathcomp Require Import boolp reals Rstruct Rbar derive. 
Require Import classical_sets posnum topology normedtype landau integral.


(*Pour distinguer fonctions mesurables et integrables,  
utiliser des structures comme posrel. *)

 Import GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.




(**********************************************************************)
(*Definition of complex and holomorphy independantly from the         *)   
 (* real-closed *)
(* of Cyril and thanks to the reals of mathcomp analysis              *) 
(**********************************************************************)

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := idtac.

Local Open Scope ring_scope.

Reserved Notation "x +i* y"
  (at level 40, left associativity, format "x  +i*  y").
Reserved Notation "x -i* y"
  (at level 40, left associativity, format "x  -i*  y").
Reserved Notation "R [i]"
  (at level 2, left associativity, format "R [i]").

Local Notation sgr := Num.sg.
Local Notation sqrtr := Num.sqrt.

Record C : Type := Complex { Re : R; Im : R }.

Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition real_complex (x : R) :=
  Complex x 0.
(* Notation real_complex := (@real_complex_def _ ). *)
Notation "x %:C" := (real_complex  x)
  (at level 2, left associativity, format "x %:C")  : complex_scope.
Notation "x +i* y" := (Complex x y) : complex_scope.
Notation "x -i* y" := (Complex x (- y)) : complex_scope.
Notation "x *i " := (Complex 0 x) (at level 8, format "x *i") : complex_scope.
Notation "''i'" := (Complex 0 1) : complex_scope.
(* Notation "C" := (complex) *)
(*   (at level 2, left associativity, format "R [i]"). *)

(* Module ComplexInternal. *)
Module ComplexEqChoice.
Section ComplexEqChoice.

(* Variable R : Type. *)

Definition sqR_of_complex (x : C) := let: a +i* b := x in [:: a; b].
Definition complex_of_sqR (x : seq R) :=
  if x is [:: a; b] then Some (a +i* b) else None.

Lemma complex_of_sqRK : pcancel sqR_of_complex complex_of_sqR.
Proof. by case. Qed.

End ComplexEqChoice.
End ComplexEqChoice.

Definition complex_eqMixin (* (R : eqType) *) :=
  PcanEqMixin (ComplexEqChoice.complex_of_sqRK ).
Definition complex_choiceMixin  (* (R : choiceType) *) :=
  PcanChoiceMixin (ComplexEqChoice.complex_of_sqRK ).
(* Definition complex_countMixin  (* (R : countType) *) := *)
(*   PcanCountMixin (ComplexEqChoice.complex_of_sqRK ). *)

Canonical complex_eqType (* (R : eqType) *) :=
  EqType C (complex_eqMixin).
Canonical complex_choiceType (* (R : choiceType) *) :=
  ChoiceType C (complex_choiceMixin).
(* Canonical complex_countType (* (R : countType) *) := *)
(*   CountType C (complex_countMixin). *)

Lemma eq_complex : forall (* (R : eqType) *) (x y : C),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=>  [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma complexr0 : forall (* (R : ringType)  *) (x : R), x +i* 0 = x%:C. Proof. by []. Qed.

Module ComplexField.
Section ComplexField.

(* Variable R : realType. *)
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition addc (x y : C) := let: a +i* b := x in let: c +i* d := y in
  (a + c) +i* (b + d).
Definition oppc (x : C) := let: a +i* b := x in (- a) +i* (- b).

Program Definition complex_zmodMixin := @ZmodMixin _ C0 oppc addc _ _ _ _.
Next Obligation. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.
Next Obligation. by move=> [a b] [c d] /=; congr (_ +i* _); rewrite addrC. Qed.
Next Obligation. by move=> [a b] /=; rewrite !add0r. Qed.
Next Obligation. by move=> [a b] /=; rewrite !addNr. Qed.
Canonical complex_zmodType := ZmodType C complex_zmodMixin.

Definition scalec (a : R) (x : C) := 
  let: b +i* c := x in (a * b) +i* (a * c).

Program Definition complex_lmodMixin := @LmodMixin _ _ scalec _ _ _ _. 
Next Obligation. by move=> a b [c d] /=; rewrite !mulrA. Qed.
Next Obligation. by move=> [a b] /=; rewrite !mul1r. Qed.
Next Obligation. by move=> a [b c] [d e] /=; rewrite !mulrDr. Qed.
Next Obligation. by move=> [a b] c d /=; rewrite !mulrDl. Qed.
Definition C_RlmodType := LmodType R C complex_lmodMixin.
(*WARNING We don't want this to be canonical / contrary to real closed  *)

Definition mulc (x y : C) := let: a +i* b := x in let: c +i* d := y in
  ((a * c) - (b * d)) +i* ((a * d) + (b * c)).

Lemma mulcC : commutative mulc.
Proof.
move=> [a b] [c d] /=.
by rewrite [c * b + _]addrC ![_ * c]mulrC ![_ * d]mulrC.
Qed.

Lemma mulcA : associative mulc.
Proof.
move=> [a b] [c d] [e f] /=.
rewrite !mulrDr !mulrDl !mulrN !mulNr !mulrA !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite !addrA addrAC;
  congr (_ + _); rewrite addrC.
Qed.

Definition invc (x : C) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i* (b / n2).

Lemma mul1c : left_id C1 mulc.
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive mulc addc.
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulrDl !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite addrCA.
Qed.

Lemma nonzero1c : C1 != C0. Proof. by rewrite eq_complex /= oner_eq0. Qed.

Definition complex_comRingMixin :=
  ComRingMixin mulcA mulcC mul1c mulc_addl nonzero1c.
Canonical complex_ringType :=RingType C complex_comRingMixin.
Canonical complex_comRingType := ComRingType C mulcC.

Lemma mulVc : forall x, x != C0 -> mulc (invc x) x = C1.
Proof.
move=> [a b]; rewrite eq_complex => /= hab; rewrite !mulNr opprK.
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr complexr0 -mulrDl mulfV //.
by rewrite paddr_eq0 -!expr2 ?expf_eq0 ?sqr_ge0.
Qed.

Lemma invc0 : invc C0 = C0. Proof. by rewrite /= !mul0r oppr0. Qed.

Definition complex_fieldUnitMixin := FieldUnitMixin mulVc invc0.
Canonical complex_unitRingType := UnitRingType C complex_fieldUnitMixin.
Canonical complex_comUnitRingType := Eval hnf in [comUnitRingType of C].

Lemma field_axiom : GRing.Field.mixin_of complex_unitRingType.
Proof. by []. Qed.

Definition ComplexFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical complex_idomainType := IdomainType C (FieldIdomainMixin field_axiom).
Canonical complex_fieldType := FieldType C field_axiom.

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)].

Lemma real_complex_is_rmorphism : rmorphism (real_complex).
Proof.
split; [|split=> //] => a b /=; simpc; first by rewrite subrr.
by rewrite !mulr0 !mul0r addr0 subr0.
Qed.

Canonical real_complex_rmorphism :=
  RMorphism real_complex_is_rmorphism.
Canonical real_complex_additive :=
  Additive real_complex_is_rmorphism.
About scalar. 
Lemma Re_is_scalar : scalar (Re : C_RlmodType -> R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Re_additive := Additive Re_is_scalar.
Canonical Re_linear := Linear Re_is_scalar.

Lemma Im_is_scalar : scalar (Im : C_RlmodType -> R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Im_additive := Additive Im_is_scalar.
Canonical Im_linear := Linear Im_is_scalar.

Definition lec (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Definition normc (x : C) : R :=
  let: a +i* b := x in sqrtr (a ^+ 2 + b ^+ 2).

Notation normC x := (normc x)%:C.

Lemma ltc0_add : forall x y, ltc 0 x -> ltc 0 y -> ltc 0 (x + y).
Proof.
move=> [a b] [c d] /= /andP [/eqP-> ha] /andP [/eqP-> hc].
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma eq0_normc x : normc x = 0 -> x = 0.
Proof.
case: x => a b /= /eqP; rewrite sqrtr_eq0 ler_eqVlt => /orP [|]; last first.
  by rewrite ltrNge addr_ge0 ?sqr_ge0.
by rewrite paddr_eq0 ?sqr_ge0 ?expf_eq0 //= => /andP[/eqP -> /eqP ->].
Qed.

Lemma eq0_normC x : normC x = 0 -> x = 0. Proof. by case=> /eq0_normc. Qed.

Lemma ge0_lec_total x y : lec 0 x -> lec 0 y -> lec x y || lec y x.
Proof.
move: x y => [a b] [c d] /= /andP[/eqP -> a_ge0] /andP[/eqP -> c_ge0].
by rewrite eqxx ler_total.
Qed.

Lemma normcM x y : normc (x * y) = normc x * normc y.
Proof.
move: x y => [a b] [c d] /=; rewrite -sqrtrM ?addr_ge0 ?sqr_ge0 //.
rewrite sqrrB sqrrD mulrDl !mulrDr -!exprMn.
rewrite mulrAC [b * d]mulrC !mulrA.
suff -> : forall (u v w z t : R), (u - v + w) + (z + v + t) = u + w + (z + t).
  by rewrite addrAC !addrA.
by move=> u v w z t; rewrite [_ - _ + _]addrAC [z + v]addrC !addrA addrNK.
Qed.

Lemma normCM x y : normC (x * y) = normC x * normC y.
Proof. by rewrite -rmorphM normcM. Qed.

Lemma subc_ge0 x y : lec 0 (y - x) = lec x y.
Proof. by move: x y => [a b] [c d] /=; simpc; rewrite subr_ge0 subr_eq0. Qed.

Lemma lec_def x y : lec x y = (normC (y - x) == y - x).
Proof.
rewrite -subc_ge0; move: (_ - _) => [a b]; rewrite eq_complex /= eq_sym.
have [<- /=|_] := altP eqP; last by rewrite andbF.
by rewrite [0 ^+ _]mul0r addr0 andbT sqrtr_sqr ger0_def.
Qed.

Lemma ltc_def x y : ltc x y = (y != x) && lec x y.
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite eq_complex /=.
by have [] := altP eqP; rewrite ?(andbF, andbT) //= ltr_def.
Qed.

Lemma lec_normD x y : lec (normC (x + y)) (normC x + normC y).
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite addr0 eqxx /=.
rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?(ler_paddr, sqrtr_ge0) //.
rewrite [X in _ <= X] sqrrD ?sqr_sqrtr;
   do ?by rewrite ?(ler_paddr, sqrtr_ge0, sqr_ge0, mulr_ge0) //.
rewrite -addrA addrCA (monoRL (addrNK _) (ler_add2r _)) !sqrrD.
set u := _ *+ 2; set v := _ *+ 2.
rewrite [a ^+ _ + _ + _]addrAC [b ^+ _ + _ + _]addrAC -addrA.
rewrite [u + _] addrC [X in _ - X]addrAC [b ^+ _ + _]addrC.
rewrite [u]lock [v]lock !addrA; set x := (a ^+ 2 + _ + _ + _).
rewrite -addrA addrC addKr -!lock addrC.
have [huv|] := ger0P (u + v); last first.
  by move=> /ltrW /ler_trans -> //; rewrite pmulrn_lge0 // mulr_ge0 ?sqrtr_ge0.
rewrite -(@ler_pexpn2r _ 2) -?topredE //=; last first.
  by rewrite ?(pmulrn_lge0, mulr_ge0, sqrtr_ge0) //.
rewrite -mulr_natl !exprMn !sqr_sqrtr ?(ler_paddr, sqr_ge0) //.
rewrite -mulrnDl -mulr_natl !exprMn ler_pmul2l ?exprn_gt0 ?ltr0n //.
rewrite sqrrD mulrDl !mulrDr -!exprMn addrAC -!addrA ler_add2l !addrA.
rewrite [_ + (b * d) ^+ 2]addrC -addrA ler_add2l.
have: 0 <= (a * d - b * c) ^+ 2 by rewrite sqr_ge0.
by rewrite sqrrB addrAC subr_ge0 [_ * c]mulrC mulrACA [d * _]mulrC.
Qed.

Definition complex_numMixin := NumMixin lec_normD ltc0_add eq0_normC
     ge0_lec_total normCM lec_def ltc_def.
Canonical complex_numDomainType := NumDomainType C complex_numMixin.

End ComplexField.
End ComplexField.

Locate numFieldType. 
Import ComplexField.

Canonical ComplexField.complex_zmodType.
Canonical ComplexField.C_RlmodType. (*Warning : is this OK ?*)
Canonical ComplexField.complex_ringType.
Canonical ComplexField.complex_comRingType.
Canonical ComplexField.complex_unitRingType.
Canonical ComplexField.complex_comUnitRingType.
Canonical ComplexField.complex_idomainType.
Canonical ComplexField.complex_fieldType.
Canonical ComplexField.complex_numDomainType.
Canonical complex_numFieldType  := [numFieldType of C]. 
Canonical ComplexField.real_complex_rmorphism.
Canonical ComplexField.real_complex_additive.
Canonical ComplexField.Re_additive.
Canonical ComplexField.Im_additive.

Definition conjc (x : C) := let: a +i* b := x in a -i* b.
Notation "x ^*" := (conjc x) (at level 2, format "x ^*") : complex_scope.
Local Open Scope complex_scope.
Delimit Scope complex_scope with C.

Ltac simpc := do ?
  [ rewrite -[- (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C - (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C + (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C * (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C ^*]/(_ +i* _)%C
  | rewrite -[_ *: (_ +i* _)%C]/(_ +i* _)%C
  | rewrite -[(_ +i* _)%C <= (_ +i* _)%C]/((_ == _) && (_ <= _))
  | rewrite -[(_ +i* _)%C < (_ +i* _)%C]/((_ == _) && (_ < _))
  | rewrite -[`|(_ +i* _)%C|]/(sqrtr (_ + _))%:C%C
  | rewrite (mulrNN, mulrN, mulNr, opprB, opprD, mulr0, mul0r,
    subr0, sub0r, addr0, add0r, mulr1, mul1r, subrr, opprK, oppr0,
    eqxx) ].


Section ComplexTheory.

(* Variable R : realType. *)

Lemma ReiNIm : forall x : C, Re (x * 'i%C) = - Im x.
Proof. by case=> a b; simpc. Qed.

Lemma ImiRe : forall x : C, Im (x * 'i%C) = Re x.
Proof. by case=> a b; simpc. Qed.

Lemma complexE x : x = (Re x)%:C + 'i%C * (Im x)%:C :> C.
Proof. by case: x => *; simpc. Qed.

Lemma real_complexE x : x%:C = x +i* 0 :> C. Proof. done. Qed.

Lemma sqr_i : 'i%C ^+ 2 = -1 :> C.
Proof. by rewrite exprS; simpc; rewrite -real_complexE rmorphN. Qed.

Lemma complexI : injective (real_complex). Proof. by move=> x y []. Qed.

Lemma ler0c (x : R) : (0 <= x%:C) = (0 <= x). Proof. by simpc. Qed.

Lemma lecE : forall x y : C, (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y : C, (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; simpc. Qed.

Lemma ltcR : forall x y : R, (x%:C < y%:C) = (x < y).
Proof. by move=> x y; simpc. Qed.

Lemma conjc_is_rmorphism : rmorphism (conjc).
Proof.
split=> [[a b] [c d] | ] /=; first by simpc; rewrite [d - _]addrC.
by split=> [[a b] [c d] | ] /=; simpc.
Qed. 

Lemma conjc_is_scalable : scalable (conjc : C -> C_RlmodType).
Proof. by move=> a [b c]; simpc. Qed.

Canonical conjc_rmorphism := RMorphism conjc_is_rmorphism.
Canonical conjc_additive := Additive conjc_is_rmorphism.
Canonical conjc_linear := AddLinear conjc_is_scalable.

Lemma conjcK : involutive (conjc).
Proof. by move=> [a b] /=; rewrite opprK. Qed.

Lemma mulcJ_ge0 (x : C) : 0 <= x * x^*%C.
Proof.
by move: x=> [a b]; simpc; rewrite mulrC addNr eqxx addr_ge0 ?sqr_ge0.
Qed.

Lemma conjc_real (x : R) : x%:C^* = x%:C.
Proof. by rewrite /= oppr0. Qed.

Lemma ReJ_add (x : C) : (Re x)%:C =  (x + x^*%C) / 2%:R.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 // -natrM pnatr_eq0.
Qed.

Lemma ImJ_sub (x : C) : (Im x)%:C =  (x^*%C - x) / 2%:R * 'i%C.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 ?opprK // -natrM pnatr_eq0.
Qed.

Lemma ger0_Im (x : C) : 0 <= x -> Im x = 0.
Proof. by move: x=> [a b] /=; simpc => /andP [/eqP]. Qed.

(* Todo : extend theory of : *)
(*   - signed exponents *)

Lemma conj_ge0 : forall x : C, (0 <= x ^*) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite oppr_eq0. Qed.

Lemma conjc_nat : forall n, (n%:R : C)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : C) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : C) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x : C, (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_complex /= eqr_oppLR oppr0. Qed.

Lemma conjc_inv: forall x : C, (x^-1)^* = (x^*%C )^-1.
Proof. exact: fmorphV. Qed.

Lemma complex_root_conj (p : {poly C}) (x : C) :
  root (map_poly conjc p) x = root p x^*.
Proof. by rewrite /root -{1}[x]conjcK horner_map /= conjc_eq0. Qed.

Lemma normc_def (z : C) : `|z| = (sqrtr ((Re z)^+2 + (Im z)^+2))%:C.
Proof. by case: z. Qed.

Lemma add_Re2_Im2 (z : C) : ((Re z)^+2 + (Im z)^+2)%:C = `|z|^+2.
Proof. by rewrite normc_def -rmorphX sqr_sqrtr ?addr_ge0 ?sqr_ge0. Qed.

Lemma addcJ (z : C) : z + z^*%C = 2%:R * (Re z)%:C.
Proof. by rewrite ReJ_add mulrC mulfVK ?pnatr_eq0. Qed.

Lemma subcJ (z : C) : z - z^*%C = 2%:R * (Im z)%:C * 'i%C.
Proof.
rewrite ImJ_sub mulrCA mulrA mulfVK ?pnatr_eq0 //.
by rewrite -mulrA ['i%C * _]sqr_i mulrN1 opprB.
Qed.

Lemma complex_real (a b : R) : a +i* b \is Num.real = (b == 0).
Proof.
rewrite realE; simpc; rewrite [0 == _]eq_sym.
by have [] := ltrgtP 0 a; rewrite ?(andbF, andbT, orbF, orbb).
Qed.

Lemma complex_realP (x : C) : reflect (exists y, x = y%:C) (x \is Num.real).
Proof.
case: x=> [a b] /=; rewrite complex_real.
by apply: (iffP eqP) => [->|[c []//]]; exists a.
Qed.

Lemma RRe_real (x : C) : x \is Num.real -> (Re x)%:C = x.
Proof. by move=> /complex_realP [y ->]. Qed.

Lemma RIm_real (x : C) : x \is Num.real -> (Im x)%:C = 0.
Proof. by move=> /complex_realP [y ->]. Qed.

End ComplexTheory.

(* all the above is copied from real-closed/complex.v *)

 Local Open Scope complex_scope.
 Import  ComplexField .

 Set Implicit Arguments.
 Unset Strict Implicit.
 Unset Printing Implicit Defensive.
 (* Obligation Tactic := idtac. *)
 
 (*This is now R from Reals *) 
 (*Adapting lemma eq_complex from complex.v, 
 which was done in boolean style*)
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

 Lemma normcN ( x : C) : normc (-x) = (normc x).
 Admitted.

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
  (*real_complex_additive*)
  move => x y ; rewrite -!complexr0 eqE_complex //=.
  by split ; last by rewrite addr0.  
 Qed.

 Lemma real_complex_inv : forall x : R, x%:C^-1 = (x^-1)%:C.
 Proof.
 Search _ (rmorphism _).
 Admitted. 

 Lemma Im_inv : ('i%C)^-1 = (-1*i) :> C.
 Proof. Admitted.  

 Lemma invcM : forall x y : C, (x*y)^-1 = x^-1 * y^-1.
 (*Maybe another lemma is doing that, or invrM *)
 Proof. Admitted.

Lemma scale_inv : forall (h : R)  (v : C), (h*:v)^-1 = h^-1 *: v^-1.
 (*Maybe another lemma is doing that, or invrM *)
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
 Proof. by move => [a b ] r; rewrite eqE_complex //=; split; simpc. Qed.

 
 
Section C_Rnormed.
 
 (* Uniform.mixin_of takes a locally but does not expect a TopologicalType, which is inserted in the Uniform.class_of *)
 (* Whereas NormedModule.mixin_of asks for a Uniform.mixin_of loc *)

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

 (*Warning : line 412 of Rstruct, why is the canonical realType structure on R 
  called real_relaType and not R_realType. *)
 (*C as a R-lmodule *)
   
 Definition C_RlmodMixin := (complex_lmodMixin). 
 (*LmodType is hard to use, not findable through Search and not checkable
 as abbreviation is not applied enough*) 
 Definition C_RlmodType := @LmodType R C C_RlmodMixin.
 Definition C_pointedType := PointedType C 0.
 Canonical C_pointedType.
 Definition C_filteredType := FilteredType C C (locally_ (ball_ (normc))).
 Canonical C_filteredType.
 (*Are we sure that the above is canonical *)
 
 (*Warning : going from R to a R:realType one must remplace
   everything related to normc to normc with explicit realtype *)
 Program Definition C_RuniformMixin :=
   @uniformmixin_of_normaxioms C_RlmodType (normc) normcD normcZ (eq0_normc).
 Definition C_RtopologicalMixin := topologyOfBallMixin C_RuniformMixin.
 Definition C_RtopologicalType := TopologicalType C_filteredType C_RtopologicalMixin.
 Definition C_RuniformType := @UniformType C_RtopologicalType C_RuniformMixin.


 Program Definition C_RnormedMixin
   := @NormedModMixin R_absRingType C_RlmodType _ C_RuniformMixin (normc)
            normcD normcZ _  (eq0_normc).
 Next Obligation. by []. Qed. 


 Definition C_RnormedType : normedModType R := @NormedModType R C_RuniformType C_RnormedMixin.


 Lemma scalecAl : forall (h : R) ( x y : C_RnormedType),
   h *: ( x * y) = h *: x * y. 
 Proof. move => h [a b] [c d]. simpc. Admitted.


 Definition C_RLalg := LalgType R C_RlmodType scalecAl. 

End C_Rnormed.
  

Section C_absRing.


  
  (*Canonical C_ringType := complex_ringType . *)
  Definition C_AbsRingMixin := @AbsRingMixin  (complex_ringType)
                 (normc) normc0 normcN1 normcD (normcM) (eq0_normc). 
  Definition C_absRingType :=  AbsRingType C C_AbsRingMixin.
  Canonical C_absRingType.
  Definition C_topologicalType := [topologicalType of C for C_absRingType].
  Canonical C_topologicalType. 
  Definition C_uniformType := [uniformType of C for C_absRingType].
  Canonical C_uniformType.
  Definition Co_pointedType := [pointedType of C^o for C_absRingType].
  Definition Co_filteredType := [filteredType C^o of C^o for C_absRingType].
  Definition Co_topologicalType := [topologicalType of C^o for C_absRingType].
  
  Canonical Zmod_topologicalType ( K : absRingType)
            (V : normedModType K):=
    [topologicalType of [zmodType of V]].
  
  Definition Co_uniformType := [uniformType of C^o for C_absRingType].
  Canonical Co_uniformType.
  Definition Co_normedType := AbsRing_NormedModType C_absRingType.
  Canonical Co_normedType.
  Canonical C_normedType := [normedModType C of C for Co_normedType].
  (*C is convertible to C^o *)

  
  Canonical R_normedType := [normedModType R of R for  [normedModType R of R^o]].
  
  Canonical absRing_normedType (K : absRingType) :=
    [normedModType K^o of K for (AbsRing_NormedModType K)].

  Lemma abs_normE : forall ( K : absRingType) (x : K), `|x|%real = `|[x]|.
  Proof.  by []. Qed.

  (*Delete absCE and adapt from abs_normE *)
  Lemma absCE : forall x : C, `|x|%real = (normc x).
  Proof. by []. Qed.

  Lemma normCR : forall x : R, `|[x%:C]| = `|x|%real.
  Proof. Admitted.
  
  Lemma absring_real_complex : forall r: R, forall x : R, AbsRing_ball 0 r x ->
   (AbsRing_ball 0%:C r x%:C).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE.
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_r. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.


  Lemma absring_real_Im :  forall r: R, forall x : R, AbsRing_ball 0 r x ->
                                            (AbsRing_ball  0%:C r x*i).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE. 
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_i. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.
  Locate imaginaryC.  (* WHAT ?????? *)
  Print imaginaryC. 
  Unset Printing Notations.
  Check 'i. 
  Lemma scalei_muli : forall (z : C),  z * 'i = 'i *: z.
  Proof. Why is it not working ? Let us do everyhting over a realtype
    by []. Coule be a problem of requiring Reals after reals.
  Qed.

  Lemma iE : 'i%C = 'i :> C.
  Proof. by []. Qed.

  Lemma scaleC_mul : forall (w  v : C^o), (v *: w = v * w).  
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
(*Diff is defined from any normedmodule of any absringtype,
 so C is a normedmodul on itsself *)
(*Vague idea that this should work, as we see C^o as a vector space on C and not R*)


(*Important : differentiable in derive.v, means continuoulsy differentiable, 
not just that the limit exists. *)
(*derivable concerns only the existence of the derivative *)

 Definition holomorphic (f : C^o -> C^o) (c: C^o) :=
  cvg ((fun (h:C^o)=> h^-1 *: ((f \o shift c) (h) - f c)) @ (locally' 0)).

 Definition complex_realfun (f : C^o -> C^o) : C_RnormedType -> C_RnormedType := f.
 Arguments complex_realfun _ _ /.

 Definition complex_Rnormed_absring : C_RnormedType -> C^o := id.

 Definition CauchyRiemanEq_R2 (f : C_RnormedType -> C_RnormedType) c :=
  let u := (fun c => Re ( f c)): C_RnormedType -> R^o  in 
  let v:= (fun c => Im (f c)) :  C_RnormedType -> R^o in
  (* ('D_(1%:C) u = 'D_('i) v) /\ ('D_('i) u = 'D_(1%:C) v). *)
  (((derive u c (1%:C)) = 
         (derive v c ('i : C_RnormedType))) /\ ((derive v c (1%:C)) = -(derive u c ('i : C_RnormedType)))).


 Definition deriveC (V W : normedModType C)(f : V -> W) c v :=
  lim ((fun (h: C^o) => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' 0).


 Definition CauchyRiemanEq (f : C -> C) z :=
  'i * lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 1%:C) - f z)) @ locally' 0) =
   lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 'i%C) - f z)) @ locally' 0).

  
 Lemma eqCr (R : rcfType) (r s : R) : (r%:C == s%:C) = (r == s).
 Proof. exact: (inj_eq (@complexI _)). Qed.

 Lemma eqCI (R : rcfType) (r s : R) : (r*i == s*i) = (r == s).
 Proof.  Admitted.


(*Lemma lim_trans (T : topologicalType) (F : set (set T))  
(G : set (set T)) (l : T) : ( F `=>` G ) -> (G --> l) -> ( F --> l). 
  move => FG Gl A x.
  Search "lim" "trans". 
 *)

 Lemma cvg_translim (T : topologicalType) (F G: set (set T)) (l :T) :
   F `=>` G -> (G --> l) -> (F --> l). 
 Proof.
  move => FG Gl. apply : cvg_trans.
   exact : FG.   
   exact : Gl. 
 Qed.


 Lemma cvg_scaler (K : absRingType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
    cvg (f @ F) -> cvg ((k \*: f) @ F ).
 Proof. 
    by move => /cvg_ex [l H0] ; apply: cvgP; apply: cvgZr; apply: H0. 
 Qed.

(* Lemma cvg_proper_top  (T : topologicalType) (F : set (set  U)) (FF : Filter F) : *)
(*   cvg F  -> ProperFilter F.   *)


 Lemma limin_scaler (K : absRingType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
      cvg(f@F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
 Proof.
  move => cv. 
  symmetry.
  by apply: cvg_lim; apply: cvgZr .  
 Qed.

(*this could be done for scale also ... *)

(*I needed filter_of_filterE to make things easier - 
looked a long time of it as I was looking for a [filter of lim]*
 instead of a [filter of filter]*)

(*There whould be a lemma analogous to [filter of lim] to ease the search  *)

Lemma holo_derivable  (f : C^o -> C^o) c :  holomorphic f c
         -> (forall v:C , derivable (complex_realfun f) c v).
Proof.
  move => /cvg_ex [l H]; rewrite /derivable => v. 
  rewrite /type_of_filter /= in l H.
  set ff : C_RnormedType -> C_RnormedType :=  f.
  set quotR := (X in (X @ locally' 0)).
  pose mulv (h :R):= (h *:v). 
  pose quotC (h : C) : C^o := h^-1 *: ((f \o shift c) (h) - f c).
  (* here f : C -> C does not work - 
as if we needed C^o still for the normed structure*)
  case : (EM (v = 0)). 
  - move => eqv0 ; apply (cvgP (l := (0:C))). 
    have eqnear0 : {near locally' (0:R), 0 =1 quotR}.
      exists 1 => // h _ _ ; rewrite /quotR /shift eqv0. simpl.
      by rewrite scaler0 add0r addrN scaler0.
      (*addrN is too hard to find through Search *)
    apply: cvg_translim.
    - exact (cvg_eq_loc eqnear0).
    - by apply : cst_continuous.
    (*WARNING : cvg_cst from normedtype applies only to endofunctions
     That should NOT be the case, as one could use it insteas of cst_continuous *)
  - move/eqP => vneq0 ; apply : (cvgP (l := v *: l)). (*chainage avant et suff *) 
    have eqnear0 : {near (locally' (0 : R)), (v \*: quotC) \o mulv =1 quotR}.
      exists 1 => // h _ neq0h //=; rewrite /quotC /quotR /mulv scale_inv.  
      rewrite scalerAl scalerCA -scalecAl mulrA -(mulrC v) mulfV. 
      rewrite mul1r; apply: (scalerI (neq0h)).
        by rewrite !scalerA //= (divff neq0h).  
        by []. 
    have subsetfilters: quotR @ locally' 0 `=>` (v \*: quotC) \o mulv @locally' 0.
    by exact: (cvg_eq_loc eqnear0).
    apply: cvg_trans subsetfilters _.
    unshelve apply : cvg_comp.
    - exact  (locally' (0:C)).
    - move => //= A [r [leq0r ballrA]].
      exists (r / (`|[v]|)).
      - apply : mulr_gt0 ; first by []. 
        by rewrite invr_gt0 normm_gt0.
      - move => b; rewrite /AbsRing_ball /ball_ sub0r absRE normrN => ballrb neqb0.
        have ballCrb : (AbsRing_ball 0 r (mulv b)). 
         rewrite  /AbsRing_ball /ball_ sub0r absrN /mulv scalecr absrM abs_normE.  
         rewrite -ltr_pdivl_mulr.
         - by rewrite normCR.
        by rewrite abs_normE normm_gt0. 
      have bneq0C : (b%:C != 0%:C) by move: neqb0; apply: contra; rewrite eqCr.
      by apply: (ballrA (mulv b) ballCrb); rewrite scaler_eq0; apply/norP; split.
    suff : v \*: quotC @ locally' (0 : C) -->  v *: l by []. 
    by apply: cvgZr ; rewrite /quotC.
Qed.      

Lemma holo_CauchyRieman (f : C^o -> C^o) c: (holomorphic f c) -> (CauchyRiemanEq f c). 
Proof.
  move => H; rewrite /CauchyRiemanEq.
  pose quotC := (fun h : C => h^-1 *: ((f \o shift c) (h) - f c)).
  pose quotR := (fun h : R => h^-1 *: ((f \o shift c) (h *: 1%:C ) - f c)).
  pose quotiR := (fun (h : R) => h^-1 *: ((f \o shift c) (h *: 'i%C) - f c)).
  have eqnear0x : {near (locally' 0), quotC \o ( fun h => h *: 1%:C) =1 quotR}.
     exists 1 ; first by [] ; move => h  _ _ //=; simpc.
       by rewrite /quotC /quotR real_complex_inv -scalecr; simpc.
  pose subsetfiltersx := (cvg_eq_loc eqnear0x).
  have -> : lim (quotR @ (locally' 0))
           = lim (quotC @ (locally' 0)).  
  apply: cvg_map_lim.  
  suff: quotR @ (locally' 0) `=>` (quotC @ (locally' 0)). 
    move => H1; apply: (cvg_translim H1) ;  exact H. (*can't apply a view*)
    apply :  cvg_trans.   
    - exact : (subsetfiltersx (locally'_filter 0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : cvg_comp. 
    (*just showing that linear maps preserve balls 
     - general lemma ? *)
       - exact (locally' 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc.      
         apply :  (absringrA h%:C).
          - by apply : absring_real_complex.
          - by rewrite eqCr .
  by [].
  have eqnear0y : {near (locally' 0), 'i \*:quotC  \o ( fun h => h *: 'i%C)  =1 quotiR }.
    exists 1 ; first by [] ; move => h _ _ //= ;  simpc.
    rewrite /quotC /quotiR (Im_mul h) invcM.   
    rewrite scalerA real_complex_inv Im_inv !scalecr; simpc ; rewrite (Im_mul h).
    by rewrite !real_complexE.
  pose subsetfiltersy := (cvg_eq_loc eqnear0y). 
  have properlocally' : ProperFilter (locally'(0:C)).
  (*This should be Canonical *)
  split.
   - rewrite /locally' /within => [[r leq0r] ballrwithin]; apply: (ballrwithin ((r/2)%:C) _). 
     rewrite /AbsRing_ball /ball_ absCE sub0r normcN //= .
     rewrite expr0n //= addr0 sqrtr_sqr //= ger0_norm.
     rewrite ltr_pdivr_mulr ; last by [] .
     rewrite ltr_pmulr ; last by  [].
     by apply: ltr_spaddl. (* 1 < 2 *)
     by apply : divr_ge0; apply ltrW. 
     have : (r / 2 != 0) by apply: mulf_neq0 ;apply: lt0r_neq0.
     have -> : (0 = 0%:C) by move => K //=. 
     by apply: contra=> /eqP /complexI /eqP.
     (* une vue permet d'abord d'utiliser une implication sur le terme 
      en tête sans avoir à l 'introduire*)  
   - by apply: locally'_filter.
  have <- : lim (quotiR @ (locally' 0))
           = 'i * lim (quotC @ (locally' 0)).
    have -> : 'i * lim (quotC @ (locally' 0)) 
           =  lim ('i \*: quotC @ (locally' 0)). 
      rewrite  scalei_muli  limin_scaler; first by [].  
      by exact: H.
    apply: cvg_map_lim.
         suff: quotiR @ (locally' 0)
                   `=>` ('i \*: quotC @ (locally' 0)).
         move => H1 ; apply: cvg_translim.
         - exact: H1.
         - by apply : cvg_scaler; exact : H. 
    apply: cvg_trans.   
    - apply : (subsetfiltersy (locally'_filter 0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : cvg_comp. 
       - exact (locally' 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0; simpc. 
         apply: (absringrA). 
          - by apply : absring_real_Im.
          - by rewrite eqCI.
      rewrite filter_of_filterE.
    by []. 
 by [].
Qed.



(* Local Notation "''D_' v f" := (derive f ^~ v). *)
(* Local Notation "''D_' v f c" := (derive f c v). *)

Print derive. 
 Lemma Diff_CR_holo (f : C -> C) : (*This does not work pointwise *)
   (forall c v : C, derivable ( f : C_RnormedType -> C_RnormedType) c v)
   /\ (forall c, CauchyRiemanEq f c) ->(forall c, (holomorphic f c)).
 (*sanity check : derivable (f : C ->C) does not type check  *)
 Proof.
   move => [der CR] c. 
   (* (* first attempt with littleo but requires to mix littleo on filter on different types ...*) *)
   suff :  exists l, forall h : C_absRingType,
         f (c + h) = f c + h * l + 'o_[filter of locally (0 : C)] id  h.
   admit.
   move: (der c 1%:C ); simpl => /cvg_ex [lr /cvg_lim //= Dlr].
   move: (der c 'i); simpl  => /cvg_ex [li /cvg_lim //= Dli].
   simpl in (type of lr); simpl in (type of Dlr).
   simpl in (type of li); simpl in (type of Dli).
   move : (CR c) ; rewrite /CauchyRiemanEq //=  (Dlr) (Dli) => CRc.
   pose l:= ((lr + lr*'i)) ; exists l; move  => [a b].
   move: (der (c + a%:C)  'i); simpl => /cvg_ex [//= la /cvg_lim //= Dla].
   move: (der (c + a%:C) 'i) => /derivable_locallyxP.
   rewrite /derive //= Dla => oR.
   have -> : (a +i* b) = (a%:C + b*: 'i%C) by simpc.
   rewrite addrA oR.
   (*have fun a => la = cst(lr) + o_0(a). *)
   move: (der c 1%:C); simpl => /derivable_locallyxP ; rewrite /derive //= Dlr => oC.
   (* rewrite [a%:C]/(a *: 1%:C). *)
   have -> : a%:C = (a *: 1%:C) by simpc.
   rewrite oC. Print real_complex. 
   have lem : (fun a =>( la - lr)) = 'o_[ filter of locally (0:R)] (@real_complex R) .
   (*tried : la - lr = 'o_[ filter of locally (0:R)] (@real_complex R) a :> C^o *)
   move => s0.  Check eqoE.
   suff :   (fun _ : R => la - lr) = 'a_o_[filter of locally (0:R)] (real_complex R).
   admit.
   move => s1. 
   (*eqoE and eqoP are not working*) 
   (* struggling with o *)
   (* (*another attempt*) *)
   (* rewrite /holomorphic cvg_ex.  *)
   (* move: (der c 1%:C ); simpl => /cvg_ex [lr //= Dlr].  *)
   (* move: (der c 'i); simpl  => /cvg_ex [li //= Dli]. *)
   (* simpl in (type of lr); simpl in (type of Dlr). *)
   (* simpl in (type of li); simpl in (type of Dli). *)
   (* move : (CR c) ; rewrite /CauchyRiemanEq //=  (cvg_lim Dlr) (cvg_lim Dli) => CRc. *)
   (* pose l:= ((lr + lr*'i)) ; exists l; move => A //= [r leq0r] normrA. *)
   (* pose r':= r/(sqrtr 2). *)
   (* have lrl : l / (1 + 'i*1) = lr. admit.   *)
   (* exists r ; first by [].     *)
   (* move => [a b] ballab abneq0 //=.  *)
   (* suff :   normc (l- (a +i* b)^-1 *: ((f (a +i* b + c) - f c) : C^o)) <= r.      *)
   (* admit. *)
   (* have : locally lr A. exists r'. *)
   (* - by rewrite mulr_gt0 //= invr_gt0 sqrtr_gt0.  *)
   (* - move => t; rewrite /ball_ -lrl.admit. *)
   (*   (*we should have a tactic rewriting in any way that fits *) *)
   (* move => /Dlr //=. *)
   (* move : (Dli A) => //=.   
     *)
 Admitted.
 
Theorem CauchyRiemann (f : C^o -> C^o) c:  ((holomorphic f c))
          <-> (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c). 
Proof.
Admitted.




End Holomorphe.