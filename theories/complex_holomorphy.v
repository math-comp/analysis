(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)


(* This is the tentative adaptation of the real-closed/complex.v file to a self-contained   *)
(* description of complex theory and holomorphy  *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum seq .
Require Import boolp reals Rstruct Rbar derive.
From mathcomp Require Import bigop  ssrint div ssrnum rat poly closed_field.
From mathcomp Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
Require Import classical_sets posnum topology normedtype landau integral reals.


(* Require Import bigop ssralg ssrint div ssrnum rat poly closed_field. *)
(* Require Import classical_sets posnum topology normedtype landau integral.  *)
(* From mathcomp *)
(* Require Import matrix mxalgebra tuple mxpoly zmodp binomial. *)

(*TODO : Definition integrale sur chemin et segment, holomorhpe, ouvert étoilé *)
(* TODO : cloner depuis integrale et commiter. Admettre la mesure sur R  *)


(*Pour distinguer fonctions mesurables et integrables, utiliser des structures comme posrel. *)
Import GRing.Theory Num.Theory (*ComplexField*) Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.



(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)
(* (* Obligation Tactic := idtac. *) *)


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

Record complex (R : Type) : Type := Complex { Re : R; Im : R }.

Delimit Scope complex_scope with C.
Local Open Scope complex_scope.

Definition real_complex_def (F : ringType) (phF : phant F) (x : F) :=
  Complex x 0.
Notation real_complex F := (@real_complex_def _ (Phant F)).
Notation "x %:C" := (real_complex _ x)
  (at level 2, left associativity, format "x %:C")  : complex_scope.
Notation "x +i* y" := (Complex x y) : complex_scope.
Notation "x -i* y" := (Complex x (- y)) : complex_scope.
Notation "x *i " := (Complex 0 x) (at level 8, format "x *i") : complex_scope.
Notation "''i'" := (Complex 0 1) : complex_scope.
Notation "R [i]" := (complex R)
  (at level 2, left associativity, format "R [i]").

(* Module ComplexInternal. *)
Module ComplexEqChoice.
Section ComplexEqChoice.

Variable R : Type.

Definition sqR_of_complex (x : R[i]) := let: a +i* b := x in [:: a ; b].
Definition complex_of_sqR (x : seq R) :=
  if x is [:: a; b] then Some (a +i* b) else None.

Lemma complex_of_sqRK : pcancel sqR_of_complex complex_of_sqR.
Proof. by case. Qed.

End ComplexEqChoice.
End ComplexEqChoice.

Definition complex_eqMixin (R : eqType) :=
  PcanEqMixin (@ComplexEqChoice.complex_of_sqRK R).
Definition complex_choiceMixin  (R : choiceType) :=
  PcanChoiceMixin (@ComplexEqChoice.complex_of_sqRK R).
Definition complex_countMixin  (R : countType) :=
  PcanCountMixin (@ComplexEqChoice.complex_of_sqRK R).

Canonical complex_eqType (R : eqType) :=
  EqType R[i] (complex_eqMixin R).
Canonical complex_choiceType (R : choiceType) :=
  ChoiceType R[i] (complex_choiceMixin R).
Canonical complex_countType (R : countType) :=
  CountType R[i] (complex_countMixin R).

Lemma eq_complex : forall  (x y : complex R),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=>  [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma complexr0 : forall (x : R), x +i* 0 = x%:C. Proof. by []. Qed.

Module ComplexField.
Section ComplexField.

Local Notation C := R[i].
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition addc (x y : R[i]) := let: a +i* b := x in let: c +i* d := y in
  (a + c) +i* (b + d).
Definition oppc (x : R[i]) := let: a +i* b := x in (- a) +i* (- b).

Program Definition complex_zmodMixin := @ZmodMixin _ C0 oppc addc _ _ _ _.
Next Obligation. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.
Next Obligation. by move=> [a b] [c d] /=; congr (_ +i* _); rewrite addrC. Qed.
Next Obligation. by move=> [a b] /=; rewrite !add0r. Qed.
Next Obligation. by move=> [a b] /=; rewrite !addNr. Qed.
Canonical complex_zmodType := ZmodType R[i] complex_zmodMixin.

Definition scalec (a : R) (x : R[i]) := 
  let: b +i* c := x in (a * b) +i* (a * c).

Program Definition complex_lmodMixin := @LmodMixin _ _ scalec _ _ _ _.
Next Obligation.  by move=> a b [c d] /=; rewrite !mulrA. Qed.
Next Obligation. by move=> [a b] /=; rewrite !mul1r. Qed.
Next Obligation. by move=> a [b c] [d e] /=; rewrite !mulrDr. Qed.
Next Obligation. by move=> [a b] c d /=; rewrite !mulrDl. Qed.
Canonical complex_lmodType := LmodType R R[i] complex_lmodMixin.

Definition mulc (x y : R[i]) := let: a +i* b := x in let: c +i* d := y in
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

Definition invc (x : R[i]) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
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
Canonical complex_ringType :=RingType R[i] complex_comRingMixin.
Canonical complex_comRingType := ComRingType R[i] mulcC.

Lemma mulVc : forall x, x != C0 -> mulc (invc x) x = C1.
Proof.
move=> [a b]; rewrite eq_complex => /= hab; rewrite !mulNr opprK.
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr complexr0 -mulrDl mulfV //.
by rewrite paddr_eq0 -!expr2 ?expf_eq0 ?sqr_ge0.
Qed.

Lemma invc0 : invc C0 = C0. Proof. by rewrite /= !mul0r oppr0. Qed.

Definition complex_fieldUnitMixin := FieldUnitMixin mulVc invc0.
Canonical complex_unitRingType := UnitRingType C complex_fieldUnitMixin.
Canonical complex_comUnitRingType := Eval hnf in [comUnitRingType of R[i]].

Lemma field_axiom : GRing.Field.mixin_of complex_unitRingType.
Proof. by []. Qed.

Definition ComplexFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical complex_idomainType := IdomainType R[i] (FieldIdomainMixin field_axiom).
Canonical complex_fieldType := FieldType R[i] field_axiom.

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)].

Lemma real_complex_is_rmorphism : rmorphism (real_complex R).
Proof.
split; [|split=> //] => a b /=; simpc; first by rewrite subrr.
by rewrite !mulr0 !mul0r addr0 subr0.
Qed.

Canonical real_complex_rmorphism :=
  RMorphism real_complex_is_rmorphism.
Canonical real_complex_additive :=
  Additive real_complex_is_rmorphism.

Lemma Re_is_scalar : scalar (@Re R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Re_additive := Additive Re_is_scalar.
Canonical Re_linear := Linear Re_is_scalar.

Lemma Im_is_scalar : scalar (@Im R).
Proof. by move=> a [b c] [d e]. Qed.

Canonical Im_additive := Additive Im_is_scalar.
Canonical Im_linear := Linear Im_is_scalar.

Definition lec (x y : R[i]) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc (x y : R[i]) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Definition normc (x : R[i]) : R :=
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
Canonical complex_numDomainType := NumDomainType R[i] complex_numMixin.

End ComplexField.
End ComplexField.

Canonical ComplexField.complex_zmodType.
Canonical ComplexField.complex_lmodType.
Canonical ComplexField.complex_ringType.
Canonical ComplexField.complex_comRingType.
Canonical ComplexField.complex_unitRingType.
Canonical ComplexField.complex_comUnitRingType.
Canonical ComplexField.complex_idomainType.
Canonical ComplexField.complex_fieldType.
Canonical ComplexField.complex_numDomainType.
Canonical complex_numFieldType := [numFieldType of complex R].
Canonical ComplexField.real_complex_rmorphism.
Canonical ComplexField.real_complex_additive.
Canonical ComplexField.Re_additive.
Canonical ComplexField.Im_additive.

Definition conjc {R : ringType} (x : R[i]) := let: a +i* b := x in a -i* b.
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


Lemma ReiNIm : forall x : R[i], Re (x * 'i%C) = - Im x.
Proof. by case=> a b; simpc. Qed.

Lemma ImiRe : forall x : R[i], Im (x * 'i%C) = Re x.
Proof. by case=> a b; simpc. Qed.

Lemma complexE x : x = (Re x)%:C + 'i%C * (Im x)%:C :> R[i].
Proof. by case: x => *; simpc. Qed.

Lemma real_complexE x : x%:C = x +i* 0 :> R[i]. Proof. done. Qed.

Lemma sqr_i : 'i%C ^+ 2 = -1 :> R[i].
Proof. by rewrite exprS; simpc; rewrite -real_complexE rmorphN. Qed.

Lemma complexI : injective (real_complex R). Proof. by move=> x y []. Qed.

Lemma ler0c (x : R) : (0 <= x%:C) = (0 <= x). Proof. by simpc. Qed.

Lemma lecE : forall x y : R[i], (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y : R[i], (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; simpc. Qed.

Lemma ltcR : forall x y : R, (x%:C < y%:C) = (x < y).
Proof. by move=> x y; simpc. Qed.


Lemma conjc_is_rmorphism : rmorphism (@conjc R_ringType).
Proof.
split=> [[a b] [c d] | ] /=; first by simpc; rewrite [d - _]addrC.
by split=> [[a b] [c d] | ] /=; simpc.
Qed.

Lemma conjc_is_scalable : scalable (@conjc R_ringType ).
Proof. by move=> a [b c]; simpc. Qed.

Canonical conjc_rmorphism := RMorphism conjc_is_rmorphism.
Canonical conjc_additive := Additive conjc_is_rmorphism.
Canonical conjc_linear := AddLinear conjc_is_scalable.

Lemma conjcK : involutive (@conjc R_ringType).
Proof. by move=> [a b] /=; rewrite opprK. Qed.

Lemma mulcJ_ge0 (x : R[i]) : 0 <= x * x^*%C.
Proof.
by move: x=> [a b]; simpc; rewrite mulrC addNr eqxx addr_ge0 ?sqr_ge0.
Qed.

Lemma conjc_real (x : R) : x%:C^* = x%:C.
Proof. by rewrite /= oppr0. Qed.

Lemma ReJ_add (x : R[i]) : (Re x)%:C =  (x + x^*%C) / 2%:R.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 // -natrM pnatr_eq0.
Qed.

Lemma ImJ_sub (x : R[i]) : (Im x)%:C =  (x^*%C - x) / 2%:R * 'i%C.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 ?opprK // -natrM pnatr_eq0.
Qed.

Lemma ger0_Im (x : R[i]) : 0 <= x -> Im x = 0.
Proof. by move: x=> [a b] /=; simpc => /andP [/eqP]. Qed.

(* Todo : extend theory of : *)
(*   - signed exponents *)

Lemma conj_ge0 : forall x : R[i], (0 <= x ^* ) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite oppr_eq0. Qed.

Lemma conjc_nat : forall n, (n%:R : R[i])^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : R[i]) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : R[i]) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x : R[i], (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_complex /= eqr_oppLR oppr0. Qed.

Lemma conjc_inv: forall x : R[i], (x^-1)^* = (x^*%C )^-1.
Proof. exact: fmorphV. Qed.

Lemma complex_root_conj (p : {poly R[i]}) (x : R[i]) :
  root (map_poly conjc p) x = root p x^*.
Proof. by rewrite /root -{1}[x]conjcK horner_map /= conjc_eq0. Qed.


(* Lemma complex_algebraic_trans (T : comRingType) (toR : {rmorphism T -> R}) : *)
(*   integralRange toR -> integralRange (real_complex R \o toR). *)
(* Proof. *)
(* set f := _ \o _ => R_integral [a b]. *)
(* have integral_real x : integralOver f (x%:C) by apply: integral_rmorph. *)
(* rewrite [_ +i* _]complexE. *)
(* apply: integral_add => //; apply: integral_mul => //=. *)
(* exists ('X^2 + 1). *)
(*   by rewrite monicE lead_coefDl ?size_polyXn ?size_poly1 ?lead_coefXn. *)
(* by rewrite rmorphD rmorph1 /= ?map_polyXn rootE !hornerE -expr2 sqr_i addNr. *)
(* Qed. *)

Lemma normc_def (z : R[i]) : `|z| = (sqrtr ((Re z)^+2 + (Im z)^+2))%:C.
Proof. by case: z. Qed.

Lemma add_Re2_Im2 (z : R[i]) : ((Re z)^+2 + (Im z)^+2)%:C = `|z|^+2.
Proof. by rewrite normc_def -rmorphX sqr_sqrtr ?addr_ge0 ?sqr_ge0. Qed.

Lemma addcJ (z : R[i]) : z + z^*%C = 2%:R * (Re z)%:C.
Proof. by rewrite ReJ_add mulrC mulfVK ?pnatr_eq0. Qed.

Lemma subcJ (z : R[i]) : z - z^*%C = 2%:R * (Im z)%:C * 'i%C.
Proof.
rewrite ImJ_sub mulrCA mulrA mulfVK ?pnatr_eq0 //.
by rewrite -mulrA ['i%C * _]sqr_i mulrN1 opprB.
Qed.

Lemma complex_real (a b : R) : a +i* b \is Num.real = (b == 0).
Proof.
rewrite realE; simpc; rewrite [0 == _]eq_sym.
by have [] := ltrgtP 0 a; rewrite ?(andbF, andbT, orbF, orbb).
Qed.

Lemma complex_realP (x : R[i]) : reflect (exists y, x = y%:C) (x \is Num.real).
Proof.
case: x=> [a b] /=; rewrite complex_real.
by apply: (iffP eqP) => [->|[c []//]]; exists a.
Qed.

Lemma RRe_real (x : R[i]) : x \is Num.real -> (Re x)%:C = x.
Proof. by move=> /complex_realP [y ->]. Qed.

Lemma RIm_real (x : R[i]) : x \is Num.real -> (Im x)%:C = 0.
Proof. by move=> /complex_realP [y ->]. Qed.

End ComplexTheory.


Section ComplexClosedTheory.


(* Lemma complexiE : 'i%C = 'i%R :> R[i]. *)
(* Proof. by []. Qed. *)

(* Lemma complexRe (x : R[i]) : (Re x)%:C = 'Re x. *)
(* Proof. *)
(* rewrite {1}[x]Crect raddfD /= mulrC ReiNIm rmorphB /=. *)
(* by rewrite ?RRe_real ?RIm_real ?Creal_Im ?Creal_Re // subr0. *)
(* Qed. *)

(* Lemma complexIm (x : R[i]) : (Im x)%:C = 'Im x. *)
(* Proof. *)
(* rewrite {1}[x]Crect raddfD /= mulrC ImiRe rmorphD /=. *)
(* by rewrite ?RRe_real ?RIm_real ?Creal_Im ?Creal_Re // add0r. *)
(* Qed. *)

(* End ComplexClosedTheory *)
(* . *)


Import ComplexField. 

(* Local Notation sgr := Num.sg. *)
(* Local Notation sqrtr := Num.sqrt. *)
Local Notation C := R[i]. 
Local Open Scope complex_scope.  (*  *)
(* Notation Re:= Re. *)
(* Notation Im:= (complex.Im). *)



  
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


Lemma normc_i (x : R) : normc (x*i) = normr (x).
Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

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

Lemma Im_inv : ('i%C)^-1 = (-1*i) :> C.
Proof. Admitted.  

Lemma invcM : forall x y : C, (x*y)^-1 = x^-1 * y^-1. (*Maybe another lemma is doing that, or invrM *)
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
Proof. by move => [a b ] r ; rewrite  eqE_complex //= ; split ;  simpc. Qed.

About AbsRing_ball.

 
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

Variable (R : rcfType). 

Definition C_RlmodMixin := complex_lmodMixin.  (*R instead of R_rcfType is not working *)
(*LmodType is hard to use, not findable through Search and not checkable as abbreviation is not applied enough*)
Definition C_RlmodType := @LmodType R C C_RlmodMixin.

(* C as a uniformtype *)
Definition C_pointedType := PointedType C 0.
Canonical C_pointedType.
Definition C_filteredType := FilteredType C C (locally_ (ball_ (@normc R))).
Canonical C_filteredType.
(*Are we sure that the above is canonical *)

Program Definition C_RuniformMixin := @uniformmixin_of_normaxioms C_RlmodType (@normc R) normcD normcZ (@eq0_normc R).
Definition C_RtopologicalMixin := topologyOfBallMixin C_RuniformMixin.
Definition C_RtopologicalType := TopologicalType C_filteredType C_RtopologicalMixin.
Definition C_RuniformType := @UniformType C_RtopologicalType C_RuniformMixin.


Program Definition C_RnormedMixin
  := @NormedModMixin R_absRingType C_RlmodType _ C_RuniformMixin (@normc R) normcD normcZ _  (@eq0_normc R) .
Next Obligation. by []. Qed. 


Definition C_RnormedType : normedModType R := @NormedModType R C_RuniformType C_RnormedMixin.
End C_Rnormed.


Section C_absRing.

  Definition C_AbsRingMixin := @AbsRingMixin (complex_ringType R_rcfType) (@normc R_rcfType) normc0 normcN1 normcD (@normcM R_rcfType ) (@eq0_normc R_rcfType).
  Definition C_absRingType :=  AbsRingType C C_AbsRingMixin.
  Canonical C_absRingType.

  
  
  Definition C_lmodtype :=  @LmodType C C C_AbsRingMixin. Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass
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


  Lemma absring_real_complex : forall r: R, forall x : R, AbsRing_ball 0 r x -> (@AbsRing_ball C_absRingType 0%:C r x%:C).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE.
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_r. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.


  Lemma absring_real_Im :  forall r: R, forall x : R, AbsRing_ball 0 r x -> (@AbsRing_ball C_absRingType 0%:C r x*i).
  Proof.
    move => r x ballrx.   
    rewrite /AbsRing_ball /ball_ absCE. 
    rewrite addrC addr0 -scaleN1r normcZ normrN1 mul1r normc_i. 
    move : ballrx ; rewrite /AbsRing_ball /ball_ absRE.
    by rewrite addrC addr0 normrN. 
  Qed.
  Check scalec.
  Unset Printing Notations.
  (* Lemma scalei_muli : forall z : C^o,  (mulc 'i  z) = ('i *: z). *)
  (* Proof. *)
  (*   by []. *)
  (* Qed. *)

  Lemma iE : 'i%C = 'i :> C.
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
(*Diff is defined from any normedmodule of any absringtype, so C is a normedmodul on itsself *)
(*Vague idea that this should work, as we see C^o as a vector space on C and not R*)


(*Important : differentiable in derive.v, means continuoulsy differentiable, not just that the limit exists. *)
(*derivable concerns only the existence of the derivative *)

Definition holomorphic (f : Co_normedType -> Co_normedType) c := forall v,
cvg ((fun h => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' (0 : Co_normedType)).

Definition complex_realfun (f : C^o -> C^o) : C_RnormedType -> C_RnormedType := f.

Definition complex_Rnormed_absring : C_RnormedType -> C^o := id. (* Coercion ? *) (*Avec C tout seul au lieu de C_absRIng ça devrait passer *) 


(* Variable ( h : C_RnormedType -> C_RnormedType) (x : C_RnormedType).  *)

(* Check ('D_x h 0). (*This has a weird type *) *)
 
Definition CauchyRiemanEq_R2 (f : C_RnormedType -> C_RnormedType) c :=
  let u := (fun c => Re ( f c)): C_RnormedType -> R^o  in 
  let v:= (fun c => Im (f c)) :  C_RnormedType -> R^o in
  (* ('D_(1%:C) u = 'D_('i) v) /\ ('D_('i) u = 'D_(1%:C) v). *)
  (((derive u c (1%:C)) = 
         (derive v c ('i))) /\ ((derive v c (1%:C)) = -(derive u c ('i)))).
Check derive. (*derive is explicitely for R normed spaces *)
Check derivable. 

Definition deriveC (V W : normedModType C)(f : V -> W) c v :=
  lim ((fun h => h^-1 *: ((f \o shift c) (h *: v) - f c)) @ locally' (0 : C^o)).


Definition CauchyRiemanEq (f : C -> C) z:=
  'i * lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 1%:C) - f z)) @ locally' (0 : R^o)) =
   lim ((fun h : R => h^-1 *: ((f \o shift z) (h *: 'i%C) - f z)) @ locally' (0 : R^o)).

  
Lemma eqCr (R : rcfType) (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (R : rcfType) (r s : R) : (r*i == s*i) = (r == s).
Proof. Admitted.


(*Lemma lim_trans (T : topologicalType) (F : set (set T))  (G : set (set T)) (l : T) : ( F `=>` G ) -> (G --> l) -> ( F --> l). 
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
  by move => /cvg_ex [l H0] ; apply : cvgP ; apply :(@cvgZr _ _ _ F _ f k l).
Qed.

About cvgZr. 


Lemma limin_scaler (K : absRingType) (V : normedModType K) (T : topologicalType)
      (F : set (set T)) (FF :Filter F) (f : T -> V) (k : K) :
      cvg(f@F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof.
  move => /cvg_ex [l H].
  (*rewrite (cvg_lim H). *)
(*   The LHS of (cvg_lim H) *)
(*     (lim (f @ F)) *)
(* matches but type classes inference fails *)
(*   Check (cvg_lim (@cvgZr K V T F FF f k l H)). *)
 Admitted. 


(*this could be done for scale also ... *)

(*I needed filter_of_filterE to make things easier - looked a long time of it as I was lookin for a [filter of lim]* instead of a [filter of filter]*)

(*There whould be a lemma analogous to [filter of lim] to ease the search  *)

(* 

Lemma filter_of_filterE {T : Type} (F : set (set T)) : [filter of F] = F.
Proof. by []. Qed.

Lemma locally_filterE {T : Type} (F : set (set T)) : locally F = F.
Proof. by []. Qed.

Module Export LocallyFilter.
Definition locally_simpl := (@filter_of_filterE, @locally_filterE).
End LocallyFilter.

Definition cvg_to {T : Type} (F G : set (set T)) := G `<=` F.
Notation "F `=>` G" := (cvg_to F G) : classical_set_scope.
Lemma cvg_refl T (F : set (set T)) : F `=>` F.
Proof. exact. Qed.

Lemma cvg_trans T (G F H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Notation "F --> G" := (cvg_to [filter of F] [filter of G]) : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filteredType U) :=
  fun F : set (set U) => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T [filter of F]) : classical_set_scope.
Notation lim F := [lim F in [filteredType _ of @type_of_filter _ [filter of F]]].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := [cvg F in [filteredType _ of @type_of_filter _ [filter of F]]].
*)



Lemma holo_derivable  (f : C^o -> C^o) c :  ((holomorphic f c))
                                            -> (forall v : C, derivable (complex_realfun f) c v).
Proof.
 move => H; rewrite /derivable => v. 
  move : (H v) => /cvg_ex [l H0] {H}. (* eapply*)
  apply : (cvgP (l := l)).
  - have eqnear0 : {near (@locally' R_topologicalType  0),
     (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h *: (complex_Rnormed_absring v)) - f c))
       \o (real_complex R) =1
     (fun h0 : R_absRingType => h0^-1 *: ((complex_realfun f \o shift c) (h0 *: v )
     - complex_realfun f c)) }.
    exists 1 ; first by [] ;  move => h _ neq0h //=; rewrite real_complex_inv -scalecr.    
    by apply : (scalerI (neq0h)) ; rewrite !scalerA //= (divff neq0h) !scale1r //= -scalecr. 
  pose subsetfilters:= (cvg_eq_loc eqnear0).  
  apply :  (@cvg_trans _ ( (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h *: (complex_Rnormed_absring v)) - f c)) \o (real_complex R) @ (@locally' R_topologicalType  0))).
  exact : (subsetfilters (@locally'_filter R_topologicalType  0)).
- unshelve apply : cvg_comp.
  exact (locally' 0%:C).
- move => //= A  [r [leq0r ballrA]] ; exists r ; first by []. 
  move => b ballrb neqb0.   
  have ballCrb : (AbsRing_ball 0%:C r b%:C).
   by apply : absring_real_complex.
  have bneq0C : (b%:C != 0%:C) by move : neqb0 ; apply : contra ; rewrite eqCr.
  by apply : (ballrA b%:C ballCrb bneq0C).
by []. 
Qed.

Lemma holo_CauchyRieman (f : C^o -> C^o) c : (holomorphic f c) -> (CauchyRiemanEq f c). 
Proof.
  move => H. (* move : (H 1%:C) => /cvg_ex [l H0] {H}. *)
  (* move :  l H0 ; rewrite filter_of_filterE => l H0. *)
  pose quotC := (fun h : C_absRingType => h^-1 *: ((f \o shift c) (h * 1%:C) - f c)).
  pose quotR := (fun h : R_absRingType => h^-1 *: ((f \o shift c) (h *: 1%:C ) - f c)).
  pose quotiR := (fun (h : R) => h^-1 *: ((f \o shift c) (h *: 'i%C) - f c)).
  have eqnear0x : {near (@locally' R_topologicalType 0), quotC \o ( fun h => h *: 1%:C)  =1 quotR }.
     exists 1 ; first by [] ; move => h  _ _ //= ;  simpc.
     by rewrite /quotC /quotR real_complex_inv -scalecr ; simpc. 
  pose subsetfiltersx := (cvg_eq_loc eqnear0x).
  rewrite /CauchyRiemanEq.
  have -> : lim (quotR @ (@locally' R_topologicalType 0))
           = lim (quotC @ (@locally' C_topologicalType 0) ).  
  apply:  (@cvg_map_lim _ _ _ (@locally' R_topologicalType 0) _ _ (lim (quotC @ (@locally' C_topologicalType 0) ))).
  suff :  quotR @ (@locally' R_topologicalType 0) `=>` (quotC @ (@locally' C_topologicalType 0)).
          by move => H1 ; apply :  (cvg_translim H1) ;  exact : H.   
  apply :  cvg_trans.   
    - exact : (subsetfiltersx (@locally'_filter R_topologicalType  0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : cvg_comp. 
    (*just showing that linear maps preserve balls - general lemma ? *)
       - exact  (@locally' C_topologicalType 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc.      
         apply :  (absringrA h%:C).
          - by apply : absring_real_complex.
          - by rewrite eqCr .
  by [].
  have eqnear0y : {near (@locally' R_topologicalType 0), 'i \*:quotC  \o ( fun h => h *: 'i%C)  =1
                   quotiR }.
    exists 1 ; first by [] ; move => h _ _ //= ;  simpc . rewrite /quotC /quotiR (Im_mul h) invcM.   
    rewrite scalerA real_complex_inv Im_inv !scalecr; simpc ; rewrite (Im_mul h).
  by rewrite !real_complexE.
  pose subsetfiltersy := (cvg_eq_loc eqnear0y).
  have <- : lim (quotiR  @ (@locally' R_topologicalType 0))
           = 'i * lim (quotC @ (@locally' C_topologicalType 0)).
    have -> : 'i * lim (quotC @ (@locally' C_topologicalType 0))
           =  lim ('i \*: quotC @ (@locally' C_topologicalType 0)). 
      rewrite  scalei_muli ; rewrite  (limin_scaler _ ('i) ).
       - by [].
       - exact : H.       
    apply :  (@cvg_map_lim _ _ _ (@locally' R_topologicalType 0) _ _ (lim ('i \*:quotC @ (@locally' C_topologicalType 0) ))).
    suff :  quotiR @ (@locally' R_topologicalType 0)
                   `=>` ('i \*: quotC @ (@locally' C_topologicalType 0)).
      move => H1 ; apply : (cvg_translim H1) .
      by apply :(@cvg_scaler _ _ _ _ _ quotC ('i) ) ; exact : H. 
    apply :  cvg_trans.   
    - apply : (subsetfiltersy (@locally'_filter R_topologicalType  0)).
      move => {subsetfiltersx eqnear0x}.
    - unshelve apply : cvg_comp. 
       - exact  (@locally' C_topologicalType 0). 
       - move => A //= [r leq0r] absringrA. 
         exists r ; first by [].   
         move => h absrh hneq0 ; simpc. 
         apply :  (absringrA h*i).
          - by apply : absring_real_Im.
          - by rewrite eqCI.
      rewrite filter_of_filterE.
    by []. 
 by [].
Qed.


Theorem CauchyRiemann (f : C^o -> C^o) c:  ((holomorphic f c))
          <-> (forall v : C, derivable (complex_realfun f) c v) /\ (CauchyRiemanEq f c). 
Proof.
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
