From HB Require Import structures.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect ssralg vector ring_quotient finmap.
From mathcomp Require Import boolp functions classical_sets.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

(** Free module *)

Section FreeLmod.
Context {R : pzRingType} {T : choiceType}.

Definition free_lmod := {fsfun T -> R with 0}.

HB.instance Definition _ := Choice.on free_lmod.

Section lmodType.

(* This is the unit of the monad *)
Elpi lock Definition free_lmod_unit (x : T) : free_lmod :=
  [fsfun [fsfun] with x |-> 1].

Elpi lock Definition zero_subdef : free_lmod := [fsfun].
Local Notation zero := zero_subdef.

Let zeroE x : zero x = 0.
Proof. by rewrite [zero]unlock fsfunE. Qed.

Elpi lock Definition opp_subdef (f : free_lmod) : free_lmod :=
   [fsfun x in finsupp f => - (f x)].
Local Notation opp := opp_subdef.

Lemma oppE (f : free_lmod) x : opp f x = - (f x).
Proof.
by rewrite [opp]unlock fsfunE mem_finsupp; case: eqP => //= ->; rewrite oppr0.
Qed.

Elpi lock Definition add_subdef (f g : free_lmod) : free_lmod :=
  [fsfun x in finsupp f `|` finsupp g => f x + g x].
Local Notation add := add_subdef.

Let addE (f g : free_lmod) x : add f g x = f x + g x.
Proof.
rewrite [add]unlock fsfunE in_fsetU !mem_finsupp.
by do 2!case: eqP => //= ->; rewrite addr0.
Qed.

Let addrA : associative add.
Proof. by move=> f g h; apply/fsfunP => x; rewrite !addE addrA. Qed.

Let addrC : commutative add.
Proof. by move=> f g; apply/fsfunP => x; rewrite !addE addrC. Qed.

Let add0r : left_id zero add.
Proof. by move=> f; apply/fsfunP => x; rewrite addE zeroE add0r. Qed.

Let addNr : left_inverse zero opp add.
Proof. by move=> f; apply/fsfunP => x; rewrite addE oppE addNr. Qed.

HB.instance Definition _ :=
  GRing.isZmodule.Build free_lmod addrA addrC add0r addNr.

Elpi lock Definition scale_subdef (a : R) (f : free_lmod) : free_lmod :=
  [fsfun x in finsupp f => a * f x].
Local Notation scale := scale_subdef.

Let scaleE a f x : scale a f x = a * f x.
Proof.
rewrite [scale]unlock fsfunE mem_finsupp.
by case: eqP => //= ->; rewrite mulr0.
Qed.

Let scalerA a b f : scale a (scale b f) = scale (a * b) f.
Proof. by apply/fsfunP => x; rewrite !scaleE mulrA. Qed.

Let scale1r : left_id 1 scale.
Proof. by move=> f; apply/fsfunP => x; rewrite !scaleE mul1r. Qed.

Let scalerDr : right_distributive scale +%R.
Proof.
by move=> a f g; apply/fsfunP => x; rewrite addE !scaleE addE mulrDr.
Qed.

Let scalerDl f : {morph scale^~ f: a b / a + b}.
Proof. by move=> a b; apply/fsfunP => x; rewrite addE !scaleE mulrDl. Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R free_lmod scalerA scale1r scalerDr scalerDl.

Lemma free_lmod0E : (0 : free_lmod) = (fun=> 0) :> (_ -> _).
Proof. exact/funext/zeroE. Qed.

Lemma free_lmodNE (f : free_lmod) : - f = \- f :> (_ -> _).
Proof. exact/funext/oppE. Qed.

Lemma free_lmodDE (f g : free_lmod) : f + g = f \+ g :> (_ -> _).
Proof. exact/funext/addE. Qed.

Lemma free_lmod_sumE I r P (F : I -> free_lmod) :
  \sum_(i <- r | P i) F i = (fun x => \sum_(i <- r | P i) F i x) :> (_ -> _).
Proof.
apply/funext => t; elim/big_ind2: _ => //= x u y v.
by rewrite free_lmodDE/= => -> ->.
Qed.

Lemma free_lmodZE a (f : free_lmod) : a *: f = (fun x => a * f x) :> (_ -> _).
Proof. exact/funext/scaleE. Qed.

Lemma free_lmod_unitE t t' : free_lmod_unit t t' = (t == t')%:R.
Proof.
by rewrite [free_lmod_unit]unlock fsfunE/= !inE/= orbF; case: eqVneq.
Qed.

End lmodType.

Section eval.
Context {U : lmodType R} (f : T -> U).

Elpi lock Definition free_lmod_eval (x : free_lmod) : U :=
   \sum_(t <- finsupp x) x t *: f t.

Lemma free_lmod_eval_linear : linear free_lmod_eval.
Proof.
move=> a x y; rewrite [free_lmod_eval]unlock scaler_sumr.
rewrite (big_fset_incl _ (fsubsetUr (finsupp x `|` finsupp y)%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r.
apply: esym; rewrite (big_fset_incl _ (fsubsetUr (finsupp (a *: x + y)%R `|` (finsupp y))%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r scaler0.
rewrite [X in _ + X](big_fset_incl _ (fsubsetUr (finsupp (a *: x + y)%R `|` (finsupp x))%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r.
rewrite fsetUAC -big_split/= -fsetUA fsetUC.
by apply: eq_bigr => i _; rewrite free_lmodDE/= scalerDl free_lmodZE scalerA.
Qed.

HB.instance Definition _ := GRing.isLinear.Build _ _ _ _ free_lmod_eval free_lmod_eval_linear.

End eval.

End FreeLmod.
Arguments free_lmod : clear implicits.
Notation "x %:lmod" := (free_lmod_unit x).


Section free_lmod_map.
Context {R : comRingType}.
Implicit Types X Y Z : choiceType.

Definition free_lmod_map {X Y}
    (f : X -> Y) (u : free_lmod R X) : free_lmod R Y :=
  free_lmod_eval (free_lmod_unit \o f) u.

Definition free_lmod_map_id {X} : free_lmod_map (@id X) =1 id.
Proof.
move=> u /=; rewrite /free_lmod_map; apply/fsfunP => x /=.
rewrite unlock /= free_lmod_sumE.
case: (finsuppP u x) => [xNu|xu].
  rewrite big1// => i _; rewrite free_lmodZE free_lmod_unitE.
  by case: eqVneq; rewrite (mulr1,mulr0)// => ->; rewrite fsfun_dflt.
rewrite (bigD1_seq x)//= free_lmodZE ?free_lmod_unitE eqxx mulr1 big1 ?addr0//.
by move=> y nyx; rewrite free_lmodZE free_lmod_unitE (negPf nyx) mulr0.
Qed.


Definition free_lmod_map_comp {X Y Z} (f : X -> Y) (g : Y -> Z) :
  free_lmod_map (g \o f) =1 free_lmod_map g \o free_lmod_map f.
Proof.
move=> u /=; rewrite /free_lmod_map/=.
rewrite ![@free_lmod_eval _ _ _ _]unlock.
Admitted.

End free_lmod_map.



HB.mixin Record ZmodQuotient_isLmodQuotient (R : pzRingType) T eqT
  (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (scaleT : R -> T -> T)
  (Q : Type) of ZmodQuotient T eqT zeroT oppT addT Q & GRing.Lmodule R Q := {
  pi_scaler : forall a, {morph \pi_Q : x / scaleT a x >-> a *: x}
}.

#[short(type="lmodQuotType")]
HB.structure Definition LmodQuotient R T eqT zeroT oppT addT scaleT :=
  {Q of ZmodQuotient_isLmodQuotient R T eqT zeroT oppT addT scaleT Q &
   ZmodQuotient T eqT zeroT oppT addT Q & GRing.Lmodule R Q }.

Section LModQuotient.

Variable (R : pzRingType) (T : Type).
Variable eqT : rel T.
Variables (zeroT : T) (oppT : T -> T) (addT : T -> T -> T) (scaleT : R -> T -> T).
Implicit Type zqT : LmodQuotient.type eqT zeroT oppT addT scaleT.

Canonical pi_scale_quot_morph zqT a := PiMorph1 (@pi_scaler _ _ _ _ _ _ _ zqT a).

End LModQuotient.

Section PiLinear.

Variables (R : pzRingType) (L : lmodType R) (equivL : rel L) (zeroL : L).
Variable Q : @lmodQuotType R L equivL zeroL -%R +%R *:%R.

Lemma pi_is_linear : linear \pi_Q.
Proof. by move=> a x y /=; rewrite !piE. Qed.

HB.instance Definition _ := GRing.isLinear.Build R L Q _ \pi_Q pi_is_linear.

End PiLinear.

(* TODO: backport *)
HB.factory Record SubmodClosed_isZmodClosed
  (R : pzRingType) (L : lmodType R) (P : {pred L}) of GRing.SubmodClosed R P :=
  {}.

HB.builders Context R L P of SubmodClosed_isZmodClosed R L P.
Lemma submodClosedB : oppr_closed P.
Proof. by move=> x xP; rewrite -scaleN1r; apply: rpredZ. Qed.

HB.instance Definition _ := GRing.isOppClosed.Build L P submodClosedB.
HB.end.

Module Quotient.
Export Quotient.
Section LmodQuotient.
Variables (R : pzRingType) (L : lmodType R) (P : submodClosed L).

Definition Pzmod : {pred _} := P.
HB.instance Definition _ := GRing.SubmodClosed.on Pzmod.
HB.instance Definition _ := @SubmodClosed_isZmodClosed.Build R L Pzmod.

Definition zmodquot := (quot Pzmod).

Definition scale a := lift_op1 zmodquot ( *:%R a).

Lemma pi_scale a : {morph \pi : x / a *: x >-> scale a x}.
Proof.
move=> x; unlock scale; apply/eqP; rewrite piE equivE.
by rewrite -scalerBr rpredZ// idealrBE reprK.
Qed.

Canonical pi_scale_morph a := PiMorph1 (pi_scale a).

Let scalerA a b f : scale a (scale b f) = scale (a * b) f.
Proof. by rewrite -[f]reprK !piE scalerA. Qed.

Let scale1r : left_id 1 scale.
Proof. by move=> f; rewrite -[f]reprK !piE scale1r. Qed.

Let scalerDr : right_distributive scale +%R.
Proof. by move=> a f g; rewrite -[f]reprK -[g]reprK !piE scalerDr. Qed.

Let scalerDl f : {morph scale^~ f: a b / a + b}.
Proof. by move=> a b; rewrite -[f]reprK !piE scalerDl. Qed.

#[export]
HB.instance Definition _ := ZmodQuotient.on zmodquot.
#[export]
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R zmodquot scalerA scale1r scalerDr scalerDl.
#[export]
HB.instance Definition _ :=
  ZmodQuotient_isLmodQuotient.Build R L (equiv Pzmod) 0 -%R +%R *:%R zmodquot pi_scale.

End LmodQuotient.
Module Exports. HB.reexport. End Exports.
End Quotient.

Export Quotient.Exports.


Module Tensor.
Section fintensor.
Variables (R : fieldType) (U V : vectType R).

Let nU := \dim (@fullv _ U).
Let nV := \dim (@fullv _ V).
Let bU := vbasis (@fullv _ U).
Let bV := vbasis (@fullv _ V).

Definition fintensor := free_lmod R ('I_nU * 'I_nV)%type.

Elpi lock Definition fintensor_proj (x : U * V) : fintensor :=
  [fsfun i in [fset i in 'I_nU] `*` [fset i in 'I_nV]
   => coord bU i.1 x.1 * coord bV i.2 x.2].

End fintensor.

Section span.
Variables (R : comRingType) (U : lmodType R) (X : {fset U}).

Definition span_ideal : {pred free_lmod R X} :=
  [pred x | free_lmod_eval (val : X -> U) x == 0].

Lemma span_ideal_submod_closed : submod_closed span_ideal.
Proof.
split=> [|a x y]; rewrite !unfold_in; first by rewrite linear0.
by rewrite linearPZ/= => /eqP -> /eqP ->; rewrite scaler0 addr0.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ span_ideal span_ideal_submod_closed.

Definition span := Quotient.zmodquot span_ideal.

End span.

Section tensor.
Variables (R : fieldType) (U V : lmodType R).

Let tensor_ideal_left_generators : set (free_lmod R (U * V)%type) :=
  [set (x.1.1 *: x.1.2 + x.2.1, x.2.2)%:lmod
   - x.1.1 *: (x.1.2, x.2.2)%:lmod - (x.2.1, x.2.2)%:lmod
  | x in @setT ((R * U) * (U * V))%type].

Let tensor_ideal_right_generators : set (free_lmod R (U * V)%type) :=
  [set (x.2.2, x.1.1 *: x.1.2 + x.2.1)%:lmod
   - x.1.1 *: (x.2.2, x.1.2)%:lmod - (x.2.2, x.2.1)%:lmod
  | x in @setT ((R * V) * (V * U))%type].

Let tensor_ideal_generators :=
  (tensor_ideal_left_generators `|` tensor_ideal_right_generators)%classic.

Definition tensor_ideal_set : set (free_lmod R (U * V)%type) :=
  smallest (fun X => submod_closed [pred x in X]) tensor_ideal_generators.
Definition tensor_ideal := [pred x in tensor_ideal_set].

Lemma tensor_ideal_submod_closed : submod_closed tensor_ideal.
Proof.
constructor; first by rewrite inE/=; move => /= A [[/[!inE]]].
move=> /= x u v /[!inE] ut vt.
move=> /= A [/[dup] Asubmod [_ /(_ x u v)] /[!inE] /[swap] inA]; apply.
  by apply: ut; split.
by apply: vt; split.
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build _ _ tensor_ideal tensor_ideal_submod_closed.

Definition tensor := Quotient.zmodquot tensor_ideal.
HB.instance Definition _ := LmodQuotient.on tensor.

End tensor.
End Tensor.
