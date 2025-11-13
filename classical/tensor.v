From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg vector ring_quotient finmap boolp.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

(** Free module *)

Section FreeLmod.
Variables (R : pzRingType) (T : choiceType).

Definition free_lmod := {fsfun T -> R with 0}.

HB.instance Definition _ := Choice.on free_lmod.

Fact free_lmod_key : unit. Proof. exact: tt. Qed.

Let zero : free_lmod := fsfun_of_fun free_lmod_key fset0 (fun=> 0) (fun=> 0).

Let zeroE x : zero x = 0.
Proof. by rewrite fsfunE in_fset0. Qed.

Let opp (f : free_lmod) := fsfun_of_fun free_lmod_key (finsupp f) (GRing.opp \o f) (fun=> 0).

Let oppE (f : free_lmod) x : opp f x = - (f x).
Proof.
rewrite fsfunE mem_finsupp; case: ifPn => //; rewrite negbK => /eqP ->.
by rewrite oppr0.
Qed.

Let add (f g : free_lmod) := fsfun_of_fun free_lmod_key (finsupp f `|` finsupp g)%fset (f \+ g) (fun=> 0).

Let addE (f g : free_lmod) x : add f g x = f x + g x.
Proof.
rewrite fsfunE in_fsetU !mem_finsupp.
case: ifPn => //; rewrite negb_or !negbK => /andP[] /eqP -> /eqP ->.
by rewrite addr0.
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

Let scale (a : R) (f : free_lmod) : free_lmod :=
  fsfun_of_fun free_lmod_key (finsupp f)%fset (fun x => a * f x) (fun=> 0).

Let scaleE a f x : scale a f x = a * f x.
Proof.
rewrite fsfunE mem_finsupp.
by case: ifPn => //; rewrite negbK => /eqP ->; rewrite mulr0.
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

Lemma free_lmodZE a (f : free_lmod) : a *: f = (fun x => a * f x) :> (_ -> _).
Proof. exact/funext/scaleE. Qed.

End FreeLmod.

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

Notation quot := (quot Pzmod).

Definition scale a := lift_op1 quot ( *:%R a).

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
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R quot scalerA scale1r scalerDr scalerDl.
#[export]
HB.instance Definition _ :=
  ZmodQuotient_isLmodQuotient.Build R L (equiv Pzmod) 0 -%R +%R *:%R quot pi_scale.

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

Definition fintensor_proj (x : U * V) : fintensor :=
  fsfun_of_fun free_lmod_key (unpickle setT) (fun i => coord bU i.1 x.1 * coord bV i.2 x.2) (fun=> 0).

End fintensor.

Section span.
Variables (R : fieldType) (U : lmodType R) (X : {fset U}).

Definition of_span_subdef (x : free_lmod R X) :=
  \sum_(i <- finsupp x) x i *: val i.

Lemma of_span_subdef_linear : linear of_span_subdef.
Proof.
move=> a x y; rewrite /of_span_subdef scaler_sumr.
rewrite (big_fset_incl _ (fsubsetUr (finsupp x `|` finsupp y)%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r.
apply: esym; rewrite (big_fset_incl _ (fsubsetUr (finsupp (a *: x + y)%R `|` (finsupp y))%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r scaler0.
rewrite [X in _ + X](big_fset_incl _ (fsubsetUr (finsupp (a *: x + y)%R `|` (finsupp x))%fset _))/=; last first.
  by move=> i _; rewrite mem_finsupp negbK => /eqP ->; rewrite scale0r.
rewrite fsetUAC -big_split/= -fsetUA fsetUC.
by apply: eq_bigr => i _; rewrite free_lmodDE/= scalerDl free_lmodZE scalerA.
Qed.

HB.instance Definition _ := GRing.isLinear.Build _ _ _ _ of_span_subdef of_span_subdef_linear.

Definition spanI0 (x : free_lmod R X) := of_span_subdef x == 0.

Lemma spanI0_submod_closed : submod_closed spanI0.
Proof.
split=> [|a x y]; rewrite !unfold_in; first by rewrite linear0.
by rewrite linearPZ/= => /eqP -> /eqP ->; rewrite scaler0 addr0.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ spanI0 spanI0_submod_closed.

(* TODO: Why does the reverse coercion fail to apply? *)
Definition span := Quotient.quot Tensor_spanI0__canonical__GRing_SubmodClosed.

Check span : zmodType .

End span.

Section tensor.
Variables (R : fieldType) (U V : lmodType R).

Definition equiv (x y : free_lmod R (U * V)%type) := true.
End tensor.
End Tensor.
