From HB Require Import structures.
From elpi Require Import elpi.
From mathcomp Require Import all_ssreflect ssralg vector ring_quotient.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import finmap boolp functions classical_sets.

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
Local Notation "x %:lmod" := (free_lmod_unit x).

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
Notation "x %:lmod" := (free_lmod_unit x).

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
Arguments free_lmod R T%_type : clear implicits.
Notation "x %:lmod" := (free_lmod_unit x).

Lemma finsupp_free_lmod_unit {R : nzRingType} {T : choiceType} (t : T) :
  finsupp (t%:lmod : free_lmod R T) = [fset t].
Proof.
apply/fsetP=> i; rewrite inE mem_finsupp free_lmod_unitE.
by case: (eqVneq i t); rewrite ?eqxx// oner_eq0.
Qed.

Lemma free_lmod_eval_unit {R : nzRingType} {T : choiceType}
  {U : lmodType R} (f : T -> U) (t : T) : free_lmod_eval f t%:lmod = f t.
Proof.
rewrite [free_lmod_eval _]unlock finsupp_free_lmod_unit.
by rewrite big_seq_fset1 free_lmod_unitE eqxx scale1r.
Qed.

Section general_kernel.
Context {R : nzRingType} {U V : lmodType R}.
Definition ker_set  (f : U -> V) : set U :=
  [set u | f u = 0].

Lemma ker_submod_closed (f : {linear U -> V}) : submod_closed [pred x in ker_set f].
Proof.
split => [|x u v] /[!inE]; rewrite /ker_set/=; first exact: linear0.
by move=> + + /[!linearP] => -> ->; rewrite scaler0 addr0.
Qed.

End general_kernel.

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
rewrite (@big_fset_incl _ _ _ _ _ [fset f x | x in finsupp u])/=; first last.
- move=> _ /imfsetP[] x/= xu ->; rewrite mem_finsupp negbK => /eqP ->.
  exact: scale0r.
- apply/fsubsetP => y; rewrite mem_finsupp => /eqP; apply: contra_notT => yf.
  rewrite free_lmod_sumE big_seq; apply: big1 => x xu.
  rewrite free_lmodZE/= free_lmod_unitE.
  case: eqP => yE; last by rewrite mulr0.
  by elim: (negP yf); apply/imfsetP; exists x.
rewrite (partition_big_imfset _ f)/=; apply: eq_bigr => y _.
rewrite big_mkcond/= free_lmod_sumE scaler_suml; apply: eq_bigr => x _.
rewrite free_lmodZE free_lmod_unitE.
case: eqP => [<-|]; first by rewrite mulr1.
by rewrite mulr0 scale0r.
Qed.

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
Section fiptensor.
Variables (R : fieldType) (U V : vectType R).

Let nU := \dim (@fullv _ U).
Let nV := \dim (@fullv _ V).
Let bU := vbasis (@fullv _ U).
Let bV := vbasis (@fullv _ V).

Definition fiptensor := free_lmod R ('I_nU * 'I_nV).

Elpi lock Definition fiptensor_proj (x : U * V) : fiptensor :=
  [fsfun i in [fset i in 'I_nU] `*` [fset i in 'I_nV]
   => coord bU i.1 x.1 * coord bV i.2 x.2].

End fiptensor.

Section span.
Variables (R : comRingType) (U : lmodType R) (X : {fset U}).

Definition span_ideal : {pred free_lmod R X} :=
  [pred x in ker_set (free_lmod_eval (val : X -> U))].

Lemma span_ideal_submod_closed : submod_closed span_ideal.
Proof. exact: ker_submod_closed. Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build _ _ span_ideal span_ideal_submod_closed.

Definition span := Quotient.zmodquot span_ideal.

End span.
End Tensor.

Section Biptensor.
Variables (R : comRingType) (U V : lmodType R).

Let tensor_ideal_left_generators : set (free_lmod R (U * V)) :=
  [set (x.1.1 *: x.1.2 + x.2.1, x.2.2)%:lmod
   - (x.1.1 *: (x.1.2, x.2.2)%:lmod + (x.2.1, x.2.2)%:lmod)
  | x in @setT ((R * U) * (U * V))%type].

Let tensor_ideal_right_generators : set (free_lmod R (U * V)) :=
  [set (x.2.2, x.1.1 *: x.1.2 + x.2.1)%:lmod
   - (x.1.1 *: (x.2.2, x.1.2)%:lmod + (x.2.2, x.2.1)%:lmod)
  | x in @setT ((R * V) * (V * U))%type].

Let tensor_ideal_generators :=
  (tensor_ideal_left_generators `|` tensor_ideal_right_generators)%classic.

Definition tensor_ideal_set : set (free_lmod R _) :=
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

Definition to_tensor (u : U) (v : V) := \pi_tensor ((u, v)%:lmod).
Notation "u *t v" := (to_tensor u v) (at level 40) : ring_scope.

Variable (W : lmodType R).

Definition tensor_umap (f : U -> V -> W) (t : tensor) : W :=
  free_lmod_eval (uncurry f) (repr t).

Lemma eq_free_lmod_eval (f : {bilinear U -> V -> W}) (a b : free_lmod R (U * V)) :
  a = b %[mod tensor] -> free_lmod_eval (uncurry f) a = free_lmod_eval (uncurry f) b.
Proof.
move=> /eqquotP; rewrite Quotient.equivE !inE /= => ab0.
(* rewrite [free_lmod_eval _]unlock. *)
apply/eqP; rewrite -subr_eq0 -raddfB/=; apply/eqP.
suff: ker_set (free_lmod_eval (uncurry f)) (a - b) by [].
apply: ab0; split; first exact: ker_submod_closed.
by move=> g [[x _ <-]|[x _ <-]]; rewrite /ker_set/= !(linearZ, linearB, linearD)/=;
   rewrite !free_lmod_eval_unit/= ?linearPr ?linearPl ?scalerN;
   rewrite addrACA !subrr addr0.
Qed.

Lemma tensor_umap_is_linear (f : {bilinear U -> V -> W}) : linear (tensor_umap f).
Proof.
move=> x t1 t2; rewrite /tensor_umap/=.
have: repr (x *: t1 + t2) = x *: repr t1 + repr t2 %[mod tensor].
   by rewrite linearP/= !reprK.
move=> /eq_free_lmod_eval ->.
rewrite [free_lmod_eval _]unlock.
set A := finsupp _; set B := finsupp _; set C := finsupp _.
rewrite (big_fset_incl _ (fsubsetUl _ (B `|` C)%fset))/=; last first.
  by move=> uv _ /fsfun_dflt->; rewrite scale0r.
rewrite [in RHS](big_fset_incl _ (fsubsetUl _ (A `|` C)%fset))/=; last first.
  by move=> uv _ /fsfun_dflt->; rewrite scale0r.
rewrite [in X in _ = _ + X](big_fset_incl _ (fsubsetUr (A `|` B)%fset _))/=; last first.
  by move=> uv _ /fsfun_dflt->; rewrite scale0r.
rewrite [in RHS]fsetUCA !fsetUA.
rewrite scaler_sumr -big_split/=; apply/eq_bigr => -[u v] _ /=.
rewrite scalerA -scalerDl; apply/eqP; rewrite -subr_eq0 -scalerBl.
by rewrite free_lmodDE/= free_lmodZE/= subrr scale0r.
Qed.
HB.instance Definition _ (f : {bilinear U -> V -> W}) :=
  GRing.isLinear.Build _ _ _ _ (tensor_umap f) (tensor_umap_is_linear f).

Definition tensor_universal_mapP (f : {bilinear U -> V -> W}) (u : U) (v : V) :
  tensor_umap f (u *t v) = f u v.
Proof.
rewrite /tensor_umap /to_tensor.
have : repr (\pi_tensor (u, v)%:lmod) = (u, v)%:lmod %[mod tensor].
  by rewrite reprK.
move=> /eq_free_lmod_eval->.
rewrite [free_lmod_eval _]unlock/= finsupp_free_lmod_unit.
by rewrite big_seq_fset1 free_lmod_unitE eqxx scale1r.
Qed.

End Biptensor.

Section ProdTensor.
Variables (R : fieldType) (I : eqType) (U_ : I -> lmodType R).

Let ptensor_ideal_generators : set (free_lmod R (forall i, U_ i)) :=
  [set
     (fun i => (if tag (x.1.1) =P i is ReflectT xi then x.1.2 *: etagged xi else 0) + x.2 i)%:lmod
     - (x.1.2 *: (fun i => if tag (x.1.1) =P i is ReflectT xi then etagged xi else x.2 i)%:lmod + x.2%:lmod)
  | x in @setT (({i : I & U_ i} * R) * (forall i, U_ i))%type].

Definition ptensor_ideal_set : set (free_lmod R _) :=
  smallest (fun X => submod_closed [pred x in X]) ptensor_ideal_generators.
Definition ptensor_ideal : {pred _} := [pred x in ptensor_ideal_set].

Lemma ptensor_ideal_submod_closed : submod_closed ptensor_ideal.
Proof.
constructor; first by rewrite inE/=; move => /= A [[/[!inE]]].
move=> /= x u v /[!inE] ut vt.
move=> /= A [/[dup] Asubmod [_ /(_ x u v)] /[!inE] /[swap] inA]; apply.
  by apply: ut; split.
by apply: vt; split.
Qed.

HB.instance Definition _ :=
  GRing.isSubmodClosed.Build _ _ ptensor_ideal ptensor_ideal_submod_closed.

Definition ptensor := Quotient.zmodquot ptensor_ideal.
HB.instance Definition _ := LmodQuotient.on ptensor.

Definition to_ptensor (u_ : forall i, U_ i) := \pi_ptensor (u_%:lmod).
Notation "u %:tensor" := (to_ptensor u) : ring_scope.

End ProdTensor.
