(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences measure csum.
From HB Require Import structures.

(******************************************************************************)
(*           Scratch file for formalization of integrals (WIP)                *)
(*                                                                            *)
(* Written by the participants to the mathcomp-analysis-dev meeting circa May *)
(* 2019.                                                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "{ 'ae' P }" (at level 0, format "{ 'ae'  P }").

Notation "0" := 0%:E : ereal_scope.
Notation "1" := 1%:E : ereal_scope.

Lemma muleC (R : numDomainType) (x y : {ereal R}) : (x * y = y * x)%E.
Proof. by case: x y => [r||] [s||]//=; rewrite mulrC. Qed.

Lemma mule1 (R : numDomainType) (x : {ereal R}) : (x * 1)%E = x.
Proof. by case: x => [r||]/=; rewrite ?mulr1 ?lee_tofin ?lte_tofin. Qed.

Lemma mul1e (R : numDomainType) (x : {ereal R}) : (1 * x)%E = x.
Proof. by rewrite muleC mule1. Qed.

Lemma addeACA (R : numDomainType) : @interchange {ereal R} +%E +%E.
Proof. by case=> [r||] [s||] [t||] [u||]//=; rewrite addrACA. Qed.

Lemma abseN (R : numDomainType) (x : {ereal R}) : (`|- x| = `|x|)%E.
Proof. by case: x => [r||]; rewrite //= normrN. Qed.

Definition sigma_finite (R : realType) (T : measurableType) (X : set T)
   (mu : set T -> {ereal R}) :=
  exists2 Y : (set T)^nat,
    X = \bigcup_(i : nat) Y i &
     forall i, measurable (Y i) /\ (mu (Y i) < +oo)%E.

Definition complete_measure (R : realType) (T : measurableType)
   (mu : set T -> {ereal R}) :=
  forall X, mu.-negligible X -> measurable X.

Definition measurable_fun (T U : measurableType) (D : set T) (f : T -> U) : Prop :=
  forall Y, measurable Y -> measurable ((f @^-1` Y) `&` D).

Module Type INTEGRAL.

Section tmp.

Variable R : realType.

Parameter measurableR : set (set R).
Parameter measurableR0 : measurableR set0.
Parameter measurableRC : forall A, measurableR A -> measurableR (~` A).
Parameter measurableR_bigcup : forall U : (set R)^nat, (forall i, measurableR (U i)) ->
    measurableR (\bigcup_i (U i)).

Definition R_isMeasurable : isMeasurable R :=
  isMeasurable.Build _ measurableR0 measurableRC measurableR_bigcup.
HB.instance (Real.sort R) R_isMeasurable.

Parameter measurableErealR : set (set {ereal R}).
Parameter measurableErealR0 : measurableErealR set0.
Parameter measurableErealRC : forall A, measurableErealR A -> measurableErealR (~` A).
Parameter measurableErealR_bigcup : forall U : (set {ereal R})^nat, (forall i, measurableErealR (U i)) ->
    measurableErealR (\bigcup_i (U i)).

Definition erealR_isMeasurable : isMeasurable {ereal R} :=
  isMeasurable.Build _ measurableErealR0 measurableErealRC measurableErealR_bigcup.
HB.instance ({ereal (Real.sort R)}) erealR_isMeasurable.

Axiom measurableEreal_gee : forall x, measurable [set y : {ereal R} | x <= y]%E.
Axiom measurableEreal_lee : forall x, measurable [set y : {ereal R} | y <= x]%E.
Axiom measurableEreal_setT : measurable (setT : set {ereal R}).

Section integral.

Variable T : measurableType.

Lemma measurable_fun_ferE (D : set T) (f : T -> {ereal R}) :
  measurable_fun D f = measurable_fun setT (f \|_ D).
Proof.
Admitted.

Lemma measurable_funN (D : set T) (f : T -> {ereal R}) :
  measurable_fun D (fun x => - f x)%E = measurable_fun D f.
Proof.
Admitted.

Lemma measurable_fun_measurable (D : set T) (f : T -> {ereal R}) :
  measurable_fun D f -> measurable D.
Proof. by move=> /(_ _ measurableEreal_setT); rewrite setTI. Qed.

Lemma measurable_fun_fer (D D' : set T) (f : T -> {ereal R}) :
  measurable_fun D (f \|_ D') = measurable_fun (D `&` D') f.
Proof. by rewrite measurable_fun_ferE [RHS]measurable_fun_ferE ferK setIC. Qed.

Parameter integral : forall (m : set T -> {ereal R}) (D : set T)
  (f : T -> {ereal R}), {ereal R}.

Definition Rintegral (m : set T -> {ereal R}) (D : set T)
  (f : T -> {ereal R}) : R := real_of_er (integral m D f).

Definition integrable (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}) :=
  measurable_fun D f /\ (integral m D (fun x => `| f x |) < +oo)%E.

Lemma integrable_measurable
    (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}) :
  integrable m D f -> measurable D.
Proof. by move=> [/measurable_fun_measurable]. Qed.

Axiom integralEposneg : forall (m : set T -> {ereal R}) (D : set T)
  (f : T -> {ereal R}), integral m D f = (integral m D f^\+ - integral m D f^\-)%E.

Axiom integral1 : forall (m : set T -> {ereal R}) (D : set T),
   integral m D (fun=> 1%:E) = m D.

Axiom integral_domE : forall (m : set T -> {ereal R}) (D : set T)
    (f : T -> {ereal R}), integral m D f = integral m setT (f \|_ D).

Lemma integral_fer (m : set T -> {ereal R}) (D D' : set T)
    (f : T -> {ereal R}) : integral m D (f \|_ D') = integral m (D `&` D') f.
Proof. by rewrite integral_domE [RHS]integral_domE ferK setIC. Qed.

Axiom integral_is_linear : forall (m : set T -> {ereal R}) (D : set T)
  (k : {ereal R}) (f g : T -> {ereal R}),
  (0 <= k)%E ->
  {ae m, forall t, D t -> 0 <= f t}%E ->
  {ae m, forall t, D t -> 0 <= g t}%E ->
  measurable_fun D f -> measurable_fun D g ->
  integral m D (fun x => f x + k * g x)%E = (integral m D f + k * integral m D g)%E.

Axiom integral_ler : forall (m : set T -> {ereal R}) (D : set T)
   (f g : T -> {ereal R}),
  {ae m, forall t, D t -> 0 <= f t}%E -> {ae m, forall t, D t -> 0 <= g t}%E ->
  measurable_fun D f -> measurable_fun D g ->
  {ae m, forall x, D x -> f x <= g x}%E -> (integral m D f <= integral m D g)%E.

Lemma eq_integralr m (D : set T) (f g : T -> {ereal R}) :
   (forall x, D x -> f x = g x) ->
  integral m D f = integral m D g.
Proof.
move=> eqfg; rewrite !(integral_domE _ D); congr integral.
by apply/funext=> x; rewrite /fer; case: asboolP => // /eqfg.
Qed.

Lemma eq_integral m (D D' : set T) (f g : T -> {ereal R}) :
  D = D' ->
   (forall x, D x -> f x = g x) ->
  integral m D f = integral m D' g.
Proof. by move=> -> /eq_integralr. Qed.

Lemma integral0 (m : {measure set T -> {ereal R}}) (D : set T) :
  integral m D (fun=> 0%E) = 0%E.
Proof.
transitivity (integral m setT ((fun=> 1%:E) \|_ set0)); last first.
  by rewrite -integral_domE integral1 measure0.
rewrite integral_domE; apply/eq_integralr => x.
by rewrite /fer/= if_same; case: asboolP.
Qed.

Lemma integral_ge0 (m : {measure set T -> {ereal R}})
  (D : set T) (f : T -> {ereal R}) :
    {ae m, forall t, D t -> 0 <= f t}%E ->
    measurable_fun D f ->
  (0 <= integral m D f)%E.
Proof.
move=> f_ge0 f_meas; have D_meas := measurable_fun_measurable f_meas.
rewrite (le_trans _ (integral_ler _ f_ge0 _ f_meas f_ge0)) ?integral0//.
  exact: aeW.
move=> X X_meas /=; have [X0|XN0] := asboolP (X 0%E).
  by rewrite (_ : (fun=> _) = setT) ?setTI// predeqE.
by rewrite (_ : (fun=> _) = set0) ?set0I ?predeqE//; apply: measurable0.
Qed.

Lemma integralD (m : set T -> {ereal R}) (D : set T) (f g : T -> {ereal R})  :
  {ae m, forall t, D t -> 0 <= f t}%E ->
  {ae m, forall t, D t -> 0 <= g t}%E ->
  measurable_fun D f -> measurable_fun D g ->
  integral m D (f \+ g)%E = (integral m D f + integral m D g)%E.
Proof.
move=> f_gt0 g_gt0 f_meas g_meas; under eq_integralr do rewrite -[g _]mul1e.
by rewrite integral_is_linear// ?lee_tofin// mul1e.
Qed.

Lemma integral_disjoint_dom : forall (m : set T -> {ereal R}) (D1 D2 : set T)
    (f : T -> {ereal R}),
   measurable D1 -> measurable D2 -> m.-negligible (D1 `&` D2) ->
 integral m (D1 `|` D2) f = (integral m D1 f + integral m D2 f)%E.
Proof.
Admitted.

Lemma aeq_integral m D (f g : T -> {ereal R}) : {ae m, f =1 g} ->
  integral m D f = integral m D g.
Proof.
move=> aeqfg; gen have intE : f g aeqfg /
  integral m D f = (integral m (D `&` [set x | f x = g x]) f); last first.
  rewrite (intE _ g)// (intE _ f)//.
    apply: eq_integral => [|? []//].
    by rewrite predeqE// => x; split=> -[]; split.
  have [N [Nmeas mN0 subN]] := aeqfg; exists N; split=> //.
  by move=> x; rewrite /setC => /eqP; rewrite eq_sym => /eqP/subN.
(* rewrite -integral_fer. apply: eq_integralr => x Dx. *)
(* transitivitintegral m D fy (integral m [set x | D x /\ f x = g x] f). *)
(*  rewrite  *)
Admitted.

Lemma integrable_mesurable_pos (m : {measure set T -> {ereal R}}) (D : set T)
  (f : T -> {ereal R}) :
  integrable m D f -> measurable_fun D f^\+%E.
Proof.
move=>  [f_meas nf_int]; rewrite funeposEge0 measurable_fun_fer => X mX.
have D_meas := measurable_fun_measurable f_meas.
pose fpD := f @^-1` [set x | 0 <= x]%E `&` D; pose fXD := f @^-1` X `&` D.
rewrite (_ : _ `&` _ = fXD `&` fpD).
  by apply: measurableI; apply: f_meas => //; apply: measurableEreal_gee.
by rewrite /fpD /fXD setIACA setIid/= setIAC setIA.
Qed.

Lemma integrable_mesurable_neg (m : {measure set T -> {ereal R}}) (D : set T)
  (f : T -> {ereal R}) :
  measurable D -> integrable m D f -> measurable_fun D f^\-%E.
Proof.
move=> D_meas [f_meas nf_int]; apply: (@integrable_mesurable_pos m) => //.
by split; [rewrite measurable_funN | under eq_integralr do rewrite abseN].
Qed.

Lemma integral_funpos_ge0 (m : {measure set T -> {ereal R}}) (D : set T)
  (f : T -> {ereal R}) :
  measurable D -> integrable m D f -> (0 <= integral m D f^\+)%E.
Proof.
move=> D_meas f_int; rewrite integral_ge0//.
  by apply: aeW => *; apply: funepos_ge0.
exact: (@integrable_mesurable_pos m).
Qed.

Lemma integral_funneg_ge0 (m : {measure set T -> {ereal R}}) (D : set T)
  (f : T -> {ereal R}) :
  measurable D -> integrable m D f -> (0 <= integral m D f^\-)%E.
Proof.
move=> D_meas f_int; rewrite integral_ge0//.
  by apply: aeW => *; apply: funepos_ge0.
exact: (@integrable_mesurable_neg m).
Qed.

Variables (m : {measure set T -> {ereal R}}) (D : set T).

Lemma RintegralE (f : T -> {ereal R}) :
  measurable D -> integrable m D f ->
  (Rintegral m D f)%:E = integral m D f.
Proof.
move=> D_meas f_int; rewrite /Rintegral/= integralEposneg.
have mDfp : measurable_fun D f ^\+%E by apply: (@integrable_mesurable_pos m).
have mDfn : measurable_fun D f ^\-%E by apply: (@integrable_mesurable_neg m).
have [f_meas] := f_int; rewrite normfunEeposneg integralD//; first 1 last.
- by apply: aeW => *; apply: funepos_ge0.
- by apply: aeW => *; apply: funepos_ge0.
have: (0 <= integral m D f ^\+)%E by apply: integral_funpos_ge0.
have: (0 <= integral m D f ^\-)%E by apply: integral_funneg_ge0.
by case: (integral m D f^\+)%E (integral m D f^\-)%E => [p||] [n||].
Qed.

(* TODO: order structure about functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
in order to be able to use the notation {homo ...}
in order to rewrite the lemma integral_ler *)

(* monotone convergence theorem:
   voir necessite de la condition de positivite (wikipedia.fr),
   pas de variante pour les fonctions non-necessairement positives
   (no variant 2., see convergence dominee) *)
Axiom cvg_monotone : forall (f_ : (T -> {ereal R})^nat),
  (forall n, {ae m, forall t, D t -> 0 <= f_ n t}%E) ->
  (forall n, measurable_fun D (f_ n)) ->
  (forall x, D x -> {homo f_^~ x : m n / (m <= n)%N >-> (m <= n)%E}) ->
  let f x := lim (f_^~ x) in
  measurable_fun D f /\ integral m D f = lim (integral m D \o f_).

(* TODO: Fatou's Lemma *)

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)

Lemma integrable_is_linear  (k : R) (f g : T -> {ereal R}) :
  integrable m D f -> integrable m D g ->
  integrable m D (fun x => f x + k%:E * g x)%E.
Proof.
move=> f_int g_int.
split.
  admit.
rewrite [f]funEeposneg [g]funEeposneg.
Admitted.

Axiom Rintegral_is_linear : forall (f g : T -> {ereal R}) (k : R),
  integrable m D f -> integrable m D g ->
  Rintegral m D (fun x => f x + k%:E * g x)%E = Rintegral m D f + k * Rintegral m D g.
(*TODO: Canonical integral_linear := Linear integral_is_linear.*)

Axiom Rintegral_ler : forall (f g : T -> {ereal R}),
  integrable m D f -> integrable m D g ->
  measurable D ->
  {ae m, forall t, D t -> f t <= g t}%E -> Rintegral m D f <= Rintegral m D g.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : (T -> {ereal R})^nat) (f g : T -> {ereal R}),
  (forall n, integrable m D (f_ n)) ->
  integrable m D g ->
  (forall n, {ae m, forall t, `| f_ n t | <= g t}%E) ->
  {ae m, forall t, f_ n t @[n --> \oo]--> f t} ->
  (Rintegral m D \o f_) @ \oo --> (Rintegral m D f : R^o).

End integral.

Axiom mprodType_is_measurable : forall (X Y : measurableType)
  (mx : set X -> {ereal R}) (my : set Y -> {ereal R}), isMeasurable (X * Y)%type.

Definition mprodType (X Y : measurableType)
  (mx : set X -> {ereal R}) (my : set Y -> {ereal R}) := (X * Y)%type.

Axiom product_measure : forall (X Y : measurableType)
  (mx : set X -> {ereal R}) (my : set Y -> {ereal R}), set (mprodType mx my) -> {ereal R}.
Arguments product_measure {X Y} _ _.

Section prod_measurable.
Variables X Y : measurableType.
Variables (mx : set X -> {ereal R}) (my : set Y -> {ereal R}).

HB.instance (mprodType mx my) (mprodType_is_measurable mx my).

End prod_measurable.
(*Canonical product_measurableType X Y := Measurable.Pack (product_measurableType_sigma_algebra X Y).*)

Section fubini.

Variables (X Y : measurableType).
Variables (mx : set X -> {ereal R}) (my : set Y -> {ereal R}).
Notation m := (product_measure mx my).
Variable f : mprodType mx my -> {ereal R}.
Variable DX : set X.
Variable DY : set Y.
Let D : set (mprodType mx my) := DX `*` DY.

Axiom product_measure_is_measure : is_measure m.
Canonical product_measure_measure := Measure product_measure_is_measure.

(* see faraut p.61 *)
Axiom fubini_tonelli : sigma_finite DX mx -> sigma_finite DY my ->
  {ae m, (forall x, D x -> 0 <= f x)%E} ->
  measurable_fun D f ->
  let F : X -> {ereal R} := fun x => integral my DY (fun y => f (x, y)) in
  measurable_fun DX F /\
  integral m D f = integral mx DX F.

Axiom fubini_lebesgue : complete_measure mx -> complete_measure my ->
  integrable m D f ->
  let F : X -> {ereal R} := fun x => integral my DY (fun y => f (x, y)) in
  integrable mx DX F /\ Rintegral m D f = Rintegral mx DX F.

End fubini.

End tmp.

End INTEGRAL.
