From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.

Local Open Scope classical_set_scope.

(* TODO: generalize to Proset when available in MathComp *)
Definition isDirected d (T : porderType d) (A : set T) :=
  forall x y, A x -> A y ->
    exists z, [/\ A z, (x <= z)%O & (y <= z)%O].

Lemma isDirected2 d (T : porderType d) (x y : T) :
  (x <= y)%O -> isDirected [set x; y].
Proof. by move=> xy _ _ /= [|]-> [|] ->; exists y; split => //; right. Qed.

Lemma isLub2 d (T : porderType d) (x y : T) :
  (x <= y)%O -> isLub [set x; y] y.
Proof. by move=> xy; split => [_/= [|] ->//|z]; apply; right. Qed.

Lemma directed_map d d' (T : porderType d) (T' : porderType d') (f : T -> T') (A : set T) :
  {homo f : x y / (x <= y)%O} -> isDirected A -> isDirected (f @` A).
Proof.
move=> ndf dirA _ _ /= [x1 A1 <-] [x2 A2 <-].
have [z [Az x1z x2z]] := dirA _ _ A1 A2.
by exists (f z); split; [exists z| apply: ndf..].
Qed.

HB.mixin Record POrder_isDCPO d T of Order.POrder d T := {
  hasLub : forall A : set T, A !=set0 -> isDirected A -> exists x, isLub A x
}.

#[short(type="DCPOType")]
HB.structure Definition DCPO d := {T of Order.POrder d T & POrder_isDCPO d T}.

#[short(type="CPOType")]
HB.structure Definition CPO d := {T of DCPO d T & Order.hasBottom d T}.

Definition net d (T : porderType d)
    (A : set T) (dA : isDirected A) X :=
  A -> X.

(* TODO: generalize to Proset when available in MathComp *)
Definition order_compact d (T : porderType d) : set T :=
  [set x | forall (A : set T) z, isDirected A -> isLub A z ->
    (x <= z)%O -> exists2 y, A y & (x <= y)%O].

Definition compact_upto d (T : porderType d) (x : T) :=
  [set y | order_compact y /\ (y <= x)%O].

(* TODO: generalize to Proset when available in MathComp *)
HB.mixin Record isAlgebraic d T of DCPO d T := {
  algebraic : forall x : T,
    isDirected (compact_upto x) /\
    isLub (compact_upto x) x
}.

Definition isUpperSet d (T : porderType d) (A : set T) :=
  forall x y, (x <= y)%O -> A x -> A y.

Lemma isUpperSetI d (T : porderType d) (A B : set T) :
 isUpperSet A -> isUpperSet B -> isUpperSet (A `&` B).
Proof.
by move=> hA hB x y xy [] /hA => /(_ _ xy) Ay /hB => /(_ _ xy) By.
Qed.

Definition scott_open d (T : porderType d) (A : set T) :=
  isUpperSet A /\
  forall (B : set T) (x : T), isDirected B -> B !=set0 ->
    isLub B x -> A x -> B `&` A !=set0.

From mathcomp Require Import topology.

Definition scott_topo d (T : porderType d) : Type := T.

HB.instance Definition _ d (T : porderType d) :=
  Equality.on (scott_topo T).
HB.instance Definition _ d (T : porderType d) :=
  Choice.on (scott_topo T).

Section scott_topology.
Context d (T' : porderType d).

Notation T := (@scott_topo _ T').

Let o : set (set T) := @scott_open _ T.

Let oT : o [set: T].
Proof. by split => // B x dB B0 _ _; rewrite setIT. Qed.

Let oI (A B : set T) : o A -> o B -> o (A `&` B).
Proof.
move=> [A1 A2] [B1 B2]; split; first exact: isUpperSetI.
move=> C x uC C0 Cx [Ax Bx].
have [x0 [Cx0 Ax0]] := A2 _ _ uC C0 Cx Ax.
have [x1 [Cx1 Bx1]] := B2 _ _ uC C0 Cx Bx.
have [x2 [Xc2 x0x2 x1x2]] := uC _ _ Cx0 Cx1.
by exists x2; split => //; split; [exact: (A1 _ _ x0x2)|exact: (B1 _ _ x1x2)].
Qed.

Let oU (I : Type) (f : I -> set T) : (forall i, o (f i)) ->
  o (\bigcup_i f i).
Proof.
move=> fo; split=> [x y xy [i _ fxi]|].
  exists i => //; have [{}fo _] := fo i.
  exact: (fo _ _ xy).
move=> B x isB B0 Bx [i _ fxi].
have [fo1 fo2] := fo i.
have [y [By fyi]] := fo2 _ _ isB B0 Bx fxi.
by exists y => //; split => //; exists i.
Qed.

HB.instance Definition _ := @isOpenTopological.Build
  (scott_topo T') o oT oI oU.

End scott_topology.

From mathcomp Require Import separation_axioms.

(* TODO: generalize to Proset when available in MathComp *)
Definition scott_continuous d (T : porderType d) d' (T' : porderType d')
    (f : T -> T') := forall (A : set T) x, A !=set0 -> isDirected A -> isLub A x ->
  isLub (f @` A) (f x).

Lemma scott_continuous_monotonic d (T : porderType d) (f : T -> T) :
  scott_continuous f -> {homo f : x y / (x <= y)%O}.
Proof.
move=> + x y xy.
have xy0 : [set x; y] !=set0 by exists x; left.
move => /(_ _ _ xy0 (isDirected2 xy)) => /(_ _ (isLub2 xy))[+ _].
by apply => /=; exists x => //; left.
Qed.

(* NB: we only need a preorder in fact *)
Definition specialization_order (T : topologicalType) : rel T :=
  fun x y => `[< forall O, open O -> O x -> O y >].
Arguments specialization_order : clear implicits.

Lemma specialization_order_refl T : reflexive (specialization_order T).
Proof. by move=> x; apply/asboolP. Qed.

Lemma specialization_order_trans T : transitive (specialization_order T).
Proof.
by move=> x y z /asboolP xy /asboolP yz; apply/asboolP => O oO /xy /yz; exact.
Qed.

Lemma specialization_order_anti T :
  kolmogorov_space T -> antisymmetric (specialization_order T).
Proof.
move=> T0 x y /andP[/asboolP xy /asboolP yx].
apply/eqP/negPn/negP => /T0[A] [].
  rewrite inE/= => -[xA].
  rewrite inE; apply.
  move: xA.
  rewrite nbhsE => /= -[O [oO Ox]].
  apply.
  by apply: xy.
rewrite inE/= => -[xA].
rewrite inE; apply.
move: xA.
rewrite nbhsE => /= -[O [oO Ox]].
apply.
by apply: yx.
Qed.

Lemma notLe_scott_open d (T : porderType d) x :
  (@open (scott_topo T)) [set z | ~ (z <= x)%O].
Proof.
split.
- move=> a b ab /=.
  apply: contra_not.
  exact: le_trans.
- move=> S y dirS S0 Hlub /= yx.
  apply/set0P/eqP.
  apply: contra_not yx => SI0.
  have : ubound S x.
    move=> z Sz.
    apply: contrapT => zy.
    by move: SI0; apply/eqP/set0P; exists z.
  by case: Hlub => _ /[apply].
Qed.

Lemma scott_specialization d (T : porderType d) x y :
  specialization_order (scott_topo T) x y <-> (x <= y)%O.
Proof.
split; last first.
  move=> xy.
  by apply/asboolP => O [upO _] Ox; apply: (upO _ _ xy).
move=> /asboolP xy.
apply: contrapT => yx.
have : [set z | ~ (z <= y)%O ] x by [].
by move/xy => /(_ (notLe_scott_open _)) /=; exact.
Qed.

Lemma scott_monotonic d (T : porderType d) d' (T' : porderType d')
  (f : scott_topo T -> scott_topo T') : continuous f -> {homo f : x y / (x <= y)%O}.
Proof.
move=> cf x y xy.
rewrite -scott_specialization.
apply/asboolP => O.
move/continuousP : cf => /[apply] -[+ _].
exact.
Qed.

Definition dlub d (T : DCPOType d) (A : set T) (A0 : A !=set0) (dirA : isDirected A) : T :=
  sval (cid (hasLub A A0 dirA)).

Lemma dlub_isLub d (T : DCPOType d) (A : set T) (A0 : A !=set0) (dirA : isDirected A) :
  isLub A (dlub A0 dirA).
Proof. by rewrite /dlub; case: cid => //. Qed.

Lemma le_dlub d (T : DCPOType d) (A : set T) (A0 : A !=set0) (dirA : isDirected A) x :
  A x -> (x <= dlub A0 dirA)%O.
Proof.
move=> Ax.
by apply (dlub_isLub A0 dirA).
Qed.

Lemma dlub_le d (T : DCPOType d) (A : set T) (A0 : A !=set0) (dirA : isDirected A) x :
  ubound A x -> (dlub A0 dirA <= x)%O.
Proof.
move=> Ax.
by apply (dlub_isLub A0 dirA).
Qed.

Lemma isLub_dlub d (T : DCPOType d) (A : set T) (A0 : A !=set0) (dirA : isDirected A) x :
  isLub A x <-> dlub A0 dirA = x.
Proof.
rewrite /dlub; case: cid => /= t [At /= tA].
split => [[Ax /= xA]|<-//].
by apply/eqP; rewrite eq_le tA// xA.
Qed.

Section scott_continuous1.
Context d (T : porderType d).
Let ST : topologicalType := (@scott_topo _ T).

Lemma scott_continuousP1 (f : ST -> ST) :
  scott_continuous f -> continuous f.
Proof.
move=> cf.
apply/continuousP => A oA.
case: oA => Hup Hopen.
have H := scott_continuous_monotonic cf.
split=> [x y xy fAx|].
  by apply: (Hup (f x)) => //; exact: H.
move=> S' x dirS' S'0 hmember.
have := cf _ _ S'0 dirS' hmember.
move=> /(Hopen _ _ (directed_map H dirS')).
have : [set f x | x in S'] !=set0.
  case: S'0 => y S'y.
  by exists (f y) => /=; exists y.
move=> /[swap] /[apply].
move=> /[apply] [[z /= [[t S't] Az]]].
by exists t => //; split => //=; rewrite Az.
Qed.

End scott_continuous1.

Section scott_continuous2.
Context d (T : DCPOType d).
Let ST : topologicalType := (@scott_topo _ T).

Lemma scott_continuousP2 (f : ST -> ST) :
  continuous f -> scott_continuous f.
Proof.
move=> Hcont S x S0 dirS Hlub.
move/scott_monotonic : (Hcont) => homof.
pose dirfS := directed_map homof dirS.
have f0 : [set f x | x in S] !=set0.
  case: S0 => y ?.
  by exists (f y); exists y.
apply/(isLub_dlub f0).
move/isLub_dlub : (Hlub) => /(_ S0 dirS) ?; subst x.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: dlub_le => _ /= [x Sx <-].
  rewrite homof//.
  exact: le_dlub.
- apply: contrapT => Hnle.
  have {}Hnle : ~ (f (dlub S0 dirS) <= dlub f0 (directed_map homof dirS))%O.
    by [].
  have : @open (scott_topo T) (f @^-1` [set z | ~ (z <= dlub f0 (directed_map homof dirS))%O]).
    move/continuousP : Hcont; apply.
    exact: notLe_scott_open.
  case=> _ Hopen.
  have {Hopen}[z [Sz Hz]] := Hopen _ _ dirS S0 (dlub_isLub _ _) Hnle.
  apply: Hz.
  apply: le_dlub.
  by exists z.
Qed.

End scott_continuous2.

Section scott_T0.
Context d (T : DCPOType d).
Let ST : topologicalType := (@scott_topo _ T).

Lemma scott_topo_is_T0 : kolmogorov_space ST.
Proof.
move=> x y xy.
Abort.

End scott_T0.

(*
xxx

#[short(type="ACPOType")]
HB.structure Definition ACPO d := {T of DCPO d T & Order.hasBottom d T}.
*)
