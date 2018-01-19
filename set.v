From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg matrix.
From SsrReals Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Proof. by move=> x y; apply: (iffP (asboolP _)). Qed.
Definition gen_eqMixin {T : Type} := EqMixin (@gen_eqP T).

Axiom gen_choiceMixin : forall {T : Type}, Choice.mixin_of T.

Definition dep_arrow_eqType (T : Type) (T' : T -> eqType) :=
  EqType (forall x : T, T' x) gen_eqMixin.
Canonical arrow_eqType (T : Type) (T' : eqType) :=
  EqType (T -> T') gen_eqMixin.
Canonical arrow_choiceType (T : Type) (T' : choiceType) :=
  ChoiceType (T -> T') gen_choiceMixin.

Canonical Prop_eqType := EqType Prop gen_eqMixin.
Canonical Prop_choiceType := ChoiceType Prop gen_choiceMixin.

Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).

Definition set A := A -> Prop.
Definition in_set T (P : set T) : pred T := [pred x | `[<P x>]].
Canonical set_predType T := @mkPredType T (set T) (@in_set T).

Lemma in_setE T (P : set T) x : x \in P = P x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.

Notation "[ 'set' x : T | P ]" := ((fun x => P) : set T)
  (at level 0, x at level 99, only parsing) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : classical_set_scope.

Notation "[ 'set' E | x 'in' A ]" := [set y | exists2 x, A x & E = y]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'") : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" := [set z | exists2 x, A x & exists2 y, B y & E = z]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'") : classical_set_scope.

Definition image {A B} (f : A -> B) (X : set A) : set B :=
  [set f a | a in X].

Definition preimage {A B} (f : A -> B) (X : set B) : set A := [set a | X (f a)].
Arguments preimage A B f X / a.

Definition setT {A} := [set _ : A | True].
Definition set0 {A} := [set _ : A | False].
Definition set1 {A} (x : A) := [set a : A | a = x].
Definition setI {A} (X Y : set A) := [set a | X a /\ Y a].
Definition setU {A} (X Y : set A) := [set a | X a \/ Y a].
Definition nonempty {A} (X : set A) := exists x, X x.
Definition setC {A} (X : set A) := [set a | ~ X a].
Definition setD {A} (X Y : set A) := [set a | X a /\ ~ Y a].
Definition setM {A B} (X : set A) (Y : set B) := [set x | X x.1 /\ Y x.2].
Definition fst_set {A B} (X : set (A * B)) := [set x | exists y, X (x, y)].
Definition snd_set {A B} (X : set (A * B)) := [set y | exists x, X (x, y)].

Notation "[ 'set' 'of' F ]" := [set F i | i in setT]
  (at level 0,
   format "[ 'set'  'of'  F ]") : classical_set_scope.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |` [set a2]) .. [set an])
  (at level 0, a1 at level 99,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A)
  (at level 2, left associativity, format "A .`1") : classical_set_scope.
Notation "A .`2" := (snd_set A)
  (at level 2, left associativity, format "A .`2") : classical_set_scope.
Notation "~` A" := (setC A) (at level 35, right associativity) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a])
  (at level 0, format "[ 'set' ~  a ]") : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.

Definition bigsetI A I (P : set I) (X : I -> set A) :=
  [set a | forall i, P i -> X i a].
Definition bigsetU A I (P : set I) (X : I -> set A) :=
  [set a | exists2 i, P i & X i a].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigsetU P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ i F" :=
  (\bigcup_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'")
 : classical_set_scope.

Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigsetI P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ i F" :=
  (\bigcap_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'")
 : classical_set_scope.

Definition subset {A} (X Y : set A) := forall a, X a -> Y a.

Notation "A `<=` B" := (subset A B) (at level 70, no associativity)
 : classical_set_scope.
Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) (at level 70, no associativity)
 : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) (at level 24) : classical_set_scope.
Notation "f @` A" := (image f A) (at level 24) : classical_set_scope.
Notation "A !=set0" := (nonempty A) (at level 80) : classical_set_scope.

Lemma eqEsubset T (F G : set T) : F `<=` G -> G `<=` F -> F = G.
Proof. by move=> H K; rewrite funeqE=> s; rewrite propeqE; split=> [/H|/K]. Qed.

Lemma imageP {A B} (f : A -> B) (X : set A) a : X a -> (f @` X) (f a).
Proof. by exists a. Qed.

Lemma sub_image_setI {A B} (f : A -> B) (X Y : set A) :
  f @` (X `&` Y) `<=` f @` X `&` f @` Y.
Proof. by move=> b [x [Xa Ya <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {A B f X Y} a _.

Lemma nonempty_image {A B} (f : A -> B) (X : set A) :
  f @` X !=set0 -> X !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma nonempty_preimage {A B} (f : A -> B) (X : set B) :
  f @^-1` X !=set0 -> X !=set0.
Proof. by case=> [a ?]; exists (f a). Qed.

Lemma preimage_image A B (f : A -> B) (X : set A) : X `<=` f@^-1` (f @` X).
Proof. by move=> a Xa; exists a. Qed.

Lemma image_preimage A B (f : A -> B) (X : set B) :
  f @` setT = setT -> f @` (f @^-1` X) = X.
Proof.
move=> fsurj; rewrite predeqE => x; split; first by move=> [?? <-].
move=> Xx; have : setT x by [].
by rewrite -fsurj => - [y _ fy_eqx]; exists y => //; rewrite /preimage fy_eqx.
Qed.

Lemma preimage_setC A B (f : A -> B) (X : set B) :
  ~` (f @^-1` X) = f @^-1` (~` X).
Proof. by rewrite predeqE => a; split=> nXfa ?; apply: nXfa. Qed.

Lemma subset_empty {A} (X Y : set A) : X `<=` Y -> X !=set0 -> Y !=set0.
Proof. by move=> sXY [x Xx]; exists x; apply: sXY. Qed.

Lemma subset_trans {A} (Y X Z : set A) : X `<=` Y -> Y `<=` Z -> X `<=` Z.
Proof. by move=> sXY sYZ ? ?; apply/sYZ/sXY. Qed.

Lemma nonempty_preimage_setI {A B} (f : A -> B) (X Y : set B) :
  (f @^-1` (X `&` Y)) !=set0 <-> (f @^-1` X `&` f @^-1` Y) !=set0.
Proof. by split; case=> x ?; exists x. Qed.

Lemma subsetC {A} (X Y : set A) : X `<=` Y -> ~` Y `<=` ~` X.
Proof. by move=> sXY ? nYa ?; apply/nYa/sXY. Qed.

Lemma subsetU {A} (X Y Z : set A) : X `<=` Z -> Y `<=` Z -> X `|` Y `<=` Z.
Proof. by move=> sXZ sYZ a; apply: or_ind; [apply: sXZ|apply: sYZ]. Qed.

Lemma setDE {A} (X Y : set A) : X `\` Y = X `&` ~` Y.
Proof. by []. Qed.

Lemma setIid {A} (X : set A) : X `&` X = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIC {A} (X Y : set A) : X `&` Y = Y `&` X.
Proof. by rewrite predeqE => ?; split=> [[]|[]]. Qed.

Lemma setIT {A} (X : set A) : X `&` setT = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIA {A} (X Y Z : set A) : X `&` (Y `&` Z) = X `&` Y `&` Z.
Proof. by rewrite predeqE => ?; split=> [[? []]|[[]]]. Qed.

Lemma setICA {A} (X Y Z : set A) : X `&` (Y `&` Z) = Y `&` (X `&` Z).
Proof. by rewrite setIA [X `&` _]setIC -setIA. Qed.

Lemma setIAC {A} (X Y Z : set A) : X `&` Y `&` Z = X `&` Z `&` Y.
Proof. by rewrite setIC setICA setIA. Qed.

Lemma setIACA {A} (X Y Z T : set A) :
  X `&` Y `&` (Z `&` T) = X `&` Z `&` (Y `&` T).
Proof. by rewrite -setIA [Y `&` _]setICA setIA. Qed.

Definition is_prop {A} (X : set A) := forall x y, X x -> X y -> x = y.
Definition is_fun {A B} (f : A -> B -> Prop) := all (is_prop \o f).
Definition is_total {A B} (f : A -> B -> Prop) := all (nonempty \o f).
Definition is_totalfun {A B} (f : A -> B -> Prop) :=
  forall x, nonempty (f x) /\ is_prop (f x).

Definition xget {T : choiceType} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).

CoInductive xget_spec {T : choiceType} x0 (P : set T) : T -> Prop -> Type :=
| XGetSome x of x = xget x0 P & P x : xget_spec x0 P x True
| XGetNone of (forall x, ~ P x) : xget_spec x0 P x0 False.

Lemma xgetP {T : choiceType} x0 (P : set T) : xget_spec x0 P (xget x0 P) (P (xget x0 P)).
Proof.
move: (erefl (xget x0 P)); set y := {2}(xget x0 P).
rewrite /xget; case: pselect => /= [?|neqP _].
  by case: sigW => x /= /asboolP Px; rewrite [P x]propT //; constructor.
suff NP x : ~ P x by rewrite [P x0]propF //; constructor.
by apply: contrap neqP => Px; exists x; apply/asboolP.
Qed.

Lemma xgetPex {T : choiceType} x0 (P : set T) : (exists x, P x) -> P (xget x0 P).
Proof. by case: xgetP=> // NP [x /NP]. Qed.

Lemma xgetI {T : choiceType} x0 (P : set T) (x : T): P x -> P (xget x0 P).
Proof. by move=> Px; apply: xgetPex; exists x. Qed.

Lemma xget_prop {T : choiceType} x0 (P : set T) (x : T) :
  P x -> is_prop P -> xget x0 P = x.
Proof. by move=> Px /(_ _ _ (xgetI x0 Px) Px). Qed.

Lemma xget_unique  {T : choiceType} x0 (P : set T) (x : T) :
  P x -> (forall y, P y -> y = x) -> xget x0 P = x.
Proof. by move=> /xget_prop gPx eqx; apply: gPx=> y z /eqx-> /eqx. Qed.

Lemma xgetPN {T : choiceType} x0 (P : set T) : (forall x, ~ P x) -> xget x0 P = x0.
Proof. by case: xgetP => // x _ Px /(_ x). Qed.

Definition fun_of_rel {A} {B : choiceType} (f0 : A -> B) (f : A -> B -> Prop) :=
  fun x => xget (f0 x) (f x).

Lemma fun_of_relP {A} {B : choiceType} (f : A -> B -> Prop) (f0 : A -> B) a :
  nonempty (f a) ->  f a (fun_of_rel f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_rel; apply: xgetI fab. Qed.

Lemma fun_of_rel_uniq {A} {B : choiceType} (f : A -> B -> Prop) (f0 : A -> B) a :
  is_prop (f a) -> forall b, f a b ->  fun_of_rel f0 f a = b.
Proof. by move=> fa_prop b /xget_prop xgeteq; rewrite /fun_of_rel xgeteq. Qed.

Module Pointed.

Definition point_of (T : Type) := T.

Record class_of (T : Type) := Class {
  base : Choice.class_of T;
  mixin : point_of T
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Choice.class_of.

Definition pack m :=
  fun bT b of phant_id (Choice.class bT) b => @Pack T (Class b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> point_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation pointedType := type.
Notation PointedType T m := (@pack T m _ _ idfun).
Notation "[ 'pointedType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'pointedType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pointedType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'pointedType'  'of'  T ]") : form_scope.

End Exports.

End Pointed.

Export Pointed.Exports.

Definition point {M : pointedType} : M := Pointed.mixin (Pointed.class M).

Canonical arrow_pointedType (T : Type) (T' : pointedType) :=
  PointedType (T -> T') (fun=> point).
Canonical bool_pointedType := PointedType bool false.
Canonical Prop_pointedType := PointedType Prop False.
Canonical nat_pointedType := PointedType nat 0%N.
Canonical prod_pointedType (T T' : pointedType) :=
  PointedType (T * T') (point, point).
Canonical matrix_pointedType m n (T : pointedType) :=
  PointedType 'M[T]_(m, n) (\matrix_(_, _) point)%R.

Notation get := (xget point).

Section PointedTheory.

Context {T : pointedType}.

Lemma getPex (P : set T) : (exists x, P x) -> P (get P).
Proof. exact: (xgetPex point). Qed.

Lemma getI (P : set T) (x : T): P x -> P (get P).
Proof. exact: (xgetI point). Qed.

Lemma get_prop (P : set T) (x : T) : P x -> is_prop P -> get P = x.
Proof. exact: (xget_prop point). Qed.

Lemma get_unique (P : set T) (x : T) :
   P x -> (forall y, P y -> y = x) -> get P = x.
Proof. exact: (xget_unique point). Qed.

Lemma getPN (P : set T) : (forall x, ~ P x) -> get P = point.
Proof. exact: (xgetPN point). Qed.

End PointedTheory.

Definition total_on T (A : set T) (R : T -> T -> Prop) :=
  forall s t, A s -> A t -> R s t \/ R t s.

Section ZL.

Variable (T : Type) (t0 : T) (R : T -> T -> Prop).
Hypothesis (Rrefl : forall t, R t t).
Hypothesis (Rtrans : forall r s t, R r s -> R s t -> R r t).
Hypothesis (Rantisym : forall s t, R s t -> R t s -> s = t).
Hypothesis (tot_lub : forall A : set T, total_on A R -> exists t,
  (forall s, A s -> R s t) /\ forall r, (forall s, A s -> R s r) -> R t r).
Hypothesis (Rsucc : forall s, exists t, R s t /\ s <> t /\
  forall r, R s r -> R r t -> r = s \/ r = t).

Let Teq := @gen_eqMixin T.
Let Tch := @gen_choiceMixin T.
Let Tp := Pointed.Pack (Pointed.Class (Choice.Class Teq Tch) t0) T.
Let lub := fun A : {A : set T | total_on A R} =>
  get (fun t : Tp => (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r).
Let succ := fun s => get (fun t : Tp => R s t /\ s <> t /\
  forall r, R s r -> R r t -> r = s \/ r = t).

Inductive tower : set T :=
  | Lub : forall A, sval A `<=` tower -> tower (lub A)
  | Succ : forall t, tower t -> tower (succ t).

Lemma ZL' : False.
Proof.
have lub_ub (A : {A : set T | total_on A R}) :
  forall s, sval A s -> R s (lub A).
  suff /getPex [] : exists t : Tp, (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r by [].
  by apply: tot_lub; apply: (svalP A).
have lub_lub (A : {A : set T | total_on A R}) :
  forall t, (forall s, sval A s -> R s t) -> R (lub A) t.
  suff /getPex [] : exists t : Tp, (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r by [].
  by apply: tot_lub; apply: (svalP A).
have RS s : R s (succ s) /\ s <> succ s.
  by have /getPex [? []] : exists t : Tp, R s t /\ s <> t /\
    forall r, R s r -> R r t -> r = s \/ r = t by apply: Rsucc.
have succS s : forall t, R s t -> R t (succ s) -> t = s \/ t = succ s.
  by have /getPex [? []] : exists t : Tp, R s t /\ s <> t /\
    forall r, R s r -> R r t -> r = s \/ r = t by apply: Rsucc.
suff Twtot : total_on tower R.
  have [R_S] := RS (lub (exist _ tower Twtot)); apply.
  by apply/Rantisym => //; apply/lub_ub/Succ/Lub.
move=> s t Tws; elim: Tws t => {s} [A sATw ihA|s Tws ihs] t Twt.
  case: (pselect (forall s, sval A s -> R s t)).
    by move=> ?; left; apply: lub_lub.
  move/asboolP; rewrite asbool_neg => /existsp_asboolPn [s /asboolP].
  rewrite asbool_neg => /imply_asboolPn [As nRst]; right.
  by have /lub_ub := As; apply: Rtrans; have [] := ihA _ As _ Twt.
suff /(_ _ Twt) [Rts|RSst] : forall r, tower r -> R r s \/ R (succ s) r.
    by right; apply: Rtrans Rts _; have [] := RS s.
  by left.
move=> r; elim=> {r} [A sATw ihA|r Twr ihr].
  case: (pselect (forall r, sval A r -> R r s)).
    by move=> ?; left; apply: lub_lub.
  move/asboolP; rewrite asbool_neg => /existsp_asboolPn [r /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ar nRrs]; right.
  by have /lub_ub := Ar; apply: Rtrans; have /ihA [] := Ar.
have [Rrs|RSsr] := ihr; last by right; apply: Rtrans RSsr _; have [] := RS r.
have : tower (succ r) by apply: Succ.
move=> /ihs [RsSr|]; last by left.
by have [->|->] := succS _ _ Rrs RsSr; [right|left]; apply: Rrefl.
Qed.

End ZL.

Require ClassicalFacts.

Lemma exist_congr T (P : T -> Prop) (s t : T) (p : P s) (q : P t) :
  s = t -> exist P s p = exist P t q.
Proof.
move=> seqt; case: _ / seqt q => q.
exact/congr1/ClassicalFacts.proof_irrelevance_cci/lem.
Qed.

Lemma Zorn T (R : T -> T -> Prop) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, forall s, R t s -> s = t.
Proof.
move=> Rrefl Rtrans Rantisym Rtot_max.
set totR := ({A : set T | total_on A R}).
set R' := fun A B : totR => sval A `<=` sval B.
have R'refl A : R' A A by [].
have R'trans A B C : R' A B -> R' B C -> R' A C by apply: subset_trans.
have R'antisym A B : R' A B -> R' B A -> A = B.
  rewrite /R'; case: A; case: B => /= B totB A totA sAB sBA.
  by apply: exist_congr; rewrite predeqE=> ?; split=> [/sAB|/sBA].
have R'tot_lub A : total_on A R' -> exists t, (forall s, A s -> R' s t) /\
    forall r, (forall s, A s -> R' s r) -> R' t r.
  move=> Atot.
  have AUtot : total_on (\bigcup_(B in A) (sval B)) R.
    move=> s t [B AB Bs] [C AC Ct].
    have [/(_ _ Bs) Cs|/(_ _ Ct) Bt] := Atot _ _ AB AC.
      by have /(_ _ _ Cs Ct) := svalP C.
    by have /(_ _ _ Bs Bt) := svalP B.
  exists (exist _ (\bigcup_(B in A) sval B) AUtot); split.
    by move=> B ???; exists B.
  by move=> B Bub ? /= [? /Bub]; apply.
apply: contrapT => nomax.
have {nomax} nomax t : exists s, R t s /\ s <> t.
  have /asboolP := nomax; rewrite asbool_neg => /forallp_asboolPn /(_ t).
  move=> /asboolP; rewrite asbool_neg => /existsp_asboolPn [s].
  by move=> /asboolP; rewrite asbool_neg => /imply_asboolPn []; exists s.
have tot0 : total_on set0 R by [].
apply: (ZL' (exist _ set0 tot0)) R'tot_lub _ => // A.
have /Rtot_max [t tub] := svalP A; have [s [Rts snet]] := nomax t.
have Astot : total_on (sval A `|` [set s]) R.
  move=> u v [Au|->]; last first.
    by move=> [/tub Rvt|->]; right=> //; apply: Rtrans Rts.
  move=> [Av|->]; [apply: (svalP A)|left] => //.
  by apply: Rtrans Rts; apply: tub.
exists (exist _ (sval A `|` [set s]) Astot); split; first by move=> ??; left.
split=> [AeAs|[B Btot] sAB sBAs].
  case: (pselect (sval A s)); first by move=> /tub Rst; apply/snet/Rantisym.
  by rewrite AeAs /=; apply; right.
case: (pselect (B s)) => [Bs|nBs].
  by right; apply: exist_congr; rewrite predeqE => r; split=> [/sBAs|[/sAB|->]].
left; case: A tub Astot sBAs sAB => A Atot /= tub Astot sBAs sAB.
apply: exist_congr; rewrite predeqE => r; split=> [Br|/sAB] //.
by have /sBAs [|ser] // := Br; rewrite ser in Br.
Qed.

Definition premaximal T (R : T -> T -> Prop) (t : T) :=
  forall s, R t s -> R s t.

Lemma ZL_preorder T (t0 : T) (R : T -> T -> Prop) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, premaximal R t.
Proof.
set Teq := @gen_eqMixin T; set Tch := @gen_choiceMixin T.
set Tp := Pointed.Pack (Pointed.Class (Choice.Class Teq Tch) t0) T.
move=> Rrefl Rtrans tot_max.
set eqR := fun s t => R s t /\ R t s; set ceqR := fun s => [set t | eqR s t].
have eqR_trans r s t : eqR r s -> eqR s t -> eqR r t.
  by move=> [Rrs Rsr] [Rst Rts]; split; [apply: Rtrans Rst|apply: Rtrans Rsr].
have ceqR_uniq s t : eqR s t -> ceqR s = ceqR t.
  by rewrite predeqE => - [Rst Rts] r; split=> [[Rr rR] | [Rr rR]]; split;
    try exact: Rtrans Rr; exact: Rtrans rR _.
set ceqRs := ceqR @` setT; set quotR := sig ceqRs.
have ceqRP t : ceqRs (ceqR t) by exists t.
set lift := fun t => exist _ (ceqR t) (ceqRP t).
have lift_surj (A : quotR) : exists t : Tp, lift t = A.
  case: A => A [t Tt ctA]; exists t; rewrite /lift; case : _ / ctA.
  exact/congr1/ClassicalFacts.proof_irrelevance_cci/lem.
have lift_inj s t : eqR s t -> lift s = lift t.
  by move=> eqRst; apply/exist_congr/ceqR_uniq.
have lift_eqR s t : lift s = lift t -> eqR s t.
  move=> cst; have ceqst : ceqR s = ceqR t by have := congr1 sval cst.
  by rewrite [_ s]ceqst; split; apply: Rrefl.
set repr := fun A : quotR => get [set t : Tp | lift t = A].
have repr_liftE t : eqR t (repr (lift t))
  by apply: lift_eqR; have -> := getPex (lift_surj (lift t)).
set R' := fun A B : quotR => R (repr A) (repr B).
have R'refl A : R' A A by apply: Rrefl.
have R'trans A B C : R' A B -> R' B C -> R' A C by apply: Rtrans.
have R'antisym A B : R' A B -> R' B A -> A = B.
  move=> RAB RBA; have [t tA] := lift_surj A; have [s sB] := lift_surj B.
  rewrite -tA -sB; apply: lift_inj; apply (eqR_trans _ _ _ (repr_liftE t)).
  have eAB : eqR (repr A) (repr B) by [].
  rewrite tA; apply: eqR_trans eAB _; rewrite -sB.
  by have [] := repr_liftE s.
have [A Atot|A Amax] := Zorn R'refl R'trans R'antisym.
  have /tot_max [t tmax] : total_on [set repr B | B in A] R.
    by move=> ?? [B AB <-] [C AC <-]; apply: Atot.
  exists (lift t) => B AB; have [Rt _] := repr_liftE t.
  by apply: Rtrans Rt; apply: tmax; exists B.
exists (repr A) => t RAt.
have /Amax <- : R' A (lift t).
  by have [Rt _] := repr_liftE t; apply: Rtrans Rt.
by have [] := repr_liftE t.
Qed.
