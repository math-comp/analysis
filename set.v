From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
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
