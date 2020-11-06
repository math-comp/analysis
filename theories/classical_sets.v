From mathcomp Require Import all_ssreflect ssralg matrix finmap order.
Require Import boolp.

(******************************************************************************)
(* This file develops a basic theory of sets and types equipped with a        *)
(* canonical inhabitant (pointed types).                                      *)
(*                                                                            *)
(* --> A decidable equality is defined for any type. It is thus possible to   *)
(*     define an eqType structure for any type using the mixin gen_eqMixin.   *)
(* --> This file adds the possibility to define a choiceType structure for    *)
(*     any type thanks to an axiom gen_choiceMixin giving a choice mixin.     *)
(* --> We chose to have generic mixins and no global instances of the eqType  *)
(*     and choiceType structures to let the user choose which definition of   *)
(*     equality to use and to avoid conflict with already declared instances. *)
(*                                                                            *)
(* * Sets:                                                                    *)
(*                       set A == type of sets on A.                          *)
(*                   (x \in P) == boolean membership predicate from ssrbool   *)
(*                                for set P, available thanks to a canonical  *)
(*                                predType T structure on sets on T.          *)
(*             [set x : T | P] == set of points x : T such that P holds.      *)
(*                 [set x | P] == same as before with T left implicit.        *)
(*            [set E | x in A] == set defined by the expression E for x in    *)
(*                                set A.                                      *)
(*   [set E | x in A & y in B] == same as before for E depending on 2         *)
(*                                variables x and y in sets A and B.          *)
(*                        setT == full set.                                   *)
(*                        set0 == empty set.                                  *)
(*                  [set of F] == set defined by the expression F x for any   *)
(*                                x.                                          *)
(*                     [set a] == set containing only a.                      *)
(*                 [set a : T] == same as before with the type of a made      *)
(*                                explicit.                                   *)
(*                     A `|` B == union of A and B.                           *)
(*                      a |` A == A extended with a.                          *)
(*        [set a1; a2; ..; an] == set containing only the n elements ai.      *)
(*                     A `&` B == intersection of A and B.                    *)
(*                     A `*` B == product of A and B, i.e. set of pairs (a,b) *)
(*                                such that A a and B b.                      *)
(*                        A.`1 == set of points a such that there exists b so *)
(*                                that A (a, b).                              *)
(*                        A.`2 == set of points a such that there exists b so *)
(*                                that A (b, a).                              *)
(*                        ~` A == complement of A.                            *)
(*                   [set ~ a] == complement of [set a].                      *)
(*                     A `\` B == complement of B in A.                       *)
(*                      A `\ a == A deprived of a.                            *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P.                          *)
(*           \bigcup_(i : T) F == union of the family F indexed on T.         *)
(*                 \bigcup_i F == same as before with T left implicit.        *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P.                  *)
(*           \bigcap_(i : T) F == union of the family F indexed on T.         *)
(*                 \bigcap_i F == same as before with T left implicit.        *)
(*                   A `<=` B <-> A is included in B.                         *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A.     *)
(*                   f @^-1` A == preimage of A by f.                         *)
(*                      f @` A == image of A by f.                            *)
(*                    A !=set0 := exists x, A x.                              *)
(*               is_subset1 X <-> X contains only 1 element.                  *)
(*                   is_fun f <-> for each a, f a contains only 1 element.    *)
(*                 is_total f <-> for each a, f a is non empty.               *)
(*              is_totalfun f <-> conjunction of is_fun and is_total.         *)
(*                   xget x0 P == point x in P if it exists, x0 otherwise;    *)
(*                                P must be a set on a choiceType.            *)
(*             fun_of_rel f0 f == function that maps x to an element of f x   *)
(*                                if there is one, to f0 x otherwise.         *)
(*                                                                            *)
(* * Pointed types:                                                           *)
(*                 pointedType == interface type for types equipped with a    *)
(*                                canonical inhabitant.                       *)
(*             PointedType T m == packs the term m : T to build a             *)
(*                                pointedType; T must have a choiceType       *)
(*                                structure.                                  *)
(*   [pointedType of T for cT] == T-clone of the pointedType structure cT.    *)
(*          [pointedType of T] == clone of a canonical pointedType structure  *)
(*                                on T.                                       *)
(*                       point == canonical inhabitant of a pointedType.      *)
(*                       get P == point x in P if it exists, point otherwise; *)
(*                                P must be a set on a pointedType.           *)
(*                                                                            *)
(* --> Thanks to this basic set theory, we proved Zorn's Lemma, which states  *)
(*     that any ordered set such that every totally ordered subset admits an  *)
(*     upper bound has a maximal element. We also proved an analogous version *)
(*     for preorders, where maximal is replaced with premaximal: t is         *)
(*     premaximal if whenever t < s we also have s < t.                       *)
(*                                                                            *)
(* * Upper and lower bounds:                                                  *)
(*              ubound, lbound == upper bound and lower bound sets            *)
(*               supremum x0 E == supremum of E or x0 if E is empty           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ 'set' x : T | P ]"
  (at level 0, x at level 99, only parsing).
Reserved Notation "[ 'set' x | P ]"
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]" (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' 'of' F ]" (at level 0, format "[ 'set'  'of'  F ]").
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (at level 2, left associativity, format "A .`1").
Reserved Notation "A .`2" (at level 2, left associativity, format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (at level 0, format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
(*
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
*)
Reserved Notation "\bigcup_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Proof. by move=> x y; apply: (iffP (asboolP _)). Qed.
Definition gen_eqMixin {T : Type} := EqMixin (@gen_eqP T).

Canonical arrow_eqType (T : Type) (T' : eqType) :=
  EqType (T -> T') gen_eqMixin.
Canonical arrow_choiceType (T : Type) (T' : choiceType) :=
  ChoiceType (T -> T') gen_choiceMixin.

Definition dep_arrow_eqType (T : Type) (T' : T -> eqType) :=
  EqType (forall x : T, T' x) gen_eqMixin.
Definition dep_arrow_choiceClass (T : Type) (T' : T -> choiceType) :=
  Choice.Class (Equality.class (dep_arrow_eqType T')) gen_choiceMixin.
Definition dep_arrow_choiceType (T : Type) (T' : T -> choiceType) :=
  Choice.Pack (dep_arrow_choiceClass T').

Canonical Prop_eqType := EqType Prop gen_eqMixin.
Canonical Prop_choiceType := ChoiceType Prop gen_choiceMixin.

Definition set A := A -> Prop.
(* we use fun x => instead of pred to prevent inE from working *)
(* we will then extend inE with in_setE to make this work      *)
Definition in_set T (P : set T) : pred T := (fun x => `[<P x>]).
Canonical set_predType T := @PredType T (set T) (@in_set T).

Lemma in_setE T (P : set T) x : x \in P = P x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Definition inE := (inE, in_setE).

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.

Notation "[ 'set' x : T | P ]" := ((fun x => P) : set T) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.
Notation "[ 'set' E | x 'in' A ]" :=
  [set y | exists2 x, A x & E = y] : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  [set z | exists2 x, A x & exists2 y, B y & E = z] : classical_set_scope.

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

Notation "[ 'set' 'of' F ]" := [set F i | i in setT] : classical_set_scope.
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A) : classical_set_scope.
Notation "A .`2" := (snd_set A) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.

Definition bigsetI A I (P : set I) (X : I -> set A) :=
  [set a | forall i, P i -> X i a].
Definition bigsetU A I (P : set I) (X : I -> set A) :=
  [set a | exists2 i, P i & X i a].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigsetU P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigsetI P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

Definition subset {A} (X Y : set A) := forall a, X a -> Y a.
Notation "A `<=` B" := (subset A B) : classical_set_scope.

Definition proper {A} (X Y : set A) := X `<=` Y /\ ~ (Y `<=` X).
Notation "A `<` B" := (proper A B) : classical_set_scope.

Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image f A) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Lemma eqEsubset T (F G : set T) : (F = G) = (F `<=` G /\ G `<=` F).
Proof.
rewrite propeqE; split => [->|[FG GF]]; [by split|].
by rewrite predeqE => t; split=> [/FG|/GF].
Qed.

Lemma sub0set T (X : set T) : set0 `<=` X.
Proof. by []. Qed.

Lemma setUCr T (A : set T) : A `|` ~` A = setT.
Proof.
by rewrite predeqE => t; split => // _; case: (pselect (A t)); [left|right].
Qed.

Lemma setC0 T : ~` set0 = setT :> set T.
Proof. by rewrite predeqE; split => ?. Qed.

Lemma setCK T : involutive (@setC T).
Proof. by move=> A; rewrite funeqE => t; rewrite /setC; exact: notLR. Qed.

Lemma subsets_disjoint {T} (A B : set T) : (A `<=` B) <-> (A `&` ~` B = set0).
Proof.
split=> [AB|]; first by rewrite predeqE => t; split => // -[/AB].
rewrite predeqE => AB t At; move: (AB t) => [{}AB _].
by apply: contrapT => Bt; exact: AB.
Qed.

Lemma disjoints_subset {T} (A B : set T) : A `&` B = set0 <-> A `<=` ~` B.
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma setCT T : ~` setT = set0 :> set T. Proof. by rewrite -setC0 setCK. Qed.

Lemma setDE {A} (X Y : set A) : X `\` Y = X `&` ~` Y.
Proof. by []. Qed.

Lemma setTD T (A : set T) : setT `\` A = ~` A.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma setDv T (A : set T) : A `\` A = set0.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma subset0 T (X : set T) : (X `<=` set0) = (X = set0).
Proof. by rewrite eqEsubset propeqE; split => [X0|[]//]; split. Qed.

Lemma set0P T (X : set T) : (X != set0) <-> (X !=set0).
Proof.
split=> [/negP X_neq0|[t tX]]; last by apply/negP => /eqP X0; rewrite X0 in tX.
apply: contrapT => /asboolPn/forallp_asboolPn X0; apply/X_neq0/eqP.
by rewrite eqEsubset; split.
Qed.

Lemma imageP {A B} (f : A -> B) (X : set A) a : X a -> (f @` X) (f a).
Proof. by exists a. Qed.

Lemma image_inj {A B} (f : A -> B) (X : set A) a :
  injective f -> (f @` X) (f a) = X a.
Proof.
by move=> f_inj; rewrite propeqE; split => [[b Xb /f_inj <-]|/(imageP f)//].
Qed.
Arguments image_inj {A B} [f X a].

Lemma image_comp T U V (f : T -> U) (g : U -> V) A :
  g @` (f @` A) = (g \o f) @` A.
Proof.
rewrite eqEsubset; split => x.
- by case => b [] a Xa <- <-; apply/imageP.
- by case => a Xa <-; apply/imageP/imageP.
Qed.

Lemma image_id T (A : set T) : id @` A = A.
Proof. by rewrite eqEsubset; split => a; [case=> /= x Xx <-|exists a]. Qed.

Lemma image_setU T U (f : T -> U) A B : f @` (A `|` B) = f @` A `|` f @` B.
Proof.
rewrite eqEsubset; split => b.
- by case=> a [] Ha <-; [left | right]; apply imageP.
- by case=> -[] a Ha <-; apply imageP; [left | right].
Qed.

Lemma image_set0 T U (f : T -> U) : f @` set0 = set0.
Proof. by rewrite eqEsubset; split => b // -[]. Qed.

Lemma image_set0_set0 T U (A : set T) (f : T -> U) : f @` A = set0 -> A = set0.
Proof.
move=> fA0; rewrite predeqE => t; split => // At.
by have : set0 (f t) by rewrite -fA0; exists t.
Qed.

Lemma image_set1 T U (f : T -> U) (t : T) : f @` [set t] = [set f t].
Proof. by rewrite eqEsubset; split => [b [a' -> <-] //|b ->]; exact/imageP. Qed.

Lemma subset_set1 T (A : set T) a : A `<=` [set a] -> A = set0 \/ A = [set a].
Proof.
move=> Aa; have [|/set0P/negP/negPn/eqP->] := pselect (A !=set0); [|by left].
by case=> t At; right; rewrite eqEsubset; split => // ? ->; rewrite -(Aa _ At).
Qed.

Lemma sub_image_setI {A B} (f : A -> B) (X Y : set A) :
  f @` (X `&` Y) `<=` f @` X `&` f @` Y.
Proof. by move=> b [x [Xa Ya <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {A B f X Y} a _.

Lemma nonempty_image {A B} (f : A -> B) (X : set A) :
  f @` X !=set0 -> X !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma image_subset A B (f : A -> B) (X Y : set A) :
  X `<=` Y -> f @` X `<=` f @` Y.
Proof. by move=> XY _ [a Xa <-]; exists a => //; apply/XY. Qed.

Lemma preimage_set0 T U (f : T -> U) : f @^-1` set0 = set0.
Proof. by rewrite predeqE. Qed.

Lemma nonempty_preimage {A B} (f : A -> B) (X : set B) :
  f @^-1` X !=set0 -> X !=set0.
Proof. by case=> [a ?]; exists (f a). Qed.

Lemma preimage_image A B (f : A -> B) (X : set A) : X `<=` f @^-1` (f @` X).
Proof. by move=> a Xa; exists a. Qed.

Lemma image_preimage_subset A B (f : A -> B) (Y : set B) :
  f @` (f @^-1` Y) `<=` Y.
Proof. by move=> _ [a /= Yfa <-]. Qed.

Lemma image_preimage A B (f : A -> B) (X : set B) :
  f @` setT = setT -> f @` (f @^-1` X) = X.
Proof.
move=> fsurj; rewrite predeqE => x; split; first by move=> [?? <-].
move=> Xx; have : setT x by [].
by rewrite -fsurj => - [y _ fy_eqx]; exists y => //; rewrite /preimage fy_eqx.
Qed.

Lemma preimage_setU {A B} (f : A -> B) (X Y : set B) :
  f @^-1` (X `|` Y) = f @^-1` X `|` f @^-1` Y.
Proof. by rewrite predeqE. Qed.

Lemma preimage_bigcup {A B I} (P : set I) (f : A -> B) F :
  f @^-1` (\bigcup_ (i in P) F i) = \bigcup_(i in P) (f @^-1` F i).
Proof. by rewrite predeqE. Qed.

Lemma preimage_setI {A B} (f : A -> B) (X Y : set B) :
  f @^-1` (X `&` Y) = f @^-1` X `&` f @^-1` Y.
Proof. by rewrite predeqE. Qed.

Lemma preimage_bigcap {A B I} (P : set I) (f : A -> B) F :
  f @^-1` (\bigcap_ (i in P) F i) = \bigcap_(i in P) (f @^-1` F i).
Proof. by rewrite predeqE. Qed.

Lemma preimage_setC A B (f : A -> B) (X : set B) :
  ~` (f @^-1` X) = f @^-1` (~` X).
Proof. by rewrite predeqE => a; split=> nXfa ?; apply: nXfa. Qed.

Lemma preimage_subset A B (f : A -> B) (X Y : set B) :
  X `<=` Y -> f @^-1` X `<=` f @^-1` Y.
Proof. by move=> XY a /XY. Qed.

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

Lemma subUset T (X Y Z : set T) : (Y `|` Z `<=` X) = ((Y `<=` X) /\ (Z `<=` X)).
Proof.
rewrite propeqE; split => [|[YX ZX] x]; last by case; [exact: YX | exact: ZX].
by move=> sYZ_X; split=> x ?; apply sYZ_X; [left | right].
Qed.

Lemma setIidPl {T} (A B : set T) : A `&` B = A <-> A `<=` B.
Proof.
rewrite predeqE; split=> [AB t /AB [] //|AB t].
by split=> [[]//|At]; split=> //; exact: AB.
Qed.

Lemma setUidPl {T} (X Y : set T) : X `|` Y = X <-> Y `<=` X.
Proof.
split=> [<- ? ?|YX]; first by right.
rewrite predeqE => t; split=> [[//|/YX//]|?]; by left.
Qed.

Lemma subsetI A (X Y Z : set A) : (X `<=` Y `&` Z) = ((X `<=` Y) /\ (X `<=` Z)).
Proof.
rewrite propeqE; split=> [H|[y z ??]]; split; by [move=> ?/H[]|apply y|apply z].
Qed.

Lemma setDidPl {T} (A B :set T) : A `\` B = A <-> A `&` B = set0.
Proof.
rewrite setDE disjoints_subset predeqE; split => [AB t|AB t].
by rewrite -AB => -[].
by split=> [[]//|At]; move: (AB t At).
Qed.

Lemma subIset {A} (X Y Z : set A) : X `<=` Z \/ Y `<=` Z -> X `&` Y `<=` Z.
Proof. case => H a; by [move=> [/H] | move=> [_ /H]]. Qed.

Lemma subsetI_neq0 T (A B C D : set T) :
  A `<=` B -> C `<=` D -> A `&` C !=set0 -> B `&` D !=set0.
Proof. by move=> AB CD [x [/AB Bx /CD Dx]]; exists x. Qed.

Lemma subsetI_eq0 T (A B C D : set T) :
  A `<=` B -> C `<=` D -> B `&` D = set0 -> A `&` C = set0.
Proof. by move=> AB /(subsetI_neq0 AB); rewrite -!set0P => /contra_eq. Qed.

Lemma setD_eq0 A (X Y : set A) : (X `\` Y = set0) = (X `<=` Y).
Proof.
rewrite propeqE; split=> [XDY0 a|sXY].
  by apply: contraPP => nYa xA; rewrite -[False]/(set0 a) -XDY0.
by rewrite predeqE => ?; split=> // - [?]; apply; apply: sXY.
Qed.

Lemma properEneq {A} (X Y : set A) : (X `<` Y) = (X != Y /\ X `<=` Y).
Proof.
rewrite /proper andC propeqE; split => [[YX XY]|[/eqP]].
by split => //; apply/negP; apply: contra_not YX => /eqP ->.
by rewrite eqEsubset => XY YX; split => //; exact: contra_not XY.
Qed.

Lemma nonsubset {A} (X Y : set A) : ~ (X `<=` Y) -> X `&` ~` Y !=set0.
Proof. by rewrite -setD_eq0 setDE -set0P => /eqP. Qed.

Lemma setIC {A} (X Y : set A) : X `&` Y = Y `&` X.
Proof. by rewrite predeqE => ?; split=> [[]|[]]. Qed.

Lemma setIS T (A B C : set T) : A `<=` B -> C `&` A `<=` C `&` B.
Proof. by move=> sAB t [Ct At]; split => //; exact: sAB. Qed.

Lemma setSI T (A B C : set T) : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(setIC C); apply setIS. Qed.

Lemma setSD T (A B C : set T) : A `<=` B -> A `\` C `<=` B `\` C.
Proof. by rewrite !setDE; apply: setSI. Qed.

Lemma setISS T (A B C D : set T) : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(@setSI _ _ _ B) /subset_trans sAC /(@setIS _ _ _ C) /sAC. Qed.

Lemma setIT {A} (X : set A) : X `&` setT = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setTI {A} (X : set A) : setT `&` X = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setI0 {A} (X : set A) : X `&` set0 = set0.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma set0I A (Y : set A) : set0 `&` Y = set0.
Proof. by rewrite setIC setI0. Qed.

Lemma setICl {A} (X : set A) : ~` X `&` X = set0.
Proof. by rewrite predeqE => ?; split => // -[]. Qed.

Lemma setICr {A} (X : set A) : X `&` ~` X = set0.
Proof. by rewrite setIC setICl. Qed.

Lemma setIA {A} (X Y Z : set A) : X `&` (Y `&` Z) = X `&` Y `&` Z.
Proof. by rewrite predeqE => ?; split=> [[? []]|[[]]]. Qed.

Lemma setICA {A} (X Y Z : set A) : X `&` (Y `&` Z) = Y `&` (X `&` Z).
Proof. by rewrite setIA [X `&` _]setIC -setIA. Qed.

Lemma setIAC {A} (X Y Z : set A) : X `&` Y `&` Z = X `&` Z `&` Y.
Proof. by rewrite setIC setICA setIA. Qed.

Lemma setIACA {A} (X Y Z T : set A) :
  X `&` Y `&` (Z `&` T) = X `&` Z `&` (Y `&` T).
Proof. by rewrite -setIA [Y `&` _]setICA setIA. Qed.

Lemma setIid {A} (X : set A) : X `&` X = X.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIIl T (A B C : set T) : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr T (A B C : set T) : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(setIC A) setIIl. Qed.

Lemma setUA A : associative (@setU A).
Proof. move=> p q r; rewrite /setU predeqE => a; tauto. Qed.

Lemma setUid A : idempotent (@setU A).
Proof. move=> p; rewrite /setU predeqE => a; tauto. Qed.

Lemma setUC A : commutative (@setU A).
Proof. move=> p q; rewrite /setU predeqE => a; tauto. Qed.

Lemma set0U T (X : set T) : set0 `|` X = X.
Proof. by rewrite predeqE => t; split; [case|right]. Qed.

Lemma setU0 T (X : set T) : X `|` set0 = X.
Proof. by rewrite predeqE => t; split; [case|left]. Qed.

Lemma setTU T (X : set T) : setT `|` X = setT.
Proof. by rewrite predeqE => t; split; [case|left]. Qed.

Lemma setUT T (X : set T) : X `|` setT = setT.
Proof. by rewrite predeqE => t; split; [case|right]. Qed.

Lemma setU_eq0 T (X Y : set T) : (X `|` Y = set0) = ((X = set0) /\ (Y = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setUCl T (A : set T) : ~` A `|` A = setT.
Proof. by rewrite setUC setUCr. Qed.

Lemma setCS T (A B : set T) : (~` A `<=` ~` B) = (B `<=` A).
Proof.
rewrite propeqE; split => [|BA].
  by move/subsets_disjoint; rewrite setCK setIC => /subsets_disjoint.
by apply/subsets_disjoint; rewrite setCK setIC; apply/subsets_disjoint.
Qed.

Lemma setDS T (A B C : set T) : A `<=` B -> C `\` B `<=` C `\` A.
Proof. by rewrite !setDE -setCS; apply: setIS. Qed.

Lemma setDSS T (A B C D : set T) : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof.
by move=> /(@setSD _ _ _ B) /subset_trans sAC /(@setDS _ _ _ C) /sAC.
Qed.

Lemma setCU T (X Y : set T) : ~`(X `|` Y) = ~` X `&` ~` Y.
Proof.
rewrite predeqE => z.
by apply: asbool_eq_equiv; rewrite asbool_and !asbool_neg asbool_or negb_or.
Qed.

Lemma setCI T (A B : set T) : ~` (A `&` B) = ~` A `|` ~` B.
Proof. by rewrite -[in LHS](setCK A) -[in LHS](setCK B) -setCU setCK. Qed.

Lemma setDUr T (A B C : set T) : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Proof. by rewrite !setDE setCU setIIr. Qed.

Lemma setI_bigcapl A I (D : set I) (f : I -> set A) (X : set A) :
  D !=set0 -> \bigcap_(i in D) f i `&` X = \bigcap_(i in D) (f i `&` X).
Proof.
move=> [i Di]; rewrite predeqE => a; split=> [[Ifa Xa] j Dj|IfIXa].
  by split=> //; apply: Ifa.
by split=> [j /IfIXa [] | ] //; have /IfIXa [] := Di.
Qed.

Lemma setIUl T : left_distributive (@setI T) (@setU T).
Proof.
move=> X Y Z; rewrite predeqE => t; split.
  by move=> [[Xt|Yt] Zt]; [left|right].
by move=> [[Xt Zt]|[Yt Zt]]; split => //; [left|right].
Qed.

Lemma setIUr T : right_distributive (@setI T) (@setU T).
Proof. by move=> X Y Z; rewrite ![X `&` _]setIC setIUl. Qed.

Lemma setUIl T : left_distributive (@setU T) (@setI T).
Proof.
move=> X Y Z; rewrite predeqE => t; split.
  by move=> [[Xt Yt]|Zt]; split; by [left|right].
by move=> [[Xt|Zt] [Yt|Zt']]; by [left|right].
Qed.

Lemma setUIr T : right_distributive (@setU T) (@setI T).
Proof. by move=> X Y Z; rewrite ![X `|` _]setUC setUIl. Qed.

Lemma setUK T (A B : set T) : (A `|` B) `&` A = A.
Proof. by rewrite eqEsubset; split => [t []//|t ?]; split => //; left. Qed.

Lemma setKU T (A B : set T) : A `&` (B `|` A) = A.
Proof. by rewrite eqEsubset; split => [t []//|t ?]; split => //; right. Qed.

Lemma setIK T (A B : set T) : (A `&` B) `|` A = A.
Proof. by rewrite eqEsubset; split => [t [[]//|//]|t At]; right. Qed.

Lemma setKI T (A B : set T) : A `|` (B `&` A) = A.
Proof. by rewrite eqEsubset; split => [t [//|[]//]|t At]; left. Qed.

Lemma setDUl T (A B C : set T) : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
Proof. by rewrite !setDE setIUl. Qed.

Lemma setIDA T (A B C : set T) : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by rewrite !setDE setIA. Qed.

Lemma setDD T (A B : set T) : A `\` (A `\` B) = A `&` B.
Proof. by rewrite 2!setDE setCI setCK setIUr setICr set0U. Qed.

Lemma bigcup_set0 T U (X : U -> set T) : \bigcup_(i in set0) X i = set0.
Proof. by rewrite eqEsubset; split => a // []. Qed.

Lemma bigcup_set1 T V (U : V -> set T) v : \bigcup_(i in [set v]) U i = U v.
Proof. by rewrite eqEsubset; split => ? => [[] ? -> //|]; exists v. Qed.

Lemma bigcapCU T I (U : I -> set T) E :
  \bigcap_(i in E) (U i) = ~` (\bigcup_(i in E) (~` U i)).
Proof.
rewrite predeqE => t; split => [capU|cupU i Et].
  by move=> -[n En]; apply; apply capU.
by rewrite -(setCK (U i)) => CU; apply cupU; exists i.
Qed.

Lemma setM0 T U (A : set T) : A `*` @set0 U = set0.
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma set0M T U (B : set U) : @set0 T `*` B = set0.
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma setMT {A B} : (@setT A) `*` (@setT B) = setT.
Proof. by rewrite predeqE. Qed.

Definition is_subset1 {A} (X : set A) := forall x y, X x -> X y -> x = y.
Definition is_fun {A B} (f : A -> B -> Prop) := Logic.all (is_subset1 \o f).
Definition is_total {A B} (f : A -> B -> Prop) := Logic.all (nonempty \o f).
Definition is_totalfun {A B} (f : A -> B -> Prop) :=
  forall x, f x !=set0 /\ is_subset1 (f x).

Definition xget {T : choiceType} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).

CoInductive xget_spec {T : choiceType} x0 (P : set T) : T -> Prop -> Type :=
| XGetSome x of x = xget x0 P & P x : xget_spec x0 P x True
| XGetNone of (forall x, ~ P x) : xget_spec x0 P x0 False.

Lemma xgetP {T : choiceType} x0 (P : set T) :
  xget_spec x0 P (xget x0 P) (P (xget x0 P)).
Proof.
move: (erefl (xget x0 P)); set y := {2}(xget x0 P).
rewrite /xget; case: pselect => /= [?|neqP _].
  by case: sigW => x /= /asboolP Px; rewrite [P x]propT //; constructor.
suff NP x : ~ P x by rewrite [P x0]propF //; constructor.
by apply: contra_not neqP => Px; exists x; apply/asboolP.
Qed.

Lemma xgetPex {T : choiceType} x0 (P : set T) : (exists x, P x) -> P (xget x0 P).
Proof. by case: xgetP=> // NP [x /NP]. Qed.

Lemma xgetI {T : choiceType} x0 (P : set T) (x : T): P x -> P (xget x0 P).
Proof. by move=> Px; apply: xgetPex; exists x. Qed.

Lemma xget_subset1 {T : choiceType} x0 (P : set T) (x : T) :
  P x -> is_subset1 P -> xget x0 P = x.
Proof. by move=> Px /(_ _ _ (xgetI x0 Px) Px). Qed.

Lemma xget_unique  {T : choiceType} x0 (P : set T) (x : T) :
  P x -> (forall y, P y -> y = x) -> xget x0 P = x.
Proof. by move=> /xget_subset1 gPx eqx; apply: gPx=> y z /eqx-> /eqx. Qed.

Lemma xgetPN {T : choiceType} x0 (P : set T) :
  (forall x, ~ P x) -> xget x0 P = x0.
Proof. by case: xgetP => // x _ Px /(_ x). Qed.

Definition fun_of_rel {A} {B : choiceType} (f0 : A -> B) (f : A -> B -> Prop) :=
  fun x => xget (f0 x) (f x).

Lemma fun_of_relP {A} {B : choiceType} (f : A -> B -> Prop) (f0 : A -> B) a :
  f a !=set0 -> f a (fun_of_rel f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_rel; apply: xgetI fab. Qed.

Lemma fun_of_rel_uniq {A} {B : choiceType}
    (f : A -> B -> Prop) (f0 : A -> B) a :
  is_subset1 (f a) -> forall b, f a b ->  fun_of_rel f0 f a = b.
Proof. by move=> fa1 b /xget_subset1 xgeteq; rewrite /fun_of_rel xgeteq. Qed.

Section SetMonoids.
Variable (T : Type).

Import Monoid.
Canonical setU_monoid := Law (@setUA T) (@set0U T) (@setU0 T).
Canonical setU_comoid := ComLaw (@setUC T).
Canonical setU_mul_monoid := MulLaw (@setTU T) (@setUT T).
Canonical setI_monoid := Law (@setIA T) (@setTI T) (@setIT T).
Canonical setI_comoid := ComLaw (@setIC T).
Canonical setI_mul_monoid := MulLaw (@set0I T) (@setI0 T).
Canonical setU_add_monoid := AddLaw (@setUIl T) (@setUIr T).
Canonical setI_add_monoid := AddLaw (@setIUl T) (@setIUr T).

End SetMonoids.

Lemma bigcup_recl T n (A : nat -> set T) :
  \bigcup_i A i = \big[setU/set0]_(i < n) A i `|` \bigcup_i A (n + i)%N.
Proof.
elim: n => [|n ih]; first by rewrite big_ord0 set0U.
rewrite ih big_ord_recr /= -setUA; congr (_ `|` _).
rewrite predeqE => t; split => [[[|m] _ At]|[At|[i _ At]]].
- by left; rewrite addn0 in At.
  by right; exists m => //; rewrite addSnnS.
- by exists 0%N => //; rewrite addn0.
  by exists i.+1 => //; rewrite -addSnnS.
Qed.

Lemma bigcup_distrr T (A : nat -> set T) X :
  X `&` \bigcup_i (A i) = \bigcup_i (X `&` A i).
Proof.
rewrite predeqE => t; split => [[Xt [k _ Akt]]|[k _ [Xt Akt]]];
  by [exists k |split => //; exists k].
Qed.

Lemma bigcup_ord T n (A : nat -> set T) :
 \big[setU/set0]_(i < n) A i = \bigcup_(i in [set k | (k < n)%N]) A i.
Proof.
elim: n => [|n IHn] in A *; first by rewrite big_ord0 predeqE; split => -[].
rewrite big_ord_recl /= (IHn (fun i => A i.+1)) predeqE => x; split.
  by move=> [A0|[i AS]]; [exists 0%N|exists i.+1].
by move=> [[|i] Ai]; [left|right; exists i].
Qed.

Lemma subset_bigsetU T m n (U : nat -> set T) : (m <= n)%N ->
  \big[setU/set0]_(i < m) U i `<=` \big[setU/set0]_(i < n) U i.
Proof.
by rewrite !bigcup_ord => mn x [i im ?]; exists i => //; rewrite (leq_trans im).
Qed.

Lemma bigcap_ord T n (A : nat -> set T) :
 \big[setI/setT]_(i < n) A i = \bigcap_(i in [set k | (k < n)%N]) A i.
Proof.
elim: n => [|n IHn] in A *; first by rewrite big_ord0 predeqE.
rewrite big_ord_recl /= (IHn (fun i => A i.+1)) predeqE => x; split.
  by move=> [A0 AS] [|i]// /AS.
by move=> AP; split => [|i i_lt]; apply: AP.
Qed.

Module Pointed.

Definition point_of (T : Type) := T.

Record class_of (T : Type) := Class {
  base : Choice.class_of T;
  mixin : point_of T
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Choice.class_of.

Definition pack m :=
  fun bT b of phant_id (Choice.class bT) b => @Pack T (Class b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.

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

Definition dep_arrow_pointedType (T : Type) (T' : T -> pointedType) :=
  Pointed.Pack
   (Pointed.Class (dep_arrow_choiceClass T') (fun i => @point (T' i))).

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

Lemma get_subset1 (P : set T) (x : T) : P x -> is_subset1 P -> get P = x.
Proof. exact: (xget_subset1 point). Qed.

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
Let Tp := Pointed.Pack (Pointed.Class (Choice.Class Teq Tch) t0).
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
  have [?|/asboolP] := pselect (forall s, sval A s -> R s t).
    by left; apply: lub_lub.
  rewrite asbool_neg => /existsp_asboolPn [s /asboolP].
  rewrite asbool_neg => /imply_asboolPn [As nRst]; right.
  by have /lub_ub := As; apply: Rtrans; have [] := ihA _ As _ Twt.
suff /(_ _ Twt) [Rts|RSst] : forall r, tower r -> R r s \/ R (succ s) r.
    by right; apply: Rtrans Rts _; have [] := RS s.
  by left.
move=> r; elim=> {r} [A sATw ihA|r Twr ihr].
  have [?|/asboolP] := pselect (forall r, sval A r -> R r s).
    by left; apply: lub_lub.
  rewrite asbool_neg => /existsp_asboolPn [r /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ar nRrs]; right.
  by have /lub_ub := Ar; apply: Rtrans; have /ihA [] := Ar.
have [Rrs|RSsr] := ihr; last by right; apply: Rtrans RSsr _; have [] := RS r.
have : tower (succ r) by apply: Succ.
move=> /ihs [RsSr|]; last by left.
by have [->|->] := succS _ _ Rrs RsSr; [right|left]; apply: Rrefl.
Qed.

End ZL.

Lemma exist_congr T (P : T -> Prop) (s t : T) (p : P s) (q : P t) :
  s = t -> exist P s p = exist P t q.
Proof. by move=> st; case: _ / st in q *; apply/congr1/Prop_irrelevance. Qed.

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
have {}nomax t : exists s, R t s /\ s <> t.
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
  have [/tub Rst|] := (pselect (sval A s)); first exact/snet/Rantisym.
  by rewrite AeAs /=; apply; right.
have [Bs|nBs] := pselect (B s).
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
set Tp := Pointed.Pack (Pointed.Class (Choice.Class Teq Tch) t0).
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
  exact/congr1/Prop_irrelevance.
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

Section UpperLowerTheory.
Import Order.TTheory.
Variables (d : unit) (T : porderType d).
Implicit Types E : set T.

Definition ubound E : set T := [set z | forall y, E y -> (y <= z)%O].
Definition lbound E : set T := [set z | forall y, E y -> (z <= y)%O].

Lemma ubP E x : (forall y, E y -> (y <= x)%O) <-> ubound E x.
Proof. by []. Qed.

Lemma lbP E x : (forall y, E y -> (x <= y)%O) <-> lbound E x.
Proof. by []. Qed.

Lemma ub_set1 x y : ubound [set x] y = (x <= y)%O.
Proof. by rewrite propeqE; split => [/(_ x erefl)//|xy z ->]. Qed.

Lemma lb_set1 x y : lbound [set x] y = (x >= y)%O.
Proof. by rewrite propeqE; split => [/(_ x erefl)//|xy z ->]. Qed.

Lemma lb_ub_set1 x y : lbound (ubound [set x]) y -> (y <= x)%O.
Proof. by move/(_ x); apply; rewrite ub_set1. Qed.

Lemma ub_lb_set1 x y : ubound (lbound [set x]) y -> (x <= y)%O.
Proof. by move/(_ x); apply; rewrite lb_set1. Qed.

Lemma lb_ub_refl x : lbound (ubound [set x]) x.
Proof. by move=> y; apply. Qed.

Lemma ub_lb_refl x : ubound (lbound [set x]) x.
Proof. by move=> y; apply. Qed.

Lemma ub_lb_ub E x y : ubound E y -> lbound (ubound E) x -> (x <= y)%O.
Proof. by move=> Ey; apply. Qed.

Lemma lb_ub_lb E x y : lbound E y -> ubound (lbound E) x -> (y <= x)%O.
Proof. by move=> Ey; apply. Qed.

(* down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down E : set T := [set x | exists y, E y /\ (x <= y)%O].

(* Real set supremum and infimum existence condition. *)
Definition has_ubound E := ubound E !=set0.
Definition has_sup E := E !=set0 /\ has_ubound E.
Definition has_lbound  E := lbound E !=set0.
Definition has_inf E := E !=set0 /\ has_lbound E.

Lemma has_ub_set1 x : has_ubound [set x].
Proof. by exists x; rewrite ub_set1. Qed.

Lemma downP E x : (exists2 y, E y & (x <= y)%O) <-> down E x.
Proof. by split => [[y Ey xy]|[y [Ey xy]]]; [exists y| exists y]. Qed.

Definition supremums E := ubound E `&` lbound (ubound E).

Lemma supremums_set1 x : supremums [set x] = [set x].
Proof.
rewrite /supremums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite ub_set1|exact: lb_ub_refl].
by rewrite ub_set1 => xy /lb_ub_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_supremums E : is_subset1 (supremums E).
Proof.
move=> x y [Ex xE] [Ey yE]; apply/eqP.
by rewrite eq_le (ub_lb_ub Ex yE) (ub_lb_ub Ey xE).
Qed.

Definition supremum (x0 : T) E :=
  if pselect (E !=set0) then xget x0 (supremums E) else x0.

Definition infimums E := lbound E `&` ubound (lbound E).

Definition infimum (x0 : T) E :=
  if pselect (E !=set0) then xget x0 (infimums E) else x0.

Lemma infimums_set1 x : infimums [set x] = [set x].
Proof.
rewrite /infimums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite lb_set1|apply ub_lb_refl].
by rewrite lb_set1 => xy /ub_lb_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_infimums E : is_subset1 (infimums E).
Proof.
move=> x y [Ex xE] [Ey yE]; apply/eqP.
by rewrite eq_le (lb_ub_lb Ex yE) (lb_ub_lb Ey xE).
Qed.

End UpperLowerTheory.

Section UpperLowerOrderTheory.
Import Order.TTheory.
Variables (d : unit) (T : orderType d).
Implicit Types E : set T.

Lemma ge_supremum_Nmem x0 E t :
  supremums E !=set0 -> E t -> (supremum x0 E >= t)%O.
Proof.
case=> x Ex; rewrite /supremum.
case: pselect => /= [_ | /set0P/negP/negPn/eqP -> //].
by case: xgetP => [t' t'E [uEt' _]|/(_ x) //]; exact: uEt'.
Qed.

Lemma le_infimum_Nmem x0 E t :
  infimums E !=set0 -> E t -> (infimum x0 E <= t)%O.
Proof.
case=> x Ex; rewrite /infimum.
case: pselect => /= [_ | /set0P/negP/negPn/eqP -> //].
by case: xgetP => [t' t'E [uEt' _]|/(_ x) //]; exact: uEt'.
Qed.

End UpperLowerOrderTheory.

Lemma nat_supremums_neq0 (E : set nat) : ubound E !=set0 -> supremums E !=set0.
Proof.
case => /=; elim => [E0|n ih]; first by exists O.
case: (pselect (ubound E n)) => [/ih //|En {ih}] En1.
exists n.+1; split => // m Em; case/existsNP : En => k /not_implyP[Ek /negP].
rewrite -Order.TotalTheory.ltNge => kn.
by rewrite (Order.POrderTheory.le_trans _ (Em _ Ek)).
Qed.

Fact set_display : unit. Proof. by []. Qed.

Module SetOrder.
Module Internal.
Section SetOrder.

Context {T : Type}.
Implicit Types X Y : set T.

Lemma le_def X Y : `[< X `<=` Y >] = (X `&` Y == X).
Proof. by apply/asboolP/eqP; rewrite setIidPl. Qed.

Lemma lt_def X Y : `[< X `<` Y >] = (Y != X) && `[< X `<=` Y >].
Proof.
apply/idP/idP => [/asboolP|/andP[YX /asboolP XY]]; rewrite properEneq eq_sym;
  by [move=> [] -> /asboolP|apply/asboolP].
Qed.

Fact SetOrder_joinKI (Y X : set T) : X `&` (X `|` Y) = X.
Proof. by rewrite setUC setKU. Qed.

Fact SetOrder_meetKU (Y X : set T) : X `|` (X `&` Y) = X.
Proof. by rewrite setIC setKI. Qed.

Definition orderMixin := @MeetJoinMixin _ _ (fun X Y => `[<proper X Y>]) setI
  setU le_def lt_def (@setIC _) (@setUC _) (@setIA _) (@setUA _) SetOrder_joinKI
  SetOrder_meetKU (@setIUl _) setIid.

Local Canonical porderType := POrderType set_display (set T) orderMixin.
Local Canonical latticeType := LatticeType (set T) orderMixin.
Local Canonical distrLatticeType := DistrLatticeType (set T) orderMixin.

Fact SetOrder_sub0set (x : set T) : (set0 <= x)%O.
Proof. by apply/asboolP; apply: sub0set. Qed.

Fact SetOrder_setTsub (x : set T) : (x <= setT)%O.
Proof. exact/asboolP. Qed.

Local Canonical bLatticeType :=
  BLatticeType (set T) (Order.BLattice.Mixin  SetOrder_sub0set).
Local Canonical tbLatticeType :=
  TBLatticeType (set T) (Order.TBLattice.Mixin SetOrder_setTsub).
Local Canonical bDistrLatticeType := [bDistrLatticeType of set T].
Local Canonical tbDistrLatticeType := [tbDistrLatticeType of set T].

Lemma subKI X Y : Y `&` (X `\` Y) = set0.
Proof. by rewrite setDE setICA setICr setI0. Qed.

Lemma joinIB X Y : (X `&` Y) `|` X `\` Y = X.
Proof. by rewrite setDE -setIUr setUCr setIT. Qed.

Local Canonical cbDistrLatticeType := CBDistrLatticeType (set T)
  (@CBDistrLatticeMixin _ _ (fun X Y => X `\` Y) subKI joinIB).

Local Canonical ctbDistrLatticeType := CTBDistrLatticeType (set T)
  (@CTBDistrLatticeMixin _ _ _ (fun X => ~` X) (fun x => esym (setTD x))).

End SetOrder.
End Internal.

Module Exports.

Canonical Internal.porderType.
Canonical Internal.latticeType.
Canonical Internal.distrLatticeType.
Canonical Internal.bLatticeType.
Canonical Internal.tbLatticeType.
Canonical Internal.bDistrLatticeType.
Canonical Internal.tbDistrLatticeType.
Canonical Internal.cbDistrLatticeType.
Canonical Internal.ctbDistrLatticeType.

Lemma subsetEset {T} (X Y : set T) : (X <= Y)%O = (X `<=` Y) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma properEset  {T} (X Y : set T) : (X < Y)%O = (X `<` Y) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma subEset {T} (X Y : set T) : (X `\` Y)%O = (X `\` Y). Proof. by []. Qed.
Lemma complEset {T} (X Y : set T) : (~` X)%O = ~` X. Proof. by []. Qed.
Lemma botEset {T} (X Y : set T) : 0%O = @set0 T. Proof. by []. Qed.
Lemma topEset {T} (X Y : set T) : 1%O = @setT T. Proof. by []. Qed.

Lemma meetEset {T} (X Y : set T) : (X `&` Y)%O = (X `&` Y). Proof. by []. Qed.
Lemma joinEset {T} (X Y : set T) : (X `|` Y)%O = (X `|` Y). Proof. by []. Qed.

End Exports.
End SetOrder.
