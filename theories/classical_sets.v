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
(*                       set T == type of sets on T.                          *)
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
(*               is_subset1 A <-> A contains only 1 element.                  *)
(*                   is_fun f <-> for each a, f a contains only 1 element.    *)
(*                 is_total f <-> for each a, f a is non empty.               *)
(*              is_totalfun f <-> conjunction of is_fun and is_total.         *)
(*                   xget x0 P == point x in P if it exists, x0 otherwise;    *)
(*                                P must be a set on a choiceType.            *)
(*             fun_of_rel f0 f == function that maps x to an element of f x   *)
(*                                if there is one, to f0 x otherwise.         *)
(*                    F `#` G <-> intersections beween elements of F an G are *)
(*                                all non empty.                              *)
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
(* About the naming conventions in this file:                                 *)
(* - use T, T', T1, T2, etc., aT (domain type), rT (return type) for names of *)
(*   variables in Type (or choiceType/pointedType/porderType)                 *)
(*   + use the same suffix or prefix for the sets as their containing type    *)
(*     (e.g., A1 in T1, etc.)                                                 *)
(*   + as a consequence functions are rather of type aT -> rT                 *)
(* - use I, J when the type corresponds to an index                           *)
(* - sets are named A, B, C, D, etc., or Y when it is ostensibly an image set *)
(*   (i.e., of type set rT)                                                   *)
(* - indexed sets are rather named F                                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope classical_set_scope.

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
Reserved Notation "[ 'disjoint' A & B ]" (at level 0,
  format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").

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

Definition set T := T -> Prop.
(* we use fun x => instead of pred to prevent inE from working *)
(* we will then extend inE with in_setE to make this work      *)
Definition in_set T (A : set T) : pred T := (fun x => `[<A x>]).
Canonical set_predType T := @PredType T (set T) (@in_set T).

Lemma in_setE T (A : set T) x : x \in A = A x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Definition inE := (inE, in_setE).

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.

Definition mkset {T} (P : T -> Prop) : set T := P.
Arguments mkset _ _ _ /.

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.
Notation "[ 'set' E | x 'in' A ]" :=
  [set y | exists2 x, A x & E = y] : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  [set z | exists2 x, A x & exists2 y, B y & E = z] : classical_set_scope.

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).

Definition image f A : set rT := [set f a | a in A].
Definition preimage f Y : set T := [set t | Y (f t)].

Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setI A B := [set x | A x /\ B x].
Definition setU A B := [set x | A x \/ B x].
Definition nonempty A := exists a, A a.
Definition setC A := [set a | ~ A a].
Definition setD A B := [set x | A x /\ ~ B x].
Definition setM T1 T2 (A1 : set T1) (A2 : set T2) := [set z | A1 z.1 /\ A2 z.2].
Definition fst_set T1 T2 (A : set (T1 * T2)) := [set x | exists y, A (x, y)].
Definition snd_set T1 T2 (A : set (T1 * T2)) := [set y | exists x, A (x, y)].

Lemma mksetE (P : T -> Prop) x : [set x | P x] x = P x.
Proof. by []. Qed.

Definition bigsetI T I (P : set I) (F : I -> set T) :=
  [set a | forall i, P i -> F i a].
Definition bigsetU T I (P : set I) (F : I -> set T) :=
  [set a | exists2 i, P i & F i a].

Definition subset A B := forall t, A t -> B t.
Local Notation "A `<=` B" := (subset A B).

Definition proper A B := A `<=` B /\ ~ (B `<=` A).

End basic_definitions.
Arguments preimage T rT f Y / t.

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
Notation "[ 'disjoint' A & B ]" := (A `&` B == set0) : classical_set_scope.

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

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<` B" := (proper A B) : classical_set_scope.

Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image f A) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Lemma eq_set T (P Q : T -> Prop) : (forall x : T, P x = Q x) ->
  [set x | P x] = [set x | Q x].
Proof. by move=> /funext->. Qed.

Section basic_lemmas.
Context {T : Type}.
Implicit Types A B C D : set T.

Lemma predeqP A B : (A = B) <-> (forall x, A x <-> B x).
Proof. by rewrite predeqE. Qed.

Lemma eqEsubset A B : (A = B) = (A `<=>` B).
Proof.
rewrite propeqE; split => [->|[AB BA]]; [by split|].
by rewrite predeqE => t; split=> [/AB|/BA].
Qed.

Lemma seteqP A B : (A = B) <-> (A `<=>` B). Proof. by rewrite eqEsubset. Qed.

Lemma sub0set A : set0 `<=` A. Proof. by []. Qed.

Lemma setUCr A : A `|` ~` A = setT.
Proof.
by rewrite predeqE => t; split => // _; case: (pselect (A t)); [left|right].
Qed.

Lemma setC0 : ~` set0 = setT :> set T.
Proof. by rewrite predeqE; split => ?. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; rewrite funeqE => t; rewrite /setC; exact: notLR. Qed.

Lemma subsets_disjoint A B : (A `<=` B) <-> (A `&` ~` B = set0).
Proof.
split=> [AB|]; first by rewrite predeqE => t; split => // -[/AB].
rewrite predeqE => AB t At; move: (AB t) => [{}AB _].
by apply: contrapT => Bt; exact: AB.
Qed.

Lemma disjoints_subset A B : A `&` B = set0 <-> A `<=` ~` B.
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma setCT : ~` setT = set0 :> set T. Proof. by rewrite -setC0 setCK. Qed.

Lemma setDE A B : A `\` B = A `&` ~` B. Proof. by []. Qed.

Lemma setTD A : setT `\` A = ~` A.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma setDv A : A `\` A = set0.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma subset0 A : (A `<=` set0) = (A = set0).
Proof. by rewrite eqEsubset propeqE; split => [A0|[]//]; split. Qed.

Lemma set0P A : (A != set0) <-> (A !=set0).
Proof.
split=> [/negP A_neq0|[t tA]]; last by apply/negP => /eqP A0; rewrite A0 in tA.
apply: contrapT => /asboolPn/forallp_asboolPn A0; apply/A_neq0/eqP.
by rewrite eqEsubset; split.
Qed.

Lemma subset_nonempty A B : A `<=` B -> A !=set0 -> B !=set0.
Proof. by move=> sAB [x Ax]; exists x; apply: sAB. Qed.

Lemma subset_trans B A C : A `<=` B -> B `<=` C -> A `<=` C.
Proof. by move=> sAB sBC ? ?; apply/sBC/sAB. Qed.

Lemma subsetC A B : A `<=` B -> ~` B `<=` ~` A.
Proof. by move=> sAB ? nBa ?; apply/nBa/sAB. Qed.

Lemma subsetU A B C : A `<=` C -> B `<=` C -> A `|` B `<=` C.
Proof. by move=> sAC sBC t; apply: or_ind; [apply: sAC|apply: sBC]. Qed.

Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) /\ (C `<=` A)).
Proof.
rewrite propeqE; split => [|[BA CA] x]; last by case; [exact: BA | exact: CA].
by move=> sBC_A; split=> x ?; apply sBC_A; [left | right].
Qed.

Lemma setIidPl A B : A `&` B = A <-> A `<=` B.
Proof.
rewrite predeqE; split=> [AB t /AB [] //|AB t].
by split=> [[]//|At]; split=> //; exact: AB.
Qed.

Lemma setUidPl A B : A `|` B = A <-> B `<=` A.
Proof.
split=> [<- ? ?|BA]; first by right.
rewrite predeqE => t; split=> [[//|/BA//]|?]; by left.
Qed.

Lemma subsetI A B C : (A `<=` B `&` C) = ((A `<=` B) /\ (A `<=` C)).
Proof.
rewrite propeqE; split=> [H|[y z ??]]; split; by [move=> ?/H[]|apply y|apply z].
Qed.

Lemma setDidPl A B : A `\` B = A <-> A `&` B = set0.
Proof.
rewrite setDE disjoints_subset predeqE; split => [AB t|AB t].
by rewrite -AB => -[].
by split=> [[]//|At]; move: (AB t At).
Qed.

Lemma subIset A B C : A `<=` C \/ B `<=` C -> A `&` B `<=` C.
Proof. case => H a; by [move=> [/H] | move=> [_ /H]]. Qed.

Lemma subsetI_neq0 A B C D :
  A `<=` B -> C `<=` D -> A `&` C !=set0 -> B `&` D !=set0.
Proof. by move=> AB CD [x [/AB Bx /CD Dx]]; exists x. Qed.

Lemma subsetI_eq0 A B C D :
  A `<=` B -> C `<=` D -> B `&` D = set0 -> A `&` C = set0.
Proof. by move=> AB /(subsetI_neq0 AB); rewrite -!set0P => /contra_eq. Qed.

Lemma setD_eq0 A B : (A `\` B = set0) = (A `<=` B).
Proof.
rewrite propeqE; split=> [ADB0 a|sAB].
  by apply: contraPP => nBa xA; rewrite -[False]/(set0 a) -ADB0.
by rewrite predeqE => ?; split=> // - [?]; apply; apply: sAB.
Qed.

Lemma properEneq A B : (A `<` B) = (A != B /\ A `<=` B).
Proof.
rewrite /proper andC propeqE; split => [[BA AB]|[/eqP]].
  by split => //; apply/negP; apply: contra_not BA => /eqP ->.
by rewrite eqEsubset => AB BA; split => //; exact: contra_not AB.
Qed.

Lemma nonsubset A B : ~ (A `<=` B) -> A `&` ~` B !=set0.
Proof. by rewrite -setD_eq0 setDE -set0P => /eqP. Qed.

Lemma setIC A B : A `&` B = B `&` A.
Proof. by rewrite predeqE => ?; split=> [[]|[]]. Qed.

Lemma setIS A B C : A `<=` B -> C `&` A `<=` C `&` B.
Proof. by move=> sAB t [Ct At]; split => //; exact: sAB. Qed.

Lemma setSI A B C : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(setIC C); apply setIS. Qed.

Lemma setSD A B C : A `<=` B -> A `\` C `<=` B `\` C.
Proof. by rewrite !setDE; apply: setSI. Qed.

Lemma setISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(@setSI _ _ B) /subset_trans sAC /(@setIS _ _ C) /sAC. Qed.

Lemma setIT A : A `&` setT = A.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setTI A : setT `&` A = A.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setI0 A : A `&` set0 = set0.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma set0I A : set0 `&` A = set0.
Proof. by rewrite setIC setI0. Qed.

Lemma setICl A : ~` A `&` A = set0.
Proof. by rewrite predeqE => ?; split => // -[]. Qed.

Lemma setICr A : A `&` ~` A = set0.
Proof. by rewrite setIC setICl. Qed.

Lemma setIA A B C : A `&` (B `&` C) = A `&` B `&` C.
Proof. by rewrite predeqE => ?; split=> [[? []]|[[]]]. Qed.

Lemma setICA A B C : A `&` (B `&` C) = B `&` (A `&` C).
Proof. by rewrite setIA [A `&` _]setIC -setIA. Qed.

Lemma setIAC A B C : A `&` B `&` C = A `&` C `&` B.
Proof. by rewrite setIC setICA setIA. Qed.

Lemma setIACA A B C D : A `&` B `&` (C `&` D) = A `&` C `&` (B `&` D).
Proof. by rewrite -setIA [B `&` _]setICA setIA. Qed.

Lemma setIid A : A `&` A = A.
Proof. by rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(setIC A) setIIl. Qed.

Lemma setUA : associative (@setU T).
Proof. move=> p q r; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUid : idempotent (@setU T).
Proof. move=> p; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUC : commutative (@setU T).
Proof. move=> p q; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma set0U A : set0 `|` A = A.
Proof. by rewrite predeqE => t; split; [case|right]. Qed.

Lemma setU0 A : A `|` set0 = A.
Proof. by rewrite predeqE => t; split; [case|left]. Qed.

Lemma setTU A : setT `|` A = setT.
Proof. by rewrite predeqE => t; split; [case|left]. Qed.

Lemma setUT A  : A `|` setT = setT.
Proof. by rewrite predeqE => t; split; [case|right]. Qed.

Lemma setU_eq0 A B : (A `|` B = set0) = ((A = set0) /\ (B = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setUCl A : ~` A `|` A = setT. Proof. by rewrite setUC setUCr. Qed.

Lemma setCS A B : (~` A `<=` ~` B) = (B `<=` A).
Proof.
rewrite propeqE; split => [|BA].
  by move/subsets_disjoint; rewrite setCK setIC => /subsets_disjoint.
by apply/subsets_disjoint; rewrite setCK setIC; apply/subsets_disjoint.
Qed.

Lemma setDT A : A `\` setT = set0.
Proof. by rewrite setDE setCT setI0. Qed.

Lemma set0D A : set0 `\` A = set0.
Proof. by rewrite setDE set0I. Qed.

Lemma setD0 A : A `\` set0 = A.
Proof. by rewrite setDE setC0 setIT. Qed.

Lemma setDS A B C : A `<=` B -> C `\` B `<=` C `\` A.
Proof. by rewrite !setDE -setCS; apply: setIS. Qed.

Lemma setDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. by move=> /(@setSD _ _ B) /subset_trans sAC /(@setDS _ _ C) /sAC. Qed.

Lemma setCU A B : ~`(A `|` B) = ~` A `&` ~` B.
Proof.
rewrite predeqE => z.
by apply: asbool_eq_equiv; rewrite asbool_and !asbool_neg asbool_or negb_or.
Qed.

Lemma setCI A B : ~` (A `&` B) = ~` A `|` ~` B.
Proof. by rewrite -[in LHS](setCK A) -[in LHS](setCK B) -setCU setCK. Qed.

Lemma setDUr A B C : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Proof. by rewrite !setDE setCU setIIr. Qed.

Lemma setIUl : left_distributive (@setI T) (@setU T).
Proof.
move=> A B C; rewrite predeqE => t; split.
  by move=> [[At|Bt] Ct]; [left|right].
by move=> [[At Ct]|[Bt Ct]]; split => //; [left|right].
Qed.

Lemma setIUr : right_distributive (@setI T) (@setU T).
Proof. by move=> A B C; rewrite ![A `&` _]setIC setIUl. Qed.

Lemma setUIl : left_distributive (@setU T) (@setI T).
Proof.
move=> A B C; rewrite predeqE => t; split.
  by move=> [[At Bt]|Ct]; split; by [left|right].
by move=> [[At|Ct] [Bt|Ct']]; by [left|right].
Qed.

Lemma setUIr : right_distributive (@setU T) (@setI T).
Proof. by move=> A B C; rewrite ![A `|` _]setUC setUIl. Qed.

Lemma setUK A B : (A `|` B) `&` A = A.
Proof. by rewrite eqEsubset; split => [t []//|t ?]; split => //; left. Qed.

Lemma setKU A B : A `&` (B `|` A) = A.
Proof. by rewrite eqEsubset; split => [t []//|t ?]; split => //; right. Qed.

Lemma setIK A B : (A `&` B) `|` A = A.
Proof. by rewrite eqEsubset; split => [t [[]//|//]|t At]; right. Qed.

Lemma setKI A B : A `|` (B `&` A) = A.
Proof. by rewrite eqEsubset; split => [t [//|[]//]|t At]; left. Qed.

Lemma setDUl A B C : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
Proof. by rewrite !setDE setIUl. Qed.

Lemma setIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by rewrite !setDE setIA. Qed.

Lemma setDD A B : A `\` (A `\` B) = A `&` B.
Proof. by rewrite 2!setDE setCI setCK setIUr setICr set0U. Qed.

End basic_lemmas.

Lemma mkset_nil (T : choiceType) : [set x | x \in [::]] = @set0 T.
Proof. by rewrite predeqP. Qed.

(* TODO: other lemmas that relate fset and classical sets *)
Lemma fdisjoint_cset (T : choiceType) (A B : {fset T}) :
  [disjoint A & B]%fset = [disjoint [set x | x \in A] & [set x | x \in B]].
Proof.
rewrite -fsetI_eq0; apply/idP/idP; apply: contraLR.
by move=> /set0P[t [tA tB]]; apply/fset0Pn; exists t; rewrite inE; apply/andP.
by move=> /fset0Pn[t]; rewrite inE => /andP[tA tB]; apply/set0P; exists t.
Qed.

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

Section image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma imageP f A a : A a -> (f @` A) (f a). Proof. by exists a. Qed.

Lemma image_inj f A a : injective f -> (f @` A) (f a) = A a.
Proof.
by move=> f_inj; rewrite propeqE; split => [[b Ab /f_inj <-]|/(imageP f)//].
Qed.

Lemma image_id A : id @` A = A.
Proof. by rewrite eqEsubset; split => a; [case=> /= x Ax <-|exists a]. Qed.

Lemma image_setU f A B : f @` (A `|` B) = f @` A `|` f @` B.
Proof.
rewrite eqEsubset; split => b.
- by case=> a [] Ha <-; [left | right]; apply imageP.
- by case=> -[] a Ha <-; apply imageP; [left | right].
Qed.

Lemma image_set0 f : f @` set0 = set0.
Proof. by rewrite eqEsubset; split => b // -[]. Qed.

Lemma image_set0_set0 A f : f @` A = set0 -> A = set0.
Proof.
move=> fA0; rewrite predeqE => t; split => // At.
by have : set0 (f t) by rewrite -fA0; exists t.
Qed.

Lemma image_set1 f t : f @` [set t] = [set f t].
Proof. by rewrite eqEsubset; split => [b [a' -> <-] //|b ->]; exact/imageP. Qed.

Lemma subset_set1 A a : A `<=` [set a] -> A = set0 \/ A = [set a].
Proof.
move=> Aa; have [|/set0P/negP/negPn/eqP->] := pselect (A !=set0); [|by left].
by case=> t At; right; rewrite eqEsubset; split => // ? ->; rewrite -(Aa _ At).
Qed.

Lemma sub_image_setI f A B : f @` (A `&` B) `<=` f @` A `&` f @` B.
Proof. by move=> b [x [Aa Ba <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {f A B} t _.

Lemma nonempty_image f A : f @` A !=set0 -> A !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof. by move=> AB _ [a Aa <-]; exists a => //; apply/AB. Qed.

Lemma preimage_set0 f : f @^-1` set0 = set0. Proof. exact/predeqP. Qed.

Lemma nonempty_preimage f Y : f @^-1` Y !=set0 -> Y !=set0.
Proof. by case=> [t ?]; exists (f t). Qed.

Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Proof. by move=> a Aa; exists a. Qed.

Lemma image_preimage_subset f Y : f @` (f @^-1` Y) `<=` Y.
Proof. by move=> _ [t /= Yft <-]. Qed.

Lemma image_preimage f Y : f @` setT = setT -> f @` (f @^-1` Y) = Y.
Proof.
move=> fsurj; rewrite predeqE => x; split; first by move=> [?? <-].
move=> Ax; have : setT x by [].
rewrite -fsurj => - [y _ fy_eqx]; exists y => //.
by rewrite /preimage/= fy_eqx.
Qed.

Lemma preimage_setU f Y1 Y2 : f @^-1` (Y1 `|` Y2) = f @^-1` Y1 `|` f @^-1` Y2.
Proof. exact/predeqP. Qed.

Lemma preimage_setI f Y1 Y2 : f @^-1` (Y1 `&` Y2) = f @^-1` Y1 `&` f @^-1` Y2.
Proof. exact/predeqP. Qed.

Lemma preimage_setC f Y : ~` (f @^-1` Y) = f @^-1` (~` Y).
Proof. by rewrite predeqE => a; split=> nAfa ?; apply: nAfa. Qed.

Lemma preimage_subset f Y1 Y2 : Y1 `<=` Y2 -> f @^-1` Y1 `<=` f @^-1` Y2.
Proof. by move=> Y12 t /Y12. Qed.

Lemma nonempty_preimage_setI f Y1 Y2 :
  (f @^-1` (Y1 `&` Y2)) !=set0 <-> (f @^-1` Y1 `&` f @^-1` Y2) !=set0.
Proof. by split; case=> t ?; exists t. Qed.

End image_lemmas.
Arguments image_inj {aT rT} [f A a].
Arguments sub_image_setI {aT rT f A B} t _.

Lemma image_comp T1 T2 T3 (f : T1 -> T2) (g : T2 -> T3) A :
  g @` (f @` A) = (g \o f) @` A.
Proof.
by rewrite eqEsubset; split => [x [b [a Aa] <- <-]|x [a Aa] <-];
  [apply/imageP |apply/imageP/imageP].
Qed.

Section bigop_lemmas.
Context {T I : Type}.
Implicit Types (A : set T) (i : I) (P : set I) (F G : I -> set T).

Lemma bigcup_sup i P F : P i -> F i `<=` \bigcup_(j in P) F j.
Proof. by move=> Pi a Fia; exists i. Qed.

Lemma setI_bigcapl P F A :
  P !=set0 -> \bigcap_(i in P) F i `&` A = \bigcap_(i in P) (F i `&` A).
Proof.
move=> [i Di]; rewrite predeqE => a; split=> [[Ifa Aa] j Dj|IfIAa].
  by split=> //; apply: Ifa.
by split=> [j /IfIAa [] | ] //; have /IfIAa [] := Di.
Qed.

Lemma bigcup_set0 F : \bigcup_(i in set0) F i = set0.
Proof. by rewrite eqEsubset; split => a // []. Qed.

Lemma bigcup_set1 F i : \bigcup_(j in [set i]) F j = F i.
Proof. by rewrite eqEsubset; split => ? => [[] ? -> //|]; exists i. Qed.

Lemma bigcup_nonempty P F :
  (\bigcup_(i in P) F i !=set0) <-> exists2 i, P i & F i !=set0.
Proof.
split=> [[t [i ? ?]]|[j ? [t ?]]]; by [exists i => //; exists t| exists t, j].
Qed.

Lemma bigcup0 P F :
  (forall i, P i -> F i = set0) -> \bigcup_(i in P) F i = set0.
Proof. by move=> PF; rewrite predeqE => t; split => // -[i /PF ->]. Qed.

Lemma bigcup0P P F :
  (\bigcup_(i in P) F i = set0) <-> (P = set0) \/ (forall i, P i -> F i = set0).
Proof.
split=> [|[->|]]; [|by rewrite bigcup_set0|exact: bigcup0].
apply: contraPP => /not_orP[/eqP/set0P[i Pi]].
move=> /existsNP[j /not_implyP[Pj /eqP/set0P[t Fit]]].
 by apply/eqP/set0P; exists t, j.
Qed.

Lemma subset_bigcup_r P : {homo (fun x : I -> set T => \bigcup_(i in P) x i)
  : F G / [set F i | i in P] `<=` [set G i | i in P] >-> F `<=` G}.
Proof.
move=> F G FG t [i Pi Fit]; have := FG (F i).
by move=> /(_ (ex_intro2 _ _ _ Pi erefl))[j Pj ji]; exists j => //; rewrite ji.
Qed.

Lemma eqbigcup_r P F G : (forall i, P i -> F i = G i) ->
  \bigcup_(i in P) F i = \bigcup_(i in P) G i.
Proof.
by move=> FG; rewrite eqEsubset; split; apply: subset_bigcup_r;
  move=> A [i ? <-]; exists i => //; rewrite FG.
Qed.

Lemma setC_bigcup P F : ~` (\bigcup_(i in P) F i) = \bigcap_(i in P) ~` F i.
Proof.
by rewrite eqEsubset; split => [t PFt i Pi ?|t PFt [i Pi ?]];
  [apply PFt; exists i | exact: (PFt _ Pi)].
Qed.

Lemma setC_bigcap P F : ~` (\bigcap_(i in P) (F i)) = \bigcup_(i in P) ~` F i.
Proof.
rewrite eqEsubset; split=> [| t [i Pi Fit] /(_ _ Pi)//].
by move=> t /existsNP[i /not_implyP[Pi Fit]]; exists i.
Qed.

End bigop_lemmas.

Lemma bigcup_mkset (T : choiceType) U (s : seq T) (f : T -> set U) :
  \bigcup_(t in [set x | x \in s]) (f t) = \big[setU/set0]_(t <- s) (f t).
Proof.
elim: s => [/=|h s ih]; first by rewrite mkset_nil bigcup_set0 big_nil.
rewrite big_cons -ih predeqE => u; split => [[t]|[?|[t ts ?]]].
- by rewrite /mkset inE => /orP[/eqP-> ?|? ?]; [left|right; exists t].
- by exists h => //; rewrite /mkset mem_head.
- by exists t => //; rewrite /mkset inE ts orbT.
Qed.

Section bigop_nat_lemmas.
Context {T : Type}.
Implicit Types (A : set T) (F : nat -> set T).

Lemma bigcup_recl n F :
  \bigcup_i F i = \big[setU/set0]_(i < n) F i `|` \bigcup_i F (n + i)%N.
Proof.
elim: n => [|n ih]; first by rewrite big_ord0 set0U.
rewrite ih big_ord_recr /= -setUA; congr (_ `|` _).
rewrite predeqE => t; split => [[[|m] _ At]|[At|[i _ At]]].
- by left; rewrite addn0 in At.
  by right; exists m => //; rewrite addSnnS.
- by exists 0%N => //; rewrite addn0.
  by exists i.+1 => //; rewrite -addSnnS.
Qed.

Lemma bigcup_distrr F (P : set nat) A :
  A `&` \bigcup_(i in P) (F i) = \bigcup_(i in P) (A `&` F i).
Proof.
rewrite predeqE => t; split => [[At [k ? ?]]|[k ? [At ?]]];
  by [exists k |split => //; exists k].
Qed.

Lemma bigcup_distrl F (P : set nat) A :
  \bigcup_(i in P) F i `&` A = \bigcup_(i in P) (F i `&` A).
Proof.
by rewrite predeqE => t; split => [[[n ? Ant ?]]|[n ? [Ant ?]]];
  [exists n|split => //; exists n].
Qed.

Lemma bigcup_ord n F :
  \big[setU/set0]_(i < n) F i = \bigcup_(i in [set k | (k < n)%N]) F i.
Proof.
elim: n => [|n IHn] in F *; first by rewrite big_ord0 predeqE; split => -[].
rewrite big_ord_recl /= (IHn (fun i => F i.+1)) predeqE => x; split.
  by move=> [F0|[i FS]]; [exists 0%N|exists i.+1].
by move=> [[|i] Fi]; [left|right; exists i].
Qed.

Lemma subset_bigsetU m n F : (m <= n)%N ->
  \big[setU/set0]_(i < m) F i `<=` \big[setU/set0]_(i < n) F i.
Proof.
rewrite !bigcup_ord => mn x [i im ?]; exists i => //.
by rewrite /mkset (leq_trans im).
Qed.

Lemma bigcap_ord n F :
 \big[setI/setT]_(i < n) F i = \bigcap_(i in [set k | (k < n)%N]) F i.
Proof.
elim: n => [|n IHn] in F *; first by rewrite big_ord0 predeqE.
rewrite big_ord_recl /= (IHn (fun i => F i.+1)) predeqE => x; split.
  by move=> [F0 FS] [|i]// /FS.
by move=> FP; split => [|i i_lt]; apply: FP.
Qed.

End bigop_nat_lemmas.

Lemma preimage_bigcup {aT rT I} (P : set I) (f : aT -> rT) A :
  f @^-1` (\bigcup_ (i in P) A i) = \bigcup_(i in P) (f @^-1` A i).
Proof. exact/predeqP. Qed.

Lemma preimage_bigcap {aT rT I} (P : set I) (f : aT -> rT) F :
  f @^-1` (\bigcap_ (i in P) F i) = \bigcap_(i in P) (f @^-1` F i).
Proof. exact/predeqP. Qed.

Lemma setM0 T1 T2 (A1 : set T1) : A1 `*` set0 = set0 :> set (T1 * T2).
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma set0M T1 T2 (A2 : set T2) : set0 `*` A2 = set0 :> set (T1 * T2).
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma setMT {T1 T2} : setT `*` setT = setT :> set (T1 * T2).
Proof. exact/predeqP. Qed.

Definition is_subset1 {T} (A : set T) := forall x y, A x -> A y -> x = y.
Definition is_fun {T1 T2} (f : T1 -> T2 -> Prop) := Logic.all (is_subset1 \o f).
Definition is_total {T1 T2} (f : T1 -> T2 -> Prop) := Logic.all (nonempty \o f).
Definition is_totalfun {T1 T2} (f : T1 -> T2 -> Prop) :=
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

Definition fun_of_rel {aT} {rT : choiceType} (f0 : aT -> rT) (f : aT -> rT -> Prop) :=
  fun x => xget (f0 x) (f x).

Lemma fun_of_relP {aT} {rT : choiceType} (f : aT -> rT -> Prop) (f0 : aT -> rT) a :
  f a !=set0 -> f a (fun_of_rel f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_rel; apply: xgetI fab. Qed.

Lemma fun_of_rel_uniq {aT} {rT : choiceType}
    (f : aT -> rT -> Prop) (f0 : aT -> rT) a :
  is_subset1 (f a) -> forall b, f a b ->  fun_of_rel f0 f a = b.
Proof. by move=> fa1 b /xget_subset1 xgeteq; rewrite /fun_of_rel xgeteq. Qed.

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

Section partitions.

Definition trivIset T I (D : set I) (F : I -> set T) :=
  forall i j : I, D i -> D j -> F i `&` F j !=set0 -> i = j.

Lemma trivIsetP {T} {I : eqType} {D : set I} {F : I -> set T} :
  trivIset D F <->
  forall i j : I, D i -> D j -> i != j -> F i `&` F j = set0.
Proof.
split=> tDF i j Di Dj; first by apply: contraNeq => /set0P/tDF->.
by move=> /set0P; apply: contraNeq => /tDF->.
Qed.

Lemma trivIset_bigUI T (D : {pred nat}) (F : nat -> set T) : trivIset D F ->
  forall n m, D m -> n <= m -> \big[setU/set0]_(i < n | D i) F i `&` F m = set0.
Proof.
move=> /trivIsetP tA; elim => [|n IHn] m Dm.
  by move=> _; rewrite big_ord0 set0I.
move=> lt_nm; rewrite big_mkcond/= big_ord_recr -big_mkcond/=.
rewrite setIUl IHn 1?ltnW// set0U.
by case: ifPn => [Dn|NDn]; rewrite ?set0I// tA// ltn_eqF.
Qed.

Lemma trivIset_setI T I D (F : I -> set T) X :
  trivIset D F -> trivIset D (fun i => X `&` F i).
Proof.
move=> tDF i j Di Dj; rewrite setIACA setIid => -[x [_ Fijx]].
by apply: tDF => //; exists x.
Qed.

Definition cover T I D (F : I -> set T) := \bigcup_(i in D) F i.

Definition partition T I D (F : I -> set T) (A : set T) :=
  [/\ cover D F = A, trivIset D F & forall i, D i -> F i !=set0].

Definition pblock_index T (I : pointedType) D (F : I -> set T) (x : T) :=
  get (fun i => D i /\ F i x).

Definition pblock T (I : pointedType) D (F : I -> set T) (x : T) :=
  F (pblock_index D F x).

(* TODO: theory of trivIset, cover, partition, pblock_index and pblock *)

Lemma trivIset_sets T I D (F : I -> set T) :
  trivIset D F -> trivIset [set F i | i in D] id.
Proof. by move=> DF A B [i Di <-{A}] [j Dj <-{B}] /DF ->. Qed.

Lemma trivIset_restr T I D' D (F : I -> set T) :
(*  D `<=` D' -> (forall i, D i -> ~ D' i -> F i !=set0) ->*)
  D `<=` D' -> (forall i, D' i -> ~ D i -> F i = set0) ->
  trivIset D F = trivIset D' F.
Proof.
move=> DD' DD'F.
rewrite propeqE; split=> [DF i j D'i D'j FiFj0|D'F i j Di Dj FiFj0].
  have [Di|Di] := pselect (D i); last first.
    by move: FiFj0; rewrite (DD'F i) // set0I => /set0P; rewrite eqxx.
  have [Dj|Dj] := pselect (D j).
  - exact: DF.
  - by move: FiFj0; rewrite (DD'F j) // setI0 => /set0P; rewrite eqxx.
by apply D'F => //; apply DD'.
Qed.

Lemma perm_eq_trivIset {T : eqType} (s1 s2 : seq (set T)) : perm_eq s1 s2 ->
  trivIset setT (fun i => nth set0 s1 i) ->
  trivIset setT (fun i => nth set0 s2 i).
Proof.
rewrite perm_sym => /(perm_iotaP set0)[s ss1 s12] /trivIsetP /(_ _ _ I I) ts1.
apply/trivIsetP => i j _ _ ij.
rewrite {}s12 {s2}; have [si|si] := ltnP i (size s); last first.
  by rewrite (nth_default set0) ?size_map// set0I.
rewrite (nth_map O) //; have [sj|sj] := ltnP j (size s); last first.
  by rewrite (nth_default set0) ?size_map// setI0.
by rewrite  (nth_map O) // ts1 // nth_uniq // (perm_uniq ss1) iota_uniq.
Qed.

End partitions.

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
Implicit Types A : set T.

Definition ubound A : set T := [set z | forall y, A y -> (y <= z)%O].
Definition lbound A : set T := [set z | forall y, A y -> (z <= y)%O].

Lemma ubP A x : (forall y, A y -> (y <= x)%O) <-> ubound A x.
Proof. by []. Qed.

Lemma lbP A x : (forall y, A y -> (x <= y)%O) <-> lbound A x.
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

Lemma ub_lb_ub A x y : ubound A y -> lbound (ubound A) x -> (x <= y)%O.
Proof. by move=> Ay; apply. Qed.

Lemma lb_ub_lb A x y : lbound A y -> ubound (lbound A) x -> (y <= x)%O.
Proof. by move=> Ey; apply. Qed.

(* down set (i.e., generated order ideal) *)
(* i.e. down A := { x | exists y, y \in A /\ x <= y} *)
Definition down A : set T := [set x | exists y, A y /\ (x <= y)%O].

(* Real set supremum and infimum existence condition. *)
Definition has_ubound A := ubound A !=set0.
Definition has_sup A := A !=set0 /\ has_ubound A.
Definition has_lbound A := lbound A !=set0.
Definition has_inf A := A !=set0 /\ has_lbound A.

Lemma subset_has_lbound A B : A `<=` B -> has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma subset_has_ubound A B : A `<=` B -> has_ubound B -> has_ubound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma has_ub_set1 x : has_ubound [set x].
Proof. by exists x; rewrite ub_set1. Qed.

Lemma downP A x : (exists2 y, A y & (x <= y)%O) <-> down A x.
Proof. by split => [[y Ay xy]|[y [Ay xy]]]; [exists y| exists y]. Qed.

Definition supremums A := ubound A `&` lbound (ubound A).

Lemma supremums_set1 x : supremums [set x] = [set x].
Proof.
rewrite /supremums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite ub_set1|exact: lb_ub_refl].
by rewrite ub_set1 => xy /lb_ub_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_supremums A : is_subset1 (supremums A).
Proof.
move=> x y [Ex xE] [Ey yE]; apply/eqP.
by rewrite eq_le (ub_lb_ub Ex yE) (ub_lb_ub Ey xE).
Qed.

Definition supremum (x0 : T) A :=
  if pselect (A !=set0) then xget x0 (supremums A) else x0.

Definition infimums A := lbound A `&` ubound (lbound A).

Definition infimum (x0 : T) A :=
  if pselect (A !=set0) then xget x0 (infimums A) else x0.

Lemma infimums_set1 x : infimums [set x] = [set x].
Proof.
rewrite /infimums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite lb_set1|apply ub_lb_refl].
by rewrite lb_set1 => xy /ub_lb_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_infimums A : is_subset1 (infimums A).
Proof.
move=> x y [Ax xA] [Ay yA]; apply/eqP.
by rewrite eq_le (lb_ub_lb Ax yA) (lb_ub_lb Ay xA).
Qed.

End UpperLowerTheory.

Section UpperLowerOrderTheory.
Import Order.TTheory.
Variables (d : unit) (T : orderType d).
Implicit Types A : set T.

Lemma ge_supremum_Nmem x0 A t :
  supremums A !=set0 -> A t -> (supremum x0 A >= t)%O.
Proof.
case=> x Ax; rewrite /supremum.
case: pselect => /= [_ | /set0P/negP/negPn/eqP -> //].
by case: xgetP => [y yA [uAy _]|/(_ x) //]; exact: uAy.
Qed.

Lemma le_infimum_Nmem x0 A t :
  infimums A !=set0 -> A t -> (infimum x0 A <= t)%O.
Proof.
case=> x Ex; rewrite /infimum.
case: pselect => /= [_ | /set0P/negP/negPn/eqP -> //].
by case: xgetP => [y yE [uEy _]|/(_ x) //]; exact: uEy.
Qed.

End UpperLowerOrderTheory.

Lemma nat_supremums_neq0 (A : set nat) : ubound A !=set0 -> supremums A !=set0.
Proof.
case => /=; elim => [A0|n ih]; first by exists O.
case: (pselect (ubound A n)) => [/ih //|An {ih}] An1.
exists n.+1; split => // m Am; case/existsNP : An => k /not_implyP[Ak /negP].
rewrite -Order.TotalTheory.ltNge => kn.
by rewrite (Order.POrderTheory.le_trans _ (Am _ Ak)).
Qed.

(** ** Intersection of classes of set *)

Definition meets T (F G : set (set T)) :=
  forall A B, F A -> G B -> A `&` B !=set0.

Reserved Notation "F `#` G"
 (at level 48, left associativity, format "F  `#`  G").

Notation "F `#` G" := (meets F G) : classical_set_scope.

Section meets.

Lemma meetsC T (F G : set (set T)) : F `#` G = G `#` F.
Proof.
gen have sFG : F G / F `#` G -> G `#` F.
  by move=> FG B A => /FG; rewrite setIC; apply.
by rewrite propeqE; split; apply: sFG.
Qed.

Lemma sub_meets T (F F' G G' : set (set T)) :
  F `<=` F' -> G `<=` G' -> F' `#` G' -> F `#` G.
Proof. by move=> sF sG FG A B /sF FA /sG GB; apply: (FG A B). Qed.

Lemma meetsSr T (F G G' : set (set T)) :
  G `<=` G' -> F `#` G' -> F `#` G.
Proof. exact: sub_meets. Qed.

Lemma meetsSl T (G F F' : set (set T)) :
  F `<=` F' -> F' `#` G -> F `#` G.
Proof. by move=> /sub_meets; apply. Qed.

End meets.

Fact set_display : unit. Proof. by []. Qed.

Module SetOrder.
Module Internal.
Section SetOrder.

Context {T : Type}.
Implicit Types A B : set T.

Lemma le_def A B : `[< A `<=` B >] = (A `&` B == A).
Proof. by apply/asboolP/eqP; rewrite setIidPl. Qed.

Lemma lt_def A B : `[< A `<` B >] = (B != A) && `[< A `<=` B >].
Proof.
apply/idP/idP => [/asboolP|/andP[BA /asboolP AB]]; rewrite properEneq eq_sym;
  by [move=> [] -> /asboolP|apply/asboolP].
Qed.

Fact SetOrder_joinKI B A : A `&` (A `|` B) = A.
Proof. by rewrite setUC setKU. Qed.

Fact SetOrder_meetKU B A : A `|` (A `&` B) = A.
Proof. by rewrite setIC setKI. Qed.

Definition orderMixin := @MeetJoinMixin _ _ (fun A B => `[<proper A B>]) setI
  setU le_def lt_def (@setIC _) (@setUC _) (@setIA _) (@setUA _) SetOrder_joinKI
  SetOrder_meetKU (@setIUl _) setIid.

Local Canonical porderType := POrderType set_display (set T) orderMixin.
Local Canonical latticeType := LatticeType (set T) orderMixin.
Local Canonical distrLatticeType := DistrLatticeType (set T) orderMixin.

Fact SetOrder_sub0set A : (set0 <= A)%O.
Proof. by apply/asboolP; apply: sub0set. Qed.

Fact SetOrder_setTsub A : (A <= setT)%O.
Proof. exact/asboolP. Qed.

Local Canonical bLatticeType :=
  BLatticeType (set T) (Order.BLattice.Mixin  SetOrder_sub0set).
Local Canonical tbLatticeType :=
  TBLatticeType (set T) (Order.TBLattice.Mixin SetOrder_setTsub).
Local Canonical bDistrLatticeType := [bDistrLatticeType of set T].
Local Canonical tbDistrLatticeType := [tbDistrLatticeType of set T].

Lemma subKI A B : B `&` (A `\` B) = set0.
Proof. by rewrite setDE setICA setICr setI0. Qed.

Lemma joinIB A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite setDE -setIUr setUCr setIT. Qed.

Local Canonical cbDistrLatticeType := CBDistrLatticeType (set T)
  (@CBDistrLatticeMixin _ _ (fun A B => A `\` B) subKI joinIB).

Local Canonical ctbDistrLatticeType := CTBDistrLatticeType (set T)
  (@CTBDistrLatticeMixin _ _ _ (fun A => ~` A) (fun x => esym (setTD x))).

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

Context {T : Type}.
Implicit Types A B : set T.

Lemma subsetEset A B : (A <= B)%O = (A `<=` B) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma properEset A B : (A < B)%O = (A `<` B) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma subEset A B : (A `\` B)%O = (A `\` B). Proof. by []. Qed.

Lemma complEset A : (~` A)%O = ~` A. Proof. by []. Qed.

Lemma botEset : 0%O = @set0 T. Proof. by []. Qed.

Lemma topEset : 1%O = @setT T. Proof. by []. Qed.

Lemma meetEset A B : (A `&` B)%O = (A `&` B). Proof. by []. Qed.

Lemma joinEset A B : (A `|` B)%O = (A `|` B). Proof. by []. Qed.

Lemma subsetPset A B : reflect (A `<=` B) (A <= B)%O.
Proof. by apply: (iffP idP); rewrite subsetEset. Qed.

Lemma properPset A B : reflect (A `<` B) (A < B)%O.
Proof. by apply: (iffP idP); rewrite properEset. Qed.

End Exports.
End SetOrder.
Export SetOrder.Exports.
