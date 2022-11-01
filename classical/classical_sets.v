(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import ssrint interval.
Require Import mathcomp_extra boolp.

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
(*                     range f == the range of f, i.e. [set f x | x in setT]  *)
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
(*                    [set~ a] == complement of [set a].                      *)
(*                     A `\` B == complement of B in A.                       *)
(*                      A `\ a == A deprived of a.                            *)
(*                        `I_n := [set k | k < n]                             *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P.                          *)
(*           \bigcup_(i : T) F == union of the family F indexed on T.         *)
(*           \bigcup_(i < n) F := \bigcup_(i in `I_n) F                       *)
(*                 \bigcup_i F == same as before with T left implicit.        *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P.                  *)
(*           \bigcap_(i : T) F == union of the family F indexed on T.         *)
(*           \bigcap_(i < n) F := \bigcap_(i in `I_n) F                       *)
(*                 \bigcap_i F == same as before with T left implicit.        *)
(*                smallest C G := \bigcap_(A in [set M | C M /\ G `<=` M]) A  *)
(*                   A `<=` B <-> A is included in B.                         *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A.     *)
(*                   f @^-1` A == preimage of A by f.                         *)
(*                      f @` A == image of A by f. Notation for `image A f`.  *)
(*                    A !=set0 := exists x, A x.                              *)
(*                    [set` p] == a classical set corresponding to the        *)
(*                                predType p                                  *)
(*                     `[a, b] := [set` `[a, b]], i.e., a classical set       *)
(*                                corresponding to the interval `[a, b].      *)
(*                     `]a, b] := [set` `]a, b]]                              *)
(*                     `[a, b[ := [set` `[a, b[]                              *)
(*                     `]a, b[ := [set` `]a, b[]                              *)
(*                   `]-oo, b] := [set` `]-oo, b]]                            *)
(*                   `]-oo, b[ := [set` `]-oo, b[]                            *)
(*                   `[a, +oo[ := [set` `[a, +oo[]                            *)
(*                   `]a, +oo[ := [set` `]a, +oo[]                            *)
(*                 `]-oo, +oo[ := [set` `]-oo, +oo[]                          *)
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
(*                      $| T | == T : Type is inhabited                       *)
(*                    squash x == proof of $| T | (with x : T)                *)
(*                  unsquash s == extract a witness from s : $| T |           *)
(* --> Tactic:                                                                *)
(*   - squash x:                                                              *)
(*     solves a goal $| T | by instantiating with x or [the T of x]           *)
(*                                                                            *)
(*                trivIset D F == the sets F i, where i ranges over D : set I,*)
(*                                are pairwise-disjoint                       *)
(*                   cover D F := \bigcup_(i in D) F i                        *)
(*             partition D F A == the non-empty sets F i,where i ranges over  *)
(*                                D : set I, form a partition of A            *)
(*          pblock_index D F x == index i such that i \in D and x \in F i     *)
(*                pblock D F x := F (pblock_index D F x)                      *)
(*                                                                            *)
(* * Upper and lower bounds:                                                  *)
(*              ubound A == the set of upper bounds of the set A              *)
(*              lbound A == the set of lower bounds of the set A              *)
(*   Predicates to express existence conditions of supremum and infimum of    *)
(*   sets of real numbers:                                                    *)
(*          has_ubound A := ubound A != set0                                  *)
(*             has_sup A := A != set0 /\ has_ubound A                         *)
(*          has_lbound A := lbound A != set0                                  *)
(*             has_inf A := A != set0 /\ has_lbound A                         *)
(*                                                                            *)
(*             isLub A m := m is a least upper bound of the set A             *)
(*           supremums A := set of supremums of the set A                     *)
(*         supremum x0 A == supremum of A or x0 if A is empty                 *)
(*            infimums A := set of infimums of the set A                      *)
(*          infimum x0 A == infimum of A or x0 if A is empty                  *)
(*                                                                            *)
(*               F `#` G := the classes of sets F and G intersect             *)
(*                                                                            *)
(* * sections:                                                                *)
(*           xsection A x == with A : set (T1 * T2) and x : T1 is the         *)
(*                           x-section of A                                   *)
(*           ysection A y == with A : set (T1 * T2) and y : T2 is the         *)
(*                           y-section of A                                   *)
(*                                                                            *)
(* * About the naming conventions in this file:                               *)
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
(* * Composition of relations:                                                *)
(*                A \; B == [set x | exists z, A (x.1, z) & B (z, x.2)]       *)
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
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (at level 0, format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
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
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).
Reserved Notation "[ 'set`' p ]" (at level 0, format "[ 'set`'  p ]").
Reserved Notation "[ 'disjoint' A & B ]" (at level 0,
  format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").
Reserved Notation "F `#` G"
 (at level 48, left associativity, format "F  `#`  G").
Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").

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

Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].
Arguments image _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A ]" :=
  (image A (fun x => E)) : classical_set_scope.

Definition image2 {TA TB rT} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & f x y = z].
Arguments image2 _ _ _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (image2 A B (fun x y => E)) : classical_set_scope.

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).

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
Definition setMR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | A1 z.1 /\ A2 z.1 z.2].
Definition setML T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | A1 z.2 z.1 /\ A2 z.2].

Lemma mksetE (P : T -> Prop) x : [set x | P x] x = P x.
Proof. by []. Qed.

Definition bigcap T I (P : set I) (F : I -> set T) :=
  [set a | forall i, P i -> F i a].
Definition bigcup T I (P : set I) (F : I -> set T) :=
  [set a | exists2 i, P i & F i a].

Definition subset A B := forall t, A t -> B t.
Local Notation "A `<=` B" := (subset A B).

Definition disj_set A B := setI A B == set0.

Definition proper A B := A `<=` B /\ ~ (B `<=` A).

End basic_definitions.
Arguments preimage T rT f Y t /.
Arguments set0 _ _ /.
Arguments setT _ _ /.
Arguments set1 _ _ _ /.
Arguments setI _ _ _ _ /.
Arguments setU _ _ _ _ /.
Arguments setC _ _ _ /.
Arguments setD _ _ _ _ /.
Arguments setM _ _ _ _ _ /.
Arguments setMR _ _ _ _ _ /.
Arguments setML _ _ _ _ _ /.
Arguments fst_set _ _ _ _ /.
Arguments snd_set _ _ _ _ /.

Notation range F := [set F i | i in setT].
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A) : classical_set_scope.
Notation "A .`2" := (snd_set A) : classical_set_scope.
Notation "A `*`` B" := (setMR A B) : classical_set_scope.
Notation "A ``*` B" := (setML A B) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.
Notation "[ 'disjoint' A & B ]" := (disj_set A B) : classical_set_scope.

Notation "'`I_' n" := [set k | is_true (k < n)%N].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : classical_set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<` B" := (proper A B) : classical_set_scope.

Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image A f) (only parsing) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Notation "[ 'set`' p ]":= [set x | is_true (x \in p)] : classical_set_scope.
Notation pred_set := (fun i => [set` i]).

Notation "`[ a , b ]" :=
  [set` Interval (BLeft a) (BRight b)] : classical_set_scope.
Notation "`] a , b ]" :=
  [set` Interval (BRight a) (BRight b)] : classical_set_scope.
Notation "`[ a , b [" :=
  [set` Interval (BLeft a) (BLeft b)] : classical_set_scope.
Notation "`] a , b [" :=
  [set` Interval (BRight a) (BLeft b)] : classical_set_scope.
Notation "`] '-oo' , b ]" :=
  [set` Interval -oo%O (BRight b)] : classical_set_scope.
Notation "`] '-oo' , b [" :=
  [set` Interval -oo%O (BLeft b)] : classical_set_scope.
Notation "`[ a , '+oo' [" :=
  [set` Interval (BLeft a) +oo%O] : classical_set_scope.
Notation "`] a , '+oo' [" :=
  [set` Interval (BRight a) +oo%O] : classical_set_scope.
Notation "`] -oo , '+oo' [" :=
  [set` Interval -oo%O +oo%O] : classical_set_scope.

Lemma preimage_itv T (d : unit) (rT : porderType d) (f : T -> rT) (i : interval rT) (x : T) :
  ((f @^-1` [set` i]) x) = (f x \in i).
Proof. by rewrite inE. Qed.

Lemma preimage_itv_o_infty T (d : unit) (rT : porderType d) (f : T -> rT) y :
  f @^-1` `]y, +oo[%classic = [set x | (y < f x)%O].
Proof.
by rewrite predeqE => t; split => [|?]; rewrite /= in_itv/= andbT.
Qed.

Lemma preimage_itv_c_infty T (d : unit) (rT : porderType d) (f : T -> rT) y :
  f @^-1` `[y, +oo[%classic = [set x | (y <= f x)%O].
Proof.
by rewrite predeqE => t; split => [|?]; rewrite /= in_itv/= andbT.
Qed.

Lemma preimage_itv_infty_o T (d : unit) (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y[%classic = [set x | (f x < y)%O].
Proof. by rewrite predeqE => t; split => [|?]; rewrite /= in_itv. Qed.

Lemma preimage_itv_infty_c T (d : unit) (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y]%classic = [set x | (f x <= y)%O].
Proof. by rewrite predeqE => t; split => [|?]; rewrite /= in_itv. Qed.

Lemma eq_set T (P Q : T -> Prop) : (forall x : T, P x = Q x) ->
  [set x | P x] = [set x | Q x].
Proof. by move=> /funext->. Qed.

Coercion set_type T (A : set T) := {x : T | x \in A}.

Definition SigSub {T} {pT : predType T} {P : pT} x : x \in P -> {x | x \in P} :=
  exist (fun x => x \in P) x.

Lemma set0fun {P T : Type} : @set0 T -> P. Proof. by case=> x; rewrite inE. Qed.

Lemma pred_oappE {T : Type} (D : {pred T}) :
  pred_oapp D = mem (some @` D)%classic.
Proof.
apply/funext=> -[x|]/=; apply/idP/idP; rewrite /pred_oapp/= inE //=.
- by move=> xD; exists x.
- by move=> [// + + [<-]].
- by case.
Qed.

Lemma pred_oapp_set {T : Type} (D : set T) :
  pred_oapp (mem D) = mem (some @` D)%classic.
Proof.
by rewrite pred_oappE; apply/funext => x/=; apply/idP/idP; rewrite ?inE;
   move=> [y/= ]; rewrite ?in_setE; exists y; rewrite ?in_setE.
Qed.

Section basic_lemmas.
Context {T : Type}.
Implicit Types A B C D : set T.

Lemma mem_set {A} {u : T} : A u -> u \in A. Proof. by rewrite inE. Qed.
Lemma set_mem {A} {u : T} : u \in A -> A u. Proof. by rewrite inE. Qed.
Lemma mem_setT (u : T)    : u \in [set: T]. Proof. by rewrite inE. Qed.
Lemma mem_setK {A} {u : T} : cancel (@mem_set A u) set_mem. Proof. by []. Qed.
Lemma set_memK {A} {u : T} : cancel (@set_mem A u) mem_set. Proof. by []. Qed.

Lemma memNset (A : set T) (u : T) : ~ A u -> u \in A = false.
Proof. by apply: contra_notF; rewrite inE. Qed.

Lemma notin_set (A : set T) x : (x \notin A : Prop) = ~ (A x).
Proof. by apply/propext; split=> /asboolPn. Qed.

Lemma setTPn (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.
#[deprecated(note="Use setTPn instead")]
Notation setTP := setTPn.

Lemma in_set0 (x : T) : (x \in set0) = false. Proof. by rewrite memNset. Qed.
Lemma in_setT (x : T) : x \in setT. Proof. by rewrite mem_set. Qed.

Lemma in_setC (x : T) A : (x \in ~` A) = (x \notin A).
Proof. by apply/idP/idP; rewrite inE notin_set. Qed.

Lemma in_setI (x : T) A B : (x \in A `&` B) = (x \in A) && (x \in B).
Proof. by apply/idP/andP; rewrite !inE. Qed.

Lemma in_setD (x : T) A B : (x \in A `\` B) = (x \in A) && (x \notin B).
Proof. by apply/idP/andP; rewrite !inE notin_set. Qed.

Lemma in_setU (x : T) A B : (x \in A `|` B) = (x \in A) || (x \in B).
Proof. by apply/idP/orP; rewrite !inE. Qed.

Lemma in_setM T' (x : T * T') A E : (x \in A `*` E) = (x.1 \in A) && (x.2 \in E).
Proof. by apply/idP/andP; rewrite !inE. Qed.

Lemma set_valP {A} (x : A) : A (val x).
Proof. by apply: set_mem; apply: valP. Qed.

Lemma eqEsubset A B : (A = B) = (A `<=>` B).
Proof.
rewrite propeqE; split => [->|[AB BA]]; [by split|].
by rewrite predeqE => t; split=> [/AB|/BA].
Qed.

Lemma seteqP A B : (A = B) <-> (A `<=>` B). Proof. by rewrite eqEsubset. Qed.

Lemma set_true : [set` predT] = setT :> set T.
Proof. by apply/seteqP; split. Qed.

Lemma set_false : [set` pred0] = set0 :> set T.
Proof. by apply/seteqP; split. Qed.

Lemma set_andb (P Q : {pred T}) : [set` predI P Q] = [set` P] `&` [set` Q].
Proof. by apply/predeqP => x; split; rewrite /= inE => /andP. Qed.

Lemma set_orb (P Q : {pred T}) : [set` predU P Q] = [set` P] `|` [set` Q].
Proof. by apply/predeqP => x; split; rewrite /= inE => /orP. Qed.

Lemma fun_true : (fun=> true) = setT :> set T.
Proof. by rewrite [LHS]set_true. Qed.

Lemma fun_false : (fun=> false) = set0 :> set T.
Proof. by rewrite [LHS]set_false. Qed.

Lemma set_mem_set A : [set` A] = A.
Proof. by apply/seteqP; split=> x/=; rewrite inE. Qed.

Lemma mem_setE (P : pred T) : mem [set` P] = mem P.
Proof. by congr Mem; apply/funext=> x; apply/asboolP/idP. Qed.

Lemma subset_refl A : A `<=` A. Proof. by []. Qed.

Lemma subset_trans B A C : A `<=` B -> B `<=` C -> A `<=` C.
Proof. by move=> sAB sBC ? ?; apply/sBC/sAB. Qed.

Lemma sub0set A : set0 `<=` A. Proof. by []. Qed.

Lemma setC0 : ~` set0 = setT :> set T.
Proof. by rewrite predeqE; split => ?. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; rewrite funeqE => t; rewrite /setC; exact: notLR. Qed.

Lemma setCT : ~` setT = set0 :> set T. Proof. by rewrite -setC0 setCK. Qed.

Definition setC_inj := can_inj setCK.

Lemma setIC : commutative (@setI T).
Proof. by move=> A B; rewrite predeqE => ?; split=> [[]|[]]. Qed.

Lemma setIS C A B : A `<=` B -> C `&` A `<=` C `&` B.
Proof. by move=> sAB t [Ct At]; split => //; exact: sAB. Qed.

Lemma setSI C A B : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(setIC C); apply setIS. Qed.

Lemma setISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(@setSI B) /subset_trans sAC /(@setIS C) /sAC. Qed.

Lemma setIT : right_id setT (@setI T).
Proof. by move=> A; rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setTI : left_id setT (@setI T).
Proof. by move=> A; rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setI0 : right_zero set0 (@setI T).
Proof. by move=> A; rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma set0I : left_zero set0 (@setI T).
Proof. by move=> A; rewrite setIC setI0. Qed.

Lemma setICl : left_inverse set0 setC (@setI T).
Proof. by move=> A; rewrite predeqE => ?; split => // -[]. Qed.

Lemma setICr : right_inverse set0 setC (@setI T).
Proof. by move=> A; rewrite setIC setICl. Qed.

Lemma setIA : associative (@setI T).
Proof. by move=> A B C; rewrite predeqE => ?; split=> [[? []]|[[]]]. Qed.

Lemma setICA : left_commutative (@setI T).
Proof. by move=> A B C; rewrite setIA [A `&` _]setIC -setIA. Qed.

Lemma setIAC : right_commutative (@setI T).
Proof. by move=> A B C; rewrite setIC setICA setIA. Qed.

Lemma setIACA : @interchange (set T) setI setI.
Proof. by move=> A B C D; rewrite -setIA [B `&` _]setICA setIA. Qed.

Lemma setIid : idempotent (@setI T).
Proof. by move=> A; rewrite predeqE => ?; split=> [[]|]. Qed.

Lemma setIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(setIC A) setIIl. Qed.

Lemma setUC : commutative (@setU T).
Proof. move=> p q; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUS C A B : A `<=` B -> C `|` A `<=` C `|` B.
Proof. by move=> sAB t [Ct|At]; [left|right; exact: sAB]. Qed.

Lemma setSU C A B : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> sAB; rewrite -!(setUC C); apply setUS. Qed.

Lemma setUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. by move=> /(@setSU B) /subset_trans sAC /(@setUS C) /sAC. Qed.

Lemma setTU : left_zero setT (@setU T).
Proof. by move=> A; rewrite predeqE => t; split; [case|left]. Qed.

Lemma setUT : right_zero setT (@setU T).
Proof. by move=> A; rewrite predeqE => t; split; [case|right]. Qed.

Lemma set0U : left_id set0 (@setU T).
Proof. by move=> A; rewrite predeqE => t; split; [case|right]. Qed.

Lemma setU0 : right_id set0 (@setU T).
Proof. by move=> A; rewrite predeqE => t; split; [case|left]. Qed.

Lemma setUCl : left_inverse setT setC (@setU T).
Proof.
move=> A.
by rewrite predeqE => t; split => // _; case: (pselect (A t)); [right|left].
Qed.

Lemma setUCr : right_inverse setT setC (@setU T).
Proof. by move=> A; rewrite setUC setUCl. Qed.

Lemma setUA : associative (@setU T).
Proof. move=> p q r; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUCA : left_commutative (@setU T).
Proof. by move=> A B C; rewrite setUA [A `|` _]setUC -setUA. Qed.

Lemma setUAC : right_commutative (@setU T).
Proof. by move=> A B C; rewrite setUC setUCA setUA. Qed.

Lemma setUACA : @interchange (set T) setU setU.
Proof. by move=> A B C D; rewrite -setUA [B `|` _]setUCA setUA. Qed.

Lemma setUid : idempotent (@setU T).
Proof. move=> p; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(setUC A) setUUl. Qed.

Lemma setDE A B : A `\` B = A `&` ~` B. Proof. by []. Qed.

Lemma setDUK A B : A `<=` B -> A `|` (B `\` A) = B.
Proof.
move=> AB; apply/seteqP; split=> [x [/AB//|[//]]|x Bx].
by have [Ax|nAx] := pselect (A x); [left|right].
Qed.

Lemma setDKU A B : A `<=` B -> (B `\` A) `|` A = B.
Proof. by move=> /setDUK; rewrite setUC. Qed.

Lemma setDv A : A `\` A = set0.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma setUv A : A `|` ~` A = setT.
Proof. by apply/predeqP => x; split=> //= _; apply: lem. Qed.

Lemma setvU A : ~` A `|` A = setT. Proof. by rewrite setUC setUv. Qed.

Lemma setUCK A B : (A `|` B) `|` ~` B = setT.
Proof. by rewrite -setUA setUv setUT. Qed.

Lemma setUKC A B : ~` A `|` (A `|` B) = setT.
Proof. by rewrite setUA setvU setTU. Qed.

Lemma setICK A B : (A `&` B) `&` ~` B = set0.
Proof. by rewrite -setIA setICr setI0. Qed.

Lemma setIKC A B : ~` A `&` (A `&` B) = set0.
Proof. by rewrite setIA setICl set0I. Qed.

Lemma setDIK A B : A `&` (B `\` A) = set0.
Proof. by rewrite setDE setICA -setDE setDv setI0. Qed.

Lemma setDKI A B : (B `\` A) `&` A = set0.
Proof. by rewrite setIC setDIK. Qed.

Lemma setD1K a A : A a -> a |` A `\ a = A.
Proof.  by move=> Aa; rewrite setDUK//= => x ->. Qed.

Lemma setI1 A a : A `&` [set a] = if a \in A then [set a] else set0.
Proof.
by apply/predeqP => b; case: ifPn; rewrite (inE, notin_set) => Aa;
   split=> [[]|]//; [move=> -> //|move=> /[swap] -> /Aa].
Qed.

Lemma set1I A a : [set a] `&` A = if a \in A then [set a] else set0.
Proof. by rewrite setIC setI1. Qed.

Lemma subset0 A : (A `<=` set0) = (A = set0).
Proof. by rewrite eqEsubset propeqE; split=> [A0|[]//]; split. Qed.

Lemma subTset A : (setT `<=` A) = (A = setT).
Proof. by rewrite eqEsubset propeqE; split=> [|[]]. Qed.

Lemma sub1set x A : ([set x] `<=` A) = (x \in A).
Proof. by apply/propext; split=> [|/[!inE] xA _ ->//]; rewrite inE; exact. Qed.

Lemma subsetT A : A `<=` setT. Proof. by []. Qed.

Lemma subsetW {A B} : A = B -> A `<=` B. Proof. by move->. Qed.

Definition subsetCW {A B} : A = B -> B `<=` A := subsetW \o esym.

Lemma disj_set2E A B : [disjoint A & B] = (A `&` B == set0).
Proof. by []. Qed.

Lemma disj_set2P {A B} : reflect (A `&` B = set0) [disjoint A & B]%classic.
Proof. exact/eqP. Qed.

Lemma disj_setPS {A B} : reflect (A `&` B `<=` set0) [disjoint A & B]%classic.
Proof. by rewrite subset0; apply: disj_set2P. Qed.

Lemma disj_set_sym A B : [disjoint B & A] = [disjoint A & B].
Proof. by rewrite !disj_set2E setIC. Qed.

Lemma disj_setPCl {A B} : reflect (A `<=` B) [disjoint A & ~` B]%classic.
Proof.
apply: (iffP disj_setPS) => [P t ?|P t [/P//]].
by apply: contrapT => ?; apply: (P t).
Qed.

Lemma disj_setPCr {A B} : reflect (A `<=` B) [disjoint ~` B & A]%classic.
Proof. by rewrite disj_set_sym; apply: disj_setPCl. Qed.

Lemma disj_setPLR {A B} : reflect (A `<=` ~` B) [disjoint A & B]%classic.
Proof. by apply: (equivP idP); rewrite (rwP disj_setPCl) setCK. Qed.

Lemma disj_setPRL {A B} : reflect (B `<=` ~` A) [disjoint A & B]%classic.
Proof. by apply: (equivP idP); rewrite (rwP disj_setPCr) setCK. Qed.

Lemma subsets_disjoint A B : A `<=` B <-> A `&` ~` B = set0.
Proof. by rewrite (rwP disj_setPCl) (rwP eqP). Qed.

Lemma disjoints_subset A B : A `&` B = set0 <-> A `<=` ~` B.
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma subsetC1 x A : (A `<=` [set~ x]) = (x \in ~` A).
Proof.
rewrite !inE; apply/propext; split; first by move/[apply]; apply.
by move=> NAx y; apply: contraPnot => ->.
Qed.

Lemma setSD C A B : A `<=` B -> A `\` C `<=` B `\` C.
Proof. by rewrite !setDE; apply: setSI. Qed.

Lemma setTD A : setT `\` A = ~` A.
Proof. by rewrite predeqE => t; split => // -[]. Qed.

Lemma set0P A : (A != set0) <-> (A !=set0).
Proof.
split=> [/negP A_neq0|[t tA]]; last by apply/negP => /eqP A0; rewrite A0 in tA.
apply: contrapT => /asboolPn/forallp_asboolPn A0; apply/A_neq0/eqP.
by rewrite eqEsubset; split.
Qed.

Lemma setF_eq0 : (T -> False) -> all_equal_to (set0 : set T).
Proof. by move=> TF A; rewrite -subset0 => x; have := TF x. Qed.

Lemma subset_nonempty A B : A `<=` B -> A !=set0 -> B !=set0.
Proof. by move=> sAB [x Ax]; exists x; apply: sAB. Qed.

Lemma subsetC A B : A `<=` B -> ~` B `<=` ~` A.
Proof. by move=> sAB ? nBa ?; apply/nBa/sAB. Qed.

Lemma subsetCl A B : ~` A `<=` B -> ~` B `<=` A.
Proof. by move=> /subsetC; rewrite setCK. Qed.

Lemma subsetCr A B : A `<=` ~` B -> B `<=` ~` A.
Proof. by move=> /subsetC; rewrite setCK. Qed.

Lemma subsetC2 A B : ~` A `<=` ~` B -> B `<=` A.
Proof. by move=> /subsetC; rewrite !setCK. Qed.

Lemma subsetCP A B : ~` A `<=` ~` B <-> B `<=` A.
Proof. by split=> /subsetC; rewrite ?setCK. Qed.

Lemma subsetCPl A B : ~` A `<=` B <-> ~` B `<=` A.
Proof. by split=> /subsetC; rewrite ?setCK. Qed.

Lemma subsetCPr A B : A `<=` ~` B <-> B `<=` ~` A.
Proof. by split=> /subsetC; rewrite ?setCK. Qed.

Lemma subsetUl A B : A `<=` A `|` B. Proof. by move=> x; left. Qed.

Lemma subsetUr A B : B `<=` A `|` B. Proof. by move=> x; right. Qed.

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

Lemma setIidPr A B : A `&` B = B <-> B `<=` A.
Proof. by rewrite setIC setIidPl. Qed.

Lemma setIidl A B : A `<=` B -> A `&` B = A. Proof. by rewrite setIidPl. Qed.
Lemma setIidr A B : B `<=` A -> A `&` B = B. Proof. by rewrite setIidPr. Qed.

Lemma setUidPl A B : A `|` B = A <-> B `<=` A.
Proof.
split=> [<- ? ?|BA]; first by right.
rewrite predeqE => t; split=> [[//|/BA//]|?]; by left.
Qed.

Lemma setUidPr A B : A `|` B = B <-> A `<=` B.
Proof. by rewrite setUC setUidPl. Qed.

Lemma setUidl A B : B `<=` A -> A `|` B = A. Proof. by rewrite setUidPl. Qed.
Lemma setUidr A B : A `<=` B -> A `|` B = B. Proof. by rewrite setUidPr. Qed.

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

Lemma setDidl A B : A `&` B = set0 -> A `\` B = A.
Proof. by move=> /setDidPl. Qed.

Lemma subIset A B C : A `<=` C \/ B `<=` C -> A `&` B `<=` C.
Proof. case=> sub a; by [move=> [/sub] | move=> [_ /sub]]. Qed.

Lemma subIsetl A B : A `&` B `<=` A. Proof. by move=> x []. Qed.

Lemma subIsetr A B : A `&` B `<=` B. Proof. by move=> x []. Qed.

Lemma subDsetl A B : A `\` B `<=` A.
Proof. by rewrite setDE; apply: subIsetl. Qed.

Lemma subDsetr A B : A `\` B `<=` ~` B.
Proof. by rewrite setDE; apply: subIsetr. Qed.

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

Lemma setU_eq0 A B : (A `|` B = set0) = ((A = set0) /\ (B = set0)).
Proof. by rewrite -!subset0 subUset. Qed.

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

Lemma setDS C A B : A `<=` B -> C `\` B `<=` C `\` A.
Proof. by rewrite !setDE -setCS; apply: setIS. Qed.

Lemma setDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. by move=> /(@setSD B) /subset_trans sAC /(@setDS C) /sAC. Qed.

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

Lemma setDUl : left_distributive setD (@setU T).
Proof. by move=> A B C; rewrite !setDE setIUl. Qed.

Lemma setUKD A B : A `&` B `<=` set0 -> (A `|` B) `\` A = B.
Proof. by move=> AB0; rewrite setDUl setDv set0U setDidl// -subset0 setIC. Qed.

Lemma setUDK A B : A `&` B `<=` set0 -> (B `|` A) `\` A = B.
Proof. by move=> *; rewrite setUC setUKD. Qed.

Lemma setIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by rewrite !setDE setIA. Qed.

Lemma setDD A B : A `\` (A `\` B) = A `&` B.
Proof. by rewrite 2!setDE setCI setCK setIUr setICr set0U. Qed.

Lemma setDDl A B C : (A `\` B) `\` C = A `\` (B `|` C).
Proof. by rewrite !setDE setCU setIA. Qed.

Lemma setDDr A B C : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
Proof. by rewrite !setDE setCI setIUr setCK. Qed.

Lemma setDIr A B C : A `\` B `&` C = (A `\` B) `|` (A `\` C).
Proof. by rewrite !setDE setCI setIUr. Qed.

Lemma setUIDK A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite setUC -setDDr setDv setD0. Qed.

Lemma setM0 T' (A : set T) : A `*` set0 = set0 :> set (T * T').
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma set0M T' (A : set T') : set0 `*` A = set0 :> set (T * T').
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma setMTT T' : setT `*` setT = setT :> set (T * T').
Proof. exact/predeqP. Qed.

Lemma setMT T1 T2 (A : set T1) : A `*` @setT T2 = fst @^-1` A.
Proof. by rewrite predeqE => -[x y]; split => //= -[]. Qed.

Lemma setTM T1 T2 (B : set T2) : @setT T1 `*` B = snd @^-1` B.
Proof. by rewrite predeqE => -[x y]; split => //= -[]. Qed.

Lemma setMI T1 T2 (X1 : set T1) (X2 : set T2) (Y1 : set T1) (Y2 : set T2) :
  (X1 `&` Y1) `*` (X2 `&` Y2) = X1 `*` X2 `&` Y1 `*` Y2.
Proof. by rewrite predeqE => -[x y]; split=> [[[? ?] [*]//]|[] [? ?] [*]]. Qed.

Lemma setSM T1 T2 (C D : set T1) (A B : set T2) :
  A `<=` B -> C `<=` D -> C `*` A `<=` D `*` B.
Proof. by move=> AB CD x [] /CD Dx1 /AB Bx2. Qed.

Lemma setM_bigcupr T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  A `*` \bigcup_(i in P) F i = \bigcup_(i in P) (A `*` F i).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [/= Ax [n Pn Fny]]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma setM_bigcupl T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  \bigcup_(i in P) F i `*` A = \bigcup_(i in P) (F i `*` A).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [[n Pn Fnx] Ax]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma bigcupM1l T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :
  \bigcup_(i in A1) ([set i] `*` (A2 i)) = A1 `*`` A2.
Proof. by apply/predeqP => -[i j]; split=> [[? ? [/= -> //]]|[]]; exists i. Qed.

Lemma bigcupM1r T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :
  \bigcup_(i in A2) (A1 i `*` [set i]) = A1 ``*` A2.
Proof. by apply/predeqP => -[i j]; split=> [[? ? [? /= -> //]]|[]]; exists j. Qed.

End basic_lemmas.
#[global]
Hint Resolve subsetUl subsetUr subIsetl subIsetr subDsetl subDsetr : core.
#[deprecated(since="mathcomp-analysis 0.6", note="Use setICl instead.")]
Notation setvI := setICl.
#[deprecated(since="mathcomp-analysis 0.6", note="Use setICr instead.")]
Notation setIv := setICr.

Lemma image2E {TA TB rT : Type} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :
  [set f x y | x in A & y in B] = uncurry f @` (A `*` B).
Proof.
apply/predeqP => x; split=> [[a ? [b ? <-]]|[[a b] [? ? <-]]]/=;
by [exists (a, b) | exists a => //; exists b].
Qed.

Lemma image2_subset {aT bT rT : Type} [f : aT -> bT -> rT] [A B: set aT] [C D : set bT] :
   A `<=` B -> C `<=` D ->
   [set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D].
Proof.
move=> AB CD x [a aA [c cC xe]]; subst x; exists a; (try by apply AB).
by exists c; (try by apply CD).
Qed.

Lemma set_nil (T : choiceType) : [set` [::]] = @set0 T.
Proof. by rewrite predeqP. Qed.

Lemma set_seq_eq0 (T : eqType) (S : seq T) : ([set` S] == set0) = (S == [::]).
Proof.
apply/eqP/eqP=> [|->]; rewrite predeqE //; case: S => // h t /(_ h).
by rewrite /= mem_head => -[/(_ erefl)].
Qed.

Lemma set_fset_eq0 (T : choiceType) (S : {fset T}) :
  ([set` S] == set0) = (S == fset0).
Proof. by rewrite set_seq_eq0. Qed.

Section InitialSegment.

Lemma II0 : `I_0 = set0. Proof. by rewrite predeqE. Qed.

Lemma II1 : `I_1 = [set 0]. Proof. by rewrite predeqE; case. Qed.

Lemma IIn_eq0 n : `I_n = set0 -> n = 0.
Proof. by case: n => // n; rewrite predeqE; case/(_ 0%N); case. Qed.

Lemma IIS n : `I_n.+1 = `I_n `|` [set n].
Proof.
rewrite /mkset predeqE => i; split => [|[|->//]].
by rewrite ltnS leq_eqVlt => /orP[/eqP ->|]; by [left|right].
by move/ltn_trans; apply.
Qed.

Lemma IISl n : `I_n.+1 = n |` `I_n.
Proof. by rewrite setUC IIS. Qed.

Lemma IIDn n : `I_n.+1 `\ n = `I_n.
Proof. by rewrite IIS setUDK// => x [->/=]; rewrite ltnn. Qed.

Lemma setI_II m n : `I_m `&` `I_n = `I_(minn m n).
Proof.
by case: leqP => mn; [rewrite setIidl// | rewrite setIidr//]
   => k /= /leq_trans; apply => //; apply: ltnW.
Qed.

Lemma setU_II m n : `I_m `|` `I_n = `I_(maxn m n).
Proof.
by case: leqP => mn; [rewrite setUidr// | rewrite setUidl//]
   => k /= /leq_trans; apply => //; apply: ltnW.
Qed.

Lemma Iiota (n : nat) : [set` iota 0 n] = `I_n.
Proof. by apply/seteqP; split => [|] ?; rewrite /= mem_iota add0n. Qed.

Definition ordII {n} (k : 'I_n) : `I_n := SigSub (@mem_set _ `I_n _ (ltn_ord k)).
Definition IIord {n} (k : `I_n) := Ordinal (set_valP k).

Definition ordIIK {n} : cancel (@ordII n) IIord.
Proof. by move=> k; apply/val_inj. Qed.

Lemma IIordK {n} : cancel (@IIord n) ordII.
Proof. by move=> k; apply/val_inj. Qed.

End InitialSegment.

Lemma setT_unit : [set: unit] = [set tt].
Proof. by apply/seteqP; split => // -[]. Qed.

Lemma setT_bool : [set: bool] = [set true; false].
Proof. by rewrite eqEsubset; split => // [[]] // _; [left|right]. Qed.

(* TODO: other lemmas that relate fset and classical sets *)
Lemma fdisjoint_cset (T : choiceType) (A B : {fset T}) :
  [disjoint A & B]%fset = [disjoint [set` A] & [set` B]].
Proof.
rewrite -fsetI_eq0; apply/idP/idP; apply: contraLR.
by move=> /set0P[t [tA tB]]; apply/fset0Pn; exists t; rewrite inE; apply/andP.
by move=> /fset0Pn[t]; rewrite inE => /andP[tA tB]; apply/set0P; exists t.
Qed.

Section SetFset.
Context {T : choiceType}.
Implicit Types (x y : T) (A B : {fset T}).

Lemma set_fset0 : [set y : T | y \in fset0] = set0.
Proof. by rewrite -subset0 => x. Qed.

Lemma set_fset1 x : [set y | y \in [fset x]%fset] = [set x].
Proof. by rewrite predeqE => y; split; rewrite /= inE => /eqP. Qed.

Lemma set_fsetI A B : [set` (A `&` B)%fset] = [set` A] `&` [set` B].
Proof.
by rewrite predeqE => x; split; rewrite /= !inE; [case/andP|case=> -> ->].
Qed.

Lemma set_fsetIr (P : {pred T}) (A : {fset T}) :
  [set` [fset x | x in A & P x]%fset] = [set` A] `&` [set` P].
Proof. by apply/predeqP => x /=; split; rewrite 2!inE/= => /andP. Qed.

Lemma set_fsetU A B :
  [set` (A `|` B)%fset] = [set` A] `|` [set` B].
Proof.
rewrite predeqE => x; split; rewrite /= !inE.
  by case/orP; [left|right].
by move=> []->; rewrite ?orbT.
Qed.

Lemma set_fsetU1 x A : [set y | y \in (x |` A)%fset] = x |` [set` A].
Proof. by rewrite set_fsetU set_fset1. Qed.

Lemma set_fsetD A B :
  [set` (A `\` B)%fset] = [set` A] `\` [set` B].
Proof.
rewrite predeqE => x; split; rewrite /= !inE; last by move=> [-> /negP ->].
by case/andP => /negP xNB xA.
Qed.

Lemma set_fsetD1 A x : [set y | y \in (A `\ x)%fset] = [set` A] `\ x.
Proof. by rewrite set_fsetD set_fset1. Qed.

Lemma set_imfset (key : unit) [K : choiceType] (f : T -> K) (p : finmempred T) :
  [set` imfset key f p] = f @` [set` p].
Proof.
apply/predeqP => x; split=> [/imfsetP[i ip -> /=]|]; first by exists i.
by move=> [i ip <-]; apply: in_imfset.
Qed.

End SetFset.

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

Section base_image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma imageP f A a : A a -> (f @` A) (f a). Proof. by exists a. Qed.

Lemma imageT (f : aT -> rT) (a : aT) : range f (f a).
Proof. by apply: imageP. Qed.

End base_image_lemmas.
#[global]
Hint Extern 0 ((?f @` _) (?f _)) =>  solve [apply: imageP; assumption] : core.
#[global] Hint Extern 0 ((?f @` setT) _) => solve [apply: imageT] : core.

Section image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma image_inj {f A a} : injective f -> (f @` A) (f a) = A a.
Proof.
by move=> f_inj; rewrite propeqE; split => [[b Ab /f_inj <-]|/(imageP f)//].
Qed.

Lemma image_id A : id @` A = A.
Proof. by rewrite eqEsubset; split => a; [case=> /= x Ax <-|exists a]. Qed.

Lemma homo_setP {A Y f} :
  {homo f : x / x \in A >-> x \in Y} <-> {homo f : x / A x >-> Y x}.
Proof. by split=> fAY x; have := fAY x; rewrite !inE. Qed.

Lemma image_subP {A Y f} : f @` A `<=` Y <-> {homo f : x / A x >-> Y x}.
Proof. by split=> fAY x => [Ax|[y + <-]]; apply: fAY=> //; exists x. Qed.

Lemma image_sub  {f : aT -> rT} {A : set aT} {B : set rT} :
  (f @` A `<=` B) = (A `<=` f @^-1` B).
Proof. by apply/propext; rewrite image_subP; split=> AB a /AB. Qed.

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
move=> Aa; have [/eqP|/set0P[t At]] := boolP (A == set0); first by left.
by right; rewrite eqEsubset; split => // ? ->; rewrite -(Aa _ At).
Qed.

Lemma subset_set2 A a b : A `<=` [set a; b] ->
  [\/ A = set0, A = [set a], A = [set b] | A = [set a; b]].
Proof.
have [<-|ab Aab] := pselect (a = b).
  by rewrite setUid => /subset_set1[]->; [apply: Or41|apply: Or42].
have [|/nonsubset[x [/[dup] /Aab []// -> Ab _]]] := pselect (A `<=` [set a]).
  by move=> /subset_set1[]->; [apply: Or41|apply: Or42].
have [|/nonsubset[y [/[dup] /Aab []// -> Aa _]]] := pselect (A `<=` [set b]).
  by move=> /subset_set1[]->; [apply: Or41|apply: Or43].
by apply: Or44; apply/seteqP; split=> // z /= [] ->.
Qed.

Lemma sub_image_setI f A B : f @` (A `&` B) `<=` f @` A `&` f @` B.
Proof. by move=> b [x [Aa Ba <-]]; split; apply: imageP. Qed.

Lemma nonempty_image f A : f @` A !=set0 -> A !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof. by move=> AB _ [a Aa <-]; exists a => //; apply/AB. Qed.

Lemma preimage_set0 f : f @^-1` set0 = set0. Proof. exact/predeqP. Qed.

Lemma preimage_setT f : f @^-1` setT = setT. Proof. by []. Qed.

Lemma nonempty_preimage f Y : f @^-1` Y !=set0 -> Y !=set0.
Proof. by case=> [t ?]; exists (f t). Qed.

Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Proof. by move=> a Aa; exists a. Qed.

Lemma image_preimage_subset f Y : f @` (f @^-1` Y) `<=` Y.
Proof. by move=> _ [t /= Yft <-]. Qed.

Lemma image_preimage f Y : f @` setT = setT -> f @` (f @^-1` Y) = Y.
Proof.
move=> fsurj; rewrite predeqE => x; split; first by move=> [? ? <-].
move=> Yx; have : setT x by [].
by rewrite -fsurj => - [y _ fy_eqx]; exists y => //=; rewrite fy_eqx.
Qed.

Lemma eq_imagel T1 T2 (A : set T1) (f f' : T1 -> T2) :
  (forall x, A x -> f x = f' x) -> f @` A = f' @` A.
Proof.
by move=> h; rewrite predeqE=> y; split=> [][x ? <-]; exists x=> //; rewrite h.
Qed.

Lemma eq_image_id g A : (forall x, A x -> g x = x) -> g @` A = A.
Proof. by move=> /eq_imagel->; rewrite image_id. Qed.

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

Lemma preimage_bigcup {I} (P : set I) f (F : I -> set rT) :
  f @^-1` (\bigcup_ (i in P) F i) = \bigcup_(i in P) (f @^-1` F i).
Proof. exact/predeqP. Qed.

Lemma preimage_bigcap {I} (P : set I) f (F : I -> set rT) :
  f @^-1` (\bigcap_ (i in P) F i) = \bigcap_(i in P) (f @^-1` F i).
Proof. exact/predeqP. Qed.

Lemma eq_preimage {I T : Type} (D : set I) (A : set T) (F G : I -> T) :
  {in D, F =1 G} -> D `&` F @^-1` A = D `&` G @^-1` A.
Proof.
move=> eqFG; apply/predeqP => i.
by split=> [] [Di FAi]; split; rewrite /preimage//= (eqFG,=^~eqFG) ?inE.
Qed.

Lemma notin_setI_preimage T R D (f : T -> R) i :
  i \notin f @` D -> D `&` f @^-1` [set i] = set0.
Proof.
by rewrite notin_set/=; apply: contra_notP => /eqP/set0P[t [Dt fit]]; exists t.
Qed.

Lemma comp_preimage T1 T2 T3 (A : set T3) (g : T1 -> T2) (f : T2 -> T3) :
  (f \o g) @^-1` A = g @^-1` (f @^-1` A).
Proof. by []. Qed.

Lemma preimage_id T (A : set T) : id @^-1` A = A. Proof. by []. Qed.

Lemma preimage_comp T1 T2 (g : T1 -> rT) (f : T2 -> rT) (C : set T1) :
  f @^-1` [set g x | x in C] = [set x | f x \in g @` C].
Proof.
rewrite predeqE => t; split => /=.
  by move=> -[r Cr <-]; rewrite inE;  exists r.
by rewrite inE => -[r Cr <-]; exists r.
Qed.

Lemma preimage_setI_eq0 (f : aT -> rT) (Y1 Y2 : set rT) :
  f @^-1` (Y1 `&` Y2) = set0 <-> f @^-1` Y1 `&` f @^-1` Y2 = set0.
Proof.
by split; apply: contraPP => /eqP/set0P/(nonempty_preimage_setI f _ _).2/set0P/eqP.
Qed.

Lemma preimage0eq (f : aT -> rT) (Y : set rT) : Y = set0 -> f @^-1` Y = set0.
Proof. by move=> ->; rewrite preimage_set0. Qed.

Lemma preimage0 {T R} {f : T -> R} {A : set R} :
  A `&` range f `<=` set0 -> f @^-1` A = set0.
Proof. by rewrite -subset0 => + x /= Afx => /(_ (f x))[]; split. Qed.

Lemma preimage10P {T R} {f : T -> R} {x} : ~ range f x <-> f @^-1` [set x] = set0.
Proof.
split => [fx|]; first by rewrite preimage0// => ? [->].
by apply: contraPnot => -[t _ <-] /seteqP[+ _] => /(_ t) /=.
Qed.

Lemma preimage10 {T R} {f : T -> R} {x} : ~ range f x -> f @^-1` [set x] = set0.
Proof. by move/preimage10P. Qed.

End image_lemmas.
Arguments sub_image_setI {aT rT f A B} t _.

Lemma image_comp T1 T2 T3 (f : T1 -> T2) (g : T2 -> T3) A :
  g @` (f @` A) = (g \o f) @` A.
Proof.
by rewrite eqEsubset; split => [x [b [a Aa] <- <-]|x [a Aa] <-];
  [apply/imageP |apply/imageP/imageP].
Qed.

Lemma subKimage {T T'} {P : set (set T')} (f : T -> T') (g : T' -> T) :
  cancel f g -> [set A | P (f @` A)] `<=` [set g @` A | A in P].
Proof. by move=> ? A; exists (f @` A); rewrite ?image_comp ?eq_image_id/=. Qed.

Lemma subimageK T T' (P : set (set T')) (f : T -> T') (g : T' -> T) :
  cancel g f -> [set g @` A | A in P] `<=` [set A | P (f @` A)].
Proof. by move=> gK _ [B /= ? <-]; rewrite image_comp eq_image_id/=. Qed.

Lemma eq_imageK {T T'} {P : set (set T')} (f : T -> T') (g : T' -> T) :
    cancel f g -> cancel g f ->
  [set g @` A | A in P] = [set A | P (f @` A)].
Proof.
by move=> fK gK; apply/seteqP; split; [apply: subimageK | apply: subKimage].
Qed.

Lemma some_set0 {T} : some @` set0 = set0 :> set (option T).
Proof. by rewrite -subset0 => x []. Qed.

Lemma some_set1 {T} (x : T) : some @` [set x] = [set some x].
Proof. by apply/seteqP; split=> [_ [_ -> <-]|_ ->]//=; exists x. Qed.

Lemma some_setC {T} (A : set T) : some @` (~` A) = [set~ None] `\` (some @` A).
Proof.
apply/seteqP; split; first by move=> _ [x nAx <-]; split=> // -[y /[swap]-[->]].
by move=> [x [_ exAx]|[/(_ erefl)//]]; exists x => // Ax; apply: exAx; exists x.
Qed.

Lemma some_setT {T} : some @` [set: T] = [set~ None].
Proof. by rewrite -[setT]setCK some_setC setCT some_set0 setD0. Qed.

Lemma some_setI {T} (A B : set T) : some @` (A `&` B) = some @` A `&` some @` B.
Proof.
apply/seteqP; split; first by move=> _ [x [Ax Bx] <-]; split; exists x.
by move=> _ [[x + <-] [y By []]] => /[swap]<- Ay; exists y.
Qed.

Lemma some_setU {T} (A B : set T) : some @` (A `|` B) = some @` A `|` some @` B.
Proof.
by rewrite -[_ `|` _]setCK setCU some_setC some_setI setDIr -!some_setC !setCK.
Qed.

Lemma some_setD {T} (A B : set T) : some @` (A `\` B) = (some @` A) `\` (some @` B).
Proof. by rewrite some_setI some_setC setIDA setIidl// => _ [? _ <-]. Qed.

Lemma sub_image_some {T} (A B : set T) : some @` A `<=` some @` B -> A `<=` B.
Proof. by move=> + x Ax => /(_ (Some x))[|y By [<-]]; first by exists x. Qed.

Lemma sub_image_someP {T} (A B : set T) : some @` A `<=` some @` B <-> A `<=` B.
Proof. by split=> [/sub_image_some//|/image_subset]. Qed.

Lemma image_some_inj {T} (A B : set T) : some @` A = some @` B -> A = B.
Proof. by move=> e; apply/seteqP; split; apply: sub_image_some; rewrite e. Qed.

Lemma some_set_eq0 {T} (A : set T) : some @` A = set0 <-> A = set0.
Proof.
split=> [|->]; last by rewrite some_set0.
by rewrite -!subset0 => A0 x Ax; apply: (A0 (some x)); exists x.
Qed.

Lemma some_preimage {aT rT} (f : aT -> rT) (A : set rT) :
  some @` (f @^-1` A) = omap f @^-1` (some @` A).
Proof.
apply/seteqP; split; first by move=> _ [a Afa <-]; exists (f a).
by move=> [x|] [a Aa //= [afx]]; exists x; rewrite // -afx.
Qed.

Lemma some_image {aT rT} (f : aT -> rT) (A : set aT) :
  some @` (f @` A) = omap f @` (some @` A).
Proof. by rewrite !image_comp. Qed.

Lemma disj_set_some {T} {A B : set T} :
  [disjoint some @` A & some @` B] = [disjoint A & B].
Proof.
by apply/disj_setPS/disj_setPS; rewrite -some_setI -some_set0 sub_image_someP.
Qed.

Section bigop_lemmas.
Context {T I : Type}.
Implicit Types (A : set T) (i : I) (P : set I) (F G : I -> set T).

Lemma bigcup_sup i P F : P i -> F i `<=` \bigcup_(j in P) F j.
Proof. by move=> Pi a Fia; exists i. Qed.

Lemma bigcap_inf i P F : P i -> \bigcap_(j in P) F j `<=` F i.
Proof. by move=> Pi a /(_ i); apply. Qed.

Lemma subset_bigcup_r P : {homo (fun x : I -> set T => \bigcup_(i in P) x i)
  : F G / [set F i | i in P] `<=` [set G i | i in P] >-> F `<=` G}.
Proof.
move=> F G FG t [i Pi Fit]; have := FG (F i).
by move=> /(_ (ex_intro2 _ _ _ Pi erefl))[j Pj ji]; exists j => //; rewrite ji.
Qed.

Lemma subset_bigcap_r P : {homo (fun x : I -> set T => \bigcap_(i in P) x i)
  : F G / [set F i | i in P] `<=` [set G i | i in P] >-> G `<=` F}.
Proof.
by move=> F G FG t Gt i Pi; have [|j Pj <-] := FG (F i); [exists i|apply: Gt].
Qed.

Lemma eq_bigcupr P F G : (forall i, P i -> F i = G i) ->
  \bigcup_(i in P) F i = \bigcup_(i in P) G i.
Proof.
by move=> FG; rewrite eqEsubset; split; apply: subset_bigcup_r;
  move=> A [i ? <-]; exists i => //; rewrite FG.
Qed.

Lemma eq_bigcapr P F G : (forall i, P i -> F i = G i) ->
  \bigcap_(i in P) F i = \bigcap_(i in P) G i.
Proof.
by move=> FG; rewrite eqEsubset; split; apply: subset_bigcap_r;
  move=> A [i ? <-]; exists i => //; rewrite FG.
Qed.

Lemma setC_bigcup P F : ~` (\bigcup_(i in P) F i) = \bigcap_(i in P) ~` F i.
Proof.
by rewrite eqEsubset; split => [t PFt i Pi ?|t PFt [i Pi ?]];
  [apply PFt; exists i | exact: (PFt _ Pi)].
Qed.

Lemma setC_bigcap P F : ~` (\bigcap_(i in P) (F i)) = \bigcup_(i in P) ~` F i.
Proof.
apply: setC_inj; rewrite setC_bigcup setCK.
by apply: eq_bigcapr => ?; rewrite setCK.
Qed.

Lemma image_bigcup rT P F (f : T -> rT) :
  f @` (\bigcup_(i in P) (F i)) = \bigcup_(i in P) f @` F i.
Proof.
apply/seteqP; split=> [_/= [x [i Pi Fix <-]]|]; first by exists i.
by move=> _ [i Pi [x Fix <-]]; exists x => //; exists i.
Qed.

Lemma some_bigcap P F : some @` (\bigcap_(i in P) (F i)) =
  [set~ None] `&` \bigcap_(i in P) some @` F i.
Proof.
apply/seteqP; split.
  by move=> _ [x Fx <-]; split=> // i; exists x => //; apply: Fx.
by move=> [x|[//=]] [_ Fx]; exists x => //= i /Fx [y ? [<-]].
Qed.

Lemma bigcup_set_type P F : \bigcup_(i in P) F i = \bigcup_(j : P) F (val j).
Proof.
rewrite predeqE => x; split; last by move=> [[i/= /set_mem Pi] _ Fix]; exists i.
by move=> [i Pi Fix]; exists (SigSub (mem_set Pi)).
Qed.

Lemma eq_bigcupl P Q F : P `<=>` Q ->
  \bigcup_(i in P) F i = \bigcup_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_bigcapl P Q F : P `<=>` Q ->
  \bigcap_(i in P) F i = \bigcap_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_bigcup P Q F G : P `<=>` Q -> (forall i, P i -> F i = G i) ->
  \bigcup_(i in P) F i = \bigcup_(i in Q) G i.
Proof. by move=> /eq_bigcupl<- /eq_bigcupr->. Qed.

Lemma eq_bigcap P Q F G : P `<=>` Q -> (forall i, P i -> F i = G i) ->
  \bigcap_(i in P) F i = \bigcap_(i in Q) G i.
Proof. by move=> /eq_bigcapl<- /eq_bigcapr->. Qed.

Lemma bigcupU P F G : \bigcup_(i in P) (F i `|` G i) =
  (\bigcup_(i in P) F i) `|` (\bigcup_(i in P) G i).
Proof.
apply/predeqP => x; split=> [[i Pi [Fix|Gix]]|[[i Pi Fix]|[i Pi Gix]]];
  by [left; exists i|right; exists i|exists i =>//; left|exists i =>//; right].
Qed.

Lemma bigcapI P F G : \bigcap_(i in P) (F i `&` G i) =
  (\bigcap_(i in P) F i) `&` (\bigcap_(i in P) G i).
Proof.
apply: setC_inj; rewrite !(setCI, setC_bigcap) -bigcupU.
by apply: eq_bigcupr => *; rewrite setCI.
Qed.

Lemma bigcup_const P A : P !=set0 -> \bigcup_(_ in P) A = A.
Proof. by case=> j ?; rewrite predeqE => x; split=> [[i //]|Ax]; exists j. Qed.

Lemma bigcap_const P A : P !=set0 -> \bigcap_(_ in P) A = A.
Proof. by move=> PN0; apply: setC_inj; rewrite setC_bigcap bigcup_const. Qed.

Lemma bigcapIl P F A : P !=set0 ->
  \bigcap_(i in P) (F i `&` A) = \bigcap_(i in P) F i `&` A.
Proof. by move=> PN0; rewrite bigcapI bigcap_const. Qed.

Lemma bigcapIr P F A : P !=set0 ->
  \bigcap_(i in P) (A `&` F i) = A `&` \bigcap_(i in P) F i.
Proof. by move=> PN0; rewrite bigcapI bigcap_const. Qed.

Lemma bigcupUl P F A : P !=set0 ->
  \bigcup_(i in P) (F i `|` A) = \bigcup_(i in P) F i `|` A.
Proof. by move=> PN0; rewrite bigcupU bigcup_const. Qed.

Lemma bigcupUr P F A : P !=set0 ->
  \bigcup_(i in P) (A `|` F i) = A `|` \bigcup_(i in P) F i.
Proof. by move=> PN0; rewrite bigcupU bigcup_const. Qed.

Lemma bigcup_set0 F : \bigcup_(i in set0) F i = set0.
Proof. by rewrite eqEsubset; split => a // []. Qed.

Lemma bigcup_set1 F i : \bigcup_(j in [set i]) F j = F i.
Proof. by rewrite eqEsubset; split => ? => [[] ? -> //|]; exists i. Qed.

Lemma bigcap_set0 F : \bigcap_(i in set0) F i = setT.
Proof. by rewrite eqEsubset; split=> a // []. Qed.

Lemma bigcap_set1 F i : \bigcap_(j in [set i]) F j = F i.
Proof. by rewrite eqEsubset; split => ?; [exact|move=> ? ? ->]. Qed.

Lemma bigcup_nonempty P F :
  (\bigcup_(i in P) F i !=set0) <-> exists2 i, P i & F i !=set0.
Proof.
split=> [[t [i ? ?]]|[j ? [t ?]]]; by [exists i => //; exists t| exists t, j].
Qed.

Lemma bigcup0 P F :
  (forall i, P i -> F i = set0) -> \bigcup_(i in P) F i = set0.
Proof. by move=> PF; rewrite -subset0 => t -[i /PF ->]. Qed.

Lemma bigcap0 P F :
  (exists2 i, P i & F i = set0) -> \bigcap_(i in P) F i = set0.
Proof. by move=> [i Pi]; rewrite -!subset0 => Fi t Ft; apply/Fi/Ft. Qed.

Lemma bigcapT P F :
  (forall i, P i -> F i = setT) -> \bigcap_(i in P) F i = setT.
Proof. by move=> PF; rewrite -subTset => t -[i /PF ->]. Qed.

Lemma bigcupT P F :
  (exists2 i, P i & F i = setT) -> \bigcup_(i in P) F i = setT.
Proof. by move=> [i Pi F0]; rewrite -subTset => t; exists i; rewrite ?F0. Qed.

Lemma bigcup0P P F :
  (\bigcup_(i in P) F i = set0) <-> forall i, P i -> F i = set0.
Proof.
split=> [|/bigcup0//]; rewrite -subset0 => F0 i Pi; rewrite -subset0.
by move=> t Ft; apply: F0; exists i.
Qed.

Lemma bigcapTP P F :
  (\bigcap_(i in P) F i = setT) <-> forall i, P i -> F i = setT.
Proof.
split=> [|/bigcapT//]; rewrite -subTset => FT i Pi; rewrite -subTset.
by move=> t _; apply: FT.
Qed.

Lemma setI_bigcupr F P A :
  A `&` \bigcup_(i in P) F i = \bigcup_(i in P) (A `&` F i).
Proof.
rewrite predeqE => t; split => [[At [k ? ?]]|[k ? [At ?]]];
  by [exists k |split => //; exists k].
Qed.

Lemma setI_bigcupl F P A :
  \bigcup_(i in P) F i `&` A = \bigcup_(i in P) (F i `&` A).
Proof. by rewrite setIC setI_bigcupr//; under eq_bigcupr do rewrite setIC. Qed.

Lemma setU_bigcapr F P A :
  A `|` \bigcap_(i in P) F i = \bigcap_(i in P) (A `|` F i).
Proof.
apply: setC_inj; rewrite setCU !setC_bigcap setI_bigcupr.
by under eq_bigcupr do rewrite -setCU.
Qed.

Lemma setU_bigcapl F P A :
  \bigcap_(i in P) F i `|` A = \bigcap_(i in P) (F i `|` A).
Proof. by rewrite setUC setU_bigcapr//; under eq_bigcapr do rewrite setUC. Qed.

Lemma bigcup_mkcond P F :
  \bigcup_(i in P) F i = \bigcup_i if i \in P then F i else set0.
Proof.
rewrite predeqE => x; split=> [[i Pi Fix]|[i _]].
  by exists i => //; case: ifPn; rewrite (inE, notin_set).
by case: ifPn; rewrite (inE, notin_set) => Pi Fix; exists i.
Qed.

Lemma bigcup_mkcondr P Q F :
  \bigcup_(i in P `&` Q) F i = \bigcup_(i in P) if i \in Q then F i else set0.
Proof.
rewrite bigcup_mkcond [RHS]bigcup_mkcond; apply: eq_bigcupr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcup_mkcondl P Q F :
  \bigcup_(i in P `&` Q) F i = \bigcup_(i in Q) if i \in P then F i else set0.
Proof.
rewrite bigcup_mkcond [RHS]bigcup_mkcond; apply: eq_bigcupr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcap_mkcond F P :
  \bigcap_(i in P) F i = \bigcap_i if i \in P then F i else setT.
Proof.
apply: setC_inj; rewrite !setC_bigcap bigcup_mkcond; apply: eq_bigcupr => i _.
by case: ifP; rewrite ?setCT.
Qed.

Lemma bigcap_mkcondr P Q F :
  \bigcap_(i in P `&` Q) F i = \bigcap_(i in P) if i \in Q then F i else setT.
Proof.
rewrite bigcap_mkcond [RHS]bigcap_mkcond; apply: eq_bigcapr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcap_mkcondl P Q F :
  \bigcap_(i in P `&` Q) F i = \bigcap_(i in Q) if i \in P then F i else setT.
Proof.
rewrite bigcap_mkcond [RHS]bigcap_mkcond; apply: eq_bigcapr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcup_imset1 P (f : I -> T) : \bigcup_(x in P) [set f x] = f @` P.
Proof.
by rewrite eqEsubset; split=>[a [i ?]->| a [i ?]<-]; [apply: imageP | exists i].
Qed.

Lemma bigcup_setU F (X Y : set I) :
  \bigcup_(i in X `|` Y) F i = \bigcup_(i in X) F i `|` \bigcup_(i in Y) F i.
Proof.
rewrite predeqE => t; split=> [[z]|].
  by move=> [Xz|Yz]; [left|right]; exists z.
by move=> [[z Xz Fzy]|[z Yz Fxz]]; exists z => //; [left|right].
Qed.

Lemma bigcap_setU F (X Y : set I) :
  \bigcap_(i in X `|` Y) F i = \bigcap_(i in X) F i `&` \bigcap_(i in Y) F i.
Proof. by apply: setC_inj; rewrite !(setCI, setC_bigcap) bigcup_setU. Qed.

Lemma bigcup_setU1 F (x : I) (X : set I) :
  \bigcup_(i in x |` X) F i = F x `|` \bigcup_(i in X) F i.
Proof. by rewrite bigcup_setU bigcup_set1. Qed.

Lemma bigcap_setU1 F (x : I) (X : set I) :
  \bigcap_(i in x |` X) F i = F x `&` \bigcap_(i in X) F i.
Proof. by rewrite bigcap_setU bigcap_set1. Qed.

Lemma bigcup_setD1 (x : I) F (X : set I) : X x ->
  \bigcup_(i in X) F i = F x `|` \bigcup_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -bigcup_setU1 setD1K. Qed.

Lemma bigcap_setD1 (x : I) F (X : set I) : X x ->
  \bigcap_(i in X) F i = F x `&` \bigcap_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -bigcap_setU1 setD1K. Qed.

Lemma setC_bigsetU U (s : seq T) (f : T -> set U) (P : pred T) :
   (~` \big[setU/set0]_(t <- s | P t) f t) = \big[setI/setT]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setC0 ?setCU. Qed.

Lemma setC_bigsetI U (s : seq T) (f : T -> set U) (P : pred T) :
   (~` \big[setI/setT]_(t <- s | P t) f t) = \big[setU/set0]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setCT ?setCI. Qed.

Lemma bigcupDr (F : I -> set T) (P : set I) (A : set T) : P !=set0 ->
  \bigcap_(i in P) (A `\` F i) = A `\` \bigcup_(i in P) F i.
Proof. by move=> PN0; rewrite setDE setC_bigcup -bigcapIr. Qed.

Lemma setD_bigcupl (F : I -> set T) (P : set I) (A : set T) :
  \bigcup_(i in P) F i `\` A = \bigcup_(i in P) (F i `\` A).
Proof. by rewrite setDE setI_bigcupl; under eq_bigcupr do rewrite -setDE. Qed.

Lemma bigcup_bigcup_dep {J : Type} (F : I -> J -> set T) (P : set I) (Q : I -> set J) :
  \bigcup_(i in P) \bigcup_(j in Q i) F i j =
  \bigcup_(k in P `*`` Q) F k.1 k.2.
Proof.
apply/predeqP => x; split=> [[i Pi [j Pj Fijx]]|]; first by exists (i, j).
by move=> [[/= i j] [Pi Qj] Fijx]; exists i => //; exists j.
Qed.

Lemma bigcup_bigcup {J : Type} (F : I -> J -> set T) (P : set I) (Q : set J) :
  \bigcup_(i in P) \bigcup_(j in Q) F i j =
  \bigcup_(k in P `*` Q) F k.1 k.2.
Proof. exact: bigcup_bigcup_dep. Qed.

Lemma bigcupID (Q : set I) (F : I -> set T) (P : set I) :
  \bigcup_(i in P) F i =
    (\bigcup_(i in P `&` Q) F i) `|` (\bigcup_(i in P `&` ~` Q) F i).
Proof. by rewrite -bigcup_setU -setIUr setUv setIT. Qed.

Lemma bigcapID (Q : set I) (F : I -> set T) (P : set I) :
  \bigcap_(i in P) F i =
    (\bigcap_(i in P `&` Q) F i) `&` (\bigcap_(i in P `&` ~` Q) F i).
Proof. by rewrite -bigcap_setU -setIUr setUv setIT. Qed.

End bigop_lemmas.
Arguments bigcup_setD1 {T I} x.
Arguments bigcap_setD1 {T I} x.

Definition bigcup2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0 then A else if i == 1 then B else set0.
Arguments bigcup2 T A B n /.

Lemma bigcup2E T (A B : set T) : \bigcup_i (bigcup2 A B) i = A `|` B.
Proof.
rewrite predeqE => t; split=> [|[At|Bt]]; [|by exists 0|by exists 1].
by case=> -[_ At|[_ Bt|//]]; [left|right].
Qed.

Lemma bigcup2inE T (A B : set T) : \bigcup_(i < 2) (bigcup2 A B) i = A `|` B.
Proof.
rewrite predeqE => t; split=> [|[At|Bt]]; [|by exists 0|by exists 1].
by case=> -[_ At|[_ Bt|//]]; [left|right].
Qed.

Definition bigcap2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0 then A else if i == 1 then B else setT.
Arguments bigcap2 T A B n /.

Lemma bigcap2E T (A B : set T) : \bigcap_i (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2E /bigcap2 /bigcup2.
by apply: eq_bigcupr => -[|[|[]]]//=; rewrite setCT.
Qed.

Lemma bigcap2inE T (A B : set T) : \bigcap_(i < 2) (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2inE /bigcap2 /bigcup2.
by apply: eq_bigcupr => // -[|[|[]]].
Qed.

Lemma bigcup_sub T I (F : I -> set T) (D : set T) (P : set I) :
  (forall i, P i -> F i `<=` D) -> \bigcup_(i in P) F i `<=` D.
Proof. by move=> FD t [n Pn Fnt]; apply: (FD n). Qed.

Lemma sub_bigcap T I (F : I -> set T) (D : set T) (P : set I) :
  (forall i, P i -> D `<=` F i) -> D `<=` \bigcap_(i in P) F i.
Proof. by move=> DF t Dt n Pn; apply: DF. Qed.

Lemma subset_bigcup T I [P : set I] [F G : I -> set T] :
  (forall i, P i -> F i `<=` G i) ->
  \bigcup_(i in P) F i `<=` \bigcup_(i in P) G i.
Proof.
by move=> FG; apply: bigcup_sub => i Pi + /(FG _ Pi); apply: bigcup_sup.
Qed.

Lemma subset_bigcap T I [P : set I] [F G : I -> set T] :
  (forall i, P i -> F i `<=` G i) ->
  \bigcap_(i in P) F i `<=` \bigcap_(i in P) G i.
Proof.
move=> FG; apply: sub_bigcap => i Pi x Fx; apply: FG => //.
exact: bigcap_inf Fx.
Qed.

Lemma bigcup_image {aT rT I} (P : set aT) (f : aT -> I) (F : I -> set rT) :
  \bigcup_(x in f @` P) F x = \bigcup_(x in P) F (f x).
Proof.
rewrite eqEsubset; split=> x; first by case=> j [] i pi <- Xfix; exists i.
by case=> i Pi Ffix; exists (f i); [exists i|].
Qed.

Lemma bigcap_set_type {I T} (P : set I) (F : I -> set T) :
   \bigcap_(i in P) F i = \bigcap_(j : P) F (val j).
Proof. by apply: setC_inj; rewrite !setC_bigcap bigcup_set_type. Qed.

Lemma bigcap_image {aT rT I} (P : set aT) (f : aT -> I) (F : I -> set rT) :
  \bigcap_(x in f @` P) F x = \bigcap_(x in P) F (f x).
Proof. by apply: setC_inj; rewrite !setC_bigcap bigcup_image. Qed.

Lemma bigcup_fset {I : choiceType} {U : Type}
    (F : I -> set U) (X : {fset I}) :
  \bigcup_(i in [set i | i \in X]) F i = \big[setU/set0]_(i <- X) F i :> set U.
Proof.
elim/finSet_rect: X => X IHX; have [->|[x xX]] := fset_0Vmem X.
  by rewrite big_seq_fset0 -subset0 => x [].
rewrite -(fsetD1K xX) set_fsetU set_fset1 big_fsetU1 ?inE ?eqxx//=.
by rewrite bigcup_setU1 IHX// fproperD1.
Qed.

Lemma bigcap_fset {I : choiceType} {U : Type}
    (F : I -> set U) (X : {fset I}) :
  \bigcap_(i in [set i | i \in X]) F i = \big[setI/setT]_(i <- X) F i :> set U.
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_fset. Qed.

Lemma bigcup_fsetU1 {T U : choiceType} (F : T -> set U) (x : T) (X : {fset T}) :
  \bigcup_(i in [set j | j \in x |` X]%fset) F i =
  F x `|` \bigcup_(i in [set j | j \in X]) F i.
Proof. by rewrite set_fsetU1 bigcup_setU1. Qed.

Lemma bigcap_fsetU1 {T U : choiceType} (F : T -> set U) (x : T) (X : {fset T}) :
  \bigcap_(i in [set j | j \in x |` X]%fset) F i =
  F x `&` \bigcap_(i in [set j | j \in X]) F i.
Proof. by rewrite set_fsetU1 bigcap_setU1. Qed.

Lemma bigcup_fsetD1 {T U : choiceType} (x : T) (F : T -> set U) (X : {fset T}) :
    x \in X ->
  \bigcup_(i in [set i | i \in X]%fset) F i =
  F x `|` \bigcup_(i in [set i | i \in X `\ x]%fset) F i.
Proof. by move=> Xx; rewrite (bigcup_setD1 x)// set_fsetD1. Qed.
Arguments bigcup_fsetD1 {T U} x.

Lemma bigcap_fsetD1 {T U : choiceType} (x : T) (F : T -> set U) (X : {fset T}) :
    x \in X ->
  \bigcap_(i in [set i | i \in X]%fset) F i =
  F x `&` \bigcap_(i in [set i | i \in X `\ x]%fset) F i.
Proof. by move=> Xx; rewrite (bigcap_setD1 x)// set_fsetD1. Qed.
Arguments bigcup_fsetD1 {T U} x.

Section bigcup_set.
Variables (T : choiceType) (U : Type).

Lemma bigcup_set_cond (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcup_(t in [set x | (x \in s) && P x]) (f t) =
  \big[setU/set0]_(t <- s | P t) (f t).
Proof.
elim: s => [/=|h s ih]; first by rewrite set_nil bigcup_set0 big_nil.
rewrite big_cons -ih predeqE => u; split=> [[t /andP[]]|].
- rewrite inE => /orP[/eqP ->{t} -> fhu|ts Pt ftu]; first by left.
  case: ifPn => Ph; first by right; exists t => //; apply/andP; split.
  by exists t => //; apply/andP; split.
- case: ifPn => [Ph [fhu|[t /andP[ts Pt] ftu]]|Ph [t /andP[ts Pt ftu]]].
  + by exists h => //; apply/andP; split => //; rewrite mem_head.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
Qed.

Lemma bigcup_set (s : seq T) (f : T -> set U) :
  \bigcup_(t in [set` s]) (f t) = \big[setU/set0]_(t <- s) (f t).
Proof.
rewrite -(bigcup_set_cond s f xpredT); congr (\bigcup_(t in mkset _) _).
by rewrite funeqE => t; rewrite andbT.
Qed.

Lemma bigcap_set_cond (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcap_(t in [set x | (x \in s) && P x]) (f t) =
  \big[setI/setT]_(t <- s | P t) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_set_cond. Qed.

Lemma bigcap_set (s : seq T) (f : T -> set U) :
  \bigcap_(t in [set` s]) (f t) = \big[setI/setT]_(t <- s) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_set. Qed.

End bigcup_set.

Lemma bigcup_pred [T : finType] [U : Type] (P : {pred T}) (f : T -> set U) :
  \bigcup_(t in [set` P]) f t = \big[setU/set0]_(t in P) f t.
Proof.
apply/predeqP => u; split=> [[x Px fxu]|]; first by rewrite (bigD1 x)//; left.
move=> /mem_set; rewrite (@big_morph _ _ (fun X => u \in X) false orb).
- by rewrite big_has_cond => /hasP[x _ /andP[xP]]; rewrite inE => ufx; exists x.
- by move=> /= x y; apply/idP/orP; rewrite !inE.
- by rewrite in_set0.
Qed.

Section smallest.
Context {T} (C : set T -> Prop) (G : set T).

Definition smallest := \bigcap_(A in [set M | C M /\ G `<=` M]) A.

Lemma sub_smallest X : X `<=` G -> X `<=` smallest.
Proof. by move=> XG A /XG GA Y /= [PY]; apply. Qed.

Lemma sub_gen_smallest : G `<=` smallest. Proof. exact: sub_smallest. Qed.

Lemma smallest_sub X : C X -> G `<=` X -> smallest `<=` X.
Proof. by move=> XC GX A; apply. Qed.

Lemma smallest_id : C G -> smallest = G.
Proof.
by move=> Cs; apply/seteqP; split; [apply: smallest_sub|apply: sub_smallest].
Qed.

End smallest.
#[global] Hint Resolve sub_gen_smallest : core.

Lemma sub_smallest2r {T} (C : set T-> Prop) G1 G2 :
   C (smallest C G2) -> G1 `<=` G2 -> smallest C G1 `<=` smallest C G2.
Proof. by move=> *; apply: smallest_sub=> //; apply: sub_smallest. Qed.

Lemma sub_smallest2l {T} (C1 C2 : set T -> Prop) :
   (forall G, C2 G -> C1 G) ->
   forall G, smallest C1 G `<=` smallest C2 G.
Proof. by move=> C12 G X sX M [/C12 C1M GM]; apply: sX. Qed.

Section bigop_nat_lemmas.
Context {T : Type}.
Implicit Types (A : set T) (F : nat -> set T).

Lemma bigcup_mkord n F : \bigcup_(i < n) F i = \big[setU/set0]_(i < n) F i.
Proof.
rewrite -(big_mkord xpredT F) -bigcup_set.
by apply: eq_bigcupl; split=> i; rewrite /= mem_index_iota leq0n.
Qed.

Lemma bigcap_mkord n F : \bigcap_(i < n) F i = \big[setI/setT]_(i < n) F i.
Proof. by apply: setC_inj; rewrite setC_bigsetI setC_bigcap bigcup_mkord. Qed.

Lemma bigsetU_sup i n F : (i < n)%N -> F i `<=` \big[setU/set0]_(j < n) F j.
Proof. by move: n => // n ni; rewrite -bigcup_mkord; exact/bigcup_sup. Qed.

Lemma bigsetU_bigcup F n : \big[setU/set0]_(i < n) F i `<=` \bigcup_k F k.
Proof. by rewrite -bigcup_mkord => x [k _ Fkx]; exists k. Qed.

Lemma bigsetU_bigcup2 (A B : set T) :
   \big[setU/set0]_(i < 2) bigcup2 A B i = A `|` B.
Proof. by rewrite -bigcup_mkord bigcup2inE. Qed.

Lemma bigsetI_bigcap2 (A B : set T) :
   \big[setI/setT]_(i < 2) bigcap2 A B i = A `&` B.
Proof. by rewrite -bigcap_mkord bigcap2inE. Qed.

Lemma bigcup_splitn n F :
  \bigcup_i F i = \big[setU/set0]_(i < n) F i `|` \bigcup_i F (n + i).
Proof.
rewrite -bigcup_mkord -(bigcup_image _ (addn n)) -bigcup_setU.
apply: eq_bigcupl; split=> // k _.
have [ltkn|lenk] := ltnP k n; [left => //|right].
by exists (k - n); rewrite // subnKC.
Qed.

Lemma bigcap_splitn n F :
  \bigcap_i F i = \big[setI/setT]_(i < n) F i `&` \bigcap_i F (n + i).
Proof.
by apply: setC_inj; rewrite setCI !setC_bigcap (bigcup_splitn n) setC_bigsetI.
Qed.

Lemma subset_bigsetU F :
  {homo (fun n => \big[setU/set0]_(i < n) F i) : n m / (n <= m) >-> n `<=` m}.
Proof.
move=> m n mn; rewrite -!bigcup_mkord => x [i im Fix].
by exists i => //=; rewrite (leq_trans im).
Qed.

Lemma subset_bigsetI F :
  {homo (fun n => \big[setI/setT]_(i < n) F i) : n m / (n <= m) >-> m `<=` n}.
Proof.
move=> m n mn; rewrite -setCS !setC_bigsetI.
exact: (@subset_bigsetU (setC \o F)).
Qed.

Lemma subset_bigsetU_cond (P : pred nat) F :
  {homo (fun n => \big[setU/set0]_(i < n | P i) F i)
    : n m / (n <= m) >-> n `<=` m}.
Proof.
move=> n m nm; rewrite big_mkcond [in X in _ `<=` X]big_mkcond/=.
exact: (@subset_bigsetU (fun i => if P i then F i else _)).
Qed.

Lemma subset_bigsetI_cond (P : pred nat) F :
  {homo (fun n => \big[setI/setT]_(i < n | P i) F i)
    : n m / (n <= m) >-> m `<=` n}.
Proof.
move=> n m nm; rewrite big_mkcond [in X in _ `<=` X]big_mkcond/=.
exact: (@subset_bigsetI (fun i => if P i then F i else _)).
Qed.

End bigop_nat_lemmas.

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

Definition fun_of_rel {aT} {rT : choiceType} (f0 : aT -> rT)
  (f : aT -> rT -> Prop) := fun x => xget (f0 x) (f x).

Lemma fun_of_relP {aT} {rT : choiceType} (f : aT -> rT -> Prop) (f0 : aT -> rT) a :
  f a !=set0 -> f a (fun_of_rel f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_rel; apply: xgetI fab. Qed.

Lemma fun_of_rel_uniq {aT} {rT : choiceType}
    (f : aT -> rT -> Prop) (f0 : aT -> rT) a :
  is_subset1 (f a) -> forall b, f a b ->  fun_of_rel f0 f a = b.
Proof. by move=> fa1 b /xget_subset1 xgeteq; rewrite /fun_of_rel xgeteq. Qed.

Lemma forall_sig T (A : set T) (P : {x | x \in A} -> Prop) :
  (forall u : {x | x \in A}, P u) =
  (forall u : T, forall (a : A u), P (exist _ u (mem_set a))).
Proof.
rewrite propeqE; split=> [+ u a|PA [u a]]; first exact.
have Au : A u by rewrite inE in a.
by rewrite (Prop_irrelevance a (mem_set Au)); apply: PA.
Qed.

Lemma in_setP {U} (A : set U) (P : U -> Prop) :
  {in A, forall x, P x} <-> forall x, A x -> P x.
Proof. by split=> AP x; have := AP x; rewrite inE. Qed.

Lemma in_set2P {U V} (A : set U) (B : set V) (P : U -> V -> Prop) :
  {in A & B, forall x y, P x y} <-> (forall x y, A x -> B y -> P x y).
Proof. by split=> AP x y; have := AP x y; rewrite !inE. Qed.

Lemma in1TT [T1] [P1 : T1 -> Prop] :
  {in [set: T1], forall x : T1, P1 x : Prop} -> forall x : T1, P1 x : Prop.
Proof. by move=> + *; apply; rewrite !inE. Qed.

Lemma in2TT [T1 T2] [P2 : T1 -> T2 -> Prop] :
  {in [set: T1] & [set: T2], forall (x : T1) (y : T2), P2 x y : Prop} ->
  forall (x : T1) (y : T2), P2 x y : Prop.
Proof. by move=> + *; apply; rewrite !inE. Qed.

Lemma in3TT [T1 T2 T3] [P3 : T1 -> T2 -> T3 -> Prop] :
  {in [set: T1] & [set: T2] & [set: T3], forall (x : T1) (y : T2) (z : T3), P3 x y z : Prop} ->
  forall (x : T1) (y : T2) (z : T3), P3 x y z : Prop.
Proof. by move=> + *; apply; rewrite !inE. Qed.

Lemma inTT_bij [T1 T2 : Type] [f : T1 -> T2] :
  {in [set: T1], bijective f} -> bijective f.
Proof. by case=> [g /in1TT + /in1TT +]; exists g. Qed.

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
Canonical nat_pointedType := PointedType nat 0.
Canonical prod_pointedType (T T' : pointedType) :=
  PointedType (T * T') (point, point).
Canonical matrix_pointedType m n (T : pointedType) :=
  PointedType 'M[T]_(m, n) (\matrix_(_, _) point)%R.
Canonical option_pointedType (T : choiceType) := PointedType (option T) None.
Canonical pointed_fset {T : choiceType} := PointedType {fset T} fset0.

Notation get := (xget point).
Notation "[ 'get' x | E ]" := (get [set x | E])
  (at level 0, x name, format "[ 'get'  x  |  E ]", only printing) : form_scope.
Notation "[ 'get' x : T | E ]" := (get (fun x : T  => E))
  (at level 0, x name, format "[ 'get'  x  :  T  |  E ]", only parsing) : form_scope.
Notation "[ 'get' x | E ]" := (get (fun x => E))
  (at level 0, x name, format "[ 'get'  x  |  E ]") : form_scope.

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

Variant squashed T : Prop := squash (x : T).
Arguments squash {T} x.
Notation "$| T |" := (squashed T) : form_scope.
Tactic Notation "squash" uconstr(x) := (exists; refine x) ||
   match goal with |- $| ?T | => exists; refine [the T of x] end.

Definition unsquash {T} (s : $|T|) : T :=
  projT1 (cid (let: squash x := s in @ex_intro T _ x isT)).
Lemma unsquashK {T} : cancel (@unsquash T) squash. Proof. by move=> []. Qed.

(* Empty types *)

Module Empty.

Definition mixin_of T := T -> False.

Section EqMixin.
Variables (T : Type) (m : mixin_of T).
Definition eq_op (x y : T) := true.
Lemma eq_opP : Equality.axiom eq_op. Proof. by []. Qed.
Definition eqMixin := EqMixin eq_opP.
End EqMixin.

Section ChoiceMixin.
Variables (T : Type) (m : mixin_of T).
Definition find of pred T & nat : option T := None.
Lemma findP (P : pred T) (n : nat) (x : T) :  find P n = Some x -> P x.
Proof. by []. Qed.
Lemma ex_find (P : pred T) : (exists x : T, P x) -> exists n : nat, find P n.
Proof. by case. Qed.
Lemma eq_find (P Q : pred T) : P =1 Q -> find P =1 find Q.
Proof. by []. Qed.
Definition choiceMixin := Choice.Mixin findP ex_find eq_find.
End ChoiceMixin.

Section CountMixin.
Variables (T : Type) (m : mixin_of T).
Definition pickle : T -> nat := fun=> 0.
Definition unpickle : nat -> option T := fun=> None.
Lemma pickleK : pcancel pickle unpickle. Proof. by []. Qed.
Definition countMixin := CountMixin pickleK.
End CountMixin.

Section FinMixin.
Variables (T : countType) (m : mixin_of T).
Lemma fin_axiom : Finite.axiom ([::] : seq T). Proof. by []. Qed.
Definition finMixin := FinMixin fin_axiom.
End FinMixin.

Section ClassDef.

Set Primitive Projections.
Record class_of T := Class {
  base : Finite.class_of T;
  mixin : mixin_of T
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Finite.class_of.

Structure type : Type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack (m0 : mixin_of T) :=
  fun bT b & phant_id (Finite.class bT) b =>
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT class.
Definition finType := @Finite.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Finite.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Coercion finType : type >-> Finite.type.
Canonical finType.
Notation emptyType := type.
Notation EmptyType T m := (@pack T m _ _ id _ id).
Notation "[ 'emptyType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'emptyType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'emptyType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'emptyType'  'of'  T ]") : form_scope.
Coercion eqMixin : mixin_of >-> Equality.mixin_of.
Coercion choiceMixin : mixin_of >-> Choice.mixin_of.
Coercion countMixin : mixin_of >-> Countable.mixin_of.
End Exports.

End Empty.
Export Empty.Exports.

Definition False_emptyMixin : Empty.mixin_of False := id.
Canonical False_eqType := EqType False False_emptyMixin.
Canonical False_choiceType := ChoiceType False False_emptyMixin.
Canonical False_countType := CountType False False_emptyMixin.
Canonical False_finType := FinType False (Empty.finMixin False_emptyMixin).
Canonical False_emptyType := EmptyType False False_emptyMixin.

Definition void_emptyMixin : Empty.mixin_of void := @of_void _.
Canonical void_emptyType := EmptyType void void_emptyMixin.

Definition no {T : emptyType} : T -> False :=
  let: Empty.Pack _ (Empty.Class _ f) := T in f.
Definition any {T : emptyType} {U}  : T -> U := @False_rect _ \o no.

Lemma empty_eq0 {T : emptyType} : all_equal_to (set0 : set T).
Proof. by move=> X; apply/setF_eq0/no. Qed.

Definition quasi_canonical_of T C (sort : C -> T) (alt  : emptyType -> T):=
    forall (G : T -> Type), (forall s : emptyType, G (alt s)) -> (forall x, G (sort x)) ->
  forall x, G x.
Notation quasi_canonical_ sort alt := (@quasi_canonical_of _ _ sort alt).
Notation quasi_canonical T C := (@quasi_canonical_of T C id id).

Lemma qcanon T C (sort : C -> T) (alt : emptyType -> T) :
    (forall x, (exists y : emptyType, alt y = x) + (exists y, sort y = x)) ->
  quasi_canonical_ sort alt.
Proof. by move=> + G Cx Gs x => /(_ x)[/cid[y <-]|/cid[y <-]]. Qed.
Arguments qcanon {T C sort alt} x.

Lemma choicePpointed : quasi_canonical choiceType pointedType.
Proof.
apply: qcanon => T; have [/unsquash x|/(_ (squash _)) TF] := pselect $|T|.
  by right; exists (PointedType T x); case: T x.
left.
pose cT := CountType _ (TF : Empty.mixin_of T).
pose fM := Empty.finMixin (TF : Empty.mixin_of cT).
exists (EmptyType (FinType _ fM) TF) => //=.
by case: T TF @cT @fM.
Qed.

Lemma eqPpointed : quasi_canonical eqType pointedType.
Proof.
by apply: qcanon; elim/eqPchoice; elim/choicePpointed => [[T F]|T];
   [left; exists (Empty.Pack F) | right; exists T].
Qed.
Lemma Ppointed : quasi_canonical Type pointedType.
Proof.
by apply: qcanon; elim/Peq; elim/eqPpointed => [[T F]|T];
   [left; exists (Empty.Pack F) | right; exists T].
Qed.

Section partitions.

Definition trivIset T I (D : set I) (F : I -> set T) :=
  forall i j : I, D i -> D j -> F i `&` F j !=set0 -> i = j.

Lemma trivIset_set0 {I T} (D : set I) : trivIset D (fun=> set0 : set T).
Proof. by move=> i j Di Dj; rewrite setI0 => /set0P; rewrite eqxx. Qed.

Lemma trivIsetP {T} {I : eqType} {D : set I} {F : I -> set T} :
  trivIset D F <->
  forall i j : I, D i -> D j -> i != j -> F i `&` F j = set0.
Proof.
split=> tDF i j Di Dj; first by apply: contraNeq => /set0P/tDF->.
by move=> /set0P; apply: contraNeq => /tDF->.
Qed.

Lemma trivIset_bigsetUI T (D : {pred nat}) (F : nat -> set T) : trivIset D F ->
  forall n m, D m -> n <= m -> \big[setU/set0]_(i < n | D i) F i `&` F m = set0.
Proof.
move=> /trivIsetP tA; elim => [|n IHn] m Dm.
  by move=> _; rewrite big_ord0 set0I.
move=> lt_nm; rewrite big_mkcond/= big_ord_recr -big_mkcond/=.
rewrite setIUl IHn 1?ltnW// set0U.
by case: ifPn => [Dn|NDn]; rewrite ?set0I// tA// ltn_eqF.
Qed.

Lemma trivIset_setIl (T I : Type) (D : set I) (F : I -> set T) (G : I -> set T) :
  trivIset D F -> trivIset D (fun i => G i `&` F i).
Proof.
by move=> tF i j Di Dj [x [[Gix Fix] [Gjx Fjx]]]; apply tF => //; exists x.
Qed.

Lemma trivIset_setIr (T I : Type) (D : set I) (F : I -> set T) (G : I -> set T) :
  trivIset D F -> trivIset D (fun i => F i `&` G i).
Proof.
by move=> tF i j Di Dj [x [[Fix Gix] [Fjx Gjx]]]; apply tF => //; exists x.
Qed.

#[deprecated(note="Use trivIset_setIl instead")]
Lemma trivIset_setI T I D (F : I -> set T) X :
  trivIset D F -> trivIset D (fun i => X `&` F i).
Proof. exact: trivIset_setIl. Qed.

Lemma sub_trivIset I T (D D' : set I) (F : I -> set T) :
  D `<=` D' -> trivIset D' F -> trivIset D F.
Proof. by move=> DD' Ftriv i j /DD' + /DD' + /Ftriv->//. Qed.

Lemma trivIset_bigcup2 T (A B : set T) :
  (A `&` B = set0) = trivIset setT (bigcup2 A B).
Proof.
apply/propext; split=> [AB0|/trivIsetP/(_ 0 1 Logic.I Logic.I erefl)//].
apply/trivIsetP => -[/=|]; rewrite /bigcup2 /=.
- by move=> [//|[_ _ _ //|j _ _ _]]; rewrite setI0.
- move=> [[j _ _|]|i j _ _ _]; [by rewrite setIC| |by rewrite set0I].
  by move=> [//|j _ _ _]; rewrite setI0.
Qed.

Lemma trivIset_image (T I I' : Type) (D : set I) (f : I -> I') (F : I' -> set T) :
  trivIset D (F \o f) -> trivIset (f @` D) F.
Proof.
by move=> trivF i j [{}i Di <-] [{}j Dj <-] Ffij; congr (f _); apply: trivF.
Qed.
Arguments trivIset_image {T I I'} D f F.

Lemma trivIset_comp (T I I' : Type) (D : set I) (f : I -> I') (F : I' -> set T) :
    {in D &, injective f} ->
  trivIset D (F \o f) = trivIset (f @` D) F.
Proof.
move=> finj; apply/propext; split; first exact: trivIset_image.
move=> trivF i j Di Dj Ffij; apply: finj; rewrite ?in_setE//.
by apply: trivF => //=; [exists i| exists j].
Qed.

Definition cover T I D (F : I -> set T) := \bigcup_(i in D) F i.

Lemma cover_restr T I D' D (F : I -> set T) :
  D `<=` D' -> (forall i, D' i -> ~ D i -> F i = set0) ->
  cover D F = cover D' F.
Proof.
move=> DD' D'DF; rewrite /cover eqEsubset; split=> [r [i Di Fit]|r [i D'i Fit]].
- by have [D'i|] := pselect (D' i); [exists i | have := DD' _ Di].
- by have [Di|Di] := pselect (D i); [exists i | move: Fit; rewrite (D'DF i)].
Qed.

Lemma eqcover_r T I D (F G : I -> set T) :
  [set F i | i in D] = [set G i | i in D] ->
  cover D F = cover D G.
Proof.
move=> FG.
rewrite eqEsubset; split => [t [i Di Fit]|t [i Di Git]].
  have [j Dj GF] : [set G i | i in D] (F i) by rewrite -FG /mkset; exists i.
  by exists j => //; rewrite GF.
have [j Dj GF] : [set F i | i in D] (G i) by rewrite FG /mkset; exists i.
by exists j => //; rewrite GF.
Qed.

Definition partition T I D (F : I -> set T) (A : set T) :=
  [/\ cover D F = A, trivIset D F & forall i, D i -> F i !=set0].

Definition pblock_index T (I : pointedType) D (F : I -> set T) (x : T) :=
  [get i | D i /\ F i x].

Definition pblock T (I : pointedType) D (F : I -> set T) (x : T) :=
  F (pblock_index D F x).

(* TODO: theory of trivIset, cover, partition, pblock_index and pblock *)

Notation trivIsets X := (trivIset X id).

Lemma trivIset_sets T I D (F : I -> set T) :
  trivIset D F -> trivIsets [set F i | i in D].
Proof. exact: trivIset_image. Qed.

Lemma trivIset_widen T I D' D (F : I -> set T) :
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

Lemma perm_eq_trivIset {T : eqType} (s1 s2 : seq (set T)) (D : set nat) :
  [set k | (k < size s1)] `<=` D -> perm_eq s1 s2 ->
  trivIset D (fun i => nth set0 s1 i) -> trivIset D (fun i => nth set0 s2 i).
Proof.
move=> s1D; rewrite perm_sym => /(perm_iotaP set0)[s ss1 s12] /trivIsetP ts1.
apply/trivIsetP => i j Di Dj ij.
rewrite {}s12 {s2}; have [si|si] := ltnP i (size s); last first.
  by rewrite (nth_default set0) ?size_map// set0I.
rewrite (nth_map O) //; have [sj|sj] := ltnP j (size s); last first.
  by rewrite (nth_default set0) ?size_map// setI0.
have nth_mem k : k < size s -> nth O s k \in iota 0 (size s1).
  by move=> ?; rewrite -(perm_mem ss1) mem_nth.
rewrite (nth_map O)// ts1 ?(nth_uniq,(perm_uniq ss1),iota_uniq)//; apply/s1D.
- by have := nth_mem _ si; rewrite mem_iota leq0n add0n.
- by have := nth_mem _ sj; rewrite mem_iota leq0n add0n.
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
  [get t : Tp | (forall s, sval A s -> R s t) /\
    forall r, (forall s, sval A s -> R s r) -> R t r].
Let succ := fun s => [get t : Tp | R s t /\ s <> t /\
  forall r, R s r -> R r t -> r = s \/ r = t].

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
  by apply: eq_exist; rewrite predeqE=> ?; split=> [/sAB|/sBA].
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
  by right; apply: eq_exist; rewrite predeqE => r; split=> [/sBAs|[/sAB|->]].
left; case: A tub Astot sBAs sAB => A Atot /= tub Astot sBAs sAB.
apply: eq_exist; rewrite predeqE => r; split=> [Br|/sAB] //.
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
  by move=> eqRst; apply/eq_exist/ceqR_uniq.
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
Implicit Types (A : set T) (x y z : T).

Definition ubound A : set T := [set y | forall x, A x -> (x <= y)%O].
Definition lbound A : set T := [set y | forall x, A x -> (y <= x)%O].

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

Definition has_ubound A := ubound A !=set0.
Definition has_sup A := A !=set0 /\ has_ubound A.
Definition has_lbound A := lbound A !=set0.
Definition has_inf A := A !=set0 /\ has_lbound A.

Lemma has_ub_set1 x : has_ubound [set x].
Proof. by exists x; rewrite ub_set1. Qed.

Lemma has_inf0 : ~ has_inf (@set0 T).
Proof. by rewrite /has_inf not_andP; left; apply/set0P/negP/negPn. Qed.

Lemma has_sup0 : ~ has_sup (@set0 T).
Proof. by rewrite /has_sup not_andP; left; apply/set0P/negP/negPn. Qed.

Lemma has_sup1 x : has_sup [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma has_inf1 x : has_inf [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma subset_has_lbound A B : A `<=` B -> has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma subset_has_ubound A B : A `<=` B -> has_ubound B -> has_ubound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma downP A x : (exists2 y, A y & (x <= y)%O) <-> down A x.
Proof. by split => [[y Ay xy]|[y [Ay xy]]]; [exists y| exists y]. Qed.

Definition isLub A m := ubound A m /\ forall b, ubound A b -> (m <= b)%O.

Definition supremums A := ubound A `&` lbound (ubound A).

Lemma supremums1 x : supremums [set x] = [set x].
Proof.
rewrite /supremums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite ub_set1|exact: lb_ub_refl].
by rewrite ub_set1 => xy /lb_ub_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_supremums A : is_subset1 (supremums A).
Proof.
move=> x y [Ax xA] [Ay yA]; apply/eqP.
by rewrite eq_le (ub_lb_ub Ax yA) (ub_lb_ub Ay xA).
Qed.

Definition supremum x0 A := if A == set0 then x0 else xget x0 (supremums A).

Lemma supremum_out x0 A : ~ has_sup A -> supremum x0 A = x0.
Proof.
move=> hsA; rewrite /supremum; case: ifPn => // /set0P[/= x Ax].
case: xgetP => //= _ -> [uA _]; exfalso.
by apply: hsA; split; [exists x|exists (xget x0 (supremums A))].
Qed.

Lemma supremum0 x0 : supremum x0 set0 = x0.
Proof. by rewrite /supremum eqxx. Qed.

Lemma supremum1 x0 x : supremum x0 [set x] = x.
Proof.
rewrite /supremum ifF; last first.
  by apply/eqP; rewrite predeqE => /(_ x)[+ _]; apply.
by rewrite supremums1; case: xgetP => // /(_ x) /(_ erefl).
Qed.

Definition infimums A := lbound A `&` ubound (lbound A).

Lemma infimums1 x : infimums [set x] = [set x].
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

Definition infimum x0 A := if A == set0 then x0 else xget x0 (infimums A).

End UpperLowerTheory.

Section UpperLowerOrderTheory.
Import Order.TTheory.
Variables (d : unit) (T : orderType d).
Implicit Types (A : set T) (x y z : T).

Lemma ge_supremum_Nmem x0 A t :
  supremums A !=set0 -> A t -> (supremum x0 A >= t)%O.
Proof.
case=> x Ax; rewrite /supremum; case: ifPn => [/eqP -> //|_].
by case: xgetP => [y yA [uAy _]|/(_ x) //]; exact: uAy.
Qed.

Lemma le_infimum_Nmem x0 A t :
  infimums A !=set0 -> A t -> (infimum x0 A <= t)%O.
Proof.
case=> x Ex; rewrite /infimum; case: ifPn => [/eqP -> //|_].
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

Definition meets T (F G : set (set T)) :=
  forall A B, F A -> G B -> A `&` B !=set0.

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

Lemma joinKI B A : A `&` (A `|` B) = A.
Proof. by rewrite setUC setKU. Qed.

Lemma meetKU B A : A `|` (A `&` B) = A.
Proof. by rewrite setIC setKI. Qed.

Definition orderMixin := @MeetJoinMixin _ _ (fun A B => `[<proper A B>]) setI
  setU le_def lt_def (@setIC _) (@setUC _) (@setIA _) (@setUA _) joinKI meetKU
  (@setIUl _) setIid.

Local Canonical porderType := POrderType set_display (set T) orderMixin.
Local Canonical latticeType := LatticeType (set T) orderMixin.
Local Canonical distrLatticeType := DistrLatticeType (set T) orderMixin.

Lemma SetOrder_sub0set A : (set0 <= A)%O.
Proof. by apply/asboolP; apply: sub0set. Qed.

Lemma SetOrder_setTsub A : (A <= setT)%O.
Proof. exact/asboolP. Qed.

Local Canonical bLatticeType :=
  BLatticeType (set T) (Order.BLattice.Mixin SetOrder_sub0set).
Local Canonical tbLatticeType :=
  TBLatticeType (set T) (Order.TBLattice.Mixin SetOrder_setTsub).
Local Canonical bDistrLatticeType := [bDistrLatticeType of set T].
Local Canonical tbDistrLatticeType := [tbDistrLatticeType of set T].

Lemma subKI A B : B `&` (A `\` B) = set0.
Proof. by rewrite setDE setICA setICr setI0. Qed.

Lemma joinIB A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite setUC -setDDr setDv setD0. Qed.

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

Section exports.
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

End exports.
End Exports.
End SetOrder.
Export SetOrder.Exports.

Section product.
Variables (T1 T2 : Type).
Implicit Type A B : set (T1 * T2).

Lemma subset_fst_set : {homo @fst_set T1 T2 : A B / A `<=` B}.
Proof. by move=> A B AB x [y Axy]; exists y; exact/AB. Qed.

Lemma subset_snd_set : {homo @snd_set T1 T2 : A B / A `<=` B}.
Proof. by move=> A B AB x [y Axy]; exists y; exact/AB. Qed.

Lemma fst_set_fst A : A `<=` A.`1 \o fst. Proof. by move=> [x y]; exists y. Qed.

Lemma snd_set_snd A: A `<=` A.`2 \o snd. Proof. by move=> [x y]; exists x. Qed.

Lemma fst_setM (X : set T1) (Y : set T2) : (X `*` Y).`1 `<=` X.
Proof. by move=> x [y [//]]. Qed.

Lemma snd_setM (X : set T1) (Y : set T2) : (X `*` Y).`2 `<=` Y.
Proof. by move=> x [y [//]]. Qed.

Lemma fst_setMR (X : set T1) (Y : T1 -> set T2) : (X `*`` Y).`1 `<=` X.
Proof. by move=> x [y [//]]. Qed.

End product.

Section section.
Variables (T1 T2 : Type).
Implicit Types (A : set (T1 * T2)) (x : T1) (y : T2).

Definition xsection A x := [set y | (x, y) \in A].

Definition ysection A y := [set x | (x, y) \in A].

Lemma xsection_snd_set A x : xsection A x `<=` A.`2.
Proof. by move=> y Axy; exists x; rewrite /xsection/= inE in Axy. Qed.

Lemma ysection_fst_set A y : ysection A y `<=` A.`1.
Proof. by move=> x Axy; exists y; rewrite /ysection/= inE in Axy. Qed.

Lemma mem_xsection x y A : (y \in xsection A x) = ((x, y) \in A).
Proof. by apply/idP/idP => [|]; [rewrite inE|rewrite /xsection !inE /= inE]. Qed.

Lemma mem_ysection x y A : (x \in ysection A y) = ((x, y) \in A).
Proof. by apply/idP/idP => [|]; [rewrite inE|rewrite /ysection !inE /= inE]. Qed.

Lemma xsection0 x : xsection set0 x = set0.
Proof. by rewrite predeqE /xsection => y; split => //=; rewrite inE. Qed.

Lemma ysection0 y : ysection set0 y = set0.
Proof. by rewrite predeqE /ysection => x; split => //=; rewrite inE. Qed.

Lemma in_xsectionM X1 X2 x : x \in X1 -> xsection (X1 `*` X2) x = X2.
Proof.
move=> xX1; apply/seteqP; split=> [y /xsection_snd_set|]; first exact: snd_setM.
by move=> y X2y; rewrite /xsection/= inE; split=> //=; rewrite inE in xX1.
Qed.

Lemma in_ysectionM X1 X2 y : y \in X2 -> ysection (X1 `*` X2) y = X1.
Proof.
move=> yX2; apply/seteqP; split=> [x /ysection_fst_set|]; first exact: fst_setM.
by move=> x X1x; rewrite /ysection/= inE; split=> //=; rewrite inE in yX2.
Qed.

Lemma notin_xsectionM X1 X2 x : x \notin X1 -> xsection (X1 `*` X2) x = set0.
Proof.
move=> xX1; rewrite /xsection /= predeqE => y; split => //.
by rewrite /xsection/= inE => -[] /=; rewrite notin_set in xX1.
Qed.

Lemma notin_ysectionM X1 X2 y : y \notin X2 -> ysection (X1 `*` X2) y = set0.
Proof.
move=> yX2; rewrite /xsection /= predeqE => x; split => //.
by rewrite /ysection/= inE => -[_]; rewrite notin_set in yX2.
Qed.

Lemma xsection_bigcup (F : nat -> set (T1 * T2)) x :
  xsection (\bigcup_n F n) x = \bigcup_n xsection (F n) x.
Proof.
rewrite predeqE /xsection => y; split => [|[n _]] /=; rewrite inE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite inE.
by move=> Fnxy; rewrite inE; exists n.
Qed.

Lemma ysection_bigcup (F : nat -> set (T1 * T2)) y :
  ysection (\bigcup_n F n) y = \bigcup_n ysection (F n) y.
Proof.
rewrite predeqE /ysection => x; split => [|[n _]] /=; rewrite inE.
  by move=> -[n _ Fnxy]; exists n => //=; rewrite inE.
by move=> Fnxy; rewrite inE; exists n.
Qed.

Lemma trivIset_xsection (F : nat -> set (T1 * T2)) x : trivIset setT F ->
  trivIset setT (fun n => xsection (F n) x).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /xsection /= predeqE => y; split => //= -[]; rewrite !inE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma trivIset_ysection (F : nat -> set (T1 * T2)) y : trivIset setT F ->
  trivIset setT (fun n => ysection (F n) y).
Proof.
move=> /trivIsetP h; apply/trivIsetP => i j _ _ ij.
rewrite /ysection /= predeqE => x; split => //= -[]; rewrite !inE => Fixy Fjxy.
by have := h i j Logic.I Logic.I ij; rewrite predeqE => /(_ (x, y))[+ _]; apply.
Qed.

Lemma le_xsection x : {homo xsection ^~ x : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY y; rewrite /xsection /= 2!inE => /XY. Qed.

Lemma le_ysection y : {homo ysection ^~ y : X Y / X `<=` Y >-> X `<=` Y}.
Proof. by move=> X Y XY x; rewrite /ysection /= 2!inE => /XY. Qed.

Lemma xsectionD X Y x : xsection (X `\` Y) x = xsection X x `\` xsection Y x.
Proof.
rewrite predeqE /xsection /= => y; split; last by rewrite 3!inE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!inE.
Qed.

Lemma ysectionD X Y y : ysection (X `\` Y) y = ysection X y `\` ysection Y y.
Proof.
rewrite predeqE /ysection /= => x; split; last by rewrite 3!inE.
by rewrite inE => -[Xxy Yxy]; rewrite 2!inE.
Qed.

End section.

Notation "B \; A" :=
  ([set xy | exists2 z, A (xy.1, z) & B (z, xy.2)]) : classical_set_scope.

Lemma set_compose_subset {X Y : Type} (A C : set (X * Y)) (B D : set (Y * X)) :
  A `<=` C -> B `<=` D -> A \; B `<=` C \; D.
Proof.
by move=> AsubC BD [x z] /= [y] Bxy Ayz; exists y; [exact: BD | exact: AsubC].
Qed.

Lemma set_compose_diag {X : Type} (E : set (X * X)) :
  E \; range (fun x => (x, x)) = E.
Proof.
rewrite eqEsubset; split => [[_ _] [_ [_ _ [<- <-//]]]|[x y] Exy]/=.
by exists x => //; exists x.
Qed.
