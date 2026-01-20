(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg matrix finmap ssrnum.
From mathcomp Require Import ssrint rat interval.
From mathcomp Require Import mathcomp_extra boolp wochoice.

(**md**************************************************************************)
(* # Set Theory                                                               *)
(*                                                                            *)
(* This file develops a basic theory of sets and types equipped with a        *)
(* canonical inhabitant (pointed types):                                      *)
(* - A decidable equality is defined for any type. It is thus possible to     *)
(*   define an eqType structure for any type using the mixin gen_eqMixin.     *)
(* - This file adds the possibility to define a choiceType structure for      *)
(*   any type thanks to an axiom gen_choiceMixin giving a choice mixin.       *)
(* - We chose to have generic mixins and no global instances of the eqType    *)
(*   and choiceType structures to let the user choose which definition of     *)
(*   equality to use and to avoid conflict with already declared instances.   *)
(*                                                                            *)
(* Thanks to this basic set theory, we proved Zorn's Lemma, which states      *)
(* that any ordered set such that every totally ordered subset admits an      *)
(* upper bound has a maximal element. We also proved an analogous version     *)
(* for preorders, where maximal is replaced with premaximal: $t$ is           *)
(* premaximal if whenever $t < s$ we also have $s < t$.                       *)
(*                                                                            *)
(* About the naming conventions in this file:                                 *)
(* - use T, T', T1, T2, etc., aT (domain type), rT (return type) for names    *)
(*   of variables in Type (or choiceType/pointedType/porderType)              *)
(*   + use the same suffix or prefix for the sets as their containing type    *)
(*     (e.g., A1 in T1, etc.)                                                 *)
(*   + as a consequence functions are rather of type aT -> rT                 *)
(* - use I, J when the type corresponds to an index                           *)
(* - sets are named A, B, C, D, etc., or Y when it is ostensibly an image     *)
(*   set (i.e., of type set rT)                                               *)
(* - indexed sets are rather named F                                          *)
(*                                                                            *)
(* Examples of notations:                                                     *)
(* | Coq notations                |   | Meaning                             | *)
(* |-----------------------------:|---|:------------------------------------  *)
(* |                         set0 |==| $\emptyset$                            *)
(* |                     [set: A] |==| the full set of elements of type A     *)
(* |                   `` `\|` `` |==| $\cup$                                 *)
(* |                    `` `&` `` |==| $\cap$                                 *)
(* |                    `` `\` `` |==| set difference                         *)
(* |                    `` `+` `` |==| symmetric difference                   *)
(* |                     `` ~` `` |==| set complement                         *)
(* |                   `` `<=` `` |==| $\subseteq$                            *)
(* |                 `` f @` A `` |==| image by f of A                        *)
(* |              `` f @^-1` A `` |==| preimage by f of A                     *)
(* |                      [set x] |==| the singleton set $\{x\}$              *)
(* |                     [set~ x] |==| the complement of $\{x\}$              *)
(* |            [set E \| x in P] |==| the set of E with x ranging in P       *)
(* |                      range f |==| image by f of the full set             *)
(* | \big[setU/set0]_(i <- s \| P i) f i |==| finite union                    *)
(* |         \bigcup_(k in P) F k |==| countable union                        *)
(* |         \bigcap_(k in P) F k |==| countable intersection                 *)
(* |                 trivIset D F |==| F is a sequence of pairwise disjoint   *)
(* |                              |  | sets indexed over the domain D         *)
(*                                                                            *)
(* Detailed documentation:                                                    *)
(* ## Sets                                                                    *)
(* ```                                                                        *)
(*                       set T == type of sets on T                           *)
(*                   (x \in P) == boolean membership predicate from ssrbool   *)
(*                                for set P, available thanks to a canonical  *)
(*                                predType T structure on sets on T           *)
(*             [set x : T | P] == set of points x : T such that P holds       *)
(*                 [set x | P] == same as before with T left implicit         *)
(*            [set E | x in A] == set defined by the expression E for x in    *)
(*                                set A                                       *)
(*   [set E | x in A & y in B] == same as before for E depending on 2         *)
(*                                variables x and y in sets A and B           *)
(*                        setT == full set                                    *)
(*                        set0 == empty set                                   *)
(*                     range f == the range of f, i.e., [set f x | x in setT] *)
(*                     [set a] == set containing only a                       *)
(*                 [set a : T] == same as before with the type of a made      *)
(*                                explicit                                    *)
(*                     A `|` B == union of A and B                            *)
(*                      a |` A == A extended with a                           *)
(*        [set a1; a2; ..; an] == set containing only the n elements ai       *)
(*                     A `&` B == intersection of A and B                     *)
(*                     A `*` B == product of A and B, i.e., set of pairs      *)
(*                                (a,b) such that A a and B b                 *)
(*                        A.`1 == set of points a such that there exists b so *)
(*                                that A (a, b)                               *)
(*                        A.`2 == set of points a such that there exists b so *)
(*                                that A (b, a)                               *)
(*                        ~` A == complement of A                             *)
(*                    [set~ a] == complement of [set a]                       *)
(*                     A `\` B == complement of B in A                        *)
(*                      A `\ a == A deprived of a                             *)
(*                        `I_n := [set k | k < n]                             *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P                           *)
(*           \bigcup_(i : T) F == union of the family F indexed on T          *)
(*           \bigcup_(i < n) F := \bigcup_(i in `I_n) F                       *)
(*          \bigcup_(i >= n) F := \bigcup_(i in [set i | i >= n]) F           *)
(*                 \bigcup_i F == same as before with T left implicit         *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P                   *)
(*           \bigcap_(i : T) F == union of the family F indexed on T          *)
(*           \bigcap_(i < n) F := \bigcap_(i in `I_n) F                       *)
(*          \bigcap_(i >= n) F := \bigcap_(i in [set i | i >= n]) F           *)
(*                 \bigcap_i F == same as before with T left implicit         *)
(*                smallest C G := \bigcap_(A in [set M | C M /\ G `<=` M]) A  *)
(*                   A `<=` B <-> A is included in B                          *)
(*                     A `<` B := A `<=` B /\ ~ (B `<=` A)                    *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A      *)
(*                   f @^-1` A == preimage of A by f                          *)
(*                      f @` A == image of A by f                             *)
(*                                This is a notation for `image A f`          *)
(*                    A !=set0 := exists x, A x                               *)
(*                    [set` p] == a classical set corresponding to the        *)
(*                                predType p                                  *)
(*                     `[a, b] := [set` `[a, b]], i.e., a classical set       *)
(*                                corresponding to the interval `[a, b]       *)
(*                     `]a, b] := [set` `]a, b]]                              *)
(*                     `[a, b[ := [set` `[a, b[]                              *)
(*                     `]a, b[ := [set` `]a, b[]                              *)
(*                   `]-oo, b] := [set` `]-oo, b]]                            *)
(*                   `]-oo, b[ := [set` `]-oo, b[]                            *)
(*                   `[a, +oo[ := [set` `[a, +oo[]                            *)
(*                   `]a, +oo[ := [set` `]a, +oo[]                            *)
(*                 `]-oo, +oo[ := [set` `]-oo, +oo[]                          *)
(*               is_subset1 A <-> A contains only 1 element                   *)
(*                   is_fun f <-> for each a, f a contains only 1 element     *)
(*                 is_total f <-> for each a, f a is non empty                *)
(*              is_totalfun f <-> conjunction of is_fun and is_total          *)
(*                   xget x0 P == point x in P if it exists, x0 otherwise;    *)
(*                                P must be a set on a choiceType             *)
(*             fun_of_rel f0 f == function that maps x to an element of f x   *)
(*                                if there is one, to f0 x otherwise          *)
(*                    F `#` G <-> intersections beween elements of F an G are *)
(*                                all non empty                               *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Pointed types                                                           *)
(* ```                                                                        *)
(*                 pointedType == interface type for types equipped with a    *)
(*                                canonical inhabitant                        *)
(*                                The HB class is Pointed.                    *)
(*                       point == canonical inhabitant of a pointedType       *)
(*                       get P == point x in P if it exists, point otherwise  *)
(*                                P must be a set on a pointedType.           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## squash/unsquash                                                         *)
(* ```                                                                        *)
(*                      $| T | == the type `T : Type` is inhabited            *)
(*                                $| T | has type `Prop`.                     *)
(*                                $| T | is a notation for `squashed T`.      *)
(*                    squash x == object of type $| T | (with x : T)          *)
(*                  unsquash s == extract an inhabitant of type `T`           *)
(*                                (with s : $| T |)                           *)
(* ```                                                                        *)
(* Tactic:                                                                    *)
(*   - squash x:                                                              *)
(*     solves a goal $| T | by instantiating with x or [the T of x]           *)
(*                                                                            *)
(* ## Pairwise-disjoint sets                                                  *)
(* ```                                                                        *)
(*                trivIset D F == the sets F i, where i ranges over           *)
(*                                D : set I, are pairwise-disjoint            *)
(*                   cover D F := \bigcup_(i in D) F i                        *)
(*             partition D F A == the non-empty sets F i,where i ranges over  *)
(*                                D : set I, form a partition of A            *)
(*          pblock_index D F x == index i such that i \in D and x \in F i     *)
(*                pblock D F x := F (pblock_index D F x)                      *)
(*                                                                            *)
(*   maximal_disjoint_subcollection F A B == A is a maximal (for inclusion)   *)
(*                                   disjoint subcollection of the collection *)
(*                                   B of elements in F : I -> set T          *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Upper and lower bounds                                                  *)
(* ```                                                                        *)
(*              ubound A == the set of upper bounds of the set A              *)
(*              lbound A == the set of lower bounds of the set A              *)
(* ```                                                                        *)
(*                                                                            *)
(* Predicates to express existence conditions of supremum and infimum of sets *)
(* of real numbers:                                                           *)
(* ```                                                                        *)
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
(* ```                                                                        *)
(*                                                                            *)
(* ## Sections                                                                *)
(* ```                                                                        *)
(*           xsection A x == with A : set (T1 * T2) and x : T1 is the         *)
(*                           x-section of A                                   *)
(*           ysection A y == with A : set (T1 * T2) and y : T2 is the         *)
(*                           y-section of A                                   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Relations                                                               *)
(* Notations for composition and inverse (scope: relation_scope):             *)
(* ```                                                                        *)
(*                B \; A == [set x | exists z, A (x.1, z) & B (z, x.2)]       *)
(*                  A^-1 == [set xy | A (xy.2, xy.1)]                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope classical_set_scope.

Reserved Notation "[ 'set' x : T | P ]" (only parsing).
Reserved Notation "[ 'set' x | P ]" (format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]" (format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]" (format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (format "A .`1").
Reserved Notation "A .`2" (format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
Reserved Notation "A `+` B" (at level 54, left associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).
Reserved Notation "[ 'set`' p ]" (format "[ 'set`'  p ]").
Reserved Notation "[ 'disjoint' A & B ]"
  (format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").
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
Definition setX T1 T2 (A1 : set T1) (A2 : set T2) := [set z | A1 z.1 /\ A2 z.2].
Definition fst_set T1 T2 (A : set (T1 * T2)) := [set x | exists y, A (x, y)].
Definition snd_set T1 T2 (A : set (T1 * T2)) := [set y | exists x, A (x, y)].
Definition setXR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | A1 z.1 /\ A2 z.1 z.2].
Definition setXL T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | A1 z.2 z.1 /\ A2 z.2].

Lemma mksetE (P : T -> Prop) x : [set x | P x] x = P x.
Proof. by []. Qed.

Definition bigcap T I (P : set I) (F : I -> set T) :=
  [set a | forall i, P i -> F i a].
Definition bigcup T I (P : set I) (F : I -> set T) :=
  [set a | exists2 i, P i & F i a].

Definition subset A B := forall t, A t -> B t.
Local Notation "A `<=` B" := (subset A B).

Lemma subsetP A B : {subset A <= B} <-> (A `<=` B).
Proof. by split => + x => /(_ x); rewrite ?inE. Qed.

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
Arguments setX _ _ _ _ _ /.
Arguments setXR _ _ _ _ _ /.
Arguments setXL _ _ _ _ _ /.
Arguments fst_set _ _ _ _ /.
Arguments snd_set _ _ _ _ /.
Arguments subsetP {T A B}.

Notation range F := [set F i | i in setT].
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setX A B) : classical_set_scope.
Notation "A .`1" := (fst_set A) : classical_set_scope.
Notation "A .`2" := (snd_set A) : classical_set_scope.
Notation "A `*`` B" := (setXR A B) : classical_set_scope.
Notation "A ``*` B" := (setXL A B) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.
Notation "[ 'disjoint' A & B ]" := (disj_set A B) : classical_set_scope.

Definition setY {T : Type} (A B : set T) := (A `\` B) `|` (B `\` A).
Arguments setY _ _ _ _ /.
Notation "A `+` B" := (setY A B) : classical_set_scope.

Notation "'`I_' n" := [set k | is_true (k < n)%N].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : classical_set_scope.
Notation "\bigcup_ ( i >= n ) F" :=
  (\bigcup_(i in [set i | (n <= i)%N]) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : classical_set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : classical_set_scope.
Notation "\bigcap_ ( i >= n ) F" :=
  (\bigcap_(i in [set i | (n <= i)%N]) F) : classical_set_scope.
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

Lemma nat_nonempty : [set: nat] !=set0. Proof. by exists 1%N. Qed.

#[global] Hint Resolve nat_nonempty : core.

Lemma in_set1_eq {T : eqType} (a : T) (x : T) : x \in [set a] = (x == a).
Proof.
by apply/(sameP _ idP)/(equivP idP); rewrite inE eq_opE.
Qed.

Lemma itv_sub_in2 d (T : porderType d) (P : T -> T -> Prop) (i j : interval T) :
  [set` j] `<=` [set` i] ->
  {in i &, forall x y, P x y} -> {in j &, forall x y, P x y}.
Proof. by move=> ji + x y xj yj; apply; exact: ji. Qed.

Lemma preimage_itv T d (rT : porderType d) (f : T -> rT) (i : interval rT) (x : T) :
  ((f @^-1` [set` i]) x) = (f x \in i).
Proof. by rewrite inE. Qed.

Lemma preimage_itvoy T d (rT : porderType d) (f : T -> rT) y :
  f @^-1` `]y, +oo[%classic = [set x | (y < f x)%O].
Proof.
by rewrite predeqE => t; split => [|?]; rewrite /= in_itv/= andbT.
Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvoy")]
Notation preimage_itv_o_infty := preimage_itvoy (only parsing).

Lemma preimage_itvcy T d (rT : porderType d) (f : T -> rT) y :
  f @^-1` `[y, +oo[%classic = [set x | (y <= f x)%O].
Proof.
by rewrite predeqE => t; split => [|?]; rewrite /= in_itv/= andbT.
Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvcy")]
Notation preimage_itv_c_infty := preimage_itvcy (only parsing).

Lemma preimage_itvNyo T d (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y[%classic = [set x | (f x < y)%O].
Proof. by rewrite predeqE => t; split => [|?]; rewrite /= in_itv. Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvNyo")]
Notation preimage_itv_infty_o := preimage_itvNyo (only parsing).

Lemma preimage_itvNyc T d (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y]%classic = [set x | (f x <= y)%O].
Proof. by rewrite predeqE => t; split => [|?]; rewrite /= in_itv. Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvNyc")]
Notation preimage_itv_infty_c := preimage_itvNyc (only parsing).

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

Lemma notin_setE (A : set T) x : (x \notin A : Prop) = (~ A x).
Proof. by apply/propext; split=> /asboolPn. Qed.

Lemma setTPn (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.
#[deprecated(note="Use setTPn instead")]
Notation setTP := setTPn (only parsing).

Lemma in_set0 (x : T) : (x \in set0) = false. Proof. by rewrite memNset. Qed.

Lemma in_setT (x : T) : x \in setT. Proof. by rewrite mem_set. Qed.

Lemma in_setC (x : T) A : (x \in ~` A) = (x \notin A).
Proof. by apply/idP/idP; rewrite inE notin_setE. Qed.

Lemma in_setI (x : T) A B : (x \in A `&` B) = (x \in A) && (x \in B).
Proof. by apply/idP/andP; rewrite !inE. Qed.

Lemma in_setD (x : T) A B : (x \in A `\` B) = (x \in A) && (x \notin B).
Proof. by apply/idP/andP; rewrite !inE notin_setE. Qed.

Lemma in_setU (x : T) A B : (x \in A `|` B) = (x \in A) || (x \in B).
Proof. by apply/idP/orP; rewrite !inE. Qed.

Lemma in_setX T' (x : T * T') A E : (x \in A `*` E) = (x.1 \in A) && (x.2 \in E).
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

Lemma set_predC (P : {pred T}) : [set` predC P] = ~` [set` P].
Proof. by apply/seteqP; split => t /negP. Qed.

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

Lemma properW A B : A `<` B -> A `<=` B. Proof. by case. Qed.

Lemma properxx A : ~ A `<` A. Proof. by move=> [?]; apply. Qed.

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

Lemma setIid : idempotent_op (@setI T).
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

Lemma setUid : idempotent_op (@setU T).
Proof. move=> p; rewrite /setU/mkset predeqE => a; tauto. Qed.

Lemma setUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(setUC A) setUUl. Qed.

Lemma setU_id2r C A B :
  (forall x, (~` B) x -> A x = C x) -> (A `|` B) = (C `|` B).
Proof.
move=> h; apply/seteqP; split => [x [Ax|Bx]|x [Cx|Bx]]; [|by right| |by right].
- by have [|/h {}h] := pselect (B x); [by right|left; rewrite -h].
- by have [|/h {}h] := pselect (B x); [by right|left; rewrite h].
Qed.

Lemma setDE A B : A `\` B = A `&` ~` B. Proof. by []. Qed.

Lemma setUDl A B C : (A `\` B) `|` C = (A `|` C) `\` (B `\` C).
Proof.
apply/seteqP; split => x /=; first tauto.
#[warnings="-deprecated-syntactic-definition"] by move=> [[a|c]]; rewrite not_andE notE; tauto.
Qed.

Lemma setUDr A B C : A `|` (B `\` C) = (A `|` B) `\` (C `\` A).
Proof. by rewrite setUC setUDl setUC. Qed.

Lemma setDUK A B : A `<=` B -> A `|` (B `\` A) = B.
Proof.
move=> AB; apply/seteqP; split=> [x [/AB//|[//]]|x Bx].
by have [Ax|nAx] := pselect (A x); [left|right].
Qed.

Lemma setDKU A B : A `<=` B -> (B `\` A) `|` A = B.
Proof. by move=> /setDUK; rewrite setUC. Qed.

Lemma setDU A B C : A `<=` B -> B `<=` C -> C `\` A = (C `\` B) `|` (B `\` A).
Proof.
move=> AB BC; apply/seteqP; split.
  move=> x [Cx Ax].
  by have [Bx|Bx] := pselect (B x); [right|left].
move=> x [[Cx Bx]|[Bx Ax]].
- by split => // /AB.
- by split => //; exact/BC.
Qed.

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
by apply/predeqP => b; case: ifPn; rewrite (inE, notin_setE) => Aa;
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

Lemma nonemptyPn A : ~ (A !=set0) <-> A = set0.
Proof. by split; [|move=> ->]; move/set0P/negP; [move/negbNE/eqP|]. Qed.

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

Lemma setCD A B : ~` (A `\` B) = ~` A `|` B.
Proof. by rewrite setDE setCI setCK. Qed.

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

Lemma setIDAC A B C : (A `\` B) `&` C = A `&` (C `\` B).
Proof. by rewrite setIC !setIDA setIC. Qed.

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

Lemma setDUD A B C : (A `|` B) `\` C = A `\` C `|` B `\` C.
Proof.
apply/seteqP; split=> [x [[Ax|Bx] Cx]|x [[Ax]|[Bx] Cx]].
- by left.
- by right.
- by split=> //; left.
- by split=> //; right.
Qed.

Lemma setX0 T' (A : set T) : A `*` set0 = set0 :> set (T * T').
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma set0X T' (A : set T') : set0 `*` A = set0 :> set (T * T').
Proof. by rewrite predeqE => -[t u]; split => // -[]. Qed.

Lemma setXTT T' : setT `*` setT = setT :> set (T * T').
Proof. exact/predeqP. Qed.

Lemma setXT T1 T2 (A : set T1) : A `*` @setT T2 = fst @^-1` A.
Proof. by rewrite predeqE => -[x y]; split => //= -[]. Qed.

Lemma setTX T1 T2 (B : set T2) : @setT T1 `*` B = snd @^-1` B.
Proof. by rewrite predeqE => -[x y]; split => //= -[]. Qed.

Lemma setXI T1 T2 (X1 : set T1) (X2 : set T2) (Y1 : set T1) (Y2 : set T2) :
  (X1 `&` Y1) `*` (X2 `&` Y2) = X1 `*` X2 `&` Y1 `*` Y2.
Proof. by rewrite predeqE => -[x y]; split=> [[[? ?] [*]//]|[] [? ?] [*]]. Qed.

Lemma setSX T1 T2 (C D : set T1) (A B : set T2) :
  A `<=` B -> C `<=` D -> C `*` A `<=` D `*` B.
Proof. by move=> AB CD x [] /CD Dx1 /AB Bx2. Qed.

Lemma setX_bigcupr T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  A `*` \bigcup_(i in P) F i = \bigcup_(i in P) (A `*` F i).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [/= Ax [n Pn Fny]]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma setX_bigcupl T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  \bigcup_(i in P) F i `*` A = \bigcup_(i in P) (F i `*` A).
Proof.
rewrite predeqE => -[x y]; split; first by move=> [[n Pn Fnx] Ax]; exists n.
by move=> [n Pn [/= Ax Fny]]; split => //; exists n.
Qed.

Lemma bigcupX1l T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :
  \bigcup_(i in A1) ([set i] `*` A2 i) = A1 `*`` A2.
Proof. by apply/predeqP => -[i j]; split=> [[? ? [/= -> //]]|[]]; exists i. Qed.

Lemma bigcupX1r T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :
  \bigcup_(i in A2) (A1 i `*` [set i]) = A1 ``*` A2.
Proof. by apply/predeqP => -[i j]; split=> [[? ? [? /= -> //]]|[]]; exists j. Qed.

Lemma setY0 : right_id set0 (@setY T).
Proof. by move=> A; rewrite /setY setD0 set0D setU0. Qed.

Lemma set0Y : left_id set0 (@setY T).
Proof. by move=> A; rewrite /setY set0D setD0 set0U. Qed.

Lemma setYK A : A `+` A = set0.
Proof. by rewrite /setY setDv setU0. Qed.

Lemma setYC : commutative (@setY T).
Proof. by move=> A B; rewrite /setY setUC. Qed.

Lemma setYTC A : A `+` [set: T] = ~` A.
Proof. by rewrite /setY setDT set0U setTD. Qed.

Lemma setTYC A : [set: T] `+` A = ~` A.
Proof. by rewrite setYC setYTC. Qed.

Lemma setYA : associative (@setY T).
Proof.
move=> A B C; rewrite /setY; apply/seteqP; split => x/=;
by have [|] := pselect (A x); have [|] := pselect (B x);
  have [|] := pselect (C x); tauto.
Qed.

Lemma setIYl : left_distributive (@setI T) (@setY T).
Proof.
move=> A B C; rewrite /setY; apply/seteqP; split => x/=;
by have [|] := pselect (A x); have [|] := pselect (B x);
  have [|] := pselect (C x); tauto.
Qed.

Lemma setIYr : right_distributive (@setI T) (@setY T).
Proof. by move=> A B C; rewrite setIC setIYl -2!(setIC A). Qed.

Lemma setY_def A B : A `+` B = (A `\` B) `|` (B `\` A).
Proof. by []. Qed.

Lemma setYE A B : A `+` B = (A `|` B) `\` (A `&` B).
Proof.
rewrite /setY; apply/seteqP; split => x/=;
by have [|] := pselect (A x); have [|] := pselect (B x); tauto.
Qed.

Lemma setYU A B : (A `+` B) `+` (A `&` B) = A `|` B.
Proof.
rewrite /setY; apply/seteqP; split => x/=;
by have [|] := pselect (A x); have [|] := pselect (B x); tauto.
Qed.

Lemma setYI A B : (A `|` B) `\` (A `+` B) = A `&` B.
Proof.
rewrite /setY; apply/seteqP; split => x/=;
by have [|] := pselect (A x); have [|] := pselect (B x); tauto.
Qed.

Lemma setYD A B : A `+` (A `&` B) = A `\` B.
Proof. by rewrite /setY; apply/seteqP; split => x/=; tauto. Qed.

Lemma setYCT A : A `+` ~` A = [set: T].
Proof. by rewrite /setY setDE setCK setIid setDE setIid setUv. Qed.

Lemma setCYT A : ~` A `+` A = [set: T].
Proof. by rewrite setYC setYCT. Qed.

Lemma not_setD1 a A : ~ A a -> A `\ a = A.
Proof. by move=> NDr; apply/setDidPl/disjoints_subset/subsetCr => _ ->. Qed.

End basic_lemmas.
Arguments subsetT {T} A.

#[global]
Hint Resolve subsetUl subsetUr subIsetl subIsetr subDsetl subDsetr : core.
Arguments setU_id2r {T} C {A B}.

Lemma set_cst {T I} (x : T) (A : set I) :
  [set x | _ in A] = if A == set0 then set0 else [set x].
Proof.
apply/seteqP; split=> [_ [i +] <-|t]; first by case: ifPn => // /eqP ->.
by case: ifPn => // /set0P[i Ai ->{t}]; exists i.
Qed.

Section set_order.
Import Order.TTheory.

Lemma set_eq_le d (rT : porderType d) T (f g : T -> rT) :
  [set x | f x = g x] = [set x | (f x <= g x)%O] `&` [set x | (f x >= g x)%O].
Proof. by apply/seteqP; split => [x/= ->//|x /andP]; rewrite -eq_le =>/eqP. Qed.

Lemma set_neq_lt d (rT : orderType d) T (f g : T -> rT) :
  [set x | f x != g x ] = [set x | (f x < g x)%O] `|` [set x | (f x > g x)%O].
Proof. by apply/seteqP; split => [x/=|x /=]; rewrite neq_lt => /orP. Qed.

End set_order.

Lemma image2E {TA TB rT : Type} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :
  [set f x y | x in A & y in B] = uncurry f @` (A `*` B).
Proof.
apply/predeqP => x; split=> [[a ? [b ? <-]]|[[a b] [? ? <-]]]/=;
by [exists (a, b) | exists a => //; exists b].
Qed.

Lemma set_nil (T : eqType) : [set` [::]] = @set0 T.
Proof. by rewrite predeqP. Qed.

Lemma set_cons1 (T : eqType) (x : T) : [set` [:: x]] = [set x].
Proof. by apply/seteqP; split => y /=; rewrite ?inE => /eqP. Qed.

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

Lemma setC_I n : ~` `I_n = [set k | n <= k].
Proof.
by apply/seteqP; split => [x /negP|x /= nx]; last apply/negP; rewrite -leqNgt.
Qed.

Lemma mem_not_I N n : (n \in ~` `I_N) = (N <= n).
Proof. by rewrite in_setC /mkset /in_mem /mem /= /in_set asboolb -leqNgt. Qed.

End InitialSegment.

Lemma setT_unit : [set: unit] = [set tt].
Proof. by apply/seteqP; split => // -[]. Qed.

Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/seteqP; split => [|] [].
Qed.

Lemma setT_bool : [set: bool] = [set true; false].
Proof. by rewrite eqEsubset; split => // [[]] // _; [left|right]. Qed.

Lemma set_bool (B : set bool) :
  [\/ B == [set true], B == [set false], B == set0 | B == setT].
Proof.
have [Bt|Bt] := boolP (true \in B); have [Bf|Bf] := boolP (false \in B).
- have -> : B = setT by apply/seteqP; split => // -[] _; exact: set_mem.
  by apply/or4P; rewrite eqxx/= !orbT.
- suff : B = [set true] by move=> ->; apply/or4P; rewrite eqxx.
  apply/seteqP; split => -[]// /mem_set; last by move=> _; exact: set_mem.
  by rewrite (negbTE Bf).
- suff : B = [set false] by move=> ->; apply/or4P; rewrite eqxx/= orbT.
  apply/seteqP; split => -[]// /mem_set; last by move=> _; exact: set_mem.
  by rewrite (negbTE Bt).
- suff : B = set0 by move=> ->; apply/or4P; rewrite eqxx/= !orbT.
  by apply/seteqP; split => -[]//=; rewrite 2!notin_setE in Bt, Bf.
Qed.

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
HB.instance Definition _ := isComLaw.Build (set T) set0 setU setUA setUC set0U.
HB.instance Definition _ := isMulLaw.Build (set T) setT setU setTU setUT.
HB.instance Definition _ := isComLaw.Build (set T) setT setI setIA setIC setTI.
HB.instance Definition _ := isMulLaw.Build (set T) set0 setI set0I setI0.
HB.instance Definition _ := isAddLaw.Build (set T) setU setI setUIl setUIr.
HB.instance Definition _ := isAddLaw.Build (set T) setI setU setIUl setIUr.

HB.instance Definition _ := isComLaw.Build (set T) set0 setY setYA setYC set0Y.
HB.instance Definition _ := isAddLaw.Build (set T) setI setY setIYl setIYr.

End SetMonoids.

Section base_image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma imageP f A a : A a -> (f @` A) (f a). Proof. by exists a. Qed.

Lemma image_f f A a : a \in A -> f a \in [set f x | x in A].
Proof. by rewrite !inE; apply/imageP. Qed.

Lemma imageT (f : aT -> rT) (a : aT) : range f (f a).
Proof. by apply: imageP. Qed.

Lemma mem_range f a : f a \in range f.
Proof. by rewrite !inE; apply/imageT. Qed.

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

Lemma mem_image {f A a} : injective f ->
   (f a \in [set f x | x in A]) = (a \in A).
Proof. by move=> /image_inj finj; apply/idP/idP; rewrite !inE finj. Qed.

Lemma image_id A : id @` A = A.
Proof. by rewrite eqEsubset; split => a; [case=> /= x Ax <-|exists a]. Qed.

Lemma homo_setP {A Y f} :
  {homo f : x / x \in A >-> x \in Y} <-> {homo f : x / A x >-> Y x}.
Proof. by split=> fAY x; have := fAY x; rewrite !inE. Qed.

Lemma image_subP {A Y f} : f @` A `<=` Y <-> {homo f : x / A x >-> Y x}.
Proof. by split=> fAY x => [Ax|[y + <-]]; apply: fAY=> //; exists x. Qed.

Lemma image_sub {f : aT -> rT} {A : set aT} {B : set rT} :
  (f @` A `<=` B) = (A `<=` f @^-1` B).
Proof. by apply/propext; rewrite image_subP; split=> AB a /AB. Qed.

Lemma imsub1 x A f : f @` A `<=` [set x] -> forall a, A a -> f a = x.
Proof. by move=> + a Aa; apply; exists a. Qed.

Lemma imsub1P x A f : f @` A `<=` [set x] <-> forall a, A a -> f a = x.
Proof. by split=> [/(@imsub1 _)//|+ _ [a Aa <-]]; apply. Qed.

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

Lemma image_nonempty f A : A !=set0 -> f @` A !=set0.
Proof. by move=> [x] Ax; exists (f x), x. Qed.

Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof. by move=> AB _ [a Aa <-]; exists a => //; apply/AB. Qed.

Lemma preimage_set0 f : f @^-1` set0 = set0. Proof. exact/predeqP. Qed.

Lemma preimage_setT f : f @^-1` setT = setT. Proof. by []. Qed.

Lemma nonempty_preimage f Y : f @^-1` Y !=set0 -> Y !=set0.
Proof. by case=> [t ?]; exists (f t). Qed.

Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Proof. by move=> a Aa; exists a. Qed.

Lemma preimage_range f : f @^-1` (range f) = [set: aT].
Proof. by rewrite eqEsubset; split=> x // _; exists x. Qed.

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
by rewrite notin_setE/=; apply: contra_notP => /eqP/set0P[t [Dt fit]]; exists t.
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

Lemma preimage_true {T} (P : {pred T}) : P @^-1` [set true] = [set` P].
Proof. by apply/seteqP; split => [x/=//|x]. Qed.

Lemma preimage_false {T} (P : {pred T}) : P @^-1` [set false] = ~` [set` P].
Proof. by apply/seteqP; split => [t/= /negbT/negP|t /= /negP/negbTE]. Qed.

Lemma preimage_mem_true {T} (A : set T) : mem A @^-1` [set true] = A.
Proof. by rewrite preimage_true; under eq_fun do rewrite inE. Qed.

Lemma preimage_mem_false {T} (A : set T) : mem A @^-1` [set false] = ~` A.
Proof. by rewrite preimage_false; under eq_fun do rewrite inE. Qed.

End image_lemmas.
Arguments sub_image_setI {aT rT f A B} t _.
Arguments subset_set1 {_ _ _}.
Arguments subset_set2 {_ _ _ _}.

Lemma image2_subset {aT bT rT : Type} (f : aT -> bT -> rT)
    (A B : set aT) (C D : set bT) : A `<=` B -> C `<=` D ->
  [set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D].
Proof. by move=> AB CD; rewrite !image2E; apply: image_subset; exact: setSX. Qed.

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

Lemma inl_in_set_inr A B (x : A) (Y : set B) :
  inl x \in [set inr y | y in Y] = false.
Proof. by apply/negP; rewrite inE/= => -[]. Qed.

Lemma inr_in_set_inl A B (y : B) (X : set A) :
  inr y \in [set inl x | x in X] = false.
Proof. by apply/negP; rewrite inE/= => -[]. Qed.

Lemma inr_in_set_inr A B (y : B) (Y : set B) :
  inr y \in [set @inr A B y | y in Y] = (y \in Y).
Proof. by apply/idP/idP => [/[!inE][/= [x ? [<-]]]|/[!inE]]//; exists y. Qed.

Lemma inl_in_set_inl A B (x : A) (X : set A) :
  inl x \in [set @inl A B x | x in X] = (x \in X).
Proof. by apply/idP/idP => [/[!inE][/= [y ? [<-]]]|/[!inE]]//; exists x. Qed.

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
  by exists i => //; case: ifPn; rewrite (inE, notin_setE).
by case: ifPn; rewrite (inE, notin_setE) => Pi Fix; exists i.
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
   (~` (\big[setU/set0]_(t <- s | P t) f t)) = \big[setI/setT]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setC0 ?setCU. Qed.

Lemma setC_bigsetI U (s : seq T) (f : T -> set U) (P : pred T) :
  (~` (\big[setI/setT]_(t <- s | P t) f t)) =
  \big[setU/set0]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setCT ?setCI. Qed.

Lemma bigcupDr (F : I -> set T) (P : set I) (A : set T) : P !=set0 ->
  \bigcap_(i in P) (A `\` F i) = A `\` \bigcup_(i in P) F i.
Proof. by move=> PN0; rewrite setDE setC_bigcup -bigcapIr. Qed.

Lemma setD_bigcupl (F : I -> set T) (P : set I) (A : set T) :
  \bigcup_(i in P) F i `\` A = \bigcup_(i in P) (F i `\` A).
Proof. by rewrite setDE setI_bigcupl; under eq_bigcupr do rewrite -setDE. Qed.

Lemma bigcup_setX_dep {J : Type} (F : I -> J -> set T)
    (P : set I) (Q : I -> set J) :
  \bigcup_(k in P `*`` Q) F k.1 k.2 = \bigcup_(i in P) \bigcup_(j in Q i) F i j.
Proof.
apply/predeqP => x; split=> [|[i Pi [j Pj Fijx]]]; last by exists (i, j).
by move=> [[/= i j] [Pi Qj] Fijx]; exists i => //; exists j.
Qed.

Lemma bigcup_setX {J : Type} (F : I -> J -> set T) (P : set I) (Q : set J) :
  \bigcup_(k in P `*` Q) F k.1 k.2 = \bigcup_(i in P) \bigcup_(j in Q) F i j.
Proof. exact: bigcup_setX_dep. Qed.

Lemma bigcup_bigcup T' (F : I -> set T) (P : set I) (G : T -> set T') :
  \bigcup_(i in \bigcup_(n in P) F n) G i =
  \bigcup_(n in P) \bigcup_(i in F n) G i.
Proof.
apply/seteqP; split; first by move=> x [n [m ? ?] h]; exists m => //; exists n.
by move=> x [n ? [m ?]] h; exists m => //; exists n.
Qed.

Lemma bigcupID (Q : set I) (F : I -> set T) (P : set I) :
  \bigcup_(i in P) F i =
    (\bigcup_(i in P `&` Q) F i) `|` (\bigcup_(i in P `&` ~` Q) F i).
Proof. by rewrite -bigcup_setU -setIUr setUv setIT. Qed.

Lemma bigcapID (Q : set I) (F : I -> set T) (P : set I) :
  \bigcap_(i in P) F i =
    (\bigcap_(i in P `&` Q) F i) `&` (\bigcap_(i in P `&` ~` Q) F i).
Proof. by rewrite -bigcap_setU -setIUr setUv setIT. Qed.

Lemma bigcup_sub F A P :
  (forall i, P i -> F i `<=` A) -> \bigcup_(i in P) F i `<=` A.
Proof. by move=> FD t [n An Fnt]; exact: (FD n). Qed.

Lemma sub_bigcap F A P :
  (forall i, P i -> A `<=` F i) -> A `<=` \bigcap_(i in P) F i.
Proof. by move=> AF t At n Pn; exact: AF. Qed.

Lemma subset_bigcup P F G : (forall i, P i -> F i `<=` G i) ->
  \bigcup_(i in P) F i `<=` \bigcup_(i in P) G i.
Proof.
by move=> FG; apply: bigcup_sub => i Pi + /(FG _ Pi); apply: bigcup_sup.
Qed.

Lemma bigcup_subset P Q F : P `<=` Q ->
  \bigcup_(i in P) F i `<=` \bigcup_(i in Q) F i.
Proof. by move=> PQ t [i /PQ Qi Fit]; exists i. Qed.

Lemma subset_bigcap P F G : (forall i, P i -> F i `<=` G i) ->
  \bigcap_(i in P) F i `<=` \bigcap_(i in P) G i.
Proof.
move=> FG; apply: sub_bigcap => i Pi x Fx; apply: FG => //.
exact: bigcap_inf Fx.
Qed.

End bigop_lemmas.
Arguments bigcup_setD1 {T I} x.
Arguments bigcap_setD1 {T I} x.

Lemma setD_bigcup {T} (I : eqType) (F : I -> set T) (P : set I) (j : I) : P j ->
  F j `\` \bigcup_(i in [set k | P k /\ k != j]) (F j `\` F i) =
  \bigcap_(i in P) F i.
Proof.
move=> Pj; apply/seteqP; split => [t [Fjt UFt] i Pi|t UFt].
  by have [->//|ij] := eqVneq i j; apply: contra_notP UFt => Fit; exists i.
by split=> [|[k [Pk kj]] [Fjt]]; [|apply]; exact: UFt.
Qed.

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

Lemma bigcup_recl T (F : nat -> set T) :
  \bigcup_n F n = F 0%N `|` \bigcup_(n in ~` `I_1) F n.
Proof.
by apply/seteqP; split => [t [[_ F0t|n _ Fnt]]|t [F0t|[n /= n0 Fnt]]];
  [left|right; by exists n.+1|exists 0%N|exists n].
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

Section bigcup_seq.
Variables (T : choiceType) (U : Type).

Lemma bigcup_seq_cond (s : seq T) (f : T -> set U) (P : pred T) :
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

Lemma bigcup_seq (s : seq T) (f : T -> set U) :
  \bigcup_(t in [set` s]) (f t) = \big[setU/set0]_(t <- s) (f t).
Proof.
rewrite -(bigcup_seq_cond s f xpredT); congr (\bigcup_(t in mkset _) _).
by rewrite funeqE => t; rewrite andbT.
Qed.

Lemma bigcap_seq_cond (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcap_(t in [set x | (x \in s) && P x]) (f t) =
  \big[setI/setT]_(t <- s | P t) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_seq_cond. Qed.

Lemma bigcap_seq (s : seq T) (f : T -> set U) :
  \bigcap_(t in [set` s]) (f t) = \big[setI/setT]_(t <- s) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_seq. Qed.

End bigcup_seq.

Lemma in_set1 [T : finType] (x y : T) : (x \in [set y]) = (x \in [set y]%SET).
Proof. by apply/idP/idP; rewrite !inE /= => /eqP. Qed.

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
rewrite -(big_mkord xpredT F) -bigcup_seq.
by apply: eq_bigcupl; split=> i; rewrite /= mem_index_iota leq0n.
Qed.

Lemma bigcup_mkord_ord n (G : 'I_n.+1 -> set T) :
  \bigcup_(i < n.+1) G (inord i) = \big[setU/set0]_(i < n.+1) G i.
Proof.
rewrite bigcup_mkord; apply: eq_bigr => /= i _; congr G.
by apply/val_inj => /=; rewrite inordK.
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

Lemma bigcup_addn F n : \bigcup_i F (n + i) = \bigcup_(i >= n) F i.
Proof.
rewrite eqEsubset; split => [x /= [m _ Fmnx]|x /= [m nm Fmx]].
- by exists (n + m) => //=; rewrite leq_addr.
- by exists (m - n) => //; rewrite subnKC.
Qed.

Lemma bigcap_addn F n : \bigcap_i F (n + i) = \bigcap_(i >= n) F i.
Proof.
rewrite eqEsubset; split=> [x /= Fnx m nm|x /= nFx m _].
- by rewrite -(subnKC nm); exact: Fnx.
- exact/nFx/leq_addr.
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

HB.mixin Record isPointed T := { point : T }.

#[short(type=pointedType)]
HB.structure Definition Pointed := {T of isPointed T & Choice T}.

(* NB: was arrow_pointedType *)
HB.instance Definition _ (T : Type) (T' : T -> pointedType) :=
  isPointed.Build (forall t : T, T' t) (fun=> point).

HB.instance Definition _ := isPointed.Build unit tt.
HB.instance Definition _ := isPointed.Build bool false.
HB.instance Definition _ := isPointed.Build Prop False.
HB.instance Definition _ := isPointed.Build nat 0.
HB.instance Definition _ (T T' : pointedType) :=
  isPointed.Build (T * T')%type (point, point).
HB.instance Definition _ (n : nat) (T : pointedType) :=
  isPointed.Build (n.-tuple T) (nseq n point).
HB.instance Definition _ m n (T : pointedType) :=
  isPointed.Build 'M[T]_(m, n) (\matrix_(_, _) point)%R.
HB.instance Definition _ (T : choiceType) := isPointed.Build (option T) None.
HB.instance Definition _ (T : choiceType) := isPointed.Build {fset T} fset0.

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

Lemma setT0 : setT != set0 :> set T.
Proof. by apply/eqP => /seteqP[] /(_ point) /(_ Logic.I). Qed.

End PointedTheory.

HB.mixin Record isBiPointed (X : Type) of Equality X := {
  zero : X;
  one : X;
  zero_one_neq : zero != one;
}.

#[short(type="biPointedType")]
HB.structure Definition BiPointed :=
  { X of Choice X & isBiPointed X }.

Variant squashed T : Prop := squash (x : T).
Arguments squash {T} x.
Notation "$| T |" := (squashed T) : form_scope.
Tactic Notation "squash" uconstr(x) := (exists; refine x) ||
   match goal with |- $| ?T | => exists; refine [the T of x] end.

Definition unsquash {T} (s : $|T|) : T :=
  projT1 (cid (let: squash x := s in @ex_intro T _ x isT)).
Lemma unsquashK {T} : cancel (@unsquash T) squash. Proof. by move=> []. Qed.

(* Empty types *)

HB.mixin Record isEmpty T := {
  axiom : T -> False
}.

#[short(type="emptyType")]
HB.structure Definition Empty := {T of isEmpty T & Finite T}.

HB.factory Record Choice_isEmpty T of Choice T := {
  axiom : T -> False
}.
HB.builders Context T of Choice_isEmpty T.

Definition pickle : T -> nat := fun=> 0%N.
Definition unpickle : nat -> option T := fun=> None.
Lemma pickleK : pcancel pickle unpickle.
Proof. by move=> x; case: (axiom x). Qed.
HB.instance Definition _ := isCountable.Build T pickleK.

Lemma fin_axiom : Finite.axiom ([::] : seq T).
Proof. by move=> /[dup]/axiom. Qed.
HB.instance Definition _ := isFinite.Build T fin_axiom.

HB.instance Definition _ := isEmpty.Build T axiom.
HB.end.

HB.factory Record Type_isEmpty T := {
  axiom : T -> False
}.
HB.builders Context T of Type_isEmpty T.
Definition eq_op (x y : T) := true.
Lemma eq_opP : Equality.axiom eq_op. Proof. by move=> ? /[dup]/axiom. Qed.
HB.instance Definition _ := hasDecEq.Build T eq_opP.

Definition find of pred T & nat : option T := None.
Lemma findP (P : pred T) (n : nat) (x : T) :  find P n = Some x -> P x.
Proof. by []. Qed.
Lemma ex_find (P : pred T) : (exists x : T, P x) -> exists n : nat, find P n.
Proof. by move=> [/[dup]/axiom]. Qed.
Lemma eq_find (P Q : pred T) : P =1 Q -> find P =1 find Q.
Proof. by []. Qed.
HB.instance Definition _ := hasChoice.Build T findP ex_find eq_find.

HB.instance Definition _ := Choice_isEmpty.Build T axiom.
HB.end.

HB.instance Definition _ := Type_isEmpty.Build False id.

HB.instance Definition _ := isEmpty.Build void (@of_void _).

Definition no {T : emptyType} : T -> False := @axiom T.
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
apply: qcanon => -[Ts [Tc Te]].
set T := Choice.Pack _.
have [/unsquash x|/(_ (squash _)) TF] := pselect $|T|.
  right.
  pose Tp := isPointed.Build T x.
  pose TT : pointedType := HB.pack T Te Tc Tp.
  by exists TT.
left.
pose TMixin := Choice_isEmpty.Build T TF.
pose TT : emptyType := HB.pack T Te Tc TMixin.
by exists TT.
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

Lemma trivIset1 T I (i : I) (F : I -> set T) : trivIset [set i] F.
Proof. by move=> j k <- <-. Qed.

Lemma ltn_trivIset T (F : nat -> set T) :
  (forall n m, (m < n)%N -> F m `&` F n = set0) -> trivIset setT F.
Proof.
move=> h m n _ _ [t [mt nt]]; apply/eqP/negPn/negP.
by rewrite neq_ltn => /orP[] /h; apply/eqP/set0P; exists t.
Qed.

Lemma subsetC_trivIset T (F : nat -> set T) :
  (forall n, F n.+1 `<=` ~` (\big[setU/set0]_(i < n.+1) F i)) -> trivIset setT F.
Proof.
move=> sF; apply: ltn_trivIset => n m h; rewrite setIC; apply/disjoints_subset.
by case: n h => // n h; apply: (subset_trans (sF n)); exact/subsetC/bigsetU_sup.
Qed.

Lemma trivIset_mkcond T I (D : set I) (F : I -> set T) :
  trivIset D F <-> trivIset setT (fun i => if i \in D then F i else set0).
Proof.
split=> [tA i j _ _|tA i j Di Dj]; last first.
  by have := tA i j Logic.I Logic.I; rewrite !mem_set.
case: ifPn => iD; last by rewrite set0I => -[].
by case: ifPn => [jD /tA|jD]; [apply; exact: set_mem|rewrite setI0 => -[]].
Qed.

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

Lemma trivIset_image T I I' (D : set I) (f : I -> I') (F : I' -> set T) :
  trivIset D (F \o f) -> trivIset (f @` D) F.
Proof.
by move=> trivF i j [{}i Di <-] [{}j Dj <-] Ffij; congr (f _); apply: trivF.
Qed.
Arguments trivIset_image {T I I'} D f F.

Lemma trivIset_comp T I I' (D : set I) (f : I -> I') (F : I' -> set T) :
    {in D &, injective f} ->
  trivIset D (F \o f) = trivIset (f @` D) F.
Proof.
move=> finj; apply/propext; split; first exact: trivIset_image.
move=> trivF i j Di Dj Ffij; apply: finj; rewrite ?in_setE//.
by apply: trivF => //=; [exists i| exists j].
Qed.

Lemma trivIset_preimage1 {aT rT} D (f : aT -> rT) :
  trivIset D (fun x => f @^-1` [set x]).
Proof. by move=> y z _ _ [x [<- <-]]. Qed.

Lemma trivIset_preimage1_in {aT} {rT : choiceType} (D : set rT) (A : set aT)
  (f : aT -> rT) : trivIset D (fun x => A `&` f @^-1` [set x]).
Proof. by move=> y z _ _ [x [[_ <-] [_ <-]]]. Qed.

Lemma trivIset_bigcup (I T : Type) (J : eqType) (D : J -> set I) (F : I -> set T) :
  (forall n, trivIset (D n) F) ->
  (forall n m i j, n != m -> D n i -> D m j -> F i `&` F j !=set0 -> i = j) ->
  trivIset (\bigcup_k D k) F.
Proof.
move=> tB H; move=> i j [n _ Dni] [m _ Dmi] ij.
have [nm|nm] := eqVneq n m; first by apply: (tB m) => //; rewrite -nm.
exact: (H _ _ _ _ nm).
Qed.

Lemma trivIsetT_bigcup T1 T2 (I : eqType) (D : I -> set T1) (F : T1 -> set T2) :
  trivIset setT D ->
  trivIset (\bigcup_i D i) F ->
  trivIset setT (fun i => \bigcup_(t in D i) F t).
Proof.
move=> D0 h i j _ _ [t [[m Dim Fmt] [n Djn Fnt]]].
have mn : m = n by apply: h => //; [exists i|exists j|exists t].
rewrite {}mn {m} in Dim Fmt *.
by apply: D0 => //; exists n.
Qed.

Definition cover T I D (F : I -> set T) := \bigcup_(i in D) F i.

Lemma coverE T I D (F : I -> set T) : cover D F = \bigcup_(i in D) F i.
Proof. by []. Qed.

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
  by rewrite setIC (nth_default set0) ?size_map// set0I.
have nth_mem k : k < size s -> nth O s k \in iota 0 (size s1).
  by move=> ?; rewrite -(perm_mem ss1) mem_nth.
rewrite (nth_map O)// ts1 ?(nth_uniq,(perm_uniq ss1),iota_uniq)//; apply/s1D.
- by have := nth_mem _ si; rewrite mem_iota leq0n add0n.
- by have := nth_mem _ sj; rewrite mem_iota leq0n add0n.
Qed.

End partitions.

#[deprecated(note="Use trivIset_setIl instead")]
Notation trivIset_setI := trivIset_setIl (only parsing).

Section Zorn.

Definition total_on T (A : set T) (R : T -> T -> Prop) :=
  forall s t, A s -> A t -> R s t \/ R t s.

Let total_on_wo_chain (T : Type) (R : rel T) (P : {pred T}) :
  (forall A, total_on A R -> exists t, forall s, A s -> R s t) ->
  wo_chain R P -> exists2 z, z \in predT & upper_bound R P z.
Proof.
move: R P; elim/Peq : T => T R P Atot RP.
suff : total_on P R by move=> /Atot[t ARt]; exists t.
move=> s t Ps Pt; have [| |] := RP [predU (pred1 s) & (pred1 t)].
- by move=> x; rewrite !inE => /orP[/eqP ->{x}|/eqP ->{x}].
- by exists s; rewrite !inE eqxx.
- move=> x [[]]; rewrite !inE => /orP[/eqP ->{x}|/eqP ->{x}].
  + by move=> /(_ t); rewrite !inE eqxx orbT => /(_ isT) Rst _; left.
  + by move=> /(_ s); rewrite !inE eqxx => /(_ isT) Rts _; right.
Qed.

Lemma Zorn (T : Type) (R : rel T) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall s t, R s t -> R t s -> s = t) ->
  (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, forall s, R t s -> s = t.
Proof.
move: R; elim/Peq : T => T R Rxx Rtrans Ranti Atot.
have [//| |P _ RP|] := @Zorn's_lemma _ R predT _.
- by move=> ? ? ? _ _ _; exact: Rtrans.
- exact: total_on_wo_chain.
by move=> x _ Rx; exists x => s Rxs; apply: (Ranti _ _ _ Rxs) => //; exact: Rx.
Qed.

Definition premaximal T (R : T -> T -> Prop) (t : T) :=
  forall s, R t s -> R s t.

Lemma ZL_preorder (T : Type) (t0 : T) (R : rel T) :
  (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
  (forall A, total_on A R -> exists t, forall s, A s -> R s t) ->
  exists t, premaximal R t.
Proof.
move: t0 R; elim/Peq : T => T t0 R Rxx Rtrans Atot.
have [//| | |z _ Hz] := @Zorn's_lemma T R predT.
- by move=> ? ? ? _ _ _; exact: Rtrans.
- by move=> A _ RA; exact: total_on_wo_chain.
by exists z => s Rzs; exact: Hz.
Qed.

End Zorn.

Section Zorn_subset.
Variables (T : Type) (P : set (set T)).

Lemma Zorn_bigcup :
    (forall F : set (set T), F `<=` P -> total_on F subset ->
      P (\bigcup_(X in F) X)) ->
  exists A, P A /\ forall B, A `<` B -> ~ P B.
Proof.
move=> totP; pose R (sA sB : P) := `[< sval sA `<=` sval sB >].
have {}totR F (FR : total_on F R) : exists sB, forall sA, F sA -> R sA sB.
   have FP : [set val x | x in F] `<=` P.
     by move=> _ [X FX <-]; apply: set_mem; exact/valP.
   have totF : total_on [set val x | x in F] subset.
     move=> _ _ [X FX <-] [Y FY <-].
     by have [/asboolP|/asboolP] := FR _ _ FX FY; [left|right].
   exists (SigSub (mem_set (totP _ FP totF))) => A FA.
   exact/asboolP/(bigcup_sup (imageP val _)).
have [| | |sA sAmax] := Zorn _ _ _ totR.
- by move=> ?; apply/asboolP; exact: subset_refl.
- by move=> ? ? ? /asboolP ? /asboolP st; apply/asboolP; exact: subset_trans st.
- by move=> [A PA] [B PB] /asboolP AB /asboolP BA; exact/eq_exist/seteqP.
- exists (val sA); case: sA => A PA /= in sAmax *; split; first exact: set_mem.
  move=> B AB PB.
  have : R (exist (fun x : T -> Prop => x \in P) A PA) (SigSub (mem_set PB)).
    by apply/asboolP; exact: properW.
  move=> /(sAmax (SigSub (mem_set PB)))[BA].
  by move: AB; rewrite BA; exact: properxx.
Qed.

End Zorn_subset.

Definition maximal_disjoint_subcollection T I (F : I -> set T) (A B : set I) :=
  [/\ A `<=` B, trivIset A F & forall C,
      A `<` C -> C `<=` B -> ~ trivIset C F ].

Section maximal_disjoint_subcollection.
Context {I T : Type}.
Variables (B : I -> set T) (D : set I).

Let P := fun X => X `<=` D /\ trivIset X B.

Let maxP (A : set (set I)) :
  A `<=` P -> total_on A (fun x y => x `<=` y) -> P (\bigcup_(x in A) x).
Proof.
move=> AP h; split; first by apply: bigcup_sub => E /AP [].
move=> i j [x Ax] xi [y Ay] yj ij; have [xy|yx] := h _ _ Ax Ay.
- by apply: (AP _ Ay).2 => //; exact: xy.
- by apply: (AP _ Ax).2 => //; exact: yx.
Qed.

Lemma ex_maximal_disjoint_subcollection :
  { E | maximal_disjoint_subcollection B E D }.
Proof.
have /cid[E [[ED tEB] maxE]] := Zorn_bigcup maxP.
by exists E; split => // F /maxE + FD; exact: contra_not.
Qed.

End maximal_disjoint_subcollection.

Section UpperLowerTheory.
Import Order.TTheory.
Variables (d : Order.disp_t) (T : porderType d).
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
Proof. by rewrite /has_inf not_andP; left; exact/nonemptyPn. Qed.

Lemma has_sup0 : ~ has_sup (@set0 T).
Proof. by rewrite /has_sup not_andP; left; exact/nonemptyPn. Qed.

Lemma has_sup1 x : has_sup [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma has_inf1 x : has_inf [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma subset_has_lbound A B : A `<=` B -> has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; exact/Bl/AB. Qed.

Lemma subset_has_ubound A B : A `<=` B -> has_ubound B -> has_ubound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; exact/Bl/AB. Qed.

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
Variables (d : Order.disp_t) (T : orderType d).
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

Fact set_display : Order.disp_t. Proof. by []. Qed.

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

#[export]
HB.instance Definition _ : Choice (set T) := Choice.copy _ (set T).

#[export]
HB.instance Definition _ :=
  Order.isMeetJoinDistrLattice.Build set_display (set T)
    le_def lt_def (@setIC _) (@setUC _) (@setIA _) (@setUA _)
    joinKI meetKU (@setIUl _) setIid.

Lemma SetOrder_sub0set A : (set0 <= A)%O.
Proof. by apply/asboolP; exact: sub0set. Qed.

Lemma SetOrder_setTsub A : (A <= setT)%O.
Proof. exact/asboolP. Qed.

#[export]
HB.instance Definition _ := Order.hasBottom.Build set_display (set T)
  SetOrder_sub0set.

#[export]
HB.instance Definition _ := Order.hasTop.Build set_display (set T)
  SetOrder_setTsub.

Lemma subKI A B : B `&` (A `\` B) = set0.
Proof. by rewrite setDE setICA setICr setI0. Qed.

Lemma joinIB A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite setUC -setDDr setDv setD0. Qed.

#[export]
HB.instance Definition _ := Order.BDistrLattice_hasSectionalComplement.Build
  set_display (set T) subKI joinIB.

#[export]
HB.instance Definition _ := Order.CBDistrLattice_hasComplement.Build
  set_display (set T) (fun x => esym (setTD x)).

End SetOrder.
Module Exports. HB.reexport. End Exports.
End Internal.

Module Exports.

Export Internal.Exports.

Section exports.
Context {T : Type}.
Implicit Types A B : set T.

Lemma subsetEset A B : (A <= B)%O = (A `<=` B) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma properEset A B : (A < B)%O = (A `<` B) :> Prop.
Proof. by rewrite asboolE. Qed.

Lemma subEset A B : (A `\` B)%O = (A `\` B). Proof. by []. Qed.

Lemma complEset A : (~` A)%O = ~` A. Proof. by []. Qed.

Lemma botEset : \bot%O = @set0 T. Proof. by []. Qed.

Lemma topEset : \top%O = @setT T. Proof. by []. Qed.

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

Lemma fst_setX (X : set T1) (Y : set T2) : (X `*` Y).`1 `<=` X.
Proof. by move=> x [y [//]]. Qed.

Lemma snd_setX (X : set T1) (Y : set T2) : (X `*` Y).`2 `<=` Y.
Proof. by move=> x [y [//]]. Qed.

Lemma fst_setXR (X : set T1) (Y : T1 -> set T2) : (X `*`` Y).`1 `<=` X.
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

Lemma xsectionP x y A : xsection A x y <-> A (x, y).
Proof. by rewrite /xsection/= inE. Qed.

Lemma mem_ysection x y A : (x \in ysection A y) = ((x, y) \in A).
Proof. by apply/idP/idP => [|]; [rewrite inE|rewrite /ysection !inE /= inE]. Qed.

Lemma ysectionP x y A : ysection A y x <-> A (x, y).
Proof. by rewrite /ysection/= inE. Qed.

Lemma xsectionE A x : xsection A x = (fun y => (x, y)) @^-1` A.
Proof. by apply/seteqP; split => [y|y] /xsectionP. Qed.

Lemma ysectionE A y : ysection A y = (fun x => (x, y)) @^-1` A.
Proof. by apply/seteqP; split => [x|x] /ysectionP. Qed.

Lemma xsection0 x : xsection set0 x = set0.
Proof. by rewrite xsectionE preimage_set0. Qed.

Lemma ysection0 y : ysection set0 y = set0.
Proof. by rewrite ysectionE preimage_set0. Qed.

Lemma in_xsectionX X1 X2 x : x \in X1 -> xsection (X1 `*` X2) x = X2.
Proof.
move=> xX1; apply/seteqP; split=> [y /xsection_snd_set|]; first exact: snd_setX.
by move=> y X2y; rewrite /xsection/= inE; split=> //=; rewrite inE in xX1.
Qed.

Lemma in_ysectionX X1 X2 y : y \in X2 -> ysection (X1 `*` X2) y = X1.
Proof.
move=> yX2; apply/seteqP; split=> [x /ysection_fst_set|]; first exact: fst_setX.
by move=> x X1x; rewrite /ysection/= inE; split=> //=; rewrite inE in yX2.
Qed.

Lemma notin_xsectionX X1 X2 x : x \notin X1 -> xsection (X1 `*` X2) x = set0.
Proof.
move=> xX1; rewrite /xsection /= predeqE => y; split => //.
by rewrite /xsection/= inE => -[] /=; rewrite notin_setE in xX1.
Qed.

Lemma notin_ysectionX X1 X2 y : y \notin X2 -> ysection (X1 `*` X2) y = set0.
Proof.
move=> yX2; rewrite /xsection /= predeqE => x; split => //.
by rewrite /ysection/= inE => -[_]; rewrite notin_setE in yX2.
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

Lemma xsectionI A B x : xsection (A `&` B) x = xsection A x `&` xsection B x.
Proof. by rewrite /xsection predeqE => y/=; split; rewrite !inE => -[]. Qed.

Lemma ysectionI A B y : ysection (A `&` B) y = ysection A y `&` ysection B y.
Proof. by rewrite /ysection predeqE => x/=; split; rewrite !inE => -[]. Qed.

Lemma xsectionD X Y x : xsection (X `\` Y) x = xsection X x `\` xsection Y x.
Proof. by rewrite predeqE /xsection /= => y; split; rewrite !inE. Qed.

Lemma ysectionD X Y y : ysection (X `\` Y) y = ysection X y `\` ysection Y y.
Proof. by rewrite predeqE /ysection /= => x; split; rewrite !inE. Qed.

Lemma xsection_preimage_snd (B : set T2) x : xsection (snd @^-1` B) x = B.
Proof. by apply/seteqP; split; move=> y/=; rewrite /xsection/= inE. Qed.

Lemma ysection_preimage_fst (A : set T1) y : ysection (fst @^-1` A) y = A.
Proof. by apply/seteqP; split; move=> x/=; rewrite /ysection/= inE. Qed.

End section.

Declare Scope relation_scope.
Delimit Scope relation_scope with relation.

Notation "B \; A" :=
  ([set xy | exists2 z, A (xy.1, z) & B (z, xy.2)]) : relation_scope.

Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : relation_scope.

Local Open Scope relation_scope.

Lemma set_compose_subset {X Y : Type} (A C : set (X * Y)) (B D : set (Y * X)) :
  A `<=` C -> B `<=` D -> A \; B `<=` C \; D.
Proof.
by move=> AsubC BD [x z] /= [y] Bxy Ayz; exists y; [exact: BD | exact: AsubC].
Qed.

Lemma set_compose_diag {T : Type} (E : set (T * T)) :
  E \; range (fun x => (x, x)) = E.
Proof.
rewrite eqEsubset; split => [[_ _] [_ [_ _ [<- <-//]]]|[x y] Exy]/=.
by exists x => //; exists x.
Qed.

Lemma set_prod_invK {T : Type} (E : set (T * T)) : E^-1^-1 = E.
Proof. by rewrite eqEsubset; split; case. Qed.

Definition diagonal {T : Type} := [set x : T * T | x.1 = x.2].

Lemma diagonalP {T : Type} (x y : T) : diagonal (x, y) <-> x = y.
Proof. by []. Qed.

Local Close Scope relation_scope.
