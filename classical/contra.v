(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**md**************************************************************************)
(* # Contraposition                                                           *)
(*                                                                            *)
(* This file provides tactics to reason by contraposition and contradiction.  *)
(*                                                                            *)
(* ## Tactics                                                                 *)
(* ```                                                                        *)
(* assume_not == add a goal negation assumption. The tactic also works for    *)
(*               goals in Type, simplifies the added assumption, and          *)
(*               exposes its top-level constructive content.                  *)
(* absurd_not == proof by contradiction. Same as assume_not, but the goal is  *)
(*               erased and replaced by False.                                *)
(*               Caveat: absurd_not cannot be used as a move/ view because    *)
(*               its conclusion is indeterminate. The more general notP can   *)
(*               be used instead.                                             *)
(*     contra == proof by contraposition. Change a goal of the form           *)
(*               assumption -> conclusion to ~ conclusion -> ~ assumption.    *)
(*               As with assume_not, contra allows both assumption and        *)
(*               conclusion to be in Type, simplifies the negation of both    *)
(*               assumption and conclusion, and exposes the constructive      *)
(*               contents of the negated conclusion.                          *)
(*               The contra tactic also supports a limited form of the ':'    *)
(*               discharge pseudo tactical, whereby contra: <d-items> means   *)
(*               move: <d-items>; contra.                                     *)
(*               The only <d-items> allowed are one term, possibly preceded   *)
(*               by a clear switch.                                           *)
(*     absurd == proof by contradiction. The defective form of the tactic     *)
(*               simply replaces the entire goal with False (just as the Ltac *)
(*               exfalso), leaving the user to derive a contradiction from    *)
(*               the assumptions.                                             *)
(*               The ':' form absurd: <d-items> replaces the goal with the    *)
(*               negation of the (single) <d-item> (as with contra:, a clear  *)
(*               switch is also allowed.                                      *)
(*               Finally the Ltac absurd term form is also supported.         *)
(* ```                                                                        *)
(******************************************************************************)

(** Hiding module for the internal definitions and lemmas used by the tactics
  defined here. *)
Module Internals.

(**md**************************************************************************)
(* A wrapper for view lemmas with an indeterminate conclusion (of the form    *)
(* forall ... T ..., pattern -> T), and for which the intended view pattern   *)
(* may fail to match some assumptions. This wrapper ensures that such views   *)
(* are only used in the forward direction (as in move/), and only with the    *)
(* appropriate move_viewP hint, preventing its application to an arbitrary    *)
(* assumption A by the instatiation to A -> T' of its indeterminate           *)
(* conclusion T. This is similar to the implies wrapper, except move_viewP    *)
(* is *NOT* declared as a coercion---it must be used explicitly to apply the  *)
(* view manually to an assumption (as in, move_viewP my_view some_assumption).*)
(******************************************************************************)

Variant move_view S T := MoveView of S -> T.
Definition move_viewP {S T} mv : S -> T := let: MoveView v := mv in v.
Hint View for move/ move_viewP|2.

(**md**************************************************************************)
(* ## Type-level equivalence                                                  *)
(******************************************************************************)

Variant equivT S T := EquivT of S -> T & T -> S.

Definition equivT_refl S : equivT S S := EquivT id id.
Definition equivT_transl {S T U} : equivT S T -> equivT S U -> equivT T U :=
  fun (st : equivT S T) (su : equivT S U) =>
    let: EquivT S_T T_S := st in
    let: EquivT S_U U_S := su in
    EquivT (S_U \o T_S) (S_T \o U_S).
Definition equivT_sym {S T} : equivT S T -> equivT T S :=
   equivT_transl^~ (equivT_refl S).
Definition equivT_trans {S T U} : equivT S T -> equivT T U -> equivT S U :=
   equivT_transl \o equivT_sym.
Definition equivT_transr {S T U} eqST : equivT U S -> equivT U T :=
   equivT_trans^~ eqST.
Definition equivT_Prop (P Q : Prop) : (equivT P Q) <-> (equivT P Q).
Proof. split; destruct 1; split; assumption. Defined.
Definition equivT_LR {S T} (eq : equivT S T) : S -> T :=
  let: EquivT S_T _ := eq in S_T.
Definition equivT_RL {S T} (eq : equivT S T) : T -> S :=
  let: EquivT _ T_S := eq in T_S.

Hint View for move/ equivT_LR|2 equivT_RL|2.
Hint View for apply/ equivT_RL|2 equivT_LR|2.

(**md**************************************************************************)
(* A generic Forall "constructor" for the Gallina forall quantifier, i.e.,    *)
(* ```                                                                        *)
(*   \Forall x, P := Forall (fun x => P) := forall x, P.                      *)
(* ```                                                                        *)
(* The main use of Forall is to apply congruence to a forall equality:        *)
(* ```                                                                        *)
(*    congr1 Forall : forall P Q, P = Q -> Forall P = Forall Q.               *)
(* ```                                                                        *)
(* in particular in a classical setting with function extensionality, where   *)
(* we can have (forall x, P x = Q x) -> (forall x, P x) = (forall x, Q x).    *)
(*                                                                            *)
(* We use a forallSort structure to factor the ad hoc PTS product formation   *)
(* rules; forallSort is keyed on the type of the entire forall expression, or *)
(* (up to subsumption) the type of the forall body---this is always a sort.   *)
(*                                                                            *)
(* This implementation has two important limitations:                         *)
(* 1. It cannot handle the SProp sort and its typing rules. However, its      *)
(*    main application is extensionality, which is not compatible with        *)
(*    SProp because an (A : SProp) -> B "function" is not a generic           *)
(*    (A : Type) -> B function as SProp is not included in Type.              *)
(* 2. The Forall constructor can't be inserted by a straightforward           *)
(*    unfold (as in, rewrite -[forall x, _]/(Forall _)) because of the        *)
(*    way Coq unification handles Type constraints. The ForallI tactic        *)
(*    mitigates this issue, but there are additional issues with its          *)
(*    implementation---see below.                                             *)
(******************************************************************************)

Structure forallSort A :=
  ForallSort {forall_sort :> Type; _ : (A -> forall_sort) -> forall_sort}.

Notation mkForallSort A S := (@ForallSort A S (fun T => forall x, T x)).
Polymorphic Definition TypeForall (S := Type) (A : S) := mkForallSort A S.
Canonical TypeForall.

Canonical PropForall A := mkForallSort A Prop.

(* This is just a special case of TypeForall, but it provides a projection    *)
(* for the Set sort "constant".                                               *)
Canonical SetForall (A : Set) := mkForallSort A Set.

Definition Forall {A} {S : forallSort A} :=
  let: ForallSort _ F := S return (A -> S) -> S in F.

Notation "\Forall x .. z , T" :=
   (Forall (fun x => .. (Forall (fun z => T)) ..))
  (at level 200, x binder, z binder, T at level 200,
   format "'[hv' '\Forall'  '[' x .. z , ']' '/ '  T ']'") : type_scope.

(*  The ForallI implementation has to work around several Coq 8.12 issues:    *)
(*    - Coq unification defers Type constraints so we must ensure the type    *)
(*      constraint for the forall term F is processed, and the resulting      *)
(*      sort unified with the forall_sort projection _BEFORE_ F is unified    *)
(*      with a Forall _ pattern, because the inferred forallSort structure    *)
(*      determines the actual shape of that pattern. This is done by passing  *)
(*      F to erefl, then constraining the type of erefl to Forall _ = _. Note *)
(*      that putting a redundant F on the right hand side would break due to  *)
(*      incomplete handling of subtyping.                                     *)
(*    - ssr rewrite and Coq replace do not handle universe constraints.       *)
(*      and rewrite does not handle subsumption of the redex type. This means *)
(*      we cannot use rewrite, replace or fold, and must resort to primitive  *)
(*      equality destruction.                                                 *)
(*    - ssr case: and set do not recognize ssrpatternarg parameters, so we    *)
(*      must rely on ssrmatching.ssrpattern.                                  *)
Tactic Notation "ForallI" ssrpatternarg(pat) :=
  let F := fresh "F" in ssrmatching.ssrpattern pat => F;
  case: F / (@erefl _ F : Forall _ = _).
Tactic Notation "ForallI" := ForallI (forall x, _).

(**md**************************************************************************)
(* We define specialized copies of the wrapped structure of ssrfun for Prop   *)
(* and Type, as we need more than two alternative rules (indeed, 3 for Prop   *)
(* and 4 for Type). We need separate copies for Prop and Type as universe     *)
(* polymorphism cannot instantiate Type with Prop.                            *)
(******************************************************************************)

Structure wrappedProp := WrapProp {unwrap_Prop :> Prop}.
Definition wrap4Prop := WrapProp.
Definition wrap3Prop := wrap4Prop.
Definition wrap2Prop := wrap3Prop.
Canonical wrap1Prop P := wrap2Prop P.

Polymorphic Structure wrappedType@{i} := WrapType {unwrap_Type :> Type@{i}}.
Polymorphic Definition wrap4Type@{i} := WrapType@{i}.
Polymorphic Definition wrap3Type@{i} := wrap4Type@{i}.
Polymorphic Definition wrap2Type@{i} := wrap3Type@{i}.
Polymorphic Definition wrap1Type@{i} (T : Type@{i}) := wrap2Type T.
Canonical wrap1Type.

Lemma generic_forall_extensionality {A} {S : forallSort A} {P Q : A -> S} :
  P =1 Q -> Forall P = Forall Q.
Proof. by move/funext->. Qed.

(**md**************************************************************************)
(* A set of tools (tactics, views, and rewrite rules) to facilitate the       *)
(* handling of classical negation. The core functionality of these tools is   *)
(* implemented by three sets of canonical structures that provide for the     *)
(* simplification of negation statements (e.g., using de Morgan laws), the    *)
(* conversion from constructive statements in Type to purely logical ones in  *)
(* Prop (equivalently, expansion rules for the statement inhabited T), and    *)
(* conversely extraction of constructive contents from logical statements.    *)
(*                                                                            *)
(* Except for bool predicates and operators, all definitions are treated      *)
(* transparently when matching statements for either simplification or        *)
(* conversion; this is achieved by using the wrapper telescope pattern, first *)
(* delegating the matching of specific logical connectives, predicates, or    *)
(* type constructors to an auxiliary structure that *FAILS* to match unknown  *)
(* operators, thus triggers the expansion of defined constants. If this       *)
(* ultimately fails then the wrapper is expanded, and the primary structure   *)
(* instance for the expanded wrapper provides an alternative default rule:    *)
(* not simplifying ~ P, not expanding inhabited T, or not extracting any      *)
(* contents from a proposition P, respectively.                               *)
(*                                                                            *)
(* Additional rules, for intermediate wrapper instances, are used to handle   *)
(* forall statements (for which canonical instances are not yet supported),   *)
(* as well as addiitonal simplifications, such as inhabited P = P :> Prop.    *)
(*                                                                            *)
(* Finally various tertiary structures are used to match deeper patterns,     *)
(* such as bounded forall statements of the form forall x, P x -> Q x, or     *)
(* inequalites x != y (i.e., is_true (~~ (x == y))). As mentioned above,      *)
(* tertiary rules for bool subexpressions do not try to expand definitions,   *)
(* as this would lead to the undesirable expansion of some standard           *)
(* definitions. This is simply achieved by *NOT* using the wrapper telescope  *)
(* pattern, and just having a default instance alongside those for specific   *)
(* predicates and connectives.                                                *)
(******************************************************************************)

(**md**************************************************************************)
(* The negatedProp structure provides simplification of the Prop negation     *)
(* (~ _) for standard connectives and predicates. The instances below cover   *)
(* the pervasive and ssrbool Prop connectives, decidable equality, as well as *)
(* bool propositions (i.e., the is_true predicate), together with a few bool  *)
(* connectives and predicates: negation ~~, equality ==, and nat <= and <.    *)
(* Others can be added (e.g., Order.le/lt) by declaring appropriate instances *)
(* of bool_negation and bool_affirmation, while other Prop connectives and    *)
(* predicates can be added by declaring instances of proper_negatedProp.      *)
(******************************************************************************)

(**md**************************************************************************)
(* The implementation follows the wrapper telescope pattern outlined above:   *)
(* negatedProp instances match on the wrappedProp wrapper to try three        *)
(* generic matching rules, in succession:                                     *)
(* - Rule 1: match a specific connective or predicate with an instance of the *)
(*           properNegatedProp secondary structure, expanding definitions     *)
(*           if needed, but failing if no proper match is found.              *)
(* - Rule 2: match a forall statement (including (T : Type) -> P statements). *)
(* - Rule 3: match any Prop but return the trivial simplification.            *)
(* The simplified proposition is returned as a projection parameter nP rather *)
(* than a Structure member, so that applying the corresponding views or       *)
(* rewrite rules doesn't expose the inferred structures; properNegatedProp    *)
(* does similarly. Also, negatedProp similarly returns a 'trivial' bool flag  *)
(* that is set when Rule 3 is used, but this is actually used in the reverse  *)
(* direction: views notP and rewrite rule notE force trivial := false, thus   *)
(* excluding trivial instances.                                               *)
(******************************************************************************)

Structure negatedProp (trivial : bool) nP :=
  NegatedProp {negated_Prop :> wrappedProp; _ : (~ negated_Prop) = nP}.

Structure properNegatedProp nP := ProperNegatedProp {
  proper_negated_Prop :> Prop; _ : (~ proper_negated_Prop) = nP}.

Local Notation nProp t nP P := (unwrap_Prop (@negated_Prop t nP P)).
Local Notation nPred t nP P x := (nProp t (nP x) (P x)).
Local Notation pnProp nP P := (@proper_negated_Prop nP P).

(**md**************************************************************************)
(* User views and rewrite rules. The plain versions (notP, notE and notI) do  *)
(* not match trivial instances; lax_XXX versions allow them. In addition,     *)
(* the negation introduction rewrite rule notI does not match forall or ->    *)
(* statements---lax_notI must be used for these.                              *)
(******************************************************************************)

Lemma lax_notE {t nP} P : (~ nProp t nP P) = nP. Proof. by case: P. Qed.
Lemma lax_notP {t nP P} : ~ nProp t nP P -> nP. Proof. by rewrite lax_notE. Qed.
Definition lax_notI {t nP} P : nProp t nP P = (~ nP) := canRL notK (lax_notE P).

Definition notE {nP} P : (~ nProp false nP P) = nP := lax_notE P.
Definition notP {nP P} := MoveView (@lax_notP false nP P).

Fact proper_nPropP nP P : (~ pnProp nP P) = nP. Proof. by case: P. Qed.
Definition notI {nP} P : pnProp nP P = ~ nP := canRL notK (proper_nPropP P).

(** Rule 1: proper negation simplification, delegated to properNegatedProp. *)
Canonical proper_nProp nP P :=
  @NegatedProp false nP (wrap1Prop (pnProp nP P)) (proper_nPropP P).

(** Rule 2: forall_nProp is defined below as it uses exists_nProp. *)

(** Rule 3: trivial negation. *)
Canonical trivial_nProp P := @NegatedProp true (~ P) (wrap3Prop P) erefl.

(** properNegatedProp instances. *)

Canonical True_nProp := @ProperNegatedProp False True notB.1.
Canonical False_nProp := @ProperNegatedProp True False notB.2.
Canonical not_nProp P := @ProperNegatedProp P (~ P) (notK P).

Fact and_nPropP P tQ nQ Q : (~ (P /\ nProp tQ nQ Q)) = (P -> nQ).
Proof. by rewrite -implypN lax_notE. Qed.
Canonical and_nProp P tQ nQ Q :=
  ProperNegatedProp (@and_nPropP P tQ nQ Q).

Fact and3_nPropP P Q tR nR R : (~ [/\ P, Q & nProp tR nR R]) = (P -> Q -> nR).
Proof. by hnf; rewrite and3E notE. Qed.
Canonical and3_nProp P Q tR nR R :=
  ProperNegatedProp (@and3_nPropP P Q tR nR R).

Fact and4_nPropP P Q R tS nS S :
  (~ [/\ P, Q, R & nProp tS nS S]) = (P -> Q -> R -> nS).
Proof. by hnf; rewrite and4E notE. Qed.
Canonical and4_nProp P Q R tS nS S :=
  ProperNegatedProp (@and4_nPropP P Q R tS nS S).

Fact and5_nPropP P Q R S tT nT T :
  (~ [/\ P, Q, R, S & nProp tT nT T]) = (P -> Q -> R -> S -> nT).
Proof. by hnf; rewrite and5E notE. Qed.
Canonical and5_nProp P Q R S tT nT T :=
  ProperNegatedProp (@and5_nPropP P Q R S tT nT T).

Fact or_nPropP tP nP P tQ nQ Q :
  (~ (nProp tP nP P \/ nProp tQ nQ Q)) = (nP /\ nQ).
Proof. by rewrite not_orE !lax_notE. Qed.
Canonical or_nProp tP nP P tQ nQ Q :=
  ProperNegatedProp (@or_nPropP tP nP P tQ nQ Q).

Fact or3_nPropP tP nP P tQ nQ Q tR nR R :
  (~ [\/ nProp tP nP P, nProp tQ nQ Q | nProp tR nR R]) = [/\ nP, nQ & nR].
Proof. by rewrite or3E notE and3E. Qed.
Canonical or3_nProp tP nP P tQ nQ Q tR nR R :=
  ProperNegatedProp (@or3_nPropP tP nP P tQ nQ Q tR nR R).

Fact or4_nPropP tP nP P tQ nQ Q tR nR R tS nS S :
  (~ [\/ nProp tP nP P, nProp tQ nQ Q, nProp tR nR R | nProp tS nS S])
     = [/\ nP, nQ, nR & nS].
Proof. by rewrite or4E notE and4E. Qed.
Canonical or4_nProp tP nP P tQ nQ Q tR nR R tS nS S :=
  ProperNegatedProp (@or4_nPropP tP nP P tQ nQ Q tR nR R tS nS S).

(**md**************************************************************************)
(* The andRHS tertiary structure used to simplify (~ (P -> False)) to P,      *)
(* both here for the imply_nProp instance and for bounded_forall_nProp below. *)
(* Because the andRHS instances match the Prop RETURNED by negatedProp they   *)
(* do not need to expand definitions, hence do not need to use the wrapper    *)
(* telescope pattern.                                                         *)
(******************************************************************************)

Notation and_def binary P Q PQ := (PQ = if binary then P /\ Q else Q)%type.
Structure andRHS binary P Q PQ :=
  AndRHS {and_RHS :> Prop; _ : (P /\ and_RHS) = PQ; _ : and_def binary P Q PQ}.
Canonical unary_and_rhs P := @AndRHS false P P P True (andB.1.2 P) erefl.
Canonical binary_and_rhs P Q := @AndRHS true P Q (P /\ Q) Q erefl erefl.

Fact imply_nPropP b P nQ PnQ tR (nR : andRHS b P nQ PnQ) R :
  (~ (P -> nProp tR nR R)) = PnQ.
Proof. by rewrite -orNp {R}lax_notE; case: nR. Qed.
Canonical imply_nProp b P nQ PnQ tR nR R :=
  ProperNegatedProp (@imply_nPropP b P nQ PnQ tR nR R).

Fact exists_nPropP A tP nP P :
  (~ exists x : A, nPred tP nP P x) = (forall x : A, nP x).
Proof.
eqProp=> [nEP x | AnP [x]]; last by rewrite -/(~ _) lax_notE.
by rewrite -(lax_notE (P x)) => Px; case: nEP; exists x.
Qed.
Canonical exists_nProp A tP nP P :=
  ProperNegatedProp (@exists_nPropP A tP nP P).

Fact exists2_nPropP A P tQ nQ Q :
  (~ exists2 x : A, P x & nPred tQ nQ Q x) = (forall x : A, P x -> nQ x).
Proof. by rewrite exists2E notE. Qed.
Canonical exists2_nProp A P tQ nQ Q :=
  ProperNegatedProp (@exists2_nPropP A P tQ nQ Q).

Fact inhabited_nPropP T : (~ inhabited T) = (T -> False).
Proof. by rewrite inhabitedE notE. Qed.
Canonical inhabited_nProp T := ProperNegatedProp (inhabited_nPropP T).

(**md**************************************************************************)
(* Rule 2: forall negation, including (T : Type) -> P statements.             *)
(*                                                                            *)
(* We use tertiary structures to recognize bounded foralls and simplify,      *)
(* e.g., ~ forall x, P -> Q to exists2 x, P & ~ Q, or even exists x, P when   *)
(* Q :=  False (as above for imply).                                          *)
(*                                                                            *)
(* As forall_body_nProp and forall_body_proper_nProp are telescopes           *)
(* over negatedProp and properNegatedProp, respectively, their instances      *)
(* match instances declared above without the need to expand definitions,     *)
(* hence do not need to use the wrapper telescope idiom.                      *)
(******************************************************************************)

Structure negatedForallBody bounded P nQ tR nR := NegatedForallBody {
  negated_forall_body :> negatedProp tR nR; _ : and_def bounded P nQ nR}.
Structure properNegatedForallBody b P nQ nR := ProperNegatedForallBody {
  proper_negated_forall_body :> properNegatedProp nR; _ : and_def b P nQ nR}.
Notation nBody b P nQ t nR x := (negatedForallBody b (P x) (nQ x) t (nR x)).

(**md**************************************************************************)
(* The explicit argument to fun_if is a workaround for a bug in the Coq       *)
(* unification code that prevents default instances from ever matching match  *)
(* constructs. Furthermore rewriting with ifE would not work here, because    *)
(* the if_expr definition would be expanded by the eta expansion needed to    *)
(* match the exists_nProp rule.                                               *)
(******************************************************************************)

Fact forall_nPropP A b P nQ tR nR (R : forall x, nBody b P nQ tR nR x) :
  (~ forall x : A, R x) = if b then exists2 x, P x & nQ x else exists x, nQ x.
Proof.
rewrite exists2E -(fun_if (fun P => exists x, idfun P x)) notI /=; congr not.
apply/generic_forall_extensionality=> x; rewrite if_arg lax_notI.
by case: (R x) => _ <-.
Qed.
Canonical forall_nProp A b P nQ tR nR (R : forall x, nBody b P nQ tR nR x) :=
  @NegatedProp false _ (wrap2Prop (forall x : A, R x)) (forall_nPropP R).

Fact proper_nBodyP b P nQ nR :
  properNegatedForallBody b P nQ nR -> and_def b P nQ nR.
Proof. by case. Qed.
Canonical proper_nBody b P nQ nR R :=
  let def_nR := @proper_nBodyP b P nQ nR R in
  @NegatedForallBody b P nQ false nR (proper_nProp R) def_nR.
Canonical nonproper_nBody tP nP P :=
  @NegatedForallBody false True nP tP nP P erefl.

Fact andRHS_def b P Q PQ : andRHS b P Q PQ -> and_def b P Q PQ.
Proof. by case. Qed.
Canonical bounded_nBody b P nQ PnQ tR nR R :=
  ProperNegatedForallBody (@imply_nProp b P nQ PnQ tR nR R) (andRHS_def nR).
Canonical unbounded_nBody nQ Q :=
  @ProperNegatedForallBody false True nQ nQ Q erefl.

(**md**************************************************************************)
(* The properNegatedProp instance that handles boolean statements. We use     *)
(* two tertiary structures to handle positive and negative boolean statements *)
(* so that the contra tactic below will mostly subsume the collection of      *)
(* contraXX lemmas in ssrbool and eqtype.                                     *)
(*                                                                            *)
(* We only match manifest ~~ connectives, the true and false constants, and   *)
(* the ==, <=%N, and <%N predicates. In particular we do not use de Morgan    *)
(* laws to push boolean negation into connectives, as we did above for Prop   *)
(* connectives. It will be up to the user to use rewriting to put the negated *)
(* statement in its desired shape.                                            *)
(******************************************************************************)

Structure negatedBool nP :=
  NegatedBool {negated_bool :> bool; _ : (~ negated_bool) = nP}.
Structure positedBool P :=
  PositedBool {posited_bool :> bool; _ : is_true posited_bool = P}.

Local Fact is_true_nPropP nP (b : negatedBool nP) : (~ b) = nP.
Proof. by case: b. Qed.
Canonical is_true_nProp nP b := ProperNegatedProp (@is_true_nPropP nP b).

Local Fact true_negP : (~ true) = False. Proof. by eqProp. Qed.
Local Fact true_posP : (true : Prop) = True. Proof. by eqProp. Qed.
Local Fact false_negP : (~ false) = True. Proof. by eqProp. Qed.
Local Fact false_posP : (false : Prop) = False. Proof. by eqProp. Qed.
Canonical true_neg := NegatedBool true_negP.
Canonical true_pos := PositedBool true_posP.
Canonical false_neg := NegatedBool false_negP.
Canonical false_pos := PositedBool false_posP.

Local Fact id_negP (b : bool) : (~ b) = ~~ b. Proof. exact/reflect_eq/negP. Qed.
Canonical id_neg b := NegatedBool (id_negP b).
Canonical id_pos (b : bool) := @PositedBool b b erefl.

Local Fact negb_negP P (b : positedBool P) : (~ ~~ b) = P.
Proof. by rewrite (reflect_eq negP) negbK; case: b. Qed.
Canonical negb_neg P b := NegatedBool (@negb_negP P b).
Local Fact negb_posP nP (b : negatedBool nP) : (~~ b = nP :> Prop).
Proof. by rewrite -(reflect_eq negP) notE. Qed.
Canonical negb_pos nP b := PositedBool (@negb_posP nP b).

(**md**************************************************************************)
(* We use a tertiary structure to handle the negation of nat comparisons, and *)
(* simplify ~ m <= n to n < m, and ~ m < n to n <= m. As m < n is merely      *)
(* notation for m.+1 <= n, we need to dispatch on the left hand side of the   *)
(* comparison to perform the latter simplification.                           *)
(******************************************************************************)

Structure negatedLeqLHS n lt_nm :=
  NegatedLeqLHS {negated_leq_LHS :> nat; _ : (n < negated_leq_LHS) = lt_nm}.
Canonical neg_ltn_LHS n m := @NegatedLeqLHS n (n <= m) m.+1 erefl.
Canonical neg_leq_LHS n m := @NegatedLeqLHS n (n < m) m erefl.

Local Fact leq_negP n lt_nm (m : negatedLeqLHS n lt_nm) : (~ m <= n) = lt_nm.
Proof. by rewrite notE -ltnNge; case: m => /= m ->. Qed.
Canonical leq_neg n lt_nm m := NegatedBool (@leq_negP n lt_nm m).

(**md**************************************************************************)
(* We use two tertiary structures to simplify negation of boolean constant    *)
(* and decidable equalities, simplifying b <> true to ~~ b, b <> false to b,  *)
(* x <> y to x != y, and ~ x != y to x = y. We do need to use the wrapper     *)
(* telescope pattern here, as we want to simplify instances of x <> y when y  *)
(* evaluates to true or false. Since we only need two rules (true/false RHS   *)
(* or generic eqType RHS) we can use the generic wrapped type from ssrfun.    *)
(* The actual matching of the true and false RHS is delegated to a fourth     *)
(* level bool_eq_negation_rhs structure. Finally observe that the ~ x != y to *)
(* x = y simplification can be handled by a bool_affirmation instance.        *)
(******************************************************************************)

Structure neqRHS nP T x :=
  NeqRHS {neq_RHS :> wrapped T; _ : (x <> unwrap neq_RHS) = nP}.
Structure boolNeqRHS nP (x : bool) :=
  BoolNeqRHS {bool_neq_RHS; _ : (x <> bool_neq_RHS) = nP}.

Local Fact eq_nPropP nP T x (y : neqRHS nP x) : (x <> unwrap y :> T) = nP.
Proof. by case: y. Qed.
Canonical eq_nProp nP T x y := ProperNegatedProp (@eq_nPropP nP T x y).

Local Fact bool_neqP nP x y : (x <> @bool_neq_RHS nP x y) = nP.
Proof. by case: y. Qed.
Canonical bool_neq nP x y := @NeqRHS nP bool x (wrap _) (@bool_neqP nP x y).
Canonical true_neq nP b := BoolNeqRHS (@is_true_nPropP nP b).
Local Fact false_neqP P (b : positedBool P) : (b <> false :> bool) = P.
Proof. by move: b => [] [] /= <-; exact/propext. Qed.
Canonical false_neq P b := BoolNeqRHS (@false_neqP P b).

Local Fact eqType_neqP (T : eqType) (x y : T) : (x <> y) = (x != y).
Proof. by rewrite (reflect_eq eqP) (reflect_eq negP). Qed.
Canonical eqType_neq (T : eqType) x y :=
  @NeqRHS (x != y) T x (Wrap y) (eqType_neqP x y).
Local Fact eq_op_posP (T : eqType) x y : (x == y :> T : Prop) = (x = y).
Proof. exact/esym/reflect_eq/eqP. Qed.
Canonical eq_op_pos T x y := PositedBool (@eq_op_posP T x y).

(**md**************************************************************************)
(* The witnessedType structure provides conversion between Type and Prop in   *)
(* goals; the conversion is mostly used in the Type-to-Prop direction, e.g.,  *)
(* as a preprocessing step preceding proof by contradiction (see absurd_not   *)
(* below), but the Prop-to-Type direction is required for contraposition.     *)
(*                                                                            *)
(* Thus witnessedType associates to a type T a "witness" proposition P        *)
(* equivalent to the existence of an x of type T. As in a `{classical_logic}  *)
(* context inhabited T is such a proposition, witnessedType can be understood *)
(* as providing simplification for inhabited T, much like negatedProp         *)
(* provides simplification for ~ P for standard connectives and predicates.   *)
(******************************************************************************)

(**md**************************************************************************)
(* Similarly to negatedProp, witnessedType returns the witness proposition     *)
(* via a projection argument P, but does not need to signal "trivial"         *)
(* instances as the default value for P is nontrivial (namely, inhabited T),  *)
(* while the "trivial" case where P = T is actually desireable and handled    *)
(* by an extra top-priority rule.                                             *)
(******************************************************************************)

Structure witnessedType P := WitnessedType {
 witnessed_Type :> wrappedType; _ : inhabited witnessed_Type = P}.
Structure properWitnessedType P := ProperWitnessedType {
  proper_witnessed_Type :> Type; _ : inhabited proper_witnessed_Type = P}.
Local Notation wType P T := (unwrap_Type (@witnessed_Type P T)).
Local Notation wTycon P T x := (wType (P x) (T x)).

(* User interface lemmas. *)

Lemma witnessedType_intro {P : Prop} T : P -> wType P T.
Proof. by case: T => /= T <- /inhabited_witness. Qed.
Local Coercion witnessedType_intro : witnessedType >-> Funclass.

Lemma witnessedType_elim {P} T : wType P T -> P.
Proof. by case: T => /= T <-. Qed.
Local Notation wTypeP := witnessedType_elim.

(* Helper lemma and tactic. *)

Local Fact eq_inhabited T (P : Prop) : (T -> P) -> (P -> T) -> inhabited T = P.
Proof. by move=> T_P P_T; eqProp=> [[/T_P] | /P_T]. Qed.
Ltac eqInh := apply: eq_inhabited.

(** Rule 1: Prop goals are left as is. *)
Canonical Prop_wType P :=
  @WitnessedType P (wrap1Type P) (eq_inhabited (@id P) id).

(** Rule 2: Specific type constructors (sigs, sums, and pairs) are delegated
    to the secondary properWitnessedType structure. *)
Lemma proper_wTypeP P (T : properWitnessedType P) : inhabited T = P.
Proof. by case: T. Qed.
Canonical proper_wType P T :=
  @WitnessedType P (wrap2Type _) (@proper_wTypeP P T).

(** Rule 3: Forall (and -> as a special case). *)
Local Fact forall_wTypeP A P T :
  inhabited (forall x : A, wTycon P T x) = (forall x : A, P x) .
Proof. by do [eqInh=> allP x; have:= allP x] => [/wTypeP | /T]. Qed.
Canonical forall_wType A P T :=
  @WitnessedType _ (wrap3Type _) (@forall_wTypeP A P T).

(** Rule 4: Default to inhabited if all else fails. *)
Canonical inhabited_wType T := @WitnessedType (inhabited T) (wrap4Type T) erefl.

(** Specific proper_witnessedType instances. *)

Local Fact void_wTypeP : inhabited void = False. Proof. by eqInh. Qed.
Canonical void_wType := ProperWitnessedType void_wTypeP.

Local Fact unit_wTypeP : inhabited unit = True. Proof. by eqInh. Qed.
Canonical unit_wType := ProperWitnessedType unit_wTypeP.

Local Fact pair_wTypeP P Q S T : inhabited (wType P S * wType Q T) = (P /\ Q).
Proof. by eqInh=> [[/wTypeP-isP /wTypeP] | [/S-x /T]]. Qed.
Canonical pair_wType P Q S T := ProperWitnessedType (@pair_wTypeP P Q S T).

Local Fact sum_wTypeP P Q S T : inhabited (wType P S + wType Q T) = (P \/ Q).
Proof. by eqInh=> [[] /wTypeP | /decide_or[/S | /T]]; by [left | right]. Qed.
Canonical sum_wType P Q S T := ProperWitnessedType (@sum_wTypeP P Q S T).

Local Fact sumbool_wTypeP P Q : inhabited ({P} + {Q}) = (P \/ Q).
Proof. by eqInh=> [[] | /decide_or[]]; by [left | right]. Qed.
Canonical sumbool_wType P Q := ProperWitnessedType (@sumbool_wTypeP P Q).

Local Fact sumor_wTypeP P Q T : inhabited (wType P T + {Q}) = (P \/ Q).
Proof. by eqInh=> [[/wTypeP|] | /decide_or[/T|]]; by [left | right]. Qed.
Canonical sumor_wType P Q T := ProperWitnessedType (@sumor_wTypeP P Q T).

Local Fact sig1_wTypeP T P : inhabited {x : T | P x} = (exists x : T, P x).
Proof. by eqInh=> [[x Px] | /cid//]; exists x. Qed.
Canonical sig1_wType T P := ProperWitnessedType (@sig1_wTypeP T P).

Local Fact sig2_wTypeP T P Q :
  inhabited {x : T | P x & Q x} = exists2 x : T, P x & Q x.
Proof. by eqInh=> [[x Px Qx] | /cid2//]; exists x. Qed.
Canonical sig2_wType T P Q := ProperWitnessedType (@sig2_wTypeP T P Q).

Local Fact sigT_wTypeP A P T :
  inhabited {x : A & wTycon P T x} = (exists x : A, P x).
Proof. by eqInh=> [[x /wTypeP] | /cid[x /T]]; exists x. Qed.
Canonical sigT_wType A P T := ProperWitnessedType (@sigT_wTypeP A P T).

Local Fact sigT2_wTypeP A P Q S T :
  inhabited {x : A & wTycon P S x & wTycon Q T x} = (exists2 x : A, P x & Q x).
Proof. by eqInh=> [[x /wTypeP-Px /wTypeP] | /cid2[x /S-y /T]]; exists x. Qed.
Canonical sigT2_wType A P Q S T :=
  ProperWitnessedType (@sigT2_wTypeP A P Q S T).

(**md**************************************************************************)
(* The witnessProp structure provides for conversion of some Prop             *)
(* assumptions to Type values with some constructive contents, e.g., convert  *)
(* a P \/ Q assumption to a {P} + {Q} sumbool value. This is not the same as  *)
(* the forward direction of witnessedType, because instances here match the   *)
(* Prop statement: witness_Prop find a T such that P -> T while witnessedType *)
(* finds a P such that P -> T (and T -> P for the converse direction).        *)
(******************************************************************************)

(**md**************************************************************************)
(* The implementation follows the wrapper telescope pattern similarly to      *)
(* negatedProp, with three rules, one for Prop constructors with proper       *)
(* constructive contents, one for forall propositions (also with proper       *)
(* constructive contents) and one default rule that just returns P : Prop as  *)
(* is (thus, with no other contents except the provability of P).             *)
(*                                                                            *)
(* The witnessProp structure also uses projection parameters to return the    *)
(* inferred Type T together with a bool 'trivial' flag that is set when the   *)
(* trivial rule is used. Here, however, this flag is used in both directions: *)
(* the 'witness' view forces it to false to prevent trivial instances, but    *)
(* the flag is also used to fine tune the choice of T, selecting between      *)
(* sum, sumor, and sumbool, between sig and sigT, and sig2 and sigT2. This    *)
(* relies on the fact that the tactic engine will eagerly iota reduce the     *)
(* returned type, so that the user will never see the conditionals specified  *)
(* in the proper_witness_Prop instances.                                      *)
(*                                                                            *)
(* However, it would not be possible to construct the specialised types       *)
(* for trivial witnesses (e.g., {P} + {Q}) using the types returned by        *)
(* witnessProp instances, since thes are in Type, and the information that    *)
(* they are actully in Prop has been lost. This is solved by returning an     *)
(* additional Prop P0 that is a copy of the matched Prop P when               *)
(* trivial = true. (We put P0 = True when trivial = false, as we only need to *)
(* ensure P -> P0.)                                                           *)
(*                                                                            *)
(* Caveat: although P0 should in principle be the last parameter of           *)
(* witness_Prop, and we use this order for the wProp and wPred projector      *)
(* local notation, it is important to put P0 _BEFORE_ T, to circumvent an     *)
(* incompleteness in Coq's implementation of higher-order pattern unification *)
(* that would cause the trivial rule to fail for the body of an exists.       *)
(* In such a case the rule needs to unify (1) ?P0 x ~ ?P and (2) ?T x ~ ?P    *)
(* for some type A some x : A in the context of ?P, but not ?P0 nor ?T. This  *)
(* succeeds easily if (1) is performed before (2), setting ?P := ?P0 x and    *)
(* ?T := ?P0, but if (2) is attempted first Coq tries to perform ?P := ?T x,  *)
(* which fails Type/Prop universe constraints, and then fails outright,       *)
(* instead of using pattern unification to solve (2) as ?P := ?Q x, ?T := ?Q  *)
(* for a fresh ?Q : A -> Prop.                                                *)
(******************************************************************************)

Structure witnessProp (trivial : bool) (P0 : Prop) (T : Type) :=
  WitnessProp {witness_Prop :> wrappedProp; _ : witness_Prop -> T * P0}.
Structure properWitnessProp T :=
  ProperWitnessProp {proper_witness_Prop :> Prop; _ : proper_witness_Prop -> T}.

Local Notation wProp t T P0 P := (unwrap_Prop (@witness_Prop t P0 T P)).
Local Notation wPred t T P0 P x := (wProp t (T x) (P0 x) (P x)).

Local Fact wPropP t T P0 P : wProp t T P0 P -> T * P0. Proof. by case: P. Qed.
Lemma lax_witness {t T P0 P} : move_view (wProp t T P0 P) T.
Proof. by split=> /wPropP[]. Qed.
Definition witness {T P0 P} := @lax_witness false T P0 P.

(** Rule 1: proper instances (except forall), delegated to an auxiliary
    structures. *)
Local Fact proper_wPropP T P : wrap1Prop (@proper_witness_Prop T P) -> T * True.
Proof. by case: P => _ P_T {}/P_T. Qed.
Canonical proper_wProp T P := WitnessProp false (@proper_wPropP T P).

(** Rule 2: forall types (including implication); as only proper instances are
    allowed, we set trivial = false for the recursive body instance. *)
Local Fact forall_wPropP A T P0 P :
  wrap2Prop (forall x : A, wPred false T P0 P x) -> (forall x, T x) * True.
Proof. by move=> P_A; split=> // x; have /witness := P_A x. Qed.
Canonical forall_wProp A T P0 P := WitnessProp false (@forall_wPropP A T P0 P).

(** Rule 3: trivial (proof) self-witness. *)
Canonical trivial_wProp P :=
  WitnessProp true (fun p : wrap3Prop P => (p, p) : P * P).

(** Specific proper_witnesss_Prop instances. *)

Canonical inhabited_wProp T := ProperWitnessProp (@inhabited_witness T).

(**md**************************************************************************)
(* Conjunctions P /\ Q are a little delicate to handle, as we should not      *)
(* produce a proper instance (and thus fail) if neither P nor Q is proper.    *)
(* We use a tertiary structure for this : nand_bool b, which has instances    *)
(* only for booleans b0 such that ~~ (b0 && b). We allow the witness_Prop     *)
(* instance for P to return an arbitrary 'trivial' flag s, but then force the *)
(* 'trivial' flag for Q to be an instance of nand_bool s.                     *)
(******************************************************************************)

Structure nandBool b := NandBool {nand_bool :> bool; _ : ~~ (nand_bool && b)}.
Canonical nand_false_bool b := @NandBool b false isT.
Canonical nand_true_bool := @NandBool false true isT.

Local Fact and_wPropP s S P0 P (t : nandBool s) T Q0 Q :
  wProp s S P0 P /\ wProp t T Q0 Q -> S * T.
Proof. by case=> /lax_witness-x /lax_witness. Qed.
Canonical and_wProp s S P0 P t T Q0 Q :=
  ProperWitnessProp (@and_wPropP s S P0 P t T Q0 Q).

(* The first : Type cast ensures the return type of the inner 'if' is not     *)
(* incorrectly set to 'Set', while the second merely ensures the S + T        *)
(* notation is resolved correctly).                                           *)
Local Fact or_wPropP s S P0 P t T Q0 Q :
    wProp s S P0 P \/ wProp t T Q0 Q ->
  if t then if s then {P0} + {Q0} : Type else S + {Q0} else S + T : Type.
Proof.
by case: s t => -[] in P Q *; (case/decide_or=> /wPropP[]; [left | right]).
Qed.
Canonical or_wProp s S P0 P t T Q0 Q :=
  ProperWitnessProp (@or_wPropP s S P0 P t T Q0 Q).

Local Fact exists_wPropP A t T P0 P :
  (exists x : A, wPred t T P0 P x) -> if t then {x | P0 x} else {x & T x}.
Proof. by case/cid => x /wPropP[]; case t; exists x. Qed.
Canonical exists_wProp A t T P0 P :=
  ProperWitnessProp (@exists_wPropP A t T P0 P).

(* Note the expanded expression for st = s && t, which will be reduced to     *)
(* true or false by iota reduction when s and t are known.                    *)
Local Fact exists2_wPropP A s S P0 P t T Q0 Q (st := if s then t else false) :
    (exists2 x : A, wPred s S P0 P x & wPred t T Q0 Q x) ->
  if st then {x | P0 x & Q0 x} else {x : A & S x & T x}.
Proof. by case/cid2=> x /wPropP[P0x y] /wPropP[]; case: ifP; exists x. Qed.
Canonical exists2_wProp A s S P0 P t T Q0 Q :=
  ProperWitnessProp (@exists2_wPropP A s S P0 P t T Q0 Q).

(**md**************************************************************************)
(* ## User lemmas and tactics for proof by contradiction and contraposition.  *)
(******************************************************************************)

(**md**************************************************************************)
(* Helper lemmas:                                                             *)
(* - push_goal_copy makes a copy of the goal that can then be matched with    *)
(*     witnessedType and negatedProp instances to generate a contradiction    *)
(*     assuption, without disturbing the original form of the goal.           *)
(* - assume_not_with turns the copy generated by push_identity into an        *)
(*     equivalent negative assumption, which can then be simplified using the *)
(*     lax_notP and lax_witness views.                                        *)
(* - absurd and absurdW replace the goal with False; absurdW does this under  *)
(*     an assumption, and is used to weaken proof-by-assuming-negation to     *)
(*     proof-by-contradiction.                                                *)
(* - contra_Type converts an arbitrary function goal (with assumption and     *)
(*     conclusion in Type) to an equivalent contrapositive Prop implication.  *)
(* - contra_notP simplifies a contrapositive ~ Q -> ~ P goal using            *)
(*     negatedProp instances.                                                 *)
(******************************************************************************)

Local Fact push_goal_copy {T} : ((T -> T) -> T) -> T. Proof. exact. Qed.
Local Fact assume_not_with {R P T} : (~ P -> R) -> (wType P T -> R) -> R.
Proof. by move=> nP_T T_R; have [/T|] := asboolP P. Qed.

Local Fact absurdW {S T} : (S -> False) -> S -> T. Proof. by []. Qed.

Local Fact contra_Type {P Q S T} : (~ Q -> ~ P) -> wType P S -> wType Q T.
Proof. by rewrite implyNN => P_Q /wTypeP/P_Q/T. Qed.

Local Fact contra_notP tP tQ (nP nQ : Prop) P Q :
  (nP -> nQ) -> (~ nProp tP nP P -> ~ nProp tQ nQ Q).
Proof. by rewrite 2!lax_notE. Qed.

End Internals.
Import Internals.
Definition notP := @Internals.notP.
Hint View for move/ move_viewP|2.
Hint View for move/ Internals.equivT_LR|2 Internals.equivT_RL|2.
Hint View for apply/ Internals.equivT_RL|2 Internals.equivT_LR|2.
Export (canonicals) Internals.

(**md**************************************************************************)
(* Lemma and tactic assume_not: add a goal negation assumption. The tactic    *)
(* also works for goals in Type, simplifies the added assumption, and         *)
(* exposes its top-level constructive content.                                *)
(******************************************************************************)

Lemma assume_not {P} : (~ P -> P) -> P. Proof. by rewrite implyNp orB. Qed.
Ltac assume_not :=
  apply: Internals.push_goal_copy; apply: Internals.assume_not_with
    => /Internals.lax_notP-/Internals.lax_witness.

(**md**************************************************************************)
(* Lemma and tactic absurd_not: proof by contradiction. Same as assume_not,   *)
(* but the goal is erased and replaced by False.                              *)
(* Caveat: absurd_not cannot be used as a move/ view because its conclusion   *)
(* is indeterminate. The more general notP defined above can be used instead. *)
(******************************************************************************)
Lemma absurd_not {P} : (~ P -> False) -> P. Proof. by move/Internals.notP. Qed.
Ltac absurd_not := assume_not; apply: Internals.absurdW.

(**md**************************************************************************)
(* Tactic contra: proof by contraposition. Assume the negation of the goal    *)
(* conclusion, and prove the negation of a given assumption. The defective    *)
(* form contra (which can also be written contrapose) expects the assumption  *)
(* to be pushed on the goal which thus has the form assumption -> conclusion. *)
(*                                                                            *)
(* As with assume_not, contra allows both assumption and conclusion to be     *)
(* in Type, simplifies the negation of both assumption and conclusion, and    *)
(* exposes the constructive contents of the negated conclusion.               *)
(*                                                                            *)
(* The contra tactic also supports a limited form of the ':' discharge        *)
(* pseudo tactical, whereby contra: <d-items> means move: <d-items>; contra.  *)
(* The only <d-items> allowed are one term, possibly preceded by a clear      *)
(* switch.                                                                    *)
(******************************************************************************)

Ltac contrapose :=
  apply: Internals.contra_Type;
  apply: Internals.contra_notP => /Internals.lax_witness.
Tactic Notation "contra" := contrapose.
Tactic Notation "contra" ":" constr(H) := move: (H); contra.
Tactic Notation "contra" ":" ident(H) := move: H; contra.
Tactic Notation "contra" ":" "{" hyp_list(Hs) "}" constr(H) :=
  contra: (H); clear Hs.
Tactic Notation "contra" ":" "{" hyp_list(Hs) "}" ident(H) :=
  contra: H; clear Hs.
Tactic Notation "contra" ":" "{" "-" "}" constr(H) := contra: (H).

(**md**************************************************************************)
(* Lemma and tactic absurd: proof by contradiction. The defective form of the *)
(* lemma simply replaces the entire goal with False (just as the Ltac         *)
(* exfalso), leaving the user to derive a contradiction from the assumptions. *)
(* The ':' form absurd: <d-items> replaces the goal with the negation of the  *)
(* (single) <d-item> (as with contra:, a clear switch is also allowed.        *)
(* Finally the Ltac absurd term form is also supported.                       *)
(******************************************************************************)

Lemma absurd T : False -> T. Proof. by []. Qed.
Tactic Notation (at level 0) "absurd" := apply absurd.
Tactic Notation (at level 0) "absurd" constr(P) := have []: ~ P.
Tactic Notation "absurd" ":" constr(H) := absurd; contra: (H) => _.
Tactic Notation "absurd" ":" ident(H) := absurd; contra: H => _.
Tactic Notation "absurd" ":" "{" hyp_list(Hs) "}" constr(H) :=
  absurd: (H) => _; clear Hs.
Tactic Notation "absurd" ":" "{" hyp_list(Hs) "}" ident(H) :=
  absurd: H => _; clear Hs.
