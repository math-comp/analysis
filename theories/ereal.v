(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import finmap.
Require Import boolp classical_sets reals posnum topology.

(******************************************************************************)
(*                        Extended real numbers                               *)
(*                                                                            *)
(* Given a type R for numbers, {ereal R} is the type R extended with symbols  *)
(* -oo and +oo (notation scope: %E), suitable to represent extended real      *)
(* numbers. When R is a numDomainType, {ereal R} is equipped with a canonical *)
(* porderType and operations for addition/opposite. When R is a               *)
(* realDomainType, {ereal R} is equipped with a Canonical orderType.          *)
(*                                                                            *)
(*                    r%:E == injects real numbers into {ereal R}             *)
(*                +%E, -%E == addition/opposite for extended reals            *)
(*  (_ <= _)%E, (_ < _)%E, == comparison relations for extended reals         *)
(*  (_ >= _)%E, (_ > _)%E                                                     *)
(*   (\sum_(i in A) f i)%E == bigop-like notation in scope %E                 *)
(*             ereal_sup E == supremum of E                                   *)
(*             ereal_inf E == infimum of E                                    *)
(*  ereal_supremums_neq0 S == S has a supremum                                *)
(*                                                                            *)
(* Topology of extended real numbers:                                         *)
(*        ereal_topologicalType R == topology for extended real numbers over  *)
(*                                   R, a realFieldType                       *)
(*                       contract == order-preserving bijective function      *)
(*                                   from extended real numbers to [-1; 1]    *)
(*                         expand == function from real numbers to extended   *)
(*                                   real numbers that cancels contract in    *)
(*                                   [-1; 1]                                  *)
(*       ereal_pseudoMetricType R == pseudometric space for extended reals    *)
(*                                   over R where is a realFieldType; the     *)
(*                                   distance between x and y is defined by   *)
(*                                   `|contract x - contract y|               *)
(*                                                                            *)
(* Filters:                                                                   *)
(*                  ereal_nbhs' x == filter on extended real numbers that     *)
(*                                   corresponds to nbhs' x if x is a real    *)
(*                                   number and to predicates that are        *)
(*                                   eventually true if x is +oo/-oo.         *)
(*                   ereal_nbhs x == same as ereal_nbhs' where nbhs' is       *)
(*                                   replaced with nbhs.                      *)
(*                ereal_loc_seq x == sequence that converges to x in the set  *)
(*                                   of extended real numbers.                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: add to bigop.v *)
Lemma big_nat_widenl (R : Type) (idx : R) (op : Monoid.law idx) (m1 m2 n : nat)
    (P : pred nat) (F : nat -> R) :
  m2 <= m1 ->
  \big[op/idx]_(m1 <= i < n | P i) F i =
  \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> le_m21; have [le_nm1|lt_m1n] := leqP n m1.
  rewrite big_geq// big_nat_cond big1//.
  by move=> i /and3P[/andP[_ /leq_trans/(_ le_nm1)/ltn_geF->]].
rewrite big_mkcond big_mkcondl (big_cat_nat _ _ _ le_m21) 1?ltnW//.
rewrite [X in op X]big_nat_cond [X in op X]big_pred0; last first.
  by move=> k; case: ltnP; rewrite andbF.
by rewrite Monoid.mul1m; apply: congr_big_nat => // k /andP[].
Qed.
Arguments big_nat_widenl [R idx op].

(* TODO: add to bigop.v *)
Lemma big_geq_mkord (R : Type) (idx : R) (op : Monoid.law idx) (m n : nat)
    (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(m <= i < n | P i) F i =
  \big[op/idx]_(i < n | P i && (m <= i)) F i.
Proof. by rewrite (big_nat_widenl _ 0)// big_mkord. Qed.

Declare Scope ereal_scope.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.

Inductive er (R : Type) := ERFin of R | ERPInf | ERNInf.

Definition er_map T T' (f : T -> T') (x : er T) : er T' :=
  match x with
  | ERFin x => ERFin (f x)
  | ERPInf => ERPInf _
  | ERNInf => ERNInf _
  end.

Section ExtendedReals.
Variable (R : numDomainType).

Coercion real_of_er x : R :=
  if x is ERFin v then v else 0.

End ExtendedReals.
Arguments real_of_er {R}.

Notation "+oo" := (@ERPInf _) : ereal_scope.
Notation "-oo" := (@ERNInf _) : ereal_scope.
Notation "x %:E" := (@ERFin _ x) (at level 2, format "x %:E").

Notation "{ 'ereal' R }" := (er R) (format "{ 'ereal'  R }").

Bind    Scope ereal_scope with er.
Delimit Scope ereal_scope with E.

Local Open Scope ereal_scope.

Section EqEReal.
Variable (R : eqType).

Definition eq_ereal (x y : {ereal R}) :=
  match x, y with
    | x%:E, y%:E => x == y
    | +oo, +oo => true
    | -oo, -oo => true
    | _, _ => false
  end.

Lemma ereal_eqP : Equality.axiom eq_ereal.
Proof. by case=> [?||][?||]; apply: (iffP idP) => //= [/eqP|[]] ->. Qed.

Definition ereal_eqMixin := Equality.Mixin ereal_eqP.
Canonical ereal_eqType := Equality.Pack ereal_eqMixin.

Lemma eqe (x1 x2 : R) : (x1%:E == x2%:E) = (x1 == x2). Proof. by []. Qed.

End EqEReal.

Section ERealChoice.
Variable (R : choiceType).

Definition code (x : {ereal R}) :=
  match x with
  | x%:E => GenTree.Node 0 [:: GenTree.Leaf x]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option {ereal R} :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf x] => Some x%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

Definition ereal_choiceMixin := PcanChoiceMixin codeK.
Canonical ereal_choiceType  := ChoiceType {ereal R} ereal_choiceMixin.

End ERealChoice.

Section ERealCount.
Variable (R : countType).

Definition ereal_countMixin := PcanCountMixin (@codeK R).
Canonical ereal_countType := CountType {ereal R} ereal_countMixin.

 End ERealCount.

Section ERealOrder.
Context {R : numDomainType}.
Implicit Types (x y : {ereal R}).

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x%:E | x%:E, +oo => x \is Num.real
  | x1%:E, x2%:E => x1 <= x2
  | -oo, _    | _, +oo => true
  | +oo, _    | _, -oo => false
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x%:E | x%:E, +oo => x \is Num.real
  | x1%:E, x2%:E => x1 < x2
  | -oo, -oo  | +oo, +oo => false
  | +oo, _    | _  , -oo => false
  | -oo, _  => true
  end.

Lemma lt_def_ereal x y : lt_ereal x y = (y != x) && le_ereal x y.
Proof. by case: x y => [?||][?||] //=; rewrite lt_def eqe. Qed.

Lemma le_refl_ereal : reflexive le_ereal.
Proof. by case => /=. Qed.

Lemma le_anti_ereal : ssrbool.antisymmetric le_ereal.
Proof. by case=> [?||][?||]/=; rewrite ?andbF => // /le_anti ->. Qed.

Lemma le_trans_ereal : ssrbool.transitive le_ereal.
Proof.
case=> [?||][?||][?||] //=; rewrite -?comparabler0; first exact: le_trans.
  by move=> /le_comparable cmp /(comparabler_trans cmp).
by move=> cmp /ge_comparable /comparabler_trans; apply.
Qed.

Fact ereal_display : unit. Proof. by []. Qed.

Definition ereal_porderMixin :=
  LePOrderMixin lt_def_ereal le_refl_ereal le_anti_ereal le_trans_ereal.

Canonical ereal_porderType :=
  POrderType ereal_display {ereal R} ereal_porderMixin.

Lemma leEereal x y : (x <= y)%O = le_ereal x y. Proof. by []. Qed.
Lemma ltEereal x y : (x < y)%O = lt_ereal x y. Proof. by []. Qed.

End ERealOrder.

Notation lee := (@Order.le ereal_display _) (only parsing).
Notation "@ 'lee' R" :=
  (@Order.le ereal_display R) (at level 10, R at level 8, only parsing).
Notation lte := (@Order.lt ereal_display _) (only parsing).
Notation "@ 'lte' R" :=
  (@Order.lt ereal_display R) (at level 10, R at level 8, only parsing).
Notation gee := (@Order.ge ereal_display _) (only parsing).
Notation "@ 'gee' R" :=
  (@Order.ge ereal_display R) (at level 10, R at level 8, only parsing).
Notation gte := (@Order.gt ereal_display _) (only parsing).
Notation "@ 'gte' R" :=
  (@Order.gt ereal_display R) (at level 10, R at level 8, only parsing).

Notation "x <= y" := (lee x y) (only printing) : ereal_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_scope.

Notation "x <= y" := (lee (x : er _) (y : er _)) : ereal_scope.
Notation "x < y"  := (lte (x : er _) (y : er _)) : ereal_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_scope.

Lemma lee_fin (R : numDomainType) (x y : R) : (x%:E <= y%:E) = (x <= y)%R.
Proof. by []. Qed.

Lemma lte_fin (R : numDomainType) (x y : R) : (x%:E < y%:E) = (x < y)%R.
Proof. by []. Qed.

Lemma lte_pinfty (R : realDomainType) (x : R) : x%:E < +oo.
Proof. exact: num_real. Qed.

Lemma lee_pinfty (R : realDomainType) (x : {ereal R}) : x <= +oo.
Proof. case: x => //= r; exact: num_real. Qed.

Lemma gee0P (R : realDomainType) (x : {ereal R}) :
  0%:E <= x <-> x = +oo \/ exists2 r, (r >= 0)%R & x = r%:E.
Proof.
split=> [|[->|[r r0 ->//]]]; last exact: lee_pinfty.
by case: x => [r r0 | _ |//]; [right; exists r|left].
Qed.

Lemma lte_ninfty (R : realDomainType) (x : R) : (-oo < x%:E).
Proof. exact: num_real. Qed.

Lemma lee_ninfty (R : realDomainType) (x : {ereal R}) : -oo <= x.
Proof. case: x => //= r; exact: num_real. Qed.

Lemma lee_ninfty_eq (R : numDomainType) (x : {ereal R}) : (x <= -oo) = (x == -oo).
Proof. by case: x. Qed.

Lemma lee_pinfty_eq (R : numDomainType) (x : {ereal R}) : (+oo <= x) = (x == +oo).
Proof. by case: x. Qed.

Section ERealOrder_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y : {ereal R}).

Lemma le_total_ereal : totalPOrderMixin [porderType of {ereal R}].
Proof.
by move=> [?||][?||]//=; rewrite (ltEereal, leEereal)/= ?num_real ?le_total.
Qed.

Canonical ereal_latticeType := LatticeType {ereal R} le_total_ereal.
Canonical ereal_distrLatticeType :=  DistrLatticeType {ereal R} le_total_ereal.
Canonical ereal_orderType := OrderType {ereal R} le_total_ereal.

End ERealOrder_realDomainType.

Section ERealArith.
Context {R : numDomainType}.

Implicit Types (x y z : {ereal R}).

Definition adde x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.

Definition oppe x :=
  match x with
  | x%:E  => (-x)%:E
  | -oo => +oo
  | +oo => -oo
  end.

Definition mule x y :=
  match x, y with
  | x%:E , y%:E => (x * y)%:E
  | -oo, y | y, -oo => if 0%:E <= y then -oo else +oo
  | +oo, y | y, +oo => if 0%:E < y then +oo else -oo
  end.

Definition abse x := if x is r%:E then `|r|%:E else +oo.

End ERealArith.

Notation "+%E"   := adde.
Notation "-%E"   := oppe.
Notation "x + y" := (adde x y) : ereal_scope.
Notation "x - y" := (adde x (oppe y)) : ereal_scope.
Notation "- x"   := (oppe x) : ereal_scope.
Notation "*%E"   := mule.
Notation "x * y" := (mule x y) : ereal_scope.
Notation "`| x |" := (abse x) : ereal_scope.

Notation "f \+ g" := (fun x => f x + g x)%E : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%:E]_(i <- r | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%:E]_(i <- r) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%:E]_(m <= i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%:E]_(m <= i < n) F%R) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%:E]_(i | P%B) F%R) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%:E]_i F%R) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%:E]_(i : t | P%B) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%:E]_(i : t) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%:E]_(i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%:E]_(i < n) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%:E]_(i in A | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%:E]_(i in A) F%R) : ereal_scope.

Section ERealOrderTheory.
Context {R : numDomainType}.
Implicit Types x y z : {ereal R}.

Local Tactic Notation "elift" constr(lm) ":" ident(x) :=
  by case: x => [||?]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) :=
  by case: x y => [?||] [?||]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) ident(z) :=
  by case: x y z => [?||] [?||] [?||]; first by rewrite ?eqe; apply: lm.

Lemma le0R (x : {ereal R}) :
  0%:E <= x -> (0 <= real_of_er(*TODO: coercion broken*) x)%R.
Proof. by case: x. Qed.

Lemma lee_tofin (r0 r1 : R) : (r0 <= r1)%R -> r0%:E <= r1%:E.
Proof. by []. Qed.

Lemma lte_tofin (r0 r1 : R) : (r0 < r1)%R -> r0%:E < r1%:E.
Proof. by []. Qed.

End ERealOrderTheory.

Section finNumPred.
Context {R : numDomainType}.

Definition fin_num := [qualify a x : er R | (x != -oo) && (x != +oo)].
Fact fin_num_key : pred_key fin_num. by []. Qed.
Canonical fin_num_keyd := KeyedQualifier fin_num_key.

Lemma fin_numE x : (x \is a fin_num) = ((x != -oo) && (x != +oo)).
Proof. by []. Qed.

Lemma fin_numP x : reflect ((x != -oo) /\ (x != +oo)) (x \in fin_num).
Proof. by apply/(iffP idP) => [/andP//|/andP]. Qed.

End finNumPred.

Section ERealArithTh_numDomainType.

Context {R : numDomainType}.

Implicit Types x y z : {ereal R}.

Lemma NERFin (x : R) : (- x)%R%:E = (- x%:E). Proof. by []. Qed.

Lemma real_of_erN x : real_of_er (- x) = (- real_of_er x)%R.
Proof. by case: x => //=; rewrite oppr0. Qed.

Lemma addERFin (r r' : R) : (r + r')%R%:E = r%:E + r'%:E.
Proof. by []. Qed.

Lemma sumERFin I r P (F : I -> R) :
  \sum_(i <- r | P i) (F i)%:E = (\sum_(i <- r | P i) F i)%R%:E.
Proof. by rewrite (big_morph _ addERFin erefl). Qed.

Lemma subERFin (r r' : R) : (r - r')%R%:E = r%:E - r'%:E.
Proof. by []. Qed.

Definition adde_undef x y :=
  (x == +oo) && (y == -oo) || (x == -oo) && (y == +oo).

Lemma adde_undefC x y : adde_undef x y = adde_undef y x.
Proof. by rewrite /adde_undef andbC orbC andbC. Qed.

Lemma adde0 : right_id (0%:E : {ereal R}) +%E.
Proof. by case=> //= x; rewrite addr0. Qed.

Lemma add0e : left_id (0%:E : {ereal R}) +%E.
Proof. by case=> //= x; rewrite add0r. Qed.

Lemma addeC : commutative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] //=; rewrite addrC. Qed.

Lemma addeA : associative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] [z||] //=; rewrite addrA. Qed.

Canonical adde_monoid := Monoid.Law addeA add0e adde0.
Canonical adde_comoid := Monoid.ComLaw addeC.

Lemma addeAC : @right_commutative {ereal R} _ +%E.
Proof. by move=> x y z; rewrite -addeA (addeC y) addeA. Qed.

Lemma addeCA : @left_commutative {ereal R} _ +%E.
Proof. by move=> x y z; rewrite addeC -addeA (addeC x). Qed.

Lemma addeACA : @interchange {ereal R} +%E +%E.
Proof. by case=> [r||] [s||] [t||] [u||]//=; rewrite addrACA. Qed.

Lemma oppe0 : - 0%:E = 0%:E :> {ereal R}.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := {ereal R}) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.

Lemma oppeD x (r : R) : - (x + r%:E) = - x - r%:E.
Proof. by move: x => [x| |] //=; rewrite opprD. Qed.

Lemma muleC x y : x * y = y * x.
Proof. by case: x y => [r||] [s||]//=; rewrite mulrC. Qed.

Lemma mule1 x : x * 1%:E = x.
Proof. by case: x => [r||]/=; rewrite ?mulr1 ?lee_tofin ?lte_tofin. Qed.

Lemma mul1e x : 1%:E * x = x.
Proof. by rewrite muleC mule1. Qed.

Lemma abseN x : `|- x| = `|x|.
Proof. by case: x => [r||]; rewrite //= normrN. Qed.

Lemma eqe_opp x y : (- x == - y) = (x == y).
Proof.
move: x y => [r| |] [r'| |] //=; apply/idP/idP => [|/eqP[->]//].
by move/eqP => -[] /eqP; rewrite eqr_opp => /eqP ->.
Qed.

Lemma eqe_oppP x y : (- x = - y) <-> (x = y).
Proof. by split=> [/eqP | -> //]; rewrite eqe_opp => /eqP. Qed.

Lemma eqe_oppLR x y : (- x == y) = (x == - y).
Proof. by move: x y => [r0| |] [r1| |] //=; rewrite !eqe eqr_oppLR. Qed.

Lemma eqe_oppLRP x y : (- x = y) <-> (x = - y).
Proof.
split=> /eqP; first by rewrite eqe_oppLR => /eqP.
by rewrite -eqe_oppLR => /eqP.
Qed.

Lemma oppe_subset (A B : set {ereal R}) :
  ((A `<=` B) <-> (-%E @` A `<=` -%E @` B))%classic.
Proof.
split=> [AB _ [] x ? <-|AB x Ax]; first by exists x => //; exact: AB.
have /AB[y By] : ((-%E @` A) (- x)%E)%classic by exists x.
by rewrite eqe_oppP => <-.
Qed.

Lemma fin_numN x : (- x \is a fin_num) = (x \is a fin_num).
Proof. by rewrite !fin_numE 2!eqe_oppLR andbC. Qed.

Lemma fin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma real_of_erD :
  {in (@fin_num R) &, {morph real_of_er : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fin_num_adde_undef x y : y \is a fin_num -> ~~ adde_undef x y.
Proof. by move: x y => [x| |] [y | |]. Qed.

Lemma ERFin_real_of_er x : x \is a fin_num -> x = (real_of_er x)%:E.
Proof. by case: x. Qed.

Lemma addeK x y : x \is a fin_num -> y + x - x = y.
Proof. by move: x y => [x| |] [y| |] //; rewrite -addERFin /= addrK. Qed.

Lemma subeK x y : y \is a fin_num -> x - y + y = x.
Proof. by move: x y => [x| |] [y| |] //; rewrite -addERFin subrK. Qed.

Lemma subee x : x \is a fin_num -> x - x = 0%:E.
Proof. by move: x => [r _| |] //; rewrite -subERFin subrr. Qed.

Lemma adde_eq_ninfty x y : (x + y == -oo) = ((x == -oo) || (y == -oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma addooe x : x != -oo -> +oo + x = +oo.
Proof. by case: x. Qed.

Lemma adde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma esum_fset_ninfty
    (T : choiceType) (s : {fset T}) (P : pred T) (f : T -> {ereal R}) :
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
split=> [|[i [si Pi fi]]]; last by rewrite big_mkcond (bigD1_seq i) //= Pi fi.
rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
Qed.

Lemma esum_ninfty n (f : 'I_n -> {ereal R}) :
  (\sum_(i < n) f i == -oo) = [exists i, f i == -oo].
Proof.
rewrite -big_enum -(big_fset _ (mem_fin (fin_finpred (pred_of_simpl 'I_n)))).
apply/idP/idP => [/eqP/esum_fset_ninfty|/existsP[i /eqP fioo]].
  by move=> -[i [_ _ fioo]]; apply/existsP; exists i; exact/eqP.
by apply/eqP/esum_fset_ninfty; exists i; split => //; rewrite inE.
Qed.

Lemma esum_fset_pinfty
    (T : choiceType) (s : {fset T}) (P : pred T) (f : T -> {ereal R}) :
  (forall i, P i -> f i != -oo) ->
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
move=> finoo; split=> [|[i [si Pi fi]]]; last first.
  rewrite big_mkcond (bigD1_seq i) //= Pi fi addooe //.
  apply/eqP => /esum_fset_ninfty; apply/forallNP => t [ts ti].
  by case: ifPn => // Pt /eqP; apply/negP; rewrite finoo.
rewrite big_seq_cond; elim/big_ind: _ => // [[x| |] [y| |] //|].
by  move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
Qed.

Lemma esum_pinfty n (f : 'I_n -> {ereal R}) : (forall i, f i != -oo) ->
  (\sum_(i < n) f i == +oo) = [exists i, f i == +oo].
Proof.
move=> finoo.
rewrite -big_enum -(big_fset _ (mem_fin (fin_finpred (pred_of_simpl 'I_n)))).
apply/idP/existsP => [/eqP /=|[/= i /eqP fioo]].
  have {}finoo : (forall i, xpredT i -> f i != -oo) by move=> i _; exact: finoo.
  by move/(esum_fset_pinfty _ finoo) => [i [_ _ fioo]]; exists i; rewrite fioo.
by apply/eqP/esum_fset_pinfty => //; exists i; split => //; rewrite inE.
Qed.

Lemma adde_ge0 x y : 0%:E <= x -> 0%:E <= y -> 0%:E <= x + y.
Proof. by move: x y => [r0| |] [r1| |] // ? ?; rewrite !lee_fin addr_ge0. Qed.

Lemma sume_ge0 T (f : T -> {ereal R}) (P : pred T) :
  (forall t, P t -> 0%:E <= f t) -> forall l, 0%:E <= \sum_(i <- l | P i) f i.
Proof. by move=> f0 l; elim/big_rec : _ => // t x Pt; apply/adde_ge0/f0. Qed.

End ERealArithTh_numDomainType.

Section ERealArithTh_realDomainType.

Context {R : realDomainType}.
Implicit Types x y z a b : {ereal R}.

Lemma sube_gt0 x y : (0%:E < y - x) = (x < y).
Proof.
move: x y => [r | |] [r'| |] //=; rewrite ?(lte_pinfty,lte_ninfty) //.
by rewrite !lte_fin subr_gt0.
Qed.

Lemma sube_le0 x y : (y - x <= 0%:E) = (y <= x).
Proof.
by move: x y => [x| |] [y| |]; apply/idP/idP => //=; try
  (rewrite !(lee_pinfty,lee_ninfty) || rewrite !lee_fin subr_le0).
Qed.

Lemma suber_ge0 r x : (0%:E <= x - r%:E) = (r%:E <= x).
Proof.
move: x => [x| |] //=; rewrite ?(lee_pinfty,lee_ninfty,lee_fin) //=.
by rewrite subr_ge0.
Qed.

Lemma subre_ge0 x r : (0%:E <= r%:E - x) = (x <= r%:E).
Proof.
move: x => [x| |] //=; rewrite ?(lee_pinfty,lee_ninfty,lee_fin) //=.
by rewrite subr_ge0.
Qed.

Lemma lte_oppl x y : (- x < y) = (- y < x).
Proof.
move: x y => [r| |] [r'| |] //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_oppl.
Qed.

Lemma lte_oppr x y : (x < - y) = (y < - x).
Proof.
move: x y => [r| |] [r'| |] //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_oppr.
Qed.

Lemma lte_add a b x y : a < b -> x < y -> a + x < b + y.
Proof.
move: a b x y => [a| |] [b| |] [x| |] [y| |]; rewrite ?(lte_pinfty,lte_ninfty)//.
by rewrite !lte_fin; exact: ltr_add.
Qed.

Lemma lee_addl x y : 0%:E <= y -> x <= x + y.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ler_addl | move=> _; exact: lee_pinfty].
Qed.

Lemma lee_addr x y : 0%:E <= y -> x <= y + x.
Proof. by rewrite addeC; exact: lee_addl. Qed.

Lemma lte_addl r x : 0%:E < x -> r%:E < r%:E + x.
Proof.
by move: x => [x| |] //; rewrite ?lte_pinfty ?lte_ninfty // !lte_fin ltr_addl.
Qed.

Lemma lte_add2lE (r : R) a b : (r%:E + a < r%:E + b) = (a < b).
Proof.
move: a b => [a| |] [b| |] //; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_add2l.
Qed.

Lemma lee_add2l x a b : a <= b -> x + a <= x + b.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
- by rewrite !lee_fin ler_add2l.
- move=> r _; exact: lee_pinfty.
- move=> -[b [|  |]// | []// | //] r oob; exact: lee_ninfty.
Qed.

Lemma lee_add2lE r a b : (r%:E + a <= r%:E + b) = (a <= b).
Proof.
move: a b => [a| |] [b| |] //; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_add2l.
Qed.

Lemma lee_add2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite addeC (addeC b); exact: lee_add2l. Qed.

Lemma lee_add a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof.
move: a b x y => [a| |] [b| |] [x| |] [y| |]; rewrite ?(lee_pinfty,lee_ninfty)//.
by rewrite !lee_fin; exact: ler_add.
Qed.

Lemma lte_le_add r t x y : r%:E < x -> t%:E <= y -> r%:E + t%:E < x + y.
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_pinfty,lte_ninfty)//.
by rewrite !lte_fin; exact: ltr_le_add.
Qed.

Lemma lee_sub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof.
move: x y z t => -[x| |] -[y| |] -[z| |] -[t| |] //=;
  rewrite ?(lee_pinfty,lee_ninfty)//.
by rewrite !lee_fin; exact: ler_sub.
Qed.

Lemma lee_sum I (f g : I -> {ereal R}) s (P : pred I) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i) g i.
Proof. by move=> Pfg; elim/big_ind2 : _ => // *; apply lee_add. Qed.

Lemma lee_sum_nneg_subset I (s : seq I) (P Q : {pred I}) (f : I -> {ereal R}) :
  {subset Q <= P} -> {in [predD P & Q], forall i, 0%:E <= f i} ->
  \sum_(i <- s | Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [X in _ <= X]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> {ereal R}) : (forall i, P i -> ~~ Q i -> 0%:E <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite [X in _ <= X](bigID Q) /= -[X in X <= _]adde0 lee_add //.
by rewrite sume_ge0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_nneg_ord (f : nat -> {ereal R}) (P : pred nat) :
  (forall n, P n -> 0%:E <= f n) ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite (big_ord_widen_cond j) // big_mkcondr /=.
by rewrite lee_sum // => k ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_nneg_natr (f : nat -> {ereal R}) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0%:E <= f n) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_nneg_ord (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma lee_sum_nneg_natl (f : nat -> {ereal R}) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> 0%:E <= f m) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !big_geq_mkord/=.
rewrite lee_sum_nneg_subset// => [k | k /and3P[_ /f0->//]].
by rewrite ?inE -!topredE/= => /andP[-> /(leq_trans le_ij)->].
Qed.

Lemma lee_sum_nneg_subfset (T : choiceType) (A B : {fset T}%fset) (P : pred T)
  (f : T -> {ereal R}) : {subset A <= B} ->
  {in [predD B & A], forall t, P t -> 0%:E <= f t} ->
  \sum_(t <- A | P t) f t <= \sum_(t <- B | P t) f t.
Proof.
move=> AB f0; rewrite [X in _ <= X]big_mkcond (big_fsetID _ (mem A) B) /=.
rewrite -[X in X <= _]adde0 lee_add //.
  rewrite -big_mkcond /= {1}(_ : A = [fset x in B | x \in A]%fset) //.
  by apply/fsetP=> t; rewrite !inE /= andbC; case: (boolP (_ \in _)) => // /AB.
rewrite big_fset /= big_seq_cond sume_ge0 // => t /andP[tB tA].
by case: ifPn => // Pt; rewrite f0 // !inE tA.
Qed.

Lemma lte_subl_addr x (r : R) z : (x - r%:E < z) = (x < z + r%:E).
Proof.
move: x r z => [x| |] r [z| |] //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_subl_addr.
Qed.

Lemma lte_subl_addl (r : R) y z : (r%:E - y < z) = (r%:E < y + z).
Proof.
move: y z => [y| |] [z| |] //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subl_addl.
Qed.

Lemma lte_subr_addr (r : R) y z : (r%:E < y - z) = (r%:E + z < y).
Proof.
move: y z => [y| |] [z| |] //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subr_addr.
Qed.

Lemma lee_subr_addr x y r : (x <= y - r%:E) = (x + r%:E <= y).
Proof.
move: y x => [y| |] [x| |] //=; rewrite ?lee_ninfty ?lee_pinfty //.
by rewrite !lee_fin ler_subr_addr.
Qed.

Lemma lee_subl_addr x (r : R) z : (x - r%:E <= z) = (x <= z + r%:E).
Proof.
move: x r z => [x| |] r [z| |] //=; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_subl_addr.
Qed.

Lemma lee_oppr x y : (x <= - y) = (y <= - x).
Proof.
move: x y => [r0| |] [r1| |] //=; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_oppr.
Qed.

Lemma lee_oppl x y : (- x <= y) = (- y <= x).
Proof.
move: x y => [r0| |] [r1| |] //=; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_oppl.
Qed.

End ERealArithTh_realDomainType.
Arguments lee_sum_nneg_ord {R}.
Arguments lee_sum_nneg_natr {R}.
Arguments lee_sum_nneg_natl {R}.

Lemma lee_opp2 {R : realDomainType} : {mono @oppe R : x y /~ x <= y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lee_fin !ler_opp2.
by rewrite lee_ninfty /Order.le /= realN num_real.
by rewrite lee_pinfty /Order.le /= realN num_real.
Qed.

Lemma lte_opp2 {R : realDomainType} : {mono @oppe R : x y /~ x < y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lte_fin !ltr_opp2.
by rewrite lte_ninfty /Order.lt /= realN num_real.
by rewrite lte_pinfty /Order.lt /= realN num_real.
Qed.

Section realFieldType_lemmas.
Variable R : realFieldType.
Implicit Types x y : {ereal R}.

Lemma lee_adde x y : (forall e : {posnum R}, x <= y + e%:num%:E) -> x <= y.
Proof.
move: x y => [x| |] [y| |] //=; rewrite ?(lee_ninfty,lee_pinfty) //;
  try by move/(_ (PosNum ltr01)).
rewrite lee_fin => abe; rewrite leNgt; apply/negP => ba; apply/existsNP : abe.
have xy : (0 < (x - y) / 2)%R by apply divr_gt0 => //; rewrite subr_gt0.
exists (PosNum xy); apply/negP; rewrite -ltNge lte_fin -ltr_subr_addl.
by rewrite ltr_pdivr_mulr // ltr_pmulr ?subr_gt0 // ltr1n.
Qed.

Lemma lte_spaddr (r : R) x y : 0%:E < y -> r%:E <= x -> r%:E < x + y.
Proof.
move: y x => [y| |] [x| |] //=; rewrite ?lte_fin ?ltt_fin ?lte_pinfty //.
exact: ltr_spaddr.
Qed.

End realFieldType_lemmas.

Section ereal_supremum.
Variable R : realFieldType.
Local Open Scope classical_set_scope.
Implicit Types S : set {ereal R}.
Implicit Types x y : {ereal R}.

Lemma ereal_ub_pinfty S : ubound S +oo.
Proof. by apply/ubP=> x _; rewrite lee_pinfty. Qed.

Lemma ereal_ub_ninfty S : ubound S -oo -> S = set0 \/ S = [set -oo].
Proof.
have [/eqP ->|/set0P[x Sx] Snoo] := boolP (S == set0); first by left.
right; rewrite predeqE => y; split => [/Snoo|->{y}].
  by rewrite lee_ninfty_eq => /eqP ->.
by have := Snoo _ Sx; rewrite lee_ninfty_eq => /eqP <-.
Qed.

Lemma ereal_supremums_set0_ninfty : supremums (@set0 {ereal R}) -oo.
Proof. by split; [exact/ubP | apply/lbP=> y _; rewrite lee_ninfty]. Qed.

Lemma supremum_pinfty S x0 : S +oo -> supremum x0 S = +oo.
Proof.
move=> Spoo; rewrite /supremum ifF; last by apply/eqP => S0; rewrite S0 in Spoo.
have sSoo : supremums S +oo.
  split; first exact: ereal_ub_pinfty.
  by move=> /= y /(_ _ Spoo); rewrite lee_pinfty_eq => /eqP ->.
case: xgetP.
  by move=> _ -> sSxget; move: (is_subset1_supremums sSoo sSxget).
by move/(_ +oo) => gSoo; exfalso; apply gSoo => {gSoo}.
Qed.

Definition ereal_sup S := supremum -oo S.

Definition ereal_inf S := - ereal_sup (-%E @` S).

Lemma ereal_sup0 : ereal_sup set0 = -oo.
Proof. by rewrite /ereal_sup /supremum eqxx. Qed.

Lemma ereal_sup1 x : ereal_sup [set x] = x.
Proof.
rewrite /ereal_sup /supremum ifF; last first.
  by apply/eqP; rewrite predeqE => /(_ x)[+ _]; apply.
by rewrite supremums_set1; case: xgetP => // /(_ x) /(_ erefl).
Qed.

Lemma ereal_inf0 : ereal_inf set0 = +oo.
Proof. by rewrite /ereal_inf image_set0 ereal_sup0. Qed.

Lemma ereal_inf1 x : ereal_inf [set x] = x.
Proof. by rewrite /ereal_inf image_set1 ereal_sup1 oppeK. Qed.

Lemma ub_ereal_sup S M : ubound S M -> ereal_sup S <= M.
Proof.
rewrite /ereal_sup /supremum; case: ifPn => [/eqP ->|].
- by rewrite lee_ninfty.
- by move=> _ SM; case: xgetP => [_ -> [_]| _] /=; [exact |rewrite lee_ninfty].
Qed.

Lemma lb_ereal_inf S M : lbound S M -> M <= ereal_inf S.
Proof.
move=> SM; rewrite /ereal_inf lee_oppr; apply ub_ereal_sup => x [y Sy <-{x}].
by rewrite lee_oppl oppeK; apply SM.
Qed.

Lemma ub_ereal_sup_adherent S (e : {posnum R}) (r : R) :
  ereal_sup S = r%:E -> exists x, S x /\ (ereal_sup S - e%:num%:E < x).
Proof.
move=> Sr.
have : ~ ubound S (ereal_sup S - e%:num%:E).
  move/ub_ereal_sup; apply/negP.
  by rewrite -ltNge Sr lte_subl_addr lte_fin ltr_addl.
move/asboolP; rewrite asbool_neg; case/existsp_asboolPn => /= x.
rewrite not_implyE => -[? ?]; exists x; split => //.
by rewrite ltNge; apply/negP.
Qed.

Lemma lb_ereal_inf_adherent S (e : {posnum R}) (r : R) :
  ereal_inf S = r%:E -> exists x, S x /\ (x < ereal_inf S + e%:num%:E).
Proof.
rewrite -(oppeK r%:E) => /eqP; rewrite eqe_opp => /eqP/ub_ereal_sup_adherent.
move=> /(_ e) [x [[y Sy yx ex]]]; exists (- x); rewrite -yx oppeK; split => //.
by rewrite -(oppeK y) yx lte_oppl oppeD /ereal_inf oppeK.
Qed.

Lemma ereal_sup_gt S x : x < ereal_sup S -> exists y, S y /\ x < y.
Proof.
rewrite not_existsP => + g; apply/negP; rewrite -leNgt.
apply: ub_ereal_sup => y Sy; move: (g y).
by rewrite not_andP => -[// | /negP]; rewrite leNgt.
Qed.

Lemma ereal_inf_lt S x : ereal_inf S < x -> exists y, S y /\ y < x.
Proof.
rewrite lte_oppl => /ereal_sup_gt [_ [[y Sy] <-]].
by rewrite lte_oppl oppeK => xlty; exists y.
Qed.

End ereal_supremum.

Section ereal_supremum_realType.
Variable R : realType.
Local Open Scope classical_set_scope.
Implicit Types S : set {ereal R}.
Implicit Types x : {ereal R}.

Let real_of_er_def r0 x : R := if x is r%:E then r else r0.
(* NB: see also real_of_er above *)

Lemma ereal_supremums_neq0 S : supremums S !=set0.
Proof.
have [/eqP ->|Snoo] := boolP (S == [set -oo]).
  by exists -oo; split; [rewrite ub_set1 |exact: lb_ub_refl].
have [/eqP ->|S0] := boolP (S == set0).
  by exists -oo; exact: ereal_supremums_set0_ninfty.
have [Spoo|Spoo] := pselect (S +oo).
  by exists +oo; split; [apply/ereal_ub_pinfty | apply/lbP => /= y /ubP; apply].
have [r Sr] : exists r, S r%:E.
  move: S0 => /set0P[] [r Sr| // |Snoo1]; first by exists r.
  apply/not_existsP => nS; move/negP : Snoo; apply.
  by apply/eqP; rewrite predeqE => -[] // r; split => // /nS.
set U := [set x | (real_of_er_def r @` S) x ].
have [/eqP|] := boolP (ubound U == set0).
  rewrite -subset0 => U0; exists +oo.
  split; [exact/ereal_ub_pinfty | apply/lbP => /= -[r0 /ubP Sr0|//|]].
  - suff : ubound U r0 by move/U0.
    by apply/ubP=> _ -[] [r1 Sr1 <-|//| /= _ <-]; rewrite -lee_fin; apply Sr0.
  - by move/ereal_ub_ninfty => [|]; by [move/eqP : S0|move/eqP : Snoo].
set u : R := sup U.
exists u%:E; split; last first.
  apply/lbP=> -[r0 /ubP Sr0| |].
  - rewrite lee_fin; apply/sup_le_ub; first by exists r, r%:E.
    by apply/ubP => _ -[[r2 ? <-| // | /= _ <-]]; rewrite -lee_fin; exact: Sr0.
  - by rewrite lee_pinfty.
  - by move/ereal_ub_ninfty=> [|/eqP //]; [move/eqP : S0|rewrite (negbTE Snoo)].
apply/ubP => -[r0 Sr0|//|_]; last by rewrite lee_ninfty.
rewrite lee_fin.
suff : has_sup U by move/sup_upper_bound/ubP; apply; exists r0%:E.
split; first by exists r0, r0%:E.
exists u; apply/ubP => y; move=> [] y' Sy' <-{y}.
have : has_sup U by split; [exists r, r%:E | exact/set0P].
move/sup_upper_bound/ubP; apply.
by case: y' Sy' => [r1 /= Sr1 | // | /= _]; [exists r1%:E | exists r%:E].
Qed.

Lemma ereal_sup_ub S : ubound S (ereal_sup S).
Proof.
move=> y Sy; rewrite /ereal_sup /supremum ifF; last first.
  by apply/eqP; rewrite predeqE => /(_ y)[+ _]; exact.
case: xgetP => /=; first by move=> _ -> -[] /ubP geS _; apply geS.
by case: (ereal_supremums_neq0 S) => /= x0 Sx0; move/(_ x0).
Qed.

Lemma ereal_sup_ninfty S : ereal_sup S = -oo <-> S `<=` [set -oo].
Proof.
split.
  by move=> supS [r /ereal_sup_ub | /ereal_sup_ub |//]; rewrite supS.
move=> /(@subset_set1 _ S) [] ->; [exact: ereal_sup0|exact: ereal_sup1].
Qed.

Lemma ereal_inf_lb S : lbound S (ereal_inf S).
Proof.
by move=> x Sx; rewrite /ereal_inf lee_oppl; apply ereal_sup_ub; exists x.
Qed.

Lemma ereal_inf_pinfty S : ereal_inf S = +oo <-> S `<=` [set +oo].
Proof. rewrite eqe_oppLRP oppe_subset image_set1; exact: ereal_sup_ninfty. Qed.

Lemma le_ereal_sup : {homo @ereal_sup R : A B / A `<=` B >-> A <= B}.
Proof. by move=> A B AB; apply ub_ereal_sup => x Ax; apply/ereal_sup_ub/AB. Qed.

Lemma le_ereal_inf : {homo @ereal_inf R : A B / A `<=` B >-> B <= A}.
Proof. by move=> A B AB; apply lb_ereal_inf => x Bx; exact/ereal_inf_lb/AB. Qed.

End ereal_supremum_realType.

Canonical ereal_pointed (R : numDomainType) := PointedType {ereal R} +oo.

Section ereal_nbhs.
Context {R : numFieldType}.
Local Open Scope ereal_scope.
Definition ereal_nbhs' (a : {ereal R}) (P : {ereal R} -> Prop) : Prop :=
  match a with
    | a%:E => nbhs' a (fun x => P x%:E)
    | +oo => exists M, M \is Num.real /\ forall x, M%:E < x -> P x
    | -oo => exists M, M \is Num.real /\ forall x, x < M%:E -> P x
  end.
Definition ereal_nbhs (a : {ereal R}) (P : {ereal R} -> Prop) : Prop :=
  match a with
    | a%:E => nbhs a (fun x => P x%:E)
    | +oo => exists M, M \is Num.real /\ forall x, M%:E < x -> P x
    | -oo => exists M, M \is Num.real /\ forall x, x < M%:E -> P x
  end.
Canonical ereal_ereal_filter := FilteredType {ereal R} {ereal R} (ereal_nbhs).
End ereal_nbhs.

Lemma ereal_nbhs_pinfty_ge (R : numFieldType) (c : {posnum R}) :
  \forall x \near +oo, (c%:num%:E <= x).
Proof. by exists c%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

Lemma ereal_nbhs_ninfty_le (R : numFieldType) (c : R) : (c < 0)%R ->
  \forall x \near -oo, (x <= c%:E).
Proof. by exists c; rewrite realE (ltW H) orbT; split => // x /ltW. Qed.

Section ereal_nbhs_instances.
Context {R : numFieldType}.


Global Instance ereal_nbhs'_filter :
  forall x : {ereal R}, ProperFilter (ereal_nbhs' x).
Proof.
case=> [x||].
- case: (Proper_nbhs'_numFieldType x) => x0 [//= xT xI xS].
  apply Build_ProperFilter' => //=; apply Build_Filter => //=.
  move=> P Q lP lQ; exact: xI.
  by move=> P Q PQ /xS; apply => y /PQ.
- apply Build_ProperFilter.
    move=> P [x [xr xP]] //; exists (x + 1)%R%:E; apply xP => /=.
    by rewrite lte_fin ltr_addl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|%R; rewrite realE normr_ge0; split => // x Hx; split.
        by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0 lee_fin.
      by apply gtMQ; rewrite (le_lt_trans _ Hx) // lee_fin real_ler_normr // lexx.
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists `|MP|%R; rewrite realE normr_ge0; split => // x MPx; split.
      by apply gtMP; rewrite (le_lt_trans _ MPx) // lee_fin real_ler_normr // lexx.
      by apply gtMQ; rewrite (le_lt_trans _ MPx) // lee_fin MQ0.
    have {}MP0 : (0 < `|MP|)%R by rewrite normr_gt0.
    have {}MQ0 : (0 < `|MQ|)%R by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= posnum_ge0 /=; split => //.
    case=> [r| |//].
    * rewrite lte_fin/= posnum_max pos_lt_maxl /= => /andP[MPx MQx]; split.
      by apply/gtMP; rewrite lte_fin (le_lt_trans _ MPx) // real_ler_normr // lexx.
      by apply/gtMQ; rewrite lte_fin (le_lt_trans _ MQx) // real_ler_normr // lexx.
    * by move=> _; split; [apply/gtMP | apply/gtMQ].
  + by exists M; split => // ? /gtM /sPQ.
- apply Build_ProperFilter.
  + move=> P [M [Mr ltMP]]; exists (M - 1)%R%:E.
    by apply: ltMP; rewrite lte_fin gtr_addl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0; rewrite real0.
    * have [/eqP MP0|MP0] := boolP (MP == 0).
        have [/eqP MQ0|MQ0] := boolP (MQ == 0).
          by exists 0; rewrite real0; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|)%R; rewrite realN realE normr_ge0; split => // x xMQ; split.
          by apply ltMP; rewrite (lt_le_trans xMQ) // lee_fin MP0 ler_oppl oppr0.
       apply ltMQ; rewrite (lt_le_trans xMQ) // lee_fin ler_oppl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        exists (- `|MP|)%R; rewrite realN realE normr_ge0; split => // x MPx; split.
          apply ltMP; rewrite (lt_le_trans MPx) // lee_fin ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        by apply ltMQ; rewrite (lt_le_trans MPx) // lee_fin MQ0 ler_oppl oppr0.
      have {}MP0 : (0 < `|MP|)%R by rewrite normr_gt0.
      have {}MQ0 : (0 < `|MQ|)%R by rewrite normr_gt0.
      exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num)%R.
      rewrite realN realE /= posnum_ge0 /=; split => //.
      case=> [r|//|].
      - rewrite lte_fin ltr_oppr posnum_max pos_lt_maxl => /andP[].
        rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
          apply/ltMP; rewrite lte_fin (lt_le_trans MPx) //= ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        apply/ltMQ; rewrite lte_fin (lt_le_trans MQx) //= ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      - by move=> _; split; [apply/ltMP | apply/ltMQ].
    * by exists M; split => // x /ltM /sPQ.
Qed.
Typeclasses Opaque ereal_nbhs'.

Global Instance ereal_nbhs_filter : forall x, ProperFilter (@ereal_nbhs R x).
Proof.
case=> [x| |].
- case: (ereal_nbhs'_filter x%:E) => x0 [//=nxT xI xS].
  apply Build_ProperFilter => //=.
  move=> P /nbhs_ballP[r r0 xr]; exists x%:E; apply xr => //=.
  by rewrite /ball /= subrr normr0.
  apply Build_Filter => //=.
  by rewrite nbhsE'.
  move=> P Q.
  rewrite !nbhsE' => -[xP axP] [xQ axQ]; split => //=.
  exact: xI.
  move=> P Q PQ; rewrite !nbhsE' => -[xP axP]; split => //=.
  apply (xS P) => //=.
  exact: PQ.
exact: (ereal_nbhs'_filter +oo).
exact: (ereal_nbhs'_filter -oo).
Qed.
Typeclasses Opaque ereal_nbhs.

End ereal_nbhs_instances.

Section ereal_topologicalType.
Variable R : realFieldType.

Lemma ereal_nbhs_singleton (p : {ereal R}) (A : set {ereal R}) :
  ereal_nbhs p A -> A p.
Proof.
move: p => -[p | [M [Mreal MA]] | [M [Mreal MA]]] /=; [|exact: MA | exact: MA].
move=> /nbhs_ballP[_/posnumP[e]]; apply; exact/ballxx.
Qed.

Lemma ereal_nbhs_nbhs (p : {ereal R}) (A : set {ereal R}) :
  ereal_nbhs p A -> ereal_nbhs p (ereal_nbhs^~ A).
Proof.
move: p => -[p| [M [Mreal MA]] | [M [Mreal MA]]] //=.
- move=> /nbhs_ballP[_/posnumP[e]] ballA.
  apply/nbhs_ballP; exists (e%:num / 2) => //= r per.
  apply/nbhs_ballP; exists (e%:num / 2) => //= x rex.
  apply/ballA/(@ball_splitl _ _ r) => //; exact/ball_sym.
- exists (M + 1)%R; split; first by rewrite realD // real1.
  move=> -[x| _ |] //=.
    rewrite lte_fin => M'x /=.
    apply/nbhs_ballP; exists 1 => //= y x1y.
    apply MA; rewrite lte_fin.
    rewrite addrC -ltr_subr_addl in M'x.
    rewrite (lt_le_trans M'x) // ler_subl_addl addrC -ler_subl_addl.
    rewrite (le_trans _ (ltW x1y)) // real_ler_norm // realB //.
      rewrite ltr_subr_addr in M'x.
      rewrite -comparabler0 (@comparabler_trans _ (M + 1)%R) //.
        by rewrite /Order.comparable (ltW M'x) orbT.
      by rewrite comparabler0 realD // real1.
    by rewrite num_real. (* where we really use realFieldType *)
  by exists M.
- exists (M - 1)%R; split; first by rewrite realB // real1.
  move=> -[x| _ |] //=.
    rewrite lte_fin => M'x /=.
    apply/nbhs_ballP; exists 1 => //= y x1y.
    apply MA; rewrite lte_fin.
    rewrite ltr_subr_addl in M'x.
    rewrite (le_lt_trans _ M'x) // addrC -ler_subl_addl.
    rewrite (le_trans _ (ltW x1y)) // distrC real_ler_norm // realB //.
      by rewrite num_real. (* where we really use realFieldType *)
    rewrite addrC -ltr_subr_addr in M'x.
    rewrite -comparabler0 (@comparabler_trans _ (M - 1)%R) //.
      by rewrite /Order.comparable (ltW M'x).
    by rewrite comparabler0 realB // real1.
  by exists M.
Qed.

Definition ereal_topologicalMixin : Topological.mixin_of (@ereal_nbhs R) :=
  topologyOfFilterMixin _ ereal_nbhs_singleton ereal_nbhs_nbhs.
Canonical ereal_topologicalType := TopologicalType _ ereal_topologicalMixin.

End ereal_topologicalType.

Local Open Scope classical_set_scope.

Lemma nbhsNe (R : realFieldType) (x : {ereal R}) :
  nbhs (- x) = [set (-%E @` A) | A in nbhs x].
Proof.
case: x => [r /=| |].
- rewrite /nbhs /= /ereal_nbhs -nbhs_ballE.
  rewrite predeqE => S; split => [[_/posnumP[e] reS]|[S' [_ /posnumP[e] reS' <-]]].
    exists (-%E @` S).
      exists e%:num => // x rex; exists (- x%:E); last by rewrite oppeK.
      by apply reS; rewrite /ball /= opprK -normrN opprD opprK.
    rewrite predeqE => s; split => [[y [z Sz] <- <-]|Ss].
      by rewrite oppeK.
    by exists (- s); [exists s | rewrite oppeK].
  exists e%:num => // x rex; exists (- x%:E); last by rewrite oppeK.
  by apply reS'; rewrite /ball /= opprK -normrN opprD.
- rewrite predeqE => S; split=> [[M [Mreal MS]]|[x [M [Mreal Mx]] <-]].
    exists (-%E @` S).
      exists (- M)%R; rewrite realN Mreal; split => // x Mx.
      by exists (- x); [apply MS; rewrite lte_oppl | rewrite oppeK].
    rewrite predeqE => x; split=> [[y [z Sz <- <-]]|Sx]; first by rewrite oppeK.
    by exists (- x); [exists x | rewrite oppeK].
  exists (- M)%R; rewrite realN; split => // y yM.
  exists (- y); by [apply Mx; rewrite lte_oppr|rewrite oppeK].
- rewrite predeqE => S; split=> [[M [Mreal MS]]|[x [M [Mreal Mx]] <-]].
    exists (-%E @` S).
      exists (- M)%R; rewrite realN Mreal; split => // x Mx.
      by exists (- x); [apply MS; rewrite lte_oppr | rewrite oppeK].
    rewrite predeqE => x; split=> [[y [z Sz <- <-]]|Sx]; first by rewrite oppeK.
    by exists (- x); [exists x | rewrite oppeK].
  exists (- M)%R; rewrite realN; split => // y yM.
  exists (- y); by [apply Mx; rewrite lte_oppl|rewrite oppeK].
Qed.

Lemma nbhsNKe (R : realFieldType) (z : {ereal R}) (A : set {ereal R}) :
  nbhs (- z) (-%E @` A) -> nbhs z A.
Proof.
rewrite nbhsNe => -[S zS] SA; rewrite -(oppeK z) nbhsNe.
exists (-%E @` S); first by rewrite nbhsNe; exists S.
rewrite predeqE => x; split => [[y [u Su <-{y} <-]]|Ax].
  rewrite oppeK.
  move: SA; rewrite predeqE => /(_ (- u)) [h _].
  have : (exists2 y, S y & - y = - u) by exists u.
  by move/h => -[y Ay] /eqP; rewrite eqe_opp => /eqP <-.
exists (- x); last by rewrite oppeK.
exists x => //.
move: SA; rewrite predeqE => /(_ (- x)) [_ h].
have : (-%E @` A) (- x) by exists x.
by move/h => [y Sy] /eqP; rewrite eqe_opp => /eqP <-.
Qed.

Lemma oppe_continuous (R : realFieldType) : continuous (@oppe R).
Proof.
move=> x S /= xS; apply nbhsNKe; rewrite image_preimage //.
by rewrite predeqE => y; split => // _; exists (- y) => //; rewrite oppeK.
Qed.

Section contract_expand.
Variable R : realFieldType.
Local Open Scope ereal_scope.

Definition contract (x : {ereal R}) : R :=
  match x with
  | r%:E => r / (1 + `|r|) | +oo => 1 | -oo => -1
  end.

Lemma contract_lt1 x : (`|contract x%:E| < 1)%R.
Proof.
rewrite normrM normrV ?unitfE //; last by rewrite eq_sym lt_eqF // ltr_spaddl.
rewrite ltr_pdivr_mulr // ?mul1r; last by rewrite gtr0_norm ltr_spaddl.
by rewrite [X in (_ < X)%R]gtr0_norm ?ltr_addr// ltr_spaddl.
Qed.

Lemma contract_le1 x : (`|contract x| <= 1)%R.
Proof.
by case: x => [x| |] /=; rewrite ?normrN1 ?normr1 // (ltW (contract_lt1 _)).
Qed.

Lemma contract0 : contract 0%:E = 0.
Proof. by rewrite /contract mul0r. Qed.

Lemma contractN x : contract (- x) = (- contract x)%R.
Proof. by case: x => //= [r|]; [ rewrite normrN mulNr | rewrite opprK]. Qed.

Lemma contract_imageN (S : set {ereal R}) :
  contract @` (-%E @` S) = -%R @` (contract @` S).
Proof.
rewrite predeqE => r; split => [[y [z Sz <-{y} <-{r}]]|[s [y Sy <-{s} <-{r}]]].
by exists (contract z); [exists z | rewrite contractN].
by exists (- y); [exists y | rewrite contractN].
Qed.

(* TODO: not exploited yet: expand is nondecreasing everywhere so it should be
   possible to use some of the homoRL/homoLR lemma where monoRL/monoLR do not
   apply *)
Definition expand r : {ereal R} :=
  if (r >= 1)%R then +oo else if (r <= -1)%R then -oo else (r / (1 - `|r|))%:E.

Lemma expand1 x : (1 <= x)%R -> expand x = +oo.
Proof. by move=> x1; rewrite /expand x1. Qed.

Lemma expandN r : expand (- r)%R = - expand r.
Proof.
rewrite /expand; case: ifPn => [r1|].
  rewrite ifF; [by rewrite ifT // -ler_oppr|apply/negbTE].
  by rewrite -ltNge -(opprK r) -ltr_oppl (lt_le_trans _ r1) // -subr_gt0 opprK.
rewrite -ltNge => r1; case: ifPn; rewrite ler_oppl opprK; [by move=> ->|].
by rewrite -ltNge leNgt => ->; rewrite leNgt -ltr_oppl r1 /= mulNr normrN.
Qed.

Lemma expandN1 x : (x <= -1)%R -> expand x = -oo.
Proof.
by rewrite ler_oppr => /expand1/eqP; rewrite expandN eqe_oppLR => /eqP.
Qed.

Lemma expand0 : expand 0 = 0%:E.
Proof. by rewrite /expand leNgt ltr01 /= oppr_ge0 leNgt ltr01 /= mul0r. Qed.

Lemma expandK : {in [pred x | `|x| <= 1]%R, cancel expand contract}.
Proof.
move=> x; rewrite inE le_eqVlt => /orP[|x1].
  rewrite eqr_norml => /andP[/orP[]/eqP->{x}] _;
    by [rewrite expand1|rewrite expandN1].
rewrite /expand 2!leNgt ltr_oppl; case/ltr_normlP : (x1) => -> -> /=.
have x_pneq0 : (1 + x / (1 - x) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 - x)%R) -?mulrDl; last first.
    by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
  by rewrite subrK mulf_neq0 // invr_eq0 subr_eq0 eq_sym lt_eqF // ltr_normlW.
have x_nneq0 : (1 - x / (1 + x) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 + x)%R) -?mulrBl; last first.
    by rewrite unitfE addrC addr_eq0 gt_eqF // ltrNnormlW.
  rewrite addrK mulf_neq0 // invr_eq0 addr_eq0 -eqr_oppLR eq_sym gt_eqF //.
  exact: ltrNnormlW.
wlog : x x1 x_pneq0 x_nneq0 / (0 <= x)%R => wlog_x0.
  have [x0|x0] := lerP 0 x; first by rewrite wlog_x0.
  move: (wlog_x0 (- x)%R).
  rewrite !(normrN,opprK,mulNr) oppr_ge0 => /(_ x1 x_nneq0 x_pneq0 (ltW x0)).
  by move/eqP; rewrite eqr_opp => /eqP.
rewrite /contract !ger0_norm //; last first.
  by rewrite divr_ge0 // subr_ge0 (le_trans _ (ltW x1)) // ler_norm.
apply: (@mulIr _ (1 + x / (1 - x))%R); first by rewrite unitfE.
rewrite -(mulrA (x / _)) mulVr ?unitfE // mulr1.
rewrite -[X in (X + _ / _)%R](@divrr _ (1 - x)%R) -?mulrDl ?subrK ?div1r //.
by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
Qed.

Lemma le_contract : {mono contract : x y / (x <= y)%O}.
Proof.
apply: le_mono; move=> -[r0 | | ] [r1 | _ | _] //=.
- rewrite lte_fin => r0r1; rewrite ltr_pdivr_mulr ?ltr_paddr//.
  rewrite mulrAC ltr_pdivl_mulr ?ltr_paddr// 2?mulrDr 2?mulr1.
  have [r10|?] := ler0P r1; last first.
    rewrite ltr_le_add // mulrC; have [r00|//] := ler0P r0.
    by rewrite (@le_trans _ _ 0) // ?pmulr_lle0 // mulr_ge0 // ?oppr_ge0 // ltW.
  have [?|r00] := ler0P r0; first by rewrite ltr_le_add // 2!mulrN mulrC.
  by move: (le_lt_trans r10 (lt_trans r00 r0r1)); rewrite ltxx.
- by rewrite ltr_pdivr_mulr ?ltr_paddr// mul1r ltr_spaddl // ler_norm.
- rewrite ltr_pdivl_mulr ?mulN1r ?ltr_paddr// => _.
  by rewrite ltr_oppl ltr_spaddl // ler_normr lexx orbT.
- by rewrite -subr_gt0 opprK.
Qed.

Definition lt_contract := leW_mono le_contract.
Definition contract_inj := mono_inj lexx le_anti le_contract.

Lemma le_expand_in : {in [pred x | `|x| <= 1]%R &,
  {mono expand : x y / (x <= y)%O}}.
Proof. exact: can_mono_in (onW_can_in predT expandK) _ (in2W le_contract). Qed.

Definition lt_expand := leW_mono_in le_expand_in.
Definition expand_inj := mono_inj_in lexx le_anti le_expand_in.

Lemma real_of_er_expand x : (`|x| < 1)%R -> (real_of_er (expand x))%:E = expand x.
Proof.
by move=> x1; rewrite /expand 2!leNgt ltr_oppl; case/ltr_normlP : x1 => -> ->.
Qed.

Lemma contractK : cancel contract expand.
Proof.
apply: (onS_can [pred x | `|x| <= 1]%R contract_le1).
exact: inj_can_sym_on expandK (in1W contract_inj).
Qed.

Lemma bijective_contract : {on [pred x| `|x| <= 1]%R, bijective contract}.
Proof. exists expand; [exact: in1W contractK | exact: expandK]. Qed.

Definition le_expandLR := monoLR_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) le_expand_in.
Definition lt_expandLR := monoLR_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) lt_expand.
Definition le_expandRL := monoRL_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) le_expand_in.
Definition lt_expandRL := monoRL_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) lt_expand.

Lemma le_expand : {homo expand : x y / (x <= y)%O}.
Proof.
move=> x y xy; have [x1|] := lerP `|x| 1.
  have [y_le1|/ltW /expand1->] := leP y 1; last by rewrite lee_pinfty.
  rewrite le_expand_in ?inE// ler_norml y_le1 (le_trans _ xy)//.
  by rewrite ler_oppl (ler_normlP _ _ _).
rewrite ltr_normr => /orP[|] x1; last first.
  by rewrite expandN1 // ?lee_ninfty // ler_oppr ltW.
by rewrite expand1; [rewrite expand1 // (le_trans _ xy) // ltW | exact: ltW].
Qed.

Lemma contract_eq0 x : (contract x == 0) = (x == 0%:E).
Proof. by rewrite -(can_eq contractK) contract0. Qed.

Lemma contract_eqN1 x : (contract x == -1) = (x == -oo).
Proof. by rewrite -(can_eq contractK). Qed.

Lemma contract_eq1 x : (contract x == 1) = (x == +oo).
Proof. by rewrite -(can_eq contractK). Qed.

Lemma expand_eqoo (r : R) : (expand r == +oo) = (1 <= r)%R.
Proof. by rewrite /expand; case: ifP => //; case: ifP. Qed.

Lemma expand_eqNoo (r : R) : (expand r == -oo) = (r <= -1)%R.
Proof.
rewrite /expand; case: ifP => /= r1; last by case: ifP.
by apply/esym/negbTE; rewrite -ltNge (lt_le_trans _ r1) // -subr_gt0 opprK.
Qed.

End contract_expand.

Section contract_expand_realType.
Variable R : realType.

Let contract := @contract R.

Lemma sup_contract_le1 S : S !=set0 -> (`|sup (contract @` S)| <= 1)%R.
Proof.
case=> x Sx; rewrite ler_norml; apply/andP; split; last first.
  apply sup_le_ub; first by exists (contract x), x.
  by move=> r [y Sy] <-; case/ler_normlP : (contract_le1 y).
rewrite (@le_trans _ _ (contract x)) //.
  by case/ler_normlP : (contract_le1 x); rewrite ler_oppl.
apply sup_ub; last by exists x.
by exists 1 => r [y Sy <-]; case/ler_normlP : (contract_le1 y).
Qed.

Lemma contract_sup S : S !=set0 -> contract (ereal_sup S) = sup (contract @` S).
Proof.
move=> S0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply sup_le_ub.
    by case: S0 => x Sx; exists (contract x), x.
  move=> x [y Sy] <-{x}; rewrite le_contract; exact/ereal_sup_ub.
rewrite leNgt; apply/negP.
set supc := sup _; set csup := contract _; move=> ltsup.
suff [y [ysupS ?]] : exists y, y < ereal_sup S /\ ubound S y.
  have : ereal_sup S <= y by apply ub_ereal_sup.
  by move/(lt_le_trans ysupS); rewrite ltxx.
suff [x [? [ubSx x1]]] : exists x, (x < csup)%R /\ ubound (contract @` S) x /\
    (`|x| <= 1)%R.
  exists (expand x); split => [|y Sy].
    by rewrite -(contractK (ereal_sup S)) lt_expand // inE // contract_le1.
  by rewrite -(contractK y) le_expand //; apply ubSx; exists y.
exists ((supc + csup) / 2); split; first by rewrite midf_lt.
split => [r [y Sy <-{r}]|].
  rewrite (@le_trans _ _ supc) ?midf_le //; last by rewrite ltW.
  apply sup_ub; last by exists y.
  by exists 1 => r [z Sz <-]; case/ler_normlP : (contract_le1 z).
rewrite ler_norml; apply/andP; split; last first.
  rewrite ler_pdivr_mulr // mul1r (_ : 2 = 1 + 1)%R // ler_add //.
  by case/ler_normlP : (sup_contract_le1 S0).
  by case/ler_normlP : (contract_le1 (ereal_sup S)).
rewrite ler_pdivl_mulr // (_ : 2 = 1 + 1)%R // mulN1r opprD ler_add //.
by case/ler_normlP : (sup_contract_le1 S0); rewrite ler_oppl.
by case/ler_normlP : (contract_le1 (ereal_sup S)); rewrite ler_oppl.
Qed.

Lemma contract_inf S : S !=set0 -> contract (ereal_inf S) = inf (contract @` S).
Proof.
move=> -[x Sx]; rewrite /ereal_inf /contract (contractN (ereal_sup (-%E @` S))).
by rewrite -/contract contract_sup /inf; [rewrite contract_imageN | exists (- x), x].
Qed.

End contract_expand_realType.

Section ereal_PseudoMetric.
Variable R : realFieldType.
Implicit Types x y : {ereal R}.

Definition ereal_ball x (e : R) y := (`|contract x - contract y| < e)%R.

Lemma ereal_ball_center x (e : R) : (0 < e)%R -> ereal_ball x e x.
Proof. by move=> e0; rewrite /ereal_ball subrr normr0. Qed.

Lemma ereal_ball_sym x y (e : R) : ereal_ball x e y -> ereal_ball y e x.
Proof. by rewrite /ereal_ball distrC. Qed.

Lemma ereal_ball_triangle x y z (e1 e2 : R) :
  ereal_ball x e1 y -> ereal_ball y e2 z -> ereal_ball x (e1 + e2) z.
Proof.
rewrite /ereal_ball => h1 h2; rewrite -[X in (X - _)%R](subrK (contract y)) -addrA.
by rewrite (le_lt_trans (ler_norm_add _ _)) // ltr_add.
Qed.

Lemma ereal_ballN (x y : er R) (e : {posnum R}) :
  ereal_ball (- x) e%:num (- y) -> ereal_ball x e%:num y.
Proof. by rewrite /ereal_ball 2!contractN opprK -opprB normrN addrC. Qed.

Lemma le_ereal_ball (x : er R) :
  {homo ereal_ball x : e e' / (e <= e')%R >-> e `<=` e'}.
Proof. by move=> e e' ee' y; rewrite /ereal_ball => /lt_le_trans; exact. Qed.

Lemma ereal_ball_ninfty_oversize (e : {posnum R}) x :
  (2 < e%:num)%R -> ereal_ball -oo e%:num x.
Proof.
move=> e2; rewrite /ereal_ball /= (le_lt_trans _ e2) // -opprB normrN opprK.
rewrite (le_trans (ler_norm_add _ _)) // normr1 -ler_subr_addr.
by rewrite (le_trans (contract_le1 _)) // (_ : 2 = 1 + 1)%R // addrK.
Qed.

Lemma contract_ereal_ball_pinfty (r : R) (e : {posnum R}) :
  (1 < contract r%:E + e%:num)%R -> ereal_ball r%:E e%:num +oo.
Proof.
move=> re1; rewrite /ereal_ball; rewrite [contract +oo]/= ler0_norm; last first.
  by rewrite subr_le0; case/ler_normlP: (contract_le1 r%:E).
by rewrite opprB ltr_subl_addl.
Qed.

Lemma expand_ereal_ball_pinfty {e : {posnum R}} r : (e%:num <= 1)%R ->
  expand (1 - e%:num)%R < r%:E -> ereal_ball +oo e%:num r%:E.
Proof.
move=> e1 er; rewrite /ereal_ball gtr0_norm ?subr_gt0; last first.
  by case/ltr_normlP : (contract_lt1 r).
rewrite ltr_subl_addl addrC -ltr_subl_addl -[X in (X < _)%R]expandK ?lt_contract//.
by rewrite inE ger0_norm ?ler_subl_addl ?ler_addr // subr_ge0.
Qed.

Lemma contract_ereal_ball_fin_le (r r' : R) (e : {posnum R}) : (r <= r')%R ->
  (1 <= contract r%:E + e%:num)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
rewrite le_eqVlt => /orP[/eqP <-{r'} _|rr' re1]; first exact: ereal_ball_center.
rewrite /ereal_ball ltr0_norm; last by rewrite subr_lt0 lt_contract lte_fin.
rewrite opprB ltr_subl_addl (lt_le_trans _ re1) //.
by case/ltr_normlP : (contract_lt1 r').
Qed.

Lemma contract_ereal_ball_fin_lt (r r' : R) (e : {posnum R}) : (r' < r)%R ->
  (contract r%:E - e%:num <= -1)%R  -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r reN1; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
rewrite ltr_subl_addl addrC -ltr_subl_addl (le_lt_trans reN1) //.
by move: (contract_lt1 r'); rewrite ltr_norml => /andP[].
Qed.

Lemma expand_ereal_ball_fin_lt (r' r : R) (e : {posnum R}) : (r' < r)%R ->
  expand (contract r%:E - e%:num)%R < r'%:E ->
  (`|contract r%:E - e%:num| < 1)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r ? r'e'r.
rewrite /ereal_ball gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
by rewrite ltr_subl_addl addrC -ltr_subl_addl -lt_expandLR ?inE ?ltW.
Qed.

Lemma ball_ereal_ball_fin_lt (r r' : R) (e : {posnum R}) :
  let e' := (r - real_of_er (expand (contract r%:E - e%:num)))%R in
  ball r e' r' -> (r' < r)%R ->
  (`|contract r%:E - (e)%:num| < 1)%R ->
  ereal_ball r%:E (e)%:num r'%:E.
Proof.
move=> e' re'r' rr' X; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0// ?lt_contract ?lte_fin//.
move: re'r'.
rewrite /ball /= gtr0_norm // ?subr_gt0// /e'.
rewrite -ltr_subl_addl addrAC subrr add0r ltr_oppl opprK -lte_fin.
rewrite real_of_er_expand // lt_expandLR ?inE ?ltW//.
by rewrite ltr_subl_addl addrC -ltr_subl_addl.
Qed.

Lemma ball_ereal_ball_fin_le (r r' : R) (e : {posnum R} ) :
  let e' : R := (real_of_er (expand (contract r%:E + e%:num)) - r)%R in
  ball r e' r' -> (r <= r')%R ->
  (`| contract r%:E + e%:num | < 1)%R ->
  (ereal_ball r%:E e%:num r'%:E).
Proof.
move=> e' r'e'r rr' re1; rewrite /ereal_ball.
move: rr'; rewrite le_eqVlt => /orP[/eqP->|rr'].
  by rewrite subrr normr0.
rewrite /ball /= ltr0_norm ?subr_lt0// opprB in r'e'r.
rewrite ltr0_norm ?subr_lt0 ?lt_contract ?lte_fin//.
rewrite opprB; move: r'e'r.
rewrite /e' -ltr_subl_addr opprK subrK -lte_fin real_of_er_expand //.
by rewrite lt_expandRL ?inE ?ltW// ltr_subl_addl.
Qed.

Lemma nbhs_oo_up_e1 (A : set {ereal R}) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 ooeA.
exists (real_of_er (expand (1 - e%:num)%R)); rewrite num_real; split => //.
case => [r | | //].
- rewrite real_of_er_expand; last first.
    by rewrite ger0_norm ?ltr_subl_addl ?ltr_addr // subr_ge0.
  by move=> ?; exact/ooeA/expand_ereal_ball_pinfty.
- by move=> _; exact/ooeA/ereal_ball_center.
Qed.

Lemma nbhs_oo_down_e1 (A : set {ereal R}) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; suff h : nbhs +oo (-%E @` A).
  rewrite (_ : -oo = - +oo) // nbhsNe; exists (-%E @` A) => //.
  rewrite predeqE => x; split=> [[y [z Az <- <-]]|Ax]; rewrite ?oppeK //.
  by exists (- x); [exists x | rewrite oppeK].
apply (@nbhs_oo_up_e1 _ e) => // x x1e; exists (- x); last by rewrite oppeK.
by apply/reA/ereal_ballN; rewrite oppeK.
Qed.

Lemma nbhs_oo_up_1e (A : set {ereal R}) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0; rewrite real0.
  rewrite predeqE => x; split => // _; apply reA.
  exact/ereal_ballN/ereal_ball_ninfty_oversize.
have /andP[e10 e11] : (0 < e%:num - 1 <= 1)%R.
  by rewrite subr_gt0 e1 /= ler_subl_addl.
apply nbhsNKe.
have : ((PosNum e10)%:num <= 1)%R by [].
move/(@nbhs_oo_down_e1 (-%E @` A) (PosNum e10)); apply.
move=> y ye; exists (- y); last by rewrite oppeK.
apply/reA/ereal_ballN; rewrite oppeK /=.
by apply: le_ereal_ball ye => /=; rewrite ler_subl_addl ler_addr.
Qed.

Lemma nbhs_oo_down_1e (A : set {ereal R}) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0; rewrite real0.
  rewrite predeqE => x; split => // _.
  exact/reA/ereal_ball_ninfty_oversize.
have /andP[e10 e11] : (0 < e%:num - 1 <= 1)%R.
  by rewrite subr_gt0 e1 /= ler_subl_addl.
apply nbhsNKe.
have : ((PosNum e10)%:num <= 1)%R by [].
move/(@nbhs_oo_up_e1 (-%E @` A) (PosNum e10)); apply.
move=> y ye; exists (- y); last by rewrite oppeK.
apply/reA/ereal_ballN; rewrite /= oppeK.
by apply: le_ereal_ball ye => /=; rewrite ler_subl_addl ler_addr.
Qed.

Lemma nbhs_fin_out_above (r : R) (e : {posnum R}) (A : set {ereal R}) :
  ereal_ball r%:E e%:num `<=` A ->
  (- 1 < contract r%:E - e%:num)%R ->
  (1 <= contract r%:E + e%:num)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have er1 : (`|contract r%:E - e%:num| < 1)%R.
  rewrite ltr_norml reN1 andTb ltr_subl_addl ltr_spaddl //.
  by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
pose e' := (r - real_of_er (expand (contract r%:E - e%:num)))%R.
have e'0 : (0 < e')%R.
  rewrite subr_gt0 -lte_fin -[in X in _ < X](contractK r%:E).
  rewrite real_of_er_expand // lt_expand ?inE ?contract_le1// ?ltW//.
  by rewrite ltr_subl_addl ltr_addr.
apply/nbhs_ballP; exists e' => // r' re'r'; apply reA.
by have [?|?] := lerP r r';
  [exact: contract_ereal_ball_fin_le | exact: ball_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_below (r : R) (e : {posnum R}) (A : set {ereal R}) :
  ereal_ball r%:E e%:num `<=` A ->
  (contract r%:E - e%:num <= - 1)%R ->
  (contract r%:E + e%:num < 1)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have ? : (`|contract r%:E + e%:num| < 1)%R.
  rewrite ltr_norml re1 andbT (@lt_le_trans _ _ (contract r%:E)) // ?ler_addl //.
  by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
pose e' : R := (real_of_er (expand (contract r%:E + e%:num)) - r)%R.
have e'0 : (0 < e')%R.
  rewrite /e'.
  rewrite subr_gt0 -lte_fin -[in X in X < _](contractK r%:E).
  by rewrite real_of_er_expand // lt_expand ?inE ?contract_le1 ?ltr_addl ?ltW.
apply/nbhs_ballP; exists e' => // r' r'e'r; apply reA.
by have [?|?] := lerP r r';
  [exact: ball_ereal_ball_fin_le | exact: contract_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_above_below (r : R) (e : {posnum R}) (A : set {ereal R}) :
  ereal_ball r%:E e%:num `<=` A ->
  (contract r%:E - e%:num < -1)%R ->
  (1 < contract r%:E + e%:num)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1; suff : A = setT by move->; apply: filterT.
rewrite predeqE => x; split => // _; apply reA.
case: x => [r'| |] //.
- have [?|?] := lerP r r'.
  + by apply: contract_ereal_ball_fin_le => //; exact/ltW.
  + by apply contract_ereal_ball_fin_lt => //; exact/ltW.
- exact/contract_ereal_ball_pinfty.
- apply/ereal_ballN/contract_ereal_ball_pinfty.
  by rewrite NERFin contractN -(opprK 1) ltr_oppl opprD opprK.
Qed.

Lemma nbhs_fin_inbound (r : R) (e : {posnum R}) (A : set {ereal R}) :
  ereal_ball r%:E e%:num `<=` A -> nbhs r%:E A.
Proof.
move=> reA.
have [|reN1] := boolP (contract r%:E - e%:num == -1)%R.
  rewrite subr_eq addrC => /eqP reN1.
  have [re1|] := boolP (contract r%:E + e%:num == 1)%R.
    move/eqP : reN1; rewrite -(eqP re1) opprD addrCA subrr addr0 -subr_eq0.
    rewrite opprK -mulr2n mulrn_eq0 orFb contract_eq0 => /eqP[r0].
    move: re1; rewrite r0 contract0 add0r => /eqP e1.
    apply/nbhs_ballP; exists 1 => // r' /=; rewrite /ball /= sub0r normrN => r'1.
    apply reA.
    by rewrite /ereal_ball r0 contract0 sub0r normrN e1 contract_lt1.
  rewrite neq_lt => /orP[re1|re1].
    by apply (@nbhs_fin_out_below _ e) => //; rewrite reN1 addrAC subrr sub0r.
  have e1 : (1 < e%:num)%R.
    move: re1; rewrite reN1 addrAC ltr_subr_addl -!mulr2n -(mulr_natl e%:num).
    by rewrite -{1}(mulr1 2) => ?; rewrite -(@ltr_pmul2l _ 2).
  have Aoo : setT `\ -oo `<=` A.
    move=> x [_]; rewrite /set1 /= => xnoo; apply reA.
    case: x xnoo => [r' _ | _ |//].
      have [rr'|r'r] := lerP (contract r%:E) (contract r'%:E).
        apply: contract_ereal_ball_fin_le; last exact/ltW.
        by rewrite -lee_fin -(contractK r%:E) -(contractK r'%:E) le_expand.
      apply: contract_ereal_ball_fin_lt; last first.
        by rewrite reN1 addrAC subrr add0r.
      rewrite -lte_fin -(contractK r%:E) -(contractK r'%:E).
      by rewrite lt_expand // inE; exact: contract_le1.
    exact: contract_ereal_ball_pinfty.
  have : nbhs r%:E (setT `\ -oo) by apply/nbhs_ballP; exists 1.
  move=> /nbhs_ballP[_/posnumP[e']] /=; rewrite /ball /= => h.
  by apply/nbhs_ballP; exists e'%:num => // y /h; apply: Aoo.
move: reN1; rewrite eq_sym neq_lt => /orP[reN1|reN1].
  have [/eqP re1|re1] := boolP (contract r%:E + e%:num == 1)%R.
    by apply (@nbhs_fin_out_above _ e) => //; rewrite re1.
  move: re1; rewrite neq_lt => /orP[re1|re1].
    have ? : (`|contract r%:E - e%:num| < 1)%R.
      rewrite ltr_norml reN1 andTb ltr_subl_addl.
      rewrite (@lt_le_trans _ _ 1) // ?ler_addr //.
      by case/ltr_normlP : (contract_lt1 r).
    have ? : (`|contract r%:E + e%:num| < 1)%R.
      rewrite ltr_norml re1 andbT -(addr0 (-1)) ler_lt_add //.
      by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
    pose e' : R := Num.min (r - real_of_er (expand (contract r%:E - e%:num)))%R
                           (real_of_er (expand (contract r%:E + e%:num)) - r)%R.
    have e'0 : (0 < e')%R.
      rewrite /e' lt_minr; apply/andP; split.
        rewrite subr_gt0 -lte_fin -[in X in _ < X](contractK r%:E).
        rewrite real_of_er_expand // lt_expand// ?inE ?contract_le1 ?ltW//.
        by rewrite ltr_subl_addl ltr_addr.
      rewrite subr_gt0 -lte_fin -[in X in X < _](contractK r%:E).
      by rewrite real_of_er_expand// lt_expand ?inE ?contract_le1 ?ltr_addl ?ltW.
    apply/nbhs_ballP; exists e' => // r' re'r'; apply reA.
    have [|r'r] := lerP r r'.
      move=> rr'; apply: ball_ereal_ball_fin_le => //.
      by apply: le_ball re'r'; rewrite le_minl lexx orbT.
    move: re'r'; rewrite /ball /= lt_minr => /andP[].
    rewrite gtr0_norm ?subr_gt0 // -ltr_subl_addl addrAC subrr add0r ltr_oppl.
    rewrite opprK -lte_fin real_of_er_expand // => r'e'r _.
    exact: expand_ereal_ball_fin_lt.
  by apply (@nbhs_fin_out_above _ e) => //; rewrite ltW.
have [re1|re1] := ltrP 1 (contract r%:E + e%:num).
  exact: (@nbhs_fin_out_above_below _ e).
move: re1; rewrite le_eqVlt => /orP[re1|re1].
  have {}re1 : contract r%:E = (1 - e%:num)%R.
    by move: re1; rewrite eq_sym -subr_eq => /eqP <-.
  have e1 : (1 < e%:num)%R.
    move: reN1.
    rewrite re1 -addrA -opprD ltr_subl_addl ltr_subr_addl -!mulr2n.
    rewrite -(mulr_natl e%:num) -{1}(mulr1 2) => ?.
    by rewrite -(@ltr_pmul2l _ 2).
  have Aoo : (setT `\ +oo `<=` A).
    move=> x [_]; rewrite /set1 /= => xpoo; apply reA.
    case: x xpoo => [r' _ | // |_].
      rewrite /ereal_ball.
      have [rr'|r'r] := lerP (contract r%:E) (contract r'%:E).
        rewrite re1 opprB addrCA -[X in (_ < X)%R]addr0 ltr_add2 subr_lt0.
        by case/ltr_normlP : (contract_lt1 r').
      rewrite /ereal_ball.
      rewrite re1 addrAC ltr_subl_addl ltr_add // (lt_trans _ e1) // ltr_oppl.
      by move: (contract_lt1 r'); rewrite ltr_norml => /andP[].
    rewrite /ereal_ball.
    rewrite [contract -oo]/= opprK gtr0_norm ?subr_gt0; last first.
      rewrite -ltr_subl_addl add0r ltr_oppl.
      by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
    by rewrite re1 addrAC ltr_subl_addl ltr_add.
   have : nbhs r%:E (setT `\ +oo) by exists 1.
   case => _/posnumP[x] /=; rewrite /ball_ => h.
   by exists x%:num => // y /h; exact: Aoo.
by apply (@nbhs_fin_out_below _ e) => //; rewrite ltW.
Qed.

Lemma ereal_nbhsE : nbhs = nbhs_ (entourage_ ereal_ball).
Proof.
set diag := fun (e : R) => [set xy | ereal_ball xy.1 e xy.2].
rewrite predeq2E => x A; split.
- rewrite {1}/nbhs /= /ereal_nbhs.
  case: x => [/= r [_/posnumP[e] reA]| [M [/= Mreal MA]]| [M [/= Mreal MA]]].
  + pose e' : R := Num.min (contract r%:E - contract (r%:E - e%:num%:E))%R
                           (contract (r%:E + e%:num%:E) - contract r%:E)%R.
    exists (diag e'); rewrite /diag.
      exists e' => //.
      rewrite /= /e' lt_minr; apply/andP; split.
        by rewrite subr_gt0 lt_contract lte_fin ltr_subl_addr ltr_addl.
      by rewrite subr_gt0 lt_contract lte_fin ltr_addl.
    case=> [r' /= re'r'| |]/=.
    * rewrite /ereal_ball in re'r'.
      have [r'r|rr'] := lerP (contract r'%:E) (contract r%:E).
        apply reA.
        rewrite /ball /= real_ltr_norml // ?num_real //.
        rewrite ger0_norm ?subr_ge0// in re'r'.
        have H1 : (contract (r%:E - e%:num%:E) < contract r'%:E)%R.
          move: re'r'; rewrite /e' lt_minr => /andP[Hr'1 Hr'2].
          rewrite /e' ltr_subr_addl addrC -ltr_subr_addl in Hr'1.
          by rewrite (lt_le_trans Hr'1) // opprB addrCA subrr addr0.
        have := H1; rewrite -lt_expandRL ?inE ?contract_le1 //.
        rewrite !contractK => rer'.
        rewrite lte_fin ltr_subl_addr addrC -ltr_subl_addr in rer'.
        rewrite rer' /= andbT (@lt_le_trans _ _ 0) //.
          by rewrite ltr_oppl oppr0.
        by rewrite subr_ge0 -lee_fin -le_contract.
      apply reA.
      rewrite /ball /= real_ltr_norml // ?num_real //.
      rewrite ltr0_norm ?subr_lt0// opprB in re'r'.
      apply/andP; split; last first.
        by rewrite (@lt_trans _ _ 0) // subr_lt0 -lte_fin -lt_contract//.
      rewrite ltr_oppl opprB.
      rewrite /e' in re'r'.
      have H2 : (contract r'%:E < contract (r%:E + e%:num%:E))%R.
        move: re'r'; rewrite lt_minr => /andP[Hr'1 Hr'2].
        by rewrite ltr_subl_addr subrK in Hr'2.
      rewrite ltr_subl_addr -lte_fin -(contractK (_ + r)%:E)%R.
      by rewrite addrC -(contractK r'%:E) // lt_expand ?inE ?contract_le1.
    * rewrite /ereal_ball [contract +oo]/=.
      rewrite lt_minr => /andP[re'1 re'2].
      have [cr0|cr0] := lerP 0 (contract r%:E).
        move: re'2; rewrite ler0_norm; last first.
          by rewrite subr_le0; case/ler_normlP : (contract_le1 r%:E).
        rewrite opprB ltr_subr_addl addrCA subrr addr0 => h.
        exfalso.
        move: h; apply/negP; rewrite -leNgt.
        by case/ler_normlP : (contract_le1 (r%:E + e%:num%:E)).
      move: re'2; rewrite ler0_norm; last first.
        by rewrite subr_le0; case/ler_normlP : (contract_le1 r%:E).
      rewrite opprB ltr_subr_addl addrCA subrr addr0 => h.
      exfalso.
      move: h; apply/negP; rewrite -leNgt.
      by case/ler_normlP : (contract_le1 (r%:E + e%:num%:E)).
    * rewrite /ereal_ball [contract -oo]/=; rewrite opprK.
      rewrite lt_minr => /andP[re'1 _].
      move: re'1.
      rewrite ger0_norm; last first.
        rewrite addrC -ler_subl_addl add0r.
        by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
      rewrite ltr_add2l => h.
      exfalso.
      move: h; apply/negP; rewrite -leNgt -ler_oppl.
      by move: (contract_le1 (r%:E - e%:num%:E)); rewrite ler_norml => /andP[].
  + exists (diag (1 - contract M%:E))%R; rewrite /diag.
      exists (1 - contract M%:E)%R => //=.
      by rewrite subr_gt0 (le_lt_trans _ (contract_lt1 M)) // ler_norm.
    case=> [r| |]/=.
    * rewrite /ereal_ball [_ +oo]/= => rM1.
      apply MA.
      rewrite lte_fin.
      rewrite ger0_norm in rM1; last first.
        by rewrite subr_ge0 // (le_trans _ (contract_le1 r%:E)) // ler_norm.
      rewrite ltr_subl_addr addrC addrCA addrC -ltr_subl_addr subrr subr_gt0 in rM1.
      by rewrite -lte_fin -lt_contract.
    * rewrite /ereal_ball /= subrr normr0 => h.
      exact: MA.
    * rewrite /ereal_ball /= opprK => h {MA}.
      exfalso.
      move: h; apply/negP.
      rewrite -leNgt [in X in (_ <= X)%R]ger0_norm // ler_subl_addr.
      rewrite -/(contract M%:E) addrC -ler_subl_addr opprD addrA subrr sub0r.
      by move: (contract_le1 M%:E); rewrite ler_norml => /andP[].
  + exists (diag (1 + contract M%:E)%R); rewrite /diag.
      exists (1 + contract M%:E)%R => //=.
      rewrite -ltr_subl_addl sub0r.
      by move: (contract_lt1 M); rewrite ltr_norml => /andP[].
    case=> [r| |].
    * rewrite /ereal_ball => /= rM1.
      apply MA.
      rewrite lte_fin.
      rewrite ler0_norm in rM1; last first.
        rewrite ler_subl_addl addr0 ltW //.
        by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
      rewrite opprB opprK -ltr_subl_addl addrK in rM1.
      by rewrite -lte_fin -lt_contract.
    * rewrite /ereal_ball /= -opprD normrN => h {MA}.
      exfalso.
      move: h; apply/negP.
      rewrite -leNgt [in X in (_ <= X)%R]ger0_norm// -ler_subl_addr addrAC.
      rewrite subrr add0r -/(contract M%:E).
      by rewrite (le_trans _ (ltW (contract_lt1 M))) // ler_norm.
    * rewrite /ereal_ball /= => _; exact: MA.
- case: x => [r [E [_/posnumP[e] reA] sEA]| [E [_/posnumP[e] reA] sEA]| [E [_/posnumP[e] reA] sEA]] //=.
  + by apply nbhs_fin_inbound with e => ? ?; exact/sEA/reA.
  + have [|] := boolP (e%:num <= 1)%R.
      by move/nbhs_oo_up_e1; apply => ? ?; exact/sEA/reA.
    by rewrite -ltNge => /nbhs_oo_up_1e; apply => ? ?; exact/sEA/reA.
  + have [|] := boolP (e%:num <= 1)%R.
      by move/nbhs_oo_down_e1; apply => ? ?; exact/sEA/reA.
    by rewrite -ltNge => /nbhs_oo_down_1e; apply => ? ?; exact/sEA/reA.
Qed.

Definition ereal_pseudoMetricType_mixin :=
  PseudoMetric.Mixin ereal_ball_center ereal_ball_sym ereal_ball_triangle
                     erefl.

Definition ereal_uniformType_mixin : @Uniform.mixin_of {ereal R} nbhs :=
  uniformityOfBallMixin ereal_nbhsE ereal_pseudoMetricType_mixin.

Canonical ereal_uniformType :=
  UniformType {ereal R} ereal_uniformType_mixin.

Canonical ereal_pseudoMetricType :=
  PseudoMetricType {ereal R} ereal_pseudoMetricType_mixin.

End ereal_PseudoMetric.

(* TODO: generalize to numFieldType? *)
Lemma lt_ereal_nbhs (R : realFieldType) (a b : {ereal R}) (x : R) :
  a < x%:E -> x%:E < b ->
  exists delta : {posnum R},
    forall y, (`|y - x| < delta%:num)%R -> (a < y%:E) && (y%:E < b).
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog. (*BUG*)
  move=> {}a {}b ltxa ltxb.
  have m_gt0 : (Num.min ((x - a) / 2) ((b - x) / 2) > 0)%R.
    by rewrite lt_minr !divr_gt0 // ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite lt_minr !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite 2!lte_fin (lt_trans _ ay) ?(lt_trans yb) //=.
    by rewrite -subr_gt0 opprD addrA {1}[(b - x)%R]splitr addrK divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[(x - a)%R]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (x + 1)%R; rewrite ?lte_fin ?ltr_addl //.
  by exists d => y /dP /andP[->] /= /lt_le_trans; apply; rewrite lee_pinfty.
- have [//||d dP] := wlog (x - 1)%R b; rewrite ?lte_fin ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->] /=; rewrite lte_ninfty.
- by exists 1%:pos => ? ?; rewrite lte_ninfty lte_pinfty.
Qed.

(* TODO: generalize to numFieldType? *)
Lemma nbhs_interval (R : realFieldType) (P : R -> Prop) (x : R) (a b : {ereal R}) :
  a < x%:E -> x%:E < b ->
  (forall y, a < y%:E -> y%:E < b -> P y) ->
  nbhs x P.
Proof.
move => Hax Hxb Hp; case: (lt_ereal_nbhs Hax Hxb) => d Hd.
exists d%:num => //= y; rewrite /= distrC.
by move=> /Hd /andP[??]; apply: Hp.
Qed.

Lemma ereal_nbhs'_le (R : numFieldType) (x : {ereal R}) :
  ereal_nbhs' x --> ereal_nbhs x.
Proof.
move: x => [x P [_/posnumP[e] HP] |x P|x P] //=.
by exists e%:num => // ???; apply: HP.
Qed.

Lemma ereal_nbhs'_le_finite (R : numFieldType) (x : R) :
  ereal_nbhs' x%:E --> nbhs x%:E.
Proof.
by move=> P [_/posnumP[e] HP] //=; exists e%:num => // ???; apply: HP.
Qed.

Definition ereal_loc_seq (R : numDomainType) (x : {ereal R}) (n : nat) :=
  match x with
    | x%:E => (x + (n%:R + 1)^-1)%R%:E
    | +oo => n%:R%:E
    | -oo => - n%:R%:E
  end.

Lemma cvg_ereal_loc_seq (R : realType) (x : {ereal R}) :
  ereal_loc_seq x --> ereal_nbhs' x.
Proof.
move=> P; rewrite /ereal_loc_seq.
case: x => /= [x [_/posnumP[d] Hp] |[d [dreal Hp]] |[d [dreal Hp]]]; last 2 first.
    have /ZnatP [N Nfloor] : floor (Num.max d 0) \is a Znat.
      by rewrite Znat_def floor_ge0 le_maxr lexx orbC.
    exists N.+1 => // n ltNn; apply: Hp.
    have /le_lt_trans : (d <= Num.max d 0)%R by rewrite le_maxr lexx.
    apply; apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor.
    by rewrite -(@natrD R N 1) ler_nat addn1.
  have /ZnatP [N Nfloor] : floor (Num.max (- d)%R 0) \is a Znat.
    by rewrite Znat_def floor_ge0 le_maxr lexx orbC.
  exists N.+1 => // n ltNn; apply: Hp; rewrite lte_fin ltr_oppl.
  have /le_lt_trans : (- d <= Num.max (- d) 0)%R by rewrite le_maxr lexx.
  apply; apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor.
  by rewrite -(@natrD R N 1) ler_nat addn1.
have /ZnatP [N Nfloor] : floor (d%:num^-1) \is a Znat.
  by rewrite Znat_def floor_ge0.
exists N => // n leNn; have gt0Sn : (0 < n%:R + 1 :> R)%R.
  apply: ltr_spaddr => //; exact/ler0n.
apply: Hp; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym; apply/invr_neq0/lt0r_neq0.
rewrite /= opprD addrA subrr distrC subr0.
rewrite gtr0_norm; last by rewrite invr_gt0.
rewrite -[X in (X < _)%R]mulr1 ltr_pdivr_mull // -ltr_pdivr_mulr // div1r.
apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor ler_add //.
by rewrite ler_nat.
Qed.
