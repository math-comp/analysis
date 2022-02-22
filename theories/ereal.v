(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import boolp mathcomp_extra classical_sets functions reals posnum.
Require Import topology.

(******************************************************************************)
(*                        Extended real numbers                               *)
(*                                                                            *)
(* Given a type R for numbers, \bar R is the type R extended with symbols -oo *)
(* and +oo (notation scope: %E), suitable to represent extended real numbers. *)
(* When R is a numDomainType, \bar R is equipped with a canonical porderType  *)
(* and operations for addition/opposite. When R is a realDomainType, \bar R   *)
(* is equipped with a Canonical orderType.                                    *)
(*                                                                            *)
(*                  \bar R == coproduct of R and {+oo, -oo};                  *)
(*                            notation for extended (R:Type)                  *)
(*                    r%:E == injects real numbers into \bar R                *)
(*           +%E, -%E, *%E == addition/opposite/multiplication for extended   *)
(*                            reals                                           *)
(*                    +%dE == dual addition for extended reals                *)
(*                            (-oo + +oo = +oo instead of -oo)                *)
(*                            Import DualAddTheory for related lemmas         *)
(*                  x +? y == the addition of the extended real numbers x and *)
(*                            and y is defined, i.e., it is neither +oo - oo  *)
(*                            nor -oo + oo                                    *)
(*                  x *? y == the multiplication of the extended real numbers *)
(*                            x and y is not of the form 0 * +oo or 0 * -oo   *)
(*  (_ <= _)%E, (_ < _)%E, == comparison relations for extended reals         *)
(*  (_ >= _)%E, (_ > _)%E                                                     *)
(*   (\sum_(i in A) f i)%E == bigop-like notation in scope %E                 *)
(*      maxe x y, mine x y == notation for the maximum/minimum of two         *)
(*                            extended real numbers                           *)
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
(*                  ereal_dnbhs x == filter on extended real numbers that     *)
(*                                   corresponds to the deleted neighborhood  *)
(*                                   x^' if x is a real number and to         *)
(*                                   predicates that are eventually true if x *)
(*                                   is +oo/-oo.                              *)
(*                   ereal_nbhs x == same as ereal_dnbhs where dnbhs is       *)
(*                                   replaced with nbhs.                      *)
(*                ereal_loc_seq x == sequence that converges to x in the set  *)
(*                                   of extended real numbers.                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x %:E" (at level 2, format "x %:E").
Reserved Notation "x +? y" (at level 50, format "x  +?  y").
Reserved Notation "x *? y" (at level 50, format "x  *?  y").
Reserved Notation "'\bar' x" (at level 2, format "'\bar'  x").

Declare Scope ereal_dual_scope.
Declare Scope ereal_scope.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.

Variant extended (R : Type) := EFin of R | EPInf | ENInf.
Arguments EFin {R}.

Lemma EFin_inj T : injective (@EFin T).
Proof. by move=> a b; case. Qed.

Definition dual_extended := extended.

(* Notations in ereal_dual_scope should be kept *before* the
   corresponding notation in ereal_scope, otherwise when none of the
   scope is open (lte x y) would be displayed as (x < y)%dE, instead
   of (x < y)%E, for instance. *)
Notation "+oo" := (@EPInf _ : dual_extended _) : ereal_dual_scope.
Notation "+oo" := (@EPInf _) : ereal_scope.
Notation "-oo" := (@ENInf _ : dual_extended _) : ereal_dual_scope.
Notation "-oo" := (@ENInf _) : ereal_scope.
Notation "r %:E" := (@EFin _ r%R).
Notation "'\bar' R" := (extended R) : type_scope.
Notation "0" := (0%R%:E : dual_extended _) : ereal_dual_scope.
Notation "0" := (0%R%:E) : ereal_scope.
Notation "1" := (1%R%:E : dual_extended _) : ereal_dual_scope.
Notation "1" := (1%R%:E) : ereal_scope.

Bind    Scope ereal_dual_scope with dual_extended.
Bind    Scope ereal_scope with extended.
Delimit Scope ereal_dual_scope with dE.
Delimit Scope ereal_scope with E.

Local Open Scope ereal_scope.

Local Open Scope classical_set_scope.

Lemma EFin_bigcup T (F : nat -> set T) :
  EFin @` (\bigcup_i F i) = \bigcup_i (EFin @` F i).
Proof.
rewrite eqEsubset; split => [_ [r [n _ Fnr <-]]|]; first by exists n => //; exists r.
by move=> x [n _ [r Fnr <- /=]]; exists r => //; exists n.
Qed.

Lemma EFin_setC T (A : set T) :
  EFin @` (~` A) = (~` (EFin @` A)) `\` [set -oo; +oo].
Proof.
rewrite eqEsubset; split => [_ [r Ar <-]|[r | |]].
  by split => [|[]//]; apply: contra_not Ar => -[? ? [] <-].
- move=> [Ar _]; apply/not_exists2P; apply: contra_not Ar => h.
  by exists r => //; have [|//] := h r; apply: contrapT.
- by move=> -[_] /not_orP[_ /=].
- by move=> -[_] /not_orP[/=].
Qed.

Local Close Scope classical_set_scope.

Definition er_map T T' (f : T -> T') (x : \bar T) : \bar T' :=
  match x with
  | r%:E => (f r)%:E
  | +oo => +oo
  | -oo => -oo
  end.

Definition fine {R : zmodType} x : R := if x is EFin v then v else 0.

Section EqEReal.
Variable (R : eqType).

Definition eq_ereal (x y : \bar R) :=
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

Lemma eqe (r1 r2 : R) : (r1%:E == r2%:E) = (r1 == r2). Proof. by []. Qed.

End EqEReal.

Section ERealChoice.
Variable (R : choiceType).

Definition code (x : \bar R) :=
  match x with
  | r%:E => GenTree.Node 0 [:: GenTree.Leaf r]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option (\bar R) :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf r] => Some r%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

Definition ereal_choiceMixin := PcanChoiceMixin codeK.
Canonical ereal_choiceType  := ChoiceType (extended R) ereal_choiceMixin.

End ERealChoice.

Section ERealCount.
Variable (R : countType).

Definition ereal_countMixin := PcanCountMixin (@codeK R).
Canonical ereal_countType := CountType (extended R) ereal_countMixin.

End ERealCount.

Section ERealOrder.
Context {R : numDomainType}.
Implicit Types x y : \bar R.

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is Num.real
  | r1%:E, r2%:E => r1 <= r2
  | -oo, _    | _, +oo => true
  | +oo, _    | _, -oo => false
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, r%:E | r%:E, +oo => r \is Num.real
  | r1%:E, r2%:E => r1 < r2
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
  POrderType ereal_display (extended R) ereal_porderMixin.

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

Notation "x <= y" := (lee x y) (only printing) : ereal_dual_scope.
Notation "x <= y" := (lee x y) (only printing) : ereal_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_dual_scope.
Notation "x < y"  := (lte x y) (only printing) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x <= y <= z" := ((lee x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_dual_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) (only printing) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) (only printing) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_dual_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) (only printing) : ereal_scope.

Notation "x <= y" := (lee (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x <= y" := (lee (x : extended _) (y : extended _)) : ereal_scope.
Notation "x < y"  := (lte (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x < y"  := (lte (x : extended _) (y : extended _)) : ereal_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_dual_scope.
Notation "x >= y" := (y <= x) (only parsing) : ereal_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_dual_scope.
Notation "x > y"  := (y < x) (only parsing) : ereal_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_dual_scope.
Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ereal_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_dual_scope.
Notation "x < y <= z"  := ((x < y) && (y <= z)) : ereal_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_dual_scope.
Notation "x <= y < z"  := ((x <= y) && (y < z)) : ereal_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_dual_scope.
Notation "x < y < z"   := ((x < y) && (y < z)) : ereal_scope.

Lemma lee_fin (R : numDomainType) (x y : R) : (x%:E <= y%:E) = (x <= y)%R.
Proof. by []. Qed.

Lemma lte_fin (R : numDomainType) (x y : R) : (x%:E < y%:E) = (x < y)%R.
Proof. by []. Qed.

Lemma lee_ninfty_eq (R : numDomainType) (x : \bar R) : (x <= -oo) = (x == -oo).
Proof. by case: x. Qed.

Lemma lee_pinfty_eq (R : numDomainType) (x : \bar R) : (+oo <= x) = (x == +oo).
Proof. by case: x. Qed.

Section ERealOrder_numDomainType.
Context {R : numDomainType}.

Lemma lte_0_pinfty : (0 : \bar R) < +oo. Proof. exact: real0. Qed.

Lemma lte_ninfty_0 : -oo < (0 : \bar R). Proof. exact: real0. Qed.

Lemma lee_0_pinfty : (0 : \bar R) <= +oo. Proof. exact: real0. Qed.

Lemma lee_ninfty_0 : -oo <= (0 : \bar R). Proof. exact: real0. Qed.

End ERealOrder_numDomainType.

Section ERealOrder_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y : \bar R) (r : R).

Lemma lte_pinfty r : r%:E < +oo. Proof. exact: num_real. Qed.

Lemma lte_ninfty r : -oo < r%:E. Proof. exact: num_real. Qed.

Lemma lee_pinfty x : x <= +oo. Proof. by case: x => //= r; exact: num_real. Qed.

Lemma lee_ninfty x : -oo <= x. Proof. by case: x => //= r; exact: num_real. Qed.

Lemma gee0P x : 0 <= x <-> x = +oo \/ exists2 r, (r >= 0)%R & x = r%:E.
Proof.
split=> [|[->|[r r0 ->//]]]; last exact: lee_pinfty.
by case: x => [r r0 | _ |//]; [right; exists r|left].
Qed.

Lemma le_total_ereal : totalPOrderMixin [porderType of \bar R].
Proof.
by move=> [?||][?||]//=; rewrite (ltEereal, leEereal)/= ?num_real ?le_total.
Qed.

Canonical ereal_latticeType := LatticeType (extended R) le_total_ereal.
Canonical ereal_distrLatticeType :=  DistrLatticeType (extended R) le_total_ereal.
Canonical ereal_orderType := OrderType (extended R) le_total_ereal.

End ERealOrder_realDomainType.

Section ERealArith.
Context {R : numDomainType}.
Implicit Types x y z : \bar R.

Definition adde_subdef x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.

Definition adde := nosimpl adde_subdef.

Definition dual_adde_subdef x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%R%:E
  | +oo, _     => +oo
  | _    , +oo => +oo
  | -oo, _     => -oo
  | _    , -oo => -oo
  end.

Definition dual_adde := nosimpl dual_adde_subdef.

Definition oppe x :=
  match x with
  | r%:E  => (- r)%:E
  | -oo => +oo
  | +oo => -oo
  end.

Definition mule_subdef x y :=
  match x, y with
  | x%:E , y%:E => (x * y)%:E
  | -oo, y | y, -oo => if y == 0 then 0 else if 0 < y then -oo else +oo
  | +oo, y | y, +oo => if y == 0 then 0 else if 0 < y then +oo else -oo
  end.

Definition mule := nosimpl mule_subdef.

Definition abse x := if x is r%:E then `|r|%:E else +oo.

Local Open Scope classical_set_scope.

Lemma preimage_abse_pinfty : abse @^-1` [set +oo] = [set -oo; +oo].
Proof.
by rewrite predeqE => y; split ; move: y => [y//| |]//=; [right | left | case].
Qed.

Local Close Scope classical_set_scope.

End ERealArith.

Notation "+%dE"   := dual_adde.
Notation "+%E"   := adde.
Notation "-%E"   := oppe.
Notation "x + y" := (dual_adde x%dE y%dE) : ereal_dual_scope.
Notation "x + y" := (adde x y) : ereal_scope.
Notation "x - y" := (dual_adde x%dE (oppe y%dE)) : ereal_dual_scope.
Notation "x - y" := (adde x (oppe y)) : ereal_scope.
Notation "- x"   := (oppe (x%dE : dual_extended _)) : ereal_dual_scope.
Notation "- x"   := (oppe x) : ereal_scope.
Notation "*%E"   := mule.
Notation "x * y" := (mule (x%dE : dual_extended _) (y%dE : dual_extended _)) : ereal_dual_scope.
Notation "x * y" := (mule x y) : ereal_scope.
Notation "`| x |" := (abse (x%dE : dual_extended _)) : ereal_dual_scope.
Notation "`| x |" := (abse x) : ereal_scope.
Arguments abse {R}.

Notation "\- f" := (fun x => - f x)%dE : ereal_dual_scope.
Notation "\- f" := (fun x => - f x)%E : ereal_scope.
Notation "f \+ g" := (fun x => f x + g x)%dE : ereal_dual_scope.
Notation "f \+ g" := (fun x => f x + g x)%E : ereal_scope.
Notation "f \* g" := (fun x => f x * g x)%dE : ereal_dual_scope.
Notation "f \* g" := (fun x => f x * g x)%E : ereal_scope.
Notation "f \- g" := (fun x => f x - g x)%dE : ereal_dual_scope.
Notation "f \- g" := (fun x => f x - g x)%E : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%dE/0%:E]_(i <- r | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%:E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%dE/0%:E]_(i <- r) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%:E]_(i <- r) F%E) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%dE/0%:E]_(m <= i < n | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%:E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%dE/0%:E]_(m <= i < n) F%dE) : ereal_dual_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%:E]_(m <= i < n) F%E) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%dE/0%:E]_(i | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%:E]_(i | P%B) F%E) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%dE/0%:E]_i F%dE) : ereal_dual_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%:E]_i F%E) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%dE/0%:E]_(i : t | P%B) F%dE) (only parsing) : ereal_dual_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%:E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%dE/0%:E]_(i : t) F%dE) (only parsing) : ereal_dual_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%:E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%dE/0%:E]_(i < n | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%:E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%dE/0%:E]_(i < n) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%:E]_(i < n) F%E) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%dE/0%:E]_(i in A | P%B) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%:E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%dE/0%:E]_(i in A) F%dE) : ereal_dual_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%:E]_(i in A) F%E) : ereal_scope.

Section ERealOrderTheory.
Context {R : numDomainType}.
Implicit Types x y z : \bar R.

Local Tactic Notation "elift" constr(lm) ":" ident(x) :=
  by case: x => [||?]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) :=
  by case: x y => [?||] [?||]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) ident(z) :=
  by case: x y z => [?||] [?||] [?||]; first by rewrite ?eqe; apply: lm.

Lemma le0R x : 0 <= x -> (0 <= fine x)%R.
Proof. by case: x. Qed.

Lemma lt0R x : 0 < x < +oo -> (0 < fine x)%R.
Proof. by move: x => [x| |] //=; rewrite ?ltxx ?andbF// lte_fin => /andP[]. Qed.

Lemma lee_tofin (r0 r1 : R) : (r0 <= r1)%R -> r0%:E <= r1%:E.
Proof. by []. Qed.

Lemma lte_tofin (r0 r1 : R) : (r0 < r1)%R -> r0%:E < r1%:E.
Proof. by []. Qed.

End ERealOrderTheory.

Section finNumPred.
Context {R : numDomainType}.
Implicit Type (x : \bar R).

Definition fin_num := [qualify a x : \bar R | (x != -oo) && (x != +oo)].
Fact fin_num_key : pred_key fin_num. by []. Qed.
Canonical fin_num_keyd := KeyedQualifier fin_num_key.

Lemma fin_numE x : (x \is a fin_num) = (x != -oo) && (x != +oo).
Proof. by []. Qed.

Lemma fin_numP x : reflect ((x != -oo) /\ (x != +oo)) (x \in fin_num).
Proof. by apply/(iffP idP) => [/andP//|/andP]. Qed.

Lemma fin_numEn x : (x \isn't a fin_num) = (x == -oo) || (x == +oo).
Proof. by rewrite fin_numE negb_and ?negbK. Qed.

Lemma fin_numPn x : reflect (x = -oo \/ x = +oo) (x \isn't a fin_num).
Proof. by rewrite fin_numEn; apply: (iffP orP) => -[]/eqP; by [left|right]. Qed.

End finNumPred.

Section ERealArithTh_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y z : \bar R) (r : R).

Lemma fine_eq0 x : x \is a fin_num -> (fine x == 0%R) = (x == 0).
Proof. by move: x => [//| |] /=; rewrite fin_numE. Qed.

Lemma EFinN r : (- r)%:E = (- r%:E). Proof. by []. Qed.

Lemma fineN x : fine (- x) = (- fine x)%R.
Proof. by case: x => //=; rewrite oppr0. Qed.

Lemma EFinD r r' : (r + r')%:E = r%:E + r'%:E. Proof. by []. Qed.

Lemma EFinB r r' : (r - r')%:E = r%:E - r'%:E. Proof. by []. Qed.

Lemma EFinM r r' : (r * r')%:E = r%:E * r'%:E. Proof. by []. Qed.

Lemma sumEFin I s P (F : I -> R) :
  \sum_(i <- s | P i) (F i)%:E = (\sum_(i <- s | P i) F i)%:E.
Proof. by rewrite (big_morph _ EFinD erefl). Qed.

Definition adde_def x y :=
  ~~ ((x == +oo) && (y == -oo)) && ~~ ((x == -oo) && (y == +oo)).

Local Notation "x +? y" := (adde_def x y).

Lemma adde_defC x y : x +? y = y +? x.
Proof. by rewrite /adde_def andbC (andbC (x == -oo)) (andbC (x == +oo)). Qed.

Lemma adde_defNN x y : - x +? - y = x +? y.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_defEninfty x : (x +? -oo) = (x != +oo).
Proof. by case: x. Qed.

Lemma ge0_adde_def : {in [pred x | x >= 0] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma addeC : commutative (S := \bar R) +%E.
Proof. by case=> [x||] [y||] //; rewrite /adde /= addrC. Qed.

Lemma adde0 : right_id (0 : \bar R) +%E.
Proof. by case=> // r; rewrite /adde /= addr0. Qed.

Lemma add0e : left_id (0 : \bar R) +%E.
Proof. by move=> x; rewrite addeC adde0. Qed.

Lemma addeA : associative (S := \bar R) +%E.
Proof. by case=> [x||] [y||] [z||] //; rewrite /adde /= addrA. Qed.

Canonical adde_monoid := Monoid.Law addeA add0e adde0.
Canonical adde_comoid := Monoid.ComLaw addeC.

Lemma addeAC : @right_commutative (\bar R) _ +%E.
Proof. by move=> x y z; rewrite -addeA (addeC y) addeA. Qed.

Lemma addeCA : @left_commutative (\bar R) _ +%E.
Proof. by move=> x y z; rewrite addeC -addeA (addeC x). Qed.

Lemma addeACA : @interchange (\bar R) +%E +%E.
Proof. by case=> [r||] [s||] [t||] [u||] //; rewrite /adde /= addrACA. Qed.

Lemma adde_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof.
by move: x y => [x| |] [y| |] //; rewrite !lte_fin; exact: addr_gt0.
Qed.

Lemma padde_eq0 x y : 0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: paddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma nadde_eq0 x y : x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite !lee_fin; first exact: naddr_eq0.
by move=> x0 _ /=; rewrite andbF.
Qed.

Lemma realDe x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x + y)%O.
Proof. case: x y => [x||] [y||] //; exact: realD. Qed.

Lemma oppe0 : - 0 = 0 :> \bar R.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := \bar R) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.

Lemma oppe_eq0 x : (- x == 0)%E = (x == 0)%E.
Proof. by rewrite -(can_eq oppeK) oppe0. Qed.

Lemma oppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move: x y => [x| |] [y| |] //= _; rewrite opprD. Qed.

Lemma sube0 x : x - 0 = x.
Proof. by move: x => [x| |] //; rewrite -EFinB subr0. Qed.

Lemma sub0e x : 0 - x = - x.
Proof. by move: x => [x| |] //; rewrite -EFinB sub0r. Qed.

Lemma muleC x y : x * y = y * x.
Proof. by move: x y => [r||] [s||]//=; rewrite -EFinM mulrC. Qed.

Lemma onee_neq0 : 1 != 0 :> \bar R. Proof. exact: oner_neq0. Qed.
Lemma onee_eq0 : 1 == 0 :> \bar R = false. Proof. exact: oner_eq0. Qed.

Lemma mule1 x : x * 1 = x.
Proof.
by move: x=> [r||]/=; rewrite /mule/= ?mulr1 ?(negbTE onee_neq0) ?lte_tofin.
Qed.

Lemma mul1e x : 1 * x = x.
Proof. by rewrite muleC mule1. Qed.

Lemma mule0 x : x * 0 = 0.
Proof. by move: x => [r| |] //=; rewrite /mule/= ?mulr0// eqxx. Qed.

Lemma mul0e x : 0 * x = 0.
Proof. by move: x => [r| |]/=; rewrite /mule/= ?mul0r// eqxx. Qed.

Canonical mule_monoid := @Monoid.MulLaw _ _ mule mul0e mule0.

Definition mule_def x y :=
  ~~ (((x == 0) && (`| y | == +oo)) || ((y == 0) && (`| x | == +oo))).

Local Notation "x *? y" := (mule_def x y).

Lemma mule_defC x y : x *? y = y *? x.
Proof. by rewrite [in LHS]/mule_def orbC. Qed.

Lemma mule_def_fin x y : x \is a fin_num -> y \is a fin_num -> x *? y.
Proof.
move: x y => [x| |] [y| |] finx finy//.
by rewrite /mule_def negb_or 2!negb_and/= 2!orbT.
Qed.

Lemma mule_def_neq0_infty x y : x != 0 -> y \isn't a fin_num -> x *? y.
Proof. by move: x y => [x| |] [y| |]// x0 _; rewrite /mule_def (negbTE x0). Qed.

Lemma mule_def_infty_neq0 x y : x \isn't a fin_num -> y!= 0 -> x *? y.
Proof. by move: x y => [x| |] [y| |]// _ y0; rewrite /mule_def (negbTE y0). Qed.

Lemma neq0_mule_def x y :  x * y != 0 -> x *? y.
Proof.
move: x y => [x| |] [y| |] //; first by rewrite mule_def_fin.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_def_neq0_infty.
- by have [->|?] := eqVneq x 0%R; rewrite ?mul0e ?eqxx// mule_def_neq0_infty.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_def_infty_neq0.
- by have [->|?] := eqVneq y 0%R; rewrite ?mule0 ?eqxx// mule_def_infty_neq0.
Qed.

Lemma ltpinfty_adde_def : {in [pred x | x < +oo] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma abse_eq0 x : (`|x| == 0) = (x == 0).
Proof. by move: x => [| |] //= r; rewrite !eqe normr_eq0. Qed.

Lemma abse0 : `|0| = 0 :> \bar R. Proof. by rewrite /abse normr0. Qed.

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

Lemma oppe_subset (A B : set (\bar R)) :
  ((A `<=` B) <-> (-%E @` A `<=` -%E @` B))%classic.
Proof.
split=> [AB _ [] x ? <-|AB x Ax]; first by exists x => //; exact: AB.
have /AB[y By] : ((-%E @` A) (- x))%classic by exists x.
by rewrite eqe_oppP => <-.
Qed.

Lemma fin_numN x : (- x \is a fin_num) = (x \is a fin_num).
Proof. by rewrite !fin_numE 2!eqe_oppLR andbC. Qed.

Lemma fin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fin_numB x y :
  (x - y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fin_numM x y : x \is a fin_num -> y \is a fin_num ->
  x * y \is a fin_num.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fineD :
  {in (@fin_num R) &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fin_num_adde_def x y : y \is a fin_num -> x +? y.
Proof. by move: x y => [x| |] [y | |]. Qed.

Lemma fineK x : x \is a fin_num -> (fine x)%:E = x.
Proof. by case: x. Qed.

Lemma telescope_sume n m (f : nat -> \bar R) :
  (forall i, (n <= i <= m)%N -> f i \is a fin_num) -> (n <= m)%N ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof.
move=> nmf nm; under eq_big_nat => i /andP[ni im] do
  rewrite -[f i.+1]fineK -1?[f i]fineK ?(nmf, ni, im) 1?ltnW//= -EFinD.
by rewrite sumEFin telescope_sumr// EFinB !fineK ?nmf ?nm ?leqnn.
Qed.

Lemma addeK x y : x \is a fin_num -> y + x - x = y.
Proof. by move: x y => [x| |] [y| |] //; rewrite -EFinD -EFinB addrK. Qed.

Lemma subeK x y : y \is a fin_num -> x - y + y = x.
Proof. by move: x y => [x| |] [y| |] //; rewrite -EFinD subrK. Qed.

Lemma subee x : x \is a fin_num -> x - x = 0.
Proof. by move: x => [r _| |] //; rewrite -EFinB subrr. Qed.

Lemma sube_eq x y z : x \is a fin_num -> (y +? z) ->
  (x - z == y) = (x == y + z).
Proof.
by move: x y z => [x| |] [y| |] [z| |] // _ _; rewrite !eqe subr_eq.
Qed.

Lemma adde_eq_ninfty x y : (x + y == -oo) = ((x == -oo) || (y == -oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma addooe x : x != -oo -> +oo + x = +oo.
Proof. by case: x. Qed.

Lemma addeoo x : x != -oo -> x + +oo = +oo.
Proof. by case: x. Qed.

Lemma adde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_ss_eq0 x y : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  x + y == 0 = (x == 0) && (y == 0).
Proof. by move=> /orP[|] /andP[]; [exact: padde_eq0|exact: nadde_eq0]. Qed.

Lemma esum_ninftyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
split=> [|[i [si Pi fi]]].
  rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
  by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
rewrite big_mkcond (bigID (xpred1 i))/= (eq_bigr (fun _ => -oo)); last first.
  by move=> j /eqP ->; rewrite Pi.
rewrite big_const_seq/= [X in X + _](_ : _ = -oo)//.
elim: s i Pi fi si => // h t ih i Pi fi.
rewrite inE => /predU1P[<-/=|it]; first by rewrite eqxx.
by rewrite /= iterD ih//=; case: (_ == _).
Qed.

Lemma esum_ninfty (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
apply/idP/idP => [/eqP/esum_ninftyP|/existsP[i /andP[Pi /eqP fi]]].
  by move=> -[i [_ Pi fi]]; apply/existsP; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_ninftyP; exists i.
Qed.

Lemma esum_pinftyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
move=> finoo; split=> [|[i [si Pi fi]]].
  rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
  by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
elim: s i Pi fi si => // h t ih i Pi fi.
rewrite inE => /predU1P[<-/=|it].
  rewrite big_cons Pi fi addooe//.
  by apply/eqP => /esum_ninftyP[j [jt /finoo/negbTE/eqP]].
by rewrite big_cons; case: ifPn => Ph; rewrite (ih i)// addeoo// finoo.
Qed.

Lemma esum_pinfty (I : finType) (P : {pred I}) (f : I -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
move=> fio; apply/idP/existsP => [/eqP /=|[/= i /andP[Pi /eqP fi]]].
  have {}fio : (forall i, P i -> f i != -oo) by move=> i Pi; exact: fio.
  by move=> /(esum_pinftyP _ fio)[i [_ Pi fi]]; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_pinftyP => //; exists i.
Qed.

Lemma adde_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move: x y => [r0| |] [r1| |] // ? ?; rewrite !lee_fin addr_ge0. Qed.

Lemma adde_le0 x y : x <= 0 -> y <= 0 -> x + y <= 0.
Proof.
move: x y => [r0||] [r1||]// ? ?; rewrite !lee_fin -(addr0 0%R); exact: ler_add.
Qed.

Lemma oppe_gt0 x : (0 < - x) = (x < 0).
Proof. move: x => [x||] //; exact: oppr_gt0. Qed.

Lemma oppe_lt0 x : (- x < 0) = (0 < x).
Proof. move: x => [x||] //; exact: oppr_lt0. Qed.

Lemma oppe_ge0 x : (0 <= - x) = (x <= 0).
Proof. move: x => [x||] //; exact: oppr_ge0. Qed.

Lemma oppe_le0 x : (- x <= 0) = (0 <= x).
Proof. move: x => [x||] //; exact: oppr_le0. Qed.

Lemma sume_ge0 T (f : T -> \bar R) (P : pred T) :
  (forall t, P t -> 0 <= f t) -> forall l, 0 <= \sum_(i <- l | P i) f i.
Proof. by move=> f0 l; elim/big_rec : _ => // t x Pt; apply/adde_ge0/f0. Qed.

Lemma sume_le0 T (f : T -> \bar R) (P : pred T) :
  (forall t, P t -> f t <= 0) -> forall l, \sum_(i <- l | P i) f i <= 0.
Proof. by move=> f0 l; elim/big_rec : _ => // t x Pt; apply/adde_le0/f0. Qed.

Lemma mule_ninfty_pinfty : -oo * +oo = -oo :> \bar R.
Proof. by rewrite /mule /= lte_0_pinfty. Qed.

Lemma mule_pinfty_ninfty : +oo * -oo = -oo :> \bar R.
Proof. by rewrite muleC mule_ninfty_pinfty. Qed.

Lemma mule_pinfty_pinfty : +oo * +oo = +oo :> \bar R.
Proof. by rewrite /mule /= lte_0_pinfty. Qed.

Lemma mule_ninfty_ninfty : -oo * -oo = +oo :> \bar R.
Proof. by []. Qed.

Lemma mulrpinfty_real r : r \is Num.real -> r%:E * +oo = (Num.sg r)%:E * +oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|/negbT rn0].
move: rreal => /orP[|]; rewrite le_eqVlt !lte_fin /Num.sg.
  rewrite eq_sym (negbTE rn0)/= => rgt0.
  by rewrite [(r < 0)%R]lt_def lt_geF// eq_sym rn0/= ltr01 rgt0.
by rewrite (negbTE rn0)/= => rlt0; rewrite lt_def lt_geF// rn0 rlt0/= ltr0N1.
Qed.

Lemma mulpinftyr_real r : r \is Num.real -> +oo * r%:E = (Num.sg r)%:E * +oo.
Proof. by move=> rreal; rewrite muleC mulrpinfty_real. Qed.

Lemma mulrninfty_real r : r \is Num.real -> r%:E * -oo = (Num.sg r)%:E * -oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|/negbT rn0].
move: rreal => /orP[|]; rewrite le_eqVlt !lte_fin /Num.sg.
  rewrite eq_sym (negbTE rn0)/= => rgt0.
  by rewrite [(r < 0)%R]lt_def lt_geF// andbF ltr01 rgt0.
by rewrite (negbTE rn0)/= => rlt0; rewrite lt_def lt_geF// andbF rlt0 ltr0N1.
Qed.

Lemma mulninftyr_real r : r \is Num.real -> -oo * r%:E = (Num.sg r)%:E * -oo.
Proof. by move=> rreal; rewrite muleC mulrninfty_real. Qed.

Definition mulrinfty_real :=
  (mulrpinfty_real, mulpinftyr_real, mulrninfty_real, mulninftyr_real).

Lemma mulN1e x : - 1%E * x = - x.
Proof.
rewrite -EFinN /mule/=; case: x => [x||];
  do ?[by rewrite mulN1r|by rewrite eqe oppr_eq0 oner_eq0 lte_fin ltr0N1].
Qed.

Lemma muleN1 x : x * - 1%E = - x. Proof. by rewrite muleC mulN1e. Qed.

Lemma mule_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move: x y => [x||] [y||] x0 y0 //; rewrite /mule/= ?(lte_0_pinfty,mulf_neq0)//;
  try by (rewrite (negbTE x0); case: ifPn) ||
      by (rewrite (negbTE y0); case: ifPn).
Qed.

Lemma mule_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/idP/idP => [|/orP[] /eqP->]; rewrite ?(mule0, mul0e)//.
by apply: contraTT => /norP[]; apply: mule_neq0.
Qed.

Lemma mule_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin,eqe,lte_fin)//.
- exact: mulr_ge0.
- rewrite le_eqVlt => /predU1P[<- _|x0 _]; first by rewrite eqxx.
  by rewrite gt_eqF // x0 lee_0_pinfty.
- move=> _; rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite eqxx.
  by rewrite gt_eqF // y0 lee_0_pinfty.
- by rewrite lte_0_pinfty.
Qed.

Lemma mule_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof.
by rewrite !lt_def => /andP[? ?] /andP[? ?]; rewrite mule_neq0 ?mule_ge0.
Qed.

Lemma mule_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin,eqe,lte_fin)//.
- exact: mulr_le0.
- by rewrite lt_leAnge => -> _; case: ifP => _ //; rewrite andbF lee_0_pinfty.
- by rewrite lt_leAnge => _ ->; case: ifP => _ //; rewrite andbF lee_0_pinfty.
Qed.

Lemma mule_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
move: x y => [x| |] [y| |] //; rewrite /mule/= ?(lee_fin,lte_fin).
- exact: mulr_le0_ge0.
- by move=> x0 _; case: ifP => _ //; rewrite lt_leAnge /= x0 andbF lee_ninfty_0.
- move=> _; rewrite le_eqVlt => /predU1P[<-|->]; first by rewrite eqxx.
  by case: ifP => _ //; rewrite lee_ninfty_0.
- by rewrite lte_0_pinfty lee_ninfty_0.
Qed.

Lemma mule_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x0 y0; rewrite muleC mule_le0_ge0. Qed.

Lemma mule_lt0_lt0 x y : x < 0 -> y < 0 -> 0 < x * y.
Proof.
by rewrite !lt_neqAle => /andP[? ?]/andP[*]; rewrite eq_sym mule_neq0 ?mule_le0.
Qed.

Lemma mule_gt0_lt0 x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
rewrite lt_def !lt_neqAle => /andP[? ?]/andP[? ?].
by rewrite mule_neq0 ?mule_ge0_le0.
Qed.

Lemma mule_lt0_gt0 x y : x < 0 -> 0 < y -> x * y < 0.
Proof. by move=> x0 y0; rewrite muleC mule_gt0_lt0. Qed.

Lemma gte_opp x : 0 < x -> - x < x.
Proof. by case: x => //= r; rewrite !lte_fin; apply: gtr_opp. Qed.

Lemma realMe x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x * y)%O.
Proof.
case: x y => [x||] [y||]// rx ry;
  do ?[exact: realM
      |by rewrite /mule/= lte_0_pinfty
      |by rewrite mulrinfty_real ?realE -?lee_fin// /Num.sg;
          case: ifP; [|case: ifP]; rewrite ?mul0e /Order.comparable ?lexx;
          rewrite ?mulN1e ?lee_ninfty_0 ?mul1e ?lee_0_pinfty
      |by rewrite mule_ninfty_ninfty /Order.comparable lee_0_pinfty].
Qed.

Lemma abse_ge0 x : 0 <= `|x|.
Proof. by move: x => [x| |] /=; rewrite ?lee_0_pinfty ?lee_fin. Qed.

Lemma gee0_abs x : 0 <= x -> `|x| = x.
Proof.
by move: x => [x| |]//; rewrite lee_fin => x0; apply/eqP; rewrite eqe ger0_norm.
Qed.

Lemma gte0_abs x : 0 < x -> `|x| = x. Proof. by move=> /ltW/gee0_abs. Qed.

Lemma lee0_abs x : x <= 0 -> `|x| = - x.
Proof.
by move: x => [x| |]//; rewrite lee_fin => x0; apply/eqP; rewrite eqe ler0_norm.
Qed.

Lemma lte0_abs x : x < 0 -> `|x| = - x.
Proof. by move=> /ltW/lee0_abs. Qed.

End ERealArithTh_numDomainType.
Notation "x +? y" := (adde_def x%dE y%dE) : ereal_dual_scope.
Notation "x +? y" := (adde_def x y) : ereal_scope.
Notation "x *? y" := (mule_def x%dE y%dE) : ereal_dual_scope.
Notation "x *? y" := (mule_def x y) : ereal_scope.

Notation maxe := (@Order.max ereal_display _).
Notation "@ 'maxe' R" := (@Order.max ereal_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.

Notation mine := (@Order.min ereal_display _).
Notation "@ 'mine' R" := (@Order.min ereal_display R)
  (at level 10, R at level 8, only parsing) : fun_scope.

Module DualAddTheoryNumDomain.

Section DualERealArithTh_numDomainType.

Local Open Scope ereal_dual_scope.

Context {R : numDomainType}.

Implicit Types x y z : \bar R.

Lemma dual_addeE x y : (x + y)%dE = - ((- x) + (- y))%E.
Proof. by case: x => [x| |]; case: y => [y| |] //=; rewrite opprD !opprK. Qed.

Lemma dual_sumeE I (r : seq I) (P : pred I) (F : I -> \bar R) :
  (\sum_(i <- r | P i) F i)%dE = - (\sum_(i <- r | P i) (- F i)%E)%E.
Proof.
apply: (big_ind2 (fun x y => x = - y)%E) => [|_ x _ y -> ->|i _].
- by rewrite oppe0.
- by rewrite dual_addeE !oppeK.
- by rewrite oppeK.
Qed.

Lemma dual_addeE_def x y : x +? y -> (x + y)%dE = (x + y)%E.
Proof. by case: x => [x| |]; case: y. Qed.

Lemma dEFinD (r r' : R) : (r + r')%R%:E = r%:E + r'%:E.
Proof. by []. Qed.

Lemma dEFinB (r r' : R) : (r - r')%R%:E = r%:E - r'%:E.
Proof. by []. Qed.

Lemma dsumEFin I r P (F : I -> R) :
  \sum_(i <- r | P i) (F i)%:E = (\sum_(i <- r | P i) F i)%R%:E.
Proof. by rewrite dual_sumeE sumEFin sumrN EFinN oppeK. Qed.

Lemma daddeC : commutative (S := \bar R) +%dE.
Proof. by move=> x y; rewrite !dual_addeE addeC. Qed.

Lemma dadde0 : right_id (0 : \bar R) +%dE.
Proof. by move=> x; rewrite dual_addeE eqe_oppLRP oppe0 adde0. Qed.

Lemma dadd0e : left_id (0 : \bar R) +%dE.
Proof. by move=> x;rewrite dual_addeE eqe_oppLRP oppe0 add0e. Qed.

Lemma daddeA : associative (S := \bar R) +%dE.
Proof. by move=> x y z; rewrite !dual_addeE !oppeK addeA. Qed.

Canonical dadde_monoid := Monoid.Law daddeA dadd0e dadde0.
Canonical dadde_comoid := Monoid.ComLaw daddeC.

Lemma daddeAC : right_commutative (S := \bar R) +%dE.
Proof. by move=> x y z; rewrite !dual_addeE !oppeK addeAC. Qed.

Lemma daddeCA : left_commutative (S := \bar R) +%dE.
Proof. by move=> x y z; rewrite !dual_addeE !oppeK addeCA. Qed.

Lemma daddeACA : @interchange (\bar R) +%dE +%dE.
Proof. by move=> x y z u; rewrite !dual_addeE !oppeK addeACA. Qed.

Lemma realDed x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x + y)%O.
Proof. case: x y => [x||] [y||] //; exact: realD. Qed.

Lemma doppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move: y => [y| |] _ //; rewrite !dual_addeE !oppeK oppeD. Qed.

Lemma dsube0 x : x - 0 = x.
Proof. by move: x => [x| |] //; rewrite -dEFinB subr0. Qed.

Lemma dsub0e x : 0 - x = - x.
Proof. by move: x => [x| |] //; rewrite -dEFinB sub0r. Qed.

Lemma dfin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma dfineD :
  {in (@fin_num R) &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma daddeK x y : x \is a fin_num -> y + x - x = y.
Proof. by move=> fx; rewrite !dual_addeE oppeK addeK ?oppeK; case: x fx. Qed.

Lemma dsubeK x y : y \is a fin_num -> x - y + y = x.
Proof. by move=> fy; rewrite !dual_addeE oppeK subeK ?oppeK; case: y fy. Qed.

Lemma dsubee x : x \is a fin_num -> x - x = 0.
Proof. by move=> fx; rewrite dual_addeE subee ?oppe0; case: x fx. Qed.

Lemma dsube_eq x y z : x \is a fin_num -> (y +? z) ->
  (x - z == y) = (x == y + z).
Proof.
by move: x y z => [x| |] [y| |] [z| |] // _ _; rewrite !eqe subr_eq.
Qed.

Lemma dadde_eq_pinfty x y : (x + y == +oo) = ((x == +oo) || (y == +oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma daddooe x : x != -oo -> +oo + x = +oo.
Proof. by case: x. Qed.

Lemma daddeoo x : x != -oo -> x + +oo = +oo.
Proof. by case: x. Qed.

Lemma dadde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma dadde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma ndadde_eq0 x y : x <= 0 -> y <= 0 -> x + y == 0 = (x == 0) && (y == 0).
Proof.
move: x y => [x||] [y||] //.
- by rewrite !lee_fin -dEFinD !eqe; exact: naddr_eq0.
- by rewrite /adde/= (_ : -oo == 0 = false)// andbF.
Qed.

Lemma pdadde_eq0 x y : 0 <= x -> 0 <= y -> x + y == 0 = (x == 0) && (y == 0).
Proof.
move: x y => [x||] [y||] //.
- by rewrite !lee_fin -dEFinD !eqe; exact: paddr_eq0.
- by rewrite /adde/= (_ : +oo == 0 = false)// andbF.
Qed.

Lemma dadde_ss_eq0 x y : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  x + y == 0 = (x == 0) && (y == 0).
Proof. move=> /orP[|] /andP[]; [exact: pdadde_eq0|exact: ndadde_eq0]. Qed.

Lemma desum_pinftyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
rewrite dual_sumeE eqe_oppLRP /= esum_ninftyP.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_pinfty (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
rewrite dual_sumeE eqe_oppLR esum_ninfty.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

Lemma desum_ninftyP
    (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != +oo) ->
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
move=> fioo.
rewrite dual_sumeE eqe_oppLRP /= esum_pinftyP => [|i Pi]; last first.
  by rewrite eqe_oppLR fioo.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_ninfty (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (forall i, f i != +oo) ->
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
move=> finoo.
rewrite dual_sumeE eqe_oppLR /= esum_pinfty => [|i]; rewrite ?eqe_oppLR //.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

Lemma dadde_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. rewrite dual_addeE oppe_ge0 -!oppe_le0; exact: adde_le0. Qed.

Lemma dadde_le0 x y : x <= 0 -> y <= 0 -> x + y <= 0.
Proof. rewrite dual_addeE oppe_le0 -!oppe_ge0; exact: adde_ge0. Qed.

Lemma dsume_ge0 T (f : T -> \bar R) (P : pred T) :
  (forall n, P n -> 0 <= f n) -> forall l, 0 <= \sum_(i <- l | P i) f i.
Proof.
move=> u0 l; rewrite dual_sumeE oppe_ge0 sume_le0 // => t Pt.
rewrite oppe_le0; exact: u0.
Qed.

Lemma dsume_le0 T (f : T -> \bar R) (P : pred T) :
  (forall n, P n -> f n <= 0) -> forall l, \sum_(i <- l | P i) f i <= 0.
Proof.
move=> u0 l; rewrite dual_sumeE oppe_le0 sume_ge0 // => t Pt.
rewrite oppe_ge0; exact: u0.
Qed.

Lemma gte_dopp (r : \bar R) : (0 < r)%E -> (- r < r)%E.
Proof. by case: r => //= r; rewrite !lte_fin; apply: gtr_opp. Qed.

End DualERealArithTh_numDomainType.

End DualAddTheoryNumDomain.

Section ERealArithTh_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y z u a b : \bar R) (r : R).

Lemma fin_numElt x : (x \is a fin_num) = (-oo < x < +oo).
Proof. by rewrite fin_numE -lee_pinfty_eq -lee_ninfty_eq -2!ltNge. Qed.

Lemma fin_numPlt x : reflect (-oo < x < +oo) (x \is a fin_num).
Proof. by rewrite fin_numElt; exact: idP. Qed.

Lemma lte_pinfty_eq x : (x < +oo) = (x \is a fin_num) || (x == -oo).
Proof. by case: x => // x //=; exact: lte_pinfty. Qed.

Lemma ge0_fin_numE x : 0 <= x -> (x \is a fin_num) = (x < +oo).
Proof. by move: x => [x| |] => // x0; rewrite fin_numElt lte_ninfty. Qed.

Lemma eq_pinftyP x : x = +oo <-> (forall A, (0 < A)%R -> A%:E <= x).
Proof.
split=> [-> // A A0|Ax]; first by rewrite lee_pinfty.
apply/eqP; rewrite eq_le lee_pinfty /= leNgt; apply/negP.
move: x Ax => [x Ax _|//|]; last by move/(_ _ ltr01).
move/not_forallP : Ax; apply; exists (`|x| + 1)%R.
apply/not_implyP; split; first by rewrite -(addr0 0%R) ler_lt_add.
rewrite lee_fin => /le_trans/(_ (ler_norm x)).
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

Lemma seq_psume_eq0 (I : choiceType) (r : seq I)
    (P : pred I) (F : I -> \bar R) : (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i <- r | P i) F i == 0)%E = all (fun i => P i ==> (F i == 0%E)) r.
Proof.
move=> F0; apply/eqP/allP => PF0; last first.
  rewrite big_seq_cond big1// => i /andP[ir Pi].
  by have := PF0 _ ir; rewrite Pi implyTb => /eqP.
move=> i ir; apply/implyP => Pi; apply/eqP.
have rPF : {in r, forall i, P i ==> (F i \is a fin_num)}.
  move=> j jr; apply/implyP => Pj; rewrite fin_numElt; apply/andP; split.
    by rewrite (lt_le_trans _ (F0 _ Pj))// lte_ninfty.
  rewrite ltNge; apply/eqP; rewrite lee_pinfty_eq; apply/eqP/negP => /eqP Fjoo.
  have PFninfty k : P k -> F k != -oo%E.
    by move=> Pk; rewrite gt_eqF// (lt_le_trans _ (F0 _ Pk))// lte_ninfty.
  have /esum_pinftyP : exists i, [/\ i \in r, P i & F i = +oo%E] by exists j.
  by move=> /(_ PFninfty); rewrite PF0.
have ? : (\sum_(i <- r | P i) (fine \o F) i == 0)%R.
  apply/eqP/EFin_inj; rewrite big_seq_cond -sumEFin.
  rewrite (eq_bigr (fun i0 => F i0)); last first.
    move=> j /andP[jr Pj] /=; rewrite fineK//.
    by have := rPF _ jr; rewrite Pj implyTb.
  by rewrite -big_seq_cond PF0.
have /allP/(_ _ ir) : all (fun i => P i ==> ((fine \o F) i == 0))%R r.
  by rewrite -psumr_eq0// => j Pj/=; apply/le0R/F0.
rewrite Pi implyTb => /= => /eqP Fi0.
rewrite -(@fineK _ (F i))//; last by have := rPF _ ir; rewrite Pi implyTb.
by rewrite Fi0.
Qed.

Lemma lte_add_pinfty x y : x < +oo -> y < +oo -> x + y < +oo.
Proof. by move: x y => -[r [r'| |]| |] // ? ?; rewrite -EFinD lte_pinfty. Qed.

Lemma lte_sum_pinfty I (s : seq I) (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i < +oo) -> \sum_(i <- s | P i) f i < +oo.
Proof.
elim/big_ind : _ => [_|x y xoo yoo foo|i ?]; [exact: lte_pinfty| |exact].
by apply: lte_add_pinfty; [exact: xoo| exact: yoo].
Qed.

Lemma sube_gt0 x y : (0 < y - x) = (x < y).
Proof.
move: x y => [r | |] [r'| |] //=; rewrite ?(lte_pinfty,lte_ninfty) //.
by rewrite !lte_fin subr_gt0.
Qed.

Lemma sube_le0 x y : (y - x <= 0) = (y <= x).
Proof. by rewrite !leNgt sube_gt0. Qed.

Lemma suber_ge0 y x : y \is a fin_num -> (0 <= x - y) = (y <= x).
Proof.
by move: x y => [x| |] [y| |] //= _; rewrite ?(lee_pinfty, lee_fin, subr_ge0).
Qed.

Lemma subre_ge0 x y : y \is a fin_num -> (0 <= y - x) = (x <= y).
Proof.
move: x y => [x| |] [y| |] //=; rewrite ?(lee_pinfty,lee_ninfty,lee_fin) //=.
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

Lemma muleN x y : x * - y = - (x * y).
Proof.
move: x y => [x| |] [y| |] //=; rewrite /mule/=; try by rewrite lte_pinfty.
- by rewrite mulrN.
- by rewrite !eqe !lte_fin; case: ltrgtP => //; rewrite oppe0.
- by rewrite !eqe !lte_fin; case: ltrgtP => //; rewrite oppe0.
- rewrite !eqe oppr_eq0 eq_sym; case: ifP; rewrite ?oppe0// => y0.
  by rewrite [RHS]fun_if ltNge if_neg EFinN lee_oppl oppe0 le_eqVlt eqe y0.
- rewrite !eqe oppr_eq0 eq_sym; case: ifP; rewrite ?oppe0// => y0.
  by rewrite [RHS]fun_if ltNge if_neg EFinN lee_oppl oppe0 le_eqVlt eqe y0.
Qed.

Lemma mulNe x y : - x * y = - (x * y). Proof. by rewrite muleC muleN muleC. Qed.

Lemma muleNN x y : - x * - y = x * y. Proof. by rewrite mulNe muleN oppeK. Qed.

Lemma mulrpinfty r : r%:E * +oo%E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite [LHS]mulrpinfty_real// num_real. Qed.

Lemma mulpinftyr r : +oo%E * r%:E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite muleC mulrpinfty. Qed.

Lemma mulrninfty r : r%:E * -oo%E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite [LHS]mulrninfty_real// num_real. Qed.

Lemma mulninftyr r : -oo%E * r%:E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite muleC mulrninfty. Qed.

Definition mulrinfty := (mulrpinfty, mulpinftyr, mulrninfty, mulninftyr).

Lemma lte_mul_pinfty x y : 0 <= x -> x \is a fin_num -> y < +oo -> x * y < +oo.
Proof.
move: x y => [x| |] [y| |] // x0 xfin _; first by rewrite -EFinM lte_pinfty.
rewrite mulrinfty; move: x0; rewrite lee_fin le_eqVlt => /predU1P[<-|x0].
- by rewrite sgr0 mul0e lte_pinfty.
- by rewrite gtr0_sg // mul1e.
Qed.

Lemma mule_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
move: x y => [x| |] [y| |] //; rewrite ?lee_fin.
- by move=> x0 y0; rewrite !lte_fin; exact: mulr_ge0_gt0.
- rewrite le_eqVlt => /predU1P[<-|x0] _; first by rewrite mul0e ltxx.
  by rewrite lte_pinfty andbT mulrpinfty gtr0_sg// mul1e lte_fin x0 lte_pinfty.
- move=> _; rewrite le_eqVlt => /predU1P[<-|x0].
    by rewrite mule0 ltxx andbC.
  by rewrite lte_pinfty/= mulpinftyr gtr0_sg// mul1e lte_fin x0 lte_pinfty.
- by move=> _ _; rewrite mule_pinfty_pinfty lte_pinfty.
Qed.

Lemma gt0_mulpinfty x : (0 < x -> +oo * x = +oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mule_pinfty_pinfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulpinfty x : (x < 0 -> +oo * x = -oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mule_pinfty_ninfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty ltr0_sg// mulN1e.
Qed.

Lemma gt0_mulninfty x : (0 < x -> -oo * x = -oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mule_ninfty_pinfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulninfty x : (x < 0 -> -oo * x = +oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mule_ninfty_ninfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty ltr0_sg// mulN1e.
Qed.

Lemma mule_eq_pinfty x y : (x * y == +oo) =
  [|| (x > 0) && (y == +oo), (x < 0) && (y == -oo),
     (x == +oo) && (y > 0) | (x == -oo) && (y < 0)].
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_fin,andbF,andbT,orbF,eqxx,andbT)//=.
- by rewrite mulrpinfty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulrninfty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulpinftyr; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_pinfty_pinfty lte_pinfty.
- by rewrite mule_pinfty_ninfty.
- by rewrite mulninftyr; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mule_ninfty_pinfty.
- by rewrite lte_ninfty.
Qed.

Lemma mule_eq_ninfty x y : (x * y == -oo) =
  [|| (x > 0) && (y == -oo), (x < 0) && (y == +oo),
     (x == -oo) && (y > 0) | (x == +oo) && (y < 0)].
Proof.
have := mule_eq_pinfty x (- y); rewrite muleN eqe_oppLR => ->.
by rewrite !eqe_oppLR lte_oppr lte_oppl oppe0 (orbC _ ((x == -oo) && _)).
Qed.

Lemma lte_opp x y : (- x < - y) = (y < x).
Proof. by rewrite lte_oppl oppeK. Qed.

Lemma lte_add a b x y : a < b -> x < y -> a + x < b + y.
Proof.
move: a b x y=> [a| |] [b| |] [x| |] [y| |]; rewrite ?(lte_pinfty,lte_ninfty)//.
by rewrite !lte_fin; exact: ltr_add.
Qed.

Lemma lee_addl x y : 0 <= y -> x <= x + y.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ler_addl | move=> _; exact: lee_pinfty].
Qed.

Lemma lee_addr x y : 0 <= y -> x <= y + x.
Proof. by rewrite addeC; exact: lee_addl. Qed.

Lemma gee_addl x y : y <= 0 -> x + y <= x.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ger_addl | move=> _; exact: lee_ninfty].
Qed.

Lemma gee_addr x y : y <= 0 -> y + x <= x.
Proof. rewrite addeC; exact: gee_addl. Qed.

Lemma lte_addl y x : y \is a fin_num -> 0 < x -> y < y + x.
Proof.
by move: x y => [x| |] [y| |] _ //;
  rewrite ?lte_pinfty ?lte_ninfty // !lte_fin ltr_addl.
Qed.

Lemma lte_addr y x : y \is a fin_num -> 0 < x -> y < x + y.
Proof. rewrite addeC; exact: lte_addl. Qed.

Lemma gte_subl y x : y \is a fin_num -> 0 < x -> y - x < y.
Proof.
move: y x => [x| |] [y| |] _ //; rewrite addeC /= ?lte_ninfty //.
by rewrite !lte_fin gtr_addr ltr_oppl oppr0.
Qed.

Lemma gte_subr y x : y \is a fin_num -> 0 < x -> - x + y < y.
Proof. rewrite addeC; exact: gte_subl. Qed.

Lemma lte_add2lE x a b : x \is a fin_num -> (x + a < x + b) = (a < b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(lte_pinfty, lte_ninfty) //.
by rewrite !lte_fin ltr_add2l.
Qed.

Lemma lee_add2l x a b : a <= b -> x + a <= x + b.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
- by rewrite !lee_fin ler_add2l.
- move=> r _; exact: lee_pinfty.
- move=> -[b [|  |]// | []// | //] r oob; exact: lee_ninfty.
Qed.

Lemma lee_add2lE x a b : x \is a fin_num -> (x + a <= x + b) = (a <= b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(lee_pinfty, lee_ninfty) //.
by rewrite !lee_fin ler_add2l.
Qed.

Lemma lee_add2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite addeC (addeC b); exact: lee_add2l. Qed.

Lemma lee_add a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof.
move: a b x y => [a| |] [b| |] [x| |] [y| |]; rewrite ?(lee_pinfty,lee_ninfty)//.
by rewrite !lee_fin; exact: ler_add.
Qed.

Lemma lte_le_add a b x y : a \is a fin_num -> b \is a fin_num ->
  a < x -> b <= y -> a + b < x + y.
Proof.
move: x y a b => [x| |] [y| |] [a| |] [b| |] _ _ //=;
  rewrite ?(lte_pinfty,lte_ninfty)//.
by rewrite !lte_fin; exact: ltr_le_add.
Qed.

Lemma lee_sub x y z u : x <= y -> u <= z -> x - z <= y - u.
Proof.
move: x y z u => -[x| |] -[y| |] -[z| |] -[u| |] //=;
  rewrite ?(lee_pinfty,lee_ninfty)//.
by rewrite !lee_fin; exact: ler_sub.
Qed.

Lemma lte_le_sub z u x y : z \is a fin_num -> u \is a fin_num ->
  x < z -> u <= y -> x - y < z - u.
Proof.
move: z u => [z| |] [u| |] _ _ //.
move: x y => [x| |] [y| |]; rewrite ?(lte_pinfty,lte_ninfty)//.
by rewrite !lte_fin => xltr tley; apply: ltr_le_add; rewrite // ler_oppl opprK.
Qed.

Lemma lte_pmul2r z : z \is a fin_num -> 0 < z -> {mono *%E^~ z : x y / x < y}.
Proof.
move: z => [z| |] _ // z0 [x| |] [y| |] //.
- by rewrite !lte_fin ltr_pmul2r.
- by rewrite mulrinfty gtr0_sg// mul1e 2!lte_pinfty.
- by rewrite mulrinfty gtr0_sg// mul1e ltNge lee_ninfty ltNge lee_ninfty.
- by rewrite mulrinfty gtr0_sg// mul1e ltNge lee_pinfty ltNge lee_pinfty.
- by rewrite mulrinfty gtr0_sg// mul1e mulrinfty gtr0_sg// mul1e.
- by rewrite mulrinfty gtr0_sg// mul1e 2!lte_ninfty.
- by rewrite mulrinfty gtr0_sg// mul1e mulrinfty gtr0_sg// mul1e.
Qed.

Lemma lte_pmul2l z : z \is a fin_num -> 0 < z -> {mono *%E z : x y / x < y}.
Proof. by move=> zfin z0 x y; rewrite 2!(muleC z) lte_pmul2r. Qed.

Lemma lte_nmul2l z : z \is a fin_num -> z < 0 -> {mono *%E z : x y /~ x < y}.
Proof.
rewrite -oppe0 lte_oppr => zfin z0 x y.
by rewrite -(oppeK z) !mulNe lte_oppl oppeK -2!mulNe lte_pmul2l ?fin_numN.
Qed.

Lemma lte_nmul2r z : z \is a fin_num -> z < 0 -> {mono *%E^~ z : x y /~ x < y}.
Proof. by move=> zfin z0 x y; rewrite -!(muleC z) lte_nmul2l. Qed.

Lemma lee_sum I (f g : I -> \bar R) s (P : pred I) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i) g i.
Proof. by move=> Pfg; elim/big_ind2 : _ => // *; apply lee_add. Qed.

Lemma lee_sum_nneg_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, 0 <= f i} ->
  \sum_(i <- s | Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [X in _ <= X]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_npos_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, f i <= 0} ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | Q i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [X in _ <= X]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> 0 <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite [X in _ <= X](bigID Q) /= -[X in X <= _]adde0 lee_add //.
by rewrite sume_ge0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_npos (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> f i <= 0) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i && Q i) f i.
Proof.
move=> PQf; rewrite [X in X <= _](bigID Q) /= -[X in _ <= X]adde0 lee_add //.
by rewrite sume_le0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_nneg_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= f n) ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite (big_ord_widen_cond j) // big_mkcondr /=.
by rewrite lee_sum // => k ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_npos_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> f n <= 0)%E ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 m n ?; rewrite [X in _ <= X](big_ord_widen_cond n) // big_mkcondr /=.
rewrite lee_sum // => i ?; case: ifP => // _; exact: f0.
Qed.

Lemma lee_sum_nneg_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= f n) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_nneg_ord (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma lee_sum_npos_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> f n <= 0) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite -[m]add0n !big_addn !big_mkord.
apply: (@lee_sum_npos_ord (fun k => f (k + m)%N) (fun k => P (k + m)%N));
  by [move=> n /f0; apply; rewrite leq_addl | rewrite leq_sub2r].
Qed.

Lemma lee_sum_nneg_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> 0 <= f m) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !big_geq_mkord/=.
rewrite lee_sum_nneg_subset// => [k | k /and3P[_ /f0->//]].
by rewrite ?inE -!topredE/= => /andP[-> /(leq_trans le_ij)->].
Qed.

Lemma lee_sum_npos_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> f m <= 0) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !big_geq_mkord/=.
rewrite lee_sum_npos_subset// => [k | k /and3P[_ /f0->//]].
by rewrite ?inE -!topredE/= => /andP[-> /(leq_trans le_ij)->].
Qed.

Lemma lee_sum_nneg_subfset (T : choiceType) (A B : {fset T}%fset) (P : pred T)
  (f : T -> \bar R) : {subset A <= B} ->
  {in [predD B & A], forall t, P t -> 0 <= f t} ->
  \sum_(t <- A | P t) f t <= \sum_(t <- B | P t) f t.
Proof.
move=> AB f0; rewrite [X in _ <= X]big_mkcond (big_fsetID _ (mem A) B) /=.
rewrite -[X in X <= _]adde0 lee_add //.
  rewrite -big_mkcond /= {1}(_ : A = [fset x in B | x \in A]%fset) //.
  by apply/fsetP=> t; rewrite !inE /= andbC; case: (boolP (_ \in _)) => // /AB.
rewrite big_fset /= big_seq_cond sume_ge0 // => t /andP[tB tA].
by case: ifPn => // Pt; rewrite f0 // !inE tA.
Qed.

Lemma lee_sum_npos_subfset (T : choiceType) (A B : {fset T}%fset) (P : pred T)
  (f : T -> \bar R) : {subset A <= B} ->
  {in [predD B & A], forall t, P t -> f t <= 0} ->
  \sum_(t <- B | P t) f t <= \sum_(t <- A | P t) f t.
Proof.
move=> AB f0; rewrite big_mkcond (big_fsetID _ (mem A) B) /=.
rewrite -[X in _ <= X]adde0 lee_add //.
  rewrite -big_mkcond /= {3}(_ : A = [fset x in B | x \in A]%fset) //.
  by apply/fsetP=> t; rewrite !inE /= andbC; case: (boolP (_ \in _)) => // /AB.
rewrite big_fset /= big_seq_cond sume_le0 // => t /andP[tB tA].
by case: ifPn => // Pt; rewrite f0 // !inE tA.
Qed.

Lemma lte_subl_addr x y z : y \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_subl_addr.
Qed.

Lemma lte_subl_addl x y z : x \is a fin_num -> (x - y < z) = (x < y + z).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subl_addl.
Qed.

Lemma lte_subr_addr x y z : x \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subr_addr.
Qed.

Lemma lee_subr_addr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?lee_ninfty ?lee_pinfty //.
by rewrite !lee_fin ler_subr_addr.
Qed.

Lemma lee_subl_addr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_subl_addr.
Qed.

Lemma lte_suble_addr x y z : x \is a fin_num -> z \is a fin_num ->
  (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_subl_addr.
Qed.

Lemma lte_suble_addl x y z : y \is a fin_num -> z \is a fin_num ->
  (x - y < z) = (x < y + z).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subl_addl.
Qed.

Lemma lte_subre_addr x y z : y \is a fin_num -> z \is a fin_num ->
  (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lte_ninfty ?lte_pinfty //.
by rewrite !lte_fin ltr_subr_addr.
Qed.

Lemma lee_subre_addr x y z : x \is a fin_num -> y \is a fin_num ->
  (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?lee_ninfty ?lee_pinfty //.
by rewrite !lee_fin ler_subr_addr.
Qed.

Lemma lee_suble_addr x y z : x \is a fin_num -> z \is a fin_num ->
  (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?lee_pinfty ?lee_ninfty //.
by rewrite !lee_fin ler_subl_addr.
Qed.

Lemma pmule_rge0 x y : 0 < x -> (x * y >= 0) = (y >= 0).
Proof.
move=> x_gt0; apply/idP/idP; last exact/mule_ge0/ltW.
by apply: contra_le; apply: mule_gt0_lt0.
Qed.

Lemma pmule_lge0 x y : 0 < x -> (y * x >= 0) = (y >= 0).
Proof. by rewrite muleC; apply: pmule_rge0. Qed.

Lemma pmule_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. by move=> /pmule_rge0; rewrite !ltNge => ->. Qed.

Lemma pmule_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by rewrite muleC; apply: pmule_rlt0. Qed.

Lemma pmule_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof. by move=> xgt0; rewrite -oppe_ge0 -muleN pmule_rge0 ?oppe_ge0. Qed.

Lemma pmule_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by rewrite muleC; apply: pmule_rle0. Qed.

Lemma pmule_rgt0 x y : 0 < x -> (x * y > 0) = (y > 0).
Proof. by move=> xgt0; rewrite -oppe_lt0 -muleN pmule_rlt0 ?oppe_lt0. Qed.

Lemma pmule_lgt0 x y : 0 < x -> (y * x > 0) = (y > 0).
Proof. by rewrite muleC; apply: pmule_rgt0. Qed.

Lemma nmule_rge0 x y : x < 0 -> (x * y >= 0) = (y <= 0).
Proof. by rewrite -oppe_gt0 => /pmule_rle0<-; rewrite mulNe oppe_le0. Qed.

Lemma nmule_lge0 x y : x < 0 -> (y * x >= 0) = (y <= 0).
Proof. by rewrite muleC; apply: nmule_rge0. Qed.

Lemma nmule_rle0 x y : x < 0 -> (x * y <= 0) = (y >= 0).
Proof. by rewrite -oppe_gt0 => /pmule_rge0<-; rewrite mulNe oppe_ge0. Qed.

Lemma nmule_lle0 x y : x < 0 -> (y * x <= 0) = (y >= 0).
Proof. by rewrite muleC; apply: nmule_rle0. Qed.

Lemma nmule_rgt0 x y : x < 0 -> (x * y > 0) = (y < 0).
Proof. by rewrite -oppe_gt0 => /pmule_rlt0<-; rewrite mulNe oppe_lt0. Qed.

Lemma nmule_lgt0 x y : x < 0 -> (y * x > 0) = (y < 0).
Proof. by rewrite muleC; apply: nmule_rgt0. Qed.

Lemma nmule_rlt0 x y : x < 0 -> (x * y < 0) = (y > 0).
Proof. by rewrite -oppe_gt0 => /pmule_rgt0<-; rewrite mulNe oppe_gt0. Qed.

Lemma nmule_llt0 x y : x < 0 -> (y * x < 0) = (y > 0).
Proof. by rewrite muleC; apply: nmule_rlt0. Qed.

Lemma mule_lt0 x y : (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof.
have [xlt0|xgt0|->] := ltgtP x 0; last by rewrite mul0e.
  by rewrite nmule_rlt0//= -leNgt lt_def.
by rewrite pmule_rlt0//= !lt_neqAle andbA andbb.
Qed.

Lemma muleA : associative ( *%E : \bar R -> \bar R -> \bar R ).
Proof.
move=> [x||] [y||] [z||] //;
  rewrite /mule/mule_subdef/= ?(lte_pinfty,eqe,lte_fin,mulrA)//=.
- case: ltrgtP => [y0|y0|<-{y}]; last by rewrite mulr0 eqxx.
    case: ltrgtP => [x0|x0|<-{x}]; last by rewrite mul0r eqxx.
      by rewrite gt_eqF mulr_gt0.
    by rewrite lt_eqF ?nmulr_rlt0// nmulr_rgt0// ltNge (ltW y0).
  case: ltrgtP => [x0|x0|<-{x}]; last by rewrite mul0r eqxx.
    by rewrite lt_eqF ?nmulr_llt0// nmulr_lgt0// ltNge (ltW x0).
  by rewrite gt_eqF ?nmulr_rgt0// y0.
- case: ltrgtP => [y0|y0|<-{y}]; last by rewrite mulr0 eqxx.
    case: ltrgtP => [x0|x0|<-{x}]; last by rewrite mul0r eqxx.
      by rewrite gt_eqF mulr_gt0.
    by rewrite lt_eqF ?nmulr_rlt0// nmulr_rgt0// ltNge (ltW y0).
  case: ltrgtP => [x0|x0|<-{x}]; last by rewrite mul0r eqxx.
    by rewrite lt_eqF ?nmulr_llt0// nmulr_lgt0// ltNge (ltW x0).
  by rewrite gt_eqF ?nmulr_rgt0// y0.
- case: ltrgtP => [z0|z0|<-{z}]; try
    by case: ltrgtP => [x0|x0|_] //; rewrite mul0r.
  by case: ltrgtP; rewrite !mulr0.
- by case: ltrgtP => //=; rewrite ?lte_pinfty// eqxx.
- by case: ltrgtP => /=; rewrite ?lte_pinfty// eqxx.
- case: ltrgtP => //= [z0|z0|<-{z}]; try by case: ltrgtP => //=; rewrite mul0r.
  by case: ltrgtP; rewrite !mulr0.
- by case: ltrgtP => //=; rewrite ?lte_pinfty ?eqxx.
- by case: ltrgtP => //=; rewrite ?lte_pinfty ?eqxx.
- case: (ltrgtP 0 y) => [y0/=|y0/=|<-{y}]; last by rewrite mul0r eqxx.
    case: (ltrgtP 0 z) => [z0/=|z0|<-{z}]; last by rewrite mulr0 eqxx.
      by rewrite (negbTE (mulf_neq0 _ _)) ?gt_eqF // mulr_gt0// lte_fin z0.
    by rewrite lt_eqF ?nmulr_llt0// ltNge nmulr_lle0// (ltW y0).
  case: (ltrgtP 0 z) => [z0/=|z0|<-{z}]; last by rewrite mulr0 eqxx.
    by rewrite lt_eqF ?nmulr_rlt0// ltNge nmulr_rle0// (ltW z0).
  by rewrite gt_eqF nmulr_lgt0// y0.
- by case: ltrgtP => //=; rewrite lte_pinfty.
- by case: ltrgtP; rewrite /= ?lte_pinfty// eqxx.
- by case: ltrgtP; rewrite /= ?lte_pinfty// eqxx.
- by case: ltrgtP; rewrite /= ?lte_pinfty// eqxx.
- case: (ltrgtP 0 y) => [y0/=|y0/=|<-{y}]; last by rewrite mul0r eqxx.
    case: (ltrgtP 0 z) => [z0/=|z0|<-{z}]; last by rewrite mulr0 eqxx.
      by rewrite (negbTE (mulf_neq0 _ _)) ?gt_eqF // mulr_gt0// lte_fin z0.
    by rewrite lt_eqF ?nmulr_llt0// ltNge nmulr_lle0// (ltW y0).
  case: (ltrgtP 0 z) => [z0/=|z0|<-{z}]; last by rewrite mulr0 eqxx.
    by rewrite lt_eqF ?nmulr_rlt0// ltNge nmulr_rle0// (ltW z0).
  by rewrite gt_eqF nmulr_lgt0// y0.
- by case: ltrgtP; rewrite ?eqxx// ?mul0e//= lte_pinfty.
- by case: ltrgtP.
- by case: ltrgtP => //= [z0|z0]; rewrite ?eqxx// lte_pinfty.
- by case: ltrgtP; rewrite ?eqxx// lte_pinfty.
Qed.

Local Open Scope ereal_scope.

Lemma muleDr x y z : x \is a fin_num -> y +? z -> x * (y + z) = x * y + x * z.
Proof.
rewrite /mule/=; move: x y z => [x| |] [y| |] [z| |] //= _; try
  (by case: ltgtP => // -[] <-; rewrite ?(mul0r,add0r,adde0))
  || (by case: ltgtP => //; rewrite adde0).
by rewrite mulrDr.
Qed.

Lemma muleDl x y z : x \is a fin_num -> y +? z -> (y + z) * x = y * x + z * x.
Proof. by move=> ? ?; rewrite -!(muleC x) muleDr. Qed.

Lemma muleBr x y z : x \is a fin_num -> y +? - z -> x * (y - z) = x * y - x * z.
Proof. by move=> ? yz; rewrite muleDr ?muleN. Qed.

Lemma muleBl x y z : x \is a fin_num -> y +? - z -> (y - z) * x = y * x - z * x.
Proof. by move=> ? yz; rewrite muleDl// mulNe. Qed.

Lemma ge0_muleDl x y z : 0 <= y -> 0 <= z -> (y + z) * x = y * x + z * x.
Proof.
rewrite /mule/=; move: x y z => [r| |] [s| |] [t| |] //= s0 t0.
- by rewrite mulrDl.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => //; rewrite adde0.
- rewrite !eqe paddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite lte_fin -[in LHS](addr0 0%R) ltr_le_add // lte_fin s0.
    by case: ltgtP t0 => // [t0|[<-{t}]] _; [rewrite gt_eqF|rewrite eqxx].
  + by move: t0; rewrite lee_fin; case: (ltgtP t).
- by rewrite lte_pinfty; case: ltgtP s0.
- by rewrite lte_pinfty; case: ltgtP t0.
- by rewrite lte_pinfty.
- rewrite !eqe paddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite lte_fin -[in LHS](addr0 0%R) ltr_le_add // lte_fin s0.
    by case: ltgtP t0 => // [t0|[<-{t}]].
  + by move: t0; rewrite lee_fin; case: (ltgtP t).
- by rewrite lte_pinfty; case: ltgtP s0.
- by rewrite lte_pinfty; case: ltgtP s0.
- by rewrite lte_pinfty; case: ltgtP s0.
Qed.

Lemma ge0_muleDr x y z : 0 <= y -> 0 <= z -> x * (y + z) = x * y + x * z.
Proof. by move=> y0 z0; rewrite !(muleC x) ge0_muleDl. Qed.

Lemma le0_muleDl x y z : y <= 0 -> z <= 0 -> (y + z) * x = y * x + z * x.
Proof.
rewrite /mule/=; move: x y z => [r| |] [s| |] [t| |] //= s0 t0.
- by rewrite mulrDl.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => // -[] <-; rewrite mulr0 adde0.
- by case: ltgtP => //; rewrite adde0.
- rewrite !eqe naddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite !lte_fin -[in LHS](addr0 0%R) ltNge ler_add // ?ltW //=.
    by rewrite !ltNge ltW //.
  + by case: (ltgtP t).
- by rewrite lte_pinfty; case: ltgtP s0.
- by rewrite lte_pinfty; case: ltgtP t0.
- by rewrite lte_pinfty.
- rewrite !eqe naddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite !lte_fin -[in LHS](addr0 0%R) ltNge ler_add // ?ltW //=.
    by rewrite !ltNge ltW // -lee_fin t0; case: eqP.
  + by case: (ltgtP t).
- by rewrite ltNge s0 /=; case: eqP.
- by rewrite ltNge t0 /=; case: eqP.
Qed.

Lemma le0_muleDr x y z : y <= 0 -> z <= 0 -> x * (y + z) = x * y + x * z.
Proof. by move=> y0 z0; rewrite !(muleC x) le0_muleDl. Qed.

Lemma gee_pmull y x : y \is a fin_num -> 0 < x -> y <= 1 -> y * x <= x.
Proof.
move: x y => [x| |] [y| |] _ //=.
- by rewrite lte_fin => x0 r0; rewrite /mule/= lee_fin ger_pmull.
- by move=> _; rewrite /mule/= eqe => r1; rewrite lee_pinfty.
Qed.

Lemma lee_wpmul2r x : 0 <= x -> {homo *%E^~ x : y z / y <= z}.
Proof.
move: x => [x|_|//].
  rewrite lee_fin le_eqVlt => /predU1P[<- y z|x0]; first by rewrite 2!mule0.
  move=> [y| |] [z| |]//; first by rewrite !lee_fin// ler_pmul2r.
  - by move=> _; rewrite mulrinfty gtr0_sg// mul1e lee_pinfty.
  - by move=> _; rewrite mulrinfty gtr0_sg// mul1e lee_ninfty.
  - by move=> _; rewrite 2!mulrinfty gtr0_sg// 2!mul1e.
move=> [y| |] [z| |]//.
- rewrite lee_fin => yz.
  have [z0|z0|] := ltgtP 0%R z.
  + by rewrite [in X in _ <= X]mulrinfty gtr0_sg// mul1e lee_pinfty.
  + rewrite mulrinfty ltr0_sg// ?(le_lt_trans yz)//=.
    by rewrite [in X in _ <= X]mulrinfty ltr0_sg.
  + move=> z0; move: yz; rewrite -z0 mul0e le_eqVlt => /predU1P[->|y0].
      by rewrite mul0e.
    by rewrite mulrinfty ltr0_sg// mulN1e lee_ninfty.
  + by move=> _; rewrite mule_pinfty_pinfty lee_pinfty.
  + by move=> _; rewrite mule_ninfty_pinfty lee_ninfty.
  + by move=> _; rewrite mule_ninfty_pinfty lee_ninfty.
Qed.

Lemma ge0_sume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
elim: s x P F => [x P F F0|h t ih x P F F0]; first by rewrite 2!big_nil mul0e.
rewrite big_cons; case: ifPn => Ph; last by rewrite big_cons (negbTE Ph) ih.
by rewrite ge0_muleDl ?sume_ge0// ?F0// ih// big_cons Ph.
Qed.

Lemma ge0_sume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC ge0_sume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma le0_sume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
elim: s x P F => [x P F F0|h t ih x P F F0]; first by rewrite 2!big_nil mul0e.
rewrite big_cons; case: ifPn => Ph; last by rewrite big_cons (negbTE Ph) ih.
by rewrite le0_muleDl ?sume_le0// ?F0// ih// big_cons Ph.
Qed.

Lemma le0_sume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC le0_sume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma eq_infty x : (forall r, r%:E <= x) -> x = +oo.
Proof.
case: x => [x /(_ (x + 1)%R)|//|/(_ 0%R)//].
by rewrite EFinD addeC -lee_subr_addr// subee// lee_fin ler10.
Qed.

Lemma eq_ninfty x : (forall r, x <= r%:E) -> x = -oo.
Proof.
move=> *; apply: (can_inj oppeK); apply: eq_infty => r.
by rewrite lee_oppr -EFinN.
Qed.

Lemma lee_opp x y : (- x <= - y) = (y <= x).
Proof. by rewrite lee_oppl oppeK. Qed.

Lemma lee_abs x : x <= `|x|.
Proof. by move: x => [x| |]//=; rewrite lee_fin ler_norm. Qed.

Lemma abse_id x : `| `|x| | = `|x|.
Proof. by move: x => [x| |] //=; rewrite normr_id. Qed.

Lemma preimage_abse_ninfty : (@abse R @^-1` [set -oo])%classic = set0.
Proof.
rewrite predeqE => t; split => //=; apply/eqP.
by rewrite gt_eqF// (lt_le_trans _ (abse_ge0 t))// lte_ninfty.
Qed.

Lemma lte_absl (x y : \bar R) : (`|x| < y)%E = (- y < x < y)%E.
Proof.
move: x y => [x| |] [y| |] //=; rewrite ?lte_fin ?lte_pinfty ?lte_ninfty//.
by rewrite ltr_norml.
Qed.

Lemma eqe_absl x y : (`|x| == y) = ((x == y) || (x == - y)) && (0 <= y).
Proof.
move: x y => [x| |] [y| |] //=; rewrite? lee_pinfty//.
by rewrite !eqe eqr_norml lee_fin.
Qed.

Lemma lee_abs_add x y : `|x + y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -EFinD lee_fin ler_norm_add.
Qed.

Lemma lee_abs_sum (I : Type) (s : seq I) (F : I -> \bar R) (P : pred I) :
  `|\sum_(i <- s | P i) F i| <= \sum_(i <- s | P i) `|F i|.
Proof.
elim/big_ind2 : _ => //; first by rewrite abse0.
by move=> *; exact/(le_trans (lee_abs_add _ _) (lee_add _ _)).
Qed.

Lemma lee_abs_sub x y : `|x - y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -EFinD lee_fin ler_norm_sub.
Qed.

Lemma abseM : {morph @abse R : x y / x * y}.
Proof.
have xoo r : `|r%:E * +oo| = `|r|%:E * +oo.
  have [r0|r0] := leP 0%R r.
    by rewrite (ger0_norm r0)// gee0_abs// mule_ge0// lee_pinfty.
  rewrite (ltr0_norm r0)// lte0_abs// ?EFinN ?mulNe//.
  by rewrite mule_lt0 /= eqe lt_eqF//= lte_fin r0.
move=> [x| |] [y| |] //=; first by rewrite normrM.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite muleC xoo muleC.
- by rewrite mule_pinfty_pinfty.
- by rewrite mule_pinfty_pinfty mule_pinfty_ninfty.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite mule_pinfty_pinfty mule_ninfty_pinfty.
- by rewrite mule_pinfty_pinfty.
Qed.

Lemma maxEFin r1 r2 : maxe r1%:E r2%:E = (Num.max r1 r2)%:E.
Proof.
by have [ab|ba] := leP r1 r2;
  [apply/max_idPr; rewrite lee_fin|apply/max_idPl; rewrite lee_fin ltW].
Qed.

Lemma minEFin r1 r2 : mine r1%:E r2%:E = (Num.min r1 r2)%:E.
Proof.
by have [ab|ba] := leP r1 r2;
  [apply/min_idPl; rewrite lee_fin|apply/min_idPr; rewrite lee_fin ltW].
Qed.

Lemma adde_maxl : left_distributive (@adde R) maxe.
Proof.
move=> x y z; have [xy|yx] := leP x y.
by apply/esym/max_idPr; rewrite lee_add2r.
by apply/esym/max_idPl; rewrite lee_add2r// ltW.
Qed.

Lemma adde_maxr : right_distributive (@adde R) maxe.
Proof.
move=> x y z; have [yz|zy] := leP y z.
by apply/esym/max_idPr; rewrite lee_add2l.
by apply/esym/max_idPl; rewrite lee_add2l// ltW.
Qed.

Lemma maxe_pinftyl : left_zero (+oo : \bar R) maxe.
Proof. by move=> x; have [|//] := leP +oo x; rewrite lee_pinfty_eq => /eqP. Qed.

Lemma maxe_pinftyr : right_zero (+oo : \bar R) maxe.
Proof. by move=> x; rewrite maxC maxe_pinftyl. Qed.

Lemma maxe_ninftyl : left_id (-oo : \bar R) maxe.
Proof. by move=> x; have [//|] := leP -oo x; rewrite ltNge lee_ninfty. Qed.

Lemma maxe_ninftyr : right_id (-oo : \bar R) maxe.
Proof. by move=> x; rewrite maxC maxe_ninftyl. Qed.

Lemma mine_ninftyl : left_zero (-oo : \bar R) mine.
Proof. by move=> x; have [|//] := leP x -oo; rewrite lee_ninfty_eq => /eqP. Qed.

Lemma mine_ninftyr : right_zero (-oo : \bar R) mine.
Proof. by move=> x; rewrite minC mine_ninftyl. Qed.

Lemma mine_pinftyl : left_id (+oo : \bar R) mine.
Proof. by move=> x; have [//|] := leP x +oo; rewrite ltNge lee_pinfty. Qed.

Lemma mine_pinftyr : right_id (+oo : \bar R) mine.
Proof. by move=> x; rewrite minC mine_pinftyl. Qed.

Lemma oppe_max : {morph -%E : x y / maxe x y >-> mine x y : \bar R}.
Proof.
move=> [x| |] [y| |] //=.
- by rewrite maxEFin minEFin -EFinN oppr_max.
- by rewrite maxe_pinftyr mine_ninftyr.
- by rewrite mine_pinftyr.
- by rewrite mine_ninftyl.
- by rewrite maxe_ninftyl mine_pinftyl.
Qed.

Lemma oppe_min : {morph -%E : x y / mine x y >-> maxe x y : \bar R}.
Proof. by move=> x y; rewrite -[RHS]oppeK oppe_max !oppeK. Qed.

Lemma maxeMr z x y : z \is a fin_num -> 0 < z ->
  z * maxe x y = maxe (z * x) (z * y).
Proof.
move=> + r0; have [xy|yx|->] := ltgtP x y; last by rewrite maxxx.
- by move=> zfin; rewrite /maxe lte_pmul2l // xy.
- by move=> zfin; rewrite maxC /maxe lte_pmul2l// yx.
Qed.

Lemma maxeMl z x y : z \is a fin_num -> 0 < z ->
  maxe x y * z = maxe (x * z) (y * z).
Proof. by move=> zfin z0; rewrite muleC maxeMr// !(muleC z). Qed.

Lemma mineMr z x y : z \is a fin_num -> 0 < z ->
  z * mine x y = mine (z * x) (z * y).
Proof.
by move=> ? ?; rewrite -eqe_oppP -muleN oppe_min maxeMr// !muleN -oppe_min.
Qed.

Lemma mineMl z x y : z \is a fin_num -> 0 < z ->
  mine x y * z = mine (x * z) (y * z).
Proof. by move=> zfin z0; rewrite muleC mineMr// !(muleC z). Qed.

Lemma lee_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof.
move: x y => [x| |] [y| |] //; last by rewrite mule_pinfty_pinfty.
- by rewrite -EFinM 3!lee_fin; exact: ler_pemull.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulrinfty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[<- _|y0 _]; first by rewrite mule0.
  by rewrite mulrinfty gtr0_sg// mul1e lee_pinfty.
Qed.

Lemma lee_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof.
move: x y => [x| |] [y| |] //; last by rewrite mule_pinfty_ninfty.
- by rewrite -EFinM 3!lee_fin; exact: ler_nemull.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulrinfty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[-> _|y0 _]; first by rewrite mule0.
  by rewrite mulrinfty ltr0_sg// mulN1e lee_ninfty.
Qed.

Lemma lee_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> y0 x1; rewrite muleC lee_pemull. Qed.

Lemma lee_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> y0 x1; rewrite muleC lee_nemull. Qed.

End ERealArithTh_realDomainType.
Arguments lee_sum_nneg_ord {R}.
Arguments lee_sum_npos_ord {R}.
Arguments lee_sum_nneg_natr {R}.
Arguments lee_sum_npos_natr {R}.
Arguments lee_sum_nneg_natl {R}.
Arguments lee_sum_npos_natl {R}.
#[global] Hint Extern 0 (is_true (0 <= `| _ |)%E) => solve [apply: abse_ge0] : core.

Module DualAddTheoryRealDomain.

Section DualERealArithTh_realDomainType.

Import DualAddTheoryNumDomain.

Local Open Scope ereal_dual_scope.

Context {R : realDomainType}.
Implicit Types x y z a b : \bar R.

Lemma dsube_lt0 x y : (x - y < 0) = (x < y).
Proof. by rewrite dual_addeE oppe_lt0 sube_gt0 lte_opp. Qed.

Lemma dsube_ge0 x y : (0 <= y - x) = (x <= y).
Proof. by rewrite dual_addeE oppe_ge0 sube_le0 lee_opp. Qed.

Lemma dsuber_le0 x y : y \is a fin_num -> (x - y <= 0) = (x <= y).
Proof.
by move=> ?; rewrite dual_addeE oppe_le0 suber_ge0 ?fin_numN// lee_opp.
Qed.

Lemma dsubre_le0 y x : y \is a fin_num -> (y - x <= 0) = (y <= x).
Proof.
by move=> ?; rewrite dual_addeE oppe_le0 subre_ge0 ?fin_numN// lee_opp.
Qed.

Lemma lte_dadd a b x y : a < b -> x < y -> a + x < b + y.
Proof. rewrite !dual_addeE lte_opp -lte_opp -(lte_opp y); exact: lte_add. Qed.

Lemma lee_daddl x y : 0 <= y -> x <= x + y.
Proof. rewrite dual_addeE lee_oppr -oppe_le0; exact: gee_addl. Qed.

Lemma lee_daddr x y : 0 <= y -> x <= y + x.
Proof. rewrite dual_addeE lee_oppr -oppe_le0; exact: gee_addr. Qed.

Lemma gee_daddl x y : y <= 0 -> x + y <= x.
Proof. rewrite dual_addeE lee_oppl -oppe_ge0; exact: lee_addl. Qed.

Lemma gee_daddr x y : y <= 0 -> y + x <= x.
Proof. rewrite dual_addeE lee_oppl -oppe_ge0; exact: lee_addr. Qed.

Lemma lte_daddl y x : y \is a fin_num -> 0 < x -> y < y + x.
Proof. rewrite -fin_numN dual_addeE lte_oppr => ? ?; exact: gte_subl. Qed.

Lemma lte_daddr y x : y \is a fin_num -> 0 < x -> y < x + y.
Proof. rewrite -fin_numN dual_addeE lte_oppr addeC; exact: gte_subl. Qed.

Lemma gte_dsubl y x : y \is a fin_num -> 0 < x -> y - x < y.
Proof. rewrite -fin_numN dual_addeE lte_oppl oppeK; exact: lte_addl. Qed.

Lemma gte_dsubr y x : y \is a fin_num -> 0 < x -> - x + y < y.
Proof. rewrite -fin_numN dual_addeE lte_oppl oppeK; exact: lte_addr. Qed.

Lemma lte_dadd2lE x a b : x \is a fin_num -> (x + a < x + b) = (a < b).
Proof.
by move=> ?; rewrite !dual_addeE lte_opp lte_add2lE ?fin_numN// lte_opp.
Qed.

Lemma lee_dadd2l x a b : a <= b -> x + a <= x + b.
Proof. rewrite !dual_addeE lee_opp -lee_opp; exact: lee_add2l. Qed.

Lemma lee_dadd2lE x a b : x \is a fin_num -> (x + a <= x + b) = (a <= b).
Proof.
by move=> ?; rewrite !dual_addeE lee_opp lee_add2lE ?fin_numN// lee_opp.
Qed.

Lemma lee_dadd2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite !dual_addeE lee_opp -lee_opp; exact: lee_add2r. Qed.

Lemma lee_dadd a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof. rewrite !dual_addeE lee_opp -lee_opp -(lee_opp y); exact: lee_add. Qed.

Lemma lte_le_dadd a b x y : a \is a fin_num -> b \is a fin_num ->
  a < x -> b <= y -> a + b < x + y.
Proof. rewrite -fin_numN !dual_addeE lte_opp -lte_opp; exact: lte_le_sub. Qed.

Lemma lee_dsub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. rewrite !dual_addeE lee_oppl oppeK -lee_opp !oppeK; exact: lee_add. Qed.

Lemma lte_le_dsub z u x y : z \is a fin_num -> u \is a fin_num ->
  x < z -> u <= y -> x - y < z - u.
Proof.
rewrite -(fin_numN z) !dual_addeE lte_opp !oppeK -lte_opp; exact: lte_le_add.
Qed.

Lemma lee_dsum I (f g : I -> \bar R) s (P : pred I) :
  (forall i, P i -> f i <= g i) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i) g i.
Proof.
move=> Pfg; rewrite !dual_sumeE lee_opp.
apply: lee_sum => i Pi; rewrite lee_opp; exact: Pfg.
Qed.

Lemma lee_dsum_nneg_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, 0 <= f i} ->
  \sum_(i <- s | Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> QP PQf; rewrite !dual_sumeE lee_opp.
apply: lee_sum_npos_subset => [//|i iPQ]; rewrite oppe_le0; exact: PQf.
Qed.

Lemma lee_dsum_npos_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, f i <= 0} ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | Q i) f i.
Proof.
move=> QP PQf; rewrite !dual_sumeE lee_opp.
apply: lee_sum_nneg_subset => [//|i iPQ]; rewrite oppe_ge0; exact: PQf.
Qed.

Lemma lee_dsum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> 0 <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite !dual_sumeE lee_opp.
apply: lee_sum_npos => i Pi nQi; rewrite oppe_le0; exact: PQf.
Qed.

Lemma lee_dsum_npos (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> f i <= 0) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i && Q i) f i.
Proof.
move=> PQf; rewrite !dual_sumeE lee_opp.
apply: lee_sum_nneg => i Pi nQi; rewrite oppe_ge0; exact: PQf.
Qed.

Lemma lee_dsum_nneg_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= f n)%E ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 m n mlen; rewrite !dual_sumeE lee_opp.
apply: (lee_sum_npos_ord (fun i => - f i)%E) => [i Pi|//].
rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_ord (f : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> f n <= 0)%E ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 m n mlen; rewrite !dual_sumeE lee_opp.
apply: (lee_sum_nneg_ord (fun i => - f i)%E) => [i Pi|//].
rewrite oppe_ge0; exact: f0.
Qed.

Lemma lee_dsum_nneg_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= f n) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE lee_opp.
apply: lee_sum_npos_natr => [n ? ?|//]; rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_natr (f : nat -> \bar R) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> f n <= 0) ->
  {homo (fun n => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE lee_opp.
apply: lee_sum_nneg_natr => [n ? ?|//]; rewrite oppe_ge0; exact: f0.
Qed.

Lemma lee_dsum_nneg_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> 0 <= f m) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE lee_opp.
apply: lee_sum_npos_natl => [m ? ?|//]; rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_natl (f : nat -> \bar R) (P : pred nat) n :
  (forall m, (m < n)%N -> P m -> f m <= 0) ->
  {homo (fun m => \sum_(m <= i < n | P i) (f i)) : i j / (i <= j)%N >-> i <= j}.
Proof.
move=> f0 i j le_ij; rewrite !dual_sumeE lee_opp.
apply: lee_sum_nneg_natl => [m ? ?|//]; rewrite oppe_ge0; exact: f0.
Qed.

Lemma lee_dsum_nneg_subfset (T : choiceType) (A B : {fset T}%fset) (P : pred T)
  (f : T -> \bar R) : {subset A <= B} ->
  {in [predD B & A], forall t, P t -> 0 <= f t} ->
  \sum_(t <- A | P t) f t <= \sum_(t <- B | P t) f t.
Proof.
move=> AB f0; rewrite !dual_sumeE lee_opp.
apply: lee_sum_npos_subfset => [//|? ? ?]; rewrite oppe_le0; exact: f0.
Qed.

Lemma lee_dsum_npos_subfset (T : choiceType) (A B : {fset T}%fset) (P : pred T)
  (f : T -> \bar R) : {subset A <= B} ->
  {in [predD B & A], forall t, P t -> f t <= 0} ->
  \sum_(t <- B | P t) f t <= \sum_(t <- A | P t) f t.
Proof.
move=> AB f0; rewrite !dual_sumeE lee_opp.
apply: lee_sum_nneg_subfset => [//|? ? ?]; rewrite oppe_ge0; exact: f0.
Qed.

Lemma lte_dsubl_addr x y z : y \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr oppeK lte_subl_addr.
Qed.

Lemma lte_dsubl_addl x y z : z \is a fin_num -> (x - y < z) = (x < y + z).
Proof.
move=> zfin.
by rewrite !dual_addeE lte_oppl lte_oppr lte_subr_addr ?fin_numN// addeC.
Qed.

Lemma lte_dsubr_addr x y z : y \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move=> yfin.
by rewrite !dual_addeE lte_oppl lte_oppr lte_subl_addl ?fin_numN// addeC.
Qed.

Lemma lee_dsubr_addr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subl_addr ?fin_numN.
Qed.

Lemma lee_dsubl_addr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subr_addr ?fin_numN.
Qed.

Lemma lte_dsuble_addr x y z : x \is a fin_num -> z \is a fin_num ->
  (x - y < z) = (x < z + y).
Proof.
move=> xfin zfin.
by rewrite !dual_addeE lte_oppl lte_oppr oppeK lte_suble_addr// fin_numN.
Qed.

Lemma lte_dsuble_addl x y z : x \is a fin_num -> y \is a fin_num ->
  (x - y < z) = (x < y + z).
Proof.
move=> xfin yfin.
by rewrite !dual_addeE lte_oppl lte_oppr lte_subre_addr ?fin_numN// addeC.
Qed.

Lemma lte_dsubre_addr x y z : x \is a fin_num -> z \is a fin_num ->
  (x < y - z) = (x + z < y).
Proof.
move=> xfin zfin.
by rewrite !dual_addeE lte_oppl lte_oppr lte_suble_addl ?fin_numN// addeC.
Qed.

Lemma lee_dsubre_addr x y z : x \is a fin_num -> y \is a fin_num ->
  (x <= y - z) = (x + z <= y).
Proof.
by move=> ? ?; rewrite !dual_addeE lee_oppl lee_oppr lee_suble_addr ?fin_numN.
Qed.

Lemma lee_dsuble_addr x y z : x \is a fin_num -> z \is a fin_num ->
  (x - y <= z) = (x <= z + y).
Proof.
by move=> ? ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subre_addr ?fin_numN.
Qed.

Lemma dmuleDr x y z : x \is a fin_num -> y +? z -> x * (y + z) = x * y + x * z.
Proof. by move=> *; rewrite !dual_addeE muleN muleDr ?adde_defNN// !muleN. Qed.

Lemma dmuleDl x y z : x \is a fin_num -> y +? z -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite -!(muleC x) dmuleDr. Qed.

Lemma dge0_muleDl x y z : 0 <= y -> 0 <= z -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite !dual_addeE mulNe le0_muleDl ?oppe_le0 ?mulNe. Qed.

Lemma dge0_muleDr x y z : 0 <= y -> 0 <= z -> x * (y + z) = x * y + x * z.
Proof. by move=> *; rewrite !dual_addeE muleN le0_muleDr ?oppe_le0 ?muleN. Qed.

Lemma dle0_muleDl x y z : y <= 0 -> z <= 0 -> (y + z) * x = y * x + z * x.
Proof. by move=> *; rewrite !dual_addeE mulNe ge0_muleDl ?oppe_ge0 ?mulNe. Qed.

Lemma dle0_muleDr x y z : y <= 0 -> z <= 0 -> x * (y + z) = x * y + x * z.
Proof. by move=> *; rewrite !dual_addeE muleN ge0_muleDr ?oppe_ge0 ?muleN. Qed.

Lemma ge0_dsume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
move=> F0; rewrite !dual_sumeE !mulNe le0_sume_distrl => [|i Pi].
- by under eq_bigr => i _ do rewrite mulNe.
- by rewrite oppe_le0 F0.
Qed.

Lemma ge0_dsume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC ge0_dsume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma le0_dsume_distrl (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  (\sum_(i <- s | P i) F i) * x = \sum_(i <- s | P i) (F i * x).
Proof.
move=> F0; rewrite !dual_sumeE mulNe ge0_sume_distrl => [|i Pi].
- by under eq_bigr => i _ do rewrite mulNe.
- by rewrite oppe_ge0 F0.
Qed.

Lemma le0_dsume_distrr (I : Type) (s : seq I) x (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) (x * F i).
Proof.
by move=> F0; rewrite muleC le0_dsume_distrl//; under eq_bigr do rewrite muleC.
Qed.

Lemma lee_abs_dadd x y : `|x + y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -dEFinD lee_fin ler_norm_add.
Qed.

Lemma lee_abs_dsum (I : Type) (s : seq I) (F : I -> \bar R) (P : pred I) :
  `|\sum_(i <- s | P i) F i| <= \sum_(i <- s | P i) `|F i|.
Proof.
elim/big_ind2 : _ => //; first by rewrite abse0.
by move=> *; exact/(le_trans (lee_abs_dadd _ _) (lee_dadd _ _)).
Qed.

Lemma lee_abs_dsub x y : `|x - y| <= `|x| + `|y|.
Proof.
by move: x y => [x| |] [y| |] //; rewrite /abse -dEFinD lee_fin ler_norm_sub.
Qed.

Lemma dadde_minl : left_distributive (@dual_adde R) mine.
Proof. by move=> x y z; rewrite !dual_addeE oppe_min adde_maxl oppe_max. Qed.

Lemma dadde_minr : right_distributive (@dual_adde R) mine.
Proof. by move=> x y z; rewrite !dual_addeE oppe_min adde_maxr oppe_max. Qed.

End DualERealArithTh_realDomainType.
Arguments lee_dsum_nneg_ord {R}.
Arguments lee_dsum_npos_ord {R}.
Arguments lee_dsum_nneg_natr {R}.
Arguments lee_dsum_npos_natr {R}.
Arguments lee_dsum_nneg_natl {R}.
Arguments lee_dsum_npos_natl {R}.

End DualAddTheoryRealDomain.

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
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma lee_adde x y : (forall e : {posnum R}, x <= y + e%:num%:E) -> x <= y.
Proof.
move: x y => [x| |] [y| |] //=; rewrite ?(lee_ninfty,lee_pinfty) //;
  try by move/(_ (PosNum ltr01)).
rewrite lee_fin => abe; rewrite leNgt; apply/negP => ba; apply/existsNP : abe.
have xy : (0 < (x - y) / 2)%R by apply divr_gt0 => //; rewrite subr_gt0.
exists (PosNum xy); apply/negP; rewrite -ltNge lte_fin -ltr_subr_addl.
by rewrite ltr_pdivr_mulr // ltr_pmulr ?subr_gt0 // ltr1n.
Qed.

Lemma lte_spaddr z x y : z \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=;
  rewrite ?(lte_fin, lte_fin, lte_pinfty) //.
exact: ltr_spaddr.
Qed.

Lemma lee_mul01Pr x y : 0 <= x ->
  reflect (forall r, (0 < r < 1)%R -> r%:E * x <= y) (x <= y).
Proof.
move=> x0; apply/(iffP idP) => [xy r /andP[r0 r1]|h].
  move: x0 xy; rewrite le_eqVlt => /predU1P[<-|x0 xy]; first by rewrite mule0.
  by rewrite (le_trans _ xy) // gee_pmull // ltW.
have h01 : (0 < (2^-1 : R) < 1)%R by rewrite invr_gt0 ?invf_lt1 ?ltr0n ?ltr1n.
move: x y => [x||] [y||] // in x0 h *.
- move: (x0); rewrite lee_fin le_eqVlt => /predU1P[<-|{}x0].
    by rewrite (le_trans _ (h _ h01))// mule_ge0// lee_fin.
  have y0 : (0 < y)%R.
    by rewrite -lte_fin (lt_le_trans _ (h _ h01))// mule_gt0// lte_fin.
  rewrite lee_fin leNgt; apply/negP => yx.
  have /h : (0 < (y + x) / (2 * x) < 1)%R.
    apply/andP; split; first by rewrite divr_gt0 // ?addr_gt0// ?mulr_gt0.
    by rewrite ltr_pdivr_mulr ?mulr_gt0// mul1r mulr_natl mulr2n ltr_add2r.
  rewrite -(EFinM _ x) lee_fin invrM ?unitfE// ?gt_eqF// -mulrA mulrAC.
  by rewrite mulVr ?unitfE ?gt_eqF// mul1r; apply/negP; rewrite -ltNge midf_lt.
- by rewrite lee_pinfty.
- by have := h _ h01.
- by have := h _ h01; rewrite mulrinfty sgrV gtr0_sg // mul1e.
- by have := h _ h01; rewrite mulrinfty sgrV gtr0_sg // mul1e.
Qed.

Lemma lte_pdivr_mull r x y : (0 < r)%R -> (r^-1%:E * y < x) = (y < r%:E * x).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivr_mull.
- by rewrite mulrinfty sgrV gtr0_sg// mul1e 2!ltNge 2!lee_pinfty.
- by rewrite mulrinfty sgrV gtr0_sg// mul1e -EFinM 2!lte_ninfty.
- by rewrite mulrinfty gtr0_sg// mul1e 2!lte_pinfty.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// mul1e ltxx.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulrinfty gtr0_sg// mul1e.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// mul1e.
Qed.

Lemma lte_pdivr_mulr r x y : (0 < r)%R -> (y * r^-1%:E < x) = (y < x * r%:E).
Proof. by move=> r0; rewrite muleC lte_pdivr_mull// muleC. Qed.

Lemma lte_pdivl_mull r y x : (0 < r)%R -> (x < r^-1%:E * y) = (r%:E * x < y).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivl_mull.
- by rewrite mulrinfty sgrV gtr0_sg// mul1e 2!lte_pinfty.
- by rewrite mulrinfty sgrV gtr0_sg// mul1e.
- by rewrite mulrinfty gtr0_sg// mul1e.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// mul1e.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulrinfty gtr0_sg// mul1e 2!lte_ninfty.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulrinfty [in RHS]mulrinfty sgrV gtr0_sg// mul1e.
Qed.

Lemma lte_pdivl_mulr r x y : (0 < r)%R -> (x < y * r^-1%:E) = (x * r%:E < y).
Proof. by move=> r0; rewrite muleC lte_pdivl_mull// muleC. Qed.

Lemma lte_ndivl_mulr r x y : (r < 0)%R -> (x < y * r^-1%:E) = (y < x * r%:E).
Proof.
rewrite -oppr0 ltr_oppr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN muleN lte_oppr lte_pdivr_mulr// EFinN muleNN.
Qed.

Lemma lte_ndivl_mull r x y : (r < 0)%R -> (x < r^-1%:E * y) = (y < r%:E * x).
Proof. by move=> r0; rewrite muleC lte_ndivl_mulr// muleC. Qed.

Lemma lte_ndivr_mull r x y : (r < 0)%R -> (r^-1%:E * y < x) = (r%:E * x < y).
Proof.
rewrite -oppr0 ltr_oppr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN mulNe lte_oppl lte_pdivl_mull// EFinN muleNN.
Qed.

Lemma lte_ndivr_mulr r x y : (r < 0)%R -> (y * r^-1%:E < x) = (x * r%:E < y).
Proof. by move=> r0; rewrite muleC lte_ndivr_mull// muleC. Qed.

Lemma lee_pmul x1 y1 x2 y2 : 0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 ->
  x1 * x2 <= y1 * y2.
Proof.
move: x1 y1 x2 y2 => [x1| |] [y1| |] [x2| |] [y2| |] //; rewrite !lee_fin.
- exact: ler_pmul.
- rewrite le_eqVlt => /predU1P[<- x20 y10 _|x10 x20 xy1 _].
    by rewrite mul0e mule_ge0// lee_pinfty.
  by rewrite mulrinfty gtr0_sg// ?mul1e ?lee_pinfty// (lt_le_trans x10).
- rewrite le_eqVlt => /predU1P[<- _ y10 _|x10 _ xy1 _].
    by rewrite mul0e mule_ge0// lee_pinfty.
  rewrite mulrinfty gtr0_sg// mul1e mulrinfty gtr0_sg// ?mul1e//.
  exact: (lt_le_trans x10).
- move=> x10; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulrinfty mule_ge0// ?lee_pinfty// lee_fin sgr_ge0.
  by rewrite mulrinfty gtr0_sg ?mul1e ?lee_pinfty// (lt_le_trans x20).
- by move=> x10 x20 _ _; rewrite mule_pinfty_pinfty lee_pinfty.
- rewrite le_eqVlt => /predU1P[<- _ _ _|x10 _ _ _].
    by rewrite mule_pinfty_pinfty mul0e lee_pinfty.
  by rewrite mule_pinfty_pinfty mulrinfty gtr0_sg// mul1e.
- move=> _; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulrinfty mule_ge0// ?lee_pinfty// lee_fin sgr_ge0//.
  rewrite mulrinfty gtr0_sg// mul1e mulrinfty gtr0_sg ?mul1e//.
  exact: (lt_le_trans x20).
- move=> _; rewrite le_eqVlt => /predU1P[<- _ _|x20 _ _].
    by rewrite mule0 mule_pinfty_pinfty lee_pinfty.
  by rewrite mulrinfty gtr0_sg// mul1e// mule_pinfty_pinfty.
Qed.

Lemma lee_pdivr_mull r x y : (0 < r)%R -> (r^-1%:E * y <= x) = (y <= r%:E * x).
Proof.
move=> r0; apply/idP/idP.
- rewrite le_eqVlt => /predU1P[<-|]; last by rewrite lte_pdivr_mull// => /ltW.
  by rewrite muleA -EFinM divrr ?mul1e// unitfE gt_eqF.
- rewrite le_eqVlt => /predU1P[->|]; last by rewrite -lte_pdivr_mull// => /ltW.
  by rewrite muleA -EFinM mulVr ?mul1e// unitfE gt_eqF.
Qed.

Lemma lee_pdivr_mulr r x y : (0 < r)%R -> (y * r^-1%:E <= x) = (y <= x * r%:E).
Proof. by move=> r0; rewrite muleC lee_pdivr_mull// muleC. Qed.

Lemma lee_pdivl_mull r y x : (0 < r)%R -> (x <= r^-1%:E * y) = (r%:E * x <= y).
Proof.
move=> r0; apply/idP/idP.
- rewrite le_eqVlt => /predU1P[->|]; last by rewrite lte_pdivl_mull// => /ltW.
  by rewrite muleA -EFinM divrr ?mul1e// unitfE gt_eqF.
- rewrite le_eqVlt => /predU1P[<-|]; last by rewrite -lte_pdivl_mull// => /ltW.
  by rewrite muleA -EFinM mulVr ?mul1e// unitfE gt_eqF.
Qed.

Lemma lee_pdivl_mulr r x y : (0 < r)%R -> (x <= y * r^-1%:E) = (x * r%:E <= y).
Proof. by move=> r0; rewrite muleC lee_pdivl_mull// muleC. Qed.

Lemma lee_ndivl_mulr r x y : (r < 0)%R -> (x <= y * r^-1%:E) = (y <= x * r%:E).
Proof.
rewrite -oppr0 ltr_oppr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN muleN lee_oppr lee_pdivr_mulr// EFinN muleNN.
Qed.

Lemma lee_ndivl_mull r x y : (r < 0)%R -> (x <= r^-1%:E * y) = (y <= r%:E * x).
Proof. by move=> r0; rewrite muleC lee_ndivl_mulr// muleC. Qed.

Lemma lee_ndivr_mull r x y : (r < 0)%R -> (r^-1%:E * y <= x) = (r%:E * x <= y).
Proof.
rewrite -oppr0 ltr_oppr => r0; rewrite -{1}(opprK r) invrN.
by rewrite EFinN mulNe lee_oppl lee_pdivl_mull// EFinN muleNN.
Qed.

Lemma lee_ndivr_mulr r x y : (r < 0)%R -> (y * r^-1%:E <= x) = (x * r%:E <= y).
Proof. by move=> r0; rewrite muleC lee_ndivr_mull// muleC. Qed.

End realFieldType_lemmas.

Module DualAddTheoryRealField.

Section DualRealFieldType_lemmas.
Local Open Scope ereal_dual_scope.
Variable R : realFieldType.
Implicit Types x y : \bar R.

Lemma lee_dadde x y : (forall e : {posnum R}, x <= y + e%:num%:E) -> x <= y.
Proof. by move=> xye; apply: lee_adde => e; case: x {xye} (xye e). Qed.

Lemma lte_spdaddr (r : R) x y : 0 < y -> r%:E <= x -> r%:E < x + y.
Proof.
move: y x => [y| |] [x| |] //=; rewrite ?lte_fin ?ltt_fin ?lte_pinfty //.
exact: ltr_spaddr.
Qed.

End DualRealFieldType_lemmas.

End DualAddTheoryRealField.

Module DualAddTheory.
Export DualAddTheoryNumDomain.
Export DualAddTheoryRealDomain.
Export DualAddTheoryRealField.
End DualAddTheory.

Section ereal_supremum.
Variable R : realFieldType.
Local Open Scope classical_set_scope.
Implicit Types S : set (\bar R).
Implicit Types x y : \bar R.

Lemma ereal_ub_pinfty S : ubound S +oo.
Proof. by apply/ubP=> x _; rewrite lee_pinfty. Qed.

Lemma ereal_ub_ninfty S : ubound S -oo -> S = set0 \/ S = [set -oo].
Proof.
have [->|/set0P[x Sx] Snoo] := eqVneq S set0; first by left.
right; rewrite predeqE => y; split => [/Snoo|->{y}].
  by rewrite lee_ninfty_eq => /eqP ->.
by have := Snoo _ Sx; rewrite lee_ninfty_eq => /eqP <-.
Qed.

Lemma ereal_supremums_set0_ninfty : supremums (@set0 (\bar R)) -oo.
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

Lemma ub_ereal_sup_adherent S (e : {posnum R}) :
  ereal_sup S \is a fin_num -> exists x, S x /\ (ereal_sup S - e%:num%:E < x).
Proof.
move=> Sr.
have : ~ ubound S (ereal_sup S - e%:num%:E).
  move/ub_ereal_sup; apply/negP.
  by rewrite -ltNge lte_subl_addr // lte_addl // lte_fin.
move/asboolP; rewrite asbool_neg; case/existsp_asboolPn => /= x.
rewrite not_implyE => -[? ?]; exists x; split => //.
by rewrite ltNge; apply/negP.
Qed.

Lemma lb_ereal_inf_adherent S (e : {posnum R}) :
  ereal_inf S \is a fin_num -> exists x, S x /\ (x < ereal_inf S + e%:num%:E).
Proof.
rewrite [in X in X -> _]/ereal_inf fin_numN => /(ub_ereal_sup_adherent e)[x []].
move=> [y Sy <-]; rewrite -lte_oppr => /lt_le_trans ex; exists y; split => //.
by apply: ex; rewrite oppeD// oppeK.
Qed.

Lemma ereal_sup_gt S x : x < ereal_sup S -> exists2 y, S y & x < y.
Proof.
rewrite not_exists2P => + g; apply/negP; rewrite -leNgt.
by apply: ub_ereal_sup => y Sy; move: (g y) => [//|/negP]; rewrite leNgt.
Qed.

Lemma ereal_inf_lt S x : ereal_inf S < x -> exists2 y, S y & y < x.
Proof.
rewrite lte_oppl => /ereal_sup_gt[_ [y Sy <-]].
by rewrite lte_oppl oppeK => xlty; exists y.
Qed.

End ereal_supremum.

Section ereal_supremum_realType.
Variable R : realType.
Local Open Scope classical_set_scope.
Implicit Types S : set (\bar R).
Implicit Types x : \bar R.

Let fine_def r0 x : R := if x is r%:E then r else r0.
(* NB: see also fine above *)

Lemma ereal_supremums_neq0 S : supremums S !=set0.
Proof.
have [->|Snoo] := eqVneq S [set -oo].
  by exists -oo; split; [rewrite ub_set1 |exact: lb_ub_refl].
have [->|S0] := eqVneq S set0.
  by exists -oo; exact: ereal_supremums_set0_ninfty.
have [Spoo|Spoo] := pselect (S +oo).
  by exists +oo; split; [apply/ereal_ub_pinfty | apply/lbP => /= y /ubP; apply].
have [r Sr] : exists r, S r%:E.
  move: S0 => /set0P[] [r Sr| // |Snoo1]; first by exists r.
  apply/not_existsP => nS; move/negP : Snoo; apply.
  by apply/eqP; rewrite predeqE => -[] // r; split => // /nS.
set U := fine_def r @` S.
have [|] := eqVneq (ubound U) set0.
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

Lemma hasNub_ereal_sup (A : set (\bar R)) : ~ has_ubound A ->
  A !=set0 -> ereal_sup A = +oo%E.
Proof.
move=> hasNubA A0.
apply/eqP; rewrite eq_le lee_pinfty /= leNgt.
apply: contra_notN hasNubA => Aoo.
by exists (ereal_sup A); exact: ereal_sup_ub.
Qed.

Lemma ereal_sup_EFin  (A : set R) :
  has_ubound A -> A !=set0 -> ereal_sup (EFin @` A) = (sup A)%:E.
Proof.
move=> has_ubA A0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ub_ereal_sup => /= y [r Ar <-{y}]; rewrite lee_fin sup_ub.
set esup := ereal_sup _; have := lee_pinfty esup.
rewrite le_eqVlt => /predU1P[->|esupoo]; first by rewrite lee_pinfty.
have := lee_ninfty esup; rewrite le_eqVlt => /predU1P[/esym|ooesup].
  case: A0 => i Ai.
  by move=> /ereal_sup_ninfty /(_ i%:E) /(_ (ex_intro2 A _ i Ai erefl)).
have esup_fin_num : esup \is a fin_num.
  rewrite fin_numE -lee_ninfty_eq -ltNge ooesup /= -lee_pinfty_eq -ltNge.
  by rewrite esupoo.
rewrite -(@fineK _ esup) // lee_fin leNgt.
apply/negP => /(sup_gt A0)[r Ar]; apply/negP; rewrite -leNgt.
by rewrite -lee_fin fineK//; apply: ereal_sup_ub; exists r.
Qed.

Lemma ereal_inf_EFin (A : set R) : has_lbound A -> A !=set0 ->
   ereal_inf (EFin @` A) = (inf A)%:E.
Proof.
move=> has_lbA A0; rewrite /ereal_inf /inf EFinN; congr (- _)%E.
rewrite -ereal_sup_EFin; [|exact/has_lb_ubN|exact/nonemptyN].
by rewrite !image_comp.
Qed.

End ereal_supremum_realType.

Canonical ereal_pointed (R : numDomainType) := PointedType (extended R) 0%E.

Lemma restrict_abse T (R : numDomainType) (f : T -> \bar R) (D : set T) :
  (abse \o f) \_ D = abse \o (f \_ D).
Proof.
by apply/funext=> t; rewrite /restrict/=; case: ifPn => // _; rewrite abse0.
Qed.

Section ereal_nbhs.
Context {R : numFieldType}.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Definition ereal_dnbhs (x : \bar R) (P : \bar R -> Prop) : Prop :=
  match x with
    | r%:E => r^' (fun r => P r%:E)
    | +oo => exists M, M \is Num.real /\ forall y, M%:E < y -> P y
    | -oo => exists M, M \is Num.real /\ forall y, y < M%:E -> P y
  end.
Definition ereal_nbhs (x : \bar R) (P : \bar R -> Prop) : Prop :=
  match x with
    | x%:E => nbhs x (fun r => P r%:E)
    | +oo => exists M, M \is Num.real /\ forall y, M%:E < y -> P y
    | -oo => exists M, M \is Num.real /\ forall y, y < M%:E -> P y
  end.
Canonical ereal_ereal_filter :=
  FilteredType (extended R) (extended R) (ereal_nbhs).
End ereal_nbhs.

Lemma ereal_nbhs_pinfty_ge (R : numFieldType) (e : {posnum R}) :
  \forall x \near +oo, e%:num%:E <= x.
Proof. by exists e%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

Lemma ereal_nbhs_ninfty_le (R : numFieldType) (r : R) : (r < 0)%R ->
  \forall x \near -oo, x <= r%:E.
Proof.
by move=> /ltW r0; exists r; rewrite realE r0 orbT; split => // x /ltW.
Qed.

Section ereal_nbhs_instances.
Context {R : numFieldType}.

Global Instance ereal_dnbhs_filter :
  forall x : \bar R, ProperFilter (ereal_dnbhs x).
Proof.
case=> [x||].
- case: (Proper_dnbhs_numFieldType x) => x0 [//= xT xI xS].
  apply Build_ProperFilter' => //=; apply Build_Filter => //=.
  move=> P Q lP lQ; exact: xI.
  by move=> P Q PQ /xS; apply => y /PQ.
- apply Build_ProperFilter.
    move=> P [x [xr xP]] //; exists (x + 1)%:E; apply xP => /=.
    by rewrite lte_fin ltr_addl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0%R; rewrite real0.
  + have [MP0|MP0] := eqVneq MP 0%R.
      have [MQ0|MQ0] := eqVneq MQ 0%R.
        by exists 0%R; rewrite real0; split => // x x0; split;
        [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|%R; rewrite realE normr_ge0; split => // x MQx; split.
        by apply: gtMP; rewrite (le_lt_trans _ MQx) // MP0 lee_fin.
      by apply gtMQ; rewrite (le_lt_trans _ MQx)// lee_fin real_ler_normr ?lexx.
    have [MQ0|MQ0] := eqVneq MQ 0%R.
      exists `|MP|%R; rewrite realE normr_ge0; split => // x MPx; split.
      by apply gtMP; rewrite (le_lt_trans _ MPx)// lee_fin real_ler_normr ?lexx.
      by apply gtMQ; rewrite (le_lt_trans _ MPx) // lee_fin MQ0.
    have {}MP0 : (0 < `|MP|)%R by rewrite normr_gt0.
    have {}MQ0 : (0 < `|MQ|)%R by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= posnum_ge0 /=; split => //.
    case=> [r| |//].
    * rewrite lte_fin/= posnum_max pos_lt_maxl /= => /andP[MPx MQx]; split.
      by apply/gtMP; rewrite lte_fin (le_lt_trans _ MPx)// real_ler_normr ?lexx.
      by apply/gtMQ; rewrite lte_fin (le_lt_trans _ MQx)// real_ler_normr ?lexx.
    * by move=> _; split; [apply/gtMP | apply/gtMQ].
  + by exists M; split => // ? /gtM /sPQ.
- apply Build_ProperFilter.
  + move=> P [M [Mr ltMP]]; exists (M - 1)%:E.
    by apply: ltMP; rewrite lte_fin gtr_addl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0%R; rewrite real0.
    * have [MP0|MP0] := eqVneq MP 0%R.
        have [MQ0|MQ0] := eqVneq MQ 0%R.
          by exists 0%R; rewrite real0; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|)%R; rewrite realN realE normr_ge0; split => // x xMQ.
        split.
          by apply ltMP; rewrite (lt_le_trans xMQ)// lee_fin MP0 ler_oppl oppr0.
       apply ltMQ; rewrite (lt_le_trans xMQ) // lee_fin ler_oppl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [MQ0|MQ0] := eqVneq MQ 0%R.
        exists (- `|MP|)%R; rewrite realN realE normr_ge0; split => // x MPx.
        split.
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
Typeclasses Opaque ereal_dnbhs.

Global Instance ereal_nbhs_filter : forall x, ProperFilter (@ereal_nbhs R x).
Proof.
case=> [r| |].
- case: (ereal_dnbhs_filter r%:E) => r0 [//= nrT rI rS].
  apply: Build_ProperFilter => P /nbhs_ballP[r2 r20 rr2].
  by exists r%:E; exact/rr2/ballxx.
- exact: (ereal_dnbhs_filter +oo).
- exact: (ereal_dnbhs_filter -oo).
Qed.
Typeclasses Opaque ereal_nbhs.

End ereal_nbhs_instances.

Section ereal_topologicalType.
Variable R : realFieldType.

Lemma ereal_nbhs_singleton (p : \bar R) (A : set (\bar R)) :
  ereal_nbhs p A -> A p.
Proof.
move: p => -[p | [M [Mreal MA]] | [M [Mreal MA]]] /=; [|exact: MA | exact: MA].
move=> /nbhs_ballP[_/posnumP[e]]; apply; exact/ballxx.
Qed.

Lemma ereal_nbhs_nbhs (p : \bar R) (A : set (\bar R)) :
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
    apply/nbhs_ballP; exists 1%R => //= y x1y.
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
    apply/nbhs_ballP; exists 1%R => //= y x1y.
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

Lemma nbhsNe (R : realFieldType) (x : \bar R) :
  nbhs (- x) = [set (-%E @` A) | A in nbhs x].
Proof.
case: x => [r /=| |].
- rewrite /nbhs /= /ereal_nbhs -nbhs_ballE.
  rewrite predeqE => S; split => [[_/posnumP[e] reS]|[S' [_ /posnumP[e] reS' <-]]].
    exists (-%E @` S).
      exists e%:num => // r1 rer1; exists (- r1%:E); last by rewrite oppeK.
      by apply reS; rewrite /ball /= opprK -normrN opprD opprK.
    rewrite predeqE => s; split => [[y [z Sz] <- <-]|Ss].
      by rewrite oppeK.
    by exists (- s); [exists s | rewrite oppeK].
  exists e%:num => // r1 rer1; exists (- r1%:E); last by rewrite oppeK.
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

Lemma nbhsNKe (R : realFieldType) (z : \bar R) (A : set (\bar R)) :
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
Implicit Types (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Definition contract x : R :=
  match x with
  | r%:E => r / (1 + `|r|) | +oo => 1 | -oo => -1
  end.

Lemma contract_lt1 r : (`|contract r%:E| < 1)%R.
Proof.
rewrite normrM normrV ?unitfE //; last by rewrite eq_sym lt_eqF // ltr_spaddl.
rewrite ltr_pdivr_mulr // ?mul1r; last by rewrite gtr0_norm ltr_spaddl.
by rewrite [X in (_ < X)%R]gtr0_norm ?ltr_addr// ltr_spaddl.
Qed.

Lemma contract_le1 x : (`|contract x| <= 1)%R.
Proof.
by case: x => [r| |] /=; rewrite ?normrN1 ?normr1 // (ltW (contract_lt1 _)).
Qed.

Lemma contract0 : contract 0 = 0%R.
Proof. by rewrite /contract mul0r. Qed.

Lemma contractN x : contract (- x) = (- contract x)%R.
Proof. by case: x => //= [r|]; [ rewrite normrN mulNr | rewrite opprK]. Qed.

Lemma contract_imageN (S : set (\bar R)) :
  contract @` (-%E @` S) = -%R @` (contract @` S).
Proof.
rewrite predeqE => r; split => [[y [z Sz <-{y} <-{r}]]|[s [y Sy <-{s} <-{r}]]].
by exists (contract z); [exists z | rewrite contractN].
by exists (- y); [exists y | rewrite contractN].
Qed.

(* TODO: not exploited yet: expand is nondecreasing everywhere so it should be
   possible to use some of the homoRL/homoLR lemma where monoRL/monoLR do not
   apply *)
Definition expand r : \bar R :=
  if (r >= 1)%R then +oo else if (r <= -1)%R then -oo else (r / (1 - `|r|))%:E.

Lemma expand1 r : (1 <= r)%R -> expand r = +oo.
Proof. by move=> r1; rewrite /expand r1. Qed.

Lemma expandN r : expand (- r)%R = - expand r.
Proof.
rewrite /expand; case: ifPn => [r1|].
  rewrite ifF; [by rewrite ifT // -ler_oppr|apply/negbTE].
  by rewrite -ltNge -(opprK r) -ltr_oppl (lt_le_trans _ r1) // -subr_gt0 opprK.
rewrite -ltNge => r1; case: ifPn; rewrite ler_oppl opprK; [by move=> ->|].
by rewrite -ltNge leNgt => ->; rewrite leNgt -ltr_oppl r1 /= mulNr normrN.
Qed.

Lemma expandN1 r : (r <= -1)%R -> expand r = -oo.
Proof.
by rewrite ler_oppr => /expand1/eqP; rewrite expandN eqe_oppLR => /eqP.
Qed.

Lemma expand0 : expand 0%R = 0.
Proof. by rewrite /expand leNgt ltr01 /= oppr_ge0 leNgt ltr01 /= mul0r. Qed.

Lemma expandK : {in [pred r | `|r| <= 1]%R, cancel expand contract}.
Proof.
move=> r; rewrite inE le_eqVlt => /orP[|r1].
  rewrite eqr_norml => /andP[/orP[]/eqP->{r}] _;
    by [rewrite expand1|rewrite expandN1].
rewrite /expand 2!leNgt ltr_oppl; case/ltr_normlP : (r1) => -> -> /=.
have r_pneq0 : (1 + r / (1 - r) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 - r)%R) -?mulrDl; last first.
    by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
  by rewrite subrK mulf_neq0 // invr_eq0 subr_eq0 eq_sym lt_eqF // ltr_normlW.
have r_nneq0 : (1 - r / (1 + r) != 0)%R.
  rewrite -[X in (X + _)%R](@divrr _ (1 + r)%R) -?mulrBl; last first.
    by rewrite unitfE addrC addr_eq0 gt_eqF // ltrNnormlW.
  rewrite addrK mulf_neq0 // invr_eq0 addr_eq0 -eqr_oppLR eq_sym gt_eqF //.
  exact: ltrNnormlW.
wlog : r r1 r_pneq0 r_nneq0 / (0 <= r)%R => wlog_r0.
  have [r0|r0] := lerP 0 r; first by rewrite wlog_r0.
  move: (wlog_r0 (- r)%R).
  rewrite !(normrN, opprK, mulNr) oppr_ge0 => /(_ r1 r_nneq0 r_pneq0 (ltW r0)).
  by move/eqP; rewrite eqr_opp => /eqP.
rewrite /contract !ger0_norm //; last first.
  by rewrite divr_ge0 // subr_ge0 (le_trans _ (ltW r1)) // ler_norm.
apply: (@mulIr _ (1 + r / (1 - r))%R); first by rewrite unitfE.
rewrite -(mulrA (r / _)) mulVr ?unitfE // mulr1.
rewrite -[X in (X + _ / _)%R](@divrr _ (1 - r)%R) -?mulrDl ?subrK ?div1r //.
by rewrite unitfE subr_eq0 eq_sym lt_eqF // ltr_normlW.
Qed.

Lemma le_contract : {mono contract : x y / (x <= y)%O}.
Proof.
apply: le_mono; move=> -[r0 | | ] [r1 | _ | _] //=.
- rewrite lte_fin => r0r1; rewrite ltr_pdivr_mulr ?ltr_paddr//.
  rewrite mulrAC ltr_pdivl_mulr ?ltr_paddr// 2?mulrDr 2?mulr1.
  have [r10|?] := ler0P r1; last first.
    rewrite ltr_le_add // mulrC; have [r00|//] := ler0P r0.
    by rewrite (@le_trans _ _ 0%R) // ?pmulr_lle0// mulr_ge0// ?oppr_ge0// ltW.
  have [?|r00] := ler0P r0; first by rewrite ltr_le_add // 2!mulrN mulrC.
  by move: (le_lt_trans r10 (lt_trans r00 r0r1)); rewrite ltxx.
- by rewrite ltr_pdivr_mulr ?ltr_paddr// mul1r ltr_spaddl // ler_norm.
- rewrite ltr_pdivl_mulr ?mulN1r ?ltr_paddr// => _.
  by rewrite ltr_oppl ltr_spaddl // ler_normr lexx orbT.
- by rewrite -subr_gt0 opprK.
Qed.

Definition lt_contract := leW_mono le_contract.
Definition contract_inj := mono_inj lexx le_anti le_contract.

Lemma le_expand_in : {in [pred r | `|r| <= 1]%R &,
  {mono expand : x y / (x <= y)%O}}.
Proof. exact: can_mono_in (onW_can_in predT expandK) _ (in2W le_contract). Qed.

Definition lt_expand := leW_mono_in le_expand_in.
Definition expand_inj := mono_inj_in lexx le_anti le_expand_in.

Lemma fine_expand r : (`|r| < 1)%R ->
  (fine (expand r))%:E = expand r.
Proof.
by move=> r1; rewrite /expand 2!leNgt ltr_oppl; case/ltr_normlP : r1 => -> ->.
Qed.

Lemma contractK : cancel contract expand.
Proof.
apply: (onS_can [pred r | `|r| <= 1]%R contract_le1).
exact: inj_can_sym_on expandK (in1W contract_inj).
Qed.

Lemma bijective_contract : {on [pred r | `|r| <= 1]%R, bijective contract}.
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
  have [y_le1|/ltW /expand1->] := leP y 1%R; last by rewrite lee_pinfty.
  rewrite le_expand_in ?inE// ler_norml y_le1 (le_trans _ xy)//.
  by rewrite ler_oppl (ler_normlP _ _ _).
rewrite ltr_normr => /orP[|] x1; last first.
  by rewrite expandN1 // ?lee_ninfty // ler_oppr ltW.
by rewrite expand1; [rewrite expand1 // (le_trans _ xy) // ltW | exact: ltW].
Qed.

Lemma contract_eq0 x : (contract x == 0%R) = (x == 0).
Proof. by rewrite -(can_eq contractK) contract0. Qed.

Lemma contract_eqN1 x : (contract x == -1) = (x == -oo).
Proof. by rewrite -(can_eq contractK). Qed.

Lemma contract_eq1 x : (contract x == 1%R) = (x == +oo).
Proof. by rewrite -(can_eq contractK). Qed.

Lemma expand_eqoo r : (expand r == +oo) = (1 <= r)%R.
Proof. by rewrite /expand; case: ifP => //; case: ifP. Qed.

Lemma expand_eqNoo r : (expand r == -oo) = (r <= -1)%R.
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
by exists 1%R => r [y Sy <-]; case/ler_normlP : (contract_le1 y).
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
  by exists 1%R => r [z Sz <-]; case/ler_normlP : (contract_le1 z).
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
Implicit Types (x y : \bar R) (r : R).

Definition ereal_ball x r y := (`|contract x - contract y| < r)%R.

Lemma ereal_ball_center x r : (0 < r)%R -> ereal_ball x r x.
Proof. by move=> e0; rewrite /ereal_ball subrr normr0. Qed.

Lemma ereal_ball_sym x y r : ereal_ball x r y -> ereal_ball y r x.
Proof. by rewrite /ereal_ball distrC. Qed.

Lemma ereal_ball_triangle x y z r1 r2 :
  ereal_ball x r1 y -> ereal_ball y r2 z -> ereal_ball x (r1 + r2) z.
Proof.
rewrite /ereal_ball => h1 h2; rewrite -[X in (X - _)%R](subrK (contract y)).
by rewrite -addrA (le_lt_trans (ler_norm_add _ _)) // ltr_add.
Qed.

Lemma ereal_ballN x y (e : {posnum R}) :
  ereal_ball (- x) e%:num (- y) -> ereal_ball x e%:num y.
Proof. by rewrite /ereal_ball 2!contractN opprK -opprB normrN addrC. Qed.

Lemma le_ereal_ball x : {homo ereal_ball x : e e' / (e <= e')%R >-> e `<=` e'}.
Proof. by move=> e e' ee' y; rewrite /ereal_ball => /lt_le_trans; exact. Qed.

Lemma ereal_ball_ninfty_oversize (e : {posnum R}) x :
  (2 < e%:num)%R -> ereal_ball -oo e%:num x.
Proof.
move=> e2; rewrite /ereal_ball /= (le_lt_trans _ e2) // -opprB normrN opprK.
rewrite (le_trans (ler_norm_add _ _)) // normr1 -ler_subr_addr.
by rewrite (le_trans (contract_le1 _)) // (_ : 2 = 1 + 1)%R // addrK.
Qed.

Lemma contract_ereal_ball_pinfty r (e : {posnum R}) :
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

Lemma contract_ereal_ball_fin_le r r' (e : {posnum R}) : (r <= r')%R ->
  (1 <= contract r%:E + e%:num)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-{r'} _|rr' re1]; first exact: ereal_ball_center.
rewrite /ereal_ball ltr0_norm; last by rewrite subr_lt0 lt_contract lte_fin.
rewrite opprB ltr_subl_addl (lt_le_trans _ re1) //.
by case/ltr_normlP : (contract_lt1 r').
Qed.

Lemma contract_ereal_ball_fin_lt r r' (e : {posnum R}) : (r' < r)%R ->
  (contract r%:E - e%:num <= -1)%R  -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r reN1; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
rewrite ltr_subl_addl addrC -ltr_subl_addl (le_lt_trans reN1) //.
by move: (contract_lt1 r'); rewrite ltr_norml => /andP[].
Qed.

Lemma expand_ereal_ball_fin_lt r' r (e : {posnum R}) : (r' < r)%R ->
  expand (contract r%:E - e%:num)%R < r'%:E ->
  (`|contract r%:E - e%:num| < 1)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r ? r'e'r.
rewrite /ereal_ball gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
by rewrite ltr_subl_addl addrC -ltr_subl_addl -lt_expandLR ?inE ?ltW.
Qed.

Lemma ball_ereal_ball_fin_lt r r' (e : {posnum R}) :
  let e' := (r - fine (expand (contract r%:E - e%:num)))%R in
  ball r e' r' -> (r' < r)%R ->
  (`|contract r%:E - (e)%:num| < 1)%R ->
  ereal_ball r%:E (e)%:num r'%:E.
Proof.
move=> e' re'r' rr' X; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0// ?lt_contract ?lte_fin//.
move: re'r'.
rewrite /ball /= gtr0_norm // ?subr_gt0// /e'.
rewrite -ltr_subl_addl addrAC subrr add0r ltr_oppl opprK -lte_fin.
rewrite fine_expand // lt_expandLR ?inE ?ltW//.
by rewrite ltr_subl_addl addrC -ltr_subl_addl.
Qed.

Lemma ball_ereal_ball_fin_le r r' (e : {posnum R}) :
  let e' : R := (fine (expand (contract r%:E + e%:num)) - r)%R in
  ball r e' r' -> (r <= r')%R ->
  (`| contract r%:E + e%:num | < 1)%R ->
  (ereal_ball r%:E e%:num r'%:E).
Proof.
move=> e' r'e'r rr' re1; rewrite /ereal_ball.
move: rr'; rewrite le_eqVlt => /predU1P[->|rr']; first by rewrite subrr normr0.
rewrite /ball /= ltr0_norm ?subr_lt0// opprB in r'e'r.
rewrite ltr0_norm ?subr_lt0 ?lt_contract ?lte_fin//.
rewrite opprB; move: r'e'r.
rewrite /e' -ltr_subl_addr opprK subrK -lte_fin fine_expand //.
by rewrite lt_expandRL ?inE ?ltW// ltr_subl_addl.
Qed.

Lemma nbhs_oo_up_e1 (A : set (\bar R)) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 ooeA.
exists (fine (expand (1 - e%:num)%R)); rewrite num_real; split => //.
case => [r | | //].
- rewrite fine_expand; last first.
    by rewrite ger0_norm ?ltr_subl_addl ?ltr_addr // subr_ge0.
  by move=> ?; exact/ooeA/expand_ereal_ball_pinfty.
- by move=> _; exact/ooeA/ereal_ball_center.
Qed.

Lemma nbhs_oo_down_e1 (A : set (\bar R)) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; suff h : nbhs +oo (-%E @` A).
  rewrite (_ : -oo = - +oo) // nbhsNe; exists (-%E @` A) => //.
  rewrite predeqE => x; split=> [[y [z Az <- <-]]|Ax]; rewrite ?oppeK //.
  by exists (- x); [exists x | rewrite oppeK].
apply (@nbhs_oo_up_e1 _ e) => // x x1e; exists (- x); last by rewrite oppeK.
by apply/reA/ereal_ballN; rewrite oppeK.
Qed.

Lemma nbhs_oo_up_1e (A : set (\bar R)) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0%R; rewrite real0.
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

Lemma nbhs_oo_down_1e (A : set (\bar R)) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0%R; rewrite real0.
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

Lemma nbhs_fin_out_above r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A ->
  (- 1 < contract r%:E - e%:num)%R ->
  (1 <= contract r%:E + e%:num)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have er1 : (`|contract r%:E - e%:num| < 1)%R.
  rewrite ltr_norml reN1 andTb ltr_subl_addl ltr_spaddl //.
  by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
pose e' := (r - fine (expand (contract r%:E - e%:num)))%R.
have e'0 : (0 < e')%R.
  rewrite subr_gt0 -lte_fin -[in X in _ < X](contractK r%:E).
  rewrite fine_expand // lt_expand ?inE ?contract_le1// ?ltW//.
  by rewrite ltr_subl_addl ltr_addr.
apply/nbhs_ballP; exists e' => // r' re'r'; apply reA.
by have [?|?] := lerP r r';
  [exact: contract_ereal_ball_fin_le | exact: ball_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_below r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A ->
  (contract r%:E - e%:num <= - 1)%R ->
  (contract r%:E + e%:num < 1)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have ? : (`|contract r%:E + e%:num| < 1)%R.
  rewrite ltr_norml re1 andbT (@lt_le_trans _ _ (contract r%:E)) // ?ler_addl //.
  by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
pose e' : R := (fine (expand (contract r%:E + e%:num)) - r)%R.
have e'0 : (0 < e')%R.
  rewrite /e' subr_gt0 -lte_fin -[in X in X < _](contractK r%:E).
  rewrite fine_expand //.
  by rewrite lt_expand ?inE ?contract_le1 ?ltr_addl ?ltW.
apply/nbhs_ballP; exists e' => // r' r'e'r; apply reA.
by have [?|?] := lerP r r';
  [exact: ball_ereal_ball_fin_le | exact: contract_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_above_below r (e : {posnum R}) (A : set (\bar R)) :
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
  by rewrite EFinN contractN -(opprK 1%R) ltr_oppl opprD opprK.
Qed.

Lemma nbhs_fin_inbound r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A -> nbhs r%:E A.
Proof.
move=> reA.
have [|reN1] := boolP (contract r%:E - e%:num == -1)%R.
  rewrite subr_eq addrC => /eqP reN1.
  have [re1|] := boolP (contract r%:E + e%:num == 1)%R.
    move/eqP : reN1; rewrite -(eqP re1) opprD addrCA subrr addr0 -subr_eq0.
    rewrite opprK -mulr2n mulrn_eq0 orFb contract_eq0 => /eqP[r0].
    move: re1; rewrite r0 contract0 add0r => /eqP e1.
    apply/nbhs_ballP; exists 1%R => // r'; rewrite /ball /= sub0r normrN => r'1.
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
  have : nbhs r%:E (setT `\ -oo) by apply/nbhs_ballP; exists 1%R.
  move=> /nbhs_ballP[_/posnumP[e']] /=; rewrite /ball /= => h.
  by apply/nbhs_ballP; exists e'%:num => // y /h; apply: Aoo.
move: reN1; rewrite eq_sym neq_lt => /orP[reN1|reN1].
  have [re1|re1] := eqVneq (contract r%:E + e%:num)%R 1%R.
    by apply (@nbhs_fin_out_above _ e) => //; rewrite re1.
  move: re1; rewrite neq_lt => /orP[re1|re1].
    have ? : (`|contract r%:E - e%:num| < 1)%R.
      rewrite ltr_norml reN1 andTb ltr_subl_addl.
      rewrite (@lt_le_trans _ _ 1%R) // ?ler_addr//.
      by case/ltr_normlP : (contract_lt1 r).
    have ? : (`|contract r%:E + e%:num| < 1)%R.
      rewrite ltr_norml re1 andbT -(addr0 (-1)) ler_lt_add //.
      by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
    pose e' : R := Num.min
      (r - fine (expand (contract r%:E - e%:num)))%R
      (fine (expand (contract r%:E + e%:num)) - r)%R.
    have e'0 : (0 < e')%R.
      rewrite /e' lt_minr; apply/andP; split.
        rewrite subr_gt0 -lte_fin -[in X in _ < X](contractK r%:E).
        rewrite fine_expand // lt_expand// ?inE ?contract_le1 ?ltW//.
        by rewrite ltr_subl_addl ltr_addr.
      rewrite subr_gt0 -lte_fin -[in X in X < _](contractK r%:E).
      rewrite fine_expand//.
      by rewrite lt_expand ?inE ?contract_le1 ?ltr_addl ?ltW.
    apply/nbhs_ballP; exists e' => // r' re'r'; apply reA.
    have [|r'r] := lerP r r'.
      move=> rr'; apply: ball_ereal_ball_fin_le => //.
      by apply: le_ball re'r'; rewrite le_minl lexx orbT.
    move: re'r'; rewrite /ball /= lt_minr => /andP[].
    rewrite gtr0_norm ?subr_gt0 // -ltr_subl_addl addrAC subrr add0r ltr_oppl.
    rewrite opprK -lte_fin fine_expand // => r'e'r _.
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
   have : nbhs r%:E (setT `\ +oo) by exists 1%R.
   case => _/posnumP[x] /=; rewrite /ball_ => h.
   by exists x%:num => // y /h; exact: Aoo.
by apply (@nbhs_fin_out_below _ e) => //; rewrite ltW.
Qed.

Lemma ereal_nbhsE : nbhs = nbhs_ (entourage_ ereal_ball).
Proof.
set diag := fun r => [set xy | ereal_ball xy.1 r xy.2].
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
        apply: reA; rewrite /ball /= real_ltr_norml // ?num_real //.
        rewrite ger0_norm ?subr_ge0// in re'r'.
        have : (contract (r%:E - e%:num%:E) < contract r'%:E)%R.
          move: re'r'; rewrite /e' lt_minr => /andP[+ _].
          rewrite /e' ltr_subr_addl addrC -ltr_subr_addl => /lt_le_trans.
          by apply; rewrite opprB addrCA subrr addr0.
        rewrite -lt_expandRL ?inE ?contract_le1 // !contractK lte_fin.
        rewrite ltr_subl_addr addrC -ltr_subl_addr => ->; rewrite andbT.
        rewrite (@lt_le_trans _ _ 0%R)// 1?ltr_oppl 1?oppr0// subr_ge0.
        by rewrite -lee_fin -le_contract.
      apply: reA; rewrite /ball /= real_ltr_norml // ?num_real //.
      rewrite ltr0_norm ?subr_lt0// opprB in re'r'.
      apply/andP; split; last first.
        by rewrite (@lt_trans _ _ 0%R) // subr_lt0 -lte_fin -lt_contract.
      rewrite ltr_oppl opprB.
      rewrite /e' in re'r'.
      have r're : (contract r'%:E < contract (r%:E + e%:num%:E))%R.
        move: re'r'; rewrite lt_minr => /andP[_].
        by rewrite ltr_subl_addr subrK.
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
      apply: MA; rewrite lte_fin.
      rewrite ger0_norm in rM1; last first.
        by rewrite subr_ge0 // (le_trans _ (contract_le1 r%:E)) // ler_norm.
      rewrite ltr_subl_addr addrC addrCA addrC -ltr_subl_addr subrr in rM1.
      rewrite subr_gt0 in rM1.
      by rewrite -lte_fin -lt_contract.
    * by rewrite /ereal_ball /= subrr normr0 => h; exact: MA.
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
- case: x => [r [E [_/posnumP[e] reA] sEA] | [E [_/posnumP[e] reA] sEA] |
               [E [_/posnumP[e] reA] sEA]] //=.
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

Definition ereal_uniformType_mixin : @Uniform.mixin_of (\bar R) nbhs :=
  uniformityOfBallMixin ereal_nbhsE ereal_pseudoMetricType_mixin.

Canonical ereal_uniformType :=
  UniformType (extended R) ereal_uniformType_mixin.

Canonical ereal_pseudoMetricType :=
  PseudoMetricType (extended R) ereal_pseudoMetricType_mixin.

End ereal_PseudoMetric.

(* TODO: generalize to numFieldType? *)
Lemma lt_ereal_nbhs (R : realFieldType) (a b : \bar R) (r : R) :
  a < r%:E -> r%:E < b ->
  exists delta : {posnum R},
    forall y, (`|y - r| < delta%:num)%R -> (a < y%:E) && (y%:E < b).
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog. (*BUG*)
  move=> {}a {}b ltxa ltxb.
  have m_gt0 : (Num.min ((r - a) / 2) ((b - r) / 2) > 0)%R.
    by rewrite lt_minr !divr_gt0 // ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite lt_minr !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite 2!lte_fin (lt_trans _ ay) ?(lt_trans yb) //=.
    rewrite -subr_gt0 opprD addrA {1}[(b - r)%R]splitr addrK.
    by rewrite divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[(r - a)%R]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (r + 1)%R; rewrite ?lte_fin ?ltr_addl //.
  by exists d => y /dP /andP[->] /= /lt_le_trans; apply; rewrite lee_pinfty.
- have [//||d dP] := wlog (r - 1)%R b; rewrite ?lte_fin ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->] /=; rewrite lte_ninfty.
- by exists 1%R%:pos => ? ?; rewrite lte_ninfty lte_pinfty.
Qed.

(* TODO: generalize to numFieldType? *)
Lemma nbhs_interval (R : realFieldType) (P : R -> Prop) (r : R) (a b : \bar R) :
  a < r%:E -> r%:E < b ->
  (forall y, a < y%:E -> y%:E < b -> P y) ->
  nbhs r P.
Proof.
move => ar rb abP; case: (lt_ereal_nbhs ar rb) => d rd.
exists d%:num => //= y; rewrite /= distrC.
by move=> /rd /andP[? ?]; apply: abP.
Qed.

Lemma ereal_dnbhs_le (R : numFieldType) (x : \bar R) :
  ereal_dnbhs x --> ereal_nbhs x.
Proof.
move: x => [r P [_/posnumP[e] reP] |r P|r P] //=.
by exists e%:num => // ? ? ?; apply: reP.
Qed.

Lemma ereal_dnbhs_le_finite (R : numFieldType) (r : R) :
  ereal_dnbhs r%:E --> nbhs r%:E.
Proof.
by move=> P [_/posnumP[e] reP] //=; exists e%:num => // ? ? ?; exact: reP.
Qed.

Definition ereal_loc_seq (R : numDomainType) (x : \bar R) (n : nat) :=
  match x with
    | x%:E => (x + (n%:R + 1)^-1)%:E
    | +oo => n%:R%:E
    | -oo => - n%:R%:E
  end.

Lemma cvg_ereal_loc_seq (R : realType) (x : \bar R) :
  ereal_loc_seq x --> ereal_dnbhs x.
Proof.
move=> P; rewrite /ereal_loc_seq.
case: x => /= [x [_/posnumP[d] dP] |[d [dreal dP]] |[d [dreal dP]]]; last 2 first.
    have /ZnatP [N Nfloor] : floor (Num.max d 0%R) \is a Znat.
      by rewrite Znat_def floor_ge0 le_maxr lexx orbC.
    exists N.+1 => // n ltNn; apply: dP.
    have /le_lt_trans : (d <= Num.max d 0)%R by rewrite le_maxr lexx.
    apply; apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor.
    by rewrite -(@natrD R N 1) ler_nat addn1.
  have /ZnatP [N Nfloor] : floor (Num.max (- d)%R 0%R) \is a Znat.
    by rewrite Znat_def floor_ge0 le_maxr lexx orbC.
  exists N.+1 => // n ltNn; apply: dP; rewrite lte_fin ltr_oppl.
  have /le_lt_trans : (- d <= Num.max (- d) 0)%R by rewrite le_maxr lexx.
  apply; apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor.
  by rewrite -(@natrD R N 1) ler_nat addn1.
have /ZnatP [N Nfloor] : floor (d%:num^-1) \is a Znat.
  by rewrite Znat_def floor_ge0.
exists N => // n leNn; have gt0Sn : (0 < n%:R + 1 :> R)%R.
  apply: ltr_spaddr => //; exact/ler0n.
apply: dP; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym; apply/invr_neq0/lt0r_neq0.
rewrite /= opprD addrA subrr distrC subr0.
rewrite gtr0_norm; last by rewrite invr_gt0.
rewrite -[X in (X < _)%R]mulr1 ltr_pdivr_mull // -ltr_pdivr_mulr // div1r.
apply: lt_le_trans (lt_succ_Rfloor _) _; rewrite RfloorE Nfloor ler_add //.
by rewrite ler_nat.
Qed.
