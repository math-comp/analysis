(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

(* TODO: merge this with table.v in real-closed
   (c.f. https://github.com/math-comp/real-closed/pull/29 ) and
   incorporate it into mathcomp proper where it could then be used for
   bounds of intervals*)
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import mathcomp_extra.
Require Import signed.

(******************************************************************************)
(*                         Extended real numbers                              *)
(*                                                                            *)
(* Given a type R for numbers, \bar R is the type R extended with symbols -oo *)
(* and +oo (notation scope: %E), suitable to represent extended real numbers. *)
(* When R is a numDomainType, \bar R is equipped with a canonical porderType  *)
(* and operations for addition/opposite. When R is a realDomainType, \bar R   *)
(* is equipped with a Canonical orderType.                                    *)
(*                                                                            *)
(* Naming convention: in definition/lemma identifiers, "e" stands for an      *)
(* extended number and "y" and "Ny" for +oo ad -oo respectively.              *)
(*                                                                            *)
(*                  \bar R == coproduct of R and {+oo, -oo};                  *)
(*                            notation for extended (R:Type)                  *)
(*                    r%:E == injects real numbers into \bar R                *)
(*           +%E, -%E, *%E == addition/opposite/multiplication for extended   *)
(*                            reals                                           *)
(*    er_map (f : T -> T') == the \bar T -> \bar T' lifting of f              *)
(*                   sqrte == square root for extended reals                  *)
(*                `| x |%E == the absolute value of x                         *)
(*                  x ^+ n == iterated multiplication                         *)
(*                  x *+ n == iterated addition                               *)
(*       +%dE, (x *+ n)%dE == dual addition/dual iterated addition for        *)
(*                            extended reals (-oo + +oo = +oo instead of -oo) *)
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
(*                                                                            *)
(* Signed extended real numbers:                                              *)
(*    {posnum \bar R} == interface type for elements in \bar R that are       *)
(*                       positive, c.f., signed.v, notation in scope %E       *)
(*    {nonneg \bar R} == interface types for elements in \bar R that are      *)
(*                       non-negative, c.f. signed.v, notation in scope %E    *)
(*             x%:pos == explicitly casts x to {posnum \bar R}, in scope %E   *)
(*             x%:nng == explicitly casts x to {nonneg \bar R}, in scope %E   *)
(*                                                                            *)
(* Topology of extended real numbers:                                         *)
(*                       contract == order-preserving bijective function      *)
(*                                   from extended real numbers to [-1; 1]    *)
(*                         expand == function from real numbers to extended   *)
(*                                   real numbers that cancels contract in    *)
(*                                   [-1; 1]                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x %:E" (at level 2, format "x %:E").
Reserved Notation "x +? y" (at level 50, format "x  +?  y").
Reserved Notation "x *? y" (at level 50, format "x  *?  y").
Reserved Notation "'\bar' x" (at level 2, format "'\bar'  x").
Reserved Notation "{ 'posnum' '\bar' R }" (at level 0,
  format "{ 'posnum'  '\bar'  R }").
Reserved Notation "{ 'nonneg' '\bar' R }" (at level 0,
  format "{ 'nonneg'  '\bar'  R }").

Declare Scope ereal_dual_scope.
Declare Scope ereal_scope.

Import Order.TTheory GRing.Theory Num.Theory.

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

Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ereal_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ereal_scope.

Section ERealOrder_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y : \bar R) (r : R).

Lemma lee_fin (r s : R) : (r%:E <= s%:E) = (r <= s)%R. Proof. by []. Qed.

Lemma lte_fin (r s : R) : (r%:E < s%:E) = (r < s)%R. Proof. by []. Qed.

Lemma lee01 : 0 <= 1 :> \bar R. Proof. by rewrite lee_fin. Qed.

Lemma lte01 : 0 < 1 :> \bar R. Proof. by rewrite lte_fin. Qed.

Lemma leeNy_eq x : (x <= -oo) = (x == -oo). Proof. by case: x. Qed.

Lemma leye_eq x : (+oo <= x) = (x == +oo). Proof. by case: x. Qed.

Lemma lt0y : (0 : \bar R) < +oo. Proof. exact: real0. Qed.

Lemma ltNy0 : -oo < (0 : \bar R). Proof. exact: real0. Qed.

Lemma le0y : (0 : \bar R) <= +oo. Proof. exact: real0. Qed.

Lemma leNy0 : -oo <= (0 : \bar R). Proof. exact: real0. Qed.

Lemma lt0e x : (0 < x) = (x != 0) && (0 <= x).
Proof. by case: x => [r| |]//; rewrite lte_fin lee_fin lt0r. Qed.

Lemma ereal_comparable x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (x >=< y)%O.
Proof.
move: x y => [x||] [y||] //; rewrite /Order.comparable !lee_fin -!realE.
- exact: real_comparable.
- by rewrite /lee/= => ->.
- by rewrite /lee/= => _ ->.
Qed.

Lemma real_ltry r : r%:E < +oo = (r \is Num.real). Proof. by []. Qed.
Lemma real_ltNyr r : -oo < r%:E = (r \is Num.real). Proof. by []. Qed.

Lemma real_leey x : (x <= +oo) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma real_leNye x : (-oo <= x) = (fine x \is Num.real).
Proof. by case: x => //=; rewrite real0. Qed.

Lemma gee0P x : 0 <= x <-> x = +oo \/ exists2 r, (r >= 0)%R & x = r%:E.
Proof.
split=> [|[->|[r r0 ->//]]]; last by rewrite real_leey/=.
by case: x => [r r0 | _ |//]; [right; exists r|left].
Qed.

End ERealOrder_numDomainType.

#[global] Hint Resolve lee01 lte01 : core.

Section ERealOrder_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y : \bar R) (r : R).

Lemma ltry r : r%:E < +oo. Proof. exact: num_real. Qed.

Lemma ltey x : (x < +oo) = (x != +oo).
Proof. by case: x => // r; rewrite ltry. Qed.

Lemma ltNyr r : -oo < r%:E. Proof. exact: num_real. Qed.

Lemma ltNye x : (-oo < x) = (x != -oo).
Proof. by case: x => // r; rewrite ltNyr. Qed.

Lemma leey x : x <= +oo. Proof. by case: x => //= r; exact: num_real. Qed.

Lemma leNye x : -oo <= x. Proof. by case: x => //= r; exact: num_real. Qed.

Definition lteey := (ltey, leey).

Definition lteNye := (ltNye, leNye).

Lemma le_total_ereal : totalPOrderMixin [porderType of \bar R].
Proof.
by move=> [?||][?||]//=; rewrite (ltEereal, leEereal)/= ?num_real ?le_total.
Qed.

Canonical ereal_latticeType := LatticeType (extended R) le_total_ereal.
Canonical ereal_distrLatticeType :=  DistrLatticeType (extended R) le_total_ereal.
Canonical ereal_orderType := OrderType (extended R) le_total_ereal.

Lemma ereal_blatticeMixin :
  Order.BLattice.mixin_of (Order.POrder.class (@ereal_porderType R)).
Proof. by exists -oo; exact leNye. Qed.
Canonical ereal_blatticeType := BLatticeType (extended R) ereal_blatticeMixin.

Lemma ereal_tblatticeMixin :
  Order.TBLattice.mixin_of (Order.POrder.class ereal_blatticeType).
Proof. by exists +oo; exact leey. Qed.
Canonical ereal_tblatticeType := TBLatticeType (extended R) ereal_tblatticeMixin.

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

Definition expe x n := iterop n mule x 1.

Definition enatmul x n := iterop n adde x 0.

Definition ednatmul x n := iterop n dual_adde x 0.

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
Notation "x ^+ n" := (expe x%dE n) : ereal_dual_scope.
Notation "x ^+ n" := (expe x n) : ereal_scope.
Notation "x *+ n" := (ednatmul x%dE n) : ereal_dual_scope.
Notation "x *+ n" := (enatmul x n) : ereal_scope.

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

Lemma lee0N1 : 0 <= (-1)%:E :> \bar R = false.
Proof. by rewrite lee_fin ler0N1. Qed.

Lemma lte0N1 : 0 < (-1)%:E :> \bar R = false.
Proof. by rewrite lte_fin ltr0N1. Qed.

Lemma lteN10 : - 1%E < 0 :> \bar R.
Proof. by rewrite lte_fin ltrN10. Qed.

Lemma leeN10 : - 1%E <= 0 :> \bar R.
Proof. by rewrite lee_fin lerN10. Qed.

Lemma fine_ge0 x : 0 <= x -> (0 <= fine x)%R.
Proof. by case: x. Qed.

Lemma fine_gt0 x : 0 < x < +oo -> (0 < fine x)%R.
Proof. by move: x => [x| |] //=; rewrite ?ltxx ?andbF// lte_fin => /andP[]. Qed.

Lemma fine_lt0 x : -oo < x < 0 -> (fine x < 0)%R.
Proof. by move: x => [x| |] //= /andP[_]; rewrite lte_fin. Qed.

Lemma fine_le0 x : x <= 0 -> (fine x <= 0)%R.
Proof. by case: x. Qed.

Lemma lee_tofin (r0 r1 : R) : (r0 <= r1)%R -> r0%:E <= r1%:E.
Proof. by []. Qed.

Lemma lte_tofin (r0 r1 : R) : (r0 < r1)%R -> r0%:E < r1%:E.
Proof. by []. Qed.

Lemma enatmul_pinfty n : +oo *+ n.+1 = +oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma enatmul_ninfty n : -oo *+ n.+1 = -oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma EFin_natmul (r : R) n : (r *+ n.+1)%:E = r%:E *+ n.+1.
Proof. by elim: n => //= n <-. Qed.

Lemma mule2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma expe2 x : x ^+ 2 = x * x. Proof. by []. Qed.

End ERealOrderTheory.
#[global] Hint Resolve leeN10 lteN10 : core.

Section finNumPred.
Context {R : numDomainType}.
Implicit Type (x : \bar R).

Definition fin_num := [qualify a x : \bar R | (x != -oo) && (x != +oo)].
Fact fin_num_key : pred_key fin_num. by []. Qed.
Canonical fin_num_keyd := KeyedQualifier fin_num_key.

Lemma fin_numE x : (x \is a fin_num) = (x != -oo) && (x != +oo).
Proof. by []. Qed.

Lemma fin_numP x : reflect ((x != -oo) /\ (x != +oo)) (x \is a fin_num).
Proof. by apply/(iffP idP) => [/andP//|/andP]. Qed.

Lemma fin_numEn x : (x \isn't a fin_num) = (x == -oo) || (x == +oo).
Proof. by rewrite fin_numE negb_and ?negbK. Qed.

Lemma fin_numPn x : reflect (x = -oo \/ x = +oo) (x \isn't a fin_num).
Proof. by rewrite fin_numEn; apply: (iffP orP) => -[]/eqP; by [left|right]. Qed.

Lemma fin_real x : -oo < x < +oo -> x \is a fin_num.
Proof. by move=> /andP[oox xoo]; rewrite fin_numE gt_eqF ?lt_eqF. Qed.

Lemma fin_num_abs x : (x \is a fin_num) = (`| x | < +oo)%E.
Proof. by rewrite fin_numE; case: x => // r; rewrite real_ltry normr_real. Qed.

End finNumPred.

Section ERealArithTh_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y z : \bar R) (r : R).

Lemma fine_le : {in fin_num &, {homo @fine R : x y / x <= y >-> (x <= y)%R}}.
Proof. by move=> [? [?| |]| |]. Qed.

Lemma fine_lt : {in fin_num &, {homo @fine R : x y / x < y >-> (x < y)%R}}.
Proof. by move=> [? [?| |]| |]. Qed.

Lemma fine_abse : {in fin_num, {morph @fine R : x / `|x| >-> `|x|%R}}.
Proof. by case. Qed.

Lemma abse_fin_num x : (`|x| \is a fin_num) = (x \is a fin_num).
Proof. by case: x. Qed.

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

Lemma fin_num_adde_defr x y : x \is a fin_num -> x +? y.
Proof. by move: x y => [x| |] [y | |]. Qed.

Lemma fin_num_adde_defl x y : y \is a fin_num -> x +? y.
Proof. by rewrite adde_defC; exact: fin_num_adde_defr. Qed.

Lemma adde_defN x y : x +? - y = - x +? y.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_defDr x y z : x +? y -> x +? z -> x +? (y + z).
Proof. by move: x y z => [x||] [y||] [z||]. Qed.

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

Lemma adde_def_sum I h t (P : pred I) (f : I -> \bar R) :
    {in P, forall i : I, f h +? f i} ->
  f h +? \sum_(j <- t | P j) f j.
Proof.
move=> fhi; elim/big_rec : _; first by rewrite fin_num_adde_defl.
by move=> i x Pi fhx; rewrite adde_defDr// fhi.
Qed.

Lemma addeAC : @right_commutative (\bar R) _ +%E.
Proof. exact: Monoid.mulmAC. Qed.

Lemma addeCA : @left_commutative (\bar R) _ +%E.
Proof. exact: Monoid.mulmCA. Qed.

Lemma addeACA : @interchange (\bar R) +%E +%E.
Proof. exact: Monoid.mulmACA. Qed.

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

Lemma oppe_inj : @injective (\bar R) _ -%E.
Proof. exact: inv_inj oppeK. Qed.

Lemma adde_defNN x y : - x +? - y = x +? y.
Proof. by rewrite adde_defN oppeK. Qed.

Lemma oppe_eq0 x : (- x == 0)%E = (x == 0)%E.
Proof. by rewrite -(can_eq oppeK) oppe0. Qed.

Lemma oppeD x y : x +? y -> - (x + y) = - x - y.
Proof. by move: x y => [x| |] [y| |] //= _; rewrite opprD. Qed.

Lemma fin_num_oppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move=> finy; rewrite oppeD// fin_num_adde_defl. Qed.

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

Canonical mule_mulmonoid := @Monoid.MulLaw _ _ mule mul0e mule0.

Lemma expeS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //=; rewrite mule1. Qed.

Lemma EFin_expe r n : (r ^+ n)%:E = r%:E ^+ n.
Proof. by elim: n => [//|n IHn]; rewrite exprS EFinM IHn expeS. Qed.

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

Lemma ltninfty_adde_def : {in [pred x | -oo < x] &, forall x y, x +? y}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma abse_eq0 x : (`|x| == 0) = (x == 0).
Proof. by move: x => [| |] //= r; rewrite !eqe normr_eq0. Qed.

Lemma abse0 : `|0| = 0 :> \bar R. Proof. by rewrite /abse normr0. Qed.

Lemma abse1 : `|1| = 1 :> \bar R. Proof. by rewrite /abse normr1. Qed.

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

Lemma fin_numN x : (- x \is a fin_num) = (x \is a fin_num).
Proof. by rewrite !fin_num_abs abseN. Qed.

Lemma oppeB x y : x +? - y -> - (x - y) = - x + y.
Proof. by move=> xy; rewrite oppeD// oppeK. Qed.

Lemma fin_num_oppeB x y : y \is a fin_num -> - (x - y) = - x + y.
Proof. by move=> ?; rewrite oppeB// adde_defN fin_num_adde_defl. Qed.

Lemma fin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma sum_fin_num (T : Type) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i \is a fin_num =
  all [pred x | x \is a fin_num] [seq f i | i <- s & P i].
Proof.
by rewrite -big_all big_map big_filter; exact: (big_morph _ fin_numD).
Qed.

Lemma sum_fin_numP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  reflect (forall i, i \in s -> P i -> f i \is a fin_num)
          (\sum_(i <- s | P i) f i \is a fin_num).
Proof.
rewrite sum_fin_num; apply: (iffP allP) => /=.
  by move=> + x xs Px; apply; rewrite map_f// mem_filter Px.
by move=> + _ /mapP[x /[!mem_filter]/andP[Px xs] ->]; apply.
Qed.

Lemma fin_numB x y :
  (x - y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fin_numM x y : x \is a fin_num -> y \is a fin_num ->
  x * y \is a fin_num.
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma fin_numX x n : x \is a fin_num -> x ^+ n \is a fin_num.
Proof. by elim: n x => // n ih x finx; rewrite expeS fin_numM// ih. Qed.

Lemma fineD : {in @fin_num R &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fineB : {in @fin_num R &, {morph fine : x y / x - y >-> (x - y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma fineM : {in @fin_num R &, {morph fine : x y / x * y >-> (x * y)%R}}.
Proof. by move=> [x| |] [y| |]. Qed.

Lemma fineK x : x \is a fin_num -> (fine x)%:E = x.
Proof. by case: x. Qed.

Lemma EFin_sum_fine (I : Type) s (P : pred I) (f : I -> \bar R) :
    (forall i, P i -> f i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (f i))%:E = \sum_(i <- s | P i) f i.
Proof.
by move=> h; rewrite -sumEFin; apply: eq_bigr => i Pi; rewrite fineK// h.
Qed.

Lemma sum_fine (I : Type) s (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> F i \is a fin_num) ->
  (\sum_(i <- s | P i) fine (F i) = fine (\sum_(i <- s | P i) F i))%R.
Proof. by move=> h; rewrite -EFin_sum_fine. Qed.

Lemma sumeN I s (P : pred I) (f : I -> \bar R) :
    {in P &, forall i j, f i +? f j} ->
  \sum_(i <- s | P i) - f i = - \sum_(i <- s | P i) f i.
Proof.
elim: s => [|a b ih h]; first by rewrite !big_nil oppe0.
rewrite !big_cons; case: ifPn => Pa; last by rewrite ih.
by rewrite oppeD ?ih// adde_def_sum// => i Pi; rewrite h.
Qed.

Lemma fin_num_sumeN I s (P : pred I) (f : I -> \bar R) :
    (forall i, P i -> f i \is a fin_num) ->
  \sum_(i <- s | P i) - f i = - \sum_(i <- s | P i) f i.
Proof.
by move=> h; rewrite sumeN// => i j Pi Pj; rewrite fin_num_adde_defl// h.
Qed.

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

Lemma addye x : x != -oo -> +oo + x = +oo. Proof. by case: x. Qed.

Lemma addey x : x != -oo -> x + +oo = +oo. Proof. by case: x. Qed.

Lemma addNye x : -oo + x = -oo. Proof. by []. Qed.

Lemma addeNy x : x + -oo = -oo. Proof. by case: x. Qed.

Lemma adde_Neq_pinfty x y : x != -oo -> y != -oo ->
  (x + y != +oo) = (x != +oo) && (y != +oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_Neq_ninfty x y : x != +oo -> y != +oo ->
  (x + y != -oo) = (x != -oo) && (y != -oo).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma adde_ss_eq0 x y : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  x + y == 0 = (x == 0) && (y == 0).
Proof. by move=> /orP[|] /andP[]; [exact: padde_eq0|exact: nadde_eq0]. Qed.

Lemma esum_eqNyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
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

Lemma esum_eqNy (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
apply/idP/idP => [/eqP/esum_eqNyP|/existsP[i /andP[Pi /eqP fi]]].
  by move=> -[i [_ Pi fi]]; apply/existsP; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_eqNyP; exists i.
Qed.

Lemma esum_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
move=> finoo; split=> [|[i [si Pi fi]]].
  rewrite big_seq_cond; elim/big_ind: _ => // [[?| |] [?| |]//|].
  by move=> i /andP[si Pi] fioo; exists i; rewrite si Pi fioo.
elim: s i Pi fi si => // h t ih i Pi fi.
rewrite inE => /predU1P[<-/=|it].
  rewrite big_cons Pi fi addye//.
  by apply/eqP => /esum_eqNyP[j [jt /finoo/negbTE/eqP]].
by rewrite big_cons; case: ifPn => Ph; rewrite (ih i)// addey// finoo.
Qed.

Lemma esum_eqy (I : finType) (P : {pred I}) (f : I -> \bar R) :
  (forall i, P i -> f i != -oo) ->
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
move=> fio; apply/idP/existsP => [/eqP /=|[/= i /andP[Pi /eqP fi]]].
  have {}fio : (forall i, P i -> f i != -oo) by move=> i Pi; exact: fio.
  by move=> /(esum_eqyP _ fio)[i [_ Pi fi]]; exists i; rewrite fi eqxx andbT.
by apply/eqP/esum_eqyP => //; exists i.
Qed.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqNyP`")]
Notation esum_ninftyP := esum_eqNyP.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqNy`")]
Notation esum_ninfty := esum_eqNy.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqyP`")]
Notation esum_pinftyP := esum_eqyP.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `esum_eqy`")]
Notation esum_pinfty := esum_eqy.

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

Lemma mulNyy : -oo * +oo = -oo :> \bar R. Proof. by rewrite /mule /= lt0y. Qed.

Lemma mulyNy : +oo * -oo = -oo :> \bar R. Proof. by rewrite muleC mulNyy. Qed.

Lemma mulyy : +oo * +oo = +oo :> \bar R. Proof. by rewrite /mule /= lt0y. Qed.

Lemma mulNyNy : -oo * -oo = +oo :> \bar R. Proof. by []. Qed.

Lemma real_mulry r : r \is Num.real -> r%:E * +oo = (Num.sg r)%:E * +oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|rn0].
move: rreal => /orP[|]; rewrite le_eqVlt.
  by rewrite eq_sym rn0/= => rgt0; rewrite lte_fin rgt0 gtr0_sg// lte01.
by rewrite rn0/= => rlt0; rewrite lt_def lt_geF// andbF ltr0_sg// lte0N1.
Qed.

Lemma real_mulyr r : r \is Num.real -> +oo * r%:E = (Num.sg r)%:E * +oo.
Proof. by move=> rreal; rewrite muleC real_mulry. Qed.

Lemma real_mulrNy r : r \is Num.real -> r%:E * -oo = (Num.sg r)%:E * -oo.
Proof.
move=> rreal; rewrite /mule/= !eqe sgr_eq0; case: ifP => [//|rn0].
move: rreal => /orP[|]; rewrite le_eqVlt.
  by rewrite eq_sym rn0/= => rgt0; rewrite lte_fin rgt0 gtr0_sg// lte01.
by rewrite rn0/= => rlt0; rewrite lt_def lt_geF// andbF ltr0_sg// lte0N1.
Qed.

Lemma real_mulNyr r : r \is Num.real -> -oo * r%:E = (Num.sg r)%:E * -oo.
Proof. by move=> rreal; rewrite muleC real_mulrNy. Qed.

Definition real_mulr_infty := (real_mulry, real_mulyr, real_mulrNy, real_mulNyr).

Lemma mulN1e x : - 1%E * x = - x.
Proof.
rewrite -EFinN /mule/=; case: x => [x||];
  do ?[by rewrite mulN1r|by rewrite eqe oppr_eq0 oner_eq0 lte_fin ltr0N1].
Qed.

Lemma muleN1 x : x * - 1%E = - x. Proof. by rewrite muleC mulN1e. Qed.

Lemma mule_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move: x y => [x||] [y||] x0 y0 //; rewrite /mule/= ?(lt0y,mulf_neq0)//;
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
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin, eqe, lte_fin, lt0y)//.
- exact: mulr_ge0.
- rewrite le_eqVlt => /predU1P[<- _|x0 _]; first by rewrite eqxx.
  by rewrite gt_eqF // x0 le0y.
- move=> _; rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite eqxx.
  by rewrite gt_eqF // y0 le0y.
Qed.

Lemma mule_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof.
by rewrite !lt_def => /andP[? ?] /andP[? ?]; rewrite mule_neq0 ?mule_ge0.
Qed.

Lemma mule_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
move: x y => [x||] [y||]//=; rewrite /mule/= ?(lee_fin, eqe, lte_fin)//.
- exact: mulr_le0.
- by rewrite lt_leAnge => -> _; case: ifP => _ //; rewrite andbF le0y.
- by rewrite lt_leAnge => _ ->; case: ifP => _ //; rewrite andbF le0y.
Qed.

Lemma mule_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
move: x y => [x| |] [y| |] //; rewrite /mule/= ?(lee_fin, lte_fin).
- exact: mulr_le0_ge0.
- by move=> x0 _; case: ifP => _ //; rewrite lt_leAnge /= x0 andbF leNy0.
- move=> _; rewrite le_eqVlt => /predU1P[<-|->]; first by rewrite eqxx.
  by case: ifP => _ //; rewrite leNy0.
- by rewrite lt0y leNy0.
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
      |by rewrite /mule/= lt0y
      |by rewrite real_mulr_infty ?realE -?lee_fin// /Num.sg;
          case: ifP; [|case: ifP]; rewrite ?mul0e /Order.comparable ?lexx;
          rewrite ?mulN1e ?leNy0 ?mul1e ?le0y
      |by rewrite mulNyNy /Order.comparable le0y].
Qed.

Lemma sqreD x y : x + y \is a fin_num ->
  (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof.
case: x y => [x||] [y||] // _.
by rewrite -EFinM -EFin_natmul -!EFin_expe -!EFinD sqrrD.
Qed.

Lemma abse_ge0 x : 0 <= `|x|.
Proof. by move: x => [x| |] /=; rewrite ?le0y ?lee_fin. Qed.

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
Proof. by rewrite dual_sumeE fin_num_sumeN// oppeK sumEFin. Qed.

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
Proof. exact: Monoid.mulmAC. Qed.

Lemma daddeCA : left_commutative (S := \bar R) +%dE.
Proof. exact: Monoid.mulmCA. Qed.

Lemma daddeACA : @interchange (\bar R) +%dE +%dE.
Proof. exact: Monoid.mulmACA. Qed.

Lemma realDed x y : (0%E >=< x)%O -> (0%E >=< y)%O -> (0%E >=< x + y)%O.
Proof. case: x y => [x||] [y||] //; exact: realD. Qed.

Lemma doppeD x y : x +? y -> - (x + y) = - x - y.
Proof. by move: x y => [x| |] [y| |] //= _; rewrite opprD. Qed.

Lemma fin_num_doppeD x y : y \is a fin_num -> - (x + y) = - x - y.
Proof. by move=> finy; rewrite doppeD// fin_num_adde_defl. Qed.

Lemma dsube0 x : x - 0 = x.
Proof. by move: x => [x| |] //; rewrite -dEFinB subr0. Qed.

Lemma dsub0e x : 0 - x = - x.
Proof. by move: x => [x| |] //; rewrite -dEFinB sub0r. Qed.

Lemma doppeB x y : x +? - y -> - (x - y) = - x + y.
Proof. by move=> xy; rewrite doppeD// oppeK. Qed.

Lemma fin_num_doppeB x y : y \is a fin_num -> - (x - y) = - x + y.
Proof. by move=> ?; rewrite doppeB// fin_num_adde_defl// fin_numN. Qed.

Lemma dfin_numD x y :
  (x + y \is a fin_num) = (x \is a fin_num) && (y \is a fin_num).
Proof. by move: x y => [x| |] [y| |]. Qed.

Lemma dfineD :
  {in (@fin_num R) &, {morph fine : x y / x + y >-> (x + y)%R}}.
Proof. by move=> [r| |] [s| |]. Qed.

Lemma dfineB : {in @fin_num R &, {morph fine : x y / x - y >-> (x - y)%R}}.
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

Lemma daddye x : +oo + x = +oo. Proof. by []. Qed.

Lemma daddey x : x + +oo = +oo. Proof. by case: x. Qed.

Lemma daddNye x : x != +oo -> -oo + x = -oo. Proof. by case: x. Qed.

Lemma daddeNy x : x != +oo -> x + -oo = -oo. Proof. by case: x. Qed.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed `daddye` and generalized")]
Lemma daddooe x : x != -oo -> +oo + x = +oo. Proof. by rewrite daddye. Qed.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed `daddey` and generalized")]
Lemma daddeoo x : x != -oo -> x + +oo = +oo. Proof. by rewrite daddey. Qed.

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

Lemma desum_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \sum_(i <- s | P i) f i = +oo <-> exists i, [/\ i \in s, P i & f i = +oo].
Proof.
rewrite dual_sumeE eqe_oppLRP /= esum_eqNyP.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_eqy (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (\sum_(i | P i) f i == +oo) = [exists i in P, f i == +oo].
Proof.
rewrite dual_sumeE eqe_oppLR esum_eqNy.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

Lemma desum_eqNyP
    (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (forall i, P i -> f i != +oo) ->
  \sum_(i <- s | P i) f i = -oo <-> exists i, [/\ i \in s, P i & f i = -oo].
Proof.
move=> fioo.
rewrite dual_sumeE eqe_oppLRP /= esum_eqyP => [|i Pi]; last first.
  by rewrite eqe_oppLR fioo.
by split=> -[i + /ltac:(exists i)] => [|] []; [|split]; rewrite // eqe_oppLRP.
Qed.

Lemma desum_eqNy (I : finType) (f : I -> \bar R) (P : {pred I}) :
  (forall i, f i != +oo) ->
  (\sum_(i | P i) f i == -oo) = [exists i in P, f i == -oo].
Proof.
move=> finoo.
rewrite dual_sumeE eqe_oppLR /= esum_eqy => [|i]; rewrite ?eqe_oppLR //.
by under eq_existsb => i do rewrite eqe_oppLR.
Qed.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `desum_eqNyP`")]
Notation desum_ninftyP := desum_eqNyP.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `desum_eqNy`")]
Notation desum_ninfty := desum_eqNy.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `desum_eqyP`")]
Notation desum_pinftyP := desum_eqyP.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `desum_eqy`")]
Notation desum_pinfty := desum_eqy.

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

Lemma ednatmul_pinfty n : +oo *+ n.+1 = +oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma ednatmul_ninfty n : -oo *+ n.+1 = -oo :> \bar R.
Proof. by elim: n => //= n ->. Qed.

Lemma EFin_dnatmul (r : R) n : (r *+ n.+1)%:E = r%:E *+ n.+1.
Proof. by elim: n => //= n <-. Qed.

Lemma ednatmulE x n : x *+ n = (x *+ n)%E.
Proof.
case: x => [x| |]; case: n => [//|n].
- by rewrite -EFin_natmul -EFin_dnatmul.
- by rewrite enatmul_pinfty ednatmul_pinfty.
- by rewrite enatmul_ninfty ednatmul_ninfty.
Qed.

Lemma dmule2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma sqredD x y : x + y \is a fin_num ->
  (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof.
case: x y => [x||] [y||] // _.
by rewrite -EFinM -EFin_dnatmul -!EFin_expe -!dEFinD sqrrD.
Qed.

End DualERealArithTh_numDomainType.

End DualAddTheoryNumDomain.

Section ERealArithTh_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y z u a b : \bar R) (r : R).

Lemma fin_numElt x : (x \is a fin_num) = (-oo < x < +oo).
Proof. by rewrite fin_numE -leye_eq -leeNy_eq -2!ltNge. Qed.

Lemma fin_numPlt x : reflect (-oo < x < +oo) (x \is a fin_num).
Proof. by rewrite fin_numElt; exact: idP. Qed.

Lemma ltey_eq x : (x < +oo) = (x \is a fin_num) || (x == -oo).
Proof. by case: x => // x //=; exact: ltry. Qed.

Lemma ltNye_eq x : (-oo < x) = (x \is a fin_num) || (x == +oo).
Proof. by case: x => // x //=; exact: ltNyr. Qed.

Lemma ge0_fin_numE x : 0 <= x -> (x \is a fin_num) = (x < +oo).
Proof. by move: x => [x| |] => // x0; rewrite fin_numElt ltNyr. Qed.

Lemma le0_fin_numE x : x <= 0 -> (x \is a fin_num) = (-oo < x).
Proof. by move: x => [x| |]//=; rewrite lee_fin => x0; rewrite ltNyr. Qed.

Lemma eqyP x : x = +oo <-> (forall A, (0 < A)%R -> A%:E <= x).
Proof.
split=> [-> // A A0|Ax]; first by rewrite leey.
apply/eqP; rewrite eq_le leey /= leNgt; apply/negP.
case: x Ax => [x Ax _|//|/(_ _ ltr01)//].
suff: ~ x%:E < (Order.max 0 x + 1)%:E.
  by apply; rewrite lte_fin ltr_spaddr// le_maxr lexx orbT.
by apply/negP; rewrite -leNgt; apply/Ax/ltr_spaddr; rewrite // le_maxr lexx.
Qed.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `eqyP`")]
Notation eq_pinftyP := eqyP.

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
    by rewrite (lt_le_trans _ (F0 _ Pj))// ltNyr.
  rewrite ltNge; apply/eqP; rewrite leye_eq; apply/eqP/negP => /eqP Fjoo.
  have PFninfty k : P k -> F k != -oo%E.
    by move=> Pk; rewrite gt_eqF// (lt_le_trans _ (F0 _ Pk))// ltNyr.
  have /esum_eqyP : exists i, [/\ i \in r, P i & F i = +oo%E] by exists j.
  by move=> /(_ PFninfty); rewrite PF0.
have ? : (\sum_(i <- r | P i) (fine \o F) i == 0)%R.
  apply/eqP/EFin_inj; rewrite big_seq_cond -sumEFin.
  rewrite (eq_bigr (fun i0 => F i0)); last first.
    move=> j /andP[jr Pj] /=; rewrite fineK//.
    by have := rPF _ jr; rewrite Pj implyTb.
  by rewrite -big_seq_cond PF0.
have /allP/(_ _ ir) : all (fun i => P i ==> ((fine \o F) i == 0))%R r.
  by rewrite -psumr_eq0// => j Pj/=; apply/fine_ge0/F0.
rewrite Pi implyTb => /= => /eqP Fi0.
rewrite -(@fineK _ (F i))//; last by have := rPF _ ir; rewrite Pi implyTb.
by rewrite Fi0.
Qed.

Lemma lte_add_pinfty x y : x < +oo -> y < +oo -> x + y < +oo.
Proof. by move: x y => -[r [r'| |]| |] // ? ?; rewrite -EFinD ltry. Qed.

Lemma lte_sum_pinfty I (s : seq I) (P : pred I) (f : I -> \bar R) :
  (forall i, P i -> f i < +oo) -> \sum_(i <- s | P i) f i < +oo.
Proof.
elim/big_ind : _ => [_|x y xoo yoo foo|i ?]; [exact: ltry| |exact].
by apply: lte_add_pinfty; [exact: xoo| exact: yoo].
Qed.

Lemma sube_gt0 x y : (0 < y - x) = (x < y).
Proof.
by move: x y => [r | |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin subr_gt0.
Qed.

Lemma sube_le0 x y : (y - x <= 0) = (y <= x).
Proof. by rewrite !leNgt sube_gt0. Qed.

Lemma suber_ge0 y x : y \is a fin_num -> (0 <= x - y) = (y <= x).
Proof.
by move: x y => [x| |] [y| |] //= _; rewrite ?(leey, lee_fin, subr_ge0).
Qed.

Lemma subre_ge0 x y : y \is a fin_num -> (0 <= y - x) = (x <= y).
Proof.
by move: x y => [x| |] [y| |] //=; rewrite ?(leey, leNye, lee_fin) //= subr_ge0.
Qed.

Lemma sube_ge0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (0 <= y - x) = (x <= y).
Proof. by move=> /orP[?|?]; [rewrite suber_ge0|rewrite subre_ge0]. Qed.

Lemma lte_oppl x y : (- x < y) = (- y < x).
Proof.
by move: x y => [r| |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin ltr_oppl.
Qed.

Lemma lte_oppr x y : (x < - y) = (y < - x).
Proof.
by move: x y => [r| |] [r'| |] //=; rewrite ?(ltry, ltNyr)// !lte_fin ltr_oppr.
Qed.

Lemma lee_oppr x y : (x <= - y) = (y <= - x).
Proof.
by move: x y => [r0| |] [r1| |] //=; rewrite ?(leey, leNye)// !lee_fin ler_oppr.
Qed.

Lemma lee_oppl x y : (- x <= y) = (- y <= x).
Proof.
by move: x y => [r0| |] [r1| |] //=; rewrite ?(leey, leNye)// !lee_fin ler_oppl.
Qed.

Lemma muleN x y : x * - y = - (x * y).
Proof.
move: x y => [x| |] [y| |] //=; rewrite /mule/=; try by rewrite ltry.
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

Lemma mulry r : r%:E * +oo%E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite [LHS]real_mulry// num_real. Qed.

Lemma mulyr r : +oo%E * r%:E = (Num.sg r)%:E * +oo%E.
Proof. by rewrite muleC mulry. Qed.

Lemma mulrNy r : r%:E * -oo%E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite [LHS]real_mulrNy// num_real. Qed.

Lemma mulNyr r : -oo%E * r%:E = (Num.sg r)%:E * -oo%E.
Proof. by rewrite muleC mulrNy. Qed.

Definition mulr_infty := (mulry, mulyr, mulrNy, mulNyr).

Lemma lte_mul_pinfty x y : 0 <= x -> x \is a fin_num -> y < +oo -> x * y < +oo.
Proof.
move: x y => [x| |] [y| |] // x0 xfin _; first by rewrite -EFinM ltry.
rewrite mulr_infty; move: x0; rewrite lee_fin le_eqVlt => /predU1P[<-|x0].
- by rewrite sgr0 mul0e ltry.
- by rewrite gtr0_sg // mul1e.
Qed.

Lemma mule_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
move: x y => [x| |] [y| |] //; rewrite ?lee_fin.
- by move=> x0 y0; rewrite !lte_fin; exact: mulr_ge0_gt0.
- rewrite le_eqVlt => /predU1P[<-|x0] _; first by rewrite mul0e ltxx.
  by rewrite ltry andbT mulr_infty gtr0_sg// mul1e lte_fin x0 ltry.
- move=> _; rewrite le_eqVlt => /predU1P[<-|x0].
    by rewrite mule0 ltxx andbC.
  by rewrite ltry/= mulr_infty gtr0_sg// mul1e lte_fin x0 ltry.
- by move=> _ _; rewrite mulyy ltry.
Qed.

Lemma gt0_mulye x : (0 < x -> +oo * x = +oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mulyy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulye x : (x < 0 -> +oo * x = -oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mulyNy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty ltr0_sg// mulN1e.
Qed.

Lemma gt0_mulNye x : (0 < x -> -oo * x = -oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mulNyy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulNye x : (x < 0 -> -oo * x = +oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mulNyNy.
by rewrite lte_fin => x0; rewrite muleC mulr_infty ltr0_sg// mulN1e.
Qed.

Lemma gt0_muley x : (0 < x -> x * +oo = +oo)%E.
Proof. by move=> /gt0_mulye; rewrite muleC; apply. Qed.

Lemma lt0_muley x : (x < 0 -> x * +oo = -oo)%E.
Proof. by move=> /lt0_mulye; rewrite muleC; apply. Qed.

Lemma gt0_muleNy x : (0 < x -> x * -oo = -oo)%E.
Proof. by move=> /gt0_mulNye; rewrite muleC; apply. Qed.

Lemma lt0_muleNy x : (x < 0 -> x * -oo = +oo)%E.
Proof. by move=> /lt0_mulNye; rewrite muleC; apply. Qed.

Lemma mule_eq_pinfty x y : (x * y == +oo) =
  [|| (x > 0) && (y == +oo), (x < 0) && (y == -oo),
     (x == +oo) && (y > 0) | (x == -oo) && (y < 0)].
Proof.
move: x y => [x| |] [y| |]; rewrite ?(lte_fin,andbF,andbT,orbF,eqxx,andbT)//=.
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP x 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulyy ltry.
- by rewrite mulyNy.
- by rewrite mulr_infty; have [/ltr0_sg|/gtr0_sg|] := ltgtP y 0%R;
    move=> ->; rewrite ?(mulN1e,mul1e,sgr0,mul0e).
- by rewrite mulNyy.
- by rewrite ltNyr.
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
move: a b x y=> [a| |] [b| |] [x| |] [y| |]; rewrite ?(ltry,ltNyr)//.
by rewrite !lte_fin; exact: ltr_add.
Qed.

Lemma lee_addl x y : 0 <= y -> x <= x + y.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ler_addl | move=> _; exact: leey].
Qed.

Lemma lee_addr x y : 0 <= y -> x <= y + x.
Proof. by rewrite addeC; exact: lee_addl. Qed.

Lemma gee_addl x y : y <= 0 -> x + y <= x.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ger_addl | move=> _; exact: leNye].
Qed.

Lemma gee_addr x y : y <= 0 -> y + x <= x.
Proof. rewrite addeC; exact: gee_addl. Qed.

Lemma lte_addl y x : y \is a fin_num -> (y < y + x) = (0 < x).
Proof.
by move: x y => [x| |] [y| |] _ //; rewrite ?ltry ?ltNyr // !lte_fin ltr_addl.
Qed.

Lemma lte_addr y x : y \is a fin_num -> (y < x + y) = (0 < x).
Proof. rewrite addeC; exact: lte_addl. Qed.

Lemma gte_subl y x : y \is a fin_num -> (y - x < y) = (0 < x).
Proof.
move: y x => [x| |] [y| |] _ //; rewrite addeC /= ?ltNyr ?ltry//.
by rewrite !lte_fin gtr_addr ltr_oppl oppr0.
Qed.

Lemma gte_subr y x : y \is a fin_num -> (- x + y < y) = (0 < x).
Proof. by rewrite addeC; exact: gte_subl. Qed.

Lemma gte_addl x y : x \is a fin_num -> (x + y < x) = (y < 0).
Proof.
by move: x y => [r| |] [s| |]// _; [rewrite !lte_fin gtr_addl|rewrite !ltNyr].
Qed.

Lemma gte_addr x y : x \is a fin_num -> (y + x < x) = (y < 0).
Proof. by rewrite addeC; exact: gte_addl. Qed.

Lemma lte_add2lE x a b : x \is a fin_num -> (x + a < x + b) = (a < b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin ltr_add2l.
Qed.

Lemma lee_add2l x a b : a <= b -> x + a <= x + b.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
- by rewrite !lee_fin ler_add2l.
- by move=> r _; exact: leey.
- by move=> -[b [|  |]// | []// | //] r oob; exact: leNye.
Qed.

Lemma lee_add2lE x a b : x \is a fin_num -> (x + a <= x + b) = (a <= b).
Proof.
move: a b x => [a| |] [b| |] [x| |] _ //; rewrite ?(leey, leNye)//.
by rewrite !lee_fin ler_add2l.
Qed.

Lemma lee_add2r x a b : a <= b -> a + x <= b + x.
Proof. rewrite addeC (addeC b); exact: lee_add2l. Qed.

Lemma lee_add a b x y : a <= b -> x <= y -> a + x <= b + y.
Proof.
move: a b x y => [a| |] [b| |] [x| |] [y| |]; rewrite ?(leey, leNye)//.
by rewrite !lee_fin; exact: ler_add.
Qed.

Lemma lte_le_add a b x y : b \is a fin_num -> a < x -> b <= y -> a + b < x + y.
Proof.
move: x y a b => [x| |] [y| |] [a| |] [b| |] _ //=; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin; exact: ltr_le_add.
Qed.

Lemma lee_lt_add a b x y : a \is a fin_num -> a <= x -> b < y -> a + b < x + y.
Proof. by move=> afin xa yb; rewrite (addeC a) (addeC x) lte_le_add. Qed.

Lemma lee_sub x y z u : x <= y -> u <= z -> x - z <= y - u.
Proof.
move: x y z u => -[x| |] -[y| |] -[z| |] -[u| |] //=; rewrite ?(leey,leNye)//.
by rewrite !lee_fin; exact: ler_sub.
Qed.

Lemma lte_le_sub z u x y : u \is a fin_num ->
  x < z -> u <= y -> x - y < z - u.
Proof.
move: z u x y => [z| |] [u| |] [x| |] [y| |] _ //=; rewrite ?(ltry, ltNyr)//.
by rewrite !lte_fin => xltr tley; apply: ltr_le_add; rewrite // ler_oppl opprK.
Qed.

Lemma lte_pmul2r z : z \is a fin_num -> 0 < z -> {mono *%E^~ z : x y / x < y}.
Proof.
move: z => [z| |] _ // z0 [x| |] [y| |] //.
- by rewrite !lte_fin ltr_pmul2r.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty gtr0_sg// mul1e ltNge leNye ltNge leNye.
- by rewrite mulr_infty gtr0_sg// mul1e ltNge leey ltNge leey.
- by rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltNyr.
- by rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// mul1e.
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
move=> QP PQf; rewrite big_mkcond [leRHS]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_npos_subset I (s : seq I) (P Q : {pred I}) (f : I -> \bar R) :
  {subset Q <= P} -> {in [predD P & Q], forall i, f i <= 0} ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | Q i) f i.
Proof.
move=> QP PQf; rewrite big_mkcond [leRHS]big_mkcond lee_sum// => i.
by move/implyP: (QP i); move: (PQf i); rewrite !inE -!topredE/=; do !case: ifP.
Qed.

Lemma lee_sum_nneg (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> 0 <= f i) ->
  \sum_(i <- s | P i && Q i) f i <= \sum_(i <- s | P i) f i.
Proof.
move=> PQf; rewrite [leRHS](bigID Q) /= -[leLHS]adde0 lee_add //.
by rewrite sume_ge0// => i /andP[]; exact: PQf.
Qed.

Lemma lee_sum_npos (I : eqType) (s : seq I) (P Q : pred I)
  (f : I -> \bar R) : (forall i, P i -> ~~ Q i -> f i <= 0) ->
  \sum_(i <- s | P i) f i <= \sum_(i <- s | P i && Q i) f i.
Proof.
move=> PQf; rewrite [leLHS](bigID Q) /= -[leRHS]adde0 lee_add //.
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
  (forall n, P n -> f n <= 0) ->
  {homo (fun n => \sum_(i < n | P i) (f i)) : i j / (i <= j)%N >-> j <= i}.
Proof.
move=> f0 m n ?; rewrite [leRHS](big_ord_widen_cond n) // big_mkcondr /=.
by rewrite lee_sum // => i ?; case: ifP => // _; exact: f0.
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
move=> AB f0; rewrite [leRHS]big_mkcond (big_fsetID _ (mem A) B) /=.
rewrite -[leLHS]adde0 lee_add //.
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
rewrite -[leRHS]adde0 lee_add //.
  rewrite -big_mkcond /= {3}(_ : A = [fset x in B | x \in A]%fset) //.
  by apply/fsetP=> t; rewrite !inE /= andbC; case: (boolP (_ \in _)) => // /AB.
rewrite big_fset /= big_seq_cond sume_le0 // => t /andP[tB tA].
by case: ifPn => // Pt; rewrite f0 // !inE tA.
Qed.

Lemma lte_subl_addr x y z : y \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltry ?ltNyr //.
by rewrite !lte_fin ltr_subl_addr.
Qed.

Lemma lte_subl_addl x y z : y \is a fin_num -> (x - y < z) = (x < y + z).
Proof. by move=> ?; rewrite lte_subl_addr// addeC. Qed.

Lemma lte_subr_addr x y z : z \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltr_subr_addr.
Qed.

Lemma lte_subr_addl x y z : z \is a fin_num -> (x < y - z) = (z + x < y).
Proof. by move=> ?; rewrite lte_subr_addr// addeC. Qed.

Lemma lte_subel_addr x y z : x \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltr_subl_addr.
Qed.

Lemma lte_subel_addl x y z : x \is a fin_num -> (x - y < z) = (x < y + z).
Proof. by move=> ?; rewrite lte_subel_addr// addeC. Qed.

Lemma lte_suber_addr x y z : x \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?ltNyr ?ltry //.
by rewrite !lte_fin ltr_subr_addr.
Qed.

Lemma lte_suber_addl x y z : x \is a fin_num -> (x < y - z) = (z + x < y).
Proof. by move=> ?; rewrite lte_suber_addr// addeC. Qed.

Lemma lee_subl_addr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?leey ?leNye //.
by rewrite !lee_fin ler_subl_addr.
Qed.

Lemma lee_subl_addl x y z : y \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof. by move=> ?; rewrite lee_subl_addr// addeC. Qed.

Lemma lee_subr_addr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?leNye ?leey //.
by rewrite !lee_fin ler_subr_addr.
Qed.

Lemma lee_subr_addl x y z : z \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof. by move=> ?; rewrite lee_subr_addr// addeC. Qed.

Lemma lee_subel_addr x y z : z \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
move: x y z => [x| |] [y| |] [z| |] _ //=; rewrite ?leey ?leNye //.
by rewrite !lee_fin ler_subl_addr.
Qed.

Lemma lee_subel_addl x y z : z \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof. by move=> ?; rewrite lee_subel_addr// addeC. Qed.

Lemma lee_suber_addr x y z : y \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
move: y x z => [y| |] [x| |] [z| |] _ //=; rewrite ?leNye ?leey //.
by rewrite !lee_fin ler_subr_addr.
Qed.

Lemma lee_suber_addl x y z : y \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof. by move=> ?; rewrite lee_suber_addr// addeC. Qed.

Lemma subre_lt0 x y : x \is a fin_num -> (x - y < 0) = (x < y).
Proof. by move=> ?; rewrite lte_subel_addr// add0e. Qed.

Lemma suber_lt0 x y : y \is a fin_num -> (x - y < 0) = (x < y).
Proof. by move=> ?; rewrite lte_subl_addl// adde0. Qed.

Lemma sube_lt0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (x - y < 0) = (x < y).
Proof. by move=> /orP[?|?]; [rewrite subre_lt0|rewrite suber_lt0]. Qed.

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
move=> x y z.
wlog x0 : x y z / 0 < x => [hwlog|].
  have [x0| |->] := ltgtP x 0; [ |exact: hwlog|by rewrite !mul0e].
  by apply: oppe_inj; rewrite -!mulNe hwlog ?oppe_gt0.
wlog y0 : x y z x0 / 0 < y => [hwlog|].
  have [y0| |->] := ltgtP y 0; [ |exact: hwlog|by rewrite !(mul0e, mule0)].
  by apply: oppe_inj; rewrite -muleN -2!mulNe -muleN hwlog ?oppe_gt0.
wlog z0 : x y z x0 y0 / 0 < z => [hwlog|].
  have [z0| |->] := ltgtP z 0; [ |exact: hwlog|by rewrite !mule0].
  by apply: oppe_inj; rewrite -!muleN hwlog ?oppe_gt0.
case: x x0 => [x x0| |//]; last by rewrite !gt0_mulye ?mule_gt0.
case: y y0 => [y y0| |//]; last by rewrite gt0_mulye // muleC !gt0_mulye.
case: z z0 => [z z0| |//]; last by rewrite !gt0_muley ?mule_gt0.
by rewrite /mule/= mulrA.
Qed.

Local Open Scope ereal_scope.

Canonical mule_monoid := Monoid.Law muleA mul1e mule1.
Canonical mule_comoid := Monoid.ComLaw muleC.

Lemma muleCA : left_commutative ( *%E : \bar R -> \bar R -> \bar R ).
Proof. exact: Monoid.mulmCA. Qed.

Lemma muleAC : right_commutative ( *%E : \bar R -> \bar R -> \bar R ).
Proof. exact: Monoid.mulmAC. Qed.

Lemma muleACA : interchange (@mule R) (@mule R).
Proof. exact: Monoid.mulmACA. Qed.

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
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP t0.
- by rewrite ltry.
- rewrite !eqe paddr_eq0 //; move: s0; rewrite lee_fin.
  case: (ltgtP s) => //= [s0|->{s}] _; rewrite ?add0e.
  + rewrite lte_fin -[in LHS](addr0 0%R) ltr_le_add // lte_fin s0.
    by case: ltgtP t0 => // [t0|[<-{t}]].
  + by move: t0; rewrite lee_fin; case: (ltgtP t).
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP s0.
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
- by rewrite ltry; case: ltgtP s0.
- by rewrite ltry; case: ltgtP t0.
- by rewrite ltry.
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
- by move=> _; rewrite /mule/= eqe => r1; rewrite leey.
Qed.

Lemma lee_wpmul2r x : 0 <= x -> {homo *%E^~ x : y z / y <= z}.
Proof.
move: x => [x|_|//].
  rewrite lee_fin le_eqVlt => /predU1P[<- y z|x0]; first by rewrite 2!mule0.
  move=> [y| |] [z| |]//; first by rewrite !lee_fin// ler_pmul2r.
  - by move=> _; rewrite mulr_infty gtr0_sg// mul1e leey.
  - by move=> _; rewrite mulr_infty gtr0_sg// mul1e leNye.
  - by move=> _; rewrite 2!mulr_infty gtr0_sg// 2!mul1e.
move=> [y| |] [z| |]//.
- rewrite lee_fin => yz.
  have [z0|z0|] := ltgtP 0%R z.
  + by rewrite [leRHS]mulr_infty gtr0_sg// mul1e leey.
  + by rewrite mulr_infty ltr0_sg// ?(le_lt_trans yz)// [leRHS]mulr_infty ltr0_sg.
  + move=> z0; move: yz; rewrite -z0 mul0e le_eqVlt => /predU1P[->|y0].
      by rewrite mul0e.
    by rewrite mulr_infty ltr0_sg// mulN1e leNye.
  + by move=> _; rewrite mulyy leey.
  + by move=> _; rewrite mulNyy leNye.
  + by move=> _; rewrite mulNyy leNye.
Qed.

Lemma lee_wpmul2l x : 0 <= x -> {homo *%E x : y z / y <= z}.
Proof. by move=> x0 y z yz; rewrite !(muleC x) lee_wpmul2r. Qed.

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

Lemma fin_num_sume_distrr (I : Type) (s : seq I) x (P : pred I)
    (F : I -> \bar R) :
  x \is a fin_num -> {in P &, forall i j, F i +? F j} ->
    x * (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) x * F i.
Proof.
move=> xfin PF; elim: s => [|h t ih]; first by rewrite !big_nil mule0.
rewrite !big_cons; case: ifPn => Ph //.
by rewrite muleDr// ?ih// adde_def_sum// => i Pi; rewrite PF.
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

Lemma lte_absl (x y : \bar R) : (`|x| < y)%E = (- y < x < y)%E.
Proof.
by move: x y => [x| |] [y| |] //=; rewrite ?lte_fin ?ltry ?ltNyr// ltr_norml.
Qed.

Lemma eqe_absl x y : (`|x| == y) = ((x == y) || (x == - y)) && (0 <= y).
Proof.
by move: x y => [x| |] [y| |] //=; rewrite? leey// !eqe eqr_norml lee_fin.
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
    by rewrite (ger0_norm r0)// gee0_abs// mule_ge0// leey.
  rewrite (ltr0_norm r0)// lte0_abs// ?EFinN ?mulNe//.
  by rewrite mule_lt0 /= eqe lt_eqF//= lte_fin r0.
move=> [x| |] [y| |] //=; first by rewrite normrM.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite muleC xoo muleC.
- by rewrite mulyy.
- by rewrite mulyy mulyNy.
- by rewrite -abseN -muleNN abseN -EFinN xoo normrN.
- by rewrite mulyy mulNyy.
- by rewrite mulyy.
Qed.

Lemma fine_max :
  {in fin_num &, {mono @fine R : x y / maxe x y >-> (Num.max x y)%:E}}.
Proof.
by move=> [x| |] [y| |]//= _ _; apply/esym; have [ab|ba] := leP x y;
  [apply/max_idPr; rewrite lee_fin|apply/max_idPl; rewrite lee_fin ltW].
Qed.

Lemma EFin_max : {morph (@EFin R) : r s / Num.max r s >-> maxe r s}.
Proof. by move=> a b /=; rewrite -fine_max. Qed.

Lemma fine_min :
  {in fin_num &, {mono @fine R : x y / mine x y >-> (Num.min x y)%:E}}.
Proof.
by move=> [x| |] [y| |]//= _ _; apply/esym; have [ab|ba] := leP x y;
  [apply/min_idPl; rewrite lee_fin|apply/min_idPr; rewrite lee_fin ltW].
Qed.

Lemma EFin_min : {morph (@EFin R) : r s / Num.min r s >-> mine r s}.
Proof. by move=> a b /=; rewrite -fine_min. Qed.

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

Lemma maxye : left_zero (+oo : \bar R) maxe.
Proof. by move=> x; have [|//] := leP +oo x; rewrite leye_eq => /eqP. Qed.

Lemma maxey : right_zero (+oo : \bar R) maxe.
Proof. by move=> x; rewrite maxC maxye. Qed.

Lemma maxNye : left_id (-oo : \bar R) maxe.
Proof. by move=> x; have [//|] := leP -oo x; rewrite ltNge leNye. Qed.

Lemma maxeNy : right_id (-oo : \bar R) maxe.
Proof. by move=> x; rewrite maxC maxNye. Qed.

Canonical maxe_monoid := Monoid.Law maxA maxNye maxeNy.
Canonical maxe_comoid := Monoid.ComLaw maxC.

Lemma minNye : left_zero (-oo : \bar R) mine.
Proof. by move=> x; have [|//] := leP x -oo; rewrite leeNy_eq => /eqP. Qed.

Lemma mineNy : right_zero (-oo : \bar R) mine.
Proof. by move=> x; rewrite minC minNye. Qed.

Lemma minye : left_id (+oo : \bar R) mine.
Proof. by move=> x; have [//|] := leP x +oo; rewrite ltNge leey. Qed.

Lemma miney : right_id (+oo : \bar R) mine.
Proof. by move=> x; rewrite minC minye. Qed.

Canonical mine_monoid := Monoid.Law minA minye miney.
Canonical mine_comoid := Monoid.ComLaw minC.

Lemma oppe_max : {morph -%E : x y / maxe x y >-> mine x y : \bar R}.
Proof.
move=> [x| |] [y| |] //=.
- by rewrite -fine_max//= -fine_min//= oppr_max.
- by rewrite maxey mineNy.
- by rewrite miney.
- by rewrite minNye.
- by rewrite maxNye minye.
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
move: x y => [x| |] [y| |] //; last by rewrite mulyy.
- by rewrite -EFinM 3!lee_fin; exact: ler_pemull.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulr_infty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[<- _|y0 _]; first by rewrite mule0.
  by rewrite mulr_infty gtr0_sg// mul1e leey.
Qed.

Lemma lee_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof.
move: x y => [x| |] [y| |] //; last by rewrite mulyNy.
- by rewrite -EFinM 3!lee_fin; exact: ler_nemull.
- move=> _; rewrite lee_fin => x1.
  by rewrite mulr_infty gtr0_sg ?mul1e// (lt_le_trans _ x1).
- rewrite lee_fin le_eqVlt => /predU1P[-> _|y0 _]; first by rewrite mule0.
  by rewrite mulr_infty ltr0_sg// mulN1e leNye.
Qed.

Lemma lee_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> y0 x1; rewrite muleC lee_pemull. Qed.

Lemma lee_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> y0 x1; rewrite muleC lee_nemull. Qed.

Lemma mule_natl x n : n%:R%:E * x = x *+ n.
Proof.
elim: n => [|n]; first by rewrite mul0e.
move: x => [x| |] ih.
- by rewrite -EFinM mulr_natl EFin_natmul.
- by rewrite mulry gtr0_sg// mul1e enatmul_pinfty.
- by rewrite mulrNy gtr0_sg// mul1e enatmul_ninfty.
Qed.

Lemma lte_pmul x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move: x1 y1 x2 y2 => [x1| |] [y1| |] [x2| |] [y2| |] //;
    rewrite !(lte_fin,lee_fin).
- by move=> *; rewrite ltr_pmul.
- move=> x10 x20 xy1 xy2.
  by rewrite mulry gtr0_sg ?mul1e -?EFinM ?ltry// (le_lt_trans _ xy1).
- move=> x10 x20 xy1 xy2.
  by rewrite mulyr gtr0_sg ?mul1e -?EFinM ?ltry// (le_lt_trans _ xy2).
- by move=> *; rewrite mulyy -EFinM ltry.
Qed.

Lemma lee_pmul x1 y1 x2 y2 : 0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 ->
  x1 * x2 <= y1 * y2.
Proof.
move: x1 y1 x2 y2 => [x1| |] [y1| |] [x2| |] [y2| |] //; rewrite !lee_fin.
- exact: ler_pmul.
- rewrite le_eqVlt => /predU1P[<- x20 y10 _|x10 x20 xy1 _].
    by rewrite mul0e mule_ge0// leey.
  by rewrite mulr_infty gtr0_sg// ?mul1e ?leey// (lt_le_trans x10).
- rewrite le_eqVlt => /predU1P[<- _ y10 _|x10 _ xy1 _].
    by rewrite mul0e mule_ge0// leey.
  rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg// ?mul1e//.
  exact: (lt_le_trans x10).
- move=> x10; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulr_infty mule_ge0// ?leey// lee_fin sgr_ge0.
  by rewrite mulr_infty gtr0_sg ?mul1e ?leey// (lt_le_trans x20).
- by move=> x10 x20 _ _; rewrite mulyy leey.
- rewrite le_eqVlt => /predU1P[<- _ _ _|x10 _ _ _].
    by rewrite mulyy mul0e leey.
  by rewrite mulyy mulr_infty gtr0_sg// mul1e.
- move=> _; rewrite le_eqVlt => /predU1P[<- _ y20|x20 _ xy2].
    by rewrite mule0 mulr_infty mule_ge0// ?leey// lee_fin sgr_ge0.
  rewrite mulr_infty gtr0_sg// mul1e mulr_infty gtr0_sg ?mul1e//.
  exact: (lt_le_trans x20).
- move=> _; rewrite le_eqVlt => /predU1P[<- _ _|x20 _ _].
    by rewrite mule0 mulyy leey.
  by rewrite mulr_infty gtr0_sg// mul1e// mulyy.
Qed.

Lemma lee_pmul2l x : x \is a fin_num -> 0 < x -> {mono *%E x : x y / x <= y}.
Proof.
move: x => [x _|//|//] /[!(@lte_fin R)] x0 [y| |] [z| |].
- by rewrite -2!EFinM 2!lee_fin ler_pmul2l.
- by rewrite mulry gtr0_sg// mul1e 2!leey.
- by rewrite mulrNy gtr0_sg// mul1e 2!leeNy_eq.
- by rewrite mulry gtr0_sg// mul1e 2!leye_eq.
- by rewrite mulry gtr0_sg// mul1e.
- by rewrite mulry mulrNy gtr0_sg// mul1e mul1e.
- by rewrite mulrNy gtr0_sg// mul1e 2!leNye.
- by rewrite mulrNy mulry gtr0_sg// 2!mul1e.
- by rewrite mulrNy gtr0_sg// mul1e.
Qed.

Lemma lee_pmul2r x : x \is a fin_num -> 0 < x -> {mono *%E^~ x : x y / x <= y}.
Proof. by move=> xfin x0 y z; rewrite -2!(muleC x) lee_pmul2l. Qed.

Lemma lee_sqr x y : 0 <= x -> 0 <= y -> (x ^+ 2 <= y ^+ 2) = (x <= y).
Proof.
move=> xge0 yge0; apply/idP/idP; rewrite !expe2.
  by apply: contra_le => yltx; apply: lte_pmul.
by move=> xley; apply: lee_pmul.
Qed.

Lemma lte_sqr x y : 0 <= x -> 0 <= y -> (x ^+ 2 < y ^+ 2) = (x < y).
Proof.
move=> xge0 yge0; apply/idP/idP; rewrite !expe2.
  by apply: contra_lt => yltx; apply: lee_pmul.
by move=> xley; apply: lte_pmul.
Qed.

Lemma lee_sqrE x y : 0 <= y -> x ^+ 2 <= y ^+ 2 -> x <= y.
Proof.
move=> yge0; have [xge0|xlt0 x2ley2] := leP 0 x; first by rewrite lee_sqr.
exact: le_trans (ltW xlt0) _.
Qed.

Lemma lte_sqrE x y : 0 <= y -> x ^+ 2 < y ^+ 2 -> x < y.
Proof.
move=> yge0; have [xge0|xlt0 x2ley2] := leP 0 x; first by rewrite lte_sqr.
exact: lt_le_trans xlt0 _.
Qed.

Lemma sqre_ge0 x : 0 <= x ^+ 2.
Proof.
by case: x => [x||]; rewrite /= ?mulyy ?mulNyNy ?le0y//; apply: sqr_ge0.
Qed.

Lemma lee_paddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0e lee_add. Qed.

Lemma lte_paddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> x0 /lt_le_trans; apply; rewrite lee_paddl. Qed.

Lemma lee_paddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite addeC lee_paddl. Qed.

Lemma lte_paddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addeC lte_paddl. Qed.

Lemma lte_spaddre z x y : z \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry)//.
exact: ltr_spaddr.
Qed.

Lemma lte_spadder z x y : x \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_spaddr.
Qed.

End ERealArithTh_realDomainType.
Arguments lee_sum_nneg_ord {R}.
Arguments lee_sum_npos_ord {R}.
Arguments lee_sum_nneg_natr {R}.
Arguments lee_sum_npos_natr {R}.
Arguments lee_sum_nneg_natl {R}.
Arguments lee_sum_npos_natl {R}.
#[global] Hint Extern 0 (is_true (0 <= `| _ |)%E) => solve [apply: abse_ge0] : core.

#[deprecated(since="mathcomp-analysis 0.6", note="Use lte_spaddre instead.")]
Notation lte_spaddr := lte_spaddre.

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

Lemma dsube_le0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (y - x <= 0) = (y <= x).
Proof. by move=> /orP[?|?]; [rewrite dsuber_le0|rewrite dsubre_le0]. Qed.

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

Lemma lte_daddl y x : y \is a fin_num -> (y < y + x) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lte_oppr; exact: gte_subl. Qed.

Lemma lte_daddr y x : y \is a fin_num -> (y < x + y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lte_oppr addeC; exact: gte_subl. Qed.

Lemma gte_dsubl y x : y \is a fin_num -> (y - x < y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lte_oppl oppeK; exact: lte_addl. Qed.

Lemma gte_dsubr y x : y \is a fin_num -> (- x + y < y) = (0 < x).
Proof. by rewrite -fin_numN dual_addeE lte_oppl oppeK; exact: lte_addr. Qed.

Lemma gte_daddl x y : x \is a fin_num -> (x + y < x) = (y < 0).
Proof.
by rewrite -fin_numN dual_addeE lte_oppl -oppe0 lte_oppr; exact: lte_addl.
Qed.

Lemma gte_daddr x y : x \is a fin_num -> (y + x < x) = (y < 0).
Proof. by rewrite daddeC; exact: gte_daddl. Qed.

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

Lemma lte_le_dadd a b x y : b \is a fin_num -> a < x -> b <= y -> a + b < x + y.
Proof. rewrite !dual_addeE lte_opp -lte_opp; exact: lte_le_sub. Qed.

Lemma lee_lt_dadd a b x y : a \is a fin_num -> a <= x -> b < y -> a + b < x + y.
Proof. by move=> afin xa yb; rewrite (daddeC a) (daddeC x) lte_le_dadd. Qed.

Lemma lee_dsub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. rewrite !dual_addeE lee_oppl oppeK -lee_opp !oppeK; exact: lee_add. Qed.

Lemma lte_le_dsub z u x y : u \is a fin_num -> x < z -> u <= y -> x - y < z - u.
Proof.
rewrite !dual_addeE lte_opp !oppeK -lte_opp; exact: lte_le_add.
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

Lemma lte_dsubl_addl x y z : y \is a fin_num -> (x - y < z) = (x < y + z).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_subr_addl ?fin_numN.
Qed.

Lemma lte_dsubr_addr x y z : z \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_subl_addr ?fin_numN.
Qed.

Lemma lte_dsubr_addl x y z : z \is a fin_num -> (x < y - z) = (z + x < y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_subl_addl ?fin_numN.
Qed.

Lemma lte_dsuber_addr x y z : y \is a fin_num -> (x < y - z) = (x + z < y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_subel_addr ?fin_numN.
Qed.

Lemma lte_dsuber_addl x y z : y \is a fin_num -> (x < y - z) = (z + x < y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_subel_addl ?fin_numN.
Qed.

Lemma lte_dsubel_addr x y z : z \is a fin_num -> (x - y < z) = (x < z + y).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_suber_addr ?fin_numN.
Qed.

Lemma lte_dsubel_addl x y z : z \is a fin_num -> (x - y < z) = (x < y + z).
Proof.
by move=> ?; rewrite !dual_addeE lte_oppl lte_oppr lte_suber_addl ?fin_numN.
Qed.

Lemma lee_dsubl_addr x y z : y \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subr_addr ?fin_numN.
Qed.

Lemma lee_dsubl_addl x y z : y \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subr_addl ?fin_numN.
Qed.

Lemma lee_dsubr_addr x y z : z \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subl_addr ?fin_numN.
Qed.

Lemma lee_dsubr_addl x y z : z \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subl_addl ?fin_numN.
Qed.

Lemma lee_dsubel_addr x y z : x \is a fin_num -> (x - y <= z) = (x <= z + y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_suber_addr ?fin_numN.
Qed.

Lemma lee_dsubel_addl x y z : x \is a fin_num -> (x - y <= z) = (x <= y + z).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_suber_addl ?fin_numN.
Qed.

Lemma lee_dsuber_addr x y z : x \is a fin_num -> (x <= y - z) = (x + z <= y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subel_addr ?fin_numN.
Qed.

Lemma lee_dsuber_addl x y z : x \is a fin_num -> (x <= y - z) = (z + x <= y).
Proof.
by move=> ?; rewrite !dual_addeE lee_oppl lee_oppr lee_subel_addl ?fin_numN.
Qed.

Lemma dsuber_gt0 x y : x \is a fin_num -> (0 < y - x) = (x < y).
Proof. by move=> ?; rewrite lte_dsubr_addl// dadde0. Qed.

Lemma dsubre_gt0 x y : y \is a fin_num -> (0 < y - x) = (x < y).
Proof. by move=> ?; rewrite lte_dsuber_addl// dadde0. Qed.

Lemma dsube_gt0 x y : (x \is a fin_num) || (y \is a fin_num) ->
  (0 < y - x) = (x < y).
Proof. by move=> /orP[?|?]; [rewrite dsuber_gt0|rewrite dsubre_gt0]. Qed.

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

Lemma dmule_natl x n : n%:R%:E * x = x *+ n.
Proof. by rewrite mule_natl ednatmulE. Qed.

Lemma lee_pdaddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]dadd0e lee_dadd. Qed.

Lemma lte_pdaddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> x0 /lt_le_trans; apply; rewrite lee_pdaddl. Qed.

Lemma lee_pdaddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite daddeC lee_pdaddl. Qed.

Lemma lte_pdaddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite daddeC lte_pdaddl. Qed.

Lemma lte_spdaddre z x y : z \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_spaddr.
Qed.

Lemma lte_spdadder z x y : x \is a fin_num -> 0 < y -> z <= x -> z < x + y.
Proof.
move: z y x => [z| |] [y| |] [x| |] _ //=; rewrite ?(lte_fin,ltry,ltNyr)//.
exact: ltr_spaddr.
Qed.

End DualERealArithTh_realDomainType.
Arguments lee_dsum_nneg_ord {R}.
Arguments lee_dsum_npos_ord {R}.
Arguments lee_dsum_nneg_natr {R}.
Arguments lee_dsum_npos_natr {R}.
Arguments lee_dsum_nneg_natl {R}.
Arguments lee_dsum_npos_natl {R}.

End DualAddTheoryRealDomain.

Lemma lee_opp2 {R : numDomainType} : {mono @oppe R : x y /~ x <= y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lee_fin !ler_opp2.
  by rewrite  /Order.le/= realN.
by rewrite /Order.le/= realN.
Qed.

Lemma lte_opp2 {R : numDomainType} : {mono @oppe R : x y /~ x < y}.
Proof.
move=> x y; case: x y => [?||] [?||] //; first by rewrite !lte_fin !ltr_opp2.
  by rewrite  /Order.lt/= realN.
by rewrite /Order.lt/= realN.
Qed.

Section realFieldType_lemmas.
Variable R : realFieldType.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma lee_adde x y : (forall e : {posnum R}, x <= y + e%:num%:E) -> x <= y.
Proof.
move: x y => [x||] [y||] // xleye; rewrite ?leNye ?leey//; last first.
- exact: (le_trans (xleye 1%:pos%R)).
- by move: (!! xleye 1%:pos%R).
- by move: (!! xleye 1%:pos%R).
rewrite leNgt; apply/negP => yltx.
have xmy_gt0 : (0 < (x - y) / 2)%R by rewrite ltr_pdivl_mulr// mul0r subr_gt0.
move: (xleye (PosNum xmy_gt0)); apply/negP; rewrite -ltNge /= -EFinD lte_fin.
rewrite [Y in (Y + _)%R]splitr [X in (_ < X)%R]splitr.
by rewrite -!mulrDl ltr_pmul2r// addrCA addrK ltr_add2l.
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
- by rewrite leey.
- by have := h _ h01.
- by have := h _ h01; rewrite mulr_infty sgrV gtr0_sg // mul1e.
- by have := h _ h01; rewrite mulr_infty sgrV gtr0_sg // mul1e.
Qed.

Lemma lte_pdivr_mull r x y : (0 < r)%R -> (r^-1%:E * y < x) = (y < r%:E * x).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivr_mull.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e 2!ltNge 2!leey.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e -EFinM 2!ltNyr.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e ltxx.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
Qed.

Lemma lte_pdivr_mulr r x y : (0 < r)%R -> (y * r^-1%:E < x) = (y < x * r%:E).
Proof. by move=> r0; rewrite muleC lte_pdivr_mull// muleC. Qed.

Lemma lte_pdivl_mull r y x : (0 < r)%R -> (x < r^-1%:E * y) = (r%:E * x < y).
Proof.
move=> r0; move: x y => [x| |] [y| |] //=.
- by rewrite 2!lte_fin ltr_pdivl_mull.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e 2!ltry.
- by rewrite mulr_infty sgrV gtr0_sg// mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty gtr0_sg// mul1e 2!ltNyr.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// 2!mul1e.
- by rewrite mulr_infty [in RHS]mulr_infty sgrV gtr0_sg// mul1e.
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

Import DualAddTheoryNumDomain DualAddTheoryRealDomain.

Section DualRealFieldType_lemmas.
Local Open Scope ereal_dual_scope.
Variable R : realFieldType.
Implicit Types x y : \bar R.

Lemma lee_dadde x y : (forall e : {posnum R}, x <= y + e%:num%:E) -> x <= y.
Proof. by move=> xye; apply: lee_adde => e; case: x {xye} (xye e). Qed.

End DualRealFieldType_lemmas.

End DualAddTheoryRealField.

Section sqrte.
Variable R : rcfType.
Implicit Types x y : \bar R.

Definition sqrte x :=
  if x is +oo then +oo else if x is r%:E then (Num.sqrt r)%:E else 0.

Lemma sqrte0 : sqrte 0 = 0 :> \bar R.
Proof. by rewrite /= sqrtr0. Qed.

Lemma sqrte_ge0 x : 0 <= sqrte x.
Proof. by case: x => [x|//|]; rewrite /= ?leey// lee_fin sqrtr_ge0. Qed.

Lemma lee_sqrt x y : 0 <= y -> (sqrte x <= sqrte y) = (x <= y).
Proof.
case: x y => [x||] [y||] yge0 //=.
- exact: mathcomp_extra.ler_sqrt.
- by rewrite !leey.
- by rewrite leNye lee_fin sqrtr_ge0.
Qed.

Lemma sqrteM x y : 0 <= x -> sqrte (x * y) = sqrte x * sqrte y.
Proof.
case: x y => [x||] [y||] //= age0.
- by rewrite sqrtrM ?EFinM.
- move: age0; rewrite le_eqVlt eqe => /predU1P[<-|x0].
    by rewrite mul0e sqrte0 sqrtr0 mul0e.
  by rewrite mulry gtr0_sg ?mul1e// mulry gtr0_sg ?mul1e// sqrtr_gt0.
- move: age0; rewrite mule0 mulrNy lee_fin -sgr_ge0.
  by case: sgrP; rewrite ?mul0e ?sqrte0// ?mul1e// ler0N1.
- rewrite !mulyr; case: (sgrP y) => [->||].
  + by rewrite sqrtr0 sgr0 mul0e sqrte0.
  + by rewrite mul1e/= -sqrtr_gt0 -sgr_gt0 -lte_fin => /gt0_muley->.
  + by move=> y0; rewrite EFinN mulN1e/= ltr0_sqrtr// sgr0 mul0e.
- by rewrite mulyy.
- by rewrite mulyNy mule0.
Qed.

Lemma sqr_sqrte x : 0 <= x -> sqrte x ^+ 2 = x.
Proof.
case: x => [x||] xge0; rewrite expe2 ?mulyy//.
by rewrite -sqrteM// -EFinM/= sqrtr_sqr ger0_norm.
Qed.

Lemma sqrte_sqr x : sqrte (x ^+ 2) = `|x|%E.
Proof. by case: x => [x||//]; rewrite /expe/= ?sqrtr_sqr// mulyy. Qed.

Lemma sqrte_fin_num x : 0 <= x -> (sqrte x \is a fin_num) = (x \is a fin_num).
Proof. by case: x => [x|//|//]; rewrite !qualifE/=. Qed.

End sqrte.

Module DualAddTheory.
Export DualAddTheoryNumDomain.
Export DualAddTheoryRealDomain.
Export DualAddTheoryRealField.
End DualAddTheory.

Module ConstructiveDualAddTheory.
Export DualAddTheory.
End ConstructiveDualAddTheory.

Definition posnume (R : numDomainType) of phant R := {> 0 : \bar R}.
Notation "{ 'posnum' '\bar' R }" := (@posnume _ (Phant R))  : type_scope.
Definition nonnege (R : numDomainType) of phant R := {>= 0 : \bar R}.
Notation "{ 'nonneg' '\bar' R }" := (@nonnege _ (Phant R))  : type_scope.

Notation "x %:pos" := (widen_signed x%:sgn : {posnum \bar _}) (only parsing)
  : ereal_dual_scope.
Notation "x %:pos" := (widen_signed x%:sgn : {posnum \bar _}) (only parsing)
  : ereal_scope.
Notation "x %:nng" := (widen_signed x%:sgn : {nonneg \bar _}) (only parsing)
  : ereal_dual_scope.
Notation "x %:nng" := (widen_signed x%:sgn : {nonneg \bar _}) (only parsing)
  : ereal_scope.
Notation "x %:pos" := (@widen_signed ereal_display _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x))
    !=0 (KnownSign.Real (KnownSign.Sign >=0)) _ _)
  (only printing) : ereal_dual_scope.
Notation "x %:pos" := (@widen_signed ereal_display _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x))
    !=0 (KnownSign.Real (KnownSign.Sign >=0)) _ _)
  (only printing) : ereal_scope.
Notation "x %:nng" := (@widen_signed ereal_display _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x))
    ?=0 (KnownSign.Real (KnownSign.Sign >=0)) _ _)
  (only printing) : ereal_dual_scope.
Notation "x %:nng" := (@widen_signed ereal_display _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x))
    ?=0 (KnownSign.Real (KnownSign.Sign >=0)) _ _)
  (only printing) : ereal_scope.

#[global] Hint Extern 0 (is_true (0%E < _)%O) => solve [apply: gt0] : core.
#[global] Hint Extern 0 (is_true (_ < 0%E)%O) => solve [apply: lt0] : core.
#[global] Hint Extern 0 (is_true (0%E <= _)%O) => solve [apply: ge0] : core.
#[global] Hint Extern 0 (is_true (_ <= 0%E)%O) => solve [apply: le0] : core.
#[global] Hint Extern 0 (is_true (0%E >=< _)%O) => solve [apply: cmp0] : core.
#[global] Hint Extern 0 (is_true (_ != 0%E)%O) => solve [apply: neq0] : core.

Section SignedNumDomainStability.
Context {R : numDomainType}.

Lemma pinfty_snum_subproof : Signed.spec 0 !=0 >=0 (+oo : \bar R).
Proof. by rewrite /= le0y. Qed.

Canonical pinfty_snum := Signed.mk (pinfty_snum_subproof).

Lemma ninfty_snum_subproof : Signed.spec 0 !=0 <=0 (-oo : \bar R).
Proof. by rewrite /= leNy0. Qed.

Canonical ninfty_snum := Signed.mk (ninfty_snum_subproof).

Lemma EFin_snum_subproof nz cond (x : {num R & nz & cond}) :
  Signed.spec 0 nz cond x%:num%:E.
Proof.
apply/andP; split.
  case: cond nz x => [[[]|]|] [] x //=;
    do ?[by case: (bottom x)|by rewrite eqe eq0F].
case: cond nz x => [[[]|]|] [] x //=;
  do ?[by case: (bottom x)|by rewrite ?lee_fin ?(eq0, ge0, le0) ?[_ || _]cmp0].
Qed.

Canonical EFin_snum nz cond (x : {num R & nz & cond}) :=
  Signed.mk (EFin_snum_subproof x).

Lemma fine_snum_subproof (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) :
  Signed.spec 0%R ?=0 xr (fine x%:num).
Proof.
case: xr x => [[[]|]|]//= [x /andP[_]]/=.
- by move=> /eqP ->.
- by case: x.
- by case: x.
- by move=> /orP[]; case: x => [x||]//=; rewrite lee_fin => ->; rewrite ?orbT.
Qed.

Canonical fine_snum (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) :=
  Signed.mk (fine_snum_subproof x).

Lemma oppe_snum_subproof (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) (r := opp_reality_subdef xnz xr) :
  Signed.spec 0 xnz r (- x%:num).
Proof.
rewrite {}/r; case: xr xnz x => [[[]|]|] [] x //=;
  do ?[by case: (bottom x)
      |by rewrite ?eqe_oppLR ?oppe0 1?eq0//;
          rewrite ?oppe_le0 ?oppe_ge0 ?(eq0, eq0F, ge0, le0)//;
          rewrite orbC [_ || _]cmp0].
Qed.

Canonical oppe_snum (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) :=
  Signed.mk (oppe_snum_subproof x).

Lemma adde_snum_subproof (xnz ynz : KnownSign.nullity)
    (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr})
    (rnz := add_nonzero_subdef xnz ynz xr yr)
    (rrl := add_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num + y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  by rewrite 1?adde_ss_eq0 ?(eq0F, ge0, le0, andbF, orbT).
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by case: (bottom x)|by case: (bottom y)
      |by rewrite adde_ge0|by rewrite adde_le0
      |exact: realDe|by rewrite 2!eq0 add0e].
Qed.

Canonical adde_snum (xnz ynz : KnownSign.nullity)
    (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr}) :=
  Signed.mk (adde_snum_subproof x y).

Import DualAddTheory.

Lemma dadde_snum_subproof (xnz ynz : KnownSign.nullity)
    (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr})
    (rnz := add_nonzero_subdef xnz ynz xr yr)
    (rrl := add_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num + y%:num)%dE.
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  by rewrite 1?dadde_ss_eq0 ?(eq0F, ge0, le0, andbF, orbT).
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by case: (bottom x)|by case: (bottom y)
      |by rewrite dadde_ge0|by rewrite dadde_le0
      |exact: realDed|by rewrite 2!eq0 dadd0e].
Qed.

Canonical dadde_snum (xnz ynz : KnownSign.nullity)
    (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr}) :=
  Signed.mk (dadde_snum_subproof x y).

Lemma mule_snum_subproof (xnz ynz : KnownSign.nullity)
    (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr})
    (rnz := mul_nonzero_subdef xnz ynz xr yr)
    (rrl := mul_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num * y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []// x y;
     rewrite mule_neq0.
by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []/= x y //;
  do ?[by case: (bottom x)|by case: (bottom y)
      |by rewrite mule_ge0|by rewrite mule_le0_ge0
      |by rewrite mule_ge0_le0|by rewrite mule_le0|exact: realMe
      |by rewrite eq0 ?mule0// mul0e].
Qed.

Canonical mule_snum (xnz ynz : KnownSign.nullity) (xr yr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr})
    (y : {compare (0 : \bar R) & ynz & yr}) :=
  Signed.mk (mule_snum_subproof x y).

Definition abse_reality_subdef (xnz : KnownSign.nullity)
    (xr : KnownSign.reality) := (if xr is =0 then =0 else >=0)%snum_sign.
Arguments abse_reality_subdef /.

Lemma abse_snum_subproof (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) (r := abse_reality_subdef xnz xr) :
  Signed.spec 0 xnz r `|x%:num|.
Proof.
rewrite {}/r; case: xr xnz x => [[[]|]|] [] x //=;
  do ?[by case: (bottom x)|by rewrite eq0 abse0
      |by rewrite abse_ge0// andbT gee0_abs
      |by rewrite abse_ge0// andbT lee0_abs
      |by rewrite abse_ge0// andbT abse_eq0].
Qed.

Canonical abse_snum (xnz : KnownSign.nullity) (xr : KnownSign.reality)
    (x : {compare (0 : \bar R) & xnz & xr}) :=
  Signed.mk (abse_snum_subproof x).

End SignedNumDomainStability.

Section MorphNum.
Context {R : numDomainType} {nz : KnownSign.nullity} {cond : KnownSign.reality}.
Local Notation nR := {compare (0 : \bar R) & nz & cond}.
Implicit Types (a : \bar R).

Lemma num_abse_eq0 a : (`|a|%:nng == 0%:nng) = (a == 0).
Proof. by rewrite -abse_eq0. Qed.

End MorphNum.

Section MorphReal.
Context {R : numDomainType} {nz : KnownSign.nullity} {r : KnownSign.real}.
Local Notation nR := {compare (0 : \bar R) & nz & r}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : R) nz r).

Lemma num_lee_maxr a x y :
  a <= maxe x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_maxr// ereal_comparable. Qed.

Lemma num_lee_maxl a x y :
  maxe x%:num  y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_le_maxl// ereal_comparable. Qed.

Lemma num_lee_minr a x y :
  a <= mine x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_minr// ereal_comparable. Qed.

Lemma num_lee_minl a x y :
  mine x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_le_minl// ereal_comparable. Qed.

Lemma num_lte_maxr a x y :
  a < maxe x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_maxr// ereal_comparable. Qed.

Lemma num_lte_maxl a x y :
  maxe x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_lt_maxl// ereal_comparable. Qed.

Lemma num_lte_minr a x y :
  a < mine x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_minr// ereal_comparable. Qed.

Lemma num_lte_minl a x y :
  mine x%:num y%:num < a = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_lt_minl// ereal_comparable. Qed.

End MorphReal.

Section MorphGe0.
Context {R : numDomainType} {nz : KnownSign.nullity}.
Local Notation nR := {compare (0 : \bar R) & ?=0 & >=0}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : \bar R) ?=0 >=0).

Lemma num_abse_le a x : 0 <= a -> (`|a|%:nng <= x)%O = (a <= x%:num).
Proof. by move=> a0; rewrite -num_le//= gee0_abs. Qed.

Lemma num_abse_lt a x : 0 <= a -> (`|a|%:nng < x)%O = (a < x%:num).
Proof. by move=> a0; rewrite -num_lt/= gee0_abs. Qed.
End MorphGe0.

Variant posnume_spec (R : numDomainType) (x : \bar R) :
  \bar R -> bool -> bool -> bool -> Type :=
| IsPinftyPosnume :
  posnume_spec x +oo false true true
| IsRealPosnume (p : {posnum R}) :
  posnume_spec x (p%:num%:E) false true true.

Lemma posnumeP (R : numDomainType) (x : \bar R) : 0 < x ->
  posnume_spec x x (x == 0) (0 <= x) (0 < x).
Proof.
case: x => [x|_|//]; last by rewrite le0y lt0y; exact: IsPinftyPosnume.
rewrite lte_fin lee_fin eqe => x_gt0.
rewrite x_gt0 (ltW x_gt0) (negbTE (lt0r_neq0 x_gt0)).
exact: IsRealPosnume (PosNum x_gt0).
Qed.

Variant nonnege_spec (R : numDomainType) (x : \bar R) :
  \bar R -> bool -> Type :=
| IsPinftyNonnege : nonnege_spec x +oo true
| IsRealNonnege (p : {nonneg R}) : nonnege_spec x (p%:num%:E) true.

Lemma nonnegeP (R : numDomainType) (x : \bar R) : 0 <= x ->
  nonnege_spec x x (0 <= x).
Proof.
case: x => [x|_|//]; last by rewrite le0y; exact: IsPinftyNonnege.
by rewrite lee_fin => /[dup] x_ge0 ->; exact: IsRealNonnege (NngNum x_ge0).
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
rewrite normrM normrV ?unitfE //.
rewrite ltr_pdivr_mulr // ?mul1r//; last by rewrite gtr0_norm.
by rewrite [ltRHS]gtr0_norm ?ltr_addr// ltr_spaddl.
Qed.

Lemma contract_le1 x : (`|contract x| <= 1)%R.
Proof.
by case: x => [r| |] /=; rewrite ?normrN1 ?normr1 // (ltW (contract_lt1 _)).
Qed.

Lemma contract0 : contract 0 = 0%R.
Proof. by rewrite /contract mul0r. Qed.

Lemma contractN x : contract (- x) = (- contract x)%R.
Proof. by case: x => //= [r|]; [ rewrite normrN mulNr | rewrite opprK]. Qed.

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

Lemma le_expand : {homo expand : x y / (x <= y)%O}.
Proof.
move=> x y xy; have [x1|] := lerP `|x| 1.
  have [y_le1|/ltW /expand1->] := leP y 1%R; last by rewrite leey.
  rewrite le_expand_in ?inE// ler_norml y_le1 (le_trans _ xy)//.
  by rewrite ler_oppl (ler_normlP _ _ _).
rewrite ltr_normr => /orP[|] x1; last first.
  by rewrite expandN1 // ?leNye // ler_oppr ltW.
by rewrite expand1; [rewrite expand1 // (le_trans _ xy) // ltW | exact: ltW].
Qed.

Lemma expand_eqoo r : (expand r == +oo) = (1 <= r)%R.
Proof. by rewrite /expand; case: ifP => //; case: ifP. Qed.

Lemma expand_eqNoo r : (expand r == -oo) = (r <= -1)%R.
Proof.
rewrite /expand; case: ifP => /= r1; last by case: ifP.
by apply/esym/negbTE; rewrite -ltNge (lt_le_trans _ r1) // -subr_gt0 opprK.
Qed.

End contract_expand.

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
  by exists d => y /dP /andP[->] /= /lt_le_trans; apply; rewrite leey.
- have [//||d dP] := wlog (r - 1)%R b; rewrite ?lte_fin ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->] /=; rewrite ltNyr.
- by exists 1%:pos%R => ? ?; rewrite ltNyr ltry.
Qed.
