(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg ssrnum ssrint.
Require Import boolp.

Reserved Notation "{ 'compare' x0 & nz & cond }"
  (at level 0, x0 at level 200, nz at level 200,
   format "{ 'compare'  x0  &  nz  &  cond }").
Reserved Notation "{ 'num' R & nz & cond }"
  (at level 0, R at level 200, nz at level 200,
   format "{ 'num'  R  &  nz  &  cond }").
Reserved Notation "{ > x0 }" (at level 0, format "{ >  x0 }").
Reserved Notation "{ < x0 }" (at level 0, format "{ <  x0 }").
Reserved Notation "{ >= x0 }" (at level 0, format "{ >=  x0 }").
Reserved Notation "{ <= x0 }" (at level 0, format "{ <=  x0 }").
Reserved Notation "{ >=< x0 }" (at level 0, format "{ >=<  x0 }").
Reserved Notation "{ >< x0 }" (at level 0, format "{ ><  x0 }").
Reserved Notation "{ != x0 }" (at level 0, format "{ !=  x0 }").
Reserved Notation "{ ?= x0 }" (at level 0, format "{ ?=  x0 }").
Reserved Notation "{ > x0 : T }" (at level 0, format "{ >  x0  :  T }").
Reserved Notation "{ < x0 : T }" (at level 0, format "{ <  x0  :  T }").
Reserved Notation "{ >= x0 : T }" (at level 0, format "{ >=  x0  :  T }").
Reserved Notation "{ <= x0 : T }" (at level 0, format "{ <=  x0  :  T }").
Reserved Notation "{ >=< x0 : T }" (at level 0, format "{ >=<  x0  :  T }").
Reserved Notation "{ >< x0 : T }" (at level 0, format "{ ><  x0  :  T }").
Reserved Notation "{ != x0 : T }" (at level 0, format "{ !=  x0  :  T }").
Reserved Notation "{ ?= x0 : T }" (at level 0, format "{ ?=  x0  :  T }").
Reserved Notation ">=0" (at level 0, format ">=0").
Reserved Notation "<=0" (at level 0, format "<=0").
Reserved Notation ">=<0" (at level 0, format ">=<0").
Reserved Notation ">?<0" (at level 0, format ">?<0").
Reserved Notation "!=0" (at level 0, format "!=0").
Reserved Notation "?=0" (at level 0, format "?=0").

Reserved Notation "x %:sgn" (at level 2, format "x %:sgn").
Reserved Notation "x %:num" (at level 2, format "x %:num").
Reserved Notation "[ 'sgn' 'of' x ]" (format "[ 'sgn' 'of'  x ]").
Reserved Notation "[ 'gt0' 'of' x ]" (format "[ 'gt0' 'of'  x ]").
Reserved Notation "[ 'lt0' 'of' x ]" (format "[ 'lt0' 'of'  x ]").
Reserved Notation "[ 'ge0' 'of' x ]" (format "[ 'ge0' 'of'  x ]").
Reserved Notation "[ 'le0' 'of' x ]" (format "[ 'le0' 'of'  x ]").
Reserved Notation "[ 'cmp0' 'of' x ]" (format "[ 'cmp0' 'of'  x ]").
Reserved Notation "[ 'neq0' 'of' x ]" (format "[ 'neq0' 'of'  x ]").

Reserved Notation "{ 'posnum' R }" (at level 0, format "{ 'posnum'  R }").
Reserved Notation "{ 'nonneg' R }" (at level 0, format "{ 'nonneg'  R }").
Reserved Notation "x %:pos" (at level 2, format "x %:pos").
Reserved Notation "x %:nng" (at level 2, format "x %:nng").

Reserved Notation "!! x" (at level 100, only parsing).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

Declare Scope snum_scope.
Delimit Scope snum_scope with snum.
Declare Scope snum_sign_scope.
Delimit Scope snum_sign_scope with snum_sign.
Declare Scope snum_nullity_scope.
Delimit Scope snum_nullity_scope with snum_nullity.

(* Enrico's trick for tc resolution in have *)
Notation "!! x" := (ltac:(refine x)) (only parsing).
(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
Hint Mode infer ! : typeclass_instances.
Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Class unify {T} (x y : T) := Unify : x = y.
Hint Mode unify - + - : typeclass_instances.
Class unify' {T} (x y : T) := Unify' : x = y.
Instance unify'P {T} (x y : T) : unify' x y -> unify x y := id.
Hint Extern 0 (unify' _ _) => vm_compute; reflexivity : typeclass_instances.

Module Import KnownSign.
Variant nullity := NonZero | MaybeZero.
Coercion nullity_bool nz := if nz is NonZero then true else false.
Definition nz_of_bool b := if b then NonZero else MaybeZero.

Variant sign := NonNeg | NonPos.
Variant real := Sign of sign | AnySign.
Variant reality := Real of real | Arbitrary.
End KnownSign.

Module Signed.
Section Signed.
Context (disp : unit) (T : porderType disp) (x0 : T).

Local Coercion is_real r := if r is Real _ then true else false.
Definition reality_cond (n : reality) (x : T) :=
  match n with
  | Real (Sign NonNeg) => x >= x0
  | Real (Sign NonPos) => x <= x0
  | Real AnySign       => (x0 <= x) || (x <= x0)
  | Arbitary           => true
  end.

Record def (nz : nullity) (cond : reality) := Def {
  r :> T;
  #[canonical=no]
  P : (nz ==> (r != x0)) && reality_cond cond r
}.

End Signed.

Notation spec x0 nz cond x :=
  ((nullity_bool nz ==> (x != x0)) && (reality_cond x0 cond x)).

Definition mk {d T} x0 nz cond r P : @def d T x0 nz cond :=
  @Def d T x0 nz cond r P.

Definition from {d T x0 nz cond}
  {x : @def d T x0 nz cond} (phx : phantom T x) := x.

Definition fromP {d T x0 nz cond}
  {x : @def d T x0 nz cond} (phx : phantom T x) := P x.

Module Exports.
Coercion Sign : sign >-> real.
Coercion Real : real >-> reality.
Coercion is_real : reality >-> bool.
Bind Scope snum_sign_scope with sign.
Bind Scope snum_sign_scope with reality.
Bind Scope snum_nullity_scope with nullity.
Notation ">=0" := NonNeg : snum_sign_scope.
Notation "<=0" := NonPos : snum_sign_scope.
Notation ">=<0" := AnySign : snum_sign_scope.
Notation ">?<0" := Arbitrary : snum_sign_scope.
Notation "!=0" := NonZero : snum_nullity_scope.
Notation "?=0" := MaybeZero : snum_nullity_scope.
Notation "{ 'compare' x0 & nz & cond }" := (def x0 nz cond) : type_scope.
Notation "{ 'num' R & nz & cond }" := (def (0%R : R) nz cond) : ring_scope.
Notation "{ > x0 : T }" := (def (x0 : T) NonZero NonNeg) : type_scope.
Notation "{ < x0 : T }" := (def (x0 : T) NonZero NonPos) : type_scope.
Notation "{ >= x0 : T }" := (def (x0 : T) MaybeZero NonNeg) : type_scope.
Notation "{ <= x0 : T }" := (def (x0 : T) MaybeZero NonPos) : type_scope.
Notation "{ >< x0 : T }" := (def (x0 : T) NonZero Real) : type_scope.
Notation "{ >=< x0 : T }" := (def (x0 : T) MaybeZero Real) : type_scope.
Notation "{ != x0 : T }" := (def (x0 : T) NonZero Arbitrary) : type_scope.
Notation "{ ?= x0 : T }" := (def (x0 : T) MaybeZero Arbitrary) : type_scope.
Notation "{ > x0 }" := (def x0 NonZero NonNeg) : type_scope.
Notation "{ < x0 }" := (def x0 NonZero NonPos) : type_scope.
Notation "{ >= x0 }" := (def x0 MaybeZero NonNeg) : type_scope.
Notation "{ <= x0 }" := (def x0 MaybeZero NonPos) : type_scope.
Notation "{ >< x0 }" := (def x0 NonZero Real) : type_scope.
Notation "{ >=< x0 }" := (def x0 MaybeZero Real) : type_scope.
Notation "{ != x0 }" := (def x0 NonZero Arbitrary) : type_scope.
Notation "{ ?= x0 }" := (def x0 MaybeZero Arbitrary) : type_scope.
Notation "x %:sgn" := (from (Phantom _ x)) : ring_scope.
Notation "[ 'sgn' 'of' x ]" := (fromP (Phantom _ x)) : ring_scope.
Notation num := r.
Notation "x %:num" := (r x) : ring_scope.
Definition posnum (R : numDomainType) of phant R := {> 0%R : R}.
Notation "{ 'posnum' R }" := (@posnum _ (Phant R))  : ring_scope.
Definition nonneg (R : numDomainType) of phant R := {>= 0%R : R}.
Notation "{ 'nonneg' R }" := (@nonneg _ (Phant R))  : ring_scope.
Notation "2" := 2%:R : ring_scope.
Arguments r {disp T x0 nz cond}.
End Exports.
End Signed.
Export Signed.Exports.

Section POrder.
Variables (d : unit) (T : porderType d) (x0 : T) (nz : nullity) (cond : reality).
Local Notation sT := {compare x0 & nz & cond}.
Canonical signed_subType := [subType for @Signed.r d T x0 nz cond].
Definition signed_eqMixin := [eqMixin of sT by <:].
Canonical signed_eqType := EqType sT signed_eqMixin.
Definition signed_choiceMixin := [choiceMixin of sT by <:].
Canonical signed_choiceType := ChoiceType sT signed_choiceMixin.
Definition signed_porderMixin := [porderMixin of sT by <:].
Canonical signed_porderType := POrderType d sT signed_porderMixin.
End POrder.

(* Section Order. *)
(* Variables (d : unit) (T : orderType d) (x0 : T) (nz : nullity) (cond : reality). *)
(* Local Notation sT := {compare x0 & nz & cond}. *)

(* Lemma signed_le_total : totalPOrderMixin [porderType of sT]. *)
(* Proof. by move=> x y; apply: le_total. Qed. *)

(* Canonical signed_latticeType := LatticeType sT signed_le_total. *)
(* Canonical signed_distrLatticeType := DistrLatticeType sT signed_le_total. *)
(* Canonical signed_orderType := OrderType sT signed_le_total. *)

(* End Order. *)

Section Theory.
Context {d : unit} {T : porderType d} {x0 : T}
  {nz : nullity} {cond : reality}.
Local Notation sT := {compare x0 & nz & cond}.
Implicit Type x : sT.

Lemma signed_intro {x} : x%:num = x%:num :> T. Proof. by []. Qed.

Lemma gt0 x : unify nz NonZero -> unify cond NonNeg ->
  x0 < x%:num :> T.
Proof.
move=> nz_eq cond_eq; case: x.
by rewrite nz_eq cond_eq => //= r; rewrite lt_def.
Qed.

Lemma le0F x : unify nz NonZero -> unify cond NonNeg ->
   x%:num <= x0 :> T = false.
Proof. by move=> ? ?; rewrite lt_geF//; apply: gt0. Qed.

Lemma lt0 x : unify nz NonZero -> unify cond NonPos ->
  x%:num < x0 :> T.
Proof.
move=> nz_eq cond_eq; case: x.
by rewrite nz_eq cond_eq => //= r; rewrite lt_def [x0 == _]eq_sym.
Qed.

Lemma ge0F x : unify nz NonZero -> unify cond NonPos ->
  x0 <= x%:num :> T = false.
Proof. by move=> ? ?; rewrite lt_geF//; apply: lt0. Qed.

Lemma ge0 x : unify cond NonNeg -> x0 <= x%:num :> T.
Proof. by move=> cond_eq; case: x; rewrite cond_eq/= => ? /andP[]. Qed.

Lemma lt0F x : unify cond NonNeg -> x%:num < x0 :> T = false.
Proof. by move=> ?; rewrite le_gtF//; apply: ge0. Qed.

Lemma le0 x : unify cond NonPos -> x0 >= x%:num :> T.
Proof. by move=> cond_eq; case: x; rewrite cond_eq/= => ? /andP[]. Qed.

Lemma gt0F x : unify cond NonPos -> x0 < x%:num :> T = false.
Proof. by move=> ?; rewrite le_gtF//; apply: le0. Qed.

Lemma cmp0 {r : real} x :
  unify cond (Real r) -> (x0 >=< x%:num).
Proof.
move=> cond_eq;  rewrite /(_ >=< _); move: x; rewrite {}cond_eq.
by case: r => [[|]|] [/= x /andP[_ ->]]//; rewrite orbT.
Qed.

Lemma neq0 x : unify nz NonZero -> x%:num != x0 :> T.
Proof. by move=> nz_eq; case: x; rewrite nz_eq/= => ? /andP[]. Qed.

Lemma eq0F x : unify nz NonZero -> x%:num == x0 :> T = false.
Proof. by move=> /neq0-/(_ x)/negPf->. Qed.

End Theory.

Arguments gt0 {d T x0 nz cond} _ {_ _}.
Arguments le0F {d T x0 nz cond} _ {_ _}.
Arguments lt0 {d T x0 nz cond} _ {_ _}.
Arguments ge0F {d T x0 nz cond} _ {_ _}.
Arguments ge0 {d T x0 nz cond} _ {_}.
Arguments lt0F {d T x0 nz cond} _ {_}.
Arguments le0 {d T x0 nz cond} _ {_}.
Arguments gt0F {d T x0 nz cond} _ {_}.
Arguments cmp0 {d T x0 nz cond r} _ {_}.
Arguments neq0 {d T x0 nz cond} _ {_}.
Arguments eq0F {d T x0 nz cond} _ {_}.

Notation "[ 'gt0' 'of' x ]" := (ltac:(refine (gt0 x%:sgn))).
Notation "[ 'lt0' 'of' x ]" := (ltac:(refine (lt0 x%:sgn))).
Notation "[ 'ge0' 'of' x ]" := (ltac:(refine (ge0 x%:sgn))).
Notation "[ 'le0' 'of' x ]" := (ltac:(refine (le0 x%:sgn))).
Notation "[ 'cmp0' 'of' x ]" := (ltac:(refine (cmp0 x%:sgn))).
Notation "[ 'neq0' 'of' x ]" := (ltac:(refine (neq0 x%:sgn))).

Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: gt0] : core.
Hint Extern 0 (is_true (_ < 0%R)%O) => solve [apply: lt0] : core.
Hint Extern 0 (is_true (0%R <= _)%O) => solve [apply: ge0] : core.
Hint Extern 0 (is_true (_ <= 0%R)%O) => solve [apply: le0] : core.
Hint Extern 0 (is_true (_ \is Num.real)) => solve [apply: cmp0] : core.
Hint Extern 0 (is_true (0%R >=< _)%O) => solve [apply: cmp0] : core.
Hint Extern 0 (is_true (_ != 0%R)%O) => solve [apply: neq0] : core.

Local Open Scope ring_scope.

Section Order.
Variables (R : numDomainType) (nz : nullity) (r : real).
Local Notation nR := {num R & nz & r}.

Lemma signed_le_total : totalPOrderMixin [porderType of nR].
Proof. by move=> x y; apply: real_comparable. Qed.

Canonical signed_latticeType := LatticeType nR signed_le_total.
Canonical signed_distrLatticeType := DistrLatticeType nR signed_le_total.
Canonical signed_orderType := OrderType nR signed_le_total.

End Order.

Section NumDomainStability.
Context {R : numDomainType}.

Lemma zero_snum_subproof cond : Signed.spec 0 MaybeZero cond (0 : R).
Proof. by case: cond => // -[[]|]//=; rewrite lexx. Qed.

Canonical zero_snum cond := Signed.mk (zero_snum_subproof cond).

Lemma one_snum_subproof : Signed.spec 0 NonZero NonNeg (1 : R).
Proof. by rewrite /= oner_eq0 ler01. Qed.

Canonical one_snum := Signed.mk one_snum_subproof.

Definition opp_reality_subdef (xnz : nullity) (xr : reality) : reality :=
  match xr with
  | Real (Sign >=0) => <=0
  | Real (Sign <=0) => >=0
  | Real AnySign    => >=<0
  | Arbitrary              => >?<0
  end.

Lemma opp_snum_subproof (xnz : nullity) (xr : reality)
    (x : {num R & xnz & xr}) (r := opp_reality_subdef xnz xr) :
  Signed.spec 0 xnz r (- x%:num).
Proof.
by rewrite {}/r; case: xr x => [[[]|]|]//= [r]/=;
   rewrite oppr_eq0 ?(oppr_ge0, oppr_le0)// orbC.
Qed.

Canonical opp_snum (xnz : nullity) (xr : reality) (x : {num R & xnz & xr}) :=
  Signed.mk (opp_snum_subproof x).

Definition add_samesign_subdef (xnz ynz : nullity) (xr yr : reality) :=
  match xr, yr with
      | Real (Sign >=0), Real (Sign >=0)
      | Real (Sign <=0), Real (Sign <=0) => true
      | _, _ => false
  end.

Definition add_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool (xr && add_samesign_subdef xnz ynz xr yr && (xnz || ynz)).
Arguments add_nonzero_subdef /.

Definition both_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign >=0), Real (Sign >=0) => >=0
  | Real (Sign <=0), Real (Sign <=0) => <=0
  | Real _, Real _ => >=<0
  | _, _ => >?<0
  end.
Arguments both_reality_subdef /.

Lemma add_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr})
    (rnz := add_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num + y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  by rewrite 1?addr_ss_eq0 ?(eq0F, ge0, le0, andbF, orbT).
have addr_le0 a b : a <= 0 -> b <= 0 -> a + b <= 0.
  by rewrite -!oppr_ge0 opprD; apply: addr_ge0.
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by rewrite addr_ge0|by rewrite addr_le0|by rewrite -realE realD].
Qed.

Canonical add_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr}) :=
  Signed.mk (add_snum_subproof x y).

Definition mul_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool match xnz, ynz with
                    | NonZero, NonZero => NonZero
                    | _      , _       => MaybeZero
                    end.
Arguments mul_nonzero_subdef /.

Definition mul_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign >=0), Real (Sign >=0)
  | Real (Sign <=0), Real (Sign <=0) => >=0
  | Real (Sign >=0), Real (Sign <=0)
  | Real (Sign <=0), Real (Sign >=0) => <=0
  | Real _,          Real _          => >=<0
  | _ , _                            => >?<0
  end.
Arguments mul_reality_subdef /.

Lemma mul_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr})
    (rnz := mul_nonzero_subdef xnz ynz xr yr)
    (rrl := mul_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num * y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []// x y;
     rewrite mulf_neq0.
by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []/= x y //;
   do ?[by rewrite mulr_ge0|by rewrite mulr_le0_ge0|
        by rewrite mulr_ge0_le0|by rewrite mulr_le0|by rewrite -realE realM].
Qed.

Canonical mul_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr}) :=
  Signed.mk (mul_snum_subproof x y).

Lemma natmul_snum_subproof (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {compare 0%N & nnz & nr})
    (rnz := mul_nonzero_subdef xnz nnz xr nr)
    (rrl := mul_reality_subdef xnz nnz xr nr) :
  Signed.spec 0 rnz rrl (x%:num *+ n%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []// x n;
     rewrite mulrn_eq0//= ?eq0F.
move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []/= x [[|n]//= _] //;
   do ?[by rewrite mulrn_wge0|
        by rewrite mulrn_wle0|
        by apply: real_comparable; rewrite ?real0 ?realrMn].
Qed.

Canonical natmul_snum (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {compare 0%N & nnz & nr}) :=
  Signed.mk (natmul_snum_subproof x n).

Lemma intmul_snum_subproof (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {num int & nnz & nr})
    (rnz := mul_nonzero_subdef xnz nnz xr nr)
    (rrl := mul_reality_subdef xnz nnz xr nr) :
  Signed.spec 0 rnz rrl (x%:num *~ n%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []// x n;
     rewrite mulrz_neq0//= ?neq0.
by move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []/= x n //;
   do ?[by rewrite mulrz_ge0|by rewrite mulrz_le0_ge0|
        by rewrite mulrz_ge0_le0|by rewrite mulrz_le0|
        by rewrite -realE rpredMz//; apply: cmp0].
Qed.

Canonical intmul_snum (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {num int & nnz & nr}) :=
  Signed.mk (intmul_snum_subproof x n).

Lemma inv_snum_subproof (xnz : nullity) (xr : reality)
    (x : {num R & xnz & xr}) :
  Signed.spec 0 xnz xr (x%:num^-1 : R).
Proof.
by case: xr x => [[[]|]|]//= [r]/=;
   rewrite invr_eq0 ?(invr_ge0, invr_le0) ?realV.
Qed.

Canonical inv_snum (xnz : nullity) (xr : reality) (x : {num R & xnz & xr}) :=
  Signed.mk (inv_snum_subproof x).

Definition exprn_reality_subdef (nz : nullity) (r : reality) : reality :=
  match r with
  | Real (Sign >=0) => >=0
  | Real _ => >=<0
  | _ => >?<0
  end.
Arguments exprn_reality_subdef /.

Lemma exprn_snum_subproof (xnz : nullity) (xr : reality)
    (x : {num R & xnz & xr}) (rr := exprn_reality_subdef xnz xr) n :
  Signed.spec 0 xnz rr (x%:num ^+ n : R).
Proof.
by rewrite {}/rr; case: xnz xr x => [] [[[]|]|]//= r/=;
   rewrite ?expf_eq0 ?eq0F ?andbF//=;
   rewrite -?[_ || _]/(_ \is Num.real) ?realX ?exprn_ge0.
Qed.

Canonical exprn_snum (nz : nullity) (r : reality) (x : {num R & nz & r}) n :=
  Signed.mk (exprn_snum_subproof x n).

Definition both_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool (xnz && ynz).
Arguments both_nonzero_subdef /.

Lemma min_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr})
    (rnz := both_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (Num.min x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
     rewrite /Num.min; case: ifP => _ //.
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
rewrite /Num.min; case: ifP => _;
by [rewrite ?(ge0, le0, orbT)//|apply: cmp0].
Qed.

Canonical min_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr}) :=
  Signed.mk (min_snum_subproof x y).

Definition max_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) : nullity :=
  nz_of_bool ((xnz && ynz)
  || match xr, yr with NonNeg, NonNeg => xnz || ynz | _, _ => false end).
Arguments max_nonzero_subdef /.

Lemma max_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr})
    (rnz := max_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (Num.max x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y /=;
  do ?[have [xr yr] : x%:num \in Num.real /\ y%:num \in Num.real by [];
       case: (real_ltgtP xr yr) => //
      | by rewrite /Num.max; case: ifP => //].
  - by move=> xy; rewrite gt_eqF// (lt_trans _ xy).
  - by move=> xy; rewrite gt_eqF// (lt_trans _ xy).
  - by move=> ->.
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
rewrite /Num.max; case: ifP => _;
by [rewrite ?(ge0, le0, orbT)//|apply: cmp0].
Qed.

Canonical max_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr}) :=
  Signed.mk (max_snum_subproof x y).

Lemma norm_snum_subproof {V : normedZmodType R} (x : V) :
  Signed.spec 0 MaybeZero NonNeg `|x|.
Proof. by rewrite /=. Qed.

Canonical norm_snum  {V : normedZmodType R} (x : V) :=
  Signed.mk (norm_snum_subproof x).

End NumDomainStability.

Section RcfStability.
Context {R : rcfType}.

Definition sqrt_nonzero_subdef (xnz : nullity) (xr : reality) :=
  if xr is Real (Sign >=0) then xnz else MaybeZero.
Arguments sqrt_nonzero_subdef /.

Lemma sqrt_snum_subproof xnz xr (x : {num R & xnz & xr})
    (nz := sqrt_nonzero_subdef xnz xr) :
  Signed.spec 0 nz NonNeg (Num.sqrt x%:num).
Proof.
by rewrite {}/nz; case: xnz xr x => -[[[]|]|]//= x;
   rewrite /= sqrtr_ge0// andbT sqrtr_eq0 le0F.
Qed.

Canonical sqrt_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrt_snum_subproof x).

End RcfStability.

Section NumClosedStability.
Context {R : numClosedFieldType}.

Definition sqrtC_reality_subdef (xnz : nullity) (xr : reality) :=
  if xr is Real (Sign >=0) then xr else Arbitrary.
Arguments sqrtC_reality_subdef /.

Lemma sqrtC_snum_subproof xnz xr (x : {num R & xnz & xr})
    (nz := sqrt_nonzero_subdef xnz xr) (r := sqrtC_reality_subdef xnz xr):
  Signed.spec 0 nz r (sqrtC x%:num).
Proof.
rewrite {}/nz {}/r.
by case: xnz xr x => -[[[]|]|]//= x; rewrite /= sqrtC_ge0// sqrtC_eq0 neq0 ge0.
Qed.

Canonical sqrtC_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrtC_snum_subproof x).

End NumClosedStability.

Section NatStability.
Local Open Scope nat_scope.
Implicit Type (n : nat).

Lemma nat_snum_subproof n : Signed.spec 0 MaybeZero NonNeg n.
Proof. by []. Qed.

Canonical nat_snum n := Signed.mk (nat_snum_subproof n).

Lemma succn_snum_subproof n : Signed.spec 0 NonZero NonNeg n.+1.
Proof. by []. Qed.

Canonical succn_snum n := Signed.mk (succn_snum_subproof n).

Lemma double_snum_subproof nz r (x : {compare 0 & nz & r}) :
  Signed.spec 0 nz r x%:num.*2.
Proof. by  move: nz r x => [] [[[]|]|] [[|n]]. Qed.

Canonical double_snum nz r x :=
  Signed.mk (@double_snum_subproof nz r x).

Lemma addn_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr})
    (rnz := add_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num + y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split;
by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= [[|x]//= _] [[|y]].
Qed.

Canonical addn_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr}) :=
  Signed.mk (addn_snum_subproof x y).

Lemma muln_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr})
    (rnz := mul_nonzero_subdef xnz ynz xr yr)
    (rrl := mul_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num * y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split;
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//=;
by move=> [[|x]//= _] [[|y]//= _]; rewrite muln0.
Qed.

Canonical muln_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr}) :=
  Signed.mk (muln_snum_subproof x y).

Lemma expn_snum_subproof (xnz : nullity) (xr : reality)
    (x : {compare 0 & xnz & xr}) (rr := exprn_reality_subdef xnz xr) n :
  Signed.spec 0 xnz rr (x%:num ^ n).
Proof.
rewrite {}/rr; apply/andP; split;
by move: xr xnz x => [[[]|]|] []//= [[|x]//= _]; rewrite expn_eq0.
Qed.

Canonical expn_snum (xnz : nullity) (xr : reality)
  (x : {compare 0 & xnz & xr}) n :=
  Signed.mk (expn_snum_subproof x n).

Lemma minn_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr})
    (rnz := both_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (min x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split;
by move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= [[|x]//= _] [[|y]].
Qed.

Canonical minn_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr}) :=
  Signed.mk (minn_snum_subproof x y).

Lemma maxn_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr})
    (rnz := max_nonzero_subdef xnz ynz xr yr)
    (rrl := both_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (maxn x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split;
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//=;
by move=> [[|x]//= _] [[|y]//= _]; rewrite maxnSS.
Qed.

Canonical maxn_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr}) :=
  Signed.mk (maxn_snum_subproof x y).

End NatStability.

Section Morph0.
Context {R : numDomainType} {cond : reality}.
Local Notation nR := {num R & ?=0 & cond}.
Implicit Types x y : nR.
Local Notation num := (@num _ _ (0 : R) ?=0 cond).

Lemma num_eq0 x : (x%:num == 0) = (x == (0%:sgn : nR)).
Proof. by []. Qed.

End Morph0.

Section Morph.
Context {R : numDomainType} {nz : nullity} {cond : reality}.
Local Notation nR := {num R & nz & cond}.
Implicit Types (a : R) (x y : nR).
Local Notation num := (@num _ _ (0 : R) nz cond).

Lemma num_eq : {mono num : x y / x == y}. Proof. by []. Qed.
Lemma num_le : {mono num : x y / x <= y}. Proof. by []. Qed.
Lemma num_lt : {mono num : x y / x < y}. Proof. by []. Qed.
Lemma num_min : {morph num : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle num_le -fun_if. Qed.
Lemma num_max : {morph num : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle num_le -fun_if. Qed.

Lemma num_abs_eq0 a : (`|a|%:sgn == 0%:sgn) = (a == 0).
Proof. by rewrite -normr_eq0. Qed.

End Morph.

Section MorphReal.
Context {R : numDomainType} {nz : nullity} {r : real}.
Local Notation nR := {num R & nz & r}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : R) nz r).

Lemma num_le_maxr a x y :
  a <= Num.max x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_maxr// real_comparable. Qed.

Lemma num_le_maxl a x y :
  Num.max x%:num  y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_le_maxl// real_comparable. Qed.

Lemma num_le_minr a x y :
  a <= Num.min x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_minr// real_comparable. Qed.

Lemma num_le_minl a x y :
  Num.min x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_le_minl// real_comparable. Qed.

Lemma num_lt_maxr a x y :
  a < Num.max x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_maxr// real_comparable. Qed.

Lemma num_lt_maxl a x y :
  Num.max x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_lt_maxl// real_comparable. Qed.

Lemma num_lt_minr a x y :
  a < Num.min x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_minr// real_comparable. Qed.

Lemma num_lt_minl a x y :
  Num.min x%:num y%:num < a = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_lt_minl// real_comparable. Qed.

End MorphReal.

Section MorphGe0.
Context {R : numDomainType} {nz : nullity}.
Local Notation nR := {num R & ?=0 & >=0}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : R) ?=0 >=0).

Lemma num_abs_le a x : 0 <= a -> (`|a|%:sgn <= x) = (a <= x%:num).
Proof. by move=> a0; rewrite -num_le//= ger0_norm. Qed.

Lemma num_abs_lt a x : 0 <= a -> (`|a|%:sgn < x) = (a < x%:num).
Proof. by move=> a0; rewrite -num_lt/= ger0_norm. Qed.
End MorphGe0.

Notation "x %:pos" := (x%:sgn : {posnum _}) : ring_scope.
Notation "x %:nng" := (x%:sgn : {nonneg _}) : ring_scope.

Section Posnum.
Context (R : numDomainType) (x : R) (x_gt0 : 0 < x).
Lemma posnum_subdef : (x != 0) && (0 <= x). Proof. by rewrite -lt_def. Qed.
Definition PosNum : {posnum R} := @Signed.mk _ _ 0 !=0 >=0 _ posnum_subdef.
End Posnum.
Definition NngNum (R : numDomainType) (x : R) (x_ge0 : 0 <= x) : {nonneg R} :=
  (@Signed.mk _ _ 0 ?=0 >=0 x x_ge0).

CoInductive posnum_spec (R : numDomainType) (x : R) :
  R -> bool -> bool -> bool -> Type :=
| IsPosnum (p : {posnum R}) : posnum_spec x (p%:num) false true true.

Lemma posnumP (R : numDomainType) (x : R) : 0 < x ->
  posnum_spec x x (x == 0) (0 <= x) (0 < x).
Proof.
move=> x_gt0; case: real_ltgt0P (x_gt0) => []; rewrite ?gtr0_real // => _ _.
by rewrite -[x]/(PosNum x_gt0)%:num; constructor.
Qed.

CoInductive nonneg_spec (R : numDomainType) (x : R) : R -> bool -> Type :=
| IsNonneg (p : {nonneg R}) : nonneg_spec x (p%:num) true.

Lemma nonnegP (R : numDomainType) (x : R) : 0 <= x -> nonneg_spec x x (0 <= x).
Proof. by move=> xge0; rewrite xge0 -[x]/(NngNum xge0)%:num; constructor. Qed.



(* Section PosnumOrder. *)
(* Variables (R : numDomainType). *)
(* Local Notation nR := {posnum R}. *)

(* Lemma posnum_le_total : totalPOrderMixin [porderType of nR]. *)
(* Proof. by move=> x y; apply: real_comparable. Qed. *)

(* Canonical posnum_latticeType := LatticeType nR posnum_le_total. *)
(* Canonical posnum_distrLatticeType := DistrLatticeType nR posnum_le_total. *)
(* Canonical posnum_orderType := OrderType nR posnum_le_total. *)

(* End PosnumOrder. *)

(* Section NonnegOrder. *)
(* Variables (R : numDomainType). *)
(* Local Notation nR := {nonneg R}. *)

(* Lemma nonneg_le_total : totalPOrderMixin [porderType of nR]. *)
(* Proof. by move=> x y; apply: real_comparable. Qed. *)

(* Canonical nonneg_latticeType := LatticeType nR nonneg_le_total. *)
(* Canonical nonneg_distrLatticeType := DistrLatticeType nR nonneg_le_total. *)
(* Canonical nonneg_orderType := OrderType nR nonneg_le_total. *)

(* End NonnegOrder. *)
