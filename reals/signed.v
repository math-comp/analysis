(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg ssrnum ssrint.
From mathcomp Require Import mathcomp_extra.

Attributes deprecated(since="mathcomp-analysis 1.8.0",
                      note="Use itv.v instead.").

(**md**************************************************************************)
(* # Positive, non-negative numbers, etc.                                     *)
(*                                                                            *)
(* This file develops tools to make the manipulation of numbers with a known  *)
(* sign easier, thanks to canonical structures. This adds types like          *)
(* {posnum R} for positive values in R, a notation e%:pos that infers the     *)
(* positivity of expression e according to existing canonical instances and   *)
(* %:num to cast back from type {posnum R} to R.                              *)
(* For instance, given x, y : {posnum R}, we have                             *)
(* ((x%:num + y%:num) / 2)%:pos : {posnum R} automatically inferred.          *)
(*                                                                            *)
(* ## Types for values with known sign                                        *)
(* ```                                                                        *)
(*    {posnum R} == interface type for elements in R that are positive; R     *)
(*                  must have a zmodType structure.                           *)
(*                  Allows to solve automatically goals of the form x > 0 if  *)
(*                  x is canonically a {posnum R}. {posnum R} is canonically  *)
(*                  stable by common operations. All positive natural numbers *)
(*                  ((n.+1)%:R) are also canonically in {posnum R}            *)
(*    {nonneg R} == interface types for elements in R that are non-negative;  *)
(*                  R must have a zmodType structure. Automatically solves    *)
(*                  goals of the form x >= 0. {nonneg R} is stable by         *)
(*                  common operations. All natural numbers n%:R are also      *)
(*                  canonically in {nonneg R}.                                *)
(* {compare x0 & nz & cond} == more generic type of values comparing to       *)
(*                  x0 : T according to nz and cond (see below). T must have  *)
(*                  a porderType structure. This type is shown to be a        *)
(*                  porderType. It is also an orderTpe, as soon as T is a     *)
(*                  numDomainType.                                            *)
(* {num R & nz & cond} == {compare 0%R : R & nz & cond}. T must have a        *)
(*                  zmodType structure.                                       *)
(*        {= x0} == {compare x0 & ?=0 & =0}                                   *)
(*    {= x0 : T} == same with an explicit type T                              *)
(*        {> x0} == {compare x0 & !=0 & >=0}                                  *)
(*    {> x0 : T} == same with an explicit type T                              *)
(*        {< x0} == {compare x0 & !=0 & <=0}                                  *)
(*    {< x0 : T} == same with an explicit type T                              *)
(*       {>= x0} == {compare x0 & ?=0 & >=0}                                  *)
(*   {>= x0 : T} == same with an explicit type T                              *)
(*       {<= x0} == {compare x0 & ?=0 & <=0}                                  *)
(*   {<= x0 : T} == same with an explicit type T                              *)
(*      {>=< x0} == {compare x0 & ?=0 & >=<0}                                 *)
(*  {>=< x0 : T} == same with an explicit type T                              *)
(*       {>< x0} == {compare x0 & !=0 & >=<0}                                 *)
(*   {>< x0 : T} == same with an explicit type T                              *)
(*       {!= x0} == {compare x0 & !=0 & >?<0}                                 *)
(*   {!= x0 : T} == same with an explicit type T                              *)
(*       {?= x0} == {compare x0 & ?=0 & >?<0}                                 *)
(*   {?= x0 : T} == same with an explicit type T                              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Casts from/to values with known sign                                    *)
(* ```                                                                        *)
(*        x%:pos == explicitly casts x to {posnum R}, triggers the inference  *)
(*                  of a {posnum R} structure for x.                          *)
(*        x%:nng == explicitly casts x to {nonneg R}, triggers the inference  *)
(*                  of a {nonneg R} structure for x.                          *)
(*        x%:sgn == explicitly casts x to the most precise known              *)
(*                  {compare x0 & nz & cond} according to existing canonical  *)
(*                  instances.                                                *)
(*        x%:num == explicit cast from {compare x0 & nz & cond} to R. In      *)
(*                  particular this works from {posnum R} and {nonneg R} to R.*)
(*     x%:posnum == explicit cast from {posnum R} to R.                       *)
(*     x%:nngnum == explicit cast from {nonneg R} to R.                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Nullity conditions nz                                                   *)
(* All nz above can be the following (in scope snum_nullity_scope delimited   *)
(* by %snum_nullity)                                                          *)
(* ```                                                                        *)
(*           !=0 == to encode x != 0                                          *)
(*           ?=0 == unknown nullity                                           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Reality conditions cond                                                 *)
(* All cond above can be the following (in scope snum_sign_scope delimited by *)
(* by %snum_sign)                                                             *)
(* ```                                                                        *)
(*            =0 == to encode x == 0                                          *)
(*           >=0 == to encode x >= 0                                          *)
(*           <=0 == to encode x <= 0                                          *)
(*          >=<0 == to encode x >=< 0                                         *)
(*          >?<0 == unknown reality                                           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Sign proofs                                                             *)
(* ```                                                                        *)
(*    [sgn of x] == proof that x is of sign inferred by x%:sgn                *)
(*    [gt0 of x] == proof that x > 0                                          *)
(*    [lt0 of x] == proof that x < 0                                          *)
(*    [ge0 of x] == proof that x >= 0                                         *)
(*    [le0 of x] == proof that x <= 0                                         *)
(*   [cmp0 of x] == proof that 0 >=< x                                        *)
(*   [neq0 of x] == proof that x != 0                                         *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Constructors                                                            *)
(* ```                                                                        *)
(*   PosNum xgt0 == builds a {posnum R} from a proof xgt0 : x > 0 where x : R *)
(*   NngNum xge0 == builds a {posnum R} from a proof xgt0 : x >= 0 where x : R*)
(*   Signed.mk p == builds a {compare x0 & nz & cond} from a proof p that     *)
(*                  some x satisfies sign conditions encoded by nz and cond   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Misc.                                                                   *)
(* ```                                                                        *)
(*          !! x == triggers pretyping to fill the holes of the term x. The   *)
(*                  main use case is to trigger typeclass inference in the    *)
(*                  body of a ssreflect have := !! body.                      *)
(*                  Credits: Enrico Tassi.                                    *)
(* ```                                                                        *)
(*                                                                            *)
(* A number of canonical instances are provided for common operations, if     *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(*                                                                            *)
(* Canonical instances are also provided according to types, as a             *)
(* fallback when no known operator appears in the expression. Look to         *)
(* nat_snum below for an example on how to add your favorite type.            *)
(******************************************************************************)

Reserved Notation "{ 'compare' x0 & nz & cond }"
  (at level 0, x0 at level 200, nz at level 200,
   format "{ 'compare'  x0  &  nz  &  cond }").
Reserved Notation "{ 'num' R & nz & cond }"
  (at level 0, R at level 200, nz at level 200,
   format "{ 'num'  R  &  nz  &  cond }").
Reserved Notation "{ = x0 }" (at level 0, format "{ =  x0 }").
Reserved Notation "{ > x0 }" (at level 0, format "{ >  x0 }").
Reserved Notation "{ < x0 }" (at level 0, format "{ <  x0 }").
Reserved Notation "{ >= x0 }" (at level 0, format "{ >=  x0 }").
Reserved Notation "{ <= x0 }" (at level 0, format "{ <=  x0 }").
Reserved Notation "{ >=< x0 }" (at level 0, format "{ >=<  x0 }").
Reserved Notation "{ >< x0 }" (at level 0, format "{ ><  x0 }").
Reserved Notation "{ != x0 }" (at level 0, format "{ !=  x0 }").
Reserved Notation "{ ?= x0 }" (at level 0, format "{ ?=  x0 }").
Reserved Notation "{ = x0 : T }" (at level 0, format "{ =  x0  :  T }").
Reserved Notation "{ > x0 : T }" (at level 0, format "{ >  x0  :  T }").
Reserved Notation "{ < x0 : T }" (at level 0, format "{ <  x0  :  T }").
Reserved Notation "{ >= x0 : T }" (at level 0, format "{ >=  x0  :  T }").
Reserved Notation "{ <= x0 : T }" (at level 0, format "{ <=  x0  :  T }").
Reserved Notation "{ >=< x0 : T }" (at level 0, format "{ >=<  x0  :  T }").
Reserved Notation "{ >< x0 : T }" (at level 0, format "{ ><  x0  :  T }").
Reserved Notation "{ != x0 : T }" (at level 0, format "{ !=  x0  :  T }").
Reserved Notation "{ ?= x0 : T }" (at level 0, format "{ ?=  x0  :  T }").
Reserved Notation "=0" (at level 0, format "=0").
Reserved Notation ">=0" (at level 0, format ">=0").
Reserved Notation "<=0" (at level 0, format "<=0").
Reserved Notation ">=<0" (at level 0, format ">=<0").
Reserved Notation ">?<0" (at level 0, format ">?<0").
Reserved Notation "!=0" (at level 0, format "!=0").
Reserved Notation "?=0" (at level 0, format "?=0").

Reserved Notation "x %:sgn" (at level 2, format "x %:sgn").
Reserved Notation "x %:num" (at level 2, format "x %:num").
Reserved Notation "x %:posnum" (at level 2, format "x %:posnum").
Reserved Notation "x %:nngnum" (at level 2, format "x %:nngnum").
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

Notation "!! x" := (ltac:(refine x)) (only parsing).
(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
#[global] Hint Mode infer ! : typeclass_instances.
#[global] Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Module Import KnownSign.
Variant nullity := NonZero | MaybeZero.
Coercion nullity_bool nz := if nz is NonZero then true else false.
Definition nz_of_bool b := if b then NonZero else MaybeZero.

Variant sign := EqZero | NonNeg | NonPos.
Variant real := Sign of sign | AnySign.
Variant reality := Real of real | Arbitrary.

Definition wider_nullity xnz ynz :=
  match xnz, ynz with
  | MaybeZero, _
  | NonZero, NonZero => true
  | NonZero, MaybeZero => false
  end.
Definition wider_sign xs ys :=
  match xs, ys with
  | NonNeg, NonNeg | NonNeg, EqZero
  | NonPos, NonPos | NonPos, EqZero
  | EqZero, EqZero => true
  | NonNeg, NonPos | NonPos, NonNeg
  | EqZero, NonPos | EqZero, NonNeg => false
  end.
Definition wider_real xr yr :=
  match xr, yr with
  | AnySign, _ => true
  | Sign sx, Sign sy => wider_sign sx sy
  | Sign _, AnySign => false
  end.
Definition wider_reality xr yr :=
  match xr, yr with
  | Arbitrary, _ => true
  | Real xr, Real yr => wider_real xr yr
  | Real _, Arbitrary => false
  end.
End KnownSign.

Module Signed.
Section Signed.
Context (disp : Order.disp_t) (T : porderType disp) (x0 : T).

Local Coercion is_real r := if r is Real _ then true else false.
Definition reality_cond (n : reality) (x : T) :=
  match n with
  | Real (Sign EqZero) => x == x0
  | Real (Sign NonNeg) => x >= x0
  | Real (Sign NonPos) => x <= x0
  | Real AnySign       => (x0 <= x) || (x <= x0)
  | Arbitrary          => true
  end.

Record def (nz : nullity) (cond : reality) := Def {
  r :> T;
  #[canonical=no]
  P : (nz ==> (r != x0)) && reality_cond cond r
}.

End Signed.

Notation spec x0 nz cond x :=
  ((nullity_bool nz%snum_nullity ==> (x != x0))
   && (reality_cond x0 cond%snum_sign x)).

Record typ d nz cond := Typ {
  sort : porderType d;
  #[canonical=no]
  sort_x0 : sort;
  #[canonical=no]
  allP : forall x : sort, spec sort_x0 nz cond x
}.

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
Notation "=0" := EqZero : snum_sign_scope.
Notation ">=0" := NonNeg : snum_sign_scope.
Notation "<=0" := NonPos : snum_sign_scope.
Notation ">=<0" := AnySign : snum_sign_scope.
Notation ">?<0" := Arbitrary : snum_sign_scope.
Notation "!=0" := NonZero : snum_nullity_scope.
Notation "?=0" := MaybeZero : snum_nullity_scope.
Notation "{ 'compare' x0 & nz & cond }" := (def x0 nz cond) : type_scope.
Notation "{ 'num' R & nz & cond }" := (def (0%R : R) nz cond) : ring_scope.
Notation "{ = x0 : T }" := (def (x0 : T) MaybeZero EqZero) : type_scope.
Notation "{ > x0 : T }" := (def (x0 : T) NonZero NonNeg) : type_scope.
Notation "{ < x0 : T }" := (def (x0 : T) NonZero NonPos) : type_scope.
Notation "{ >= x0 : T }" := (def (x0 : T) MaybeZero NonNeg) : type_scope.
Notation "{ <= x0 : T }" := (def (x0 : T) MaybeZero NonPos) : type_scope.
Notation "{ >< x0 : T }" := (def (x0 : T) NonZero Real) : type_scope.
Notation "{ >=< x0 : T }" := (def (x0 : T) MaybeZero Real) : type_scope.
Notation "{ != x0 : T }" := (def (x0 : T) NonZero Arbitrary) : type_scope.
Notation "{ ?= x0 : T }" := (def (x0 : T) MaybeZero Arbitrary) : type_scope.
Notation "{ = x0 }" := (def x0 MaybeZero EqZero) : type_scope.
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
Notation "x %:posnum" := (@num _ _ 0%R !=0 >=0 x) : ring_scope.
Definition nonneg (R : numDomainType) of phant R := {>= 0%R : R}.
Notation "{ 'nonneg' R }" := (@nonneg _ (Phant R))  : ring_scope.
Notation "x %:nngnum" := (@num _ _ 0%R ?=0 >=0 x) : ring_scope.
Arguments r {disp T x0 nz cond}.
End Exports.
End Signed.
Export Signed.Exports.

Section POrder.
Variables (d : Order.disp_t) (T : porderType d).
Variables (x0 : T) (nz : nullity) (cond : reality).
Local Notation sT := {compare x0 & nz & cond}.
HB.instance Definition _ := [isSub for @Signed.r d T x0 nz cond].
HB.instance Definition _ : Order.POrder d sT := [POrder of sT by <:].
End POrder.

Lemma top_typ_subproof d (T : porderType d) (x0 x : T) :
  Signed.spec x0 ?=0 >?<0 x.
Proof. by []. Qed.

Canonical top_typ d (T : porderType d) (x0 : T) :=
  Signed.Typ (top_typ_subproof x0).

Lemma real_domain_typ_subproof (R : realDomainType) (x : R) :
  Signed.spec 0%R ?=0 >=<0 x.
Proof. by rewrite /= -realE num_real. Qed.

Canonical real_domain_typ (R : realDomainType) :=
  Signed.Typ (@real_domain_typ_subproof R).

Lemma real_field_typ_subproof (R : realFieldType) (x : R) :
  Signed.spec 0%R ?=0 >=<0 x.
Proof. exact: real_domain_typ_subproof. Qed.

Canonical real_field_typ (R : realFieldType) :=
  Signed.Typ (@real_field_typ_subproof R).

Lemma nat_typ_subproof (x : nat) : Signed.spec 0%N ?=0 >=0 x.
Proof. by []. Qed.

Canonical nat_typ := Signed.Typ nat_typ_subproof.

Lemma typ_snum_subproof d nz cond (xt : Signed.typ d nz cond)
    (x : Signed.sort xt) :
  Signed.spec (Signed.sort_x0 xt) nz cond x.
Proof. by move: xt x => []. Qed.

(** This adds _ <- Signed.r ( typ_snum )
   to canonical projections (c.f., Print Canonical Projections
   Signed.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Signed.typ, like the ones above, will be looked for. *)
Canonical typ_snum d nz cond (xt : Signed.typ d nz cond) (x : Signed.sort xt) :=
  Signed.mk (typ_snum_subproof x).

(* Section Order. *)
(* Variables (d : unit) (T : orderType d) (x0 : T) (nz : nullity) (cond : reality). *)
(* Local Notation sT := {compare x0 & nz & cond}. *)

(* Lemma signed_le_total : totalPOrderMixin [porderType of sT]. *)
(* Proof. by move=> x y; apply: le_total. Qed. *)

(* Canonical signed_latticeType := LatticeType sT signed_le_total. *)
(* Canonical signed_distrLatticeType := DistrLatticeType sT signed_le_total. *)
(* Canonical signed_orderType := OrderType sT signed_le_total. *)

(* End Order. *)

Class unify {T} f (x y : T) := Unify : f x y = true.
#[global] Hint Mode unify - - - + : typeclass_instances.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[global] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y := id.
#[global]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_nz nzx nzy :=
  (unify wider_nullity nzx%snum_nullity nzy%snum_nullity).
Notation unify_r rx ry :=
  (unify wider_reality rx%snum_sign ry%snum_sign).

#[global] Instance anysign_wider_real sign : unify_r (Real AnySign) (Real sign).
Proof. by []. Qed.

#[global] Instance any_reality_wider_eq0 cond : unify_r cond =0.
Proof. by case: cond => [[[]|]|]. Qed.

Section Theory.
Context {d : Order.disp_t} {T : porderType d} {x0 : T}.
Context {nz : nullity} {cond : reality}.
Local Notation sT := {compare x0 & nz & cond}.
Implicit Type x : sT.

Lemma signed_intro {x} : x%:num = x%:num :> T. Proof. by []. Qed.

Lemma bottom x : unify_nz !=0 nz -> unify_r =0 cond -> False.
Proof.
by move: x => [x /= /andP[]]; move: cond nz => [[[]|]|] [] //= /[swap] ->.
Qed.

Lemma gt0 x : unify_nz !=0 nz -> unify_r >=0 cond -> x0 < x%:num :> T.
Proof.
move: x => [x /= /andP[]].
by move: cond nz => [[[]|]|] [] //=; rewrite lt_def => -> // /eqP -> /=.
Qed.

Lemma le0F x : unify_nz !=0 nz -> unify_r >=0 cond -> x%:num <= x0 :> T = false.
Proof. by move=> ? ?; rewrite lt_geF//; apply: gt0. Qed.

Lemma lt0 x : unify_nz !=0 nz -> unify_r <=0 cond -> x%:num < x0 :> T.
Proof.
move: x => [x /= /andP[]].
move: cond nz => [[[]|]|] [] //=; rewrite lt_def [x0 == _]eq_sym => -> //.
by move=> /eqP -> /=.
Qed.

Lemma ge0F x : unify_nz !=0 nz -> unify_r <=0 cond -> x0 <= x%:num :> T = false.
Proof. by move=> ? ?; rewrite lt_geF//; apply: lt0. Qed.

Lemma ge0 x : unify_r >=0 cond -> x0 <= x%:num :> T.
Proof.
by case: x => [x /= /andP[]]; move: cond nz => [[[]|]|] [] //= _ /eqP ->.
Qed.

Lemma lt0F x : unify_r >=0 cond -> x%:num < x0 :> T = false.
Proof. by move=> ?; rewrite le_gtF//; apply: ge0. Qed.

Lemma le0 x : unify_r <=0 cond -> x0 >= x%:num :> T.
Proof.
by case: x => [x /= /andP[]]; move: cond nz => [[[]|]|] [] //= _ /eqP ->.
Qed.

Lemma gt0F x : unify_r <=0 cond -> x0 < x%:num :> T = false.
Proof. by move=> ?; rewrite le_gtF//; apply: le0. Qed.

Lemma cmp0 x : unify_r (Real AnySign) cond -> (x0 >=< x%:num).
Proof.
case: x => [x /= /andP[]].
by move: cond nz => [[[]|]|] [] //= _;
  do ?[by move=> /eqP ->; rewrite comparablexx];
  move=> sx; rewrite /Order.comparable sx// orbT.
Qed.

Lemma neq0 x : unify_nz !=0 nz -> x%:num != x0 :> T.
Proof. by case: x => [x /= /andP[]]; move: cond nz => [[[]|]|] []. Qed.

Lemma eq0F x : unify_nz !=0 nz -> x%:num == x0 :> T = false.
Proof. by move=> /neq0-/(_ x)/negPf->. Qed.

Lemma eq0 x : unify_r =0 cond -> x%:num = x0.
Proof.
by case: x => [x /= /andP[_]]; move: cond nz => [[[]|]|] [] //= /eqP ->.
Qed.

Lemma widen_signed_subproof x nz' cond' :
  unify_nz nz' nz -> unify_r cond' cond ->
  Signed.spec x0 nz' cond' x%:num.
Proof.
case: x => [x /= /andP[]].
by case: cond nz cond' nz' => [[[]|]|] [] [[[]|]|] [] //= nz'' cond'';
   rewrite ?nz'' ?cond'' ?orbT //; move: cond'' nz'' => /eqP ->; rewrite lexx.
Qed.

Definition widen_signed x nz' cond'
    (unz : unify_nz nz' nz) (ucond : unify_r cond' cond) :=
  Signed.mk (widen_signed_subproof x unz ucond).

Lemma widen_signedE x (unz : unify_nz nz nz) (ucond : unify_r cond cond) :
  @widen_signed x nz cond unz ucond = x.
Proof. exact/val_inj. Qed.

Lemma posE (x : sT) (unz : unify_nz !=0 nz) (ucond : unify_r >=0 cond) :
  (widen_signed x%:num%:sgn unz ucond)%:num = x%:num.
Proof. by []. Qed.

Lemma nngE (x : sT) (unz : unify_nz ?=0 nz) (ucond : unify_r >=0 cond) :
  (widen_signed x%:num%:sgn unz ucond)%:num = x%:num.
Proof. by []. Qed.

End Theory.

Arguments bottom {d T x0 nz cond} _ {_ _}.
Arguments gt0 {d T x0 nz cond} _ {_ _}.
Arguments le0F {d T x0 nz cond} _ {_ _}.
Arguments lt0 {d T x0 nz cond} _ {_ _}.
Arguments ge0F {d T x0 nz cond} _ {_ _}.
Arguments ge0 {d T x0 nz cond} _ {_}.
Arguments lt0F {d T x0 nz cond} _ {_}.
Arguments le0 {d T x0 nz cond} _ {_}.
Arguments gt0F {d T x0 nz cond} _ {_}.
Arguments cmp0 {d T x0 nz cond} _ {_}.
Arguments neq0 {d T x0 nz cond} _ {_}.
Arguments eq0F {d T x0 nz cond} _ {_}.
Arguments eq0 {d T x0 nz cond} _ {_}.
Arguments widen_signed {d T x0 nz cond} _ {_ _ _ _}.
Arguments widen_signedE {d T x0 nz cond} _ {_ _}.
Arguments posE {d T x0 nz cond} _ {_ _}.
Arguments nngE {d T x0 nz cond} _ {_ _}.

Notation "[ 'gt0' 'of' x ]" := (ltac:(refine (gt0 x%:sgn))).
Notation "[ 'lt0' 'of' x ]" := (ltac:(refine (lt0 x%:sgn))).
Notation "[ 'ge0' 'of' x ]" := (ltac:(refine (ge0 x%:sgn))).
Notation "[ 'le0' 'of' x ]" := (ltac:(refine (le0 x%:sgn))).
Notation "[ 'cmp0' 'of' x ]" := (ltac:(refine (cmp0 x%:sgn))).
Notation "[ 'neq0' 'of' x ]" := (ltac:(refine (neq0 x%:sgn))).

#[global] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: gt0] : core.
#[global] Hint Extern 0 (is_true (_ < 0%R)%O) => solve [apply: lt0] : core.
#[global] Hint Extern 0 (is_true (0%R <= _)%O) => solve [apply: ge0] : core.
#[global] Hint Extern 0 (is_true (_ <= 0%R)%O) => solve [apply: le0] : core.
#[global] Hint Extern 0 (is_true (_ \is Num.real)) => solve [apply: cmp0] : core.
#[global] Hint Extern 0 (is_true (0%R >=< _)%O) => solve [apply: cmp0] : core.
#[global] Hint Extern 0 (is_true (_ != 0%R)%O) => solve [apply: neq0] : core.

Notation "x %:pos" := (widen_signed x%:sgn : {posnum _}) (only parsing)
  : ring_scope.
Notation "x %:nng" := (widen_signed x%:sgn : {nonneg _}) (only parsing)
  : ring_scope.
Notation "x %:pos" := (@widen_signed _ _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x)) !=0 (Real (Sign >=0)) _ _)
  (only printing) : ring_scope.
Notation "x %:nng" := (@widen_signed _ _ _ _ _
    (@Signed.from _ _ _ _ _ _ (Phantom _ x)) ?=0 (Real (Sign >=0)) _ _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Section Order.
Variables (R : numDomainType) (nz : nullity) (r : real).
Local Notation nR := {num R & nz & r}.

Lemma signed_le_total : total (<=%O : rel nR).
Proof. by move=> x y; apply: real_comparable => /=. Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build ring_display nR
  signed_le_total.

End Order.

Section POrderStability.
Context {disp : Order.disp_t} {T : porderType disp} {x0 : T}.

Definition min_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool
    (xnz && ynz
     || xnz && yr && match xr with Real (Sign <=0) => true | _ => false end
     || ynz && match yr with Real (Sign <=0) => true | _ => false end).
Arguments min_nonzero_subdef /.

Definition min_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign =0), Real (Sign =0)
  | Real (Sign =0), Real (Sign >=0)
  | Real (Sign >=0), Real (Sign =0) => =0
  | Real (Sign >=0), Real (Sign >=0) => >=0
  | Real (Sign <=0), Real _
  | Real _, Real (Sign <=0) => <=0
  | Real _, Real _ => >=<0
  | _, _ => >?<0
  end.
Arguments min_reality_subdef /.

Lemma min_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare x0 & xnz & xr}) (y : {compare x0 & ynz & yr})
    (rnz := min_nonzero_subdef xnz ynz xr yr)
    (rrl := min_reality_subdef xnz ynz xr yr) :
  Signed.spec x0 rnz rrl (Order.min x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y; rewrite /Order.min;
    do ?[by case: (bottom x)|by case: (bottom y)
        |by case: ifP; rewrite ?eq0F// => xlty;
            have := !! lt_trans xlty (lt0 y); rewrite lt_neqAle => /andP[]
        |by rewrite ifT ?eq0F//; apply: lt_le_trans (ge0 y); exact: lt0
        |by have := !! le0 y;
            rewrite le_eqVlt => /predU1P[->|]; rewrite ?lt0 ?eq0F//;
            case: ifP => _; rewrite ?eq0F// lt_neqAle => /andP[]].
  have /orP[x0ley|] := !! cmp0 y.
    by rewrite ifT ?eq0F//; apply: lt_le_trans x0ley; exact: lt0.
    rewrite le_eqVlt => /predU1P[->|]; rewrite ?lt0 ?eq0F//.
  by case: ifP => _; rewrite ?eq0F// lt_neqAle => /andP[].
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by case: (bottom x)|by case: (bottom y)
      |by apply: comparable_minr; exact: cmp0
      |by rewrite minEle; case: ifP; rewrite ge0
      |by rewrite ?eq0 minEle ?ge0
      |by rewrite ?eq0 minElt; case: ifP; rewrite ?eq0// lt0F
      |by rewrite minEle; case: ifP => [xlty|]; rewrite ?le0//;
          apply: (le_trans xlty); rewrite le0
      |by have /orP[x0ley|] := !! cmp0 y;
          [rewrite minEle ifT ?le0//; apply: le_trans x0ley; exact: le0
          |rewrite minEle; case: ifP => //; exact: le_trans]].
Qed.

Canonical min_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare x0 & xnz & xr}) (y : {compare x0 & ynz & yr}) :=
  Signed.mk (min_snum_subproof x y).

Definition max_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool
    (xnz && ynz
     || xnz && match xr with Real (Sign >=0) => true | _ => false end
     || ynz && xr && match yr with Real (Sign >=0) => true | _ => false end).
Arguments max_nonzero_subdef /.

Definition max_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign =0), Real (Sign =0)
  | Real (Sign =0), Real (Sign <=0)
  | Real (Sign <=0), Real (Sign =0) => =0
  | Real (Sign <=0), Real (Sign <=0) => <=0
  | Real (Sign >=0), Real _
  | Real _, Real (Sign >=0) => >=0
  | Real _, Real _ => >=<0
  | _, _ => >?<0
  end.
Arguments max_reality_subdef /.

Lemma max_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare x0 & xnz & xr}) (y : {compare x0 & ynz & yr})
    (rnz := max_nonzero_subdef xnz ynz xr yr)
    (rrl := max_reality_subdef xnz ynz xr yr) :
  Signed.spec x0 rnz rrl (Order.max x%:num y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y; rewrite maxElt;
    do ?[by case: (bottom x)|by case: (bottom y)
        |by case: ifP => [xlty|]; rewrite ?eq0F//;
            do [suff : (x0 < y%:num)%O by rewrite lt_def => /andP[]];
            apply: le_lt_trans xlty; exact: ge0
        |by rewrite ifT ?eq0F//; apply: le_lt_trans (gt0 y); exact: le0
        |by have := !! ge0 x;
            rewrite le_eqVlt => /predU1P[<-|]; rewrite ?gt0 ?eq0F//;
            case: ifP => _; rewrite ?eq0F// lt_def => /andP[]].
  have /orP[|xlex0] := !! cmp0 x.
    rewrite le_eqVlt => /predU1P[<-|]; rewrite ?gt0 ?eq0F//.
    by case: ifP => _; rewrite ?eq0F// lt_def => /andP[].
  by rewrite ifT ?eq0F//; apply: (le_lt_trans xlex0); exact: gt0.
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by case: (bottom x)|by case: (bottom y)
      |by apply: comparable_maxr; exact: cmp0
      |by rewrite ?eq0 maxEle ?le0
      |by rewrite ?eq0 maxElt ifF// le_gtF// le0
      |by rewrite maxEle; case: ifP; rewrite ?ge0//; exact/le_trans/ge0
      |by rewrite maxElt; case: ifP => [xlty|]; rewrite ?le0//
      |by have /orP[|xlex0] := !! cmp0 x;
          [rewrite maxEle; case: ifP => // /[swap]; exact: le_trans
          |rewrite maxEle ifT ?ge0//; apply: (le_trans xlex0); exact: ge0]].
Qed.

Canonical max_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {compare x0 & xnz & xr}) (y : {compare x0 & ynz & yr}) :=
  Signed.mk (max_snum_subproof x y).

End POrderStability.

Section NumDomainStability.
Context {R : numDomainType}.

Lemma zero_snum_subproof : Signed.spec 0 ?=0 =0 (0 : R).
Proof. exact: eqxx. Qed.

Canonical zero_snum := Signed.mk zero_snum_subproof.

Lemma one_snum_subproof : Signed.spec 0 !=0 >=0 (1 : R).
Proof. by rewrite /= oner_eq0 ler01. Qed.

Canonical one_snum := Signed.mk one_snum_subproof.

Definition opp_reality_subdef (xnz : nullity) (xr : reality) : reality :=
  match xr with
  | Real (Sign =0) => =0
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
  | Real (Sign >=0), Real (Sign =0)
  | Real (Sign =0), Real (Sign >=0)
  | Real (Sign <=0), Real (Sign =0)
  | Real (Sign =0), Real (Sign <=0)
  | Real (Sign =0), Real (Sign =0)
  | Real (Sign >=0), Real (Sign >=0)
  | Real (Sign <=0), Real (Sign <=0) => true
  | _, _ => false
  end.

Definition add_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool (add_samesign_subdef xnz ynz xr yr && (xnz || ynz)).
Arguments add_nonzero_subdef /.

Definition add_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign =0), Real (Sign =0) => =0
  | Real (Sign >=0), Real (Sign =0)
  | Real (Sign =0), Real (Sign >=0)
  | Real (Sign >=0), Real (Sign >=0) => >=0
  | Real (Sign <=0), Real (Sign =0)
  | Real (Sign =0), Real (Sign <=0)
  | Real (Sign <=0), Real (Sign <=0) => <=0
  | Real _, Real _ => >=<0
  | _, _ => >?<0
  end.
Arguments add_reality_subdef /.

Lemma add_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr})
    (rnz := add_nonzero_subdef xnz ynz xr yr)
    (rrl := add_reality_subdef xnz ynz xr yr) :
  Signed.spec 0 rnz rrl (x%:num + y%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  by rewrite 1?addr_ss_eq0 ?(eq0F, ge0, le0, andbF, orbT).
have addr_le0 (a b : R) : a <= 0 -> b <= 0 -> a + b <= 0.
  by rewrite -!oppr_ge0 opprD; apply: addr_ge0.
move: xr yr xnz ynz x y => [[[]|]|] [[[]|]|] [] []//= x y;
  do ?[by rewrite addr_ge0|by rewrite addr_le0|by rewrite -realE realD
      |by case: (bottom x)|by case: (bottom y)|by rewrite !eq0 addr0].
Qed.

Canonical add_snum (xnz ynz : nullity) (xr yr : reality)
    (x : {num R & xnz & xr}) (y : {num R & ynz & yr}) :=
  Signed.mk (add_snum_subproof x y).

Definition mul_nonzero_subdef (xnz ynz : nullity) (xr yr : reality) :=
  nz_of_bool (xnz && ynz).
Arguments mul_nonzero_subdef /.

Definition mul_reality_subdef (xnz ynz : nullity) (xr yr : reality) : reality :=
  match xr, yr with
  | Real (Sign =0), _ | _, Real (Sign =0) => =0
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
   do ?[by rewrite mulr_ge0|by rewrite mulr_le0_ge0
       |by rewrite mulr_ge0_le0|by rewrite mulr_le0|by rewrite -realE realM
       |by case: (bottom x)|by case: (bottom y)|by rewrite eq0 ?mulr0// mul0r].
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
  do ?[by case: (bottom x)|by case: (bottom n)
      |by rewrite mulrn_wge0|by rewrite mulrn_wle0|by rewrite eq0 mul0rn
      |by apply: real_comparable; rewrite ?real0 ?realrMn].
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
move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []/= x n //;
  do ?[by case: (bottom x)|by case: (bottom n)
      |by rewrite mulrz_ge0|by rewrite mulrz_le0_ge0|by rewrite eq0 mul0rz
      |by rewrite mulrz_ge0_le0|by rewrite mulrz_le0|by rewrite eq0 mulr0z
      |by rewrite -realE rpredMz//; apply: cmp0].
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

Definition exprn_nonzero_subdef (xnz nnz : nullity)
    (xr nr : reality) : nullity :=
  nz_of_bool (xnz || match nr with Real (Sign =0) => true | _ => false end).
Arguments exprn_nonzero_subdef /.

Definition exprn_reality_subdef (xnz nnz : nullity)
    (xr nr : reality) : reality :=
  match xr, nr with
  | _, Real (Sign =0) => >=0
  | Real (Sign =0), _ => (if nnz then =0 else >=0)%snum_sign
  | Real (Sign >=0), _ => >=0
  | Real _, _ => >=<0
  | _, _ => >?<0
  end.
Arguments exprn_reality_subdef /.

Lemma exprn_snum_subproof (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {compare 0%N & nnz & nr})
    (rnz := exprn_nonzero_subdef xnz nnz xr nr)
    (rrl := exprn_reality_subdef xnz nnz xr nr) :
  Signed.spec 0 rnz rrl (x%:num ^+ n%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  by move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []// x n;
    do ?[by case: (bottom x)|by case: (bottom n)];
    rewrite expf_eq0/= ?eq0// ?eq0F ?andbF//.
move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []/= x [[|n]//= _] //;
  do ?[by case: (bottom x)|by case: (bottom n)|by rewrite [_ || _]realX
      |by rewrite eq0 expr0n|exact: exprn_ge0|by rewrite expr0 ler01].
Qed.

Canonical exprn_snum (xnz nnz : nullity) (xr nr : reality)
    (x : {num R & xnz & xr}) (n : {compare 0%N & nnz & nr}) :=
  Signed.mk (exprn_snum_subproof x n).

Lemma norm_snum_subproof {V : normedZmodType R} (x : V) :
  Signed.spec 0 ?=0 >=0 `|x|.
Proof. by rewrite /=. Qed.

Canonical norm_snum {V : normedZmodType R} (x : V) :=
  Signed.mk (norm_snum_subproof x).

End NumDomainStability.

Section RcfStability.
Context {R : rcfType}.

Definition sqrt_nonzero_subdef (xnz : nullity) (xr : reality) :=
  if xr is Real (Sign >=0) then xnz else MaybeZero.
Arguments sqrt_nonzero_subdef /.

Lemma sqrt_snum_subproof xnz xr (x : {num R & xnz & xr})
    (nz := sqrt_nonzero_subdef xnz xr) :
  Signed.spec 0 nz >=0 (Num.sqrt x%:num).
Proof.
by rewrite {}/nz; case: xnz xr x => -[[[]|]|]//= x;
   rewrite /= sqrtr_ge0// andbT sqrtr_eq0 le0F.
Qed.

Canonical sqrt_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrt_snum_subproof x).

End RcfStability.

Section NumClosedStability.
Context {R : numClosedFieldType}.

Definition sqrtC_reality_subdef (xnz : nullity) (xr : reality) : reality :=
  match xr with
  | Real (Sign =0) => =0
  | Real (Sign >=0) => >=0
  | _ => >?<0
  end.
Arguments sqrtC_reality_subdef /.

Lemma sqrtC_snum_subproof xnz xr (x : {num R & xnz & xr})
    (r := sqrtC_reality_subdef xnz xr) :
  Signed.spec 0 xnz r (sqrtC x%:num).
Proof.
rewrite {}/r; apply/andP; split.
  by rewrite sqrtC_eq0; case: xr xnz x => [[[]|]|] [] /=.
by case: xr xnz x => [[[]|]|] []//= x; rewrite ?sqrtC_ge0// sqrtC_eq0 eq0.
Qed.

Canonical sqrtC_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrtC_snum_subproof x).

End NumClosedStability.

Section NatStability.
Local Open Scope nat_scope.
Implicit Type (n : nat).

Lemma zeron_snum_subproof : Signed.spec 0 ?=0 =0 0.
Proof. by []. Qed.

Canonical zeron_snum := Signed.mk zeron_snum_subproof.

Lemma succn_snum_subproof n : Signed.spec 0 !=0 >=0 n.+1.
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
    (rrl := add_reality_subdef xnz ynz xr yr) :
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

Lemma expn_snum_subproof (xnz nnz : nullity) (xr nr : reality)
    (x : {compare 0 & xnz & xr}) (n : {compare 0 & nnz & nr})
    (rnz := exprn_nonzero_subdef xnz nnz xr nr)
    (rrl := exprn_reality_subdef xnz nnz xr nr) :
  Signed.spec 0 rnz rrl (x%:num ^ n%:num).
Proof.
rewrite {}/rnz {}/rrl; apply/andP; split.
  move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []// x n;
    do ?[by case: (bottom x)|by case: (bottom n)
        |by rewrite ?eq0 ?expn0// expn_eq0 ?eq0F].
move: xr nr xnz nnz x n => [[[]|]|] [[[]|]|] [] []/= x [[|n]//= _] //;
  do ?[by case: (bottom x)|by case: (bottom n)|by rewrite eq0 exp0n].
Qed.

Canonical expn_snum (xnz nnz : nullity) (xr nr : reality)
    (x : {compare 0 & xnz & xr}) (n : {compare 0 & nnz & nr}) :=
  Signed.mk (expn_snum_subproof x n).

Lemma minn_snum_subproof (xnz ynz : nullity) (xr yr : reality)
    (x : {compare 0 & xnz & xr}) (y : {compare 0 & ynz & yr})
    (rnz := min_nonzero_subdef xnz ynz xr yr)
    (rrl := min_reality_subdef xnz ynz xr yr) :
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
    (rrl := max_reality_subdef xnz ynz xr yr) :
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

Section IntStability.

Lemma Posz_snum_subproof (xnz : nullity) (xr : reality)
    (x : {compare 0%N & xnz & xr}) :
  Signed.spec 0%Z xnz xr (Posz x%:num).
Proof.
by apply/andP; split; move: xr xnz x => [[[]|]|] []//=; move=> [[|x]//= _].
Qed.

Canonical Posz_snum (xnz : nullity) (xr : reality)
    (x : {compare 0%N & xnz & xr}) :=
  Signed.mk (Posz_snum_subproof x).

Lemma Negz_snum_subproof (n : nat) : Signed.spec 0%Z !=0 <=0 (Negz n).
Proof. by []. Qed.

Canonical Negz_snum n := Signed.mk (Negz_snum_subproof n).

End IntStability.

Section Morph0.
Context {R : numDomainType} {cond : reality}.
Local Notation nR := {num R & ?=0 & cond}.
Implicit Types x y : nR.
Local Notation num := (@num _ _ (0 : R) ?=0 cond).

Lemma num_eq0 x : (x%:num == 0) = (x == (widen_signed 0%:sgn : nR)).
Proof. by []. Qed.

End Morph0.

Section Morph.
Context {d : Order.disp_t} {T : porderType d}.
Context {x0 : T} {nz : nullity} {cond : reality}.
Local Notation sT := {compare x0 & nz & cond}.
Implicit Types x y : sT.
Local Notation num := (@num _ _ x0 nz cond).

Lemma num_eq : {mono num : x y / x == y}. Proof. by []. Qed.
Lemma num_le : {mono num : x y / (x <= y)%O}. Proof. by []. Qed.
Lemma num_lt : {mono num : x y / (x < y)%O}. Proof. by []. Qed.
Lemma num_min : {morph num : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle num_le -fun_if. Qed.
Lemma num_max : {morph num : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle num_le -fun_if. Qed.

End Morph.

Section MorphNum.
Context {R : numDomainType} {nz : nullity} {cond : reality}.
Local Notation nR := {num R & nz & cond}.
Implicit Types (a : R) (x y : nR).
Local Notation num := (@num _ _ (0 : R) nz cond).

Lemma num_abs_eq0 a : (`|a|%:nng == 0%:nng) = (a == 0).
Proof. by rewrite -normr_eq0. Qed.

End MorphNum.

Section MorphReal.
Context {R : numDomainType} {nz : nullity} {r : real}.
Local Notation nR := {num R & nz & r}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : R) nz r).

Lemma num_le_max a x y :
  a <= Num.max x%:num y%:num = (a <= x%:num) || (a <= y%:num).
Proof. by rewrite -comparable_le_max// real_comparable. Qed.

Lemma num_ge_max a x y :
  Num.max x%:num y%:num <= a = (x%:num <= a) && (y%:num <= a).
Proof. by rewrite -comparable_ge_max// real_comparable. Qed.

Lemma num_le_min a x y :
  a <= Num.min x%:num y%:num = (a <= x%:num) && (a <= y%:num).
Proof. by rewrite -comparable_le_min// real_comparable. Qed.

Lemma num_ge_min a x y :
  Num.min x%:num y%:num <= a = (x%:num <= a) || (y%:num <= a).
Proof. by rewrite -comparable_ge_min// real_comparable. Qed.

Lemma num_lt_max a x y :
  a < Num.max x%:num y%:num = (a < x%:num) || (a < y%:num).
Proof. by rewrite -comparable_lt_max// real_comparable. Qed.

Lemma num_gt_max a x y :
  Num.max x%:num  y%:num < a = (x%:num < a) && (y%:num < a).
Proof. by rewrite -comparable_gt_max// real_comparable. Qed.

Lemma num_lt_min a x y :
  a < Num.min x%:num y%:num = (a < x%:num) && (a < y%:num).
Proof. by rewrite -comparable_lt_min// real_comparable. Qed.

Lemma num_gt_min a x y :
  Num.min x%:num y%:num < a = (x%:num < a) || (y%:num < a).
Proof. by rewrite -comparable_gt_min// real_comparable. Qed.

End MorphReal.
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_le_max`")]
Notation num_le_maxr := num_le_max (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_ge_max`")]
Notation num_le_maxl := num_ge_max (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_le_min`")]
Notation num_le_minr := num_le_min (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_ge_min`")]
Notation num_le_minl := num_ge_min (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_lt_max`")]
Notation num_lt_maxr := num_lt_max (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_gt_max`")]
Notation num_lt_maxl := num_gt_max (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_lt_min`")]
Notation num_lt_minr := num_lt_min (only parsing).
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed `num_gt_min`")]
Notation num_lt_minl := num_gt_min (only parsing).

Section MorphGe0.
Context {R : numDomainType} {nz : nullity}.
Local Notation nR := {num R & ?=0 & >=0}.
Implicit Type x y : nR.
Local Notation num := (@num _ _ (0 : R) ?=0 >=0).

Lemma num_abs_le a x : 0 <= a -> (`|a|%:nng <= x) = (a <= x%:num).
Proof. by move=> a0; rewrite -num_le//= ger0_norm. Qed.

Lemma num_abs_lt a x : 0 <= a -> (`|a|%:nng < x) = (a < x%:num).
Proof. by move=> a0; rewrite -num_lt/= ger0_norm. Qed.
End MorphGe0.

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

(** These proofs help integrate more arithmetic with signed.v. The issue is
    Terms like `0 < 1-q` with subtraction don't work well. So we hide the
    subtractions behind `PosNum` and `NngNum` constructors, see sequences.v
    for examples. *)
Section onem_signed.
Variable R : numDomainType.
Implicit Types r : R.

Lemma onem_PosNum r (r1 : r < 1) : `1-r = (PosNum (onem_gt0 r1))%:num.
Proof. by []. Qed.

Lemma onemX_NngNum r (r1 : r <= 1) (r0 : 0 <= r) n :
  `1-(r ^+ n) = (NngNum (onemX_ge0 n r0 r1))%:num.
Proof. by []. Qed.

Lemma onem_nonneg_proof (p : {nonneg R}) : p%:num <= 1 -> 0 <= `1-(p%:num).
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (p : {nonneg R}) (p1 : p%:num <= 1) :=
  NngNum (onem_nonneg_proof p1).

End onem_signed.
