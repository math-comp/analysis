(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg ssrnum ssrint.
From mathcomp Require Import interval mathcomp_extra.
Require Import boolp.

(******************************************************************************)
(* This file develops tools to make the manipulation of numbers within        *)
(* a known interval easier, thanks to canonical structures. This adds types   *)
(* like {itv R & `[a, b]}, a notation e%:itv that infers an enclosing         *)
(* interval for expression e according to existing canonical instances and    *)
(* %:inum to cast back from type {itv R & i} to R.                            *)
(* For instance, x : {i01 R}, we have (1 - x%:inum)%:itv : {i01 R}            *)
(* automatically inferred.                                                    *)
(*                                                                            *)
(* * types for values within known interval                                   *)
(*       {i01 R} == interface type for elements in R that live in `[0, 1];    *)
(*                  R must have a numDomainType structure.                    *)
(*                  Allows to solve automatically goals of the form x >= 0 if *)
(*                  x is canonically a {i01 R}. {i01 R} is canonically        *)
(*                  stable by common operations.                              *)
(*   {itv R & i} == more generic type of values in interval i : interval int  *)
(*                  R must have a numDomainType structure. This type is shown *)
(*                  to be a porderType.                                       *)
(*                                                                            *)
(* * casts from/to values within known interval                               *)
(*        x%:itv == explicitly casts x to the most precise known {itv R & i}  *)
(*                  according to existing canonical instances.                *)
(*        x%:i01 == explicitly casts x to {i01 R} according to existing       *)
(*                  canonical instances.                                      *)
(*       x%:inum == explicit cast from {itv R & i} to R.                      *)
(*                                                                            *)
(* * sign proofs                                                              *)
(*    [itv of x] == proof that x is in interval inferred by x%:itv            *)
(*     [lb of x] == proof that lb < x or lb <= x with lb the lower bound      *)
(*                  inferred by x%:itv                                        *)
(*     [ub of x] == proof that x < ub or x <= ub with ub the upper bound      *)
(*                  inferred by x%:itv                                        *)
(*    [lbe of x] == proof that lb <= x                                        *)
(*    [ube of x] == proof that x <= ub                                        *)
(*                                                                            *)
(* * constructors                                                             *)
(*    ItvNum xin == builds a {itv R & i} from a proof xin : x \in i           *)
(*                  where x : R                                               *)
(*                                                                            *)
(* --> A number of canonical instances are provided for common operations, if *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(* --> Canonical instances are also provided according to types, as a         *)
(* fallback when no known operator appears in the expression. Look to         *)
(* top_typ below for an example on how to add your favorite type.             *)
(******************************************************************************)

Reserved Notation "{ 'itv' R & i }"
  (at level 0, R at level 200, i at level 200, format "{ 'itv'  R  &  i }").
Reserved Notation "{ 'i01' R }"
  (at level 0, R at level 200, format "{ 'i01'  R }").

Reserved Notation "x %:itv" (at level 2, format "x %:itv").
Reserved Notation "x %:i01" (at level 2, format "x %:i01").
Reserved Notation "x %:inum" (at level 2, format "x %:inum").
Reserved Notation "[ 'itv' 'of' x ]" (format "[ 'itv' 'of'  x ]").
Reserved Notation "[ 'lb' 'of' x ]" (format "[ 'lb' 'of'  x ]").
Reserved Notation "[ 'ub' 'of' x ]" (format "[ 'ub' 'of'  x ]").
Reserved Notation "[ 'lbe' 'of' x ]" (format "[ 'lbe' 'of'  x ]").
Reserved Notation "[ 'ube' 'of' x ]" (format "[ 'ube' 'of'  x ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Order.Syntax.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope order_scope.

(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
#[global] Hint Mode infer ! : typeclass_instances.
#[global] Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Definition wider_itv (x y : interval int) := subitv y x.

Module Itv.
Section Itv.
Context (R : numDomainType).

Definition map_itv_bound S T (f : S -> T) (b : itv_bound S) : itv_bound T :=
  match b with
  | BSide b x => BSide b (f x)
  | BInfty b => BInfty _ b
  end.

Definition map_itv S T (f : S -> T) (i : interval S) : interval T :=
  let 'Interval l u := i in Interval (map_itv_bound f l) (map_itv_bound f u).

Lemma le_map_itv_bound (x y : itv_bound int) :
  x <= y ->
  map_itv_bound (fun x => x%:~R : R) x <= map_itv_bound (fun x => x%:~R : R) y.
Proof.
move: x y => [xb x | []xb //=]; last by case: xb.
case=> [yb y /=|//].
by rewrite /Order.le/=; case: (_ ==> _) => /=; rewrite ?ler_int// ltr_int.
Qed.

Lemma subitv_map_itv (x y : interval int) :
  x <= y ->
  map_itv (fun x => x%:~R : R) x <= map_itv (fun x => x%:~R : R) y.
Proof.
move: x y => [lx ux] [ly uy] /andP[lel leu].
apply/andP; split; exact: le_map_itv_bound.
Qed.

Definition itv_cond (i : interval int) (x : R) :=
  x \in map_itv (fun x => x%:~R : R) i.

Record def (i : interval int) := Def {
  r :> R;
  #[canonical=no]
  P : itv_cond i r
}.

End Itv.

Notation spec i x := (itv_cond i%Z%R x).

Record typ := Typ {
  sort : numDomainType;
  #[canonical=no]
  sort_itv : interval int;
  #[canonical=no]
  allP : forall x : sort, spec sort_itv x
}.

Definition mk {R} i r P : @def R i :=
  @Def R i r P.

Definition from {R i}
  {x : @def R i} (phx : phantom R x) := x.

Definition fromP {R i}
  {x : @def R i} (phx : phantom R x) := P x.

Module Exports.
Notation "{ 'itv' R & i }" := (def R i%Z) : type_scope.
Notation "{ 'i01' R }" := (def R `[Posz 0, Posz 1]) : type_scope.
Notation "x %:itv" := (from (Phantom _ x)) : ring_scope.
Notation "[ 'itv' 'of' x ]" := (fromP (Phantom _ x)) : ring_scope.
Notation inum := r.
Notation "x %:inum" := (r x) : ring_scope.
Arguments r {R i}.
End Exports.
End Itv.
Export Itv.Exports.

Section POrder.
Variables (R : numDomainType) (i : interval int).
Local Notation nR := {itv R & i}.
Canonical itv_subType := [subType for @Itv.r R i].
Definition itv_eqMixin := [eqMixin of nR by <:].
Canonical itv_eqType := EqType nR itv_eqMixin.
Definition itv_choiceMixin := [choiceMixin of nR by <:].
Canonical itv_choiceType := ChoiceType nR itv_choiceMixin.
Definition itv_porderMixin := [porderMixin of nR by <:].
Canonical itv_porderType := POrderType ring_display nR itv_porderMixin.
End POrder.
(* TODO: numDomainType on sT ? *)

Lemma top_typ_subproof (R : numDomainType) (x : R) :
  Itv.spec `]-oo, +oo[ x.
Proof. by []. Qed.

Canonical top_typ (R : numDomainType) := Itv.Typ (@top_typ_subproof R).

Lemma typ_inum_subproof (xt : Itv.typ) (x : Itv.sort xt) :
  Itv.spec (Itv.sort_itv xt) x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (xt : Itv.typ) (x : Itv.sort xt) :=
  Itv.mk (typ_inum_subproof x).

Class unify {T} f (x y : T) := Unify : f x y = true.
#[global] Hint Mode unify - - - + : typeclass_instances.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[global] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y := id.
#[global]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_itv ix iy := (unify wider_itv ix iy).

Section Theory.
Context {R : numDomainType} {i : interval int}.
Local Notation sT := {itv R & i}.
Implicit Type x : sT.

Lemma itv_intro {x} : x%:inum = x%:inum :> R. Proof. by []. Qed.

Definition empty_itv := `[Posz 1, Posz 0].

Lemma bottom x : unify_itv empty_itv i -> False.
Proof.
move: x => [x /subitvP /(_ x)]; rewrite in_itv/= lexx => /(_ erefl) xi.
move=> /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma gt0 x : unify_itv `]Posz 0, +oo[ i -> 0%R < x%:inum :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT.
Qed.

Lemma le0F x : unify_itv `]Posz 0, +oo[ i -> x%:inum <= 0%R :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma lt0 x : unify_itv `]-oo, Posz 0[ i -> x%:inum < 0%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv.
Qed.

Lemma ge0F x : unify_itv `]-oo, Posz 0[ i -> 0%R <= x%:inum :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma ge0 x : unify_itv `[Posz 0, +oo[ i -> 0%R <= x%:inum :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT.
Qed.

Lemma lt0F x : unify_itv `[Posz 0, +oo[ i -> x%:inum < 0%R :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma le0 x : unify_itv `]-oo, Posz 0] i -> x%:inum <= 0%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/=.
Qed.

Lemma gt0F x : unify_itv `]-oo, Posz 0] i -> 0%R < x%:inum :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma widen_itv_subproof x i' : unify_itv i' i -> Itv.spec i' x%:inum.
Proof.
by move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
Qed.

Definition widen_itv x i' (uni : unify_itv i' i) :=
  Itv.mk (widen_itv_subproof x uni).

Lemma widen_itvE x (uni : unify_itv i i) : @widen_itv x i uni = x.
Proof. exact/val_inj. Qed.

End Theory.

Arguments bottom {R i} _ {_}.
Arguments gt0 {R i} _ {_}.
Arguments le0F {R i} _ {_}.
Arguments lt0 {R i} _ {_}.
Arguments ge0F {R i} _ {_}.
Arguments ge0 {R i} _ {_}.
Arguments lt0F {R i} _ {_}.
Arguments le0 {R i} _ {_}.
Arguments gt0F {R i} _ {_}.
Arguments widen_itv {R i} _ {_ _}.
Arguments widen_itvE {R i} _ {_}.

#[global] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: gt0] : core.
#[global] Hint Extern 0 (is_true (_ < 0%R)%O) => solve [apply: lt0] : core.
#[global] Hint Extern 0 (is_true (0%R <= _)%O) => solve [apply: ge0] : core.
#[global] Hint Extern 0 (is_true (_ <= 0%R)%O) => solve [apply: le0] : core.

Notation "x %:i01" := (widen_itv x%:itv : {i01 _}) (only parsing) : ring_scope.
Notation "x %:i01" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) `[Posz 0, Posz 1] _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Section NumDomainStability.
Context {R : numDomainType}.

Lemma zero_inum_subproof : Itv.spec `[0, 0] (0 : R).
Proof. by rewrite /Itv.itv_cond/= inE. Qed.

Canonical zero_inum := Itv.mk zero_inum_subproof.

Lemma one_inum_subproof : Itv.spec `[1, 1] (1 : R).
Proof. by rewrite /Itv.itv_cond/= inE. Qed.

Canonical one_inum := Itv.mk one_inum_subproof.

Definition opp_itv_bound_subdef (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.
Arguments opp_itv_bound_subdef /.

Definition opp_itv_subdef (i : interval int) : interval int :=
  let 'Interval l u := i in
  Interval (opp_itv_bound_subdef u) (opp_itv_bound_subdef l).
Arguments opp_itv_subdef /.

Lemma opp_inum_subproof (i : interval int)
    (x : {itv R & i}) (r := opp_itv_subdef i) :
  Itv.spec r (- x%:inum).
Proof.
rewrite {}/r; move: i x => [l u] [x /= /andP[xl xu]]; apply/andP; split.
- by case: u xu => [[] b i | [] //] /=; rewrite /Order.le/= mulrNz;
    do ?[by rewrite ler_oppl opprK|by rewrite ltr_oppl opprK].
- by case: l xl => [[] b i | [] //] /=; rewrite /Order.le/= mulrNz;
    do ?[by rewrite ltr_oppl opprK|by rewrite ler_oppl opprK].
Qed.

Canonical opp_inum (i : interval int) (x : {itv R & i}) :=
  Itv.mk (opp_inum_subproof x).

Definition add_itv_boundl_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.
Arguments add_itv_boundl_subdef /.

Definition add_itv_boundr_subdef (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.
Arguments add_itv_boundr_subdef /.

Definition add_itv_subdef (i1 i2 : interval int) : interval int :=
  let 'Interval l1 u1 := i1 in
  let 'Interval l2 u2 := i2 in
  Interval (add_itv_boundl_subdef l1 l2) (add_itv_boundr_subdef u1 u2).
Arguments add_itv_subdef /.

Lemma add_inum_subproof (xi yi : interval int)
    (x : {itv R & xi}) (y : {itv R & yi})
    (r := add_itv_subdef xi yi) :
  Itv.spec r (x%:inum + y%:inum).
Proof.
rewrite {}/r.
move: xi x yi y => [lx ux] [x /= /andP[xl xu]] [ly uy] [y /= /andP[yl yu]].
rewrite /Itv.itv_cond in_itv; apply/andP; split.
- move: lx ly xl yl => [xb lx | //] [yb ly | //].
  by move: xb yb => [] []; rewrite /Order.le/= rmorphD/=;
    do ?[exact: ler_add|exact: ler_lt_add|exact: ltr_le_add|exact: ltr_add].
- move: ux uy xu yu => [xb ux | //] [yb uy | //].
  by move: xb yb => [] []; rewrite /Order.le/= rmorphD/=;
    do ?[exact: ler_add|exact: ler_lt_add|exact: ltr_le_add|exact: ltr_add].
Qed.

Canonical add_inum (xi yi : interval int)
    (x : {itv R & xi}) (y : {itv R & yi}) :=
  Itv.mk (add_inum_subproof x y).

End NumDomainStability.

Section Morph.
Context {R : numDomainType} {i : interval int}.
Local Notation nR := {itv R & i}.
Implicit Types x y : nR.
Local Notation inum := (@inum R i).

Lemma inum_eq : {mono inum : x y / x == y}. Proof. by []. Qed.
Lemma inum_le : {mono inum : x y / (x <= y)%O}. Proof. by []. Qed.
Lemma inum_lt : {mono inum : x y / (x < y)%O}. Proof. by []. Qed.

End Morph.

Section Test1.

Variable R : numDomainType.
Variable x : {i01 R}.

Goal 0%:i01 = 1%:i01 :> {i01 R}.
Abort.

Goal (- x%:inum)%:itv = (- x%:inum)%:itv :> {itv R & `[-1, 0]}.
Abort.

Goal (1 - x%:inum)%:i01 = x.
Abort.

End Test1.
