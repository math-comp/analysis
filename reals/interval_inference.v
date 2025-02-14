(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice order ssralg ssrnum ssrint.
From mathcomp Require Import interval.
From mathcomp Require Import mathcomp_extra boolp signed.

(**md**************************************************************************)
(* # Numbers within an interval                                               *)
(*                                                                            *)
(* This file develops tools to make the manipulation of numbers within        *)
(* a known interval easier, thanks to canonical structures. This adds types   *)
(* like {itv R & `[a, b]}, a notation e%:itv that infers an enclosing         *)
(* interval for expression e according to existing canonical instances and    *)
(* %:inum to cast back from type {itv R & i} to R.                            *)
(* For instance, x : {i01 R}, we have (1 - x%:inum)%:itv : {i01 R}            *)
(* automatically inferred.                                                    *)
(*                                                                            *)
(* ## types for values within known interval                                  *)
(* ```                                                                        *)
(*       {i01 R} == interface type for elements in R that live in `[0, 1];    *)
(*                  R must have a numDomainType structure.                    *)
(*                  Allows to solve automatically goals of the form x >= 0    *)
(*                  and x <= 1 if x is canonically a {i01 R}. {i01 R} is      *)
(*                  canonically stable by common operations.                  *)
(*   {itv R & i} == more generic type of values in interval i : interval int  *)
(*                  R must have a numDomainType structure. This type is shown *)
(*                  to be a porderType.                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## casts from/to values within known interval                              *)
(* ```                                                                        *)
(*        x%:itv == explicitly casts x to the most precise known {itv R & i}  *)
(*                  according to existing canonical instances.                *)
(*        x%:i01 == explicitly casts x to {i01 R} according to existing       *)
(*                  canonical instances.                                      *)
(*       x%:inum == explicit cast from {itv R & i} to R.                      *)
(* ```                                                                        *)
(*                                                                            *)
(* ## sign proofs                                                             *)
(* ```                                                                        *)
(*    [itv of x] == proof that x is in interval inferred by x%:itv            *)
(*     [lb of x] == proof that lb < x or lb <= x with lb the lower bound      *)
(*                  inferred by x%:itv                                        *)
(*     [ub of x] == proof that x < ub or x <= ub with ub the upper bound      *)
(*                  inferred by x%:itv                                        *)
(*    [lbe of x] == proof that lb <= x                                        *)
(*    [ube of x] == proof that x <= ub                                        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## constructors                                                            *)
(* ```                                                                        *)
(*    ItvNum xin == builds a {itv R & i} from a proof xin : x \in i           *)
(*                  where x : R                                               *)
(* ```                                                                        *)
(*                                                                            *)
(* A number of canonical instances are provided for common operations, if     *)
(* your favorite operator is missing, look below for examples on how to add   *)
(* the appropriate Canonical.                                                 *)
(* Canonical instances are also provided according to types, as a             *)
(* fallback when no known operator appears in the expression. Look to         *)
(* itv_top_typ below for an example on how to add your favorite type.         *)
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
HB.instance Definition _ := [isSub for @Itv.r R i].
HB.instance Definition _ := [Choice of nR by <:].
HB.instance Definition _ := [SubChoice_isSubPOrder of nR by <:
  with ring_display].
End POrder.
(* TODO: numDomainType on sT ? *)

Module TypInstances.

Lemma itv_top_typ_spec (R : numDomainType) (x : R) : Itv.spec `]-oo, +oo[ x.
Proof. by []. Qed.

Canonical itv_top_typ (R : numDomainType) := Itv.Typ (@itv_top_typ_spec R).

Lemma typ_inum_spec (xt : Itv.typ) (x : Itv.sort xt) :
  Itv.spec (Itv.sort_itv xt) x.
Proof. by move: xt x => []. Qed.

(* This adds _ <- Itv.r ( typ_inum )
   to canonical projections (c.f., Print Canonical Projections
   Itv.r) meaning that if no other canonical instance (with a
   registered head symbol) is found, a canonical instance of
   Itv.typ, like the ones above, will be looked for. *)
Canonical typ_inum (xt : Itv.typ) (x : Itv.sort xt) := Itv.mk (typ_inum_spec x).

End TypInstances.
Export (canonicals) TypInstances.

Notation unify_itv ix iy := (unify wider_itv ix iy).

Section Theory.
Context {R : numDomainType} {i : interval int}.
Local Notation sT := {itv R & i}.
Implicit Type x : sT.

Lemma itv_intro {x} : x%:inum = x%:inum :> R. Proof. by []. Qed.

Definition empty_itv := `[Posz 1, Posz 0].

Lemma itv_bottom x : unify_itv empty_itv i -> False.
Proof.
move: x => [x /subitvP /(_ x)]; rewrite in_itv/= lexx => /(_ erefl) xi.
move=> /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /andP[] /le_trans /[apply]; rewrite ler10.
Qed.

Lemma itv_gt0 x : unify_itv `]Posz 0, +oo[ i -> 0%R < x%:inum :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT.
Qed.

Lemma itv_le0F x : unify_itv `]Posz 0, +oo[ i -> x%:inum <= 0%R :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT => /lt_geF.
Qed.

Lemma itv_lt0 x : unify_itv `]-oo, Posz 0[ i -> x%:inum < 0%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv.
Qed.

Lemma itv_ge0F x : unify_itv `]-oo, Posz 0[ i -> 0%R <= x%:inum :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma itv_ge0 x : unify_itv `[Posz 0, +oo[ i -> 0%R <= x%:inum :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT.
Qed.

Lemma itv_lt0F x : unify_itv `[Posz 0, +oo[ i -> x%:inum < 0%R :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= andbT => /le_gtF.
Qed.

Lemma itv_le0 x : unify_itv `]-oo, Posz 0] i -> x%:inum <= 0%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/=.
Qed.

Lemma itv_gt0F x : unify_itv `]-oo, Posz 0] i -> 0%R < x%:inum :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /le_gtF.
Qed.

Lemma lt1 x : unify_itv `]-oo, Posz 1[ i -> x%:inum < 1%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv.
Qed.

Lemma ge1F x : unify_itv `]-oo, Posz 1[ i -> 1%R <= x%:inum :> R = false.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/= => /lt_geF.
Qed.

Lemma le1 x : unify_itv `]-oo, Posz 1] i -> x%:inum <= 1%R :> R.
Proof.
move: x => [x /= xi] /(@Itv.subitv_map_itv R) /subitvP /(_ _ xi).
by rewrite in_itv/=.
Qed.

Lemma gt1F x : unify_itv `]-oo, Posz 1] i -> 1%R < x%:inum :> R = false.
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

Arguments itv_bottom {R i} _ {_}.
Arguments itv_gt0 {R i} _ {_}.
Arguments itv_le0F {R i} _ {_}.
Arguments itv_lt0 {R i} _ {_}.
Arguments itv_ge0F {R i} _ {_}.
Arguments itv_ge0 {R i} _ {_}.
Arguments itv_lt0F {R i} _ {_}.
Arguments itv_le0 {R i} _ {_}.
Arguments itv_gt0F {R i} _ {_}.
Arguments lt1 {R i} _ {_}.
Arguments ge1F {R i} _ {_}.
Arguments le1 {R i} _ {_}.
Arguments gt1F {R i} _ {_}.
Arguments widen_itv {R i} _ {_ _}.
Arguments widen_itvE {R i} _ {_}.

#[global] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: itv_gt0] : core.
#[global] Hint Extern 0 (is_true (_ < 0%R)%O) => solve [apply: itv_lt0] : core.
#[global] Hint Extern 0 (is_true (0%R <= _)%O) => solve [apply: itv_ge0] : core.
#[global] Hint Extern 0 (is_true (_ <= 0%R)%O) => solve [apply: itv_le0] : core.
#[global] Hint Extern 0 (is_true (_ < 1%R)%O) => solve [apply: lt1] : core.
#[global] Hint Extern 0 (is_true (_ <= 1%R)%O) => solve [apply: le1] : core.

Notation "x %:i01" := (widen_itv x%:itv : {i01 _}) (only parsing) : ring_scope.
Notation "x %:i01" := (@widen_itv _ _
    (@Itv.from _ _ _ (Phantom _ x)) `[Posz 0, Posz 1] _)
  (only printing) : ring_scope.

Local Open Scope ring_scope.

Module Instances.

Section NumDomainStability.
Context {R : numDomainType}.

Lemma zero_spec : Itv.spec `[0, 0] (0 : R).
Proof. by rewrite /Itv.itv_cond/= inE. Qed.

Canonical zero_inum := Itv.mk zero_spec.

Lemma one_spec : Itv.spec `[1, 1] (1 : R).
Proof. by rewrite /Itv.itv_cond/= inE. Qed.

Canonical one_inum := Itv.mk one_spec.

Definition opp_itv_bound (b : itv_bound int) : itv_bound int :=
  match b with
  | BSide b x => BSide (~~ b) (intZmod.oppz x)
  | BInfty b => BInfty _ (~~ b)
  end.
Arguments opp_itv_bound /.

Lemma opp_itv_ge0 b : (BLeft 0%R <= opp_itv_bound b)%O = (b <= BRight 0%R)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_ge0. Qed.

Lemma opp_itv_gt0 b : (BLeft 0%R < opp_itv_bound b)%O = (b < BRight 0%R)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_ge0 // oppr_gt0.
Qed.

Lemma opp_itv_boundr (x : R) b :
  (BRight (- x)%R <= Itv.map_itv_bound intr (opp_itv_bound b))%O
  = (Itv.map_itv_bound intr b <= BLeft x)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Lemma opp_itv_le0 b : (opp_itv_bound b <= BRight 0%R)%O = (BLeft 0%R <= b)%O.
Proof. by case: b => [[] b | []//]; rewrite /= !bnd_simp oppr_le0. Qed.

Lemma opp_itv_lt0 b : (opp_itv_bound b < BRight 0%R)%O = (BLeft 0%R < b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp ?oppr_le0 // oppr_lt0.
Qed.

Lemma opp_itv_boundl (x : R) b :
  (Itv.map_itv_bound intr (opp_itv_bound b) <= BLeft (- x)%R)%O
  = (BRight x <= Itv.map_itv_bound intr b)%O.
Proof.
by case: b => [[] b | []//]; rewrite /= !bnd_simp mulrNz ?lerN2 // ltrN2.
Qed.

Definition opp_itv (i : interval int) : interval int :=
  let 'Interval l u := i in Interval (opp_itv_bound u) (opp_itv_bound l).
Arguments opp_itv /.

Lemma opp_spec (i : interval int) (x : {itv R & i}) (r := opp_itv i) :
  Itv.spec r (- x%:inum).
Proof.
rewrite {}/r; move: i x => [l u] [x /= /andP[xl xu]]; apply/andP; split.
- by case: u xu => [[] b i | [] //] /=; rewrite /Order.le/= mulrNz;
    do ?[by rewrite lerNl opprK|by rewrite ltrNl opprK].
- by case: l xl => [[] b i | [] //] /=; rewrite /Order.le/= mulrNz;
    do ?[by rewrite ltrNl opprK|by rewrite lerNl opprK].
Qed.

Canonical opp_inum (i : interval int) (x : {itv R & i}) := Itv.mk (opp_spec x).

Definition add_itv_boundl (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ true
  end.
Arguments add_itv_boundl /.

Definition add_itv_boundr (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intZmod.addz x1 x2)
  | _, _ => BInfty _ false
  end.
Arguments add_itv_boundr /.

Definition add_itv (i1 i2 : interval int) : interval int :=
  let 'Interval l1 u1 := i1 in
  let 'Interval l2 u2 := i2 in
  Interval (add_itv_boundl l1 l2) (add_itv_boundr u1 u2).
Arguments add_itv /.

Lemma add_spec (xi yi : interval int) (x : {itv R & xi}) (y : {itv R & yi})
    (r := add_itv xi yi) :
  Itv.spec r (x%:inum + y%:inum).
Proof.
rewrite {}/r.
move: xi x yi y => [lx ux] [x /= /andP[xl xu]] [ly uy] [y /= /andP[yl yu]].
rewrite /Itv.itv_cond in_itv; apply/andP; split.
- move: lx ly xl yl => [xb lx | //] [yb ly | //].
  by move: xb yb => [] []; rewrite /Order.le/= rmorphD/=;
    do ?[exact: lerD|exact: ler_ltD|exact: ltr_leD|exact: ltrD].
- move: ux uy xu yu => [xb ux | //] [yb uy | //].
  by move: xb yb => [] []; rewrite /Order.le/= rmorphD/=;
    do ?[exact: lerD|exact: ler_ltD|exact: ltr_leD|exact: ltrD].
Qed.

Canonical add_inum (xi yi : interval int) (x : {itv R & xi}) (y : {itv R & yi})
  := Itv.mk (add_spec x y).

End NumDomainStability.

Section RealDomainStability.
Context {R : realDomainType}.

Definition itv_bound_signl (b : itv_bound int) : KnownSign.sign :=
  let b0 := BLeft 0%Z in
  (if b == b0 then =0 else if (b <= b0)%O then <=0 else >=0)%snum_sign.

Definition itv_bound_signr (b : itv_bound int) : KnownSign.sign :=
  let b0 := BRight 0%Z in
  (if b == b0 then =0 else if (b <= b0)%O then <=0 else >=0)%snum_sign.

Definition interval_sign (i : interval int) : option KnownSign.real :=
  let 'Interval l u := i in
  (match itv_bound_signl l, itv_bound_signr u with
   | =0, <=0
   | >=0, =0
   | >=0, <=0 => None
   | =0, =0 => Some (KnownSign.Sign =0)
   | <=0, =0
   | <=0, <=0 => Some (KnownSign.Sign <=0)
   | =0, >=0
   | >=0, >=0 => Some (KnownSign.Sign >=0)
   | <=0, >=0 => Some >=<0
   end)%snum_sign.

Variant interval_sign_spec (l u : itv_bound int) : option KnownSign.real -> Set :=
  | ISignNone : (u <= l)%O -> interval_sign_spec l u None
  | ISignEqZero : l = BLeft 0 -> u = BRight 0 ->
                  interval_sign_spec l u (Some (KnownSign.Sign =0))
  | ISignNeg : (l < BLeft 0%:Z)%O -> (u <= BRight 0%:Z)%O ->
               interval_sign_spec l u (Some (KnownSign.Sign <=0))
  | ISignPos : (BLeft 0%:Z <= l)%O -> (BRight 0%:Z < u)%O ->
               interval_sign_spec l u (Some (KnownSign.Sign >=0))
  | ISignBoth : (l < BLeft 0%:Z)%O -> (BRight 0%:Z < u)%O ->
                interval_sign_spec l u (Some >=<0%snum_sign).

Lemma interval_signP l u :
  interval_sign_spec l u (interval_sign (Interval l u)).
Proof.
rewrite /interval_sign/itv_bound_signl/itv_bound_signr.
have [lneg|lpos|->] := ltgtP l; have [uneg|upos|->] := ltgtP u.
- apply: ISignNeg => //; exact: ltW.
- exact: ISignBoth.
- exact: ISignNeg.
- by apply/ISignNone/ltW/(lt_le_trans uneg); rewrite leBRight_ltBLeft.
- by apply: ISignPos => //; exact: ltW.
- by apply: ISignNone; rewrite leBRight_ltBLeft.
- by apply: ISignNone; rewrite -ltBRight_leBLeft.
- exact: ISignPos.
- exact: ISignEqZero.
Qed.

Definition mul_itv_boundl (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide true 0%Z, BSide _ _
  | BSide _ _, BSide true 0%Z => BSide true 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 && b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => BInfty _ false
  end.
Arguments mul_itv_boundl /.

Definition mul_itv_boundr (b1 b2 : itv_bound int) : itv_bound int :=
  match b1, b2 with
  | BSide true 0%Z, _
  | _, BSide true 0%Z => BSide true 0%Z
  | BSide false 0%Z, _
  | _, BSide false 0%Z => BSide false 0%Z
  | BSide b1 x1, BSide b2 x2 => BSide (b1 || b2) (intRing.mulz x1 x2)
  | _, BInfty _
  | BInfty _, _ => BInfty _ false
  end.
Arguments mul_itv_boundr /.

Lemma mul_itv_boundl_spec b1 b2 (x1 x2 : R) :
  (BLeft 0%:Z <= b1 -> BLeft 0%:Z <= b2 ->
   Itv.map_itv_bound intr b1 <= BLeft x1 ->
   Itv.map_itv_bound intr b2 <= BLeft x2 ->
   Itv.map_itv_bound intr (mul_itv_boundl b1 b2) <= BLeft (x1 * x2))%O.
Proof.
move: b1 b2 => [[] b1 | []//] [[] b2 | []//] /=; rewrite 4!bnd_simp.
- set bl := match b1 with 0%Z => _ | _ => _ end.
  have -> : bl = BLeft (b1 * b2).
    rewrite {}/bl; move: b1 b2 => [[|p1]|p1] [[|p2]|p2]; congr BLeft.
    by rewrite mulr0.
  rewrite -2!(ler0z R) bnd_simp intrM; exact: ler_pM.
- case: b1 => [[|p1]|//]; rewrite -2!(ler0z R) !bnd_simp ?intrM.
    by move=> _ geb2 ? ?; apply: mulr_ge0 => //; apply/(le_trans geb2)/ltW.
  move=> p1gt0 b2ge0 lep1x1 ltb2x2.
  have: (Posz p1.+1)%:~R * x2 <= x1 * x2.
    by rewrite ler_pM2r //; apply: le_lt_trans ltb2x2.
  by apply: lt_le_trans; rewrite ltr_pM2l // ltr0z.
- case: b2 => [[|p2]|//]; rewrite -2!(ler0z R) !bnd_simp ?intrM.
    by move=> geb1 _ ? ?; apply: mulr_ge0 => //; apply/(le_trans geb1)/ltW.
  move=> b1ge0 p2gt0 ltb1x1 lep2x2.
  have: b1%:~R * x2 < x1 * x2; last exact/le_lt_trans/ler_pM.
  by rewrite ltr_pM2r //; apply: lt_le_trans lep2x2; rewrite ltr0z.
- rewrite -2!(ler0z R) bnd_simp intrM; exact: ltr_pM.
Qed.

Lemma mul_itv_boundrC b1 b2 :
  mul_itv_boundr b1 b2 = mul_itv_boundr b2 b1.
Proof.
by move: b1 b2 => [[] [[|?]|?] | []] [[] [[|?]|?] | []] //=; rewrite mulnC.
Qed.

Lemma mul_itv_boundr_spec b1 b2 (x1 x2 : R) :
  (BLeft 0%R <= BLeft x1 -> BLeft 0%R <= BLeft x2 ->
   BRight x1 <= Itv.map_itv_bound intr b1 ->
   BRight x2 <= Itv.map_itv_bound intr b2 ->
   BRight (x1 * x2) <= Itv.map_itv_bound intr (mul_itv_boundr b1 b2))%O.
Proof.
move: b1 b2 => [b1b b1 | []] [b2b b2 | []] //=; last first.
- move: b2 b2b => [[|p2]|p2] [] // _ + _ +; rewrite !bnd_simp => le1 le2.
  + by move: (le_lt_trans le1 le2); rewrite ltxx.
  + by move: (conj le1 le2) => /andP/le_anti <-; rewrite mulr0.
- move: b1 b1b => [[|p1]|p1] [] // + _ + _; rewrite !bnd_simp => le1 le2.
  + by move: (le_lt_trans le1 le2); rewrite ltxx.
  + by move: (conj le1 le2) => /andP/le_anti <-; rewrite mul0r.
case: b1 => [[|p1]|p1].
- case: b1b.
    by rewrite !bnd_simp => l _ l' _; move: (le_lt_trans l l'); rewrite ltxx.
  by move: b2b b2 => [] [[|p2]|p2]; rewrite !bnd_simp;
    first (by move=> _ l _ l'; move: (le_lt_trans l l'); rewrite ltxx);
    move=> l _ l' _; move: (conj l l') => /andP/le_anti <-; rewrite mul0r.
- rewrite if_same.
  case: b2 => [[|p2]|p2].
  + case: b2b => _ + _ +; rewrite !bnd_simp => l l'.
      by move: (le_lt_trans l l'); rewrite ltxx.
    by move: (conj l l') => /andP/le_anti <-; rewrite mulr0.
  + move: b1b b2b => [] []; rewrite !bnd_simp;
      rewrite -[intRing.mulz ?[a] ?[b]]/((Posz ?[a]) * ?[b])%R intrM.
    * exact: ltr_pM.
    * move=> x1ge0 x2ge0 ltx1p1 lex2p2.
      have: x1 * p2.+1%:~R < p1.+1%:~R * p2.+1%:~R.
        by rewrite ltr_pM2r // ltr0z.
      exact/le_lt_trans/ler_pM.
    * move=> x1ge0 x2ge0 lex1p1 ltx2p2.
      have: p1.+1%:~R * x2 < p1.+1%:~R * p2.+1%:~R.
        by rewrite ltr_pM2l // ltr0z.
      exact/le_lt_trans/ler_pM.
    * exact: ler_pM.
  + case: b2b => _ + _; rewrite 2!bnd_simp => l l'.
      by move: (le_lt_trans l l'); rewrite ltr0z.
    by move: (le_trans l l'); rewrite ler0z.
- case: b1b => + _ + _; rewrite 2!bnd_simp => l l'.
    by move: (le_lt_trans l l'); rewrite ltr0z.
  by move: (le_trans l l'); rewrite ler0z.
Qed.

Lemma mul_itv_boundr'_spec b1 b2 (x1 x2 : R) :
  (BLeft 0%:R <= BLeft x1 -> BRight 0%:Z <= b2 ->
   BRight x1 <= Itv.map_itv_bound intr b1 ->
   BRight x2 <= Itv.map_itv_bound intr b2 ->
   BRight (x1 * x2) <= Itv.map_itv_bound intr (mul_itv_boundr b1 b2))%O.
Proof.
move=> x1ge0 b2ge0 lex1b1 lex2b2.
have [x2ge0 | x2lt0] := leP 0 x2; first exact: mul_itv_boundr_spec.
have lem0 : (BRight (x1 * x2) <= BRight 0%R)%O.
  by rewrite bnd_simp mulr_ge0_le0 // ltW.
apply: le_trans lem0 _.
move: b1 b2 lex1b1 lex2b2 b2ge0 => [b1b b1 | []] [b2b b2 | []] //=; last first.
- by move: b2 b2b => [[|?]|?] [].
- move: b1 b1b => [[|p1]|p1] [] //.
  by rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0); rewrite ltxx.
case: b1 => [[|p1]|p1].
- case: b1b; last by move: b2b b2 => [] [[|]|].
  by rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0); rewrite ltxx.
- rewrite if_same.
  case: b2 => [[|p2]|p2]; first (by case: b2b); last by case: b2b.
  by rewrite if_same => _ _ _ /=; rewrite leBSide ltrW_lteif // ltr0z.
- rewrite leBRight_ltBLeft => /(le_lt_trans x1ge0).
  by case: b1b; rewrite bnd_simp ?ltr0z // ler0z.
Qed.

Definition mul_itv (i1 i2 : interval int) : interval int :=
  let 'Interval l1 u1 := i1 in
  let 'Interval l2 u2 := i2 in
  let opp := opp_itv_bound in
  let mull := mul_itv_boundl in
  let mulr := mul_itv_boundr in
  match interval_sign i1, interval_sign i2 with
  | None, _ | _, None => `[1, 0]
  | some s1, Some s2 =>
    (match s1, s2 with
     | =0, _ => `[0, 0]
     | _, =0 => `[0, 0]
     | >=0, >=0 => Interval (mull l1 l2) (mulr u1 u2)
     | <=0, <=0 => Interval (mull (opp u1) (opp u2)) (mulr (opp l1) (opp l2))
     | >=0, <=0 => Interval (opp (mulr u1 (opp l2))) (opp (mull l1 (opp u2)))
     | <=0, >=0 => Interval (opp (mulr (opp l1) u2)) (opp (mull (opp u1) l2))
     | >=0, >=<0 => Interval (opp (mulr u1 (opp l2))) (mulr u1 u2)
     | <=0, >=<0 => Interval (opp (mulr (opp l1) u2)) (mulr (opp l1) (opp l2))
     | >=<0, >=0 => Interval (opp (mulr (opp l1) u2)) (mulr u1 u2)
     | >=<0, <=0 => Interval (opp (mulr u1 (opp l2))) (mulr (opp l1) (opp l2))
     | >=<0, >=<0 => Interval
                       (Order.min (opp (mulr (opp l1) u2))
                          (opp (mulr u1 (opp l2))))
                       (Order.max (mulr (opp l1) (opp l2))
                          (mulr u1 u2))
     end)%snum_sign
  end.
Arguments mul_itv /.

Lemma map_itv_bound_min (x y : itv_bound int) :
  Itv.map_itv_bound (fun x => x%:~R : R) (Order.min x y)
  = Order.min (Itv.map_itv_bound intr x) (Itv.map_itv_bound intr y).
Proof.
have [lexy|ltyx] := leP x y; first by rewrite !minEle Itv.le_map_itv_bound.
by rewrite minElt -if_neg -leNgt Itv.le_map_itv_bound // ltW.
Qed.

Lemma map_itv_bound_max (x y : itv_bound int) :
  Itv.map_itv_bound (fun x => x%:~R : R) (Order.max x y)
  = Order.max (Itv.map_itv_bound intr x) (Itv.map_itv_bound intr y).
Proof.
have [lexy|ltyx] := leP x y; first by rewrite !maxEle Itv.le_map_itv_bound.
by rewrite maxElt -if_neg -leNgt Itv.le_map_itv_bound // ltW.
Qed.

Lemma mul_spec (xi yi : interval int) (x : {itv R & xi}) (y : {itv R & yi})
    (r := mul_itv xi yi) :
  Itv.spec r (x%:inum * y%:inum).
Proof.
rewrite {}/r.
move: xi x yi y => [lx ux] [x /= /andP[+ +]] [ly uy] [y /= /andP[+ +]].
rewrite -/(interval_sign (Interval lx ux)).
rewrite -/(interval_sign (Interval ly uy)).
have empty10 (z : R) l u : (u <= l)%O ->
    (Itv.map_itv_bound [eta intr] l <= BLeft z)%O ->
    (BRight z <= Itv.map_itv_bound [eta intr] u)%O -> False.
  move=> leul; rewrite leBRight_ltBLeft => /le_lt_trans /[apply].
  rewrite lt_def => /andP[/[swap]] => + /ltac:(apply/negP).
  rewrite negbK; move: leul => /(Itv.le_map_itv_bound R) le1 le2.
  by apply/eqP/le_anti; rewrite le1.
pose opp := opp_itv_bound.
pose mull := mul_itv_boundl.
pose mulr := mul_itv_boundr.
have [leuxlx|-> ->|lxneg uxneg|lxpos uxpos|lxneg uxpos] := interval_signP.
- move=> + + /ltac:(exfalso); exact: empty10.
- rewrite 2!bnd_simp => lex1 lex2 ley1 ley2.
  have -> : x = 0 by apply: le_anti; rewrite lex1 lex2.
  rewrite mul0r.
  case: interval_signP; [|by move=> _ _; rewrite /Itv.itv_cond in_itv/= lexx..].
  by move=> leul; exfalso; move: ley1 ley2; apply: empty10.
- move=> lelxx lexux.
  have xneg : x <= 0.
    move: (le_trans lexux (Itv.le_map_itv_bound R uxneg)).
    by rewrite /= bnd_simp.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.itv_cond in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (mull (opp ux) (opp uy))
                               (mulr (opp lx) (opp ly))).
    rewrite -mulrNN /Itv.itv_cond itv_boundlr.
    rewrite mul_itv_boundl_spec ?mul_itv_boundr_spec //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr.
    * by rewrite opp_itv_boundr.
    * by rewrite opp_itv_ge0.
    * by rewrite opp_itv_ge0.
    * by rewrite opp_itv_boundl.
    * by rewrite opp_itv_boundl.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy))
                               (opp (mull (opp ux) ly))).
    rewrite -[x * y]opprK -mulNr /Itv.itv_cond itv_boundlr.
    rewrite opp_itv_boundl opp_itv_boundr.
    rewrite mul_itv_boundl_spec ?mul_itv_boundr_spec //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr.
    * by rewrite opp_itv_ge0.
    * by rewrite opp_itv_boundl.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy))
                               (mulr (opp lx) (opp ly))).
    rewrite -[x * y]opprK -mulNr /Itv.itv_cond itv_boundlr.
    rewrite opp_itv_boundl -mulrN.
    rewrite 2?mul_itv_boundr'_spec //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr.
    * by rewrite opp_itv_boundr.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite ltW.
    * by rewrite opp_itv_boundr.
- move=> lelxx lexux.
  have xpos : 0 <= x.
    move: (le_trans (Itv.le_map_itv_bound R lxpos) lelxx).
    by rewrite /= bnd_simp.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.itv_cond in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly)))
                               (opp (mull lx (opp uy)))).
    rewrite -[x * y]opprK -mulrN /Itv.itv_cond itv_boundlr.
    rewrite opp_itv_boundl opp_itv_boundr.
    rewrite mul_itv_boundr_spec ?mul_itv_boundl_spec //.
    * by rewrite opp_itv_ge0.
    * by rewrite opp_itv_boundl.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite opp_itv_boundr.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
      rewrite -[Interval _ _]/(Interval (mull lx ly) (mulr ux uy)).
    rewrite /Itv.itv_cond itv_boundlr.
    by rewrite mul_itv_boundr_spec ?mul_itv_boundl_spec.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly))) (mulr ux uy)).
    rewrite -[x * y]opprK -mulrN /Itv.itv_cond itv_boundlr.
    rewrite opp_itv_boundl -mulrN opprK.
    rewrite 2?mul_itv_boundr'_spec //.
    * by rewrite ltW.
    * by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr.
- move=> lelxx lexux.
  have [leuyly|-> ->|lyneg uyneg|lypos uypos|lyneg uypos] := interval_signP.
  + move=> + + /ltac:(exfalso); exact: empty10.
  + rewrite 2!bnd_simp => ley1 ley2.
    have -> : y = 0 by apply: le_anti; rewrite ley1 ley2.
    by rewrite mulr0 /Itv.itv_cond in_itv/= lexx.
  + move=> lelyy leyuy.
    have yneg : y <= 0.
      move: (le_trans leyuy (Itv.le_map_itv_bound R uyneg)).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr ux (opp ly)))
                               (mulr (opp lx) (opp ly))).
    rewrite -[x * y]opprK -mulrN /Itv.itv_cond itv_boundlr.
    rewrite /mulr mul_itv_boundrC mulrC opp_itv_boundl.
    rewrite [in X in _ && X]mul_itv_boundrC -mulrN.
    rewrite mul_itv_boundr'_spec ?mul_itv_boundr'_spec //.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr.
    * by rewrite opp_itv_boundr.
    * by rewrite bnd_simp oppr_ge0.
    * by rewrite ltW.
    * by rewrite opp_itv_boundr.
  + move=> lelyy leyuy.
    have ypos : 0 <= y.
      move: (le_trans (Itv.le_map_itv_bound R lypos) lelyy).
      by rewrite /= bnd_simp.
    rewrite -[Interval _ _]/(Interval (opp (mulr (opp lx) uy)) (mulr ux uy)).
    rewrite -[x * y]opprK -mulNr /Itv.itv_cond itv_boundlr.
    rewrite /mulr mul_itv_boundrC mulrC opp_itv_boundl.
    rewrite [in X in _ && X]mul_itv_boundrC -mulrN opprK.
    rewrite mul_itv_boundr'_spec ?mul_itv_boundr'_spec //.
    * by rewrite ltW.
    * by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
    * by rewrite opp_itv_boundr.
  + move=> lelyy leyuy.
    rewrite -[Interval _ _]/(Interval
                               (Order.min (opp (mulr (opp lx) uy))
                                  (opp (mulr ux (opp ly))))
                               (Order.max (mulr (opp lx) (opp ly))
                                  (mulr ux uy))).
    rewrite /Itv.itv_cond itv_boundlr.
    rewrite map_itv_bound_min map_itv_bound_max ge_min le_max.
    rewrite -[x * y]opprK !opp_itv_boundl.
    rewrite -[in X in ((X || _) && _)]mulNr -[in X in ((_ || X) && _)]mulrN.
    rewrite -[in X in (_ && (X || _))]mulrNN !opprK.
    have [xpos|xneg] := leP 0 x.
    * rewrite [in X in ((_ || X) && _)]mul_itv_boundr'_spec ?orbT //=;
        rewrite ?[in X in (_ || X)]mul_itv_boundr'_spec ?orbT //.
      - by rewrite ltW.
      - by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
      - by rewrite opp_itv_boundr.
    * rewrite [in X in ((X || _) && _)]mul_itv_boundr'_spec //=;
        rewrite ?[in X in (X || _)]mul_itv_boundr'_spec //.
      - by rewrite bnd_simp oppr_ge0 ltW.
      - by rewrite leBRight_ltBLeft opp_itv_gt0 ltBRight_leBLeft ltW.
      - by rewrite opp_itv_boundr.
      - by rewrite opp_itv_boundr.
      - by rewrite bnd_simp oppr_ge0 ltW.
      - by rewrite ltW.
      - by rewrite opp_itv_boundr.
Qed.

Canonical mul_inum (xi yi : interval int) (x : {itv R & xi}) (y : {itv R & yi})
  := Itv.mk (mul_spec x y).

End RealDomainStability.

End Instances.
Export (canonicals) Instances.

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
Proof.
Abort.

Goal (- x%:inum)%:itv = (- x%:inum)%:itv :> {itv R & `[-1, 0]}.
Proof.
Abort.

Goal (1 - x%:inum)%:i01 = x.
Proof.
Abort.

End Test1.

Section Test2.

Variable R : realDomainType.
Variable x y : {i01 R}.

Goal (x%:inum * y%:inum)%:i01 = x%:inum%:i01.
Proof.
Abort.

End Test2.

Module Test3.
Section Test3.
Variable R : realDomainType.

Definition s_of_pq (p q : {i01 R}) : {i01 R} :=
  (1 - ((1 - p%:inum)%:i01%:inum * (1 - q%:inum)%:i01%:inum))%:i01.

Lemma s_of_p0 (p : {i01 R}) : s_of_pq p 0%:i01 = p.
Proof. by apply/val_inj; rewrite /= subr0 mulr1 subKr. Qed.

Canonical onem_itv01 (p : {i01 R}) : {i01 R} :=
  @Itv.mk _ _ (onem p%:inum) [itv of 1 - p%:inum].

Definition s_of_pq' (p q : {i01 R}) : {i01 R} :=
  (`1- (`1-(p%:inum) * `1-(q%:inum)))%:i01.

End Test3.
End Test3.
