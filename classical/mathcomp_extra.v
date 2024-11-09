(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import BinPos.
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import finset interval.

(**md**************************************************************************)
(* # MathComp extra                                                           *)
(*                                                                            *)
(* This files contains lemmas and definitions missing from MathComp.          *)
(*                                                                            *)
(* ```                                                                        *)
(*               proj i f == f i, where f : forall i, T i                     *)
(*             dfwith f x == fun j => x if j = i, and f j otherwise           *)
(*                           given x : T i                                    *)
(*                 swap x := (x.2, x.1)                                       *)
(*           map_pair f x := (f x.1, f x.2)                                   *)
(*         monotonous A f := {in A &, {mono f : x y / x <= y}} \/             *)
(*                           {in A &, {mono f : x y /~ x <= y}}               *)
(*             sigT_fun f := lifts a family of functions f into a function on *)
(*                           the dependent sum                                *)
(*                prodA x := sends (X * Y) * Z to X * (Y * Z)                 *)
(*               prodAr x := sends X * (Y * Z) to (X * Y) * Z                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(**************************)
(* MathComp 2.2 additions *)
(**************************)

Notation "f \min g" := (Order.min_fun f g) : function_scope.
Notation "f \max g" := (Order.max_fun f g) : function_scope.

Lemma ler_sqrt {R : rcfType} (a b : R) :
  (0 <= b -> (Num.sqrt a <= Num.sqrt b) = (a <= b))%R.
Proof.
have [b_gt0 _|//|<- _] := ltgtP; last first.
  by rewrite sqrtr0 -[RHS]sqrtr_eq0 le_eqVlt ltNge sqrtr_ge0 orbF.
have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt// ?qualifE/= ?ltW.
by rewrite ler0_sqrtr // sqrtr_ge0 (le_trans a_le0) ?ltW.
Qed.

(**************************)
(* MathComp 2.3 additions *)
(**************************)

(* Compatibility layer for Order.disp_t introduced in MathComp 2.3            *)
(* TODO: remove when we drop the support for MathComp 2.2                     *)
Module Order.
Import Order.
Definition disp_t : Set.
Proof. exact: disp_t || exact: unit. Defined.
Definition default_display : disp_t.
Proof. exact: tt || exact: Disp tt tt. Defined.
End Order.

Lemma invf_plt (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x^-1 < y)%R = (y^-1 < x)%R}.
Proof.
by move=> x y ? ?; rewrite -[in LHS](@invrK _ y) ltf_pV2// posrE invr_gt0.
Qed.

Lemma invf_ltp (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x < y^-1)%R = (y < x^-1)%R}.
Proof.
by move=> x y ? ?; rewrite -(invrK x) invf_plt ?posrE ?invr_gt0// !invrK.
Qed.

Lemma invf_ple (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x^-1 <= y)%R = (y^-1 <= x)%R}.
Proof.
by move=> x y ? ?; rewrite -[in LHS](@invrK _ y) lef_pV2// posrE invr_gt0.
Qed.

Lemma invf_lep (F : numFieldType) :
  {in Num.pos &, forall x y : F, (x <= y^-1)%R = (y <= x^-1)%R}.
Proof.
by move=> x y ? ?; rewrite -(invrK x) invf_ple ?posrE ?invr_gt0// !invrK.
Qed.

Definition proj {I} {T : I -> Type} i (f : forall i, T i) := f i.

Section DFunWith.
Variables (I : eqType) (T : I -> Type) (f : forall i, T i).

Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.

Lemma dfwithin i x : dfwith x i = x.
Proof. by rewrite /dfwith; case: eqP => // ii; rewrite eq_axiomK. Qed.

Lemma dfwithout i (x : T i) j : i != j -> dfwith x j = f j.
Proof. by rewrite /dfwith; case: eqP. Qed.

Variant dfwith_spec i (x : T i) : forall j, T j -> Type :=
  | DFunWithin : dfwith_spec x x
  | DFunWithout j : i != j -> dfwith_spec x (f j).

Lemma dfwithP i (x : T i) (j : I) : dfwith_spec x (dfwith x j).
Proof.
by case: (eqVneq i j) => [<-|nij];
   [rewrite dfwithin|rewrite dfwithout//]; constructor.
Qed.

Lemma projK i (x : T i) : cancel (@dfwith i) (proj i).
Proof. by move=> z; rewrite /proj dfwithin. Qed.

End DFunWith.
Arguments dfwith {I T} f i x.

(**********************)
(* not yet backported *)
(**********************)

Definition idempotent_fun (U : Type) (f : U -> U) := f \o f =1 f.

From mathcomp Require Import poly.

Lemma deg_le2_ge0 (F : rcfType) (a b c : F) :
  (forall x, 0 <= a * x ^+ 2 + b * x + c)%R -> (b ^+ 2 - 4%:R * a * c <= 0)%R.
Proof.
move=> pge0; pose p := \poly_(i < 3) [:: c; b; a]`_i.
have := @deg_le2_poly_ge0 _ p (size_poly _ _); rewrite !coef_poly/=; apply=> r.
rewrite horner_poly !big_ord_recr !big_ord0/= !Monoid.simpm/= expr1.
by rewrite -mulrA -expr2 addrC addrA addrAC.
Qed.

(* NB: Coq 8.17.0 generalizes dependent_choice from Set to Type
   making the following lemma redundant *)
Section dependent_choice_Type.
Context X (R : X -> X -> Prop).

Lemma dependent_choice_Type : (forall x, {y | R x y}) ->
  forall x0, {f | f 0%N = x0 /\ forall n, R (f n) (f n.+1)}.
Proof.
move=> h x0.
set (f := fix f n := if n is n'.+1 then proj1_sig (h (f n')) else x0).
exists f; split => //.
intro n; induction n; simpl; apply: proj2_sig.
Qed.
End dependent_choice_Type.

Section max_min.
Variable R : realFieldType.

Let nz2 : 2%:R != 0 :> R. Proof. by rewrite pnatr_eq0. Qed.

Lemma maxr_absE (x y : R) : Num.max x y = (x + y + `|x - y|) / 2%:R.
Proof.
apply: canRL (mulfK _) _ => //; rewrite ?pnatr_eq0//.
case: lerP => _; (* TODO: ring *) rewrite [2%:R]mulr2n mulrDr mulr1.
  by rewrite addrACA subrr addr0.
by rewrite addrCA addrAC subrr add0r.
Qed.

Lemma minr_absE (x y : R) : Num.min x y = (x + y - `|x - y|) / 2%:R.
Proof.
apply: (addrI (Num.max x y)); rewrite addr_max_min maxr_absE. (* TODO: ring *)
by rewrite -mulrDl addrACA subrr addr0 mulrDl -splitr.
Qed.

End max_min.

Notation trivial := (ltac:(done)).

Section bigmax_seq.
Context d {T : orderType d} {x : T} {I : eqType}.
Variables (r : seq I) (i0 : I) (P : pred I).

(* NB: as of [2023-08-28], bigop.leq_bigmax_seq already exists for nat *)
Lemma le_bigmax_seq F :
  i0 \in r -> P i0 -> (F i0 <= \big[Order.max/x]_(i <- r | P i) F i)%O.
Proof.
move=> + Pi0; elim: r => // h t ih; rewrite inE big_cons.
move=> /predU1P[<-|i0t]; first by rewrite Pi0 le_max// lexx.
by case: ifPn => Ph; [rewrite le_max ih// orbT|rewrite ih].
Qed.

(* NB: as of [2023-08-28], bigop.bigmax_sup_seq already exists for nat *)
Lemma bigmax_sup_seq (m : T) (F : I -> T) :
  i0 \in r -> P i0 -> (m <= F i0)%O ->
  (m <= \big[Order.max/x]_(i <- r | P i) F i)%O.
Proof. by move=> i0r Pi0 ?; apply: le_trans (le_bigmax_seq _ _ _). Qed.

End bigmax_seq.
Arguments le_bigmax_seq {d T} x {I r} i0 P.

Lemma leq_ltn_expn m : exists n, (2 ^ n <= m.+1 < 2 ^ n.+1)%N.
Proof.
elim: m => [|m [n /andP[h1 h2]]]; first by exists O.
have [m2n|nm2] := ltnP m.+2 (2 ^ n.+1)%N.
  by exists n; rewrite m2n andbT (leq_trans h1).
exists n.+1; rewrite nm2/= -addn1.
rewrite -[X in (_ <= X)%N]prednK ?expn_gt0// -[X in (_ <= X)%N]addn1 leq_add2r.
by rewrite (leq_trans h2)// -subn1 leq_subRL ?expn_gt0// add1n ltn_exp2l.
Qed.

Definition monotonous d (T : porderType d) (pT : predType T) (A : pT) (f : T -> T) :=
  {in A &, {mono f : x y / (x <= y)%O}} \/ {in A &, {mono f : x y /~ (x <= y)%O}}.

(* NB: these lemmas have been introduced to develop the theory of bounded variation *)
Section path_lt.
Context d {T : orderType d}.
Implicit Types (a b c : T) (s : seq T).

Lemma last_filterP a (P : pred T) s :
  P a -> P (last a [seq x <- s | P x]).
Proof.
by elim: s a => //= t1 t2 ih a Pa; case: ifPn => //= Pt1; exact: ih.
Qed.

Lemma path_lt_filter0 a s : path <%O a s -> [seq x <- s | (x < a)%O] = [::].
Proof.
move=> /lt_path_min/allP sa; rewrite -(filter_pred0 s).
apply: eq_in_filter => x xs.
by apply/negbTE; have := sa _ xs; rewrite ltNge; apply: contra => /ltW.
Qed.

Lemma path_lt_filterT a s : path <%O a s -> [seq x <- s | (a < x)%O] = s.
Proof.
move=> /lt_path_min/allP sa; rewrite -[RHS](filter_predT s).
by apply: eq_in_filter => x xs; exact: sa.
Qed.

Lemma path_lt_head a b s : (a < b)%O -> path <%O b s -> path <%O a s.
Proof.
by elim: s b => // h t ih b /= ab /andP[bh ->]; rewrite andbT (lt_trans ab).
Qed.

(* TODO: this lemma feels a bit too technical, generalize? *)
Lemma path_lt_last_filter a b c s :
  (a < c)%O -> (c < b)%O -> path <%O a s -> last a s = b ->
  last c [seq x <- s | (c < x)%O] = b.
Proof.
elim/last_ind : s a b c => /= [|h t ih a b c ac cb].
  move=> a b c ac cb _ ab.
  by apply/eqP; rewrite eq_le (ltW cb) -ab (ltW ac).
rewrite rcons_path => /andP[ah ht]; rewrite last_rcons => tb.
by rewrite filter_rcons tb cb last_rcons.
Qed.

Lemma path_lt_le_last a s : path <%O a s -> (a <= last a s)%O.
Proof.
elim: s a => // a [_ c /andP[/ltW//]|b t ih i/= /and3P[ia ab bt]] /=.
have /= := ih a; rewrite ab bt => /(_ erefl).
by apply: le_trans; exact/ltW.
Qed.

End path_lt.
Arguments last_filterP {d T a} P s.

Lemma sumr_le0 (R : numDomainType) I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> F i <= 0)%R -> (\sum_(i <- r | P i) F i <= 0)%R.
Proof. by move=> F0; elim/big_rec : _ => // i x Pi; apply/ler_wnDl/F0. Qed.

Inductive boxed T := Box of T.

Reserved Notation "`1- r" (format "`1- r", at level 2).
Reserved Notation "f \^-1" (at level 35, format "f \^-1").

(* TODO: To be backported to finmap *)

Lemma fset_nat_maximum (X : choiceType) (A : {fset X})
    (f : X -> nat) : A != fset0 ->
  (exists i, i \in A /\ forall j, j \in A -> f j <= f i)%nat.
Proof.
move=> /fset0Pn[x Ax].
have [/= y _ /(_ _ isT) mf] := @arg_maxnP _ [` Ax]%fset xpredT (f \o val) isT.
exists (val y); split; first exact: valP.
by move=> z Az; have := mf [` Az]%fset.
Qed.

Lemma image_nat_maximum n (f : nat -> nat) :
  (exists i, i <= n /\ forall j, j <= n -> f j <= f i)%N.
Proof.
have [i _ /(_ _ isT) mf] := @arg_maxnP _ (@ord0 n) xpredT f isT.
by exists i; split; rewrite ?leq_ord// => j jn; have := mf (@Ordinal n.+1 j jn).
Qed.

Lemma card_fset_sum1 (T : choiceType) (A : {fset T}) :
  #|` A| = (\sum_(i <- A) 1)%N.
Proof. by rewrite big_seq_fsetE/= sum1_card cardfE. Qed.

Arguments big_rmcond {R idx op I r} P.
Arguments big_rmcond_in {R idx op I r} P.

Reserved Notation "`1- x" (format "`1- x", at level 2).

Section onem.
Variable R : numDomainType.
Implicit Types r : R.

Definition onem r := 1 - r.
Local Notation "`1- r" := (onem r).

Lemma onem0 : `1-0 = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : `1-1 = 0. Proof. by rewrite /onem subrr. Qed.

Lemma onemK r : `1-(`1-r) = r.
Proof. by rewrite /onem opprB addrCA subrr addr0. Qed.

Lemma add_onemK r : r + `1- r = 1.
Proof. by rewrite /onem addrC subrK. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < `1-r. Proof. by rewrite subr_gt0. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= `1-r.
Proof. by rewrite le_eqVlt => /predU1P[->|/onem_gt0/ltW]; rewrite ?onem1. Qed.

Lemma onem_le1 r : 0 <= r -> `1-r <= 1.
Proof. by rewrite lerBlDr lerDl. Qed.

Lemma onem_lt1 r : 0 < r -> `1-r < 1.
Proof. by rewrite ltrBlDr ltrDl. Qed.

Lemma onemX_ge0 r n : 0 <= r -> r <= 1 -> 0 <= `1-(r ^+ n).
Proof. by move=> ? ?; rewrite subr_ge0 exprn_ile1. Qed.

Lemma onemX_lt1 r n : 0 < r -> `1-(r ^+ n) < 1.
Proof. by move=> ?; rewrite onem_lt1// exprn_gt0. Qed.

Lemma onemD r s : `1-(r + s) = `1-r - s.
Proof. by rewrite /onem addrAC opprD addrA addrAC. Qed.

Lemma onemMr r s : s * `1-r = s - s * r.
Proof. by rewrite /onem mulrBr mulr1. Qed.

Lemma onemM r s : `1-(r * s) = `1-r + `1-s - `1-r * `1-s.
Proof.
rewrite /onem mulrBr mulr1 mulrBl mul1r opprB -addrA.
by rewrite (addrC (1 - r)) !addrA subrK opprB addrA subrK addrK.
Qed.

End onem.
Notation "`1- r" := (onem r) : ring_scope.

Lemma onemV (F : numFieldType) (x : F) : x != 0 -> `1-(x^-1) = (x - 1) / x.
Proof. by move=> ?; rewrite mulrDl divff// mulN1r. Qed.

Lemma lez_abs2 (a b : int) : 0 <= a -> a <= b -> (`|a| <= `|b|)%N.
Proof. by case: a => //= n _; case: b. Qed.

Lemma ler_gtP (R : numFieldType) (x y : R) :
  reflect (forall z, z > y -> x <= z) (x <= y).
Proof.
apply: (equivP (ler_addgt0Pr _ _)); split=> [xy z|xz e e_gt0].
  by rewrite -subr_gt0 => /xy; rewrite addrC addrNK.
by apply: xz; rewrite -[ltLHS]addr0 ler_ltD.
Qed.

Lemma ler_ltP (R : numFieldType) (x y : R) :
  reflect (forall z, z < x -> z <= y) (x <= y).
Proof.
apply: (equivP (ler_addgt0Pr _ _)); split=> [xy z|xz e e_gt0].
  by rewrite -subr_gt0 => /xy; rewrite addrCA -[leLHS]addr0 lerD2l subr_ge0.
by rewrite -lerBlDr xz// -[ltRHS]subr0 ler_ltB.
Qed.

Definition inv_fun T (R : unitRingType) (f : T -> R) x := (f x)^-1%R.
Notation "f \^-1" := (inv_fun f) : ring_scope.
Arguments inv_fun {T R} _ _ /.

Definition bound_side d (T : porderType d) (c : bool) (x : itv_bound T) :=
  if x is BSide c' _ then c == c' else false.

Lemma real_ltr_distlC [R : numDomainType] [x y : R] (e : R) :
  x - y \is Num.real -> (`|x - y| < e) = (x - e < y < x + e).
Proof. by move=> ?; rewrite distrC real_ltr_distl// -rpredN opprB. Qed.

Definition swap {T1 T2 : Type} (x : T1 * T2) := (x.2, x.1).

Section reassociate_products.
Context {X Y Z : Type}.

Definition prodA (xyz : (X * Y) * Z) : X * (Y * Z) :=
  (xyz.1.1, (xyz.1.2, xyz.2)).

Definition prodAr (xyz : X * (Y * Z)) : (X * Y) * Z :=
  ((xyz.1, xyz.2.1), xyz.2.2).

Lemma prodAK : cancel prodA prodAr.
Proof. by case; case. Qed.

Lemma prodArK : cancel prodAr prodA.
Proof. by case => ? []. Qed.

End reassociate_products.

Lemma swapK {T1 T2 : Type} : cancel (@swap T1 T2) (@swap T2 T1).
Proof. by case=> ? ?. Qed.

Definition map_pair {S U : Type} (f : S -> U) (x : (S * S)) : (U * U) :=
  (f x.1, f x.2).

Section order_min.
Variables (d : Order.disp_t) (T : orderType d).

Lemma lt_min_lt (x y z : T) : (Order.min x z < Order.min y z)%O -> (x < y)%O.
Proof.
rewrite /Order.min/=; case: ifPn => xz; case: ifPn => yz; rewrite ?ltxx//.
- by move=> /lt_le_trans; apply; rewrite leNgt.
- by rewrite ltNge (ltW yz).
Qed.

End order_min.

Section positive.

Lemma Pos_to_natE p : Pos.to_nat p = nat_of_pos p.
Proof.
by elim: p => //= p <-;
  rewrite ?(Pnat.Pos2Nat.inj_xI,Pnat.Pos2Nat.inj_xO) NatTrec.doubleE -mul2n.
Qed.

End positive.

Lemma intrD1 {R : ringType} (i : int) : i%:~R + 1 = (i + 1)%:~R :> R.
Proof. by rewrite intrD. Qed.

Lemma intr1D {R : ringType} (i : int) : 1 + i%:~R = (1 + i)%:~R :> R.
Proof. by rewrite intrD. Qed.

From mathcomp Require Import archimedean.

Section floor_ceil.
Context {R : archiDomainType}.
Implicit Type x : R.

Lemma ge_floor x : (Num.floor x)%:~R <= x.
Proof. exact: Num.Theory.ge_floor. Qed.

Lemma floor_ge_int x (z : int) : (z%:~R <= x) = (z <= Num.floor x).
Proof. exact: Num.Theory.floor_ge_int. Qed.

Lemma floor_lt_int x (z : int) : (x < z%:~R) = (Num.floor x < z).
Proof. by rewrite ltNge floor_ge_int -ltNge. Qed.

Lemma floor_ge0 x : (0 <= Num.floor x) = (0 <= x).
Proof. by rewrite -floor_ge_int. Qed.

Lemma floor_le0 x : (x < 1) = (Num.floor x <= 0).
Proof. by rewrite -ltzD1 add0r -floor_lt_int. Qed.

Lemma floor_lt0 x : (x < 0) = (Num.floor x < 0).
Proof. by rewrite -floor_lt_int. Qed.

Lemma lt_succ_floor x : x < (Num.floor x + 1)%:~R.
Proof. exact: Num.Theory.lt_succ_floor. Qed.

Lemma floor_eq x m : (Num.floor x == m) = (m%:~R <= x < (m + 1)%:~R).
Proof.
apply/eqP/idP; [move=> <-|by move=> /Num.Theory.floor_def ->].
by rewrite Num.Theory.ge_floor//= Num.Theory.lt_succ_floor.
Qed.

Lemma floor_neq0 x : (Num.floor x != 0) = (x < 0) || (x >= 1).
Proof. by rewrite neq_lt -floor_lt_int gtz0_ge1 -floor_ge_int. Qed.

#[deprecated(since="mathcomp-analysis 1.3.0", note="use `Num.Theory.le_ceil` instead")]
Lemma ceil_ge x : x <= (Num.ceil x)%:~R.
Proof. exact: Num.Theory.le_ceil. Qed.

#[deprecated(since="mathcomp-analysis 1.3.0", note="use `Num.Theory.ceil_le_int`")]
Lemma ceil_ge_int x (z : int) : (x <= z%:~R) = (Num.ceil x <= z).
Proof. exact: Num.Theory.ceil_le_int. Qed.

Lemma ceil_gt_int x (z : int) : (z%:~R < x) = (z < Num.ceil x).
Proof. by rewrite ltNge Num.Theory.ceil_le_int// -ltNge. Qed.

Lemma ceilN x : Num.ceil (- x) = - Num.floor x.
Proof. by rewrite /Num.ceil opprK. Qed.

Lemma floorN x : Num.floor (- x) = - Num.ceil x.
Proof. by rewrite /Num.ceil opprK. Qed.

Lemma ceil_ge0 x : (- 1 < x) = (0 <= Num.ceil x).
Proof. by rewrite ltrNl floor_le0 floorN lerNl oppr0. Qed.

Lemma ceil_gt0 x : (0 < x) = (0 < Num.ceil x).
Proof. by rewrite -ceil_gt_int. Qed.

Lemma ceil_le0 x : (x <= 0) = (Num.ceil x <= 0).
Proof. by rewrite -Num.Theory.ceil_le_int. Qed.

Lemma abs_ceil_ge x : `|x| <= `|Num.ceil x|.+1%:R.
Proof.
rewrite -natr1 natr_absz; have [x0|x0] := ltP 0 x.
  by rewrite !gtr0_norm// -?ceil_gt0// (le_trans (Num.Theory.le_ceil _))// lerDl.
by rewrite !ler0_norm -?ceil_le0// opprK intrD1 ltW// lt_succ_floor.
Qed.

End floor_ceil.

#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to `ceil_gt_int`")]
Notation ceil_lt_int := ceil_gt_int (only parsing).

Section bijection_forall.

Lemma bij_forall A B (f : A -> B) (P : B -> Prop) :
  bijective f -> (forall y, P y) <-> (forall x, P (f x)).
Proof.
by case; rewrite /cancel => g _ cangf; split => // => ? y; rewrite -(cangf y).
Qed.

End bijection_forall.

Lemma and_prop_in (T : Type) (p : mem_pred T) (P Q : T -> Prop) :
  {in p, forall x, P x /\ Q x} <->
  {in p, forall x, P x} /\ {in p, forall x, Q x}.
Proof.
split=> [cnd|[cnd1 cnd2] x xin]; first by split=> x xin; case: (cnd x xin).
by split; [apply: cnd1 | apply: cnd2].
Qed.

Lemma mem_inc_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y / (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f a, f b]}.
Proof.
move=> fle x xab; have leab : (a <= b)%O by rewrite (itvP xab).
by rewrite in_itv/= !fle ?(itvP xab).
Qed.

Lemma mem_dec_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y /~ (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f b, f a]}.
Proof.
move=> fge x xab; have leab : (a <= b)%O by rewrite (itvP xab).
by rewrite in_itv/= !fge ?(itvP xab).
Qed.

Definition sigT_fun {I : Type} {X : I -> Type} {T : Type}
  (f : forall i, X i -> T) (x : {i & X i}) : T :=
  (f (projT1 x) (projT2 x)).
