(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import archimedean finset interval mathcomp_extra.

(**md**************************************************************************)
(* # MathComp extra                                                           *)
(*                                                                            *)
(* This files contains lemmas that should eventually be backported            *)
(* to mathcomp. These lemmas may change before being backported to mathcomp,  *)
(* don't use anything in this file outside of Analysis. For this same reason, *)
(* nothing in this file should be mentionned in the changelog.                *)
(* Once a result is backported to mathcomp, please move it to mathcomp_extra.v*)
(* and mention it in the changelog.                                           *)
(*                                                                            *)
(* ```                                                                        *)
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

Attributes warn(note="The unstable.v file should only be used inside analysis.",
  cats="internal-analysis").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

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
  by rewrite addrCA addrK.
by rewrite addrCA addrAC subrr add0r.
Qed.

Lemma minr_absE (x y : R) : Num.min x y = (x + y - `|x - y|) / 2%:R.
Proof.
apply: (addrI (Num.max x y)); rewrite addr_max_min maxr_absE. (* TODO: ring *)
by rewrite -mulrDl addrCA addrK mulrDl -splitr.
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

Lemma onemK r : `1-(`1-r) = r. Proof. exact: subKr. Qed.

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

Lemma intrD1 {R : ringType} (i : int) : i%:~R + 1 = (i + 1)%:~R :> R.
Proof. by rewrite intrD. Qed.

Lemma intr1D {R : ringType} (i : int) : 1 + i%:~R = (1 + i)%:~R :> R.
Proof. by rewrite intrD. Qed.

Section num_trunc_floor_ceil.
Context {R : archiNumDomainType}.
Implicit Type x : R.

Lemma ge_trunc x : ((Num.trunc x)%:R <= x) = (0 <= x).
Proof.
by have := trunc_floor x; case: ifP => [/trunc_itv/andP[] | _ -> //].
(* simplify proof when backporting:
by have := Def.truncP x; case: ifP => [+ /andP[] | + /eqP->//]. *)
Qed.

Lemma real_ltStrunc x : x \is Num.real -> x < (Num.trunc x).+1%:R.
Proof. by move/real_ge0P => [/trunc_itv/andP[]|/lt_le_trans->]. Qed.

Lemma trunc_ge_nat x n : 0 <= x -> (n <= Num.trunc x)%N = (n%:R <= x).
Proof.
move=> /trunc_itv /andP[letx ltxt1]; apply/idP/idP => lenx.
  by apply: le_trans letx; rewrite ler_nat.
by rewrite -ltnS -(ltr_nat R); apply: le_lt_trans ltxt1.
Qed.

Lemma trunc_gt_nat x n : (n < Num.trunc x)%N = (n.+1%:R <= x).
Proof.
have := trunc_floor x; case: ifP => [x0 _ | x0 ->].
  by rewrite trunc_ge_nat.
by rewrite ltn0; apply/esym/(contraFF _ x0)/le_trans.
(* simplify proof when backporting
have := archimedean.Num.Def.truncP x; case: ifP => [x0 _ | x0 /eqP->].
  by rewrite trunc_ge_nat.
by rewrite ltn0; apply/esym/(contraFF _ x0)/le_trans. *)
Qed.

Lemma trunc_lt_nat x n : 0 <= x -> (Num.trunc x < n)%N = (x < n%:R).
Proof. by move=> ?; rewrite real_ltNge ?ger0_real// ltnNge trunc_ge_nat. Qed.

Lemma real_trunc_le_nat x n : x \is Num.real ->
  (Num.trunc x <= n)%N = (x < n.+1%:R).
Proof. by move=> ?; rewrite real_ltNge// leqNgt trunc_gt_nat. Qed.

Lemma trunc_eq x n : 0 <= x -> (Num.trunc x == n) = (n%:R <= x < n.+1%:R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: trunc_itv|exact: trunc_def].
Qed.

Lemma le_trunc : {homo Num.trunc : x y / x <= y :> R >-> (x <= y)%N}.
Proof.
move=> x y lexy.
move: (trunc_floor x) (trunc_floor y).
case: ifP => [x0 _ | x0->//].
case: ifP => [y0 _ | + ->]; [|by rewrite (le_trans x0 lexy)].
move: (trunc_itv y0) => /andP[_ /(le_lt_trans lexy)].
move: (trunc_itv x0) => /andP[+ _] => /le_lt_trans/[apply].
by rewrite ltr_nat ltnS.
(* simplify proof when backporting:
move: (archimedean.Num.Def.truncP x) (archimedean.Num.Def.truncP y).
case: ifP => [x0 /andP[letx _] | x0 /eqP->//].
case: ifP => [y0 /andP[_] | + /eqP->]; [|by rewrite (le_trans x0 lexy)].
by move=> /(le_lt_trans lexy) /(le_lt_trans letx); rewrite ltr_nat ltnS. *)
Qed.

Lemma real_lt_floorD1 x : x \is Num.real -> x < (Num.floor x + 1)%:~R.
Proof. by move=> /real_floor_itv /andP[]. Qed.

(* TODO: rename to real_floor_ge_int,
   once the currently deprecated one has been removed *)
Lemma real_floor_ge_int_tmp x n : x \is Num.real ->
  (n <= Num.floor x) = (n%:~R <= x).
Proof.
move=> /real_floor_itv /andP[lefx ltxf1]; apply/idP/idP => lenx.
  by apply: le_trans lefx; rewrite ler_int.
by rewrite -ltzD1 -(ltr_int R); apply: le_lt_trans ltxf1.
Qed.

#[deprecated(since="mathcomp-analysis 1.10.0",
  note="Use real_floor_ge_int_tmp instead.")]
Lemma real_floor_ge_int x n : x \is Num.real -> (n%:~R <= x) = (n <= Num.floor x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma real_floor_lt_int x n : x \is Num.real -> (Num.floor x < n) = (x < n%:~R).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_floor_ge_int_tmp -?ltNge.
Qed.

Lemma le_floor : {homo (@Num.floor R) : x y / x <= y}.
Proof. exact: floor_le. Qed.

Lemma real_floor_eq x n : x \is Num.real ->
  (Num.floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_floor_itv|exact: floor_def].
Qed.

Lemma real_floor_ge0 x : x \is Num.real -> (0 <= Num.floor x) = (0 <= x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma floor_lt0 x : (Num.floor x < 0) = (x < 0).
Proof.
have := archimedean.Num.Theory.floorP x; case: ifP => [xr _ | xr /eqP].
  by rewrite real_floor_lt_int.
rewrite -?[0%Z]/(@GRing.zero int) => <-.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ltr0_real.
(* simpler proof when backporting:
have := archimedean.Num.Theory.floorP x; case: ifP => [xr _ | xr /eqP<-].
  by rewrite real_floor_lt_int.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ltr0_real. *)
Qed.

Lemma real_floor_le0 x : x \is Num.real -> (Num.floor x <= 0) = (x < 1).
Proof. by move=> ?; rewrite -ltzD1 add0r real_floor_lt_int. Qed.

Lemma floor_gt0 x : (Num.floor x > 0) = (x >= 1).
Proof.
have := archimedean.Num.Theory.floorP x; case: ifP => [xr _ | xr /eqP->].
  by rewrite gtz0_ge1 real_floor_ge_int_tmp.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ger1_real.
Qed.

Lemma floor_neq0 x : (Num.floor x != 0) = (x < 0) || (x >= 1).
Proof.
have := archimedean.Num.Theory.floorP x.
case: ifP => [xr _ | xr /eqP->]; rewrite ?eqxx/=.
  by rewrite neq_lt floor_lt0 floor_gt0.
by apply/esym/(contraFF _ xr) => /orP[]; [exact: ltr0_real|exact: ger1_real].
Qed.

(* TODO: rename to real_ceil_le_int,
   once the currently deprecated one has been removed *)
Lemma real_ceil_le_int_tmp x n : x \is Num.real ->
  (Num.ceil x <= n) = (x <= n%:~R).
Proof.
rewrite -realN; move=> /(real_floor_ge_int_tmp (- n)).
by rewrite ?ceilNfloor mulrNz lerNl => ->; rewrite lerN2.
Qed.

#[deprecated(since="mathcomp-analyss 1.10.0",
  note="Use real_ceil_le_int_tmp instead.")]
Lemma real_ceil_le_int x n : x \is Num.real -> (x <= n%:~R) = (Num.ceil x <= n).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma real_ceil_gt_int x n : x \is Num.real -> (n < Num.ceil x) = (n%:~R < x).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_ceil_le_int_tmp ?ltNge.
Qed.

Lemma le_ceil : {homo (@Num.ceil R) : x y / x <= y}.
Proof. exact: ceil_le. Qed.

Lemma real_ceil_eq x n : x \is Num.real ->
  (Num.ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_ceil_itv|exact: ceil_def].
Qed.

Lemma real_ceil_ge0 x : x \is Num.real -> (0 <= Num.ceil x) = (-1 < x).
Proof.
by move=> ?; rewrite ?ceilNfloor oppr_ge0 real_floor_le0 ?realN// ltrNl.
Qed.

Lemma ceil_lt0 x : Num.ceil x < 0 = (x <= -1).
Proof. by rewrite ?ceilNfloor oppr_lt0 floor_gt0 lerNr. Qed.

Lemma real_ceil_le0 x : x \is Num.real -> (Num.ceil x <= 0) = (x <= 0).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma ceil_gt0 x : (Num.ceil x > 0) = (x > 0).
Proof. by rewrite ?ceilNfloor oppr_gt0 floor_lt0 oppr_lt0. Qed.

Lemma ceil_neq0 x : (Num.ceil x != 0) = (x <= -1) || (x > 0).
Proof. by rewrite ?ceilNfloor oppr_eq0 floor_neq0 oppr_lt0 lerNr orbC. Qed.

End num_trunc_floor_ceil.

Section trunc_floor_ceil.
Context {R : archiDomainType}.
Implicit Type x : R.

Lemma ltStrunc x : x < (Num.trunc x).+1%:R.
Proof. exact: real_ltStrunc. Qed.

Lemma trunc_le_nat x n : (Num.trunc x <= n)%N = (x < n.+1%:R).
Proof. exact: real_trunc_le_nat. Qed.

Lemma lt_floorD1 x : x < (Num.floor x + 1)%:~R.
Proof. exact: real_lt_floorD1. Qed.

#[deprecated(since="mathcomp-analysis 1.10.0", note="Use floor_ge_int_tmp instead.")]
Lemma floor_ge_int x n : (n%:~R <= x) = (n <= Num.floor x).
Proof. exact: real_floor_ge_int. Qed.

(* TODO: rename to floor_ge_int,
   once the currently deprecated one has been removed *)
Lemma floor_ge_int_tmp x n : (n <= Num.floor x) = (n%:~R <= x).
Proof. exact: real_floor_ge_int_tmp. Qed.

Lemma floor_lt_int x n : (Num.floor x < n) = (x < n%:~R).
Proof. exact: real_floor_lt_int. Qed.

Lemma floor_eq x n : (Num.floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof. exact: real_floor_eq. Qed.

Lemma floor_ge0 x : (0 <= Num.floor x) = (0 <= x).
Proof. exact: real_floor_ge0. Qed.

Lemma floor_le0 x : (Num.floor x <= 0) = (x < 1).
Proof. exact: real_floor_le0. Qed.

#[deprecated(since="mathcomp-analysis 1.10.0", note="Use ceil_le_int_tmp instead.")]
Lemma ceil_le_int x n : x <= n%:~R = (Num.ceil x <= n).
Proof. exact: real_ceil_le_int. Qed.

(* TODO: rename to ceil_le_int,
   once the currently deprecated one has been removed *)
Lemma ceil_le_int_tmp x n : (Num.ceil x <= n) = (x <= n%:~R).
Proof. exact: real_ceil_le_int_tmp. Qed.

Lemma ceil_gt_int x n : (n < Num.ceil x) = (n%:~R < x).
Proof. exact: real_ceil_gt_int. Qed.

Lemma ceil_eq x n : (Num.ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof. exact: real_ceil_eq. Qed.

Lemma ceil_ge0 x : (0 <= Num.ceil x) = (-1 < x).
Proof. exact: real_ceil_ge0. Qed.

Lemma ceil_le0 x : (Num.ceil x <= 0) = (x <= 0).
Proof. exact: real_ceil_le0. Qed.

Lemma abs_ceil_ge x : `|x| <= `|Num.ceil x|.+1%:R.
Proof.
rewrite -natr1 natr_absz; have [x0|x0] := ltP 0 x.
  by rewrite !gtr0_norm ?ceil_gt0// (le_trans (Num.Theory.le_ceil _))// lerDl.
by rewrite !ler0_norm ?ceil_le0// ?ceilNfloor opprK intrD1 ltW// lt_floorD1.
Qed.

End trunc_floor_ceil.

#[deprecated(since="mathcomp-analysis 1.3.0", note="Use ceil_gt_int instead.")]
Notation ceil_lt_int := ceil_gt_int (only parsing).

Lemma natr_int {R : archiNumDomainType} n : n%:R \is a @Num.int R.
Proof. by rewrite Num.Theory.intrEge0. Qed.

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

(* PR 114 to finmap in progress *)
Section FsetPartitions.
Variables T I : choiceType.
Implicit Types (x y z : T) (A B D X : {fset T}) (P Q : {fset {fset T}}).
Implicit Types (J : pred I) (F : I -> {fset T}).

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Let rhs_cond P K E :=
  (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A | K x) E x)%fset.
Let rhs P E := (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A) E x)%fset.

Lemma partition_disjoint_bigfcup (f : T -> R) (F : I -> {fset T})
  (K : {fset I}) :
  (forall i j, i \in K -> j \in K -> i != j -> [disjoint F i & F j])%fset ->
  \big[op/idx]_(i <- \big[fsetU/fset0]_(x <- K) (F x)) f i =
  \big[op/idx]_(k <- K) (\big[op/idx]_(i <- F k) f i).
Proof.
move=> disjF; pose P := [fset F i | i in K & F i != fset0]%fset.
have trivP : trivIfset P.
  apply/trivIfsetP => _ _ /imfsetP[i iK ->] /imfsetP[j jK ->] neqFij.
  move: iK; rewrite !inE/= => /andP[iK Fi0].
  move: jK; rewrite !inE/= => /andP[jK Fj0].
  by apply: (disjF _ _ iK jK); apply: contraNneq neqFij => ->.
have -> : (\bigcup_(i <- K) F i)%fset = fcover P.
  apply/esym; rewrite /P fcover_imfset big_mkcond /=; apply eq_bigr => i _.
  by case: ifPn => // /negPn/eqP.
rewrite big_trivIfset // /rhs big_imfset => [|i j iK /andP[jK notFj0] eqFij] /=.
  rewrite big_filter big_mkcond; apply eq_bigr => i _.
  by case: ifPn => // /negPn /eqP ->;  rewrite big_seq_fset0.
move: iK; rewrite !inE/= => /andP[iK Fi0].
by apply: contraNeq (disjF _ _ iK jK) _; rewrite -fsetI_eq0 eqFij fsetIid.
Qed.

End FsetPartitions.

(* TODO: move to ssrnum *)
Lemma prodr_ile1 {R : realDomainType} (s : seq R) :
  (forall x, x \in s -> 0 <= x <= 1)%R -> (\prod_(j <- s) j <= 1)%R.
Proof.
elim: s => [_ | y s ih xs01]; rewrite ?big_nil// big_cons.
have /andP[y0 y1] : (0 <= y <= 1)%R by rewrite xs01// mem_head.
rewrite mulr_ile1 ?andbT//.
  rewrite big_seq prodr_ge0// => x xs.
  by have := xs01 x; rewrite inE xs orbT => /(_ _)/andP[].
by rewrite ih// => e xs; rewrite xs01// in_cons xs orbT.
Qed.

(* TODO: move to ssrnum *)

Lemma size_filter_gt0 T P (r : seq T) : (size (filter P r) > 0)%N = (has P r).
Proof. by elim: r => //= x r; case: ifP. Qed.

Lemma ltr_sum [R : numDomainType] [I : Type] (r : seq I)
    [P : pred I] [F G : I -> R] :
  has P r ->
  (forall i : I, P i -> F i < G i) ->
  \sum_(i <- r | P i) F i < \sum_(i <- r | P i) G i.
Proof.
rewrite -big_filter -[ltRHS]big_filter -size_filter_gt0.
case: filter (filter_all P r) => //= x {}r /andP[Px Pr] _ ltFG.
rewrite !big_cons ltr_leD// ?ltFG// -(all_filterP Pr) !big_filter.
by rewrite ler_sum => // i Pi; rewrite ltW ?ltFG.
Qed.

Lemma ltr_sum_nat [R : numDomainType] [m n : nat] [F G : nat -> R] :
  (m < n)%N -> (forall i : nat, (m <= i < n)%N -> F i < G i) ->
  \sum_(m <= i < n) F i < \sum_(m <= i < n) G i.
Proof.
move=> lt_mn i; rewrite big_nat [ltRHS]big_nat ltr_sum//.
by apply/hasP; exists m; rewrite ?mem_index_iota leqnn lt_mn.
Qed.
