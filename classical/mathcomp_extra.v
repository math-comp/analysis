(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
Require Import BinPos.
From mathcomp Require choice.
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
(*         monotonous A f := {in A &, {mono f : x y / x <= y}} \/             *)
(*                           {in A &, {mono f : x y /~ x <= y}}               *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(**************************)
(* MathComp 2.1 additions *)
(**************************)

From mathcomp Require Import poly.

Definition coefE :=
  (coef0, coef1, coefC, coefX, coefXn,
   coefZ, coefMC, coefCM, coefXnM, coefMXn, coefXM, coefMX, coefMNn, coefMn,
   coefN, coefB, coefD,
   coef_cons, coef_Poly, coef_poly,
   coef_deriv, coef_nderivn, coef_derivn, coef_map, coef_sum,
   coef_comp_poly).

Module Export Pdeg2.

Module Export Field.

Section Pdeg2Field.
Variable F : fieldType.
Hypothesis nz2 : 2%:R != 0 :> F.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let a2neq0 : 2%:R * a != 0. Proof. by rewrite mulf_neq0. Qed.
Let sqa2neq0 : (2%:R * a) ^+ 2 != 0. Proof. exact: expf_neq0. Qed.

Let aa4 : 4%:R * a * a = (2%:R * a)^+2.
Proof. by rewrite expr2 mulrACA mulrA -natrM. Qed.

Let splitr (x : F) : x = x / 2%:R + x / 2%:R.
Proof.
apply: (mulIf nz2); rewrite -mulrDl mulfVK//.
by rewrite -[2%:R]/(1 + 1)%:R natrD mulrDr mulr1.
Qed.

Let pE : p = a *: 'X^2 + b *: 'X + c%:P.
Proof.
apply/polyP => + /[!coefE] => -[|[|[|i]]] /=; rewrite !Monoid.simpm//.
by rewrite nth_default// degp.
Qed.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg2_poly_canonical :
  p = a *: (('X + (b / (2%:R * a))%:P)^+2 - (delta / (4%:R * a ^+ 2))%:P).
Proof.
rewrite pE sqrrD -!addrA scalerDr; congr +%R; rewrite addrA scalerDr; congr +%R.
- rewrite -mulrDr -polyCD -!mul_polyC mulrA mulrAC -polyCM.
  by rewrite [a * _]mulrC mulrDl invfM -!mulrA mulVf// mulr1 -splitr.
- rewrite [a ^+ 2]expr2 mulrA aa4 -polyC_exp -polyCB expr_div_n -mulrBl subKr.
  by rewrite -mul_polyC -polyCM mulrCA mulrACA aa4 mulrCA mulfV// mulr1.
Qed.

Variable r : F.
Hypothesis r_sqrt_delta : r ^+ 2 = delta.

Let r1 := (- b - r) / (2%:R * a).
Let r2 := (- b + r) / (2%:R * a).

Lemma deg2_poly_factor : p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof.
rewrite [p]deg2_poly_canonical//= -/a -/b -/c -/delta /r1 /r2.
rewrite ![(- b + _) * _]mulrDl 2!polyCD 2!opprD 2!addrA !mulNr !polyCN !opprK.
rewrite -scalerAl [in RHS]mulrC -subr_sqr -polyC_exp -[4%:R]/(2 * 2)%:R natrM.
by rewrite -expr2 -exprMn [in RHS]exprMn exprVn r_sqrt_delta.
Qed.

End Pdeg2Field.
End Field.

Module Real.

Section Pdeg2Real.

Variable F : realFieldType.

Section Pdeg2RealConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis age0 : 0 <= a.

Let delta := b ^+ 2 - 4%:R * a * c.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a4gt0 : 0 < 4%:R * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Lemma deg2_poly_min x : p.[- b / (2%:R * a)] <= p.[x].
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c /delta !hornerE/=.
by rewrite ler_pM2l// lerD2r addrC mulNr subrr ?mulr0 ?expr0n sqr_ge0.
Qed.

Lemma deg2_poly_minE : p.[- b / (2%:R * a)] = - delta / (4%:R * a).
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c -/delta !hornerE/=.
rewrite -?expr2 [X in X^+2]addrC [in LHS]mulNr subrr expr0n add0r mulNr.
by rewrite mulrC mulNr invfM mulrA mulfVK.
Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2%:R * a)))]; last first.
  by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
apply: le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
Qed.

End Pdeg2RealConvex.

End Pdeg2Real.

Section Pdeg2RealClosed.

Variable F : rcfType.

Section Pdeg2RealClosedConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let nz2 : 2%:R != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Let delta := b ^+ 2 - 4%:R * a * c.

Let r1 := (- b - Num.sqrt delta) / (2%:R * a).
Let r2 := (- b + Num.sqrt delta) / (2%:R * a).

Lemma deg2_poly_factor : 0 <= delta -> p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

End Pdeg2RealClosedConvex.

End Pdeg2RealClosed.
End Real.

End Pdeg2.

Section Degle2PolyRealConvex.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg_le2_poly_delta_ge0 : 0 <= a -> (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
move=> age0 pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'.
  exact/(Real.deg2_poly_ge0 degp' age0).
have a0 : a = 0 by rewrite /a nth_default.
rewrite /delta a0 mulr0 mul0r subr0 exprn_even_le0//=.
have [//|/eqP nzb] := eqP; move: (pge0 ((- 1 - c) / b)).
have -> : p = b *: 'X + c%:P.
  apply/polyP => + /[!coefE] => -[|[|i]] /=; rewrite !Monoid.simpm//.
  by rewrite nth_default// -ltnS (leq_trans degp').
by rewrite !hornerE/= mulrAC mulfV// mul1r subrK ler0N1.
Qed.

End Degle2PolyRealConvex.

Section Degle2PolyRealClosedConvex.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg_le2_poly_ge0 : (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
have [age0|alt0] := leP 0 a; first exact: deg_le2_poly_delta_ge0.
move=> pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'; last first.
  by move: alt0; rewrite /a nth_default ?ltxx.
have [//|dge0] := leP delta 0.
pose r1 := (- b - Num.sqrt delta) / (2%:R * a).
pose r2 := (- b + Num.sqrt delta) / (2%:R * a).
pose x0 := Num.max (r1 + 1) (r2 + 1).
move: (pge0 x0); rewrite (Real.deg2_poly_factor degp' (ltW dge0)).
rewrite !hornerE/= -mulrA nmulr_rge0// leNgt => /negbTE<-.
by apply: mulr_gt0; rewrite subr_gt0 lt_maxr ltrDl ltr01 ?orbT.
Qed.

End Degle2PolyRealClosedConvex.

Lemma natr1 (R : ringType) (n : nat) : (n%:R + 1 = n.+1%:R :> R)%R.
Proof. by rewrite GRing.mulrSr. Qed.

Lemma nat1r (R : ringType) (n : nat) : (1 + n%:R = n.+1%:R :> R)%R.
Proof. by rewrite GRing.mulrS. Qed.

(**************************)
(* MathComp 2.2 additions *)
(**************************)

Notation "f \min g" := (Order.min_fun f g) : function_scope.
Notation "f \max g" := (Order.max_fun f g) : function_scope.

Lemma ler_sqrt {R : rcfType} (a b : R) :
  (0 <= b -> (Num.sqrt a <= Num.sqrt b) = (a <= b))%R.
Proof.
have [b_gt0 _|//|<- _] := ltgtP; last first.
  by rewrite sqrtr0 -sqrtr_eq0 le_eqVlt ltNge sqrtr_ge0 orbF.
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

(**********************)
(* not yet backported *)
(**********************)

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
move=> /predU1P[<-|i0t]; first by rewrite Pi0 le_maxr// lexx.
by case: ifPn => Ph; [rewrite le_maxr ih// orbT|rewrite ih].
Qed.

(* NB: as of [2023-08-28], bigop.bigmax_sup_seq already exists for nat *)
Lemma bigmax_sup_seq (m : T) (F : I -> T) :
  i0 \in r -> P i0 -> (m <= F i0)%O ->
  (m <= \big[Order.max/x]_(i <- r | P i) F i)%O.
Proof. by move=> i0r Pi0 ?; apply: le_trans (le_bigmax_seq _ _ _). Qed.

End bigmax_seq.
Arguments le_bigmax_seq {d T} x {I r} i0 P.

(* NB: PR 1079 to MathComp in progress *)
Lemma gerBl {R : numDomainType} (x y : R) : 0 <= y -> x - y <= x.
Proof. by move=> y0; rewrite lerBlDl lerDr. Qed.

(* the following appears in MathComp 2.1.0 and MathComp 1.18.0 *)
Section normr.
Variable R : realDomainType.

Definition Rnpos : qualifier 0 R := [qualify x : R | x <= 0].
Lemma nposrE x : (x \is Rnpos) = (x <= 0). Proof. by []. Qed.

Lemma ger0_le_norm :
  {in Num.nneg &, {mono (@Num.Def.normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !nnegrE => x0 y0; rewrite !ger0_norm. Qed.

Lemma gtr0_le_norm :
  {in Num.pos &, {mono (@Num.Def.normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !posrE => /ltW x0 /ltW y0; exact: ger0_le_norm. Qed.

Lemma ler0_ge_norm :
  {in Rnpos &, {mono (@Num.Def.normr _ R) : x y / x <= y >-> x >= y}}.
Proof.
move=> x y; rewrite !nposrE => x0 y0.
by rewrite !ler0_norm// -subr_ge0 opprK addrC subr_ge0.
Qed.

Lemma ltr0_ge_norm :
  {in Num.neg &, {mono (@Num.Def.normr _ R) : x y / x <= y >-> x >= y}}.
Proof. by move=> x y; rewrite !negrE => /ltW x0 /ltW y0; exact: ler0_ge_norm. Qed.

End normr.

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
Reserved Notation "f \^-1" (at level 3, format "f \^-1", left associativity).

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

Definition swap (T1 T2 : Type) (x : T1 * T2) := (x.2, x.1).

Section order_min.
Variables (d : Order.disp_t) (T : orderType d).

Lemma lt_min_lt (x y z : T) : (Order.min x z < Order.min y z)%O -> (x < y)%O.
Proof.
rewrite /Order.min/=; case: ifPn => xz; case: ifPn => yz; rewrite ?ltxx//.
- by move=> /lt_le_trans; apply; rewrite leNgt.
- by rewrite ltNge (ltW yz).
Qed.

End order_min.

Structure revop X Y Z (f : Y -> X -> Z) := RevOp {
  fun_of_revop :> X -> Y -> Z;
  _ : forall x, f x =1 fun_of_revop^~ x
}.

Definition mulr_rev {R : ringType} (y x : R) := x * y.
Canonical rev_mulr {R : ringType} :=
  @RevOp _ _ _ mulr_rev (@GRing.mul R) (fun _ _ => erefl).
