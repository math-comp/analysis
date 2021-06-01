(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import nsatz_realtype.
Require Import classical_sets posnum topology normedtype landau sequences.
Require Import derive.

(******************************************************************************)
(*                Definitions and lemmas about exponential                    *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*  Some addition for  _ --> _                                                *)
(******************************************************************************)

Section Cvg.

Section cvg_extra.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvg_sub0 f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Proof.
by move=> Cfg Cg; have := cvgD Cfg Cg; rewrite subrK add0r; apply.
Qed.

Lemma cvg_zero f a : (f - cst a) @ F --> (0 : V) -> f @ F --> a.
Proof. by move=> Cfa; apply: cvg_sub0 Cfa (cvg_cst _). Qed.

Lemma cvg_equiv (f g : T -> V) (a : V) :
  {near F, f =1 g} -> f x @[x --> F] --> a -> g x @[x --> F] --> a.
Proof. by move=> /near_eq_cvg; exact: cvg_trans. Qed.

End cvg_extra.

Variable R : realType.

Lemma cvg_series_bounded (f : R^nat) :
  cvg (series f) ->  exists2 K, 0 < K & (forall i, `|f i| < K).
Proof.
(* There should be something simpler *)
move=> Cf.
have F1 := cvg_series_cvg_0 Cf.
have F2 : bounded_near id [filter of f] by apply: cvg_bounded F1.
have [K1 K1_gt0 KF]:= ex_strict_bound_gt0 F2.
case: KF => x _ Hx.
pose K2 := \sum_(i < x) (1 + `|f i|).
have K2_ge0 : 0 <= K2 by apply: sumr_ge0 => *; apply: addr_ge0.
have K1LK1DK2 : K1 <= K1 + K2 by rewrite -{1}[K1]addr0 ler_add2l.
have K2LK1DK2 : K2 <= K1 + K2 by rewrite -{1}[K2]add0r ler_add2r ltW.
exists (K1 + K2) => [|i]; first by apply: lt_le_trans K1_gt0 _.
have [iLx|xLi] := leqP x i; first by apply: lt_le_trans (Hx i iLx) _.
apply: lt_le_trans K2LK1DK2.
rewrite /K2 (bigD1 (Ordinal xLi)) //=.
rewrite -subr_gt0 addrC !addrA [- _ + _]addrC subrK.
apply: lt_le_trans (_ : 1 <= _) => //.
rewrite -subr_ge0 [1 + _]addrC addrK //.
by apply: sumr_ge0 => *; apply: addr_ge0.
Qed.

Lemma eq_cvg_lim : forall (R : realType) (f g : (R) ^nat),
  f = g -> (f --> lim f) = (g --> lim g).
Proof. by move=> R1 f1 g1 ->. Qed.

Lemma eq_cvgl (f g : R^nat) (x : R) : f = g -> (f --> x) = (g --> x).
Proof. by move->. Qed. 

Lemma cvgS (f : R^nat) (x : R) : (f \o S --> x) = (f --> x).
Proof.
have <- /= := @cvg_shiftn 1 _ f x.
by apply/eq_cvgl/funext => i; rewrite addn1.
Qed.

Lemma is_cvg_seriesN (f : R^nat) : cvg (series f) -> cvg (series (-f)).
Proof.
move=> Cf.
rewrite /series /= (funext (fun n => sumrN (index_iota 0 n) _ _)).
by apply: is_cvgN => //; apply: is_cvg_cst.
Qed.

Lemma lim_seriesN (f : R^nat) : 
  cvg (series f) -> lim (series (-f)) = - lim (series f).
Proof.
move=> Cf.
rewrite /series /= (funext (fun n => sumrN (index_iota 0 n) _ _)).
by rewrite limN.
Qed.

Lemma is_cvg_seriesZr (f : R^nat) k : cvg (series f) -> cvg (series (k *: f)).
Proof.
move=> Cf.
rewrite /series /= -(funext (fun n => scaler_sumr k (index_iota 0 n) _ _)).
by apply: is_cvgZr => //; apply: is_cvg_cst.
Qed.

Lemma lim_seriesZr (f : R^nat) k : 
  cvg (series f) -> lim (series (k *: f)) = k *: lim (series f).
Proof.
move=> Cf.
rewrite /series /= -(funext (fun n => scaler_sumr k (index_iota 0 n) _ _)).
by rewrite limZr.
Qed.

Lemma is_cvg_seriesD (f g : R^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f + g)).
Proof.
move=> Cf Cg.
rewrite /series /= (funext (fun n => big_split _ (index_iota 0 n) _ _ _)) /=.
by apply: is_cvgD.
Qed.

Lemma lim_seriesD (f g : R^nat) : 
  cvg (series f) -> cvg (series g) -> 
  lim (series (f + g)) = lim (series f) + lim (series g).
Proof.
move=> Cf Cg.
rewrite /series /= (funext (fun n => big_split _ (index_iota 0 n) _ _ _)) /=.
by apply: limD.
Qed.

Lemma is_cvg_seriesB (f g : R^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f - g)).
Proof.
by move=> Cf Cg; apply: is_cvg_seriesD => //; apply: is_cvg_seriesN.
Qed.

Lemma lim_seriesB (f g : R^nat) : 
  cvg (series f) -> cvg (series g) -> 
  lim (series (f - g)) = lim (series f) - lim (series g).
Proof.
move=> Cf Cg; rewrite lim_seriesD //; last by apply: is_cvg_seriesN.
by rewrite lim_seriesN.
Qed.

Lemma lim_series_norm (f : R^nat) :
  cvg [normed series f] -> `|lim (series f)| <= lim [normed series f].
Proof.
move=> Cnf.
have Cf : cvg (series f) by apply: normed_cvg.
rewrite -lim_norm //.
apply: ler_lim => [|//|]; first by apply: is_cvg_norm.
near=> x.
by rewrite /series /= /series /= ler_norm_sum.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_series_le (f g : (R) ^nat) : 
  cvg (series f) -> cvg (series g) -> (forall n : nat, f n <= g n) -> 
  lim (series f) <= lim (series g).
Proof.
move=> Cf Cg fLg; apply ler_lim => [//|//|].
by near=> x; rewrite /series /= ler_sum.
Grab Existential Variables. all: end_near. Qed.

End Cvg.

(******************************************************************************)
(*  Some addition for  continuous                                             *)
(******************************************************************************)

(* About continuous *)

Section continuous.

Lemma continuous_withinNshiftx 
  {K : numFieldType} {U V : normedModType K} 
    (f : U -> V) x :
  f \o shift x @ 0^' --> f x <-> {for x, continuous f}.
Proof.
split=> [cfx P /= fxP|].
  rewrite !nbhs_nearE !near_map !near_nbhs in fxP *.
  rewrite (@near_shift _ _ 0) subr0 /=.
  have /= := cfx P fxP.
  rewrite !near_simpl near_withinE near_simpl /= => Pf; near=> y.
  have [->|] := eqVneq y 0.
    by rewrite /= add0r; apply: nbhs_singleton.
  by near: y.
move=> Cf.
apply: continuous_cvg => //.
rewrite -[X in _ --> X]add0r.
apply: cvgD; last by apply: cvg_cst.
by apply: nbhs_dnbhs.
Grab Existential Variables. all: end_near. Qed.

End continuous.

(******************************************************************************)
(*  Some addition for  is_derive                                              *)
(******************************************************************************)

Section is_derive.

Variable R : realType.

Global Instance is_derive1_id (x : R) : is_derive x 1 id 1.
Proof.
have Did := (@linear_differentiable _ _ _ [linear of idfun]).
constructor; first by apply/derivable1_diffP.
rewrite deriveE //.
by have /= -> := (@diff_lin _ _ _ [linear of idfun] x).
Qed.

Lemma is_derive_0_cst (f : R -> R) x y : 
  (forall x, is_derive x 1 f 0) -> f x = f y.
Proof.
move=> Hd.
wlog xLy : x y / x <= y.
  by move=> H; case: (leP x y) => [/H |/ltW /H].
rewrite -(subKr (f y) (f x)).
case: (MVT xLy) => [x1 _|_ _].
  by apply/differentiable_continuous/derivable1_diffP.
by rewrite mul0r => ->; rewrite subr0.
Qed.

Lemma is_derive1_carat (f : R -> R) (x a : R) :
  is_derive x 1 f a <-> 
  exists g, [/\ forall z, f z - f x = g z * (z - x),
        {for x, continuous g} & g x = a].
Proof.
split => [Hd|[g [fxE Cg gxE]]].
  exists (fun z => if z == x then a else (f(z) - f(x)) / (z - x)); split.
  - move=> z; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
    by rewrite -subr_eq0 => /divfK->.
  - apply/continuous_withinNshiftx; rewrite eqxx /=.
    pose g1 h := (h^-1 *: ((f \o shift x) h%:A - f x)).
    have F1 : g1 @ 0^' --> a by case: Hd => H1 <-.
    apply: cvg_equiv F1.
    near=> i.
    rewrite ifN; first by rewrite addrK mulrC /= [_%:A]mulr1.
    rewrite -subr_eq0 addrK.
    by near: i; rewrite near_withinE /= near_simpl; near=> x1.
  by rewrite eqxx.
suff Hf : h^-1 *: ((f \o shift x) h%:A - f x) @[h --> 0^'] --> a.
  have F1 : 'D_1 f x = a by apply: cvg_lim.
  rewrite -F1 in Hf.
  by constructor.
have F1 :  (g \o shift x) y @[y --> 0^'] --> a.
  by rewrite -gxE; apply/continuous_withinNshiftx.
apply: cvg_equiv F1.
near=> y.
rewrite /= fxE /= addrK [_%:A]mulr1.
suff yNZ : y != 0 by rewrite [RHS]mulrC mulfK.
by near: y; rewrite near_withinE /= near_simpl; near=> x1.
Grab Existential Variables. all: end_near. Qed.

Global Instance is_derive1_chain (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b -> 
  is_derive x  1 (f \o g) (a * b).
Proof.
move=> Df Dg.
have Cg : {for x, continuous g}.
  apply: differentiable_continuous.
  by case: Dg => /derivable1_diffP.
have /is_derive1_carat[g' [gE Cg' g'E]] := Dg.
have /is_derive1_carat[f' [fE Cf' f'gE]] := Df.
apply/is_derive1_carat.
exists (fun z => if z == x then a * b else (f (g z) - f (g x)) / (z - x)).
split; last by rewrite eqxx.
- move=> z /=.
  case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
  by rewrite -subr_eq0 => zBxNZ; rewrite divfK.
apply/continuous_withinNx; rewrite eqxx.
have /continuous_withinNx : {for x, continuous ((f' \o g) * g')}.
  apply: continuousM => [| //].
  by apply: continuous_comp.
rewrite [(_ * g')]/*%R /= f'gE g'E => Cab.
apply: cvg_equiv Cab; near=> z.
have F : z != x.
  by near: z; rewrite near_withinE /= near_simpl; near=> z.
by rewrite (negPf F) fE gE -mulrA mulfK // subr_eq0.
Grab Existential Variables. all: end_near. Qed.

End is_derive.
(******************************************************************************)
(* Unfold function application (f + f) 0 gives f 0 + f 0                      *)
(******************************************************************************)

Ltac rcfE := 
repeat  rewrite /(@GRing.mul (fct_ringType _ _)) /=
          /(@GRing.exp (fct_ringType _ _)) /=
          /(@GRing.add (fct_ringType _ _)) /=
          /(@GRing.add (fct_zmodType _ _)) /=
          /(@GRing.scale _ (fct_lmodType _ _)) /=
          /(@GRing.opp (fct_ringType _ _)) /=
          /(@GRing.opp (fct_zmodType _ _)) /=.


(******************************************************************************)
(* Differentiability of series inspired by HOL-Light transc.ml                *)
(******************************************************************************)

Section TermDiff.

Variable R : realType.

Fact cvg_series_Xn_inside_norm f (x z : R) :
  cvg (series (fun i =>    f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => `|f i| * z ^+ i)).
Proof.
move=> Cx zLx.
have [K K_gt0 KP] := cvg_series_bounded Cx.
have F1 := cvg_series_cvg_0 Cx.
have F2 n : 0 <= K * `|z ^+ n| / `|x ^+ n|.
  by rewrite !mulr_ge0 ?invr_ge0 // ltW.
apply: normed_cvg.
apply: series_le_cvg F2 _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pmul || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply: ltW.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivr_mulr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric K `|z / x|).
apply: is_cvg_geometric_series; first by rewrite normr_id.
apply/funext => i /=.
by rewrite normrM exprMn mulrA normfV !normrX exprVn.
Qed.

Fact cvg_series_Xn_inside f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => f i * z ^+ i)).
Proof.
move=> Cx zLx.
apply: normed_cvg; rewrite /normed_series_of /=.
rewrite (_ : (fun _ => _) = (fun i : nat => `|f i| * `|z| ^+ i)); last first.
  by apply/funext => i; rewrite normrM normrX.
by apply: cvg_series_Xn_inside_norm Cx _; rewrite normr_id.
Qed.

Definition diffs (f : nat -> R) i := i.+1%:R * f i.+1.

Lemma diffsN (f : nat -> R) :  diffs (- f) = -(diffs f).
Proof. by apply/funext => i; rewrite /diffs /= -mulrN. Qed.

Lemma diffs_sumE n f x :
  \sum_(0 <= i < n)  diffs f i * x ^+ i =
 (\sum_(0 <= i < n) i%:R * f i * x ^+ i.-1) + n%:R * f n * x ^+ n.-1.
Proof.
case: n => [|n]; first by rewrite !big_nil !mul0r add0r.
under eq_bigr do unfold diffs.
by rewrite big_nat_recr //= big_nat_recl //= !mul0r add0r.
Qed.

Lemma diffs_equiv f x :
  let s1 i := diffs f i * x ^+ i in
  let s2 i := i%:R * f i * x ^+ i.-1 in
  cvg (series s1) -> series s2 --> lim (series s1).
Proof.
move=> s1 s2 Cx; rewrite -[lim _]subr0 {2}/series /=.
have s2E n : 
  \sum_(0 <= i < n) s2 i = \sum_(0 <= i < n) s1 i - n%:R * f n * x ^+ n.-1.
  by rewrite diffs_sumE addrK. 
rewrite (eq_cvgl _ (funext s2E)).
apply: cvgB => //; rewrite -cvgS.
by apply: cvg_series_cvg_0.
Qed.

Lemma cvg_diffs_equiv f x :
  let s1 i := diffs f i * x ^+ i in
  let s2 i := i%:R * f i * x ^+ i.-1 in cvg (series s1) -> cvg (series s2).
Proof.
move=> s1 s2 Cx; rewrite /s1 /s2 in Cx.
have F1 := diffs_equiv Cx.
by rewrite (cvg_lim _ (F1)).
Qed.

Let termdiff_P1 m (z h : R) :
  \sum_(0 <= i < m) ((h + z) ^+ (m - i) * z ^+ i - z ^+ m) =
  \sum_(0 <= i < m) z ^+ i * ((h + z) ^+ (m - i) - z ^+ (m - i)).
Proof.
rewrite !big_mkord; apply: eq_bigr => i _.
by rewrite mulrDr mulrN -exprD mulrC addnC subnK // ltnW.
Qed.

Let termdiff_P2 n (z h : R) :
  h != 0 ->
  ((h + z) ^+ n - (z ^+ n)) / h - n%:R * z ^+ n.-1 =
  h * \sum_(0 <= i < n.-1) z ^+ i *
      \sum_(0 <= j < n.-1 - i) (h + z) ^+ j * z ^+ (n.-2 - i - j).
Proof.
move=> hNZ; apply: (mulfI hNZ).
rewrite mulrBr mulrC divfK //.
case: n => [|n].
  by rewrite !expr0 !(mul0r, mulr0, subr0, subrr, big_geq).
rewrite subrXX addrK -mulrBr; congr (_ * _).
rewrite -(big_mkord xpredT (fun i : nat => (h + z) ^+ (n - i) * z ^+ i)).
rewrite big_nat_recr //= subnn expr0 -addrA -mulrBl.
rewrite  -add1n natrD opprD addrA subrr sub0r mulNr.
rewrite mulr_natl -{4}(subn0 n) -sumr_const_nat -sumrB.
rewrite termdiff_P1 mulr_sumr !big_mkord; apply: eq_bigr => i _.
rewrite mulrCA; congr (_ * _).
rewrite subrXX addrK big_nat_rev /= big_mkord.
congr (_ * _); apply: eq_bigr => k _.
by rewrite -!predn_sub subKn // -subnS.
Qed.

Let termdiff_P3 (z h : R) n K :
 h != 0 -> `|z| <= K -> `|h + z| <= K ->
    `|((h +z) ^+ n - z ^+ n) / h - n%:R * z ^+ n.-1|
        <= n%:R * n.-1%:R * K ^+ n.-2 * `|h|.
Proof.
move=> hNZ zLK zhLk.
have KP : 0 <= K by apply: le_trans zLK.
rewrite termdiff_P2 // normrM mulrC.
rewrite ler_pmul2r ?normr_gt0 //.
apply: le_trans (ler_norm_sum _ _ _) _.
rewrite -mulrA mulrC -mulrA.
rewrite -{4}[n.-1]subn0 mulr_natl -sumr_const_nat.
rewrite !big_mkord; apply: ler_sum => i _.
rewrite normrM /=.
case: n i => //= [[]//| n i].
pose d := (n.-1 - i)%nat.
rewrite -[(n - i)%nat]prednK ?subn_gt0 // predn_sub -/d.
rewrite -(subnK (_ : i <= n.-1)%nat) -/d; last first.
  by rewrite -ltnS prednK // (leq_trans _ (ltn_ord i)).
rewrite addnC exprD mulrAC -mulrA.
apply: ler_pmul => //.
  by rewrite normrX ler_expn2r ?qualifE // (le_trans _ zLK).
apply: le_trans (_ : d.+1%:R * K ^+ d <= _); last first.
  rewrite ler_wpmul2r //; first by rewrite exprn_ge0 // (le_trans _ zLK).
  rewrite ler_nat ltnS (leq_trans (leq_subr _ _)) // -ltnS prednK //.
  by rewrite (leq_ltn_trans _ (ltn_ord i)).
apply: le_trans (ler_norm_sum _ _ _) _.
rewrite -{2}[d.+1]subn0 mulr_natl -sumr_const_nat.
rewrite !big_mkord; apply: ler_sum => j _.
rewrite -{4}(subnK (_ : j <= d)%nat) -1?ltnS // addnC exprD normrM.
by apply: ler_pmul; rewrite // normrX ler_expn2r ?qualifE.
Qed.

Lemma cvg_to_0_linear (f : R -> R) K k :
  0 < k -> (forall h, 0 < `|h| < k -> `|f h| <= K * `|h|) ->
    f x @[x --> 0^'] --> (0 : R).
Proof.
(* There should be a shorter proof *)
move=> k_gt0 H; apply/cvg_distP => /= eps eps_gt0; rewrite !near_simpl.
pose k2 : R := k / 2.
have k2_gt0 : 0 < k2 by rewrite divr_gt0.
have k2Lk : k2 < k.
  by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 -subr_gt0 addrK.
have : 0 <= K.
  rewrite -(pmulr_rge0 _ k2_gt0) mulrC -(gtr0_norm k2_gt0).
  apply: le_trans (H _ _) => //.
  by rewrite ger0_norm  ?k2_gt0 // ltW.
rewrite le_eqVlt => /orP[/eqP K_eq0| K_gt0].
  pose k3 := if k2 < eps then k2 else eps.
  have k3_gt0 : 0 < k3 by rewrite /k3; case: (k2 < _).
  have k3Lk : k3 < k by rewrite /k3; case: (ltrP k2) => // /le_lt_trans ->. 
  exists k3 => //= t /=; rewrite !sub0r !normrN => H1 Ht.
  apply: le_lt_trans (H _ _) _; last by rewrite -K_eq0 mul0r.
  by apply/andP; split; [rewrite normr_gt0 | apply: lt_trans H1 _].
have KNZ : K != 0 by case: (ltrgt0P K) K_gt0.
pose k3 := if k2 < eps / K then k2 else eps / K.
have k3_gt0 : 0 < k3 by rewrite /k3; case: (k2 < _); rewrite // divr_gt0.
have k3Lk : k3 < k by rewrite /k3; case: (ltrP k2) => // /le_lt_trans ->.
have k3Le : K * k3 <= eps.
  rewrite -[eps](divfK (_ : K != 0)) // mulrC ler_pmul2r //.
  by rewrite /k3; case: (ltrP k2) => // /ltW.
exists k3 => //= t /=; rewrite !sub0r !normrN => tLk3 tNZ.
have /le_lt_trans ->// : `|f t| <= K * `|t|.
  apply/H/andP; split; first by rewrite normr_gt0.
  by apply: lt_trans tLk3 _.
apply: lt_le_trans k3Le.
by rewrite ltr_pmul2l //.
Qed.

Lemma lim_cvg_to_0_linear (f : nat -> R) (g : R -> nat -> R) k :
  0 < k -> cvg (series f) ->
    (forall h : R, 0 < `|h| < k -> forall n, `|g h n| <= f n * `|h|) ->
     lim (series (g x)) @[x --> 0^'] --> (0 : R).
Proof.
move=> k_gt0 Cf Hg.
apply: (@cvg_to_0_linear _ (lim (series f)) k) => // h hLk; rewrite mulrC.
have Ckf := @is_cvg_seriesZr _ _ `|h| Cf.
have Lkf := lim_seriesZr `|h| Cf.
have Cng : cvg [normed series (g h)].
  apply: series_le_cvg (Hg _ hLk) _  => //.
    by move=> h1; apply: le_trans (Hg _ hLk _).
  by rewrite (funext (fun _ => (@mulrC R _ _))).
apply: le_trans (_ : lim [normed series (g h)] <= _).
  by apply: lim_series_norm.
rewrite -[_ * _]lim_seriesZr //.
apply: lim_series_le => //= => n.
by rewrite [X in _ <= X]mulrC; apply: Hg.
Qed.

Lemma termdiff (c : R^nat) K x :
  cvg (series (fun n => c n * K ^+ n)) ->
  cvg (series (fun n => diffs c n * K ^+ n)) ->
  cvg (series (fun n => diffs (diffs c) n * K ^+ n)) ->
  `|x| < `|K| ->
  is_derive x 1
    (fun x => lim (series (fun n => c(n) * x ^+ n))) 
    (lim (series (fun n => diffs c n * x ^+ n))).
Proof.
move=> Ck CdK CddK xLK; set s := (fun n : nat => _).
set (f := fun x => _).
suff Hf : 
  h^-1 *: (f (h + x) - f x) @[h --> 0^'] --> lim (series s).
  have F : f^`() x = lim (series s) by  apply: cvg_lim Hf.
  rewrite (_ : (fun h => h^-1 *: (f (h + x) - f x)) = 
              (fun h => h^-1 *: (f (h%:A + x) - f x))) in Hf; last first.
    by apply/funext => i //=; rewrite [i%:A]mulr1.
  have Df : derivable f x 1 by rewrite /derivable (cvg_lim _ Hf).
  by constructor=> [//|]; rewrite -derive1E.
set sx := fun n : nat => c n * x ^+ n.
have Csx : cvg (series sx) by apply: cvg_series_Xn_inside Ck _.
pose shx h := fun n : nat => c n * (h + x) ^+ n.
suff Cc :
      lim (h^-1 *: (series (shx h - sx))) @[h --> 0^'] --> lim (series s).
  apply: cvg_sub0 Cc.
  apply/cvg_distP => eps eps_gt0 /=; rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0 -/sx -/(shx _); apply/eqP.
  have Cshx : cvg (series (shx h)).
    apply: cvg_series_Xn_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  rewrite limZr; last by apply: is_cvg_seriesB.
  by rewrite lim_seriesB.
apply: cvg_zero => /=.
suff Cc : 
  lim (series
       (fun n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1)))
   @[h --> 0^'] --> (0 : R).
  apply: cvg_sub0 Cc.
  apply/cvg_distP => eps eps_gt0 /=.
  rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0; apply/eqP.
  have Cs : cvg (series s) by apply: cvg_series_Xn_inside CdK _.
  have Cs1 := cvg_diffs_equiv (Cs).
  have Fs1 := diffs_equiv (Cs).
  set s1 := (fun i => _) in Cs1.
  have Cshx : cvg (series (shx h)).
    apply: cvg_series_Xn_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  have C1 := is_cvg_seriesB Cshx Csx.
  have Ckf := @is_cvg_seriesZr _ _ h^-1 C1.
  have Cu : 
   (series (h^-1 *: (shx h - sx)) - series s1) x0 @[x0 --> \oo] --> 
    lim (series (h^-1 *: (shx h - sx))) - lim (series s).
    by apply: cvgB.
  set w := fun n : nat => _.
  have -> : w = h^-1 *: (shx h - sx)  - s1.
    apply: funext => i /=; rcfE.
    rewrite /w /shx /sx /s1 /= mulrBr; congr (_ - _); last first.
      by rewrite mulrCA !mulrA.
    by rewrite -mulrBr [RHS]mulrCA [_^-1 * _]mulrC.
  rewrite [X in X h = _]/+%R /= [X in _ + X h = _]/-%R /=.
  have -> : series (h^-1 *: (shx h - sx) - s1) = 
            series (h^-1 *: (shx h - sx)) - (series s1).
    by apply/funext => i; rewrite /series /= sumrB.
  have -> : h^-1 *: series (shx h - sx) = series (h^-1 *: (shx h - sx)).
    by apply/funext => i; rewrite /series /= -scaler_sumr.
  by apply/sym_equal/cvg_lim.
pose r := (`|x| + `|K|) / 2.
have xLr : `|x| < r by rewrite ltr_pdivl_mulr // mulr2n mulrDr mulr1 ltr_add2l.
have rLx : r < `|K| by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 ltr_add2r.
have r_gt0 : 0 < r by apply: le_lt_trans xLr.
have rNZ : r != 0by case: ltrgt0P r_gt0.
apply: (@lim_cvg_to_0_linear
  (fun n => `|c n| * n%:R * (n.-1)%:R * r ^+ n.-2)
  (fun h n => c n * (((h + x) ^+ n - x ^+ n) / h -
                     n%:R * x ^+ n.-1))
  (r - `|x|)); first by rewrite subr_gt0.
- have : cvg (series (fun n => `|diffs (diffs c) n| * r ^+ n)).
    apply: cvg_series_Xn_inside_norm CddK _.
    by rewrite ger0_norm // ltW // (le_lt_trans _ xLr).
  have -> : (fun n => `|diffs (diffs c) n| * r ^+ n) = 
            (fun n => diffs (diffs (fun m => `|c m|)) n * r ^+ n).
    apply/funext => i.
    by rewrite /diffs !normrM !mulrA ger0_norm // ger0_norm.
  move=> /cvg_diffs_equiv.
  rewrite /diffs.
  have -> :
         (fun n => n%:R * ((n.+1)%:R * `|c n.+1|) * r ^+ n.-1) =
         (fun n => diffs (fun m => (m.-1)%:R * `|c m| * r^-1) n * r ^+ n).
    apply/funext => n.
    rewrite /diffs /= mulrA.
    case: n => [|n /=]; first by rewrite !(mul0r, mulr0).
    rewrite [_%:R *_]mulrC !mulrA -[RHS]mulrA exprS.
    by rewrite [_^-1 * _]mulrA mulVf ?mul1r.
  move/cvg_diffs_equiv.
  have ->// : (fun n : nat => n%:R * (n.-1%:R * `|c n| / r) * r ^+ n.-1) =
              (fun n : nat => `|c n| * n%:R * n.-1%:R * r ^+ n.-2).
  apply/funext => [] [|[|i]]; rewrite ?(mul0r, mulr0) //=.
  rewrite mulrA -mulrA exprS [_^-1 * _]mulrA mulVf //.
  rewrite mul1r !mulrA; congr (_ * _).
  by rewrite mulrC mulrA.
move=> h /andP[h_gt0 hLrBx] n.
have hNZ : h != 0 by rewrite -normr_gt0.
rewrite normrM -!mulrA ler_wpmul2l //.
apply: le_trans (termdiff_P3 _ hNZ (ltW xLr) _) _; last by rewrite !mulrA.
apply: le_trans (ler_norm_add _ _) _.
by rewrite -(subrK `|x| r) ler_add2r ltW.
Grab Existential Variables. all: end_near. Qed.

End TermDiff.


(******************************************************************************)
(*  Exponentiel series                                                        *)
(******************************************************************************)

Section fact_facts.

Local Open Scope nat_scope.

Lemma leq_fact n : n <= n`!.
Proof.
by case: n => // n;  rewrite dvdn_leq ?fact_gt0 // dvdn_fact ?andTb.
Qed.

Lemma prod_rev n m :
  \prod_(0 <= k < n - m) (n - k) = \prod_(m.+1 <= k < n.+1) k.
Proof.
rewrite [in RHS]big_nat_rev /= -{1}(add0n m.+1) big_addn subSS.
by apply eq_bigr => i _; rewrite addnS subSS addnC subnDr.
Qed.

Lemma fact_split n m : m <= n -> n`! = \prod_(0 <= k < n - m) (n - k) * m`!.
Proof.
move=> ?; rewrite [in RHS]fact_prod mulnC prod_rev -big_cat [in RHS]/index_iota.
rewrite subn1 -iota_add subSS addnBCA // subnn addn0 [in LHS]fact_prod.
by rewrite [in RHS](_ : n = n.+1 - 1) // subn1.
Qed.

End fact_facts.

Section exponential_series.

Variable R : realType.
Implicit Types x : R.

Import Order.TTheory.
Import Num.Theory.
Import GRing.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition exp_coeff x := [sequence x ^+ n / n`!%:R]_n.

Local Notation exp := exp_coeff.

Lemma exp_coeff_ge0 x n : 0 <= x -> 0 <= exp x n.
Proof. by move=> x0; rewrite /exp divr_ge0 // ?exprn_ge0 // ler0n. Qed.

Lemma series_exp_coeff0 n : series (exp 0) n.+1 = 1.
Proof.
rewrite /series /= big_nat_recl //= /exp /= expr0n divr1 big1 ?addr0 // => i _.
by rewrite expr0n mul0r.
Qed.

Section exponential_series_cvg.

Variable x : R.
Hypothesis x0 : 0 < x.

Let S0 N n := (N ^ N)%:R * \sum_(N.+1 <= i < n) (x / N%:R) ^+ i.

Let is_cvg_S0 N : x < N%:R -> cvg (S0 N).
Proof.
move=> xN; apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series; rewrite normrM normfV.
by rewrite ltr_pdivr_mulr ?mul1r !ger0_norm // 1?ltW // (lt_trans x0).
Qed.

Let S0_ge0 N n : 0 <= S0 N n.
Proof.
rewrite mulr_ge0 // ?ler0n //; apply sumr_ge0 => i _.
by rewrite exprn_ge0 // divr_ge0 // ?ler0n // ltW.
Qed.

Let S0_sup N n : x < N%:R -> S0 N n <= sup [set of S0 N].
Proof.
move=> xN; apply/sup_upper_bound; [split; [by exists (S0 N n), n|]|by exists n].
rewrite (_ : [set of _] = [set `|S0 N n0| | n0 in setT]).
  by apply: cvg_has_ub (is_cvg_S0 xN).
by rewrite predeqE=> y; split=> -[z _ <-]; exists z; rewrite ?ger0_norm ?S0_ge0.
Qed.

Let S1 N n := \sum_(N.+1 <= i < n) exp x i.

Lemma incr_S1 N : nondecreasing_seq (S1 N).
Proof.
apply/nondecreasing_seqP => n; rewrite /S1.
have [nN|Nn] := leqP n N; first by rewrite !big_geq // (leq_trans nN).
by rewrite big_nat_recr//= ler_addl exp_coeff_ge0 // ltW.
Qed.

Let S1_sup N : x < N%:R -> has_ubound [set of S1 N].
Proof.
move=> xN; exists (sup [set of S0 N]) => _ [n _ <-].
rewrite (le_trans _ (S0_sup n xN)) // /S0 big_distrr /=.
have N_gt0 := lt_trans x0 xN.
apply ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pmul2l ?exprn_gt0 // (@le_trans _ _ 1) //.
    by rewrite invf_le1 ?ler1n ?ltr0n // fact_gt0.
  rewrite natrX -expfB_cond ?(negPf (lt0r_neq0 N_gt0)) //.
  by rewrite exprn_ege1 // ler1n; case: (N) xN x0; case: ltrgt0P.
rewrite /exp expr_div_n /= (fact_split Ni) mulrCA.
rewrite ler_pmul2l ?exprn_gt0 // natrX -invf_div -expfB //.
rewrite lef_pinv ?qualifE; last 2 first.
- rewrite ltr0n muln_gt0 fact_gt0 andbT.
  rewrite big_mkord prodn_gt0  // => j.
  by rewrite subn_gt0 (leq_trans (ltn_ord _) (leq_subr _ _)).
- by rewrite exprn_gt0.
rewrite prod_rev -natrX ler_nat -prod_nat_const_nat big_add1 /= big_ltn //.
rewrite mulnC leq_mul //; last by apply: leq_trans (leq_fact _).
rewrite -(subnK Ni); elim: (_ - _)%N => [|k IH]; first by rewrite !big_geq.
rewrite !addSn !big_nat_recr //= ?leq_mul ?leq_addl //.
by rewrite -addSn -addSnnS leq_addl.
Qed.

Lemma is_cvg_series_exp_coeff_pos : cvg (series (exp x)).
Proof.
rewrite /series; near \oo => N; have xN : x < N%:R; last first.
  rewrite -(@is_cvg_series_restrict N.+1).
  exact/(nondecreasing_is_cvg (incr_S1 N))/S1_sup.
near: N; exists (absz (floor x)).+1 => // m; rewrite /mkset -(@ler_nat R).
move/lt_le_trans => -> //; rewrite (lt_le_trans (lt_succ_Rfloor x)) // -addn1.
rewrite natrD (_ : 1%:R = 1%R) // ler_add2r RfloorE -(@gez0_abs (floor x)) //.
by rewrite floor_ge0// ltW.
Grab Existential Variables. all: end_near. Qed.

End exponential_series_cvg.

Lemma normed_series_exp_coeff x : [normed series (exp x)] = series (exp `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma is_cvg_series_exp_coeff x : cvg (series (exp x)).
Proof.
have [/eqP ->|x0] := boolP (x == 0).
  apply/cvg_ex; exists 1; apply/cvg_distP => // => _/posnumP[e].
  rewrite near_map; near=> n; have [m ->] : exists m, n = m.+1.
    by exists n.-1; rewrite prednK //; near: n; exists 1%N.
  by rewrite series_exp_coeff0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp_coeff.
by apply: is_cvg_series_exp_coeff_pos; rewrite normr_gt0.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_exp_coeff x : exp x --> (0 : R).
Proof. exact: (cvg_series_cvg_0 (@is_cvg_series_exp_coeff x)). Qed.

End exponential_series.

(******************************************************************************)
(*   Starting with the exponentiel function                                   *)
(******************************************************************************)


Section exp.

Variable R : realType.

Definition exp (x : R) : R := lim (series (exp_coeff x)).

Lemma exp0 : exp 0 = 1.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_ge1Dx x : 0 <= x -> 1 + x <= exp x.
Proof.
 move=> xP; rewrite /exp.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = lim (series (f x)).
  by apply/sym_equal/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => [] [|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_gt1 x : 0 < x  -> 1 < exp x.
Proof.
move=> xP.
apply: lt_le_trans (exp_ge1Dx (ltW xP)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.


Lemma exp_coeffE (x : R) : 
  exp_coeff x = (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /exp_coeff /= mulrC. Qed.

Lemma expE : 
  exp = fun x => lim (series (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n)).
Proof. by apply/funext => x; rewrite -exp_coeffE. Qed.

Lemma diffs_exp : 
  diffs (fun n => (n`!%:R)^-1) = (fun n => (n`!%:R)^-1 : R).
Proof.
by apply/funext => i; rewrite /diffs factS natrM invfM mulrA mulfV ?mul1r.
Qed.

Global Instance is_derive_exp x : is_derive x 1 exp (exp x).
Proof.
pose s1 n := diffs (fun n => n`!%:R^-1) n * x ^+ n.
rewrite expE /=.
rewrite (_ : (fun n => _) = s1); last first.
  by apply/funext => i; rewrite /s1 diffs_exp.
apply: (@termdiff _ _ (`|x| + 1)).
- rewrite -exp_coeffE; apply: is_cvg_series_exp_coeff.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite diffs_exp exp_coeffE.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite !diffs_exp exp_coeffE.
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Lemma derivable_exp x : derivable exp x 1.
Proof. by apply: ex_derive; apply: is_derive_exp. Qed.

Lemma continuous_exp : continuous exp.
Proof.
move=> x.
apply: differentiable_continuous.
by apply/derivable1_diffP/derivable_exp.
Qed.

Lemma expxDyMexpx x y : exp (x + y) * exp (- x) = exp y.
Proof.
apply: etrans (_ : exp(0 + y) * exp (- 0) = _); last first.
  by rewrite add0r oppr0 exp0 mulr1.
apply: (@is_derive_0_cst _ (fun x => exp (x + y) * exp (- x))) => x1.
have -> : 0 = exp (x1 + y) * (exp (-x1) * (- 1)) + 
              exp (- x1) * (exp (x1 + y) * (1 + 0)).
  by rewrite mulrN1 addr0 mulr1 mulrN addrC mulrC subrr.
apply: is_deriveM.
apply: is_derive1_chain.
apply: is_deriveN.
Qed.

Lemma expxMexpNx_1 x : exp x * exp (-x) = 1.
Proof. by rewrite -{1}[x]addr0 expxDyMexpx exp0. Qed.

Lemma exp_gt0 x : 0 < exp x.
Proof.
case: (ltrgt0P x) => [xP|xP|->]; first by apply: lt_trans (exp_gt1 xP).
  have F : 0 < exp (- x) by apply: lt_trans (exp_gt1 _); rewrite ?oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expxMexpNx_1.
by rewrite exp0.
Qed.

Lemma expV x : exp (-x) = (exp x)^-1.
Proof.
apply: (mulfI (lt0r_neq0 (exp_gt0 x))).
by rewrite expxMexpNx_1 mulfV // (lt0r_neq0 (exp_gt0 x)).
Qed.

Lemma expD x y : exp (x + y) = exp x * exp y.
Proof.
apply: (mulIf (lt0r_neq0 (exp_gt0 (- x)))).
rewrite expxDyMexpx expV [_ * exp y]mulrC mulfK //.
by case: ltrgt0P (exp_gt0 x).
Qed.

End exp.

Section CosSin.

Variable R : realType.

Definition sin_coeff (x : R) :=
   [sequence  (odd n)%:R * (-1) ^+ n.-1./2 * x ^+ n / n`!%:R]_n.

Lemma sin_coeffE (x : R) : 
  sin_coeff x = (fun n => (fun n => (odd n)%:R * (-1) ^+ n.-1./2 *
                                    (n`!%:R)^-1) n * x ^+ n).
Proof.
by apply/funext => i; rewrite /sin_coeff /= -!mulrA [_ / _]mulrC.
Qed.

Lemma is_cvg_series_sin_coeff x : cvg (series (sin_coeff x)).
Proof.
apply: normed_cvg.
apply: series_le_cvg; last by apply: (@is_cvg_series_exp_coeff _ `|x|).
- by move=> n; rewrite normr_ge0.
- by move=> n; rewrite divr_ge0 ?exprn_ge0 // ler0n.
move=> n /=.
rewrite /exp_coeff /sin_coeff /=.
rewrite !normrM normfV !normr_nat !normrX normrN normr1 expr1n mulr1.
case: odd; first by rewrite mul1r.
by rewrite !mul0r divr_ge0 ?exprn_ge0 // ler0n.
Qed.

Definition sin (x : R) : R := lim (series (sin_coeff x)).

Lemma sinE : 
  sin = fun x => 
    lim (series (fun n => 
                  (fun n => (odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1) n 
                  * x ^+ n)).
Proof. by apply/funext => x; rewrite -sin_coeffE. Qed.

Lemma diffs_sin : 
  diffs (fun n => (odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1) =
   (fun n => (~~(odd n))%:R * (-1) ^+ n./2 * (n`!%:R)^-1 : R).
Proof.
apply/funext => i.
rewrite /diffs /= factS natrM invfM.
by rewrite [_.+1%:R * _]mulrC -!mulrA [_.+1%:R^-1 * _]mulrC mulfK.
Qed.

Lemma series_sin_coeff0 n : series (sin_coeff 0) n.+1 = 0.
Proof.
rewrite /series /= big_nat_recl //= /sin_coeff /= expr0n divr1 !mulr1.
by rewrite big1 ?addr0 // => i _; rewrite expr0n !(mul0r, mulr0).
Qed.

Lemma sin0 : sin 0 = 0.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_sin_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /sin_coeff /= expr0n !(mulr0, mul0r).
Grab Existential Variables. all: end_near. 
Qed.

Definition cos_coeff (x : R) :=
   [sequence  (~~(odd n))%:R * (-1)^n./2 * x ^+ n / n`!%:R]_n.

Lemma cos_coeffE (x : R) : 
  cos_coeff x = (fun n => (fun n => (~~(odd n))%:R * (-1) ^+ n./2 *
                                    (n`!%:R)^-1) n * x ^+ n).
Proof.
by apply/funext => i; rewrite /cos_coeff /= -!mulrA [_ / _]mulrC.
Qed.

Lemma is_cvg_series_cos_coeff x : cvg (series (cos_coeff x)).
Proof.
apply: normed_cvg.
apply: series_le_cvg; last by apply: (@is_cvg_series_exp_coeff _ `|x|).
- by move=> n; rewrite normr_ge0.
- by move=> n; rewrite divr_ge0 ?exprn_ge0 // ler0n.
move=> n /=.
rewrite /exp_coeff /cos_coeff /=.
rewrite !normrM normfV !normr_nat !normrX normrN normr1 expr1n mulr1.
case: odd; last by rewrite mul1r.
by rewrite !mul0r divr_ge0 ?exprn_ge0 // ler0n.
Qed.

Definition cos (x : R) : R := lim (series (cos_coeff x)).

Lemma cosE : 
  cos = fun x => 
    lim (series (fun n => 
                  (fun n => (~~(odd n))%:R * (-1)^+ n./2 * (n`!%:R)^-1) n 
                  * x ^+ n)).
Proof. by apply/funext => x; rewrite -cos_coeffE. Qed.

Lemma diffs_cos : 
  diffs (fun n => (~~(odd n))%:R * (-1) ^+ n./2 * (n`!%:R)^-1) =
  (fun n => - ((odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1): R).
Proof.
apply/funext => [] [|i] /=.
  by rewrite /diffs /= !mul0r mulr0 oppr0.
rewrite /diffs /= negbK exprS mulN1r !(mulNr, mulrN).
rewrite  factS natrM invfM.
by rewrite [_.+1%:R * _]mulrC -!mulrA [_.+1%:R^-1 * _]mulrC mulfK.
Qed.

Lemma series_cos_coeff0 n : series (cos_coeff 0) n.+1 = 1.
Proof.
rewrite /series /= big_nat_recl //= /cos_coeff /= expr0n divr1 !mulr1.
by rewrite big1 ?addr0 // => i _; rewrite expr0n !(mul0r, mulr0).
Qed.

Lemma cos0 : cos 0 = 1.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_cos_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /cos_coeff /= expr0n !(mulr0, mul0r).
Grab Existential Variables. all: end_near. 
Qed.

Global Instance is_derive_sin x : is_derive x 1 sin (cos x).
Proof.
rewrite sinE /=.
pose s : R^nat := fun n => (odd n)%:R * (-1) ^+ (n.-1)./2 / n`!%:R.
pose s1 n := diffs s n * x ^+ n.
rewrite cosE /=.
rewrite (_ : (fun n => _) = s1); last first.
  by apply/funext => i; rewrite /s1 diffs_sin.
apply: (@termdiff _ _ (`|x| + 1)).
- rewrite -sin_coeffE; apply: is_cvg_series_sin_coeff.
- rewrite (_ : (fun n : nat => _) = cos_coeff (`|x| + 1)).
    by apply: is_cvg_series_cos_coeff.
  by apply/funext => i; rewrite diffs_sin cos_coeffE.
- rewrite (_ : (fun n : nat => _) = - sin_coeff (`|x| + 1)).
  apply: is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  apply/funext => i.
  by rewrite diffs_sin diffs_cos sin_coeffE {1}[in RHS]/-%R /= !mulNr.
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Global Instance is_derive_cos x : is_derive x 1 cos (- (sin x)).
Proof.
rewrite cosE /=.
pose s : R^nat := fun n => (~~ odd n)%:R * (-1) ^+ n./2 / n`!%:R.
pose s1 n := diffs s n * x ^+ n.
rewrite sinE /=.
rewrite (_ : (fun n => _) = - s1); last first.
  by apply/funext => i; rewrite /s1 diffs_cos {1}[in RHS]/-%R /= mulNr opprK.
rewrite lim_seriesN ?opprK; last first.
  rewrite (_ : s1 = - sin_coeff x).
    apply: is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  apply/funext => i.
  by rewrite /s1 diffs_cos sin_coeffE {1}[in RHS]/-%R /= mulNr.
apply: (@termdiff _ _ (`|x| + 1)).
- by rewrite -cos_coeffE; apply: is_cvg_series_cos_coeff.
- rewrite (_ : (fun n : nat => _) = - sin_coeff (`|x| + 1)).
    apply: is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  by apply/funext => i; rewrite diffs_cos sin_coeffE {1}[in RHS]/-%R /= mulNr.
- rewrite (_ : (fun n : nat => _) = - cos_coeff (`|x| + 1)).
  apply: is_cvg_seriesN.
    by apply: is_cvg_series_cos_coeff.
  apply/funext => i.
  rewrite diffs_cos.
  pose f n : R := ((odd n)%:R * (-1) ^+ (n.-1)./2 / n`!%:R) .
  rewrite (_ : (fun n => _) = - f); last first.
    by apply/funext=> j /=; rewrite [in RHS]/-%R.
  rewrite diffsN diffs_sin cos_coeffE {1}[in LHS]/-%R {1}[in RHS]/-%R /=.
  by rewrite mulNr. 
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Lemma cos2Dsin2 a : (cos a) ^+ 2 + (sin a) ^+ 2 = 1.
Proof.
apply: etrans (_ : (cos 0) ^+ 2 + (sin 0) ^+ 2 = 1); last first.
  by rewrite cos0 sin0 expr1n expr0n addr0. 
apply: (@is_derive_0_cst _ (fun x => (cos x) ^ 2 + (sin x)^2)) => x1.
have -> : 0 = (2 * cos x1) * (- sin x1) + (2 * sin x1) * cos x1.
  by rewrite ?expr1 mulrN mulrAC addrC subrr.
apply: is_deriveD.
apply: (@is_deriveX _ _ cos 1).
apply: (@is_deriveX _ _ sin 1).
Qed.

Fact sinD_aux x y :
  (sin (x + y) - (sin x * cos y + cos x * sin y)) ^+ 2 +
  (cos (x + y) - (cos x * cos y - sin x * sin y)) ^+ 2 = 0.
Proof.
pose f := (sin \o +%R^~ y - (sin * cst (cos y) + cos * cst (sin y)))^+2 +
          (cos \o +%R^~ y - (cos * cst (cos y) - sin * cst (sin y)))^+2.
apply: etrans (_ : f x = 0); first by [].
apply: etrans (_ : f 0 = 0); last first.
  rewrite /f /cst; rcfE.
  by rewrite cos0 sin0 !(mul1r, mul0r, add0r, subr0, subrr).
apply: is_derive_0_cst => {}x.
have F x1 y1 : x1 = y1 -> is_derive x 1 f x1 -> is_derive x 1 f y1.
  by move->.
eapply F; last first.
do 7 (apply is_deriveB || apply is_deriveD || apply is_deriveX ||
      apply is_deriveM || apply is_derive1_chain || apply is_derive1_id || 
      apply is_derive_sin || apply is_derive_cos || apply is_derive_cst).
rewrite /cst; rcfE.
rewrite !(scaler0, add0r, addr0, mulr1, expr1) mulr2n.
nsatz.
Qed.

Lemma sinD x y : sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
have /eqP := sinD_aux x y.
rewrite paddr_eq0 => [/andP[]||]; try by apply: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma cosD x y : cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
have /eqP := sinD_aux x y.
rewrite paddr_eq0 => [/andP[_]||]; try by apply: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma sin2cos2 a : sin a ^+ 2 = 1 - cos a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym addrC -subr_eq => /eqP. Qed.

Lemma cos2sin2 a : cos a ^+ 2 = 1 - sin a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym -subr_eq => /eqP. Qed.

Lemma sin_mulr2n a : sin (a *+ 2) = (cos a * sin a) *+ 2.
Proof. by rewrite mulr2n sinD mulrC -mulr2n. Qed.

Lemma sinN_aux x :
    (sin (- x ) + (sin x)) ^+ 2 + (cos (- x) - (cos x)) ^+ 2 = 0.
Proof.
pose f := (sin \o -%R + sin)^+2 + (cos \o -%R - cos )^+2.
apply: etrans (_ : f x = 0); first by [].
apply: etrans (_ : f 0 = 0); last first.
  rewrite /f /cst; rcfE.
  by rewrite oppr0 cos0 sin0 !(mul1r, mul0r, add0r, subr0, subrr).
apply: is_derive_0_cst => {}x.
have F x1 y1 : x1 = y1 -> is_derive x 1 f x1 -> is_derive x 1 f y1.
  by move->.
eapply F; last first.
do 8 (apply is_deriveB || apply is_deriveD || apply is_deriveX ||
      apply is_deriveM || apply is_derive1_chain || apply is_derive1_id || 
      apply is_derive_sin || apply is_derive_cos || apply is_derive_cst ||
      apply is_deriveN).
- by apply: is_deriveN; apply: is_derive1_id.
- by apply: is_derive1_id.
- by apply: is_deriveN; apply: is_derive1_id.
- by apply: is_derive1_id.
rewrite /cst; rcfE.
rewrite !(scaler0, add0r, addr0, mulr1, expr1) mulr2n.
nsatz.
Qed.

Lemma sinN a : sin (- a) = - sin a.
Proof.
have /eqP := sinN_aux a.
rewrite paddr_eq0 => [/andP[]||]; try by apply: sqr_ge0.
by rewrite sqrf_eq0 addr_eq0 => /eqP.
Qed.

Lemma cosN a : cos (- a) = cos a.
Proof.
have /eqP := sinN_aux a.
rewrite paddr_eq0 => [/andP[_]||]; try by apply: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma cosB a b : cos (a - b) = cos a * cos b + sin a * sin b.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sinB a b : sin (a - b) = sin a * cos b - cos a * sin b.
Proof. by rewrite sinD cosN sinN mulrN. Qed.

End CosSin.

Section Pi.

Variable R : realType.

Definition pi :=
  if pselect (exists x : R, 0 <= x <= 2 /\ cos x = 0) is left e 
  then (projT1 (cid e)) *+ 2 else 0.

End Pi.
