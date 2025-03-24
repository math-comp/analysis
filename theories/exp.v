(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import mathcomp_extra reals ereal interval_inference.
From mathcomp Require Import topology tvs normedtype landau sequences derive.
From mathcomp Require Import realfun interval_inference convex.

(**md**************************************************************************)
(* # Theory of exponential/logarithm functions                                *)
(*                                                                            *)
(* This file defines exponential and logarithm functions and develops their   *)
(* theory.                                                                    *)
(*                                                                            *)
(* ## Differentiability of series (Section PseriesDiff)                       *)
(*                                                                            *)
(* This formalization is inspired by HOL-Light (transc.ml). This part is      *)
(* temporary: it should be subsumed by a proper theory of power series.       *)
(* ```                                                                        *)
(*         pseries f x == [series f n * x ^ n]_n                              *)
(*   pseries_diffs f i == (i + 1) * f (i + 1)                                 *)
(*                                                                            *)
(*             expeR x == extended real number-valued exponential function    *)
(*                ln x == the natural logarithm                               *)
(*              s `^ r == power function, in ring_scope (assumes s >= 0)      *)
(*              e `^ r == power function, in ereal_scope (assumes e >= 0)     *)
(*          riemannR a == sequence n |-> 1 / (n.+1) `^ a where a has a type   *)
(*                        of type realType                                    *)
(*       e `^?(r +? s) == validity condition for the distributivity of        *)
(*                        the power of the addition, in ereal_scope           *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "x '`^?' ( r +? s )"
 (format "x  '`^?' ( r  +?  s )", r at next level, at level 11) .

(* PR to mathcomp in progress *)
Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE/=. Qed.
#[global] Hint Extern 0 (is_true (@Num.norm _ _ _ \is Num.nneg)) =>
  solve [apply: normr_nneg] : core.
(* /PR to mathcomp in progress *)

Section PseriesDiff.

Variable R : realType.

Definition pseries f (x : R) := [series f i * x ^+ i]_i.

Fact is_cvg_pseries_inside_norm f (x z : R) :
    cvgn (pseries f x) -> `|z| < `|x| ->
  cvgn (pseries (fun i => `|f i|) z).
Proof.
move=> Cx zLx; have [K [Kreal Kf]] := cvg_series_bounded Cx.
have Kzxn n : 0 <= `|K + 1| * `|z ^+ n| / `|x ^+ n| by rewrite !mulr_ge0.
apply: normed_cvg.
apply: series_le_cvg Kzxn _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pM || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply Kf => //; rewrite (lt_le_trans _ (ler_norm _))// ltrDl.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivrMr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric `|K + 1| `|z / x|); last first.
  by apply/funext => i /=; rewrite normrM exprMn mulrA normfV !normrX exprVn.
by apply: is_cvg_geometric_series; rewrite normr_id.
Qed.

Fact is_cvg_pseries_inside f (x z : R) :
  cvgn (pseries f x) -> `|z| < `|x| -> cvgn (pseries f z).
Proof.
move=> Cx zLx.
apply: normed_cvg; rewrite /normed_series_of /=.
rewrite (_ : (fun _ => _) = (fun i => `|f i| * `|z| ^+ i)); last first.
  by apply/funext => i; rewrite normrM normrX.
by apply: is_cvg_pseries_inside_norm Cx _; rewrite normr_id.
Qed.

Definition pseries_diffs (f : nat -> R) i := i.+1%:R * f i.+1.

Lemma pseries_diffsN (f : nat -> R) :  pseries_diffs (- f) = -(pseries_diffs f).
Proof. by apply/funext => i; rewrite /pseries_diffs /= -mulrN. Qed.

Lemma pseries_diffs_inv_fact :
  pseries_diffs (fun n => (n`!%:R)^-1) = (fun n => (n`!%:R)^-1 : R).
Proof.
apply/funext => i.
by rewrite /pseries_diffs factS natrM invfM mulrA mulfV ?mul1r.
Qed.

Lemma pseries_diffs_sumE n f x :
  \sum_(0 <= i < n)  pseries_diffs f i * x ^+ i =
  (\sum_(0 <= i < n) i%:R * f i * x ^+ i.-1) + n%:R * f n * x ^+ n.-1.
Proof.
case: n => [|n]; first by rewrite !big_nil !mul0r add0r.
under eq_bigr do unfold pseries_diffs.
by rewrite big_nat_recr //= big_nat_recl //= !mul0r add0r.
Qed.

Lemma pseries_diffs_equiv f x :
  let s i := i%:R * f i * x ^+ i.-1 in
  cvgn (pseries (pseries_diffs f) x) ->
  series s @ \oo --> limn (pseries (pseries_diffs f) x).
Proof.
move=> s Cx; rewrite -[lim _]subr0.
rewrite /pseries/= [X in X @ \oo --> _]/series /=.
rewrite [X in X @ \oo --> _](_ : _ = (fun n => \sum_(0 <= i < n)
    pseries_diffs f i * x ^+ i - n%:R * f n * x ^+ n.-1)); last first.
  by rewrite funeqE => n; rewrite pseries_diffs_sumE addrK.
by apply: cvgB => //; rewrite -cvg_shiftS; exact: cvg_series_cvg_0.
Qed.

Lemma is_cvg_pseries_diffs_equiv f x :
    cvgn (pseries (pseries_diffs f) x) ->
  cvgn ([series i%:R * f i * x ^+ i.-1]_i).
Proof.
by by move=> Cx; have := pseries_diffs_equiv Cx; move/(cvg_lim _) => -> //.
Qed.

Let pseries_diffs_P1 m (z h : R) :
  \sum_(0 <= i < m) ((h + z) ^+ (m - i) * z ^+ i - z ^+ m) =
  \sum_(0 <= i < m) z ^+ i * ((h + z) ^+ (m - i) - z ^+ (m - i)).
Proof.
rewrite !big_mkord; apply: eq_bigr => i _.
by rewrite mulrDr mulrN -exprD mulrC addnC subnK // ltnW.
Qed.

Let pseries_diffs_P2 n (z h : R) :
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
rewrite -(big_mkord xpredT (fun i => (h + z) ^+ (n - i) * z ^+ i)).
rewrite big_nat_recr //= subnn expr0 -addrA -mulrBl.
rewrite -nat1r opprD addrA subrr sub0r mulNr.
rewrite mulr_natl -[in X in _ *+ X](subn0 n) -sumr_const_nat -sumrB.
rewrite pseries_diffs_P1 mulr_sumr !big_mkord; apply: eq_bigr => i _.
rewrite mulrCA; congr (_ * _).
rewrite subrXX addrK big_nat_rev /= big_mkord; congr (_ * _).
by apply: eq_bigr => k _; rewrite -!predn_sub subKn // -subnS.
Qed.

Let pseries_diffs_P3 (z h : R) n K :
  h != 0 -> `|z| <= K -> `|h + z| <= K ->
    `|((h +z) ^+ n - z ^+ n) / h - n%:R * z ^+ n.-1|
      <= n%:R * n.-1%:R * K ^+ n.-2 * `|h|.
Proof.
move=> hNZ zLK zhLk.
rewrite pseries_diffs_P2// normrM mulrC.
rewrite ler_pM2r ?normr_gt0//.
rewrite (le_trans (ler_norm_sum _ _ _))//.
rewrite -mulrA mulrC -mulrA mulr_natl -[X in _ *+ X]subn0 -sumr_const_nat.
apply ler_sum_nat => i /=.
case: n => //= n ni.
rewrite normrM.
pose d := (n.-1 - i)%nat.
rewrite -[(n - i)%nat]prednK ?subn_gt0// predn_sub -/d.
rewrite -(subnK (_ : i <= n.-1)%nat) -/d; last first.
  by rewrite -ltnS prednK// (leq_ltn_trans _ ni).
rewrite addnC exprD mulrAC -mulrA.
apply: ler_pM => //.
  by rewrite normrX lerXn2r// qualifE/= (le_trans _ zLK).
apply: le_trans (_ : d.+1%:R * K ^+ d <= _); last first.
  rewrite ler_wpM2r //; first by rewrite exprn_ge0 // (le_trans _ zLK).
  by rewrite ler_nat ltnS /d -subn1 -subnDA leq_subr.
rewrite (le_trans (ler_norm_sum _ _ _))//.
rewrite mulr_natl -[X in _ *+ X]subn0 -sumr_const_nat ler_sum_nat//= => j jd1.
rewrite -[in leRHS](subnK (_ : j <= d)%nat) -1?ltnS // addnC exprD normrM.
by rewrite ler_pM// normrX lerXn2r// qualifE/= (le_trans _ zLK).
Qed.

Lemma pseries_snd_diffs (c : R^nat) K x :
  cvgn (pseries c K) ->
  cvgn (pseries (pseries_diffs c) K) ->
  cvgn (pseries (pseries_diffs (pseries_diffs c)) K) ->
  `|x| < `|K| ->
  is_derive x (1 : R)
    (fun x => limn (pseries c x))
    (limn (pseries (pseries_diffs c) x)).
Proof.
move=> Ck CdK CddK xLK; rewrite /pseries.
set s := (fun n : nat => _); set (f := fun x0 => _).
suff hfxs : h^-1 *: (f (h + x) - f x) @[h --> 0^'] --> limn (series s).
  have F : f^`() x = limn (series s) by apply: cvg_lim hfxs.
  have Df : derivable f x 1.
    move: hfxs; rewrite /derivable [X in X @ 0^'](_ : _ =
        (fun h => h^-1 *: (f (h%:A + x) - f x))) /=; last first.
      by apply/funext => i //=; rewrite [i%:A]mulr1.
    by move=> /(cvg_lim _) -> //.
  by constructor; [exact: Df|rewrite -derive1E].
pose sx := fun n : nat => c n * x ^+ n.
have Csx : cvgn (pseries c x) by apply: is_cvg_pseries_inside Ck _.
pose shx := fun h (n : nat) => c n * (h + x) ^+ n.
suff Cc : limn (h^-1 *: (series (shx h - sx))) @[h --> 0^'] --> limn (series s).
  apply: cvg_sub0 Cc.
  apply/cvgrPdist_lt => eps eps_gt0 /=.
  near=> h; rewrite sub0r normrN /=.
  rewrite (le_lt_trans _ eps_gt0)//.
  rewrite normr_le0 subr_eq0 -/sx -/(shx _); apply/eqP.
  have Cshx' : cvgn (series (shx h)).
    apply: is_cvg_pseries_inside Ck _.
    rewrite (le_lt_trans (ler_normD _ _))// -(subrK  `|x| `|K|) ltrD2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2%:R) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    rewrite (lt_le_trans H)// ler_pdivrMr // mulr2n mulrDr mulr1.
    by rewrite ler_wpDr // subr_ge0 ltW.
  rewrite limZr; last exact/is_cvg_seriesB/Csx.
  by rewrite lim_seriesB; last exact: Csx.
apply: cvg_zero => /=.
suff Cc : limn
    (series (fun n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1)))
    @[h --> 0^'] --> 0.
  apply: cvg_sub0 Cc.
  apply/cvgrPdist_lt => eps eps_gt0 /=.
  near=> h; rewrite sub0r normrN /=.
  rewrite (le_lt_trans _ eps_gt0)// normr_le0 subr_eq0; apply/eqP.
  have Cs : cvgn (series s) by apply: is_cvg_pseries_inside CdK _.
  have Cs1 := is_cvg_pseries_diffs_equiv Cs.
  have Fs1 := pseries_diffs_equiv Cs.
  set s1 := (fun i => _) in Cs1.
  have Cshx : cvgn (series (shx h)).
    apply: is_cvg_pseries_inside Ck _.
    rewrite (le_lt_trans (ler_normD _ _))// -(subrK  `|x| `|K|) ltrD2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) / 2%:R) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    rewrite (lt_le_trans H)// ler_pdivrMr // mulr2n mulrDr mulr1.
    by rewrite ler_wpDr // subr_ge0 ltW.
  have C1 := is_cvg_seriesB Cshx Csx.
  have Ckf := @is_cvg_seriesZ _ _ h^-1 C1.
  have Cu : (series (h^-1 *: (shx h - sx)) - series s1) x0 @[x0 --> \oo] -->
      limn (series (h^-1 *: (shx h - sx))) - limn (series s).
    exact: cvgB Ckf Fs1.
  set w := (fun n : nat => _ in RHS).
  have -> : w = h^-1 *: (shx h - sx)  - s1.
    apply: funext => i; rewrite !fctE.
    rewrite /w /shx /sx /s1 /= mulrBr; congr (_ - _); last first.
      by rewrite mulrCA !mulrA.
    by rewrite -mulrBr [RHS]mulrCA [_^-1 * _]mulrC.
  rewrite [X in X h = _]/+%R /= [X in _ + X h = _]/-%R /=.
  have -> : series (h^-1 *: (shx h - sx) - s1) =
           series (h^-1 *: (shx h - sx)) - (series s1).
    by apply/funext => i; rewrite /series /= sumrB.
  have -> : h^-1 *: series (shx h - sx) = series (h^-1 *: (shx h - sx)).
    by apply/funext => i; rewrite /series /= -scaler_sumr.
  exact/esym/cvg_lim.
pose r := (`|x| + `|K|) / 2.
have xLr : `|x| < r by rewrite ltr_pdivlMr // mulrDr mulr1 ltrD2l.
have rLx : r < `|K| by rewrite ltr_pdivrMr // mulrDr mulr1 ltrD2r.
have r_gt0 : 0 < r by apply: le_lt_trans xLr.
have rNZ : r != 0by case: ltrgt0P r_gt0.
apply: (@lim_cvg_to_0_linear _
  (fun n => `|c n| * n%:R * (n.-1)%:R * r ^+ n.-2)
  (fun h n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1))
  (r - `|x|)); first by rewrite subr_gt0.
- have : cvgn ([series `|pseries_diffs (pseries_diffs c) n| * r ^+ n]_n).
    apply: is_cvg_pseries_inside_norm CddK _.
    by rewrite ger0_norm // ltW // (le_lt_trans _ xLr).
  have -> : (fun n => `|pseries_diffs (pseries_diffs c) n| * r ^+ n) =
            (fun n => pseries_diffs (pseries_diffs
                                      (fun m => `|c m|)) n * r ^+ n).
    apply/funext => i.
    by rewrite /pseries_diffs !normrM !mulrA ger0_norm // ger0_norm.
  move=> /is_cvg_pseries_diffs_equiv.
  rewrite /pseries_diffs.
  have -> : (fun n => n%:R * ((n.+1)%:R * `|c n.+1|) * r ^+ n.-1) =
           (fun n => pseries_diffs
             (fun m => (m.-1)%:R * `|c m| * r^-1) n * r ^+ n).
    apply/funext => n.
    rewrite /pseries_diffs /= mulrA.
    case: n => [|n /=]; first by rewrite !(mul0r, mulr0).
    rewrite [_%:R *_]mulrC !mulrA -[RHS]mulrA exprS.
    by rewrite [_^-1 * _]mulrA mulVf ?mul1r.
  move/is_cvg_pseries_diffs_equiv.
  have ->// : (fun n => n%:R * (n.-1%:R * `|c n| / r) * r ^+ n.-1) =
              (fun n => `|c n| * n%:R * n.-1%:R * r ^+ n.-2).
  apply/funext => [] [|[|i]]; rewrite ?(mul0r, mulr0) //=.
  rewrite mulrA -mulrA exprS [_^-1 * _]mulrA mulVf //.
  rewrite mul1r !mulrA; congr (_ * _).
  by rewrite mulrC mulrA.
- move=> h /andP[h_gt0 hLrBx] n.
  rewrite normrM -!mulrA ler_wpM2l //.
  rewrite (le_trans (pseries_diffs_P3 _ _ (ltW xLr) _))// ?mulrA -?normr_gt0//.
  by rewrite (le_trans (ler_normD _ _))// -(subrK `|x| r) lerD2r ltW.
Unshelve. all: by end_near.
Qed.

End PseriesDiff.

Section expR.
Variable R : realType.
Implicit Types x : R.

Lemma expR0 : expR 0 = 1 :> R.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Unshelve. all: by end_near. Qed.

Local Lemma expR_ge1Dx_subproof x : 0 <= x -> 1 + x <= expR x.
Proof.
move=> x_ge0; rewrite /expR.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = limn (series (f x)).
  by apply/esym/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => -[|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Unshelve. all: by end_near. Qed.

Lemma exp_coeffE x : exp_coeff x = (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /exp_coeff /= mulrC. Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma expRE :
  expR = fun x => limn (pseries (fun n => (fun n => (n`!%:R)^-1) n) x).
Proof. by apply/funext => x; rewrite /pseries -exp_coeffE. Qed.

Global Instance is_derive_expR x : is_derive x 1 expR (expR x).
Proof.
pose s1 n := pseries_diffs (fun n => n`!%:R^-1) n * x ^+ n.
rewrite expRE /= /pseries (_ : (fun _ => _) = s1); last first.
  by apply/funext => i; rewrite /s1 pseries_diffs_inv_fact.
apply: (@pseries_snd_diffs _ _ (`|x| + 1)); rewrite /pseries.
- by rewrite -exp_coeffE; apply: is_cvg_series_exp_coeff.
- rewrite (_ : (fun _ => _) = exp_coeff (`|x| + 1)).
    exact: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite pseries_diffs_inv_fact exp_coeffE.
- rewrite (_ : (fun _ => _) = exp_coeff (`|x| + 1)).
    exact: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite !pseries_diffs_inv_fact exp_coeffE.
by rewrite [ltRHS]ger0_norm// addrC -subr_gt0 addrK.
Qed.

Lemma derivable_expR x : derivable expR x 1.
Proof. by apply: ex_derive; apply: is_derive_exp. Qed.

Lemma derive_expR : 'D_1 expR = expR :> (R -> R).
Proof. by apply/funext => r /=; rewrite derive_val. Qed.

Lemma continuous_expR : continuous (@expR R).
Proof.
by move=> x; exact/differentiable_continuous/derivable1_diffP/derivable_expR.
Qed.

Lemma expRxDyMexpx x y : expR (x + y) * expR (- x) = expR y.
Proof.
set v := LHS; pattern x in v; move: @v; set f := (X in let _ := X x in _) => /=.
apply: etrans (_ : f x = f 0) _; last by rewrite /f add0r oppr0 expR0 mulr1.
apply: is_derive_0_is_cst => x1.
apply: trigger_derive.
by rewrite /GRing.scale /= mulrN1 addr0 mulr1 mulrN addrC mulrC subrr.
Qed.

Lemma expRxMexpNx_1 x : expR x * expR (- x) = 1.
Proof. by rewrite -[X in _ X * _ = _]addr0 expRxDyMexpx expR0. Qed.

Lemma pexpR_gt1 x : 0 < x -> 1 < expR x.
Proof.
by move=> x0; rewrite (lt_le_trans _ (expR_ge1Dx_subproof (ltW x0)))// ltrDl.
Qed.

Lemma expR_gt0 x : 0 < expR x.
Proof.
case: (ltrgt0P x) => [x_gt0|x_gt0|->]; last by rewrite expR0.
- exact: lt_trans (pexpR_gt1 x_gt0).
- have F : 0 < expR (- x) by rewrite (lt_trans _ (pexpR_gt1 _))// oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expRxMexpNx_1.
Qed.

Lemma expR_ge0 x : 0 <= expR x. Proof. by rewrite ltW// expR_gt0. Qed.

Lemma expR_eq0 x : (expR x == 0) = false.
Proof. by rewrite gt_eqF ?expR_gt0. Qed.

Lemma expRN x : expR (- x) = (expR x)^-1.
Proof.
apply: (mulfI (lt0r_neq0 (expR_gt0 x))).
by rewrite expRxMexpNx_1 mulfV // (lt0r_neq0 (expR_gt0 x)).
Qed.

Lemma expRD x y : expR (x + y) = expR x * expR y.
Proof.
apply: (mulIf (lt0r_neq0 (expR_gt0 (- x)))).
rewrite expRxDyMexpx expRN [_ * expR y]mulrC mulfK //.
by case: ltrgt0P (expR_gt0 x).
Qed.

Lemma expR_sum T s (P : pred T) (f : T -> R) :
  expR (\sum_(i <- s | P i) f i) = \prod_(i <- s | P i) expR (f i).
Proof. by elim/big_ind2 : _ => [|? ? ? ? <- <-|]; rewrite ?expR0// expRD. Qed.

Lemma expRM_natl n x : expR (n%:R * x) = expR x ^+ n.
Proof.
elim: n x => [x|n IH x] /=; first by rewrite mul0r expr0 expR0.
by rewrite exprS -nat1r mulrDl mul1r expRD IH.
Qed.

Lemma expRM_natr n x : expR (x * n%:R) = expR x ^+ n.
Proof. by rewrite mulrC expRM_natl. Qed.

Lemma expR_gt1 x : (1 < expR x) = (0 < x).
Proof.
case: ltrgt0P => [x_gt0| xN|->]; last by rewrite expR0.
- by rewrite (pexpR_gt1 x_gt0).
- apply/idP/negP.
  rewrite -[x]opprK expRN -leNgt invf_cp1 ?expR_gt0 //.
  by rewrite ltW // pexpR_gt1 // lterNE.
Qed.

Lemma expR_lt1 x : (expR x < 1) = (x < 0).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; last by rewrite expR0.
- by apply/idP/negP; rewrite -leNgt ltW // expR_gt1.
- by rewrite -[x]opprK expRN invf_cp1 ?expR_gt0 // expR_gt1 lterNE.
Qed.

Lemma expR_le1 x : (expR x <= 1) = (x <= 0).
Proof.
case: ltrgt0P => [||->]; last by rewrite expR0 lexx.
- by rewrite -expR_gt1 ltNge => /negbTE.
- by rewrite -expR_lt1 => /ltW.
Qed.

Lemma expRB x y : expR (x - y) = expR x / expR y.
Proof. by rewrite expRD expRN. Qed.

Lemma ltr_expR : {mono (@expR R) : x y / x < y}.
Proof.
move=> x y.
by  rewrite -[in LHS](subrK x y) expRD ltr_pMl ?expR_gt0 // expR_gt1 subr_gt0.
Qed.

Lemma ler_expR : {mono (@expR R) : x y / x <= y}.
Proof.
move=> x y.
case: (ltrgtP x y) => [xLy|yLx|<-]; last by rewrite lexx.
- by rewrite ltW // ltr_expR.
- by rewrite leNgt ltr_expR yLx.
Qed.

Lemma expR_gt1Dx x : x != 0 -> 1 + x < expR x.
Proof.
rewrite neq_lt => /orP[x0|x0].
- have [?|_] := leP x (-1).
    by rewrite (@le_lt_trans _ _ 0) ?expR_gt0// -lerBrDl sub0r.
  have [] := @MVT R expR expR _ _ x0 (fun x _ => is_derive_expR x).
    exact/continuous_subspaceT/continuous_expR.
  move=> c; rewrite in_itv/= => /andP[xc c0].
  rewrite expR0 sub0r => /eqP; rewrite subr_eq addrC -subr_eq => /eqP <-.
  by rewrite mulrN opprK ltrD2l ltr_nMl// -expR0 ltr_expR.
- have [] := @MVT R expR expR _ _ x0 (fun x _ => is_derive_expR x).
    exact/continuous_subspaceT/continuous_expR.
  move=> c; rewrite in_itv/= => /andP[c0 cx].
  rewrite subr0 expR0 => /eqP /[!subr_eq] /eqP ->.
  by rewrite addrC ltrD2r ltr_pMl// -expR0 ltr_expR.
Qed.

Lemma expR_ge1Dx x : 1 + x <= expR x.
Proof.
by have [->|/expR_gt1Dx/ltW//] := eqVneq x 0; rewrite expR0 addr0.
Qed.

Lemma cvgr_expR : @expR R (- x) @[x --> +oo] --> 0.
Proof.
apply/cvgrPdist_le => e e0; near=> x.
rewrite sub0r normrN ger0_norm; last exact: expR_ge0.
rewrite expRN -[leRHS]invrK lef_pV2 ?posrE ?expR_gt0 ?invr_gt0//.
rewrite (le_trans _ (expR_ge1Dx _))// -lerBlDl.
by near: x; apply: nbhs_pinfty_ge; exact: num_real.
Unshelve. end_near. Qed.

Lemma cvgn_expR : @expR R (- n%:R) @[n --> \oo] --> 0%R.
Proof.
under eq_cvg do rewrite -mulNrn -mulr_natr expRM_natr; apply: cvg_expr.
by rewrite ger0_norm ?expR_ge0// expRN invf_lt1 ?expR_gt1// expR_gt0.
Qed.

Lemma expR_inj : injective (@expR R).
Proof.
move=> x y exE.
by have [] := (ltr_expR x y, ltr_expR y x); rewrite exE ltxx; case: ltrgtP.
Qed.

Lemma expR_total_gt1 x :
  1 <= x -> exists y, [/\ 0 <= y, 1 + y <= x & expR y = x].
Proof.
move=> x_ge1; have x_ge0 : 0 <= x by apply: le_trans x_ge1.
have [x1 x1Ix| |x1 _ /eqP] := @IVT _ (fun y => expR y - x) _ _ 0 x_ge0.
- apply: continuousB => // y1; last exact: cst_continuous.
  by apply/continuous_subspaceT=> ?; exact: continuous_expR.
- rewrite expR0; have [_| |] := ltrgtP (1 - x) (expR x - x).
  + by rewrite subr_le0 x_ge1 subr_ge0 (le_trans _ (expR_ge1Dx _)) ?lerDr.
  + by rewrite ltrD2r expR_lt1 ltNge x_ge0.
  + rewrite subr_le0 x_ge1 => -> /=; rewrite subr_ge0.
    by rewrite (le_trans _ (expR_ge1Dx _)) ?lerDr.
- rewrite subr_eq0 => /eqP x1_x; exists x1; split => //.
  + by rewrite -ler_expR expR0 x1_x.
  + by rewrite -x1_x expR_ge1Dx // -ler_expR x1_x expR0.
Qed.

Lemma expR_total x : 0 < x -> exists y, expR y = x.
Proof.
case: (lerP 1 x) => [/expR_total_gt1[y [_ _ Hy]]|x_lt1 x_gt0].
  by exists y.
have /expR_total_gt1[y [H1y H2y H3y]] : 1 <= x^-1 by rewrite ltW // !invf_cp1.
by exists (-y); rewrite expRN H3y invrK.
Qed.

Local Open Scope convex_scope.
Lemma convex_expR (t : {i01 R}) (a b : R^o) :
  expR (a <| t |> b) <= (expR a : R^o) <| t |> (expR b : R^o).
Proof.
have [ab|/ltW ba] := leP a b.
- apply: second_derivative_convex => //.
  + by move=> x axb; rewrite derive_expR derive_val expR_ge0.
  + exact/cvg_at_left_filter/continuous_expR.
  + exact/cvg_at_right_filter/continuous_expR.
  + by move=> z zab; rewrite derive_expR; exact: derivable_expR.
- rewrite convC [leRHS]convC; apply: second_derivative_convex => //.
  + by move=> x axb; rewrite derive_expR derive_val expR_ge0.
  + exact/cvg_at_left_filter/continuous_expR.
  + exact/cvg_at_right_filter/continuous_expR.
  + by move=> z zab; rewrite derive_expR; exact: derivable_expR.
Qed.
Local Close Scope convex_scope.

Definition expR_itv_boundl b :=
  Order.max (BRight 0%Z) (IntItv.add_boundl b (BLeft 1)).

Definition expR_itv_boundr b :=
  match b with
  | BSide _ (Negz _) => BLeft 1%Z
  | BSide b 0%Z => BSide b 1%Z
  | _ => +oo%O
  end.

Definition expR_itv i :=
  match i with
  | Itv.Top => Itv.Real `[0%Z, +oo[
  | Itv.Real (Interval l u) =>
      Itv.Real (Interval (expR_itv_boundl l) (expR_itv_boundr u))
  end.

Lemma num_spec_expR (i : Itv.t) (x : Itv.def (@Itv.num_sem R) i)
    (r := expR_itv i) :
  Itv.spec (@Itv.num_sem R) r (expR x%:num).
Proof.
rewrite {}/r; case: i x => [|[l u]] x /=.
  by apply/and3P; rewrite ?num_real// bnd_simp expR_ge0.
case: x => [x /=/and3P[xr lx xu]]; apply/and3P; split; [exact: num_real| | ].
- rewrite Instances.num_itv_bound_max maxEge.
  case: ifP; rewrite ?bnd_simp ?expR_gt0// => _.
  apply: le_trans (Instances.num_itv_add_boundl lx _) _; first exact: lexx.
  by rewrite bnd_simp addrC expR_ge1Dx.
- case: u xu => [[] [[|//] | u] |//]; rewrite !bnd_simp.
  + by rewrite expR_lt1.
  + by rewrite expR_lt1 => /lt_trans; apply.
  + by rewrite expR_le1.
  + by rewrite expR_lt1 => /le_lt_trans; apply.
Qed.

Canonical expR_inum (i : Itv.t) (x : Itv.def (@Itv.num_sem R) i) :=
  Itv.mk (num_spec_expR x).

End expR.

#[deprecated(since="mathcomp-analysis 1.1.0", note="renamed `expRM_natl`")]
Notation expRMm := expRM_natl (only parsing).

Section expeR.
Context {R : realType}.
Implicit Types (x y : \bar R) (r s : R).

Local Open Scope ereal_scope.

Definition expeR x :=
  match x with | r%:E => (expR r)%:E | +oo => +oo | -oo => 0 end.

Lemma expeR0 : expeR 0 = 1. Proof. by rewrite /= expR0. Qed.

Lemma expeR_ge0 x : 0 <= expeR x.
Proof. by case: x => //= r; rewrite lee_fin expR_ge0. Qed.

Lemma expeR_gt0 x : -oo < x -> 0 < expeR x.
Proof. by case: x => //= r; rewrite lte_fin expR_gt0. Qed.

Lemma expeR_eq0 x : (expeR x == 0) = (x == -oo).
Proof. by case: x => //= [r|]; rewrite ?eqxx// eqe expR_eq0. Qed.

Lemma expeRD x y : expeR (x + y) = expeR x * expeR y.
Proof.
case: x => /= [r| |]; last by rewrite mul0e.
- case: y => /= [s| |]; last by rewrite mule0.
  + by rewrite expRD EFinM.
  + by rewrite mulry gtr0_sg ?mul1e// expR_gt0.
- case: y => /= [s| |]; last by rewrite mule0.
  + by rewrite mulyr gtr0_sg ?mul1e// expR_gt0.
  + by rewrite mulyy.
Qed.

Lemma expeR_ge1Dx x : 1 + x <= expeR x.
Proof.
case : x => //= [r|]; last by rewrite addeNy.
by rewrite -EFinD !lee_fin; exact: expR_ge1Dx.
Qed.

Lemma ltr_expeR : {mono expeR : x y / x < y}.
Proof.
move=> [r| |] [s| |]//=; rewrite ?ltry//.
- by rewrite !lte_fin ltr_expR.
- by rewrite !ltNge lee_fin expR_ge0 leNye.
- by rewrite lte_fin expR_gt0 ltNye.
Qed.

Lemma ler_expeR : {mono expeR : x y / x <= y}.
Proof.
move=> [r| |] [s| |]//=; rewrite ?leey ?lexx//.
- by rewrite !lee_fin ler_expR.
- by rewrite !leNgt lte_fin expR_gt0 ltNye.
- by rewrite lee_fin expR_ge0 leNye.
Qed.

Lemma expeR_inj : injective expeR.
Proof.
move=> [r| |] [s| |] => //=.
- by move=> [] /expR_inj ->.
- by case => /eqP; rewrite expR_eq0.
- by case => /esym/eqP; rewrite expR_eq0.
Qed.

Lemma expeR_total x : 0 <= x -> exists y, expeR y = x.
Proof.
move: x => [r|_|//]; last by exists +oo.
rewrite le_eqVlt => /predU1P[<-|]; first by exists -oo.
by rewrite lte_fin => /expR_total[y <-]; exists y%:E.
Qed.

End expeR.

Section Ln.
Variable R : realType.
Implicit Types x : R.

Notation exp := (@expR R).

Definition ln x : R := [get y | exp y == x ].

Fact ln0 x : x <= 0 -> ln x = 0.
Proof.
rewrite /ln; case: xgetP => //= y _ /eqP yx x0.
by have := expR_gt0 y; rewrite yx => /(le_lt_trans x0); rewrite ltxx.
Qed.

Lemma expRK : cancel exp ln.
Proof.
by move=> x; rewrite /ln; case: xgetP => [x1 _ /eqP/expR_inj //|/(_ x)[]/=].
Qed.

Lemma lnK : {in Num.pos, cancel ln exp}.
Proof.
move=> x; rewrite qualifE => x_gt0.
rewrite /ln; case: xgetP=> [x1 _ /eqP// |H].
by case: (expR_total x_gt0) => y /eqP Hy; case: (H y).
Qed.

Lemma lnK_eq x : (exp (ln x) == x) = (0 < x).
Proof.
by apply/eqP/idP=> [<-|x0]; [exact: expR_gt0|rewrite lnK// in_itv/= x0].
Qed.

Lemma ln1 : ln 1 = 0.
Proof. by apply/expR_inj; rewrite lnK// ?expR0// qualifE/=. Qed.

Lemma lnM : {in Num.pos &, {morph ln : x y / x * y >-> x + y}}.
Proof.
move=> x y x0 y0; apply: expR_inj; rewrite expRD !lnK//.
by move: x0 y0; rewrite !qualifE; exact: mulr_gt0.
Qed.

Lemma ln_inj : {in Num.pos &, injective ln}.
Proof. by move=> x y /lnK {2}<- /lnK {2}<- ->. Qed.

Lemma lnV : {in Num.pos, {morph ln : x / x ^-1 >-> - x}}.
Proof.
move=> x x0; apply: expR_inj; rewrite lnK// ?expRN ?lnK//.
by move: x0; rewrite !qualifE/= invr_gt0.
Qed.

Lemma ln_div : {in Num.pos &, {morph ln : x y / x / y >-> x - y}}.
Proof.
move=> x y x0 y0; rewrite (lnM x0) ?lnV//.
by move: y0; rewrite !qualifE/= invr_gt0.
Qed.

Lemma ltr_ln : {in Num.pos &, {mono ln : x y / x < y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ltr_expR !lnK. Qed.

Lemma ler_ln : {in Num.pos &, {mono ln : x y / x <= y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ler_expR !lnK. Qed.

Lemma lnXn n x : 0 < x -> ln (x ^+ n) = ln x *+ n.
Proof.
move=> x_gt0; elim: n => [|n ih] /=; first by rewrite expr0 ln1 mulr0n.
by rewrite !exprS lnM ?qualifE//= ?exprn_gt0// mulrS ih.
Qed.

Lemma le_ln1Dx x : -1 < x -> ln (1 + x) <= x.
Proof.
move=> N1x; rewrite -ler_expR lnK ?expR_ge1Dx //.
by rewrite posrE addrC -ltrBlDr sub0r.
Qed.

Lemma ln_sublinear x : 0 < x -> ln x < x.
Proof.
move=> x_gt0; apply: lt_le_trans (_ : ln (1 + x) <= _).
  by rewrite -ltr_expR !lnK ?qualifE/= ?addr_gt0 // ltrDr.
by rewrite -ler_expR lnK ?qualifE/= ?addr_gt0// expR_ge1Dx // ltW.
Qed.

Lemma ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
by move=> x_ge1; rewrite -ler_expR expR0 lnK// qualifE/= (lt_le_trans _ x_ge1).
Qed.

Lemma ln_lt0 x : 0 < x < 1 -> ln x < 0.
Proof. by move=> /andP[x_gt0 x_lt1]; rewrite -ltr_expR expR0 lnK. Qed.

Lemma ln_gt0 x : 1 < x -> 0 < ln x.
Proof.
by move=> x_gt1; rewrite -ltr_expR expR0 lnK // qualifE/= (lt_trans _ x_gt1).
Qed.

Lemma ln_le0 (x : R) : x <= 1 -> ln x <= 0.
Proof.
have [x0|x0 x1] := leP x 0; first by rewrite ln0.
by rewrite -ler_expR expR0 lnK.
Qed.

Lemma continuous_ln x : 0 < x -> {for x, continuous ln}.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: nbhs_singleton (near_can_continuous _ _); near=> z; first exact: expRK.
by apply: continuous_expR.
Unshelve. all: by end_near. Qed.

Global Instance is_derive1_ln (x : R) : 0 < x -> is_derive x 1 ln x^-1.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: (@is_derive_inverse R expR); first by near=> z; apply: expRK.
  by near=>z; apply: continuous_expR.
by rewrite lnK // lt0r_neq0.
Unshelve. all: by end_near. Qed.

Local Open Scope convex_scope.
Lemma concave_ln (t : {i01 R}) (a b : R^o) : 0 < a -> 0 < b ->
  (ln a : R^o) <| t |> (ln b : R^o) <= ln (a <| t |> b).
Proof.
move=> a0 b0; have := convex_expR t (ln a) (ln b).
by rewrite !lnK// -(@ler_ln) ?posrE ?expR_gt0 ?conv_gt0// expRK.
Qed.
Local Close Scope convex_scope.

End Ln.

Section PowR.
Variable R : realType.
Implicit Types a x y z r : R.

Definition powR a x := if a == 0 then (x == 0)%:R else expR (x * ln a).

Local Notation "a `^ x" := (powR a x).

Lemma expRM x y : expR (x * y) = (expR x) `^ y.
Proof. by rewrite /powR gt_eqF ?expR_gt0// expRK mulrC. Qed.

Lemma powR_ge0 a x : 0 <= a `^ x.
Proof. by rewrite /powR; case: ifPn => // _; exact: expR_ge0. Qed.

Lemma powR_gt0 a x : 0 < a -> 0 < a `^ x.
Proof. by move=> a0; rewrite /powR gt_eqF// expR_gt0. Qed.

Lemma gt0_powR a x : 0 < x -> 0 <= a -> 0 < a `^ x -> 0 < a.
Proof.
move=> x0 a0; rewrite /powR; case: ifPn => [_|a_neq0 _].
  by rewrite gt_eqF//= ltxx.
by rewrite lt_neqAle a0 andbT eq_sym.
Qed.

Lemma powR0 x : x != 0 -> 0 `^ x = 0.
Proof. by move=> x0; rewrite /powR eqxx (negbTE x0). Qed.

Lemma powRr1 a : 0 <= a -> a `^ 1 = a.
Proof.
rewrite le_eqVlt => /predU1P[<-|a0]; first by rewrite powR0// oner_eq0.
by rewrite /powR gt_eqF// mul1r lnK// posrE.
Qed.

Lemma powRr0 a : a `^ 0 = 1.
Proof. by rewrite /powR; case: ifPn; rewrite ?eqxx// mul0r expR0. Qed.

Lemma powR1 : powR 1 = fun=> 1.
Proof. by apply/funext => x; rewrite /powR oner_eq0 ln1 mulr0 expR0. Qed.

Lemma powR_eq0 x p : (x `^ p == 0) = (x == 0) && (p != 0).
Proof.
rewrite /powR; have [_|x_neq0] := eqVneq x 0 => //.
  by case: (p == 0); rewrite (oner_eq0, eqxx).
by rewrite expR_eq0.
Qed.

Lemma powR_eq0_eq0 x p : x `^ p = 0 -> x = 0.
Proof. by move=> /eqP; rewrite powR_eq0 => /andP[/eqP]. Qed.

Lemma ger_powR a : 0 < a <= 1 -> {homo powR a : x y /~ y <= x}.
Proof.
move=> /andP[a0 a1] x y xy.
by rewrite /powR gt_eqF// ler_expR ler_wnM2r// ln_le0.
Qed.

Lemma ler_powR a : 1 <= a -> {homo powR a : x y / x <= y}.
Proof.
move=> a1 x y xy.
by rewrite /powR gt_eqF ?(lt_le_trans _ a1)// ler_expR ler_wpM2r ?ln_ge0.
Qed.

Lemma powR_injective r : 0 < r -> {in Num.nneg &, injective (powR ^~ r)}.
Proof.
move=> r0 x y x0 y0; rewrite /powR; case: ifPn => [/eqP ->|xneq0].
  by case: ifPn => [/eqP ->//|_ /eqP]; rewrite (gt_eqF r0) eq_sym expR_eq0.
case: ifPn => [/eqP -> /eqP|yneq0]; first by rewrite (gt_eqF r0) expR_eq0.
by move/expR_inj/mulfI => /(_ (negbT (gt_eqF r0))); apply: ln_inj;
  rewrite posrE lt_neqAle eq_sym (xneq0,yneq0).
Qed.

Lemma ler1_powR a r : 1 <= a -> r <= 1 -> a >= a `^ r.
Proof.
by move=> a1 r1; rewrite (le_trans (ler_powR _ r1)) ?powRr1// (le_trans _ a1).
Qed.

Lemma le1r_powR a r : 1 <= a -> 1 <= r -> a <= a `^ r.
Proof.
by move=> a1 r1; rewrite (le_trans _ (ler_powR _ r1)) ?powRr1// (le_trans _ a1).
Qed.

Lemma ger1_powR a r : 0 < a <= 1 -> r <= 1 -> a <= a `^ r.
Proof.
move=> /andP[a0 _a1] r1.
by rewrite (le_trans _ (ger_powR _ r1)) ?powRr1 ?a0// ltW.
Qed.

Lemma ge1r_powR a r : 0 < a <= 1 -> 1 <= r -> a >= a `^ r.
Proof.
move=> /andP[a0 a1] r1.
by rewrite (le_trans (ger_powR _ r1)) ?powRr1 ?a0// ltW.
Qed.

Lemma ge0_ler_powR r : 0 <= r ->
  {in Num.nneg &, {homo powR ^~ r : x y / x <= y >-> x <= y}}.
Proof.
rewrite le_eqVlt => /predU1P[<- x y _ _ _|]; first by rewrite !powRr0.
move=> a0 x y; rewrite 2!nnegrE !le_eqVlt => /predU1P[<-|x0].
  move=> /predU1P[<- _|y0 _]; first by rewrite eqxx.
  by rewrite !powR0 ?(gt_eqF a0)// powR_gt0 ?orbT.
move=> /predU1P[<-|y0]; first by rewrite gt_eqF//= ltNge (ltW x0).
move=> /predU1P[->//|xy]; first by rewrite eqxx.
by apply/orP; right; rewrite /powR !gt_eqF// ltr_expR ltr_pM2l// ltr_ln.
Qed.

Lemma gt0_ltr_powR r : 0 < r ->
  {in Num.nneg &, {homo powR ^~ r : x y / x < y >-> x < y}}.
Proof.
move=> r0 x y x0 y0 xy; have := ge0_ler_powR (ltW r0) x0 y0 (ltW xy).
rewrite le_eqVlt => /orP[/eqP/(powR_injective r0 x0 y0)/eqP|//].
by rewrite lt_eqF.
Qed.

Lemma powRM x y r : 0 <= x -> 0 <= y -> (x * y) `^ r = x `^ r * y `^ r.
Proof.
rewrite /powR mulf_eq0.
case: (ltgtP x 0) => // x0 _; case: (ltgtP y 0) => //= y0 _; do ?
  by case: eqVneq => [r0|]; rewrite ?r0 ?mul0r ?expR0 ?mulr0 ?mul1r.
by rewrite lnM// mulrDr expRD.
Qed.

Lemma ge1r_powRZ x y r : 0 < x <= 1 -> 0 <= y -> 1 <= r ->
  (x * y) `^ r <= x * (y `^ r).
Proof.
move=> /andP[x0 x1] y0 r1.
by rewrite (powRM _ (ltW _))// ler_wpM2r ?powR_ge0// ge1r_powR// x0.
Qed.

Lemma le1r_powRZ x y r : x >= 1 -> 0 <= y -> 1 <= r ->
  (x * y) `^ r >= x * (y `^ r).
Proof.
move=> x1 y0 r1.
by rewrite (powRM _ (le_trans _ x1))// ler_wpM2r ?powR_ge0// le1r_powR// x0.
Qed.

Lemma powRrM x y z : x `^ (y * z) = (x `^ y) `^ z.
Proof.
rewrite /powR mulf_eq0; have [_|xN0] := eqVneq x 0.
  by case: (y == 0); rewrite ?eqxx//= oner_eq0 ln1 mulr0 expR0.
by rewrite expR_eq0 expRK mulrCA mulrA.
Qed.

Lemma powRAC x y z : (x `^ y) `^ z = (x `^ z) `^ y.
Proof. by rewrite -!powRrM mulrC. Qed.

Lemma powRD x r s : (r + s == 0) ==> (x != 0) -> x `^ (r + s) = x `^ r * x `^ s.
Proof.
rewrite /powR; case: (eqVneq x 0) => //= [_|x_neq0 _];
  last by rewrite mulrDl expRD.
have [->|] := eqVneq r 0; first by rewrite mul1r add0r.
by rewrite implybF mul0r => _ /negPf ->.
Qed.

Lemma mulr_powRB1 x p : 0 <= x -> 0 < p -> x * x `^ (p - 1) = x `^ p.
Proof.
rewrite le_eqVlt => /predU1P[<- p0|x0 p0]; first by rewrite mul0r powR0 ?gt_eqF.
by rewrite -{1}(powRr1 (ltW x0))// -powRD addrCA subrr addr0// gt_eqF.
Qed.

Lemma powRN x r : x `^ (- r) = (x `^ r)^-1.
Proof.
have [r0|r0] := eqVneq r 0%R; first by rewrite r0 oppr0 powRr0 invr1.
have [->|xN0] := eqVneq x 0; first by rewrite !powR0 ?oppr_eq0// invr0.
rewrite -div1r; apply: (canRL (mulfK _)); first by rewrite powR_eq0 (negPf xN0).
by rewrite -powRD ?addNr ?powRr0// xN0 eqxx.
Qed.

Lemma powRB x r s : (r == s) ==> (x != 0) -> x `^ (r - s) = x `^ r / x `^ s.
Proof. by move=> ?; rewrite powRD ?subr_eq0// powRN. Qed.

Lemma powR_mulrn a n : 0 <= a -> a `^ n%:R = a ^+ n.
Proof.
move=> a_ge0; elim: n => [|n IHn]; first by rewrite powRr0 expr0.
by rewrite -natr1 powRD ?natr1 ?pnatr_eq0// powRr1// IHn exprSr.
Qed.

Lemma powR_inv1 a : 0 <= a -> a `^ (-1) = a ^-1.
Proof. by move=> a_ge0; rewrite powRN powRr1. Qed.

Lemma powR_invn a n : 0 <= a -> a `^ (- n%:R) = a ^- n.
Proof. by move=> a_ge0; rewrite powRN powR_mulrn. Qed.

Lemma powR_intmul a (z : int) : 0 <= a -> a `^ z%:~R = a ^ z.
Proof. by move=> a0; case: z => n; [exact: powR_mulrn | exact: powR_invn]. Qed.

Lemma ln_powR a x : ln (a `^ x) = x * ln a.
Proof.
have [->|x0] := eqVneq x 0; first by rewrite powRr0 ln1// mul0r.
have [->|a0] := eqVneq a 0; first by rewrite powR0// ln0// mulr0.
by rewrite /powR (negbTE a0) expRK.
Qed.

Lemma powR12_sqrt a : 0 <= a -> a `^ (2^-1) = Num.sqrt a.
Proof.
rewrite le_eqVlt => /predU1P[<-|a0].
  by rewrite powR0 ?invr_eq0 ?pnatr_eq0// sqrtr0.
have /eqP : (a `^ (2^-1)) ^+ 2 = (Num.sqrt a) ^+ 2.
  rewrite sqr_sqrtr; last exact: ltW.
  by rewrite /powR gt_eqF// -expRM_natl mulrA divrr ?mul1r ?unitfE// lnK.
rewrite eqf_sqr => /predU1P[//|/eqP h].
have : 0 < a `^ 2^-1 by exact: powR_gt0.
by rewrite h oppr_gt0 ltNge sqrtr_ge0.
Qed.

Lemma norm_powR a x : 0 <= a -> `|a `^ x| = `|a| `^ x.
Proof.
move=> a0; rewrite /powR; case: ifPn => [/eqP ->|].
  by rewrite normr0 eqxx normr_nat.
rewrite neq_lt ltNge a0/= => {}a0.
by rewrite gtr0_norm ?expR_gt0// gtr0_norm// gt_eqF.
Qed.

Lemma lt0_norm_powR a x : a < 0 -> `|a `^ x| = 1.
Proof.
move=> a0; rewrite /powR lt_eqF// gtr0_norm ?expR_gt0//.
by rewrite ln0 ?mulr0 ?expR0// ltW.
Qed.

Lemma conjugate_powR a b p q : 0 <= a -> 0 <= b ->
  0 < p -> 0 < q -> p^-1 + q^-1 = 1 ->
  a * b <= a `^ p / p + b `^ q / q.
Proof.
rewrite le_eqVlt => /predU1P[<- b0 p0 q0 _|a0].
  by rewrite mul0r powR0 ?gt_eqF// mul0r add0r divr_ge0 ?powR_ge0 ?ltW.
rewrite le_eqVlt => /predU1P[<-|b0] p0 q0 pq.
  by rewrite mulr0 powR0 ?gt_eqF// mul0r addr0 divr_ge0 ?powR_ge0 ?ltW.
have iq1 : q^-1 <= 1 by rewrite -pq ler_wpDl// invr_ge0 ltW.
have ap0 : (0 < a `^ p)%R by rewrite powR_gt0.
have bq0 : (0 < b `^ q)%R by rewrite powR_gt0.
have := @concave_ln _ (Itv01 (eqbRL (invr_ge0 _) (ltW q0)) iq1) _ _ ap0 bq0.
have pq' : (p^-1 = 1 - q^-1)%R by rewrite -pq addrK.
rewrite !convRE/= /onem -pq' -[_ <= ln _]ler_expR expRD (mulrC p^-1).
rewrite ln_powR mulrAC divff ?mul1r ?gt_eqF// (mulrC q^-1).
rewrite ln_powR mulrAC divff ?mul1r ?gt_eqF//.
rewrite lnK ?posrE// lnK ?posrE// => /le_trans; apply.
rewrite lnK//; last by rewrite posrE addr_gt0// mulr_gt0// ?invr_gt0.
by rewrite (mulrC _ p^-1) (mulrC _ q^-1).
Qed.

End PowR.
Notation "a `^ x" := (powR a x) : ring_scope.

#[deprecated(since="mathcomp-analysis 0.6.5", note="renamed `ge0_ler_powR`")]
Notation gt0_ler_powR := ge0_ler_powR.

Section poweR.
Local Open Scope ereal_scope.
Context {R : realType}.
Implicit Types (s r : R) (x y : \bar R).

Definition poweR x r :=
  match x with
  | x'%:E => (x' `^ r)%:E
  | +oo => if r == 0%R then 1%E else +oo
  | -oo => if r == 0%R then 1%E else 0%E
  end.

Local Notation "x `^ r" := (poweR x r).

Lemma poweR_EFin s r : s%:E `^ r = (s `^ r)%:E.
Proof. by []. Qed.

Lemma poweRyr r : r != 0%R -> +oo `^ r = +oo.
Proof. by move/negbTE => /= ->. Qed.

Lemma poweRe0 x : x `^ 0 = 1.
Proof. by move: x => [x'| |]/=; rewrite ?powRr0// eqxx. Qed.

Lemma poweRe1 x : 0 <= x -> x `^ 1 = x.
Proof.
by move: x => [x'| |]//= x0; rewrite ?powRr1// (negbTE (oner_neq0 _)).
Qed.

Lemma poweRN x r : x \is a fin_num -> x `^ (- r) = (fine x `^ r)^-1%:E.
Proof. by case: x => // x xf; rewrite poweR_EFin powRN. Qed.

Lemma poweRNyr r : r != 0%R -> -oo `^ r = 0.
Proof. by move=> r0 /=; rewrite (negbTE r0). Qed.

Lemma poweR_eqy x r : x `^ r = +oo -> x = +oo.
Proof. by case: x => [x| |] //=; case: ifP. Qed.

Lemma eqy_poweR x r : (0 < r)%R -> x = +oo -> x `^ r = +oo.
Proof. by move: x => [| |]//= r0 _; rewrite gt_eqF. Qed.

Lemma poweR_lty x r : x < +oo -> x `^ r < +oo.
Proof.
by move: x => [x| |]//=; rewrite ?ltry//; case: ifPn => // _; rewrite ltry.
Qed.

Lemma lty_poweRy x r : r != 0%R -> x `^ r < +oo -> x < +oo.
Proof.
by move=> r0; move: x => [x| | _]//=; rewrite ?ltry// (negbTE r0).
Qed.

Lemma poweR0r r : r != 0%R -> 0 `^ r = 0.
Proof. by move=> r0; rewrite poweR_EFin powR0. Qed.

Lemma poweR1r r : 1 `^ r = 1. Proof. by rewrite poweR_EFin powR1. Qed.

Lemma fine_poweR x r : fine (x `^ r) = ((fine x) `^ r)%R.
Proof.
by move: x => [x| |]//=; case: ifPn => [/eqP ->|?]; rewrite ?powRr0 ?powR0.
Qed.

Lemma poweR_ge0 x r : 0 <= x `^ r.
Proof. by move: x => [x| |]/=; rewrite ?lee_fin ?powR_ge0//; case: ifPn. Qed.

Lemma poweR_gt0 x r : 0 < x -> 0 < x `^ r.
Proof.
by move: x => [x|_|]//=; [rewrite lte_fin; exact: powR_gt0|case: ifPn].
Qed.

Lemma gt0_poweR x r : (0 < r)%R -> 0 <= x -> 0 < x `^ r -> 0 < x.
Proof.
move=> r0; move: x => [x|//|]; rewrite ?leeNe_eq// lee_fin !lte_fin.
exact: gt0_powR.
Qed.

Lemma poweR_eq0 x r : 0 <= x -> (x `^ r == 0) = ((x == 0) && (r != 0%R)).
Proof.
move: x => [x _|_/=|//]; first by rewrite poweR_EFin eqe powR_eq0.
by case: ifP => //; rewrite onee_eq0.
Qed.

Lemma poweR_eq0_eq0 x r : 0 <= x -> x `^ r = 0 -> x = 0.
Proof. by move=> + /eqP => /poweR_eq0-> /andP[/eqP]. Qed.

Lemma gt0_ler_poweR r : (0 <= r)%R ->
  {in `[0, +oo] &, {homo poweR ^~ r : x y / x <= y >-> x <= y}}.
Proof.
move=> r0 + y; case=> //= [x /[1!in_itv]/= /andP[xint _]| _ _].
- case: y => //= [y /[1!in_itv]/= /andP[yint _] xy| _ _].
  + by rewrite !lee_fin ge0_ler_powR.
  + by case: eqP => [->|]; rewrite ?powRr0 ?leey.
- by rewrite leye_eq => /eqP ->.
Qed.

Lemma fin_num_poweR x r : x \is a fin_num -> x `^ r \is a fin_num.
Proof.
by move=> xfin; rewrite ge0_fin_numE ?poweR_lty ?ltey_eq ?xfin// poweR_ge0.
Qed.

Lemma poweRM x y r : 0 <= x -> 0 <= y -> (x * y) `^ r = x `^ r * y `^ r.
Proof.
have [->|rN0] := eqVneq r 0%R; first by rewrite !poweRe0 mule1.
have powyrM s : (0 <= s)%R -> (+oo * s%:E) `^ r = +oo `^ r * s%:E `^ r.
  case: ltgtP => // [s_gt0 _|<- _]; last first.
    by rewrite mule0 poweRyr// !poweR0r// mule0.
  by rewrite gt0_mulye// poweRyr// gt0_mulye// poweR_gt0.
case: x y => [x| |] [y| |]// x0 y0; first by rewrite /= -EFinM powRM.
- by rewrite muleC powyrM// muleC.
- by rewrite powyrM.
- by rewrite mulyy !poweRyr// mulyy.
Qed.

Lemma poweRrM x r s : x `^ (r * s) = (x `^ r) `^ s.
Proof.
have [->|s0] := eqVneq s 0%R; first by rewrite mulr0 !poweRe0.
have [->|r0] := eqVneq r 0%R; first by rewrite mul0r poweRe0 poweR1r.
case: x => [x| |]//; first by rewrite /= powRrM.
  by rewrite !poweRyr// mulf_neq0.
by rewrite !poweRNyr ?poweR0r ?(negPf s0)// mulf_neq0.
Qed.

Lemma poweRAC x r s : (x `^ r) `^ s = (x `^ s) `^ r.
Proof. by rewrite -!poweRrM mulrC. Qed.

Definition poweRD_def x r s := ((r + s == 0)%R ==>
  ((x != 0) && ((x \isn't a fin_num) ==> (r == 0%R) && (s == 0%R)))).
Notation "x '`^?' ( r +? s )" := (poweRD_def x r s) : ereal_scope.

Lemma poweRD_defE x r s :
  x `^?(r +? s) = ((r + s == 0)%R ==>
  ((x != 0) && ((x \isn't a fin_num) ==> (r == 0%R) && (s == 0%R)))).
Proof. by []. Qed.

Lemma poweRB_defE x r s :
  x `^?(r +? - s) = ((r == s)%R ==>
  ((x != 0) && ((x \isn't a fin_num) ==> (r == 0%R) && (s == 0%R)))).
Proof. by rewrite poweRD_defE subr_eq0 oppr_eq0. Qed.

Lemma add_neq0_poweRD_def x r s : (r + s != 0)%R -> x `^?(r +? s).
Proof. by rewrite poweRD_defE => /negPf->. Qed.

Lemma add_neq0_poweRB_def x r s : (r != s)%R -> x `^?(r +? - s).
Proof. by rewrite poweRB_defE => /negPf->. Qed.

Lemma nneg_neq0_poweRD_def x r s : x != 0 -> (r >= 0)%R -> (s >= 0)%R ->
  x `^?(r +? s).
Proof.
move=> xN0 rge0 sge0; rewrite /poweRD_def xN0/=.
by case: ltgtP rge0 => // [r_gt0|<-]; case: ltgtP sge0 => // [s_gt0|<-]//=;
   rewrite ?addr0 ?add0r ?implybT// gt_eqF//= ?addr_gt0.
Qed.

Lemma nneg_neq0_poweRB_def x r s : x != 0 -> (r >= 0)%R -> (s <= 0)%R ->
  x `^?(r +? - s).
Proof. by move=> *; rewrite nneg_neq0_poweRD_def// oppr_ge0. Qed.

Lemma poweRD x r s : x `^?(r +? s) -> x `^ (r + s) = x `^ r * x `^ s.
Proof.
rewrite /poweRD_def.
have [->|r0]/= := eqVneq r 0%R; first by rewrite add0r poweRe0 mul1e.
have [->|s0]/= := eqVneq s 0%R; first by rewrite addr0 poweRe0 mule1.
case: x => // [t|/=|/=]; rewrite ?(negPf r0, negPf s0, implybF); last 2 first.
- by move=> /negPf->; rewrite mulyy.
- by move=> /negPf->; rewrite mule0.
rewrite !poweR_EFin eqe => /implyP/(_ _)/andP cnd.
by rewrite powRD//; apply/implyP => /cnd[].
Qed.

Lemma poweRB x r s : x `^?(r +? - s) -> x `^ (r - s) = x `^ r * x `^ (- s).
Proof. by move=> rs; rewrite poweRD. Qed.

Lemma poweR12_sqrt x : 0 <= x -> x `^ 2^-1 = sqrte x.
Proof.
move: x => [x|_|//]; last by rewrite poweRyr.
by rewrite lee_fin => x0 /=; rewrite powR12_sqrt.
Qed.

End poweR.
Notation "a `^ x" := (poweR a x) : ereal_scope.

Section riemannR_series.
Variable R : realType.
Implicit Types a : R.
Local Open Scope real_scope.

Definition riemannR a : R ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemannR a n /.

Lemma riemannR_gt0 a i : 0 <= a -> 0 < riemannR a i.
Proof. by move=> ?; rewrite /riemannR invr_gt0 powR_gt0. Qed.

Lemma dvg_riemannR a : 0 <= a <= 1 -> ~ cvgn (series (riemannR a)).
Proof.
move=> /andP[a0 a1].
have : forall n, harmonic n <= riemannR a n.
  move=> [/=|n]; first by rewrite powR1 invr1.
  rewrite -[leRHS]div1r ler_pdivlMr ?powR_gt0// mulrC ler_pdivrMr//.
  by rewrite mul1r -[leRHS]powRr1// (ler_powR)// ler1n.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemannR_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemannR_series.
