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
(*               lne x == extended real numer-valued natural logarithm        *)
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

Lemma expeR_eqy x : (expeR x == +oo) = (x == +oo).
Proof. by case : x => //= [r|]. Qed. 

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

Lemma lt0_ln (x : R) : x < 0 -> ln x = 0.
Proof.
move=> x0; rewrite /ln/=.
rewrite getPN//= => y /eqP eqx.
by move: x0; rewrite -eqx le_gtF// expR_ge0.
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

Section Lne.
  Variable R : realType.
  Implicit Types x : \bar R.
  
  Local Open Scope ereal_scope.
  
  Definition lne x := 
  match x with
  | x'%:E => if x' == 0%R then -oo else (ln x')%:E
  | +oo => +oo
  | -oo => 0 
  end.
  
  Lemma lne0 x : x < 0 -> lne x = 0.
  Proof.
  by move: x => [x||]//=; rewrite lte_fin => ?; rewrite lt_eqF ?ln0 ?ltW.
  Qed.
  
  Lemma lner r : (r != 0)%R -> lne (r%:E) = (ln r)%:E.
  Proof. by move => /negbTE //= ->. Qed.
  
  Lemma expeRK : cancel expeR lne.
  Proof. by case=> //=[x|]; rewrite ?eqxx ?gt_eqF ?expR_gt0 ?expRK. Qed.
  
  (*x  \is Num.pos -> exp (ln x) = x*)
  Lemma lneK x : 0 < x ->  expeR (lne x) = x.
  (* {in Num.pos, cancel lne (@expeR R)}.*)
  Proof.
  case : x => [r|//|]; last by rewrite ltNge leNye.
  by rewrite /expeR/lne; case: ifPn => [/eqP ->|_ ?]; rewrite ?lnK.
  Qed.
  
  Lemma lneK_eq x : (expeR (lne x) == x) = (0 <= x).
  Proof.
  case: x => //=[r|]; last by rewrite eqxx leey.
  case: ifPn => /=[/eqP->|r0]; first by rewrite eqxx lexx.
  by rewrite eqe lnK_eq lee_fin lt_neqAle eq_sym r0.
  Qed.  
  
  Lemma lne1 : lne 1 = 0.
  Proof. by rewrite lner //= ln1. Qed.  
  
  Lemma lneM x y : 0 < x -> 0 < y -> lne (x * y) = (lne x + lne y).
  Proof. 
  by move => x0 y0; apply expeR_inj; rewrite expeRD !lneK// mule_gt0.
  Qed. 
  
  Lemma lne_inj x y : 0 < x -> 0 < y -> lne x = lne y -> x = y.
  Proof. by move=> /lneK {2}<- /lneK {2}<- ->. Qed. 
  
  Lemma lneV (r : R) : (0 < r)%R -> lne (r%R^-1)%:E = - lne (r%:E).
  Proof. by move=> r0; rewrite !lner ?gt_eqF ?invr_gt0// lnV. Qed.
  
  Lemma lne_div x y : 
    0 < x -> 0 < y -> lne (x * (fine y)^-1%:E) = lne x - lne y.
  Proof.
  case: x => //[x|]; case: y => //[y|]; rewrite ?lte_fin => a0 b0/=.
  - by rewrite !ifF ?gt_eqF ?divr_gt0// ln_div.
  - by rewrite ifT ?invr0 ?mulr0// addeNy.
  - by rewrite ifF ?gt0_mulye ?lte_fin ?invr_gt0// gt_eqF.
  - by rewrite invr0 mule0/= eqxx addeNy.
  Qed.  
  
  Lemma ltr_lne x y : 0 < x -> 0 < y -> (lne x < lne y) = (x < y).
  Proof. by move => x_gt0 y_gt0; rewrite -ltr_expeR !lneK. Qed. 
  
  Lemma ler_lne x y :  0 < x -> 0 < y -> (lne x <= lne y) = (x <= y).
  Proof. by move=> x_gt0 y_gt0; rewrite -ler_expeR !lneK. Qed.
  
  Lemma lneXn n x : 0 < x -> lne (x ^+ n) = lne x *+ n.
  Proof.
  case: n => [/=|]; first by rewrite ifF ?ln1// gt_eqF.
  case: x => //[r|] n; rewrite ?lte_fin => x0.
  - by rewrite -EFin_expe /lne !gt_eqF// -?EFin_natmul ?exprn_gt0// lnXn.
  - by case: n => //n; rewrite expeS gt0_mulye ?expe_gt0// ?enatmul_pinfty.
  Qed.

  Lemma le_lne1Dx x : -(1) < x -> lne (1 + x) <= x.
  Proof.
  by move=> ?; rewrite -ler_expeR lneK ?expeR_ge1Dx// addrC -(oppeK 1) sube_gt0.
  Qed.
  
  Lemma lne_sublinear x : 0 < x < +oo -> lne x < x.
  Proof.
  by case: x => [?||] /andP [? _]//; rewrite /lne gt_eqF// lte_fin ln_sublinear.
  Qed.
  
  Lemma lne_ge0 x : 1 <= x -> 0 <= lne x.
  Proof.
  case: x => [r rge1||]//; rewrite /lne//.
  by rewrite gt_eqF ?(lt_le_trans ltr01)// lee_fin// ln_ge0.
  Qed.
  
  Lemma lne_lt0 x : 0 < x < 1 -> lne x < 0.
  Proof.
  by move => /andP [x_gt0 x_lt1]; rewrite -ltr_expeR expeR0 lneK.
  Qed.
  
  Lemma lne_gt0 x : 1 < x -> 0 < lne x.
  Proof. by move=> x_gt1; rewrite -ltr_expeR expeR0 lneK// (lt_trans _ x_gt1). Qed.
  
  Fact lne_le0_le0 x : x <= 1 -> lne x <= 0.
  Proof. by move: x => [r||]//?; rewrite /lne; case: ifPn => //?; exact: ln_le0. Qed.
  
  End Lne.

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

Lemma lt0_powR {x} {p} : (x < 0)%R -> x `^ p = 1.
Proof.
move => lts0; rewrite /powR; case : ifP => /eqP eqs0.
- by rewrite eqs0 in lts0; move : lts0; rewrite ltxx.
- move : lts0; rewrite lt_def => /andP [? les0].
  by rewrite (ln0 les0) mulr0 expR0.
Qed.

Lemma powR_eq1 x p : (x `^ p == 1) = (x == 1) || (x < 0) || (p == 0).
Proof.
have [-> | x1] := eqVneq x 1 => //=; first by rewrite powR1 eq_refl.
have [-> | p0] := eqVneq p 0; rewrite ?powRr0 ? eq_refl orbC //=.
case : (ltgtP x 0) => [x0 | x0 | ->]; first by rewrite (lt0_powR x0) eq_refl.
  + rewrite /powR [X in if X then _ else _]eq_sym (lt_eqF x0).
    rewrite -expR0; apply /negP => /eqP /expR_inj /eqP.
    rewrite mulf_eq0 (negbTE p0) -ln1 //= => /eqP /(ln_inj x0 ltr01) /eqP.
    by rewrite (negbTE x1).
  + by rewrite powR0 // eq_sym oner_eq0.
Qed.

Lemma powR_eq0_eq0 x p : x `^ p = 0 -> x = 0.
Proof. by move=> /eqP; rewrite powR_eq0 => /andP[/eqP]. Qed.

Lemma powR_eq1_eq1 x p : x `^ p = 1 -> (x = 1) \/ (x < 0) \/ (p = 0).
Proof. move => /eqP; rewrite powR_eq1 => /orP[/orP[/eqP ->|->]| /eqP ->]; 
  by [left | right;left | right;right].
Qed.

Lemma ger_powR a : 0 < a <= 1 -> {homo powR a : x y /~ y <= x}.
Proof.
move=> /andP[a0 a1] x y xy.
by rewrite /powR gt_eqF// ler_expR ler_wnM2r// ln_le0.
Qed.

Lemma gtr_powR a : 0 < a < 1 -> {homo powR a : x y /~ y < x}.
Proof.
move=> /[dup] /andP [a0 a1] ? x y xy.
by rewrite /powR gt_eqF// ltr_expR ltr_nM2r// ln_lt0//.
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
Implicit Types (s r : R) (x y z : \bar R).

Definition poweR x y := if x == 0 then (y == 0)%:R%:E else expeR (y * lne x).

Local Notation "x `^ y" := (poweR x y).

Lemma poweR_EFin s r : s%:E `^ r%:E = (s `^ r)%:E.
Proof.
rewrite /poweR /powR.
symmetry.
case: ifPn => [/eqP ->|/eqP s0]; first by rewrite ifT//.
rewrite ifF; last by apply/eqP; case.
by rewrite lner//; exact/eqP.
Qed.

Lemma poweRey_gt1 x : 1 < x -> x `^ +oo = +oo.
Proof.
rewrite /poweR => x1; rewrite gt_eqF// ?(lt_trans lte01)//.
by apply/eqP; rewrite expeR_eqy gt0_mulye// lne_gt0.
Qed.

Lemma poweReNy_gt1 x : 1 < x -> x `^ -oo = 0.
Proof.
rewrite /poweR => x1; rewrite gt_eqF// ?(lt_trans lte01)//.
by apply/eqP; rewrite expeR_eq0 gt0_mulNye// lne_gt0.
Qed.

Lemma poweRey_lt1 x : 0 <= x < 1 -> x `^ +oo = 0.
Proof.
rewrite /poweR le_eqVlt => /andP[/orP[/eqP <- _|x0 x1]]; first by rewrite eqxx.
by rewrite gt_eqF//; apply/eqP; rewrite expeR_eq0 lt0_mulye// lne_lt0// x0 x1.
Qed.

Lemma poweReNy_lt1 x : 0 < x < 1 -> x `^ -oo = +oo.
Proof.
rewrite /poweR => /andP[x0 x1];rewrite gt_eqF//; apply/eqP.
by rewrite expeR_eqy lt0_mulNye// lne_lt0// x0 x1.
Qed.

Lemma poweR0_neq0 y : y != 0 -> 0 `^ y = 0.
Proof. by move=> /eqP y0; rewrite /poweR eqxx; case: eqP. Qed.

Lemma poweRyPe x : 0 < x -> +oo `^ x = +oo.
Proof. by rewrite /poweR=> x0; rewrite gt_eqF// gt0_muley. Qed.
  
Lemma poweRyNe x : x < 0 -> +oo `^ x = 0.
Proof. by rewrite /poweR => x0; rewrite gt_eqF//= lt0_muley. Qed.

Lemma poweRe0 x : x `^ 0 = 1.
Proof. by rewrite /poweR; case: ifPn => _; rewrite ?eqxx// mul0e expeR0. Qed.

Lemma poweRe1 x : 0 <= x -> x `^ 1 = x.
Proof.
case: x => //[r|_].
  rewrite lee_fin poweR_EFin /powR.
  case: ifPn => [/eqP -> _|rneq0 rge0]; first by rewrite gt_eqF.
  by rewrite mul1r lnK// posrE lt_neqAle eq_sym rneq0 rge0.
by rewrite /poweR gt_eqF//= gt0_muley.
Qed. 
  
Lemma poweRN x y :
  x \is a fin_num -> y \is a fin_num -> x `^ (- y) = (fine x `^ fine y)^-1%:E.
Proof. by case: x => //r _; case: y => //s _/=; rewrite poweR_EFin powRN. Qed. 

Lemma poweRNye x : -oo `^ x = 1.
Proof. by rewrite /poweR lt_eqF//= mule0 expeR0. Qed.

Lemma lt0_poweR x y : (x < 0) -> (x `^ y = 1).
Proof.
case: x => //[r r0|?]; by rewrite /poweR lt_eqF// /lne ?lt_eqF// ?lt0_ln// mule0 expeR0.
Qed.

Lemma poweR_eqy x r : x `^ r%:E = +oo -> x = +oo.
Proof.
case: x => [x||]; rewrite /poweR//.
case: ifPn => [/eqP -> //|x0].
by rewrite lner.
Qed. 

(*redundant !!!*)
Lemma eqy_poweR x y : 0 < y -> x = +oo -> x `^ y = +oo.
Proof. 
by move: x => [x'||] r0 ->; rewrite poweRyPe.
Qed.

(* TODO: work from here *)

Lemma poweR_lty x y : x < +oo -> -oo < y < +oo -> x `^ y < +oo.
Proof.
case: x => //[r _|_]; case y => //s _; first by rewrite poweR_EFin ltry.
by rewrite /poweR ?mule0 ?ltry.
Qed.  

(*Lemma lty_poweRy x r : r != 0%R -> x `^ r < +oo -> x < +oo. !!!*)
Lemma lty_poweRy x y : 0 < y -> x `^ y < +oo -> x < +oo.
Proof.
move: x => [x| | _]//= y0; first by rewrite ?ltry.
by rewrite /poweR gt_eqF//= gt0_muley.
Qed.

Lemma poweR0e y : y != 0 -> 0 `^ y = 0.
Proof. by rewrite /poweR eqxx; case: eqP. Qed.

Lemma poweR1e y : 1 `^ y = 1.
Proof.
case: y => [r||]; first by rewrite poweR_EFin powR1.
all: by rewrite /poweR gt_eqF// lne1 mule0 expeR0.
Qed. 

(*!!!*)
Lemma fine_poweR x y : x \is a fin_num -> y \is a fin_num -> fine (x `^ y) = ((fine x) `^ (fine y))%R.
Proof. by case: x => //r _; case: y => //s _; rewrite poweR_EFin. Qed.

Lemma poweR_ge0 x y : 0 <= x `^ y.
Proof. by rewrite /poweR; case: ifPn => // _; rewrite expeR_ge0. Qed. 

Lemma poweR_gt0 x y : 0 < x < +oo -> y \is a fin_num -> 0 < x `^ y.
Proof. 
case: x => //[r|] /andP[r0 ry]; case: y => //s.
by rewrite /poweR gt_eqF// expeR_gt0 /lne// gt_eqF// -EFinM ltNyr.
Qed.

Lemma poweR_gt0_lt0r x y : 0 < x -> 0 <= y < +oo -> 0 < x `^ y.
Proof.
case: x => //[r r0|_]; case: y => //[s|]/andP[s0 sy]//.
all: rewrite /poweR gt_eqF// expeR_gt0//= ?gt_eqF//.
- by rewrite -EFinM ltNyr.
- by move: s0; rewrite le_eqVlt => /orP[/eqP <-|s0]; rewrite ?mul0e ?gt0_muley.
Qed. 

Lemma gt0_poweR x y : 0 < y -> 0 <= x -> 0 < x `^ y -> 0 < x.
Proof.
case: x => //[r]. case: y => //[s|_]; rewrite lee_fin lte_fin.
- by rewrite poweR_EFin lte_fin => /gt0_powR /[apply] /[apply].
rewrite /poweR; case: ifPn; rewrite eqe => r0 le0r/=; rewrite ?ltxx// => _.
by rewrite lt_neqAle eq_sym r0 le0r.
Qed.

(*
Lemma poweR_eq0 x r : 
0 <= x -> (x `^ r == 0) = ((x == 0) && (r != 0%R)).
!!!*)
Lemma poweR_eq0y x y : 
  0 <= x ->
    (x `^ y == 0) = ((x == 0) && (y != 0)) || 
                    ((1 < x) && (y == -oo)) ||
                    ((0 < x < 1) && (y == +oo)) ||
                    ((x == +oo) && (y < 0)).
Proof.
move=> xge0.
apply/eqP.
  case: ifPn => [/orP[/orP[/orP[/andP[]|/andP[]]|/andP[]]|/andP[]]|].
  - by move=> /eqP ->; exact: poweR0e.
  - by move=> x1 /eqP ->; exact: poweReNy_gt1.
  - by move=> /andP[_ x1] /eqP ->; apply: poweRey_lt1; rewrite xge0 x1.
  by move=> /eqP ->; exact: poweRyNe.
rewrite !negb_or => /andP[/andP[/andP[]]].
rewrite !negb_and !ltNge !Bool.negb_involutive => /orP h1 /orP h2 /orP h3 /orP h4.
rewrite /poweR.
case: ifPn => [xeq0|xneq0].
  by case: h1 => [|->]; rewrite ?xeq0//=; apply/eqP.
move=> /eqP; rewrite expeR_eq0=> /eqP.
case: h1 => [_|/eqP ->]; last by rewrite mul0e.
case: h3 => [/orP[xle0|xge1]|yneqoo].
- have xeq0 : x = 0 by apply/eqP; rewrite eq_le xge0 xle0.
  by rewrite xeq0 eqxx in xneq0.
- case: h2 => [xle1|yneqnoo].
    have ->: x = 1 by apply/eqP; rewrite eq_le xle1 xge1.
    by rewrite lne1 mule0.
  case: h4 => [xneqoo|yge0].
    move: xge0 xneq0 xge1 xneqoo yneqnoo; case: x => //r.
    rewrite !lee_fin !eqe => rge0 rneq0 rge1 _.
    case: y => //[s _|_]; first by rewrite lner.
    rewrite lner// mulyr.
    move: rge1; rewrite le_eqVlt eq_sym => /orP[/eqP ->|rgt1]; first by rewrite ln1 sgr0 mul0e.
    by rewrite gtr0_sg ?ln_gt0// mul1e.
  move: yneqnoo yge0. case: y => //[s _|_ _].
    rewrite lee_fin => sge0.
    move: xge0 xneq0 xge1; case: x => //[r rge0 rneq0 rge1|_ _ _/=]; first by rewrite lner.
    move: sge0; rewrite le_eqVlt mulry => /orP[/eqP <-|sge0]; first by rewrite sgr0 mul0e.
    by rewrite gtr0_sg// mul1e.
  move: xge0 xneq0 xge1; case: x => //=[r|]; last by rewrite mulyy.
  rewrite !lee_fin !eqe => rge0 rneq0 rge1.
  rewrite gt_eqF// ?(lt_le_trans _ rge1)// mulyr.
  move: rge1; rewrite le_eqVlt eq_sym => /orP[/eqP ->|rgt1]; first by rewrite ln1 sgr0 mul0e.
  by rewrite gtr0_sg ?ln_gt0// mul1e.
move: h2 h4 yneqoo; case: y => //[s|] h2 h4 _.
  case: h4 => //[|sge0]; first by move: xge0 xneq0 h2; case: x => //r ? ? ? ?; rewrite lner.
  move: xge0 xneq0 h2; case: x => //[r|] ? ? ?; first by rewrite lner.
  move: sge0; rewrite /= lee_fin le_eqVlt mulry => /orP[/eqP <-|sgt0]; first by rewrite sgr0 mul0e.
  by rewrite gtr0_sg// mul1e.
case: h2 => //; rewrite le_eqVlt => /orP[/eqP ->|xlt1]; first by rewrite lne1 mule0.
move: xge0 xneq0 xlt1 h4; case: x => //r; rewrite !lee_fin !lte_fin !eqe => rge0 rneq0 rlt1 _.
rewrite lner// mulNyr ltr0_sg//=; first by rewrite EFinN mulNe mul1e.
by rewrite ln_lt0// rlt1 lt_neqAle eq_sym rneq0 rge0.
Qed.

Lemma gt0_ler_poweR z : 0 <= z ->
  {in `[0, +oo] &, {homo poweR ^~ z : x y / x <= y >-> x <= y}}.
Proof.
move=> z0/= + y; case=> //= [x /[1!in_itv]/= /andP[xint _]| _ _]; last first.
  by rewrite leye_eq => /eqP ->; rewrite lexx.
move: z0; rewrite le_eqVlt => /orP[/eqP <- _ _|z0]; first by rewrite !poweRe0 lexx.
case : y => //= [y /[1!in_itv]/= /andP[yint _] xy| _ _]; last by rewrite poweRyPe// leey.
move: z0; case: z => //[r|_].
  by rewrite lte_fin => r0; rewrite !poweR_EFin !lee_fin ge0_ler_powR// ltW.
move: xy.
have [->|xneq1] := @eqVneq _ x 1%R.
  rewrite poweR1e le_eqVlt => /orP[/eqP <-|ygt1]; first by rewrite poweR1e lexx.
  by rewrite poweRey_gt1// leey.
have /orP[] := @real_leVge _ x 1 (num_real x) (num_real 1); rewrite le_eqVlt.
  move=> /orP[/eqP xeq1|xlt1 xy]; first by rewrite xeq1 eqxx in xneq1.
  by rewrite poweRey_lt1// ?xint//= poweR_ge0.
move=> /orP[/eqP xeq1|xgt1 xy]; first by rewrite xeq1 eqxx in xneq1.
by rewrite !poweRey_gt1// (lt_le_trans _ xy).
Qed.

Lemma fin_num_poweR x y : x \is a fin_num -> y \is a fin_num -> x `^ y \is a fin_num.
Proof. by case: x => //r; case: y => //s _ _; rewrite poweR_EFin. Qed.

Lemma poweRM x y r : (r != 0)%R -> 0 <= x -> 0 <= y -> (x * y) `^ r%:E = x `^ r%:E * y `^ r%:E.
Proof.
have [->|rN0] := eqVneq r 0%R; first by rewrite !poweRe0 mule1.
have powyrM s : (0 <= s)%R -> (+oo * s%:E) `^ r%:E = +oo `^ r%:E * s%:E `^ r%:E.
  case: ltgtP => // [s_gt0 _|<- _]; last first.
    by rewrite poweR0e// !mule0 poweR0e.
  rewrite gt0_mulye//; case: (ltgtP r 0%R) rN0 => // p0 _.
    by rewrite poweRyNe ?mul0e.
  rewrite poweRyPe// gt0_mulye// poweR_gt0_lt0r//.
  by rewrite lee_fin le0r p0 orbC ?ltry.
case: x y => [x||] [y||]// _ x0 y0.
- by rewrite ?poweR_EFin -EFinM; f_equal; rewrite powRM.
- by rewrite muleC [X in _ = X]muleC powyrM.
- by rewrite powyrM.
rewrite mulyy; move: rN0; case: (ltgtP r 0%R) => // rN0 _.
  by rewrite poweRyNe ?mule0.
by rewrite poweRyPe ?mulyy.
Qed.
  
Definition poweRrM_def x y z :=
  ((x <= 1) || (0 <= y) || (x*y*z < +oo)) && ((1 <= x) || (-oo < y*z)).

Lemma poweRrM_defE x y z :
  ((x <= 1) || (0 <= y) || (x*y*z < +oo)) && ((1 <= x) || (-oo < y*z)) = 
    if 1 < x then (0 <= y) || (x*y*z < +oo) else (-oo < y*z) || (x == 1).
Proof.
case: ifPn => h.
- by rewrite (@ltW _ _ 1 x)//= andbT leNgt h.
- by rewrite leNgt h/= eq_le (leNgt x 1) h/= orbC.
Qed.

Lemma poweRrM (x y z : \bar R) : poweRrM_def x y z -> x `^ (y * z) = (x `^ y) `^ z. 
Proof.
rewrite /poweRrM_def; have [x0|x0|->] := (ltgtP x 0); last first.
- have [->|y0] := eqVneq y 0; have [->|z0] := eqVneq z 0;
  by rewrite ?mul0e ?mule0 ?poweRe0 ?poweR1e ?poweR0e ?mule_neq0.
- move: x y z x0 => [x||]//[y||]//[z||]// => x0; 
  try have [y0|y0|y0]:= (ltgtP y%:E 0);try have [z0|z0|z0]:= (ltgtP z%:E 0);
  try have ?:= negbT (gt_eqF y0);try have ?:= negbT (gt_eqF z0);
  try have yz0:= mule_gt0 y0 z0;try have yz0:= mule_lt0_gt0 y0 z0;
  try have yz0:= mule_gt0_lt0 y0 z0;try have yz0:= mule_lt0_lt0 y0 z0;
  last first; rewrite ?y0 ?z0 ?mulyy ?mulNyy ?mulNyNy ?mulyNy ?mul0e ?mule0
  ?(gt0_muleNy y0) ?(lt0_muleNy y0) ?(gt0_muley y0) ?(lt0_muley y0)
  ?(gt0_mulNye z0) ?(lt0_mulNye z0) ?(gt0_mulye z0) ?(lt0_mulye z0).
all:
  rewrite ?leye_eq ?leeNy_eq ?leey ?mulNyy ?mulNyy ?orbT ?(gt_eqF ltNy0)
    ?(lt0_mulye y0) ?(gt0_muleNy x0) ?(gt0_mulNye z0) ?(lt0_mulNye z0).
all: try
  by rewrite 
       ?(poweRyPe yz0) ?(poweRyNe yz0) ?(poweRyNe ltNy0) ?(poweRyPe lt0y) 
       ?(poweRyPe y0) ?(poweRyNe y0) ?(poweRyPe z0) ?(poweRyNe z0) ?poweRe0 
       ?poweR0e ?poweR1e ?(poweRyNe ltNy0) ?(poweRyPe lt0y) ?(poweRyPe y0) 
       ?(poweRyNe y0) ?(poweRyPe z0) ?(poweRyNe z0).
all: try by (rewrite -EFinM !poweR_EFin; f_equal; rewrite powRrM).
all: try have [x1|x1|->] := (ltgtP x%:E 1); rewrite ?poweR1e //.
all: try (have gelt0x1 : 0 <= x%:E < 1; 
          first by apply /andP; split => //; rewrite le_eqVlt x0 orbC). 
all: try (have ltlt0x1 : 0 < x%:E < 1; first by apply /andP; split).
all: try (have ? : (0 < x <= 1)%R; 
          first by apply /andP; split => //=; rewrite le_eqVlt -lte_fin x1 orbC).
all: try (have ?: (y <= 0)%R;first by rewrite le_eqVlt -lte_fin y0 orbC).
all: try (have ?: (1 <= x)%R;first by rewrite le_eqVlt -lte_fin x1 orbC).
all: try (have ? : x%:E `^ y%:E != 1; 
    first by rewrite poweR_EFin eqe; apply /negP; rewrite powR_eq1 -eqe 
    ?(lt_eqF x1) ?(gt_eqF x1) -eqe ?(lt_eqF y0) ?(gt_eqF y0) orbC//=;
    move=> ltx0;rewrite -falseE -(@ltxx _ R 0%R);apply: (lt_trans _ ltx0)). 
all: try (have ? : 1 != x%:E `^ y%:E; first by rewrite eq_sym).
all: try (have ? : x%:E `^ y%:E != 0%R; first by rewrite poweR_EFin eqe;
          apply /negP; rewrite powR_eq0 -eqe (gt_eqF x0)).
all: have ? := poweR_ge0.
all: rewrite ?(poweRey_lt1 gelt0x1) ?(poweReNy_lt1 ltlt0x1)
       ?(poweReNy_gt1 x1) ?(poweRey_gt1 x1).
all: try by rewrite ?(poweRyNe ltNy0) ?(poweRyPe lt0y) ?(poweRyNe z0)
              ?(poweRyPe z0) ?(poweReNy_gt1 x1) ?(poweRey_gt1 x1) ?poweR0e.
all: try by rewrite muleAC ?(gt0_muleNy x0) ?(lt0_mulNye y0).
3,5,6: rewrite ?poweReNy_lt1 ?poweRey_lt1 ?lt_def//.
1,2,6: rewrite ?poweReNy_gt1 ?poweRey_gt1 ?lt_def//.
all: try do 2 (apply /andP; split) =>//; try (apply /andP; split) =>//;
       rewrite ?poweR_EFin ?lee_fin -?(powRr0 x).
all: try by apply /ger_powR => //; rewrite le0r; apply /orP; right.
all: try by apply /ler_powR => //; rewrite le0r; apply /orP; right.
by rewrite [X in _ = X `^ _]lt0_poweR // poweR1e lt0_poweR.
Qed.

Lemma poweRAC x y z : 
  poweRrM_def x y z -> 
  (x `^ y) `^ z = (x `^ z) `^ y.
Proof.
  move=> ACdef. rewrite -!poweRrM // /poweRrM_def muleC // [X in -oo < X]muleC.
  move: ACdef=> /andP [/orP[/orP [lex1 | y0] | xyz] /orP [gex1| yz]];
  rewrite ?gex1 ?lex1 ?yz andbC //= orbC //= ?le_eqVlt; 
  case (ltgtP z 0) => [z0|z0|->]; rewrite ?eq_refl ?z0 ?orbT //=; 
  try by rewrite muleA [X in X * z]muleC xyz ?orbT.
  - rewrite (_ : y * (x * z) < +oo) //.
  apply: le_lt_trans; last by apply lt0y. 
  by repeat apply: mule_ge0_le0 => //;
      rewrite ?le_eqVlt ?z0 ?(lt_le_trans lte01 gex1) ?orbT.
  - case (ltgtP x 0) => [x0|x0|->]; rewrite ?(lt_trans x0 lte01) 
      ?mul0e ?mule0 ?lte01 ?orbT //=.
    rewrite (_ : (y * (x * z) < +oo)) ?orbT //. 
    apply: le_lt_trans; last by apply: lt0y.
    repeat apply: mule_ge0_le0 => //; rewrite ?le_eqVlt ?x0 ?z0 ?orbT //.
Qed.
    

(* Definition poweRD_def x y z := ((y + z == 0) ==> *)
(*   ((x != 0) && ((x \isn't a fin_num) ==> (y == 0) && (z == 0)))). *)
(* Notation "x '`^?' ( y +? z )" := (poweRD_def x y z) : ereal_scope. *)

(* Lemma poweRD_defE x y z : *)
(*   x `^?(y +? z) = (y + z == 0 ==> *)
(*   ((x != 0) && ((x \isn't a fin_num) ==> (y == 0%R) && (z == 0%R)))). *)
(* Proof. by []. Qed. *)

(* Lemma poweRB_defE x y z : *)
(*   x `^?(y +? - z) = ((y == z) ==> *)
(*   ((x != 0) && ((x \isn't a fin_num) ==> (y == 0%R) && (z == 0%R)))). *)
(* Proof. by rewrite poweRD_defE subr_eq0 oppr_eq0. Qed. *)

(* Lemma add_neq0_poweRD_def x r s : (r + s != 0)%R -> x `^?(r +? s). *)
(* Proof. by rewrite poweRD_defE => /negPf->. Qed. *)

(* Lemma add_neq0_poweRB_def x r s : (r != s)%R -> x `^?(r +? - s). *)
(* Proof. by rewrite poweRB_defE => /negPf->. Qed. *)

(* Lemma nneg_neq0_poweRD_def x r s : x != 0 -> (r >= 0)%R -> (s >= 0)%R -> *)
(*   x `^?(r +? s). *)
(* Proof. *)
(* move=> xN0 rge0 sge0; rewrite /poweRD_def xN0/=. *)
(* by case: ltgtP rge0 => // [r_gt0|<-]; case: ltgtP sge0 => // [s_gt0|<-]//=; *)
(*    rewrite ?addr0 ?add0r ?implybT// gt_eqF//= ?addr_gt0. *)
(* Qed. *)

(* Lemma nneg_neq0_poweRB_def x r s : x != 0 -> (r >= 0)%R -> (s <= 0)%R -> *)
(*   x `^?(r +? - s). *)
(* Proof. by move=> *; rewrite nneg_neq0_poweRD_def// oppr_ge0. Qed. *)

(* Lemma poweRD x y z : x `^?(y +? z) -> x `^ (y + z) = x `^ y * x `^ z. *)
(* Proof. *)
(* rewrite /poweRD_def. *)
(* have [->|r0]/= := eqVneq r 0%R; first by rewrite add0r poweRe0 mul1e. *)
(* have [->|s0]/= := eqVneq s 0%R; first by rewrite addr0 poweRe0 mule1. *)
(* case: x => // [t|/=|/=]; rewrite ?(negPf r0, negPf s0, implybF); last 2 first. *)
(* - move=> /negPf->; rewrite mulyy. *)
(* - by move=> /negPf->; rewrite mule0. *)
(* rewrite !poweR_EFin eqe => /implyP/(_ _)/andP cnd. *)
(* by rewrite powRD//; apply/implyP => /cnd[]. *)
(* Qed. *)


Definition poweRD_def x y z : bool :=
  match x, y, z with
  | x%:E , y%:E , z%:E => (y + z == 0%R) ==> (x != 0%R)
  | x%:E , -oo , +oo => (x <= 0)%R || (1 <= x)%R
  | x%:E , +oo , -oo => (x <= 0)%R || (1 <= x)%R
  | x%:E , _ , _ => x == 0%R
  | +oo , y%:E , z%:E =>
      if (y + z < 0)%R then ((y <= 0) && (z <= 0))%R else
      if (y + z > 0)%R then ((y >= 0)%R && (z >= 0))%R else
      ((y == 0) && (z == 0))%R
  | +oo , +oo , z%:E => (z > 0)%R
  | +oo , y%:E , +oo => (y > 0)%R
  | _ , _ , _ => true
  end. 
Notation "x '`^?' ( y +? z )" := (poweRD_def x y z) : ereal_scope.

Lemma poweRD x y z : x `^? ( y +? z ) -> x `^ (y + z) = x `^ y * x `^ z.
Proof.
case: x => [a||]; case: y => [b||]; case: z => [c||] //=.
by rewrite -EFinD !poweR_EFin -EFinM => Ddef; f_equal; rewrite (powRD Ddef).
all: try by move => /eqP ->;
  rewrite ?addey ?addye ?addNye ?addeNy
    ?(@poweR0e +oo) ?(@poweR0e -oo) ?mule0 ?mul0e.
all: try (rewrite ?addeNy ?addNye => /orP [|];
  case: (ltrgtP a 0) => // a0 +;
  case: (ltrgtP a 1) => // a1).
all: try by rewrite !lt0_poweR ?lte_fin ?mul1e.
all: try by rewrite a0 !poweR0e // mul0e.
all: try by rewrite ?poweReNy_gt1 ?poweRey_gt1 ?mule0 ?mul0e.
all: try by rewrite a1 !poweR1e mule1.
repeat case: ifPn; rewrite -EFinD;
  case: (ltrgtP b 0);case: (ltrgtP c 0);case: (ltrgtP (b+c) 0)=> c0 b0 bc0 //=.
  all: try by rewrite ?b0 ?c0 ?bc0 ?addr0 ?add0r ?poweRe0
    ?(@poweRyNe b%:E) ?(@poweRyNe c%:E) ?(@poweRyNe (b+c)%:E) 
    ?(@poweRyPe b%:E) ?(@poweRyPe c%:E) ?(@poweRyPe (b+c)%:E)
    ?mul0e ?mule0 ?mul1e.
  all: try by rewrite ?b0 ?c0 ?bc0 ?addr0 ?add0r ?poweRe0
    ?(@poweRyPe b%:E) ?(@poweRyPe c%:E) ?(@poweRyPe (b+c)%:E)
    ?mul1e ?mulyy ?gt0_mulye.
all: try by move => b0; rewrite ?addey ?addye ?poweRyPe ?gt0_muley.
all: try by rewrite ?addeNy ?addNye poweRyNe ?mule0.
all: by rewrite addNye poweRyNe // ?mul0e.
Qed.

(*


Lemma poweRD x y z : 0 <= y -> 0 <= z -> 0 <= x -> ((y + z == 0) ==> (x != 0)) -> x `^ (y + z) = x `^ y * x `^ z.
Proof.
have [->|] := eqVneq x 1; first by rewrite !poweR1e mule1.
case: y => //[s +s0|+_]; case: z => //[t +t0|+_]; case: x => //[r rneq1 r0|_ _] h.
all: rewrite -?EFinD ?addey// ?addye//.
- by rewrite !poweR_EFin powRD.
all: have poweRyy: +oo `^ +oo = +oo by rewrite poweRyPe.
all: rewrite ?poweRyy ?mulyy//.
- move: s0; rewrite le_eqVlt eqe => /orP[/eqP <-|s0]; first by rewrite add0r poweRe0 mul1e.
  move: t0; rewrite le_eqVlt eqe => /orP[/eqP <-|t0]; first by rewrite addr0 poweRe0 mule1.
  by rewrite !poweRyPe// ?lte_fin ?addr_gt0// mulyy.
- have /orP[rle1|rge1] := @real_leVge _ r 1 (num_real r) (num_real 1).
    by rewrite poweRey_lt1 ?mule0// r0 lt_neqAle rneq1 lee_fin rle1.
  rewrite poweRey_gt1; last by rewrite lt_neqAle eq_sym rneq1 lee_fin rge1.
  by rewrite poweR_EFin mulry gtr0_sg ?mul1e// powR_gt0// (lt_le_trans _ rge1).
- admit. (* move: s0; rewrite lee_fin le_eqVlt => /orP[/eqP <-|]. admit. *)
(* case: x => [r||]/=. *)
(* move=> y0 z0. *)
(* rewrite /poweR. *)
(* case: ifPn => x0; last first. *)
(* move: x0; case: x => [r r0|_|_]. *)
(* rewrite muleDl ?lner//. *)

(* rewrite /poweRD_def. *)
(* have [->|r0]/= := eqVneq r 0%R; first by rewrite add0r poweRe0 mul1e. *)
(* have [->|s0]/= := eqVneq s 0%R; first by rewrite addr0 poweRe0 mule1. *)
(* case: x => // [t|/=|/=]; rewrite ?(negPf r0, negPf s0, implybF); last 2 first. *)
(* - move=> /negPf->; rewrite mulyy. *)
(* - by move=> /negPf->; rewrite mule0. *)
(* rewrite !poweR_EFin eqe => /implyP/(_ _)/andP cnd. *)
(* by rewrite powRD//; apply/implyP => /cnd[]. *)
(* Qed. *)
Admitted.
*)

(*
Lemma poweRB x y z : (* x `^?(r +? - s) -> *)
  0 <= y -> 0 <= - z -> 0 <= x -> ((y + - z == 0) ==> (x != 0)) -> x `^ (y - z) = x `^ y * x `^ (- z).
Proof.
move=> y0 z0 x0 h. rewrite poweRD //.
Proof. by move=> y0 z0 x0 h; rewrite poweRD. Qed.
  *)

Lemma poweRB x y z : x `^?(y +? - z) -> x `^ (y - z) = x `^ y * x `^ (- z).
Proof. by move=> rs; rewrite poweRD. Qed.

Lemma poweR12_sqrt x : 0 <= x -> x `^ (2^-1%:E) = sqrte x.
Proof.
move: x => [x|_|//]; last by rewrite poweRyPe.
by rewrite lee_fin => x0 /=; rewrite poweR_EFin powR12_sqrt.
Qed.

Lemma conjugate_poweR x y r s : 0 <= x -> 0 <= y ->
  (0 < r)%R -> (0 < s)%R -> (r^-1 + s^-1 = 1)%R ->
  x * y <= (x `^ r%:E) * (r^-1%:E) + (y `^ s%:E) * (s^-1%:E).
Proof.
case: (eqVneq 0 x) => [<-|]; case: (eqVneq 0 y) => [<-|];
[move=> _ _ |move=> neq0x le0x _ |move=> neq0x le0x _ |
move=> neq0y neq0x le0x le0y ] => r0 s0 rs1;
rewrite ?poweR0e ?mul0e ?mule0 ?add0e ?le_refl ?negbT ?gt_eqF ?adde_ge0 
  ?mule_ge0 ?poweR_ge0 ?lee_fin ?invr_ge0 ?(ltW r0) ?(ltW s0)//.
have lt0x : 0 < x; first by rewrite lt_def eq_sym neq0x le0x.
have lt0y : 0 < y; first by rewrite lt_def eq_sym neq0y le0y.
move: x y neq0y neq0x le0x le0y lt0y lt0x=> 
  [x||][y||]// neq0y neq0x le0x le0y lt0y lt0x;
rewrite ?poweR_EFin -?EFinM -?EFinD ?lee_fin ?conjugate_powR
?poweRyPe ?gt0_muley ?gt0_mulye ?lte_fin ?invr_gt0 
?addye ?addey ?negbT ?gt_eqF ?poweR_EFin -?EFinM ?ltNyr //.
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
