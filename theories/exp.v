(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import mathcomp_extra.
Require Import reals ereal nsatz_realtype.
Require Import signed topology normedtype landau sequences derive realfun.
Require Import itv convex.

(******************************************************************************)
(*               Theory of exponential/logarithm functions                    *)
(*                                                                            *)
(* This file defines exponential and logarithm functions and develops their   *)
(* theory.                                                                    *)
(*                                                                            *)
(* * Differentiability of series (Section PseriesDiff)                        *)
(*   This formalization is inspired by HOL-Light (transc.ml). This part is    *)
(*   temporary: it should be subsumed by a proper theory of power series.     *)
(*         pseries f x == [series f n * x ^ n]_n                              *)
(*   pseries_diffs f i == (i + 1) * f (i + 1)                                 *)
(*                                                                            *)
(*                ln x == the natural logarithm                               *)
(*              s `^ r == power function, in ring_scope (assumes s >= 0)      *)
(*              e `^ r == power function, in ereal_scope (assumes e >= 0)     *)
(*          riemannR a == sequence n |-> 1 / (n.+1) `^ a where a has a type   *)
(*                        of type realType                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* PR to mathcomp in progress *)
Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE. Qed.
#[global] Hint Resolve normr_nneg : core.
(* /PR to mathcomp in progress *)

Section PseriesDiff.

Variable R : realType.

Definition pseries f (x : R) := [series f i * x ^+ i]_i.

Fact is_cvg_pseries_inside_norm f (x z : R) :
  cvg (pseries f x) -> `|z| < `|x| -> cvg (pseries (fun i => `|f i|) z).
Proof.
move=> Cx zLx; have [K [Kreal Kf]] := cvg_series_bounded Cx.
have Kzxn n : 0 <= `|K + 1| * `|z ^+ n| / `|x ^+ n|  by rewrite !mulr_ge0.
apply: normed_cvg.
apply: series_le_cvg Kzxn _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pmul || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply Kf => //; rewrite (lt_le_trans _ (ler_norm _))// ltr_addl.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivr_mulr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric `|K + 1| `|z / x|); last first.
  by apply/funext => i /=; rewrite normrM exprMn mulrA normfV !normrX exprVn.
by apply: is_cvg_geometric_series; rewrite normr_id.
Qed.

Fact is_cvg_pseries_inside f (x z : R) :
  cvg (pseries f x) -> `|z| < `|x| -> cvg (pseries f z).
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
  cvg (pseries (pseries_diffs f) x) -> series s -->
  lim (pseries (pseries_diffs f) x).
Proof.
move=> s Cx; rewrite -[lim _]subr0 /pseries [X in X --> _]/series /=.
rewrite [X in X --> _](_ : _ = (fun n => \sum_(0 <= i < n)
    pseries_diffs f i * x ^+ i - n%:R * f n * x ^+ n.-1)); last first.
  by rewrite funeqE => n; rewrite pseries_diffs_sumE addrK.
by apply: cvgB => //; rewrite -cvg_shiftS; exact: cvg_series_cvg_0.
Qed.

Lemma is_cvg_pseries_diffs_equiv f x :
  cvg (pseries (pseries_diffs f) x) -> cvg [series i%:R * f i * x ^+ i.-1]_i.
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
rewrite ler_pmul2r ?normr_gt0//.
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
apply: ler_pmul => //.
  by rewrite normrX ler_expn2r// qualifE (le_trans _ zLK).
apply: le_trans (_ : d.+1%:R * K ^+ d <= _); last first.
  rewrite ler_wpmul2r //; first by rewrite exprn_ge0 // (le_trans _ zLK).
  by rewrite ler_nat ltnS /d -subn1 -subnDA leq_subr.
rewrite (le_trans (ler_norm_sum _ _ _))//.
rewrite mulr_natl -[X in _ *+ X]subn0 -sumr_const_nat ler_sum_nat//= => j jd1.
rewrite -[in leRHS](subnK (_ : j <= d)%nat) -1?ltnS // addnC exprD normrM.
by rewrite ler_pmul// normrX ler_expn2r// qualifE (le_trans _ zLK).
Qed.

Lemma pseries_snd_diffs (c : R^nat) K x :
  cvg (pseries c K) ->
  cvg (pseries (pseries_diffs c) K) ->
  cvg (pseries (pseries_diffs (pseries_diffs c)) K) ->
  `|x| < `|K| ->
  is_derive x 1
    (fun x => lim (pseries c x))
    (lim (pseries (pseries_diffs c) x)).
Proof.
move=> Ck CdK CddK xLK; rewrite /pseries.
set s := (fun n : nat => _); set (f := fun x0 => _).
suff hfxs : h^-1 *: (f (h + x) - f x) @[h --> 0^'] --> lim (series s).
  have F : f^`() x = lim (series s) by apply: cvg_lim hfxs.
  have Df : derivable f x 1.
    move: hfxs; rewrite /derivable [X in X @ _](_ : _ =
        (fun h => h^-1 *: (f (h%:A + x) - f x))) /=; last first.
      by apply/funext => i //=; rewrite [i%:A]mulr1.
    by move=> /(cvg_lim _) -> //.
  by constructor; [exact: Df|rewrite -derive1E].
pose sx := fun n : nat => c n * x ^+ n.
have Csx : cvg (pseries c x) by apply: is_cvg_pseries_inside Ck _.
pose shx := fun h (n : nat) => c n * (h + x) ^+ n.
suff Cc : lim (h^-1 *: (series (shx h - sx))) @[h --> 0^'] --> lim (series s).
  apply: cvg_sub0 Cc.
  apply/cvgrPdist_lt => eps eps_gt0 /=.
  near=> h; rewrite sub0r normrN /=.
  rewrite (le_lt_trans _ eps_gt0)//.
  rewrite normr_le0 subr_eq0 -/sx -/(shx _); apply/eqP.
  have Cshx' : cvg (series (shx h)).
    apply: is_cvg_pseries_inside Ck _.
    rewrite (le_lt_trans (ler_norm_add _ _))// -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    rewrite (lt_le_trans H)// ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  by rewrite limZr; [rewrite lim_seriesB|exact: is_cvg_seriesB].
apply: cvg_zero => /=.
suff Cc : lim
    (series (fun n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1)))
    @[h --> 0^'] --> (0 : R).
  apply: cvg_sub0 Cc.
  apply/cvgrPdist_lt => eps eps_gt0 /=.
  near=> h; rewrite sub0r normrN /=.
  rewrite (le_lt_trans _ eps_gt0)// normr_le0 subr_eq0; apply/eqP.
  have Cs : cvg (series s) by apply: is_cvg_pseries_inside CdK _.
  have Cs1 := is_cvg_pseries_diffs_equiv Cs.
  have Fs1 := pseries_diffs_equiv Cs.
  set s1 := (fun i => _) in Cs1.
  have Cshx : cvg (series (shx h)).
    apply: is_cvg_pseries_inside Ck _.
    rewrite (le_lt_trans (ler_norm_add _ _))// -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    rewrite (lt_le_trans H)// ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  have C1 := is_cvg_seriesB Cshx Csx.
  have Ckf := @is_cvg_seriesZ _ _ h^-1 C1.
  have Cu : (series (h^-1 *: (shx h - sx)) - series s1) x0 @[x0 --> \oo] -->
      lim (series (h^-1 *: (shx h - sx))) - lim (series s).
    by apply: cvgB.
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
have xLr : `|x| < r by rewrite ltr_pdivl_mulr // mulr2n mulrDr mulr1 ltr_add2l.
have rLx : r < `|K| by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 ltr_add2r.
have r_gt0 : 0 < r by apply: le_lt_trans xLr.
have rNZ : r != 0by case: ltrgt0P r_gt0.
apply: (@lim_cvg_to_0_linear _
  (fun n => `|c n| * n%:R * (n.-1)%:R * r ^+ n.-2)
  (fun h n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1))
  (r - `|x|)); first by rewrite subr_gt0.
- have : cvg [series `|pseries_diffs (pseries_diffs c) n| * r ^+ n]_n.
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
  rewrite normrM -!mulrA ler_wpmul2l //.
  rewrite (le_trans (pseries_diffs_P3 _ _ (ltW xLr) _))// ?mulrA -?normr_gt0//.
  by rewrite (le_trans (ler_norm_add _ _))// -(subrK `|x| r) ler_add2r ltW.
Unshelve. all: by end_near. Qed.

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

Lemma expR_ge1Dx x : 0 <= x -> 1 + x <= expR x.
Proof.
move=> x_gt0; rewrite /expR.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = lim (series (f x)).
  by apply/esym/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => [] [|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Unshelve. all: by end_near. Qed.

Lemma exp_coeffE x : exp_coeff x = (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /exp_coeff /= mulrC. Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma expRE :
  expR = fun x => lim (pseries (fun n => (fun n => (n`!%:R)^-1) n) x).
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
by move=> x_gt0; rewrite (lt_le_trans _ (expR_ge1Dx (ltW x_gt0)))// ltr_addl.
Qed.

Lemma expR_gt0 x : 0 < expR x.
Proof.
case: (ltrgt0P x) => [x_gt0|x_gt0|->]; last by rewrite expR0.
- exact: lt_trans (pexpR_gt1 x_gt0).
- have F : 0 < expR (- x) by rewrite (lt_trans _ (pexpR_gt1 _))// oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expRxMexpNx_1.
Qed.

Lemma expR_ge0 x : 0 <= expR x. Proof. by rewrite ltW// expR_gt0. Qed.

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

Lemma expRMm n x : expR (n%:R * x) = expR x ^+ n.
Proof.
elim: n x => [x|n IH x] /=; first by rewrite mul0r expr0 expR0.
by rewrite exprS -nat1r mulrDl mul1r expRD IH.
Qed.

Lemma expR_gt1 x:  (1 < expR x) = (0 < x).
Proof.
case: ltrgt0P => [x_gt0| xN|->]; last by rewrite expR0.
- by rewrite (pexpR_gt1 x_gt0).
- apply/idP/negP.
  rewrite -[x]opprK expRN -leNgt invf_cp1 ?expR_gt0 //.
  by rewrite ltW // pexpR_gt1 // lter_oppE.
Qed.

Lemma expR_lt1 x:  (expR x < 1) = (x < 0).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; last by rewrite expR0.
- by apply/idP/negP; rewrite -leNgt ltW // expR_gt1.
- by rewrite -[x]opprK expRN invf_cp1 ?expR_gt0 // expR_gt1 lter_oppE.
Qed.

Lemma expRB x y : expR (x - y) = expR x / expR y.
Proof. by rewrite expRD expRN. Qed.

Lemma ltr_expR : {mono (@expR R) : x y / x < y}.
Proof.
move=> x y.
by  rewrite -[in LHS](subrK x y) expRD ltr_pmull ?expR_gt0 // expR_gt1 subr_gt0.
Qed.

Lemma ler_expR : {mono (@expR R) : x y / x <= y}.
Proof.
move=> x y.
case: (ltrgtP x y) => [xLy|yLx|<-]; last by rewrite lexx.
- by rewrite ltW // ltr_expR.
- by rewrite leNgt ltr_expR yLx.
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
- rewrite expR0; have [_| |] := ltrgtP (1- x) (expR x - x).
  + by rewrite subr_le0 x_ge1 subr_ge0 (le_trans _ (expR_ge1Dx _)) ?ler_addr.
  + by rewrite ltr_add2r expR_lt1 ltNge x_ge0.
  + rewrite subr_le0 x_ge1 => -> /=; rewrite subr_ge0.
    by rewrite (le_trans _ (expR_ge1Dx x_ge0)) ?ler_addr.
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

Section Ln.
Variable R : realType.
Implicit Types x : R.

Notation exp := (@expR R).

Definition ln x : R := xget 0 [set y | exp y == x ].

Fact ln0 x : x <= 0 -> ln x = 0.
Proof.
rewrite /ln; case: xgetP => //= y _ /eqP yx x0.
by have := expR_gt0 y; rewrite yx => /(le_lt_trans x0); rewrite ltxx.
Qed.

Lemma expK : cancel exp ln.
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
Proof. by apply/expR_inj; rewrite lnK// ?expR0// qualifE. Qed.

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
by move: x0; rewrite !qualifE invr_gt0.
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

Lemma lnX n x : 0 < x -> ln(x ^+ n) = ln x *+ n.
Proof.
move=> x_gt0; elim: n => [|n ih] /=; first by rewrite expr0 ln1 mulr0n.
by rewrite !exprS lnM ?qualifE// ?exprn_gt0// mulrS ih.
Qed.

Lemma le_ln1Dx x : 0 <= x -> ln (1 + x) <= x.
Proof.
move=> x_ge0; rewrite -ler_expR lnK ?expR_ge1Dx //.
by apply: lt_le_trans (_ : 0 < 1) _; rewrite // ler_addl.
Qed.

Lemma ln_sublinear x : 0 < x -> ln x < x.
Proof.
move=> x_gt0; apply: lt_le_trans (_ : ln (1 + x) <= _).
  by rewrite -ltr_expR !lnK ?qualifE ?addr_gt0 // ltr_addr.
by rewrite -ler_expR lnK ?qualifE ?addr_gt0// expR_ge1Dx // ltW.
Qed.

Lemma ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
by move=> x_ge1; rewrite -ler_expR expR0 lnK// qualifE (lt_le_trans _ x_ge1).
Qed.

Lemma ln_gt0 x : 1 < x -> 0 < ln x.
Proof.
by move=> x_gt1; rewrite -ltr_expR expR0 lnK // qualifE (lt_trans _ x_gt1).
Qed.

Lemma continuous_ln x : 0 < x -> {for x, continuous ln}.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: nbhs_singleton (near_can_continuous _ _); near=> z; first exact: expK.
by apply: continuous_expR.
Unshelve. all: by end_near. Qed.

Global Instance is_derive1_ln (x : R) : 0 < x -> is_derive x 1 ln x^-1.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: (@is_derive_inverse R expR); first by near=> z; apply: expK.
  by near=>z; apply: continuous_expR.
by rewrite lnK // lt0r_neq0.
Unshelve. all: by end_near. Qed.

End Ln.

Section PowerPos.
Variable R : realType.
Implicit Types a x : R.

Definition power_pos a x :=
  if a == 0 then (x == 0)%:R else expR (x * ln a).

Local Notation "a `^ x" := (power_pos a x).

Lemma power_pos_ge0 a x : 0 <= a `^ x.
Proof. by rewrite /power_pos; case: ifPn => // _; exact: expR_ge0. Qed.

Lemma power_pos_gt0 a x : 0 < a -> 0 < a `^ x.
Proof. by move=> a0; rewrite /power_pos gt_eqF// expR_gt0. Qed.

Lemma power_posr1 a : 0 <= a -> a `^ 1 = a.
Proof.
move=> a0; rewrite /power_pos; case: ifPn => [/eqP->|a0'].
  by rewrite oner_eq0.
by rewrite mul1r lnK// posrE lt_neqAle eq_sym a0'.
Qed.

Lemma power_posr0 a : a `^ 0 = 1.
Proof.
by rewrite /power_pos; case: ifPn; rewrite ?eqxx// mul0r expR0.
Qed.

Lemma power_pos0 x : power_pos 0 x = (x == 0)%:R.
Proof. by rewrite /power_pos eqxx. Qed.

Lemma power_pos1 : power_pos 1 = fun=> 1.
Proof. by apply/funext => x; rewrite /power_pos oner_eq0 ln1 mulr0 expR0. Qed.

Lemma power_pos_eq0 x p : x `^ p = 0 -> x = 0.
Proof.
rewrite /power_pos. have [->|_] := eqVneq x 0 => //.
by move: (expR_gt0 (p * ln x)) => /gt_eqF /eqP.
Qed.

Lemma ler_power_pos a : 1 <= a -> {homo power_pos a : x y / x <= y}.
Proof.
move=> a1 x y xy.
by rewrite /power_pos gt_eqF ?(lt_le_trans _ a1)// ler_expR ler_wpmul2r ?ln_ge0.
Qed.

Lemma power_posM x y r : 0 <= x -> 0 <= y -> (x * y) `^ r = x `^ r * y `^ r.
Proof.
rewrite 2!le_eqVlt.
move=> /predU1P[<-|x0] /predU1P[<-|y0]; rewrite ?(mulr0, mul0r,power_pos0).
- by rewrite -natrM; case: eqP.
- by case: eqP => [->|]/=; rewrite ?mul0r ?power_posr0 ?mulr1.
- by case: eqP => [->|]/=; rewrite ?mulr0 ?power_posr0 ?mulr1.
- rewrite /power_pos mulf_eq0; case: eqP => [->|x0']/=.
    rewrite (@gt_eqF _ _ y)//.
    by case: eqP => /=; rewrite ?mul0r ?mul1r// => ->; rewrite mul0r expR0.
  by rewrite gt_eqF// lnM ?posrE // -expRD mulrDr.
Qed.

Lemma power_posAC x y z : (x `^ y) `^ z = (x `^ z) `^ y.
Proof.
rewrite /power_pos.
have [->/=|z0] := eqVneq z 0; rewrite ?mul0r.
- have [->/=|y0] := eqVneq y 0; rewrite ?mul0r//=.
  have [x0|x0] := eqVneq x 0; rewrite ?eqxx ?oner_eq0 ?ln1 ?mulr0 ?expR0//.
  by rewrite oner_eq0 if_same ln1 mulr0 expR0.
- have [->/=|y0] := eqVneq y 0; rewrite ?mul0r/=.
    have [x0|x0] := eqVneq x 0; rewrite ?eqxx ?oner_eq0 ?ln1 ?mulr0 ?expR0//.
    by rewrite oner_eq0 if_same ln1  mulr0 expR0.
  have [x0|x0] := eqVneq x 0; rewrite ?eqxx ?oner_eq0 ?ln1 ?mulr0 ?expR0.
    by [].
  rewrite gt_eqF ?expR_gt0// gt_eqF; last by rewrite expR_gt0.
  by rewrite !expK mulrCA.
Qed.

Lemma power_posD a : 0 < a -> {morph power_pos a : x y / x + y >-> x * y}.
Proof. by move=> a0 x y; rewrite /power_pos gt_eqF// mulrDl expRD. Qed.

Lemma power_pos_mulrn a n : 0 <= a -> a `^ n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih].
  by rewrite mulr0n expr0 power_posr0//; apply: lt0r_neq0.
move: a0; rewrite le_eqVlt => /predU1P[<-|a0].
  by rewrite !power_pos0 mulrn_eq0/= oner_eq0/= expr0n.
by rewrite -natr1 power_posD// ih power_posr1// ?exprS 1?mulrC// ltW.
Qed.

Lemma power_pos_inv1 a : 0 <= a -> a `^ (-1) = a ^-1.
Proof.
rewrite le_eqVlt => /predU1P[<-|a0].
  by rewrite power_pos0 invr0 oppr_eq0 oner_eq0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -[X in X * _ = _](power_posr1 (ltW a0)) -power_posD // subrr.
by rewrite power_posr0 divff// gt_eqF.
Qed.

Lemma power_pos_inv a n : 0 <= a -> a `^ (- n%:R) = a ^- n.
Proof.
move=> a0; elim: n => [|n ih].
  by rewrite -mulNrn mulr0n power_posr0 -exprVn expr0.
move: a0; rewrite le_eqVlt => /predU1P[<-|a0].
  by rewrite power_pos0 oppr_eq0 mulrn_eq0 oner_eq0 orbF exprnN exp0rz oppr_eq0.
rewrite -natr1 opprD power_posD// (power_pos_inv1 (ltW a0)) ih.
by rewrite -[in RHS]exprVn exprS [in RHS]mulrC exprVn.
Qed.

Lemma power_pos_intmul a (z : int) : 0 <= a -> a `^ z%:~R = a ^ z.
Proof.
move=> a0; have [z0|z0] := leP 0 z.
  rewrite -[in RHS](gez0_abs z0) abszE -exprnP -power_pos_mulrn//.
  by rewrite natr_absz -abszE gez0_abs.
rewrite -(opprK z) (_ : - z = `|z|%N); last by rewrite ltz0_abs.
by rewrite -exprnN -power_pos_inv// nmulrn.
Qed.

Lemma ln_power_pos s r : s != 0 -> ln (s `^ r) = r * ln s.
Proof. by move=> s0; rewrite /power_pos (negbTE s0) expK. Qed.

Lemma power12_sqrt a : 0 <= a -> a `^ (2^-1) = Num.sqrt a.
Proof.
rewrite le_eqVlt => /predU1P[<-|a0].
  by rewrite power_pos0 sqrtr0 invr_eq0 pnatr_eq0.
have /eqP : (a `^ (2^-1)) ^+ 2 = (Num.sqrt a) ^+ 2.
  rewrite sqr_sqrtr; last exact: ltW.
  by rewrite /power_pos gt_eqF// -expRMm mulrA divrr ?mul1r ?unitfE// lnK.
rewrite eqf_sqr => /predU1P[//|/eqP h].
have : 0 < a `^ 2^-1 by apply: power_pos_gt0.
by rewrite h oppr_gt0 ltNge sqrtr_ge0.
Qed.

End PowerPos.
Notation "a `^ x" := (power_pos a x) : ring_scope.

Section powere_pos.
Local Open Scope ereal_scope.
Context {R : realType}.
Implicit Types (r : R) (x y : \bar R).

Definition powere_pos x r :=
  match x with
  | x'%:E => (x' `^ r)%:E
  | +oo => if r == 0%R then 1%E else +oo
  | -oo => if r == 0%R then 1%E else 0%E
  end.

Local Notation "x `^ r" := (powere_pos x r).

Lemma powere_pos_EFin (s : R) r : s%:E `^ r = (s `^ r)%:E.
Proof. by []. Qed.

Lemma powere_posyr r : r != 0%R -> +oo `^ r = +oo.
Proof. by move/negbTE => /= ->. Qed.

Lemma powere_pose0 x : x `^ 0 = 1.
Proof. by move: x => [x'| |]/=; rewrite ?power_posr0// eqxx. Qed.

Lemma powere_pose1 x : 0 <= x -> x `^ 1 = x.
Proof.
by move: x => [x'| |]//= x0; rewrite ?power_posr1// (negbTE (oner_neq0 _)).
Qed.

Lemma powere_posNyr r : r != 0%R -> -oo `^ r = 0.
Proof.
by move => xne0; rewrite /powere_pos ifF //; apply/eqP; move: xne0 => /eqP.
Qed.

Lemma powere_pos0r r : 0 `^ r = (r == 0)%:R%:E.
Proof. by rewrite powere_pos_EFin power_pos0. Qed.

Lemma powere_pos1r r : 1 `^ r = 1.
Proof. by rewrite powere_pos_EFin power_pos1. Qed.

Lemma fine_powere_pos x r : fine (x `^ r) = ((fine x) `^ r)%R.
Proof. by move: x => [x| |]//=; rewrite power_pos0; case: ifPn. Qed.

Lemma powere_pos_ge0 x r : 0 <= x `^ r.
Proof.
by move: x => [x| |];
  rewrite ?powere_pos_EFin ?lee_fin ?power_pos_ge0// /powere_pos; case: ifPn.
Qed.

Lemma powere_pos_gt0 x r : 0 < x -> 0 < x `^ r.
Proof.
move: x => [x|_|//]; rewrite ?lte_fin; first exact: power_pos_gt0.
by rewrite /powere_pos; case: ifPn.
Qed.

Lemma powere_pos_eq0 x r : -oo < x -> x `^ r = 0 -> x = 0.
Proof.
move: x => [x _|_/=|//].
- by rewrite powere_pos_EFin => -[] /power_pos_eq0 ->.
- by case: ifPn => // _ /eqP; rewrite onee_eq0.
Qed.

Lemma powere_posM x y r : 0 <= x -> 0 <= y -> (x * y) `^ r = x `^ r * y `^ r.
Proof.
move: x y => [x| |] [y| |]//=.
- by move=> x0 y0; rewrite -EFinM power_posM.
- move=> x0 _; case: ifPn => /= [/eqP ->|r0].
  + by rewrite mule1 power_posr0 powere_pose0.
  + move: x0; rewrite le_eqVlt => /predU1P[[]<-|/[1!(@lte_fin R)] x0].
    * by rewrite mul0e powere_pos0r power_pos0 (negbTE r0)/= mul0e.
    * by rewrite mulry [RHS]mulry !gtr0_sg ?power_pos_gt0// !mul1e powere_posyr.
- move=> _ y0; case: ifPn => /= [/eqP ->|r0].
  + by rewrite power_posr0 powere_pose0 mule1.
  + move: y0; rewrite le_eqVlt => /predU1P[[]<-|/[1!(@lte_fin R)] u0].
    by rewrite mule0 powere_pos0r power_pos0 (negbTE r0) mule0.
  + by rewrite 2!mulyr !gtr0_sg ?power_pos_gt0// mul1e powere_posyr.
- move=> _ _; case: ifPn => /= [/eqP ->|r0].
  + by rewrite powere_pose0 mule1.
  + by rewrite mulyy powere_posyr.
Qed.

Lemma powere12_sqrt x : 0 <= x -> x `^ 2^-1 = sqrte x.
Proof.
move: x => [x|_|//]; last by rewrite powere_posyr.
by rewrite lee_fin => x0 /=; rewrite power12_sqrt.
Qed.

End powere_pos.
Notation "a `^ x" := (powere_pos a x) : ereal_scope.

Section riemannR_series.
Variable R : realType.
Implicit Types a : R.
Local Open Scope real_scope.

Definition riemannR a : R ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemannR a n /.

Lemma riemannR_gt0 a i : 0 <= a -> 0 < riemannR a i.
Proof. by move=> ?; rewrite /riemannR invr_gt0 power_pos_gt0. Qed.

Lemma dvg_riemannR a : 0 <= a <= 1 -> ~ cvg (series (riemannR a)).
Proof.
move=> /andP[a0 a1].
have : forall n, harmonic n <= riemannR a n.
  move=> [/=|n]; first by rewrite power_pos1 invr1.
  rewrite -[leRHS]div1r ler_pdivl_mulr ?power_pos_gt0// mulrC ler_pdivr_mulr//.
  by rewrite mul1r -[leRHS]power_posr1// (ler_power_pos)// ler1n.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemannR_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemannR_series.
