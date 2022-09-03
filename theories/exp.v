(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
Require Import mathcomp_extra boolp reals ereal nsatz_realtype classical_sets.
Require Import signed functions topology normedtype landau sequences derive.
Require Import realfun.

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
(*              a `^ x == exponential functions                               *)
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
  apply/cvg_distP => eps eps_gt0 /=; rewrite !near_simpl /=.
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
  apply/cvg_distP => eps eps_gt0 /=.
  rewrite !near_simpl /=.
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

Section ExpFun.
Variable R : realType.
Implicit Types a x : R.

Definition exp_fun a x := expR (x * ln a).

Local Notation "a `^ x" := (exp_fun a x).

Lemma exp_fun_gt0 a x : 0 < a `^ x. Proof. by rewrite expR_gt0. Qed.

Lemma exp_funr1 a : 0 < a -> a `^ 1 = a.
Proof. by move=> a0; rewrite /exp_fun mul1r lnK. Qed.

Lemma exp_funr0 a : 0 < a -> a `^ 0 = 1.
Proof. by move=> a0; rewrite /exp_fun mul0r expR0. Qed.

Lemma exp_fun1 : exp_fun 1 = fun=> 1.
Proof. by rewrite funeqE => x; rewrite /exp_fun ln1 mulr0 expR0. Qed.

Lemma ler_exp_fun a : 1 < a -> {homo exp_fun a : x y / x <= y}.
Proof. by move=> a1 x y xy; rewrite /exp_fun ler_expR ler_pmul2r // ln_gt0. Qed.

Lemma exp_funD a : 0 < a -> {morph exp_fun a : x y / x + y >-> x * y}.
Proof. by move=> a0 x y; rewrite [in LHS]/exp_fun mulrDl expRD. Qed.

Lemma exp_fun_inv a : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -[X in X * _ = _](exp_funr1 a0) -exp_funD // subrr exp_funr0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma exp_fun_mulrn a n : 0 < a -> exp_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 exp_funr0.
by rewrite -natr1 exprSr exp_funD// ih exp_funr1.
Qed.

End ExpFun.
Notation "a `^ x" := (exp_fun a x).

Section riemannR_series.
Variable R : realType.
Implicit Types a : R.
Local Open Scope ring_scope.

Definition riemannR a : R ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemannR a n /.

Lemma riemannR_gt0 a i : 0 < a -> 0 < riemannR a i.
Proof. move=> ?; by rewrite /riemannR invr_gt0 exp_fun_gt0. Qed.

Lemma dvg_riemannR a : 0 < a <= 1 -> ~ cvg (series (riemannR a)).
Proof.
case/andP => a0; rewrite le_eqVlt => /orP[/eqP ->|a1].
  rewrite (_ : riemannR 1 = harmonic); first exact: dvg_harmonic.
  by rewrite funeqE => i /=; rewrite exp_funr1.
have : forall n, harmonic n <= riemannR a n.
  case=> /= [|n]; first by rewrite exp_fun1 invr1.
  rewrite -[leRHS]div1r ler_pdivl_mulr ?exp_fun_gt0 // mulrC ler_pdivr_mulr //.
  by rewrite mul1r -[leRHS]exp_funr1 // (ler_exp_fun) // ?ltr1n // ltW.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemannR_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemannR_series.
