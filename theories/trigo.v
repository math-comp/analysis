(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
Require Import mathcomp_extra boolp reals ereal nsatz_realtype classical_sets.
Require Import signed functions topology normedtype landau sequences derive.
Require Import realfun exp.

(******************************************************************************)
(*                     Theory of trigonometric functions                      *)
(*                                                                            *)
(* This file provides the definitions of basic trigonometric functions and    *)
(* develops their theories.                                                   *)
(*                                                                            *)
(*    periodic f T == f is a periodic function of period T                    *)
(* alternating f T == f is an alternating function of period T                *)
(*     sin_coeff x == the sequence of coefficients of sin x                   *)
(*           sin x == the sine function, i.e., lim (series (sin_coeff x))     *)
(*    sin_coeff' x == the sequence of odd coefficients of sin x               *)
(*     cos_coeff x == the sequence of coefficients of cos x                   *)
(*           cos x == the cosine function, i.e., lim (series (cos_coeff x))   *)
(*    cos_coeff' x == the sequence of even coefficients of cos x              *)
(*              pi == pi                                                      *)
(*           tan x == the tangent function                                    *)
(*          acos x == the arccos function                                     *)
(*          asin x == the arcsin function                                     *)
(*          atan x == the arctangent function                                 *)
(*                                                                            *)
(* Acknowledgments: the proof of cos 2 < 0 is inspired from HOL-light, some   *)
(* proofs of trigonometric relations are taken from                           *)
(* https://github.com/affeldt-aist/coq-robot.                                 *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* NB: backport to mathcomp in progress *)
Lemma sqrtrV (R : rcfType) (x : R) : 0 <= x -> Num.sqrt (x^-1) = (Num.sqrt x)^-1.
Proof.
move=> x_ge0.
case: (x =P 0) => [->|/eqP xD0]; first by rewrite invr0 sqrtr0 invr0.
rewrite -[LHS]mul1r -(mulVf (_ : Num.sqrt x != 0)); last first.
  by rewrite sqrtr_eq0 -ltNge; case: ltrgt0P x_ge0 xD0.
by rewrite -mulrA -sqrtrM // divff // sqrtr1 mulr1.
Qed.

Lemma eqr_div (R : numFieldType) (x y z t : R):
  y != 0 -> t != 0 -> (x / y == z / t) = (x * t == z * y).
Proof.
move=> yD0 tD0.
rewrite -[x in RHS](divfK yD0) -[z in RHS](divfK tD0) mulrAC.
by apply/eqP/eqP=> [->//|xyty]; exact/(mulIf tD0)/(mulIf yD0).
Qed.

Lemma big_nat_mul (R : zmodType) (f : R ^nat) (n k : nat) :
  \sum_(0 <= i < n * k) f i =
  \sum_(0 <= i < n) \sum_(i * k <= j < i.+1 * k) f j.
Proof.
elim: n => [|n ih]; first by rewrite mul0n 2!big_nil.
rewrite [in RHS]big_nat_recr//= -ih mulSn addnC [in LHS]/index_iota subn0 iotaD.
rewrite big_cat /= [in X in _ = X  _]/index_iota subn0; congr (_ + _).
by rewrite add0n /index_iota (addnC _ k) addnK.
Qed.
(* /NB: backport to mathcomp in progress *)

Lemma cvg_series_cvg_series_group (R : realFieldType) (f : R ^nat) k :
  cvg (series f) -> (0 < k)%N ->
  [series \sum_(n * k <= i < n.+1 * k) f i]_n --> lim (series f).
Proof.
move=> /cvg_ballP cf k0; apply/cvg_ballP => _/posnumP[e].
have := !! cf _ (gt0 e); rewrite near_map => -[n _ nl].
rewrite near_map; near=> m.
rewrite /ball /= [in X in `|_ - X|]/series [in X in `|_ - X|]/= -big_nat_mul.
have /nl : (n <= m * k)%N.
  by near: m; exists n.+1 => //= p /ltnW /leq_trans /(_ (leq_pmulr _ k0)).
by rewrite /ball /= distrC.
Unshelve. all: by end_near. Qed.

Lemma lt_sum_lim_series (R : realFieldType) (f : R ^nat) n : cvg (series f) ->
  (forall d, 0 < f (n + d.*2)%N + f (n + d.*2.+1)%N) ->
  \sum_(0 <= i < n) f i < lim (series f).
Proof.
move=> /cvg_ballP cf fn.
have fn0 : 0 < f n + f n.+1 by have := fn 0%N; rewrite double0 addn0 addn1.
rewrite ltNge; apply: contraPN cf => ffn /(_ _ fn0).
rewrite near_map /ball /=.
have nf_ub N : \sum_(0 <= i < n.+2) f i <= \sum_(0 <= i < N.+1.*2 + n) f i.
  elim: N => // N /le_trans ->//; rewrite -(addn1 (N.+1)) doubleD addnAC.
  rewrite [in leRHS]/index_iota subn0 iotaD big_cat.
  rewrite -[in X in _ <= X + _](subn0 (N.+1.*2 + n)%N) ler_addl /= add0n.
  by rewrite 2!big_cons big_nil addr0 -(addnC n) ltW// -addnS fn.
case=> N _ Nfn; have /Nfn/ltr_distlC_addr : (N.+1.*2 + n >= N)%N.
  by rewrite doubleS -addn2 -addnn -2!addnA leq_addr.
rewrite addrA => ffnfn.
have : lim (series f) + f n + f n.+1 <= \sum_(0 <= i < N.+1.*2 + n) f i.
  apply: (le_trans _ (nf_ub N)).
  by do 2 rewrite big_nat_recr //=; by rewrite -2!addrA ler_add2r.
by move/(lt_le_trans ffnfn); rewrite ltxx.
Qed.

Section periodic.
Variables U V : zmodType.
Implicit Type f : U -> V.

Definition periodic f (T : U) := forall u, f (u + T) = f u.

Lemma periodicn f (T : U) : periodic f T -> forall n a, f (a + T *+ n) = f a.
Proof.
by move=> fT; elim=> [|n ih] a;[rewrite mulr0n addr0|rewrite mulrS addrA ih fT].
Qed.
End periodic.

Section alternating.
Variables (U : zmodType) (V : ringType).
Implicit Type f : U -> V.

Definition alternating f (T : U) := forall x, f (x + T) = - f x.

Lemma alternatingn f (T : U) : alternating f T ->
  forall n a, f (a + T *+ n) = (- 1) ^+ n * f a.
Proof.
move=> fT; elim => [a|n ih a]; first by rewrite mulr0n expr0 addr0 mul1r.
by rewrite mulrS addrA ih fT exprS mulrN mulN1r mulNr.
Qed.

End alternating.

Section CosSin.
Variable R : realType.
Implicit Types x y : R.

Definition sin_coeff x :=
  [sequence (odd n)%:R * (-1) ^+ n.-1./2 * x ^+ n / n`!%:R]_n.

Lemma sin_coeffE x : sin_coeff x =
  (fun n => (fun n => (odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /sin_coeff /= -!mulrA [_ / _]mulrC. Qed.

Lemma sin_coeff_even n x : sin_coeff x n.*2 = 0.
Proof. by rewrite /sin_coeff /= odd_double /= !mul0r. Qed.

Lemma is_cvg_series_sin_coeff x : cvg (series (sin_coeff x)).
Proof.
apply: normed_cvg.
apply: series_le_cvg; last exact: (@is_cvg_series_exp_coeff _ `|x|).
- by move=> n; rewrite normr_ge0.
- by move=> n; rewrite divr_ge0.
- move=> n /=; rewrite /exp_coeff /sin_coeff /=.
  rewrite !normrM normfV !normr_nat !normrX normrN normr1 expr1n mulr1.
  by case: odd; [rewrite mul1r| rewrite !mul0r].
Qed.

Definition sin x : R := lim (series (sin_coeff x)).

Lemma sinE : sin = fun x =>
  lim (pseries (fun n => (odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1) x).
Proof. by apply/funext => x; rewrite /pseries -sin_coeffE. Qed.

Definition sin_coeff' x (n : nat) := (-1)^n * x ^+ n.*2.+1 / n.*2.+1`!%:R.

Lemma sin_coeff'E x n : sin_coeff' x n = sin_coeff x n.*2.+1.
Proof.
by rewrite /sin_coeff' /sin_coeff /= odd_double mul1r -2!mulrA doubleK.
Qed.

Lemma cvg_sin_coeff' x : series (sin_coeff' x) --> sin x.
Proof.
have /(@cvg_series_cvg_series_group _ _ 2) := @is_cvg_series_sin_coeff x.
move=> /(_ isT); apply: cvg_trans.
rewrite [X in _ --> series X](_ : _ = (fun n => sin_coeff x n.*2.+1)).
  rewrite [X in series X --> _](_ : _ = (fun n => sin_coeff x n.*2.+1)) //.
  by rewrite funeqE => n; exact: sin_coeff'E.
rewrite funeqE=> n; rewrite /= 2!muln2 big_nat_recl //= sin_coeff_even add0r.
by rewrite big_nat_recl // big_geq // addr0.
Qed.

Lemma diffs_sin :
  pseries_diffs (fun n => (odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1) =
   (fun n => (~~(odd n))%:R * (-1) ^+ n./2 * (n`!%:R)^-1 : R).
Proof.
apply/funext => i; rewrite /pseries_diffs /= factS natrM invfM.
by rewrite [_.+1%:R * _]mulrC -!mulrA [_.+1%:R^-1 * _]mulrC mulfK.
Qed.

Lemma series_sin_coeff0 n : series (sin_coeff 0) n.+1 = 0.
Proof.
rewrite /series /= big_nat_recl //= /sin_coeff /= expr0n divr1 !mulr1.
by rewrite big1 ?addr0 // => i _; rewrite expr0n !(mul0r, mulr0).
Qed.

Lemma sin0 : sin 0 = 0.
Proof.
apply: lim_near_cst => //; near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_sin_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /sin_coeff /= expr0n !(mulr0, mul0r).
Unshelve. all: by end_near. Qed.

Definition cos_coeff x :=
  [sequence (~~ odd n)%:R * (-1)^n./2 * x ^+ n / n`!%:R]_n.

Lemma cos_coeff_odd n x : cos_coeff x n.*2.+1 = 0.
Proof. by rewrite /cos_coeff /= odd_double /= !mul0r. Qed.

Lemma cos_coeff_2_0 : cos_coeff 2 0%N = 1 :> R.
Proof. by rewrite /cos_coeff /= mul1r expr0 mulr1 expr0z divff. Qed.

Lemma cos_coeff_2_2 : cos_coeff 2 2%N = - 2%:R :> R.
Proof.
by rewrite /cos_coeff /= mul1r expr1z mulN1r expr2 mulNr -mulrA divff// mulr1.
Qed.

Lemma cos_coeff_2_4 : cos_coeff 2 4%N = 2%:R / 3%:R :> R.
Proof.
rewrite /cos_coeff /= mul1r -exprnP sqrrN expr1n mul1r 2!factS mulnCA mulnC.
by rewrite 3!exprS expr1 2!mulrA natrM -mulf_div -2!natrM divff// mul1r.
Qed.

Lemma cos_coeffE x :
  cos_coeff x = (fun n => (fun n => (~~(odd n))%:R * (-1) ^+ n./2 *
                                    (n`!%:R)^-1) n * x ^+ n).
Proof.
by apply/funext => i; rewrite /cos_coeff /= -!mulrA [_ / _]mulrC.
Qed.

Lemma is_cvg_series_cos_coeff x : cvg (series (cos_coeff x)).
Proof.
apply: normed_cvg.
apply: series_le_cvg; last exact: (@is_cvg_series_exp_coeff _ `|x|).
- by move=> n; rewrite normr_ge0.
- by move=> n; rewrite divr_ge0.
- move=> n /=; rewrite /exp_coeff /cos_coeff /=.
  rewrite !normrM normfV !normr_nat !normrX normrN normr1 expr1n mulr1.
  by case: odd; [rewrite !mul0r | rewrite mul1r].
Qed.

Definition cos x : R := lim (series (cos_coeff x)).

Lemma cosE : cos = fun x =>
  lim (series (fun n =>
                (fun n => (~~(odd n))%:R * (-1)^+ n./2 * (n`!%:R)^-1) n
                * x ^+ n)).
Proof. by apply/funext => x; rewrite -cos_coeffE. Qed.

Definition cos_coeff' x (n : nat) := (-1)^n * x ^+ n.*2 / n.*2`!%:R.

Lemma cos_coeff'E x n : cos_coeff' x n = cos_coeff x n.*2.
Proof.
rewrite /cos_coeff' /cos_coeff /= odd_double /= mul1r -2!mulrA; congr (_ * _).
by rewrite (half_bit_double n false).
Qed.

Lemma cvg_cos_coeff' x : series (cos_coeff' x) --> cos x.
Proof.
have /(@cvg_series_cvg_series_group _ _ 2) := @is_cvg_series_cos_coeff x.
move=> /(_ isT); apply: cvg_trans.
rewrite [X in _ --> series X](_ : _ = (fun n => cos_coeff x n.*2)); last first.
  rewrite funeqE=> n; rewrite /= 2!muln2 big_nat_recr //= cos_coeff_odd addr0.
  by rewrite big_nat_recl//= /index_iota subnn big_nil addr0.
rewrite [X in series X --> _](_ : _ = (fun n => cos_coeff x n.*2)) //.
by rewrite funeqE => n; exact: cos_coeff'E.
Qed.

Lemma diffs_cos :
  pseries_diffs (fun n => (~~(odd n))%:R * (-1) ^+ n./2 * (n`!%:R)^-1) =
  (fun n => - ((odd n)%:R * (-1) ^+ n.-1./2 * (n`!%:R)^-1): R).
Proof.
apply/funext => [] [|i] /=.
  by rewrite /pseries_diffs /= !mul0r mulr0 oppr0.
rewrite /pseries_diffs /= negbK exprS mulN1r !(mulNr, mulrN).
rewrite factS natrM invfM.
by rewrite [_.+1%:R * _]mulrC -!mulrA [_.+1%:R^-1 * _]mulrC mulfK.
Qed.

Lemma series_cos_coeff0 n : series (cos_coeff 0) n.+1 = 1.
Proof.
rewrite /series /= big_nat_recl //= /cos_coeff /= expr0n divr1 !mulr1.
by rewrite big1 ?addr0 // => i _; rewrite expr0n !(mul0r, mulr0).
Qed.

Lemma cos0 : cos 0 = 1.
Proof.
apply: lim_near_cst => //; near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_cos_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /cos_coeff /= expr0n !(mulr0, mul0r).
Unshelve. all: by end_near. Qed.

Global Instance is_derive_sin x : is_derive x 1 sin (cos x).
Proof.
rewrite sinE /=.
pose s : R^nat := fun n => (odd n)%:R * (-1) ^+ (n.-1)./2 / n`!%:R.
pose s1 n := pseries_diffs s n * x ^+ n.
rewrite cosE /= /pseries (_ : (fun _ => _) = s1); last first.
  by apply/funext => i; rewrite /s1 diffs_sin.
apply: (@pseries_snd_diffs _ _ (`|x| + 1)); rewrite /pseries.
- by rewrite -sin_coeffE; apply: is_cvg_series_sin_coeff.
- rewrite (_ : (fun _ => _) = cos_coeff (`|x| + 1)).
    exact: is_cvg_series_cos_coeff.
  by apply/funext => i; rewrite diffs_sin cos_coeffE.
- rewrite /pseries (_ : (fun _ => _) = - sin_coeff (`|x| + 1)).
    by rewrite is_cvg_seriesN; exact: is_cvg_series_sin_coeff.
  by apply/funext => i; rewrite diffs_sin diffs_cos sin_coeffE !fctE !mulNr.
- by rewrite [ltRHS]ger0_norm// addrC -subr_gt0 addrK.
Qed.

Lemma derivable_sin x : derivable sin x 1.
Proof. by apply: ex_derive; apply: is_derive_sin. Qed.

Lemma continuous_sin : continuous sin.
Proof.
by move=> x; apply/differentiable_continuous/derivable1_diffP/derivable_sin.
Qed.

Global Instance is_derive_cos x : is_derive x 1 cos (- (sin x)).
Proof.
rewrite cosE /=.
pose s : R^nat := fun n => (~~ odd n)%:R * (-1) ^+ n./2 / n`!%:R.
pose s1 n := pseries_diffs s n * x ^+ n.
rewrite sinE /= /pseries.
rewrite (_ : (fun _ => _) = - s1); last first.
  by apply/funext => i; rewrite /s1 diffs_cos !fctE mulNr opprK.
rewrite lim_seriesN ?opprK; last first.
  rewrite (_ : s1 = - sin_coeff x).
    by rewrite is_cvg_seriesN; exact: is_cvg_series_sin_coeff.
  by apply/funext => i; rewrite /s1 diffs_cos sin_coeffE !fctE mulNr.
apply: (@pseries_snd_diffs _ _ (`|x| + 1)).
- by rewrite /pseries -cos_coeffE; apply: is_cvg_series_cos_coeff.
- rewrite /pseries (_ : (fun _ => _) = - sin_coeff (`|x| + 1)).
    by rewrite is_cvg_seriesN; exact: is_cvg_series_sin_coeff.
  by apply/funext => i; rewrite diffs_cos sin_coeffE !fctE mulNr.
- rewrite /pseries (_ : (fun _=> _) = - cos_coeff (`|x| + 1)).
    by rewrite is_cvg_seriesN; exact: is_cvg_series_cos_coeff.
  apply/funext => i; rewrite diffs_cos pseries_diffsN.
  by rewrite diffs_sin cos_coeffE mulNr.
- by rewrite [ltRHS]ger0_norm// addrC -subr_gt0 addrK.
Qed.

Lemma derivable_cos x : derivable cos x 1.
Proof. by apply: ex_derive; apply: is_derive_cos. Qed.

Lemma continuous_cos : continuous cos.
Proof.
by move=> x; exact/differentiable_continuous/derivable1_diffP/derivable_cos.
Qed.

Lemma cos2Dsin2 x : (cos x) ^+ 2 + (sin x) ^+ 2 = 1.
Proof.
set v := LHS; pattern x in v; move: @v; set f := (X in let _ := X x in _) => /=.
apply: (@eq_trans _ _ (f 0)); last by rewrite /f sin0 cos0 expr1n expr0n addr0.
apply: is_derive_0_is_cst => {}x.
apply: trigger_derive; rewrite /GRing.scale /=.
by rewrite mulrN ![sin x * _]mulrC -opprD addrC subrr.
Qed.

Lemma cos_max x : `| cos x | <= 1.
Proof.
rewrite -(expr_le1 (_ : 0 < 2)%nat) // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite -(cos2Dsin2 x) ler_addl ?sqr_ge0.
Qed.

Lemma cos_geN1 x : -1 <= cos x.
Proof. by rewrite ler_oppl; have /ler_normlP[] := cos_max x. Qed.

Lemma cos_le1 x : cos x <= 1.
Proof. by have /ler_normlP[] := cos_max x. Qed.

Lemma sin_max x : `| sin x | <= 1.
Proof.
rewrite -(expr_le1 (_ : 0 < 2)%nat) // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite -(cos2Dsin2 x) ler_addr ?sqr_ge0.
Qed.

Lemma sin_geN1 x : -1 <= sin x.
Proof. by rewrite ler_oppl; have /ler_normlP[] := sin_max x. Qed.

Lemma sin_le1 x : sin x <= 1.
Proof. by have /ler_normlP[] := sin_max x. Qed.

Fact sinD_cosD x y :
  (sin (x + y) - (sin x * cos y + cos x * sin y)) ^+ 2 +
  (cos (x + y) - (cos x * cos y - sin x * sin y)) ^+ 2 = 0.
Proof.
set v := LHS; pattern x in v; move: @v; set f := (X in let _ := X x in _) => /=.
apply: (@eq_trans _ _ (f 0)); last first.
  by rewrite /f cos0 sin0 !(mul1r, mul0r, add0r, subr0, subrr, expr0n).
apply: is_derive_0_is_cst => {}x.
by apply: trigger_derive; rewrite /GRing.scale /=; nsatz.
Qed.

Lemma sinD x y : sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
have /eqP := sinD_cosD x y.
rewrite paddr_eq0 => [/andP[]||]; try exact: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma cosD x y : cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
have /eqP := sinD_cosD x y.
rewrite paddr_eq0 => [/andP[_]||]; try exact: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma sin2cos2 x : sin x ^+ 2 = 1 - cos x ^+ 2.
Proof. by move/eqP: (cos2Dsin2 x); rewrite eq_sym addrC -subr_eq => /eqP. Qed.

Lemma cos2sin2 x : cos x ^+ 2 = 1 - sin x ^+ 2.
Proof. by move/eqP: (cos2Dsin2 x); rewrite eq_sym -subr_eq => /eqP. Qed.

Lemma sin_mulr2n x : sin (x *+ 2) = (cos x * sin x) *+ 2.
Proof. by rewrite mulr2n sinD mulrC -mulr2n. Qed.

Lemma cos_mulr2n x : cos (x *+ 2) = cos x ^+2 *+ 2 - 1.
Proof. by rewrite mulr2n cosD -!expr2 sin2cos2 opprB addrA mulr2n. Qed.

Fact sinN_cosN x :
  (sin (- x) + sin x) ^+ 2 + (cos (- x) - cos x) ^+ 2 = 0.
Proof.
set v := LHS; pattern x in v; move: @v; set f := (X in let _ := X x in _) => /=.
apply: (@eq_trans _ _ (f 0)); last first.
  by rewrite /f oppr0 cos0 sin0 !(addr0, subrr, expr0n).
apply: is_derive_0_is_cst => {}x.
by apply: trigger_derive; rewrite /GRing.scale /=; nsatz.
Qed.

Lemma sinN x : sin (- x) = - sin x.
Proof.
have /eqP := sinN_cosN x.
rewrite paddr_eq0 => [/andP[]||]; try exact: sqr_ge0.
by rewrite sqrf_eq0 addr_eq0 => /eqP.
Qed.

Lemma cosN x : cos (- x) = cos x.
Proof.
have /eqP := sinN_cosN x.
rewrite paddr_eq0 => [/andP[_]||]; try exact: sqr_ge0.
by rewrite sqrf_eq0 subr_eq0 => /eqP.
Qed.

Lemma sin_sg x y : sin (Num.sg x * y) = Num.sg x * sin y.
Proof. by case: sgrP; rewrite ?mul1r ?mulN1r ?sinN // !mul0r sin0. Qed.

Lemma cos_sg x y : x != 0 -> cos (Num.sg x * y) = cos y.
Proof. by case: sgrP; rewrite ?mul1r ?mulN1r ?cosN. Qed.

Lemma cosB x y : cos (x - y) = cos x * cos y + sin x * sin y.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sinB x y : sin (x - y) = sin x * cos y - cos x * sin y.
Proof. by rewrite sinD cosN sinN mulrN. Qed.

Lemma norm_cos_eq1 x : (`|cos x| == 1) = (sin x == 0).
Proof.
rewrite -sqrf_eq0 -sqrp_eq1 // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite [X in _ = (X == _)]sin2cos2 subr_eq0 eq_sym.
Qed.

Lemma norm_sin_eq1 x : (`|sin x| == 1) = (cos x == 0).
Proof.
rewrite -sqrf_eq0 -sqrp_eq1 // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite [X in _ = (X == _)]cos2sin2 subr_eq0 eq_sym.
Qed.

Lemma cos1sin0 x : `|cos x| = 1 -> sin x = 0.
Proof. by move/eqP; rewrite norm_cos_eq1 => /eqP. Qed.

Lemma sin1cos0 x : `|sin x| = 1 -> cos x = 0.
Proof. by move/eqP; rewrite norm_sin_eq1 => /eqP. Qed.

Lemma sin0cos1 x : sin x = 0 -> `|cos x| = 1.
Proof. by move/eqP; rewrite -norm_cos_eq1 => /eqP. Qed.

Lemma cos_norm x : cos `|x| = cos x.
Proof. by case: (ler0P x); rewrite ?cosN. Qed.

End CosSin.
Arguments sin {R}.
Arguments cos {R}.

Section Pi.
Variable R : realType.
Implicit Types (x y : R) (n k : nat).

Definition pi : R := get [set x | 0 <= x <= 2 /\ cos x = 0] *+ 2.

Lemma pihalfE : pi / 2 = get [set x | 0 <= x <= 2 /\ cos x = 0].
Proof. by rewrite /pi -(mulr_natr (get _)) -mulrA divff ?mulr1. Qed.

Lemma cos2_lt0 : cos 2 < 0 :> R.
Proof.
rewrite -(opprK (cos _)) oppr_lt0; have /cvgN h := @cvg_cos_coeff' R 2.
rewrite -(cvg_lim (@Rhausdorff R) h).
apply: (@lt_trans _ _ (\sum_(0 <= i < 3) - cos_coeff' 2 i)).
  do 3 rewrite big_nat_recl//; rewrite big_nil addr0 3!cos_coeff'E double0.
  rewrite cos_coeff_2_0 cos_coeff_2_2 -muln2 cos_coeff_2_4 addrA -(opprD 1).
  rewrite opprB -(@natrB _ 2 1)// subn1/= -[in X in X - _](@divff _ 3%:R)//.
  by rewrite -mulrBl divr_gt0// -natrB// -[(_ - _)%N]/_.+1.
rewrite -seriesN lt_sum_lim_series //.
  by move/cvgP in h; by rewrite seriesN.
move=> d.
rewrite /cos_coeff' 2!exprzD_nat (exprSz _ d.*2) -[in (-1) ^ d.*2](muln2 d).
rewrite -(exprnP _ (d * 2)) (exprM (-1)) sqrr_sign 2!mulr1 -exprSzr.
rewrite (_ : 4 = 2 * 2)%N // -(exprnP _ (2 * 2)) (exprM (-1)) sqrr_sign.
rewrite mul1r [(-1) ^ 3](_ : _ = -1) ?mulN1r ?mulNr ?opprK; last first.
  by rewrite -exprnP 2!exprS expr1 mulrN1 opprK mulr1.
rewrite subr_gt0.
rewrite addnS doubleS -[X in 2 ^+ X]addn2 exprD -mulrA ltr_pmul2l//.
rewrite factS factS 2!natrM mulrA invfM !mulrA.
rewrite ltr_pdivr_mulr ?ltr0n ?fact_gt0// mulVf ?pnatr_eq0 ?gtn_eqF ?fact_gt0//.
rewrite ltr_pdivr_mulr ?mul1r //.
by rewrite expr2 -!natrM ltr_nat !mulSn !add2n mul0n !addnS.
Qed.

Lemma sin2_gt0 x : 0 < x < 2 -> 0 < sin x.
Proof.
move=> /andP[x_gt0 x_lt2].
have sinx := @cvg_sin_coeff' _ x.
rewrite -(cvg_lim (@Rhausdorff R) sinx).
rewrite [ltLHS](_ : 0 = \sum_(0 <= i < 0) sin_coeff' x i :> R); last first.
  by rewrite big_nil.
rewrite lt_sum_lim_series //; first by move/cvgP in sinx.
move=> d.
rewrite /sin_coeff' 2!exprzD_nat (exprSz _ d.*2) -[in (-1) ^ d.*2](muln2 d).
rewrite -(exprnP _ (d * 2)) (exprM (-1)) sqrr_sign 2!mulr1 -exprSzr.
rewrite !add0n!mul1r mulN1r -[d.*2.+1]addn1 doubleD -addSn exprD.
rewrite -(ffact_fact (leq_addl _ _)) addnK.
rewrite mulNr -!mulrA -mulrBr mulr_gt0 ?exprn_gt0 //.
set u := _.+1.
rewrite natrM invfM.
rewrite -[X in _ < X - _]mul1r !mulrA -mulrBl divr_gt0 //; last first.
  by rewrite (ltr_nat _ 0) fact_gt0.
rewrite subr_gt0.
set v := _ ^_ _; rewrite -[ltRHS](divff (_ : v%:R != 0)); last first.
  by rewrite lt0r_neq0 // (ltr_nat _ 0) ffact_gt0 leq_addl.
rewrite ltr_pmul2r; last by rewrite invr_gt0 (ltr_nat _ 0) ffact_gt0 leq_addl.
rewrite {}/v !addnS addn0 !ffactnS ffactn0 muln1 /= natrM.
by rewrite (ltr_pmul (ltW _ ) (ltW _)) // (lt_le_trans x_lt2) // ler_nat.
Qed.

Lemma cos1_gt0 : cos 1 > 0 :> R.
Proof.
have h := @cvg_cos_coeff' R 1; rewrite -(cvg_lim (@Rhausdorff R) h).
apply: (@lt_trans _ _ (\sum_(0 <= i < 2) cos_coeff' 1 i)).
  rewrite big_nat_recr//= big_nat_recr//= big_nil add0r.
  rewrite /cos_coeff' expr0z expr1n fact0 !mul1r expr1n expr1z.
  by rewrite !mulNr subr_gt0 mul1r div1r ltf_pinv ?posrE ?ltr0n// ltr_nat.
rewrite lt_sum_lim_series //; [by move/cvgP in h|move=> d].
rewrite /cos_coeff' !(expr1n,mulr1).
rewrite -muln2 -mulSn muln2 -exprnP -signr_odd odd_double expr0.
rewrite -exprnP -signr_odd oddD/= muln2 odd_double/= expr1 add2n.
rewrite mulNr subr_gt0 2!div1r ltf_pinv ?posrE ?ltr0n ?fact_gt0//.
by rewrite ltr_nat ltn_pfact//ltn_double doubleS.
Qed.

Lemma cos_exists : exists2 pih : R, 1 <= pih <= 2 & cos pih = 0.
Proof.
have /IVT[] : minr (cos 1) (cos 2) <= (0 : R) <= maxr (cos 1) (cos 2).
  - by rewrite le_maxr (ltW cos1_gt0) le_minl (ltW cos2_lt0) orbC.
  - by rewrite ler1n.
  - by apply/continuous_subspaceT => ?; exact: continuous_cos.
by move=> pih /itvP pihI chpi_eq0; exists pih; rewrite ?pihI.
Qed.

Lemma cos_02_uniq x y :
  0 <= x <= 2 -> cos x = 0 -> 0 <= y <= 2 -> cos y = 0 -> x = y.
Proof.
wlog xLy : x y / x <= y => [H xB cx0 yB cy0|].
  by case: (lerP x y) => [/H //| /ltW /H H1]; [exact|exact/esym/H1].
move=> /andP[x_ge0 x_le2] cx0 /andP[y_ge0 y_le2] cy0.
case: (x =P y) => // /eqP xDy.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
have /(Rolle xLLs)[x1 _|x1|x1 x1I [_ x1D]] : cos x = cos y by rewrite cy0.
- exact: derivable_cos.
- by apply/continuous_subspaceT => ?; exact: continuous_cos.
- have [_ /esym/eqP] := is_derive_cos x1; rewrite x1D oppr_eq0 => /eqP Hs.
  suff : 0 < sin x1 by rewrite Hs ltxx.
  apply/sin2_gt0/andP; split.
  + by rewrite (le_lt_trans x_ge0)// (itvP x1I).
  + by rewrite (lt_le_trans _ y_le2)// (itvP x1I).
Qed.

Lemma pihalf_02_cos_pihalf : 0 <= pi / 2 <= 2 /\ cos (pi / 2) = 0.
Proof.
have [x /andP[x1 x2] cs0] := cos_exists; rewrite pihalfE.
case: xgetP => [_->[]//|/(_ x)/=].
by rewrite cs0 (le_trans _ x1)// x2 => /not_andP[].
Qed.

#[deprecated(note="Use pihalf_ge1 and pihalf_lt2 instead")]
Lemma pihalf_02 : 0 < pi / 2 < 2.
Proof.
have [pih02 cpih] := pihalf_02_cos_pihalf.
rewrite 2!lt_neqAle andbCA -andbA pih02 andbT; apply/andP; split.
  by apply/eqP => pih2; have := cos2_lt0; rewrite -pih2 cpih ltxx.
apply/eqP => pih0; have := @cos0 R.
by rewrite pih0 cpih; apply/eqP; rewrite eq_sym oner_eq0.
Qed.

Let pihalf_12 : 1 <= pi / 2 < 2.
Proof.
have [/andP[pih0 pih2] cpih] := pihalf_02_cos_pihalf.
rewrite lt_neqAle andbA andbAC pih2 andbT; apply/andP; split; last first.
  by apply/eqP => hpi2; have := cos2_lt0; rewrite -hpi2 cpih ltxx.
rewrite leNgt; apply/negP => hpi1; have [x /andP[x1 x2] cs0] := cos_exists.
have := @cos_02_uniq (pi / 2) x.
rewrite pih0 pih2 cpih (le_trans _ x1)// x2 cs0 => /(_ erefl erefl erefl erefl).
by move=> pih; move: hpi1; rewrite pih => /lt_le_trans/(_ x1); rewrite ltxx.
Qed.

Lemma pihalf_ge1 : 1 <= pi / 2.
Proof. by have /andP[] := pihalf_12. Qed.

Lemma pihalf_lt2 : pi / 2 < 2.
Proof. by have /andP[] := pihalf_12. Qed.

Lemma pi_ge2 : 2 <= pi.
Proof. by  have := pihalf_ge1; rewrite ler_pdivl_mulr// mul1r. Qed.

Lemma pi_gt0 : 0 < pi. Proof. by rewrite (lt_le_trans _ pi_ge2). Qed.

Lemma pi_ge0 : 0 <= pi. Proof. exact: (ltW pi_gt0). Qed.

Lemma sin_gt0_pihalf x : 0 < x < pi / 2 -> 0 < sin x.
Proof.
move=> /andP[x_gt0 xLpi]; apply: sin2_gt0; rewrite x_gt0 /=.
by apply: lt_trans xLpi _; exact: pihalf_lt2.
Qed.

Lemma cos_gt0_pihalf x : -(pi / 2) < x < pi / 2 -> 0 < cos x.
Proof.
wlog : x / 0 <= x => [Hw|x_ge0].
  case: (leP 0 x) => [/Hw//| x_lt_0].
  rewrite -{-1}[x]opprK ltr_oppl andbC [-- _ < _]ltr_oppl cosN.
  by apply: Hw => //; rewrite oppr_cp0 ltW.
move=> /andP[x_gt0 xLpi2]; case: (ler0P (cos x)) => // cx_le0.
have /IVT[]// : minr (cos 0) (cos x) <= 0 <= maxr (cos 0) (cos x).
  by rewrite cos0 /minr /maxr !ifN ?cx_le0 //= -leNgt (le_trans cx_le0).
- by apply/continuous_subspaceT => ?; exact: continuous_cos.
move=> x1 /itvP xx1 cx1_eq0.
suff x1E : x1 = pi/2.
  have : x1 < pi / 2 by apply: le_lt_trans xLpi2; rewrite xx1.
  by rewrite x1E ltxx.
apply: cos_02_uniq=> //; last by case pihalf_02_cos_pihalf => _ ->.
  by rewrite xx1 ltW // (lt_trans _ pihalf_lt2) // (le_lt_trans _ xLpi2) // xx1.
by rewrite divr_ge0 ?(ltW pihalf_lt2)// pi_ge0.
Qed.

Lemma cos_pihalf : cos (pi / 2) = 0. Proof. exact: pihalf_02_cos_pihalf.2. Qed.

Lemma sin_pihalf : sin (pi / 2) = 1.
Proof.
have := cos2Dsin2 (pi / 2); rewrite cos_pihalf expr0n add0r.
rewrite -[in X in _ = X -> _](expr1n _ 2%N) => /eqP; rewrite -subr_eq0 subr_sqr.
rewrite mulf_eq0=> /orP[|]; first by rewrite subr_eq0=> /eqP.
rewrite addr_eq0 => /eqP spi21; have /sin2_gt0: 0 < pi / 2 < 2.
  by rewrite pihalf_lt2 andbT (lt_le_trans _ pihalf_ge1).
by rewrite spi21 ltr0N1.
Qed.

Lemma cos_ge0_pihalf x : -(pi / 2) <= x <= pi / 2 -> 0 <= cos x.
Proof.
rewrite le_eqVlt; case: (_ =P x) => /= [<-|_].
  by rewrite cosN cos_pihalf.
rewrite le_eqVlt; case: (x =P _) => /= [->|_ H]; first by rewrite cos_pihalf.
by rewrite ltW //; apply: cos_gt0_pihalf.
Qed.

Lemma cospi : cos pi = - 1.
Proof.
by rewrite /pi mulr2n cosD -pihalfE sin_pihalf mulr1 cos_pihalf mulr0 add0r.
Qed.

Lemma sinpi : sin pi = 0.
Proof.
have := sinD (pi / 2) (pi / 2); rewrite cos_pihalf mulr0 mul0r.
by rewrite -mulrDl -mulr2n -mulr_natr -mulrA divff// mulr1 addr0.
Qed.

Lemma cos2pi : cos (pi *+ 2) = 1.
Proof. by rewrite mulr2n cosD cospi sinpi !mulrN1 mulr0 subr0 opprK. Qed.

Lemma sin2pi : sin (pi *+ 2) = 0.
Proof. by rewrite mulr2n sinD sinpi cospi !mulrN1 mulr0 oppr0 addr0. Qed.

Lemma sinDpi : alternating sin pi.
Proof. by move=> a; rewrite sinD cospi mulrN1 sinpi mulr0 addr0. Qed.

Lemma cosDpi : alternating cos pi.
Proof. by move=> a; rewrite cosD cospi mulrN1 sinpi mulr0 subr0. Qed.

Lemma sinD2pi : periodic sin (pi *+ 2).
Proof. by move=> a; rewrite sinD cos2pi sin2pi mulr0 mulr1 addr0. Qed.

Lemma cosD2pi : periodic cos (pi *+ 2).
Proof. by move=> a; rewrite cosD cos2pi mulr1 sin2pi mulr0 subr0. Qed.

Lemma cosDpihalf a : cos (a + pi / 2) = - sin a.
Proof. by rewrite cosD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma cosBpihalf a : cos (a - pi / 2) = sin a.
Proof. by rewrite cosB cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma sinDpihalf a : sin (a + pi / 2) = cos a.
Proof. by rewrite sinD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma sinBpihalf a : sin (a - pi / 2) = - cos a.
Proof. by rewrite sinB cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma sin_ge0_pi x : 0 <= x <= pi -> 0 <= sin x.
Proof.
move=> xI; rewrite -cosBpihalf cos_ge0_pihalf //.
by rewrite ler_subr_addl subrr ler_sub_addr -mulr2n -[_ *+ 2]mulr_natr divfK.
Qed.

Lemma sin_gt0_pi x : 0 < x < pi -> 0 < sin x.
Proof.
move=> xI; rewrite -cosBpihalf cos_gt0_pihalf //.
by rewrite ltr_subr_addl subrr ltr_sub_addr -mulr2n -[_ *+ 2]mulr_natr divfK.
Qed.

Lemma ltr_cos : {in `[0, pi] &, {mono cos : x y /~ y < x}}.
Proof.
move=> x y; rewrite !in_itv/= le_eqVlt; case: eqP => [<- _|_] /=.
  rewrite cos0 le_eqVlt; case: eqP => /= [<- _|_ /andP[y_gt0 gLpi]].
    by rewrite cos0 !ltxx.
  rewrite y_gt0; apply/idP.
  suff : cos y != 1 by case: ltrgtP (cos_le1 y).
  rewrite -cos0 eq_sym; apply/eqP => /Rolle [||x1|x1 /itvP x1I [_ x1D]] //.
    by apply/continuous_subspaceT => ?; exact: continuous_cos.
  case: (is_derive_cos x1) => _ /eqP; rewrite x1D eq_sym oppr_eq0 => /eqP s_eq0.
  suff : 0 < sin x1 by rewrite s_eq0 ltxx.
  by apply: sin_gt0_pi; rewrite x1I /= (lt_le_trans (_ : _ < y)) ?x1I // yI.
rewrite le_eqVlt; case: eqP => [-> _ /andP[y_ge0]|/= _ /andP[x_gt0 x_ltpi]] /=.
  rewrite cospi le_eqVlt; case: eqP => /= [-> _|/eqP yDpi y_ltpi].
    by rewrite cospi ltxx.
  by rewrite ltNge cos_geN1 ltNge ltW.
rewrite le_eqVlt; case: eqP => [<- _|_] /=.
  rewrite cos0 [_ < 0]ltNge ltW //=.
  by apply/idP/negP; rewrite -leNgt cos_le1.
rewrite le_eqVlt; case: eqP => /= [-> _ | _ /andP[y_gt0 y_ltpi]].
  rewrite cospi x_ltpi; apply/idP.
  suff : cos x != -1 by case: ltrgtP (cos_geN1 x).
  rewrite -cospi; apply/eqP => /Rolle [||x1|x1 /itvP x1I [_ x1D]] //.
    by apply/continuous_subspaceT => ?; exact: continuous_cos.
  case: (is_derive_cos x1) => _ /eqP; rewrite x1D eq_sym oppr_eq0 => /eqP s_eq0.
  suff : 0 < sin x1 by rewrite s_eq0 ltxx.
  by apply: sin_gt0_pi; rewrite x1I /= (lt_le_trans (_ : _ < x)) ?x1I.
wlog xLy : x y x_gt0 x_ltpi y_gt0 y_ltpi / x <= y => [H | ].
  case: (lerP x y) => [/H //->//|yLx].
  by rewrite !ltNge ltW ?(ltW yLx) // H // ltW.
case: (x =P y) => [->| /eqP xDy]; first by rewrite ltxx.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
rewrite xLLs -subr_gt0 -opprB; rewrite -subr_gt0 in xLLs; apply/idP.
have [x1|z /itvP zI ->] := @MVT_segment _ cos (- sin) _ _ xLy.
  by apply/continuous_subspaceT => ?; exact: continuous_cos.
rewrite -mulNr opprK mulr_gt0 //; apply: sin_gt0_pi.
by rewrite (lt_le_trans x_gt0) ?zI //= (le_lt_trans _ y_ltpi) ?zI.
Qed.

Lemma ltr_sin : {in `[ (- (pi/2)), pi/2] &, {mono sin : x y / x < y}}.
Proof.
move=> x y /itvP xpi /itvP ypi; rewrite -[sin x]opprK ltr_oppl.
rewrite -!cosDpihalf -[x < y](ltr_add2r (pi /2)) ltr_cos// !in_itv/=.
- by rewrite -ler_subl_addr sub0r xpi/= [leRHS]splitr ler_add2r xpi.
- by rewrite -ler_subl_addr sub0r ypi/= [leRHS]splitr ler_add2r ypi.
Qed.

Lemma cos_inj : {in `[0,pi] &, injective (@cos R)}.
Proof.
move=> x y x0pi y0pi xy; apply/eqP; rewrite eq_le; apply/andP; split.
- by have := ltr_cos y0pi x0pi; rewrite xy ltxx => /esym/negbT; rewrite -leNgt.
- by have := ltr_cos x0pi y0pi; rewrite xy ltxx => /esym/negbT; rewrite -leNgt.
Qed.

Lemma sin_inj : {in `[(- (pi/2)), (pi/2)] &, injective sin}.
Proof.
move=> x y /itvP xpi /itvP ypi sinE; have : - sin x = - sin y by rewrite sinE.
rewrite -!cosDpihalf => /cos_inj h; apply/(addIr (pi/2))/h; rewrite !in_itv/=.
- by rewrite -ler_subl_addr sub0r xpi/= [leRHS]splitr ler_add2r xpi.
- by rewrite -ler_subl_addr sub0r ypi/= [leRHS]splitr ler_add2r ypi.
Qed.

End Pi.

Arguments pi {R}.

Section Tan.
Variable R : realType.

Definition tan (x : R) := sin x / cos x.

Lemma tan0 : tan 0 = 0 :> R.
Proof. by rewrite /tan sin0 cos0 mul0r. Qed.

Lemma tanpi : tan pi = 0.
Proof. by rewrite /tan sinpi mul0r. Qed.

Lemma tanN x : tan (- x) = - tan x.
Proof. by rewrite /tan sinN cosN mulNr. Qed.

Lemma tanD x y : cos x != 0 -> cos y != 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
move=> cxNZ cyNZ.
rewrite /tan sinD cosD !addf_div // [sin y * cos x]mulrC -!mulrA -invfM.
congr (_ / _).
rewrite mulrBr mulr1 !mulrA.
rewrite -[_ * _ * sin x]mulrA [cos x * (_ * _)]mulrC mulfK //.
by rewrite -[_ * _ * sin y]mulrA [cos y * (_ * _)]mulrC mulfK.
Qed.

Lemma tan_mulr2n x :
  cos x != 0 -> tan (x *+ 2) = tan x *+ 2 / (1 -  tan x ^+ 2).
Proof.
move=> cxNZ.
rewrite /tan cos_mulr2n sin_mulr2n.
rewrite !mulr2n exprMn exprVn -[in RHS](divff (_ : 1 != 0)) //.
rewrite -mulNr !addf_div ?sqrf_eq0 //.
rewrite mul1r mulr1 -!mulrA -invfM -expr2; congr (_ / _).
  by rewrite [cos x * _]mulrC.
rewrite mulrCA mulrA mulfK  ?sqrf_eq0 // [X in _ = _ - X]sin2cos2.
by rewrite opprB addrA.
Qed.

Lemma cos2_tan2 x : cos x != 0 -> (cos x) ^- 2 = 1 + (tan x) ^+ 2.
Proof.
move=> cosx.
rewrite /tan exprMn [X in _ = 1 + X * _]sin2cos2 mulrBl -exprMn divff //.
by rewrite expr1n addrCA subrr addr0 mul1r exprVn.
Qed.

Lemma tan_pihalf : tan (pi / 2) = 0.
Proof. by rewrite /tan cos_pihalf invr0 mulr0. Qed.

Lemma tan_piquarter : tan (pi / 4%:R) = 1.
Proof.
rewrite /tan -cosBpihalf (splitr (pi / 2)) opprD addrA -mulrA -invfM -natrM.
rewrite subrr sub0r cosN divff// gt_eqF// cos_gt0_pihalf//.
rewrite ltr_pmul2l ?pi_gt0// ltf_pinv ?qualifE// ltr_nat andbT.
by rewrite (@lt_trans _ _ 0)// ?oppr_lt0 ?divr_gt0 ?pi_gt0.
Qed.

Lemma tanDpi x : tan (x + pi) = tan x.
Proof. by rewrite /tan cosDpi sinDpi mulNr invrN mulrN opprK. Qed.

Lemma continuous_tan x : cos x != 0 -> {for x, continuous tan}.
Proof.
move=> cxNZ.
apply: continuousM; first exact: continuous_sin.
exact/(continuousV cxNZ)/continuous_cos.
Qed.

Lemma is_derive_tan x :
  cos x != 0 -> is_derive x 1 tan ((cos x)^-2).
Proof.
move=> cxNZ; apply: trigger_derive.
rewrite /= ![_ *: - _]mulrN mulNr mulrN opprK [_^-1 *: _]mulVf //.
rewrite mulrCA -expr2 [X in _ * X + _ = _]sin2cos2.
by rewrite mulrBr mulr1 mulVf ?sqrf_eq0 // subrK.
Qed.

Lemma derivable_tan x : cos x != 0 -> derivable tan x 1.
Proof. by move=> /is_derive_tan[]. Qed.

Lemma ltr_tan : {in `](- (pi/2)), (pi/2)[ &, {mono tan : x y / x < y}}.
Proof.
move=> x y; wlog xLy : x y / x <= y => [H xB yB|/itvP xB /itvP yB].
  case: (lerP x y) => [/H //->//|yLx].
  by rewrite !ltNge ltW ?(ltW yLx) // H // ltW.
case: (x =P y) => [->| /eqP xDy]; first by rewrite ltxx.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
rewrite -subr_gt0 xLLs; rewrite -subr_gt0 in xLLs; apply/idP.
have [x1 /itvP x1I|z |] := @MVT_segment _ tan (fun x => (cos x) ^-2) _ _ xLy.
- apply: is_derive_tan.
  rewrite gt_eqF // cos_gt0_pihalf // (@lt_le_trans _  _ x) ?x1I ?xB//=.
  by rewrite (@le_lt_trans _  _ y) ?x1I ?yB.
- apply/continuous_in_subspaceT => ? -/[!(@mem_setE R)] /itvP inI.
  apply: continuous_tan; rewrite gt_eqF// cos_gt0_pihalf//.
  by rewrite (@lt_le_trans _  _ x) ?xB ?inI// (@le_lt_trans _  _ y) ?yB ?inI.
- move=> x1 /itvP x1I ->.
  rewrite mulr_gt0 // invr_gt0 // exprn_gte0 // cos_gt0_pihalf //.
  by rewrite (@lt_le_trans _  _ x) ?x1I ?xB//= (@le_lt_trans _  _ y) ?x1I ?yB.
Qed.

Lemma tan_inj : {in `](- (pi/2)), (pi/2)[ &, injective tan}.
Proof.
move=> x y xB yB tanE.
by case: (ltrgtP x y); rewrite // -ltr_tan ?tanE ?ltxx.
Qed.

End Tan.
Arguments tan {R}.

#[global] Hint Extern 0 (is_derive _ _ tan _) =>
  (eapply is_derive_tan; first by []) : typeclass_instances.

Section Acos.
Variable R : realType.

Definition acos (x : R) : R := get [set y | 0 <= y <= pi /\ cos y = x].

Lemma acos_def x :
  -1 <= x <= 1 -> 0 <= acos x <= pi /\ cos (acos x) = x.
Proof.
move=> xB; rewrite /acos; case: xgetP => //= He.
pose f y := cos y - x.
have /(IVT (@pi_ge0 _))[] // : minr (f 0) (f pi) <= 0 <= maxr (f 0) (f pi).
  rewrite /f cos0 cospi /minr /maxr ltr_add2r -subr_lt0 opprK (_ : 1 + 1 = 2)//.
  by rewrite ltrn0 subr_le0 subr_ge0.
- move=> y y0pi.
  by apply: continuousB; apply/continuous_in_subspaceT => ? ?;
    [exact: continuous_cos|exact: cst_continuous].
- rewrite /f => x1 /itvP x1I /eqP; rewrite subr_eq0 => /eqP cosx1E.
  by case: (He x1); rewrite !x1I.
Qed.

Lemma acos_ge0 x : -1 <= x <= 1 -> 0 <= acos x.
Proof. by move=> /acos_def[/andP[]]. Qed.

Lemma acos_lepi x : -1 <= x <= 1 -> acos x <= pi.
Proof. by move=> /acos_def[/andP[]]. Qed.

Lemma acosK : {in `[(-1),1], cancel acos cos}.
Proof. by move=> x; rewrite in_itv/==> /acos_def[/andP[]]. Qed.

Lemma acos_gt0 x : -1 <= x < 1 -> 0 < acos x.
Proof.
move=> /andP[x_geN1 x_lt1]; move: (x_lt1).
have : 0 <= acos x by rewrite acos_ge0 // x_geN1 ltW.
have : cos (acos x) = x by rewrite acosK// in_itv/= x_geN1/= ltW.
by case: ltrgt0P => // ->; rewrite cos0 => ->; rewrite ltxx.
Qed.

Lemma acos_ltpi x : -1 < x <= 1 -> acos x < pi.
Proof.
move=> /andP[x_gtN1 x_le1]; move: (x_gtN1).
have : acos x <= pi by rewrite acos_lepi // x_le1 ltW.
have : cos (acos x) = x by rewrite acosK// in_itv/= x_le1 ltW.
by case: (ltrgtP (acos x) pi) => // ->; rewrite cospi => ->; rewrite ltxx.
Qed.

Lemma cosK : {in `[0, pi], cancel cos acos}.
Proof.
move=> x xB; apply: cos_inj => //; rewrite ?acosK//; last first.
  by move: xB; rewrite !in_itv/= => /andP[? ?];rewrite cos_geN1 cos_le1.
move: xB; rewrite !in_itv/= => /andP[? ?].
by rewrite acos_ge0 ?acos_lepi ?cos_geN1 ?cos_le1.
Qed.

Lemma acos1 : acos (1 : R) = 0.
Proof.
by have := @cosK 0; rewrite cos0 => -> //; rewrite in_itv //= lexx pi_ge0.
Qed.

Lemma acos0 : acos (0 : R) = pi / 2%:R.
Proof.
have := @cosK (pi / 2%:R).
rewrite cos_pihalf => -> //; rewrite in_itv//= divr_ge0 ?ler0n ?pi_ge0//=.
by rewrite ler_pdivr_mulr ?ltr0n// ler_pemulr ?pi_ge0// ler1n.
Qed.

Lemma acosN a : -1 <= a <= 1 -> acos (- a) = pi - acos a.
Proof.
move=> a1; have ? : -1 <= - a <= 1 by rewrite ler_oppl opprK ler_oppl andbC.
apply: cos_inj; first by rewrite in_itv/= acos_ge0//= acos_lepi.
- by rewrite in_itv/= subr_ge0 acos_lepi//= ler_subl_addl ler_addr acos_ge0.
- by rewrite addrC cosDpi cosN !acosK.
Qed.

Lemma acosN1 : acos (- 1) = (pi : R).
Proof. by rewrite acosN ?acos1 ?subr0 ?lexx// -subr_ge0 opprK addr_ge0. Qed.

Lemma cosKN a : - pi <= a <= 0 -> acos (cos a) = - a.
Proof.
by move=> pia0; rewrite -(cosN a) cosK// in_itv/= ler_oppr oppr0 ler_oppl andbC.
Qed.

Lemma sin_acos x : -1 <= x <= 1 -> sin (acos x) = Num.sqrt (1 - x^+2).
Proof.
move=> xB.
rewrite -[LHS]ger0_norm; last by rewrite sin_ge0_pi // acos_ge0 ?acos_lepi.
by rewrite -sqrtr_sqr sin2cos2 acosK.
Qed.

Lemma continuous_acos x : -1 < x < 1 -> {for x, continuous acos}.
Proof.
move=> /andP[x_gtN1 x_lt1]; rewrite -[x]acosK; first last.
  by have : -1 <= x <= 1 by rewrite !ltW //; case/andP: xB.
apply: nbhs_singleton (near_can_continuous _ _); last first.
   by near=> z; apply: continuous_cos.
have /near_in_itv aI : acos x \in `]0, pi[.
  suff : 0 < acos x < pi by [].
  by rewrite acos_gt0 ?ltW //= acos_ltpi // ltW ?andbT.
near=> z; apply: cosK.
suff /itvP zI : z \in `]0, pi[ by have : 0 <= z <= pi by rewrite ltW ?zI.
by near: z.
Unshelve. all: by end_near. Qed.

Lemma is_derive1_acos (x : R) :
  -1 < x < 1 -> is_derive x 1 acos (- (Num.sqrt (1 - x ^+ 2))^-1).
Proof.
move=> /andP[x_gtN1 x_lt1]; rewrite -sin_acos ?ltW // -invrN.
rewrite -{1}[x]acosK; last by have : -1 <= x <= 1 by rewrite ltW // ltW.
have /near_in_itv aI : acos x \in `]0, pi[.
  suff : 0 < acos x < pi by [].
  by rewrite acos_gt0 ?ltW //= acos_ltpi // ltW ?andbT.
apply: (@is_derive_inverse R cos).
- near=> z; apply: cosK.
  suff /itvP zI : z \in `]0, pi[ by have : 0 <= z <= pi by rewrite ltW ?zI.
  by near: z.
- by near=> z; apply: continuous_cos.
- rewrite oppr_eq0 sin_acos ?ltW // sqrtr_eq0 // -ltNge subr_gt0.
  rewrite -real_normK ?qualifE; last by case: ltrgt0P.
  by rewrite exprn_cp1 // ltr_norml x_gtN1.
Unshelve. all: by end_near. Qed.

End Acos.

#[global] Hint Extern 0 (is_derive _ 1 (@acos _) _) =>
  (eapply is_derive1_acos; first by []) : typeclass_instances.

Section Asin.
Variable R : realType.

Definition asin (x : R) : R := get [set y | -(pi / 2) <= y <= pi / 2 /\ sin y = x].

Lemma asin_def x :
  -1 <= x <= 1 -> -(pi / 2) <= asin x <= pi / 2 /\ sin (asin x) = x.
Proof.
move=> xB; rewrite /asin; case: xgetP => //= He.
pose f y := sin y - x.
have /IVT[] // :
    minr (f (-(pi/2))) (f (pi/2)) <= 0 <= maxr (f (-(pi/2))) (f (pi/2)).
  rewrite /f sinN sin_pihalf /minr /maxr ltr_add2r -subr_gt0 opprK.
  by rewrite (_ : 1 + 1 = 2)// ltr0n/= subr_le0 subr_ge0.
- by rewrite -subr_ge0 opprK -splitr pi_ge0.
- by move=> *; apply: continuousB; apply/continuous_in_subspaceT => ? ?;
   [exact: continuous_sin| exact: cst_continuous].
- rewrite /f => x1 /itvP x1I /eqP; rewrite subr_eq0 => /eqP sinx1E.
  by case: (He x1); rewrite !x1I.
Qed.

Lemma asin_geNpi2 x : -1 <= x <= 1 -> -(pi / 2) <= asin x.
Proof. by move=> /asin_def[/andP[]]. Qed.

Lemma asin_lepi2 x : -1 <= x <= 1 -> asin x <= pi / 2.
Proof. by move=> /asin_def[/andP[]]. Qed.

Lemma asinK : {in `[(-1),1], cancel asin sin}.
Proof. by move=> x; rewrite in_itv/= => /asin_def[/andP[]]. Qed.

Lemma asin_ltpi2 x : -1 <= x < 1 -> asin x < pi/2.
Proof.
move=> /andP[x_geN1 x_lt1]; move: (x_lt1).
have : asin x <= pi / 2 by rewrite asin_lepi2 // x_geN1 ltW.
have : sin (asin x) = x by rewrite asinK// in_itv/= x_geN1 ltW.
case: (ltrgtP _ ((pi / 2))) => // ->.
by rewrite sin_pihalf => <-; rewrite ltxx.
Qed.

Lemma asin_gtNpi2 x : -1 < x <= 1 -> - (pi / 2) < asin x.
Proof.
move=> /andP[x_gtN1 x_le1]; move: (x_gtN1).
have : - (pi / 2) <= asin x by rewrite asin_geNpi2 // x_le1 ltW.
have : sin (asin x) = x by rewrite asinK// in_itv/= x_le1 ltW.
by case: (ltrgtP (asin x)) => //->; rewrite sinN sin_pihalf => <-; rewrite ltxx.
Qed.

Lemma sinK : {in `[(- (pi / 2)), pi / 2], cancel sin asin}.
Proof.
move=> x; rewrite !in_itv/= => xB ; apply: sin_inj => //; last first.
  by rewrite asinK// in_itv/= sin_geN1 sin_le1.
by rewrite in_itv/= asin_geNpi2/= ?asin_lepi2 ?sin_geN1 ?sin_le1.
Qed.

Lemma cos_asin x : -1 <= x <= 1 -> cos (asin x) = Num.sqrt (1 - x^+2).
Proof.
move=> xB; rewrite -[LHS]ger0_norm; first by rewrite -sqrtr_sqr cos2sin2 asinK.
by apply: cos_ge0_pihalf; rewrite asin_lepi2 // asin_geNpi2.
Qed.

Lemma continuous_asin x : -1 < x < 1 -> {for x, continuous asin}.
Proof.
move=> /andP[x_gtN1 x_lt1]; rewrite -[x]asinK; first last.
  by have : -1 <= x <= 1 by rewrite !ltW //; case/andP: xB.
apply: nbhs_singleton (near_can_continuous _ _); last first.
  by near=> z; apply: continuous_sin.
have /near_in_itv aI : asin x \in `](-(pi/2)), (pi/2)[.
  suff : - (pi / 2) < asin x < pi / 2 by [].
  by rewrite asin_gtNpi2 ?ltW ?andbT //= asin_ltpi2 // ltW.
near=> z; apply: sinK.
suff /itvP zI : z \in `](-(pi/2)), (pi/2)[.
  by have : - (pi / 2) <= z <= pi / 2 by rewrite ltW ?zI.
by near: z.
Unshelve. all: by end_near. Qed.

Lemma is_derive1_asin (x : R) :
  -1 < x < 1 -> is_derive x 1 asin ((Num.sqrt (1 - x ^+ 2))^-1).
Proof.
move=> /andP[x_gtN1 x_lt1]; rewrite -cos_asin ?ltW //.
rewrite -{1}[x]asinK; last by have : -1 <= x <= 1 by rewrite ltW // ltW.
have /near_in_itv aI : asin x \in `](-(pi/2)), (pi/2)[.
  suff : -(pi/2) < asin x < pi/2 by [].
  by rewrite asin_gtNpi2 ?ltW ?andbT //= asin_ltpi2 // ltW.
apply: (@is_derive_inverse R sin).
- near=> z; apply: sinK.
  suff /itvP zI : z \in `](-(pi/2)), (pi/2)[.
    by have : - (pi / 2) <= z <= pi / 2 by rewrite ltW ?zI.
  by near: z.
- by near=> z; exact: continuous_sin.
- rewrite cos_asin ?ltW // sqrtr_eq0 // -ltNge subr_gt0.
  rewrite -real_normK ?qualifE; last by case: ltrgt0P.
  by rewrite exprn_cp1 // ltr_norml x_gtN1.
Unshelve. all: by end_near. Qed.

End Asin.

#[global] Hint Extern 0 (is_derive _ 1 (@asin _) _) =>
  (eapply is_derive1_asin; first by []) : typeclass_instances.

Section Atan.
Variable R : realType.

Definition atan (x : R) : R :=
  get [set y | -(pi / 2) < y < pi / 2 /\ tan y = x].

(* Did not see how to use ITV like in the other *)
Lemma atan_def x : -(pi / 2) < atan x < pi / 2 /\ tan (atan x) = x.
Proof.
rewrite /atan; case: xgetP => //= He.
pose x1 := Num.sqrt (1 + x^+ 2) ^-1.
have ox2_gt0 : 0 < 1 + x^2.
  by apply: lt_le_trans (_ : 1 <= _); rewrite ?ler_addl ?sqr_ge0.
have ox2_ge0 : 0 <= 1 + x^2 by rewrite ltW.
have x1B : -1 <= x1 <= 1.
  rewrite -ler_norml /x1 ger0_norm ?sqrtr_ge0 // -[leRHS]sqrtr1.
  by rewrite ler_psqrt ?qualifE ?invr_gte0 //= invf_cp1 // ler_addl sqr_ge0.
case: (He (Num.sg x * acos x1)); split; last first.
  case: (x =P 0) => [->|/eqP xD0]; first by rewrite /tan sgr0 mul0r sin0 mul0r.
  rewrite /tan sin_sg cos_sg // acosK ?sin_acos //.
  rewrite /x1 sqr_sqrtr// ?invr_ge0 //.
  rewrite -{1}[_^-1 in X in X / _ = _]mul1r.
  rewrite -{1}[X in X - _](divff (_: 1 != 0)) //.
  rewrite -mulNr addf_div ?lt0r_neq0 //.
  rewrite mul1r mulr1 [X in X - 1]addrC addrK // sqrtrM ?sqr_ge0 //.
  rewrite sqrtrV // invrK // mulrA divfK //; last by rewrite sqrtr_eq0 -ltNge.
  by rewrite sqrtr_sqr mulr_sg_norm.
rewrite -ltr_norml normrM.
have pi2 : 0 < pi / 2 :> R by rewrite divr_gt0 // pi_gt0.
case: (x =P 0) => [->|/eqP xD0]; first by rewrite sgr0 normr0 mul0r.
rewrite normr_sg xD0 mul1r ltr_norml.
rewrite (@lt_le_trans _ _ 0) ?acos_ge0 ?oppr_cp0 //=.
rewrite -ltr_cos ?in_itv/= ?acos_ge0/= ?acos_lepi//; last first.
  by rewrite divr_ge0 ?pi_ge0//= ler_pdivr_mulr// ler_pmulr ?pi_gt0// ler1n.
by rewrite cos_pihalf acosK // ?sqrtr_gt0 ?invr_gt0.
Qed.

Lemma atan_gtNpi2 x : - (pi / 2) < atan x.
Proof. by case: (atan_def x) => [] /andP[]. Qed.

Lemma atan_ltpi2 x : atan x < pi / 2.
Proof. by case: (atan_def x) => [] /andP[]. Qed.

Lemma atanK : cancel atan tan.
Proof. by move=> x; case: (atan_def x). Qed.

Lemma atan0 : atan 0 = 0 :> R.
Proof.
apply: tan_inj; last by rewrite atanK tan0.
- by rewrite in_itv/= atan_gtNpi2 atan_ltpi2.
- by rewrite in_itv/= oppr_cp0 divr_gt0 ?pi_gt0.
Qed.

Lemma atan1 : atan 1 = pi / 4%:R :> R.
Proof.
apply: tan_inj; first 2 last.
  by rewrite atanK tan_piquarter.
  by rewrite in_itv/= atan_gtNpi2 atan_ltpi2.
rewrite in_itv/= -mulNr (lt_trans _ (_ : 0 < _ )) /=; last 2 first.
  by rewrite mulNr oppr_cp0 divr_gt0 // pi_gt0.
  by rewrite divr_gt0 ?pi_gt0 // ltr0n.
rewrite ltr_pdivr_mulr// -mulrA ltr_pmulr// ?pi_gt0//.
by rewrite (natrM _ 2 2) mulrA mulVf// mul1r ltr1n.
Qed.

Lemma atanN x : atan (- x) = - atan x.
Proof.
apply: tan_inj; first by rewrite in_itv/= atan_ltpi2 atan_gtNpi2.
- by rewrite in_itv/= ltr_oppl opprK ltr_oppl andbC atan_ltpi2 atan_gtNpi2.
- by rewrite tanN !atanK.
Qed.

Lemma tanK : {in `](- (pi / 2)), (pi / 2)[ , cancel tan atan}.
Proof.
move=> x xB; apply tan_inj => //; rewrite ?atanK//.
by rewrite in_itv/= atan_gtNpi2 atan_ltpi2.
Qed.

Lemma continuous_atan x : {for x, continuous atan}.
Proof.
rewrite -[x]atanK.
have /near_in_itv aI : atan x \in `](-(pi / 2)), (pi / 2)[.
  suff : - (pi / 2) < atan x < pi / 2 by [].
  by rewrite atan_gtNpi2 atan_ltpi2.
apply: nbhs_singleton (near_can_continuous _ _); last first.
  by near=> z; apply/continuous_tan/lt0r_neq0/cos_gt0_pihalf; near: z.
by near=> z; apply: tanK; near: z.
Unshelve. all: by end_near. Qed.

Lemma cos_atan x : cos (atan x) = (Num.sqrt (1 + x ^+ 2)) ^-1.
Proof.
have cos_gt0 : 0 < cos (atan x).
  by apply: cos_gt0_pihalf; rewrite atan_gtNpi2 atan_ltpi2.
have cosD0 : cos (atan x) != 0 by apply: lt0r_neq0.
have /eqP : cos (atan x) ^+2 = (Num.sqrt (1 + x ^+ 2))^-2.
  by rewrite -[LHS]invrK cos2_tan2 // atanK sqr_sqrtr // addr_ge0 // sqr_ge0.
rewrite -exprVn eqf_sqr => /orP[] /eqP // cosE.
move: cos_gt0; rewrite cosE ltNge; case/negP.
by rewrite oppr_le0 invr_ge0 sqrtr_ge0.
Qed.

Global Instance is_derive1_atan (x : R) : is_derive x 1 atan (1 + x ^+ 2)^-1.
Proof.
rewrite -{1}[x]atanK.
have cosD0 : cos (atan x) != 0.
  by apply/lt0r_neq0/cos_gt0_pihalf; rewrite atan_gtNpi2 atan_ltpi2.
have /near_in_itv aI : atan x \in `](-(pi/2)), (pi/2)[.
  suff : - (pi / 2) < atan x < pi / 2 by [].
  by rewrite atan_gtNpi2 atan_ltpi2.
apply: (@is_derive_inverse R tan).
- by near=> z; apply: tanK; near: z.
- by near=> z; apply/continuous_tan/lt0r_neq0/cos_gt0_pihalf; near: z.
- by rewrite -[X in 1 + X ^+ 2]atanK -cos2_tan2 //; exact: is_derive_tan.
by apply/lt0r_neq0/(@lt_le_trans _ _ 1) => //; rewrite ler_addl sqr_ge0.
Unshelve. all: by end_near. Qed.

End Atan.
