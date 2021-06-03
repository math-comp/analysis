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

End cvg_extra.

Variable R : realType.

Lemma cvg_series_bounded (f : R ^nat) :
  cvg (series f) -> exists2 K, 0 < K & (forall i, `|f i| < K).
Proof.
move=> /cvg_series_cvg_0/cvgP/cvg_seq_bounded[r [_ /(_ (r + 1)) fr]].
exists (maxr 1 (r + 2)); [by rewrite lt_maxr ltr01 | move=> n].
by rewrite (le_lt_trans (fr _ _ _)) ?ltr_spaddr// lt_maxr ltr_add2l ltr1n orbT.
Qed.

(* NB: useful? *)
Lemma eq_cvg_lim : forall (R : realType) (f g : R ^nat),
  f = g -> (f --> lim f) = (g --> lim g).
Proof. by move=> R1 f1 g1 ->. Qed.

Lemma eq_cvgl (f g : R ^nat) (x : R) : f = g -> (f --> x) = (g --> x).
Proof. by move->. Qed.

Lemma seriesN (f : R ^nat) : series (- f) = - series f.
Proof. by rewrite funeqE => n; rewrite /series /= sumrN. Qed.

Lemma seriesZr (f : R ^nat) k : series (k *: f) = k *: series f.
Proof. by rewrite funeqE => n; rewrite /series /= -scaler_sumr. Qed.

Lemma seriesD (f g : R ^nat) : series (f + g) = series f + series g.
Proof. by rewrite /series /= funeqE => n; rewrite big_split. Qed.

Lemma is_cvg_seriesN (f : R ^nat) : cvg (series (- f)) = cvg (series f).
Proof. by rewrite seriesN is_cvgNE. Qed.

Lemma lim_seriesN (f : R ^nat) : cvg (series f) ->
  lim (series (- f)) = - lim (series f).
Proof. by move=> cf; rewrite seriesN limN. Qed.

Lemma is_cvg_seriesZr (f : R ^nat) k : cvg (series f) -> cvg (series (k *: f)).
Proof. by move=> cf; rewrite seriesZr; exact: is_cvgZr. Qed.

Lemma lim_seriesZr (f : R ^nat) k : cvg (series f) ->
  lim (series (k *: f)) = k *: lim (series f).
Proof. by move=> cf; rewrite seriesZr limZr. Qed.

Lemma is_cvg_seriesD (f g : R ^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f + g)).
Proof. by move=> cf cg; rewrite seriesD; exact: is_cvgD. Qed.

Lemma lim_seriesD (f g : R ^nat) : cvg (series f) -> cvg (series g) ->
  lim (series (f + g)) = lim (series f) + lim (series g).
Proof. by move=> cf cg; rewrite seriesD limD. Qed.

Lemma is_cvg_seriesB (f g : R ^nat) :
  cvg (series f) -> cvg (series g) -> cvg (series (f - g)).
Proof. by move=> cf cg; apply: is_cvg_seriesD; rewrite ?is_cvg_seriesN. Qed.

Lemma lim_seriesB (f g : R ^nat) : cvg (series f) -> cvg (series g) ->
  lim (series (f - g)) = lim (series f) - lim (series g).
Proof. by move=> Cf Cg; rewrite lim_seriesD ?is_cvg_seriesN// lim_seriesN. Qed.

Lemma lim_series_norm (f : R ^nat) :
  cvg [normed series f] -> `|lim (series f)| <= lim [normed series f].
Proof.
move=> cnf; have cf := normed_cvg cnf.
rewrite -lim_norm // (ler_lim (is_cvg_norm cf) cnf) //.
by near=> x; rewrite ler_norm_sum.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_series_le (f g : R ^nat) :
  cvg (series f) -> cvg (series g) -> (forall n, f n <= g n) ->
  lim (series f) <= lim (series g).
Proof.
by move=> cf cg fg; apply (ler_lim cf cg); near=> x; rewrite ler_sum.
Grab Existential Variables. all: end_near. Qed.

End Cvg.

(******************************************************************************)
(*  Some addition for  continuous                                             *)
(******************************************************************************)

(* About continuous *)

Section continuous.
Variables (K : numFieldType) (U V : normedModType K).

Lemma continuous_shift (f : U -> V) u :
  {for u, continuous f} = {for 0, continuous (f \o shift u)}.
Proof. by rewrite [in RHS]forE /= add0r cvg_comp_shift add0r. Qed.

Lemma continuous_withinNshiftx (f : U -> V) u :
  f \o shift u @ 0^' --> f u <-> {for u, continuous f}.
Proof.
rewrite continuous_shift; split=> [cfu|].
  by apply/(continuous_withinNx _ _).2/(cvg_trans cfu); rewrite /= add0r.
by move/(continuous_withinNx _ _).1/cvg_trans; apply; rewrite /= add0r.
Qed.

End continuous.

(******************************************************************************)
(*  Some addition for  is_derive                                              *)
(******************************************************************************)

Lemma chain_rule (R : realFieldType) (f g : R -> R) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  (g \o f)^`() x = g^`() (f x) * f^`() x.
Proof.
move=> /derivable1_diffP df /derivable1_diffP dg.
rewrite derive1E'; last exact/differentiable_comp.
rewrite diff_comp // !derive1E' //= -{1}[X in 'd  _ _ X = _]mulr1.
by rewrite {1}linearZ mulrC.
Qed.

Section is_derive.

Variable R : realType.

Global Instance is_derive1_id (x : R) : is_derive x 1 id 1.
Proof.
constructor; first exact/derivable1_diffP.
by rewrite deriveE // (@diff_lin _ _ _ [linear of idfun]).
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

Global Instance is_derive1_chain (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b ->
  is_derive x 1 (f \o g) (a * b).
Proof.
move=> [fgxv <-{a}] [gv <-{b}]; apply: (@DeriveDef _ _ _ _ _ (f \o g)).
  apply/derivable1_diffP/differentiable_comp; first exact/derivable1_diffP.
  by move/derivable1_diffP in fgxv.
by rewrite -derive1E (chain_rule gv fgxv) 2!derive1E.
Qed.

(* Trick to trigger type class resolution *)
Lemma trigger_derive (f : R -> R) x x1 y1 : 
  is_derive x 1 f x1 -> x1 = y1 -> is_derive x 1 f y1.
Proof. by move=> Hi <-. Qed.

End is_derive.

(******************************************************************************)
(* Unfold function application (f + f) 0 gives f 0 + f 0                      *)
(******************************************************************************)

Ltac rcfE :=
repeat (
(let u := fresh "u" in
set u := (@GRing.exp (fct_ringType _ _) _ _ _);
move: @u; rewrite {1}/GRing.exp /=) ||
(let u := fresh "u" in
set u := (@GRing.scale (fct_ringType _ _) _ _ _);
move: @u; rewrite {1}/GRing.scale /=) ||

(let u := fresh "u" in
set u := (@GRing.scale (fct_ringType _ _) _ _ _);
move: @u; rewrite {1}/GRing.scale /=) ||
(let u := fresh "u" in
set u := (@GRing.add (fct_zmodType _ _) _ _ _);
move: @u; rewrite {1}/+%R /=) ||
(let u := fresh "u" in
set u := (@GRing.mul (fct_ringType _ _) _ _ _);
move: @u; rewrite {1}/*%R /=) ||
(let u := fresh "u" in
set u := (@GRing.opp (fct_ringType _ _) _ _);
move: @u; rewrite {1}/-%R /=) ||
(let u := fresh "u" in
set u := (cst _ _);
move: @u; rewrite {1}/cst/=) ||
(let u := fresh "u" in
set u := (@comp _ _ _ _ _);
move: @u; rewrite {1}/comp /=) ).

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
apply: cvgB => //; rewrite -cvg_shiftS.
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

(* TODO: rebase: this section is not in master/sequences.v *)
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

(* TODO: rebase: this section is not in master/sequences.v *)
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

(* TODO: rebase: exp is not in master and called expR *)
Definition exp (x : R) : R := lim (series (exp_coeff x)).

Lemma exp0 : exp 0 = 1.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. Qed.

Lemma exp_ge1Dx x : 0 <= x -> 1 + x <= exp x.
Proof.
 move=> x_gt0; rewrite /exp.
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
Grab Existential Variables. all: end_near. Qed.

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

Lemma pexp_gt1 x: 0 < x -> 1 < exp x.
Proof.
move=> x_gt0.
apply: lt_le_trans (exp_ge1Dx (ltW x_gt0)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.

Lemma exp_gt0 x : 0 < exp x.
Proof.
case: (ltrgt0P x) => [x_gt0|x_gt0|->].
- by apply: lt_trans (pexp_gt1 x_gt0).
- have F : 0 < exp (- x) by apply: lt_trans (pexp_gt1 _); rewrite ?oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expxMexpNx_1.
by rewrite exp0.
Qed.

Lemma expN x : exp (-x) = (exp x)^-1.
Proof.
apply: (mulfI (lt0r_neq0 (exp_gt0 x))).
by rewrite expxMexpNx_1 mulfV // (lt0r_neq0 (exp_gt0 x)).
Qed.

Lemma expD x y : exp (x + y) = exp x * exp y.
Proof.
apply: (mulIf (lt0r_neq0 (exp_gt0 (- x)))).
rewrite expxDyMexpx expN [_ * exp y]mulrC mulfK //.
by case: ltrgt0P (exp_gt0 x).
Qed.

Lemma expMm n x : exp (n%:R * x) = exp x ^+ n.
Proof.
elim: n x => [x|n IH x] /=; first by rewrite mul0r expr0 exp0.
by rewrite exprS -add1n natrD mulrDl mul1r expD IH.
Qed.

Lemma exp_gt1 x:  (1 < exp x) = (0 < x).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite exp0.
- by rewrite (pexp_gt1 x_gt0).
apply/idP/negP.
rewrite -[x]opprK expN -leNgt invf_cp1 ?exp_gt0 //.
by rewrite ltW // pexp_gt1 // lter_oppE.
Qed.

Lemma exp_lt1 x:  (exp x < 1) = (x < 0).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite exp0 //.
- by apply/idP/negP; rewrite -leNgt ltW // exp_gt1.
by rewrite -[x]opprK expN invf_cp1 ?exp_gt0 // exp_gt1 lter_oppE.
Qed.

Lemma expB x y : exp (x - y) = exp x / exp y.
Proof. by rewrite expD expN. Qed.

Lemma ltr_exp : {mono exp : x y / x < y}.
Proof.
move=> x y.
by rewrite -{1}(subrK x y) expD ltr_pmull ?exp_gt0 // exp_gt1 subr_gt0.
Qed.

Lemma ler_exp : {mono exp : x y / x <= y}.
Proof.
move=> x y.
case: (ltrgtP x y) => [xLy|yLx|<-].
- by rewrite ltW // ltr_exp.
- by rewrite leNgt ltr_exp yLx.
by rewrite lexx.
Qed.

Lemma expI : injective exp.
Proof.
move=> x y exE.
by have [] := (ltr_exp x y, ltr_exp y x); rewrite exE ltxx; case: ltrgtP.
Qed.

End exp.

Section Ln.

Variable R : realType.

Notation exp := (@exp R).

Definition ln x : R := xget 0 [set y | exp y == x ].

Lemma expK : cancel exp ln.
Proof.
by move=> x; rewrite /ln; case: xgetP => [x1 _ /eqP/expI //|/(_ x)[]/=].
Qed.

Lemma exp_total_gt1 x :
  1 <= x -> exists y, [/\ 0 <= y, 1 + y <= x & exp y = x].
Proof.
move=> x_ge1; have x_ge0 : 0 <= x by apply: le_trans x_ge1.
case: (@IVT _ (fun y => exp y - x) 0 x 0) => //.
- move=> x1 x1Ix; apply: continuousB => // y1.
    by apply: continuous_exp.
  by apply: continuous_cst.
rewrite exp0; case: (ltrgtP (1- x) (exp x - x)) => [_||].
- rewrite subr_le0 x_ge1 subr_ge0.
  by apply: le_trans (exp_ge1Dx _); rewrite ?ler_addr.
- by rewrite ltr_add2r exp_lt1 ltNge x_ge0.
- rewrite subr_le0 x_ge1 => -> /=; rewrite subr_ge0.
  by apply: le_trans (exp_ge1Dx x_ge0); rewrite ler_addr.
move=> x1 _ /eqP; rewrite subr_eq0 => /eqP Hx1.
exists x1; split => //; first by rewrite -ler_exp exp0 Hx1.
by rewrite -Hx1 exp_ge1Dx // -ler_exp Hx1 exp0.
Qed.

Lemma exp_total x :  0 < x -> exists y, exp y = x.
Proof.
case: (lerP 1 x) => [/exp_total_gt1[y [_ _ Hy]]|x_lt1 x_gt0].
  by exists y.
have /exp_total_gt1[y [H1y H2y H3y]] : 1 <= x^-1 by rewrite ltW // !invf_cp1.
by exists (-y); rewrite expN H3y invrK.
Qed.

Lemma lnK x : 0 < x -> exp (ln x) = x.
Proof.
move=> x_gt0; rewrite /ln; case: xgetP=> [x1 _ /eqP// |H].
by case: (exp_total x_gt0) => y /eqP Hy; case: (H y).
Qed.

Lemma lnK_eq x : (exp (ln x) == x) = (0 < x).
Proof.
apply/eqP/idP=> [<-|]; last by apply: lnK.
by apply: exp_gt0.
Qed.

Lemma ln1 : ln 1 = 0.
Proof. by apply/expI; rewrite lnK // exp0. Qed.

Lemma lnM x y : 0 < x -> 0 < y -> ln (x * y) = ln x + ln y.
Proof.
by move=> x_gt0 y_gt0; apply: expI; rewrite ?expD !lnK // mulr_gt0.
Qed.

Lemma lnI x y : 0 < x -> 0 < y -> ln x = ln y -> x = y.
Proof. by move=> /lnK {2}<- /lnK {2}<- ->. Qed.

Lemma lnV x : 0 < x -> ln (x^-1) = - ln x.
Proof.
move=> x_gt0; have xVP : 0 < x^-1 by rewrite invr_gt0.
by apply: expI; rewrite lnK // expN lnK.
Qed.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof. by move=> x_gt0 y_gt0; rewrite lnM  ?invr_gt0 // lnV. Qed.

Lemma ltr_ln : {in Num.pos &, {mono ln : x y / x < y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ltr_exp !lnK. Qed.

Lemma ler_ln : {in Num.pos &, {mono ln : x y / x <= y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ler_exp !lnK. Qed.

Lemma lnX n x : 0 < x -> ln(x ^+ n) = ln x *+ n.
Proof.
move=> x_gt0; elim: n => [|n IH] /=; first by rewrite expr0 ln1 mulr0n.
by rewrite !exprS lnM ?exprn_gt0 // -add1n mulrnDr mulr1n IH.
Qed.

Lemma ln_le1Dx x : 0 <= x -> ln (1 + x) <= x.
Proof.
move=> x_ge0; rewrite -ler_exp lnK ?exp_ge1Dx //.
by apply: lt_le_trans (_ : 0 < 1) _; rewrite // ler_addl.
Qed.
Search (_ < exp.exp _).

Lemma ln_sublinear x : 0 < x -> ln x < x.
Proof.
move=> x_gt0; apply: lt_le_trans (_ : ln (1 + x) <= _).
  by rewrite -ltr_exp !lnK ?addr_gt0 // ltr_addr.
by rewrite -ler_exp lnK ?addr_gt0 // exp_ge1Dx // ltW.
Qed.

Lemma ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
by move=> x_ge1; rewrite -ler_exp exp0 lnK // (lt_le_trans _ x_ge1).
Qed.

Lemma ln_gt0 x : 1 < x -> 0 < ln x.
Proof.
by move=> x_gt1; rewrite -ltr_exp exp0 lnK // (lt_trans _ x_gt1).
Qed.

End Ln.

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

Lemma sinE : sin = fun x =>
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
Grab Existential Variables. all: end_near. Qed.

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

Lemma cosE : cos = fun x =>
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
Grab Existential Variables. all: end_near. Qed.

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
  rewrite is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  apply/funext => i.
  by rewrite diffs_sin diffs_cos sin_coeffE {1}[in RHS]/-%R /= !mulNr.
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Lemma derivable_sin x : derivable sin x 1.
Proof. by apply: ex_derive; apply: is_derive_sin. Qed.

Lemma continuous_sin : continuous sin.
Proof.
move=> x.
apply: differentiable_continuous.
by apply/derivable1_diffP/derivable_sin.
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
    rewrite is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  apply/funext => i.
  by rewrite /s1 diffs_cos sin_coeffE {1}[in RHS]/-%R /= mulNr.
apply: (@termdiff _ _ (`|x| + 1)).
- by rewrite -cos_coeffE; apply: is_cvg_series_cos_coeff.
- rewrite (_ : (fun n : nat => _) = - sin_coeff (`|x| + 1)).
    rewrite is_cvg_seriesN.
    by apply: is_cvg_series_sin_coeff.
  by apply/funext => i; rewrite diffs_cos sin_coeffE {1}[in RHS]/-%R /= mulNr.
- rewrite (_ : (fun n : nat => _) = - cos_coeff (`|x| + 1)).
  rewrite is_cvg_seriesN.
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

Lemma derivable_cos x : derivable cos x 1.
Proof. by apply: ex_derive; apply: is_derive_cos. Qed.

Lemma continuous_cos : continuous cos.
Proof.
move=> x.
apply: differentiable_continuous.
by apply/derivable1_diffP/derivable_cos.
Qed.

Lemma cos2Dsin2 a : (cos a) ^+ 2 + (sin a) ^+ 2 = 1.
Proof.
pose f := cos ^+2 + sin^+2; rewrite -[LHS]/(f a).
apply: etrans (_ : f 0 = 1); last first.
  by rewrite /f; rcfE; rewrite sin0 cos0 mul1r mul0r addr0.
apply: is_derive_0_cst => {}x.
apply: trigger_derive; rewrite /GRing.scale /=.
by rewrite ?expr1 mulrN mulrAC addrC subrr.
Qed.

Lemma cos_max a : `| cos a | <= 1.
Proof.
rewrite -(expr_le1 (_ : 0 < 2)%nat) // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite -(cos2Dsin2 a) ler_addl ?sqr_ge0.
Qed.

Lemma cos_geN1 a : -1 <= cos a.
Proof. by rewrite ler_oppl; have /ler_normlP[] := cos_max a. Qed.

Lemma cos_le1 a : cos a <= 1.
Proof. by have /ler_normlP[] := cos_max a. Qed.

Lemma sin_max a : `| sin a | <= 1.
Proof.
rewrite -(expr_le1 (_ : 0 < 2)%nat) // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite -(cos2Dsin2 a) ler_addr ?sqr_ge0.
Qed.

Lemma sin_geN1 a : -1 <= sin a.
Proof. by rewrite ler_oppl; have /ler_normlP[] := sin_max a. Qed.

Lemma sin_le1 a : sin a <= 1.
Proof. by have /ler_normlP[] := sin_max a. Qed.

Fact sinD_aux x y :
  (sin (x + y) - (sin x * cos y + cos x * sin y)) ^+ 2 +
  (cos (x + y) - (cos x * cos y - sin x * sin y)) ^+ 2 = 0.
Proof.
pose f := (sin \o +%R^~ y - (sin * cst (cos y) + cos * cst (sin y)))^+2 +
          (cos \o +%R^~ y - (cos * cst (cos y) - sin * cst (sin y)))^+2.
rewrite -[LHS]/(f x); apply: etrans (_ : f 0 = 0); last first.
  rewrite /f; rcfE.
  by rewrite cos0 sin0 !(mul1r, mul0r, add0r, subr0, subrr).
apply: is_derive_0_cst => {}x.
apply: trigger_derive.
by rcfE; rewrite !(scaler0, add0r, addr0, mulr1, expr1) mulr2n; nsatz.
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
    (sin (- x ) + sin x) ^+ 2 + (cos (- x) - cos x) ^+ 2 = 0.
Proof.
pose f := (sin \o -%R + sin)^+2 + (cos \o -%R - cos )^+2.
apply: etrans (_ : f x = 0); first by [].
apply: etrans (_ : f 0 = 0); last first.
  by rewrite /f ; rcfE;
     rewrite oppr0 cos0 sin0 !(mul1r, mul0r, add0r, subr0, subrr).
apply: is_derive_0_cst => {}x.
apply: trigger_derive.
  by apply: is_deriveD; apply: is_deriveX;
     apply: is_deriveD; apply: is_derive1_chain; apply: is_deriveN.
rcfE; rewrite !(scaler0, add0r, addr0, mulr1, expr1) mulr2n; nsatz.
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

Lemma norm_cos_eq1 a : (`|cos a| == 1) = (sin a == 0).
Proof.
rewrite -sqrf_eq0 -sqrp_eq1 // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite [X in _ = (X == _)]sin2cos2 subr_eq0 eq_sym.
Qed.

Lemma norm_sin_eq1 a : (`|sin a| == 1) = (cos a == 0).
Proof.
rewrite -sqrf_eq0 -sqrp_eq1 // -normrX ger0_norm ?exprn_even_ge0 //.
by rewrite [X in _ = (X == _)]cos2sin2 subr_eq0 eq_sym.
Qed.

Lemma cos1sin0 a : `|cos a| = 1 -> sin a = 0.
Proof. by move/eqP; rewrite norm_cos_eq1 => /eqP. Qed.

Lemma sin1cos0 a : `|sin a| = 1 -> cos a = 0.
Proof. by move/eqP; rewrite norm_sin_eq1 => /eqP. Qed.

Lemma sin0cos1 a : sin a = 0 -> `|cos a| = 1.
Proof. by move/eqP; rewrite -norm_cos_eq1 => /eqP. Qed.

Lemma cos_norm a : cos `|a| = cos a.
Proof. by case: (ler0P a); rewrite ?cosN. Qed.

End CosSin.

Section Pi.
Variable R : realType.

Definition pi : R := get [set x | 0 <= x <= 2 /\ cos x = 0] *+ 2.

Lemma cos_coeff_odd n (x : R) : cos_coeff x n.*2.+1 = 0.
Proof. by rewrite /cos_coeff /= odd_double /= !mul0r. Qed.

Lemma cos_coeff_2_0 : cos_coeff 2 0%N = 1 :> R.
Proof. by rewrite /cos_coeff /= mul1r expr0 mulr1 expr0z divff. Qed.

Lemma cos_coeff_2_2 : cos_coeff 2 2%N = - 2%:R :> R.
Proof.
by rewrite /cos_coeff /= mul1r expr1z mulN1r expr2 mulNr -mulrA divff// mulr1.
Qed.

Lemma cos_coeff_2_4 : cos_coeff 2 4 = 2%:R / 3%:R :> R.
Proof.
rewrite /cos_coeff /= mul1r -exprnP sqrrN expr1n mul1r 2!factS mulnCA mulnC.
by rewrite 3!exprS expr1 2!mulrA natrM -mulf_div -2!natrM divff// mul1r.
Qed.

Lemma SUM_GROUP (f : R ^nat) (n k : nat) :
  \sum_(0 <= i < n) \sum_(i * k <= j < i.+1 * k) f j =
  \sum_(0 <= i < n * k) f i.
Proof.
elim: n => [|n ih]; first by rewrite mul0n 2!big_nil.
rewrite big_nat_recr//= ih mulSn addnC [in RHS]/index_iota subn0 iota_add.
rewrite big_cat /= [in X in X + _ = _]/index_iota subn0; congr (_ + _).
by rewrite /index_iota addnC addnK.
Qed.

Lemma SER_GROUP (f : R ^nat) (k : nat) : cvg (series f) -> (0 < k)%N ->
  series (fun n => \sum_(n * k <= i < n.+1 * k) f i) --> lim (series f).
Proof.
move=> /cvg_ballP cf k0; apply/cvg_ballP => _/posnumP[e].
have := cf _ (posnum_gt0 e); rewrite near_map => -[n _ nl].
rewrite near_map; near=> m.
rewrite /ball /= [in X in `|_ - X|]/series [in X in `|_ - X|]/= SUM_GROUP.
have /nl : (n <= m * k)%N.
  by near: m; exists n.+1 => //= p /ltnW /leq_trans /(_ (leq_pmulr _ k0)).
by rewrite /ball /= distrC.
Grab Existential Variables. all: end_near. Qed.

Lemma SER_PAIR (f : R ^nat) : cvg (series f) ->
 series (fun n => \sum_(n.*2 <= i < n.*2 + 2) f i) --> lim (series f).
Proof.
move=> cf; rewrite [X in series X --> _](_ : _ =
    (fun n => \sum_(n * 2 <= k < n.+1 * 2) f k)); last first.
  by rewrite funeqE => n; rewrite /= addnC -(muln2 n) -mulSn.
exact: SER_GROUP.
Qed.

Definition cos_coeff' (x : R) (n : nat) := (-1)^n * x ^+ n.*2 / n.*2`!%:R.

Lemma cos_coeff'E (x : R) (n : nat) : cos_coeff' x n = cos_coeff x n.*2.
Proof.
rewrite /cos_coeff' /cos_coeff /= odd_double /= mul1r -2!mulrA; congr (_ * _).
by rewrite (half_bit_double n false).
Qed.

Lemma cvg_cos_coeff' (x : R) : series (cos_coeff' x) --> cos x.
Proof.
have /SER_PAIR := (@is_cvg_series_cos_coeff _ x).
apply: cvg_trans.
rewrite [X in _ --> series X](_ : _ = (fun n => cos_coeff x n.*2)); last first.
  rewrite funeqE=> n; rewrite addn2 big_nat_recr //= cos_coeff_odd addr0.
  by rewrite  big_nat_recl//= /index_iota subnn big_nil addr0.
rewrite [X in series X --> _](_ : _ = (fun n => cos_coeff x n.*2)) //.
by rewrite funeqE => n; exact: cos_coeff'E.
Qed.

Lemma SER_POS_LT_PAIR (f : R ^nat) n : cvg (series f) ->
  (forall d, 0 < f (n + d.*2)%N + f (n + d.*2.+1)%N) ->
  \sum_(0 <= i < n) f i < lim (series f).
Proof.
move=> /cvg_ballP cf fn.
have fn0 : 0 < f n + f n.+1 by have := fn 0%N; rewrite double0 addn0 addn1.
rewrite ltNge; apply: contraPN cf => ffn /(_ _ fn0).
rewrite near_map /ball /=.
have nf_ub N : \sum_(0 <= i < n.+2) f i <= \sum_(0 <= i < N.+1.*2 + n) f i.
  elim: N => // N /le_trans ->//; rewrite -(addn1 (N.+1)) doubleD addnAC.
  rewrite [in X in _ <= X]/index_iota subn0 iota_add big_cat.
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

Lemma cos2_lt0 : cos 2 < 0 :> R.
Proof.
rewrite -(opprK (cos _)) oppr_lt0; have /cvgN H := @cvg_cos_coeff' 2.
rewrite -(cvg_lim (@Rhausdorff R) H).
apply: (@lt_trans _ _ (\sum_(0 <= i < 3) - cos_coeff' 2 i)).
  do 3 rewrite big_nat_recl//; rewrite big_nil addr0 3!cos_coeff'E double0.
  rewrite cos_coeff_2_0 cos_coeff_2_2 -muln2 cos_coeff_2_4 addrA -(opprD 1).
  rewrite opprB -(@natrB _ 2 1)// subn1/= -{1}(@divff _ 3%:R)// -mulrBl.
  by rewrite divr_gt0// -natrB.
rewrite -seriesN SER_POS_LT_PAIR //.
  by move/cvgP in H; by rewrite seriesN.
move=> d.
rewrite /cos_coeff' 2!exprzD_nat (exprSz _ d.*2) -[in (-1) ^ d.*2](muln2 d).
rewrite -(exprnP _ (d * 2)) (exprM (-1)) sqrr_sign 2!mulr1 -exprSzr.
rewrite (_ : 4 = 2 * 2)%N // -(exprnP _ (2 * 2)) (exprM (-1)) sqrr_sign.
rewrite mul1r [(-1) ^ 3](_ : _ = -1) ?mulN1r ?mulNr ?opprK; last first.
  by rewrite -exprnP 2!exprS expr1 mulrN1 opprK mulr1.
rewrite subr_gt0.
rewrite addnS doubleS -[X in 2 ^+ X]addn2 exprD -mulrA ltr_pmul2l ?exprn_gt0//.
rewrite factS factS 2!natrM mulrA invfM !mulrA.
rewrite ltr_pdivr_mulr ?ltr0n ?fact_gt0// mulVf ?pnatr_eq0 ?gtn_eqF ?fact_gt0//.
rewrite ltr_pdivr_mulr ?mul1r //.
by rewrite expr2 -!natrM ltr_nat !mulSn !add2n mul0n !addnS.
Qed.

End Pi.
