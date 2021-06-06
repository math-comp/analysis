(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import nsatz_realtype.
Require Import classical_sets posnum topology normedtype landau sequences.
Require Import derive.

(******************************************************************************)
(* Lemmas about exponential/logarithm functions, theory for sin, cos, and tan *)
(*                                                                            *)
(*            ln x == the natural logarithm                                   *)
(*          a `^ x == exponential functions                                   *)
(*      riemannR a == sequence n |-> 1 / (n.+1) ^ a where a has a type of     *)
(*                    type realType                                           *)
(*           sin x == the sine function                                       *)
(*           cos x == the cosine function                                     *)
(*    periodic f T == f is a periodic function of period T                    *)
(* alternating f T == f is a periodic function of period T                    *)
(*              pi == pi                                                      *)
(*           tan x == the tangent function                                    *)
(*                                                                            *)
(* TODO: credit HOL-light (and coq-robot?)                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section AboutCvg.

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

End AboutCvg.

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

Global Instance is_deriveV (f : R -> R) (x t v : R) :
 f x != 0 -> is_derive x v f t ->
 is_derive x v [fun y => (f y)^-1]  (- (f x) ^- 2 *: t).
Proof.
move=> fxNZ Df.
constructor; first by apply: derivableV => //; case: Df.
by rewrite deriveV //; case: Df => _ ->.
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
suff Cc : lim (h^-1 *: (series (shx h - sx))) @[h --> 0^'] --> lim (series s).
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

Section expR.

Variable R : realType.
Implicit Types x : R.

Lemma expR0 : expR 0 = 1 :> R.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. Qed.

Lemma expR_ge1Dx x : 0 <= x -> 1 + x <= expR x.
Proof.
move=> x_gt0; rewrite /expR.
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

Lemma exp_coeffE x :
  exp_coeff x = (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /exp_coeff /= mulrC. Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma expRE :
  expR = fun x => lim (series (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n)).
Proof. by apply/funext => x; rewrite -exp_coeffE. Qed.

Lemma diffs_inv_fact :
  diffs (fun n => (n`!%:R)^-1) = (fun n => (n`!%:R)^-1 : R).
Proof.
by apply/funext => i; rewrite /diffs factS natrM invfM mulrA mulfV ?mul1r.
Qed.

Global Instance is_derive_expR x : is_derive x 1 expR (expR x).
Proof.
pose s1 n := diffs (fun n => n`!%:R^-1) n * x ^+ n.
rewrite expRE /=.
rewrite (_ : (fun n => _) = s1); last first.
  by apply/funext => i; rewrite /s1 diffs_inv_fact.
apply: (@termdiff _ _ (`|x| + 1)).
- rewrite -exp_coeffE; apply: is_cvg_series_exp_coeff.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite diffs_inv_fact exp_coeffE.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite !diffs_inv_fact exp_coeffE.
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Lemma derivable_expR x : derivable expR x 1.
Proof. by apply: ex_derive; apply: is_derive_exp. Qed.

Lemma continuous_expR : continuous (@expR R).
Proof.
move=> x.
apply: differentiable_continuous.
by apply/derivable1_diffP/derivable_expR.
Qed.

Lemma expRxDyMexpx x y : expR (x + y) * expR (- x) = expR y.
Proof.
apply: etrans (_ : expR (0 + y) * expR (- 0) = _); last first.
  by rewrite add0r oppr0 expR0 mulr1.
apply: (@is_derive_0_cst _ (fun x => expR (x + y) * expR (- x))) => x1.
have -> : 0 = expR (x1 + y) * (expR (- x1) * (- 1)) +
              expR (- x1) * (expR (x1 + y) * (1 + 0)).
  by rewrite mulrN1 addr0 mulr1 mulrN addrC mulrC subrr.
apply: is_deriveM.
apply: is_derive1_chain.
apply: is_deriveN.
Qed.

Lemma expRxMexpNx_1 x : expR x * expR (- x) = 1.
Proof. by rewrite -{1}[x]addr0 expRxDyMexpx expR0. Qed.

Lemma pexpR_gt1 x: 0 < x -> 1 < expR x.
Proof.
move=> x_gt0.
apply: lt_le_trans (expR_ge1Dx (ltW x_gt0)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.

Lemma expR_gt0 x : 0 < expR x.
Proof.
case: (ltrgt0P x) => [x_gt0|x_gt0|->].
- by apply: lt_trans (pexpR_gt1 x_gt0).
- have F : 0 < expR (- x) by apply: lt_trans (pexpR_gt1 _); rewrite ?oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expRxMexpNx_1.
by rewrite expR0.
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
by rewrite exprS -add1n natrD mulrDl mul1r expRD IH.
Qed.

Lemma expR_gt1 x:  (1 < expR x) = (0 < x).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite expR0.
- by rewrite (pexpR_gt1 x_gt0).
apply/idP/negP.
rewrite -[x]opprK expRN -leNgt invf_cp1 ?expR_gt0 //.
by rewrite ltW // pexpR_gt1 // lter_oppE.
Qed.

Lemma expR_lt1 x:  (expR x < 1) = (x < 0).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite expR0 //.
- by apply/idP/negP; rewrite -leNgt ltW // expR_gt1.
by rewrite -[x]opprK expRN invf_cp1 ?expR_gt0 // expR_gt1 lter_oppE.
Qed.

Lemma expRB x y : expR (x - y) = expR x / expR y.
Proof. by rewrite expRD expRN. Qed.

Lemma ltr_expR : {mono (@expR R) : x y / x < y}.
Proof.
move=> x y.
by rewrite -{1}(subrK x y) expRD ltr_pmull ?expR_gt0 // expR_gt1 subr_gt0.
Qed.

Lemma ler_expR : {mono (@expR R) : x y / x <= y}.
Proof.
move=> x y.
case: (ltrgtP x y) => [xLy|yLx|<-].
- by rewrite ltW // ltr_expR.
- by rewrite leNgt ltr_expR yLx.
by rewrite lexx.
Qed.

Lemma expRI : injective (@expR R).
Proof.
move=> x y exE.
by have [] := (ltr_expR x y, ltr_expR y x); rewrite exE ltxx; case: ltrgtP.
Qed.

Lemma expR_total_gt1 x :
  1 <= x -> exists y, [/\ 0 <= y, 1 + y <= x & expR y = x].
Proof.
move=> x_ge1; have x_ge0 : 0 <= x by apply: le_trans x_ge1.
case: (@IVT _ (fun y => expR y - x) 0 x 0) => //.
- by move=> x1 x1Ix; apply: continuousB => // y1;
    [exact: continuous_expR|exact: cst_continuous].
- rewrite expR0; case: (ltrgtP (1- x) (expR x - x)) => [_| |].
  + rewrite subr_le0 x_ge1 subr_ge0.
    by apply: le_trans (expR_ge1Dx _); rewrite ?ler_addr.
  + by rewrite ltr_add2r expR_lt1 ltNge x_ge0.
  + rewrite subr_le0 x_ge1 => -> /=; rewrite subr_ge0.
    by apply: le_trans (expR_ge1Dx x_ge0); rewrite ler_addr.
- move=> x1 _ /eqP; rewrite subr_eq0 => /eqP Hx1.
  exists x1; split => //; first by rewrite -ler_expR expR0 Hx1.
  by rewrite -Hx1 expR_ge1Dx // -ler_expR Hx1 expR0.
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
by move=> x; rewrite /ln; case: xgetP => [x1 _ /eqP/expRI //|/(_ x)[]/=].
Qed.

Lemma lnK x : 0 < x -> exp (ln x) = x.
Proof.
move=> x_gt0; rewrite /ln; case: xgetP=> [x1 _ /eqP// |H].
by case: (expR_total x_gt0) => y /eqP Hy; case: (H y).
Qed.

Lemma lnK_eq x : (exp (ln x) == x) = (0 < x).
Proof. by apply/eqP/idP=> [<-|]; [exact: expR_gt0|exact: lnK]. Qed.

Lemma ln1 : ln 1 = 0.
Proof. by apply/expRI; rewrite lnK // expR0. Qed.

Lemma lnM x y : 0 < x -> 0 < y -> ln (x * y) = ln x + ln y.
Proof.
by move=> x_gt0 y_gt0; apply: expRI; rewrite ?expRD !lnK // mulr_gt0.
Qed.

Lemma lnI x y : 0 < x -> 0 < y -> ln x = ln y -> x = y.
Proof. by move=> /lnK {2}<- /lnK {2}<- ->. Qed.

Lemma lnV x : 0 < x -> ln (x^-1) = - ln x.
Proof.
move=> x_gt0; have xVP : 0 < x^-1 by rewrite invr_gt0.
by apply: expRI; rewrite lnK // expRN lnK.
Qed.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof. by move=> x_gt0 y_gt0; rewrite lnM  ?invr_gt0 // lnV. Qed.

Lemma ltr_ln : {in Num.pos &, {mono ln : x y / x < y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ltr_expR !lnK. Qed.

Lemma ler_ln : {in Num.pos &, {mono ln : x y / x <= y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ler_expR !lnK. Qed.

Lemma lnX n x : 0 < x -> ln(x ^+ n) = ln x *+ n.
Proof.
move=> x_gt0; elim: n => [|n IH] /=; first by rewrite expr0 ln1 mulr0n.
by rewrite !exprS lnM ?exprn_gt0 // -add1n mulrnDr mulr1n IH.
Qed.

Lemma ln_le1Dx x : 0 <= x -> ln (1 + x) <= x.
Proof.
move=> x_ge0; rewrite -ler_expR lnK ?expR_ge1Dx //.
by apply: lt_le_trans (_ : 0 < 1) _; rewrite // ler_addl.
Qed.

Lemma ln_sublinear x : 0 < x -> ln x < x.
Proof.
move=> x_gt0; apply: lt_le_trans (_ : ln (1 + x) <= _).
  by rewrite -ltr_expR !lnK ?addr_gt0 // ltr_addr.
by rewrite -ler_expR lnK ?addr_gt0 // expR_ge1Dx // ltW.
Qed.

Lemma ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
by move=> x_ge1; rewrite -ler_expR expR0 lnK // (lt_le_trans _ x_ge1).
Qed.

Lemma ln_gt0 x : 1 < x -> 0 < ln x.
Proof.
by move=> x_gt1; rewrite -ltr_expR expR0 lnK // (lt_trans _ x_gt1).
Qed.

End Ln.

Section ExpFun.
Variable R : realType.
Implicit Types a x : R.

Definition exp_fun a x := expR (x * ln a).

Local Notation "a `^ x" := (exp_fun a x).

Lemma exp_fun_gt0 a x : 0 < a `^ x. Proof. by rewrite expR_gt0. Qed.

Lemma exp_funa1 a : 0 < a -> a `^ 1 = a.
Proof. by move=> a0; rewrite /exp_fun mul1r lnK. Qed.

Lemma exp_fun1 : exp_fun 1 = fun=> 1.
Proof. by rewrite funeqE => x; rewrite /exp_fun ln1 mulr0 expR0. Qed.

Lemma ler_exp_fun a : 1 < a -> {homo exp_fun a : x y / x <= y}.
Proof. by move=> a1 x y xy; rewrite /exp_fun ler_expR ler_pmul2r // ln_gt0. Qed.

Lemma exp_funD a : 0 < a -> {morph exp_fun a : x y / x + y >-> x * y}.
Proof. by move=> a0 x y; rewrite {1}/exp_fun mulrDl expRD. Qed.

Lemma exp_funa0 a : 0 < a -> a `^ 0 = 1.
Proof. by move=> a0; rewrite /exp_fun mul0r expR0. Qed.

Lemma exp_fun_inv a : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -{1}(exp_funa1 a0) -exp_funD // subrr exp_funa0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma exp_fun_mulrn a n : 0 < a -> exp_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 exp_funa0.
by rewrite -addn1 natrD exp_funD // exprD ih exp_funa1.
Qed.

End ExpFun.
Notation "a `^ x" := (exp_fun a x).

Lemma dvg_harmonic (R : numFieldType) : ~ cvg (@series [zmodType of R^o] harmonic).
Admitted. (* NB(rei): this is in master, we just need to rebase *)

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
  by rewrite funeqE => i /=; rewrite exp_funa1.
have : forall n, harmonic n <= riemannR a n.
  case=> /= [|n]; first by rewrite exp_fun1 invr1.
  rewrite -[X in _ <= X]div1r ler_pdivl_mulr ?exp_fun_gt0 // mulrC.
  rewrite ler_pdivr_mulr // mul1r -[X in _ <= X]exp_funa1 //.
  by rewrite (ler_exp_fun) // ?ltr1n // ltW.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemannR_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemannR_series.

Section CosSin.

Variable R : realType.
Implicit Types x : R.

Definition sin_coeff x :=
   [sequence  (odd n)%:R * (-1) ^+ n.-1./2 * x ^+ n / n`!%:R]_n.

Lemma sin_coeffE x :
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

Definition sin x : R := lim (series (sin_coeff x)).

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

Definition cos_coeff x :=
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

Definition cos x : R := lim (series (cos_coeff x)).

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

Lemma cos_mulr2n a : cos (a *+ 2) = cos a ^+2 *+ 2 - 1.
Proof. by rewrite mulr2n cosD -!expr2 sin2cos2 opprB addrA mulr2n. Qed.

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
Arguments sin {R}.
Arguments cos {R}.

Lemma SUM_GROUP (R : zmodType) (f : R ^nat) (n k : nat) :
  \sum_(0 <= i < n) \sum_(i * k <= j < i.+1 * k) f j =
  \sum_(0 <= i < n * k) f i.
Proof.
elim: n => [|n ih]; first by rewrite mul0n 2!big_nil.
rewrite big_nat_recr//= ih mulSn addnC [in RHS]/index_iota subn0 iota_add.
rewrite big_cat /= [in X in X + _ = _]/index_iota subn0; congr (_ + _).
by rewrite /index_iota addnC addnK.
Qed.

Lemma SER_GROUP (R : realFieldType) (f : R ^nat) k : cvg (series f) -> (0 < k)%N ->
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

Lemma SER_PAIR (R : realFieldType) (f : R ^nat) : cvg (series f) ->
 series (fun n => \sum_(n.*2 <= i < n.*2 + 2) f i) --> lim (series f).
Proof.
move=> cf; rewrite [X in series X --> _](_ : _ =
    (fun n => \sum_(n * 2 <= k < n.+1 * 2) f k)); last first.
  by rewrite funeqE => n; rewrite /= addnC -(muln2 n) -mulSn.
exact: SER_GROUP.
Qed.

Lemma SER_POS_LT_PAIR (R : realFieldType) (f : R ^nat) n : cvg (series f) ->
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

Section periodic.
Variables U V : zmodType.
Implicit Type f : U -> V.

Definition periodic f (T : U) := forall u, f (u + T) = f u.

Lemma periodicn f (T : U) : periodic f T -> forall n a, f (a + T *+ n) = f a.
Proof.
move=> fT; elim => [a|n ih a]; first by rewrite mulr0n addr0.
by rewrite mulrS addrA ih fT.
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

Section Pi.
Variable R : realType.
Implicit Types (x y : R) (n k : nat).

Definition pi : R := get [set x | 0 <= x <= 2 /\ cos x = 0] *+ 2.

Lemma pihalfE : pi / 2 = get [set x | 0 <= x <= 2 /\ cos x = 0].
Proof. by rewrite /pi -(mulr_natr (get _)) -mulrA divff ?mulr1. Qed.

(* TODO: move closer to cos? *)
Lemma cos_coeff_odd n x : cos_coeff x n.*2.+1 = 0.
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

Definition cos_coeff' x n := (-1)^n * x ^+ n.*2 / n.*2`!%:R.

Lemma cos_coeff'E x n : cos_coeff' x n = cos_coeff x n.*2.
Proof.
rewrite /cos_coeff' /cos_coeff /= odd_double /= mul1r -2!mulrA; congr (_ * _).
by rewrite (half_bit_double n false).
Qed.

Lemma cvg_cos_coeff' x : series (cos_coeff' x) --> cos x.
Proof.
have /SER_PAIR := (@is_cvg_series_cos_coeff _ x).
apply: cvg_trans.
rewrite [X in _ --> series X](_ : _ = (fun n => cos_coeff x n.*2)); last first.
  rewrite funeqE=> n; rewrite addn2 big_nat_recr //= cos_coeff_odd addr0.
  by rewrite  big_nat_recl//= /index_iota subnn big_nil addr0.
rewrite [X in series X --> _](_ : _ = (fun n => cos_coeff x n.*2)) //.
by rewrite funeqE => n; exact: cos_coeff'E.
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

Lemma cos_exists : exists2 pih : R, 0 <= pih <= 2 & cos pih = 0.
Proof.
have /IVT[]// : minr (cos 0) (cos 2) <= (0 : R) <= maxr (cos 0) (cos 2).
  rewrite /minr /maxr cos0 !ifN;
      try  by rewrite -leNgt ltW // (lt_trans cos2_lt0).
  by rewrite (ler_nat R 0 1) andbT ?ltW // cos2_lt0 //.
by move=> *; apply: continuous_cos.
by move=> pih /itvP pihI chpi_eq0; exists pih; rewrite ?pihI.
Qed.

(* TODO: move closed to sin? *)
Definition sin_coeff' x n := (-1)^n * x ^+ n.*2.+1 / n.*2.+1`!%:R.

Lemma sin_coeff'E x n : sin_coeff' x n = sin_coeff x n.*2.+1.
Proof.
rewrite /sin_coeff' /sin_coeff /= odd_double mul1r -2!mulrA; congr (_ * _).
by rewrite doubleK.
Qed.

Lemma sin_coeff_even n x : sin_coeff x n.*2 = 0.
Proof. by rewrite /sin_coeff /= odd_double /= !mul0r. Qed.

Lemma cvg_sin_coeff' x : series (sin_coeff' x) --> sin x.
Proof.
have /SER_PAIR := (@is_cvg_series_sin_coeff _ x).
apply: cvg_trans.
rewrite [X in _ --> series X](_ : _ = (fun n => sin_coeff x n.*2.+1)); last first.
  rewrite funeqE=> n; rewrite addn2 big_nat_recl //= sin_coeff_even add0r.
  by rewrite  big_nat_recl // big_geq // addr0.
rewrite [X in series X --> _](_ : _ = (fun n => sin_coeff x n.*2.+1)) //.
by rewrite funeqE => n; exact: sin_coeff'E.
Qed.

Lemma sin2_gt0 x : 0 < x < 2 -> 0 < sin x.
Proof.
move=> /andP[x_gt0 x_lt2].
have H := @cvg_sin_coeff' x.
rewrite -(cvg_lim (@Rhausdorff R) H).
rewrite [X in X < _](_ : 0 = \sum_(0 <= i < 0) sin_coeff' x i :> R); last first.
  by rewrite big_nil.
rewrite SER_POS_LT_PAIR //; first by move/cvgP in H.
move=> d.
rewrite /sin_coeff' 2!exprzD_nat (exprSz _ d.*2) -[in (-1) ^ d.*2](muln2 d).
rewrite -(exprnP _ (d * 2)) (exprM (-1)) sqrr_sign 2!mulr1 -exprSzr.
rewrite !add0n!mul1r mulN1r -[d.*2.+1]addn1 doubleD -addSn exprD.
rewrite -(ffact_fact (leq_addl _ _)) addnK.
rewrite mulNr -!mulrA -mulrBr mulr_gt0 ?exprn_gt0 //.
rewrite natrM invfM -{1}[_^-1]mul1r !mulrA -mulrBl divr_gt0 //; last first.
  by rewrite (ltr_nat _ 0) fact_gt0.
rewrite subr_gt0.
rewrite -{2}(divff (_ : ((d.*2.*2.+1 + 1.*2) ^_ 1.*2)%:R != 0)); last first.
  by rewrite lt0r_neq0 // (ltr_nat _ 0) ffact_gt0 leq_addl.
rewrite ltr_pmul2r; last by rewrite invr_gt0 (ltr_nat _ 0) ffact_gt0 leq_addl.
rewrite !addnS addn0 !ffactnS ffactn0 muln1 /= natrM.
by rewrite (ltr_pmul (ltW _ ) (ltW _)) // (lt_le_trans x_lt2) // ler_nat.
Qed.

Lemma cos_pihalf_uniq x y :
  0 <= x <= 2 -> cos x = 0 -> 0 <= y <= 2 -> cos y = 0 -> x = y.
Proof.
wlog xLy : x y / x <= y => [H xB cx0 yB cy0|].
  by case: (lerP x y) => [/H //| /ltW /H H1]; [exact|exact/esym/H1].
move=> /andP[x_ge0 x_le2] cx0 /andP[y_ge0 y_le2] cy0.
case: (x =P y) => // /eqP xDy.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
have /(Rolle xLLs)[x1 _|x1 _|x1 x1I [_ x1D]] : cos x = cos y by rewrite cy0.
- by apply: derivable_cos.
- by apply: continuous_cos.
have [_ /esym/eqP] := is_derive_cos x1; rewrite x1D oppr_eq0 => /eqP Hs.
suff : 0 < sin x1 by rewrite Hs ltxx.
apply/sin2_gt0/andP; split.
- by apply: le_lt_trans x_ge0 _; rewrite (itvP x1I).
- by apply: lt_le_trans _ y_le2; rewrite (itvP x1I).
Qed.

Local Lemma cos_pihalf' : 0 <= pi / 2 <= 2 /\ cos (pi / 2) = 0.
Proof.
have [x ? ?] := cos_exists; rewrite pihalfE.
by case: xgetP => [_->[]//|/(_ x)/=]; last tauto.
Qed.

Lemma pihalf_02 : 0 < pi / 2 < 2.
Proof.
have [pih02 cpih] := cos_pihalf'.
rewrite 2!lt_neqAle andbCA -andbA pih02 andbT; apply/andP; split.
  by apply/eqP => pih2; have := cos2_lt0; rewrite -pih2 cpih ltxx.
apply/eqP => pih0; have := @cos0 R.
by rewrite pih0 cpih; apply/eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma pi_gt0 : 0 < pi.
Proof.
by rewrite -[pi](divfK (_ : 2 != 0)) // mulr_gt0 //; case/andP: pihalf_02.
Qed.

Lemma sin_gt0_halfpi x : 0 < x < pi / 2 -> 0 < sin x.
Proof.
move=> /andP[x_gt0 xLpi].
apply: sin2_gt0; rewrite x_gt0 /=.
by apply: lt_trans xLpi _; have /andP[] := pihalf_02.
Qed.

Lemma cos_gt0_halfpi x : -(pi /2) < x < pi / 2 -> 0 < cos x.
Proof.
wlog : x / 0 <= x => [Hw|x_ge0].
  case: (leP 0 x) => [/Hw//| x_lt_0].
  rewrite -{-1}[x]opprK ltr_oppl andbC [-- _ < _]ltr_oppl cosN.
  by apply: Hw => //; rewrite oppr_cp0 ltW.
have /andP[pi2_gt0 pi2L2] := pihalf_02.
move=> /andP[x_gt0 xLpi2]; case: (ler0P (cos x)) => // cx_le0.
have /IVT[]// : minr (cos 0) (cos x) <= 0 <= maxr (cos 0) (cos x).
  by rewrite cos0 /minr /maxr !ifN ?cx_le0 //= -leNgt (le_trans cx_le0).
- by move=> *; apply: continuous_cos.
move=> x1 /itvP Hx1 cx1_eq0.
suff x1E : x1 = pi/2.
  have : x1 < pi / 2 by apply: le_lt_trans xLpi2; rewrite Hx1.
  by rewrite x1E ltxx.
apply: cos_pihalf_uniq=> //; last by (case cos_pihalf' => _ ->).
  by rewrite Hx1 ltW // (lt_trans _ pi2L2) // (le_lt_trans _ xLpi2) // Hx1.
by rewrite !ltW.
Qed.

Lemma cos_pihalf : cos (pi / 2) = 0. Proof. exact: cos_pihalf'.2. Qed.

Lemma sin_pihalf : sin (pi / 2) = 1.
Proof.
have := cos2Dsin2 (pi / 2); rewrite cos_pihalf expr0n add0r.
rewrite -[in X in _ = X -> _](expr1n _ 2%N) => /eqP; rewrite -subr_eq0 subr_sqr.
rewrite mulf_eq0=> /orP[|]; first by rewrite subr_eq0=> /eqP.
move/eqP/absurd; apply; apply/eqP; rewrite addr_eq0 -eqr_oppLR.
apply/eqP => Nspi21.
have := @ler01 R; rewrite -{}Nspi21 ler_oppr oppr0 leNgt => /negP; apply.
exact/sin2_gt0/pihalf_02.
Qed.

Lemma cos_ge0_halfpi x : -(pi /2) <= x <= pi / 2 -> 0 <= cos x.
Proof.
rewrite le_eqVlt; case: (_ =P x) => /= [<-|_].
  by rewrite cosN cos_pihalf.
rewrite le_eqVlt; case: (x =P _) => /= [->|_ H]; first by rewrite cos_pihalf.
by rewrite ltW //; apply: cos_gt0_halfpi.
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
move=> xI; rewrite -cosBpihalf cos_ge0_halfpi //.
by rewrite ler_subr_addl subrr ler_sub_addr -mulr2n -[_ *+ 2]mulr_natr divfK.
Qed.

Lemma sin_gt0_pi x : 0 < x < pi -> 0 < sin x.
Proof.
move=> xI; rewrite -cosBpihalf cos_gt0_halfpi //.
by rewrite ltr_subr_addl subrr ltr_sub_addr -mulr2n -[_ *+ 2]mulr_natr divfK.
Qed.

Lemma cosI x y :
  0 <= x <= pi -> 0 <= y <= pi -> cos x = cos y -> x = y.
Proof.
wlog xLy : x y / x <= y => [H xB yB cE|].
  by case: (lerP x y) => [/H //| /ltW /H H1]; [exact|exact/esym/H1].
move=> /andP[x_ge0 x_lepi] /andP[y_ge0 y_lepi] cxE.
case: (x =P y) => // /eqP xDy.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
have /Rolle[|x1 x1I|x1 x1I|x1 /itvP x1I [_ /eqP]] // := cxE.
  by apply: continuous_cos.
have [_ /esym<-] := is_derive_cos x1.
rewrite oppr_eq0 => /eqP Hs.
suff : 0 < sin x1 by rewrite Hs ltxx.
apply: sin_gt0_pi => //.
rewrite (le_lt_trans x_ge0) ?x1I //.
rewrite (lt_le_trans _ y_lepi) ?x1I //.
Qed.

Lemma sinI x y :
  -(pi/2) <= x <= pi/2 -> -(pi/2) <= y <= pi/2 -> sin x = sin y -> x = y.
Proof.
move=> xB yB sinE.
have : - sin x = - sin y by rewrite sinE.
rewrite -!cosDpihalf => {}sinE.
by apply/(addIr (pi/2))/cosI => //;
   rewrite -{1}[pi/2]opprK subr_ge0 -{3}[pi](divfK (_ : 2 != 0)) // 
           mulr_natr [(pi/2) *+ 2]mulr2n ler_add2r.
Qed.

(* Maybe this should be stated with mono *)
Lemma cos_nmono x y : 0 <= x <= pi -> 0 <= y <= pi -> (cos y < cos x) = (x < y).
Proof.
(* There should be a better proof *)
rewrite le_eqVlt; case: eqP => [<- _|_] /=.
  rewrite cos0 le_eqVlt; case: eqP => /= [<- _|_ /andP[y_gt0 gLpi]].
    by rewrite cos0 !ltxx.
  rewrite y_gt0; apply/idP.
  suff : cos y != 1 by case: ltrgtP (cos_le1 y).
  rewrite -cos0 eq_sym; apply/eqP => /Rolle [||x1 _|x1 /itvP x1I [_ x1D]] //.
    by apply: continuous_cos.
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
  rewrite -cospi; apply/eqP => /Rolle [||x1 _|x1 /itvP x1I [_ x1D]] //.
    by apply: continuous_cos.
  case: (is_derive_cos x1) => _ /eqP; rewrite x1D eq_sym oppr_eq0 => /eqP s_eq0.
  suff : 0 < sin x1 by rewrite s_eq0 ltxx.
  by apply: sin_gt0_pi; rewrite x1I /= (lt_le_trans (_ : _ < x)) ?x1I.
wlog xLy : x y x_gt0 x_ltpi y_gt0 y_ltpi / x <= y => [H | ].
  case: (lerP x y) => [/H //->//|yLx].
  by rewrite !ltNge ltW ?(ltW yLx) // H // ltW.
case: (x =P y) => [->| /eqP xDy]; first by rewrite ltxx.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
rewrite xLLs -subr_gt0 -opprB; rewrite -subr_gt0 in xLLs; apply/idP.
have [x1 _|z /itvP zI ->] := @MVT _ cos (-sin) _ _ xLy.
  by apply: continuous_cos.
rewrite -mulNr opprK mulr_gt0 //; apply: sin_gt0_pi.
by rewrite (lt_le_trans x_gt0) ?zI //= (le_lt_trans _ y_ltpi) ?zI.
Qed.

Lemma sin_mono x y : 
 -(pi/2) <= x <= pi/2 -> -(pi/2) <= y <= pi/2 -> (sin x < sin y) = (x < y).
Proof.
move=> xB yB; rewrite -[sin x]opprK ltr_oppl.
rewrite -!cosDpihalf -[x < y](ltr_add2r (pi /2)).
by apply: cos_nmono;
   rewrite -{1}[pi /2]opprK subr_ge0 -{3}[pi](divfK (_ : 2 != 0)) // 
           mulr_natr [_/_ *+ 2]mulr2n ler_add2r.
Qed.
  
End Pi.

Section Tan.

Variable R : realType.
Notation pi := (@pi R).

Definition tan (a : R) := sin a / cos a.

Lemma tan0 : tan 0 = 0 :> R.
Proof. by rewrite /tan sin0 cos0 mul0r. Qed.

Lemma tanpi : tan pi = 0.
Proof. by rewrite /tan sinpi mul0r. Qed.

Lemma tanN x : tan (- x) = - tan x.
Proof. by rewrite /tan sinN cosN mulNr. Qed.

Lemma tanD x y :
  cos x != 0 -> cos y != 0 ->
  tan(x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
move=> cxNZ cyNZ.
rewrite /tan sinD  cosD !addf_div // [sin y * cos x]mulrC -!mulrA -invfM.
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
rewrite !mulr2n exprMn exprVn -{2}(divff (_ : 1 != 0)) //.
rewrite -mulNr !addf_div ?sqrf_eq0 //.
rewrite mul1r mulr1 -!mulrA -invfM -expr2; congr (_ / _).
  by rewrite [cos x * _]mulrC.
rewrite mulrCA mulrA mulfK  ?sqrf_eq0 // [X in _ = _ - X]sin2cos2.
by rewrite opprB addrA.
Qed.

Lemma divr_eq (x y z t : R):
  y != 0 -> t != 0 -> (x / y == z / t) = (x * t == z * y).
Proof.
move=> yD0 tD0.
rewrite -{2}[x](divfK yD0) -{2}[z](divfK tD0) mulrAC.
apply/eqP/eqP=> [->//|H].
by apply/(mulIf tD0)/(mulIf yD0).
Qed.

(*
Lemma tanI x y :
  - (pi / 2) < x < pi / 2 -> - (pi / 2) < y < pi / 2 -> tan x = tan y -> x = y.
Proof.
move=> xB yB tanE.
have sE : sin (x - y) = 0.
  apply/eqP; rewrite sinB subr_eq0 [_ * sin y]mulrC -divr_eq //.
  - by rewrite [X in X == _]tanE.
  - by rewrite lt0r_neq0 // cos_gt0_halfpi.
  by rewrite lt0r_neq0 // cos_gt0_halfpi.

apply/eqP; rewrite -subr_eq0; apply/eqP/sinI.
  admit.
  admit.
by rewrite sin0.
  rewrite sin_
rewrite /tan.
Search (_ / _ == _ / _).
wlog xLy : x y / x <= y => [H xB yB cE|].
  by case: (lerP x y) => [/H //| /ltW /H H1]; [exact|exact/esym/H1].
move=> /andP[x_ge0 x_lepi] /andP[y_ge0 y_lepi] cxE.
case: (x =P y) => // /eqP xDy.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
*)

Lemma cos2_tan2 x : cos x != 0 -> 1 / (cos x) ^+ 2 = 1 + (tan x) ^+ 2.
Proof.
move=> cosx.
rewrite /tan exprMn [X in _ = 1 + X * _]sin2cos2 mulrBl -exprMn divff //.
by rewrite expr1n addrCA subrr addr0 div1r mul1r exprVn.
Qed.

Lemma tan_halfpi : tan (pi / 2) = 0.
Proof. by rewrite /tan cos_pihalf invr0 mulr0. Qed.

Lemma tan_quaterpi : tan (pi / 4%:R) = 1.
Proof.
rewrite /tan -cosBpihalf -mulNr addf_div // mulNr -mulrBr.
rewrite -opprB -natrB //= !(mulrN, mulNr) cosN invfM [_/2]mulrC mulrA mulfK //.
rewrite divff // lt0r_neq0 // -cos_pihalf.
have pi_gt0 := pi_gt0 R.
rewrite cos_nmono ?lter_pdivr_mulr ?divr_ge0 ?ltW ?pi_gt0 //.
- by rewrite -{1}[pi](divfK (_ : 2 != 0)) // ltr_pmul2l ?ltr_nat // divr_gt0.
- by rewrite -{1}[pi]mulr1 ltr_pmul2l ?(ltr_nat _ 1).
by rewrite  mulr_natr mulr2n ltr_addr.
Qed.

Lemma tanDpi x : tan (x + pi) = tan x.
Proof. by rewrite /tan cosDpi sinDpi mulNr invrN mulrN opprK. Qed.

Lemma continuous_tan x : cos x != 0 -> {for x, continuous tan}.
Proof.
move=> cxNZ.
apply: continuousM; first by apply: continuous_sin.
apply: continuousV => //.
by apply: continuous_cos.
Qed.

Global Instance is_derive_tan x :
  cos x != 0 -> is_derive x 1 tan ((cos x)^-2).
Proof.
move=> cxNZ.
apply: trigger_derive; first by apply: is_deriveM; apply: is_deriveV.
rewrite /= ![_ *: - _]mulrN mulNr mulrN opprK [_^-1 *: _]mulVf //.
rewrite mulrCA -expr2 [X in _ * X + _ = _]sin2cos2.
by rewrite mulrBr mulr1 mulVf ?sqrf_eq0 // subrK.
Qed.

Lemma derivable_tan x : cos x != 0 -> derivable tan x 1.
Proof. by move=> /is_derive_tan[]. Qed.

(* Maybe this should be stated with mono *)
Lemma tan_mono x y : 
  -(pi /2) < x < pi/2 -> -(pi /2) < y < pi/2 -> (tan x < tan y) = (x < y).
Proof.
wlog xLy : x y / x <= y => [H xB yB|xB yB].
  case: (lerP x y) => [/H //->//|yLx].
  by rewrite !ltNge ltW ?(ltW yLx) // H // ltW.
case: (x =P y) => [->| /eqP xDy]; first by rewrite ltxx.
have xLLs : x < y by rewrite le_eqVlt (negPf xDy) in xLy.
rewrite -subr_gt0 xLLs; rewrite -subr_gt0 in xLLs; apply/idP.
have [x1 /itvP x1I|z /itvP zI|] := @MVT _ tan (fun x => (cos x) ^-2) _ _ xLy.
- apply: is_derive_tan.
  rewrite lt0r_neq0 // cos_gt0_halfpi //.
  rewrite (lt_le_trans (_ : _ < x)); last by rewrite x1I.
    by rewrite (lt_le_trans (_ : _ < y)) // ?x1I // ltW; case/andP: yB.
  by case/andP: xB.
- apply: continuous_tan.
  rewrite lt0r_neq0 // cos_gt0_halfpi //.
  rewrite (lt_le_trans (_ : _ < x)); last by rewrite zI.
    by rewrite (le_lt_trans (_ : _ <= y)) // ?zI //; case/andP: yB.
  by case/andP: xB.
move=> x1 /itvP x1I ->.
rewrite  mulr_gt0 // invr_gt0 // exprn_gte0 // cos_gt0_halfpi //.
rewrite (lt_le_trans (_ : _ < x)); last by rewrite x1I.
  by rewrite (le_lt_trans (_ : _ <= y)) // ?x1I //; case/andP: yB.
by case/andP: xB.
Qed.

Lemma tanI x y : 
  -(pi /2) < x < pi/2 -> -(pi /2) < y < pi/2 -> tan x = tan y -> x = y.
Proof.
move=> xB yB tanE.
by case: (ltrgtP x y); rewrite // -tan_mono ?tanE ?ltxx.
Qed.

End Tan.
Arguments tan {R}.

Section Acos.

Variable R : realType.
Local Notation pi := (@pi R).

Definition acos (x : R) := get [set y | 0 <= y <= pi /\ cos y = x].

Lemma acos_def x : 
  -1 <= x <= 1 -> 0 <= acos x <= pi /\ cos (acos x) = x.
Proof.
move=> xB; rewrite /acos; case: xgetP => //= He.
pose f y := cos y - x. 
have /IVT[] // :  minr (f 0) (f pi) <= 0 <= maxr (f 0) (f pi).
  rewrite /f cos0 cospi /minr /maxr ltr_add2r (_ : 1 < -1 = false) .
    by rewrite subr_le0 subr_ge0.
  by rewrite -subr_lt0 opprK -mulr2n (ltr_nat _ 2  0).
- by apply/ltW/pi_gt0.
- move=> *; apply: continuousB => //.
    by apply: continuous_cos.
  by apply: continuous_cst.
rewrite /f => x1 /itvP x1I /eqP; rewrite subr_eq0 => /eqP cosx1E.
by case: (He x1); rewrite !x1I.
Qed.

Lemma acos_ge0 x : -1 <= x <= 1 -> 0 <= acos x.
Proof. by move=> /acos_def[/andP[]]. Qed.

Lemma acos_lepi x : -1 <= x <= 1 -> acos x <= pi.
Proof. by move=> /acos_def[/andP[]]. Qed.

Lemma acosK x : -1 <= x <= 1 -> cos(acos x) = x.
Proof. by move=> /acos_def[/andP[]]. Qed.

Lemma acos_gt0 x : -1 <= x < 1 -> 0 < acos x.
Proof.
move=> /andP[x_geN1 x_lt1]; move: (x_lt1).
have : 0 <= acos x by rewrite acos_ge0 // x_geN1 ltW.
have : cos(acos x) = x by rewrite acosK // x_geN1 ltW.
by case: ltrgt0P => // ->; rewrite cos0 => ->; rewrite ltxx.
Qed.

Lemma acos_ltpi x : -1 < x <= 1 -> acos x < pi.
Proof.
move=> /andP[x_gtN1 x_le1]; move: (x_gtN1).
have : acos x <= pi by rewrite acos_lepi // x_le1 ltW.
have : cos(acos x) = x by rewrite acosK // x_le1 ltW.
by case: (ltrgtP (acos x) pi) => // ->; rewrite cospi => ->; rewrite ltxx.
Qed.

Lemma cosK x : 0 <= x <= pi -> acos (cos x) = x.
Proof.
move=> xB; apply: cosI => //.
  by rewrite acos_ge0 ?acos_lepi ?cos_geN1 ?cos_le1.
by rewrite acosK // cos_geN1 cos_le1.
Qed.

Lemma sin_acos x : -1 <= x <= 1 -> sin (acos x) = Num.sqrt (1 - x^+2).
Proof.
move=> xB.
rewrite -[LHS]ger0_norm; last by rewrite sin_ge0_pi // acos_ge0 ?acos_lepi.
by rewrite -sqrtr_sqr sin2cos2 acosK.
Qed.

End Acos.

Section Asin.

Variable R : realType.
Notation pi := (@pi R).

Definition asin (x : R) := get [set y | -(pi / 2) <= y <= pi / 2 /\ sin y = x].

Lemma asin_def x : 
  -1 <= x <= 1 -> -(pi / 2) <= asin x <= pi / 2 /\ sin (asin x) = x.
Proof.
move=> xB; rewrite /asin; case: xgetP => //= He.
pose f y := sin y - x. 
have /IVT[] // :
    minr (f (-(pi/2))) (f (pi/2)) <= 0 <= maxr (f (-(pi/2))) (f (pi/2)).
  rewrite /f sinN sin_pihalf /minr /maxr ltr_add2r (_ : -1 < 1 = true) .
    by rewrite subr_le0 subr_ge0.
  by rewrite -subr_gt0 opprK -mulr2n (ltr_nat _ 0).
- by rewrite -subr_ge0 opprK addr_ge0 // divr_ge0 // ltW // pi_gt0.
- move=> *; apply: continuousB => //.
    by apply: continuous_sin.
  by apply: continuous_cst.
rewrite /f => x1 /itvP x1I /eqP; rewrite subr_eq0 => /eqP sinx1E.
by case: (He x1); rewrite !x1I.
Qed.

Lemma asin_geNpi2 x : -1 <= x <= 1 -> -(pi/2) <= asin x.
Proof. by move=> /asin_def[/andP[]]. Qed.

Lemma asin_lepi2 x : -1 <= x <= 1 -> asin x <= pi / 2.
Proof. by move=> /asin_def[/andP[]]. Qed.

Lemma asinK x : -1 <= x <= 1 -> sin (asin x) = x.
Proof. by move=> /asin_def[/andP[]]. Qed.

Lemma asin_gtpi x : -1 <= x < 1 -> asin x < pi/2.
Proof.
move=> /andP[x_geN1 x_lt1]; move: (x_lt1).
have : asin x <= pi / 2 by rewrite asin_lepi2 // x_geN1 ltW.
have : sin (asin x) = x by rewrite asinK // x_geN1 ltW.
case: (ltrgtP _ ((pi / 2))) => // ->.
by rewrite sin_pihalf => <-; rewrite ltxx.
Qed.

Lemma asin_gtNpi2 x : -1 < x <= 1 -> - (pi / 2) < asin x.
Proof.
move=> /andP[x_gtN1 x_le1]; move: (x_gtN1).
have : - (pi / 2) <= asin x by rewrite asin_geNpi2 // x_le1 ltW.
have : sin (asin x) = x by rewrite asinK // x_le1 ltW.
by case: (ltrgtP (asin x)) => // ->; 
   rewrite sinN sin_pihalf => <-; rewrite ltxx.
Qed.

Lemma sinK x : - (pi / 2) <= x <= pi / 2 -> asin (sin x) = x.
Proof.
move=> xB; apply: sinI => //.
  by rewrite asin_geNpi2 ?asin_lepi2 ?sin_geN1 ?sin_le1.
by rewrite asinK // sin_geN1 sin_le1.
Qed.

Lemma cos_asin x : -1 <= x <= 1 -> cos (asin x) = Num.sqrt (1 - x^+2).
Proof.
move=> xB.
rewrite -[LHS]ger0_norm; last first.
  by apply: cos_ge0_halfpi; rewrite asin_lepi2 // asin_geNpi2.
by rewrite -sqrtr_sqr cos2sin2 asinK.
Qed.

End Asin.

(*
let atn = new_definition
  `atn(y) = @x. --(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)`;;
*)

Section Atan.

Variable R : realType.
Notation pi := (@pi R).

Definition atan (x : R) :=
  get [set y | -(pi / 2) < y < pi / 2 /\ tan y = x].

Lemma sqrtrV (x : R) : 0 <= x -> Num.sqrt (x^-1) = (Num.sqrt x)^-1.
Proof.
move=> x_ge0.
case: (x =P 0) => [->|/eqP xD0]; first by rewrite invr0 sqrtr0 invr0.
rewrite -[LHS]mul1r -(mulVf (_ : Num.sqrt x != 0)); last first.
  by rewrite sqrtr_eq0 -ltNge; case: ltrgt0P x_ge0 xD0.
by rewrite -mulrA -sqrtrM // divff // sqrtr1 mulr1.
Qed.

Lemma sin_sg (x y : R) : sin(Num.sg x * y) = Num.sg x * sin y.
Proof. by case: sgrP; rewrite ?mul1r ?mulN1r ?sinN // !mul0r sin0. Qed.

Lemma cos_sg (x y : R) : x != 0 -> cos(Num.sg x * y) = cos y.
Proof. by case: sgrP; rewrite ?mul1r ?mulN1r ?cosN. Qed.

(* Did not see how to use ITV like in the other *)
Lemma atan_def x : -(pi / 2) < atan x < pi / 2 /\ tan (atan x) = x.
Proof.
rewrite /atan; case: xgetP => //= He.
pose x1 := Num.sqrt (1 + x^+ 2) ^-1.
have ox2_gt0 : 0 < 1 + x^2.
  by apply: lt_le_trans (_ : 1 <= _); rewrite ?ler_addl ?sqr_ge0.
have ox2_ge0 : 0 <= 1 + x^2 by rewrite ltW.
have x1B : -1 <= x1 <= 1.
  rewrite -ler_norml /x1 ger0_norm ?sqrtr_ge0 //.
  rewrite -[X in _ <= X]sqrtr1 ler_psqrt ?qualifE ?invr_gte0 //=.
  by rewrite invf_cp1 // ler_addl sqr_ge0.
case: (He (Num.sg x * acos x1)); split; last first.
  case: (x =P 0) => [->|/eqP xD0]; first by rewrite /tan sgr0 mul0r sin0 mul0r.
  rewrite /tan sin_sg cos_sg // acosK ?sin_acos //.
  rewrite /x1 sqr_sqrtr ?invr_ge0 //.
  rewrite -{1}[_^-1]mul1r -{1}[1](divff (_: 1 != 0)) //.
  rewrite -mulNr addf_div ?lt0r_neq0 //. 
  rewrite mul1r mulr1 {1}[1 + _]addrC addrK // sqrtrM ?sqr_ge0 //.
  rewrite sqrtrV // invrK // mulrA divfK //; last by rewrite sqrtr_eq0 -ltNge.
  by rewrite sqrtr_sqr mulr_sg_norm.
rewrite -ltr_norml normrM.
have pi2 : 0 < pi / 2 by rewrite divr_gt0 // pi_gt0.
case: (x =P 0) => [->|/eqP xD0]; first by rewrite sgr0 normr0 mul0r.
rewrite normr_sg xD0 mul1r ltr_norml.
rewrite (lt_le_trans (_ : _ < 0)) ?acos_ge0 ?oppr_cp0 //=.
rewrite -cos_nmono ?(acos_ge0, acos_lepi) //; last first.
   by rewrite ltW //= ler_pdivr_mulr // mulr2n mulrDr mulr1 
              ler_addr ltW // pi_gt0.
by rewrite cos_pihalf acosK // ?sqrtr_gt0 ?invr_gt0.
Qed.

Lemma atan_gtNpi2 x : - (pi / 2) < atan x.
Proof. by case: (atan_def x) => [] /andP[]. Qed.

Lemma atan_ltpi2 x : atan x < pi / 2.
Proof. by case: (atan_def x) => [] /andP[]. Qed.

Lemma atanK x : tan (atan x) = x.
Proof. by case: (atan_def x). Qed.

Lemma tanK x : - (pi / 2) < x < pi / 2 -> atan (tan x) = x.
Proof.
move=> xB; apply: tanI => //.
  by rewrite !(atan_gtNpi2, atan_ltpi2).
by rewrite atanK.
Qed.

End Atan.

(*

From mathcomp Require Import complex.

Section expC.
Variable R : realType.
Local Open Scope complex_scope.
Implicit Types n : nat.

Lemma demoivre n (a : R) :
 (cos a +i* sin a) ^+ n = cos (a *+ n) +i* sin (a *+ n).
Proof.
elim: n => [|n ih]; first by rewrite expr0 mulr0n cos0 sin0.
by rewrite exprS ih mulrS cosD sinD; simpc; rewrite [in X in _ +i* X = _]addrC.
Qed.

End expC.

*)