(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import poly sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau differential
  derivative.

(**md**************************************************************************)
(* # Lemmas about directional derivatives                                     *)
(*                                                                            *)
(* This file provides lemmas about directional derivatives. It includes       *)
(* standard theorems (the Extreme Value Theorem, Rolle's theorem, the Mean    *)
(* Value Theorem, etc.).                                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DeriveRU.
Context {d} {R : numFieldType} {U : normedModType d R}.
Implicit Types f : R -> U.

Lemma derivable_within_continuous f (i : interval R) :
  {in i, forall x, derivable f x 1} -> {within [set` i], continuous f}.
Proof.
move=> di; apply/continuous_in_subspaceT => z /[1!inE] zA.
apply/differentiable_continuous; rewrite -derivable1_diffP.
by apply: di; rewrite inE.
Qed.

End DeriveRU.

Section DeriveVW.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.
Implicit Types f : V -> W.

Lemma derivableP f x v : derivable f x v -> is_derive x v f ('D_v f x).
Proof. by move=> df; apply: DeriveDef. Qed.

Global Instance is_derive_cst (a : W) (x v : V) : is_derive x v (cst a) 0.
Proof.
apply: DeriveDef; last by rewrite deriveE // diff_val.
exact/diff_derivable.
Qed.

Lemma derivable_cst (w : W) (x v : V) : derivable (cst w) x v.
Proof. exact/diff_derivable. Qed.

Lemma is_derive_eq f (x v : V) (df f' : W) :
  is_derive x v f f' -> f' = df -> is_derive x v f df.
Proof. by move=> ? <-. Qed.

End DeriveVW.
Arguments derivable_cst {d R V d' W}.

Section Derive_lemmasVW.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.
Implicit Types f g : V -> W.

Fact der_add f g (x v : V) : derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f + g) \o shift x) (h *: v) - (f + g) x)) @
  0^'  --> 'D_v f x + 'D_v g x.
Proof.
move=> df dg.
under [X in X @ _]eq_fun.
  move=> /= h.
  rewrite !scalerDr scalerN scalerDr opprD addrACA -!scalerBr.
  over.
exact: cvgD.
Qed.

Lemma deriveD f g (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f + g) x = 'D_v f x + 'D_v g x.
Proof. by move=> df dg; apply: cvg_lim (der_add df dg). Qed.

Lemma derivableD f g (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f + g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (derive f x v + derive g x v).
exact: der_add.
Qed.

Global Instance is_deriveD f g (x v : V) (df dg : W) :
  is_derive x v f df -> is_derive x v g dg -> is_derive x v (f + g) (df + dg).
Proof.
move=> dfx dgx; apply: DeriveDef; first exact: derivableD.
by rewrite deriveD // !derive_val.
Qed.

Global Instance is_derive_sum n (h : 'I_n -> V -> W) (x v : V)
  (dh : 'I_n -> W) : (forall i, is_derive x v (h i) (dh i)) ->
  is_derive x v (\sum_(i < n) h i) (\sum_(i < n) dh i).
Proof.
by elim/big_ind2 : _ => // [|] *; [exact: is_derive_cst|exact: is_deriveD].
Qed.

Lemma derivable_sum n (h : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (h i) x v) -> derivable (\sum_(i < n) h i) x v.
Proof.
move=> df; suff : forall i, is_derive x v (h i) ('D_v (h i) x) by [].
by move=> ?; apply: derivableP.
Qed.

Lemma derive_sum n (h : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (h i) x v) ->
  'D_v (\sum_(i < n) h i) x = \sum_(i < n) 'D_v (h i) x.
Proof.
move=> df; suff dfx : forall i, is_derive x v (h i) ('D_v (h i) x).
  by rewrite derive_val.
by move=> ?; apply: derivableP.
Qed.

Fact der_opp f (x v : V) : derivable f x v ->
  (fun h => h^-1 *: (((- f) \o shift x) (h *: v) - (- f) x)) @
  0^' --> - 'D_v f x.
Proof.
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=.
  by rewrite funeqE => h; rewrite !scalerDr !scalerN -opprD -scalerBr /g.
exact: cvgN.
Qed.

Lemma deriveN f (x v : V) : derivable f x v -> 'D_v (- f) x = - 'D_v f x.
Proof. by move=> df; apply: cvg_lim (der_opp df). Qed.

Lemma derivableN f (x v : V) :
  derivable f x v -> derivable (- f) x v.
Proof. by move=> df; apply/cvg_ex; exists (- 'D_v f x); apply: der_opp. Qed.

Global Instance is_deriveN f (x v : V) (df : W) :
  is_derive x v f df -> is_derive x v (- f) (- df).
Proof.
move=> dfx; apply: DeriveDef; first exact: derivableN.
by rewrite deriveN // derive_val.
Qed.

Global Instance is_deriveB f g (x v : V) (df dg : W) :
  is_derive x v f df -> is_derive x v g dg -> is_derive x v (f - g) (df - dg).
Proof. by move=> ??; apply: is_derive_eq. Qed.

Lemma deriveB f g (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f - g) x = 'D_v f x - 'D_v g x.
Proof. by move=> /derivableP df /derivableP dg; rewrite derive_val. Qed.

Lemma derivableB f g (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f - g) x v.
Proof. by move=> /derivableP df /derivableP dg. Qed.

Fact der_scal f (k : R) (x v : V) : derivable f x v ->
  (fun h => h^-1 *: ((k \*: f \o shift x) (h *: v) - (k \*: f) x)) @
  0^' --> k *: 'D_v f x.
Proof.
move=> df; evar (h : R -> W); rewrite [X in X @ _](_ : _ = h) /=.
  rewrite funeqE => r.
  by rewrite scalerBr !scalerA mulrC -!scalerA -!scalerBr /h.
exact: cvgZl_tmp.
Qed.

Lemma deriveZ f (k : R) (x v : V) : derivable f x v ->
  'D_v (k \*: f) x = k *: 'D_v f x.
Proof. by move=> df; apply: cvg_lim (der_scal df). Qed.

Lemma derivableZ f (k : R) (x v : V) :
  derivable f x v -> derivable (k \*: f) x v.
Proof.
by move=> df; apply/cvg_ex; exists (k *: 'D_v f x); apply: der_scal.
Qed.

Global Instance is_deriveZ f (k : R) (x v : V) (df : W) :
  is_derive x v f df -> is_derive x v (k \*: f) (k *: df).
Proof.
move=> dfx; apply: DeriveDef; first exact: derivableZ.
by rewrite deriveZ // derive_val.
Qed.

Lemma derive_cst (k : W) (x v : V) : 'D_v (cst k) x = 0.
Proof. by rewrite derive_val. Qed.

End Derive_lemmasVW.

Section Derive_LR.
Context {d} {R : numFieldType} {V : normedModType d R}.
Implicit Types (k : R -> R) (f : R -> V) (x : R).

Lemma der1_scaleLR k f x : derivable k x 1 -> derivable f x 1 ->
  h^-1 *: (((fun x0 => k x0 *: f x0) \o  shift x) h%:A - k x *: f x)
  @[h --> 0^'] --> 'D_1 k x *: f x + k x *: 'D_1 f x.
Proof.
move=> der_k der_f/=; rewrite (@near_eq_cvg_eq _ _ _ _ _
    (fun h => (h^-1 * (k (h%:A + x) - k x)) *: f (h%:A + x) +
              k x *: (h^-1 *: (f (h%:A + x) - f x)))).
  near=> h.
  rewrite scalerA (mulrC (k x)) -(scalerA h^-1 (k x)) -scalerA -scalerDr.
  by congr (_ *: _); rewrite scalerBl scalerBr addrA subrK.
apply: cvgD.
- apply/(cvgZ der_k)/(@cvg_comp _ _ _ _ _ _ (nbhs x)).
  + apply: cvg0D => //;  apply: (@cvg0M _ _ _ _ _ _ 1) => //.
    exact: cvg_within_filter.
  + rewrite -/(continuous_at x f).
    exact/differentiable_continuous/derivable1_diffP.
- exact: cvgZl_tmp der_f.
Unshelve. all: by end_near. Qed.

Global Instance is_derive1ZLR k f x (dk : R) (df : V) :
  is_derive x 1 k dk -> is_derive x 1 f df ->
  is_derive x 1 (fun x => k x *: f x) (dk *: f x + k x *: df).
Proof.
move=> [der_k <-] [der_f <-]/=; apply: DeriveDef.
- exact: cvgP (der1_scaleLR _ _).
- by apply: norm_cvg_lim; exact: cvg_trans (der1_scaleLR _ _).
Qed.

Lemma deriveZLR k f x : derivable k x 1 -> derivable f x 1 ->
  'D_1 (fun x => k x *: f x) x = 'D_1 k x *: f x + k x *: 'D_1 f x.
Proof. by move=> dk df; exact/derive_val/is_derive1ZLR. Qed.

Lemma derivableZLR k f x : derivable k x 1 -> derivable f x 1 ->
  derivable (fun x => k x *: f x) x 1.
Proof. by move=> dk df; exact/ex_derive/is_derive1ZLR; apply: derivableP. Qed.

End Derive_LR.

Section derive_id.
Context {d} {R : numFieldType} {V : normedModType d R}.

Lemma derivable_id (x v : V) : derivable id x v.
Proof. exact/diff_derivable. Qed.

Global Instance is_derive_id (x v : V) : is_derive x v id v.
Proof.
apply: (DeriveDef (@derivable_id _ _)).
rewrite deriveE// (@diff_lin _ _ _ _ _ idfun)//=.
by rewrite /continuous_at.
Qed.

Global Instance is_deriveNid (x v : V) : is_derive x v -%R (- v).
Proof. exact: is_deriveN. Qed.

Lemma derive_id (x v : V) : 'D_v id x = v.
Proof. by have /derivableP := @derivable_id x v; rewrite derive_val. Qed.

End derive_id.

Lemma derive1_onem {R : numFieldType} :
  (fun x => x.~ : R^o)^`()%classic = cst (-1).
Proof.
by apply/funext => x; rewrite derive1E deriveB// derive_id derive_cst sub0r.
Qed.

Section Derive_lemmasVR.
Context {d} {R : numFieldType} {V : normedModType d R}.
Implicit Types (f g : V -> R) (x v : V).

Fact der_mult f g x v :
  derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f * g) \o shift x) (h *: v) - (f * g) x)) @
  0^' --> f x *: 'D_v g x + g x *: 'D_v f x.
Proof.
move=> df dg.
evar (fg : R -> R); rewrite [X in X @ _](_ : _ = fg) /=.
  rewrite funeqE => h.
  have -> : (f * g) (h *: v + x) - (f * g) x =
    f (h *: v + x) *: (g (h *: v + x) - g x) + g x *: (f (h *: v + x) - f x).
    by rewrite !scalerBr -addrA ![g x *: _]mulrC addKr.
  rewrite scalerDr scalerA mulrC -scalerA.
  by rewrite [_ *: (g x *: _)]scalerA mulrC -scalerA /fg.
apply: cvgD; last exact: cvgZl_tmp df.
apply: cvg_comp2 (@scale_continuous _ _ _ (_, _)) => /=; last exact: dg.
suff : {for 0, continuous (fun h : R => f(h *: v + x))}.
  by move=> /continuous_withinNx; rewrite scale0r add0r.
exact/differentiable_continuous/derivable1_diffP/(derivable1P _ _ _).1.
Qed.

Lemma deriveM f g x v : derivable f x v -> derivable g x v ->
  'D_v (f * g) x = f x *: 'D_v g x + g x *: 'D_v f x.
Proof. by move=> df dg; apply: cvg_lim (der_mult df dg). Qed.

Lemma derivableM f g x v :
  derivable f x v -> derivable g x v -> derivable (f * g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (f x *: 'D_v g x + g x *: 'D_v f x).
exact: der_mult.
Qed.

Lemma deriveMr f (r : R) x v :
  derivable f x v -> 'D_v (r \o* f) x = r * 'D_v f x.
Proof.
move/deriveM => /(_ _ (derivable_cst _ _ _)) ->.
by rewrite derive_cst scaler0 add0r.
Qed.

Lemma deriveMl f (r : R) x v :
  derivable f x v -> 'D_v (r \*o f) x = r * 'D_v f x.
Proof. by move=> fxv; rewrite -deriveMr// mul_funC. Qed.

Global Instance is_deriveM f g x v (df dg : R) :
  is_derive x v f df -> is_derive x v g dg ->
  is_derive x v (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx; apply: DeriveDef; first exact: derivableM.
by rewrite deriveM // !derive_val.
Qed.

Global Instance is_deriveX f n x v (df : R) :
  is_derive x v f df -> is_derive x v (f ^+ n) ((n%:R * f x ^+ n.-1) *: df).
Proof.
case: n => [fdf|n dfx].
  by rewrite expr0 mul0r scale0r; exact: is_derive_cst.
elim: n => [|n ihn]; first by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_derive_eq.
rewrite scalerA -scalerDl mulrCA -[f x * _]exprS.
by rewrite [in LHS]mulr_natl exprfctE -mulrSr mulr_natl.
Qed.

Lemma derivableX f n x v : derivable f x v -> derivable (f ^+ n) x v.
Proof. by case: n => [_|n /derivableP]; [rewrite expr0|]. Qed.

Lemma deriveX f n x v : derivable f x v ->
  'D_v (f ^+ n) x = (n%:R * f x ^+ n.-1) *: 'D_v f x.
Proof. by move=> /derivableP df; rewrite derive_val. Qed.

Fact der_inv f x v : f x != 0 -> derivable f x v ->
  (fun h => h^-1 *: (((fun y => (f y)^-1) \o shift x) (h *: v) - (f x)^-1)) @
  0^' --> - (f x) ^-2 *: 'D_v f x.
Proof.
move=> fxn0 df.
have /derivable1P/derivable1_diffP/differentiable_continuous := df.
move=> /continuous_withinNx; rewrite scale0r add0r => fc.
have fn0 : 0^' [set h | f (h *: v + x) != 0].
  apply: (fc [set x | x != 0]); exists `|f x|; first by rewrite /= normr_gt0.
  move=> y; rewrite /= => yltfx.
  by apply/eqP => y0; move: yltfx; rewrite y0 subr0 ltxx.
have : (fun h => - ((f x)^-1 * (f (h *: v + x))^-1) *:
  (h^-1 *: (f (h *: v + x) - f x))) @ 0^' -->
  - (f x) ^- 2 *: 'D_v f x.
  by apply: cvgM => //; apply: cvgN; rewrite expr2 invfM; apply: cvgM => //;
     exact: cvgV.
apply: cvg_trans => A [_/posnumP[e] /= Ae].
move: fn0; apply: filter_app; near=> h => /= fhvxn0.
have he : ball 0 e%:num (h : R) by near: h; exists e%:num => /=.
have hn0 : h != 0 by near: h; exists e%:num => /=.
suff <- :
  - ((f x)^-1 * (f (h *: v + x))^-1) *: (h^-1 *: (f (h *: v + x) - f x)) =
  h^-1 *: ((f (h *: v + x))^-1 - (f x)^-1) by exact: Ae.
rewrite scalerA mulrC -scalerA; congr (_ *: _).
apply/eqP; rewrite scaleNr eqr_oppLR opprB scalerBr.
rewrite -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
by rewrite mulrC -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
Unshelve. all: by end_near. Qed.

Lemma deriveV f x v : f x != 0 -> derivable f x v ->
  'D_v (fun y => (f y)^-1) x = - (f x) ^- 2 *: 'D_v f x.
Proof. by move=> fxn0 df; apply: cvg_lim (der_inv fxn0 df). Qed.

Lemma derivableV f x v :
  f x != 0 -> derivable f x v -> derivable (fun y => (f y)^-1) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (- (f x) ^- 2 *: 'D_v f x).
exact: der_inv.
Qed.

Lemma is_deriveV f x v (df : R) :
  f x != 0 -> is_derive x v f df ->
  is_derive x v (fun y => (f y)^-1) (- (f x) ^- 2 *: df).
Proof.
move=> fxNZ Df; apply: DeriveDef; first exact: derivableV.
by rewrite deriveV//; case: Df => _ ->.
Qed.

End Derive_lemmasVR.

#[global] Hint Extern 0 (is_derive _ _ (fun _ => (_ _)^-1) _) =>
  (apply: is_deriveV; first by []) : typeclass_instances.

Lemma derive_shift {d} {R : numFieldType} {V : normedModType d R} (v k : V) :
  'D_v (shift k : V -> V) = cst v.
Proof.
by apply/funext => x/=; rewrite deriveD// derive_id derive_cst addr0.
Qed.

Lemma derive1_shift {R : numFieldType} (k : R) : (shift k)^`() = cst 1.
Proof. by rewrite -(derive_shift _ k); apply/funext => x; rewrite derive1E. Qed.

Lemma is_derive_shift {d} {R : numFieldType} {V : normedModType d R}
  x (v k : V) :
  is_derive x v (shift k) v.
Proof. by apply: DeriveDef => //; rewrite derive_val addr0. Qed.

Section derive_comp_shift.
Context {d} {R : numFieldType} {V : normedModType d R} (f : R -> V).
Implicit Types x a v : R.

Lemma derive_comp_shift x a v : 'D_v (f \o shift a) x = 'D_v f (x + a).
Proof. by rewrite /derive/=; under [in RHS]eq_fun do rewrite addrA. Qed.

Lemma derive1_comp_shift x a : (f \o shift a)^`() x = f^`() (x + a).
Proof. by rewrite 2!derive1E derive_comp_shift. Qed.

Lemma derivable_comp_shift x a v :
  derivable f (x + a) v -> derivable (f \o shift a) x v.
Proof. by rewrite {1}/derivable/=; under eq_is_cvg do rewrite addrA. Qed.

Lemma is_derive_comp_shift x a (df : V) :
  is_derive (x + a) 1 f df -> is_derive x 1 (f \o shift a) df.
Proof.
by move=> [/derivable_comp_shift derf] <-; split => //; rewrite derive_comp_shift.
Qed.

End derive_comp_shift.

Lemma derive1_cst {d} {R : numFieldType} (V : normedModType d R) (k : V) t :
  (cst k)^`() t = 0.
Proof. by rewrite derive1E derive_cst. Qed.

Lemma derive1Mr {R : numFieldType} (f : R -> R) (x r : R) :
  derivable f x 1 ->
  (fun x => f x * r)^`()%classic x = f^`()%classic x * r.
Proof. by move=> ?; rewrite derive1E deriveMr ?derive1E 1?mulrC. Qed.

Lemma derive1Ml {R : numFieldType} (f : R -> R) (x r : R) :
  derivable f x 1 ->
  (fun x => r * f x)^`()%classic x = r * f^`()%classic x :> R.
Proof. by move=> ?; rewrite derive1E deriveMl ?derive1E. Qed.

Lemma exprn_derivable {R : numFieldType} n (x : R) v :
  derivable (@GRing.exp R ^~ n) x v.
Proof.
elim: n => [/=|n ih]; first by rewrite (_ : _ ^~ _ = 1).
rewrite (_ : _ ^~ _ = (fun x => x * x ^+ n)).
  by apply/funext => y; rewrite exprS.
by apply: derivableM; first exact: derivable_id.
Qed.

Lemma exp_derive {R : numFieldType} n x v :
  'D_v (@GRing.exp R ^~ n) x = n%:R *: x ^+ n.-1 *: v.
Proof.
have /= := @deriveX _ R R id n x v (@derivable_id _ _ _ _ _).
by rewrite fctE => ->; rewrite derive_id.
Qed.

Global Instance is_derive_exp (R : numFieldType) n x v :
  is_derive x v (@GRing.exp R ^~ n) (n%:R *: x ^+ n.-1 *: v).
Proof. by constructor; [exact: exprn_derivable|exact: exp_derive]. Qed.

Lemma exp_derive1 {R : numFieldType} n x :
  (@GRing.exp R ^~ n)^`() x = n%:R *: x ^+ n.-1.
Proof. by rewrite derive1E exp_derive [LHS]mulr1. Qed.

Lemma compact_EVT_max {d} {T : topologicalType d} {R : realType} (f : T -> R)
    (A : set T) :
  A !=set0 -> compact A -> {within A, continuous f} ->
  exists2 c, c \in A & forall t, t \in A -> f t <= f c.
Proof.
move=> A0 cA cf.
have sup_fA : has_sup (f @` A).
  by apply/compact_has_sup; [exact: image_nonempty A0|exact/continuous_compact].
have [|imf_ltsup] := pselect (exists2 c, c \in A & f c = sup (f @` A)).
  move=> [c cinA fcsupfA]; exists c => // t tA; rewrite fcsupfA.
  by apply/sup_upper_bound => //; exact/imageP/set_mem.
have {}AfsupfA t : t \in A -> f t < sup (f @` A).
  move=> tA; have [//|supfAft] := ltrP (f t) (sup (f @` A)).
  rewrite falseE; apply: imf_ltsup; exists t => //.
  apply/eqP; rewrite eq_le supfAft andbT sup_upper_bound//.
  exact/imageP/set_mem.
pose g t : R := (sup (f @` A) - f t)^-1.
have invf_continuous : {within A, continuous g}.
  rewrite continuous_subspace_in => t tA; apply: cvgV => //=.
    by rewrite subr_eq0 gt_eqF// AfsupfA//; rewrite inE in tA.
  by apply: cvgD => //; apply: cvgN; exact: cf.
have /ex_strict_bound_gt0[k k_gt0 /= imVfltk] : bounded_set (g @` A).
  exact/compact_bounded/continuous_compact.
have [_ [t tA <-]] : exists2 y, (f @` A) y & sup (f @` A) - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
rewrite ltrBlDr -ltrBlDl.
suff : sup (f @` A) - f t > k^-1 by move=> /ltW; rewrite leNgt => /negbTE ->.
rewrite invf_plt ?posrE ?subr_gt0 ?AfsupfA//; first exact/mem_set.
by rewrite (le_lt_trans (ler_norm _))// imVfltk//; exact: imageP.
Qed.

Lemma compact_EVT_min d (T : topologicalType d) (R : realType) (f : T -> R)
    (A : set T) :
  A !=set0 -> compact A -> {within A, continuous f} ->
  exists2 c, c \in A & forall t, t \in A -> f c <= f t.
Proof.
move=> A0 cA cf.
have /(compact_EVT_max A0 cA)[c cinA fcmin] : {within A, continuous (- f)}.
  by move=> ?; apply: continuousN => ?; exact: cf.
by exists c => // t tA; rewrite -lerN2 fcmin.
Qed.

Lemma EVT_max (R : realType) (f : R -> R) (a b : R) :
  a <= b -> {within `[a, b], continuous f} ->
  exists2 c, c \in `[a, b]%R & forall t, t \in `[a, b]%R -> f t <= f c.
Proof.
move=> ab cf.
have ab0 : `[a, b] !=set0 by exists a => /=; rewrite in_itv/= lexx.
have [/= c cab maxf] := compact_EVT_max ab0 (@segment_compact _ a b) cf.
by rewrite inE in cab; exists c => //= t tab; apply: maxf; rewrite inE.
Qed.

Lemma EVT_min (R : realType) (f : R -> R) (a b : R) :
  a <= b -> {within `[a, b], continuous f} ->
  exists2 c, c \in `[a, b]%R & forall t, t \in `[a, b]%R -> f c <= f t.
Proof.
move=> ab cf.
have ab0 : `[a, b] !=set0 by exists a => /=; rewrite in_itv/= lexx.
have [/= c cab minf] := compact_EVT_min ab0 (@segment_compact _ a b) cf.
by rewrite inE in cab; exists c => //= t tab; apply: minf; rewrite inE.
Qed.

Lemma cvg_at_rightE {d} {R : numFieldType} {V : normedModType d R}
    (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ at_right x).
Proof.
move=> cvfx; apply/esym/norm_cvg_lim.
move=> A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y /gt_eqF/negbT/xe_A; exact.
Qed.
Arguments cvg_at_rightE {d R V} f x.

Lemma cvg_at_leftE {d} {R : numFieldType} {V : normedModType d R}
    (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ at_left x).
Proof.
move=> cvfx; apply/esym/norm_cvg_lim.
move=> A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y /lt_eqF/negbT/xe_A; exact.
Qed.
Arguments cvg_at_leftE {d R V} f x.

Lemma derive1_at_max {R : realFieldType} (f : R -> R) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[%R -> derivable f t 1) -> c \in `]a, b[%R ->
  (forall t, t \in `]a, b[%R -> f t <= f c) -> is_derive c 1 f 0.
Proof.
move=> leab fdrvbl cab cmax; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ['D_1 f c]cvg_at_rightE; first exact: fdrvbl.
  apply: limr_le.
    have /fdrvbl dfc := cab.
    rewrite -(cvg_at_rightE (fun h : R => h^-1 *: ((f \o shift c) _ - f c))) //.
    apply: cvg_trans dfc; apply: cvg_app.
    move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
    exact/lt0r_neq0.
  near=> h; apply: mulr_ge0_le0.
    by rewrite invr_ge0; apply: ltW; near: h; exists 1 => /=.
  rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
  exists (b - c); first by rewrite /= subr_gt0 (itvP cab).
  move=> h; rewrite /= distrC subr0 /= in_itv /= -ltrBrDr.
  move=> /(le_lt_trans (ler_norm _)) -> /ltr_pDl -> //.
  by rewrite (itvP cab).
rewrite ['D_1 f c]cvg_at_leftE; first exact: fdrvbl.
apply: limr_ge.
  have /fdrvbl dfc := cab.
  rewrite -(cvg_at_leftE (fun h => h^-1 *: ((f \o shift c) _ - f c)))//.
  apply: cvg_trans dfc; apply: cvg_app.
  move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
  exact/ltr0_neq0.
near=> h; apply: mulr_le0.
  by rewrite invr_le0; apply: ltW; near: h; exists 1 => /=.
rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
exists (c - a); first by rewrite /= subr_gt0 (itvP cab).
move=> h; rewrite /= distrC subr0.
move=> /ltr_normlP []; rewrite ltrBrDl ltrBlDl in_itv /= => -> _.
by move=> /ltr_nDl -> //; rewrite (itvP cab).
Unshelve. all: by end_near. Qed.

Lemma derive1_at_min {R : realFieldType} (f : R -> R) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[%R -> derivable f t 1) -> c \in `]a, b[%R ->
  (forall t, t \in `]a, b[%R -> f c <= f t) -> is_derive c 1 f 0.
Proof.
move=> leab fdrvbl cab cmin; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite -oppr_eq0; apply/eqP.
rewrite -deriveN; first exact: fdrvbl.
suff df : is_derive c 1 (- f) 0 by rewrite derive_val.
apply: derive1_at_max leab _ (cab) _ => t tab; first exact/derivableN/fdrvbl.
by rewrite lerN2; apply: cmin.
Qed.

Lemma Rolle (R : realType) (f : R -> R) (a b : R) :
  a < b -> (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  {within `[a, b], continuous f} -> f a = f b ->
  exists2 c, c \in `]a, b[%R & is_derive c 1 f 0.
Proof.
move=> ltab fdrvbl fcont faefb.
have [cmax cmaxab fcmax] := EVT_max (ltW ltab) fcont.
have [cmaxeaVb|] := boolP (cmax \in [set a; b]); last first.
  rewrite notin_setE => /not_orP[/eqP cnea /eqP cneb].
  have {}cmaxab : cmax \in `]a, b[%R.
    by rewrite in_itv /= !lt_def !(itvP cmaxab) cnea eq_sym cneb.
  exists cmax => //; apply: derive1_at_max (ltW ltab) fdrvbl cmaxab _ => t tab.
  by apply: fcmax; rewrite in_itv /= !ltW // (itvP tab).
have [cmin cminab fcmin] := EVT_min (ltW ltab) fcont.
have [cmineaVb|] := boolP (cmin \in [set a; b]); last first.
  rewrite notin_setE => /not_orP[/eqP cnea /eqP cneb].
  have {}cminab : cmin \in `]a, b[%R.
    by rewrite in_itv /= !lt_def !(itvP cminab) cnea eq_sym cneb.
  exists cmin => //; apply: derive1_at_min (ltW ltab) fdrvbl cminab _ => t tab.
  by apply: fcmin; rewrite in_itv /= !ltW // (itvP tab).
have midab : (a + b) / 2 \in `]a, b[%R by apply: mid_in_itvoo.
exists ((a + b) / 2) => //; apply: derive1_at_max (ltW ltab) fdrvbl (midab) _.
move=> t tab.
suff fcst s : s \in `]a, b[%R -> f s = f cmax by rewrite !fcst.
move=> sab.
apply/eqP; rewrite eq_le fcmax; first by rewrite in_itv /= !ltW ?(itvP sab).
suff -> : f cmax = f cmin by rewrite fcmin // in_itv /= !ltW ?(itvP sab).
by move: cmaxeaVb cmineaVb; rewrite 2!inE => -[|] -> [|] ->.
Qed.

Lemma MVT (R : realType) (f df : R -> R) (a b : R) :
  a < b -> (forall x, x \in `]a, b[%R -> is_derive x 1 f (df x)) ->
  {within `[a, b], continuous f} ->
  exists2 c, c \in `]a, b[%R & f b - f a = df c * (b - a).
Proof.
move=> altb fdrvbl fcont.
set g := f + (- ( *:%R^~ ((f b - f a) / (b - a)) : R -> R)).
have gdrvbl x : x \in `]a, b[%R -> derivable g x 1.
  by move=> /fdrvbl dfx; apply/derivableB/derivable1_diffP.
have gcont : {within `[a, b], continuous g}.
  move=> x; apply: continuousD _ ; first exact: fcont.
  exact/continuousN/continuous_subspaceT/scalel_continuous.
have gaegb : g a = g b.
  rewrite /g -![(_ - _ : _ -> _) _]/(_ - _).
  apply/eqP; rewrite -subr_eq /= opprK addrAC -addrA -scalerBl.
  rewrite [_ *: _]mulrC divfK; last by rewrite addrC subrK.
  by apply: lt0r_neq0; rewrite subr_gt0.
have [c cab dgc0] := Rolle altb gdrvbl gcont gaegb.
exists c; first exact: cab.
have /fdrvbl dfc := cab; move/@derive_val: dgc0; rewrite deriveB //.
move/eqP; rewrite [X in _ - X]deriveE // derive_val diff_val scale1r subr_eq0.
by move/eqP->; rewrite divfK// subr_eq0 gt_eqF.
Qed.

(* Weakens MVT to work when the interval is a single point: *)
Lemma MVT_segment (R : realType) (f df : R -> R) (a b : R) :
  a <= b -> (forall x, x \in `]a, b[%R -> is_derive x 1 f (df x)) ->
  {within `[a, b], continuous f} ->
  exists2 c, c \in `[a, b]%R & f b - f a = df c * (b - a).
Proof.
move=> leab fdrvbl fcont; case: ltgtP leab => // [altb|aeb]; last first.
  by exists a; [rewrite inE/= aeb lexx|rewrite aeb !subrr mulr0].
have [c cab D] := MVT altb fdrvbl fcont.
by exists c => //; rewrite in_itv /= ltW (itvP cab).
Qed.

Section ger0_derive1_le.
Context {R : realType} (f : R -> R) (a b : R).
Hypothesis df : forall x, x \in `]a, b[%R -> derivable f x 1.
Hypothesis dfge0 : forall x, x \in `]a, b[%R -> 0 <= f^`() x.

Lemma ger0_derive1_le (sa sb : bool) :
  {within [set` (Interval (BSide sa a) (BSide sb b))], continuous f} ->
  {in Interval (BSide sa a) (BSide sb b) &, {homo f : x y / x <= y}}.
Proof.
move=> cf x y + + xy.
move: (xy); rewrite le_eqVlt=> /predU1P[-> | xy']; first by rewrite lexx.
rewrite !itv_boundlr -subr_ge0 /= => /andP[ax _] /andP[_ yb].
have HMVT1 : {within `[x, y], continuous f}.
  exact/(continuous_subspaceW _ cf)/subset_itv.
have zab : `]x, y[ `<=` `]a, b[.
  clear -ax yb; apply/subset_itv.
    by move: sa ax => []; rewrite !bnd_simp// => /ltW.
  by move: sb yb => []; rewrite !bnd_simp// => /ltW.
have HMVT0 z : z \in `]x, y[%R -> is_derive z 1 f (f^`() z).
  by move=> zxy; rewrite derive1E; exact/derivableP/df/zab.
have[z zxy ->]:= MVT xy' HMVT0 HMVT1.
by rewrite mulr_ge0// ?subr_ge0// dfge0// zab.
Qed.

Lemma ger0_derive1_le_cc : {within `[a, b] , continuous f} ->
  {in `[a, b]%R &, {homo f : x y / x <= y >-> x <= y}}.
Proof. exact: ger0_derive1_le. Qed.

Lemma ger0_derive1_le_co : {within `[a, b[ , continuous f} ->
  {in `[a, b[%R &, {homo f : x y / x <= y >-> x <= y}}.
Proof. exact: ger0_derive1_le. Qed.

Lemma ger0_derive1_le_oc : {within `]a, b], continuous f} ->
  {in `]a, b]%R &, {homo f : x y / x <= y >-> x <= y}}.
Proof. exact: ger0_derive1_le. Qed.

Lemma ger0_derive1_le_oo : {in `]a, b[, continuous f} ->
  {in `]a, b[%R &, {homo f : x y / x <= y >-> x <= y}}.
Proof. by rewrite -continuous_open_subspace//; exact: ger0_derive1_le. Qed.

End ger0_derive1_le.

Section ler0_derive1_le.
Context {R : realType} (f : R -> R) (a b : R).
Hypothesis df : forall x, x \in `]a, b[%R -> derivable f x 1.
Hypothesis dfle0 : forall x, x \in `]a, b[%R -> f^`() x <= 0.

Lemma ler0_derive1_le (sa sb : bool) :
  {within [set` (Interval (BSide sa a) (BSide sb b))], continuous f} ->
  {in Interval (BSide sa a) (BSide sb b) &, {homo f : x y /~ x <= y}}.
Proof.
move=> cf.
suff : {in Interval (BSide sa a) (BSide sb b) &, {homo (- f) : x y / x <= y}}.
  by move=> h y x iy ix xy; move: (h x y ix iy xy); rewrite opprfctE lerNl opprK.
apply: ger0_derive1_le.
- move => x xab; exact/derivableN/df.
- move => x xab; rewrite derive1E deriveN; first exact: df.
  by rewrite -derive1E oppr_ge0 dfle0.
by move=> x; exact/continuousN/cf.
Qed.

Lemma ler0_derive1_le_cc :{within `[a, b], continuous f} ->
  {in `[a, b]%R &, {homo f : x y /~ x <= y}}.
Proof. exact: ler0_derive1_le. Qed.

Lemma ler0_derive1_le_co : {within `[a, b[, continuous f} ->
  {in `[a, b[%R &, {homo f : x y /~ x <= y}}.
Proof. exact: ler0_derive1_le. Qed.

Lemma ler0_derive1_le_oc : {within `]a, b], continuous f} ->
  {in `]a, b]%R &, {homo f : x y /~ x <= y}}.
Proof. exact: ler0_derive1_le. Qed.

Lemma ler0_derive1_le_oo : {in `]a, b[, continuous f} ->
  {in `]a, b[%R &, {homo f : x y /~ x <= y}}.
Proof. by rewrite -continuous_open_subspace//; exact: ler0_derive1_le. Qed.

End ler0_derive1_le.

Section gtr0_derive1_lt.
Context {R : realType} (f : R -> R) (a b : R).
Hypothesis df : forall x, x \in `]a, b[%R -> derivable f x 1.
Hypothesis dfgt0 : forall x, x \in `]a, b[%R -> 0 < f^`() x.

Lemma gtr0_derive1_lt (sa sb : bool) :
  {within [set` (Interval (BSide sa a) (BSide sb b))], continuous f} ->
  {in Interval (BSide sa a) (BSide sb b) &, {homo f : x y / x < y}}.
Proof.
move=> cf x y + + xy.
rewrite !itv_boundlr /= -subr_gt0 => /andP [] ax ? /andP [] ? yb.
have HMVT1: {within `[x, y], continuous f}.
  exact/(continuous_subspaceW _ cf)/subset_itv.
have zab : `]x, y[ `<=` `]a, b[.
  clear -ax yb; apply/subset_itv.
    by move: sa ax => []; rewrite !bnd_simp// => /ltW.
  by move: sb yb => []; rewrite !bnd_simp// => /ltW.
have HMVT0 (z : R^o) : z \in `]x, y[%R -> is_derive z 1 f (f^`() z).
  by move=> zxy; rewrite derive1E; exact/derivableP/df/zab.
have[z zxy ->]:= MVT xy HMVT0 HMVT1.
by rewrite mulr_gt0// ?subr_gt0// dfgt0// zab.
Qed.

Lemma gtr0_derive1_lt_cc : {within `[a, b], continuous f} ->
  {in `[a, b]%R &, {homo f : x y / x < y}}.
Proof. exact: gtr0_derive1_lt. Qed.

Lemma gtr0_derive1_lt_co : {within `[a, b[, continuous f} ->
  {in `[a, b[%R &, {homo f : x y / x < y}}.
Proof. exact: gtr0_derive1_lt. Qed.

Lemma gtr0_derive1_lt_oc : {within `]a, b], continuous f} ->
  {in `]a, b]%R &, {homo f : x y / x < y}}.
Proof. exact: gtr0_derive1_lt. Qed.

Lemma gtr0_derive1_lt_oo : {in `]a, b[, continuous f} ->
  {in `]a, b[%R &, {homo f : x y / x < y}}.
Proof. by rewrite -continuous_open_subspace//; exact: gtr0_derive1_lt. Qed.

End gtr0_derive1_lt.

Section ltr0_derive1_lt.
Context {R : realType} (f : R -> R) (a b : R).
Hypothesis df : forall x, x \in `]a, b[%R -> derivable f x 1.
Hypothesis dflt0 : forall x, x \in `]a, b[%R -> f^`() x < 0.

Lemma ltr0_derive1_lt (sa sb : bool) :
  {within [set` (Interval (BSide sa a) (BSide sb b))], continuous f} ->
  {in Interval (BSide sa a) (BSide sb b) &, {homo f : x y /~ x < y}}.
Proof.
move=> cf.
suff : {in Interval (BSide sa a) (BSide sb b) &, {homo (- f) : x y / x < y}}.
  by move=> h x y ix iy xy; move: (h y x iy ix xy); rewrite opprfctE ltrNl opprK.
apply: gtr0_derive1_lt.
- move => x xab; exact/derivableN/df.
- move => x xab; rewrite derive1E deriveN; first exact: df.
  by rewrite -derive1E oppr_gt0 dflt0.
by move=> x; exact/continuousN/cf.
Qed.

Lemma ltr0_derive1_lt_cc : {within `[a, b], continuous f} ->
  {in `[a, b]%R &, {homo f : x y /~ x < y}}.
Proof. exact: ltr0_derive1_lt. Qed.

Lemma ltr0_derive1_lt_co : {within `[a, b[, continuous f} ->
  {in `[a, b[%R &, {homo f : x y /~ x < y}}.
Proof. exact: ltr0_derive1_lt. Qed.

Lemma ltr0_derive1_lt_oc : {within `]a, b], continuous f} ->
  {in `]a, b]%R &, {homo f : x y /~ x < y}}.
Proof. exact: ltr0_derive1_lt. Qed.

Lemma ltr0_derive1_lt_oo : {in `]a, b[, continuous f} ->
  {in `]a, b[%R &, {homo f : x y /~ x < y}}.
Proof. by rewrite -continuous_open_subspace//; exact: ltr0_derive1_lt. Qed.

End ltr0_derive1_lt.

#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
    H : x \is_near _ |- _ =>
      solve[near: x; apply: nbhs_pinfty_ge; apply: num_real]
  end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
    H : x \is_near _ |- _ =>
      solve[near: x; apply: nbhs_ninfty_le; apply: num_real]
  end : core.

Lemma ler0_derive1_nincry {R : realType} (f : R -> R) (a : R) :
  (forall x, x \in `]a, +oo[%R -> derivable f x 1) ->
  (forall x, x \in `]a, +oo[%R -> f^`() x <= 0) ->
  {within `[a, +oo[, continuous f} ->
  forall x y, a <= x -> x <= y -> f y <= f x.
Proof.
move=> df dfle0 cf x y ax xy.
near (pinfty_nbhs R)%R => N.
apply: (@ler0_derive1_le_cc _ _ a N) => [r|r| | | | // ]; rewrite ?in_itv/=.
- by move=> /andP[ar rN]; apply: df; rewrite !in_itv/= andbT ar.
- by move=> /andP[ar rN]; apply: dfle0; rewrite !in_itv/= andbT ar.
- exact/continuous_subspaceW/cf/subset_itvl.
- by rewrite (le_trans ax)/=.
- by rewrite ax/=.
Unshelve. all: end_near. Qed.

Lemma ler0_derive1_nincrNy {R : realType} (f : R -> R) (b : R) :
  (forall x, x \in `]-oo, b[%R -> derivable f x 1) ->
  (forall x, x \in `]-oo, b[%R -> f^`() x <= 0) ->
  {within `]-oo, b], continuous f} ->
  forall x y, x <= y -> y <= b -> f y <= f x.
Proof.
move=> df dfle0 cf x y xy yb.
near (ninfty_nbhs R)%R => N.
apply: (@ler0_derive1_le_cc _ _ N b) => [r|r| | | | // ]; rewrite ?in_itv/=.
- by move=> /andP[Nr rb]; apply: df; rewrite !in_itv/= rb.
- by move=> /andP[Nr rb]; apply: dfle0; rewrite !in_itv/= rb.
- exact/continuous_subspaceW/cf/subset_itvr.
- by rewrite yb andbT.
by rewrite (le_trans xy)//= andbT.
Unshelve. all: end_near. Qed.

Lemma ger0_derive1_ndecr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> 0 <= f^`() x) ->
  {within `[a,b], continuous f} ->
  forall x y, a <= x -> x <= y -> y <= b -> f x <= f y.
Proof.
move=> df dfge0 cf x y ax xy yb.
by apply: (@ger0_derive1_le_cc _ _ a b) => //;
  rewrite in_itv/= ?(le_trans _ xy)//= ?(le_trans xy) ?andbT.
Qed.

Lemma ger0_derive1_ndecry {R : realType} (f : R -> R) (a : R) :
  (forall x, x \in `]a, +oo[%R -> derivable f x 1) ->
  (forall x, x \in `]a, +oo[%R -> 0 <= f^`() x) ->
  {within `[a, +oo[, continuous f} ->
  forall x y, a <= x -> x <= y -> f x <= f y.
Proof.
move=> df dfge0 cf x y ax xy.
near (pinfty_nbhs R)%R => N.
apply: (@ger0_derive1_le_cc _ _ a N) => [r|r| | | | // ]; rewrite ?in_itv/=.
- by move=> /andP[ar rN]; apply: df; rewrite !in_itv/= andbT ar.
- by move=> /andP[ar rN]; apply: dfge0; rewrite !in_itv/= andbT ar.
- exact/continuous_subspaceW/cf/subset_itvl.
- by rewrite (le_trans ax)/=.
- by rewrite (le_trans ax)/=.
Unshelve. all: end_near. Qed.

Lemma ger0_derive1_ndecrNy {R : realType} (f : R -> R) (b : R) :
  (forall x, x \in `]-oo, b[%R -> derivable f x 1) ->
  (forall x, x \in `]-oo, b[%R -> 0 <= f^`() x) ->
  {within `]-oo, b], continuous f} ->
  forall x y, x <= y -> y <= b -> f x <= f y.
Proof.
move=> df dfge0 cf x y xy yb.
near (ninfty_nbhs R)%R => N.
apply: (@ger0_derive1_le_cc _ _ N b) => [r|r| | | | // ]; rewrite ?in_itv/=.
- by move=> /andP[Nr rb]; apply: df; rewrite !in_itv/=.
- by move=> /andP[Nr rb]; apply: dfge0; rewrite !in_itv/=.
- exact/continuous_subspaceW/cf/subset_itvr.
- by rewrite (le_trans xy)//= andbT.
- by rewrite yb andbT.
Unshelve. all: end_near. Qed.

Lemma decr_derive1_le0 {R : realFieldType} (f : R -> R) (D : set R) (x : R) :
  {in D° : set R, forall x, derivable f x 1%R} ->
  {in D &, {homo f : x y /~ x < y}} ->
  D° x -> f^`() x <= 0.
Proof.
move=> df decrf Dx.
apply: limr_le.
  under eq_fun; first (move=> h; rewrite -{2}(scaler1 h); over).
  by apply: df; rewrite inE.
have [e /= e0 Hball] := open_subball (open_interior D) Dx.
near=> h.
have h0 : h != 0%R by near: h.
have Dhx : D° (h + x).
  apply: (Hball (`|2 * h|%R)) => //.
  - rewrite /= sub0r normrN normr_id normrM ger0_norm// -ltr_pdivlMl//.
      by near: h; apply: dnbhs0_lt; exact: mulr_gt0.
    by rewrite normrM ger0_norm// mulr_gt0// normr_gt0.
  apply: ball_sym; rewrite /ball/= addrK.
  by rewrite normrM (@ger0_norm _ 2)// ltr_pMl ?normr_gt0// ltr1n.
move: h0; rewrite neq_lt => /orP[h0|h0].
- rewrite nmulr_rle0 ?invr_lt0// subr_ge0 ltW//.
  by apply: decrf; rewrite ?in_itv ?andbT ?gtrDr// inE; exact: interior_subset.
- rewrite pmulr_rle0 ?invr_gt0// subr_le0 ltW//.
  by apply: decrf; rewrite ?in_itv ?andbT ?ltrDr// inE; exact: interior_subset.
Unshelve. end_near. Qed.

Lemma decr_derive1_le0_itv {R : realType} (f : R -> R)
    (b0 b1 : bool) (a b : R) (z : R) :
  {in `]a, b[, forall x : R, derivable f x 1%R} ->
  {in Interval (BSide b0 a) (BSide b1 b) &, {homo f : x y /~ (x < y)%R}} ->
  z \in `]a, b[%R -> f^`() z <= 0.
Proof.
have [?|ab] := leP b a; first by move=> _ _ /lt_in_itv; rewrite bnd_simp le_gtF.
move=> df decrf zab.
have {}zab : [set` (Interval (BSide b0 a) (BSide b1 b))]° z.
  by rewrite interior_itv// inE/=.
apply: decr_derive1_le0 zab; first by rewrite interior_itv.
by move=> x y /[!inE]/=; apply/decrf.
Qed.

Lemma decr_derive1_le0_itvy {R : realType} (f : R -> R)
    (b0 : bool) (a : R) (z : R) :
  {in `]a, +oo[, forall x : R, derivable f x 1%R} ->
  {in Interval (BSide b0 a) (BInfty _ false) &, {homo f : x y /~ (x < y)%R}} ->
  z \in `]a, +oo[%R -> f^`() z <= 0.
Proof.
move=> df decrf zay.
have {}zay : [set` (Interval (BSide b0 a) (BInfty _ false))]° z.
  by rewrite interior_itv// inE/=.
apply: decr_derive1_le0 zay; first by rewrite interior_itv.
by move=> x y /[!inE]/=; apply/decrf.
Qed.

Lemma decr_derive1_le0_itvNy {R : realType} (f : R -> R)
    (b1 : bool) (b : R) (z : R) :
  {in `]-oo, b[, forall x : R, derivable f x 1%R} ->
  {in Interval (BInfty _ true) (BSide b1 b) &, {homo f : x y /~ (x < y)%R}} ->
  z \in `]-oo, b[%R -> f^`() z <= 0.
Proof.
move=> df decrf zNyb.
have {}zNyb : [set` (Interval (BInfty _ true) (BSide b1 b))]° z.
  by rewrite interior_itv// inE/=.
apply: decr_derive1_le0 zNyb; first by rewrite interior_itv.
by move=> x y /[!inE]/=; apply/decrf.
Qed.

Lemma incr_derive1_ge0 {R : realFieldType} (f : R -> R)
   (D : set R) (x : R):
  {in D° : set R, forall x : R, derivable f x 1%R} ->
  {in D &, {homo f : x y / (x < y)%R}} ->
  D° x -> 0 <= f^`() x.
Proof.
move=> df incrf Dx; rewrite -[leRHS]opprK oppr_ge0.
have dfx : derivable f x 1 by apply: df; rewrite inE.
rewrite derive1E -deriveN// -derive1E; apply: decr_derive1_le0 Dx.
- by move=> y Dy; apply: derivableN; apply: df.
- by move=> y z Dy Dz yz; rewrite ltrN2; apply: incrf.
Qed.

Lemma incr_derive1_ge0_itv {R : realType} (f : R -> R)
  (b0 b1 : bool) (a b : R) (z : R) :
  {in `]a, b[ : set R, forall x : R, derivable f x 1%R} ->
  {in Interval (BSide b0 a) (BSide b1 b) &, {homo f : x y / (x < y)%R}} ->
  z \in `]a, b[%R -> 0 <= f^`() z.
Proof.
move=> df incrf zab; rewrite -[leRHS]opprK oppr_ge0.
have dfz : derivable f z 1 by apply: df; rewrite inE.
rewrite derive1E -deriveN// -derive1E.
apply: (@decr_derive1_le0_itv _ _ b0 b1 a b); last exact: zab.
- by move=> y Dy; apply: derivableN; apply: df.
- move=> x y Dx Dy yx; rewrite ltrN2; apply: incrf => //; rewrite in_itv/=.
Qed.

Lemma incr_derive1_ge0_itvy {R : realType} (f : R -> R)
    (b0 : bool) (a : R) (z : R) :
  {in `]a, +oo[, forall x : R, derivable f x 1%R} ->
  {in Interval (BSide b0 a) +oo%O &, {homo f : x y / (x < y)%R}} ->
  z \in `]a, +oo[%R -> 0 <= f^`() z.
Proof.
move=> df incrf zay; rewrite -[leRHS]opprK oppr_ge0.
have dfz : derivable f z 1 by apply: df; rewrite inE.
rewrite derive1E -deriveN// -derive1E.
apply: (@decr_derive1_le0_itvy _ _ b0 _ _ _ _ zay).
- by move=> y Dy; apply: derivableN; apply: df.
- by move=> x y Dx Dy yx; rewrite ltrN2; apply: incrf.
Qed.

Lemma incr_derive1_ge0_itvNy {R : realType} (f : R -> R)
    (b1 : bool) (b : R) (z : R) :
  {in `]-oo, b[, forall x : R, derivable f x 1%R} ->
  {in Interval (BInfty _ true) (BSide b1 b) &, {homo f : x y / (x < y)%R}} ->
  z \in `]-oo, b[%R -> 0 <= f^`() z.
Proof.
move=> df incrf zNyb; rewrite -[leRHS]opprK oppr_ge0.
have dfz : derivable f z 1 by apply: df; rewrite inE.
rewrite derive1E -deriveN// -derive1E.
apply: (@decr_derive1_le0_itvNy _ _ b1 _ _ _ _ zNyb).
- by move=> y Dy; apply: derivableN; apply: df.
- by move=> x y Dx Dy yx; rewrite ltrN2; apply: incrf.
Qed.

Lemma derive1_comp {R : numFieldType} (f g : R -> R) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  (g \o f)^`() x = g^`()%classic (f x) * f^`()%classic x.
Proof.
move=> /derivable1_diffP df /derivable1_diffP dg.
rewrite derive1E'; first exact/differentiable_comp.
rewrite diff_comp // !derive1E' //= -[X in 'd  _ _ X = _]mulr1.
by rewrite [LHS]linearZ mulrC.
Qed.

Global Instance is_derive1_comp {R : numFieldType} (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b -> is_derive x 1 (f \o g) (a * b).
Proof.
move=> [fgxv <-{a}] [gv <-{b}]; apply: (@DeriveDef _ _ _ _ _ _ _ (f \o g)).
  apply/derivable1_diffP/differentiable_comp; first exact/derivable1_diffP.
  by move/derivable1_diffP in fgxv.
by rewrite -derive1E (derive1_comp gv fgxv) 2!derive1E.
Qed.

Lemma near_eq_growth_rate {d} {R : numFieldType} {V : normedModType d R}
    {d'} {W : normedModType d' R} (f g : V -> W) (a v : V) :
  {near a, f =1 g} ->
  \forall h \near 0,
    h^-1 *: (f (h *: v + a) - f a) = h^-1 *: (g (h *: v + a) - g a).
Proof.
move=> fg; near do rewrite (nbhs_singleton fg) (near fg)// addrC.
apply/(@near0Z _ _ _ _ [set v | (a + v) \is_near (nbhs a)])=> /=.
by rewrite (near_shift a)/=; near do rewrite /= sub0r addrC addrNK//.
Unshelve. all: by end_near. Qed.

Lemma near_eq_derivable {d} {R : numFieldType} {V : normedModType d R}
    {d'} {W : normedModType d' R} (f g : V -> W) (a v : V) :
  {near a, f =1 g} -> derivable f a v -> derivable g a v.
Proof.
have [-> _ _|] := eqVneq v 0; first exact/derivable0.
move=> vn0 nfg /cvg_ex[/= l fl]; apply/cvg_ex; exists l => /=.
exact/(cvg_trans _ fl)/near_eq_cvg/cvg_within/near_eq_growth_rate.
Qed.

Lemma near_eq_derive {d} {R : numFieldType} {V : normedModType d R}
    {d'} {W : normedModType d' R} (f g : V -> W) (a v : V) :
  (\forall a0 \near a, f a0 = g a0) -> 'D_v f a = 'D_v g a.
Proof.
have [-> _|] := eqVneq v 0; first by rewrite !derive0.
move=> v0 fg; rewrite /derive; congr (lim _).
rewrite eqEsubset; split; apply/near_eq_cvg/cvg_within/near_eq_growth_rate =>//.
by near do apply/esym.
Unshelve. all: by end_near. Qed.

Lemma near_eq_is_derive {d} {R : numFieldType} {V : normedModType d R}
    {d'} {W : normedModType d' R} (f g : V -> W) (a v : V) (df : W) :
  (\forall a0 \near a, f a0 = g a0) -> is_derive a v f df -> is_derive a v g df.
Proof.
move=> fg [fav <-]; rewrite (near_eq_derive _ fg).
by apply: DeriveDef => //; exact: near_eq_derivable fav.
Qed.

Section near_eq_derive1.
Context {d} {R : numFieldType} {V : normedModType d R}.
Implicit Types (f g : R -> V) (x : R).

Lemma near_eq_derive1n_near n f g x:
  {near x, f =1 g} -> {near x, f^`(n) =1 g^`(n)}.
Proof.
move=> fg; elim: n => [//|n IH].
near do (rewrite 2!derive1nS !derive1E; apply: near_eq_derive).
exact: (@near_join _ _ x).
Unshelve. all: by end_near. Qed.

Lemma near_eq_derive1_near f g x : {near x, f =1 g} -> {near x, f^`() =1 g^`()}.
Proof. by rewrite -!derive1n1; exact: near_eq_derive1n_near. Qed.

Lemma near_eq_derive1n n f g x : {near x, f =1 g} -> f^`(n) x = g^`(n) x.
Proof. by move=> /near_eq_derive1n_near => /(_ n)/nbhs_singleton. Qed.

Lemma near_eq_derive1 f g x : {near x, f =1 g} -> f^`() x = g^`() x.
Proof. by rewrite -!derive1n1; exact: near_eq_derive1n. Qed.

End near_eq_derive1.

Section Derive_max.
Context {d} {K : realType} {V : normedModType d K}
  {d'} {W : normedModType d' K}.
Implicit Types f g : V -> K^o.
Implicit Type x : V.

Fact der_max_subproof f g x v : f x != g x ->
  derivable f x v -> derivable g x v ->
  {for x, continuous f} -> {for x, continuous g} ->
  (fun h => h^-1 *: (((f \max g) \o shift x) (h *: v) - (f \max g) x))
    @ 0^' --> if f x < g x then 'D_v g x else 'D_v f x.
Proof.
wlog: f g x / f x < g x.
  move=> wlg; rewrite neq_lt => /orP[fg|gf df dg fxv gxv].
  - by apply: wlg => //; rewrite lt_eqF.
  - rewrite fun_maxC ltNge if_neg le_eqVlt eq_sym gt_eqF//=.
    by apply: wlg => //; rewrite lt_eqF.
move=> fx_lt_gx fg_neq df dg cf cg; case: ifPn => fg /=.
- rewrite /Num.max fg => A DgxA.
  apply: (@near_eq_cvg _ _ _ _ (fun h => h^-1 *: (g (h *: v + x) - g x))).
  + near do rewrite ifT// -subr_lt0 -[ltLHS]/(((f - g) \o shift x) (_ *: v)).
    have Hf (h : V -> K^o) : continuous_at x h ->
        h (shift x (k *: v)) @[k --> nbhs 0^'] --> h x.
      move=> ch.
      apply: cvg_comp; last exact: ch.
      by apply: cvg0D => //; apply: cvg0Z => //; exact: nbhs_dnbhs.
    apply/(cvgr_lt (f x - g x)); last by rewrite subr_lt0.
    by apply: cvgB; exact: Hf.
  + exact: dg.
- absurd.
  by rewrite fx_lt_gx in fg.
Unshelve. all: by end_near. Qed.

Lemma derivable_max f g x v :
  f x != g x -> derivable f x v -> derivable g x v ->
  {for x, continuous f} -> {for x, continuous g} ->
  derivable (f \max g) x v.
Proof.
move=> fx_gx df dg cf cg; apply/cvg_ex => /=.
exists (if f x < g x then 'D_v g x else 'D_v f x).
exact: der_max_subproof.
Qed.

Lemma derive_maxl f g x v : f x > g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \max g) x = 'D_v f x.
Proof.
have [-> gx_fx cf cg|v0 fg cf cg]:= eqVneq v 0.
  by rewrite !derive0.
apply: near_eq_derive => //.
near do rewrite /Order.max_fun /Num.max ifN// -leNgt -subr_le0.
by move: fg; rewrite -subr_lt0; apply: cvgr_le; exact: cvgB.
Unshelve. all: by end_near. Qed.

Lemma derive_maxr f g x v : f x < g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \max g) x = 'D_v g x.
Proof. by move=> fg cf cg; rewrite fun_maxC derive_maxl. Qed.

Lemma derivable_min f g x v :
  f x != g x -> derivable f x v -> derivable g x v ->
  {for x, continuous f} -> {for x, continuous g} ->
  derivable (f \min g) x v.
Proof.
have [-> *|x0] := eqVneq v 0; first exact/derivable0.
rewrite min_fun_to_max => fx_gx df dg cf cg.
by apply/derivableB; [apply/(derivableD df dg) |apply/derivable_max].
Qed.

Lemma derive_minr f g x v : f x > g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \min g) x = 'D_v g x.
Proof.
have [-> *|v0 fg cf cg] := eqVneq v 0; first by rewrite !derive0.
apply: near_eq_derive => //.
near do rewrite /Order.min_fun /Num.min ifN// -leNgt -subr_le0.
by move: fg; rewrite -subr_lt0; apply: cvgr_le; exact: cvgB.
Unshelve. all: by end_near. Qed.

Lemma derive_minl f g x v : f x < g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \min g) x = 'D_v f x.
Proof. by move=> fg cf cg; rewrite fun_minC derive_minr. Qed.

End Derive_max.

Lemma derive1N {R : realFieldType} (f : R -> R) (x : R) :
  derivable f x 1 -> (- f)^`() x = (- f^`()%classic x).
Proof. by move=> fx; rewrite !derive1E deriveN. Qed.

Lemma derivable_opp {R : realFieldType} (x : R) v : derivable -%R x v.
Proof. by apply: derivableN; exact: derivable_id. Qed.

Lemma derive1_id {R : realFieldType} (x : R) : id^`() x = 1.
Proof. by rewrite derive1E derive_id. Qed.

(* Trick to trigger type class resolution *)
Lemma trigger_derive (R : realType) (f : R -> R) x x1 y1 :
  is_derive x (1 : R) f x1 -> x1 = y1 -> is_derive x 1 f y1.
Proof. by move=> Hi <-. Qed.

Section derive_horner.
Context {R : realFieldType}.
Local Open Scope ring_scope.

Lemma horner0_ext : horner (0 : {poly R}) = 0.
Proof. by apply/funext => y /=; rewrite horner0. Qed.

Lemma hornerD_ext (p : {poly R}) r :
  horner (p * 'X + r%:P) = horner (p * 'X) + horner (r%:P).
Proof. by apply/funext => y /=; rewrite !(hornerE,fctE). Qed.

Lemma horner_scale_ext (p : {poly R}) :
  horner (p * 'X) = (fun x => p.[x] * x)%R.
Proof. by apply/funext => y; rewrite !hornerE. Qed.

Lemma hornerC_ext (r : R) : horner r%:P = cst r.
Proof. by apply/funext => y /=; rewrite !hornerE. Qed.

Lemma derivable_horner (p : {poly R}) x : derivable (horner p) x 1.
Proof.
elim/poly_ind: p => [|p r ih]; first by rewrite horner0_ext.
rewrite hornerD_ext; apply: derivableD.
- rewrite horner_scale_ext/=.
  by apply: derivableM; [exact:ih|exact:derivable_id].
- by rewrite hornerC_ext; exact: derivable_cst.
Qed.

Lemma derivE (p : {poly R}) : horner (p^`()) = (horner p)^`()%classic.
Proof.
apply/funext => x; elim/poly_ind: p => [|p r ih].
  by rewrite deriv0 hornerC horner0_ext derive1_cst.
rewrite derivD hornerD hornerD_ext.
rewrite derive1E deriveD//; [exact: derivable_horner..|].
rewrite -!derive1E hornerC_ext derive1_cst addr0.
rewrite horner_scale_ext derive1E deriveM//; first exact: derivable_horner.
rewrite derive_id -derive1E -ih derivC horner0 addr0 derivM hornerD !hornerE.
by rewrite derivX hornerE mulr1 addrC mulrC scaler1.
Qed.

Global Instance is_derive_poly (p : {poly R}) (x : R) :
  is_derive x (1:R) (horner p) p^`().[x].
Proof.
by apply: DeriveDef; [exact: derivable_horner|rewrite derivE derive1E].
Qed.

Lemma continuous_horner (p : {poly R}) : continuous (horner p).
Proof.
move=> /= x; apply/differentiable_continuous.
exact/derivable1_diffP/derivable_horner.
Qed.

End derive_horner.

Section derivative_limit_thm_right.
Context {R : realType} (f df : R -> R) (a l : R).
Hypothesis cfa : f @ a^'+ --> f a.
Hypothesis der_f : \forall x \near a^'+, is_derive x (1 : R) f (df x).
Hypothesis df_rcvg : df @ a^'+ --> l.

Lemma right_derivative_limit : h^-1 *: (f (h + a) - f a) @[h --> 0^'+] --> l.
Proof.
apply/cvgrPdist_lt => /= e e0.
have [/= r r0 dfr] := der_f.
move: df_rcvg => /cvgrPdist_lt /(_ e e0) [/= s s0 dfs].
near=> h.
have aha : a < h + a by rewrite ltrDr.
have [//| | |c + ->] := @MVT _ f df a (h + a).
- move=> x; rewrite in_itv/= => /andP[ax xha].
  apply: dfr => //=.
  by rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr (lt_trans xha)// ltrD2r.
- apply/continuous_within_itvccP => //; split => //.
  + move=> x; rewrite in_itv/= => /andP[ax xha].
    apply/differentiable_continuous/derivable1_diffP/ex_derive.
    apply: dfr => //=.
    by rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr (lt_trans xha)// ltrD2r.
  + apply: cvg_at_left_filter.
    apply/differentiable_continuous/derivable1_diffP/ex_derive.
    apply: dfr => //=.
    by rewrite addrC opprD subrK normrN gtr0_norm.
rewrite in_itv/= => /andP[ac cha].
rewrite addrK [X in `|_ - X|]mulrCA mulVf ?mulr1//.
apply: dfs => //=.
by rewrite ltr0_norm ?subr_lt0// opprB ltrBlDr (lt_trans cha)// ltrD2r.
Unshelve. all: by end_near. Qed.

End derivative_limit_thm_right.
Arguments right_derivative_limit {R f} df.

Section derivative_limit_thm_left.
Context {R : realType} (f df : R -> R) (b l : R).
Hypothesis cfb : f @ b^'- --> f b.
Hypothesis der_f : \forall x \near b^'-, is_derive x (1 :> R) f (df x).
Hypothesis df_lcvg : df @ b^'- --> l.

Lemma left_derivative_limit : h^-1 *: (f (h + b) - f b) @[h --> 0^'-] --> l.
Proof.
have := @right_derivative_limit _ (f \o -%R) (\- df \o -%R) (-b) (-l).
rewrite /= !opprK.
have /[swap] /[apply] : (f \o -%R) x @[x --> (- b)^'+] --> f b.
  by rewrite -cvg_at_leftNP.
have /[swap] /[apply] :
    \forall x \near (- b)^'+, is_derive x (1 : R) (f \o -%R) (- df (- x)).
  rewrite at_rightN near_map; near=> x.
  apply: is_derive_eq.
    apply: (is_derive1_comp (a := df x)) => //.
    by rewrite opprK; near: x.
  by rewrite derive_val mulrN1 opprK.
have /[swap] /[apply] : (\- df \o -%R) x @[x --> (- b)^'+] --> - l.
  by apply: cvgN; exact/cvg_at_leftNP.
move=> /cvg_at_rightNP /cvgN; rewrite oppr0 opprK.
apply: cvg_trans; apply: near_eq_cvg.
near=> h.
by rewrite fctE/= opprB invrN scaleNr !opprK (addrC b).
Unshelve. all: by end_near. Qed.

End derivative_limit_thm_left.
Arguments left_derivative_limit {R f} df.

(**md
For $a \in \mathbb{R}$ and $f : \mathbb{R} \to \mathbb{R}$, if:
1. $f$ is continuous at $a$
2. $f$ is derivable near $a$ (but not necessarily *at* $a$)
3. The limit of $f'(x)$ as $x \to a, x \neq a$ exists and equals $\ell \in \mathbb{R}$

Then $f$ is derivable at $a$ and $f'(a) = \ell$. *)
Section derivative_limit_thm.
Context {R : realType} (f df : R -> R) (a l : R).
Hypothesis cfa : continuous_at a f.
Hypothesis der_f : \forall x \near a^', is_derive x (1 : R) f (df x).
Hypothesis df_dcvg : df @ a^' --> l.

Lemma derivative_limit : is_derive a 1 f l.
Proof.
suff dcvg : h^-1 *: (f (h%:A + a) - f a) @[h --> 0^'] --> l.
  by split; [ exact: cvgP dcvg | exact: norm_cvg_lim dcvg ].
under eq_cvg do rewrite scaler1.
apply: cvg_at_right_left_dnbhs.
- apply: (right_derivative_limit df).
  + exact: cvg_at_right_filter cfa.
  + by apply: within_subset der_f  => ? /gt_eqF ->.
  + exact: cvg_dnbhs_at_right.
- apply: (left_derivative_limit df).
  + exact: cvg_at_left_filter cfa.
  + by apply: within_subset der_f => ? /lt_eqF ->.
  + exact: cvg_dnbhs_at_left.
Qed.

End derivative_limit_thm.
