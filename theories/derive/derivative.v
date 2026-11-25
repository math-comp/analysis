(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import poly sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau differential.

(**md**************************************************************************)
(* # Derivatives                                                              *)
(*                                                                            *)
(* See also `differential.v` for shared documentation (e.g., about            *)
(* automation).                                                               *)
(*                                                                            *)
(* Parsable notations (in all of the following, f is not supposed to be       *)
(* differentiable):                                                           *)
(*                                                                            *)
(* `'D_v f`                                                                   *)
(* : the directional derivative of `f` along `v`                              *)
(*                                                                            *)
(* `` f^`() ``                                                                *)
(* : the derivative of `f` of domain `R`                                      *)
(*                                                                            *)
(* `` f^`(n) ``                                                               *)
(* : the `n`th derivative of `f` of domain `R`                                *)
(*                                                                            *)
(* `derivable f a v`                                                          *)
(* : the function `f` is derivable at a with direction `v`                    *)
(* : The type of `f` is `V -> W` with `V W : normedModType R` and             *)
(* : `R : numFieldType`                                                       *)
(*                                                                            *)
(* `is_derive x v f df`                                                       *)
(* : the derivative of a function `f` at point `x` along `v` is `df` and `f`  *)
(* : is derivable at `x` along `v`                                            *)
(*                                                                            *)
(* Naming convention in this directory:                                       *)
(* - lemmas of the form `... -> derivable f x v` are named `derivable*`       *)
(*   (e.g., `derivableV`, `derivableM`)                                       *)
(*   or `*derivable` (e.g., `diff_derivable`)                                 *)
(* - lemmas of the form `D_v f x = ...` are named `derive*`                   *)
(*   (e.g., `deriveVP, `deriveM`)                                             *)
(* - lemmas of the form ``f^`() x = ...`` are named `derive1*`                *)
(*   (e.g., `derive1_cst`, `derive1_comp`)                                    *)
(* - lemmas of the form `... -> is_derive x v f df` are named `is_derive*`    *)
(*   (e.g., `is_derive_cst`)                                                  *)
(*                                                                            *)
(* It is worth mentioning that every differentiable function is derivable     *)
(* via the lemma `diff_derivable` and that a function is differentiable iff   *)
(* it is derivable in the case of functions from $\mathbb{R}$ to a normed     *)
(* module, via the lemma `derivable1_diffP`.                                  *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "''D_' v f" (at level 10, v, f at next level,
  format "''D_' v  f").
Reserved Notation "''D_' v f c" (at level 10, v, f at next level,
  format "''D_' v  f  c"). (* printing *)
Reserved Notation "f ^` ()" (format "f ^` ()").
Reserved Notation "f ^` ( n )" (format "f ^` ( n )").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DifferentialR.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.

Definition derive (f : V -> W) a v :=
  lim ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ 0^').

Local Notation "''D_' v f" := (derive f ^~ v).
Local Notation "''D_' v f c" := (derive f c v). (* printing *)

Definition derivable (f : V -> W) a v :=
  cvg ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ 0^').

Class is_derive (a v : V) (f : V -> W) (df : W) := DeriveDef {
  ex_derive : derivable f a v;
  derive_val : 'D_v f a = df
}.

Lemma derivable_nbhs (f : V -> W) a v :
  derivable f a v ->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (nbhs 0) id.
Proof.
move=> df; apply/eqaddoP => _/posnumP[e].
rewrite -nbhs_nearE nbhs_simpl /= dnbhsE; split; last first.
  apply/principal_filterP.
  rewrite opprD -![(_ + _ : _ -> _) _]/(_ + _) scale0r add0r.
  by rewrite addrCA addKr normrN scale0r !normr0 mulr0.
have /eqolimP := df.
move=> /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]).
apply: filter_app; rewrite /= !near_simpl near_withinE; near=> h => hN0.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|1|]normr1 mulr1 => dfv.
rewrite addrA -[X in X + _]scale1r -(@mulVf _ h) //.
rewrite mulrC -scalerA -scalerBr normrZ.
by rewrite -ler_pdivlMl ?normr_gt0// mulrC mulfK ?normr_eq0.
Unshelve. all: by end_near. Qed.

Lemma derivable_nbhsP (f : V -> W) a v :
  derivable f a v <->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (nbhs 0) id.
Proof.
split; first exact: derivable_nbhs.
move=> df; apply/cvg_ex; exists ('D_v f a).
apply/(@eqolimP _ _ _ _ (dnbhs_filter_on _))/eqaddoP => _/posnumP[e].
have /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]) := df.
rewrite /= !(near_simpl, near_withinE); apply: filter_app; near=> h.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|1|]normr1 mulr1 addrA => dfv hN0.
rewrite -[X in _ - X]scale1r -(@mulVf _ h) //.
rewrite -scalerA -scalerBr normrZ normfV ler_pdivrMl ?normr_gt0 //.
by rewrite mulrC.
Unshelve. all: by end_near. Qed.

Lemma derivable_nbhsx (f : V -> W) a v :
  derivable f a v -> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (nbhs 0)) h.
Proof.
move=> /derivable_nbhs; rewrite funeqE => df.
by apply: eqaddoEx => h; have /= := df h; rewrite addrC => ->.
Qed.

Lemma derivable_nbhsxP (f : V -> W) a v :
  derivable f a v <-> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (nbhs 0)) h.
Proof.
split; first exact: derivable_nbhsx.
move=> df; apply/derivable_nbhsP; apply/eqaddoE; rewrite funeqE => h.
by rewrite /= addrC df.
Qed.

Lemma derivable0 (f : V -> W) (x : V) : derivable f x 0.
Proof.
apply: (is_cvg_near_cst 0) => //=.
near=> h.
by rewrite scaler0 add0r subrr scaler0.
Unshelve. all: by end_near. Qed.

Lemma derive0 (f : V -> W) (x : V) : 'D_0 f x = 0.
Proof.
apply/lim_near_cst => //=.
near=> h.
by rewrite scaler0 add0r subrr scaler0.
Unshelve. all: by end_near. Qed.

Lemma is_derive0 (f : V -> W) (x : V) : is_derive x 0 f 0.
Proof. by split; [exact/derivable0|rewrite derive0]. Qed.

End DifferentialR.

Notation "''D_' v f" := (derive f ^~ v).
Notation "''D_' v f c" := (derive f c v). (* printing *)
#[global] Hint Extern 0 (derivable _ _ _) => solve[apply: ex_derive] : core.

Section DifferentialR_numFieldType.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable f a -> 'D_v f a = 'd f a v.
Proof.
rewrite /derive => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=.
  rewrite funeqE=> h.
  by rewrite -[_ - _]addrA addrC subrKA scalerDr addrC linearZ scalerA /g.
apply: cvg_lim => //.
pose g1 : R -> W := fun h => (h^-1 * h) *: 'd f a v.
pose g2 : R -> W := fun h : R => h^-1 *: k (h *: v ).
rewrite (_ : g = g1 + g2) ?funeqE//; apply: cvgD0.
  apply: cvg1Z => //= X [e e0].
  rewrite /ball_ /= => eX.
  apply/nbhs_ballP.
  by exists e => //= x _ x0; apply eX; rewrite mulVf//= subrr normr0.
rewrite /g2.
have [->|v0] := eqVneq v 0.
  rewrite (_ : (fun _ => _) = cst 0)//.
  by rewrite funeqE => ?; rewrite scaler0 /k littleo_lim0 // scaler0.
apply/cvgrPdist_lt => e e0.
rewrite nearE /=; apply/nbhs_ballP.
have /(littleoP [littleo of k]) /nbhs_ballP[i i0 Hi] : 0 < e / (2 * `|v|).
  by rewrite divr_gt0 // pmulr_rgt0 // normr_gt0.
exists (i / `|v|); first by rewrite /= divr_gt0 // normr_gt0.
move=> /= j; rewrite /ball /= /ball_ add0r normrN.
rewrite ltr_pdivlMr ?normr_gt0 // => jvi j0.
rewrite add0r normrN normrZ -ltr_pdivlMl ?normr_gt0 ?invr_neq0 //.
have /Hi/le_lt_trans -> // : ball 0 i (j *: v).
  by rewrite -ball_normE/= add0r normrN (le_lt_trans _ jvi) // normrZ.
rewrite -(mulrC e) -mulrA -ltr_pdivlMl // mulKf ?gt_eqF// normfV invrK.
rewrite ltr_pdivrMl; first by rewrite pmulr_rgt0 // normr_gt0.
rewrite normrZ mulrC -mulrA.
by rewrite ltr_pMl ?ltr1n // pmulr_rgt0 ?normm_gt0 // normr_gt0.
Qed.

End DifferentialR_numFieldType.

Section DifferentialR2.
Context {d : filter_display} {R : numFieldType}.
Implicit Type V : normedModType d R.

Definition derive1 V (f : R -> V) (a : R) :=
  lim ((fun h => h^-1 *: (f (h + a) - f a)) @ 0^').

Local Notation "f ^` ()" := (derive1 f).

Lemma derive1E V (f : R -> V) a : f^`() a = 'D_1 f a.
Proof.
rewrite /derive1 /derive.
set df := (fun _ : R => _); set df' := (fun _ : R => _).
suff -> : df = df' by []; rewrite funeqE=> h.
by rewrite /df /df' /= [h%:A](mulr1).
Qed.

(* Is it necessary? *)
Lemma derive1E' V f a : differentiable (f : R -> V) a ->
  f^`() a = 'd f a 1.
Proof. by move=> ?; rewrite derive1E deriveE. Qed.

Definition derive1n V n (f : R -> V) := iter n (@derive1 V) f.

Local Notation "f ^` ( n )" := (derive1n n f).

Lemma derive1n0 V (f : R -> V) : f^`(0) = f.
Proof. by []. Qed.

Lemma derive1n1 V (f : R -> V) : f^`(1) = f^`().
Proof. by []. Qed.

Lemma derive1nS V (f : R -> V) n : f^`(n.+1) = f^`(n)^`().
Proof. by []. Qed.

Lemma derive1Sn V (f : R -> V) n : f^`(n.+1) = f^`()^`(n).
Proof. exact: iterSr. Qed.

Lemma derive1Dn V (f : R -> V) m n : f^`(n + m) = f^`(m)^`(n).
Proof. by rewrite /derive1n iterD. Qed.

End DifferentialR2.
Notation "f ^` ()" := (derive1 f) : classical_set_scope.
Notation "f ^` ( n )" := (derive1n n f) : classical_set_scope.

Section DeriveRU.
Context {d} {R : numFieldType} {U : normedModType d R}.
Implicit Types f : R -> U.

Let der1 f x : derivable f x 1 ->
  f \o shift x = cst (f x) + ( *:%R^~ (f^`() x)) +o_ 0 id.
Proof.
move=> df; apply/eqaddoE; have /derivable_nbhsP := df.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
by rewrite derive1E =>->.
Qed.

Lemma deriv1E f x : derivable f x 1 -> 'd f x = ( *:%R^~ (f^`() x)) :> (R -> U).
Proof.
pose dh (h : R) := h *: (f^`() x)%classic.
move=> df; have lin_scal : linear dh by move=> ? ? ?
  ; rewrite /dh scalerDl scalerA.
pose scallM := GRing.isLinear.Build _ _ _ _ _ lin_scal.
pose scalL : {linear _ -> _} := HB.pack dh scallM.
rewrite -/dh -[dh]/(scalL : _ -> _).
by apply: diff_unique; [apply: scalel_continuous|apply: der1].
Qed.

Lemma diff1E f x :
  differentiable f x -> 'd f x = (fun h => h *: f^`()%classic x) :> (R -> U).
Proof.
pose dh (h : R) := h *: 'd f x 1.
move=> df; have lin_scal : linear dh by move=> ? ? ?
  ; rewrite /dh scalerDl scalerA.
pose scallM := GRing.isLinear.Build _ _ _ _ _ lin_scal.
pose scalL : {linear _ -> _} := HB.pack dh scallM.
have -> : (fun h => h *: f^`()%classic x) = scalL by rewrite derive1E'.
apply: diff_unique; first exact: scalel_continuous.
apply/eqaddoE; have /diff_locally -> := df; congr (_ + _ + _).
by rewrite funeqE => h /=; rewrite -{1}[h]mulr1 linearZ.
Qed.

Lemma derivable1_diffP f x : derivable f x 1 <-> differentiable f x.
Proof.
split=> dfx.
  by apply/diff_locallyP; rewrite deriv1E //; split;
    [apply: scalel_continuous|apply: der1].
apply/derivable_nbhsP/eqaddoE.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
by have /diff_locally := dfx; rewrite diff1E // derive1E =>->.
Qed.

End DeriveRU.

Section DeriveVW.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.
Implicit Types f : V -> W.

Lemma derivable1P f x v :
  derivable f x v <-> derivable (fun h : R => f (h *: v + x)) 0 1.
Proof.
rewrite /derivable; set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Lemma diff_derivable f a v : differentiable f a -> derivable f a v.
Proof.
move=> dfa; apply/derivable1P/derivable1_diffP.
by apply: differentiable_comp; rewrite ?scale0r ?add0r.
Qed.

End DeriveVW.
