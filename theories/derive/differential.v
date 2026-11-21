(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import poly sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau.

(**md**************************************************************************)
(* # Differentiation                                                          *)
(*                                                                            *)
(* This file provides basics of a theory of differentiation. It includes the  *)
(* standard rules of differentiation (differential of a sum, of a product, of *)
(* exponentiation, of the inverse, etc.).                                     *)
(*                                                                            *)
(* Parsable notations (in all of the following, f is not supposed to be       *)
(* differentiable):                                                           *)
(*                                                                            *)
(* `'d f x`                                                                   *)
(* : the differential of a function `f` at a point `x`                        *)
(*                                                                            *)
(* `differentiable f x`                                                       *)
(* : the function `f` is differentiable at a point `x`                        *)
(*                                                                            *)
(* `'D_v f`                                                                   *)
(* : the directional derivative of `f` along `v`                              *)
(*                                                                            *)
(* `derivable f a v`                                                          *)
(* : the function `f` is derivable at a with direction `v`                    *)
(* : The type of `f` is `V -> W` with `V W : normedModType R` and             *)
(* : `R : numFieldType`                                                       *)
(*                                                                            *)
(* `` f^`() ``                                                                *)
(* : the derivative of `f` of domain `R`                                      *)
(*                                                                            *)
(* `` f^`(n) ``                                                               *)
(* : the `n`th derivative of `f` of domain `R`                                *)
(*                                                                            *)
(* `is_derive x v f df`                                                       *)
(* : the derivative of a function `f` at point `x` along `v` is `df` and `f`  *)
(* : is derivable at `x` along `v`                                            *)
(*                                                                            *)
(* `is_diff x f df`                                                           *)
(* : the differential of a function `f` at point `x` is `df` and `f` is       *)
(* : differentiable at point `x`                                              *)
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
(* - lemmas of the form `... -> is_diff x f df` are named `is_diff*`          *)
(*   (e.g., `is_diff_cst`)                                                    *)
(*                                                                            *)
(* # Automatic derivation and differentiation with `is_diff` and `is_derive`  *)
(*                                                                            *)
(* Statements of the form `is_diff` and `is_derive` are typeclasses           *)
(* registered via `Instance` declarations with a proof `ex_derive`/`ex_diff`  *)
(* of derivability/differentiability of the expression and a proof            *)
(* `derive_val`/`diff_val` of the value of the derivative/differential        *)
(* of the function; so that typeclass resolution can automatically synthesize *)
(* the differential/derivative of a compound expression from the              *)
(* differentials/derivatives of its parts, instead of requiring the user to   *)
(* prove and compute derivatives by hand.                                     *)
(*                                                                            *)
(* ## Lemmas of the form `is_derive` and `is_diff`                            *)
(*                                                                            *)
(* For a compound expression, e.g., built from f and g, state the goal with   *)
(* the expected derivative/differential and let typeclass resolution fill the *)
(* proof by `apply: is_derive_eq` or `apply: is_diff_eq`:                     *)
(*  ```coq                                                                    *)
(*  Lemma is_derive_example (W : normedModType R)                             *)
(*    (t : R^o) (f g : R^o -> W) (f' g' : W) v :                              *)
(*    is_derive t v f f' ->                                                   *)
(*    is_derive t v g g' ->                                                   *)
(*    is_derive t v (f + g) (f' + g').                                        *)
(* Proof. move => is_der_f is_der_g. by apply: is_derive_eq. Qed.             *)
(*  ```                                                                       *)
(*                                                                            *)
(* The proof is inferred structurally by chaining declared `is_derive` or     *)
(* `is_diff` instances matching the pattern of the goal stated.               *)
(*                                                                            *)
(* To verify if a given expression is derivable or differentiable, you can    *)
(* use `apply: ex_derive` or `apply: ex_diff`, given the right                *)
(* `is_derive _` or `is_diff _` instances are defined such as:                *)
(* ```coq                                                                     *)
(* Hypothesis derivable_f : forall t, derivable f t 1.                        *)
(* Hypothesis derivable_h : forall t, derivable h t 1.                        *)
(* Local Instance is_derive_f t : is_derive t 1 f ('D_1 f t).                 *)
(* by apply: derivableP. Qed.                                                 *)
(* Local Instance is_derive_h t : is_derive t 1 h ('D_1 h t).                 *)
(* by apply: derivableP. Qed.                                                 *)
(*                                                                            *)
(* Lemma is_derivable_example (t : R^o) : derivable (f + h) t 1.              *)
(* Proof. apply/ex_derive. Qed.                                               *)
(* ```                                                                        *)
(*                                                                            *)
(* To verify the value of a given function you can apply `derive_val` or      *)
(* `diff_val`, given the right `is_derive/diff` instances are defined, e.g.:  *)
(* ```coq                                                                     *)
(*    Lemma is_derive_val_example t :                                         *)
(*    'D_1 (f + h) t = 'D_1 f t + 'D_1 h t.                                   *)
(*    Proof. by apply/derive_val. Qed.                                        *)
(* ```                                                                        *)
(*                                                                            *)
(* It is worth mentioning that every differentiable function is derivable     *)
(* via the lemma `diff_derivable` and that a function is differentiable iff   *)
(* it is derivable in the case of functions from $\mathbb{R}$ to a normed     *)
(* module, via the lemma `derivable1_diffP`.                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Reserved Notation "''d' f x" (at level 0, f at level 0, x at level 0,
  format "''d'  f  x").
Reserved Notation "'is_diff' F" (at level 0, F at level 0,
  format "'is_diff'  F").
Reserved Notation "''D_' v f" (at level 10, v, f at next level,
  format "''D_' v  f").
Reserved Notation "''D_' v f c" (at level 10, v, f at next level,
  format "''D_' v  f  c"). (* printing *)
Reserved Notation "f ^` ()" (format "f ^` ()").
Reserved Notation "f ^` ( n )" (format "f ^` ( n )").

Section Differential.
Context {d} {K : numDomainType} {V : normedModType d K}
  {d'} {W : normedModType d' K}.

Definition diff (F : filter_on V) (_ : phantom (set_system V) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => continuous df /\ forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).

Local Notation "''d' f x" := (@diff _ (Phantom _ (nbhs x)) f).

Fact diff_key : forall T, T -> unit. Proof. by constructor. Qed.
Variant differentiable_def (f : V -> W) (x : filter_on V)
  (phF : phantom (set_system V) x) : Prop := DifferentiableDef of
  (continuous ('d f x) /\
  f = cst (f (lim x)) + 'd f x \o center (lim x) +o_x (center (lim x))).

Local Notation differentiable f F :=
  (@differentiable_def f _ (Phantom _ (nbhs F))).

Class is_diff_def (x : filter_on V) (Fph : phantom (set_system V) x) (f : V -> W)
  (df : V -> W) := DiffDef {
    ex_diff : differentiable f x ;
    diff_val : 'd f x = df :> (V -> W)
  }.
Hint Mode is_diff_def - - ! - : typeclass_instances.

Lemma diffP (F : filter_on V) (f : V -> W) :
  differentiable f F <->
  continuous ('d f F) /\
  (forall x, f x = f (lim F) + 'd f F (x - lim F) +o_(x \near F) (x - lim F)).
Proof. by split=> [[] |]; last constructor; rewrite funeqE. Qed.

Lemma diff_continuous (x : filter_on V) (f : V -> W) :
  differentiable f x -> continuous ('d f x).
Proof. by move=> /diffP []. Qed.
(* We should have a continuous class or structure *)
Hint Extern 0 (continuous _) => solve[apply: diff_continuous] : core.

Lemma diffE (F : filter_on V) (f : V -> W) :
  differentiable f F ->
  forall x, f x = f (lim F) + 'd f F (x - lim F) +o_(x \near F) (x - lim F).
Proof. by move=> /diffP []. Qed.

Lemma littleo_center0 (x : V) (f : V -> W) (e : V -> V) :
  [o_x e of f] = [o_ 0 (e \o shift x) of f \o shift x] \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP => _/posnumP[eps].
  rewrite [\forall x \near _, _ <= _](near_shift x) sub0r; near=> y.
  by rewrite /= subrK; near: y; have /eqoP := littleo_eqo g; apply.
rewrite insubF //; apply/asboolP => fe; apply: Nfe => _/posnumP[eps].
by rewrite [\forall x \near _, _ <= _](near_shift 0) subr0; apply: fe.
Unshelve. all: by end_near. Qed.

End Differential.

Section Differential_numFieldType.
Context {d} {K : numFieldType (*TODO: to numDomainType?*)}
  {V : normedModType d K} {d'} {W : normedModType d' K}.

(* duplicate from Section Differential *)
Local Notation differentiable f F :=
  (@differentiable_def _ _ _ _ _ f _ (Phantom _ (nbhs F))).
Local Notation "''d' f x" := (@diff _ _ _ _ _ _ (Phantom _ (nbhs x)) f).
Hint Extern 0 (continuous _) => solve[now apply: diff_continuous] : core.

Lemma diff_locallyxP (x : V) (f : V -> W) :
  differentiable f x <-> continuous ('d f x) /\
  forall h, f (h + x) = f x + 'd f x h +o_(h \near 0) h.
Proof.
split=> [dxf|[dfc dxf]].
  split => //; apply: eqaddoEx => h; have /diffE -> := dxf.
  rewrite lim_id // addrK; congr (_ + _); rewrite littleo_center0 /= addrK.
  by congr ('o); rewrite funeqE => k /=; rewrite addrK.
apply/diffP; split=> //; apply: eqaddoEx; move=> y.
rewrite lim_id // -[in LHS](subrK x y) dxf; congr (_ + _).
rewrite -(comp_centerK x id) -[X in the_littleo _ _ _ X](comp_centerK x).
by rewrite -[_ (y - x)]/((_ \o (center x)) y) -littleo_center0.
Qed.

Lemma diff_locallyx (x : V) (f : V -> W) : differentiable f x ->
  forall h, f (h + x) = f x + 'd f x h +o_(h \near 0) h.
Proof. by move=> /diff_locallyxP []. Qed.

Lemma diff_locallyxC (x : V) (f : V -> W) : differentiable f x ->
  forall h, f (x + h) = f x + 'd f x h +o_(h \near 0) h.
Proof. by move=> ?; apply/eqaddoEx => h; rewrite [x + h]addrC diff_locallyx. Qed.

Lemma diff_locallyP (x : V) (f : V -> W) :
  differentiable f x <->
  continuous ('d f x) /\ (f \o shift x = cst (f x) + 'd f x +o_ 0 id).
Proof. by apply: iff_trans (diff_locallyxP _ _) _; rewrite funeqE. Qed.

Lemma diff_locally (x : V) (f : V -> W) : differentiable f x ->
  (f \o shift x = cst (f x) + 'd f x +o_ 0 id).
Proof. by move=> /diff_locallyP []. Qed.

End Differential_numFieldType.

Notation "''d' f F" := (@diff _ _ _ _ _ _ (Phantom _ (nbhs F)) f).
Notation differentiable f F :=
  (@differentiable_def _ _ _ _ _ f _ (Phantom _ (nbhs F))).

Notation "'is_diff' F" := (is_diff_def (Phantom _ (nbhs F))).
#[global] Hint Extern 0 (differentiable _ _) => solve[apply: ex_diff] : core.
#[global] Hint Extern 0 ({for _, continuous _}) =>
  solve[now apply: diff_continuous] : core.

Lemma differentiableP (R : numDomainType) d (V : normedModType d R)
  d' (W : normedModType d' R) (f : V -> W) x :
  differentiable f x -> is_diff x f ('d f x).
Proof. by move=> ?; apply: DiffDef. Qed.

Section DifferentialR.
Context {d} {R : numFieldType} {V : normedModType d R}
  {d'} {W : normedModType d' R}.

(* split in multiple bits:
- a linear map which is locally bounded is a little o of 1
- the identity is a littleo of 1
*)
Lemma differentiable_continuous (x : V) (f : V -> W) :
  differentiable f x -> {for x, continuous f}.
Proof.
move=> /diff_locallyP [dfc]; rewrite -addrA.
rewrite (littleo_bigO_eqo (cst (1 : R))).
  by apply/eqOP; near=> k; rewrite /cst [`|1|]normr1 mulr1; near do by [].
rewrite addfo; last by move=> /eqolim; rewrite cvg_comp_shift add0r.
by apply/eqolim0P; apply: (cvg_trans (dfc 0)); rewrite linear0.
Unshelve. all: by end_near. Qed.

Section littleo_lemmas.
Context {d1} {X : normedModType d1 R}
  {d2} {Y : normedModType d2 R} {d3} {Z : normedModType d3 R}.

Lemma normm_littleo x (f : X -> Y) : `| [o_(x \near x) (1 : R) of f x]| = 0.
Proof.
rewrite /cst /=; have [e /(_ (`|e x|/2) _)/nbhs_singleton /=] := littleo.
rewrite pmulr_lgt0 // [`|1|]normr1 mulr1 [leLHS]splitr gerDr pmulr_lle0 //.
by move=> /implyP; case : real_ltgtP; rewrite ?realE ?normrE //= lexx.
Qed.

Lemma littleo_lim0 (f : X -> Y) (h : _ -> Z) (x : X) :
  f @ x --> 0 -> [o_x f of h] x = 0.
Proof.
move/eqolim0P => ->; have [k /(_ _ [gt0 of 1 : R])/=] := littleo.
by move=> /nbhs_singleton; rewrite mul1r normm_littleo normr_le0 => /eqP.
Qed.

End littleo_lemmas.

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)
(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential being b *: idfun is locally bounded *)
(* and thus a littleo of 1, and so is id *)
(* This can be generalized to any dimension *)
Lemma diff_locally_converse_part1 (f : R -> R) (a b x : R) :
  f \o shift x = cst a + b *: idfun +o_ 0 id -> f x = a.
Proof.
rewrite funeqE => /(_ 0) /=; rewrite add0r => ->.
by rewrite -[LHS]/(_ 0 + _ 0 + _ 0) /cst [X in a + X]scaler0 littleo_lim0 ?addr0.
Qed.

End diff_locally_converse_tentative.

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

Section DifferentialR3.
Context {R : numFieldType}.
Generalizable Variable d.

Fact dcst `{V : normedModType d R} `{W : normedModType d' R} (a : W) (x : V) :
  continuous (0 : V -> W) /\
  cst a \o shift x = cst (cst a x) + \0 +o_ 0 id.
Proof.
split; first exact: cst_continuous.
apply/eqaddoE; rewrite addr0 funeqE => ? /=; rewrite -[LHS]addr0; congr (_ + _).
by rewrite littleoE; first exact: littleo0_subproof.
Qed.

Fact dadd `{V : normedModType d R} `{W : normedModType d' R} (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  continuous ('d f x \+ 'd g x) /\
  (f + g) \o shift x = cst ((f + g) x) + ('d f x \+ 'd g x) +o_ 0 id.
Proof.
move=> df dg; split => [?|]; do ?exact: continuousD.
apply/(@eqaddoE _ _ R); rewrite funeqE => y /=.
by rewrite !fctE ![_ (_ + x)]diff_locallyx// addrACA addox addrACA.
Qed.

Fact dopp `{V : normedModType d R} `{W : normedModType d' R} (f : V -> W) x :
  differentiable f x -> continuous (- ('d f x : V -> W)) /\
  (- f) \o shift x = cst (- f x) \- 'd f x +o_ 0 id.
Proof.
move=> df; split; first by move=> ?; apply: continuousN.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(- f) _]/(- (_ _)) diff_locallyx// !opprD oppox.
Qed.

Lemma is_diff_eq `{V : normedModType d R} `{W : normedModType d' R}
  (f f' g : V -> W) (x : V) :
  is_diff x f f' -> f' = g -> is_diff x f g.
Proof. by move=> ? <-. Qed.

Fact dscale `{V : normedModType d R} `{W : normedModType d' R}
  (f : V -> W) k x :
  differentiable f x -> continuous (k \*: 'd f x) /\
  (k *: f) \o shift x = cst ((k *: f) x) + k \*: 'd f x +o_ 0 id.
Proof.
move=> df; split; first by move=> ?; apply: continuousZl_tmp.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(k *: f) _]/(_ *: _) diff_locallyx // !scalerDr scaleox.
Qed.

(* NB: could be generalized with K : absRingType instead of R; DONE? *)
Fact dscalel `{V : normedModType d R} `{W : normedModType d' R}
  (k : V -> R) (f : W) x :
  differentiable k x ->
  continuous (fun z : V => 'd k x z *: f) /\
  (fun z => k z *: f) \o shift x =
    cst (k x *: f) + (fun z => 'd k x z *: f) +o_ 0 id.
Proof.
move=> df; split.
  move=> ?; exact/continuousZr_tmp/diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite diff_locallyx //= !scalerDl scaleolx.
Qed.

Fact dlin `{V : normedModType d R} `{W : normedModType d' R}
    (f : {linear V -> W}) x :
  continuous f -> f \o shift x = cst (f x) + f +o_ 0 id.
Proof.
move=> df; apply: eqaddoE; rewrite funeqE => y /=.
rewrite linearD addrC -[LHS]addr0; congr (_ + _).
by rewrite littleoE; first exact: littleo0_subproof. (*fixme*)
Qed.

(* TODO: generalize *)
Lemma compoO_eqo `{U : normedModType d1 R} `{V : normedModType d2 R}
  `{W : normedModType d3 R} (f : U -> V) (g : V -> W) :
  [o_ 0 id of g] \o [O_ 0 id of f] =o_ 0 id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ 0 id of f]].
have := littleoP [littleo of [o_ 0 id of g]].
move=>  /(_ (e%:num / k%:num)) /(_ _) /nbhs_ballP [//|_ /posnumP[e'] he'].
apply: filter_app; near=> x => leOxkx; apply: le_trans (he' _ _) _; last first.
  by rewrite -ler_pdivlMl // invf_div mulrA divfK.
by rewrite -ball_normE /= distrC subr0 (le_lt_trans leOxkx) // -ltr_pdivlMl.
Unshelve. all: by end_near. Qed.

Lemma compoO_eqox `{U : normedModType d1 R} `{V : normedModType d2 R}
  `{W : normedModType d3 R} (f : U -> V) (g : V -> W) :
  forall x : U, [o_ 0 id of g] ([O_ 0 id of f] x) =o_(x \near 0) x.
Proof. by move=> x; rewrite -[LHS]/((_ \o _) x) compoO_eqo. Qed.

(* TODO: generalize *)
Lemma compOo_eqo `{U : normedModType d1 R} `{V : normedModType d2 R}
  `{W : normedModType d3 R} (f : U -> V) (g : V -> W) :
  [O_ 0 id of g] \o [o_ 0 id of f] =o_ 0 id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ 0 id of g]].
move=> /nbhs_ballP [_ /posnumP[e'] he'].
have ekgt0 : e%:num / k%:num > 0 by [].
have /(_ _ ekgt0) := littleoP [littleo of [o_ 0 id of f]].
apply: filter_app; near=> x => leoxekx; apply: le_trans (he' _ _) _; last first.
  by rewrite -ler_pdivlMl // mulrA [_^-1 * _]mulrC.
by rewrite -ball_normE /= distrC subr0 (le_lt_trans leoxekx)// -ltr_pdivlMl //.
Unshelve. all: by end_near. Qed.

End DifferentialR3.

Section DifferentialR3_numFieldType.
Context {R : numFieldType}.
Generalizable Variables d.

Lemma littleo_linear0 `(V : normedModType d R) `(W : normedModType d' R)
  (f : {linear V -> W}) :
  (f : V -> W) =o_ 0 id -> f = cst 0 :> (V -> W).
Proof.
move/eqoP => oid.
rewrite funeqE => x; apply/eqP; have [|xn0] := real_le0P (normr_real x).
  by rewrite normr_le0 => /eqP ->; rewrite linear0.
rewrite -normr_le0 -(mul0r `|x|) -ler_pdivrMr //.
apply/ler_gtP => _ /posnumP[e]; rewrite ler_pdivrMr //.
have /oid /nbhs_ballP [_ /posnumP[e'] dfe] := [elaborate gt0 e].
set k := ((e'%:num / 2) / (PosNum xn0)%:num)^-1.
rewrite -{1}(@scalerKV _ _ k _ x) /k // linearZZ normrZ.
rewrite -ler_pdivlMl; first by rewrite gtr0_norm.
rewrite mulrCA (@le_trans _ _ (e%:num * `|k^-1 *: x|)) //; last first.
  by rewrite ler_pM // normrZ normfV.
apply: dfe; rewrite -ball_normE /= sub0r normrN normrZ.
rewrite invrK -ltr_pdivlMr // ger0_norm // ltr_pdivrMr //.
by rewrite divfK ?lt0r_neq0// [ltRHS]splitr ltrDl.
Qed.

Lemma diff_unique `(V : normedModType d R) `(W : normedModType d' R)
  (f : V -> W) (df : {linear V -> W}) x :
  continuous df -> f \o shift x = cst (f x) + df +o_ 0 id ->
  'd f x = df :> (V -> W).
Proof.
move=> dfc dxf; apply/subr0_eq; rewrite -[LHS]/(_ \- _).
apply/littleo_linear0/eqoP/eq_some_oP => /=; rewrite funeqE => y /=.
have hdf h : (f \o shift x = cst (f x) + h +o_ 0 id) ->
    h = f \o shift x - cst (f x) +o_ 0 id.
  move=> hdf; apply: eqaddoE.
  rewrite hdf addrAC -!addrA addrC !addrA subrK.
  rewrite -[LHS]addr0 -addrA; congr (_ + _).
  by apply/eqP; rewrite eq_sym addrC addr_eq0 oppo.
rewrite (hdf _ dxf).
suff /diff_locally /hdf -> : differentiable f x.
  by rewrite [_ - _ + _]addrC addrKA oppox addox.
apply/diffP => /=.
apply: (@getPex _ (fun (df : {linear V -> W}) => continuous df /\
  forall y, f y = f (lim (nbhs x)) + df (y - lim (nbhs x))
                  +o_(y \near x) (y - lim (nbhs x)))).
exists df; split=> //; apply: eqaddoEx => z.
rewrite (hdf _ dxf) !addrA lim_id // /(_ \o _) /= subrK [f _ + _]addrC addrK.
rewrite -addrA -[LHS]addr0; congr (_ + _).
apply/eqP; rewrite eq_sym addrC addr_eq0 oppox; apply/eqP.
rewrite [in LHS]littleo_center0 (comp_centerK x id).
by rewrite -[- _ in RHS](comp_centerK x).
Qed.

Lemma diff_cst `(V : normedModType d R) `(W : normedModType d' R) a x :
  ('d (cst a) x : V -> W) = 0.
Proof. by apply/diff_unique; have [] := dcst a x. Qed.

Lemma differentiable_cst `(V : normedModType d R) `(W : normedModType d' R)
  (a : W) (x : V) :
  differentiable (cst a) x.
Proof. by apply/diff_locallyP; rewrite diff_cst; have := dcst a x. Qed.

Global Instance is_diff_cst `(V : normedModType d R) `(W : normedModType d' R)
  (a : W) (x : V) :
  is_diff x (cst a) 0.
Proof. exact: DiffDef (differentiable_cst _ _) (diff_cst _ _). Qed.

Lemma diffD `(V : normedModType d R) `(W : normedModType d' R)
  (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  'd (f + g) x = 'd f x \+ 'd g x :> (V -> W).
Proof. by move=> df dg; apply/diff_unique; have [] := dadd df dg. Qed.

Lemma differentiableD `(V : normedModType d R) `(W : normedModType d' R)
  (f g : V -> W) x :
  differentiable f x -> differentiable g x -> differentiable (f + g) x.
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diffD; have := dadd df dg.
Qed.

Global Instance is_diffD `(V : normedModType d R) `(W : normedModType d' R)
  (f g df dg : V -> W) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f + g) (df + dg).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiableD.
by rewrite diffD; last (congr (_ + _); apply: diff_val).
Qed.

Lemma differentiable_sum `(V : normedModType d R) `(W : normedModType d' R)
  n (f : 'I_n -> V -> W) (x : V) :
  (forall i, differentiable (f i) x) -> differentiable (\sum_(i < n) f i) x.
Proof.
by elim/big_ind : _ => // ? ? g h ?; apply: differentiableD; [exact:g|exact:h].
Qed.

Lemma diffN `(V : normedModType d R) `(W : normedModType d' R) (f : V -> W) x :
  differentiable f x -> 'd (- f) x = - ('d f x : V -> W) :> (V -> W).
Proof.
move=> df; rewrite -[RHS]/(@GRing.opp _ \o _); apply/diff_unique;
by have [] := dopp df.
Qed.

Lemma differentiableN `(V : normedModType d R) `(W : normedModType d' R)
  (f : V -> W) x :
  differentiable f x -> differentiable (- f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffN //; have := dopp df.
Qed.

Global Instance is_diffN `(V : normedModType d R) `(W : normedModType d' R)
  (f df : V -> W) x :
  is_diff x f df -> is_diff x (- f) (- df).
Proof.
move=> dfx; apply: DiffDef; first exact: differentiableN.
by rewrite diffN // diff_val.
Qed.

Global Instance is_diffB `(V : normedModType d R) `(W : normedModType d' R)
  (f g df dg : V -> W) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f - g) (df - dg).
Proof. by move=> dfx dgx; apply: is_diff_eq. Qed.

Lemma diffB `(V : normedModType d R) `(W : normedModType d' R)
  (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  'd (f - g) x = 'd f x \- 'd g x :> (V -> W).
Proof.
by move=> /differentiableP df /differentiableP dg; rewrite [LHS]diff_val.
Qed.

Lemma differentiableB `(V : normedModType d R) `(W : normedModType d' R)
  (f g : V -> W) x :
  differentiable f x -> differentiable g x -> differentiable (f \- g) x.
Proof. by move=> /differentiableP df /differentiableP dg. Qed.

Lemma diffZ `(V : normedModType d R) `(W : normedModType d' R)
  (f : V -> W) k x :
  differentiable f x -> 'd (k *: f) x = k \*: 'd f x :> (V -> W).
Proof. by move=> df; apply/diff_unique; have [] := dscale k df. Qed.

Lemma differentiableZ `(V : normedModType d R) `(W : normedModType d' R)
  (f : V -> W) k x :
  differentiable f x -> differentiable (k *: f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffZ //; have := dscale k df.
Qed.

Global Instance is_diffZ `(V : normedModType d R) `(W : normedModType d' R)
  (f df : V -> W) k x :
  is_diff x f df -> is_diff x (k *: f) (k *: df).
Proof.
move=> dfx; apply: DiffDef; first exact: differentiableZ.
by rewrite diffZ // diff_val.
Qed.

Lemma diffZl `(V : normedModType d R) `(W : normedModType d' R)
  (k : V -> R) (f : W) x :
  differentiable k x ->
  'd (fun z => k z *: f) x = (fun z => 'd k x z *: f) :> (_ -> _).
Proof.
move=> df; set g := RHS; have glin : linear g.
  by move=> a u v; rewrite /g linearP /= scalerDl -scalerA.
pose glM := GRing.isLinear.Build _ _ _ _ _ glin.
pose gL : {linear _ -> _} := HB.pack g glM.
by apply: (@diff_unique _ _ _ _ _ gL); have [] := dscalel f df.
Qed.

Lemma differentiableZl `(V : normedModType d R) `(W : normedModType d' R)
  (k : V -> R) (f : W) x :
  differentiable k x -> differentiable (fun z => k z *: f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffZl //; have [] := dscalel f df.
Qed.

Lemma diff_lin `(V : normedModType d R) `(W : normedModType d' R)
  (f : {linear V -> W}) x :
  continuous f -> 'd f x = f :> (V -> W).
Proof. by move=> fcont; apply/diff_unique => //; apply: dlin. Qed.

Lemma linear_differentiable `(V : normedModType d R) `(W : normedModType d' R)
   (f : {linear V -> W}) x :
  continuous f -> differentiable f x.
Proof.
by move=> fcont; apply/diff_locallyP; rewrite diff_lin //; have := dlin x fcont.
Qed.

Global Instance is_diff_id `(V : normedModType d R) (x : V) : is_diff x id id.
Proof.
apply: DiffDef.
  by apply: (@linear_differentiable _ _ _ _ idfun) => ? //.
by rewrite (@diff_lin _ _ _ _ idfun) // => ? //.
Qed.

Global Instance is_diff_scaler `(V : normedModType d R) (k : R) (x : V) :
  is_diff x ( *:%R k) ( *:%R k).
Proof.
apply: DiffDef; first exact/linear_differentiable/scaler_continuous.
by rewrite diff_lin //; apply: scaler_continuous.
Qed.

Global Instance is_diff_scalel `(V : normedModType d R) (k : R) (x : V) :
  is_diff k ( *:%R ^~ x) ( *:%R ^~ x).
Proof.
have sx_lin : linear ( *:%R ^~ x : R -> _).
  by move=> u y z; rewrite scalerDl scalerA.
pose sxlM := GRing.isLinear.Build _ _ _ _ _ sx_lin.
pose sxL : {linear _ -> _} := HB.pack ( *:%R ^~ x) sxlM.
have -> : *:%R ^~ x = sxL by rewrite funeqE.
apply: DiffDef; first exact/linear_differentiable/scalel_continuous.
by rewrite diff_lin //; apply: scalel_continuous.
Qed.

Lemma linear_lipschitz `(V : normedModType d R) `(W : normedModType d' R)
  (f : {linear V -> W}) :
  continuous f -> exists2 k, k > 0 & forall x, `|f x| <= k * `|x|.
Proof.
move=> /(_ 0); rewrite /continuous_at linear0 => /(_ _ (nbhsx_ballx _ _ ltr01)).
move=> /nbhs_ballP [_ /posnumP[e] he]; exists (2 / e%:num) => // x.
have [|xn0] := real_le0P (normr_real x).
  by rewrite normr_le0 => /eqP->; rewrite linear0 !normr0 mulr0.
set k := 2 / e%:num * (PosNum xn0)%:num.
have kn0 : k != 0 by rewrite /k.
have abskgt0 : `|k| > 0 by rewrite normr_gt0.
rewrite -[x in leLHS](scalerKV kn0) linearZZ normrZ -ler_pdivlMl //.
suff /he : ball 0 e%:num (k^-1 *: x).
  rewrite -ball_normE /= distrC subr0 => /ltW /le_trans; apply.
  by rewrite ger0_norm /k // mulVf.
rewrite -ball_normE /= distrC subr0 normrZ.
rewrite normfV ger0_norm /k // invfM/= divfK ?gt_eqF//.
by rewrite invf_div gtr_pMr// invf_lt1// ltr1n.
Qed.

Lemma linear_eqO `(V : normedModType d R) `(W : normedModType d' R)
    (f : {linear V -> W}) :
  continuous f -> (f : V -> W) =O_ 0 id.
Proof.
move=> /linear_lipschitz [k kgt0 flip]; apply/eqO_exP; exists k => //.
exact: filterE.
Qed.

Lemma diff_eqO `(V : normedModType d R) `(W : normedModType d' R)
  (x : filter_on V) (f : V -> W) :
  differentiable f x -> ('d f x : V -> W) =O_ 0 id.
Proof. by move=> /diff_continuous /linear_eqO; apply. Qed.

Lemma compOo_eqox `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : U -> V) (g : V -> W) x :
  [O_ 0 id of g] ([o_ 0 id of f] x) =o_(x \near 0) x.
Proof. by rewrite -[LHS]/((_ \o _) x) compOo_eqo. Qed.

Fact dcomp `(U : normedModType d1 R) `(V : normedModType d2 R)
  `(W : normedModType d3 R) (f : U -> V) (g : V -> W) x :
  differentiable f x -> differentiable g (f x) ->
  continuous ('d g (f x) \o 'd f x) /\ forall y,
  g (f (y + x)) = g (f x) + ('d g (f x) \o 'd f x) y +o_(y \near 0) y.
Proof.
move=> df dg; split; first by move=> ?; apply: continuous_comp.
apply: eqaddoEx => y; rewrite diff_locallyx// -addrA diff_locallyxC// linearD.
rewrite addrA -[LHS]addrA; congr (_ + _ + _).
rewrite diff_eqO // ['d f x : _ -> _]diff_eqO //.
by rewrite {2}eqoO addOx compOo_eqox compoO_eqox addox.
Qed.

Lemma diff_comp `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : U -> V) (g : V -> W) x :
  differentiable f x -> differentiable g (f x) ->
  'd (g \o f) x = 'd g (f x) \o 'd f x :> (U -> W).
Proof. by move=> df dg; apply/diff_unique; have [? /funext] := dcomp df dg. Qed.

Lemma differentiable_comp `(U : normedModType d1 R)
  `(V : normedModType d2 R) `(W : normedModType d3 R)
  (f : U -> V) (g : V -> W) x :
  differentiable f x -> differentiable g (f x) -> differentiable (g \o f) x.
Proof.
move=> df dg; apply/diff_locallyP; rewrite diff_comp //;
by have [? /funext]:= dcomp df dg.
Qed.

Global Instance is_diff_comp `(U : normedModType d1 R)
    `(V : normedModType d2 R) `(W : normedModType d3 R)
    (f df : U -> V) (g dg : V -> W) x :
  is_diff x f df -> is_diff (f x) g dg -> is_diff x (g \o f) (dg \o df) | 99.
Proof.
move=> dfx dgfx; apply: DiffDef; first exact: differentiable_comp.
by rewrite diff_comp // !diff_val.
Qed.

Lemma bilinear_schwarz `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : {bilinear U -> V -> W}) :
  continuous (fun p => f p.1 p.2) ->
  exists2 k, k > 0 & forall u v, `|f u v| <= k * `|u| * `|v|.
Proof.
move=> /(_ 0); rewrite /continuous_at linear0r => /(_ _ (nbhsx_ballx _ _ ltr01)).
move=> /nbhs_ballP [_ /posnumP[e] he]; exists ((2 / e%:num) ^+2) => // u v.
have [|un0] := real_le0P (normr_real u).
  by rewrite normr_le0 => /eqP->; rewrite linear0l !normr0 mulr0 mul0r.
have [|vn0] := real_le0P (normr_real v).
  by rewrite normr_le0 => /eqP->; rewrite linear0r !normr0 mulr0.
rewrite -[`|u|]/((PosNum un0)%:num) -[`|v|]/((PosNum vn0)%:num).
set ku := 2 / e%:num * (PosNum un0)%:num.
set kv := 2 / e%:num * (PosNum vn0)%:num.
rewrite -[X in f X](@scalerKV _ _ ku) /ku // linearZl_LR normrZ.
rewrite gtr0_norm // -ler_pdivlMl //.
rewrite -[X in f _ X](@scalerKV _ _ kv) /kv // linearZr_LR normrZ.
rewrite gtr0_norm // -ler_pdivlMl //.
suff /he : ball 0 e%:num (ku^-1 *: u, kv^-1 *: v).
  rewrite -ball_normE /= distrC subr0 => /ltW /le_trans; apply.
  rewrite ler_pdivlMl 1?pmulr_lgt0// mulr1 ler_pdivlMl 1?pmulr_lgt0//.
  by rewrite mulrA [ku * _]mulrAC expr2.
rewrite -ball_normE /= distrC subr0.
have -> : (ku^-1 *: u, kv^-1 *: v) =
    (e%:num / 2) *: ((PosNum un0)%:num ^-1 *: u, (PosNum vn0)%:num ^-1 *: v).
  by rewrite invfM [kv ^-1]invfM invf_div -[_ *: u]scalerA -[_ *: v]scalerA.
rewrite normrZ ger0_norm // -mulrA gtr_pMr // ltr_pdivrMl // mulr1.
by rewrite prod_normE/= !normrZ !normfV !normr_id !mulVf ?gt_eqF// maxxx ltr1n.
Qed.

Lemma bilinear_eqo `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : {bilinear U -> V -> W}) :
  continuous (fun p => f p.1 p.2) -> (fun p => f p.1 p.2) =o_ (0 : U * V) id.
Proof.
move=> fc; have [_ /posnumP[k] fschwarz] := bilinear_schwarz fc.
apply/eqoP=> _ /posnumP[e]; near=> x; rewrite (le_trans (fschwarz _ _))//.
rewrite ler_pM ?pmulr_rge0 //; last by rewrite num_le_max /= lexx orbT.
rewrite -ler_pdivlMl //.
suff : `|x| <= k%:num ^-1 * e%:num.
  by apply: le_trans; rewrite num_le_max /= lexx.
near: x; apply/nbhs_le_nbhs_norm.
by exists (k%:num ^-1 * e%:num) => //= ? /=; rewrite /= distrC subr0 => /ltW.
Unshelve. all: by end_near. Qed.

Fact dbilin `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : {bilinear U -> V -> W}) p :
  continuous (fun p => f p.1 p.2) ->
  continuous (fun q => (f p.1 q.2 + f q.1 p.2)) /\
  (fun q => f q.1 q.2) \o shift p = cst (f p.1 p.2) +
    (fun q => f p.1 q.2 + f q.1 p.2) +o_ (0 : U * V) id.
Proof.
move=> fc; split=> [q|].
  by apply: (@continuousD _ _ _ _ _ (fun q => f p.1 q.2) (fun q => f q.1 p.2));
    move=> A /(fc (_.1, _.2)) /= /nbhs_ballP [_ /posnumP[e] fpqe_A];
    apply/nbhs_ballP; exists e%:num => //= r [? ?]; exact: (fpqe_A (_.1, _.2)).
apply/eqaddoE; rewrite funeqE => q /=.
rewrite linearDr !linearDl -addrA addrC addrA [_ + f p.1 p.2]addrC.
by congr (_ + _); rewrite -[LHS]/((fun p => f p.1 p.2) q) bilinear_eqo.
Qed.

Lemma diff_bilin `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : {bilinear U -> V -> W}) p :
  continuous (fun p => f p.1 p.2) -> 'd (fun q => f q.1 q.2) p =
  (fun q => f p.1 q.2 + f q.1 p.2) :> (U * V -> W).
Proof.
pose s q := f p.1 q.2 + f q.1 p.2.
move=> fc; have lind : linear s.
  by move=> ? ? ?; rewrite /s linearPr linearPl scalerDr addrACA.
pose slM := GRing.isLinear.Build _ _ _ _ _ lind.
pose sL : {linear _ -> _} := HB.pack s slM.
rewrite -/s -[s]/(sL : _ -> _).
by apply/diff_unique; have [] := dbilin p fc.
Qed.

Lemma differentiable_bilin `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : {bilinear U -> V -> W}) p :
  continuous (fun p => f p.1 p.2) -> differentiable (fun p => f p.1 p.2) p.
Proof.
by move=> fc; apply/diff_locallyP; rewrite diff_bilin //; apply: dbilin p fc.
Qed.

Lemma mulr_is_bilinear :
  bilinear_for
    (GRing.Scale.Law.clone _ _ *:%R _) (GRing.Scale.Law.clone _ _ *:%R _)
    (@GRing.mul R).
Proof.
split=> [u'|u] a x y /=.
- by rewrite mulrDl scalerAl.
- by rewrite mulrDr scalerAr.
Qed.
HB.instance Definition _ := bilinear_isBilinear.Build R R R R _ _ (@GRing.mul R)
  mulr_is_bilinear.

Global Instance is_diff_mulr (p : R * R) :
  is_diff p (fun q => q.1 * q.2) (fun q => p.1 * q.2 + q.1 * p.2).
Proof.
apply: DiffDef; last by rewrite diff_bilin // => ?; apply: mul_continuous.
by apply: differentiable_bilin =>?; apply: mul_continuous.
Qed.

Lemma eqo_pair `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (F : filter_on U) (f : U -> V) (g : U -> W) :
  (fun t => ([o_F id of f] t, [o_F id of g] t)) =o_F id.
Proof.
apply/eqoP => _/posnumP[e]; near=> x; rewrite num_ge_max /=.
by apply/andP; split; near: x; apply: littleoP.
Unshelve. all: by end_near. Qed.

Fact dpair `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : U -> V) (g : U -> W) x :
  differentiable f x -> differentiable g x ->
  continuous (fun y => ('d f x y, 'd g x y)) /\
  (fun y => (f y, g y)) \o shift x = cst (f x, g x) +
  (fun y => ('d f x y, 'd g x y)) +o_ 0 id.
Proof.
move=> df dg; split=> [?|]; first by apply: cvg_pair; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
rewrite ![_ (_ + x)]diff_locallyx//.
(* fixme *)
have -> : forall h e, (f x + 'd f x y + [o_ 0 id of h] y,
  g x + 'd g x y + [o_ 0 id of e] y) =
  (f x, g x) + ('d f x y, 'd g x y) +
  ([o_ 0 id of h] y, [o_ 0id of e] y) by [].
by congr (_ + _); rewrite -[LHS]/((fun y => (_ y, _ y)) y) eqo_pair.
Qed.

Lemma diff_pair `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : U -> V) (g : U -> W) x :
  differentiable f x -> differentiable g x -> 'd (fun y => (f y, g y)) x =
  (fun y => ('d f x y, 'd g x y)) :> (U -> V * W).
Proof.
move=> df dg.
pose p y := ('d f x y, 'd g x y).
have lin_pair : linear p by move=> ???; rewrite /p !linearPZ.
pose pairlM := GRing.isLinear.Build _ _ _ _ _ lin_pair.
pose pairL : {linear _ -> _} := HB.pack p pairlM.
rewrite -/p -[p]/(pairL : _ -> _).
by apply: diff_unique; have [] := dpair df dg.
Qed.

Lemma differentiable_pair `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f : U -> V) (g : U -> W) x :
  differentiable f x -> differentiable g x ->
  differentiable (fun y => (f y, g y)) x.
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diff_pair //; apply: dpair.
Qed.

Global Instance is_diff_pair `(U : normedModType d1 R) `(V : normedModType d2 R)
    `(W : normedModType d3 R) (f df : U -> V) (g dg : U -> W) x :
  is_diff x f df -> is_diff x g dg ->
  is_diff x (fun y => (f y, g y)) (fun y => (df y, dg y)).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiable_pair.
by rewrite diff_pair // !diff_val.
Qed.

Global Instance is_diffM `(V : normedModType d R) (f g df dg : V -> R) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx.
have -> : f * g = (fun p => p.1 * p.2) \o (fun y => (f y, g y)) by [].
apply: is_diff_eq.
by rewrite funeqE => ?; rewrite /= [_ * g _]mulrC.
Qed.

Lemma diffM `(V : normedModType d R) (f g : V -> R) x :
  differentiable f x -> differentiable g x ->
  'd (f * g) x = f x \*: 'd g x + g x \*: 'd f x :> (V -> R).
Proof.
by move=> /differentiableP df /differentiableP dg; rewrite [LHS]diff_val.
Qed.

Lemma differentiableM `(V : normedModType d R) (f g : V -> R) x :
  differentiable f x -> differentiable g x -> differentiable (f * g) x.
Proof. by move=> /differentiableP df /differentiableP dg. Qed.

(* TODO: fixme using (1 / (h + x) - 1 / x) / h = - 1 / (h + x) x = -1/x^2 + o(1) *)
Fact dinv (x : R) :
  x != 0 -> continuous (fun h : R => - x ^- 2 *: h) /\
  (fun x => x^-1)%R \o shift x = cst (x^-1)%R +
  (fun h : R => - x ^- 2 *: h) +o_ 0 id.
Proof.
move=> xn0; split; first by move=> ?; exact: continuousZl_tmp.
apply/eqaddoP => _ /posnumP[e]; near=> h.
have hDx_neq0 : h + x != 0.
  near: h; rewrite !nbhs_simpl; apply/nbhs_normP.
  exists `|x|; first by rewrite /= normr_gt0.
  move=> h /=; rewrite /= distrC subr0 -subr_gt0 => lthx.
  rewrite -(normr_gt0 (h + x)) addrC -[h]opprK.
  apply: lt_le_trans (ler_dist_dist _ _).
  by rewrite ger0_norm normrN //; apply: ltW.
rewrite !fctE/= opprD scaleNr opprK.
suff: `|h * h| / `|h + x| / `|x * x| <= e%:num * `|h|.
  rewrite -2!normf_div -mulrA -invfM; congr (`|_| <= _).
  apply/(canLR (mulfK _)); rewrite ?mulf_neq0//.
  rewrite mulrDl mulKf// [(_ + _) * _]mulrC mulrDr mulrN.
  rewrite -mulrA mulfK// -mulrA mulVKf ?mulf_neq0//.
  by rewrite [- _ + _]addrC !mulrDl [x * h]mulrC addrKA subrKC.
rewrite ler_pdivrMr ?normr_gt0 ?mulf_neq0 // mulrAC ler_pdivrMr ?normr_gt0 //.
have : `|h * h| <= `|x / 2| * (e%:num * `|x * x| * `|h|).
  rewrite !mulrA; near: h; exists (`|x / 2| * e%:num * `|x * x|).
    by rewrite /= !pmulr_rgt0 // normr_gt0 mulf_neq0.
  by move=> h /ltW; rewrite distrC subr0 [`|h * _|]normrM => /ler_pM; apply.
move=> /le_trans -> //; rewrite [leLHS]mulrC ler_pM ?mulr_ge0 //.
near: h; exists (`|x| / 2); first by rewrite /= divr_gt0 ?normr_gt0.
move=> h; rewrite /= distrC subr0 => lthhx; rewrite addrC -[h]opprK.
apply: le_trans (@ler_dist_dist  _ R  _ _).
rewrite normrN [leRHS]ger0_norm.
  rewrite subr_ge0; apply: ltW; apply: lt_le_trans lthhx _.
  by rewrite ler_pdivrMr // -{1}(mulr1 `|x|) ler_pM // ler1n.
rewrite lerBrDr -lerBrDl (splitr `|x|).
rewrite normf_div (@ger0_norm _ 2) // addrK; apply/ltW.
Unshelve. all: by end_near. Qed.

Lemma diff_Rinv (x : R) : x != 0 ->
  'd GRing.inv x = (fun h : R => - x ^- 2 *: h) :> (R -> R).
Proof.
move=> xn0; have -> : (fun h : R => - x ^- 2 *: h) = ( *:%R (- x ^- 2)) by [].
by apply: diff_unique; have [] := dinv xn0.
Qed.

Lemma differentiable_Rinv (x : R) : x != 0 ->
  differentiable (GRing.inv : R -> R) x.
Proof.
by move=> xn0; apply/diff_locallyP; rewrite diff_Rinv //; apply: dinv.
Qed.

Lemma diffV `(V : normedModType d R) (f : V -> R) x :
  differentiable f x -> f x != 0 ->
  'd (fun y => (f y)^-1) x = - (f x) ^- 2 \*: 'd f x :> (V -> R).
Proof.
move=> df fxn0.
by rewrite [LHS](diff_comp df (differentiable_Rinv fxn0)) diff_Rinv.
Qed.

Lemma differentiableV `(V : normedModType d R) (f : V -> R) x :
  differentiable f x -> f x != 0 -> differentiable (fun y => (f y)^-1) x.
Proof.
by move=> df fxn0; apply: differentiable_comp _ (differentiable_Rinv fxn0).
Qed.

Global Instance is_diffX `(V : normedModType d R) (f df : V -> R) n x :
  is_diff x f df -> is_diff x (f ^+ n.+1) (n.+1%:R * f x ^+ n *: df).
Proof.
move=> dfx; elim: n => [|n ihn]; first by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_diff_eq.
rewrite scalerA mulrCA -exprS -scalerDl.
by rewrite [in LHS]mulr_natl exprfctE -mulrSr mulr_natl.
Qed.

Lemma differentiableX `(V : normedModType d R) (f : V -> R) n x :
  differentiable f x -> differentiable (f ^+ n.+1) x.
Proof. by move=> /differentiableP. Qed.

Lemma diffX `(V : normedModType d R) (f : V -> R) n x :
  differentiable f x ->
  'd (f ^+ n.+1) x = n.+1%:R * f x ^+ n \*: 'd f x :> (V -> R).
Proof. by move=> /differentiableP df; rewrite diff_val. Qed.

End DifferentialR3_numFieldType.

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
