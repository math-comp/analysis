(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau forms.

(**md**************************************************************************)
(* # Differentiation                                                          *)
(*                                                                            *)
(* This file provides a theory of differentiation. It includes the standard   *)
(* rules of differentiation (differential of a sum, of a product, of          *)
(* exponentiation, of the inverse, etc.) as well as standard theorems (the    *)
(* Extreme Value Theorem, Rolle's theorem, the Mean Value Theorem).           *)
(*                                                                            *)
(* Parsable notations (in all of the following, f is not supposed to be       *)
(* differentiable):                                                           *)
(* ```                                                                        *)
(*               'd f x == the differential of a function f at a point x      *)
(*   differentiable f x == the function f is differentiable at a point x      *)
(*               'J f x == the Jacobian of f at a point x                     *)
(*               'D_v f == the directional derivative of f along v            *)
(*      derivable f a v == the function f is derivable at a with direction v  *)
(*                         The type of f is V -> W with V W : normedModType R *)
(*                         and R : numFieldType                               *)
(*               f^`()  == the derivative of f of domain R                    *)
(*               f^`(n) == the nth derivative of f of domain R                *)
(* ```                                                                        *)
(*                                                                            *)
(* Naming convention in this file:                                            *)
(* - lemmas of the form `... -> derivable f x v` are named `derivable*`       *)
(*   (e.g., `derivableV`, `derivableM`)                                       *)
(*   or `*derivable` (e.g., `diff_derivable`)                                 *)
(* - lemmas of the form `D_v f x = ...` are named `derive*`                   *)
(*   (e.g., `deriveVP, `deriveM`)                                             *)
(* - lemmas of the form `f^`() x = ...` are named `derive1*`                  *)
(*   (e.g., `derive1_cst`, `derive1_comp`)                                    *)
(* - lemmas of the form `... -> is_derive x v f df` are named `is_derive*`    *)
(*   (e.g., `is_derive_cst`)                                                  *)
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
Reserved Notation "''J' f p" (at level 10, p, f at next level,
  format "''J'  f  p").
Reserved Notation "''D_' v f" (at level 10, v, f at next level,
  format "''D_' v  f").
Reserved Notation "''D_' v f c" (at level 10, v, f at next level,
  format "''D_' v  f  c"). (* printing *)
Reserved Notation "f ^` ()" (format "f ^` ()").
Reserved Notation "f ^` ( n )" (format "f ^` ( n )").

Section Differential.
Context {K : numDomainType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => continuous df /\ forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).

Local Notation "''d' f x" := (@diff _ (Phantom _ (nbhs x)) f).

Fact diff_key : forall T, T -> unit. Proof. by constructor. Qed.
CoInductive differentiable_def (f : V -> W) (x : filter_on V)
  (phF : phantom (set (set V)) x) : Prop := DifferentiableDef of
  (continuous ('d f x) /\
  f = cst (f (lim x)) + 'd f x \o center (lim x) +o_x (center (lim x))).

Local Notation differentiable f F :=
  (@differentiable_def f _ (Phantom _ (nbhs F))).

Class is_diff_def (x : filter_on V) (Fph : phantom (set (set V)) x) (f : V -> W)
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
Hint Extern 0 (continuous _) => exact: diff_continuous : core.

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
Context {K : numFieldType (*TODO: to numDomainType?*)} {V W : normedModType K}.

(* duplicate from Section Differential *)
Local Notation differentiable f F :=
  (@differentiable_def _ _ _ f _ (Phantom _ (nbhs F))).
Local Notation "''d' f x" := (@diff _ _ _ _ (Phantom _ (nbhs x)) f).
Hint Extern 0 (continuous _) => exact: diff_continuous : core.

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

Notation "''d' f F" := (@diff _ _ _ _ (Phantom _ (nbhs F)) f).
Notation differentiable f F := (@differentiable_def _ _ _ f _ (Phantom _ (nbhs F))).

Notation "'is_diff' F" := (is_diff_def (Phantom _ (nbhs F))).
#[global] Hint Extern 0 (differentiable _ _) => solve[apply: ex_diff] : core.
#[global] Hint Extern 0 ({for _, continuous _}) => exact: diff_continuous : core.

Lemma differentiableP (R : numDomainType) (V W : normedModType R) (f : V -> W) x :
  differentiable f x -> is_diff x f ('d f x).
Proof. by move=> ?; apply: DiffDef. Qed.

Section jacobian.

Definition jacobian n m (R : numFieldType) (f : 'rV[R]_n.+1 -> 'rV[R]_m.+1) p :=
  lin1_mx ('d f p).

End jacobian.

Notation "''J' f p" := (jacobian f p).

Section DifferentialR.

Context {R : numFieldType} {V W : normedModType R}.

(* split in multiple bits:
- a linear map which is locally bounded is a little o of 1
- the identity is a littleo of 1
*)
Lemma differentiable_continuous (x : V) (f : V -> W) :
  differentiable f x -> {for x, continuous f}.
Proof.
move=> /diff_locallyP [dfc]; rewrite -addrA.
rewrite (littleo_bigO_eqo (cst (1 : R))); last first.
  by apply/eqOP; near=> k; rewrite /cst [`|1|]normr1 mulr1; near do by [].
rewrite addfo; first by move=> /eqolim; rewrite cvg_comp_shift add0r.
by apply/eqolim0P; apply: (cvg_trans (dfc 0)); rewrite linear0.
Unshelve. all: by end_near. Qed.

Section littleo_lemmas.
Variables (X Y Z : normedModType R).

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
  rewrite /at_point opprD -![(_ + _ : _ -> _) _]/(_ + _) scale0r add0r.
  by rewrite addrCA addKr normrN scale0r !normr0 mulr0.
have /eqolimP := df.
move=> /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]).
apply: filter_app; rewrite /= !near_simpl near_withinE; near=> h => hN0.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|1|]normr1 mulr1 => dfv.
rewrite addrA -[X in X + _]scale1r -(@mulVf _ h) //.
rewrite mulrC -scalerA -scalerBr normrZ.
rewrite -ler_pdivlMl; last by rewrite normr_gt0.
by rewrite mulrCA mulVf ?mulr1; last by rewrite normr_eq0.
Unshelve. all: by end_near. Qed.

Lemma derivable_nbhsP (f : V -> W) a v :
  derivable f a v <->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (nbhs 0) id.
Proof.
split; first exact: derivable_nbhs.
move=> df; apply/cvg_ex; exists ('D_v f a).
apply/(@eqolimP _ _ _ (dnbhs_filter_on _))/eqaddoP => _/posnumP[e].
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
by apply: eqaddoEx => h; have /= := (df h); rewrite addrC => ->.
Qed.

Lemma derivable_nbhsxP (f : V -> W) a v :
  derivable f a v <-> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near nbhs 0) h.
Proof.
split; first exact: derivable_nbhsx.
move=> df; apply/derivable_nbhsP; apply/eqaddoE; rewrite funeqE => h.
by rewrite /= addrC df.
Qed.

End DifferentialR.

Notation "''D_' v f" := (derive f ^~ v).
Notation "''D_' v f c" := (derive f c v). (* printing *)
#[global] Hint Extern 0 (derivable _ _ _) => solve[apply: ex_derive] : core.

Section DifferentialR_numFieldType.
Context {R : numFieldType} {V W : normedModType R}.

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable f a -> 'D_v f a = 'd f a v.
Proof.
rewrite /derive => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE=> h; rewrite !scalerDr scalerN /cst /=.
  by rewrite addrC !addrA addNr add0r linearZ /= scalerA /g.
apply: cvg_lim => //.
pose g1 : R -> W := fun h => (h^-1 * h) *: 'd f a v.
pose g2 : R -> W := fun h : R => h^-1 *: k (h *: v ).
rewrite (_ : g = g1 + g2) ?funeqE // -(addr0 (_ _ v)); apply: cvgD.
  rewrite -(scale1r (_ _ v)); apply: cvgZl => /= X [e e0].
  rewrite /ball_ /= => eX.
  apply/nbhs_ballP.
  by exists e => //= x _ x0; apply eX; rewrite mulVr // ?unitfE //= subrr normr0.
rewrite /g2.
have [->|v0] := eqVneq v 0.
  rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
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
rewrite -(mulrC e) -mulrA -ltr_pdivlMl // mulrA mulVr ?unitfE ?gt_eqF //.
rewrite normrV ?unitfE // div1r invrK ltr_pdivrMl; last first.
  by rewrite pmulr_rgt0 // normr_gt0.
rewrite normrZ mulrC -mulrA.
by rewrite ltr_pMl ?ltr1n // pmulr_rgt0 ?normm_gt0 // normr_gt0.
Qed.

End DifferentialR_numFieldType.

Section DifferentialR2.
Variable R : numFieldType.
Implicit Type (V : normedModType R).

Lemma derivemxE m n (f : 'rV[R]_m.+1 -> 'rV[R]_n.+1) (a v : 'rV[R]_m.+1) :
  differentiable f a -> 'D_ v f a = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

Definition derive1 V (f : R -> V) (a : R) :=
   lim ((fun h => h^-1 *: (f (h + a) - f a)) @ 0^').

Local Notation "f ^` ()" := (derive1 f).

Lemma derive1E V (f : R -> V) a : f^`() a = 'D_1 f a.
Proof.
rewrite /derive1 /derive; set d := (fun _ : R => _); set d' := (fun _ : R => _).
by suff -> : d = d' by []; rewrite funeqE=> h; rewrite /d /d' /= [h%:A](mulr1).
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

End DifferentialR2.

Notation "f ^` ()" := (derive1 f) : classical_set_scope.
Notation "f ^` ( n )" := (derive1n n f) : classical_set_scope.

Section DifferentialR3.
Variable R : numFieldType.

Fact dcst (V W : normedModType R) (a : W) (x : V) : continuous (0 : V -> W) /\
  cst a \o shift x = cst (cst a x) + \0 +o_ 0 id.
Proof.
split; first exact: cst_continuous.
apply/eqaddoE; rewrite addr0 funeqE => ? /=; rewrite -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof.
Qed.

Variables (V W : normedModType R).

Fact dadd (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  continuous ('d f x \+ 'd g x) /\
  (f + g) \o shift x = cst ((f + g) x) + ('d f x \+ 'd g x) +o_ 0 id.
Proof.
move=> df dg; split => [?|]; do ?exact: continuousD.
apply/(@eqaddoE R); rewrite funeqE => y /=; rewrite -[(f + g) _]/(_ + _).
by rewrite ![_ (_ + x)]diff_locallyx// addrACA addox addrACA.
Qed.

Fact dopp (f : V -> W) x :
  differentiable f x -> continuous (- ('d f x : V -> W)) /\
  (- f) \o shift x = cst (- f x) \- 'd f x +o_ 0 id.
Proof.
move=> df; split; first by move=> ?; apply: continuousN.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(- f) _]/(- (_ _)) diff_locallyx// !opprD oppox.
Qed.

Lemma is_diff_eq (V' W' : normedModType R) (f f' g : V' -> W') (x : V') :
  is_diff x f f' -> f' = g -> is_diff x f g.
Proof. by move=> ? <-. Qed.

Fact dscale (f : V -> W) k x :
  differentiable f x -> continuous (k \*: 'd f x) /\
  (k *: f) \o shift x = cst ((k *: f) x) + k \*: 'd f x +o_ 0 id.
Proof.
move=> df; split; first by move=> ?; apply: continuousZr.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(k *: f) _]/(_ *: _) diff_locallyx // !scalerDr scaleox.
Qed.

(* NB: could be generalized with K : absRingType instead of R; DONE? *)
Fact dscalel (k : V -> R) (f : W) x :
  differentiable k x ->
  continuous (fun z : V => 'd k x z *: f) /\
  (fun z => k z *: f) \o shift x =
    cst (k x *: f) + (fun z => 'd k x z *: f) +o_ 0 id.
Proof.
move=> df; split.
  move=> ?; exact/continuousZl/diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite diff_locallyx //= !scalerDl scaleolx.
Qed.

Fact dlin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> f \o shift x = cst (f x) + f +o_ 0 id.
Proof.
move=> df; apply: eqaddoE; rewrite funeqE => y /=.
rewrite linearD addrC -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof. (*fixme*)
Qed.

(* TODO: generalize *)
Lemma compoO_eqo (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') :
  [o_ 0 id of g] \o [O_ 0 id of f] =o_ 0 id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ 0 id of f]].
have := littleoP [littleo of [o_ 0 id of g]].
move=>  /(_ (e%:num / k%:num)) /(_ _) /nbhs_ballP [//|_ /posnumP[d] hd].
apply: filter_app; near=> x => leOxkx; apply: le_trans (hd _ _) _; last first.
  rewrite -ler_pdivlMl //; apply: le_trans leOxkx _.
  by rewrite invf_div mulrA -[_ / _ * _]mulrA mulVf // mulr1.
by rewrite -ball_normE /= distrC subr0 (le_lt_trans leOxkx) // -ltr_pdivlMl.
Unshelve. all: by end_near. Qed.

Lemma compoO_eqox (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') :
  forall x : U, [o_ 0 id of g] ([O_ 0 id of f] x) =o_(x \near 0) x.
Proof. by move=> x; rewrite -[LHS]/((_ \o _) x) compoO_eqo. Qed.

(* TODO: generalize *)
Lemma compOo_eqo  (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') :
  [O_ 0 id of g] \o [o_ 0 id of f] =o_ 0 id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ 0 id of g]].
move=> /nbhs_ballP [_ /posnumP[d] hd].
have ekgt0 : e%:num / k%:num > 0 by [].
have /(_ _ ekgt0) := littleoP [littleo of [o_ 0 id of f]].
apply: filter_app; near=> x => leoxekx; apply: le_trans (hd _ _) _; last first.
  by rewrite -ler_pdivlMl // mulrA [_^-1 * _]mulrC.
by rewrite -ball_normE /= distrC subr0 (le_lt_trans leoxekx)// -ltr_pdivlMl //.
Unshelve. all: by end_near. Qed.

End DifferentialR3.

Section DifferentialR3_numFieldType.
Variable R : numFieldType.

Lemma littleo_linear0 (V W : normedModType R) (f : {linear V -> W}) :
  (f : V -> W) =o_ 0 id -> f = cst 0 :> (V -> W).
Proof.
move/eqoP => oid.
rewrite funeqE => x; apply/eqP; have [|xn0] := real_le0P (normr_real x).
  by rewrite normr_le0 => /eqP ->; rewrite linear0.
rewrite -normr_le0 -(mul0r `|x|) -ler_pdivrMr //.
apply/ler_gtP => _ /posnumP[e]; rewrite ler_pdivrMr //.
have /oid /nbhs_ballP [_ /posnumP[d] dfe] := [elaborate gt0 e].
set k := ((d%:num / 2) / (PosNum xn0)%:num)^-1.
rewrite -{1}(@scalerKV _ _ k _ x) /k // linearZZ normrZ.
rewrite -ler_pdivlMl; last by rewrite gtr0_norm.
rewrite mulrCA (@le_trans _ _ (e%:num * `|k^-1 *: x|)) //; last first.
  by rewrite ler_pM // normrZ normfV.
apply: dfe; rewrite -ball_normE /= sub0r normrN normrZ.
rewrite invrK -ltr_pdivlMr // ger0_norm // ltr_pdivrMr //.
by rewrite -mulrA mulVf ?lt0r_neq0 // mulr1 [ltRHS]splitr ltrDl.
Qed.

Lemma diff_unique (V W : normedModType R) (f : V -> W)
  (df : {linear V -> W}) x :
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
  by rewrite opprD addrCA -(addrA (_ - _)) addKr oppox addox.
apply/diffP => /=.
apply: (@getPex _ (fun (df : {linear V -> W}) => continuous df /\
  forall y, f y = f (lim (nbhs x)) + df (y - lim (nbhs x))
                  +o_(y \near x) (y - lim (nbhs x)))).
exists df; split=> //; apply: eqaddoEx => z.
rewrite (hdf _ dxf) !addrA lim_id // /(_ \o _) /= subrK [f _ + _]addrC addrK.
rewrite -addrA -[LHS]addr0; congr (_ + _).
apply/eqP; rewrite eq_sym addrC addr_eq0 oppox; apply/eqP.
by rewrite littleo_center0 (comp_centerK x id) -[- _ in RHS](comp_centerK x).
Qed.

Lemma diff_cst (V W : normedModType R) a x : ('d (cst a) x : V -> W) = 0.
Proof. by apply/diff_unique; have [] := dcst a x. Qed.

Variables (V W : normedModType R).

Lemma differentiable_cst (W' : normedModType R) (a : W') (x : V) :
  differentiable (cst a) x.
Proof. by apply/diff_locallyP; rewrite diff_cst; have := dcst a x. Qed.

Global Instance is_diff_cst (a : W) (x : V) : is_diff x (cst a) 0.
Proof. exact: DiffDef (differentiable_cst _ _) (diff_cst _ _). Qed.

Lemma diffD (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  'd (f + g) x = 'd f x \+ 'd g x :> (V -> W).
Proof. by move=> df dg; apply/diff_unique; have [] := dadd df dg. Qed.

Lemma differentiableD (f g : V -> W) x :
  differentiable f x -> differentiable g x -> differentiable (f + g) x.
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diffD; have := dadd df dg.
Qed.

Global Instance is_diffD (f g df dg : V -> W) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f + g) (df + dg).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiableD.
by rewrite diffD; first (congr (_ + _); apply: diff_val).
Qed.

Lemma differentiable_sum n (f : 'I_n -> V -> W) (x : V) :
  (forall i, differentiable (f i) x) -> differentiable (\sum_(i < n) f i) x.
Proof.
by elim/big_ind : _ => // ? ? g h ?; apply: differentiableD; [exact:g|exact:h].
Qed.

Lemma diffN (f : V -> W) x :
  differentiable f x -> 'd (- f) x = - ('d f x : V -> W) :> (V -> W).
Proof.
move=> df; rewrite -[RHS]/(@GRing.opp _ \o _); apply/diff_unique;
by have [] := dopp df.
Qed.

Lemma differentiableN (f : V -> W) x :
  differentiable f x -> differentiable (- f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffN //; have := dopp df.
Qed.

Global Instance is_diffN (f df : V -> W) x :
  is_diff x f df -> is_diff x (- f) (- df).
Proof.
move=> dfx; apply: DiffDef; first exact: differentiableN.
by rewrite diffN // diff_val.
Qed.

Global Instance is_diffB (f g df dg : V -> W) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f - g) (df - dg).
Proof. by move=> dfx dgx; apply: is_diff_eq. Qed.

Lemma diffB (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  'd (f - g) x = 'd f x \- 'd g x :> (V -> W).
Proof.
by move=> /differentiableP df /differentiableP dg; rewrite [LHS]diff_val.
Qed.

Lemma differentiableB (f g : V -> W) x :
  differentiable f x -> differentiable g x -> differentiable (f \- g) x.
Proof. by move=> /differentiableP df /differentiableP dg. Qed.

Lemma diffZ (f : V -> W) k x :
  differentiable f x -> 'd (k *: f) x = k \*: 'd f x :> (V -> W).
Proof. by move=> df; apply/diff_unique; have [] := dscale k df. Qed.

Lemma differentiableZ (f : V -> W) k x :
  differentiable f x -> differentiable (k *: f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffZ //; have := dscale k df.
Qed.

Global Instance is_diffZ (f df : V -> W) k x :
  is_diff x f df -> is_diff x (k *: f) (k *: df).
Proof.
move=> dfx; apply: DiffDef; first exact: differentiableZ.
by rewrite diffZ // diff_val.
Qed.

Lemma diffZl (k : V -> R) (f : W) x : differentiable k x ->
  'd (fun z => k z *: f) x = (fun z => 'd k x z *: f) :> (_ -> _).
Proof.
move=> df; set g := RHS; have glin : linear g.
  by move=> a u v; rewrite /g linearP /= scalerDl -scalerA.
pose glM := GRing.isLinear.Build _ _ _ _ _ glin.
pose gL : {linear _ -> _} := HB.pack g glM.
by apply:(@diff_unique _ _ _ gL); have [] := dscalel f df.
Qed.

Lemma differentiableZl (k : V -> R) (f : W) x :
  differentiable k x -> differentiable (fun z => k z *: f) x.
Proof.
by move=> df; apply/diff_locallyP; rewrite diffZl //; have [] := dscalel f df.
Qed.

Lemma diff_lin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> 'd f x = f :> (V' -> W').
Proof. by move=> fcont; apply/diff_unique => //; apply: dlin. Qed.

Lemma linear_differentiable (V' W' : normedModType R) (f : {linear V' -> W'})
  x : continuous f -> differentiable f x.
Proof.
by move=> fcont; apply/diff_locallyP; rewrite diff_lin //; have := dlin x fcont.
Qed.

Global Instance is_diff_id (x : V) : is_diff x id id.
Proof.
apply: DiffDef.
  by apply: (@linear_differentiable _ _ idfun) => ? //.
by rewrite (@diff_lin _ _ idfun) // => ? //.
Qed.

Global Instance is_diff_scaler (k : R) (x : V) : is_diff x ( *:%R k) ( *:%R k).
Proof.
apply: DiffDef; first exact/linear_differentiable/scaler_continuous.
by rewrite diff_lin //; apply: scaler_continuous.
Qed.

Global Instance is_diff_scalel (k : R) (x : V) :
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

Lemma differentiable_coord m n (M : 'M[R]_(m.+1, n.+1)) i j :
  differentiable (fun N : 'M[R]_(m.+1, n.+1) => N i j : R ) M.
Proof.
have @f : {linear 'M[R]_(m.+1, n.+1) -> R}.
  by exists (fun N : 'M[R]_(_, _) => N i j); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma linear_lipschitz (V' W' : normedModType R) (f : {linear V' -> W'}) :
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
rewrite normfV ger0_norm /k // invrM ?unitfE // mulrAC mulVf //.
by rewrite invf_div mul1r [ltRHS]splitr; apply: ltr_pwDr.
Qed.

Lemma linear_eqO (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> (f : V' -> W') =O_ 0 id.
Proof.
move=> /linear_lipschitz [k kgt0 flip]; apply/eqO_exP; exists k => //.
exact: filterE.
Qed.

Lemma diff_eqO (V' W' : normedModType R) (x : filter_on V') (f : V' -> W') :
  differentiable f x -> ('d f x : V' -> W') =O_ 0 id.
Proof. by move=> /diff_continuous /linear_eqO; apply. Qed.

Lemma compOo_eqox (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
  [O_ 0 id of g] ([o_ 0 id of f] x) =o_(x \near 0) x.
Proof. by rewrite -[LHS]/((_ \o _) x) compOo_eqo. Qed.

Fact dcomp (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
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

Lemma diff_comp (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
  differentiable f x -> differentiable g (f x) ->
  'd (g \o f) x = 'd g (f x) \o 'd f x :> (U -> W').
Proof. by move=> df dg; apply/diff_unique; have [? /funext] := dcomp df dg. Qed.

Lemma differentiable_comp (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') x : differentiable f x -> differentiable g (f x) ->
  differentiable (g \o f) x.
Proof.
move=> df dg; apply/diff_locallyP; rewrite diff_comp //;
by have [? /funext]:= dcomp df dg.
Qed.

Global Instance is_diff_comp (U V' W' : normedModType R) (f df : U -> V')
  (g dg : V' -> W') x : is_diff x f df -> is_diff (f x) g dg ->
  is_diff x (g \o f) (dg \o df) | 99.
Proof.
move=> dfx dgfx; apply: DiffDef; first exact: differentiable_comp.
by rewrite diff_comp // !diff_val.
Qed.

Lemma bilinear_schwarz (U V' W' : normedModType R)
  (f : {bilinear U -> V' -> W'}) : continuous (fun p => f p.1 p.2) ->
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
  rewrite invrM ?unitfE // [kv ^-1]invrM ?unitfE //.
  rewrite mulrC -[_ *: u]scalerA [X in X *: v]mulrC -[_ *: v]scalerA.
  by rewrite invf_div.
rewrite normrZ ger0_norm // -mulrA gtr_pMr // ltr_pdivrMl // mulr1.
by rewrite prod_normE/= !normrZ !normfV !normr_id !mulVf ?gt_eqF// maxxx ltr1n.
Qed.

Lemma bilinear_eqo (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) :
  continuous (fun p => f p.1 p.2) -> (fun p => f p.1 p.2) =o_ (0 : U * V') id.
Proof.
move=> fc; have [_ /posnumP[k] fschwarz] := bilinear_schwarz fc.
apply/eqoP=> _ /posnumP[e]; near=> x; rewrite (le_trans (fschwarz _ _))//.
rewrite ler_pM ?pmulr_rge0 //; last by rewrite num_le_max /= lexx orbT.
rewrite -ler_pdivlMl //.
suff : `|x| <= k%:num ^-1 * e%:num.
  by apply: le_trans; rewrite num_le_max /= lexx.
near: x; rewrite !near_simpl; apply/nbhs_le_nbhs_norm.
by exists (k%:num ^-1 * e%:num) => //= ? /=; rewrite /= distrC subr0 => /ltW.
Unshelve. all: by end_near. Qed.

Fact dbilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) ->
  continuous (fun q => (f p.1 q.2 + f q.1 p.2)) /\
  (fun q => f q.1 q.2) \o shift p = cst (f p.1 p.2) +
    (fun q => f p.1 q.2 + f q.1 p.2) +o_ (0 : U * V') id.
Proof.
move=> fc; split=> [q|].
  by apply: (@continuousD _ _ _ (fun q => f p.1 q.2) (fun q => f q.1 p.2));
    move=> A /(fc (_.1, _.2)) /= /nbhs_ballP [_ /posnumP[e] fpqe_A];
    apply/nbhs_ballP; exists e%:num => //= r [? ?]; exact: (fpqe_A (_.1, _.2)).
apply/eqaddoE; rewrite funeqE => q /=.
rewrite linearDl !linearDr addrA addrC.
rewrite -[f q.1 _ + _ + _]addrA [f q.1 _ + _]addrC addrA [f q.1 _ + _]addrC.
by congr (_ + _); rewrite -[LHS]/((fun p => f p.1 p.2) q) bilinear_eqo.
Qed.

Lemma diff_bilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) -> 'd (fun q => f q.1 q.2) p =
  (fun q => f p.1 q.2 + f q.1 p.2) :> (U * V' -> W').
Proof.
pose d q := f p.1 q.2 + f q.1 p.2.
move=> fc; have lind : linear d.
  by move=> ? ? ?; rewrite /d linearPr linearPl scalerDr addrACA.
pose dlM := GRing.isLinear.Build _ _ _ _ _ lind.
pose dL : {linear _ -> _} := HB.pack d dlM.
rewrite -/d -[d]/(dL : _ -> _).
by apply/diff_unique; have [] := dbilin p fc.
Qed.

Lemma differentiable_bilin (U V' W' : normedModType R)
  (f : {bilinear U -> V' -> W'}) p :
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

Lemma eqo_pair (U V' W' : normedModType R) (F : filter_on U)
  (f : U -> V') (g : U -> W') :
  (fun t => ([o_F id of f] t, [o_F id of g] t)) =o_F id.
Proof.
apply/eqoP => _/posnumP[e]; near=> x; rewrite num_ge_max /=.
by apply/andP; split; near: x; apply: littleoP.
Unshelve. all: by end_near. Qed.

Fact dpair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
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

Lemma diff_pair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable f x -> differentiable g x -> 'd (fun y => (f y, g y)) x =
  (fun y => ('d f x y, 'd g x y)) :> (U -> V' * W').
Proof.
move=> df dg.
pose d y := ('d f x y, 'd g x y).
have lin_pair : linear d by move=> ???; rewrite /d !linearPZ.
pose pairlM := GRing.isLinear.Build _ _ _ _ _ lin_pair.
pose pairL : {linear _ -> _} := HB.pack d pairlM.
rewrite -/d -[d]/(pairL : _ -> _).
by apply: diff_unique; have [] := dpair df dg.
Qed.

Lemma differentiable_pair (U V' W' : normedModType R) (f : U -> V')
  (g : U -> W') x : differentiable f x -> differentiable g x ->
  differentiable (fun y => (f y, g y)) x.
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diff_pair //; apply: dpair.
Qed.

Global Instance is_diff_pair (U V' W' : normedModType R) (f df : U -> V')
  (g dg : U -> W') x : is_diff x f df -> is_diff x g dg ->
   is_diff x (fun y => (f y, g y)) (fun y => (df y, dg y)).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiable_pair.
by rewrite diff_pair // !diff_val.
Qed.

Global Instance is_diffM (f g df dg : V -> R) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx.
have -> : f * g = (fun p => p.1 * p.2) \o (fun y => (f y, g y)) by [].
apply: is_diff_eq.
by rewrite funeqE => ?; rewrite /= [_ * g _]mulrC.
Qed.

Lemma diffM (f g : V -> R) x :
  differentiable f x -> differentiable g x ->
  'd (f * g) x = f x \*: 'd g x + g x \*: 'd f x :> (V -> R).
Proof.
by move=> /differentiableP df /differentiableP dg; rewrite [LHS]diff_val.
Qed.

Lemma differentiableM (f g : V -> R) x :
  differentiable f x -> differentiable g x -> differentiable (f * g) x.
Proof. by move=> /differentiableP df /differentiableP dg. Qed.

(* TODO: fixme using (1 / (h + x) - 1 / x) / h = - 1 / (h + x) x = -1/x^2 + o(1) *)
Fact dinv (x : R) :
  x != 0 -> continuous (fun h : R => - x ^- 2 *: h) /\
  (fun x => x^-1)%R \o shift x = cst (x^-1)%R +
  (fun h : R => - x ^- 2 *: h) +o_ 0 id.
Proof.
move=> xn0; suff: continuous (fun h : R => - (1 / x) ^+ 2 *: h) /\
  (fun x => 1 / x ) \o shift x = cst (1 / x) +
  (fun h : R => - (1 / x) ^+ 2 *: h) +o_ 0 id.
  rewrite !mul1r !GRing.exprVn.
  rewrite (_ : (fun x => x^-1) =  (fun x => 1 / x ))//.
  by rewrite funeqE => y; rewrite mul1r.
split; first by move=> ?; apply: continuousZr.
apply/eqaddoP => _ /posnumP[e]; near=> h.
rewrite -[(_ + _ : R -> R) h]/(_ + _) -[(- _ : R -> R) h]/(- _) /=.
rewrite opprD scaleNr opprK /cst /=.
rewrite -[- _]mulr1 -[X in - _ * X](mulfVK xn0) mulrA mulNr -expr2 mulNr.
rewrite [- _ + _]addrC -mulrBr.
rewrite -[X in X + _]mulr1 -[X in 1 / _ * X](@mulfVK _ (x ^+ 2)); last first.
  by rewrite sqrf_eq0.
rewrite mulrA mulf_div mulr1.
have hDx_neq0 : h + x != 0.
  near: h; rewrite !nbhs_simpl; apply/nbhs_normP.
  exists `|x|; first by rewrite /= normr_gt0.
  move=> h /=; rewrite /= distrC subr0 -subr_gt0 => lthx.
  rewrite -(normr_gt0 (h + x)) addrC -[h]opprK.
  apply: lt_le_trans (ler_dist_dist _ _).
  by rewrite ger0_norm normrN //; apply: ltW.
rewrite addrC -[X in X * _]mulr1 -{2}[1](@mulfVK _ (h + x)) //.
rewrite mulrA expr_div_n expr1n mulf_div mulr1 [_ ^+ 2 * _]mulrC -mulrA.
rewrite -mulrDr mulrBr [1 / _ * _]mulrC normrM.
rewrite mulrDl mulrDl opprD addrACA addrA [x * _]mulrC expr2 2!subrK.
rewrite div1r normfV [X in _ / X]normrM invfM [X in _ * X]mulrC.
rewrite mulrA mulrAC ler_pdivrMr ?normr_gt0 ?mulf_neq0 //.
rewrite mulrAC ler_pdivrMr ?normr_gt0 //.
have : `|h * h| <= `|x / 2| * (e%:num * `|x * x| * `|h|).
  rewrite !mulrA; near: h; exists (`|x / 2| * e%:num * `|x * x|).
    by rewrite /= !pmulr_rgt0 // normr_gt0 mulf_neq0.
  by move=> h /ltW; rewrite distrC subr0 [`|h * _|]normrM => /ler_pM; apply.
move=> /le_trans -> //; rewrite [leLHS]mulrC ler_pM ?mulr_ge0 //.
near: h; exists (`|x| / 2); first by rewrite /= divr_gt0 ?normr_gt0.
move=> h; rewrite /= distrC subr0 => lthhx; rewrite addrC -[h]opprK.
apply: le_trans (@ler_dist_dist  _ R  _ _).
rewrite normrN [leRHS]ger0_norm; last first.
  rewrite subr_ge0; apply: ltW; apply: lt_le_trans lthhx _.
  by rewrite ler_pdivrMr // -{1}(mulr1 `|x|) ler_pM // ler1n.
rewrite lerBrDr -lerBrDl (splitr `|x|).
by rewrite normrM normfV (@ger0_norm _ 2) // addrK; apply/ltW.
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

Lemma diffV (f : V -> R) x : differentiable f x -> f x != 0 ->
  'd (fun y => (f y)^-1) x = - (f x) ^- 2 \*: 'd f x :> (V -> R).
Proof.
move=> df fxn0.
by rewrite [LHS](diff_comp df (differentiable_Rinv fxn0)) diff_Rinv.
Qed.

Lemma differentiableV (f : V -> R) x :
  differentiable f x -> f x != 0 -> differentiable (fun y => (f y)^-1) x.
Proof.
by move=> df fxn0; apply: differentiable_comp _ (differentiable_Rinv fxn0).
Qed.

Global Instance is_diffX (f df : V -> R) n x :
  is_diff x f df -> is_diff x (f ^+ n.+1) (n.+1%:R * f x ^+ n *: df).
Proof.
move=> dfx; elim: n => [|n ihn]; first by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_diff_eq.
rewrite scalerA mulrCA -exprS -scalerDl.
by rewrite [in LHS]mulr_natl exprfctE -mulrSr mulr_natl.
Qed.

Lemma differentiableX (f : V -> R) n x :
  differentiable f x -> differentiable (f ^+ n.+1) x.
Proof. by move=> /differentiableP. Qed.

Lemma diffX (f : V -> R) n x :
  differentiable f x ->
  'd (f ^+ n.+1) x = n.+1%:R * f x ^+ n \*: 'd f x :> (V -> R).
Proof. by move=> /differentiableP df; rewrite diff_val. Qed.

End DifferentialR3_numFieldType.

Section DeriveRU.
Variables (R : numFieldType) (U : normedModType R).
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
pose d (h : R) := h *: (f^`() x)%classic.
move=> df; have lin_scal : linear d by move=> ? ? ?; rewrite /d scalerDl scalerA.
pose scallM := GRing.isLinear.Build _ _ _ _ _ lin_scal.
pose scalL : {linear _ -> _} := HB.pack d scallM.
rewrite -/d -[d]/(scalL : _ -> _).
by apply: diff_unique; [apply: scalel_continuous|apply: der1].
Qed.

Lemma diff1E f x :
  differentiable f x -> 'd f x = (fun h => h *: f^`()%classic x) :> (R -> U).
Proof.
pose d (h : R) := h *: 'd f x 1.
move=> df; have lin_scal : linear d by move=> ? ? ?; rewrite /d scalerDl scalerA.
pose scallM := GRing.isLinear.Build _ _ _ _ _ lin_scal.
pose scalL : {linear _ -> _} := HB.pack d scallM.
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

Lemma derivable_within_continuous f (i : interval R) :
  {in i, forall x, derivable f x 1} -> {within [set` i], continuous f}.
Proof.
move=> di; apply/continuous_in_subspaceT => z /[1!inE] zA.
apply/differentiable_continuous; rewrite -derivable1_diffP.
by apply: di; rewrite inE.
Qed.

End DeriveRU.

Section DeriveVW.
Variables (R : numFieldType) (V W : normedModType R).
Implicit Types f : V -> W.

Lemma derivable1P f x v :
  derivable f x v <-> derivable (fun h : R => f (h *: v + x)) 0 1.
Proof.
rewrite /derivable; set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Lemma derivableP f x v : derivable f x v -> is_derive x v f ('D_v f x).
Proof. by move=> df; apply: DeriveDef. Qed.

Lemma diff_derivable f a v : differentiable f a -> derivable f a v.
Proof.
move=> dfa; apply/derivable1P/derivable1_diffP.
by apply: differentiable_comp; rewrite ?scale0r ?add0r.
Qed.

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
Arguments derivable_cst {R V W}.

Section Derive_lemmasVW.
Variables (R : numFieldType) (V W : normedModType R).
Implicit Types f g : V -> W.

Fact der_add f g (x v : V) : derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f + g) \o shift x) (h *: v) - (f + g) x)) @
  0^'  --> 'D_v f x + 'D_v g x.
Proof.
move=> df dg.
evar (fg : R -> W); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  by rewrite !scalerDr scalerN scalerDr opprD addrACA -!scalerBr /fg.
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
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  by rewrite funeqE => h; rewrite !scalerDr !scalerN -opprD -scalerBr /g.
exact: cvgN.
Qed.

Lemma deriveN f (x v : V) : derivable f x v ->
  'D_v (- f) x = - 'D_v f x.
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
move=> df; evar (h : R -> W); rewrite [X in X @ _](_ : _ = h) /=; last first.
  rewrite funeqE => r.
  by rewrite scalerBr !scalerA mulrC -!scalerA -!scalerBr /h.
exact: cvgZr.
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

Lemma derive_cst (k : R) (x v : V) : 'D_v (cst k) x = 0.
Proof. by rewrite derive_val. Qed.

End Derive_lemmasVW.

Section derive_id.
Variables (R : numFieldType) (V : normedModType R).

Lemma derivable_id (x v : V) : derivable id x v.
Proof. exact/diff_derivable. Qed.

Global Instance is_derive_id (x v : V) : is_derive x v id v.
Proof.
apply: (DeriveDef (@derivable_id _ _)).
rewrite deriveE// (@diff_lin _ _ _ idfun)//=.
by rewrite /continuous_at.
Qed.

Global Instance is_deriveNid (x v : V) : is_derive x v -%R (- v).
Proof. exact: is_deriveN. Qed.

Lemma derive_id (x v : V) : 'D_v id x = v.
Proof. by have /derivableP := @derivable_id x v; rewrite derive_val. Qed.

End derive_id.

Section Derive_lemmasVR.
Variables (R : numFieldType) (V : normedModType R).
Implicit Types f g : V -> R.

Fact der_mult f g (x v : V) :
  derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f * g) \o shift x) (h *: v) - (f * g) x)) @
  0^' --> f x *: 'D_v g x + g x *: 'D_v f x.
Proof.
move=> df dg.
evar (fg : R -> R); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  have -> : (f * g) (h *: v + x) - (f * g) x =
    f (h *: v + x) *: (g (h *: v + x) - g x) + g x *: (f (h *: v + x) - f x).
    by rewrite !scalerBr -addrA ![g x *: _]mulrC addKr.
  rewrite scalerDr scalerA mulrC -scalerA.
  by rewrite [_ *: (g x *: _)]scalerA mulrC -scalerA /fg.
apply: cvgD; last exact: cvgZr df.
apply: cvg_comp2 (@scale_continuous _ _ (_, _)) => /=; last exact: dg.
suff : {for 0, continuous (fun h : R => f(h *: v + x))}.
  by move=> /continuous_withinNx; rewrite scale0r add0r.
exact/differentiable_continuous/derivable1_diffP/(derivable1P _ _ _).1.
Qed.

Lemma deriveM f g (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f * g) x = f x *: 'D_v g x + g x *: 'D_v f x.
Proof. by move=> df dg; apply: cvg_lim (der_mult df dg). Qed.

Lemma derivableM f g (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f * g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (f x *: 'D_v g x + g x *: 'D_v f x).
exact: der_mult.
Qed.

Lemma deriveMr f (r : R) (x v : V) :
  derivable f x v -> 'D_v (r \o* f) x = (r * 'D_v f x)%R.
Proof.
move/deriveM => /(_ _ (derivable_cst _ _ _)) ->.
by rewrite derive_cst scaler0 add0r.
Qed.

Lemma deriveMl f (r : R) (x v : V) :
  derivable f x v -> 'D_v (r \*o f) x = (r * 'D_v f x)%R.
Proof. by move=> fxv; rewrite -deriveMr// mul_funC. Qed.

Global Instance is_deriveM f g (x v : V) (df dg : R) :
  is_derive x v f df -> is_derive x v g dg ->
  is_derive x v (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx; apply: DeriveDef; first exact: derivableM.
by rewrite deriveM // !derive_val.
Qed.

Global Instance is_deriveX f n (x v : V) (df : R) :
  is_derive x v f df -> is_derive x v (f ^+ n.+1) ((n.+1%:R * f x ^+n) *: df).
Proof.
move=> dfx; elim: n => [|n ihn]; first by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_derive_eq.
rewrite scalerA -scalerDl mulrCA -[f x * _]exprS.
by rewrite [in LHS]mulr_natl exprfctE -mulrSr mulr_natl.
Qed.

Lemma derivableX f n (x v : V) : derivable f x v -> derivable (f ^+ n) x v.
Proof. by case: n => [_|n /derivableP]; [rewrite expr0|]. Qed.

Lemma deriveX f n (x v : V) : derivable f x v ->
  'D_v (f ^+ n.+1) x = (n.+1%:R * f x ^+ n) *: 'D_v f x.
Proof. by move=> /derivableP df; rewrite derive_val. Qed.

Fact der_inv f (x v : V) : f x != 0 -> derivable f x v ->
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
  by apply: cvgM => //; apply: cvgN; rewrite expr2 invfM; apply: cvgM;
     [exact: cvg_cst|  exact: cvgV].
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

Lemma derivableV f (x v : V) :
  f x != 0 -> derivable f x v -> derivable (fun y => (f y)^-1) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (- (f x) ^- 2 *: 'D_v f x).
exact: der_inv.
Qed.

End Derive_lemmasVR.

Lemma derive_shift {R : numFieldType} (v k : R) :
  'D_v (shift k : R^o -> R^o) = cst v.
Proof.
by apply/funext => x/=; rewrite deriveD// derive_id derive_cst addr0.
Qed.

Lemma is_derive_shift {R : numFieldType} x v (k : R) :
  is_derive x v (shift k : R^o -> R^o) v.
Proof. by apply: DeriveDef => //; rewrite derive_val addr0. Qed.

Lemma derive1_cst {R : numFieldType} (k : R) t : (cst k)^`() t = 0.
Proof. by rewrite derive1E derive_cst. Qed.

Lemma exprn_derivable {R : numFieldType} n (x : R) v :
  derivable (@GRing.exp R ^~ n) x v.
Proof.
elim: n => [/=|n ih]; first by rewrite (_ : _ ^~ _ = 1).
rewrite (_ : _ ^~ _ = (fun x => x * x ^+ n)); last first.
  by apply/funext => y; rewrite exprS.
by apply: derivableM; first exact: derivable_id.
Qed.

Lemma exp_derive {R : numFieldType} n x v :
  'D_v (@GRing.exp R ^~ n.+1) x = n.+1%:R *: x ^+ n *: v.
Proof.
have /= := @deriveX R R id n x v (@derivable_id _ _ _ _).
by rewrite fctE => ->; rewrite derive_id.
Qed.

Lemma exp_derive1 {R : numFieldType} n x :
  (@GRing.exp R ^~ n.+1)^`() x = n.+1%:R *: x ^+ n.
Proof. by rewrite derive1E exp_derive [LHS]mulr1. Qed.

Lemma EVT_max (R : realType) (f : R -> R) (a b : R) : (* TODO : Filter not infered *)
  a <= b -> {within `[a, b], continuous f} -> exists2 c, c \in `[a, b]%R &
  forall t, t \in `[a, b]%R -> f t <= f c.
Proof.
move=> leab fcont; set imf := f @` `[a, b].
have imf_sup : has_sup imf.
  split; first by exists (f a); apply/imageP; rewrite /= in_itv /= lexx.
  have [M [Mreal imfltM]] : bounded_set (f @` `[a, b]).
    by apply/compact_bounded/continuous_compact => //; exact: segment_compact.
  exists (M + 1) => y /imfltM yleM.
  by rewrite (le_trans _ (yleM _ _)) ?ler_norm ?ltrDl.
have [|imf_ltsup] := pselect (exists2 c, c \in `[a, b]%R & f c = sup imf).
  move=> [c cab fceqsup]; exists c => // t tab; rewrite fceqsup.
  by apply/sup_upper_bound => //; exact/imageP.
have {}imf_ltsup t : t \in `[a, b]%R -> f t < sup imf.
  move=> tab; case: (ltrP (f t) (sup imf)) => // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //; apply/eqP.
  by rewrite eq_le supleft andbT sup_upper_bound//; exact/imageP.
pose g t : R := (sup imf - f t)^-1.
have invf_continuous : {within `[a, b], continuous g}.
  rewrite continuous_subspace_in => t tab; apply: cvgV => //=.
    by rewrite subr_eq0 gt_eqF // imf_ltsup //; rewrite inE in tab.
  by apply: cvgD; [exact: cst_continuous | apply: cvgN; exact: (fcont t)].
have /ex_strict_bound_gt0 [k k_gt0 /= imVfltk] : bounded_set (g @` `[a, b]).
  apply/compact_bounded/continuous_compact; last exact: segment_compact.
  exact: invf_continuous.
have [_ [t tab <-]] : exists2 y, imf y & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
rewrite ltrBlDr -ltrBlDl.
suff : sup imf - f t > k^-1 by move=> /ltW; rewrite leNgt => /negbTE ->.
rewrite -[ltRHS]invrK ltf_pV2// ?qualifE/= ?invr_gt0 ?subr_gt0 ?imf_ltsup//.
by rewrite (le_lt_trans (ler_norm _) _) ?imVfltk//; exact: imageP.
Qed.

Lemma EVT_min (R : realType) (f : R -> R) (a b : R) :
  a <= b -> {within `[a, b], continuous f} -> exists2 c, c \in `[a, b]%R &
  forall t, t \in `[a, b]%R -> f c <= f t.
Proof.
move=> leab fcont.
have /(EVT_max leab) [c clr fcmax] : {within `[a, b], continuous (- f)}.
  by move=> ?; apply: continuousN => ?; exact: fcont.
by exists c => // ? /fcmax; rewrite lerN2.
Qed.

Lemma cvg_at_rightE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ at_right x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_right _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _]; apply: xe_A.
Qed.
Arguments cvg_at_rightE {R V} f x.

Lemma cvg_at_leftE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ at_left x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_left _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _].
by apply: xe_A => //; rewrite eq_sym.
Qed.
Arguments cvg_at_leftE {R V} f x.

Lemma derive1_at_max (R : realFieldType) (f : R -> R) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[%R -> derivable f t 1) -> c \in `]a, b[%R ->
  (forall t, t \in `]a, b[%R -> f t <= f c) -> is_derive c 1 f 0.
Proof.
move=> leab fdrvbl cab cmax; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ['D_1 f c]cvg_at_rightE; last exact: fdrvbl.
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
rewrite ['D_1 f c]cvg_at_leftE; last exact: fdrvbl.
apply: limr_ge.
  have /fdrvbl dfc := cab; rewrite -(cvg_at_leftE (fun h => h^-1 *: ((f \o shift c) _ - f c))) //.
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

Lemma derive1_at_min (R : realFieldType) (f : R -> R) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[%R -> derivable f t 1) -> c \in `]a, b[%R ->
  (forall t, t \in `]a, b[%R -> f c <= f t) -> is_derive c 1 f 0.
Proof.
move=> leab fdrvbl cab cmin; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite -oppr_eq0; apply/eqP.
rewrite -deriveN; last exact: fdrvbl.
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
apply/eqP; rewrite eq_le fcmax; last by rewrite in_itv /= !ltW ?(itvP sab).
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
  rewrite [_ *: _]mulrC divfK; first by rewrite addrC subrK.
  by apply: lt0r_neq0; rewrite subr_gt0.
have [c cab dgc0] := Rolle altb gdrvbl gcont gaegb.
exists c; first exact: cab.
have /fdrvbl dfc := cab; move/@derive_val: dgc0; rewrite deriveB //.
move/eqP; rewrite [X in _ - X]deriveE // derive_val diff_val scale1r subr_eq0.
move/eqP->; rewrite -mulrA mulVf ?mulr1 //; apply: lt0r_neq0.
by rewrite subr_gt0.
Qed.

(* Weakens MVT to work when the interval is a single point. *)
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

Lemma ler0_derive1_nincr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> f^`() x <= 0) ->
  {within `[a, b], continuous f} ->
  forall x y, a <= x -> x <= y -> y <= b -> f y <= f x.
Proof.
move=> fdrvbl dfle0 ctsf x y leax lexy leyb; rewrite -subr_ge0.
case: ltgtP lexy => // [xlty|->]; last by rewrite subrr.
have itvW : {subset `[x, y]%R <= `[a, b]%R}.
  by apply/subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have itvWlt : {subset `]x, y[%R <= `]a, b[%R}.
  by apply subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have fdrv z : z \in `]x, y[%R -> is_derive z 1 f (f^`()z).
  rewrite in_itv/= => /andP[xz zy]; apply: DeriveDef; last by rewrite derive1E.
  by apply: fdrvbl; rewrite in_itv/= (le_lt_trans _ xz)// (lt_le_trans zy).
have [] := @MVT _ f (f^`()) x y xlty fdrv.
  apply: (@continuous_subspaceW _ _ _ `[a, b]); first exact: itvW.
  by rewrite continuous_subspace_in.
move=> t /itvWlt dft dftxy _; rewrite -oppr_le0 opprB dftxy.
by apply: mulr_le0_ge0 => //; [exact: dfle0|by rewrite subr_ge0 ltW].
Qed.

Lemma ltr0_derive1_decr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> f^`() x < 0) ->
  {within `[a, b], continuous f}%classic ->
  forall x y, a <= x -> x < y -> y <= b -> f y < f x.
Proof.
move=> fdrvbl dflt0 ctsf x y leax ltxy leyb; rewrite -subr_gt0.
case: ltgtP ltxy => // xlty _.
have itvW : {subset `[x, y]%R <= `[a, b]%R}.
  by apply/subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have itvWlt : {subset `]x, y[%R <= `]a, b[%R}.
  by apply subitvP; rewrite /<=%O /= /<=%O /= leyb leax.
have fdrv z : z \in `]x, y[%R -> is_derive z 1 f (f^`()z).
  rewrite in_itv/= => /andP[xz zy]; apply: DeriveDef; last by rewrite derive1E.
  by apply: fdrvbl; rewrite in_itv/= (le_lt_trans _ xz)// (lt_le_trans zy).
have [] := @MVT _ f (f^`()) x y xlty fdrv.
  apply: (@continuous_subspaceW _ _ _ `[a, b]); first exact: itvW.
  by rewrite continuous_subspace_in.
move=> t /itvWlt dft dftxy; rewrite -oppr_lt0 opprB dftxy.
by rewrite pmulr_llt0 ?subr_gt0// dflt0.
Qed.

Lemma gtr0_derive1_incr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> 0 < f^`() x) ->
  {within `[a, b], continuous f}%classic ->
  forall x y, a <= x -> x < y -> y <= b -> f x < f y.
Proof.
move=> fdrvbl dfgt0 ctsf x y leax ltxy leyb.
rewrite -ltrN2; apply: (@ltr0_derive1_decr _ (\- f) a b).
- by move=> z zab; apply: derivableN; exact: fdrvbl.
- move=> z zab; rewrite derive1E deriveN; last exact: fdrvbl.
  by rewrite ltrNl oppr0 -derive1E dfgt0.
- by move=> z; apply: continuousN; exact: ctsf.
- exact: leax.
- exact: ltxy.
- exact: leyb.
Qed.

Lemma ler0_derive1_nincry {R : realType} (f : R -> R) (a : R) :
  (forall x, x \in `]a, +oo[%R -> derivable f x 1) ->
  (forall x, x \in `]a, +oo[%R -> f^`() x <= 0) ->
  {within `[a, +oo[, continuous f} ->
  forall x y, a <= x -> x <= y -> f y <= f x.
Proof.
move=> fdrvbl dfle0 fcont x y ax xy.
near (pinfty_nbhs R)%R => N.
apply: (@ler0_derive1_nincr _ _ a N) => //.
- move=> r /[!in_itv]/= /andP[ar rN].
  by apply: fdrvbl; rewrite !in_itv/= andbT ar.
- move=> r /[!in_itv]/= /andP[ar rN].
  by apply: dfle0; rewrite !in_itv/= andbT ar.
- apply: continuous_subspaceW fcont.
  exact: subset_itvl.
- near: N.
  apply: nbhs_pinfty_ge.
  by rewrite num_real.
Unshelve. all: end_near. Qed.

Lemma ler0_derive1_nincrNy {R : realType} (f : R -> R) (b : R) :
  (forall x, x \in `]-oo, b[%R -> derivable f x 1) ->
  (forall x, x \in `]-oo, b[%R -> f^`() x <= 0) ->
  {within `]-oo, b], continuous f} ->
  forall x y, x <= y -> y <= b -> f y <= f x.
Proof.
move=> fdrvbl dfle0 fcont x y ax xy.
near (ninfty_nbhs R)%R => N.
apply: (@ler0_derive1_nincr _ _ N b) => //.
- move=> r /[!in_itv]/= /andP[Nr rb].
  by apply: fdrvbl; rewrite !in_itv/= rb.
- move=> r /[!in_itv]/= /andP[Nr rb].
  by apply: dfle0; rewrite !in_itv/= rb.
- apply: continuous_subspaceW fcont.
  exact: subset_itvr.
- near: N.
  apply: nbhs_ninfty_le.
  by rewrite num_real.
Unshelve. all: end_near. Qed.

Lemma ger0_derive1_ndecr (R : realType) (f : R -> R) (a b : R) :
  (forall x, x \in `]a, b[%R -> derivable f x 1) ->
  (forall x, x \in `]a, b[%R -> 0 <= f^`() x) ->
  {within `[a,b], continuous f} ->
  forall x y, a <= x -> x <= y -> y <= b -> f x <= f y.
Proof.
move=> fdrvbl dfge0 fcont x y; rewrite -[f _ <= _]lerN2.
apply (@ler0_derive1_nincr _ (- f)) => t tab; first exact/derivableN/fdrvbl.
  rewrite derive1E deriveN; last exact: fdrvbl.
  by rewrite oppr_le0 -derive1E; apply: dfge0.
by apply: continuousN; exact: fcont.
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0",
  note="renamed to `ger0_derive1_ndecr`")]
Notation le0r_derive1_ndecr := ger0_derive1_ndecr (only parsing).

Lemma ger0_derive1_ndecry {R : realType} (f : R -> R) (a b : R) :
  (forall x, x \in `]a, +oo[%R -> derivable f x 1) ->
  (forall x, x \in `]a, +oo[%R -> 0 <= f^`() x) ->
  {within `[a, +oo[, continuous f} ->
  forall x y, a <= x -> x <= y -> f x <= f y.
Proof.
move=> fdrvbl dfge0 fcont x y ax xy; rewrite -[f _ <= _]lerN2.
apply: (@ler0_derive1_nincry _ (- f)) => //.
- move=> r /[!in_itv]/=/[!andbT] xr; apply/derivableN.
  by apply: fdrvbl; rewrite !in_itv/= andbT (le_lt_trans ax).
- move=> r /[!in_itv]/=/[!andbT] /(le_lt_trans ax) xr.
  rewrite derive1E deriveN; last by (apply: fdrvbl; rewrite in_itv/= andbT).
  by rewrite -derive1E oppr_le0; apply: dfge0; rewrite in_itv/= andbT.
- move=> r; apply: continuousN; move: r.
  apply: continuous_subspaceW fcont.
  exact: subset_itvr.
Qed.

Lemma ger0_derive1_ndecrNy {R : realType} (f : R -> R) (b : R) :
  (forall x, x \in `]-oo, b[%R -> derivable f x 1) ->
  (forall x, x \in `]-oo, b[%R -> 0 <= f^`() x) ->
  {within `]-oo, b], continuous f} ->
  forall x y, x <= y -> y <= b -> f x <= f y.
Proof.
move=> fdrvbl dfge0 fcont x y xy yb; rewrite -[f _ <= _]lerN2.
apply: (@ler0_derive1_nincrNy _ (- f)) => //.
- move=> r /[!in_itv]/= ry; apply/derivableN.
  by apply: fdrvbl; rewrite !in_itv/= (lt_le_trans ry).
- move=> r /[!in_itv]/= ry; have rb := lt_le_trans ry yb.
  rewrite derive1E deriveN; last by (apply: fdrvbl; rewrite in_itv/=).
  by rewrite -derive1E oppr_le0; apply: dfge0; rewrite in_itv/=.
- move=> r; apply: continuousN; move: r.
  apply: continuous_subspaceW fcont.
  exact: subset_itvl.
Qed.

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
have h0 : h != 0%R by near: h; exact: nbhs_dnbhs_neq.
have Dhx : D° (h + x).
  apply: (Hball (`|2 * h|%R)) => //.
  - rewrite /= sub0r normrN normr_id normrM ger0_norm// -ltr_pdivlMl//.
      by near: h; apply: dnbhs0_lt; exact: mulr_gt0.
    by rewrite normrM ger0_norm// mulr_gt0// normr_gt0.
  apply: ball_sym; rewrite /ball/= addrK.
  by rewrite normrM ger0_norm// ltr_pMl ?normr_gt0// ltr1n.
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

Lemma derive1_comp (R : realFieldType) (f g : R -> R) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  (g \o f)^`() x = g^`()%classic (f x) * f^`()%classic x.
Proof.
move=> /derivable1_diffP df /derivable1_diffP dg.
rewrite derive1E'; last exact/differentiable_comp.
rewrite diff_comp // !derive1E' //= -[X in 'd  _ _ X = _]mulr1.
by rewrite [LHS]linearZ mulrC.
Qed.

Section near_derive.
Context (R : numFieldType) (V W : normedModType R).
Variables (f g : V -> W) (a v : V).
Hypotheses (v0 : v != 0) (afg : {near a, f =1 g}).

Let near_derive :
  {near 0^', (fun h => h^-1 *: (f (h *: v + a) - f a)) =1
             (fun h => h^-1 *: (g (h *: v + a) - g a))}.
Proof.
near do congr (_ *: _).
move: afg; rewrite {1}/prop_near1/= nbhsE/= => -[B [oB Ba] /[dup] Bfg Bfg'].
have [e /= e0 eB] := open_subball oB Ba.
have vv0 : 0 < `|2 *: v| by rewrite normrZ mulr_gt0 ?normr_gt0.
near=> x.
have x0 : 0 < `|x| by rewrite normr_gt0//; near: x; exact: nbhs_dnbhs_neq.
congr (_ - _); last exact: Bfg'.
apply: Bfg; apply: (eB (`|x| * `|2 *: v|)).
- rewrite /ball_/= sub0r normrN normrM !normr_id -ltr_pdivlMr//.
  by near: x; apply: dnbhs0_lt; rewrite divr_gt0.
- by rewrite mulr_gt0.
- rewrite -ball_normE/= opprD addrCA subrr addr0 normrN normrZ ltr_pM2l//.
  by rewrite normrZ ltr_pMl ?normr_gt0// gtr0_norm ?ltr1n.
Unshelve. all: by end_near. Qed.

Lemma near_eq_derivable : derivable f a v -> derivable g a v.
Proof.
move=> /cvg_ex[/= l fl]; apply/cvg_ex; exists l => /=.
by apply: cvg_trans fl; apply: near_eq_cvg; exact: near_derive.
Qed.

Lemma near_eq_derive : 'D_v f a = 'D_v g a.
Proof.
rewrite /derive; congr (lim _).
have {}fg := near_derive.
rewrite eqEsubset; split; apply: near_eq_cvg=> //.
by move/filterS : fg; apply => ? /esym.
Qed.

Lemma near_eq_is_derive (df : W) : is_derive a v f df -> is_derive a v g df.
Proof.
move=> [fav <-]; rewrite near_eq_derive.
by apply: DeriveDef => //; exact: near_eq_derivable fav.
Qed.

End near_derive.

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
Variable (R : realFieldType).
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
rewrite derive1E deriveD//; [|exact: derivable_horner..].
rewrite -!derive1E hornerC_ext derive1_cst addr0.
rewrite horner_scale_ext derive1E deriveM//; last exact: derivable_horner.
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
