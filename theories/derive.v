(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop order matrix interval.
Require Import boolp reals.
Require Import classical_sets posnum topology prodnormedzmodule normedtype landau forms.

(******************************************************************************)
(* This file provides a theory of differentiation. It includes the standard   *)
(* rules of differentiation (differential of a sum, of a product, of          *)
(* exponentiation, of the inverse, etc.) as well standard theorems (the       *)
(* Extreme Value Theorem, Rolle's theorem, the Mean Value Theorem).           *)
(*                                                                            *)
(* Parsable notations:                                                        *)
(*               'd f x == the differential of a function f at a point x      *)
(*   differentiable f x == the function f is differentiable at a point x      *)
(*               'J f x == the Jacobian of f at a point x                     *)
(*               'D_v f == the directional derivative of f along v            *)
(*               f^`()  == the derivative of f of domain R                    *)
(*               f^`(n) == the nth derivative of f of domain R                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

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
Reserved Notation "f ^` ()" (at level 8, format "f ^` ()").
Reserved Notation "f ^` ( n )" (at level 8, format "f ^` ( n )").

Section Differential.
Context {K : numDomainType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => continuous df /\ forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).

Local Notation "''d' f x" := (@diff _ (Phantom _ [filter of x]) f).

Fact diff_key : forall T, T -> unit. Proof. by constructor. Qed.
CoInductive differentiable_def (f : V -> W) (x : filter_on V)
  (phF : phantom (set (set V)) x) : Prop := DifferentiableDef of
  (continuous ('d f x) /\
  f = cst (f (lim x)) + 'd f x \o center (lim x) +o_x (center (lim x))).

Local Notation differentiable f F := (@differentiable_def f _ (Phantom _ [filter of F])).

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
  [o_x e of f] = [o_ (0 : V) (e \o shift x) of f \o shift x] \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP => _/posnumP[eps].
  rewrite [\forall x \near _, _ <= _](near_shift x) sub0r; near=> y.
  by rewrite /= subrK; near: y; have /eqoP := littleo_eqo g; apply.
rewrite insubF //; apply/asboolP => fe; apply: Nfe => _/posnumP[eps].
by rewrite [\forall x \near _, _ <= _](near_shift 0) subr0; apply: fe.
Grab Existential Variables. end_near. Qed.

End Differential.

Section Differential_numFieldType.
Context {K : numFieldType (*TODO: to numDomainType?*)} {V W : normedModType K}.

(* duplicate from Section Differential *)
Local Notation differentiable f F := (@differentiable_def _ _ _ f _ (Phantom _ [filter of F])).
Local Notation "''d' f x" := (@diff _ _ _ _ (Phantom _ [filter of x]) f).
Hint Extern 0 (continuous _) => exact: diff_continuous : core.

Lemma diff_locallyxP (x : V) (f : V -> W) :
  differentiable f x <-> continuous ('d f x) /\
  forall h, f (h + x) = f x + 'd f x h +o_(h \near 0 : V) h.
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
  forall h, f (h + x) = f x + 'd f x h +o_(h \near 0 : V) h.
Proof. by move=> /diff_locallyxP []. Qed.

Lemma diff_locallyxC (x : V) (f : V -> W) : differentiable f x ->
  forall h, f (x + h) = f x + 'd f x h +o_(h \near 0 : V) h.
Proof. by move=> ?; apply/eqaddoEx => h; rewrite [x + h]addrC diff_locallyx. Qed.

Lemma diff_locallyP (x : V) (f : V -> W) :
  differentiable f x <->
  continuous ('d f x) /\ (f \o shift x = cst (f x) + 'd f x +o_ (0 : V) id).
Proof. by apply: iff_trans (diff_locallyxP _ _) _; rewrite funeqE. Qed.

Lemma diff_locally (x : V) (f : V -> W) : differentiable f x ->
  (f \o shift x = cst (f x) + 'd f x +o_ (0 : V) id).
Proof. by move=> /diff_locallyP []. Qed.

End Differential_numFieldType.

Notation "''d' f F" := (@diff _ _ _ _ (Phantom _ [filter of F]) f).
Notation differentiable f F := (@differentiable_def _ _ _ f _ (Phantom _ [filter of F])).

Notation "'is_diff' F" := (is_diff_def (Phantom _ [filter of F])).
Hint Extern 0 (differentiable _ _) => solve[apply: ex_diff] : core.
Hint Extern 0 ({for _, continuous _}) => exact: diff_continuous : core.

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
rewrite (littleo_bigO_eqo (cst (1 : R^o))); last first.
  apply/eqOP; near=> k; rewrite /cst [`|1 : R^o|]normr1 mulr1.
  near=> y; rewrite ltW //; near: y; apply/locally_normP.
  by exists k; [near: k; exists 0; rewrite real0|move=> ? /=; rewrite sub0r normrN].
rewrite addfo; first by move=> /eqolim; rewrite cvg_shift add0r.
by apply/eqolim0P; apply: (cvg_trans (dfc 0)); rewrite linear0.
Grab Existential Variables. all: end_near. Qed.

Section littleo_lemmas.

Variables (X Y Z : normedModType R).

Lemma normm_littleo x (f : X -> Y) : `| [o_(x \near x) (1 : R^o) of f x]| = 0.
Proof.
rewrite /cst /=; have [e /(_ (`|e x|/2) _)/locally_singleton /=] := littleo.
rewrite pmulr_lgt0 // [`|1 : R^o|]normr1 mulr1 [X in X <= _]splitr.
rewrite ger_addr pmulr_lle0 // => /implyP.
case : real_ltgtP; rewrite ?realE ?normrE //=.
by apply/orP; left.
Qed.

Lemma littleo_lim0 (f : X -> Y) (h : _ -> Z) (x : X) :
  f @ x --> (0 : Y) -> [o_x f of h] x = 0.
Proof.
move/eqolim0P => ->; have [k /(_ _ [gt0 of 1])/=] := littleo.
by move=> /locally_singleton; rewrite mul1r normm_littleo normr_le0 => /eqP.
Qed.

End littleo_lemmas.

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)
(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential being b *: idfun is locally bounded *)
(* and thus a littleo of 1, and so is id *)
(* This can be generalized to any dimension *)
Lemma diff_locally_converse_part1 (f : R^o -> R^o) (a : R^o) (b : R^o) (x : R^o) :
  f \o shift x = cst a + b *: idfun +o_ (0 : [filteredType R^o of R^o]) id -> f x = a.
Proof.
rewrite funeqE => /(_ 0) /=; rewrite add0r => ->.
by rewrite -[LHS]/(_ 0 + _ 0 + _ 0) /cst [X in a + X]scaler0 littleo_lim0 ?addr0.
Qed.

End diff_locally_converse_tentative.

Definition derive (f : V -> W) a v :=
  lim ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ locally' (0 : R^o)).

Local Notation "''D_' v f" := (derive f ^~ v).
Local Notation "''D_' v f c" := (derive f c v). (* printing *)

Definition derivable (f : V -> W) a v :=
  cvg ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ locally' (0 : R^o)).

Class is_derive (a v : V) (f : V -> W) (df : W) := DeriveDef {
  ex_derive : derivable f a v;
  derive_val : 'D_v f a = df
}.

Lemma derivable_locally (f : V -> W) a v :
  derivable f a v ->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (locally (0 : [filteredType R^o of R^o])) id.
Proof.
move=> df; apply/eqaddoP => _/posnumP[e].
rewrite -locally_nearE locally_simpl /= locallyE'; split; last first.
  rewrite /at_point opprD -![(_ + _ : _ -> _) _]/(_ + _) scale0r add0r.
  by rewrite addrA subrr add0r normrN scale0r !normr0 mulr0.
have /eqolimP := df; rewrite -[lim _]/(derive _ _ _).
move=> /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]).
apply: filter_app; rewrite /= !near_simpl near_withinE; near=> h => hN0.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|1 : R^o|]normr1 mulr1 => dfv.
rewrite addrA -[X in X + _]scale1r -(@mulVf _ h) //.
rewrite mulrC -scalerA -scalerBr normmZ.
rewrite -ler_pdivl_mull; last by rewrite normr_gt0.
by rewrite mulrCA mulVf ?mulr1; last by rewrite normr_eq0.
Grab Existential Variables. all: end_near. Qed.

Lemma derivable_locallyP (f : V -> W) a v :
  derivable f a v <->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (locally (0 : [filteredType R^o of R^o])) id.
Proof.
split; first exact: derivable_locally.
move=> df; apply/cvg_ex; exists ('D_v f a).
apply/(@eqolimP _ R^o _ (locally'_filter_on _))/eqaddoP => _/posnumP[e].
have /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]) := df.
rewrite /= !(near_simpl, near_withinE); apply: filter_app; near=> h.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|1 : R^o|]normr1 mulr1 addrA => dfv hN0.
rewrite -[X in _ - X]scale1r -(@mulVf _ h) //.
rewrite -scalerA -scalerBr normmZ normfV ler_pdivr_mull ?normr_gt0 //.
by rewrite mulrC.
Grab Existential Variables. all: end_near. Qed.

Lemma derivable_locallyx (f : V -> W) a v :
  derivable f a v -> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (locally (0 : [filteredType R^o of R^o]))) h.
Proof.
move=> /derivable_locally; rewrite funeqE => df.
by apply: eqaddoEx => h; have /= := (df h); rewrite addrC => ->.
Qed.

Lemma derivable_locallyxP (f : V -> W) a v :
  derivable f a v <-> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (locally (0 : [filteredType R^o of R^o]))) h.
Proof.
split; first exact: derivable_locallyx.
move=> df; apply/derivable_locallyP; apply/eqaddoE; rewrite funeqE => h.
by rewrite /= addrC df.
Qed.

End DifferentialR.

Notation "''D_' v f" := (derive f ^~ v).
Notation "''D_' v f c" := (derive f c v). (* printing *)
Hint Extern 0 (derivable _ _ _) => solve[apply: ex_derive] : core.

Section DifferentialR_numFieldType.
Context {R : numFieldType} {V W : normedModType R}.

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable f a -> 'D_v f a = 'd f a v.
Proof.
rewrite /derive => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE=> h; rewrite !scalerDr scalerN /cst /=.
  by rewrite addrC !addrA addNr add0r linearZ /= scalerA /g.
apply: cvg_map_lim => //.
pose g1 : R -> W := fun h => (h^-1 * h) *: 'd f a v.
pose g2 : R -> W := fun h : R => h^-1 *: k (h *: v ).
rewrite (_ : g = g1 + g2) ?funeqE // -(addr0 (_ _ v)); apply: (@cvgD _ _ [topologicalType of R^o]).
  rewrite -(scale1r (_ _ v)); apply: cvgZl => /= X [e e0].
  rewrite /ball_ /= => eX.
  apply/locallyP; rewrite locally_E.
  by exists e => //= x _ x0; apply eX; rewrite mulVr // ?unitfE // subrr normr0.
rewrite /g2.
have [/eqP ->|v0] := boolP (v == 0).
  rewrite (_ : (fun _ => _) = cst 0); first exact: cvg_cst.
  by rewrite funeqE => ?; rewrite scaler0 /k littleo_lim0 // scaler0.
apply/cvg_distP => e e0.
rewrite nearE /=; apply/locallyP; rewrite locally_E.
have /(littleoP [littleo of k]) /locallyP[i i0 Hi] : 0 < e / (2 * `|v|).
  by rewrite divr_gt0 // pmulr_rgt0 // normr_gt0.
exists (i / `|v|); first by rewrite divr_gt0 // normr_gt0.
move=> /= j; rewrite /ball /= /ball_ add0r normrN.
rewrite ltr_pdivl_mulr ?normr_gt0 // => jvi j0.
rewrite add0r normrN normmZ -ltr_pdivl_mull ?normr_gt0 ?invr_neq0 //.
have /Hi/le_lt_trans -> // : ball 0 i (j *: v).
  by rewrite -ball_normE /ball_ add0r normrN (le_lt_trans _ jvi) // normmZ.
rewrite -(mulrC e) -mulrA -ltr_pdivl_mull // mulrA mulVr ?unitfE ?gt_eqF //.
rewrite normrV ?unitfE // div1r invrK ltr_pdivr_mull; last first.
  by rewrite pmulr_rgt0 // normr_gt0.
rewrite normmZ mulrC -mulrA.
by rewrite ltr_pmull ?ltr1n // pmulr_rgt0 ?normm_gt0 // normr_gt0.
Qed.

End DifferentialR_numFieldType.

Section DifferentialR2.
Variable R : numFieldType.
Implicit Type (V : normedModType R).

Lemma derivemxE m n (f : 'rV[R]_m.+1 -> 'rV[R]_n.+1) (a v : 'rV[R^o]_m.+1) :
  differentiable f a -> 'D_ v f a = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

Definition derive1 V (f : R -> V) (a : R) :=
   lim ((fun h => h^-1 *: (f (h + a) - f a)) @ locally' (0 : R^o)).

Local Notation "f ^` ()" := (derive1 f).

Lemma derive1E V (f : R -> V) a : f^`() a = 'D_1 (f : R^o -> _) a.
Proof.
rewrite /derive1 /derive; set d := (fun _ : R => _); set d' := (fun _ : R => _).
by suff -> : d = d' by []; rewrite funeqE=> h; rewrite /d /d' /= [h%:A](mulr1).
Qed.

(* Is it necessary? *)
Lemma derive1E' V f a : differentiable (f : R^o -> V) a ->
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

Notation "f ^` ()" := (derive1 f).
Notation "f ^` ( n )" := (derive1n n f).

Section DifferentialR3.
Variable R : numFieldType.

Fact dcst (V W : normedModType R) (a : W) (x : V) : continuous (0 : V -> W) /\
  cst a \o shift x = cst (cst a x) + \0 +o_ (0 : V) id.
Proof.
split; first exact: continuous_cst.
apply/eqaddoE; rewrite addr0 funeqE => ? /=; rewrite -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof.
Qed.

Variables (V W : normedModType R).

Fact dadd (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  continuous ('d f x \+ 'd g x) /\
  (f + g) \o shift x = cst ((f + g) x) + ('d f x \+ 'd g x) +o_ (0 : V) id.
Proof.
move=> df dg; split => [?|]; do ?exact: continuousD.
apply/(@eqaddoE R); rewrite funeqE => y /=; rewrite -[(f + g) _]/(_ + _).
by rewrite ![_ (_ + x)]diff_locallyx// addrACA addox addrACA.
Qed.

Fact dopp (f : V -> W) x :
  differentiable f x -> continuous (- ('d f x : V -> W)) /\
  (- f) \o shift x = cst (- f x) \- 'd f x +o_ (0 : V) id.
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
  (k *: f) \o shift x = cst ((k *: f) x) + k \*: 'd f x +o_ (0 : V) id.
Proof.
move=> df; split; first by move=> ?; apply: continuousZr.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(k *: f) _]/(_ *: _) diff_locallyx // !scalerDr scaleox.
Qed.

(* NB: could be generalized with K : absRingType instead of R; DONE? *)
Fact dscalel (k : V -> R^o) (f : W) x :
  differentiable k x ->
  continuous (fun z : V => 'd k x z *: f) /\
  (fun z => k z *: f) \o shift x =
    cst (k x *: f) + (fun z => 'd k x z *: f) +o_ (0 : V) id.
Proof.
move=> df; split.
  move=> ?; exact/continuousZl/(@diff_continuous _ _ [normedModType R of R^o]).
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite diff_locallyx //= !scalerDl scaleolx.
Qed.

Fact dlin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> f \o shift x = cst (f x) + f +o_ (0 : V') id.
Proof.
move=> df; apply: eqaddoE; rewrite funeqE => y /=.
rewrite linearD addrC -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof. (*fixme*)
Qed.

(* TODO: generalize *)
Lemma compoO_eqo (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') :
  [o_ (0 : V') id of g] \o [O_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ (0 : U) id of f]].
have := littleoP [littleo of [o_ (0 : V') id of g]].
move=>  /(_ (e%:num / k%:num)) /(_ _) /locallyP [//|_ /posnumP[d] hd].
apply: filter_app; near=> x => leOxkx; apply: le_trans (hd _ _) _; last first.
  rewrite -ler_pdivl_mull //; apply: le_trans leOxkx _.
  by rewrite invf_div mulrA -[_ / _ * _]mulrA mulVf // mulr1.
rewrite -ball_normE /= distrC subr0 (le_lt_trans leOxkx) //.
rewrite -ltr_pdivl_mull //; near: x; rewrite /= !locally_simpl.
apply/locallyP; exists (k%:num ^-1 * d%:num)=> // x.
by rewrite -ball_normE /= distrC subr0.
Grab Existential Variables. all: end_near. Qed.

Lemma compoO_eqox (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') :
  forall x : U, [o_ (0 : V') id of g] ([O_ (0 : U) id of f] x) =o_(x \near 0 : U) x.
Proof. by move=> x; rewrite -[X in X = _]/((_ \o _) x) compoO_eqo. Qed.

(* TODO: generalize *)
Lemma compOo_eqo  (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') :
  [O_ (0 : V') id of g] \o [o_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ (0 : V') id of g]].
move=> /locallyP [_ /posnumP[d] hd].
have ekgt0 : e%:num / k%:num > 0 by [].
have /(_ _ ekgt0) := littleoP [littleo of [o_ (0 : U) id of f]].
apply: filter_app; near=> x => leoxekx; apply: le_trans (hd _ _) _; last first.
  by rewrite -ler_pdivl_mull // mulrA [_^-1 * _]mulrC.
rewrite -ball_normE /= distrC subr0; apply: le_lt_trans leoxekx _.
rewrite -ltr_pdivl_mull //; near: x; rewrite /= locally_simpl.
apply/locallyP; exists ((e%:num / k%:num) ^-1 * d%:num)=> // x.
by rewrite -ball_normE /= distrC subr0.
Grab Existential Variables. all: end_near. Qed.

End DifferentialR3.

Section DifferentialR3_realFieldType.
Variable R : realFieldType.

Lemma littleo_linear0 (V W : normedModType R) (f : {linear V -> W}) :
  (f : V -> W) =o_ (0 : V) id -> f = cst 0 :> (V -> W).
Proof.
move/eqoP => oid.
rewrite funeqE => x; apply/eqP; case: (ler0P `|x|) => [|xn0].
  by rewrite normr_le0 => /eqP ->; rewrite linear0.
rewrite -normr_le0 -(mul0r `|x|) -ler_pdivr_mulr //.
apply/ler0_addgt0P => _ /posnumP[e]; rewrite ler_pdivr_mulr //.
have /oid /locallyP [_ /posnumP[d] dfe] := posnum_gt0 e.
set k := ((d%:num / 2) / (PosNum xn0)%:num)^-1.
rewrite -{1}(@scalerKV _ _ k _ x) // linearZZ normmZ.
rewrite -ler_pdivl_mull; last by rewrite gtr0_norm.
rewrite mulrCA (@le_trans _ _ (e%:num * `|k^-1 *: x|)) //; last first.
  by rewrite ler_pmul // normmZ normfV.
apply dfe.
rewrite -ball_normE /ball_ sub0r normrN normmZ.
rewrite invrK -ltr_pdivl_mulr // ger0_norm // ltr_pdivr_mulr //.
by rewrite -mulrA mulVf ?lt0r_neq0 // mulr1 [X in _ < X]splitr ltr_addl.
Qed.

Lemma diff_unique (V W : normedModType R) (f : V -> W)
  (df : {linear V -> W}) x :
  continuous df -> f \o shift x = cst (f x) + df +o_ (0 : V) id ->
  'd f x = df :> (V -> W).
Proof.
move=> dfc dxf; apply/subr0_eq; rewrite -[LHS]/(_ \- _).
apply/littleo_linear0/eqoP/eq_some_oP => /=; rewrite funeqE => y /=.
have hdf h :
  (f \o shift x = cst (f x) + h +o_ (0 : V) id) ->
  h = f \o shift x - cst (f x) +o_ (0 : V) id.
  move=> hdf; apply: eqaddoE.
  rewrite hdf addrAC (addrC _ h) addrK.
  rewrite -[LHS]addr0 -addrA; congr (_ + _).
  by apply/eqP; rewrite eq_sym addrC addr_eq0 oppo.
rewrite (hdf _ dxf).
suff /diff_locally /hdf -> : differentiable f x.
  by rewrite opprD addrCA -(addrA (_ - _)) addKr oppox addox.
apply/diffP; apply: (@getPex _ (fun (df : {linear V -> W}) => continuous df /\
  forall y, f y = f (lim x) + df (y - lim x) +o_(y \near x) (y - lim x))).
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
by move=> df dg; apply/diff_locallyP; rewrite diffD //; have := dadd df dg.
Qed.

Global Instance is_diffD (f g df dg : V -> W) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f + g) (df + dg).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiableD.
by rewrite diffD // !diff_val.
Qed.

Lemma differentiable_sum n (f : 'I_n -> V -> W) (x : V) :
  (forall i, differentiable (f i) x) -> differentiable (\sum_(i < n) f i) x.
Proof.
elim: n f => [f _| n IH f H]; first by rewrite big_ord0.
rewrite big_ord_recr /=; apply/differentiableD; [apply/IH => ? |]; exact: H.
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
Proof. by move=> /differentiableP df /differentiableP dg; rewrite diff_val. Qed.

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

Lemma diffZl (k : V -> R^o) (f : W) x : differentiable k x ->
  'd (fun z => k z *: f) x = (fun z => 'd k x z *: f) :> (_ -> _).
Proof.
move=> df; set g := RHS; have glin : linear g.
  by move=> a u v; rewrite /g linearP /= scalerDl -scalerA.
by apply:(@diff_unique _ _ _ (Linear glin)); have [] := dscalel f df.
Qed.

Lemma differentiableZl (k : V -> R^o) (f : W) x :
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
  by apply: (@linear_differentiable _ _ [linear of idfun]) => ? //.
by rewrite (@diff_lin _ _ [linear of idfun]) // => ? //.
Qed.

Global Instance is_diff_scaler (k : R) (x : V) : is_diff x ( *:%R k) ( *:%R k).
Proof.
apply: DiffDef; first exact/linear_differentiable/scaler_continuous.
by rewrite diff_lin //; apply: scaler_continuous.
Qed.

Global Instance is_diff_scalel (x k : [filteredType R^o of R^o]) :
  is_diff k ( *:%R ^~ x) ( *:%R ^~ x).
Proof.
have -> : *:%R ^~ x = GRing.scale_linear [lmodType R of R^o] x.
  by rewrite funeqE => ? /=; rewrite [_ *: _]mulrC.
apply: DiffDef; first exact/linear_differentiable/scaler_continuous.
by rewrite diff_lin //; apply: scaler_continuous.
Qed.

Lemma differentiable_coord m n (M : 'M[R^o]_(m.+1, n.+1)) i j :
  differentiable (fun N : 'M[R]_(m.+1, n.+1) => N i j : R^o) M.
Proof.
have @f : {linear 'M[R]_(m.+1, n.+1) -> R^o}.
  by exists (fun N : 'M[R]_(_, _) => N i j); eexists; move=> ? ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma linear_lipschitz (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> exists2 k, k > 0 & forall x, `|f x| <= k * `|x|.
Proof.
move=> /(_ 0); rewrite linear0 => /(_ _ (locally_ball 0 1%:pos)).
move=> /locallyP [_ /posnumP[e] he]; exists (2 / e%:num) => // x.
case: (lerP `|x| 0) => [|xn0].
  by rewrite normr_le0 => /eqP->; rewrite linear0 !normr0 mulr0.
set k := 2 / e%:num * (PosNum xn0)%:num.
have kn0 : k != 0 by [].
have abskgt0 : `|k| > 0 by rewrite normr_gt0.
rewrite -[x in X in X <= _](scalerKV kn0) linearZZ normmZ -ler_pdivl_mull //.
suff /he : ball 0 e%:num (k^-1 *: x).
  rewrite -ball_normE /= distrC subr0 => /ltW /le_trans; apply.
  by rewrite ger0_norm // mulVf.
rewrite -ball_normE /= distrC subr0 normmZ.
rewrite normfV ger0_norm // invrM ?unitfE // mulrAC mulVf //.
by rewrite invf_div mul1r [X in _ < X]splitr; apply: ltr_spaddr.
Qed.

Lemma linear_eqO (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> (f : V' -> W') =O_ (0 : V') id.
Proof.
move=> /linear_lipschitz [k kgt0 flip]; apply/eqO_exP; exists k => //.
exact: filterE.
Qed.

Lemma diff_eqO (V' W' : normedModType R) (x : filter_on V') (f : V' -> W') :
  differentiable f x -> ('d f x : V' -> W') =O_ (0 : V') id.
Proof. by move=> /diff_continuous /linear_eqO; apply. Qed.

Lemma compOo_eqox (U V' W' : normedModType R) (f : U -> V')
  (g : V' -> W') : forall x,
  [O_ (0 : V') id of g] ([o_ (0 : U) id of f] x) =o_(x \near 0 : U) x.
Proof. by move=> x; rewrite -[X in X = _]/((_ \o _) x) compOo_eqo. Qed.

Fact dcomp (U V' W' : normedModType R) (f : U -> V') (g : V' -> W') x :
  differentiable f x -> differentiable g (f x) ->
  continuous ('d g (f x) \o 'd f x) /\ forall y,
  g (f (y + x)) = g (f x) + ('d g (f x) \o 'd f x) y +o_(y \near 0 : U) y.
Proof.
move=> df dg; split; first by move=> ?; apply: continuous_comp.
apply: eqaddoEx => y; rewrite diff_locallyx// -addrA diff_locallyxC// linearD.
rewrite addrA -addrA; congr (_ + _ + _).
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
move=> /(_ 0); rewrite linear0r => /(_ _ (locally_ball 0 1%:pos)).
move=> /locallyP [_ /posnumP[e] he]; exists ((2 / e%:num) ^+2) => // u v.
case: (lerP `|u| 0) => [|un0].
  by rewrite normr_le0 => /eqP->; rewrite linear0l !normr0 mulr0 mul0r.
case: (lerP `|v| 0) => [|vn0].
  by rewrite normr_le0 => /eqP->; rewrite linear0r !normr0 mulr0.
rewrite -[`|u|]/((PosNum un0)%:num) -[`|v|]/((PosNum vn0)%:num).
set ku := 2 / e%:num * (PosNum un0)%:num.
set kv := 2 / e%:num * (PosNum vn0)%:num.
rewrite -[X in f X](@scalerKV _ _ ku) // linearZl_LR normmZ.
rewrite gtr0_norm // -ler_pdivl_mull //.
rewrite -[X in f _ X](@scalerKV _ _ kv) // linearZr_LR normmZ.
rewrite gtr0_norm // -ler_pdivl_mull //.
suff /he : ball 0 e%:num (ku^-1 *: u, kv^-1 *: v).
  rewrite -ball_normE /= distrC subr0 => /ltW /le_trans; apply.
  rewrite ler_pdivl_mull // mulr1 ler_pdivl_mull //.
  by rewrite mulrA [ku * _]mulrAC expr2.
rewrite -ball_normE /= distrC subr0.
have -> : (ku^-1 *: u, kv^-1 *: v) =
  (e%:num / 2) *: ((PosNum un0)%:num ^-1 *: u, (PosNum vn0)%:num ^-1 *: v).
  rewrite invrM ?unitfE // [kv ^-1]invrM ?unitfE //.
  rewrite mulrC -[_ *: u]scalerA [X in X *: v]mulrC -[_ *: v]scalerA.
  by rewrite invf_div.
rewrite normmZ ger0_norm // -mulrA gtr_pmulr // ltr_pdivr_mull // mulr1.
rewrite prod_normE /= (_ : _%:nng = 1%:nng); last first.
  by apply/val_inj => /=; rewrite normmZ normrV ?unitfE ?gt_eqF // normr_id mulVf ?gt_eqF.
rewrite (_ : _%:nng = 1%:nng); last first.
  by apply/val_inj => /=; rewrite normmZ normrV ?unitfE ?gt_eqF // normr_id mulVf ?gt_eqF.
by rewrite joinxx /= ltr1n.
Qed.

Lemma bilinear_eqo (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) :
  continuous (fun p => f p.1 p.2) -> (fun p => f p.1 p.2) =o_ (0 : U * V') id.
Proof.
move=> fc; have [_ /posnumP[k] fschwarz] := bilinear_schwarz fc.
apply/eqoP=> _ /posnumP[e]; near=> x; rewrite (le_trans (fschwarz _ _))//.
rewrite ler_pmul ?pmulr_rge0 //; last by rewrite nng_lexU /= lexx orbT.
rewrite -ler_pdivl_mull //.
suff : `|x| <= k%:num ^-1 * e%:num by apply: le_trans; rewrite nng_lexU /= lexx.
near: x; rewrite !near_simpl; apply/locally_le_locally_norm.
by exists (k%:num ^-1 * e%:num) => // ? /=; rewrite distrC subr0 => /ltW.
Grab Existential Variables. all: end_near. Qed.

Fact dbilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) ->
  continuous (fun q => (f p.1 q.2 + f q.1 p.2)) /\
  (fun q => f q.1 q.2) \o shift p = cst (f p.1 p.2) +
    (fun q => f p.1 q.2 + f q.1 p.2) +o_ (0 : U * V') id.
Proof.
move=> fc; split=> [q|].
  by apply: (@continuousD _ _ _ (fun q => f p.1 q.2) (fun q => f q.1 p.2));
    move=> A /(fc (_.1, _.2)) /= /locallyP [_ /posnumP[e] fpqe_A];
    apply/locallyP; exists e%:num => // r [??]; exact: (fpqe_A (_.1, _.2)).
apply/eqaddoE; rewrite funeqE => q /=.
rewrite linearDl !linearDr addrA addrC.
rewrite -[f q.1 _ + _ + _]addrA [f q.1 _ + _]addrC addrA [f q.1 _ + _]addrC.
by congr (_ + _); rewrite -[LHS]/((fun p => f p.1 p.2) q) bilinear_eqo.
Qed.

Lemma diff_bilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) -> 'd (fun q => f q.1 q.2) p =
  (fun q => f p.1 q.2 + f q.1 p.2) :> (U * V' -> W').
Proof.
move=> fc; have lind : linear (fun q => f p.1 q.2 + f q.1 p.2).
  by move=> ???; rewrite linearPr linearPl scalerDr addrACA.
have -> : (fun q => f p.1 q.2 + f q.1 p.2) = Linear lind by [].
by apply/diff_unique; have [] := dbilin p fc.
Qed.

Lemma differentiable_bilin (U V' W' : normedModType R)
  (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) -> differentiable (fun p => f p.1 p.2) p.
Proof.
by move=> fc; apply/diff_locallyP; rewrite diff_bilin //; apply: dbilin p fc.
Qed.

Definition Rmult_rev (y x : R) := x * y.
Canonical rev_Rmult := @RevOp _ _ _ Rmult_rev (@GRing.mul [ringType of R])
  (fun _ _ => erefl).

Lemma Rmult_is_linear x : linear (@GRing.mul [ringType of R] x : R^o -> R^o).
Proof. by move=> ???; rewrite mulrDr scalerAr. Qed.
Canonical Rmult_linear x := Linear (Rmult_is_linear x).

Lemma Rmult_rev_is_linear y : linear (Rmult_rev y : R^o -> R^o).
Proof. by move=> ???; rewrite /Rmult_rev mulrDl scalerAl. Qed.
Canonical Rmult_rev_linear y := Linear (Rmult_rev_is_linear y).

Canonical Rmult_bilinear :=
  [bilinear of (@GRing.mul [ringType of [lmodType R of R^o]])].

Global Instance is_diff_Rmult (p : [filteredType R^o * R^o of R^o * R^o]) :
  is_diff p (fun q => q.1 * q.2) (fun q => p.1 * q.2 + q.1 * p.2).
Proof.
apply: DiffDef; last by rewrite diff_bilin // => ?; apply: mul_continuous.
by apply: differentiable_bilin =>?; apply: mul_continuous.
Qed.

Lemma eqo_pair (U V' W' : normedModType R) (F : filter_on U)
  (f : U -> V') (g : U -> W') :
  (fun t => ([o_F id of f] t, [o_F id of g] t)) =o_F id.
Proof.
apply/eqoP => _/posnumP[e]; near=> x; rewrite nng_leUx /=.
by apply/andP; split; near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.

Fact dpair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable f x -> differentiable g x ->
  continuous (fun y => ('d f x y, 'd g x y)) /\
  (fun y => (f y, g y)) \o shift x = cst (f x, g x) +
  (fun y => ('d f x y, 'd g x y)) +o_ (0 : U) id.
Proof.
move=> df dg; split=> [?|]; first by apply: cvg_pair; apply: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
rewrite ![_ (_ + x)]diff_locallyx//.
(* fixme *)
have -> : forall h e, (f x + 'd f x y + [o_ (0 : U) id of h] y,
  g x + 'd g x y + [o_ (0 : U) id of e] y) =
  (f x, g x) + ('d f x y, 'd g x y) +
  ([o_ (0 : U) id of h] y, [o_ (0 : U) id of e] y) by [].
by congr (_ + _); rewrite -[LHS]/((fun y => (_ y, _ y)) y) eqo_pair.
Qed.

Lemma diff_pair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable f x -> differentiable g x -> 'd (fun y => (f y, g y)) x =
  (fun y => ('d f x y, 'd g x y)) :> (U -> V' * W').
Proof.
move=> df dg.
have lin_pair : linear (fun y => ('d f x y, 'd g x y)).
  by move=> ???; rewrite !linearPZ.
have -> : (fun y => ('d f x y, 'd g x y)) = Linear lin_pair by [].
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

Global Instance is_diffM (f g df dg : V -> R^o) x :
  is_diff x f df -> is_diff x g dg -> is_diff x (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx.
have -> : f * g = (fun p => p.1 * p.2) \o (fun y => (f y, g y)) by [].
(* TODO: type class inference should succeed or fail, not leave an evar *)
apply: is_diff_eq; do ?exact: is_diff_comp.
by rewrite funeqE => ?; rewrite /= [_ * g _]mulrC.
Qed.

Lemma diffM (f g : V -> R^o) x :
  differentiable f x -> differentiable g x ->
  'd (f * g) x = f x \*: 'd g x + g x \*: 'd f x :> (V -> R).
Proof. by move=> /differentiableP df /differentiableP dg; rewrite diff_val. Qed.

Lemma differentiableM (f g : V -> R^o) x :
  differentiable f x -> differentiable g x -> differentiable (f * g) x.
Proof. by move=> /differentiableP df /differentiableP dg. Qed.

(* fixme using *)
(* (1 / (h + x) - 1 / x) / h = - 1 / (h + x) x = -1/x^2 + o(1) *)
Fact dinv (x : R) :
  x != 0 -> continuous (fun h : R^o => - x ^- 2 *: h) /\
  (fun x => x^-1 : R^o) \o shift x = cst (x^-1) +
  (fun h : R^o => - x ^- 2 *: h) +o_ (0 : [filteredType R^o of R^o]) id.
Proof.
move=> xn0; suff: continuous (fun h : R^o => - (1 / x) ^+ 2 *: h) /\
  (fun x => 1 / x : R^o) \o shift x = cst (1 / x) +
  (fun h : R^o => - (1 / x) ^+ 2 *: h) +o_ (0 : [filteredType R^o of R^o]) id.
  rewrite !mul1r !GRing.exprVn.
  rewrite (_ : (fun x => x^-1 : R^o) =  (fun x => 1 / x : R^o))//.
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
  near: h; rewrite !locally_simpl; apply/locally_normP.
  exists `|x|; first by rewrite normr_gt0.
  move=> h /=; rewrite distrC subr0 -subr_gt0 => lthx.
  rewrite -(normr_gt0 (h + x : R^o)) addrC -[h]opprK.
  apply: lt_le_trans (ler_dist_dist _ _).
  by rewrite ger0_norm normrN //; apply: ltW.
rewrite addrC -[X in X * _]mulr1 -{2}[1](@mulfVK _ (h + x)) //.
rewrite mulrA expr_div_n expr1n mulf_div mulr1 [_ ^+ 2 * _]mulrC -mulrA.
rewrite -mulrDr mulrBr [1 / _ * _]mulrC normrM.
rewrite mulrDl mulrDl opprD addrACA addrA [x * _]mulrC expr2.
do 2 ?[rewrite -addrA [- _ + _]addrC subrr addr0].
rewrite div1r normfV [X in _ / X]normrM invfM [X in _ * X]mulrC.
rewrite mulrA mulrAC ler_pdivr_mulr ?normr_gt0 ?mulf_neq0 //.
rewrite mulrAC ler_pdivr_mulr ?normr_gt0 //.
have : `|h * h| <= `|x / 2| * (e%:num * `|x * x| * `|h : R^o|).
  rewrite !mulrA; near: h; exists (`|x / 2| * e%:num * `|x * x|).
    by rewrite !pmulr_rgt0 // normr_gt0 mulf_neq0.
  by move=> h /ltW; rewrite distrC subr0 [`|h * _|]normrM => /ler_pmul; apply.
move=> /le_trans-> //; rewrite [X in X <= _]mulrC ler_pmul ?mulr_ge0 //.
near: h; exists (`|x| / 2); first by rewrite divr_gt0 ?normr_gt0.
move=> h; rewrite /= distrC subr0 => lthhx; rewrite addrC -[h]opprK.
apply: le_trans (@ler_dist_dist _ [normedModType R of R^o] _ _).
rewrite normrN [X in _ <= X]ger0_norm; last first.
  rewrite subr_ge0; apply: ltW; apply: lt_le_trans lthhx _.
  by rewrite ler_pdivr_mulr // -{1}(mulr1 `|x|) ler_pmul // ler1n.
rewrite ler_subr_addr -ler_subr_addl (splitr `|x : R^o|).
by rewrite normrM normfV (@ger0_norm _ 2) // -addrA subrr addr0; apply: ltW.
Grab Existential Variables. all: end_near. Qed.

Lemma diff_Rinv (x : [filteredType R^o of R^o]) : x != 0 ->
  'd GRing.inv x = (fun h => - x ^- 2 *: h) :> (R^o -> R^o).
Proof.
move=> xn0; have -> : (fun h : R^o => - x ^- 2 *: h) =
  GRing.scale_linear _ (- x ^- 2) by [].
by apply: diff_unique; have [] := dinv xn0.
Qed.

Lemma differentiable_Rinv (x : R^o) : x != 0 ->
  differentiable (GRing.inv : R^o -> R^o) x.
Proof.
by move=> xn0; apply/diff_locallyP; rewrite diff_Rinv //; apply: dinv.
Qed.

Lemma diffV (f : V -> R^o) x : differentiable f x -> f x != 0 ->
  'd (fun y => (f y)^-1) x = - (f x) ^- 2 \*: 'd f x :> (V -> R).
Proof.
move=> df fxn0.
by rewrite [LHS](diff_comp df (differentiable_Rinv fxn0)) diff_Rinv.
Qed.

Lemma differentiableV (f : V -> R^o) x :
  differentiable f x -> f x != 0 -> differentiable (fun y => (f y)^-1) x.
Proof.
by move=> df fxn0; apply: differentiable_comp _ (differentiable_Rinv fxn0).
Qed.

Lemma exprfunE (T : pointedType) (K : ringType) (f : T -> K) n :
  f ^+ n = (fun x => f x ^+ n).
Proof.
by elim: n => [|n ihn]; rewrite funeqE=> ?; [rewrite !expr0|rewrite !exprS ihn].
Qed.

Global Instance is_diffX (f df : V -> R^o) n x :
  is_diff x f df -> is_diff x (f ^+ n.+1) (n.+1%:R * f x ^+ n *: df).
Proof.
move=> dfx; elim: n => [|n ihn].
  by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_diff_eq.
rewrite scalerA mulrCA -exprS -scalerDl exprfunE -{2}[_ ^+ _]mul1r.
by rewrite -mulrDl -{2}[1]/(1%:R) -natrD addn1.
Qed.

Lemma differentiableX (f : V -> R^o) n x :
  differentiable f x -> differentiable (f ^+ n.+1) x.
Proof. by move=> /differentiableP. Qed.

Lemma diffX (f : V -> R^o) n x :
  differentiable f x ->
  'd (f ^+ n.+1) x = n.+1%:R * f x ^+ n \*: 'd f x :> (V -> R).
Proof. by move=> /differentiableP df; rewrite diff_val. Qed.

End DifferentialR3_realFieldType.

Section Derive.
Variables (R : realFieldType) (V W : normedModType R).

Let der1 (U : normedModType R) (f : R^o -> U) x : derivable f x 1 ->
  f \o shift x = cst (f x) + ( *:%R^~ (f^`() x)) +o_ (0 : [filteredType R^o of R^o]) id.
Proof.
move=> df; apply/eqaddoE; have /derivable_locallyP := df.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
by rewrite derive1E =>->.
Qed.

Lemma deriv1E (U : normedModType R) (f : R^o -> U) x :
  derivable f x 1 -> 'd f x = ( *:%R^~ (f^`() x)) :> (R^o -> U).
Proof.
move=> df; have lin_scal : linear (fun h : R^o => h *: f^`() x).
  by move=> ???; rewrite scalerDl scalerA.
have -> : (fun h : R^o => h *: f^`() x) = Linear lin_scal by [].
by apply: diff_unique; [apply: scalel_continuous|apply: der1].
Qed.

Lemma diff1E (U : normedModType R) (f : R^o -> U) x :
  differentiable f x -> 'd f x = (fun h => h *: f^`() x) :> (R^o -> U).
Proof.
move=> df; have lin_scal : linear (fun h : R^o => h *: 'd f x 1).
  by move=> ???; rewrite scalerDl scalerA.
have -> : (fun h : R^o => h *: f^`() x) = Linear lin_scal.
  by rewrite derive1E'.
apply: diff_unique; first exact: scalel_continuous.
apply/eqaddoE; have /diff_locally -> := df; congr (_ + _ + _).
by rewrite funeqE => h /=; rewrite -{1}[h]mulr1 linearZ.
Qed.

Lemma derivable1_diffP (U : normedModType R) (f : R^o -> U) x :
  derivable f x 1 <-> differentiable f x.
Proof.
split=> dfx.
  by apply/diff_locallyP; rewrite deriv1E //; split;
    [apply: scalel_continuous|apply: der1].
apply/derivable_locallyP/eqaddoE.
have -> : (fun h => (f \o shift x) h%:A) = f \o shift x.
  by rewrite funeqE=> ?; rewrite [_%:A]mulr1.
by have /diff_locally := dfx; rewrite diff1E // derive1E =>->.
Qed.

Lemma derivable1P (U : normedModType R) (f : V -> U) x v :
  derivable f x v <-> derivable (fun h : R^o => f (h *: v + x)) 0 1.
Proof.
rewrite /derivable; set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Lemma derivableP (U : normedModType R) (f : V -> U) x v :
  derivable f x v -> is_derive x v f ('D_v f x).
Proof. by move=> df; apply: DeriveDef. Qed.

Global Instance is_derive_cst (U : normedModType R) (a : U) (x v : V) :
  is_derive x v (cst a) 0.
Proof.
apply: DeriveDef; last by rewrite deriveE // diff_val.
apply/derivable1P/derivable1_diffP.
by have -> : (fun h => cst a (h *: v + x)) = cst a by rewrite funeqE.
Qed.

Fact der_add (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f + g) \o shift x) (h *: v) - (f + g) x)) @
  locally' (0 : R^o) --> 'D_v f x + 'D_v g x.
Proof.
move=> df dg.
evar (fg : R -> W); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  by rewrite !scalerDr scalerN scalerDr opprD addrACA -!scalerBr /fg.
exact: (@cvgD _ _ [topologicalType of R^o]).
Qed.

Lemma deriveD (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f + g) x = 'D_v f x + 'D_v g x.
Proof. by move=> df dg; apply: cvg_map_lim (der_add df dg). Qed.

Lemma derivableD (f g : V -> W) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f + g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (derive f x v + derive g x v).
exact: der_add.
Qed.

Global Instance is_deriveD (f g : V -> W) (x v : V) (df dg : W) :
  is_derive x v f df -> is_derive x v g dg -> is_derive x v (f + g) (df + dg).
Proof.
move=> dfx dgx; apply: DeriveDef; first exact: derivableD.
by rewrite deriveD // !derive_val.
Qed.

Global Instance is_derive_sum n (f : 'I_n -> V -> W) (x v : V)
  (df : 'I_n -> W) : (forall i, is_derive x v (f i) (df i)) ->
  is_derive x v (\sum_(i < n) f i) (\sum_(i < n) df i).
Proof.
elim: n f df => [f df dfx|f df dfx n ihn].
  by rewrite !big_ord0 (_ : 0 = cst 0) //; apply: is_derive_cst.
by rewrite !big_ord_recr /=; apply: is_deriveD.
Qed.

Lemma derivable_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) -> derivable (\sum_(i < n) f i) x v.
Proof.
move=> df; suff : forall i, is_derive x v (f i) ('D_v (f i) x) by [].
by move=> ?; apply: derivableP.
Qed.

Lemma derive_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) ->
  'D_v (\sum_(i < n) f i) x = \sum_(i < n) 'D_v (f i) x.
Proof.
move=> df; suff dfx : forall i, is_derive x v (f i) ('D_v (f i) x).
  by rewrite derive_val.
by move=> ?; apply: derivableP.
Qed.

Fact der_opp (f : V -> W) (x v : V) : derivable f x v ->
  (fun h => h^-1 *: (((- f) \o shift x) (h *: v) - (- f) x)) @
  locally' (0 : R^o) --> - 'D_v f x.
Proof.
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  by rewrite funeqE => h; rewrite !scalerDr !scalerN -opprD -scalerBr /g.
exact: (@cvgN _ _ [topologicalType of R^o]).
Qed.

Lemma deriveN (f : V -> W) (x v : V) : derivable f x v ->
  'D_v (- f) x = - 'D_v f x.
Proof. by move=> df; apply: cvg_map_lim (der_opp df). Qed.

Lemma derivableN (f : V -> W) (x v : V) :
  derivable f x v -> derivable (- f) x v.
Proof. by move=> df; apply/cvg_ex; exists (- 'D_v f x); apply: der_opp. Qed.

Global Instance is_deriveN (f : V -> W) (x v : V) (df : W) :
  is_derive x v f df -> is_derive x v (- f) (- df).
Proof.
move=> dfx; apply: DeriveDef; first exact: derivableN.
by rewrite deriveN // derive_val.
Qed.

Lemma is_derive_eq (V' W' : normedModType R) (f : V' -> W') (x v : V')
  (df f' : W') : is_derive x v f f' -> f' = df -> is_derive x v f df.
Proof. by move=> ? <-. Qed.

Global Instance is_deriveB (f g : V -> W) (x v : V) (df dg : W) :
  is_derive x v f df -> is_derive x v g dg -> is_derive x v (f - g) (df - dg).
Proof. by move=> ??; apply: is_derive_eq. Qed.

Lemma deriveB (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f - g) x = 'D_v f x - 'D_v g x.
Proof. by move=> /derivableP df /derivableP dg; rewrite derive_val. Qed.

Lemma derivableB (f g : V -> W) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f - g) x v.
Proof. by move=> /derivableP df /derivableP dg. Qed.

Fact der_scal (f : V -> W) (k : R) (x v : V) : derivable f x v ->
  (fun h => h^-1 *: ((k \*: f \o shift x) (h *: v) - (k \*: f) x)) @
  locally' (0 : R^o) --> k *: 'D_v f x.
Proof.
move=> df; evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE => h.
  by rewrite scalerBr !scalerA mulrC -!scalerA -!scalerBr /g.
exact: (@cvgZr _ _ [topologicalType of R^o]).
Qed.

Lemma deriveZ (f : V -> W) (k : R) (x v : V) : derivable f x v ->
  'D_v (k \*: f) x = k *: 'D_v f x.
Proof. by move=> df; apply: cvg_map_lim (der_scal df). Qed.

Lemma derivableZ (f : V -> W) (k : R) (x v : V) :
  derivable f x v -> derivable (k \*: f) x v.
Proof.
by move=> df; apply/cvg_ex; exists (k *: 'D_v f x); apply: der_scal.
Qed.

Global Instance is_deriveZ (f : V -> W) (k : R) (x v : V) (df : W) :
  is_derive x v f df -> is_derive x v (k \*: f) (k *: df).
Proof.
move=> dfx; apply: DeriveDef; first exact: derivableZ.
by rewrite deriveZ // derive_val.
Qed.

Fact der_mult (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v ->
  (fun h => h^-1 *: (((f * g) \o shift x) (h *: v) - (f * g) x)) @
  locally' (0 : R^o) --> f x *: 'D_v g x + g x *: 'D_v f x.
Proof.
move=> df dg.
evar (fg : R -> R); rewrite [X in X @ _](_ : _ = fg) /=; last first.
  rewrite funeqE => h.
  have -> : (f * g) (h *: v + x) - (f * g) x =
    f (h *: v + x) *: (g (h *: v + x) - g x) + g x *: (f (h *: v + x) - f x).
    by rewrite !scalerBr -addrA ![g x *: _]mulrC addKr.
  rewrite scalerDr scalerA mulrC -scalerA.
  by rewrite [_ *: (g x *: _)]scalerA mulrC -scalerA /fg.
apply: (@cvgD _ _ [topologicalType of R^o]); last exact: cvgZr df.
apply: cvg_comp2 (@mul_continuous _ (_, _)) => /=; last exact: dg.
suff : {for 0, continuous (fun h : [filteredType _ of R^o] => f(h *: v + x))}.
  by move=> /continuous_withinNx; rewrite scale0r add0r.
exact/(@differentiable_continuous _ _ _ (0 : R^o))/derivable1_diffP/derivable1P.
Qed.

Lemma deriveM (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v ->
  'D_v (f * g) x = f x *: 'D_v g x + g x *: 'D_v f x.
Proof. by move=> df dg; apply: cvg_map_lim (der_mult df dg). Qed.

Lemma derivableM (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v -> derivable (f * g) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (f x *: 'D_v g x + g x *: 'D_v f x).
exact: der_mult.
Qed.

Global Instance is_deriveM (f g : V -> R^o) (x v : V) (df dg : R^o) :
  is_derive x v f df -> is_derive x v g dg ->
  is_derive x v (f * g) (f x *: dg + g x *: df).
Proof.
move=> dfx dgx; apply: DeriveDef; first exact: derivableM.
by rewrite deriveM // !derive_val.
Qed.

Global Instance is_deriveX (f : V -> R^o) n (x v : V) (df : R^o) :
  is_derive x v f df -> is_derive x v (f ^+ n.+1) ((n.+1%:R * f x ^+n) *: df).
Proof.
move=> dfx; elim: n => [|n ihn]; first by rewrite expr1 expr0 mulr1 scale1r.
rewrite exprS; apply: is_derive_eq.
rewrite scalerA -scalerDl mulrCA -[f x * _]exprS.
rewrite -[X in _ + X]mul1r [X in 1 * (X _)]exprfunE -mulrDl.
by rewrite -{2}[1]/1%:R -natrD addn1.
Qed.

Lemma derivableX (f : V -> R^o) n (x v : V) :
  derivable f x v -> derivable (f ^+ n.+1) x v.
Proof. by move/derivableP. Qed.

Lemma deriveX (f : V -> R^o) n (x v : V) :
  derivable f x v ->
  'D_v (f ^+ n.+1) x = (n.+1%:R * f x ^+ n) *: 'D_v f x.
Proof. by move=> /derivableP df; rewrite derive_val. Qed.

Fact der_inv (f : V -> R^o) (x v : V) :
  f x != 0 -> derivable f x v ->
  (fun h => h^-1 *: (((fun y => (f y)^-1) \o shift x) (h *: v) - (f x)^-1)) @
  locally' (0 : R^o) --> - (f x) ^-2 *: 'D_v f x.
Proof.
move=> fxn0 df.
have /derivable1P/derivable1_diffP/differentiable_continuous := df.
move=> /continuous_withinNx; rewrite scale0r add0r => fc.
have fn0 : locally' (0 : R^o) [set h | f (h *: v + x) != 0].
  apply: (fc [set x | x != 0]); exists `|f x|; first by rewrite normr_gt0.
  move=> y; rewrite /= => yltfx.
  by apply/eqP => y0; move: yltfx; rewrite y0 subr0 ltxx.
have : (fun h => - ((f x)^-1 * (f (h *: v + x))^-1) *:
  (h^-1 *: (f (h *: v + x) - f x))) @ locally' (0 : R^o) -->
  - (f x) ^- 2 *: 'D_v f x.
  by apply: cvgM => //; apply: cvgN; rewrite expr2 invfM; apply: cvgM;
     [exact: cvg_cst|  exact: cvgV].
apply: cvg_trans => A [_/posnumP[e] /= Ae].
move: fn0; apply: filter_app; near=> h => /=.
move=> fhvxn0; have he : ball 0 e%:num (h : R^o) by near: h; exists e%:num.
have hn0 : h != 0 by near: h; exists e%:num.
suff <- :
  - ((f x)^-1 * (f (h *: v + x))^-1) *: (h^-1 *: (f (h *: v + x) - f x)) =
  h^-1 *: ((f (h *: v + x))^-1 - (f x)^-1) by exact: Ae.
rewrite scalerA mulrC -scalerA; congr (_ *: _).
apply/eqP; rewrite scaleNr eqr_oppLR opprB scalerBr.
rewrite -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
by rewrite mulrC -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
Grab Existential Variables. all: end_near. Qed.

Lemma deriveV (f : V -> R^o) x v : f x != 0 -> derivable f x v ->
  'D_v[fun y => (f y)^-1] x = - (f x) ^- 2 *: 'D_v f x.
Proof. by move=> fxn0 df; apply: cvg_map_lim (der_inv fxn0 df). Qed.

Lemma derivableV (f : V -> R^o) (x v : V) :
  f x != 0 -> derivable f x v -> derivable (fun y => (f y)^-1) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (- (f x) ^- 2 *: 'D_v f x).
exact: der_inv.
Qed.

End Derive.

Lemma EVT_max (R : realType) (f : R^o -> R^o) (a b : R^o) :
  a <= b -> {in `[a, b], continuous f} -> exists2 c, c \in `[a, b] &
  forall t, t \in `[a, b] -> f t <= f c.
Proof.
move=> leab fcont; set imf := [pred t | t \in f @` [set x | x \in `[a, b]]].
have imf_sup : has_sup imf.
  apply/has_supP; split.
    by exists (f a); rewrite !inE; apply/asboolP/imageP; rewrite inE/= lexx.
  have [M [Mreal imfltM]] : bounded_set (f @` [set x | x \in `[a, b]] : set R^o).
    apply/compact_bounded/continuous_compact; last exact: segment_compact.
    by move=> ?; rewrite inE => /asboolP /fcont.
  exists (M + 1); apply/ubP => y; rewrite !inE => /asboolP /imfltM yleM.
  apply: le_trans (yleM _ _); last by rewrite ltr_addl.
  by rewrite ler_norm.
case: (pselect (exists2 c, c \in `[a, b] & f c = sup imf)) => [|imf_ltsup].
  move=> [c cab fceqsup]; exists c => // t tab.
  rewrite fceqsup; apply: sup_upper_bound=> //; rewrite !inE; apply/asboolP.
  exact: imageP.
have {imf_ltsup} imf_ltsup : forall t, t \in `[a, b] -> f t < sup imf.
  move=> t tab; case: (ltrP (f t) (sup imf))=> // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //.
  apply/eqP; rewrite eq_le supleft sup_upper_bound => //.
  by rewrite !inE; apply/asboolP/imageP.
have invf_continuous : {in `[a, b], continuous (fun t => (sup imf - f t)^-1 : R^o)}.
  move=> t tab; apply: cvgV.
    by rewrite neq_lt subr_gt0 orbC imf_ltsup.
  by apply: cvgD; [apply: continuous_cst|apply: cvgN; apply:fcont].
have /ex_strict_bound_gt0 [k k_gt0 /= imVfltk] :
   bounded_set ((fun t => (sup imf - f t)^-1) @` [set x | x \in `[a, b]] : set R^o).
  apply/compact_bounded/continuous_compact; last exact: segment_compact.
  by move=> ?; rewrite inE => /asboolP /invf_continuous.
have : exists2 y, y \in imf & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
move=> [y]; rewrite !inE => /asboolP [t tab <-] {y}.
rewrite ltr_subl_addr -ltr_subl_addl.
suff : sup imf - f t > k^-1 by move=> /ltW; rewrite leNgt => /negbTE ->.
rewrite -[X in _ < X]invrK ltf_pinv ?qualifE ?invr_gt0 ?subr_gt0 ?imf_ltsup//.
by rewrite (le_lt_trans (ler_norm _) _) ?imVfltk//; apply: imageP.
Qed.

Lemma EVT_min (R : realType) (f : R^o -> R^o) (a b : R^o) :
  a <= b -> {in `[a, b], continuous f} -> exists2 c, c \in `[a, b] &
  forall t, t \in `[a, b] -> f c <= f t.
Proof.
move=> leab fcont.
have /(EVT_max leab) [c clr fcmax] : {in `[a, b], continuous (- f)}.
  by move=> ? /fcont; apply: (@continuousN _ [normedModType R of R^o]).
by exists c => // ? /fcmax; rewrite ler_opp2.
Qed.

Lemma cvg_at_rightE (R : numFieldType) (V : normedModType R) (f : R^o -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_right x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
(* should be inferred *)
have atrF := at_right_proper_filter x.
apply: (@cvg_map_lim _ _ _ (at_right _)) => // A /cvfx /locallyP [_ /posnumP[e] xe_A].
by exists e%:num => // y xe_y; rewrite lt_def => /andP [xney _]; apply: xe_A.
Qed.

Lemma cvg_at_leftE (R : numFieldType) (V : normedModType R) (f : R^o -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_left x).
Proof.
move=> cvfx; apply/Logic.eq_sym.
(* should be inferred *)
have atrF := at_left_proper_filter x.
apply: (@cvg_map_lim _ _ _ (at_left _)) => // A /cvfx /locallyP [_ /posnumP[e] xe_A].
exists e%:num => // y xe_y; rewrite lt_def => /andP [xney _].
by apply: xe_A => //; rewrite eq_sym.
Qed.

Lemma le0r_cvg_map (R : realFieldType) (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, 0 <= f x) -> cvg (f @ F) -> 0 <= lim (f @ F).
Proof.
move=> fge0 fcv; case: (lerP 0 (lim (f @ F))) => // limlt0; near F => x.
have := near fge0 x; rewrite leNgt => /(_ _) /negbTE<- //; near: x.
have normlimgt0 : `|lim (f @ F)| > 0 by rewrite normr_gt0 ltr0_neq0.
have /fcv := locally_ball_norm (lim (f @ F)) (PosNum normlimgt0).
rewrite /= !near_simpl; apply: filterS => x.
rewrite /= distrC => /(le_lt_trans (ler_norm _)).
rewrite ltr_subl_addr => /lt_le_trans; apply.
by rewrite ltr0_norm // addrC subrr.
Grab Existential Variables. all: end_near. Qed.

Lemma ler0_cvg_map (R : realFieldType) (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, f x <= 0) -> cvg (f @ F) -> lim (f @ F) <= 0.
Proof.
move=> fle0 fcv; rewrite -oppr_ge0.
have limopp : - lim (f @ F) = lim (- f @ F).
  by apply: Logic.eq_sym; apply: cvg_map_lim => //; apply: cvgN.
rewrite limopp; apply: le0r_cvg_map; last by rewrite -limopp; apply: cvgN.
by move: fle0; apply: filterS => x; rewrite oppr_ge0.
Qed.

Lemma ler_cvg_map (R : realFieldType) (T : topologicalType) (F : set (set T)) (FF : ProperFilter F)
  (f g : T -> R^o) :
  (\forall x \near F, f x <= g x) -> cvg (f @ F) -> cvg (g @ F) ->
  lim (f @ F) <= lim (g @ F).
Proof.
move=> lefg fcv gcv; rewrite -subr_ge0.
have eqlim : lim (g @ F) - lim (f @ F) = lim ((g - f) @ F).
  by apply/esym; apply: cvg_map_lim => //; apply: cvgD => //; apply: cvgN.
rewrite eqlim; apply: le0r_cvg_map; last first.
  by rewrite /(cvg _) -eqlim /=; apply: cvgD => //; apply: cvgN.
by move: lefg; apply: filterS => x; rewrite subr_ge0.
Qed.

Lemma derive1_at_max (R : realFieldType) (f : R^o -> R^o) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[ -> derivable f t 1) -> c \in `]a, b[ ->
  (forall t, t \in `]a, b[ -> f t <= f c) -> is_derive (c : R^o) 1 f 0.
Proof.
move=> leab fdrvbl cab cmax; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ['D_1 f c]cvg_at_rightE; last exact: fdrvbl.
  apply: ler0_cvg_map; last first.
    have /fdrvbl dfc := cab.
    rewrite -(@cvg_at_rightE _ _ (fun h : R^o => h^-1 *: ((f \o shift c) _ - f c))) //.
    apply: cvg_trans dfc; apply: cvg_app.
    move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
    exact/lt0r_neq0.
  near=> h; apply: mulr_ge0_le0.
    by rewrite invr_ge0; apply: ltW; near: h; exists 1.
  rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
  exists (b - c); first by rewrite subr_gt0 (itvP cab).
  move=> h; rewrite /= distrC subr0.
  move=> /(le_lt_trans (ler_norm _)); rewrite ltr_subr_addr inE/= => ->.
  by move=> /ltr_spsaddl -> //; rewrite (itvP cab).
rewrite ['D_1 f c]cvg_at_leftE; last exact: fdrvbl.
apply: le0r_cvg_map; last first.
  have /fdrvbl dfc := cab; rewrite -(@cvg_at_leftE _ _ (fun h => h^-1 *: ((f \o shift c) _ - f c))) //.
  apply: cvg_trans dfc; apply: cvg_app.
  move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
  exact/ltr0_neq0.
near=> h; apply: mulr_le0.
  by rewrite invr_le0; apply: ltW; near: h; exists 1.
rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h.
exists (c - a); first by rewrite subr_gt0 (itvP cab).
move=> h; rewrite /= distrC subr0.
move=> /ltr_normlP []; rewrite ltr_subr_addl ltr_subl_addl inE/= => -> _.
by move=> /ltr_snsaddl -> //; rewrite (itvP cab).
Grab Existential Variables. all: end_near. Qed.

Lemma derive1_at_min (R : realFieldType) (f : R^o -> R^o) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[ -> derivable f t 1) -> c \in `]a, b[ ->
  (forall t, t \in `]a, b[ -> f c <= f t) -> is_derive (c : R^o) 1 f 0.
Proof.
move=> leab fdrvbl cab cmin; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite -oppr_eq0; apply/eqP.
rewrite -deriveN; last exact: fdrvbl.
suff df : is_derive (c : R^o) 1 (- f) 0 by rewrite derive_val.
apply: derive1_at_max leab _ (cab) _ => t tab; first exact/derivableN/fdrvbl.
by rewrite ler_opp2; apply: cmin.
Qed.

Lemma Rolle (R : realType) (f : R^o -> R^o) (a b : R) :
  a < b -> (forall x, x \in `]a, b[ -> derivable f x 1) ->
  {in `[a, b], continuous f} -> f a = f b ->
  exists2 c, c \in `]a, b[ & is_derive (c : R^o) 1 f 0.
Proof.
move=> ltab fdrvbl fcont faefb.
have [cmax cmaxab fcmax] := EVT_max (ltW ltab) fcont.
case: (pselect ([set a; b] cmax))=> [cmaxeaVb|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnea /asboolPn/eqP cneb].
  have {cmaxab} cmaxab : cmax \in `]a, b[.
    by rewrite inE/= !lt_def !(itvP cmaxab) cnea eq_sym cneb.
  exists cmax => //; apply: derive1_at_max (ltW ltab) fdrvbl cmaxab _ => t tab.
  by apply: fcmax; rewrite inE/= !ltW // (itvP tab).
have [cmin cminab fcmin] := EVT_min (ltW ltab) fcont.
case: (pselect ([set a; b] cmin))=> [cmineaVb|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnea /asboolPn/eqP cneb].
  have {cminab} cminab : cmin \in `]a, b[.
    by rewrite inE/= !lt_def !(itvP cminab) cnea eq_sym cneb.
  exists cmin => //; apply: derive1_at_min (ltW ltab) fdrvbl cminab _ => t tab.
  by apply: fcmin; rewrite inE/= !ltW // (itvP tab).
have midab : (a + b) / 2 \in `]a, b[ by apply: mid_in_itvoo.
exists ((a + b) / 2) => //; apply: derive1_at_max (ltW ltab) fdrvbl (midab) _.
move=> t tab.
suff fcst : forall s, s \in `]a, b[ -> f s = f cmax by rewrite !fcst.
move=> s sab.
apply/eqP; rewrite eq_le fcmax; last by rewrite inE/= !ltW ?(itvP sab).
suff -> : f cmax = f cmin by rewrite fcmin // inE/= !ltW ?(itvP sab).
by case: cmaxeaVb => ->; case: cmineaVb => ->.
Qed.

Lemma MVT (R : realType) (f df : R^o -> R^o) (a b : R) :
  a <= b -> (forall x, x \in `]a, b[ -> is_derive (x : R^o) 1 f (df x)) ->
  {in `[a, b], continuous f} ->
  exists2 c, c \in `[a, b] & f b - f a = df c * (b - a).
Proof.
move=> leab fdrvbl fcont; move: leab; rewrite le_eqVlt => /orP [/eqP aeb|altb].
  by exists a; [rewrite inE/= aeb lexx|rewrite aeb !subrr mulr0].
set g := f + (- ( *:%R^~ ((f b - f a) / (b - a)) : R -> R)).
have gdrvbl : forall x, x \in `]a, b[ -> derivable g x 1.
  by move=> x /fdrvbl dfx; apply: derivableB => //; apply/derivable1_diffP.
have gcont : {in `[a, b], continuous g}.
  move=> x /fcont fx; apply: continuousD fx _; apply: continuousN.
  exact: scalel_continuous.
have gaegb : g a = g b.
  rewrite /g -![(_ - _ : _ -> _) _]/(_ - _).
  apply/eqP; rewrite -subr_eq /= opprK addrAC -addrA -scalerBl.
  rewrite [_ *: _]mulrA mulrC mulrA mulVf.
    by rewrite mul1r addrCA subrr addr0.
  by apply: lt0r_neq0; rewrite subr_gt0.
have [c cab dgc0] := Rolle altb gdrvbl gcont gaegb.
exists c; first by apply/andP; split; apply/ltW; rewrite (itvP cab).
have /fdrvbl dfc := cab; move/@derive_val: dgc0; rewrite deriveB //; last first.
  exact/derivable1_diffP.
move/eqP; rewrite [X in _ - X]deriveE // derive_val diff_val scale1r subr_eq0.
move/eqP->; rewrite -mulrA mulVf ?mulr1 //; apply: lt0r_neq0.
by rewrite subr_gt0.
Qed.

Lemma ler0_derive1_nincr (R : realType) (f : R^o -> R^o) (a b : R) :
  (forall x, x \in `[a, b] -> derivable f x 1) ->
  (forall x, x \in `[a, b] -> f^`() x <= 0) ->
  forall x y, a <= x -> x <= y -> y <= b -> f y <= f x.
Proof.
move=> fdrvbl dfle0 x y leax lexy leyb; rewrite -subr_ge0.
have itvW : {subset `[x, y] <= `[a, b]} by apply/subitvP; rewrite /= leyb leax.
have fdrv z : z \in `]x, y[ -> is_derive (z : R^o) 1 f (f^`()z).
  rewrite inE => /andP [/ltW lexz /ltW lezy].
  apply: DeriveDef; last by rewrite derive1E.
  apply: fdrvbl; rewrite inE; apply/andP; split; first exact: le_trans lexz.
  exact: le_trans leyb.
have [] := @MVT _ f (f^`()) x y lexy fdrv.
  by move=> ? /itvW /fdrvbl /derivable1_diffP /differentiable_continuous.
move=> t /itvW /dfle0 dft dftxy; rewrite -oppr_le0 opprB dftxy.
by apply: mulr_le0_ge0 => //; rewrite subr_ge0.
Qed.

Lemma le0r_derive1_ndecr (R : realType) (f : R^o -> R^o) (a b : R) :
  (forall x, x \in `[a, b] -> derivable f x 1) ->
  (forall x, x \in `[a, b] -> 0 <= f^`() x) ->
  forall x y, a <= x -> x <= y -> y <= b -> f x <= f y.
Proof.
move=> fdrvbl dfge0 x y; rewrite -[f _ <= _]ler_opp2.
apply: (@ler0_derive1_nincr _ (- f)) => t tab; first exact/derivableN/fdrvbl.
rewrite derive1E deriveN; last exact: fdrvbl.
by rewrite oppr_le0 -derive1E; apply: dfge0.
Qed.
