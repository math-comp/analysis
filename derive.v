(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype bigop matrix interval.
Require Import boolp reals classical_sets posnum topology hierarchy landau.
Require Import forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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

Context {K : realFieldType} {V W : normedModType K}.
Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => continuous df /\ forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).
Canonical diff_linear F phF f := [linear of @diff F phF f].
Canonical diff_raddf F phF f := [additive of @diff F phF f].

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

Lemma diff_locallyxP (x : V) (f : V -> W) :
  differentiable f x <-> continuous ('d f x) /\
  forall h, f (h + x) = f x + 'd f x h +o_(h \near 0 : V) h.
Proof.
split=> [dxf|[dfc dxf]].
  split => //; apply: eqaddoEx => h; have /diffE -> := dxf.
  rewrite lim_id addrK; congr (_ + _); rewrite littleo_center0 /= addrK.
  by congr ('o); rewrite funeqE => k /=; rewrite addrK.
apply/diffP; split=> //; apply: eqaddoEx; move=> y.
rewrite lim_id -[in LHS](subrK x y) dxf; congr (_ + _).
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

End Differential.

Notation "''d' f F" := (@diff _ _ _ _ (Phantom _ [filter of F]) f).
Notation differentiable f F := (@differentiable_def _ _ _ f _ (Phantom _ [filter of F])).

Notation "'is_diff' F" := (is_diff_def (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "'is_diff'  F").
Hint Extern 0 (differentiable _ _) => solve[apply: ex_diff] : core.
Hint Extern 0 ({for _, continuous _}) => exact: diff_continuous : core.

Lemma differentiableP (R : realFieldType) (V W : normedModType R) (f : V -> W)
  x : differentiable f x -> is_diff x f ('d f x).
Proof. by move=> ?; apply: DiffDef. Qed.

Section jacobian.

Definition jacobian n m (R : realFieldType) (f : 'rV[R]_n -> 'rV[R]_m)
  p := lin1_mx ('d f p).

End jacobian.

Notation "''J' f p" := (jacobian f p).

Section DifferentialR.

Context (R : realFieldType) {V W : normedModType R}.

(* split in multiple bits:
- a linear map which is locally bounded is a little o of 1
- the identity is a littleo of 1
*)
Lemma differentiable_continuous (x : V) (f : V -> W) :
  differentiable f x -> {for x, continuous f}.
Proof.
move=> /diff_locallyP [dfc]; rewrite -addrA.
rewrite (littleo_bigO_eqo (cst (1 : R^o))); last first.
  apply/eqOP; near=> k; rewrite /cst [`|[_]|]normr1 mulr1.
  near=> y; rewrite ltrW //; near: y; apply/locally_normP.
  by exists k; [near: k; exists 0|move=> ? /=; rewrite sub0r normmN].
rewrite addfo; first by move=> /eqolim; rewrite flim_shift add0r.
by apply/eqolim0P; apply: (flim_trans (dfc 0)); rewrite linear0.
Grab Existential Variables. all: end_near. Qed.

Section littleo_lemmas.

Variables X Y Z : normedModType R.

Lemma normm_littleo x (f : X -> Y) : `|[ [o_(x \near x) (1 : R^o) of f x]]| = 0.
Proof.
rewrite /cst /=; have [e /(_ (`|[e x]|/2) _)/locally_singleton /=] := littleo.
rewrite pmulr_lgt0 // [`|[1 : R^o]|]normr1 mulr1 [X in X <= _]splitr.
by rewrite ger_addr pmulr_lle0 // => /implyP; case: ltrgtP; rewrite ?normm_lt0.
Qed.

Lemma littleo_lim0 (f : X -> Y) (h : _ -> Z) (x : X) :
  f @ x --> (0 : Y) -> [o_x f of h] x = 0.
Proof.
move/eqolim0P => ->; have [k /(_ _ [gt0 of 1])/=] := littleo.
by move=> /locally_singleton; rewrite mul1r normm_littleo normm_le0 => /eqP.
Qed.

End littleo_lemmas.

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)
(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential being b *: idfun is locally bounded *)
(* and thus a littleo of 1, and so is id *)
(* This can be generalized to any dimension *)
Lemma diff_locally_converse_part1 (f : R^o -> R^o) (a b : R^o) (x : R^o) :
  f \o shift x = cst a + b *: idfun +o_ (0 : R^o) id -> f x = a.
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
    (fun h => h *: ('D_v f a)) +o_ (locally (0 : R^o)) id.
Proof.
move=> df; apply/eqaddoP => _/posnumP[e].
rewrite -locally_nearE locally_simpl /= locallyE'; split; last first.
  rewrite /at_point opprD -![(_ + _ : _ -> _) _]/(_ + _) scale0r add0r.
  by rewrite addrA subrr add0r normmN scale0r !normm0 mulr0.
have /eqolimP := df; rewrite -[lim _]/(derive _ _ _).
move=> /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]).
apply: filter_app; rewrite /= !near_simpl near_withinE; near=> h => hN0.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|[1 : R^o]|]normr1 mulr1 => dfv.
rewrite addrA -[X in X + _]scale1r -(@mulVf _ h) //.
rewrite mulrC -scalerA -scalerBr normmZ.
rewrite -ler_pdivl_mull; last by rewrite normr_gt0.
by rewrite mulrCA mulVf ?mulr1; last by rewrite normr_eq0.
Grab Existential Variables. all: end_near. Qed.

Lemma derivable_locallyP (f : V -> W) a v :
  derivable f a v <->
  (fun h => (f \o shift a) (h *: v)) = (cst (f a)) +
    (fun h => h *: ('D_v f a)) +o_ (locally (0 : R^o)) id.
Proof.
split; first exact: derivable_locally.
move=> df; apply/cvg_ex; exists ('D_v f a).
apply/(@eqolimP _ _ _ (locally'_filter_on _))/eqaddoP => _/posnumP[e].
have /eqaddoP /(_ e%:num) /(_ [gt0 of e%:num]) := df.
rewrite /= !(near_simpl, near_withinE); apply: filter_app; near=> h.
rewrite /= opprD -![(_ + _ : _ -> _) _]/(_ + _) -![(- _ : _ -> _) _]/(- _).
rewrite /cst /= [`|[1 : R^o]|]normr1 mulr1 addrA => dfv hN0.
rewrite -[X in _ - X]scale1r -(@mulVf _ h) //.
by rewrite -scalerA -scalerBr normmZ normfV ler_pdivr_mull ?normr_gt0 // mulrC.
Grab Existential Variables. all: end_near. Qed.

Lemma derivable_locallyx (f : V -> W) a v :
  derivable f a v -> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (locally (0 : R^o))) h.
Proof.
move=> /derivable_locally; rewrite funeqE => df.
by apply: eqaddoEx => h; have /= := (df h); rewrite addrC => ->.
Qed.

Lemma derivable_locallyxP (f : V -> W) a v :
  derivable f a v <-> forall h, f (a + h *: v) = f a + h *: 'D_v f a
  +o_(h \near (locally (0 : R^o))) h.
Proof.
split; first exact: derivable_locallyx.
move=> df; apply/derivable_locallyP; apply/eqaddoE; rewrite funeqE => h.
by rewrite /= addrC df.
Qed.

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable f a -> 'D_v f a = 'd f a v.
Proof.
rewrite /derive => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE=> h; rewrite !scalerDr scalerN /cst /=.
  by rewrite addrC !addrA addNr add0r linearZ /= scalerA /g.
apply: flim_map_lim.
pose g1 : R -> W := fun h => (h^-1 * h) *: 'd f a v.
pose g2 : R -> W := fun h : R => h^-1 *: k (h *: v ).
rewrite (_ : g = g1 + g2) ?funeqE // -(addr0 (_ _ v)); apply: lim_add.
  rewrite -(scale1r (_ _ v)); apply: lim_scalel.
  apply/app_flim_entouragesP => X entX; apply/locallyP.
  rewrite locally_E; exists X => // x _ x0; rewrite mulVf //.
  exact: entourage_refl.
rewrite /g2.
have [/eqP ->|v0] := boolP (v == 0).
  rewrite (_ : (fun _ => _) = cst 0); first exact: cst_continuous.
  by rewrite funeqE => ?; rewrite scaler0 /k littleo_lim0 // scaler0.
apply/flim_normP => e e0; rewrite /locally' -filter_from_norm_locally.
have /(littleoP [littleo of k]) /locally_normP [i i0 Hi] : 0 < e / (2 * `|[v]|).
  by rewrite divr_gt0 // pmulr_rgt0 // normm_gt0.
exists (i / `|[v]|); first by rewrite divr_gt0 // normm_gt0.
move=> /= j; rewrite normmB subr0 ltr_pdivl_mulr ?normm_gt0 // => jvi j0.
rewrite normmB subr0 normmZ -ltr_pdivl_mull ?normr_gt0 ?invr_neq0 //.
have /Hi/ler_lt_trans -> // : ball norm 0 i (j *: v).
  by rewrite /ball add0r normmN (ler_lt_trans _ jvi) // normmZ.
rewrite -(mulrC e) -mulrA -ltr_pdivl_mull // mulrA mulVr ?unitfE ?gtr_eqF //.
rewrite normrV ?unitfE // div1r invrK ltr_pdivr_mull; last first.
  by rewrite pmulr_rgt0 // normm_gt0.
by rewrite normmZ mulrC -mulrA ltr_pmull ?ltr1n // pmulr_rgt0 normm_gt0.
Qed.

End DifferentialR.

Notation "''D_' v f" := (derive f ^~ v).
Notation "''D_' v f c" := (derive f c v). (* printing *)
Hint Extern 0 (derivable _ _ _) => solve[apply: ex_derive] : core.

Section DifferentialR2.

Variable (R : realFieldType) (V : normedModType R).

Lemma derivemxE m n (f : 'rV[R]_m -> 'rV[R]_n) (a v : 'rV[R]_m) :
  differentiable f a -> 'D_ v f a = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

Definition derive1 (f : R -> V) (a : R) :=
   lim ((fun h => h^-1 *: (f (h + a) - f a)) @ locally' (0 : R^o)).

Local Notation "f ^` ()" := (derive1 f).

Lemma derive1E (f : R -> V) a : f^`() a = 'D_1 (f : R^o -> _) a.
Proof.
rewrite /derive1 /derive; set d := (fun _ : R => _); set d' := (fun _ : R => _).
by suff -> : d = d' by []; rewrite funeqE=> h; rewrite /d /d' /= [h%:A](mulr1).
Qed.

(* Is it necessary? *)
Lemma derive1E' f a : differentiable (f : R^o -> V) a ->
  f^`() a = 'd f a 1.
Proof. by move=> ?; rewrite derive1E deriveE. Qed.

Definition derive1n n (f : R -> V) := iter n derive1 f.

Local Notation "f ^` ( n )" := (derive1n n f).

Lemma derive1n0 (f : R -> V) : f^`(0) = f.
Proof. by []. Qed.

Lemma derive1n1 (f : R -> V) : f^`(1) = f^`().
Proof. by []. Qed.

Lemma derive1nS (f : R -> V) n : f^`(n.+1) = f^`(n)^`().
Proof. by []. Qed.

Lemma derive1Sn (f : R -> V) n : f^`(n.+1) = f^`()^`(n).
Proof. exact: iterSr. Qed.

End DifferentialR2.

Notation "f ^` ()" := (derive1 f).
Notation "f ^` ( n )" := (derive1n n f).

Section DifferentialR3.

Variable (R : realFieldType).

Lemma littleo_linear0 (V W : normedModType R) (f : {linear V -> W}) :
  (f : V -> W) =o_ (0 : V) id -> f = cst 0 :> (V -> W).
Proof.
move/eqoP => oid.
rewrite funeqE => x; apply/eqP; case: (ler0P `|[x]|) => [|xn0].
  by rewrite normm_le0 => /eqP ->; rewrite linear0.
rewrite -normm_le0 -(mul0r `|[x]|) -ler_pdivr_mulr //.
apply/ler0_addgt0P => _ /posnumP[e]; rewrite ler_pdivr_mulr //.
have /oid /locally_normP [_/posnumP[d] dfe] := [gt0 of e%:num].
set k := ((d%:num / 2) / (PosNum xn0)%:num)^-1.
rewrite -{1}(@scalerKV _ _ k _ x) // linearZZ normmZ.
rewrite -ler_pdivl_mull ?gtr0_norm // mulrCA.
rewrite (@ler_trans _ (e%:num * `|[k^-1 *: x]|)) //; last first.
  by rewrite ler_pmul // normmZ normfV gtr0_norm.
apply dfe; rewrite /ball sub0r normmN normmZ.
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
  rewrite hdf -addrA addrACA [cst _ + _]addrC addrK -[LHS]addr0; congr (_ + _).
  by apply/eqP; rewrite eq_sym addrC addr_eq0 oppo.
rewrite (hdf _ dxf).
suff /diff_locally /hdf -> : differentiable f x.
  by rewrite opprD addrCA -(addrA (_ - _)) addKr oppox addox.
apply/diffP; apply: (@getPex _ (fun (df : {linear V -> W}) => continuous df /\
  forall y, f y = f (lim x) + df (y - lim x) +o_(y \near x) (y - lim x))).
exists df; split=> //; apply: eqaddoEx => z.
rewrite (hdf _ dxf) !addrA lim_id /funcomp /= subrK [f _ + _]addrC addrK.
rewrite -addrA -[LHS]addr0; congr (_ + _).
apply/eqP; rewrite eq_sym addrC addr_eq0 oppox; apply/eqP.
by rewrite littleo_center0 (comp_centerK x id) -[- _ in RHS](comp_centerK x).
Qed.

Fact dcst (V W : normedModType R) (a : W) (x : V) : continuous (0 : V -> W) /\
  cst a \o shift x = cst (cst a x) + \0 +o_ (0 : V) id.
Proof.
split; first exact: continuous_cst.
apply/eqaddoE; rewrite addr0 funeqE => ? /=; rewrite -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof.
Qed.

Lemma diff_cst (V W : normedModType R) a x : ('d (cst a) x : V -> W) = 0.
Proof. by apply/diff_unique; have [] := dcst a x. Qed.

Variables (V W : normedModType R).

Lemma differentiable_cst (W' : normedModType R) (a : W') (x : V) :
  differentiable (cst a) x.
Proof. by apply/diff_locallyP; rewrite diff_cst; have := dcst a x. Qed.

Global Instance is_diff_cst (a : W) (x : V) : is_diff x (cst a) 0.
Proof. exact: DiffDef (differentiable_cst _ _) (diff_cst _ _). Qed.

Fact dadd (f g : V -> W) x :
  differentiable f x -> differentiable g x ->
  continuous ('d f x \+ 'd g x) /\
  (f + g) \o shift x = cst ((f + g) x) + ('d f x \+ 'd g x) +o_ (0 : V) id.
Proof.
move=> df dg; split => [?|]; do ?exact: continuousD.
apply/eqaddoE; rewrite funeqE => y /=; rewrite -[(f + g) _]/(_ + _).
by rewrite ![_ (_ + x)]diff_locallyx// addrACA addox addrACA.
Qed.

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

Fact dopp (f : V -> W) x :
  differentiable f x -> continuous (- ('d f x : V -> W)) /\
  (- f) \o shift x = cst (- f x) \- 'd f x +o_ (0 : V) id.
Proof.
move=> df; split; first by move=> ?; apply: continuousN.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(- f) _]/(- (_ _)) diff_locallyx// !opprD oppox.
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

Lemma is_diff_eq (V' W' : normedModType R) (f f' g : V' -> W') (x : V') :
  is_diff x f f' -> f' = g -> is_diff x f g.
Proof. by move=> ? <-. Qed.

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

Fact dscale (f : V -> W) k x :
  differentiable f x -> continuous (k \*: 'd f x) /\
  (k *: f) \o shift x = cst ((k *: f) x) + k \*: 'd f x +o_ (0 : V) id.
Proof.
move=> df; split; first by move=> ?; apply: continuousZ.
apply/eqaddoE; rewrite funeqE => y /=.
by rewrite -[(k *: f) _]/(_ *: _) diff_locallyx // !scalerDr scaleox.
Qed.

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

(* NB: could be generalized with K : absRingType instead of R *)
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

Fact dlin (V' W' : normedModType R) (f : {linear V' -> W'}) x :
  continuous f -> f \o shift x = cst (f x) + f +o_ (0 : V') id.
Proof.
move=> df; apply: eqaddoE; rewrite funeqE => y /=.
rewrite linearD addrC -[LHS]addr0; congr (_ + _).
by rewrite littleoE; last exact: littleo0_subproof. (*fixme*)
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

Global Instance is_diff_scalel (x k : R^o) :
  is_diff k ( *:%R ^~ x) ( *:%R ^~ x).
Proof.
have -> : *:%R ^~ x = GRing.scale_linear [lmodType R of R^o] x.
  by rewrite funeqE => ? /=; rewrite [_ *: _]mulrC.
apply: DiffDef; first exact/linear_differentiable/scaler_continuous.
by rewrite diff_lin //; apply: scaler_continuous.
Qed.

Lemma differentiable_coord m n (M : 'M[R]_(m, n)) i j :
  differentiable (fun N : 'M[R]_(m, n) => N i j : R^o) M.
Proof.
have @f : {linear 'M[R]_(m, n) -> R^o}.
  by exists (fun N : 'M[R]_(_, _) => N i j); eexists; move=> ? ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma linear_lipschitz (V' W' : normedModType R) (f : {linear V' -> W'}) :
  continuous f -> exists2 k, k > 0 & forall x, `|[f x]| <= k * `|[x]|.
Proof.
move=> /(_ 0); rewrite linear0 => /(_ _ (locally_ball 0 1%:pos)) /locally_normP.
move=> [_ /posnumP[e] he]; exists (2 / e%:num) => // x.
case: (lerP `|[x]| 0) => [|xn0].
  by rewrite normm_le0 => /eqP->; rewrite linear0 !normm0 mulr0.
set k := 2 / e%:num * (PosNum xn0)%:num.
have kn0 : k != 0 by [].
have abskgt0 : `|k| > 0 by rewrite normr_gt0.
rewrite -[x in X in X <= _](scalerKV kn0) linearZZ normmZ -ler_pdivl_mull //.
suff /he : ball norm 0 e%:num (k^-1 *: x).
  rewrite /= normmB subr0 => /ltrW /ler_trans; apply.
  by rewrite ger0_norm // mulVf.
rewrite /= normmB subr0 normmZ normfV ger0_norm // invfM -mulrA mulVf //.
by rewrite invf_div mulr1 [X in _ < X]splitr; apply: ltr_spaddr.
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

(* TODO: generalize *)
Lemma compoO_eqo (K : realFieldType) (U V' W' : normedModType K) (f : U -> V')
  (g : V' -> W') :
  [o_ (0 : V') id of g] \o [O_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ (0 : U) id of f]].
have /(_ (e%:num / k%:num)) := littleoP [littleo of [o_ (0 : V') id of g]].
move=> /(_ _) /locally_normP [//|_/posnumP[d] hd].
apply: filter_app; near=> x => leOxkx; apply: ler_trans (hd _ _) _; last first.
  rewrite -ler_pdivl_mull //; apply: ler_trans leOxkx _.
  by rewrite invf_div mulrA -[_ / _ * _]mulrA mulVf // mulr1.
rewrite /= normmB subr0 (ler_lt_trans leOxkx) // -ltr_pdivl_mull //; near: x.
apply/locally_normP; exists (k%:num ^-1 * d%:num) => // x.
by rewrite /= normmB subr0.
Grab Existential Variables. all: end_near. Qed.

Lemma compoO_eqox (K : realFieldType) (U V' W' : normedModType K) (f : U -> V')
  (g : V' -> W') :
  forall x : U, [o_ (0 : V') id of g] ([O_ (0 : U) id of f] x) =o_(x \near 0 : U) x.
Proof. by move=> x; rewrite -[X in X = _]/((_ \o _) x) compoO_eqo. Qed.

(* TODO: generalize *)
Lemma compOo_eqo (K : realFieldType) (U V' W' : normedModType K) (f : U -> V')
  (g : V' -> W') :
  [O_ (0 : V') id of g] \o [o_ (0 : U) id of f] =o_ (0 : U) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ (0 : V') id of g]].
move=> /locally_normP [_/posnumP[d] hd]; have ekgt0 : e%:num / k%:num > 0 by [].
have /(_ _ ekgt0) := littleoP [littleo of [o_ (0 : U) id of f]].
apply: filter_app; near=> x => leoxekx; apply: ler_trans (hd _ _) _; last first.
  by rewrite -ler_pdivl_mull // mulrA [_^-1 * _]mulrC.
rewrite /ball normmB subr0; apply: ler_lt_trans leoxekx _.
rewrite -ltr_pdivl_mull //; near: x; apply/locally_normP.
by exists ((e%:num / k%:num) ^-1 * d%:num)=> // x; rewrite /ball normmB subr0.
Grab Existential Variables. all: end_near. Qed.

Lemma compOo_eqox (K : realFieldType) (U V' W' : normedModType K) (f : U -> V')
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
  exists2 k, k > 0 & forall u v, `|[f u v]| <= k * `|[u]| * `|[v]|.
Proof.
move=> /(_ (0, 0)); rewrite linear0r => /(_ _ (locally_ball 0 1%:pos)).
move=> [[A B] [/locally_normP /= [_/posnumP[eA] sA]]].
move=> /locally_normP [_/posnumP[eB] sB] sAB.
set e := minr eA%:num eB%:num; exists ((2 / e) ^+2) => // u v.
case: (lerP `|[u]| 0) => [|un0].
  by rewrite normm_le0 => /eqP->; rewrite linear0l !normm0 mulr0 mul0r.
case: (lerP `|[v]| 0) => [|vn0].
  by rewrite normm_le0 => /eqP->; rewrite linear0r !normm0 mulr0.
rewrite -[`|[u]|]/((PosNum un0)%:num) -[`|[v]|]/((PosNum vn0)%:num).
set ku := 2 / e * (PosNum un0)%:num.
set kv := 2 / e * (PosNum vn0)%:num.
rewrite -[X in f X](@scalerKV _ _ ku) // linearZl_LR normmZ gtr0_norm //.
rewrite -ler_pdivl_mull // -[X in f _ X](@scalerKV _ _ kv) // linearZr_LR.
rewrite normmZ gtr0_norm // -ler_pdivl_mull //.
suff : ball norm 0 e (ku^-1 *: u, kv^-1 *: v).
  rewrite /ball ltr_maxl !ltr_minr => /andP [/andP[/sA uA _] /andP[_ /sB vB]].
  have /sAB /= := conj uA vB; rewrite normmB subr0 => /ltrW /ler_trans; apply.
  by rewrite ler_pdivl_mull// mulr1 ler_pdivl_mull// mulrA [ku * _]mulrAC expr2.
rewrite /ball normmB subr0.
have -> : (ku^-1 *: u, kv^-1 *: v) =
  (e / 2) *: ((PosNum un0)%:num ^-1 *: u, (PosNum vn0)%:num ^-1 *: v).
  rewrite invrM ?unitfE // [kv ^-1]invrM ?unitfE //.
  rewrite mulrC -[_ *: u]scalerA [X in X *: v]mulrC -[_ *: v]scalerA.
  by rewrite invf_div.
rewrite normmZ ger0_norm // -mulrA gtr_pmulr // ltr_pdivr_mull // mulr1.
by rewrite ltr_maxl !normmZ !ger0_norm // !mulVf // ltr1n.
Qed.

Lemma bilinear_eqo (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) :
  continuous (fun p => f p.1 p.2) -> (fun p => f p.1 p.2) =o_ (0 : U * V') id.
Proof.
move=> fc; have [_ /posnumP[k] fschwarz] := bilinear_schwarz fc.
apply/eqoP=> _ /posnumP[e]; near=> x; rewrite (ler_trans (fschwarz _ _))//.
rewrite ler_pmul ?pmulr_rge0 //; last by rewrite ler_maxr orbC lerr.
rewrite -ler_pdivl_mull //.
suff : `|[x]| <= k%:num ^-1 * e%:num by apply: ler_trans; rewrite ler_maxr lerr.
near: x; apply/locally_normP; exists (k%:num ^-1 * e%:num) => //.
by move=> ? /=; rewrite normmB subr0 => /ltrW.
Grab Existential Variables. all: end_near. Qed.

Fact dbilin (U V' W' : normedModType R) (f : {bilinear U -> V' -> W'}) p :
  continuous (fun p => f p.1 p.2) ->
  continuous (fun q => (f p.1 q.2 + f q.1 p.2)) /\
  (fun q => f q.1 q.2) \o shift p = cst (f p.1 p.2) +
    (fun q => f p.1 q.2 + f q.1 p.2) +o_ (0 : U * V') id.
Proof.
move=> fc; split=> [q|].
  apply: (@continuousD _ _ _ (fun q => f p.1 q.2) (fun q => f q.1 p.2));
    move=> A /(fc (_.1, _.2)) [PQ [/locally_normP [_/posnumP[eP] sP]]];
    move=> /locally_normP [_/posnumP[eQ] sQ] sPQ /=; apply/locally_normP.
    exists eQ%:num => // xy; rewrite /= ltr_maxl => /andP [_ /sQ Qy].
    by apply: (sPQ (_,_)); split=> //=; apply/sP.
  exists eP%:num => // xy; rewrite /= ltr_maxl => /andP [/sP Px _].
  by apply: (sPQ (_,_)); split=> //=; apply/sQ.
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

Definition mulr_rev (y x : R) := x * y.
Canonical rev_Rmult := @RevOp _ _ _ mulr_rev *%R (fun _ _ => erefl).

Lemma mulr_is_linear (x : R^o) : linear (GRing.mul x).
Proof. by move=> ???; rewrite mulrDr scalerAr. Qed.
Canonical mulr_linear x := Linear (mulr_is_linear x).

Lemma mulr_rev_is_linear y : linear (mulr_rev y : R^o -> R^o).
Proof. by move=> ???; rewrite /mulr_rev mulrDl scalerAl. Qed.
Canonical mulr_rev_linear y := Linear (mulr_rev_is_linear y).

Canonical mulr_bilinear := [bilinear of (@GRing.mul [ringType of R^o])].

Global Instance is_diff_Rmult (p : R^o * R^o) :
  is_diff p (fun q => q.1 * q.2) (fun q => p.1 * q.2 + q.1 * p.2).
Proof.
apply: DiffDef; first by apply: differentiable_bilin =>?; apply: lim_mult.
by rewrite diff_bilin // => ?; apply: lim_mult.
Qed.

Lemma eqo_pair (K : realFieldType) (U V' W' : normedModType K) (F : filter_on U)
  (f : U -> V') (g : U -> W') :
  (fun t => ([o_F id of f] t, [o_F id of g] t)) =o_F id.
Proof.
apply/eqoP => _/posnumP[e]; near=> x; rewrite ler_maxl /=.
by apply/andP; split; near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.

Fact dpair (U V' W' : normedModType R) (f : U -> V') (g : U -> W') x :
  differentiable f x -> differentiable g x ->
  continuous (fun y => ('d f x y, 'd g x y)) /\
  (fun y => (f y, g y)) \o shift x = cst (f x, g x) +
  (fun y => ('d f x y, 'd g x y)) +o_ (0 : U) id.
Proof.
move=> df dg; split=> [?|]; first by apply: flim_pair; apply: diff_continuous.
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
by apply: is_diff_eq; rewrite funeqE => ?; rewrite /= [_ * g _]mulrC.
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
  x != 0 -> continuous (fun h : R^o => - (1 / x) ^+ 2 *: h) /\
  (fun x => 1 / x : R^o) \o shift x = cst (1 / x) +
  (fun h : R^o => - (1 / x) ^+ 2 *: h) +o_ (0 : R^o) id.
Proof.
move=> xn0; split; first by move=> ?; apply: continuousZ.
apply/eqaddoP => _ /posnumP[e]; near=> h.
rewrite -[(_ + _ : R -> R) h]/(_ + _) -[(- _ : R -> R) h]/(- _) /=.
rewrite opprD scaleNr opprK /cst /=.
rewrite -[- _]mulr1 -[X in - _ * X](mulfVK xn0) mulrA mulNr -expr2 mulNr.
rewrite [- _ + _]addrC -mulrBr.
rewrite -[X in X + _]mulr1 -[X in 1 / _ * X](@mulfVK _ (x ^+ 2)); last first.
  by rewrite sqrf_eq0.
rewrite mulrA mulf_div mulr1.
have hDx_neq0 : h + x != 0.
  near: h; apply/locally_normP; exists `|x|; first by rewrite normr_gt0.
  move=> h /=; rewrite normmB subr0 -subr_gt0 => lthx.
  rewrite -(normm_gt0 (h + x : R^o)) addrC -[h]opprK.
  apply: ltr_le_trans (ler_distm_dist _ _).
  by rewrite ger0_norm normmN //; apply: ltrW.
rewrite addrC -[X in X * _]mulr1 -{2}[1](@mulfVK _ (h + x)) //.
rewrite mulrA expr_div_n expr1n mulf_div mulr1 [_ ^+ 2 * _]mulrC -mulrA.
rewrite -mulrDr mulrBr [1 / _ * _]mulrC [`|[_]|]normrM.
rewrite mulrDl mulrDl opprD addrACA addrA [x * _]mulrC expr2.
do 2 ?[rewrite -addrA [- _ + _]addrC subrr addr0].
rewrite div1r normfV [X in _ / X]normrM invfM [X in _ * X]mulrC.
rewrite mulrA mulrAC ler_pdivr_mulr ?normr_gt0 ?mulf_neq0 //.
rewrite mulrAC ler_pdivr_mulr ?normr_gt0 //.
have : `|h * h| <= `|x / 2| * (e%:num * `|x * x| * `|[h : R^o]|).
  rewrite !mulrA; near: h; apply/locally_normP.
  exists (`|x / 2| * e%:num * `|x * x|).
    by rewrite !pmulr_rgt0 // normr_gt0 mulf_neq0.
  by move=> h /ltrW; rewrite normmB subr0 [`|h * _|]normrM => /ler_pmul; apply.
move=> /ler_trans-> //; rewrite [X in X <= _]mulrC ler_pmul ?mulr_ge0 //.
near: h; apply/locally_normP; exists (`|x| / 2).
  by rewrite divr_gt0 ?normr_gt0.
move=> h; rewrite /ball normmB subr0 => lthhx; rewrite addrC -[h]opprK.
apply: ler_trans (ler_distm_dist _ _); rewrite normmN [X in _ <= X]ger0_norm.
  rewrite ler_subr_addr -ler_subr_addl (splitr `|[x : R^o]|).
  by rewrite normrM normfV (@ger0_norm _ 2) // -addrA subrr addr0; apply: ltrW.
rewrite subr_ge0; apply: ltrW; apply: ltr_le_trans lthhx _.
by rewrite [`|[_]|]splitr ler_addl; apply: divr_ge0.
Grab Existential Variables. all: end_near. Qed.

Lemma diff_Rinv (x : R^o) : x != 0 ->
  'd (fun y => 1 / y) x = (fun h => - (1 / x) ^+ 2 *: h) :> (R^o -> R^o).
Proof.
move=> xn0; have -> : (fun h : R^o => - (1 / x) ^+2 *: h) =
  GRing.scale_linear _ (- (1 / x) ^+2) by [].
by apply: diff_unique; have [] := dinv xn0.
Qed.

Lemma differentiable_Rinv (x : R^o) :
  x != 0 -> differentiable (fun y : R^o => 1 / y) x.
Proof.
by move=> xn0; apply/diff_locallyP; rewrite diff_Rinv //; apply: dinv.
Qed.

Lemma inv_continuous x : x != 0 -> {for x, continuous (fun y : R^o => 1 / y)}.
Proof.
by move=> xn0; apply: differentiable_continuous (differentiable_Rinv xn0).
Qed.

Lemma lim_inv (T : topologicalType) (F : set (set T)) (FF : Filter F)
  (f : T -> R^o) (a : R^o) :
  a != 0 -> f @ F --> a -> (fun y => 1 / f y) @ F --> 1 / a.
Proof.
move=> an0 fa; apply: (flim_trans _ (inv_continuous an0)).
exact: (@flim_comp _ _ _ f (fun y => 1 / y) _ _ _ fa).
Qed.

Lemma diffV (f : V -> R^o) x : differentiable f x -> f x != 0 ->
  'd (fun y => 1 / f y) x = - (1 / f x) ^+ 2 \*: 'd f x :> (V -> R).
Proof.
move=> df fxn0.
by rewrite [LHS](diff_comp df (differentiable_Rinv fxn0)) diff_Rinv.
Qed.

Lemma differentiableV (f : V -> R^o) x :
  differentiable f x -> f x != 0 -> differentiable (fun y => 1 / f y) x.
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

End DifferentialR3.

Section Derive.

Variable (R : realFieldType) (V W : normedModType R).

Let der1 (U : normedModType R) (f : R^o -> U) x : derivable f x 1 ->
  f \o shift x = cst (f x) + ( *:%R^~ (f^`() x)) +o_ (0 : R^o) id.
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
exact: lim_add.
Qed.

Lemma deriveD (f g : V -> W) (x v : V) : derivable f x v -> derivable g x v ->
  'D_v (f + g) x = 'D_v f x + 'D_v g x.
Proof. by move=> df dg; apply: flim_map_lim (der_add df dg). Qed.

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
exact: lim_opp.
Qed.

Lemma deriveN (f : V -> W) (x v : V) : derivable f x v ->
  'D_v (- f) x = - 'D_v f x.
Proof. by move=> df; apply: flim_map_lim (der_opp df). Qed.

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
exact: lim_scaler.
Qed.

Lemma deriveZ (f : V -> W) (k : R) (x v : V) : derivable f x v ->
  'D_v (k \*: f) x = k *: 'D_v f x.
Proof. by move=> df; apply: flim_map_lim (der_scal df). Qed.

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
apply: lim_add; last exact: lim_scaler df.
apply: flim_comp2 (@lim_mult _ _ _) => /=; last exact: dg.
suff : {for 0, continuous (fun h => f(h *: v + x))}.
  by move=> /continuous_withinNx; rewrite scale0r add0r.
exact/differentiable_continuous/derivable1_diffP/derivable1P.
Qed.

Lemma deriveM (f g : V -> R^o) (x v : V) :
  derivable f x v -> derivable g x v ->
  'D_v (f * g) x = f x *: 'D_v g x + g x *: 'D_v f x.
Proof. by move=> df dg; apply: flim_map_lim (der_mult df dg). Qed.

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
  (fun h => h^-1 *: (((fun y => 1 / f y) \o shift x) (h *: v) - 1 / f x)) @
  locally' (0 : R^o) --> - (1 / f x) ^+2 *: 'D_v f x.
Proof.
move=> fxn0 df.
have /derivable1P/derivable1_diffP/differentiable_continuous := df.
move=> /continuous_withinNx; rewrite scale0r add0r => fc.
have fn0 : locally' (0 : R^o) [set h | f (h *: v + x) != 0].
  apply: (fc [set x | x != 0]); rewrite /= -filter_from_norm_locally.
  exists `|[f x]|; first by rewrite normm_gt0.
  move=> y; rewrite /ball => yltfx.
  by apply/eqP => y0; move: yltfx; rewrite y0 subr0 ltrr.
have : (fun h => - ((1 / f x) * (1 / f (h *: v + x))) *:
  (h^-1 *: (f (h *: v + x) - f x))) @ locally' (0 : R^o) -->
  - (1 / f x) ^+2 *: 'D_v f x.
  apply: flim_comp2 (@lim_mult _ _ _) => //=.
  apply: (@lim_opp _ [normedModType R of R^o]); rewrite expr2.
  exact/lim_scaler/lim_inv.
apply: flim_trans; rewrite [in X in _ --> X]/locally' -filter_from_norm_locally.
move=> A [_/posnumP[e] Ae]; move: fn0; apply: filter_app; near=> h => /= fhvxn0.
have he : ball norm 0 e%:num h by near: h; apply/locally_normP; exists e%:num.
have hn0 : h != 0 by near: h; apply/locally_normP; exists e%:num.
suff <- :
  - ((1 / f x) * (1 / f (h *: v + x))) *: (h^-1 *: (f (h *: v + x) - f x)) =
  h^-1 *: (1 / f (h *: v + x) - 1 / f x) by exact: Ae.
rewrite scalerA mulrC -scalerA; congr (_ *: _).
apply/eqP; rewrite scaleNr eqr_oppLR opprB !div1r scalerBr.
rewrite -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
by rewrite mulrC -scalerA [_ *: f _]mulVf // [_%:A]mulr1.
Grab Existential Variables. all: end_near. Qed.

Lemma deriveV (f : V -> R^o) x v : f x != 0 -> derivable f x v ->
  'D_v[fun y => 1 / f y] x = - (1 / f x) ^+2 *: 'D_v f x.
Proof. by move=> fxn0 df; apply: flim_map_lim (der_inv fxn0 df). Qed.

Lemma derivableV (f : V -> R^o) (x v : V) :
  f x != 0 -> derivable f x v -> derivable (fun y => 1 / f y) x v.
Proof.
move=> df dg; apply/cvg_ex; exists (- (1 / f x) ^+2 *: 'D_v f x).
exact: der_inv.
Qed.

End Derive.

Lemma EVT_max (R : realType) (f : R -> R) (a b : R) :
  a <= b -> {in `[a, b], continuous f} -> exists2 c, c \in `[a, b] &
  forall t, t \in `[a, b] -> f t <= f c.
Proof.
move=> leab fcont; set imf := [pred t | t \in f @` [set x | x \in `[a, b]]].
have imf_sup : has_sup imf.
  apply/has_supP; split.
    by exists (f a); rewrite !inE; apply/asboolP/imageP; rewrite inE lerr.
  have [M imfltM] : bounded (f @` [set x | x \in `[a, b]] : set R^o).
    apply/compact_bounded/continuous_compact; last exact: segment_compact.
    by move=> ?; rewrite inE => /asboolP /fcont.
  exists (M + 1); apply/ubP => y; rewrite !inE => /asboolP /imfltM yltM.
  by apply/ltrW; apply: ler_lt_trans (yltM _ _); rewrite ?ler_norm // ltr_addl.
case: (pselect (exists2 c, c \in `[a, b] & f c = sup imf)) => [|imf_ltsup].
  move=> [c cab fceqsup]; exists c => // t tab.
  rewrite fceqsup; apply: sup_upper_bound=> //; rewrite !inE; apply/asboolP.
  exact: imageP.
have {imf_ltsup} imf_ltsup : forall t, t \in `[a, b] -> f t < sup imf.
  move=> t tab; case: (ltrP (f t) (sup imf))=> // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //.
  apply/eqP; rewrite eqr_le supleft sup_upper_bound => //.
  by rewrite !inE; apply/asboolP/imageP.
have invf_cont : {in `[a, b], continuous (fun t => 1 / (sup imf - f t))}.
  move=> t tab; apply: (@lim_inv _ _ (locally t)).
    by rewrite neqr_lt subr_gt0 orbC imf_ltsup.
  by apply: lim_add; [apply: continuous_cst|apply/lim_opp/fcont].
have [M imVfltM] : bounded ((fun t => 1 / (sup imf - f t)) @`
  [set x | x \in `[a, b]] : set R^o).
  apply/compact_bounded/continuous_compact; last exact: segment_compact.
  by move=> ?; rewrite inE => /asboolP /invf_cont.
set k := maxr (M + 1) 1; have kgt0 : 0 < k by rewrite ltr_maxr ltr01 orbC.
have : exists2 y, y \in imf & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
move=> [y]; rewrite !inE => /asboolP [t tab <-] {y}.
rewrite ltr_subl_addr - ltr_subl_addl.
suff : sup imf - f t > k^-1 by move=> /ltrW; rewrite lerNgt => /negbTE ->.
rewrite -[X in _ < X]invrK ltr_pinv.
    rewrite -div1r; apply: ler_lt_trans (ler_norm _) _.
    by apply: imVfltM; [rewrite ltr_maxr ltr_addl ltr01|apply: imageP].
  by rewrite inE kgt0 unitfE lt0r_neq0.
have invsupft_gt0 : 0 < (sup imf - f t)^-1.
  by rewrite invr_gt0 subr_gt0 imf_ltsup.
by rewrite inE invsupft_gt0 unitfE lt0r_neq0.
Qed.

Lemma EVT_min (R : realType) (f : R -> R) (a b : R) :
  a <= b -> {in `[a, b], continuous f} -> exists2 c, c \in `[a, b] &
  forall t, t \in `[a, b] -> f c <= f t.
Proof.
move=> leab fcont.
have /(EVT_max leab) [c clr fcmax] : {in `[a, b], continuous (- f)}.
  by move=> ? /fcont; apply: (@continuousN _ [normedModType R of R^o]).
by exists c => // ? /fcmax; rewrite ler_opp2.
Qed.

Lemma cvg_at_rightE (R : realType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_right x).
Proof.
move=> cvfx; apply/esym. (* should be inferred *)
have atrF := at_right_proper_filter x; apply: flim_map_lim => A /cvfx.
rewrite /locally' /at_right -filter_from_norm_locally.
move=> [_/posnumP[e] xe_A]; exists e%:num => // y xe_y.
by rewrite ltr_def => /andP[xney _]; apply: xe_A.
Qed.

Lemma cvg_at_leftE (R : realType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ locally' x) -> lim (f @ locally' x) = lim (f @ at_left x).
Proof.
move=> cvfx; apply/esym. (* should be inferred *)
have atrF := at_left_proper_filter x; apply: flim_map_lim => A /cvfx.
rewrite /locally' /at_left -filter_from_norm_locally.
move=> [_ /posnumP[e] xe_A]; exists e%:num => // y xe_y.
by rewrite ltr_def => /andP [xney _]; apply: xe_A => //; rewrite eq_sym.
Qed.

Lemma le0r_flim_map (R : realFieldType) (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, 0 <= f x) -> cvg (f @ F) -> 0 <= lim (f @ F).
Proof.
move=> fge0 fcv; case: (lerP 0 (lim (f @ F))) => // limlt0; near F => x.
have := near fge0 x; rewrite lerNgt => /(_ _) /negbTE<- //; near: x.
have normlimgt0 : `|[lim (f @ F)]| > 0 by rewrite normm_gt0 ltr0_neq0.
have /fcv := locally_ball (lim (f @ F)) (PosNum normlimgt0).
rewrite /= !near_simpl; apply: filterS => x.
rewrite /= normmB => /(ler_lt_trans (ler_norm _)).
rewrite ltr_subl_addr => /ltr_le_trans; apply.
by rewrite [`|[_]|]ltr0_norm // addrC subrr.
Grab Existential Variables. all: end_near. Qed.

Lemma ler0_flim_map (R : realFieldType) (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f : T -> R^o) :
  (\forall x \near F, f x <= 0) -> cvg (f @ F) -> lim (f @ F) <= 0.
Proof.
move=> fle0 fcv; rewrite -oppr_ge0.
have limopp : - lim (f @ F) = lim (- f @ F).
  exact/Logic.eq_sym/flim_map_lim/lim_opp.
rewrite limopp; apply: le0r_flim_map; last by rewrite -limopp; apply: lim_opp.
by move: fle0; apply: filterS => x; rewrite oppr_ge0.
Qed.

Lemma ler_flim_map (R : realFieldType) (T : topologicalType) (F : set (set T))
  (FF : ProperFilter F) (f g : T -> R^o) :
  (\forall x \near F, f x <= g x) -> cvg (f @ F) -> cvg (g @ F) ->
  lim (f @ F) <= lim (g @ F).
Proof.
move=> lefg fcv gcv; rewrite -subr_ge0.
have eqlim : lim (g @ F) - lim (f @ F) = lim ((g - f) @ F).
  by apply/Logic.eq_sym/flim_map_lim/lim_add => //; apply: lim_opp.
rewrite eqlim; apply: le0r_flim_map; last first.
  by rewrite /(cvg _) -eqlim /=; apply: lim_add => //; apply: lim_opp.
by move: lefg; apply: filterS => x; rewrite subr_ge0.
Qed.

Lemma derive1_at_max (R : realType) (f : R^o -> R^o) (a b c : R) :
  a <= b -> (forall t, t \in `]a, b[ -> derivable f t 1) -> c \in `]a, b[ ->
  (forall t, t \in `]a, b[ -> f t <= f c) -> is_derive (c : R^o) 1 f 0.
Proof.
move=> leab fdrvbl cab cmax; apply: DeriveDef; first exact: fdrvbl.
apply/eqP; rewrite eqr_le; apply/andP; split.
  rewrite ['D_1 f c]cvg_at_rightE; last exact: fdrvbl.
  apply: ler0_flim_map; last first.
    have /fdrvbl dfc := cab; rewrite -cvg_at_rightE //.
    apply: flim_trans dfc; apply: flim_app.
    move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
    exact/lt0r_neq0.
  near=> h; apply: mulr_ge0_le0.
    by rewrite invr_ge0; apply: ltrW; near: h; apply/locally_normP; exists 1.
  rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h; apply/locally_normP.
  exists (b - c); first by rewrite subr_gt0 (itvP cab).
  move=> h; rewrite /ball normmB subr0.
  move=> /(ler_lt_trans (ler_norm _)); rewrite ltr_subr_addr inE => ->.
  by move=> /ltr_spsaddl -> //; rewrite (itvP cab).
rewrite ['D_1 f c]cvg_at_leftE; last exact: fdrvbl.
apply: le0r_flim_map; last first.
  have /fdrvbl dfc := cab; rewrite -cvg_at_leftE //.
  apply: flim_trans dfc; apply: flim_app.
  move=> A [e egt0 Ae]; exists e => // x xe xgt0; apply: Ae => //.
  exact/ltr0_neq0.
near=> h; apply: mulr_le0.
  by rewrite invr_le0; apply: ltrW; near: h; apply/locally_normP; exists 1.
rewrite subr_le0 [_%:A]mulr1; apply: cmax; near: h; apply/locally_normP.
exists (c - a); first by rewrite subr_gt0 (itvP cab).
move=> h; rewrite /ball normmB subr0.
move=> /ltr_normlP []; rewrite ltr_subr_addl ltr_subl_addl inE => -> _.
by move=> /ltr_snsaddl -> //; rewrite (itvP cab).
Grab Existential Variables. all: end_near. Qed.

Lemma derive1_at_min (R : realType) (f : R^o -> R^o) (a b c : R) :
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
have [cmax cmaxab fcmax] := EVT_max (ltrW ltab) fcont.
case: (pselect ([set a; b] cmax))=> [cmaxeaVb|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnea /asboolPn/eqP cneb].
  have {cmaxab} cmaxab : cmax \in `]a, b[.
    by rewrite inE !ltr_def !(itvP cmaxab) cnea eq_sym cneb.
  exists cmax => //; apply: derive1_at_max (ltrW ltab) fdrvbl cmaxab _ => t tab.
  by apply: fcmax; rewrite inE !ltrW // (itvP tab).
have [cmin cminab fcmin] := EVT_min (ltrW ltab) fcont.
case: (pselect ([set a; b] cmin))=> [cmineaVb|]; last first.
  move=> /asboolPn; rewrite asbool_or => /norP.
  move=> [/asboolPn/eqP cnea /asboolPn/eqP cneb].
  have {cminab} cminab : cmin \in `]a, b[.
    by rewrite inE !ltr_def !(itvP cminab) cnea eq_sym cneb.
  exists cmin => //; apply: derive1_at_min (ltrW ltab) fdrvbl cminab _ => t tab.
  by apply: fcmin; rewrite inE !ltrW // (itvP tab).
have midab : (a + b) / 2 \in `]a, b[ by apply: mid_in_itvoo.
exists ((a + b) / 2) => //; apply: derive1_at_max (ltrW ltab) fdrvbl (midab) _.
move=> t tab.
suff fcst : forall s, s \in `]a, b[ -> f s = f cmax by rewrite !fcst.
move=> s sab.
apply/eqP; rewrite eqr_le fcmax; last by rewrite inE !ltrW ?(itvP sab).
suff -> : f cmax = f cmin by rewrite fcmin // inE !ltrW ?(itvP sab).
by case: cmaxeaVb => ->; case: cmineaVb => ->.
Qed.

Lemma MVT (R : realType) (f df : R^o -> R^o) (a b : R) :
  a <= b -> (forall x, x \in `]a, b[ -> is_derive (x : R^o) 1 f (df x)) ->
  {in `[a, b], continuous f} ->
  exists2 c, c \in `[a, b] & f b - f a = df c * (b - a).
Proof.
move=> leab fdrvbl fcont; move: leab; rewrite ler_eqVlt => /orP [/eqP aeb|altb].
  by exists a; [rewrite inE aeb lerr|rewrite aeb !subrr mulr0].
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
exists c; first by apply/andP; split; apply/ltrW; rewrite (itvP cab).
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
  rewrite inE => /andP [/ltrW lexz /ltrW lezy].
  apply: DeriveDef; last by rewrite derive1E.
  apply: fdrvbl; rewrite inE; apply/andP; split; first exact: ler_trans lexz.
  exact: ler_trans leyb.
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
