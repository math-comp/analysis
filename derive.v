(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp reals.
Require Import Rstruct Rbar set posnum hierarchy landau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Section Differential.

Context {K : absRingType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) =>
       f = cst (f (lim F)) + df \o center (lim F)
           +o_F (center (lim F))) : _ -> _).
Canonical diff_linear F phF f := [linear of @diff F phF f].
Canonical diff_raddf F phF f := [additive of @diff F phF f].

Notation "''d_' F" := (@diff _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").

Definition differentiable_def (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
   f = cst (f (lim F)) + 'd_F f \o center (lim F) +o_F (center (lim F)).

Notation differentiable F := (@differentiable_def _ (Phantom _ [filter of F])).

Lemma littleo_shift (y x : V) (f : V -> W) (e : V -> V) :
  littleo (locally y) (f \o shift (x - y)) (e \o shift (x - y)) ->
  littleo (locally x) f e.
Proof.
move=> fe _/posnumP[eps]; rewrite near_simpl (near_shift y).
exact: filterS (fe _ [gt0 of eps%:num]).
Qed.

Lemma littleo_center0 (x : V) (f : V -> W) (e : V -> V) :
  [o_x e of f] = [o_(0 : V) (e \o shift x) of f \o shift x] \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP; apply: (@littleo_shift x).
  by rewrite sub0r !comp_shiftK => ?; apply: littleoP.
rewrite insubF //; apply/asboolP => fe; apply: Nfe.
by apply: (@littleo_shift 0); rewrite subr0.
Qed.

Lemma diff_locally (x : V) (f : V -> W) : differentiable x f ->
  f \o shift x = cst (f x) + 'd_x f +o_(0 : V) id.
Proof.
move=> dxf; apply: eqaddoE; rewrite funeqE {1}dxf {dxf} => h /=.
congr (_ + _ + _); rewrite ?lim_id ?addrK //=.
rewrite littleo_center0 /= ?addrK; congr (the_littleo _ _ _ _ _).
by rewrite funeqE => k /=; rewrite addrK.
Qed.

End Differential.

Notation "''d_' F" := (@diff _ _ _ _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").
Notation differentiable F := (@differentiable_def _ _ _ _ (Phantom _ [filter of F])).

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)

(* Prove more generally that if f @ x --> 0 then 'O_x f x = 0. *)
(* statement: Lemma littleo_id (f : R^o -> R^o) (h : _ -> R^o) (x : R^o) :
  f @ x --> (0 : R^o) -> [O_(x : R^o) f of h] x = 0.*)
Lemma littleo_id0 (h : _ -> R^o) : [o_(0 : R^o) id of h] 0 = 0.
Proof.
set k := 'o _; have /(_ _ [gt0 of 1])/= := littleoP [littleo of k].
by move=> /locally_singleton; rewrite mul1r normm0 normm_le0 => /eqP.
Qed.

(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential beeing b *: idfun is locally bounded *)
(* and thus a littleo of 1, and so is id *)
(* This can be generalized to any dimension *)
Lemma diff_locally_converse_part1 (f : R^o -> R^o) (a b : R^o) (x : R^o) :
  f \o shift x = cst a + b *: idfun +o_(0 : R^o) id -> f x = a.
Proof.
rewrite funeqE => /(_ 0) /=; rewrite add0r => ->.
by rewrite -[LHS]/(_ 0 + _ 0 + _ 0) /cst [X in a + X]scaler0 littleo_id0 !addr0.
Qed.

Lemma lim_littleo_div h : let f := [o_(0 : R^o) id of h] : _-> R^o in
  (fun y => f y / y) @ (0 : R^o) --> (0 : R^o).
Proof.
move=> f; apply/flim_ballP => _/posnumP[e]; rewrite !near_simpl.
have e20 : 0 < e%:num / 2 by rewrite divr_gt0.
have /(_ _ e20) H : littleo [filter of 0:R^o] f id by [].
begin_near x.
  case/boolP : (x == 0) => [/eqP x0|x0].
    rewrite x0 invr0 mulr0 //; exact: ball_center e.
  rewrite -ball_normE /ball_ add0r normmN.
  suff : `|[f x]| <= e%:num / 2 * `|[x]|.
    rewrite -ler_pdivr_mulr ?normm_gt0 // => H'.
    apply: ler_lt_trans; [by apply: absrM|].
    rewrite !absRE normrV ?unitfE //; apply: ler_lt_trans; [by apply: H'|].
    by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
  near x.
end_near.
Qed.

End diff_locally_converse_tentative.

Section derivative_univariate.
(* high-school definition of univariate derivative *)

Lemma littleo_id_div h : forall e, 0 < e ->
  let f := [o_(0 : R^o) id of h] : _-> R^o in
  exists e', 0 < e' /\ e' < e /\ \forall y \near (0:R^o), `| f y / y | < e'.
Proof.
move=> e e0.
move/flim_ballP : (lim_littleo_div h).
set f := [o_(0 : R^o) id of h] => H.
have e20 : 0 < e / 2 by rewrite divr_gt0.
exists (e / 2); split => //; split.
  by rewrite ltr_pdivr_mulr // ltr_pmulr // {1}(_ : 1 = 1%:R) // ltr_nat.
move: {H}(H _ e20); rewrite !near_simpl => H.
begin_near x.
  suff : ball 0 (e / 2) (f x / x) by rewrite -ball_normE /ball_ add0r normmN.
  near x.
end_near.
Qed.

Definition derivative1 f a := lim ((fun h => (f (a + h) - f a) / h) @ (0 : R^o)).

Lemma derivative1E f a : differentiable a f ->
  derivative1 f a = lim ((fun x => ('d_a f x) / x) @ (0 : R^o)).
Proof.
move=> fa /=; congr get.
(* bad practice? *)
set h := f \o shift a \- (cst (f a) + 'd_a f).
set g := [o_(0:R^o) id of h].
have /= H : (fun y => 'd_a f y / y) = (fun y => (f (a + y) - f a) / y - g y * y^-1).
  rewrite funeqE => y; rewrite (addrC a) -[f (y + a)]/((f \o shift a) y).
  rewrite (diff_locally fa) -addrA addrAC subrr add0r mulrDl.
  by apply/eqP; rewrite -subr_eq; apply/eqP; rewrite opprK.
rewrite funeqE => /= x; rewrite propeqE; rewrite funeqE in H; split.
- move/app_flim_locally => K; apply/app_flim_locally => e e0.
  rewrite !near_simpl.
  have [e' [? [? ?]]] := littleo_id_div h e0.
  have /K{K}K : 0 < e - e' by rewrite subr_gt0.
  begin_near y.
    rewrite (H y) -ball_normE /ball_ opprB addrCA.
    rewrite (ler_lt_trans (ler_abs_add _ _)) //.
    rewrite (_ : e = e' + (e - e')); last by rewrite addrCA subrr addr0.
    by rewrite ltr_add //; near y.
  end_near.
- move/app_flim_locally => K; apply/app_flim_locally => e e0.
  rewrite !near_simpl.
  have [e' [? [? ?]]] := littleo_id_div h e0.
  have /K{K}K : 0 < e - e' by rewrite subr_gt0.
  begin_near y.
    move: (H y) => /esym/eqP; rewrite subr_eq => /eqP ->.
    rewrite -ball_normE /ball_ opprD addrA (ler_lt_trans (ler_abs_add _ _)) //.
    rewrite (_ : e = (e - e') + e'); last by rewrite addrNK.
    by rewrite absrN ltr_add //; near y.
  end_near.
Qed.

End derivative_univariate.

From mathcomp Require Import fintype matrix.

(* sketch definition of "jacobian f p" as "lin1_mx ('d_p f)"
   to see what are the mathematical structures needed *)
Section jacobian_tentative.

Canonical rV_pointedType n (T : pointedType) :=
  PointedType 'rV[T]_n (\row_i point).
Definition filter_rV n {T : Type} (F : set (set T)) : set (set 'rV[T]_n).
Admitted.
Canonical filtered_rV n' X (Z : filteredType X) : filteredType 'rV[X]_n'.+1 :=
  FilteredType 'rV[X]_n'.+1 'rV[Z]_n'.+1
    (fun x => @filter_rV n'.+1 X (locally (x ord0 ord0))).

Section rV_Topology.
Variables (n' : nat) (T : topologicalType).
Let n := n'.+1.
Implicit Types p : 'rV[T]_n.
Let rV_loc p := @filter_rV n T (@locally T _ (p ord0 ord0)).
Lemma rV_loc_filter p : ProperFilter (rV_loc p). Admitted.
Lemma rV_loc_singleton p (A : set 'rV[T]_n) : rV_loc p A -> A p. Admitted.
Lemma rV_loc_loc p (A : set 'rV[T]_n) : rV_loc p A -> rV_loc p (rV_loc^~ A).
Admitted.
Definition rV_topologicalTypeMixin :=
  topologyOfFilterMixin rV_loc_filter rV_loc_singleton rV_loc_loc.
Canonical rV_topologicalType :=
  TopologicalType 'rV[T]_n rV_topologicalTypeMixin.
End rV_Topology.

Section rV_Uniform.
Variables (n' : nat) (T : uniformType).
Let n := n'.+1.
Implicit Types x y : 'rV[T]_n.
Definition rV_ball x (e : R) y : Prop. Admitted.
Lemma rV_ball_center x (e : R) : 0 < e -> rV_ball x e x. Admitted.
Lemma rV_ball_sym x y (e : R) : rV_ball x e y -> rV_ball y e x. Admitted.
Lemma rV_ball_triangle x y z (e1 e2 : R) :
  rV_ball x e1 y -> rV_ball y e2 z -> rV_ball x (e1 + e2) z. Admitted.
Lemma rV_locally : @locally _ _ = @locally_ 'rV[T]_n _ rV_ball. Admitted.
Definition rV_uniformType_mixin :=
  Uniform.Mixin rV_ball_center rV_ball_sym rV_ball_triangle rV_locally.
Canonical rV_uniformType := UniformType 'rV[T]_n rV_uniformType_mixin.
End rV_Uniform.

Section rV_normedMod.
Variables (n' : nat).
Let n := n'.+1.
Let T := [normedModType R of R^o].
Implicit Types x y : 'rV[T]_n.
Definition rV_norm x : R. Admitted. (* maximum norm *)
Lemma rV_ax1 : forall x y, rV_norm (x + y) <= rV_norm x + rV_norm y. Admitted.
Lemma rV_ax2 : forall (l : R) x, rV_norm (l *: x) <= abs l * rV_norm x.
Admitted.
Lemma rV_ax3 : ball = ball_ rV_norm. Admitted.
Lemma rV_ax4 : forall x : 'rV[T]_n, rV_norm x = 0 -> x = 0. Admitted.
End rV_normedMod.

Definition rV_NormedModMixin n' :=
  @NormedModMixin [absRingType of R] _ _ _ (@rV_norm n') (@rV_ax1 n')
    (@rV_ax2 n') (@rV_ax3 n') (@rV_ax4 n').

Canonical rV_NormedType n' := NormedModType R _ (@rV_NormedModMixin n').

Notation "''RV_' n" := (rV_NormedType n.-1)
  (at level 8, n at level 2, format "''RV_' n").

Definition jacobian n m (f : 'RV_n -> 'RV_m) p := lin1_mx ('d_p f).

End jacobian_tentative.

Section DifferentialR.

Context {V W : normedModType R}.

(* split in multiple bits:
- a linear map which is locally bounded is a little o of 1
- the identity is a littleo of 1
*)
Lemma diff_continuous (x : V) (f : V -> W) :
  differentiable x f -> 'd_x f =O_(0 : V) (cst (1 : R^o)) ->
  {for x, continuous f}.
Proof.
move=> dxf dxfO; have /diff_locally := dxf; rewrite -addrA.
rewrite (littleo_bigO_eqo (cst (1 : R^o))); last first.
  apply/eqOP; exists 1 => //; rewrite /cst mul1r [`|[1 : R^o]|]absr1.
  begin_near y; [rewrite ltrW //; near y|end_near].
  by apply/locally_normP; eexists=> [|?];
    last (rewrite /= ?sub0r ?normmN; apply).
rewrite addfo; first by move=> /eqolim; rewrite flim_shift add0r.
apply/eqolim0P; apply: (flim_trans (linear_continuous _ _ _)) => //.
by rewrite linear0.
Qed.

End DifferentialR.
