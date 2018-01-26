(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype matrix.
From SsrReals Require Import boolp reals.
Require Import Rstruct Rbar set posnum topology hierarchy landau.

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

Section jacobian.

Definition jacobian n m (R : absRingType) (f : 'rV[R]_n.+1 -> 'rV[R]_m.+1) p :=
  lin1_mx ('d_p f).

End jacobian.

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
  near=> y; [rewrite ltrW //; near: y|end_near].
  by apply/locally_normP; eexists=> [|?];
    last (rewrite /= ?sub0r ?normmN; apply).
rewrite addfo; first by move=> /eqolim; rewrite flim_shift add0r.
apply/eqolim0P; apply: (flim_trans (linear_continuous _ _ _)) => //.
by rewrite linear0.
Qed.

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

End diff_locally_converse_tentative.


Section derivative_univariate.
(* high-school definition of univariate derivative *)

Definition derivative1 f a := lim ((fun h => (f (a + h) - f a) / h) @ (0 : R^o)).

Lemma derivative1E f a : differentiable a f ->
  derivative1 f a =
  @jacobian 0 0 _ (fun x => (f (x ord0 ord0))%:M) a%:M ord0 ord0.
Proof.
Admitted.

End derivative_univariate.

End DifferentialR.

