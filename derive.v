(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import ssralg ssrnum fintype matrix.
Require Import boolp reals.
Require Import Rstruct Rbar set posnum topology hierarchy landau.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Section Differential.

Context {K : absRingType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  (get (fun (df : {linear V -> W}) => forall x,
      f x = f (lim F) + df (x - lim F) +o_(x \near F) (x - lim F))).
Canonical diff_linear F phF f := [linear of @diff F phF f].
Canonical diff_raddf F phF f := [additive of @diff F phF f].

Notation "''d_' F" := (@diff _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").

Definition differentiable_def (F : filter_on V) (_ : phantom (set (set V)) F)
  (f : V -> W) :=
  f = cst (f (lim F)) + 'd_F f \o center (lim F) +o_F (center (lim F)).


Notation differentiable F := (@differentiable_def _ (Phantom _ [filter of F])).

Lemma diffP (F : filter_on V) (f : V -> W) :
  differentiable F f <->
  (forall x, f x = f (lim F) + 'd_F f (x - lim F) +o_(x \near F) (x - lim F)).
Proof. by rewrite /differentiable_def funeqE. Qed.

Lemma littleo_shift (y x : V) (f : V -> W) (e : V -> V) :
  littleo (locally y) (f \o shift (x - y)) (e \o shift (x - y)) ->
  littleo (locally x) f e.
Proof.
move=> fe _/posnumP[eps]; rewrite near_simpl (near_shift y).
exact: filterS (fe _ [gt0 of eps%:num]).
Qed.

Lemma littleo_center0 (x : V) (f : V -> W) (e : V -> V) :
  [o_x e of f] = [o_ (0 : V) (e \o shift x) of f \o shift x] \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP; apply: (@littleo_shift x).
  by rewrite sub0r !comp_shiftK => ?; apply: littleoP.
rewrite insubF //; apply/asboolP => fe; apply: Nfe.
by apply: (@littleo_shift 0); rewrite subr0.
Qed.

Lemma diff_locallyx (x : V) (f : V -> W) : differentiable x f ->
  forall h, f (h + x) = f x + 'd_x f h +o_(h \near 0 : V) h.
Proof.
move=> /diffP dxf; apply: eqaddoEx => h /=; rewrite dxf lim_id addrK /=.
congr (_ + _ + _); rewrite littleo_center0 /= addrK.
by congr ('o); rewrite funeqE => k /=; rewrite addrK.
Qed.

Lemma diff_locally  (x : V) (f : V -> W) : differentiable x f ->
  (f \o shift x = cst (f x) + 'd_x f +o_ (0 : V) id).
Proof. by move=> /diff_locallyx fhx; rewrite funeqE. Qed.

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
  differentiable x f -> ('d_x f : _ -> _) =O_ (0 : V) (cst (1 : R^o)) ->
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

Section littleo_lemmas.

Variables X Y Z : normedModType R.

Lemma normm_littleo x (f : X -> Y) : `|[ [o_(x \near x) (1 : R^o) of f x]]| = 0.
Proof.
rewrite /cst /=; set e := 'o _; apply/eqP.
have /(_  (`|[e x]|/2) _)/locally_singleton /= := littleoP [littleo of e].
rewrite pmulr_lgt0 // [`|[1 : R^o]|]normr1 mulr1 [X in X <= _]splitr.
by rewrite ger_addr pmulr_lle0 // => /implyP; case: ltrgtP; rewrite ?normm_lt0.
Qed.


Lemma littleo_lim0 (f : X -> Y) (h : _ -> Z) (x : X) :
  f @ x --> (0 : Y) -> [o_x f of h] x = 0.
Proof.
move/eqolim0P => ->.
set k := 'o _; have /(_ _ [gt0 of 1])/= := littleoP [littleo of k].
by move=> /locally_singleton; rewrite mul1r normm_littleo normm_le0 => /eqP.
Qed.

End littleo_lemmas.

Section diff_locally_converse_tentative.
(* if there exist A and B s.t. f(a + h) = A + B h + o(h) then
   f is differentiable at a, A = f(a) and B = f'(a) *)
(* this is a consequence of diff_continuous and eqolim0 *)
(* indeed the differential beeing b *: idfun is locally bounded *)
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
  lim ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ (0 : R^o)).

Lemma deriveE (f : V -> W) (a v : V) :
  differentiable a f -> derive f a v = 'd_a f v.
Proof.
rewrite /derive /jacobian => /diff_locally -> /=; set k := 'o _.
evar (g : R -> W); rewrite [X in X @ _](_ : _ = g) /=; last first.
  rewrite funeqE=> h; rewrite !scalerDr scalerN /cst /=.
  by rewrite addrC !addrA addNr add0r linearZ /= scalerA /g.
Admitted.

End DifferentialR.

Section DifferentialR2.
Implicit Type (V : normedModType R).

Lemma derivemxE m n (f : 'rV[R]_m.+1 -> 'rV[R]_n.+1) (a v : 'rV[R]_m.+1) :
  differentiable a f -> derive f a v = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

Definition derive1 V (f : R -> V) (a : R) :=
   lim ((fun h => h^-1 *: (f (h + a) - f a)) @ (0 : R^o)).

Lemma derive1E V (f : R -> V) a : derive1 f a = derive (f : R^o -> _) a 1.
Proof.
rewrite /derive1 /derive; set d := (fun _ : R => _); set d' := (fun _ : R => _).
by suff -> : d = d' by []; rewrite funeqE=> h; rewrite /d /d' /= [h%:A](mulr1).
Qed.

(* Is it necessary? *)
Lemma derive1E' V f a : differentiable a (f : R^o -> V) ->
  derive1 f a = 'd_a f 1.
Proof. by move=> ?; rewrite derive1E deriveE. Qed.

End DifferentialR2.
