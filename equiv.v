(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Rcomplements Rbar Markov Iter Lub.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp reals.
Require Import Rstruct set R_ext hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Delimit Scope R_scope with coqR.
Delimit Scope real_scope with real.
Local Close Scope R_scope.
Local Open Scope ring_scope.
Local Open Scope real_scope.
Local Open Scope classical_set_scope.

Section function_space.

Definition cst {T T' : Type} (x : T') : T -> T' := fun=> x.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @ZmodMixin (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g) _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite addrA. Qed.
Next Obligation. by move=> f g; rewrite funeqE=> x /=; rewrite addrC. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite add0r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite addNr. Qed.
Canonical fct_zmodType T (M : zmodType) := ZmodType (T -> M) (fct_zmodMixin T M).

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @RingMixin [zmodType of T -> M] (cst 1) (fun f g x => f x * g x)
             _ _ _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrA. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mul1r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mulr1. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDl. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDr. Qed.
Next Obligation.
by apply/eqP; rewrite funeqE => /(_ point) /eqP; rewrite oner_eq0.
Qed.
Canonical fct_ringType (T : pointedType) (M : ringType) :=
  RingType (T -> M) (fct_ringMixin T M).

Program Canonical fct_comRingType (T : pointedType) (M : comRingType) :=
  ComRingType (T -> M) _.
Next Obligation. by move=> f g; rewrite funeqE => x; rewrite mulrC. Qed.

End function_space.

(* Tentative to handle small o and big O notations *)
Section Domination.

Context {K : absRingType} {T : Type} {V W : normedModType K}.

Definition littleo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall (eps : posreal), \near x in F, `|[f x]| <= pos eps * `|[g x]|.

Structure littleo_type (F : set (set T)) (g : T -> W) := Littleo {
  littleo_fun :> T -> V;
  _ : `[< littleo F littleo_fun g >]
}.
Notation "''o_' F" := (littleo_type F)
  (at level 0, F at level 0, format "''o_' F").

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Lemma littleo0 F g : Filter F -> littleo F 0 g.
Proof.
move=> FF eps /=; apply: filter_forall => x; rewrite normm0.
by rewrite mulr_ge0 // ltrW.
Qed.

Canonical little0 (F : filter_on T) g := Littleo (asboolT (@littleo0 F g _)).

Lemma littleoP (F : set (set T)) (g : T -> W) (f : 'o_F g) :
  forall eps, eps > 0 -> \near x in F, `|[f x]| <= eps * `|[g x]|.
Proof.
by case: f => ? /= /asboolP Fg eps eps_gt0; apply: (Fg (PosReal eps_gt0)).
Qed.

Definition the_littleo (F : filter_on T) (phF : phantom (set (set T)) F) f h := insubd (little0 F h) f.
Arguments the_littleo : simpl never, clear implicits.

Notation mklittleo x := (the_littleo _ (Phantom _ [filter of x])).

Notation "f = g '+o_' F h" :=
  (f%function = g%function + mklittleo F (f \- g) h)
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" := (f = \0 +o_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Lemma add_littleo_subproof (F : filter_on T) e (df dg :'o_F e) :
  littleo F (df \+ dg) e.
Proof.
move=> eps; near x => /=.
  rewrite (double_var eps) mulrDl.
  rewrite (ler_trans (ler_normm_add _ _)) // ler_add //; assume_near x.
by end_near; apply: littleoP.
Qed.

Canonical add_littleo (F : filter_on T) e (df dg :'o_F e) :=
  Littleo (asboolT (add_littleo_subproof df dg)).

Lemma addo (F : filter_on T) (f g: T -> V) e :
  (mklittleo F f e : T -> V) + (mklittleo F g e : T -> V) =
  mklittleo F
    (add_littleo (mklittleo F f e) (mklittleo F g e)) e.
Proof.
rewrite {3}/the_littleo /insubd insubT //; apply/asboolP.
by move=> eps; apply: littleoP.
Qed.

Lemma addox (F : filter_on T) (f g: T -> V) e x :
  mklittleo F f e x + mklittleo F g e x =
  mklittleo F ((add_littleo (mklittleo F f e) (mklittleo F g e))) e x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addo. Qed.

(* This notation is printing only in order to display 'o
   without looking at the contents *)
Notation "''o' '_' F" := (mklittleo F _ _)
  (at level 0, F at level 0, format "''o' '_' F").

Lemma eqadd_some_oP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + mklittleo F h e -> littleo F (f - g) e.
Proof.
rewrite /the_littleo /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_] eps  /=.
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: littleoP.
Qed.

Lemma eqaddoP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +o_ F e) <-> (littleo F (f - g) e).
Proof.
split=> [/eqadd_some_oP//|/asboolP fg_o_e].
by rewrite /the_littleo /insubd insubT /= addrC addrNK.
Qed.

Lemma eqoP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =o_ F e) <-> (littleo F f e).
Proof. by rewrite eqaddoP subr0. Qed.

Lemma eqoE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + mklittleo F h e -> f = g +o_ F e.
Proof. by move=> /eqadd_some_oP /eqaddoP. Qed.

Lemma eqo_trans (F : filter_on T) (f g h : T -> V) (e : T -> W):
  f = g +o_ F e -> g = h +o_F e -> f = h +o_F e.
Proof. by move=> -> ->; apply: eqoE; rewrite -addrA addo. Qed.

(* :TODO: add a spec to replace a 'o_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)

Definition bigo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists k, \near x in F, `|[f x]| < k * `|[g x]|.

End Domination.

Notation "''o_' F" := (@littleo_type _ _ _ _ F)
  (at level 0, F at level 0, format "''o_' F").

Arguments the_littleo {_ _ _ _} _ _ _ _ : simpl never.
Notation mklittleo x := (the_littleo _ (Phantom _ [filter of x])).

Notation "f = g '+o_' F h" :=
  (f%function = g%function +
     mklittleo F (f \- g : _ -> _) h)
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" := (f = \0 +o_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Notation "''o' '_' F" := (mklittleo F _)
  (at level 0, F at level 0, format "''o' '_' F").

Section Limit.

Context {K : absRingType} {T : Type} {V W X : normedModType K}.

Lemma eqolimP (F : filter_on T) (f : T -> V) (k : W) : k != 0 ->
  cvg (f @ F) <-> f = cst (lim (f @ F)) +o_F (cst k).
Proof.
move=> k_gt0; split=> fF.
  apply/eqaddoP => eps; near x.
    by rewrite /cst ltrW //= normmB; assume_near x.
  by end_near; apply: (flim_norm _ fF); rewrite mulr_gt0 ?normm_gt0.
apply/flim_normP=> eps; rewrite !near_simpl.
have lt_eps x : x <= (pos eps / (`|[k]| + 1)) * `|[k]| -> x < pos eps.
  rewrite -mulrA => /ler_lt_trans; apply; rewrite -ltr_pdivl_mull ?mulVf //.
  by rewrite ltr_pdivr_mull ?mulr1 ?ltr_addl ?addr_gt0 ?normm_gt0.
near x.
  rewrite [X in X x]fF opprD addNKr normmN lt_eps //; assume_near x.
end_near; rewrite /= !near_simpl.
by apply: littleoP; rewrite divr_gt0 ?addr_gt0 ?normm_gt0.
Qed.

End Limit.

Section Domination2.
(* Context {K : absRingType} {T : Type} {V W X : normedModType K}. *)


(* Context {K : absRingType} {T : Type} {V W X : normedModType K}. *)

(* Lemma eqo_transo (F : filter_on T) f g :  *)
(*    @the_littleo _ _ _ *)

(*   f ='o_F g -> 'o_F f = 'o_F g *)
(* Proof. *)
(* by move=> -> ->; apply: eqoE; rewrite funeqE=> x; rewrite /= -addrA addo. *)
(* Qed. *)
  (*
 *)
End Domination2.

Section Shift.

Context {R : zmodType} {T : Type}.

Definition shift (x y : R) := y + x.
Notation center c := (shift (- c)).
Arguments shift x / y.

Lemma comp_shiftK (x : R) (f : R -> T) : (f \o shift x) \o center x = f.
Proof. by rewrite funeqE => y /=; rewrite addrNK. Qed.

Lemma comp_centerK (x : R) (f : R -> T) : (f \o center x) \o shift x = f.
Proof. by rewrite funeqE => y /=; rewrite addrK. Qed.

Lemma shift0 : shift 0 = id.
Proof. by rewrite funeqE => x /=; rewrite addr0. Qed.

Lemma center0 : center 0 = id.
Proof. by rewrite oppr0 shift0. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

Section Differential.

Context {K : absRingType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  get (fun (df : V -> W) =>
       f = cst (lim (f @ F)) + df \o center (lim F)
           +o_F (center (lim F))).

Notation "''d_' F" := (@diff _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").


Definition differentiable_def (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
   f = cst (lim (f @ F)) + 'd_F f \o center (lim F) +o_F (center (lim F)).

Notation differentiable F := (@differentiable_def _ (Phantom _ [filter of F])).

Lemma lim_id (x : V) : lim x = x.
Proof.
symmetry; apply: is_filter_lim_locally_unique.
by apply/cvg_ex; exists x.
Qed.

Lemma littleo_shift (y x : V) (f : V -> W) (e : V -> V) :
  littleo (locally y) (f \o shift (x - y)) (e \o shift (x - y)) ->
  littleo (locally x) f e.
Proof.
rewrite /=; move=> fe eps; have /locally_normP [d _ de] := fe eps.
apply/locally_normP; exists d => // z xdz.
have /= := de (z + y - x); rewrite -!addrA addKr subrr addr0; apply.
by rewrite /ball_norm addrA opprB addrC opprD -addrA addrNK.
Qed.

Lemma littleo_center0 (x : V) (f : V -> W) (e : V -> V) :
  littleo_fun (mklittleo x f e) =
  (mklittleo (0 : V) (f \o shift x) (e \o shift x)) \o center x.
Proof.
rewrite /the_littleo /insubd /=; have [g /= _ <-{f}|/asboolP Nfe] /= := insubP.
  rewrite insubT //= ?comp_shiftK //; apply/asboolP; apply: (@littleo_shift x).
  by rewrite sub0r !comp_shiftK => ?; apply: littleoP.
rewrite insubF //; apply/asboolP => fe; apply: Nfe.
by apply: (@littleo_shift 0); rewrite subr0.
Qed.

Lemma diff_locally (x : V) (f : V -> W) : differentiable x f ->
  f \o shift x = cst (lim (f @ x)) + 'd_x f +o_(0 : V) id.
Proof.
move=> dxf; apply: eqoE; rewrite funeqE {1}dxf {dxf} => h /=.
congr (_ + _ + _); rewrite ?lim_id ?addrK //=.
rewrite littleo_center0 /= ?addrK; congr (the_littleo _ _ _ _ _).
by rewrite funeqE => k /=; rewrite addrK.
Qed.

End Differential.
