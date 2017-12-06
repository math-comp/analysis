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

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Canonical linear_eqType := EqType {linear U -> V | s} gen_eqMixin.
Canonical linear_choiceType := ChoiceType {linear U -> V | s} gen_choiceMixin.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).
Canonical linear_pointedType := PointedType {linear U -> V | GRing.Scale.op s_law}
                                            (@GRing.null_fun_linear R U V s s_law).
End Linear2.

(* Tentative to handle small o and big O notations *)
Section Domination.

Context {K : absRingType} {T : Type} {V W : normedModType K}.

Definition littleo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps : R, 0 < eps -> \near x in F, `|[f x]| <= eps * `|[g x]|.

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
move=> FF _/posrealP[eps] /=; apply: filter_forall => x; rewrite normm0.
by rewrite mulr_ge0 // ltrW.
Qed.

Canonical little0 (F : filter_on T) g := Littleo (asboolT (@littleo0 F g _)).

Lemma littleoP (F : set (set T)) (g : T -> W) (f : 'o_F g) : littleo F f g.
Proof. by case: f => ? /= /asboolP. Qed.

Definition the_littleo (F : filter_on T) (phF : phantom (set (set T)) F) f h :=
   insubd (little0 F h) f.
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
move=> _/posrealP[eps]; near x => /=.
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

(* replaces a 'o_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqoE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + mklittleo F h e -> f = g +o_ F e.
Proof. by move=> /eqadd_some_oP /eqaddoP. Qed.

Lemma eqo_trans (F : filter_on T) (f g h : T -> V) (e : T -> W):
  f = g +o_ F e -> g = h +o_F e -> f = h +o_F e.
Proof. by move=> -> ->; apply: eqoE; rewrite -addrA addo. Qed.

Definition bigo (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists k, \near x in F, `|[f x]| <= k * `|[g x]|.

Structure bigo_type (F : set (set T)) (g : T -> W) := Bigo {
  bigo_fun :> T -> V;
  _ : `[< bigo F bigo_fun g >]
}.
Notation "''O_' F" := (bigo_type F)
  (at level 0, F at level 0, format "''O_' F").

Canonical bigo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@bigo_fun F g)].

Lemma bigo0 F g : Filter F -> bigo F 0 g.
Proof.
by move=> FF; exists 0; apply: filter_forall=> x; rewrite normm0 mul0r.
Qed.

Canonical big0 (F : filter_on T) g := Bigo (asboolT (@bigo0 F g _)).

Lemma bigoP (F : set (set T)) (g : T -> W) (f : 'O_F g) : bigo F f g.
Proof. by case: f => ? /= /asboolP. Qed.

Definition the_bigo (F : filter_on T) (phF : phantom (set (set T)) F) f h :=
   insubd (big0 F h) f.
Arguments the_bigo : simpl never, clear implicits.

Notation mkbigo x := (the_bigo _ (Phantom _ [filter of x])).

Notation "f = g '+O_' F h" :=
  (f%function = g%function + mkbigo F (f \- g) h)
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+O_' F  h").
Notation "f '=O_' F h" := (f = \0 +O_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=O_' F  h").

Lemma add_bigo_subproof (F : filter_on T) e (df dg :'O_F e) :
  bigo F (df \+ dg) e.
Proof.
have [[kf xkf] [kg xkg]] := (bigoP df, bigoP dg).
exists (kf + kg); apply: filterS2 xkf xkg => x /ler_add fD/fD{fD}.
by rewrite mulrDl; apply: ler_trans; apply: ler_normm_add.
Qed.

Canonical add_bigo (F : filter_on T) e (df dg :'O_F e) :=
  Bigo (asboolT (add_bigo_subproof df dg)).

Lemma addO (F : filter_on T) (f g: T -> V) e :
  (mkbigo F f e : T -> V) + (mkbigo F g e : T -> V) =
  mkbigo F
    (add_bigo (mkbigo F f e) (mkbigo F g e)) e.
Proof.
rewrite {3}/the_bigo /insubd insubT //; apply/asboolP.
by case: (add_bigo _ _) => ? /= /asboolP.
Qed.

Lemma addOx (F : filter_on T) (f g: T -> V) e x :
  mkbigo F f e x + mkbigo F g e x =
  mkbigo F ((add_bigo (mkbigo F f e) (mkbigo F g e))) e x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addO. Qed.

(* This notation is printing only in order to display 'O
   without looking at the contents *)
Notation "''O' '_' F" := (mkbigo F _ _)
  (at level 0, F at level 0, format "''O' '_' F").

Lemma eqadd_some_OP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + mkbigo F h e -> bigo F (f - g) e.
Proof.
rewrite /the_bigo /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_].
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: bigoP.
Qed.

Lemma eqaddOP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +O_ F e) <-> (bigo F (f - g) e).
Proof.
split=> [/eqadd_some_OP//|/asboolP fg_O_e].
by rewrite /the_bigo /insubd insubT /= addrC addrNK.
Qed.

Lemma eqOP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =O_ F e) <-> (bigo F f e).
Proof. by rewrite eqaddOP subr0. Qed.

(* replaces a 'O_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqOE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + mkbigo F h e -> f = g +O_ F e.
Proof. by move=> /eqadd_some_OP /eqaddOP. Qed.

Lemma eqO_trans (F : filter_on T) (f g h : T -> V) (e : T -> W):
  f = g +O_ F e -> g = h +O_F e -> f = h +O_F e.
Proof. by move=> -> ->; apply: eqOE; rewrite -addrA addO. Qed.

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

Notation "''o_' F" := (@littleo_type _ _ _ _ F)
  (at level 0, F at level 0, format "''o_' F").

Arguments the_bigo {_ _ _ _} _ _ _ _ : simpl never.
Notation mkbigo x := (the_bigo _ (Phantom _ [filter of x])).

Notation "f = g '+O_' F h" :=
  (f%function = g%function +
     mkbigo F (f \- g : _ -> _) h)
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+O_' F  h").
Notation "f '=O_' F h" := (f = \0 +O_ F h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=O_' F  h").

Notation "''O' '_' F" := (mkbigo F _)
  (at level 0, F at level 0, format "''O' '_' F").

Section Limit.

Context {K : absRingType} {T : Type} {V W X : normedModType K}.

Lemma eqolimP (F : filter_on T) (f : T -> V) (l : V) (k : W) : k != 0 ->
  f @ F --> l <-> f = cst l +o_F (cst k).
Proof.
move=> k_gt0; split=> fF.
  apply/eqaddoP => _/posrealP[eps]; near x.
    by rewrite /cst ltrW //= normmB; assume_near x.
  by end_near; apply: (flim_norm _ fF); rewrite mulr_gt0 ?normm_gt0.
apply/flim_normP=> _/posrealP[eps]; rewrite !near_simpl.
have lt_eps x : x <= (pos eps / (`|[k]| + 1)) * `|[k]| -> x < pos eps.
  rewrite -mulrA => /ler_lt_trans; apply; rewrite -ltr_pdivl_mull ?mulVf //.
  by rewrite ltr_pdivr_mull ?mulr1 ?ltr_addl ?addr_gt0 ?normm_gt0.
near x.
  rewrite [X in X x]fF opprD addNKr normmN lt_eps //; assume_near x.
end_near; rewrite /= !near_simpl.
by apply: littleoP; rewrite divr_gt0 ?addr_gt0 ?normm_gt0.
Qed.

Lemma littleo_littleo (F : filter_on T) (f : T -> V) (g : T -> W) (h : T -> X) :
  f =o_F g -> ((mklittleo F h f) : _ -> _) =o_F g.
Proof.
move=> /eqaddoP; rewrite subr0 => f_eq_og; apply/eqaddoP.
rewrite subr0 => _/posrealP[eps].
set k := the_littleo _ _ _ _; have kf := littleoP k.
near x.
  apply: (@ler_trans _ (Num.sqrt (eps : R) * `|[f x]|)); first by assume_near x.
  rewrite -{2}[eps : R]sqr_sqrtr // -mulrA ler_pmul ?sqrtr_ge0 //.
  by assume_near x.
by end_near; [apply: kf|apply: f_eq_og].
Qed.

Lemma addfo (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =o_F e -> f + mklittleo F h e =o_F e.
Proof. by move->; apply/eqoE; rewrite !add0r addo. Qed.

End Limit.

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

Lemma near_shift {K : absRingType} {R : normedModType K}
   (y x : R) (P : set R) :
   (\near x, P x) = (\near z in y, (P \o shift (x - y)) z).
Proof.
rewrite propeqE; split=> /= /locally_normP [_/posrealP[e] ye];
apply/locally_normP; exists e=> // t /= et.
  apply: ye; rewrite /ball_norm !opprD addrA addrACA subrr add0r.
  by rewrite opprK addrC.
have /= := ye (t - (x - y)); rewrite addrNK; apply.
by rewrite /ball_norm !opprB addrA addrCA subrr addr0.
Qed.

Lemma flim_shift {T : Type}  {K : absRingType} {R : normedModType K}
  (x y : R) (f : R -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Section Linear3.
Context (U : normedModType R) (V : normedModType R) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).

Lemma linear_continuous (f: {linear U -> V | GRing.Scale.op s_law}) (k : V) :
  k != 0 -> (f : _ -> _) =O_(0 : U) (cst k) -> continuous f.
Proof.
move=> k_neq0 /eqaddOP [l]; rewrite subr0 /= => /locally_normP [_/posrealP[d]].
rewrite /cst /=; move: (_ * _) => {l k k_neq0}l fl.
have [{l fl}l f_lipshitz] : exists l, forall x , `|[f x]| <= l * `|[x]|.
  exists (l / ((d : R) / 2)%coqR).
  move=> x; have := fl ((pos d / 2)%coqR * `|[x]| ^-1 *: x).
  rewrite /ball_norm sub0r normmN.
  (** BUG! in a vector space, the normm is totally scalable : normmZ *)
  admit.
have [l_gt0|l_le0] := ltrP 0 l; last first.
  suff ->: (f : U -> V) = (0 : U -> V).
    by move=> x; apply: (flim_trans (flim_const 0)).
  rewrite funeqE => x /=; apply/eqP; rewrite -normm_eq0.
  by rewrite eqr_le normm_ge0 andbT (ler_trans (f_lipshitz _)) // mulr_le0_ge0.
move: l_gt0 => /posrealP[{l}l] in f_lipshitz *.
move=> x; apply/flim_normP => _/posrealP[eps]; rewrite !near_simpl.
rewrite (near_shift 0) /= subr0; near y => /=.
  rewrite -linearB opprD addrC addrNK linearN normmN.
  by rewrite (ler_lt_trans (f_lipshitz _)) // -ltr_pdivl_mull //; assume_near y.
end_near.
apply/locally_normP.
by eexists; last by move=> ?; rewrite /ball_norm sub0r normmN; apply.
Admitted.

End Linear3.


Section Differential.

Context {K : absRingType} {V W : normedModType K}.

Definition diff (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
  get (fun (df : {linear V -> W}) =>
       f = cst (f (lim F)) + df \o center (lim F)
           +o_F (center (lim F))).

Notation "''d_' F" := (@diff _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").

Definition differentiable_def (F : filter_on V) (_ : phantom (set (set V)) F) (f : V -> W) :=
   f = cst (f (lim F)) + 'd_F f \o center (lim F) +o_F (center (lim F)).

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
move=> fe _/posrealP[eps]; rewrite near_simpl (near_shift y).
exact: filterS (fe _ [gt0 of eps]).
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
  f \o shift x = cst (f x) + 'd_x f +o_(0 : V) id.
Proof.
move=> dxf; apply: eqoE; rewrite funeqE {1}dxf {dxf} => h /=.
congr (_ + _ + _); rewrite ?lim_id ?addrK //=.
rewrite littleo_center0 /= ?addrK; congr (the_littleo _ _ _ _ _).
by rewrite funeqE => k /=; rewrite addrK.
Qed.

End Differential.

Notation "''d_' F" := (@diff _ _ _ _ (Phantom _ [filter of F]))
  (at level 0, F at level 0, format "''d_' F").
Notation differentiable F := (@differentiable_def _ _ _ _ (Phantom _ [filter of F])).

Section DifferentialR.

Context {V W : normedModType R}.

Lemma diff_continuous (x : V) (f : V -> W) (k : W) : k != 0 ->
  differentiable x f -> ('d_x f : _ -> _) =O_(0 : V) (cst k) -> {for x, continuous f}.
Proof.
move=> kn0 dxf dxfO; have /diff_locally := dxf; rewrite -addrA.
rewrite (@littleo_littleo _ _ _ _ _ _ _ (cst k)); last first.
  apply/eqaddoP=> _/posrealP[eps] /=; rewrite !near_simpl subr0 /cst.
  near y; [rewrite ltrW //; assume_near y|end_near].
  apply/locally_normP; eexists=> [|?]; last first.
    by rewrite /ball_norm ?sub0r ?normmN; apply.
  by rewrite mulr_gt0 // normm_gt0.
rewrite add0r addfo; last first.
  apply/eqolimP => //.
  apply: flim_trans (@linear_continuous _ _ _ _ _ k _ _ _) _ => //.
  by rewrite linear0.
by rewrite add0r => /eqoE /eqolimP -/(_ kn0); rewrite flim_shift add0r.
Qed.

End DifferentialR.