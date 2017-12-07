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

Program Definition fct_lmodMixin (U : Type) (R : ringType) (V : lmodType R)
  := @LmodMixin R [zmodType of U -> V] (fun k f => k \*: f) _ _ _ _.
Next Obligation. rewrite funeqE => x; exact: scalerA. Qed.
Next Obligation. by move=> f; rewrite funeqE => x /=; rewrite scale1r. Qed.
Next Obligation. by move=> f g h; rewrite funeqE => x /=; rewrite scalerDr. Qed.
Next Obligation. by move=> f g; rewrite funeqE => x /=; rewrite scalerDl. Qed.
Canonical fct_lmodType U (R : ringType) (V : lmodType R) :=
  LmodType _ (U -> V) (fct_lmodMixin U V).

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
Notation "{o_ F f }" := (littleo_type F f)
  (at level 0, F at level 0, format "{o_ F  f }").

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Lemma littleo0_subproof F g : Filter F -> littleo F 0 g.
Proof.
move=> FF _/posrealP[eps] /=; apply: filterE => x; rewrite normm0.
by rewrite mulr_ge0 // ltrW.
Qed.

Canonical littleo0 (F : filter_on T) g :=
  Littleo (asboolT (@littleo0_subproof F g _)).

Lemma littleo_boolP (F : set (set T)) (g : T -> W) (f : {o_F g}) : `[<littleo F f g>].
Proof. by case: f => ?. Qed.
Hint Resolve littleo_boolP.

Lemma littleoP (F : set (set T)) (g : T -> W) (f : {o_F g}) : littleo F f g.
Proof. exact/asboolP. Qed.
Hint Resolve littleoP.

Definition the_littleo (F : filter_on T) (phF : phantom (set (set T)) F) f h :=
   insubd (littleo0 F h) f.
Arguments the_littleo : simpl never, clear implicits.

Notation mklittleo x := (the_littleo _ (Phantom _ [filter of x])).
Notation "[o_ x e 'of' f ]" := (mklittleo x f e)
  (at level 0, x, e at level 0, format "[o_ x  e  'of'  f ]").

Lemma littleoE (F : filter_on T) f h : littleo F f h ->
  ([o_F h of f] : _ -> _) = f.
Proof. by move=> /asboolP?; rewrite /the_littleo /insubd insubT. Qed.

Notation "f = g '+o_' F h" :=
  ((f%function : _ -> _)= (g%function : _ -> _) + [o_F h of f \- g])
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" :=
  ((f%function : _ -> _)= [o_F h of f])
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Lemma add_littleo_subproof (F : filter_on T) e (df dg : {o_F e}) :
  littleo F (df \+ dg) e.
Proof.
move=> _/posrealP[eps]; near x => /=.
  rewrite (double_var eps) mulrDl.
  rewrite (ler_trans (ler_normm_add _ _)) // ler_add //; assume_near x.
by end_near; apply: littleoP.
Qed.

Canonical add_littleo (F : filter_on T) e (df dg : {o_F e}) :=
  Littleo (asboolT (add_littleo_subproof df dg)).

Lemma addo (F : filter_on T) (f g: T -> V) e :
  ([o_F e of f] : _ -> _) + [o_F e of g] =
  [o_F e of add_littleo [o_F e of f] [o_F e of g]].
Proof. by rewrite [RHS]littleoE. Qed.

Lemma addox (F : filter_on T) (f g: T -> V) e x :
  [o_F e of f] x + [o_F e of g] x =
  [o_F e of add_littleo [o_F e of f] [o_F e of g]] x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addo. Qed.

(* This notation is printing only in order to display 'o
   without looking at the contents *)
Notation "''o' '_' F" := (mklittleo F _ _)
  (at level 0, F at level 0, format "''o' '_' F").

Lemma eqadd_some_oP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + [o_F e of h] -> littleo F (f - g) e.
Proof.
rewrite /the_littleo /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_] eps  /=.
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: littleoP.
Qed.

Lemma eqaddoP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +o_ F e) <-> (littleo F (f - g) e).
Proof.
by split=> [/eqadd_some_oP|fg_o_e]; rewrite ?littleoE // addrC addrNK.
Qed.

Lemma eqoP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =o_ F e) <-> (littleo F f e).
Proof. by rewrite -[f]subr0 -eqaddoP -[f \- 0]/(f - 0) subr0 add0r. Qed.

Lemma eq_some_oP (F : filter_on T) (e : T -> W) (f : T -> V) h :
   f = [o_F e of h] -> littleo F f e.
Proof. by have := @eqadd_some_oP F f 0 e h; rewrite add0r subr0. Qed.

(* replaces a 'o_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqaddoE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + [o_F e of h] -> f = g +o_ F e.
Proof. by move=> /eqadd_some_oP /eqaddoP. Qed.

Lemma eqoE (F : filter_on T) (f : T -> V) h (e : T -> W) :
  f = [o_F e of h] -> f =o_ F e.
Proof. by move=> /eq_some_oP /eqoP. Qed.

Lemma littleo_eqo (F : filter_on T) (g : T -> W) (f : {o_F g}) : f =o_F g.
Proof. by apply/eqoP; apply: littleoP. Qed.

Lemma eqo_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [o_ F e of fg] -> g = h + [o_F e of gh] -> f = h +o_F e.
Proof. by move=> -> ->; apply: eqaddoE; rewrite -addrA addo. Qed.

Lemma scale_littleo_subproof (F : filter_on T) e (df : {o_F e}) a :
  littleo F (a *: (df : _ -> _)) e.
Proof.
have [->|a0] := eqVneq a 0; first by rewrite scale0r.
move=> _ /posrealP[eps]; have aa := absr_eq0 a; near x => /=.
  rewrite (ler_trans (ler_normmZ _ _)) //.
  by rewrite -ler_pdivl_mull ?ltr_def ?aa ?a0 //= mulrA; assume_near x.
by end_near; apply: littleoP; rewrite mulr_gt0 // invr_gt0 ?ltr_def ?aa ?a0 /=.
Qed.

Canonical scale_littleo (F : filter_on T) e a (df : {o_F e}) :=
  Littleo (asboolT (scale_littleo_subproof df a)).

Lemma scaleo (F : filter_on T) a (f : T -> V) e :
  a *: ([o_F e of f] : _ -> _) =
  [o_F e of scale_littleo a [o_F e of f]].
Proof. by rewrite [RHS]littleoE. Qed.

Definition bigOW (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists k, \near x in F, `|[f x]| <= k * `|[g x]|.

Definition bigO (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists2 k, k > 0 & \near x in F, `|[f x]| <= k * `|[g x]|.

Lemma bigOWE (F : set (set T)) : Filter F -> bigOW F = bigO F.
Proof.
rewrite predeq2E => f g; split=> [[k] | [k k_gt0]] kP; last by exists k.
exists (maxr k 1); first by rewrite ltr_maxr ltr01 orbT.
by apply: filterS kP => x /ler_trans; apply; rewrite ler_wpmul2r // ler_maxr lerr.
Qed.

Lemma bigOWP (F : set (set T)) f g : Filter F -> bigOW F f g -> bigO F f g.
Proof. by move=> /bigOWE->. Qed.

Lemma bigOWI (F : set (set T)) f g : Filter F -> bigO F f g -> bigOW F f g.
Proof. by move=> /bigOWE->. Qed.

Structure bigO_type (F : set (set T)) (g : T -> W) := BigO {
  bigO_fun :> T -> V;
  _ : `[< bigO F bigO_fun g >]
}.
Notation "{O_ F f }" := (bigO_type F f)
  (at level 0, F at level 0, format "{O_  F  f }").

Canonical bigO_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@bigO_fun F g)].

Lemma bigO0_subproof F g : Filter F -> bigO F 0 g.
Proof.
move=> FF; apply/bigOWP.
by exists 0 => //; apply: filterE=> x; rewrite normm0 mul0r.
Qed.

Canonical bigO0 (F : filter_on T) g :=
 BigO (asboolT (@bigO0_subproof F g _)).

Lemma bigO_boolP (F : set (set T)) (g : T -> W) (f : {O_F g}) : `[<bigO F f g>].
Proof. by case: f => ?. Qed.
Hint Resolve bigO_boolP.

Lemma bigOP (F : set (set T)) (g : T -> W) (f : {O_F g}) : bigO F f g.
Proof. exact/asboolP. Qed.
Hint Resolve bigOP.

Lemma bigOW_hint (F : filter_on T) (g : T -> W) (f : {O_F g}) : bigOW F f g.
Proof. exact/bigOWI. Qed.
Hint Resolve bigOW_hint.

Definition the_bigO (F : filter_on T) (phF : phantom (set (set T)) F) f h :=
   insubd (bigO0 F h) f.
Arguments the_bigO : simpl never, clear implicits.

Notation mkbigO x := (the_bigO _ (Phantom _ [filter of x])).
Notation "[O_ x e 'of' f ]" := (mkbigO x f e)
  (at level 0, x, e at level 0, format "[O_ x  e  'of'  f ]").

Lemma bigOE (F : filter_on T) f h : bigO F f h ->
  ([O_F h of f] : _ -> _) = f.
Proof. by move=> /asboolP?; rewrite /the_bigO /insubd insubT. Qed.

Notation "f = g '+O_' F h" :=
  ((f%function : _ -> _) = (g%function : _ -> _) + [O_F h of f \- g])
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+O_' F  h").
Notation "f '=O_' F h" :=
  ((f%function : _ -> _) = [O_F h of f])
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=O_' F  h").

Lemma add_bigO_subproof (F : filter_on T) e (df dg : {O_F e}) :
  bigO F (df \+ dg) e.
Proof.
have [[_/posrealP[kf] xkf] [_ /posrealP[kg] xkg]] := (bigOP df, bigOP dg).
exists (pos kf + kg) => //; apply: filterS2 xkf xkg => x /ler_add fD/fD{fD}.
by rewrite mulrDl; apply: ler_trans; apply: ler_normm_add.
Qed.

Canonical add_bigO (F : filter_on T) e (df dg : {O_F e}) :=
  BigO (asboolT (add_bigO_subproof df dg)).

Lemma addO (F : filter_on T) (f g: T -> V) e :
  ([O_F e of f] : T -> V) + [O_F e of g] =
  [O_F e of add_bigO [O_F e of f] [O_F e of g]].
Proof. by rewrite [RHS]bigOE //; case: (add_bigO _ _) => ? /= /asboolP. Qed.

Lemma addOx (F : filter_on T) (f g: T -> V) e x :
  [O_F e of f] x + [O_F e of g] x =
  [O_F e of add_bigO [O_F e of f] [O_F e of g]] x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addO. Qed.

(* This notation is printing only in order to display 'O
   without looking at the contents *)
Notation "''O' '_' F" := (mkbigO F _ _)
  (at level 0, F at level 0, format "''O' '_' F").

Lemma eqadd_some_OP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + [O_F e of h] -> bigO F (f - g) e.
Proof.
rewrite /the_bigO /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_].
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: bigOP.
Qed.

Lemma eqaddOP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +O_ F e) <-> (bigO F (f - g) e).
Proof. by split=> [/eqadd_some_OP|fg_O_e]; rewrite ?bigOE // addrC addrNK. Qed.

Lemma eqOP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =O_ F e) <-> (bigO F f e).
Proof. by rewrite -[f]subr0 -eqaddOP -[f \- 0]/(f - 0) subr0 add0r. Qed.

Lemma eq_some_OP (F : filter_on T) (e : T -> W) (f : T -> V) h :
   f = [O_F e of h] -> bigO F f e.
Proof. by have := @eqadd_some_OP F f 0 e h; rewrite add0r subr0. Qed.

Lemma bigO_eqO (F : filter_on T) (g : T -> W) (f : {O_F g}) : f =O_F g.
Proof. by apply/eqOP; apply: bigOP. Qed.

Lemma eqO_bigO (F : filter_on T) (e : T -> W) (f : T -> V) :
   f =O_ F e -> bigO F f e.
Proof. by rewrite eqOP. Qed.

(* replaces a 'O_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqaddOE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g +[O_F e of h] -> f = g +O_ F e.
Proof. by move=> /eqadd_some_OP /eqaddOP. Qed.

Lemma eqOE (F : filter_on T) (f : T -> V) h (e : T -> W) :
  f = [O_F e of h] -> f =O_F e.
Proof. by move=> /eq_some_OP /eqOP. Qed.

Lemma littleo_bigO (F : filter_on T) (f : T -> V) (e : T -> W) :
  ([o_F e of f] : _ -> _) =O_F e.
Proof.
by apply/eqOP; exists 1 => //; case: the_littleo => g /= /asboolP; apply.
Qed.
Hint Resolve littleo_bigO.

Lemma littleo_eqO (F : filter_on T) (e : T -> W) (f : {o_F e}) : f =O_F e.
Proof. by apply: eqOE; rewrite littleo_eqo littleo_bigO. Qed.

Canonical littleo_is_bigO (F : filter_on T) (e : T -> W) (f : {o_F e}) :=
  BigO (asboolT (eqO_bigO (littleo_eqO f))).

Lemma eqO_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [O_ F e of fg] -> g = h + [O_F e of gh] -> f = h +O_F e.
Proof. by move=> -> ->; apply: eqaddOE; rewrite -addrA addO. Qed.

End Domination.

Notation "{o_ F f }" := (@littleo_type _ _ _ _ F f)
  (at level 0, F at level 0, format "{o_ F  f }").

Arguments the_littleo {_ _ _ _} _ _ _ _ : simpl never.
Notation mklittleo x := (the_littleo _ (Phantom _ [filter of x])).
Notation "[o_ x e 'of' f ]" := (mklittleo x f e)
  (at level 0, x, e at level 0, format "[o_ x  e  'of'  f ]").

Notation "f = g '+o_' F h" :=
  ((f%function : _ -> _) = (g%function : _ -> _) + [o_F h of f \- g])
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Notation "f '=o_' F h" :=
  ((f%function : _ -> _) = [o_F h of f])
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").

Notation "''o' '_' F" := (mklittleo F _)
  (at level 0, F at level 0, format "''o' '_' F").

Notation "{O_ F f }" := (@bigO_type _ _ _ _ F f)
  (at level 0, F at level 0, format "{O_ F  f }").

Arguments the_bigO {_ _ _ _} _ _ _ _ : simpl never.
Notation mkbigO x := (the_bigO _ (Phantom _ [filter of x])).
Notation "[O_ x e 'of' f ]" := (mkbigO x f e)
  (at level 0, x, e at level 0, format "[O_ x  e  'of'  f ]").

Notation "f = g '+O_' F h" :=
  (f%function = g%function +
     mkbigO F (f \- g : _ -> _) h)
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+O_' F  h").
Notation "f '=O_' F h" :=
  (f%function = mkbigO F (f%function : _ -> _) h)
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=O_' F  h").

Notation "''O' '_' F" := (mkbigO F _)
  (at level 0, F at level 0, format "''O' '_' F").

Hint Resolve littleoP.
Hint Resolve littleo_boolP.
Hint Resolve bigOP.
Hint Resolve bigO_boolP.
Hint Resolve bigOP.
Hint Resolve bigOW_hint.
Hint Resolve littleo_bigO.
Hint Resolve littleo_eqO.

Section Limit.

Context {K : absRingType} {T : Type} {V W X : normedModType K}.

Lemma eqolimP (F : filter_on T) (f : T -> V) (l : V) :
  f @ F --> l <-> f = cst l +o_F (cst (1 : K^o)).
Proof.
split=> fFl.
  apply/eqaddoP => _/posrealP[eps]; near x.
    by rewrite /cst ltrW //= normmB; assume_near x.
  by end_near; apply: (flim_norm _ fFl); rewrite mulr_gt0 // ?absr1_gt0.
apply/flim_normP=> _/posrealP[eps]; rewrite !near_simpl.
have lt_eps x : x <= (pos eps / 2%:R) * `|1 : K^o|%real -> x < pos eps.
  rewrite absr1 mulr1 => /ler_lt_trans; apply.
  by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
near x.
  by rewrite [X in X x]fFl opprD addNKr normmN lt_eps //; assume_near x.
by end_near; rewrite /= !near_simpl; apply: littleoP; rewrite divr_gt0.
Qed.

Lemma eqolim (F : filter_on T) (f : T -> V) (l : V) e :
  f = cst l + [o_F (cst (1 : K^o)) of e] -> f @ F --> l.
Proof. by move=> /eqaddoE /eqolimP. Qed.

Lemma eqolim0P (F : filter_on T) (f : T -> V) :
  f @ F --> (0 : V) <-> f =o_F (cst (1 : K^o)).
Proof. by rewrite eqolimP add0r -[f \- cst 0]/(f - 0) subr0. Qed.

Lemma eqolim0 (F : filter_on T) (f : T -> V) :
  f =o_F (cst (1 : K^o)) -> f @ F --> (0 : V).
Proof. by move=> /eqoE /eqolim0P. Qed.

Lemma bigO_littleo {F : filter_on T} (g : T -> W) (f : T -> V) (h : T -> X) :
  f =O_F g -> [o_F f of h] =o_F g.
Proof.
move->; apply/eqoP => _/posrealP[eps].
set k := [O_F g of _]; have [/= _/posrealP[c]] := bigOP k.
apply: filter_app; near x.
  rewrite -!ler_pdivr_mull //; apply: ler_trans.
  by rewrite ler_pdivr_mull // mulrA; assume_near x.
by end_near; rewrite /= !near_simpl; apply: littleoP.
Qed.
Arguments bigO_littleo {F}.

Lemma addfo (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =o_F e -> f + [o_F e of h] =o_F e.
Proof. by move->; apply/eqoE; rewrite addo. Qed.

Example littleo_littleo (F : filter_on T) (f : T -> V) (g : T -> W) g' (h : T -> X) :
  f = [o_F g of g'] -> [o_F f of h] =o_F g.
Proof. by move=> ->; apply: eqoE; rewrite (bigO_littleo g). Qed.

End Limit.

Arguments bigO_littleo {K T V W X F}.

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

Lemma linear_continuous (f: {linear U -> V | GRing.Scale.op s_law}) :
  (f : _ -> _) =O_(0 : U) (cst (1 : R^o)) -> continuous f.
Proof.
move=> /eqOP [_/posrealP[l]].
rewrite /= => /locally_normP [_/posrealP[d]]; rewrite /cst /=.
rewrite [`|[1 : R^o]|]absr1 mulr1 => fl.
have [{l fl}_ /posrealP[l] f_lipshitz] :
  exists2 l, l > 0 & forall x , `|[f x]| <= l * `|[x]|.
  exists (pos l / ((d : R) / 2)%coqR) => //.
  move=> x; have := fl ((pos d / 2)%coqR * `|[x]| ^-1 *: x).
  rewrite /ball_norm sub0r normmN.
  (** BUG! in a vector space, the normm should be totally scalable : normmZ *)
  admit.
move=> x; apply/flim_normP => _/posrealP[eps]; rewrite !near_simpl.
rewrite (near_shift 0) /= subr0; near y => /=.
  rewrite -linearB opprD addrC addrNK linearN normmN.
  by rewrite (ler_lt_trans (f_lipshitz _)) // -ltr_pdivl_mull //; assume_near y.
end_near.
apply/locally_normP.
by eexists; last by move=> ?; rewrite /ball_norm sub0r normmN; apply.
Admitted.

End Linear3.

Arguments linear_continuous {U V s s_law} f _.

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
  ([o_x e of f] : _ -> _) =
  [o_(0 : V) (e \o shift x) of f \o shift x] \o center x.
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

Section DifferentialR.

Context {V W : normedModType R}.

Lemma diff_continuous (x : V) (f : V -> W) :
  differentiable x f -> ('d_x f : _ -> _) =O_(0 : V) (cst (1 : R^o)) -> {for x, continuous f}.
Proof.
move=> dxf dxfO; have /diff_locally := dxf; rewrite -addrA.
rewrite (bigO_littleo (cst (1 : R^o))); last first.
  apply/eqOP; exists 1 => //; rewrite /cst mul1r [`|[1 : R^o]|]absr1.
  near y; [rewrite ltrW //; assume_near y|end_near].
  by apply/locally_normP; eexists=> [|?];
    last (rewrite /ball_norm ?sub0r ?normmN; apply).
rewrite addfo; first by move=> /eqolim; rewrite flim_shift add0r.
apply/eqolim0P; apply: (flim_trans (linear_continuous _ _ _)) => //.
by rewrite linear0.
Qed.

End DifferentialR.