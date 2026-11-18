(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import poly sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau differential.

(**md**************************************************************************)
(* # Differentiation                                                          *)
(*                                                                            *)
(* This file contains lemmas about differentiation and matrices.              *)
(*                                                                            *)
(* Parsable notations (f is not supposed to be differentiable):               *)
(* ```                                                                        *)
(*               'J f x == the Jacobian of f at a point x                     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "''J' f p" (at level 10, p, f at next level,
  format "''J'  f  p").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma EVT_max_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
    A !=set0 -> compact A -> {within A, continuous f} ->
  exists2 c, c \in A & forall t, t \in A -> f t <= f c.
Proof. by move=> A0 cA cf; exact: compact_EVT_max. Qed.

Lemma EVT_min_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
  A !=set0 -> compact A -> {within A, continuous f} ->
  exists2 c, c \in A & forall t, t \in A -> f c <= f t.
Proof. by move=> A0 cA cf; exact: compact_EVT_min. Qed.

Section jacobian.

Definition jacobian n m (R : numFieldType) (f : 'rV[R]_n -> 'rV[R]_m) p :=
  lin1_mx ('d f p).

End jacobian.

Notation "''J' f p" := (jacobian f p).

Section DifferentialR2.
Context {d : filter_display} {R : numFieldType}.
Implicit Type V : normedModType d R.

Lemma deriveEjacobian m n (f : 'rV[R]_m -> 'rV[R]_n) (a v : 'rV[R]_m) :
  differentiable f a -> 'D_ v f a = v *m jacobian f a.
Proof. by move=> /deriveE->; rewrite /jacobian mul_rV_lin1. Qed.

End DifferentialR2.

Section DifferentialR3_numFieldType.
Context {R : numFieldType}.
Generalizable Variables d.

Lemma differentiable_coord m n (M : 'M[R]_(m, n)) i j :
  differentiable (fun N : 'M[R]_(m, n) => N i j : R ) M.
Proof.
have @f : {linear 'M[R]_(m, n) -> R}.
  by exists (fun N : 'M[R]_(_, _) => N i j); do 2![eexists]; do ?[constructor];
     rewrite ?mxE// => ? *; rewrite ?mxE//; move=> ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma differentiable_rsubmx m {n1 n2} v :
  differentiable (rsubmx : 'M[R]_(m, n1 + n2) -> 'M[R]_(m, n2)) v.
Proof. exact/linear_differentiable/continuous_rsubmx. Qed.

Lemma differentiable_lsubmx m {n1 n2} v :
  differentiable (lsubmx : 'M[R]_(m, n1 + n2) -> 'M[R]_(m, n1)) v.
Proof. exact/linear_differentiable/continuous_lsubmx. Qed.

End DifferentialR3_numFieldType.

Section pointwise_derivable.
Context {d} {R : realFieldType} {V : normedModType d R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

Lemma derivable_mxP M t v :
  derivable M t v <-> forall i j, derivable (fun x => M x i j) t v.
Proof.
split=> [|Mvt].
- move=> /cvg_ex[/= l Mvtl] i j; apply/cvg_ex; exists (l i j).
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Mvtl => /(_ _ e0)[/= r r0] rMvte.
  near=> x.
  apply: le_trans (rMvte x _ _).
  + rewrite [leRHS]/Num.Def.normr/= mx_normrE.
    apply: le_trans; last exact: le_bigmax.
    by rewrite !mxE.
  + rewrite /ball_/= sub0r normrN.
    by near: x; exact: dnbhs0_lt.
  + by near: x.
- apply/cvg_ex => /=.
  exists (\matrix_(i < m, j < n) sval (cid ((cvg_ex _).1 (Mvt i j)))).
  apply/cvgrPdist_le => /= e e0.
  near=> x.
  rewrite /Num.Def.normr/= mx_normrE (bigmax_le _ (ltW e0))//= => i _.
  rewrite !mxE/=.
  move: i; near: x; apply: filter_forall => /= i.
  exact: ((cvgrPdist_le _ _).1 (svalP (cid ((cvg_ex _).1 (Mvt i.1 i.2))))).
Unshelve. all: by end_near. Qed.

End pointwise_derivable.

Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {d} {R : realFieldType} {V : normedModType d R}.

Lemma derive_mx {m n : nat} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v ->
  'D_v M t = \matrix_(i < m, j < n) 'D_v (fun t => M t i j) t.
Proof.
move=> /cvg_ex[/= l Mvtl]; apply/cvg_lim => //=; apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : (Mvtl) => /(_ (e / 2)) /[!divr_gt0]//.
move=> /(_ isT)[e' /= e0' dle].
near=> x.
rewrite [leLHS]/Num.Def.normr/= mx_normrE (bigmax_le _ (ltW e0))//= => -[i j] _.
rewrite [in leLHS]mxE/= [X in _ + X]mxE -(subrKA (l i j)).
rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
- rewrite mxE.
  suff : (h^-1 *: (M (h *: v + t) i j - M t i j)) @[h --> 0^'] --> l i j.
    move/cvg_lim => /=; rewrite /derive /= => ->//.
    by rewrite subrr normr0 divr_ge0// ltW.
  apply/cvgrPdist_le => /= r r0.
  move/cvgrPdist_le : Mvtl => /(_ r r0)[/= s s0] sr.
  near=> y.
  apply: (@le_trans _ _ (`|l - y^-1 *: (M (y *: v + t) - M t)|)).
    rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
    by under eq_bigr do rewrite !mxE; exact: (le_bigmax _ _ (i, j)).
  rewrite sr//=; last by near: y.
  by rewrite sub0r normrN; near: y; exact: dnbhs0_lt.
- rewrite mxE.
  apply: (@le_trans _ _ `|l - x^-1 *: (M (x *: v + t) - M t)|).
    rewrite [in leRHS]/Num.Def.normr/= mx_normrE/=.
    under eq_bigr do rewrite !mxE.
    apply: le_trans; last exact: le_bigmax.
    by rewrite !mxE.
  apply: dle => //=; last by near: x.
  by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
Unshelve. all: by end_near. Qed.

Lemma is_derive_mx {m n : nat} (M : V -> 'M[R]_(m, n))
    (dM : 'M[R]_(m, n)) (x v : V) :
  (forall i j, is_derive x v (fun t => M t i j) (dM i j)) ->
  is_derive x v M dM.
Proof.
move=> MdM; apply: DeriveDef; first exact/derivable_mxP.
apply/matrixP => i j.
have [_ <-] := MdM i j.
rewrite derive_mx ?mxE//.
apply/derivable_mxP => i0 j0.
by have [] := MdM i0 j0.
Qed.

Lemma derivable_trmx {m n} (M : V -> 'M[R]_(m, n)) t v :
  derivable (fun x => (M x)^T) t v = derivable M t v.
Proof.
suff: forall N, derivable N t v -> derivable (fun x => (N x)^T) t v.
  move=> suf; apply/propext; split; last exact: suf.
  by move=> /suf; under eq_fun do rewrite trmxK.
move=> {}m {}n {}M /cvg_ex[/= l Ml]; apply/cvg_ex => /=; exists l^T.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Ml => /(_ _ e0)[/= r r0 re].
near=> x.
rewrite [leLHS](_ : _ = `|l - x^-1 *: (M (x *: v + t) - M t)|).
  rewrite -[RHS]norm_trmx [in RHS]linearD/= [in RHS]linearN.
  by congr (`| _ - _ |); rewrite [RHS]linearZ/= [in RHS]linearB.
apply: re => /=; last by near: x.
by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
Unshelve. all: by end_near. Qed.

Lemma derive_trmx {m n} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v -> 'D_v (trmx \o M) t = ('D_v M t)^T.
Proof.
move=> Mtv; rewrite !derive_mx//=; first by rewrite derivable_trmx.
apply/matrixP => i j; rewrite !mxE.
by under eq_fun do rewrite mxE.
Qed.

Global Instance is_derive_trmx {m n} (f : V -> 'M[R]_(m, n)) (f' : 'M[R]_(m, n))
    (t : V) w :
  is_derive t w f f' -> is_derive t w (fun x => (f x)^T) f'^T.
Proof.
move=> fD.
have fDer : derivable f t w by case: fD.
apply/DeriveDef; last by have [_ <-] := fD; rewrite derive_trmx.
by rewrite derivable_trmx.
Qed.

Fact dmx {m n : nat} (M : V -> 'M[R]_(m, n)) (x : V) :
  let g := fun t : V => (\matrix_(i < m, j < n) 'd M x t i j) in
  differentiable M x ->
  continuous g /\
  M \o shift x = cst (M x) + g +o_ 0 id.
Proof.
move=> dM Mx; split => [|].
- apply/continuous_mx => i j v; apply/cvgrPdist_le => /= e e0.
  case: Mx => -[+ _] => /(_ v)/cvgrPdist_le/(_ _ e0).
  apply: filterS => /= t; apply: le_trans.
  by rewrite {2}/Num.norm/= mx_normrE (le_trans _ (le_bigmax _ _ (i, j))) ?mxE.
- apply/eqaddoE; rewrite funeqE => y /=.
  rewrite (diff_locallyx Mx) /dM !fctE; congr (_ + _ + _).
  by apply/matrixP => i j/=; rewrite mxE.
Qed.

Lemma diffmx {m n : nat} (M : V -> 'M[R]_(m, n)) x :
  differentiable M x ->
  'd M (nbhs_filter_on x) =
  (fun t : V => \matrix_(i < m, j < n) 'd M x t i j) :> (_ -> _).
Proof.
move=> dM.
set g := fun t : V => \matrix_(i, j) 'd M x t i j.
have glin : linear (g : V -> _).
  move=> a u w.
  by rewrite /g linearD linearZ/=; apply/matrixP => i j; rewrite !mxE.
pose glM := GRing.isLinear.Build _ _ _ _ _ glin.
pose gL : {linear _ -> _} := HB.pack g glM.
by apply: (@diff_unique _ _ _ _ _ _ gL); have [? ?] := dmx dM.
Qed.

Global Instance is_derive_mx_coord n m
    (f : V -> 'M[R]_(n, m)) (f' : 'M[R]_(n,m)) (t : V) w :
  is_derive t w f f' ->
  forall i j, is_derive t w (fun x => f x i j) (f' i j).
Proof.
move=> fD i j /=.
have fDer : derivable f t w by case: fD.
apply/DeriveDef; last by have [_ <-] := fD; rewrite derive_mx// mxE.
by move/derivable_mxP : fDer => /(_ i j).
Qed.

Global Instance is_derive_mulmx n m p
    (M : V -> 'M[R]_(n, m)) M'
    (N : V -> 'M[R]_(m, p)) N' (t : V) w :
  is_derive t w M M'  -> is_derive t w N N' ->
  is_derive t w (fun t => M t *m N t) (M' *m N t + M t *m N').
Proof.
move=> is_der_M' is_der_N'.
apply is_derive_mx => i j /=.
rewrite !mxE/=.
under eq_fun do rewrite mxE/=.
rewrite -!big_split /= -fct_sumE.
apply/is_derive_sum => k.
by rewrite mulrC addrC; exact/is_deriveM.
Qed.

End pointwise_derive.

Section Ris_diff_mx.
Local Open Scope classical_set_scope.
Context {R : realFieldType}.

Global Instance is_diff_mx {m n : nat} (M dM : R -> 'M[R]_(m, n)) (x : R) :
  (forall i j, is_diff x (fun t => M t i j) (fun t => dM t i j)) ->
  is_diff x M dM.
Proof.
move=> /= MdM.
have diffMx : differentiable M (nbhs_filter_on x).
  apply/derivable1_diffP; apply/derivable_mxP => i j.
  by have [/(@derivable1_diffP _ _ _ (fun t => M t i j) x)] := MdM i j.
apply: DiffDef; first exact: diffMx.
rewrite diffmx//=; apply/funext => /= v; apply/matrixP => i j.
rewrite !mxE.
have [diffMij dMdM] := MdM i j.
rewrite -deriveE//.
move/(congr1 (fun f => f v)) : dMdM.
rewrite -(deriveE _ diffMij) => <-.
rewrite derive_mx; last by rewrite /= mxE.
apply/derivable_mxP => i0 j0/=.
by have [/diff_derivable-/(_ v)] := MdM i0 j0.
Qed.

End Ris_diff_mx.

Section derivable_derive_row_mx.
Context {d} {R : realFieldType} {V : normedModType d R} {n1 n2 : nat}.
Implicit Types (f : V -> 'rV[R]_n1) (g : V -> 'rV[R]_n2).

Lemma derivable_row_mx f g t v : derivable f t v -> derivable g t v ->
  derivable (fun x => row_mx (f x) (g x)) t v.
Proof.
move=> /= fv gv; apply/derivable_mxP => i j; rewrite (ord1 i)/=.
have /cvg_ex[/= l Hl] := fv.
have /cvg_ex[/= k Hk] := gv.
apply/cvg_ex => /=; exists (row_mx l k ord0 j).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0) Hl.
move/cvgrPdist_le : Hk => /(_ _ e0) Hk.
move: Hl Hk; apply: filterS2 => x Hl Hk.
rewrite !mxE; case: fintype.splitP => j1 jj1.
- rewrite (le_trans _ Hl)// [in leRHS]/Num.Def.normr/= mx_normrE.
  by rewrite (le_trans _ (le_bigmax _ _ (ord0, j1)))// !mxE.
- rewrite (le_trans _ Hk)// [in leRHS]/Num.Def.normr/= mx_normrE.
  by rewrite (le_trans _ (le_bigmax _ _ (ord0, j1)))// !mxE.
Qed.

Lemma derive_row_mx f g t v : derivable f t v -> derivable g t v ->
  'D_v (fun x => row_mx (f x) (g x)) t = row_mx ('D_v f t) ('D_v g t).
Proof.
move=> fv gv; rewrite derive_mx.
  by apply: derivable_row_mx; [exact: fv|exact: gv].
apply/matrixP => i j.
rewrite !mxE !derive_mx//; case: splitP => k jE; rewrite !mxE; congr ('D_v _ t);
  apply/funext => w; rewrite !mxE; case: splitP => l lE//.
- by congr (f w i _); apply/val_inj => /=; rewrite -jE -lE.
- by absurd: lE; rewrite ltn_eqF//= jE (leq_trans (ltn_ord k))// leq_addr.
- by absurd: lE; rewrite gtn_eqF//= jE (leq_trans (ltn_ord l))// leq_addr.
- congr (g w i _); apply/val_inj => /=.
  by apply/eqP; rewrite -(eqn_add2l n1) -lE -jE.
Qed.

Global Instance is_derive_row_mx f A g B x v :
  is_derive x v f A -> is_derive x v g B ->
  is_derive x v (fun t => row_mx (f t) (g t)) (row_mx A B).
Proof.
move=> [dfx fA] [dgx gB]; apply: DeriveDef; first exact: derivable_row_mx.
by rewrite derive_row_mx// fA gB.
Qed.

End derivable_derive_row_mx.

Lemma eqo_row_mx (K : realFieldType) {m n1 n2 : nat} (F : filter_on K)
  (A1 : K -> 'M[K]_(m, n1)) (A2 : K -> 'M[K]_(m, n2)) (f : K -> K) :
  (fun t => row_mx ([o_F f of A1] t) ([o_F f of A2] t)) =o_F f.
Proof.
apply/eqoP => _/posnumP[e]; near=> x; rewrite norm_row_mx ge_max.
by apply/andP; split; near: x; apply: littleoP.
Unshelve. all: by end_near. Qed.

Section is_diff_row_mx.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {n1 n2 : nat}.
Implicit Types (M dM : R -> 'rV[R]_n1) (N dN : R -> 'rV[R]_n2) (x t : R).

Fact drow_mx M N x (f : R -> R) : differentiable M x -> differentiable N x ->
  continuous (fun y => row_mx ('d M x y) ('d N x y)) /\
  (fun y => row_mx (M y) (N y)) \o shift x = cst (row_mx (M x) (N x)) +
  (fun y => row_mx ('d M x y) ('d N x y)) +o_ 0 id.
Proof.
move=> df dg; split=> [/= ?|].
  by apply: cvg_row_mx => //=; exact: diff_continuous.
apply/eqaddoE; rewrite funeqE => y /=.
rewrite ![_ (_ + x)]diff_locallyx//.
have ->/= : forall h e, row_mx (M x + 'd M x y + [o_ 0 id of h] y)
  (N x + 'd N x y + [o_ 0 id of e] y) =
  row_mx (M x) (N x) + row_mx ('d M x y) ('d N x y) +
  row_mx ([o_ 0 id of h] y) ([o_ 0 id of e] y).
  by move=> /= h e; rewrite !add_row_mx.
congr (_ + _).
by rewrite -[LHS]/((fun y => row_mx (_ y) (_ y)) y) eqo_row_mx.
Qed.

Lemma diff_row_mx M N x : differentiable M x -> differentiable N x ->
  'd (fun y => row_mx (M y) (N y)) x =
  (fun y => row_mx ('d M x y) ('d N x y)) :> (R -> 'rV[R]_(n1 + n2)).
Proof.
move=> df dg.
pose d y := row_mx ('d M x y) ('d N x y).
have lin_row_mx : linear d.
  by move=> /= a b c; rewrite /d 2!linearPZ scale_row_mx add_row_mx.
pose row_mxlM := GRing.isLinear.Build _ _ _ _ _ lin_row_mx.
pose row_mxL : {linear _ -> _} := HB.pack d row_mxlM.
rewrite -/d -[d]/(row_mxL : _ -> _).
by apply: diff_unique; have [] := drow_mx id df dg.
Qed.

Lemma differentiable_row_mx M N x : differentiable M x -> differentiable N x ->
  differentiable (fun t => row_mx (M t) (N t)) x.
Proof.
by move=> df dg; apply/diff_locallyP; rewrite diff_row_mx //; apply: drow_mx.
Qed.

Global Instance is_diff_row_mx M dM N dN x :
  is_diff x M dM -> is_diff x N dN ->
  is_diff x (fun t => row_mx (M t) (N t)) (fun t => row_mx (dM t) (dN t)).
Proof.
move=> dfx dgx; apply: DiffDef; first exact: differentiable_row_mx.
by rewrite diff_row_mx// !diff_val.
Qed.

End is_diff_row_mx.
