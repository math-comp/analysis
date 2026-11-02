(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions wochoice.
From mathcomp Require Import cardinality fsbigop set_interval filter reals.
From mathcomp Require Import topology_structure uniform_structure
  pseudometric_structure.

(**md**************************************************************************)
(* # Metrizability for uniform spaces                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*  countable_uniform.type == endows a pseudoMetric on a uniform type whose   *)
(*                            entourage has a countable basis                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* This section proves that uniform spaces, with a countable base for their
   entourage, are metrizable. The definition of this metric is rather arcane,
   and the proof is tough. That's ok because the resulting metric is not
   intended to be used explicitly. Instead, this is typically used in
   applications that do not depend on the metric:
   - `metric spaces are T4`
   - `in metric spaces, compactness and sequential compactness agree`
   - infinite products of metric spaces are metrizable
*)
Module countable_uniform.
Section countable_uniform.
Local Open Scope relation_scope.
Context {R : realType} {T : uniformType}.

Hypothesis cnt_unif : @countable_uniformity T.

Let f_ := projT1 (cid2 (iffLR countable_uniformityP cnt_unif)).

Local Lemma countableBase : forall A, entourage A -> exists N, f_ N `<=` A.
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

Let entF : forall n, entourage (f_ n).
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

(* Step 1:
   We build a nicer base `g` for `entourage` with better assumptions than `f`
   - each (g_ n) is symmetric
   - the sets (g_ n) are nested downward
   - g_ n.+1 \o g_ n.+1 \o g_ n.+1 `<=` g_ n says the sets descend `quickly`
 *)

Local Fixpoint g_ n : set (T * T) :=
  if n is n.+1 then let W := split_ent (split_ent (g_ n)) `&` f_ n in W `&` W^-1
  else [set: T*T].

Let entG n : entourage (g_ n).
Proof.
elim: n => /=; first exact: entourageT.
by move=> n entg; apply/entourage_invI; exact: filterI.
Qed.

Local Lemma symG n : (g_ n)^-1 = g_ n.
Proof.
by case: n => // n; rewrite eqEsubset; split; case=> ? ?; rewrite /= andC.
Qed.

Local Lemma descendG1 n : g_ n.+1 `<=` g_ n.
Proof.
apply: subIset; left; apply: subIset; left; apply: subset_trans.
  by apply: split_ent_subset; exact: entourage_split_ent.
by apply: subset_trans; last exact: split_ent_subset.
Qed.

Local Lemma descendG n m : (m <= n)%N -> g_ n `<=` g_ m.
Proof.
elim: n; rewrite ?leqn0; first by move=>/eqP ->.
move=> n IH; rewrite leq_eqVlt ltnS => /orP [/eqP <- //|] /IH.
by apply: subset_trans; exact: descendG1.
Qed.

Local Lemma splitG3 n : g_ n.+1 \; g_ n.+1 \; g_ n.+1 `<=` g_ n.
Proof.
suff g2split : g_ n.+1 \; g_ n.+1 `<=` split_ent (g_ n).
  apply: subset_trans; last exact: subset_split_ent (entG n).
  apply: set_compose_subset (g2split); rewrite -[_ n.+1]set_compose_diag.
  apply: subset_trans g2split; apply: set_compose_subset => //.
  by move=> [_ _] [z _] [<- <-]; exact: entourage_refl.
apply: subset_trans; last exact: subset_split_ent.
by apply: set_compose_subset; apply: subIset; left; apply: subIset; left.
Qed.

Local Lemma gsubf n : g_ n.+1 `<=` f_ n.
Proof. by apply: subIset; left; apply: subIset; right. Qed.

Local Lemma countableBaseG A : entourage A -> exists N, g_ N `<=` A.
Proof.
move=> /countableBase [N] fnA; exists N.+1.
by apply: subset_trans fnA; exact: gsubf.
Qed.

(* Step 2.
   We build a sensible notion of balls for our metric.
   The naive attempt,
                     `ball x e y := g_ (distN e) (x,y))
   doesn't respect triangle inequality. We need to cook triangle inequality
   into the balls themselves. So we define balls in terms of steps:
      `ball x e y := there are n steps x_0 = x,...,x_i,..., x_n.+1 = y and
                     e_1,...,e_n such that
                           g_ (distN e_i) (x_i,x_i+1)
                                    and
                               sum (e_i) = e
*)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Definition distN (e : R) : nat := Num.truncn e^-1.

Local Lemma distN0 : distN 0 = 0%N.
Proof. by rewrite /distN invr0 truncn0. Qed.

Local Lemma distN_nat (n : nat) : distN n%:R^-1 = n.
Proof.
by rewrite /distN invrK; apply/eqP; rewrite -(@eqr_nat R) -natrEtruncn.
Qed.

Local Lemma distN_le e1 e2 : e1 > 0 -> e1 <= e2 -> (distN e2 <= distN e1)%N.
Proof.
move=> e1pos e1e2; rewrite /distN le_truncn// lef_pV2// posrE.
by rewrite (lt_le_trans e1pos).
Qed.

Local Fixpoint n_step_ball n x e z :=
  if n is n.+1 then exists y d1 d2,
    [/\ n_step_ball n x d1 y,
        0 < d1,
        0 < d2,
        g_ (distN d2) (y, z) &
        d1 + d2 = e]
  else e > 0 /\ g_ (distN e) (x, z).

Local Definition step_ball x e z := exists i, (n_step_ball i x e z).

Local Lemma n_step_ball_pos n x e z : n_step_ball n x e z -> 0 < e.
Proof.
by case: n => [[]|] // n; case=> [?] [?] [?] [] ? ? ? ? <-; exact: addr_gt0.
Qed.

Local Lemma step_ball_pos x e z : step_ball x e z -> 0 < e.
Proof. by case => ?; exact: n_step_ball_pos. Qed.

Local Lemma entourage_nball e :
  0 < e -> entourage [set xy | step_ball xy.1 e xy.2].
Proof.
move=> epos; apply: (@filterS _ _ _ (g_ (distN e))) => // [[x y]] ?.
by exists 0%N.
Qed.

Local Lemma n_step_ball_center x e : 0 < e -> n_step_ball 0 x e x.
Proof. by move=> epos; split => //; exact: entourage_refl. Qed.

Local Lemma step_ball_center x e : 0 < e -> step_ball x e x.
Proof. by move=> epos; exists 0%N; apply: n_step_ball_center. Qed.

Local Lemma n_step_ball_triangle n m x y z d1 d2 :
  n_step_ball n x d1 y ->
  n_step_ball m y d2 z ->
  n_step_ball (n + m).+1 x (d1 + d2) z.
Proof.
move: n z d2; elim: m => [n z d2 Nxy [? ?]|n IH m z d2 Oxy].
  by exists y, d1, d2; split; rewrite ?addn0 // (n_step_ball_pos Nxy).
move=> [w] [e1] [e2] [Oyw ? ? ? <-].
exists w, (d1 + e1), e2; rewrite addnS addrA.
split => //; last by rewrite addr_gt0//; exact: n_step_ball_pos Oxy.
by case: (IH m w e1 Oxy Oyw) => t [e3] [e4] [] Oxt ? ? ? <-; exists t, e3, e4.
Qed.

Local Lemma step_ball_triangle x y z d1 d2 :
  step_ball x d1 y -> step_ball y d2 z -> step_ball x (d1 + d2) z.
Proof.
move=> [n Oxy] [m Oyz]; exists (n + m).+1.
exact: n_step_ball_triangle Oxy Oyz.
Qed.

Local Lemma n_step_ball_sym n x y e :
  n_step_ball n x e y -> n_step_ball n y e x.
Proof.
move: x y e; elim: n; first by move=> ? ? ?; rewrite /= -{1}symG.
move=> n IH x y e [t] [d1] [d2] [] /IH Oty ? ?.
rewrite addrC -symG -[n]add0n => gty <-; apply: (n_step_ball_triangle _ Oty).
by split => //; exact: gty.
Qed.

Local Lemma step_ball_sym x y e : step_ball x e y -> step_ball y e x.
Proof. by case=> n /n_step_ball_sym ?; exists n. Qed.

(* Step 3:
   We prove that step_ball respects the original entourage. This requires an
   induction on the length of the steps, which is pretty tricky. The central
   lemma is `split_n_step_ball`, which lets us break a list into parts three
   parts as: half + one_step + half. Then our we can break apart our n +1 path

                         nlong + one_step
   into
                  (half + one_step + half) + one_step
                                =
                  half + one_step + (half + one_step)

   and we can we can use our (strong) induction hypothesis.
   And lastly we finish with splitG3.
*)

Local Lemma n_step_ball_le n x e1 e2 :
  e1 <= e2 -> n_step_ball n x e1 `<=` n_step_ball n x e2.
Proof.
move: x e1 e2; elim: n.
  move=> x e1 e2 e1e2 y [?] gxy; split; first exact: (lt_le_trans _ e1e2).
  by apply: descendG; last (exact: gxy); exact: distN_le.
move=> n IH x e1 e2 e1e2 z [y] [d1] [d2] [] /IH P d1pos d2pos gyz d1d2e1.
exists y, (e2 - d2), d2; split => //.
- by apply: P; rewrite lerBrDr d1d2e1.
- by apply: lt_le_trans d1pos _; rewrite lerBrDr d1d2e1.
- by rewrite subrK.
Qed.

Local Lemma step_ball_le x e1 e2 :
  e1 <= e2 -> step_ball x e1 `<=` step_ball x e2.
Proof. by move=> e1e2 ? [n P]; exists n; exact: (n_step_ball_le e1e2). Qed.

Local Lemma distN_half (n : nat) : n.+1%:R^-1 / (2:R) <= n.+2%:R^-1.
Proof.
rewrite -invrM //; [exact: unitf_gt0 |exact: unitf_gt0|].
rewrite lef_pV2 ?posrE // -?natrM ?ler_nat -addn1 -addn1 -addnA mulnDr.
by rewrite muln1 leq_add2r leq_pmull.
Qed.

Local Lemma split_n_step_ball n x e1 e2 z :
  0 < e1 -> 0 < e2 -> n_step_ball n.+1 x (e1 + e2) z ->
    exists t1 t2 a b,
    [/\
      n_step_ball a x e1 t1,
      n_step_ball 0 t1 (e1 + e2) t2,
      n_step_ball b t2 e2 z &
      (a + b = n)%N
    ].
Proof.
move: e1 e2 x z; elim: n.
  move=> e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Oxy ? ? gd2yz deE.
  case: (pselect (e1 <= d1)).
    move=> e1d1; exists x, y, 0%N, 0%N; split.
    - exact: n_step_ball_center.
    - apply: n_step_ball_le; last exact: Oxy.
      by rewrite -deE lerDl; apply: ltW.
    - by apply: (@n_step_ball_le _ _ d2); rewrite // -(lerD2l e1) -deE lerD.
    - by rewrite addn0.
  move=> /negP; rewrite -ltNge//.
  move=> e1d1; exists y, z, 0%N, 0%N; split.
  - by apply: n_step_ball_le; last (exact: Oxy); exact: ltW.
  - by apply: (@n_step_ball_le _ _ d2); rewrite // -deE lerDr ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
move=> n IH e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Od1xy d1pos d2pos gd2yz deE.
case: (pselect (e2 <= d2)).
  move=> e2d2; exists y, z, n.+1, 0%N; split.
  - by apply: (@n_step_ball_le _ _ d1); rewrite // -(lerD2r e2) -deE lerD.
  - by apply: (@n_step_ball_le _ _ d2); rewrite // -deE lerDr; exact: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
have d1E' : d1 = e1 + (e2 - d2) by rewrite addrA -deE addrK.
move=> /negP; rewrite -ltNge// => d2lee2.
  case: (IH e1 (e2 - d2) x y); rewrite ?subr_gt0 // -d1E' //.
  move=> t1 [t2] [c1] [c2] [] Oxy1 gt1t2 t2y <-.
  exists t1, t2, c1, c2.+1; split => //.
  - by apply: (@n_step_ball_le _ _ d1); rewrite -?deE // ?lerDl; exact: ltW.
  - by exists y, (e2 - d2), d2; rewrite // ?subr_gt0// subrK.
  - by rewrite addnS.
Qed.

Local Lemma n_step_ball_le_g x n :
  n_step_ball 0 x n%:R^-1 `<=` [set y | g_ n (x,y)].
Proof. by move=> y [] ?; rewrite distN_nat. Qed.

Local Lemma subset_n_step_ball n x N :
  n_step_ball n x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof.
move: N x; elim: n {-2}n (leqnn n) => n.
  rewrite leqn0 => /eqP -> N x; apply: subset_trans.
    exact: n_step_ball_le_g.
  by move=> y ?; exact: descendG.
move=> IH1 + + N x1 x4; case.
  by move=> ? [?] P; apply: descendG _ P; rewrite distN_nat.
move=> l ln1 Ox1x4.
case: (@split_n_step_ball l x1 (N.+1%:R^-1/2) (N.+1%:R^-1/2) x4) => //.
  by rewrite -splitr.
move=> x2 [x3] [l1] [l2] [] P1 [? +] P3 l1l2; rewrite -splitr distN_nat => ?.
have l1n : (l1 <= n)%N by rewrite (leq_trans (leq_addr l2 l1))// l1l2 -ltnS.
have l2n : (l2 <= n)%N by rewrite (leq_trans (leq_addl l1 l2))// l1l2 -ltnS.
apply: splitG3; exists x3; [exists x2 => //|].
  by move/(n_step_ball_le (distN_half N))/(IH1 _ l1n) : P1.
by move/(n_step_ball_le (distN_half N))/(IH1 _ l2n) : P3.
Qed.

Local Lemma subset_step_ball x N :
  step_ball x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof. by move=> y [] n; exact: subset_n_step_ball. Qed.

Local Lemma step_ball_entourage : entourage = entourage_ step_ball.
Proof.
rewrite predeqE => E; split; first last.
  by case=> e /= epos esubE; apply: (filterS esubE); exact: entourage_nball.
move=> entE; case: (countableBase entE) => N fN.
exists N.+2%:R^-1; first by rewrite /= invr_gt0.
apply: (subset_trans _ fN); apply: subset_trans; last apply: gsubf.
by case=> x y /= N1ball; apply: (@subset_step_ball x N.+1).
Qed.

Definition type : Type := let _ := countableBase in let _ := entF in T.

#[export] HB.instance Definition _ := Uniform.on type.
#[export] HB.instance Definition _ := Uniform_isPseudoMetric.Build R type
  step_ball_center step_ball_sym step_ball_triangle step_ball_entourage.
#[export] HB.instance Definition _ {q : Pointed T} :=
  Pointed.copy type (Pointed.Pack q).

Lemma countable_uniform_bounded (x y : T) : @ball _ type x 2 y.
Proof.
rewrite /ball; exists O%N; rewrite /n_step_ball; split; rewrite // /distN.
rewrite (_ : Num.truncn _ = 0)//.
by apply/eqP; rewrite truncn_eq// invr_ge0// ler0n/= invf_lt1// ltr1n.
Qed.

End countable_uniform.

Module Exports. HB.reexport. End Exports.
End countable_uniform.
Export countable_uniform.Exports.

Notation countable_uniform := countable_uniform.type.
