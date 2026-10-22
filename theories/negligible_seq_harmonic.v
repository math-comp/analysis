(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import topology normedtype landau.
From mathcomp Require Import negligible_seq.

(**md**************************************************************************)
(* # Negligible sequences and the harmonic metric                             *)
(*                                                                            *)
(* The index of a sequence is read as a point of the one-point                *)
(* compactification of the natural numbers, with None the point at infinity.  *)
(* At exponent c the index n has the coordinate n ^- c and the point at       *)
(* infinity the coordinate 0; the distance of two points is the distance of   *)
(* their coordinates. A sequence is negligible iff its extension by 0 at      *)
(* infinity is Lipschitz at infinity for every exponent, and iff it is        *)
(* Lipschitz for every positive exponent. Both conditions exclude Some 0.     *)
(*                                                                            *)
(* The distance is a pseudometric only: for c > 0, index 0 has coordinate     *)
(* 0 ^- c = 0 of the point at infinity, and at c = 0 every index has the      *)
(* coordinate 1. The Lipschitz conditions therefore exclude the index 0, and  *)
(* the second characterization ranges over positive exponents.                *)
(*                                                                            *)
(* ```                                                                        *)
(*        harmonic_coord c x == n ^- c if x is Some n, 0 if x is None         *)
(*       harmonic_dist c x y == `|harmonic_coord c x - harmonic_coord c y|    *)
(*            extend_infty u == the extension of u : R ^nat to option nat by  *)
(*                              0 at None                                     *)
(*    lipschitz_at_infty c u == there is L such that `|u n| <= L * n ^- c     *)
(*                              for every positive n                          *)
(*    harmonic_lipschitz c u == extend_infty u is Lipschitz for               *)
(*                              harmonic_dist c on the points other than      *)
(*                              Some 0                                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section harmonic_dist.
Context {R : archiRealFieldType}.
Implicit Types (c : nat) (x y z : option nat) (u : R ^nat).

Definition harmonic_coord c x : R := if x is Some n then n%:R ^- c else 0.

Definition harmonic_dist c x y : R :=
  `|harmonic_coord c x - harmonic_coord c y|.

Lemma harmonic_distxx c x : harmonic_dist c x x = 0.
Proof. by rewrite /harmonic_dist subrr normr0. Qed.

Lemma harmonic_dist_infty c n : harmonic_dist c (Some n) None = n%:R ^- c.
Proof. by rewrite /harmonic_dist /= subr0 ger0_norm // invr_ge0 exprn_ge0. Qed.

Definition extend_infty u x : R := if x is Some n then u n else 0.

End harmonic_dist.

Section lipschitz_at_infty.
Context {R : archiRealFieldType}.
Implicit Types (c d m n : nat) (u : R ^nat).

Let inv_expn_le_base k (a b : R) : 0 < a -> a <= b -> b ^- k <= a ^- k.
Proof.
move=> a_gt0 ab; have b_gt0 := lt_le_trans a_gt0 ab.
by rewrite lef_pV2 ?posrE ?exprn_gt0 // lerXn2r // nnegrE; exact: ltW.
Qed.

Let inv_expn_le_exponent c d n :
  (0 < n)%N -> (c <= d)%N -> n%:R ^- d <= n%:R ^- c :> R.
Proof.
move=> n_gt0 cd.
by rewrite lef_pV2 ?posrE ?exprn_gt0 ?ltr0n // ler_weXn2l // ler1n.
Qed.

(* The extension of u by 0 is Lipschitz at the point at infinity for
   harmonic_dist c, with the index 0 excluded. *)
Definition lipschitz_at_infty c u : Prop :=
  exists L : R, forall n, (0 < n)%N -> `|u n| <= L * n%:R ^- c.

Let lipschitz_const_ge0 c u (L : R) :
  (forall n, (0 < n)%N -> `|u n| <= L * n%:R ^- c) -> 0 <= L.
Proof. by move/(_ 1%N isT); rewrite expr1n invr1 mulr1; exact: le_trans. Qed.

Lemma lipschitz_at_inftyP c u : lipschitz_at_infty c u <->
  exists L : R, forall x, x != Some 0%N ->
    `|extend_infty u x - extend_infty u None| <= L * harmonic_dist c x None.
Proof.
split=> -[L uL]; exists L.
  case=> [[|n]|] //= _; first by rewrite subr0 harmonic_dist_infty; exact: uL.
  by rewrite subrr normr0 harmonic_distxx mulr0.
move=> n n_gt0; have := uL (Some n); rewrite /= subr0 harmonic_dist_infty.
by apply; rewrite -lt0n.
Qed.

Lemma lipschitz_at_infty_le c d u :
  (c <= d)%N -> lipschitz_at_infty d u -> lipschitz_at_infty c u.
Proof.
move=> cd [L uL]; exists L => n n_gt0; apply: le_trans (uL n n_gt0) _.
by rewrite ler_wpM2l ?(lipschitz_const_ge0 uL) ?inv_expn_le_exponent.
Qed.

Lemma negligible_seq_lipschitz_at_inftyP u :
  u \in negligible_seq <-> forall c, lipschitz_at_infty c u.
Proof.
split=> [/set_mem un c|un].
  have [N _ uN] := un c.
  pose M := \big[maxr/0]_(i < N) (`|u i| * i%:R ^+ c).
  exists (maxr 1 M) => n n_gt0.
  have [Nn|nN] := leqP N n.
    apply/ltW/(lt_le_trans (uN n Nn)).
    by rewrite ler_peMl ?invr_ge0 ?exprn_ge0 // le_max lexx.
  rewrite ler_pdivlMr ?exprn_gt0 ?ltr0n // le_max.
  by rewrite (le_bigmax _ _ (Ordinal nN)) orbT.
apply/mem_set => c; have [L uL] := un c.+1.
have L_ge0 := lipschitz_const_ge0 uL; near=> n.
have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
apply: le_lt_trans (uL n n_gt0) _.
rewrite exprS invfM mulrA gtr_pMl ?invr_gt0 ?exprn_gt0 ?ltr0n //.
rewrite ltr_pdivrMr ?ltr0n // mul1r; apply: lt_le_trans (archi_boundP L_ge0) _.
by rewrite ler_nat; near: n; exact: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

(* The extension of u by 0 is Lipschitz for harmonic_dist c on the points
   other than the index 0, whose coordinate is that of the point at
   infinity when c is positive. *)
Definition harmonic_lipschitz c u : Prop :=
  exists L : R, forall x y, x != Some 0%N -> y != Some 0%N ->
    `|extend_infty u x - extend_infty u y| <= L * harmonic_dist c x y.

Lemma harmonic_dist_ge_inv c m n : (0 < c)%N -> (0 < m)%N -> (m < n)%N ->
  m%:R ^- c.+1 <= 2 * harmonic_dist c (Some m) (Some n) :> R.
Proof.
case: c => // c _ m_gt0 mn.
have mR_gt0 : 0 < m%:R :> R by rewrite ltr0n.
have dmn_ge0 : 0 <= m%:R ^- c.+1 - n%:R ^- c.+1 :> R.
  by rewrite subr_ge0 inv_expn_le_base // ler_nat; exact: ltnW.
rewrite /harmonic_dist /= ger0_norm //.
pose a : R := m%:R; pose b : R := m.+1%:R.
have b_gt0 : 0 < b by rewrite ltr0n.
have a_neq0 := lt0r_neq0 mR_gt0; have b_neq0 := lt0r_neq0 b_gt0.
apply: le_trans (_ : _ <= 2 * (a ^- c.+1 - a ^- c / b)) _.
  rewrite 2!exprSr 2!invfM -mulrBr mulrCA -mulrA.
  rewrite ler_pM2l ?invr_gt0 ?exprn_gt0 //.
  have -> : a^-1 - b^-1 = a^-1 / b.
    apply: (mulIf b_neq0); rewrite mulfVK // mulrBl mulVf //.
    by rewrite /b -addn1 natrD mulrDr mulVf // mulr1 addrC addKr.
  rewrite mulrCA ler_pM2l ?invr_gt0 // ler_pdivlMr // mulrC ler_pdivrMr //.
  by rewrite -natrM ler_nat mul2n -addnn -addn1 leq_add2l.
have bn : b <= n%:R by rewrite ler_nat.
rewrite ler_pM2l // lerB // (le_trans (inv_expn_le_base _ b_gt0 bn)) //.
rewrite exprSr invfM ler_pM2r ?invr_gt0 //.
by rewrite inv_expn_le_base // ler_nat.
Qed.

Lemma harmonic_lipschitzW c u :
  harmonic_lipschitz c u -> lipschitz_at_infty c u.
Proof.
by move=> [L uL]; apply/lipschitz_at_inftyP; exists L => x x_neq0; exact: uL.
Qed.

Lemma lipschitz_at_inftyS_harmonic c u :
  (0 < c)%N -> lipschitz_at_infty c.+1 u -> harmonic_lipschitz c u.
Proof.
move=> c_gt0 [L uL]; have L_ge0 := lipschitz_const_ge0 uL.
have uL4 n : (0 < n)%N -> `|u n| <= 4 * L * n%:R ^- c.
  move=> n_gt0; apply: le_trans (uL n n_gt0) _.
  by rewrite ler_pM ?invr_ge0 ?exprn_ge0 ?ler_peMl ?ler1n ?inv_expn_le_exponent.
have uLlt m n : (0 < m)%N -> (m < n)%N ->
    `|u m - u n| <= 4 * L * harmonic_dist c (Some m) (Some n).
  move=> m_gt0 mn; have n_gt0 := ltn_trans m_gt0 mn.
  apply: le_trans (ler_normB _ _) _.
  apply: le_trans (lerD (uL m m_gt0) (uL n n_gt0)) _.
  apply: le_trans (_ : _ <= 2 * L * m%:R ^- c.+1) _.
    rewrite -mulrA mulr2n mulrDl mul1r lerD2l ler_wpM2l //.
    by rewrite inv_expn_le_base ?ltr0n // ler_nat; exact: ltnW.
  have -> : 4 * L = 2 * L * 2 by rewrite mulrAC -natrM.
  rewrite -[_ * 2 * _]mulrA ler_wpM2l ?mulr_ge0 //.
  exact: harmonic_dist_ge_inv.
exists (4 * L) => -[[|m]|] [[|n]|] //= _ _.
- have [mn|nm|->] := ltngtP m n.
  + exact: uLlt.
  + by rewrite distrC /harmonic_dist [X in _ <= 4 * L * X]distrC uLlt.
  + by rewrite subrr normr0 harmonic_distxx mulr0.
- by rewrite subr0 harmonic_dist_infty uL4.
- rewrite sub0r normrN /harmonic_dist /= sub0r normrN.
  rewrite [X in _ <= 4 * L * X]ger0_norm ?invr_ge0 ?exprn_ge0 //.
  exact: uL4.
- by rewrite subrr normr0 harmonic_distxx mulr0.
Qed.

Lemma negligible_seq_harmonic_lipschitzP u :
  u \in negligible_seq <-> forall c, (0 < c)%N -> harmonic_lipschitz c u.
Proof.
apply: iff_trans (negligible_seq_lipschitz_at_inftyP u) _.
split=> uL c; first by move=> c_gt0; exact: lipschitz_at_inftyS_harmonic.
exact: lipschitz_at_infty_le (leqnSn c) (harmonic_lipschitzW (uL c.+1 isT)).
Qed.

End lipschitz_at_infty.
