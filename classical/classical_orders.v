From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From HB Require Import structures.
From mathcomp Require Import functions set_interval.

(**md**************************************************************************)
(* # classical orders                                                         *)
(*                                                                            *)
(* This file provides some additional order theory that requires stronger     *)
(* axioms than mathcomp's own orders expect.                                  *)
(* ```                                                                        *)
(*     same_prefix n == two elements in a product space agree up n            *)
(*    first_diff x y == the first occurrence where x n != y n, or None        *)
(*       big_lexi_le == the (countably) infinite lexicographical ordering     *)
(*    big_lexi_order == an alias for attaching this order type                *)
(*  start_with n x y == x for the first n values, then switches to y          *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Definition big_lexi_order {I : Type} (T : I -> Type) : Type := forall i, T i.
HB.instance Definition _ (I : Type) (K : I -> choiceType) :=
  Choice.on (big_lexi_order K).

Section big_lexi_le.
Context {K : nat -> eqType}.

Definition same_prefix n (t1 t2 : forall n, K n) :=
  forall m, (m < n)%O -> t1 m = t2 m.

Lemma same_prefix0 t1 t2 : same_prefix 0 t1 t2. Proof. by []. Qed.
Hint Resolve same_prefix0 : core.

Lemma same_prefix_sym n t1 t2 : same_prefix n t1 t2 <-> same_prefix n t2 t1.
Proof. by rewrite /same_prefix; split => + m mn => /(_ m mn). Qed.

Lemma same_prefix_leq n m t1 t2 :
  n <= m -> same_prefix m t1 t2 -> same_prefix n t1 t2.
Proof.
move=> nm + r rn; apply.
by move: nm; rewrite leq_eqVlt => /predU1P[<-//|]; exact: ltn_trans.
Qed.

Lemma same_prefix_refl n x : same_prefix n x x. Proof. by []. Qed.

Lemma same_prefix_trans n x y z :
  same_prefix n x y ->
  same_prefix n y z ->
  same_prefix n x z.
Proof. by move=> + + m mn => /(_ _ mn) ->; exact. Qed.

Definition first_diff (t1 t2 : forall n, K n) : option nat :=
  xget None (Some @` [set n | same_prefix n t1 t2 /\ t1 n != t2 n]).

Lemma first_diff_sym t1 t2 : first_diff t1 t2 = first_diff t2 t1.
Proof.
rewrite /first_diff /=; congr (xget _ (image _ _)).
under eq_set do rewrite eq_sym.
by apply/seteqP; split => z/= [] /same_prefix_sym.
Qed.

Lemma first_diff_unique (x y : forall n, K n) n m :
  same_prefix n x y -> x n != y n ->
  same_prefix m x y -> x m != y m ->
  n = m.
Proof.
move=> nfx xyn mfx xym; apply/eqP; rewrite eq_le 2!leNgt; apply/andP; split.
by apply/negP => /nfx; exact/eqP.
by apply/negP => /mfx; exact/eqP.
Qed.

Lemma first_diff_SomeP x y n :
  first_diff x y = Some n <-> same_prefix n x y /\ x n != y n.
Proof.
split => [|[pfx xNy]]; rewrite /first_diff.
  by case: xgetP=> //= -[m ->|//] [p + <-[]] => /[swap] ->.
case: xgetP => /=; last by move=> /(_ (Some n))/forall2NP/(_ n)[/not_andP[]|].
by move=> [m|? []//] -> [p [pxy xyp]] <-; rewrite (@first_diff_unique x y n p).
Qed.

Lemma first_diff_NoneP t1 t2 : t1 = t2 <-> first_diff t1 t2 = None.
Proof.
rewrite /first_diff; split => [->|].
  by case: xgetP => //= -[n|//] -> [m []]; rewrite eqxx.
case: xgetP => [? -> [i /=] [?] ? <-//|/= R _].
apply/functional_extensionality_dep.
suff : forall n x, x < n -> t1 x = t2 x by move=> + n => /(_ n.+1)/(_ n); exact.
elim => [//|n ih x]; rewrite ltnS leq_eqVlt => /predU1P[->|xn]; last exact: ih.
by have /forall2NP/(_ n)[/not_andP[//|/negP/negPn/eqP]|] := R (Some n).
Qed.

Lemma first_diff_lt a x y n m :
  n < m ->
  first_diff a x = Some n ->
  first_diff a y = Some m ->
  first_diff x y = Some n.
Proof.
move=> nm /first_diff_SomeP [xpfx xE] /first_diff_SomeP [ypfx yE].
apply/first_diff_SomeP; split; last by rewrite -(ypfx _ nm) eq_sym.
by move=> o /[dup] on /xpfx <-; exact/ypfx/(ltn_trans on).
Qed.
Arguments first_diff_lt a {x y n m}.

Lemma first_diff_eq a x y n m :
  first_diff a x = Some n ->
  first_diff a y = Some n ->
  first_diff x y = Some m ->
  n <= m.
Proof.
case/first_diff_SomeP => axPfx axn /first_diff_SomeP[ayPfx ayn].
case/first_diff_SomeP => xyPfx; apply: contraNleq => mn.
by rewrite -(ayPfx _ mn) -(axPfx _ mn).
Qed.

Lemma first_diff_dfwith (x : forall n : nat, K n) i b :
  x i != b <-> first_diff x (dfwith x i b) = Some i.
Proof.
split => [xBn|/first_diff_SomeP[_]]; last by rewrite dfwithin.
apply/first_diff_SomeP; split; last by rewrite dfwithin.
by move=> n ni; rewrite dfwithout// gt_eqF.
Qed.

Definition big_lexi_le
    (R : forall n, K n -> K n -> bool) (t1 t2 : forall n, K n) :=
  if first_diff t1 t2 is Some n then R n (t1 n) (t2 n) else true.

Lemma big_lexi_le_reflexive R : reflexive (big_lexi_le R).
Proof.
move=> x; rewrite /big_lexi_le /= /first_diff.
by case: xgetP => //= -[n _|//] [m []]; rewrite eqxx.
Qed.

Lemma big_lexi_le_anti R : (forall n, antisymmetric (R n)) ->
  antisymmetric (big_lexi_le R).
Proof.
move=> antiR x y /andP[xy yx]; apply/first_diff_NoneP; move: xy yx.
rewrite /big_lexi_le first_diff_sym.
case E : (first_diff y x) => [n|]// Rxy Ryx.
case/first_diff_SomeP : E => _.
by apply: contra_neqP => _; apply/antiR; rewrite Ryx.
Qed.

Lemma big_lexi_le_trans R :
  (forall n, transitive (R n)) ->
  (forall n, antisymmetric (R n)) ->
  transitive (big_lexi_le R).
Proof.
move=> Rtrans Ranti y x z; rewrite /big_lexi_le /=.
case Ep : (first_diff x y) => [p|]; last by move/first_diff_NoneP : Ep ->.
case Er : (first_diff x z) => [r|]; last by move/first_diff_NoneP : Er ->.
case Eq : (first_diff y z) => [q|]; first last.
  by move: Ep Er; move/first_diff_NoneP: Eq => -> -> [->].
have [pq|qp|pqE]:= ltgtP p q.
- move: Er.
  rewrite (first_diff_lt y pq)// 1?first_diff_sym// => -[<-] ? _.
  by case/first_diff_SomeP : Eq => /(_ _ pq) <-.
- move: Er.
  rewrite first_diff_sym (first_diff_lt y qp)// 1?first_diff_sym// => -[<-] _ ?.
  by case/first_diff_SomeP: Ep => /(_ _ qp) ->.
- move: Ep Eq; rewrite pqE => Eqx Eqz.
  rewrite first_diff_sym in Eqx; have := first_diff_eq Eqx Eqz Er.
  rewrite leq_eqVlt => /predU1P[->|qr]; first exact: Rtrans.
  case/first_diff_SomeP : Er => /(_ _ qr) -> _ qzy qyz.
  case/first_diff_SomeP : Eqz => _; apply: contra_neqP => _.
  by apply/Ranti/andP; split.
Qed.

Lemma big_lexi_le_total R : (forall n, total (R n)) -> total (big_lexi_le R).
Proof.
move=> Rtotal x y.
case E : (first_diff x y) => [n|]; first last.
  by move/first_diff_NoneP : E ->; rewrite big_lexi_le_reflexive.
by rewrite /big_lexi_le E first_diff_sym E; exact: Rtotal.
Qed.

Definition start_with n (t1 t2 : forall n, K n) (i : nat) : K i :=
  if (i < n)%O then t1 i else t2 i.

Lemma start_with_prefix n x y : same_prefix n x (start_with n x y).
Proof. by move=> r rn; rewrite /start_with rn. Qed.

End big_lexi_le.

Section big_lexi_porder.
Context {d} {K : nat -> porderType d}.

Let Rn n (k1 k2 : K n) := (k1 <= k2)%O.

Local Lemma big_lexi_ord_reflexive : reflexive (big_lexi_le Rn).
Proof. exact: big_lexi_le_reflexive. Qed.

Local Lemma big_lexi_ord_anti : antisymmetric (big_lexi_le Rn).
Proof. by apply: big_lexi_le_anti => n; exact: le_anti. Qed.

Local Lemma big_lexi_ord_trans : transitive (big_lexi_le Rn).
Proof. by apply: big_lexi_le_trans => n; [exact: le_trans|exact: le_anti]. Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build d (big_lexi_order K)
  big_lexi_ord_reflexive big_lexi_ord_anti big_lexi_ord_trans.

Lemma leEbig_lexi_order (a b : big_lexi_order K) :
  (a <= b)%O = if first_diff a b is Some n then (a n <= b n)%O else true.

Proof. by []. Qed.

End big_lexi_porder.

Section big_lexi_total.
Context {d} {K : nat -> orderType d}.

Local Lemma big_lexi_ord_total : total (@Order.le _ (big_lexi_order K)).
Proof. by apply: big_lexi_le_total => ?; exact: le_total. Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build _
  (big_lexi_order K) big_lexi_ord_total.

End big_lexi_total.

Section big_lexi_bottom.
Context {d} {K : nat -> bPOrderType d}.

Let b : big_lexi_order K := (fun=> \bot)%O.
Local Lemma big_lex_bot (x : big_lexi_order K) : (b <= x)%O.
Proof.
by rewrite leEbig_lexi_order; case: first_diff => // ?; exact: Order.le0x.
Qed.

HB.instance Definition _ := @Order.hasBottom.Build _
  (big_lexi_order K) b big_lex_bot.

End big_lexi_bottom.

Section big_lexi_top.
Context {d} {K : nat -> tPOrderType d}.

Let t : big_lexi_order K := (fun=> \top)%O.
Local Lemma big_lex_top (x : big_lexi_order K) : (x <= t)%O.
Proof.
by rewrite leEbig_lexi_order; case: first_diff => // ?; exact: Order.lex1.
Qed.

HB.instance Definition _ := @Order.hasTop.Build _
  (big_lexi_order K) t big_lex_top.

End big_lexi_top.

Section big_lexi_intervals.
Context {d} {K : nat -> orderType d}.

Lemma big_lexi_order_prefix_lt (b a x: big_lexi_order K) n :
  (a < b)%O ->
  first_diff a b = Some n ->
  same_prefix n.+1 x b ->
  (a < x)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP[pfa abN].
case E1 : (first_diff a x) => [m|]; first last.
  by move/first_diff_NoneP : E1 <- => _/(_ n (ltnSn _))/eqP/negPn; rewrite abN.
move=> ab pfx; rewrite lt_neqAle; apply/andP; split.
  by apply/eqP => /first_diff_NoneP; rewrite E1.
move: ab; rewrite lt_neqAle => /andP[ba].
rewrite 2!leEbig_lexi_order E1 abD.
suff : n = m by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ a x) => //=; [| |by case/first_diff_SomeP : E1..].
- by apply/(same_prefix_trans pfa)/same_prefix_sym; exact: same_prefix_leq.
- by rewrite (pfx n (ltnSn _)).
Qed.

Lemma big_lexi_order_prefix_gt (b a x : big_lexi_order K) n :
  (b < a)%O ->
  first_diff a b = Some n ->
  same_prefix n.+1 x b ->
  (x < a)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP[pfa /eqP abN].
case E1 : (first_diff x a) => [m|]; first last.
  by move/first_diff_NoneP : E1 -> => _ /(_ n (ltnSn _)).
move=> ab pfx; rewrite lt_neqAle; apply/andP; split.
  by apply/negP => /eqP/first_diff_NoneP; rewrite E1.
move: ab; rewrite lt_neqAle => /andP[ba].
rewrite 2!leEbig_lexi_order (@first_diff_sym _ b a) E1 abD.
suff : n = m by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ x a) => //=; [| |by case/first_diff_SomeP : E1..].
- apply/same_prefix_sym/(same_prefix_trans pfa)/same_prefix_sym.
  exact: same_prefix_leq.
- by rewrite (pfx n (ltnSn _)) eq_sym; exact/eqP.
Qed.

Lemma big_lexi_order_between (a x b : big_lexi_order K) n :
  (a <= x <= b)%O ->
  same_prefix n a b ->
  same_prefix n x a.
Proof.
move=> axb; elim: n => // n IH pfxSn m mSn.
have pfxA : same_prefix n a x.
  exact/same_prefix_sym/IH/(same_prefix_leq _  pfxSn).
have pfxB : same_prefix n x b.
  apply: (@same_prefix_trans _ n x a b); first exact/same_prefix_sym.
  exact: (same_prefix_leq _  pfxSn).
move: mSn; rewrite ltEnat/= ltnS leq_eqVlt => /predU1P[->|]; first last.
  by move: pfxA; rewrite same_prefix_sym; exact.
apply: le_anti; apply/andP; split.
  case/andP: axb => ? +; rewrite leEbig_lexi_order (pfxSn n (ltnSn _)).
  case E : (first_diff x b) => [r|]; last by move/first_diff_NoneP : E ->.
  move=> xrb; have : n <= r.
    rewrite leqNgt; apply/negP=> /[dup] /pfxB xbE.
    by case/first_diff_SomeP : E => _; rewrite xbE eqxx.
  rewrite leq_eqVlt => /predU1P[->//|nr].
  by case/first_diff_SomeP : E => /(_ n nr) ->.
case/andP : axb => + ?; rewrite leEbig_lexi_order.
case E : (first_diff a x) => [r|]; last by move/first_diff_NoneP : E => <-.
move=> xrb.
have : n <= r.
  rewrite leqNgt; apply/negP => /[dup] /pfxA xbE.
  by case/first_diff_SomeP : E => _; rewrite xbE eqxx.
rewrite leq_eqVlt => /predU1P[->//|nr].
by case/first_diff_SomeP : E => /(_ n nr) ->.
Qed.

Lemma big_lexi_order_interval_prefix (i : interval (big_lexi_order K))
    (x : big_lexi_order K) :
  itv_open_ends i -> x \in i ->
  exists n, same_prefix n x `<=` [set` i].
Proof.
move: i; case=> [][[]l|[]] [[]r|[]] /orP []// ?; rewrite ?in_itv /= ?andbT.
- move=> /andP[lx xr].
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP : E1 ->; rewrite bnd_simp.
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP : E2 ->; rewrite bnd_simp.
  exists (Order.max n m).+1 => p xppfx; rewrite set_itvE.
  apply/andP; split.
    apply: (big_lexi_order_prefix_lt lx E1) => w wm; apply/esym/xppfx.
    by move/ltnSE/leq_ltn_trans : wm; apply; rewrite ltnS leq_max leqnn orbT.
  rewrite first_diff_sym in E2.
  apply: (big_lexi_order_prefix_gt xr E2) => w wm; apply/esym/xppfx.
  by move/ltnSE/leq_ltn_trans : wm; apply; rewrite ltnS leq_max leqnn.
- move=> lx.
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP : E1 ->; rewrite bnd_simp.
  exists m.+1 => p xppfx; rewrite set_itvE /=.
  by apply: (big_lexi_order_prefix_lt lx E1) => w wm; exact/esym/xppfx.
- move=> xr.
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP : E2 ->; rewrite bnd_simp.
  exists n.+1; rewrite first_diff_sym in E2 => p xppfx.
  rewrite set_itvE /=.
  by apply: (big_lexi_order_prefix_gt xr E2) => w wm; exact/esym/xppfx.
by move=> _; exists 0 => ? ?; rewrite set_itvE.
Qed.

End big_lexi_intervals.

Lemma big_lexi_order_prefix_closed_itv {d} {K : nat -> tbOrderType d} n
  (x : big_lexi_order K) :
  same_prefix n x = `[
    (@start_with K n x (fun=>\bot):big_lexi_order K)%O,
    (start_with n x (fun=>\top))%O].
Proof.
rewrite eqEsubset; split=> [z pfxz|z]; first last.
  rewrite set_itvE /= => xbt; apply: same_prefix_trans.
    exact: (start_with_prefix _ (fun=> \bot)%O).
  apply/same_prefix_sym/(big_lexi_order_between xbt).
  apply: same_prefix_trans (start_with_prefix _ _).
  exact/same_prefix_sym/start_with_prefix.
rewrite set_itvE /= !leEbig_lexi_order; apply/andP; split;
  case E : (first_diff _ _) => [m|] //; rewrite /start_with /=.
- by case: ifPn => [/pfxz -> //|]; rewrite le0x.
- by case: ifPn => [/pfxz -> //|]; rewrite lex1.
Qed.
