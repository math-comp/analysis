From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From HB Require Import structures.
From mathcomp Require Import functions set_interval.

(**md**************************************************************************)
(* # classical orders                                                         *)
(*                                                                            *)
(* This file provides some additional order theory that requires stronger     *)
(* axioms than mathcomp's own orders expect                                   *)
(*    share_prefix n == two elements in a product space agree up n            *)
(*    first_diff x y == the first occurrence where x n != y n, or None        *)
(*      lexi_bigprod == the (countably) infinite lexicographical ordering      *)
(*    big_lexi_order == an alias for attack this order type                   *)
(*  start_with n x y == x for the first n values, then switches to y          *)
(*                                                                            *)
(******************************************************************************)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.

Section big_lexi_order.

Context {K : nat -> eqType} .

Definition share_prefix n (t1 t2: forall n, K n) :=
  (forall m, (m < n)%O -> t1 m = t2 m).

Lemma share_prefix0 t1 t2 : share_prefix 0 t1 t2.
Proof. by rewrite /share_prefix. Qed.

Hint Resolve share_prefix0 : core.

Lemma share_prefixC n t1 t2 : share_prefix n t1 t2 <-> share_prefix n t2 t1.
Proof. by rewrite /share_prefix; split => + m mn => /(_ m mn). Qed.

Lemma share_prefixS n m t1 t2 :
  n <= m -> share_prefix m t1 t2 -> share_prefix n t1 t2.
Proof.
move=> nm + r rn; apply; move: nm; rewrite leq_eqVlt => /orP.
by case=>[/eqP <- //|/(ltn_trans rn)]; exact.
Qed.

Lemma share_prefix_refl n x : share_prefix n x x.
Proof. by move=> ? ?. Qed.

Lemma share_prefix_trans n x y z :
  share_prefix n x y ->
  share_prefix n y z ->
  share_prefix n x z.
Proof. by move=> + + m mn => /(_ _ mn) ->; apply. Qed.

Definition first_diff (t1 t2: forall n, K n) : option nat :=
  xget None (Some  @` [set n | share_prefix n t1 t2 /\ t1 n <> t2 n]).

Lemma first_diffC t1 t2 : first_diff t1 t2 = first_diff t2 t1.
Proof.
by rewrite /first_diff /=; congr (_ _ _); rewrite eqEsubset; split => z /=;
  (case => w [wE /nesym NE]; exists w => //; split);
  rewrite // share_prefixC.
Qed.

Lemma first_diff_unique (x y : forall n, K n) : forall (n m : nat),
  (share_prefix n x y /\ x n <> y n) ->
  (share_prefix m x y /\ x m <> y m) ->
  n = m.
Proof.
move=> n m [nPfx xyn] [mPfx xym]; apply/eqP.
apply: contrapT; move/negP; rewrite neq_ltn => /orP; case => RN.
  by move: xyn; have -> := mPfx _ RN.
by move: xym; have -> := nPfx _ RN.
Qed.

Lemma first_diff_SomeP x y n :
  first_diff x y = Some n <-> share_prefix n x y /\ x n <> y n.
Proof.
split.
  rewrite /first_diff; case: xgetP=> // ? -> []? [+ + <-/Some_inj nE].
  by rewrite {}nE /= => ? ?; split.
case=> pfx xNy; rewrite /first_diff; case: xgetP => //=; first last.
  by move/(_ (Some n)); apply: absurd; exists n.
case; last by move => ? [].
by move=> m -> [o] [? ?] <-; congr(_ _); apply: (@first_diff_unique x y).
Qed.

Lemma first_diff_NoneP t1 t2 : t1 = t2 <-> first_diff t1 t2 = None.
Proof.
split; rewrite /first_diff.
  by move=> ->; case: xgetP => //; case => // ? ? [? /=] []//.
case: xgetP; first by move=> ? -> [i /=] [?] ? <-.
move=> /= R _; apply/functional_extensionality_dep.
suff : forall n, forall x, x < n -> t1 x = t2 x.
  by move=> + n => /(_ n.+1)/(_ n); apply.
elim; first by move=> ?.
move=> n IH x; rewrite leq_eqVlt => /orP [/eqP/succn_inj ->|xn]; last exact: IH.
have /forall2NP/(_ n) [] := R (Some n) => // /not_andP.
case; first by case/existsNP=> m /not_implyP [//] mx; apply: absurd; apply/IH.
by move/contrapT ->.
Qed.

Lemma first_diff_lt a x y n m :
  n < m ->
  first_diff a x = Some n ->
  first_diff a y = Some m ->
  first_diff x y = Some n.
Proof.
move=> nm /first_diff_SomeP [xpfx xE] /first_diff_SomeP [ypfx yE].
apply/first_diff_SomeP; split.
  by move=> o /[dup] on /xpfx <-; apply: ypfx; apply: (ltn_trans on).
by have <- := ypfx _ nm; exact/nesym.
Qed.

Lemma first_diff_eq a x y n m :
  first_diff a x = Some n ->
  first_diff a y = Some n ->
  first_diff x y = Some m ->
  n <= m.
Proof.
case/first_diff_SomeP => axPfx axn /first_diff_SomeP [ayPfx ayn].
case/first_diff_SomeP => xyPfx; rewrite leqNgt; apply: contra_notN => mn.
by have <- := ayPfx _ mn; have <- := axPfx _ mn.
Qed.

Lemma first_diff_dfwith x i b :
  (x i) <> b <-> first_diff x (@dfwith _ K x i b) = Some i.
Proof.
split; first last.
  by case/first_diff_SomeP => _ /=; apply: contra_not; rewrite dfwithin.
move=> xNb; apply/first_diff_SomeP; split; last by rewrite dfwithin.
move=> n ni; apply/eqP; rewrite dfwithout //.
by apply/negP => /eqP E; move: ni; rewrite E ltexx.
Qed.

Definition lexi_bigprod (R : forall n, K n -> K n -> bool) (t1 t2 : forall n, K n) :=
  match first_diff t1 t2 with
  | Some n => R n (t1 n) (t2 n)
  | None => true
  end.

Lemma lexi_bigprod_reflexive R : reflexive (lexi_bigprod R).
Proof.
move=> x; rewrite /lexi_bigprod /=.
rewrite /lexi_bigprod/first_diff.
by case: xgetP => //=; case=> // n /= _ [m [/= _]].
Qed.

Lemma lexi_bigprod_anti R : (forall n, antisymmetric (R n)) ->
  antisymmetric (lexi_bigprod R).
Proof.
move=> antiR x y /andP [xy yx]; apply/first_diff_NoneP; move: xy yx.
rewrite /lexi_bigprod first_diffC; case E: (first_diff y x) => [n|]// ? ?.
case/first_diff_SomeP: E => _; apply: contra_notP => _.
by apply: antiR; apply/andP; split.
Qed.

Lemma lexi_bigprod_trans R :
  (forall n, transitive (R n)) ->
  (forall n, antisymmetric (R n)) ->
  transitive (lexi_bigprod R).
move=> Rtrans Ranti y x z; rewrite /lexi_bigprod /=.
case Ep: (first_diff x y) => [p|]; last by move/first_diff_NoneP: Ep ->.
case Er: (first_diff x z) => [r|]; last by move/first_diff_NoneP: Er ->.
case Eq: (first_diff y z) => [q|]; first last.
  by move: Ep Er; move/first_diff_NoneP: Eq => -> -> /Some_inj ->.
have := leqVgt p q; rewrite leq_eqVlt => /orP [/orP[]|].
- move=> /eqP pqE; move: Ep Eq; rewrite pqE => Eqx Eqz.
  rewrite first_diffC in Eqx; have := first_diff_eq Eqx Eqz Er.
  rewrite leq_eqVlt => /orP [/eqP ->|qr]; first by exact: Rtrans.
  case/first_diff_SomeP:Er => /(_ _ qr) -> _ ? ?; have : z q = y q.
    by apply: Ranti; apply/andP; split.
  by move=> E; case/first_diff_SomeP: Eqz=> + /nesym; rewrite E.
- move=> pq; move: Er.
  rewrite (@first_diff_lt y x z _ _ pq) ?[_ y x]first_diffC //.
  by move/Some_inj <- => ? _; case/first_diff_SomeP:Eq => /(_ _ pq) <-.
- move=> qp; move: Er.
  rewrite first_diffC (@first_diff_lt y _ _ _ _ qp) // ?[_ y x]first_diffC //.
  by move/Some_inj <- => _ ?; case/first_diff_SomeP:Ep => /(_ _ qp) ->.
Qed.

Lemma lexi_bigprod_total R : (forall n, total (R n)) -> total (lexi_bigprod R).
Proof.
move=> Rtotal; move=> x y.
case E : (first_diff x y) => [n|]; first last.
  by move/first_diff_NoneP:E ->; rewrite lexi_bigprod_reflexive.
rewrite /lexi_bigprod E first_diffC E; exact: Rtotal.
Qed.

Definition start_with n (t1 t2: forall n, K n) (i : nat) : K i :=
  if (i < n)%O then t1 i else t2 i.

Lemma start_with_prefix n x y : share_prefix n x (start_with n x y).
Proof. by move=> r rn; rewrite /start_with rn. Qed.

End big_lexi_order.

Definition big_lexi_order {I : Type} (T : I -> Type) : Type := forall i, T i.
HB.instance Definition _ (I : Type) (K : I -> choiceType) :=
  Choice.on (big_lexi_order K).

Section big_lexi_porder.
Context {d} {K : nat -> porderType d}.

Definition big_lexi_ord : rel (big_lexi_order K) :=
  lexi_bigprod (fun n k1 k2 => k1 <= k2)%O.

Local Lemma big_lexi_ord_reflexive : reflexive big_lexi_ord.
Proof. exact: lexi_bigprod_reflexive. Qed.

Local Lemma big_lexi_ord_anti : antisymmetric big_lexi_ord.
Proof. by apply: lexi_bigprod_anti => n; exact: le_anti. Qed.

Local Lemma big_lexi_ord_trans : transitive big_lexi_ord.
Proof. by apply: lexi_bigprod_trans=> n; [exact: le_trans| exact: le_anti]. Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build d (big_lexi_order K)
  big_lexi_ord_reflexive big_lexi_ord_anti big_lexi_ord_trans.
End big_lexi_porder.

Section big_lexi_total.
Context {d} {K : nat -> orderType d}.

Local Lemma big_lexi_ord_total : total (@big_lexi_ord _ K).
Proof. by apply: lexi_bigprod_total => ?; exact: le_total. Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build _
  (big_lexi_order K) big_lexi_ord_total.

End big_lexi_total.

Section big_lexi_bottom.
Context {d} {K : nat -> bPOrderType d}.

Local Lemma big_lex_bot x : (@big_lexi_ord _ K) (fun=> \bot)%O x.
Proof.
rewrite /big_lexi_ord/lexi_bigprod.
by case E: (first_diff _ _); [exact: Order.le0x | done].
Qed.

HB.instance Definition _ := @Order.hasBottom.Build _
  (big_lexi_order K) (fun=> \bot)%O big_lex_bot.

End big_lexi_bottom.

Section big_lexi_top.
Context {d} {K : nat -> tPOrderType d}.

Local Lemma big_lex_top x : (@big_lexi_ord _ K) x (fun=> \top)%O.
Proof.
rewrite /big_lexi_ord/lexi_bigprod.
by case E: (first_diff _ _); [exact: Order.lex1 | done].
Qed.

HB.instance Definition _ := @Order.hasTop.Build _
  (big_lexi_order K) (fun=> \top)%O big_lex_top.

End big_lexi_top.

Section big_lexi_intervals.
Context {d} {K : nat -> orderType d}.
Lemma lexi_bigprod_prefix_lt (b a x: big_lexi_order K) n :
  (a < b)%O ->
  first_diff a b = Some n ->
  share_prefix n.+1 x b ->
  (a < x)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP [pfa abN].
case E1 : (first_diff a x) => [m|]; first last.
  by move/first_diff_NoneP:E1 <- => _ /(_ n (ltnSn _)).
move=> ab pfx; apply/andP; split.
  by apply/negP => /eqP/first_diff_NoneP; rewrite first_diffC E1.
move: ab; rewrite /Order.lt/= => /andP [?].
rewrite /big_lexi_ord /lexi_bigprod E1 abD; suff : n = m.
  by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ a x) => //=; last by case/first_diff_SomeP:E1.
split; last by by have -> := pfx n (ltnSn _).
by apply: (share_prefix_trans pfa); rewrite share_prefixC; exact: share_prefixS.
Qed.

Lemma lexi_bigprod_prefix_gt (b a x: big_lexi_order K) n :
  (b < a)%O ->
  first_diff a b = Some n ->
  share_prefix n.+1 x b ->
  (x < a)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP [pfa abN].
case E1 : (first_diff x a) => [m|]; first last.
  by move/first_diff_NoneP:E1 -> => _ /(_ n (ltnSn _)).
move=> ab pfx; apply/andP; split.
  by apply/negP => /eqP/first_diff_NoneP; rewrite first_diffC E1.
move: ab; rewrite /Order.lt/= => /andP [?].
rewrite /big_lexi_ord /lexi_bigprod [_ b a]first_diffC E1 abD; suff : n = m.
  by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ x a) => //=; last by case/first_diff_SomeP:E1.
rewrite share_prefixC; split; last by have -> := pfx n (ltnSn _); apply/nesym.
by apply: (share_prefix_trans pfa); rewrite share_prefixC; exact: share_prefixS.
Qed.

Lemma lexi_bigprod_between (a x b: big_lexi_order K) n :
  (a <= x <= b)%O ->
  share_prefix n a b ->
  share_prefix n x a.
Proof.
move=> axb; elim: n => // n IH.
move=> pfxSn m mSn; have pfxA : share_prefix n a x.
  by rewrite share_prefixC; apply: IH; apply: (share_prefixS _  pfxSn).
have pfxB : share_prefix n x b.
  apply (@share_prefix_trans _ n x a b); first by rewrite share_prefixC.
  exact: (share_prefixS _  pfxSn).
move: mSn; rewrite /Order.lt/= ltnS leq_eqVlt => /orP []; first last.
  by move: pfxA; rewrite share_prefixC; exact.
move/eqP ->; apply: le_anti; apply/andP; split.
  case/andP:axb => ? +; rewrite {1}/Order.le/=/big_lexi_ord/lexi_bigprod.
  have -> := pfxSn n (ltnSn _).
  case E : (first_diff x b) => [r|]; last by move/first_diff_NoneP:E ->.
  move=> xrb; have : n <= r.
    rewrite leqNgt; apply/negP=> /[dup] /pfxB xbE.
    by case/first_diff_SomeP:E => _; rewrite xbE.
  rewrite leq_eqVlt => /orP [/eqP -> //|] => nr.
  by case/first_diff_SomeP:E => /(_ n nr) ->.
case/andP:axb => + ?; rewrite {1}/Order.le/=/big_lexi_ord/lexi_bigprod.
case E : (first_diff a x) => [r|]; last by move/first_diff_NoneP:E <-.
move=> xrb; have : n <= r.
  rewrite leqNgt; apply/negP=> /[dup] /pfxA xbE.
  by case/first_diff_SomeP:E => _; rewrite xbE.
rewrite leq_eqVlt => /orP [/eqP -> //|] => nr.
by case/first_diff_SomeP:E => /(_ n nr) ->.
Qed.

Lemma big_lexi_interval_prefix (i : interval (big_lexi_order K))
    (x : big_lexi_order K) :
  itv_open_ends i -> x \in i ->
  exists n, (share_prefix n x `<=` [set` i]).
Proof.
move: i; case=> [][[]l|[]] [[]r|[]] [][]; rewrite ?in_itv /= ?andbT.
- move=> /andP [] lx xr.
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP: E1 ->; rewrite bnd_simp.
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP: E2 ->; rewrite bnd_simp.
  exists (Order.max n m).+1 => p xppfx; rewrite set_itvE.
  apply/andP; split.
    apply: (lexi_bigprod_prefix_lt lx E1) => w wm; apply/sym_equal/xppfx.
    by move/ltnSE/leq_ltn_trans: wm; apply; rewrite ltnS leq_max leqnn orbT.
  rewrite first_diffC in E2.
  apply: (lexi_bigprod_prefix_gt xr E2) => w wm; apply/sym_equal/xppfx.
  by move/ltnSE/leq_ltn_trans: wm; apply; rewrite ltnS leq_max leqnn.
- move=> lx.
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP: E1 ->; rewrite bnd_simp.
  exists m.+1 => p xppfx; rewrite set_itvE /=.
  by apply: (lexi_bigprod_prefix_lt lx E1) => w wm; apply/sym_equal/xppfx.
- move=> xr.
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP: E2 ->; rewrite bnd_simp.
  exists n.+1; rewrite first_diffC in E2 => p xppfx.
  rewrite set_itvE /=.
  by apply: (lexi_bigprod_prefix_gt xr E2) => w wm; apply/sym_equal/xppfx.
by move=> _; exists 0=> ? ?; rewrite set_itvE.
Qed.
End big_lexi_intervals.

(** TODO: generalize to tbOrderType when that's available in mathcomp*)
Lemma shared_prefix_closed_itv {d} {K : nat -> finOrderType d} n
  (x : big_lexi_order K) :
  share_prefix n x =
    `[(start_with n x (fun=>\bot):big_lexi_order K)%O, (start_with n x (fun=>\top))%O].
Proof.
rewrite eqEsubset; split=> z; first last.
  rewrite set_itvE /= => xbt; apply: share_prefix_trans.
    apply: (@start_with_prefix _ _ _ (fun=> \bot)%O).
  rewrite share_prefixC; apply: (lexi_bigprod_between xbt).
  apply:share_prefix_trans; last by apply: @start_with_prefix.
  by rewrite share_prefixC; apply: start_with_prefix.
move=> pfxz; rewrite set_itvE /= /Order.le /= /big_lexi_ord /= /lexi_bigprod.
apply/andP; split.
  case E : (first_diff _ _ ) => [m|] //; rewrite /start_with /=.
  case mn : (_ < _)%O => //; last by rewrite le0x.
  by (suff -> : x m = z m by done); apply: pfxz.
case E : (first_diff _ _ ) => [m|] //; rewrite /start_with /=.
case mn : (_ < _)%O => //; last by rewrite lex1.
by (suff -> : x m = z m by done); exact: pfxz.
Qed.
