Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov hierarchy.

Require Rstruct.
From mathcomp Require Import ssrbool eqtype ssrnat choice fintype ssralg.
From mathcomp Require Import ssrfun seq bigop ssrnum.

(* We should have compatilibity modules for every lemma in Hierarchy
that we deleted (and replaced by mathcomp's ones) so that the rest of
Coquelicot compiles just with a import of The compatibility modules *)

Section AbelianGroup1.

Notation AbelianGroup := zmodType.

Context {G : AbelianGroup}.

Notation zero := (0%R : G).
Notation plus := +%R.
Notation opp := GRing.opp.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).

Import GRing.Theory.

Lemma plus_comm : forall x y : G, plus x y = plus y x.
Proof. exact: addrC. Qed.

Lemma plus_assoc : forall x y z : G, plus x (plus y z) = plus (plus x y) z.
Proof. exact: addrA. Qed.

Lemma plus_zero_r : forall x : G, plus x zero = x.
Proof. exact: addr0. Qed.

Lemma plus_opp_r : forall x : G, plus x (opp x) = zero.
Proof. exact: addrN. Qed.

Lemma plus_zero_l : forall x : G, plus zero x = x.
Proof. exact: add0r. Qed.

Lemma plus_opp_l : forall x : G, plus (opp x) x = zero.
Proof. exact: addNr. Qed.

Lemma opp_zero : opp zero = zero.
Proof. exact: oppr0. Qed.

Lemma minus_zero_r : forall x : G, minus x zero = x.
Proof. exact: subr0. Qed.

Lemma minus_eq_zero (x : G) : minus x x = zero.
Proof. exact: subrr. Qed.

Lemma plus_reg_l : forall r x y : G, plus r x = plus r y -> x = y.
Proof.
move=> r x y /eqP.
by rewrite (addrC r y) -subr_eq addrAC subrr add0r => /eqP.
Qed.

Lemma plus_reg_r : forall r x y : G, plus x r = plus y r -> x = y.
Proof.
by move=> r x y => /eqP; rewrite -subr_eq -addrA subrr addr0 => /eqP.
Qed.

Lemma opp_opp : forall x : G, opp (opp x) = x.
Proof. exact: opprK. Qed.

Lemma opp_plus : forall x y : G, opp (plus x y) = plus (opp x) (opp y).
Proof. exact: opprD. Qed.

Lemma opp_minus (x y : G) : opp (minus x y) = minus y x.
Proof. exact: opprB. Qed.

Lemma minus_trans (r x y : G) : minus x y = plus (minus x r) (minus r y).
Proof. by rewrite addrA -(addrA x) (addrC _ r) subrr addr0. Qed.

End AbelianGroup1.

Section Sums.

Notation AbelianGroup := zmodType.

Context {G : AbelianGroup}.

Notation zero := (0%R : G).
Notation plus := +%R.
Notation opp := GRing.opp.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).

Import GRing.Theory.

Definition sum_n_m (a : nat -> G) n m := Iter.iter_nat plus zero a n m.

Lemma sum_n_mE a n m : sum_n_m a n m = (\sum_(n <= i < m.+1) (a i))%R.
Proof.
rewrite /sum_n_m /Iter.iter_nat BigOp.bigopE /reducebig /index_iota.
move Hs : (iota _ _) => s {Hs n m}.
by elim: s => // h t IH /=; rewrite IH.
Qed.

Definition sum_n (a : nat -> G) n := sum_n_m a O n.

Lemma sum_n_m_Chasles (a : nat -> G) (n m k : nat) :
  (n <= S m)%nat -> (m <= k)%nat
    -> sum_n_m a n k = plus (sum_n_m a n m) (sum_n_m a (S m) k).
Proof.
move=> nm mk; rewrite !sum_n_mE -big_cat /=; apply congr_big => //.
rewrite /index_iota (_ : k.+1 - n = m.+1 - n + (k.+1 - m.+1))%N; last first.
  by rewrite addnC addnBA // subnK.
by rewrite iota_add subnKC.
Qed.

Lemma sum_n_n (a : nat -> G) (n : nat) : sum_n_m a n n = a n.
Proof. by rewrite sum_n_mE big_nat1. Qed.

Lemma sum_O (a : nat -> G) : sum_n a 0 = a O.
Proof. by rewrite /sum_n sum_n_mE big_nat_recr //= big_nil add0r. Qed.

Lemma sum_n_Sm (a : nat -> G) (n m : nat) :
  (n <= S m)%nat -> sum_n_m a n (S m) = plus (sum_n_m a n m) (a (S m)).
Proof. by move=> nm; rewrite !sum_n_mE big_nat_recr. Qed.

Lemma sum_Sn_m (a : nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a n m = plus (a n) (sum_n_m a (S n) m).
Proof. by move=> nm; rewrite !sum_n_mE big_nat_recl // big_add1. Qed.

Lemma sum_n_m_S (a : nat -> G) (n m : nat) :
  sum_n_m (fun n => a (S n)) n m = sum_n_m a (S n) (S m).
Proof. by rewrite !sum_n_mE big_add1. Qed.

Lemma sum_Sn (a : nat -> G) (n : nat) :
  sum_n a (S n) = plus (sum_n a n) (a (S n)).
Proof. by rewrite /sum_n !sum_n_mE big_nat_recr. Qed.

Lemma sum_n_m_zero (a : nat -> G) (n m : nat) :
  (m < n)%nat -> sum_n_m a n m = zero.
Proof.
move=> mn; rewrite !sum_n_mE big_seq_cond (eq_bigl xpred0) ?big_pred0 // => i.
move: mn; rewrite mem_iota; rewrite -subn_eq0 => /eqP ->; rewrite addn0 andbT.
by apply/negbTE; rewrite negb_and leqNgt negbK orbN.
Qed.

Lemma sum_n_m_const_zero (n m : nat) : sum_n_m (fun _ => zero) n m = zero.
Proof. by rewrite sum_n_mE big1. Qed.

Lemma sum_n_m_ext_loc (a b : nat -> G) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  sum_n_m a n m = sum_n_m b n m.
Proof.
move=> k.
rewrite !sum_n_mE big_seq_cond [in RHS]big_seq_cond; apply eq_bigr => i /=.
rewrite andbT mem_iota; case/boolP : (m.+1 - n == 0)%N => [/eqP->|].
  rewrite addn0; case/andP => ni /leq_trans/(_ ni); by rewrite ltnn.
rewrite subn_eq0 -leqNgt => ?; rewrite subnKC; last by rewrite ltnW.
rewrite ltnS; by apply k.
Qed.

Lemma sum_n_m_ext (a b : nat -> G) n m : (forall n, a n = b n) ->
  sum_n_m a n m = sum_n_m b n m.
Proof. move=> ?; rewrite !sum_n_mE; by apply eq_bigr. Qed.

Lemma sum_n_ext_loc : forall (a b : nat -> G) N,
  (forall n, (n <= N)%nat -> a n = b n) ->
  sum_n a N = sum_n b N.
Proof.
move=> a b N H; apply sum_n_m_ext_loc => k; rewrite leq0n /=; by apply H.
Qed.

Lemma sum_n_ext : forall (a b : nat -> G) N, (forall n, a n = b n) ->
  sum_n a N = sum_n b N.
Proof. intros a b N H; by apply sum_n_ext_loc. Qed.

Lemma sum_n_m_plus : forall (u v : nat -> G) (n m : nat),
  sum_n_m (fun k => plus (u k) (v k)) n m = plus (sum_n_m u n m) (sum_n_m v n m).
Proof. move=> u v n m; by rewrite !sum_n_mE big_split. Qed.

Lemma sum_n_plus : forall (u v : nat -> G) (n : nat),
  sum_n (fun k => plus (u k) (v k)) n = plus (sum_n u n) (sum_n v n).
Proof. move=> u v n; apply sum_n_m_plus. Qed.

Lemma sum_n_switch : forall (u : nat -> nat -> G) (m n : nat),
  sum_n (fun i => sum_n (u i) n) m = sum_n (fun j => sum_n (fun i => u i j) m) n.
Proof.
move=> u m n; rewrite /sum_n !sum_n_mE.
rewrite (eq_bigr (fun i : nat => (\sum_(O <= j < n.+1) (u i j))%R)); last first.
  move=> i _; by rewrite sum_n_mE.
rewrite exchange_big; apply eq_bigr => i _l; by rewrite sum_n_mE.
Qed.

Lemma sum_n_m_sum_n (a:nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a (S n) m = minus (sum_n a m) (sum_n a n).
Proof.
move=> nm; apply/eqP; rewrite !/sum_n !sum_n_mE.
rewrite -subr_eq opprK /sum_n /sum_n_m addrC -big_cat.
by rewrite -{2}(add0n n.+1) -iota_add subn0 add0n subnKC.
Qed.

End Sums.

Section Ring1.

Notation Ring := ringType.

Context {K : Ring}.

Definition mult : K -> K -> K := *%R.
Definition one : K := 1%R.

Notation zero := 0%R.
Notation opp := GRing.opp.
Notation plus := +%R.

Import GRing.Theory.

Lemma mult_assoc : forall x y z : K, mult x (mult y z) = mult (mult x y) z.
Proof. exact: mulrA. Qed.

Lemma mult_one_r : forall x : K, mult x one = x.
Proof. exact: mulr1. Qed.

Lemma mult_one_l : forall x : K, mult one x = x.
Proof. exact: mul1r. Qed.

Lemma mult_distr_r : forall x y z : K, mult (plus x y) z = plus (mult x z) (mult y z).
Proof. exact: mulrDl. Qed.

Lemma mult_distr_l : forall x y z : K, mult x (plus y z) = plus (mult x y) (mult x z).
Proof. exact: mulrDr. Qed.

Lemma mult_zero_r : forall x : K, mult x zero = zero.
Proof. exact: mulr0. Qed.

Lemma mult_zero_l : forall x : K, mult zero x = zero.
Proof. exact: mul0r. Qed.

Lemma opp_mult_r : forall x y : K, opp (mult x y) = mult x (opp y).
Proof. by move=> *; rewrite -mulrN. Qed.

Lemma opp_mult_l : forall x y : K, opp (mult x y) = mult (opp x) y.
Proof. by move=> *; rewrite -mulNr. Qed.

Lemma opp_mult_m1 : forall x : K, opp x = mult (opp one) x.
Proof. by move=> *; rewrite -mulN1r. Qed.

Lemma sum_n_m_mult_r : forall (a : K) (u : nat -> K) (n m : nat),
  sum_n_m (fun k => mult (u k) a) n m = mult (sum_n_m u n m) a.
Proof. by move=> a u n m; rewrite !sum_n_mE -big_distrl. Qed.

Lemma sum_n_m_mult_l : forall (a : K) (u : nat -> K) (n m : nat),
  sum_n_m (fun k => mult a (u k)) n m = mult a (sum_n_m u n m).
Proof. by move=> a u n m; rewrite !sum_n_mE -big_distrr. Qed.

Lemma sum_n_mult_r : forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult (u k) a) n = mult (sum_n u n) a.
Proof. intros ; by apply sum_n_m_mult_r. Qed.

Lemma sum_n_mult_l : forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult a (u k)) n = mult a (sum_n u n).
Proof. intros ; by apply sum_n_m_mult_l. Qed.

(** pow_n *)

Definition pow_n (x : K) (N : nat) : K := (x ^+ N).

(*Fixpoint pow_n (x : K) (N : nat) {struct N} : K :=
  match N with
   | 0%nat => one
   | S i => mult x (pow_n x i)
  end.*)

Lemma pow_n_plus : forall (x : K) (n m : nat), pow_n x (n+m) = mult (pow_n x n) (pow_n x m).
Proof. exact: exprD. Qed.

Lemma pow_n_comm_1 : forall (x : K) (n : nat), mult (pow_n x n) x = mult x (pow_n x n).
Proof.
move=> x; elim=> /= => [|n]; first by rewrite /pow_n expr0 /mult mulr1 mul1r.
rewrite /mult /pow_n; by rewrite !exprS -mulrA => ->.
Qed.

Lemma pow_n_comm : forall (x : K) n m, mult (pow_n x n) (pow_n x m) = mult (pow_n x m) (pow_n x n).
Proof. move=> x n m; by rewrite /mult -exprD addnC exprD. Qed.

End Ring1.

Section AbsRing1.

Notation AbsRing := absRingType.

Context {K : AbsRing}.

Notation abs := (@abs K).
Notation zero := 0%R.
Notation opp := GRing.opp.
Notation plus := +%R.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).

Lemma abs_zero : abs zero = 0.
Proof. exact: absr0. Qed.

Lemma abs_opp_one : abs (opp one) = 1.
Proof. exact: @absrN1 K. Qed.

Lemma abs_triangle : forall x y : K, abs (plus x y) <= abs x + abs y.
Proof. move=> x y; by move/Rstruct.RlebP: (@ler_abs_add K x y). Qed.

Lemma abs_mult : forall x y : K, abs (mult x y) <= abs x * abs y.
Proof. move=> x y; by move/Rstruct.RlebP : (absrM x y). Qed.

Lemma abs_eq_zero : forall x : K, abs x = 0 -> x = zero.
Proof. exact: absr0_eq0. Qed.

Lemma abs_opp : forall x, abs (opp x) = abs x.
Proof. exact: absrN. Qed.

Lemma abs_minus : forall x y : K, abs (minus x y) = abs (minus y x).
Proof. exact: absrB. Qed.

Lemma abs_one : abs one = 1.
Proof. exact: absr1. Qed.

Lemma abs_ge_0 : forall x, 0 <= abs x.
Proof. move=> x; by move/Rstruct.RlebP : (absr_ge0 x). Qed.

Lemma abs_pow_n : forall (x : K) n, abs (pow_n x n) <= (abs x)^n.
Proof.
move=> x n; move/Rstruct.RlebP : (absrX x n) => /Rle_trans; apply.
rewrite Rstruct.RpowE; by apply Rle_refl.
Qed.

End AbsRing1.

(*Import AbsRingCompat.*)

Section NormedModule1.

Notation AbsRing := absRingType.
Notation NormedModule K := (normedModType K).

Context {K : AbsRing} {V : NormedModule K}.

Notation zero := 0%R.
Notation opp := GRing.opp.
Notation plus := +%R.
Notation scal := *:%R.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).

Definition norm : V -> R := NormedModule.norm (NormedModule.class V).

Definition norm_factor : R := NormedModule.norm_factor (NormedModule.class V).

Lemma norm_triangle : forall x y : V, norm (plus x y) <= norm x + norm y.
Proof. by move=> x y; move/Rstruct.RlebP: (ler_normm_add x y). Qed.

Lemma norm_scal : forall (l : K) (x : V), norm (scal l x) <= abs l * norm x.
Proof. by move=> l k; move/Rstruct.RlebP: (ler_normmZ l k). Qed.

Lemma norm_compat1 : forall (x y : V) (eps : R), norm (minus y x) < eps -> ball x eps y.
Proof.
move=> x y e yxe.
have He : 0 < e by apply/(Rle_lt_trans _ _ _ _ yxe)/Rstruct.RlebP/normm_ge0.
suff : ball y (mkposreal _ He) x by apply ball_sym.
by apply/(@NormedModule.ax3 _ _ _ (NormedModule.class V))/Rstruct.RltbP.
Qed.

Lemma norm_compat2 : forall (x y : V) (eps : posreal), ball x eps y ->
  norm (minus y x) < norm_factor * eps.
Proof.
by move=> x y e /ball_sym/(@NormedModule.ax4 _ _ _ (NormedModule.class V))/Rstruct.RltbP.
Qed.

Lemma norm_eq_zero : forall x : V, norm x = 0 -> x = zero.
Proof. exact: NormedModule.ax5. Qed.

Lemma norm_zero : norm zero = 0.
Proof. move: (@normm_eq0 K V zero); by rewrite eqxx => /eqP. Qed.

Lemma norm_factor_gt_0 : 0 < norm_factor.
Proof. by move: (@norm_factor_gt_0 K V) => /Rstruct.RltbP. Qed.

Lemma norm_opp : forall x : V, norm (opp x) = norm x.
Proof. exact: normmN. Qed.

Lemma norm_ge_0 : forall x : V, 0 <= norm x.
Proof. by move=> x; move: (normm_ge0 x) => /Rstruct.RlebP. Qed.

Lemma norm_triangle_inv : forall x y : V, Rabs (norm x - norm y) <= norm (minus x y).
Proof. move=> x y; by move: (ler_distm_dist x y) => /= => /Rstruct.RlebP. Qed.

Lemma eq_close : forall x y : V, close x y -> x = y.
Proof. by move=> x y; rewrite closeE. Qed.

Definition ball_norm (x : V) (eps : R) (y : V) := norm (minus y x) < eps.

Definition locally_norm (x : V) (P : V -> Prop) :=
  exists eps : posreal, forall y, ball_norm x eps y -> P y.

Lemma locally_le_locally_norm x : filter_le (locally x) (locally_norm x).
Proof.
rewrite -locally_locally_norm /filter_le => P [e He].
exists e => y /Rstruct.RltbP Hy; apply He.
by rewrite /hierarchy.ball_norm normmB in Hy.
Qed.

Lemma locally_norm_le_locally x : filter_le (locally_norm x) (locally x).
Proof.
rewrite -locally_locally_norm /filter_le => P [e He].
exists e => y /Rstruct.RltbP Hy; apply He.
by rewrite /hierarchy.ball_norm normmB.
Qed.

Lemma locally_norm_ball_norm x (e : posreal) : locally_norm x (ball_norm x e).
Proof. by exists e. Qed.

Lemma locally_norm_ball : forall x (eps : posreal), locally_norm x (ball x eps).
Proof. move=> x e; by apply/locally_norm_le_locally/locally_ball. Qed.

Lemma locally_ball_norm x (eps : posreal) : locally x (ball_norm x eps).
Proof. by apply/locally_le_locally_norm/locally_norm_ball_norm. Qed.

Lemma ball_norm_triangle (x y z : V) (e1 e2 : R) :
  ball_norm x e1 y -> ball_norm y e2 z -> ball_norm x (e1 + e2) z.
Proof.
move: (@ball_norm_triangle _ _ x y z e1 e2); rewrite /ball_norm.
rewrite /hierarchy.ball_norm normmB (normmB _ z) (normmB x) => H.
by move/Rstruct.RltbP => ? /Rstruct.RltbP ?; apply/Rstruct.RltbP/H.
Qed.

Lemma ball_norm_center (x : V) (e : posreal) : ball_norm x e x.
Proof. by move: (ball_norm_center x e) => /Rstruct.RltbP. Qed.

Lemma ball_norm_dec : forall (x y : V) (eps : posreal),
  {ball_norm x eps y} + {~ ball_norm x eps y}.
Proof.
move=> x y e; move: (ball_norm_dec x y e).
rewrite /hierarchy.ball_norm (normmB x) /ball_norm.
case; by [move=> /Rstruct.RltbP; left | right; apply/Rstruct.RltbP/negP].
Qed.

Lemma ball_norm_sym x y (e : posreal) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm -opp_minus norm_opp. Qed.

Lemma ball_norm_le : forall (x : V) (e1 e2 : posreal), e1 <= e2 ->
  forall y, ball_norm x e1 y -> ball_norm x e2 y.
Proof. move=> x e1 e2 He y H1; exact: (Rlt_le_trans _ _ _ H1). Qed.

Lemma ball_norm_eq : forall x y : V,
  (forall eps : posreal, ball_norm x eps y) -> x = y.
Proof.
move=> x y H; apply: (@ball_norm_eq K V x y) => e; move: (H e).
by rewrite /ball_norm /hierarchy.ball_norm -opp_minus norm_opp => /Rstruct.RltbP.
Qed.

Local Open Scope classical_set_scope.

Lemma is_filter_lim_unique {F} {FF : ProperFilter' F} (x y : V) :
  F --> x -> F --> y -> x = y.
Proof. exact: is_filter_lim_unique. Qed.

Lemma is_filter_lim_locally_unique (x y : V) : x --> y -> x = y.
Proof. move=> H; rewrite -closeE; exact: is_filter_lim_locally_close. Qed.

End NormedModule1.
