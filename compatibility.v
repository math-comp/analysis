Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov hierarchy.

From mathcomp Require Import ssrbool eqtype ssrnat choice fintype ssralg.
From mathcomp Require Import ssrfun seq bigop.

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

Definition sum_n_m (a : nat -> G) n m := (\sum_(n <= i < m.+1) (a i))%R.
(*  iter_nat plus zero a n m.*)
Definition sum_n (a : nat -> G) n := sum_n_m a O n.

Lemma sum_n_m_Chasles (a : nat -> G) (n m k : nat) :
  (n <= S m)%nat -> (m <= k)%nat
    -> sum_n_m a n k = plus (sum_n_m a n m) (sum_n_m a (S m) k).
Proof.
move=> nm mk; rewrite -big_cat /=; apply congr_big => //.
rewrite /index_iota (_ : k.+1 - n = m.+1 - n + (k.+1 - m.+1))%N; last first.
  by rewrite addnC addnBA // subnK.
by rewrite iota_add subnKC.
Qed.

Lemma sum_n_n (a : nat -> G) (n : nat) : sum_n_m a n n = a n.
Proof. by rewrite /sum_n_m big_nat1. Qed.

Lemma sum_O (a : nat -> G) : sum_n a 0 = a O.
Proof. by rewrite /sum_n /sum_n_m big_nat_recr //= big_nil add0r. Qed.

Lemma sum_n_Sm (a : nat -> G) (n m : nat) :
  (n <= S m)%nat -> sum_n_m a n (S m) = plus (sum_n_m a n m) (a (S m)).
Proof. by move=> nm; rewrite /sum_n_m big_nat_recr. Qed.

Lemma sum_Sn_m (a : nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a n m = plus (a n) (sum_n_m a (S n) m).
Proof. by move=> nm; rewrite /sum_n_m big_nat_recl // big_add1. Qed.

Lemma sum_n_m_S (a : nat -> G) (n m : nat) :
  sum_n_m (fun n => a (S n)) n m = sum_n_m a (S n) (S m).
Proof. by rewrite /sum_n_m big_add1. Qed.

Lemma sum_Sn (a : nat -> G) (n : nat) :
  sum_n a (S n) = plus (sum_n a n) (a (S n)).
Proof. by rewrite /sum_n /sum_n_m big_nat_recr. Qed.

Lemma sum_n_m_zero (a : nat -> G) (n m : nat) :
  (m < n)%nat -> sum_n_m a n m = zero.
Proof.
move=> mn; rewrite /sum_n_m big_seq_cond (eq_bigl xpred0) ?big_pred0 // => i.
move: mn; rewrite mem_iota; rewrite -subn_eq0 => /eqP ->; rewrite addn0 andbT.
by apply/negbTE; rewrite negb_and leqNgt negbK orbN.
Qed.

Lemma sum_n_m_const_zero (n m : nat) : sum_n_m (fun _ => zero) n m = zero.
Proof. by rewrite /sum_n_m big1. Qed.

Lemma sum_n_m_ext_loc (a b : nat -> G) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  sum_n_m a n m = sum_n_m b n m.
Proof.
move=> k.
rewrite /sum_n_m big_seq_cond [in RHS]big_seq_cond; apply eq_bigr => i /=.
rewrite andbT mem_iota; case/boolP : (m.+1 - n == 0)%N => [/eqP->|].
  rewrite addn0; case/andP => ni /leq_trans/(_ ni); by rewrite ltnn.
rewrite subn_eq0 -leqNgt => ?; rewrite subnKC; last by rewrite ltnW.
rewrite ltnS; by apply k.
Qed.

Lemma sum_n_m_ext (a b : nat -> G) n m : (forall n, a n = b n) ->
  sum_n_m a n m = sum_n_m b n m.
Proof. move=> ?; by apply eq_bigr. Qed.

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
Proof. move=> u v n m; by rewrite /sum_n_m big_split. Qed.

Lemma sum_n_plus : forall (u v : nat -> G) (n : nat),
  sum_n (fun k => plus (u k) (v k)) n = plus (sum_n u n) (sum_n v n).
Proof. move=> u v n; apply sum_n_m_plus. Qed.

Lemma sum_n_switch : forall (u : nat -> nat -> G) (m n : nat),
  sum_n (fun i => sum_n (u i) n) m = sum_n (fun j => sum_n (fun i => u i j) m) n.
Proof. move=> u m n; by rewrite /sum_n /sum_n_m exchange_big. Qed.

Lemma sum_n_m_sum_n (a:nat -> G) (n m : nat) :
  (n <= m)%nat -> sum_n_m a (S n) m = minus (sum_n a m) (sum_n a n).
Proof.
move=> nm; apply/eqP.
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
Proof. by move=> a u n m; rewrite /sum_n_m -big_distrl. Qed.

Lemma sum_n_m_mult_l : forall (a : K) (u : nat -> K) (n m : nat),
  sum_n_m (fun k => mult a (u k)) n m = mult a (sum_n_m u n m).
Proof. by move=> a u n m; rewrite /sum_n_m -big_distrr. Qed.

Lemma sum_n_mult_r : forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult (u k) a) n = mult (sum_n u n) a.
Proof. intros ; by apply sum_n_m_mult_r. Qed.

Lemma sum_n_mult_l :
 forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => mult a (u k)) n = mult a (sum_n u n).
Proof.
  intros ; by apply sum_n_m_mult_l.
Qed.

(** pow_n *)

Fixpoint pow_n (x : K) (N : nat) {struct N} : K :=
  match N with
   | 0%nat => one
   | S i => mult x (pow_n x i)
  end.

Lemma pow_n_plus :
  forall (x : K) (n m : nat), pow_n x (n+m) = mult (pow_n x n) (pow_n x m).
Proof.
  intros x.
  elim => /= [ | n IH] m.
  by rewrite mult_one_l.
  by rewrite IH mult_assoc.
Qed.

Lemma pow_n_comm_1 :
  forall (x : K) (n : nat), mult (pow_n x n) x = mult x (pow_n x n).
Proof.
  intros x n.
  elim: n => /= [ | n IH].
  by rewrite mult_one_l mult_one_r.
  by rewrite -(mult_assoc _ (pow_n x n)) IH.
Qed.

Lemma pow_n_comm :
  forall (x : K) n m, mult (pow_n x n) (pow_n x m) = mult (pow_n x m) (pow_n x n).
Proof.
  intros x n m.
  rewrite -2!pow_n_plus.
  by apply f_equal, Plus.plus_comm.
Qed.

End Ring1.