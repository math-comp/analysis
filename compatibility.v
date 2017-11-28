(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov hierarchy set.
Local Open Scope classical_set_scope.

Require Rstruct.
From mathcomp Require Import ssrbool eqtype ssrnat choice fintype ssralg.
From mathcomp Require Import ssrfun seq bigop ssrnum.

From SsrReals Require Import boolp.
(* We should have compatilibity modules for every lemma in Hierarchy
that we deleted (and replaced by mathcomp's ones) so that the rest of
Coquelicot compiles just with a import of The compatibility modules *)

(* Filter renamings *)
Notation filter_le := flim.

Lemma filter_le_refl T (F : set (set T)) : filter_le F F.
Proof. exact. Qed.

Lemma filter_le_trans T (F G H : set (set T)) :
  (filter_le F G) -> (filter_le G H) -> (filter_le F H).
Proof. exact: flim_trans. Qed.

Definition filter_true := @filterT.
Arguments filter_true {T F Filter}.
Definition filter_and := @filterI.
Arguments filter_and {T F Filter}.
Definition filter_imp := @filterS.
Arguments filter_imp {T F Filter}.

Inductive filter_prod {T U : Type} (F G : _ -> Prop) (P : T * U -> Prop) : Prop :=
  Filter_prod (Q : T -> Prop) (R : U -> Prop) :
    F Q -> G R -> (forall x y, Q x -> R y -> P (x, y)) -> filter_prod F G P.

Lemma filter_prodE {T U : Type} : @filter_prod T U = @hierarchy.filter_prod T U.
Proof.
rewrite predeq3E=> F G P; split=> [[Q R FQ GR QRP] | [_ [Q FQ [R GR <-]]] QRP].
  by exists (Q `*` R); do ?eexists; move=> // [??] [/=??]; apply: QRP.
by exists Q R => // ????; apply: QRP.
Qed.

Global Instance filter_prod_filter  T U (F : set (set T)) (G : set (set U)) :
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof. by rewrite filter_prodE; typeclasses eauto. Qed.

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Proof. by rewrite filter_prodE; typeclasses eauto. Qed.
Definition filter_prod_proper' := @filter_prod_proper.

Lemma filterlim_pair {T U V F} {G : set (set U)} {H : set (set V)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H} (f : T -> U) (g : T -> V) :
  f @ F `=>` G -> g @ F `=>` H ->
  (fun x => (f x, g x)) @ F `=>` filter_prod G H.
Proof. by rewrite filter_prodE; exact: filterlim_pair. Qed.

Lemma filterlim_comp_2 {T U V W}
  {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F `=>` G -> g @ F `=>` H ->
  (fun x => h (fst x) (snd x)) @ (filter_prod G H) `=>` I ->
  (fun x => h (f x) (g x)) @ F `=>` I.
Proof. by rewrite filter_prodE; exact: flim_comp2. Qed.

(* Algebraic structures renamings *)
Notation AbelianGroup := zmodType.
Notation AbsRing := absRingType.
Notation Ring := ringType.
Notation NormedModule K := (normedModType K).
Notation UniformSpace := uniformType.
Notation zero := (GRing.zero _).
Notation plus := +%R.
Notation opp := GRing.opp.
Notation minus := (fun a b => GRing.add a (GRing.opp b)).
Notation abs := (@abs _).
Notation scal := *:%R.

Section AbelianGroup1.

Context {G : AbelianGroup}.

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

Lemma opp_zero : opp zero = zero :> G.
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

Context {G : AbelianGroup}.

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

Context {K : Ring}.

Definition mult : K -> K -> K := *%R.
Definition one : K := 1%R.

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

Context {K : AbsRing}.

Lemma abs_zero : abs (zero : K) = 0.
Proof. exact: absr0. Qed.

Lemma abs_opp_one : abs (opp one : K) = 1.
Proof. exact: @absrN1 K. Qed.

Lemma abs_triangle : forall x y : K, abs (plus x y) <= abs x + abs y.
Proof. move=> x y; by move/Rstruct.RlebP: (@ler_abs_add K x y). Qed.

Lemma abs_mult : forall x y : K, abs (mult x y) <= abs x * abs y.
Proof. move=> x y; by move/Rstruct.RlebP : (absrM x y). Qed.

Lemma abs_eq_zero : forall x : K, abs x = 0 -> x = zero.
Proof. exact: absr0_eq0. Qed.

Lemma abs_opp : forall x : K, abs (opp x) = abs x.
Proof. exact: absrN. Qed.

Lemma abs_minus : forall x y : K, abs (minus x y) = abs (minus y x).
Proof. exact: absrB. Qed.

Lemma abs_one : abs (one : K) = 1.
Proof. exact: absr1. Qed.

Lemma abs_ge_0 : forall x : K, 0 <= abs x.
Proof. move=> x; by move/Rstruct.RlebP : (absr_ge0 x). Qed.

Lemma abs_pow_n : forall (x : K) n, abs (pow_n x n) <= (abs x)^n.
Proof.
move=> x n; move/Rstruct.RlebP : (absrX x n) => /Rle_trans; apply.
rewrite Rstruct.RpowE; by apply Rle_refl.
Qed.

End AbsRing1.

(*Import AbsRingCompat.*)

Notation ModuleSpace K := (lmodType K).

Section ModuleSpace1.

Context {K : Ring} {V : ModuleSpace K}.

Lemma scal_assoc (x y : K) (u : V) : scal x (scal y u) = scal (mult x y) u.
Proof. exact: GRing.scalerA. Qed.

Lemma scal_one (u : V) : scal one u = u.
Proof. exact: GRing.scale1r. Qed.

Lemma scal_distr_l (x : K) (u v : V) : scal x (plus u v) = plus (scal x u) (scal x v).
Proof. exact: GRing.scalerDr. Qed.

Lemma scal_distr_r (x y : K) (u : V) : scal (plus x y) u = plus (scal x u) (scal y u).
Proof. exact: GRing.scalerDl. Qed.

Lemma scal_zero_r (x : K) : scal x (zero : V) = zero.
Proof. exact: GRing.scaler0. Qed.

Lemma scal_zero_l (u : V) : scal zero u = zero.
Proof.
Proof. exact: GRing.scale0r. Qed.

Lemma scal_opp_l (x : K) (u : V) : scal (opp x) u = opp (scal x u).
Proof. exact: GRing.scaleNr. Qed.

Lemma scal_opp_r (x : K) (u : V) : scal x (opp u) = opp (scal x u).
Proof. exact: GRing.scalerN. Qed.

Lemma scal_opp_one (u : V) : scal (opp one) u = opp u.
Proof. exact: GRing.scaleN1r. Qed.

Lemma scal_minus_distr_l (x : K) (u v : V) : scal x (minus u v) = minus (scal x u) (scal x v).
Proof. exact: GRing.scalerBr. Qed.

Lemma scal_minus_distr_r (x y : K) (u : V) : scal (minus x y) u = minus (scal x u) (scal y u).
Proof. exact: GRing.scalerBl. Qed.

Lemma sum_n_m_scal_l (a : K) (u : nat -> V) (n m : nat) :
  sum_n_m (fun k => scal a (u k)) n m = scal a (sum_n_m u n m).
Proof. by rewrite sum_n_mE -GRing.scaler_sumr -sum_n_mE. Qed.

Lemma sum_n_scal_l (a : K) (u : nat -> V) (n : nat) :
  sum_n (fun k => scal a (u k)) n = scal a (sum_n u n).
Proof. by rewrite /sum_n sum_n_m_scal_l. Qed.

End ModuleSpace1.

Section NormedModule1.

Context {K : AbsRing} {V : NormedModule K}.

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
Proof. exact: flim_unique. Qed.

Lemma is_filter_lim_locally_unique (x y : V) : x --> y -> x = y.
Proof. move=> H; rewrite -closeE; exact: is_filter_lim_locally_close. Qed.

End NormedModule1.

(* TODO *)
(* Section RealSums. *)

(* Lemma sum_n_Reals : forall a N, sum_n a N = sum_f_R0 a N. *)
(* Proof. *)
(*   intros a; induction N; simpl. *)
(*   apply sum_n_n. *)
(*   by rewrite sum_Sn IHN. *)
(* Qed. *)
(* Lemma sum_n_m_Reals a n m : (n <= m)%nat -> sum_n_m a n m = sum_f n m a. *)
(* Proof. *)
(*   induction m => //= Hnm. *)
(*   apply le_n_O_eq in Hnm. *)
(*   by rewrite -Hnm sum_n_n /=. *)
(*   case: (le_dec n m) => H. *)
(*   rewrite sum_n_Sm // IHm //. *)
(*   rewrite sum_f_n_Sm //. *)
(*   replace n with (S m). *)
(*   rewrite sum_n_n. *)
(*   by rewrite /sum_f minus_diag /=. *)
(*   apply le_antisym => //. *)
(*   apply not_le in H. *)
(*   by apply lt_le_S. *)
(* Qed. *)

(* Lemma sum_n_m_const (n m : nat) (a : R) : *)
(*   sum_n_m (fun _ => a) n m = INR (S m - n) * a. *)
(* Proof. *)
(*   rewrite /sum_n_m /iter_nat (iter_const _ a). *)
(*   by rewrite -{2}(seq.size_get n (S m - n)). *)
(* Qed. *)
(* Lemma sum_n_const (n : nat) (a : R) : *)
(*   sum_n (fun _ => a) n = INR (S n) * a. *)
(* Proof. *)
(*   by rewrite /sum_n sum_n_m_const -minus_n_O. *)
(* Qed. *)

(* Lemma norm_sum_n_m {K : AbsRing} {V : NormedModule K} (a : nat -> V) (n m : nat) : *)
(*   norm (sum_n_m a n m) <= sum_n_m (fun n => norm (a n)) n m. *)
(* Proof. *)
(*   case: (le_dec n m) => Hnm. *)
(*   elim: m n a Hnm => /= [ | m IH] n a Hnm. *)
(*   apply le_n_O_eq in Hnm. *)
(*   rewrite -Hnm !sum_n_n. *)
(*   by apply Rle_refl. *)
(*   destruct n. *)
(*   rewrite /sum_n !sum_n_Sm ; try by apply le_O_n. *)
(*   eapply Rle_trans. *)
(*   apply norm_triangle. *)
(*   apply Rplus_le_compat_r, IH, le_O_n. *)
(*   rewrite -!sum_n_m_S. *)
(*   apply IH. *)
(*   by apply le_S_n. *)
(*   apply not_le in Hnm. *)
(*   rewrite !sum_n_m_zero // norm_zero. *)
(*   by apply Rle_refl. *)
(* Qed. *)

(* Lemma sum_n_m_le (a b : nat -> R) (n m : nat) : *)
(*   (forall k, a k <= b k) *)
(*   -> sum_n_m a n m <= sum_n_m b n m. *)
(* Proof. *)
(*   intros H. *)
(*   case: (le_dec n m) => Hnm. *)
(*   elim: m n a b Hnm H => /= [ | m IH] n a b Hnm H. *)
(*   apply le_n_O_eq in Hnm ; rewrite -Hnm. *)
(*   rewrite !sum_n_n ; by apply H. *)
(*   destruct n. *)
(*   rewrite !sum_n_Sm ; try by apply le_O_n. *)
(*   apply Rplus_le_compat. *)
(*   apply IH => // ; by apply le_O_n. *)
(*   by apply H. *)
(*   rewrite -!sum_n_m_S. *)
(*   apply IH => //. *)
(*   by apply le_S_n. *)
(*   apply not_le in Hnm. *)
(*   rewrite !sum_n_m_zero //. *)
(*   by apply Rle_refl. *)
(* Qed. *)

(* Lemma pow_n_pow : *)
(*   forall (x : R) k, pow_n x k = x^k. *)
(* Proof. *)
(* intros x; induction k; simpl. *)
(* easy. *)
(* now rewrite IHk. *)
(* Qed. *)

(* End RealSums. *)

Local Open Scope classical_set_scope.

Lemma filterlim_locally {U : uniformType} {F} {FF : Filter F} (y : U) :
  F --> y <-> forall eps : posreal, F [set x | ball y eps x].
Proof. exact: @filterlim_locally _ F FF y. Qed.

Lemma filterlim_opp {K : absRingType} {V : normedModType K} (x : V) : (@GRing.opp V) @ x --> (- x)%R.
Proof. exact: filterlim_opp. Qed.

Lemma filterlim_plus (K : absRingType) (V : normedModType K) (x y : V) : (z.1 + z.2)%R @[z --> (x, y)] --> (x + y)%R.
Proof. exact: filterlim_plus. Qed.

Lemma ballE (l : R) (e : R(*posreal*)) : ball l e = (fun y => R_dist y l < e).
Proof.
rewrite funeqE => x; rewrite propeqE.
rewrite /ball /= /AbsRing_ball absrB; split => [/Rstruct.RltP //| ?]; by apply/Rstruct.RltP.
Qed.

Lemma locally_ex_dec {T : uniformType} (x : T) (P : T -> Prop) :
  (forall x, P x \/ ~ P x) ->
  locally x P ->
  {d : posreal | forall y, ball x d y -> P y}.
Proof. move=> _; exact: locally_ex. Qed.

Lemma normE {K : absRingType} {U : normedModType K} (x : U) : norm x = (`|[ x ]|)%R.
Proof. by []. Qed.

Lemma filterlim_locally_ball_norm {K : absRingType} {T} {U : normedModType K}
  {F : set (set T)} {FF : Filter F} (f : T -> U) (y : U) :
  f @ F --> y <-> forall eps : posreal, F (fun x => ball_norm y eps (f x)).
Proof.
rewrite flim_normP; split => /= Ff eps; have := Ff eps;
by apply: filterS => P; move=> /Rstruct.RltP; rewrite normmB.
Qed.

Lemma locally_singleton {T : UniformSpace} (x : T) (P : T -> Prop) : locally x P -> P x.
Proof. exact: locally_singleton. Qed.

Require Import Rstruct.

Canonical R_lmodtype := LmodType R R (GRing.Lmodule.class [lmodType R of R^o]).
Canonical R_NormedModule := NormedModType R R (NormedModule.class [normedModType R of R^o]).
Canonical R_completeNormedModule := [completeNormedModType R of R].

Lemma RabsE (a : R) : Rabs a = `| a |%R.
Proof. exact: absRE. Qed.

Lemma open_lt (y : R) : open (fun u : R => (u < y)%coqR).
Proof.
rewrite (_ : Rlt^~y = fun x => (x < y)%R); first by apply open_lt.
by rewrite funeqE => x; rewrite propeqE; split => /RltP.
Qed.

Lemma open_gt (y : R) : open (fun u : R => (y < u)%coqR).
Proof.
rewrite (_ : Rlt y = fun x => (y < x)%R); first by apply open_gt.
by rewrite funeqE => x; rewrite propeqE; split => /RltP.
Qed.

Lemma open_Rbar_lt' x y : Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof. exact: open_Rbar_lt'. Qed.

Lemma open_Rbar_gt' x y : Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof. exact: open_Rbar_gt'. Qed.

Import Num.Def.

Lemma sqrt_plus_sqr (x y : R) :
  Rmax `|x|%R `|y|%R <= Num.sqrt (x^+2 + y^+2) <= Num.sqrt 2%:R * Rmax `|x|%R `|y|%R.
Proof. case/andP: (sqrt_plus_sqr x y) => /RleP ? /RleP ?; by rewrite RmaxE. Qed.

(** ** Iterated Products *)

Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n => prod T (Tn n T)
  end.

Notation "[ x1 , .. , xn ]" := (pair x1 .. (pair xn tt) .. ).

Fixpoint mk_Tn {T} (n : nat) (u : nat -> T) : Tn n T :=
  match n with
    | O => (tt : Tn O T)
    | S n => (u O, mk_Tn n (fun n => u (S n)))
  end.
Fixpoint coeff_Tn {T} {n : nat} (x0 : T) : (Tn n T) -> nat -> T :=
  match n with
  | O => fun (_ : Tn O T) (_ : nat) => x0
  | S n' => fun (v : Tn (S n') T) (i : nat) => match i with
           | O => fst v
           | S i => coeff_Tn x0 (snd v) i
           end
  end.
Lemma mk_Tn_bij {T} {n : nat} (x0 : T) (v : Tn n T) :
  mk_Tn n (coeff_Tn x0 v) = v.
Proof.
  induction n ; simpl.
  now apply unit_ind.
  rewrite IHn ; by destruct v.
Qed.
Lemma coeff_Tn_bij {T} {n : nat} (x0 : T) (u : nat -> T) :
  forall i, (i < n)%coq_nat -> coeff_Tn x0 (mk_Tn n u) i = u i.
Proof.
  revert u ; induction n => /= u i Hi.
  by apply lt_n_O in Hi.
  destruct i.
  by [].
  now apply (IHn (fun n => u (S n))), lt_S_n.
Qed.
Lemma coeff_Tn_ext {T} {n : nat} (x1 x2 : T) (v1 v2 : Tn n T) :
  v1 = v2 <-> forall i, (i < n)%coq_nat -> coeff_Tn x1 v1 i = coeff_Tn x2 v2 i.
Proof.
  split.
  + move => -> {v1}.
    induction n => i Hi.
    by apply lt_n_O in Hi.
    destruct i ; simpl.
    by [].
    by apply IHn, lt_S_n.
  + induction n => H.
    apply unit_ind ; move: (v1) ; now apply unit_ind.
    apply injective_projections.
    by apply (H O), lt_O_Sn.
    apply IHn => i Hi.
    by apply (H (S i)), lt_n_S.
Qed.
Lemma mk_Tn_ext {T} (n : nat) (u1 u2 : nat -> T) :
  (forall i, (i < n)%coq_nat -> (u1 i) = (u2 i))
    <-> (mk_Tn n u1) = (mk_Tn n u2).
Proof.
  move: u1 u2 ; induction n ; simpl ; split ; intros.
  by [].
  by apply lt_n_O in H0.
  apply f_equal2.
  by apply H, lt_O_Sn.
  apply IHn => i Hi.
  by apply H, lt_n_S.
  destruct i.
  by apply (f_equal (@fst _ _)) in H.
  move: i {H0} (lt_S_n _ _ H0).
  apply IHn.
  by apply (f_equal (@snd _ _)) in H.
Qed.


(*
Global Instance AbelianGroup_Tn {T} :
  AbelianGroup T -> forall n, AbelianGroup (Tn n T) | 10.
Proof.
  intro GT.
  elim => /= [ | n IH].
  - apply Build_AbelianGroup with (fun _ _ => tt) (fun _ => tt) tt ; auto.
    by apply unit_ind.
  - by apply AbelianGroup_prod.
Defined.

Global Instance MetricBall_Tn :
  forall T, MetricBall T -> forall n, MetricBall (Tn n T) | 10.
Proof.
intros T MT n.
elim: n => [ | n MTn].
by apply Build_MetricBall with (fun _ _ _ => True).
by apply MetricBall_prod.
Defined.

Global Instance VectorSpace_mixin_Tn {T} {K} {FK : Ring K} :
  forall GT : AbelianGroup T,
  VectorSpace_mixin T K GT ->
  forall n, VectorSpace_mixin (Tn n T) K (AbelianGroup_Tn GT n) | 10.
Proof.
  intros GT VV.
  elim => [ | n VVn].
  apply Build_VectorSpace_mixin with (fun _ _ => tt) ; by apply unit_ind.
  by apply VectorSpace_mixin_prod.
Defined.

Global Instance VectorSpace_Tn {T} {K} {FK : Ring K} :
  VectorSpace T K -> forall n, VectorSpace (Tn n T) K | 10.
Proof.
  intros VV n.
  apply Build_VectorSpace with (AbelianGroup_Tn _ n).
  now apply VectorSpace_mixin_Tn, VV.
Defined.

Global Instance NormedVectorSpace_Tn {T} {K} {FK : absRingType K} :
  NormedVectorSpace T K ->
  forall n, NormedVectorSpace (Tn n T) K | 10.
Proof.
  move => VT.
  elim => [ | n NVTn].
  - econstructor.
    apply Build_NormedVectorSpace_mixin with (fun _ => 0).
    move => _ _.
    rewrite Rplus_0_l ; by apply Rle_refl.
    move => l _ ; rewrite Rmult_0_r ; by apply Rle_refl.
    easy.
    exists [posreal of 1].
    intros x y eps _.
    rewrite Rmult_1_l.
    apply cond_pos.
  - by apply NormedVectorSpace_prod.
Defined.
*)


Fixpoint Fn (n : nat) (T U : Type) : Type :=
  match n with
  | O => U
  | S n => T -> Fn n T U
  end.

(*
Global Instance MetricBall_Fn {T M} (n : nat) :
  MetricBall M -> MetricBall (Fn n T M) | 10.
Proof.
  intros MM.
  elim: n => /= [ | n IHn].
  exact MM.
  exact (MetricBall_fct IHn).
Defined.
*)
