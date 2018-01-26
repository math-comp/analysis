(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import xfinmap boolp reals discrete.
From SsrReals Require Import realseq realsum distr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Section IsCoupling.
Context {R : realType} (T1 T2 : choiceType).

Definition iscoupling mu1 mu2 (mu : {distr (T1 * T2) / R}) :=
  [/\ dfst mu =1 mu1 & dsnd mu =1 mu2].
End IsCoupling.

(* -------------------------------------------------------------------- *)
Section TV.
Context {R : realType} (T : choiceType).

Definition tv (mu1 mu2 : {distr T / R}) : R :=
  sup [pred x | `[exists E, x == `|pr mu1 E - pr mu2 E|%R]].
End TV.

(* -------------------------------------------------------------------- *)
Definition is_path_metric {T : Type} (d : T -> T -> nat) :=
  [/\ forall x y, d x y = 0 -> x = y, forall x, d x x = 0
   & forall x z, 1 < d x z -> exists2 y, d x y = 1 & d x z = d x y + d y z]%N.

(* -------------------------------------------------------------------- *)
Section PathMetricTh.
Context {T : eqType} (d : T -> T -> nat).

Hypothesis ipm : is_path_metric d.

Lemma ipm_eq0 s1 s2 : (d s1 s2 == 0%N) = (s1 == s2).
Proof. by case: ipm=> h1 h2 _; apply/eqP/eqP=> [/h1|->]. Qed.
End PathMetricTh.

(* -------------------------------------------------------------------- *)
Section Lift.
Context {R : realType} (T : choiceType).

(* Should directly defined dlift with distr scalar multiplication *)
Definition mlift (f : T -> {distr T / R}) :=
  fun mu x => \E_[mu] (fun v => f v x).

Lemma isd_mlift f mu : isdistr (mlift f mu).
Proof. Admitted.

Definition dlift f mu := mkdistr (isd_mlift f mu).

Definition klift (f : T -> {distr T / R}) (k : nat) :=
  fun x : T => iter k (dlift f) (dunit x).
End Lift.

(* -------------------------------------------------------------------- *)
Section PathCoupling.
Context {R : realType} (T : choiceType).

Local Notation distr T := {distr T / R}.

Implicit Types (s : T) (mu : distr T).

Parameter d : T -> T -> nat.
Parameter D : nat.
Parameter f : T -> {distr T / R}.
Parameter F : T -> T -> distr (T * T).
Parameter b : R.

Hypothesis dpm :
  is_path_metric d.

Hypothesis diameter :
  forall s1 s2, (d s1 s2 <= D)%N.

Hypothesis F_cpl1 :
  forall s1 s2, d s1 s2 = 1%N -> iscoupling (f s1) (f s2) (F s1 s2).

Hypothesis F_esp1 :
  forall s1 s2, d s1 s2 = 1%N ->
    \E_[F s1 s2] (fun xy => (d xy.1 xy.2)%:R) < b * (d s1 s2)%:R.

Lemma pathE : forall s1 s2, `[exists p : seq T,
  [&& path [rel r1 r2 | d r1 r2 == 1%N] s1 p & last s1 p == s2]].
Proof.                          (* FIXME: break abstraction *)
move=> s1 s2; move: {2}(d s1 s2) (erefl (d s1 s2)) => [/eqP|l].
  by rewrite ipm_eq0 // => /eqP->; apply/existsbP; exists [::] => /=.
elim: l s1 s2 => [|l ih] s1 s2 => [eq1_d|eq_d].
  by apply/existsbP; exists [:: s2]; rewrite /= eq1_d !eqxx.
case: dpm => _ _ /(_ s1 s2); rewrite eq_d => -[] // x eq1 eq2.
have /eqP: d x s2 == l.+1 by rewrite -eqSS eq2 eq1 add1n.
move/ih=> /existsbP[p] /andP[ih1 ih2]; apply/existsbP.
by exists (x :: p) => /=; rewrite eq1 eqxx /= ih1 ih2.
Qed.

Fixpoint Fx_r s (p : seq T) :=
  match p with
  | [::]    => mkdistrd (fun r => (r.1 == r.2)%:R * f s r.1)
  | [:: s'] => F s s'
  | s' :: p =>
      let (mu1, mu2) := (F s s', Fx_r s' p) in
      mkdistrd (fun r => psum (fun v =>
        (mu1 (r.1, v) * mu2 (v, r.2)) / f s' v))
  end.

Definition Fx s1 s2 :=
  let p := xchooseb (pathE s1 s2) in Fx_r s1 p.

Definition Fxk k r1 r2 := klift (fun r => Fx r.1 r.2) k (r1, r2).

Goal forall s1 s2 k, tv (klift f k s1) (klift f k s2) < b^+k * D%:R.
Proof. Admitted.

End PathCoupling.

(* -------------------------------------------------------------------- *)
