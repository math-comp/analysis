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
  [/\ forall x y, d x y = 0 -> x = y
   & forall x z, 1 < d x z -> exists2 y, d x z = 1 & d x y = d x z + d x y]%N.

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

Fixpoint Fx_r (n : nat) (s1 s2 : T) : {distr (T * T) / R} :=
  if n is n.+1 then
    match d s1 s2 with
    | 0 => mkdistrd (fun r => (r.1 == r.2)%:R * f s1 r.1)
    | 1 => F s1 s2
    | _ =>
       if @idP `[exists s, [&& d s1 s == 1 & d s1 s2 == d s1 s + d s s2]%N]
          is ReflectT Px
       then
         let s   := xchooseb Px in
         let mu1 := Fx_r n s1 s in
         let mu2 := Fx_r n s s2 in

         mkdistrd (fun r => psum (fun v =>
           (mu1 (r.1, v) * mu2 (v, r.2)) / f s v))

       else dnull
    end
  else dnull.

Definition Fx    s1 s2 := Fx_r D s1 s2.
Definition Fxk k r1 r2 := klift (fun r => Fx r.1 r.2) k (r1, r2).

Goal forall s1 s2 k, tv (klift f k s1) (klift f k s2) < b^+k * D%:R.
Proof. Admitted.

End PathCoupling.

(* -------------------------------------------------------------------- *)
