From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp fsbigop.
From mathcomp Require Import xfinmap constructive_ereal reals discrete realseq.
From mathcomp.classical Require Import classical_sets functions.
From mathcomp.experimental_reals Require Import realsum distr.
From mathcomp.analysis Require Import esum ereal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Reserved Notation "\Ee_[ mu ] f" (at level 2, format "\Ee_[ mu ]  f").

Section Esp.
  Context {R : realType} {T : choiceType}.

  Implicit Types (mu : {distr T / R}) (f : T -> \bar R).

  Definition espe  mu f := sum (fun x => mule (f x) ((mu x)%:E)).

  Notation "\Ee_[ mu ] f" := (espe mu f).
End Esp.

Section PrCoreTheory.
  Context {R : realType} {T : choiceType}.

  Implicit Types (mu : {distr T / R}) (A B E : pred T).

  Lemma exp_dunit (f : T -> \bar R) (x : T) :
    espe (dunit x) f = f x.
  Proof.
    rewrite /espe.
    rewrite (@eq_sum _ _ _ (fun y : T => if x == y then f y else 0%R)%E).
    + move => x0. rewrite dunit1E.
      by case (x == x0) => //=; rewrite ?mule1 ?mule0.
    by rewrite sum_unit.
  Qed.

  Lemma exp_cst mu r : (espe mu (fun _ => r) = (\P_[mu] predT)%:E * r)%E.
  Proof.
    rewrite pr_predT psum_sum /espe //.
    rewrite sumZ.
    - move => ?. rewrite lee_fin //.
    by rewrite sum_sum // muleC.
  Qed.

  Lemma exp0 mu : espe mu (fun _ => 0) = 0.
  Proof. by rewrite exp_cst mule0. Qed.

  Lemma exp_dlet {U: choiceType} mu (nu : T -> {distr U / R}) F :
    (forall x, 0%:E <= F x)%E ->
    espe (dlet nu mu) F = espe mu (fun x => espe (nu x) F).
  Proof.
    move => HF.
    have pos : (forall (i : T) (j : U), (0%R <= F j * ((mu i)%:E * (nu i j)%:E))%E).
    - move => i j; rewrite mule_ge0 //.
      by rewrite mule_ge0 // lee_tofin.
    rewrite /espe.
    rewrite (eq_sum
               (S1:=fun x : U => (F x * ((\dlet_(i <- mu) nu i) x)%:E)%E)
               (S2:=fun x : U => (F x * esum [set:T] (fun y : T => (mu y * nu y x)%:E)))%E).
    - move => x; rewrite dletE.
      congr ( _ * _)%E.
      rewrite -esum_psum //.
      - by move => i; rewrite mulr_ge0.
      - apply/(le_summable (F2 := mu)) => //.
        by move=> x0; rewrite mulr_ge0 //= ler_piMr ?le1_mu1.
    symmetry.
    rewrite (eq_sum
               (S1:=(fun x : T => (sum (fun x0 : U => F x0 * (nu x x0)%:E) * (mu x)%:E)%E))
               (S2:=(fun x : T => (esum [set:U] (fun x0 : U => F x0 * ((mu x)%:E * (nu x x0)%:E))%E)))).
    - move => x; rewrite muleC.
      rewrite -sumZ.
      - move => x1; rewrite mule_ge0 //=.
      - exact:  (ge0_mu (nu x) x1).
      rewrite (eq_sum
               (S1:=(fun x0 : U => (mu x)%:E * (F x0 * (nu x x0)%:E))%E)
               (S2:=(fun x0 : U => F x0 * ((mu x)%:E * (nu x x0)%:E))%E)) //.
      - by move => ?; rewrite muleCA.
    rewrite esum_sum' //.
    rewrite esum_sum'.
     - by move => ?; rewrite esum_ge0 //.
   rewrite esum_esum' //.
   rewrite esum_sum'.
   - move => ?; rewrite mule_ge0 // esum_ge0 //.
     by move => ??; rewrite  lee_tofin //  mulr_ge0.
   rewrite {1}(eq_esum
              (b:= fun x => (F x * (\esum_(y in [set: T]) (mu y * nu y x)%:E))%E)) //.
   - move => ??. rewrite esumZ //.
     by move => ?; rewrite  mule_ge0 // lee_tofin.
  Qed.

  (* Lemma expZ mu F c : \E_[mu] (c \*o F) = c * \E_[mu] F. *)
  (* Proof. by rewrite -sumZ; apply/eq_sum=> x /=; rewrite mulrA. Qed. *)

End PrCoreTheory.
