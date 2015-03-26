
Lemma ge_sup_ub E x : has_ub E -> sup E <= x -> ub E x.
Proof. by move/sup_ub=> ubE leEx y /ubE leyE; apply: leR_trans leEx. Qed.

Lemma leR_total x1 x2 : x1 <= x2 \/ x2 <= x1.
Proof.
pose E y := x2 = y; have ubE: (Real.has_sup E) by (split; exists x2) => [|x <-].
have [[y <-] | leEx1] := sup_total x1 ubE; first by left.
by right; apply: leR_trans leEx1; apply: sup_ub => //; exists x2 => x <-.
Qed.

Lemma eqR_le2 x1 x2 : x1 == x2 <-> x1 <= x2 <= x1. Proof. by []. Qed.

Lemma eqR_le x1 x2 : x1 == x2 -> x1 <= x2. Proof. by case. Qed.

Lemma gtR_neq x1 x2 : x2 < x1 -> x1 != x2. Proof. by move=> ? /eqR_le. Qed.

Lemma ltR_neq x1 x2 : x1 < x2 -> x1 != x2.
Proof. by rewrite /eqR; tauto. Qed.

Lemma ltR_total x1 x2 : x1 != x2 -> x1 < x2 \/ x2 < x1.
Proof. by have:= leR_total x1 x2; rewrite /eqR; tauto. Qed.

Lemma ltRW x1 x2 : x1 < x2 -> x1 <= x2.
Proof. by case: (leR_total x1 x2). Qed.
Hint Resolve ltRW.

Lemma leR_lt_trans x1 x2 x3 : x1 <= x2 -> x2 < x3 -> x1 < x3.
Proof. by move=> lex12 ltx23 lex31; case: ltx23; apply: leR_trans lex12. Qed.

Lemma ltR_le_trans x1 x2 x3 : x1 < x2 -> x2 <= x3 -> x1 < x3.
Proof. by move=> ltx12 lex23 lex31; case: ltx12; apply: leR_trans lex31. Qed.

Lemma ltR_trans x1 x2 x3 : x1 < x2 -> x2 < x3 -> x1 < x3.
Proof. by move=> ltx12; apply: leR_lt_trans; apply: ltRW. Qed.

(**********************************************************)
(**      The setoid structure                             *)
(**********************************************************)

Lemma eqR_refl x : x == x. Proof. by []. Qed.
Hint Resolve eqR_refl.

Lemma eqR_congr x y : x = y -> x == y. Proof. by move->. Qed.

Lemma eqR_sym x1 x2 : x1 == x2 -> x2 == x1. Proof. by case. Qed.
Hint Immediate eqR_sym.

Lemma eqR_trans x1 x2 x3 : x1 == x2 -> x2 == x3 -> x1 == x3.
Proof.
by move=> [lex12 lex21] [lex23 lex32]; split; eapply leR_trans; eauto.
Qed.

Add Parametric Relation : Rtype eqR
  reflexivity proved by eqR_refl
  symmetry proved by eqR_sym
  transitivity proved by eqR_trans
  as real_model_equality.

Add Parametric Morphism : (@Real.le R) with
  signature eqR ==> eqR ==> iff as leR_morphism.
Proof.
move: leR_trans => le_tr x1 y1 [lexy1 leyx1] x2 y2 [lexy2 leyx2]; split; eauto.
Qed.

(**********************************************************)
(**       Addition                                        *)
(**********************************************************)

Lemma addRC x1 x2 : x1 + x2 == x2 + x1.
Proof. exact: (Real.add_commutative R). Qed.

Add Parametric Morphism : (@Real.add R) with
  signature eqR ==> eqR ==> eqR as addR_morphism.
Proof.
move=> x1 y1 Dx1 x2 y2 Dx2; apply: (@eqR_trans _ (x1 + y2)).
  by case: Dx2; split; apply: (Real.add_monotone R).
by rewrite -!(addRC y2); case: Dx1; split; apply: (Real.add_monotone R).
Qed.

Lemma addRA x1 x2 x3 : x1 + (x2 + x3) == x1 + x2 + x3.
Proof. exact: (Real.add_associative R). Qed.

Lemma addRCA x1 x2 x3 : x1 + (x2 + x3) ==  x2 + (x1 + x3).
Proof. by rewrite !addRA (addRC x1). Qed.

Lemma addRAC x1 x2 x3 : x1 + x2 + x3 ==  x1 + x3 + x2.
Proof. by rewrite -!addRA (addRC x2). Qed.

Lemma add0R x : 0 + x == x.
Proof. exact: (Real.add_zero_left R). Qed.

Lemma addR0 x : x + 0 == x.
Proof. by rewrite addRC add0R. Qed.

Lemma subRR x : x - x == 0.
Proof. exact: (Real.add_opposite_right R). Qed.

Lemma addRK x1 x2 : x1 + x2 - x2 == x1.
Proof. by rewrite -addRA subRR addR0. Qed.

Lemma subRK x1 x2 : x1 - x2 + x2 == x1.
Proof. by rewrite addRAC addRK. Qed.

Lemma addKR x1 x2 : - x1 + (x1 + x2) == x2.
Proof. by rewrite addRCA addRA subRR add0R. Qed.

Lemma addRI x x1 x2 : x + x1 == x + x2 -> x1 == x2.
Proof. by move=> Ex12; rewrite -(addKR x x1) Ex12 addKR. Qed.

Lemma addIR x x1 x2 : x1 + x == x2 + x -> x1 == x2.
Proof. by rewrite -!(addRC x); apply: addRI. Qed.

Lemma oppRK x : - - x == x.
Proof. by apply: (@addIR (- x)); rewrite addRC !subRR. Qed.

Lemma oppRD x1 x2 : - (x1 + x2) == - x1 - x2.
Proof.
by apply: (@addRI (x1 + x2)); rewrite subRR addRCA addRK addRC subRR.
Qed.

Lemma oppRB x1 x2 : - (x1 - x2) == x2 - x1.
Proof. by rewrite oppRD oppRK addRC. Qed.

Lemma oppR0 : - (0 : R) == 0.
Proof. by apply: (@addRI 0); rewrite subRR add0R. Qed.

Lemma leR_add2l x x1 x2 : x + x1 <= x + x2 <-> x1 <= x2.
Proof.
split=> lex12; last exact: (Real.add_monotone R).
by rewrite -(addKR x x1) -(addKR x x2); apply: (Real.add_monotone R).
Qed.

Lemma leR_add2r x x1 x2 : x1 + x <= x2 + x <-> x1 <= x2.
Proof. by rewrite -!(addRC x); apply: leR_add2l. Qed.

Lemma subR_ge0 x1 x2 : 0 <= x2 - x1 <-> x1 <= x2.
Proof. by rewrite -(leR_add2r x1) subRK add0R. Qed.

Lemma subR_le0 x1 x2 : x1 - x2 <= 0 <-> x1 <= x2.
Proof. by rewrite -subR_ge0 oppRB add0R subR_ge0. Qed.

Lemma leR_opp2 x1 x2 : - x1 <= - x2 <-> x2 <= x1.
Proof. by rewrite -subR_ge0 oppRK addRC subR_ge0. Qed.

Lemma oppR_inj x1 x2 : - x1 == - x2 -> x1 == x2.
Proof. by rewrite /eqR !leR_opp2 => /eqR_sym. Qed.

Add Parametric Morphism : (@Real.opp R) with
  signature eqR ==> eqR as oppR_morphism.
Proof. by move=> x y Exy; apply: oppR_inj; rewrite !oppRK. Qed.

(**********************************************************)
(**       Multiplication                                  *)
(**********************************************************)

Lemma mulRC x1 x2 : x1 * x2 == x2 * x1.
Proof. exact: (Real.mul_commutative R). Qed.

Lemma mulRDr x x1 x2 : x * (x1 + x2) == x * x1 + x * x2.
Proof. exact: (Real.mul_distributive_right R). Qed.

Lemma mulRDl x x1 x2 : (x1 + x2) * x == x1 * x + x2 * x.
Proof. by rewrite -!(mulRC x) -mulRDr. Qed.

Add Parametric Morphism : (@Real.mul R) with
  signature eqR ==> eqR ==> eqR as mulR_morphism.
Proof.
have posMr x x1 x2 : 0 <= x -> x1 == x2 -> x * x1 == x * x2.
  by move=> pos_x [lex12 lex21]; split; apply: (Real.mul_monotone R).
suffices allMr x x1 x2: x1 == x2 -> x * x1 == x * x2.
  by move=> x1 y1 /allMr Dx1 x2 y2 /allMr->; rewrite -!(mulRC y2) Dx1.
case: (leR_total 0 x) => [x_ge0 | x_le0] /posMr Dx1; first exact: Dx1.
have{x_le0} nx_ge0: 0 <= - x by rewrite -oppR0 leR_opp2.
by apply: (@addIR (- x * x1)); rewrite !(=^~ mulRDl, Dx1) ?subRR.
Qed.

Lemma mulRA x1 x2 x3 : x1 * (x2 * x3) == x1 * x2 * x3.
Proof. exact: (Real.mul_associative R). Qed.

Lemma mulRCA x1 x2 x3 : x1 * (x2 * x3) == x2 * (x1 * x3).
Proof. by rewrite !mulRA (mulRC x1). Qed.

Lemma mulRAC x1 x2 x3 : x1 * x2 * x3 == x1 * x3 * x2.
Proof. by rewrite -!mulRA (mulRC x2). Qed.

Lemma mul0R x : 0 * x == 0.
Proof. by apply (@addRI (0 * x)); rewrite -mulRDl !addR0. Qed.

Lemma mulR0 x : x * 0 == 0.
Proof. by rewrite mulRC mul0R. Qed.

Lemma mulRN x1 x2 : x1 * - x2 == - (x1 * x2).
Proof. by apply (@addRI (x1 * x2)); rewrite -mulRDr !subRR mulR0. Qed.

Lemma mulNR x1 x2 : - x1 * x2 == - (x1 * x2).
Proof. by rewrite mulRC mulRN mulRC. Qed.

Lemma mul1R x : 1 * x == x.
Proof. exact: (Real.mul_one_left R). Qed.

Lemma mulR1 x : x * 1 == x.
Proof. by rewrite mulRC mul1R. Qed.

Lemma mul2R x : 2 * x == x + x.
Proof. by rewrite mulRDl !mul1R. Qed.

Lemma mulN1R x : - 1 * x == - x.
Proof. by rewrite mulNR mul1R. Qed.

Lemma mulRN1 x : x * - 1 == - x.
Proof. by rewrite mulRN mulR1. Qed.

(* Properties of 1 (finally!) *)

Lemma neqR10 : (1 : R) != 0.
Proof. exact: (Real.one_nonzero R). Qed.

Lemma ltR01 : (0 : R) < 1.
Proof.
case/ltR_total: neqR10 => // lt10 le10; case: lt10.
have{le10} le0N1: (0 : R) <= -1 by rewrite -oppR0 leR_opp2.
by have:= Real.mul_monotone R le0N1 le0N1; rewrite mulR0 mulN1R oppRK.
Qed.
Hint Resolve ltR01.

Lemma ltRS x : x < x + 1.
Proof. by rewrite -subR_le0 (addRC x) addRK. Qed.
Implicit Arguments ltRS [].

Lemma ltPR x : x - 1 < x.
Proof. by rewrite -subR_le0 oppRB addRCA subRR addR0. Qed.
Implicit Arguments ltPR [].

Lemma ltR02 : (0 : R) < 2.
Proof. exact: ltR_trans ltR01 (ltRS _). Qed.
Hint Resolve ltR02.

(* Division (well : mostly inverse) *)

Lemma divRR x : x != 0 -> x / x == 1.
Proof. exact: (Real.mul_inverse_right R). Qed.

Lemma pmulKR x x1 : x > 0 -> x^-1 * (x * x1) == x1.
Proof. by move=> /gtR_neq-x_nz; rewrite mulRCA mulRA (divRR x_nz) mul1R. Qed.

Lemma pmulRI x x1 x2 : x > 0 -> x * x1 == x * x2 -> x1 == x2.
Proof. by move=> x_gt0 Dx1; rewrite -(pmulKR x1 x_gt0) Dx1 pmulKR. Qed.

Lemma pmulIR x x1 x2 : x > 0 -> x1 * x == x2 * x -> x1 == x2.
Proof. by rewrite -!(mulRC x); apply: pmulRI. Qed.

Local Notation leMl x_gt0 := (Real.mul_monotone R (ltRW x_gt0)).

Lemma invR_gt0 x : x > 0 -> x^-1 > 0.
Proof.
by move=> x_gt0 /(leMl x_gt0); rewrite (divRR (gtR_neq x_gt0)) mulR0 => /ltR01.
Qed.

Lemma leR_pmul2l x x1 x2 : x > 0 -> (x * x1 <= x * x2 <-> x1 <= x2).
Proof.
move=> x_gt0; have [/pmulKR-mxK x1_gt0] := (x_gt0, invR_gt0 x_gt0).
by split=> lex12; first rewrite -(mxK x1) -(mxK x2); apply: (leMl _) lex12.
Qed.

Lemma leR_pmul2r x x1 x2 : x > 0 -> (x1 * x <= x2 * x <-> x1 <= x2).
Proof. by move=> x_gt0; rewrite -!(mulRC x); apply: leR_pmul2l x_gt0. Qed.

Lemma pmulR_rle0 x1 x2 : x1 > 0 -> (x1 * x2 <= 0 <-> x2 <= 0).
Proof. by move=> x1_gt0; rewrite -(leR_pmul2l x2 0 x1_gt0) mulR0. Qed.

Lemma mulR_gt0 x1 x2 : x1 > 0 -> x2 > 0 -> x1 * x2 > 0.
Proof. by move=> x1gt0 /(pmulR_rle0 _ x1gt0). Qed.

Lemma mulRI x x1 x2 : x != 0 -> x * x1 == x * x2 -> x1 == x2.
Proof.
case/ltR_total=> [x_lt0 /oppR_morphism | x_gt0]; last exact: pmulRI.
by rewrite -!mulNR; apply: pmulRI; rewrite -leR_opp2 oppR0 oppRK.
Qed.

Lemma mulIR x x1 x2 : x != 0 -> x1 * x == x2 * x -> x1 == x2.
Proof. by rewrite -!(mulRC x); apply: mulRI. Qed.

(* The inverse is only a partial morphism. It might be worth fixing, say,     *)
(* 1/0 = 0 in order to make setoid rewriting work better.                     *)

Lemma invR_morphism x y : x != 0 -> x == y -> x^-1 == y^-1.
Proof.
move=> nz_x Dx; have Hy: y != 0 by rewrite -Dx.
by apply: (mulRI nz_x); rewrite divRR // Dx divRR.
Qed.

Lemma invR1 : (1^-1 : R) == 1.
Proof. by move: (divRR neqR10); rewrite mul1R. Qed.

Lemma invR_pmul x1 x2 : x1 > 0 -> x2 > 0 -> (x1 * x2)^-1 == x1^-1 / x2.
Proof.
move=> x1gt0 x2gt0; apply: (pmulRI x1gt0); rewrite mulRCA pmulKR //.
apply: (pmulRI x2gt0); rewrite mulRCA mulRA.
by rewrite !divRR //; apply: gtR_neq; rewrite // -(mulR0 x1) leR_pmul2l.
Qed.

Lemma invRN x : x != 0 -> (- x)^-1 == - x^-1.
Proof.
move=> nz_x; apply: (mulRI nz_x); apply: oppR_inj.
by rewrite -mulNR mulRN oppRK !divRR // -oppR0 => /oppR_inj.
Qed.

Lemma leR_pinv2 x1 x2 : x1 > 0 -> x2 > 0 -> (x1^-1 <= x2^-1 <-> x2 <= x1).
Proof.
move=> x1gt0 x2gt0; rewrite -(leR_pmul2r _ _ x1gt0).
by rewrite -(leR_pmul2r _ _ x2gt0) -!mulRA pmulKR // (mulRC x1) pmulKR.
Qed.

Lemma invR_neq0 x : x != 0 -> x^-1 != 0.
Proof. by move=> nz_x vx0; case: neqR10; rewrite -(divRR nz_x) vx0 mulR0. Qed.

Lemma invRK x : x != 0 -> x^-1^-1 == x.
Proof.
move=> nz_x; have nz_vx := invR_neq0 nz_x.
by apply: (mulIR nz_vx); rewrite mulRC !divRR.
Qed.

(**********************************************************)
(**      The least upper bound and derived operations.    *)
(**********************************************************)

Lemma sup_le_ub E x : Real.nonempty E -> Real.ub E x -> sup E <= x.
Proof.
move=> hasE leEx; set y := sup E; pose z := (x + y) / 2.
have Dz: 2 * z == x + y by rewrite /z mulRA mulRC (pmulKR _ ltR02).
have ubE: Real.has_sup E by split; last by exists x.
have [[t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(leR_add2l x) -Dz -(mul2R x) leR_pmul2l //.
  exact/(leR_trans lezt)/leEx.
by rewrite -(leR_add2r y) -Dz -(mul2R y) leR_pmul2l.
Qed.

Lemma sup_sup E : Real.has_sup E -> forall x, Real.ub E x <-> sup E <= x.
Proof.
by case=> hasE ubE x; split; [apply: sup_le_ub | apply: ge_sup_ub].
Qed.



(* Partial morphism property of the sup function; similarly to 1/0,   *)
(* it might be helpful to define (sup [_]True) and (sup [_]False).  *)

Lemma sup_morphism E :
  Real.has_sup E -> forall F, (forall x, E x <-> F x) -> sup E == sup F.
Proof.
case=> neE ubE F /all_and2[sEF sFE].
have neF: Real.nonempty F by have [x /sEF-Fx] := neE; exists x.
wlog suffices leFE: E F ubE {neE sEF} neF sFE / sup F <= sup E.
  by split; apply: leFE => //; have [y leEy] := ubE; exists y => x /sFE/leEy.
by apply: sup_le_ub => // x /sFE-Ex; apply: sup_ub.
Qed.

Lemma nonempty_Rdown E : Real.nonempty (Real.down E) <-> Real.nonempty E.
Proof. by split=> [[_ [x Ex _]] | [x Ex]]; do 2?exists x. Qed.

Lemma has_ub_Rdown E : Real.has_ub (Real.down E) <-> Real.has_ub E.
Proof.
split=> -[x ubEx]; exists x; first by move=> y Ey; apply ubEx; exists y.
by move=> z [y /ubEx-leyx lezy]; apply: leR_trans lezy leyx.
Qed.

Lemma has_sup_Rdown E : Real.has_sup (Real.down E) <-> Real.has_sup E.
Proof. by rewrite /Real.has_sup nonempty_Rdown has_ub_Rdown. Qed.

Lemma sup_Rdown E : Real.has_sup E -> sup (Real.down E) == sup E.
Proof.
move=> supE; split; apply/sup_sup=> //; first exact/has_sup_Rdown.
  by move=> z [y Ey lezy]; apply/(leR_trans lezy)/sup_ub; case: supE.
by move=> y Ey; apply/sup_ub; [case/has_sup_Rdown: supE | exists y].
Qed.

(* Definition by nondeterministic cases.                        *)

Section PickCases.

Variables (P1 P2 : Prop) (x1 x2 : R).
Hypotheses (defined : P1 \/ P2) (unambiguous : P1 /\ P2 -> x1 == x2).

Inductive pickR_spec : R -> Prop :=
  PickRSpec y of pickR_set P1 P2 x1 x2 y : pickR_spec y.

Lemma pickR_cases : pickR_spec (select {x1 if P1, x2 if P2}).
Proof.
pose E := pickR_set P1 P2 x1 x2; set x := select {x1 if P1, x2 if P2}.
have [x3 Ex3 Dx3]: exists2 x3, E x3 & forall y, E y <-> y == x3.
  by case: defined => havePi; [ exists x1; try split; try by left; split
                              | exists x2; try split; try by right; split];
     case; case=> Hpj Dy //; apply: (eqR_trans Dy); do 2![auto; apply eqR_sym].
have le_E_x3: Real.ub E x3 by move=> x4; rewrite (Dx3 x4) => ->.
split; rewrite -/E (Dx3 x).
by split; [apply: sup_le_ub | apply: sup_ub]; try exists x3.
Qed.

End PickCases.

Section PickRMorphism.

Variables (P1 P2 : Prop) (x1 x2 : R).
Hypotheses (defined : P1 \/ P2) (unambiguous : P1 /\ P2 -> x1 == x2).

Lemma pickR_morphism Q1 Q2 y1 y2 :
   (P1 <-> Q1) -> (P2 <-> Q2) -> x1 == y1 -> x2 == y2 ->
  select {x1 if P1, x2 if P2} == select {y1 if Q1, y2 if Q2}.
Proof.
move=> DP1 DP2 Dx1 Dx2; have Qdef: Q1 \/ Q2 by rewrite -DP1 -DP2.
have Quniq: Q1 /\ Q2 -> y1 == y2 by rewrite -DP1 -DP2 -Dx1 -Dx2.
case: pickR_cases => // x; case: pickR_cases => // y.
rewrite /pickR_set -DP1 -DP2 -Dx1 -Dx2.
by case; case=> HPi ->; case; case=> HPj ->; do 2![auto; apply: eqR_sym].
Qed.

End PickRMorphism.

(* min and max.                                                         *)

Section MinMaxReal.

Variable x1 x2 : R.

Let Hx12 := leR_total x1 x2.
Let Ex12 (eq_x : x1 <= x2 <= x1) := eq_x : x1 == x2.
Let Ex21 (eq_x : x1 <= x2 <= x1) := eqR_sym eq_x.

Lemma leR_minl : min x1 x2 <= x1.
Proof. by rewrite /min; case: (pickR_cases Hx12 Ex12) => x3 [] [le_x ->]. Qed.

Lemma leR_minr : min x1 x2 <= x2.
Proof. by rewrite /min; case: (pickR_cases Hx12 Ex12) => x3 [] [le_x ->]. Qed.
Hint Resolve leR_minl leR_minr.

Lemma ltR_min x : x < min x1 x2 <-> x < x1 /\ x < x2.
Proof.
rewrite /min; case: (pickR_cases Hx12 Ex12) => x3.
by case=> [] [le_x ->]; split=> [|[]] //; split=> //; apply: ltR_le_trans le_x.
Qed.

Lemma leR_min x : x <= min x1 x2 <-> x <= x1 /\ x <= x2.
Proof.
split=> [|[lex1 lex2]]; first by split; eapply leR_trans; eauto.
by rewrite /min; case: (pickR_cases Hx12 Ex12) => x3 [] [le_x ->].
Qed.

Lemma leR_maxl : x1 <= max x1 x2.
Proof. by rewrite /max; case: (pickR_cases Hx12 Ex21) => x3 [] [ge_x ->]. Qed.

Lemma leR_maxr : x2 <= max x1 x2.
Proof. by rewrite /max; case: (pickR_cases Hx12 Ex21) => x3 [] [ge_x ->]. Qed.
Hint Resolve leR_maxl leR_maxr.

Lemma ltR_max x : max x1 x2 < x <-> x1 < x /\ x2 < x.
Proof.
rewrite /max; case: (pickR_cases Hx12 Ex21) => x3.
by case=> -[ge_x ->]; split=> [|[]] //; split=> //; apply: (leR_lt_trans ge_x).
Qed.

Lemma leR_max x : max x1 x2 <= x <-> x1 <= x /\ x2 <= x.
Proof.
split=> [|[gex1 gex2]]; first by split; eapply leR_trans; eauto.
by rewrite /max; case: (pickR_cases Hx12 Ex21) => x3 [] [ge_x ->].
Qed.

End MinMaxReal.

Add Parametric Morphism : (@min R) with
  signature eqR ==> eqR ==> eqR as min_morphism.
Proof.
by move=> x1 y1 Dx1 x2 y2 Dx2; apply: pickR_morphism => //;
 try apply leR_total; rewrite Dx1 Dx2; split.
Qed.

Add Parametric Morphism : (@max R) with
  signature eqR ==> eqR ==> eqR as max_morphism.
Proof.
by move=> x1 y1 Dx1 x2 y2 Dx2; apply: pickR_morphism => //;
 try apply leR_total; by [rewrite Dx1 Dx2 | move/eqR_sym].
Qed.

(**********************************************************)
(** Properties of the injections from N, Z, and Q into R  *)
(**********************************************************)

Lemma intRS n : n.+1 == n + 1.
Proof. by case: n => [|n] /=; rewrite ?add0R // addRC. Qed.

Lemma ltR0Sn n : 0 < n.+1.
Proof.
by elim: n => // n IHn; apply: ltR_trans IHn _; rewrite /= addRC; apply: ltRS.
Qed.
Implicit Arguments ltR0Sn [].

Lemma leR0n n : 0 <= n.
Proof. by case: n => // n; apply/ltRW/ltR0Sn. Qed.
Hint Resolve ltR0Sn leR0n.

Lemma intRN m : (- m)%R == - m.
Proof. by case: m => [[|n]|n]; rewrite ?oppR0 ?oppRK. Qed.

Lemma intRD1 m : (m + 1)%R == m + 1.
Proof.
case: m => [n|[|n]]; [by rewrite addrC intRS | by rewrite addRC subRR |].
by rewrite /= subn1 oppRD addRAC -addRA addKR.
Qed.

Lemma intRD m1 m2 : (m1 + m2)%R == m1 + m2.
Proof.
suffices intRDn m n: (m + n)%R == m + n.
  by case: m2 => // n; rewrite -[m1]opprK NegzE -opprD !(intRN, intRDn) oppRD.
elim: n => [|n IHn]; first by rewrite addr0 addR0.
by rewrite -addn1 PoszD addrA !intRD1 IHn addRA.
Qed.

Lemma intRB m1 m2 : (m1 - m2)%R == m1 - m2.
Proof. by rewrite intRD intRN. Qed.

Lemma intRB1 m : (m - 1)%R == m - 1.
Proof. exact: intRB. Qed.

Lemma intRM m1 m2 : (m1 * m2)%R == m1 * m2.
Proof.
suffices intMn m n: (m * n)%R == m * n.
  by case: m2 => n; rewrite ?NegzE ?mulrN ?intRN ?mulRN intMn.
rewrite -mulrzz -pmulrn; elim: n => [|n IHn]; first by rewrite mulR0.
by rewrite mulrS (PoszD 1%N) !intRD mulRDr mulR1 -IHn.
Qed.

Lemma intR_addbit m : m == (m %% 2%N)%Z + 2 * (m %/ 2%N)%Z.
Proof. by rewrite {1}(divz_eq m 2%:Z) mulRC addRC intRD intRM. Qed.

Lemma intR_leP m1 m2 : reflect (m1 <= m2) (m1 <= m2)%R.
Proof.
apply: (equivP idP); rewrite -subr_ge0 -subR_ge0 -intRB.
by case: (m2 - m1)%R => n; split; rewrite // -oppR0 leR_opp2 => /ltR0Sn.
Qed.

Lemma intR_ltP m1 m2 : reflect (m1 < m2) (m1 + 1 <= m2)%R.
Proof. by rewrite lez_addr1 ltrNge; apply: (iffP idP) => /intR_leP. Qed.

(* Embedding the rationals.                                                  *)

Lemma ratRE a : ratRR a == numq a / denq a.
Proof.
by rewrite /ratRR /ratR unfold_in; case: eqP => // ->; rewrite invR1 mulR1.
Qed.

Lemma ratR_eq a : {r | a = (r.1%:Q / r.2.+1%:Q)%R & a * r.2.+1 == r.1}.
Proof.
have [d Dd] := denqP a; exists (numq a, d); rewrite -Dd ?divq_num_den //=.
by rewrite ratRE mulRAC mulRC (mulRC (numq a)) pmulKR ?Dd.
Qed.

Lemma ratR_leP a1 a2 : reflect (a1 <= a2) (a1 <= a2)%R.
Proof.
have [[r1 {3}-> Dr1] [r2 {3}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
rewrite ler_pdivl_mulr ?ltr0Sn // mulrAC ler_pdivr_mulr ?ltr0Sn //.
rewrite -!intrM ler_int /=; apply: (equivP (intR_leP _ _)).
by rewrite !intRM -Dr1 -Dr2 mulRAC !leR_pmul2r.
Qed.

Lemma ratR_ltP a1 a2 : reflect (a1 < a2) (a1 < a2)%R.
Proof. by rewrite ltrNge; apply: (iffP idP) => /ratR_leP. Qed.

Lemma ratR_lt0P a : reflect (0 < a) (0 < a)%R. Proof. exact: (ratR_ltP 0). Qed.

Lemma ratRz m : m%:Q = m :> R.
Proof. by rewrite /ratRR /ratR rpred_int numq_int. Qed.

Lemma ratR0 : 0%:Q = 0 :> R. Proof. by []. Qed.
Lemma ratR1 : 1%:Q = 1 :> R. Proof. by []. Qed.
Lemma ratR2 : 2%:Q = 2 :> R. Proof. by []. Qed.

Lemma ratRN a : (- a)%R == - a.
Proof. by rewrite !ratRE numqN denqN intRN mulNR. Qed.

Lemma ratRMn a n : (a * n%:Q)%R == a * n.
Proof.
have [[r1 Da Dr1] [r2 Dan Dr2]] := (ratR_eq a, ratR_eq (a * n%:Q)).
apply/(pmulIR (ltR0Sn r2.2))/(pmulIR (ltR0Sn r1.2)).
rewrite {}Dr2 -2!(mulRAC _ r1.2.+1) {}Dr1 -!intRM -!ratRz !intrM.
apply/eqR_congr/(congr1 ratRR)/(canRL (divfK _)); first by rewrite intr_eq0.
by rewrite mulrAC -{}Dan {}Da  mulrAC divfK ?intr_eq0.
Qed.

Lemma ratRD a1 a2 : (a1 + a2)%R == a1 + a2.
Proof.
have [[r1 {2}-> Dr1] [r2 {2}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
apply/(pmulIR (ltR0Sn r2.2))/(pmulIR (ltR0Sn r1.2)).
rewrite !mulRDl (mulRAC a1) Dr1 Dr2 -!ratRMn !mulrDl mulrAC !divfK ?intr_eq0 //.
by rewrite -!intrM -intrD ratRz intRD !intRM.
Qed.

Lemma ratRM a1 a2 : (a1 * a2)%R == a1 * a2.
Proof.
have [[r1 {2}-> Dr1] [r2 {2}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
apply/(pmulIR (ltR0Sn r1.2))/(pmulIR (ltR0Sn r2.2)).
rewrite -2!ratRMn (mulRAC a1) -mulRA {}Dr1 {}Dr2 -mulrA mulrACA.
by rewrite !divfK ?intr_eq0 // -intrM ratRz intRM.
Qed.

Lemma ratR_pinv a : (0 < a)%R -> a^-1%R == a^-1.
Proof.
move=> a_gt0; have aR_gt0: 0 < a by rewrite -ratR0; apply/ratR_ltP.
apply: (pmulIR aR_gt0); rewrite -ratRM mulRC (divRR (gtR_neq aR_gt0)).
by rewrite mulVf ?ratR1 ?gtr_eqF.
Qed.

(* The floor function                                                   *)

Fact ub_floor_set x : Real.ub (floor_set x) x.
Proof. by move=> y [m]. Qed.
Hint Resolve ub_floor_set.

Fact has_ub_floor_set x : Real.has_ub (floor_set x).
Proof. by exists x. Qed.
Hint Resolve has_ub_floor_set.

Let has_floor_max x : Real.nonempty (floor_set x) -> x < floor x + 1.
Proof.
move=> has_x0 le_x1x; have supE: Real.has_sup (floor_set x) by [].
have inc_lex m (lemx : m <= x): (m + 1)%R <= x.
  by apply: leR_trans le_x1x; rewrite intRD1 leR_add2r; apply: sup_ub.
have [[_ [m]] | ] := sup_total (floor x - 1) supE; last exact: ltPR.
do 2!move/inc_lex; rewrite -/intRR -{2}[m](addrK 1%R) intRB1 leR_add2r => lem2x.
by case/leR_lt_trans/(_ (ltRS _)); rewrite -intRD1; apply: sup_ub.
Qed.

Fact nonempty_floor_set x : Real.nonempty (floor_set x).
Proof.
have [le0x | lex0] := leR_total 0 x; first by exists 0%N.
have ub_nx0: Real.has_sup (floor_set (- x)).
  by split=> //; exists 0%N; split; rewrite /= -oppR0 leR_opp2.
have [[_ [m _] lex1m] | /ltPR//] := sup_total (floor (- x) - 1) ub_nx0.
pose m1 := (m + 1)%R; pose m2 := (m1 + 1)%R.
exists (- m2)%R; split; move: lex1m; rewrite -/intRR -(addRK m 1) leR_add2r.
rewrite -{2}(oppRK x) intRN leR_opp2 -{2}(subRK (- x) 1) !intRD1 leR_add2r.
apply/leR_trans/ltRW; rewrite -(leR_add2r 1) subRK.
by apply: has_floor_max; case: ub_nx0.
Qed.
Hint Resolve nonempty_floor_set.

Lemma has_sup_floor_set x : Real.has_sup (floor_set x). Proof. by []. Qed.
Hint Resolve has_sup_floor_set.

Add Parametric Morphism : (@floor R) with
  signature eqR ==> eqR as floor_morphism.
Proof.
move=> x1 x2 Dx; apply: sup_morphism => // y.
by split=> [] [m lemx {y}]; split; apply: (leR_trans lemx); case: Dx.
Qed.

Add Parametric Morphism : (@range1 R) with
  signature eqR ==> eqR ==> iff as range1_morphism.
Proof. by move=> x1 y1 Dx1 x2 y2 Dx2; rewrite /range1 Dx1 Dx2. Qed.

Lemma range1_floor x : range1 (floor x) x.
Proof. by split; [apply: sup_le_ub | apply: has_floor_max]. Qed.

Lemma int_floor x : exists m : int, floor x == m.
Proof.
case: (range1_floor x); set y := floor x => leyx ltxy1; pose h2 : R := 2^-1.
have h2gt0: 0 < h2 by apply: invR_gt0.
have lty2y: y - h2 < y by rewrite -subR_ge0 addRC addKR -oppR0 leR_opp2.
have [[_ [m lemx] ley2m] | //] := sup_total (y - h2) (has_sup_floor_set x).
rewrite -/intRR in lemx ley2m; exists m; split; last exact: sup_ub.
pose m2 := m + h2; have leym2: y <= m2 by rewrite -(leR_add2r (- h2)) addRK.
apply: sup_le_ub => // _ [m1 lem1x]; rewrite -(leR_add2r 1) -!intRD1.
apply/intR_leP/intR_ltP; have:= h2gt0; rewrite -(leR_add2l m2) addR0.
rewrite -addRA -mul2R (divRR (gtR_neq ltR02)) -(intRD1 m).
exact/leR_lt_trans/(ge_sup_ub _ leym2).
Qed.

Lemma range1z_inj x m1 m2 : range1 m1 x -> range1 m2 x -> m1 = m2.
Proof.
move=> [m1x x_m1] [m2x x_m2].
wlog suffices: m1 m2 m1x {x_m1 m2x} x_m2 / (m1 <= m2)%R.
  by move=> IH; apply/eqP; rewrite eqr_le !IH.
rewrite -(ler_add2r 1); apply/intR_ltP.
by rewrite intRD1; eapply leR_lt_trans; eauto.
Qed.

Lemma range1zz m : range1 m m.
Proof. by split; rewrite // -intRD1; apply/intR_ltP. Qed.

Lemma range1z_floor m x : range1 m x <-> floor x == m.
Proof.
have floor1 m1 x1: floor x1 == m1 -> range1 m1 x1.
  by move=> <-; apply: range1_floor.
split=> [x1m | /floor1 //]; have [m1 Dm1] := int_floor x.
by rewrite -(range1z_inj (floor1 _ _ Dm1) x1m).
Qed.

Lemma floor_znat m : floor m == m.
Proof. by rewrite -(range1z_floor m m); apply: range1zz. Qed.

Lemma find_range1z x : exists m : int, range1 m x.
Proof.
by have [m Dm] := int_floor x; exists m; case: (range1z_floor m x); auto.
Qed.

Lemma ratR_dense x y : x < y -> exists2 a : rat, x < a & a < y.
Proof.
move=> ltxy; pose z := y - x; have z_gt0: z > 0 by rewrite subR_le0.
have [[d|n] [ledv ltvd1]] := find_range1z z^-1; last first.
  case: ltvd1; apply: ltRW; apply: leR_lt_trans (invR_gt0 z_gt0).
  by rewrite NegzE intRN intRS oppRD subRK -subR_ge0 add0R oppRK.
set d1 : R := d.+1; have d1gt0: d1 > 0 by exact: ltR0Sn.
have [m [lemx ltxm1]] := find_range1z (d1 * x).
exists ((m + 1)%:Q / d.+1%:Q)%R; rewrite -(leR_pmul2r _ _ d1gt0) -ratRMn.
  by rewrite divfK ?intr_eq0 // mulRC ratRz intRD1.
rewrite divfK ?intr_eq0 // ratRz intRD1.
rewrite -(addKR x y) addRC -addRA -/z mulRC mulRDr -(divRR (gtR_neq z_gt0)).
move: lemx; rewrite -(leR_add2r (d1 * z)); apply: ltR_le_trans.
by rewrite leR_add2l mulRC leR_pmul2l // /d1 intRS.
Qed.

(**********************************************************)
(*   The excluded middle, and lemmas that depend on       *)
(* explicit classical reasoning.                          *)
(**********************************************************)

Lemma reals_classic : excluded_middle.
Proof.
move=> P; pose E x := x = 0 \/ P /\ x = 2.
have ubE: Real.has_ub E by exists 2 => x [->|[_ ->]] //; apply: ltRW.
have supE: Real.has_sup E by split; first by exists 0; left.
have [ [x [-> /ltR01 // | []]] | leE1] := sup_total 1 supE; first by left.
right=> haveP; case: (ltRS 1); apply: leR_trans leE1.
by apply: sup_ub; last by right.
Qed.

(* Deciding comparisons. *)

Lemma leR_eqVlt x1 x2 : x1 <= x2 <-> x1 == x2 \/ x1 < x2.
Proof.
by rewrite /eqR; case: (reals_classic (x2 <= x1)) (leR_total x1 x2); tauto.
Qed.

Lemma ltR_neqAle x1 x2 : x1 < x2 <-> x1 != x2 /\ x1 <= x2.
Proof. by rewrite (leR_eqVlt x1 x2) /eqR; tauto. Qed.

(* Deciding definition by cases. *)

Lemma select_cases P x1 x2 :
  pickR_spec P (~ P) x1 x2 (select {x1 if P, else x2}).
Proof. by apply: pickR_cases; try tauto; apply: reals_classic. Qed.

Add Parametric Morphism : (@selectR R) with
  signature iff ==> eqR ==> eqR ==> eqR as selectR_morphism.
Proof.
move=> P Q DP x1 y1 Dx1 x2 y2 Dx2; apply: pickR_morphism; try tauto.
exact: reals_classic.
Qed.

End RealLemmas.

Implicit Arguments neqR10 [].
Implicit Arguments ltR01 [].
Implicit Arguments ltR02 [].
Implicit Arguments ltRS [R].
Implicit Arguments ltPR [R].
Implicit Arguments ltR0Sn [].
Implicit Arguments intR_leP [R m1 m2].
Implicit Arguments intR_ltP [R m1 m2].
Implicit Arguments ratR_leP [R a1 a2].
Implicit Arguments ratR_ltP [R a1 a2].
Prenex Implicits intR_leP intR_ltP ratR_leP ratR_ltP.

Existing Instance real_model_equality.
Existing Instance real_model_equality_Transitive.
Existing Instance real_model_equality_Symmetric.
Existing Instance real_model_equality_Reflexive.
Existing Instance real_model_equality_relation.
Existing Instance leR_morphism_Proper.
Existing Instance addR_morphism_Proper.
Existing Instance oppR_morphism_Proper.
Existing Instance mulR_morphism_Proper.
Existing Instance min_morphism_Proper.
Existing Instance max_morphism_Proper.
Existing Instance range1_morphism_Proper.
Existing Instance floor_morphism_Proper.
Existing Instance selectR_morphism_Proper.

