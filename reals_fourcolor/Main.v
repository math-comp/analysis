From HB Require Import structures.
From mathcomp Require Import reals all_ssreflect all_algebra lra.
From mathcomp Require Import classical_sets topology contra normedtype boolp functions.
Import Order.Theory Num.Theory GRing.Theory.
From fourcolor Require Import real realsyntax realcategorical realprop.
Import reals.

Record realModel := {
  R :> Real.model;
  eqR_is_eq : forall {x y: R}, Real.eq x y -> x = y ;
  inv00 : Real.eq (Real.inv (Real.zero R)) (Real.zero R);

  eqb := fun (x y: R) => asbool (Real.eq x y);
  leb := fun (x y: R) => asbool (Real.le x y);
    
  trunc: R -> nat;
  truncP : forall (x: R),
    if leb 0 x
    then ((Real.le (Real.nat _ (trunc x)) x) /\ (Real.lt x (Real.nat _ (trunc x).+1)))
    else (trunc x == 0);

  sup_adherent_subdef: forall (E : set R) (eps : R),
    (~~ leb eps 0) -> Real.has_sup E -> exists2 e : R, E e & (~~leb e (Real.sup E - eps));
}.
Arguments eqR_is_eq {_ _ _}.
Arguments inv00 {_}.
Arguments eqb {_}.
Arguments leb {_}.
Arguments trunc {_}.
Arguments truncP {_}.
Arguments sup_adherent_subdef {_}.

Section TtoM.
Open Scope ring_scope.

Variable (R: realType).

Definition map_structure : Real.structure := {|
  Real.val := R;
  Real.le := fun (x y: R) => x <= y;
  Real.sup := fun (S: R -> Prop) => reals.sup S;
  Real.add := fun (x y: R) => x + y;
  Real.zero := 0%R;
  Real.opp := fun (x: R) => (-x)%R;
  Real.mul := fun (x y: R) => x * y;
  Real.one := 1%R;
  Real.inv := fun (x: R) => x^-1;
|}.

Definition sets_correspondance : Real.set map_structure -> set R.
Proof. done. Defined.

Definition down_correspondance : forall S x,
    down (T:=R) (sets_correspondance S) x -> Real.down S x.
Proof. by move=> ? ? [y] [] ? ?; exists y. Defined.

Definition map_axioms : Real.axioms map_structure.
Proof.
unshelve econstructor;
rewrite /map_structure;
rewrite /Real.add /Real.mul /Real.opp /Real.inv /Real.zero /Real.one /Real.eq /Real.le;
do ?[move=> *; nra].
- by move=> ? ?; apply: sup_upper_bound.
- move=> S x has_sup.
  elim: (sup_total x has_sup); last by right.
  by left; apply: down_correspondance.
- by move=> x ne0; rewrite divff //; lra.
Defined.

Definition weakModel: Real.model := {|
  Real.model_structure := map_structure;
  Real.model_axioms := map_axioms;
|}.

Lemma req_is_eq_holds : forall (x y: weakModel), (x == y)%Rval -> x = y.
Proof.
rewrite /Real.eq /Real.le /=.
move=> ? ?; lra.
Defined.

Lemma natmul_correspondance : forall n, (Real.nat weakModel n) = GRing.natmul 1 n.
Proof.
case=> // n; rewrite /GRing.natmul iteropS.
elim: n => //= n <-.
by rewrite addrC.
Qed.

Definition map : realModel.
Proof.
unshelve econstructor.
- exact: weakModel.
- exact: Num.truncn.
- move=> ? ?; rewrite /Real.eq /Real.le /=.
  lra.
- rewrite /Real.inv /= invr0.
  rewrite /Real.eq /Real.le /=.
  by split.
- move=> x; rewrite asboolb.
  have := archimedean.Num.Theory.truncnP x.
  move: (orbN (0 <= x)) => /orP []; last by move=> /negPf ->.
  move=> -> /andP; rewrite -!natmul_correspondance.
  move=> [] ? ?; split=> //.
  by apply /negP; rewrite -real_ltNge ?num_real.
- move=> E eps /=.
  move=> /asboolPn /negP; rewrite /Real.le -real_ltNge ?num_real //.
  move=> eps_pos has_sup.
  elim: (reals.sup_adherent_subdef E eps eps_pos has_sup) => e inE isclose.
  exists e => //.
  by apply /asboolPn /negP; rewrite /Real.le -real_ltNge ?num_real.
Qed.
End TtoM.

Section MtoT.
Variable (R: realModel).
Open Scope ring_scope.

Lemma eqbP : forall (x y: R), reflect (x = y) (eqb x y).
Proof.
move=> x y; apply /(iffP idP).
- move=> /asboolP; exact: eqR_is_eq.
- move=> ->; apply /asboolP.
  exact: eqR_refl.
Qed.

HB.instance Definition _ := @hasDecEq.Build R eqb eqbP.

Definition eqRP (x y: R) : reflect (x == y)%real (x == y).
Proof. by apply /(iffP eqP)=> [->|/eqR_is_eq]. Qed.

Lemma eqR_eq (x y: R) : (x == y)%real <-> (x = y).
Proof. by split=> [/eqRP /eqP|->]. Qed.


HB.instance Definition _ := gen_choiceMixin R.


Definition zero : R := 0.

Definition add (x y: R) := (x + y)%real.

Definition opp (x: R) := (-x)%real.

Definition addrA : associative add.
Proof. move=> x y z; apply /eqR_eq; exact: (Real.add_associative R). Defined.

Definition addrC : commutative add.
Proof. move=> x y; apply /eqR_eq; exact: (Real.add_commutative R). Defined.

Definition add0r : left_id zero add.
Proof. move=> x; apply /eqR_eq; exact: (Real.add_zero_left R). Defined.

Definition addNr : left_inverse zero opp add.
Proof. move=> x; apply /eqR_eq; rewrite addrC; exact: (Real.add_opposite_right R). Defined.

HB.instance Definition _ := GRing.isZmodule.Build R addrA addrC add0r addNr.


Definition one : R := 1.

Definition mul (x y: R) := (x * y)%real.

Lemma mulrA: associative mul.
Proof. move=> x y z; apply /eqR_eq; exact: (Real.mul_associative R). Defined.

Lemma mulrC: commutative mul.
Proof. move=> x y; apply /eqR_eq; exact: (Real.mul_commutative R). Defined.

Lemma mul1r: left_id one mul.
Proof. move=> x; apply /eqR_eq; exact: (Real.mul_one_left R). Defined.

Lemma mulrDl : left_distributive mul add.
Proof.
move=> x y z; rewrite !(mulrC _ z).
apply /eqR_eq; exact: (Real.mul_distributive_right R).
Defined.

Lemma mul0r : left_zero zero mul.
Proof. move=> x; apply /eqR_eq; exact: realprop.mul0R. Defined.

Lemma oner_neq0 : (one != zero)%B.
Proof.
have := Real.one_nonzero R.
by move=> /eqR_eq; apply /contra_notN=> /eqP.
Defined.

HB.instance Definition _ := GRing.Nmodule_isComNzSemiRing.Build R mulrA mulrC mul1r mulrDl mul0r oner_neq0.


Definition unit : pred R := [pred x | x != zero].

Definition inv (x: R) := Real.inv x.

Lemma mulVr : {in unit, left_inverse one inv mul}.
Proof.
move=> x xU; apply /eqP.
rewrite mulrC; apply /eqP /eqR_eq.
apply: (Real.mul_inverse_right R _).
move: xU; rewrite inE.
by apply: contraNnot => /eqRP.
Qed.

Lemma unitPl : forall (x y: R), (y * x)%R = 1%R -> unit x.
Proof.
move=> x y; apply: contra_eq_neq => ->.
by rewrite mulr0 eq_sym oner_neq0.
Qed.

Definition invr_out : {in [predC unit], inv =1 id}.
Proof.
move=> x; rewrite !inE negbK=> /eqP ->.
apply /eqR_eq; exact: inv00.
Qed.

HB.instance Definition _ := @GRing.ComNzRing_hasMulInverse.Build R unit inv mulVr unitPl invr_out.


Definition mulf_eq0_subproof : forall x y : R, (x * y)%R = 0%R -> (x == 0%R) || (y == 0%R).
Proof.
move=> x y H; apply /orP.
have := orbN (y == 0)=> /orP []; first by right.
left; apply /eqRP /realprop.mulIR.
  apply /eqRP; exact: b.
by rewrite realprop.mul0R; apply /eqR_eq.
Qed.

HB.instance Definition _ := @GRing.ComUnitRing_isIntegral.Build R mulf_eq0_subproof.


Definition le (x y: R) := leb x y.

Definition lt (x y: R) := ~~ leb y x.

Definition lt_def : forall x y : R, lt x y = (y != x) && le x y.
Proof.
move=> x y.
apply /Bool.eq_iff_eq_true; split.
  move=> /asboolPn /ltR_neqAle [? ?]; apply /andP.
  split; last by apply /asboolP.
  by rewrite eq_sym; apply /eqRP.
move=> /andP [?] /asboolP ?; apply /asboolPn /ltR_neqAle.
split=> //.
by apply /eqRP; rewrite eq_sym.
Qed.

Lemma le_refl : reflexive (@leb R).
Proof. move=> x; apply /asboolP; exact: (Real.le_reflexive R). Qed.

Lemma le_anti : antisymmetric (@leb R).
Proof.
  move=> x y /andP [? ?]; apply /eqR_eq.
  by split; apply /asboolP.
Defined.

Lemma le_trans : transitive (@leb R).
Proof.
  move=> y x z /asboolP le1 /asboolP le2.
  by apply /asboolP /(Real.le_transitive R); [exact: le1 | exact le2].
Qed.

HB.instance Definition _ := @Order.isPOrder.Build ring_display R le lt lt_def le_refl le_anti le_trans.

Lemma leP (x y: R) : reflect (x <= y)%real (x <= y).
Proof. exact: asboolP. Qed.

Lemma ltP (x y: R) : reflect (x < y)%real (x < y).
Proof. exact: asboolPn. Qed.


Definition abs (x: R) := if leb 0 x then x else -x.

Lemma elim_abs (x: R) (P: R -> Prop) : (0 <= x -> P x)%real -> (x < 0 -> P (-x))%real -> P (abs x).
Proof.
move=> H H'.
rewrite /abs.
move: (orbN (leb 0 x))=> /orP.
case=> /[dup] /leP ? ; first by move=> ->; apply /H.
by move=> /negPf ->; apply /H'.
Qed.

Definition norm (x: R) := abs x.

Lemma negx_le_x (x: R) : (0 <= x)%real -> (-x <= x)%real.
Proof.
move=> H; apply /(Real.le_transitive R); first by apply /leR_opp2; exact: H.
by rewrite oppR0.
Qed.

Lemma x_le_negx (x: R) : (x <= 0)%real -> (x <= -x)%real.
Proof.
move=> H; apply /(Real.le_transitive R); first by exact: H.
by apply /leR_opp2; rewrite oppRK oppR0.
Qed.

Definition ler_normD : forall (x y: R), norm (x + y) <= (norm x + norm y).
Proof.
move=> x y.
apply: (elim_abs (x + y) (fun z => z <= _))=> H1;
apply: (elim_abs x (fun z => _ <= z + _))=> H2;
apply: (elim_abs y (fun z => _ <= _ + z))=> H3 //; apply /leP.
- by apply /leR_add2l /x_le_negx /ltRW.
- by apply /leR_add2r /x_le_negx /ltRW.
- apply /leP /(le_trans (x - y)%real); apply /leP.
  + by apply /leR_add2l /x_le_negx /ltRW.
  + by apply /leR_add2r /x_le_negx /ltRW.
- apply /negx_le_x.
  rewrite -(Real.add_zero_left R 0);
  apply /leP /(le_trans (0 + y)); first by apply /leP /leR_add2l.
  by apply /leP /leR_add2r.
- by rewrite oppRD; apply /leR_add2r /negx_le_x.
- by rewrite oppRD; apply /leR_add2l /negx_le_x.
- by rewrite oppRD; apply (Real.le_reflexive R).
Qed.

Lemma normr0_eq0 : forall x : R, norm x = 0 -> x = 0.
Proof.
move=> x.
rewrite /norm/abs; case: (leb 0 x)=> // neg0.
apply /eqR_eq /oppR_inj; rewrite oppR0.
by apply /eqR_eq.
Qed.

Lemma natmul_pos (x: R) (n: nat) : 0 <= x -> 0 <= (x *+ n).
Proof.
move=> H; elim: n => [|n IHn]; first by rewrite mulr0n; apply /le_refl.
rewrite mulrSr.
apply /(le_trans (x *+ n + 0)); first by rewrite addr0.
by apply /leP /leR_add2l /leP.
Qed.

Lemma natmul_neg (x: R) (n: nat) : x < 0 -> (x *+ n.+1) < 0.
Proof.
move=> H; elim: n => [|n IHn]; first by rewrite mulr1n.
rewrite mulrSr.
apply /(@le_lt_trans _ _ (0 + x)); last by rewrite GRing.add0r.
apply /leP; rewrite leR_add2r.
by move: IHn; rewrite /Order.lt/= lt_def /Order.le/= => /andP [] _ /leP.
Qed.

Lemma normrMn : forall (x: R) (n: nat), norm (x *+ n)%R = (norm x *+ n)%R.
Proof.
move=> x n; elim: n => [|n IHn].
  rewrite !mulr0n /norm/abs.
  elim: (leb 0 0%R)=> //.
  by apply /eqR_eq /oppR0.
rewrite !mulrSr -IHn{IHn} -mulrSr /norm/abs.
move: (orbN (0 <= x)) => /orP [] /[dup] H.
- move: (natmul_pos x n H) (natmul_pos x (n.+1) H).
  rewrite /Order.le/=/le=> -> -> ->.
  by rewrite mulrSr.
- rewrite (negPf (natmul_neg x n H)).
  have := negPf H; rewrite /Order.le/=/le => -> _.
  case: n=> [|n]; first by rewrite mulr0n -mulNrn (le_refl 0) GRing.add0r.
  by rewrite (negPf (natmul_neg x n H)) -!mulNrn mulrSr.
Qed.

Lemma normrN : forall (x: R), norm (-x) = norm x.
Proof.
move=> x; do 2 ! apply elim_abs => //.
- move=> H1 /leR_opp2.
  rewrite oppR0 oppRK => H2.
  have : x = 0; first by apply /eqR_eq; split.
  by move=> ->; apply /eqR_eq; rewrite oppR0.
- by move=> _ _; apply /eqR_eq; rewrite oppRK.
- move=> H1 /ltRW /leR_opp2.
  rewrite {1}oppRK {1}oppR0.
  by move: H1 => /[apply].
Qed.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R R norm ler_normD normr0_eq0 normrMn normrN.


Lemma addr_gt0 : forall x y : R, (0 < x) -> (0 < y) -> (0 < x + y).
Proof.
move=> x y ? ?.
apply /ltP /(@ltR_le_trans _ _ (x + 0)); first by rewrite addR0; apply /ltP.
by apply /leR_add2l /ltRW /ltP.
Qed.

Lemma ger_leVge : forall x y : R, (0 <= x)%R -> (0 <= y)%R -> (x <= y)%R || (y <= x)%R.
Proof.
move=> x y ? ?; case: (leR_total x y) => ?; apply /orP.
- by left; apply /ltP.
- by right; apply /ltP.
Qed.

Lemma normrM : {morph (Num.Def.normr : R -> R) : x y / (x * y)%real}.
Proof.
move=> x y; do 3 ! apply elim_abs => //; move=> H1 H2 H3; apply /eqR_eq.
- have H4 : (x * y <= 0)%real.
    rewrite -(mulR0 x).
    apply /(Real.mul_monotone R) => //.
    by apply /ltRW.
  rewrite mulRN.
  have : (x * y)%real = 0; first by apply /eqR_eq; split.
  by move=> ->; rewrite oppR0.
- have H4 : (x * y <= 0)%real.
    rewrite -(mul0R y) !(mulRC _ y).
    apply /(Real.mul_monotone R) => //.
    by apply /ltRW.
  rewrite !(mulRC _ y) mulRN !(mulRC y _).
  have : (x * y)%real = 0; first by apply /eqR_eq; split.
  by move=> ->; rewrite oppR0.
- by rewrite mulRN !(mulRC _ y) mulRN oppRK.
- have H4 : (x * y >= 0)%real.
    rewrite -(mulR0 x).
    by apply /(Real.mul_monotone R).
  have : (x * y)%real = 0; first by apply /eqR_eq; split.
  by move=> ->; rewrite oppR0.
- by rewrite mulRN.
- by rewrite !(mulRC _ y) mulRN.
- have H4 : (x * y >= 0)%real.
    rewrite -(oppRK (x * y)) -mulRN (mulRC x _) -mulRN -(mulR0 (-y)).
    by apply /(Real.mul_monotone R); rewrite -oppR0; apply /leR_opp2 /ltRW.
  have : (x * y)%real = 0; first by apply /eqR_eq; split.
  by move=> ->; rewrite oppR0.
Qed.

Lemma sub_ge : forall (x y: R), (x <= y) = (0 <= (y - x)).
Proof.
move=> x y; apply /Bool.eq_iff_eq_true.
split; by move /leP /subR_ge0 /leP.
Qed.

Lemma zero_only_self_opp : forall (x: R), -x = x -> x = 0.
Proof.
move=> x H; apply /eqR_eq /(@mulRI _ 2).
  move: (ltR02 R) => /ltR_neqAle [] /[swap] _.
  by apply /contra_not; move /eqR_sym.
rewrite mulR0 mul2R.
apply /(@addIR _ (-x)).
rewrite add0R addRK.
by apply /eqR_sym /eqR_eq.
Qed.

Lemma ler_def : forall x y : R, (x <= y) = (`|y - x| == (y - x)).
Proof.
rewrite /Num.norm/=/norm/abs.
move=> x y; apply /Bool.eq_iff_eq_true; split.
  rewrite sub_ge /Order.le/=/le => ->.
  by apply /eqP.
move: (orbN (leb 0 (y - x))) => /orP [].
  by move=> /[dup] ? -> _; rewrite sub_ge.
rewrite /Order.le/=/le.
move /negPf=> ->; move /eqP.
move /zero_only_self_opp /subr0_eq=> ->.
by apply le_refl.
Qed.

HB.instance Definition _ := @Num.isNumRing.Build R addr_gt0 ger_leVge normrM ler_def.


Lemma real : Num.real_axiom R.
move=> x; rewrite qualifE.
apply /orP.
by case: (leR_total 0 x) => ?; [left|right]; apply /leP.
Qed.

HB.instance Definition _ := @Num.NumDomain_isReal.Build R real.


Lemma fieldP : GRing.field_axiom R. Proof. by []. Qed.
HB.instance Definition _ := GRing.UnitRing_isField.Build R fieldP.


Definition scale : R -> R -> R := mul.
Definition scalerA := mulrA.
Definition scale0r := mul0r.
Definition scale1r := mul1r.
Definition scalerDr : right_distributive scale +%R := @mulrDr R.
Definition scalerDl : forall v : R, {morph scale^~ v : a b / a + b >-> a + b}.
Proof. move=> x y z; exact: mulrDl. Qed.

HB.instance Definition _ := @GRing.Nmodule_isLSemiModule.Build R R scale scalerA scale0r scale1r scalerDr scalerDl.


Lemma normrZ : forall (l : R) (x : R), norm (l *: x) = `|l| * norm x.
Admitted.

Check (R: lmodType _).
Check (R: lmodType R).
Check (R: zmodType).
HB.about Real.val.
Check R: normedZmodType _.
HB.instance Definition _ := @Lmodule_isNormed.Build R R norm ler_normD normrZ normr0_eq0.
HB.about Real.val.
HB.about normedModType.
HB.about Lmodule_isNormed.Build.
Check (R: normedZmodType _).
HB.howto R pseudoMetricNormedZmodType.
HB.about PseudoMetricNormedZmod.
HB.howto R normedModType.
Fail Check (R: normedModType _).
(* TODO: doesn't seem to give R a normedModType structure? *)
Fail Check (R: pseudoMetricNormedZmodType R).
(* Is it because I'm missing that R is a pseudoMetricNormedZmodType ? *)


HB.instance Definition _ := Topological.copy R (order_topology R).


HB.instance Definition _ := GRing.Lalgebra.copy R R^o.


Definition interval (a b: R) := `[a, b]%classic.

Definition continuous_poly (p: {poly R}) : continuous (horner p)%classic.
Proof.
elim /poly_ind: p.
  rewrite (funext (fun x => horner0 x)).
  exact: cst_continuous.
move=> A B A_cont.
have : horner (A * 'X + B%:P) = horner A * id + (fun=> B).
  apply /funext => x.
  by rewrite !hornerE.
move=> ->.
(* we're missing R: normedModType to apply continuity lemmas :( *)
Fail Check R: normedModType _.
Admitted.


Lemma has_sup_correspondance : forall E : set R,
    has_sup E -> Real.has_sup E.
Proof.
move=> ? [? [w wineq]]; split=> //.
exists w=> y ?.
move: (wineq y)=> H.
by apply /leP /H.
Qed.

Lemma sup_is_ubound : forall E : set R,
    has_sup E -> ubound E (Real.sup E).
Proof.
move=> E ?.
rewrite /ubound => x inE /=.
apply /asboolP /real_sup_ub => //.
by apply: has_sup_correspondance.
Qed.

Lemma sup_is_supremum : forall E : set R,
    has_sup E -> supremums E (Real.sup E).
Proof.
move=> E ?; split; first by exact: sup_is_ubound.
move=> x ubound.
apply /asboolP /real_sup_le_ub; first by apply: has_sup_correspondance.
by move=> y yinE; apply /asboolP /ubound.
Qed.

Lemma sup_is_unique : forall E : set R,
    has_sup E -> supremum 0 E = Real.sup E.
Proof.
move=> E /[dup] has_sup.
rewrite /supremum; case=> /set0P /negPf -> _.
rewrite (xget_unique 0%real (sup_is_supremum E _)) => //.
move=> y [is_upper_bound least_upper_bound].
apply /le_anti /andP; split; first by apply /least_upper_bound /sup_is_ubound.
move: (sup_is_supremum E has_sup) => [is_sup_upper_bound sup_least_upper_bound].
by apply sup_least_upper_bound; exact: is_upper_bound.
Qed.

Lemma sup_upper_bound_subdef : forall E : set R,
    has_sup E -> ubound E (supremum 0 E).
Proof.
move=> E /[dup] has_sup; case=> /set0P.
case: (E == set0)%B => // _ has_ubound.
rewrite sup_is_unique=> //.
move=> x inE; apply /asboolP /real_sup_ub => //.
exact: has_sup_correspondance.
Qed.

Lemma sup_adherent_subdef' : forall (E : set R) (eps : R),
    (0 < eps)%R -> has_sup E -> exists2 e : R, E e & ((supremum 0 E - eps) < e)%R.
Proof.
move=> E eps pos_eps has_sup.
have := sup_adherent_subdef E eps pos_eps.
move /(_ (has_sup_correspondance _ has_sup)).
case=> e inE isclose; exists e => //.
by rewrite sup_is_unique.
Qed.


Lemma continuity_epsilon : forall (f: R -> R) (x: R),
    {for x, continuous f} ->
    forall eps, (eps > 0) -> exists delta, (delta > 0) /\ (forall y, x - delta < y < x + delta -> (f x) - eps < f y < (f x) + eps).
Admitted.

Lemma poly_ivt_subproof : Num.real_closed_axiom R.
Proof.
move=> p a b Hle /andP [pa_neg pb_pos].
absurd_not=> noroots.

pose N := [set y: R | y < 0]%R%classic.
pose I := interval a b.
pose preN := ((preimage (horner p) N) `&` I)%classic.

have a_in_preN : a \in preN.
  rewrite in_setE; split; last by apply /andP; split.
  rewrite /N/= -(opprK p.[a]) oppr_lt0 lt0r.
  apply /andP; split; last by rewrite -oppr_le0 opprK=> //.
  by rewrite -oppr0 eqr_opp; apply /noroots; lra.

have preN_has_sup : has_sup preN.
  split; first by exists a; rewrite -in_setE; exact a_in_preN.
  exists b => t.
  rewrite /preN /setI /I /interval set_itvE.
  by case=> _ /= /andP [].

pose x := Real.sup preN.

have : root p x; first last.
  apply /negP /noroots.
  apply /andP; split.
    by apply /asboolP /real_sup_ub; [exact: has_sup_correspondance | exact: set_mem].
  have := sup_is_supremum _ preN_has_sup.
  case=> _; move /(_ b); apply.
  rewrite /ubound/preN/I/interval set_itvE /= => ?.
  by case; lra.

rewrite /root.
apply /eqP /le_anti /andP => []; split.
- (* p.[x] <= 0 *)
  apply /contraT=> /ltP/ltP px_lt_0.
  pose eps := p.[x] / 2.
  
  have eps_pos : eps > 0; first by rewrite /eps; nra.

  have := continuity_epsilon (horner p) x (continuous_poly p x) eps eps_pos.
  case=> delta [] delta_pos /[dup] Heps.
  pose z := x - delta/2.
  move=> /(_ z).
  have x_z_close : x - delta < z < x + delta.
    by apply /andP; split; rewrite /z; nra.
  move /(_ x_z_close) => H.

  have : ubound preN z.
    move=> t t_in_preN.
    apply /contraT => /ltP /ltP.
    move: (orbN (t > x)) => /orP [].
      move=> /[swap] _.
      have := sup_is_ubound preN preN_has_sup t t_in_preN.
      rewrite real_ltNge ?num_real => //.
      by move=> /[swap] /negP /[apply].
    rewrite -real_leNgt ?num_real /z // => ? ?.
    have: x - delta < t < x + delta; first by nra.
    move: (Heps t) => /[apply].
    rewrite /eps => ?; have: p.[t] > 0; first by lra.
    by move: t_in_preN; rewrite /preN /N /=; lra.
  have := sup_is_supremum preN preN_has_sup.
  rewrite /supremums /lbound /=; move=> [] _.
  move=> /(_ z) /[apply].

  have : x > z; first by rewrite /z; nra.
  rewrite real_leNgt ?num_real => // /[swap].
  by move=> /negP /[apply].
- (* p.[x] => 0 *)
  apply /contraT=> /ltP/ltP px_lt_0.
  
  have a_lt_x : a < x.
    have := sup_is_ubound preN preN_has_sup a.
    rewrite -inE a_in_preN => /(_ isT).
    admit.

  have x_lt_b : b < x.
    admit.

  pose eps := - p.[x] / 2.
  have eps_pos : eps > 0.
    rewrite /eps.
    admit.
  
  have := continuity_epsilon (horner p) x (continuous_poly p x) eps eps_pos.
  case=> delta [] delta_pos.

  pose alpha := Num.min (delta / 2) ((b - x)/2).
  pose z := x + alpha.
  move=> /(_ z).
  have x_z_close : x - delta < z < x + delta.
    admit.
  move /(_ x_z_close); rewrite /eps => H.

  have z_in_preN : preN z.
    admit.

  have := sup_upper_bound_subdef preN preN_has_sup z z_in_preN.
  rewrite (sup_is_unique _ preN_has_sup).
  
  have: z > x.
    rewrite /z.
    admit.
  rewrite real_ltNge ?num_real => //.
  by move=> /negP /[apply].
Admitted.

HB.instance Definition _ := @Num.RealField_isClosed.Build R poly_ivt_subproof.

Lemma natmul_correspondance' : forall n, Real.nat R n = GRing.natmul 1 n.
Proof.
case=> // n; rewrite /GRing.natmul iteropS.
elim: n => //= n <-.
by rewrite GRing.addrC.
Qed.

Definition nat_num : pred R :=
  fun (x: R) => (((trunc x)%:R)%R == x)%B.

Definition int_num : pred R :=
  fun (x: R) => nat_num x || nat_num (- x)%R.

Lemma truncP' : forall (x: R),
    if (0 <= x)%R
    then ((trunc x)%:R <= x < (trunc x).+1%:R)%R
    else (trunc x == 0%R)%B.
Proof.
move=> x.
have := truncP x.
move: (orbN (0 <= x)%R) => /orP []; last first.
  by rewrite /Order.le/=/le /GRing.zero/=/zero => /negPf ->.
rewrite /Order.le/=/le /GRing.zero/=/zero => -> [] ? ?.
by apply /andP; split; apply /asboolP; rewrite -natmul_correspondance'.
Qed.

Lemma natrE : forall (x : R), nat_num x = (((trunc x)%:R)%R == x)%B.
Proof. by []. Qed.

Lemma intrE : forall (x : R), int_num x = nat_num x || nat_num (- x)%R.
Proof. by []. Qed.

HB.instance Definition _ := @Num.NumDomain_hasTruncn.Build R trunc nat_num int_num truncP' natrE intrE.


HB.instance Definition _ := @ArchimedeanField_isReal.Build R sup_upper_bound_subdef sup_adherent_subdef'.


Definition comap: realType := R.
End MtoT.
