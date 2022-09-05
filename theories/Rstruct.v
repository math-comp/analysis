(* This file is a modification of an eponymous file from the CoqApprox        *)
(* library. The header of the original file is reproduced below. Changes are  *)
(* part of the analysis library and enjoy the same licence as this library.   *)
(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
Require Import Rtrigo1 Reals.
From mathcomp Require Import all_ssreflect ssralg poly mxpoly ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope R_scope.

Lemma Req_EM_T (r1 r2 : R) : {r1 = r2} + {r1 <> r2}.
Proof.
case: (total_order_T r1 r2) => [[r1Lr2 | <-] | r1Gr2].
- by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {2}r1Er2.
- by left.
by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {1}r1Er2.
Qed.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical R_eqMixin := EqMixin eqrP.
Canonical R_eqType := Eval hnf in EqType R R_eqMixin.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%N. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

Definition R_choiceMixin : choiceMixin R :=
  Choice.Mixin pickR_some pickR_ex pickR_ext.

Canonical R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Definition R_zmodMixin := ZmodMixin RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Canonical R_zmodType := Eval hnf in ZmodType R R_zmodMixin.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

Definition R_ringMixin := RingMixin RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

Canonical R_ringType := Eval hnf in RingType R R_ringMixin.
Canonical R_comRingType := Eval hnf in ComRingType R Rmult_comm.

Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Definition Rinvx r := if (r != 0) then / r else r.

Definition unit_R r := r != 0.

Lemma RmultRinvx : {in unit_R, left_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_l //; apply/eqP.
Qed.

Lemma RinvxRmult : {in unit_R, right_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_r //; apply/eqP.
Qed.

Lemma intro_unit_R x y : y * x = 1 /\ x * y = 1 -> unit_R x.
Proof.
move=> [yx_eq1 _]; apply: contra_eqN yx_eq1 => /eqP->.
by rewrite Rmult_0_r eq_sym R1_neq_0.
Qed.

Lemma Rinvx_out : {in predC unit_R, Rinvx =1 id}.
Proof. by move=> x; rewrite inE/= /Rinvx -if_neg => ->. Qed.

Definition R_unitRingMixin :=
  UnitRingMixin RmultRinvx RinvxRmult intro_unit_R Rinvx_out.

Canonical R_unitRing :=
  Eval hnf in UnitRingType R R_unitRingMixin.

Canonical R_comUnitRingType :=
  Eval hnf in [comUnitRingType of R].

Lemma R_idomainMixin x y : x * y = 0 -> (x == 0) || (y == 0).
Proof. by move=> /Rmult_integral []->; rewrite eqxx ?orbT. Qed.

Canonical R_idomainType := Eval hnf in IdomainType R R_idomainMixin.

Lemma R_fieldMixin : GRing.Field.mixin_of [unitRingType of R].
Proof. by done. Qed.

Definition R_fieldIdomainMixin := FieldIdomainMixin R_fieldMixin.

Canonical R_fieldType := FieldType R R_fieldMixin.

(** Reflect the order on the reals to bool *)

Definition Rleb r1 r2 := if Rle_dec r1 r2 is left _ then true else false.
Definition Rltb r1 r2 := Rleb r1 r2 && (r1 != r2).
Definition Rgeb r1 r2 := Rleb r2 r1.
Definition Rgtb r1 r2 := Rltb r2 r1.

Lemma RlebP r1 r2 : reflect (r1 <= r2) (Rleb r1 r2).
Proof. by rewrite /Rleb; apply: (iffP idP); case: Rle_dec. Qed.

Lemma RltbP r1 r2 : reflect (r1 < r2) (Rltb r1 r2).
Proof.
rewrite /Rltb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
- by case=> // r1Er2 /eqP[].
- by move=> _ r1Lr2; apply/eqP/Rlt_not_eq.
by move=> Nr1Lr2 r1Lr2; case: Nr1Lr2; left.
Qed.

(*
Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one //=.
*)

Section ssreal_struct.

Import GRing.Theory.
Import Num.Theory.
Import Num.Def.

Local Open Scope R_scope.

Lemma Rleb_norm_add x y : Rleb (Rabs (x + y)) (Rabs x + Rabs y).
Proof. by apply/RlebP/Rabs_triang. Qed.

Lemma addr_Rgtb0 x y : Rltb 0 x -> Rltb 0 y -> Rltb 0 (x + y).
Proof. by move/RltbP=> Hx /RltbP Hy; apply/RltbP/Rplus_lt_0_compat. Qed.

Lemma Rnorm0_eq0 x : Rabs x = 0 -> x = 0.
Proof. by move=> H; case: (x == 0) /eqP=> // /Rabs_no_R0. Qed.

Lemma Rleb_leVge x y : Rleb 0 x -> Rleb 0 y -> (Rleb x y) || (Rleb y x).
Proof.
move/RlebP=> Hx /RlebP Hy; case: (Rlt_le_dec x y).
by move/Rlt_le/RlebP=> ->.
by move/RlebP=> ->; rewrite orbT.
Qed.

Lemma RnormM : {morph Rabs : x y / x * y}.
exact: Rabs_mult. Qed.

Lemma Rleb_def x y : (Rleb x y) = (Rabs (y - x) == y - x).
apply/(sameP (RlebP x y))/(iffP idP)=> [/eqP H| /Rle_minus H].
  apply: Rminus_le; rewrite -Ropp_minus_distr.
  apply/Rge_le/Ropp_0_le_ge_contravar.
  by rewrite -H; apply: Rabs_pos.
apply/eqP/Rabs_pos_eq.
rewrite -Ropp_minus_distr.
by apply/Ropp_0_ge_le_contravar/Rle_ge.
Qed.

Lemma Rltb_def x y : (Rltb x y) = (y != x) && (Rleb x y).
apply/(sameP (RltbP x y))/(iffP idP).
  case/andP=> /eqP H /RlebP/Rle_not_gt H2.
  by case: (Rtotal_order x y)=> // [][] // /esym.
move=> H; apply/andP; split; [apply/eqP|apply/RlebP].
  exact: Rgt_not_eq.
exact: Rlt_le.
Qed.

Definition R_numMixin := NumMixin Rleb_norm_add addr_Rgtb0 Rnorm0_eq0
                                  Rleb_leVge RnormM Rleb_def Rltb_def.
Canonical R_porderType := POrderType ring_display R R_numMixin.
Canonical R_numDomainType := NumDomainType R R_numMixin.
Canonical R_normedZmodType := NormedZmodType R R R_numMixin.

Lemma RleP : forall x y, reflect (Rle x y) (x <= y)%R.
Proof. exact: RlebP. Qed.
Lemma RltP : forall x y, reflect (Rlt x y) (x < y)%R.
Proof. exact: RltbP. Qed.
(* :TODO: *)
(* Lemma RgeP : forall x y, reflect (Rge x y) (x >= y)%R. *)
(* Proof. exact: RlebP. Qed. *)
(* Lemma RgtP : forall x y, reflect (Rgt x y) (x > y)%R. *)
(* Proof. exact: RltbP. Qed. *)

Canonical R_numFieldType := [numFieldType of R].

Lemma Rreal_axiom (x : R) : (0 <= x)%R || (x <= 0)%R.
Proof.
case: (Rle_dec 0 x)=> [/RleP ->|] //.
by move/Rnot_le_lt/Rlt_le/RleP=> ->; rewrite orbT.
Qed.

Lemma R_total : totalPOrderMixin R_porderType.
Proof.
move=> x y; case: (Rle_lt_dec x y) => [/RleP -> //|/Rlt_le/RleP ->];
  by rewrite orbT.
Qed.

Canonical R_latticeType := LatticeType R R_total.
Canonical R_distrLatticeType := DistrLatticeType R R_total.
Canonical R_orderType := OrderType R R_total.
Canonical R_realDomainType := [realDomainType of R].
Canonical R_realFieldType := [realFieldType of R].

Lemma Rarchimedean_axiom : Num.archimedean_axiom R_numDomainType.
Proof.
move=> x; exists (Z.abs_nat (up x) + 2)%N.
have [Hx1 Hx2]:= (archimed x).
have Hz (z : Z): z = (z - 1 + 1)%Z by rewrite Zplus_comm Zplus_minus.
have Zabs_nat_Zopp z : Z.abs_nat (- z)%Z = Z.abs_nat z by case: z.
apply/RltbP/Rabs_def1.
  apply: (Rlt_trans _ ((Z.abs_nat (up x))%:R)%R); last first.
    rewrite -[((Z.abs_nat _)%:R)%R]Rplus_0_r mulrnDr.
    by apply/Rplus_lt_compat_l/Rlt_0_2.
  apply: (Rlt_le_trans _ (IZR (up x)))=> //.
  elim/(well_founded_ind (Zwf_well_founded 0)): (up x) => z IHz.
  case: (Z_lt_le_dec 0 z) => [zp | zn].
    rewrite [z]Hz plus_IZR Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE mulrnDr.
    apply/Rplus_le_compat_r/IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_trans _ (IZR 0)); first exact: IZR_le.
  by apply/RlebP/(ler0n R_numDomainType (Z.abs_nat z)).
apply: (Rlt_le_trans _ (IZR (up x) - 1)).
  apply: Ropp_lt_cancel; rewrite Ropp_involutive.
  rewrite Ropp_minus_distr /Rminus -opp_IZR -{2}(Z.opp_involutive (up x)).
  elim/(well_founded_ind (Zwf_well_founded 0)): (- up x)%Z => z IHz .
  case: (Z_lt_le_dec 0 z) => [zp | zn].
  rewrite [z]Hz Zabs_nat_Zopp plus_IZR.
  rewrite Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE -Rplus_assoc -addnA [(_ + 2)%N]addnC addnA mulrnDr.
    apply: Rplus_lt_compat_r; rewrite -Zabs_nat_Zopp.
    apply: IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_lt_trans _ 1).
    rewrite -{2}[1]Rplus_0_r; apply: Rplus_le_compat_l.
    by rewrite -/(IZR 0); apply: IZR_le.
  rewrite mulrnDr; apply: (Rlt_le_trans _ 2).
    by rewrite -{1}[1]Rplus_0_r; apply/Rplus_lt_compat_l/Rlt_0_1.
  rewrite -[2]Rplus_0_l; apply: Rplus_le_compat_r.
  by apply/RlebP/(ler0n R_numDomainType (Z.abs_nat _)).
apply: Rminus_le.
rewrite /Rminus Rplus_assoc [- _ + _]Rplus_comm -Rplus_assoc -!/(Rminus _ _).
exact: Rle_minus.
Qed.

(* Canonical R_numArchiDomainType := ArchiDomainType R Rarchimedean_axiom. *)
(* (* Canonical R_numArchiFieldType := [numArchiFieldType of R]. *) *)
(* Canonical R_realArchiDomainType := [realArchiDomainType of R]. *)
Canonical R_realArchiFieldType := ArchiFieldType R Rarchimedean_axiom.

(** Here are the lemmas that we will use to prove that R has
the rcfType structure. *)

Lemma continuity_eq f g : f =1 g -> continuity f -> continuity g.
Proof.
move=> Hfg Hf x eps Heps.
have [y [Hy1 Hy2]]:= Hf x eps Heps.
by exists y; split=> // z; rewrite -!Hfg; exact: Hy2.
Qed.

Lemma continuity_sum (I : finType) F (P : pred I):
(forall i, P i -> continuity (F i)) ->
continuity (fun x => (\sum_(i | P i) ((F i) x)))%R.
Proof.
move=> H; elim: (index_enum I)=> [|a l IHl].
  set f:= fun _ => _.
  have Hf: (fun x=> 0) =1 f by move=> x; rewrite /f big_nil.
  by apply: (continuity_eq Hf); exact: continuity_const.
set f := fun _ => _.
case Hpa: (P a).
  have Hf: (fun x => F a x + \sum_(i <- l | P i) F i x)%R =1 f.
    by move=> x; rewrite /f big_cons Hpa.
  apply: (continuity_eq Hf); apply: continuity_plus=> //.
  exact: H.
have Hf: (fun x => \sum_(i <- l | P i) F i x)%R =1 f.
  by move=> x; rewrite /f big_cons Hpa.
exact: (continuity_eq Hf).
Qed.

Lemma continuity_exp f n: continuity f -> continuity (fun x => (f x)^+ n)%R.
Proof.
move=> Hf; elim: n=> [|n IHn]; first exact: continuity_const.
set g:= fun _ => _.
have Hg: (fun x=> f x * f x ^+ n)%R =1 g.
  by move=> x; rewrite /g exprS.
by apply: (continuity_eq Hg); exact: continuity_mult.
Qed.

Lemma Rreal_closed_axiom : Num.real_closed_axiom R_numDomainType.
Proof.
move=> p a b; rewrite !le_eqVlt.
case Hpa: ((p.[a])%R == 0%R).
  by move=> ? _ ; exists a=> //; rewrite lexx le_eqVlt.
case Hpb: ((p.[b])%R == 0%R).
  by move=> ? _; exists b=> //; rewrite lexx le_eqVlt andbT.
case Hab: (a == b).
  by move=> _; rewrite (eqP Hab) eq_sym Hpb (ltNge 0) /=; case/andP=> /ltW ->.
rewrite eq_sym Hpb /=; clear=> /RltbP Hab /andP [] /RltbP Hpa /RltbP Hpb.
suff Hcp: continuity (fun x => (p.[x])%R).
  have [z [[Hza Hzb] /eqP Hz2]]:= IVT _ a b Hcp Hab Hpa Hpb.
  by exists z=> //; apply/andP; split; apply/RlebP.
rewrite -[p]coefK poly_def.
set f := fun _ => _.
have Hf: (fun (x : R) => \sum_(i < size p) (p`_i * x^+i))%R =1 f.
  move=> x; rewrite /f horner_sum.
  by apply: eq_bigr=> i _; rewrite hornerZ hornerXn.
apply: (continuity_eq Hf); apply: continuity_sum=> i _.
apply:continuity_scal; apply: continuity_exp=> x esp Hesp.
by exists esp; split=> // y [].
Qed.

Canonical R_rcfType := RcfType R Rreal_closed_axiom.
(* Canonical R_realClosedArchiFieldType := [realClosedArchiFieldType of R]. *)

End ssreal_struct.

Local Open Scope ring_scope.
Require Import reals boolp classical_sets.

Section ssreal_struct_contd.
Implicit Type E : set R.

Lemma is_upper_boundE E x : is_upper_bound E x = (ubound E) x.
Proof.
rewrite propeqE; split; [move=> h|move=> /ubP h y Ey; exact/RleP/h].
by apply/ubP => y Ey; apply/RleP/h.
Qed.

Lemma boundE E : bound E = has_ubound E.
Proof. by apply/eq_exists=> x; rewrite is_upper_boundE. Qed.

Lemma Rcondcomplete E : has_sup E -> {m | isLub E m}.
Proof.
move=> [E0 uE]; have := completeness E; rewrite boundE => /(_ uE E0)[x [E1 E2]].
exists x; split; first by rewrite -is_upper_boundE; apply: E1.
by move=> y; rewrite -is_upper_boundE => /E2/RleP.
Qed.

Lemma Rsupremums_neq0 E : has_sup E -> (supremums E !=set0)%classic.
Proof. by move=> /Rcondcomplete[x [? ?]]; exists x. Qed.

Lemma Rsup_isLub x0 E : has_sup E -> isLub E (supremum x0 E).
Proof.
have [-> [/set0P]|E0 hsE] := eqVneq E set0; first by rewrite eqxx.
have [s [Es sE]] := Rcondcomplete hsE.
split => x Ex; first by apply/ge_supremum_Nmem=> //; exact: Rsupremums_neq0.
rewrite /supremum (negbTE E0); case: xgetP => /=.
  by move=> _ -> [_ EsE]; apply/EsE.
by have [y Ey /(_ y)] := Rsupremums_neq0 hsE.
Qed.

(* :TODO: rewrite like this using (a fork of?) Coquelicot *)
(* Lemma real_sup_adherent (E : pred R) : real_sup E \in closure E. *)
Lemma real_sup_adherent x0 E (eps : R) : (0 < eps) ->
  has_sup E -> exists2 e, E e & (supremum x0 E - eps) < e.
Proof.
move=> eps_gt0 supE; set m := _ - eps; apply: contrapT=> mNsmall.
have : (ubound E) m.
  apply/ubP => y Ey.
  by have /negP := mNsmall (ex_intro2 _ _ y Ey _); rewrite -leNgt.
have [_ /(_ m)] := Rsup_isLub x0 supE.
move => m_big /m_big.
by rewrite -subr_ge0 addrC addKr oppr_ge0 leNgt eps_gt0.
Qed.

Lemma Rsup_ub x0 E : has_sup E -> (ubound E) (supremum x0 E).
Proof.
by move=> supE x Ex; apply/ge_supremum_Nmem => //; exact: Rsupremums_neq0.
Qed.

Definition real_realMixin : Real.mixin_of _ :=
  RealMixin (@Rsup_ub (0 : R)) (real_sup_adherent 0).
Canonical real_realType := RealType R real_realMixin.

Implicit Types (x y : R) (m n : nat).

(* equational lemmas about exp, sin and cos for mathcomp compat *)

(* Require Import realsum. *)

(* :TODO: One day, do this *)
(* Notation "\Sum_ i E" := (psum (fun i => E)) *)
(*  (at level 100, i ident, format "\Sum_ i  E") : ring_scope. *)

(* Definition exp x := \Sum_n (n`!)%:R^-1 * x ^ n. *)

Lemma expR0 : exp (0 : R) = 1.
Proof. by rewrite exp_0. Qed.

Lemma expRD x y : exp x * exp y = exp (x + y).
Proof. by rewrite exp_plus. Qed.

Lemma expRX x n : exp x ^+ n = exp (x *+ n).
Proof.
elim: n => [|n Ihn]; first by rewrite expr0 mulr0n exp_0.
by rewrite exprS Ihn mulrS expRD.
Qed.

Lemma sinD x y : sin (x + y) = sin x * cos y + cos x * sin y.
Proof. by rewrite sin_plus. Qed.

Lemma cosD x y : cos (x + y) = (cos x * cos y - sin x * sin y).
Proof. by rewrite cos_plus. Qed.

Lemma RplusE x y : Rplus x y = x + y. Proof. by []. Qed.

Lemma RminusE x y : Rminus x y = x - y. Proof. by []. Qed.

Lemma RmultE x y : Rmult x y = x * y. Proof. by []. Qed.

Lemma RoppE x : Ropp x = - x. Proof. by []. Qed.

Lemma RinvE x : x != 0 -> Rinv x = x^-1.
Proof. by move=> x_neq0; rewrite -[RHS]/(if _ then _ else _) x_neq0. Qed.

Lemma RdivE x y : y != 0 -> Rdiv x y = x / y.
Proof. by move=> y_neq0; rewrite /Rdiv RinvE. Qed.

Lemma INRE n : INR n = n%:R.
Proof. elim: n => // n IH; by rewrite S_INR IH RplusE -addn1 natrD. Qed.

Lemma RsqrtE x : 0 <= x -> sqrt x = Num.sqrt x.
Proof.
move => x0; apply/eqP; have [t1 t2] := conj (sqrtr_ge0 x) (sqrt_pos x).
rewrite eq_sym -(eqr_expn2 (_: 0 < 2)%N t1) //; last by apply /RleP.
rewrite sqr_sqrtr // !exprS expr0 mulr1 -RmultE ?sqrt_sqrt //; by apply/RleP.
Qed.

Lemma RpowE x n : pow x n = x ^+ n.
Proof. by elim: n => [ | n In] //=; rewrite exprS In RmultE. Qed.

Lemma RmaxE x y : Rmax x y = Num.max x y.
Proof.
case: (lerP x y) => H; first by rewrite Rmax_right //; apply: RlebP.
by rewrite ?ltW // Rmax_left //;  apply/RlebP; move/ltW : H.
Qed.

(* useful? *)
Lemma RminE x y : Rmin x y = Num.min x y.
Proof.
case: (lerP x y) => H; first by rewrite Rmin_left //; apply: RlebP.
by rewrite ?ltW // Rmin_right //;  apply/RlebP; move/ltW : H.
Qed.

Section bigmaxr.
Context {R : realDomainType}.

(* bigop pour le max pour des listes non vides ? *)
#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Definition bigmaxr (r : R) s := \big[Num.max/head r s]_(i <- s) i.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_nil (x0 : R) : bigmaxr x0 [::] = x0.
Proof. by rewrite /bigmaxr /= big_nil. Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_un (x0 x : R) : bigmaxr x0 [:: x] = x.
Proof. by rewrite /bigmaxr /= big_cons big_nil maxxx. Qed.

(* previous definition *)
#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxrE (r : R) s : bigmaxr r s = foldr Num.max (head r s) (behead s).
Proof.
rewrite (_ : bigmaxr _ _ = if s isn't h :: t then r else \big[Num.max/h]_(i <- s) i).
  case: s => // ? t; rewrite big_cons /bigmaxr.
  by elim: t => //= [|? ? <-]; [rewrite big_nil maxxx | rewrite big_cons maxCA].
by case: s => //=; rewrite /bigmaxr big_nil.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigrmax_dflt (x y : R) s : Num.max x (\big[Num.max/x]_(j <- y :: s) j) =
  Num.max x (\big[Num.max/y]_(i <- y :: s) i).
Proof.
elim: s => /= [|h t IH] in x y *.
by rewrite !big_cons !big_nil maxxx maxCA maxxx maxC.
by rewrite big_cons maxCA IH maxCA [in RHS]big_cons IH.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_cons (x0 x y : R) lr :
  bigmaxr x0 (x :: y :: lr) = Num.max x (bigmaxr x0 (y :: lr)).
Proof. by rewrite [y :: lr]lock /bigmaxr /= -lock big_cons bigrmax_dflt. Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_ler (x0 : R) s i :
  (i < size s)%N -> (nth x0 s i) <= (bigmaxr x0 s).
Proof.
rewrite /bigmaxr; elim: s i => // h t IH [_|i] /=.
  by rewrite big_cons /= le_maxr lexx.
rewrite ltnS => ti; case: t => [|h' t] // in IH ti *.
by rewrite big_cons bigrmax_dflt le_maxr orbC IH.
Qed.

(* Compatibilité avec l'addition *)
#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_addr (x0 : R) lr (x : R) :
  bigmaxr (x0 + x) (map (fun y : R => y + x) lr) = (bigmaxr x0 lr) + x.
Proof.
rewrite /bigmaxr; case: lr => [|h t]; first by rewrite !big_nil.
elim: t h => /= [|h' t IH] h; first by rewrite ?(big_cons,big_nil) -addr_maxl.
by rewrite [in RHS]big_cons bigrmax_dflt addr_maxl -IH big_cons bigrmax_dflt.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_mem (x0 : R) lr : (0 < size lr)%N -> bigmaxr x0 lr \in lr.
Proof.
rewrite /bigmaxr; case: lr => // h t _.
elim: t => //= [|h' t IH] in h *; first by rewrite big_cons big_nil inE maxxx.
rewrite big_cons bigrmax_dflt inE eq_le; case: lerP => /=.
- by rewrite le_maxr lexx.
- by rewrite lt_maxr ltxx => ?; rewrite max_r ?IH // ltW.
Qed.

(* TODO: bigmaxr_morph? *)
#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_mulr (A : finType) (s : seq A) (k : R) (x : A -> R) :
  0 <= k -> bigmaxr 0 (map (fun i => k * x i) s) = k * bigmaxr 0 (map x s).
Proof.
move=> k0; elim: s => /= [|h [/=|h' t ih]].
by rewrite bigmaxr_nil mulr0.
by rewrite !bigmaxr_un.
by rewrite bigmaxr_cons {}ih bigmaxr_cons maxr_pmulr.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_index (x0 : R) lr :
  (0 < size lr)%N -> (index (bigmaxr x0 lr) lr < size lr)%N.
Proof.
rewrite /bigmaxr; case: lr => //= h t _; case: ifPn => // /negbTE H.
move: (@bigmaxr_mem x0 (h :: t) isT).
by rewrite ltnS index_mem inE /= eq_sym H.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_lerP (x0 : R) lr (x : R) :
  (0 < size lr)%N ->
  reflect (forall i, (i < size lr)%N -> (nth x0 lr i) <= x) ((bigmaxr x0 lr) <= x).
Proof.
move=> lr_size; apply: (iffP idP) => [le_x i i_size | H].
  by apply: (le_trans _ le_x); apply: bigmaxr_ler.
by move/(nthP x0): (bigmaxr_mem x0 lr_size) => [i i_size <-]; apply: H.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_ltrP (x0 : R) lr (x : R) :
  (0 < size lr)%N ->
  reflect (forall i, (i < size lr)%N -> (nth x0 lr i) < x) ((bigmaxr x0 lr) < x).
Proof.
move=> lr_size; apply: (iffP idP) => [lt_x i i_size | H].
  by apply: le_lt_trans lt_x; apply: bigmaxr_ler.
by move/(nthP x0): (bigmaxr_mem x0 lr_size) => [i i_size <-]; apply: H.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxrP (x0 : R) lr (x : R) :
  (x \in lr /\ forall i, (i < size lr) %N -> (nth x0 lr i) <= x) -> (bigmaxr x0 lr = x).
Proof.
move=> [] /(nthP x0) [] j j_size j_nth x_ler; apply: le_anti; apply/andP; split.
  by apply/bigmaxr_lerP => //; apply: (leq_trans _ j_size).
by rewrite -j_nth (bigmaxr_ler _ j_size).
Qed.

(* surement à supprimer à la fin
Lemma bigmaxc_lttc x0 lc :
  uniq lc -> forall i, (i < size lc)%N -> (i != index (bigmaxc x0 lc) lc)
    -> lttc (nth x0 lc i) (bigmaxc x0 lc).
Proof.
move=> lc_uniq Hi size_i /negP neq_i.
rewrite lttc_neqAle (bigmaxc_letc _ size_i) andbT.
apply/negP => /eqP H; apply: neq_i; rewrite -H eq_sym; apply/eqP.
by apply: index_uniq.
Qed. *)

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bigmaxr_lerif (x0 : R) lr :
  uniq lr -> forall i, (i < size lr)%N ->
     (nth x0 lr i) <= (bigmaxr x0 lr) ?= iff (i == index (bigmaxr x0 lr) lr).
Proof.
move=> lr_uniq i i_size; rewrite /Num.leif (bigmaxr_ler _ i_size).
rewrite -(nth_uniq x0 i_size (bigmaxr_index _ (leq_trans _ i_size)) lr_uniq) //.
rewrite nth_index //.
by apply: bigmaxr_mem; apply: (leq_trans _ i_size).
Qed.

(* bigop pour le max pour des listes non vides ? *)
#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Definition bmaxrf n (f : {ffun 'I_n.+1 -> R}) :=
  bigmaxr (f ord0) (codom f).

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bmaxrf_ler n (f : {ffun 'I_n.+1 -> R}) i :
  (f i) <= (bmaxrf f).
Proof.
move: (@bigmaxr_ler (f ord0) (codom f) (nat_of_ord i)).
rewrite /bmaxrf size_codom card_ord => H; move: (ltn_ord i); move/H.
suff -> : nth (f ord0) (codom f) i = f i; first by [].
by rewrite /codom (nth_map ord0) ?size_enum_ord // nth_ord_enum.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bmaxrf_index n (f : {ffun 'I_n.+1 -> R}) :
  (index (bmaxrf f) (codom f) < n.+1)%N.
Proof.
rewrite /bmaxrf.
rewrite [in X in (_ < X)%N](_ : n.+1 = size (codom f)); last first.
  by rewrite size_codom card_ord.
by apply: bigmaxr_index; rewrite size_codom card_ord.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Definition index_bmaxrf n f := Ordinal (@bmaxrf_index n f).

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma ordnat i n (ord_i : (i < n)%N) : i = Ordinal ord_i :> nat.
Proof. by []. Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma eq_index_bmaxrf n (f : {ffun 'I_n.+1 -> R}) :
  f (index_bmaxrf f) = bmaxrf f.
Proof.
move: (bmaxrf_index f).
rewrite -[X in _ (_ < X)%N]card_ord -(size_codom f) index_mem.
move/(nth_index (f ord0)) => <-; rewrite (nth_map ord0).
  by rewrite (ordnat (bmaxrf_index _)) /index_bmaxrf nth_ord_enum.
by rewrite size_enum_ord; apply: bmaxrf_index.
Qed.

#[deprecated(note="To be removed. Use topology.v's bigmax/min lemmas instead.")]
Lemma bmaxrf_lerif n (f : {ffun 'I_n.+1 -> R}) :
  injective f -> forall i,
     (f i) <= (bmaxrf f) ?= iff (i == index_bmaxrf f).
Proof.
by move=> inj_f i; rewrite /Num.leif bmaxrf_ler -(inj_eq inj_f) eq_index_bmaxrf.
Qed.

End bigmaxr.

End ssreal_struct_contd.

Require Import signed topology normedtype.

Section analysis_struct.

Canonical R_pointedType := [pointedType of R for pointed_of_zmodule R_ringType].
Canonical R_filteredType :=
  [filteredType R of R for filtered_of_normedZmod R_normedZmodType].
Canonical R_topologicalType : topologicalType := TopologicalType R
  (topologyOfEntourageMixin
    (uniformityOfBallMixin
      (@nbhs_ball_normE _ R_normedZmodType)
      (pseudoMetric_of_normedDomain R_normedZmodType))).
Canonical R_uniformType : uniformType :=
  UniformType R
  (uniformityOfBallMixin (@nbhs_ball_normE _ R_normedZmodType)
    (pseudoMetric_of_normedDomain R_normedZmodType)).
Canonical R_pseudoMetricType : pseudoMetricType R_numDomainType :=
  PseudoMetricType R (pseudoMetric_of_normedDomain R_normedZmodType).

(* TODO: express using ball?*)
Lemma continuity_pt_nbhs (f : R -> R) x :
  continuity_pt f x <->
  forall eps : {posnum R}, nbhs x (fun u => `|f u - f x| < eps%:num).
Proof.
split=> [fcont e|fcont _/RltP/posnumP[e]]; last first.
  have [_/posnumP[d] xd_fxe] := fcont e.
  exists d%:num; split; first by apply/RltP; have := [gt0 of d%:num].
  by move=> y [_ /RltP yxd]; apply/RltP/xd_fxe; rewrite /= distrC.
have /RltP egt0 := [gt0 of e%:num].
have [_ [/RltP/posnumP[d] dx_fxe]] := fcont e%:num egt0.
exists d%:num => //= y xyd; case: (eqVneq x y) => [->|xney].
  by rewrite subrr normr0.
apply/RltP/dx_fxe; split; first by split=> //; apply/eqP.
by have /RltP := xyd; rewrite distrC.
Qed.

Lemma continuity_pt_cvg (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof.
eapply iff_trans; first exact: continuity_pt_nbhs.
apply iff_sym.
have FF : Filter (f @ x).
  by typeclasses eauto.
  (*by apply fmap_filter; apply: @filter_filter' (locally_filter _).*)
case: (@cvg_ballP _ _ (f @ x) FF (f x)) => {FF}H1 H2.
(* TODO: in need for lemmas and/or refactoring of already existing lemmas (ball vs. Rabs) *)
split => [{H2} - /H1 {}H1 eps|{H1} H].
- have {H1} [//|_/posnumP[x0] Hx0] := H1 eps%:num.
  exists x0%:num => //= Hx0' /Hx0 /=.
  by rewrite /= distrC; apply.
- apply H2 => _ /posnumP[eps]; move: (H eps) => {H} [_ /posnumP[x0] Hx0].
  exists x0%:num => //= y /Hx0 /= {}Hx0.
  by rewrite /ball /= distrC.
Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_cvg. Qed.

Local Open Scope classical_set_scope.

Lemma continuity_pt_cvg' f x :
  continuity_pt f x <-> f @ x^' --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx. Qed.

Lemma continuity_pt_dnbhs f x :
  continuity_pt f x <->
  forall eps, 0 < eps -> x^' (fun u => `|f x - f u| < eps).
Proof.
rewrite continuity_pt_cvg' (@cvg_distP _ [normedModType _ of R^o]).
exact.
Qed.

Lemma nbhs_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  nbhs (f x) P -> continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_cvg; apply. Qed.

End analysis_struct.
