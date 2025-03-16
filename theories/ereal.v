(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import fsbigop cardinality set_interval.
From mathcomp Require Import reals interval_inference topology.
From mathcomp Require Export constructive_ereal.

(**md**************************************************************************)
(* # Extended real numbers, classical part ($\overline{\mathbb{R}}$)          *)
(*                                                                            *)
(* This is an addition to the file constructive_ereal.v with classical logic  *)
(* elements.                                                                  *)
(* ```                                                                        *)
(*  (\sum_(i \in A) f i)%E == finitely supported sum, see fsbigop.v           *)
(*                                                                            *)
(*             ereal_sup E == supremum of E                                   *)
(*             ereal_inf E == infimum of E                                    *)
(*  ereal_supremums_neq0 S == S has a supremum                                *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Topology of extended real numbers                                       *)
(* ```                                                                        *)
(*        ereal_topologicalType R == topology for extended real numbers over  *)
(*                                   R, a realFieldType                       *)
(*       ereal_pseudoMetricType R == pseudometric space for extended reals    *)
(*                                   over R where is a realFieldType; the     *)
(*                                   distance between x and y is defined by   *)
(*                                   `|contract x - contract y|               *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Filters                                                                 *)
(* ```                                                                        *)
(*                  ereal_dnbhs x == filter on extended real numbers that     *)
(*                                   corresponds to the deleted neighborhood  *)
(*                                   x^' if x is a real number and to         *)
(*                                   predicates that are eventually true if x *)
(*                                   is +oo/-oo.                              *)
(*                   ereal_nbhs x == same as ereal_dnbhs where dnbhs is       *)
(*                                   replaced with nbhs.                      *)
(*                ereal_loc_seq x == sequence that converges to x in the set  *)
(*                                   of extended real numbers.                *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
From mathcomp Require Import mathcomp_extra.

Local Open Scope ring_scope.

Local Open Scope ereal_scope.

Local Open Scope classical_set_scope.

Lemma EFin_bigcup T (F : nat -> set T) :
  EFin @` (\bigcup_i F i) = \bigcup_i (EFin @` F i).
Proof.
rewrite eqEsubset; split => [_ [r [n _ Fnr <-]]|]; first by exists n => //; exists r.
by move=> x [n _ [r Fnr <- /=]]; exists r => //; exists n.
Qed.

Lemma EFin_setC T (A : set T) :
  EFin @` (~` A) = (~` (EFin @` A)) `\` [set -oo; +oo].
Proof.
rewrite eqEsubset; split => [_ [r Ar <-]|[r | |]].
  by split => [|[]//]; apply: contra_not Ar => -[? ? [] <-].
- move=> [Ar _]; apply/not_exists2P; apply: contra_not Ar => h.
  by exists r => //; have [|//] := h r; apply: contrapT.
- by move=> -[_] /not_orP[_ /=].
- by move=> -[_] /not_orP[/=].
Qed.

Local Close Scope classical_set_scope.

Notation "\sum_ ( i '\in' A ) F" := (\big[+%dE/0%dE]_(i \in A) F%dE) :
  ereal_dual_scope.
Notation "\sum_ ( i '\in' A ) F" := (\big[+%E/0%E]_(i \in A) F%E) :
  ereal_scope.

Section ERealArith.
Context {R : numDomainType}.
Implicit Types x y z : \bar R.

Local Open Scope classical_set_scope.

Lemma preimage_abse_pinfty : @abse R @^-1` [set +oo] = [set -oo; +oo].
Proof.
by rewrite predeqE => y; split ; move: y => [y//| |]//=; [right | left | case].
Qed.

Lemma preimage_abse_ninfty : (@abse R @^-1` [set -oo])%classic = set0.
Proof.
rewrite predeqE => t; split => //=; apply/eqP.
by rewrite gt_eqF// (lt_le_trans _ (abse_ge0 t)).
Qed.

Lemma compreDr T (h : R -> \bar R) (f g : T -> R) :
  {morph h : x y / (x + y)%R >-> (x + y)%E} ->
  h \o (f \+ g)%R = ((h \o f) \+ (h \o g))%E.
Proof. by move=> mh; apply/funext => t /=; rewrite mh. Qed.

Lemma compreN T (h : R -> \bar R) (f : T -> R) :
  {morph h : x / (- x)%R >-> (- x)%E} ->
  h \o (\- f)%R = \- (h \o f)%E.
Proof. by move=> mh; apply/funext => t /=; rewrite mh. Qed.

Lemma compreBr T (h : R -> \bar R) (f g : T -> R) :
  {morph h : x y / (x - y)%R >-> (x - y)%E} ->
  h \o (f \- g)%R = ((h \o f) \- (h \o g))%E.
Proof. by move=> mh; apply/funext => t /=; rewrite mh. Qed.

Lemma compre_scale T (h : R -> \bar R) (f : T -> R) k :
  {morph h : x y / (x * y)%R >-> (x * y)%E} ->
  h \o (k \o* f) = (fun t => h k * h (f t))%E.
Proof. by move=> mf; apply/funext => t /=; rewrite mf; rewrite muleC. Qed.

Local Close Scope classical_set_scope.

End ERealArith.

Section ERealArithTh_numDomainType.
Context {R : numDomainType}.
Implicit Types (x y z : \bar R) (r : R).

Lemma range_oppe : range -%E = [set: \bar R]%classic.
Proof. by apply/seteqP; split => [//|x] _; exists (- x); rewrite ?oppeK. Qed.

Lemma oppe_subset (A B : set (\bar R)) :
  ((A `<=` B) <-> (-%E @` A `<=` -%E @` B))%classic.
Proof.
split=> [AB _ [] x ? <-|AB x Ax]; first by exists x => //; exact: AB.
have /AB[y By] : ((-%E @` A) (- x))%classic by exists x.
by rewrite eqe_oppP => <-.
Qed.

Lemma fsume_ge0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) -> 0 <= \sum_(i \in P) F i.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sume_ge0// => i /XP/PF.
Qed.

Lemma fsume_le0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  (forall t, P t -> F t <= 0) -> \sum_(i \in P) F i <= 0.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sume_le0// => i /XP/PF.
Qed.

Lemma fsumEFin (I : choiceType) A (F : I -> R) : finite_set A ->
  \sum_(i \in A) (F i)%:E = (\sum_(i \in A) F i)%:E.
Proof. by move=> fs; rewrite fsbig_finite//= sumEFin -fsbig_finite. Qed.

End ERealArithTh_numDomainType.

Section ERealArithTh_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y z u a b : \bar R) (r : R).

Lemma le_er_map_in (A : set R) (f : R -> R) :
  {in A &, {homo f : x y / (x <= y)%O}} ->
  {in (EFin @` A)%classic &, {homo er_map f : x y / (x <= y)%E}}.
Proof.
move=> h x y; rewrite !inE/= => -[r Ar <-{x}] [s As <-{y}].
by rewrite !lee_fin/= => /h; apply; rewrite inE.
Qed.

Lemma fsume_gt0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  0 < \sum_(i \in P) F i -> exists2 i, P i & 0 < F i.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsume_le0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma fsume_lt0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  \sum_(i \in P) F i < 0 -> exists2 i, P i & F i < 0.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsume_ge0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma pfsume_eq0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  finite_set P ->
  (forall i, P i -> 0 <= F i) ->
  \sum_(i \in P) F i = 0 -> forall i, P i -> F i = 0.
Proof.
move=> Pfin F0 /eqP; apply: contraTP => /existsPNP[i Pi /eqP Fi0].
rewrite (fsbigD1 i)//= padde_eq0 ?F0 ?negb_and ?Fi0//.
by rewrite fsume_ge0// => j [/F0->].
Qed.

Lemma lee_fsum_nneg_subset [T : choiceType] [A B : set T] [f : T -> \bar R] :
  finite_set A -> finite_set B ->
  {subset A <= B} -> {in [predD B & A], forall t : T, 0 <= f t}%E ->
  (\sum_(t \in A) f t <= \sum_(t \in B) f t)%E.
Proof.
move=> finA finB AB f0; rewrite !fsbig_finite//=; apply: lee_sum_nneg_subfset.
  by apply/fsubsetP; rewrite -fset_set_sub//; apply/subsetP.
by move=> t; rewrite !inE !in_fset_set// => /f0.
Qed.

Lemma lee_fsum [T : choiceType] (I : set T) (a b : T -> \bar R) :
  finite_set I ->
  (forall i, I i -> a i <= b i)%E -> (\sum_(i \in I) a i <= \sum_(i \in I) b i)%E.
Proof.
move=> finI ab.
rewrite !fsbig_finite// big_seq [in leRHS]big_seq lee_sum //.
by move=> i; rewrite in_fset_set// inE; exact: ab.
Qed.

Lemma ge0_mule_fsumr (T : choiceType) x (F : T -> \bar R) (P : set T) :
  (forall i : T, 0 <= F i) -> x * (\sum_(i \in P) F i) = \sum_(i \in P) x * F i.
Proof.
move=> F0; have [->{x}|x0] := eqVneq x 0%E.
  by rewrite mul0e big1// => ? _; rewrite mul0e.
rewrite ge0_sume_distrr//; apply: eq_fbigl => y.
rewrite !unlock; congr (_ \in fset_set _).
apply/seteqP; rewrite /preimage; split=> [|] z/= [Pz Fz0];
  split=> //; apply: contra_not Fz0.
by move=> /eqP; rewrite mule_eq0 (negbTE x0)/= => /eqP.
by move=> ->; rewrite mule0.
Qed.

Lemma ge0_mule_fsuml (T : choiceType) x (F : T -> \bar R) (P : set T) :
  (forall i : T, 0 <= F i) -> (\sum_(i \in P) F i) * x = \sum_(i \in P) F i * x.
Proof.
move=> F0; rewrite muleC ge0_mule_fsumr//.
by apply: eq_fsbigr => i; rewrite muleC.
Qed.

End ERealArithTh_realDomainType.
Arguments lee_fsum [R T I a b].

Module DualAddTheoryNumDomain.

Import DualAddTheory.

Section DualERealArithTh_numDomainType.

Local Open Scope ereal_dual_scope.

Context {R : numDomainType}.

Implicit Types x y z : \bar R.

Lemma finite_supportNe (I : choiceType) (P : set I) (F : I -> \bar R) :
  finite_support 0%E P (\- F)%E = finite_support 0%E P F.
Proof.
rewrite /finite_support !unlock; congr fset_set; congr setI.
by rewrite seteqP; split=> x /= /eqP + /ltac:(apply/eqP); rewrite oppe_eq0.
Qed.

Lemma dual_fsumeE (I : choiceType) (P : set I) (F : I -> \bar R) :
  (\sum_(i \in P) F i)%dE = (- (\sum_(i \in P) (- F i)))%E.
Proof.
rewrite finite_supportNe.
apply: (big_ind2 (fun x y => x = - y)%E) => [|_ x _ y -> ->|i _].
- by rewrite oppe0.
- by rewrite dual_addeE !oppeK.
- by rewrite oppeK.
Qed.

Lemma dfsume_ge0 (I : choiceType) (P : set I) (F : I -> \bar^d R) :
  (forall i, P i -> 0 <= F i) -> 0 <= \sum_(i \in P) F i.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr dsume_ge0// => i /XP/PF.
Qed.

Lemma dfsume_le0 (I : choiceType) (P : set I) (F : I -> \bar R) :
  (forall t, P t -> F t <= 0) -> \sum_(i \in P) F i <= 0.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr dsume_le0// => i /XP/PF.
Qed.

End DualERealArithTh_numDomainType.

Section DualERealArithTh_realDomainType.

Import DualAddTheory.

Local Open Scope ereal_dual_scope.

Context {R : realDomainType}.
Implicit Types x y z a b : \bar^d R.

Lemma dfsume_gt0 (I : choiceType) (P : set I) (F : I -> \bar^d R) :
  0 < \sum_(i \in P) F i -> exists2 i, P i & 0 < F i.
Proof.
rewrite dual_fsumeE oppe_gt0 => /fsume_lt0[i Pi].
by rewrite oppe_lt0 => ?; exists i.
Qed.

Lemma dfsume_lt0 (I : choiceType) (P : set I) (F : I -> \bar^d R) :
  \sum_(i \in P) F i < 0 -> exists2 i, P i & F i < 0.
Proof.
rewrite dual_fsumeE oppe_lt0 => /fsume_gt0[i Pi].
by rewrite oppe_gt0 => ?; exists i.
Qed.

Lemma pdfsume_eq0 (I : choiceType) (P : set I) (F : I -> \bar^d R) :
  finite_set P ->
  (forall i, P i -> 0 <= F i) ->
  \sum_(i \in P) F i = 0 -> forall i, P i -> F i = 0.
Proof.
move=> Pfin F0 /eqP; apply: contraTP => /existsPNP[i Pi /eqP Fi0].
rewrite (fsbigD1 i)//= pdadde_eq0 ?F0 ?negb_and ?Fi0//.
by rewrite dfsume_ge0// => j [/F0->].
Qed.

Lemma le0_mule_dfsumr (T : choiceType) x (F : T -> \bar^d R) (P : set T) :
  (forall i : T, F i <= 0) -> x * (\sum_(i \in P) F i) = \sum_(i \in P) x * F i.
Proof.
move=> Fge0.
rewrite !dual_fsumeE muleN ge0_mule_fsumr; last by move=> ?; rewrite oppe_ge0.
rewrite (eq_bigr _ (fun _ _ => muleN _ _)).
by rewrite (eq_finite_support _ (fun i _ => muleN _ _)).
Qed.

Lemma le0_mule_dfsuml (T : choiceType) x (F : T -> \bar^d R) (P : set T) :
  (forall i : T, F i <= 0) -> (\sum_(i \in P) F i) * x = \sum_(i \in P) F i * x.
Proof.
move=> F0; rewrite muleC le0_mule_dfsumr//.
by apply: eq_fsbigr => i; rewrite muleC.
Qed.

End DualERealArithTh_realDomainType.

End DualAddTheoryNumDomain.

Module DualAddTheory.
Export ConstructiveDualAddTheory.
Export DualAddTheoryNumDomain.
End DualAddTheory.

HB.instance Definition _ (R : numDomainType) := isPointed.Build (\bar R) 0%E.

Lemma funID {aT : pointedType} (D : set aT) {R : numDomainType}
  (f : aT -> \bar R) : f = (f \_ ~` D) \+ (f \_ D).
Proof.
by apply/funext => x; rewrite !patchE in_setC; case: ifPn => [xD|/negPn ->];
  rewrite ?(negbTE xD) ?(addr0,add0r).
Qed.

Section ereal_supremum.
Variable R : realFieldType.
Local Open Scope classical_set_scope.
Implicit Types (S : set (\bar R)) (x y : \bar R).

Lemma uboundT : ubound [set: \bar R] = [set +oo].
Proof.
apply/seteqP; split => /= [x Tx|x -> ?]; last by rewrite leey.
by apply/eqP; rewrite eq_le leey /= Tx.
Qed.

Lemma ereal_ub_pinfty S : ubound S +oo.
Proof. by apply/ubP=> x _; rewrite leey. Qed.

Lemma ereal_ub_ninfty S : ubound S -oo -> S = set0 \/ S = [set -oo].
Proof.
have [->|/set0P[x Sx] Snoo] := eqVneq S set0; first by left.
right; rewrite predeqE => y; split => [/Snoo|->{y}].
  by rewrite leeNy_eq => /eqP ->.
by have := Snoo _ Sx; rewrite leeNy_eq => /eqP <-.
Qed.

Lemma supremumsT : supremums [set: \bar R] = [set +oo].
Proof.
rewrite /supremums uboundT.
by apply/seteqP; split=> [x []//|x -> /=]; split => // y ->.
Qed.

Lemma ereal_supremums_set0_ninfty : supremums (@set0 (\bar R)) -oo.
Proof. by split; [exact/ubP | apply/lbP=> y _; rewrite leNye]. Qed.

Lemma supremumT : supremum -oo [set: \bar R] = +oo.
Proof.
rewrite /supremum (negbTE setT0) supremumsT.
by case: xgetP => // /(_ +oo)/= /eqP; rewrite eqxx.
Qed.

Lemma supremum_pinfty S x0 : S +oo -> supremum x0 S = +oo.
Proof.
move=> Spoo; rewrite /supremum ifF; last by apply/eqP => S0; rewrite S0 in Spoo.
have sSoo : supremums S +oo.
  split; first exact: ereal_ub_pinfty.
  by move=> /= y /(_ _ Spoo); rewrite leye_eq => /eqP ->.
case: xgetP.
  by move=> _ -> sSxget; move: (is_subset1_supremums sSoo sSxget).
by move/(_ +oo) => gSoo; exfalso; exact: gSoo.
Qed.

Definition ereal_sup S := supremum -oo S.

Definition ereal_inf S := - ereal_sup (-%E @` S).

Lemma ereal_sup0 : ereal_sup set0 = -oo. Proof. exact: supremum0. Qed.

Lemma ereal_supT : ereal_sup [set: \bar R] = +oo.
Proof. by rewrite /ereal_sup/= supremumT. Qed.

Lemma ereal_sup1 x : ereal_sup [set x] = x. Proof. exact: supremum1. Qed.

Lemma ereal_inf0 : ereal_inf set0 = +oo.
Proof. by rewrite /ereal_inf image_set0 ereal_sup0. Qed.

Lemma ereal_infT : ereal_inf [set: \bar R] = -oo.
Proof. by rewrite /ereal_inf range_oppe/= ereal_supT. Qed.

Lemma ereal_inf1 x : ereal_inf [set x] = x.
Proof. by rewrite /ereal_inf image_set1 ereal_sup1 oppeK. Qed.

Lemma ub_ereal_sup S M : ubound S M -> ereal_sup S <= M.
Proof.
rewrite /ereal_sup /supremum; case: ifPn => [/eqP ->|]; first by rewrite leNye.
- by move=> _ SM; case: xgetP => [_ -> [_]| _] /=; [exact |rewrite leNye].
Qed.

Lemma lb_ereal_inf S M : lbound S M -> M <= ereal_inf S.
Proof.
move=> SM; rewrite /ereal_inf leeNr; apply: ub_ereal_sup => x [y Sy <-{x}].
by rewrite leeNl oppeK; exact: SM.
Qed.

Lemma ub_ereal_sup_adherent S (e : R) : (0 < e)%R ->
  ereal_sup S \is a fin_num -> exists2 x, S x & (ereal_sup S - e%:E < x).
Proof.
move=> e0 Sr; have : ~ ubound S (ereal_sup S - e%:E).
  by move/ub_ereal_sup; apply/negP; rewrite -ltNge lteBlDr// lteDl// lte_fin.
move/asboolP; rewrite asbool_neg; case/existsp_asboolPn => /= x.
by rewrite not_implyE => -[? ?]; exists x => //; rewrite ltNge; apply/negP.
Qed.

Lemma lb_ereal_inf_adherent S (e : R) : (0 < e)%R ->
  ereal_inf S \is a fin_num -> exists2 x, S x & (x < ereal_inf S + e%:E).
Proof.
move=> e0; rewrite fin_numN => /(ub_ereal_sup_adherent e0)[x []].
move=> y Sy <-; rewrite -lteNr => /lt_le_trans ex; exists y => //.
by apply: ex; rewrite fin_num_oppeD// oppeK.
Qed.

Lemma ereal_sup_gt S x : x < ereal_sup S -> exists2 y, S y & x < y.
Proof.
rewrite not_exists2P => + g; apply/negP; rewrite -leNgt.
by apply: ub_ereal_sup => y Sy; move: (g y) => [//|/negP]; rewrite leNgt.
Qed.

Lemma ereal_inf_lt S x : ereal_inf S < x -> exists2 y, S y & y < x.
Proof.
rewrite lteNl => /ereal_sup_gt[_ [y Sy <-]].
by rewrite lteNl oppeK => xlty; exists y.
Qed.

Lemma ereal_infEN S : ereal_inf S = - ereal_sup [set - x | x in S].
Proof. by []. Qed.

Lemma ereal_supN S : ereal_sup [set - x | x in S] = - ereal_inf S.
Proof. by rewrite oppeK. Qed.

Lemma ereal_infN S : ereal_inf [set - x | x in S] = - ereal_sup S.
Proof.
rewrite /ereal_inf; congr (- ereal_sup _) => /=.
by rewrite image_comp/=; under eq_imagel do rewrite /= oppeK; rewrite image_id.
Qed.

Lemma ereal_supEN S : ereal_sup S = - ereal_inf [set - x | x in S].
Proof. by rewrite ereal_infN oppeK. Qed.

End ereal_supremum.

Section ereal_supremum_realType.
Variable R : realType.
Local Open Scope classical_set_scope.
Implicit Types S : set (\bar R).
Implicit Types x : \bar R.

Let fine_def r0 x : R := if x is r%:E then r else r0.
(* NB: see also fine above *)

Lemma ereal_supremums_neq0 S : supremums S !=set0.
Proof.
have [->|Snoo] := eqVneq S [set -oo].
  by exists -oo; split; [rewrite ub_set1 |exact: lb_ub_refl].
have [->|S0] := eqVneq S set0.
  by exists -oo; exact: ereal_supremums_set0_ninfty.
have [Spoo|Spoo] := pselect (S +oo).
  by exists +oo; split; [apply/ereal_ub_pinfty | apply/lbP => /= y /ubP; apply].
have [r Sr] : exists r, S r%:E.
  move: S0 => /set0P[] [r Sr| // |Snoo1]; first by exists r.
  apply/not_existsP => nS; move/negP : Snoo; apply.
  by apply/eqP; rewrite predeqE => -[] // r; split => // /nS.
set U := fine_def r @` S.
have [|] := eqVneq (ubound U) set0.
  rewrite -subset0 => U0; exists +oo.
  split; [exact/ereal_ub_pinfty | apply/lbP => /= -[r0 /ubP Sr0|//|]].
  - suff : ubound U r0 by move/U0.
    by apply/ubP=> _ -[] [r1 Sr1 <-|//| /= _ <-]; rewrite -lee_fin; exact: Sr0.
  - by move/ereal_ub_ninfty => [|]; by [move/eqP : S0|move/eqP : Snoo].
set u : R := sup U.
exists u%:E; split; last first.
  apply/lbP=> -[r0 /ubP Sr0| |].
  - rewrite lee_fin; apply/sup_le_ub; first by exists r, r%:E.
    by apply/ubP => _ -[[r2 ? <-| // | /= _ <-]]; rewrite -lee_fin; exact: Sr0.
  - by rewrite leey.
  - by move/ereal_ub_ninfty=> [|/eqP //]; [move/eqP : S0|rewrite (negbTE Snoo)].
apply/ubP => -[r0 Sr0|//|_]; last by rewrite leNye.
rewrite lee_fin.
suff : has_sup U by move/sup_upper_bound/ubP; apply; exists r0%:E.
split; first by exists r0, r0%:E.
exists u; apply/ubP => y; move=> [] y' Sy' <-{y}.
have : has_sup U by split; [exists r, r%:E | exact/set0P].
move/sup_upper_bound/ubP; apply.
by case: y' Sy' => [r1 /= Sr1 | // | /= _]; [exists r1%:E | exists r%:E].
Qed.

Lemma ereal_sup_ubound S : ubound S (ereal_sup S).
Proof.
move=> y Sy; rewrite /ereal_sup /supremum ifF; last first.
  by apply/eqP; rewrite predeqE => /(_ y)[+ _]; exact.
case: xgetP => /=; first by move=> _ -> -[] /ubP geS _; apply: geS.
by case: (ereal_supremums_neq0 S) => /= x0 Sx0 /(_ x0).
Qed.

Lemma ereal_supy S : S +oo -> ereal_sup S = +oo.
Proof.
by move=> Soo; apply/eqP; rewrite eq_le leey/=; exact: ereal_sup_ubound.
Qed.

Lemma ereal_sup_ge S x : (exists2 y, S y & x <= y) -> x <= ereal_sup S.
Proof. by move=> [y Sy] /le_trans; apply; exact: ereal_sup_ubound. Qed.

Lemma ereal_sup_ninfty S : ereal_sup S = -oo <-> S `<=` [set -oo].
Proof.
split.
  by move=> supS [r /ereal_sup_ubound|/ereal_sup_ubound|//]; rewrite supS.
by move=> /(@subset_set1 _ S) [] ->; [exact: ereal_sup0|exact: ereal_sup1].
Qed.

Lemma ereal_inf_lbound S : lbound S (ereal_inf S).
Proof.
by move=> x Sx; rewrite /ereal_inf leeNl; apply: ereal_sup_ubound; exists x.
Qed.

Lemma ereal_inf_le S x : (exists2 y, S y & y <= x) -> ereal_inf S <= x.
Proof. by move=> [y Sy]; apply: le_trans; exact: ereal_inf_lbound. Qed.

Lemma ereal_inf_pinfty S : ereal_inf S = +oo <-> S `<=` [set +oo].
Proof. rewrite eqe_oppLRP oppe_subset image_set1; exact: ereal_sup_ninfty. Qed.

Lemma le_ereal_sup : {homo @ereal_sup R : A B / A `<=` B >-> A <= B}.
Proof.
by move=> A B AB; apply: ub_ereal_sup => x Ax; exact/ereal_sup_ubound/AB.
Qed.

Lemma le_ereal_inf : {homo @ereal_inf R : A B / A `<=` B >-> B <= A}.
Proof.
by move=> A B AB; apply: lb_ereal_inf => x Bx; exact/ereal_inf_lbound/AB.
Qed.

Lemma hasNub_ereal_sup (A : set R) : ~ has_ubound A ->
  A !=set0 -> ereal_sup (EFin @` A) = +oo%E.
Proof.
move=> + A0; apply: contra_notP => /eqP; rewrite -ltey => Aoo.
exists (fine (ereal_sup (EFin @` A))) => x Ax.
rewrite -lee_fin -(@fineK _ x%:E)// lee_fin fine_le//; last first.
  by apply: ereal_sup_ubound => /=; exists x.
rewrite fin_numE// -ltey Aoo andbT.
apply/eqP => /ereal_sup_ninfty/(_ x%:E).
by have /[swap] /[apply]: (EFin @` A) x%:E by exists x.
Qed.

Lemma ereal_sup_EFin (A : set R) :
  has_ubound A -> A !=set0 -> ereal_sup (EFin @` A) = (sup A)%:E.
Proof.
move=> has_ubA A0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ub_ereal_sup => /= y [r Ar <-{y}]; rewrite lee_fin sup_ubound.
set esup := ereal_sup _; have := leey esup.
rewrite [X in _ X]le_eqVlt => /predU1P[->|esupoo]; first by rewrite leey.
have := leNye esup; rewrite [in X in X -> _]le_eqVlt => /predU1P[/esym|ooesup].
  case: A0 => i Ai.
  by move=> /ereal_sup_ninfty /(_ i%:E) /(_ (ex_intro2 A _ i Ai erefl)).
have esup_fin_num : esup \is a fin_num.
  by rewrite fin_numE -leeNy_eq -ltNge ooesup /= -leye_eq -ltNge esupoo.
rewrite -(@fineK _ esup) // lee_fin leNgt.
apply/negP => /(sup_gt A0)[r Ar]; apply/negP; rewrite -leNgt.
by rewrite -lee_fin fineK//; apply: ereal_sup_ubound; exists r.
Qed.

Lemma ereal_inf_EFin (A : set R) : has_lbound A -> A !=set0 ->
  ereal_inf (EFin @` A) = (inf A)%:E.
Proof.
move=> has_lbA A0; rewrite /ereal_inf /inf EFinN; congr (- _)%E.
rewrite -ereal_sup_EFin; [|exact/has_lb_ubN|exact/nonemptyN].
by rewrite !image_comp.
Qed.

Lemma ereal_supP S x :
  reflect (forall y : \bar R, S y -> y <= x) (ereal_sup S <= x).
Proof.
apply/(iffP idP) => [+ y Sy|].
  by move=> /(le_trans _)->//; rewrite ereal_sup_ge//; exists y.
apply: contraPP => /negP; rewrite -ltNge -existsPNP.
by move=> /ereal_sup_gt[y Sy ltyx]; exists y => //; rewrite lt_geF.
Qed.

Lemma ereal_infP S x :
  reflect (forall y : \bar R, S y -> x <= y) (x <= ereal_inf S).
Proof.
rewrite leeNr; apply/(equivP (ereal_supP _ _)); setoid_rewrite leeNr.
split=> [ge_x y Sy|ge_x _ [y Sy <-]]; rewrite ?oppeK// ?ge_x//.
by rewrite -[y]oppeK ge_x//; exists y.
Qed.

Lemma ereal_sup_gtP S x :
  reflect (exists2 y : \bar R, S y & x < y) (x < ereal_sup S).
Proof.
rewrite ltNge; apply/(equivP negP); rewrite -(rwP (ereal_supP _ _)) -existsPNP.
by apply/eq_exists2r => y; rewrite (rwP2 negP idP) -ltNge.
Qed.

Lemma ereal_inf_ltP S x :
  reflect (exists2 y : \bar R, S y & y < x) (ereal_inf S < x).
Proof.
rewrite ltNge; apply/(equivP negP); rewrite -(rwP (ereal_infP _ _)) -existsPNP.
by apply/eq_exists2r => y; rewrite (rwP2 negP idP) -ltNge.
Qed.

Lemma ereal_inf_leP S x : S (ereal_inf S) ->
  reflect (exists2 y : \bar R, S y & y <= x) (ereal_inf S <= x).
Proof.
move=> Sinf; apply: (iffP idP); last exact: ereal_inf_le.
by move=> Sx; exists (ereal_inf S).
Qed.

Lemma ereal_sup_geP S x : S (ereal_sup S) ->
  reflect (exists2 y : \bar R, S y & x <= y) (x <= ereal_sup S).
Proof.
move=> Ssup; apply: (iffP idP); last exact: ereal_sup_ge.
by move=> Sx; exists (ereal_sup S).
Qed.

Lemma lb_ereal_infNy_adherent S e :
  ereal_inf S = -oo -> exists2 x : \bar R, S x & x < e%:E.
Proof. by move=> infNy; apply/ereal_inf_ltP; rewrite infNy ltNyr. Qed.

Lemma ereal_sup_real : @ereal_sup R (range EFin) = +oo.
Proof.
rewrite hasNub_ereal_sup//; last by exists 0%R.
by apply/has_ubPn => x; exists (x+1)%R => //; rewrite ltrDl.
Qed.

Lemma ereal_inf_real : @ereal_inf R (range EFin) = -oo.
Proof.
rewrite /ereal_inf [X in ereal_sup X](_ : _ = range EFin); last first.
  apply/seteqP; split => x/=[y].
    by move=> [z] _ <- <-; exists (-z)%R.
  by move=> _ <-; exists (-y%:E); first (by exists (-y)%R); rewrite oppeK.
by rewrite ereal_sup_real.
Qed.

End ereal_supremum_realType.
#[deprecated(since="mathcomp-analysis 1.3.0", note="Renamed `ereal_sup_ubound`.")]
Notation ereal_sup_ub := ereal_sup_ubound (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="Renamed `ereal_inf_lbound`.")]
Notation ereal_inf_lb := ereal_inf_lbound (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="Renamed `ereal_sup_ge`.")]
Notation ereal_sup_le := ereal_sup_ge.

Arguments ereal_supP {R S x}.
Arguments ereal_infP {R S x}.
Arguments ereal_sup_gtP {R S x}.
Arguments ereal_inf_ltP {R S x}.
Arguments ereal_sup_geP {R S x}.
Arguments ereal_inf_leP {R S x}.

Lemma restrict_abse T (R : numDomainType) (f : T -> \bar R) (D : set T) :
  (abse \o f) \_ D = abse \o (f \_ D).
Proof.
by apply/funext=> t; rewrite /restrict/=; case: ifPn => // _; rewrite abse0.
Qed.

Lemma restrict_EFin T (R : numFieldType) (f : T -> R) (D : set T) :
  (EFin \o f) \_ D = EFin \o (f \_ D).
Proof. by apply/funext => x; rewrite /= !patchE; case: ifPn. Qed.

Section SignedRealFieldStability.
Context {R : realFieldType}.

Lemma ext_num_spec_ereal_sup i (S : Itv.def (@ext_num_sem R) i -> Prop)
    (r := Itv.real1 IntItv.keep_nonpos i) :
  Itv.spec (@ext_num_sem R) r (ereal_sup [set x%:num | x in S]).
Proof.
rewrite {}/r; case: i S => [//| [l u]] S /=.
apply/and3P; split.
- rewrite real_fine -real_leey.
  by rewrite ub_ereal_sup// => _ [[[x||] /=/and3P[? ? ?]] _ <-].
- by case: ereal_sup.
- case: u S => [[] [[| u] | u] S |//]; rewrite /= bnd_simp//;
     apply: ub_ereal_sup => _ [[x /=/and3P[_ _ /= +]] _ <-]; rewrite bnd_simp//.
  + by move/ltW.
  + by move=> /ltW /le_trans; apply; rewrite lee_fin lerz0.
  + by move=> /le_trans; apply; rewrite lee_fin lerz0.
Qed.

Canonical ereal_sup_inum i (S : Itv.def (@ext_num_sem R) i -> Prop) :=
  Itv.mk (ext_num_spec_ereal_sup S).

Lemma ext_num_spec_ereal_inf i (S : Itv.def (@ext_num_sem R) i -> Prop)
    (r := Itv.real1 IntItv.keep_nonneg i) :
  Itv.spec (@ext_num_sem R) r (ereal_inf [set x%:num | x in S]).
Proof.
rewrite {}/r; case: i S => [//| [l u]] S /=.
apply/and3P; split.
- rewrite real_fine -real_leNye.
  by rewrite lb_ereal_inf// => _ [[[x||] /=/and3P[? ? ?]] _ <-].
- case: l S => [[] [l | l] S |//]; rewrite /= bnd_simp//;
     apply: lb_ereal_inf => _ [[x /=/and3P[_ /= + _]] _ <-]; rewrite bnd_simp.
  + by apply: le_trans; rewrite lee_fin ler0z.
  + by move=> /ltW; apply: le_trans; rewrite lee_fin ler0z.
- by case: ereal_inf.
Qed.

Canonical ereal_inf_inum i (S : Itv.def (@ext_num_sem R) i -> Prop) :=
  Itv.mk (ext_num_spec_ereal_inf S).

End SignedRealFieldStability.

Section ereal_nbhs.
Context {R : numFieldType}.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Definition ereal_dnbhs (x : \bar R) : set_system (\bar R) :=
  [set P | match x with
    | r%:E => r^' (fun r => P r%:E)
    | +oo => exists M, M \is Num.real /\ forall y, M%:E < y -> P y
    | -oo => exists M, M \is Num.real /\ forall y, y < M%:E -> P y
  end].
Definition ereal_nbhs (x : \bar R) : set_system (\bar R) :=
  [set P | match x with
    | x%:E => nbhs x (fun r => P r%:E)
    | +oo => exists M, M \is Num.real /\ forall y, M%:E < y -> P y
    | -oo => exists M, M \is Num.real /\ forall y, y < M%:E -> P y
  end].
HB.instance Definition _ := hasNbhs.Build (\bar R) ereal_nbhs.
End ereal_nbhs.

Section ereal_nbhs_instances.
Context {R : numFieldType}.

Global Instance ereal_dnbhs_filter :
  forall x : \bar R, ProperFilter (ereal_dnbhs x).
Proof.
case=> [x| |].
- case: (Proper_dnbhs_numFieldType x) => x0 [//= xT xI xS].
    by apply: Build_ProperFilter => //=; exact: Build_Filter.
- apply: Build_ProperFilter_ex.
    move=> P [x [xr xP]] //; exists (x + 1)%:E; apply: xP => /=.
    by rewrite lte_fin ltrDl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0%R.
  + have [MP0|MP0] := eqVneq MP 0%R.
      have [MQ0|MQ0] := eqVneq MQ 0%R.
        by exists 0%R; split => // x x0; split;
          [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|%R; rewrite realE normr_ge0; split => // x MQx; split.
        by apply: gtMP; rewrite (le_lt_trans _ MQx) // MP0 lee_fin.
      apply: gtMQ.
      by rewrite (le_lt_trans _ MQx)// lee_fin real_ler_normr ?lexx.
    have [MQ0|MQ0] := eqVneq MQ 0%R.
      exists `|MP|%R; rewrite realE normr_ge0; split => // x MPx; split.
        apply: gtMP.
        by rewrite (le_lt_trans _ MPx)// lee_fin real_ler_normr ?lexx.
      by apply: gtMQ; rewrite (le_lt_trans _ MPx) // lee_fin MQ0.
    have {}MP0 : (0 < `|MP|)%R by rewrite normr_gt0.
    have {}MQ0 : (0 < `|MQ|)%R by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= ge0 /=; split => //.
    case=> [r| |//].
    * rewrite lte_fin/= num_max num_gt_max /= => /andP[MPx MQx]; split.
      by apply/gtMP; rewrite lte_fin (le_lt_trans _ MPx)// real_ler_normr ?lexx.
      by apply/gtMQ; rewrite lte_fin (le_lt_trans _ MQx)// real_ler_normr ?lexx.
    * by move=> _; split; [apply/gtMP | apply/gtMQ].
  + by exists M; split => // ? /gtM /sPQ.
- apply: Build_ProperFilter_ex.
  + move=> P [M [Mr ltMP]]; exists (M - 1)%:E.
    by apply: ltMP; rewrite lte_fin gtrDl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0%R.
    * have [MP0|MP0] := eqVneq MP 0%R.
        have [MQ0|MQ0] := eqVneq MQ 0%R.
          by exists 0%R; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|)%R; rewrite realN realE normr_ge0; split => // x xMQ.
        split.
          by apply: ltMP; rewrite (lt_le_trans xMQ)// lee_fin MP0 lerNl oppr0.
       apply: ltMQ; rewrite (lt_le_trans xMQ) // lee_fin lerNl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [MQ0|MQ0] := eqVneq MQ 0%R.
        exists (- `|MP|)%R; rewrite realN realE normr_ge0; split => // x MPx.
        split.
          apply: ltMP; rewrite (lt_le_trans MPx) // lee_fin lerNl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        by apply: ltMQ; rewrite (lt_le_trans MPx) // lee_fin MQ0 lerNl oppr0.
      have {}MP0 : (0 < `|MP|)%R by rewrite normr_gt0.
      have {}MQ0 : (0 < `|MQ|)%R by rewrite normr_gt0.
      exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num)%R.
      rewrite realN realE /= ge0 /=; split => //.
      case=> [r|//|].
      - rewrite lte_fin ltrNr num_max num_gt_max => /andP[].
        rewrite ltrNr => MPx; rewrite ltrNr => MQx; split.
          apply/ltMP; rewrite lte_fin (lt_le_trans MPx) //= lerNl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        apply/ltMQ; rewrite lte_fin (lt_le_trans MQx) //= lerNl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      - by move=> _; split; [apply/ltMP | apply/ltMQ].
    * by exists M; split => // x /ltM /sPQ.
Qed.
Typeclasses Opaque ereal_dnbhs.

Global Instance ereal_nbhs_filter : forall x, ProperFilter (@ereal_nbhs R x).
Proof.
case=> [r| |].
- case: (ereal_dnbhs_filter r%:E) => r0 [//= nrT rI rS].
  apply: Build_ProperFilter_ex => P /nbhs_ballP[r2 r20 rr2].
  by exists r%:E; exact/rr2/ballxx.
- exact: (ereal_dnbhs_filter +oo).
- exact: (ereal_dnbhs_filter -oo).
Qed.
Typeclasses Opaque ereal_nbhs.

End ereal_nbhs_instances.

Section ereal_nbhs_infty.
Context (R : numFieldType).
Implicit Type r : R.

Lemma ereal_nbhs_pinfty_gt r : r \is Num.real -> \forall x \near +oo, r%:E < x.
Proof. by exists r. Qed.

Lemma ereal_nbhs_pinfty_ge r : r \is Num.real -> \forall x \near +oo, r%:E <= x.
Proof. by exists r; split => //; apply: ltW. Qed.

Lemma ereal_nbhs_ninfty_lt r : r \is Num.real -> \forall x \near -oo, r%:E > x.
Proof. by exists r. Qed.

Lemma ereal_nbhs_ninfty_le r : r \is Num.real -> \forall x \near -oo, r%:E >= x.
Proof. by exists r; split => // ?; apply: ltW. Qed.

Lemma ereal_nbhs_pinfty_real : \forall x \near +oo, fine x \is @Num.real R.
Proof.
apply: filterS (ereal_nbhs_pinfty_gt (@real0 _)) => x.
by case: x => //= x; apply: gtr0_real.
Qed.

Lemma ereal_nbhs_ninfty_real : \forall x \near -oo, fine x \is @Num.real R.
Proof.
apply: filterS (ereal_nbhs_ninfty_lt (@real0 _)) => x.
by case: x => //= x; apply: ltr0_real.
Qed.

End ereal_nbhs_infty.

Section ereal_topologicalType.
Variable R : realFieldType.

Lemma ereal_nbhs_singleton (p : \bar R) (A : set (\bar R)) :
  ereal_nbhs p A -> A p.
Proof.
move: p => -[p | [M [Mreal MA]] | [M [Mreal MA]]] /=; [|exact: MA | exact: MA].
move=> /nbhs_ballP[_/posnumP[e]]; apply; exact/ballxx.
Qed.

Lemma ereal_nbhs_nbhs (p : \bar R) (A : set (\bar R)) :
  ereal_nbhs p A -> ereal_nbhs p (ereal_nbhs^~ A).
Proof.
move: p => -[p| [M [Mreal MA]] | [M [Mreal MA]]] //=.
- move=> /nbhs_ballP[_/posnumP[e]] ballA.
  apply/nbhs_ballP; exists (e%:num / 2) => //= r per.
  apply/nbhs_ballP; exists (e%:num / 2) => //= x rex.
  apply/ballA/(@ball_splitl _ _ r) => //; exact/ball_sym.
- exists (M + 1)%R; split; first by rewrite realD.
  move=> -[x| _ |_] //=; last by exists M.
  rewrite lte_fin => M'x /=.
  apply/nbhs_ballP; exists 1%R => //= y x1y.
  apply: MA; rewrite lte_fin.
  rewrite addrC -ltrBrDl in M'x.
  rewrite (lt_le_trans M'x) // lerBlDl addrC -lerBlDl.
  rewrite (le_trans _ (ltW x1y)) // real_ler_norm // realB //.
    rewrite ltrBrDr in M'x.
    rewrite -comparabler0 (@comparabler_trans _ (M + 1)%R) //.
      by rewrite /Order.comparable (ltW M'x) orbT.
    by rewrite comparabler0 realD.
  by rewrite num_real. (* where we really use realFieldType *)
- exists (M - 1)%R; split; first by rewrite realB.
  move=> -[x| _ |_] //=; last by exists M.
  rewrite lte_fin => M'x /=.
  apply/nbhs_ballP; exists 1%R => //= y x1y.
  apply: MA; rewrite lte_fin.
  rewrite ltrBrDl in M'x.
  rewrite (le_lt_trans _ M'x) // addrC -lerBlDl.
  rewrite (le_trans _ (ltW x1y)) // distrC real_ler_norm // realB //.
    by rewrite num_real. (* where we really use realFieldType *)
  rewrite addrC -ltrBrDr in M'x.
  rewrite -comparabler0 (@comparabler_trans _ (M - 1)%R) //.
    by rewrite /Order.comparable (ltW M'x).
  by rewrite comparabler0 realB.
Qed.

End ereal_topologicalType.

Local Open Scope classical_set_scope.

Lemma nbhsNe (R : realFieldType) (x : \bar R) :
  nbhs (- x) = [set (-%E @` A) | A in nbhs x].
Proof.
case: x => [r /=| |].
- rewrite /nbhs /= /ereal_nbhs -nbhs_ballE.
  rewrite predeqE => S; split => [[_/posnumP[e] reS]|[S' [_ /posnumP[e] reS' <-]]].
    exists (-%E @` S).
      exists e%:num => //= r1 rer1; exists (- r1%:E); last by rewrite oppeK.
      by apply: reS; rewrite /ball /= opprK -normrN opprD opprK.
    rewrite predeqE => s; split => [[y [z Sz] <- <-]|Ss].
      by rewrite oppeK.
    by exists (- s); [exists s | rewrite oppeK].
  exists e%:num => //= r1 rer1; exists (- r1%:E); last by rewrite oppeK.
  by apply: reS'; rewrite /ball /= opprK -normrN opprD.
- rewrite predeqE => S; split=> [[M [Mreal MS]]|[x [M [Mreal Mx]] <-]].
    exists (-%E @` S).
      exists (- M)%R; rewrite realN Mreal; split => // x Mx.
      by exists (- x); [apply: MS; rewrite lteNl | rewrite oppeK].
    rewrite predeqE => x; split=> [[y [z Sz <- <-]]|Sx]; first by rewrite oppeK.
    by exists (- x); [exists x | rewrite oppeK].
  exists (- M)%R; rewrite realN; split => // y yM.
  exists (- y); by [apply: Mx; rewrite lteNr|rewrite oppeK].
- rewrite predeqE => S; split=> [[M [Mreal MS]]|[x [M [Mreal Mx]] <-]].
    exists (-%E @` S).
      exists (- M)%R; rewrite realN Mreal; split => // x Mx.
      by exists (- x); [apply: MS; rewrite lteNr | rewrite oppeK].
    rewrite predeqE => x; split=> [[y [z Sz <- <-]]|Sx]; first by rewrite oppeK.
    by exists (- x); [exists x | rewrite oppeK].
  exists (- M)%R; rewrite realN; split => // y yM.
  exists (- y); by [apply: Mx; rewrite lteNl|rewrite oppeK].
Qed.

Lemma nbhsNKe (R : realFieldType) (z : \bar R) (A : set (\bar R)) :
  nbhs (- z) (-%E @` A) -> nbhs z A.
Proof.
rewrite nbhsNe => -[S zS] SA; rewrite -(oppeK z) nbhsNe.
exists (-%E @` S); first by rewrite nbhsNe; exists S.
rewrite predeqE => x; split => [[y [u Su <-{y} <-]]|Ax].
  rewrite oppeK.
  move: SA; rewrite predeqE => /(_ (- u)) [h _].
  have : (exists2 y, S y & - y = - u) by exists u.
  by move/h => -[y Ay] /eqP; rewrite eqe_opp => /eqP <-.
exists (- x); last by rewrite oppeK.
exists x => //.
move: SA; rewrite predeqE => /(_ (- x)) [_ h].
have : (-%E @` A) (- x) by exists x.
by move/h => [y Sy] /eqP; rewrite eqe_opp => /eqP <-.
Qed.

Lemma oppe_continuous (R : realFieldType) :
  continuous (-%E : \bar R -> \bar R).
Proof.
move=> x S /= xS; apply: nbhsNKe; rewrite image_preimage //.
by rewrite predeqE => y; split => // _; exists (- y) => //; rewrite oppeK.
Qed.

Section contract_expand.
Variable R : realFieldType.
Implicit Types (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma contract_imageN (S : set (\bar R)) :
  (@contract R) @` (-%E @` S) = -%R @` ((@contract R) @` S).
Proof.
rewrite predeqE => r; split => [[y [z Sz <-{y} <-{r}]]|[s [y Sy <-{s} <-{r}]]].
by exists (contract z); [exists z | rewrite contractN].
by exists (- y); [exists y | rewrite contractN].
Qed.

Lemma contractK : cancel (@contract R) (@expand R).
Proof.
apply: (onS_can [pred r | `|r| <= 1]%R (@contract_le1 R)).
exact: inj_can_sym_on (@expandK R) (on2W (@contract_inj R)).
Qed.

Lemma bijective_contract : {on [pred r | `|r| <= 1]%R, bijective (@contract R)}.
Proof. exists (@expand R); [exact: in1W contractK | exact: (@expandK R)]. Qed.

Definition le_expandLR := monoLR_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) (@le_expand_in R).
Definition lt_expandLR := monoLR_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) (@lt_expand R).
Definition le_expandRL := monoRL_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) (@le_expand_in R).
Definition lt_expandRL := monoRL_in
  (in_onW_can _ predT contractK) (fun x _ => contract_le1 x) (@lt_expand R).

Lemma contract_eq0 x : (contract x == 0%R) = (x == 0).
Proof. by rewrite -(can_eq contractK) contract0. Qed.

Lemma contract_eqN1 x : (contract x == -1) = (x == -oo).
Proof. by rewrite -(can_eq contractK). Qed.

Lemma contract_eq1 x : (contract x == 1%R) = (x == +oo).
Proof. by rewrite -(can_eq contractK). Qed.

End contract_expand.

Section contract_expand_realType.
Variable R : realType.

Let contract := @contract R.

Lemma sup_contract_le1 S : S !=set0 -> (`|sup (contract @` S)| <= 1)%R.
Proof.
case=> x Sx; rewrite ler_norml; apply/andP; split; last first.
  apply: sup_le_ub; first by exists (contract x), x.
  by move=> r [y Sy] <-; case/ler_normlP : (contract_le1 y).
rewrite (@le_trans _ _ (contract x)) //.
  by case/ler_normlP : (contract_le1 x); rewrite lerNl.
apply: sup_ubound; last by exists x.
by exists 1%R => r [y Sy <-]; case/ler_normlP : (contract_le1 y).
Qed.

Lemma contract_sup S : S !=set0 -> contract (ereal_sup S) = sup (contract @` S).
Proof.
move=> S0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: sup_le_ub.
    by case: S0 => x Sx; exists (contract x), x.
  by move=> x [y Sy] <-{x}; rewrite le_contract; exact/ereal_sup_ubound.
rewrite leNgt; apply/negP.
set supc := sup _; set csup := contract _; move=> ltsup.
suff [y [ysupS ?]] : exists y, y < ereal_sup S /\ ubound S y.
  have : ereal_sup S <= y by exact: ub_ereal_sup.
  by move/(lt_le_trans ysupS); rewrite ltxx.
suff [x [? [ubSx x1]]] : exists x, (x < csup)%R /\ ubound (contract @` S) x /\
    (`|x| <= 1)%R.
  exists (expand x); split => [|y Sy].
    by rewrite -(contractK (ereal_sup S)) lt_expand // inE // contract_le1.
  by rewrite -(contractK y) le_expand //; apply: ubSx; exists y.
exists ((supc + csup) / 2); split; first by rewrite midf_lt.
split => [r [y Sy <-{r}]|].
  rewrite (@le_trans _ _ supc) ?midf_le //; last by rewrite ltW.
  apply: sup_ubound; last by exists y.
  by exists 1%R => r [z Sz <-]; case/ler_normlP : (contract_le1 z).
rewrite ler_norml; apply/andP; split; last first.
  rewrite ler_pdivrMr // mul1r (_ : 2 = 1 + 1)%R // lerD //.
  by case/ler_normlP : (sup_contract_le1 S0).
  by case/ler_normlP : (contract_le1 (ereal_sup S)).
rewrite ler_pdivlMr // (_ : 2 = 1 + 1)%R // mulN1r opprD lerD //.
by case/ler_normlP : (sup_contract_le1 S0); rewrite lerNl.
by case/ler_normlP : (contract_le1 (ereal_sup S)); rewrite lerNl.
Qed.

Lemma contract_inf S : S !=set0 -> contract (ereal_inf S) = inf (contract @` S).
Proof.
move=> -[x Sx]; rewrite /ereal_inf /contract (contractN (ereal_sup (-%E @` S))).
by rewrite -/contract contract_sup /inf;
  [rewrite contract_imageN|exists (- x), x].
Qed.

End contract_expand_realType.

Section ereal_PseudoMetric.
Variable R : realFieldType.
Implicit Types (x y : \bar R) (r : R).

Lemma le_ereal_ball x : {homo ereal_ball x : e e' / (e <= e')%R >-> e `<=` e'}.
Proof. by move=> e e' ee' y; rewrite /ereal_ball => /lt_le_trans; exact. Qed.

Lemma expand_ereal_ball_pinfty {e : {posnum R}} r : (e%:num <= 1)%R ->
  expand (1 - e%:num)%R < r%:E -> ereal_ball +oo e%:num r%:E.
Proof.
move=> e1 er; rewrite /ereal_ball gtr0_norm ?subr_gt0; last first.
  by case/ltr_normlP : (contract_lt1 r).
rewrite ltrBlDl addrC -ltrBlDl -[ltLHS]expandK ?lt_contract//.
by rewrite inE ger0_norm ?lerBlDl ?lerDr // subr_ge0.
Qed.

Lemma contract_ereal_ball_fin_le r r' (e : {posnum R}) : (r <= r')%R ->
  (1 <= contract r%:E + e%:num)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-{r'} _|rr' re1]; first exact: ereal_ball_center.
rewrite /ereal_ball ltr0_norm; last by rewrite subr_lt0 lt_contract lte_fin.
rewrite opprB ltrBlDl (lt_le_trans _ re1) //.
by case/ltr_normlP : (contract_lt1 r').
Qed.

Lemma contract_ereal_ball_fin_lt r r' (e : {posnum R}) : (r' < r)%R ->
  (contract r%:E - e%:num <= -1)%R  -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r reN1; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
rewrite ltrBlDl addrC -ltrBlDl (le_lt_trans reN1) //.
by move: (contract_lt1 r'); rewrite ltr_norml => /andP[].
Qed.

Lemma expand_ereal_ball_fin_lt r' r (e : {posnum R}) : (r' < r)%R ->
  expand (contract r%:E - e%:num)%R < r'%:E ->
  (`|contract r%:E - e%:num| < 1)%R -> ereal_ball r%:E e%:num r'%:E.
Proof.
move=> r'r ? r'e'r.
rewrite /ereal_ball gtr0_norm ?subr_gt0 ?lt_contract ?lte_fin//.
by rewrite ltrBlDl addrC -ltrBlDl -lt_expandLR ?inE ?ltW.
Qed.

Lemma ball_ereal_ball_fin_lt r r' (e : {posnum R}) :
  let e' := (r - fine (expand (contract r%:E - e%:num)))%R in
  ball r e' r' -> (r' < r)%R ->
  (`|contract r%:E - (e)%:num| < 1)%R ->
  ereal_ball r%:E e%:num r'%:E.
Proof.
move=> e' re'r' rr' X; rewrite /ereal_ball.
rewrite gtr0_norm ?subr_gt0// ?lt_contract ?lte_fin//.
move: re'r'.
rewrite /ball /= gtr0_norm // ?subr_gt0// /e'.
rewrite -ltrBlDl addrAC subrr add0r ltrNl opprK -lte_fin.
rewrite fine_expand // lt_expandLR ?inE ?ltW//.
by rewrite ltrBlDl addrC -ltrBlDl.
Qed.

Lemma ball_ereal_ball_fin_le r r' (e : {posnum R}) :
  let e' : R := (fine (expand (contract r%:E + e%:num)) - r)%R in
  ball r e' r' -> (r <= r')%R ->
  (`| contract r%:E + e%:num | < 1)%R ->
  ereal_ball r%:E e%:num r'%:E.
Proof.
move=> e' r'e'r rr' re1; rewrite /ereal_ball.
move: rr'; rewrite le_eqVlt => /predU1P[->|rr']; first by rewrite subrr normr0.
rewrite /ball /= ltr0_norm ?subr_lt0// opprB in r'e'r.
rewrite ltr0_norm ?subr_lt0 ?lt_contract ?lte_fin//.
rewrite opprB; move: r'e'r.
rewrite /e' -ltrBlDr opprK subrK -lte_fin fine_expand //.
by rewrite lt_expandRL ?inE ?ltW// ltrBlDl.
Qed.

Lemma nbhs_oo_up_e1 (A : set (\bar R)) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 ooeA.
exists (fine (expand (1 - e%:num)%R)); rewrite num_real; split => //.
case => [r | | //].
- rewrite fine_expand; last first.
    by rewrite ger0_norm ?ltrBlDl ?ltrDr // subr_ge0.
  by move=> ?; exact/ooeA/expand_ereal_ball_pinfty.
- by move=> _; exact/ooeA/ereal_ball_center.
Qed.

Lemma nbhs_oo_down_e1 (A : set (\bar R)) (e : {posnum R}) : (e%:num <= 1)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; suff h : nbhs +oo (-%E @` A).
  rewrite (_ : -oo = - +oo) // nbhsNe; exists (-%E @` A) => //.
  rewrite predeqE => x; split=> [[y [z Az <- <-]]|Ax]; rewrite ?oppeK //.
  by exists (- x); [exists x | rewrite oppeK].
apply/ (@nbhs_oo_up_e1 _ e) => // x x1e; exists (- x); last by rewrite oppeK.
by apply/reA/ereal_ballN; rewrite oppeK.
Qed.

Lemma nbhs_oo_up_1e (A : set (\bar R)) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball +oo e%:num `<=` A -> nbhs +oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0%R.
  rewrite predeqE => x; split => // _; apply: reA.
  exact/ereal_ballN/ereal_ball_ninfty_oversize.
have /andP[e10 e11] : (0 < e%:num - 1 <= 1)%R.
  by rewrite subr_gt0 e1 /= lerBlDl.
apply: nbhsNKe.
have : ((PosNum e10)%:num <= 1)%R by [].
move/(@nbhs_oo_down_e1 (-%E @` A) (PosNum e10)); apply=> y ye.
exists (- y); last by rewrite oppeK.
apply/reA/ereal_ballN; rewrite oppeK /=.
by apply: le_ereal_ball ye => /=; rewrite lerBlDl lerDr.
Qed.

Lemma nbhs_oo_down_1e (A : set (\bar R)) (e : {posnum R}) : (1 < e%:num)%R ->
  ereal_ball -oo e%:num `<=` A -> nbhs -oo A.
Proof.
move=> e1 reA; have [e2{e1}|e2] := ltrP 2 e%:num.
  suff -> : A = setT by exists 0%R.
  by rewrite predeqE => x; split => // _; exact/reA/ereal_ball_ninfty_oversize.
have /andP[e10 e11] : (0 < e%:num - 1 <= 1)%R.
  by rewrite subr_gt0 e1 /= lerBlDl.
apply: nbhsNKe.
have : ((PosNum e10)%:num <= 1)%R by [].
move/(@nbhs_oo_up_e1 (-%E @` A) (PosNum e10)); apply.
move=> y ye; exists (- y); last by rewrite oppeK.
apply/reA/ereal_ballN; rewrite /= oppeK.
by apply: le_ereal_ball ye => /=; rewrite lerBlDl lerDr.
Qed.

Lemma nbhs_fin_out_above r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A ->
  (- 1 < contract r%:E - e%:num)%R ->
  (1 <= contract r%:E + e%:num)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have er1 : (`|contract r%:E - e%:num| < 1)%R.
  rewrite ltr_norml reN1 andTb ltrBlDl ltr_pwDl //.
  by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
pose e' := (r - fine (expand (contract r%:E - e%:num)))%R.
have e'0 : (0 < e')%R.
  rewrite subr_gt0 -lte_fin -[ltRHS](contractK r%:E).
  rewrite fine_expand // lt_expand ?inE ?contract_le1// ?ltW//.
  by rewrite ltrBlDl ltrDr.
apply/nbhs_ballP; exists e' => // r' re'r'; apply: reA.
by have [?|?] := lerP r r';
  [exact: contract_ereal_ball_fin_le | exact: ball_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_below r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A ->
  (contract r%:E - e%:num <= - 1)%R ->
  (contract r%:E + e%:num < 1)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1.
have ? : (`|contract r%:E + e%:num| < 1)%R.
  rewrite ltr_norml re1 andbT (@lt_le_trans _ _ (contract r%:E)) // ?lerDl //.
  by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
pose e' : R := (fine (expand (contract r%:E + e%:num)) - r)%R.
have e'0 : (0 < e')%R.
  rewrite /e' subr_gt0 -lte_fin -[in ltLHS](contractK r%:E).
  by rewrite fine_expand // lt_expand ?inE ?contract_le1 ?ltrDl ?ltW.
apply/nbhs_ballP; exists e' => // r' r'e'r; apply: reA.
by have [?|?] := lerP r r';
  [exact: ball_ereal_ball_fin_le | exact: contract_ereal_ball_fin_lt].
Qed.

Lemma nbhs_fin_out_above_below r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A ->
  (contract r%:E - e%:num < -1)%R ->
  (1 < contract r%:E + e%:num)%R ->
  nbhs r%:E A.
Proof.
move=> reA reN1 re1; suff : A = setT by move->; apply: filterT.
rewrite predeqE => x; split => // _; apply: reA.
case: x => [r'| |] //.
- have [?|?] := lerP r r'.
  + by apply: contract_ereal_ball_fin_le => //; exact/ltW.
  + by apply: contract_ereal_ball_fin_lt => //; exact/ltW.
- exact/contract_ereal_ball_pinfty.
- apply/ereal_ballN/contract_ereal_ball_pinfty.
  by rewrite EFinN contractN -(opprK 1%R) ltrNl opprD opprK.
Qed.

Lemma nbhs_fin_inbound r (e : {posnum R}) (A : set (\bar R)) :
  ereal_ball r%:E e%:num `<=` A -> nbhs r%:E A.
Proof.
move=> reA.
have [|reN1] := boolP (contract r%:E - e%:num == -1)%R.
  rewrite subr_eq addrC => /eqP reN1.
  have [re1|] := boolP (contract r%:E + e%:num == 1)%R.
    move/eqP : reN1; rewrite -(eqP re1) opprD addrCA subrr addr0 -subr_eq0.
    rewrite opprK -mulr2n mulrn_eq0 orFb contract_eq0 => /eqP[r0].
    move: re1; rewrite r0 contract0 add0r => /eqP e1.
    apply/nbhs_ballP; exists 1%R => //= r'; rewrite /ball /= sub0r normrN => r'1.
    apply: reA.
    by rewrite /ereal_ball r0 contract0 sub0r normrN e1 contract_lt1.
  rewrite neq_lt => /orP[re1|re1].
    by apply: (@nbhs_fin_out_below _ e) => //; rewrite reN1 addrAC subrr sub0r.
  have e1 : (1 < e%:num)%R.
    move: re1; rewrite reN1 addrAC ltrBrDl -!mulr2n -(mulr_natl e%:num).
    by rewrite -{1}(mulr1 2%:R) => ?; rewrite -(@ltr_pM2l _ 2).
  have Aoo : setT `\ -oo `<=` A.
    move=> x [_]; rewrite /set1 /= => xnoo; apply: reA.
    case: x xnoo => [r' _ | _ |//].
      have [rr'|r'r] := lerP (contract r%:E) (contract r'%:E).
        apply: contract_ereal_ball_fin_le; last exact/ltW.
        by rewrite -lee_fin -(contractK r%:E) -(contractK r'%:E) le_expand.
      apply: contract_ereal_ball_fin_lt; last first.
        by rewrite reN1 addrAC subrr add0r.
      rewrite -lte_fin -(contractK r%:E) -(contractK r'%:E).
      by rewrite lt_expand // inE; exact: contract_le1.
    exact: contract_ereal_ball_pinfty.
  have : nbhs r%:E (setT `\ -oo) by apply/nbhs_ballP; exists 1%R => /=.
  move=> /nbhs_ballP[_/posnumP[e']] /=; rewrite /ball /= => h.
  by apply/nbhs_ballP; exists e'%:num => //= y /h; apply: Aoo.
move: reN1; rewrite eq_sym neq_lt => /orP[reN1|reN1].
  have [re1|re1] := eqVneq (contract r%:E + e%:num)%R 1%R.
    by apply: (@nbhs_fin_out_above _ e) => //; rewrite re1.
  move: re1; rewrite neq_lt => /orP[re1|re1].
    have ? : (`|contract r%:E - e%:num| < 1)%R.
      rewrite ltr_norml reN1 andTb ltrBlDl.
      rewrite (@lt_le_trans _ _ 1%R) // ?lerDr//.
      by case/ltr_normlP : (contract_lt1 r).
    have ? : (`|contract r%:E + e%:num| < 1)%R.
      rewrite ltr_norml re1 andbT -(addr0 (-1)) ler_ltD //.
      by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
    pose e' : R := Num.min
      (r - fine (expand (contract r%:E - e%:num)))%R
      (fine (expand (contract r%:E + e%:num)) - r)%R.
    have e'0 : (0 < e')%R.
      rewrite /e' lt_min; apply/andP; split.
        rewrite subr_gt0 -lte_fin -[in ltRHS](contractK r%:E).
        rewrite fine_expand // lt_expand// ?inE ?contract_le1 ?ltW//.
        by rewrite ltrBlDl ltrDr.
      rewrite subr_gt0 -lte_fin -[in ltLHS](contractK r%:E).
      by rewrite fine_expand// lt_expand ?inE ?contract_le1 ?ltrDl ?ltW.
    apply/nbhs_ballP; exists e' => // r' re'r'; apply: reA.
    have [|r'r] := lerP r r'.
      move=> rr'; apply: ball_ereal_ball_fin_le => //.
      by apply: le_ball re'r'; rewrite ge_min lexx orbT.
    move: re'r'; rewrite /ball /= lt_min => /andP[].
    rewrite gtr0_norm ?subr_gt0 // -ltrBlDl addrAC subrr add0r ltrNl.
    rewrite opprK -lte_fin fine_expand // => r'e'r _.
    exact: expand_ereal_ball_fin_lt.
  by apply :(@nbhs_fin_out_above _ e) => //; rewrite ltW.
have [re1|re1] := ltrP 1 (contract r%:E + e%:num).
  exact: (@nbhs_fin_out_above_below _ e).
move: re1; rewrite le_eqVlt => /orP[re1|re1].
  have {}re1 : contract r%:E = (1 - e%:num)%R.
    by move: re1; rewrite eq_sym -subr_eq => /eqP <-.
  have e1 : (1 < e%:num)%R.
    move: reN1.
    rewrite re1 -addrA -opprD ltrBlDl ltrBrDl -!mulr2n.
    rewrite -(mulr_natl e%:num) -{1}(mulr1 2%:R) => ?.
    by rewrite -(@ltr_pM2l _ 2).
  have Aoo : (setT `\ +oo `<=` A).
    move=> x [_]; rewrite /set1 /= => xpoo; apply: reA.
    case: x xpoo => [r' _ | // |_].
      rewrite /ereal_ball.
      have [rr'|r'r] := lerP (contract r%:E) (contract r'%:E).
        rewrite re1 opprB addrCA -[ltRHS]addr0 ltrD2 subr_lt0.
        by case/ltr_normlP : (contract_lt1 r').
      rewrite /ereal_ball.
      rewrite re1 addrAC ltrBlDl ltrD // (lt_trans _ e1) // ltrNl.
      by move: (contract_lt1 r'); rewrite ltr_norml => /andP[].
    rewrite /ereal_ball.
    rewrite [contract -oo]/= opprK gtr0_norm ?subr_gt0; last first.
      rewrite -ltrBlDl add0r ltrNl.
      by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
    by rewrite re1 addrAC ltrBlDl ltrD.
   have : nbhs r%:E (setT `\ +oo) by exists 1%R => /=.
   case => _/posnumP[x] /=; rewrite /ball_ => h.
   by exists x%:num => //= y /h; exact: Aoo.
by apply: (@nbhs_fin_out_below _ e) => //; rewrite ltW.
Qed.

Lemma ereal_nbhsE : nbhs = nbhs_ (entourage_ (@ereal_ball R)).
Proof.
set diag := fun r => [set xy | ereal_ball xy.1 r xy.2].
rewrite predeq2E => x A; split.
- rewrite {1}/nbhs /= /ereal_nbhs.
  case: x => [/= r [_/posnumP[e] reA]| [M [/= Mreal MA]]| [M [/= Mreal MA]]].
  + pose e' : R := Num.min (contract r%:E - contract (r%:E - e%:num%:E))%R
                           (contract (r%:E + e%:num%:E) - contract r%:E)%R.
    exists (diag e'); rewrite /diag.
      exists e' => //.
      rewrite /= /e' lt_min; apply/andP; split.
        by rewrite subr_gt0 lt_contract lte_fin ltrBlDr ltrDl.
      by rewrite subr_gt0 lt_contract lte_fin ltrDl.
    case=> [r' /= /xsectionP/= re'r'| |]/=.
    * rewrite /ereal_ball in re'r'.
      have [r'r|rr'] := lerP (contract r'%:E) (contract r%:E).
        apply: reA; rewrite /ball /= ltr_norml//.
        rewrite ger0_norm ?subr_ge0// in re'r'.
        have : (contract (r%:E - e%:num%:E) < contract r'%:E)%R.
          move: re'r'; rewrite /e' lt_min => /andP[+ _].
          rewrite /e' ltrBrDl addrC -ltrBrDl => /lt_le_trans.
          by apply; rewrite opprB addrCA subrr addr0.
        rewrite -lt_expandRL ?inE ?contract_le1 // !contractK lte_fin.
        rewrite ltrBlDr addrC -ltrBlDr => ->; rewrite andbT.
        rewrite (@lt_le_trans _ _ 0%R)// 1?ltrNl 1?oppr0// subr_ge0.
        by rewrite -lee_fin -le_contract.
      apply: reA; rewrite /ball /= ltr_norml//.
      rewrite ltr0_norm ?subr_lt0// opprB in re'r'.
      apply/andP; split; last first.
        by rewrite (@lt_trans _ _ 0%R) // subr_lt0 -lte_fin -lt_contract.
      rewrite ltrNl opprB.
      rewrite /e' in re'r'.
      have r're : (contract r'%:E < contract (r%:E + e%:num%:E))%R.
        move: re'r'; rewrite lt_min => /andP[_].
        by rewrite ltrBlDr subrK.
      rewrite ltrBlDr -lte_fin -(contractK (_ + r)%:E)%R.
      by rewrite addrC -(contractK r'%:E) // lt_expand ?inE ?contract_le1.
    * move=> /xsectionP/=; rewrite /ereal_ball [contract +oo]/=.
      rewrite lt_min => /andP[re'1 re'2].
      have [cr0|cr0] := lerP 0 (contract r%:E).
        move: re'2; rewrite ler0_norm; last first.
          by rewrite subr_le0; case/ler_normlP : (contract_le1 r%:E).
        rewrite opprB ltrBrDl addrCA subrr addr0 => h.
        exfalso.
        move: h; apply/negP; rewrite -leNgt.
        by case/ler_normlP : (contract_le1 (r%:E + e%:num%:E)).
      move: re'2; rewrite ler0_norm; last first.
        by rewrite subr_le0; case/ler_normlP : (contract_le1 r%:E).
      rewrite opprB ltrBrDl addrCA subrr addr0 => h.
      exfalso.
      move: h; apply/negP; rewrite -leNgt.
      by case/ler_normlP : (contract_le1 (r%:E + e%:num%:E)).
    * move=> /xsectionP/=; rewrite /ereal_ball [contract -oo]/= opprK.
      rewrite lt_min => /andP[re'1 _].
      move: re'1.
      rewrite ger0_norm; last first.
        rewrite addrC -lerBlDl add0r.
        by move: (contract_le1 r%:E); rewrite ler_norml => /andP[].
      rewrite ltrD2l => h.
      exfalso.
      move: h; apply/negP; rewrite -leNgt -lerNl.
      by move: (contract_le1 (r%:E - e%:num%:E)); rewrite ler_norml => /andP[].
  + exists (diag (1 - contract M%:E))%R; rewrite /diag.
      exists (1 - contract M%:E)%R => //=.
      by rewrite subr_gt0 (le_lt_trans _ (contract_lt1 M)) // ler_norm.
    case=> [r| |]/= /xsectionP/=.
    * rewrite /ereal_ball [_ +oo]/= => rM1.
      apply: MA; rewrite lte_fin.
      rewrite ger0_norm in rM1; last first.
        by rewrite subr_ge0 // (le_trans _ (contract_le1 r%:E)) // ler_norm.
      rewrite ltrBlDr addrC addrCA addrC -ltrBlDr subrr subr_gt0 in rM1.
      by rewrite -lte_fin -lt_contract.
    * by rewrite /ereal_ball /= subrr normr0 => h; exact: MA.
    * rewrite /ereal_ball /= opprK => h {MA}.
      exfalso.
      move: h; apply/negP.
      rewrite -leNgt [in leRHS]ger0_norm // lerBlDr.
      rewrite -/(contract M%:E) addrC -lerBlDr opprD addrA subrr sub0r.
      by move: (contract_le1 M%:E); rewrite ler_norml => /andP[].
  + exists (diag (1 + contract M%:E)%R); rewrite /diag.
      exists (1 + contract M%:E)%R => //=.
      rewrite -ltrBlDl sub0r.
      by move: (contract_lt1 M); rewrite ltr_norml => /andP[].
    case=> [r| |] /xsectionP/=.
    * rewrite /ereal_ball => /= rM1.
      apply: MA; rewrite lte_fin.
      rewrite ler0_norm in rM1; last first.
        rewrite lerBlDl addr0 ltW //.
        by move: (contract_lt1 r); rewrite ltr_norml => /andP[].
      rewrite opprB opprK -ltrBlDl addrK in rM1.
      by rewrite -lte_fin -lt_contract.
    * rewrite /ereal_ball /= -opprD normrN => h {MA}.
      exfalso.
      move: h; apply/negP.
      rewrite -leNgt [in leRHS]ger0_norm// -lerBlDr addrAC.
      rewrite subrr add0r -/(contract M%:E).
      by rewrite (le_trans _ (ltW (contract_lt1 M))) // ler_norm.
    * rewrite /ereal_ball /= => _; exact: MA.
- case: x => [r [E [_/posnumP[e] reA] sEA] | [E [_/posnumP[e] reA] sEA] |
               [E [_/posnumP[e] reA] sEA]] //=.
  + by apply: (@nbhs_fin_inbound _ e) => ? ?; exact/sEA/xsectionP/reA.
  + have [|] := boolP (e%:num <= 1)%R.
      by move/nbhs_oo_up_e1; apply => ? ?; exact/sEA/xsectionP/reA.
    by rewrite -ltNge => /nbhs_oo_up_1e; apply => ? ?; exact/sEA/xsectionP/reA.
  + have [|] := boolP (e%:num <= 1)%R.
      move/nbhs_oo_down_e1; apply => ? ?; apply: sEA.
      by rewrite /xsection/= inE; exact: reA.
    by rewrite -ltNge =>/nbhs_oo_down_1e; apply => ? ?; exact/sEA/xsectionP/reA.
Qed.

HB.instance Definition _ := Nbhs_isPseudoMetric.Build R (\bar R)
  ereal_nbhsE ereal_ball_center ereal_ball_sym ereal_ball_triangle erefl.

End ereal_PseudoMetric.

(* TODO: generalize to numFieldType? *)
Lemma nbhs_interval (R : realFieldType) (P : R -> Prop) (r : R) (a b : \bar R) :
  a < r%:E -> r%:E < b ->
  (forall y, a < y%:E -> y%:E < b -> P y) ->
  nbhs r P.
Proof.
move => ar rb abP; case: (lt_ereal_nbhs ar rb) => d rd.
exists d%:num => //= y; rewrite /= distrC.
by move=> /rd /andP[? ?]; apply: abP.
Qed.

Lemma ereal_dnbhs_le (R : numFieldType) (x : \bar R) :
  ereal_dnbhs x --> ereal_nbhs x.
Proof.
move: x => [r P [_/posnumP[e] reP] |r P|r P] //=.
by exists e%:num => //= ? ? ?; apply: reP.
Qed.

Lemma ereal_dnbhs_le_finite (R : numFieldType) (r : R) :
  ereal_dnbhs r%:E --> nbhs r%:E.
Proof.
by move=> P [_/posnumP[e] reP] //=; exists e%:num => //= ? ? ?; exact: reP.
Qed.

Definition ereal_loc_seq (R : numDomainType) (x : \bar R) (n : nat) :=
  match x with
    | x%:E => (x + (n%:R + 1)^-1)%:E
    | +oo => n%:R%:E
    | -oo => - n%:R%:E
  end.

Lemma cvg_ereal_loc_seq (R : realType) (x : \bar R) :
  ereal_loc_seq x  @ \oo--> ereal_dnbhs x.
Proof.
move=> P; rewrite /ereal_loc_seq.
case: x => /= [x [_/posnumP[d] dP] |[d [dreal dP]] |[d [dreal dP]]]; last 2 first.
    have /natrP[N Nfloor] : Num.floor (Num.max d 0%R) \is a Num.nat.
      by rewrite Znat_def floor_ge0 le_max lexx orbC.
    exists N.+1 => // n ltNn; apply: dP; rewrite lte_fin.
    have /le_lt_trans : (d <= Num.max d 0)%R by rewrite le_max lexx.
    apply; rewrite (lt_le_trans (lt_succ_floor _))// Nfloor.
    by rewrite natr1 mulrz_nat ler_nat.
  have /natrP[N Nfloor] : Num.floor (Num.max (- d)%R 0%R) \is a Num.nat.
    by rewrite Znat_def floor_ge0 le_max lexx orbC.
  exists N.+1 => // n ltNn; apply: dP; rewrite lte_fin ltrNl.
  have /le_lt_trans : (- d <= Num.max (- d) 0)%R by rewrite le_max lexx.
  apply; rewrite (lt_le_trans (lt_succ_floor _))// Nfloor.
  by rewrite natr1 mulrz_nat ler_nat.
have /natrP[N Nfloor] : Num.floor d%:num^-1 \is a Num.nat.
  by rewrite Znat_def floor_ge0.
exists N => // n leNn; apply: dP; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym; exact/invr_neq0/lt0r_neq0.
rewrite /= opprD addrA subrr distrC subr0 gtr0_norm; last by rewrite invr_gt0.
rewrite -[ltLHS]mulr1 ltr_pdivrMl // -ltr_pdivrMr // div1r.
by rewrite (lt_le_trans (lt_succ_floor _))// Nfloor !natr1 mulrz_nat ler_nat.
Qed.
