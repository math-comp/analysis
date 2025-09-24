(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop reals.
From mathcomp Require Import interval_inference ereal topology normedtype.
From mathcomp Require Import sequences esum numfun.
From mathcomp Require Import measurable_structure measure_function.

(**md**************************************************************************)
(* # The Counting Measure                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*      counting T R == counting measure                                      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition counting (T : choiceType) (R : realType) (X : set T) : \bar R :=
  if `[< finite_set X >] then (#|` fset_set X |)%:R%:E else +oo%E.
Arguments counting {T R}.

Section measure_count.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (D : set T) (mD : measurable D).

Local Notation counting := (@counting T R).

Let counting0 : counting set0 = 0.
Proof. by rewrite /counting asboolT// fset_set0. Qed.

Let counting_ge0 (A : set T) : 0 <= counting A.
Proof. by rewrite /counting; case: ifPn; rewrite ?lee_fin// lee_pinfty. Qed.

Let counting_sigma_additive : semi_sigma_additive counting.
Proof.
move=> F mF tF mU.
have [[i Fi]|infinF] := pselect (exists k, infinite_set (F k)).
  have -> : counting (\bigcup_n F n) = +oo.
    rewrite /counting asboolF//.
    by apply: contra_not Fi; exact/sub_finite_set/bigcup_sup.
  apply/cvgeyPge => M; near=> n.
  have ni : (i < n)%N by near: n; exists i.+1.
  rewrite (bigID (xpred1 i))/= big_mkord (big_pred1 (Ordinal ni))//=.
  rewrite [X in X + _]/(counting _) asboolF// addye ?leey//.
  by rewrite gt_eqF// (@lt_le_trans _ _ 0)//; exact: sume_ge0.
have {infinF}finF : forall i, finite_set (F i) by exact/not_forallP.
pose u : nat^nat := fun n => #|` fset_set (F n) |.
have sumFE n : \sum_(i < n) counting (F i) =
               #|` fset_set (\big[setU/set0]_(k < n) F k) |%:R%:E.
  rewrite -trivIset_sum_card// natr_sum -sumEFin.
  by apply: eq_bigr => // i _; rewrite /counting asboolT.
have [cvg_u|dvg_u] := pselect (cvg (nseries u @ \oo)).
  have [N _ Nu] : \forall n \near \oo, u n = 0%N by apply: cvg_nseries_near.
  rewrite [X in _ --> X](_ : _ = \sum_(i < N) counting (F i)); last first.
    have -> : \bigcup_i (F i) = \big[setU/set0]_(i < N) F i.
      rewrite (bigcupID (`I_N)) setTI bigcup_mkord.
      rewrite [X in _ `|` X](_ : _ = set0) ?setU0// bigcup0// => i [_ /negP].
      by rewrite -leqNgt => /Nu/eqP/[!cardfs_eq0]/eqP/fset_set_set0 ->.
    by rewrite /counting /= asboolT ?sumFE// -bigcup_mkord; exact: bigcup_finite.
  rewrite -(cvg_shiftn N)/=.
  rewrite (_ : (fun n => _) = (fun=> \sum_(i < N) counting (F i))).
    exact: cvg_cst.
  apply/funext => n; rewrite /index_iota subn0 (addnC n) iotaD big_cat/=.
  rewrite [X in _ + X](_ : _ = 0) ?adde0.
    by rewrite -{1}(subn0 N) big_mkord.
  rewrite add0n big_seq big1// => i /[!mem_iota] => /andP[NI iNn].
  by rewrite /counting asboolT//= -/(u _) Nu.
have {dvg_u}cvg_F : (fun n => \sum_(i < n) counting (F i)) @ \oo --> +oo.
  rewrite (_ : (fun n => _) = [sequence (\sum_(0 <= i < n) (u i))%:R%:E]_n).
    exact/cvgenyP/dvg_nseries.
  apply/funext => n /=; under eq_bigr.
    by rewrite /counting => i _; rewrite asboolT//; over.
  by rewrite sumEFin natr_sum big_mkord.
have [UFoo|/contrapT[k UFk]] := pselect (infinite_set (\bigcup_n F n)).
  rewrite /counting asboolF//.
  by under eq_fun do rewrite big_mkord.
suff: false by [].
move: cvg_F =>/cvgeyPge/(_ k.+1%:R) [K _] /(_ K (leqnn _)) /=; apply: contra_leT => _.
rewrite sumFE lte_fin ltr_nat ltnS.
have -> : k = #|` fset_set (\bigcup_n F n) |.
  by apply/esym/card_eq_fsetP; rewrite fset_setK//; exists k.
apply/fsubset_leq_card; rewrite -fset_set_sub //.
- by move=> /= t; rewrite -bigcup_mkord => -[m _ Fmt]; exists m.
- by rewrite -bigcup_mkord; exact: bigcup_finite.
- by exists k.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ counting
  counting0 counting_ge0 counting_sigma_additive.

End measure_count.

Lemma sigma_finite_counting (R : realType) :
  sigma_finite [set: nat] (@counting _ R).
Proof.
exists (fun n => `I_n.+1); first by apply/seteqP; split=> //x _; exists x => /=.
by move=> k; split => //; rewrite /counting/= asboolT// ltry.
Qed.
HB.instance Definition _ R :=
  @isSigmaFinite.Build _ _ _ (@counting _ R) (sigma_finite_counting R).
