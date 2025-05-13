From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop interval_inference.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval esum measure lebesgue_measure numfun.

(**md**************************************************************************)
(* # Basic facts about G-delta and F-sigma sets                               *)
(*                                                                            *)
(* ```                                                                        *)
(*         Gdelta S == S is countable intersection of open sets               *)
(*   Gdelta_dense S == S is a countable intersection of dense open sets       *)
(*         Fsigma S == S is countable union of closed sets                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.

Lemma denseI (T : topologicalType) (A B : set T) :
  open A -> dense A -> dense B -> dense (A `&` B).
Proof.
move=> oA dA dB C C0 oC.
have CA0 : C `&` A !=set0 by exact: dA.
suff: (C `&` A) `&` B !=set0 by rewrite setIA.
by apply: dB => //; exact: openI.
Qed.

Lemma dense0 {R : ptopologicalType} : ~ dense (@set0 R).
Proof.
apply/existsNP; exists setT.
apply/not_implyP; split; first exact/set0P/setT0.
apply/not_implyP; split; first exact: openT.
by rewrite setTI => -[].
Qed.

Lemma dense_set1C {R : realType} (r : R) : dense (~` [set r]).
Proof.
move=> /= O O0 oO.
suff [s Os /eqP sr] : exists2 s, O s & s != r by exists s; split.
case: O0 => o Oo.
have [->{r}|ro] := eqVneq r o; last by exists o => //; rewrite eq_sym.
have [e' /= e'0 e'o] := open_itvoo_subset oO Oo.
near (0:R)^'+ => e.
exists (o + e/2)%R; last by rewrite gt_eqF// ltrDl// divr_gt0.
apply: (e'o e) => //=.
  by rewrite sub0r normrN gtr0_norm.
rewrite in_itv/= !ltrD2l; apply/andP; split.
  by rewrite (@lt_le_trans _ _ 0%R) ?divr_ge0// ltrNl oppr0.
by rewrite gtr_pMr// invf_lt1// ltr1n.
Unshelve. all: by end_near. Qed.

Section Gdelta_Fsigma.
Context {T : topologicalType}.
Implicit Type S : set T.

Definition Gdelta S :=
  exists2 F : (set T)^nat, (forall i, open (F i)) & S = \bigcap_i (F i).

Lemma open_Gdelta S : open S -> Gdelta S.
Proof. by exists (fun=> S)=> //; rewrite bigcap_const. Qed.

Definition Gdelta_dense S :=
  exists2 F : (set T)^nat,
    (forall i, open (F i) /\ dense (F i)) & S = \bigcap_i (F i).

Definition Fsigma S :=
  exists2 F : (set T)^nat, (forall i, closed (F i)) & S = \bigcup_i (F i).

Lemma closed_Fsigma S : closed S -> Fsigma S.
Proof. by exists (fun=> S)=> //; rewrite bigcup_const. Qed.

End Gdelta_Fsigma.

Lemma Gdelta_measurable {R : realType} (S : set R) : Gdelta S -> measurable S.
Proof.
move=> [] B oB ->; apply: bigcapT_measurable => i.
exact: open_measurable.
Qed.

Lemma Gdelta_subspace_open {R : realType} (A : set R) (S : set (subspace A)) :
  open A -> Gdelta S -> Gdelta (A `&` S).
Proof.
move=> oA [/= S_ oS_ US].
exists (fun n => A `&` (S_ n)).
  by move=> ?; rewrite open_setSI.
by rewrite bigcapIr// US.
Qed.

Section irrational_Gdelta.
Context {R : realType}.

Lemma irrational_Gdelta : Gdelta_dense (irrational R).
Proof.
rewrite irrationalE.
have /pcard_eqP/bijPex[f bijf] := card_rat.
pose f1 := 'pinv_(fun => 0%R) [set: rat] f.
exists (fun n => ~` [set ratr (f1 n)]).
  move=> n.
  rewrite openC.
  split; last exact: dense_set1C.
  exact/accessible_closed_set1/hausdorff_accessible/Rhausdorff.
apply/seteqP; split => [/= r/= rE n _/= rf1n|/=r rE q _/= [_ -> qr]].
  by apply: (rE (f1 n)) => //=; exists (f1 n).
apply: (rE (f q)) => //=.
rewrite /f1 pinvKV ?inE//=.
exact: set_bij_inj bijf.
Qed.

End irrational_Gdelta.

Lemma not_rational_Gdelta (R : realType) : ~ Gdelta (@rational R).
Proof.
apply/forall2NP => A.
apply/not_andP => -[oA ratrA].
have dense_A n : dense (A n).
  move=> D D0 oD.
  have := @dense_rat R D D0 oD.
  apply: subset_nonempty.
  apply: setIS.
  rewrite -/(@rational R) ratrA.
  exact: bigcap_inf.
have [/= B oB irratB] := @irrational_Gdelta R.
pose C : (set R)^nat := fun n => A n `&` B n.
have C0 : set0 = \bigcap_i C i by rewrite bigcapI -ratrA -irratB setICr.
have : forall n, open (C n) /\ dense (C n).
  move=> n; split.
    by apply: openI => //; apply oB.
  by apply: denseI => //; apply oB.
move/Baire.
rewrite -C0.
exact: dense0.
Qed.
