(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat algebra.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.

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

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.

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
move=> oA [/= S_ oS_ US]; exists (fun n => A `&` (S_ n)).
  by move=> ?; rewrite open_setSI.
by rewrite bigcapIr// US.
Qed.

Section irrational_Gdelta.
Context {R : realType}.

Lemma irrational_Gdelta : Gdelta_dense (@irrational R).
Proof.
rewrite irrationalE.
have /pcard_eqP/bijPex[f bijf] := card_rat.
pose f1 := 'pinv_(fun => 0%R) [set: rat] f.
exists (fun n => ~` [set ratr (f1 n)]).
  move=> n; rewrite openC; split; last exact: dense_set1C.
  exact/accessible_closed_set1/hausdorff_accessible/Rhausdorff.
apply/seteqP; split => [/= r/= rE n _/= rf1n|/=r rE q _/= [_ -> qr]].
  by apply: (rE (f1 n)) => //=; exists (f1 n).
apply: (rE (f q)) => //=.
by rewrite /f1 pinvKV ?inE//=; exact: set_bij_inj bijf.
Qed.

End irrational_Gdelta.

Definition borel_type (T : topologicalType) := g_sigma_algebraType (@open T).

Section borel_normedModType.
Local Open Scope ring_scope.
Context {R : realType} {V : normedModType R}.

Lemma singleton_bigcap (x : V) :
  [set x] = \bigcap_(k : nat) ball x (k.+1%:R)^-1.
Proof.
apply/seteqP; split => [_ -> k _|y xy].
  by rewrite -ball_normE/= subrr normr0 invr_gt0 ltr0n.
apply/eqP; rewrite eq_sym -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pl => e e0; rewrite addr0.
have := xy (truncn e^-1) I; rewrite -ball_normE/= => /ltW/le_trans; apply.
by rewrite invf_ple ?posrE ?ltr0n ?invr_gt0//; apply/ltW/truncnS_gt.
Qed.

Lemma measurable1 (x : borel_type V) : measurable [set x].
Proof.
rewrite singleton_bigcap; apply: bigcap_measurable => // k _.
by apply: sub_sigma_algebra; exact: ball_open.
Qed.

End borel_normedModType.

#[non_forgetful_inheritance]
HB.instance Definition _ (R : realType) (V : normedModType R) :=
  Measurable.copy V (borel_type V).

Lemma not_rational_Gdelta (R : realType) : ~ Gdelta (@rational R).
Proof.
apply/forall2NP => A; apply/not_andP => -[oA ratrA].
have dense_A n : dense (A n).
  move=> D D0 /(@dense_rat R D D0); apply/subset_nonempty; apply: setIS.
  by rewrite -/(@rational R) ratrA; exact: bigcap_inf.
have [/= B oB irratB] := @irrational_Gdelta R.
pose C : (set R)^nat := fun n => A n `&` B n.
have C0 : set0 = \bigcap_i C i by rewrite bigcapI -ratrA -irratB setICr.
have /Baire : forall n, open (C n) /\ dense (C n).
  move=> n; split.
  - by apply: openI => //; apply oB.
  - by apply: denseI => //; apply oB.
by rewrite -C0; exact: dense0.
Qed.
