From mathcomp Require Import all_ssreflect all_algebra archimedean finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop interval_inference.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval numfun esum measure lebesgue_measure.

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
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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

Section perfectlynormalspace.
Context (R : realType) (T : topologicalType).

Definition perfectly_normal_space (x : R) :=
  forall E : set T, closed E -> 
    exists f : T -> R, continuous f /\ E = f @^-1` [set x].

Lemma perfectly_normal_spaceP x y : perfectly_normal_space x -> perfectly_normal_space y.
Proof.
move=>px E cE.
case:(px E cE) => f [] cf ->.
pose f' := f + cst (y - x). 
exists f'.
split.
rewrite /f'.
move=> z.
apply: continuousD.
exact:cf.
exact:cst_continuous.
apply/seteqP.
rewrite /f' /cst /=.
split => z /=.
rewrite addrfctE => ->.
by rewrite subrKC.
rewrite addrfctE.
move/eqP.
by rewrite eq_sym -subr_eq opprB subrKC eq_sym => /eqP.
Qed.

Definition perfectly_normal_space01 :=
  forall E F : set T, closed E -> closed F -> [disjoint E & F] ->
    exists f : T -> R, continuous f /\ E = f @^-1` [set 0] /\ F = f @^-1` [set 1] 
      /\ f @` [set: T] = `[0, 1]%classic.

Definition perfectly_normal_space_G_delta :=
  normal_space T /\ forall E : set T, closed E -> Gdelta E.

Lemma perfectly_normal_space01P : perfectly_normal_space <-> perfectly_normal_space01.
Proof.
Admitted.

End perfectlynormalspace.
