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

Import Order.TTheory GRing.Theory Num.Theory Num.Def.
Import numFieldNormedType.Exports.
Import numFieldTopology.Exports.
Import exp.

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

Definition perfectly_normal_space' (x : R) :=
  forall E : set T, open E -> 
    exists f : T -> R, continuous f /\ E = f @^-1` ~`[set x].

Definition perfectly_normal_space01 :=
  forall E F : set T, closed E -> closed F -> [disjoint E & F] ->
    exists f : T -> R, continuous f /\ E = f @^-1` [set 0] /\ F = f @^-1` [set 1] 
      /\ f @` [set: T] = `[0, 1]%classic.

Definition perfectly_normal_space_Gdelta :=
  normal_space T /\ forall E : set T, closed E -> Gdelta E.

Lemma perfectly_normal_space01_normal :
  perfectly_normal_space01 -> normal_space T.
Proof.
move=> pns01 A cA B /set_nbhsP[C] [oC AC CB].
case: (pns01 A (~` C) cA).
- by rewrite closedC.
- exact/disj_setPCl.
move=> f [/continuousP /= cf] [f0] [f1] f01.
exists (f @^-1` `]-oo, 1/2]).
  apply/set_nbhsP.
  exists (f @^-1` `]-oo, 1/2[).
  split => //.
  - exact: cf.
  - by rewrite f0 => x /= ->; rewrite in_itv /=.
  - by apply: preimage_subset => x /=; rewrite !in_itv /=; apply: ltW.
apply: subset_trans CB.
have<-:= proj1 (closure_id _).
  have<-:= (setCK C).
  rewrite f1 preimage_setC.
  apply: preimage_subset => x /=; rewrite in_itv /=.
  apply: contraTnot => ->.
  by rewrite -ltNge ltr_pdivrMr // mul1r ltr1n.
have/continuousP /continuous_closedP:= cf.
apply.
exact: lray_closed.
Qed.

Lemma EFin_series (f : R^nat) : EFin \o series f = eseries (EFin \o f).
Proof.
apply/boolp.funext => n.
rewrite /series /eseries /=.
elim: n => [|n IH]; first by rewrite !big_geq.
by rewrite !big_nat_recr //= EFinD IH.
Qed.

Let perfectly_normal_space_12 : perfectly_normal_space_Gdelta -> perfectly_normal_space 0.
Proof.
move=> pnsGd E cE.
case: (pnsGd) => nT cEGdE.
have[U oU HE]:= cEGdE E cE.
have/boolp.choice[f_n Hn]: forall n, exists f : T -> R, 
  [/\ continuous f, range f `<=` `[0, 1], f @` E `<=` [set 0] & f @` (~` U n) `<=` [set 1]].
  move=> n.
  apply/uniform_separatorP.
  apply: normal_uniform_separator => //.
  - by rewrite closedC.
  - rewrite HE -subsets_disjoint.
    exact: bigcap_inf.
pose f_sum := fun n => \sum_(0 <= k < n) (f_n k \* cst (2^-k.+1)).
have cf_sum n : continuous (f_sum n).
  rewrite /f_sum => x; elim: n => [|n IH].
    rewrite big_geq //; exact: cst_continuous.
  rewrite big_nat_recr //=; apply: continuousD => //.
  apply/continuousM/cst_continuous.
  by case: (Hn n) => /(_ x).
have f_sumE x : f_sum ^~ x = [series f_n k x * 2^-k.+1]_k.
  apply/boolp.funext => n.
  rewrite /f_sum /series /mk_sequence.
  elim: n => [|n IH]; first by rewrite !big_geq.
  by rewrite !big_nat_recr //= [X in X _ _ x]/GRing.add /= IH.
pose f := fun x => limn (f_sum^~ x).
rewrite /= in f.
exists f.
have ndf_sum y : {homo f_sum^~ y : a b / (a <= b)%N >-> a <= b}.
  move=> a b ab.
  rewrite /f_sum.
  rewrite (big_cat_nat _ ab) //= lerDl.
  elim/big_rec: _ => //= i f0 _.
  rewrite /GRing.add /= => /le_trans; apply.
  rewrite lerDr mulr_ge0 //.
    case: (Hn i) => _ Hr _ _.
    have /Hr /= := imageT (f_n i) y.
    by rewrite in_itv /= => /andP[].
  by rewrite invr_ge0 exprn_ge0.
(*have Hub y m k : (\sum_(m <= i < k) f_n i \* cst (2 ^- i.+1)) y <= 2^-m.
  apply: (@le_trans _ _ (2^-m - 2^-k)); last first.
  by rewrite gerBl invr_ge0 exprn_ge0.*)
have Hcvg y : cvgn (f_sum^~ y).
  apply: nondecreasing_is_cvgn => //.
  exists 1 => z /= [m] _ <-.
  rewrite /f_sum.
  apply: (@le_trans _ _ (1 - 2^-m)); last by rewrite gerBl invr_ge0 exprn_ge0.
  elim: m => [|m IH]; first by rewrite big_geq // expr0 invr1 subrr.
  rewrite big_nat_recr //=.
  have Hm : f_n m y * 2 ^- m.+1 <= 2 ^- m.+1.
    case: (Hn m) => _ Hr _ _.
    have /Hr /= := imageT (f_n m) y.
    rewrite in_itv /= => /andP[f0 f1].
    by rewrite -[leRHS]mul1r ler_pM.
  apply: (le_trans (lerD IH Hm)).
  rewrite -addrA.
  have -> : 2^- m = 2 * 2^-m.+1 :> R.
    by rewrite exprS invfM mulrA mulfV // mul1r.
  rewrite -{1}add1n {1}mulrnDr mulrDl !mul1r opprD !addrA -addrA.
  by rewrite [_ + 2^- _]addrC subrr addr0.
split.
  move=> x Nfx.
  rewrite -filter_from_ballE.
  case => eps /= eps0 HB.
  pose n := (2 + truncn (- ln eps / ln 2))%N.
  have eps0' : eps / 2 > 0 by exact: divr_gt0.
  move/continuousP/(_ _ (ball_open (f_sum n x) eps0')) : (cf_sum n) => /= ofs.
  rewrite nbhs_filterE.
  rewrite fmapE.
  rewrite nbhsE /=.
  set B := _ @^-1` _ in ofs.
  exists B.
    split => //.
    exact: ballxx.
  apply: subset_trans (preimage_subset (f:=f) HB).
  rewrite /B /preimage /ball => t /=.
  have Hf y :
    f y = f_sum n y + limn (fun n' => \sum_(n <= k < n') f_n k y * 2^- k.+1).
    have /= := nondecreasing_telescope_sumey n _ (ndf_sum y).
    rewrite EFin_lim // fin_numE /= => /(_ isT).
    rewrite (eq_eseriesr (g:=fun i => ((f_n i \* cst (2 ^- i.+1)) y)%:E));
      last first.
      move => i _.
      rewrite /f_sum -EFinD big_nat_recr //=.
      by rewrite [X in X _ _ y]/GRing.add /= addrAC subrr add0r.
    move/(f_equal (fun x => (f_sum n y)%:E + x)).
    rewrite addrA addrAC -EFinB subrr add0r => H.
    apply: EFin_inj.
    rewrite -H EFinD; congr (_ + _).
    rewrite -EFin_lim.
      apply/congr_lim/boolp.funext => k /=.
      elim: k => [|k IH]; first by rewrite !big_geq.
      case: (leP n k) => nk.
        by rewrite !big_nat_recr //= IH EFinD.
      by rewrite !big_geq.
    move: (Hcvg y).
    by rewrite is_cvg_series_restrict f_sumE.
  move=> feps.
  rewrite !Hf opprD addrA (addrAC (f_sum n x)) -(addrA (_ - _)).
  apply: (le_lt_trans (ler_normD _ _)).
  rewrite (splitr eps).
  apply: ltr_leD => //.
  admit.
apply/seteqP; split => x /= Hx.
  apply: EFin_inj.
  rewrite -EFin_lim // f_sumE EFin_series /= eseries0 // => i _ _ /=.
  case: (Hn i) => _ _ /(_ (f_n i x)) /= => ->.
    by rewrite mul0r.
  by exists x.
apply: contraPP Hx.
rewrite (_ : (~ E x) = setC E x) // HE setC_bigcap /= => -[] i _ HU.
case: (Hn i) => _ _ _ /(_ (f_n i x)) /= => Hfix.
rewrite /f => Hf.
have := (nondecreasing_cvgn_le (ndf_sum x) (Hcvg x) i.+1).
have := ndf_sum x _ _ (leq0n i.+1).
rewrite Hf {1}/f_sum big_geq // => /[swap] fi_le0.
rewrite le0r ltNge fi_le0 orbF.
rewrite /f_sum big_nat_recr //= [X in X _ _ x]/GRing.add /= -/(f_sum i).
rewrite Hfix; last by exists x.
rewrite mul1r /cst => /eqP fi0.
have := ndf_sum x _ _ (leq0n i).
rewrite {1}/f_sum big_geq // -[0 x]fi0 gerDl.
by rewrite leNgt invr_gt0 exprn_gt0.
Admitted.

Let perfectly_normal_space_13 : perfectly_normal_space_Gdelta -> perfectly_normal_space' 0.
move=> pnsGd E oE.
case: (pnsGd) => nT cEGdE.
have clcpE: closed (~`E).
  by rewrite closedC.
have[U oU hE]:= cEGdE (~` E) clcpE.
have/boolp.choice[f_n Hn]: forall n, exists f : T -> R, 
  [/\ continuous f, range f `<=` `[0, 1], f @` (~` E) `<=` [set 0] & f @` (~` U n) `<=` [set 1]].
  move=> n.
  apply/uniform_separatorP.
  apply: normal_uniform_separator => //.
  - by rewrite closedC.
  - rewrite hE.
    rewrite -subsets_disjoint.
    exact: bigcap_inf.
Admitted.

Let perfectly_normal_space_23 : perfectly_normal_space 0 -> perfectly_normal_space' 0.
Proof.
Admitted.

Let perfectly_normal_space_32 : perfectly_normal_space' 0 -> perfectly_normal_space 0.
Proof.
move=> pns' E cE; case: (pns' (~`E)).
  by rewrite openC.
move=> f [cf f0]; exists f.
split.
  by [].
by rewrite -[RHS]setCK preimage_setC -f0 setCK.
Qed.

Let perfectly_normal_space_24 : perfectly_normal_space 0 -> perfectly_normal_space01.
Proof.
Admitted.

Let perfectly_normal_space_34 : perfectly_normal_space' 0 -> perfectly_normal_space01.
Proof.
Admitted.

Local Lemma perfectly_normal_space_42 :                                 
perfectly_normal_space01  -> perfectly_normal_space 0.                  
Proof.                                                                  
move=> + E cE => /(_ E set0 cE closed0).                                
rewrite disj_set2E setI0 eqxx => /(_ erefl).                            
case=> f [] cf [] Ef [] _ _.                                            
by exists f; split.                                                     
Qed.                                                                    
                                                                        
Let perfectly_normal_space_41 :
  perfectly_normal_space01 -> perfectly_normal_space_Gdelta.
Proof.            
move=> pns01; split; first exact: perfectly_normal_space01_normal.
move=> E cE; case:(perfectly_normal_space_42 pns01 cE) => // f [] cf Ef.
exists (fun n => f @^-1` `]-n.+1%:R^-1,n.+1%:R^-1[%classic).
  by move=> n; move/continuousP: cf; apply; exact: itv_open.
rewrite -preimage_bigcap (_ : bigcap _ _ = [set 0])//.
rewrite eqEsubset; split; last first.
  by move=> x -> n _ /=; rewrite in_itv//= oppr_lt0 andbb invr_gt0.
apply: subsetC2; rewrite setC_bigcap => x /= /eqP x0.
exists (trunc `|x^-1|) => //=; rewrite in_itv/= -ltr_norml ltNge.
apply/negP; rewrite negbK.
by rewrite invf_ple ?posrE// ?normr_gt0// -normfV ltW// truncnS_gt.
Qed.

Theorem Vedenissoff_closed : perfectly_normal_space_Gdelta <-> perfectly_normal_space 0.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

Theorem Vedenissoff_open : perfectly_normal_space_Gdelta <-> perfectly_normal_space' 0.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

Theorem Vedenissoff01 : perfectly_normal_space_Gdelta <-> perfectly_normal_space01.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_23 perfectly_normal_space_34 perfectly_normal_space_41.
tauto.
Qed.

End perfectlynormalspace.
