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
    exists f : T -> R,
      [/\ continuous f, E = f @^-1` [set 0], F = f @^-1` [set 1]
        & range f `<=` `[0, 1]%classic].

Definition perfectly_normal_space_Gdelta :=
  normal_space T /\ forall E : set T, closed E -> Gdelta E.

Lemma perfectly_normal_space01_normal :
  perfectly_normal_space01 -> normal_space T.
Proof.
move=> pns01.
rewrite (@normal_separatorP R).
move=> A B cA cB /eqP AB.
apply/uniform_separatorP.
have[f [] cf Af Bf f01] := pns01 _ _ cA cB AB.
exists f.
by split => //; rewrite (Af, Bf); exact:image_preimage_subset.
Qed.

Lemma EFin_series (f : R^nat) : EFin \o series f = eseries (EFin \o f).
Proof.
apply/boolp.funext => n.
rewrite /series /eseries /=.
elim: n => [|n IH]; first by rewrite !big_geq.
by rewrite !big_nat_recr //= EFinD IH.
Qed.

Section f_n.
Variable f_n : nat -> T -> R.
Hypothesis cf_n : forall i, continuous (f_n i).
Hypothesis f_n_ge0 : forall i y, 0 <= f_n i y.
Hypothesis f_n_le1 : forall i y, f_n i y <= 1.
Let f_sum := fun n : nat => \sum_(0 <= k < n) f_n k \* cst (2 ^- k.+1).

Local Lemma cf_sum n : continuous (f_sum n).
Proof.
rewrite /f_sum => x; elim: n => [|n IH].
  rewrite big_geq //; exact: cst_continuous.
rewrite big_nat_recr //=; apply: continuousD => //.
exact/continuousM/cst_continuous/cf_n.
Qed.

Local Lemma f_sumE x n : f_sum n x = [series f_n k x / 2 ^+ k.+1]_k n.
Proof. exact: (big_morph (@^~ x)). Qed.
Local Definition f_sumE' x := boolp.funext (f_sumE x).

Let f x := limn (f_sum^~ x).

Local Lemma ndf_sum y : {homo f_sum^~ y : a b / (a <= b)%N >-> a <= b}.
Proof.
move=> a b ab.
rewrite !f_sumE -subr_ge0 sub_series_geq // sumr_ge0 //= => i _.
by rewrite mulr_ge0.
Qed.

Local Lemma cvgn_f_sum y : cvgn (f_sum^~ y).
Proof.
apply: nondecreasing_is_cvgn; first exact: ndf_sum.
exists 1 => z /= [m] _ <-.
have -> : 1 = 2^-1 / (1 - 2^-1) :> R.
  rewrite -[LHS](@mulfV _ (2^-1)) //; congr (_ / _).
  by rewrite [X in X - _](splitr 1) mul1r addrK.
rewrite f_sumE.
apply: le_trans (geometric_le_lim m _ _ _) => //; last first.
  by rewrite ltr_norml (@lt_trans _ _ 0) //= invf_lt1 // ltr1n.
rewrite ler_sum // => i _.
by rewrite /geometric /= -exprS -exprVn ler_piMl.
Qed.

Local Lemma f_sum_lim n y :
  f y = f_sum n y + limn (fun n' => \sum_(n <= k < n') f_n k y * 2^- k.+1).
Proof.
have Hcvg := cvgn_f_sum.
have /= := nondecreasing_telescope_sumey n _ (ndf_sum y).
rewrite EFin_lim //= fin_numE /= => /(_ isT).
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
  exact/esym/big_morph.
by rewrite is_cvg_series_restrict -f_sumE'.
Qed.

Local Lemma sum_f_n_oo n y :
  0 <= \big[+%R/0]_(n <= k <oo) (f_n k y / 2 ^+ k.+1) <= 2^-n.
Proof.
have Hcvg := @cvgn_f_sum y.
apply/andP; split.
  have := nondecreasing_cvgn_le (ndf_sum y) Hcvg n.
  by rewrite [limn _](f_sum_lim n) lerDl.
have H2n : 0 <= 2^-n :> R by rewrite -exprVn exprn_ge0.
rewrite -lee_fin.
apply: le_trans (epsilon_trick0 xpredT H2n).
rewrite -EFin_lim; last by rewrite is_cvg_series_restrict -f_sumE'.
under [EFin \o _]boolp.funext do
  rewrite /= (big_morph EFin (id1:=0) (op1:=GRing.add)) //.
rewrite -nneseries_addn; last by move=> i; rewrite lee_fin mulr_ge0.
apply: lee_nneseries => i _.
  by rewrite lee_fin mulr_ge0.
by rewrite lee_fin natrX -!exprVn -exprD addnS addnC ler_piMl.
Qed.
End f_n.

Local Lemma perfectly_normal_space_12 : perfectly_normal_space_Gdelta -> perfectly_normal_space 0.
Proof.
move=> pnsGd E cE.
case: (pnsGd) => nT cEGdE.
have[U oU HE]:= cEGdE E cE.
have/boolp.choice[f_n Hn] n : exists f : T -> R, 
  [/\ continuous f, range f `<=` `[0, 1], f @` E `<=` [set 0] & f @` (~` U n) `<=` [set 1]].
  apply /uniform_separatorP /normal_uniform_separator => //.
  - by rewrite closedC.
  - rewrite HE -subsets_disjoint.
    exact: bigcap_inf.
have cf_n i : continuous (f_n i) by case: (Hn i).
have f_n_ge0 i y : 0 <= f_n i y.
    case: (Hn i) => _ Hr _ _.
    have /Hr /= := imageT (f_n i) y.
    by rewrite in_itv /= => /andP[].
have f_n_le1 i y : f_n i y <= 1.
    case: (Hn i) => _ Hr _ _.
    have /Hr /= := imageT (f_n i) y.
    by rewrite in_itv /= => /andP[].
pose f_sum := fun n => \sum_(0 <= k < n) (f_n k \* cst (2^-k.+1)).
have cf_sum := cf_sum cf_n.
pose f x := limn (f_sum ^~ x).
exists f.
split.
  move=> x Nfx.
  rewrite -filter_from_ballE.
  case => eps /= eps0 HB.
  pose n := (2 + truncn (- ln eps / ln 2))%N.
  have Hf := f_sum_lim f_n_ge0 f_n_le1 n.
  have eps0' : eps / 2 > 0 by exact: divr_gt0.
  move/continuousP/(_ _ (ball_open (f_sum n x) eps0')) : (cf_sum n) => /= ofs.
  rewrite nbhs_filterE fmapE nbhsE /=.
  set B := _ @^-1` _ in ofs.
  exists B.
    split => //; exact: ballxx.
  apply: subset_trans (preimage_subset (f:=f) HB).
  rewrite /B /preimage /ball => t /=.
  move=> feps.
  rewrite /f !Hf opprD addrA (addrAC (f_sum n x)) -(addrA (_ - _)).
  apply: (le_lt_trans (ler_normD _ _)).
  rewrite (splitr eps).
  apply: ltr_leD => //.
  have Hfn0 x := proj1 (andP (sum_f_n_oo f_n_ge0 f_n_le1 n x)).
  have Hfn1 x := proj2 (andP (sum_f_n_oo f_n_ge0 f_n_le1 n x)).
  apply: (@le_trans _ _ (2^-n)).
    rewrite ler_norml !lerBDl (le_trans (Hfn1 t)) ?lerDl //=.
    by rewrite (le_trans (Hfn1 x)) // lerDr.
  rewrite /n -exprVn addSnnS exprD expr1 ler_pdivrMl //.
  rewrite mulrA (mulrC 2) mulfK // -(@lnK _ (2^-1)) ?posrE //.
  rewrite -expRM_natl -{2}(@lnK _ eps) // ler_expR lnV ?posrE //.
  rewrite -ler_ndivrMr ?posrE; last by rewrite oppr_lt0 ln_gt0 // ltr1n.
  by rewrite invrN mulrN mulNr ltW // truncnS_gt.
apply/seteqP; split => x /= Hx.
  have Hcvg := cvgn_f_sum f_n_ge0 f_n_le1 (y:=x).
  apply: EFin_inj.
  rewrite -EFin_lim // f_sumE' EFin_series /= eseries0 // => i _ _ /=.
  case: (Hn i) => _ _ /(_ (f_n i x)) /= => ->.
    by rewrite mul0r.
  by exists x.
apply: contraPP Hx.
rewrite (_ : (~ E x) = setC E x) // HE setC_bigcap /= => -[] i _ HU.
case: (Hn i) => _ _ _ /(_ (f_n i x)) /= => Hfix.
rewrite /f => Hf.
have Hcvg := cvgn_f_sum f_n_ge0 f_n_le1 (y:=x).
have := nondecreasing_cvgn_le (ndf_sum f_n_ge0 x) Hcvg i.+1.
have := ndf_sum f_n_ge0 x (leq0n i.+1).
rewrite Hf big_geq // => /[swap] fi_le0.
rewrite le0r ltNge fi_le0 orbF.
rewrite big_nat_recr //= [X in X _ _ x]/GRing.add /= -/(f_sum i).
rewrite Hfix; last by exists x.
rewrite mul1r /cst => /eqP fi0.
have := ndf_sum f_n_ge0 x (leq0n i).
rewrite big_geq // -[0 x]fi0 gerDl.
by rewrite leNgt invr_gt0 exprn_gt0.
Qed.

Local Lemma perfectly_normal_space_23 : perfectly_normal_space 0 -> perfectly_normal_space' 0.
Proof.
move=> pns' E cE; case: (pns' (~`E)).
  by rewrite closedC.
move=> f [cf f0]; exists f.
split.
  by [].
by rewrite -[LHS]setCK f0 preimage_setC.
Qed.

Local Lemma perfectly_normal_space_32 : perfectly_normal_space' 0 -> perfectly_normal_space 0.
Proof.
move=> pns' E cE; case: (pns' (~`E)).
  by rewrite openC.
move=> f [cf f0]; exists f.
split.
  by [].
by rewrite -[RHS]setCK preimage_setC -f0 setCK.
Qed.

(* (norm \o f) @^-1` [set 0] = f @^-1` [set 0] *)
Lemma norm_preimage0 (f : T -> R) :
  continuous f ->
  exists f' : T -> R, [/\ continuous f', (forall x, f' x >= 0)
                        & f' @^-1` [set 0] = f @^-1` [set 0]].
Proof.
move=> cf; exists (fun x => `|f x|); split => //.
- move=> x; exact/continuous_comp/norm_continuous/cf.
- apply/seteqP; split => [x|x /= ->]; [exact: normr0_eq0 | by rewrite normr0].
Qed.

Local Lemma perfectly_normal_space_24 : perfectly_normal_space 0 -> perfectly_normal_space01.
Proof.
move=> pns0 E F cE cF EF.
have [_ [/norm_preimage0 [f [cf f_ge0 <-]] E0]] := pns0 E cE.
have [_ [/norm_preimage0 [g [cg g_ge0 <-]] F0]] := pns0 F cF.
have fg_gt0 x : f x + g x > 0.
  move: (f_ge0 x) (g_ge0 x).
  rewrite !le_eqVlt => /orP[/eqP|] Hf /orP[/eqP|] Hg; last exact: addr_gt0.
  + by move: EF; rewrite E0 F0 => /disj_setPRL/(_ x); elim.
  + by rewrite -Hf add0r.
  + by rewrite -Hg addr0.
have fg_neq0 x : f x + g x != 0 by apply: lt0r_neq0.
exists (fun x => f x / (f x + g x)); split.
- move=> x; apply: (continuousM (cf x)).
  apply: continuous_comp; [exact/continuousD/cg/cf | exact: inv_continuous].
- rewrite E0.
  apply/seteqP; split => x /=; first by move->; rewrite mul0r.
  move/(f_equal (GRing.mul ^~ (f x + g x))).
  by rewrite -mulrA mulVf // mulr1 mul0r.
- rewrite F0.
  apply/seteqP; split => x /=.
    rewrite -{1}(addr0 (f x)) => <-; exact: mulfV.
  move/(f_equal (GRing.mul ^~ (f x + g x))).
  rewrite -mulrA mulVf // mulr1 mul1r => /eqP.
  by rewrite addrC -subr_eq subrr eq_sym => /eqP.
- move=> _ [x] _ /= <-.
  have fgx : (f x + g x)^-1 >= 0 by apply/ltW; rewrite invr_gt0.
  by rewrite in_itv /= mulr_ge0 //= -(mulfV (fg_neq0 x)) ler_pM // lerDl.
Qed.

Local Lemma perfectly_normal_space_42 :                                 
perfectly_normal_space01  -> perfectly_normal_space 0.                  
Proof.                                                                  
move=> + E cE => /(_ E set0 cE closed0).                                
rewrite disj_set2E setI0 eqxx => /(_ erefl).                            
case=> f [] cf [] Ef [] _ _.                                            
by exists f; split.                                                     
Qed.                                                                    
                                                                        
Local Lemma perfectly_normal_space_41 :
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
move: perfectly_normal_space_12 perfectly_normal_space_24 perfectly_normal_space_41.
tauto.
Qed.

Theorem Vedenissoff_open : perfectly_normal_space_Gdelta <-> perfectly_normal_space' 0.
Proof.
move: Vedenissoff_closed perfectly_normal_space_23 perfectly_normal_space_32.
tauto.
Qed.

Theorem Vedenissoff01 : perfectly_normal_space_Gdelta <-> perfectly_normal_space01.
Proof.
move: perfectly_normal_space_12 perfectly_normal_space_24 perfectly_normal_space_41.
tauto.
Qed.

End perfectlynormalspace.
