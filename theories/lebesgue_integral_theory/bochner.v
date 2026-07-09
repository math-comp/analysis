From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop ereal topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun measurable_realfun.
From mathcomp Require Import normed_module measurable_structure simple_functions.
From mathcomp Require Import hahn_banach_theorem.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope measure_display_scope.

Lemma open_closed_measurable (t : topologicalType) :
(@open t).-sigma.-measurable = (@closed t).-sigma.-measurable.
Proof.
rewrite eqEsubset; split; rewrite{1}/measurable/=.
  apply: sigma_algebra_subl=> U oU.
  rewrite -(setCK U); apply: sigma_algebraC.
  apply: sub_sigma_algebra=>//; exact: open_closedC.
apply: sigma_algebra_subl=> F cF; rewrite -(setCK F); apply:sigma_algebraC.
apply: sub_sigma_algebra=>//; exact: closed_openC.
Qed.

(* Some should be moved in topology_structure.v, some in metric_structure.v*)
Section topology_lemmas.
Context {T : topologicalType}.

Definition separable :=
exists D: set T, countable D /\ dense D.

Definition separable_set (A : set T) :=
exists D,
  [/\ countable D, D `<=` A & forall O, A`&`O !=set0 -> open O -> O`&`D !=set0].

Lemma separableTE : separable = separable_set [set:T].
Proof.
apply: eq_exists=>A. rewrite [X in [/\ _, _ & X]] (_:_ = dense A)//.
  by under eq_forall do rewrite setTI.
by rewrite propeqE; split=>[[cA dA]|[cA _ dA]].
Qed.

Lemma separable_set0 : separable_set set0.
Proof. by exists set0; split=>// U; rewrite set0I =>[[x]]. Qed.
#[local] Hint Resolve separable_set0 : core.

Lemma bigcupT_separable [A : (set T)^nat] : (forall n, separable_set (A n)) ->
separable_set (\bigcup_n A n).
Proof.
move=>/choice [D_ /all_and3 [cDx DAx dDx]]. exists (\bigcup_n D_ n); split.
  exact: bigcup_countable. exact: subset_bigcup. move=> O [x [[n _ Anx] Ox] oO].
have /(dDx n O) /(_ oO) [y [Oy Dny]] : A n `&` O !=set0 by exists x.
by exists y; split=>//; exists n.
Qed.

Lemma bigcup_separable [A : (set T)^nat] [P : set nat] :
(forall n, P n -> separable_set (A n))
-> separable_set (\bigcup_(i in P) A i).
Proof.
rewrite bigcup_mkcond => nsPA. apply: bigcupT_separable=>n.
case: ifPn=>[|_]. rewrite in_setE. apply: (nsPA n).
by exists set0; split=>// U [x [F]].
Qed.

Lemma basisP {B : set_system T} : basis B <-> B `<=`open
/\ (forall U: set T, open U -> U = \bigcup_(V in [set W | B W /\ W `<=`U]) V).
Proof.
split=> [[oB bB]|[Bo dec]]. split=> //U oU.
  rewrite eqEsubset /bigcup; split=>[x Ux/=|x [A/= [BA AU] /AU //]].
  have:= bB x. rewrite/cvg_to {2}/nbhs/filter_from/= => /(_ U)/=.
  have nT: \near x, U x by apply: (open_in_nearW oU)=>[y|]; rewrite in_setE.
  rewrite nbhs_nearE !exists2E/= => /(_ nT).
  by under eq_exists=>x0 do rewrite -andA {1}(andC (x0 x) _) andA.
split=>// x. rewrite/cvg_to/=nbhsE/open_nbhs => P /=
  [U [/(dec U)->] [A [BA AU] Ax] UP]. exists A=>// t At; apply: UP. by exists A.
Qed.

Lemma countable_basis_to_seq {B : set_system T} :
countable B -> basis B -> [set:T] !=set0 -> exists f : nat -> _, range f = B /\
forall U : set T, open U -> U = \bigcup_(n in [set m| f m `<=`U]) (f n).
Proof.
move=> /pfcard_geP /=. case=> [->/basisP[_ /(_ setT openT) /= d0]
  /set0P/eqP T0|/surjfunPex [f ->]/basisP[Bo dec]]; first exfalso.
  move: d0; rewrite (_ : [set _ | False /\ _] = set0) ?bigcup0//.
    by apply: eq_set=> y; apply: notTE=>[[]].
exists f; split=>//. move=> U /(dec U) ->; apply:eq_set=>x/=.
rewrite !exists2E propeqE; split=>//=[[A [[[n _ <- fnU] fnx]]]| [n [fni fnx]]].
  exists n; split=>//= y fny/=. exists (f n)=>//. split=>//. by exists n.
exists (f n); split=>//; split=>[|y /fni/= [V [_ VU /VU//]]]. by exists n.
Qed.

Lemma second_countable_separable :
@second_countable T -> separable.
Proof.
move=> [B] /(sub_countable (card_le_setD B [set set0])).
rewrite/countable=> /pfcard_geP. case=> [|[f] /basisP [oB bB]].
rewrite setD_eq0=> /subset_set1. case=> -> /basisP [oB bB];
  have:= (bB [set:T]) openT. rewrite [X in \bigcup_(_ in X) _] (_:_ = set0).
      by apply: eq_set=>x/=; rewrite andB.
    by rewrite bigcup0 // separableTE => ->.
  rewrite [X in \bigcup_(_ in X) _] (_:_ = [set set0]).
    by apply: eq_set=>A/=; rewrite (propT (subsetT A)) andB.1.2.
  by rewrite bigcup_set1 separableTE=> ->.
have rfB0:= image_eq f.
have /choice [g BG]: forall n, exists x, B (f n) /\ f n x. move=>n;
  have := imageT f n. by rewrite rfB0=>/= [[Bfn /eqP/set0P [x fnx]]]; exists x.
exists (range g); split=>[|A /[swap] /(bB A) -> /bigcup_nonempty
  [V /= [BV VA] /set0P/eqP V0]]; first exact: card_image_le.
have : (B `\ set0) V by split. rewrite -rfB0 => [[n _ fnV]].
exists (g n); split=>//; exists V=>//=. by rewrite -fnV; have [_] := (BG n).
Qed.

Lemma salgebra_second_countable {B : set_system T} :
countable B -> basis B -> open.-sigma.-measurable = B.-sigma.-measurable.
Proof.
move=> cB bB; have [T0|/set0P/(countable_basis_to_seq cB bB) [f [rfb dec]]] :=
  eqVneq [set:T] set0.
  have o0 : @open T = [set set0]. rewrite eqEsubset; split=> [U _| A ->] /=;
      first by rewrite -subset0 -T0. exact: open0.
  rewrite/measurable/= eqEsubset; split; first rewrite o0.
    apply: sigma_algebra_subl=> x ->. exact: sigma_algebra0.
  by have [/sigma_algebra_sub P _] := bB.
rewrite eqEsubset =>/=; split. apply: sigma_algebra_subl => U /(dec U)->.
  rewrite bigcup_mkcond -rfb; apply: sigma_algebra_bigcup => i /=.
  case: ifP=> _//. exact: sub_sigma_algebra. exact: sigma_algebra0.
by apply: sigma_algebra_sub; have [] := bB.
Qed.

End topology_lemmas.

Section uniform_lemmas.
Context {U : choiceType} {V : uniformType}.

Lemma cvg_uniform_fin_bigcup [f : U -> V] [F : set_system (U -> V)] {I}
    [D : set I] {A : I -> set U} : Filter F -> finite_set D ->
(forall i, D i -> {uniform A i, F --> f}) ->
{uniform \bigcup_(i in D) A i, F --> f}.
Proof.
move=> fF /finite_setP [n]. move:D.
elim:n=>/=[D|n Ih D /eq_cardSP [x Dx /Ih Dxn] UD].
  rewrite II0 card_eq0 => /eqP -> _; rewrite bigcup0 => //=;
  exact: cvg_uniform_set0. rewrite -(setD1K Dx) bigcup_setU1.
apply: cvg_uniformU. exact: (UD x). by apply: Dxn=>i [/UD Di//].
Qed.
End uniform_lemmas.

(* TODO: move all of this to metric spaces *)
Section norm_lemmas.

Definition norm_separable_set {K : numDomainType}
  {M : pseudoMetricType K} (A : set M) := exists D,
  [/\ countable D, D `<=` A & forall (x : M) (r : K),
0<r -> A x -> D `&` ball x r !=set0].

Lemma norm_separableP {K : numDomainType} {M : pseudoMetricNormedZmodType K}
  (A : set M) : norm_separable_set A <-> separable_set A.
Proof.
split=>[[D [cD DA dD]]|[D [cD DA DD]]]; exists D. split=>// U [x [Ax Ux] oU].
  have /nbhs_ballP/= : nbhs x U by apply/open_nbhs_nbhs.
  rewrite /nbhs_ball/nbhs_ball_ => [[r /= /[dup] r0 /(dD x)/= /(_ Ax)
    [d [Dd bdrx]] bxrA]]. exists d; split=>//=; exact: bxrA.
split=>//= x r r0 Ax. rewrite setIC; apply: (DD (ball x r));
  last exact: ball_open.
exists x; split=>//; exact: ballxx.
Qed.

Definition totally_bounded {K : numDomainType} {M : pseudoMetricType K}
  (A : set M) := forall eps, 0<eps -> exists F, [/\ finite_set F,
  F `<=` A & A `<=` \bigcup_(x in F) ball x eps].

Lemma totally_bounded_invnP {K : realType} {M : pseudoMetricType K}
  (A : set M) : totally_bounded A <-> forall n, exists F, [/\ finite_set F,
  F `<=` A & A `<=` \bigcup_(x in F) ball x n.+1%:R^-1].
Proof.
split=> [tA n| /choice [F /all_and3 [Ffset FA AbF]] eps e0].
  exact: (tA n.+1%:R^-1). set n := truncn (eps^-1).
exists (F n); split=>//. have leb : forall x, F n x ->
  ball x n.+1%:R^-1 `<=` ball x eps. move=> x Fnx; apply: le_ball.
  rewrite invf_ple ?posrE //; exact (ltW (truncnS_gt eps^-1)).
exact: (subset_trans (AbF n) (subset_bigcup leb)).
Qed.

Lemma totally_bounded_separable {K : realType} {M : pseudoMetricNormedZmodType K}
(A : set M) : totally_bounded A -> separable_set A.
Proof.
move=> /totally_bounded_invnP/choice [F /all_and3 [fF FA AbF]].
apply/norm_separableP.
  exists (\bigcup_n F n); split=>[||x r r0 /(AbF (truncn r^-1)) [d Fd bd]].
    apply: bigcup_countable=> // i _; exact: finite_set_countable.
  exact: bigcup_sub. exists d; split. by exists (truncn r^-1).
apply: ball_sym; apply: le_ball bd. rewrite invf_ple ?posrE //;
exact: (ltW (truncnS_gt r^-1)).
Qed.

(* Should be generalized to metric spaces,
but normedModType doesn't inherit from metricType yet*)
Lemma closed_dist0 {R:realType} {N:normedModType R} {F : set N}
(cF : closed F) (x:N) :
F x = forall e:R, 0 < e -> exists f:N, F f /\ `|x - f| < e.
Proof.
  rewrite propeqE; split=>[Fx e|Cx]. exists x; split=>//=. by rewrite subrr normr0.
  have Q : forall n:nat, exists f:N, F f /\ `|x-f| < n.+1%:R^-1.
  move=> n; apply: (Cx n.+1%:R^-1)=>//.
  have [f Pf] := choice Q. apply: (@closed_cvg _ _ _ eventually_filter f _ cF).
  by exists 0=>// n _; have [Ffn _] := Pf n.
  apply/cvg_ballP=> e e0. rewrite pseudo_metric_ball_norm/=.
  have Pfe := (Pf (truncn (e^-1))). near=>n. apply: (@lt_trans _ _ (n.+1%:R^-1)).
  near:n. by apply: nearW=>n; have [_ d] := (Pf n).
  rewrite invf_plt=>//. by rewrite posrE. apply: (@lt_trans _ _ n%:R).
  near:n. exact: nbhs_infty_gtr. by rewrite ltr_nat.
Unshelve. all: end_near. Qed.

Lemma supP {R : realType} (S : set R) (x : R) (supS: has_sup S) :
sup S <= x <-> forall y, S y -> y<=x.
Proof.
split=> [sSx y Sy|Sx]. apply: (le_trans _ sSx); exact: sup_upper_bound.
apply: ge_sup=>//. by apply/set0P/eqP=> S0; apply: (@has_sup0 _ R); rewrite -S0.
Qed.

Lemma gt_sup {R : realType} (S : set R) (x : R) (supS : has_sup S):
sup S < x -> forall y, S y -> y<x.
Proof.
move=> sSx y Sy. apply: (le_lt_trans _ sSx); exact: sup_upper_bound.
Qed.

Lemma uniform_to_norm  {T : choiceType} {R : realType} {N : normedModType R}
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0) (eps:R) (e0 : 0<eps):
{uniform A, f_ @ \oo --> f} ->
\forall n \near \oo, forall t:T, A t -> `|f_ n t - f t| < eps.
rewrite -nbhs_entourageE uniform_entourage => [/filter_fromP/= Cuf].
set C := [set gf: (T->N)*_ | forall t, A t -> ball (gf.1 t) eps (gf.2 t)].
have: nbhs \oo (f_ @^-1` xsection C f). apply: Cuf.
  apply: (@in_filter_from _ _ _ _ [set xy | ball xy.1 (PosNum e0)%:num xy.2]);
  exact: entourage_ball. rewrite /xsection/=. under eq_set do rewrite in_setE.
rewrite/C/= => [[n0 _ Cvn]]; exists n0=>//n/Cvn. rewrite -ball_normE/= =>
/[swap] t /[swap] At /(_ t At) fnte. by rewrite distrC.
Qed.

Lemma uniform_cvg_sup0 {T : choiceType} {R : realType} {N : normedModType R}
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0):
{uniform A, f_ @ \oo --> f} <->
(\forall n\near \oo, has_sup [set `|f_ n x - f x| | x in A]) /\
sup [set `|f_ n x - f x| | x in A] @[n--> \oo] --> 0.
Proof.
split=>[/(uniform_to_norm An0) L |[[n1 _ has_sup_n1] /cvgr0Pnorm_lt s0]].
  split. have [n0 _ fNf1] := (L 1 ltr01).
    exists n0=>// n /fNf1 fnf1; split. exact: image_nonempty.
    exists 1=>a [t At <-]. exact: (ltW (fnf1 t At)).
  apply/cvgr0Pnorm_le => e /(L e) [n0 _ fNfe]. exists n0=>// n /fNfe fnfe.
  have /normr_idP -> : 0 <= sup [set `|f_ n x - f x| | x in A] by
  apply: sup_ge0=>x /= [t At <-]; exact: normr_ge0. apply/supP=>[|y [t At <-]].
    split. exact: image_nonempty. exists e=> a [t At <-].
    1,2: try (exact: (ltW (fnfe t At))).
rewrite -nbhs_entourageE uniform_entourage -entourage_from_ballE =>
[F/= [G [H [e/=e0 beH] HG]]]. rewrite/xsection; under eq_set do rewrite in_setE.
have [n0 _ Nfe] := s0 e e0 => GF. exists (maxn n0 n1)=>// n.
under eq_set do rewrite geq_max. move=> /andP /[dup] [[n0n n1n]] [/Nfe].
have /normr_idP -> : 0 <= sup [set `|f_ n x - f x| | x in A] by
  apply: sup_ge0=>x /= [t At <-]; exact: normr_ge0.
move=> /[swap] /(has_sup_n1) hs /(gt_sup hs) fnfe/=. apply: GF;
apply: HG=>t At; apply: beH=>/=. rewrite -ball_normE/= distrC. apply: fnfe.
by exists t.
Qed.

Lemma uniform_cvg_has_sup0 {T : choiceType} {R : realType} {N : normedModType R}
{f_ : (T->N)^nat} {f : T -> N} (A : set T) (An0 : A !=set0):
{uniform A, f_ @ \oo --> f} <->
forall eps, 0<eps -> \forall n\near \oo, has_sup
  [set `|f_ n x - f x| | x in A] /\ sup [set `|f_ n x - f x| | x in A] < eps.
Proof.
apply: (iff_trans (uniform_cvg_sup0 An0)); split=> [[hs /cvgr0_norm_lt s0 eps
/(s0 eps) se]|S0]. near=>n; split. by near:n. rewrite -[X in X < _](normr_idP _).
  apply: sup_ge0=> x [y _ <-]//. by near:n.
split. have [n _ nP] := S0 1 ltr01; exists n=>// n0 /nP [//].
apply/cvgr0Pnorm_lt=> eps /(S0 eps) [n0 _ ns]. exists n0=>// n /ns [_ se].
by rewrite (normr_idP _)//; apply: sup_ge0=> x [y _ <-]//.
Unshelve. all: end_near. Qed.

End norm_lemmas.

(*Should be moved to measurable_fun.v*)
Section measurable_fun_lemmas.

Lemma measurable_fun_open_closed {d} {aT : measurableType d}
{T : topologicalType} {D : set aT} (f : aT -> T) :
measurable_fun D (f : aT -> g_sigma_algebraType (@open T)) =
measurable_fun D (f : aT -> g_sigma_algebraType (@closed T)).
Proof.
  rewrite propeqE; split=> mf mD Y;
  [rewrite -open_closed_measurable| rewrite open_closed_measurable]; exact: mf.
Qed.

Import MeasurableR.
(*Cannot be generalized yet as it is for a different display from normr_continuous*)
Lemma normr_measurable_gen {R : realType} {N : normedModType R} {A : set N} :
measurable_fun A normr.
Proof.
move=> /[dup] mA.
apply: (@measurability _ _ _ _ _ (@normr R N) _
  (eq_trans (esym (RGenOpenSets.measurableE R)) (RGenOInfty.measurableE R))).
move=> U [I [x] ->] <-. have [/(_ norm_continuous) nopen _] :=
  continuousP (normr: N-> R). apply: measurableI => //.
apply: sub_sigma_algebra; exact: nopen.
Qed.

Lemma measurable_fun_dist {d} {A : measurableType d} {R : realType}
{N : normedModType R} {f g : A -> N} {D : set A}: separable_set (image D f)
-> measurable_fun D f -> measurable_fun D g -> measurable D ->
forall (r:R), 0<r -> measurable (D `&` [set a | `|f a - g a| < r]).
Proof.
move=> /norm_separableP [Df [cDf _ DF]] mf mg mD r r0.
rewrite ( _ : (_ `&`_) = \bigcup_q \bigcup_(z in Df)
\bigcup_(k in [set k | rat.ratr q + k.+1%:R^-1 < r])
  (D `&` f@^-1`(ball z k.+1%:R^-1) `&` (D `&` g@^-1`(ball z (rat.ratr q))))).
  rewrite eqEsubset /bigcup; split=>[x [Dx /= fgxr]|x [q _ /= [z Dfz] [k qkr]
      [[Dx bzkf] [_ bzqg]]]].
    have /dense_rat/(_ (itv_open `|f x - g x| r)) /=[q] :
      `]`|f x - g x|, r[%classic !=set0. exists ((`|f x - g x|+r)/2).
      rewrite/=in_itv/=. apply/andP;split; by apply (midf_lt fgxr).
    rewrite /=in_itv=>/= [[/andP[fgq qr]] [q1 _ q1q]].
    pose eps := minr (q - `|f x - g x|) (r-q). pose k := truncn eps^-1.
    have eps0 : 0 < eps by rewrite lt_min !subr_gt0; apply/andP.
    have [erq eqfg] : eps <= r-q /\ eps <= q - `|f x - g x| by
      rewrite !ge_min; split; apply/orP; [right|left].
    exists q1=>//=. rewrite q1q/=.
    have ke : k.+1%:R^-1 < eps by rewrite invf_plt ?posrE//;
      exact: truncnS_gt.
    have k0 : (0:R) < k.+1%:R^-1 by rewrite invr_gt0.
    have [z [Dfz]] := DF (f x) _ k0 (imageP f Dx); rewrite -ball_normE/=distrC.
    exists z=>//. exists k. rewrite -ltrBrDl. exact: (lt_le_trans ke erq).
    split=>//; split=>//. apply: (le_lt_trans (ler_distD (f x) z (g x))).
    rewrite -(addrNK `|f x - g x| q).
    exact: (ltr_leD (lt_le_trans (lt_trans b ke) eqfg)).
  split=>//; rewrite -ball_normE /= in bzkf, bzqg.
  apply: (le_lt_trans (ler_distD z _ _) (lt_trans _ qkr)).
    rewrite addrC (distrC (f x) z); exact: ltrD.
apply: bigcupT_measurable_rat=> q. apply: countable_bigcup_measurable=>// z Dfz.
apply: bigcup_measurable=>k /= qkr.
  apply: measurableI; [apply: (mf mD)|apply: (mg mD)];
  apply: sub_sigma_algebra; exact: ball_open.
Qed.

(* Lemma 4.29 Infinite Dimensional Analysis A Hitchhikers Guide,
Third Edition (Charalambos D. Aliprantis, Kim C. Border)*)
Lemma measurable_fun_cv {d} {T : measurableType d} {R : realType}
{X : normedModType R} [D : set T] [h : (T->X)^nat] [f : T -> X] :
(forall m:nat, measurable_fun D (h m)) ->
(forall x : T, D x -> h ^~ x @\oo --> f x)
-> measurable_fun D f.
Proof.
move=> mhn hf; rewrite measurable_fun_open_closed.
rewrite/measurable_fun=> /[dup] mD. apply: measurability=>// C. case=>F cF<-.
pose G n := [set y | exists c, F c /\ `|c-y| < (n.+1%:R)^-1].
rewrite [D`&`f@^-1` F] (_:_ = \bigcap_m \bigcup_n \bigcap_(k>=n)
  (D `&` (h k) @^-1` (G m))).
  rewrite eqEsubset; split=>[x/= [Dx]|x b/=].
    rewrite closed_dist0// => Fx m _.
    have : (0:R)<(m.+1%:R^-1)/2 by apply divr_gt0.
    move=> /[dup] m20 /Fx [y [fy fxym]].
    have /(_ eventually_filter _ m20) [n0 _ fhn0] := cvgr_dist_lt _ _ (hf x Dx).
    exists n0=>// n /fhn0 fhnm2. split=>//; exists y; split=>//.
    rewrite [X in _<X]splitr.
    apply: (le_lt_trans (ler_distD (f x) _ _) (ltrD _ _))=>//.
      by rewrite distrC.
  have Dx : D x by have [n _ /(_ n (le_refl n)) [Dx _]] := b 0 I.
  split=>//; rewrite closed_dist0// => e e0.
  have e20 : 0 < e/2 by apply: divr_gt0. have [n0 _] := b (truncn (e/2)^-1) I.
  have/(_ eventually_filter _ e20) [n1 _ /(_ (maxn n0 n1) (leq_maxr n0 n1)) fhe]
    := cvgr_dist_lt _ _ (hf x Dx).
  move=> /(_ (maxn n0 n1) (leq_maxl n0 n1)) [_ [/=f0 [f0F yhe]]].
  exists f0; split=>//. rewrite (splitr e).
  apply: (le_lt_trans (ler_distD (h (maxn n0 n1) x) _ _) (ltrD _ _))=>//.
  rewrite distrC; apply: (lt_trans yhe). rewrite invf_plt ?posrE//.
  exact: truncnS_gt.
apply: bigcap_measurable=>// m _. apply: bigcup_measurable=>// n _.
apply: bigcap_measurableType => k /= nk. apply: (mhn k)=>//.
apply: sub_sigma_algebra.
rewrite [X in open X] (_:_ = \bigcup_(c in F) [set y | `|c-y| < m.+1%:R^-1]).
  by apply eq_set=> x/=; rewrite exists2E.
apply: bigcup_open=> f0 f0F. have df0c : continuous (normr \o(fun y=> f0-y)).
  move=> x; apply: continuous_comp. apply: continuousB=>//.
    exact: cst_continuous. exact: norm_continuous.
rewrite -preimage_itvNyo. exact: open_comp.
Qed.

End measurable_fun_lemmas.

Section measure_lemmas.
Context d {T : measurableType d} {R : realType} {mu : {measure set T -> \bar R}}.

Lemma measure0P {A} : (forall eps, 0<eps -> (mu A < eps%:E)%E) -> mu A = 0.
Proof.
move=> mAe. apply/eqP; rewrite eq_le; apply/andP; split=>//.
apply/le_ltP=> z z0. have [/(_ (ltW z0)) [->|[r r0 rz]] _] := (gee0P z).
  apply: (lt_trans (mAe 1 (ltr01))). exact: ltry.
by move: z0; rewrite rz lte_fin=> /mAe.
Qed.

Lemma measure0P_invn {A} : (forall n, (mu A < n.+1%:R^-1%:E))%E -> mu A = 0.
Proof.
move=> mAn; apply/measure0P=>eps e0. apply: (lt_trans (mAn (truncn eps^-1))).
rewrite lte_fin invf_plt ?posrE //; exact: truncnS_gt.
Qed.

End measure_lemmas.

Section almost_uniform_cvg.
Context {d} {T : measurableType d} {R : realType}
{U : pseudoMetricType R} (mu : {measure set T -> \bar R})
(f_ : (T->U)^nat) (f : T -> U).

Definition almost_uniform_cvg  (D : set T) :=
forall eps:R, 0<eps -> exists E, [/\ measurable E, (mu E < eps%:E)%E &
    {uniform D `\` E, f_ @ \oo --> f}].

Definition almost_uniform_cvgT :=
forall eps:R, 0<eps -> exists E, [/\ measurable E, (mu E < eps%:E)%E &
    {uniform ~`E, f_ @ \oo --> f}].

Lemma almost_uniform_cvgTP : almost_uniform_cvg [set:T] <-> almost_uniform_cvgT.
Proof.
by rewrite /almost_uniform_cvg/almost_uniform_cvgT;
  under eq_forall do under eq_exists do rewrite setTD.
Qed.

Lemma almost_uniform_cvg_nnincseqP (D : set T) (h : R^nat)
(ph : forall n, 0 < h n) (h0 : h @ \oo --> 0) : almost_uniform_cvg D <->
exists E_ : (set T)^nat, {homo E_ : n m / (n<=m)%N >-> (m<=n)%O} /\
  forall n, [/\ measurable (E_ n), (mu (E_ n) < (h n)%:E)%E &
  {uniform D`\`(E_ n), f_ @ \oo --> f}].
Proof.
split=>[aucD|[E_ [nniE /all_and3 [mE0 mEn CuEn] eps e0]]].
  have /choice [E /all_and3 [mE0 mEn CuEn]] : forall n, exists E,
  [/\ measurable E, (mu E < (h n)%:E)%E & {uniform D`\`E, f_ @ \oo --> f}] by
    move=>n; apply: (aucD (h n)).
  exists (fun n => \bigcap_(k < n.+1) (E k)); split.
  apply/nonincreasing_seqP=>n/=.
  rewrite subsetEset/bigcap => x /= bn2x i in1;
    exact: (bn2x i (ltn_trans in1 (ltnSn n.+1))).
  move=>n. split. apply: bigcap_measurableType=>//.
    apply: (le_lt_trans _ (mEn n)). apply: le_measure; rewrite ?in_setE//.
      apply: bigcap_measurableType=>//. apply: bigcap_inf=>/=; exact: ltnSn.
  rewrite setD_bigcapr; exact: cvg_uniform_fin_bigcup.
have [n0 _ /=/(_ n0 (le_refl n0))]:= cvgr0_norm_lt h h0 eps e0.
rewrite (normr_idP (ltW (ph n0)))=> hne; exists (E_ n0); split=>//.
exact: lt_trans.
Qed.

End almost_uniform_cvg.

Section egorov.
Context d {R : realType} {N : normedModType R}
 {T : measurableType d} {mu : {finite_measure set T -> \bar R}}.
Import MeasurableR.

(* A more general version of Erogov's theorem *)
Lemma pointwise_almost_uniform_sep (f : (T -> N)^nat) (g : T -> N)
  (D : set T) : (forall n, separable_set (image D (f n)))
  -> (forall n, measurable_fun D (f n)) ->
  measurable D -> (forall x, D x -> f ^~ x @ \oo --> g x) ->
  almost_uniform_cvg mu f g D.
Proof.
move=> sf mf mD fg eps e0. pose A n k := D `&`
  [set x | `|f n x - g x| >=k.+1%:R^-1]. have mg := measurable_fun_cv mf fg.
have mA : forall n k, measurable (A n k).
  rewrite /A/==>n k. rewrite -setDD {2}/setD/= [X in _`\`X] (_:_ =
    [set x| D x /\ `|f n x - g x| < k.+1%:R^-1]).
    apply: eq_set=>x. rewrite propeqE; split=>/=[[Dx nle]|[Dx lt]]; split=>//.
      apply: (contra_not_lt nle)=>//.
    exact: (@contra_lt_not _ _ (k.+1%:R^-1 <= `|f n x - g x|) _ _ _ lt).
  apply: measurableD=>//. exact: measurable_fun_dist.
pose B n k := \bigcup_(i>=n) A i k. have mB: forall n k, measurable (B n k)
  by rewrite/B=> n k; apply: bigcup_measurable.
have capB_0 : forall k, \bigcap_n B n k = set0.
  rewrite/bigcap/B/bigcup/A/==>k; rewrite -subset0 =>a/=. apply: contraPP=> _.
  rewrite -existsNE. under eq_exists do rewrite not_implyE exists2E -forallNE.
  have[ad|nad]:= pselect (D a).
    have k0 : (0:R) < k.+1%:R^-1 by rewrite invr_gt0.
    have /(_ eventually_filter) [n0 _ nfg] := cvgr_dist_lt _ _ (fg a ad) _ k0.
    exists n0; split=>// n [n0n [_ kfg]].
    rewrite -falseE -(lt_irreflexive (k.+1%:R^-1: R)); apply: (le_lt_trans kfg).
    rewrite distrC; exact: nfg.
  by exists 0; split=>//n; rewrite not_andE not_andE; right; left.
have cvB0 : forall k, fine (mu (\bigcap_(i<n.+1) B i k)) @[n --> \oo] --> 0.
  move=>k; rewrite (_: 0 = fine (mu (\bigcap_n B n k))).
  by rewrite capB_0 measure0.
  apply: fine_cvg; rewrite fineK ?fin_num_measure//.
    exact: bigcapT_measurable. apply: (cvg_measure_bigcap (mB ^~ k)).
  exact: fin_num_measure.
have /choice [p pBe] : forall k, exists n, true ->
  (mu (\bigcap_(i<n) B i k) <= (eps / 2 / (2^ k.+1)%:R)%:E)%E. move=>k.
  have ekp : 0 < eps / 2 / 2 ^ k.+1 by rewrite ltr_pdivlMr ?mul0r ?divr_gt0.
  have /(_ eventually_filter) [n0 _ /(_ _ (le_refl n0)) /ltW Bn0e2k] :=
    cvgr0_norm_lt _ (cvB0 k) _ ekp. exists n0.+1 => _.
  have mBn0 : measurable (\bigcap_(i < n0.+1) B i k)
    by exact: bigcap_measurableType.
  rewrite -[X in (X <= _)%E](fineK) ?fin_num_measure// lee_fin/= -?lee_fin
    ?fineK ?fin_num_measure// -[X in (X <= _)%E]fineK ?fin_num_measure//.
  rewrite lee_fin -[X in X <= _]ger0_norm. exact: fine_ge0.
  by rewrite (_ : (_ ^ _)%:R = 2 ^ k.+1) ?natrX.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have mBp : forall k, measurable (\bigcap_(i<p k) (B i k))
  by move=>k; exact: bigcap_measurableType.
pose C := (\bigcup_k \bigcap_(i<(p k)) (B i k)). exists C; split=>[||].
    exact: bigcupT_measurable.
  apply: (le_lt_trans (generalized_Boole_inequality mu mBp _)).
    exact: bigcup_measurable.
  have e2e : ((eps / 2)%:E < eps%:E)%E by rewrite lte_fin ltr_pdivrMr // ltr_pMr
    // {1}(_ : 1 = (1 : nat)%:R) ?ltr_nat //.
  have nn_muB : forall i, (0 <= i)%N -> true ->
    (0 <= mu (\bigcap_(i0 < p i)  B i0 i))%E by move=> i _ _; exact:measure_ge0.
  exact: (le_lt_trans (le_trans (lee_nneseries nn_muB pBe)
    (epsilon_trick0 xpredT (ltW e20))) e2e).
apply/uniform_restrict_cvg=> U/=; rewrite uniform_nbhsT.
case/nbhs_ex => r /= ballU; apply: filterS; first by move=> ?; exact: ballU.
have [n0 _ /(_ n0)/(_ (leqnn _)) n0ir] := near_infty_natSinv_lt r.
exists (p n0)=>// n /=pn0n x; rewrite /patch. case: ifPn=>//.
rewrite setDE in_setE=> [[Dx]]; rewrite setC_bigcup /B/A => /(_ n0 I).
rewrite setC_bigcap; under eq_bigcupr do rewrite setC_bigcup.
move=> [i /= ipn0] /(_ n (ltnW (ltn_leq_trans ipn0 pn0n))).
rewrite setCI /=; case=>[/(_ Dx) //|].
move=> /contra_not_lt; rewrite notB.2 => /(_ I) /lt_trans /(_ n0ir) //.
by rewrite -ball_normE distrC.
Qed.

End egorov.


Section bochner_measurable_function.
Import MeasurableR.
Context {d} {T : measurableType d} {R : realType}
  (mu : {finite_measure set T -> \bar R}) (X : normedModType R).

(* TODO : remove the lmodType cast when bug fixed*)
Definition bochner_measurable (f: T -> X) :=
  exists f_ : ({sfun T >-> X} : lmodType _)^nat,
\forall x \ae mu, f_ n x @[n --> \oo]--> f x.

Lemma bmeas_meas (f : T -> X) : bochner_measurable f -> measure_is_complete mu
 -> measurable_fun [set:T] f.
Proof.
move=> [F [A [mA mA0 /subsetCl cv]]] cmu. rewrite -(setvU A).
apply/measurable_funU=>//. exact: measurableC. split=>[|_ Y mY].
  apply: measurable_fun_cv _ cv=>m. apply: measurable_funP.
apply: cmu. apply: (negligibleS (@subIsetl _ A (f@^-1`Y))).
by exists A; split.
Qed.

Lemma bmeasD (f g : T -> X) : bochner_measurable f -> bochner_measurable g ->
bochner_measurable (f + g).
Proof.
move=> [F [A [mA mA0 /subsetCl FfxA]]] [G [B [mB mB0 /subsetCl GgxB]]].
exists (F+G); exists (A`|`B); split. exact: measurableU. exact: null_set_setU.
apply: subsetCl; rewrite setCU => x [/FfxA Ffx /GgxB /= Ggx]; exact: cvgD.
Qed.

Lemma bmeasZ (x : R) (f : T -> X) (mmf : bochner_measurable f) :
bochner_measurable (x *: f).
Proof.
case: mmf=> F [A [mA mA0 CnA]]. exists (x*:F); exists A; split=>//.
apply: (subset_trans _ CnA). apply: subsetC=>y /=. exact: cvgZl_tmp.
Qed.

Lemma countim_bmeas (f : T -> X) (mf : forall z, measurable (f@^-1`[set z])):
 countable (range f) -> bochner_measurable f.
Proof.
move=> /countable_bijP [B] /card_esym/card_set_bijP /= [h] /[dup]
  /set_bij_inj ih /set_bij_surj; rewrite surjE=> rfh.
pose a n := mindic_lmod_sfun (mf (h n)) (h n): {sfun T>->X} : lmodType _.
pose f_ n := \sum_(i<n | `[<B i>]) a i.
exists f_; exists set0; split=>//. apply:subsetCl.
rewrite setC0 -(preimage_range f).
apply: (subset_trans (preimage_subset rfh)).
rewrite -bigcup_imset1 preimage_bigcup => t [n0 /asboolP Bn0/=fthn].
apply/cvgrPdist_lt=> /= eps e0. exists n0.+1 => // n /= n0n.
apply: (le_lt_trans _ e0); rewrite normrE subr_eq0 fthn /f_; apply/eqP.
rewrite sfun_sum /=; under eq_bigr do rewrite /mindic_lmod/indic_lmod /= indicE.
rewrite (bigD1_ord (Ordinal n0n)) //= mem_set //= scale1r.
have indeq0 : forall i,
  `[<B (bump n0 i)>] -> t \in (f @^-1` [set h (bump n0 i)]) = 0%N :> nat.
  rewrite /preimage /= => i Bi. apply/eqP;
  rewrite eqb0 notin_setE /= fthn => /ih. by rewrite !in_setE=>
  /(_ (asboolW Bn0) (asboolW Bi)) /eqP /(negP (neq_bump n0 i)).
under eq_bigr do rewrite indeq0 // scale0r. by rewrite big_const_idem /= addr0.
Qed.

Lemma sfun_norm_sep_val (f : {sfun T >-> X}) (D:set T) :
separable_set (image D f).
Proof.
apply/norm_separableP.
exists (image D f); split=>//[|y r r0 [x Dx <-]]. apply: finite_set_countable.
  exact: (sub_finite_set (image_subset f (subsetT D))).
exists (f x); split=>//; exact: (ballxx (f x) r0).
Qed.

Lemma bmeas_almost_uniformP (f : T -> X) : bochner_measurable f <->
exists (f_ : {sfun T >-> X}^nat), almost_uniform_cvgT mu f_ f.
Proof.
split=> [[f_ [N [mN mN0 /subsetCl f_fN]]]|[f_] Cf]. exists f_=> eps eps0.
  have nsf_ : forall n, separable_set [set f_ n x  | x in ~` N] by move=>n;
    apply: sfun_norm_sep_val.
  have mf_ : forall n, measurable_fun (~`N) (f_ n) by move=>n;
    exact: (measurable_funS measurableT).
  have[E [mE0 mEe f_fnE]]:= @pointwise_almost_uniform_sep _ _ _ _ mu f_ f (~`N)
    nsf_ mf_ (measurableC mN) f_fN eps eps0.
  exists (E`|`N); split. exact: measurableU. by rewrite measureU0.
  rewrite [~`(E `|` N)] (_:_ = ~`N `\` E); by rewrite // setDE setCU setIC.
have /choice [E_ /all_and3 [mE mEn Une]] : forall n, exists E, [/\ measurable E,
  (mu E < n.+1%:R^-1%:E)%E & {uniform ~`E, (f_ : (T->X)^nat) @ \oo --> f}]
  by move=>n; exact: (Cf n.+1%:R^-1).
exists f_. exists (\bigcap_n (E_ n)); split. exact: bigcap_measurable.
  apply: measure0P_invn=>//n.
  apply: (le_lt_trans (le_measure mu _ _ (bigcap_inf _)) (mEn n));
    rewrite ?in_setE //. exact: bigcap_measurableType.
apply: subsetCl. rewrite setC_bigcap=> z [i _ nEi]/=.
rewrite -in_setE -sub1set in nEi.
have: {uniform [set z], (f_ : (T->X)^nat) @ \oo --> f}
  by apply: (uniform_subset_cvg _ nEi).
by rewrite uniform_set1.
Qed.

Lemma bmeas_almost_uniformP_invn (f : T -> X) : bochner_measurable f <->
exists (f_ : {sfun T>->X}^nat), forall n, exists E, [/\ measurable E,
(mu E < n.+1%:R^-1%:E)%E & {uniform (~`E), (f_ : (T->X)^nat) @ \oo --> f}].
Proof.
split=>[/bmeas_almost_uniformP [f_ Uf]|[f_ Ufn]].
  exists f_=> n; exact: (Uf n.+1%:R^-1).
apply/bmeas_almost_uniformP; exists f_ => eps e0.
have [Ee [mEe mEee UEe]] := Ufn (truncn eps^-1); exists Ee; split=>//.
apply: (lt_trans mEee). rewrite lte_fin invf_plt ?posrE//; exact: truncnS_gt.
Qed.

Lemma bmeas_cvg (f : (T -> X)^nat) (g : T -> X)
(mmf : forall n:nat, bochner_measurable (f n)) (fg : forall x, f ^~ x  @\oo--> g x) :
bochner_measurable g.
Proof.
have /choice [f_ /choice [E0_ /all_and2 [decE0 mE0_]]] : forall n,
  exists (fn_ : {sfun T>->X}^nat), exists En_ : (set T) ^nat,
  {homo En_ : n m / (n <= m)%N >-> (m<=n)%O} /\ forall k : nat,
  [/\ d.-measurable (En_ k),  (mu (En_ k) < (k.+2%:R^-1 * 2^-n.+1)%:E)%E &
  {uniform ~`En_ k, (fn_ : (T->X)^nat) @\oo --> f n}].
  move=>n; have /bmeas_almost_uniformP[fn_ /almost_uniform_cvgTP sfnf] := mmf n;
  exists fn_. under eq_exists do under eq_forall do rewrite -setTD.
  apply/almost_uniform_cvg_nnincseqP=>//. apply/cvgr0Pnorm_lt=> eps e0; near=>k.
  rewrite (normr_idP _) ?invr_ge0//; apply: (@lt_trans _ _ k.+2%:R^-1).
    rewrite ltr_pdivrMr // ltr_pMr // exprn_egt1 // [1] (_:_ = (1:nat)%:R)
      ?ltr_nat //. apply: (@lt_trans _ _ k.+1%:R^-1).
    rewrite invf_plt ?posrE// -[X in X^-1]div1r invf_div divr1 ltr_nat//.
  near:k; apply: (near_infty_natSinv_lt (PosNum e0)).
pose E_ k := \bigcup_n E0_ n k.
have [dE /all_and3 [mE mEk UEk]] : {homo E_ : n m / (n<=m)%N >-> (m<=n)%O} /\
forall k, [/\ measurable (E_ k), (mu (E_ k) < k.+1%:R^-1%:E)%E & ~`E_ k !=set0
-> forall n, (\forall m \near \oo,
  has_sup [set `|f_ n m x - f n x| | x in ~`E_ k]) /\
  sup [set `|f_ n m x - f n x| | x in ~`E_ k] @[m --> \oo] --> 0].
  split=>[n m nm |k]. by rewrite subsetEset; apply: subset_bigcup => i _;
    rewrite -subsetEset; exact: (decE0 i).
  have /all_and3 [mE0 mE0nk UE0]: forall n, [/\ forall k, measurable (E0_ n k),
  forall k, (mu (E0_ n k) < (k.+2%:R^-1 / 2^+n.+1)%:E)%E & forall k, {uniform
    ~`E0_ n k, (f_ n : (T->X)^nat) @\oo --> f n}]. move=>n; exact: all_and3.
  split. exact: bigcupT_measurable.
    have k20: (0:R) <= k.+2%:R^-1 by rewrite invr_ge0.
    have leE0k: forall n, xpredT n ->
      (mu (E0_ n k) <= (k.+2%:R^-1 / 2^+n.+1)%:E)%E
      by move=> n _; exact: (ltW (mE0nk n k)).
    apply: (le_lt_trans (le_mu_bigcup _ _ _))=>//. exact: bigcupT_measurable.
    apply: (le_lt_trans (lee_nneseries _ leE0k))=> [i _ _|]. exact: measure_ge0.
    under eq_eseriesr do rewrite -natrX.
    apply (le_lt_trans (epsilon_trick0 xpredT k20)).
    by rewrite lte_fin invf_plt ?posrE// invrK ltr_nat.
  move=> nEk0 n. have EkE0 : ~` E_ k `<=` ~` E0_ n k by apply: subsetC;
    exact: bigcup_sup. apply (uniform_cvg_sup0 nEk0).
    apply: (uniform_subset_cvg _ EkE0). exact: (UE0 n k).
have /choice [M PM] : forall t, exists mt, forall x,
  (~` E_ t.1) x -> `|f_ t.2 mt x - f t.2 x| < t.2.+1%:R^-1. move=> [k n].
  have [->| /set0P nEk0] := eqVneq (~`E_ k) set0. by exists 0.
  have invn0 : (0:R) < n.+1%:R^-1 by rewrite invr_gt0.
  have [[m1 _ hsup] /cvgr0Pnorm_lt/(_ _ invn0)
    [m2 _  sup0]] := UEk k nEk0 n. exists (maxn m1 m2)=>x nEkx.
  have hsupm := hsup _ (leq_maxl m1 m2);
  have := sup0 _ (leq_maxr m1 m2). rewrite (normr_idP _).
    apply: sup_ge0=> y /= [z _ <-]; exact: normr_ge0.
  move=> /(gt_sup hsupm) supn. by apply: supn=>/=; exists x.
exists (fun n => f_ n (M (n, n))); exists (\bigcap_k (E_ k)).
split. exact: bigcap_measurableType. apply/measure0P_invn=>n.
  apply: (le_lt_trans (le_measure mu _ _ (bigcap_inf _)) (mEk n));
    rewrite ?in_setE //. exact: bigcap_measurableType.
apply: subsetCl. rewrite setC_bigcap => x [i _ nEi] /=.
apply/cvgrPdistC_lt=> eps e0. have e20: 0 < eps/2 by rewrite ltr_pdivlMr ?mul0r.
have /=fnge2 := cvgr_distC_lt (f ^~ x) (g x) (fg x) _ e20.
have /=n2e2 := near_infty_natSinv_lt (PosNum e20). near=>n.
rewrite (splitr eps). apply: (le_lt_trans (ler_distD (f n x) _ _) (ltrD _ _)).
  have /(dE i n) : (i<=n)%N by near:n; exact: nbhs_infty_ge.
  rewrite subsetEset => /subsetC /(_ x nEi) dEin.
  apply: (lt_trans (PM (n,n) x dEin))=>/=. by near:n. by near:n; apply: fnge2.
Unshelve. all: end_near. Qed.

Lemma bmeas_cvg_ae (f : (T -> X)^nat) (g : T -> X)
(mmf : forall n, bochner_measurable (f n)) :
  (\forall x \ae mu, f ^~ x  @\oo--> g x) -> bochner_measurable g.
Proof.
move=> [A [mA mA0 /subsetCl nAcv]].
pose f_ n := patch (f n) A g.
have : forall x, f_ ^~ x  @\oo--> g x.
move=> x; case: (boolP (x \in A)); rewrite/f_/patch.
    rewrite -{1}(eqb_id (x \in A))=>/eqP xA. under eq_cvg do rewrite xA.
    exact: cvg_cst.
  move=> xnA; rewrite [x \in A] (_:_ = false). exact: negbTE.
  rewrite notin_setE in xnA. by move: xnA => /nAcv.
apply: bmeas_cvg => n. have [fn_ [B [mB mB0 /subsetCl nBcv]]] := mmf n.
exists fn_; exists (A`|`B); split. exact: measurableU. exact: null_set_setU.
apply: subsetCl; rewrite setCU /f_ => x [nAx nBx] /=.
rewrite [X in _ --> X] (_:_ = f n x). rewrite /patch ifF //.
  by apply: negbTE; rewrite notin_setE.
exact: nBcv.
Qed.

(* TODO : Move to norm_lemmas *)
Lemma hahn_banach_on_seq x : exists xs : {linear_continuous X -> R}, xs x = `|x|
/\ forall y, `|xs y| <= `|y|.
Proof.
About hahn_banach_extension_normed.
set P := fun z => `[<exists k, z = k*:x>].
have := (@hahn_banach_extension_normed _ _ P _ _).
Admitted.

Lemma ess_sep_lim_count  (f : T -> X) : (exists A, [/\ measurable A, mu A = 0,
  measurable_fun (~`A) f & separable_set (image (~`A) f)]) -> forall eps,
  0<eps -> exists g: T->X, [/\ measurable_fun [set:T] g,
  countable (range g) & \forall t \ae mu, `|f t - g t| < eps].
Proof.
move=> [A [mA mA0 mAf /[dup] nsfA /norm_separableP
  [D [/pcard_surjP [x_ cx] ifx dfx]]]] eps e0.
have /choice [xs_ /all_and2 [xsx xsb]] : forall n,
  exists xs : {linear_continuous X -> R}, xs (x_ n) = `|x_ n|
    /\ forall y, `|xs y| <= `|y| by move=>n; exact:hahn_banach_on_seq.
pose g_ n t := `|f t - x_ n|. pose E_ n := (~`A) `&` [set t | g_ n t < eps].
have mE : forall n, measurable (E_ n) by move=>n;
  apply: measurable_fun_dist=>//; exact: measurableC.
exists (x_ \o (fun t => xget 0 [set n | seqDU E_ n t])); split.
rewrite -(setvU (\bigcup_n E_ n)). apply/measurable_funU.
        apply: measurableC; exact: bigcupT_measurable.
      exact: bigcupT_measurable. split.
      apply: (eq_measurable_fun (cst (x_ 0)))=>// x.
      rewrite in_setE setC_bigcup /bigcap=> /= nEx.
      rewrite xgetPN /seqDU=>//= n; rewrite not_andE; left; exact: nEx.
    rewrite seqDU_bigcup_eq; apply/measurable_fun_bigcup=>// [|i].
      exact: seqDU_measurable. apply: (eq_measurable_fun (cst (x_ i)))=>// x.
    rewrite in_setE [X in X -> _] (_:_ = [set n | seqDU E_ n x] i) // => Eni /=;
    rewrite (xget_unique 0 Eni) //= => m Enm.
    have /trivIsetP/(_ m i I I) /= /contra_not trvE := (trivIset_seqDU E_).
    by apply/eqP/negPn/negP; apply: trvE; apply/eqP/set0P; exists x.
  rewrite -(image_comp _ x_).
  apply: (sub_countable (subset_card_le (image_subset x_ (subsetT _))));
  exact: card_image_le.
exists (~`\bigcup_n E_ n); split. apply: measurableC; exact: bigcupT_measurable.
  apply/eqP; rewrite eq_le; apply/andP; split=>//. rewrite -mA0.
  apply: le_measure; rewrite ?in_setE //.
    apply: measurableC; exact: bigcupT_measurable.
  apply: subsetCl=> x nAx. rewrite surjE in cx. have [z [/cx [n _ <-]]]:=
    dfx (f x) eps e0 (imageP f nAx). rewrite -ball_normE => fxnxe.
  by exists n.
rewrite setCS seqDU_bigcup_eq => x [n _ ] /=.
rewrite [X in X -> _] (_:_ = [set n0 | seqDU E_ n0 x] n) // => Enx /=.
rewrite (xget_unique 0 Enx) //=. move=> m Emx.
  have /trivIsetP/(_ m n I I) /= /contra_not trvE := (trivIset_seqDU E_).
  by apply/eqP/negPn/negP; apply: trvE; apply/eqP/set0P; exists x.
by have [_ ] := subset_seqDU Enx.
Qed.

Lemma lim_count_bmeas (f : T -> X) : (forall eps, 0<eps ->
exists g: T->X, [/\ measurable_fun [set:T] g, countable (range g) &
\forall t \ae mu, `|f t - g t| < eps]) -> bochner_measurable f.
Proof.
move=> CC.
have /choice [g_ /all_and3 [mG Crg /choice [E_ /all_and3 [mE mE0 gfE]]]] :
forall n, exists g : T -> X, [/\ measurable_fun [set:T] g, countable (range g) &
  (\forall t \ae mu, `|f t - g t| < n.+1%:R^-1)]. by move=> n; apply: CC.
apply: (@bmeas_cvg_ae g_ f) => [n|].
  apply: countim_bmeas=>// z; rewrite -[X in measurable X](setTI).
  apply: (mG n)=>//; exact : measurable1.
exists (\bigcup_n E_ n); split. exact: bigcupT_measurable.
  apply/negligibleP. exact: bigcupT_measurable. apply: negligible_bigcup=>k.
  apply/negligibleP=>//; exact: mE0.
apply:subsetCl; rewrite setC_bigcup/bigcap=> x /= nE.
apply/cvgrPdistC_lt => /= eps e0. exists (truncn eps^-1).+1=>// n /= en.
have /subsetCl /(_ x) /(_ (nE n I))/= fgn := gfE n.
rewrite distrC; apply (lt_trans fgn).
have ne : (n.+1%:R^-1 : R) < (truncn eps^-1).+1%:R^-1 by
rewrite invf_plt ?posrE // invrK ltr_nat. apply: (lt_trans ne).
rewrite invf_plt ?posrE //; exact: truncnS_gt.
Qed.

(* Mix of lemma 11.37 in Infinite Dimensional Analysis : a Hitchhiker's guide
  and thm2 (Petti's measurability theorem) in Vector Measures (math surveys)*)
Lemma bmeas_meas_ess_sepP (f : T -> X) : bochner_measurable f <-> exists A,
  [/\ measurable A, mu A = 0,  measurable_fun (~`A) f
  & separable_set (image (~`A) f)].
Proof.
split=>[/bmeas_almost_uniformP_invn [f_ /choice[E_ /all_and3 [mE mEn UEn]]]|
  /ess_sep_lim_count/lim_count_bmeas //].
exists (\bigcap_n E_ n); split. exact: bigcap_measurableType.
    apply: measure0P_invn=>n. apply: (le_lt_trans
      (le_measure mu _ _ (bigcap_inf _)) (mEn n)); rewrite ?in_setE //.
    exact: bigcap_measurableType.
  apply: (@measurable_fun_cv _ _ _ _ _ f_). move=> m.
    exact: (measurable_funS measurableT). rewrite setC_bigcap=> x [i _ nEix].
  have nEin0 : ~`E_ i !=set0 by exists x.
  apply/cvgrPdist_lt=> eps e0.
  have /(uniform_cvg_has_sup0 nEin0) /(_ eps e0) [n0 _ nhs] := UEn i.
  exists n0=>// n /nhs [hsn sne]. apply: (gt_sup hsn sne _).
  by rewrite distrC; exists x.
rewrite setC_bigcap image_bigcup. apply: bigcup_separable=> n _.
apply: totally_bounded_separable => eps e0.
have [->|/set0P] := eqVneq (~` E_ n) set0.
  by exists set0; rewrite image_set0; split.
have e20 : 0 < eps/2 by rewrite ltr_pdivlMr // mul0r.
have C := uniform_to_norm _ e20 (UEn n) => /C [n0 _ /(_ n0 (lexx n0)) f0fe].
have /choice [G PG] : forall x:X, exists y, image (~` E_ n) (f_ n0) x ->
  image (~` E_ n) f y /\ `|x - y| < eps/2. move=> x.
  case: (boolP (x \in image (~` E_ n) (f_ n0))); rewrite ?in_setE ?notin_setE.
  move=> [z Enz <-]. exists (f z)=> _; split=>//. exact: f0fe.
  by move=> nrfn; exists 0 => /nrfn.
exists (image (image (~`E_ n) (f_ n0)) G);
  split=>[|x [y /(PG y) [ifGy _ <-]] // | x [t Ent <-]]. apply: finite_image;
    exact: (sub_finite_set (image_subset (f_ n0) (subsetT _))).
have [|] := (PG (f_ n0 t) _) => // ifG fn0G. exists (G (f_ n0 t)).
  by exists (f_ n0 t).
rewrite -ball_normE /= distrC; apply: (le_lt_trans (ler_distD (f_ n0 t) _ _)).
rewrite {1}distrC (splitr eps); apply: ltrD=>//; exact: f0fe.
Qed.

(* Corollary 3 of Vector Measures *)
Lemma bmeas_lim_countmeasP (f : T -> X) :  bochner_measurable f <->
forall eps, 0<eps -> exists g: T->X, [/\ measurable_fun [set:T] g,
countable (range g) & \forall t \ae mu, `|f t - g t| < eps].
Proof. by split=>[/bmeas_meas_ess_sepP/ess_sep_lim_count|/lim_count_bmeas]. Qed.

End bochner_measurable_function.


Reserved Notation "\int [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, i, D at level 60,
  format "'[' \int [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\int [ mu ]_ i F"
  (F at level 36, i at level 0,
    right associativity, format "'[' \int [ mu ]_ i '/  '  F ']'").

(** Definition of simple integrals: *)
Section simple_fun_raw_integral.
Context d (T : sigmaRingType d) (R : realType) (X : normedModType R)
  (mu : {finite_measure set T -> \bar R}) (f : T -> X).

Definition sbintegral := \sum_(x \in [set: X]) fine (mu (f @^-1` [set x])) *: x.

Lemma sbintegralET :
  sbintegral = \sum_(x \in [set: X]) fine (mu (f @^-1` [set x])) *: x.
Proof. by []. Qed.

End simple_fun_raw_integral.

Section sbintegral_lemmas.
Context d (T : sigmaRingType d) (R : realType) (X : normedModType R).
Variable mu : {finite_measure set T -> \bar R}.
Import MeasurableR.

Lemma sbintegralE (f : T -> X) :
  sbintegral mu f = \sum_(x \in range f) fine (mu (f @^-1` [set x])) *: x.
Proof.
rewrite (fsbig_widen (range f) setT)//= => x [_ Nfx] /=.
by rewrite preimage10// measure0 scale0r.
Qed.

Lemma sbintegral0 : sbintegral mu (cst 0%R) = (0:X).
Proof.
rewrite sbintegralE fsbig1// => r _; rewrite preimage_cst.
by case: ifPn => [/[!inE] <-|]; rewrite ?scaler0 // measure0 /= scale0r.
Qed.

Lemma sbintegral_indic_lmod (A : set T) (z : X) :
  sbintegral mu (indic_lmod A z) = fine (mu A) *: z.
Proof.
rewrite sbintegralE (fsbig_widen _ [set 0%R; z]) => //=.
  - exact: image_indic_lmod_sub.
  - by move=> t [[] -> /= /preimage10->]; rewrite measure0 scale0r.
have [->|/eqP] := eqVneq z 0;
rewrite fsbigU//=; first by move=> t [->]/=; rewrite scaler0.
rewrite !fsbig_set1 !scaler0 addr0//.
move=> x /= [-> _]; by rewrite scaler0.
rewrite !fsbig_set1 !preimage_indic_lmod /= => z0.
rewrite ifN ?notin_setE//= ifT ?in_setE //= scaler0 add0r
  ifT ?in_setE //= ifN ?notin_setE //=. exact: nesym.
Qed.

End sbintegral_lemmas.

Lemma eq_sbintegral d (T : sigmaRingType d) (R : realType) (X : normedModType R)
    (mu : {finite_measure set T -> \bar R}) (g f : T -> X) :
  f =1 g -> sbintegral mu f = sbintegral mu g.
Proof. by move=> /funext->. Qed.
Arguments eq_sbintegral {d T R X mu} g.

Section sbintegralrZ.
Context d (T : sigmaRingType d) (R : realType) (X : normedModType R).
Import MeasurableR.
Variables (m : {finite_measure set T -> \bar R}) (r : R) (f : {sfun T >-> X}).

(* Proof is a lot more complicated than it should have been *)
Lemma sbintegralrZ : sbintegral m (r \*: f) = r *: sbintegral m f.
Proof.
have [->|r0] := eqVneq r 0.
  by rewrite scale0r (eq_sbintegral (cst 0%R)) ?sbintegral0// => x /=;
  rewrite scale0r.
have eqscaler : forall x y : X, (r *: x = r *: y) = (x=y).
  move=> x y; rewrite propeqE; split=>[rxy|->//].
  by rewrite -[LHS]scale1r -[RHS]scale1r -(divff r0) mulrC -!scalerA rxy.
rewrite !sbintegralE scaler_sumr/= (reindex_fsbig ( *:%R r) (range f)) /=.
rewrite [X in set_bij _ X] (_:_ = image (range f) ( *:%R r)).
    rewrite image_comp; exact: eq_set.
  split=>// x y _ _ rxy. by rewrite -eqscaler.
have scale_preim : forall x, (r \*: f) @^-1` [set r *: x] = f @^-1` [set x].
  rewrite /preimage => x/=; apply: eq_set=> t; exact:eqscaler.
under eq_bigr do rewrite scale_preim scalerA mulrC -scalerA. congr (bigop.body).
case: finite_supportP => [/(sub_infinite_set (@subIsetl _ (range f) _)) infr //
  | Y Yrf rfnY0 Yrn0]. apply/eqP/fset_eqP => x; rewrite in_finite_support.
  exact: (sub_finite_set ((@subIsetl _ (range f) _))).
rewrite [X in _`&`X] (_:_ = (fun i : X =>
  fine (m ((r \*: f) @^-1` [set r *: i])) *: (r *: i)) @^-1` [set~ 0]).
  rewrite/preimage; apply: eq_set=> z/=; rewrite scalerA mulrC -scalerA propeqE.
  apply: not_iff_compat. rewrite -{2}(scaler0 X r) -propeqE
    [[set t | r *: f t = r *: z]] (_:_ = [set t | f t = z]).
    apply:eq_set=>t; exact: eqscaler.
  apply: Logic.eq_sym; exact:eqscaler.
by rewrite -Yrn0 mem_setE.
Qed.

End sbintegralrZ.

Section sbintegralD.
Context d (T : measurableType d) (R : realType) (X : normedModType R).
Import MeasurableR.
Variables (m : {finite_measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f g : {sfun T >-> X}).
(* TODO *)
Lemma sbintegralD : sbintegral m (f \+ g)%R = sbintegral m f + sbintegral m g.
Proof.
rewrite !sbintegralE; set F := f @` _; set G := g @` _; set FG := _ @` _.
pose pf x := f @^-1` [set x]; pose pg y := g @^-1` [set y].
rewrite !fsbig_finite //=.
About fsbig_finite. About fsbig_supp. About fsbig_seq.
Abort.

End sbintegralD.