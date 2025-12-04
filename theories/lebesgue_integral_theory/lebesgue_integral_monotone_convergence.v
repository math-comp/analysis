(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference topology ereal tvs normedtype.
From mathcomp Require Import sequences real_interval function_spaces esum.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import simple_functions measurable_fun_approximation.
From mathcomp Require Import lebesgue_integral_definition.

(**md**************************************************************************)
(* # Monotone convergence theorem for the Lebesgue Integral                   *)
(*                                                                            *)
(* Monotone convergence and Fatou's lemmas for the Lebesgue integral.         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section nondecreasing_integral_limit.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (f : T -> \bar R)
          (g : {nnsfun T >-> R}^nat).
Hypothesis f0 : forall x, 0 <= f x.
Hypothesis mf : measurable_fun setT f.

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~x).
Hypothesis gf : forall x, EFin \o g^~ x @ \oo --> f x.
Local Open Scope ereal_scope.

Lemma nd_ge0_integral_lim : \int[mu]_x f x = limn (sintegral mu \o g).
Proof.
rewrite ge0_integralTE//.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: lime_le; first exact: is_cvg_sintegral.
  near=> n; apply: ereal_sup_ubound; exists (g n) => //= => x.
  have <- : limn (EFin \o g ^~ x) = f x by exact/cvg_lim/gf.
  have : EFin \o g ^~ x @ \oo --> ereal_sup (range (EFin \o g ^~ x)).
    by apply: ereal_nondecreasing_cvgn => p q pq /=; rewrite lee_fin; exact/nd_g.
  by move/cvg_lim => -> //; apply: ereal_sup_ubound; exists n.
have := leey (\int[mu]_x (f x)).
rewrite [in X in X -> _]le_eqVlt => /predU1P[|] mufoo; last first.
  have : \int[mu]_x (f x) \is a fin_num by rewrite ge0_fin_numE// integral_ge0.
  rewrite ge0_integralTE// => /ub_ereal_sup_adherent h.
  apply/lee_addgt0Pr => _/posnumP[e].
  have {h} [/= _ [G Gf <-]] := h _ [gt0 of e%:num].
  rewrite EFinN lteBlDr// => fGe.
  have : forall x, cvgn (g^~ x) -> (G x <= limn (g ^~ x))%R.
    move=> x cg; rewrite -lee_fin -(EFin_lim cg).
    by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _))// gxfx.
  move=> /(nd_sintegral_lim_lemma mu nd_g)/(leeD2r e%:num%:E).
  exact/le_trans/ltW.
suff : limn (sintegral mu \o g) = +oo.
  by move=> ->; rewrite -ge0_integralTE// mufoo.
apply/eqyP => r r0.
have [G [Gf rG]] : exists h : {nnsfun T >-> R},
    (forall x, (h x)%:E <= f x) /\ (r%:E <= sintegral mu h).
  have : r%:E < \int[mu]_x (f x).
    move: (mufoo) => /eqyP/(_ _ (addr_gt0 r0 r0)).
    by apply: lt_le_trans => //; rewrite lte_fin ltrDr.
  rewrite ge0_integralTE// => /ereal_sup_gt[x [/= G Gf Gx rx]].
  by exists G; split => //; rewrite (le_trans (ltW rx)) // Gx.
have : forall x, cvgn (g^~ x) -> (G x <= limn (g^~ x))%R.
  move=> x cg; rewrite -lee_fin -(EFin_lim cg).
  by have /cvg_lim gxfx := @gf x; rewrite (le_trans (Gf _)) // gxfx.
by move/(nd_sintegral_lim_lemma mu nd_g) => Gg; rewrite (le_trans rG).
Unshelve. all: by end_near. Qed.

End nondecreasing_integral_limit.

Section ge0_le_integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (f1 f2 : T -> \bar R).
Hypothesis f10 : forall x, D x -> 0 <= f1 x.
Hypothesis mf1 : measurable_fun D f1.
Hypothesis mf2 : measurable_fun D f2.

Import HBNNSimple.

Lemma ge0_le_integral : (forall x, D x -> f1 x <= f2 x) ->
  \int[mu]_(x in D) f1 x <= \int[mu]_(x in D) f2 x.
Proof.
move=> f12; rewrite !(integral_mkcond D).
set h1 := f1 \_ D; set h2 := f2 \_ D.
have h10 x : 0 <= h1 x by apply: erestrict_ge0.
have h20 x : 0 <= h2 x.
  by apply: erestrict_ge0 => // t /[dup] Dt /f12; apply: le_trans; exact: f10.
have mh1 : measurable_fun setT h1 by exact/(measurable_restrictT _ _).1.
have mh2 : measurable_fun setT h2 by exact/(measurable_restrictT _ _).1.
have h12 x : h1 x <= h2 x by apply: lee_restrict.
pose g1 := nnsfun_approx measurableT mh1.
rewrite (@nd_ge0_integral_lim _ _ _ _ _ g1)//; last 2 first.
  by move=> x m n mn; exact/lefP/nd_nnsfun_approx.
  by move=> x; exact: cvg_nnsfun_approx.
apply: lime_le.
  by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_nnsfun_approx.
near=> n; rewrite ge0_integralTE//; apply: ereal_sup_ubound => /=.
exists (g1 n) => // t; rewrite (le_trans _ (h12 _))//.
have := leey (h1 t); rewrite le_eqVlt => /predU1P[->|ftoo].
  by rewrite leey.
have h1tfin : h1 t \is a fin_num.
  by rewrite fin_numE gt_eqF/= ?lt_eqF// (lt_le_trans _ (h10 t)).
have /= := @cvg_nnsfun_approx _ _ _ _ measurableT _ mh1 (fun x _ => h10 x) t Logic.I.
rewrite -(fineK h1tfin) => /fine_cvgP[ft_near].
set u_ := (X in X --> _) => u_h1.
have <- : lim u_ = fine (h1 t) by exact/cvg_lim.
rewrite lee_fin; apply: nondecreasing_cvgn_le.
  by move=> // a b ab; rewrite /u_ /=; exact/lefP/nd_nnsfun_approx.
by apply/cvg_ex; eexists; exact: u_h1.
Unshelve. all: by end_near. Qed.

End ge0_le_integral.

Section monotone_convergence_theorem.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (D : set T) (mD : measurable D) (g' : (T -> \bar R)^nat).
Hypothesis mg' : forall n, measurable_fun D (g' n).
Hypothesis g'0 : forall n x, D x -> 0 <= g' n x.
Hypothesis nd_g' : forall x, D x -> nondecreasing_seq (g'^~ x).
Let f' := fun x => limn (g'^~ x).

Let g n := (g' n \_ D).

Let g0 n x : 0 <= g n x. Proof. exact/erestrict_ge0/g'0. Qed.

Let mg n : measurable_fun setT (g n).
Proof. exact/(measurable_restrictT _ _).1. Qed.

Let nd_g x : nondecreasing_seq (g^~ x).
Proof.
by move=> m n mn; rewrite /g/patch; case: ifP => // /set_mem /nd_g' ->.
Qed.

Let f := fun x => limn (g^~ x).

Let is_cvg_g t : cvgn (g^~ t).
Proof.
by move=> ?; apply: ereal_nondecreasing_is_cvgn => m n ?; exact/nd_g.
Qed.

Local Definition g2' n : (T -> R)^nat := approx setT (g n).
Local Definition g2 n : {nnsfun T >-> R}^nat := nnsfun_approx measurableT (mg n).

Local Definition max_g2' : (T -> R)^nat :=
  fun k t => (\big[maxr/0]_(i < k) (g2' i k) t)%R.
Local Definition max_g2 : {nnsfun T >-> R}^nat :=
  fun k => bigmax_nnsfun (g2^~ k) k.

Import HBNNSimple.

Let is_cvg_g2 n t : cvgn (EFin \o (g2 n ^~ t)).
Proof.
apply: ereal_nondecreasing_is_cvgn => a b ab.
by rewrite lee_fin 2!nnsfun_approxE; exact/lefP/nd_approx.
Qed.

Let nd_max_g2 : nondecreasing_seq (max_g2 : (T -> R)^nat).
Proof.
apply/nondecreasing_seqP => n; apply/lefP => x; rewrite 2!bigmax_nnsfunE.
rewrite (@le_trans _ _ (\big[maxr/0]_(i < n) g2 i n.+1 x)%R) //.
  apply: le_bigmax2 => i _; apply: (nondecreasing_seqP (g2 i ^~ x)).2 => a b ab.
   by rewrite !nnsfun_approxE; exact/lefP/nd_approx.
rewrite (bigmaxD1 ord_max)// le_max; apply/orP; right.
rewrite [leRHS](eq_bigl (fun i => nat_of_ord i < n)%N).
  by rewrite (big_ord_narrow (leqnSn n)).
move=> i /=; rewrite neq_lt; apply/orP/idP => [[//|]|]; last by left.
by move=> /(leq_trans (ltn_ord i)); rewrite ltnn.
Qed.

Let is_cvg_max_g2 t : cvgn (EFin \o max_g2 ^~ t).
Proof.
apply: ereal_nondecreasing_is_cvgn => m n mn; rewrite lee_fin.
exact/lefP/nd_max_g2.
Qed.

Let max_g2_g k x : ((max_g2 k x)%:E <= g k x)%O.
Proof.
rewrite bigmax_nnsfunE.
apply: (@le_trans _ _ (\big[maxe/0%:E]_(i < k) g k x)); last first.
  by apply/bigmax_leP; split => //; apply: g0D.
rewrite (big_morph _ (@EFin_max R) erefl) //.
apply: le_bigmax2 => i _; rewrite nnsfun_approxE /=.
by rewrite (le_trans (le_approx _ _ _)) => //; exact/nd_g/ltnW.
Qed.

Let lim_max_g2_f t : limn (EFin \o max_g2 ^~ t) <= f t.
Proof. by apply: lee_lim => //=; near=> n; exact/max_g2_g.
Unshelve. all: by end_near. Qed.

Let lim_g2_max_g2 t n : limn (EFin \o g2 n ^~ t) <= limn (EFin \o max_g2 ^~ t).
Proof.
apply: lee_lim => //.
near=> k; rewrite /= bigmax_nnsfunE lee_fin.
have nk : (n < k)%N by near: k; exists n.+1.
exact: (bigmax_sup (Ordinal nk)).
Unshelve. all: by end_near. Qed.

Let cvg_max_g2_f t : EFin \o max_g2 ^~ t @ \oo --> f t.
Proof.
have /cvg_ex[l g_l] := @is_cvg_max_g2 t.
suff : l == f t by move=> /eqP <-.
rewrite eq_le; apply/andP; split.
  by rewrite /f (le_trans _ (lim_max_g2_f _)) // (cvg_lim _ g_l).
have := leey l; rewrite [in X in X -> _]le_eqVlt => /predU1P[->|loo].
  by rewrite leey.
rewrite -(cvg_lim _ g_l) //= lime_le => //.
near=> n.
have := leey (g n t); rewrite le_eqVlt => /predU1P[|] fntoo.
  have h := @dvg_approx _ _ _ setT _ t Logic.I fntoo.
  have g2oo : limn (EFin \o g2 n ^~ t) = +oo.
    apply/cvg_lim => //; apply/cvgeryP.
    under [in X in X --> _]eq_fun do rewrite nnsfun_approxE.
    have : {homo (approx setT (g n))^~ t : n0 m / (n0 <= m)%N >-> (n0 <= m)%R}.
      exact/lef_at/nd_approx.
    by move/nondecreasing_dvgn_lt => /(_ h).
  have -> : limn (EFin \o max_g2 ^~ t) = +oo.
    by have := lim_g2_max_g2 t n; rewrite g2oo leye_eq => /eqP.
  by rewrite leey.
- have approx_g_g := @cvg_approx _ _ _ setT _ t (fun t _ => g0 n t) Logic.I fntoo.
  suff : limn (EFin \o g2 n ^~ t) = g n t.
    by move=> <-; exact: (le_trans _ (lim_g2_max_g2 t n)).
  have /cvg_lim <- // : EFin \o (approx setT (g n)) ^~ t @ \oo --> g n t.
    move/cvg_comp : approx_g_g; apply.
    by rewrite -(@fineK _ (g n t))// ge0_fin_numE// g0.
  rewrite (_ : _ \o _ = EFin \o approx setT (g n) ^~ t)// funeqE => m.
  by rewrite [in RHS]/= -nnsfun_approxE.
Unshelve. all: by end_near. Qed.

Lemma monotone_convergence :
  \int[mu]_(x in D) (f' x) = limn (fun n => \int[mu]_(x in D) (g' n x)).
Proof.
rewrite integral_mkcond.
under [in RHS]eq_fun do rewrite integral_mkcond -/(g _).
have -> : f' \_ D = f.
  apply/funext => x; rewrite /f /f' /g /patch /=; case: ifPn => //=.
  by rewrite lim_cst.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  have nd_int_g : nondecreasing_seq (fun n => \int[mu]_x g n x).
    move=> m n mn; apply: ge0_le_integral => //.
    by move=> *; exact: nd_g.
  have ub n : \int[mu]_x g n x <= \int[mu]_x f x.
    apply: ge0_le_integral => //.
    - apply: emeasurable_fun_cvg mg _ => x _.
      exact: ereal_nondecreasing_is_cvgn.
    - move=> x Dx; apply: lime_ge => //.
      near=> m; have nm : (n <= m)%N by near: m; exists n.
      exact/nd_g.
  by apply: lime_le => //; [exact:ereal_nondecreasing_is_cvgn|exact:nearW].
rewrite (@nd_ge0_integral_lim _ _ _ mu _ max_g2) //; last 2 first.
  - move=> t; apply: lime_ge => //.
    by apply: nearW => n; exact: g0.
  - by move=> t m n mn; exact/lefP/nd_max_g2.
apply: lee_lim.
- by apply: is_cvg_sintegral => // t m n mn; exact/lefP/nd_max_g2.
- apply: ereal_nondecreasing_is_cvgn => // n m nm; apply: ge0_le_integral => //.
  by move=> *; exact/nd_g.
- apply: nearW => n; rewrite ge0_integralTE//.
  by apply: ereal_sup_ubound; exists (max_g2 n) => // t; exact: max_g2_g.
Unshelve. all: by end_near. Qed.

Lemma cvg_monotone_convergence :
  \int[mu]_(x in D) g' n x @[n \oo] --> \int[mu]_(x in D) f' x.
Proof.
rewrite monotone_convergence; apply: ereal_nondecreasing_is_cvgn => m n mn.
by apply: ge0_le_integral => // t Dt; [exact: g'0|exact: nd_g'].
Qed.

End monotone_convergence_theorem.

Section fatou.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Variable f : (T -> \bar R)^nat.
Hypothesis mf : forall n, measurable_fun D (f n).
Hypothesis f0 : forall n x, D x -> 0 <= f n x.

Lemma fatou : \int[mu]_(x in D) limn_einf (f^~ x) <=
              limn_einf (fun n => \int[mu]_(x in D) f n x).
Proof.
pose g n := fun x => einfs (f ^~ x) n.
have mg := measurable_fun_einfs mf.
have g0 n x : D x -> 0 <= g n x.
  by move=> Dx; apply: le_ereal_inf_tmp => _ [m /= nm <-]; exact: f0.
under eq_integral do rewrite limn_einf_lim.
rewrite limn_einf_lim monotone_convergence //; last first.
  move=> x Dx m n mn /=; apply: ereal_inf_le_tmp => _ /= [p /= np <-].
  by exists p => //=; rewrite (leq_trans mn).
apply: lee_lim.
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: ge0_le_integral => //; [exact: g0| exact: mg| exact: mg|].
  move=> x Dx; apply: ereal_inf_le_tmp => _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
  apply: ereal_inf_le_tmp => // _ [n /= bn <-].
  by exists n => //=; rewrite (leq_trans ab).
- apply: nearW => m.
  have : forall n p, (p >= n)%N ->
      \int[mu]_(x in D) g n x <= einfs (fun k => \int[mu]_(x in D) f k x) n.
    move=> n p np; apply: le_ereal_inf_tmp => /= _ [k /= nk <-].
    apply: ge0_le_integral => //; [exact: g0|exact: mg|].
    by move=> x Dx; apply: ereal_inf_lbound; exists k.
  exact.
Qed.

End fatou.
