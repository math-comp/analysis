(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality reals fsbigop.
From mathcomp Require Import interval_inference ereal topology tvs normedtype.
From mathcomp Require Import sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun function_spaces.
From mathcomp Require Import simple_functions.

(**md**************************************************************************)
(* # Definition of the Lebesgue integral                                      *)
(*                                                                            *)
(* This file contains the definition of the Lebesgue integral. It starts      *)
(* with the integral of simple functions, proves their basic properties       *)
(* (linearity, non-decreasingness, etc.), and then defines the integral of    *)
(* measurable functions.                                                      *)
(*                                                                            *)
(* Main notations:                                                            *)
(* | Coq notation          |  | Meaning                         |             *)
(* |----------------------:|--|:--------------------------------              *)
(* | \int[mu]_(x in D) f x |==| $\int_D f(x)\mathbf{d}\mu(x)$                 *)
(* | \int[mu]_x f x        |==| $\int f(x)\mathbf{d}\mu(x)$                   *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*         sintegral mu f == integral of the function f with the measure mu   *)
(*  \int[mu]_(x in D) f x == integral of the measurable function f over the   *)
(*                           domain D with measure mu                         *)
(*         \int[mu]_x f x := \int[mu]_(x in setT) f x                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "\int [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, mu at level 10, i, D at level 50,
  format "'[' \int [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\int [ mu ]_ i F"
  (at level 36, F at level 36, mu at level 10, i at level 0,
    right associativity, format "'[' \int [ mu ]_ i '/  '  F ']'").

(** Definition of simple integrals: *)
Section simple_fun_raw_integral.
Local Open Scope ereal_scope.
Variables (T : Type) (R : numDomainType) (mu : set T -> \bar R) (f : T -> R).

Definition sintegral := \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).

Lemma sintegralET :
  sintegral = \sum_(x \in [set: R]) x%:E * mu (f @^-1` [set x]).
Proof. by []. Qed.

End simple_fun_raw_integral.

#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: measure_ge0] : core.

Section sintegral_lemmas.
Context d (T : sigmaRingType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Lemma sintegralE f :
  sintegral mu f = \sum_(x \in range f) x%:E * mu (f @^-1` [set x]).
Proof.
rewrite (fsbig_widen (range f) setT)//= => x [_ Nfx] /=.
by rewrite preimage10// measure0 mule0.
Qed.

Lemma sintegral0 : sintegral mu (cst 0%R) = 0.
Proof.
rewrite sintegralE fsbig1// => r _; rewrite preimage_cst.
by case: ifPn => [/[!inE] <-|]; rewrite ?mul0e// measure0 mule0.
Qed.

Import HBNNSimple.

Lemma sintegral_ge0 (f : {nnsfun T >-> R}) : 0 <= sintegral mu f.
Proof. by rewrite sintegralE fsume_ge0// => r _; exact: nnsfun_mulemu_ge0. Qed.

Lemma sintegral_indic (A : set T) : sintegral mu \1_A = mu A.
Proof.
rewrite sintegralE (fsbig_widen _ [set 0%R; 1%R]) => //=; last 2 first.
  - exact: image_indic_sub.
  - by move=> t [[] -> /= /preimage10->]; rewrite measure0 mule0.
have N01 : (0 <> 1:> R)%R by apply/eqP; rewrite eq_sym oner_eq0.
rewrite fsbigU//=; last by move=> t [->].
rewrite !fsbig_set1 mul0e add0e mul1e.
by rewrite preimage_indic ifT ?inE// ifN ?notin_setE.
Qed.

(* NB: not used *)
Lemma sintegralEnnsfun (f : {nnsfun T >-> R}) : sintegral mu f =
  \sum_(x \in [set r | r > 0]%R) x%:E * mu (f @^-1` [set x]).
Proof.
rewrite (fsbig_widen _ setT) ?sintegralET//.
move=> x [_ /=]; case: ltgtP => //= [xlt0 _|<-]; last by rewrite mul0e.
rewrite preimage10 ?measure0 ?mule0//= => -[t _ xE].
by apply/negP: xlt0; rewrite -leNgt -xE.
Qed.

End sintegral_lemmas.

Lemma eq_sintegral d (T : sigmaRingType d) (R : numDomainType)
    (mu : set T -> \bar R) g f :
  f =1 g -> sintegral mu f = sintegral mu g.
Proof. by move=> /funext->. Qed.
Arguments eq_sintegral {d T R mu} g.

Section sintegralrM.
Local Open Scope ereal_scope.
Context d (T : sigmaRingType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (r : R) (f : {nnsfun T >-> R}).

Import HBNNSimple.

Lemma sintegralrM : sintegral m (cst r \* f)%R = r%:E * sintegral m f.
Proof.
have [->|r0] := eqVneq r 0%R.
  by rewrite mul0e (eq_sintegral (cst 0%R)) ?sintegral0// => x/=; rewrite mul0r.
rewrite !sintegralET ge0_mule_fsumr; last exact: nnsfun_mulemu_ge0.
rewrite (reindex_fsbigT ( *%R r))/=; last first.
  by exists ( *%R r^-1); [exact: mulKf|exact: mulVKf].
by apply: eq_fsbigr => x; rewrite preimage_cstM// [(_ / r)%R]mulrC mulKf// muleA.
Qed.

End sintegralrM.

Section sintegralD.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}).
Variables (D : set T) (mD : measurable D) (f g : {nnsfun T >-> R}).

Import HBNNSimple.

Lemma sintegralD : sintegral m (f \+ g)%R = sintegral m f + sintegral m g.
Proof.
rewrite !sintegralE; set F := f @` _; set G := g @` _; set FG := _ @` _.
pose pf x := f @^-1` [set x]; pose pg y := g @^-1` [set y].
transitivity (\sum_(z \in FG) z%:E * \sum_(a \in F) m (pf a `&` pg (z - a)%R)).
  apply: eq_fsbigr => z _; rewrite preimage_add -fsbig_setU// measure_fsbig//.
    by move=> x Fx; exact: measurableI.
  exact/trivIset_setIr/trivIset_preimage1.
under eq_fsbigr do rewrite ge0_mule_fsumr//; rewrite exchange_fsbig//=.
transitivity (\sum_(x \in F) \sum_(y \in G) (x + y)%:E * m (pf x `&` pg y)).
  apply: eq_fsbigr => x _; rewrite /pf /pg (fsbig_widen G setT)//=; last first.
    by move=> y [_ /= /preimage10->]; rewrite setI0 measure0 mule0.
  rewrite (fsbig_widen FG setT)//=; last first.
    move=> z [_ /= FGz]; rewrite [X in m X](_ : _ = set0) ?measure0 ?mule0//.
    rewrite -subset0 => //= {x}i /= [<-] /(canLR (@addrNK _ _)).
    by apply: contra_not FGz => <-; exists i; rewrite //= addrC.
  rewrite (reindex_fsbigT (+%R x))//=.
  by apply: eq_fsbigr => y; rewrite addrC addrK.
transitivity (\sum_(x \in F) \sum_(y \in G) x%:E * m (pf x `&` pg y) +
              \sum_(x \in F) \sum_(y \in G) y%:E * m (pf x `&` pg y)).
  do 2![rewrite -fsbig_split//; apply: eq_fsbigr => _ /set_mem [? _ <-]].
  by rewrite EFinD ge0_muleDl// ?lee_fin.
congr +%E; last rewrite exchange_fsbig//; apply: eq_fsbigr => x _.
  by rewrite -ge0_mule_fsumr// additive_nnsfunr nnsfun_cover setIT.
by rewrite -ge0_mule_fsumr// additive_nnsfunl nnsfun_cover setTI.
Qed.

End sintegralD.

Section le_sintegral.
Context d (T : measurableType d) (R : realType) (m : {measure set T -> \bar R}).
Variables f g : {nnsfun T >-> R}.

Import HBNNSimple.

Hypothesis fg : forall x, f x <= g x.

Let fgnn : @isNonNegFun T R (g \- f).
Proof. by split=> x; rewrite subr_ge0 fg. Qed.
#[local] HB.instance Definition _ := fgnn.

Lemma le_sintegral : (sintegral m f <= sintegral m g)%E.
Proof.
have gfgf : g =1 f \+ (g \- f) by move=> x /=; rewrite addrC subrK.
by rewrite (eq_sintegral _ _ gfgf) sintegralD// leeDl // sintegral_ge0.
Qed.

End le_sintegral.

Section is_cvg_sintegral.
Import HBNNSimple.

Lemma is_cvg_sintegral d (T : measurableType d) (R : realType)
  (m : {measure set T -> \bar R}) (f : {nnsfun T >-> R}^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) -> cvgn (sintegral m \o f).
Proof.
move=> nd_f; apply/cvg_ex; eexists; apply/ereal_nondecreasing_cvgn => a b ab.
by apply: le_sintegral => // => x; exact/nd_f.
Qed.

End is_cvg_sintegral.

Section sintegral_nondecreasing_limit_lemma.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat) (f : {nnsfun T >-> R}).

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, cvgn (g^~ x) -> f x <= limn (g^~ x).

Let fleg c : (set T)^nat := fun n => [set x | c * f x <= g n x].

Let nd_fleg c : {homo fleg c : n m / (n <= m)%N >-> (n <= m)%O}.
Proof.
move=> n m nm; rewrite /fleg; apply/subsetPset => x /= cfg.
by move: cfg => /le_trans; apply; exact: nd_g.
Qed.

Let mfleg c n : measurable (fleg c n).
Proof.
rewrite /fleg [X in _ X](_ : _ = \big[setU/set0]_(y <- fset_set (range f))
    \big[setU/set0]_(x <- fset_set (range (g n)) | c * y <= x)
      (f @^-1` [set y] `&` (g n @^-1` [set x]))).
  apply: bigsetU_measurable => r _; apply: bigsetU_measurable => r' crr'.
  exact/measurableI/measurable_sfunP.
rewrite predeqE => t; split => [/= cfgn|].
- rewrite -bigcup_seq; exists (f t); first by rewrite /= in_fset_set//= mem_set.
  rewrite -bigcup_seq_cond; exists (g n t) => //=.
  by rewrite in_fset_set// mem_set.
- rewrite bigsetU_fset_set// => -[r [x _ fxr]].
  rewrite bigsetU_fset_set_cond// => -[r' [[x' _ gnx'r'] crr']].
  by rewrite /preimage/= => -[-> ->].
Qed.

Let g1 c n : {nnsfun T >-> R} := proj_nnsfun f (mfleg c n).

Let le_ffleg c : {homo (fun p x => g1 c p x): m n / (m <= n)%N >-> (m <= n)%O}.
Proof.
move=> m n mn; apply/asboolP => t; rewrite /g1/= ler_pM// 2!mindicE/= ler_nat.
have [|//] := boolP (t \in fleg c m); rewrite inE => cnt.
by have := nd_fleg c mn => /subsetPset/(_ _ cnt) cmt; rewrite mem_set.
Qed.

Let bigcup_fleg c : c < 1 -> \bigcup_n fleg c n = setT.
Proof.
move=> c1; rewrite predeqE => x; split=> // _.
have := @fun_ge0 _ _ f x; rewrite le_eqVlt => /predU1P[|] gx0.
  by exists O => //; rewrite /fleg /=; rewrite -gx0 mulr0 fun_ge0.
have [cf|df] := pselect (cvgn (g^~ x)).
  have cfg : limn (g^~ x) > c * f x.
    by rewrite (lt_le_trans _ (gf cf)) // gtr_pMl.
  suff [n cfgn] : exists n, g n x >= c * f x by exists n.
  move/(@lt_lim _ _ _ (nd_g x) cf) : cfg => [n _ nf].
  by exists n; apply: nf => /=.
have /cvgryPge/(_ (c * f x))[n _ ncfgn]:= nondecreasing_dvgn_lt (nd_g x) df.
by exists n => //; rewrite /fleg /=; apply: ncfgn => /=.
Qed.

Local Open Scope ereal_scope.

Lemma nd_sintegral_lim_lemma : sintegral mu f <= limn (sintegral mu \o g).
Proof.
suff ? : forall c, (0 < c < 1)%R ->
    c%:E * sintegral mu f <= limn (sintegral mu \o g).
  by apply/lee_mul01Pr => //; exact: sintegral_ge0.
move=> c /andP[c0 c1].
have cg1g n : c%:E * sintegral mu (g1 c n) <= sintegral mu (g n).
  rewrite -sintegralrM (_ : (_ \* _)%R = scale_nnsfun (g1 c n) (ltW c0)) //.
  apply: le_sintegral => // t.
  suff : forall m x, (c * g1 c m x <= g m x)%R by move=> /(_ n t).
  move=> m x; rewrite /g1 /proj_nnsfun/= mindicE.
  by have [|] := boolP (_ \in _); [rewrite inE mulr1|rewrite 2!mulr0 fun_ge0].
suff {cg1g}<- : limn (fun n => sintegral mu (g1 c n)) = sintegral mu f.
  have is_cvg_g1 : cvgn (fun n => sintegral mu (g1 c n)).
    by apply: is_cvg_sintegral => //= x m n /(le_ffleg c)/lefP/(_ x).
  rewrite -limeMl // lee_lim//; first exact: is_cvgeZl.
  - by apply: is_cvg_sintegral => // m n mn; apply/lefP => t; apply: nd_g.
  - exact/nearW/cg1g.
suff : sintegral mu (g1 c n) @[n \oo] --> sintegral mu f by apply/cvg_lim.
rewrite [X in X @ \oo --> _](_ : _ = fun n => \sum_(x <- fset_set (range f))
    x%:E * mu (f @^-1` [set x] `&` fleg c n)); last first.
  rewrite funeqE => n; rewrite sintegralE.
  transitivity (\sum_(x \in range f) x%:E * mu (g1 c n @^-1` [set x])).
    apply: eq_fbigl => r.
    do 2 (rewrite in_finite_support; last exact/finite_setIl).
    apply/idP/idP.
      rewrite in_setI => /andP[]; rewrite inE/= => -[x _]; rewrite mindicE.
      have [_|xcn] := boolP (_ \in _).
        by rewrite mulr1 => <-; rewrite !inE/= => ?; split => //; exists x.
      by rewrite mulr0 => /esym ->; rewrite !inE/= mul0e.
    rewrite in_setI => /andP[]; rewrite inE => -[x _ <-].
    rewrite !inE/= => h; split=> //; move: h; rewrite mindicE => /eqP.
    rewrite mule_eq0 negb_or => /andP[_]; set S := (X in mu X) => mS0.
    suff : S !=set0 by move=> [y yx]; exists y.
    by apply/set0P; apply: contra mS0 => /eqP ->; rewrite measure0.
  rewrite fsbig_finite//=; apply: eq_fbigr => r.
  rewrite in_fset_set// inE => -[t _ ftr _].
  have [->|r0] := eqVneq r 0%R; first by rewrite 2!mul0e.
  congr (_ * mu _); apply/seteqP; split => x.
    rewrite /preimage/= mindicE.
    have [|_] := boolP (_ \in _); first by rewrite mulr1 inE.
    by rewrite mulr0 => /esym/eqP; rewrite (negbTE r0).
  by rewrite /preimage/= => -[fxr cnx]; rewrite mindicE mem_set// mulr1.
rewrite sintegralE fsbig_finite//=.
apply: cvg_nnesum=> [r _|r _].
  near=> A; apply: (mulemu_ge0 (fun x => f @^-1` [set x] `&` fleg c A)) => r0.
  by rewrite preimage_nnfun0// set0I.
apply: cvgeZl => //=; rewrite [X in _ --> X](_ : _ =
    mu (\bigcup_n (f @^-1` [set r] `&` fleg c n))); last first.
  by rewrite -setI_bigcupr bigcup_fleg// setIT.
have ? k i : measurable (f @^-1` [set k] `&` fleg c i) by exact: measurableI.
apply: nondecreasing_cvg_mu; [by []|exact: bigcupT_measurable|].
move=> n m nm; apply/subsetPset; apply: setIS.
by move/(nd_fleg c) : nm => /subsetPset.
Unshelve. all: by end_near. Qed.

End sintegral_nondecreasing_limit_lemma.

Section sintegral_nondecreasing_limit.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variables (g : {nnsfun T >-> R}^nat) (f : {nnsfun T >-> R}).

Import HBNNSimple.

Hypothesis nd_g : forall x, nondecreasing_seq (g^~ x).
Hypothesis gf : forall x, g ^~ x @ \oo --> f x.

Let limg x : limn (g^~ x) = f x.
Proof. by apply/cvg_lim => //; exact: gf. Qed.

Lemma nd_sintegral_lim : sintegral mu f = limn (sintegral mu \o g).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: nd_sintegral_lim_lemma => // x; rewrite -limg.
have : nondecreasing_seq (sintegral mu \o g).
  by move=> m n mn; apply: le_sintegral => // x; exact/nd_g.
move=> /ereal_nondecreasing_cvgn/cvg_lim -> //.
apply: ub_ereal_sup => _ [n _ <-] /=; apply: le_sintegral => // x.
rewrite -limg // (nondecreasing_cvgn_le (nd_g x)) //.
by apply/cvg_ex; exists (f x); exact: gf.
Qed.

End sintegral_nondecreasing_limit.

Section integral.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Implicit Types (f g : T -> \bar R) (D : set T).

Import HBNNSimple.

Let nnintegral mu f := ereal_sup [set sintegral mu h |
  h in [set h : {nnsfun T >-> R} | forall x, (h x)%:E <= f x]].

Definition integral mu D f (g := f \_ D) :=
  nnintegral mu (g ^\+) - nnintegral mu (g ^\-).

Variable (mu : {measure set T -> \bar R}).

Let nnintegral_ge0 f : (forall x, 0 <= f x) -> 0 <= nnintegral mu f.
Proof.
by move=> f0; apply: ereal_sup_ubound; exists nnsfun0 => //; exact: sintegral0.
Qed.

Let eq_nnintegral g f : f =1 g -> nnintegral mu f = nnintegral mu g.
Proof. by move=> /funext->. Qed.

Let nnintegral0 : nnintegral mu (cst 0) = 0.
Proof.
rewrite /nnintegral /=; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply/ereal_sup_ubound; exists nnsfun0; [|exact: sintegral0].
apply/ub_ereal_sup => /= x [f /= f0 <-]; have {}f0 : forall x, f x = 0%R.
  by move=> y; apply/eqP; rewrite eq_le -2!lee_fin f0 //= lee_fin//.
by rewrite (eq_sintegral (@nnsfun0 _ T R)) ?sintegral0.
Qed.

Let nnintegral_nnsfun (h : {nnsfun T >-> R}) :
  nnintegral mu (EFin \o h) = sintegral mu h.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ub_ereal_sup => /= _ -[g /= gh <-]; rewrite le_sintegral.
by apply: ereal_sup_ubound => /=; exists h.
Qed.

Local Notation "\int_ ( x 'in' D ) F" := (integral mu D (fun x => F)%E)
  (at level 36, F at level 36, x, D at level 50,
  format "'[' \int_ ( x  'in'  D ) '/  '  F ']'").

Lemma eq_integral D g f : {in D, f =1 g} ->
  \int_(x in D) f x = \int_(x in D) g x.
Proof. by rewrite /integral => /eq_restrictP->. Qed.

Lemma ge0_integralE D f : (forall x, D x -> 0 <= f x) ->
  \int_(x in D) f x = nnintegral mu (f \_ D).
Proof.
move=> f0; rewrite /integral funeneg_restrict funepos_restrict.
have /eq_restrictP-> := ge0_funeposE f0.
have /eq_restrictP-> := ge0_funenegE f0.
by rewrite erestrict0 nnintegral0 sube0.
Qed.

Lemma ge0_integralTE f : (forall x, 0 <= f x) ->
  \int_(x in setT) f x = nnintegral mu f.
Proof. by move=> f0; rewrite ge0_integralE// patch_setT. Qed.

Lemma integralE D f :
  \int_(x in D) f x = \int_(x in D) (f ^\+ x) - \int_(x in D) f ^\- x.
Proof.
by rewrite [in LHS]/integral funepos_restrict funeneg_restrict -!ge0_integralE.
Qed.

Lemma integral0 D : \int_(x in D) cst 0 x = 0.
Proof. by rewrite ge0_integralE// erestrict0 nnintegral0. Qed.

Lemma integral0_eq D f :
  (forall x, D x -> f x = 0) -> \int_(x in D) f x = 0.
Proof.
move=> f0; under eq_integral; first by move=> x /[1!inE] /f0 ->; over.
by rewrite integral0.
Qed.

Lemma integral_ge0 D f : (forall x, D x -> 0 <= f x) -> 0 <= \int_(x in D) f x.
Proof.
move=> f0; rewrite ge0_integralE// nnintegral_ge0// => x.
by rewrite /patch; case: ifP; rewrite // inE => /f0->.
Qed.

Lemma integral_nnsfun D (mD : measurable D) (h : {nnsfun T >-> R}) :
  \int_(x in D) (h x)%:E = sintegral mu (h \_ D).
Proof.
rewrite mrestrict -nnintegral_nnsfun// -mrestrict ge0_integralE ?comp_patch//.
by move=> x Dx /=; rewrite lee_fin; exact: fun_ge0.
Qed.

End integral.

Notation "\int [ mu ]_ ( x 'in' D ) f" :=
  (integral mu D (fun x => f)%E) : ereal_scope.
Notation "\int [ mu ]_ x f" :=
  ((integral mu setT (fun x => f)%E))%E : ereal_scope.
Arguments eq_integral {d T R mu D} g.

Section integral_indic.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType)
        (mu : {measure set T -> \bar R}) (D : set T) (mD : measurable D).
Implicit Type A : set T.

Import HBNNSimple.

Lemma integral_indic A : measurable A ->
  \int[mu]_(x in D) (\1_A x)%:E = mu (A `&` D).
Proof.
move=> mA; rewrite (_ : \1_A = indic_nnsfun R mA)// integral_nnsfun//=.
by rewrite restrict_indic sintegral_indic//; exact: measurableI.
Qed.

End integral_indic.

Section domain_change.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma integral_mkcond D f : \int[mu]_(x in D) f x = \int[mu]_x (f \_ D) x.
Proof. by rewrite /integral patch_setT. Qed.

Import HBNNSimple.

Lemma integralT_nnsfun (h : {nnsfun T >-> R}) :
  \int[mu]_x (h x)%:E = sintegral mu h.
Proof. by rewrite integral_nnsfun// patch_setT. Qed.

Lemma integral_mkcondr D P f :
  \int[mu]_(x in D `&` P) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite integral_mkcond [RHS]integral_mkcond patch_setI. Qed.

Lemma integral_mkcondl D P f :
  \int[mu]_(x in P `&` D) f x = \int[mu]_(x in D) (f \_ P) x.
Proof. by rewrite setIC integral_mkcondr. Qed.

End domain_change.
Arguments integral_mkcond {d T R mu} D f.
