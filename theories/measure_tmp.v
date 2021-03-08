(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum topology normedtype.
Require Import sequences measure csum cardinality.
From HB Require Import structures.

(******************************************************************************)
(*                        measure.v cont'd (WIP)                              *)
(*                                                                            *)
(* mu_ext mu == outer measure built from a measure mu on a ring of sets       *)
(* mu.-measurable A == A is Caratheodory measurable                           *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(* - Caratheodory's theorem (mu.-measurable sets form a sigma-algebra, the    *)
(*   restriction of mu to M is a positive measure, mu*-negligible sets are    *)
(*   measurable)                                                              *)
(* - extension of a measure to an outer measure                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition uncurry A B C (f : A -> B -> C) := fun x : A * B => f x.1 x.2.

Notation ssum u := (lim (series u)).

Definition ext_measurable (R : realType) (T : Type)
  (mu : {outer_measure set T -> {ereal R}}) (A : set T) := forall X,
  (mu X = mu (X `&` A) + mu (X `&` ~` A))%E.

Notation "mu .-measurable" := (ext_measurable mu)
  (at level 2, format "mu .-measurable").

Lemma le_ext_measurable (R : realType) T
  (mu : {outer_measure set T -> {ereal R}}) (A : set T) :
  (forall X, (mu (X `&` A) + mu (X `&` ~` A) <= mu X)%E) ->
  mu.-measurable A.
Proof.
move=> suf X; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: le_outer_measureIC | exact: suf].
Qed.

Section caratheodory_theorem_part1.

Variables (R : realType) (T : Type)
  (mu : {outer_measure set T -> {ereal R}}).

Let M := mu.-measurable.

Lemma sigma_algebra_set0 : M set0.
Proof. by move=> X /=; rewrite setI0 outer_measure0 add0e setC0 setIT. Qed.

Lemma sigma_algebra_setC A : M A -> M (~` A).
Proof. by move=> MA X; rewrite setCK addeC -MA. Qed.

Lemma sigma_algebra_setU_helper (X : set T) A B
  (MA : mu.-measurable A)
  (MB : mu.-measurable B) :
  (mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <= mu X)%E.
Proof.
have /(lee_add2r (mu (X `&` (~` (A `|` B))))) :
    (mu (X `&` A `|` X `&` B `&` ~` A) <=
     mu (X `&` A) + mu (X `&` B `&` ~` A))%E.
  set C := bigcup2 (X `&` A) (X `&` B `&` ~` A).
  have -> :  X `&` A `|` X `&` B `&` ~` A = \bigcup_k C k.
    rewrite predeqE => t; split=> [[XAt|XBAt]|[]]; [by exists O|by exists 1%N|].
    by move=> [_ C0t|[_ C1t|//]]; [left | right].
  apply: (le_trans (outer_measure_sigma_subadditive mu C)).
  suff : (fun n => \sum_(i < n) mu (C i))%E -->
         (mu (X `&` A) + mu (X `&` B `&` ~` A))%E by move/cvg_lim => ->.
  rewrite -(cvg_shiftn 2) /=; set l := (X in _ --> X).
  rewrite (_ : (fun _ => _) = cst l); first exact: cvg_cst.
  rewrite funeqE => i; rewrite addn2 2!big_ord_recl big1 ?adde0 //.
  by move=> ? _; exact: outer_measure0.
have /le_trans : (mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <=
    mu (X `&` A `|` X `&` B `&` ~` A) + mu (X `&` ~` (A `|` B)))%E.
  rewrite setIUr (_ : X `&` A `|` X `&` B = (X `&` A) `|` (X `&` B `&` ~` A))//.
  rewrite -[in LHS](setIT B) -(setUCr A) 2!setIUr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply subIset; right.
suff -> : (mu (X `&` A) + mu (X `&` B `&` ~` A) +
    mu (X `&` (~` (A `|` B))) = mu X)%E by exact.
by rewrite setCU setIA -(setIA X) setICA (setIC B) -addeA -MB -MA.
Qed.

Lemma sigma_algebra_setU A B : M A -> M B -> M (A `|` B).
Proof.
rewrite /M => MA MB X /=; apply/eqP; rewrite eq_le.
apply/andP; split; first by apply le_outer_measureIC => //; exact: measurableU.
exact: sigma_algebra_setU_helper.
Qed.

Lemma sigma_algebra_bigU (A : (set T) ^nat) : (forall n, M (A n)) ->
  forall n, M (\big[setU/set0]_(i < n) A i).
Proof.
move=> MA; elim=> [|n ih]; first by rewrite big_ord0; exact: sigma_algebra_set0.
by rewrite big_ord_recr; apply sigma_algebra_setU.
Qed.

Lemma sigma_algebra_setI A B : M A -> M B -> M (A `&` B).
Proof.
move=> MA MB; rewrite -(setCK A) -(setCK B) -setCU.
apply sigma_algebra_setC.
by apply sigma_algebra_setU; apply sigma_algebra_setC.
Qed.

Section additive_ext_lemmas.
Variable E F : set T.
Hypothesis (ME : M E) (MF : M F).

Lemma additive_ext_decomp A :
  mu A = (mu (A `&` E `&` F) + mu (A `&` E `&` ~` F) +
          mu (A `&` ~` E `&` F) + mu (A `&` ~` E `&` ~` F))%E.
Proof. by rewrite ME MF [X in (_ + _ + X)%E = _]MF addeA. Qed.

Lemma additive_ext_decompU A : mu (A `&` (E `|` F)) =
  (mu (A `&` E `&` F) + mu (A `&` ~` E `&` F) + mu (A `&` E `&` ~` F))%E.
Proof.
rewrite additive_ext_decomp -!addeA; congr (mu _ + _)%E.
  rewrite -!setIA; congr (_ `&` _).
  by rewrite setIC; apply/setIidPl; apply subIset; left; left.
rewrite addeA addeC [X in (mu X + _)%E](_ : _ = set0) ?outer_measure0 ?add0e; last first.
  by rewrite predeqE => t; split => //; rewrite -setIA -setCU -setIA setICr setI0.
rewrite addeC; rewrite -!setIA; congr (mu (A `&` _) + mu (A `&` _))%E.
by rewrite setIC; apply/setIidPl; apply subIset; right; right.
by rewrite setIC; apply/setIidPl; apply subIset; left; left.
Qed.

Lemma additive_ext_inter A : E `&` F = set0 ->
  mu (A `&` (E `|` F)) = (mu (A `&` E) + mu (A `&` F))%E.
Proof.
move=> EF0; rewrite additive_ext_decomp -setIA EF0 setI0 outer_measure0 add0e.
rewrite addeC -setIA -setCU -setIA setICr setI0 outer_measure0 add0e.
rewrite -!setIA; congr (mu (A `&` _ ) + mu (A `&` _))%E.
rewrite (setIC E) setIA setIC; apply/setIidPl.
- by rewrite setIUl setICr setU0 subsetI; move/disjoints_subset in EF0; split.
- rewrite setIA setIC; apply/setIidPl; rewrite setIUl setICr set0U.
  by move: EF0; rewrite setIC => /disjoints_subset => EF0; rewrite subsetI; split.
Qed.
End additive_ext_lemmas.

Lemma additive_ext (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset A -> forall n X, mu (X `&` \big[setU/set0]_(i < n) A i) =
                        (\sum_(i < n) mu (X `&` A i))%E.
Proof.
move=> MA ta; elim=> [|n ih] X; first by rewrite !big_ord0 setI0 outer_measure0.
rewrite big_ord_recr /= additive_ext_inter // ?ih ?big_ord_recr //.
- exact: sigma_algebra_bigU.
- exact: trivIset_bigUI.
Qed.

Lemma lee_bigU_lim_sum (A : (set T) ^nat)  X :
  (mu (X `&` \bigcup_k A k) <= lim (fun n => \sum_(k < n) mu (X `&` A k)))%E.
Proof.
apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
by apply/le_outer_measure; rewrite bigcup_distrr.
Qed.

Lemma lee_lim_sum_bigU (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset A -> forall X,
  (lim (fun n => \sum_(k < n) mu (X `&` A k)) + mu (X `&` ~` \bigcup_k A k) <=
   mu X)%E.
Proof.
move=> MA tA X.
set A' := \bigcup_k A k; set B := fun n => \big[setU/set0]_(k < n) (A k).
suff : forall n, (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` A') <= mu X)%E.
  move=> lee_sum_bigU.
  rewrite [X in (X + _)%E](_ : _ = ereal_sup
    ((fun n : nat => \sum_(k < n) mu (X `&` A k))%E @` setT)); last first.
    set F := (X in lim_in _ X); have : ProperFilter F by typeclasses eauto.
    move/(@cvg_lim _ _ _); apply => //.
    apply/nondecreasing_seq_ereal_cvg.
    apply: (@lee_sum_nneg_ord _ (fun n => mu (X `&` A n)) xpredT) => n _.
    exact: outer_measure_ge0.
  move XAx : (mu (X `&` ~` A')) => x.
  case: x XAx => [x| |] XA.
  - rewrite -lee_subr_addr; apply ub_ereal_sup => /= y [n _] <-{y}.
    by rewrite lee_subr_addr -XA; exact: lee_sum_bigU.
  - suff : mu X = +oo%E by move=> ->; rewrite lee_pinfty.
    apply/eqP;rewrite -lee_pinfty_eq -XA.
    have : (X `&` ~` A' `<=` X) by apply subIset; left.
    by move/(le_outer_measure mu); apply; rewrite !inE.
  - by rewrite addeC /= lee_ninfty.
move=> n.
apply (@le_trans _ _ (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` B n))%E).
  apply/lee_add2l/le_outer_measure; apply: setIS; apply: subsetC => t.
  by rewrite /B bigcup_ord => -[i ni Ait]; exists i.
rewrite [in X in (_ <= X)%E](sigma_algebra_bigU MA n) lee_add2r //.
by rewrite additive_ext.
Qed.

Lemma sigma_algebra_trivIset_bigsetU (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset A -> M (\bigcup_k (A k)).
Proof.
move=> MA tA; apply le_ext_measurable => X /=.
have /(lee_add2r (mu (X `&` ~` \bigcup_k A k))) := lee_bigU_lim_sum A X.
by move/le_trans; apply; exact: lee_lim_sum_bigU.
Qed.

Lemma sigma_algebra_bigsetU (A : (set T) ^nat) : (forall n, M (A n)) ->
  M (\bigcup_k (A k)).
Proof.
move=> MA; set B := fun n => if n is m.+1 then
  A m.+1 `&` ~` (\big[setU/set0]_(i < n) A i) else A O.
have BA : forall n, B n `<=` A n.
  by case => // n; rewrite /B; apply subIset; left.
have MB : M (\bigcup_k B k).
  have MB : forall n, M (B n).
    case=> [|n /=]; first exact: MA.
    apply sigma_algebra_setI; [exact: MA|apply sigma_algebra_setC].
    exact: sigma_algebra_bigU.
  suff tB : trivIset B by exact: sigma_algebra_trivIset_bigsetU.
  move=> i j.
  wlog : i j / (i < j)%N.
    move=> H; rewrite neq_lt => /orP[ji|ij].
    by rewrite H // lt_eqF.
    by rewrite setIC H // lt_eqF.
  move=> ij _.
  rewrite predeqE => t; split => // -[] Bjt Bit.
  have Ait : A i t by apply BA.
  have BAC : forall n k, (k > n)%N -> B k `<=` ~` A n.
    move=> n [] // k; rewrite ltnS => nk /=; apply subIset.
    by right; apply subsetC => t' Ant; rewrite bigcup_ord; exists n.
  exact: (BAC _ _ ij t).
rewrite [X in M X](_ : _ = \bigcup_k B k) //.
rewrite predeqE => t; split; last by case => n _ Bnt; exists n => //; apply BA.
case=> n _ Ant.
set n0 := [arg min_(i < @ord_max n | `[< A i t >]) i].
have An0t : A n0 t.
  by rewrite /n0; case: arg_minnP => [|i /asboolP //]; apply/asboolP.
have nAn0t : forall k, (k < n0)%N -> ~ A k t.
  move=> k; rewrite /n0; case: arg_minnP; first exact/asboolP.
  move=> i /asboolP Ait H ki /asboolP Akt.
  have @k' : 'I_n.+1 by exists k; rewrite (ltn_trans ki).
  by move: (H k') => /(_ Akt); apply/negP; rewrite -ltnNge.
exists n0 => //.
move: nAn0t An0t; case: n0 => -[//|n0 /= n0n H An0t]; split => //.
by rewrite bigcup_ord => -[] => m /H.
Qed.

End caratheodory_theorem_part1.

Definition measurables (R : realType) (T : Type)
  (mu : {outer_measure set T -> {ereal R}}) := T.

Section caratheodory_theorem_instance.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> {ereal R}}).

(* caratheodory(1): mu.-measurable sets form a sigma-algebra *)
HB.instance Definition caratheodory_mixin := @isMeasurable.Build (measurables mu)
  mu.-measurable
  (sigma_algebra_set0 mu)
  (@sigma_algebra_setC _ _ mu)
  (@sigma_algebra_bigsetU _ _ mu).

Definition caratheodory_measurableType := [the measurableType of measurables mu].
(*Canonical caratheodory_measurableType : measurableType :=
  Measurable.Pack caratheodory_mixin.*)
End caratheodory_theorem_instance.

Section caratheodory_theorem_part2.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> {ereal R}}).
Let U : measurableType := caratheodory_measurableType mu.

Lemma caratheodory_measure0 : mu (set0 : set U) = 0%:E.
Proof. exact: outer_measure0. Qed.

(*Print Graph.
Check @measurable0 U.
Check mesurableI (set0 : set U) (set0 : set U).

Variable A : set U.
Variables (X : measurableType) (B : set X).

Check measurable B.*)

Lemma caratheodory_measure_ge0 (x : set U) :
  @measurable U x -> (0%:E <= (mu x : {ereal R}))%E.
Proof. by move=> mx; apply outer_measure_ge0. Qed.

Lemma caratheodory_measure_sigma_additive : @semi_sigma_additive _ U mu.
Proof.
move=> A mA tA mbigcupA; set B := \bigcup_k A k.
suff : forall X, (mu X = lim (fun n : nat => \sum_(k < n) mu (X `&` A k)) +
             mu (X `&` ~` B))%E.
  move/(_ B); rewrite setICr outer_measure0 adde0.
  rewrite (_ : (fun n => _) = (fun n => (\sum_(k < n) mu (A k))%E)); last first.
    rewrite funeqE => n; apply eq_bigr => i _; congr (mu _).
    by rewrite setIC; apply/setIidPl => t Ait; exists i.
  move=> ->.
  have : forall n, (0%:E <= mu (A n))%E by move=> n; apply outer_measure_ge0.
  move/(@is_cvg_ereal_nneg_series _ (mu \o A)) => /cvg_ex[l] H.
  by move/(@cvg_lim _ (@ereal_hausdorff R)) : (H) => ->.
move=> X.
have mB : mu.-measurable B := sigma_algebra_bigsetU mA.
apply/eqP; rewrite eq_le (lee_lim_sum_bigU mA tA X) andbT.
have /(lee_add2r (mu (X `&` ~` B))) := lee_bigU_lim_sum mu A X.
by rewrite -le_ext_measurable // => ?; rewrite -mB.
Qed.

Definition caratheodory_measure_mixin := Measure.Measure caratheodory_measure0
  caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
(* caratheodory(2): restriction of mu to M is a positive measure *)
Canonical caratheodory_measure : {measure set (measurables mu) -> _} :=
  Measure.Pack _ caratheodory_measure_mixin.

(* caratheodory(3): mu*-negligible sets are measurable *)
Lemma caratheodory_measure_complete (N : set U) :
  caratheodory_measure.-negligible N -> mu.-measurable N.
Proof.
move=> [A [mA muA0 NA]]; apply le_ext_measurable => X.
suff -> : mu (X `&` N) = 0%:E.
  by rewrite add0e le_outer_measure //; apply subIset; left.
have muN0 : mu N = 0%:E.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  by move: (le_outer_measure mu NA); rewrite muA0 => ->.
apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
have : X `&` N `<=` N by apply subIset; right.
by move/(le_outer_measure mu); rewrite muN0 => ->.
Qed.
End caratheodory_theorem_part2.

Section measure_extension.
Variables (R : realType) (T : ringOfSetsType) (mu : {measure set T -> {ereal R}}).

Definition measurable_cover A :=
  [set A_ : (set T) ^nat | (forall i, measurable (A_ i)) /\
                         A `<=` \bigcup_k (A_ k)].

Lemma cover_measurable A B : measurable_cover A B -> forall k, measurable (B k).
Proof. by move=> AB k; move: AB; rewrite /measurable_cover => -[] /(_ k). Qed.

Lemma cover_bigcup A B : measurable_cover A B -> A `<=` \bigcup_k (B k).
Proof. by case. Qed.

Definition mu_ext (A : set T) : {ereal R} :=
  ereal_inf [set lim [sequence (\sum_(i < n) mu (A_ i))%E]_n |
                 A_ in measurable_cover A].

Lemma mu_ext_ge0 A : (0%:E <= mu_ext A)%E.
Proof.
apply: lb_ereal_inf => x [B [mB AB] <-{x}]; rewrite ereal_lim_ge //=.
  by apply: (@is_cvg_ereal_nneg_series _ (mu \o B)) => // n; exact: measure_ge0.
by near=> n; rewrite sume_ge0 // => i _; apply: measure_ge0.
Grab Existential Variables. all: end_near. Qed.

Lemma mu_ext0 : mu_ext set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: mu_ext_ge0; exact: measurable0.
rewrite /mu_ext; apply ereal_inf_lb; exists (fun _ => set0).
  by split => // _; exact: measurable0.
by apply: (@lim_near_cst _ _ _ _ _ 0%:E) => //; near=> n => /=; rewrite big1.
Grab Existential Variables. all: end_near. Qed.

Lemma le_mu_ext : {homo mu_ext : A B / A `<=` B >-> (A <= B)%E}.
Proof.
move=> A B AB; apply/le_ereal_inf => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_sigma_subadditive : sigma_subadditive mu_ext.
Proof.
move=> A; rewrite /sigma_subadditive.
have [[i ioo]|] := pselect (exists i, mu_ext (A i) = +oo%E).
  rewrite (_ : lim _ = +oo%E) ?lee_pinfty //.
  apply: (@ereal_nneg_series_pinfty _ (mu_ext \o A) _ _ ioo) => n.
  exact: mu_ext_ge0.
rewrite -forallNE => Aoo.
suff add2e : forall e : {posnum R}, (mu_ext (\bigcup_n A n) <=
    lim (fun n => \sum_(i < n) mu_ext (A i)) + ((2 * e%:num)%R)%:E)%E.
  apply lee_adde => e; rewrite (_ : e%:num = 2 * (e%:num / 2)) ?add2e //.
  by rewrite mulrC -mulrA mulVr ?mulr1 // unitfE.
move=> e.
set P := fun n u_ => measurable_cover (A n) u_ /\
    (lim [sequence \sum_(j < k) mu (u_ j)]_k <=
     mu_ext (A n) + (e%:num / (2 ^ n)%:R)%:E)%E.
have [B BA] : {B : ((set T)^nat)^nat & forall n, P n (B n)}.
  apply: (@choice _ _ P) => n.
  rewrite /P /mu_ext; set S : set {ereal R} := fun _ : _ => _.
  move infS : (ereal_inf S) => iS.
  case: iS infS => [r Sr|Soo|Soo].
  - have en : 0 < e%:num / (2 ^ n.+1)%:R by rewrite divr_gt0 // ltr0n expn_gt0.
    (* TODO: (+,,,+) add to posnum *)
    have [x [[B [mB AnB muBx]] xS]] := lb_ereal_inf_adherent (PosNum en) Sr.
    exists B; split => //; rewrite muBx -Sr; apply/ltW.
    rewrite (lt_le_trans xS) // lee_add2l //= lee_fin ler_pmul //=.
    + by rewrite invr_ge0 // ler0n.
    + rewrite ler_pinv // ?inE ?unitfE;
        try by rewrite pnatr_eq0 expn_eq0 /= ltr0n expn_gt0.
      by rewrite ler_nat leq_exp2l.
  - by have := Aoo n; rewrite /mu_ext Soo.
  - suff : lbound S 0%:E by move/lb_ereal_inf; rewrite Soo.
    move=> /= _ [B [mB AnB] <-]; apply: (@ereal_nneg_series_lim_ge0 _ (mu \o B)).
    by move=> ?; exact: measure_ge0.
apply: (@le_trans _ _ (lim (fun n =>
  \sum_(i < n) (mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E)%E)); last first.
  rewrite (_ : (fun n => _) = ((fun n => \sum_(i < n) (mu_ext (A i)))%E \+
      (fun n => \sum_(i < n) (((e)%:num / (2 ^ i)%:R)%:E)%E))%E); last first.
    by rewrite funeqE => n; rewrite big_split.
  have cvggeo :
      (fun n => (\sum_(i < n) (e%:num / (2 ^ i)%:R)%:E)%E) --> (2 * e%:num)%:E.
    rewrite (_ : (fun n => _) =
        (@ERFin R) \o series (geometric e%:num (2^-1)%R)); last first.
      rewrite funeqE => n; rewrite /series /=.
      rewrite (@big_morph _ _ (@ERFin R) 0%:E adde) //.
      by apply eq_bigr => i _; rewrite natrX exprVn.
    apply: cvg_comp.
      apply: cvg_geometric_series.
      by rewrite ger0_norm // invr_lt1 // ?ltr1n // unitfE.
    rewrite (_ : [filter of _] = [filter of 2 * e%:num : R^o]) // !filter_of_filterE.
    congr ([filter of _]); rewrite mulrC; congr (_ * _); apply mulr1_eq.
    by rewrite mulrBl mulVr ?unitfE// mul1r (_ : 1 = 1%:R)// -natrB.
  rewrite ereal_limD //.
  - by rewrite lee_add2l // (cvg_lim _ cvggeo).
  - by apply: (@is_cvg_ereal_nneg_series _ (mu_ext \o A)) => n; exact: mu_ext_ge0.
  - apply: (@is_cvg_ereal_nneg_series _ (fun i => (e%:num / (2 ^ i)%:R)%:E)) => n.
    by rewrite lee_fin divr_ge0 // ler0n.
  - by rewrite (cvg_lim _ cvggeo) //= negb_or /= !negb_and /= orbT orbT.
pose muB :=
  lim [sequence (\sum_(i < n) (lim [sequence (\sum_(j < k) mu (B i j))%E]_k))%E ]_n.
apply (@le_trans _ _ muB).
  suff : (mu_ext (\bigcup_n A n) <=
      lim [sequence (\sum_(i < n) (lim [sequence (\sum_(j < m) mu (B i j))%E]_m))%E]_n)%E.
    exact/le_trans.
  have AB : \bigcup_n A n `<=` \bigcup_n (\bigcup_k B n k).
    move=> t [i _].
    by move/(cover_bigcup (proj1 (BA i))) => -[j _ ?]; exists i => //; exists j.
  have : (mu_ext (\bigcup_n A n) <= csum setT (mu \o uncurry B))%E.
    rewrite /mu_ext; apply ereal_inf_lb.
    have [f [TfT injf]] :
        exists e, enumeration (@setT (nat * nat)) e /\ injective e.
      have /countable_enumeration [|[f ef]] := countable_prod_nat.
        by rewrite predeqE => /(_ (O%N, 0%N)) [] /(_ I).
      by exists (enum_wo_rep infinite_prod_nat ef); split;
       [exact: enumeration_enum_wo_rep | exact: injective_enum_wo_rep].
    exists (uncurry B \o f).
      split; first by move=> i; exact: (cover_measurable (proj1 (BA (f i).1))).
      move/subset_trans : AB; apply => t [i _ [j _ Bijt]].
      rewrite /enumeration in TfT.
      have [k ijk] : exists k, f k = (i, j).
        have : setT (i, j) by [].
        rewrite TfT => -[k _ fkij].
        by exists k.
      exists k => //=.
      by rewrite ijk.
    have : forall x, (0%:E <= mu (uncurry B x))%E.
      by move=> x; exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
    move/(@csum_countable R _ (mu \o uncurry B) f xpredT) => <- //; rewrite TfT /=.
    congr (csum _ _).
    rewrite predeqE => /= -[a b]; split => [[n _ <-]|[m _ <-]].
      by exists n.
    by exists m.
  move/le_trans; apply.
  pose J : nat -> set (nat * nat) := fun i => [set (i, j) | j in setT].
  rewrite (_ : setT = \bigcup_k J k); last first.
    by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b.
  rewrite csum_csum; last 4 first.
  - by move=> /= x; exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
  - by exists O.
  - by move=> k; exists (k, O); exists O.
  - move=> i j ij.
    rewrite predeqE => -[x1 x2] /=; split => //= -[] [_] _ [<-{x1} _].
    by move=> [x2' _] [] /esym/eqP; rewrite (negbTE ij).
  rewrite (_ : setT = [set id i | i in xpredT]); last first.
    by rewrite predeqE => n; split => // _; exists n.
  rewrite csum_countable //; last first.
  - move=> n; apply csum_ge0 => /= x.
    exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
  apply lee_lim.
  - apply: (@is_cvg_ereal_nneg_series _ (fun i => csum (J i) (mu \o uncurry B))).
    move=> n; apply csum_ge0 => x.
    exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
  - apply: (@is_cvg_ereal_nneg_series _
       (fun i => lim (fun m => (\sum_(j < m) mu (B i j))%E))).
    move=> n; apply ereal_lim_ge.
    + apply: (@is_cvg_ereal_nneg_series _ (mu \o B n)) => k.
      exact/measure_ge0/(cover_measurable (proj1 (BA n))).
    + near=> m; apply sume_ge0 => i _.
      exact/measure_ge0/(cover_measurable (proj1 (BA n))).
  - near=> n.
    apply: lee_sum => j _.
    pose x_j : nat -> nat * nat := fun y => (nat_of_ord j, y).
    have [enux injx] : enumeration (J j) x_j /\ injective x_j.
      split => [|x y [] //].
      red.
        by rewrite predeqE=> -[? ?]; split => //.
    rewrite -(@csum_countable R _ (mu \o uncurry B) x_j predT) //=.
      rewrite le_eqVlt; apply/orP; left; apply/eqP.
      congr (csum _ _).
      rewrite predeqE => -[a b]; split.
        rewrite /J => -[i _ <-].
        by exists i.
      by move=> [i _ <-]; rewrite /J; exists i.
    by move=> x; exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
(*    + apply/card_eqP; exists (fun '(i, j) => j); split => //.
      * move=> /= [a b] [c d]; rewrite in_setE => -[x _ [<-{a} <-{b}]].
        by rewrite in_setE => -[y _ [<-{c} <-{d}]] ->.
      * by move=> /= k _ ; exists (nat_of_ord j, k); split => //; exists k.*)
apply lee_lim.
- apply/cvg_ex; eexists; apply nondecreasing_seq_ereal_cvg => i j ij.
  apply: (@lee_sum_nneg_ord _ (fun i => lim (fun k => (\sum_(j < k) mu (B i j))%E)) xpredT) => // n _.
  apply ereal_lim_ge.
  + apply: (@is_cvg_ereal_nneg_series _ (mu \o B n)) => x.
    exact/measure_ge0/(cover_measurable (proj1 (BA n))).
  + near=> m; apply sume_ge0 => // k _.
    exact/measure_ge0/(cover_measurable (proj1 (BA n))).
- apply/cvg_ex; eexists; apply nondecreasing_seq_ereal_cvg => i j ij.
  apply: (@lee_sum_nneg_ord _ (fun i => mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E xpredT) => // n _.
  by apply adde_ge0; [exact: mu_ext_ge0 | rewrite lee_fin // divr_ge0 // ler0n].
- by near=> n; apply: lee_sum => i _; exact: (proj2 (BA i)).
Grab Existential Variables. all: end_near. Qed.

End measure_extension.

Canonical canonical_outer_measure (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> {ereal R}}) : {outer_measure set T -> {ereal R}} :=
    OuterMeasure (OuterMeasure.OuterMeasure (mu_ext0 mu) (mu_ext_ge0 mu)
      (le_mu_ext mu) (mu_ext_sigma_subadditive mu)).

(* proposition 13.19 *)
Lemma mu_ext_measurable (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> {ereal R}}) X : measurable X -> mu_ext mu X = mu X.
Proof.
move=> mX; apply/eqP; rewrite eq_le; apply/andP; split.
  apply ereal_inf_lb; exists (fun n => if n is 0%N then X else set0).
    by split=> [[]// _|t Xt]; [exact: measurable0 | exists 0%N].
  set F := (X in lim_in _ X); have : ProperFilter F by typeclasses eauto.
  move/(@cvg_lim _ _ _); apply => //.
  rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu X)); first exact: cvg_cst.
  by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
apply/lb_ereal_inf => x [A [mA XA] <-{x}].
have XUA : X = \bigcup_n (X `&` A n).
  rewrite predeqE => t; split => [Xt|[i _ []//]].
  by have [i _ Ait] := XA _ Xt; exists i; split.
apply: (@le_trans _ _ (lim (fun n => \sum_(i < n) mu (X `&` A i)))%E).
  rewrite {1}XUA; apply: generalized_Boole_inequality => //; by [
    move=> i; exact: measurableI | rewrite -XUA].
apply lee_lim.
- apply: (@is_cvg_ereal_nneg_series _ (fun i => mu (X `&` A i))) => n.
  exact/measure_ge0/measurableI.
- by apply: (@is_cvg_ereal_nneg_series _ (mu \o A)) => n; exact/measure_ge0.
- near=> n; apply: lee_sum => i  _.
  apply: le_measure => //;
    rewrite /mkset ?in_setE //; by [exact: measurableI | apply: subIset; right].
Grab Existential Variables. all: end_near.
Qed.

Section outer_measurable.

Variables (R : realType) (T : measurableType) (mu : {measure set T -> {ereal R}}).

Lemma outer_measurable :
  forall A, measurable A -> (canonical_outer_measure mu).-measurable A.
Proof.
move=> A mA; apply le_ext_measurable => // X /=.
suff H : forall B, measurable B -> X `<=` B ->
  (mu_ext mu (X `&` A) + mu_ext mu (X `&` ~` A) <= mu B)%E.
  apply lb_ereal_inf => Y [B [mB XB] <-{Y}].
  have : measurable (\bigcup_k B k) by exact: measurable_bigcup.
  move/H => /(_ XB) /le_trans; apply.
  by apply: generalized_Boole_inequality => //; exact: measurable_bigcup.
move=> B mB BX; apply (@le_trans _ _ (mu (B `&` A) + mu (B `&` ~` A))%E).
  apply: lee_add.
  - apply/ereal_inf_lb; exists (fun n => if n is 0%N then B `&` A else set0).
      split=> [[|_]|t [Xt At]]; [apply: measurableI => // | exact: measurable0 | ].
      by exists 0%N => //; split => //; exact: BX.
    set F := (X in lim_in _ X); have : ProperFilter F by typeclasses eauto.
    move/(@cvg_lim _ _ _); apply => //.
    rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu (B `&` A))); first exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
  - apply ereal_inf_lb; exists (fun n => if n is 0%N then B `&` ~` A else set0).
      split=> [[|_]|t [Xt At]].
      + by rewrite -setDE; apply: measurableD.
      + exact: measurable0.
      + by exists 0%N; split => //; exact: BX.
    set F := (X in lim_in _ X); have : ProperFilter F by typeclasses eauto.
    move/(@cvg_lim _ _ _); apply => //.
    rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu (B `&` ~` A))).
      exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
rewrite -measure_additive2 //.
- by rewrite -setIUr setUCr setIT.
- exact: measurableI.
- by rewrite -setDE; apply: measurableD.
- by rewrite setICA -(setIA B) setICr 2!setI0.
Qed.

End outer_measurable.

Definition measurableP (U : Type) (T : set (set U)) :=
  [/\ T set0, (forall A, T A -> T (~` A)) &
             (forall A : (set U)^nat, (forall n, T (A n)) -> T (\bigcup_k A k))].

Lemma measurableP_measurable (T : measurableType) : measurableP (@measurable T).
Proof.
by split => //;
  [exact: measurable0 |exact: measurableC | exact: measurable_bigcup].
Qed.

Lemma measurableP_bigcap (U : Type) (I : choiceType) (T : I -> (set (set U))) :
  forall (J : set I), (forall n, J n -> measurableP (T n)) ->
                 measurableP (\bigcap_(i in J) (T i)).
Proof.
move=> J mT; split=> [i Ji|A AJ i Ji|A_ TA_ i Ji].
- by have [] := mT i.
- by have [_ mTiC _] := mT i Ji; exact/mTiC/AJ.
- by have [_ _ mTiU] := mT i Ji; apply mTiU => j; apply TA_.
Qed.

Reserved Notation "'s<<' A '>>'".

Section gen_salgebra.
Variables (U : Type).
Implicit Types M : set (set U).

Inductive gen_salgebra M : set (set U) :=
| gen_salgebra_self : forall A, M A -> s<< M >> A
| gen_salgebra_set0 : s<< M >> set0
| gen_salgebra_setC : forall A, s<< M >> A -> s<< M >> (~` A)
| gen_salgebra_bigcup : forall A : (set U)^nat, (forall i, s<< M >> (A i)) ->
    s<< M >> (\bigcup_i (A i)) where "'s<<' M '>>'" := (gen_salgebra M).

Lemma gen_salgebraE M :
  s<< M >> = \bigcap_(A in [set T | measurableP T /\ M `<=` T]) A.
Proof.
rewrite predeqE => A; split => [|]. elim=>
  [ {}A ? N [?] | {}A [[]]| {}A ? MA N [[? NC ?] ?] | {}A ? MA N [[? ? NI] ?]];
  [exact | by [] | by apply/NC; apply: MA | by apply NI => i; exact: (MA i)].
apply; split; [split|]; [exact: gen_salgebra_set0 | exact: gen_salgebra_setC |
  exact: gen_salgebra_bigcup | by move=> B MB; apply gen_salgebra_self].
Qed.

Lemma measurableP_gen_salgebra M : measurableP (gen_salgebra M).
Proof. by rewrite gen_salgebraE; apply measurableP_bigcap => /= ? [?]. Qed.

Lemma gen_salgebra_smallest M :
  forall T, measurableP T -> M `<=` T -> gen_salgebra M `<=` T.
Proof. by move=> T mT MT t; rewrite gen_salgebraE; exact. Qed.

End gen_salgebra.
Notation "'s<<' M '>>'" := (gen_salgebra M).

Definition gen_measurable (U : Type) (C : set (set U)) := U.

Section gen_salgebra_instance.
Variables (U : Type) (C : set (set U)).

HB.instance Definition gen_salgebra_mixin :=
  @isMeasurable.Build (gen_measurable C)
  (gen_salgebra C)
  (@gen_salgebra_set0 _ C)
  (@gen_salgebra_setC _ C)
  (@gen_salgebra_bigcup _ C).

Definition gen_salgebra_measurableType := [the measurableType of gen_measurable C].

End gen_salgebra_instance.

Definition eseries (R : realFieldType) (u_ : nat -> {ereal R}) : {ereal R} ^nat :=
  [sequence (\sum_(k < n) u_ k)%E]_n.

Section Hahn.
Variables (R : realType) (T : ringOfSetsType) (mu : {measure set T -> {ereal R}}).

Let mstar : {outer_measure set T -> {ereal R}} := canonical_outer_measure mu.
Let M : measurableType := caratheodory_measurableType mstar.

Lemma subset_gen_salgebra_caratheodory : s<< @measurable T >> `<=` @measurable M.
Proof.
apply: gen_salgebra_smallest.
  split; [exact: measurable0 | by move=> X mX; exact: measurableC |
    by move=> u_ mu_; exact: measurable_bigcup].
move=> A mA; apply le_ext_measurable => // X.
apply lb_ereal_inf => _ [B [mB XB] <-].
set BA := eseries (fun i => mu (B i `&` A)).
set BNA := eseries (fun i => mu (B i `&` ~` A)).
apply (@le_trans _ _ (lim BA + lim BNA)%E); [apply: lee_add|].
  - rewrite (_ : BA = eseries (fun i => mstar (B i `&` A))); last first.
      rewrite funeqE => n; apply: eq_bigr => i _.
      by rewrite /mstar /= mu_ext_measurable //; exact: measurableI.
    apply (@le_trans _ _ (mstar (\bigcup_k (B k `&` A)))).
      by apply le_mu_ext; rewrite -bigcup_distrl; apply setISS.
    exact: outer_measure_sigma_subadditive.
  - rewrite (_ : BNA = eseries (fun i => mstar (B i `\` A))%E); last first.
      rewrite funeqE => n; apply eq_bigr => i _.
      by rewrite /mstar /= mu_ext_measurable //; exact: measurableD.
    apply (@le_trans _ _ (mstar (\bigcup_k (B k `\` A)))).
      by apply le_mu_ext; rewrite -bigcup_distrl; apply setISS.
    exact: outer_measure_sigma_subadditive.
have ? : cvg BNA.
  apply/is_cvg_ereal_nneg_series => n.
  by rewrite -setDE; apply: measure_ge0 => //; apply: measurableD.
have ? : cvg BA.
  apply/is_cvg_ereal_nneg_series => n.
  by apply: measure_ge0 => //; apply: measurableI.
have ? : cvg (eseries (mu \o B)).
  by apply/is_cvg_ereal_nneg_series => n; exact: measure_ge0.
have [|undef] := boolP (adde_undef (lim BA) (lim BNA)).
  case/orP => [/andP[BAoo BNAoo]|/andP[BAoo BNAoo]].
  - suff : lim (eseries (mu \o B))%E = +oo%E by move=> ->; rewrite lee_pinfty.
    apply/eqP; rewrite -lee_pinfty_eq -(eqP BAoo); apply/lee_lim => //.
    near=> n; apply: lee_sum => m _; apply: le_measure; rewrite /mkset; by
      [rewrite inE; exact: measurableI | rewrite inE | apply: subIset; left].
  - suff : lim (eseries (mu \o B)) = +oo%E by move=> ->; rewrite lee_pinfty.
    apply/eqP; rewrite -lee_pinfty_eq -(eqP BNAoo); apply/lee_lim => //.
    near=> n; apply: lee_sum => m _; rewrite -setDE; apply: le_measure; rewrite /mkset; by
      [rewrite inE; exact: measurableD | rewrite inE | apply: subIset; left].
rewrite -ereal_limD // (_ : (fun _ => _) =
    eseries (fun i => mu (B i `&` A) + mu (B i `&` ~` A))%E); last first.
  by rewrite funeqE => n; rewrite -big_split /=; apply eq_bigr.
apply/lee_lim => //.
  apply/is_cvg_ereal_nneg_series => // n; apply/adde_ge0.
  by apply: measure_ge0 => //; apply: measurableI.
  by rewrite -setDE; apply: measure_ge0; apply: measurableD.
near=> n; apply: lee_sum => i _; rewrite -measure_semi_additive2.
- apply: le_measure; rewrite /mkset; [rewrite inE|by rewrite inE|by rewrite -setIUr setUCr setIT].
  by apply: measurableU; [exact: measurableI | rewrite -setDE; exact: measurableD].
- exact: measurableI.
- by rewrite -setDE; exact: measurableD.
- apply: measurableU; [exact: measurableI | rewrite -setDE; exact: measurableD].
- by rewrite setIACA setICr setI0.
Grab Existential Variables. all: end_near. Qed.

Let Hahn_mu : {measure set M -> {ereal R}} := caratheodory_measure mstar.

(*Let I : measurableType := gen_salgebra_measurableType (@setT (set T)).
Definition Hahn_mu : {measure set I -> {ereal R}}.*)

End Hahn.

From mathcomp Require Import interval.

(* NB: dup *)
Lemma segment_open (R : realFieldType) a b : open [set x : R^o | x \in `]a, b[].
Proof.
by apply interval_open.
Qed.
Lemma segment_closed (R : realFieldType) a b : closed [set x : R^o | x \in `[a, b] ].
Proof.
by apply interval_closed.
Qed.
(* NB: dup? *)
Definition set_of_interval (R : numDomainType) (i : interval R) : set R :=
  match i with
  | `]a, b[ => [set x | a < x < b] | `[a, b] => [set x | a <= x <= b]
  | `]a, b] => [set x | a < x <= b] | `[a, b[ => [set x | a <= x < b]
  | `]-oo, b[ => [set x | x < b] | `]-oo, b] => [set x | x <= b]
  | `]-oo, +oo[ => setT
  | `]a, +oo[ => [set x | a < x] | `[a, +oo[ => [set x | a <= x]
  | Interval _ -oo%O | Interval +oo%O _ => set0
  end.

Lemma mkset_intervalE (R : numDomainType) (i : interval R) : [set x | x \in i] = set_of_interval i.
Proof.
by move: i => [[[] r1|[]] [[]r2 | []]] //=; rewrite predeqE => x; split; rewrite /mkset !inE //=
  subitvE ?andbF // ?andbT //.
Qed.

Section set_of_interval.
Variable R : realType.

Lemma is_intervalP (X : set R) :
  is_interval X <-> exists i : interval R, X = [set x | x \in i].
Proof.
split.
move=> iX.
exists (Rhull X).
by apply/is_intervalP.
case => x ->.
by apply/interval_is_interval.
Qed.

Lemma open_closed_set1 (a b : R) : a < b ->
  [set x | a < x <= b] = [set x | a < x < b] `|` [set b].
Proof.
move=> ab; rewrite predeqE => r; rewrite /mkset; split=> [/andP[ar]|].
  by rewrite le_eqVlt => /orP[/eqP->|rb]; [by right|left; rewrite ar].
by case=> [/andP[ar /ltW ->]|->]; [rewrite andbT|rewrite ab lexx].
Qed.

Lemma closed_open_set1 (a b : R) : a < b ->
  [set x | a <= x < b] = [set a] `|` [set x | a < x < b].
Proof.
move=> ab; rewrite predeqE => r; rewrite /mkset; split=> [/andP[]|].
  by rewrite le_eqVlt => /orP[/eqP->|ar rb]; [left|right; rewrite ar].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma closed_closed_set1l (a b : R) : a <= b ->
  [set x | a <= x <= b] = [set a] `|` [set x | a < x <= b].
Proof.
move=> ab; rewrite predeqE => r; rewrite /mkset; split=> [/andP[]|].
  by rewrite le_eqVlt => /orP[/eqP->|ar rb]; [left|right; rewrite ar].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma closed_closed_set1r (a b : R) : a <= b ->
  [set x | a <= x <= b] = [set x | a <= x < b] `|` [set b].
Proof.
move=> ab; rewrite predeqE => r; rewrite /mkset; split=> [/andP[ar]|].
  by rewrite le_eqVlt => /orP[/eqP->|rb]; [right|left; rewrite ar].
by case=> [/andP[-> /ltW //]|->]; rewrite lexx ab.
Qed.

Lemma closed_infty_set1 (a : R) :
  [set x | a <= x] = [set a] `|` [set x | a < x].
Proof.
rewrite predeqE => r; rewrite /mkset; split; last by case=> [->//|/ltW].
by rewrite le_eqVlt => /orP[/eqP ->|ar]; [left|right].
Qed.

Lemma infty_closed_set1 (a : R) :
  [set x | x <= a] = [set x | x < a] `|` [set a].
Proof.
rewrite predeqE => r; rewrite /mkset; split => [|[/ltW //|->//]].
by rewrite le_eqVlt => /orP[/eqP ->|ar]; [right|left].
Qed.

Lemma subset_has_lbound (A B : set R) : A `<=` B ->
  has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma subset_has_ubound (A B : set R) : A `<=` B ->
  has_ubound B -> has_ubound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma sup_setU (A B : set R) : has_sup B -> (forall a b, A a -> B b -> a <= b) ->
  sup (A `|` B) = sup B.
Proof.
move=> [B0 [l Bl]] AB; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub => [|x [Ax|]]; first by apply: subset_nonempty B0 => ?; right.
  by case: B0 => b Bb; rewrite (le_trans (AB _ _ Ax Bb)) // sup_ub //; exists l.
- by move=> Bx; rewrite sup_ub //; exists l.
- apply sup_le_ub => // b Bb; apply sup_ub; last by right.
  by exists l => x [Ax|Bx]; [rewrite (le_trans (AB _ _ Ax Bb)) // Bl|exact: Bl].
Qed.

Lemma inf_setU (A B : set R) : has_inf A -> (forall a b, A a -> B b -> a <= b) ->
  inf (A `|` B) = inf A.
Proof.
move=> hiA AB; congr (- _).
rewrite image_setU setUC sup_setU //; first exact/has_inf_supN.
by move=> _ _ [] b Bb <-{} [] a Aa <-{}; rewrite ler_oppl opprK; apply AB.
Qed.

Lemma has_lbound_open_open (a b : R) : has_lbound [set x | a < x < b].
Proof. by exists a => y; rewrite /mkset => /andP[] /ltW. Qed.

Lemma has_lbound_open_closed (a b : R) : has_lbound [set x | a < x <= b].
Proof. by exists a => y; rewrite /mkset => /andP[] /ltW. Qed.

Lemma has_lbound_closed_open (a b : R) : has_lbound [set x | a <= x < b].
Proof. by exists a => y; rewrite /mkset => /andP[]. Qed.

Lemma has_lbound_closed_closed (a b : R) : has_lbound [set x | a <= x <= b].
Proof. by exists a => y; rewrite /mkset => /andP[]. Qed.

Lemma has_ubound_open_open (a b : R) : has_ubound [set x | a < x < b].
Proof. by exists b => y; rewrite /mkset => /andP[_] /ltW. Qed.

Lemma has_ubound_open_closed (a b : R) : has_ubound [set x | a < x <= b].
Proof. by exists b => y; rewrite /mkset => /andP[]. Qed.

Lemma has_ubound_closed_open (a b : R) : has_ubound [set x | a <= x < b].
Proof. by exists b => y; rewrite /mkset => /andP[_] /ltW. Qed.

Lemma has_ubound_closed_closed (a b : R) : has_ubound [set x | a <= x <= b].
Proof. by exists b => y; rewrite /mkset => /andP[]. Qed.

Lemma has_lbound_open_infty (a : R) : has_lbound [set x | a < x].
Proof. by exists a => y; rewrite /mkset => /ltW. Qed.

Lemma has_lbound_closed_infty (a : R) : has_lbound [set x | a <= x].
Proof. by exists a. Qed.

Lemma has_lbound_infty_open (a : R) : ~ has_lbound [set x | x < a].
Proof.
apply/has_lbPn => x; exists (minr (a - 1) (x - 1)).
by rewrite /mkset lt_minl ltr_subl_addr ltr_addl ltr01.
by rewrite lt_minl orbC ltr_subl_addr ltr_addl ltr01.
Qed.

Lemma has_lbound_infty_closed (a : R) : ~ has_lbound [set x | x <= a].
Proof.
have := @has_lbound_infty_open a.
by apply/ssrbool.contra_not/subset_has_lbound => x /ltW.
Qed.

Lemma has_ubound_infty_open (a : R) : has_ubound [set x | x < a].
Proof. by exists a => y; rewrite /mkset => /ltW. Qed.

Lemma has_ubound_infty_closed (a : R) : has_ubound [set x | x <= a].
Proof. by exists a. Qed.

Lemma has_ubound_open_infty (a : R) : ~ has_ubound [set x | a < x].
Proof.
apply/has_ubPn => x; rewrite /mkset; exists (maxr (a + 1) (x + 1));
by rewrite lt_maxr ltr_addl ltr01 // orbT.
Qed.

Lemma has_ubound_closed_infty (a : R) : ~ has_ubound [set x | a <= x].
Proof.
have := @has_ubound_open_infty a.
by apply/ssrbool.contra_not/subset_has_ubound => x /ltW.
Qed.

Lemma has_ubound_setT : ~ has_ubound (@setT R).
Proof.
case=> x; rewrite /ubound /mkset => /(_ (x + 1) I).
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

Lemma has_lbound_setT : ~ has_lbound (@setT R).
Proof.
case=> x; rewrite /ubound /mkset => /(_ (x - 1) I).
by apply/negP; rewrite -ltNge ltr_subl_addr ltr_addl.
Qed.

Hint Resolve has_lbound_open_open : core.
Hint Resolve has_lbound_open_closed : core.
Hint Resolve has_lbound_closed_open : core.
Hint Resolve has_lbound_closed_closed : core.
Hint Resolve has_ubound_open_open : core.
Hint Resolve has_ubound_open_closed : core.
Hint Resolve has_ubound_closed_open : core.
Hint Resolve has_ubound_closed_closed : core.
Hint Resolve has_ubound_open_infty : core.
Hint Resolve has_lbound_open_infty : core.
Hint Resolve has_lbound_closed_infty : core.
Hint Resolve has_lbound_infty_open : core.
Hint Resolve has_lbound_infty_closed : core.
Hint Resolve has_ubound_infty_open : core.
Hint Resolve has_ubound_open_infty : core.
Hint Resolve has_ubound_infty_closed : core.
Hint Resolve has_ubound_closed_infty : core.
Hint Resolve has_ubound_setT : core.
Hint Resolve has_lbound_setT : core.

Lemma has_sup1 (a : R) : has_sup [set a].
Proof. by split; [exists a | exists a => x ->]. Qed.

Lemma has_inf1 (a : R) : has_inf [set a].
Proof. by split; [exists a | exists a => x ->]. Qed.

Hint Resolve has_sup1 : core.
Hint Resolve has_inf1 : core.

Lemma has_sup_open_open (a b : R) : a < b -> has_sup [set x | a < x < b].
Proof.
by split => //; exists ((a + b) / 2); rewrite /mkset midf_lt //= midf_lt.
Qed.

Lemma has_inf_open_open (a b : R) : a < b -> has_inf [set x | a < x < b].
Proof.
by split => //; exists ((a + b) / 2); rewrite /mkset midf_lt //= midf_lt.
Qed.

Lemma has_inf_open_closed (a b : R) : a < b -> has_inf [set x | a < x <= b].
Proof.
by split => //; exists ((a + b) / 2); rewrite /mkset ?(midf_lt,midf_le (ltW _)).
Qed.

Lemma has_inf_closed_open (a b : R) : a < b -> has_inf [set x | a <= x < b].
Proof.
by split => //; exists ((a + b) / 2); rewrite /mkset ?(midf_lt,midf_le (ltW _)).
Qed.

Lemma has_inf_open_infty (a : R) : has_inf [set x | a < x].
Proof. by split => //; exists (a + 1); rewrite /mkset ltr_addl. Qed.

Lemma inf_open_infty (a : R) : inf [set x | a < x] = a.
Proof.
set i := inf _; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite leNgt; apply/negP => ai; pose p := (a + i) / 2.
  suff [/andP[?]]: (a < p) && (p < i) by apply/negP; rewrite -leNgt inf_lb.
  by rewrite !midf_lt.
- by apply lb_le_inf; [exists (a + 1); rewrite /mkset ltr_addl|move=> ? /ltW].
Qed.

Lemma inf_closed_infty (a : R) : inf [set x | a <= x] = a.
Proof. by rewrite closed_infty_set1 inf_setU ?inf1 // => _ b -> /ltW. Qed.

Lemma inf_open_open (a b : R) : a < b -> inf [set x | a < x < b] = a.
Proof.
move=> ?; set A := mkset _; set B := [set x | b <= x]; rewrite -(@inf_setU A B).
- rewrite -(inf_open_infty a); congr inf.
  rewrite predeqE => x; rewrite /mkset; split=> [[/andP[]//|]|ax].
  exact: lt_le_trans.
  by have [xb|bx] := ltP x b; [left; rewrite /A /mkset ax|right].
- exact: has_inf_open_open.
- move=> x y; rewrite /A /B /mkset => /andP[ax xb] yb.
  by rewrite (le_trans _ yb) // ltW.
Qed.

Lemma inf_closed_open (a b : R) : a < b -> inf [set x | a <= x < b] = a.
Proof.
by move=> ?; rewrite closed_open_set1// inf_setU ?inf1 // => _ ? -> /andP[/ltW].
Qed.

Lemma inf_open_closed (a b : R) : a < b -> inf [set x | a < x <= b] = a.
Proof.
move=> ?; rewrite open_closed_set1 // inf_setU ?inf_open_open //; by
  [exact: has_inf_open_open|move=> x y; rewrite /mkset => /andP[ax /ltW xb] ->].
Qed.

Lemma inf_closed_closed (a b : R) : a <= b -> inf [set x | a <= x <= b] = a.
Proof.
move=> ab; rewrite closed_closed_set1l // inf_setU ?inf1 //.
by move=> x y; rewrite /mkset => -> /andP[/ltW].
Qed.

Lemma sup_infty_open (a : R) : sup [set x | x < a] = a.
Proof.
set s := sup _; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub; last by move=> ? /ltW.
  by exists (a - 1); rewrite /mkset ltr_subl_addr ltr_addl.
- rewrite leNgt; apply/negP => sa; pose p := (s + a) / 2.
  suff [/andP[?]]: (p < a) && (s < p) by apply/negP; rewrite -leNgt sup_ub.
  by rewrite !midf_lt.
Qed.

Lemma sup_infty_closed (a : R) : sup [set x | x <= a] = a.
Proof.
rewrite infty_closed_set1 sup_setU ?sup1 // => a' b a'a ->; exact/ltW.
Qed.

Lemma sup_open_open (a b : R) : a < b -> sup [set x | a < x < b] = b.
Proof.
move=> ?; set B := mkset _; set A := [set x | x <= a]; rewrite -(@sup_setU A B).
- rewrite -(sup_infty_open b); congr sup.
  rewrite predeqE => x; rewrite /mkset; split=> [[|/andP[]//]|xb].
  by move/le_lt_trans; apply.
  by have [ax|xa] := ltP a x; [right; rewrite /B /mkset ax | left].
- exact: has_sup_open_open.
- move=> x y; rewrite /A /B /mkset => ax /andP[ay yb].
  by rewrite (le_trans _ (ltW ay)).
Qed.

Lemma sup_open_closed (a b : R) : a < b -> sup [set x | a < x <= b] = b.
Proof.
move=> ab; rewrite open_closed_set1 // sup_setU ?sup1 //.
by move=> x y; rewrite /mkset => /andP[ax /ltW xb] ->.
Qed.

Lemma sup_closed_open (a b : R) : a < b -> sup [set x | a <= x < b] = b.
Proof.
move=> ab; rewrite closed_open_set1 // sup_setU ?sup_open_open //; by
  [exact: has_sup_open_open|move=> x y; rewrite /mkset => -> /andP[/ltW]].
Qed.

Lemma sup_closed_closed (a b : R) : a <= b -> sup [set x | a <= x <= b] = b.
Proof.
move=> ab; rewrite closed_closed_set1r // sup_setU ?sup1//; by
  [exact: xxxhas_sup1|move=> x y; rewrite /mkset => /andP[_ /ltW xb ->]].
Qed.

Lemma nonempty_open_open (a b : R) : ([set x | a < x < b] == set0) = (a >= b).
Proof.
apply/idP/idP => [/eqP ab|ba]; [|apply/eqP].
  rewrite leNgt; apply/negP => ba; move/eqP : ab; apply/negP/set0P.
  by exists ((a + b) / 2); rewrite /mkset !midf_lt.
rewrite predeqE => r; split => //= => /andP[ar /(lt_trans ar)].
by rewrite ltNge ba.
Qed.

Lemma nonempty_closed_open (a b : R) : ([set x | a <= x < b] == set0) = (a >= b).
Proof.
apply/idP/idP => [/eqP ab|ba]; [|apply/eqP].
  rewrite leNgt; apply/negP => ba; move/eqP : ab; apply/negP/set0P.
  by exists ((a + b) / 2); rewrite /mkset (midf_le (ltW _)) // midf_lt.
rewrite predeqE => r; split => //= => /andP[ar /(le_lt_trans ar)].
by rewrite ltNge ba.
Qed.

Lemma nonempty_open_closed (a b : R) : ([set x | a < x <= b] == set0) = (a >= b).
Proof.
apply/idP/idP => [/eqP ab|ba]; [|apply/eqP].
  rewrite leNgt; apply/negP => ba; move/eqP : ab; apply/negP/set0P.
  by exists ((a + b) / 2); rewrite /mkset (midf_le (ltW _)) // midf_lt.
rewrite predeqE => r; split => //= => /andP[ar /(lt_le_trans ar)].
by rewrite ltNge ba.
Qed.

Lemma nonempty_closed_closed (a b : R) : ([set x| a <= x <= b] == set0) = (a > b).
Proof.
apply/idP/idP => [/eqP ab|ba]; [|apply/eqP].
  rewrite ltNge; apply/negP => ba; move/eqP : ab; apply/negP/set0P.
  by exists ((a + b) / 2); rewrite /mkset !midf_le.
rewrite predeqE => r; split => //= => /andP[ar /(le_trans ar)].
by rewrite leNgt ba.
Qed.

Lemma set_of_intervalK (X : interval R) : set_of_interval X !=set0 ->
  Rhull (set_of_interval X) = X.
Proof.
move: X => [[[] i1|[]] [[] i2|[]]]; rewrite /set_of_interval /Rhull //=.
- move/set0P; rewrite nonempty_closed_open -ltNge => i12.
  rewrite asboolT //= inf_closed_open // lexx i12 asboolT //.
  by rewrite asboolT // sup_closed_open // ltW // ltxx asboolF.
- move/set0P; rewrite nonempty_closed_closed -leNgt => X0.
  rewrite asboolT // inf_closed_closed // lexx X0 asboolT //.
  by rewrite asboolT // sup_closed_closed // X0 lexx asboolT //.
- by move/set0P; rewrite eqxx.
- by move=> _; rewrite asboolT // inf_closed_infty lexx asboolT // asboolF.
- move/set0P; rewrite nonempty_open_open -ltNge => i12.
  rewrite asboolT // inf_open_open // ltxx asboolF // asboolT // sup_open_open //.
  by rewrite ltxx andbF asboolF.
- move/set0P; rewrite nonempty_open_closed -ltNge => i12.
  rewrite asboolT // inf_open_closed // ltxx asboolF // asboolT // sup_open_closed //.
  by rewrite i12 lexx asboolT.
- by move/set0P; rewrite eqxx.
- by move=> _; rewrite asboolT // inf_open_infty ltxx asboolF // asboolF.
- by move=> _; rewrite asboolF // asboolT // sup_infty_open ltxx asboolF.
- by move=> _; rewrite asboolF // asboolT // sup_infty_closed lexx asboolT.
- by move/set0P; rewrite eqxx.
- by move=> _; rewrite asboolF // asboolF.
- by move/set0P; rewrite eqxx.
- by move/set0P; rewrite eqxx.
- by move/set0P; rewrite eqxx.
- by move/set0P; rewrite eqxx.
Qed.

Lemma interval_of_setK (X : set R) : is_interval X ->
  set_of_interval (Rhull X) = X.
Proof.
move=> iX; rewrite /Rhull /set_of_interval /=.
case: ifPn => /asboolP bX; last first.
  case: ifPn => /asboolP aX; last by rewrite (interval_unbounded_setT _ bX aX).
  have [/asboolP XsupX|/negPn /asboolP XsupX] := ifPn.
    rewrite predeqE => r; split => [|Xr]; last first.
      exact: sup_ub_strict.
    rewrite -interval_left_unbounded_interior //.
    exact: (@interior_subset [topologicalType of R^o]).
  rewrite eqEsubset; split => [r|r Xr].
    rewrite /mkset le_eqVlt => /orP[/eqP -> //|rX].
    move/has_lbPn : bX => /(_ r)[y Xy yr].
    by move: (iX _ _ Xy XsupX); apply; rewrite yr.
  by rewrite /mkset sup_ub //; exact/asboolP.
case: ifPn => /asboolP XinfX.
  case: ifPn => /asboolP aX; last first.
    rewrite predeqE => r; split => [|Xr]; last exact: inf_lb.
    rewrite /mkset le_eqVlt => /orP[/eqP <- //|infXr].
    move/has_ubPn : aX => /(_ r)[y Xy yr].
    by move: (iX _ _ XinfX Xy); apply; rewrite infXr.
  have [/asboolP XsupX|/negPn /asboolP XsupX] := ifPn.
    rewrite eqEsubset; split => [r|r Xr].
      rewrite /mkset => /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXr rsupX].
      apply: (@interior_subset [topologicalType of R^o]).
      by rewrite interval_bounded_interior //; rewrite /mkset infXr.
    by rewrite /mkset inf_lb //= sup_ub_strict.
  rewrite predeqE => r; split=> [|Xr]; last first.
    by rewrite /mkset sup_ub // andbT inf_lb.
  rewrite /mkset => /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXr].
  rewrite le_eqVlt => /orP[/eqP -> //|rsupX].
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_bounded_interior //; rewrite /mkset infXr.
case: ifPn => /asboolP uX.
  have [/asboolP XsupX|/negPn /asboolP XsupX] := ifPn.
    rewrite predeqE => r; split=> [|Xr]; last first.
      by rewrite /mkset inf_lb_strict // sup_ub_strict.
    move => /andP[infXr rsupX].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior //; rewrite /mkset infXr.
  rewrite predeqE => r; split=> [|Xr]; last first.
    by rewrite /mkset inf_lb_strict // sup_ub.
  rewrite /mkset => /andP[infXr]; rewrite le_eqVlt => /orP[/eqP -> //|rsupX].
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_bounded_interior //; rewrite /mkset infXr.
rewrite predeqE => r; split=> [|Xr]; last exact: inf_lb_strict.
rewrite -interval_right_unbounded_interior //.
exact: (@interior_subset [topologicalType of R^o]).
Qed.

Lemma Rhull_inj (X Y : set R) : is_interval X -> is_interval Y -> Rhull X = Rhull Y -> X = Y.
Proof.
move=> iX iY XY.
by rewrite -(interval_of_setK iX) -(interval_of_setK iY) XY.
Qed.

Lemma set_of_interval_inj (X Y : interval R) :
  set_of_interval X !=set0 -> set_of_interval Y !=set0 ->
  set_of_interval X = set_of_interval Y -> X = Y.
Proof.
move=> X0 Y0 XY.
have iX : is_interval (set_of_interval X).
  apply is_intervalP.
  exists X.
  by rewrite mkset_intervalE.
have iY : is_interval (set_of_interval Y).
  apply is_intervalP.
  exists Y.
  by rewrite mkset_intervalE.
by rewrite -(set_of_intervalK X0) -(set_of_intervalK Y0) XY.
Qed.

End set_of_interval.

Section cleanme.
Variable R : realType.

(* not used? *)
Lemma inf_is_sup (X : set R) : has_ubound X -> has_lbound X -> X !=set0 ->
  inf X = sup X -> X = [set inf X].
Proof.
move=> sX iX X0 iXsX; rewrite predeqE => r; split => [Xr|].
- rewrite /set1 /=; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite iXsX; apply: sup_upper_bound => //; split => //; exists r.
  by apply: inf_lower_bound => //; split => //; exists r.
- rewrite /set1 /= => ->{r}.
  apply: contrapT => XiX.
  case: X0 => x Xx.
  move: (inf_lb_strict iX XiX Xx).
  apply/negP.
  rewrite -leNgt.
  rewrite iXsX.
  by apply sup_upper_bound => //; split => //; exists x.
Qed.

(* not used? *)
Lemma inf_le_sup (X : set R) : has_ubound X -> has_lbound X ->
  X !=set0 -> inf X <= sup X.
Proof.
move=> uX lX [x Xx].
have [XiX|XiX] := pselect (X (inf X)).
  by apply sup_ub => //; case: uX.
have [XuX|XuX] := pselect (X (sup X)).
  by apply inf_lower_bound => //; split => //; exists (sup X).
by apply: (@le_trans _ _ x); [exact: inf_lb|exact: sup_ub].
Qed.

Lemma interval_closed_inf_subset (X Y : set R) : is_interval X -> is_interval Y ->
  has_lbound X -> has_lbound Y ->
  inf X = inf Y -> X (inf X) -> Y (inf Y) ->
  X `<=` Y \/ Y `<=` X.
Proof.
move=> iX iY lX lY infXY XinfX YinfY.
have [uX|uX] := pselect (has_ubound X); last first.
  right => y Yy.
  have : inf Y <= y by exact: inf_lb.
  rewrite le_eqVlt => /orP[/eqP <-|]; first by rewrite -infXY.
  rewrite -infXY => infXy.
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_right_unbounded_interior.
have [uY|uY] := pselect (has_ubound Y); last first.
  left => y Yy.
  have : inf X <= y by apply inf_lb.
  rewrite le_eqVlt => /orP[/eqP <-|]; first by rewrite infXY.
  rewrite infXY => infYy.
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_right_unbounded_interior.
rewrite -(interval_of_setK iY) -(interval_of_setK iX).
rewrite /set_of_interval /= /Rhull /=.
rewrite (asboolT lX) (asboolT uX) (asboolT XinfX).
rewrite (asboolT lY) (asboolT uY) (asboolT YinfY).
have [XY| YX | XY] := ltgtP (sup X) (sup Y).
- left => r.
  case: ifPn => /asboolP XsX; move/andP => [Xx xX]; case: ifPn => /asboolP YsY /=.
  by rewrite -infXY Xx /= (lt_trans xX).
  by rewrite -infXY Xx /= (le_trans (ltW xX) (ltW _)).
  by rewrite -infXY Xx /= (le_lt_trans xX _).
  by rewrite -infXY Xx /= (le_trans xX (ltW _)).
- right => r.
  case: ifPn => /asboolP YsY; move/andP => [Yx xY]; case: ifPn => /asboolP XsX /=.
  by rewrite infXY Yx (lt_trans xY _).
  by rewrite infXY Yx (ltW (lt_trans xY _)).
  by rewrite infXY Yx (le_lt_trans xY _).
  by rewrite infXY Yx (le_trans xY (ltW _)).
- have [XsX|XsX] := boolP `[< X (sup X) >].
  + right => r.
    case: ifPn => /asboolP YxY /= /andP[Yx xY].
    by rewrite infXY Yx XY ltW.
    by rewrite infXY Yx /= XY.
  + left => r /andP[Xx xX].
    case: ifPn => //= /asboolP YsY; rewrite -infXY Xx /=.
    by rewrite -XY.
    by rewrite -XY ltW.
Qed.

Lemma interval_open_inf_subset (X Y : set R) : is_interval X -> is_interval Y ->
  has_lbound X -> has_lbound Y ->
  inf X = inf Y -> ~ X (inf X) -> ~ Y (inf Y) ->
  X `<=` Y \/ Y `<=` X.
Proof.
move=> iX iY lX lY infXY XinfX YinfY.
have [uX|uX] := pselect (has_ubound X); last first.
  right => y Yy.
  have : inf Y <= y by apply inf_lb.
  rewrite le_eqVlt => /orP[/eqP yY|]; first by rewrite yY in YinfY.
  rewrite -infXY => infXy.
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_right_unbounded_interior.
have [uY|uY] := pselect (has_ubound Y); last first.
  left => y Yy.
  have : inf X <= y by apply inf_lb.
  rewrite le_eqVlt => /orP[/eqP yX|]; first by rewrite yX in XinfX.
  rewrite infXY => infYy.
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_right_unbounded_interior.
rewrite -(interval_of_setK iY) -(interval_of_setK iX).
rewrite /set_of_interval /= /Rhull.
rewrite (asboolT lY) (asboolT uY).
rewrite (asboolT lX) (asboolT uX).
rewrite (asboolF XinfX) (asboolF YinfY).
have [XY| YX | XY] := ltgtP (sup X) (sup Y).
- left => r.
  case: ifPn => /asboolP XsX /=; move/andP => [Xx xX]; case: ifPn => /asboolP YsY /=.
  by rewrite -infXY Xx /= (lt_trans xX).
  by rewrite -infXY Xx /= (le_trans (ltW xX) (ltW _)).
  by rewrite -infXY Xx /= (le_lt_trans xX _).
  by rewrite -infXY Xx /= (le_trans xX (ltW _)).
- right => r.
  case: ifPn => /asboolP YsY /=; move/andP => [Yx xY]; case: ifPn => /asboolP XsX /=.
  by rewrite infXY Yx (lt_trans xY _).
  by rewrite infXY Yx (ltW (lt_trans xY _)).
  by rewrite infXY Yx (le_lt_trans xY _).
  by rewrite infXY Yx (le_trans xY (ltW _)).
- have [XsX|XsX] := boolP `[< X (sup X) >].
  + right => r.
    case: ifPn => /asboolP YxY /= /andP[Yx xY].
    by rewrite infXY Yx XY ltW.
    by rewrite infXY Yx /= XY.
  + left => r /andP[Xx xX].
    case: ifPn => //= /asboolP YsY; rewrite -infXY Xx /=.
    by rewrite -XY.
    by rewrite -XY ltW.
Qed.

Lemma interval_infty_subset (X Y : set R) : is_interval X -> is_interval Y ->
  ~ has_lbound X -> ~ has_lbound Y ->
  has_ubound X -> has_ubound Y ->
  X `<=` Y \/ Y `<=` X.
Proof.
move=> iX iY lX lY uX uY.
rewrite -(interval_of_setK iY) -(interval_of_setK iX).
rewrite /set_of_interval /= /Rhull /=.
rewrite (asboolT uX) (asboolT uY).
rewrite (asboolF lX) (asboolF lY).
have [XY| YX | XY] := ltgtP (sup X) (sup Y).
- left => r.
  case: ifPn => /asboolP XsX; rewrite /mkset /= => XsupX; case: ifPn => /asboolP YsY.
  by rewrite (lt_trans XsupX).
  by rewrite (le_trans (ltW XsupX) (ltW _)).
  by rewrite (le_lt_trans XsupX).
  by rewrite (le_trans XsupX (ltW _)).
- right => r.
  case: ifPn => /asboolP YsY; rewrite /mkset /= => xsupY; case: ifPn => /asboolP XsX.
  by rewrite (lt_trans xsupY).
  by rewrite (le_trans (ltW xsupY) (ltW _)).
  by rewrite (le_lt_trans xsupY).
  by rewrite (le_trans xsupY (ltW _)).
- have [XsX|XsX] := boolP `[< X (sup X) >].
    right => r.
    case: ifPn => /asboolP YsY /= => xsupY.
    by rewrite XY ltW.
    by rewrite XY.
  left => r; rewrite {1}/mkset => xsupX.
  case: ifPn => /asboolP YsY /=.
  by rewrite -XY.
  by rewrite -XY (ltW xsupX).
Qed.

End cleanme.

Lemma is_interval_set0 (R : numDomainType) : `[< is_interval (@set0 R) >].
Proof. exact/asboolP. Qed.

(* NB: from infotheo *)
Definition equality_mixin_of_Type (T : Type) : Equality.mixin_of T :=
  EqMixin (fun x y : T => boolp.asboolP (x = y)).
Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (equality_mixin_of_Type T) boolp.gen_choiceMixin).

Module Ritv.
Record t (R : numDomainType) := mk {
  set_of_ritv : set R; is_itv : `[< is_interval set_of_ritv >] }.
Module Exports.
Section exports.
Variable R : numDomainType.
Definition ritv := t.
Coercion set_of_ritv : t >-> set.
Canonical Rinterval_eqType := Equality.Pack (equality_mixin_of_Type (ritv R)).
Canonical Rinterval_choiceType := choice_of_Type (ritv R).
Canonical Rinterval_subType := Eval hnf in [subType for (@set_of_ritv R)].
Canonical Rinterval_predType :=
  Eval hnf in PredType (fun t : ritv R => (fun x => x \in (t : set _))).
End exports.
End Exports.
End Ritv.
Export Ritv.Exports.

Section ritv_lemmas.
Variable R : numDomainType.

Lemma ritv_def (X : ritv R) :
  (forall x y, (X : set _) x -> (X : set _) y -> forall z, x < z < y -> (X : set _) z).
Proof. by case: X => /= i /asboolP. Qed.

Definition empty_ritv := Ritv.mk (is_interval_set0 R).


Lemma is_interval_set_of_itv0 (i : interval R) : `[< is_interval (set_of_interval i) >].
Proof.
apply/asboolP; rewrite -mkset_intervalE; exact: interval_is_interval.
Qed.

Definition ritv_of_itv (i : interval R) := Ritv.mk (@is_interval_set_of_itv0 i).

End ritv_lemmas.

Section real_measure.
Variable R : realType.

Definition lt_ritv (i j : ritv R) : bool :=
  match `[< has_lbound i >], `[< has_lbound j >] with
  | false, true => true
  | true, false => false
  | false, false =>
    match `[< has_ubound i >], `[< has_ubound j >] with
    | false, false => false
    | false, true => false
    | true, false => true
    | true, true => if i == j then false else `[< i `<=` j >]
    end
  | true, true =>
    if inf i < inf j then true else
    if inf i == inf j then
      match `[< (i : set _) (inf i) >], `[< (j : set _) (inf j) >] with
      | true, false => true
      | false, true => false
      | false, false => if i == j then false else `[< i `<=` j >]
      | true, true => if i == j then false else `[< i `<=` j >]
      end
    else
      false
 end.

Lemma lt_trans_ritv : transitive lt_ritv.
Proof.
move=> [j Hj] [i Hi] [k Hk] /=; rewrite /lt_ritv /=.
case: ifPn => Ki.
  case: ifPn => Kj //.
  case: ltgtP => [ij _|//|<-].
    case: ifPn => Kk //.
    case: ltgtP => [jk _|//|<-].
      by rewrite (lt_trans ij).
    by rewrite ij.
  case: ifPn => jj.
    case: ifPn => [ji|ji _].
      case: ifPn => ji' // /asboolP ij.
      case: ifPn => Kk //.
      case: ltgtP => [//|//|<-].
      case: ifPn => // ki.
      case: ifPn => jk' // /asboolP jk.
      case: ifPn.
        move/eqP => -[] ik.
        have ij' : i = j.
          rewrite eqEsubset.
          by split => //; rewrite ik.
        exfalso.
        move/negP : ji'; apply.
        apply/eqP => /=.
        by apply/val_inj.
      move=> _.
      by have /asboolP := subset_trans ij jk.
    case: ifPn => Kk //.
    case: ltgtP => [//|//|<-].
    by case: ifPn.
  case: ifPn => // ji.
  case: ifPn => ji' // /asboolP ij.
  case: ifPn => // Kk.
  case: ltgtP => [//|//|<-].
  case: ifPn => // ki.
  case: ifPn => jk' // /asboolP jk.
  case: ifPn => [/eqP[ik']|].
    have ij' : i = j.
      rewrite eqEsubset.
       by split => //; rewrite ik'.
     exfalso.
     move/negP : ji'; apply.
     apply/eqP => /=.
     by apply/val_inj.
  move=> _.
  by have /asboolP := subset_trans ij jk.
case: ifPn => [Kj _|Kj].
  case: ifPn => [Kk|//].
  case: ltgtP => [//|//|<-].
  by case: ifPn.
case: ifPn => uKi.
  case: ifPn => [uKj|uKj _].
    case: ifPn => // ij' /asboolP ij.
    case: ifPn => Kk => //.
    case: ifPn => uKk //.
    case: ifPn => jk' // /asboolP jk.
    case: ifPn => [/eqP[ik']|].
      have ji' : i = j.
        rewrite eqEsubset.
        by split => //; rewrite ik'.
     exfalso.
     move/negP : ij'; apply.
     apply/eqP => /=.
     by apply/val_inj.
  move=> _.
  by have /asboolP := subset_trans ij jk.
  case: ifPn => lKk //.
  by rewrite if_same.
by rewrite if_same.
Qed.

Lemma ltxx_ritv i : lt_ritv i i = false.
Proof.
rewrite /lt_ritv; case: ifPn => [Ki|/negbTE ->].
  rewrite Ki ltxx eqxx.
  by case: ifPn => [->|/negbTE ->]; rewrite eqxx.
by case: ifPn => [->|]; [rewrite eqxx|rewrite if_same].
Qed.

Definition le_ritv i j := (i == j) || (lt_ritv i j).

Lemma le_ritv_def i j : le_ritv i j = (i == j) || (lt_ritv i j).
Proof. by []. Qed.

Definition lt_ritv_pOrderMixin := LtPOrderMixin le_ritv_def ltxx_ritv lt_trans_ritv.

Lemma lt_ritv_display : unit. Proof. exact: tt. Qed.
Definition le_ritv_pOrderMixin :=
  Order.LtPOrderMixin.lePOrderMixin lt_ritv_pOrderMixin.
Canonical lt_ritv_pOrderType :=
  POrderType lt_ritv_display (ritv R) le_ritv_pOrderMixin.

Lemma lt_ritvE (i j : ritv R) : (i < j)%O = lt_ritv i j.
Proof. by []. Qed.

Lemma le_ritvE (i j : ritv R) : le_ritv i j = (i == j) || (i < j)%O.
Proof. by []. Qed.

Lemma total_le_ritv : total le_ritv.
Proof.
move=> [i inti] [j intj].
- rewrite 2!le_ritvE; have [//|/= ij] := boolP (_ == _).
  rewrite !lt_ritvE /lt_ritv /=.
  case: ifPn => /asboolP lKi.
    case: ifPn => /asboolP lKj; last by rewrite orbT.
    case: ltgtP => [//| |infij].
      by rewrite !orbT.
    case: ifPn => /asboolP ii.
      case: ifPn => /asboolP ji //.
      rewrite (negbTE ij) eq_sym (negbTE ij) /=.
      clear ij.
      move/asboolP in inti.
      move/asboolP in intj.
      by move: (interval_closed_inf_subset inti intj lKi lKj infij ii ji) => [|] /asboolP -> //; rewrite orbT.
    case: ifPn => /asboolP jj; first by rewrite orbT.
    rewrite (negbTE ij) eq_sym (negbTE ij) /=.
    clear ij.
    move/asboolP in inti.
    move/asboolP in intj.
    by move: (interval_open_inf_subset inti intj lKi lKj infij ii jj) => [|] /asboolP -> //; rewrite orbT.
- case: ifPn => // /asboolP lKj.
  case: ifPn => // /asboolP uKi.
    case: ifPn => // /asboolP uKj.
      rewrite (negbTE ij) eq_sym (negbTE ij) /=.
      clear ij.
      move/asboolP in inti.
      move/asboolP in intj.
      have [|] := interval_infty_subset inti intj lKi lKj uKi uKj; move/asboolP => -> //.
      by rewrite orbT.
    case: ifPn => // /asboolP uKj.
      by rewrite orbT.
    rewrite /= orbF.
    apply/eqP/val_inj => /=.
    simpl in *.
    rewrite (interval_unbounded_setT _ lKi uKi); last by exact/asboolP.
    rewrite (interval_unbounded_setT _ lKj uKj) //; exact/asboolP.
Qed.

Lemma le_ritv_total : totalPOrderMixin [porderType of ritv R].
Proof. exact: total_le_ritv. Qed.

Canonical le_ritv_latticeType := LatticeType (ritv R) le_ritv_total.
Canonical le_ritv_distrLatticeType := DistrLatticeType (ritv R) le_ritv_total.
Canonical le_ritv_orderType := OrderType (ritv R) le_ritv_total.

Lemma itv_ritv_subset (i j : interval R) :
  {subset i <= j} <-> ritv_of_itv i `<=` ritv_of_itv j.
Proof.
move: i j => [[[] i1|[]] [[] i2|[]]] [[[] j1|[]] [[] j2|[]]] //=; split => // H x; move: (H x); rewrite /mkset ?(inE,lteifT,lteifF,andbT,andbF,subitvE) //;
  rewrite /set0 /mkset -?falseE => K ?; by apply K.
Qed.

Definition empty_itv : interval R := `]0, 0[.

Lemma set_of_itv0_empty_itv : set_of_interval empty_itv = set0.
Proof.
rewrite eqEsubset; split => // x.
by rewrite /set_of_interval /= mc_1_10.Num.Theory.ltr_asym.
Qed.

Lemma ritv_of_itv0 : ritv_of_itv empty_itv = @empty_ritv R :> ritv R.
Proof.
apply/val_inj => /=; rewrite eqEsubset; split => // x; rewrite /mkset.
by rewrite andbC => /andP[x0 /(lt_trans x0)]; rewrite ltxx.
Qed.

Definition itv_cplt (i : interval R) : interval R * option (interval R) :=
  match i with
  | `]a, b[ => (`]-oo, a], Some `[b, +oo[ )
  | `[a, b] => (`]-oo, a[, Some `]b, +oo[ )
  | `] a, b] => (`]-oo, a], Some `]b, +oo[ )
  | `[a, b[ => (`]-oo, a[, Some `[b, +oo[ )
  | `]-oo, b[ => (`[b, +oo[, None)
  | `]-oo, b] => (`]b, +oo[, None)
  | `]a, +oo[ => (`]-oo, a], None)
  | `[a, +oo[ => (`]-oo, a[, None)
  | `]-oo, +oo[ => (empty_itv, None)
  | Interval _ -oo%O => (`]-oo, +oo[, None)
  | Interval +oo%O _ => (`]-oo, +oo[, None)
  end.

Ltac simplify_inequality :=
  match goal with
  | H : is_true (?i < ?j) |- is_true (?i < ?j) => exact: H
  | H : is_true (?i <= ?j) |- is_true (?i <= ?j) => exact: H
  | H : is_true (?i < ?j) |- is_true (?i <= ?j) => exact: (ltW H)
  | H : is_true (?i < ?j), K : is_true (?j < ?k) |- is_true (?i < ?k) =>
    exact: (lt_trans H K)
  | H : is_true (?i < ?j), K : is_true (?j <= ?k) |- is_true (?i < ?k) =>
    exact: (lt_le_trans H K)
  | H : is_true (?i <= ?j), K : is_true (?j < ?k) |- is_true (?i < ?k) =>
    exact: (le_lt_trans H K)
  | H : is_true (?i < ?v), K : is_true (?v <= ?j) |- is_true (?i <= ?j) =>
    exact: (le_trans (ltW H) K)
  | H : is_true (?i <= ?v), K : is_true (?v < ?j) |- is_true (?i <= ?j) =>
    exact: (le_trans H (ltW K))
  | H : is_true (?i < ?u) |- is_true (?i < ?j) => rewrite (lt_le_trans H) //=
  | H : is_true (?v <= ?j) |- is_true (?i <= ?j) => rewrite (le_trans _ H) //=
  | H : is_true (?v < ?j) |- is_true (?i < ?j) => rewrite (le_lt_trans _ H) //=
  | H : is_true (?i < ?j) |- is_true (?i < ?j < ?k) => rewrite H //=
  | H : is_true (?i < ?j) |- is_true (?i < ?j <= ?k) => rewrite H //=
  | H : is_true (?j <= ?k) |- is_true (?i < ?j <= ?k) => rewrite H ?andbT //=
  | H : is_true (?j < ?k) |- is_true (?i <= ?j < ?k) => rewrite H ?andbT //=
  | H : is_true (?i <= ?j) |- is_true (?i <= ?j < ?k) => rewrite H //=
  | H : is_true (?j <= ?k) |- is_true (?i <= ?j <= ?k) => rewrite H ?andbT //=
  | H : is_true (?i <= ?j) |- is_true (?i <= ?j <= ?k) => rewrite H //=
  | H : is_true (?i <= ?u) |- is_true (?i < ?j < ?k) => rewrite (le_lt_trans H) //=
  | H : is_true (?i < ?u) |- is_true (?i < ?j < ?k) => rewrite (lt_le_trans H) //=
  | H : is_true (?i < ?u) |- is_true (?i < ?j <= ?k) => rewrite (lt_le_trans H) //=
  | H : is_true (?v < ?k) |- is_true (?i <= ?j < ?k) => rewrite (le_lt_trans _ H) ?andbT//=
  | H : is_true (?i <= ?u) |- is_true (?i <= ?j < ?k) => rewrite (le_trans H) //=
  | H : is_true (?v <= ?k) |- is_true (?i <= ?j < ?k) => rewrite (lt_le_trans _ H) ?andbT //=
  | H : is_true (?v <= ?k) |- is_true (?i < ?j <= ?k) => rewrite (le_trans _ H) ?andbT //=
  | H : is_true (?v < ?k) |- is_true (?i < ?j <= ?k) => rewrite (le_trans _ (ltW H)) ?andbT //=
  | H : is_true (?i <= ?u) |- is_true (?i <= ?j <= ?k) => rewrite (le_trans H) //=
  | H : is_true (?v <= ?k) |- is_true (?i <= ?j <= ?k) => rewrite (le_trans _ H) ?andbT //=
  end.

Lemma le_BR_BL (a b : R) : (BRight a <= BLeft b)%O = (a < b). Proof. by []. Qed.
Lemma le_BL_BL (a b : R) : (BLeft a <= BLeft b)%O = (a <= b). Proof. by []. Qed.
Lemma le_BR_BR (a b : R) : (BRight a <= BRight b)%O = (a <= b). Proof. by []. Qed.
Lemma le_BL_BR (a b : R) : (BLeft a <= BRight b)%O = (a <= b). Proof. by []. Qed.
Lemma lt_BR_BL (a b : R) : (BRight a < BLeft b)%O = (a < b). Proof. by []. Qed.
Lemma lt_BL_BL (a b : R) : (BLeft a < BLeft b)%O = (a < b). Proof. by []. Qed.
Lemma lt_BR_BR (a b : R) : (BRight a < BRight b)%O = (a < b). Proof. by []. Qed.
Lemma lt_BL_BR (a b : R) : (BLeft a < BRight b)%O = (a <= b). Proof. by []. Qed.


Definition le_BB := (le_BR_BL,le_BL_BR,le_BR_BR,le_BL_BL,lt_BR_BL,lt_BL_BR,lt_BR_BR,lt_BL_BR).

Lemma itv_cplt_pairP (i j1 j2 : interval R) : itv_cplt i = (j1, Some j2) ->
  forall x y z, x \in j1 -> y \in j2 -> z \in i -> x < z < y.
Proof.
move: i => [[[] i1|[]] [[] i2|[]]] //= [] <-{j1} <-{j2} x y z;
  rewrite !inE /= !subitvE /= ?(andbT,andbF,le_BB) => H1 H2 /andP[H3 H4]; by repeat simplify_inequality.
Qed.

Definition set_of_pair (x : interval R * option (interval R)) :=
  match x with
  | (x', None) => set_of_interval x'
  | (x1, Some x2) => set_of_interval x1 `|` set_of_interval x2
  end.

Lemma itv_cpltE (i : interval R) : set_of_pair (itv_cplt i) = ~` set_of_interval i.
Proof.
rewrite eqEsubset; split => x; move: i => [[[] i1|[]] [[] i2|[]]] /=; rewrite /mkset.
- case=> xi /andP[].
  + by move=> /(lt_le_trans xi); rewrite ltxx.
  + by move=> _ /(le_lt_trans xi); rewrite ltxx.
- case=> xi /andP[].
  + by move=> /(lt_le_trans xi); rewrite ltxx.
  + by move=> _ /(lt_le_trans xi); rewrite ltxx.
- by rewrite setC0.
- by move=> xi /(lt_le_trans xi); rewrite ltxx.
- case=> xi /andP[].
  + by move=> /(le_lt_trans xi); rewrite ltxx.
  + by move=> _ /(le_lt_trans xi); rewrite ltxx.
- case=> xi /andP[].
  + by move=> /(le_lt_trans xi); rewrite ltxx.
  + by move=> _ /(lt_le_trans xi); rewrite ltxx.
- by rewrite setC0.
- by move=> xi /(le_lt_trans xi); rewrite ltxx.
- by move=> xi /(le_lt_trans xi); rewrite ltxx.
- by move=> xi /(lt_le_trans xi); rewrite ltxx.
- by rewrite setC0.
- by rewrite mc_1_10.Num.Theory.ltr_asym.
- by rewrite setC0.
- by rewrite setC0.
- by rewrite setC0.
- by rewrite setC0.
- by move/negP; rewrite negb_and -leNgt -ltNge => /orP[?|?]; [left|right].
- by move/negP; rewrite negb_and -!ltNge => /orP[?|?]; [left|right].
- by rewrite setC0.
- by move/negP; rewrite -ltNge.
- by move/negP; rewrite negb_and -!leNgt => /orP[?|?]; [left|right].
- by move/negP; rewrite negb_and -ltNge -leNgt => /orP[?|?]; [left|right].
- by rewrite setC0.
- by move/negP; rewrite -leNgt.
- by move/negP; rewrite -leNgt.
- by move/negP; rewrite -ltNge.
- by rewrite setC0.
- by move=> nTx; exfalso; apply nTx.
- by rewrite setC0.
- by rewrite setC0.
- by rewrite setC0.
- by rewrite setC0.
Qed.

Ltac case_leltP :=
  match goal with
  | |- context [ (if (?i <= ?j) then _ else _) ] => (case: (leP i j) => ?)
  | |- context [ (if (?i < ?j) then _ else _) ] => (case: (ltP i j) => ?)
  end.

Ltac MAX := rewrite /mkset ?(le_maxl,lt_minr,le_minr,lt_maxl) /=.

Ltac ANDP :=
  (move=> /andP[/andP[? ?] /andP[? ?]] ||
   move=> /andP[/andP[? ?] ?] ||
   move=> /andP[? /andP[? ?]] ||
   move=> /andP[? ?] ||
   idtac
  )
  ;
  rewrite /setI /mkset; split; by repeat simplify_inequality.

Ltac TRY :=
  (by ANDP ||
   by case_leltP; MAX; ANDP ||
   by case_leltP; MAX; case_leltP; MAX; ANDP ||
   by rewrite if_same).

Ltac SPLIT3 :=
  (by simplify_inequality) ||
  (apply/andP; split; ((by simplify_inequality) || SPLIT3)).

Ltac AND_HYPO :=
  (rewrite /setI /mkset => -[/andP[? ?] /andP[? ?]] ||
  rewrite /setI /mkset => -[/andP[? ?] ?] ||
  rewrite /setI /mkset => -[? /andP[? ?]] ||
  rewrite /setI /mkset => -[? ?]
 ).

Ltac GOAL2 :=
    (AND_HYPO; MAX; SPLIT3) ||
    (AND_HYPO; case_leltP; SPLIT3) ||
    (AND_HYPO; case_leltP; MAX; SPLIT3) ||
    (AND_HYPO; case_leltP; case_leltP; MAX; SPLIT3).

Lemma itv_intersectionE (i j : interval R) :
  set_of_interval (itv_intersection i j) = set_of_interval i `&` set_of_interval j.
Proof.
rewrite eqEsubset; split => x.
- move: i j => [[[] i1|[]] [[] i2|[]]] [[[] j1|[]] [[] j2|[]]] /=;
    rewrite ?(orbT,andbT,andbF,orbF,le_total,meetEtotal,joinEtotal) //=;
    rewrite -?(leNgt,ltNge);
    MAX; rewrite ?mc_1_10.Num.Theory.ltr_asym; MAX; try TRY.

    case_leltP; MAX; case_leltP; MAX; by ANDP.
    case_leltP; MAX; case_leltP; MAX; by ANDP.
    case_leltP; MAX; case_leltP; MAX; by ANDP.
    case_leltP; MAX; case_leltP; MAX; by ANDP.

- move: i j => [[[] i1|[]] [[] i2|[]]] [[[] j1|[]] [[] j2|[]]] /=;
    rewrite ?(orbT,andbT,andbF,orbF,le_total,meetEtotal,joinEtotal) //=;
    rewrite -?(leNgt,ltNge); rewrite ?(setI0,set0I,setIT,setTI) //;
    rewrite ?mc_1_10.Num.Theory.ltr_asym; try GOAL2.

Qed.

(* don't use with j <= i! *)
Definition itv_diff (i j : interval R) : interval R :=
  match itv_cplt j with
  | (j', None) => itv_intersection i j'
  | (j1, Some j2) => if set_of_interval (itv_intersection i j1) != set0 then
                      itv_intersection i j1
                    else
                      itv_intersection i j2
  end.

Lemma itv_diffE (i j : interval R) : ~ {subset j <= i} ->
  set_of_interval (itv_diff i j) = set_of_interval i `\` set_of_interval j.
Proof.
move=> ji; rewrite setDE -itv_cpltE /itv_diff.
move H : (itv_cplt j) => h.
case: h => j1 [j2|] in H *; last by rewrite itv_intersectionE.
case: ifPn => ij10.
  rewrite /= setIUr itv_intersectionE //.
  move/(congr1 set_of_pair) : (H) => H'.
  rewrite itv_cpltE /= in H'.
  have {}ij10 : set_of_interval i `&` set_of_interval j1 != set0.
    apply: contra ij10 => /eqP ij10.
    rewrite -itv_intersectionE in ij10.
    exact/eqP.
  rewrite (_ : _ `&` set_of_interval j2 = set0) ?setU0 //.
  have {}ji : ~ set_of_interval j `<=` set_of_interval i.
    apply: ssrbool.contra_not ji.
    by move/itv_ritv_subset.
  apply: contrapT.
  move/eqP/set0P => ij20.
  apply: ji.
  move/set0P in ij10.
  move=> x jx.
  case: ij20 => i2 [ii2 j2i2].
  case: ij10 => i1 [ii1 j1i1].
  apply: (@ritv_def _ (ritv_of_itv i) i1 i2) => //.
  apply: (@itv_cplt_pairP j j1 j2) => //.
  by rewrite -mkset_intervalE /mkset in j1i1.
  by rewrite -mkset_intervalE /mkset in j2i2.
  by rewrite -mkset_intervalE /mkset in jx.
move/negPn in ij10.
rewrite /= setIUr itv_intersectionE //.
rewrite -[X in X `|` _]itv_intersectionE (eqP ij10).
by rewrite set0U.
Qed.

Definition ritv_diff (i j : ritv R) : ritv R :=
  ritv_of_itv (itv_diff (Rhull i) (Rhull j)).

Definition ritv_cplt (i : ritv R) : ritv R * option (ritv R) :=
  match itv_cplt (Rhull i) with
    | (i', None) => (ritv_of_itv i', None)
    | (i1, Some i2) => (ritv_of_itv i1, Some (ritv_of_itv i2))
  end.

Lemma ritv_diffE (i j : ritv R) : ~ i `<=` j -> ~ j `<=` i ->
  ritv_diff i j = i `\` j :> set _.
Proof.
move=> ij ji.
rewrite /ritv_diff.
rewrite /=.
rewrite itv_diffE; last first.
  apply: ssrbool.contra_not ji.
  move/itv_ritv_subset.
  destruct i.
  destruct j.
  rewrite [Rhull _]lock.
  rewrite [X in _ `<=` ritv_of_itv X]lock.
  rewrite /=.
  rewrite -2!lock.
  by rewrite !interval_of_setK //; exact/asboolP.
destruct i.
destruct j.
simpl.
clear ij ji.
move/asboolP in is_itv.
move/asboolP in is_itv0.
rewrite -[in RHS](interval_of_setK is_itv).
by rewrite -[in RHS](interval_of_setK is_itv0).
Qed.

Definition fint : Type := {fset (ritv R)}.
Definition ufint (x : seq (ritv R)) : set R :=
  \bigcup_(i in [set j | j \in x]) i.

Program Definition decompose' (s : seq (ritv R))
  (f : forall s', (size s' < size s)%N -> seq (ritv R)) : seq (ritv R) :=
  match s with
  | [::] => [::]
  | [:: i] => [:: i]
  | [:: i, j & tl] =>
    match pselect (i `<=` j) with
    | left _ => f (j :: tl) _
    | right not_ij => match pselect (j `<=` i) with
                     | left _ => f (i :: tl) _
                     | right _ => ritv_diff i j :: f (j :: tl) _
                     end
    end
  end.

Lemma wfr : well_founded (fun s' s : seq (ritv R) => (size s' < size s)%N).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => s t /ssrnat.ltP. Qed.

Definition decompose : seq (ritv R) -> seq (ritv R) :=
  Fix wfr (fun _ => _ _) decompose'.

Lemma decompose'_ext (x : seq (ritv R))
  (f g : forall y : seq (ritv R), (size y < size x)%N -> seq (ritv R)) :
    (forall (y : seq (ritv R)) (p : (size y < size x)%N), f y p = g y p) ->
  decompose' f = decompose' g.
Proof.
move => fg; congr decompose'.
by apply functional_extensionality_dep => ?; apply functional_extensionality_dep.
Qed.

Lemma decompose_nil : decompose [::] = [::].
Proof. by rewrite /decompose Fix_eq //=; exact decompose'_ext. Qed.

Lemma decompose_one i : decompose [:: i] = [:: i].
Proof. rewrite /decompose Fix_eq //=; exact: decompose'_ext. Qed.

Lemma decompose_two i j tl : decompose [:: i, j & tl] =
    match pselect (i `<=` j) with
    | left _ => decompose (j :: tl)
    | right not_ij => match pselect (j `<=` i) with
                     | left _ => decompose (i :: tl)
                     | right _ => ritv_diff i j :: decompose (j :: tl)
                     end
    end.
Proof.
rewrite {1}/decompose Fix_eq; last exact: decompose'_ext.
move: i j => [i1 i2] [j1 j2] //=; case: pselect => //.
by case: pselect => //.
Qed.

Lemma bigcup_cons {T : choiceType} U (h : T) t (f : T -> set U) :
  \bigcup_(i in [set i | i \in h :: t]) (f i) =
  f h `|` \bigcup_(i in [set i | i \in t]) (f i).
Proof.
rewrite predeqE => u; split.
  move=> [i]; rewrite /mkset inE => /orP[/eqP-> fhu|it fiu]; by [left|right; exists i].
case=> [fhu|].
  by exists h => //; rewrite /mkset mem_head.
by move=> [i it fiu]; exists i => //; rewrite /mkset inE it orbT.
Qed.

Lemma ufint_decompose (s : seq (ritv R)) :
  path.sorted <%O s -> ufint (decompose s) = ufint s.
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j tl]]].
  by case => // _ _; rewrite decompose_nil.
  by move=> _ _; rewrite decompose_one.
move=> [tln] Hsort.
rewrite decompose_two.
case: (pselect _) => ij.
  rewrite /= ih //; last by move: Hsort; rewrite /= => /andP[].
  rewrite /ufint 3!bigcup_cons setUA; congr setU.
  by rewrite setUC; apply/esym/setUidPl.
case: (pselect _) => ji.
  rewrite /= ih //; last first.
    rewrite (_ : _ :: _ = mask (true :: false :: nseq (size tl) true) [:: i, j & tl]); last first.
      by rewrite /= mask_true.
    apply path.path_mask => //.
    exact: lt_trans.
  rewrite /ufint 3!bigcup_cons setUA; congr setU.
  by apply/esym/setUidPl.
rewrite /= {1}/ufint /= (@bigcup_cons _ _ _ (decompose (j :: tl))).
rewrite -/(ufint (decompose (j :: tl))) ih //; last first.
  by move: Hsort; rewrite /= => /andP[].
rewrite {2}/ufint bigcup_cons -/(ufint _).
rewrite ritv_diffE //.
rewrite eqEsubset; split.
  move=> x [|]; last by right.
  by case; by left.
move=> x [ix|].
  have [jx|jx] := pselect ((j : set _) x).
    right.
    exists j => //.
    by rewrite /mkset mem_head.
  by left.
by right.
Qed.

Lemma trivIset_decompose (s : seq (ritv R)) : path.sorted <%O s ->
  forall t : ritv R, (forall c, c \in s -> t `&` c = set0) ->
  path.path (fun a b : ritv R => a `&` b == set0) t (decompose s).
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j tl]]].
  move=> _ /size0nil ->{} _ t tc.
  by rewrite decompose_nil.
  move=> _ _ t tc.
  by rewrite decompose_one /= tc ?mem_head // eqxx.
case.
destruct n => // -[] tln H t tc.
rewrite decompose_two.
case: pselect => ij.
  apply ih => //.
  by rewrite /= tln.
  rewrite /= in H.
  simpl.
  by case/andP : H.
  move=> c cjtl.
  by rewrite tc // inE cjtl orbT.
case: pselect => // ji.
  apply ih.
  by rewrite /= tln.
  rewrite (_ : _ :: _ = mask (true :: false :: nseq (size tl) true) [:: i, j & tl]); last first.
    by rewrite /= mask_true.
  apply path.path_mask => //.
  exact: lt_trans.
  move=> c.
  rewrite inE => citl.
  by rewrite tc // !inE orbCA citl orbT.
simpl.
apply/andP; split.
  rewrite itv_diffE //.
  rewrite interval_of_setK //.
  rewrite interval_of_setK //.
  rewrite setDE.
  rewrite setIA.
  rewrite tc ?set0I //.
  by rewrite mem_head.
  apply/asboolP/Ritv.is_itv.
  apply/asboolP/Ritv.is_itv.
  apply: ssrbool.contra_not ji.
  move/itv_ritv_subset.
  rewrite [Rhull _]lock [X in _ `<=` ritv_of_itv X]lock /= -2!lock.
  rewrite interval_of_setK; last first.
    apply/asboolP/Ritv.is_itv.
  rewrite interval_of_setK; last first.
    apply/asboolP/Ritv.is_itv.
  done.
apply ih.
by rewrite /= tln.
move: H.
apply: path.subseq_sorted.
exact: lt_trans.
exact: subseq_cons.
move=> c cjtl.
rewrite ritv_diffE //.

Admitted.

(*Lemma trivIset_decompose (s : seq (ritv R)) : path.sorted <%O s ->
  trivIset [sequence (nth (empty_ritv R) (decompose s) n)]_n.
Proof.
move=> Hsort i j ij.
rewrite /=.
Admitted.*)

Ltac Obligation Tactic := idtac.
Program Definition interval_isRingOfSets : isRingOfSets R :=
  @isRingOfSets.Build _ _ _ _ _.
Next Obligation.
exact [set ufint X | X in @setT fint].
Defined.
Next Obligation.
rewrite /interval_isRingOfSets_obligation_1.
exists fset0 => //.
rewrite /ufint /= (_ : (fun j : (ritv R) => _) = set0); last by rewrite predeqE.
by rewrite bigcup_set0.
Qed.
Next Obligation.
rewrite /interval_isRingOfSets_obligation_1 in H H0 *.
case: H => a _ aA.
case: H0 => b _ bB.
exists (a `|` b)%fset => //.
rewrite eqEsubset; split => [r [I]|r [Ar|Br]].
  rewrite /mkset inE => /orP[Ia Ir|Ib Ir].
  by left; rewrite -aA /ufint; exists I.
  by right; rewrite -bB /ufint; exists I.
move: Ar; rewrite -aA => -[I Ia Ir].
by exists I => //; rewrite /mkset in_fsetE Ia.
move: Br; rewrite -bB => -[I Ib Ir].
by exists I => //; rewrite /mkset in_fsetE Ib orbT.
Qed.
Next Obligation.
rewrite /interval_isRingOfSets_obligation_1 in H *.
case: H => a _ aA.
rewrite /mkset /=.
set b := decompose a.
Admitted.

Definition length_interval (i : interval R) : {ereal R} :=
  match i with
  | `]a, b[ => `|b - a|%:E
  | `[a, b] => `|b - a|%:E
  | `]a, b] => `|b - a|%:E
  | `[a, b[ => `|b - a|%:E
  | Interval (BInfty true) _ => +oo
  | Interval _ (BInfty false) => +oo
  | _ => 0%:E
  end.

Lemma length_interval_ge0 i : (0%:E <= length_interval i)%E.
Proof.
by move: i => [[[] r1|[]] [[] r2|[]]] /=; rewrite ?lee_pinfty // ?lee_fin.
Qed.

Definition countable_cover (A : set R) : set ((interval R) ^nat) :=
  [set u_ | exists (a_ : R ^nat), exists (b_ : R ^nat),
    [/\ (forall n, (a_ n <= b_ n)),
       (A `<=` \bigcup_n (set_of_interval `] (a_ n), (b_ n) [ )) &
       (u_ = fun n => `] (a_ n), (b_ n) [)] ].

Definition lstar (A : set R) := ereal_inf
  [set x : {ereal R} | exists i : (interval R) ^nat,
    countable_cover A i /\
    let u_ := (fun n => \sum_(k < n) (length_interval (i k)))%E in
    x = if pselect (cvg u_) is left _ then (lim (u_ @ \oo)) else +oo%E].

Lemma lstar_set0 : lstar set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply ereal_inf_lb; exists (fun=> `]0, 0[); split.
    by exists (fun=> 0), (fun=> 0); split.
  move=> u_.
  have u_E : u_ = fun=> 0%:E.
    by rewrite funeqE => n; rewrite /u_ /= big1 // => _ _; rewrite subr0 normr0.
  have : cvg u_ by rewrite u_E; exact: is_cvg_cst.
  case: pselect => // _ _; rewrite u_E.
  exact/esym/(@lim_cst _ (@ereal_hausdorff _)).
- apply lb_ereal_inf => /= x [i [ci ->{x}]].
  case: pselect => [cli|]; last by rewrite lee_pinfty.
  apply: (@ereal_nneg_series_lim_ge0 _ (fun k => length_interval (i k))).
  move=> n.
  exact: length_interval_ge0.
Grab Existential Variables. all: end_near. Qed.

End real_measure.
