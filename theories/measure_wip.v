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

(* WIP *)
Lemma setDT {T} (A : set T) : A `\` setT = set0.
Proof. by rewrite setDE setCT setI0. Qed.

Lemma set0D {T} (A : set T) : set0 `\` A = set0.
Proof. by rewrite setDE set0I. Qed.

Lemma setD0 {T} (A : set T) : A `\` set0 = A.
Proof. by rewrite setDE setC0 setIT. Qed.

Lemma bigcup_cons {T : choiceType} U (h : T) t (f : T -> set U) :
  \bigcup_(i in [set i | i \in h :: t]) (f i) =
  f h `|` \bigcup_(i in [set i | i \in t]) (f i).
Proof.
rewrite predeqE => u; split.
- move=> [i]; rewrite /mkset inE => /orP[/eqP-> fhu|it fiu];
    by [left|right; exists i].
- case=> [fhu|]; first by exists h => //; rewrite /mkset mem_head.
  by move=> [i it fiu]; exists i => //; rewrite /mkset inE it orbT.
Qed.

Lemma mkset0 {T : choiceType} : [set x | x \in [::]] = set0 :> set T.
Proof. by rewrite predeqP. Qed.

Lemma bigcup_nil {T : choiceType} U (f : T -> set U) :
  \bigcup_(i in [set i | i \in [::]]) (f i) = set0.
Proof. by rewrite predeqE => u; split => // -[t]; rewrite mkset0. Qed.

Lemma bigcup_cons1 {T : choiceType} U (h : T) (f : T -> set U) :
  \bigcup_(i in [set i | i \in [:: h]]) (f i) = f h.
Proof. by rewrite bigcup_cons bigcup_nil setU0. Qed.

Lemma bigcupC (T I : Type) (U : I -> set T) (E : set I) :
  ~` (\bigcup_(i in E) U i) = \bigcap_(i in E) ~` U i.
Proof.
rewrite eqEsubset; split => [x nU i Ei Uix|x nU [i Ei Uix]];
  [by apply nU; exists i | exact: (nU i Ei)].
Qed.

Lemma subset_has_lbound (R : numDomainType) (A B : set R) : A `<=` B ->
  has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. Qed.

Lemma subset_has_ubound (R : numDomainType) (A B : set R) : A `<=` B ->
  has_ubound B -> has_ubound A.
Proof.
by move=> AB [l Bl]; exists l => a Aa; apply/Bl/AB. (*NB: use has_lb_ubN ?*)
Qed.

Lemma sup_setU (R : realType) (A B : set R) : has_sup B ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof.
move=> [B0 [l Bl]] AB; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub => [|x [Ax|]]; first by apply: subset_nonempty B0 => ?; right.
  by case: B0 => b Bb; rewrite (le_trans (AB _ _ Ax Bb)) // sup_ub //; exists l.
- by move=> Bx; rewrite sup_ub //; exists l.
- apply sup_le_ub => // b Bb; apply sup_ub; last by right.
  by exists l => x [Ax|Bx]; [rewrite (le_trans (AB _ _ Ax Bb)) // Bl|exact: Bl].
Qed.

Lemma inf_setU (R : realType) (A B : set R) : has_inf A ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof.
move=> hiA AB; congr (- _).
rewrite image_setU setUC sup_setU //; first exact/has_inf_supN.
by move=> _ _ [] b Bb <-{} [] a Aa <-{}; rewrite ler_oppl opprK; apply AB.
Qed.

Lemma le_pinfty_eq (R : numDomainType) (x : itv_bound R) : (+oo <= x)%O = (x == +oo)%O.
Proof. by move: x => [[]|[]]. Qed.

Lemma le_minfty_eq (R : numDomainType) (x : itv_bound R) : (x <= -oo)%O = (x == -oo%O).
Proof. by case: x => // -[]. Qed.

Lemma pinfty_lt (R : numDomainType) (x : itv_bound R) : (+oo%O < x)%O = false.
Proof. by case: x. Qed.

Lemma itv_bound_meet_minfty (R : realDomainType) (i : itv_bound R) : (i `&` -oo = -oo)%O.
Proof. by rewrite meetEtotal /= minElt ifF //; case: i => [[]i|[]]. Qed.

Lemma itv_bound_minfty_meet (R : realDomainType) (i : itv_bound R) : (-oo `&` i = -oo)%O.
Proof. by rewrite meetC itv_bound_meet_minfty. Qed.

Lemma itv_bound_join_pinfty (R : realDomainType) (i : itv_bound R) : (+oo `|` i = +oo)%O.
Proof. by rewrite joinEtotal /= maxElt (@ifF _ (+oo < i)%O). Qed.

Lemma itv_bound_pinfty_join (R : realDomainType) (i : itv_bound R) : (i `|` +oo = +oo)%O.
Proof. by rewrite joinC itv_bound_join_pinfty. Qed.

Definition itv_join_meet := (itv_bound_meet_minfty, itv_bound_minfty_meet,
  itv_bound_join_pinfty, itv_bound_pinfty_join).

Lemma itv_meet_minfty_open (R : realDomainType) (i1 i2 : itv_bound R) (j1 : R) :
  itv_meet (Interval i1 i2) `]-oo, j1[ = Interval i1 (i2 `&` (BLeft j1))%O.
Proof. by move: i1 i2 => [? i1|[]] ?. Qed.

Lemma itv_meet_minfty_closed (R : realDomainType) (i1 i2 : itv_bound R) (j1 : R) :
  itv_meet (Interval i1 i2) `]-oo, j1] = Interval i1 (i2 `&` (BRight j1))%O.
Proof. by move: i1 i2 => [? i1|[]] ?. Qed.

Lemma itv_meet_open_pinfty (R : realDomainType) (i1 i2 : itv_bound R) (j2 : R) :
  itv_meet (Interval i1 i2) `]j2, +oo[ = (Interval (i1 `|` (BRight j2)) i2)%O.
Proof. by move: i1 i2 => i1 [? i2|[]]. Qed.

Lemma itv_meet_closed_pinfty (R : realDomainType) (i1 i2 : itv_bound R) (j2 : R) :
  itv_meet (Interval i1 i2) `[j2, +oo[ = (Interval (i1 `|` (BLeft j2)) i2)%O.
Proof. by move: i1 i2 => i1 [? i2|[]]. Qed.

Definition itv_meet_infty := (itv_meet_minfty_open, itv_meet_minfty_closed,
  itv_meet_open_pinfty, itv_meet_closed_pinfty).

Lemma itv_meet_mem (R : realDomainType) (i1 i2 j1 j2 : itv_bound R) (x : R) :
  x \in itv_meet (Interval i1 i2) (Interval j1 j2) <->
  x \in Interval i1 i2 /\ x \in Interval j1 j2.
Proof.
split.
  rewrite /= 3!itv_boundlr joinEtotal meetEtotal le_maxl le_minr.
  by move=> /andP[/andP[-> ->] /andP[-> ->]].
case; rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[j1x xj2].
by rewrite /= itv_boundlr joinEtotal meetEtotal le_maxl le_minr i1x j1x xj2 xi2.
Qed.

Section set_of_itv.
Variable (R : numDomainType).
Implicit Type i j : interval R.
Implicit Type x y : R.

Definition set_of_itv i : set R := [set x | x \in i].

Lemma is_interval_set_of_itv i : is_interval (set_of_itv i).
Proof. exact: interval_is_interval. Qed.

Lemma set_of_itv_mem i x : (set_of_itv i) x <-> x \in i.
Proof. by move: i => [[[]i1|[]] [[]i2|[]]]. Qed.

Lemma itv_set_of_itv_subset i j : {subset i <= j} <-> set_of_itv i `<=` set_of_itv j.
Proof. by move: i j => [[[] ?|[]] [[] ?|[]]] [[[] ?|[]] [[] ?|[]]]. Qed.

Lemma set_of_itv_empty_set0 (i j : itv_bound R) :
  ~~ (i < j)%O -> set_of_itv (Interval i j) = set0.
Proof.
move/itv_ge => ij0; rewrite predeqE => r; split => //.
by rewrite /set_of_itv /mkset ij0.
Qed.

Lemma set_of_itv_pinfty_set0 (a : itv_bound R) : set_of_itv (Interval +oo%O a) = set0.
Proof. by rewrite set_of_itv_empty_set0. Qed.

Lemma set_of_itv_minfty_set0 (a : itv_bound R) : set_of_itv (Interval a -oo%O) = set0.
Proof. rewrite set_of_itv_empty_set0 //=; by case: a => [[]a|[]]. Qed.

Definition set_of_itv_infty_set0 := (set_of_itv_minfty_set0, set_of_itv_pinfty_set0).

Lemma set_of_itv_open_open x y : set_of_itv `]x, y[ = (fun z => x < z < y).
Proof. by []. Qed.

Lemma set_of_itv_closed_closed x y : set_of_itv `[x, y] = (fun z => x <= z <= y).
Proof. by []. Qed.

Lemma set_of_itv_open_closed x y : set_of_itv `]x, y] = (fun z => x < z <= y).
Proof. by []. Qed.

Lemma set_of_itv_closed_open x y : set_of_itv `[x, y[ = (fun z => x <= z < y).
Proof. by []. Qed.

Lemma set_of_itv_minfty_pinfty : set_of_itv `]-oo, +oo[ = setT :> set R.
Proof. by rewrite predeqE. Qed.

Lemma set_of_itv_open_pinfty x : set_of_itv `]x, +oo[ = (fun z => x < z).
Proof. by rewrite predeqE /set_of_itv /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_of_itv_closed_pinfty x : set_of_itv `[x, +oo[ = (fun z => x <= z).
Proof. by rewrite predeqE /set_of_itv /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_of_itv_minfty_open x : set_of_itv `]-oo, x[ = (fun z => z < x).
Proof. by rewrite predeqE /set_of_itv /mkset => r; rewrite in_itv. Qed.

Lemma set_of_itv_minfty_closed x : set_of_itv `]-oo, x] = (fun z => z <= x).
Proof. by rewrite predeqE /set_of_itv /mkset => r; rewrite in_itv. Qed.

Lemma set_of_itv_minfty_minfty : set_of_itv (Interval -oo%O -oo%O) = set0 :> set R.
Proof. by rewrite set_of_itv_empty_set0. Qed.

Lemma set_of_itv_pinfty_minfty : set_of_itv (Interval +oo%O -oo%O) = set0 :> set R.
Proof. by rewrite set_of_itv_empty_set0. Qed.

Lemma set_of_itv_pinfty_pinfty : set_of_itv (Interval +oo%O +oo%O) = set0 :> set R.
Proof. by rewrite set_of_itv_empty_set0. Qed.

Definition set_of_itvE := (set_of_itv_open_open, set_of_itv_closed_closed,
  set_of_itv_open_closed, set_of_itv_closed_open, set_of_itv_minfty_pinfty,
  set_of_itv_open_pinfty, set_of_itv_closed_pinfty, set_of_itv_minfty_open,
  set_of_itv_minfty_closed, set_of_itv_minfty_minfty, set_of_itv_pinfty_minfty,
  set_of_itv_pinfty_pinfty).

Section punctured_interval.

Lemma open_closed_set1 x y : x < y ->
  set_of_itv `]x, y] = set_of_itv `]x, y[ `|` [set y].
Proof.
move=> ab; rewrite !set_of_itvE predeqE => r; split=>[/andP[xr]|].
  by rewrite le_eqVlt => /orP[/eqP->|ry]; [by right|left; rewrite xr].
by case=> [/andP[ar /ltW ->]|->]; [rewrite andbT|rewrite ab lexx].
Qed.

Lemma closed_open_set1 x y : x < y ->
  set_of_itv `[x, y[ = [set x] `|` set_of_itv `]x, y[.
Proof.
move=> xy; rewrite !set_of_itvE predeqE => r; split=> [/andP[]|].
  by rewrite le_eqVlt => /orP[/eqP->|xr ry]; [left|right; rewrite xr].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma closed_closed_set1l x y : x <= y ->
  set_of_itv `[x, y] = [set x] `|` set_of_itv `]x, y].
Proof.
move=> ab; rewrite !set_of_itvE predeqE => r; split=> [/andP[]|].
  by rewrite le_eqVlt => /orP[/eqP->|xr ry]; [left|right; rewrite xr].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma closed_closed_set1r x y : x <= y ->
  set_of_itv `[x, y] = set_of_itv `[x, y[ `|` [set y].
Proof.
move=> xy; rewrite !set_of_itvE predeqE => r; split=> [/andP[xr]|].
  by rewrite le_eqVlt => /orP[/eqP->|ry]; [right|left; rewrite xr].
by case=> [/andP[-> /ltW //]|->]; rewrite lexx xy.
Qed.

Lemma closed_infty_set1 x : set_of_itv `[x, +oo[ = [set x] `|` set_of_itv `]x, +oo[.
Proof.
rewrite predeqE => r; rewrite !set_of_itvE; split; last by case=> [->//|/ltW].
by rewrite le_eqVlt => /orP[/eqP ->|?]; [left|right].
Qed.

Lemma infty_closed_set1 x : set_of_itv `]-oo, x] = set_of_itv `]-oo, x[ `|` [set x].
Proof.
rewrite predeqE => r; rewrite !set_of_itvE; split => [|[/ltW //|-> //=]].
by rewrite le_eqVlt => /orP[/eqP ->|xr]; [right|left].
Qed.

End punctured_interval.

End set_of_itv.
Arguments set_of_itv {R}.

Lemma set_of_itvC_minfty_BSide (R : realDomainType) b (r : R) :
  ~` set_of_itv (Interval -oo%O (BSide b r)) = set_of_itv (Interval (BSide b r) +oo%O).
Proof.
case: b; rewrite !set_of_itvE predeqE => x.
by split; rewrite leNgt => /negP.
by split; rewrite ltNge => /negP.
Qed.

Lemma set_of_itvC_BSide_pinfty (R : realDomainType) b (r : R) :
  ~` set_of_itv (Interval (BSide b r) +oo%O) = set_of_itv (Interval -oo%O (BSide b r)).
Proof. by rewrite -set_of_itvC_minfty_BSide setCK. Qed.

Let set_of_itvC_BSide_BSide (R : realDomainType) a b (x y : R) :
  ~` set_of_itv (Interval (BSide a x) (BSide b y)) =
  set_of_itv (Interval -oo%O (BSide a x)) `|` set_of_itv (Interval (BSide b y) +oo%O).
Proof.
move: a b => [] []; rewrite !set_of_itvE predeqE => r; split.
by move/negP; rewrite negb_and -ltNge -leNgt => /orP.
by move/orP; rewrite leNgt (ltNge r x) -negb_and => /negP.
by move/negP; rewrite negb_and -2!ltNge => /orP.
by move/orP; rewrite 2!ltNge -negb_and => /negP.
by move/negP; rewrite negb_and -2!leNgt => /orP.
by move/orP; rewrite 2!leNgt -negb_and => /negP.
by move/negP; rewrite negb_and -leNgt -ltNge => /orP.
by move/orP; rewrite leNgt (ltNge y r) -negb_and => /negP.
Qed.

Lemma set_of_itvC_Interval (R : realDomainType) (a b : itv_bound R) :
  ~` set_of_itv (Interval a b) =
  set_of_itv (Interval -oo%O a) `|` set_of_itv (Interval b +oo%O).
Proof.
move: a b => [[] a|[]] [[] b|[]].
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itvC_BSide_BSide.
by rewrite !set_of_itvE setUT set_of_itv_empty_set0 // setC0.
by rewrite set_of_itvC_BSide_pinfty !set_of_itvE setU0.
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itv_empty_set0 // setC0 !set_of_itvE setUT.
by rewrite set_of_itvC_BSide_pinfty !set_of_itvE setU0.
by rewrite set_of_itvC_minfty_BSide !set_of_itvE set0U.
by rewrite set_of_itvC_minfty_BSide !set_of_itvE set0U.
by rewrite set_of_itvE setC0 set0U set_of_itvE.
by rewrite !set_of_itvE setCT set0U.
by rewrite !set_of_itvE setTU set_of_itv_empty_set0 // setC0.
by rewrite !set_of_itvE setTU set_of_itv_empty_set0 // setC0.
by rewrite set_of_itv_empty_set0 // setC0 !set_of_itvE setTU.
by rewrite !set_of_itvE setC0 setU0.
Qed.

Definition set_of_itvC := (set_of_itvC_minfty_BSide,
                           set_of_itvC_BSide_pinfty,
                           set_of_itvC_Interval).

Lemma itv_meetE (R : realDomainType) (i j : interval R) :
  set_of_itv (itv_meet i j) = set_of_itv i `&` set_of_itv j.
Proof.
rewrite eqEsubset; split => x; move: i j => [i1 i2] [j1 j2].
- move/set_of_itv_mem => /=.
  rewrite itv_boundlr joinEtotal meetEtotal le_maxl le_minr => /andP[/andP[i1x j1x] /andP[xi2 xj2]].
  by split; apply/set_of_itv_mem; rewrite itv_boundlr ?i1x ?xi2 // j1x xj2.
- case => /set_of_itv_mem; rewrite itv_boundlr => /andP[i1x xi2] /set_of_itv_mem.
  rewrite itv_boundlr => /andP[j1x xj2].
  by apply/set_of_itv_mem; rewrite itv_boundlr joinEtotal meetEtotal le_maxl le_minr i1x xi2 j1x.
Qed.

Section set_of_itv_numFieldType.
Variable R : numFieldType.

Lemma set_of_itv_empty_eq0 (a b : itv_bound R) :
  (set_of_itv (Interval a b) == set0) = ~~ (a < b)%O.
Proof.
apply/idP/idP => [/eqP|]; last first.
  by move/set_of_itv_empty_set0 => ->.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite !set_of_itvE.
- by rewrite predeqE => /(_ a); rewrite lexx /= => -[] /negP.
- by rewrite predeqE => /(_ a); rewrite lexx /= => -[] /negP.
- by rewrite predeqE => /(_ a); rewrite lexx /= => -[] /negP.
- move=> i0; apply/negP => ab; move: i0.
  rewrite predeqE => /(_ ((a + b) / 2)); rewrite !midf_lt //= => -[+ _].
  exact.
- by rewrite predeqE => /(_ b); rewrite lexx andbT /= => -[] /negP.
- by rewrite predeqE => /(_ (a + 1)); rewrite ltr_addl ltr01 => -[] /negP.
- rewrite predeqE => /(_ (b - 1)); rewrite ltr_subl_addl ltr_addr ltr01.
  by case => /negP.
- by rewrite predeqE => /(_ b); rewrite lexx => -[] /negP.
- by rewrite predeqE => /(_ 0) [+ _]; rewrite falseE; apply.
Qed.

Lemma set_of_itv_empty_pred0 (i : interval R) :
  set_of_itv i = set0 <-> i =i pred0.
Proof.
move: i => [a b]; split.
  by move/eqP; rewrite set_of_itv_empty_eq0 => /itv_ge.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite ?set_of_itvE.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => //.
  by rewrite /set_of_itv /mkset in_itv /= andbF.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => //.
  by rewrite /set_of_itv /mkset in_itv /= andbF.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move/(_ 0); rewrite in_itv /= inE.
- by move=> ?; rewrite predeqE.
- by move=> ?; rewrite predeqE.
- by move=> ?; rewrite predeqE.
- by move=> ?; rewrite predeqE.
Qed.

End set_of_itv_numFieldType.

Section itv_bound_lteE.
Variable R : numDomainType.

Lemma BLeft_ltE (x y : R) : (BLeft x < BLeft y)%O = (x < y).
Proof. by []. Qed.
Lemma BLeft_BRight_ltE (x y : R) : (BLeft x < BRight y)%O = (x <= y).
Proof. by []. Qed.
Lemma BRight_BSide_ltE (x y : R) b : (BRight x < BSide b y)%O = (x < y).
Proof. by case: b. Qed.
Lemma BRight_BSide_leE (x y : R) b : (BLeft x <= BSide b y)%O = (x <= y).
Proof. by case: b. Qed.
Lemma BRight_BLeft_leE (x y : R) : (BRight x <= BLeft y)%O = (x < y).
Proof. by []. Qed.
Lemma BRight_leE (x y : R) : (BRight x <= BRight y)%O = (x <= y).
Proof. by []. Qed.

Definition itv_bound_lteE := (BLeft_ltE, BLeft_BRight_ltE, BRight_BSide_ltE,
  BRight_BSide_leE, BRight_BLeft_leE, BRight_leE).

End itv_bound_lteE.

Section interval_has_bound.
Variable R : numDomainType.

Lemma has_lbound_bounded (x y : R) (b0 b1 : bool) :
  has_lbound (set_of_itv (Interval (BSide b0 x) (BSide b1 y))).
Proof. by case: b0; exists x => r /andP[]; rewrite itv_bound_lteE // => /ltW. Qed.

Lemma has_ubound_bounded (x y : R) (b0 b1 : bool) :
  has_ubound (set_of_itv (Interval (BSide b0 x) (BSide b1 y))).
Proof. by case: b1; exists y => r /andP[]; rewrite itv_bound_lteE // => _ /ltW. Qed.

Lemma has_lbound_infty (x : R) b : has_lbound (set_of_itv (Interval (BSide b x) +oo%O)).
Proof. by case: b; exists x => y; rewrite !set_of_itvE // => /ltW. Qed.

Lemma has_ubound_infty (x : R) b : has_ubound (set_of_itv (Interval -oo%O (BSide b x))).
Proof. by case: b; exists x => y // /ltW. Qed.

End interval_has_bound.

Hint Extern 0 (has_lbound (set_of_itv _)) =>
  solve[apply: has_lbound_bounded | apply: has_lbound_infty] : core.
Hint Extern 0 (has_ubound (set_of_itv _)) =>
  solve[apply: has_ubound_bounded | apply: has_ubound_infty] : core.

Section interval_hasNbound.

Lemma hasNubound_setT (R : realDomainType) : ~ has_ubound (@set_of_itv R `]-oo, +oo[).
Proof.
case=> x; rewrite /ubound => /(_ (x + 1) erefl).
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

Lemma hasNlbound_setT (R : realDomainType) : ~ has_lbound (@set_of_itv R `]-oo, +oo[).
Proof.
case=> x; rewrite /ubound => /(_ (x - 1) erefl).
by apply/negP; rewrite -ltNge ltr_subl_addr ltr_addl.
Qed.

Variable R : realType.

Lemma hasNlbound_minfty (r : R) b : ~ has_lbound (set_of_itv (Interval -oo%O (BSide b r))).
Proof.
suff : ~ has_lbound (set_of_itv `]-oo, r[).
  by case: b => //; apply/ssrbool.contra_not/subset_has_lbound => x /ltW.
apply/has_lbPn => x; exists (minr (r - 1) (x - 1)).
by rewrite !set_of_itvE lt_minl ltr_subl_addr ltr_addl ltr01.
by rewrite lt_minl orbC ltr_subl_addr ltr_addl ltr01.
Qed.

Lemma hasNubound_pinfty (r : R) b : ~ has_ubound (set_of_itv (Interval (BSide b r) +oo%O)).
Proof.
suff : ~ has_ubound (set_of_itv `]r, +oo[).
  case: b => //; apply/ssrbool.contra_not/subset_has_ubound => x.
  by rewrite !set_of_itvE => /ltW.
apply/has_ubPn => x; rewrite !set_of_itvE; exists (maxr (r + 1) (x + 1));
by rewrite ?in_itv /= ?andbT lt_maxr ltr_addl ltr01 // orbT.
Qed.

End interval_hasNbound.

Hint Extern 0 (~ has_lbound _) =>
  solve[apply: hasNlbound_setT | apply: hasNlbound_minfty] : core.
Hint Extern 0 (~ has_ubound _) =>
  solve[apply: hasNubound_setT | apply: hasNubound_pinfty] : core.

Section interval_has.
Variable R : realType.
Implicit Types x : R.

Lemma has_sup1 x : has_sup [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma has_inf1 x : has_inf [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma has_sup_half x b (i : itv_bound R) : (i < BSide b x)%O ->
  has_sup (set_of_itv (Interval i (BSide b x))).
Proof.
move: b i => [] [[]y|[]]; rewrite ?itv_bound_lteE => xy; try
  (split => //; exists ((x + y) / 2); rewrite !set_of_itvE addrC !(midf_le,midf_lt) //; exact: ltW) ||
  (by split => //; exists (x - 1); rewrite !set_of_itvE !(ltr_subl_addr,ler_subl_addr, ltr_addl,ler_addl)).
Qed.

Lemma has_inf_half x b (i : itv_bound R) : (BSide b x < i)%O ->
  has_inf (set_of_itv (Interval (BSide b x) i)).
Proof.
move: b i => [] [[]y|[]]; rewrite ?itv_bound_lteE => xy; try
  (split => //; exists ((x + y) / 2); rewrite !set_of_itvE !(midf_le,midf_lt) //; exact: ltW) ||
  (by split => //; exists (x + 1); rewrite !set_of_itvE !(ltr_addl,ler_addl)).
Qed.

End interval_has.

Hint Extern 0 (has_sup _) => solve[apply: has_sup1 | exact: has_sup_half] : core.
Hint Extern 0 (has_inf _) => solve[apply: has_inf1 | exact: has_inf_half]: core.

Lemma minus_open_pinfty (R : numDomainType) (y : R) b :
  -%R @` set_of_itv (Interval (BSide b y) +oo%O) =
  set_of_itv (Interval -oo%O (BSide (negb b) (- y))).
Proof.
rewrite predeqE /image => /= r; split=> [[x ax <-]|ra].
  case: b ax; [by rewrite !set_of_itvE ler_oppl opprK |
  by rewrite !set_of_itvE ltr_oppl opprK].
exists (- r); rewrite ?opprK //.
case: b ra; [by rewrite !set_of_itvE ler_oppr |
  by rewrite !set_of_itvE ltr_oppr].
Qed.

Lemma minus_open_open (R : numDomainType) (x y : R) :
  -%R @` set_of_itv (Interval (BRight x) (BLeft y)) =
  set_of_itv (Interval (BRight (- y)) (BLeft (- x))).
Proof.
rewrite predeqE /image => /= r; split=> [[u /andP[xu uy <-]]|/andP[yr rx]].
rewrite !itv_bound_lteE in xu, uy.
by rewrite !set_of_itvE ltr_oppl opprK uy /= ltr_oppl opprK.
exists (- r); last by rewrite opprK.
rewrite !itv_bound_lteE in yr, rx.
by rewrite !set_of_itvE ltr_oppr rx /= ltr_oppl.
Qed.

Section interval_sup_inf.
Variable R : realType.
Implicit Types x y : R.

Lemma sup_minfty x b : sup (set_of_itv (Interval -oo%O (BSide b x))) = x.
Proof.
case: b; last first.
  by rewrite infty_closed_set1 sup_setU ?sup1 // => ? ? ? ->; exact/ltW.
set s := sup _; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub; last by move=> ? /ltW.
  by exists (x - 1); rewrite !set_of_itvE ltr_subl_addr ltr_addl.
- rewrite leNgt; apply/negP => sx; pose p := (s + x) / 2.
  suff [/andP[?]]: (p < x) && (s < p) by apply/negP; rewrite -leNgt sup_ub.
  by rewrite !midf_lt.
Qed.

Lemma inf_pinfty x b : inf (set_of_itv (Interval (BSide b x) +oo%O)) = x.
Proof.
case: b; last by rewrite /inf minus_open_pinfty sup_minfty opprK.
by rewrite closed_infty_set1 inf_setU ?inf1 // => _ b ->; rewrite !set_of_itvE => /ltW.
Qed.

Let sup_open_side x y b : x < y ->
  sup (set_of_itv (Interval (BRight x) (BSide b y))) = y.
Proof.
case: b => xy; last first.
  by rewrite open_closed_set1 // sup_setU ?sup1 // => ? ? /andP[? /ltW ?] ->.
set B := set_of_itv _; set A := set_of_itv `]-oo, x].
rewrite -(@sup_setU _ A B) //.
- rewrite -(sup_minfty y true); congr sup.
  rewrite predeqE => u; split=> [[|/andP[]//]|yu].
  by rewrite /A !set_of_itvE => /le_lt_trans; apply.
  by have [xu|ux] := ltP x u; [right; rewrite /B !set_of_itvE xu| left].
- by move=> u v; rewrite /A /B => ? /andP[xv _]; rewrite (le_trans _ (ltW xv)).
Qed.

Lemma sup_bounded x y a b : x < y ->
  sup (set_of_itv (Interval (BSide a x) (BSide b y))) = y.
Proof.
case: a => xy; last exact: sup_open_side.
case: b.
  by rewrite closed_open_set1 // sup_setU ?sup_open_side // => ? ? -> /andP[/ltW].
rewrite closed_closed_set1r; last exact/ltW.
by rewrite  sup_setU ?sup1// => ? ? /andP[_ /ltW ? ->].
Qed.

Lemma sup_closed_closed x y : x <= y -> sup (set_of_itv `[x, y]) = y.
Proof.
by move=> xy; rewrite closed_closed_set1r // sup_setU ?sup1 // => ? ? /andP[_ /ltW ? ->].
Qed.

Let inf_side_open x y b : x < y ->
  inf (set_of_itv (Interval (BSide b x) (BLeft y))) = x.
Proof.
case: b => xy.
  by rewrite closed_open_set1// inf_setU ?inf1 // => _ ? -> /andP[/ltW].
by rewrite /inf minus_open_open sup_open_side ?opprK // ltr_oppl opprK.
Qed.

Lemma inf_bounded x y a b : x < y ->
  inf (set_of_itv (Interval (BSide a x) (BSide b y))) = x.
Proof.
case: b => xy; first exact: inf_side_open.
case: a.
  rewrite closed_closed_set1l; last exact: ltW.
  by rewrite inf_setU ?inf1 // => ? ? -> /andP[/ltW].
by rewrite open_closed_set1 // inf_setU ?inf_side_open // => ? ? /andP[? /ltW ?] ->.
Qed.

Lemma inf_closed_closed x y : x <= y -> inf (set_of_itv `[x, y]) = x.
Proof.
by move=> ?; rewrite closed_closed_set1l // inf_setU ?inf1 // => ? ? -> /andP[/ltW].
Qed.

End interval_sup_inf.

Section set_of_itv_cancel.
Variable R : realType.

Lemma set_of_itvK :
  {in [pred X : interval R | ~~ `[< X =i pred0 >] ], cancel set_of_itv (@Rhull _)}.
Proof.
move=> [[[] i1|[]] [[] i2|[]]] /asboolP; rewrite /Rhull //=.
- move/set_of_itv_empty_pred0/eqP; rewrite set_of_itv_empty_eq0 negbK itv_bound_lteE => i12.
  rewrite asboolT //= inf_bounded // {1}set_of_itvE lexx i12 asboolT //.
  by rewrite asboolT // sup_bounded // {1}set_of_itvE /= ltW // ltxx asboolF.
- move/set_of_itv_empty_pred0/eqP; rewrite set_of_itv_empty_eq0 negbK itv_bound_lteE => X0.
  rewrite asboolT // inf_closed_closed // {1}set_of_itvE  lexx X0 asboolT //.
  by rewrite asboolT // sup_closed_closed // {1}set_of_itvE X0 lexx asboolT.
- by have := @itv_ge _ _ (BLeft i1) -oo%O erefl.
- by move=> _; rewrite asboolT // {1}set_of_itvE inf_pinfty lexx asboolT // asboolF.
- move/set_of_itv_empty_pred0/eqP; rewrite set_of_itv_empty_eq0 negbK itv_bound_lteE => i12.
  rewrite asboolT // inf_bounded // {1}set_of_itvE ltxx asboolF // asboolT //.
  by rewrite sup_bounded // {1}set_of_itvE ltxx andbF asboolF.
- move/set_of_itv_empty_pred0/eqP; rewrite set_of_itv_empty_eq0 negbK itv_bound_lteE => i12.
  rewrite asboolT // inf_bounded // {1}set_of_itvE ltxx asboolF // asboolT //.
  by rewrite sup_bounded // {1}set_of_itvE i12 lexx asboolT.
- by have := @itv_ge _ _ (BRight i1) -oo%O erefl.
- by move=> _; rewrite asboolT // inf_pinfty {1}set_of_itvE ltxx asboolF // asboolF.
- by move=> _; rewrite asboolF // asboolT // {1}set_of_itvE sup_minfty ltxx asboolF.
- by move=> _; rewrite asboolF // asboolT // {1}set_of_itvE sup_minfty lexx asboolT.
- by have := @itv_ge _ _ -oo%O -oo%O erefl.
- by move=> _; rewrite asboolF // asboolF.
- by have := @itv_ge _ _ +oo%O (BLeft i2) erefl.
- by have := @itv_ge _ _ +oo%O (BRight i2) erefl.
- by have := @itv_ge _ _ +oo%O -oo%O erefl.
- by have := @itv_ge _ _ +oo%O +oo%O erefl.
Qed.

Lemma RhullK :
  {in [pred X : set R | `[< is_interval X >]], cancel (@Rhull _) set_of_itv}.
Proof.
move=> X /asboolP iX; rewrite /Rhull /set_of_itv /mkset /= predeqE => r.
case: ifPn => /asboolP bX; last first.
  case: ifPn => /asboolP aX; last by rewrite (interval_unbounded_setT _ bX aX).
  rewrite in_itv /= negbK; have [/asboolP XsupX /=|/asboolPn XsupX /=] := boolP `[< _ >].
    split => [|Xr].
      rewrite le_eqVlt => /orP[/eqP -> //|rX].
      move/has_lbPn : bX => /(_ r)[y Xy yr].
      by move: (iX _ _ Xy XsupX); apply; rewrite yr.
    by rewrite /mkset sup_ub //; exact/asboolP.
  split => [rX|Xr]; last exact: sup_ub_strict.
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_left_unbounded_interior.
case: ifPn => /asboolP uX.
  have [/asboolP XinfX | /asboolPn XinfX ] := boolP `[< _ >].
    rewrite in_itv /= negbK; have [/asboolP XsupX /=|/asboolP XsupX /=] := boolP `[< _ >].
      split=> [|Xr]; last first.
        by rewrite /mkset sup_ub // andbT inf_lb.
      move => /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXr].
      rewrite le_eqVlt => /orP[/eqP -> //|rsupX].
      apply: (@interior_subset [topologicalType of R^o]).
      by rewrite interval_bounded_interior //; rewrite /mkset infXr.
    split => [|Xr].
      rewrite /mkset => /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXr rsupX].
      apply: (@interior_subset [topologicalType of R^o]).
      by rewrite interval_bounded_interior //; rewrite /mkset infXr.
    by rewrite /mkset inf_lb //= sup_ub_strict.
  have [/asboolP XsupX /=|/asboolP XsupX /=] := boolP `[< _ >].
    rewrite in_itv /=; split=> [|Xr]; last first.
      by rewrite inf_lb_strict // sup_ub.
    move=> /andP[infXr]; rewrite le_eqVlt => /orP[/eqP -> //|rsupX].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior //; rewrite /mkset infXr.
  rewrite in_itv /=; split=> [|Xr]; last first.
    by rewrite inf_lb_strict // sup_ub_strict.
  move => /andP[infXr rsupX].
  apply: (@interior_subset [topologicalType of R^o]).
  by rewrite interval_bounded_interior //; rewrite /mkset infXr.
rewrite in_itv /=; have [/asboolP XinfX /=| /asboolPn XinfX /=] := boolP `[< _ >].
  rewrite andbT; split => [|Xr]; last exact: inf_lb.
  rewrite le_eqVlt => /orP[/eqP <- //|infXr].
  move/has_ubPn : uX => /(_ r)[y Xy yr].
  by move: (iX _ _ XinfX Xy); apply; rewrite infXr.
rewrite andbT.
split=> [infXr|Xr]; last exact: inf_lb_strict.
apply: (@interior_subset [topologicalType of R^o]).
by rewrite interval_right_unbounded_interior.
Qed.

End set_of_itv_cancel.

(* finite union of intervals *)
Definition fint (R : numDomainType) : Type := {fset (interval R)}.
Definition ufint (R : numDomainType) (x : seq (interval R)) : set R :=
  \bigcup_(i in [set j | j \in x]) (set_of_itv i).

Lemma mem_ufint (R : numDomainType) (s1 s2 : seq (interval R)) :
  s1 =i s2 -> ufint s1 = ufint s2.
Proof.
move=> s12; rewrite eqEsubset; split => x [i]; rewrite /mkset => + ix.
by rewrite s12 => ?; exists i.
by rewrite -s12 => ?; exists i.
Qed.

Lemma ufint_filter_neq0 (R : numDomainType) (s : seq (interval R)) :
  ufint [seq x <- s | set_of_itv x != set0] = ufint s.
Proof.
elim: s => // h t ih /=; case: ifPn => [h0|/negPn/eqP h0].
  by rewrite {1}/ufint bigcup_cons -/(ufint _) ih {2}/ufint bigcup_cons.
by rewrite ih {2}/ufint bigcup_cons h0 set0U.
Qed.

Definition bnd1 {R : numDomainType} (x : interval R) :=
  let: Interval i _ := x in i.
Definition bnd2 {R : numDomainType} (x : interval R) :=
  let: Interval _ j := x in j.

Section itv_cplt.
Variable R : realType.

Definition itv_cplt (s : seq (interval R)) : seq (interval R) :=
  let a' := -oo%O :: map bnd2 s in
  let b' := rcons (map bnd1 s) +oo%O in
  map (uncurry (@Interval _)) (zip a' b').

Lemma itv_cpltE1 (s : seq (interval R)) : ~` ufint s `<=` ufint (itv_cplt s).
Proof.
elim: s => [x _|[a1 b1] t ih x].
  by rewrite /itv_cplt /= /ufint bigcup_cons1 set_of_itvE.
rewrite {1}/ufint bigcup_cons -/(ufint _) setCU => -[] x_notin_h /ih {}ih.
set a := map bnd1 (Interval a1 b1 :: t).
set b := map bnd2 (Interval a1 b1 :: t).
rewrite (_ : itv_cplt _ = Interval -oo%O a1 ::
  map (uncurry (@Interval _)) (zip b (rcons (behead a) +oo%O))) //.
rewrite /ufint bigcup_cons.
have : (set_of_itv (Interval -oo%O a1) `|` set_of_itv (Interval b1 +oo%O)) x.
  by rewrite set_of_itvC in x_notin_h.
case=> [xa1|/set_of_itv_mem xb1]; [by left|right].
have {ih}[j] : ufint (map (uncurry (@Interval _))
  (zip (-oo%O :: behead b) (rcons (behead a) +oo%O))) x by [].
rewrite {1}/mkset => + /set_of_itv_mem jx.
rewrite {}/b {}/a.
move: t => [|[a2 b2] t /=]; first by rewrite bigcup_cons1.
rewrite inE => /orP[/eqP jb2|jb2].
  exists (Interval b1 a2); first by rewrite /mkset inE eqxx.
  apply/set_of_itv_mem; rewrite itv_splitI xb1 /=.
  by move: jx; rewrite jb2 => /set_of_itv_mem.
by exists j => //; rewrite /mkset inE jb2 orbT.
Qed.

Lemma itv_cpltE2 (s : seq (interval R)) :
  path.sorted <=%O (map bnd2 s) /\ path.sorted <=%O (map bnd1 s) ->
  ufint (itv_cplt s) `<=` ~` ufint s.
Proof.
set a := map bnd1 s.
set b := map bnd2 s.
move=> [sorted_b sorted_a] x.
rewrite {1}/ufint => -[/= j] /mapP[[b' a']] /(nthP (+oo%O, -oo%O)) => -[k'].
rewrite size_zip /= size_rcons 2!size_map minnn ltnS => k's.
rewrite nth_zip; last by rewrite size_rcons /= !size_map.
move=> -[kb' ka'] jba'.
move/set_of_itv_mem => xj -[] i si /set_of_itv_mem xi.
have [k [ks ik]] : exists k, (k < size s)%N /\
    i = Interval (nth -oo%O a k) (nth +oo%O b k).
  move/(nthP 0%O) : si => [k ks ki].
  exists k; split => //.
  by rewrite /a /b !(nth_map 0%O) // ki; case: i {xi ki}.
move: xi; rewrite ik itv_boundlr => /andP[akx xbk].
move: xj; rewrite jba' itv_boundlr => /andP[b'x xa'].
rewrite -/a in ka'.
rewrite -/b in kb'.
have [kk'|k'k] := leP k k'.
  case: k' => [|k'] in k's ka' kb' kk' *.
    move: kk'; rewrite lex0 => /eqP k0.
    rewrite {k's ks} /= in kb' jba' b'x xa'.
    rewrite -{}kb' {b'x b'} in jba'.
    rewrite -ka' /= in xa'.
    rewrite k0 /a /= in akx.
    rewrite {jba' k0 ka' xbk ik k sorted_a sorted_b a' b j}.
    rewrite {}/a in xa'.
    case: s => [//|s0 s1] in si akx xa' *.
    have := le_trans xa' akx.
    by rewrite itv_bound_lteE ltxx.
  rewrite /= in kb'.
  have : (k' <= (size s).-1)%N by move: k's; clear -si; case: s si.
  rewrite leq_eqVlt => /orP[/eqP k's1|k's1].
    move: ka'; rewrite nth_rcons size_map k's1 prednK //; last first.
      by move: k's; clear -si; case: s si.
    rewrite ltnn eqxx => ka'.
    have : (BRight x <= BLeft x)%O.
      rewrite (le_trans xbk) // (le_trans _ b'x) //= -kb'.
      apply: (path.sorted_leq_nth le_trans) => //.
      by rewrite inE /b size_map.
      by rewrite inE size_map.
      by rewrite -ltnS k's1 prednK // (leq_ltn_trans _ ks).
    by rewrite itv_bound_lteE ltxx.
  move: kk'; rewrite le_eqVlt => /orP[kk'|kk'].
    have : (BRight x <= BLeft x)%O.
      rewrite (@le_trans _ _ (nth -oo%O a k)) // (le_trans xa') // -ka'.
      by rewrite nth_rcons size_map -(eqP kk') ks.
    by rewrite itv_bound_lteE ltxx.
  have : (BRight x <= BLeft x)%O.
    rewrite (@le_trans _ _ (nth +oo%O b k)) // (le_trans _ b'x) //= -kb'.
    apply: (path.sorted_leq_nth le_trans) => //.
    by rewrite inE /b size_map.
    by rewrite inE size_map.
  by rewrite itv_bound_lteE ltxx.
have : (BRight x <= BLeft x)%O.
  rewrite (le_trans xa') //= (le_trans _ akx) //.
  rewrite -ka' nth_rcons size_map (ltn_trans k'k ks).
  apply: (path.sorted_leq_nth le_trans) => //.
  by rewrite inE size_map (ltn_trans k'k).
  by rewrite inE size_map.
  by rewrite ltnW.
by rewrite itv_bound_lteE ltxx.
Qed.

Lemma itv_cpltE (s : seq (interval R)) :
  path.sorted <=%O (map bnd2 s) /\ path.sorted <=%O (map bnd1 s) ->
  ufint (itv_cplt s) = ~` ufint s.
Proof. by rewrite eqEsubset; split; [exact: itv_cpltE2 | exact: itv_cpltE1]. Qed.

End itv_cplt.

Section itv_diff.
Variable R : realType.

(* assumes ~ j <= i *)
Definition itv_diff (i j : interval R) : interval R :=
  if set_of_itv (itv_meet i j) == set0 then i
  else
    let: Interval i1 i2 := i in let: Interval j1 j2 := j in
    if (j1 <= i1)%O then
      (if (j2 <= i2)%O then Interval j2 i2 else 0%O)
    else
      (if (j2 <= i2)%O then 0%O else Interval i1 j1).

Lemma itv_diffE (i j : interval R) : ~ {subset j <= i} ->
  set_of_itv (itv_diff i j) = set_of_itv i `\` set_of_itv j.
Proof.
move=> ji.
rewrite /itv_diff; case: ifPn => ij0.
  by apply/esym/setDidPl; rewrite -itv_meetE (eqP ij0).
move: i j => [i1 i2] [j1 j2] /= in ji ij0 *.
have [ji1|ji1] := leP j1 i1.
- have [ji2|ji2] := leP j2 i2.
  + rewrite eqEsubset; split => x.
    * move/set_of_itv_mem; rewrite itv_boundlr => /andP[j2x xi2]; split.
        apply/set_of_itv_mem.
        rewrite itv_boundlr xi2 andbT (@le_trans _ _ j2) // leNgt; apply/negP => j2j1.
        move/negP : ij0; apply; apply/eqP.
        rewrite joinEtotal meetEtotal maxElt ltNge ji1 /= minElt ltNge ji2 /=.
        by rewrite set_of_itv_empty_set0 // -leNgt ltW.
      move/set_of_itv_mem; rewrite itv_boundlr => /andP[j1x xj2].
      by have := le_trans xj2 j2x; rewrite itv_bound_lteE ltxx.
    * move=> -[/set_of_itv_mem]; rewrite itv_boundlr => /andP[i1x xi2 ix].
      apply/set_of_itv_mem; rewrite itv_boundlr xi2 andbT.
      rewrite leNgt; apply/negP => xj2.
      apply: ix.
      apply/set_of_itv_mem.
      by rewrite itv_boundlr (le_trans ji1).
  + rewrite set_of_itv_empty_set0 //.
    apply/esym.
    rewrite setD_eq0 => x.
    move/set_of_itv_mem; rewrite itv_boundlr => /andP[i1x xi2].
    apply/set_of_itv_mem; rewrite itv_boundlr (le_trans ji1) //=.
    by rewrite (le_trans xi2) // ltW.
- have [ji2|ji2] := leP j2 i2.
    exfalso.
    apply: ji => x; rewrite 2!itv_boundlr => /andP[j1x xj2].
    by rewrite (le_trans xj2 ji2) andbT (le_trans _ j1x) // ltW.
  rewrite eqEsubset; split => x.
  * move/set_of_itv_mem; rewrite itv_boundlr => /andP[i1x xj1]; split.
      apply/set_of_itv_mem; rewrite itv_boundlr i1x /= leNgt; apply/negP => i2j1.
      move/eqP : ij0; apply.
      rewrite set_of_itv_empty_set0 // meetEtotal minElt ji2 joinEtotal maxElt.
      by rewrite ji1 -leNgt (le_trans _ xj1) // (le_trans (ltW i2j1)).
    move/set_of_itv_mem; rewrite itv_boundlr => /andP[j1x xj2].
    by have := le_trans xj1 j1x; rewrite itv_bound_lteE ltxx.
  * move=> -[/set_of_itv_mem]; rewrite itv_boundlr => /andP[i1x xi2] /set_of_itv_mem.
    rewrite itv_boundlr => /negP; rewrite negb_and -2!ltNge => /orP[xj1|j2x].
      by apply/set_of_itv_mem; rewrite itv_boundlr i1x.
    by have := lt_trans (le_lt_trans xi2 ji2) j2x; rewrite ltxx.
Qed.

Lemma itv_diffxx (a : interval R) : set_of_itv (itv_diff a a) = set0.
Proof.
have [[a0 aa0]|/set0P/negP/negPn/eqP a0] := pselect (set_of_itv a !=set0).
  rewrite /itv_diff ifF; last first.
    by rewrite itv_meetE; apply/negbTE/set0P; exists a0.
  case: a aa0 => [a1 a2] aa0.
  by rewrite !lexx set_of_itv_empty_set0 // ltxx.
by rewrite /itv_diff ifT // itv_meetE a0 set0I.
Qed.

End itv_diff.

Definition disjoint_itv {R : numDomainType} : rel (interval R) :=
  fun a b => set_of_itv a `&` set_of_itv b == set0.

Lemma lt_disjoint (R : numDomainType) (i j : interval R) :
  (forall x y, x \in i -> y \in j -> x < y) -> disjoint_itv i j.
Proof.
move=> ij; apply/eqP; rewrite predeqE => x; split => // -[].
move/set_of_itv_mem => xi /set_of_itv_mem xj.
by have := ij _ _ xi xj; rewrite ltxx.
Qed.

Lemma path_disjoint_setT_eq0 (R : numDomainType) (t : seq (interval R)) :
  (forall i, i \in t -> set_of_itv i !=set0) ->
  path.path disjoint_itv `]-oo, +oo[ t ->
  t = [::].
Proof.
case: t => // h t /= /(_ h); rewrite mem_head => /(_ erefl).
move=> [x /set_of_itv_mem xh] /andP[hoo _]; exfalso.
by move: hoo; rewrite /disjoint_itv; apply/negP/set0P; exists x.
Qed.

Section lt_itv.
Variable R : realType.

Definition lt_itv (i j : interval R) := match i, j with
  | Interval i1 i2, Interval j1 j2 =>
    if (i1 < j1)%O then true else if i1 == j1 then (i2 < j2)%O else false
  end.

Lemma lt_trans_itv : transitive lt_itv.
Proof.
move=> [k1 k2] [i1 i2] [j1 j2]; rewrite /lt_itv.
case: (ltgtP i1 k1) => // [ik1 _| <-{k1} ik2].
  case: (ltgtP k1 j1) => // [kj1 _|kj1]; last by rewrite -kj1 ik1.
  by rewrite (lt_trans ik1).
by case: (ltgtP i1 j1) => // _; apply: lt_trans.
Qed.

Definition le_itv i j := (i == j) || (lt_itv i j).

Lemma total_le_itv : total le_itv.
Proof.
move=> [i1 i2] [j1 j2]; rewrite /le_itv /=.
case/boolP : (_ == _) => ij //=.
case: (ltgtP i1 j1) => //=; rewrite ?orbT // => ij1.
rewrite eq_sym (negbTE ij) /= -neq_lt; apply/negP => /eqP ij2.
by exfalso; move/negP : ij; apply; rewrite ij1 ij2.
Qed.

Lemma le_trans_itv : transitive le_itv.
Proof.
move=> y x z.
rewrite /le_itv => /orP[/eqP -> //|xy] /orP[/eqP <-|yz]; first by rewrite orbC xy.
by rewrite (lt_trans_itv xy yz) orbT.
Qed.

Lemma le_lt_trans_itv y x z : le_itv x y -> lt_itv y z -> lt_itv x z.
Proof. by rewrite /le_itv => /orP[/eqP ->//|]; exact: lt_trans_itv. Qed.

Lemma lt_le_trans_itv y x z : lt_itv x y -> le_itv y z -> lt_itv x z.
Proof. by move=> xy; rewrite /le_itv => /orP[/eqP <- //|]; exact: lt_trans_itv. Qed.

Lemma ltW_itv x y : lt_itv x y -> le_itv x y.
Proof. by rewrite /le_itv => ->; rewrite orbT. Qed.

Lemma lt_itvxx a : lt_itv a a = false.
Proof. by case: a => ? ? /=; rewrite ltxx eqxx ltxx. Qed.

Let lt_itv_lt (a b : interval R) : lt_itv a b ->
  set_of_itv a `&` set_of_itv b = set0 ->
  forall x y, x \in a -> y \in b -> x < y.
Proof.
move: a b => [i1 i2] [j1 j2].
rewrite /lt_itv; case: (ltgtP i1 j1) => // [ij1 _|].
- rewrite -itv_meetE => /set_of_itv_empty_pred0 ij0 x y.
  rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[j1y yj2].
  have [i2j1|i2j1] := leP i2 j1.
    by have := le_trans xi2 (le_trans i2j1 j1y).
  rewrite ltNge; apply/negP => yx.
  have /negP := ij0 y.
  apply; apply/itv_meet_mem; rewrite 2!itv_boundlr.
  by rewrite (le_trans (ltW ij1)) //= (le_trans _ xi2) // yj2 andbT j1y.
- move=> <-{j1} ij2; rewrite -itv_meetE => /set_of_itv_empty_pred0 => ij0 x y.
  rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[i1y yj2].
  rewrite ltNge; apply/negP => yx.
  have /negP := ij0 x.
  apply; apply/itv_meet_mem; split => //; rewrite itv_boundlr i1x //=.
  by rewrite (le_trans xi2) // ltW.
Qed.

Lemma lt_itv_le (a b : interval R) : le_itv a b ->
  set_of_itv a `&` set_of_itv b = set0 ->
  forall x y, x \in a -> y \in b -> x < y.
Proof.
move: a b => [i1 i2] [j1 j2].
move/orP => [/eqP[<-{j1} <-{j2}]|]; last exact: lt_itv_lt.
have [i1i2|i1i2 _ x y] := ltP i1 i2.
  move=> i1i20; exfalso; move/eqP: i1i20; apply/negP.
  by rewrite -itv_meetE set_of_itv_empty_eq0 negbK meetxx joinxx.
by rewrite itv_ge // -leNgt.
Qed.

Let lt_itv_subset (a b c : interval R) (x : R) :
  x \in a -> x \in c -> x \notin b ->
  lt_itv a b -> lt_itv b c ->
  {subset a <= b} \/ {subset b <= a}.
Proof.
move: a b c => [a1 a2] [b1 b2] [c1 c2] + + + ab bc; move: bc ab => /=.
case : (ltgtP b1 c1) => // [b1c1 _|<-{c1} b2c2]; last first.
  case : (ltgtP a1 b1) => // [a1b1 _|<-{b1} a2b2]; last first.
    rewrite 2!itv_boundlr => /andP[a1x xa2] /andP[_ xc2] _.
    left => y.
    by rewrite 2!itv_boundlr => /andP[-> /=] /le_trans; apply; exact: ltW.
  rewrite 3!itv_boundlr => /andP[a1x xa2] /andP[b1x xc2].
  rewrite negb_and -2!ltNge => xb1b2.
  right => y; rewrite 2!itv_boundlr => /andP[b1y yb2].
  case/orP: xb1b2 => [|?]; first by move/(le_lt_trans b1x); rewrite ltxx.
  rewrite (le_trans (ltW a1b1)) //= (le_trans _ xa2) //= (le_trans yb2) //.
  exact/ltW.
case : (ltgtP a1 b1) => // [a1b1 _|-> // a2b2].
  rewrite 3!itv_boundlr => /andP[a1x xa2] /andP[c1x xc2].
  rewrite negb_and -2!ltNge => xb1b2; right => y.
  rewrite 2!itv_boundlr => /andP[b1y yb2]; case/orP: xb1b2 => [xb1|b2x].
    by have := lt_trans (lt_le_trans b1c1 c1x) xb1; rewrite ltxx.
  rewrite (le_trans (ltW a1b1) b1y) /= (le_trans _ xa2) // (le_trans yb2) //.
  exact/ltW.
rewrite 3!itv_boundlr => /andP[b1x xa2] /andP[c1x xc2] _; left => y.
by rewrite 2!itv_boundlr => /andP[-> /=] /le_trans; apply; exact: ltW.
Qed.

Lemma le_itv_subset (a b c : interval R) (x : R) :
  x \in a -> x \in c -> x \notin b ->
  le_itv a b -> le_itv b c ->
  {subset a <= b} \/ {subset b <= a}.
Proof.
move=> xa xc xb /orP[/eqP <- _|ab]; [by left|].
move/orP => [/eqP bc|]; last exact: (lt_itv_subset _ xc).
by move: xb; rewrite bc xc.
Qed.

End lt_itv.
Arguments lt_itv {R}.
Arguments le_itv {R}.
Arguments lt_trans_itv {R _ _ _}.
Arguments le_trans_itv {R _ _ _}.

Lemma ufint_sort_le_itv (R : realType) (s : seq (interval R)) :
  ufint (path.sort le_itv s) = ufint s.
Proof. exact/mem_ufint/path.mem_sort. Qed.

Section lt_itv_diff.
Variable R : realType.

Lemma lt_itv_diff (a b : interval R) : lt_itv a b ->
  ~ {subset b <= a} -> ~ {subset a <= b} ->
  lt_itv (itv_diff a b) b.
Proof.
rewrite /itv_diff; case: ifPn => //; move: a b => [a1 a2] [b1 b2] /=.
case: ltgtP => [a1b1 _ ab0 sba sab|//|<-{b1}].
  have [b2a2|b2a2] /= := leP b2 a2; last by rewrite a1b1.
  exfalso; apply: sba => x.
  rewrite itv_boundlr => /andP[b1x xb2].
  by rewrite itv_boundlr (le_trans (ltW a1b1) b1x) /= (le_trans _ b2a2).
move=> ab0 a2b2 sba sab; rewrite leNgt a2b2 /=.
exfalso; apply: sab => x.
rewrite itv_boundlr => /andP[a1x xb2].
by rewrite itv_boundlr a1x /= (le_trans xb2) // ltW.
Qed.

Lemma le_itv_diff (a b : interval R) : le_itv a b ->
  ~ {subset b <= a} -> ~ {subset a <= b} ->
  le_itv (itv_diff a b) b.
Proof.
rewrite /le_itv => /orP[/eqP <-{b}|]; first by move=> saa; exfalso; exact: saa.
by move=> ab sba sab; apply/orP; right; exact: lt_itv_diff.
Qed.

Lemma lt_itv_itv_diff (y : interval R) a b :
  ~ {subset b <= a} ->
  set_of_itv y `&` set_of_itv a = set0 ->
  lt_itv a b -> lt_itv y a -> lt_itv y b ->
  lt_itv y (itv_diff a b).
Proof.
move: y a b => [y1 y2] [a1 a2] [b1 b2] /=.
case: (ltgtP a1 b1) => [a1b1 ba + _| // | <-{b1}].
  have a2b2 : (a2 < b2)%O.
    rewrite ltNge; apply/negP => b2a2.
    apply: ba => x; rewrite itv_boundlr => /andP[b1x xb2].
    by rewrite itv_boundlr (le_trans (ltW _) b1x) //= (le_trans xb2).
  move: ba a1b1; case: (ltgtP y1 a1) => [y1a1 _ a1b1 ya _| // | <-{a1} ba a1b1 ya y2a2 _].
    rewrite (lt_trans y1a1) // /itv_diff => _.
    case: ifPn => [_ |ab0]; first by rewrite y1a1.
    by rewrite leNgt a1b1 /= leNgt a2b2 /= y1a1.
  rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite ltxx eqxx.
  rewrite leNgt a1b1 /= leNgt a2b2 /= ltxx eqxx ltNge; apply/negP => b1y2.
  move/eqP : ya; apply/negP.
  rewrite -itv_meetE /= meetEtotal minElt y2a2 joinEtotal /= maxEle lexx.
  by rewrite set_of_itv_empty_eq0 negbK (lt_le_trans a1b1).
case: (ltgtP y1 a1) => [y1a1 ab ya a2b2 _ _| // |<-{a1} ab ya a2b2 y2a2 y2b2].
  rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite y1a1.
  rewrite lexx leNgt a2b2 /=; case: ifPn => //.
  rewrite -leNgt le_pinfty_eq => /eqP y1oo.
  by move: y1a1; rewrite y1oo.
rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite ltxx eqxx.
rewrite lexx leNgt a2b2 /=; case: ifPn => //.
rewrite -leNgt le_pinfty_eq => /eqP y1oo.
exfalso.
move/eqP : ab0; apply.
by rewrite /= y1oo itv_join_meet /= set_of_itv_empty_set0.
Qed.

Lemma le_itv_itv_diff (y : interval R) a b :
  ~ {subset b <= a} ->
  set_of_itv y `&` set_of_itv a = set0 ->
  le_itv a b -> le_itv y a -> le_itv y b ->
  le_itv y (itv_diff a b).
Proof.
move=> ba ya0; rewrite {1}/le_itv => /orP[/eqP[ab]|ab].
  by exfalso; move: ba; rewrite -ab; exact.
rewrite {1}/le_itv => /orP[/eqP ya|ya].
  move: ya0; rewrite {}ya {y} => aa0.
  have [[x xa] _|/set0P/negP/negPn/eqP a0 _] := pselect (set_of_itv a !=set0).
    by exfalso; move/eqP : aa0; apply/negP/set0P; exists x.
 (* lemma? *)
 apply/orP; left.
 by rewrite /itv_diff itv_meetE ifT // a0 set0I.
move/orP => [/eqP yb|yb].
by move: ya; rewrite yb => /(lt_trans_itv ab); rewrite lt_itvxx.
by apply/orP; right; exact: lt_itv_itv_diff.
Qed.

End lt_itv_diff.

Section lt_itv_disjoint.
Variable R : realType.

Lemma nonempty_sorted_disjoint_itv h (t : seq (interval R)) :
  (forall i, i \in t -> set_of_itv i !=set0) ->
  path.sorted le_itv (h :: t) ->
  path.path disjoint_itv h t ->
  (forall c, c \in t -> disjoint_itv h c).
Proof.
elim: t h => [h t0 _ _ c //|b t ih a t0 /= /andP[lt_ab lt_bt] /andP[dis_ab dis_bt] c].
rewrite inE => /orP[/eqP ->{c} //|ct]; apply: ih => //.
- move=> i it; apply t0 => //.
  by rewrite inE it orbT.
- rewrite (_ : _ :: _ = mask (true :: false :: nseq (size t) true) [:: a, b & t]); last first.
    by rewrite /= mask_true.
  apply (path.path_mask (@le_trans_itv R)).
  by rewrite /= lt_ab.
- case: t => [//|d t] in t0 lt_bt dis_bt ct *.
  move: dis_bt; rewrite [in X in X -> _]/= => /andP[dis_bd dis_dt].
  rewrite /= {}dis_dt andbT.
  move: (lt_itv_le lt_ab (eqP dis_ab)) => {}lt_ab.
  move/andP : lt_bt => [+ _] => /lt_itv_le/(_ (eqP dis_bd)) lt_bd.
  apply/lt_disjoint => x y xa yd.
  have [z bz] : set_of_itv b !=set0 by apply t0; rewrite mem_head.
  by rewrite (@lt_trans _ _ z _ _ (lt_ab _ _ _ _) (lt_bd _ _ _ _)).
Qed.

Lemma nonempty_sorted_disjoint_itv_trivIset h (t : seq (interval R)) :
  (forall c, c \in t -> set_of_itv c !=set0) ->
  path.sorted le_itv (h :: t) ->
  path.path disjoint_itv h t ->
  trivIset (fun i => set_of_itv (nth 0%O (h :: t) i)).
Proof.
elim: t h => //= [h t0 _ _ i j ij|b t ih a t0 /andP[lt_ab lt_bt] /andP[dis_ab dis_bt]].
  case: i => [|i] /= in ij *.
    case: j => [|j] //= in ij *.
    by rewrite nth_nil set_of_itv_empty_set0 // setI0.
  by rewrite nth_nil set_of_itv_empty_set0 // set0I.
move=> [|i] [|j] //= ?.
- have [jbt|btj] := ltP j (size (b :: t)).
    apply/eqP/(@nonempty_sorted_disjoint_itv _ (b :: t)) => //=.
    by rewrite lt_ab.
    by rewrite dis_ab.
    by rewrite mem_nth.
  by rewrite nth_default // set_of_itv_empty_set0 // setI0.
- have [ibt|bti] := ltP i (size (b :: t)).
    rewrite setIC.
    apply/eqP/(@nonempty_sorted_disjoint_itv _ (b :: t)) => //=.
    by rewrite lt_ab.
    by rewrite dis_ab.
    by rewrite mem_nth.
  by rewrite nth_default // set_of_itv_empty_set0 // set0I.
- by apply ih => // c ct; apply t0; rewrite inE ct orbT.
Qed.

Lemma path_disjoint_pinfty_eq0 (t : seq (interval R)) j :
  (forall i, i \in t -> set_of_itv i !=set0) ->
  path.path lt_itv (Interval j +oo%O) t ->
  path.path disjoint_itv (Interval j +oo%O) t ->
  t = [::].
Proof.
case: t => // h t ne.
case: j => [b r|[]]; last 2 first.
  by move=> _; apply path_disjoint_setT_eq0.
  rewrite /=; case: h => h1 h2 in ne *.
  by rewrite pinfty_lt if_same.
case: h => h1 h2 /= in ne *.
rewrite pinfty_lt if_same.
case: ifPn => //= rh1 ht /andP[rooh Hdis].
exfalso.
move: rooh; apply/negP/set0P; rewrite -itv_meetE /=.
rewrite joinEtotal maxElt rh1 meetEtotal minElt /=.
by apply ne; rewrite mem_head.
Qed.

Lemma sorted_le_itv_bound (s : seq (interval R)) :
  (forall i, i \in s -> set_of_itv i !=set0) ->
  path.sorted le_itv s ->
  path.path (fun x y => disjoint_itv x y) (head 0%O s) (behead s) ->
  path.sorted <=%O (map bnd2 s) /\ path.sorted <=%O (map bnd1 s).
Proof.
elim: s => // -[h1 h2] [//|[t11 t12] t2] ih /= ne ht Hdis; split.
  apply/andP; split.
    case/andP : ht => + _.
    move/orP => -[/eqP[_ <-]//|].
    rewrite /lt_itv; case: ltgtP => //= [|_ /ltW] // h11t11 _.
    move/andP : Hdis => [H _].
    rewrite leNgt; apply/negP => t12h2.
    move : H; apply/negP/set0P.
    have [x t11t12x] : set_of_itv (Interval t11 t12) !=set0.
      by apply ne; rewrite 2!inE eqxx orbT.
    exists x; split => //.
    apply/set_of_itv_mem; rewrite itv_boundlr.
    move/set_of_itv_mem : t11t12x; rewrite itv_boundlr => /andP[t11x xt12].
    by rewrite (le_trans (ltW _) t11x) // (le_trans xt12) // ltW.
  apply: (proj1 (ih _ _ _)).
  by move=> i it1t2; apply ne; rewrite inE it1t2 orbT.
  by case/andP : ht => ? ht.
  by rewrite /=; move/andP : Hdis => // -[].
apply/andP; split.
  move/andP : ht => -[] /orP[/eqP[<-//]|].
  by rewrite /lt_itv; case: ltgtP.
apply: (proj2 (ih _ _ _)).
by move=> i it1t2; apply ne; rewrite inE it1t2 orbT.
by case/andP : ht.
by rewrite /=; move/andP : Hdis => // -[].
Qed.

End lt_itv_disjoint.

Section decomposition.
Variable R : realType.

Program Definition decompose' (s : seq (interval R))
  (f : forall s', (size s' < size s)%N -> seq (interval R)) : seq (interval R) :=
  match s with
  | [::] => [::] | [:: i] => [:: i]
  | [:: i, j & tl] => match pselect {subset i <= j} with
    | left _ => f (j :: tl) _
    | right not_ij => match pselect {subset j <= i} with
                     | left _ => f (i :: tl) _
                     | right _ => itv_diff i j :: f (j :: tl) _
                     end
    end
  end.

Lemma wfr : well_founded (fun s' s : seq (interval R) => (size s' < size s)%N).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => s t /ssrnat.ltP. Qed.

Definition decompose : seq (interval R) -> seq (interval R) :=
  Fix wfr (fun _ => _ _) decompose'.

Lemma decompose'_ext (x : seq (interval R))
  (f g : forall y : seq (interval R), (size y < size x)%N -> seq (interval R)) :
    (forall (y : seq (interval R)) (p : (size y < size x)%N), f y p = g y p) ->
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
    match pselect {subset i <= j} with
    | left _ => decompose (j :: tl)
    | right not_ij => match pselect {subset j <= i} with
                     | left _ => decompose (i :: tl)
                     | right _ => itv_diff i j :: decompose (j :: tl)
                     end
    end.
Proof.
rewrite {1}/decompose Fix_eq; last exact: decompose'_ext.
by move: i j => [i1 i2] [j1 j2] //=; case: pselect => //; case: pselect.
Qed.

Lemma ufint_decompose (s : seq (interval R)) :
  path.sorted le_itv s -> ufint (decompose s) = ufint s.
Proof.
move sn : (size s) => n; elim: n s sn => [|n ih [//|i [|j tl]]].
  by case => // _ _; rewrite decompose_nil.
  by move=> _ _; rewrite decompose_one.
move=> [tln] Hsort.
rewrite decompose_two.
case: (pselect _) => ij.
  rewrite /= ih //; last by move: Hsort; rewrite /= => /andP[].
  rewrite /ufint 3!bigcup_cons setUA; congr setU.
  by rewrite setUC; apply/esym/setUidPl/itv_set_of_itv_subset.
case: (pselect _) => ji.
  rewrite /= ih //; last first.
    rewrite (_ : _ :: _ = mask (true :: false :: nseq (size tl) true) [:: i, j & tl]); last first.
      by rewrite /= mask_true.
    by apply (path.path_mask (@le_trans_itv _)).
  rewrite /ufint 3!bigcup_cons setUA; congr setU.
  by apply/esym/setUidPl/itv_set_of_itv_subset.
rewrite /= {1}/ufint /= (bigcup_cons _ (decompose (j :: tl))).
rewrite -/(ufint (decompose (j :: tl))) ih //; last first.
  by move: Hsort => /andP[].
rewrite {2}/ufint bigcup_cons -/(ufint _).
rewrite /ufint bigcup_cons !setUA; congr (_ `|` _).
have [i0|/set0P/negP/negPn/eqP i0] := pselect (set_of_itv i !=set0); last first.
  move/itv_set_of_itv_subset in ij.
  by exfalso; apply: ij; rewrite i0.
rewrite itv_diffE // eqEsubset; split.
  apply: subsetU; last by move=> x; right.
  by move=> x ix; left; case: ix.
move=> x [ix|jx]; last by right.
by have [jx|jx] := pselect ((set_of_itv j) x); [right|left].
Qed.

Lemma decompose_nonempty (s : seq (interval R)) :
  (forall i, i \in s -> set_of_itv i !=set0) ->
  (forall i, i \in decompose s -> set_of_itv i !=set0).
Proof.
move sn : (size s) => n; elim: n s sn => [|n ih [//|i [|j tl]]].
  by move=> s /size0nil ->{} _ i; rewrite decompose_nil.
  by move=> _ H t; rewrite decompose_one /= inE => /eqP ->; apply H; rewrite inE.
rewrite /= => -[tln] ne t.
rewrite decompose_two.
case: pselect => ij.
  apply ih => // k kjtl; apply ne.
  by rewrite inE kjtl orbT.
case: pselect => ji.
  apply ih => // k kjtl; apply ne.
  move: kjtl; rewrite inE => /orP[/eqP ->|].
  by rewrite mem_head.
  by rewrite !inE => ->; rewrite !orbT.
rewrite inE => /orP[/eqP ->|].
  rewrite itv_diffE //.
  suff : exists x, (set_of_itv i) x /\ ~ (set_of_itv j) x by case=> x [? ?]; exists x.
  apply/not_existsP => xij.
  apply ij.
  apply/itv_set_of_itv_subset => x ix.
  have := xij x.
  by rewrite not_andP => -[//|/contrapT].
apply ih => // k kjtl.
apply ne.
by rewrite inE kjtl orbT.
Qed.

Lemma path_disjoint_itv_decompose (s : seq (interval R)) :
  path.sorted le_itv s ->
  forall t, (forall c, c \in s -> disjoint_itv t c) ->
  path.path disjoint_itv t (decompose s).
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j tl]]].
  by move=> _ /size0nil ->{} _ t tc; rewrite decompose_nil.
  by move=> _ _ t tc; rewrite decompose_one /= tc ?mem_head // eqxx.
case.
case: n => [//|n] in ih * => -[] tln H t tc.
rewrite decompose_two.
case: pselect => ij.
  apply ih => //.
    by rewrite /= tln.
  by case/andP : H.
  move=> c cjtl.
  by rewrite tc // inE cjtl orbT.
case: pselect => // ji.
  apply ih; first by rewrite /= tln.
  rewrite (_ : _ :: _ = mask (true :: false :: nseq (size tl) true) [:: i, j & tl]); last first.
    by rewrite /= mask_true.
  by apply (path.path_mask (@le_trans_itv _)).
  move=> c; rewrite inE => citl.
  by rewrite tc // !inE orbCA citl orbT.
rewrite /=; apply/andP; split.
  by apply/eqP; rewrite itv_diffE // setDE setIA (eqP (tc _ _)) ?set0I // mem_head.
apply ih; first by rewrite /= tln.
  apply: (path.subseq_sorted (@le_trans_itv _)) H.
  exact: subseq_cons.
move=> c cjtl.
apply/eqP; rewrite itv_diffE //.
move: cjtl.
rewrite inE => /orP[/eqP ->|ctl].
  by rewrite setDE -setIA setICl setI0.
rewrite predeqE => x; split => // -[].
rewrite setDE => -[] /set_of_itv_mem ix /set_of_itv_mem/negP jx /set_of_itv_mem cx.
have jc : le_itv j c.
  move: ctl.
  rewrite -sub1seq.
  move/path.subseq_path_in => /(_ le_itv j) /=; rewrite andbT; apply => //.
    by move=> ? ? ? ? ? ?; exact: le_trans_itv.
  by move: H => /= /andP[].
have iijj : le_itv i j by move: H; rewrite /= => /andP[].
apply ji.
by have [|] := le_itv_subset ix cx jx iijj jc.
Qed.

Lemma path_disjoint_itv_decompose_head_behead (s : seq (interval R)) :
  path.sorted le_itv s ->
  path.path disjoint_itv (head 0%O (decompose s)) (behead (decompose s)).
Proof.
move sn : (size s) => n.
elim: n s sn => [|n ih [//|i [|j tl]]].
  by move=> _ /size0nil ->{} _; rewrite decompose_nil.
  by move=> ic _; rewrite decompose_one /=.
case.
case: n => [//|n] in ih *=> -[] tln H.
rewrite decompose_two.
case: pselect => ij.
  apply ih => //.
    by rewrite /= tln.
  by case/andP : H.
case: pselect => // ji.
  apply ih; first by rewrite /= tln.
  rewrite (_ : _ :: _ = mask (true :: false :: nseq (size tl) true) [:: i, j & tl]); last first.
    by rewrite /= mask_true.
  by apply (path.path_mask (@le_trans_itv _)).
rewrite /=.
apply path_disjoint_itv_decompose.
  by move: H => /= /andP[].
move=> c cjtl.
apply/eqP; rewrite itv_diffE //.
move: cjtl.
rewrite inE => /orP[/eqP ->|ctl].
  by rewrite setDE -setIA setICl setI0.
rewrite predeqE => x; split => // -[].
rewrite setDE => -[] /set_of_itv_mem ix /set_of_itv_mem/negP jx /set_of_itv_mem cx.
have jc : le_itv j c.
  move: ctl.
  rewrite -sub1seq.
  move/path.subseq_path_in => /(_ le_itv j) /=; rewrite andbT; apply => //.
    by move=> ? ? ? ? ? ?; exact: le_trans_itv.
  by move: H => /= /andP[].
have iijj : le_itv i j by move: H; rewrite /= => /andP[].
apply ji.
by have [|] := le_itv_subset ix cx jx iijj jc.
Qed.

Lemma all_decompose t y : path.sorted le_itv t ->
  all (fun x => le_itv y x && disjoint_itv y x) t ->
  all (fun x => le_itv y x && disjoint_itv y x) (decompose t).
Proof.
move: y.
have [n] := ubnP (size t); elim: n t => // n ih.
case.
  by move=> _ y _ _; rewrite decompose_nil.
move=> a [|b t].
  by move=> /= n1 y _; by rewrite decompose_one /= andbT.
move=> /=; rewrite ltnS => tn y /andP[ab bt] /and3P[ya yb yt].
rewrite decompose_two.
case: pselect.
  move=> sab.
  apply ih => //.
  apply/allP => z.
  rewrite inE => /orP[/eqP -> //| zt].
  by move/allP : yt; apply.
move=> sab.
case: pselect => sba.
  apply ih => //.
  rewrite /=.
  rewrite (_ : t = mask (false :: nseq (size t) true) [:: b & t]); last first.
    by rewrite /= mask_true.
  apply (path.path_mask (@le_trans_itv _)) => //.
  by rewrite /= ab.
  apply/allP => z.
  rewrite inE => /orP[/eqP -> //|zt].
  by move/allP : yt; apply.
apply/allP.
move=> z.
rewrite inE => /orP[|]; last first.
  move=> zbt.
  have : all (fun x : interval R => le_itv y x && (disjoint_itv y x)) (decompose (b :: t)).
    apply ih => //.
    apply/allP => u.
    rewrite inE => /orP[/eqP -> //|ut].
    by move/allP : yt; apply.
  move/allP => H.
  by apply H.
move/eqP=> ->{z}.
apply/andP; split.
  apply le_itv_itv_diff => //.
  by move/andP : ya => -[_ /eqP].
  by move/andP : ya => -[].
  by move/andP : yb => -[].
rewrite /disjoint_itv itv_diffE //=.
apply/eqP.
apply: (@subsetI_eq0 _ _ (set_of_itv y)_ (set_of_itv a)) => //.
by move=> x [].
by move/andP : ya => -[_ /eqP].
Qed.

Lemma sorted_decompose s : path.sorted le_itv s -> path.sorted le_itv (decompose s).
Proof.
have [n] := ubnP (size s); elim: n s => // n ih.
case.
  by move=> _ _; rewrite decompose_nil.
move=> a [|b t].
  by move=> _ _; rewrite decompose_one.
rewrite ltnS => abtn abt.
rewrite decompose_two.
case: pselect => ab.
  apply ih => //.
  by move: abt => /= /andP[].
case: pselect => ba.
  apply ih => //.
  rewrite (_ : _ :: _ = mask (true :: false :: nseq (size t) true) [:: a, b & t]); last first.
    by rewrite /= mask_true.
  apply path.path_mask => //.
  by move=> y x z; apply le_trans_itv.
rewrite /=.
have bt : path.sorted le_itv (decompose (b :: t)).
  by apply ih => //; move: abt => /= /andP[].
rewrite path.path_min_sorted //.
have bt' : path.sorted le_itv (b :: t).
  by move: abt => /= /andP[].
have : all (fun x => le_itv (itv_diff a b) x && (disjoint_itv (itv_diff a b) x)) (b :: t).
  rewrite /=.
  rewrite le_itv_diff //=; last first.
    by move: abt => /= => /andP[].
  apply/andP; split.
    by apply/eqP; rewrite itv_diffE // setDE -setIA setICl setI0.
  apply/allP => z zt.
  apply/andP; split.
    rewrite (@le_trans_itv _ b) //.
      apply le_itv_diff => //.
      by move: abt => /= /andP[].
    move: abt => /= /andP[_ bt''].
    by move/path.order_path_min : bt'' => /(_ (@le_trans_itv R)) /allP; apply.
  rewrite /disjoint_itv itv_diffE //.
  apply/negPn/negP => /set0P[x] -[[] ].
  move/set_of_itv_mem => xa bx /set_of_itv_mem zx.
  move: a b z => [a1 a2] [b1 b2] [z1 z2] in zt zx abtn abt ab ba bt bt' bx xa *.
  apply: bx.
  apply/set_of_itv_mem.
  rewrite itv_boundlr in xa.
  rewrite itv_boundlr in zx.
  rewrite itv_boundlr.
  case/andP : zx => zx1 zx2.
  rewrite (le_trans _ zx1) //=; last first.
     have : le_itv (Interval b1 b2) (Interval z1 z2).
       have : path.path le_itv (Interval b1 b2) t.
         by move: abt => /=.
     by move/path.order_path_min => /(_ (@le_trans_itv R))/allP; apply.
     rewrite /le_itv => /orP[/eqP[ <- //]|].
     rewrite /=.
     by case: ltgtP => //.
   rewrite leNgt; apply/negP => b2x.
   case/andP : xa => xa1 xa2.
   apply: ba.
   move=> u.
   rewrite itv_boundlr => /andP[b1u ub2].
   rewrite itv_boundlr; apply/andP; split.
     rewrite (le_trans _ b1u) //.
     move: abt; rewrite /= /le_itv => /andP[/orP[/eqP[<- //]| /=]].
     by case: ltgtP.
   by rewrite (le_trans _ xa2) // (le_trans _ (ltW b2x)).
move/(@all_decompose (b :: t) (itv_diff a b) bt').
by apply sub_all => z /andP[].
Qed.

(* NB: not used *)
Lemma trivIset_decompose (s : seq (interval R)) :
  path.sorted le_itv s ->
  (forall c, c \in s -> set_of_itv c !=set0) ->
  trivIset (fun i => set_of_itv (nth 0%O (decompose s) i)).
Proof.
move=> sorteds smem0.
have [/eqP|s0] := boolP (size (decompose s) == 0%N).
  move/size0nil => -> /= i j ij.
  by rewrite nth_nil set_of_itv_empty_set0 // set0I.
have head_behead : decompose s = head 0%O (decompose s) :: behead (decompose s).
  by move: s0; case: (decompose s).
rewrite head_behead.
apply: nonempty_sorted_disjoint_itv_trivIset.
by move=> c cs; exact/(decompose_nonempty smem0)/mem_behead.
by rewrite -head_behead sorted_decompose.
suff : path.path disjoint_itv 0%O (head 0%O (decompose s) :: behead (decompose s)).
  by rewrite /= => /andP[].
rewrite -head_behead path_disjoint_itv_decompose => // c cs.
by apply/eqP; rewrite set_of_itv_empty_set0 // set0I.
Qed.

Lemma itv_cplt_decomposeE (s : seq (interval R)) :
  ufint (itv_cplt (decompose (path.sort le_itv [seq x <- s | set_of_itv x != set0]))) = ~` ufint s.
Proof.
rewrite itv_cpltE.
  rewrite ufint_decompose.
    by rewrite ufint_sort_le_itv // ufint_filter_neq0.
  exact: (path.sort_sorted (@total_le_itv _)).
apply sorted_le_itv_bound.
- apply decompose_nonempty => i.
  by rewrite path.mem_sort mem_filter => /andP[/set0P].
- apply: sorted_decompose; exact: (path.sort_sorted (@total_le_itv _)).
- apply: path_disjoint_itv_decompose_head_behead.
  exact: (path.sort_sorted (@total_le_itv _)).
Qed.

End decomposition.
(* WIP(end) *)

Section real_measure.
Variable R : realType.

Ltac Obligation Tactic := idtac.
Program Definition interval_isRingOfSets : isRingOfSets R :=
  @isRingOfSets.Build _ _ _ _ _.
Next Obligation.
exact [set ufint X | X in @setT (@fint _)].
Defined.
Next Obligation.
rewrite /interval_isRingOfSets_obligation_1.
exists fset0 => //.
rewrite /ufint /= (_ : (fun j : interval R => _) = set0); last by rewrite predeqE.
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
rewrite /mkset.
set s := itv_cplt (decompose (path.sort le_itv [seq x <- a | set_of_itv x != set0])).
exists ([fset x | x in s]%fset) => //=.
rewrite (@mem_ufint _ _ s) //; last by move=> i; rewrite inE.
by rewrite /s itv_cplt_decomposeE aA.
Qed.

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
       (A `<=` \bigcup_n (set_of_itv `] (a_ n), (b_ n) [ )) &
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
