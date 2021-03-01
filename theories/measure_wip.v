(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
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
  trivIset setT A -> forall n X, mu (X `&` \big[setU/set0]_(i < n) A i) =
                        (\sum_(i < n) mu (X `&` A i))%E.
Proof.
move=> MA ta; elim=> [|n ih] X; first by rewrite !big_ord0 setI0 outer_measure0.
rewrite big_ord_recr /= additive_ext_inter // ?ih ?big_ord_recr //.
- exact: sigma_algebra_bigU.
- by have /= := (@trivIset_bigUI _ predT); apply; rewrite // ?trueE.
Qed.

Lemma lee_bigU_lim_sum (A : (set T) ^nat)  X :
  (mu (X `&` \bigcup_k A k) <= lim (fun n => \sum_(k < n) mu (X `&` A k)))%E.
Proof.
apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
by apply/le_outer_measure; rewrite bigcup_distrr.
Qed.

Lemma lee_lim_sum_bigU (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall X,
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
  trivIset setT A -> M (\bigcup_k (A k)).
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
  suff tB : trivIset setT B by exact: sigma_algebra_trivIset_bigsetU.
  apply/trivIsetP => i j _ _.
  wlog ij : i j / (i < j)%N => [hwlog|].
    by case: ltngtP => // ij _; last rewrite setIC; rewrite hwlog// ltn_eqF.
  move=> _; rewrite predeqE => t; split => // -[] Bjt Bit.
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

Definition caratheodory_measure_mixin := Measure.Axioms caratheodory_measure0
  caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
(* caratheodory(2): restriction of mu to M is a positive measure *)
(*Canonical*)Definition measure_of_outer_measure : {measure set (measurables mu) -> _} :=
  Measure.Pack _ caratheodory_measure_mixin.

(* caratheodory(3): mu*-negligible sets are measurable *)
Lemma caratheodory_measure_complete (N : set U) :
  measure_of_outer_measure.-negligible N -> mu.-measurable N.
Proof.
move=> [A [mA muA0 NA]]; apply le_ext_measurable => X.
suff -> : mu (X `&` N) = 0%:E.
  by rewrite add0e le_outer_measure //; apply subIset; left.
have muN0 : mu N = 0%:E.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  move: (le_outer_measure mu NA).
  move/le_trans; apply.
  by rewrite -muA0 /=.
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
  - apply/trivIsetP => i j _ _ ij.
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

Canonical outer_measure_of_measure (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> {ereal R}}) : {outer_measure set T -> {ereal R}} :=
    OuterMeasure (OuterMeasure.Axioms (mu_ext0 mu) (mu_ext_ge0 mu)
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
  forall A, measurable A -> (outer_measure_of_measure mu).-measurable A.
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

Section Hahn_extension.
Variables (R : realType) (T : ringOfSetsType) (mu : {measure set T -> {ereal R}}).

Let mstar : {outer_measure set T -> {ereal R}} := outer_measure_of_measure mu.
(*Let M : measurableType := caratheodory_measurableType mstar.*)
Let M : measurableType := [the measurableType of measurables [outer_measure of mu_ext mu]].

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

(*Definition Hahn_extension : {measure set M -> {ereal R}} := measure_of_outer_measure mstar.*)

(*Let I : measurableType := gen_salgebra_measurableType (@setT (set T)).
Definition Hahn_mu : {measure set I -> {ereal R}}.*)

End Hahn_extension.

From mathcomp Require Import interval.

(* PR merged to mathcomp's master *)
Lemma ge_pinfty (R : numDomainType) (x : itv_bound R) : (+oo <= x)%O = (x == +oo)%O.
Proof. by move: x => [[]|[]]. Qed.

Lemma le_ninfty (R : numDomainType) (x : itv_bound R) : (x <= -oo)%O = (x == -oo%O).
Proof. by case: x => // -[]. Qed.

Lemma gt_pinfty (R : numDomainType) (x : itv_bound R) : (+oo%O < x)%O = false.
Proof. by case: x. Qed.

Lemma lt_ninfty (R : numDomainType) (x : itv_bound R) : (x < -oo%O)%O = false.
Proof. by case: x => // -[]. Qed.
(* end PR merged to mathcomp's master *)

(* TODO: add to ereal.v? *)
Lemma subee (R : numDomainType) (x : {ereal R}) :
  x != +oo%E -> x != -oo%E -> (x - x = 0%:E)%E.
Proof. by move: x => [r _ _| |] //; rewrite -subERFin subrr. Qed.

Lemma addeK (R : realDomainType) (x y : er R) : is_real x -> (y + x - x)%E = y.
Proof. by move: x y => [x| |] [y| |] //; rewrite -addERFin addrK. Qed.

Lemma subeK (R : realDomainType) (y x : er R) : is_real y -> (x - y + y)%E = x.
Proof. by move: x y => [x| |] [y| |] //; rewrite -addERFin subrK. Qed.

Lemma lee_sub (R : realDomainType) (x y z t : er R) : (x <= y)%E -> (t <= z)%E -> (x - z <= y - t)%E.
Proof.
move: x y z t => -[x| |] -[y| |] -[z| |] -[t| |] //=;
  rewrite ?(lee_pinfty,lee_ninfty)//.
by rewrite !lee_fin; exact: ler_sub.
Qed.

Lemma ERFin_sum (R : numDomainType) n m (f : nat -> {ereal R}) :
  (forall i, (n <= i < m)%nat -> is_real (f i)) ->
  (\sum_(n <= i < m) (f i))%E = (\sum_(n <= i < m) (real_of_er (f i)))%:E.
Proof.
move=> nim; rewrite (@big_morph _ _ (@ERFin R) 0%:E adde) //.
rewrite [LHS]big_nat_cond [RHS]big_nat_cond; apply eq_bigr => i.
by rewrite andbT => /nim fi; rewrite -ERFin_real_of_er.
Qed.

Lemma real_of_erD (R : numDomainType) (a b : {ereal R}) :
  is_real a -> is_real b -> real_of_er (a + b) = real_of_er a + real_of_er b.
Proof. by move: a b => [r| |] [s| |]. Qed.

Lemma telescope_sume (R : numDomainType) n m (f : nat -> {ereal R}) :
  (forall i, (n <= i <= m)%nat -> is_real (f i)) ->
  (n <= m)%N ->
  (\sum_(n <= k < m) (f k.+1 - f k)%E = f m - f n)%E.
Proof.
move=> foo nm.
have [g fg] : exists g : nat -> R, forall i, (n <= i <= m)%N -> f i = (g i)%:E.
  exists (fun i => real_of_er (f i)) => i nim.
  by rewrite -ERFin_real_of_er // foo.
rewrite ERFin_sum //; last first.
  move=> i /andP[ni im].
  rewrite is_realD is_realN (foo i) // ?andbT ?ni ?(ltnW im) //.
  by rewrite foo // im andbT (leq_trans ni).
rewrite [in LHS]big_nat_cond.
(under eq_bigr) => [i|].
  rewrite andbT => /andP[ni im].
  rewrite real_of_erD //; last 2 first.
    by rewrite foo // im (leq_trans ni).
    by rewrite is_realN foo // ni /= (ltnW im).
  rewrite real_of_erN.
  over.
rewrite -big_nat_cond telescope_sumr // subERFin.
rewrite -ERFin_real_of_er; last first.
  by rewrite foo // nm leqnn.
by rewrite -ERFin_real_of_er // foo // nm leqnn.
Qed.

From mathcomp Require Import ssrint.

(* WIP *)
Lemma head_behead {T : eqType} (s : seq T) def : s != [::] -> head def s :: behead s = s.
Proof. by case: s. Qed.

Lemma has_inf0 d (T : porderType d) : ~ has_inf (@set0 T).
Proof. by rewrite /has_inf not_andP; left; apply/set0P/negP/negPn. Qed.

Lemma has_sup0 d (T : porderType d) : ~ has_sup (@set0 T).
Proof. by rewrite /has_sup not_andP; left; apply/set0P/negP/negPn. Qed.

Lemma has_lbound0 {R : numDomainType} : has_lbound (@set0 R). Proof. by exists 0. Qed.

Lemma has_ubound0 {R : numDomainType} : has_ubound (@set0 R). Proof. by exists 0. Qed.

Lemma sup0 (R : realType) : sup (@set0 R) = 0.
Proof. by rewrite sup_out //; exact: has_sup0. Qed.

Lemma inf0 (R : realType) : inf (@set0 R) = 0.
Proof. by rewrite inf_out //; exact: has_inf0. Qed.

Lemma Rhull0 (R : realType) : Rhull set0 = `]0, 0[ :> interval R.
Proof.
rewrite /Rhull (asboolT has_lbound0) (asboolT has_ubound0) /= asboolF //=.
by rewrite sup0 inf0.
Qed.

Lemma itv_boundNpinfty (R : numDomainType) (a : itv_bound R) :
  a != +oo%O <-> (a = -oo%O \/ exists b r, a = BSide b r).
Proof.
move: a => [b r|[]] => /=; split => //.
- by move=> _; right; exists b, r.
- by move=> _; left.
- by move=> [//|[b [r //]]].
Qed.

Lemma itv_boundNninfty (R : numDomainType) (a : itv_bound R) :
  a != -oo%O <-> (a = +oo%O \/ exists b r, a = BSide b r).
Proof.
move: a => [b r|[]] => /=; split => //.
- by move=> _; right; exists b, r.
- by move=> [//|[b [r //]]].
- by move=> _; left.
Qed.

Lemma mkset_nil {T : choiceType} : [set x | x \in [::]] = set0 :> set T.
Proof. by rewrite predeqP. Qed.

Lemma bigcup_mkset {T : choiceType} U (s : seq T) (f : T -> set U) :
  \bigcup_(i in [set i | i \in s]) (f i) = \big[setU/set0]_(i <- s) (f i).
Proof.
elim: s => [/=|h t ih].
  by rewrite mkset_nil bigcup_set0 big_nil.
rewrite big_cons -ih predeqE => u; split.
- move=> [i]; rewrite /mkset inE => /orP[/eqP-> fhu|it fiu];
    by [left|right; exists i].
- case=> [fhu|]; first by exists h => //; rewrite /mkset mem_head.
  by move=> [i it fiu]; exists i => //; rewrite /mkset inE it orbT.
Qed.

Lemma bigcup_empty {T : choiceType} (I : Type) (F : I -> set T) (D : set I) :
  (\bigcup_(i in D) F i = set0) <-> (D = set0) \/ (forall i, D i -> F i = set0).
Proof.
split=> [|[->|]]; [|by rewrite bigcup_set0|].
  apply: contraPP => /not_orP[/eqP/set0P[i Di]].
  move/existsNP => [j /not_implyP[Dj /eqP/set0P[t Fjt]]].
  by move/eqP; apply/negP/set0P; exists t, j.
apply: contraPP => /eqP/set0P[t [i Di Fit]].
by move/(_ _ Di)/eqP; apply/negP/set0P; exists t.
Qed.

Lemma bigcup_nonempty {T : choiceType} (I : Type) (F : I -> set T) (D : set I) :
  (\bigcup_(i in D) F i !=set0) <-> (D !=set0) /\ (exists i, D i /\ F i !=set0).
Proof.
apply/iff_not2; split=> [|/not_andP[/set0P/negP/negPn/eqP ->{D}|/forallNP DF]].
- move=> /set0P/negP/negPn/eqP/bigcup_empty[D0|DF]; apply/not_andP.
  by left; apply/set0P/negP/negPn/eqP.
  by right; apply/forallNP=> i [Di]; apply/set0P/negP/negPn/eqP/DF.
- 1,2: apply/set0P/negP/negPn/eqP/bigcup_empty.
  by left.
  by right => i Di; have /not_andP[//|/set0P/negP/negPn/eqP] := DF i.
Qed.

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

Coercion interval_to_pair T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

Section set_of_itv.
Variable (R : numDomainType).
Implicit Type i j : interval R.
Implicit Type x y : R.

Lemma IntervalE i : i = Interval i.1 i.2.
Proof. by case: i. Qed.

Definition set_of_itv i : set R := [set x | x \in i].

Lemma is_interval_set_of_itv i : is_interval (set_of_itv i).
Proof. exact: interval_is_interval. Qed.

Lemma set_of_itv_mem i x : (set_of_itv i) x <-> x \in i.
Proof. by move: i => [[[]i1|[]] [[]i2|[]]]. Qed.

Lemma itv_set_of_itv_subset i j : {subset i <= j} <-> set_of_itv i `<=` set_of_itv j.
Proof. by move: i j => [[[] ?|[]] [[] ?|[]]] [[[] ?|[]] [[] ?|[]]]. Qed.

Lemma set_of_itv_empty_set0 i : ~~ (i.1 < i.2)%O -> set_of_itv i = set0.
Proof.
case: i => a b /itv_ge ij0; rewrite predeqE => r; split => //.
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
  set_of_itv_pinfty_pinfty, set_of_itv_pinfty_set0, set_of_itv_minfty_set0).

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

Lemma trivIset_set_of_itv_nth (R : numDomainType) def (s : seq (interval R))
  (D : set nat) : set_of_itv def = set0 ->
  trivIset D (fun i => set_of_itv (nth def s i)) <->
    trivIset D (fun i => nth set0 (map set_of_itv s) i).
Proof.
move=> def0; split=> /trivIsetP ss; apply/trivIsetP => i j Di Dj ij.
- have [si|si] := ltP i (size s); last first.
    by rewrite (nth_default set0) ?size_map// set0I.
  have [sj|sj] := ltP j (size s); last first.
    by rewrite setIC (nth_default set0) ?size_map// set0I.
  by rewrite (nth_map def) // (nth_map def) // ss.
- have [?|h] := ltP i (size s); last by rewrite (nth_default def h) def0 set0I.
  have [?|h] := ltP j (size s); last by rewrite (nth_default def h) def0 setI0.
  by have := ss _ _ Di Dj ij; rewrite (nth_map def) // (nth_map def).
Qed.
Arguments trivIset_set_of_itv_nth {R} _ {s}.

Section set_of_itv_realDomainType.
Variable R : realDomainType.

Lemma set_of_itvC_minfty_BSide b (r : R) :
  ~` set_of_itv (Interval -oo%O (BSide b r)) = set_of_itv (Interval (BSide b r) +oo%O).
Proof.
case: b; rewrite !set_of_itvE predeqE => x.
by split; rewrite leNgt => /negP.
by split; rewrite ltNge => /negP.
Qed.

Lemma set_of_itvC_BSide_pinfty b (r : R) :
  ~` set_of_itv (Interval (BSide b r) +oo%O) = set_of_itv (Interval -oo%O (BSide b r)).
Proof. by rewrite -set_of_itvC_minfty_BSide setCK. Qed.

Let set_of_itvC_BSide_BSide a b (x y : R) :
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

Lemma set_of_itvC_Interval (a b : itv_bound R) : ~` set_of_itv (Interval a b) =
  set_of_itv (Interval -oo%O a) `|` set_of_itv (Interval b +oo%O).
Proof.
move: a b => [[] a|[]] [[] b|[]].
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itvC_BSide_BSide.
by rewrite !set_of_itvE setUT setC0.
by rewrite set_of_itvC_BSide_pinfty !set_of_itvE setU0.
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itvC_BSide_BSide.
by rewrite set_of_itv_empty_set0 // setC0 !set_of_itvE setUT.
by rewrite set_of_itvC_BSide_pinfty !set_of_itvE setU0.
by rewrite set_of_itvC_minfty_BSide !set_of_itvE set0U.
by rewrite set_of_itvC_minfty_BSide !set_of_itvE set0U.
by rewrite set_of_itvE setC0 set0U set_of_itvE.
by rewrite !set_of_itvE setCT set0U.
by rewrite !set_of_itvE setTU setC0.
by rewrite !set_of_itvE setTU setC0.
by rewrite set_of_itv_empty_set0 // setC0 !set_of_itvE setTU.
by rewrite !set_of_itvE setC0 setU0.
Qed.

Definition set_of_itvC := (set_of_itvC_minfty_BSide,
                           set_of_itvC_BSide_pinfty,
                           set_of_itvC_Interval).

Lemma itv_meetE (i j : interval R) :
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

End set_of_itv_realDomainType.

Section set_of_itv_numFieldType.
Variable R : numFieldType.

Lemma set_of_itv_empty_eq0 (a b : itv_bound R) :
  (set_of_itv (Interval a b) == set0) = ~~ (a < b)%O.
Proof.
apply/idP/idP => [/eqP|]; last by move=> ab; rewrite set_of_itv_empty_set0.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite !set_of_itvE/=.
- by rewrite predeqE => /(_ a)/=; rewrite lexx /= => -[] /negP.
- by rewrite predeqE => /(_ a)/=; rewrite lexx /= => -[] /negP.
- by rewrite predeqE => /(_ a)/=; rewrite lexx /= => -[] /negP.
- move=> i0; apply/negP => ab; move: i0.
  rewrite predeqE => /(_ ((a + b) / 2))/=; rewrite !midf_lt //= => -[+ _].
  exact.
- by rewrite predeqE => /(_ b)/=; rewrite lexx andbT /= => -[] /negP.
- by rewrite predeqE => /(_ (a + 1))/=; rewrite ltr_addl ltr01 => -[] /negP.
- rewrite predeqE => /(_ (b - 1))/=; rewrite ltr_subl_addl ltr_addr ltr01.
  by case => /negP.
- by rewrite predeqE => /(_ b)/=; rewrite lexx => -[] /negP.
- by rewrite predeqE => /(_ 0)/= [+ _]; rewrite falseE; apply.
Qed.

Lemma set_of_itv_nonempty_lt (a b : itv_bound R) :
  set_of_itv (Interval a b) != set0 -> (a < b)%O.
Proof. by rewrite set_of_itv_empty_eq0 negbK. Qed.

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
- by move=> ab; rewrite predeqE.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- move=> ab; rewrite predeqE => r; split => // ir.
  by move: ab => /(_ r); rewrite in_itv /= inE ir.
- by move=> ab; rewrite predeqE.
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

Lemma hasNsup_pred0 (i : interval R) : i =i pred0 -> ~ has_sup (set_of_itv i).
Proof.
case: i => a b /= ab0; rewrite /has_sup not_andP; left.
exact/set0P/negP/negPn/eqP/set_of_itv_empty_pred0.
Qed.

Lemma hasNinf_pred0 (i : interval R) : i =i pred0 -> ~ has_inf (set_of_itv i).
Proof.
case: i => a b /= ab0; rewrite /has_inf not_andP; left.
exact/set0P/negP/negPn/eqP/set_of_itv_empty_pred0.
Qed.

End set_of_itv_numFieldType.

Lemma non_empty_bnd1 (R : numFieldType) (s : seq (interval R)) :
  all (fun j => [set x | x \in j] != set0 :> set _) s ->
  forall i, i \in s -> i.1 != +oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo.
move: si; rewrite boo => /sne/negP; apply.
by rewrite set_of_itv_empty_eq0 // -leNgt.
Qed.

Lemma non_empty_bnd2 (R : numFieldType) (s : seq (interval R)) :
  all (fun x => set_of_itv x != set0) s ->
  forall i, i \in s -> i.2 != -oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo.
move: si; rewrite boo => /sne/negP; apply.
by rewrite set_of_itv_empty_eq0 // lt_ninfty.
Qed.

Section itv_bound_lteE.
Variable R : numDomainType.

Lemma BLeft_ltE (x y : R) : (BLeft x < BLeft y)%O = (x < y).
Proof. by []. Qed.
Lemma BRight_leE (x y : R) : (BRight x <= BRight y)%O = (x <= y).
Proof. by []. Qed.
Lemma BRight_BLeft_leE (x y : R) : (BRight x <= BLeft y)%O = (x < y).
Proof. by []. Qed.
Lemma BLeft_BRight_ltE (x y : R) : (BLeft x < BRight y)%O = (x <= y).
Proof. by []. Qed.
Lemma BRight_BSide_ltE (x y : R) b : (BRight x < BSide b y)%O = (x < y).
Proof. by case: b. Qed.
Lemma BLeft_BSide_leE (x y : R) b : (BLeft x <= BSide b y)%O = (x <= y).
Proof. by case: b. Qed.

Definition itv_bound_lteE := (BLeft_ltE, BLeft_BRight_ltE, BRight_BSide_ltE,
  BLeft_BSide_leE, BRight_BLeft_leE, BRight_leE).

Lemma BSide_BRight_le (x y : R) b : (BSide b x <= BRight y)%O = (x <= y).
Proof. by case: b. Qed.
Lemma BSide_BLeft_le (x y : R) b : (BSide b x < BLeft y)%O = (x < y).
Proof. by case: b. Qed.
Lemma BSide_leE (x y : R) b : (BSide b x <= BSide b y)%O = (x <= y).
Proof. by case: b. Qed.
Lemma BSide_ltE (x y : R) b : (BSide b x < BSide b y)%O = (x < y).
Proof. by case: b. Qed.

End itv_bound_lteE.

Lemma ltBRight_le (R : realDomainType) (a : itv_bound R) (r : R) : (a < BRight r)%O -> (a <= BLeft r)%O.
Proof. by move: a => [[] a|[]]. Qed.

Lemma set_of_itv_split (R : realDomainType) (a c b : itv_bound R) : (a <= c <= b)%O ->
  set_of_itv (Interval a b) = set_of_itv (Interval a c) `|` set_of_itv (Interval c b).
Proof.
move=> /andP[ac cb]; rewrite predeqE => r; split.
- rewrite set_of_itv_mem itv_boundlr => /andP[ar rb].
  have [rc|cr] := leP (BRight r) c.
    by left; rewrite set_of_itv_mem itv_boundlr ar rc.
    by right; rewrite set_of_itv_mem itv_boundlr rb andbT ltBRight_le.
case; rewrite !set_of_itv_mem !itv_boundlr => /andP[].
by move=> -> /le_trans; apply.
by move=> + ->; rewrite andbT; apply le_trans.
Qed.

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

Lemma hasNubound_setT (R : realDomainType) : ~ has_ubound (@setT R).
Proof. by case=> x /(_ (x + 1) I); apply/negP; rewrite -ltNge ltr_addl. Qed.

Lemma hasNlbound_setT (R : realDomainType) : ~ has_lbound (@setT R).
Proof.
by case=> x /(_ (x - 1) I); apply/negP; rewrite -ltNge ltr_subl_addr ltr_addl.
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

Definition Mid (R : numDomainType) (i : interval R) : R :=
  match i with
  | Interval (BSide ba a) (BSide bb b) => (a + b) / 2
  | Interval -oo%O (BSide bb b) => b - 1
  | Interval (BSide ba a) +oo%O => a + 1
  | Interval -oo%O +oo%O => 0
  | _ => 0
  end.

Lemma mem_Mid (R : numFieldType) (i : interval R) : set_of_itv i != set0 ->
  Mid i \in i.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //=;
  rewrite set_of_itv_empty_eq0 negbK // ?itv_bound_lteE => ab; rewrite in_itv /=.
by rewrite midf_lt // andbT midf_le // ltW.
by rewrite midf_le // midf_le.
by rewrite ler_addl ler01.
by rewrite midf_lt // midf_lt.
by rewrite midf_lt // midf_le // ltW.
by rewrite ltr_addl ltr01.
by rewrite ltr_subl_addr ltr_addl.
by rewrite ler_subl_addr ler_addl.
Qed.

Lemma midf_in_itv ba bb (R : numFieldType) (a b : R) : a < b ->
  (a + b) / 2 \in Interval (BSide ba a) (BSide bb b).
Proof.
move=> ab; rewrite (@mem_Mid _ (Interval (BSide ba a) (BSide bb b))) //.
rewrite set_of_itv_empty_eq0 negbK.
by move: ba bb => [] [] //; rewrite itv_bound_lteE ltW.
Qed.

Lemma Mid_bnd2 (R : numFieldType) (i : interval R) : set_of_itv i != set0 ->
  forall b, (BSide b (Mid i) <= i.2)%O.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //=;
  rewrite set_of_itv_empty_eq0 negbK // ?itv_bound_lteE => ab; case; rewrite itv_bound_lteE.
by rewrite midf_le // ltW.
by rewrite midf_lt.
by rewrite midf_le.
by rewrite midf_le.
by rewrite midf_le // ltW.
by rewrite midf_lt.
by rewrite midf_le // ltW.
by rewrite midf_le // ltW.
by rewrite ler_subl_addl ler_addr.
by rewrite ltr_subl_addl ltr_addr.
by rewrite ler_subl_addl ler_addr.
by rewrite ler_subl_addl ler_addr.
Qed.

Lemma Mid_bnd1 (R : numFieldType) (i : interval R) : set_of_itv i != set0 ->
  forall b, (i.1 <= BSide b (Mid i))%O.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //=;
  rewrite set_of_itv_empty_eq0 negbK // ?itv_bound_lteE => ab; case; rewrite itv_bound_lteE.
by rewrite midf_le // ltW.
by rewrite midf_le // ltW.
by rewrite midf_le.
by rewrite midf_le.
by rewrite ler_addl.
by rewrite ler_addl.
by rewrite midf_lt.
by rewrite midf_le // ltW.
by rewrite midf_lt.
by rewrite midf_le // ltW.
by rewrite ltr_addl.
by rewrite ler_addl.
Qed.

Lemma BLeft_Mid_lt (R : numFieldType) (a b : itv_bound R) : (a < b)%O -> (BLeft (Mid (Interval a b)) < b)%O.
Proof.
move: b a => [[]b|[]] [[]a|[]] //=; rewrite ?itv_bound_lteE => ab.
by rewrite midf_lt.
by rewrite midf_lt.
by rewrite ltr_subl_addl ltr_addr.
by rewrite midf_le.
by rewrite midf_le // ltW.
by rewrite ler_subl_addl ler_addr.
Qed.

Lemma lt_BLeft_Mid (R : numFieldType) (a b : itv_bound R) : (a < b)%O -> (a < BRight (Mid (Interval a b)))%O.
Proof.
move: b a => [[]b|[]] [[]a|[]] //=; rewrite ?itv_bound_lteE => ab.
by rewrite midf_le // ltW.
by rewrite midf_lt.
by rewrite midf_le.
by rewrite midf_lt.
by rewrite ler_addl.
by rewrite ltr_addl.
Qed.

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
- by move=> _; rewrite set_of_itvE asboolF // asboolF.
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

Lemma set_of_itv_setT (R : realType) (i : interval R) :
  set_of_itv i = setT -> i = `]-oo, +oo[.
Proof.
have [i0 iT|i0 /(congr1 (@Rhull _))] := pselect (i =i pred0).
  exfalso.
  move/set_of_itv_empty_pred0 : i0; rewrite iT predeqE => /(_ 0).
  by case=> + _; exact.
rewrite set_of_itvK.
  by move=> ->; rewrite /Rhull asboolF // asboolF.
by rewrite inE; apply/negP => /asboolP.
Qed.

(* finite union of intervals *)
Definition ufint (R : numDomainType) (x : seq (interval R)) : set R :=
  \big[setU/set0]_(i <- x) (set_of_itv i).

Lemma ufintE (R : numDomainType) (x : seq (interval R)) :
  ufint x = \bigcup_(i in [set j | j \in x]) (set_of_itv i).
Proof. by rewrite bigcup_mkset. Qed.

Lemma ufintP (R : numDomainType) (s : seq (interval R)) x :
  ufint s x <-> (\bigcup_(i in [set j | j \in s]) (set_of_itv i)) x.
Proof. by rewrite -ufintE. Qed.

Lemma mem_ufint (R : numDomainType) (s1 s2 : seq (interval R)) :
  s1 =i s2 -> ufint s1 = ufint s2.
Proof.
move=> s12; rewrite 2!ufintE eqEsubset; split => x [i]; rewrite /mkset => + ix.
by rewrite s12 => ?; exists i.
by rewrite -s12 => ?; exists i.
Qed.

Lemma ufint_filter_neq0 (R : numDomainType) (s : seq (interval R)) :
  ufint [seq x <- s | set_of_itv x != set0] = ufint s.
Proof.
elim: s => // h t ih /=; case: ifPn => [h0|/negPn/eqP h0].
  by rewrite {1}/ufint big_cons -/(ufint _) ih {2}/ufint big_cons.
by rewrite ih {2}/ufint big_cons h0 set0U.
Qed.

Lemma ufint_set0 (R : numDomainType) (s : seq (interval R)) :
  all (fun i => set_of_itv i != set0) s -> ufint s = set0 -> s = [::].
Proof.
case: s => // h t /= /andP[h0 _].
by rewrite /ufint big_cons setU_eq0 => -[/eqP]; rewrite (negbTE h0).
Qed.

Notation bnd1 := (fun (i : interval _) => i.1).
Notation bnd2 := (fun (i : interval _) => i.2).

Section itv_cplt.
Variable R : realType.

Definition itv_cplt (s : seq (interval R)) : seq (interval R) :=
  let a' := -oo%O :: map bnd2 s in
  let b' := rcons (map bnd1 s) +oo%O in
  map (uncurry (@Interval _)) (zip a' b').

Lemma itv_cpltE1 (s : seq (interval R)) : ~` ufint s `<=` ufint (itv_cplt s).
Proof.
elim: s => [x _|[a1 b1] t ih x].
  by rewrite /itv_cplt /= /ufint big_seq1 set_of_itvE.
rewrite {1}/ufint big_cons -/(ufint _) setCU => -[] x_notin_h /ih {}ih.
set a := map bnd1 (Interval a1 b1 :: t).
set b := map bnd2 (Interval a1 b1 :: t).
rewrite (_ : itv_cplt _ = Interval -oo%O a1 ::
  map (uncurry (@Interval _)) (zip b (rcons (behead a) +oo%O))) //.
rewrite /ufint big_cons.
have : (set_of_itv (Interval -oo%O a1) `|` set_of_itv (Interval b1 +oo%O)) x.
  by rewrite set_of_itvC in x_notin_h.
case=> [xa1|/set_of_itv_mem xb1]; [by left|right].
have {ih} /ufintP[j] : ufint (map (uncurry (@Interval _))
  (zip (-oo%O :: behead b) (rcons (behead a) +oo%O))) x by [].
rewrite {1}/mkset => + /set_of_itv_mem jx.
rewrite {}/b {}/a.
move: t => [|[a2 b2] t /=]; first by rewrite big_seq1.
rewrite inE => /orP[/eqP jb2|jb2].
  apply/ufintP; exists (Interval b1 a2); first by rewrite /mkset inE eqxx.
  apply/set_of_itv_mem; rewrite itv_splitI xb1 /=.
  by move: jx; rewrite jb2 => /set_of_itv_mem.
by apply/ufintP; exists j => //; rewrite /mkset inE jb2 orbT.
Qed.

Lemma itv_cpltE2 (s : seq (interval R)) :
  path.sorted <=%O (map bnd2 s) /\ path.sorted <=%O (map bnd1 s) ->
  ufint (itv_cplt s) `<=` ~` ufint s.
Proof.
set a := map bnd1 s.
set b := map bnd2 s.
move=> [sorted_b sorted_a] x.
move=> /ufintP[/= j] /mapP[[b' a']] /(nthP (+oo%O, -oo%O)) => -[k'].
rewrite size_zip /= size_rcons 2!size_map minnn ltnS => k's.
rewrite nth_zip; last by rewrite size_rcons /= !size_map.
move=> -[kb' ka'] jba'.
move/set_of_itv_mem => xj /ufintP[] i si /set_of_itv_mem xi.
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

Definition itv_cplt_ne (s : seq (interval R)) :=
  [seq x <- itv_cplt s | set_of_itv x != set0].

Lemma itv_cplt_neE (s : seq (interval R)) :
  path.sorted <=%O (map bnd2 s) /\ path.sorted <=%O (map bnd1 s) ->
  ufint (itv_cplt_ne s) = ~` ufint s.
Proof. by move/itv_cpltE=> sE; rewrite /itv_cplt_ne ufint_filter_neq0 sE. Qed.

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

Lemma itv_diffE (i j : interval R) : ~ {subset j <= i} \/ ({subset j <= i} /\ bnd1 j = bnd1 i) ->
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
    case: ji => [ji|[ji j1i1]].
      exfalso.
      apply: ji => x; rewrite 2!itv_boundlr => /andP[j1x xj2].
      by rewrite (le_trans xj2 ji2) andbT (le_trans _ j1x) // ltW.
    by move: ji1; rewrite j1i1 ltxx.
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

(* Lemma itv_diffE (i j : interval R) : ~ {subset j <= i} ->
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
Qed.*)

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

Lemma disjoint_itvP {R : realFieldType} (i j : interval R) :
  disjoint_itv i j <-> itv_meet i j =i pred0.
Proof.
case: i j => [a b] [c d]; rewrite /disjoint_itv /= -itv_meetE; split.
  by move/eqP/set_of_itv_empty_pred0.
by move=> ij0; apply/eqP/set_of_itv_empty_pred0.
Qed.

Lemma lt_disjoint (R : numDomainType) (i j : interval R) :
  (forall x y, x \in i -> y \in j -> x < y) -> disjoint_itv i j.
Proof.
move=> ij; apply/eqP; rewrite predeqE => x; split => // -[].
move/set_of_itv_mem => xi /set_of_itv_mem xj.
by have := ij _ _ xi xj; rewrite ltxx.
Qed.

Lemma path_disjoint_setT_eq0 (R : numDomainType) (t : seq (interval R)) :
  all (fun x => set_of_itv x != set0) t ->
  path.path disjoint_itv `]-oo, +oo[ t ->
  t = [::].
Proof.
case: t => // h t /= /andP[/set0P[x hx] ne] /andP[hT]; exfalso.
by move: hT; rewrite /disjoint_itv; apply/negP/set0P; exists x.
Qed.

Section lt_itv.
Variable R : realFieldType.

Definition lt_itv (i j : interval R) := match i, j with
  | Interval i1 i2, Interval j1 j2 =>
    if (i1 < j1)%O then true else if i1 == j1 then (i2 < j2)%O else false
  end.

Lemma lt_itvE (i j : interval R) : lt_itv i j =
  if (bnd1 i < bnd1 j)%O then true
  else if bnd1 i == bnd1 j then (bnd2 i < bnd2 j)%O else false.
Proof. by move: i j => [? ?] []. Qed.

Definition le_itv i j := (i == j) || (lt_itv i j).

Lemma lt_itvxx a : lt_itv a a = false.
Proof. by case: a => ? ? /=; rewrite ltxx eqxx ltxx. Qed.

Lemma lt_itv_def b1 b2 : lt_itv b1 b2 = (b2 != b1) && le_itv b1 b2.
Proof.
rewrite /le_itv andb_orr eq_sym andNb /=; apply/idP/idP => [b1b2|/andP[]//].
rewrite andbC b1b2 /=; apply/negP => /eqP b2b1; move: b1b2.
by rewrite b2b1 lt_itvxx.
Qed.

Lemma le_itv_refl : reflexive le_itv.
Proof. by case=> a b; rewrite /le_itv eqxx. Qed.

Lemma le_itv_anti : antisymmetric le_itv.
Proof.
move=> /= [a b] [c d]; rewrite /le_itv => /andP[/orP[/eqP[-> -> //]|]].
rewrite /=; case: ifPn => [ac _ /orP[/eqP //|]|].
  by rewrite ltNge (ltW ac) /= eq_sym lt_eqF.
rewrite -leNgt le_eqVlt => /orP[/eqP ->{c}|ca]; last by rewrite gt_eqF.
by rewrite eqxx ltxx => bd /orP[/eqP[->//]|]; rewrite ltNge (ltW bd).
Qed.

Lemma lt_itv_trans : transitive lt_itv.
Proof.
move=> [k1 k2] [i1 i2] [j1 j2]; rewrite /lt_itv.
case: (ltgtP i1 k1) => // [ik1 _| <-{k1} ik2].
  case: (ltgtP k1 j1) => // [kj1 _|kj1]; last by rewrite -kj1 ik1.
  by rewrite (lt_trans ik1).
by case: (ltgtP i1 j1) => // _; apply: lt_trans.
Qed.

Lemma le_itv_trans : transitive le_itv.
Proof.
move=> y x z.
rewrite /le_itv => /orP[/eqP -> //|xy] /orP[/eqP <-|yz]; first by rewrite orbC xy.
by rewrite (lt_itv_trans xy yz) orbT.
Qed.

Definition le_itv_porderMixin :=
  LePOrderMixin lt_itv_def le_itv_refl le_itv_anti le_itv_trans.
Fact le_itv_display (disp : unit) : unit. Proof. exact. Qed.
Definition le_itv_porderType (disp : unit) :=
  POrderType (le_itv_display disp) (interval R) le_itv_porderMixin.

Lemma le_lt_trans_itv y x z : le_itv x y -> lt_itv y z -> lt_itv x z.
Proof. exact: (@le_lt_trans _ (le_itv_porderType _)). Qed.

Lemma lt_le_trans_itv y x z : lt_itv x y -> le_itv y z -> lt_itv x z.
Proof. exact: (@lt_le_trans _ (le_itv_porderType _)). Qed.

Lemma ltW_itv x y : lt_itv x y -> le_itv x y.
Proof. exact: (@ltW _ (le_itv_porderType _)). Qed.

Lemma total_le_itv : total le_itv.
Proof.
move=> [i1 i2] [j1 j2]; rewrite /le_itv /=.
case/boolP : (_ == _) => ij //=.
case: (ltgtP i1 j1) => //=; rewrite ?orbT // => ij1.
rewrite eq_sym (negbTE ij) /= -neq_lt; apply/negP => /eqP ij2.
by exfalso; move/negP : ij; apply; rewrite ij1 ij2.
Qed.

Definition le_itv_orderMixin :=
  LeOrderMixin lt_itv_def (fun _ _ => erefl) (fun _ _ => erefl)
               le_itv_anti le_itv_trans total_le_itv.
Fail Canonical le_itv_latticeType := LatticeType (interval R) le_itv_orderMixin.

Let lt_itv_lt (a b : interval R) : lt_itv a b -> disjoint_itv a b ->
  forall x y, x \in a -> y \in b -> x < y.
Proof.
move: a b => [i1 i2] [j1 j2].
rewrite /lt_itv; case: (ltgtP i1 j1) => // [ij1 _|].
- rewrite /disjoint_itv -itv_meetE => /eqP/set_of_itv_empty_pred0 ij0 x y.
  rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[j1y yj2].
  have [i2j1|i2j1] := leP i2 j1.
    by have := le_trans xi2 (le_trans i2j1 j1y).
  rewrite ltNge; apply/negP => yx.
  have /negP := ij0 y.
  apply; apply/itv_meet_mem; rewrite 2!itv_boundlr.
  by rewrite (le_trans (ltW ij1)) //= (le_trans _ xi2) // yj2 andbT j1y.
- move=> <-{j1} ij2; rewrite /disjoint_itv -itv_meetE => /eqP /set_of_itv_empty_pred0 => ij0 x y.
  rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[i1y yj2].
  rewrite ltNge; apply/negP => yx.
  have /negP := ij0 x.
  apply; apply/itv_meet_mem; split => //; rewrite itv_boundlr i1x //=.
  by rewrite (le_trans xi2) // ltW.
Qed.

Lemma lt_itv_le (a b : interval R) : le_itv a b ->
  disjoint_itv a b ->
  forall x y, x \in a -> y \in b -> x < y.
Proof.
move: a b => [i1 i2] [j1 j2].
move/orP => [/eqP[<-{j1} <-{j2}]|]; last exact: lt_itv_lt.
have [i1i2|i1i2 _ x y] := ltP i1 i2.
  move=> i1i20; exfalso; move/eqP: i1i20 => /eqP; apply/negP.
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
Arguments lt_itv_trans {R}.
Arguments le_itv_trans {R}.
Arguments total_le_itv {R}.
Arguments le_itv_refl {R}.
Arguments le_itv_anti {R}.

Lemma perm_eq_trivIset_new {T : eqType} (s1 s2 : seq (set T)) (D : set nat) :
  [set k | (k < size s1)%N] `<=` D -> perm_eq s1 s2 ->
  trivIset D (fun i => nth set0 s1 i) -> trivIset D (fun i => nth set0 s2 i).
Proof.
move=> s1D.
rewrite perm_sym => /(perm_iotaP set0)[s ss1 s12] /trivIsetP ts1.
apply/trivIsetP => i j Di Dj ij.
rewrite {}s12 {s2}; have [si|si] := ltnP i (size s); last first.
  by rewrite (nth_default set0) ?size_map// set0I.
rewrite (nth_map O) //; have [sj|sj] := ltnP j (size s); last first.
  by rewrite (nth_default set0) ?size_map// setI0.
rewrite (nth_map O) // ts1 //.
  apply s1D; rewrite /mkset.
  have : nth O s i \in iota 0 (size s1) by rewrite -(perm_mem ss1) mem_nth.
  by rewrite mem_iota leq0n add0n.
  apply s1D; rewrite /mkset.
  have : nth O s j \in iota 0 (size s1) by rewrite -(perm_mem ss1) mem_nth.
  by rewrite mem_iota leq0n add0n.
by rewrite nth_uniq // (perm_uniq ss1) iota_uniq.
Qed.

Lemma trivIset_sort (R : realFieldType) (s : seq (interval R)) (D : set nat) :
  [set k | (k < size s)%N] `<=` D ->
  trivIset D (fun i => set_of_itv (nth 0%O s i)) ->
  trivIset D (fun i => set_of_itv (nth 0%O (path.sort le_itv s) i)).
Proof.
move=> sD ts.
rewrite trivIset_set_of_itv_nth ?set_of_itvE//.
apply (@perm_eq_trivIset_new _ (map set_of_itv s)).
- by apply: subset_trans _ sD => /= i; rewrite size_map.
- by rewrite perm_map // perm_sym path.perm_sort.
- by rewrite -(@trivIset_set_of_itv_nth _ 0%O) ?set_of_itvE.
Qed.

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
  disjoint_itv y a ->
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
  move/disjoint_itvP : ya => /=.
  rewrite joinxx (meet_l (ltW y2a2)) => /set_of_itv_empty_pred0/eqP.
  by rewrite set_of_itv_empty_eq0; apply/negP; rewrite negbK (lt_le_trans a1b1).
case: (ltgtP y1 a1) => [y1a1 ab ya a2b2 _ _| // |<-{a1} ab ya a2b2 y2a2 y2b2].
  rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite y1a1.
  rewrite lexx leNgt a2b2 /=; case: ifPn => //.
  rewrite -leNgt ge_pinfty => /eqP y1oo.
  by move: y1a1; rewrite y1oo.
rewrite /itv_diff; case: ifPn => [_|ab0]; first by rewrite ltxx eqxx.
rewrite lexx leNgt a2b2 /=; case: ifPn => //.
rewrite -leNgt ge_pinfty => /eqP y1oo.
exfalso.
move/eqP : ab0; apply.
by rewrite /= y1oo join_r // set_of_itv_empty_set0.
Qed.

Lemma le_itv_itv_diff0 (a b : interval R) : set_of_itv a = set0 -> le_itv a (itv_diff a b).
Proof.
move=> a0; apply/orP; left.
by rewrite /itv_diff itv_meetE ifT // a0 set0I.
Qed.

Lemma le_itv_itv_diff (y : interval R) a b :
  ~ {subset b <= a} ->
  disjoint_itv y a ->
  le_itv a b -> le_itv y a -> le_itv y b ->
  le_itv y (itv_diff a b).
Proof.
move=> ba ya0; rewrite {1}/le_itv => /orP[/eqP[ab]|ab].
  by exfalso; move: ba; rewrite -ab; exact.
rewrite {1}/le_itv => /orP[/eqP ya|ya].
  move: ya0; rewrite {}ya {y} => aa0.
  have [[x xa] _|/set0P/negP/negPn/eqP a0 _] := pselect (set_of_itv a !=set0).
    by exfalso; move: aa0; apply/negP/set0P; exists x.
  exact: le_itv_itv_diff0.
move/orP => [/eqP yb|yb].
by move: ya; rewrite yb => /(lt_itv_trans _ _ _ ab); rewrite lt_itvxx.
by apply/orP; right; exact: lt_itv_itv_diff.
Qed.

End lt_itv_diff.

Lemma mask_second (T : Type) (b : T) a t :
  a :: t = mask (true :: false :: nseq (size t) true) [:: a, b & t].
Proof. by rewrite /= mask_true. Qed.

Section lt_itv_disjoint.
Variable R : realType.

Lemma nonempty_sorted_disjoint_itv h (t : seq (interval R)) :
  all (fun x => set_of_itv x != set0) t ->
  path.sorted le_itv (h :: t) ->
  path.path disjoint_itv h t ->
  (forall c, c \in t -> disjoint_itv h c).
Proof.
elim: t h => [h t0 _ _ c //|b t ih a t0 /= /andP[lt_ab lt_bt] /andP[dis_ab dis_bt] c].
rewrite inE => /orP[/eqP ->{c} //|ct]; apply: ih => //.
- by move: t0; rewrite /= => /andP[].
- by rewrite (mask_second b) (path.sorted_mask (@le_itv_trans _)) //= lt_ab.
- case: t => [//|d t] in t0 lt_bt dis_bt ct *.
  move: dis_bt; rewrite [in X in X -> _]/= => /andP[dis_bd dis_dt].
  rewrite /= {}dis_dt andbT.
  move: (lt_itv_le lt_ab dis_ab) => {}lt_ab.
  move/andP : lt_bt => [+ _] => /lt_itv_le/(_ dis_bd) lt_bd.
  apply/lt_disjoint => x y xa yd.
  have [z bz] : set_of_itv b !=set0.
    by move/allP : t0 => /(_ b); rewrite mem_head => /(_ erefl)/set0P.
  by rewrite (@lt_trans _ _ z _ _ (lt_ab _ _ _ _) (lt_bd _ _ _ _)).
Qed.

Lemma nonempty_sorted_disjoint_itv_trivIset h (t : seq (interval R)) :
  all (fun x => set_of_itv x != set0) t ->
  path.sorted le_itv (h :: t) ->
  path.path disjoint_itv h t ->
  trivIset setT (fun i => set_of_itv (nth 0%O (h :: t) i)).
Proof.
elim: t h => //= [h t0 _ _|b t ih a /andP[b0 t0] /andP[lt_ab lt_bt] /andP[dis_ab dis_bt]].
  apply/trivIsetP => i j _ _ ij.
  case: i => [|i] /= in ij *.
    case: j => [|j] //= in ij *.
    by rewrite nth_nil set_of_itvE setI0.
  by rewrite nth_nil set_of_itvE set0I.
apply/trivIsetP => i j _ _; move: i j.
move=> [|i] [|j] //= ?.
- have [jbt|btj] := ltP j (size (b :: t)).
    apply/eqP/(@nonempty_sorted_disjoint_itv _ (b :: t)) => //=.
    by rewrite b0.
    by rewrite lt_ab.
    by rewrite dis_ab.
    by rewrite mem_nth.
  by rewrite nth_default // set_of_itvE setI0.
- have [ibt|bti] := ltP i (size (b :: t)).
    rewrite setIC.
    apply/eqP/(@nonempty_sorted_disjoint_itv _ (b :: t)) => //=.
    by rewrite b0.
    by rewrite lt_ab.
    by rewrite dis_ab.
    by rewrite mem_nth.
  by rewrite nth_default // set_of_itvE set0I.
- by have /trivIsetP := ih b t0 lt_bt dis_bt; apply.
Qed.

Lemma trivIset_disjoint h (t : seq (interval R)) :
  trivIset setT (fun i => set_of_itv (nth 0%O (h :: t) i)) ->
  path.path disjoint_itv h t.
Proof.
elim: t h => // t1 t2 ih h /= /trivIsetP tsht1t2.
apply/andP; split.
  by move: (tsht1t2 O 1%N Logic.I Logic.I erefl) => /= /eqP.
apply ih => //; apply/trivIsetP => i j _ _ ij.
by move: (tsht1t2 i.+1 j.+1 Logic.I Logic.I); apply.
Qed.

Lemma path_disjoint_pinfty_eq0 (t : seq (interval R)) j :
  all (fun x => set_of_itv x != set0) t ->
  path.path lt_itv (Interval j +oo%O) t ->
  path.path disjoint_itv (Interval j +oo%O) t ->
  t = [::].
Proof.
case: t => // h t ne.
case: j => [b r|[]]; last 2 first.
  by move=> _; apply: path_disjoint_setT_eq0.
  rewrite /=; case: h => h1 h2 in ne *.
  by rewrite gt_pinfty if_same.
case: h => h1 h2 /= in ne *.
rewrite gt_pinfty if_same.
case: ifPn => //= rh1 ht /andP[rooh Hdis].
exfalso.
move: rooh; apply/negP/set0P; rewrite -itv_meetE /=.
rewrite joinEtotal maxElt rh1 meetEtotal minElt /=.
by case/andP : ne => /set0P.
Qed.

Lemma sorted_le_itv_bound (s : seq (interval R)) :
  all (fun x => set_of_itv x != set0) s ->
  path.sorted le_itv s ->
  path.path disjoint_itv (head 0%O s) (behead s) ->
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
      by move/and3P : ne => [_ /set0P].
    exists x; split => //.
    apply/set_of_itv_mem; rewrite itv_boundlr.
    move/set_of_itv_mem : t11t12x; rewrite itv_boundlr => /andP[t11x xt12].
    by rewrite (le_trans (ltW _) t11x) // (le_trans xt12) // ltW.
  apply: (proj1 (ih _ _ _)).
  by move/andP : ne => [].
  by case/andP : ht => ? ht.
  by rewrite /=; move/andP : Hdis => // -[].
apply/andP; split.
  move/andP : ht => -[] /orP[/eqP[<-//]|].
  by rewrite /lt_itv; case: ltgtP.
apply: (proj2 (ih _ _ _)).
by move/andP : ne => [].
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
  rewrite /ufint 3!big_cons setUA; congr setU.
  by rewrite setUC; apply/esym/setUidPl/itv_set_of_itv_subset.
case: (pselect _) => ji.
  rewrite /= ih //; last by rewrite (mask_second j) (path.sorted_mask le_itv_trans).
  rewrite /ufint 3!big_cons setUA; congr setU.
  by apply/esym/setUidPl/itv_set_of_itv_subset.
rewrite {1}/ufint (big_cons _ _ _ (decompose (j :: tl))).
rewrite -/(ufint (decompose (j :: tl))) ih //; last first.
  by move: Hsort => /andP[].
rewrite {2}/ufint big_cons -/(ufint _).
rewrite /ufint big_cons !setUA; congr (_ `|` _).
have [i0|/set0P/negP/negPn/eqP i0] := pselect (set_of_itv i !=set0); last first.
  move/itv_set_of_itv_subset in ij.
  by exfalso; apply: ij; rewrite i0.
rewrite itv_diffE //; last by left.
rewrite eqEsubset; split.
  apply: subsetU; last by move=> x; right.
  by move=> x ix; left; case: ix.
move=> x [ix|jx]; last by right.
by have [jx|jx] := pselect ((set_of_itv j) x); [right|left].
Qed.

Lemma decompose_nonempty (s : seq (interval R)) :
  all (fun i => set_of_itv i != set0) s ->
  all (fun i => set_of_itv i != set0) (decompose s).
Proof.
move sn : (size s) => n; elim: n s sn => [|n ih [//|i [|j tl]] ].
  by move=> s /size0nil ->{} _; rewrite decompose_nil.
  by move=> _ i0; rewrite decompose_one.
move=> [tln] /= /and3P[i0 j0 ne]; rewrite decompose_two.
case: pselect => ij; first by rewrite ih //= ne andbT.
case: pselect => ji; first by rewrite ih //= ne andbT.
apply/allP=> t; rewrite inE => /orP[/eqP ->|].
  rewrite itv_diffE; last by left.
  suff : exists x, set_of_itv i x /\ ~ set_of_itv j x.
    by case=> x [? ?]; apply/set0P; exists x.
  apply/not_existsP => xij; apply ij; apply/itv_set_of_itv_subset => x ix.
  by have /not_andP[//|/contrapT] := xij x.
by move: t; apply/allP; rewrite ih //= ne andbT.
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
  by move=> c cjtl; rewrite tc // inE cjtl orbT.
case: pselect => // ji.
  apply ih; first by rewrite /= tln.
    by rewrite (mask_second j) (path.sorted_mask le_itv_trans).
  move=> c; rewrite inE => citl.
  by rewrite tc // !inE orbCA citl orbT.
rewrite /=; apply/andP; split.
  apply/eqP; rewrite itv_diffE; last by left.
  by rewrite setDE setIA (eqP (tc _ _)) ?set0I // mem_head.
apply ih; first by rewrite /= tln.
  by apply: (path.subseq_sorted le_itv_trans) H; exact: subseq_cons.
move=> c cjtl.
apply/eqP; rewrite itv_diffE; last by left.
move: cjtl; rewrite inE => /orP[/eqP ->|ctl].
  by rewrite setDE -setIA setICl setI0.
rewrite predeqE => x; split => // -[].
rewrite setDE => -[] /set_of_itv_mem ix /set_of_itv_mem/negP jx /set_of_itv_mem cx.
have jc : le_itv j c.
  move: ctl.
  rewrite -sub1seq.
  move/path.subseq_path_in => /(_ le_itv j) /=; rewrite andbT; apply => //.
    by move=> ? ? ? ? ? ?; exact: le_itv_trans.
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
  by rewrite (mask_second j) (path.sorted_mask le_itv_trans).
rewrite /=.
apply path_disjoint_itv_decompose.
  by move: H => /= /andP[].
move=> c cjtl.
apply/eqP; rewrite itv_diffE; last by left.
move: cjtl.
rewrite inE => /orP[/eqP ->|ctl].
  by rewrite setDE -setIA setICl setI0.
rewrite predeqE => x; split => // -[].
rewrite setDE => -[] /set_of_itv_mem ix /set_of_itv_mem/negP jx /set_of_itv_mem cx.
have jc : le_itv j c.
  move: ctl.
  rewrite -sub1seq.
  move/path.subseq_path_in => /(_ le_itv j) /=; rewrite andbT; apply => //.
    by move=> ? ? ? ? ? ?; exact: le_itv_trans.
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
case; first by move=> _ y _ _; rewrite decompose_nil.
move=> a [|b t]; first by move=> /= n1 y _; by rewrite decompose_one /= andbT.
move=> /=; rewrite ltnS => tn y /andP[ab bt] /and3P[ya yb yt].
rewrite decompose_two.
case: pselect => [sab|sab].
  apply ih => //; apply/allP => z.
  rewrite inE => /orP[/eqP -> //| zt].
  by move/allP : yt; apply.
case: pselect => sba.
  apply ih => //.
  - rewrite (mask_second b).
    apply (path.path_mask le_itv_trans) => //.
    by rewrite /= ab.
  - apply/allP => z.
    rewrite inE => /orP[/eqP -> //|zt].
    by move/allP : yt; apply.
apply/allP => z.
rewrite inE => /orP[/eqP ->{z}|zbt]; last first.
  have : all (fun x : interval R => le_itv y x && (disjoint_itv y x)) (decompose (b :: t)).
    apply ih => //; apply/allP => u.
    rewrite inE => /orP[/eqP -> //|ut].
    by move/allP : yt; apply.
  by move/allP; apply.
apply/andP; split.
  apply le_itv_itv_diff => //.
  by move/andP : ya => -[].
  by move/andP : ya => -[].
  by move/andP : yb => -[].
rewrite /disjoint_itv itv_diffE; last by left.
apply/eqP; apply: (@subsetI_eq0 _ _ (set_of_itv y)_ (set_of_itv a)) => //.
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
  rewrite (mask_second b).
  by apply (path.path_mask le_itv_trans).
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
    apply/eqP; rewrite itv_diffE; last by left.
    by rewrite setDE -setIA setICl setI0.
  apply/allP => z zt.
  apply/andP; split.
    rewrite (@le_itv_trans _ b) //.
      apply le_itv_diff => //.
      by move: abt => /= /andP[].
    move: abt => /= /andP[_ bt''].
    by move/path.order_path_min : bt'' => /(_ le_itv_trans) /allP; apply.
  rewrite /disjoint_itv itv_diffE; last by left.
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
       have : path.path le_itv (Interval b1 b2) t by [].
       by move/path.order_path_min => /(_ le_itv_trans)/allP; apply.
     rewrite /le_itv => /orP[/eqP[ <- //]|/=].
     by case: ltgtP.
   rewrite leNgt; apply/negP => b2x.
   case/andP : xa => xa1 xa2.
   apply: ba => u.
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
  all (fun x => set_of_itv x != set0) s ->
  trivIset setT (fun i => set_of_itv (nth 0%O (decompose s) i)).
Proof.
move=> sorteds smem0.
have [/eqP|s0] := boolP (size (decompose s) == 0%N).
  move/size0nil => ->; apply/trivIsetP => /= i j _ _ ij.
  by rewrite nth_nil set_of_itv_empty_set0 // set0I.
have head_behead : decompose s = head 0%O (decompose s) :: behead (decompose s).
  by move: s0; case: (decompose s).
rewrite head_behead.
apply: nonempty_sorted_disjoint_itv_trivIset.
by have := decompose_nonempty smem0; rewrite head_behead /= => /andP[].
by rewrite -head_behead sorted_decompose.
suff : path.path disjoint_itv 0%O (head 0%O (decompose s) :: behead (decompose s)).
  by rewrite /= => /andP[].
rewrite -head_behead path_disjoint_itv_decompose => // c cs.
by apply/eqP; rewrite set_of_itv_empty_set0 // set0I.
Qed.

Definition Decompose (s : seq (interval R)) :=
  decompose (path.sort le_itv [seq x <- s | set_of_itv x != set0]).

Lemma itv_cplt_decomposeE (s : seq (interval R)) :
  ufint (itv_cplt_ne (Decompose s)) = ~` ufint s.
Proof.
rewrite itv_cplt_neE.
  rewrite ufint_decompose.
    by rewrite ufint_sort_le_itv // ufint_filter_neq0.
  exact: (path.sort_sorted total_le_itv).
apply sorted_le_itv_bound.
- by rewrite decompose_nonempty // path.all_sort; apply/allP => i; rewrite mem_filter => /andP[].
- by apply: sorted_decompose; exact: (path.sort_sorted total_le_itv).
- by apply: path_disjoint_itv_decompose_head_behead; exact: (path.sort_sorted total_le_itv).
Qed.

Definition contiguous_itv (i j : interval R) : bool := bnd2 i == bnd1 j.

Definition cat_itv (i j : interval R) : interval R :=
  if contiguous_itv i j then
    match i, j with Interval x _, Interval _ y => Interval x y end
  else
    0%O.

Program Definition minimize' (s : seq (interval R))
  (f : forall s', (size s' < size s)%N -> seq (interval R)) : seq (interval R) :=
  match s with
  | [::] => [::] | [:: i] => [:: i]
  | [:: i, j & tl] => if contiguous_itv i j then
                      f (cat_itv i j :: tl) _
                    else
                      i :: f (j :: tl) _
  end.

Definition minimize : seq (interval R) -> seq (interval R) :=
  Fix wfr (fun _ => _ _) minimize'.

Lemma minimize'_ext (x : seq (interval R))
  (f g : forall y : seq (interval R), (size y < size x)%N -> seq (interval R)) :
    (forall (y : seq (interval R)) (p : (size y < size x)%N), f y p = g y p) ->
  minimize' f = minimize' g.
Proof.
move => fg; congr minimize'.
by apply functional_extensionality_dep => ?; apply functional_extensionality_dep.
Qed.

Lemma minimize_nil : minimize [::] = [::].
Proof. by rewrite /minimize Fix_eq //=; exact minimize'_ext. Qed.

Lemma minimize_one i : minimize [:: i] = [:: i].
Proof. rewrite /minimize Fix_eq //=; exact: minimize'_ext. Qed.

Lemma minimize_two i j tl :
  minimize [:: i, j & tl] = if contiguous_itv i j then minimize (cat_itv i j :: tl) else i :: minimize (j :: tl).
Proof.
rewrite {1}/minimize Fix_eq; last exact: minimize'_ext.
by move: i j => [i1 i2] [j1 j2] //=; case: pselect => //; case: pselect.
Qed.

Definition mDecompose (s : seq (interval R)) : seq (interval R) := minimize (Decompose s).

Definition decomposition_of (s : seq (interval R)) : seq (interval R) -> Prop :=
  fun x => [/\ path.sorted le_itv x,
           path.path disjoint_itv (head 0%O x) (behead x) &
           ufint x = ufint s ].

Lemma decomposition_of_Decompose (s : seq (interval R)) : decomposition_of s (Decompose s).
Proof.
split.
- by apply sorted_decompose; exact: (path.sort_sorted total_le_itv).
- by apply: path_disjoint_itv_decompose_head_behead; exact: (path.sort_sorted total_le_itv).
- rewrite ufint_decompose; last exact: (path.sort_sorted total_le_itv).
  by rewrite ufint_sort_le_itv ufint_filter_neq0.
Qed.

End decomposition.

Module ITVS.
Section itvs.
Variable R : realType.

Definition itvs_ringOfSets_carrier (x : set R) : Prop :=
  exists y : seq (interval R), x = ufint y (*/\ all (fun i => set_of_itv i != set0) y*).

Lemma itvs_ringOfSets_set0 : itvs_ringOfSets_carrier set0.
Proof. by exists fset0; rewrite /ufint big_nil. Qed.

Lemma itvs_ringOfSets_setU (A B : set R) :
  itvs_ringOfSets_carrier A -> itvs_ringOfSets_carrier B ->
  itvs_ringOfSets_carrier (A `|` B).
Proof.
move=> [a aA] [b bB]; exists (a ++ b)%fset.
rewrite eqEsubset; split => [r [Ar|Br]|r].
  move: Ar; rewrite aA => /ufintP[/= j ja jr].
  by apply/ufintP; exists j => //; rewrite /mkset mem_cat ja.
  move: Br; rewrite bB => /ufintP[/= j jb jr].
  by apply/ufintP; exists j => //; rewrite /mkset mem_cat jb orbT.
move/ufintP => [j]; rewrite /mkset mem_cat => /orP[ja|jb] jr.
by left; rewrite aA; apply/ufintP; exists j.
by right; rewrite bB; apply/ufintP; exists j.
(*move=> [a [aA a0]] [b [bB b0]]; exists (a `|` b)%fset => //; split.
  rewrite eqEsubset; split => [r [Ar|Br]|r].
    move: Ar; rewrite aA => /ufintP[/= j ja jr].
    by apply/ufintP; exists j => //; rewrite /mkset inE ja.
    move: Br; rewrite bB => /ufintP[/= j jb jr].
    by apply/ufintP; exists j => //; rewrite /mkset inE jb orbT.
  move/ufintP => [j]; rewrite /mkset inE => /orP[ja|jb] jr.
  by left; rewrite aA; apply/ufintP; exists j.
  by right; rewrite bB; apply/ufintP; exists j.
apply/allP => /= i; rewrite inE => /orP[ia|ib].
by move/allP : a0; apply.
by move/allP : b0; apply.*)
Qed.

Lemma itvs_ringOfSets_setC (A : set R) :
  itvs_ringOfSets_carrier A -> itvs_ringOfSets_carrier (~` A).
Proof.
move=> [a aA].
set s := itv_cplt_ne (Decompose a).
exists [fset x | x in s]%fset.
rewrite (@mem_ufint _ _ s) //; last by move=> i; rewrite inE.
by rewrite /s itv_cplt_decomposeE aA.
(*move=> [a [aA a0]].
have [->|A0] := pselect (A = setT).
  by rewrite setCT; exists fset0; split => //; rewrite /ufint big_nil.
set s := itv_cplt_ne (Decompose a).
exists [fset x | x in s]%fset; split.
  rewrite (@mem_ufint _ _ s) //; last by move=> i; rewrite inE.
  by rewrite /s itv_cplt_decomposeE aA.
by apply/allP => i; rewrite inE /= /s /itv_cplt_ne mem_filter => /andP[].*)
Qed.

End itvs.

Section ring_of_sets_instance.
Variable R : realType.

HB.instance Definition itvs_ringOfSets :=
  @isRingOfSets.Build (Real.sort R)
    (@itvs_ringOfSets_carrier R)
    (@itvs_ringOfSets_set0 R) (@itvs_ringOfSets_setU R) (@itvs_ringOfSets_setC R).

Definition itvs_ringOfSetsType := [the ringOfSetsType of (Real.sort R)].

Goal measurable (@set0 R).
exact: measurable0.
Abort.

End ring_of_sets_instance.
End ITVS.

Lemma itv_subset1 (R : numDomainType) (i : interval R) c : {subset i <= `[c, c]} ->
  forall r, r \in i -> r = c.
Proof.
by move/itv_set_of_itv_subset; rewrite set_of_itvE => ir r /ir; rewrite -eq_le => /eqP.
Qed.

Lemma itv_subset1'_side_pinfty (R : numFieldType) b r (c : R) : ~ {subset Interval (BSide b r) +oo%O <= `[c, c]}.
Proof.
set i := Interval (BSide b r) +oo%O.
move=> ic; have : Mid i < Mid i + 1 by rewrite ltr_spaddr.
rewrite lt_neqAle => /andP[/negP r1 _]; apply/r1/eqP.
transitivity c.
  move/itv_subset1 : ic; apply.
  by rewrite mem_Mid // set_of_itv_empty_eq0.
apply/esym; move/itv_subset1 : ic; apply; rewrite in_itv /= andbT.
by case: b => /= in i r1 *; [rewrite -addrA ler_addl|rewrite -addrA ltr_addl].
Qed.

Lemma itv_subset1'_ninfty_side (R : numFieldType) b r (c : R) : ~ {subset Interval -oo%O (BSide b r) <= `[c, c]}.
Proof.
move=> ic; set i := Interval -oo%O (BSide b r).
have : Mid i - 1 < Mid i by rewrite ltr_subl_addr ltr_spaddr.
rewrite lt_neqAle => /andP[/negP r1 _]; apply/r1/eqP.
transitivity c.
  move/itv_subset1 : ic; apply.
  rewrite in_itv /=.
  case: b => /= in i r1 *.
  by rewrite -addrA -opprD ltr_subl_addl ltr_addr.
  by rewrite -addrA -opprD ler_subl_addl ler_addr.
apply/esym; move/itv_subset1 : ic; apply.
by rewrite mem_Mid // set_of_itv_empty_eq0.
Qed.

Lemma itv_subset1' (R : numFieldType) (i : interval R) c : {subset i <= `[c, c]} ->
  i =i pred0 \/ i = `[c, c].
Proof.
move=> ic; have [[r ir]|/set0P/negP/negPn/eqP i0] := pselect (set_of_itv i !=set0); last first.
  by left => r; apply/idP/idP => //; apply/negP; rewrite -(set_of_itv_mem i) i0.
move: i ic ir => [[[]a|[]] [[]b|[]]] //= ic ir.
- right; have ab : a < b.
    by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[ar rb]; rewrite (le_lt_trans ar).
  have : a < Mid `[a, b[ by rewrite midf_lt.
  rewrite lt_neqAle => /andP[/negP ab2 _]; exfalso; apply/ab2/eqP.
  transitivity c.
    by move/itv_subset1 : ic; apply; rewrite in_itv /= lexx ab.
  apply/esym; move/itv_subset1 : ic; apply.
  by rewrite mem_Mid // set_of_itv_empty_eq0 negbK.
- right; suff : a = c /\ b = c by move=> [-> ->].
  have ab : a <= b.
    by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[ar rb]; rewrite (le_trans ar).
  split.
    by move/itv_subset1 : ic; apply; rewrite in_itv /= lexx /=.
  by move/itv_subset1 : ic; apply; rewrite in_itv /= ab lexx.
- by left; apply itv_ge.
- by have := itv_subset1'_side_pinfty ic.
- left; exfalso.
  have : r < (r + b) / 2 by rewrite midf_lt //; move: ir; rewrite set_of_itv_mem in_itv /= => /andP[_ ].
  rewrite lt_neqAle => /andP[/negP rb2 _]; apply rb2; apply/eqP.
  transitivity c.
    move/itv_subset1 : ic; apply; rewrite in_itv /=.
    by move: ir; rewrite set_of_itv_mem !in_itv /=.
  apply/esym; move/itv_subset1 : ic; apply; rewrite in_itv /=.
  apply/andP; split.
    rewrite (@lt_le_trans _ _ r) //.
      by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[].
    rewrite midf_le // ltW //.
    by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[].
  rewrite midf_lt //.
  by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[].
- right; have ab : a < b.
    by move: ir; rewrite set_of_itv_mem in_itv /= => /andP[ar rb]; rewrite (lt_le_trans ar).
  have : Mid `]a, b] < b by rewrite midf_lt.
  rewrite lt_neqAle=> /andP[/negP ab2 _]; exfalso; apply/ab2/eqP.
  transitivity c.
    move/itv_subset1 : ic; apply.
    by rewrite in_itv /= midf_lt //= (midf_le (ltW _)).
  apply/esym; move/itv_subset1 : ic; apply.
  by rewrite in_itv /= lexx ab.
- by left; apply itv_ge.
- by have := itv_subset1'_side_pinfty ic.
- by have := itv_subset1'_ninfty_side ic.
- by have := itv_subset1'_ninfty_side ic.
- exfalso; have : r < r + 1 by rewrite ltr_spaddr.
  rewrite lt_neqAle => /andP[/negP r1 _]; apply/r1/eqP.
  transitivity c.
    by move/itv_subset1 : ic; apply; rewrite -set_of_itv_mem.
  by apply/esym; move/itv_subset1 : ic; apply; rewrite in_itv.
Qed.

Coercion ereal_of_itv_bound T (b : itv_bound T) : er T :=
  match b with BSide _ y => y%:E | +oo%O => +oo%E | -oo%O => -oo%E end.
Arguments ereal_of_itv_bound T !b.

Lemma le_erbnd (R : realDomainType) (a b : itv_bound R) : (a <= b)%O -> (a <= b)%E.
Proof.
move: a b => -[[] a|[]] [bb b|[]] //=; rewrite ?(lee_pinfty,lee_ninfty)//.
  by rewrite BLeft_BSide_leE lee_fin.
by case: bb => //; rewrite BRight_BLeft_leE => /ltW; rewrite lee_fin.
Qed.

Lemma lt_erbnd (R : realDomainType) (a b : itv_bound R) : (a < b)%E -> (a < b)%O.
Proof.
by move: a b => -[[] a|[]] [[] b|[]] //=;
  rewrite ?(lee_pinfty,lee_ninfty,lte_fin)// => ab; rewrite itv_bound_lteE ltW.
Qed.

Lemma interval_pred0_lee (R : realFieldType) (i : interval R) : i =i pred0 -> (i.2 <= i.1)%E.
Proof.
move/set_of_itv_empty_pred0.
by case: i => /= a b /eqP; rewrite set_of_itv_empty_eq0 -leNgt => /le_erbnd.
Qed.

Section conv_Rhull.
Variable R : realType.

Lemma N01 (t : R) : (0 <= t <= 1) = (0 <= 1 - t <= 1).
Proof.
apply/idP/idP => /andP[t0 t1]; apply/andP; split; first by rewrite subr_ge0.
by rewrite ler_subl_addr addrC -ler_subl_addr subrr.
by move: t1; rewrite ler_subl_addr addrC -ler_subl_addr subrr.
by move: t0; rewrite subr_ge0.
Qed.

Definition conv (t : R) (a b : R) : R := (1 - t) * a + t * b.

Lemma conv0 (a b : R) : conv 0 a b = a.
Proof. by rewrite /conv subr0 mul1r mul0r addr0. Qed.

Lemma conv1 (a b : R) : conv 1 a b = b.
Proof. by rewrite /conv subrr mul0r add0r mul1r. Qed.

Lemma convN (a b t : R) : conv t a b = conv (1 - t) b a.
Proof. by rewrite /conv opprB addrCA subrr addr0 addrC. Qed.

Lemma le_conv (a b t : R) : a <= b -> 0 <= t <= 1 -> a <= conv t a b <= b.
Proof.
move=> ab /andP[].
rewrite le_eqVlt => /orP[/eqP/esym ->{t} _|t0]; first by rewrite conv0 lexx.
rewrite le_eqVlt => /orP[/eqP ->{t0 t}|t1]; first by rewrite conv1 lexx andbT.
have t1t : 1 - t + t = 1 by rewrite subrK.
rewrite /conv; apply/andP; split.
  by rewrite -{1}(mul1r a) -{1}t1t [in X in X <= _]mulrDl ler_add // ler_pmul2l.
by rewrite -{2}(mul1r b) -{2}t1t [in X in _ <= X]mulrDl ler_add // ler_pmul2l // subr_gt0.
Qed.

Definition factor (a b x : R) := (x - a) / (b - a).

Lemma factor01 (a b x : R) : a != b -> a <= x -> x <= b -> 0 <= factor a b x <= 1.
Proof.
move=> ab ax xb; rewrite divr_ge0 // ?subr_ge0 // ?(le_trans ax) //=.
by rewrite ler_pdivr_mulr ?mul1r ?ler_sub// subr_gt0 lt_neqAle ab (le_trans ax).
Qed.

Lemma conv_factor (a b x : R) : a != b -> conv (factor a b x) a b = x.
Proof.
move=> ab; rewrite /conv -(@divff _ (b - a)) ?subr_eq0 1?eq_sym// -mulrBl.
rewrite opprB addrA subrK mulrAC (mulrAC (x - a)) -mulrDl 2!mulrBl.
rewrite -addrA (addrC (b * a)) -addrA (mulrC a b) subrK.
by rewrite -mulrN addrC -mulrDr -mulrA mulfV ?mulr1 // subr_eq0 eq_sym.
Qed.

Lemma conv_subset_Rhull (A : set R) :
  [set x | exists (a b t : R), [/\ A a, A b, 0 <= t <= 1 & x = conv t a b]]
    `<=` set_of_itv (Rhull A).
Proof.
move=> r -[a [b [t [Aa Ab /andP[t0 t1] ->{r}]]]].
have /is_intervalPle iRhullA := @is_interval_set_of_itv _ (Rhull A).
have [ab|/ltW ba] := leP a b.
  apply: (iRhullA a b); rewrite ?set_of_itv_mem; try exact/sub_Rhull.
  by rewrite le_conv // t0.
apply: (iRhullA b a); rewrite ?set_of_itv_mem; try exact/sub_Rhull.
by rewrite convN le_conv => //; rewrite -N01 t0.
Qed.

Lemma Rhull_subset_conv (A : set R) : A !=set0 -> set_of_itv (Rhull A) `<=`
  [set x | exists (a b t : R), [/\ A a, A b, 0 <= t <= 1 & x = conv t a b]].
Proof.
move=> A0 r; rewrite set_of_itv_mem /Rhull; set i : R := inf A; set s : R := sup A.
have [|] := boolP (`[< has_lbound A >]) => /asboolP lA.
- have [|]:= boolP (`[< has_ubound A >]) => /asboolP uA.
  + have [|] := boolP (`[< A i >]) => /asboolP Ai.
    * have [|] := boolP (`[< A s >]) => /asboolP As; rewrite in_itv /= => /andP[ir rs].
      - have [/eqP si|si] := boolP (i == s).
        + have /eqP <- : i == r by rewrite eq_le {2}si ir.
          by exists i, s, 0; rewrite conv0 lexx ler01.
        + by exists i, s, (factor i s r); rewrite factor01 // conv_factor.
      - pose e := s - r.
        have [u ? seu] : exists2 u, A u & s - e < u by apply sup_adherent; rewrite ?subr_gt0.
        have ? : i < u by rewrite (le_lt_trans _ seu)// (le_trans ir)// opprB addrCA subrr addr0.
        exists i, u, (factor i u r); rewrite factor01 ?conv_factor// ?lt_eqF//.
        by rewrite (le_trans _ (ltW seu))// /e opprB addrCA subrr addr0.
    * have [|] := boolP (`[< A s >]) => /asboolP As; rewrite in_itv /= => /andP[ir rs].
      - pose e := r - i.
        have [l ? lie] : exists2 l, A l & l < i + e by apply inf_adherent; rewrite ?subr_gt0.
        have ? : l < s by rewrite (lt_le_trans lie)// (le_trans _ rs)// addrCA subrr addr0.
        exists l, s, (factor l s r); rewrite factor01// ?conv_factor// ?lt_eqF//.
        by rewrite (le_trans (ltW lie)) // /e addrCA subrr addr0.
      - pose e := ((r - i) `&` (s - r))%O.
        have [u ? seu] : exists2 u, A u & s - e < u by apply sup_adherent; rewrite ?ltxI 2?subr_gt0 ?ir.
        have [l ? lie] : exists2 l, A l & l < i + e by apply inf_adherent; rewrite ?ltxI 2?subr_gt0 ?ir.
        have ? : i + e <= r by rewrite -ler_sub_addl leIx lexx.
        have ? : r <= s - e by rewrite -ler_sub_addr opprK -ler_sub_addl leIx lexx orbT.
        have ? : l < u by rewrite (lt_le_trans lie)// (le_trans _ (ltW seu))// (@le_trans _ _ r).
        exists l, u, (factor l u r); rewrite factor01// ?conv_factor// ?lt_eqF//.
        by rewrite (le_trans (ltW lie)).
        by rewrite (le_trans _ (ltW seu)).
  + have [|] := boolP (`[< A i >]) => /asboolP Ai; rewrite in_itv /= andbT => ir.
    * have [u Au ru] : exists2 u, A u & r < u by move/has_ubPn : uA => /(_ r).
      have ? : i < u by rewrite (le_lt_trans ir).
      by exists i, u, (factor i u r); rewrite factor01// ?conv_factor // ?lt_eqF// ltW.
    * pose e := r - i.
      have [l ? lie] : exists2 l, A l & l < i + e by apply inf_adherent; rewrite ?subr_gt0.
      have [u ? ru] : exists2 u, A u & r < u by move/has_ubPn : uA => /(_ r).
      have ? : l < u by rewrite (lt_le_trans lie) // addrCA subrr addr0 ltW.
      have ? : l <= r by rewrite (le_trans (ltW lie)) // addrCA subrr addr0.
      by exists l, u, (factor l u r); rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
- have [|]:= boolP (`[< has_ubound A >]) => /asboolP uA; last move=> _.
  + have [|] := boolP (`[< A s >]) => /asboolP As; rewrite in_itv /= => rs.
    * have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
      have ? : l < s by rewrite (lt_le_trans lr).
      by exists l, s, (factor l s r); rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
    * pose e := s - r.
      have [u ? seu] : exists2 u, A u & s - e < u by apply sup_adherent; rewrite ?subr_gt0.
      have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
      have ? : l < u by rewrite (le_lt_trans _ seu)// (le_trans (ltW lr))// opprB addrCA subrr addr0.
      have ? : r <= u by rewrite (le_trans _ (ltW seu))// opprB addrCA subrr addr0.
      by exists l, u, (factor l u r); rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
  + have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
    have [u ? ru] : exists2 u, A u & r < u by move/has_ubPn : uA => /(_ r).
    have ? : l < u by rewrite (lt_trans lr).
    by exists l, u, (factor l u r); rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
Qed.

Lemma le_Rhull : {homo (@Rhull R) : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A; have [A0 B AB r|/set0P/negP/negPn/eqP ->{A} B _ r] := pselect (A !=set0); last first.
  by rewrite Rhull0 in_itv /= lt_asym.
move/(Rhull_subset_conv A0) => -[a [b [t [{A0} Aa Ab /andP[t0 t1] ->]]]].
by apply/conv_subset_Rhull; exists a, b, t; split => //; try exact/AB; rewrite t0.
Qed.

Lemma Rhull_pred0 (a : set R) : Rhull a =i pred0 -> a = set0.
Proof.
by move=> a0; rewrite predeqE => r; split => // /sub_Rhull; rewrite /mkset a0 inE.
Qed.

Lemma Rhull_involutive (a : set R) : Rhull (set_of_itv (Rhull a)) = Rhull a.
Proof.
have [/asboolP/Rhull_pred0 ->|a0] := boolP (`[< Rhull a =i pred0 >]).
  by rewrite Rhull0 set_of_itv_empty_set0 //= ?itv_bound_lteE -?leNgt // Rhull0.
have := @RhullK _ (set_of_itv (Rhull a)).
by rewrite inE => /(_ (@is_interval_set_of_itv _ _)); by rewrite set_of_itvK.
Qed.

End conv_Rhull.

Section hlength.
Variable R : realType.

Definition hlength {R : realType} (A : set R) : {ereal R} :=
  let i := Rhull A in (i.2 - i.1)%E.

Lemma hlength0 : hlength (set0 : set R) = 0%:E.
Proof. by rewrite /hlength Rhull0 /= subrr. Qed.

Lemma hlength_singleton (r : R) : hlength (set_of_itv `[r, r]) = 0%:E.
Proof.
rewrite /hlength /= asboolT // sup_closed_closed // {1}set_of_itvE lexx.
by rewrite asboolT // asboolT // inf_closed_closed // set_of_itvE lexx /= subrr.
Qed.

Lemma hlength_itv (i : interval R) :
  hlength (set_of_itv i) = if (i.2 > i.1)%E then (i.2 - i.1)%E else 0%:E.
Proof.
case: ltP => [i12|].
  rewrite /hlength set_of_itvK// inE; move: i12.
  by rewrite ltNge; apply: contra => /asboolP; exact: interval_pred0_lee.
rewrite le_eqVlt => /orP[|/lt_erbnd i12]; last first.
  by rewrite set_of_itv_empty_set0 ?hlength0// -leNgt ltW.
case: i => -[ba a|[|]] [bb b|[|]] //=.
- rewrite /= => /eqP[->{b}]; move: ba bb => -[] []; try
    by rewrite set_of_itv_empty_set0 ?hlength0 //= itv_bound_lteE -leNgt.
  by rewrite hlength_singleton.
- by move=> _; rewrite set_of_itvE hlength0.
- by move=> _; rewrite set_of_itvE hlength0.
Qed.

Lemma hlength_oo (i : interval R) : hlength (set_of_itv i) = +oo%E ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Proof.
rewrite hlength_itv; case: i => -[ba a|[]] [bb b|[]] //= => [|_|_|].
- by case: ifPn.
- by left; exists ba, a; right.
- by left; exists bb, b; left.
- by right.
Qed.

Lemma hlength_ge0 (i : interval R) : (0%:E <= hlength (set_of_itv i))%E.
Proof.
rewrite hlength_itv; case: ifPn => //; case: (i.1 : er _) => [r||].
by rewrite suber_ge0 => /ltW.
by rewrite ltNge lee_pinfty.
by case: (i.2 : er _) => //=; rewrite lee_pinfty.
Qed.
Local Hint Extern 0 ((0%:E <= hlength _)%E) =>
  solve[apply: hlength_ge0] : core.

Lemma le_hlength0 (a b : itv_bound R) : (b <= a)%O ->
  hlength (set_of_itv (Interval a b)) = 0%:E.
Proof.
move=> /= /le_erbnd ba; rewrite hlength_itv.
by case: ifPn => //; rewrite ltNge ba.
Qed.

Lemma hlength_Rhull (a : set R) : hlength (set_of_itv (Rhull a)) = hlength a.
Proof. by rewrite /hlength Rhull_involutive. Qed.

Lemma le_hlength_itv (i j : interval R) : {subset i <= j} ->
 (hlength (set_of_itv i) <= hlength (set_of_itv j))%E.
Proof.
set I := set_of_itv i; set J := set_of_itv j.
have [I0|/set0P/negP/negPn/eqP -> _] := pselect (I !=set0); last first.
  by rewrite hlength0 hlength_ge0.
have [J0|/set0P/negP/negPn/eqP J0] := pselect (J !=set0); last first.
  by move/itv_set_of_itv_subset; rewrite -/J J0 subset0 -/I; move/set0P/eqP : I0.
move=> /itv_set_of_itv_subset ij; apply lee_sub => /=.
- have [/asboolP ui|/asboolP ui] := boolP (`[< has_ubound I >]).
  + have [/asboolP uj /=|/asboolP uj] := boolP (`[< has_ubound J >]); last by rewrite lee_pinfty.
    by rewrite lee_fin le_sup // => r Ir; exists r; split => //; move : ij; apply.
  + have [/asboolP uj /=|//] := boolP (`[< has_ubound J >]); exfalso.
    by apply: ui; apply: subset_has_ubound uj.
- have [/asboolP lj /=|/asboolP lj] := boolP (`[< has_lbound J >]); last by rewrite lee_ninfty.
  have [/asboolP li /=|/asboolP li] := boolP (`[< has_lbound I >]).
    rewrite lee_fin ler_oppl opprK le_sup // -?has_inf_supN//.
    - by move=> r [r' Ir' <-{r}]; exists (- r'); split => //; exists r' => //; apply: ij.
    - by case: I0 => x Ix; exists (- x), x.
  by exfalso; apply: li; apply: subset_has_lbound lj.
Qed.

Lemma le_hlength : {homo (@hlength R) : A B / (A `<=` B) >-> (A <= B)%E}.
Proof.
by move=> a b /le_Rhull /le_hlength_itv; by rewrite (hlength_Rhull a) (hlength_Rhull b).
Qed.

End hlength.
Hint Extern 0 ((0%:E <= hlength _)%E) => solve[apply: hlength_ge0] : core.

Require Import integral.
(*TODO: move sigma_finite to measure.v *)
(* NB: PR in progress *)

Section seq_interval_bounds.
Variable R : realType.

Lemma le_itv_bnd1 (i j : interval R) : le_itv i j -> (i.1 <= j.1)%O.
Proof.
move=> /orP[/eqP ->//|].
by move: i j => [i1 i2] [j1 j2] /=; case: ltgtP => //.
Qed.

Lemma le_itv_bnd2 (i j : interval R) : le_itv i j -> set_of_itv j !=set0 ->
  disjoint_itv i j -> (i.2 <= j.2)%O.
Proof.
move: i j => [i1 i2] [j1 j2] /=.
rewrite /le_itv => /orP[/eqP[-> -> //]|] /=.
case: ltgtP => // [i1j1 _ j0 ij|->{i1} /ltW //].
rewrite leNgt; apply/negP => j2i2.
move/eqP : ij; apply/eqP/set0P.
by rewrite -itv_meetE /= (join_r (ltW _))// (meet_r (ltW _))//.
Qed.

Lemma le_itv_disjoint_bnd2_bnd1 (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  (i.2 <= j.1)%O.
Proof.
move=> i0 j0 le_ij dis_ij; rewrite leNgt; apply/negP => i1i.
move: (dis_ij); apply/negP/set0P.
move: (le_ij) => /orP[/eqP <-|]; first by rewrite setIid.
move: i1i.
have : (bnd1 i <= bnd1 j)%O by exact: le_itv_bnd1.
have i2j2 : (bnd2 i <= bnd2 j)%O by apply le_itv_bnd2.
rewrite le_eqVlt => /orP[/eqP i1j1 K1I2|I1K1 K1I2].
  rewrite lt_itvE i1j1 ltxx eqxx => {}I2K2.
  rewrite -itv_meetE (IntervalE i) (IntervalE j) /= i1j1 join_l // meet_l; last exact/ltW.
  by apply/set0P; rewrite set_of_itv_empty_eq0 negbK.
rewrite lt_itvE I1K1 => _.
rewrite -itv_meetE (IntervalE i) (IntervalE j) /= join_r; last exact/ltW.
by rewrite meet_l //; apply/set0P; rewrite set_of_itv_empty_eq0 negbK.
Qed.

Lemma le_itv_disjoint_bnd2Noo (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  bnd2 i != +oo%O.
Proof.
move=> i0 j0 ss ts.
have ii1 := le_itv_disjoint_bnd2_bnd1 i0 j0 ss ts.
apply/negP => /eqP ioo.
rewrite ioo ge_pinfty in ii1.
move/set0P : j0 => /negP; apply.
rewrite set_of_itv_empty_set0 // (eqP ii1).
by rewrite -leNgt bound_lex1.
Qed.

Lemma le_itv_disjoint_bnd2r (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  exists b r, bnd2 i = BSide b r.
Proof.
move=> i0 j0 les ts.
move i2E : (bnd2 i) => i2.
case: i2 => [b i2|[]] in i2E *.
- by exists b, i2.
- exfalso; move: i2E; apply/eqP.
  by rewrite (@non_empty_bnd2 _ [:: i]) //= ?andbT// ?inE //; exact/set0P.
- by exfalso; move: i2E; apply/eqP/(le_itv_disjoint_bnd2Noo _ j0).
Qed.

Lemma le_itv_disjoint_bnd1Noo (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  bnd1 j != -oo%O.
Proof.
move=> i0 j0 ss ts.
have ii1 := le_itv_disjoint_bnd2_bnd1 i0 j0 ss ts.
apply/negP => /eqP ioo.
rewrite ioo le_ninfty in ii1.
have : set_of_itv i == set0.
  by rewrite (IntervalE i) set_of_itv_empty_eq0 (eqP ii1) -leNgt.
exact/negP/set0P.
Qed.

Lemma le_itv_disjoint_bnd1r (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  exists b a, bnd1 j = BSide b a.
Proof.
move=> i0 j0 sle str.
move i1E : (bnd1 j) => i1.
case: i1 => [b i1|[]] in i1E *.
- by exists b, i1.
- by exfalso; move: i1E; apply/eqP/(@le_itv_disjoint_bnd1Noo i).
- exfalso; move: i1E; apply/eqP.
  move/set0P : j0; apply: contra => /eqP j1oo.
  by rewrite (IntervalE j) j1oo set_of_itv_empty_set0.
Qed.

Lemma le_itv_disjoint_contiguous (i j : interval R) :
  set_of_itv i !=set0 -> set_of_itv j !=set0 ->
  le_itv i j -> disjoint_itv i j ->
  is_interval (set_of_itv i `|` set_of_itv j) ->
  contiguous_itv i j.
Proof.
move=> ine jne sle str sin.
rewrite /contiguous_itv eq_le; apply/andP; split.
  exact: le_itv_disjoint_bnd2_bnd1.
rewrite leNgt; apply/negP=> i1i.
have [b [a ba]] := le_itv_disjoint_bnd2r ine jne sle str.
have [b' [a' ba']] := le_itv_disjoint_bnd1r ine jne sle str.
set x := (a + a') / 2.
move: i1i; rewrite ba ba' => aa'.
have aa'W : a <= a'.
  by move: b b' {ba' ba} aa' => [] [] /=; rewrite itv_bound_lteE // => /ltW.
have H1 : (set_of_itv i `|` set_of_itv j) x.
  set midi := Mid i.
  set midi1 := Mid j.
  move/is_intervalPle in sin; apply: (@sin midi midi1).
  - left.
    rewrite set_of_itv_mem mem_Mid //; exact/set0P.
  - right.
    rewrite set_of_itv_mem mem_Mid //; exact/set0P.
  - have /Mid_bnd2/(_ b) : set_of_itv i != set0.
      exact/set0P.
    rewrite ba BSide_leE -/midi => midia.
    have /Mid_bnd1/(_ b') : set_of_itv j != set0.
      exact/set0P.
    rewrite ba' BSide_leE -/midi1 => midi1a.
    rewrite (le_trans midia) /=; last by rewrite midf_le.
    by rewrite (le_trans _ midi1a) //= midf_le.
have aa's : Interval (BSide b a) (BSide b' a') \in itv_cplt [:: i; j].
  rewrite /itv_cplt; apply/mapP.
  exists (BSide b a, BSide b' a') => //.
  apply/(nthP (+oo%O, -oo%O)).
  exists 1%nat; first by rewrite size_zip.
  by rewrite !nth_zip //= -ba -ba'.
have : x \in ufint (itv_cplt [:: i; j]).
  rewrite /ufint -bigcup_mkset in_setE.
  exists (Interval (BSide b a) (BSide b' a')) => //.
  rewrite set_of_itv_mem /x -/(Mid (Interval (BSide b a) (BSide b' a'))).
  by rewrite mem_Mid // set_of_itv_empty_eq0 // negbK.
rewrite itv_cpltE; last first.
  rewrite /= !andbT; split.
  by apply le_itv_bnd2.
  by apply le_itv_bnd1.
by rewrite inE; apply; rewrite /ufint !big_cons big_nil setU0.
Qed.

End seq_interval_bounds.

Reserved Notation "[ 'disjoint' A & B ]".
Notation "[ 'disjoint' A & B ]" := (A `&` B == set0) : classical_set_scope.

Section AboutPartition.
Variable T I : choiceType.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

Fail Lemma partition_disjoint_bigcup (f : T -> R) (F : I -> set T)
  (K : set I) :
  (forall i j, i != j -> [disjoint F i & F j]) ->
  \big[op/idx]_(i <- \big[setU/set0]_(x in K) (F x)) f i =
  \big[op/idx]_(k <- K) (\big[op/idx]_(i <- F k) f i).

End AboutPartition.

Section seq_interval_rbnd.
Variable R : realType.

Definition real_of_bnd := fun (def : {ereal R}) x => match x with BSide _ y => y%:E | _ => def end.
Definition rbnd1 def i := real_of_bnd def (bnd1 i).
Definition rbnd2 def i := real_of_bnd def (bnd2 i).

Lemma erbnd2E (i : interval R) def : (set_of_itv i != set0) ->
   (hlength (set_of_itv i) < +oo)%E ->
  i.2 = rbnd2 def i :> er _.
Proof.
move: i => [[ba a|[]] [bb b|[]]] //=; do ?by rewrite ?set_of_itvE ?eqxx.
  by rewrite hlength_itv; move=> ab0; rewrite lte_pinfty //.
by rewrite hlength_itv/= ltxx.
Qed.

Lemma erbnd1E (i : interval R) def : (set_of_itv i != set0) ->
    (hlength (set_of_itv i) < +oo)%E ->
  i.1 = rbnd1 def i :> er _.
Proof.
move: i => [[ba a|[]] [bb b|[]]] //=; try by rewrite ?set_of_itvE ?eqxx.
  by rewrite hlength_itv; move=> ab0; rewrite lte_ninfty.
by rewrite hlength_itv/= ltxx.
Qed.

Lemma hlengthE' (i : interval R) def def' : (set_of_itv i != set0) ->
  (hlength (set_of_itv i) < +oo)%E ->
  (hlength (set_of_itv i) = rbnd2 def i - rbnd1 def' i)%E.
Proof.
rewrite hlength_itv.
move: i => [[ba a|[]] [bb b|[]]] //=; try by rewrite ?set_of_itvE ?eqxx.
- move=> ab0; rewrite lte_fin; case: ifPn => [ab _ //|].
  rewrite -leNgt le_eqVlt => /orP[/eqP ->|ab _]; first by rewrite subrr.
  exfalso.
  move/negP : ab0; apply.
  rewrite set_of_itv_empty_eq0 /= -leNgt.
  by move: ba bb => [] [] //; rewrite itv_bound_lteE // ltW.
- by rewrite lte_pinfty.
- by rewrite lte_ninfty.
Qed.

Lemma set_of_itv_empty_erbnd (i : interval R) :
  (i.2 < i.1)%E -> set_of_itv i == set0.
Proof.
case: i => -[ba a|[]] [bb b|[]] //=.
- rewrite lte_fin => ab; rewrite set_of_itv_empty_set0 //= -leNgt.
  by move: ba bb => [] [] //; rewrite itv_bound_lteE // ltW.
- by move=> _; rewrite set_of_itv_empty_set0.
- by move=> _; rewrite set_of_itv_empty_set0.
- by move=> _; rewrite set_of_itv_empty_set0.
Qed.

Lemma set_of_itvP (i j : interval R) : set_of_itv i = set_of_itv j :> set _ <-> i =i j.
Proof.
split => [ij x|ij].
- by apply/idP/idP; rewrite -set_of_itv_mem;
    [rewrite ij set_of_itv_mem | rewrite -ij set_of_itv_mem].
- by rewrite predeqE => r; split; rewrite set_of_itv_mem;
    [rewrite ij -set_of_itv_mem | rewrite -ij -set_of_itv_mem].
Qed.

Lemma set_of_itv0P (i : interval R) : set_of_itv i = set0 :> set _ <-> i =i pred0.
Proof. exact: set_of_itv_empty_pred0. Qed.

Lemma set_of_itv0 : set_of_itv (0%O : interval R) = 0%O :> set _.
Proof. by rewrite set_of_itvE. Qed.

Lemma hlength_itv0 (i : interval R) : i =i pred0 -> hlength (set_of_itv i) = 0%:E.
Proof. by move=> /set_of_itv0P ->; rewrite hlength0. Qed.

Lemma hlength_set (i j : interval R) : i =i j ->
  hlength (set_of_itv i) = hlength (set_of_itv j).
Proof. by move=> /set_of_itvP->. Qed.

Lemma disjoint_itv_Rhull (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B ->
  disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK // inE.
Qed.

Lemma Rhull_setU2 (A B : set R) : B !=set0 -> A `&` B = set0 ->
  is_interval A -> is_interval B -> lt_itv (Rhull A) (Rhull B) ->
  (Rhull (A `|` B)).2 = (Rhull B).2.
Proof.
move=> B0 AB0 iA iB AB /=.
have [|] := boolP (`[< has_ubound (A `|` B) >]) => /asboolP uAB; last first.
  rewrite asboolF //.
  apply: contra_not uAB => -[x Bx].
  exists x => z [Az|Bz]; last exact: Bx.
  case: B0 => b0 Bb0.
  rewrite (@le_trans _ _ b0) //; last exact: Bx.
  apply/ltW/(lt_itv_le (ltW_itv AB)) => //; try exact: sub_Rhull.
  by rewrite disjoint_itv_Rhull.
have uB : has_ubound B.
  case: uAB => x ABx.
  by exists x => y By; apply ABx; right.
rewrite (asboolT uB) // sup_setU //; last first.
  move=> a b Aa Bb.
  apply/ltW/(lt_itv_le (ltW_itv AB)) => //; try exact/sub_Rhull.
  by rewrite disjoint_itv_Rhull.
congr (BSide (~~ `[< _ >]) _).
rewrite propeqE; split; last by right.
case => // AsB.
exfalso.
move/set0P : B0 => /eqP; apply.
rewrite predeqE => x; split => // Bx.
have : sup B < x.
  apply: (lt_itv_le (ltW_itv AB)) => //; try exact: sub_Rhull.
  by rewrite disjoint_itv_Rhull.
by apply/negP; rewrite -leNgt; exact: sup_ub.
Qed.

Lemma Rhull_setU1 (A B : set R) : A !=set0 -> A `&` B = set0 ->
  is_interval A -> is_interval B -> lt_itv (Rhull A) (Rhull B) ->
  (Rhull (A `|` B)).1 = (Rhull A).1.
Proof.
move=> A0 AB0 iA iB AB.
rewrite /=.
have [|] := boolP (`[< has_lbound (A `|` B) >]) => /asboolP uAB; last first.
  rewrite asboolF //.
  apply: contra_not uAB => -[x Ax].
  exists x => y [Ay|By].
    by apply Ax.
  case: A0 => a0 Aa0.
  rewrite (@le_trans _ _ a0) //; first exact: Ax.
  apply/ltW/(lt_itv_le (ltW_itv AB)); try exact: sub_Rhull.
  by rewrite disjoint_itv_Rhull.
have lA : has_lbound A.
  case: uAB => x ABx.
  by exists x => y Ay; apply ABx; left.
rewrite (asboolT lA) // inf_setU //; last first.
  move=> a b Aa Bb.
  apply/ltW/(lt_itv_le (ltW_itv AB)) => //; try exact/sub_Rhull.
  by rewrite disjoint_itv_Rhull.
congr (BSide (`[< _ >]) _).
rewrite propeqE; split; last by left.
case => // AsB.
exfalso.
case: A0 => a0 Aa0.
have : a0 < inf A.
  apply: (lt_itv_le (ltW_itv AB)) => //; try exact: sub_Rhull.
  by rewrite disjoint_itv_Rhull.
by apply/negP; rewrite -leNgt; apply inf_lb.
Qed.

Lemma hlength_itvU (A B : set R) : A `&` B = set0 ->
    is_interval A -> is_interval B -> is_interval (A `|` B) ->
  hlength (A `|` B) = (hlength A + hlength B)%E.
Proof.
move=> AB0 iA iB iAUB.
have [A0|/set0P/negP/negPn/eqP ->] := pselect (A !=set0); last first.
  by rewrite set0U hlength0 add0e.
have [B0|/set0P/negP/negPn/eqP ->] := pselect (B !=set0); last first.
  by rewrite setU0 hlength0 adde0.
wlog : A B A0 B0 AB0 iA iB iAUB / lt_itv (Rhull A) (Rhull B).
  move=> H; have [/eqP AB|AB] := boolP (Rhull A == Rhull B).
      move/(congr1 set_of_itv) : AB AB0.
      rewrite RhullK ?inE// RhullK ?inE// => ->.
      by rewrite setIid; move/set0P/eqP : B0.
  have /orP[|] := total_le_itv (Rhull A) (Rhull B).
    by rewrite /le_itv (negbTE AB) orFb; exact: H.
  rewrite /le_itv eq_sym (negbTE AB) orFb => {}AB.
  by rewrite setUC H // 1?addeC// 1?setIC// 1?setU // setUC.
move=> AB.
have : contiguous_itv (Rhull A) (Rhull B).
  apply le_itv_disjoint_contiguous => //; try by rewrite RhullK ?inE.
  exact/ltW_itv.
  by rewrite disjoint_itv_Rhull.
  by rewrite RhullK ?inE// RhullK ?inE.
rewrite /contiguous_itv => /eqP A2B1.
rewrite /hlength A2B1 Rhull_setU2 // Rhull_setU1 // [in RHS]addeC ![in RHS]addeA.
congr (_ - _)%E.
rewrite subeK //.
destruct (Rhull B).1 as [b b1|[]] => //.
- exfalso.
  move/set0P : A0.
  move/negP; apply.
  rewrite -(@RhullK _ A) ?inE //.
  apply set_of_itv_empty_set0.
  by rewrite A2B1 -leNgt.
- exfalso.
  move: A2B1; apply/eqP.
  apply: (@le_itv_disjoint_bnd2Noo _ _ (Rhull B)) => //; try by rewrite RhullK ?inE.
  exact/ltW_itv.
  by rewrite disjoint_itv_Rhull.
Qed.

Lemma subset_bigcup_r T I (D : set I) :
  {homo (fun x : I -> set T => \bigcup_(i in D) x i) : F G /
     [set F i | i in D] `<=` [set G i | i in D] >-> F `<=` G}.
Proof.
move=> F G FG t [i Di Fit]; have := FG (F i).
by move=> /(_ (ex_intro2 _ _ _ Di erefl))[j Dj ji]; exists j => //; rewrite ji.
Qed.

Lemma eqbigcup_r T I (D : set I) (F G : I -> set T) :
  [set F i | i in D] = [set G i | i in D] ->
  \bigcup_(i in D) F i = \bigcup_(i in D) G i.
Proof. by rewrite 2!eqEsubset => -[FG GF]; split; apply: subset_bigcup_r. Qed.

Lemma bigcup1 {T : choiceType} I (D : set I) (F : I -> set T) :
  (forall i, D i -> F i = set0) -> \bigcup_(i in D) F i = set0.
Proof. by move=> DF0; apply/bigcup_empty; right. Qed.

Lemma cover_restr T I D' D (F : I -> set T) :
  D `<=` D' -> (forall i, D' i -> ~ D i -> F i = set0) ->
  cover D F = cover D' F.
Proof.
move=> DD' D'DF; rewrite /cover eqEsubset; split=> [r [i Di Fit]|r [i D'i Fit]].
- by have [D'i|] := pselect (D' i); [exists i | have := DD' _ Di].
- by have [Di|Di] := pselect (D i); [exists i | move: Fit; rewrite (D'DF i)].
Qed.

Lemma perm_subset_set_of_itv_nth (D : set nat) (s s' : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D -> perm_eq s s' ->
  [set set_of_itv (nth 0%O s i) | i in D] `<=`
    [set set_of_itv (nth 0%O s' i) | i in D].
Proof.
move=> sD ss' A [i Di iA].
have [/(mem_nth 0%O)|si] := ltnP i (size s); last first.
  move: iA; rewrite nth_default // => <-.
  by exists i => //; rewrite nth_default // -(perm_size ss').
move/perm_mem : (ss') => ->.
move/(nthP 0%O) => [j js' ji]; exists j; last by rewrite ji.
by apply sD; rewrite (perm_size ss').
Qed.

Lemma perm_set_of_itv_nth (D : set nat) (s s' : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D -> perm_eq s s' ->
  [set set_of_itv (nth 0%O s i) | i in D] =
    [set set_of_itv (nth 0%O s' i) | i in D].
Proof.
move=> sD ss'; rewrite eqEsubset; split; apply perm_subset_set_of_itv_nth => //.
by rewrite -(perm_size ss').
by rewrite perm_sym.
Qed.

Lemma cover_set_of_itv_nth_sort (D : set nat) (s : seq (interval R)) :
  [set k | (k < size s)%N] `<=` D ->
  cover D (fun i => set_of_itv (nth 0%O s i)) =
  cover D (fun i => set_of_itv (nth 0%O (sort le_itv s) i)).
Proof.
move=> sD; apply/eqbigcup_r/perm_set_of_itv_nth => //.
by rewrite perm_sym perm_sort.
Qed.

Lemma cover_set_of_itv_nthE (s : seq (interval R)) (D : set nat) :
  [set k | (k < size s)%N] `<=` D ->
  cover D (fun i => set_of_itv (nth 0%O s i)) =
    \big[setU/set0]_(i <- s) (set_of_itv i).
Proof.
move=> sD; rewrite eqEsubset; split => [r [i Di ri]|r].
- rewrite -bigcup_mkset; exists (nth 0%O s i) => //; apply/mem_nth.
  by rewrite ltnNge; apply: contraPN ri => si; rewrite nth_default.
- rewrite -bigcup_mkset => -[/= i /(nthP 0%O)[k ks <-{i} kr]]; exists k => //.
  exact: sD.
Qed.

(* NB: not used*)
Lemma all_nonempty_set_of_itv_nth_sort (s : seq (interval R)) :
  (forall i, (i < size s)%N -> set_of_itv (nth 0%O s i) !=set0) ->
  (forall i, (i < size s)%N-> set_of_itv (nth 0%O (sort le_itv s) i) !=set0).
Proof.
move=> sne i /= si.
have [u us ->] := perm_iota_sort le_itv 0%O s.
rewrite (nth_map 0%O); last by rewrite (perm_size us) size_iota.
apply sne.
have : nth O u i \in iota 0 (size s).
  by rewrite -(perm_mem us) mem_nth // (leq_trans si) // (perm_size us) size_iota.
by rewrite mem_iota leq0n add0n.
Qed.

Lemma hlengthUitv (A : set R) (s : seq (interval R)) :
  is_interval A ->
  cover setT (fun i => set_of_itv (nth 0%O s i)) = A ->
  trivIset setT (fun i => set_of_itv (nth 0%O s i)) ->
  hlength A = (\sum_(i <- s) hlength (set_of_itv i))%E.
Proof.
move=> Aitv AE ts.
have Fmap (s' : seq (interval R)) :
    (fun i => set_of_itv (nth 0%O s' i)) =
      (fun i => nth 0%O (map set_of_itv s') i).
  apply/funext => i; have [is'|is'] := ltnP i (size s').
    by rewrite (nth_map 0%O).
  by rewrite !nth_default ?size_map// set_of_itv0.
wlog : s ts AE / sorted le_itv s => [hwlog|].
  have /permPl pss := perm_sort le_itv s.
  rewrite -(perm_big _ pss); apply: hwlog; [exact: trivIset_sort|
    by rewrite -cover_set_of_itv_nth_sort|exact: (sort_sorted total_le_itv)].
elim: (s : seq _) => [|j {}s IHs]/= in A Aitv ts AE *.
  rewrite /cover bigcup1 in AE; last by move=> i _; rewrite nth_nil set_of_itvE.
  by rewrite !big_nil/= in AE * => _; rewrite -AE hlength0.
rewrite (path_sortedE le_itv_trans) => /andP[/allP/= j_small s_sorted].
set K := \big[setU/set0]_(j <- s) set_of_itv j.
have K_itv : is_interval K.
  move=> x z Kx Kz y /andP[xy yz].
  have: A y.
    apply: (Aitv x z); rewrite ?xy//;
      by rewrite -AE cover_set_of_itv_nthE// big_cons; right.
  rewrite -AE /= cover_set_of_itv_nthE// big_cons=> -[]//.
  move=> /set_of_itv_mem jy; move: Kx; rewrite /K.
  rewrite -bigcup_mkset => -[k/= ks /set_of_itv_mem kx].
  suff: x > y by case: ltgtP xy.
  apply: (lt_itv_le (j_small k ks)) => //.
  have /(nthP 0%O)[ik ik_small <-] := ks.
  rewrite /disjoint_itv; apply/eqP.
  by have /trivIsetP-/(_ 0%N ik.+1 I I isT) := ts.
transitivity (hlength (set_of_itv j) + hlength K)%E; last first.
  rewrite big_cons; congr (_ + _)%E; rewrite IHs// ?cover_set_of_itv_nthE//.
  by move=> i0 i1 _ _ /(ts i0.+1 i1.+1 I I)[].
rewrite -AE cover_set_of_itv_nthE// big_cons /= hlength_itvU//.
- rewrite big_distrr/= big1_seq => //= i /(nthP 0%O)[ii ii_lt <-].
  by apply: contraTeq isT => /set0P-/(ts 0%N ii.+1 I I).
- exact: is_interval_set_of_itv.
- by move: AE; rewrite cover_set_of_itv_nthE// big_cons => ->.
Qed.

(*Lemma hlengthUitv (A : set R) (s : seq (interval R)) :
  is_interval A ->
  all (fun x => set_of_itv x != set0) s ->
  trivIset setT (fun i => set_of_itv (nth 0%O s i)) ->
  A = \big[setU/set0]_(k <- s) set_of_itv k ->
  hlength A = (\sum_(i <- s) hlength (set_of_itv i))%E.
Proof.
move=> Aitv sne ts AE.
have Fmap (s' : seq (interval R)) :
   (fun i : nat => set_of_itv (nth 0%O s' i))
    = (fun i : nat => nth 0%O (map set_of_itv s') i).
  apply/funext => i; have [is'|is'] := ltnP i (size s').
    by rewrite (nth_map 0%O).
  by rewrite !nth_default ?size_map// set_of_itv0.
wlog : s sne ts AE / sorted le_itv s => [hwlog|].
  have /permPl pss := perm_sort le_itv s.
  rewrite -(perm_big _ pss); apply: hwlog;
    rewrite ?all_sort ?(perm_big _ pss) ?(sort_sorted total_le_itv)//.
  move: ts; rewrite !Fmap; apply: perm_eq_trivIset.
  by rewrite perm_map// perm_sym.
elim: (s : seq _) => [|j {}s IHs]/= in A Aitv sne ts AE *.
  by rewrite !big_nil/= in AE * => _; rewrite AE hlength0.
rewrite (path_sortedE le_itv_trans) => /andP[/allP/= j_small s_sorted].
rewrite !big_cons in AE *; move: sne => /andP[j_neq0 sne].
set K := \big[setU/set0]_(j <- s) set_of_itv j.
have K_itv : is_interval K.
  move=> x z Kx Kz y /andP[xy yz].
  have: A y by apply: (Aitv x z); rewrite ?xy// AE; right.
  rewrite AE /= => -[]// /set_of_itv_mem jy; move: Kx; rewrite /K.
  rewrite -bigcup_mkset => -[k/= ks /set_of_itv_mem kx].
  suff: x > y by case: ltgtP xy.
  apply: (lt_itv_le (j_small k ks)) => //.
  have /(nthP 0%O)[ik ik_small <-] := ks.
  rewrite /disjoint_itv; apply/eqP.
  by have /trivIsetP-/(_ 0%N ik.+1 I I isT) := ts.
transitivity (hlength (set_of_itv j) + hlength K)%E; last first.
  by congr (_ + _)%E; rewrite IHs// => i0 i1 _ _ /(ts i0.+1 i1.+1 I I)[].
rewrite AE hlength_itvU// -?AE//; last exact: is_interval_set_of_itv.
rewrite big_distrr/= big1_seq => //= i /(nthP 0%O)[ii ii_lt <-].
  by apply: contraTeq isT => /set0P-/(ts 0%N ii.+1 I I).
Qed.*)

Lemma cover_hlength_set_of_itv (I J : seq (interval R)) :
  cover setT (fun i => set_of_itv (nth 0%O I i)) =
    cover setT (fun i => set_of_itv (nth 0%O J i)) ->
  trivIset setT (fun i => set_of_itv (nth 0%O J i)) ->
  forall i, i \in I ->
  hlength (set_of_itv i) = (\sum_(j <- J) hlength (set_of_itv (itv_meet i j)))%E.
Proof.
move=> IJ tJ i iI.
have h : set_of_itv i = \big[setU/set0]_(j <- J) (set_of_itv i `&` set_of_itv j).
  rewrite -big_distrr /= (big_nth 0%O) big_mkord.
  move/esym: (IJ); rewrite -(@cover_restr _ _ _ [set k | (k < size J)%N]) //; last first.
    by move=> k _ /negP; rewrite -leqNgt => Jk; rewrite nth_default // set_of_itvE.
  rewrite /cover -bigcup_ord => ->; apply/esym; rewrite setIidPl.
  move: iI => /(nthP 0%O)[k kI <-].
  exact: (@bigcup_sup _ _ k setT (fun i => set_of_itv (nth 0%O I i))).
rewrite h (@hlengthUitv _ [seq (itv_meet i j) | j <- J]) // ?big_map//.
- by rewrite -h; apply is_interval_set_of_itv.
- rewrite -(@cover_restr _ _ _ [set k | (k < size J)%N]) //; last first.
    by move=> k _ /negP; rewrite -leqNgt => Jk; rewrite nth_default ?size_map// set_of_itvE.
  rewrite /cover -bigcup_ord (big_nth 0%O) big_mkord.
  by apply eq_bigr => k _; rewrite (nth_map 0%O) // itv_meetE.
- rewrite -(@trivIset_restr _ _ _ [set k | (k < size J)%N]) //; last first.
    by move=> k _ /negP; rewrite -leqNgt => Jk; rewrite nth_default ?size_map// set_of_itvE.
  apply/trivIsetP => a b aJ bJ ab.
  rewrite (nth_map 0%O) // (nth_map 0%O) // !itv_meetE setIACA setIid.
  by move/trivIsetP : tJ => -> //; rewrite setI0.
Qed.

Lemma hlengthUset (I J : seq (interval R)) :
  cover setT (fun i => set_of_itv (nth 0%O I i)) =
    cover setT (fun i => set_of_itv (nth 0%O J i)) ->
  trivIset setT (fun i => set_of_itv (nth 0%O I i)) ->
  trivIset setT (fun i => set_of_itv (nth 0%O J i)) ->
  (\sum_(i <- I) hlength (set_of_itv i) = \sum_(i <- J) hlength (set_of_itv i))%E.
Proof.
move=> IJ tI tJ.
rewrite big_seq_cond big_andbC/= [RHS]big_seq_cond [in RHS]big_andbC/=.
(under eq_bigr) => [i /(cover_hlength_set_of_itv IJ tJ) ->|]; first over.
rewrite /= exchange_big /=; apply/esym.
(under eq_bigr) => [j /(cover_hlength_set_of_itv (esym IJ) tI) ->|]; first over.
rewrite -big_seq; apply eq_bigr => j _; rewrite -big_seq.
by under eq_bigr do rewrite itv_meetC.
Qed.

End seq_interval_rbnd.

Section length_measure.
Variable R : realType.

Definition length (x : set R) : {ereal R} :=
 match pselect (ITVS.itvs_ringOfSets_carrier x) with
 | left e => (\sum_(i <- Decompose (projT1 (cid e))) hlength (set_of_itv i))%E
 | right _ => -oo%E
 end.

Lemma length_ge0 (X : set (ITVS.itvs_ringOfSetsType R)) :
  ITVS.itvs_ringOfSets_carrier X -> (0 <= length X)%E.
Proof.
move=> HX; rewrite /length; case: pselect => [eX /=|H].
  by apply/sume_ge0 => i _; apply hlength_ge0.
by exfalso; apply H; exists fset0; rewrite /ufint big_nil.
Qed.

(* TODO: too ad hoc?*)
Lemma eq_bigcup_l_set_of_itv (i : interval R) (s : seq (interval R)) :
  set_of_itv i = ufint s ->
  \big[setU/set0]_(i0 <- s) set_of_itv i0 =
  \big[setU/set0]_(i0 <- [:: i]) set_of_itv i0.
Proof.
move=> si.
rewrite predeqE => r; split.
  rewrite -bigcup_mkset.
  case=> /= j js jr.
  rewrite big_cons big_nil setU0.
  rewrite si /ufint.
  rewrite -bigcup_mkset.
  by exists j.
rewrite big_cons big_nil setU0 => ir.
by rewrite si /ufint in ir.
Qed.

Lemma Decompose_set0 (s : seq (interval R)) : ufint s = set0 -> forall i, i \in Decompose s -> i =i pred0.
Proof.
move=> s0 i si x; apply/idP/idP; apply/negP => xi.
have : ufint (Decompose s) = ufint s.
  rewrite /Decompose ufint_decompose //; last exact: (sort_sorted total_le_itv).
  rewrite ufint_sort_le_itv /ufint big_filter big_mkcond; apply eq_bigr => // j _.
  by case: ifPn => // /negPn/eqP.
rewrite s0 => /eqP; apply/negP/set0P; exists x.
by rewrite /ufint -bigcup_mkset; exists i.
Qed.

Lemma length_set0 : length set0 = 0%:E.
Proof.
rewrite /length; case: pselect => [[s s0] /=|].
  case: cid => {}s [/esym {}s0] /=.
  rewrite big_seq_cond big_andbC /= big1 // => j.
  rewrite /Decompose => /Decompose_set0 => /(_ s0) /set_of_itv0P => ->.
  by rewrite hlength0.
move=> ne0; exfalso; apply ne0; exists fset0.
by rewrite /ufint /= big_nil.
(*rewrite /length; case: pselect => [[s [s0 sne]] /=|].
  case: cid => {}s [/esym {}s0 {}sne] /=.
  rewrite big_seq_cond big_andbC /=.
  rewrite big1 // => j.
  rewrite /Decompose => /xxx => /(_ s0).
  move/set_of_itv0P => ->.
  by rewrite hlength0.
(*  by rewrite (ufint_set0 sne s0) /Decompose /= decompose_nil big_nil.*)
move=> ne0; exfalso; apply ne0; exists fset0; split => //.
by rewrite /ufint /= big_nil.*)
Qed.

Lemma length_itv (i : interval R) : length (set_of_itv i) = hlength (set_of_itv i).
Proof.
have [/eqP ->|i0] := boolP (set_of_itv i == set0).
  by rewrite length_set0 hlength0.
rewrite /length; case: pselect => [[s si]|]; last first.
  apply: absurd.
  exists [fset i]%fset.
  by rewrite /ufint /= big_seq_fset1.
case: cid => /= {s si} s si.
rewrite -[RHS]/((hlength \o set_of_itv) i) -[RHS](big_seq1 adde_monoid i).
apply: hlengthUset.
+ do 2 rewrite cover_set_of_itv_nthE//.
  case: (decomposition_of_Decompose s) => sorted_s disjoint_s cover_s.
  by rewrite -/(ufint _) cover_s; exact: eq_bigcup_l_set_of_itv.
+ apply: (trivIset_decompose (sort_sorted total_le_itv _)); apply/allP => j.
  by rewrite mem_sort /= mem_filter => /andP[].
+ by apply/trivIsetP => -[|a] [|b] //=; rewrite nth_nil set_of_itvE ?(setI0,set0I).
Qed.

Lemma length_additive_on_sets (x : set R) (s : seq (interval R)) :
  x = ufint s ->
  trivIset setT (fun i => set_of_itv (nth 0%O s i)) ->
  length x = (\sum_(j <- s) (length (set_of_itv j)))%E.
Proof.
move=> xs ts.
rewrite {1}/length; case: pselect => [[s' xs']|]; last first.
  apply: absurd.
  by exists s.
apply/esym; under eq_bigr do rewrite length_itv; apply/esym.
apply: hlengthUset => //.
- do 2 rewrite cover_set_of_itv_nthE//.
  case: cid => /= {s' xs'} s' [xs'].
  case: (decomposition_of_Decompose s') => sorted_s' disjoint_s' cover_s'.
  by rewrite -/(ufint _) cover_s' -xs'.
- apply: (trivIset_decompose (sort_sorted total_le_itv _)); apply/allP => j.
  by rewrite mem_sort /= mem_filter => /andP[].
Qed.

Lemma length_sigma_finite : sigma_finite setT (length : set (ITVS.itvs_ringOfSetsType R) -> {ereal R}).
Proof.
exists (fun n => set_of_itv `[ (- (n%:R)), (n%:R) ]).
  rewrite predeqE => /= r; split => // _.
  have [r0|r0] := leP 0 r.
    exists (absz (ceil r)) => //; apply/set_of_itv_mem.
    rewrite itv_boundlr /= 2!itv_bound_lteE (le_trans _ r0) // ?oppr_le0 //=.
    rewrite (le_trans (le_Rceil _)) // RceilE pmulrn ler_int gez0_abs //.
    by rewrite ceil_ge0.
  exists (absz (floor r)) => //; apply/set_of_itv_mem.
  rewrite itv_boundlr /= 2!itv_bound_lteE (le_trans (ltW r0)) // ?ler0n // andbT.
  rewrite (le_trans _ (ge_Rfloor _)) // RfloorE pmulrn lez0_abs ?floor_le0 //; last exact/ltW.
  by rewrite mulrNz opprK.
move=> i; split.
  by exists [fset `[ (- (i%:R)), i%:R ] ]%fset; rewrite /ufint /= big_seq_fset1.
by rewrite length_itv hlength_itv /=; case: ifPn; rewrite lte_pinfty.
Qed.

Lemma trivIset_Decompose (a : seq (interval R)) :
  trivIset setT (fun i => set_of_itv (nth 0%O (Decompose a) i)).
Proof.
have [/eqP ->|a0] := boolP (Decompose a == [::]).
  by apply/trivIsetP => i j _ _ ?; rewrite nth_nil set_of_itvE set0I.
rewrite -(head_behead 0%O a0).
apply nonempty_sorted_disjoint_itv_trivIset.
- apply/allP => /= j /mem_behead; rewrite /Decompose.
  set s := sort _ _.
  have /decompose_nonempty/allP sne : all (fun i => set_of_itv i != set0) s.
    by rewrite all_sort all_filter; apply/allP => i ia /=; exact: implybb.
  by move/sne.
- rewrite head_behead //.
  by have [] := decomposition_of_Decompose a.
- by have [] := decomposition_of_Decompose a.
Qed.

Lemma length_additive : additive (length : set (ITVS.itvs_ringOfSetsType R) -> {ereal R}).
Proof.
apply/additive2P; first by rewrite length_set0.
move=> A B /= [a Aa] [b Bb] AB0.
set a' := Decompose a.
set b' := Decompose b.
have ABE : A `|` B = ufint (a' ++ b').
  rewrite Aa Bb.
  have [_ _ <-] := decomposition_of_Decompose a.
  have [_ _ <-] := decomposition_of_Decompose b.
  by rewrite -/a' -/b' /ufint big_cat.
have tAB : trivIset setT (fun i : nat => set_of_itv (nth 0%O (a' ++ b') i)).
  apply/trivIsetP => k1 k2 _ _.
  wlog : k1 k2 / (k1 < k2)%N.
    move=> hwlog.
    rewrite eqn_leq negb_and -2!ltnNge => /orP[k2k1|k1k2].
      by rewrite setIC hwlog // lt_eqF.
    by rewrite hwlog // lt_eqF.
  move=> k1k2 _.
  have [k2a'b'|a'b'k2] := ltnP k2 (size (a' ++ b'))%N; last first.
    by rewrite setIC nth_default // set_of_itvE set0I.
  have [k2a'|a'k2] := ltnP k2 (size a').
    rewrite nth_cat (ltn_trans k1k2) // nth_cat k2a'.
    have /trivIsetP := @trivIset_Decompose a.
    by apply => //; rewrite ltn_eqF.
  have [k1a'|a'k1] := ltnP k1 (size a').
    rewrite nth_cat k1a' nth_cat ltnNge a'k2 /=.
    apply: subsetI_eq0 AB0.
      rewrite Aa.
      have [_ _ <-] := decomposition_of_Decompose a.
      rewrite /ufint -bigcup_mkset => r /set_of_itv_mem ra'.
      by exists (nth 0%O a' k1) => //; exact/mem_nth.
    rewrite Bb.
    have [_ _ <-] := decomposition_of_Decompose b.
    rewrite /ufint -bigcup_mkset => r /set_of_itv_mem rb'.
    exists (nth 0%O b' (k2 - size a')) => //.
    rewrite /mkset -/b'; apply/mem_nth.
    by rewrite ltn_subLR // -size_cat.
  rewrite nth_cat ltnNge a'k1 /= nth_cat ltnNge a'k2 /=.
  have /trivIsetP := @trivIset_Decompose b.
  apply => //; rewrite -(eqn_add2r (size a')) subnK // subnK //.
  by rewrite ltn_eqF.
rewrite (@length_additive_on_sets _ (a' ++ b')) //.
rewrite (@length_additive_on_sets A a') //; last 2 first.
  rewrite /a' /Decompose (ufint_decompose (sort_sorted total_le_itv _)) //.
  by rewrite ufint_sort_le_itv ufint_filter_neq0.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tAB => /(_ i j Logic.I Logic.I ij).
  rewrite nth_cat; case: ifPn => [ia'|]; last first.
    by rewrite -leqNgt => a'i; rewrite (nth_default _ a'i) set_of_itvE set0I.
  rewrite nth_cat; case: ifPn => [//|].
  by rewrite -leqNgt => b'i; rewrite (nth_default _ b'i) set_of_itvE setI0.
rewrite (@length_additive_on_sets B b') //; last 2 first.
  rewrite /a' /Decompose (ufint_decompose (sort_sorted total_le_itv _)) //.
  by rewrite ufint_sort_le_itv ufint_filter_neq0.
  apply/trivIsetP => i j _ _ ij.
  move/trivIsetP : tAB => /(_ (size a' + i)%N (size a' + j)%N Logic.I Logic.I).
  rewrite eqn_add2l => /(_ ij).
  rewrite nth_cat -ltn_subRL subnn ltn0 addnC addnK.
  by rewrite nth_cat -ltn_subRL subnn ltn0 addnC addnK.
by rewrite big_cat /=.
Qed.

Lemma length_semi_sigma_additive : semi_sigma_additive (length : set (ITVS.itvs_ringOfSetsType R) -> {ereal R}).
Proof.
move=> A mA tA UA.
Admitted.

Definition length_measure0 : {measure set (ITVS.itvs_ringOfSetsType R) -> {ereal R}} :=
  Measure.Pack _ (@Measure.Axioms _ _ _ length_set0 length_ge0 length_semi_sigma_additive).

Definition length_measure : {measure set (measurables (outer_measure_of_measure length_measure0)) -> {ereal R}} :=
  measure_of_outer_measure (outer_measure_of_measure length_measure0).

End length_measure.

(* NB: WIP? *)
Section outer_measure_alt.
Variable R : realType.

Definition countable_cover (A : set R) : set ((interval R) ^nat) :=
  [set u_ | exists (a_ : R ^nat), exists (b_ : R ^nat),
    [/\ (forall n, (a_ n <= b_ n)),
       (A `<=` \bigcup_n (set_of_itv `] (a_ n), (b_ n) [ )) &
       (u_ = fun n => `] (a_ n), (b_ n) [)] ].

Definition lstar (A : set R) := ereal_inf
  [set x : {ereal R} | exists i : (interval R) ^nat,
    countable_cover A i /\
    let u_ := (fun n => \sum_(k < n) (length (set_of_itv (i k))))%E in
    x = if pselect (cvg u_) is left _ then lim (u_ @ \oo) else +oo%E].

Lemma lstar_set0 : lstar set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply ereal_inf_lb; exists (fun=> `]0, 0[); split.
    by exists (fun=> 0), (fun=> 0); split.
  move=> u_.
  have u_E : u_ = fun=> 0%:E.
    rewrite funeqE => n; rewrite /u_ /= big1 //= => _ _.
    by rewrite length_itv hlength_itv /= ltxx.
  have : cvg u_ by rewrite u_E; exact: is_cvg_cst.
  case: pselect => // _ _; rewrite u_E.
  exact/esym/(@lim_cst _ (@ereal_hausdorff _)).
- apply lb_ereal_inf => /= x [i [ci ->{x}]].
  case: pselect => [cli|]; last by rewrite lee_pinfty.
  apply: (@ereal_nneg_series_lim_ge0 _ (fun k => length (set_of_itv (i k)))).
  move=> n.
  by rewrite length_itv hlength_ge0.
Grab Existential Variables. all: end_near. Qed.

End outer_measure_alt.
