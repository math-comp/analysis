(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal classical_sets posnum topology normedtype.
Require Import sequences measure cardinality csum.
From HB Require Import structures.

(******************************************************************************)
(*                        measure.v cont'd (WIP)                              *)
(*                                                                            *)
(* mu.-negligible A == A is mu negligible                                     *)
(* mu.-ae P == P holds almost everywhere for the measure mu                   *)
(* {outer_measure set T -> {ereal R}} == type of an outer measure over sets   *)
(*                                 of elements o ftype T where R is expected  *)
(*                                 to be a numFieldType                       *)
(* mu_ext mu == outer measure built from a measure mu on a ring of sets       *)
(* mu.-measurable A == A is Caratheodory measurable                           *)
(*                                                                            *)
(* Caratheodory's theorem (mu.-measurable sets form a sigma-algebra,          *)
(* mu*-negligible sets are measurable                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section negligible.
Variables (R : realFieldType) (T : ringOfSetsType).

Definition negligible (mu : {measure set T -> {ereal R}}) (N : set T) :=
  exists A : set T, [/\ measurable A, mu A = 0%:E & N `<=` A].

Local Notation "mu .-negligible" := (negligible mu)
  (at level 2, format "mu .-negligible").

Lemma negligibleP mu A : measurable A -> mu.-negligible A <-> mu A = 0%:E.
Proof.
move=> mA; split => [[B [mB mB0 AB]]|mA0]; last by exists A; split.
apply/eqP; rewrite eq_le measure_ge0 // andbT -mB0.
by apply: (le_measure (measure_additive_measure mu)) => //; rewrite in_setE.
Qed.

Lemma negligible_set0 mu : mu.-negligible set0.
Proof. by apply/negligibleP => //; exact: measurable0. Qed.

Definition almost_satisfied (mu : {measure set T -> {ereal R}}) (P : T -> Prop) :=
  mu.-negligible (~` [set x | P x]).

Local Notation "mu '.-ae' P" := (almost_satisfied mu P)
  (at level 0, format "mu '.-ae'  P").

Lemma satisfies_almost_satisfied mu (P : T -> Prop) :
  (forall x, P x) -> mu.-ae P.
Proof.
move=> aP.
have -> : P = setT by rewrite predeqE => t; split.
apply/negligibleP; first by rewrite setCT; exact: measurable0.
by rewrite setCT measure0.
Qed.

End negligible.

Notation "mu .-negligible" := (negligible mu)
  (at level 2, format "mu .-negligible").

Notation "mu '.-ae' P" := (almost_satisfied mu P)
  (at level 0, format "mu '.-ae'  P").

Definition sigma_subadditive (R : numFieldType) (T : Type)
  (mu : set T -> {ereal R}) := forall (A : (set T) ^nat),
  (mu (\bigcup_n (A n)) <= lim (fun n => \sum_(i < n) mu (A i)))%E.

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : Type).
Record axioms (mu : set T -> {ereal R}) := OuterMeasure {
  _ : mu set0 = 0%:E ;
  _ : forall x, (0%:E <= mu x)%E ;
  _ : {homo mu : A B / A `<=` B >-> (A <= B)%E} ;
  _ : sigma_subadditive mu}.

Structure map (phUV : phant (set T -> {ereal R})) :=
  Pack {apply : set T -> {ereal R} ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> {ereal R})) (f g : set T -> {ereal R}).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation is_outer_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation OuterMeasure fA := (Pack (Phant _) fA).
Notation "{ 'outer_measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'outer_measure'  fUV }") : ring_scope.
Notation "[ 'outer_measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'outer_measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'outer_measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'outer_measure'  'of'  f ]") : form_scope.
End Exports.

End OuterMeasure.
Include OuterMeasure.Exports.

Section outer_measure_lemmas.
Variables (R : numFieldType) (T : Type).
Variable mu : {outer_measure set T -> {ereal R}}.

Lemma outer_measure0 : mu set0 = 0%:E.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_ge0 : forall x, (0%:E <= mu x)%E.
Proof. by case: mu => ? []. Qed.

Lemma le_outer_measure : {homo mu : A B / A `<=` B >-> (A <= B)%E}.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_sigma_subadditive :sigma_subadditive mu.
Proof. by case: mu => ? []. Qed.

End outer_measure_lemmas.

Hint Extern 0 (_ set0 = 0%:E) => solve [apply: outer_measure0] : core.
Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

Lemma le_outer_measureIC (R : realType) T
  (mu : {outer_measure set T -> {ereal R}}) (A : set T) :
  forall X, (mu X <= mu (X `&` A) + mu (X `&` ~` A))%E.
Proof.
move=> X.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have cvg_mu_ext :
    (fun n => (\sum_(i < n) mu (B i))%E) -->
  (mu (B 0%N) + mu (B 1%N))%E.
  apply/cvg_ballP => e e0; rewrite near_map; near=> n.
  rewrite /ball /= /ereal_ball /=.
  have [m Hm] : exists m, n = m.+2%N.
    by near: n; exists 2%N => // -[//|[//|n ?]]; exists n.
  rewrite (@le_lt_trans _ _ 0) // normr_le0 subr_eq0; apply/eqP.
  congr (contract _).
  rewrite Hm big_ord_recl; congr (_ + _)%E.
  by rewrite big_ord_recl /= big1 ?adde0 // => i _; rewrite outer_measure0.
move: (outer_measure_sigma_subadditive mu B).
rewrite /sigma_subadditive.
have -> : \bigcup_n B n = X.
  transitivity (\big[setU/set0]_(i < 2) B i).
    rewrite (bigcup_recl 2) // bigcup_ord.
    rewrite (_ : \bigcup_i B (2 + i)%N = set0) ?setU0 //.
    rewrite predeqE => t; split => // -[] //.
  by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIUr setUCr setIT.
move/le_trans; apply.
by rewrite (cvg_lim _ cvg_mu_ext).
Grab Existential Variables. all: end_near. Qed.

Notation ssum u := (lim (series u)).

(* build an outer measure from a measure *)
Section measure_extension.

Variables (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> {ereal R}}).

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
apply: lb_ereal_inf => x [B [mB AB] <-{x}].
rewrite ereal_lim_ge //=.
  apply: (@is_cvg_ereal_nneg_series _ (mu \o B)) => // n.
  exact: measure_ge0.
by near=> n; rewrite sume_ge0 // => i; apply: measure_ge0.
Grab Existential Variables. all: end_near. Qed.

Lemma mu_ext0 : mu_ext set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: mu_ext_ge0; exact: measurable0.
rewrite /mu_ext; apply ereal_inf_lb.
exists (fun _ => set0).
  by split => // _; exact: measurable0.
apply: (@lim_near_cst _ _ _ _ _ 0%:E) => //.
by near=> n => /=; rewrite big1.
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
rewrite -forallN => Aoo.
suff add2e : forall e : {posnum R}, (mu_ext (\bigcup_n A n) <=
    lim (fun n => \sum_(i < n) mu_ext (A i)) + (2 * e%:num)%:E)%E.
  apply lee_adde => e.
  rewrite (_ : e%:num = 2 * (e%:num / 2)); last first.
    by rewrite mulrC -mulrA mulVr ?mulr1 // unitfE.
  exact: add2e.
move=> e.
have [B BA] : {B : ((set T) ^nat) ^nat &
  forall n, measurable_cover (A n) (B n) /\
  (lim [sequence \sum_(j < k) mu (B n j)]_k <=
   mu_ext (A n) + (e%:num / (2 ^ n)%:R)%:E)%E}.
  apply: (@choice nat ((set T) ^nat) (fun n u_ => measurable_cover (A n) u_ /\
    (lim [sequence \sum_(j < k) mu (u_ j)]_k <=
     mu_ext (A n) + (e%:num / (2 ^ n)%:R)%:E)%E)) => n.
  rewrite /mu_ext.
  set S := fun _ : {ereal R} => _.
  move infS : (ereal_inf S) => iS.
  case: iS infS => [r Sr|Soo|Soo]; last 2 first.
  - by have := Aoo n; rewrite /mu_ext Soo.
  - have : lbound S 0%:E.
      move=> /= y [B [mB AnB] <-{y}].
      (* TODO: redundant!!! (+,,,+) *)
      rewrite ereal_lim_ge //=.
        apply: (@is_cvg_ereal_nneg_series _ (mu \o B)) => // m.
        exact: measure_ge0.
      by near=> k; rewrite sume_ge0 // => i; apply: measure_ge0.
    by move/lb_ereal_inf; rewrite Soo.
  - have en : 0 < e%:num / (2 ^ n.+1)%:R. (* TODO: (+,,,+) add to posnum *)
      by rewrite divr_gt0 // ltr0n expn_gt0.
    case: (@lb_ereal_inf_adherent _ _ (PosNum en) _ Sr) => x [[B [mB AnB muBx]] xS].
    exists B; split => //.
    rewrite muBx -Sr; apply/ltW.
    rewrite (lt_le_trans xS) // lee_add2l //= lee_fin.
    apply ler_pmul => //.
      by rewrite invr_ge0 // ler0n.
    rewrite ler_pinv // ?inE ?unitfE; last 2 first.
      by rewrite pnatr_eq0 expn_eq0 /= ltr0n expn_gt0.
      by rewrite pnatr_eq0 expn_eq0 /= ltr0n expn_gt0.
    by rewrite ler_nat leq_exp2l.
apply: (@le_trans _ _ (lim (fun n =>
  (\sum_(i < n) (mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E)%E))); last first.
  rewrite (_ : (fun n : nat => _) = ((fun n => \sum_(i < n) (mu_ext (A i)))%E \+
      (fun n => \sum_(i < n) (((e)%:num / (2 ^ i)%:R)%:E)%E))%E); last first.
    by rewrite funeqE => n; rewrite big_split.
  have cvggeo :
      (fun x => (\sum_(i < x) ((e)%:num / (2 ^ i)%:R)%:E)%E) --> (2 * e%:num)%:E.
    rewrite (_ : (fun n : nat => _) =
        (fun x => x%:E) \o (series (geometric e%:num (2^-1)%R))); last first.
      rewrite funeqE => n; rewrite /series /=.
      rewrite (@big_morph _ _ (fun x => x%:E) 0%:E adde) //.
      by apply eq_bigr => i _; rewrite natrX exprVn.
    apply: cvg_comp.
      apply: cvg_geometric_series.
      by rewrite ger0_norm // invr_lt1 // ?ltr1n // unitfE.
    rewrite (_ : [filter of _] = [filter of 2 * e%:num : R^o]) // !filter_of_filterE.
    congr ([filter of _]).
    rewrite mulrC; congr (_ * _); apply mulr1_eq.
    by rewrite mulrBl mulVr ?unitfE// mul1r (_ : 1 = 1%:R)// -natrB.
  rewrite ereal_limD //; last 3 first.
    by apply: (@is_cvg_ereal_nneg_series _ (mu_ext \o A)) => n; exact: mu_ext_ge0.
    apply: (@is_cvg_ereal_nneg_series _ (fun i => ((e)%:num / (2 ^ i)%:R)%:E)) => n.
    by rewrite lee_fin divr_ge0 // ler0n.
    by rewrite (cvg_lim _ cvggeo) //= negb_or /= !negb_and /= orbT orbT.
  by rewrite lee_add2l // (cvg_lim _ cvggeo).
pose muB := lim [sequence (\sum_(i < n) (lim [sequence (\sum_(j < k) mu (B i j))%E]_k))%E ]_n .
have : (mu_ext (\bigcup_n A n) <= muB)%E.
  suff : (mu_ext (\bigcup_n A n) <=
      lim [sequence (\sum_(i < n) (lim [sequence (\sum_(j < m) mu (B i j))%E]_m))%E]_n)%E.
    exact/le_trans.
  have AB : \bigcup_n A n `<=` \bigcup_n (\bigcup_k B n k).
    move=> t [i _].
    by move/(cover_bigcup (proj1 (BA i))) => -[j _ ?]; exists i => //; exists j.
  have : (mu_ext (\bigcup_n A n) <=
          csum setT (fun ab : [choiceType of nat * nat] => mu (B ab.1 ab.2)))%E.
    rewrite /mu_ext.
    apply ereal_inf_lb.
    have [enu [enuenu injenu]] : exists e : nat -> nat * nat, enumeration (@setT (nat * nat)) e /\ injective e.
      have /countable_enumeration [|[f ef]] := countable_prod_nat.
        by rewrite predeqE => /(_ (O%N, 0%N)) [] /(_ I).
      by exists (enum_wo_rep infinite_prod_nat ef); split;
       [exact: enumeration_enum_wo_rep | exact: injective_enum_wo_rep].
    exists (fun x => let i := enu x in B i.1 i.2).
      split.
        by move=> i; exact: (cover_measurable (proj1 (BA (enu i).1))).
      move/subset_trans : AB; apply.
      move=> t [i _ [j _ Bijt]].
      case: enuenu => sur_enu enuE.
      have [k [_ ijk]] := sur_enu (i, j) I.
      by exists k => //; rewrite -ijk.
    have : forall ab : nat * nat, (0%:E <= mu (B ab.1 ab.2))%E.
      by move=> ab; exact/measure_ge0/(cover_measurable (proj1 (BA ab.1))).
    move/(@csum_countable R _ setT (fun x => mu (B x.1 x.2)) enu).
    by move/(_ countably_infinite_prod_nat enuenu injenu).
  move/le_trans; apply.
  rewrite (@csum_csum _ _ setT setT (fun i => [set (i, j) | j in @setT nat])
      (fun x => mu (B x.1 x.2)) _); last 5 first.
    by move=> /= x; exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
    by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b.
    by exists O.
    by move=> k; exists (k, O); exists O.
    move=> i j ij.
    rewrite predeqE => -[x1 x2] /=; split => //= -[] [_] _ [<-{x1} _].
    by move=> [x2' _] [] /esym/eqP; rewrite (negbTE ij).
  rewrite (@csum_countable R _ setT
    (fun k => csum (fun y : nat * nat => exists2 j, setT j & (k, j) = y)
                (fun i => mu (B i.1 i.2))) id _ _ enumeration_id) //; last 2 first.
      move=> n /=; apply csum_ge0 => /= x.
      exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
      exact/card_eqTT.
  apply lee_lim.
    apply: (@is_cvg_ereal_nneg_series _
      (fun i => csum (fun y : nat * nat => exists2 j, setT j & (i, j) = y)
      (fun i => mu (B i.1 i.2)))).
    move=> n; apply csum_ge0 => x.
    exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
    apply: (@is_cvg_ereal_nneg_series _
       (fun i => lim (fun m => (\sum_(j < m) mu (B i j))%E))).
    move=> n; apply ereal_lim_ge.
      apply: (@is_cvg_ereal_nneg_series _ (mu \o B n)) => k.
      exact/measure_ge0/(cover_measurable (proj1 (BA n))).
    near=> m.
    apply sume_ge0 => i.
    exact/measure_ge0/(cover_measurable (proj1 (BA n))).
  near=> n.
  apply: (@lee_sum _
   (fun i => csum (fun y : nat * nat => exists2 j, setT j & (i, j) = y)
   (fun i => mu (B i.1 i.2))) (fun i => lim (fun m => (\sum_(j < m) mu (B i j))%E))).
  move=> j /=.
  pose enu := fun x : nat => (j, x).
  have [enuenu injenu] :
      enumeration (fun y => exists2 j0 : nat, setT j0 & (j, j0) = y) enu /\ injective enu.
    split.
      split.
        by move=> [x1 x2] [_ _ [<- _]]; exists x2.
      by rewrite predeqE => -[x1 x2]; split.
    by move=> x y [].
  rewrite (@csum_countable R _ (fun y => exists2 j0, setT j0 & (j, j0) = y) (fun i => mu (B i.1 i.2)) enu) //=; last 2 first.
    by move=> x; exact/measure_ge0/(cover_measurable (proj1 (BA x.1))).
  apply/card_eqP; exists (fun '(i, j) => j); split => //.
  - move=> /= [x1 x2] [y1 y2].
    rewrite in_setE => -[x _ [<-{x1} <-{x2}]].
    rewrite in_setE => -[y _ [<-{y1} <-{y2}]].
    by move=> ->.
  - by move=> /= k _; exists (j, k); split => //; exists k.
move/le_trans; apply; rewrite {}/muB /=; apply lee_lim.
- apply/cvg_ex; eexists.
  apply nondecreasing_seq_ereal_cvg => i j ij.
  apply: (@lee_sum_nneg_ord _ (fun i => lim (fun k => (\sum_(j < k) mu (B i j))%E))) => // n.
  apply ereal_lim_ge.
    apply: (@is_cvg_ereal_nneg_series _ (mu \o B n)) => x.
    exact/measure_ge0/(cover_measurable (proj1 (BA n))).
  near=> m.
  apply sume_ge0 => // k.
  exact/measure_ge0/(cover_measurable (proj1 (BA n))).
- apply/cvg_ex; eexists.
  apply nondecreasing_seq_ereal_cvg => i j ij.
  apply: (@lee_sum_nneg_ord _ (fun i => (mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E)) => // n.
  apply adde_ge0; first exact: mu_ext_ge0.
  by rewrite lee_fin // divr_ge0 // ler0n.
near=> n.
apply: (@lee_sum _
    (fun i => lim (fun k => (\sum_(j < k) mu (B i j))%E))
    (fun i => (mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E)).
by move=> i; exact: (proj2 (BA i)).
Grab Existential Variables. all: end_near. Qed.

End measure_extension.

Canonical canonical_outer_measure (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}) : {outer_measure set T -> {ereal R}} :=
    OuterMeasure (OuterMeasure.OuterMeasure (mu_ext0 mu) (mu_ext_ge0 mu)
      (le_mu_ext mu) (mu_ext_sigma_subadditive mu)).

Lemma mu_ext_measurable (R : realType) (T : ringOfSetsType)
  (mu : {measure set T -> {ereal R}}) X : measurable X -> mu_ext mu X = mu X.
Proof.
move=> mX; apply/eqP; rewrite eq_le; apply/andP; split.
- apply ereal_inf_lb; exists (fun n => if n is 0%N then X else set0).
    by split=> [[]// _|t Xt]; [exact: measurable0 | exists 0%N].
  apply: cvg_lim => //.
  rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu X)); first exact: cvg_cst.
  by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
- apply/lb_ereal_inf => x [A [mA XA] <-{x}].
  have XUA : X = \bigcup_n (X `&` A n).
    rewrite predeqE => t; split => [Xt|[i _ []//]].
    by have [i _ Ait] := XA _ Xt; exists i; split.
  apply: (@le_trans _ _ (lim (fun n => \sum_(i < n) mu (X `&` A i)))%E).
    rewrite {1}XUA.
    apply: generalized_Boole_inequality => //.
    by move=> i; exact: measurableI.
    by rewrite -XUA.
  apply lee_lim.
    apply: (@is_cvg_ereal_nneg_series _ (fun i => mu (X `&` A i))) => n.
    exact/measure_ge0/measurableI.
    apply: (@is_cvg_ereal_nneg_series _ (mu \o A)) => n.
    exact/measure_ge0.
  near=> n.
  apply: (@lee_sum _ (fun i => mu (X `&` A i)) (mu \o A)).
  move=> i.
  apply le_measure => //; rewrite ?in_setE //.
  exact: measurableI.
  by apply subIset; right.
Grab Existential Variables. all: end_near. Qed.

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

Section outer_measurable.

Variables (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}).

Lemma outer_measurable :
  forall A, measurable A -> (canonical_outer_measure mu).-measurable A.
Proof.
move=> A mA.
apply le_ext_measurable => // X /=.
suff H : forall B, measurable B -> X `<=` B ->
  (mu_ext mu (X `&` A) + mu_ext mu (X `&` ~` A) <= mu B)%E.
  apply lb_ereal_inf => Y [B [mB XB] <-{Y}].
  have : Builders_6.Super.measurable (\bigcup_k B k) by exact: measurable_bigcup.
  move/H => /(_ XB) /le_trans; apply.
  by apply generalized_Boole_inequality => //; exact: measurable_bigcup.
move=> B mB BX.
have : (mu_ext mu (X `&` A) + mu_ext mu (X `&` ~` A) <=
        mu (B `&` A) + mu (B `&` ~` A))%E.
  apply: lee_add.
  - apply/ereal_inf_lb; exists (fun n => if n is 0%N then B `&` A else set0).
      split=> [[|_]|t [Xt At]].
      exact: measurableI.
      exact: measurable0.
      by exists 0%N => //; split => //; exact: BX.
    apply: cvg_lim => //.
    rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu (B `&` A))); first exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
  - apply ereal_inf_lb; exists (fun n => if n is 0%N then B `&` ~` A else set0).
      split=> [[|_]|t [Xt At]].
      by apply measurableI => //; apply: measurableC.
      exact: measurable0.
      by exists 0%N; split => //; exact: BX.
    apply: cvg_lim => //.
    rewrite -cvg_shiftS (_ : [sequence _]_n = cst (mu (B `&` ~` A))); first exact: cvg_cst.
    by rewrite funeqE => n /=; rewrite big_ord_recl /= big1 ?adde0.
move/le_trans; apply.
rewrite -measure_additive2 //; last 3 first.
  exact: measurableI.
  by apply measurableI => //; exact: measurableC.
  by rewrite setICA -(setIA B) setICr 2!setI0.
by rewrite -setIUr setUCr setIT.
Qed.

End outer_measurable.

Section caratheodory_theorem_part1.
(* mu.-measurable sets form a tribu *)

Variables (R : realType) (T : Type)
  (mu : {outer_measure set T -> {ereal R}}).

Let M := mu.-measurable.

Lemma sigma_algebra_set0 : M set0.
Proof.
by move=> X /=; rewrite setI0 outer_measure0 add0e setC0 setIT.
Qed.

Lemma sigma_algebra_setC A : M A -> M (~` A).
Proof. by move=> MA X; rewrite setCK addeC -MA. Qed.

Lemma sigma_algebra_setU A B : M A -> M B -> M (A `|` B).
Proof.
rewrite /M => MA MB.
move=> X /=; apply/eqP; rewrite eq_le.
have -> : (mu X <=
    mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)))%E.
  by apply le_outer_measureIC => //; exact: measurableU.
have step1 : (mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <=
    mu (X `&` A `|` X `&` B `&` ~` A) + mu (X `&` ~` (A `|` B)))%E.
  rewrite setIUr (_ : X `&` A `|` X `&` B = (X `&` A) `|` (X `&` B `&` ~` A))//.
  rewrite -[in LHS](setIT B) -(setUCr A) 2!setIUr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply subIset; right.
have /(lee_add2r (mu (X `&` (~` (A `|` B))))) :
    (mu (X `&` A `|` X `&` B `&` ~` A) <=
     mu (X `&` A) + mu (X `&` B `&` ~` A))%E.
  set C : (set T) ^nat := bigcup2 (X `&` A) (X `&` B `&` ~` A).
  have CE :  X `&` A `|` X `&` B `&` ~` A = \bigcup_k C k.
    rewrite predeqE => t; split=> [[XAt|XBAt]|[]].
    by exists O.
    by exists 1%N.
    move=> [_ C0t|[_ C1t|//]].
    by left.
    by right.
  rewrite CE.
  apply: (le_trans (outer_measure_sigma_subadditive mu C)).
  have : (fun n => \sum_(i < n) mu (C i))%E -->
         (mu (X `&` A) + mu (X `&` B `&` ~` A))%E.
    rewrite -(cvg_shiftn 2) /=.
    set l := (X in _ --> X).
    rewrite (_ : (fun _ => _) = cst l); last first.
      rewrite funeqE => i; rewrite addn2 2!big_ord_recl big1 ?adde0//.
      by move=> ? _; exact: outer_measure0.
    exact: cvg_cst.
  by move/cvg_lim => ->.
move/(le_trans step1) => {step1}.
have -> : (mu (X `&` A) + mu (X `&` B `&` ~` A) +
    mu (X `&` (~` (A `|` B))) = mu X)%E.
  by rewrite setCU setIA -(setIA X) setICA (setIC B) -addeA -MB -MA.
exact.
Qed.

Lemma sigma_algebra_bigfinU (A : (set T) ^nat) : (forall n, M (A n)) ->
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
  triviset A -> forall n X, mu (X `&` \big[setU/set0]_(i < n) A i) =
                        (\sum_(i < n) mu (X `&` A i))%E.
Proof.
move=> MA ta; elim=> [|n ih] X; first by rewrite !big_ord0 setI0 outer_measure0.
rewrite big_ord_recr /= additive_ext_inter //; last 2 first.
  exact: sigma_algebra_bigfinU.
  exact: triviset_set0.
by rewrite ih big_ord_recr.
Qed.

Lemma sigma_algebra_setU'_helper (A : (set T) ^nat) :
  (forall n : nat, M (A n)) -> triviset A ->
  let A' := \bigcup_k A k : set T in
  let B := fun n => \big[setU/set0]_(k < n) (A k) in
  forall X : set T,
  (mu (X `&` A') + mu (X `&` ~` A') <=
    lim (fun n => \sum_(k < n) mu (X `&` A k)) + mu (X `&` ~` A') <=
    mu X)%E.
Proof.
move=> MA tA A' B X.
have MB : forall n, M (B n).
  elim => [|n ih]; first by rewrite /B big_ord0; exact: sigma_algebra_set0.
  by rewrite /B big_ord_recr /=; apply sigma_algebra_setU.
apply/andP; split.
  apply: lee_add2r.
  apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
  apply le_outer_measure.
  by rewrite /A' bigcup_distrr.
suff : forall n, (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` A') <= mu X)%E.
  move=> H.
  rewrite [X in (X + _)%E](_ : _ = ereal_sup
    ((fun n : nat => \sum_(k < n) mu (X `&` A k))%E @` setT)); last first.
  apply/cvg_lim/nondecreasing_seq_ereal_cvg => //.
  apply: (@le_ereal_nneg_series _ (fun n => mu (X `&` A n))) => n.
  exact: outer_measure_ge0.
  move XA : (mu (X `&` ~` A')) => x.
  case: x XA => [x| |] XA; last 2 first.
    suff : mu X = +oo%E by move=> ->; rewrite lee_pinfty.
    apply/eqP.
    rewrite -lee_pinfty_eq -XA.
    have : (X `&` ~` A' `<=` X) by apply subIset; left.
    by move/(le_outer_measure mu); apply; rewrite !inE //.
    by rewrite addeC /= lee_ninfty.
  rewrite -lee_subr_addr.
  apply ub_ereal_sup => /= y [n _] <-{y}.
  rewrite lee_subr_addr -XA.
  exact: H.
move=> n.
apply (@le_trans _ _ (\sum_(k < n) mu (X `&` A k) +
                      mu (X `&` ~` B n))%E).
  apply: lee_add2l.
  apply le_outer_measure.
  apply: setIS; apply: subsetC => t.
  by rewrite /B bigcup_ord => -[i ni Ait]; exists i.
by rewrite [in X in (_ <= X)%E](MB n) lee_add2r // additive_ext.
Qed.

Lemma sigma_algebra_bigU' (A : (set T) ^nat) : (forall n, M (A n)) ->
  triviset A -> M (\bigcup_k (A k)).
Proof.
move=> MA tA.
set A' := \bigcup_k (A k).
set B : nat -> set T := fun n => \big[setU/set0]_(k < n) (A k).
apply le_ext_measurable.
move=> X /=.
move: (sigma_algebra_setU'_helper MA tA X) => /andP[].
exact: le_trans.
Qed.

Lemma sigma_algebra_bigU (A : (set T) ^nat) : (forall n, M (A n)) ->
  M (\bigcup_k (A k)).
Proof.
move=> MA.
set B : (set T) ^nat := fun n => match n with
  O => A O
| m.+1 => A m.+1 `&` ~` (\big[setU/set0]_(i < n) A i)
end.
have BA : forall n, B n `<=` A n.
  by case => // n; rewrite /B; apply subIset; left.
have MB : M (\bigcup_k B k).
  have MB : forall n, M (B n).
    case=> [|n /=]; first exact: MA.
    apply sigma_algebra_setI; [exact: MA|apply sigma_algebra_setC].
    rewrite big_ord_recr /=; apply sigma_algebra_setU; [|exact: MA].
    elim: n => [|n ih]; first by rewrite big_ord0; exact: sigma_algebra_set0.
    by rewrite big_ord_recr /=; apply sigma_algebra_setU.
  have tB : triviset B.
    have BAC : forall n k, (k > n)%N -> B k `<=` ~` A n.
      move=> n [] // k; rewrite ltnS => nk /=; apply subIset.
      by right; apply subsetC => t Ant; rewrite bigcup_ord; exists n.
    move=> i j.
    wlog : i j / (i < j)%N.
      move=> H; rewrite neq_lt => /orP[ji|ij].
      by rewrite H // lt_eqF.
      by rewrite setIC H // lt_eqF.
    move=> ij _.
    rewrite predeqE => t; split => // -[] Bjt Bit.
    have Ait : A i t by apply BA.
    by have := BAC _ _ ij t Bit.
  exact: sigma_algebra_bigU'.
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
move: nAn0t An0t.
case: n0 => -[//|n0 /= n0n H An0t]; split => //.
by rewrite bigcup_ord => -[] => m /H.
Qed.

End caratheodory_theorem_part1.

Section caratheodory_theorem_instance.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> {ereal R}}).

HB.instance Definition caratheodory_mixin := @isMeasurable.Build T
  mu.-measurable (sigma_algebra_set0 mu) (@sigma_algebra_setC _ _ mu) (@sigma_algebra_bigU _ _ mu).

Definition caratheodory_measurableType :=
  [the measurableType of T].

(*Canonical caratheodory_measurableType : measurableType :=
  Measurable.Pack caratheodory_mixin.*)
End caratheodory_theorem_instance.

Section caratheodory_theorem_part2.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> {ereal R}}).
Definition U : measurableType := caratheodory_measurableType mu.

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
move=> A mA tA _mbigcupA.
set B := \bigcup_k A k.
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
have mB : mu.-measurable B by move=> Y; apply sigma_algebra_bigU.
move: (sigma_algebra_setU'_helper mA tA X).
rewrite -le_ext_measurable; last by move=> ?; rewrite -mB.
by rewrite -eq_le => /eqP.
Qed.

Definition caratheodory_measure_mixin := Measure.Measure caratheodory_measure0
 caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
Canonical caratheodory_measure : {measure _ -> _} :=
  Measure.Pack _ caratheodory_measure_mixin.

Lemma caratheodory_measure_complete (N : set U) :
  caratheodory_measure.-negligible N ->
  mu.-measurable N.
Proof.
case => A [mA muA0 NA].
have muN : mu N = 0%:E.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  by move: (le_outer_measure mu NA); rewrite muA0 => ->.
apply le_ext_measurable => X.
have -> : mu (X `&` N) = 0%:E.
  apply/eqP; rewrite eq_le outer_measure_ge0.
  have : X `&` N `<=` N by apply subIset; right.
  by move/(le_outer_measure mu); rewrite muN => ->.
by rewrite add0e le_outer_measure //; apply subIset; left.
Qed.
End caratheodory_theorem_part2.

From mathcomp Require Import interval.

Section real_measure.
Variable R : realType.

Definition length_interval (i : interval R) : R :=
  match i with
  | Interval (BOpen a) (BOpen b) => `|b - a|
  | Interval (BClose a) (BClose b) => `|b - a|
  | Interval (BOpen a) (BClose b) => `|b - a|
  | Interval (BClose a) (BOpen b) => `|b - a|
  | Interval BInfty _ => 0 (*shouldn't happen*)
  | Interval _ BInfty => 0
  end.

Lemma length_interval_ge0 i : 0 <= length_interval i.
Proof. by move: i => [] [[|]a | ] [[|]b | ] => /=. Qed.

Definition set_of_interval (i : interval R) : set R :=
  match i with
  | Interval (BOpen a) (BOpen b) => [set x | a < x < b]
  | Interval (BClose a) (BClose b) => [set x | a <= x <= b]
  | Interval (BOpen a) (BClose b) => [set x | a < x <= b]
  | Interval (BClose a) (BOpen b) => [set x | a <= x < b]
  | Interval BInfty (BOpen b) => [set x | x < b]
  | Interval BInfty (BClose b) => [set x | x <= b]
  | Interval BInfty BInfty => setT
  | Interval (BOpen a) BInfty => [set x | a < x]
  | Interval (BClose a) BInfty => [set x | a <= x]
  end.

Definition countable_cover (A : set R) : set ((interval R) ^nat) :=
  [set u_ | exists (a_ : R ^nat), exists (b_ : R ^nat),
    [/\ (forall n, (a_ n <= b_ n)),
       (A `<=` \bigcup_n (set_of_interval `] (a_ n), (b_ n) [ )) &
       (u_ = fun n => `] (a_ n), (b_ n) [)] ].

Definition lstar (A : set R) := ereal_inf
  [set x : {ereal R} | exists i : (interval R) ^nat,
    countable_cover A i /\
    let u_ := (fun n => \sum_(k < n) (length_interval (i k)) : R^o) in
    x = if pselect (cvg u_) is left _ then (lim (u_ @ \oo))%:E else +oo%E].

Lemma lstar_set0 : lstar set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply ereal_inf_lb.
  exists (fun=> Interval (BOpen 0) (BOpen 0)); split.
    by exists (fun=> 0), (fun=> 0); split.
  move=> u_.
  have u_E : u_ = fun=> 0.
    rewrite funeqE => n.
    by rewrite /u_ /= big1 // => _ _; rewrite subr0 normr0.
  have : cvg u_.
    rewrite u_E.
    by apply: is_cvg_cst.
  case: pselect => // _ _.
  rewrite u_E.
  congr (_ %:E).
  apply/esym.
  by apply: (@lim_cst _ (@Rhausdorff [realFieldType of R])).
- apply lb_ereal_inf => /= x.
  move=> -[i [ci ->{x}]].
  case: pselect => [cli|]; last by rewrite lee_pinfty.
  rewrite lee_fin.
  apply/lim_ge => //.
  near=> n.
  apply sumr_ge0 => k _.
  exact: length_interval_ge0.
Grab Existential Variables. all: end_near. Qed.

End real_measure.
