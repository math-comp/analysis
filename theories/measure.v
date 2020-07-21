(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences.

(******************************************************************************)
(* This file provides basic elements of a theory of measure illustrated       *)
(* by a formalization of Boole's inequality.                                  *)
(*                                                                            *)
(* {measure set T -> {ereal R}} == type of a measure over sets of elements of *)
(*                                 type T where R is expected to be a         *)
(*                                 a realFieldType or a realType              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move to classical_sets *)
Definition triviset T (U : nat -> set T) :=
  forall j i, (i != j)%nat -> U i `&` U j = set0.

Module Measurable.

Record mixin_of T := Mixin {
  sets : set (set T) ;
  _ : sets set0 ;
  _ : forall A, sets A -> sets (~` A) ;
  _ : forall U : (set T)^nat, (forall i, sets (U i)) -> sets (\bigcup_i (U i)) }.

Notation class_of := mixin_of.

Structure type := Pack { sort : Type ; class : class_of sort }.

Module Exports.
Notation measurableType := type.
Coercion sort : type >-> Sortclass.
Definition measurable (T : type) := sets (class T).
Notation is_sigma_algebra := class_of.
Notation MesurableMixin := Mixin.
End Exports.

End Measurable.

Export Measurable.Exports.

Section measurable_interface.
Variables T : measurableType.

Lemma measurable0 : measurable (set0 : set T).
Proof. by case: T => ? []. Qed.

Lemma measurableC (A : set T) : measurable A -> measurable (~` A).
Proof. by case: T A => ? []. Qed.

Lemma measurable_bigU (U : (set T)^nat) :
  (forall i, measurable (U i)) -> measurable (\bigcup_i (U i)).
Proof. by case: T U => ? []. Qed.

End measurable_interface.

Section measurable_lemmas.
Variables T : measurableType.
Implicit Types A B : set T.

Lemma measurableT : measurable (setT : set T).
Proof. by rewrite -setC0; apply measurableC; exact: measurable0. Qed.

Lemma measurableU A B : measurable A -> measurable B -> measurable (A `|` B).
Proof.
move=> mA mB; rewrite (_ : A `|` B = \bigcup_i
    (fun i => match i with O => A | 1 => B | _ => set0 end) i); last first.
  rewrite predeqE => x; split => [[Ax|Bx]|]; [by exists 0%N|by exists 1%nat|].
  by move=> [[_|[|[|]//]]]; [left|right].
by apply measurable_bigU => -[//|[//|_]]; exact: measurable0.
Qed.

Lemma measurableI A B : measurable A -> measurable B -> measurable (A `&` B).
Proof.
move=> mA mB; rewrite -(setCK A) -(setCK B) -setCU; apply measurableC.
by apply/measurableU; apply/measurableC.
Qed.

Lemma measurableD A B : measurable A -> measurable B -> measurable (A `\` B).
Proof.
by move=> mA mB; rewrite setDE; apply measurableI => //; exact: measurableC.
Qed.

Lemma measurable_finbigU (U : (set T) ^nat) : (forall i, measurable (U i)) ->
  forall n, measurable (\big[setU/set0]_(i < n) U i).
Proof.
move=> mU; elim=> [|n ih]; first by rewrite big_ord0; exact: measurable0.
by rewrite big_ord_recr /=; apply measurableU.
Qed.

Lemma measurable_bigI (U : (set T)^nat) :
  (forall i, measurable (U i)) -> measurable (\bigcap_i (U i)).
Proof.
move=> mU; rewrite bigcapCU; apply/measurableC/measurable_bigU => i.
exact: measurableC.
Qed.

End measurable_lemmas.

Section additivity.
Variables (R : numFieldType) (T : measurableType) (mu : set T -> {ereal R}).

Definition additive2 := forall A B, measurable A -> measurable B ->
  A `&` B = set0 -> mu (A `|` B) = (mu A + mu B)%E.

Definition additive :=
  forall A, (forall i, measurable (A i)) -> triviset A ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = (\sum_(i < n) mu (A i))%E.

Definition sigma_additive :=
  forall A, (forall i, measurable (A i)) -> triviset A ->
  (fun n => (\sum_(i < n) mu (A i))%E) --> mu (\bigcup_n A n).

Lemma additive2P : mu set0 = 0%:E -> additive <-> additive2.
Proof.
move=> mu0; split => [amx A B mA mB AB|a2mx A mA ATI n].
  set C := fun n => if n isn't n'.+1 then A else if n' is O then B else set0.
  have tC : triviset C by move=> [|[|i]] [|[|j]]; rewrite ?set0I ?setI0// setIC.
  have mC : forall i, measurable (C i).
    by move=> [|[]] //= i; exact: measurable0.
  by have := amx _ mC tC 2%N; rewrite !big_ord_recl !big_ord0 adde0/= setU0.
elim: n => [|n IHn] in A mA ATI *.
  by rewrite !big_ord0.
rewrite big_ord_recr /= a2mx //; last 2 first.
   exact: measurable_finbigU.
   rewrite big_distrl /= big1 // => i _; apply: ATI; rewrite lt_eqF //.
   exact: ltn_ord.
by rewrite IHn // [in RHS]big_ord_recr.
Qed.

End additivity.

Lemma sigma_additive_implies_additive
  (R : realFieldType) (X : measurableType) (mu : set X -> {ereal R}) :
  mu set0 = 0%:E -> sigma_additive mu -> additive mu.
Proof.
move=> mu0 samu; apply/additive2P => // A B mA mB AB_eq0.
set C := fun i => if (i == 0)%N then A else if (i == 1)%N then B else set0.
have tC : triviset C by move=> [|[|i]] [|[|j]]; rewrite ?setI0 ?set0I// setIC.
have -> : A `|` B = \bigcup_i C i.
  rewrite predeqE => x; split.
    by case=> [Ax|Bx]; by [exists 0%N|exists 1%N].
  by case=> [[|[|n]]]//; by [left|right].
have mC : forall i, measurable (C i).
  by move=> [|[]] //= i; rewrite /C /=; exact: measurable0.
have /cvg_unique := samu C mC tC; apply => //.
apply: cvg_near_cst.
exists 3%N => // -[//|[//|n]] _.
by rewrite !big_ord_recl /= big1 ?adde0.
Qed.

Module Measure.

Section ClassDef.

Variables (R : numFieldType) (T : measurableType).
Record axioms (mu : set T -> {ereal R}) := Measure {
  _ : mu set0 = 0%:E ;
  _ : forall x, measurable x -> (0%:E <= mu x)%E ;
  _ : sigma_additive mu }.

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
Notation is_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation Measure fA := (Pack (Phant _) fA).
Notation "{ 'measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'measure'  fUV }") : ring_scope.
Notation "[ 'measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'measure'  'of'  f ]") : form_scope.
End Exports.

End Measure.
Include Measure.Exports.

Section measure_lemmas.
Variables (R : numFieldType) (T : measurableType).
Variable mu : {measure set T -> {ereal R}}.

Lemma measure0 : mu set0 = 0%:E.
Proof. by case: mu => ? []. Qed.

Lemma measure_ge0 : forall x, measurable x -> (0%:E <= mu x)%E.
Proof. by case: mu => ? []. Qed.

Lemma measure_sigma_additive : sigma_additive mu.
Proof. by case: mu => ? []. Qed.

End measure_lemmas.

Hint Extern 0 (_ set0 = 0%:E) => solve [apply: measure0] : core.
Hint Extern 0 (sigma_additive _) =>
  solve [apply: measure_sigma_additive] : core.

Section measure_additive_lemmas.
Variables (R : realFieldType) (X : measurableType).
Variable (mu : {measure set X -> {ereal R}}).

Lemma measure_additive : additive mu.
Proof. by apply: sigma_additive_implies_additive. Qed.
Hint Resolve measure_additive.

Lemma measure_additive2 : additive2 mu.
Proof. exact/additive2P. Qed.

End measure_additive_lemmas.

(* measure is monotone *)
Lemma le_measure (R : realFieldType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}) :
  {in [set x | measurable x] &, {homo mu : A B / A `<=` B >-> (A <= B)%E}}.
Proof.
move=> A B mA mB AB; have {1}-> : B = A `|` (B `\` A).
  rewrite funeqE => x; rewrite propeqE.
  have [Ax|Ax] := pselect (A x).
    split=> [Bx|]; by [left | move=> -[/AB //|] []].
  by split=> [Bx|]; by [right| move=> -[//|] []].
rewrite 2!inE in mA, mB.
have ? : measurable (B `\` A) by apply: measurableD.
rewrite measure_additive2 // ?lee_addl // ?measure_ge0 //.
rewrite setDE setICA (_ : _ `&` ~` _ = set0) ?setI0 //.
by rewrite funeqE => x; rewrite propeqE; split => // -[].
Qed.

Section boole_inequality.
Variables (R : realFieldType) (T : measurableType).
Variables (mu : {measure set T -> {ereal R}}).

Definition B_of (A : (set T) ^nat) :=
  fun n => if n isn't n'.+1 then A O else A n `\` A n'.

Lemma triviset_B_of (A : (set T) ^nat) :
  {homo A : n m / (n <= m)%nat >-> n `<=` m} -> triviset (B_of A).
Proof.
move=> ndA j i; wlog : j i / (i < j)%N.
  move=> h; rewrite neq_ltn => /orP[|] ?; by
    [rewrite h // ltn_eqF|rewrite setIC h // ltn_eqF].
move=> ij _; move: j i ij; case => // j [_ /=|n].
  rewrite funeqE => x; rewrite propeqE; split => // -[A0 [Aj1 Aj]].
  exact/Aj/(ndA O).
rewrite ltnS => nj /=; rewrite funeqE => x; rewrite propeqE; split => //.
by move=> -[[An1 An] [Aj1 Aj]]; apply/Aj/(ndA n.+1).
Qed.

Lemma UB_of (A : (set T) ^nat) : {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  forall n, A n.+1 = A n `|` B_of A n.+1.
Proof.
move=> ndA n; rewrite /B_of funeqE => x; rewrite propeqE; split.
by move=> ?; have [?|?] := pselect (A n x); [left | right].
by move=> -[|[]//]; apply: ndA.
Qed.

Lemma bigUB_of (A : (set T) ^nat) n :
  \big[setU/set0]_(i < n.+1) A i = \big[setU/set0]_(i < n.+1) B_of A i.
Proof.
elim: n => [|n ih]; first by rewrite !big_ord_recl !big_ord0.
rewrite big_ord_recr [in RHS]big_ord_recr /= predeqE => x; split=> [[Ax|An1x]|].
    by rewrite -ih; left.
  rewrite -ih.
  have [Anx|Anx] := pselect (A n x); last by right.
  by left; rewrite big_ord_recr /=; right.
move=> [summyB|[An1x NAnx]]; by [rewrite ih; left | right].
Qed.

Lemma eq_bigsetUB_of (A : (set T) ^nat) n :
  {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  A n = \big[setU/set0]_(i < n.+1) B_of A i.
Proof.
move=> ndA; elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
- by move=> ?; rewrite big_ord_recl big_ord0; left.
- by rewrite big_ord_recl big_ord0 setU0.
- rewrite (UB_of ndA) => -[|/=].
  by rewrite big_ord_recr /= -ih => Anx; left.
  by move=> -[An1x Anx]; rewrite big_ord_recr /=; right.
- rewrite big_ord_recr /= -ih => -[|[]//]; exact: ndA.
Qed.

Lemma eq_bigcupB_of (A : (set T) ^nat) : {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  \bigcup_n A n = \bigcup_n (B_of A) n.
Proof.
move=> ndA; rewrite funeqE => x; rewrite propeqE; split.
  move=> -[n _]; rewrite (eq_bigsetUB_of _ ndA) bigcup_ord => -[m mn ?].
  by exists m.
move=> -[m _] myBAmx; exists m => //; rewrite (eq_bigsetUB_of _ ndA) bigcup_ord.
by exists m.
Qed.

(* 401,p.43 measure is continuous from below *)
Lemma cvg_mu_inc (A : (set T) ^nat) :
  (forall i, measurable (A i)) ->
  {homo A : n m / (n <= m)%nat >-> n `<=` m} ->
  mu \o A --> mu (\bigcup_n A n).
Proof.
move=> mA ndA.
have Binter : triviset (B_of A) := triviset_B_of ndA.
have ABE : forall n, A n.+1 = A n `|` B_of A n.+1 := UB_of ndA.
have AE n : A n = \big[setU/set0]_(i < n.+1) (B_of A) i := eq_bigsetUB_of n ndA.
have -> : \bigcup_n A n = \bigcup_n (B_of A) n := eq_bigcupB_of ndA.
have mB : forall i, measurable (B_of A i).
  by elim=> [|i ih] //=; apply: measurableD.
apply: cvg_trans (measure_sigma_additive mB Binter).
apply: (@cvg_trans _ [filter of (fun n => (\sum_(i < n.+1) mu (B_of A i))%E)]); last first.
  by move=> S [n _] nS; exists n => // m nm; apply/(nS m.+1)/(leq_trans nm).
rewrite (_ : (fun n => \sum_(i < n.+1) mu (B_of A i))%E = mu \o A) //.
rewrite funeqE => n; rewrite -measure_additive// bigcup_ord.
by rewrite -bigcup_ord -AE.
Qed.

Theorem Boole_inequality (A : (set T) ^nat) : (forall i, measurable (A i)) ->
  forall n, (mu (\big[setU/set0]_(i < n) A i) <= \sum_(i < n) mu (A i))%E.
Proof.
move=> mA; elim => [|n ih]; first by rewrite !big_ord0 measure0.
set B := \big[setU/set0]_(i < n) A i.
set C := \big[setU/set0]_(i < n.+1) A i.
have -> : C = B `|` (A n `&` ~` B).
  rewrite predeqE => x; split => [|].
    rewrite /C big_ord_recr /= => -[sumA|]; first by left.
    by have [?|?] := pselect (B x); [left|right].
  move=> -[|[An1x _]].
    by rewrite /C big_ord_recr; left.
  by rewrite /C big_ord_recr; right.
have ? : measurable B by apply measurable_finbigU.
rewrite measure_additive2 //; last 2 first.
  apply measurableI => //.
  rewrite setCE; apply measurableD => //.
  exact: measurableT.
  rewrite setIC -setIA (_ : ~` _ `&` _ = set0) ?setI0 //.
  by rewrite funeqE => x; rewrite propeqE; split => // -[].
rewrite (@le_trans _ _ (mu B + mu (A n))%E) // ?lee_add2l //.
  rewrite le_measure //; last 2 first.
    by rewrite inE; apply mA.
    by apply subIset; left.
    rewrite inE. apply measurableI => //.
    by rewrite setCE; apply: measurableD => //; exact: measurableT.
by rewrite big_ord_recr /= lee_add2r.
Qed.

End boole_inequality.
Notation le_mu_bigsetU := Boole_inequality.

(* NB: see also nondecreasing_series *)
Lemma ereal_nondecreasing_series (R : realFieldType) (u_ : {ereal R} ^nat) :
  (forall n, 0%:E <= u_ n)%E ->
  nondecreasing_seq (fun n => \sum_(i < n) u_ i)%E.
Proof.
move=> u_ge0 n m nm; rewrite -(subnKC nm).
rewrite -[X in (_ <= X)%E](big_mkord xpredT) /index_iota subn0 iota_add.
rewrite big_cat -[in X in (_ <= X + _)%E](subn0 n) big_mkord lee_addl //=.
by rewrite sume_ge0.
Qed.

Lemma series_nneg (R : realType) (u_ : {ereal R} ^nat) k :
  (forall n, (0%:E <= u_ n)%E) ->
  (\sum_(i < k.+1) u_ i <= lim (fun n : nat => \sum_(i < n) u_ i))%E.
Proof.
move/ereal_nondecreasing_series/nondecreasing_seq_ereal_cvg/cvg_lim => -> //.
by apply ereal_sup_ub; exists k.+1.
Qed.

Section generalized_boole_inequality.
Variables (R : realType) (T : measurableType).
Variable (mu : {measure set T -> {ereal R}}).

(* 404,p.44 measure satisfies generalized Boole's inequality *)
Theorem generalized_Boole_inequality (A : (set T) ^nat) :
  (forall i : nat, measurable (A i)) ->
  (mu (\bigcup_n A n) <= lim (fun n => \sum_(i < n) mu (A i)))%E.
Proof.
move=> mA; set B := fun n => \big[setU/set0]_(i < n.+1) (A i).
rewrite [X in mu X](_ : _ = \bigcup_n B n); last first.
  rewrite predeqE => x; split.
  by move=> -[k _ Akx]; exists k => //; rewrite /B big_ord_recr /=; right.
  move=> -[m _].
  rewrite /B big_ord_recr /= => -[].
  by rewrite bigcup_ord => -[k km Akx]; exists k.
  by move=> Amx; exists m.
have ndB : {homo B : n m / (n <= m)%N >-> n `<=` m}.
  by move=> n m nm; apply subset_bigsetU.
have mB : forall i, measurable (B i) by move=> i; exact: measurable_finbigU.
move/(@cvg_mu_inc _ _ mu _ mB) : ndB => /cvg_lim => <- //.
have -> : lim (mu \o B) = ereal_sup ((mu \o B) @` setT).
  suff : nondecreasing_seq (mu \o B).
    by move/nondecreasing_seq_ereal_cvg; apply/cvg_lim.
  move=> n m nm; apply: le_measure => //; try by rewrite inE; apply mB.
  exact: subset_bigsetU.
have BA : forall m, (mu (B m) <= lim (fun n : nat => \sum_(i < n) mu (A i)))%E.
  move=> m; rewrite (le_trans (le_mu_bigsetU mu mA m.+1)) // -/(B m).
  by apply: (@series_nneg _ (mu \o A)) => n; exact: measure_ge0.
by apply ub_ereal_sup => /= x [n _ <-{x}]; apply BA.
Qed.

End generalized_boole_inequality.
Notation le_mu_bigcup := generalized_Boole_inequality.
