(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import mathcomp_extra signed.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section qbs_prop.
Variable R : realType.

Definition Borel_sets :=
  <<s [set A : set R| exists a b, A = `]a, b[%classic ] >>.

Variable (X : Type) (carrier : set (R -> X)).

Definition qbs_propa :=
  forall a (f : R -> R), carrier a -> measurable_fun setT f -> carrier (a \o f).

Definition qbs_propb := forall r, carrier (cst r).

Definition qbs_propc :=
  forall F : (set R)^nat, trivIset setT F -> \bigcup_i F i = setT ->
    (forall i, Borel_sets (F i)) ->
    forall a : (R -> X)^nat, (forall i, carrier (a i)) ->
    forall b : R -> X, (forall r i, F i r -> b r = a i r) -> carrier b.

End qbs_prop.

HB.mixin Record isQBS (R : realType) (X : Type) := {
  carrier : set (R -> X) ;
  propa : qbs_propa carrier ;
  propb : qbs_propb carrier ;
  propc : qbs_propc carrier }.

#[short(type=qbs)]
HB.structure Definition QBS (R : realType) := {X of isQBS R X}.

Section prop9.
Variables (R : realType) (d : _) (T : measurableType d)
  (X : Type) (N : set (T -> X)).

Definition qbs_prop2a :=
  forall a (f : T -> T), measurable_fun setT f -> N a -> N (a \o f).

Definition qbs_prop2b := forall r, N (cst r).

Definition qbs_prop2c :=
  forall F : (set T)^nat, trivIset setT F -> \bigcup_i F i = setT ->
    (forall i, measurable (F i)) ->
    forall a : (T -> X)^nat, (forall i, N (a i)) ->
    forall b : T -> X, (forall r i, F i r -> b r = a i r) -> N b.

End prop9.

Section prop9.
Variables (R : realType) (d : _) (T : measurableType d)
  (i : R -> T) (j : T -> R) (ij : cancel i j) (ji : cancel j i)
  (mi : measurable_fun setT i) (mj : measurable_fun setT j)
  (X : Type) (N : set (T -> X)).

Definition carrier9 : set (R -> X) := [set a \o i | a in N].

Let ij1 : i \o j = id.
Proof. by apply/funext => x/=; rewrite ji. Qed.

Let ji1 : j \o i = id.
Proof. by apply/funext => x/=; rewrite ij. Qed.

Lemma prop9 : [/\ qbs_prop2a N, qbs_prop2b N & qbs_prop2c N] <->
  [/\ qbs_propa carrier9, qbs_propb carrier9 & qbs_propc carrier9].
Proof.
split => -[pa pb pc]; split.
- move=> _ f [xi Nxi <-] /= mf; rewrite /carrier9/=.
  red in pa.
  pose g := i \o f \o j.
  exists (xi \o g) => //.
    apply: pa => //.
    apply: measurable_fun_comp => //.
    exact: measurable_fun_comp.
  rewrite -compA.
  rewrite /g.
  rewrite -compA.
  by rewrite ji1.
- move=> r.
  red in pb.
  rewrite /carrier9/=.
  exists (cst r \o j) => //.
  red in pa.
  apply: (pa _(i \o j)) => //; last exact: pb.
  rewrite ij1.
  exact: measurable_fun_id.
- move=> F tF UF BF a ca b hb.
  red.
  simpl.
  red in pc.
  admit.
- admit.
- admit.
- admit.
Admitted.

End prop9.

(* PR 516 in progress *)
HB.mixin Record isProbability (d : measure_display) (T : measurableType d)
  (R : realType) (P : set T -> \bar R) of isMeasure d R T P :=
  { probability_setT : P setT = 1%E }.

#[short(type=probability)]
HB.structure Definition Probability (d : measure_display) (T : measurableType d)
    (R : realType) :=
  {P of isProbability d T R P & isMeasure d R T P }.

Definition qbsProbability (R : realType) (X : qbs R) := {
  alphamu : (R -> X) *
            (probability [the measurableType _ of measurableTypeR R] R) |
  (@carrier R [the QBS.type R of X]) alphamu.1 }.
