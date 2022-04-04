(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype landau sequences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Definition principle_filter {X} (x : X) : set (set X) := globally [set x].

Lemma principle_filterP {X} (x : X) (W : set X) : 
  principle_filter x W <-> W x.
Proof.
rewrite /principle_filter/globally /=; split => //=; first exact.
by move=>? ? ->.
Qed.

Lemma principle_filter_proper {X} (x : X) : ProperFilter (principle_filter x).
Proof. exact: globally_properfilter. Qed.

Canonical bool_discrete_filter := FilteredType bool bool (principle_filter).
 
Program Definition discrete_topological_mixin {X : pointedType} :
  Topological.mixin_of (principle_filter) := @topologyOfFilterMixin
    X principle_filter principle_filter_proper _ _.
Next Obligation. by move=> ???/principle_filterP. Qed.
Next Obligation. 
  move=> ???/principle_filterP?. 
  exact/principle_filterP/principle_filterP.
Qed.

Canonical bool_discrete_topology := 
    TopologicalType bool (@discrete_topological_mixin _).


Lemma compactU {X : topologicalType} (A B : set X) : 
  compact A -> compact B -> compact (A `|` B).
Proof.
rewrite ?compact_ultra=> cptA cptB F UF FAB; rewrite setIUl.
case: (in_ultra_setVsetC A); first by move=>/cptA [x ?]; exists x; left.
move=> /(filterI FAB); rewrite setIUl setIv set0U => FBA.
have : F B by apply: (filterS _ FBA); exact: subIsetr.
by move=> /cptB [x ?]; exists x; right.
Qed.

Lemma bool2E : [set: bool] = [set true; false].
Proof.  by rewrite eqEsubset; split => //= [[]] //= _;[left|right]. Qed.

Lemma bool_compact : compact [set: bool].
Proof. by rewrite bool2E; apply compactU; exact: compact_set1. Qed.

Lemma open_bool (b : bool): open [set b].
Proof. by rewrite /open /= /open_of_nbhs => ? /= -> //=. Qed.

Lemma bool_discrete_hausdorff : hausdorff_space bool_discrete_topology.
Proof.
move=> p q => //= /(_ [set p] [set q]) //=; case.
- exact: open_bool.
- exact: open_bool.
- by move=> r //= [] ->.
Qed.

Definition cantor_space := 
  product_topologicalType (fun (_ : nat) => bool_discrete_topology).

Lemma cantor_space_compact: compact [set: cantor_space].
Proof.
have := (@tychonoff _ (fun (_: nat) => bool_discrete_topology) _ 
  (fun=> bool_compact)).
by congr (compact _) => //=; rewrite eqEsubset; split => b //=.
Qed.

Lemma cantor_space_hausdorff : hausdorff_space cantor_space.
Proof. apply: hausdorff_product => ?; exact: bool_discrete_hausdorff. Qed.

Definition min_diff (x y : cantor_space) n :=
  x n != y n /\ (forall m, m < n -> x m == y m).

Lemma cantor_space_neqP (x y : cantor_space) :
  x != y <-> exists n, min_diff x y n.
Proof.
split. 
  apply: contra_neqP=> /forallNP N; rewrite funeqE.
  apply: (@well_founded_ind nat lt (Wf_nat.lt_wf) (fun q => x q = y q)) => n E.
  move: (N n); apply contra_notP => xnNyn; split; first exact/eqP.
  by move=> M Mn; apply/eqP; apply E; apply/ ssrnat.leP.
case=> n [+ _]; apply: contraNN=> /eqP; rewrite funeqE => ?; exact/eqP.
Qed.

Definition pull (x : cantor_space) : cantor_space := fun n => x (S n).

Inductive prefix (x : cantor_space) : seq bool -> Prop := 
  | NilPrefix : prefix x nil 
  | ConsPrefix : forall b s, b = x 0 -> prefix (pull x) s -> prefix x (b :: s)
.

Lemma prefixP (x : cantor_space) (b : bool) (s : seq bool) : 
  prefix x (b :: s) <-> (b = x 0 /\ prefix (pull x) s).
Proof.
(* TODO: Why does `case` discard the nil case?*)
split; first by move=> pxb; inversion pxb; subst; tauto.
by move=>[??]; constructor.
Qed.

  



Definition fixed_prefix (s : seq bool) (x : cantor_space) : Prop := 
  prefix x s.

Lemma empty_prefix : fixed_prefix nil = [set: cantor_space] .
Proof. by rewrite eqEsubset; split => //= x _; constructor. Qed.

Fixpoint false_extend (s : seq bool) : cantor_space :=
  match s with 
  | nil => (fun=> false)
  | b :: s => (fun n => 
    match n with 
    | 0 => b
    | S m => (false_extend s m)
    end)
  end.

Lemma false_extend_prefix (s : seq bool) : fixed_prefix s (false_extend s).
Proof.  by elim:s=> //=; [constructor | move=> ???; constructor]. Qed.

Fixpoint prefix_of (x : cantor_space) (n : nat) : seq bool :=
  match n with 
  | 0 => nil
  | S m => x 0 :: prefix_of (pull x) m
  end.

Lemma prefix_of_prefix (x : cantor_space) (i : nat) : fixed_prefix (prefix_of x i) x.
Proof.
move:x; elim i=> //=; first (by move=> ?; rewrite empty_prefix).
by move=> n ind x /=; constructor => //=; exact: ind.
Qed.

Local Fixpoint prefix_helper (i : nat) (s : seq bool) :=
match s with 
| nil => [set: cantor_space]
| b :: l => prod_topo_apply i @^-1` [set b] `&` 
    prefix_helper (S i) l
end.

Local Lemma prefix_helper_S (s : seq bool) j x :
    prefix_helper j s (pull x) <-> 
    prefix_helper (j + 1) s x.
Proof.
move: j; elim: s => //= b l; rewrite /prod_topo_apply/pull => E; split.
by case=> <- Q; split; rewrite -add1n ?addn0 addn1 // addnC; apply/ E.
rewrite -add1n ?addn0 addn1 => [[]] <- Q; split => //=.
by apply/E; rewrite addn1.
Qed.


Local Lemma fixed_helperE (s : seq bool) : 
  fixed_prefix s = prefix_helper 0 s.
Proof.
elim:s; first by rewrite empty_prefix.
move=> b l => //=; rewrite ?eqEsubset => E; split => x //=.
  move=> /prefixP [-> ?]; split; first by done.
  by rewrite -[1]add0n; apply/prefix_helper_S;  apply E.
rewrite -[1]add0n/prod_topo_apply => [[<-]] W. 
by constructor => //=;  apply: (proj2 E); exact/prefix_helper_S.
Qed.

Local Lemma open_fixed_prefix i (s : seq bool) : open (prefix_helper i s).
Proof.
move: i; elim: s; first (move=> ? //=; exact: openT).
move=> ???? //=; apply: openI => //; apply: open_comp; last exact: open_bool.
by move=> + _; exact: prod_topo_apply_continuous.
Qed.

Lemma open_fixed (s : seq bool) : open (fixed_prefix s).
Proof. rewrite fixed_helperE; exact: open_fixed_prefix. Qed.

Lemma negb_neqP (a b : bool) : ~~ a = b <-> a <> b.
Proof. by case: a; case: b => //=. Qed.

Lemma closed_fixed (s : seq bool) (b : bool) :  
  ~`(fixed_prefix (b :: s)) = fixed_prefix(map negb (b :: s)).
Proof.
move: b; elim s => //.
  move=> b; rewrite eqEsubset; split => x => //.
    move=> W; constructor; last constructor.
    by apply/negb_neqP => Q; apply W; constructor => //; constructor.
  by move=> /prefixP [] /negb_neqP W _ /prefixP [??]; apply W.
move=> a l IH b; rewrite eqEsubset; split => x => //.
  move=> //= /prefixP/not_andP [/negb_neqP nbx|].
  apply/prefixP; split=> //=. move: (IH a) => //=; rewrite eqEsubset.
  case => + _. apply.


Section cantor_sets.

Context {R: realFieldType} {base : nat}.
Local Open Scope ereal_scope.
Local Open Scope ring_scope.
Definition cantor_map (x : cantor_space) : R := 
  lim (series (fun n => 
    (if x n then ((base%:~R - 1) * (1/(base%:~R))^+n ) else 0) : R)).

End cantor_sets.

Definition cantor_ternary {R : realFieldType} := @cantor_map R 3 @` [set: cantor_space].
