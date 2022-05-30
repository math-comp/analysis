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

Definition pull (x : cantor_space) : cantor_space := fun n => x (S n).

Lemma pull_projection_preimage (n : nat) (b : bool) : 
  pull @^-1` (prod_topo_apply n @^-1` [set b]) = prod_topo_apply (n.+1) @^-1` [set b].
Proof.  by rewrite eqEsubset; split=> x /=; rewrite /prod_topo_apply /pull /=. Qed.

Lemma continuous_pull : continuous pull.
move=> x; apply/ cvg_sup; first by apply: fmap_filter; case: (nbhs_filter x).
move=> n; apply/cvg_image; first by apply: fmap_filter; case: (nbhs_filter x).
  by rewrite eqEsubset; split=> u //= _; exists (fun=> u).
move=> W.
have Q: nbhs [set[set f n | f in A] | A in pull x @[x --> x]] [set pull x n].
  exists (prod_topo_apply n @^-1` [set (pull x n)]); first last.
    rewrite eqEsubset; split => u //=; first by  by case=> ? <- <-.
    move->; exists (pull x) => //=.
  apply: open_nbhs_nbhs; split.
    rewrite pull_projection_preimage; apply: open_comp; last exact: open_bool.
    by move=> + _; apply: prod_topo_apply_continuous.
  done.
have [] := (@subset_set2 _ W true false). 
- by rewrite -bool2E; exact: subsetT.
- by move=> ->; rewrite /nbhs /= => /principle_filterP.
- by move -> => /= /nbhs_singleton <-; exact Q.
- by move -> => /= /nbhs_singleton <-; exact Q.
- rewrite -bool2E => -> _; exists setT; last by rewrite eqEsubset; split.
  by rewrite /= preimage_setT; exact: filterT.
Qed.

Inductive prefix (x : cantor_space) : seq bool -> Prop := 
  | NilPrefix : prefix x nil 
  | ConsPrefix : forall b s, b = x 0 -> prefix (pull x) s -> prefix x (b :: s)
.

Fixpoint prefix_of (x : cantor_space) (n : nat) : seq bool :=
  match n with 
  | 0 => nil
  | S m => x 0 :: prefix_of (pull x) m
  end.

Definition fixed_prefix (s : seq bool) (x : cantor_space) : Prop := 
  prefix x s.

(*
Lemma prefix_near (x : cantor_space) (n: nat): 
  \forall y \near x, prefix_of y n = prefix_of x n.
Proof.
move: x; elim: n; first by move=>?; near=> y.
move=> n IH x; near=> y => //=; congr(_ :: _).
  near: y; pose U := (prod_topo_apply 0 @^-1` [set (x 0)]).
  have : open_nbhs x U.
    (split; last by []); apply: open_comp => //=; last exact: open_bool.
    by move=> + _; exact: prod_topo_apply_continuous.
  by rewrite open_nbhsE => [[_]].
by near: y; near_simpl; have /continuous_pull := (IH (pull x)); exact.
Unshelve. all: end_near. Qed.
*)

Lemma prefixP (x : cantor_space) (b : bool) (s : seq bool) : 
  prefix x (b :: s) <-> (b = x 0 /\ prefix (pull x) s).
Proof.
(* TODO: Why does `case` discard the nil case?*)
split; first by move=> pxb; inversion pxb; subst; tauto.
by move=>[??]; constructor.
Qed.

Lemma empty_prefix : fixed_prefix nil = [set: cantor_space] .
Proof. by rewrite eqEsubset; split => //= x _; constructor. Qed.


Lemma prefix_of_prefix (x : cantor_space) (i : nat) : 
  fixed_prefix (prefix_of x i) x.
Proof.
move:x; elim i=> //=; first (by move=> ?; rewrite empty_prefix).
by move=> n ind x /=; constructor => //=; exact: ind.
Qed.

Lemma fixed_prefixP (x y : cantor_space) (j : nat) : 
  fixed_prefix (prefix_of x j) y <->
  (forall i, i < j -> x i = y i).
Proof.
split.
  move=> + i; move: x y i; elim: j => //= j IH x y; case; first by move=> /prefixP [].
  by move=> i /prefixP [_ ?] ?; rewrite -/(pull x i) -/(pull y i); exact: IH.
move: x y; elim: j; first by move=> ? ? ?; rewrite empty_prefix.
move=> n IH x y xy; apply/prefixP; split; first by apply: xy.
by apply: IH => ? ?; apply: xy.
Qed.

Lemma fixed_prefixW (x y : cantor_space) (i j : nat) : 
  i < j ->
  fixed_prefix (prefix_of x j) y ->
  fixed_prefix (prefix_of x i) y.
Proof.
move=> ij /fixed_prefixP P; apply/fixed_prefixP=> k ?; apply: P.
exact: (ltn_trans _ ij).
Qed.

Lemma prefix_cvg (x : cantor_space) : 
  filter_from [set: nat] (fun n => fixed_prefix (prefix_of x n)) --> x.
Proof.
have ? : Filter (filter_from [set: nat] (fun n => fixed_prefix(prefix_of x n))).
  apply: filter_from_filter; first by exists 0.
  move=> i j _ _; exists (i + j) => //.
  move: x j; elim: i => //= i; first by move=> ?; rewrite empty_prefix setTI add0n.
  move=> IH x j /=; rewrite -addnE => z /prefixP [] x0z0 /IH [??].
  split; first by apply/prefixP; split => //.
  by apply: (@fixed_prefixW _ _ _ (j.+1)) => //=; apply/prefixP; split.
apply/cvg_sup => n; apply/cvg_image; first by (rewrite eqEsubset; split).
move=> W /=; rewrite /nbhs /= => /principle_filterP Wxn.
have [] := (@subset_set2 _ W true false). 
- by rewrite -bool2E; exact: subsetT.
- by move: Wxn => /[swap] ->.
- move: Wxn => /[swap] -> <-; exists (fixed_prefix (prefix_of x (n.+1))); first by exists (n.+1).
  rewrite eqEsubset; split => y; last (move=> -> /=; exists x => //=; exact: (prefix_of_prefix x (n.+1))).
  by case=> z /fixed_prefixP/(_ n) P <-; simpl; apply/sym_equal/P.
- move: Wxn => /[swap] -> <-; exists (fixed_prefix (prefix_of x (n.+1))); first by exists (n.+1).
  rewrite eqEsubset; split => y; last (move=> -> /=; exists x => //=; exact: (prefix_of_prefix x (n.+1))).
  by case=> z /fixed_prefixP/(_ n) P <-; simpl; apply/sym_equal/P.
- rewrite -bool2E => ->; exists setT; last by rewrite eqEsubset; split.
  exact: filterT.
Qed.

Lemma cantor_nbhs_prefix (x : cantor_space) (W : set cantor_space) : 
  nbhs x W -> exists n, fixed_prefix (prefix_of x n) `<=` W.
Proof.
move=> nbhsW; move: (@prefix_cvg x _ nbhsW) => /=; rewrite nbhs_simpl.
by case=> n _ ?; exists n.
Qed.

Lemma length_prefix_of (x : cantor_space) (n : nat) : 
  length (prefix_of x n) = n.
Proof.  by elim: n x => //= n IH x; congr( _ .+1); exact: IH. Qed.

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

Lemma fixed_prefix_unique (s1 s2 : seq bool) (x : cantor_space): 
  length s1 = length s2 -> fixed_prefix s1 x -> fixed_prefix s2 x -> s1 = s2.
Proof.
move: s2 x; elim s1. 
  by move=> ? ? ? ? ?; apply sym_equal; apply List.length_zero_iff_nil.
move=> a l1 IH [] //= b l2 x /eq_add_S lng /prefixP [] -> ? /prefixP [] -> ?. 
by congr (_ :: _); apply: (IH _ (pull x)) => //=.
Qed.

Lemma closed_fixed (s : seq bool) : closed (fixed_prefix s).
Proof.
elim s; first by rewrite empty_prefix //.
move=> b l clsFl x.
pose B := fixed_prefix (prefix_of x ((length l) + 1)).
move=> /(_ B) /=; case. 
  suff: (open_nbhs x B) by rewrite open_nbhsE=> [[]].
  by split; [exact: open_fixed | exact: prefix_of_prefix].
move=> y [] pfy By /=; suff -> : (b :: l = (prefix_of x (length l + 1))).
  exact: prefix_of_prefix.
apply: (@fixed_prefix_unique _ _ y) => //=. 
by rewrite length_prefix_of addn1.
Qed.


Section cantor_space_metric.

Definition is_min_diff (x y : cantor_space) (n : nat) : Prop :=
  x n != y n /\ (forall m, m < n -> x m == y m).

Lemma is_min_diff_sym (x y : cantor_space) (n : nat) : 
  is_min_diff x y n <-> is_min_diff y x n.
Proof.
by split; move=> [? W]; (split; first by rewrite eq_sym) => m; rewrite eq_sym; exact: W.
Qed.

Lemma is_min_diff_unique (x y : cantor_space) (m n : nat) : 
  is_min_diff x y n -> is_min_diff x y m -> n = m.
Proof.
wlog : n m / (n <= m).
  case (leqP n m); first by (move=> ? + ? ?; exact).
  by move=> ? W ? ?; apply sym_equal; apply W => //; exact: ltnW.
move=> W [neqN minN] [neqM minM]; apply/eqTleqif; first exact/leqif_geq.
by case (leqP m n)=> // => /minM; move/negP: neqN.
Qed.

Lemma cantor_space_neqP (x y : cantor_space) :
  x != y -> exists n, is_min_diff x y n.
Proof.
apply: contra_neqP=> /forallNP N; rewrite funeqE.
apply: (@well_founded_ind nat lt (Wf_nat.lt_wf) (fun q => x q = y q)) => n E.
move: (N n); apply contra_notP => /eqP; split => // M Mn; apply/eqP; apply E. 
exact/ ssrnat.leP.
Qed.

Definition min_diff (x y : cantor_space) : nat :=
  if pselect (x != y) is left neq
  then (projT1 (cid ((@cantor_space_neqP x y) neq)))
  else 0
.

Lemma min_diff_sym (x y : cantor_space) : 
  min_diff x y = min_diff y x.
Proof.
rewrite /min_diff; case (eqVneq x y); first by move=> ->.
move=> /[dup]; rewrite {2} eq_sym; (do 2 (case: pselect => //)).
move=> ? ? ? ?; apply: (@is_min_diff_unique x y); first exact: projT2.
by apply is_min_diff_sym; exact: projT2.
Qed.

Lemma min_diff_is_min_diff (x y : cantor_space) : 
  x != y -> is_min_diff x y (min_diff x y).
Proof. rewrite/ min_diff; case pselect => // ? ?; exact: projT2. Qed.

Lemma min_diff_le (x y : cantor_space) (n : nat) : 
  x != y ->
  (forall m, m < n -> x m == y m) -> n <= min_diff x y.
Proof.
move=> xneqy; elim: n => // n IH Q.
have: n <= min_diff x y by apply: IH=> ??; apply: Q; rewrite ltnS; apply ltnW.
rewrite leq_eqVlt=> /orP; case => //.
move: Q => /[swap] /eqP -> /(_ (min_diff x y) (ltnSn _)) /eqP. 
by have [+ _ ?] := min_diff_is_min_diff xneqy => /eqP ?.
Qed.

Context {R : realType}.

Definition cantor_dist (x y : cantor_space) : R := 
  (if pselect (x != y) is left neq
  then (GRing.natmul (GRing.one R) ((min_diff x y).+1))^-1 else 0)%R.
Proof.

Lemma cantor_dist_sym (x y : cantor_space) : 
  cantor_dist x y = cantor_dist y x.
Proof.
rewrite /cantor_dist; case: (eqVneq x y) => //=; first by move=> ->.
by rewrite min_diff_sym.
Qed.

Lemma cantor_dist_refl (x : cantor_space) : 
  cantor_dist x x = (0)%R.
Proof.
by rewrite /cantor_dist; case pselect => //= ?; exact: (@contra_neqP _ x x).
Qed.

Lemma cantor_dist_pos (x y : cantor_space) : 
  (x != y -> 0 < (cantor_dist x y))%R.
Proof.
rewrite /cantor_dist; case pselect => //= ? _.
Qed.
 
Lemma cantor_dist_nneg (x y : cantor_space) : (0 <= cantor_dist x y)%R.
Proof.
case E : (x != y); first by apply ltW; exact: cantor_dist_pos.
by move/negbT/negPn/eqP: E => ->; rewrite cantor_dist_refl.
Qed.

Lemma min_diff_trans (x y z : cantor_space) : 
  (x != y) -> 
  (y != z) -> 
  (x != z) -> 
  Order.min (min_diff x y) (min_diff y z) <= min_diff x z .
Proof.
wlog yzLe : x y z / (min_diff x y <= min_diff y z).
  case/orP: (@leq_total (min_diff y z) (min_diff x y)).
    move=> ? E2; rewrite minC => ? ? ?.
    rewrite (min_diff_sym x z) (min_diff_sym y z) (min_diff_sym x y).
    apply: E2; try (rewrite eq_sym //). 
    by rewrite (min_diff_sym y x) (min_diff_sym z y).
  by move=> /[swap]; apply.
rewrite min_l // => ???; apply: min_diff_le => // m mLe. 
have [ // | _ /(_ _ mLe) /eqP -> ] := @min_diff_is_min_diff x y _.
have [ // | _ ] := @min_diff_is_min_diff y z; apply.
rewrite leq_eqVlt in yzLe; case/orP: yzLe; first by move=>/eqP <-.
by apply ltn_trans.
Qed.

Lemma cantor_dist_triangle (x y z : cantor_space) : 
  (cantor_dist x z <= cantor_dist x y + cantor_dist y z)%R.
Proof.
wlog yzLe : x y z / (min_diff x y <= min_diff y z).
    case/orP: (@leq_total (min_diff y z) (min_diff x y)).
    move=> ? E2; rewrite addrC.
    rewrite (cantor_dist_sym x z) (cantor_dist_sym y z) (cantor_dist_sym x y).
    by apply: E2 => //=; rewrite (min_diff_sym y x) (min_diff_sym z y).
  by move=> /[swap]; apply.
rewrite {1}/cantor_dist; case pselect; last first.
  move=>/negP/negPn/eqP ->; apply addr_ge0; exact: cantor_dist_nneg.
move=> xz; rewrite {1}/cantor_dist; case pselect; last first.
  move=>/negP/negPn/eqP <-; rewrite add0r; rewrite /cantor_dist. 
  by case pselect.
move=> xy; rewrite /cantor_dist; case pselect; last first.
  by move=>/negP/negPn/eqP ->; rewrite addr0.
move=> yz.
have := (@min_diff_trans x y z xy yz xz); rewrite min_l // => lexz.
Search (GRing.natmul) (GRing.inv).
rewrite -ler_pinv ?invrK; first last.
  + rewrite inE; apply/andP; split;[rewrite unitfE; apply: lt0r_neq0|]; exact: gt0.
  + rewrite inE; apply/andP; split;[rewrite unitfE; apply: lt0r_neq0|]; exact: gt0.
rewrite -[w in (w + _)%R]div1r -[w in (_ + w)%R]div1r. 
rewrite GRing.addf_div ?mul1r; first last. 
  + apply: lt0r_neq0; exact: gt0.
  + apply: lt0r_neq0; exact: gt0.
rewrite invf_div ler_pdivr_mulr; first last.
  + exact: gt0.
rewrite -natrD -?natrM ler_nat mulnDr.
apply: (@leq_trans  (S(min_diff x z) * S(min_diff y z))).
  rewrite leq_pmul2r //=.
apply leq_addr.
Qed.

Check entourage_.
Definition cantor_ball (x : cantor_space) (eps : R) (y : cantor_space) : Prop := 
  (cantor_dist x y < eps)%R.

Definition cantor_ball_center (x : cantor_space) (e : R) : 
  (0 < e)%R -> cantor_ball x e x.
Proof. by move=> ?; rewrite /cantor_ball cantor_dist_refl. Qed.

Definition cantor_ball_sym (x y : cantor_space) (e : R) : 
  cantor_ball x e y -> cantor_ball y e x.
Proof. by rewrite /cantor_ball cantor_dist_sym. Qed.

Definition cantor_ball_triangle (x y z : cantor_space) (e1 e2 : R) : 
  cantor_ball x e1 y -> cantor_ball y e2 z -> cantor_ball x (e1 + e2) z.
Proof. 
rewrite /cantor_ball => L1 L2. 
by apply: (le_lt_trans (@cantor_dist_triangle x y z)); exact: ltr_add.
Qed.

Definition cantor_space_pseudo_metric_mixin : 
  (@PseudoMetric.mixin_of R cantor_space (entourage_ cantor_ball)) :=
  PseudoMetricMixin cantor_ball_center cantor_ball_sym cantor_ball_triangle erefl.

Lemma cantor_space_uniformity : nbhs = nbhs_ (entourage_ cantor_ball).
Proof.
rewrite funeqE=> x; rewrite eqEsubset; split=> W /=.
Qed.

Program Definition cantor_space_uniformity_mixin := 
  uniformityOfBallMixin cantor_space_uniformity cantor_space_pseudo_metric_mixin.

Canonical cantor_space_uniform := 
  UniformType cantor_space cantor_space_uniformity_mixin.

Canonical cantor_space_pseudo_metric := 
  PseudoMetricType cantor_space cantor_space_pseudo_metric_mixin.


End cantor_space_metric.

Section cantor_sets.

Context {R: realFieldType} {base : nat}.
Local Open Scope ereal_scope.
Local Open Scope ring_scope.
Definition cantor_map (x : cantor_space) : R := 
  lim (series (fun n => 
    (if x n then ((base%:~R - 1) * (1/(base%:~R))^+n ) else 0) : R)).

End cantor_sets.

Definition cantor_ternary {R : realFieldType} := @cantor_map R 3 @` [set: cantor_space].
