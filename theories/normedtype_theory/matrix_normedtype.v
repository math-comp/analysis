(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference reals topology.
From mathcomp Require Import separation_axioms function_spaces real_interval.
From mathcomp Require Import prodnormedzmodule tvs pseudometric_normed_Zmodule.
From mathcomp Require Import normed_module.

(**md**************************************************************************)
(* # Normed topological Abelian group of matrices                             *)
(*                                                                            *)
(* This file defines a `normedModType` of space of matrices. It also proves   *)
(* the Heine-Borel theorem, more precisely that a closed and bounded set of   *)
(* vectors in $\bar{R}^n$ is compact and various lemmas about compact sets.   *)
(*                                                                            *)
(* ```                                                                        *)
(*           mx_norm M == norm of the matrix M                                *)
(*                     := \big[maxr/0]_i `|x i.1 i.2|                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Proof.
move=> /= M s /= /(nbhs_ballP (M i j)) [e e0 es].
by apply/nbhs_ballP; exists e => //= N [_ MN]; exact/es/MN.
Qed.

#[local]Lemma rV_compact_nondegenerate (T : ptopologicalType) n
    (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (prod_topology _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (prod_topology _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter_ex.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : prod_topology _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in [set x | 'I_n.+1 x]];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma rV_compact (T : ptopologicalType) n (A : 'I_n -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n | forall i, A i (v ord0 i)].
Proof.
case: n A => [A _ | ]; last exact: rV_compact_nondegenerate.
have P0 : #|{: 'I_1 * 'I_0}| = 0 by rewrite card_prod/= !card_ord muln0.
pose v0 := Matrix (ffun0 P0 : {ffun 'I_1 * 'I_0 -> T}).
rewrite (_ : mkset _ = [set v0]); first exact: compact_set1.
by rewrite predeqE => x /=; split => [ _ | _ []//]; apply/rowP => -[].
Qed.

Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).

Definition mx_norm x : K := (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.
Proof. by []. Qed.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
rewrite !mx_normE [_ <= _%:num]num_le; apply/bigmax_leP.
split=> [|ij _]; first exact: addr_ge0.
rewrite mxE; apply: le_trans (ler_normD _ _) _.
by rewrite lerD// -[leLHS]nngE num_le; exact: le_bigmax.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le -[0]nngE mx_normE num_le => /andP[/bigmax_leP[_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -num_abs_eq0 eq_le (x0 (i, j))//= -num_le/=.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%R%:nng)) /=.
  by elim/big_ind : _ => // a b; rewrite num_max => -> ->; rewrite maxxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b%:num != 0 by exists i.
  by apply: contra H => b0; rewrite max_r.
+ suff /Ha[i xi] : a%:num != 0 by exists i.
  by apply: contra H => a0; rewrite max_l // ltW.
Qed.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/mx_norm_eq0->|x0] := eqVneq (mx_norm x) 0.
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -num_abs_le; last by rewrite mx_normE.
apply/bigmax_geP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
by rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; rewrite normr_id.
Qed.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Proof.
congr (_%:nngnum).
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE -num_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
by have [ab|ab] := leP a b; [rewrite max_r | rewrite max_l // ltW].
Qed.

HB.instance Definition _ (K : numDomainType) (m n : nat) :=
  Num.Zmodule_isNormed.Build K 'M[K]_(m, n)
    (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _)
    (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangle m n (M N : 'M[K]_(m, n)) :
  `|M + N| <= `|M| + `|N|.
Proof. exact: ler_normD. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. exact: ler_normD. Qed.

End example_of_sharing.

Section matrix_pseudoMetricNormedZmod.
Variables (K : numFieldType) (m n : nat).

Local Lemma ball_gt0 (x y : 'M[K]_(m, n)) e : ball x e y -> 0 < e.
Proof. by case. Qed.

Lemma mx_norm_ball : @ball _ 'M[K]_(m, n) = ball_ (fun x => `| x |).
Proof.
rewrite /normr /ball_ predeq3E => x e y/= /[!mx_normE]; split=> [[]|xey].
- move=> /[dup] => /ltW/nonnegP[{}e] e_gt0 xey.
  rewrite num_lt; apply/bigmax_ltP => /=.
  by rewrite -num_lt /=; split => // -[? ?] _; rewrite !mxE; exact: xey.
- have e_gt0 : 0 < e by rewrite (le_lt_trans _ xey).
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0.
  move=> /(bigmax_ltP _ _ _ (fun=> _%:itv)) /= [e0 xey].
  split=> // i j.
  by move: (xey (i, j)); rewrite !mxE; exact.
Qed.

HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build K 'M[K]_(m, n) mx_norm_ball.

End matrix_pseudoMetricNormedZmod.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R]_n) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
    [set v : 'rV[R]_n | forall i, v ord0 i \in `[(- (M + 1)), (M + 1)]].
  apply: (@rV_compact _  _ (fun=> `[(- (M + 1)), (M + 1)]%classic)).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltrDl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v x.1 x.2| | x : 'I_1 * 'I_n].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
by rewrite [leRHS]/normr /= mx_normrE; apply/bigmax_geP; right => /=; exists j.
Qed.

Section matrix_NormedModule.

Lemma mx_normZ (K : numDomainType) m n (l : K) (x : 'M[K]_(m, n)) :
  `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
    (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE maxr_pMr.
Qed.

HB.instance Definition _ (K : numFieldType) m n :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build K 'M[K]_(m, n)
    (@mx_normZ K m n).

End matrix_NormedModule.
