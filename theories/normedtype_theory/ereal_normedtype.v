(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference ereal reals topology.
From mathcomp Require Import separation_axioms function_spaces real_interval.
From mathcomp Require Import prodnormedzmodule tvs.
From mathcomp Require Import num_normedtype.

(**md**************************************************************************)
(* # Preliminaries for norm-related notions                                   *)
(*                                                                            *)
(* This file contains various definitions and lemmas about topological        *)
(* notions for extended numeric types that are useful to develop the theory   *)
(* of normed modules in this directory.                                       *)
(*                                                                            *)
(* ## Limit superior and inferior                                             *)
(* ```                                                                        *)
(*   limf_esup f F, limf_einf f F == limit sup/inferior of f at "filter" F    *)
(*                                   f has type X -> \bar R.                  *)
(*                                   F has type set (set X).                  *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Lower semicontinuous                                                    *)
(* ```                                                                        *)
(*         lower_semicontinuous f == the extended real-valued function f is   *)
(*                                   lower-semicontinuous. The type of f is   *)
(*                                   X -> \bar R with X : topologicalType and *)
(*                                   R : realType                             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section limf_esup_einf.
Variables (T : choiceType) (X : filteredType T) (R : realFieldType).
Implicit Types (f : X -> \bar R) (F : set (set X)).
Local Open Scope ereal_scope.

Definition limf_esup f F := ereal_inf [set ereal_sup (f @` V) | V in F].

Definition limf_einf f F := - limf_esup (\- f) F.

Lemma limf_esupE f F :
  limf_esup f F = ereal_inf [set ereal_sup (f @` V) | V in F].
Proof. by []. Qed.

Lemma limf_einfE f F :
  limf_einf f F = ereal_sup [set ereal_inf (f @` V) | V in F].
Proof.
rewrite /limf_einf limf_esupE /ereal_inf oppeK -[in RHS]image_comp /=.
congr (ereal_sup [set _ | _ in [set ereal_sup _ | _ in _]]).
by under eq_fun do rewrite -image_comp.
Qed.

Lemma limf_esupN f F : limf_esup (\- f) F = - limf_einf f F.
Proof. by rewrite /limf_einf oppeK. Qed.

Lemma limf_einfN f F : limf_einf (\- f) F = - limf_esup f F.
Proof. by rewrite /limf_einf; under eq_fun do rewrite oppeK. Qed.

End limf_esup_einf.

Section limf_esup_einf_realType.
Variables (T : choiceType) (X : filteredType T) (R : realType).
Implicit Types (f : X -> \bar R) (F : set (set X)).
Local Open Scope ereal_scope.

Lemma limf_esup_ge0 f F : ~ F set0 ->
  (forall x, 0 <= f x) -> 0 <= limf_esup f F.
Proof.
move=> F0 f0; rewrite limf_esupE; apply: le_ereal_inf_tmp => /= x [A].
have [-> /F0//|/set0P[y Ay FA] <-{x}] := eqVneq A set0.
by apply: le_ereal_sup_tmp; exists (f y).
Qed.

End limf_esup_einf_realType.

Section lower_semicontinuous.
Context {X : topologicalType} {R : numFieldType}.
Implicit Types f : X -> \bar R.
Local Open Scope ereal_scope.

Definition lower_semicontinuous f := forall x a, a%:E < f x ->
  exists2 V, nbhs x V & forall y, V y -> a%:E < f y.

Lemma lower_semicontinuousP f :
  lower_semicontinuous f <-> forall a, open [set x | f x > a%:E].
Proof.
split=> [sci a|openf x a afx].
  rewrite openE /= => x /= /sci[A + Aaf]; rewrite nbhsE /= => -[B xB BA].
  apply: nbhs_singleton; apply: nbhs_interior.
  by rewrite nbhsE /=; exists B => // y /BA /=; exact: Aaf.
exists [set x | a%:E < f x] => //.
by rewrite nbhsE/=; exists [set x | a%:E < f x].
Qed.

End lower_semicontinuous.

#[global] Hint Extern 0 (is_true (_ < ?x)%E) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_pinfty_gt] end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)%E) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_pinfty_ge] end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)%E) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_ninfty_lt] end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)%E) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_ninfty_le] end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_pinfty_real] end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; apply: ereal_nbhs_ninfty_real] end : core.

Section ecvg_infty_numField.
Local Open Scope ereal_scope.
Context {R : numFieldType}.

Let cvgeyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E < x;
(* 3 *) \forall A \near +oo%R, \forall x \near F, A%:E < x;
(* 4 *) \forall A \near +oo%R, \forall x \near F, A%:E <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Let cvgeNyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E > x;
(* 3 *) \forall A \near -oo%R, \forall x \near F, A%:E > x;
(* 4 *) \forall A \near -oo%R, \forall x \near F, A%:E >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types (f : T -> \bar R) (u : T -> R).

Lemma cvgeyPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 1%N). Qed.

Lemma cvgeyPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 2%N). Qed.

Lemma cvgeyPgty f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 3%N). Qed.

Lemma cvgeyPgey f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 4%N). Qed.

Lemma cvgeNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 1%N). Qed.

Lemma cvgeNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 2%N). Qed.

Lemma cvgeNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 3%N). Qed.

Lemma cvgeNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 4%N). Qed.

Lemma cvgey_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPger. Qed.

Lemma cvgey_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgtr. Qed.

Lemma cvgeNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPler. Qed.

Lemma cvgeNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPltr. Qed.

Lemma cvgNey f : (\- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgeNyPler cvgeyPger; split=> Foo A Areal;
by near do rewrite -leeN2 ?oppeK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNeNy f : (\- f @ F --> -oo) <-> (f @ F --> +oo).
Proof.
by rewrite -cvgNey (_ : \- \- f = f)//; apply/funeqP => x /=; rewrite oppeK.
Qed.

Lemma cvgeryP u : ((u x)%:E @[x --> F] --> +oo) <-> (u @ F --> +oo%R).
Proof.
split=> [/cvgeyPger|/cvgryPger] Foo.
  by apply/cvgryPger => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeyPger => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

Lemma cvgerNyP u : ((u x)%:E @[x --> F] --> -oo) <-> (u @ F --> -oo%R).
Proof.
split=> [/cvgeNyPler|/cvgrNyPler] Foo.
  by apply/cvgrNyPler => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeNyPler => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

End ecvg_infty_numField.

Section ecvg_infty_realField.
Local Open Scope ereal_scope.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> \bar R).

Lemma cvgeyPge : f @ F --> +oo <-> forall A, \forall x \near F, A%:E <= f x.
Proof.
by rewrite cvgeyPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeyPgt : f @ F --> +oo <-> forall A, \forall x \near F, A%:E < f x.
Proof.
by rewrite cvgeyPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A%:E >= f x.
Proof.
by rewrite cvgeNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A%:E > f x.
Proof.
by rewrite cvgeNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgey_ge : f @ F --> +oo -> forall A, \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPge. Qed.

Lemma cvgey_gt : f @ F --> +oo -> forall A, \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgt. Qed.

Lemma cvgeNy_le : f @ F --> -oo -> forall A, \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPle. Qed.

Lemma cvgeNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPlt. Qed.

End ecvg_infty_realField.

Section open_closed_sets_ereal.
Variable R : realFieldType (* TODO: generalize to numFieldType? *).
Local Open Scope ereal_scope.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R | r%:E < y].
Proof.
case: y => [y||] /=; first exact: open_lt.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltry trueE.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set r : R | y < r%:E].
Proof.
case: y => [y||] /=; first exact: open_gt.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltNyr trueE.
Qed.

Lemma open_ereal_lt' x y : x < y -> ereal_nbhs x (fun u => u < y).
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
- case: y => [y||//] /= in xy *; last by exists 0%R.
  by exists y; rewrite num_real; split => //= x ?.
- case: y => [y||//] /= in xy *.
  + by exists y; rewrite num_real; split => //= x ?.
  + by exists 0%R; split => // x /lt_le_trans; apply; rewrite leey.
Qed.

Lemma open_ereal_gt' x y : y < x -> ereal_nbhs x (fun u => y < u).
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0.
- by exists y; rewrite num_real.
- by move=> _; exists 0%R; split => // x; apply/le_lt_trans; rewrite leNye.
Qed.

Lemma open_ereal_lt_ereal x : open [set y | y < x].
Proof.
have openr r : open [set x : \bar R | x < r%:E].
  (* BUG: why doesn't case work? *)
  move=> [? | // | ?]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_lt r%:E); rewrite openE; apply; rewrite /= lte_fin.
move: x => [ // | | ]; last by move=> []. (* same BUG *)
suff -> : [set y | y < +oo] = \bigcup_r [set y : \bar R | y < r%:E].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltry; split => // _.
  by exists (r + 1)%R => //=; rewrite lte_fin ltrDl.
- by rewrite ltxx; split => // -[] x /=; rewrite ltNge leey.
- by split => // _; exists 0%R => //=; rewrite ltNye.
Qed.

Lemma open_ereal_gt_ereal x : open [set y | x < y].
Proof.
have openr r : open [set x | r%:E < x].
  move=> [? | ? | //]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_gt r%:E); rewrite openE; apply; rewrite /= lte_fin.
case: x => [ // | | ]; first by move=> [].
suff -> : [set y | -oo < y] = \bigcup_r [set y : \bar R | r%:E < y].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltNyr; split => // _.
  by exists (r - 1)%R => //=; rewrite lte_fin ltrBlDr ltrDl.
- by split => // _; exists 0%R => //=; rewrite ltey.
- by rewrite ltxx; split => // -[] x _ /=; rewrite ltNge leNye.
Qed.

Lemma closed_ereal_le_ereal y : closed [set x | y <= x].
Proof.
rewrite (_ : [set x | y <= x] = ~` [set x | y > x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal y : closed [set x | y >= x].
Proof.
rewrite (_ : [set x | y >= x] = ~` [set x | y < x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_gt_ereal.
Qed.

End open_closed_sets_ereal.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_EFin r (X : set R) :
  nbhs r X -> nbhs r%:E ((fun r => r%:E) @` X).
Proof.
case => _/posnumP[e] xeX; exists e%:num => //= s res.
by exists s => //; exact: xeX.
Qed.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_pinfty r : (nbhs +oo [set y | r%:E < y])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= ltry].
Qed.

Lemma nbhs_open_ereal_ninfty r : (nbhs -oo [set y | y < r%:E])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= ltNyr].
Qed.

Lemma ereal_hausdorff : hausdorff_space (\bar R).
Proof.
move=> -[r| |] // [r' | |] //=.
- move=> rr'; congr (_%:E); apply Rhausdorff => /= A B rA r'B.
  have [/= z [[r0 ? r0z] [r1 ?]]] :=
    rr' _ _ (nbhs_image_EFin rA) (nbhs_image_EFin r'B).
  by rewrite -r0z => -[r1r0]; exists r0; split => //; rewrite -r1r0.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r : r < r + 1.
    by rewrite ltrDl.
  move/(_ _ _ loc_r (nbhs_open_ereal_pinfty (r + 1))) => -[z [zr rz]].
  by move: (lt_trans rz zr); rewrite lte_fin ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) loc_r : r - 1 < r.
    by rewrite ltrBlDr ltrDl.
  move/(_ _ _ loc_r (nbhs_open_ereal_ninfty (r - 1))) => -[z [rz zr]].
  by move: (lt_trans zr rz); rewrite ltxx.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r' : r' < r' + 1.
    by rewrite ltrDl.
  move/(_ _ _ (nbhs_open_ereal_pinfty (r' + 1)) loc_r') => -[z [r'z zr']].
  by move: (lt_trans zr' r'z); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_pinfty 0) (nbhs_open_ereal_ninfty 0)).
  by move=> -[z [zx xz]]; move: (lt_trans xz zx); rewrite ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) yB : r' - 1 < r'.
    by rewrite ltrBlDr ltrDl.
  move/(_ _ _ (nbhs_open_ereal_ninfty (r' - 1)) yB) => -[z [zr' r'z]].
  by move: (lt_trans r'z zr'); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_ninfty 0) (nbhs_open_ereal_pinfty 0)).
  by move=> -[z [zO Oz]]; move: (lt_trans Oz zO); rewrite ltxx.
Qed.

End ereal_is_hausdorff.

#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: ereal_hausdorff] : core.

Section ProperFilterERealType.
Context {T : Type} {a : set_system T} {Fa : ProperFilter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma cvge_to_ge f b c : f @ a --> c -> (\near a, b <= f a) -> b <= c.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_le_ereal _ b)) /[apply].
Qed.

Lemma cvge_to_le f b c : f @ a --> c -> (\near a, f a <= b) -> c <= b.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_ge_ereal _ b))/[apply].
Qed.

Lemma lime_ge x f : cvg (f @ a) -> (\near a, x <= f a) -> x <= lim (f @ a).
Proof. exact: cvge_to_ge. Qed.

Lemma lime_le x f : cvg (f @ a) -> (\near a, x >= f a) -> x >= lim (f @ a).
Proof. exact: cvge_to_le. Qed.

End ProperFilterERealType.

Lemma cvgenyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R)%:E @[n --> F] --> +oo%E) <-> (f @ F --> \oo).
Proof. by rewrite cvgeryP cvgrnyP. Qed.

Section nbhs_ereal.
Context {R : numFieldType} (P : \bar R -> Prop).

Lemma nbhs_EFin (x : R) : (\forall y \near x%:E, P y) <-> \near x, P x%:E.
Proof. done. Qed.

Lemma nbhs_ereal_pinfty :
  (\forall x \near +oo%E, P x) <-> [/\ P +oo%E & \forall x \near +oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.

Lemma nbhs_ereal_ninfty :
  (\forall x \near -oo%E, P x) <-> [/\ P -oo%E & \forall x \near -oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.
End nbhs_ereal.

Section ereal_OrderNbhs.
Variable R : realFieldType.

Let ereal_order_nbhsE (x : \bar R) :
  nbhs x = filter_from (fun i => itv_open_ends i /\ x \in i)
                       (fun i => [set` i]).
Proof.
apply/seteqP; split=> A.
- rewrite /nbhs/= /ereal_nbhs/=; move: x => [r [e/= e0 reA]||].
  + exists `](r - e)%:E, (r + e)%:E[ => [|[y|/andP[]//|//]]; rewrite ?in_itv/=.
    * by rewrite !lte_fin ltrBlDr andbb ltrDl; split => //; right.
    * by move/subset_ball_prop_in_itv : reA => /(_ y); rewrite /= !in_itv.
  + case=> M [Mreal MA].
    exists `]M%:E, +oo[ => [|y/=]; rewrite in_itv/= andbT ?ltry; last exact: MA.
    by split => //; left.
  + case=> M [Mreal MA].
    exists `]-oo, M%:E[ => [|y/=]; rewrite in_itv/= ?ltNyr; last exact: MA.
    by split => //; left.
- move=> [[ [[]/= r|[]] [[]/= s|[]] ]] [] []// _.
  + move=> /[dup]/ltgte_fin_num/fineK <-; rewrite in_itv/=.
    move=> /andP[rx sx] rsA; apply: (nbhs_interval rx sx) => z rz zs.
    by apply: rsA =>/=; rewrite in_itv/= rz.
  + rewrite nbhsE/= => rx rA; exists `]r, +oo[%classic => //.
    by split => //; rewrite set_itvE; exact: open_ereal_gt_ereal.
  + rewrite nbhsE/= => xs ?; exists `]-oo, s[%classic => //.
    by split => //; rewrite set_itvE; exact: open_ereal_lt_ereal.
  + by rewrite set_itvE/= subTset => _ ->; exact: filter_nbhsT.
Qed.

HB.instance Definition _ := Order_isNbhs.Build _ (\bar R) ereal_order_nbhsE.

End ereal_OrderNbhs.
