(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality set_interval.
From mathcomp Require Import interval_inference reals topology.
From mathcomp Require Import function_spaces real_interval.
From mathcomp Require Import prodnormedzmodule tvs.

(**md**************************************************************************)
(* # Preliminaries for norm-related notions                                   *)
(*                                                                            *)
(* This file contains various definitions and lemmas about topological        *)
(* notions of numeric types that are useful to develop the theory of normed   *)
(* modules in this directory.                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*         pinfty_nbhs == filter for +oo (for a numFieldType)                 *)
(*                        Notation: +oo (ring_scope)                          *)
(*         ninfty_nbhs == filter for -oo (for a numFieldType)                 *)
(*                        Notation: -oo (ring_scope)                          *)
(*       is_interval E == the set E is an interval                            *)
(*  bigcup_ointsub U q == union of open real interval included                *)
(*                        in U and that contain the rational                  *)
(*                        number q                                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*   f @`[ a , b ], f @`] a , b [ == notations for images of intervals,       *)
(*                                   intended for continuous, monotonous      *)
(*                                   functions, defined in ring_scope and     *)
(*                                   classical_set_scope respectively as:     *)
(*                  f @`[ a , b ] := `[minr (f a) (f b), maxr (f a) (f b)]%O  *)
(*                  f @`] a , b [ := `]minr (f a) (f b), maxr (f a) (f b)[%O  *)
(*                  f @`[ a , b ] := `[minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)]%classic              *)
(*                  f @`] a , b [ := `]minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)[%classic              *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "f @`[ a , b ]" (at level 20, b at level 9,
  format "f  @`[ a ,  b ]").
Reserved Notation "f @`] a , b [" (at level 20, b at level 9,
  format "f  @`] a ,  b [").
Reserved Notation "+oo_ R" (at level 3, left associativity, format "+oo_ R").
Reserved Notation "-oo_ R" (at level 3, left associativity, format "-oo_ R").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* multi-rule bound_in_itv already exists in interval.v, but we
  advocate that it should actually have the following statement.
  This does not expose the order between interval bounds. *)
Lemma bound_itvE (R : numDomainType) (a b : R) :
  ((a \in `[a, b]) = (a <= b)) *
  ((b \in `[a, b]) = (a <= b)) *
  ((a \in `[a, b[) = (a < b)) *
  ((b \in `]a, b]) = (a < b)) *
  (a \in `[a, +oo[) *
  (a \in `]-oo, a]).
Proof. by rewrite !(boundr_in_itv, boundl_in_itv). Qed.

Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]) : ring_scope.
Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]%classic) : classical_set_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[) : ring_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[%classic) : classical_set_scope.

Section image_interval.
Variable R : realDomainType.
Implicit Types (a b : R) (f : R -> R).

Lemma mono_mem_image_segment a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `[a, b] >-> x \in f @`[a, b]}.
Proof.
move=> [fle|fge] x xab; have leab : a <= b by rewrite (itvP xab).
  have: f a <= f b by rewrite fle ?bound_itvE.
  by case: leP => // fafb _; rewrite in_itv/= !fle ?(itvP xab).
have: f a >= f b by rewrite fge ?bound_itvE.
by case: leP => // fafb _; rewrite in_itv/= !fge ?(itvP xab).
Qed.

Lemma mono_mem_image_itvoo a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `]a, b[ >-> x \in f @`]a, b[}.
Proof.
move=> []/[dup] => [/leW_mono_in|/leW_nmono_in] flt fle x xab;
    have ltab : a < b by rewrite (itvP xab).
  have: f a <= f b by rewrite ?fle ?bound_itvE ?ltW.
  by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
have: f a >= f b by rewrite fle ?bound_itvE ?ltW.
by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
Qed.

Lemma mono_surj_image_segment a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  f @` `[a, b] = f @`[a, b]%classic.
Proof.
move=> leab fmono; apply: surj_image_eq => _ /= [x xab <-];
exact: mono_mem_image_segment.
Qed.

Lemma inc_segment_image a b f : f a <= f b -> f @`[a, b] = `[f a, f b].
Proof. by case: ltrP. Qed.

Lemma dec_segment_image a b f : f b <= f a -> f @`[a, b] = `[f b, f a].
Proof. by case: ltrP. Qed.

Lemma inc_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  f @` `[a, b] = `[f a, f b]%classic.
Proof.
move=> leab fle f_surj; have fafb : f a <= f b by rewrite fle ?bound_itvE.
by rewrite mono_surj_image_segment ?inc_segment_image//; left.
Qed.

Lemma dec_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  f @` `[a, b] = `[f b, f a]%classic.
Proof.
move=> leab fge f_surj; have fafb : f b <= f a by rewrite fge ?bound_itvE.
by rewrite mono_surj_image_segment ?dec_segment_image//; right.
Qed.

Lemma inc_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f a, f b]).
Proof.
move=> /inc_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma dec_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f b, f a]).
Proof.
move=> /dec_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma mono_surj_image_segmentP a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in f @`[a, b]).
Proof.
move=> /mono_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

End image_interval.

Lemma bigcup_ballT {R : realType} : \bigcup_n ball (0%R : R) n%:R = setT.
Proof.
rewrite -[RHS](bigcup_itvT false true); apply: eq_bigcup => //= n _.
by apply/seteqP; split=> [?|?]; rewrite /ball/= sub0r normrN in_itv/= ltr_norml.
Qed.

Section nbhs_pseudoMetricType.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallNE notK => exNP.
pose D := [set d : R^o | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/nbhs_ballP; exists e%:num => /=. Qed.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /nbhs_ballP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /nbhs_ballP xP.
pose D := [set d : R^o | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End nbhs_pseudoMetricType.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrCA addKr normrN ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
Qed.

#[global] Hint Extern 0 (ProperFilter _^') =>
  solve[apply: Proper_dnbhs_numFieldType] : typeclass_instances.

Definition pinfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo_ R" := (pinfty_nbhs R) (only parsing) : ring_scope.
Notation "-oo_ R" := (ninfty_nbhs R) (only parsing) : ring_scope.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Lemma ninftyN {R : numFieldType} : (- x : R)%R @[x --> -oo] = +oo.
Proof.
apply/seteqP; split => [A [M [Mreal MA]]|A [M [Mreal MA]]].
  exists (- M); rewrite realN; split => // x.
  by rewrite ltrNl => /MA/=; rewrite opprK.
by exists (- M); rewrite ?realN; split=> // x; rewrite ltrNr => /MA.
Qed.

Lemma ninfty {R : numFieldType} : (- x : R)%R @[x --> +oo] = -oo.
Proof.
apply/seteqP; split => [A [M [Mreal MA]]|A [M [Mreal MA]]].
  exists (- M); rewrite realN; split => // x.
  by rewrite -ltrNr => /MA/=; rewrite opprK.
by exists (- M); rewrite ?realN; split=> // x; rewrite ltrNl => /MA.
Qed.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Implicit Types r : R.

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Proof.
apply Build_ProperFilter_ex.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltrDl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0.
- exists (maxr MP MQ); split=> [|x]; first exact: max_real.
  by rewrite comparable_gt_max ?real_comparable // => /andP[/gtMP ? /gtMQ].
- by exists M; split => // ? /gtM /sPQ.
Qed.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Proof.
apply Build_ProperFilter_ex.
  move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtrDl oppr_lt0.
split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
- by exists 0.
- exists (Num.min MP MQ); split=> [|x]; first exact: min_real.
  by rewrite comparable_lt_min ?real_comparable // => /andP[/ltMP ? /ltMQ].
- by exists M; split => // x /ltM /sPQ.
Qed.

Lemma nbhs_pinfty_gt r : r \is Num.real -> \forall x \near +oo, r < x.
Proof. by exists r. Qed.

Lemma nbhs_pinfty_ge r : r \is Num.real -> \forall x \near +oo, r <= x.
Proof. by exists r; split => //; apply: ltW. Qed.

Lemma nbhs_ninfty_lt r : r \is Num.real -> \forall x \near -oo, r > x.
Proof. by exists r. Qed.

Lemma nbhs_ninfty_le r : r \is Num.real -> \forall x \near -oo, r >= x.
Proof. by exists r; split => // ?; apply: ltW. Qed.

Lemma nbhs_pinfty_real : \forall x \near +oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_pinfty_gt (@real0 _)); apply: gtr0_real. Qed.

Lemma nbhs_ninfty_real : \forall x \near -oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_ninfty_lt (@real0 _)); apply: ltr0_real. Qed.

Lemma pinfty_ex_gt (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_gt.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_ge (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m <= M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_gt0 (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Proof. exact: pinfty_ex_gt. Qed.

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
move=> [M [Mreal AM]]; exists (M * 2); split; first by rewrite realM.
by move=> x; rewrite -ltr_pdivlMr //; exact: AM.
Qed.

Lemma not_near_inftyP (P : pred R) :
  ~ (\forall x \near +oo, P x) <->
    forall M : R, M \is Num.real -> exists2 x, M < x & ~ P x.
Proof.
rewrite nearE -forallNP -propeqE; apply: eq_forall => M.
by rewrite propeqE -implypN existsPNP.
Qed.

Lemma not_near_ninftyP (P : pred R):
  ~ (\forall x \near -oo, P x) <->
    forall M : R, M \is Num.real -> exists2 x, x < M & ~ P x.
Proof.
rewrite -filterN ninftyN not_near_inftyP/=; split => PN M; rewrite -realN;
by move=> /PN[x Mx PNx]; exists (- x) => //; rewrite 1?(ltrNl,ltrNr,opprK).
Qed.

End infty_nbhs_instances.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_pinfty_gt] end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_pinfty_ge] end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_ninfty_lt] end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_ninfty_le] end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_pinfty_real] end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => solve[near: x; now apply: nbhs_ninfty_real] end : core.

Section cvg_infty_numField.
Context {R : numFieldType}.

Let cvgryPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A < x;
(* 3 *) \forall A \near +oo, \forall x \near F, A < x;
(* 4 *) \forall A \near +oo, \forall x \near F, A <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do apply: (@lt_le_trans _ _ B) => //=; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; apply: (@lt_le_trans _ _ B) => //]; apply: AF.
Unshelve. all: by end_near. Qed.

Let cvgrNyPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A > x;
(* 3 *) \forall A \near -oo, \forall x \near F, A > x;
(* 4 *) \forall A \near -oo, \forall x \near F, A >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do apply: (@le_lt_trans _ _ B) => //; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; apply: (@le_lt_trans _ _ B) => //]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types f : T -> R.

Lemma cvgryPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 1%N). Qed.

Lemma cvgryPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 2%N). Qed.

Lemma cvgryPgty f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 3%N). Qed.

Lemma cvgryPgey f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 4%N). Qed.

Lemma cvgrNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 1%N). Qed.

Lemma cvgrNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 2%N). Qed.

Lemma cvgrNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 3%N). Qed.

Lemma cvgrNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 4%N). Qed.

Lemma cvgry_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. by rewrite cvgryPger. Qed.

Lemma cvgry_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. by rewrite cvgryPgtr. Qed.

Lemma cvgrNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPler. Qed.

Lemma cvgrNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPltr. Qed.

Lemma cvgNry f : (- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgrNyPler cvgryPger; split=> Foo A Areal;
by near do rewrite -lerN2 ?opprK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNrNy f : (- f @ F --> -oo) <-> (f @ F --> +oo).
Proof. by rewrite -cvgNry opprK. Qed.

End cvg_infty_numField.

Section cvg_infty_realField.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> R).

Lemma cvgryPge : f @ F --> +oo <-> forall A, \forall x \near F, A <= f x.
Proof.
by rewrite cvgryPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgryPgt : f @ F --> +oo <-> forall A, \forall x \near F, A < f x.
Proof.
by rewrite cvgryPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A >= f x.
Proof.
by rewrite cvgrNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A > f x.
Proof.
by rewrite cvgrNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgry_ge : f @ F --> +oo -> forall A, \forall x \near F, A <= f x.
Proof. by rewrite cvgryPge. Qed.

Lemma cvgry_gt : f @ F --> +oo -> forall A, \forall x \near F, A < f x.
Proof. by rewrite cvgryPgt. Qed.

Lemma cvgrNy_le : f @ F --> -oo -> forall A, \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPle. Qed.

Lemma cvgrNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPlt. Qed.

End cvg_infty_realField.

Lemma cvgr_expr2 {R : realFieldType} : (x ^+ 2 : R) @[x --> +oo] --> +oo.
Proof.
by apply/cvgryPge => M; near=> x; rewrite (@le_trans _ _ x)// expr2 ler_peMl.
Unshelve. all: end_near. Qed.

Lemma cvgr_idn {R : realType} : (n%:R : R) @[n --> \oo] --> +oo.
Proof.
by apply/cvgryPge => M; exact: nbhs_infty_ger.
Unshelve. all: end_near. Qed.

Lemma cvgrnyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R) @[n --> F] --> +oo) <-> (f @ F --> \oo).
Proof.
split=> [/cvgryPge|/cvgnyPge] Foo.
  by apply/cvgnyPge => A; near do rewrite -(@ler_nat R); apply: Foo.
apply/cvgryPgey; near=> A; near=> n.
rewrite pmulrn ceil_le_int// [ceil _]intEsign.
by rewrite le_gtF ?expr0 ?mul1r ?lez_nat ?ceil_ge0//; near: n; apply: Foo.
Unshelve. all: by end_near. Qed.

Section gt0_cvg.
Context {R : realFieldType} {F : set_system R} {FF : Filter F}.
Variables (M : R) (f : R -> R).
Hypothesis M0 : 0 < M.

Lemma gt0_cvgMlNy : (f r) @[r --> F] --> -oo -> (f r * M)%R @[r --> F] --> -oo.
Proof.
move=> /cvgrNyPle fy; apply/cvgrNyPle => A.
by apply: filterS (fy (A / M)) => x; rewrite ler_pdivlMr.
Qed.

Lemma gt0_cvgMrNy : (f r) @[r --> F] --> -oo -> (M * f r)%R @[r --> F] --> -oo.
Proof. by move=> fy; under eq_fun do rewrite mulrC; exact: gt0_cvgMlNy. Qed.

Lemma gt0_cvgMly : f r @[r --> F] --> +oo -> (f r * M)%R @[r --> F] --> +oo.
Proof.
move=> /cvgryPge fy; apply/cvgryPge => A.
by apply: filterS (fy (A / M)) => x; rewrite ler_pdivrMr.
Qed.

Lemma gt0_cvgMry : f r @[r --> F] --> +oo -> (M * f r)%R @[r --> F] --> +oo.
Proof. by move=> fy; under eq_fun do rewrite mulrC; exact: gt0_cvgMly. Qed.

End gt0_cvg.

Lemma cvgNy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> -oo] --> l <-> (f \o -%R) x @[x --> +oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg -oo _ f_opp) fmap_comp ninftyN.
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `cvgNy_compNP`")]
Notation cvgyNP := cvgNy_compNP (only parsing).

Lemma cvgy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> +oo] --> l <-> (f \o -%R) x @[x --> -oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg +oo _ f_opp) fmap_comp ninfty.
Qed.

Section monotonic_itv_bigcup.
Context {R : realType}.
Implicit Types (F : R -> R) (a : R).

Lemma decreasing_itvNyo_bigcup F a :
  {in `[a, +oo[ &, {homo F : x y /~ x < y}} ->
  F x @[x --> +oo] --> -oo ->
  (`]-oo, F a[ = \bigcup_i `]F (a + i.+1%:R), F a[)%classic.
Proof.
move=> dF nyF; rewrite itvNy_bnd_bigcup_BLeft eqEsubset; split.
- move=> y/= [n _]/=; rewrite in_itv/= => /andP[Fany yFa].
  have [i iFan] : exists i, F (a + i.+1%:R) < F a - n%:R.
    move/cvgrNy_lt : nyF.
    move/(_ (F a - n%:R)) => [z [zreal zFan]].
    by exists (trunc (z - a)); rewrite zFan// -ltrBlDl truncnS_gt.
  by exists i => //=; rewrite in_itv/= yFa (lt_le_trans _ Fany).
- move=> z/= [n _ /=]; rewrite in_itv/= => /andP[Fanz zFa].
  exists `|ceil (F (a + n.+1%:R) - F a)%R|.+1 => //=.
  rewrite in_itv/= zFa andbT lerBlDr -lerBlDl (le_trans _ (abs_ceil_ge _))//.
  by rewrite ler_normr orbC opprB lerB// ltW.
Qed.

Lemma decreasing_itvoo_bigcup F a n :
  {in `[a, +oo[ &, {homo F : x y /~ x < y}} ->
  (`]F (a + n%:R), F a[ = \bigcup_(i < n) `]F (a + i.+1%:R), F a[)%classic.
Proof.
move=> decrF; rewrite eqEsubset; split.
- move: n => [|n]; first by rewrite addr0 set_itvoo0.
  by apply: (@bigcup_sup _ _ n) => /=.
- apply: bigcup_sub => k/= kn; apply: subset_itvr; rewrite bnd_simp.
  move: kn; rewrite leq_eqVlt => /predU1P[<-//|kn].
  by rewrite ltW// decrF ?in_itv/= ?andbT ?lerDl//= ltrD2l ltr_nat.
Qed.

Lemma increasing_itvNyo_bigcup F a :
  {in `]-oo, a] &, {homo F : x y / x < y}} ->
  F x @[x --> -oo] --> -oo ->
 (`]-oo, F a] = \bigcup_i `]F (a - i.+1%:R), F a])%classic.
Proof.
move=> dF nyF; rewrite itvNy_bnd_bigcup_BLeft eqEsubset; split.
- move=> y/= [n _]/=; rewrite in_itv/= => /andP[Fany yFa].
  have [i iFan] : exists i, F (a - i.+1%:R) < F a - n%:R.
    move/cvgrNy_lt : nyF => /(_ (F a - n%:R))[z [zreal zFan]].
    exists `|ceil (a - z)|%N.
    rewrite zFan// ltrBlDr -ltrBlDl.
    rewrite (le_lt_trans (Num.Theory.le_ceil _)) ?num_real//.
    by rewrite (le_lt_trans (ler_norm _))// -natr1 -intr_norm ltrDl.
  by exists i => //=; rewrite in_itv/= yFa andbT (lt_le_trans _ Fany).
- move=> z/= [n _ /=]; rewrite in_itv/= => /andP[Fanz zFa].
  exists `|ceil (F (a - n.+1%:R) - F a)|.+1 => //=.
  rewrite in_itv/= zFa andbT lerBlDr -lerBlDl (le_trans _ (abs_ceil_ge _))//.
  by rewrite ler_normr orbC opprB lerB// ltW.
Qed.

Lemma increasing_itvoc_bigcup F a n :
  {in `]-oo, a] &, {homo F : x y / x < y}} ->
  (`]F (a - n%:R), F a] = \bigcup_(i < n) `]F (a - i.+1%:R), F a])%classic.
Proof.
move=> incrF; rewrite eqEsubset; split.
- move: n => [|n]; first by rewrite subr0 set_itvoc0.
  by apply: (@bigcup_sup _ _ n) => /=.
- apply: bigcup_sub => k/= kn; apply: subset_itvr; rewrite bnd_simp.
  move: kn; rewrite leq_eqVlt => /predU1P[<-//|kn].
  by rewrite ltW// incrF ?in_itv/= ?andbT ?gerBl ?ler_ltB ?ltr_nat.
Qed.

End monotonic_itv_bigcup.

Section open_closed_sets.
(* TODO: duplicate theory within the subspace topology of Num.real
         in a numDomainType *)
Context {R : realFieldType}.
Implicit Types x y : R.

Lemma open_lt y : open [set x | x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0. exists (y - x) => // z.
by rewrite /= ltr_distlC addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt y : open [set x | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= ltr_distlC subKr => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq y : open [set x | x != y].
Proof.
rewrite (_ : mkset _ = [set x | x < y] `|` [set x | x > y]); first exact: openU.
rewrite predeqE => x /=.
by rewrite eq_le negb_and -!ltNge orbC; symmetry; apply (rwP orP).
Qed.

Lemma interval_open a b : ~~ bound_side true a -> ~~ bound_side false b ->
  open [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _.
- have -> : [set x | a < x < b] = [set x | a < x] `&` [set x | x < b].
    by rewrite predeqE => r; rewrite /mkset; split => [/andP[? ?] //|[-> ->]].
  by apply openI; [exact: open_gt | exact: open_lt].
- by under eq_set do rewrite itv_ge// inE.
- by under eq_set do rewrite in_itv andbT/=; exact: open_gt.
- exact: open_lt.
- by rewrite (_ : mkset _ = setT); [exact: openT | rewrite predeqE].
Qed.

(* TODO: we can probably extend these results to numFieldType
   by adding a precondition that y \is Num.real *)
Lemma closed_le y : closed [set x | x <= y].
Proof.
rewrite (_ : mkset _ = ~` [set x | x > y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_ge y : closed [set x | y <= x].
Proof.
rewrite (_ : mkset _ = ~` [set x | x < y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_eq y : closed [set x | x = y].
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: open_closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _;
  do ?by under eq_set do rewrite itv_ge// inE falseE; apply: closed0.
- have -> : `[a, b]%classic = [set x | x >= a] `&` [set x | x <= b].
    by rewrite predeqE => ?; rewrite /= in_itv/=; split=> [/andP[]|[->]].
  by apply closedI; [exact: closed_ge | exact: closed_le].
- by under eq_set do rewrite in_itv andbT/=; exact: closed_ge.
- exact: closed_le.
Qed.

End open_closed_sets.
#[global] Hint Extern 0 (open _) => now apply: open_gt : core.
#[global] Hint Extern 0 (open _) => now apply: open_lt : core.
#[global] Hint Extern 0 (open _) => now apply: open_neq : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_ge : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_le : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_eq : core.
#[global] Hint Extern 0 (open _) => now apply: interval_open : core.

Section near_in_itv.
Context {R : realFieldType} (a b : R).

Lemma near_in_itvoo :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof. exact: interval_open. Qed.

Lemma near_in_itvoy :
  {in `]a, +oo[, forall y, \forall z \near y, z \in `]a, +oo[}.
Proof. exact: interval_open. Qed.

Lemma near_in_itvNyo :
  {in `]-oo, b[, forall y, \forall z \near y, z \in `]-oo, b[}.
Proof. exact: interval_open. Qed.

End near_in_itv.
#[deprecated(since="mathcomp-analysis 1.7.0",
  note="use `near_in_itvoo` instead")]
Notation near_in_itv := near_in_itvoo (only parsing).

Lemma near_infty_natSinv_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Proof.
near=> n; rewrite -(@ltr_pM2r _ n.+1%:R) // mulVr ?unitfE //.
rewrite -(@ltr_pM2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // ltr_nat.
by near: n; exists (Num.bound e%:num^-1).
Unshelve. all: by end_near. Qed.

Lemma near_infty_natSinv_expn_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, 1 / 2 ^+ n < e%:num.
Proof.
near=> n.
rewrite -(@ltr_pM2r _ (2 ^+ n)) // -?natrX ?ltr0n ?expn_gt0//.
rewrite mul1r mulVr ?unitfE ?gt_eqF// ?ltr0n ?expn_gt0//.
rewrite -(@ltr_pM2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // natrX upper_nthrootP //.
near: n; eexists; last by move=> m; exact.
by [].
Unshelve. all: by end_near. Qed.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x <= z <= y -> E z.

Lemma is_intervalPlt (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x < z < y -> E z.
Proof.
split=> iE x y Ex Ey z /andP[].
  by move=> xz zy; apply: (iE x y); rewrite ?ltW.
rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy].
by apply: (iE x y); rewrite ?xz.
Qed.

Lemma interval_is_interval (i : interval R) : is_interval [set` i].
Proof.
by case: i => -[[]a|[]] [[]b|[]] // x y /=; do ?[by rewrite ?itv_ge//];
  move=> xi yi z; rewrite -[x <= z <= y]/(z \in `[x, y]); apply/subitvP;
  rewrite subitvE /Order.le/= ?(itvP xi, itvP yi).
Qed.

End interval.

Lemma interval_unbounded_setT {R : realFieldType} (X : set R) : is_interval X ->
  ~ has_lbound X -> ~ has_ubound X -> X = setT.
Proof.
move=> iX lX uX; rewrite predeqE => x; split => // _.
move/has_lbPn : lX => /(_ x) [y Xy xy].
move/has_ubPn : uX => /(_ x) [z Xz xz].
by apply: (iX y z); rewrite ?ltW.
Qed.

Section open_union_rat.
Variable R : realType.
Implicit Types A U : set R.

Let ointsub A U := [/\ open A, is_interval A & A `<=` U].

Let ointsub_rat U q := [set A | ointsub A U /\ A (ratr q)].

Let ointsub_rat0 q : ointsub_rat set0 q = set0.
Proof. by apply/seteqP; split => // A [[_ _]]; rewrite subset0 => ->. Qed.

Definition bigcup_ointsub U q := \bigcup_(A in ointsub_rat U q) A.

Lemma bigcup_ointsub0 q : bigcup_ointsub set0 q = set0.
Proof. by rewrite /bigcup_ointsub ointsub_rat0 bigcup_set0. Qed.

Lemma open_bigcup_ointsub U q : open (bigcup_ointsub U q).
Proof. by apply: bigcup_open => i [[]]. Qed.

Lemma is_interval_bigcup_ointsub U q : is_interval (bigcup_ointsub U q).
Proof.
move=> /= a b [A [[oA iA AU] Aq] Aa] [B [[oB iB BU] Bq] Bb] c /andP[ac cb].
have [cq|cq|->] := ltgtP c (ratr q); last by exists A.
- by exists A => //; apply: (iA a (ratr q)) => //; rewrite ac (ltW cq).
- by exists B => //; apply: (iB (ratr q) b) => //; rewrite cb (ltW cq).
Qed.

Lemma bigcup_ointsub_sub U q : bigcup_ointsub U q `<=` U.
Proof. by move=> y [A [[oA _ +] _ Ay]]; exact. Qed.

Lemma open_bigcup_rat U : open U ->
  U = \bigcup_(q in [set q | ratr q \in U]) bigcup_ointsub U q.
Proof.
move=> oU; have [->|U0] := eqVneq U set0.
  by rewrite bigcup0// => q _; rewrite bigcup_ointsub0.
apply/seteqP; split=> [x Ux|x [p _ Ipx]]; last exact: bigcup_ointsub_sub Ipx.
suff [q Iqx] : exists q, bigcup_ointsub U q x.
  by exists q => //=; rewrite in_setE; case: Iqx => A [[_ _ +] ? _]; exact.
have : nbhs x U by rewrite nbhsE /=; exists U.
rewrite -nbhs_ballE /nbhs_ball /nbhs_ball_ => -[_/posnumP[r] xrU].
have /rat_in_itvoo[q qxxr] : (x - r%:num < x + r%:num)%R.
  by rewrite ltrBlDr -addrA ltrDl.
exists q, `](x - r%:num)%R, (x + r%:num)%R[%classic; last first.
  by rewrite /= in_itv/= ltrBlDl ltrDr// ltrDl//; apply/andP.
split=> //; split; [exact: interval_open|exact: interval_is_interval|].
move=> y /=; rewrite in_itv/= => /andP[xy yxr]; apply xrU => /=.
rewrite /ball /= /ball_ /= in xrU *; have [yx|yx] := leP x y.
  by rewrite ler0_norm ?subr_le0// opprB ltrBlDl.
by rewrite gtr0_norm ?subr_gt0// ltrBlDr -ltrBlDl.
Qed.

End open_union_rat.

Section ball_realFieldType.
Variables (R : realFieldType).

Lemma ball0 (a r : R) : ball a r = set0 <-> r <= 0.
Proof.
split.
  move=> /seteqP[+ _] => H; rewrite leNgt; apply/negP => r0.
  by have /(_ (ballxx _ r0)) := H a.
move=> r0; apply/seteqP; split => // y; rewrite /ball/=.
by move/lt_le_trans => /(_ _ r0); rewrite normr_lt0.
Qed.

End ball_realFieldType.

Section interval_realType.
Variable R : realType.

Lemma interval_left_unbounded_interior (X : set R) : is_interval X ->
  ~ has_lbound X -> has_ubound X -> X° = [set r | r < sup X].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: right_bounded_interior.
rewrite -(open_subsetE _ (@open_lt _ _)) => r rsupX.
move/has_lbPn : lX => /(_ r)[y Xy yr].
have hsX : has_sup X by split => //; exists y.
have /sup_adherent/(_ hsX)[e Xe] : 0 < sup X - r by rewrite subr_gt0.
by rewrite subKr => re; apply: (iX y e); rewrite ?ltW.
Qed.

Lemma interval_right_unbounded_interior (X : set R) : is_interval X ->
  has_lbound X -> ~ has_ubound X -> X° = [set r | inf X < r].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: left_bounded_interior.
rewrite -(open_subsetE _ (@open_gt _ _)) => r infXr.
move/has_ubPn : uX => /(_ r)[y Xy yr].
have hiX : has_inf X by split => //; exists y.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
by rewrite addrC subrK => er; apply: (iX e y); rewrite ?ltW.
Qed.

Lemma interval_bounded_interior (X : set R) : is_interval X ->
  has_lbound X -> has_ubound X -> X° = [set r | inf X < r < sup X].
Proof.
move=> iX bX aX; rewrite eqEsubset; split=> [r Xr|].
  apply/andP; split;
    [exact: left_bounded_interior|exact: right_bounded_interior].
rewrite -open_subsetE; last exact: (@interval_open _ (BRight _) (BLeft _)).
move=> r /andP[iXr rsX].
have [X0|/set0P X0] := eqVneq X set0.
  by move: (lt_trans iXr rsX); rewrite X0 inf_out ?sup_out ?ltxx // => - [[]].
have hiX : has_inf X by split.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
rewrite addrC subrK => er.
have hsX : has_sup X by split.
have /sup_adherent/(_ hsX)[f Xf] : 0 < sup X - r by rewrite subr_gt0.
by rewrite subKr => rf; apply: (iX e f); rewrite ?ltW.
Qed.

Lemma interior_set1 (a : R) : [set a]° = set0.
Proof.
rewrite interval_bounded_interior; first last.
- by exists a => [?]/= ->; apply: lexx.
- by exists a => [?]/= ->; apply: lexx.
- by move=> ? ?/= -> -> r; rewrite -eq_le; move/eqP <-.
- rewrite inf1 sup1 eqEsubset; split => // => x/=.
  by rewrite ltNge => /andP[/negP + ?]; apply; apply/ltW.
Qed.

Lemma interior_itv_bnd (x y : R) (a b : bool) :
  [set` Interval (BSide a x) (BSide b y)]° = `]x, y[%classic.
Proof.
have [|xy] := leP y x.
  rewrite le_eqVlt => /predU1P[-> |yx].
    by case: a; case: b; rewrite set_itvoo0 ?set_itvE ?interior_set1 ?interior0.
  rewrite !set_itv_ge ?interior0//.
  - by rewrite bnd_simp -leNgt ltW.
  - by case: a; case: b; rewrite bnd_simp -?leNgt -?ltNge ?ltW.
rewrite interval_bounded_interior//; last exact: interval_is_interval.
rewrite inf_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
rewrite sup_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
exact: set_itvoo.
Qed.

Lemma interior_itv_bndy (x : R) (b : bool) :
  [set` Interval (BSide b x) (BInfty _ false)]° = `]x, +oo[%classic.
Proof.
rewrite interval_right_unbounded_interior//.
- rewrite inf_itv; last by case: b; rewrite bnd_simp ?ltW.
  by rewrite set_itvoy.
- exact: interval_is_interval.
- by apply: hasNubound_itv; rewrite lt_eqF.
Qed.

Lemma interior_itv_Nybnd (y : R) (b : bool) :
  [set` Interval (BInfty _ true) (BSide b y)]° = `]-oo, y[%classic.
Proof.
rewrite interval_left_unbounded_interior//.
- rewrite sup_itv; last by case b; rewrite bnd_simp ?ltW.
  exact: set_itvNyo.
- exact: interval_is_interval.
- by apply: hasNlbound_itv; rewrite gt_eqF.
Qed.

Lemma interior_itv_Nyy :
  [set` Interval (BInfty R true) (BInfty _ false)]° = `]-oo, +oo[%classic.
Proof. by rewrite set_itvNyy; exact: interiorT. Qed.

Definition interior_itv :=
  (interior_itv_bnd, interior_itv_bndy, interior_itv_Nybnd, interior_itv_Nyy).

End interval_realType.
