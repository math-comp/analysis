(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences measure.
Require Import cardinality.

(******************************************************************************)
(*        summation of non-negative extended reals over countable sets        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma ereal_sup_adherent2 (R : realType) (T : choiceType) (a : T -> {ereal R})
  (J : nat -> set T) (L : {fset nat}%fset) (L0 : L != fset0) (e : {posnum R})
  (l := #|` L| : nat) (j : 'I_l) c :
  ereal_sup [set y | exists2 F : {fset T}%fset,
   (fun i : T => i \in F) `<=` J (nth 0%N L j) &
   (\sum_(i <- F) a i = y)%E] = c%:E ->
  exists Fj : {fset T},
    ([set x | x \in Fj] `<=` J (nth 0%N L j)) /\
    (c%:E - (e%:num / l%:R)%:E < \sum_(s <- Fj) a s)%E.
Proof.
set S : set {ereal R} := (X in ereal_sup X) => Sc [:f'].
have @f : {posnum R}.
  exists (e%:num / l%:R); abstract: f'.
  by rewrite divr_gt0 // /l ltr0n cardfs_gt0.
have jL : nth 0%N L j \in L by rewrite mem_nth.
have : ~ ubound S (ereal_sup S - (e%:num / l%:R) %:E)%E.
  move/ub_ereal_sup; apply/negP.
  by rewrite -ltNge Sc lte_subl_addr lte_fin ltr_addl.
move/asboolP; rewrite asbool_neg; case/existsp_asboolPn => /= x.
rewrite not_implyE => -[[A AJj <-{x}] AS].
by exists A; split => //; rewrite ltNge; apply/negP; rewrite subERFin -Sc.
Qed.

(* TODO: PR to normedtype.v *)
Lemma ereal_nbhs_pinfty_ge (R : numFieldType) (c : {posnum R}) :
  (\forall x \near +oo, (c%:num%:E <= x))%E.
Proof. by exists c%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

Lemma ereal_nbhs_ninfty_le (R : numFieldType) (c : R) : c < 0 ->
  (\forall x \near -oo, (x <= c%:E))%E.
Proof. by exists c; rewrite realE (ltW H) orbT; split => // x /ltW. Qed.

Lemma closed_ereal_le_ereal (R : realFieldType) (y : {ereal R}) :
  closed (fun x => y <= x)%E.
Proof.
rewrite (_ : [set x | y <= x]%E = ~` [set x | y > x]%E); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal (R : realFieldType) (y : {ereal R}) :
  closed (fun x => y >= x)%E.
Proof.
rewrite (_ : [set x | y >= x]%E = ~` [set x | y < x]%E); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_gt_ereal.
Qed.

Lemma oppe_continuous (R : realFieldType) : continuous (@oppe R).
Proof.
move=> x S /= xS; apply nbhsNKe; rewrite image_preimage //.
by rewrite predeqE => y; split => // _; exists (- y)%E => //; rewrite oppeK.
Qed.

(* TODO: PR to sequences.v *)
Lemma ereal_cvg_ge0 (R : realFieldType) (f : {ereal R} ^nat) (a : {ereal R}) :
  (forall n, 0%:E <= f n)%E -> f --> a -> (0%:E <= a)%E.
Proof.
move=> f0 /closed_cvg_loc V; elim/V : _; last exact: closed_ereal_le_ereal.
by exists O => // ? _; exact: f0.
Qed.

Lemma ereal_lim_ge (R : realFieldType) x (u_ : {ereal R} ^nat) : cvg u_ ->
  (\forall n \near \oo, (x <= u_ n)%E) -> (x <= lim u_)%E.
Proof.
move=> /closed_cvg_loc V xu_; elim/V: _; last exact: closed_ereal_le_ereal.
case: xu_ => m _ xu_.
near \oo => n.
have mn : (n >= m)%N by near: n; exists m.
by exists n => // k nk /=; exact: (xu_ _ (leq_trans mn nk)).
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_lim_le (R : realFieldType) x (u_ : {ereal R} ^nat) : cvg u_ ->
  (\forall n \near \oo, (u_ n <= x)%E) -> (lim u_ <= x)%E.
Proof.
move=> /closed_cvg_loc V xu_; elim/V: _; last exact: closed_ereal_ge_ereal.
case: xu_ => m _ xu_.
near \oo => n.
have mn : (n >= m)%N by near: n; exists m.
by exists n => // k nk /=; exact: (xu_ _ (leq_trans mn nk)).
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgN (R : realFieldType) (f : {ereal R} ^nat) (a : {ereal R}) :
  f --> a -> (fun n => - (f n))%E --> (- a)%E.
Proof.
rewrite (_ : (fun n => - (f n))%E = -%E \o f) // => /cvg_comp; apply.
exact: oppe_continuous.
Qed.

Lemma is_cvg_ereal_nneg_series (R : realType) (u_ : {ereal R} ^nat) :
  (forall n, (0%:E <= u_ n)%E) ->
  cvg (fun n : nat => (\sum_(i < n) u_ i)%E).
Proof.
move/lee_sum_nneg_ord/nondecreasing_seq_ereal_cvg => cu.
by apply/cvg_ex; eexists; exact: cu.
Qed.

Lemma ereal_nneg_series_pinfty (R : realType) (u_ : {ereal R} ^nat) k :
  (forall n, (0%:E <= u_ n)%E) -> u_ k = +oo%E ->
  (lim (fun n : nat => \sum_(i < n) u_ i) = +oo)%E.
Proof.
move=> u0 ukoo; apply/eqP; rewrite eq_le lee_pinfty /=.
rewrite (le_trans _ (ereal_nneg_series_lim_ge k.+1 u0)) // big_ord_recr /= ukoo /=.
suff : (\sum_(i < k) u_ i != -oo)%E by case: (\sum_(i < k) _)%E.
rewrite esum_ninfty negb_exists; apply/forallP => i; apply/negP => /eqP ioo.
by move: (u0 i); rewrite ioo; apply/negP.
Qed.

Lemma ereal_cvg_real (R : realFieldType) (f : {ereal R} ^nat) a :
  {near \oo, forall x, is_real (f x)} /\
  (real_of_er \o f --> (a : R^o)) <-> f --> a%:E.
Proof.
split=> [[[N _ foo] fa]|fa].
  rewrite -(cvg_shiftn N).
  have {fa} : [sequence (real_of_er (f (n + N)%N))]_n --> a.
    by rewrite (@cvg_shiftn _ _ (real_of_er \o f : _ -> R^o)).
  move/(@cvg_app _ _ _ _ (@ERFin R)).
  apply: cvg_trans; apply: near_eq_cvg; near=> n => /=.
  by rewrite -ERFin_real_of_er //; apply foo; rewrite leq_addl.
split; last first.
  move/(@cvg_app _ _ _ _ real_of_er) : fa.
  by apply: cvg_trans; exact: cvg_id.
move/cvg_ballP : fa.
have e0 : 0 < minr (1 + contract a%:E) (1 - contract a%:E).
  by rewrite lt_minr -ltr_subl_addl add0r subr_gt0 -ltr_norml contract_lt1.
move/(_ _ e0); rewrite near_map => -[N _ fa]; near=> n.
have /fa : (N <= n)%N by near: n; exists N.
rewrite /ball /= /ereal_ball; case: (f n) => //.
- rewrite ltr0_norm; last first.
    by rewrite -opprB ltr_oppl oppr0; move: e0; rewrite lt_minr => -/andP[].
  by rewrite opprB lt_minr ltxx andbF.
- rewrite opprK gtr0_norm; last first.
    by rewrite addrC; move: e0; rewrite lt_minr => -/andP[].
  by rewrite lt_minr addrC ltxx.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgPpinfty (R : realFieldType) (u_ : {ereal R} ^nat) :
  u_ --> +oo%E <-> (forall A : R, 0 < A -> \forall n \near \oo, (A%:E <= u_ n)%E).
Proof.
split => [u_cvg _/posnumP[A]|u_ge X [A [Ar AX]]].
  rewrite -(near_map u_ \oo (fun x => (A%:num%:E <= x))%E).
  by apply: u_cvg; apply: ereal_nbhs_pinfty_ge.
rewrite !near_simpl [\near u_, X _](near_map u_ \oo); near=> x.
apply: AX.
rewrite (@lt_le_trans _ _ ((maxr 0 A) +1)%:E) //.
  by rewrite addERFin lte_spaddr // ?lte_fin// lee_fin le_maxr lexx orbT.
by near: x; apply: u_ge; rewrite ltr_spaddr // le_maxr lexx.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgPninfty (R : realFieldType) (u_ : {ereal R} ^nat) :
  u_ --> -oo%E <-> (forall A : R, A < 0 -> \forall n \near \oo, (u_ n <= A%:E)%E).
Proof.
split => [u_cvg A A0|u_le X [A [Ar AX]]].
  rewrite -(near_map u_ \oo (fun x => (x <= A%:E))%E).
  by apply: u_cvg; apply: ereal_nbhs_ninfty_le.
rewrite !near_simpl [\near u_, X _](near_map u_ \oo); near=> x.
apply: AX.
rewrite (@le_lt_trans _ _ ((minr 0 A) -1)%:E) //.
  by near: x; apply: u_le; rewrite ltr_subl_addl addr0 lt_minl ltr01.
by rewrite lte_fin ltr_subl_addl lt_minl ltr_addr ltr01 orbT.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_pinfty_fin (R : realType) (f g : {ereal R} ^nat) b :
  f --> +oo%E -> g --> b%:E -> (f \+ g)%E --> +oo%E.
Proof.
move=> /ereal_cvgPpinfty foo /ereal_cvg_real -[realg gb].
apply/ereal_cvgPpinfty => A A0.
have : cvg (real_of_er \o g : _ -> R^o) by apply/cvg_ex; exists b.
move/cvg_has_inf => -[gT0 [M gtM]].
have : 0 < maxr A (A - M)%R by rewrite lt_maxr A0.
move/foo => [m _ {}foo].
case: realg => k _ realg.
near=> n.
have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn].
move/realg => /ERFin_real_of_er ->.
rewrite -lee_subl_addr -subERFin.
apply: le_trans; last exact: foo.
rewrite lee_fin le_maxr; apply/orP; right.
by apply ler_sub => //; apply gtM; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_ninfty_fin (R : realType) (f g : {ereal R} ^nat) b :
  f --> -oo%E -> g --> b%:E -> (f \+ g)%E --> -oo%E.
Proof.
move=> /ereal_cvgPninfty foo /ereal_cvg_real -[realg gb].
apply/ereal_cvgPninfty => A A0.
have : cvg (real_of_er \o g : _ -> R^o) by apply/cvg_ex; exists b.
move/cvg_has_sup => -[gT0 [M gtM]].
have : minr A (A - M)%R < 0 by rewrite lt_minl A0.
move/foo => [m _ {}foo].
case: realg => k _ realg.
near=> n.
have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn].
move/realg => /ERFin_real_of_er ->.
rewrite -lee_subr_addr -subERFin.
apply: le_trans; first exact: foo.
rewrite lee_fin le_minl; apply/orP; right.
by apply ler_sub => //; apply gtM; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_pinfty_pinfty (R : realFieldType) (f g : {ereal R} ^nat) :
  f --> +oo%E -> g --> +oo%E -> (f \+ g)%E --> +oo%E.
Proof.
move=> /ereal_cvgPpinfty foo /ereal_cvgPpinfty goo.
apply/ereal_cvgPpinfty => A A0.
have A20 : 0 < A / 2 by rewrite divr_gt0.
case: (foo _ A20) => m _ {}foo.
case: (goo _ A20) => k _ {}goo.
near=> n; have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn kn].
by rewrite (splitr A) addERFin lee_add // ?foo // goo.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_ninfty_ninfty (R : realFieldType) (f g : {ereal R} ^nat) :
  f --> -oo%E -> g --> -oo%E -> (f \+ g)%E --> -oo%E.
Proof.
move=> /ereal_cvgPninfty foo /ereal_cvgPninfty goo.
apply/ereal_cvgPninfty => A A0.
have A20 : A / 2 < 0 by rewrite ltr_pdivr_mulr // mul0r.
case: (foo _ A20) => m _ {}foo.
case: (goo _ A20) => k _ {}goo.
near=> n; have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn kn].
by rewrite (splitr A) addERFin lee_add // ?foo // goo.
Grab Existential Variables. all: end_near. Qed.

Lemma lee_lim (R : realType) (u_ v_ : {ereal R} ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, (u_ n <= v_ n)%E) -> (lim u_ <= lim v_)%E.
Proof.
move=> cu cv uv; move lu : (lim u_) => l; move kv : (lim v_) => k.
case: l k => [l| |] [k| |] // in lu kv *.
- have : u_ --> l%:E.
    move/cvg_ex : cu => -[l' ul'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (ul'); rewrite lu => ->.
  move/ereal_cvg_real => [realu ul].
  have : v_ --> k%:E.
    move/cvg_ex : cv => -[k' vk'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (vk'); rewrite kv => ->.
  move/ereal_cvg_real => [realv vk].
  move/(@cvg_lim [topologicalType of R^o] (@Rhausdorff R)) : (ul) => <-.
  move/(@cvg_lim [topologicalType of R^o] (@Rhausdorff R)) : (vk) => <-.
  apply: ler_lim.
  by apply/cvg_ex; eexists; exact: ul.
  by apply/cvg_ex; eexists; exact: vk.
  case: uv => n1 _ uv.
  case: realu => n2 _ realu.
  case: realv => n3 _ realv.
  near=> n.
  have n123 : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite !geq_max in n123; case/and3P : n123 => n1n n2n n3n.
  rewrite -lee_fin -(ERFin_real_of_er (realu _ n2n)).
  by rewrite -(ERFin_real_of_er (realv _ n3n)) uv.
- by rewrite lee_pinfty.
- exfalso.
  have : u_ --> l%:E.
    move/cvg_ex : cu => -[l' ul'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (ul'); rewrite lu => ->.
  move/ereal_cvg_real => [realu ul].
  have : v_ --> -oo%E.
    move/cvg_ex : cv => -[k' vk'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (vk'); rewrite kv => ->.
  move/ereal_cvgPninfty => voo.
  have : cvg (real_of_er \o u_ : _ -> R^o) by apply/cvg_ex; exists l.
  move/cvg_has_inf => -[uT0 [M uTM]].
  have : minr (M - 1) (-1) < 0 by rewrite lt_minl ltrN10 orbT.
  move/voo => {voo} [n1 _ vM].
  case: uv => n2 _ uv.
  case: realu => n3 _ realu.
  near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  move/vM : (n1n) => {}vM.
  have : (v_ n < u_ n)%E.
    apply (le_lt_trans vM).
    apply (@lt_le_trans _ _ M%:E).
      by rewrite lte_fin lt_minl ltr_subl_addl ltr_addr ltr01.
    by rewrite (ERFin_real_of_er (realu _ n3n)) lee_fin; apply uTM; exists n.
  by apply/negP; rewrite -leNgt uv.
- exfalso.
  have : v_ --> k%:E.
    move/cvg_ex : cv => -[k' vk'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (vk'); rewrite kv => ->.
  move/ereal_cvg_real => [realv vk].
  have : u_ --> +oo%E.
    move/cvg_ex : cu => -[l' ul'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (ul'); rewrite lu => ->.
  move/ereal_cvgPpinfty => uoo.
  have : cvg (real_of_er \o v_ : _ -> R^o) by apply/cvg_ex; exists k.
  move/cvg_has_sup => -[vT0 [M vTM]].
  have : 0 < maxr (M + 1) 1 by rewrite lt_maxr ltr01 orbT.
  move/uoo => {uoo} [n1 _ uM].
  case: uv => n2 _ uv.
  case: realv => n3 _ realv.
  near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  move/uM : (n1n) => {}uM.
  have : (v_ n < u_ n)%E.
    apply (@le_lt_trans _ _ M%:E).
      by rewrite (ERFin_real_of_er (realv _ n3n)) lee_fin; apply vTM; exists n.
    apply: (lt_le_trans _ uM).
    by rewrite lte_fin lt_maxr ltr_addl ltr01.
  by apply/negP; rewrite -leNgt uv.
- exfalso.
  have : u_ --> +oo%E.
    move/cvg_ex : cu => -[l' ul'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (ul'); rewrite lu => ->.
  move/ereal_cvgPpinfty => uoo.
  have : v_ --> -oo%E.
    move/cvg_ex : cv => -[k' vk'].
    by move/(cvg_lim (@ereal_hausdorff R)) : (vk'); rewrite kv => ->.
  move/ereal_cvgPninfty => voo.
  case: uv => n1 _ uv.
  have [n2 _ {}uoo] := uoo _ ltr01.
  have [n3 _ {}voo] := voo _ (@ltrN10 R).
  near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  have : (v_ n < u_ n)%E.
    apply: (@lt_trans _ _ 0%:E).
      apply: (le_lt_trans (voo _ n3n)).
      by rewrite lte_fin ltrN10.
    apply: (lt_le_trans _ (uoo _ n2n)).
    by rewrite lte_fin ltr01.
  by apply/negP; rewrite -leNgt; apply uv.
- by rewrite lee_ninfty.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD (R : realType) (f g : {ereal R} ^nat) a b :
  ~~ adde_undef a b ->
  f --> a -> g --> b -> (f \+ g)%E --> (a + b)%E.
Proof.
move: a b => [a| |] [b| |] // _.
- case/ereal_cvg_real => [[na _ foo] fa].
  case/ereal_cvg_real => [[nb _ goo] gb].
  apply/ereal_cvg_real; split.
    exists (maxn na nb) => // n; rewrite geq_max => /andP[nan nbn].
    by rewrite /= is_realD; apply/andP; split; [exact: foo | exact: goo].
  rewrite -(@cvg_shiftn (maxn na nb) [topologicalType of R^o]).
  rewrite (_ : (fun n => _) = (fun n => real_of_er (f (n + maxn na nb)%N)
      + real_of_er (g (n + maxn na nb)%N))); last first.
    rewrite funeqE => n /=.
    have /ERFin_real_of_er -> : is_real (f (n + maxn na nb)%N).
      by apply/foo; apply (leq_trans (leq_maxl _ _) (leq_addl _ _)).
    suff /ERFin_real_of_er -> : is_real (g (n + maxn na nb)%N) by [].
    by apply/goo; apply (leq_trans (leq_maxr _ _) (leq_addl _ _)).
  apply: (@cvgD _ [normedModType R of R^o]).
    by rewrite (@cvg_shiftn _ [topologicalType of R^o] (real_of_er \o f)).
  by rewrite (@cvg_shiftn _ [topologicalType of R^o] (real_of_er \o g)).
- move=> fa goo.
  rewrite (_ : (_ \+ _)%E = (g \+ f)%E); last by rewrite funeqE => i; rewrite addeC.
  exact: (ereal_cvgD_pinfty_fin _ fa).
- move=> fa goo.
  rewrite (_ : (_ \+ _)%E = (g \+ f)%E); last by rewrite funeqE => i; rewrite addeC.
  exact: (ereal_cvgD_ninfty_fin _ fa).
- exact: ereal_cvgD_pinfty_fin.
- exact: ereal_cvgD_pinfty_pinfty.
- exact: ereal_cvgD_ninfty_fin.
- exact: ereal_cvgD_ninfty_ninfty.
Qed.

Lemma ereal_limD (R : realType) (f g : nat -> {ereal R}) :
  cvg f -> cvg g -> ~~ adde_undef (lim f) (lim g) ->
  (lim (f \+ g) = lim f + lim g)%E.
Proof. by move=> cf cg fg; apply/cvg_lim => //; apply ereal_cvgD. Qed.
(* end TODO: PR *)

Section FsetPartitions.

Variables T I : choiceType.
Implicit Types (x y z : T) (A B D X : {fset T}) (P Q : {fset {fset T}}).
Implicit Types (J : pred I) (F : I -> {fset T}).

Definition cover P := (\bigcup_(B <- P) B)%fset.
Definition trivIset P := (\sum_(B <- P) #|` B|)%N == #|` cover P|.

Lemma leq_card_fsetU A B :
  ((#|` A `|` B|)%fset <= #|` A| + #|` B| ?= iff [disjoint A & B]%fset)%N.
Proof.
rewrite -(addn0 #|`_|) -fsetI_eq0 -cardfs_eq0 -cardfsUI eq_sym.
by rewrite (mono_leqif (leq_add2l _)).
Qed.

Lemma leq_card_cover P :
  ((#|` cover P|)%fset <= \sum_(A <- P) #|`A| ?= iff trivIset P)%N.
Proof.
split; last exact: eq_sym.
rewrite /cover; elim/big_rec2: _ => [|A n U _ leUn]; first by rewrite cardfs0.
by rewrite (leq_trans (leq_card_fsetU A U).1) ?leq_add2l.
Qed.

Lemma trivIsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]%fset} (trivIset P).
Proof.
have [l Pl ul] : {l | enum_fset P =i l & uniq l} by exists (enum_fset P).
elim: l P Pl ul => [P P0 _|A e ih P PAe] /=.
  rewrite /trivIset /cover.
  have -> : P = fset0 by apply/fsetP => i; rewrite P0 !inE.
  rewrite !big_seq_fset0 cardfs0 eqxx.
  by left => x y; rewrite in_fset0.
have {PAe} -> : P = [fset x | x in A :: e]%fset.
  by apply/fsetP => i; rewrite !inE /= PAe inE.
move=> {P} /andP[]; rewrite fset_cons => Ae ue.
set E := [fset x | x in e]%fset; have Ee : E =i e by move=> x; rewrite !inE.
rewrite -Ee in Ae; move: (ih _ Ee ue) => {}ih.
rewrite /trivIset /cover !big_setU1 // eq_sym.
have := leq_card_cover E; rewrite -(mono_leqif (leq_add2l #|` A|)).
move/(leqif_trans (leq_card_fsetU _ _)) => /= ->.
have [dAcE|dAcE]/= := boolP [disjoint A & cover E]%fset; last first.
  right=> tI; move/negP : dAcE; apply.
  rewrite -fsetI_eq0; apply/eqP/fsetP => t; apply/idP/idP => //; apply/negP.
  rewrite inE => /andP[tA].
  rewrite /cover => /bigfcupP[/= B]; rewrite andbT => BE tB.
  have AB : A != B by apply: contra Ae => /eqP ->.
  move: (tI A B).
  rewrite 2!inE eqxx /= => /(_ isT); rewrite 2!inE BE orbT => /(_ isT AB).
  by move/disjoint_fsetI0 => /fsetP /(_ t); rewrite inE tA tB inE.
apply: (iffP ih) => [tI B C|tI B C PB PC]; last first.
  by apply: tI; rewrite !inE /= -Ee ?(PB,PC) orbT.
rewrite 2!inE => /orP[/eqP->{B}|BE].
  rewrite 2!inE => /orP[/eqP->|{tI}]; first by rewrite eqxx.
  move: dAcE; rewrite -fsetI_eq0 => /eqP AE0 CE AC.
  rewrite -fsetI_eq0; apply/eqP/fsetP => t; apply/idP/idP; apply/negP.
  rewrite inE => /andP[tA tC].
  move/fsetP : AE0 => /(_ t); rewrite !inE tA /= => /negbT/negP; apply.
  by apply/bigfcupP; exists C => //; rewrite CE.
rewrite 2!inE => /orP[/eqP-> BA|]; last exact: tI.
rewrite -fsetI_eq0; apply/eqP/fsetP => t; apply/idP/idP; apply/negP.
rewrite inE => /andP[tB tA]; move: dAcE.
rewrite -fsetI_eq0 => /eqP/fsetP/(_ t); rewrite !inE tA /= => /negP; apply.
by apply/bigfcupP; exists B => //; rewrite BE.
Qed.

Lemma cover_imfset (J : {fset I}) F (P : pred I) :
  cover [fset F i | i in J & P i]%fset = (\bigcup_(i <- J | P i) F i)%fset.
Proof.
apply/fsetP=> x; apply/bigfcupP/bigfcupP => [[/= t]|[i /andP[iJ Pi xFi]]].
  by rewrite andbT => /imfsetP[i /= Ji -> xFi]; exists i.
exists (F i) => //; rewrite andbT; apply/imfsetP; exists i => //=.
by rewrite inE Pi andbT.
Qed.

Section FsetBigOps.

Variables (R : realType) (idx : {ereal R}) (op : Monoid.com_law idx).
Let rhs_cond P K E :=
  (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A | K x) E x)%fset.
Let rhs P E := (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A) E x)%fset.

Lemma big_trivIset P (E : T -> {ereal R}) :
  trivIset P -> (\big[op/idx]_(x <- cover P) E x)%E = rhs P E.
Proof.
rewrite /rhs /cover => /trivIsetP tI.
have {tI} : {in enum_fset P &, forall A B, A != B -> [disjoint A & B]%fset}.
  by [].
elim: (enum_fset P) (fset_uniq P) => [_|h t ih /= /andP[ht ut] tP].
  by rewrite !big_nil.
rewrite !big_cons -ih //; last first.
  by move=> x y xt yt xy; apply tP => //; rewrite !inE ?(xt,yt) orbT.
rewrite {1}/fsetU big_imfset //= undup_cat /= big_cat !undup_id //.
congr (op _ _).
suff : [seq x <- h | x \notin (\bigcup_(j <- t) j)%fset] = h by move=>->.
rewrite -[RHS]filter_predT; apply eq_in_filter => x xh.
apply/negP/idP; apply/negP => /bigfcupP[/= A].
rewrite andbT => At xA.
have hA : h != A by move/negP : ht => /negP; apply: contra => /eqP ->.
move: (tP h A).
rewrite !inE eqxx => /(_ erefl);  rewrite At orbT => /(_ erefl hA).
by rewrite -fsetI_eq0 => /eqP /fsetP /(_ x); rewrite !inE xh xA.
Qed.

Lemma partition_disjoint_bigfcup (f : T -> {ereal R}) (F : I -> {fset T})
  (K : {fset I}) :
  (forall i j, i != j -> [disjoint F i & F j])%fset ->
  \big[op/idx]_(i <- \big[fsetU/fset0]_(x <- K) (F x)) f i =
  \big[op/idx]_(k <- K) (\big[op/idx]_(i <- F k) f i).
Proof.
move=> disjF; pose P := [fset F i | i in K & F i != fset0]%fset.
have trivP : trivIset P.
  apply/trivIsetP => _ _ /imfsetP[i _ ->] /imfsetP[j _ ->] neqFij.
  by apply: disjF; apply: contraNneq neqFij => ->.
have -> : (\bigcup_(i <- K) F i)%fset = cover P.
  apply/esym; rewrite /P cover_imfset big_mkcond /=; apply eq_bigr => i _.
  by case: ifPn => // /negPn/eqP.
rewrite big_trivIset // /rhs big_imfset => [|i j _ /andP[jK notFj0] eqFij] /=.
  rewrite big_filter big_mkcond; apply eq_bigr => i _.
  by case: ifPn => // /negPn /eqP ->;  rewrite big_seq_fset0.
by apply: contraNeq (disjF _ _) _; rewrite -fsetI_eq0 eqFij fsetIid.
Qed.

End FsetBigOps.

End FsetPartitions.

Definition csum (R : realFieldType) (T : choiceType) (S : set T)
    (a : T -> {ereal R}) :=
  if pselect (S !=set0) is left _ then
    ereal_sup [set (\sum_(i <- F) a i)%E |
               F in [set F : {fset T} | [set i | i \in F] `<=` S]]
  else 0%:E.

Lemma csum0 (R : realFieldType) (T : choiceType) (a : T -> {ereal R}) :
  csum set0 a = 0%:E.
Proof. by rewrite /csum; case: pselect => // -[]. Qed.

Lemma csum_ge0 (R : realType) (T : choiceType) (a : T -> {ereal R})
    (a0 : forall x, (0%:E <= a x)%E) (I : set T) :
  (0%:E <= csum I a)%E.
Proof.
rewrite /csum; case: pselect => // -[] i Ii.
by apply: ereal_sup_ub; exists fset0 => //; rewrite big_nil.
Qed.

Lemma csum_fset (R : realType) (T : choiceType) (S : {fset T})
    (f : T -> {ereal R}) : (forall i, 0%:E <= f i)%E ->
  csum [set x | x \in S] f = (\sum_(i <- S) f i)%E.
Proof.
move=> f0; rewrite /csum; case: pselect => [S0|]; last first.
  move/set0P/negP/negPn; rewrite eq_set0_fset0 => /eqP ->.
  by rewrite big_seq_fset0.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply ub_ereal_sup => /= x -[F FS <-{x}]; rewrite /set1 lee_sum_nneg_seq.
by apply ereal_sup_ub; exists S.
Qed.

Lemma csum_countable (R : realType) (T : pointedType) (S : set T)
  (a : T -> {ereal R}) (e : nat -> T) : (forall n, 0%:E <= a n)%E ->
  S #= @setT nat (* countably infinite *) ->
  enumeration S e ->
  injective e ->
  csum S a = lim (fun n => (\sum_(i < n) a (e i))%E).
Proof.
move=> a0 ST [Se SeT] ie; rewrite /csum; case: pselect => [S0|]; last first.
  move/set0P/negP/negPn/eqP => S0; move: SeT.
  by rewrite S0 => /esym/image_set0_set0; rewrite predeqE => /(_ 1%N) [] /(_ I).
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ereal_lim_le.
    by apply: (@is_cvg_ereal_nneg_series _ (a \o e)) => n; exact: a0.
  near=> N.
  have N0 : (0 < N)%nat by near: N; exists 1%N.
  have [N' NN'] : exists N', N = N'.+1 by exists N.-1; rewrite prednK.
  have -> : (\sum_(i < N) a (e i) =
      \sum_(i <- [fset i | i in 'I_N]%fset) a (e i))%E.
    by rewrite big_imfset //= big_enum.
  apply: ereal_sup_ub.
  exists (e @` [fset (nat_of_ord i) | i in 'I_N'.+1])%fset.
     move=> t /imfsetP[k /= /imfsetP[/= j _ ->{k} ->{t}]].
     by rewrite SeT; exists j.
  rewrite big_imfset /=; last first.
    by move=> x y /imfsetP[/= x' _ xx' /imfsetP[/= y' _ yy']]; exact: ie.
  rewrite big_imfset /=; last by move=> x y _ _; apply ord_inj.
  by rewrite big_imfset /= // NN'.
apply: ub_ereal_sup => x [/= F FS <-{x}].
have [/eqP ->|F0] := boolP (F == fset0).
  rewrite big_nil.
  apply: ereal_lim_ge.
    by apply: (@is_cvg_ereal_nneg_series _ (a \o e)) => /= n; apply: a0.
  by near=> n; apply: sume_ge0 => m; apply: a0.
have [N FNS] : exists N, (F `<=` [fset (e (nat_of_ord i)) | i in 'I_N])%fset.
  have [N H] : exists N, forall x, x \in F -> forall i, e i = x -> (i <= N)%N.
    have eF0 : e @^-1` (fun x => x \in F) !=set0.
      case/fset0Pn : F0 => t Ft; have [i [_ tei]] := Se _ (FS _ Ft).
      by exists i; rewrite /preimage -tei.
    have feF : set_finite (e @^-1` (fun x => x \in F)).
      by apply set_finite_preimage;
        [move=> ? ? ? ?; exact: ie|exact: fset_set_finite].
    have [i []] := set_finite_maximum feF eF0.
    by rewrite /preimage => eiF K; exists i => t tF j ejt; apply K; rewrite ejt.
  exists N.+1;apply/fsubsetP => x Fx; apply/imfsetP => /=.
  have [j [_ xej]] := Se _ (FS _ Fx).
  by exists (inord j) => //; rewrite xej inordK // ltnS (H _ Fx).
apply ereal_lim_ge.
  by apply: (@is_cvg_ereal_nneg_series _ (a \o e)) => n; exact: a0.
near=> n.
rewrite -big_image /= lee_sum_nneg_seq // ?fset_uniq //; last first.
  by rewrite map_inj_uniq //; [exact: enum_uniq | move=> i j /ie /ord_inj].
move=> x xF; apply/mapP.
have Nn : (N <= n)%N by near: n; exists N.
move/fsubsetP : FNS => /(_ _ xF)/imfsetP[/= j _ xej].
by exists (widen_ord Nn j) => //; rewrite mem_enum.
Grab Existential Variables. all: end_near. Qed.

Lemma csum_csum (R : realType) (T : pointedType) (I : set T) (K : set nat)
    (J : nat -> set T) (a : T -> {ereal R}) (a0 : (forall x, 0%:E <= a x)%E) :
  I = \bigcup_(k in K) (J k) ->
  K !=set0 ->
  (forall k, J k !=set0) ->
  triviset J ->
  csum I a = csum K (fun k => csum (J k) a).
Proof.
move=> IJ K0 J0 tJ.
have I0 : I !=set0.
  by case: K0 => k Kk; have [t Jkt] := J0 k; rewrite IJ; exists t; exists k.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite {1}/csum; case: pselect => // _.
  apply ub_ereal_sup => /= x [F GI <-{x}].
  pose Fk := fun k => [fset x in F | x \in J k]%fset.
  have tFk : forall i j, i != j -> [disjoint Fk i & Fk j]%fset.
    move=> i j ij.
    rewrite -fsetI_eq0; apply/eqP/fsetP => t; apply/idP/idP => //; apply/negP.
    rewrite inE => /andP[]; rewrite !inE /= => /andP[Ft tJi] /andP[_ tJj].
    rewrite !in_setE in tJi, tJj.
    by move: (tJ _ _ ij); rewrite predeqE => /(_ t) [] // /(_ (conj tJi tJj)).
  pose L := [set k | K k /\ Fk k != fset0].
  have finL : set_finite L.
    set L' := [set k | Fk k != fset0].
    have finL' : set_finite L'.
      pose g := fun t => xget O [set n | t \in J n].
      have sur_g : surjective [set x | x \in F] [set k | Fk k != fset0] g.
        move=> i /fset0Pn[t]; rewrite /Fk !inE /= => /andP[Ft tJi].
        exists t; split => //; rewrite /g; case: xgetP; last by move/(_ i).
        move=> i' _ tJi'; apply/eqP/negPn/negP => /(tJ i i').
        rewrite predeqE => /(_ t); rewrite !in_setE in tJi, tJi'.
        by case => // /(_ (conj tJi tJi')).
      by case: (surjective_set_finite sur_g (fset_set_finite F)).
    have LL' : L `<=` L' by move=> t [].
    by have [] := set_finite_subset LL' finL'.
  set L' : {fset nat} := proj1_sig (set_finite_fset finL).
  have LK : (fun i => i \in L') `<=` K.
    move=> /= i iL'.
    have := proj2_sig (set_finite_fset finL).
    rewrite /= funeqE => /(_ i).
    rewrite iL' => /esym.
    by rewrite /L trueE propeqE => -[_] /(_ Logic.I) [].
  have -> : (\sum_(i <- F) a i = \sum_(k <- L') (\sum_(i <- Fk k) a i)%E)%E.
    have -> : F = (\big[fsetU/fset0]_(x <- L') (Fk x))%fset.
      apply/fsetP => t; apply/idP/idP => [tF|].
        have := GI _ tF; rewrite IJ => -[i Ki Jit].
        apply/bigfcupP; exists i; rewrite ?andbT /L'.
          have := proj2_sig (set_finite_fset finL).
          rewrite funeqE => /(_ i) ->; rewrite /L; split => //.
          apply/negP => /eqP/fsetP/(_ t).
          rewrite !inE /= => /negbT /negP; apply.
          by rewrite tF /= in_setE.
        by rewrite /Fk !inE /= tF in_setE.
      case/bigfcupP => i; rewrite andbT => iL'.
      by rewrite /Fk !inE => /andP[].
    by apply/partition_disjoint_bigfcup; exact: tFk.
  apply: (@le_trans _ _ (\sum_(k <- L') (csum (J k) a))%E).
    apply: lee_sum_seq => i iL'; rewrite /csum; case: pselect => // _.
    apply: ereal_sup_ub; exists (Fk i) => // t.
    by rewrite /Fk !inE /= => /andP[_]; rewrite in_setE.
  rewrite [in X in (_ <= X)%E]/csum; case: pselect => // _.
  by apply ereal_sup_ub; exists L'.
rewrite {1}[in X in (X <= _)%E]/csum; case: pselect => // _.
apply ub_ereal_sup => /= x [L LK <-{x}].
have [/eqP ->|L0] := boolP (L == fset0); first by rewrite big_nil csum_ge0.
have [->|[r Iar]] := gee0P (csum_ge0 a0 I); first by rewrite lee_pinfty.
apply lee_adde => e; rewrite -lee_subl_addr.
pose l := #|` L |.
suff : (\sum_(i < l) csum (J (nth O L i)) a - (e)%:num%:E <= csum I a)%E.
  apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by congr (_ - _)%E; rewrite (big_nth O) // big_mkord.
have [Fj H2] : exists F : 'I_l -> {fset T}%fset, forall j : 'I_l,
  ([set x | x \in F j] `<=` J (nth 0%N L j)) /\
  (csum (J (nth 0%N L j)) a - (e%:num / #|` L |%:R)%:E < \sum_(s <- F j) a s)%E.
  have H1 : forall j : 'I_l, exists Fj : {fset T}%fset,
    ([set x | x \in Fj] `<=` J (nth 0%N L j)) /\
    (csum (J (nth 0%N L j)) a - (e%:num / #|` L |%:R)%:E < \sum_(s <- Fj) a s)%E.
    move=> j; rewrite /csum; case: pselect => // _.
    set es := ereal_sup _.
    have [esoo|[c esc]] : es = +oo%E \/ exists r, es = r%:E.
      suff : (0%:E <= es)%E by move/gee0P.
      by apply ereal_sup_ub; exists fset0 => //; rewrite big_nil.
    - move: Iar; rewrite /csum; case: pselect => // _.
      set es' := ereal_sup _ => es'r.
      suff : (es <= es')%E by rewrite esoo es'r.
      apply: le_ereal_sup => x [F FJ Fx]; exists F => //.
      move/subset_trans : FJ; apply.
      rewrite IJ => t Jt.
      by exists (nth 0%N L j) => //; apply LK; rewrite mem_nth.
    - by rewrite esc; apply: ereal_sup_adherent2.
  move: (@choice _ _ (fun (i : 'I_l) (F : {fset T}%fset) =>
    ([set x | x \in F] `<=` J (nth 0%N L i)) /\
    (csum (J (nth 0%N L i)) a - (e%:num / l%:R)%:E < \sum_(s <- F) a s)%E) H1).
  by case => Fj H2; exists Fj.
pose F := \big[fsetU/fset0]_(i < l) Fj i.
apply: (@le_trans _ _ (\sum_(i <- F) a i)%E); last first.
  rewrite /csum; case pselect => // _; apply ereal_sup_ub; exists F => //.
  rewrite IJ => t /bigfcupP[/= i _] /(proj1 (H2 i)) Jt.
  by exists (nth 0%N L i) => //; apply LK; rewrite mem_nth.
apply: (@le_trans _ _ (\sum_(i < l) (\sum_(j <- Fj i) a j)%E)%E); last first.
  have tFj : (forall i j : 'I_l, i != j -> [disjoint Fj i & Fj j])%fset.
    move=> i j ij; rewrite -fsetI_eq0; rewrite -eq_set0_fset0.
    have Jij0 : J (nth 0%N L i) `&` J (nth 0%N L j) = set0.
      apply tJ; apply: contra ij => /eqP /(congr1 (fun x => index x L)).
      by rewrite index_uniq // index_uniq // => /ord_inj ->.
    apply/eqP; rewrite predeqE => t; split => //.
    rewrite inE => /andP[] /(proj1 (H2 i)) Ji /(proj1 (H2 j)) Jj.
    by rewrite -Jij0; split.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  apply/esym.
  pose IL := [fset i | i in 'I_l]%fset.
  have -> : F = (\bigcup_(i <- IL | true) Fj i)%fset.
    by rewrite /IL big_imfset //= big_enum.
  transitivity ((\sum_(i <- IL) (\sum_(j <- Fj i) a j)%E)%E); last first.
    by rewrite /IL big_imfset //= big_enum.
  by apply partition_disjoint_bigfcup; exact: tFj.
rewrite (_ : e%:num%:E = (\sum_(i < l) (e%:num / l%:R))%:E); last first.
  rewrite big_const iter_addr addr0 card_ord -mulr_natr.
  by rewrite -mulrA mulVr ?mulr1 // unitfE pnatr_eq0 /l cardfs_eq0.
rewrite -NERFin (@big_morph _ _ _ 0 _ _ _ (@opprD R)) ?oppr0//.
rewrite (@big_morph _ _ _ 0%:E _ _ _ addERFin) // -big_split /=.
by apply: lee_sum_ord => i; exact: (ltW (proj2 (H2 i))).
Qed.
