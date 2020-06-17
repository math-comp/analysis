(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences measure.

(******************************************************************************)
(*                       More measure theory (wip)                            *)
(*                                                                            *)
(* {outer_measure set T -> {ereal R}} == type of an outer measure over sets   *)
(*                                 of elements o ftype T where R is expected  *)
(*                                 to be a a realFieldType or a realType      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: swap i and j in the definition of triviset (PR: pending) *)
Lemma triviset_set0 {T} (A : (set T) ^nat) : triviset A -> forall n m, (n <= m)%N ->
  \big[setU/set0]_(i < n) A i `&` A m = set0.
Proof.
move=> tA; elim => [|n ih m]; first by move=> m _; rewrite big_ord0 set0I.
rewrite ltn_neqAle => /andP[nm nm'].
by rewrite big_ord_recr /= setIDl tA // setU0 ih.
Qed.

Lemma triviset_setI {T} (A : (set T) ^nat) : triviset A ->
  forall X, triviset (fun n => X `&` A n).
Proof.
by move=> tA X j i ij; move: (tA _ _ ij); apply: subsetI_eq0; apply subIset; right.
Qed.

Lemma lee_adde (R : realFieldType) (a b : {ereal R}) :
  (forall e : {posnum R}, (a <= b + e%:num%:E)%E) -> (a <= b)%E.
Proof.
move: a b => [a| |] [b| |] //=; rewrite ?(lee_ninfty,lee_pinfty) //;
  try by move/(_ (PosNum ltr01)).
rewrite lee_fin => abe; rewrite leNgt; apply/negP => ba; apply/existsNP : abe.
have ab : 0 < (a - b) / 2 by apply divr_gt0 => //; rewrite subr_gt0.
exists (PosNum ab); apply/negP; rewrite -ltNge lte_fin -ltr_subr_addl.
by rewrite ltr_pdivr_mulr // ltr_pmulr ?subr_gt0 // ltr1n.
Qed.

(* TODO: move to normedtype.v *)
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

Lemma oppe_continuous (R : realFieldType) : continuous (@oppe R).
Proof.
move=> x S /= xS; apply nbhsNKe; rewrite image_preimage //.
by rewrite predeqE => y; split => // _; exists (- y)%E => //; rewrite oppeK.
Qed.

Lemma le_ereal_nneg_series (R : realDomainType) (f : {ereal R} ^nat) :
  (forall n, 0%:E <= f n)%E ->
  {homo (fun n => (\sum_(k < n) f k)%E) : n m / (n <= m)%N >-> (n <= m)%E}.
Proof.
move=> f0 n; elim=> [|m ih]; first by rewrite leqn0 =>/eqP ->; rewrite big_ord0.
rewrite leq_eqVlt => /orP[/eqP-> //|]; rewrite ltnS => /ih /le_trans; apply.
by rewrite big_ord_recr /= lee_addl // outer_measure_ge0.
Qed.

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
move/le_ereal_nneg_series/nondecreasing_seq_ereal_cvg => cu.
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
  move/vM : (n1n) => {vM}vM.
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
  move/uM : (n1n) => {uM}uM.
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

(* *)

Definition sigma_subadditive (R : numFieldType) T
  (mu : set T -> {ereal R}) (A : (set T) ^nat) :=
  (mu (\bigcup_n (A n)) <= lim (fun n => \sum_(i < n) mu (A i)))%E.

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : Type).
Record axioms (mu : set T -> {ereal R}) := OuterMeasure {
  _ : mu set0 = 0%:E ;
  _ : forall x, (0%:E <= mu x)%E ;
  _ : {homo mu : A B / A `<=` B >-> (A <= B)%E} ;
  _ : forall (A : (set T) ^nat), sigma_subadditive mu A }.

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

Lemma outer_measure_sigma_subadditive : forall A, sigma_subadditive mu A.
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
pose B : (set T) ^nat := fun n =>
  match n with | O => X `&` A | 1 => X `&` ~` A | _ => set0 end.
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
  rewrite big_ord_recl /=.
  rewrite big1; last first.
    move=> _ _.
    by rewrite outer_measure0.
  by rewrite adde0.
move: (outer_measure_sigma_subadditive mu B).
rewrite /sigma_subadditive.
have -> : \bigcup_n B n = X.
  transitivity (\big[setU/set0]_(i < 2) B i).
    rewrite (bigcup_recl 2) // bigcup_ord.
    rewrite (_ : \bigcup_i B (2 + i)%N = set0) ?setU0 //.
    rewrite predeqE => t; split => // -[] //.
  by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIDr setUCr setIT.
move/le_trans; apply.
by rewrite (cvg_lim _ cvg_mu_ext).
Grab Existential Variables. all: end_near. Qed.

(* build an outer measure from a measure *)
Section measure_extension.

Variables (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}).

Definition mu_ext : set T -> {ereal R} :=
  fun A => ereal_inf [set mu B | B in (fun x => measurable x /\ A `<=` x)].

Lemma mu_ext_ge0 A : (0%:E <= mu_ext A)%E.
Proof. by apply: lb_ereal_inf => x [B [mB AB] <-{x}]; exact: measure_ge0. Qed.

Lemma mu_ext0 : mu_ext set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: mu_ext_ge0; exact: measurable0.
rewrite /mu_ext; apply ereal_inf_lb.
by exists set0 => //; split => //; exact: measurable0.
Qed.

Lemma le_mu_ext : {homo mu_ext : A B / A `<=` B >-> (A <= B)%E}.
Proof.
move=> A B AB; apply/le_ereal_inf => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_sigma_subadditive : forall A, sigma_subadditive mu_ext A.
Proof.
move=> A; rewrite /sigma_subadditive.
have [[i ioo]|] := pselect (exists i, mu_ext (A i) = +oo%E).
  rewrite (_ : lim _ = +oo%E) ?lee_pinfty //.
  apply: (@ereal_nneg_series_pinfty _ (fun i => mu_ext (A i))%E _ _ ioo) => n.
  by apply lb_ereal_inf => x [B [mB AnB] <-{x}]; exact: measure_ge0.
rewrite -forallN => Aoo.
suff : forall e : {posnum R},
  (mu_ext (\bigcup_n A n) <= lim (fun n : nat => \sum_(i < n) mu_ext (A i)) + (2 * e%:num)%:E)%E.
  move=> H.
  apply lee_adde => e.
  rewrite (_ : e%:num = 2 * (e%:num / 2)); last by rewrite mulrC -mulrA mulVr ?mulr1 // unitfE.
  exact: H.
move=> e.
have [B BA] : {B : (set T) ^nat & forall n,
    A n `<=` B n /\ measurable (B n) /\ (mu (B n) <= mu_ext (A n) + (e%:num / (2 ^ n)%:R)%:E)%E}.
  apply: (@choice _ _
    (fun x y => A x `<=` y /\ measurable y /\ (mu y <= mu_ext (A x) + (e%:num / (2 ^ x)%:R)%:E)%E)) => n.
  rewrite /mu_ext.
  set S := fun _ : {ereal R} => _.
  move infS : (ereal_inf S) => iS.
  case: iS infS => [r| |]; last 2 first.
  - move=> Soo.
    exists setT.
    split => //; split; first exact: measurableT.
    by rewrite lee_pinfty.
  - move=> Soo.
    have : lbound S 0%:E by move=> /= y [B [mB AnB]] <-{y}; apply measure_ge0.
    by move/lb_ereal_inf; rewrite Soo.
  - move=> Sr.
    have en : 0 < e%:num / (2 ^ n)%:R.
      apply divr_gt0 => //.
      by rewrite ltr0n expn_gt0.
    move: (@lb_ereal_inf_adherent _ _ (PosNum en) _ Sr).
    case => x [[B [mB AnB muBx]] xS].
    exists B.
    split => //.
    split => //.
    rewrite muBx -Sr.
    by rewrite ltW.
have H1 : (mu_ext (\bigcup_n A n) <= mu (\bigcup_n B n))%E.
  apply ereal_inf_lb; exists (\bigcup_i B i) => //; split.
  by apply: measurable_bigU => i; move: (BA i) => [_ []].
  by move=> x [n _ Anx]; exists n => //; move: (BA n) => [AB _]; apply AB.
have H2 : (mu (\bigcup_n B n) <= lim (fun k => \sum_(i < k) mu (B i)))%E.
  by apply generalized_Boole_inequality => i; move: (BA i) => [_ []].
apply: (le_trans H1) => {H1} //.
apply: (le_trans H2) => {H2}.
apply: (@le_trans _ _ (lim (fun n => (\sum_(i < n) (mu_ext (A i) + (e%:num / (2 ^ i)%:R)%:E)%E)%E))).
- apply lee_lim.
  + apply: (@is_cvg_ereal_nneg_series _ (mu \o B)) => n.
    apply: measure_ge0.
    by move: (BA n) => [_ []].
  + apply: (@is_cvg_ereal_nneg_series _ (fun i => (mu_ext (A i) + ((e)%:num / (2 ^ i)%:R)%:E)%E)) => n.
    by rewrite adde_ge0 // ?mu_ext_ge0// lee_fin divr_ge0// ler0n.
  + near=> n.
    apply: (@lee_sum R (mu \o B) (fun i => (mu_ext (A i) + ((e)%:num / (2 ^ i)%:R)%:E)))%E => i.
    by move: (BA i) => [AB [mB sumBA]].
rewrite (_ : (fun n : nat => _) = ((fun n => \sum_(i < n) (mu_ext (A i)))%E \+
    (fun n : nat => \sum_(i < n) (((e)%:num / (2 ^ i)%:R)%:E)%E))%E); last first.
  by rewrite funeqE => n; rewrite big_split.
- have H : (fun x => (\sum_(i < x) ((e)%:num / (2 ^ i)%:R)%:E)%E) --> (2 * e%:num)%:E.
    rewrite (_ : (fun n : nat => _) = (fun x => x%:E) \o (series (geometric e%:num (2^-1)%R))); last first.
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
    by rewrite (cvg_lim _ H) //= negb_or /= !negb_and /= orbT orbT.
  by rewrite lee_add2l // (cvg_lim _ H).
Grab Existential Variables. all: end_near. Qed.

Lemma mu_ext_measurable X : measurable X -> mu_ext X = mu X.
Proof.
move=> mX; apply/eqP; rewrite eq_le; apply/andP; split.
- by apply ereal_inf_lb; exists X => //; split.
- by apply/lb_ereal_inf => x [B [mB XB] <-]; rewrite le_measure // ?inE.
Qed.

End measure_extension.

Canonical canonical_outer_measure (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}) : {outer_measure set T -> {ereal R}} :=
    OuterMeasure (OuterMeasure.OuterMeasure (mu_ext0 mu) (mu_ext_ge0 mu)
      (le_mu_ext mu) (mu_ext_sigma_subadditive mu)).

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
  by apply lb_ereal_inf => Y [B [mB XB] <-{Y}]; exact: H.
move=> B mB BX.
have : (mu_ext mu (X `&` A) + mu_ext mu (X `&` ~` A) <=
        mu (B `&` A) + mu (B `&` ~` A))%E.
  apply: lee_add.
  - apply/ereal_inf_lb; exists (B `&` A) => //; split.
    + exact: measurableI.
    + by rewrite subsetI; split => //; apply subIset; [left | right].
  - apply/ereal_inf_lb; exists (B `&` ~` A) => //; split.
    + by apply measurableI => //; exact: measurableC.
    + by rewrite subsetI; split => //; apply subIset; [left | right].
move/le_trans; apply.
rewrite -measure_additive2 //; last 3 first.
  exact: measurableI.
  by apply measurableI => //; exact: measurableC.
  by rewrite setICA -(setIA B) setICr 2!setI0.
by rewrite -setIDr setUCr setIT.
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
  rewrite setIDr (_ : X `&` A `|` X `&` B = (X `&` A) `|` (X `&` B `&` ~` A))//.
  rewrite -[in LHS](setIT B) -(setUCr A) 2!setIDr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply subIset; right.
have /(lee_add2r (mu (X `&` (~` (A `|` B))))) :
    (mu (X `&` A `|` X `&` B `&` ~` A) <=
     mu (X `&` A) + mu (X `&` B `&` ~` A))%E.
  set C : (set T) ^nat := fun n => match n with
    O => X `&` A
  | 1 => X `&` B `&` ~` A
  | _ => set0 end.
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
      by rewrite funeqE => i; rewrite addn2 2!big_ord_recl /= big1 // adde0.
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
- by rewrite setIDl setICr setU0 subsetI; move/disjoints_subset in EF0; split.
- rewrite setIA setIC; apply/setIidPl; rewrite setIDl setICr set0U.
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

Definition caratheodory_mixin := @Measurable.Mixin _ mu.-measurable
  (sigma_algebra_set0 mu) (@sigma_algebra_setC _ _ mu)
  (@sigma_algebra_bigU _ _ mu).

Canonical caratheodory_measurableType : measurableType :=
  Measurable.Pack caratheodory_mixin.
End caratheodory_theorem_instance.

Definition negligeable (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}) (N : set T) :=
  exists A : set T, mu A = 0%:E /\ N `<=` A.

Notation "mu .-negligeable" := (@negligeable _ _ mu)
  (at level 2, format "mu .-negligeable").

Section caratheodory_theorem_part2.
Variables (R : realType) (T : Type) (mu : {outer_measure set T -> {ereal R}}).
Let U := caratheodory_measurableType mu.

Lemma caratheodory_measure0 : mu (set0 : set U) = 0%:E.
Proof. exact: outer_measure0. Qed.

Lemma caratheodory_measure_ge0 : forall x : set U, measurable x -> (0%:E <= mu x)%E.
Proof. by move=> x mx; apply outer_measure_ge0. Qed.

Lemma caratheodory_measure_sigma_additive : @sigma_additive _ U mu.
Proof.
move=> A mA tA.
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

Definition caratheodory_measure := Measure.Measure caratheodory_measure0
 caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
Canonical caratheodory_measureType : {measure _ -> _} :=
  Measure.Pack _ caratheodory_measure.

Lemma caratheodory_measure_complete (N : set U) :
  @negligeable _ U caratheodory_measureType N ->
  mu.-measurable N.
Proof.
case => A [muA0 NA].
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
