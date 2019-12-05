(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import div ssralg ssrint ssrnum fintype bigop order.
From mathcomp Require Import binomial matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* This file defines sequences and prove textbook lemmas about them.
     sequence R == nat -> R (notation R ^nat)
   Outline:
   - consequences of topology.v (squeeze lemma, easy lemmas about convergence
     and limits in section sequences_normedModType)
   - properties of sequences over R (sections sequences_R_*, sequences_R_lemmas_* )
   - a few examples of concrete sequences (harmonic, geometric, arithmetic,
     Euler constant---section exp_base).
   - Density of R (i.e., for any x in R and 0 < a, there is an increasing
     sequence of Q.a that converges to x)
   - Cesaro's lemma.
   - Partial sums and (absolute) convergence of series.
   - Examples of series: harmonic, Riemann.
*)

Reserved Notation "R ^nat" (at level 0).
Reserved Notation "a `^ x" (at level 11).

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) : sequences_scope.

Local Open Scope sequences_scope.

Canonical eventually_filter := FilterType eventually _.
Canonical eventually_pfilter := PFilterType eventually (filter_not_empty _).

Section nat_topologicalType.
Let D : set nat := setT.
Let b : nat -> set nat := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite funeqE => i; rewrite propeqE; split => // _; exists i. Qed.
Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, D k /\ b k t /\ b k `<=` b i `&` b j.
Proof. by move=> i j t _ _ ->{t} ->{i}; exists j. Qed.
Definition nat_topologicalTypeMixin := topologyOfBaseMixin bT bD.
Canonical nat_topologicalType := Topological.Pack
  (@Topological.Class _ (Filtered.Class (Pointed.class nat_pointedType) _)
                        nat_topologicalTypeMixin).
End nat_topologicalType.

Section test. (* ca. 2019-02-21 *)

Local Notation eqolimn := (@eqolim _ _ _ eventually_filter).
Local Notation eqolimPn := (@eqolimP _ _ _ eventually_filter).

Lemma lim_add3sequence (R : numFieldType) (u_ v_ w_ : (R^o) ^nat) : cvg u_ -> cvg v_ -> cvg w_ ->
  lim (u_ + v_ + w_) = lim u_ + lim v_ +  lim w_.
Proof.
move=> /eqolimPn u_cv /eqolimPn v_cv /eqolimPn w_cv.
apply/flim_map_lim.
apply: eqolimn.
rewrite [in LHS]u_cv /= [in LHS]v_cv /= [in LHS]w_cv.
rewrite addrACA -!addrA.
(* rewrite showo. *)
rewrite addo.
(* rewrite showo. *)
rewrite [cst _ + (cst _ + _)]addrA addrA.
rewrite addrACA !addrA -addrA.
rewrite [X in X + _]addrAC.
congr (_ + _ + _ + _).
exact: addo.
Qed.

End test.

Lemma squeeze (T : Type) (R : realFieldType) (f g h : T -> R) (a : filter_on T) :
  (\forall x \near a, f x <= g x <= h x) -> forall (l : R),
  f @ a --> (l : R^o) -> h @ a --> (l : R^o) -> g @ a --> (l : R^o).
Proof.
move=> afgh l fal hal; apply/(@flim_locally _ [pseudoMetricType R of R^o])=> _/posnumP[/= e].
rewrite near_map; near=> x.
rewrite /ball /= ltr_norml; apply/andP; split.
- rewrite ltr_oppl opprB (@le_lt_trans _ _ (h x - l)) //.
  + rewrite ler_sub //.
    by have /(_ _) /andP[//|_ ->] := near afgh x.
  + rewrite (@le_lt_trans _ _ `|h x - l|) // ?real_ler_norm // ?num_real // distrC.
    near: x.
    move/(@flim_locally _ [pseudoMetricType R of R^o]) : hal => /(_ e%:num (posnum_gt0 e)).
    by rewrite near_map.
- rewrite (@le_lt_trans _ _ (l - f x)) //.
  + rewrite ler_sub //.
    by have /(_ _) /andP[|] := near afgh x.
  + rewrite (@le_lt_trans _ _ `|l - f x|) // ?real_ler_norm // ?num_real //.
    near: x.
    move/(@flim_locally _ [pseudoMetricType R of R^o]) : fal => /(_ e%:num (posnum_gt0 e)).
    by rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

Section sequences_normedModType.

Variables (K : numFieldType) (V : normedModType K).

Lemma cvg_cst (k : V) : cvg (fun _ : nat => k).
Proof. apply/cvg_ex; exists k; exact: flim_const. Qed.

Lemma cvg_opp (u_ : V ^nat) : cvg (- u_) = cvg u_.
Proof.
rewrite propeqE; split; case/cvg_ex => /= l ul; apply/cvg_ex; exists (- l).
- move/(@lim_opp _ _ nat_topologicalType) : ul => /subset_trans; apply.
  by rewrite (_ : (fun x : nat => _) = u_) // funeqE => ?; rewrite opprK.
- exact: (@lim_opp _ _ nat_topologicalType).
Qed.

Lemma cvg_add (u_ v_ : V ^nat) : cvg u_ -> cvg v_ -> cvg (u_ + v_).
Proof.
move=> /cvg_ex[l ?] /cvg_ex[l' ?]; apply/cvg_ex; exists (l + l').
exact: (@lim_add _ _ nat_topologicalType).
Qed.

Lemma lim_cst_sequence (l : V) : lim (fun _ : nat => l) = l.
Proof. apply: flim_map_lim; exact: flim_const. Qed.

Lemma lim_opp_sequence (u_ : V ^nat) : cvg u_ -> lim (- u_) = - lim u_.
Proof.
move=> ?; apply: flim_map_lim; exact: (@lim_opp _ _ nat_topologicalType).
Qed.

Lemma lim_add_sequence (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ + v_) = lim u_ + lim v_.
Proof.
move=> *; apply: flim_map_lim; exact: (@lim_add _ _ nat_topologicalType).
Qed.

Lemma lim_sub_sequence (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ - v_) = lim u_ - lim v_.
Proof.
move=> ? ?.
rewrite lim_add_sequence //; by [rewrite lim_opp_sequence|rewrite cvg_opp].
Qed.

Lemma approach_abs (u_ : V ^nat) : u_ @ \oo --> lim u_ ->
  (fun n => `| u_ n |) @ \oo --> (`| lim u_ | : K^o).
Proof.
move/flim_normP => H; apply/(@flim_normP _ [normedModType K of K^o]) => e e0.
rewrite near_map; near=> x; rewrite (le_lt_trans (ler_dist_dist _ _)) //.
near: x; exact: H.
Grab Existential Variables. all: end_near. Qed.

Lemma approach_restrict (u_ : V ^nat) N (f : nat -> V) :
  u_ @ \oo --> (0 : V) -> (fun n => if (n <= N)%nat then f n else u_ n) @ \oo --> (0 : V).
Proof.
move/flim_normP => H; apply/flim_normP => e e0; rewrite near_map; near=> i.
rewrite distrC subr0.
case: ifPn => [|_]; last by rewrite -(subr0 (u_ i)) distrC; near: i; exact: H.
rewrite leqNgt => /negP H0; exfalso; move: H0; apply.
by near: i; rewrite nearE; exists N.+1.
Grab Existential Variables. all: end_near. Qed.

End sequences_normedModType.

Section sequences_R_numFieldType.
Variable R : numFieldType.

Lemma lim_mul_sequence (u_ v_ : R^o ^nat) : cvg u_ -> cvg v_ ->
  lim (u_ * v_) = lim u_ * lim v_.
Proof.
by move=> *; apply: flim_map_lim; apply: (@lim_scale _ _ nat_topologicalType).
Qed.

Lemma cvg_scalel (u_ : R^o ^nat) (k : R^o) : cvg u_ -> cvg (fun n => k * u_ n).
Proof.
move=> /cvg_ex[l ul]; apply/cvg_ex; exists (k * l).
apply: (@lim_scale _ _ nat_topologicalType) => //; exact: (@flim_const _ [pseudoMetricType R of R^o]).
Qed.

Lemma cvg_scaler (u_ : R^o ^nat) (k : R^o) : cvg u_ -> cvg (fun n => u_ n * k).
Proof.
rewrite (_ : (fun n => u_ n * k) = (fun n => k * u_ n)); last first.
  by rewrite funeqE => i; rewrite mulrC.
exact/cvg_scalel.
Qed.

Lemma cvg_scaler' (u_ : R^o ^nat) (k : R^o) : k != 0 -> cvg (fun n => u_ n * k) -> cvg u_.
Proof.
move=> k0 /cvg_ex[/= l] ul.
apply/cvg_ex; exists (l / k); apply/(@flim_normP _ [normedModType R of R^o]) => e e0.
rewrite near_map; near=> i.
rewrite -(@ltr_pmul2l _ `|k|) ?normr_gt0 // -normmZ scalerBr scalerAr.
rewrite (_ : k *: k^-1 = k * k^-1) // divrr ?unitfE // mulr1.
rewrite (_ : k *: (u_ i : R^o) = k * u_ i) // mulrC.
near: i.
move/(@flim_normP _ [normedModType R of R^o]) : ul.
have K : 0 < `|k| * e by rewrite mulr_gt0 // normr_gt0.
by move/(_ _ K); rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

End sequences_R_numFieldType.

Section sequences_R_realFieldType.
Variable R : realFieldType.

Lemma approach_inv (u_ : (R^o) ^nat) :
  cvg u_ -> (forall n, 0 < u_ n) -> 0 < lim u_ ->
  (fun n => (u_ n)^-1) @ \oo --> (lim u_)^-1.
Proof.
set u := lim u_ => cu un u0; apply/flim_normP => e e0.
rewrite near_map; near=> n.
rewrite (_ : `| _ | = `| u_ n - u | / (u * u_ n)); last first.
  rewrite -{1}(div1r u) -(div1r (u_ n)) -mulNr addf_div ?lt0r_neq0 //.
  rewrite mulN1r mul1r normmZ; congr (_ * _).
  by apply/normr_idP; rewrite invr_ge0 mulr_ge0 // ltW.
apply: (@lt_le_trans _ _ ((e * u^+2 / 2) * (2 / u^+2))); last first.
  rewrite mulrA -(mulrA (e * _)) mulVr ?unitfE // mulr1 -mulrA divrr ?mulr1 //.
  by rewrite unitfE sqrf_eq0 lt0r_neq0.
rewrite ltr_pmul //.
- by rewrite invr_ge0 mulr_ge0 // ltW.
- rewrite distrC; near: n.
  have H : 0 < e * u ^+ 2 / 2 by rewrite mulr_gt0 // mulr_gt0 // exprn_gt0.
  by move/flim_normP : cu => /(_ _ H); rewrite near_map.
- suff H : u_ n > u / 2.
    rewrite invrM ?unitfE ?lt0r_neq0 // ltr_pdivr_mull // mulrA.
    rewrite ltr_pdivl_mulr expr2 ?mulr_gt0 // mulrA mulVr ?unitfE ?lt0r_neq0 //.
    by rewrite  mul1r mulrC -lter_pdivr_mull // mulrC.
  near: n.
  have u20 : 0 < u / 2 by rewrite divr_gt0.
  move/flim_normP : cu => /(_ _ u20); rewrite near_map => H.
  near=> n.
  rewrite -(@ltr_add2r _ (u / 2)) -splitr -ltr_sub_addl.
  case/boolP : (u < u_ n) => [uun|].
    by rewrite (@lt_le_trans _ _ 0) // ?subr_lt0 // divr_ge0 // ltW.
  rewrite -leNgt -subr_ge0 => /normr_idP <-.
  by near: n.
Grab Existential Variables. all: end_near. Qed.

End sequences_R_realFieldType.

Definition increasing (T : numDomainType) (u_ : T ^nat) := forall n, u_ n <= u_ n.+1.

Definition decreasing (T : numDomainType) (u_ : T ^nat) := increasing (- u_).

Lemma increasing_ler (T : numDomainType) (u_ : T ^nat) : increasing u_ ->
  {homo u_ : n m / (n <= m)%nat >-> n <= m}.
Proof.
move=> iu n; elim=> [|m ih]; first by rewrite leqn0 => /eqP ->; exact/lexx.
rewrite leq_eqVlt => /orP[/eqP <-|]; first exact/lexx.
rewrite ltnS => /ih/le_trans; apply; apply iu.
Qed.

Definition cauchy_seq (K : numDomainType) (V : normedModType K) (u_ : V ^nat) :=
  forall eps : {posnum K}, \forall n \near (\oo, \oo), `| u_ n.1 - u_ n.2 | < eps%:num.

Lemma cvg_cauchy_seq (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  cvg u_ -> cauchy_seq u_.
Proof.
move/flim_normP => H e; near=> n.
rewrite -(addrK (- lim u_) (u_ n.1)) opprK -(addrA (u_ n.1 - _)).
rewrite (le_lt_trans (ler_norm_add _ _)) // (splitr e%:num).
rewrite ltr_add //; near: n; apply: filter_pair_near_of => /= x y xoo yoo.
rewrite distrC; near: x; exact: H.
near: y; exact: H.
Grab Existential Variables. all: end_near. Qed.

Lemma approach_addn (K : numFieldType) (V : normedModType K) (u_ : V ^nat) (l : V) (N : nat) :
  u_ --> l -> (fun n => u_ (n + N)%nat) --> l.
Proof.
move=> ul; move/flim_normP : (ul) => H.
apply/flim_normP => e e0; rewrite near_map; near=> n.
rewrite distrC -(subrKA (u_ n)) (le_lt_trans (ler_norm_add _ _)) //.
rewrite (splitr e)  ltr_add //; last first.
  by rewrite distrC; near: n; apply H; rewrite divr_gt0.
near: n.
have /cvg_cauchy_seq : cvg u_ by apply/cvg_ex; exists l.
have e20 : 0 < e / 2 by rewrite divr_gt0.
rewrite /cauchy_seq => /(_ (PosNumDef _ e20)) /= -[[a b] /= [ao bo] ab]; near=> n.
apply (ab ((n + N)%nat, n)); split => /=.
- near: n; case: ao => a0 _ a0a; near=> n.
  apply a0a; near: n.
  by rewrite nearE; exists (a0 - N)%nat => // y; rewrite leq_subLR addnC.
- near: n; case: bo => b0 _ b0b; near=> n.
  by apply b0b; near: n; rewrite nearE; exists b0.
Grab Existential Variables. all: end_near. Qed.

Lemma approach_subn (K : numFieldType) (V : normedModType K) (u_ : V ^nat) (l : V) (N : nat) :
  u_ --> l -> (fun n => u_ (n - N)%nat) --> l.
Proof.
move=> ul; move/flim_normP : (ul) => H.
apply/flim_normP => e e0; rewrite near_map; near=> n.
rewrite distrC -(subrKA (u_ n)) (le_lt_trans (ler_norm_add _ _)) //.
rewrite (splitr e)  ltr_add //; last first.
  by rewrite distrC; near: n; apply H; rewrite divr_gt0.
near: n.
have /cvg_cauchy_seq : cvg u_ by apply/cvg_ex; exists l.
have e20 : 0 < e / 2 by rewrite divr_gt0.
rewrite /cauchy_seq => /(_ (PosNumDef _ e20)) /= -[[a b] /= [ao bo] ab]; near=> n.
apply (ab ((n - N)%nat, n)); split => /=.
- near: n; case: ao => a0 _ a0a; near=> n.
  apply a0a; near: n.
  by rewrite nearE; exists (a0 + N)%nat => // y /(leq_sub2r N); rewrite addnK.
- near: n; case: bo => b0 _ b0b; near=> n.
  by apply b0b; near: n; rewrite nearE; exists b0.
Grab Existential Variables. all: end_near. Qed.

Definition cauchy_seq_entourages (K : numDomainType) (V : normedModType K) (u_ : V ^nat) :=
  forall E, E \in entourages -> exists n,
    forall x, (x.1 >= n)%nat -> (x.2 >= n)%nat -> (u_ x.1, u_ x.2) \in E.

Lemma cauchy_seqP (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  cauchy_seq u_ <-> cauchy_seq_entourages u_.
Proof.
rewrite /cauchy_seq /cauchy_seq_entourages; split=> [csu E|csu -[e e0]].
- rewrite inE => /asboolP; rewrite /entourages => -[e e0 HE].
  have {csu}csu := csu (PosNumDef _ e0).
  near \oo => N; exists N => X NX1 NX2.
  rewrite inE; apply/asboolP/HE => /=; rewrite -ball_normE /ball_.
  move: X NX1 NX2; near: N.
  move: csu; rewrite -near2_pair => -[[x1 x2] /= [Hx1 Hx2] x1x2].
  near=> N; move=> -[y1 y2] /= Ny1 Ny2.
  apply (x1x2 (y1, y2)); split => /=.
  move: y1 Ny1; near: N; move: Hx1 => [i _ Hi].
  by exists i => // j ij y1 ?; apply Hi; rewrite (leq_trans ij).
  move: y2 Ny2; near: N; move: Hx2 => [i _ Hi].
  by exists i => // j ij y2 jy2; apply Hi; rewrite (leq_trans ij).
- have /asboolP HE : @entourages _ V (fun x => `|x.1 - x.2| < e).
    by exists e => // x; rewrite -ball_normE.
  move: csu => /(_ (fun x => `|x.1 - x.2| < e)); rewrite inE => /(_ HE){HE} [N csu].
  near=> n.
  apply/asboolP; move: csu => /(_ n); rewrite inE /=; apply;
    near: n; rewrite near_simpl -near2_pair /=.
  + by apply filter_prod1; exists N.
  + by apply filter_prod2; exists N.
Grab Existential Variables. all: end_near. Qed.

Lemma cauchy_seq_cauchy (K : numFieldType) (V : normedModType K) (u_ : V ^nat) : cauchy_seq u_ <-> cauchy (u_ @ \oo).
Proof.
split=> [csu e e0 | csu e].
- rewrite near_simpl; near=> x => /=; rewrite -ball_normE /ball_.
  by near: x; have := csu (PosNumDef _ e0).
- near=> x; rewrite -/(ball_ (fun x => `| x |) _ _ _) ball_normE; near: x.
  by have := csu e%:num (posnum_gt0 e); rewrite !near_simpl near2E.
Grab Existential Variables. all: end_near. Qed.

Section sequences_R_lemmas_realFieldType.
Variable R : realFieldType.

Lemma dvgP (u_ : R^o ^nat) :
  u_ --> +oo <-> forall A : {posnum R}, \forall n \near \oo, A%:num <= u_ n.
Proof.
split.
  move=> ulim A; rewrite -(near_map u_ \oo (<=%R A%:num)).
  by apply: ulim; apply: locally_pinfty_ge.
move=> /(_ (PosNum _)) u_ge X [A [Ar AX]].
rewrite near_simpl [\forall x \near _, X x](near_map u_ \oo).
near=> x.
apply: AX; rewrite (@lt_le_trans _ _ ((maxr 0 A) +1)) //.
  by rewrite ltr_spaddr // lexU lexx orbT.
by near: x; apply: u_ge; rewrite ltr_spaddr // lexU lexx.
Grab Existential Variables. all: end_near. Qed.

Lemma dvgN (u_ : R^o ^nat) : u_ --> -oo <-> - u_ --> +oo.
Proof.
split; move=> uo /= x ox; move: (uo ((fun z => - z) @` x)) => {uo}uo.
- rewrite (_ : _ x = [filter of (u_ : R^o ^nat)] ([eta -%R] @` x)) //; last first.
    rewrite propeqE; split; move=> -[] i _ Hi; exists i => //;
      apply (subset_trans Hi) => j /=.
    + by move=> xuj; exists ((- u_) j) => //; rewrite opprK.
    + by move=> -[z xz /eqP]; rewrite eqr_oppLR => /eqP zuj; rewrite zuj in xz.
  apply uo.
  rewrite (_ : _ (_ @` x) = [filter of +oo] x) //.
  rewrite propeqE; split; move=> -[z [zreal zx]]; exists (- z); rewrite realN;
    split => // y zy; move: (zx (- y)).
  by rewrite ltr_oppl => /(_ zy) => -[u xu /eqP]; rewrite eqr_opp => /eqP <-.
  by rewrite ltr_oppr => /(_ zy) => xy; exists (- y) => //; rewrite opprK.
- rewrite (_ : _ x = [filter of - u_] ([eta -%R] @` x)); last first.
    rewrite propeqE; split; move=> -[] i _ Hi; exists i => //;
      apply (subset_trans Hi) => j /=.
    + by move=> xuj; exists (u_ j).
    + by move=> -[z xz /eqP]; rewrite eqr_opp => /eqP <-.
  apply uo.
  rewrite (_ : _ (_ x) = [filter of -oo] x) //.
  rewrite propeqE; split; move=> -[z [zreal zx]]; exists (- z); rewrite realN;
    split => // y zy; move: (zx (- y)).
  by rewrite ltr_oppr => /(_ zy) => -[u xu /eqP]; rewrite eqr_opp => /eqP <-.
  by rewrite ltr_oppl => /(_ zy) xy; exists (- y) => //; rewrite opprK.
Qed.

Lemma dvgNP (u_ : R^o ^nat) :
  u_ --> -oo <-> forall A : R, A < 0 -> \forall n \near \oo, A >= u_ n.
Proof.
split; [have H := proj1 (dvgP (- u_)) | have H := proj2 (dvgP (- u_))].
- move/dvgN/dvgP => Au A A0.
  have @A' : {posnum R}.
    by apply: PosNum; rewrite -(opprK A) ltr_oppl oppr0 in A0; exact: A0.
  near=> n.
  rewrite -(opprK (u_ _)) ler_oppl.
  suff : A'%:num <= - u_ n by rewrite (_ : A'%:num = - A :> R).
  by near: n.
- move=> Au; apply/dvgN/dvgP => A.
  move: (Au (- A%:num)); rewrite ltr_oppl oppr0 => /(_ (posnum_gt0 A)) => {Au}Au.
  near=> n.
  rewrite -(opprK A%:num) ler_oppl opprK.
  by near: n.
Grab Existential Variables. all: end_near. Qed.

Lemma dvg_ler (u_ v_ : R^o ^nat) : (\forall n \near \oo, u_ n <= v_ n) ->
  u_ --> +oo -> v_ --> +oo.
Proof.
move=> uv.
move/dvgP => dvgu.
apply/dvgP => A.
near=> n.
have uA := dvgu A.
rewrite (@le_trans _ _ (u_ n)) //; by near: n.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_ge0 (u_ : R^o ^nat) N : cvg u_ ->
  (forall n, (N <= n)%nat -> 0 <= u_ n) -> 0 <= lim u_.
Proof.
move=> /flim_normP cu H.
rewrite leNgt; apply/negP => u0.
have /cu : 0 < `| lim u_ |.
  by rewrite -normrN normr_gt0 eqr_oppLR lt_eqF // oppr0.
rewrite near_map => -[M _ K].
near \oo => m.
have /K : (M <= m)%nat by near: m; exists M.
apply/negP; rewrite -leNgt distrC -normrN (@le_trans _ _ `|- lim u_|%R) //.
rewrite ger0_norm ?oppr_ge0; last exact/ltW.
rewrite (@le_trans _ _ `|u_ m - lim u_|%R)// ger0_norm.
  rewrite ler_subr_addr addrC subrr; apply/H.
  by near: m; exists N.
rewrite subr_ge0 (@le_trans _ _ 0) //; first by rewrite ltW.
by apply H; near: m; exists N.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_ler (u_ v_ : R^o ^nat) N :
  (forall n, (N <= n)%nat -> u_ n <= v_ n) ->
  cvg u_ -> cvg v_ -> lim u_ <= lim v_.
Proof.
move=> uv cu cv.
rewrite -subr_ge0 -(@lim_opp_sequence _ [normedModType R of R^o]) //.
rewrite -(@lim_add_sequence _ [normedModType R of R^o]) // ?cvg_opp //.
apply (@lim_ge0  _ N); first by apply/cvg_add => //; rewrite cvg_opp.
move=> n; rewrite subr_ge0; exact/uv.
Qed.

Lemma decreasing_cvg_ger (u_ : R^o ^nat) : decreasing u_ -> cvg u_ ->
  forall n, lim u_ <= u_ n.
Proof.
move=> du ul p; rewrite leNgt; apply/negP => up0.
have abs : forall n, (n >= p)%nat -> u_ n <= u_ p.
  by move=> n pn; move: (increasing_ler du pn); rewrite ler_oppl opprK.
move/flim_normP : ul => /(_ `|u_ p - lim u_|%R).
rewrite {1}ltr0_norm ?subr_lt0 // opprB subr_gt0 => /(_ up0).
rewrite near_map => ul.
near \oo => N.
have /abs uNp : (p <= N)%nat by near: N; rewrite nearE; exists p.
have : `|lim u_ - u_ N| >= `|u_ p - lim u_|%R.
 rewrite ltr0_norm // ?subr_lt0 // opprB distrC.
 rewrite (@le_trans _ _ (lim u_ - u_ N)) // ?ler_sub //.
 rewrite (_ : `| _ | = `|u_ N - lim u_|%R) // ler0_norm // ?opprB //.
 by rewrite subr_le0 (le_trans _ (ltW up0)).
rewrite leNgt => /negP; apply; by near: N.
Grab Existential Variables. all: end_near. Qed.

Lemma increasing_cvg_ger (u_ : R^o ^nat) : increasing u_ -> cvg u_ ->
  forall n, u_ n <= lim u_.
Proof.
move=> iu cu n; move: (@decreasing_cvg_ger (- u_)); rewrite /decreasing opprK.
by move=> /(_ iu); rewrite cvg_opp => /(_ cu n); rewrite (@lim_opp_sequence _ [normedModType R of R^o]) // ler_oppl opprK.
Qed.

End sequences_R_lemmas_realFieldType.

Section sequences_R_lemmas.
Variable R : realType.

Lemma cvg_has_ub (u_ : R^o ^nat) :
  cvg u_ -> has_ub (in_set [set `|u_ n| | n in setT]).
Proof.
case/cvg_seq_bounded => /= M uM; apply/has_ubP/nonemptyP.
exists M; apply/ubP => x; rewrite inE => /asboolP[n _ <-{x}]; exact: uM.
Qed.

Lemma increasing_upper_bound_cvg (u_ : (R^o) ^nat) N : increasing u_ ->
  (forall n, u_ n <= N) -> cvg u_ /\ lim u_ = sup (in_set [set u_ n | n in setT]).
Proof.
move=> iu uN.
set S := in_set [set u_ n | n in setT].
set l := sup S.
have supS : has_sup S.
  apply/has_supP; split; first by exists (u_ O); rewrite in_setE; exists O.
  exists N; rewrite in_setE => /= x.
  rewrite negb_imply; apply propF => /andP[].
  rewrite in_setE=> -[m _] <-{x}; rewrite -ltNge.
  by move: (uN m) => /le_lt_trans H/H; rewrite ltxx.
move: (sup_ub (proj2 supS)) => /ubP ubS.
suff ul : u_ @ \oo --> (l:R^o) by split; [apply/cvg_ex; exists l | exact/flim_lim].
apply: flim_normW => _/posnumP[e]; rewrite near_map.
have [m um] : exists m, l - e%:num <= u_ m <= l.
  case: (sup_adherent supS (posnum_gt0 e)) => uns.
  rewrite in_setE => -[p _] <-{uns} => supep.
  exists p; rewrite ltW //=.
  have /ubS : S (u_ p) by apply/asboolP; exists p.
  exact.
near=> p.
rewrite distrC ler_norml -(ler_add2l l) addrCA subrr addr0.
(* NB: ler_add2r defined with {mono notation} vs. ltr_add2r (defined as an equality) *)
rewrite -[in X in _ && X](ler_add2r l) subrK; apply/andP; split; last first.
  rewrite (@le_trans _ _ l) // ?ler_addr //.
  have /ubS : S (u_ p) by apply/asboolP; exists p.
  exact.
case/andP : um => /le_trans um _; rewrite um //.
suff : (m <= p)%nat by move/increasing_ler; exact.
near: p.
rewrite nearE; by exists m.
Grab Existential Variables. all: end_near. Qed.

Lemma decreasing_lower_bound_cvg (u_ : (R^o) ^nat) N : decreasing u_ ->
  (forall n, N <= u_ n) -> cvg u_.
Proof.
move=> du Nu.
have {Nu} : forall n, (- u_) n <= - N by move=> ?; rewrite ler_oppl opprK.
case/(increasing_upper_bound_cvg du); by rewrite cvg_opp.
Qed.

Lemma increasing_has_ub_cvg (u_ : (R^o) ^nat) : increasing u_ ->
  has_ub (in_set [set u_ n | n in setT]) ->
  cvg u_ /\ lim u_ = sup (in_set [set u_ n | n in setT]).
Proof.
move=> iu /has_ubP/nonemptyP[N]; rewrite inE => /forallbP uN.
apply/(@increasing_upper_bound_cvg _ N iu) => n.
move: (uN (u_ n)); rewrite inE => /implyP; apply.
by apply/asboolP; exists n.
Qed.

Lemma increasing_cvg_has_sup (u_ : (R^o) ^nat) : increasing u_ ->
  cvg u_ -> has_sup (in_set [set u_ n | n in setT]).
Proof.
move=> iu cu; move/cvg_ex : (cu) => [/= l ul].
apply/has_supP; split.
  by apply/nonemptyP; exists (u_ O); rewrite inE; apply/asboolP; exists O.
apply/nonemptyP; exists l; apply/ubP => /= x; rewrite inE => /asboolP[p _ <-{x}].
have : forall m, (m >= p)%nat -> u_ m >= u_ p by move=> m /(increasing_ler iu).
move/lim_ler => /(_ (@cvg_cst _ [normedModType R of R^o] (u_ p)) cu).
rewrite (@lim_cst_sequence _ [normedModType R of R^o]) => /le_trans; apply.
by move/flim_lim : ul => ->.
Qed.

Lemma cauchy_seq_cvg (u_ : R^o ^nat) : cauchy_seq u_ -> cvg u_.
Proof. move/cauchy_seq_cauchy; exact: R_complete. Qed.

Lemma adjacent (u_ v_ : R^o ^nat) : increasing u_ -> decreasing v_ ->
  (u_ - v_) --> (0 : R^o) -> lim u_ = lim v_.
Proof.
move=> iu dv uv0.
have vu : forall n, v_ n >= u_ n.
  pose w_ : R^o ^nat := v_ - u_.
  have dw : decreasing w_.
    move=> n; rewrite /w_ opprB -subr_ge0 opprB addrA addrC 2!addrA -addrA addr_ge0 //.
    rewrite addrC subr_ge0; exact: iu.
    rewrite -(opprK (v_ n)) subr_ge0; exact: dv.
  have {dw}w0 : forall n, 0 <= w_ n.
    move=> n.
    have <- : lim w_ = 0.
      apply/flim_lim; move/(@lim_opp _ _ nat_topologicalType) : uv0.
      by rewrite oppr0 (_ : (fun _ => _) = v_ - u_) // funeqE => ?; rewrite opprB.
    have ? : cvg w_.
      apply/cvg_ex; exists 0.
      rewrite (_ : w_ = - (u_ - v_)); last by rewrite funeqE => i; rewrite opprB.
      by rewrite -oppr0; apply: (@lim_opp _ _ nat_topologicalType).
    exact: decreasing_cvg_ger.
  by move=> n; rewrite -subr_ge0 w0.
have cu : cvg u_.
  have : forall n, u_ n <= v_ O.
    move=> n; rewrite (le_trans (vu _)) //.
    by move/increasing_ler : dv => /(_ O n (leq0n n)); rewrite ler_oppl opprK.
  by case/(increasing_upper_bound_cvg iu).
have cv : cvg v_.
  have ?: forall n, u_ O <= v_ n.
    by move=> n; rewrite (le_trans _ (vu _)) //; exact: increasing_ler.
  exact: (@decreasing_lower_bound_cvg _ (u_ O)).
case/cvg_ex : (cu) => l Hl.
case/cvg_ex : (cv) => l' Hl'.
apply/eqP.
rewrite -subr_eq0 -lim_sub_sequence //; exact/eqP/flim_lim.
Qed.

End sequences_R_lemmas.

Section sequences_examples.
Variable R : realType.

Definition harmonic_seq : R^o ^nat := fun n => n.+1%:R^-1.

Lemma harmonic_seq_gt0 i : 0 < harmonic_seq i.
Proof. by rewrite /harmonic_seq invr_gt0 ltr0n. Qed.

Lemma harmonic_seq_ge0 i : 0 <= harmonic_seq i.
Proof. exact/ltW/harmonic_seq_gt0. Qed.

Lemma approach_harmonic_seq : harmonic_seq --> (0 : R^o).
Proof.
apply: flim_normW => e e0; rewrite near_map; near=> i.
rewrite distrC subr0 (_ : `| _ | = `|i.+1%:R^-1|%R) //.
rewrite ger0_norm ?invr_ge0 ?ler0n // -(mulr1 (_^-1)) ler_pdivr_mull ?ltr0n //.
rewrite -addn1 natrD mulrDl mul1r -ler_subl_addr -ler_pdivr_mulr //.
near: i; rewrite nearE /locally /= /eventually /=.
set j : R := let k := (1 - e) / e in if k \in Rint then `|k| else floor `|k| + 1.
have /RintP[z jz] : j \in Rint.
  rewrite /j; case: ifP => [/RintP[x ex] | _].
  by apply/RintP; exists `|x|%R; rewrite ex intr_norm.
  by rewrite rpredD // ?isint_floor // Rint1.
have /ZnatP[n zn] : 0 <= z.
  rewrite -(@ler0z R) -jz /j; case: ifPn => _; first exact: normr_ge0.
  by rewrite addr_ge0 // floor_ge0 normr_ge0.
exists n => // i; rewrite -(@ler_nat R); apply le_trans.
rewrite (@le_trans _ _ j) //; last by rewrite jz zn.
rewrite /j; case: ifPn => [_| _].
by rewrite real_ler_norm // Num.Internals.num_real.
by rewrite (le_trans _ (ltW (floorS_gtr _))) // real_ler_norm // Num.Internals.num_real.
Grab Existential Variables. all: end_near. Qed.

Definition geometric_seq_half : R^o ^nat := fun n => ratr (1%:Q / (2 ^ n)%:Q).

Lemma approach_geometric_seq_half : geometric_seq_half --> (0 : R^o).
Proof.
have H : forall n : nat, ratr (1%:Q / (2 ^ n)%:~R) <= harmonic_seq n.
  suff H : forall n : nat, n.+1%:~R <= (2 ^ n)%:~R :> R.
    move=> n.
    rewrite /harmonic_seq (_ : n.+1%:R^-1 = ratr (1%:Q / n.+1%:Q)); last first.
      by rewrite rmorph_div /= ?unitfE ?intq_eq0 // !ratr_int div1r.
    rewrite ler_rat // !div1r ler_pinv //=; last first.
      by rewrite !inE ltr0z andbT unitfE intq_eq0.
      rewrite inE ltr0z unitfE intr_eq0 expf_neq0 //= lt_neqAle eq_sym.
      by rewrite expf_neq0 //= -exprnP // exprn_ge0.
    rewrite ler_int.
    move: (H n).
    by rewrite ler_int.
  elim => [|n]; first by rewrite ler_int.
  rewrite ler_int => ih.
  rewrite -{1}addn1 ler_int exprSz mul2z PoszD ler_add // -exprnP.
  by destruct n => //; rewrite (le_trans _ ih).
apply (@squeeze _ _ (fun=> (0 : R^o)) geometric_seq_half harmonic_seq).
near=> n; by rewrite H andbT ler0q divr_ge0 // ler0z -exprnP exprn_ge0.
exact: (@flim_const _ [pseudoMetricType R of R^o]).
exact: approach_harmonic_seq.
Grab Existential Variables. all: end_near. Qed.

Definition arithmetic_seq (a z : R) : R^o ^nat := fun n => a + z *+ n.

Lemma arithmetic_seq_dvg (a : R) (z : R^o) : z > 0 -> arithmetic_seq a z --> +oo.
Proof.
move=> z0; apply/dvgP => A; rewrite nearE.
exists (`| (ifloor ((A%:num - a) / z) + 1)%R |%N) => // i.
rewrite -(@ler_nat [numDomainType of R]) => Hi.
rewrite -ler_subl_addl -mulr_natr -ler_pdivr_mull // mulrC (le_trans _ Hi) //.
case: (ltrP (A%:num - a) 0) => Aa0.
  by rewrite (@le_trans _ _ 0) // pmulr_lle0 // ?invr_gt0 // ltW.
move: (ltW (floorS_gtr ((A%:num - a) / z))) => /le_trans; apply.
rewrite [X in X + _ <= _](floorE _) {2}(_ : 1 = 1%:~R) // -intrD.
rewrite -mulrz_nat ler_int -{1}(@gez0_abs (_ + _)) ?natz //.
by rewrite addr_ge0 // ifloor_ge0 divr_ge0 // ltW.
Qed.

(* TODO *)
Definition geometric_seq (a z : R) : R^o ^nat := fun n => a * z ^+ n.

Section exp_base.

Definition e_seq : (R^o) ^nat := fun n => (1 + 1 / n%:R) ^+ n.

Lemma e_seq0 : e_seq O = 1.
Proof. by rewrite /e_seq expr0 {1}(_ : 1 = 1%:R) // ler_nat. Qed.

Lemma e_seq1 : e_seq 1%nat = 2.
Proof. by rewrite /e_seq expr1 divr1. Qed.

Lemma e_seq2 : e_seq 2%nat = 9%:R / 4%:R.
Proof.
rewrite /e_seq -{1}(@divrr _ 2) ?unitfE // -mulrDl.
by rewrite expr_div_n {2}(_ : 1 = 1%:R) // -natrD -2!natrX.
Qed.

Section e_seq_is_bounded_by_4.

Let v_ (n m : nat) : R^o := (n - m + 2)%:R / (n - m)%:R.

Let v_increasing (n : nat) : forall m, (m < n)%nat -> v_ n.*2 m < v_ n.*2 m.+1.
Proof.
move=> m mn.
rewrite /v_.
have H : forall p q, (1 < q < p)%nat -> (p%:R : R) / q%:R < (p%:R - 1) / (q%:R - 1).
  move=> p q pq; rewrite ltr_pdivr_mulr; last first.
    by move/andP : pq => -[a b]; rewrite (_ : 0 = 0%:R) // ltr_nat (ltn_trans _ a).
  rewrite mulrAC ltr_pdivl_mulr; last first.
    by rewrite subr_gt0 (_ : 1 = 1%:R) // ltr_nat; case/andP: pq.
  by rewrite mulrBl mulrBr mul1r mulr1 ler_lt_sub // ltr_nat; case/andP : pq.
rewrite -(addn1 m) !subnDA (@natrB _ _ 1); last first.
  by rewrite subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (_ : (n.*2 - m - 1 + 2)%:R = (n.*2 - m + 2 - 1)%:R); last first.
  by rewrite !subn1 !addn2 /= prednK // subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (@natrB _ _ 1) ?subn_gt0 ?addn2 //.
apply H; apply/andP; split; last by rewrite ltnS.
move: (mn); rewrite -(ltn_add2r 1) !addn1 => mn'.
by rewrite ltn_subRL addn1 (leq_trans mn'){mn'} // -addnn -{1}(addn0 n) ltn_add2l (leq_trans _ mn).
Qed.

Let v_increasing_ler (n : nat) : forall i, (i < n)%nat -> v_ n.*2 0 <= v_ n.*2 i.
Proof.
elim=> // -[/= _ n1|i ih ni].
  by apply/ltW/v_increasing; rewrite (ltn_trans _ n1).
rewrite (le_trans (ih _)) // ?(leq_trans _ ni) //.
by apply/ltW/v_increasing; rewrite (leq_trans _ ni).
Qed.

Let v_prod (n : nat) : (0 < n)%nat ->
  \prod_(i < n) v_ n.*2 i = (n.*2.+2 * n.*2.+1)%:R / (n.+2 * n.+1)%:R.
Proof.
move=> n0; set lhs := LHS. set rhs := RHS.
rewrite -(@divr1_eq _ lhs rhs) // {}/lhs {}/rhs invf_div mulrA.
rewrite /v_ big_split /= -mulrA mulrACA.
rewrite [X in X * _ = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R); last first.
  rewrite 2!big_ord_recr /= -mulrA; congr (_ * _).
  by rewrite -addnn addnK subnS addnK 2!addn2 /= natrM prednK.
rewrite [X in _ * X = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R^-1); last first.
  rewrite 2!big_ord_recl /= mulrA [in LHS]mulrC; congr (_ * _).
    rewrite subn0 addn2 subn1 addn2 prednK ?double_gt0 //.
    by rewrite natrM invrM ?unitfE // mulrC.
    apply eq_bigr => i _; congr (_ %:R^-1).
    rewrite /bump !leq0n !add1n -addn2 subnDA subn2 addn2 /= prednK; last first.
      rewrite -subnS subn_gt0 -addnn -(addn1 i) (@leq_trans n.+1) //.
      by rewrite addn1 ltnS.
      by rewrite -{1}(addn0 n) ltn_add2l.
    by rewrite prednK // subn_gt0 -addnn (@leq_trans n) // leq_addr.
by rewrite -big_split /= big1 // => i _; rewrite divrr // ?unitfE addn2.
Qed.

Lemma e_seq_bound : forall n, (0 < n)%nat -> e_seq n < 4%:R.
Proof.
move=> n n0.
rewrite /e_seq -{1}(@divrr _ n%:R) ?unitfE ?pnatr_eq0 -?lt0n // -mulrDl.
rewrite (_ : _ ^+ n = \prod_(i < n) ((n%:R + 1) / n%:R)); last first.
  move _ : (_ / _) => h.
  elim: n n0 => // -[_ _|n ih _]; first by rewrite big_ord_recl big_ord0 mulr1 expr1.
  by rewrite exprS ih // [in RHS]big_ord_recl.
rewrite (@le_lt_trans _ _ (\prod_(i < n) v_ n.*2 i)) //; last first.
  rewrite v_prod // (_ : _ / _%:R = 2%:R * (n.*2.+1)%:R / n.+2%:R); last first.
    rewrite -doubleS natrM -muln2 (natrM _ _ 2) natrM invrM ?unitfE ?pnatr_eq0 //.
    rewrite mulrCA 3!mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r; congr (_ * _).
  rewrite ltr_pdivr_mulr // (_ : 4 = 2 * 2)%nat // (natrM _ 2) -mulrA ltr_pmul2l //.
  by rewrite -natrM mul2n ltr_nat doubleS 2!ltnS -2!muln2 leq_mul2r /=.
apply ler_prod => i _; apply/andP; split.
  apply divr_ge0; last exact/ler0n.
  by rewrite [X in _ <= _ + X](_ : _ = 1%:R) // -natrD ler0n.
apply: (@le_trans _ _ (v_ n.*2 (@ord0 n))).
  rewrite /v_ subn0 addn2 -doubleS.
  rewrite -2!muln2 2!natrM invrM // ?unitfE //; last first.
    by rewrite pnatr_eq0 -lt0n.
  rewrite -mulrA (mulrA 2) divrr ?unitfE // div1r.
  by rewrite [X in (_ + X) / _ <= _](_ : _ = 1%:R) // -natrD addn1.
destruct i as [i i0] => /=; exact/v_increasing_ler.
Qed.

End e_seq_is_bounded_by_4.

Section e_seq_increasing.

Let sum_group_by_2 n (f : nat -> R) :
  \sum_(i < n) f i = \sum_(i < n./2) (f i.*2 + f i.*2.+1) + if
  odd n.+1 then 0 else f n.-1.
Proof.
elim: n.+1 {-2}n (ltnSn n) => {n} // m ih [_|n].
  by rewrite 2!big_ord0 /= addr0.
rewrite ltnS => nm.
rewrite big_ord_recr /= ih // negbK; case: ifPn => /= [|].
  by move/negbTE => no; rewrite no addr0 uphalf_half no add0n.
rewrite negbK => no.
rewrite no uphalf_half no add1n addr0 big_ord_recr /= -!addrA; congr (_ + _).
move: (odd_double_half n); rewrite no add1n => nE.
by rewrite nE -{1}nE.
Qed.

Lemma increasing_e_seq : forall n, e_seq n < e_seq n.+1.
Proof.
case=> [|n]; first by rewrite e_seq0 e_seq1 {1}(_ : 1 = 1%:R) // ltr_nat /e_seq.
rewrite -(@ltr_pmul2l _ (((n.+2%:R - 1) / n.+2%:R) ^+ n.+2)); last first.
  apply/exprn_gt0/divr_gt0; last by rewrite ltr0n.
  by rewrite subr_gt0 {1}(_ : 1 = 1%:R) // ltr_nat.
rewrite [X in X < _](_ : _ = (n.+2%:R - 1) / n.+2%:R); last first.
  rewrite {1}/e_seq exprS -[RHS]mulr1 -3!mulrA; congr (_ * _).
  rewrite -mulrA; congr (_ * _).
  rewrite (_ : _ / n.+2%:R = (1 + 1 / n.+1%:R) ^-1); last first.
    rewrite -{4}(@divrr _ n.+1%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
    by rewrite invf_div {2 6}(_ : 1 = 1%:R) // -natrD -natrB // subn1 addn1.
  by rewrite exprVn mulVr // unitfE expf_eq0 /= paddr_eq0 //= oner_eq0.
rewrite [X in _ < X](_ : _ = ((n.+2%:R ^+ 2 - 1) / n.+2%:R ^+ 2) ^+ n.+2); last first.
  rewrite /e_seq.
  rewrite -{4}(@divrr _ n.+2%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
  rewrite -exprMn_comm; last by rewrite /GRing.comm mulrC.
  congr (_ ^+ _); rewrite mulrACA -subr_sqr expr1n; congr (_ * _).
  by rewrite -invrM // unitfE pnatr_eq0.
rewrite mulrBl divrr ?unitfE ?pnatr_eq0 // mulrBl divrr ?unitfE ?expf_eq0 /= ?pnatr_eq0 //.
rewrite exprBn_comm; last by rewrite /GRing.comm mulrC.
rewrite big_ord_recl 2!expr0 expr1n bin0 mulr1n 2![in X in _ < X]mul1r.
rewrite big_ord_recl 2!expr1 expr1n bin1 [in X in _ < X]mul1r mulN1r.
rewrite (_ : -1 / _ *+ _ = -1 / n.+2%:R); last first.
  rewrite 2!mulN1r mulNrn; congr (- _).
  rewrite expr2 invrM ?unitfE ?pnatr_eq0 //.
  rewrite -mulrnAr -[RHS]mulr1; congr (_ * _).
  by rewrite -mulr_natl divrr // unitfE pnatr_eq0.
rewrite addrA mulN1r div1r -ltr_subl_addl subrr.
pose F : 'I_n.+1 -> R :=
  fun i => (-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2).
rewrite (eq_bigr F); last first.
  by move=> i _; congr (_ *+ _); rewrite /= expr1n mulr1.
rewrite (sum_group_by_2 n.+1 (fun i => ((-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2)))).
destruct n as [|n'].
  by rewrite /= big_ord0 add0r -signr_odd /= expr0 mul1r.
set n := n'.+1.
set G := BIG_F.
have G_gt0 : forall i, 0 < G i.
  move=> /= i; rewrite /G.
  rewrite -signr_odd /= negbK odd_double expr0 mul1r.
  rewrite -signr_odd /= negbK odd_double /= expr1 mulN1r.
  rewrite mulNrn (@exprSr _ _ i.*2.+2) -mulrnAr -mulr_natr -mulrBr mulr_gt0 // ?exprn_gt0 //.
  rewrite subr_gt0 -mulr_natr ltr_pdivr_mull // -natrX -natrM.
  move: (@mul_bin_left n.+2 i.*2.+2).
  move/(congr1 (fun x => x%:R : R)).
  move/(congr1 (fun x => (i.*2.+3)%:R^-1 * x)).
  rewrite natrM mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r => ->.
  rewrite 2!natrM mulrA.
  have ? : (i.*2.+1 < n.+2)%nat.
    move: (ltn_ord i).
    rewrite 3!ltnS -(@leq_pmul2r 2) // !muln2 => /leq_trans; apply.
    case/boolP : (odd n') => on'.
      move: (odd_geq n' on'); rewrite leqnn => /esym.
      by move/leq_trans; apply; rewrite leqnSn.
    by move: (@odd_geq n' n on') => <-; rewrite leqnSn.
  rewrite ltr_pmul2r ?ltr0n ?bin_gt0 // ltr_pdivr_mull // -natrM ltr_nat.
  rewrite -(@ltn_add2r i.*2.+2) subnK // ltn_addr // -{1}(mul1n n.+2) -mulnn.
  by rewrite  mulnA ltn_mul2r /= mulSn addSn ltnS addSn.
have sum_G_gt0 : 0 < \big[+%R/0]_i G i.
  rewrite {1}(_ : 0 = \big[+%R/0]_(i < n.+1./2) 0); last by rewrite big1.
  apply: (@lt_leif _ _ _ _ false).
  rewrite (_ : false = [forall i : 'I_n.+1./2, false]); last first.
    apply/idP/forallP => //=; apply; exact: (@Ordinal _ 0).
  apply: leif_sum => i _; exact/leifP/G_gt0.
case: ifPn => no; first by rewrite addr0.
rewrite addr_gt0 //= -signr_odd (negbTE no) expr0 mul1r.
by rewrite pmulrn_lgt0 ?bin_gt0 // exprn_gt0.
Qed.

End e_seq_increasing.

Lemma cvg_e_seq : cvg e_seq.
Proof.
apply increasing_has_ub_cvg.
  by move=> n; exact/ltW/increasing_e_seq.
apply/has_ubP/nonemptyP; exists 4%:R; rewrite inE; apply/forallbP => /= x.
rewrite inE; apply/implyP => /asboolP[n _ <-{x}].
case: n.
by rewrite e_seq0 {1}(_ : 1 = 1%:R) // ler_nat.
by move=> n; apply/ltW/e_seq_bound.
Qed.

Lemma lim_e_seq_lb : 2 < lim e_seq.
Proof.
apply: (@lt_le_trans _ _ (e_seq 2%nat)).
  by rewrite e_seq2 ltr_pdivl_mulr // -natrM ltr_nat.
pose u_ : (R^o) ^nat := fun n => e_seq 2%nat.
rewrite (_ : e_seq _ = lim u_) //; last first.
  by apply/esym; apply: (@flim_map_lim _ [normedModType R of R^o]); apply: cst_continuous.
apply (@lim_ler [realFieldType of R] _ _ 2%nat); last 2 first.
  exact/cvg_cst.
  exact/cvg_e_seq.
move=> i; rewrite /u_.
apply increasing_ler => ?.
exact/ltW/increasing_e_seq.
Qed.

Definition exp_base : R := lim e_seq.

Lemma exp_base0 : 0 < exp_base.
Proof. by rewrite (lt_trans _ lim_e_seq_lb). Qed.

Lemma exp_base1 : exp_base != 1.
Proof. by rewrite eq_sym lt_eqF // (lt_trans _ lim_e_seq_lb) // ltr1n. Qed.

End exp_base.

(* wip *)
Definition exp_n (x : R) : R^o ^nat := fun n => x ^+ n / n`!%:R.

Lemma exp_n_bound (x : R) : 0 < x -> exp_n x --> (0 : R^o).
Proof.
move=> x0.
apply: flim_normW => _/posnumP[r].
rewrite near_map.
near=> n.
rewrite distrC subr0.
set p' := floor (10%:R * x).
set p := `|Rtoint p'|%nat.
rewrite (@le_trans _ _ (10%:R ^+ p *exp_n x p / 10%:R ^+ n)) //.
Abort.

(* TODO: prove existence *)
Axiom pow_fun : forall a : R, R -> R.
Local Notation "a `^ x" := (pow_fun a x).
Axiom pow_fun1 : pow_fun 1 = fun=> 1.
Axiom pow_fun_gt0 : forall a : R, 0 < a -> (forall x, 0 < a `^ x).
Axiom pow_fun_morph : forall a : R, 0 < a -> {morph pow_fun a : x y / x + y >-> x * y}.
Axiom pow_funa0 : forall a : R, 0 < a -> a `^ 0 = 1.
Axiom pow_funa1 : forall a : R, 0 < a -> a `^ 1 = a.
Axiom pow_fun_homo_leq : forall a : R, 1 < a -> {homo pow_fun a : x y / x <= y}.
Axiom pow_fun_homo_geq : forall a : R, 0 < a -> a < 1 -> {homo pow_fun a : x y / x >= y}.

Lemma pow_fun_inv (a : R) : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -{1}(pow_funa1 a0) -pow_fun_morph // subrr pow_funa0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma pow_fun_mulrn (a : R) (n : nat) : 0 < a -> pow_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 pow_funa0.
by rewrite -addn1 natrD pow_fun_morph // exprD ih pow_funa1.
Qed.

Definition exp_fun : R -> R := pow_fun exp_base.

Definition riemann_seq (a : R) : R^o ^nat := fun n => (n.+1%:R `^ a)^-1.

Lemma riemann_seq_gt0 a i : 0 < a -> 0 < riemann_seq a i.
Proof. move=> ?; by rewrite /riemann_seq invr_gt0 pow_fun_gt0. Qed.

End sequences_examples.

Notation "a `^ x" := (pow_fun a x) : sequences_scope.

Section R_dense.

(* TODO: move? *)
Lemma ratr_fracq (G : realType) (p : int) (q : nat) :
  (p + 1)%:~R / q.+1%:~R = @ratr [unitRingType of G] ((p + 1)%:Q / q.+1%:Q).
Proof. by rewrite rmorph_div /= ?ratr_int // unitfE. Qed.

(* sequence in Q.a that converges to x \in R *)
Section rat_approx_R.

Variables (G : archiFieldType) (a x : G) (m : int).

Fixpoint seq_Q (n : nat) : rat :=
  if n is n'.+1 then
    if x - ratr (seq_Q n') * a < ratr (1%:Q / (2^n'.+1)%:Q) * a then
      seq_Q n'
    else if x - ratr (seq_Q n') * a > ratr (1%:Q / (2^n'.+1)%:Q) * a then
           seq_Q n' + 1%:Q / (2^n'.+1)%:Q
         else
           0 (* should not happen *)
  else m%:~R.

Hypothesis a0 : 0 < a.

Lemma increasing_seq_Q : (forall q : rat, x != ratr q * a) ->
   increasing seq_Q.
Proof.
move=> xa n /=; case: ifPn => //; rewrite -leNgt le_eqVlt => /orP[/eqP abs|->].
  exfalso; move/eqP : abs; apply/negP.
  rewrite eq_sym subr_eq -mulrDl -rmorphD /=; exact: xa.
by rewrite ler_addl mulr_ge0 // ltW // invr_gt0 // ltr0z exprn_gt0.
Qed.

Hypothesis xma : x < (m + 1)%:~R * a.

Lemma seq_QP : (forall q : rat, x != ratr q * a) ->
   forall n, x - ratr (seq_Q n) * a < ratr (1%:Q / (2^n)%:Q) * a.
Proof.
move=> xqa; elim => [|n ih] /=.
  by rewrite expr0z divr1 ltr_subl_addr -mulrDl 2!ratr_int -intrD addrC.
case: ifPn => [//|].
rewrite -leNgt le_eqVlt => /orP[abs|H1].
  exfalso; move: abs; apply/negP.
  rewrite eq_sym subr_eq -mulrDl -rmorphD /=; exact: xqa.
rewrite H1 rmorphD /= mulrDl opprD addrA ltr_sub_addr -mulrDl -rmorphD.
rewrite -mulrDl /= -intrD exprSz intrM invrM; last 2 first.
  by rewrite unitfE intr_eq0.
  by rewrite unitfE intr_eq0 expf_neq0.
rewrite mulrCA divrr ?unitfE ?intr_eq0 // mulr1.
by rewrite div1r in ih.
Qed.

Hypothesis max : m%:~R * a <= x.

Lemma seq_Q_ub : (forall q : rat, x != ratr q * a) ->
   forall n, ratr (seq_Q n) * a <= x.
Proof.
move=> xa; elim => [|n unx].
  by rewrite /= ratr_int.
move: (seq_QP xa) => H /=.
case: ifPn => //.
rewrite -leNgt le_eqVlt => /orP[abs|K].
- exfalso.
  move: abs; apply/negP.
  by rewrite eq_sym subr_eq -mulrDl -rmorphD /= xa.
- by rewrite K rmorphD /= mulrDl -lter_sub_addl ltW.
Qed.

End rat_approx_R.

Section rat_approx_R2.
Variables (R : realType) (a x : R) (m : int).

Hypothesis a0 : 0 < a.
Hypothesis xma : x < (m + 1)%:~R * a.
Hypothesis max : m%:~R * a <= x.

Lemma cvg_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  cvg (fun n : nat => ratr (seq_Q a x m n) : R^o).
Proof.
apply: (proj1 (@increasing_upper_bound_cvg _ _ (x / a) _ _)).
by move=> n; rewrite ler_rat; apply: increasing_seq_Q.
by move=> n; rewrite ler_pdivl_mulr //; apply seq_Q_ub => //; exact/ltrW.
Qed.

Lemma approach_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  (fun n : nat => ratr (seq_Q a x m n) * a : R^o) --> (x:R^o).
Proof.
apply/(@flim_normP _ [normedModType R of R^o]) => e e0.
rewrite near_map; near=> n.
move: (seq_Q_ub xma max xa n) => H1.
rewrite [X in X < _](_ : _ = `|x - ratr (seq_Q a x m n) * a|%R) // ger0_norm // ?subr_ge0 //.
move: (seq_QP xma xa) => H.
rewrite (lt_le_trans (H _)) // -ler_pdivl_mulr // ltW //.
rewrite [X in X < _](_ : _ = `| (0 - ratr (1%:Q / (2 ^ n)%:Q)) : R^o |); last first.
  rewrite distrC subr0 [RHS](_ : _ = `|ratr (1%:~R / (2 ^ n)%:~R)|%R) //.
  by rewrite ger0_norm // ler0q divr_ge0 // ler0z // -exprnP exprn_ge0.
near: n.
have K : geometric_seq_half R --> (0 : R^o) by apply approach_geometric_seq_half.
have ea0 : 0 < e / a by rewrite divr_gt0.
by move/flim_normP : K => /(_ _ ea0) /=; rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

Lemma start_x : (forall q : rat, x != ratr q * a) ->
  {m : int | m%:~R * a < x < (m + 1)%:~R * a}.
Proof.
move=> xa; exists (ifloor (x / a)); apply/andP; split; last first.
   by rewrite -ltr_pdivr_mulr // intrD -floorE floorS_gtr.
rewrite -ltr_pdivl_mulr // lt_neqAle -{2}floorE floor_ler andbT.
apply/negP => /eqP H.
move: (xa (ifloor (x / a))%:~R) => /negP; apply; apply/eqP.
by rewrite ratr_int H -mulrA mulVr ?mulr1 // unitfE gt_eqF.
Qed.

End rat_approx_R2.

Lemma R_dense_corollary (R : realType) (a x : R) (a0 : 0 < a) :
  {x_ : rat ^nat | increasing x_ /\ cvg (fun n => ratr (x_ n) : R^o) /\ lim (fun n => ratr (x_ n) * a : R^o) = x}.
Proof.
have [xa|xa] := pselect (forall q : rat, x != ratr q * a); last first.
  have [q xqa] : {q : rat | x = ratr q * a}.
    apply/cid/asboolP/negPn/negP => abs; apply xa => {xa} q.
    apply: contra abs => /eqP ->.
    by apply/asboolP; exists q.
  exists (fun=> q); split.
  by [].
  split.
  exact: (@cvg_cst _ [normedModType R of R^o]).
  rewrite xqa; exact: (@lim_cst_sequence _ [normedModType R of R^o]).
have [m /andP[max xma]] := start_x a0 xa.
set x0 := m%:~R * a; set x_ := seq_Q a x m; exists (seq_Q a x m).
split; first by move=> n; exact: increasing_seq_Q.
split; first by apply: cvg_seq_Q => //; rewrite addrC in xma => //; exact/ltW.
apply/(@flim_lim _ [normedModType R of R^o])/approach_seq_Q => //; exact/ltW.
Qed.

End R_dense.

Section cesaro.
Variable R : realType.

Definition average (u_ : R^o ^nat) : R^o ^nat :=
  fun n => n.+1%:R^-1 * (\sum_(i < n.+1) u_ i).

Definition cesaro_stmt (u_ : R^o ^nat) (l : R^o) :=
  cvg u_ -> lim u_ = l ->
  cvg (average u_) /\ lim (average u_) = l.

Lemma cesaro (u_ : R^o ^nat) l : cesaro_stmt u_ l.
Proof.
suff H : forall u_, cesaro_stmt u_ 0.
  move=> cu ul.
  pose u' : R^o ^nat := fun n => u_ n - l.
  have cu' : cvg u'.
    rewrite /u' (_ : (fun n : nat => _) = u_ - cst l) //.
    apply: cvg_add => //; rewrite cvg_opp; exact: cvg_cst.
  have u'l : lim u' = 0.
    rewrite /u' (@lim_add_sequence _ [normedModType R of R^o]) //; last by rewrite cvg_opp; exact: cvg_cst.
    rewrite lim_opp_sequence; last exact: cvg_cst.
    by rewrite lim_cst_sequence ul subrr.
  case: {H}(H _ cu' u'l) => ? H.
  have u'ul : average u' = average u_ - cst l.
    rewrite /average /u' funeqE => i.
    rewrite -[RHS]/(_ - _) big_split /= mulrDr; congr (_ + _).
    rewrite [in LHS](eq_bigr (fun j => (- l) * 1)); last by rewrite mulr1.
    rewrite -big_distrr /= mulrCA big_const card_ord -Monoid.iteropE.
    by rewrite -/(_ %:R) mulVr ?mulr1 // unitfE pnatr_eq0.
  move/eqP : (u'ul); rewrite -subr_eq opprK => /eqP <-.
  split.
  - apply (@cvg_add _ [normedModType R of R^o]) => //; exact: cvg_cst.
  - rewrite (@lim_add_sequence _ [normedModType R of R^o]) //; last exact: cvg_cst.
    by rewrite lim_cst_sequence H add0r.
move=> {u_ l}u_ cu lu.
have cesaro_split : forall n M, (M <= n)%nat ->
  `|n.+1%:R^-1 * \big[+%R/0]_(i < n.+1) u_ i| <=
    n.+1%:R^-1 * `|\big[+%R/0]_(i < M.+1) u_ i| +
    n.+1%:R^-1 * `|\big[+%R/0]_(M.+1 <= i < n.+1) u_ i|.
  move=> n M; rewrite -ltnS => Mn.
  rewrite (bigID (fun i : 'I_n.+1 => (i <= M)%nat)) /= mulrDr.
  rewrite (eq_bigl (fun i : 'I_n.+1 => (i < M.+1)%nat)) // -big_ord_widen //.
  rewrite (le_trans (ler_norm_add _ _)) // ler_add //.
    by rewrite normrM ler_wpmul2r // ger0_norm.
  rewrite normrM ger0_norm // ler_wpmul2l //.
  rewrite (eq_bigl (fun i : 'I__ => (M < i)%nat)); last first.
    by move=> ?; rewrite ltnNge.
  rewrite -big_mkord -{1}(subnKC Mn).
  rewrite {1}/index_iota subn0 iota_add big_cat -!/(index_iota _ _) add0n.
  rewrite -/(index_iota 0 M.+1) /= big_mkord (eq_bigr (fun=> 0)); last first.
    move=> /= i Mi; move: (ltn_ord i); rewrite ltnS => /(leq_trans Mi).
    by rewrite ltnn.
  rewrite big1 // add0r le_eqVlt; apply/orP; left; apply/eqP; congr (`|_|).
  rewrite [in RHS]big_nat_cond /= [in LHS]big_nat_cond /=; apply eq_bigl => i.
  by rewrite andbAC andbb andbT.
suff K : average u_ @ \oo --> (0 : R^o).
  by split; [apply/cvg_ex; exists 0 | exact/flim_lim].
have {cu lu}u0 : u_ @ \oo --> (0 : R^o).
  case/cvg_ex : (cu) => /= x Hx.
  by have <- : x = 0 by move/flim_lim : Hx; rewrite lu.
apply/flim_normP => e e0; rewrite near_simpl.
near \oo => M.
near=> n.
have Mn : (M <= n)%nat.
  by near: n; rewrite nearE /locally /= /eventually; exists M.
rewrite distrC subr0.
rewrite (le_lt_trans (cesaro_split _ _ Mn)) // (splitr e) ltr_add //.
- near: n.
  case/boolP : (`|\big[+%R/0]_(i < M.+1) u_ i| == 0) => [/eqP ->|H0].
    by near=> n; rewrite mulr0 // divr_gt0.
  have {H0}H1 : 0 < `|\big[+%R/0]_(i < M.+1) u_ i|.
    by rewrite lt_neqAle eq_sym H0 /= normr_ge0.
  have H2 : 0 < e / `|\big[+%R/0]_(i < M.+1) u_ i| / 2.
    by rewrite divr_gt0 // divr_gt0.
  move/flim_norm : (@approach_harmonic_seq R) => /(_ _ H2).
  rewrite !near_simpl => H3.
  near=> n.
  rewrite -ltr_pdivl_mulr // mulrAC -[X in X < _]ger0_norm //.
  by rewrite -[X in `|X|%R]subr0 distrC; near: n.
- rewrite (@le_lt_trans _ _ (n.+1%:R^-1 * (n - M)%:R * (e / 2))) //; last first.
    rewrite -[X in _ < X](mul1r (e / 2)) ltr_pmul2r // ?divr_gt0 //.
    by rewrite lter_pdivr_mull // mulr1 ltr_nat ltnS leq_subLR leq_addl.
  rewrite -mulrA ler_wpmul2l // (le_trans (ler_norm_sum _ _ _)) //.
  rewrite (@le_trans _ _ (\big[+%R/0]_(M.+1 <= i < n.+1) (e / 2))) //; last first.
    rewrite big_const_nat subSS le_eqVlt; apply/orP; left.
    elim : (n - M)%nat => /= [|k IH]; first by rewrite mul0r.
    by rewrite -(addn1 k) natrD mulrDl (eqP IH) mul1r addrC.
  rewrite big_nat_cond [in X in _ <= X]big_nat_cond; apply ler_sum.
  move=> i; rewrite andbT => /andP[Mi _]; apply ltW; move: i Mi.
  near: M.
  have : \forall x \near \oo, `|u_ x| < e / 2.
    near=> x; rewrite -(subr0 (u_ x)) distrC; near: x.
    move/flim_normP : u0; apply; by rewrite divr_gt0.
  rewrite nearE => -[j _ Hj] /=.
  rewrite nearE; exists j => // k Hk i ki.
  by rewrite Hj // (leq_trans Hk) // ltnW.
Grab Existential Variables. all: end_near. Qed.

End cesaro.

(* sequences of partial sums *)
Section partial_sum.
Variables (K : numDomainType) (V : normedModType K) (u_ : V ^nat).

Definition psum : V ^nat := fun n => \sum_(k < n) (u_ k).

Lemma psumD (n : nat) : u_ n = psum n.+1 - psum n.
Proof. by rewrite /psum big_ord_recr /= addrAC subrr add0r. Qed.

End partial_sum.

Section series_convergence.

Definition psum_cvg (K : numDomainType) (V : normedModType K) (u_ : V ^nat) :=
  cvg (psum u_).

Lemma psum_cvg_cvg (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  psum_cvg u_ -> lim u_ = 0.
Proof.
move=> psum_cvg; apply/flim_lim; rewrite (_ : u_ = fun n => psum u_ (n + 1)%nat - psum u_ n); last first.
  rewrite funeqE => i; rewrite addn1; exact: psumD.
rewrite -(subrr (lim (psum u_))).
apply: (@lim_add _ _ nat_topologicalType) => //.
exact: approach_addn.
exact: (@lim_opp _ _ nat_topologicalType).
Qed.

(* absolute convergence *)
Definition acvg (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :=
  @psum_cvg _ [normedModType K of K^o ] (fun n => `| u_ n |).

Lemma increasing_psum (R : numFieldType) (u_ : R^o ^nat) : (forall n, 0 <= u_ n) ->
  increasing (psum u_).
Proof. by move=> u0 n; rewrite {2}/psum big_ord_recr /= ler_addl. Qed.

End series_convergence.

Section series_R.
Variable R : realType.

Lemma psum_ler (u_ v_ : R^o ^nat) : (forall n, 0 <= u_ n) -> (forall n, 0 <= v_ n) ->
  (forall n, u_ n <= v_ n) ->
  psum_cvg v_ -> psum_cvg u_.
Proof.
move=> u0 v0 uv.
have UV n : psum u_ n <= psum v_ n by apply ler_sum => *; exact: uv.
move/cvg_has_ub => /nonemptyP[M] /ubP vub.
have : has_ub (in_set [set psum u_ n | n in setT]).
  apply/has_ubP/nonemptyP; exists M; apply/ubP => x.
  rewrite inE => /asboolP[y _ <-{x}].
  rewrite (@le_trans _ _ (psum v_ y)) // vub // inE.
  apply/asboolP; exists y => //.
  rewrite [LHS]ger0_norm //; by apply sumr_ge0 => *; exact/v0.
by case/(increasing_has_ub_cvg (increasing_psum u0)).
Qed.

Lemma psum_cvg_cauchy (u_ : R^o ^nat) : psum_cvg u_ <->
  forall e : {posnum R}, \forall n \near (\oo, \oo), (n.1 < n.2)%nat ->
                 `| \sum_(n.1 <= k < n.2) u_ k | < e%:num.
Proof.
split=> [/cvg_cauchy_seq|H].
- rewrite /cauchy_seq => H e; near=> np => Hnp.
  rewrite -[X in `| X |](addrK (\big[+%R/0]_(i < np.1) u_ i)).
  rewrite [in X in `| X - _  |]addrC -{1}(big_mkord xpredT).
  rewrite -big_cat -{2}(add0n np.1) /index_iota subn0.
  rewrite {2}(add0n np.1) -iota_add subnKC; last exact: ltnW.
  rewrite -(subn0 np.2) (@big_mkord _ _ _ np.2 xpredT) distrC {Hnp}.
  near: np; exact: H.
- apply/cauchy_seq_cvg => e; near=> np.
  have [Hnp|] := boolP (np.1 < np.2)%nat.
  + rewrite distrC /psum -2!(big_mkord xpredT) -{1}(subnKC (ltnW Hnp)).
    rewrite {1}/index_iota subn0 iota_add big_cat add0n addrAC -{1}(subn0 np.1) subrr add0r.
    move: Hnp; near: np; exact: H.
  + rewrite -leqNgt leq_eqVlt => -/orP[/eqP ->|Hnp].
      by rewrite subrr normr0.
    rewrite distrC /psum -[X in `|_ - X|](big_mkord xpredT).
    rewrite -{1}(subnKC (ltnW Hnp)) /index_iota subn0 iota_add big_cat add0n.
    rewrite -(big_mkord xpredT) -[X in `|X - _|]add0r -{2}(subn0 np.2) addrKA sub0r normrN.
    move: Hnp; near: np; move: (H e).
    by rewrite -(near2_curry _ _ (fun b => fun a => (b < a)%N ->
      `|\sum_(i <- iota b (a - b)) u_ i| < e%:num)) near_swap near2_curry.
Grab Existential Variables. all: end_near. Qed.

Lemma acvg_cvg (u_ : R^o ^nat) : acvg u_ -> psum_cvg u_.
Proof.
move/psum_cvg_cauchy => H; apply/cauchy_seq_cvg => e; near=> np.
- have [Hnp|] := boolP (np.2 < np.1)%nat.
  + rewrite /psum -(big_mkord xpredT) -{1}(subnKC (ltnW Hnp)) /index_iota subn0.
    rewrite iota_add big_cat /= add0n addrAC -{1}(subn0 np.2).
    rewrite -(big_mkord xpredT) subrr add0r (le_lt_trans (ler_norm_sum _ _ _)) //.
    rewrite -[X in X < _](@ger0_norm _ _); last first.
      exact: (sumr_ge0 _ (fun i => fun=> normr_ge0 (u_ i))).
    move: Hnp; near: np; move: (H e).
    rewrite -(near2_curry _ _ (fun a => fun b => (a < b)%N ->
      `|\big[+%R/0]_(a <= k < b) `|u_ k| | < e%:num)) near_swap near2_curry.
    exact.
  + rewrite -leqNgt leq_eqVlt => /orP[/eqP <-|Hnp].
      by rewrite subrr normr0.
    rewrite /psum -[X in _ - X](big_mkord xpredT) /index_iota subn0.
    rewrite -(subnKC (ltnW Hnp)) iota_add big_cat add0n.
    rewrite -(big_mkord xpredT) -[X in `| X - _ |]add0r.
    rewrite -{2}(subn0 np.1) addrKA sub0r normrN.
    rewrite (le_lt_trans (ler_norm_sum _ _ _)) //.
    rewrite -[X in X < _](@ger0_norm _ _); last first.
      exact: (sumr_ge0 _ (fun i => fun=> normr_ge0 (u_ i))).
    by move: Hnp; near: np; move: (H e).
Grab Existential Variables. all: end_near. Qed.

End series_R.

Section series_examples.
Variable R : realType.

Lemma harmonic_dvg : ~ psum_cvg (harmonic_seq R).
Proof.
have psum_harmonic n : psum (harmonic_seq R) n.*2 - psum (harmonic_seq R) n =
         \big[+%R/0]_(n <= i < n.*2) harmonic_seq R i.
  rewrite /psum -(@subnKC n n.*2); last by rewrite -addnn leq_addr.
  rewrite -(big_mkord xpredT) {1}/index_iota subn0 iota_add big_cat /=.
  rewrite addrAC -(big_mkord xpredT) -{1}(subn0 n) subrr add0r add0n.
  by rewrite /index_iota subnKC // -addnn leq_addr.
have H : forall n, (0 < n)%nat -> 2^-1 <= psum (harmonic_seq R) n.*2 - psum (harmonic_seq R) n.
  move=> n n0.
  rewrite psum_harmonic.
  rewrite (@le_trans _ _ (\sum_(n <= i < n.*2) n.*2%:R^-1)) //; last first.
    rewrite -/(index_iota _ _) big_seq_cond [in X in _ <= X]big_seq_cond.
    apply ler_sum => i; rewrite andbT mem_iota subnKC; last first.
      by rewrite -addnn leq_addr.
    move/andP => [ni ni2].
    rewrite /harmonic_seq -(mulr1 i.+1%:R^-1) ler_pdivl_mull ?ltr0n //.
    by rewrite ler_pdivr_mulr ?mul1r ?ler_nat // ltr0n (leq_ltn_trans _ ni2).
  rewrite (eq_bigr (fun=> n.*2%:R^-1 * 1)); last by move=> *; rewrite mulr1.
  rewrite -big_distrr /= big_const_nat -{2}(addnn n) addnK.
  rewrite (_ : iter _ _ _ = n%:R); last first.
    by elim: {n0} n => // n ih /=; rewrite ih -add1n natrD.
  rewrite -muln2 natrM invrM ?unitfE // ?pnatr_eq0 -?lt0n //.
  by rewrite -mulrA mulVr ?mulr1 // unitfE pnatr_eq0 -lt0n.
move/psum_cvg_cauchy => /(_ 2^-1%:pos)/filter2P -[[A B] /= [[a _ aA] [b _ bB]]].
have Aab : A (maxn a b).+1 by apply aA; rewrite ltnW // ltnS leq_maxl.
have Bab : B (maxn a b).+1.*2.
  by apply bB; rewrite -addnn addSnnS (leq_trans _ (leq_addr _ _)) // leq_maxr.
have ab : ((maxn a b).+1 < (maxn a b).+1.*2)%nat.
  by rewrite -addnn addSn ltnS addnS ltnS leq_addr.
move/(_ _ _ Aab Bab ab); apply/negP.
rewrite -leNgt [X in _ <= X]ger0_norm; last first.
  by apply sumr_ge0 => i _; exact: harmonic_seq_ge0.
move: (H (maxn a b).+1); rewrite psum_harmonic; exact.
Qed.

Lemma riemann_dvg (a : R): 0 < a <= 1 -> ~ psum_cvg (riemann_seq a).
Proof.
case/andP => a0; rewrite le_eqVlt => /orP[/eqP ->|a1].
  rewrite (_ : riemann_seq 1 = harmonic_seq R); first exact: harmonic_dvg.
  by rewrite funeqE => i; rewrite /riemann_seq pow_funa1.
have : forall n, harmonic_seq R n <= riemann_seq a n.
  rewrite /harmonic_seq /riemann_seq.
  case=> [|n]; first by rewrite pow_fun1 invr1.
  rewrite -[X in _ <= X]div1r ler_pdivl_mulr ?pow_fun_gt0 // mulrC.
  rewrite ler_pdivr_mulr // mul1r -[X in _ <= X]pow_funa1 //.
  by rewrite (pow_fun_homo_leq) // ?ltr1n // ltW.
move/(psum_ler (harmonic_seq_ge0 R) (fun i => ltW (riemann_seq_gt0 i a0))).
move/contrap; apply; exact: harmonic_dvg.
Qed.

End series_examples.
