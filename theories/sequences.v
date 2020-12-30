(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import bigop div ssralg ssrint ssrnum fintype order.
From mathcomp Require Import binomial matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau derive forms.

(******************************************************************************)
(*                Definitions and lemmas about sequences                      *)
(*                                                                            *)
(* The purpose of this file is to gather generic definitions and lemmas about *)
(* sequences. Since it is an early version, it is likely to undergo changes.  *)
(* Here follow sample definitions and lemmas to give an idea of contents.     *)
(* See file sequences_applications.v for small scale usage examples.          *)
(*                                                                            *)
(* Definitions:                                                               *)
(*           R ^nat == notation for sequences,                                *)
(*                     i.e., functions of type nat -> R                       *)
(*         harmonic == harmonic sequence                                      *)
(*       arithmetic == arithmetic sequence                                    *)
(*        geometric == geometric sequence                                     *)
(*        series u_ == the sequence of partial sums of u_                     *)
(* [sequence u_n]_n == the sequence of general element u_n                    *)
(*   [series u_n]_n == the series of general element u_n                      *)
(*       [normed S] == transforms a series S = [series u_n]_n in its          *)
(*                     normed series [series `|u_n|]_n]                       *)
(*                     (useful to represent absolute and normed convergence:  *)
(*                        cvg [norm S_n])                                     *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*                       squeeze == squeeze lemma                             *)
(*                 cvgNpinfty u_ == (- u_ --> +oo) = (u_ --> -oo).            *)
(*    nonincreasing_cvg_ge u_ == if u_ is nonincreasing and convergent then   *)
(*                                  forall n, lim u_ <= u_ n                  *)
(*    nondecreasing_cvg_le u_ == if u_ is nondecreasing and convergent then   *)
(*                                  forall n, lim u_ >= u_ n                  *)
(*       nondecreasing_cvg u_ == if u_ is nondecreasing and bounded then u_   *)
(*                                  is convergent and its limit is sup u_n    *)
(*       nonincreasing_cvg u_ == if u_ is nonincreasing u_ and bound by below *)
(*                                  then u_ is convergent                     *)
(*                      adjacent == adjacent sequences lemma                  *)
(*                        cesaro == Cesaro's lemma                            *)
(* Sections sequences_R_* contain properties of sequences of real numbers     *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import mc_1_10.Num.Theory. (* because 1.11.0+beta1 does have bugs! *)
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "R ^nat" (at level 0).
Reserved Notation "a `^ x" (at level 11).
Reserved Notation "[ 'sequence' E ]_ n"
  (at level 0, E at level 200, n ident, format "[ 'sequence'  E ]_ n").
Reserved Notation "[ 'series' E ]_ n"
  (at level 0, E at level 0, n ident, format "[ 'series'  E ]_ n").
Reserved Notation "[ 'normed' E ]"  (at level 0, format "[ 'normed'  E ]").

Definition sequence R := nat -> R.
Definition mk_sequence R f : sequence R := f.
Arguments mk_sequence R f /.
Notation "[ 'sequence' E ]_ n" := (mk_sequence (fun n => E)) : ring_scope.
Notation "R ^nat" := (sequence R) : type_scope.

Notation "'nondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_seq' f" := ({mono f : n m / (n <= m)%nat >-> (n >= m)%O})
  (at level 10).
(* TODO:  the "strict" versions with mono instead of homo should also have notations*)

Lemma nondecreasing_opp (T : numDomainType) (u_ : T ^nat) :
  nondecreasing_seq (- u_) = nonincreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite ler_opp2. Qed.

Lemma nonincreasing_opp (T : numDomainType) (u_ : T ^nat) :
  nonincreasing_seq (- u_) = nondecreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite ler_opp2. Qed.

Lemma decreasing_opp (T : numDomainType) (u_ : T ^nat) :
  decreasing_seq (- u_) = increasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du ler_opp2. Qed.

Lemma increasing_opp (T : numDomainType) (u_ : T ^nat) :
  increasing_seq (- u_) = decreasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du ler_opp2. Qed.

Lemma nondecreasing_seqP (T : numDomainType) (u_ : T ^nat) :
  (forall n, u_ n <= u_ n.+1) -> nondecreasing_seq u_.
Proof. exact: homo_leq le_trans. Qed.

Lemma nonincreasing_seqP (T : numDomainType) (u_ : T ^nat) :
  (forall n, u_ n >= u_ n.+1) -> nonincreasing_seq u_.
Proof. by apply: homo_leq (fun _ _ _ u v => le_trans v u). Qed.

Lemma increasing_seqP (T : numDomainType) (u_ : T ^nat) :
  (forall n, u_ n < u_ n.+1) -> increasing_seq u_.
Proof. by move=> u_nondec; apply: lenr_mono; apply: homo_ltn lt_trans _. Qed.

Lemma decreasing_seqP (T : numDomainType) (u_ : T ^nat) :
  (forall n, u_ n > u_ n.+1) -> decreasing_seq u_.
Proof.
move=> u_noninc;
(* FIXME: add shortcut to order.v *)
apply: (@total_homo_mono _ _ _ leq ltn ger gtr leqnn (@lerr _)
  ltn_neqAle _ (fun _ _ _ => esym (ler_anti _)) leq_total
  (homo_ltn (fun _ _ _ u v => lt_trans v u) _)) => //.
by move=> x y; rewrite /= lt_neqAle eq_sym.
Qed.
(* TODO (maybe): variants for near \oo ?? *)

Local Notation eqolimn := (@eqolim _ _ _ eventually_filter).
Local Notation eqolimPn := (@eqolimP _ _ _ eventually_filter).

Section sequences_patched.
(* TODO: generalizations to numDomainType *)

Section NatShift.

Variables (N : nat) (V : topologicalType).
Implicit Types  (f : nat -> V) (u : V ^nat)  (l : V).

Lemma cvg_restrict f u_ l :
  ([sequence if (n <= N)%N then f n else u_ n]_n @ \oo --> l) =
  (u_ @ \oo --> l).
Proof.
rewrite propeqE; split; apply: cvg_trans; apply: near_eq_cvg;
by near=> n => /=; case: ifP => //; rewrite ltn_geF//; near: n.
Grab Existential Variables. all: end_near. Qed.

Lemma is_cvg_restrict f u_ :
  cvg ([sequence if (n <= N)%nat then f n else u_ n]_n @ \oo) =
  cvg (u_ @ \oo).
Proof.
by rewrite propeqE; split;
  [rewrite cvg_restrict|rewrite -(cvg_restrict f)] => /cvgP.
Qed.

Lemma cvg_centern u_ l : ([sequence u_ (n - N)%N]_n --> l) = (u_ --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; apply: cvg_subnr.
gen have cD : u_ l / u_ --> l -> (fun n => u_ (n + N)%N) --> l.
   by apply: cvg_comp; apply: cvg_addnr.
by move=> /cD /=; under [X in X --> l]funext => n do rewrite addnK.
Qed.

Lemma cvg_shiftn u_ l : ([sequence u_ (n + N)%N]_n --> l) = (u_ --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; apply: cvg_addnr.
rewrite -[X in X -> _]cvg_centern; apply: cvg_trans => /=.
by apply: near_eq_cvg; near=> n; rewrite subnK//; near: n; exists N.
Grab Existential Variables. all: end_near. Qed.

End NatShift.

Variables (V : topologicalType).

Lemma cvg_shiftS u_ (l : V) : ([sequence u_ n.+1]_n --> l) = (u_ --> l).
Proof.
suff -> : [sequence u_ n.+1]_n = [sequence u_(n + 1)%N]_n by rewrite cvg_shiftn.
by rewrite funeqE => n/=; rewrite addn1.
Qed.

End sequences_patched.

Section sequences_R_lemmas_realFieldType.
Variable R : realFieldType.

Lemma squeeze T (f g h : T -> R) (a : filter_on T) :
  (\forall x \near a, f x <= g x <= h x) -> forall (l : R),
  f @ a --> (l : R^o) -> h @ a --> (l : R^o) -> g @ a --> (l : R^o).
Proof.
have cvg_distRP := (@cvg_distP _ [normedModType R of R^o]).
move=> fgh l /cvg_distRP lfa /cvg_distRP lga; apply/cvg_distRP => _/posnumP[e].
rewrite near_map; apply: filterS3 fgh (lfa _ e) (lga _ e) => /= x /andP[fg gh].
rewrite ![`|l - _|]distrC; rewrite !ltr_distl => /andP[lf _] /andP[_ hl].
by rewrite (lt_le_trans lf)? (le_lt_trans gh).
Qed.

Lemma cvgPpinfty (u_ : R^o ^nat) :
  u_ --> +oo <-> forall A, A > 0 -> \forall n \near \oo, A <= u_ n.
Proof.
split => [u_cvg _/posnumP[A]|u_ge X [A [Ar AX]]].
  rewrite -(near_map u_ \oo (<=%R A%:num)).
  by apply: u_cvg; apply: nbhs_pinfty_ge.
rewrite !near_simpl [\near u_, X _](near_map u_ \oo); near=> x.
apply: AX; rewrite (@lt_le_trans _ _ ((maxr 0 A) +1)) //.
  by rewrite ltr_spaddr // le_maxr lexx orbT.
by near: x; apply: u_ge; rewrite ltr_spaddr // le_maxr lexx.
Grab Existential Variables. all: end_near. Qed.

Lemma cvgNpinfty (u_ : R^o ^nat) : (- u_ --> +oo) = (u_ --> -oo).
Proof.
rewrite propeqE; split => u_cvg P [/= l [l_real Pl]];
rewrite !near_simpl [\forall x \near _, P _](near_map _ \oo);
have [|/=n _]:= u_cvg (fun x => P (- x)); do ?by [exists n
  | exists (- l); split; rewrite ?rpredN// => x;
    rewrite (ltr_oppl, ltr_oppr); apply: Pl].
by under [X in _ `<=` X]funext do rewrite /= opprK; exists n.
Qed.

Lemma cvgNminfty (u_ : R^o ^nat) : (- u_ --> -oo) = (u_ --> +oo).
Proof. by rewrite -cvgNpinfty opprK. Qed.

Lemma cvgPminfty (u_ : R^o ^nat) :
  u_ --> -oo <-> forall A, A > 0 -> \forall n \near \oo, - A >= u_ n.
Proof.
rewrite -cvgNpinfty; rewrite cvgPpinfty.
by split => uA A A_gt0; near=> n; rewrite ler_oppr; near: n; apply: uA.
Grab Existential Variables. all: end_near. Qed.

Lemma ger_cvg_pinfty (u_ v_ : R^o ^nat) : (\forall n \near \oo, u_ n <= v_ n) ->
  u_ --> +oo -> v_ --> +oo.
Proof.
move=> uv /cvgPpinfty ucvg; apply/cvgPpinfty => _/posnumP[A].
by apply: filterS2 (ucvg _ A) uv => x; apply: le_trans.
Qed.

Lemma ler_cvg_minfty (v_ u_ : R^o ^nat) : (\forall n \near \oo, u_ n <= v_ n) ->
  v_ --> -oo -> u_ --> -oo.
Proof.
move=> uv /cvgPminfty ucvg; apply/cvgPminfty => _/posnumP[A].
by apply: filterS2 uv (ucvg _ A) => x; apply: le_trans.
Qed.

(* TODO: rewrite closed_cvg_loc with the right implicits to do elim *)
(*       and using `\forall x \near F, D (f x)` instead of F ...    *)
(* it should be renamed closed_cvg and replace closed_seq below     *)
Lemma closed_seq {V : topologicalType} (u_ : V ^nat) (A : V -> Prop) :
   (* BUG: elim does not see this as an elimination principle if A : set V *)
   closed A -> (\forall n \near \oo, A (u_ n)) ->
   forall l, u_ --> l -> A l.
Proof. by move=> A_closed u_A l /closed_cvg_loc; apply. Qed.
Arguments closed_seq {V}.

Lemma lim_ge x (u_ : R^o ^nat) : cvg u_ ->
  (\forall n \near \oo, x <= u_ n) -> x <= lim u_.
Proof. by move=> /closed_cvg_loc V ?; elim/V: _. Qed.

Lemma lim_le x (u_ : R^o ^nat) : cvg u_ ->
  (\forall n \near \oo, x >= u_ n) -> x >= lim u_.
Proof. by move=> /closed_cvg_loc V ?; elim/V: _. Qed.

Lemma ler_lim (u_ v_ : R^o ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof.
move=> uv cu cv; rewrite -subr_ge0 -(@limB _ [normedModType R of R^o])//.
apply: lim_ge; first exact: is_cvgB.
by apply: filterS cv => n; rewrite subr_ge0.
Qed.

Lemma nonincreasing_cvg_ge (u_ : R^o ^nat) : nonincreasing_seq u_ -> cvg u_ ->
  forall n, lim u_ <= u_ n.
Proof.
move=> du ul p; rewrite leNgt; apply/negP => up0.
move/cvg_distP : ul => /(_ `|u_ p - lim u_|%R).
rewrite {1}ltr0_norm ?subr_lt0 // opprB subr_gt0 => /(_ up0).
rewrite near_map => ul.
near \oo => N.
have /du uNp : (p <= N)%nat by near: N; rewrite nearE; exists p.
have : `|lim u_ - u_ N| >= `|u_ p - lim u_|%R.
 rewrite ltr0_norm // ?subr_lt0 // opprB distrC.
 rewrite (@le_trans _ _ (lim u_ - u_ N)) // ?ler_sub //.
 rewrite (_ : `| _ | = `|u_ N - lim u_|%R) // ler0_norm // ?opprB //.
 by rewrite subr_le0 (le_trans _ (ltW up0)).
rewrite leNgt => /negP; apply; by near: N.
Grab Existential Variables. all: end_near. Qed.

Lemma nondecreasing_cvg_le (u_ : R^o ^nat) : nondecreasing_seq u_ -> cvg u_ ->
  forall n, u_ n <= lim u_.
Proof.
move=> iu cu n; move: (@nonincreasing_cvg_ge (- u_)).
rewrite -nondecreasing_opp opprK => /(_ iu); rewrite is_cvgNE => /(_ cu n).
by rewrite (@limN _ [normedModType R of R^o]) // ler_oppl opprK.
Qed.

End sequences_R_lemmas_realFieldType.

Section partial_sum.
Variables (V : zmodType) (u_ : V ^nat).

Definition series : V ^nat := [sequence \sum_(k < n) u_ k]_n.
Definition telescope : V ^nat := [sequence u_ n.+1 - u_ n]_n.

Lemma seriesSr n : series n.+1 = series n + u_ n.
Proof. by rewrite /series/= big_ord_recr/=. Qed.

Lemma seriesS n : series n.+1 = u_ n + series n.
Proof. by rewrite addrC seriesSr. Qed.

Lemma seriesSB (n : nat) : series n.+1 - series n = u_ n.
Proof. by rewrite seriesS addrK. Qed.

Lemma seriesEord : series = [sequence \sum_(k < n) u_ k]_n.
Proof. by []. Qed.

Lemma seriesEnat : series = [sequence \sum_(0 <= k < n) u_ k]_n.
Proof. by rewrite funeqE => n /=; rewrite big_mkord. Qed.

Lemma series_addn m n : series (n + m)%N = series m + \sum_(m <= k < n + m) u_ k.
Proof. by rewrite seriesEnat/= -big_cat_nat// leq_addl. Qed.

Lemma sub_series_geq m n : (m <= n)%N ->
  series n - series m = \sum_(m <= k < n) u_ k.
Proof. by move=> /subnK<-; rewrite series_addn addrAC subrr add0r. Qed.

Lemma sub_series m n :
  series n - series m = if (m <= n)%N then \sum_(m <= k < n) u_ k
                        else - \sum_(n <= k < m) u_ k.
Proof. by have [mn|/ltnW mn] := leqP m n; rewrite -sub_series_geq// opprB. Qed.

Lemma sub_double_series n : series n.*2 - series n = \sum_(n <= k < n.*2) u_ k.
Proof. by rewrite sub_series_geq// -addnn leq_addl. Qed.

End partial_sum.

Arguments series {V} u_ n : simpl never.
Arguments telescope {V} u_ n : simpl never.
Notation "[ 'series' E ]_ n" := (series [sequence E]_n) : ring_scope.

Lemma telescopeK (V : zmodType) (u_ : V ^nat) :
  series (telescope u_) = [sequence u_ n - u_ 0%N]_n.
Proof. by rewrite funeqE => n; rewrite seriesEnat/= telescope_sumr. Qed.

Lemma seriesK (V : zmodType) : cancel (@series V) telescope.
Proof. move=> ?; exact/funext/seriesSB. Qed.

Lemma eq_sum_telescope (V : zmodType) (u_ : V ^nat) n :
  u_ n = u_ 0%N + series (telescope u_) n.
Proof. by rewrite telescopeK/= addrC addrNK. Qed.

(* TODO: port to mathcomp *)
(* missing mathcomp lemmas *)
Lemma ler_sum_nat  (R : numDomainType) (m n : nat) (F G : nat -> R) :
  (forall i, (m <= i < n)%N -> (F i <= G i)%O) ->
  (\sum_(m <= i < n) F i <= \sum_(m <= i < n) G i)%O.
Proof.
move=> leFG; rewrite big_nat_cond [in X in _ <= X]big_nat_cond.
by rewrite ler_sum// => i; rewrite andbT => /leFG.
Qed.

Lemma sumr_const_nat (V : zmodType) (m n : nat) (x : V) :
   \sum_(n <= i < m) x = x *+ (m - n).
Proof. by rewrite big_const_nat; elim: (m - n)%N => //= k ->; rewrite mulrS. Qed.
(* end missing mathcomp lemmas *)

Section series_patched.

Variables (N : nat) (K : numFieldType) (V : normedModType K).
Implicit Types  (f : nat -> V) (u : V ^nat)  (l : V).

Lemma is_cvg_series_restrict u_ :
  cvg [sequence \sum_(N <= k < n) u_ k]_n = cvg (series u_).
Proof.
suff -> : (fun n => \sum_(N <= k < n) u_ k) =
          fun n => if (n <= N)%N then \sum_(N <= k < n) u_ k
                   else series u_ n - \sum_(0 <= k < N) u_ k.
  by rewrite is_cvg_restrict/= is_cvgDlE//; apply: is_cvg_cst.
rewrite funeqE => n; case: leqP => // ltNn; apply: (canRL (addrK _)).
by rewrite seriesEnat addrC -big_cat_nat// ltnW.
Qed.

End series_patched.

Section sequences_R_lemmas.
Variable R : realType.

Lemma cvg_has_ub (u_ : R^o ^nat) :
  cvg u_ -> has_ubound [set `|u_ n| | n in setT].
Proof.
move=> /cvg_seq_bounded/pinfty_ex_gt0[M M_gt0 /= uM].
by exists M; apply/ubP => x -[n _ <-{x}]; exact: uM.
Qed.

(* TODO: move *)
Lemma has_ub_image_norm (S : set R) : has_ubound (normr @` S) -> has_ubound S.
Proof.
case => M /ubP uM; exists `|M|; apply/ubP => r rS.
rewrite (le_trans (real_ler_norm _)) ?num_real //.
rewrite (le_trans (uM _ _)) ?real_ler_norm ?num_real //.
by exists r.
Qed.

Lemma cvg_has_sup (u_ : R^o ^nat) : cvg u_ -> has_sup (u_ @` setT).
Proof.
move/cvg_has_ub; rewrite -/(_ @` _) -(image_comp u_ normr setT).
move=> /has_ub_image_norm uM; split => //.
by exists (u_ 0%N), 0%N.
Qed.

Lemma cvg_has_inf (u_ : R^o ^nat) : cvg u_ -> has_inf (u_ @` setT).
Proof.
move/is_cvgN/cvg_has_sup; rewrite has_inf_supN.
suff -> : (- u_) @` setT = -%R @` (u_ @` setT) by [].
rewrite predeqE => x; split.
by case=> n _ <-; exists (u_ n) => //; exists n.
by case=> y [] n _ <- <-; exists n.
Qed.

Lemma nondecreasing_cvg (u_ : (R^o) ^nat) (M : R) :
    nondecreasing_seq u_ -> (forall n, u_ n <= M) ->
  u_ --> (sup (u_ @` setT) : R^o).
Proof.
move=> u_nd u_M; set S := _ @` _; set M0 := sup S.
have supS : has_sup S.
  split; first by exists (u_ 0%N), 0%N.
  by exists M; apply/ubP => x -[n _ <-{x}].
apply: cvg_distW; first exact: fmap_filter.
move=> _/posnumP[e]; rewrite near_map.
have [p /andP[M0u_p u_pM0]] : exists p, M0 - e%:num <= u_ p <= M0.
  have [x] := sup_adherent supS (posnum_gt0 e).
  move=> -[p _] <-{x} => /ltW M0u_p.
  exists p; rewrite M0u_p /=; have /ubP := sup_upper_bound supS.
  by apply; exists p.
near=> n; have pn : (p <= n)%N by near: n; apply: nbhs_infty_ge.
rewrite distrC ler_norml ler_sub_addl (ler_trans M0u_p (u_nd _ _ pn)) /=.
rewrite ler_subl_addr (@le_trans _ _ M0) ?ler_addr //.
by have /ubP := sup_upper_bound supS; apply; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma nondecreasing_is_cvg (u_ : (R^o) ^nat) (M : R) :
  nondecreasing_seq u_ -> (forall n, u_ n <= M) -> cvg u_.
Proof. by move=> u_incr u_bnd; apply: cvgP; apply: nondecreasing_cvg. Qed.

Lemma near_nondecreasing_is_cvg (u_ : (R^o) ^nat) (M : R) :
    {near \oo, nondecreasing_seq u_} ->
    (\forall n \near \oo, u_ n <= M) ->
  cvg u_.
Proof.
move=> [k _ u_nd] [k' _ u_M]; suff : cvg [sequence u_ (n + maxn k k')%N]_n.
  by case/cvg_ex => /= l; rewrite cvg_shiftn => ul; apply/cvg_ex; exists l.
apply (@nondecreasing_is_cvg _ M) => [/= ? ? ? | ?].
  by rewrite u_nd ?leq_add2r//= (leq_trans (leq_maxl _ _) (leq_addl _ _)).
by rewrite u_M //= (leq_trans (leq_maxr _ _) (leq_addl _ _)).
Qed.

Lemma nonincreasing_cvg (u_ : (R^o) ^nat) (m : R) :
    nonincreasing_seq u_ -> (forall n, m <= u_ n) ->
  u_ --> (inf (u_ @` setT) : R^o).
Proof.
rewrite -nondecreasing_opp => /(@nondecreasing_cvg _ (- m)) u_sup mu_.
rewrite -[X in X --> _]opprK /inf image_comp.
by apply: cvgN; apply u_sup => p; rewrite ler_oppl opprK.
Qed.

Lemma nonincreasing_is_cvg (u_ : (R^o) ^nat) (m : R) :
  nonincreasing_seq u_ -> (forall n, m <= u_ n) -> cvg u_.
Proof. by move=> u_decr u_bnd; apply: cvgP; apply: nonincreasing_cvg. Qed.

Lemma near_nonincreasing_is_cvg (u_ : (R^o) ^nat) (m : R) :
    {near \oo, nonincreasing_seq u_} ->
    (\forall n \near \oo, m <= u_ n) ->
  cvg u_.
Proof.
move=> u_ni u_m.
rewrite -(opprK u_); apply: is_cvgN; apply/(@near_nondecreasing_is_cvg _ (- m)).
by apply: filterS u_ni => x u_x y xy; rewrite ler_oppl opprK u_x.
by apply: filterS u_m => x u_x; rewrite ler_oppl opprK.
Qed.

Lemma adjacent (u_ v_ : R^o ^nat) : nondecreasing_seq u_ -> nonincreasing_seq v_ ->
  (v_ - u_) --> (0 : R^o) -> [/\ lim v_ = lim u_, cvg u_ & cvg v_].
Proof.
set w_ := v_ - u_ => iu dv w0.
have vu n : v_ n >= u_ n.
  suff : lim w_ <= w_ n by rewrite (cvg_lim _ w0)// subr_ge0.
  apply: nonincreasing_cvg_ge; last apply: cvgP w0.
  by move=> m p mp; rewrite ler_sub; rewrite ?iu ?dv.
have cu : cvg u_.
  suff: forall n, u_ n <= v_ O by apply: nondecreasing_is_cvg.
  by move=> n; rewrite (le_trans (vu _)) //; apply/dv.
have cv : cvg v_.
  suff: forall n, u_ O <= v_ n by apply: nonincreasing_is_cvg.
  by move=> n; rewrite (le_trans _ (vu _)) //; exact: iu.
by split=> //; apply/eqP; rewrite -subr_eq0 -limB //; exact/eqP/cvg_lim.
Qed.

End sequences_R_lemmas.

Definition harmonic {R : fieldType} : R^o ^nat := [sequence n.+1%:R^-1]_n.
Arguments harmonic {R} n /.

Lemma harmonic_gt0 {R : numFieldType} i : 0 < harmonic i :> R.
Proof. by rewrite /= invr_gt0 ltr0n. Qed.

Lemma harmonic_ge0 {R : numFieldType} i : 0 <= harmonic i :> R.
Proof. exact/ltW/harmonic_gt0. Qed.

Lemma cvg_harmonic {R : archiFieldType} : harmonic --> (0 : R^o).
Proof.
apply: cvg_distW; first exact: fmap_filter.
move=> _/posnumP[e]; rewrite near_map; near=> i.
rewrite distrC subr0 ger0_norm//= -lef_pinv ?qualifE// invrK.
rewrite (le_trans (ltW (archi_boundP _)))// ler_nat -add1n -leq_subLR.
by near: i; apply: nbhs_infty_ge.
Grab Existential Variables. all: end_near. Qed.

(* TODO: is there an equivalent in mathcomp? *)
Lemma iter_addr (V : zmodType) n (r : V) p : iter n (+%R r) p = r *+ n + p.
Proof.
elim: n => /= [|n ih]; by [rewrite mulr0n add0r|rewrite ih mulrS addrA].
Qed.

Definition arithmetic_mean (R : numDomainType) (u_ : R^o ^nat) : R^o ^nat :=
  [sequence n.+1%:R^-1 * (series u_ n.+1)]_n.

Definition harmonic_mean (R : numDomainType) (u_ : R^o ^nat) : R^o ^nat :=
  let v := [sequence (u_ n)^-1]_n in
  [sequence (n.+1%:R / series v n.+1)]_n.

Definition root_mean_square (R : realType) (u_ : R^o ^nat) : R^o ^nat :=
  let v_ := [sequence (u_ k)^+2]_k in
  [sequence Num.sqrt (n.+1%:R^-1 * series v_ n.+1)]_n.

Section cesaro.
Variable R : archiFieldType.

Theorem cesaro (u_ : R^o ^nat) (l : R^o) : u_ --> l -> arithmetic_mean u_ --> l.
Proof.
move=> u0_cvg; have ssplit v_ m n : (m <= n)%N -> `|n%:R^-1 * series v_ n| <=
    n%:R^-1 * `|series v_ m| + n%:R^-1 * `|\sum_(m <= i < n) v_ i|.
  move=> /subnK<-; rewrite series_addn mulrDr (le_trans (ler_norm_add _ _))//.
  by rewrite !normrM ger0_norm ?invr_ge0 ?ler0n.
apply/cvg_distP; first exact: fmap_filter.
move=> _/posnumP[e]; rewrite near_simpl; near \oo => m; near=> n.
have {}/ssplit -/(_ _ [sequence l - u_ n]_n) : (m.+1 <= n.+1)%nat by near: n; exists m.
rewrite /series /= big_split/= sumrN mulrBr sumr_const card_ord -(mulr_natl l) mulKf//.
move=> /le_lt_trans->//; rewrite [e%:num]splitr ltr_add//.
  have [->|neq0] := eqVneq (\sum_(k < m.+1) (l - u_ k)) 0.
    by rewrite normr0 mulr0.
  rewrite -ltr_pdivl_mulr ?normr_gt0//.
  rewrite -ltf_pinv ?qualifE// ?mulr_gt0 ?invr_gt0 ?normr_gt0// invrK.
  rewrite (lt_le_trans (archi_boundP _))// ?(invr_ge0, mulr_ge0)// ler_nat leqW//.
  by near: n; apply: nbhs_infty_ge.
rewrite ltr_pdivr_mull ?ltr0n // (le_lt_trans (ler_norm_sum _ _ _)) //.
rewrite (le_lt_trans (@ler_sum_nat _ _ _ _ (fun i => e%:num / 2) _))//; last first.
  by rewrite sumr_const_nat mulr_natl ltr_pmuln2l// ltn_subrL.
move=> i /andP[mi _]; move: i mi; near: m.
have : \forall x \near \oo, `|l - u_ x| < e%:num / 2.
  by move/cvg_distP : u0_cvg; apply; rewrite divr_gt0.
move=> -[N _ Nu]; exists N => // k Nk i ki.
by rewrite ltW// Nu//= (leq_trans Nk)// ltnW.
Grab Existential Variables. all: end_near. Qed.

End cesaro.

Section cesaro_converse.
Variable R : archiFieldType.

Let cesaro_converse_off_by_one (u_ : R^o ^nat) :
  [sequence n.+1%:R^-1 * series u_ n.+1]_ n --> (0 : R^o) ->
  [sequence n.+1%:R^-1 * series u_ n]_ n --> (0 : R^o).
Proof.
move=> H; apply/cvg_distP; first exact: fmap_filter.
move=> _/posnumP[e]; rewrite near_map.
move/cvg_distP : H => /(_ e%:num (posnum_gt0 e)); rewrite near_map => -[m _ mu].
near=> n; rewrite sub0r normrN /=.
have /andP[n0] : ((0 < n) && (m <= n.-1))%N.
  near: n; exists m.+1 => // k mk; rewrite (leq_trans _ mk) //=.
  by rewrite -(leq_add2r 1%N) !addn1 prednK // (leq_trans _ mk).
move/mu => {mu}; rewrite sub0r normrN /= prednK //; apply: le_lt_trans.
rewrite !normrM ler_wpmul2r // ger0_norm // ger0_norm // ?invr_ge0 // ?ler0n //.
by rewrite lef_pinv // ?ler_nat // posrE // ltr0n.
Grab Existential Variables. all: end_near. Qed.

Lemma cesaro_converse (u_ : R^o ^nat) (l : R^o) :
  telescope u_ =o_\oo harmonic ->
  arithmetic_mean u_ --> l -> u_ --> l.
Proof.
pose a_ := telescope u_ => a_o u_l.
suff abel : forall n,
    u_ n - arithmetic_mean u_ n = \sum_(1 <= k < n.+1) k%:R / n.+1%:R * a_ k.-1.
  suff K : u_ - arithmetic_mean u_ --> (0 : R^o).
    rewrite -(add0r l).
    rewrite (_ : u_ = u_ - arithmetic_mean u_ + arithmetic_mean u_); last first.
      by rewrite funeqE => n; rewrite subrK.
    exact: cvgD.
  rewrite (_ : _ - arithmetic_mean u_ =
      (fun n => \sum_(1 <= k < n.+1) k%:R / n.+1%:R * a_ k.-1)); last first.
    by rewrite funeqE.
  rewrite {abel} /= (_ : (fun _ => _) =
      fun n => n.+1%:R^-1 * \sum_(k < n) k.+1%:R * a_ k); last first.
    rewrite funeqE => n; rewrite big_add1 /= big_mkord /= big_distrr /=.
    by apply eq_bigr => i _; rewrite mulrCA mulrA.
  have {}a_o : [sequence n.+1%:R * telescope u_ n]_n --> (0 : R^o).
    apply: (@eqolim0 R nat [normedModType R of R^o] eventually_filterType).
    rewrite a_o.
    set h := 'o_[filter of \oo] harmonic.
    apply/eqoP => _/posnumP[e] /=.
    near=> n; rewrite normr1 mulr1 normrM -ler_pdivl_mull ?normr_gt0 //.
    rewrite mulrC -normrV ?unitfE //.
    near: n.
    by case: (@eqoP R nat [normedModType R of R^o] [normedModType R of R^o] eventually_filterType harmonic h) => Hh _; apply Hh.
  move: (cesaro a_o); rewrite /arithmetic_mean /series /= -/a_.
  exact: (@cesaro_converse_off_by_one (fun k : nat => k.+1%:R * a_ k)).
case => [|n].
  rewrite /arithmetic_mean /= invr1 mul1r /series /= big_ord_recl !big_ord0.
  by rewrite addr0 subrr big_nil.
rewrite /arithmetic_mean /= /series /= big_ord_recl /=.
under eq_bigr do rewrite /bump /= add1n eq_sum_telescope.
rewrite big_split /= big_const card_ord iter_addr addr0 addrA -mulrS mulrDr.
rewrite -(mulr_natl (u_ O)) mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r opprD addrA.
rewrite eq_sum_telescope (addrC (u_ O)) addrK.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) \sum_(0 <= k < n.+1 | (k < i.+1)%N) a_ k); last first.
  by rewrite big_mkord; apply eq_bigr => i _; rewrite big_mkord -big_ord_widen.
rewrite (exchange_big_dep_nat xpredT) //=.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) \sum_(i <= j < n.+1) a_ i ); last first.
  apply congr_big_nat => //= i ni.
  rewrite big_const_nat iter_addr addr0 -big_filter.
  rewrite big_const_seq iter_addr addr0; congr (_ *+ _).
  rewrite /index_iota subn0 -[in LHS](subnKC (ltnW ni)) iota_add filter_cat.
  rewrite count_cat (_ : [seq _ <- _ | _] = [::]); last first.
    rewrite -(filter_pred0 (iota 0 i)); apply eq_in_filter => j.
    by rewrite mem_iota leq0n andTb add0n => ji; rewrite ltnNge ji.
  rewrite 2!add0n (_ : [seq _ <- _ | _] = iota i (n.+1 - i)); last first.
    rewrite -[RHS]filter_predT; apply eq_in_filter => j.
    rewrite mem_iota => /andP[ij]; rewrite subnKC; last exact/ltnW.
    by move=> jn; rewrite ltnS ij.
  by rewrite count_predT size_iota.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) a_ i * (n.+1 - i)%:R); last first.
  by apply eq_bigr => i _; rewrite big_const_nat iter_addr addr0 mulr_natr.
rewrite big_distrr /= big_mkord (big_morph _ (@opprD _) (@oppr0 _)).
rewrite -big_split /= big_add1 /= big_mkord; apply eq_bigr => i _.
rewrite mulrCA -[X in X - _]mulr1 -mulrBr [RHS]mulrC; congr (_ * _).
rewrite -[X in X - _](@divrr _ (n.+2)%:R) ?unitfE ?pnatr_eq0 //.
rewrite [in X in _ - X]mulrC -mulrBl; congr (_ / _).
rewrite -natrB; last by rewrite (@leq_trans n.+1) // leq_subr.
rewrite subnBA; by [rewrite addSnnS addnC addnK | rewrite ltnW].
Grab Existential Variables. all: end_near. Abort.

End cesaro_converse.

Section series_convergence.

Lemma cvg_series_cvg_0 (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  cvg (series u_) -> u_ --> (0 : V).
Proof.
move=> cvg_series.
rewrite (_ : u_ = fun n => series u_ (n + 1)%nat - series u_ n); last first.
  by rewrite funeqE => i; rewrite addn1 seriesSB.
rewrite -(subrr (lim (series u_))).
by apply: cvgD; rewrite ?cvg_shiftn//; apply: cvgN.
Qed.

Lemma nondecreasing_series (R : numFieldType) (u_ : R^o ^nat) :
  (forall n, 0 <= u_ n) -> nondecreasing_seq (series u_).
Proof.
move=> u_ge0; apply: nondecreasing_seqP => n.
by rewrite /series/= big_ord_recr ler_addl.
Qed.

Lemma increasing_series (R : numFieldType) (u_ : R^o ^nat) :
  (forall n, 0 < u_ n) -> increasing_seq (series u_).
Proof.
move=> u_ge0; apply: increasing_seqP => n.
by rewrite /series/= big_ord_recr ltr_addl.
Qed.

End series_convergence.

Definition arithmetic (R : zmodType) a z : R^o ^nat := [sequence a + z *+ n]_n.
Arguments arithmetic {R} a z n /.

Lemma mulrn_arithmetic (R : zmodType) : @GRing.natmul R = arithmetic 0.
Proof. by rewrite funeq2E => z n /=; rewrite add0r. Qed.

Definition geometric (R : ringType) a z : R^o ^nat := [sequence a * z ^+ n]_n.
Arguments geometric {R} a z n /.

Lemma exprn_geometric (R : ringType) : (@GRing.exp R) = geometric 1.
Proof. by rewrite funeq2E => z n /=; rewrite mul1r. Qed.

Lemma cvg_arithmetic (R : archiFieldType) a (z : R^o) :
  z > 0 -> arithmetic a z --> +oo.
Proof.
move=> z_gt0; apply/cvgPpinfty => _ /posnumP[A]; near=> n => /=.
rewrite -ler_subl_addl -mulr_natl -ler_pdivr_mulr//; set x := (X in X <= _).
rewrite ler_normlW// ltW// (lt_le_trans (archi_boundP _))// ler_nat.
by near: n; apply: nbhs_infty_ge.
Grab Existential Variables. all: end_near. Qed.

(* Cyril: I think the shortest proof would rely on cauchy completion *)
Lemma cvg_expr (R : archiFieldType) (z : R) :
  `|z| < 1 -> (@GRing.exp R z : R^o^nat) --> (0 : R^o).
Proof.
move=> Nz_lt1; apply: cvg_dist0; pose t := (1 - `|z|).
pose oo_filter := eventually_filterType. (* Cyril: fixme *)
apply: (@squeeze _ _ (cst 0) _ (t^-1 *: harmonic) oo_filter); last 2 first.
- exact: (@cvg_cst [topologicalType of R^o]).
- by rewrite -(scaler0 _ t^-1); exact: (cvgZr cvg_harmonic).
near=> n; rewrite normr_ge0 normrX/= ler_pdivl_mull ?subr_gt0//.
rewrite -(@ler_pmul2l _ n.+1%:R)// mulfV// [t * _]mulrC mulr_natl.
have -> : 1 = (`|z| + t) ^+ n.+1 by rewrite addrC addrNK expr1n.
rewrite exprDn (bigD1 (inord 1)) ?inordK// subn1 expr1 bin1 ler_addl sumr_ge0//.
by move=> i; rewrite ?(mulrn_wge0, mulr_ge0, exprn_ge0, subr_ge0)// ltW.
Grab Existential Variables. all: end_near. Qed.

Lemma geometric_mult (R : ringType) (z a : R) :
  a *: geometric 1 z = geometric a z.
Proof.
  by rewrite funeqE => n; rewrite /GRing.scale /= /GRing.scale /= mul1r.
Qed.

Lemma geometric_exp (R : ringType) (z : R) :
  geometric 1 z = GRing.exp z .
Proof.
  by rewrite funeqE => n; rewrite /GRing.scale /= /GRing.scale /= mul1r.
Qed.

Lemma geometric_comm (R : ringType) (z : R) n :
  GRing.comm (geometric 1 z n) z .
Proof.
  by rewrite /GRing.comm /= mul1r -exprSr -exprS.
Qed.

Lemma geometric_series_ring_E (R : ringType) (z a : R) n :
   series (geometric a z) n * (1 - z) = a * (1 - z ^+ n).
Proof.
  rewrite seriesEnat /= mulr_suml.
  (under eq_bigr do rewrite -mulrA); rewrite -mulr_sumr.
  congr (_ * _).
  under eq_bigr do rewrite mulrBr mulr1 -exprSr -opprB.
  by rewrite sumrN telescope_sumr // opprB.
Qed.
 
Lemma geometric_seriesE (R : numFieldType) (a z : R) : z != 1 ->
  series (geometric a z) = [sequence a * (1 - z ^+ n) / (1 - z)]_n.
Proof.
  rewrite funeqE => z_neq1 n.
  apply: (@mulIf _ (1 - z)); rewrite ?mulfVK ?subr_eq0 1?eq_sym//.
  by rewrite geometric_series_ring_E.
Qed.

Lemma cvg_geometric_series (R : archiFieldType) (a z : R) : `|z| < 1 ->
  series (geometric a z) --> (a * (1 - z)^-1 : R^o).
Proof.
move=> Nz_lt1; rewrite geometric_seriesE ?lt_eqF 1?ltr_normlW//.
have -> : a / (1 - z) = (a * (1 - 0)) / (1 - z) by rewrite subr0 mulr1.
by apply: cvgMl; apply: cvgMr; apply: cvgB; [apply: cvg_cst|apply: cvg_expr].
Qed.

Lemma cvg_geometric (R : archiFieldType) (a z : R) : `|z| < 1 ->
  geometric a z --> (0 : R^o).
Proof. by move=> /cvg_geometric_series/cvgP/cvg_series_cvg_0. Qed.

Lemma is_cvg_geometric_series (R : archiFieldType) (a z : R) : `|z| < 1 ->
 cvg (series (geometric a z)).
Proof. by move=> /cvg_geometric_series/cvgP; apply. Qed.

Definition normed_series_of (K : numDomainType) (V : normedModType K)
    (u_ : V ^nat) of phantom V^nat (series u_) : K^o ^nat :=
  [series `|u_ n|]_n.
Notation "[ 'normed' s_ ]" := (@normed_series_of _ _ _ (Phantom _ s_)) : ring_scope.
Arguments normed_series_of {K V} u_ _ n /.

Lemma ger0_normed {K : numFieldType} (u_ : K^o ^nat) :
  (forall n, 0 <= u_ n) -> [normed series u_] = series u_.
Proof.
by move=> u_gt0; rewrite funeqE => n /=; apply: eq_bigr => k; rewrite ger0_norm.
Qed.

Lemma cauchy_seriesP {R : numFieldType} (V : normedModType R) (u_ : V ^nat) :
  cauchy (series u_ @ \oo) <->
  forall e : R, e > 0 ->
    \forall n \near (\oo, \oo), `|\sum_(n.1 <= k < n.2) u_ k| < e.
Proof.
rewrite -cauchy_ballP; split=> su_cv _/posnumP[e]; have {}su_cv := su_cv _ e;
rewrite -near2_pair -ball_normE !near_simpl/= in su_cv *.
  apply: filterS su_cv => -[/= m n]; rewrite distrC sub_series.
  by have [|/ltnW]:= leqP m n => mn//; rewrite (big_geq mn) ?normr0.
have := su_cv; rewrite near_swap => su_cvC; near=> m => /=; rewrite sub_series.
by have [|/ltnW]:= leqP m.2 m.1 => m12; rewrite ?normrN; near: m.
Grab Existential Variables. all: end_near. Qed.

Lemma series_le_cvg (R : realType) (u_ v_ : R^o ^nat) :
  (forall n, 0 <= u_ n) -> (forall n, 0 <= v_ n) ->
  (forall n, u_ n <= v_ n) ->
  cvg (series v_) -> cvg (series u_).
Proof.
move=> u_ge0 v_ge0 le_uv; have le_UV n : series u_ n <= series v_ n.
  by apply ler_sum => *; exact: le_uv.
move=> /cvg_seq_bounded/pinfty_ex_gt0[/= M _ svM].
apply: (@nondecreasing_is_cvg _ _ M); first by apply: nondecreasing_series.
by move=> n; apply: le_trans (svM n _); rewrite // ger0_norm ?sumr_ge0.
Qed.

Lemma normed_cvg {R : realType} (V : completeNormedModType R) (u_ : V ^nat) :
  cvg [normed series u_] -> cvg (series u_).
Proof.
move=> /cauchy_cvgP/cauchy_seriesP u_ncvg.
apply/cauchy_cvgP; first exact: fmap_proper_filter.
apply/cauchy_seriesP => e /u_ncvg.
apply: filterS => n /=; rewrite ger0_norm ?sumr_ge0//.
by apply: le_lt_trans; apply: ler_norm_sum.
Qed.

Lemma cvg_is_cvg {T : topologicalType} (F : set(set(T))) (a:T) :
  ProperFilter F ->
  hausdorff T ->
  F --> a -> cvg F.
Proof.
  by move=> ? ? ?; have ->: (lim F) = a by apply: cvg_lim.
Qed.


Lemma geometric_cvgB 
    {R : realType } {V : unitalBanachAlgType R} (z : V) :
  `|z| < 1 -> 
  cvg (series (geometric 1 z)).
Proof.
  move => z_lt. 
  apply: normed_cvg. 
  apply: series_le_cvg. 
  4: apply: (@is_cvg_geometric_series R 1 `|z|).
  - by move=> ? //=.
  - elim => //= n IH; rewrite mul1r exprS.
    apply: mulr_ge0 => //=.
    by rewrite mul1r in IH.
  - move=> n /=; rewrite ?mul1r.
    by apply: normBmul_le_n.
  - by rewrite normrE.
Qed.

Lemma cvg_expr_B
    {R : realType } {V : unitalBanachAlgType R}
    (z : V) : 
  `|z| < 1 -> (GRing.exp z @ \oo --> (0 : V)).
Proof.
  move=> /geometric_cvgB/cvgP/cvg_series_cvg_0. 
  by rewrite geometric_exp.
Qed.

Lemma geometric_inv_l
    {R : realType } {V : unitalBanachAlgType R} (z : V) :
  `|z| < 1 -> 
  (lim (series (geometric 1 z))) * (1-z) = 1.
Proof.
  move=> z_lt.
  have c_cvg: ([sequence (1-z)]_n) --> 1-z.
    by apply: cvg_cst.
  pose geo_cvg := (geometric_cvgB z_lt).
  pose Q := (limB_M eventually_filter geo_cvg c_cvg). 
  move: Q.
  under [X in X @ _ --> _]funext => n /=. 
    rewrite /GRing.mul /= geometric_series_ring_E mul1r. 
  over.
  move=> Q; rewrite -(cvg_lim _ Q) //.
  rewrite limB ?lim_cst //. 
  by rewrite (cvg_lim _ (cvg_expr_B z_lt)) // subr0.
  apply: cvg_cst.
  apply: cvg_is_cvg => //=. 
  by apply: cvg_expr_B.
Qed.

Lemma sequence_commute 
  {R : realType } {V : unitalBanachAlgType R} (f g: V ^nat) :
  (forall n, GRing.comm (f n) (g n)) -> 
  GRing.comm f g.
Proof.
  move=> fg_comm; apply funext=> n.
  by rewrite /GRing.mul /= fg_comm.
Qed.

Lemma series_commute
  {R : realType } {V : unitalBanachAlgType R} (x : V) (f: V ^nat) :
  (forall n, GRing.comm (f n) x) -> 
  (forall n, GRing.comm (series f n) x).
Proof.
  move=> fg_comm n.
  rewrite  /GRing.comm seriesEnat /= mulr_sumr.
  under [RHS]eq_bigr do rewrite -(fg_comm).
  by rewrite mulr_suml.
Qed.

Lemma lim_commute_filter 
  {R : realType } {V : unitalBanachAlgType R} 
  (x y: V) (F : (set(set V))) :
  ProperFilter F ->
  (\near F, GRing.comm x F) ->
  F --> y -> GRing.comm x y.
Proof.
  move => FF xF_comm Fy.
  apply: subr0_eq.
  set g := (fun z => x * z - z * x).
  have cts_g : (continuous g). {
    rewrite /g => z.
    apply: continuousB; apply: continuous2_cvg => //=.
    2,4: by apply: continuous_cst.
    1,2: by apply: continuous_BM.
  }
  apply: close_eq => //=; apply (cvg_close (F := g @ F)).
  - by apply: cvg_fmap => //= ?; apply: cts_g.
  - apply: cvg_near_cst. 
    near=> z; rewrite /g.
    apply/eqP; rewrite subr_eq0; apply/eqP.
    near: z.
    apply xF_comm.
  Grab Existential Variables. all: end_near. Qed.

Lemma lim_series_commute 
  {R : realType } {V : unitalBanachAlgType R} 
  (x: V) (f : V^nat) :
  (forall n, GRing.comm x (f n)) ->
  (cvg (series f)) ->
  GRing.comm x (lim (series f)).
Proof.
  move=> xf_comm cvgf.
  apply: (@lim_commute_filter R V x _ (series f @ \oo)).
  2: by apply: cvgf.
  near_simpl; near=> z.
  apply GRing.commr_sym.
  apply: series_commute => ?.
  by apply GRing.commr_sym.
Grab Existential Variables. all: end_near. Qed.

Lemma geometric_inv_r
    {R : realType } {V : unitalBanachAlgType R} (z : V) :
  `|z| < 1 -> 
  (1-z) * (lim (series (geometric 1 z))) = 1.
Proof.
  move=> z_lt.
  rewrite lim_series_commute.
  - by apply: geometric_inv_l.
  - move=>?; apply: GRing.commr_sym; apply: commrD.
      1: by apply: commr1.
    by apply commrN; apply: geometric_comm.
  - by apply: geometric_cvgB.
Qed.

Lemma norm_lt_1_unit 
    {R : realType } {V : unitalBanachAlgType R} (z : V) :
  `|z| < 1 -> 
  (1-z) \is a GRing.unit.
Proof.
  move=> z_lt.
  apply/unitrP; exists (lim(series (geometric 1 z))); split.
  - by apply: geometric_inv_l.
  - by apply: geometric_inv_r.
Qed.

Lemma geometric_cvg_inv 
    {R : realType } {V : unitalBanachAlgType R} (z : V) :
  `|z| < 1 -> 
  (series (geometric 1 z)) --> (1-z)^-1.
Proof.
  move=>?.
  suff <-: ( lim (series(geometric 1 z)) = (1-z)^-1)
    by apply: geometric_cvgB.
  apply: mulrI.
    1: by apply: norm_lt_1_unit; eauto. 
  rewrite geometric_inv_r // mulrV //.
  by apply: norm_lt_1_unit; eauto. 
Qed.

Section sequences_of_extended_real_numbers.

Lemma ereal_cvgN (R : realFieldType) (f : {ereal R} ^nat) (a : {ereal R}) :
  f --> a -> (fun n => - (f n))%E --> (- a)%E.
Proof.
rewrite (_ : (fun n => - (f n))%E = -%E \o f) // => /cvg_comp; apply.
exact: oppe_continuous.
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

Lemma ereal_lim_le (R : realFieldType) x (u_ : {ereal R} ^nat) : cvg u_ ->
  (\forall n \near \oo, (u_ n <= x)%E) -> (lim u_ <= x)%E.
Proof.
move=> /closed_cvg_loc V xu_; elim/V: _; last exact: closed_ereal_ge_ereal.
case: xu_ => m _ xu_.
near \oo => n.
have mn : (n >= m)%N by near: n; exists m.
by exists n => // k nk /=; exact: (xu_ _ (leq_trans mn nk)).
Grab Existential Variables. all: end_near. Qed.

(* NB: worth keeping in addition to cvgPpinfty? *)
Lemma cvgPpinfty_lt (R : realFieldType) (u_ : R^o ^nat) :
  u_ --> +oo <-> forall A, A > 0 -> \forall n \near \oo, A < u_ n.
Proof.
split => [/cvgPpinfty uoo A A0|uoo]; last first.
  by apply/cvgPpinfty => A {}/uoo [n _ uoo]; exists n => // m nm; apply/ltW/uoo.
have /uoo[n _ {}uoo] : 0 < A *+ 2 by rewrite pmulrn_lgt0.
exists n => // m nm; rewrite (@lt_le_trans _ _ (A *+ 2)) // ?mulr2n ?ltr_addr //.
exact: uoo.
Qed.

Lemma dvg_ereal_cvg (R : realFieldType) (u_ : (R^o) ^nat) :
  u_ --> +oo -> (fun n => (u_ n)%:E) --> +oo%E.
Proof.
move/cvgPpinfty_lt => uoo; apply/cvg_ballP; first exact: fmap_filter.
move=> _/posnumP[e]; rewrite near_map.
have [e1|e1] := lerP 1 e%:num.
  case: (uoo _ ltr01) => k _ k1un; near=> n.
  rewrite /ball /= /ereal_ball [contract +oo]/= ger0_norm ?subr_ge0; last first.
    by move: (contract_le1 (u_ n)%:E); rewrite ler_norml => /andP[].
  rewrite ltr_subl_addr addrC -ltr_subl_addr.
  have /le_lt_trans->//: contract 1%:E < contract (u_ n)%:E.
    by rewrite lt_contract lte_fin k1un//; near: n; exists k.
  by rewrite (@le_trans _ _ 0) // ?subr_le0 //= normr1 divr_ge0.
have onee1 : `|1 - e%:num| < 1.
  by rewrite gtr0_norm // ?subr_gt0 // ltr_subl_addl addrC -ltr_subl_addl subrr.
have : 0 < real_of_er (expand (1 - e%:num)).
  rewrite -lte_fin real_of_er_expand //.
  by rewrite lt_expandRL ?inE ?ltW// contract0 subr_gt0.
case/uoo => k _ k1un; near=> n.
rewrite /ball /= /ereal_ball [contract +oo]/= ger0_norm ?subr_ge0; last first.
  by move: (contract_le1 (u_ n)%:E); rewrite ler_norml => /andP[].
rewrite ltr_subl_addr addrC -ltr_subl_addr.
suff : `|1 - e%:num| < contract (u_ n)%:E by exact: le_lt_trans (ler_norm _).
rewrite gtr0_norm ?subr_gt0 // -lt_expandLR ?inE ?ltW//.
by rewrite -real_of_er_expand // lte_fin k1un//; near: n; exists k.
Grab Existential Variables. all: end_near. Qed.

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
  by rewrite -ERFin_real_of_er // foo//= leq_addl.
split; last first.
  by move/(@cvg_app _ _ _ _ real_of_er) : fa; apply: cvg_trans; exact: cvg_id.
move/cvg_ballP : fa.
have e0 : 0 < minr (1 + contract a%:E) (1 - contract a%:E).
  by rewrite lt_minr -ltr_subl_addl add0r subr_gt0 -ltr_norml contract_lt1.
move/(_ _ e0); rewrite near_map => -[N _ fa]; near=> n.
have /fa : (N <= n)%N by near: n; exists N.
rewrite /ball /= /ereal_ball; case: (f n) => //.
- rewrite ltr0_norm; first by rewrite opprB lt_minr ltxx andbF.
  by rewrite -opprB ltr_oppl oppr0; move: e0; rewrite lt_minr => -/andP[].
- rewrite opprK gtr0_norm; first by rewrite lt_minr addrC ltxx.
  by rewrite addrC; move: e0; rewrite lt_minr => -/andP[].
Grab Existential Variables. all: end_near. Qed.

Lemma nondecreasing_seq_ereal_cvg (R : realType) (u_ : nat -> {ereal R}) :
  nondecreasing_seq u_ -> u_ --> ereal_sup (u_ @` setT).
Proof.
move=> nd_u_; set S := u_ @` setT; set l := ereal_sup S.
have [Spoo|Spoo] := pselect (S +oo%E).
  have [N Nu] : exists N, forall n, (n >= N)%nat -> u_ n = +oo%E.
    case: Spoo => N _ uNoo; exists N => n Nn.
    by move: (nd_u_ _ _ Nn); rewrite uNoo lee_pinfty_eq => /eqP.
  have -> : l = +oo%E by rewrite /l /ereal_sup; exact: supremum_pinfty.
  rewrite -(cvg_shiftn N); set f := (X in X --> _).
  rewrite (_ : f = (fun=> +oo%E)); first exact: cvg_cst.
  by rewrite funeqE => n; rewrite /f /= Nu // leq_addl.
have [Snoo|Snoo] := pselect (u_ = fun=> -oo%E).
  suff : l = -oo%E by move=> ->; rewrite Snoo; exact: cvg_cst.
  rewrite /l.
  suff -> : S = [set -oo%E] by rewrite ereal_sup_set1.
  rewrite predeqE => x; split => [-[n _ <-]|->].
  by rewrite Snoo.
  by exists O => //; rewrite Snoo.
have [/eqP|lnoo] := boolP (l == -oo%E).
  move/ereal_sup_ninfty => loo.
  suff : u_ = (fun=> -oo%E) by [].
  by rewrite funeqE => m; apply (loo (u_ m)); exists m.
apply/cvg_ballP; first exact: fmap_filter.
move=> _/posnumP[e].
have [/eqP {lnoo}loo|lpoo] := boolP (l == +oo%E).
  rewrite near_map; near=> n; rewrite /ball /= /ereal_ball.
  have unoo : u_ n != -oo%E.
    near: n.
    have [m /eqP umoo] : exists m, u_ m <> -oo%E.
      apply/existsNP => uoo.
      by apply/Snoo; rewrite funeqE => ?; rewrite uoo.
    exists m => // k mk; apply: contra umoo => /eqP ukoo.
    by move/nd_u_ : mk; rewrite ukoo lee_ninfty_eq.
  rewrite loo ger0_norm ?subr_ge0; last by case/ler_normlP : (contract_le1 (u_ n)).
  have [e2|e2] := lerP 2 e%:num.
    rewrite /= ltr_subl_addr addrC -ltr_subl_addr.
    case/ler_normlP : (contract_le1 (u_ n)); rewrite ler_oppl => un1 _.
    rewrite (@le_lt_trans _ _ (-1)) //.
      by rewrite ler_subl_addr addrC -ler_subl_addr opprK (le_trans e2).
    by move: un1; rewrite le_eqVlt eq_sym contract_eqN1 (negbTE unoo).
  rewrite ltr_subl_addr addrC -ltr_subl_addr -lt_expandLR ?inE//=.
    near: n.
    suff [n Hn] : exists n, (expand (contract +oo - e%:num)%R < u_ n)%E.
      by exists n => // m nm; rewrite (lt_le_trans Hn) //; apply nd_u_.
    apply/not_existsP => abs.
    have : (l <= expand (contract +oo - e%:num)%R)%E.
      apply: ub_ereal_sup => x [n _ <-{x}].
      rewrite leNgt; apply/negP/abs.
      rewrite loo lee_pinfty_eq expand_eqoo ler_sub_addr addrC -ler_sub_addr.
      by rewrite subrr; apply/negP; rewrite -ltNge.
    have [e1|e1] := ltrP 1 e%:num.
      by rewrite ler_subl_addr (le_trans (ltW e2)).
    by rewrite ler_subl_addr ler_addl.
have [r lr] : exists r, l = r%:E by move: l lnoo lpoo => [] // r' _ _; exists r'.
have [re1|re1] := ltrP (`|contract l - e%:num|) 1; last first.
  rewrite near_map; near=> n; rewrite /ball /= /ereal_ball /=.
  have unoo : u_ n != -oo%E.
    near: n.
    have [m /eqP umoo] : exists m, u_ m <> -oo%E.
      apply/existsNP => uoo.
      by apply/Snoo; rewrite funeqE => ?; rewrite uoo.
    exists m => // k mk; apply: contra umoo => /eqP ukoo.
    by move/nd_u_ : mk; rewrite ukoo lee_ninfty_eq.
  rewrite ger0_norm ?subr_ge0 ?le_contract ?ereal_sup_ub//; last by exists n.
  have [l0|l0] := ger0P (contract l).
    have ? : e%:num > contract r%:E.
      rewrite ltNge; apply/negP => er.
      rewrite lr ger0_norm ?subr_ge0// -ler_subl_addr opprK in re1.
      case/ler_normlP : (contract_le1 r%:E) => _ /(le_trans re1); apply/negP.
      by rewrite -ltNge ltr_addl.
    rewrite lr ltr0_norm ?subr_lt0// opprB in re1.
    rewrite ltr_subl_addr addrC -ltr_subl_addr -opprB ltr_oppl lr.
    rewrite (lt_le_trans _ re1) // lt_neqAle eqr_oppLR contract_eqN1 unoo /=.
    by case/ler_normlP : (contract_le1 (u_ n)).
  rewrite ler0_norm in re1; last first.
    by rewrite subr_le0 (le_trans (ltW l0)).
  rewrite opprB ler_subr_addr addrC -ler_subr_addr in re1.
  rewrite ltr_subl_addr (le_lt_trans re1) // -ltr_subl_addl addrAC subrr add0r.
  rewrite ltr_neqAle eq_sym contract_eqN1 unoo /=.
  by case/ler_normlP : (contract_le1 (u_ n)); rewrite ler_oppl.
pose e' := r - real_of_er (expand (contract l - e%:num)).
have e'0 : 0 < e'.
  rewrite /e' subr_gt0 -lte_fin real_of_er_expand //.
  rewrite lt_expandLR ?inE ?ltW//.
  by rewrite lr ltr_subl_addr // ltr_addl.
have [y [[m _] umx] Se'y] := @ub_ereal_sup_adherent _ S (PosNum e'0) _ lr.
rewrite near_map; near=> n; rewrite /ball /= /ereal_ball /=.
rewrite ger0_norm ?subr_ge0 ?le_contract ?ereal_sup_ub//; last by exists n.
move: Se'y; rewrite -{}umx {y} /= => le'um.
have leum : contract l - e%:num < contract (u_ m).
  rewrite -lt_expandLR ?inE ?ltW//.
  move: le'um; rewrite /e' NERFin -/l [in X in (X - _ < _)%E -> _]lr /= opprB.
  by rewrite addrCA subrr addr0 real_of_er_expand //.
rewrite ltr_subl_addr addrC -ltr_subl_addr (lt_le_trans leum) //.
by rewrite le_contract nd_u_//; near: n; exists m.
Grab Existential Variables. all: end_near. Qed.

(* NB: see also nondecreasing_series *)
Lemma ereal_nondecreasing_series (R : realDomainType) (u_ : {ereal R} ^nat) :
  (forall n, 0%:E <= u_ n)%E ->
  nondecreasing_seq (fun n => \sum_(i < n) u_ i)%E.
Proof.
move=> u_ge0 n m nm; rewrite -(subnKC nm).
rewrite -[X in (_ <= X)%E](big_mkord xpredT) /index_iota subn0 iota_add.
rewrite big_cat -[in X in (_ <= X + _)%E](subn0 n) big_mkord lee_addl //=.
by rewrite sume_ge0.
Qed.

Lemma ereal_nneg_series_lim_ge (R : realType) (u_ : {ereal R} ^nat) k :
  (forall n, (0%:E <= u_ n)%E) ->
  (\sum_(i < k) u_ i <= lim (fun n : nat => \sum_(i < n) u_ i))%E.
Proof.
move/ereal_nondecreasing_series/nondecreasing_seq_ereal_cvg/cvg_lim => -> //.
by apply ereal_sup_ub; exists k.
Qed.

Lemma is_cvg_ereal_nneg_series_cond (R : realType) (u_ : {ereal R} ^nat)
  (P : pred nat) : (forall n, P n -> (0%:E <= u_ n)%E) ->
  cvg (fun n : nat => (\sum_(i < n | P i) u_ i)%E).
Proof.
move/lee_sum_nneg_ord/nondecreasing_seq_ereal_cvg => cu.
by apply/cvg_ex; eexists; exact: cu.
Qed.

Lemma is_cvg_ereal_nneg_series (R : realType) (u_ : {ereal R} ^nat) :
  (forall n, (0%:E <= u_ n)%E) -> cvg (fun n : nat => (\sum_(i < n) u_ i)%E).
Proof. by move=> ?; exact: (@is_cvg_ereal_nneg_series_cond _ _ xpredT). Qed.

Lemma ereal_nneg_series_lim_ge0 (R : realType) (u_ : {ereal R} ^nat) :
  (forall n, (0%:E <= u_ n)%E) ->
  (0%:E <= lim (fun n : nat => \sum_(i < n) u_ i))%E.
Proof.
move=> u0; apply: (ereal_lim_ge (is_cvg_ereal_nneg_series u0)).
by near=> k; rewrite sume_ge0 // => i; apply: u0.
Grab Existential Variables. all: end_near. Qed.

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

Lemma lee_lim (R : realType) (u_ v_ : {ereal R} ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, (u_ n <= v_ n)%E) -> (lim u_ <= lim v_)%E.
Proof.
move=> cu cv uv; move lu : (lim u_) => l; move kv : (lim v_) => k.
case: l k => [l| |] [k| |] // in lu kv *.
- have /ereal_cvg_real[realu ul] : u_ --> l%:E by rewrite -lu.
  have /ereal_cvg_real[realv vk] : v_ --> k%:E by rewrite -kv.
  rewrite -(cvg_lim (@Rhausdorff R) ul) -(cvg_lim (@Rhausdorff R) vk).
  apply: ler_lim.
  + by apply/cvg_ex; eexists; exact: ul.
  + by apply/cvg_ex; eexists; exact: vk.
  + move: uv realu realv => [n1 _ uv] [n2 _ realu] [n3 _ realv].
    near=> n; have : (n >= maxn n1 (maxn n2 n3))%N.
      by near: n; exists (maxn n1 (maxn n2 n3)).
    rewrite !geq_max => /and3P[n1n n2n n3n]; rewrite -lee_fin.
    rewrite -(ERFin_real_of_er (realu _ n2n)).
    by rewrite -(ERFin_real_of_er (realv _ n3n)) uv.
- by rewrite lee_pinfty.
- exfalso.
  have /ereal_cvg_real [realu ul] : u_ --> l%:E by rewrite -lu.
  have /ereal_cvgPninfty voo : v_ --> -oo%E by rewrite -kv.
  have /cvg_has_inf [uT0 [M uTM]] : cvg (real_of_er \o u_ : _ -> R^o).
    by apply/cvg_ex; exists l.
  have {}/voo [n1 _ vM] : minr (M - 1) (-1) < 0 by rewrite lt_minl ltrN10 orbT.
  move: uv realu => [n2 _ uv] [n3 _ realu].
  near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  move/vM : (n1n) => {}vM.
  suff : (v_ n < u_ n)%E by apply/negP; rewrite -leNgt uv.
  rewrite (le_lt_trans vM) // (@lt_le_trans _ _ M%:E) //.
    by rewrite lte_fin lt_minl ltr_subl_addl ltr_addr ltr01.
  by rewrite (ERFin_real_of_er (realu _ n3n)) lee_fin; apply uTM; exists n.
- exfalso.
  have /ereal_cvg_real [realv vk] : v_ --> k%:E by rewrite -kv.
  have /ereal_cvgPpinfty uoo : u_ --> +oo%E by rewrite -lu.
  have /cvg_has_sup [vT0 [M vTM]] : cvg (real_of_er \o v_ : _ -> R^o).
    by apply/cvg_ex; exists k.
  have {}/uoo [n1 _ uM] : 0 < maxr (M + 1) 1 by rewrite lt_maxr ltr01 orbT.
  move: uv realv => [n2 _ uv] [n3 _ realv]; near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  move/uM : (n1n) => {}uM.
  suff : (v_ n < u_ n)%E by apply/negP; rewrite -leNgt uv.
  rewrite (@le_lt_trans _ _ M%:E) //.
    by rewrite (ERFin_real_of_er (realv _ n3n)) lee_fin; apply vTM; exists n.
  by rewrite (lt_le_trans _ uM) // lte_fin lt_maxr ltr_addl ltr01.
- exfalso.
  have /ereal_cvgPpinfty uoo : u_ --> +oo%E by rewrite -lu.
  have /ereal_cvgPninfty voo : v_ --> -oo%E by rewrite -kv.
  move: uv => [n1 _ uv].
  have [n2 _ {}uoo] := uoo _ ltr01.
  have [n3 _ {}voo] := voo _ (@ltrN10 R).
  near \oo => n.
  have : (n >= maxn n1 (maxn n2 n3))%N by near: n; exists (maxn n1 (maxn n2 n3)).
  rewrite 2!geq_max => /and3P[n1n n2n n3n].
  suff : (v_ n < u_ n)%E by apply/negP; rewrite -leNgt; apply uv.
  rewrite (@lt_trans _ _ 0%:E) //.
    by rewrite (le_lt_trans (voo _ n3n)) // lte_fin ltrN10.
  by rewrite (lt_le_trans _ (uoo _ n2n)) // lte_fin ltr01.
- by rewrite lee_ninfty.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_pinfty_fin (R : realType) (f g : {ereal R} ^nat) b :
  f --> +oo%E -> g --> b%:E -> (f \+ g)%E --> +oo%E.
Proof.
move=> /ereal_cvgPpinfty foo /ereal_cvg_real -[realg gb].
apply/ereal_cvgPpinfty => A A0.
have : cvg (real_of_er \o g : _ -> R^o) by apply/cvg_ex; exists b.
move/cvg_has_inf => -[gT0 [M gtM]].
have /foo[m _ {}foo] : 0 < maxr A (A - M)%R by rewrite lt_maxr A0.
case: realg => k _ realg.
near=> n.
have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn] /realg /ERFin_real_of_er ->.
rewrite -lee_subl_addr -subERFin (le_trans _ (foo _ mn)) // lee_fin.
by rewrite le_maxr; apply/orP; right; apply ler_sub => //; apply gtM; exists n.
Grab Existential Variables. all: end_near. Qed.

Lemma ereal_cvgD_ninfty_fin (R : realType) (f g : {ereal R} ^nat) b :
  f --> -oo%E -> g --> b%:E -> (f \+ g)%E --> -oo%E.
Proof.
move=> /ereal_cvgPninfty foo /ereal_cvg_real -[realg gb].
apply/ereal_cvgPninfty => A A0.
have : cvg (real_of_er \o g : _ -> R^o) by apply/cvg_ex; exists b.
move/cvg_has_sup => -[gT0 [M gtM]].
have /foo [m _ {}foo] : minr A (A - M)%R < 0 by rewrite lt_minl A0.
case: realg => k _ realg.
near=> n.
have : (n >= maxn m k)%N by near: n; exists (maxn m k).
rewrite geq_max => /andP[mn].
move/realg => /ERFin_real_of_er ->.
rewrite -lee_subr_addr -subERFin (le_trans (foo _ mn)) // lee_fin.
by rewrite  le_minl; apply/orP; right; apply ler_sub => //; apply gtM; exists n.
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

Lemma ereal_cvgD (R : realType) (f g : {ereal R} ^nat) a b :
  ~~ adde_undef a b ->
  f --> a -> g --> b -> (f \+ g)%E --> (a + b)%E.
Proof.
move: a b => [a| |] [b| |] // _.
- case/ereal_cvg_real => [[na _ foo] fa].
  case/ereal_cvg_real => [[nb _ goo] gb].
  apply/ereal_cvg_real; split.
    exists (maxn na nb) => // n; rewrite /= geq_max => /andP[nan nbn].
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
Proof. 
move=> cf cg fg; apply/(@cvg_lim _ _ ((f \+ g)%E @ \oo)) => //=. (* BUG *)
exact: ereal_cvgD.
Qed.

End sequences_of_extended_real_numbers.
