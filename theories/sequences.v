(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions set_interval mathcomp_extra.
Require Import reals ereal signed topology normedtype landau.

(******************************************************************************)
(*                Definitions and lemmas about sequences                      *)
(*                                                                            *)
(* The purpose of this file is to gather generic definitions and lemmas about *)
(* sequences.                                                                 *)
(*                                                                            *)
(* * About sequences of real numbers:                                         *)
(*        [sequence u_n]_n == the sequence of general element u_n             *)
(*                  R ^nat == notation for the type of sequences, i.e.,       *)
(*                            functions of type nat -> R                      *)
(*                 seqDU F == sequence F_0, F_1 \ F_0, F_2 \ (F_0 U F_1),...  *)
(*                  seqD F == the sequence F_0, F_1 \ F_0, F_2 \ F_1,...      *)
(*               series u_ == the sequence of partial sums of u_              *)
(*            telescope u_ := [sequence u_ n.+1 - u_ n]_n                     *)
(*                harmonic == harmonic sequence                               *)
(*              arithmetic == arithmetic sequence                             *)
(*               geometric == geometric sequence                              *)
(*                            also arithmetic_mean, harmonic_mean,            *)
(*                            root_mean_square                                *)
(*          [series u_n]_n == the series of general element u_n               *)
(*              [normed S] == transforms a series S = [series u_n]_n in its   *)
(*                            normed series [series `|u_n|]_n] (useful to     *)
(*                            represent absolute and normed convergence:      *)
(*                            cvg [norm S_n])                                 *)
(*             exp_coeff n == the sequence of coefficients of the real        *)
(*                            exponential                                     *)
(*                  expR x == the exponential function defined on a realType  *)
(* is_cvg_series_exp_coeff == convergence of \sum_n^+oo x^n / n!              *)
(*                                                                            *)
(*        \sum_<range> F i == lim (fun n => (\sum_<range>) F i)) where        *)
(*                            <range> can be (i <oo), (i <oo | P i),          *)
(*                            (m <= i <oo), or (m <= i <oo | P i)             *)
(*                                                                            *)
(* Sections sequences_R_* contain properties of sequences of real numbers.    *)
(* For example:                                                               *)
(* nonincreasing_cvg_ge u_ == if u_ is nonincreasing and convergent then      *)
(*                            forall n, lim u_ <= u_ n                        *)
(* nondecreasing_cvg_le u_ == if u_ is nondecreasing and convergent then      *)
(*                            forall n, lim u_ >= u_ n                        *)
(*    nondecreasing_cvg u_ == if u_ is nondecreasing and bounded then u_      *)
(*                            is convergent and its limit is sup u_n          *)
(*    nonincreasing_cvg u_ == if u_ is nonincreasing u_ and bound by below    *)
(*                            then u_ is convergent                           *)
(*                adjacent == adjacent sequences lemma                        *)
(*                  cesaro == Cesaro's lemma                                  *)
(*                                                                            *)
(* * About sequences of natural numbers:                                      *)
(*   nseries                                                                  *)
(*                                                                            *)
(* * About sequences of extended real numbers:                                *)
(*   eseries, etelescope, etc.                                                *)
(*                                                                            *)
(* Section sequences_ereal contain properties of sequences of extended real   *)
(* numbers.                                                                   *)
(*                                                                            *)
(*   Naming convention: lemmas about series of non-negative (resp. non-       *)
(*   positive) extended numbers use the string "nneseries" (resp. "npeseries")*)
(*   as part of their identifier                                              *)
(*                                                                            *)
(* * Limit superior and inferior:                                             *)
(*             sdrop u n := {u_k | k >= n}                                    *)
(*                sups u := [sequence sup (sdrop u n)]_n                      *)
(*                infs u := [sequence inf (sdrop u n)]_n                      *)
(*         lim_{inf,sup} == limit inferior/superior for realType              *)
(*               esups u := [sequence ereal_sup (sdrop u n)]_n                *)
(*               einfs u := [sequence ereal_inf (sdrop u n)]_n                *)
(*        lim_e{inf,sup} == limit inferior/superior for \bar R                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "R ^nat" (at level 0).
Reserved Notation "a `^ x" (at level 11).
Reserved Notation "[ 'sequence' E ]_ n"
  (at level 0, E at level 200, n name, format "[ 'sequence'  E ]_ n").
Reserved Notation "[ 'series' E ]_ n"
  (at level 0, E at level 0, n name, format "[ 'series'  E ]_ n").
Reserved Notation "[ 'normed' E ]"  (at level 0, format "[ 'normed'  E ]").

Reserved Notation "\big [ op / idx ]_ ( m <= i <oo | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <oo  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i <oo ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <oo ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <oo | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  <oo |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <oo ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  <oo )  F ']'").

Reserved Notation "\sum_ ( m <= i '<oo' | P ) F"
  (at level 41, F at level 41, i, m at level 50,
           format "'[' \sum_ ( m  <=  i  <oo  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i '<oo' ) F"
  (at level 41, F at level 41, i, m at level 50,
           format "'[' \sum_ ( m  <=  i  <oo ) '/  '  F ']'").
Reserved Notation "\sum_ ( i '<oo' | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  <oo  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i '<oo' ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  <oo ) '/  '  F ']'").

Definition sequence R := nat -> R.
Definition mk_sequence R f : sequence R := f.
Arguments mk_sequence R f /.
Notation "[ 'sequence' E ]_ n" := (mk_sequence (fun n => E%E)) : ereal_scope.
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

Lemma nondecreasing_seqP (d : unit) (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n <= u_ n.+1)%O <-> nondecreasing_seq u_.
Proof. by split=> [|h n]; [exact: homo_leq le_trans | exact: h]. Qed.

Lemma nonincreasing_seqP (d : unit) (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n >= u_ n.+1)%O <-> nonincreasing_seq u_.
Proof.
split; first by apply: homo_leq (fun _ _ _ u v => le_trans v u).
by move=> u_nincr n; exact: u_nincr.
Qed.

Lemma increasing_seqP (d : unit) (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n < u_ n.+1)%O <-> increasing_seq u_.
Proof.
split; first by move=> u_nondec; apply: le_mono; apply: homo_ltn lt_trans _.
by move=> u_incr n; rewrite lt_neqAle eq_le !u_incr leqnSn ltnn.
Qed.

Lemma decreasing_seqP (d : unit) (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n > u_ n.+1)%O <-> decreasing_seq u_.
Proof.
split.
  move=> u_noninc.
  (* FIXME: add shortcut to order.v *)
  apply: (@total_homo_mono _ T u_ leq ltn _ _ leqnn _ ltn_neqAle
    _ (fun _ _ _ => esym (le_anti _)) leq_total
    (homo_ltn (fun _ _ _ u v => lt_trans v u) u_noninc)) => //.
  by move=> x y; rewrite eq_sym -lt_neqAle.
by move=> u_decr n; rewrite lt_neqAle eq_le !u_decr !leqnSn ltnn.
Qed.
(* TODO (maybe): variants for near \oo ?? *)

Lemma lef_at (aT : Type) d (T : porderType d) (f : (aT -> T)^nat) x :
  nondecreasing_seq f -> {homo (f^~ x) : n m / (n <= m)%N >-> (n <= m)%O}.
Proof. by move=> nf m n mn; have /asboolP := nf _ _ mn; exact. Qed.

Lemma nondecreasing_seqD T (d : unit) (R : numDomainType) (f g : (T -> R)^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) ->
  (forall x, nondecreasing_seq (g ^~ x)) ->
  (forall x, nondecreasing_seq ((f \+ g) ^~ x)).
Proof. by move=> ndf ndg t m n mn; apply: ler_add; [exact/ndf|exact/ndg]. Qed.

Local Notation eqolimn := (@eqolim _ _ _ eventually_filter).
Local Notation eqolimPn := (@eqolimP _ _ _ eventually_filter).

(*********************)
(* Sequences of sets *)
(*********************)

Section seqDU.
Variables (T : Type).
Implicit Types F : (set T)^nat.

Definition seqDU F n := F n `\` \big[setU/set0]_(k < n) F k.

Lemma trivIset_seqDU F : trivIset setT (seqDU F).
Proof.
move=> i j _ _; wlog ij : i j / (i < j)%N => [/(_ _ _ _) tB|].
  by have [ij /tB->|ij|] := ltngtP i j; rewrite //setIC => /tB ->.
move=> /set0P; apply: contraNeq => _; apply/eqP.
rewrite /seqDU 2!setDE !setIA setIC (bigD1 (Ordinal ij)) //=.
by rewrite setCU setIAC !setIA setICl !set0I.
Qed.

Lemma bigsetU_seqDU F n :
  \big[setU/set0]_(k < n) F k = \big[setU/set0]_(k < n) seqDU F k.
Proof.
elim: n => [|n ih]; first by rewrite 2!big_ord0.
rewrite !big_ord_recr /= predeqE => t; split=> [[Ft|Fnt]|[Ft|[Fnt Ft]]].
- by left; rewrite -ih.
- have [?|?] := pselect ((\big[setU/set0]_(i < n) seqDU F i) t); first by left.
  by right; split => //; rewrite ih.
- by left; rewrite ih.
- by right.
Qed.

Lemma seqDU_bigcup_eq F : \bigcup_k F k = \bigcup_k seqDU F k.
Proof.
rewrite /seqDU predeqE => t; split=> [[n _ Fnt]|[n _]]; last first.
  by rewrite setDE => -[? _]; exists n.
have [UFnt|UFnt] := pselect ((\big[setU/set0]_(k < n) F k) t); last by exists n.
suff [m [Fmt FNmt]] : exists m, F m t /\ forall k, (k < m)%N -> ~ F k t.
  by exists m => //; split => //; rewrite -bigcup_mkord => -[k kj]; exact: FNmt.
move: UFnt; rewrite -bigcup_mkord => -[/= k _ Fkt] {Fnt n}.
have [n kn] := ubnP k; elim: n => // n ih in t k Fkt kn *.
case: k => [|k] in Fkt kn *; first by exists O.
have [?|] := pselect (forall m, (m <= k)%N -> ~ F m t); first by exists k.+1.
move=> /existsNP[i] /not_implyP[ik] /contrapT Fit; apply (ih t i) => //.
by rewrite (leq_ltn_trans ik).
Qed.

End seqDU.
#[global] Hint Resolve trivIset_seqDU : core.

Section seqD.
Variable T : Type.
Implicit Types F : (set T) ^nat.

Definition seqD F := fun n => if n isn't n'.+1 then F O else F n `\` F n'.

Lemma seqDU_seqD F : nondecreasing_seq F -> seqDU F = seqD F.
Proof.
move=> ndF; rewrite funeqE => -[|n] /=; first by rewrite /seqDU big_ord0 setD0.
rewrite /seqDU big_ord_recr /= setUC; congr (_ `\` _); apply/setUidPl.
by rewrite -bigcup_mkord => + [k /= kn]; exact/subsetPset/ndF/ltnW.
Qed.

Lemma trivIset_seqD F : nondecreasing_seq F -> trivIset setT (seqD F).
Proof. by move=> ndF; rewrite -seqDU_seqD //; exact: trivIset_seqDU. Qed.

Lemma bigsetU_seqD F n :
  \big[setU/set0]_(i < n) F i = \big[setU/set0]_(i < n) seqD F i.
Proof.
case: n => [|n]; first by rewrite 2!big_ord0.
elim: n => [|n ih]; first by rewrite !big_ord_recl !big_ord0.
rewrite big_ord_recr [in RHS]big_ord_recr /= -{}ih predeqE => x; split.
  move=> [?|?]; first by left.
  have [?|?] := pselect (F n x); last by right.
  by left; rewrite big_ord_recr /=; right.
by move=> [?|[? ?]]; [left | right].
Qed.

Lemma setU_seqD F : nondecreasing_seq F ->
  forall n, F n.+1 = F n `|` seqD F n.+1.
Proof.
move=> ndF n; rewrite /seqD funeqE => x; rewrite propeqE; split.
by move=> ?; have [?|?] := pselect (F n x); [left | right].
by move=> -[|[]//]; move: x; exact/subsetPset/ndF.
Qed.

Lemma eq_bigsetU_seqD F n : nondecreasing_seq F ->
  F n = \big[setU/set0]_(i < n.+1) seqD F i.
Proof.
move=> ndF; elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
- by move=> ?; rewrite big_ord_recl big_ord0; left.
- by rewrite big_ord_recl big_ord0 setU0.
- rewrite (setU_seqD ndF) => -[|/=].
  by rewrite big_ord_recr /= -ih => Fnx; left.
  by move=> -[Fn1x Fnx]; rewrite big_ord_recr /=; right.
- by rewrite big_ord_recr /= -ih => -[|[]//]; move: x; exact/subsetPset/ndF.
Qed.

Lemma eq_bigcup_seqD F : \bigcup_n F n = \bigcup_n seqD F n.
Proof.
rewrite funeqE => x; rewrite propeqE; split.
  case; elim=> [_ F0x|n ih _ Fn1x]; first by exists O.
  have [|Fnx] := pselect (F n x); last by exists n.+1.
  by move=> /(ih I)[m _ Fmx]; exists m.
case; elim=> [_ /= F0x|n ih _ /= [Fn1x Fnx]]; by [exists O | exists n.+1].
Qed.

Lemma eq_bigcup_seqD_bigsetU F :
  \bigcup_n (seqD (fun n => \big[setU/set0]_(i < n.+1) F i) n) = \bigcup_n F n.
Proof.
rewrite -(@eq_bigcup_seqD (fun n => \big[setU/set0]_(i < n.+1) F i)).
rewrite eqEsubset; split => [t [i _]|t [i _ Fit]].
  by rewrite -bigcup_set_cond => -[/= j _ Fjt]; exists j.
by exists i => //; rewrite big_ord_recr /=; right.
Qed.

End seqD.

(************************************)
(* Convergence of patched sequences *)
(************************************)

Section sequences_patched.
(* TODO: generalizations to numDomainType *)

Section NatShift.

Variables (N : nat) (V : topologicalType).
Implicit Types (f : nat -> V) (u : V ^nat)  (l : V).

Lemma cvg_restrict f u_ l :
  ([sequence if (n <= N)%N then f n else u_ n]_n @ \oo --> l) =
  (u_ @ \oo --> l).
Proof.
rewrite propeqE; split; apply: cvg_trans; apply: near_eq_cvg;
by near do [move=> /=; case: ifP => //; rewrite ltn_geF//].
Unshelve. all: by end_near. Qed.

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
by apply: near_eq_cvg; near do rewrite subnK; exists N.
Unshelve. all: by end_near. Qed.

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
Implicit Types u v : R ^nat.

Lemma __deprecated__squeeze T (f g h : T -> R) (a : filter_on T) :
  (\forall x \near a, f x <= g x <= h x) -> forall (l : R),
  f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof. exact: squeeze_cvgr. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `squeeze_cvgr`")]
Notation squeeze := __deprecated__squeeze.

Lemma __deprecated__cvgPpinfty (u_ : R ^nat) :
  u_ --> +oo <-> forall A, \forall n \near \oo, A <= u_ n.
Proof. exact: cvgryPge. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgryPge`, and generalized to any filter")]
Notation cvgPpinfty := __deprecated__cvgPpinfty.

Lemma __deprecated__cvgNpinfty u_ : (- u_ --> +oo) = (u_ --> -oo).
Proof. exact/propeqP/cvgNry. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgNry` instead")]
Notation cvgNpinfty := __deprecated__cvgNpinfty.

Lemma __deprecated__cvgNninfty u_ : (- u_ --> -oo) = (u_ --> +oo).
Proof. exact/propeqP/cvgNrNy. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgNrNy` instead")]
Notation cvgNninfty := __deprecated__cvgNninfty.

Lemma __deprecated__cvgPninfty (u_ : R ^nat) :
  u_ --> -oo <-> forall A, \forall n \near \oo, A >= u_ n.
Proof. exact: cvgrNyPle. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrNyPle`, and generalized to any filter")]
Notation cvgPninfty := __deprecated__cvgPninfty.

Lemma __deprecated__ger_cvg_pinfty u_ v_ : (\forall n \near \oo, u_ n <= v_ n) ->
  u_ --> +oo -> v_ --> +oo.
Proof. exact: ger_cvgy. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `ger_cvgy`, and generalized to any filter")]
Notation ger_cvg_pinfty := __deprecated__ger_cvg_pinfty.

Lemma __deprecated__ler_cvg_ninfty v_ u_ : (\forall n \near \oo, u_ n <= v_ n) ->
  v_ --> -oo -> u_ --> -oo.
Proof. exact: ler_cvgNy. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `ler_cvgNy`, and generalized to any filter")]
Notation ler_cvg_ninfty := __deprecated__ler_cvg_ninfty.

Lemma __deprecated__lim_ge x u : cvg u -> (\forall n \near \oo, x <= u n) -> x <= lim u.
Proof. exact: limr_ge. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `limr_ge`, and generalized to any proper filter")]
Notation lim_ge := __deprecated__lim_ge.

Lemma __deprecated__lim_le x u : cvg u -> (\forall n \near \oo, x >= u n) -> x >= lim u.
Proof. exact: limr_le. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `limr_le`, and generalized to any proper filter")]
Notation lim_le := __deprecated__lim_le.

Lemma lt_lim u (M : R) : nondecreasing_seq u -> cvg u -> M < lim u ->
  \forall n \near \oo, M <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, M <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have {}Mu : forall x, M > u x by move=> x; rewrite ltNge; apply/negP.
have : lim u <= M by apply: limr_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near. Qed.

Lemma nonincreasing_cvg_ge u_ : nonincreasing_seq u_ -> cvg u_ ->
  forall n, lim u_ <= u_ n.
Proof.
move=> du ul p; rewrite leNgt; apply/negP => up0.
move/cvgrPdist_lt : ul => /(_ `|u_ p - lim u_|%R).
rewrite {1}ltr0_norm ?subr_lt0 // opprB subr_gt0 => /(_ up0) ul.
near \oo => N.
have /du uNp : (p <= N)%nat by near: N; rewrite nearE; exists p.
have : `|lim u_ - u_ N| >= `|u_ p - lim u_|%R.
 rewrite ltr0_norm // ?subr_lt0 // opprB distrC.
 rewrite (@le_trans _ _ (lim u_ - u_ N)) // ?ler_sub //.
 rewrite (_ : `| _ | = `|u_ N - lim u_|%R) // ler0_norm // ?opprB //.
 by rewrite subr_le0 (le_trans _ (ltW up0)).
rewrite leNgt => /negP; apply; by near: N.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_cvg_le u_ : nondecreasing_seq u_ -> cvg u_ ->
  forall n, u_ n <= lim u_.
Proof.
move=> iu cu n; move: (@nonincreasing_cvg_ge (- u_)).
rewrite -nondecreasing_opp opprK => /(_ iu); rewrite is_cvgNE => /(_ cu n).
by rewrite limN // ler_oppl opprK.
Qed.

Lemma cvg_has_ub u_ : cvg u_ -> has_ubound [set `|u_ n| | n in setT].
Proof.
move=> /cvg_seq_bounded/pinfty_ex_gt0[M M_gt0 /= uM].
by exists M; apply/ubP => x -[n _ <-{x}]; exact: uM.
Qed.

Lemma cvg_has_sup u_ : cvg u_ -> has_sup (u_ @` setT).
Proof.
move/cvg_has_ub; rewrite -/(_ @` _) -(image_comp u_ normr setT).
by move=> /has_ub_image_norm uM; split => //; exists (u_ 0%N), 0%N.
Qed.

Lemma cvg_has_inf u_ : cvg u_ -> has_inf (u_ @` setT).
Proof. by move/is_cvgN/cvg_has_sup; rewrite -has_inf_supN image_comp. Qed.

Lemma __deprecated__cvgPpinfty_lt (u_ : R ^nat) :
  u_ --> +oo%R <-> forall A, \forall n \near \oo, (A < u_ n)%R.
Proof. exact: cvgryPgt. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgryPgt`, and generalized to any proper filter")]
Notation cvgPpinfty_lt := __deprecated__cvgPpinfty_lt.

Lemma __deprecated__cvgPninfty_lt (u_ : R ^nat) :
  u_ --> -oo%R <-> forall A, \forall n \near \oo, (A > u_ n)%R.
Proof. exact: cvgrNyPlt. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrNyPlt`, and generalized to any proper filter")]
Notation cvgPninfty_lt := __deprecated__cvgPninfty_lt.

Lemma __deprecated__cvgPpinfty_near (u_ : R ^nat) :
  u_ --> +oo%R <-> \forall A \near +oo, \forall n \near \oo, (A <= u_ n)%R.
Proof. exact: cvgryPgey. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgryPgey`, and generalized to any proper filter")]
Notation cvgPpinfty_near := __deprecated__cvgPpinfty_near.

Lemma __deprecated__cvgPninfty_near (u_ : R ^nat) :
  u_ --> -oo%R <-> \forall A \near -oo, \forall n \near \oo, (A >= u_ n)%R.
Proof. exact: cvgrNyPleNy. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrNyPleNy`, and generalized to any proper filter")]
Notation cvgPninfty_near := __deprecated__cvgPninfty_near.

Lemma __deprecated__cvgPpinfty_lt_near (u_ : R ^nat) :
  u_ --> +oo%R <-> \forall A \near +oo, \forall n \near \oo, (A < u_ n)%R.
Proof. exact: cvgryPgty. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgryPgty`, and generalized to any proper filter")]
Notation cvgPpinfty_lt_near := __deprecated__cvgPpinfty_lt_near.

Lemma __deprecated__cvgPninfty_lt_near (u_ : R ^nat) :
  u_ --> -oo%R <-> \forall A \near -oo, \forall n \near \oo, (A > u_ n)%R.
Proof. exact: cvgrNyPltNy. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrNyPltNy`, and generalized to any proper filter")]
Notation cvgPninfty_lt_near := __deprecated__cvgPninfty_lt_near.

End sequences_R_lemmas_realFieldType.

Lemma __deprecated__invr_cvg0 (R : realFieldType) (u : R^nat) :
  (forall i, 0 < u i) -> ((u i)^-1 @[i --> \oo] --> 0) <-> (u --> +oo).
Proof. by move=> ?; rewrite gtr0_cvgV0//; apply: nearW. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `gtr0_cvgV0` and generalized")]
Notation invr_cvg0 := __deprecated__invr_cvg0.

Lemma __deprecated__invr_cvg_pinfty (R : realFieldType) (u : R^nat) :
  (forall i, 0 < u i) -> ((u i)^-1 @[i --> \oo] --> +oo) <-> (u --> 0).
Proof. by move=> ?; rewrite cvgrVy//; apply: nearW. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrVy` and generalized")]
Notation invr_cvg_pinfty := __deprecated__invr_cvg_pinfty.

Section partial_sum.
Variables (V : zmodType) (u_ : V ^nat).

Definition series : V ^nat := [sequence \sum_(0 <= k < n) u_ k]_n.
Definition telescope : V ^nat := [sequence u_ n.+1 - u_ n]_n.

Lemma seriesEnat : series = [sequence \sum_(0 <= k < n) u_ k]_n.
Proof. by []. Qed.

Lemma seriesEord : series = [sequence \sum_(k < n) u_ k]_n.
Proof. by rewrite funeqE => n; rewrite /series/= big_mkord. Qed.

Lemma seriesSr n : series n.+1 = series n + u_ n.
Proof. by rewrite !seriesEord/= big_ord_recr. Qed.

Lemma seriesS n : series n.+1 = u_ n + series n.
Proof. by rewrite addrC seriesSr. Qed.

Lemma seriesSB (n : nat) : series n.+1 - series n = u_ n.
Proof. by rewrite seriesS addrK. Qed.

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

Lemma seriesN (V : zmodType) (f : V ^nat) : series (- f) = - series f.
Proof. by rewrite funeqE => n; rewrite /series /= sumrN. Qed.

Lemma seriesD (V : zmodType) (f g : V ^nat) : series (f + g) = series f + series g.
Proof. by rewrite /series /= funeqE => n; rewrite big_split. Qed.

Lemma seriesZ (R : ringType) (V : lmodType R) (f : V ^nat) k :
  series (k *: f) = k *: series f.
Proof. by rewrite funeqE => n; rewrite /series /= -scaler_sumr. Qed.

Section partial_sum_numFieldType.
Variables V : numFieldType.
Implicit Types f g : V ^nat.

Lemma is_cvg_seriesN f : cvg (series (- f)) = cvg (series f).
Proof. by rewrite seriesN is_cvgNE. Qed.

Lemma lim_seriesN f : cvg (series f) -> lim (series (- f)) = - lim (series f).
Proof. by move=> cf; rewrite seriesN limN. Qed.

Lemma is_cvg_seriesZ f k : cvg (series f) -> cvg (series (k *: f)).
Proof. by move=> cf; rewrite seriesZ; exact: is_cvgZr. Qed.

Lemma lim_seriesZ f k : cvg (series f) ->
  lim (series (k *: f)) = k *: lim (series f).
Proof. by move=> cf; rewrite seriesZ limZr. Qed.

Lemma is_cvg_seriesD f g :
  cvg (series f) -> cvg (series g) -> cvg (series (f + g)).
Proof. by move=> cf cg; rewrite seriesD; exact: is_cvgD. Qed.

Lemma lim_seriesD f g : cvg (series f) -> cvg (series g) ->
  lim (series (f + g)) = lim (series f) + lim (series g).
Proof. by move=> cf cg; rewrite seriesD limD. Qed.

Lemma is_cvg_seriesB f g :
  cvg (series f) -> cvg (series g) -> cvg (series (f - g)).
Proof. by move=> cf cg; apply: is_cvg_seriesD; rewrite ?is_cvg_seriesN. Qed.

Lemma lim_seriesB f g : cvg (series f) -> cvg (series g) ->
  lim (series (f - g)) = lim (series f) - lim (series g).
Proof. by move=> Cf Cg; rewrite lim_seriesD ?is_cvg_seriesN// lim_seriesN. Qed.

End partial_sum_numFieldType.

Lemma lim_series_le (V : realFieldType) (f g : V ^nat) :
  cvg (series f) -> cvg (series g) -> (forall n, f n <= g n) ->
  lim (series f) <= lim (series g).
Proof.
by move=> cf cg fg; apply (ler_lim cf cg); near=> x; rewrite ler_sum.
Unshelve. all: by end_near. Qed.

Lemma telescopeK (V : zmodType) (u_ : V ^nat) :
  series (telescope u_) = [sequence u_ n - u_ 0%N]_n.
Proof. by rewrite funeqE => n; rewrite seriesEnat/= telescope_sumr. Qed.

Lemma seriesK (V : zmodType) : cancel (@series V) telescope.
Proof. move=> ?; exact/funext/seriesSB. Qed.

Lemma eq_sum_telescope (V : zmodType) (u_ : V ^nat) n :
  u_ n = u_ 0%N + series (telescope u_) n.
Proof. by rewrite telescopeK/= addrC addrNK. Qed.

Section series_patched.
Variables (N : nat) (K : numFieldType) (V : normedModType K).
Implicit Types (f : nat -> V) (u : V ^nat)  (l : V).

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

Lemma nondecreasing_cvg (u_ : R ^nat) :
    nondecreasing_seq u_ -> has_ubound (range u_) ->
  u_ --> sup (range u_).
Proof.
move=> leu u_ub; set M := sup (range u_).
have su_ : has_sup (range u_) by split => //; exists (u_ 0%N), 0%N.
apply/cvgrPdist_le => _/posnumP[e].
have [p /andP[Mu_p u_pM]] : exists p, M - e%:num <= u_ p <= M.
  have [_ -[p _] <- /ltW Mu_p] := sup_adherent (gt0 e) su_.
  by exists p; rewrite Mu_p; have /ubP := sup_upper_bound su_; apply; exists p.
near=> n; have pn : (p <= n)%N by near: n; exact: nbhs_infty_ge.
rewrite ler_distlC (le_trans Mu_p (leu _ _ _))//= (@le_trans _ _ M) ?ler_addl//.
by have /ubP := sup_upper_bound su_; apply; exists n.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_is_cvg (u_ : R ^nat) :
  nondecreasing_seq u_ -> has_ubound (range u_) -> cvg u_.
Proof. by move=> u_nd u_ub; apply: cvgP; apply: nondecreasing_cvg. Qed.

Lemma nondecreasing_dvg_lt (u_ : R ^nat) :
  nondecreasing_seq u_ -> ~ cvg u_ -> u_ --> +oo.
Proof.
move=> nu du; apply: contrapT => /cvgryPge/existsNP[l lu]; apply: du.
apply: nondecreasing_is_cvg => //; exists l => _ [n _ <-].
rewrite leNgt; apply/negP => lun; apply: lu; near=> m.
by rewrite (le_trans (ltW lun)) //; apply: nu; near: m; exists n.
Unshelve. all: by end_near. Qed.

Lemma near_nondecreasing_is_cvg (u_ : R ^nat) (M : R) :
    {near \oo, nondecreasing_seq u_} -> (\forall n \near \oo, u_ n <= M) ->
  cvg u_.
Proof.
move=> [k _ u_nd] [k' _ u_M]; suff : cvg [sequence u_ (n + maxn k k')%N]_n.
  by case/cvg_ex => /= l; rewrite cvg_shiftn => ul; apply/cvg_ex; exists l.
apply: nondecreasing_is_cvg; [move=> /= m n mn|exists M => _ [n _ <-]].
  by rewrite u_nd ?leq_add2r//= (leq_trans (leq_maxl _ _) (leq_addl _ _)).
by rewrite u_M //= (leq_trans (leq_maxr _ _) (leq_addl _ _)).
Qed.

Lemma nonincreasing_cvg (u_ : R ^nat) :
    nonincreasing_seq u_ -> has_lbound (range u_) ->
  u_ --> inf (u_ @` setT).
Proof.
rewrite -nondecreasing_opp => u_nd u_lb; rewrite -[X in X --> _](opprK u_).
apply: cvgN; rewrite image_comp; apply: nondecreasing_cvg => //.
by move/has_lb_ubN : u_lb; rewrite image_comp.
Qed.

Lemma nonincreasing_is_cvg (u_ : R ^nat) :
  nonincreasing_seq u_ -> has_lbound (range u_) -> cvg u_.
Proof. by move=> u_decr u_bnd; apply: cvgP; apply: nonincreasing_cvg. Qed.

Lemma near_nonincreasing_is_cvg (u_ : R ^nat) (m : R) :
    {near \oo, nonincreasing_seq u_} -> (\forall n \near \oo, m <= u_ n) ->
  cvg u_.
Proof.
move=> u_ni u_m.
rewrite -(opprK u_); apply: is_cvgN; apply/(@near_nondecreasing_is_cvg _ (- m)).
- by apply: filterS u_ni => x u_x y xy; rewrite ler_oppl opprK u_x.
- by apply: filterS u_m => x u_x; rewrite ler_oppl opprK.
Qed.

Lemma adjacent (u_ v_ : R ^nat) : nondecreasing_seq u_ -> nonincreasing_seq v_ ->
  (v_ - u_) --> (0 : R) -> [/\ lim v_ = lim u_, cvg u_ & cvg v_].
Proof.
set w_ := v_ - u_ => iu dv w0; have vu n : v_ n >= u_ n.
  suff : lim w_ <= w_ n by rewrite (cvg_lim _ w0)// subr_ge0.
  apply: (nonincreasing_cvg_ge _ (cvgP _ w0)) => m p mp.
  by rewrite ler_sub; rewrite ?iu ?dv.
have cu : cvg u_.
  apply: nondecreasing_is_cvg => //; exists (v_ 0%N) => _ [n _ <-].
  by rewrite (le_trans (vu _)) // dv.
have cv : cvg v_.
  apply: nonincreasing_is_cvg => //; exists (u_ 0%N) => _ [n _ <-].
  by rewrite (le_trans _ (vu _)) // iu.
by split=> //; apply/eqP; rewrite -subr_eq0 -limB //; exact/eqP/cvg_lim.
Qed.

End sequences_R_lemmas.

Definition harmonic {R : fieldType} : R ^nat := [sequence n.+1%:R^-1]_n.
Arguments harmonic {R} n /.

Lemma harmonic_gt0 {R : numFieldType} i : 0 < harmonic i :> R.
Proof. by rewrite /=. Qed.

Lemma harmonic_ge0 {R : numFieldType} i : 0 <= harmonic i :> R.
Proof. exact/ltW/harmonic_gt0. Qed.

Lemma cvg_harmonic {R : archiFieldType} : harmonic --> (0 : R).
Proof.
apply/cvgrPdist_le => _/posnumP[e]; near=> i.
rewrite distrC subr0 ger0_norm//= -lef_pinv ?qualifE// invrK.
rewrite (le_trans (ltW (archi_boundP _)))// ler_nat -add1n -leq_subLR.
by near: i; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

Lemma dvg_harmonic (R : numFieldType) : ~ cvg (series (@harmonic R)).
Proof.
have ge_half n : (0 < n)%N -> 2^-1 <= \sum_(n <= i < n.*2) harmonic i.
  case: n => // n _.
  rewrite (@le_trans _ _ (\sum_(n.+1 <= i < n.+1.*2) n.+1.*2%:R^-1)) //=.
    rewrite sumr_const_nat -addnn addnK addnn -mul2n natrM invfM.
    by rewrite -[_ *+ n.+1]mulr_natr divfK.
  by apply: ler_sum_nat => i /andP[? ?]; rewrite lef_pinv ?qualifE ?ler_nat.
move/cvg_cauchy/cauchy_ballP => /(_ _ [gt0 of 2^-1 : R]); rewrite !near_map2.
rewrite -ball_normE => /nearP_dep hcvg; near \oo => n; near \oo => m.
have: `|series harmonic n - series harmonic m| < 2^-1 :> R by near: m; near: n.
rewrite le_gtF// distrC -[X in X - _](addrNK (series harmonic n.*2)).
rewrite sub_series_geq; last by near: m; apply: nbhs_infty_ge.
rewrite -addrA sub_series_geq -addnn ?leq_addr// addnn.
have sh_ge0 i j : 0 <= \sum_(i <= k < j) harmonic k :> R.
  by rewrite ?sumr_ge0//; move=> k _; apply: harmonic_ge0.
by rewrite ger0_norm// ler_paddl// ge_half//; near: n.
Unshelve. all: by end_near. Qed.

Definition arithmetic_mean (R : numDomainType) (u_ : R ^nat) : R ^nat :=
  [sequence n.+1%:R^-1 * (series u_ n.+1)]_n.

Definition harmonic_mean (R : numDomainType) (u_ : R ^nat) : R ^nat :=
  let v := [sequence (u_ n)^-1]_n in
  [sequence (n.+1%:R / series v n.+1)]_n.

Definition root_mean_square (R : realType) (u_ : R ^nat) : R ^nat :=
  let v_ := [sequence (u_ k)^+2]_k in
  [sequence Num.sqrt (n.+1%:R^-1 * series v_ n.+1)]_n.

Section cesaro.
Variable R : archiFieldType.

Theorem cesaro (u_ : R ^nat) (l : R) : u_ --> l -> arithmetic_mean u_ --> l.
Proof.
move=> u0_cvg; have ssplit v_ m n : (m <= n)%N -> `|n%:R^-1 * series v_ n| <=
    n%:R^-1 * `|series v_ m| + n%:R^-1 * `|\sum_(m <= i < n) v_ i|.
  move=> /subnK<-; rewrite series_addn mulrDr (le_trans (ler_norm_add _ _))//.
  by rewrite !normrM ger0_norm.
apply/cvgrPdist_lt=> _/posnumP[e]; near \oo => m; near=> n.
have {}/ssplit -/(_ _ [sequence l - u_ n]_n) : (m.+1 <= n.+1)%nat.
  by near: n; exists m.
rewrite !seriesEnat /= big_split/=.
rewrite sumrN mulrBr sumr_const_nat -(mulr_natl l) mulKf//.
move=> /le_lt_trans->//; rewrite [e%:num]splitr ltr_add//.
  have [->|neq0] := eqVneq (\sum_(0 <= k < m.+1) (l - u_ k)) 0.
    by rewrite normr0 mulr0.
  rewrite -ltr_pdivl_mulr ?normr_gt0//.
  rewrite -ltf_pinv ?qualifE// ?mulr_gt0 ?invr_gt0 ?normr_gt0// invrK.
  rewrite (lt_le_trans (archi_boundP _))// ler_nat leqW//.
  by near: n; apply: nbhs_infty_ge.
rewrite ltr_pdivr_mull ?ltr0n // (le_lt_trans (ler_norm_sum _ _ _)) //.
rewrite (le_lt_trans (@ler_sum_nat _ _ _ _ (fun i => e%:num / 2) _))//; last first.
  by rewrite sumr_const_nat mulr_natl ltr_pmuln2l// ltn_subrL.
move=> i /andP[mi _]; move: i mi; near: m.
have : \forall x \near \oo, `|l - u_ x| < e%:num / 2.
  by move/cvgrPdist_lt : u0_cvg; apply.
move=> -[N _ Nu]; exists N => // k Nk i ki.
by rewrite ltW// Nu//= (leq_trans Nk)// ltnW.
Unshelve. all: by end_near. Qed.

End cesaro.

Section cesaro_converse.
Variable R : archiFieldType.

Let cesaro_converse_off_by_one (u_ : R ^nat) :
  [sequence n.+1%:R^-1 * series u_ n.+1]_ n --> (0 : R) ->
  [sequence n.+1%:R^-1 * series u_ n]_ n --> (0 : R).
Proof.
move=> H; apply/cvgrPdist_lt => _/posnumP[e].
move/cvgrPdist_lt : H => /(_ _ (gt0 e)) -[m _ mu].
near=> n; rewrite sub0r normrN /=.
have /andP[n0] : ((0 < n) && (m <= n.-1))%N.
  near: n; exists m.+1 => // k mk; rewrite (leq_trans _ mk) //=.
  by rewrite -(leq_add2r 1%N) !addn1 prednK // (leq_trans _ mk).
move/mu => {mu}; rewrite sub0r normrN /= prednK //; apply: le_lt_trans.
rewrite !normrM ler_wpmul2r // ger0_norm // ger0_norm //.
by rewrite lef_pinv // ?ler_nat // posrE // ltr0n.
Unshelve. all: by end_near. Qed.

Lemma cesaro_converse (u_ : R ^nat) (l : R) :
  telescope u_ =o_\oo harmonic -> arithmetic_mean u_ --> l -> u_ --> l.
Proof.
pose a_ := telescope u_ => a_o u_l.
suff abel : forall n,
    u_ n - arithmetic_mean u_ n = \sum_(1 <= k < n.+1) k%:R / n.+1%:R * a_ k.-1.
  suff K : u_ - arithmetic_mean u_ --> (0 : R).
    rewrite -(add0r l).
    rewrite (_ : u_ = u_ - arithmetic_mean u_ + arithmetic_mean u_); last first.
      by rewrite funeqE => n; rewrite subrK.
    exact: cvgD.
  rewrite (_ : _ - arithmetic_mean u_ =
      (fun n => \sum_(1 <= k < n.+1) k%:R / n.+1%:R * a_ k.-1)); last first.
    by rewrite funeqE.
  rewrite {abel} /= (_ : (fun _ => _) =
      fun n => n.+1%:R^-1 * \sum_(0 <= k < n) k.+1%:R * a_ k); last first.
    rewrite funeqE => n; rewrite big_add1 /= /= big_distrr /=.
    by apply eq_bigr => i _; rewrite mulrCA mulrA.
  have {}a_o : [sequence n.+1%:R * telescope u_ n]_n --> (0 : R).
    apply: (@eqolim0 _ _ _ eventually_filterType).
    rewrite a_o.
    set h := 'o_[filter of \oo] harmonic.
    apply/eqoP => _/posnumP[e] /=.
    near=> n; rewrite normr1 mulr1 normrM -ler_pdivl_mull// ?normr_gt0//.
    rewrite mulrC -normrV ?unitfE //.
    near: n.
    by case: (eqoP eventually_filterType harmonic h) => Hh _; apply Hh.
  move: (cesaro a_o); rewrite /arithmetic_mean /series /= -/a_.
  exact: (@cesaro_converse_off_by_one (fun k => k.+1%:R * a_ k)).
case => [|n].
  rewrite /arithmetic_mean/= invr1 mul1r !seriesEnat/=.
  by rewrite big_nat1 subrr big_geq.
rewrite /arithmetic_mean /= seriesEnat /= big_nat_recl //=.
under eq_bigr do rewrite eq_sum_telescope.
rewrite big_split /= big_const_nat iter_addr addr0 addrA -mulrS mulrDr.
rewrite -(mulr_natl (u_ O)) mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r opprD addrA.
rewrite eq_sum_telescope (addrC (u_ O)) addrK.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) \sum_(0 <= k < n.+1 | (k < i.+1)%N) a_ k); last first.
  rewrite !big_mkord; apply eq_bigr => i _.
  by rewrite seriesEord/= big_mkord -big_ord_widen//.
rewrite (exchange_big_dep_nat xpredT) //=.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) \sum_(i <= j < n.+1) a_ i ); last first.
  apply congr_big_nat => //= i ni.
  rewrite big_const_nat iter_addr addr0 -big_filter.
  rewrite big_const_seq iter_addr addr0; congr (_ *+ _).
  rewrite /index_iota subn0 -[in LHS](subnKC (ltnW ni)) iotaD filter_cat.
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
rewrite seriesEord -big_split /= big_add1 /= big_mkord; apply eq_bigr => i _.
rewrite mulrCA -[X in X - _]mulr1 -mulrBr [RHS]mulrC; congr (_ * _).
rewrite -[X in X - _](@divrr _ (n.+2)%:R) ?unitfE ?pnatr_eq0 //.
rewrite [in X in _ - X]mulrC -mulrBl; congr (_ / _).
rewrite -natrB; last by rewrite (@leq_trans n.+1) // leq_subr.
rewrite subnBA; by [rewrite addSnnS addnC addnK | rewrite ltnW].
Unshelve. all: by end_near. Qed.

End cesaro_converse.

Section series_convergence.

Lemma cvg_series_cvg_0 (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  cvg (series u_) -> u_ --> (0 : V).
Proof.
move=> cvg_series.
rewrite (_ : u_ = fun n => series u_ n.+1 - series u_ n); last first.
  by rewrite funeqE => i; rewrite seriesSB.
by rewrite -(subrr (lim (series u_))); apply: cvgB => //; rewrite ?cvg_shiftS.
Qed.

Lemma nondecreasing_series (R : numFieldType) (u_ : R ^nat) (P : pred nat) :
  (forall n, P n -> 0 <= u_ n)%R ->
  nondecreasing_seq (fun n=> \sum_(0 <= k < n | P k) u_ k)%R.
Proof.
move=> u_ge0; apply/nondecreasing_seqP => n.
rewrite [in leRHS]big_mkcond [in leRHS]big_nat_recr//=.
by rewrite -[in leRHS]big_mkcond/= ler_addl; case: ifPn => //; exact: u_ge0.
Qed.

Lemma increasing_series (R : numFieldType) (u_ : R ^nat) :
  (forall n, 0 < u_ n) -> increasing_seq (series u_).
Proof.
move=> u_ge0; apply/increasing_seqP => n.
by rewrite !seriesEord/= big_ord_recr ltr_addl.
Qed.

End series_convergence.

Definition arithmetic (R : zmodType) a z : R ^nat := [sequence a + z *+ n]_n.
Arguments arithmetic {R} a z n /.

Lemma mulrn_arithmetic (R : zmodType) : @GRing.natmul R = arithmetic 0.
Proof. by rewrite funeq2E => z n /=; rewrite add0r. Qed.

Definition geometric (R : fieldType) a z : R ^nat := [sequence a * z ^+ n]_n.
Arguments geometric {R} a z n /.

Lemma exprn_geometric (R : fieldType) : (@GRing.exp R) = geometric 1.
Proof. by rewrite funeq2E => z n /=; rewrite mul1r. Qed.

Lemma cvg_arithmetic (R : archiFieldType) a (z : R) :
  z > 0 -> arithmetic a z --> +oo.
Proof.
move=> z_gt0; apply/cvgryPge => A; near=> n => /=.
rewrite -ler_subl_addl -mulr_natl -ler_pdivr_mulr//.
rewrite ler_normlW// ltW// (lt_le_trans (archi_boundP _))// ler_nat.
by near: n; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

Lemma cvg_expr (R : archiFieldType) (z : R) :
  `|z| < 1 -> (GRing.exp z : R ^nat) --> (0 : R).
Proof.
move=> Nz_lt1; apply/norm_cvg0P; pose t := (1 - `|z|).
apply: (@squeeze_cvgr _ _ _ _ (cst 0) _ (t^-1 *: @harmonic R)); last 2 first.
- exact: cvg_cst.
- by rewrite -(scaler0 _ t^-1); exact: (cvgZr cvg_harmonic).
near=> n; rewrite normr_ge0 normrX/= ler_pdivl_mull ?subr_gt0//.
rewrite -(@ler_pmul2l _ n.+1%:R)// mulfV// [t * _]mulrC mulr_natl.
have -> : 1 = (`|z| + t) ^+ n.+1 by rewrite addrC addrNK expr1n.
rewrite exprDn (bigD1 (inord 1)) ?inordK// subn1 expr1 bin1 ler_addl sumr_ge0//.
by move=> i; rewrite ?(mulrn_wge0, mulr_ge0, exprn_ge0, subr_ge0)// ltW.
Unshelve. all: by end_near. Qed.

Lemma geometric_seriesE (R : numFieldType) (a z : R) : z != 1 ->
  series (geometric a z) = [sequence a * (1 - z ^+ n) / (1 - z)]_n.
Proof.
rewrite funeqE => z_neq1 n.
apply: (@mulIf _ (1 - z)); rewrite ?mulfVK ?subr_eq0 1?eq_sym//.
rewrite seriesEnat !mulrBr [in LHS]mulr1 mulr_suml -opprB -sumrB.
by under eq_bigr do rewrite -mulrA -exprSr; rewrite telescope_sumr// opprB.
Qed.

Lemma cvg_geometric_series (R : archiFieldType) (a z : R) : `|z| < 1 ->
  series (geometric a z) --> (a * (1 - z)^-1).
Proof.
move=> Nz_lt1; rewrite geometric_seriesE ?lt_eqF 1?ltr_normlW//.
have -> : a / (1 - z) = (a * (1 - 0)) / (1 - z) by rewrite subr0 mulr1.
by apply: cvgMl; apply: cvgMr; apply: cvgB; [apply: cvg_cst|apply: cvg_expr].
Qed.

Lemma cvg_geometric_series_half (R : archiFieldType) (r : R) n :
  series (fun k => r / (2 ^ (k + n.+1))%:R : R^o) --> (r / 2 ^+ n : R^o).
Proof.
rewrite (_ : series _ = series (geometric (r / (2 ^ n.+1)%:R) 2^-1%R)); last first.
  rewrite funeqE => m; rewrite /series /=; apply eq_bigr => k _.
  by rewrite expnD natrM (mulrC (2 ^ k)%:R) invfM exprVn (natrX _ 2 k) mulrA.
apply: cvg_trans.
  apply: cvg_geometric_series.
  by rewrite ger0_norm // invr_lt1 // ?ltr1n // unitfE.
rewrite [X in (X - _)%R](splitr 1) div1r addrK.
by rewrite -mulrA -invfM expnSr natrM -mulrA divff// mulr1 natrX.
Qed.
Arguments cvg_geometric_series_half {R} _ _.

Lemma cvg_geometric (R : archiFieldType) (a z : R) : `|z| < 1 ->
  geometric a z --> (0 : R).
Proof. by move=> /cvg_geometric_series/cvgP/cvg_series_cvg_0. Qed.

Lemma is_cvg_geometric_series (R : archiFieldType) (a z : R) : `|z| < 1 ->
 cvg (series (geometric a z)).
Proof. by move=> /cvg_geometric_series/cvgP; apply. Qed.

Definition normed_series_of (K : numDomainType) (V : normedModType K)
    (u_ : V ^nat) of phantom V^nat (series u_) : K ^nat :=
  [series `|u_ n|]_n.
Notation "[ 'normed' s_ ]" := (@normed_series_of _ _ _ (Phantom _ s_)) : ring_scope.
Arguments normed_series_of {K V} u_ _ n /.

Lemma ger0_normed {K : numFieldType} (u_ : K ^nat) :
  (forall n, 0 <= u_ n) -> [normed series u_] = series u_.
Proof.
by move=> u_gt0; rewrite funeqE => n /=; apply: eq_bigr => k; rewrite ger0_norm.
Qed.

Lemma cauchy_seriesP {R : numFieldType} (V : normedModType R) (u_ : V ^nat) :
  cauchy (series u_ @ \oo) <->
  forall e : R, e > 0 ->
    \forall n \near (\oo, \oo), `|\sum_(n.1 <= k < n.2) u_ k| < e.
Proof.
rewrite -cauchy_ballP; split=> su_cv _/posnumP[e];
have {}su_cv := !! su_cv _ (gt0 e);
rewrite -near2_pair -ball_normE !near_simpl/= in su_cv *.
  apply: filterS su_cv => -[/= m n]; rewrite distrC sub_series.
  by have [|/ltnW]:= leqP m n => mn//; rewrite (big_geq mn) ?normr0.
have := su_cv; rewrite near_swap => su_cvC; near=> m => /=; rewrite sub_series.
by have [|/ltnW]:= leqP m.2 m.1 => m12; rewrite ?normrN; near: m.
Unshelve. all: by end_near. Qed.

Lemma series_le_cvg (R : realType) (u_ v_ : R ^nat) :
  (forall n, 0 <= u_ n) -> (forall n, 0 <= v_ n) ->
  (forall n, u_ n <= v_ n) ->
  cvg (series v_) -> cvg (series u_).
Proof.
move=> u_ge0 v_ge0 le_uv /cvg_seq_bounded/bounded_fun_has_ubound[M v_M].
apply: nondecreasing_is_cvg; first exact: nondecreasing_series.
exists M => _ [n _ <-].
by apply: le_trans (v_M (series v_ n) _); [apply: ler_sum | exists n].
Qed.

Lemma normed_cvg {R : realType} (V : completeNormedModType R) (u_ : V ^nat) :
  cvg [normed series u_] -> cvg (series u_).
Proof.
move=> /cauchy_cvgP/cauchy_seriesP u_ncvg.
apply/cauchy_cvgP/cauchy_seriesP => e /u_ncvg.
apply: filterS => n /=; rewrite ger0_norm ?sumr_ge0//.
by apply: le_lt_trans; apply: ler_norm_sum.
Qed.

Lemma lim_series_norm {R : realType} (V : completeNormedModType R) (f : V ^nat) :
  cvg [normed series f] -> `|lim (series f)| <= lim [normed series f].
Proof.
move=> cnf; have cf := normed_cvg cnf.
rewrite -lim_norm // (ler_lim (is_cvg_norm cf) cnf) //.
by near=> x; rewrite ler_norm_sum.
Unshelve. all: by end_near. Qed.

Section series_linear.

Lemma cvg_series_bounded (R : realFieldType) (f : R ^nat) :
  cvg (series f) -> bounded_fun f.
Proof.
by move/cvg_series_cvg_0 => f0; apply/cvg_seq_bounded/cvg_ex; exists 0.
Qed.

Lemma cvg_to_0_linear (R : realFieldType) (f : R -> R) K k :
  0 < k -> (forall r, 0 < `| r | < k -> `|f r| <= K * `| r |) ->
    f x @[x --> 0^'] --> 0.
Proof.
move=> k0 kfK; have [K0|K0] := lerP K 0.
- apply/cvgrPdist_lt => _/posnumP[e]; near=> x.
  rewrite distrC subr0 (le_lt_trans (kfK _ _)) //; last first.
    by rewrite (@le_lt_trans _ _ 0)// mulr_le0_ge0.
  near: x; exists (k / 2); first by rewrite /mkset divr_gt0.
  move=> t /=; rewrite distrC subr0 => tk2 t0.
  by rewrite normr_gt0 t0 (lt_trans tk2) // -[in ltLHS](add0r k) midf_lt.
- apply/eqolim0/eqoP => _/posnumP[e]; near=> x.
  rewrite (le_trans (kfK _ _)) //=.
  + near: x; exists (k / 2); first by rewrite /mkset divr_gt0.
    move=> t /=; rewrite distrC subr0 => tk2 t0.
    by rewrite normr_gt0 t0 (lt_trans tk2) // -[in ltLHS](add0r k) midf_lt.
  + rewrite normr1 mulr1 mulrC -ler_pdivl_mulr //.
    near: x; exists (e%:num / K); first by rewrite /mkset divr_gt0.
    by move=> t /=; rewrite distrC subr0 => /ltW.
Unshelve. all: by end_near. Qed.

Lemma lim_cvg_to_0_linear (R : realType) (f : nat -> R) (g : R -> nat -> R) k :
  0 < k -> cvg (series f) ->
  (forall r, 0 < `|r| < k -> forall n, `|g r n| <= f n * `| r |) ->
  lim (series (g x)) @[x --> 0^'] --> 0.
Proof.
move=> k_gt0 Cf Hg.
apply: (@cvg_to_0_linear _ _ (lim (series f)) k) => // h hLk; rewrite mulrC.
have Ckf := @is_cvg_seriesZ _ _ `|h| Cf.
have Cng : cvg [normed series (g h)].
  apply: series_le_cvg (Hg _ hLk) _ => [//|?|].
    exact: le_trans (Hg _ hLk _).
  by under eq_fun do rewrite mulrC.
apply: (le_trans (lim_series_norm Cng)).
rewrite -[_ * _](lim_seriesZ _ Cf) (lim_series_le Cng Ckf) // => n.
by rewrite [leRHS]mulrC; apply: Hg.
Qed.

End series_linear.

Section exponential_series.

Variable R : realType.
Implicit Types x : R.

Definition exp_coeff x := [sequence x ^+ n / n`!%:R]_n.

Local Notation exp := exp_coeff.

Lemma exp_coeff_ge0 x n : 0 <= x -> 0 <= exp x n.
Proof. by move=> x0; rewrite /exp divr_ge0 // exprn_ge0. Qed.

Lemma series_exp_coeff0 n : series (exp 0) n.+1 = 1.
Proof.
rewrite /series /= big_mkord big_ord_recl /= /exp /= expr0n divr1.
by rewrite big1 ?addr0 // => i _; rewrite expr0n mul0r.
Qed.

Section exponential_series_cvg.

Variable x : R.
Hypothesis x0 : 0 < x.

Let S0 N n := (N ^ N)%:R * \sum_(N.+1 <= i < n) (x / N%:R) ^+ i.

Let is_cvg_S0 N : x < N%:R -> cvg (S0 N).
Proof.
move=> xN; apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series; rewrite normrM normfV.
by rewrite ltr_pdivr_mulr ?mul1r !ger0_norm // 1?ltW // (lt_trans x0).
Qed.

Let S0_ge0 N n : 0 <= S0 N n.
Proof.
rewrite mulr_ge0 // ?ler0n //; apply sumr_ge0 => i _.
by rewrite exprn_ge0 // divr_ge0 // ltW.
Qed.

Let S0_sup N n : x < N%:R -> S0 N n <= sup (range (S0 N)).
Proof.
move=> xN; apply/sup_upper_bound; [split; [by exists (S0 N n), n|]|by exists n].
rewrite (_ : (range _) = [set `|S0 N n0| | n0 in setT]).
  by apply: cvg_has_ub (is_cvg_S0 xN).
by rewrite predeqE=> y; split=> -[z _ <-]; exists z; rewrite ?ger0_norm ?S0_ge0.
Qed.

Let S1 N n := \sum_(N.+1 <= i < n) exp x i.

Lemma incr_S1 N : nondecreasing_seq (S1 N).
Proof.
apply/nondecreasing_seqP => n; rewrite /S1.
have [nN|Nn] := leqP n N; first by rewrite !big_geq // (leq_trans nN).
by rewrite big_nat_recr//= ler_addl exp_coeff_ge0 // ltW.
Qed.

Let S1_sup N : x < N%:R -> ubound (range (S1 N)) (sup (range (S0 N))).
Proof.
move=> xN _ [n _ <-]; rewrite (le_trans _ (S0_sup n xN)) // /S0 big_distrr /=.
have N_gt0 := lt_trans x0 xN; apply ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pmul2l ?exprn_gt0// (@le_trans _ _ 1) //.
    by rewrite invf_le1// ?ler1n ?ltr0n // fact_gt0.
  rewrite natrX -expfB_cond ?(negPf (lt0r_neq0 N_gt0))//.
  by rewrite exprn_ege1 // ler1n; case: (N) xN x0; case: ltrgt0P.
rewrite /exp expr_div_n /= (fact_split Ni) mulrCA ler_pmul2l ?exprn_gt0// natrX.
rewrite -invf_div -expfB // lef_pinv ?qualifE ?exprn_gt0//; last first.
  rewrite ltr0n muln_gt0 fact_gt0/= big_seq big_mkcond/= prodn_gt0// => j.
  by case: ifPn=>//; rewrite mem_index_iota => /andP[+ _]; exact: leq_ltn_trans.
rewrite big_nat_rev/= -natrX ler_nat -prod_nat_const_nat big_add1 /= big_ltn //.
rewrite leq_mul//; first by rewrite (leq_trans (fact_geq _))// leq_pmull.
under [in X in (_ <= X)%N]eq_bigr do rewrite 2!addSn 2!subSS.
rewrite !big_seq/=; elim/big_ind2 : _ => //; first by move=> *; exact: leq_mul.
move=> j; rewrite mem_index_iota => /andP[_ ji].
by rewrite -addnBA// ?leq_addr// ltnW// ltnW.
Qed.

Lemma is_cvg_series_exp_coeff_pos : cvg (series (exp x)).
Proof.
rewrite /series; near \oo => N; have xN : x < N%:R; last first.
  rewrite -(@is_cvg_series_restrict N.+1).
  by apply: (nondecreasing_is_cvg (incr_S1 N)); eexists; apply: S1_sup.
near: N; exists (absz (floor x)).+1 => // m; rewrite /mkset -(@ler_nat R).
move/lt_le_trans => -> //; rewrite (lt_le_trans (lt_succ_floor x)) // -addn1.
by rewrite natrD ler_add2r -(@gez0_abs (floor x)) ?floor_ge0// ltW.
Unshelve. all: by end_near. Qed.

End exponential_series_cvg.

Lemma normed_series_exp_coeff x : [normed series (exp x)] = series (exp `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma is_cvg_series_exp_coeff x : cvg (series (exp x)).
Proof.
have [->|x0] := eqVneq x 0.
  apply/cvg_ex; exists 1; apply/cvgrPdist_lt => // => _/posnumP[e].
  near=> n; have [m ->] : exists m, n = m.+1.
    by exists n.-1; rewrite prednK //; near: n; exists 1%N.
  by rewrite series_exp_coeff0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp_coeff.
by apply: is_cvg_series_exp_coeff_pos; rewrite normr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvg_exp_coeff x : exp x --> (0 : R).
Proof. exact: (cvg_series_cvg_0 (@is_cvg_series_exp_coeff x)). Qed.

End exponential_series.

(* TODO: generalize *)
Definition expR {R : realType} (x : R) : R := lim (series (exp_coeff x)).

(********************************)
(* Sequences of natural numbers *)
(********************************)

Lemma __deprecated__nat_dvg_real (R : realType) (u_ : nat ^nat) : u_ --> \oo ->
  ([sequence (u_ n)%:R : R^o]_n --> +oo)%R.
Proof. by move=> ?; apply/cvgrnyP. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgrnyP` and generalized")]
Notation nat_dvg_real := __deprecated__nat_dvg_real.

Lemma __deprecated__nat_cvgPpinfty (u : nat^nat) :
  u --> \oo <-> forall A, \forall n \near \oo, (A <= u n)%N.
Proof. exact: cvgnyPge. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
      note="renamed to `cvgnyPge` and generalized")]
Notation nat_cvgPpinfty:= __deprecated__nat_cvgPpinfty.

Lemma nat_nondecreasing_is_cvg (u_ : nat^nat) :
  nondecreasing_seq u_ -> has_ubound (range u_) -> cvg u_.
Proof.
move=> u_nd [l ul].
suff [N Nu] : exists N, forall n, (n >= N)%N -> u_ n = u_ N.
  apply/cvg_ex; exists (u_ N); rewrite -(cvg_shiftn N).
  rewrite [X in X --> _](_ : _ = cst (u_ N))//; first exact: cvg_cst.
  by apply/funext => n /=; rewrite Nu// leq_addl.
apply/not_existsP => hu.
have {hu}/choice[f Hf] : forall x, (exists n, x <= n /\ u_ n > u_ x)%N.
  move=> x; have /existsNP[N /not_implyP[xN Nx]] := hu x.
  exists N; split => //; move/eqP : Nx; rewrite neq_lt => /orP[|//].
  by move/u_nd : xN; rewrite le_eqVlt => /predU1P[->|//].
have uf : forall x, (x < u_ (iter x.+1 f O))%N.
  elim=> /= [|i ih]; first by have := Hf O => -[_]; exact: leq_trans.
  by have := Hf (f (iter i f O)) => -[_]; exact: leq_trans.
have /ul : range u_ (u_ (iter l.+1 f O)) by exists (iter l.+1 f O).
by rewrite leNgt => /negP; apply; rewrite ltEnat //=; exact: uf.
Qed.

Definition nseries (u : nat^nat) := (fun n => \sum_(0 <= k < n) u k)%N.

Lemma le_nseries (u : nat^nat) : {homo nseries u : a b / a <= b}%N.
Proof.
move=> a b ab; rewrite /nseries [in X in (_ <= X)%N]/index_iota subn0.
rewrite -[in X in (_ <= X)%N](subnKC ab) iotaD big_cat/= add0n.
by rewrite /index_iota subn0 leq_addr.
Qed.

Lemma cvg_nseries_near (u : nat^nat) : cvg (nseries u) ->
  \forall n \near \oo, u n = 0%N.
Proof.
move=> /cvg_ex[l ul]; have /ul[a _ aul] : nbhs l [set l].
  exists [set l]; split; last by split.
  by exists [set l] => //; rewrite bigcup_set1.
have /ul[b _ bul] : nbhs l [set l.-1; l].
  by exists [set l]; split => //; exists [set l] => //; rewrite bigcup_set1.
exists (maxn a b) => // n /= abn.
rewrite (_ : u = fun n => nseries u n.+1 - nseries u n)%N; last first.
  by rewrite funeqE => i; rewrite /nseries big_nat_recr//= addnC addnK.
have /aul -> : (a <= n)%N by rewrite (leq_trans _ abn) // leq_max leqnn.
have /bul[->|->] : (b <= n.+1)%N by rewrite leqW// (leq_trans _ abn)// leq_maxr.
- by apply/eqP; rewrite subn_eq0// leq_pred.
- by rewrite subnn.
Qed.

Lemma dvg_nseries (u : nat^nat) : ~ cvg (nseries u) -> nseries u --> \oo.
Proof.
move=> du; apply: contrapT => /cvgnyPgt/existsNP[l lu]; apply: du.
apply: nat_nondecreasing_is_cvg => //; first exact: le_nseries.
exists l => _ [n _ <-]; rewrite leNgt; apply/negP => lun; apply: lu.
by near do rewrite (leq_trans lun) ?le_nseries//; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

(**************************************)
(* Sequences of extended real numbers *)
(**************************************)

Notation "\big [ op / idx ]_ ( m <= i <oo | P ) F" :=
  (lim (fun n => (\big[ op / idx ]_(m <= i < n | P) F))) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i <oo ) F" :=
  (lim (fun n => (\big[ op / idx ]_(m <= i < n) F))) : big_scope.
Notation "\big [ op / idx ]_ ( i <oo | P ) F" :=
  (lim (fun n => (\big[ op / idx ]_(i < n | P) F))) : big_scope.
Notation "\big [ op / idx ]_ ( i <oo ) F" :=
  (lim (fun n => (\big[ op / idx ]_(i < n) F))) : big_scope.

Notation "\sum_ ( m <= i <oo | P ) F" :=
  (\big[+%E/0%E]_(m <= i <oo | P%B) F%E) : ereal_scope.
Notation "\sum_ ( m <= i <oo ) F" :=
  (\big[+%E/0%E]_(m <= i <oo) F%E) : ereal_scope.
Notation "\sum_ ( i <oo | P ) F" :=
  (\big[+%E/0%E]_(0 <= i <oo | P%B) F%E) : ereal_scope.
Notation "\sum_ ( i <oo ) F" :=
  (\big[+%E/0%E]_(0 <= i <oo) F%E) : ereal_scope.

Section partial_esum.
Local Open Scope ereal_scope.

Variables (R : numDomainType) (u_ : (\bar R)^nat).

Definition eseries : (\bar R)^nat := [sequence \sum_(0 <= k < n) u_ k]_n.
Definition etelescope : (\bar R)^nat := [sequence u_ n.+1 - u_ n]_n.

Lemma eseriesEnat : eseries = [sequence \sum_(0 <= k < n) u_ k]_n.
Proof. by []. Qed.

Lemma eseriesEord : eseries = [sequence \sum_(k < n) u_ k]_n.
Proof. by rewrite funeqE => n; rewrite /eseries/= big_mkord. Qed.

Lemma eseriesSr n : eseries n.+1 = eseries n + u_ n.
Proof. by rewrite !eseriesEord/= big_ord_recr. Qed.

Lemma eseriesS n : eseries n.+1 = u_ n + eseries n.
Proof. by rewrite addeC eseriesSr. Qed.

Lemma eseriesSB (n : nat) :
  eseries n \is a fin_num -> eseries n.+1 - eseries n = u_ n.
Proof. by move=> enfin; rewrite eseriesS addeK//=. Qed.

Lemma eseries_addn m n : eseries (n + m)%N = eseries m + \sum_(m <= k < n + m) u_ k.
Proof. by rewrite eseriesEnat/= -big_cat_nat// leq_addl. Qed.

Lemma sub_eseries_geq m n : (m <= n)%N -> eseries m \is a fin_num ->
  eseries n - eseries m = \sum_(m <= k < n) u_ k.
Proof. by move=> /subnK<- emfin; rewrite eseries_addn addeAC subee// add0e. Qed.

Lemma sub_eseries m n : eseries m \is a fin_num -> eseries n \is a fin_num ->
  eseries n - eseries m = if (m <= n)%N then \sum_(m <= k < n) u_ k
                        else - \sum_(n <= k < m) u_ k.
Proof.
move=> ? ?; have [mn|/ltnW mn] := leqP m n; rewrite -sub_eseries_geq//.
by rewrite oppeD ?fin_numN// oppeK addeC.
Qed.

Lemma sub_double_eseries n : eseries n \is a fin_num ->
  eseries n.*2 - eseries n = \sum_(n <= k < n.*2) u_ k.
Proof. by move=> enfin; rewrite sub_eseries_geq// -addnn leq_addl. Qed.

End partial_esum.

Arguments eseries {R} u_ n : simpl never.
Arguments etelescope {R} u_ n : simpl never.
Notation "[ 'series' E ]_ n" := (eseries [sequence E%E]_n) : ereal_scope.

Section eseries_ops.
Variable (R : numDomainType).
Local Open Scope ereal_scope.

Lemma eseriesD (f g : (\bar R)^nat) : eseries (f \+ g) = eseries f \+ eseries g.
Proof. by rewrite /eseries /= funeqE => n; rewrite big_split. Qed.

End eseries_ops.

Section sequences_ereal_realDomainType.
Local Open Scope ereal_scope.
Variable T : realDomainType.
Implicit Types u : (\bar T)^nat.

Lemma ereal_nondecreasing_opp u_ :
  nondecreasing_seq (-%E \o u_) = nonincreasing_seq u_.
Proof.
rewrite propeqE; split => ni_u m n mn; last by rewrite lee_oppr oppeK ni_u.
by rewrite -(oppeK (u_ m)) -lee_oppr ni_u.
Qed.

End sequences_ereal_realDomainType.

Section sequences_ereal.
Local Open Scope ereal_scope.

Lemma __deprecated__ereal_cvg_abs0 (R : realFieldType) (f : (\bar R)^nat) :
  abse \o f --> nbhs 0 -> f --> 0.
Proof. by move/cvg_abse0P. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvg_abse0P` and generalized")]
Notation ereal_cvg_abs0 := __deprecated__ereal_cvg_abs0.

Lemma __deprecated__ereal_cvg_ge0 (R : realFieldType) (f : (\bar R)^nat) (a : \bar R) :
  (forall n, 0 <= f n) -> f --> a -> 0 <= a.
Proof. by move=> f_ge0; apply: cvge_ge; apply: nearW. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvge_ge` instead")]
Notation ereal_cvg_ge0 := __deprecated__ereal_cvg_ge0.

Lemma __deprecated__ereal_lim_ge (R : realFieldType) x (u_ : (\bar R)^nat) : cvg u_ ->
  (\forall n \near \oo, x <= u_ n) -> x <= lim u_.
Proof. exact: lime_ge. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `lime_ge` and generalized")]
Notation ereal_lim_ge := __deprecated__ereal_lim_ge.

Lemma __deprecated__ereal_lim_le (R : realFieldType) x (u_ : (\bar R)^nat) : cvg u_ ->
  (\forall n \near \oo, u_ n <= x) -> lim u_ <= x.
Proof. exact: lime_le. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `lime_le` and generalized")]
Notation ereal_lim_le := __deprecated__ereal_lim_le.

Lemma __deprecated__dvg_ereal_cvg (R : realFieldType) (u_ : R ^nat) :
  u_ --> +oo%R -> [sequence (u_ n)%:E]_n --> +oo.
Proof. by rewrite cvgeryP. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgeryP` and generalized")]
Notation dvg_ereal_cvg := __deprecated__dvg_ereal_cvg.

Lemma __deprecated__ereal_cvg_real (R : realFieldType) (f : (\bar R)^nat) a :
  {near \oo, forall x, f x \is a fin_num} /\
  (fine \o f --> a) <-> f --> a%:E.
Proof. by rewrite fine_cvgP. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `fine_cvgP` and generalized")]
Notation ereal_cvg_real := __deprecated__ereal_cvg_real.

Lemma ereal_nondecreasing_cvg (R : realType) (u_ : (\bar R)^nat) :
  nondecreasing_seq u_ -> u_ --> ereal_sup (u_ @` setT).
Proof.
move=> nd_u_; set S := u_ @` setT; set l := ereal_sup S.
have [Spoo|Spoo] := pselect (S +oo).
  have [N Nu] : exists N, forall n, (n >= N)%nat -> u_ n = +oo.
    case: Spoo => N _ uNoo; exists N => n Nn.
    by move: (nd_u_ _ _ Nn); rewrite uNoo leye_eq => /eqP.
  have -> : l = +oo by rewrite /l /ereal_sup; exact: supremum_pinfty.
  rewrite -(cvg_shiftn N); set f := (X in X --> _).
  rewrite (_ : f = (fun=> +oo)); first exact: cvg_cst.
  by rewrite funeqE => n; rewrite /f /= Nu // leq_addl.
have [Snoo|Snoo] := pselect (u_ = fun=> -oo).
  rewrite /l (_ : S = [set -oo]); last first.
    rewrite predeqE => x; split => [-[n _ <-]|->]; first by rewrite Snoo.
    by exists O => //; rewrite Snoo.
  by rewrite ereal_sup1 Snoo; exact: cvg_cst.
have [/ereal_sup_ninfty loo|lnoo] := eqVneq l -oo.
  suff : u_ = (fun=> -oo) by [].
  by rewrite funeqE => m; apply (loo (u_ m)); exists m.
apply/cvg_ballP => _/posnumP[e].
have [{lnoo}loo|lpoo] := eqVneq l +oo.
  near=> n; rewrite /ball /= /ereal_ball.
  have unoo : u_ n != -oo.
    near: n; have [m /eqP umoo] : exists m, u_ m <> -oo.
      apply/existsNP => uoo.
      by apply/Snoo; rewrite funeqE => ?; rewrite uoo.
    exists m => // k mk; apply: contra umoo => /eqP ukoo.
    by move/nd_u_ : mk; rewrite ukoo leeNy_eq.
  rewrite loo ger0_norm ?subr_ge0; last first.
    by case/ler_normlP : (contract_le1 (u_ n)).
  have [e2|e2] := lerP 2 e%:num.
    rewrite /= ltr_subl_addr addrC -ltr_subl_addr.
    case/ler_normlP : (contract_le1 (u_ n)); rewrite ler_oppl => un1 _.
    rewrite (@le_lt_trans _ _ (-1)) //.
      by rewrite ler_subl_addr addrC -ler_subl_addr opprK (le_trans e2).
    by move: un1; rewrite le_eqVlt eq_sym contract_eqN1 (negbTE unoo).
  rewrite ltr_subl_addr addrC -ltr_subl_addr -lt_expandLR ?inE//=.
    near: n.
    suff [n Hn] : exists n, expand (contract +oo - e%:num)%R < u_ n.
      by exists n => // m nm; rewrite (lt_le_trans Hn) //; apply nd_u_.
    apply/not_existsP => abs.
    have : l <= expand (contract +oo - e%:num)%R.
      apply: ub_ereal_sup => x [n _ <-{x}].
      rewrite leNgt; apply/negP/abs.
      rewrite loo leye_eq expand_eqoo ler_sub_addr addrC -ler_sub_addr subrr.
      by apply/negP; rewrite -ltNge.
    have [e1|e1] := ltrP 1 e%:num.
      by rewrite ler_subl_addr (le_trans (ltW e2)).
    by rewrite ler_subl_addr ler_addl.
have l_fin_num : l \is a fin_num by rewrite fin_numE lpoo lnoo.
have [le1|le1] := (ltrP (`|contract l - e%:num|) 1)%R; last first.
  near=> n; rewrite /ball /= /ereal_ball /=.
  have unoo : u_ n != -oo.
    near: n.
    have [m /eqP umoo] : exists m, u_ m <> -oo.
      apply/existsNP => uoo.
      by apply/Snoo; rewrite funeqE => ?; rewrite uoo.
    exists m => // k mk; apply: contra umoo => /eqP ukoo.
    by move/nd_u_ : mk; rewrite ukoo leeNy_eq.
  rewrite ger0_norm ?subr_ge0 ?le_contract ?ereal_sup_ub//; last by exists n.
  have [l0|l0] := ger0P (contract l).
    have el : (e%:num > contract l)%R.
      rewrite ltNge; apply/negP => er.
      rewrite ger0_norm ?subr_ge0// -ler_subl_addr opprK in le1.
      case/ler_normlP : (contract_le1 l) => _ /(le_trans le1); apply/negP.
      by rewrite -ltNge ltr_addl.
    rewrite ltr0_norm ?subr_lt0// opprB in le1.
    rewrite ltr_subl_addr addrC -ltr_subl_addr -opprB ltr_oppl.
    rewrite (lt_le_trans _ le1) // lt_neqAle eqr_oppLR contract_eqN1 unoo /=.
    by case/ler_normlP : (contract_le1 (u_ n)).
  rewrite ler0_norm in le1; last by rewrite subr_le0 (le_trans (ltW l0)).
  rewrite opprB ler_subr_addr addrC -ler_subr_addr in le1.
  rewrite ltr_subl_addr (le_lt_trans le1) // -ltr_subl_addl addrAC subrr add0r.
  rewrite lt_neqAle eq_sym contract_eqN1 unoo /=.
  by case/ler_normlP : (contract_le1 (u_ n)); rewrite ler_oppl.
pose e' :=
  (fine l - fine (expand (contract l - e%:num)))%R.
have e'0 : (0 < e')%R.
  rewrite /e' subr_gt0 -lte_fin fine_expand //.
  rewrite lt_expandLR ?inE ?ltW// ltr_subl_addr fineK //.
  by rewrite ltr_addl.
have [y [m _ umx] Se'y] := ub_ereal_sup_adherent e'0 l_fin_num.
near=> n; rewrite /ball /= /ereal_ball /=.
rewrite ger0_norm ?subr_ge0 ?le_contract ?ereal_sup_ub//; last by exists n.
move: Se'y; rewrite -{}umx {y} /= => le'um.
have leum : (contract l - e%:num < contract (u_ m))%R.
  rewrite -lt_expandLR ?inE ?ltW//.
  move: le'um; rewrite /e' EFinN /= opprB EFinB.
  rewrite (fineK l_fin_num) fine_expand //.
  by rewrite addeCA subee // adde0.
rewrite ltr_subl_addr addrC -ltr_subl_addr (lt_le_trans leum) //.
by rewrite le_contract nd_u_//; near: n; exists m.
Unshelve. all: by end_near. Qed.

Lemma ereal_nondecreasing_is_cvg (R : realType) (u_ : (\bar R) ^nat) :
  nondecreasing_seq u_ -> cvg u_.
Proof. by move=> ?; apply/cvg_ex; eexists; exact: ereal_nondecreasing_cvg. Qed.

Lemma ereal_nonincreasing_cvg (R : realType) (u_ : (\bar R)^nat) :
  nonincreasing_seq u_ -> u_ --> ereal_inf (u_ @` setT).
Proof.
move=> ni_u; rewrite [X in X --> _](_ : _ = -%E \o -%E \o u_); last first.
  by rewrite funeqE => n; rewrite /= oppeK.
apply: cvgeN.
rewrite [X in _ --> X](_ : _ = ereal_sup (range (-%E \o u_))); last first.
  congr ereal_sup; rewrite predeqE => x; split=> [[_ [n _ <-]] <-|[n _] <-];
    by [exists n | exists (u_ n) => //; exists n].
by apply: ereal_nondecreasing_cvg; rewrite ereal_nondecreasing_opp.
Qed.

Lemma ereal_nonincreasing_is_cvg (R : realType) (u_ : (\bar R) ^nat) :
  nonincreasing_seq u_ -> cvg u_.
Proof. by move=> ?; apply/cvg_ex; eexists; apply: ereal_nonincreasing_cvg. Qed.

(* NB: see also nondecreasing_series *)
Lemma ereal_nondecreasing_series (R : realDomainType) (u_ : (\bar R)^nat)
  (P : pred nat) : (forall n, P n -> 0 <= u_ n) ->
  nondecreasing_seq (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> u_ge0 n m nm; rewrite lee_sum_nneg_natr// => k _ /u_ge0. Qed.

Lemma eq_eseries (R : realFieldType) (f g : (\bar R)^nat) (P : pred nat) :
  (forall i, P i -> f i = g i) -> \sum_(i <oo | P i) f i = \sum_(i <oo | P i) g i.
Proof. by move=> efg; congr (lim _); apply/funext => n; exact: eq_bigr. Qed.

Section ereal_series.
Variables (R : realFieldType) (f : (\bar R)^nat).
Implicit Types P : pred nat.

Lemma ereal_series_cond k P :
  \sum_(k <= i <oo | P i) f i = \sum_(i <oo | (k <= i)%N && P i) f i.
Proof.
congr (lim _); apply/funext => n.
rewrite big_nat_cond (big_nat_widenl k 0%N)//= 2!big_mkord.
by apply: eq_big => //= i; rewrite andbAC ltn_ord andbT andbb.
Qed.

Lemma ereal_series k : \sum_(k <= i <oo) f i = \sum_(i <oo | (k <= i)%N) f i.
Proof.
rewrite ereal_series_cond; congr (lim _); apply/funext => n.
by apply: eq_big => // i; rewrite andbT.
Qed.

Lemma eseries0 P : (forall i, P i -> f i = 0) -> \sum_(i <oo | P i) f i = 0.
Proof. by move=> f0; under eq_fun do rewrite big1//; rewrite lim_cst. Qed.

Lemma eseries_pred0 P : P =1 xpred0 -> \sum_(i <oo | P i) f i = 0.
Proof.
move=> P0; rewrite (_ : (fun _ => _) = fun=> 0) ?lim_cst// funeqE => n.
by rewrite big1 // => i; rewrite P0.
Qed.

End ereal_series.

Lemma nneseries_lim_ge (R : realType) (u_ : (\bar R)^nat) (P : pred nat) k :
  (forall n, P n -> 0 <= u_ n) ->
  \sum_(0 <= i < k | P i) u_ i <= \sum_(i <oo | P i) u_ i.
Proof.
move/ereal_nondecreasing_series/ereal_nondecreasing_cvg/cvg_lim => -> //.
by apply: ereal_sup_ub; exists k.
Qed.

Lemma eseries_pinfty (R : realFieldType) (u_ : (\bar R)^nat)
    (P : pred nat) k : (forall n, P n -> u_ n != -oo) -> P k ->
  u_ k = +oo -> \sum_(i <oo | P i) u_ i = +oo.
Proof.
move=> uNy Pk uky; apply: lim_near_cst => //; near=> n.
apply/eqP; rewrite big_mkord esum_eqy; last first.
  by move=> /= i Pi; rewrite uNy.
apply/existsP.
have kn : (k < n)%N by near: n; exists k.+1.
by exists (Ordinal kn) => /=; rewrite uky eqxx andbT.
Unshelve. all: by end_near. Qed.

Section cvg_eseries.
Variable (R : realType) (u_ : (\bar R)^nat).
Implicit Type P : pred nat.

Lemma is_cvg_ereal_nneg_natsum_cond m P :
  (forall n, (m <= n)%N -> P n -> 0 <= u_ n) ->
cvg (fun n => \sum_(m <= i < n | P i) u_ i).
Proof.
by move/lee_sum_nneg_natr/ereal_nondecreasing_cvg => cu; apply: cvgP; exact: cu.
Qed.

Lemma is_cvg_ereal_npos_natsum_cond m P :
  (forall n, (m <= n)%N -> P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(m <= i < n | P i) u_ i).
Proof.
by move/lee_sum_npos_natr/ereal_nonincreasing_cvg => cu; apply: cvgP; exact: cu.
Qed.

Lemma is_cvg_ereal_nneg_natsum m : (forall n, (m <= n)%N -> 0 <= u_ n) ->
  cvg (fun n => \sum_(m <= i < n) u_ i).
Proof. by move=> u_ge0; apply: is_cvg_ereal_nneg_natsum_cond => n /u_ge0. Qed.

Lemma is_cvg_ereal_npos_natsum m : (forall n, (m <= n)%N -> u_ n <= 0) ->
  cvg (fun n => \sum_(m <= i < n) u_ i).
Proof. by move=> u_le0; apply: is_cvg_ereal_npos_natsum_cond => n /u_le0. Qed.

Lemma is_cvg_nneseries_cond P : (forall n, P n -> 0 <= u_ n) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> u_ge0; apply: is_cvg_ereal_nneg_natsum_cond => n _ /u_ge0. Qed.

Lemma is_cvg_npeseries_cond P : (forall n, P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> u_le0; apply: is_cvg_ereal_npos_natsum_cond => n _ /u_le0. Qed.

Lemma is_cvg_nneseries P : (forall n, P n -> 0 <= u_ n) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> ?; exact: is_cvg_nneseries_cond. Qed.

Lemma is_cvg_npeseries P : (forall n, P n -> u_ n <= 0) ->
  cvg (fun n => \sum_(0 <= i < n | P i) u_ i).
Proof. by move=> ?; exact: is_cvg_npeseries_cond. Qed.

Lemma nneseries_ge0 P : (forall n, P n -> 0 <= u_ n) ->
  0 <= \sum_(i <oo | P i) u_ i.
Proof.
move=> u0; apply: (lime_ge (is_cvg_nneseries u0)).
by apply: nearW => k; rewrite sume_ge0.
Qed.

Lemma npeseries_le0 P : (forall n : nat, P n -> u_ n <= 0) ->
  \sum_(i <oo | P i) u_ i <= 0.
Proof.
move=> u0; apply: (lime_le (is_cvg_npeseries u0)).
by apply: nearW => k; rewrite sume_le0.
Qed.

End cvg_eseries.
Arguments is_cvg_nneseries {R}.

Lemma nnseries_is_cvg {R : realType} (u : nat -> R) :
  (forall i, 0 <= u i)%R -> \sum_(k <oo) (u k)%:E < +oo -> cvg (series u).
Proof.
move=> ? ?; apply: nondecreasing_is_cvg.
  move=> m n mn; rewrite /series/=.
  rewrite -(subnKC mn) {2}/index_iota subn0 iotaD big_cat/=.
  by rewrite add0n -{2}(subn0 m) -/(index_iota _ _) ler_addl sumr_ge0.
exists (fine (\sum_(k <oo) (u k)%:E)).
rewrite /ubound/= => _ [n _ <-]; rewrite -lee_fin fineK//; last first.
  rewrite fin_num_abs gee0_abs//; apply: nneseries_ge0 => // i _.
  by rewrite lee_fin.
by rewrite -sumEFin; apply: nneseries_lim_ge => i _; rewrite lee_fin.
Qed.

Lemma nneseriesrM (R : realType) (f : nat -> \bar R) (P : pred nat) x :
  (forall i, P i -> 0 <= f i) ->
  (\sum_(i <oo | P i) (x%:E * f i) = x%:E * \sum_(i <oo | P i) f i).
Proof.
move=> f0; rewrite -limeMl//; last exact: is_cvg_nneseries.
by congr (lim _); apply/funext => /= n; rewrite ge0_sume_distrr.
Qed.

Lemma adde_def_nneseries (R : realType) (f g : (\bar R)^nat)
    (P Q : pred nat) :
  (forall n, P n -> 0 <= f n) -> (forall n, Q n -> 0 <= g n) ->
  (\sum_(i <oo | P i) f i) +? (\sum_(i <oo | Q i) g i).
Proof.
move=> f0 g0; rewrite /adde_def !negb_and; apply/andP; split; apply/orP.
- by right; apply/eqP => Qg; have := nneseries_ge0 g0; rewrite Qg.
- by left; apply/eqP => Pf; have := nneseries_ge0 f0; rewrite Pf.
Qed.

Lemma __deprecated__ereal_cvgPpinfty (R : realFieldType) (u_ : (\bar R)^nat) :
  u_ --> +oo <-> (forall A, (0 < A)%R -> \forall n \near \oo, A%:E <= u_ n).
Proof.
by split=> [/cvgeyPge//|u_ge]; apply/cvgeyPgey; near=> x; apply u_ge.
Unshelve. all: by end_near. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgeyPge` or a variant instead")]
Notation ereal_cvgPpinfty := __deprecated__ereal_cvgPpinfty.

Lemma __deprecated__ereal_cvgPninfty (R : realFieldType) (u_ : (\bar R)^nat) :
  u_ --> -oo <-> (forall A, (A < 0)%R -> \forall n \near \oo, u_ n <= A%:E).
Proof.
by split=> [/cvgeNyPle//|u_ge]; apply/cvgeNyPleNy; near=> x; apply u_ge.
Unshelve. all: by end_near. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgeNyPle` or a variant instead")]
Notation ereal_cvgPninfty := __deprecated__ereal_cvgPninfty.

Lemma __deprecated__ereal_squeeze (R : realType) (f g h : (\bar R)^nat) :
  (\forall x \near \oo, f x <= g x <= h x) -> forall (l : \bar R),
  f --> l -> h --> l -> g --> l.
Proof. by move=> ? ?; apply: squeeze_cvge. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `squeeze_cvge` and generalized")]
Notation ereal_squeeze := __deprecated__ereal_squeeze.

Lemma nneseries_pinfty (R : realType) (u_ : (\bar R)^nat)
  (P : pred nat) k : (forall n, P n -> 0 <= u_ n) -> P k ->
  u_ k = +oo -> \sum_(i <oo | P i) u_ i = +oo.
Proof.
move=> u_ge0 Pk ukoo; apply: (eseries_pinfty _ Pk ukoo) => // n Pn.
by rewrite gt_eqF// (lt_le_trans _ (u_ge0 _ Pn)).
Qed.

Lemma lee_nneseries (R : realType) (u v : (\bar R)^nat) (P : pred nat) :
  (forall i, P i -> 0 <= u i) -> (forall n, P n -> u n <= v n) ->
  \sum_(i <oo | P i) u i <= \sum_(i <oo | P i) v i.
Proof.
move=> u0 Puv; apply: lee_lim.
- by apply: is_cvg_ereal_nneg_natsum_cond => n _ /u0.
- apply: is_cvg_ereal_nneg_natsum_cond => n _ Pn.
  by rewrite (le_trans _ (Puv _ Pn))// u0.
- by near=> n; exact: lee_sum.
Unshelve. all: by end_near. Qed.

Lemma lee_npeseries (R : realType) (u v : (\bar R)^nat) (P : pred nat) :
  (forall i, P i -> u i <= 0) -> (forall n, P n -> v n <= u n) ->
  \sum_(i <oo | P i) v i <= \sum_(i <oo | P i) u i.
Proof.
move=> u0 Puv; apply: lee_lim.
- apply: is_cvg_ereal_npos_natsum_cond => n _ /[dup] Pn /Puv/le_trans; apply.
  exact/u0.
- by apply: is_cvg_ereal_npos_natsum_cond => n _ Pn; exact/u0.
- by near=> n; exact: lee_sum.
Unshelve. all: by end_near. Qed.

Lemma __deprecated__ereal_cvgD_pinfty_fin (R : realFieldType) (f g : (\bar R)^nat) b :
  f --> +oo -> g --> b%:E -> f \+ g --> +oo.
Proof. exact: cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeD` instead")]
Notation ereal_cvgD_pinfty_fin := __deprecated__ereal_cvgD_pinfty_fin.

Lemma __deprecated__ereal_cvgD_ninfty_fin (R : realFieldType) (f g : (\bar R)^nat) b :
  f --> -oo -> g --> b%:E -> f \+ g --> -oo.
Proof. exact: cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeD` instead")]
Notation ereal_cvgD_ninfty_fin := __deprecated__ereal_cvgD_ninfty_fin.

Lemma __deprecated__ereal_cvgD_pinfty_pinfty (R : realFieldType) (f g : (\bar R)^nat) :
  f --> +oo -> g --> +oo -> f \+ g --> +oo.
Proof. exact: cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeD` instead")]
Notation ereal_cvgD_pinfty_pinfty := __deprecated__ereal_cvgD_pinfty_pinfty.

Lemma __deprecated__ereal_cvgD_ninfty_ninfty (R : realFieldType) (f g : (\bar R)^nat) :
  f --> -oo -> g --> -oo -> f \+ g --> -oo.
Proof. exact: cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeD` instead")]
Notation ereal_cvgD_ninfty_ninfty := __deprecated__ereal_cvgD_ninfty_ninfty.

Lemma __deprecated__ereal_cvgD (R : realFieldType) (f g : (\bar R)^nat) a b :
  a +? b -> f --> a -> g --> b -> f \+ g --> a + b.
Proof. exact: cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgeD` and generalized")]
Notation ereal_cvgD := __deprecated__ereal_cvgD.

Section nneseries_split.

Lemma __deprecated__ereal_cvgB (R : realFieldType) (f g : (\bar R)^nat) a b :
  a +? - b -> f --> a -> g --> b -> f \- g --> a - b.
Proof. exact: cvgeB. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgeB` and generalized")]
Notation ereal_cvgB := __deprecated__ereal_cvgB.

Lemma __deprecated__ereal_is_cvgD (R : realFieldType) (u v : (\bar R)^nat) :
  lim u +? lim v -> cvg u -> cvg v -> cvg (u \+ v).
Proof. exact: is_cvgeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `is_cvgeD` and generalized")]
Notation ereal_is_cvgD := __deprecated__ereal_is_cvgD.

Lemma __deprecated__ereal_cvg_sub0 (R : realFieldType) (f : (\bar R)^nat) (k : \bar R) :
  k \is a fin_num -> (fun x => f x - k) --> 0 <-> f --> k.
Proof. exact: cvge_sub0. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvge_sub0` and generalized")]
Notation ereal_cvg_sub0 := __deprecated__ereal_cvg_sub0.

Lemma __deprecated__ereal_limD (R : realFieldType) (f g : (\bar R)^nat) :
  cvg f -> cvg g -> lim f +? lim g ->
  lim (f \+ g) = lim f + lim g.
Proof. exact: limeD. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `limeD` and generalized")]
Notation ereal_limD := __deprecated__ereal_limD.

Lemma __deprecated__ereal_cvgM_gt0_pinfty (R : realFieldType) (f g : (\bar R)^nat) b :
  (0 < b)%R -> f --> +oo -> g --> b%:E -> f \* g --> +oo.
Proof.
move=> b_lt0 fl gl; have /= := cvgeM _ fl gl; rewrite gt0_mulye//; apply.
by rewrite mule_def_infty_neq0// gt_eqF.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeM` instead")]
Notation ereal_cvgM_gt0_pinfty := __deprecated__ereal_cvgM_gt0_pinfty.

Lemma __deprecated__ereal_cvgM_lt0_pinfty (R : realFieldType) (f g : (\bar R)^nat) b :
  (b < 0)%R -> f --> +oo -> g --> b%:E -> f \* g --> -oo.
Proof.
move=> b_lt0 fl gl; have /= := cvgeM _ fl gl; rewrite lt0_mulye//; apply.
by rewrite mule_def_infty_neq0// lt_eqF.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeM` instead")]
Notation ereal_cvgM_lt0_pinfty := __deprecated__ereal_cvgM_lt0_pinfty.

Lemma __deprecated__ereal_cvgM_gt0_ninfty (R : realFieldType) (f g : (\bar R)^nat) b :
  (0 < b)%R -> f --> -oo -> g --> b%:E -> f \* g --> -oo.
Proof.
move=> b_lt0 fl gl; have /= := cvgeM _ fl gl; rewrite gt0_mulNye//; apply.
by rewrite mule_def_infty_neq0// gt_eqF.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeM` instead")]
Notation ereal_cvgM_gt0_ninfty := __deprecated__ereal_cvgM_gt0_ninfty.

Lemma __deprecated__ereal_cvgM_lt0_ninfty (R : realFieldType) (f g : (\bar R)^nat) b :
  (b < 0)%R -> f --> -oo -> g --> b%:E -> f \* g --> +oo.
Proof.
move=> b_lt0 fl gl; have /= := cvgeM _ fl gl; rewrite lt0_mulNye//; apply.
by rewrite mule_def_infty_neq0// lt_eqF.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0", note="use `cvgeM` instead")]
Notation ereal_cvgM_lt0_ninfty := __deprecated__ereal_cvgM_lt0_ninfty.

Lemma __deprecated__ereal_cvgM (R : realType) (f g : (\bar R) ^nat) (a b : \bar R) :
 a *? b -> f --> a -> g --> b -> f \* g --> a * b.
Proof. exact: cvgeM. Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgeM` and generalized")]
Notation ereal_cvgM := __deprecated__ereal_cvgM.

Lemma __deprecated__ereal_lim_sum (R : realFieldType) (I : Type) (r : seq I)
    (f : I -> (\bar R)^nat) (l : I -> \bar R) (P : pred I) :
  (forall k n, P k -> 0 <= f k n) ->
  (forall k, P k -> f k --> l k) ->
  (fun n => \sum_(k <- r | P k) f k n) --> \sum_(k <- r | P k) l k.
Proof.
by move=> f0 ?; apply: cvg_nnesum => // ? ?; apply: nearW => ?; apply: f0.
Qed.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvg_nnesum` and generalized")]
Notation ereal_lim_sum := __deprecated__ereal_lim_sum.

Let lim_shift_cst (R : realFieldType) (u : (\bar R) ^nat) (l : \bar R) :
  cvg u -> (forall n, 0 <= u n) -> -oo < l -> lim (fun x => l + u x) = l + lim u.
Proof.
move=> cu u0 hl; apply/cvg_lim => //; apply: cvgeD (cu); last first.
  exact: cvg_cst.
rewrite ltninfty_adde_def// inE (@lt_le_trans _ _ 0)//.
by apply: lime_ge => //; exact: nearW.
Qed.

Let near_eq_lim (R : realFieldType) (f g : nat -> \bar R) :
  cvg g -> {near \oo, f =1 g} -> lim f = lim g.
Proof.
move=> cg fg; suff: f --> lim g by exact/cvg_lim.
by apply: cvg_trans cg; apply: near_eq_cvg; near do apply/esym.
Unshelve. all: by end_near. Qed.

Lemma nneseries_split (R : realType) (f : nat -> \bar R) n :
  (forall k, 0 <= f k) ->
  \sum_(k <oo) f k = \sum_(k < n) f k + \sum_(n <= k <oo) f k.
Proof.
move=> f0; elim: n => [|n ih]; first by rewrite big_ord0 add0e.
rewrite big_ord_recr/= -addeA [f n + _](_ : _ = \sum_(n <= k <oo) f k)//.
rewrite -lim_shift_cst; last by rewrite (@lt_le_trans _ _ 0).
- apply: (@near_eq_lim _ (fun x => f n + _)).
    exact: is_cvg_ereal_nneg_natsum.
  by near do rewrite -big_ltn//; exact: nbhs_infty_gt.
- exact: is_cvg_ereal_nneg_natsum.
- by move=> m; exact: sume_ge0.
Unshelve. all: by end_near. Qed.

End nneseries_split.

Lemma nneseriesD (R : realType) (f g : nat -> \bar R) (P : pred nat) :
  (forall i, P i -> 0 <= f i) -> (forall i, P i -> 0 <= g i) ->
  \sum_(i <oo | P i) (f i + g i) =
  \sum_(i <oo | P i) f i + \sum_(i <oo | P i) g i.
Proof.
move=> f_eq0 g_eq0.
transitivity (lim (fun n => \sum_(0 <= i < n | P i) f i +
                         \sum_(0 <= i < n | P i) g i)).
  by congr (lim _); apply/funext => n; rewrite big_split.
rewrite limeD /adde_def //=; do ? exact: is_cvg_nneseries.
by rewrite ![_ == -oo]gt_eqF ?andbF// (@lt_le_trans _ _ 0)
           ?[_ < _]real0// nneseries_ge0.
Qed.

Lemma nneseries_sum_nat (R : realType) n (f : nat -> nat -> \bar R) :
  (forall i j, 0 <= f i j) ->
  \sum_(j <oo) (\sum_(0 <= i < n) f i j) =
  \sum_(0 <= i < n) (\sum_(j <oo) (f i j)).
Proof.
move=> f0; elim: n => [|n IHn].
  by rewrite big_geq// eseries0// => i; rewrite big_geq.
rewrite big_nat_recr// -IHn/= -nneseriesD//; last by move=> i; rewrite sume_ge0.
by congr (lim _); apply/funext => m; apply: eq_bigr => i _; rewrite big_nat_recr.
Qed.

Lemma nneseries_sum I (r : seq I) (P : {pred I})
    [R : realType] [f : I -> nat -> \bar R] :
    (forall i j, P i -> 0 <= f i j) ->
  \sum_(j <oo) \sum_(i <- r | P i) f i j = \sum_(i <- r | P i) \sum_(j <oo) f i j.
Proof.
move=> f_ge0; case Dr : r => [|i r']; rewrite -?{}[_ :: _]Dr.
  by rewrite big_nil eseries0// => i; rewrite big_nil.
rewrite {r'}(big_nth i) big_mkcond.
rewrite (eq_eseries (fun _ _ => big_nth i _ _)).
rewrite (eq_eseries (fun _ _ => big_mkcond _ _))/=.
rewrite nneseries_sum_nat; last by move=> ? ?; case: ifP => // /f_ge0.
by apply: eq_bigr => j _; case: ifP => //; rewrite eseries0.
Qed.

Lemma lte_lim (R : realFieldType) (u : (\bar R)^nat) (M : R) :
  nondecreasing_seq u -> cvg u -> M%:E < lim u ->
  \forall n \near \oo, M%:E <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|] := pselect (exists n, M%:E <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
move/forallNP => Mu.
have {}Mu : forall x, M%:E > u x by move=> x; rewrite ltNge; apply/negP.
have : lim u <= M%:E by apply lime_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near. Qed.

Lemma lim_mkord (R : realFieldType) (P : {pred nat}) (f : (\bar R)^nat) :
  lim (fun n => \sum_(k < n | P k) f k)%E = \sum_(k <oo | P k) f k.
Proof.
rewrite (_ : (fun n => _) = (fun n => \sum_(0 <= k < n | P k) f k)%E) //.
by rewrite funeqE => k; rewrite big_mkord.
Qed.

Lemma eseries_mkcond [R : realFieldType] [P : pred nat] (f : nat -> \bar R) :
  \sum_(i <oo | P i) f i = \sum_(i <oo) if P i then f i else 0.
Proof. by congr (lim _); apply: eq_fun => n /=; apply: big_mkcond. Qed.

End sequences_ereal.
#[deprecated(since="analysis 0.6.0", note="Use eseries0 instead.")]
Notation nneseries0 := eseries0.
#[deprecated(since="analysis 0.6.0", note="Use eq_eseries instead.")]
Notation eq_nneseries := eq_eseries.
#[deprecated(since="analysis 0.6.0", note="Use eseries_pred0 instead.")]
Notation nneseries_pred0 := eseries_pred0.
#[deprecated(since="analysis 0.6.0", note="Use eseries_mkcond instead.")]
Notation nneseries_mkcond := eseries_mkcond.

Definition sdrop T (u : T^nat) n := [set u k | k in [set k | k >= n]]%N.

Section sdrop.
Variables (d : unit) (R : porderType d).
Implicit Types (u : R^o^nat).

Lemma has_lbound_sdrop u : has_lbound (range u) ->
  forall m, has_lbound (sdrop u m).
Proof.
by move=> [M uM] n; exists M => _ [m /= nm] <-; rewrite uM //; exists m.
Qed.

Lemma has_ubound_sdrop u : has_ubound (range u) ->
  forall m, has_ubound (sdrop u m).
Proof.
by move=> [M uM] n; exists M => _ [m /= nm] <-; rewrite uM //; exists m.
Qed.

End sdrop.

Section sups_infs.
Variable R : realType.
Implicit Types (r : R) (u : R^o^nat).

Definition sups u := [sequence sup (sdrop u n)]_n.

Definition infs u := [sequence inf (sdrop u n)]_n.

Lemma supsN u : sups (-%R \o u) = - infs u.
Proof.
rewrite funeqE => n; rewrite /sups /infs /inf /= opprK; congr (sup _).
by rewrite predeqE => x; split => [[m /= nm <-]|[_ [m /= nm] <-] <-];
  [exists (u m) => //; exists m | exists m].
Qed.

Lemma infsN u : infs (-%R \o u) = - sups u.
Proof.
apply/eqP; rewrite -eqr_oppLR -supsN; apply/eqP; congr (sups _).
by rewrite funeqE => ? /=; rewrite opprK.
Qed.

Lemma nonincreasing_sups u : has_ubound (range u) ->
  nonincreasing_seq (sups u).
Proof.
move=> u_ub m n mn; apply: le_sup => [_ /= [p np] <-| |].
- by apply/downP; exists (u p) => //=; exists p => //; exact: leq_trans np.
- by exists (u n) => /=; exists n => /=.
- by split; [exists (u m); exists m => //=|exact/has_ubound_sdrop].
Qed.

Lemma nondecreasing_infs u : has_lbound (range u) ->
  nondecreasing_seq (infs u).
Proof.
move=> u_lb; rewrite -nonincreasing_opp -supsN; apply/nonincreasing_sups.
by move: u_lb => /has_lb_ubN; rewrite /comp /= image_comp.
Qed.

Lemma is_cvg_sups u : cvg u -> cvg (sups u).
Proof.
move=> cf; have [M [Mreal Mu]] := cvg_seq_bounded cf.
apply: nonincreasing_is_cvg.
  exact/nonincreasing_sups/bounded_fun_has_ubound/cvg_seq_bounded.
exists (- (M + 1)) => _ [n _ <-]; rewrite (@le_trans _ _ (u n)) //.
  by apply/lerNnormlW/Mu => //; rewrite ltr_addl.
apply: sup_ub; last by exists n => /=.
exact/has_ubound_sdrop/bounded_fun_has_ubound/cvg_seq_bounded.
Qed.

Lemma is_cvg_infs u : cvg u -> cvg (infs u).
Proof.
move/is_cvgN/is_cvg_sups; rewrite supsN.
by move/(@is_cvgN _ [normedModType R of R^o]); rewrite opprK.
Qed.

Lemma infs_le_sups u n : cvg u -> infs u n <= sups u n.
Proof.
move=> cu; rewrite /infs /sups /=; set A := sdrop _ _.
have [a Aa] : A !=set0 by exists (u n); rewrite /A /=; exists n => //=.
rewrite (@le_trans _ _ a) //; [apply/inf_lb|apply/sup_ub] => //.
- exact/has_lbound_sdrop/bounded_fun_has_lbound/cvg_seq_bounded.
- exact/has_ubound_sdrop/bounded_fun_has_ubound/cvg_seq_bounded.
Qed.

Lemma cvg_sups_inf u : has_ubound (range u) -> has_lbound (range u) ->
  sups u --> inf (range (sups u)).
Proof.
move=> u_ub u_lb.
apply: nonincreasing_cvg; first exact: nonincreasing_sups.
case: u_lb => M uM; exists M => _ [n _ <-].
rewrite (@le_trans _ _ (u n)) //; first by apply uM; exists n.
by apply: sup_ub; [exact/has_ubound_sdrop|exists n => /=].
Qed.

Lemma cvg_infs_sup u : has_ubound (range u) -> has_lbound (range u) ->
  infs u --> sup (range (infs u)).
Proof.
move=> u_ub u_lb; have : sups (- u) --> inf (range (sups (- u))).
  apply: cvg_sups_inf.
  - by move: u_lb => /has_lb_ubN; rewrite image_comp.
  - by move: u_ub => /has_ub_lbN; rewrite image_comp.
rewrite /inf => /(@cvg_comp _ _ _ _ (fun x => - x)).
rewrite supsN /comp /= -[in X in _ -> X --> _](opprK (infs u)); apply.
rewrite image_comp /comp /= -(opprK (sup (range (infs u)))).
apply: (@cvgN _ [normedModType R of R^o]).
by rewrite (_ : [set _ | _ in setT] = (range (infs u))) // opprK.
Qed.

Lemma sups_preimage T (D : set T) r (f : (T -> R)^nat) n :
  (forall t, D t -> has_ubound (range (f ^~ t))) ->
  D `&` (fun x => sups (f ^~x) n) @^-1` `]r, +oo[%classic =
  D `&` \bigcup_(k in [set k | n <= k]%N) f k @^-1` `]r, +oo[.
Proof.
move=> f_ub; rewrite predeqE => t; split.
- have [|/set0P h] := eqVneq (sdrop (f ^~ t) n) set0.
    by rewrite predeqE => /(_ (f n t))[+ _] => /forall2NP/(_ n)/= [].
  rewrite /= in_itv /= andbT => -[Dt].
  move=> /(sup_gt h)[_ [m /= nm <-]] rfmt. split => //; exists m => //.
  by rewrite /= in_itv /= rfmt.
- move=> [Dt [k /= nk]]; rewrite in_itv /= andbT => rfkt.
  split=> //; rewrite /= in_itv /= andbT; apply: (lt_le_trans rfkt).
  by apply: sup_ub; [exact/has_ubound_sdrop/f_ub|by exists k].
Qed.

Lemma infs_preimage T (D : set T) r (f : (T -> R)^nat) n :
  (forall t, D t -> has_lbound (range (f ^~ t))) ->
  D `&` (fun x => infs (f ^~ x) n) @^-1` `]-oo, r[ =
  D `&` \bigcup_(k in [set k | n <= k]%N) f k @^-1` `]-oo, r[.
Proof.
move=> lb_f; rewrite predeqE => t; split.
- have [|/set0P h] := eqVneq (sdrop (f ^~ t) n) set0.
    by rewrite predeqE => /(_ (f n t))[+ _] => /forall2NP/(_ n)/= [].
  rewrite /= in_itv /= => -[Dt].
  by move=>  /(inf_lt h)[_ [m /= nm <-]] fmtr; split => //; exists m.
- move=> [Dt [k /= nk]]; rewrite /= in_itv /= => fktr.
  rewrite in_itv /=; split => //; apply: le_lt_trans fktr.
  by apply/inf_lb => //; [exact/has_lbound_sdrop/lb_f|by exists k].
Qed.

Lemma bounded_fun_has_lbound_sups u :
  bounded_fun u -> has_lbound (range (sups u)).
Proof.
move=> /[dup] ba /bounded_fun_has_lbound/has_lbound_sdrop h.
have [M hM] := h O; exists M => y [n _ <-].
rewrite (@le_trans _ _ (u n)) //; first by apply hM; exists n.
apply: sup_ub; last by exists n => /=.
by move: ba => /bounded_fun_has_ubound/has_ubound_sdrop; exact.
Qed.

Lemma bounded_fun_has_ubound_infs u :
  bounded_fun u -> has_ubound (range (infs u)).
Proof.
move=> /[dup] ba /bounded_fun_has_ubound/has_ubound_sdrop h.
have [M hM] := h O; exists M => y [n _ <-].
rewrite (@le_trans _ _ (u n)) //; last by apply hM; exists n.
apply: inf_lb; last by exists n => /=.
by move: ba => /bounded_fun_has_lbound/has_lbound_sdrop; exact.
Qed.

End sups_infs.

Section lim_sup_lim_inf.
Variable R : realType.
Implicit Types (r : R) (u v : R^o^nat).

Definition lim_sup u := lim (sups u).

Definition lim_inf u := lim (infs u).

Lemma lim_infN u : cvg u -> lim_inf (-%R \o u) = - lim_sup u.
Proof.
move=> cu_; rewrite /lim_inf infsN.
rewrite (@limN _ [normedModType R of R^o] _ _ _ (sups u)) //.
exact: is_cvg_sups.
Qed.

Lemma lim_supE u : bounded_fun u -> lim_sup u = inf (range (sups u)).
Proof.
move=> ba; apply/cvg_lim; first exact: Rhausdorff.
by apply/cvg_sups_inf; [exact/bounded_fun_has_ubound|
                        exact/bounded_fun_has_lbound].
Qed.

Lemma lim_infE u : bounded_fun u -> lim_inf u = sup (range (infs u)).
Proof.
move=> ba; apply/cvg_lim; first exact: Rhausdorff.
apply/cvg_infs_sup; [exact/bounded_fun_has_ubound|
                     exact/bounded_fun_has_lbound].
Qed.

Lemma lim_inf_le_lim_sup u : cvg u -> lim_inf u <= lim_sup u.
Proof.
move=> cf_; apply: ler_lim; [exact: is_cvg_infs|exact: is_cvg_sups|].
by apply: nearW => n; apply: infs_le_sups.
Qed.

Lemma cvg_lim_inf_sup u l : u --> l -> (lim_inf u = l) * (lim_sup u = l).
Proof.
move=> ul.
have /cvg_seq_bounded [M [Mr Mu]] : cvg u by apply/cvg_ex; eexists; exact: ul.
suff: lim_sup u <= l <= lim_inf u.
  move=> /andP[sul liu].
  have /lim_inf_le_lim_sup iusu : cvg u by apply/cvg_ex; eexists; exact: ul.
  split; first by apply/eqP; rewrite eq_le liu andbT (le_trans iusu).
  by apply/eqP; rewrite eq_le sul /= (le_trans _ iusu).
apply/andP; split.
- apply/ler_addgt0Pr => e e0.
  apply: limr_le; first by apply: is_cvg_sups; apply/cvg_ex; exists l.
  move/cvgrPdist_lt : (ul) => /(_ _ e0) -[k _ klu].
  near=> n; have kn : (k <= n)%N by near: n; exists k.
  apply: sup_le_ub; first by exists (u n) => /=; exists n => //=.
  move=> _ /= [m nm] <-; apply/ltW/ltr_distl_addr; rewrite distrC.
  by apply: (klu m) => /=; rewrite (leq_trans kn).
- apply/ler_addgt0Pr => e e0; rewrite -ler_subl_addr.
  apply: limr_ge; first by apply: is_cvg_infs; apply/cvg_ex; exists l.
  move/cvgrPdist_lt : (ul) => /(_ _ e0) -[k _ klu].
  near=> n; have kn: (k <= n)%N by near: n; exists k.
  apply: lb_le_inf; first by exists (u n) => /=; exists n => //=.
  move=> _ /= [m nm] <-; apply/ltW/ltr_distl_subl.
  by apply: (klu m) => /=; rewrite (leq_trans kn).
Unshelve. all: by end_near. Qed.

Lemma cvg_lim_infE u : cvg u -> lim_inf u = lim u.
Proof.
move=> /cvg_ex[l ul]; have [-> _] := cvg_lim_inf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma cvg_lim_supE u : cvg u -> lim_sup u = lim u.
Proof.
move=> /cvg_ex[l ul]; have [_ ->] := cvg_lim_inf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma cvg_sups u l : u --> l -> (sups u) --> (l : R^o).
Proof.
move=> ul; have [iul <-] := cvg_lim_inf_sup ul.
apply/cvg_closeP; split => //; apply: is_cvg_sups.
by apply/cvg_ex; eexists; apply: ul.
Qed.

Lemma cvg_infs u l : u --> l -> (infs u) --> (l : R^o).
Proof.
move=> ul; have [<- iul] := cvg_lim_inf_sup ul.
apply/cvg_closeP; split => //; apply: is_cvg_infs.
by apply/cvg_ex; eexists; apply: ul.
Qed.

Lemma le_lim_supD u v :
  bounded_fun u -> bounded_fun v -> lim_sup (u \+ v) <= lim_sup u + lim_sup v.
Proof.
move=> ba bb; have ab k : sups (u \+ v) k <= sups u k + sups v k.
  apply: sup_le_ub; first by exists ((u \+ v) k); exists k => /=.
  by move=> M [n /= kn <-]; apply: ler_add; apply: sup_ub; [
    exact/has_ubound_sdrop/bounded_fun_has_ubound; exact | exists n |
    exact/has_ubound_sdrop/bounded_fun_has_ubound; exact | exists n ].
have cu : cvg (sups u).
  apply: nonincreasing_is_cvg; last exact: bounded_fun_has_lbound_sups.
  exact/nonincreasing_sups/bounded_fun_has_ubound.
have cv : cvg (sups v).
  apply: nonincreasing_is_cvg; last exact: bounded_fun_has_lbound_sups.
  exact/nonincreasing_sups/bounded_fun_has_ubound.
rewrite -(@limD _ [normedModType R of R^o] _ _ _ _ _ cu cv); apply: ler_lim.
- apply: nonincreasing_is_cvg; last first.
    exact/bounded_fun_has_lbound_sups/bounded_funD.
  exact/nonincreasing_sups/bounded_fun_has_ubound/bounded_funD.
- exact: (@is_cvgD _ [normedModType R of R^o] _ _ _ _ _ cu cv).
- exact: nearW.
Qed.

Lemma le_lim_infD u v :
  bounded_fun u -> bounded_fun v -> lim_inf u + lim_inf v <= lim_inf (u \+ v).
Proof.
move=> ba bb; have ab k : infs u k + infs v k <= infs (u \+ v) k.
  apply: lb_le_inf; first by exists ((u \+ v) k); exists k => /=.
  by move=> M [n /= kn <-]; apply: ler_add; apply: inf_lb; [
    exact/has_lbound_sdrop/bounded_fun_has_lbound; exact | exists n |
    exact/has_lbound_sdrop/bounded_fun_has_lbound; exact | exists n ].
have cu : cvg (infs u).
  apply: nondecreasing_is_cvg; last exact: bounded_fun_has_ubound_infs.
  exact/nondecreasing_infs/bounded_fun_has_lbound.
have cv : cvg (infs v).
  apply: nondecreasing_is_cvg; last exact: bounded_fun_has_ubound_infs.
  exact/nondecreasing_infs/bounded_fun_has_lbound.
rewrite -(@limD _ [normedModType R of R^o] _ _ _ _ _ cu cv); apply: ler_lim.
- exact: (@is_cvgD _ [normedModType R of R^o] _ _ _ _ _ cu cv).
- apply: nondecreasing_is_cvg; last first.
    exact/bounded_fun_has_ubound_infs/bounded_funD.
  exact/nondecreasing_infs/bounded_fun_has_lbound/bounded_funD.
- exact: nearW.
Qed.

Lemma lim_supD u v : cvg u -> cvg v -> lim_sup (u \+ v) = lim_sup u + lim_sup v.
Proof.
move=> cu cv; have [ba bb] := (cvg_seq_bounded cu, cvg_seq_bounded cv).
apply/eqP; rewrite eq_le le_lim_supD //=.
have := @le_lim_supD _ _ (bounded_funD ba bb) (bounded_funN bb).
rewrite -ler_subl_addr; apply: le_trans.
rewrite -[_ \+ _]/(u + v - v) addrK -lim_infN; last exact: is_cvgN.
rewrite /comp /=; under eq_fun do rewrite opprK.
by rewrite ler_add// cvg_lim_infE// cvg_lim_supE.
Qed.

Lemma lim_infD u v : cvg u -> cvg v -> lim_inf (u \+ v) = lim_inf u + lim_inf v.
Proof.
move=> cu cv; rewrite (cvg_lim_infE cu) -(cvg_lim_supE cu).
rewrite (cvg_lim_infE cv) -(cvg_lim_supE cv) -lim_supD//.
rewrite cvg_lim_supE; last exact: (@is_cvgD _ _ _ _ _ _ _ cu cv).
by rewrite cvg_lim_infE //; exact: (@is_cvgD _ _ _ _ _ _ _ cu cv).
Qed.

End lim_sup_lim_inf.

Section esups_einfs.
Variable R : realType.
Implicit Types (u : (\bar R)^nat).
Local Open Scope ereal_scope.

Definition esups u := [sequence ereal_sup (sdrop u n)]_n.

Definition einfs u := [sequence ereal_inf (sdrop u n)]_n.

Lemma esupsN u : esups (-%E \o u) = -%E \o einfs u.
Proof.
rewrite funeqE => n; rewrite /esups /= oppeK; congr (ereal_sup _).
by rewrite predeqE => x; split => [[m /= nm <-]|[_ [m /= nm] <-] <-];
  [exists (u m) => //; exists m | exists m].
Qed.

Lemma einfsN u : einfs (-%E \o u) = -%E \o esups u.
Proof.
by rewrite [in RHS](_ : u = -%E \o -%E \o u);
  rewrite ?esupsN funeqE => n /=; rewrite oppeK.
Qed.

Lemma nonincreasing_esups u : nonincreasing_seq (esups u).
Proof.
move=> m n mn; apply: le_ereal_sup => _ /= [k nk <-]; exists k => //=.
by rewrite (leq_trans mn).
Qed.

Lemma nondecreasing_einfs u : nondecreasing_seq (einfs u).
Proof.
move=> m n mn; apply: le_ereal_inf => _ /= [k nk <-]; exists k => //=.
by rewrite (leq_trans mn).
Qed.

Lemma einfs_le_esups u n : einfs u n <= esups u n.
Proof.
rewrite /einfs /=; set A := sdrop _ _; have [a Aa] : A !=set0.
  by exists (u n); rewrite /A /=; exists n => //=.
by rewrite (@le_trans _ _ a) //; [exact/ereal_inf_lb|exact/ereal_sup_ub].
Unshelve. all: by end_near. Qed.

Lemma cvg_esups_inf u : esups u --> ereal_inf (range (esups u)).
Proof. by apply: ereal_nonincreasing_cvg => //; exact: nonincreasing_esups. Qed.

Lemma is_cvg_esups u : cvg (esups u).
Proof. by apply/cvg_ex; eexists; exact/cvg_esups_inf. Qed.

Lemma cvg_einfs_sup u : einfs u --> ereal_sup (range (einfs u)).
Proof. by apply: ereal_nondecreasing_cvg => //; exact: nondecreasing_einfs. Qed.

Lemma is_cvg_einfs u : cvg (einfs u).
Proof. by apply/cvg_ex; eexists; exact/cvg_einfs_sup. Qed.

Lemma esups_preimage T (a : \bar R) (f : (T -> \bar R)^nat) n :
  (fun x => esups (f^~x) n) @^-1` `]a, +oo[ =
  \bigcup_(k in [set k | n <= k]%N) f k @^-1` `]a, +oo[.
Proof.
rewrite predeqE => t; split => /=.
  rewrite /= in_itv /= andbT=> /ereal_sup_gt[_ [/= k nk <-]] afnt.
  by exists k => //=; rewrite in_itv /= afnt.
move=> -[k /= nk] /=; rewrite in_itv /= andbT => /lt_le_trans afkt.
by rewrite in_itv andbT/=; apply/afkt/ereal_sup_ub; exists k.
Qed.

Lemma einfs_preimage T (a : \bar R) (f : (T -> \bar R)^nat) n :
  (fun x => einfs (f^~x) n) @^-1` `[a, +oo[%classic =
  \bigcap_(k in [set k | n <= k]%N) f k @^-1` `[a, +oo[%classic.
Proof.
rewrite predeqE => t; split => /= [|h].
  rewrite in_itv andbT /= => h k nk /=.
  by rewrite /= in_itv/= (le_trans h)//; apply ereal_inf_lb; exists k.
rewrite /= in_itv /= andbT leNgt; apply/negP.
move=> /ereal_inf_lt[_ /= [k nk <-]]; apply/negP.
by have := h _ nk; rewrite /= in_itv /= andbT -leNgt.
Qed.

End esups_einfs.

Module LimSup.
Definition lim_esup (R : realType) (u : (\bar R)^nat) := lim (esups u).
Definition lim_einf (R : realType) (u : (\bar R)^nat) := lim (einfs u).
End LimSup.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_esup`")]
Notation elim_sup := LimSup.lim_esup.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_einf`")]
Notation elim_inf := LimSup.lim_einf.

Notation lim_esup := LimSup.lim_esup.
Notation lim_einf := LimSup.lim_einf.

Section lim_esup_inf.
Local Open Scope ereal_scope.
Variable R : realType.
Implicit Types (u v : (\bar R)^nat) (l : \bar R).

Lemma lim_einf_shift u l : l \is a fin_num ->
  lim_einf (fun x => l + u x) = l + lim_einf u.
Proof.
move=> lfin; apply/cvg_lim => //; apply: cvg_trans; last first.
  apply: (@cvgeD _ \oo _ _ (cst l) (einfs u) _ (lim (einfs u))).
  - by rewrite adde_defC fin_num_adde_def.
  - exact: cvg_cst.
  - exact: is_cvg_einfs.
suff : einfs (fun n => l + u n) = (fun n => l + einfs u n) by move=> ->.
rewrite funeqE => n.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite addeC -lee_subl_addr//; apply: lb_ereal_inf => /= _ [m /= mn] <-.
  rewrite lee_subl_addr//; apply: ereal_inf_lb.
  by exists m => //; rewrite addeC.
- apply: lb_ereal_inf => /= _ [m /= mn] <-.
  by rewrite lee_add2l//; apply: ereal_inf_lb; exists m => /=.
Qed.

Lemma lim_esup_le_cvg u l : lim_esup u <= l -> (forall n, l <= u n) -> u --> l.
Proof.
move=> supul ul; have usupu n : l <= u n <= esups u n.
  by rewrite ul /=; apply/ereal_sup_ub; exists n => /=.
suff : esups u --> l.
  by apply: (@squeeze_cvge _ _ _ _ (cst l)) => //; [exact: nearW|exact: cvg_cst].
apply/cvg_closeP; split; first exact: is_cvg_esups.
rewrite closeE//; apply/eqP; rewrite eq_le supul.
apply: (lime_ge (@is_cvg_esups _ _)); apply: nearW => m.
have /le_trans : l <= einfs u m by apply: lb_ereal_inf => _ [p /= pm] <-.
by apply; exact: einfs_le_esups.
Qed.

Lemma lim_einfN u : lim_einf (-%E \o u) = - lim_esup u.
Proof.
by rewrite /lim_einf einfsN /lim_esup limeN //; exact/is_cvg_esups.
Qed.

Lemma lim_esupN u : lim_esup (-%E \o u) = - lim_einf u.
Proof.
apply/eqP; rewrite -eqe_oppLR -lim_einfN /=.
by rewrite (_ : _ \o _ = u) // funeqE => n /=; rewrite oppeK.
Qed.

Lemma lim_einf_sup u : lim_einf u <= lim_esup u.
Proof.
apply: lee_lim; [exact/is_cvg_einfs|exact/is_cvg_esups|].
by apply: nearW; exact: einfs_le_esups.
Qed.

Lemma cvgNy_lim_einf_sup u : u --> -oo ->
  (lim_einf u = -oo) * (lim_esup u = -oo).
Proof.
move=> uoo; suff: lim_esup u = -oo.
  by move=> {}uoo; split => //; apply/eqP; rewrite -leeNy_eq -uoo lim_einf_sup.
apply: cvg_lim => //=. apply/cvgeNyPle => M.
have /cvgeNyPle/(_ M)[m _ uM] := uoo.
near=> n; apply: ub_ereal_sup => _ [k /= nk <-].
by apply: uM => /=; rewrite (leq_trans _ nk)//; near: n; exists m.
Unshelve. all: by end_near. Qed.

Lemma cvgNy_einfs u : u --> -oo -> einfs u --> -oo.
Proof.
move=> /cvgNy_lim_einf_sup[uoo _].
by apply/cvg_closeP; split; [exact: is_cvg_einfs|rewrite closeE].
Qed.

Lemma cvgNy_esups u : u --> -oo -> esups u --> -oo.
Proof.
move=> /cvgNy_lim_einf_sup[_ uoo].
by apply/cvg_closeP; split; [exact: is_cvg_esups|rewrite closeE].
Qed.

Lemma cvgy_einfs u : u --> +oo -> einfs u --> +oo.
Proof.
move=> /cvgeN/cvgNy_esups/cvgeN; rewrite esupsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvgy_esups u : u --> +oo -> esups u --> +oo.
Proof.
move=> /cvgeN/cvgNy_einfs/cvgeN; rewrite einfsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvg_esups u l : u --> l -> esups u --> l.
Proof.
case: l => [l /fine_cvgP[u_fin_num] ul| |]; last 2 first.
  - exact: cvgy_esups.
  - exact: cvgNy_esups.
have [p _ pu] := u_fin_num; apply/cvg_ballP => _/posnumP[e].
have : EFin \o sups (fine \o u) --> l%:E.
  by apply: continuous_cvg => //; apply: cvg_sups.
move=> /cvg_ballP /(_ e%:num (gt0 _))[q _ qsupsu]; near=> n.
have -> : esups u n = (EFin \o sups (fine \o u)) n.
  rewrite /= -ereal_sup_EFin; last 2 first.
    - apply/has_ubound_sdrop/bounded_fun_has_ubound.
      by apply/cvg_seq_bounded/cvg_ex; eexists; exact ul.
    - by eexists; rewrite /sdrop /=; exists n; [|reflexivity].
  congr (ereal_sup _).
  rewrite predeqE => y; split=> [[m /= nm <-{y}]|[r [m /= nm <-{r} <-{y}]]].
    have /pu : (p <= m)%N by rewrite (leq_trans _ nm) //; near: n; exists p.
    by move=> /fineK umE; eexists; [exists m|exact/umE].
  have /pu : (p <= m)%N by rewrite (leq_trans _ nm) //; near: n; exists p.
  by move=> /fineK umE; exists m => //; exact/umE.
by apply: qsupsu => /=; near: n; exists q.
Unshelve. all: by end_near. Qed.

Lemma cvg_einfs u l : u --> l -> einfs u --> l.
Proof.
move=> /cvgeN/cvg_esups/cvgeN; rewrite oppeK esupsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvg_lim_einf_sup u l : u --> l -> (lim_einf u = l) * (lim_esup u = l).
Proof.
by move=> ul; split; apply/cvg_lim => //; [apply/cvg_einfs|apply/cvg_esups].
Qed.

Lemma is_cvg_lim_einfE u : cvg u -> lim_einf u = lim u.
Proof.
move=> /cvg_ex[l ul]; have [-> _] := cvg_lim_einf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma is_cvg_lim_esupE u : cvg u -> lim_esup u = lim u.
Proof.
move=> /cvg_ex[l ul]; have [_ ->] := cvg_lim_einf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

End lim_esup_inf.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_einf_shift`")]
Notation elim_inf_shift := lim_einf_shift.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_esup_le_cvg`")]
Notation elim_sup_le_cvg := lim_esup_le_cvg.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_einfN`")]
Notation elim_infN := lim_einfN.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_esupN`")]
Notation elim_supN := lim_esupN.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `lim_einf_sup`")]
Notation elim_inf_sup := lim_einf_sup.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgNy_lim_einf_sup`")]
Notation cvg_ninfty_elim_inf_sup := cvgNy_lim_einf_sup.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgNy_einfs`")]
Notation cvg_ninfty_einfs := cvgNy_einfs.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgNy_esups`")]
Notation cvg_ninfty_esups := cvgNy_esups.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgy_einfs`")]
Notation cvg_pinfty_einfs := cvgy_einfs.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgy_esups`")]
Notation cvg_pinfty_esups := cvgy_esups.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvg_lim_einf_sup`")]
Notation cvg_elim_inf_sup := cvg_lim_einf_sup.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `is_cvg_lim_einfE`")]
Notation is_cvg_elim_infE := is_cvg_lim_einfE.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `is_cvg_lim_esupE`")]
Notation is_cvg_elim_supE := is_cvg_lim_esupE.

Section banach_contraction.

Context {R : realType} {X : completeNormedModType R} (U : set X).
Variables (f : {fun U >-> U}).

Section contractions.
Variables (q : {nonneg R}) (ctrf : contraction q f) (base : X) (Ubase : U base).
Let C := `|f base - base| / (1 - q%:num).
Let y := fun n => iter n f base.
Let q1 := ctrf.1.
Let ctrfq := ctrf.2.
Let C_ge0 : 0 <= C.
Proof. by rewrite ?(invr_ge0, mulr_ge0, subr_ge0, ltW q1). Qed.

Lemma contraction_dist n m : `|y n - y (n + m)| <= C * q%:num ^+ n.
Proof.
have f1 k : `|y k.+1 - y k| <= q%:num ^+ k * `|f base - base|.
  elim: k => [|k /(ler_wpmul2l (ge0 q))]; first by rewrite expr0 mul1r.
  rewrite mulrA -exprS; apply: le_trans.
  by rewrite (@ctrfq (y k.+1, y k)); split; exact: funS.
have /le_trans -> // : `| y n - y (n + m)| <=
    series (geometric (`|f base - base| * q%:num ^+ n) q%:num) m.
  elim: m => [|m ih].
    by rewrite geometric_seriesE ?lt_eqF//= addn0 subrr normr0 subrr mulr0 mul0r.
  rewrite (le_trans (ler_dist_add (y (n + m)%N) _ _))//.
  apply: (le_trans (ler_add ih _)); first by rewrite distrC addnS; exact: f1.
  rewrite [_ * `|_|]mulrC exprD mulrA geometric_seriesE ?lt_eqF//=.
  rewrite -!/(`1-_) (onem_PosNum ctrf.1) (onemX_NngNum (ltW ctrf.1)).
  rewrite -!mulrA -mulrDr ler_pmul// -mulrDr exprSr onemM -addrA.
  rewrite -[in leRHS](mulrC _ `1-(_ ^+ m)) -onemMr onemK.
  by rewrite [in leRHS]mulrDl mulrAC mulrV ?mul1r// unitf_gt0// onem_gt0.
rewrite geometric_seriesE ?lt_eqF//= -[leRHS]mulr1 (ACl (1*4*2*3))/= -/C.
by rewrite ler_wpmul2l// 1?mulr_ge0// ler_subl_addr ler_addl.
Qed.

Lemma contraction_cvg : cvg y.
Proof.
apply/cauchy_cvgP; apply/cauchy_ballP => _/posnumP[e]; near_simpl.
have lt_min n m : `|y n - y m| <= C * q%:num ^+ minn n m.
  wlog : n m / (n <= m)%N => W.
    by case/orP: (leq_total n m) => /W //; rewrite distrC minnC.
  by rewrite (minn_idPl _)// (le_trans _ (contraction_dist _ (m - n)))// subnKC.
case: ltrgt0P C_ge0 => // [Cpos|C0] _; last first.
  near=> n m => /=; rewrite -ball_normE.
  by apply: (le_lt_trans (lt_min _ _)); rewrite C0 mul0r.
near=> n; rewrite -ball_normE /= (le_lt_trans (lt_min n.1 n.2)) //.
rewrite // -ltr_pdivl_mull //.
suff : ball 0 (C^-1 * e%:num) (q%:num ^+ minn n.1 n.2).
  by rewrite /ball /= sub0r normrN ger0_norm.
near: n; rewrite nbhs_simpl.
pose g := fun w : nat * nat => q%:num ^+ minn w.1 w.2.
have := @fcvg_ball _ _ (g @ filter_prod \oo \oo) _ 0 _ (C^-1 * e%:num).
move: (@cvg_geometric _ 1 q%:num); rewrite ger0_norm // => /(_ q1) geo.
near_simpl; apply; last by rewrite mulr_gt0 // invr_gt0.
apply/cvg_ballP => _/posnumP[delta]; near_simpl.
have [N _ Q] : \forall N \near \oo, ball 0 delta%:num (geometric 1 q%:num N).
  exact: (@fcvg_ball R R _ _ 0 geo).
exists ([set n | N <= n], [set n | N <= n])%N; first by split; exists N.
move=> [n m] [Nn Nm]; rewrite /ball /= sub0r normrN ger0_norm /g //.
apply: le_lt_trans; last by apply: (Q N) => /=.
rewrite sub0r normrN ger0_norm /geometric //= mul1r.
by rewrite ler_wiexpn2l // ?ltW // leq_min Nn.
Unshelve. all: end_near. Qed.

Lemma contraction_cvg_fixed : closed U -> lim y = f (lim y).
Proof.
move=> clU; apply: cvg_lim => //.
apply/cvgrPdist_lt => _/posnumP[e]; near_simpl; apply: near_inftyS.
have [q_gt0 | | q0] := ltrgt0P q%:num.
- near=> n => /=; apply: (le_lt_trans (@ctrfq (_, _) _)) => //=.
  + split; last exact: funS.
    by apply: closed_cvg contraction_cvg => //; apply: nearW => ?; exact: funS.
  + rewrite -ltr_pdivl_mull //; near: n; move/cvgrPdist_lt: contraction_cvg; apply.
    by rewrite mulr_gt0 // invr_gt0.
- by rewrite ltNge//; exact: contraNP.
- apply: nearW => /= n; apply: (le_lt_trans (@ctrfq (_, _) _)).
  + split; last exact: funS.
    by apply: closed_cvg contraction_cvg => //; apply: nearW => ?; exact: funS.
  + by rewrite q0 mul0r.
Unshelve. all: end_near. Qed.

End contractions.

Variable ctrf : is_contraction f.

Theorem banach_fixed_point : closed U -> U !=set0 -> exists2 p, U p & p = f p.
Proof.
case: ctrf => [q ctrq] ? [base Ubase]; exists (lim (iter n f base @[n -->\oo])).
  apply: closed_cvg (contraction_cvg ctrq Ubase) => //.
  by apply: nearW => ?; exact: funS.
exact: (contraction_cvg_fixed ctrq).
Unshelve. all: end_near. Qed.

End banach_contraction.
