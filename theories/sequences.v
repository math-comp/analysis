(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import set_interval reals itv ereal topology.
From mathcomp Require Import tvs normedtype landau.

(**md**************************************************************************)
(* # Definitions and lemmas about sequences                                   *)
(*                                                                            *)
(* The purpose of this file is to gather generic definitions and lemmas about *)
(* sequences. Incidentally, it defines the exponential function.              *)
(* ```                                                                        *)
(*     nondecreasing_seq u == the sequence u is non-decreasing                *)
(*     nonincreasing_seq u == the sequence u is non-increasing                *)
(*        increasing_seq u == the sequence u is (strictly) increasing         *)
(*        decreasing_seq u == the sequence u is (strictly) decreasing         *)
(* ```                                                                        *)
(*                                                                            *)
(* ## About sequences of real numbers                                         *)
(* ```                                                                        *)
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
(*        \sum_<range> F i == lim (fun n => (\sum_<range>) F i)) where        *)
(*                            <range> can be (i <oo), (i <oo | P i),          *)
(*                            (m <= i <oo), or (m <= i <oo | P i)             *)
(* ```                                                                        *)
(*                                                                            *)
(* Sections sequences_R_* contain properties of sequences of real numbers.    *)
(* For example:                                                               *)
(* ```                                                                        *)
(* nonincreasing_cvgn_ge u_ == if u_ is nonincreasing and convergent then     *)
(*                             forall n, lim u_ <= u_ n                       *)
(* nondecreasing_cvgn_le u_ == if u_ is nondecreasing and convergent then     *)
(*                             forall n, lim u_ >= u_ n                       *)
(*    nondecreasing_cvgn u_ == if u_ is nondecreasing and bounded then u_     *)
(*                             is convergent and its limit is sup u_n         *)
(*    nonincreasing_cvgn u_ == if u_ is nonincreasing u_ and bound by below   *)
(*                             then u_ is convergent                          *)
(*                 adjacent == adjacent sequences lemma                       *)
(*                   cesaro == Cesaro's lemma                                 *)
(* ```                                                                        *)
(*                                                                            *)
(* ## About sequences of natural numbers                                      *)
(* ```                                                                        *)
(*                nseries u := fun n => \sum_(0 <= k < n) u k                 *)
(*                             where u has type nat^nat                       *)
(* ```                                                                        *)
(*                                                                            *)
(* ## About sequences of extended real numbers                                *)
(* ```                                                                        *)
(*                eseries u := [sequence \sum_(0 <= k < n) u k]_n             *)
(*                             where u has type (\bar R)^nat                  *)
(*             etelescope u := [sequence u n.+1 - u n]_n                      *)
(* ```                                                                        *)
(*                                                                            *)
(* Section sequences_ereal contain properties of sequences of extended real   *)
(* numbers.                                                                   *)
(*                                                                            *)
(*   Naming convention: lemmas about series of non-negative (resp.            *)
(*   non-positive) extended numbers use the string "nneseries" (resp.         *)
(*   "npeseries") as part of their identifier                                 *)
(*                                                                            *)
(* ## Limit superior and inferior for sequences                               *)
(* ```                                                                        *)
(*              sdrop u n := {u_k | k >= n}                                   *)
(*                 sups u := [sequence sup (sdrop u n)]_n                     *)
(*                 infs u := [sequence inf (sdrop u n)]_n                     *)
(*     limn_sup, limn_inf == limit sup/inferior for a sequence of reals       *)
(*                esups u := [sequence ereal_sup (sdrop u n)]_n               *)
(*                einfs u := [sequence ereal_inf (sdrop u n)]_n               *)
(* limn_esup u, limn_einf == limit sup/inferior for a sequence of             *)
(*                           of extended reals                                *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Bounded functions                                                       *)
(* This section proves Baire's Theorem, stating that complete normed spaces   *)
(* are Baire spaces, and Banach-Steinhaus' theorem, stating that between a    *)
(* complete normed vector space and a normed vector spaces, pointwise bounded *)
(* and uniformly bounded subset of functions correspond.                      *)
(* ```                                                                        *)
(*     bounded_fun_norm f == a function between normed spaces transforms a    *)
(*                           bounded set into a bounded set                   *)
(*    pointwise_bounded F == F is a set of pointwise bounded functions        *)
(*                           between normed spaces                            *)
(*      uniform_bounded F == F is a set of uniform bounded functions          *)
(*                           between normed spaces                            *)
(* ```                                                                        *)
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
Proof. by rewrite propeqE; split => du x y /du; rewrite lerN2. Qed.

Lemma nonincreasing_opp (T : numDomainType) (u_ : T ^nat) :
  nonincreasing_seq (- u_) = nondecreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite lerN2. Qed.

Lemma decreasing_opp (T : numDomainType) (u_ : T ^nat) :
  decreasing_seq (- u_) = increasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du lerN2. Qed.

Lemma increasing_opp (T : numDomainType) (u_ : T ^nat) :
  increasing_seq (- u_) = decreasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du lerN2. Qed.

Lemma nondecreasing_seqP d (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n <= u_ n.+1)%O <-> nondecreasing_seq u_.
Proof. by split=> [|h n]; [exact: homo_leq le_trans | exact: h]. Qed.

Lemma nonincreasing_seqP d (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n >= u_ n.+1)%O <-> nonincreasing_seq u_.
Proof.
split; first by apply: homo_leq (fun _ _ _ u v => le_trans v u).
by move=> u_nincr n; exact: u_nincr.
Qed.

Lemma increasing_seqP d (T : porderType d) (u_ : T ^nat) :
  (forall n, u_ n < u_ n.+1)%O <-> increasing_seq u_.
Proof.
split; first by move=> u_nondec; apply: le_mono; apply: homo_ltn lt_trans _.
by move=> u_incr n; rewrite lt_neqAle eq_le !u_incr leqnSn ltnn.
Qed.

Lemma decreasing_seqP d (T : porderType d) (u_ : T ^nat) :
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

Lemma nondecreasing_seqD T (R : numDomainType) (f g : (T -> R)^nat) :
  (forall x, nondecreasing_seq (f ^~ x)) ->
  (forall x, nondecreasing_seq (g ^~ x)) ->
  (forall x, nondecreasing_seq ((f \+ g) ^~ x)).
Proof. by move=> ndf ndg t m n mn; apply: lerD; [exact/ndf|exact/ndg]. Qed.

Local Notation eqolimn := (@eqolim _ _ _ eventually_filter).
Local Notation eqolimPn := (@eqolimP _ _ _ eventually_filter).

(** Sequences of sets *)

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
move=> /existsNP[i] /not_implyP[ik] /contrapT Fit; apply: (ih t i) => //.
by rewrite (leq_ltn_trans ik).
Qed.

Lemma seqDUIE (S : set T) (F : (set T)^nat) :
  seqDU (fun n => S `&` F n) = (fun n => S `&` F n `\` \bigcup_(i < n) F i).
Proof.
apply/funext => n; rewrite -setIDA; apply/seteqP; split; last first.
  move=> x [Sx [Fnx UFx]]; split=> //; apply: contra_not UFx => /=.
  by rewrite bigcup_mkord -big_distrr/= => -[].
by rewrite /seqDU -setIDA bigcup_mkord -big_distrr/= setDIr setIUr setDIK set0U.
Qed.

End seqDU.
Arguments trivIset_seqDU {T} F.
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

Lemma nondecreasing_bigsetU_seqD F n : nondecreasing_seq F ->
  \big[setU/set0]_(i < n.+1) seqD F i = F n.
Proof.
move=> ndF; elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
- by rewrite big_ord_recl big_ord0 setU0.
- by move=> ?; rewrite big_ord_recl big_ord0; left.
- by rewrite big_ord_recr /= ih => -[|[]//]; move: x; exact/subsetPset/ndF.
- rewrite (setU_seqD ndF) => -[|/= [Fn1x Fnx]].
    by rewrite big_ord_recr /= -ih => Fnx; left.
  by rewrite big_ord_recr /=; right.
Qed.

Lemma eq_bigcup_seqD F : \bigcup_n seqD F n = \bigcup_n F n.
Proof.
apply/seteqP; split => [x []|x []].
  by elim=> [_ /= F0x|n ih _ /= [Fn1x Fnx]]; [exists O | exists n.+1].
elim=> [_ F0x|n ih _ Fn1x]; first by exists O.
have [|Fnx] := pselect (F n x); last by exists n.+1.
by move=> /(ih I)[m _ Fmx]; exists m.
Qed.

Lemma eq_bigcup_seqD_bigsetU F :
  \bigcup_n (seqD (fun n => \big[setU/set0]_(i < n.+1) F i) n) = \bigcup_n F n.
Proof.
rewrite (eq_bigcup_seqD (fun n => \big[setU/set0]_(i < n.+1) F i)).
rewrite eqEsubset; split => [t [i _]|t [i _ Fit]].
  by rewrite -bigcup_seq_cond => -[/= j _ Fjt]; exists j.
by exists i => //; rewrite big_ord_recr /=; right.
Qed.

Lemma bigcup_bigsetU_bigcup F :
  \bigcup_k \big[setU/set0]_(i < k.+1) F i = \bigcup_k F k.
Proof.
apply/seteqP; split=> [x [i _]|x [i _ Fix]].
  by rewrite -bigcup_mkord => -[j _ Fjx]; exists j.
by exists i => //; rewrite big_ord_recr/=; right.
Qed.

End seqD.
#[deprecated(since="mathcomp-analysis 1.2.0", note="renamed to `nondecreasing_bigsetU_seqD`")]
Notation eq_bigsetU_seqD := nondecreasing_bigsetU_seqD (only parsing).

(** Convergence of patched sequences *)

Section sequences_patched.
(* TODO: generalizations to numDomainType *)

Section NatShift.

Variables (N : nat) (V : ptopologicalType).
Implicit Types (f : nat -> V) (u : V ^nat)  (l : set_system V).

Lemma cvg_restrict f u_ l :
  ([sequence if (n <= N)%N then f n else u_ n]_n @ \oo --> l) =
  (u_ @ \oo --> l).
Proof.
rewrite propeqE; split; apply: cvg_trans; apply: near_eq_cvg;
by near do [move=> /=; case: ifP => //; rewrite ltn_geF//].
Unshelve. all: by end_near. Qed.

Lemma is_cvg_restrict f u_ :
  cvgn [sequence if (n <= N)%nat then f n else u_ n]_n = cvgn u_.
Proof.
by rewrite propeqE; split;
  [rewrite cvg_restrict|rewrite -(cvg_restrict f)] => /cvgP.
Qed.

Lemma cvg_centern u_ l :
  ([sequence u_ (n - N)%N]_n @ \oo --> l) = (u_ @ \oo --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; apply: cvg_subnr.
gen have cD : u_ l / u_ @ \oo --> l -> (fun n => u_ (n + N)%N) @ \oo --> l.
   by apply: cvg_comp; apply: cvg_addnr.
by move=> /cD /=; under [X in X @ _ --> l]funext => n do rewrite addnK.
Qed.

Lemma cvg_shiftn u_ l :
  ([sequence u_ (n + N)%N]_n @ \oo --> l) = (u_ @ \oo --> l).
Proof.
rewrite propeqE; split; last by apply: cvg_comp; apply: cvg_addnr.
rewrite -[X in X -> _]cvg_centern; apply: cvg_trans => /=.
by apply: near_eq_cvg; near do rewrite subnK; exists N.
Unshelve. all: by end_near. Qed.

End NatShift.

Variables (V : ptopologicalType).

Lemma cvg_shiftS u_ (l : set_system V) :
  ([sequence u_ n.+1]_n @ \oo --> l) = (u_ @ \oo --> l).
Proof.
suff -> : [sequence u_ n.+1]_n = [sequence u_(n + 1)%N]_n by rewrite cvg_shiftn.
by rewrite funeqE => n/=; rewrite addn1.
Qed.

End sequences_patched.

Section sequences_R_lemmas_realFieldType.
Variable R : realFieldType.
Implicit Types u v : R ^nat.

Lemma lt_lim u (M : R) : nondecreasing_seq u ->
  cvgn u -> M < limn u -> \forall n \near \oo, M <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, M <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have {}Mu : forall x, M > u x by move=> x; rewrite ltNge; apply/negP.
have : limn u <= M by apply: limr_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near. Qed.

Lemma nonincreasing_cvgn_ge u_ : nonincreasing_seq u_ -> cvgn u_ ->
  forall n, limn u_ <= u_ n.
Proof.
move=> du ul p; rewrite leNgt; apply/negP => up0.
move/cvgrPdist_lt : ul => /(_ `|u_ p - limn u_|%R).
rewrite {1}ltr0_norm ?subr_lt0 // opprB subr_gt0 => /(_ up0) ul.
near \oo => N.
have /du uNp : (p <= N)%nat by near: N; rewrite nearE; exists p.
have : `|limn u_ - u_ N| >= `|u_ p - limn u_|%R.
 rewrite ltr0_norm // ?subr_lt0 // opprB distrC.
 rewrite (@le_trans _ _ (limn u_ - u_ N)) // ?lerB //.
 rewrite (_ : `| _ | = `|u_ N - limn u_|%R) // ler0_norm // ?opprB //.
 by rewrite subr_le0 (le_trans _ (ltW up0)).
rewrite leNgt => /negP; apply; by near: N.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_cvgn_le u_ : nondecreasing_seq u_ -> cvgn u_ ->
  forall n, u_ n <= limn u_.
Proof.
move=> iu cu n; move: (@nonincreasing_cvgn_ge (- u_)).
rewrite -nondecreasing_opp opprK => /(_ iu); rewrite is_cvgNE => /(_ cu n).
by rewrite limN // lerNl opprK.
Qed.

Lemma cvg_has_ub u_ : cvgn u_ -> has_ubound [set `|u_ n| | n in setT].
Proof.
move=> /cvg_seq_bounded/pinfty_ex_gt0[M M_gt0 /= uM].
by exists M; apply/ubP => x -[n _ <-{x}]; exact: uM.
Qed.

Lemma cvg_has_sup u_ : cvgn u_ -> has_sup (u_ @` setT).
Proof.
move/cvg_has_ub; rewrite -/(_ @` _) -(image_comp u_ normr setT).
by move=> /has_ub_image_norm uM; split => //; exists (u_ 0%N), 0%N.
Qed.

Lemma cvg_has_inf u_ : cvgn u_ -> has_inf (u_ @` setT).
Proof. by move/is_cvgN/cvg_has_sup; rewrite -has_inf_supN image_comp. Qed.

End sequences_R_lemmas_realFieldType.
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nonincreasing_cvgn_ge`")]
Notation nonincreasing_cvg_ge := nonincreasing_cvgn_ge (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nondecreasing_cvgn_le`")]
Notation nondecreasing_cvg_le := nondecreasing_cvgn_le (only parsing).

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
Proof. by move=> /subnK<-; rewrite series_addn addrC addKr. Qed.

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

Lemma is_cvg_seriesN f : cvgn (series (- f)) = cvgn (series f).
Proof. by rewrite seriesN is_cvgNE. Qed.

Lemma lim_seriesN f : cvg (series f @ \oo) ->
  limn (series (- f)) = - limn (series f).
Proof. by move=> cf; rewrite seriesN limN. Qed.

Lemma is_cvg_seriesZ f k : cvgn (series f) -> cvgn (series (k *: f)).
Proof. by move=> cf; rewrite seriesZ; exact: is_cvgZr. Qed.

Lemma lim_seriesZ f k : cvgn (series f) ->
  limn (series (k *: f)) = k *: limn (series f).
Proof. by move=> cf; rewrite seriesZ limZr. Qed.

Lemma is_cvg_seriesD f g :
  cvgn (series f) -> cvgn (series g) -> cvgn (series (f + g)).
Proof. by move=> cf cg; rewrite seriesD; exact: is_cvgD. Qed.

Lemma lim_seriesD f g : cvgn (series f) -> cvgn (series g) ->
  limn (series (f + g)) = limn (series f) + limn (series g).
Proof. by move=> cf cg; rewrite seriesD limD. Qed.

Lemma is_cvg_seriesB f g :
  cvgn (series f) -> cvgn (series g) -> cvgn (series (f - g)).
Proof. by move=> cf cg; apply: is_cvg_seriesD; rewrite ?is_cvg_seriesN. Qed.

Lemma lim_seriesB f g : cvg (series f @ \oo) -> cvg (series g @ \oo) ->
  limn (series (f - g)) = limn (series f) - limn (series g).
Proof. by move=> Cf Cg; rewrite lim_seriesD ?is_cvg_seriesN// lim_seriesN. Qed.

End partial_sum_numFieldType.

Lemma lim_series_le (V : realFieldType) (f g : V ^nat) :
  cvgn (series f) -> cvgn (series g) -> (forall n, f n <= g n) ->
  limn (series f) <= limn (series g).
Proof.
by move=> cf cg fg; apply: (ler_lim cf cg); near=> x; rewrite ler_sum.
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
Implicit Types (f : nat -> V) (u : V ^nat)  (l : set_system V).

Lemma is_cvg_series_restrict u_ :
  cvgn [sequence \sum_(N <= k < n) u_ k]_n = cvgn (series u_).
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

Lemma nondecreasing_cvgn (u_ : R ^nat) :
    nondecreasing_seq u_ -> has_ubound (range u_) ->
  u_ @ \oo --> sup (range u_).
Proof.
move=> leu u_ub; set M := sup (range u_).
have su_ : has_sup (range u_) by split => //; exists (u_ 0%N), 0%N.
apply/cvgrPdist_le => _/posnumP[e].
have [p Mu_p] : exists p, M - e%:num <= u_ p.
  have [_ -[p _] <- /ltW Mu_p] := sup_adherent (gt0 e) su_.
  by exists p; rewrite Mu_p.
near=> n; have pn : (p <= n)%N by near: n; exact: nbhs_infty_ge.
rewrite ler_distlC (le_trans Mu_p (leu _ _ _))//= (@le_trans _ _ M) ?lerDl//.
by have /ubP := sup_upper_bound su_; apply; exists n.
Unshelve. all: by end_near. Qed.

Lemma nondecreasing_is_cvgn (u_ : R ^nat) :
  nondecreasing_seq u_ -> has_ubound (range u_) -> cvgn u_.
Proof. by move=> u_nd u_ub; apply: cvgP; exact: nondecreasing_cvgn. Qed.

Lemma nondecreasing_dvgn_lt (u_ : R ^nat) :
  nondecreasing_seq u_ -> ~ cvgn u_ -> u_ @ \oo --> +oo.
Proof.
move=> nu du; apply: contrapT => /cvgryPge/existsNP[l lu]; apply: du.
apply: nondecreasing_is_cvgn => //; exists l => _ [n _ <-].
rewrite leNgt; apply/negP => lun; apply: lu; near=> m.
by rewrite (le_trans (ltW lun)) //; apply: nu; near: m; exists n.
Unshelve. all: by end_near. Qed.

Lemma near_nondecreasing_is_cvgn (u_ : R ^nat) (M : R) :
    {near \oo, nondecreasing_seq u_} -> (\forall n \near \oo, u_ n <= M) ->
  cvgn u_.
Proof.
move=> [k _ u_nd] [k' _ u_M].
suff : cvgn [sequence u_ (n + maxn k k')%N]_n.
  by case/cvg_ex => /= l; rewrite cvg_shiftn => ul; apply/cvg_ex; exists l.
apply: nondecreasing_is_cvgn; [move=> /= m n mn|exists M => _ [n _ <-]].
  by rewrite u_nd ?leq_add2r//= (leq_trans (leq_maxl _ _) (leq_addl _ _)).
by rewrite u_M //= (leq_trans (leq_maxr _ _) (leq_addl _ _)).
Qed.

Lemma nonincreasing_cvgn (u_ : R ^nat) :
    nonincreasing_seq u_ -> has_lbound (range u_) ->
  u_ @ \oo --> inf (u_ @` setT).
Proof.
rewrite -nondecreasing_opp => u_nd u_lb; rewrite -[X in X @ _ --> _](opprK u_).
apply: cvgN; rewrite image_comp; apply: nondecreasing_cvgn => //.
by move/has_lb_ubN : u_lb; rewrite image_comp.
Qed.

Lemma nonincreasing_is_cvgn (u_ : R ^nat) :
  nonincreasing_seq u_ -> has_lbound (range u_) -> cvgn u_.
Proof. by move=> u_decr u_bnd; apply: cvgP; exact: nonincreasing_cvgn. Qed.

Lemma near_nonincreasing_is_cvgn (u_ : R ^nat) (m : R) :
    {near \oo, nonincreasing_seq u_} -> (\forall n \near \oo, m <= u_ n) ->
  cvgn u_.
Proof.
move=> u_ni u_m.
rewrite -(opprK u_); apply: is_cvgN; apply/(@near_nondecreasing_is_cvgn _ (- m)).
- by apply: filterS u_ni => x u_x y xy; rewrite lerNl opprK u_x.
- by apply: filterS u_m => x u_x; rewrite lerNl opprK.
Qed.

Lemma adjacent (u_ v_ : R ^nat) : nondecreasing_seq u_ -> nonincreasing_seq v_ ->
  v_ - u_ @ \oo --> 0 ->
  [/\ limn v_ = limn u_, cvgn u_ & cvgn v_].
Proof.
set w_ := v_ - u_ => iu dv w0; have vu n : v_ n >= u_ n.
  suff : limn w_ <= w_ n by rewrite (cvg_lim _ w0)// subr_ge0.
  apply: (nonincreasing_cvgn_ge _ (cvgP _ w0)) => m p mp.
  by rewrite lerB; rewrite ?iu ?dv.
have cu : cvgn u_.
  apply: nondecreasing_is_cvgn => //; exists (v_ 0%N) => _ [n _ <-].
  by rewrite (le_trans (vu _)) // dv.
have cv : cvgn v_.
  apply: nonincreasing_is_cvgn => //; exists (u_ 0%N) => _ [n _ <-].
  by rewrite (le_trans _ (vu _)) // iu.
by split=> //; apply/eqP; rewrite -subr_eq0 -limB //; exact/eqP/cvg_lim.
Qed.

End sequences_R_lemmas.
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nonincreasing_cvgn`")]
Notation nonincreasing_cvg := nonincreasing_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nondecreasing_cvgn`")]
Notation nondecreasing_cvg := nondecreasing_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nonincreasing_is_cvgn`")]
Notation nonincreasing_is_cvg := nonincreasing_is_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nondecreasing_is_cvgn`")]
Notation nondecreasing_is_cvg := nondecreasing_is_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `nondecreasing_dvgn_lt`")]
Notation nondecreasing_dvg_lt := nondecreasing_dvgn_lt (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `near_nondecreasing_is_cvgn`")]
Notation near_nondecreasing_is_cvg := near_nondecreasing_is_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `near_nonincreasing_is_cvgn`")]
Notation near_nonincreasing_is_cvg := near_nonincreasing_is_cvgn (only parsing).

Definition harmonic {R : fieldType} : R ^nat := [sequence n.+1%:R^-1]_n.
Arguments harmonic {R} n /.

Lemma harmonic_gt0 {R : numFieldType} i : 0 < harmonic i :> R.
Proof. by rewrite /=. Qed.

Lemma harmonic_ge0 {R : numFieldType} i : 0 <= harmonic i :> R.
Proof. exact/ltW/harmonic_gt0. Qed.

Lemma cvg_harmonic {R : archiFieldType} : @harmonic R @ \oo --> 0.
Proof.
apply/cvgrPdist_le => _/posnumP[e]; near=> i.
rewrite distrC subr0 ger0_norm//= -lef_pV2 ?qualifE//= invrK.
rewrite (le_trans (ltW (archi_boundP _)))// ler_nat -add1n -leq_subLR.
by near: i; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

Lemma cvge_harmonic {R : archiFieldType} : (EFin \o @harmonic R) @ \oo --> 0%E.
Proof. by apply: cvg_EFin; [exact: nearW | exact: cvg_harmonic]. Qed.

Lemma dvg_harmonic (R : numFieldType) : ~ cvgn (series (@harmonic R)).
Proof.
have ge_half n : (0 < n)%N -> 2^-1 <= \sum_(n <= i < n.*2) harmonic i.
  case: n => // n _.
  rewrite (@le_trans _ _ (\sum_(n.+1 <= i < n.+1.*2) n.+1.*2%:R^-1)) //=.
    rewrite sumr_const_nat -addnn addnK addnn -mul2n natrM invfM.
    by rewrite -[_ *+ n.+1]mulr_natr divfK.
  by apply: ler_sum_nat => i /andP[? ?]; rewrite lef_pV2 ?qualifE/= ?ler_nat.
move/cvg_cauchy/cauchy_ballP => /(_ _ [gt0 of 2^-1 : R]); rewrite !near_map2.
rewrite -ball_normE => /nearP_dep hcvg; near \oo => n; near \oo => m.
have: `|series harmonic n - series harmonic m| < 2^-1 :> R by near: m; near: n.
rewrite le_gtF// distrC -[X in X - _](addrNK (series harmonic n.*2)).
rewrite sub_series_geq; last by near: m; apply: nbhs_infty_ge.
rewrite -addrA sub_series_geq -addnn ?leq_addr// addnn.
have sh_ge0 i j : 0 <= \sum_(i <= k < j) harmonic k :> R.
  by rewrite ?sumr_ge0//; move=> k _; apply: harmonic_ge0.
by rewrite ger0_norm// ler_wpDl// ge_half//; near: n.
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

Theorem cesaro (u_ : R ^nat) (l : R) : u_ @ \oo --> l ->
  arithmetic_mean u_ @ \oo --> l.
Proof.
move=> u0_cvg; have ssplit v_ m n : (m <= n)%N -> `|n%:R^-1 * series v_ n| <=
    n%:R^-1 * `|series v_ m| + n%:R^-1 * `|\sum_(m <= i < n) v_ i|.
  move=> /subnK<-; rewrite series_addn mulrDr (le_trans (ler_normD _ _))//.
  by rewrite !normrM ger0_norm.
apply/cvgrPdist_lt=> _/posnumP[e]; near \oo => m; near=> n.
have {}/ssplit -/(_ _ [sequence l - u_ n]_n) : (m.+1 <= n.+1)%nat.
  by near: n; exists m.
rewrite !seriesEnat /= big_split/=.
rewrite sumrN mulrBr sumr_const_nat -(mulr_natl l) mulKf//.
move=> /le_lt_trans->//; rewrite [e%:num]splitr ltrD//.
  have [->|neq0] := eqVneq (\sum_(0 <= k < m.+1) (l - u_ k)) 0.
    by rewrite normr0 mulr0.
  rewrite -ltr_pdivlMr ?normr_gt0//.
  rewrite -ltf_pV2 ?qualifE//= ?mulr_gt0 ?invr_gt0 ?normr_gt0// invrK.
  rewrite (lt_le_trans (archi_boundP _))// ler_nat leqW//.
  by near: n; apply: nbhs_infty_ge.
rewrite ltr_pdivrMl ?ltr0n // (le_lt_trans (ler_norm_sum _ _ _)) //.
rewrite (le_lt_trans (@ler_sum_nat _ _ _ _ (fun i => e%:num / 2) _))//; last first.
  by rewrite sumr_const_nat mulr_natl ltr_pMn2l// ltn_subrL.
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
    [sequence n.+1%:R^-1 * series u_ n.+1]_n @ \oo --> 0 ->
  [sequence n.+1%:R^-1 * series u_ n]_n @ \oo --> 0.
Proof.
move=> H; apply/cvgrPdist_lt => _/posnumP[e].
move/cvgrPdist_lt : H => /(_ _ (gt0 e)) -[m _ mu].
near=> n; rewrite sub0r normrN /=.
have /andP[n0] : ((0 < n) && (m <= n.-1))%N.
  near: n; exists m.+1 => // k mk; rewrite (leq_trans _ mk) //=.
  by rewrite -(leq_add2r 1%N) !addn1 prednK // (leq_trans _ mk).
move/mu => {mu}; rewrite sub0r normrN /= prednK //; apply: le_lt_trans.
rewrite !normrM ler_wpM2r // ger0_norm // ger0_norm //.
by rewrite lef_pV2 // ?ler_nat // posrE // ltr0n.
Unshelve. all: by end_near. Qed.

Lemma cesaro_converse (u_ : R ^nat) (l : R) :
    telescope u_ =o_\oo @harmonic R ->
  arithmetic_mean u_ @ \oo --> l -> u_ @ \oo --> l.
Proof.
pose a_ := telescope u_ => a_o u_l.
suff abel : forall n,
    u_ n - arithmetic_mean u_ n = \sum_(1 <= k < n.+1) k%:R / n.+1%:R * a_ k.-1.
  suff K : u_ - arithmetic_mean u_ @ \oo --> 0.
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
  have {}a_o : [sequence n.+1%:R * telescope u_ n]_n @ \oo --> 0.
    apply: (@eqolim0 _ _ _ eventually_filterType).
    rewrite a_o.
    set h := 'o_\oo (@harmonic R).
    apply/eqoP => _/posnumP[e] /=.
    near=> n; rewrite normr1 mulr1 normrM -ler_pdivlMl ?normr_gt0//.
    rewrite mulrC -normrV ?unitfE //.
    near: n.
    by case: (eqoP eventually_filterType (@harmonic R) h) => Hh _; apply Hh.
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
  rewrite !big_mkord; apply: eq_bigr => i _.
  by rewrite seriesEord/= big_mkord -big_ord_widen.
rewrite (exchange_big_dep_nat xpredT) //=.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) \sum_(i <= j < n.+1) a_ i ); last first.
  apply: congr_big_nat => //= i ni.
  rewrite big_const_nat iter_addr addr0 -big_filter.
  rewrite big_const_seq iter_addr addr0; congr (_ *+ _).
  rewrite /index_iota subn0 -[in LHS](subnKC (ltnW ni)) iotaD filter_cat.
  rewrite count_cat (_ : [seq _ <- _ | _] = [::]); last first.
    rewrite -(filter_pred0 (iota 0 i)); apply: eq_in_filter => j.
    by rewrite mem_iota leq0n andTb add0n => ji; rewrite ltnNge ji.
  rewrite 2!add0n (_ : [seq _ <- _ | _] = iota i (n.+1 - i)); last first.
    rewrite -[RHS]filter_predT; apply: eq_in_filter => j.
    rewrite mem_iota => /andP[ij]; rewrite subnKC; last exact/ltnW.
    by move=> jn; rewrite ltnS ij.
  by rewrite count_predT size_iota.
rewrite [X in _ - _ * X](_ : _ =
    \sum_(0 <= i < n.+1) a_ i * (n.+1 - i)%:R); last first.
  by apply: eq_bigr => i _; rewrite big_const_nat iter_addr addr0 mulr_natr.
rewrite big_distrr /= big_mkord (big_morph _ (@opprD _) (@oppr0 _)).
rewrite seriesEord -big_split /= big_add1 /= big_mkord; apply: eq_bigr => i _.
rewrite mulrCA -[X in X - _]mulr1 -mulrBr [RHS]mulrC; congr (_ * _).
rewrite -[X in X - _](@divrr _ (n.+2)%:R) ?unitfE ?pnatr_eq0 //.
rewrite [in X in _ - X]mulrC -mulrBl; congr (_ / _).
rewrite -natrB; last by rewrite (@leq_trans n.+1) // leq_subr.
rewrite subnBA; by [rewrite addSnnS addnC addnK | rewrite ltnW].
Unshelve. all: by end_near. Qed.

End cesaro_converse.

Section series_convergence.

Lemma cvg_series_cvg_0 (K : numFieldType) (V : normedModType K) (u_ : V ^nat) :
  cvgn (series u_) -> u_ @ \oo --> 0.
Proof.
move=> cvg_series.
rewrite (_ : u_ = fun n => series u_ n.+1 - series u_ n); last first.
  by rewrite funeqE => i; rewrite seriesSB.
rewrite -(subrr (limn (series u_))).
by apply: cvgB => //; rewrite ?cvg_shiftS.
Qed.

Lemma nondecreasing_series (R : numFieldType) (u_ : R ^nat) (P : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= u_ n)%R ->
  nondecreasing_seq (fun n=> \sum_(m <= k < n | P k) u_ k)%R.
Proof.
move=> u_ge0; apply/nondecreasing_seqP => n.
have [mn|nm] := leqP m n.
  rewrite [leRHS]big_mkcond/= [leRHS]big_nat_recr//=.
  by rewrite -[in leRHS]big_mkcond/= lerDl; case: ifPn => //; exact: u_ge0.
by rewrite (big_geq (ltnW _)) // big_geq.
Qed.

Lemma increasing_series (R : numFieldType) (u_ : R ^nat) :
  (forall n, 0 < u_ n) -> increasing_seq (series u_).
Proof.
move=> u_ge0; apply/increasing_seqP => n.
by rewrite !seriesEord/= big_ord_recr ltrDl.
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
  z > 0 -> arithmetic a z @ \oo --> +oo.
Proof.
move=> z_gt0; apply/cvgryPge => A; near=> n => /=.
rewrite -lerBlDl -mulr_natl -ler_pdivrMr//.
rewrite ler_normlW// ltW// (lt_le_trans (archi_boundP _))// ler_nat.
by near: n; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

Lemma cvg_expr (R : archiFieldType) (z : R) :
  `|z| < 1 -> (GRing.exp z : R ^nat) @ \oo --> 0.
Proof.
move=> Nz_lt1; apply/norm_cvg0P; pose t := (1 - `|z|).
apply: (@squeeze_cvgr _ _ _ _ (cst 0) (t^-1 *: @harmonic R)); last 2 first.
- exact: cvg_cst.
- by rewrite -(scaler0 _ t^-1); exact: (cvgZr cvg_harmonic).
near=> n; rewrite normr_ge0 normrX/= ler_pdivlMl ?subr_gt0//.
rewrite -(@ler_pM2l _ n.+1%:R)// mulfV// [t * _]mulrC mulr_natl.
have -> : 1 = (`|z| + t) ^+ n.+1 by rewrite addrC addrNK expr1n.
rewrite exprDn (bigD1 (inord 1)) ?inordK// subn1 expr1 bin1 lerDl sumr_ge0//.
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
  series (geometric a z) @ \oo --> (a * (1 - z)^-1).
Proof.
move=> Nz_lt1; rewrite geometric_seriesE ?lt_eqF 1?ltr_normlW//.
have -> : a / (1 - z) = (a * (1 - 0)) / (1 - z) by rewrite subr0 mulr1.
by apply: cvgMl; apply: cvgMr; apply: cvgB; [apply: cvg_cst|apply: cvg_expr].
Qed.

Lemma cvg_geometric_series_half (R : archiFieldType) (r : R) n :
  series (fun k => r / (2 ^ (k + n.+1))%:R : R^o) @ \oo --> (r / 2 ^+ n : R^o).
Proof.
rewrite (_ : series _ = series (geometric (r / (2 ^ n.+1)%:R) 2^-1%R)); last first.
  rewrite funeqE => m; rewrite /series /=; apply: eq_bigr => k _.
  by rewrite expnD natrM (mulrC (2 ^ k)%:R) invfM exprVn (natrX _ 2 k) mulrA.
apply: cvg_trans.
  apply: cvg_geometric_series.
  by rewrite ger0_norm // invr_lt1 // ?ltr1n // unitfE.
rewrite [X in (X - _)%R](splitr 1) div1r addrK.
by rewrite -mulrA -invfM expnSr natrM -mulrA divff// mulr1 natrX.
Qed.
Arguments cvg_geometric_series_half {R} _ _.

Lemma geometric_partial_tail {R : fieldType} (n m : nat) (x : R) :
  \sum_(m <= i < m + n) x ^+ i = series (geometric (x ^+ m) x) n.
Proof.
by rewrite (big_addn 0 _ m) addnC addnK; under eq_bigr do rewrite exprD mulrC.
Qed.

Lemma cvg_geometric (R : archiFieldType) (a z : R) : `|z| < 1 ->
  geometric a z @ \oo --> 0.
Proof. by move=> /cvg_geometric_series/cvgP/cvg_series_cvg_0. Qed.

Lemma is_cvg_geometric_series (R : archiFieldType) (a z : R) : `|z| < 1 ->
  cvgn (series (geometric a z)).
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
have {}su_cv := [elaborate su_cv _ (gt0 e)];
rewrite -near2_pair -ball_normE !near_simpl/= in su_cv *.
  apply: filterS su_cv => -[/= m n]; rewrite distrC sub_series.
  by have [|/ltnW]:= leqP m n => mn//; rewrite (big_geq mn) ?normr0.
have := su_cv; rewrite near_swap => su_cvC; near=> m => /=; rewrite sub_series.
by have [|/ltnW]:= leqP m.2 m.1 => m12; rewrite ?normrN; near: m.
Unshelve. all: by end_near. Qed.

Lemma series_le_cvg (R : realType) (u_ v_ : R ^nat) :
  (forall n, 0 <= u_ n) -> (forall n, 0 <= v_ n) ->
  (forall n, u_ n <= v_ n) ->
  cvgn (series v_) -> cvgn (series u_).
Proof.
move=> u_ge0 v_ge0 le_uv /cvg_seq_bounded/bounded_fun_has_ubound[M v_M].
apply: nondecreasing_is_cvgn; first exact: nondecreasing_series.
exists M => _ [n _ <-].
by apply: le_trans (v_M (series v_ n) _); [apply: ler_sum | exists n].
Qed.

Lemma normed_cvg {R : realType} (V : completeNormedModType R) (u_ : V ^nat) :
  cvgn [normed series u_] -> cvgn (series u_).
Proof.
move=> /cauchy_cvgP/cauchy_seriesP u_ncvg.
apply/cauchy_cvgP/cauchy_seriesP => e /u_ncvg.
apply: filterS => n /=; rewrite ger0_norm ?sumr_ge0//.
by apply: le_lt_trans; apply: ler_norm_sum.
Qed.

Lemma lim_series_norm {R : realType} (V : completeNormedModType R) (f : V ^nat) :
    cvgn [normed series f] ->
  `|limn (series f)| <= limn [normed series f].
Proof.
move=> cnf; have cf := normed_cvg cnf.
rewrite -lim_norm // (ler_lim (is_cvg_norm cf) cnf) //.
by near=> x; rewrite ler_norm_sum.
Unshelve. all: by end_near. Qed.

Section series_linear.

Lemma cvg_series_bounded (R : realFieldType) (f : R ^nat) :
  cvgn (series f) -> bounded_fun f.
Proof.
by move/cvg_series_cvg_0 => f0; apply/cvg_seq_bounded/cvg_ex; exists 0.
Qed.

Lemma cvg_to_0_linear (R : realFieldType) (f : R -> R) K (k : R) :
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
- apply/(@eqolim0 _ _ R 0^')/eqoP => _/posnumP[e]; near=> x.
  rewrite (le_trans (kfK _ _)) //=.
  + near: x; exists (k / 2); first by rewrite /mkset divr_gt0.
    move=> t /=; rewrite distrC subr0 => tk2 t0.
    by rewrite normr_gt0 t0 (lt_trans tk2) // -[in ltLHS](add0r k) midf_lt.
  + rewrite normr1 mulr1 mulrC -ler_pdivlMr //.
    near: x; exists (e%:num / K); first by rewrite /mkset divr_gt0.
    by move=> t /=; rewrite distrC subr0 => /ltW.
Unshelve. all: by end_near. Qed.

Lemma lim_cvg_to_0_linear (R : realType) (f : nat -> R) (g : R -> nat -> R) k :
  0 < k -> cvgn (series f) ->
  (forall r, 0 < `|r| < k -> forall n, `|g r n| <= f n * `| r |) ->
  limn (series (g x)) @[x --> 0^'] --> 0.
Proof.
move=> k_gt0 Cf Hg.
apply: (@cvg_to_0_linear _ _ (limn (series f)) k) => // h hLk; rewrite mulrC.
have Ckf : cvgn (series (`|h| *: f)) := @is_cvg_seriesZ _ _ `|h| Cf.
have Cng : cvgn [normed series (g h)].
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

Let is_cvg_S0 N : x < N%:R -> cvgn (S0 N).
Proof.
move=> xN; apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series; rewrite normrM normfV.
by rewrite ltr_pdivrMr ?mul1r !ger0_norm // 1?ltW // (lt_trans x0).
Qed.

Let S0_ge0 N n : 0 <= S0 N n.
Proof.
rewrite mulr_ge0 // ?ler0n //; apply: sumr_ge0 => i _.
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
by rewrite big_nat_recr//= lerDl exp_coeff_ge0 // ltW.
Qed.

Let S1_sup N : x < N%:R -> ubound (range (S1 N)) (sup (range (S0 N))).
Proof.
move=> xN _ [n _ <-]; rewrite (le_trans _ (S0_sup n xN)) // /S0 big_distrr /=.
have N_gt0 := lt_trans x0 xN; apply: ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pM2l ?exprn_gt0// (@le_trans _ _ 1) //.
    by rewrite invf_le1// ?ler1n ?ltr0n // fact_gt0.
  rewrite natrX -expfB_cond ?(negPf (lt0r_neq0 N_gt0))//.
  by rewrite exprn_ege1 // ler1n; case: (N) xN x0; case: ltrgt0P.
rewrite /exp expr_div_n /= (fact_split Ni) mulrCA ler_pM2l ?exprn_gt0// natrX.
rewrite -invf_div -expfB // lef_pV2 ?qualifE/= ?exprn_gt0//; last first.
  rewrite ltr0n muln_gt0 fact_gt0/= big_seq big_mkcond/= prodn_gt0// => j.
  by case: ifPn=>//; rewrite mem_index_iota => /andP[+ _]; exact: leq_ltn_trans.
rewrite big_nat_rev/= -natrX ler_nat -prod_nat_const_nat big_add1 /= big_ltn //.
rewrite leq_mul//; first by rewrite (leq_trans (fact_geq _))// leq_pmull.
under [in X in (_ <= X)%N]eq_bigr do rewrite 2!addSn 2!subSS.
rewrite !big_seq/=; elim/big_ind2 : _ => //; first by move=> *; exact: leq_mul.
move=> j; rewrite mem_index_iota => /andP[_ ji].
by rewrite -addnBA// ?leq_addr// ltnW// ltnW.
Qed.

Lemma is_cvg_series_exp_coeff_pos : cvgn (series (exp x)).
Proof.
rewrite /series; near \oo => N; have xN : x < N%:R; last first.
  rewrite -(@is_cvg_series_restrict N.+1).
  by apply: (nondecreasing_is_cvgn (incr_S1 N)); eexists; apply: S1_sup.
near: N; exists `|floor x|.+1 => // m; rewrite /mkset -(@ler_nat R).
move/lt_le_trans => -> //; rewrite (lt_le_trans (mathcomp_extra.lt_succ_floor x))//.
by rewrite -intrD1 -natr1 lerD2r -(@gez0_abs (floor x)) ?floor_ge0// ltW.
Unshelve. all: by end_near. Qed.

End exponential_series_cvg.

Lemma normed_series_exp_coeff x : [normed series (exp x)] = series (exp `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma is_cvg_series_exp_coeff x : cvgn (series (exp x)).
Proof.
have [->|x0] := eqVneq x 0.
  apply/cvg_ex; exists 1; apply/cvgrPdist_lt => // => _/posnumP[e].
  near=> n; have [m ->] : exists m, n = m.+1.
    by exists n.-1; rewrite prednK //; near: n; exists 1%N.
  by rewrite series_exp_coeff0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp_coeff.
by apply: is_cvg_series_exp_coeff_pos; rewrite normr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvg_exp_coeff x : exp x @ \oo --> 0.
Proof. exact: (cvg_series_cvg_0 (@is_cvg_series_exp_coeff x)). Qed.

End exponential_series.

(* TODO: generalize *)
Definition expR {R : realType} (x : R) : R := limn (series (exp_coeff x)).

(** Sequences of natural numbers *)

Lemma nat_nondecreasing_is_cvg (u_ : nat^nat) :
  nondecreasing_seq u_ -> has_ubound (range u_) -> cvgn u_.
Proof.
move=> u_nd [l ul].
suff [N Nu] : exists N, forall n, (n >= N)%N -> u_ n = u_ N.
  apply/cvg_ex; exists (u_ N); rewrite -(cvg_shiftn N).
  rewrite [X in X @ \oo --> _](_ : _ = cst (u_ N))//; first exact: cvg_cst.
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

Lemma cvg_nseries_near (u : nat^nat) : cvgn (nseries u) ->
  \forall n \near \oo, u n = 0%N.
Proof.
move=> /cvg_ex[l ul]; have /ul[a _ aul] : nbhs l [set l].
  by rewrite nbhs_principalE.
have /ul[b _ bul] : nbhs l [set l.-1; l].
  by rewrite nbhs_principalE ; apply/principal_filterP => /=; right.
exists (maxn a b) => // n /= abn.
rewrite (_ : u = fun n => nseries u n.+1 - nseries u n)%N; last first.
  by rewrite funeqE => i; rewrite /nseries big_nat_recr//= addnC addnK.
have /aul -> : (a <= n)%N by rewrite (leq_trans _ abn) // leq_max leqnn.
have /bul[->|->] : (b <= n.+1)%N by rewrite leqW// (leq_trans _ abn)// leq_maxr.
- by apply/eqP; rewrite subn_eq0// leq_pred.
- by rewrite subnn.
Qed.

Lemma dvg_nseries (u : nat^nat) : ~ cvgn (nseries u) ->
  nseries u @ \oo --> \oo.
Proof.
move=> du; apply: contrapT => /cvgnyPgt/existsNP[l lu]; apply: du.
apply: nat_nondecreasing_is_cvg => //; first exact: le_nseries.
exists l => _ [n _ <-]; rewrite leNgt; apply/negP => lun; apply: lu.
by near do rewrite (leq_trans lun) ?le_nseries//; apply: nbhs_infty_ge.
Unshelve. all: by end_near. Qed.

(** Sequences of extended real numbers *)

Notation "\big [ op / idx ]_ ( m <= i <oo | P ) F" :=
  (limn (fun n => (\big[ op / idx ]_(m <= i < n | P) F))) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i <oo ) F" :=
  (limn (fun n => (\big[ op / idx ]_(m <= i < n) F))) : big_scope.
Notation "\big [ op / idx ]_ ( i <oo | P ) F" :=
  (limn (fun n => (\big[ op / idx ]_(i < n | P) F))) : big_scope.
Notation "\big [ op / idx ]_ ( i <oo ) F" :=
  (limn (fun n => (\big[ op / idx ]_(i < n) F))) : big_scope.

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
by rewrite fin_num_oppeD ?fin_numN// oppeK addeC.
Qed.

Lemma sub_double_eseries n : eseries n \is a fin_num ->
  eseries n.*2 - eseries n = \sum_(n <= k < n.*2) u_ k.
Proof. by move=> enfin; rewrite sub_eseries_geq// -addnn leq_addl. Qed.

End partial_esum.

Arguments eseries {R} u_ n : simpl never.
Arguments etelescope {R} u_ n : simpl never.
Notation "[ 'series' E ]_ n" := (eseries [sequence E%E]_n) : ereal_scope.

Lemma cvg_geometric_eseries_half {R : archiFieldType} (r : R) (n : nat) :
  eseries (fun k => (r / (2 ^ (k + n.+1))%:R)%:E) @ \oo --> (r / 2 ^+ n)%:E.
Proof.
apply: cvg_EFin => //.
  by apply: nearW => //= x; rewrite /eseries/= sumEFin.
rewrite [X in X @ _ --> _](_ : _ = series (fun k => r / (2 ^ (k + n.+1))%:R)); last first.
  by apply/funext => x; rewrite /= /eseries/= sumEFin.
exact: cvg_geometric_series_half.
Qed.

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

Lemma ereal_nondecreasing_oppn u_ :
  nondecreasing_seq (-%E \o u_) = nonincreasing_seq u_.
Proof.
rewrite propeqE; split => ni_u m n mn; last by rewrite leeNr oppeK ni_u.
by rewrite -(oppeK (u_ m)) -leeNr ni_u.
Qed.

End sequences_ereal_realDomainType.
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `ereal_nondecreasing_oppn`")]
Notation ereal_nondecreasing_opp := ereal_nondecreasing_oppn (only parsing).

Section sequences_ereal.
Local Open Scope ereal_scope.

Lemma ereal_nondecreasing_cvgn (R : realType) (u_ : (\bar R)^nat) :
  nondecreasing_seq u_ -> u_ @ \oo --> ereal_sup (range u_).
Proof.
move=> nd_u_; set S := u_ @` setT; set l := ereal_sup S.
have [Spoo|Spoo] := pselect (S +oo).
  have [N Nu] : exists N, forall n, (n >= N)%nat -> u_ n = +oo.
    case: Spoo => N _ uNoo; exists N => n Nn.
    by move: (nd_u_ _ _ Nn); rewrite uNoo leye_eq => /eqP.
  have -> : l = +oo by rewrite /l /ereal_sup; exact: supremum_pinfty.
  rewrite -(cvg_shiftn N); set f := (X in X @ \oo --> _).
  rewrite (_ : f = cst +oo); first exact: cvg_cst.
  by rewrite funeqE => n; rewrite /f /= Nu // leq_addl.
have [/funext Snoo|Snoo] := pselect (forall n, u_ n = -oo).
  rewrite /l (_ : S = [set -oo]).
    by rewrite ereal_sup1 Snoo; exact: cvg_cst.
  apply/seteqP; split => [_ [n _] <- /[!Snoo]//|_ ->].
  by rewrite /S Snoo; exists 0%N.
have [/ereal_sup_ninfty loo|lnoo] := eqVneq l -oo.
  by exfalso; apply: Snoo => n; rewrite (loo (u_ n))//; exists n.
have {Snoo}[N Snoo] : exists N, forall n, (n >= N)%N -> u_ n != -oo.
  move/existsNP : Snoo => [m /eqP].
  rewrite neq_lt => /orP[|umoo]; first by rewrite ltNge leNye.
  by exists m => k mk; rewrite gt_eqF// (lt_le_trans umoo)// nd_u_.
have u_fin_num n : (n >= N)%N -> u_ n \is a fin_num.
  move=> Nn; rewrite fin_numE Snoo//=; apply: contra_notN Spoo => /eqP unpoo.
  by exists n.
have [{lnoo}loo|lpoo] := eqVneq l +oo.
  rewrite loo; apply/cvgeyPge => M.
  have /ereal_sup_gt[_ [n _] <- Mun] : M%:E < l by rewrite loo// ltry.
  by exists n => // m /= nm; rewrite (le_trans (ltW Mun))// nd_u_.
have l_fin_num : l \is a fin_num by rewrite fin_numE lpoo lnoo.
rewrite -(@fineK _ l)//; apply/fine_cvgP; split.
  near=> n; rewrite fin_numE Snoo/=; last by near: n; exists N.
  by apply: contra_notN Spoo => /eqP unpoo; exists n.
rewrite -(cvg_shiftn N); set v_ := [sequence _]_ _.
have <- : sup (range v_) = fine l.
  apply: EFin_inj; rewrite -ereal_sup_EFin//; last 2 first.
    - exists (fine l) => /= _ [m _ <-]; rewrite /v_ /= fine_le//.
        by rewrite u_fin_num// leq_addl.
      by apply: ereal_sup_ubound; exists (m + N)%N.
    - by exists (v_ 0%N), 0%N.
  rewrite fineK//; apply/eqP; rewrite eq_le; apply/andP; split.
    apply: le_ereal_sup => _ /= [_ [m _] <-] <-.
    by exists (m + N)%N => //; rewrite /v_/= fineK// u_fin_num// leq_addl.
  apply: ub_ereal_sup => /= _ [m _] <-.
  rewrite (@le_trans _ _ (u_ (m + N)%N))//; first by rewrite nd_u_// leq_addr.
  apply: ereal_sup_ubound => /=; exists (fine (u_ (m + N))); first by exists m.
  by rewrite fineK// u_fin_num// leq_addl.
apply: nondecreasing_cvgn.
- move=> m n mn /=; rewrite /v_ /= fine_le ?u_fin_num ?leq_addl//.
  by rewrite nd_u_// leq_add2r.
- exists (fine l) => /= _ [m _ <-]; rewrite /v_ /= fine_le//.
    by rewrite u_fin_num// leq_addl.
  by apply: ereal_sup_ubound; exists (m + N).
Unshelve. all: by end_near. Qed.

Lemma ereal_nondecreasing_is_cvgn (R : realType) (u_ : (\bar R) ^nat) :
  nondecreasing_seq u_ -> cvgn u_.
Proof. by move=> ?; apply/cvg_ex; eexists; exact: ereal_nondecreasing_cvgn. Qed.

Lemma ereal_nonincreasing_cvgn (R : realType) (u_ : (\bar R)^nat) :
  nonincreasing_seq u_ -> u_ @ \oo --> ereal_inf (u_ @` setT).
Proof.
move=> ni_u; rewrite [X in X @ \oo --> _](_ : _ = -%E \o -%E \o u_); last first.
  by rewrite funeqE => n; rewrite /= oppeK.
apply: cvgeN.
rewrite [X in _ --> X](_ : _ = ereal_sup (range (-%E \o u_))); last first.
  congr ereal_sup; rewrite predeqE => x; split=> [[_ [n _ <-]] <-|[n _] <-];
    by [exists n | exists (u_ n) => //; exists n].
by apply: ereal_nondecreasing_cvgn; rewrite ereal_nondecreasing_oppn.
Qed.

Lemma ereal_nonincreasing_is_cvgn (R : realType) (u_ : (\bar R) ^nat) :
  nonincreasing_seq u_ -> cvgn u_.
Proof. by move=> ?; apply/cvg_ex; eexists; apply: ereal_nonincreasing_cvgn. Qed.

(* NB: see also nondecreasing_series *)
Lemma ereal_nondecreasing_series (R : realDomainType) (u_ : (\bar R)^nat)
  (P : pred nat) N : (forall n, (N <= n)%N -> P n -> 0 <= u_ n) ->
  nondecreasing_seq (fun n => \sum_(N <= i < n | P i) u_ i).
Proof. by move=> u_ge0 n m nm; rewrite lee_sum_nneg_natr. Qed.

Lemma congr_lim (R : numFieldType) (f g : nat -> \bar R) :
  f = g -> limn f = limn g.
Proof. by move=> ->. Qed.

Lemma eseries_cond {R : numFieldType} (f : (\bar R)^nat) P N :
  \sum_(N <= i <oo | P i) f i = \sum_(i <oo | P i && (N <= i)%N) f i.
Proof. by apply/congr_lim/eq_fun => n /=; apply: big_nat_widenl. Qed.

Lemma eseries_mkcondl {R : numFieldType} (f : (\bar R)^nat) P Q N :
  \sum_(N <= i <oo | P i && Q i) f i =
  \sum_(N <= i <oo | Q i) if P i then f i else 0.
Proof. by apply/congr_lim/funext => n; rewrite big_mkcondl. Qed.

Lemma eseries_mkcondr {R : numFieldType} (f : (\bar R)^nat) P Q N :
  \sum_(N <= i <oo | P i && Q i) f i =
  \sum_(N <= i <oo | P i) if Q i then f i else 0.
Proof. by apply/congr_lim/funext => n; rewrite big_mkcondr. Qed.

Lemma eq_eseriesr (R : numFieldType) (f g : (\bar R)^nat) (P : pred nat) {N} :
  (forall i, P i -> f i = g i) ->
  \sum_(N <= i <oo | P i) f i = \sum_(N <= i <oo | P i) g i.
Proof. by move=> efg; apply/congr_lim/funext => n; exact: eq_bigr. Qed.

Lemma eq_eseriesl (R : realFieldType) (P Q : pred nat) (f : (\bar R)^nat) N :
  P =1 Q -> \sum_(N <= i <oo | P i) f i = \sum_(N <= i <oo | Q i) f i.
Proof. by move=> efg; apply/congr_lim/funext => n; apply: eq_bigl. Qed.
Arguments eq_eseriesl {R P} Q.

Lemma lim_mkord (R : realFieldType) (P : {pred nat}) (f : (\bar R)^nat) :
  limn (fun n => \sum_(k < n | P k) f k)%E = \sum_(k <oo | P k) f k.
Proof. by under eq_fun do rewrite -big_mkord. Qed.

Section ereal_series.
Variables (R : realFieldType) (f : (\bar R)^nat).
Implicit Types P : pred nat.

Lemma ereal_series_cond k P :
  \sum_(k <= i <oo | P i) f i = \sum_(i <oo | (k <= i)%N && P i) f i.
Proof.
apply/congr_lim/funext => n.
rewrite big_nat_cond (big_nat_widenl k 0%N)//= 2!big_mkord.
by apply: eq_big => //= i; rewrite andbAC ltn_ord andbT andbb.
Qed.

Lemma ereal_series k : \sum_(k <= i <oo) f i = \sum_(i <oo | (k <= i)%N) f i.
Proof.
rewrite ereal_series_cond; congr (limn _); apply/funext => n.
by apply: eq_big => // i; rewrite andbT.
Qed.

Lemma eseries0 N P : (forall i, (N <= i)%N -> P i -> f i = 0) ->
  \sum_(N <= i <oo | P i) f i = 0.
Proof.
move=> f0; apply/cvg_lim => //.
under eq_fun.
  move=> n.
  rewrite big_nat_cond big1; last by move=> k /andP[/andP[+ _]]; exact: f0.
  over.
exact: cvg_cst.
Qed.

Lemma eseries_pred0 P : P =1 xpred0 -> \sum_(i <oo | P i) f i = 0.
Proof.
move=> P0; rewrite (_ : (fun _ => _) = fun=> 0) ?lim_cst// funeqE => n.
by rewrite big1 // => i; rewrite P0.
Qed.

End ereal_series.

Lemma nneseries_lim_ge (R : realType) (u_ : (\bar R)^nat) (P : pred nat) {m} k :
  (forall n, (m <= n)%N -> P n -> 0 <= u_ n) ->
  \sum_(m <= i < k | P i) u_ i <= \sum_(m <= i <oo | P i) u_ i.
Proof.
move/ereal_nondecreasing_series/ereal_nondecreasing_cvgn/cvg_lim => -> //.
by apply: ereal_sup_ubound; exists k.
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
  cvgn (fun n => \sum_(m <= i < n | P i) u_ i).
Proof.
by move/lee_sum_nneg_natr/ereal_nondecreasing_cvgn => cu; apply: cvgP; exact: cu.
Qed.

Lemma is_cvg_ereal_npos_natsum_cond m P :
    (forall n, (m <= n)%N -> P n -> u_ n <= 0) ->
  cvgn (fun n => \sum_(m <= i < n | P i) u_ i).
Proof.
by move/lee_sum_npos_natr/ereal_nonincreasing_cvgn => cu; apply: cvgP; exact: cu.
Qed.

Lemma is_cvg_ereal_nneg_natsum m : (forall n, (m <= n)%N -> 0 <= u_ n) ->
  cvgn (fun n => \sum_(m <= i < n) u_ i).
Proof. by move=> u_ge0; apply: is_cvg_ereal_nneg_natsum_cond => n /u_ge0. Qed.

Lemma is_cvg_ereal_npos_natsum m : (forall n, (m <= n)%N -> u_ n <= 0) ->
  cvgn (fun n => \sum_(m <= i < n) u_ i).
Proof. by move=> u_le0; apply: is_cvg_ereal_npos_natsum_cond => n /u_le0. Qed.

Lemma is_cvg_nneseries_cond P N : (forall n, (N <= n)%N -> P n -> 0 <= u_ n) ->
  cvgn (fun n => \sum_(N <= i < n | P i) u_ i).
Proof.
by move=> u_ge0; apply: is_cvg_ereal_nneg_natsum_cond => n Nn; exact: u_ge0.
Qed.

Lemma is_cvg_npeseries_cond P N : (forall n, (N <= n)%N -> P n -> u_ n <= 0) ->
  cvgn (fun n => \sum_(N <= i < n | P i) u_ i).
Proof. by move=> u_le0; exact: is_cvg_ereal_npos_natsum_cond. Qed.

Lemma is_cvg_nneseries P N : (forall n, (N <= n)%N -> P n -> 0 <= u_ n) ->
  cvgn (fun n => \sum_(N <= i < n | P i) u_ i).
Proof. by move=> ?; exact: is_cvg_nneseries_cond. Qed.

Lemma is_cvg_npeseries P N : (forall n, (N <= n)%N -> P n -> u_ n <= 0) ->
  cvgn (fun n => \sum_(N <= i < n | P i) u_ i).
Proof. by move=> ?; exact: is_cvg_npeseries_cond. Qed.

Lemma nneseries_ge0 P N : (forall n, (N <= n)%N -> P n -> 0 <= u_ n) ->
  0 <= \sum_(N <= i <oo | P i) u_ i.
Proof.
move=> u0; apply: (lime_ge (is_cvg_nneseries u0)); apply: nearW => k.
by rewrite big_nat_cond sume_ge0// => n /andP[/andP[+ _]]; exact: u0.
Qed.

Lemma npeseries_le0 P N : (forall n : nat, (N <= n)%N -> P n -> u_ n <= 0) ->
  \sum_(N <= i <oo | P i) u_ i <= 0.
Proof.
move=> u0; apply: (lime_le (is_cvg_npeseries u0)); apply: nearW => k.
by rewrite big_nat_cond sume_le0// => n /andP[/andP[+ _]]; exact: u0.
Qed.

End cvg_eseries.
Arguments is_cvg_nneseries {R}.
Arguments nneseries_ge0 {R u_ P} N.

Lemma nnseries_is_cvg {R : realType} (u : nat -> R) :
    (forall i, 0 <= u i)%R -> \sum_(k <oo) (u k)%:E < +oo ->
  cvgn (series u).
Proof.
move=> ? ?; apply: nondecreasing_is_cvgn.
  move=> m n mn; rewrite /series/=.
  rewrite -(subnKC mn) {2}/index_iota subn0 iotaD big_cat/=.
  by rewrite add0n -{2}(subn0 m) -/(index_iota _ _) lerDl sumr_ge0.
exists (fine (\sum_(k <oo) (u k)%:E)).
rewrite /ubound/= => _ [n _ <-]; rewrite -lee_fin fineK//; last first.
  rewrite fin_num_abs gee0_abs//; apply: nneseries_ge0 => // i _.
  by rewrite lee_fin.
by rewrite -sumEFin; apply: nneseries_lim_ge => i _; rewrite lee_fin.
Qed.

Lemma nneseriesZl (R : realType) (f : nat -> \bar R) (P : pred nat) x N :
  (forall i, P i -> 0 <= f i) ->
  (\sum_(N <= i <oo | P i) (x%:E * f i) = x%:E * \sum_(N <= i <oo | P i) f i).
Proof.
move=> f0; rewrite -limeMl//; last by apply: is_cvg_nneseries => n _; exact: f0.
by apply/congr_lim/funext => /= n; rewrite ge0_sume_distrr.
Qed.

Lemma adde_def_nneseries (R : realType) (f g : (\bar R)^nat)
    (P Q : pred nat) m :
  (forall n, (m <= n)%N -> P n -> 0 <= f n) ->
  (forall n, (m <= n)%N -> Q n -> 0 <= g n) ->
  (\sum_(m <= i <oo | P i) f i) +? (\sum_(m <= i <oo | Q i) g i).
Proof.
move=> f0 g0; rewrite /adde_def !negb_and; apply/andP; split; apply/orP.
- by right; apply/eqP => Qg; have := nneseries_ge0 m g0; rewrite Qg.
- by left; apply/eqP => Pf; have := nneseries_ge0 m f0; rewrite Pf.
Qed.

Lemma nneseries_pinfty (R : realType) (u_ : (\bar R)^nat)
  (P : pred nat) k : (forall n, P n -> 0 <= u_ n) -> P k ->
  u_ k = +oo -> \sum_(i <oo | P i) u_ i = +oo.
Proof.
move=> u_ge0 Pk ukoo; apply: (eseries_pinfty _ Pk ukoo) => // n Pn.
by rewrite gt_eqF// (lt_le_trans _ (u_ge0 _ Pn)).
Qed.

Lemma lee_nneseries (R : realType) (u v : (\bar R)^nat) (P : pred nat) N :
  (forall i, (N <= i)%N -> P i -> 0 <= u i) ->
  (forall n, P n -> u n <= v n) ->
  \sum_(N <= i <oo | P i) u i <= \sum_(N <= i <oo | P i) v i.
Proof.
move=> u0 Puv; apply: lee_lim.
- by apply: is_cvg_ereal_nneg_natsum_cond => n Nn /u0; exact.
- apply: is_cvg_ereal_nneg_natsum_cond => n Nn Pn.
  by rewrite (le_trans _ (Puv _ Pn))// u0.
- by near=> n; apply: lee_sum => k; exact: Puv.
Unshelve. all: by end_near. Qed.

Lemma subset_lee_nneseries (R : realType) (u : (\bar R)^nat) (P Q : pred nat)
    (N : nat) :
  (forall i, Q i -> 0 <= u i) ->
  (forall i, P i -> Q i) ->
  \sum_(N <= i <oo | P i) u i <= \sum_(N <= i <oo | Q i) u i.
Proof.
move=> Pu PQ; apply: lee_lim.
- apply: ereal_nondecreasing_is_cvgn => a b ab.
  by apply: lee_sum_nneg_natr => // n Mn Pn; apply: Pu => //; exact: PQ.
- apply: ereal_nondecreasing_is_cvgn => a b ab.
  by apply: lee_sum_nneg_natr => // n Mn Pn; apply: Pu => //; exact: PQ.
- near=> n; apply: lee_sum_nneg_subset => //.
  by move=> i; rewrite inE => /andP[iP iQ]; exact: Pu.
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

Let lim_shift_cst (R : realFieldType) (u : (\bar R) ^nat) (l : \bar R) :
    cvgn u -> (forall n, 0 <= u n) -> -oo < l ->
  limn (fun x => l + u x) = l + limn u.
Proof.
move=> cu u0 hl; apply/cvg_lim => //; apply: cvgeD (cu); last first.
  exact: cvg_cst.
rewrite ltninfty_adde_def// inE (@lt_le_trans _ _ 0)//.
by apply: lime_ge => //; exact: nearW.
Qed.

Lemma eseries_mkcond [R : realFieldType] [P : pred nat] (f : nat -> \bar R) N :
  \sum_(N <= i <oo | P i) f i = \sum_(N <= i <oo) if P i then f i else 0.
Proof. by apply/congr_lim/eq_fun => n /=; apply: big_mkcond. Qed.

Section nneseries_split.

Let near_eq_lim (R : realFieldType) (f g : nat -> \bar R) :
  cvgn g -> {near \oo, f =1 g} -> limn f = limn g.
Proof.
move=> cg fg; suff: f @ \oo --> limn g by exact/cvg_lim.
by apply: cvg_trans cg; apply: near_eq_cvg; near do apply/esym.
Unshelve. all: by end_near. Qed.

Lemma nneseries_split (R : realType) (f : nat -> \bar R) N n :
  (forall k, (N <= k)%N -> 0 <= f k) ->
  \sum_(N <= k <oo) f k = \sum_(N <= k < N + n) f k + \sum_(N + n <= k <oo) f k.
Proof.
elim: n N => [N |n ih N] f0.
  rewrite addn0 [in X in _ = X + _]/index_iota subnn.
  by rewrite (@size0nil _ (iota _ 0)) ?size_iota// big_nil add0r.
rewrite addnS big_nat_recr/= ?leq_addr// -addeA.
rewrite [f (N + n)%N + _](_ : _ = \sum_(N + n <= k <oo) f k); first exact: ih.
have cf m : (m >= N)%N -> cvgn (fun n => \sum_(m <= k < n) f k).
  move=> Nm; apply: is_cvg_ereal_nneg_natsum => p Nmp.
  by rewrite f0// (leq_trans _ Nmp).
rewrite -lim_shift_cst; last by rewrite (@lt_le_trans _ _ 0)// f0// leq_addr.
- apply: (@near_eq_lim _ (fun x => f (N + n)%N + _)) => //.
  by apply: cf; rewrite leq_addr.
  by near do rewrite -big_ltn//; exact: nbhs_infty_gt.
- by apply: cf; rewrite -addnS leq_addr.
- move=> m; rewrite big_seq; apply: sume_ge0 => /= p.
  rewrite mem_index_iota => /andP[Nnp _].
  by rewrite f0// (leq_trans _ Nnp)// -addnS leq_addr.
Unshelve. all: by end_near. Qed.

Lemma nneseries_split_cond (R : realType) (f : nat -> \bar R) N n (P : pred nat) :
  (forall k, P k -> 0 <= f k)%E ->
  \sum_(N <= k <oo | P k) f k =
  \sum_(N <= k < N + n | P k) f k + \sum_(N + n <= k <oo | P k) f k.
Proof.
move=> NPf; rewrite eseries_mkcond [X in _ = (_ + X)]eseries_mkcond.
rewrite big_mkcond/= (nneseries_split n)// => k Nk.
by case: ifPn => //; exact: NPf.
Qed.

End nneseries_split.
Arguments nneseries_split {R f} _ _.
Arguments nneseries_split_cond {R f} _ _ _.

Lemma nneseries_recl (R : realType) (f : nat -> \bar R) :
  (forall k, 0 <= f k) -> \sum_(k <oo) f k = f 0%N + \sum_(1 <= k <oo) f k.
Proof.
move=> f0; rewrite [LHS](nneseries_split _ 1)// add0n.
by rewrite /index_iota subn0/= big_cons big_nil addr0.
Qed.

Lemma nneseries_tail_cvg (R : realType) (f : (\bar R)^nat) P :
  (\sum_(0 <= k <oo | P k) f k < +oo -> (forall k, P k -> 0 <= f k) ->
  \sum_(N <= k <oo | P k) f k @[N --> \oo] --> 0)%E.
Proof.
move=> foo f0.
have : cvg (\sum_(0 <= k < n | P k) f k @[n --> \oo]).
  apply: ereal_nondecreasing_is_cvgn.
  by apply: lee_sum_nneg_natr => n _; exact: f0.
move/cvg_ex => [[l fl||/cvg_lim fnoo]] /=; last 2 first.
  - by move/cvg_lim => fpoo; rewrite fpoo// in foo.
  - have : 0 <= \sum_(k <oo | P k) f k.
      by apply: nneseries_ge0 => n _; exact: f0.
    by rewrite fnoo.
rewrite [X in X @ _ --> _](_ : _ = fun N => l%:E - \sum_(0 <= k < N | P k) f k).
  apply/cvgeNP; rewrite oppe0.
  under eq_fun => ? do rewrite oppeD// oppeK addeC.
  exact/sube_cvg0.
apply/funext => N; apply/esym/eqP; rewrite sube_eq//.
  by rewrite addeC -nneseries_split_cond//; exact/eqP/esym/cvg_lim.
rewrite ge0_adde_def//= ?inE; last exact: sume_ge0.
by apply: nneseries_ge0 => n Nn; exact: f0.
Qed.

Lemma nneseriesD (R : realType) (f g : nat -> \bar R) (P : pred nat) N :
  (forall i, (N <= i)%N -> P i -> 0 <= f i) ->
  (forall i, (N <= i)%N -> P i -> 0 <= g i) ->
  \sum_(N <= i <oo | P i) (f i + g i) =
  \sum_(N <= i <oo | P i) f i + \sum_(N <= i <oo | P i) g i.
Proof.
move=> f_eq0 g_eq0.
transitivity (limn (fun n => \sum_(N <= i < n | P i) f i +
                         \sum_(N <= i < n | P i) g i)).
  by apply/congr_lim/funext => n; rewrite big_split.
rewrite limeD /adde_def //=; do ? exact: is_cvg_nneseries.
by rewrite ![_ == -oo]gt_eqF ?andbF// (@lt_le_trans _ _ 0)
           ?[_ < _]real0// nneseries_ge0.
Qed.

Lemma nneseries_sum_nat (R : realType) m n (f : nat -> nat -> \bar R) N :
  (forall i j, 0 <= f i j) ->
  \sum_(N <= j <oo) (\sum_(m <= i < n) f i j) =
  \sum_(m <= i < n) (\sum_(N <= j <oo) f i j).
Proof.
move=> f0; elim: n => [|n ih].
  by rewrite big_geq// eseries0// => i; rewrite big_geq.
have [mn|nm] := leqP m n.
  rewrite big_nat_recr// -ih/= -nneseriesD//; last by move=> i; rewrite sume_ge0.
  by apply/congr_lim/funext => ?; apply: eq_bigr => i _; rewrite big_nat_recr.
by rewrite big_geq// eseries0// => i; rewrite big_geq.
Qed.

Lemma nneseries_sum I (r : seq I) (P : {pred I}) [R : realType]
    [f : I -> nat -> \bar R] N : (forall i j, P i -> 0 <= f i j) ->
  \sum_(N <= j <oo) \sum_(i <- r | P i) f i j =
  \sum_(i <- r | P i) \sum_(N <= j <oo) f i j.
Proof.
move=> f_ge0; case Dr : r => [|i r']; rewrite -?{}[_ :: _]Dr.
  by rewrite big_nil eseries0// => i; rewrite big_nil.
rewrite {r'}(big_nth i) big_mkcond.
rewrite (eq_eseriesr (fun _ _ => big_nth i _ _)).
rewrite (eq_eseriesr (fun _ _ => big_mkcond _ _))/=.
rewrite nneseries_sum_nat; last by move=> ? ?; case: ifP => // /f_ge0.
by apply: eq_bigr => j _; case: ifP => //; rewrite eseries0.
Qed.

Lemma nneseries_addn {R : realType} (f : (\bar R)^nat) k :
  (forall i, 0 <= f i) ->
  \sum_(i <oo) f (i + k)%N = \sum_(k <= i <oo) f i.
Proof.
move=> f0; have /cvg_ex[/= l fl] : cvg (\sum_(k <= i < n) f i @[n --> \oo]).
  by apply: ereal_nondecreasing_is_cvgn => m n mn; exact: lee_sum_nneg_natr.
rewrite (cvg_lim _ fl)//; apply/cvg_lim => //=.
move: fl; rewrite -(cvg_shiftn k) /=.
by under eq_fun do rewrite -{1}(add0n k)// big_addn addnK.
Qed.

Lemma lte_lim (R : realFieldType) (u : (\bar R)^nat) (M : R) :
  nondecreasing_seq u -> cvgn u -> M%:E < limn u ->
  \forall n \near \oo, M%:E <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|] := pselect (exists n, M%:E <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
move/forallNP => Mu.
have {}Mu : forall x, M%:E > u x by move=> x; rewrite ltNge; apply/negP.
have : limn u <= M%:E by apply lime_le => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near. Qed.

End sequences_ereal.
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `ereal_nondecreasing_cvgn`")]
Notation ereal_nondecreasing_cvg := ereal_nondecreasing_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `ereal_nondecreasing_is_cvgn`")]
Notation ereal_nondecreasing_is_cvg := ereal_nondecreasing_is_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `ereal_nonincreasing_cvgn`")]
Notation ereal_nonincreasing_cvg := ereal_nonincreasing_cvgn (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6",
  note="renamed to `ereal_nonincreasing_is_cvgn`")]
Notation ereal_nonincreasing_is_cvg := ereal_nonincreasing_is_cvgn (only parsing).

Arguments nneseries_split {R f} _ _.

Section minr_cvg_0.
Local Open Scope ring_scope.
Context {R : realFieldType}.
Implicit Types (u : R^nat) (r : R).

Lemma minr_cvg_0_cvg_0 u r : 0 < r -> (forall k, 0 <= u k) ->
  minr (u n) r @[n --> \oo] --> 0 -> u n @[n --> \oo] --> 0.
Proof.
move=> r0 u0 minr_cvg; apply/cvgrPdist_lt => _ /posnumP[e].
have : 0 < minr e%:num r by rewrite lt_min// r0 andbT.
move/cvgrPdist_lt : minr_cvg => /[apply] -[M _ hM].
near=> n; rewrite sub0r normrN.
have /hM : (M <= n)%N by near: n; exists M.
rewrite sub0r normrN (ger0_norm (u0 n)) ger0_norm// => [/lt_min_lt//|].
by rewrite le_min u0 ltW.
Unshelve. all: by end_near. Qed.

Lemma maxr_cvg_0_cvg_0 u r : r < 0 -> (forall k, u k <= 0) ->
  maxr (u n) r @[n --> \oo] --> 0 -> u n @[n --> \oo] --> 0.
Proof.
rewrite -[in r < _]oppr0 ltrNr => r0 u0.
under eq_fun do rewrite -(opprK (u _)) -[in maxr _ _](opprK r) -oppr_min.
rewrite -[in _ --> _]oppr0 => /cvgNP/minr_cvg_0_cvg_0-/(_ r0).
have Nu0 k : 0 <= - u k by rewrite lerNr oppr0.
by move=> /(_ Nu0)/(cvgNP _ _).2; rewrite opprK oppr0.
Qed.

End minr_cvg_0.

Section mine_cvg_0.
Context {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types (u : (\bar R)^nat) (r : R) (x : \bar R).

Lemma mine_cvg_0_cvg_fin_num u x : 0 < x -> (forall k, 0 <= u k) ->
  mine (u n) x @[n --> \oo] --> 0 ->
  \forall n \near \oo, u n \is a fin_num.
Proof.
case: x => [r r0 u0 /fine_cvgP[_]|_ u0|//]; last first.
  under eq_cvg do rewrite miney.
  by case/fine_cvgP.
move=> /cvgrPdist_lt/(_ _ r0)[N _ hN].
near=> n; have /hN : (N <= n)%N by near: n; exists N.
rewrite sub0r normrN /= ger0_norm ?fine_ge0//; last first.
  by rewrite le_min u0 ltW.
by have := u0 n; case: (u n) => //=; rewrite ltxx.
Unshelve. all: by end_near. Qed.

Lemma mine_cvg_minr_cvg u r : (0 < r)%R -> (forall k, 0 <= u k) ->
  mine (u n) r%:E @[n --> \oo] --> 0 ->
  minr (fine (u n)) r @[n --> \oo] --> 0%R.
Proof.
move=> r0 u0 mine_cvg; apply: (cvg_trans _ (fine_cvg mine_cvg)).
move/fine_cvgP : mine_cvg => [_ /=] /cvgrPdist_lt.
move=> /(_ _ r0)[N _ hN]; apply: near_eq_cvg; near=> n.
have xnoo : u n < +oo.
  rewrite ltNge leye_eq; apply/eqP => xnoo.
  have /hN : (N <= n)%N by near: n; exists N.
  by rewrite /= sub0r normrN xnoo //= gtr0_norm // ltxx.
by rewrite /= -(@fineK _ (u n)) ?ge0_fin_numE//= -fine_min.
Unshelve. all: by end_near. Qed.

Lemma mine_cvg_0_cvg_0 u x : 0 < x -> (forall k, 0 <= u k) ->
  mine (u n) x @[n --> \oo] --> 0 -> u n @[n --> \oo] --> 0.
Proof.
move=> x0 u0 h; apply/fine_cvgP; split.
  exact: (mine_cvg_0_cvg_fin_num x0).
case: x x0 h => [r r0 h|_|//]; last first.
  under eq_cvg do rewrite miney.
  exact: fine_cvg.
apply: (@minr_cvg_0_cvg_0 _ (fine \o u) r) => //.
  by move=> k /=; rewrite fine_ge0.
exact: mine_cvg_minr_cvg.
Qed.

Lemma maxe_cvg_0_cvg_fin_num u x : x < 0 -> (forall k, u k <= 0) ->
  maxe (u n) x @[n --> \oo] --> 0 ->
  \forall n \near \oo, u n \is a fin_num.
Proof.
rewrite -[in x < _]oppe0 lteNr => x0 u0.
under eq_fun do rewrite -(oppeK (u _)) -[in maxe _ _](oppeK x) -oppe_min.
rewrite -[in _ --> _]oppe0 => /cvgeNP/mine_cvg_0_cvg_fin_num-/(_ x0).
have Nu0 k : 0 <= - u k by rewrite leeNr oppe0.
by move=> /(_ Nu0)[n _ nu]; exists n => // m/= nm; rewrite -fin_numN nu.
Qed.

Lemma maxe_cvg_maxr_cvg u r : (r < 0)%R -> (forall k, u k <= 0) ->
  maxe (u n) r%:E @[n --> \oo] --> 0 ->
  maxr (fine (u n)) r @[n --> \oo] --> 0%R.
Proof.
rewrite -[in (r < _)%R]oppr0 ltrNr => r0 u0.
under eq_fun do rewrite -(oppeK (u _)) -[in maxe _ _](oppeK r%:E) -oppe_min.
rewrite -[in _ --> _]oppe0 => /cvgeNP/mine_cvg_minr_cvg-/(_ r0).
have Nu0 k : 0 <= - u k by rewrite leeNr oppe0.
move=> /(_ Nu0)/(cvgNP _ _).2; rewrite oppr0.
by under eq_cvg do rewrite /GRing.opp /= oppr_min fineN !opprK.
Qed.

Lemma maxe_cvg_0_cvg_0 u x : x < 0 -> (forall k, u k <= 0) ->
  maxe (u n) x @[n --> \oo] --> 0 -> u n @[n --> \oo] --> 0.
Proof.
rewrite -[in x < _]oppe0 lteNr => x0 u0.
under eq_fun do rewrite -(oppeK (u _)) -[in maxe _ _](oppeK x) -oppe_min.
rewrite -[in _ --> _]oppe0 => /cvgeNP/mine_cvg_0_cvg_0-/(_ x0).
have Nu0 k : 0 <= - u k by rewrite leeNr oppe0.
by move=> /(_ Nu0); rewrite -[in _ --> _]oppe0 => /cvgeNP.
Qed.

End mine_cvg_0.

Definition sdrop T (u : T^nat) n := [set u k | k in [set k | k >= n]]%N.

Section sdrop.
Variables (d : Order.disp_t) (R : porderType d).
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

Lemma is_cvg_sups u : cvgn u -> cvgn (sups u).
Proof.
move=> cf; have [M [Mreal Mu]] := cvg_seq_bounded cf.
apply: nonincreasing_is_cvgn.
  exact/nonincreasing_sups/bounded_fun_has_ubound/cvg_seq_bounded.
exists (- (M + 1)) => _ [n _ <-]; rewrite (@le_trans _ _ (u n)) //.
  by apply/lerNnormlW/Mu => //; rewrite ltrDl.
apply: sup_ubound; last by exists n => /=.
exact/has_ubound_sdrop/bounded_fun_has_ubound/cvg_seq_bounded.
Qed.

Lemma is_cvg_infs u : cvgn u -> cvgn (infs u).
Proof.
by move/is_cvgN/is_cvg_sups; rewrite supsN; move/is_cvgN; rewrite opprK.
Qed.

Lemma infs_le_sups u n : cvgn u -> infs u n <= sups u n.
Proof.
move=> cu; rewrite /infs /sups /=; set A := sdrop _ _.
have [a Aa] : A !=set0 by exists (u n); rewrite /A /=; exists n => //=.
rewrite (@le_trans _ _ a) //; [apply/inf_lbound|apply/sup_ubound] => //.
- exact/has_lbound_sdrop/bounded_fun_has_lbound/cvg_seq_bounded.
- exact/has_ubound_sdrop/bounded_fun_has_ubound/cvg_seq_bounded.
Qed.

Lemma cvg_sups_inf u : has_ubound (range u) -> has_lbound (range u) ->
  sups u @ \oo --> inf (range (sups u)).
Proof.
move=> u_ub u_lb; apply: nonincreasing_cvgn; first exact: nonincreasing_sups.
case: u_lb => M uM; exists M => _ [n _ <-].
rewrite (@le_trans _ _ (u n)) //; first by apply: uM; exists n.
by apply: sup_ubound; [exact/has_ubound_sdrop|exists n => /=].
Qed.

Lemma cvg_infs_sup u : has_ubound (range u) -> has_lbound (range u) ->
  infs u @ \oo --> sup (range (infs u)).
Proof.
move=> u_ub u_lb; have : sups (- u) @ \oo --> inf (range (sups (- u))).
  apply: cvg_sups_inf.
  - by move: u_lb => /has_lb_ubN; rewrite image_comp.
  - by move: u_ub => /has_ub_lbN; rewrite image_comp.
rewrite /inf => /(@cvg_comp _ _ _ _ (fun x => - x)).
rewrite supsN /comp /= -[in X in _ -> X --> _](opprK (infs u)); apply.
rewrite image_comp /comp /= -(opprK (sup (range (infs u)))); apply: cvgN.
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
  by apply: sup_ubound; [exact/has_ubound_sdrop/f_ub|by exists k].
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
  by apply/inf_lbound => //; [exact/has_lbound_sdrop/lb_f|by exists k].
Qed.

Lemma bounded_fun_has_lbound_sups u :
  bounded_fun u -> has_lbound (range (sups u)).
Proof.
move=> /[dup] ba /bounded_fun_has_lbound/has_lbound_sdrop h.
have [M hM] := h O; exists M => y [n _ <-].
rewrite (@le_trans _ _ (u n)) //; first by apply: hM; exists n.
apply: sup_ubound; last by exists n => /=.
by move: ba => /bounded_fun_has_ubound/has_ubound_sdrop; exact.
Qed.

Lemma bounded_fun_has_ubound_infs u :
  bounded_fun u -> has_ubound (range (infs u)).
Proof.
move=> /[dup] ba /bounded_fun_has_ubound/has_ubound_sdrop h.
have [M hM] := h O; exists M => y [n _ <-].
rewrite (@le_trans _ _ (u n)) //; last by apply: hM; exists n.
apply: inf_lbound; last by exists n => /=.
by move: ba => /bounded_fun_has_lbound/has_lbound_sdrop; exact.
Qed.

End sups_infs.

Section limn_sup_limn_inf.
Variable R : realType.
Implicit Types (r : R) (u v : R^o^nat).

Definition limn_sup u := limn (sups u).

Definition limn_inf u := limn (infs u).

Lemma limn_infN u : cvgn u -> limn_inf (-%R \o u) = - limn_sup u.
Proof.
by move=> cu_; rewrite /limn_inf infsN limN//; exact: is_cvg_sups.
Qed.

Lemma limn_supE u : bounded_fun u -> limn_sup u = inf (range (sups u)).
Proof.
move=> ba; apply/cvg_lim => //.
by apply/cvg_sups_inf; [exact/bounded_fun_has_ubound|
                        exact/bounded_fun_has_lbound].
Qed.

Lemma limn_infE u : bounded_fun u -> limn_inf u = sup (range (infs u)).
Proof.
move=> ba; apply/cvg_lim => //.
by apply/cvg_infs_sup; [exact/bounded_fun_has_ubound|
                        exact/bounded_fun_has_lbound].
Qed.

Lemma limn_inf_sup u : cvgn u -> limn_inf u <= limn_sup u.
Proof.
move=> cf_; apply: ler_lim; [exact: is_cvg_infs|exact: is_cvg_sups|].
by apply: nearW => n; apply: infs_le_sups.
Qed.

Lemma cvg_limn_inf_sup u l : u @ \oo --> l -> (limn_inf u = l) * (limn_sup u = l).
Proof.
move=> ul.
have /cvg_seq_bounded [M [Mr Mu]] : cvg (u @ \oo)
   by apply/cvg_ex; eexists; exact: ul.
suff: limn_sup u <= l <= limn_inf u.
  move=> /andP[sul liu].
  have /limn_inf_sup iusu : cvg (u @ \oo) by apply/cvg_ex; eexists; exact: ul.
  split; first by apply/eqP; rewrite eq_le liu andbT (le_trans iusu).
  by apply/eqP; rewrite eq_le sul /= (le_trans _ iusu).
apply/andP; split.
- apply/ler_addgt0Pr => e e0.
  apply: limr_le; first by apply: is_cvg_sups; apply/cvg_ex; exists l.
  move/cvgrPdist_lt : (ul) => /(_ _ e0) -[k _ klu].
  near=> n; have kn : (k <= n)%N by near: n; exists k.
  apply: sup_le_ub; first by exists (u n) => /=; exists n => //=.
  move=> _ /= [m nm] <-; apply/ltW/ltr_distlDr; rewrite distrC.
  by apply: (klu m) => /=; rewrite (leq_trans kn).
- apply/ler_addgt0Pr => e e0; rewrite -lerBlDr.
  apply: limr_ge; first by apply: is_cvg_infs; apply/cvg_ex; exists l.
  move/cvgrPdist_lt : (ul) => /(_ _ e0) -[k _ klu].
  near=> n; have kn : (k <= n)%N by near: n; exists k.
  apply: lb_le_inf; first by exists (u n) => /=; exists n => //=.
  move=> _ /= [m nm] <-; apply/ltW/ltr_distlBl.
  by apply: (klu m) => /=; rewrite (leq_trans kn).
Unshelve. all: by end_near. Qed.

Lemma cvg_limn_infE u : cvgn u -> limn_inf u = limn u.
Proof.
move=> /cvg_ex[l ul]; have [-> _] := cvg_limn_inf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma cvg_limn_supE u : cvgn u -> limn_sup u = limn u.
Proof.
move=> /cvg_ex[l ul]; have [_ ->] := cvg_limn_inf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma cvg_sups u l : u @ \oo --> l -> sups u @ \oo --> (l : R^o).
Proof.
move=> ul; have [iul <-] := cvg_limn_inf_sup ul.
apply/cvg_closeP; split => //; apply: is_cvg_sups.
by apply/cvg_ex; eexists; apply: ul.
Qed.

Lemma cvg_infs u l : u @ \oo --> l -> infs u @ \oo --> (l : R^o).
Proof.
move=> ul; have [<- iul] := cvg_limn_inf_sup ul.
apply/cvg_closeP; split => //; apply: is_cvg_infs.
by apply/cvg_ex; eexists; apply: ul.
Qed.

Lemma le_limn_supD u v : bounded_fun u -> bounded_fun v ->
  limn_sup (u \+ v) <= limn_sup u + limn_sup v.
Proof.
move=> ba bb; have ab k : sups (u \+ v) k <= sups u k + sups v k.
  apply: sup_le_ub; first by exists ((u \+ v) k); exists k => /=.
  by move=> M [n /= kn <-]; apply: lerD; apply: sup_ubound; [
    exact/has_ubound_sdrop/bounded_fun_has_ubound; exact | exists n |
    exact/has_ubound_sdrop/bounded_fun_has_ubound; exact | exists n ].
have cu : cvgn (sups u).
  apply: nonincreasing_is_cvgn; last exact: bounded_fun_has_lbound_sups.
  exact/nonincreasing_sups/bounded_fun_has_ubound.
have cv : cvgn (sups v).
  apply: nonincreasing_is_cvgn; last exact: bounded_fun_has_lbound_sups.
  exact/nonincreasing_sups/bounded_fun_has_ubound.
rewrite -(limD cu cv); apply: ler_lim.
- apply: nonincreasing_is_cvgn; last first.
    exact/bounded_fun_has_lbound_sups/bounded_funD.
  exact/nonincreasing_sups/bounded_fun_has_ubound/bounded_funD.
- exact: is_cvgD cu cv.
- exact: nearW.
Qed.

Lemma le_limn_infD u v : bounded_fun u -> bounded_fun v ->
  limn_inf u + limn_inf v <= limn_inf (u \+ v).
Proof.
move=> ba bb; have ab k : infs u k + infs v k <= infs (u \+ v) k.
  apply: lb_le_inf; first by exists ((u \+ v) k); exists k => /=.
  by move=> M [n /= kn <-]; apply: lerD; apply: inf_lbound; [
    exact/has_lbound_sdrop/bounded_fun_has_lbound; exact | exists n |
    exact/has_lbound_sdrop/bounded_fun_has_lbound; exact | exists n ].
have cu : cvgn (infs u).
  apply: nondecreasing_is_cvgn; last exact: bounded_fun_has_ubound_infs.
  exact/nondecreasing_infs/bounded_fun_has_lbound.
have cv : cvgn (infs v).
  apply: nondecreasing_is_cvgn; last exact: bounded_fun_has_ubound_infs.
  exact/nondecreasing_infs/bounded_fun_has_lbound.
rewrite -(limD cu cv); apply: ler_lim.
- exact: is_cvgD cu cv.
- apply: nondecreasing_is_cvgn; last first.
    exact/bounded_fun_has_ubound_infs/bounded_funD.
  exact/nondecreasing_infs/bounded_fun_has_lbound/bounded_funD.
- exact: nearW.
Qed.

Lemma limn_supD u v : cvgn u -> cvgn v ->
  limn_sup (u \+ v) = limn_sup u + limn_sup v.
Proof.
move=> cu cv; have [ba bb] := (cvg_seq_bounded cu, cvg_seq_bounded cv).
apply/eqP; rewrite eq_le le_limn_supD //=.
have := @le_limn_supD _ _ (bounded_funD ba bb) (bounded_funN bb).
rewrite -lerBlDr; apply: le_trans.
rewrite -[_ \+ _]/(u + v - v) addrK -limn_infN; last exact: is_cvgN.
rewrite /comp /=; under eq_fun do rewrite opprK.
by rewrite lerD// cvg_limn_infE// cvg_limn_supE.
Qed.

Lemma limn_infD u v : cvgn u -> cvgn v ->
  limn_inf (u \+ v) = limn_inf u + limn_inf v.
Proof.
move=> cu cv; rewrite (cvg_limn_infE cu) -(cvg_limn_supE cu).
rewrite (cvg_limn_infE cv) -(cvg_limn_supE cv) -limn_supD//.
rewrite cvg_limn_supE; last exact: (@is_cvgD _ _ _ _ _ _ _ cu cv).
by rewrite cvg_limn_infE //; exact: (@is_cvgD _ _ _ _ _ _ _ cu cv).
Qed.

End limn_sup_limn_inf.

#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_sup`")]
Notation lim_sup := limn_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_inf`")]
Notation lim_inf := limn_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_infN`")]
Notation lim_infN := limn_infN (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_supE`")]
Notation lim_supE := limn_supE (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_infE`")]
Notation lim_infE := limn_infE (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_inf_sup`")]
Notation lim_inf_le_lim_sup := limn_inf_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `cvg_limn_infE`")]
Notation cvg_lim_infE := cvg_limn_infE (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `cvg_limn_supE`")]
Notation cvg_lim_supE := cvg_limn_supE (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `le_limn_supD`")]
Notation le_lim_supD := le_limn_supD (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `le_limn_infD`")]
Notation le_lim_infD := le_limn_infD (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_supD`")]
Notation lim_supD := limn_supD (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_infD`")]
Notation lim_infD := limn_infD (only parsing).

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
by rewrite (@le_trans _ _ a)//; [exact/ereal_inf_lbound|exact/ereal_sup_ubound].
Unshelve. all: by end_near. Qed.

Lemma cvg_esups_inf u : esups u @ \oo --> ereal_inf (range (esups u)).
Proof. by apply: ereal_nonincreasing_cvgn => //; exact: nonincreasing_esups. Qed.

Lemma is_cvg_esups u : cvgn (esups u).
Proof. by apply/cvg_ex; eexists; exact/cvg_esups_inf. Qed.

Lemma cvg_einfs_sup u : einfs u @ \oo --> ereal_sup (range (einfs u)).
Proof. by apply: ereal_nondecreasing_cvgn => //; exact: nondecreasing_einfs. Qed.

Lemma is_cvg_einfs u : cvgn (einfs u).
Proof. by apply/cvg_ex; eexists; exact/cvg_einfs_sup. Qed.

Lemma esups_preimage T (a : \bar R) (f : (T -> \bar R)^nat) n :
  (fun x => esups (f^~x) n) @^-1` `]a, +oo[ =
  \bigcup_(k in [set k | n <= k]%N) f k @^-1` `]a, +oo[.
Proof.
rewrite predeqE => t; split => /=.
  rewrite /= in_itv /= andbT=> /ereal_sup_gt[_ [/= k nk <-]] afnt.
  by exists k => //=; rewrite in_itv /= afnt.
move=> -[k /= nk] /=; rewrite in_itv /= andbT => /lt_le_trans afkt.
by rewrite in_itv andbT/=; apply/afkt/ereal_sup_ubound; exists k.
Qed.

Lemma einfs_preimage T (a : \bar R) (f : (T -> \bar R)^nat) n :
  (fun x => einfs (f^~x) n) @^-1` `[a, +oo[%classic =
  \bigcap_(k in [set k | n <= k]%N) f k @^-1` `[a, +oo[%classic.
Proof.
rewrite predeqE => t; split => /= [|h].
  rewrite in_itv andbT /= => h k nk /=.
  by rewrite /= in_itv/= (le_trans h)//; apply: ereal_inf_lbound; exists k.
rewrite /= in_itv /= andbT leNgt; apply/negP.
move=> /ereal_inf_lt[_ /= [k nk <-]]; apply/negP.
by have := h _ nk; rewrite /= in_itv /= andbT -leNgt.
Qed.

End esups_einfs.

Section limn_esup_einf.
Context {R : realType}.
Implicit Type (u : (\bar R)^nat).
Local Open Scope ereal_scope.

Definition limn_esup u := limf_esup u \oo.

Definition limn_einf u := - limn_esup (\- u).

Lemma limn_esup_lim u : limn_esup u = limn (esups u).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: lime_ge; first exact: is_cvg_esups.
  near=> m; apply: ereal_inf_lbound => /=.
  by exists [set k | (m <= k)%N] => //=; exists m.
apply: lb_ereal_inf => /= _ [A [r /= r0 rA] <-].
apply: lime_le; first exact: is_cvg_esups.
near=> m;   apply: le_ereal_sup => _ [n /= mn] <-.
exists n => //; apply: rA => //=; apply: leq_trans mn.
by near: m; exists r.
Unshelve. all: by end_near. Qed.

Lemma limn_einf_lim u : limn_einf u = limn (einfs u).
Proof.
rewrite /limn_einf limn_esup_lim esupsN -limeN//.
  by under eq_fun do rewrite oppeK.
by apply: is_cvgeN; exact: is_cvg_einfs.
Qed.

End limn_esup_einf.

Section lim_esup_inf.
Local Open Scope ereal_scope.
Variable R : realType.
Implicit Types (u v : (\bar R)^nat) (l : \bar R).

Lemma limn_einf_shift u l : l \is a fin_num ->
  limn_einf (fun x => l + u x) = l + limn_einf u.
Proof.
move=> lfin; rewrite !limn_einf_lim; apply/cvg_lim => //; apply: cvg_trans; last first.
  apply: (@cvgeD _ \oo _ _ (cst l) (einfs u) _ (limn (einfs u))).
  - by rewrite fin_num_adde_defr.
  - exact: cvg_cst.
  - exact: is_cvg_einfs.
suff : einfs (fun n => l + u n) = (fun n => l + einfs u n) by move=> ->.
rewrite funeqE => n.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite addeC -leeBlDr//; apply: lb_ereal_inf => /= _ [m /= mn] <-.
  rewrite leeBlDr//; apply: ereal_inf_lbound.
  by exists m => //; rewrite addeC.
- apply: lb_ereal_inf => /= _ [m /= mn] <-.
  by rewrite leeD2l//; apply: ereal_inf_lbound; exists m => /=.
Qed.

Lemma limn_esup_le_cvg u l : limn_esup u <= l -> (forall n, l <= u n) ->
  u @ \oo --> l.
Proof.
move=> supul ul; have usupu n : l <= u n <= esups u n.
  by rewrite ul /=; apply/ereal_sup_ubound; exists n => /=.
suff : esups u @ \oo --> l.
  by apply: (@squeeze_cvge _ _ _ _ (cst l)) => //; [exact: nearW|exact: cvg_cst].
apply/cvg_closeP; split; first exact: is_cvg_esups.
rewrite closeE//; apply/eqP.
rewrite eq_le -[X in X <= _ <= _]limn_esup_lim supul/=.
apply: (lime_ge (@is_cvg_esups _ _)); apply: nearW => m.
have /le_trans : l <= einfs u m by apply: lb_ereal_inf => _ [p /= pm] <-.
by apply; exact: einfs_le_esups.
Qed.

Lemma limn_einfN u : limn_einf (-%E \o u) = - limn_esup u.
Proof. by rewrite /limn_esup -limf_einfN. Qed.

Lemma limn_esupN u : limn_esup (-%E \o u) = - limn_einf u.
Proof. by rewrite /limn_einf oppeK. Qed.

Lemma limn_einf_sup u : limn_einf u <= limn_esup u.
Proof.
rewrite limn_esup_lim limn_einf_lim.
apply: lee_lim; [exact/is_cvg_einfs|exact/is_cvg_esups|].
by apply: nearW; exact: einfs_le_esups.
Qed.

Lemma cvgNy_limn_einf_sup u : u @ \oo --> -oo ->
  (limn_einf u = -oo) * (limn_esup u = -oo).
Proof.
move=> uoo; suff: limn_esup u = -oo.
  by move=> {}uoo; split => //; apply/eqP; rewrite -leeNy_eq -uoo limn_einf_sup.
rewrite limn_esup_lim; apply: cvg_lim => //=; apply/cvgeNyPle => M.
have /cvgeNyPle/(_ M)[m _ uM] := uoo.
near=> n; apply: ub_ereal_sup => _ [k /= nk <-].
by apply: uM => /=; rewrite (leq_trans _ nk)//; near: n; exists m.
Unshelve. all: by end_near. Qed.

Lemma cvgNy_einfs u : u @ \oo --> -oo -> einfs u @ \oo --> -oo.
Proof.
move=> /cvgNy_limn_einf_sup[uoo _].
apply/cvg_closeP; split; [exact: is_cvg_einfs|rewrite closeE//].
by rewrite -limn_einf_lim.
Qed.

Lemma cvgNy_esups u : u @ \oo --> -oo -> esups u @ \oo --> -oo.
Proof.
move=> /cvgNy_limn_einf_sup[_ uoo]; apply/cvg_closeP.
by split; [exact: is_cvg_esups|rewrite closeE// -limn_esup_lim].
Qed.

Lemma cvgy_einfs u : u @ \oo --> +oo -> einfs u @ \oo --> +oo.
Proof.
move=> /cvgeN/cvgNy_esups/cvgeN; rewrite esupsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvgy_esups u : u @ \oo --> +oo -> esups u @ \oo --> +oo.
Proof.
move=> /cvgeN/cvgNy_einfs/cvgeN; rewrite einfsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvg_esups u l : u @ \oo --> l -> esups u @ \oo --> l.
Proof.
case: l => [l /fine_cvgP[u_fin_num] ul| |]; last 2 first.
  - exact: cvgy_esups.
  - exact: cvgNy_esups.
have [p _ pu] := u_fin_num; apply/cvg_ballP => _/posnumP[e].
have : EFin \o sups (fine \o u) @ \oo --> l%:E.
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

Lemma cvg_einfs u l : u @ \oo --> l -> einfs u @ \oo --> l.
Proof.
move=> /cvgeN/cvg_esups/cvgeN; rewrite oppeK esupsN.
by under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvg_limn_einf_sup u l : u @ \oo --> l ->
  (limn_einf u = l) * (limn_esup u = l).
Proof.
move=> ul; rewrite limn_esup_lim limn_einf_lim; split.
- by apply/cvg_lim => //; exact/cvg_einfs.
- by apply/cvg_lim => //; exact/cvg_esups.
Qed.

Lemma is_cvg_limn_einfE u : cvgn u -> limn_einf u = limn u.
Proof.
move=> /cvg_ex[l ul]; have [-> _] := cvg_limn_einf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

Lemma is_cvg_limn_esupE u : cvgn u -> limn_esup u = limn u.
Proof.
move=> /cvg_ex[l ul]; have [_ ->] := cvg_limn_einf_sup ul.
by move/cvg_lim : ul => ->.
Qed.

End lim_esup_inf.
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_einf_shift`")]
Notation lim_einf_shift := limn_einf_shift (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_esup_le_cvg`")]
Notation lim_esup_le_cvg := limn_esup_le_cvg (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_einfN`")]
Notation lim_einfN := limn_einfN (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_esupN`")]
Notation lim_esupN := limn_esupN (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `limn_einf_sup`")]
Notation lim_einf_sup := limn_einf_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `cvgNy_limn_einf_sup`")]
Notation cvgNy_lim_einf_sup := cvgNy_limn_einf_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `cvg_limn_einf_sup`")]
Notation cvg_lim_einf_sup := cvg_limn_einf_sup (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `is_cvg_limn_einfE`")]
Notation is_cvg_lim_einfE := is_cvg_limn_einfE (only parsing).
#[deprecated(since="mathcomp-analysis 0.6.6", note="renamed to `is_cvg_limn_esupE`")]
Notation is_cvg_lim_esupE := is_cvg_limn_esupE (only parsing).

Lemma geometric_le_lim {R : realType} (n : nat) (a x : R) :
  0 <= a -> 0 < x -> `|x| < 1 -> series (geometric a x) n <= a * (1 - x)^-1.
Proof.
move=> a0 x0 x1.
have /(@cvg_unique _ (@Rhausdorff R)) := @cvg_geometric_series _ a _ x1.
move/(_ _ (@is_cvg_geometric_series _ a _ x1)) => ->.
apply: nondecreasing_cvgn_le; last exact: is_cvg_geometric_series.
by apply: nondecreasing_series => ? _ /=; rewrite pmulr_lge0 // exprn_gt0.
Qed.

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
  elim: k => [|k /(ler_wpM2l (ge0 q))]; first by rewrite expr0 mul1r.
  rewrite mulrA -exprS; apply: le_trans.
  by rewrite (@ctrfq (y k.+1, y k)); split; exact: funS.
have /le_trans -> // : `| y n - y (n + m)| <=
    series (geometric (`|f base - base| * q%:num ^+ n) q%:num) m.
  elim: m => [|m ih].
    by rewrite geometric_seriesE ?lt_eqF//= addn0 subrr normr0 subrr mulr0 mul0r.
  rewrite (le_trans (ler_distD (y (n + m)%N) _ _))//.
  apply: (le_trans (lerD ih _)); first by rewrite distrC addnS; exact: f1.
  rewrite [_ * `|_|]mulrC exprD mulrA geometric_seriesE ?lt_eqF//=.
  pose q' := Itv01 [elaborate ge0 q] (ltW q1).
  rewrite -[q%:num]/(q'%:num) -!mulrA -mulrDr ler_pM// {}/q'/=.
  rewrite -!/(`1-_) -mulrDr exprSr onemM -addrA.
  rewrite -[in leRHS](mulrC _ `1-(_ ^+ m)) -onemMr onemK.
  by rewrite [in leRHS]mulrDl mulrAC mulrV ?mul1r// unitf_gt0// onem_gt0.
rewrite geometric_seriesE ?lt_eqF//= -[leRHS]mulr1 (ACl (1*4*2*3))/= -/C.
by rewrite ler_wpM2l// 1?mulr_ge0// lerBlDr lerDl.
Qed.

Lemma contraction_cvg : cvgn y.
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
rewrite // -ltr_pdivlMl //.
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
by rewrite ler_wiXn2l // ?ltW // leq_min Nn.
Unshelve. all: end_near. Qed.

Lemma contraction_cvg_fixed : closed U -> limn y = f (limn y).
Proof.
move=> clU; apply: cvg_lim => //.
apply/cvgrPdist_lt => _/posnumP[e]; near_simpl; apply: near_inftyS.
have [q_gt0 | | q0] := ltrgt0P q%:num.
- near=> n => /=; apply: (le_lt_trans (@ctrfq (_, _) _)) => //=.
  + split; last exact: funS.
    by apply: closed_cvg contraction_cvg => //; apply: nearW => ?; exact: funS.
  + rewrite -ltr_pdivlMl //; near: n; move/cvgrPdist_lt: contraction_cvg.
    by apply; rewrite mulr_gt0 // invr_gt0.
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

Section Baire.
Variable K : realType.

(* TODO: generalize to complete metric spaces  *)
Theorem Baire (U : completeNormedModType K) (F : (set U)^nat) :
  (forall i, open (F i) /\ dense (F i)) -> dense (\bigcap_i (F i)).
Proof.
move=> odF D Dy OpenD.
have /(_ D Dy OpenD)[a0 DF0a0] : dense (F 0%N) := proj2 (odF 0%N).
have {OpenD Dy} openIDF0 : open (D `&` F 0%N).
  by apply: openI => //; exact: (proj1 (odF 0%N)).
have /open_nbhs_nbhs/nbhs_closedballP[r0 Ball_a0] : open_nbhs a0 (D `&` F 0%N).
  by [].
pose P (m : nat) (arn : U * {posnum K}) (arm : U * {posnum K}) :=
  closed_ball arm.1 (arm.2%:num) `<=` (closed_ball arn.1 arn.2%:num)^° `&` F m
  /\ arm.2%:num < m.+1%:R^-1.
have Ar : forall na : nat * (U * {posnum K}), exists b : U * {posnum K},
    P na.1.+1 na.2 b.
  move=> [n [an rn]].
  have [ openFn denseFn] := odF n.+1.
  have [an1 B0Fn2an1] : exists x, ((closed_ball an rn%:num)^° `&` F n.+1) x.
    have [//|? ?] := @open_nbhs_closed_ball _ _ an rn%:num.
    by apply: denseFn => //; exists an.
  have openIB0Fn1 : open ((closed_ball an rn%:num)^° `&` F n.+1).
    by apply/openI => //; exact/open_interior.
  have /open_nbhs_nbhs/nbhs_closedballP[rn01 Ball_an1] :
    open_nbhs an1 ((closed_ball an rn%:num)^° `&` F n.+1) by [].
  have n31_gt0 : n.+3%:R^-1 > 0 :> K by [].
  have majr : minr (PosNum n31_gt0)%:num rn01%:num > 0 by exact/gt0/K.
  exists (an1, PosNum majr); split.
    apply/(subset_trans _ Ball_an1)/le_closed_ball => /=.
    by rewrite ge_min lexx orbT.
  rewrite (@le_lt_trans _ _ n.+3%:R^-1) //= ?ge_min ?lexx//.
  by rewrite ltf_pV2 // ?ltr_nat// posrE.
have [f Pf] := choice Ar.
pose fix ar n := if n is p.+1 then (f (p, ar p)) else (a0, r0).
pose a := fun n => (ar n).1.
pose r := fun n => (ar n).2.
have Suite_ball n m : (n <= m)%N ->
    closed_ball (a m) (r m)%:num `<=` closed_ball (a n) (r n)%:num.
  elim m=> [|k iHk]; first by rewrite leqn0 => /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP -> //|/iHk]; apply: subset_trans.
  have [+ _] : P k.+1 (a k, r k) (a k.+1, r k.+1) by apply: (Pf (k, ar k)).
  rewrite subsetI => -[+ _].
  by move/subset_trans; apply => //; exact: interior_subset.
have : cvg (a @ \oo).
  suff : cauchy (a @ \oo) by exact: cauchy_cvg.
  suff : cauchy_ex (a @ \oo) by exact: cauchy_exP.
  move=> e e0; rewrite /fmapE -ball_normE /ball_.
  have [n rne] : exists n, 2 * (r n)%:num < e.
    pose eps := e / 2.
    have [n n1e] : exists n, n.+1%:R^-1 < eps.
      exists `|ceil eps^-1|%N.
      rewrite -ltf_pV2 ?(posrE,divr_gt0)// invrK -addn1 natrD.
      rewrite natr_absz gtr0_norm.
        by rewrite (le_lt_trans (ceil_ge _)) // ltrDl.
      by rewrite -ceil_gt0 invr_gt0 divr_gt0.
    exists n.+1; rewrite -ltr_pdivlMl //.
    have /lt_trans : (r n.+1)%:num < n.+1%:R^-1.
      have [_ ] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply: (Pf (n, ar n)).
      by move/lt_le_trans => -> //; rewrite lef_pV2// // ?posrE// ler_nat.
    by apply; rewrite mulrC.
  exists (a n), n => // m nsupm.
  apply: (@lt_trans _ _ (2 * (r n)%:num) (`|a n - a m|) e) => //.
  have : (closed_ball (a n) (r n)%:num) (a m).
     have /(_ (a m)) := Suite_ball n m nsupm.
     by apply; exact: closed_ballxx.
  rewrite closed_ballE /closed_ball_ //= => /le_lt_trans; apply.
  by rewrite  -?ltr_pdivrMr ?mulfV ?ltr1n.
rewrite cvg_ex //= => -[l Hl]; exists l; split.
- have Hinter : (closed_ball a0 r0%:num) l.
    apply: (@closed_cvg _ _ \oo eventually_filter a) => //.
    + exact: closed_ball_closed.
    + apply: nearW; move=> m; have /(_ (a m)) := @Suite_ball 0%N _ (leq0n m).
      by apply; exact: closed_ballxx.
  suff : closed_ball a0 r0%:num `<=` D by move/(_ _ Hinter).
  by move: Ball_a0; rewrite closed_ballE //= subsetI; apply: proj1.
- move=> i _.
  have : closed_ball (a i) (r i)%:num l.
    rewrite -(@cvg_shiftn i _ a _) /= in Hl.
    apply: (@closed_cvg _ _ \oo eventually_filter (fun n => a (n + i)%N)) => //=.
    + exact: closed_ball_closed.
    + by apply: nearW; move=> n; exact/(Suite_ball _ _ (leq_addl n i))/closed_ballxx.
  move: i => [|n].
    by move: Ball_a0; rewrite subsetI => -[_ p] la0; move: (p _ la0).
  have [+ _] : P n.+1 (a n, r n) (a n.+1, r n.+1) by apply : (Pf (n , ar n)).
  by rewrite subsetI => -[_ p] lan1; move: (p l lan1).
Unshelve. all: by end_near. Qed.

End Baire.

(* TODO: generalize once PR#1107 is integrated *)
Definition bounded_fun_norm (K : realType) (V : normedModType K)
    (W : normedModType K) (f : V -> W) :=
  forall r, exists M, forall x, `|x| <= r -> `|f x| <= M.

Lemma bounded_landau (K : realType) (V : normedModType K)
    (W : normedModType K) (f : {linear V -> W}) :
  bounded_fun_norm f <-> ((f : V -> W) =O_ (0 : V) cst (1:K)).
Proof.
rewrite eqOP; split => [|Bf].
- move=> /(_ 1)[M bm].
  rewrite !nearE /=; exists M; rewrite num_real; split => // x Mx.
  apply/nbhs_normP; exists 1 => //= y /=.
  rewrite sub0r normrN/= normr1 mulr1 => y1.
  by apply/ltW; rewrite (le_lt_trans _ Mx)// bm// ltW.
- apply/bounded_funP; rewrite /bounded_near.
  near=> M.
  rewrite (_ : mkset _ = (fun x => `|f x| <= M * `|cst 1 x|)); last first.
    by rewrite funeqE => x; rewrite normr1 mulr1.
  by near: M.
Unshelve. all: by end_near. Qed.

(* TODO: to be changed once PR#1107 is integrated, and the following put in evt.v *)

(* Definition bounded_top (K: realType) (E : normedModType K) (B : set E) :=
forall (U : set E), nbhs 0 U ->
(exists (k:K), B `<=` (fun (x:E) => (k *: x) ) @` U).

Definition pointwise_bounded (K : realType) (V : normedModType K) (W : normedModType K)
(F : set (V -> W)) := bounded_top F {ptws V -> W}.

Definition uniform_bounded (K : realType) (V : normedModType K) (W : normedModType K)
 (F : set (V -> W)) := bounded_top F {uniform V -> W}.  *)

Definition pointwise_bounded (K : realType) (V : normedModType K) (W : normedModType K)
  (F : set (V -> W)) := forall x, exists M, forall f, F f -> `|f x| <= M.

Definition uniform_bounded (K : realType) (V : normedModType K) (W : normedModType K)
  (F : set (V -> W)) := forall r, exists M, forall f, F f -> forall x, `|x| <= r -> `|f x| <= M.

Section banach_steinhaus.
Variables (K : realType) (V : completeNormedModType K) (W : normedModType K).

Let pack_linear (f : V -> W) (lf : linear f) : {linear V -> W}
 := HB.pack f (GRing.isLinear.Build _ _ _ _ _ lf).
(* NB: pack linear used 5 times below, used inside a proof in derive.v,
fieldext.v, vector.v. *)

Theorem Banach_Steinhauss (F : set (V -> W)):
  (forall f, F f -> bounded_fun_norm f /\ linear f) ->
  pointwise_bounded F -> uniform_bounded F.
Proof.
move=> Propf BoundedF.
set O := fun n => \bigcup_(f in F) (normr \o f)@^-1` [set y | y > n%:R].
have O_open : forall n, open ( O n ).
  move=> n; apply: bigcup_open => i Fi.
  apply: (@open_comp _ _ (normr \o i) [set y | y > n%:R]); last first.
    exact: open_gt.
  move=> x Hx; apply: continuous_comp; last exact: norm_continuous.
  have Li : linear i := proj2 (Propf _ Fi).
  apply: (@linear_continuous K V W (pack_linear Li)) => /=.
  exact/(proj1 (bounded_landau (pack_linear Li)))/(proj1 (Propf _ Fi)).
set O_inf := \bigcap_i (O i).
have O_infempty : O_inf = set0.
  rewrite -subset0 => x.
  have [M FxM] := BoundedF x; rewrite /O_inf /O /=.
  move=> /(_ `|ceil M|%N Logic.I)[f Ff]; apply/negP; rewrite -leNgt.
  rewrite (le_trans (FxM _ Ff))// (le_trans (ceil_ge _))//.
  by have := lez_abs (ceil M); rewrite -(@ler_int K).
have ContraBaire : exists i, not (dense (O i)).
  have dOinf : ~ dense O_inf.
    rewrite /dense O_infempty ; apply /existsNP; exists setT; elim.
    - by move=> x; rewrite setI0.
    - by exists point.
    - exact: openT.
  have /contra_not/(_ dOinf) : (forall i, open (O i) /\ dense (O i)) -> dense (O_inf).
    exact: Baire.
  move=> /asboolPn /existsp_asboolPn[n /and_asboolP /nandP Hn].
  by exists n; case: Hn => /asboolPn.
have [n [x0 [r H]] k] :
    exists n x (r : {posnum K}), (ball x r%:num) `<=` (~` (O n)).
  move: ContraBaire =>
  [i /(denseNE) [ O0 [ [ x /open_nbhs_nbhs /nbhs_ballP [r r0 bxr]
   /((@subsetI_eq0 _ (ball x r) O0 (O i) (O i)))]]]] /(_ bxr) bxrOi.
  by exists i, x, (PosNum r0); apply/disjoints_subset/bxrOi.
exists ((n + n)%:R * k * 2 / r%:num)=> f Ff y Hx; move: (Propf f Ff) => [ _ linf].
case: (eqVneq y 0) => [-> | Zeroy].
  move: (linear0 (pack_linear linf)) => /= ->.
  by rewrite normr0 !mulr_ge0 // (le_trans _ Hx).
have majballi : forall f x, F f -> (ball x0 r%:num) x -> `|f x | <= n%:R.
  move=> g x Fg /(H x); rewrite leNgt.
  by rewrite /O setC_bigcup /= => /(_ _ Fg)/negP.
have majball : forall f x, F f -> (ball x0 r%:num) x -> `|f (x - x0)| <= n%:R + n%:R.
  move=> g x Fg; move: (Propf g Fg) => [Bg Lg].
  move: (linearB (pack_linear Lg)) => /= -> Ballx.
  apply/(le_trans (ler_normB _ _))/lerD; first exact: majballi.
  by apply: majballi => //; exact/ball_center.
have ballprop : ball x0 r%:num (2^-1 * (r%:num / `|y|) *: y  + x0).
  rewrite -ball_normE /ball_ /= opprD addrC subrK normrN normrZ.
  rewrite 2!normrM -2!mulrA (@normfV _ `|y|) normr_id mulVf ?mulr1 ?normr_eq0//.
  by rewrite gtr0_norm // gtr0_norm // gtr_pMl // invf_lt1 // ltr1n.
have := majball f (2^-1 * (r%:num / `|y|) *: y + x0) Ff ballprop.
rewrite -addrA addrN linf.
move: (linear0 (pack_linear linf)) => /= ->.
rewrite addr0 normrZ 2!normrM gtr0_norm // gtr0_norm //.
rewrite normfV normr_id -ler_pdivlMl //=; last first.
  by rewrite mulr_gt0 // mulr_gt0 // invr_gt0 normr_gt0.
move/le_trans; apply.
rewrite -natrD -!mulrA (mulrC (_%:R)) ler_pM //.
by rewrite invfM invrK mulrCA ler_pM2l // invf_div // ler_pM2r.
Qed.

End banach_steinhaus.
