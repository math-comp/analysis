(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
Require Import boolp classical_sets mathcomp_extra reals ereal posnum nngnum.
Require Import functions topology normedtype sequences cardinality csum.
From HB Require Import structures.

(******************************************************************************)
(*                            Measure Theory                                  *)
(*                                                                            *)
(* semiRingOfSetsType == the type of semirings of sets                        *)
(*     ringOfSetsType == the type of rings of sets                            *)
(*  algebraOfSetsType == the type of algebras of sets                         *)
(*     measurableType == the type of sigma-algebras                           *)
(*   sigma_finite A f == the measure f is sigma-finite on A : set T with      *)
(*                       T : ringOfSetsType.                                  *)
(*                                                                            *)
(* {additive_measure set T -> {ereal R}} == type of a function over sets of   *)
(*                    elements of type T where R is expected to be a          *)
(*                    numFieldType such that this function maps set0 to 0, is *)
(*                    non-negative over measurable sets, and is semi-additive *)
(* {measure set T -> {ereal R}} == type of a function over sets of elements   *)
(*                   of type T where R is expected to be a numFieldType such  *)
(*                   that this function maps set0 to 0, is non-negative over  *)
(*                   measurable sets and is semi-sigma-additive               *)
(*                                                                            *)
(*          seqDU F == the sequence F_0, F_1 \ F_0, F_2 \ (F_0 U F_1),...     *)
(*           seqD F == the sequence F_0, F_1 \ F_0, F_2 \ F_1,...             *)
(*                                                                            *)
(* Theorems: Boole_inequality, generalized_Boole_inequality                   *)
(*                                                                            *)
(* mu.-negligible A == A is mu negligible                                     *)
(* {ae mu, forall x, P x} == P holds almost everywhere for the measure mu     *)
(*                                                                            *)
(* {outer_measure set T -> {ereal R}} == type of an outer measure over sets   *)
(*                                 of elements of type T where R is expected  *)
(*                                 to be a numFieldType                       *)
(*                                                                            *)
(*    mu.-measurable X == X is Caratheodory measurable for the outer measure  *)
(*                        mu, i.e.,                                           *)
(*                        forall Y, mu X = mu (X `&` Y) + mu (X `&` ~` Y)     *)
(* measure_is_complete mu == the measure mu is complete                       *)
(*                                                                            *)
(*     measurable_fun D f == the function f with domain D is measurable       *)
(*                                                                            *)
(* Caratheodory theorem:                                                      *)
(* caratheodory_type mu := T, where mu : {outer_measure set T -> {ereal R}}   *)
(*                         it is a canonical mesurableType copy of T.         *)
(* caratheodory_measure mu == the restriction of the outer measure mu to the  *)
(*                         sigma algebra of Caratheodory measurable sets is a *)
(*                         measure                                            *)
(*                         Remark: sets that are negligible for               *)
(*                         caratheodory_measure are Caratheodory measurable   *)
(*                                                                            *)
(* Extension theorem:                                                         *)
(* measurable_cover X == the set of sequences F such that                     *)
(*                       - forall i, F i is measurable                        *)
(*                       - X `<=` \bigcup_i (F i)                             *)
(*          mu_ext mu == the extension of the measure mu, a measure over a    *)
(*                       ring of sets; it is an outer measure, declared as    *)
(*                       canonical (i.e., we have the notation                *)
(*                       [outer_measure of mu_ext mu])                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Reserved Notation "mu .-negligible" (at level 2, format "mu .-negligible").
Reserved Notation "{ 'ae' m , P }" (at level 0, format "{ 'ae'  m ,  P }").
Reserved Notation "mu .-measurable" (at level 2, format "mu .-measurable").

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* NB: in MathComp 1.13.0 *)

Lemma natr_absz (R : numDomainType) i : `|i|%:R = `|i|%:~R :> R.
Proof. by rewrite -abszE. Qed.

Lemma ge_pinfty (R : numDomainType) (x : itv_bound R) :
  (+oo <= x)%O = (x == +oo)%O.
Proof. by move: x => [[]|[]]. Qed.

Lemma le_ninfty (R : numDomainType) (x : itv_bound R) :
  (x <= -oo)%O = (x == -oo%O).
Proof. by case: x => // -[]. Qed.

Lemma gt_pinfty (R : numDomainType) (x : itv_bound R) : (+oo%O < x)%O = false.
Proof. by case: x. Qed.

Lemma lt_ninfty (R : numDomainType) (x : itv_bound R) : (x < -oo%O)%O = false.
Proof. by case: x => // -[]. Qed.
(* /NB: in MathComp 1.13.0 *)

(******************************************************************************)
(*                         lemmas waiting to be PRed                          *)
(******************************************************************************)

Section Elim3.

Variables (R1 R2 R3 R4 : Type) (K : R1 -> R2 -> R3 -> R4 -> Type).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).
Variables (id3 : R3) (op3 : R3 -> R3 -> R3).
Variables (id4 : R4) (op4 : R4 -> R4 -> R4).

Hypothesis Kid : K id1 id2 id3 id4.

Lemma big_rec4 I r (P : pred I) F1 F2 F3 F4
    (K_F : forall i y1 y2 y3 y4, P i -> K y1 y2 y3 y4 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2) (op3 (F3 i) y3) (op4 (F4 i) y4)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i)
    (\big[op4/id4]_(i <- r | P i) F4 i).
Proof. by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F. Qed.

Hypothesis Kop : forall x1 x2 x3 x4 y1 y2 y3 y4,
  K x1 x2 x3 x4 -> K y1 y2 y3 y4 ->
  K (op1 x1 y1) (op2 x2 y2) (op3 x3 y3) (op4 x4 y4).
Lemma big_ind4 I r (P : pred I) F1 F2 F3 F4
   (K_F : forall i, P i -> K (F1 i) (F2 i) (F3 i) (F4 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i)
    (\big[op4/id4]_(i <- r | P i) F4 i).
Proof. by apply: big_rec4 => i x1 x2 x3 x4 /K_F; apply: Kop. Qed.

End Elim3.

Arguments big_rec4 [R1 R2 R3 R4] K
  [id1 op1 id2 op2 id3 op3 id4 op4] _ [I r P F1 F2 F3 F4].
Arguments big_ind4 [R1 R2 R3 R4] K
  [id1 op1 id2 op2 id3 op3 id4 op4] _ _ [I r P F1 F2 F3 F4].

Coercion Choice.mixin : Choice.class_of >-> Choice.mixin_of.

(* TODO: move to classical_sets *)
Lemma memNset (T : Type) (A : set T) (u : T) : ~ A u -> u \in A = false.
Proof. by apply: contra_notF; rewrite inE. Qed.

Lemma setTP (T : Type) (A : set T) : A != setT <-> exists t, ~ A t.
Proof.
split => [/negP|[t]]; last by apply: contra_notP => /negP/negPn/eqP ->.
apply: contra_notP => /forallNP h.
by apply/eqP; rewrite predeqE => t; split => // _; apply: contrapT.
Qed.

Lemma in_set0 (T : Type) (x : T) : (x \in set0) = false.
Proof. by rewrite memNset. Qed.

Lemma in_setT T (x : T) : x \in setT.
Proof. by rewrite mem_set. Qed.

Lemma in_setC (T : Type) (x : T) (A : set T) : (x \in ~` A) = (x \notin A).
Proof. by apply/idP/idP; rewrite inE notin_set. Qed.

Lemma in_setI (T : Type) (x : T) (A B : set T) :
  (x \in A `&` B) = (x \in A) && (x \in B).
Proof. by apply/idP/andP; rewrite !inE. Qed.

Lemma in_setD (T : Type) (x : T) (A B : set T) :
  (x \in A `\` B) = (x \in A) && (x \notin B).
Proof. by apply/idP/andP; rewrite !inE notin_set. Qed.

Lemma in_setU (T : Type) (x : T) (A B : set T) :
  (x \in A `|` B) = (x \in A) || (x \in B).
Proof. by apply/idP/orP; rewrite !inE. Qed.

Arguments preimage : simpl never.

Lemma comp_preimage T1 T2 T3 (A : set T3) (g : T1 -> T2) (f : T2 -> T3) :
  (f \o g) @^-1` A = g @^-1` (f @^-1` A).
Proof. by []. Qed.

Lemma preimage_id T (A : set T) : id @^-1` A = A. Proof. by []. Qed.

Lemma preimage_comp T1 T2 rT (g : T1 -> rT) (f : T2 -> rT) (C : set T1) :
  f @^-1` [set g x | x in C] = [set x | f x \in g @` C].
Proof.
rewrite predeqE => t; split => /=.
  by move=> -[r Cr <-]; rewrite inE;  exists r.
by rewrite /preimage /= inE => -[r Cr <-]; exists r.
Qed.

Lemma empty_preimage_setI {aT rT : Type} (f : aT -> rT) (Y1 Y2 : set rT) :
  f @^-1` (Y1 `&` Y2) = set0 <-> f @^-1` Y1 `&` f @^-1` Y2 = set0.
Proof.
by split; apply: contraPP => /eqP/set0P/(nonempty_preimage_setI f _ _).2/set0P/eqP.
Qed.

Lemma empty_preimage {aT rT : Type} (f : aT -> rT) (Y : set rT) :
  Y = set0 -> f @^-1` Y = set0.
Proof.
move=> ->.
by rewrite preimage_set0.
Qed.

Lemma preimage_abse_pinfty (R : numDomainType) :
  @abse R @^-1` [set +oo%E] = [set -oo%E; +oo%E].
Proof.
by rewrite predeqE => y; split ; move: y => [y//| |]//=; [right | left | case].
Qed.

Lemma preimage_abse_ninfty (R : realDomainType) :
  @abse R @^-1` [set -oo%E] = set0.
Proof.
rewrite predeqE => t; split => //=; apply/eqP.
by rewrite gt_eqF// (lt_le_trans _ (abse_ge0 t))// lte_ninfty.
Qed.

(* TODO: PR along subset_set1? *)
Lemma subset_set2 T (A : set T) a b : A `<=` [set a; b] ->
  A = set0 \/ A = [set a] \/ A = [set b] \/ A = [set a; b].
Proof.
have [<-|ab Aab] := pselect (a = b).
  by rewrite setUid => Aa; have [|] := subset_set1 Aa; tauto.
have [Aa|Aa] := pselect (A `<=` [set a]).
  by rewrite orA; left; exact/subset_set1.
have [Ab|Ab] := pselect (A `<=` [set b]).
  have [A0|{}Ab] := subset_set1 Ab; first by left.
  by rewrite orA; right; left.
rewrite 2!orA; right; rewrite eqEsubset; split => //.
move/nonsubset : Ab => -[y [Ay yb]].
have <- : y = a by apply: contrapT => ya; move/Aab : Ay => [|].
move/nonsubset : Aa => -[z [Az za]].
have <- : z = b by apply: contrapT => zb; move/Aab : Az => [|].
by move=> _ [|] ->.
Qed.

(* TODO: remove when available in all the Coq versions supported by the CI
   (as of today, only in Coq 8.13) *)
Definition uncurry {A B C : Type} (f : A -> B -> C)
  (p : A * B) : C := match p with (x, y) => f x y end.

Definition bigcup2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0%N then A else if i == 1%N then B else set0.
Arguments bigcup2 T A B n /.

Lemma bigcup2E T (A B : set T) : \bigcup_i (bigcup2 A B) i = A `|` B.
Proof.
rewrite predeqE => t; split=> [|[At|Bt]]; [|by exists 0%N|by exists 1%N].
by case=> -[_ At|[_ Bt|//]]; [left|right].
Qed.

Lemma bigcup2inE T (A B : set T) : \bigcup_(i in `I_2) (bigcup2 A B) i = A `|` B.
Proof.
rewrite predeqE => t; split=> [|[At|Bt]]; [|by exists 0%N|by exists 1%N].
by case=> -[_ At|[_ Bt|//]]; [left|right].
Qed.

Definition bigcap2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0%N then A else if i == 1%N then B else setT.
Arguments bigcap2 T A B n /.

Lemma bigcap2E T (A B : set T) : \bigcap_i (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2E /bigcap2 /bigcup2.
by apply: eq_bigcupr => -[|[|[]]]//=; rewrite setCT.
Qed.

Lemma bigcap2inE T (A B : set T) : \bigcap_(i in `I_2) (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2inE /bigcap2 /bigcup2.
by apply: eq_bigcupr => // -[|[|[]]].
Qed.

Lemma trivIset_bigcup2 T (A B : set T) :
  (A `&` B = set0) = trivIset setT (bigcup2 A B).
Proof.
apply/propext; split=> [AB0|/trivIsetP/(_ 0%N 1%N Logic.I Logic.I erefl)//].
apply/trivIsetP => -[/=|]; rewrite /bigcup2 /=.
- by move=> [//|[_ _ _ //|j _ _ _]]; rewrite setI0.
- move=> [[j _ _|]|i j _ _ _]; [by rewrite setIC| |by rewrite set0I].
  by move=> [//|j _ _ _]; rewrite setI0.
Qed.

Lemma sub_bigcup T I (F : I -> set T) (D : set T) (P : set I) :
  (forall i, P i -> F i `<=` D) -> \bigcup_(i in P) F i `<=` D.
Proof. by move=> FD t [n Pn Fnt]; apply: (FD n). Qed.

(* TODO: move to reals.v *)
Lemma sup_gt (R : realType) (S : set R) (x : R) : S !=set0 ->
  (x < sup S -> exists2 y, S y & x < y)%R.
Proof.
move=> S0; rewrite not_exists2P => + g; apply/negP; rewrite -leNgt.
by apply sup_le_ub => // y Sy; move: (g y) => -[// | /negP]; rewrite leNgt.
Qed.

Lemma inf_lt (R : realType) (S : set R) (x : R) : S !=set0 ->
  (inf S < x -> exists2 y, S y & y < x)%R.
Proof.
move=> /nonemptyN S0; rewrite /inf ltr_oppl => /sup_gt => /(_ S0)[r [r' Sr']].
by move=> <-; rewrite ltr_oppr opprK => r'x; exists r'.
Qed.

Lemma ltr_opp (R : numDomainType) (r : R) : (0 < r)%R -> (- r < r)%R.
Proof. by move=> n0; rewrite -subr_lt0 -opprD oppr_lt0 addr_gt0. Qed.

Lemma ltr_add_invr (R : realType) (y x : R) :
  (y < x -> exists k, y + k.+1%:R^-1 < x)%R.
Proof.
move=> yx; exists `|floor (x - y)^-1|%N.
rewrite -ltr_subr_addl -{2}(invrK (x - y)%R) ltr_pinv ?inE.
- rewrite -addn1 natrD natr_absz ger0_norm; last first.
    by rewrite floor_ge0 invr_ge0 subr_ge0 ltW.
  by rewrite -RfloorE lt_succ_Rfloor.
- by rewrite ltr0n andbT unitfE pnatr_eq0.
- by rewrite invr_gt0 subr_gt0 yx andbT unitfE invr_eq0 gt_eqF// subr_gt0.
Qed.

(* TODO: move to ereal.v *)
Lemma hasNub_ereal_sup (R : realType) (A : set (\bar R)) : ~ has_ubound A ->
  A !=set0 -> ereal_sup A = +oo%E.
Proof.
move=> hasNubA A0.
apply/eqP; rewrite eq_le lee_pinfty /= leNgt.
apply: contra_notN hasNubA => Aoo.
by exists (ereal_sup A); exact: ereal_sup_ub.
Qed.

Lemma ereal_sup_EFin (R : realType) (A : set R) :
  has_ubound A -> A !=set0 -> ereal_sup (EFin @` A) = (sup A)%:E.
Proof.
move=> has_ubA A0; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: ub_ereal_sup => /= y [r Ar <-{y}]; rewrite lee_fin sup_ub.
set esup := ereal_sup _; have := lee_pinfty esup.
rewrite le_eqVlt => /predU1P[->|esupoo]; first by rewrite lee_pinfty.
have := lee_ninfty esup; rewrite le_eqVlt => /predU1P[/esym|ooesup].
  case: A0 => i Ai.
  by move=> /ereal_sup_ninfty /(_ i%:E) /(_ (ex_intro2 A _ i Ai erefl)).
have esup_fin_num : esup \is a fin_num.
  rewrite fin_numE -lee_ninfty_eq -ltNge ooesup /= -lee_pinfty_eq -ltNge.
  by rewrite esupoo.
rewrite -(@fineK _ esup) // lee_fin leNgt.
apply/negP => /(sup_gt A0)[r Ar]; apply/negP; rewrite -leNgt.
by rewrite -lee_fin fineK//; apply: ereal_sup_ub; exists r.
Qed.

Lemma ereal_inf_EFin (R : realType) (A : set R) :
  has_lbound A -> A !=set0 -> ereal_inf (EFin @` A) = (inf A)%:E.
Proof.
move=> has_lbA A0; rewrite /ereal_inf /inf EFinN; congr (- _)%E.
rewrite -ereal_sup_EFin; [|exact/has_lb_ubN|exact/nonemptyN].
by rewrite !image_comp.
Qed.

Lemma gt0_mulpinfty (R : realDomainType) (x : \bar R) : (0 < x -> +oo * x = +oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mule_pinfty_pinfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulpinfty (R : realDomainType) (x : \bar R) : (x < 0 -> +oo * x = -oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mule_pinfty_ninfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty ltr0_sg// mulN1e.
Qed.

Lemma gt0_mulninfty (R : realDomainType) (x : \bar R) : (0 < x -> -oo * x = -oo)%E.
Proof.
move: x => [x|_|//]; last by rewrite mule_ninfty_pinfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty gtr0_sg// mul1e.
Qed.

Lemma lt0_mulninfty (R : realDomainType) (x : \bar R) : (x < 0 -> -oo * x = +oo)%E.
Proof.
move: x => [x|//|_]; last by rewrite mule_ninfty_ninfty.
by rewrite lte_fin => x0; rewrite muleC mulrinfty ltr0_sg// mulN1e.
Qed.

(* NB: not used? *)
Lemma EFin_inj (R : numDomainType) : injective (@EFin R).
Proof. by move=> a b; case. Qed.

Lemma mask_second (T : Type) (b : T) a t :
  a :: t = mask (true :: false :: nseq (size t) true) [:: a, b & t].
Proof. by rewrite /= mask_true. Qed.

Lemma cons_head_beheadE {T : eqType} (s : seq T) def :
  s != [::] -> head def s :: behead s = s.
Proof. by case: s. Qed.


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

Section seqD.
Variable T : Type.
Implicit Types F : (set T) ^nat.

Definition seqD F := fun n => if n isn't n'.+1 then F O else F n `\` F n'.

Lemma seqDUE F : nondecreasing_seq F -> seqDU F = seqD F.
Proof.
move=> ndF; rewrite funeqE => -[|n] /=; first by rewrite /seqDU big_ord0 setD0.
rewrite /seqDU big_ord_recr /= setUC; congr (_ `\` _); apply/setUidPl.
by rewrite -bigcup_mkord => + [k /= kn]; exact/subsetPset/ndF/ltnW.
Qed.

Lemma trivIset_seqD F : nondecreasing_seq F -> trivIset setT (seqD F).
Proof. by move=> ndF; rewrite -seqDUE //; exact: trivIset_seqDU. Qed.

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

Definition setI_closed T (G : set (set T)) :=
  forall A B, G A -> G B -> G (A `&` B).

Definition fin_bigcap_closed T (G : set (set T)) :=
    forall I (D : set I) A_, finite_set D -> (forall i, D i -> G (A_ i)) ->
  G (\bigcap_(i in D) (A_ i)).

Definition finN0_bigcap_closed T (G : set (set T)) :=
    forall I (D : set I) A_, finite_set D -> D !=set0 ->
    (forall i, D i -> G (A_ i)) ->
  G (\bigcap_(i in D) (A_ i)).

Definition setU_closed T (G : set (set T)) :=
  forall A B, G A -> G B -> G (A `|` B).

Definition fin_bigcup_closed T (G : set (set T)) :=
    forall I (D : set I) A_, finite_set D -> (forall i, D i -> G (A_ i)) ->
  G (\bigcup_(i in D) (A_ i)).

Definition setC_closed T (G : set (set T)) := forall A, G A -> G (~` A).

Definition setD_closed T (G : set (set T)) :=
  forall A B, B `<=` A -> G A -> G B -> G (A `\` B).

Definition setDI_closed T (G : set (set T)) :=
  forall A B, G A -> G B -> G (A `\` B).

Definition ndseq_closed T (G : set (set T)) :=
  forall F, nondecreasing_seq F -> (forall i, G (F i)) -> G (\bigcup_i (F i)).

Definition trivIset_closed T (G : set (set T)) :=
  forall F : (set T)^nat, trivIset setT F -> (forall n, G (F n)) ->
                    G (\bigcup_k F k).

Definition fin_trivIset_closed T (G : set (set T)) :=
  forall I (D : set I) (F : I -> set T), finite_set D -> trivIset D F ->
   (forall i, D i -> G (F i)) -> G (\bigcup_(k in D) F k).

Definition are_measurable_sets T D (G : set (set T)) :=
  [/\ G set0, (forall A, G A -> G (D `\` A)) &
     (forall A : (set T)^nat, (forall n, G (A n)) -> G (\bigcup_k A k))].

(* TODO: duplicate of finite_II? *)
Lemma finite_set_II n : finite_set `I_n. Proof. by exists n. Qed.
Hint Resolve finite_set_II : core.

Section are_measurable_sets_lemmas.

Lemma bigcap_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A -> \bigcap_(i in A) F i = \big[setI/setT]_(i <- fset_set A) F i.
Proof.
by move=> *; apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_fset_set.
Qed.

Lemma fin_bigcup_closedP T (G : set (set T)) :
  (G set0 /\ setU_closed G) <-> fin_bigcup_closed G.
Proof.
split=> [[G0 GU] I D A DF GA|GU]; last first.
  have G0 : G set0 by have := GU void set0 point; rewrite bigcup0//; apply.
  by split=> // A B GA GB; rewrite -bigcup2inE; apply: GU => // -[|[|[]]].
elim/Pchoice: I => I in D DF A GA *; rewrite bigcup_fset_set// big_seq.
by elim/big_ind: _ => // i; rewrite in_fset_set// inE => /GA.
Qed.

Lemma finN0_bigcap_closedP T (G : set (set T)) :
  setI_closed G <-> finN0_bigcap_closed G.
Proof.
split=> [GI I D A DF [i Di] GA|GI A B GA GB]; last first.
  by rewrite -bigcap2inE; apply: GI => // [|[|[|[]]]]; first by exists 0%N.
elim/Pchoice: I => I in D DF i Di A GA *.
have finDDi : finite_set (D `\ i) by exact: finite_setD.
rewrite (bigcap_setD1 i)// bigcap_fset_set// big_seq.
elim/big_rec: _ => // [|j B]; first by rewrite setIT; apply: GA.
rewrite in_fset_set// inE => -[Dj /eqP nij] GAB.
by rewrite setICA; apply: GI => //; apply: GA.
Qed.

Lemma sedDI_closedP T (G : set (set T)) :
  setDI_closed G <-> (setI_closed G /\ setD_closed G).
Proof.
split=> [GDI|[GI GD]].
  by split=> A B => [|AB] => GA GB; rewrite -?setDD//; do ?apply: (GDI).
move=> A B GA GB; suff <- : A `\` (A `&` B) = A `\` B.
  by apply: GD => //; apply: GI.
by rewrite setDE setCI setIUr -setDE setDv set0U.
Qed.

Lemma are_measurable_sets_bigcap T (I : choiceType) (D : set T)
    (F : I -> set (set T)) (J : set I) :
  (forall n, J n -> are_measurable_sets D (F n)) ->
  are_measurable_sets D (\bigcap_(i in J) F i).
Proof.
move=> mG; split=> [i Ji|A AJ i Ji|H GH i Ji]; first by have [] := mG i.
- by have [_ mGiC _] := mG i Ji; exact/mGiC/AJ.
- by have [_ _ mGiU] := mG i Ji; apply mGiU => j; exact: GH.
Qed.

Lemma are_measurable_setsP T U (C : set (set T)) :
  (forall X, C X -> X `<=` U) ->
  are_measurable_sets U C <->
  [/\ C U, setD_closed C, ndseq_closed C & setI_closed C].
Proof.
move=> C_subU; split => [[C0 CD CU]|[DT DC DU DI]]; split.
- by rewrite -(setD0 U); apply: CD.
- move=> A B BA CA CB; rewrite (_ : A `\` B = U `\` ((U `\` A) `|` B)).
    by apply CD; rewrite -bigcup2E; apply: CU => -[|[|[|]]] //=; exact: CD.
  rewrite setDUr setDD [in RHS]setDE setIACA setIid -setDE setIidr//.
  by rewrite setDE; apply: subIset; left; apply: C_subU.
- by move=> F ndF DF; exact: CU.
- move=> A B DA DB; rewrite (_ : A `&` B = U `\` ((U `\` A) `|` (U `\` B))).
    by apply CD; rewrite -bigcup2E; apply: CU => -[|[|[|]]] //; exact: CD.
  rewrite setDUr !setDD setIACA setIid (@setIidr _ U)//.
  by apply: subIset; left; exact: C_subU.
- by rewrite -(setDv U); exact: DC.
- by move=> A CA; apply: DC => //; exact: C_subU.
- move=> F DF.
  rewrite [X in C X](_ : _ = \bigcup_i \big[setU/set0]_(j < i.+1) F j).
    apply: DU; first by move=> *; exact/subsetPset/subset_bigsetU.
    elim=> [|n ih]; first by rewrite big_ord_recr /= big_ord0 set0U; exact: DF.
    have CU : setU_closed C.
      move=> A B DA DB; rewrite (_ : A `|` B = U `\` ((U `\` A) `&` (U `\` B))).
        apply DC => //; last by apply: DI; apply: DC => //; exact: C_subU.
        by apply: subIset; left; apply: subIset; left.
      by rewrite setDIr// !setDD (setIidr (C_subU _ DA)) (setIidr (C_subU _ _)).
    by rewrite big_ord_recr; exact: CU.
  rewrite predeqE => x; split => [[n _ Fnx]|[n _]].
    by exists n => //; rewrite big_ord_recr /=; right.
  by rewrite -bigcup_mkord => -[m /=]; rewrite ltnS => _ Fmx; exists m.
Qed.

End are_measurable_sets_lemmas.

Definition gen_class T (G : set (set T)) (P : set (set T) -> Prop) :=
  \bigcap_(A in [set M | P M /\ G `<=` M]) A.

Lemma subset_gen_class T (G : set (set T)) P : G `<=` gen_class G P.
Proof. by move=> A GA C /= [PC]; apply. Qed.

Lemma gen_class_smallest T (G : set (set T)) (P : set (set T) -> Prop) C :
  G `<=` C -> P C -> gen_class G P `<=` C.
Proof. by move=> GC PC A; apply. Qed.


Reserved Notation "'s<|' D , G '|>'" (at level 40, G, D at next level).
Reserved Notation "'s<<' A '>>'".
Reserved Notation "'d<<' D '>>'".

Hint Extern 0 (is_true (0 <= `| _ |)%E) => solve [apply: abse_ge0] : core.

Section generated_sigma_algebra.
Variable T : Type.
Implicit Types M G : set (set T).

Inductive g_salgebra (D : set T) G : set (set T) :=
| g_salgebra_self : G `<=` s<| D, G |>
| g_salgebra_set0 : s<| D, G |> set0
| g_salgebra_setC : forall A, s<| D, G |> A -> s<| D, G |> (D `\` A)
| g_salgebra_bigcup : forall A : (set T)^nat, (forall i, s<| D, G |> (A i)) ->
    s<| D, G |> (\bigcup_i (A i))
where "'s<|' D , G '|>'" := (g_salgebra D G).

Lemma g_salgebraE D G : s<| D, G |> = gen_class G (are_measurable_sets D).
Proof.
rewrite predeqE => A; split.
  by elim=>
  [ {}A ? N [?] | {}A [[]]| {}A ? MA N [[? NC ?] ?] | {}A ? MA N [[? ? NI] ?]];
  [exact | by [] | by apply/NC; apply: MA | by apply NI => i; exact: (MA i)].
apply; split; [split|]; [exact: g_salgebra_set0 | exact: g_salgebra_setC |
  exact: g_salgebra_bigcup | by move=> B MB; apply g_salgebra_self].
Qed.

Lemma are_measurable_sets_g_salgebra D G : are_measurable_sets D (s<| D, G |>).
Proof. by rewrite g_salgebraE; apply: are_measurable_sets_bigcap => ? []. Qed.

Lemma g_salgebra_smallest D G M : G `<=` M -> are_measurable_sets D M ->
  s<| D, G |> `<=` M.
Proof. by move=> GM DM; rewrite g_salgebraE; apply: gen_class_smallest. Qed.

Lemma subset_g_salgebra D M G : M `<=` G -> s<| D, M |> `<=` s<| D, G |>.
Proof.
move=> MG; apply: g_salgebra_smallest.
  by move=> C AC; exact/g_salgebra_self/MG.
exact: are_measurable_sets_g_salgebra.
Qed.

End generated_sigma_algebra.
Notation "'s<|' D , G '|>'" := (g_salgebra D G).
Notation "'s<<' G '>>'" := (g_salgebra setT G).

Definition is_monotone_class {T} E (G : set (set T)) :=
  [/\ (forall A, G A -> A `<=` E), G E, setD_closed G & ndseq_closed G].

Lemma is_monotone_class_g_salgebra T (G : set (set T)) (D : set T) :
  (forall X, s<| D, G |> X -> X `<=` D) -> G D ->
  is_monotone_class D (s<| D, G |>).
Proof.
move=> sDGD GD; split; [by move=> *; exact: sDGD|exact: g_salgebra_self| |].
- move=> A B BA sCA sCB; rewrite (_ : _ `\` _ = D `\` ((D `\` A) `|` B)).
    apply: g_salgebra_setC.
    rewrite -bigcup2E; apply: g_salgebra_bigcup => -[|[|[|]]] //=.
    + exact: g_salgebra_setC.
    + exact: g_salgebra_set0.
    + by move=> ?; exact: g_salgebra_set0.
  rewrite setDUr setDD [in RHS]setDE setIACA setIid -setDE setIidr//.
  by rewrite setDE; apply: subIset; left; apply: sDGD.
- by move=> *; exact: g_salgebra_bigcup.
Qed.

Section smallest_monotone_classE.
Variables (T : Type) (G : set (set T)) (setIG : setI_closed G).
Variables (D : set T) (GD : G D).
Variables (H : set (set T)) (monoH : is_monotone_class D H) (GH : G `<=` H).

Lemma smallest_monotone_classE : (forall X, s<| D, G |> X -> X `<=` D) ->
  (forall E, is_monotone_class D E -> G `<=` E -> H `<=` E) ->
  H = s<| D, G |>.
Proof.
move=> sDGD smallestH; rewrite eqEsubset; split.
  apply: (smallestH _ _ (@g_salgebra_self _ D G)).
  exact: is_monotone_class_g_salgebra.
suff: setI_closed H.
  move=> IH; apply: g_salgebra_smallest => //.
  by apply/are_measurable_setsP; by case: monoH.
pose H_ A := [set X | H X /\ H (X `&` A)].
have setDH_ A : setD_closed (H_ A).
  move=> X Y XY [HX HXA] [HY HYA]; case: monoH => h _ setDH _; split.
    exact: setDH.
  rewrite (_ : _ `&` _ = (X `&` A) `\` (Y `&` A)); last first.
    rewrite predeqE => x; split=> [[[? ?] ?]|]; first by split => // -[].
    by move=> [[? ?] YAx]; split => //; split => //; apply: contra_not YAx.
  by apply setDH => //; exact: setSI.
have ndH_ A : ndseq_closed (H_ A).
  move=> F ndF H_AF; split.
    by case: monoH => h _ _; apply => // => n; have [] := H_AF n.
  rewrite setI_bigcupl; case: monoH => h _ _; apply => //.
    by move=> m n mn; apply/subsetPset; apply: setSI; apply/subsetPset/ndF.
  by move=> n; have [] := H_AF n.
have GGH_ X : G X -> G `<=` H_ X.
  by move=> *; split; [exact: GH | apply: GH; exact: setIG].
have GHH_ X : G X -> H `<=` H_ X.
  move=> CX; apply: smallestH; [split => //; last exact: GGH_|exact: GGH_].
  by move=> ? [? ?]; case: monoH => + _ _ _; exact.
have HGH_ X : H X -> G `<=` H_ X.
  by move=> *; split; [exact: GH|rewrite setIC; apply GHH_].
have HHH_ X : H X -> H `<=` H_ X.
  move=> HX; apply: (smallestH _ _ (HGH_ _ HX)); split=> //.
  - by move=> ? [? ?]; case: monoH => + _ _ _; exact.
  - exact: HGH_.
by move=> *; apply HHH_.
Qed.

End smallest_monotone_classE.

Section monotone_class_subset.
Variables (T : Type) (G : set (set T)) (setIG : setI_closed G).
Variables (D : set T) (GD : G D).
Variables (H : set (set T)) (monoH : is_monotone_class D H) (GH : G `<=` H).

Lemma monotone_class_subset : (forall X, (s<| D, G |>) X -> X `<=` D) ->
  s<| D, G |> `<=` H.
Proof.
move=> sDGD; set M := gen_class G (@is_monotone_class T D).
rewrite -(@smallest_monotone_classE _ _ setIG _ _ M) //.
- exact: gen_class_smallest.
- split => [A MA | E [monoE] | A B BA MA MB E [[EsubD ED setDE ndE] GE] |].
  + by case: monoH => + _ _ _; apply; exact: MA.
  + exact.
  + by apply setDE => //; [exact: MA|exact: MB].
  + by move=> F ndF MF E [[EsubD ED setDE ndE] CE]; apply ndE=> // n; exact: MF.
- exact: subset_gen_class.
- by move=> ? ? ?; exact: gen_class_smallest.
Qed.

End monotone_class_subset.

Section dynkin.
Variable T : Type.
Implicit Types G D : set (set T).

Definition dynkin G := [/\ G setT, setC_closed G & trivIset_closed G].

Lemma dynkinT G : dynkin G -> G setT. Proof. by case. Qed.

Lemma dynkinC G : dynkin G -> setC_closed G. Proof. by case. Qed.

Lemma dynkinU G : dynkin G -> (forall F : (set T)^nat, trivIset setT F ->
  (forall n, G (F n)) -> G (\bigcup_k F k)). Proof. by case. Qed.

Definition g_dynkin G := gen_class G dynkin.

End dynkin.
Notation "'d<<' D '>>'" := (g_dynkin D).

Section dynkin_lemmas.
Variable T : Type.
Implicit Types D G : set (set T).

Lemma dynkin_monotone G : dynkin G <-> is_monotone_class setT G.
Proof.
split => [[GT setCG trG]|[_ GT setDG ndG]]; split => //.
- move=> A B BA GA GB; rewrite setDE -(setCK (_ `&` _)) setCI; apply setCG.
  rewrite setCK -bigcup2E; apply: trG.
  + by rewrite -trivIset_bigcup2 setIC; apply subsets_disjoint.
  + by move=> [|[//|n]]; [exact: setCG|rewrite /bigcup2 -setCT; apply: setCG].
- move=> F ndF GF; rewrite eq_bigcup_seqD; apply trG.
    exact: trivIset_seqD.
  move=> [/=|n]; first exact: GF.
  rewrite /seqD setDE -(setCK (_ `&` _)) setCI; apply setCG.
  rewrite setCK -bigcup2E; apply trG.
  + rewrite -trivIset_bigcup2 setIC; apply subsets_disjoint.
    exact/subsetPset/ndF/ltnW.
  + move=> [|[|]]; rewrite /bigcup2 /=; [exact/setCG/GF|exact/GF|].
    by move=> _; rewrite -setCT; apply: setCG.
- by move=> A B; rewrite -setTD; apply: setDG.
- move=> F tF GF; pose A i := \big[setU/set0]_(k < i.+1) F k.
  rewrite (_ : bigcup _ _ = \bigcup_i A i); last first.
    rewrite predeqE => t; split => [[n _ Fn]|[n _]].
      by exists n => //; rewrite /A -bigcup_mkord; exists n=> //=; rewrite ltnS.
    by rewrite /A -bigcup_mkord => -[m /=]; rewrite ltnS => mn Fmt; exists m.
  apply ndG; first by move=> a b ab; exact/subsetPset/subset_bigsetU.
  elim=> /= => [|n ih].
    by rewrite /A big_ord_recr /= big_ord0 set0U; exact: GF.
  rewrite /A /= big_ord_recr /= -/(A n).
  rewrite (_ : _ `|` _ = ~` (~` A n `\` F n.+1)); last first.
    by rewrite setDE setCI !setCK.
  rewrite -setTD; apply setDG => //; apply setDG => //; last first.
    by rewrite -setTD; apply: setDG.
  apply/disjoints_subset; rewrite setIC.
  by apply: (@trivIset_bigsetUI _ predT) => //; rewrite /predT /= trueE.
Qed.

Lemma dynkin_g_dynkin G : dynkin (d<< G >>).
Proof.
split=> [D /= [] []//| | ].
- by move=> Y sGY D /= [dD GD]; exact/(dynkinC dD)/(sGY D).
- by move=> F tF gGF D /= [dD GD]; apply dD => // k; exact: gGF.
Qed.

Lemma are_measurable_sets_dynkin G : are_measurable_sets setT G -> dynkin G.
Proof.
case=> ? DC DU; split => [| |? ? ?]; last exact: DU.
- by rewrite -setC0 -setTD; exact: DC.
- by move=> A GA; rewrite -setTD; apply: DC.
Qed.

Lemma dynkin_setI_bigsetI G (F : (set T)^nat) : dynkin G -> setI_closed G ->
  (forall n, G (F n)) -> forall n, G (\big[setI/setT]_(i < n) F i).
Proof.
move=> dG GI GF; elim => [|n ih]; last by rewrite big_ord_recr /=; apply: GI.
by rewrite big_ord0; exact: (dynkinT dG).
Qed.

Lemma dynkin_setI_are_measurable_sets G : dynkin G -> setI_closed G ->
  are_measurable_sets setT G.
Proof.
move=> dG GI; split => [|//|F DF].
- by rewrite -setCT; exact/(dynkinC dG)/(dynkinT dG).
- by move=> A GA; rewrite setTD; exact: (dynkinC dG).
- rewrite seqDU_bigcup_eq; apply/(dynkinU dG) => //; first exact/trivIset_seqDU.
  move=> n; rewrite /seqDU setDE; apply GI => //.
  rewrite -bigcup_mkord setC_bigcup bigcap_mkord.
  by apply: (@dynkin_setI_bigsetI _ (fun x => ~` F x)) => // ?; exact/(dynkinC dG).
Qed.

Lemma setI_closed_gdynkin_salgebra G : setI_closed G -> d<< G >> = s<< G >>.
Proof.
move=> GI; rewrite eqEsubset; split.
  apply: (gen_class_smallest (@g_salgebra_self _ _ _)).
  by apply/are_measurable_sets_dynkin; exact/are_measurable_sets_g_salgebra.
pose delta (D : set T) := [set E | d<< G >> (E `&` D)].
have ddelta (D : set T) : d<< G >> D -> dynkin (delta D).
  move=> dGD; split; first by rewrite /delta /= setTI.
  - move=> E DE; rewrite /delta /=.
    have -> : (~` E) `&` D = ~` ((E `&` D) `|` (~` D)).
      by rewrite -[LHS]setU0 -(setICl D) -setIUl -setCI -{2}(setCK D) -setCU.
    have : d<< G >> ((E `&` D) `|` ~` D).
      rewrite -bigcup2E => S [dS GS]; apply (dynkinU dS).
        move=> [|[|i]] [|[|j]] => // _ _; rewrite /bigcup2 /=.
        + by rewrite -setIA setICr setI0 => /set0P; rewrite eqxx.
        + by rewrite setI0 => /set0P; rewrite eqxx.
        + by rewrite setICA setICl setI0 => /set0P; rewrite eqxx.
        + by rewrite setI0 => /set0P; rewrite eqxx.
        + by rewrite set0I => /set0P; rewrite eqxx.
        + by rewrite set0I => /set0P; rewrite eqxx.
        + by rewrite set0I => /set0P; rewrite eqxx.
      move=> [|[|n]] //; rewrite /bigcup2 /=; [exact: DE| |].
      + suff: d<< G >> (~` D) by exact.
        by move=> F [dF GF]; apply (dynkinC dF) => //; exact: dGD.
      + by rewrite -setCT; apply/(dynkinC dS)/(dynkinT dS).
    by move=> dGEDD S /= [+ GS] => dS; apply/(dynkinC dS); exact: dGEDD.
  - move=> F tF deltaDF; rewrite /delta /= => S /= [dS GS].
    rewrite setI_bigcupl; apply (dynkinU dS) => //.
      by under eq_fun do rewrite setIC; exact: trivIset_setI.
    by move=> n; exact: deltaDF.
have GdG : G `<=` d<< G >> by move=> ? ? ? [_]; apply.
have Gdelta A : G A -> G `<=` delta A.
  by move=> ? ? ?; rewrite /delta /= => ? [?]; apply; exact/GI.
have GdGdelta A : G A -> d<< G >> `<=` delta A.
  move=> ?; apply: gen_class_smallest => //; first exact: Gdelta.
  by apply/ddelta; exact: GdG.
have dGGI A B : d<< G >> A -> G B -> d<< G >> (A `&` B).
  by move=> ? ?; apply: GdGdelta.
have dGGdelta A : d<< G >> A -> G `<=` delta A.
  by move=> ? ? ?; rewrite /delta /= setIC; exact: dGGI.
have dGdGdelta A : d<< G >> A -> d<< G >> `<=` delta A.
  by move=> ?; exact: gen_class_smallest (dGGdelta _ _) (ddelta _ _).
have dGdGdG A B : d<< G >> A -> d<< G >> B -> d<< G >> (A `&` B).
  by move=> ? ?; exact: dGdGdelta.
apply: g_salgebra_smallest => //; apply: dynkin_setI_are_measurable_sets => //.
exact: dynkin_g_dynkin.
Qed.

End dynkin_lemmas.

HB.mixin Record isSemiRingOfSets T := {
  ptclass : Pointed.class_of T;
  measurable : set (set T) ;
  diff_fsets : set T -> set T -> {fset (set T)} ;
  measurable0 : measurable set0 ;
  measurableI : setI_closed measurable;
  measurable_diff_fsets : forall A B C, measurable A -> measurable B ->
    C \in diff_fsets A B -> measurable C ;
  (* we skip the hypos measurable A measurable B because we can define a *)
  (* default behavior (diff A B = [set A `\` B]) when A or B are not in  *)
  (* measurable *)
  diff_fsetsE : forall A B, (*measurable A -> measurable B -> *)
    A `\` B = \big[setU/set0]_(X <- enum_fset (diff_fsets A B)) X ;
  diff_fsets_disjoint : forall A B C D, (*measurable A -> measurable B ->*)
    C != D -> C \in diff_fsets A B -> D \in diff_fsets A B -> C `&` D = set0
}.

HB.structure Definition SemiRingOfSets := {T of isSemiRingOfSets T}.
Notation semiRingOfSetsType := SemiRingOfSets.type.

Canonical semiRingOfSets_eqType (T : semiRingOfSetsType) := EqType T ptclass.
Canonical semiRingOfSets_choiceType (T : semiRingOfSetsType) :=
  ChoiceType T ptclass.
Canonical semiRingOfSets_ptType (T : semiRingOfSetsType) :=
  PointedType T ptclass.

HB.mixin Record RingOfSets_from_semiRingOfSets T of isSemiRingOfSets T := {
  measurableU : forall A B : set T,
    measurable A -> measurable B -> measurable (A `|` B) }.

HB.structure Definition RingOfSets := {T of RingOfSets_from_semiRingOfSets T &}.
Notation ringOfSetsType := RingOfSets.type.

Canonical ringOfSets_eqType (T : ringOfSetsType) := EqType T ptclass.
Canonical ringOfSets_choiceType (T : ringOfSetsType) := ChoiceType T ptclass.
Canonical ringOfSets_ptType (T : ringOfSetsType) := PointedType T ptclass.

HB.mixin Record AlgebraOfSets_from_RingOfSets T of RingOfSets T := {
  measurableT : measurable (@setT T)
}.

HB.structure Definition AlgebraOfSets := {T of AlgebraOfSets_from_RingOfSets T &}.
Notation algebraOfSetsType := AlgebraOfSets.type.

Canonical algebraOfSets_eqType (T : algebraOfSetsType) := EqType T ptclass.
Canonical algebraOfSets_choiceType (T : algebraOfSetsType) :=
  ChoiceType T ptclass.
Canonical algebraOfSets_ptType (T : algebraOfSetsType) :=
  PointedType T ptclass.

HB.mixin Record Measurable_from_algebraOfSets T of AlgebraOfSets T := {
  measurable_bigcup : forall U : (set T)^nat, (forall i, measurable (U i)) ->
    measurable (\bigcup_i (U i))
}.

HB.structure Definition Measurable := {T of Measurable_from_algebraOfSets T &}.
Notation measurableType := Measurable.type.

Canonical measurable_eqType (T : measurableType) := EqType T ptclass.
Canonical measurable_choiceType (T : measurableType) := ChoiceType T ptclass.
Canonical measurable_ptType (T : measurableType) := PointedType T ptclass.

HB.factory Record isRingOfSets T := {
  ptclass : Pointed.class_of T;
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableU : setU_closed measurable;
  measurableD : setDI_closed measurable;
}.

HB.builders Context T of isRingOfSets T.
Implicit Types (A B C D : set T).

Lemma mI A B : measurable A -> measurable B -> measurable (A `&` B).
Proof. by move=> mA mB; rewrite -setDD; do ?apply: measurableD. Qed.

Definition d A B := [fset (A `\` B)%classic]%fset.

Lemma mD A B C : measurable A -> measurable B -> C \in d A B -> measurable C.
Proof. by move=> mA mB; rewrite inE => /eqP ->; apply: measurableD. Qed.

Lemma dE A B : A `\` B = \big[setU/set0]_(X <- d A B) X.
Proof. by rewrite big_seq_fset1. Qed.

Lemma d_disj A B C D : C != D -> C \in d A B -> D \in d A B -> C `&` D = set0.
Proof.
by move=> /= CS; rewrite !inE => CAB DAB; move: CS; rewrite CAB DAB eqxx.
Qed.

HB.instance Definition T_isSemiRingOfSets :=
  @isSemiRingOfSets.Build T ptclass measurable d measurable0 mI mD dE d_disj.

HB.instance Definition T_isRingOfSets :=
  RingOfSets_from_semiRingOfSets.Build T measurableU.

HB.end.

HB.factory Record isAlgebraOfSets T := {
  ptclass : Pointed.class_of T;
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableU : setU_closed measurable;
  measurableC : setC_closed measurable
}.

HB.builders Context T of isAlgebraOfSets T.

Lemma mD : setDI_closed measurable.
Proof.
move=> A B mA mB; rewrite setDE -[A]setCK -setCU.
by do ?[apply: measurableU | apply: measurableC].
Qed.

HB.instance Definition T_isRingOfSets := @isRingOfSets.Build T ptclass
  measurable measurable0 measurableU mD.

Lemma measurableT : measurable (@setT T).
Proof. by rewrite -setC0; apply: measurableC; exact: measurable0. Qed.

HB.instance Definition T_isAlgebraOfSets : AlgebraOfSets_from_RingOfSets T :=
  AlgebraOfSets_from_RingOfSets.Build T measurableT.

HB.end.

HB.factory Record isMeasurable T := {
  ptclass : Pointed.class_of T;
  measurable : set (set T) ;
  measurable0 : measurable set0 ;
  measurableC : forall A, measurable A -> measurable (~` A) ;
  measurable_bigcup : forall U : (set T)^nat, (forall i, measurable (U i)) ->
    measurable (\bigcup_i (U i))
}.

HB.builders Context T of isMeasurable T.

Obligation Tactic := idtac.

Lemma mU : setU_closed measurable.
Proof.
move=> A B mA mB; rewrite -bigcup2E.
by apply measurable_bigcup => -[//|[//|i]]; exact: measurable0.
Qed.

Lemma mC : setC_closed measurable. Proof. by move=> *; apply: measurableC. Qed.

HB.instance Definition T_isAlgebraOfSets :=
  @isAlgebraOfSets.Build T ptclass measurable measurable0 mU mC.

HB.instance Definition T_isMeasurable :=
  @Measurable_from_algebraOfSets.Build T measurable_bigcup.

HB.end.

Hint Extern 0 (measurable set0) => solve [apply: measurable0] : core.
Hint Extern 0 (measurable setT) => solve [apply: measurableT] : core.

Section ringofsets_lemmas.
Variables T : ringOfSetsType.
Implicit Types A B : set T.

Lemma bigsetU_measurable I r (P : pred I) (F : I -> set T) :
  (forall i, P i -> measurable (F i)) ->
  measurable (\big[setU/set0]_(i <- r | P i) F i).
Proof. by move=> mF; elim/big_ind : _ => //; exact: measurableU. Qed.

Lemma fin_bigcup_measurable I (D : set I) (F : I -> set T) :
    finite_set D ->
    (forall i, D i -> measurable (F i)) ->
  measurable (\bigcup_(i in D) F i).
Proof.
elim/Pchoice: I => I in D F * => Dfin Fm.
rewrite bigcup_fset_set// big_seq; apply: bigsetU_measurable => i.
by rewrite in_fset_set ?inE// => *; apply: Fm.
Qed.

Lemma measurableD : setDI_closed (@measurable T).
Proof.
move=> A B mA mB; rewrite diff_fsetsE big_seq.
by apply: bigsetU_measurable => /= i; exact: measurable_diff_fsets.
Qed.

End ringofsets_lemmas.

Section algebraofsets_lemmas.
Variables T : algebraOfSetsType.
Implicit Types A B : set T.

Lemma measurableC A : measurable A -> measurable (~` A).
Proof. by move=> mA; rewrite -setTD; exact: measurableD. Qed.

Lemma bigsetI_measurable I r (P : pred I) (F : I -> set T) :
  (forall i, P i -> measurable (F i)) ->
  measurable (\big[setI/setT]_(i <- r | P i) F i).
Proof.
move=> mF; rewrite -[X in measurable X]setCK setC_bigsetI; apply: measurableC.
by apply: bigsetU_measurable => i Pi; apply/measurableC/mF.
Qed.

Lemma fin_bigcap_measurable I (D : set I) (F : I -> set T) :
    finite_set D ->
    (forall i, D i -> measurable (F i)) ->
  measurable (\bigcap_(i in D) F i).
Proof.
elim/Pchoice: I => I in D F * => Dfin Fm.
rewrite bigcap_fset_set// big_seq; apply: bigsetI_measurable => i.
by rewrite in_fset_set ?inE// => *; apply: Fm.
Qed.

End algebraofsets_lemmas.

Section measurable_lemmas.
Variables T : measurableType.
Implicit Types A B : set T.

Lemma are_measurable_sets_measurable : are_measurable_sets setT (@measurable T).
Proof. by split=> // [A|]; [exact: measurableD|exact: measurable_bigcup]. Qed.

Lemma bigcup_measurable (F : (set T)^nat) (P : set nat) :
  (forall k, P k -> measurable (F k)) -> measurable (\bigcup_(i in P) F i).
Proof.
move=> PF; rewrite bigcup_mkcond; apply: measurable_bigcup => k.
by case: asboolP => // Pk; exact: PF.
Qed.

Lemma bigcap_measurable (F : (set T)^nat) (P : set nat) :
  (forall k, P k -> measurable (F k)) -> measurable (\bigcap_(i in P) F i).
Proof.
move=> PF; rewrite -[X in measurable X]setCK setC_bigcap; apply: measurableC.
by apply: bigcup_measurable => k Pk; exact/measurableC/PF.
Qed.

Lemma measurable_bigcap (F : (set T)^nat) :
  (forall i, measurable (F i)) -> measurable (\bigcap_i (F i)).
Proof. by move=> ?; apply: bigcap_measurable. Qed.

End measurable_lemmas.

Definition g_measurable {T} (G : set (set T)) := T.

Section g_salgebra_instance.
Variables (T : pointedType) (G : set (set T)).

Lemma g_salgebra_on_setC_setT (A : set T) : s<< G >> A -> s<< G >> (~` A).
Proof. by move=> sGA; rewrite -setTD; exact: g_salgebra_setC. Qed.

Canonical g_measurable_eqType := EqType (g_measurable G) (Equality.class T).
Canonical g_measurable_choiceType := ChoiceType (g_measurable G) (Choice.class T).
Canonical g_measurable_ptType := PointedType (g_measurable G) (Pointed.class T).
HB.instance Definition _ := @isMeasurable.Build (g_measurable G) (Pointed.class T)
  (g_salgebra setT G) (@g_salgebra_set0 _ setT G) (@g_salgebra_on_setC_setT)
  (@g_salgebra_bigcup _ setT G).

Definition g_measurableType := [the measurableType of g_measurable G].

End g_salgebra_instance.

Lemma measurable_g_measurableTypeE (T : pointedType) (G : set (set T)) :
  are_measurable_sets setT G -> @measurable (g_measurableType G) = G.
Proof.
move=> mM; rewrite eqEsubset; split; first exact: g_salgebra_smallest.
by move=> A MA; apply g_salgebra_self.
Qed.

Definition measurable_fun (T U : measurableType) (D : set T) (f : T -> U) :=
  forall Y, measurable Y -> measurable (D `&` f @^-1` Y).

(* TODO: move to measure.v *)
Section measurability.

Definition preimage_class (aT rT : Type) (D : set aT) (f : aT -> rT)
    (G : set (set rT)) : set (set aT) :=
  [set D `&` f @^-1` B | B in G].

(* f1 is measurable on the sigma-algebra generated by itself *)
Lemma preimage_class_measurable_fun (aT : pointedType) (rT : measurableType)
  (D : set aT) (f : aT -> rT) :
  @measurable_fun (g_measurableType (preimage_class D f measurable))
    rT D f.
Proof. by move=> A mA; apply: g_salgebra_self; exists A. Qed.

Lemma are_measurable_sets_preimage_class (aT rT : Type) (G : set (set rT))
    (D : set aT) (f : aT -> rT) :
  are_measurable_sets setT G -> are_measurable_sets D (preimage_class D f G).
Proof.
case=> h0 hC hU; split; first by exists set0 => //; rewrite preimage_set0 setI0.
- move=> A; rewrite /preimage_class /= => -[B mB <-{A}].
  exists (~` B); first by rewrite -setTD; exact: hC.
  rewrite predeqE => x; split=> [[Dx Bfx]|[Dx]]; first by split => // -[] _ /Bfx.
  by move=> /not_andP[].
- move=> F; rewrite /preimage_class /= => mF.
  have {}mF : forall n, exists x, G x /\ D `&` f @^-1` x = F n.
    by move=> n; have := mF n => -[B mB <-]; exists B.
  have [F' mF'] := @choice _ _ (fun x y => G y /\ D `&` f @^-1` y = F x) mF.
  exists (\bigcup_k (F' k)); first by apply: hU => n; exact: (mF' n).1.
  rewrite preimage_bigcup setI_bigcupr; apply eq_bigcupr => i _.
  exact: (mF' i).2.
Qed.

Definition image_class (aT rT : Type) (D : set aT) (f : aT -> rT)
    (G : set (set aT)) : set (set rT) :=
  [set B : set rT | G (D `&` f @^-1` B)].

Lemma are_measurable_sets_image_class (aT rT : Type) (D : set aT) (f : aT -> rT)
    (G : set (set aT)) :
  are_measurable_sets D G -> are_measurable_sets setT (image_class D f G).
Proof.
move=> [G0 GC GU]; split; rewrite /image_class.
- by rewrite /= preimage_set0 setI0.
- move=> A /= GfAD; rewrite setTD -preimage_setC -setDE.
  rewrite (_ : _ `\` _ = D `\` (D `&` f @^-1` A)); first exact: GC.
  rewrite predeqE => x; split=> [[Dx fAx]|[Dx fADx]].
    by split => // -[] _ /fAx.
  by split => //; exact: contra_not fADx.
- by move=> F /= mF; rewrite preimage_bigcup setI_bigcupr; exact: GU.
Qed.

(* TODO: rename? *)
Lemma transfer aT (rT : pointedType) (D : set aT) (f : aT -> rT) (G' : set (set rT)) :
  s<| D, preimage_class D f G' |> =
  preimage_class D f (@measurable (g_measurableType G')).
Proof.
rewrite eqEsubset; split.
  have mG : are_measurable_sets D
      (preimage_class D f (@measurable (g_measurableType G'))).
    exact/are_measurable_sets_preimage_class/are_measurable_sets_measurable.
  have subset_preimage : preimage_class D f G' `<=`
                         preimage_class D f (@measurable (g_measurableType G')).
    by move=> A [B CCB <-{A}]; exists B => //; apply g_salgebra_self.
  exact: g_salgebra_smallest.
have G'pre A' : G' A' -> (preimage_class D f G') (D `&` f @^-1` A').
  by move=> ?; exists A'.
pose I : set (set aT) := s<| D, preimage_class D f G' |>.
have G'sfun : G' `<=` image_class D f I.
  by move=> A' /G'pre[B G'B h]; apply: g_salgebra_self; exists B.
have sG'sfun : s<< G' >> `<=` image_class D f I.
  apply: g_salgebra_smallest => //; apply: are_measurable_sets_image_class.
  exact: are_measurable_sets_g_salgebra.
by move=> _ [B mB <-]; exact: sG'sfun.
Qed.

Lemma measurability (aT rT : measurableType) (D : set aT) (f : aT -> rT)
    (G' : set (set rT)) : measurable D ->
  @measurable rT = s<< G' >> -> preimage_class D f G' `<=` @measurable aT ->
  measurable_fun D f.
Proof.
move=> mD sG_rT fG_aT.
suff h : preimage_class D f (@measurable rT) `<=` @measurable aT.
  by move=> A mA; apply: h; exists A.
have -> : preimage_class D f (@measurable rT) =
         s<| D , (preimage_class D f G')|>.
  by rewrite [in LHS]sG_rT [in RHS]transfer.
apply: g_salgebra_smallest => //; split => //.
- by move=> A mA; exact: measurableD.
- by move=> F h; exact: measurable_bigcup.
Qed.

End measurability.

Local Open Scope ereal_scope.


Lemma fset_set_II n : fset_set `I_n = [fset val i | i in 'I_n ]%fset.
Proof.
apply/fsetP => i; rewrite /= ?inE in_fset_set//.
apply/idP/imfsetP; rewrite ?inE/=.
  by move=> lt_in; exists (Ordinal lt_in).
by move=> [j _ ->].
Qed.

Section additivity.
Variables (R : numFieldType) (T : semiRingOfSetsType) (mu : set T -> \bar R).

Definition semi_additive2 := forall A B, measurable A -> measurable B ->
  measurable (A `|` B) ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition semi_additive := forall A n,
 (forall i : nat, measurable (A i)) -> trivIset setT A ->
  measurable (\big[setU/set0]_(i < n) A i) ->
  mu (\big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (A i).

Definition semi_sigma_additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  measurable (\bigcup_n A n) ->
  (fun n => \sum_(i < n) mu (A i)) --> mu (\bigcup_n A n).

Definition additive2 := forall A B, measurable A -> measurable B ->
  A `&` B = set0 -> mu (A `|` B) = mu A + mu B.

Definition additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  forall n, mu (\big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (A i).

Definition sigma_additive :=
  forall A, (forall i : nat, measurable (A i)) -> trivIset setT A ->
  (fun n => \sum_(i < n) mu (A i)) --> mu (\bigcup_n A n).

Definition sub_additive := forall (A : set T) (A_ : nat -> set T) n,
 (forall i : nat, `I_n i -> measurable (A_ i)) -> measurable A ->
  A `<=` \big[setU/set0]_(i < n) A_ i ->
  mu A <= \sum_(i < n) mu (A_ i).

Definition sigma_sub_additive := forall (A : set T) (A_ : nat -> set T),
 (forall i : nat, measurable (A_ i)) -> measurable A ->
  A `<=` \bigcup_i A_ i ->
  mu A <= \sum_(i <oo) mu (A_ i).

Definition sigma_finite (A : set T) (mu : set T -> \bar R) :=
  exists2 F : (set T)^nat,  A = \bigcup_(i : nat) F i &
      forall i, measurable (F i) /\ mu (F i) < +oo.

Lemma semi_additiveW : mu set0 = 0 -> semi_additive -> semi_additive2.
Proof.
move=> mu0 amx A B mA mB + AB; rewrite -bigcup2inE bigcup_mkord.
move=> /(amx (bigcup2 A B))->.
- by rewrite !(big_ord_recl, big_ord0)/= adde0.
- by move=> [|[|[]]]//=.
- by move=> [|[|i]] [|[|j]]/= _ _; rewrite ?(AB, setI0, set0I, setIC) => -[].
Qed.

End additivity.

Section ring_additivity.
Variables (R : numFieldType) (T : ringOfSetsType) (mu : set T -> \bar R).

Lemma semi_additiveE : semi_additive mu = additive mu.
Proof.
rewrite propeqE; split=> [sa A mA tA n|+ A m mA tA UAm]; last by move->.
by rewrite sa //; exact: bigsetU_measurable.
Qed.

Lemma semi_additive2E : semi_additive2 mu = additive2 mu.
Proof.
rewrite propeqE; split=> [amu A B ? ? ?|amu A B ? ? _ ?]; last by rewrite amu.
by rewrite amu //; exact: measurableU.
Qed.

Lemma additive2P : mu set0 = 0 -> semi_additive mu <-> additive2 mu.
Proof.
move=> mu0; rewrite -semi_additive2E; split; first exact: semi_additiveW.
rewrite semi_additiveE semi_additive2E => muU A Am Atriv n.
elim: n => [|n IHn]; rewrite ?(big_ord_recr, big_ord0) ?mu0//=.
rewrite muU ?IHn//=; first by apply: bigsetU_measurable.
rewrite -bigcup_mkord -subset0 => x [[/= m + Amx] Anx].
by rewrite (Atriv m n) ?ltnn//=; exists x.
Qed.

End ring_additivity.

Lemma semi_sigma_additive_is_additive
  (R : realFieldType (*TODO: numFieldType if possible?*))
  (X : semiRingOfSetsType) (mu : set X -> \bar R) :
  mu set0 = 0 -> semi_sigma_additive mu -> semi_additive mu.
Proof.
move=> mu0 samu A n Am Atriv UAm.
have := samu (fun i => if (i < n)%N then A i else set0).
rewrite (bigcup_splitn n) bigcup0 ?setU0; last first.
  by move=> i _; rewrite -ltn_subRL subnn.
under eq_bigr do rewrite ltn_ord.
move=> /(_ _ _ UAm)/cvg_lim<-//; last 2 first.
- by move=> i; case: ifP.
- move=> i j _ _; do 2![case: ifP] => ? ?; do ?by rewrite (setI0, set0I) => -[].
  by move=> /Atriv; apply.
apply: lim_near_cst => //=; near=> i.
have /subnKC<- : (n <= i)%N by near: i; exists n.
rewrite big_split_ord/=; under eq_bigr do rewrite ltn_ord.
by rewrite [X in _ + X]big1 ?adde0// => ?; rewrite -ltn_subRL subnn.
Unshelve. all: by end_near. Qed.

Lemma semi_sigma_additiveE
  (R : numFieldType) (X : measurableType) (mu : set X -> \bar R) :
  semi_sigma_additive mu = sigma_additive mu.
Proof.
rewrite propeqE; split=> [amu A mA tA|amu A mA tA mbigcupA]; last exact: amu.
by apply: amu => //; exact: measurable_bigcup.
Qed.

Lemma sigma_additive_is_additive
  (R : realFieldType) (X : measurableType) (mu : set X -> \bar R) :
  mu set0 = 0 -> sigma_additive mu -> additive mu.
Proof.
move=> mu0; rewrite -semi_sigma_additiveE -semi_additiveE.
exact: semi_sigma_additive_is_additive.
Qed.

Notation "f \|_ D" := (restrict D f) : fun_scope.

Lemma fset_set_image (T1 T2 : choiceType) (D : set T1) (f : T1 -> T2) :
  finite_set D -> fset_set (f @` D) = (f @` (fset_set D))%fset.
Proof.
move=> Dfin; apply/fsetP => z; rewrite in_fset_set; last exact: finite_image.
apply/idP/idP => [|/imfsetP[r /=]].
  rewrite inE /= => -[x Dx <-{z}]; apply/imfsetP => /=; exists x => //.
  by rewrite in_fset_set ?inE/=.
by rewrite in_fset_set// inE => Dr ->; rewrite inE; exists r.
Qed.

Module AdditiveMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, 0 <= mu x ;
  _ : semi_additive mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation additive_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation AdditiveMeasure fA := (Pack (Phant _) fA).
Notation "{ 'additive_measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'additive_measure'  fUV }") : ring_scope.
Notation "[ 'additive_measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'additive_measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'additive_measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'additive_measure'  'of'  f ]") : form_scope.
End Exports.

End AdditiveMeasure.
Include AdditiveMeasure.Exports.

Section additive_measure_on_semiring_of_sets.
Variables (R : realFieldType) (T : semiRingOfSetsType)
  (mu : {additive_measure set T -> \bar R}).

Lemma measure0 : mu set0 = 0.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure0 : core.

Lemma measure_ge0 : forall x, 0 <= mu x.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_ge0 : core.

Lemma measure_semi_additive : semi_additive mu.
Proof. by case: mu => ? []. Qed.
Hint Resolve measure_semi_additive : core.

Lemma content_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D ->
    trivIset D F ->
    (forall i, D i -> measurable (F i)) ->
    measurable (\bigcup_(i in D) F i) ->
  mu (\bigcup_(i in D) F i) = \sum_(i <- fset_set D) mu (F i).
Proof.
move=> Dfin Ftriv Fm UFm; pose G (i : option I) : set T := oapp (F \|_ D) set0 i.
have UFG : \bigcup_(i in D) F i = \bigcup_(i in [set Some x | x in D]) G i.
  apply/predeqP => x; split=> [[i Di Fix]|[[]// _ [i Di [<- /=]]]].
    by exists (Some i) => //=; rewrite ?patchT ?inE//; exists i.
  by rewrite ?patchT ?inE// => Fix; exists i.
suff muG : mu (\bigcup_(i in some @` D) G i) = \sum_(i <- fset_set (some @` D)) mu (G i).
  transitivity (mu (\bigcup_(i in some @` D) G i)); first by rewrite UFG.
    rewrite muG fset_set_image// (big_imfset _ _ _ (in2W Some_inj))/=.
    by apply: eq_big_seq => X; rewrite in_fset_set// => XD; rewrite patchT.
have oDfin: finite_set (Some @` D) by exact: finite_image.
rewrite bigcup_fset_set//= !(big_nth None) !big_mkord.
set s : seq (option I) := fset_set (some @` D).
rewrite (@measure_semi_additive (fun i => G (nth None s i)))//.
- move=> i; case: (ltnP i (size s)) => [/(mem_nth None)|/(nth_default _)->//=].
  rewrite in_fset_set// inE/= => -[j Dj <-]//=.
  by rewrite patchT ?inE//; apply: Fm.
- move=> m n _ _.
  case: (ltnP m (size s)) => [lt_ms|/(nth_default _)->]; last first.
    by rewrite set0I => -[].
  case: (ltnP n (size s)) => [lt_ns|/(nth_default _)->]; last first.
    by rewrite setI0 => -[].
  have := mem_nth None lt_ns; have := mem_nth None lt_ms.
  rewrite !in_fset_set// !inE/= => -[i Di ieq]/= -[j Dj jeq].
  rewrite -ieq -jeq/= !patchT ?inE// => /(Ftriv _ _ Di Dj) eqij.
  by have := jeq; rewrite -eqij ieq => /uniqP; apply => //; rewrite fset_uniq.
- rewrite -(big_mkord predT (fun i => G (nth None s i))) -(big_nth None xpredT).
  by rewrite -bigcup_fset_set// -UFG.
Qed.

Lemma measure_semi_additive2 : semi_additive2 mu.
Proof. exact/semi_additiveW. Qed.
Hint Resolve measure_semi_additive2 : core.

End additive_measure_on_semiring_of_sets.

Hint Resolve measure0 measure_ge0 measure_semi_additive2
  measure_semi_additive : core.

Section additive_measure_on_ring_of_sets.
Variables (R : realFieldType) (T : ringOfSetsType)
  (mu : {additive_measure set T -> \bar R}).

Lemma measureU : additive2 mu.
Proof. by rewrite -semi_additive2E. Qed.

Lemma measure_bigsetU : additive mu.
Proof. by rewrite -semi_additiveE. Qed.

Lemma measure_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D ->
    trivIset D F ->
    (forall i, D i -> measurable (F i)) ->
  mu (\bigcup_(i in D) F i) = \sum_(i <- fset_set D) mu (F i).
Proof.
move=> Dfin Ftriv Fm; rewrite content_fin_bigcup//.
exact: fin_bigcup_measurable.
Qed.

End additive_measure_on_ring_of_sets.

Hint Resolve measureU measure_bigsetU : core.

Module Measure.

Section ClassDef.

Variables (R : numFieldType) (T : semiRingOfSetsType).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, 0 <= mu x ;
  _ : semi_sigma_additive mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation is_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation Measure fA := (Pack (Phant _) fA).
Notation "{ 'measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'measure'  fUV }") : ring_scope.
Notation "[ 'measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'measure'  'of'  f ]") : form_scope.
End Exports.

End Measure.
Include Measure.Exports.

Section measure_lemmas.
Variables (R : realFieldType) (T : semiRingOfSetsType).

Coercion measure_to_nadditive_measure (mu : set T -> \bar R) :
  is_measure mu -> additive_measure mu.
Proof.
by move=> [mu0 muge0 /(semi_sigma_additive_is_additive mu0)]; split.
Qed.

Variable mu : {measure set T -> \bar R}.

Lemma measure_semi_sigma_additive : semi_sigma_additive mu.
Proof. by case: mu => ? []. Qed.

End measure_lemmas.

Section measure_lemmas.
Variables (R : realFieldType) (T : measurableType).
Variable mu : {measure set T -> \bar R}.

Lemma measure_sigma_additive : sigma_additive mu.
Proof.
by rewrite -semi_sigma_additiveE //; apply: measure_semi_sigma_additive.
Qed.

End measure_lemmas.

Hint Extern 0 (_ set0 = 0) => solve [apply: measure0] : core.
Hint Extern 0 (sigma_additive _) =>
  solve [apply: measure_sigma_additive] : core.

Section measure_is_additive_measure.
Variables (R : realFieldType) (T : semiRingOfSetsType)
  (mu : {measure set T -> \bar R}).

Lemma measure_is_additive_measure : additive_measure mu.
Proof.
case: mu => f [f0 fg0 fsa]; split => //=.
exact/semi_sigma_additive_is_additive.
Qed.

Canonical measure_additive_measure :=
  AdditiveMeasure measure_is_additive_measure.

End measure_is_additive_measure.

Coercion measure_additive_measure : Measure.map >-> AdditiveMeasure.map.

Lemma set_fsetK (T : choiceType) (A : {fset T}) : fset_set [set` A] = A.
Proof.
apply/fsetP => x; rewrite in_fset_set//=.
by apply/idP/idP; rewrite ?inE.
Qed.

Lemma fset_set_inj {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B -> fset_set A = fset_set B -> A = B.
Proof. by move=> Afin Bfin /(congr1 pred_set); rewrite !fset_setK. Qed.

Lemma trivIset_setIr [T I : Type] [D : set I] [F : I -> set T] [X : set T] :
  trivIset D F -> trivIset D (fun i : I => F i `&` X).
Proof. by move=> Ftriv; under eq_fun do rewrite setIC; apply: trivIset_setI. Qed.

Hint Extern 0 (finite_set [set` _]) => solve [apply: finite_finpred] : core.

Lemma set_imfset (key : unit) [K T : choiceType] (f : T -> K) (p : finmempred T) :
  [set` imfset key f p] = f @` [set` p].
Proof.
apply/predeqP => x; split=> [/imfsetP[i ip -> /=]|]; first by exists i.
by move=> [i ip <-]; apply: in_imfset.
Qed.

Lemma eq_big_supp [R : eqType] [idx : R] [op : Monoid.law idx] [I : Type]
  [r : seq I] [P1 : pred I] (P2 : pred I) (F : I -> R) :
  {in [pred x | F x != idx], P1 =1 P2} ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Proof.
move=> P12; rewrite big_mkcond [RHS]big_mkcond; apply: eq_bigr => i _.
by case: (eqVneq (F i) idx) => [->|/P12->]; rewrite ?if_same.
Qed.

Lemma perm_big_supp_cond [R : eqType] [idx : R] [op : Monoid.com_law idx] [I : eqType]
  [r s : seq I] [P : pred I] (F : I -> R) :
  perm_eq [seq i <- r | P i && (F i != idx)] [seq i <- s | P i && (F i != idx)] ->
  \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- s| P i) F i.
Proof.
move=> prs; rewrite !(bigID [pred i | F i == idx] P F)/=.
rewrite big1 ?Monoid.mul1m; last by move=> i /andP[_ /eqP->].
rewrite [in RHS]big1 ?Monoid.mul1m; last by move=> i /andP[_ /eqP->].
by rewrite -[in LHS]big_filter -[in RHS]big_filter; apply perm_big.
Qed.

Lemma perm_big_supp [R : eqType] [idx : R] [op : Monoid.com_law idx] [I : eqType]
  [r s : seq I] [P : pred I] (F : I -> R) :
  perm_eq [seq i <- r | (F i != idx)] [seq i <- s | (F i != idx)] ->
  \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- s| P i) F i.
Proof.
by move=> ?; apply: perm_big_supp_cond; rewrite !filter_predI perm_filter.
Qed.

Lemma big_trivIset (I : choiceType) D T (R : Type) (idx : R)
   (op : Monoid.com_law idx) (A : I -> set T) (F : set T -> R) :
    finite_set D -> trivIset D A -> F set0 = idx ->
  \big[op/idx]_(i <- fset_set D) F (A i) =
  \big[op/idx]_(X <- (A @` fset_set D)%fset) F X.
Proof.
elim/Pchoice: R => R in idx op F *.
move=> Dfin Atriv F0; symmetry.
pose D' := [fset i in fset_set D | A i != set0]%fset.
transitivity (\big[op/idx]_(X <- (A @` D')%fset) F X).
  apply: perm_big_supp; rewrite uniq_perm ?filter_uniq//=.
  move=> X; rewrite !mem_filter; case: (eqVneq (F X) idx) => //= FXNidx.
  apply/imfsetP/imfsetP=> -[i/=]; rewrite ?(inE, in_fset_set)//=.
    move=> Di XAi; exists i; rewrite // !(inE, in_fset_set)//=.
    by rewrite (mem_set Di)/= -XAi; apply: contra_neq FXNidx => ->.
  by move=> /andP[Di AiN0] XAi; exists i; rewrite ?in_fset_set.
rewrite big_imfset//=; last first.
  move=> i j; rewrite !(inE, in_fset_set)//= => /andP[+ +] /andP[+ +].
  rewrite !inE => Di /set0P[x Aix] Dj _ Aij.
  by apply: (Atriv _ _ Di Dj); exists x; split=> //; rewrite -Aij.
apply: perm_big_supp; rewrite uniq_perm ?filter_uniq//= => i.
rewrite !mem_filter; case: (eqVneq (F (A i)) idx) => //= FAiidx.
rewrite !(in_fset_set, inE)//=; case: (boolP (i \in D)) => //= Di.
by apply: contra_neq FAiidx => ->.
Qed.

Section covering.
Context {T : Type}.
Implicit Type (C : forall I, set (set I)).
Implicit Type (P : forall I, set I -> set (I -> set T)).

Definition covered_by C P :=
  [set X : set T | exists I D A, [/\ C I D, P I D A & X = cover D A]].

Lemma covered_bySr C P P' : (forall I D A, P I D A -> P' I D A) ->
  covered_by C P `<=` covered_by C P'.
Proof.
by move=> PP' X [I [D [A [CX PX ->]]]]; exists I, D, A; split=> //; apply: PP'.
Qed.

Lemma covered_byP C P I D A : C I D -> P I D A -> covered_by C P (cover D A).
Proof. by move=> CID PIDA; exists I, D, A. Qed.

Lemma covered_by_finite P :
    (forall I (D : set I) A, (forall i, D i -> A i = set0) -> P I D A) ->
    (forall (I : pointedType) D A, finite_set D -> P I D A ->
       P nat `I_#|` fset_set D| (A \o nth point (fset_set D))) ->
  covered_by (@finite_set) P =
    [set X : set T | exists n A, [/\ P nat `I_n A & X = cover `I_n A]].
Proof.
move=> P0 Pc; apply/predeqP=> X; rewrite /covered_by /cover/=; split; last first.
  by move=> [n [A [Am ->]]]; exists nat, `I_n, A; split.
case; elim/Ppointed=> I [D [A [Dfin Am ->]]].
  exists 0%N, (fun=> set0); split; first by rewrite II0; apply: P0.
  by rewrite //= emptyE II0 !bigcup0.
exists #|`fset_set D|, (A \o nth point (fset_set D)).
split; first exact: Pc.
by rewrite bigcup_fset_set// (big_nth point) big_mkord bigcup_mkord.
Qed.

Lemma covered_by_countable P :
    (forall I (D : set I) A, (forall i, D i -> A i = set0) -> P I D A) ->
    (forall (I : pointedType) (D : set I) (A : I -> set T) (f : nat -> I),
       set_surj [set: nat] D f ->
       P I D A -> P nat [set: nat] (A \o f)) ->
  covered_by (@countable) P =
    [set X : set T | exists A, [/\ P nat [set: nat] A & X = cover [set: nat] A]].
Proof.
move=> P0 Pc; apply/predeqP=> X; rewrite /covered_by /cover/=; split; last first.
  by move=> [A [Am ->]]; exists nat, [set: nat], A; split.
case; elim/Ppointed=> I [D [A [Dcnt Am ->]]].
  exists (fun=> set0); split; first exact: P0.
  by rewrite emptyE bigcup_set0 bigcup0.
have /pfcard_geP[->|[f]] := Dcnt.
  exists (fun=> set0); split; first exact: P0.
  by rewrite !bigcup_set0 bigcup0.
pose g := [splitsurjfun of split f].
exists (A \o g); split=> /=; first exact: Pc Am.
apply/predeqP=> x; split=> [[i Di Aix]|[n _ Afnx]].
  by exists (g^-1%FUN i) => //=; rewrite invK// inE.
by exists (g n) => //; apply: funS.
Qed.

End covering.

Lemma bigcupDr {T I : Type} (F : I -> set T) (P : set I) (A : set T) : P !=set0 ->
  \bigcap_(i in P) (A `\` F i) = A `\` \bigcup_(i in P) F i.
Proof. by move=> PN0; rewrite setDE setC_bigcup -bigcapIr. Qed.

Lemma setD_bigcupl {T I : Type} (F : I -> set T) (P : set I) (A : set T) :
  \bigcup_(i in P) F i `\` A = \bigcup_(i in P) (F i `\` A).
Proof. by rewrite setDE setI_bigcupl; under eq_bigcupr do rewrite -setDE. Qed.

Lemma bigcup_bigcup {T I J : Type} (F : I -> J -> set T) (P : set I) (Q : set J) :
  \bigcup_(i in P) \bigcup_(j in Q) F i j =
  \bigcup_(k in P `*` Q) F k.1 k.2.
Proof.
apply/predeqP => x; split=> [[i Pi [j Pj Fijx]]|]; first by exists (i, j).
by move=> [[/= i j] [Pi Qj] Fijx]; exists i => //; exists j.
Qed.

Lemma bigcup_pred [T : finType] [U : Type] (P : {pred T}) (f : T -> set U) :
  \bigcup_(t in [set` P]) f t = \big[setU/set0]_(t in P) f t.
Proof.
apply/predeqP => u; split=> [[x Px fxu]|]; first by rewrite (bigD1 x)//; left.
move=> /mem_set; rewrite (@big_morph _ _ (fun X => u \in X) false orb).
- by rewrite big_has_cond => /hasP[x _ /andP[xP]]; rewrite inE => ufx; exists x.
- by move=> /= x y; apply/idP/orP; rewrite !inE.
- by rewrite in_set0.
Qed.


Module SetRing.
Definition type (T : Type) := T.

Section SetRing.
Context {T : semiRingOfSetsType}.

Let m : set (set T) := covered_by (@finite_set)
   (fun I D A => forall i : I, D i -> measurable (A i)).
Local Definition mdisj : set (set T) := covered_by (@finite_set)
   (fun I D A => trivIset D A /\ forall i : I, D i -> measurable (A i)).

Local Lemma mE : m = [set X : set T | exists n A,
  [/\ forall i, `I_n i -> measurable (A i) & X = cover `I_n A]].
Proof.
rewrite /m covered_by_finite// => I D A; first by move=> AP i /AP->.
move=> Dfin AP i Di; apply: AP; apply: (@set_mem _ D).
by rewrite -in_fset_set// mem_nth.
Qed.

Local Lemma mdisjE : mdisj = [set X : set T | exists n A,
  [/\ trivIset `I_n A /\ forall i, `I_n i -> measurable (A i) & X = cover `I_n A]].
Proof.
rewrite /mdisj covered_by_finite// => I D A => [A0|Dfin [Atriv Am]].
  split; last by move=> i /A0->.
  by move=> i j /A0-> /A0->; rewrite setI0; case.
have nthD x0 i : (i < #|` fset_set D|)%N -> D (nth x0 (fset_set D) i).
  by move=> ?; apply: (@set_mem _ D); rewrite -in_fset_set// mem_nth//.
split; last by move=> i /= ilt; apply: Am; apply: nthD.
by move=> i j ? ? /Atriv/uniqP; apply; rewrite ?fset_uniq//; apply: nthD.
Qed.

Local Lemma m0 : m set0.
Proof. by exists void, point, point; split=> //; rewrite /cover bigcup0. Qed.

Local Lemma mdisj0 : mdisj set0.
Proof. by exists void, point, point; do ?split; rewrite // /cover bigcup0. Qed.

Hint Resolve m0 mdisj0 : core.

Local Lemma mU : setU_closed m.
Proof.
move=> A B [aT [aX [A_ [aXfin A_m ->]]]] [bT [bX [B_ [bXfin B_m ->]]]].
exists (aT + bT)%type, ([set inl a | a in aX] `|` [set inr _ b | b in bX]).
exists (fun x => match x with inl a => A_ a | inr b => B_ b end).
split; first by rewrite finite_setU; split; apply: finite_image.
  by case=> [] c [] [c']// ? []<-//; [apply: A_m | apply: B_m].
apply/predeqP => x; split; last first.
  by move=> [[a|b] [] [c Xc// [<-]]]; [left|right]; exists c.
move=> [[a Xa Ax]|[b Xb Bx]]; first by exists (inl a) => //; left; exists a.
by exists (inr b) => //; right; exists b.
Qed.

Local Lemma mdisjm : mdisj `<=` m.
Proof. by apply: covered_bySr => I D X []. Qed.

Local Lemma mdisjW A : measurable A -> mdisj A.
Proof.
move=> mA; exists unit, [set tt], (fun=> A); do ?split => //.
  by move=> i j -> ->.
by rewrite /cover bigcup_set1.
Qed.

Local Lemma mW A : measurable A -> m A. Proof. by move=> /mdisjW/mdisjm. Qed.

Local Lemma m_bigcup : fin_bigcup_closed m.
Proof. by apply/fin_bigcup_closedP; split=> //; apply: mU. Qed.

Local Lemma mdisjI : setI_closed mdisj.
Proof.
move=> A B [aT [aX [A_ [aXF [Atr A_m] ->]]]] [bT [bX [B_ [bXF [Btr B_m] ->]]]].
rewrite setI_bigcupl; under eq_bigcupr do rewrite setI_bigcupr.
rewrite bigcup_bigcup; apply: covered_byP; first by apply: finite_setX.
split.
  move=> [a b] [a' b']/= [Xa Xb] [Xa' Xb']; rewrite setIACA.
  by move=> [x [Ax Bx]]; rewrite (Atr a a') 1?(Btr b b')//; exists x.
by move=> [i j] [Xi Xj]; apply: measurableI; [apply: A_m | apply: B_m].
Qed.

Local Lemma mdisj_bigcap : finN0_bigcap_closed mdisj.
Proof. exact/finN0_bigcap_closedP/mdisjI. Qed.

Local Lemma mDbigcup I (D : set I) (A : set T) (B : I -> set T) : finite_set D ->
  measurable A -> (forall i, D i -> measurable (B i)) ->
  mdisj (A `\` \bigcup_(i in D) B i).
Proof.
have [->|/set0P] := eqVneq D set0; first by rewrite bigcup0// setD0 => *; apply: mdisjW.
elim/Ppointed: I => I in D B * => Ffin DN0 Am Bm.
  by move: Ffin; rewrite emptyE=> -[].
rewrite -bigcupDr//; apply: mdisj_bigcap=> // i Di.
rewrite diff_fsetsE -bigcup_fset; apply: covered_byP => //.
split=> [X Y XD YD /set0P|X XD].
  by apply: contra_neq_eq => nXY; apply: (diff_fsets_disjoint A (B i)).
by apply: (measurable_diff_fsets A (B i)) => //; apply: Bm.
Qed.

Local Lemma mDI : setDI_closed m.
Proof.
move=> A B [aT [aX [A_ [aXfin A_m ->]]]] [bT [bX [B_ [bXfin B_m ->]]]].
rewrite setD_bigcupl; apply: m_bigcup => // a aXa.
by apply: mdisjm; apply: mDbigcup => //; apply: A_m.
Qed.

Notation rT := (type T).
Canonical g_measurable_eqType := EqType rT ptclass.
Canonical g_measurable_choiceType := ChoiceType rT ptclass.
Canonical g_measurable_ptType := PointedType rT ptclass.
#[export]
HB.instance Definition _ := isRingOfSets.Build rT ptclass m0 mU mDI.
Definition ring := [the ringOfSetsType of rT].

Lemma measurableW (A : set T) : measurable A -> measurable (A : set rT).
Proof. exact: mW. Qed.

Definition measurableE : measurable = m :> set (set rT).
Proof. by []. Qed.

Lemma measurable_disj (A : set rT) : measurable A -> mdisj (A : set T).
Proof.
rewrite measurableE mE /cover => -[n [{}A [/= Am ->]]].
elim: n => [|n IHn] in Am *; first by rewrite II0 bigcup_set0.
rewrite IIS setUC bigcup_setU1.
pose B := \bigcup_(i in `I_n) A i; pose C := A n `\` B.
suff: mdisj (C `|` B) by rewrite /C setUC setDE setUIr setUCr setIT setUC.
have: C `&` B = set0 by rewrite setDKI.
have: mdisj B by apply: IHn => i /ltnW/Am.
have: mdisj C by apply: mDbigcup=> //= *; apply: Am=> //=; apply/ltnW.
move=> [cT [cX [C_ [cXF [Ctr Cm] ->]]]] [bT [bX [B_ [bXfin [Btr Bm] ->]]]].
rewrite -subset0 => CB0.
exists (cT + bT)%type, ([set inl c | c in cX] `|` [set inr _ b | b in bX]).
exists (fun x => match x with inl c => C_ c | inr b => B_ b end).
split; first by rewrite finite_setU; split; apply: finite_image.
  split; last by case=> [] x [] [x']// ? []<-//; [apply: Cm | apply: Bm].
  move=> [] _ [] _ [] [//= u Xu [<-]] [] [//= v Xv [<-]].
  - by move=> /Ctr->//.
  - by move=> [x [Cx Bx]]; have []/= := CB0 x; split; [exists u|exists v].
  - by move=> [x [Bx Cx]]; have []/= := CB0 x; split; [exists v|exists u].
  - by move=> /Btr-> //.
apply/predeqP => i; split; last first.
  by move=> [[c|b] [] [x Xx// [<-]]]; [left|right]; exists x.
move=> [[c Xc Cx]|[b Xb Bx]]; first by exists (inl c) => //; left; exists c.
by exists (inr b) => //; right; exists b.
Qed.

Lemma fsets (A : set rT) : measurable A -> exists (B : {fset set T}),
  [/\ trivIset [set` B] id,
      (forall X : set T, X \in B -> measurable X) &
      A = cover [set` B] id ].
Proof.
move=> /measurable_disj; rewrite /cover mdisjE => -[k [B [[Btr Bm] ->]]].
exists [fset (B (val i)) | i in 'I_k]%fset; split.
- by move=> _ _ /= /imfsetP[i _ ->] /imfsetP[j _ ->] /Btr -> /=.
- by move=> _ /imfsetP[i _ ->]; apply: Bm => /=.
- by rewrite set_imfset bigcup_image//= /cover bigcup_mkord bigcup_pred.
Qed.

Definition decomp (A : set rT) : {fset set T} :=
  if pselect (measurable A) is left mA then projT1 (cid (fsets mA)) else fset0.

Lemma decomp_triv (A : set rT) : trivIset [set` decomp A] id.
Proof. by rewrite /decomp; case: pselect => // Am; case: cid => //= ? []. Qed.
Hint Resolve decomp_triv : core.

Lemma decomp_measurable (A : set rT) X : X \in decomp A -> measurable X.
Proof.
by rewrite /decomp; case: pselect => // Am; case: cid => //= ? [_ + _]; apply.
Qed.

Lemma cover_decomp (A : set rT) : measurable A -> cover [set` decomp A] id = A.
Proof. by rewrite /decomp; case: pselect => // Am; case: cid => //= ? []. Qed.

Context {R : realFieldType}.

Definition measure (mu : set T -> \bar R) (A : set rT) : \bar R :=
  \sum_(X <- decomp A) mu X.

Section additive_measure.
Context (mu : {additive_measure set T -> \bar R}).
Local Notation Rmu := (measure mu).
Arguments big_trivIset {I D T R idx op} A F.

Lemma Rmu_fin_bigcup (I : choiceType) (D : set I) (F : I -> set T) :
    finite_set D -> trivIset D F -> (forall i, D i -> measurable (F i)) ->
  Rmu (\bigcup_(i in D) F i) = \sum_(i <- fset_set D) mu (F i).
Proof.
move=> Dfin Ftriv Fm; rewrite /measure.
have: measurable (\bigcup_(i in D) F i : set rT).
  rewrite bigcup_fset_set// big_seq.
  apply: bigsetU_measurable => i; rewrite in_fset_set// inE => Di.
  exact/measurableW/Fm.
rewrite /decomp; case: pselect => // UFm _; case: cid => /= E [Etriv Em].
rewrite /cover/= bigcup_fset.
have [->|/set0P[i0 Di0]] := eqVneq D set0.
  rewrite bigcup_set0 fset_set0 big_seq_fset0 -bigcup_fset.
  by move=> /esym/bigcup0P/= E0; rewrite big_seq big1 => //= X /E0->.
move=> FE.
transitivity (\sum_(X <- E) \sum_(i <- fset_set D) mu (X `&` F i)).
  apply: eq_big_seq => /= X XE.
  have Xeq : X = \bigcup_(i in D) (X `&` F i).
    by rewrite -setI_bigcupr setIidl// FE -bigcup_set; apply: bigcup_sup.
  rewrite -content_fin_bigcup// -?Xeq//; last exact: Em.
    exact: trivIset_setI.
  by move=> i Di; apply: measurableI; [apply: Em | apply: Fm].
rewrite exchange_big; apply: eq_big_seq => i; rewrite in_fset_set ?inE//= => Di.
have Feq : F i = \bigcup_(X in [set` E]) (X `&` F i).
  by rewrite -setI_bigcupl setIidr// bigcup_fset -FE; apply: bigcup_sup.
rewrite -[E]set_fsetK -content_fin_bigcup -?Feq//; last exact: Fm.
  exact: trivIset_setIr.
by move=> X /= XE; apply: measurableI; [apply: Em | apply: Fm].
Qed.

Lemma RmuE (A : set T) : measurable A -> Rmu A = mu A.
Proof.
move=> Am; rewrite -[A in LHS](@bigcup_set1 _ unit _ tt).
by rewrite Rmu_fin_bigcup// ?fset_set1// ?big_seq_fset1// => -[].
Qed.

Lemma Rmu0 : Rmu set0 = 0.
Proof.
rewrite -(bigcup_set0 (fun _ : void => set0)).
by rewrite Rmu_fin_bigcup// fset_set0 big_seq_fset0.
Qed.

Lemma Rmu_ge0 A : Rmu A >= 0.
Proof. by rewrite sume_ge0//= => *; rewrite ?measure_ge0. Qed.

Lemma Rmu_additive : semi_additive Rmu.
Proof.
apply/(additive2P Rmu0) => // A B.
move=> /fsets[/= {}A [Atriv Am ->]] /fsets[/= {}B [Btriv Bm ->]].
rewrite -subset0 => coverAB0.
rewrite -bigcup_setU !Rmu_fin_bigcup//=.
- rewrite fset_setU// !set_fsetK -big_cat/=.
  have muNN0 (X : set T) : ~~ (X != set0) -> mu X = 0 by move=> /negPn/eqP->.
  rewrite -!(big_rmcond _ _ muNN0) -big_filter -[RHS]big_filter.
  apply: perm_big; rewrite uniq_perm//.
  + by rewrite ?filter_uniq ?fset_uniq.
  + rewrite filter_cat cat_uniq ?filter_uniq ?fset_uniq ?andbT//=.
    apply/hasPn => X; rewrite mem_filter => /andP[/set0P[x Xx] XB].
    apply: contraTN isT; rewrite inE mem_filter => /andP[_ XA].
    by have [] := coverAB0 x; split; exists X.
  + by move=> X; rewrite !mem_filter inE mem_cat.
- by rewrite finite_setU.
- move=> X Y [] ABX [] ABY; do ?by [apply: Atriv|apply: Btriv].
    by move=> [u [Xu Yu]]; have []/= := coverAB0 u; split; [exists X|exists Y].
  by move=> [u [Xu Yu]]; have []/= := coverAB0 u; split; [exists Y|exists X].
- by move=> X [/Am|/Bm].
Qed.

Lemma Rmu_additive_measure : additive_measure Rmu.
Proof. by split; [apply: Rmu0|apply: Rmu_ge0|apply: Rmu_additive]. Qed.

Canonical measure_additive_measure :=
  AdditiveMeasure Rmu_additive_measure.

End additive_measure.

Section sigma_sub_additive_measure.
Context (mu : set T -> \bar R).
Local Notation Rmu := (measure mu).

Lemma sigma_sub_additive_measure :
  sigma_sub_additive mu -> sigma_sub_additive Rmu.
Proof.
move=> /(_ _) /= muS /= D A Am Dm Dsub; rewrite /Rmu.

Admitted.

End sigma_sub_additive_measure.

End SetRing.
Module Exports.
Canonical g_measurable_eqType.
Canonical g_measurable_choiceType.
Canonical g_measurable_ptType.
Canonical measure_additive_measure.
HB.reexport.
End Exports.
End SetRing.
Export SetRing.Exports.

Lemma le_measure (R : realFieldType) (T : semiRingOfSetsType)
    (mu : {additive_measure set T -> \bar R}) :
  {in measurable &, {homo mu : A B / A `<=` B >-> (A <= B)%E}}.
Proof.
move=> A B; rewrite ?inE => mA mB AB; have [|muBfin] := leP +oo%E (mu B).
  by rewrite lee_pinfty_eq => /eqP ->; rewrite lee_pinfty.
rewrite -[X in _ <= X]SetRing.RmuE// -[B](setDUK AB) measureU/= ?setDIK//.
- rewrite SetRing.RmuE ?lee_addl// ?measure_ge0//.
- exact: SetRing.measurableW.
- by apply: measurableD; exact: SetRing.measurableW.
Qed.

Lemma measureIl (R : realFieldType) (T : semiRingOfSetsType)
    (mu : {additive_measure set T -> \bar R}) (A B : set T) :
  measurable A -> measurable B -> (mu (A `&` B) <= mu A)%E.
Proof. by move=> mA mB; rewrite le_measure ?inE//; apply: measurableI. Qed.

Lemma measureIr (R : realFieldType) (T : semiRingOfSetsType)
    (mu : {additive_measure set T -> \bar R}) (A B : set T) :
  measurable A -> measurable B -> (mu (A `&` B) <= mu B)%E.
Proof. by move=> mA mB; rewrite le_measure ?inE//; apply: measurableI. Qed.

Lemma subset_measure0 (T : semiRingOfSetsType) (R : realType)
  (mu : {additive_measure set T -> \bar R}) (A B : set T) :
  measurable A -> measurable B -> A `<=` B ->
  mu B = 0%E -> mu A = 0%E.
Proof.
move=> mA mB AB B0; apply/eqP; rewrite eq_le measure_ge0// ?andbT -?B0.
by apply: le_measure; rewrite ?inE.
Qed.

Section measureD.
Variables (R : realFieldType) (T : ringOfSetsType).
Variable mu : {measure set T -> \bar R}.

Lemma measureDI A B : measurable A -> measurable B ->
  mu A = mu (A `\` B) + mu (A `&` B).
Proof.
move=> mA mB; rewrite -measure_semi_additive2.
- by rewrite -setDDr setDv setD0.
- exact: measurableD.
- exact: measurableI.
- by apply: measurableU; [exact: measurableD |exact: measurableI].
- by rewrite setDE setIACA setICl setI0.
Qed.

Lemma measureD A B : measurable A -> measurable B ->
  mu A < +oo -> mu (A `\` B) = mu A - mu (A `&` B).
Proof.
move=> mA mB mAoo.
rewrite (measureDI mA mB) addeK// fin_numE 1?gt_eqF 1?lt_eqF//.
- rewrite (le_lt_trans _ mAoo)// le_measure // ?inE//.
  + exact: measurableI.
- by rewrite (lt_le_trans _ (measure_ge0 _ _))// ?lte_ninfty.
Qed.

End measureD.

Lemma measureUfinr (T : ringOfSetsType) (R : realFieldType) (A B : set T)
   (mu : {measure set T -> \bar R}):
    measurable A -> measurable B -> (mu B < +oo)%E ->
  mu (A `|` B) = (mu A + mu B - mu (A `&` B))%E.
Proof.
move=> Am Bm mBfin; rewrite -[B in LHS](setDUK (@subIsetl _ _ A)) setUA.
rewrite [A `|` _]setUidl; last exact: subIsetr.
rewrite measureU//=; do ?by apply:measurableD; do ?apply: measurableI.
  rewrite measureD//; do ?exact: measurableI.
  by rewrite addeA setIA setIid setIC.
by rewrite setDE setCI setIUr -!setDE setDv set0U setDIK.
Qed.

Lemma measureUfinl (T : ringOfSetsType) (R : realFieldType) (A B : set T)
   (mu : {measure set T -> \bar R}):
    measurable A -> measurable B -> (mu A < +oo)%E ->
  mu (A `|` B) = (mu A + mu B - mu (A `&` B))%E.
Proof. by move=> *; rewrite setUC measureUfinr// setIC [(mu B + _)%E]addeC. Qed.

Lemma oppe_eq0 (R : numDomainType) (x : \bar R) : (- x == 0)%E = (x == 0)%E.
Proof. by rewrite -(can_eq oppeK) oppe0. Qed.

Lemma measure_le0  (T : ringOfSetsType) (R : realFieldType)
    (mu : {additive_measure set T -> \bar R}) (A : set T) :
    measurable A -> (mu A <= 0)%E = (mu A == 0)%E.
Proof. by case: ltgtP (measure_ge0 mu A). Qed.

Lemma null_set_setU (R : realFieldType) (T : ringOfSetsType)
  (mu : {measure set T -> \bar R}) (A B : set T) :
  measurable A -> measurable B -> mu A = 0%E -> mu B = 0%E -> mu (A `|` B) = 0%E.
Proof.
move=> mA mB A0 B0; rewrite measureUfinl ?A0 ?lte_pinfty//= ?B0 ?add0e.
apply/eqP; rewrite oppe_eq0 -measure_le0/=; do ?exact: measurableI.
by rewrite -A0 measureIl.
Qed.

(* 401,p.43 measure is continuous from below *)
Lemma cvg_mu_inc (R : realFieldType) (T : ringOfSetsType)
  (mu : {measure set T -> \bar R}) (F : (set T) ^nat) :
  (forall i, measurable (F i)) -> measurable (\bigcup_n F n) ->
  nondecreasing_seq F ->
  mu \o F --> mu (\bigcup_n F n).
Proof.
move=> mF mbigcupF ndF.
have Binter : trivIset setT (seqD F) := trivIset_seqD ndF.
have FBE : forall n, F n.+1 = F n `|` seqD F n.+1 := setU_seqD ndF.
have FE n : F n = \big[setU/set0]_(i < n.+1) (seqD F) i := eq_bigsetU_seqD n ndF.
rewrite eq_bigcup_seqD.
have mB : forall i, measurable (seqD F i) by elim=> * //=; apply: measurableD.
apply: cvg_trans (measure_semi_sigma_additive mB Binter _); last first.
  by rewrite -eq_bigcup_seqD.
apply: (@cvg_trans _ [filter of (fun n => \sum_(i < n.+1) mu (seqD F i))]).
  rewrite [X in _ --> X](_ : _ = mu \o F) // funeqE => n.
  by rewrite -measure_semi_additive // -?FE// => -[|k].
by move=> S [n _] nS; exists n => // m nm; apply/(nS m.+1)/(leq_trans nm).
Qed.

Section boole_inequality.
Variables (R : realFieldType) (T : semiRingOfSetsType).
Variables (mu : {additive_measure set T -> \bar R}).

Theorem semi_Boole_inequality : sub_additive mu.
Proof.
move=> X A n Am Xm Xsub; rewrite -SetRing.RmuE//.
under eq_bigr => i do [rewrite -SetRing.RmuE; do ?by apply: Am=> /=].
pose rT := SetRing.type T.
have {}Am i : `I_n i -> measurable (A i : set rT).
  by move=> *; apply/SetRing.measurableW/Am => /=.
have {}Xm : measurable (X : set rT) by exact: SetRing.measurableW.
pose ammu := [additive_measure of SetRing.measure mu].
rewrite (le_trans (le_measure ammu  _ _ Xsub)) ?inE// {Xsub}.
  by rewrite -bigcup_mkord; apply: fin_bigcup_measurable.
elim: n Am Xm => [|n IHn] Am Xm; first by rewrite !big_ord0 measure0.
have Anm : measurable (A n : set rT) by apply: Am => /=.
set B := \big[setU/set0]_(i < n) A i.
set C := \big[setU/set0]_(i < n.+1) A i.
have -> : C = B `|` (A n `\` B).
  suff -> : A n `\` B = C `\` B by rewrite setDUK// /C big_ord_recr/=; left.
  by rewrite /C big_ord_recr/= !setDE setIUl -!setDE setDv set0U.
have Bm : measurable (B : set rT).
  by rewrite -[B]bigcup_mkord; apply: fin_bigcup_measurable => //= i /ltnW/Am.
rewrite measureU // ?setDIK//; last exact: measurableD.
rewrite (@le_trans _ _ (ammu B + ammu (A n))) // ?lee_add2l //; last first.
  by rewrite big_ord_recr /= lee_add2r// IHn// => i /ltnW/Am.
by rewrite le_measure // ?inE// ?setDE//; exact: measurableD.
Qed.
End boole_inequality.

Section boole_inequality.
Variables (R : realFieldType) (T : ringOfSetsType).
Variables (mu : {additive_measure set T -> \bar R}).

Theorem Boole_inequality (A : (set T) ^nat) n :
    (forall i, `I_n i -> measurable (A i)) ->
  mu (\big[setU/set0]_(i < n) A i) <= \sum_(i < n) mu (A i).
Proof.
move=> Am; rewrite semi_Boole_inequality// -bigcup_mkord.
exact: fin_bigcup_measurable.
Qed.

End boole_inequality.
Notation le_mu_bigsetU := Boole_inequality.

Section sigma_finite_lemma.
Variables (R : realFieldType) (T : ringOfSetsType) (A : set T)
  (mu : {additive_measure set T -> \bar R}).

Lemma sigma_finiteP : sigma_finite A mu ->
  exists2 F, A = \bigcup_i F i &
    nondecreasing_seq F /\ forall i, measurable (F i) /\ mu (F i) < +oo.
Proof.
move=> [S AS moo]; exists (fun n => \big[setU/set0]_(i < n.+1) S i).
  rewrite AS predeqE => t; split => [[i _ Sit]|[i _]].
    by exists i => //; rewrite big_ord_recr /=; right.
  by rewrite -bigcup_mkord => -[j /= ji Sjt]; exists j.
split=> [|i].
- apply/nondecreasing_seqP => i.
  rewrite [in X in (_ <= X)%O]big_ord_recr /=.
  by apply/subsetPset; left.
- split; first by apply: bigsetU_measurable => j _; exact: (moo j).1.
  rewrite (@le_lt_trans _ _ (\sum_(j < i.+1) mu (S j)))//.
    by apply: Boole_inequality => j _; exact: (moo j).1.
  by apply/lte_sum_pinfty => j _; exact: (moo j).2.
Qed.

End sigma_finite_lemma.

Section generalized_boole_inequality.
Variables (R : realType) (T : semiRingOfSetsType).
Variable (mu : {measure set T -> \bar R}).

(* 404,p.44 measure satisfies generalized Boole's inequality *)
Theorem generalized_semi_Boole_inequality : sigma_sub_additive mu.
Proof.
move=> X A Am Xm Xsub.
Abort.

End generalized_boole_inequality.

Section generalized_boole_inequality.
Variables (R : realType) (T : ringOfSetsType).
Variable (mu : {measure set T -> \bar R}).

(* 404,p.44 measure satisfies generalized Boole's inequality *)
Theorem generalized_Boole_inequality (A : (set T) ^nat) :
  (forall i, measurable (A i)) -> measurable (\bigcup_n A n) ->
  mu (\bigcup_n A n) <= \sum_(i <oo) mu (A i).
Proof.
move=> mA mbigcupA; set B := fun n => \big[setU/set0]_(i < n.+1) (A i).
have AB : \bigcup_k A k = \bigcup_n B n.
  rewrite predeqE => x; split => [[k _ ?]|[m _]].
    by exists k => //; rewrite /B big_ord_recr /=; right.
  rewrite /B big_ord_recr /= => -[|Amx]; last by exists m.
  by rewrite -bigcup_mkord => -[k ? ?]; exists k.
have ndB : nondecreasing_seq B.
  by move=> n m nm; exact/subsetPset/subset_bigsetU.
have mB : forall i, measurable (B i) by move=> i; exact: bigsetU_measurable.
rewrite AB.
move/(@cvg_mu_inc _ _ mu _ mB) : ndB => /(_ _)/cvg_lim <- //; last first.
  by rewrite -AB.
have -> : lim (mu \o B) = ereal_sup ((mu \o B) @` setT).
  suff : nondecreasing_seq (mu \o B).
    by move/ereal_nondecreasing_cvg; exact/cvg_lim.
  move=> n m nm; apply: le_measure => //; try by rewrite inE; apply mB.
  by move: nm; rewrite -ltnS; exact/subset_bigsetU.
suff BA m : mu (B m) <= \sum_(i <oo) mu (A i)
  by apply ub_ereal_sup => /= x [n _ <-{x}]; apply BA.
have := le_mu_bigsetU [additive_measure of mu] (fun i (_ : `I_m.+1 i) => mA i).
move=> /le_trans->//; rewrite -(big_mkord xpredT (mu \o A)).
apply: (@ereal_nneg_series_lim_ge _ (mu \o A) xpredT) => n _ /=.
exact: measure_ge0.
Qed.

End generalized_boole_inequality.
Notation le_mu_bigcup := generalized_Boole_inequality.

Section negligible.
Variables (R : realFieldType) (T : ringOfSetsType).

Definition negligible (mu : set T -> \bar R) (N : set T) :=
  exists A : set T, [/\ measurable A, mu A = 0 & N `<=` A].

Local Notation "mu .-negligible" := (negligible mu).

Lemma negligibleP (mu : {measure _ -> _}) A :
  measurable A -> mu.-negligible A <-> mu A = 0.
Proof.
move=> mA; split => [[B [mB mB0 AB]]|mA0]; last by exists A; split.
apply/eqP; rewrite eq_le measure_ge0 // andbT -mB0.
by apply: (le_measure (measure_additive_measure mu)) => //; rewrite in_setE.
Qed.

Lemma negligible_set0 (mu : {measure _ -> _}) : mu.-negligible set0.
Proof. exact/negligibleP. Qed.

Definition almost_everywhere (mu : set T -> \bar R) (P : T -> Prop)
     & (phantom Prop (forall x, P x)) :=
   mu.-negligible (~` [set x | P x]).
Local Notation "{ 'ae' m , P }" :=
  (almost_everywhere m (inPhantom P)) : type_scope.

Lemma aeW (mu : {measure _ -> _}) (P : T -> Prop) :
  (forall x, P x) -> {ae mu, forall x, P x}.
Proof.
move=> aP; have -> : P = setT by rewrite predeqE => t; split.
by apply/negligibleP; [rewrite setCT|rewrite setCT measure0].
Qed.

End negligible.

Notation "mu .-negligible" := (negligible mu) : type_scope.

Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom P)) : type_scope.

Definition sigma_subadditive (R : numFieldType) (T : Type)
  (mu : set T -> \bar R) := forall (A : (set T) ^nat),
  mu (\bigcup_n (A n)) <= \sum_(i <oo) mu (A i).

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : Type).
Record axioms (mu : set T -> \bar R) := Axioms {
  _ : mu set0 = 0 ;
  _ : forall x, 0 <= mu x ;
  _ : {homo mu : A B / A `<=` B >-> A <= B} ;
  _ : sigma_subadditive mu }.

Structure map (phUV : phant (set T -> \bar R)) :=
  Pack {apply : set T -> \bar R ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> \bar R)) (f g : set T -> \bar R).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation outer_measure f := (axioms f).
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
Variable mu : {outer_measure set T -> \bar R}.

Lemma outer_measure0 : mu set0 = 0.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_ge0 : forall x, 0 <= mu x.
Proof. by case: mu => ? []. Qed.

Lemma le_outer_measure : {homo mu : A B / A `<=` B >-> A <= B}.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_sigma_subadditive : sigma_subadditive mu.
Proof. by case: mu => ? []. Qed.

End outer_measure_lemmas.

Hint Extern 0 (_ set0 = 0) => solve [apply: outer_measure0] : core.
Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

Lemma le_outer_measureIC (R : realFieldType) T
  (mu : {outer_measure set T -> \bar R}) (A X : set T) :
  mu X <= mu (X `&` A) + mu (X `&` ~` A).
Proof.
pose B : (set T) ^nat := bigcup2 (X `&` A) (X `&` ~` A).
have cvg_mu : (fun n => \sum_(i < n) mu (B i)) --> mu (B 0%N) + mu (B 1%N).
  rewrite -2!cvg_shiftS /=.
  rewrite [X in X --> _](_ : _ = (fun=> mu (B 0%N) + mu (B 1%N))); last first.
    rewrite funeqE => i; rewrite 2!big_ord_recl /= big1 ?adde0 // => j _.
    by rewrite /B /bigcup2 /=.
  exact: cvg_cst.
have := outer_measure_sigma_subadditive mu B.
suff : \bigcup_n B n = X.
  move=> -> /le_trans; apply; under eq_fun do rewrite big_mkord.
  by rewrite (cvg_lim _ cvg_mu).
transitivity (\big[setU/set0]_(i < 2) B i).
  by rewrite (bigcup_splitn 2) // -bigcup_mkord setUidl// => t -[].
by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIUr setUCr setIT.
Unshelve. all: by end_near. Qed.

Definition caratheodory_measurable (R : realType) (T : Type)
  (mu : {outer_measure set T -> \bar R}) (A : set T) := forall X,
  mu X = mu (X `&` A) + mu (X `&` ~` A).

Notation "mu .-measurable" := (caratheodory_measurable mu)
  (at level 2, format "mu .-measurable") : type_scope.

Lemma le_caratheodory_measurable (R : realType) T
  (mu : {outer_measure set T -> \bar R}) (A : set T) :
  (forall X, mu (X `&` A) + mu (X `&` ~` A) <= mu X) ->
  mu.-measurable A.
Proof.
move=> suf X; apply/eqP; rewrite eq_le; apply/andP; split;
  [exact: le_outer_measureIC | exact: suf].
Qed.

Section caratheodory_theorem_sigma_algebra.

Variables (R : realType) (T : Type) (mu : {outer_measure set T -> \bar R}).

Lemma outer_measure_bigcup_lim (A : (set T) ^nat) X :
  mu (X `&` \bigcup_k A k) <= \sum_(k <oo) mu (X `&` A k).
Proof.
apply: (le_trans _ (outer_measure_sigma_subadditive mu (fun n => X `&` A n))).
by apply/le_outer_measure; rewrite setI_bigcupr.
Qed.

Let M := mu.-measurable.

Lemma caratheodory_measurable_set0 : M set0.
Proof. by move=> X /=; rewrite setI0 outer_measure0 add0e setC0 setIT. Qed.

Lemma caratheodory_measurable_setC A : M A -> M (~` A).
Proof. by move=> MA X; rewrite setCK addeC -MA. Qed.

Lemma caratheodory_measurable_setU_le (X A B : set T) :
  mu.-measurable A -> mu.-measurable B ->
  mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <= mu X.
Proof.
move=> mA mB; pose Y := X `&` A `|` X `&` B `&` ~` A.
have /(lee_add2r (mu (X `&` ~` (A `|` B)))) :
    mu Y <= mu (X `&` A) + mu (X `&` B `&` ~` A).
  pose Z := bigcup2 (X `&` A) (X `&` B `&` ~` A).
  have -> : Y = \bigcup_k Z k.
    rewrite predeqE => t; split=> [[?|?]|[]]; [by exists O|by exists 1%N|].
    by move=> [_ ?|[_ ?|//]]; [left|right].
  rewrite (le_trans (outer_measure_sigma_subadditive mu Z)) //.
  suff : ((fun n => \sum_(i < n) mu (Z i)) -->
      mu (X `&` A) + mu (X `&` B `&` ~` A)).
    move/cvg_lim => /=; under [in X in X <= _]eq_fun do rewrite big_mkord.
    by move=> ->.
  rewrite -(cvg_shiftn 2) /=; set l := (X in _ --> X).
  rewrite [X in X --> _](_ : _ = cst l); first exact: cvg_cst.
  rewrite funeqE => i; rewrite addn2 2!big_ord_recl big1 ?adde0 //.
  by move=> ? _; exact: outer_measure0.
have /le_trans : mu (X `&` (A `|` B)) + mu (X `&` ~` (A `|` B)) <=
    mu Y + mu (X `&` ~` (A `|` B)).
  rewrite setIUr (_ : X `&` A `|` X `&` B = Y) //.
  rewrite /Y -[in LHS](setIT B) -(setUCr A) 2!setIUr setUC -[in RHS]setIA.
  rewrite setUC setUA; congr (_ `|` _).
  by rewrite setUidPl setICA; apply subIset; right.
suff -> : mu (X `&` A) + mu (X `&` B `&` ~` A) +
    mu (X `&` (~` (A `|` B))) = mu X by exact.
by rewrite setCU setIA -(setIA X) setICA (setIC B) -addeA -mB -mA.
Qed.

Lemma caratheodory_measurable_setU A B : M A -> M B -> M (A `|` B).
Proof.
move=> mA mB X; apply/eqP; rewrite eq_le.
by rewrite le_outer_measureIC andTb caratheodory_measurable_setU_le.
Qed.

Lemma caratheodory_measurable_bigsetU (A : (set T) ^nat) : (forall n, M (A n)) ->
  forall n, M (\big[setU/set0]_(i < n) A i).
Proof.
move=> MA; elim=> [|n ih]; first by rewrite big_ord0; exact: caratheodory_measurable_set0.
by rewrite big_ord_recr; apply caratheodory_measurable_setU.
Qed.

Lemma caratheodory_measurable_setI A B : M A -> M B -> M (A `&` B).
Proof.
move=> mA mB; rewrite -(setCK A) -(setCK B) -setCU.
by apply/caratheodory_measurable_setC/caratheodory_measurable_setU;
  exact/caratheodory_measurable_setC.
Qed.

Lemma caratheodory_measurable_setD A B : M A -> M B -> M (A `\` B).
Proof.
move=> mA mB; rewrite setDE; apply caratheodory_measurable_setI => //.
exact: caratheodory_measurable_setC.
Qed.

Section additive_ext_lemmas.
Variable A B : set T.
Hypothesis (mA : M A) (mB : M B).

Let caratheodory_decomp X :
  mu X = mu (X `&` A `&` B) + mu (X `&` A `&` ~` B) +
         mu (X `&` ~` A `&` B) + mu (X `&` ~` A `&` ~` B).
Proof. by rewrite mA mB [X in _ + _ + X = _]mB addeA. Qed.

Let caratheorody_decompIU X : mu (X `&` (A `|` B)) =
  mu (X `&` A `&` B) + mu (X `&` ~` A `&` B) + mu (X `&` A `&` ~` B).
Proof.
rewrite caratheodory_decomp -!addeA; congr (mu _ + _).
  rewrite -!setIA; congr (_ `&` _).
  by rewrite setIC; apply/setIidPl; apply subIset; left; left.
rewrite addeA addeC [X in mu X + _](_ : _ = set0); last first.
  by rewrite -setIA -setCU -setIA setICr setI0.
rewrite outer_measure0 add0e addeC -!setIA; congr (mu (X `&` _) + mu (X `&` _)).
by rewrite setIC; apply/setIidPl; apply subIset; right; right.
by rewrite setIC; apply/setIidPl; apply subIset; left; left.
Qed.

Lemma disjoint_caratheodoryIU X : [disjoint A & B] ->
  mu (X `&` (A `|` B)) = mu (X `&` A) + mu (X `&` B).
Proof.
move=> /eqP AB; rewrite caratheodory_decomp -setIA AB setI0 outer_measure0.
rewrite add0e addeC -setIA -setCU -setIA setICr setI0 outer_measure0 add0e.
rewrite -!setIA; congr (mu (X `&` _ ) + mu (X `&` _)).
rewrite (setIC A) setIA setIC; apply/setIidPl.
- by rewrite setIUl setICr setU0 subsetI; move/disjoints_subset in AB; split.
- rewrite setIA setIC; apply/setIidPl; rewrite setIUl setICr set0U.
  by move: AB; rewrite setIC => /disjoints_subset => AB; rewrite subsetI; split.
Qed.
End additive_ext_lemmas.

Lemma caratheodory_additive (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall n X,
    mu (X `&` \big[setU/set0]_(i < n) A i) = \sum_(i < n) mu (X `&` A i).
Proof.
move=> MA ta; elim=> [|n ih] X; first by rewrite !big_ord0 setI0 outer_measure0.
rewrite big_ord_recr /= disjoint_caratheodoryIU // ?ih ?big_ord_recr //.
- exact: caratheodory_measurable_bigsetU.
- by apply/eqP/(@trivIset_bigsetUI _ predT) => //; rewrite /predT /= trueE.
Qed.

Lemma caratheodory_lim_lee (A : (set T) ^nat) : (forall n, M (A n)) ->
  trivIset setT A -> forall X,
  \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` \bigcup_k A k) <= mu X.
Proof.
move=> MA tA X.
set A' := \bigcup_k A k; set B := fun n => \big[setU/set0]_(k < n) (A k).
suff : forall n, \sum_(k < n) mu (X `&` A k) + mu (X `&` ~` A') <= mu X.
  move=> XA; rewrite (_ : lim _ = ereal_sup
      ((fun n => \sum_(k < n) mu (X `&` A k)) @` setT)); last first.
    under eq_fun do rewrite big_mkord.
    apply/cvg_lim => //; apply/ereal_nondecreasing_cvg.
    apply: (lee_sum_nneg_ord (fun n => mu (X `&` A n)) xpredT) => n _.
    exact: outer_measure_ge0.
  move XAx : (mu (X `&` ~` A')) => [x| |].
  - rewrite -lee_subr_addr //; apply ub_ereal_sup => /= _ [n _] <-.
    by rewrite EFinN lee_subr_addr // -XAx XA.
  - suff : mu X = +oo by move=> ->; rewrite lee_pinfty.
    by apply/eqP; rewrite -lee_pinfty_eq -XAx le_outer_measure.
  - by rewrite addeC /= lee_ninfty.
move=> n.
apply (@le_trans _ _ (\sum_(k < n) mu (X `&` A k) + mu (X `&` ~` B n))).
  apply/lee_add2l/le_outer_measure; apply: setIS; apply: subsetC => t.
  by rewrite /B -bigcup_mkord => -[i ? ?]; exists i.
rewrite [in X in _ <= X](caratheodory_measurable_bigsetU MA n) lee_add2r //.
by rewrite caratheodory_additive.
Qed.

Lemma caratheodory_measurable_trivIset_bigcup (A : (set T) ^nat) :
  (forall n, M (A n)) -> trivIset setT A -> M (\bigcup_k (A k)).
Proof.
move=> MA tA; apply le_caratheodory_measurable => X /=.
have /(lee_add2r (mu (X `&` ~` \bigcup_k A k))) := outer_measure_bigcup_lim A X.
by move/le_trans; apply; exact: caratheodory_lim_lee.
Qed.

Lemma caratheodory_measurable_bigcup (A : (set T) ^nat) : (forall n, M (A n)) ->
  M (\bigcup_k (A k)).
Proof.
move=> MA; rewrite -eq_bigcup_seqD_bigsetU.
apply/caratheodory_measurable_trivIset_bigcup; last first.
  apply: (@trivIset_seqD _ (fun n => \big[setU/set0]_(i < n.+1) A i)).
  by move=> n m nm; exact/subsetPset/subset_bigsetU.
by case=> [|n /=]; [| apply/caratheodory_measurable_setD => //];
  exact/caratheodory_measurable_bigsetU.
Qed.

End caratheodory_theorem_sigma_algebra.

Definition caratheodory_type (R : realType) (T : Type)
  (mu : {outer_measure set T -> \bar R}) := T.

Section caratheodory_sigma_algebra.
Variables (R : realType) (T : pointedType) (mu : {outer_measure set T -> \bar R}).

HB.instance Definition caratheodory_mixin := @isMeasurable.Build
  (caratheodory_type mu) (Pointed.class T) mu.-measurable
    (caratheodory_measurable_set0 mu)
    (@caratheodory_measurable_setC _ _ mu)
    (@caratheodory_measurable_bigcup _ _ mu).

End caratheodory_sigma_algebra.

Definition measure_is_complete (R : realType) (T : measurableType)
    (mu : set T -> \bar R) :=
  forall X, mu.-negligible X -> measurable X.

Section caratheodory_measure.
Variables (R : realType) (T : pointedType) (mu : {outer_measure set T -> \bar R}).
Local Notation U := (caratheodory_type mu).

Lemma caratheodory_measure0 : mu (set0 : set U) = 0.
Proof. exact: outer_measure0. Qed.

Lemma caratheodory_measure_ge0 (A : set U) : 0 <= mu A.
Proof. exact: outer_measure_ge0. Qed.

Lemma caratheodory_measure_sigma_additive : semi_sigma_additive (mu : set U -> _).
Proof.
move=> A mA tA mbigcupA; set B := \bigcup_k A k.
suff : forall X, mu X = \sum_(k <oo) mu (X `&` A k) + mu (X `&` ~` B).
  move/(_ B); rewrite setICr outer_measure0 adde0.
  rewrite (_ : (fun n => _) = fun n => \sum_(k < n) mu (A k)); last first.
    rewrite funeqE => n; rewrite big_mkord; apply eq_bigr => i _; congr (mu _).
    by rewrite setIC; apply/setIidPl => t Ait; exists i.
  move=> ->; have := fun n (_ : xpredT n) => outer_measure_ge0 mu (A n).
  move/(@is_cvg_ereal_nneg_series _ _) => /cvg_ex[l] hl.
  under eq_fun do rewrite -(big_mkord xpredT (mu \o A)).
  by move/(@cvg_lim _ (@ereal_hausdorff R)) : (hl) => ->.
move=> X.
have mB : mu.-measurable B := caratheodory_measurable_bigcup mA.
apply/eqP; rewrite eq_le (caratheodory_lim_lee mA tA X) andbT.
have /(lee_add2r (mu (X `&` ~` B))) := outer_measure_bigcup_lim mu A X.
by rewrite -le_caratheodory_measurable // => ?; rewrite -mB.
Qed.

Definition caratheodory_measure_mixin := Measure.Axioms caratheodory_measure0
  caratheodory_measure_ge0 caratheodory_measure_sigma_additive.
Definition caratheodory_measure : {measure set U -> \bar R} :=
  Measure caratheodory_measure_mixin.

Lemma measure_is_complete_caratheodory : measure_is_complete caratheodory_measure.
Proof.
move=> B [A [mA muA0 BA]]; apply le_caratheodory_measurable => X.
suff -> : mu (X `&` B) = 0.
  by rewrite add0e le_outer_measure //; apply subIset; left.
have muB0 : mu B = 0.
  apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
  by apply: (le_trans (le_outer_measure mu BA)); rewrite -muA0.
apply/eqP; rewrite eq_le outer_measure_ge0 andbT.
have : X `&` B `<=` B by apply subIset; right.
by move/(le_outer_measure mu); rewrite muB0 => ->.
Qed.

End caratheodory_measure.

(* TODO: move? *)
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

Lemma epsilon_trick (R : realType) (A : (\bar R)^nat) (e : {nonneg R})
    (P : pred nat) : (forall n, 0 <= A n) ->
  \sum_(i <oo | P i) (A i + (e%:nngnum / (2 ^ i.+1)%:R)%:E) <=
  \sum_(i <oo | P i) A i + e%:nngnum%:E.
Proof.
move=> A0; rewrite (@le_trans _ _ (lim (fun n => (\sum_(0 <= i < n | P i) A i) +
    \sum_(0 <= i < n) (e%:nngnum / (2 ^ i.+1)%:R)%:E))) //.
  rewrite ereal_pseriesD //; last by move=> n _; apply: divr_ge0.
  rewrite ereal_limD //.
  - rewrite lee_add2l //; apply: lee_lim => //.
    + by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
    + by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
    + by near=> n; apply: lee_sum_nneg_subset => // i _; apply divr_ge0.
  - exact: is_cvg_ereal_nneg_series.
  - by apply: is_cvg_ereal_nneg_series => n _; apply: divr_ge0.
  - by apply: adde_def_nneg_series => // n _; apply: divr_ge0.
suff cvggeo : (fun n => \sum_(0 <= i < n) (e%:nngnum / (2 ^ i.+1)%:R)%:E) -->
    e%:nngnum%:E.
  rewrite ereal_limD //.
  - by rewrite lee_add2l // (cvg_lim _ cvggeo).
  - exact: is_cvg_ereal_nneg_series.
  - by apply: is_cvg_ereal_nneg_series => ?; rewrite lee_fin divr_ge0.
  - by rewrite (cvg_lim _ cvggeo) //= fin_num_adde_def.
rewrite (_ : (fun n => _) = EFin \o
    (fun n => \sum_(0 <= i < n) (e%:nngnum / (2 ^ (i + 1))%:R))%R); last first.
  rewrite funeqE => n /=; rewrite (@big_morph _ _ EFin 0 adde)//.
  by under [in RHS]eq_bigr do rewrite addn1.
apply: cvg_comp; last apply cvg_refl.
have := cvg_geometric_series_half e%:nngnum O.
by rewrite expr0 divr1; apply: cvg_trans.
Unshelve. all: by end_near. Qed.

Section measurable_cover.
Variable T : semiRingOfSetsType.
Implicit Types (X : set T) (F : (set T)^nat).

Definition measurable_cover X := [set F : (set T)^nat |
  (forall i, measurable (F i)) /\ X `<=` \bigcup_k (F k)].

Lemma cover_measurable X F : measurable_cover X F -> forall k, measurable (F k).
Proof. by move=> + k; rewrite /measurable_cover => -[] /(_ k). Qed.

Lemma cover_subset X F : measurable_cover X F -> X `<=` \bigcup_k (F k).
Proof. by case. Qed.

End measurable_cover.

Section measure_extension.
Variables (R : realType) (T : semiRingOfSetsType) (mu : {additive_measure set T -> \bar R}).

Definition mu_ext (X : set T) : \bar R :=
  ereal_inf [set \sum_(i <oo) mu (A i) | A in measurable_cover X].

Lemma le_mu_ext : {homo mu_ext : A B / A `<=` B >-> A <= B}.
Proof.
move=> A B AB; apply/le_ereal_inf => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_ge0 A : 0 <= mu_ext A.
Proof.
apply: lb_ereal_inf => x [B [mB AB] <-{x}]; rewrite ereal_lim_ge //=.
  by apply: is_cvg_ereal_nneg_series => // n _; exact: measure_ge0.
by near=> n; rewrite sume_ge0 // => i _; apply: measure_ge0.
Unshelve. all: by end_near. Qed.

Lemma mu_ext0 : mu_ext set0 = 0.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last exact/mu_ext_ge0.
rewrite /mu_ext; apply ereal_inf_lb; exists (fun _ => set0); first by split.
by apply: (@lim_near_cst _ _ _ _ _ 0) => //; near=> n => /=; rewrite big1.
Unshelve. all: by end_near. Qed.

Lemma measurable_uncurry (G : ((set T)^nat)^nat) (x : nat * nat) :
  measurable (G x.1 x.2) -> measurable (uncurry G x).
Proof. by case: x. Qed.

Lemma mu_ext_sigma_subadditive : sigma_subadditive mu_ext.
Proof.
move=> A; have [[i ioo]|] := pselect (exists i, mu_ext (A i) = +oo).
  rewrite (ereal_nneg_series_pinfty _ _ ioo)// ?lee_pinfty// => n _.
  exact: mu_ext_ge0.
rewrite -forallNE => Aoo.
suff add2e : forall e : {posnum R},
    mu_ext (\bigcup_n A n) <= \sum_(i <oo) mu_ext (A i) + e%:num%:E.
  apply lee_adde => e.
  by rewrite -(mul1r e%:num) -(@divff _ 2%:R)// -mulrAC -mulrA add2e.
move=> e; rewrite (le_trans _ (epsilon_trick _ _ _))//; last first.
  by move=> n; apply: mu_ext_ge0.
pose P n (B : (set T)^nat) := measurable_cover (A n) B /\
  \sum_(k <oo) mu (B k) <= mu_ext (A n) + (e%:num / (2 ^ n.+1)%:R)%:E.
have [G PG] : {G : ((set T)^nat)^nat & forall n, P n (G n)}.
  apply: (@choice _ _ P) => n; rewrite /P /mu_ext.
  set S := (X in ereal_inf X); move infS : (ereal_inf S) => iS.
  case: iS infS => [r Sr|Soo|Soo].
  - have en1 : (0 < e%:num / (2 ^ n.+1)%:R)%R.
      by rewrite divr_gt0 // ltr0n expn_gt0.
    have /(lb_ereal_inf_adherent (PosNum en1)) : ereal_inf S \is a fin_num.
      by rewrite Sr.
    move=> [x [[B [mB AnB muBx]] xS]].
    exists B; split => //; rewrite muBx -Sr; apply/ltW.
    by rewrite (lt_le_trans xS) // lee_add2l //= lee_fin ler_pmul.
  - by have := Aoo n; rewrite /mu_ext Soo.
  - suff : lbound S 0 by move/lb_ereal_inf; rewrite Soo.
    move=> /= _ [B [mB AnB] <-].
    by apply: ereal_nneg_series_lim_ge0 => ? _; exact: measure_ge0.
have muG_ge0 : forall x, 0 <= (mu \o uncurry G) x.
  by move=> x; apply/measure_ge0.
apply (@le_trans _ _ (\csum_(i in setT) (mu \o uncurry G) i)).
  rewrite /mu_ext; apply: ereal_inf_lb => /=.
  have /card_esym/ppcard_eqP[f] := card_nat2.
  exists (uncurry G \o f).
    split => [i|]; first exact/measurable_uncurry/(PG (f i).1).1.1.
    apply: (@subset_trans _  (\bigcup_n \bigcup_k G n k)) => [t [i _]|].
      by move=> /(cover_subset (PG i).1) -[j _ ?]; exists i => //; exists j.
    move=> t [i _ [j _ Bijt]]; exists (f^-1%FUN (i, j)) => //=.
    by rewrite invK ?inE.
  rewrite -(@csum_image _ _ (mu \o uncurry G) _ xpredT) //; congr csum.
  by rewrite -[RHS](image_eq f)predeqE=> -[a b]/=; split=> -[n _ <-]; exists n.
rewrite (_ : csum _ _ = \sum_(i <oo) \sum_(j <oo ) mu (G i j)); last first.
  pose J : nat -> set (nat * nat) := fun i => [set (i, j) | j in setT].
  rewrite (_ : setT = \bigcup_k J k); last first.
    by rewrite predeqE => -[a b]; split => // _; exists a => //; exists b.
  rewrite csum_bigcup /=; last 2 first.
    - apply/trivIsetP => i j _ _ ij.
      rewrite predeqE => -[n m] /=; split => //= -[] [_] _ [<-{n} _].
      by move=> [m' _] [] /esym/eqP; rewrite (negbTE ij).
    - by move=> /= [n m]; apply/measure_ge0; exact: (cover_measurable (PG n).1).
  rewrite (_ : setT = id @` xpredT); last first.
    by rewrite image_id funeqE => x; rewrite trueE.
  rewrite csum_image //; last by move=> n _; apply: csum_ge0.
  apply: eq_ereal_pseries => /= j.
  rewrite -(@csum_image R _ (mu \o uncurry G) (pair j) predT) //=; last first.
  - by apply: (@can_inj _ _ _ snd).
  - by move=> n _; rewrite (muG_ge0 (_ , _)).
  by congr csum; rewrite predeqE => -[a b]; split; move=> [i _ <-]; exists i.
apply lee_lim.
- apply: is_cvg_ereal_nneg_series => n _.
  by apply: ereal_nneg_series_lim_ge0 => m _; exact: (muG_ge0 (n, m)).
- by apply: is_cvg_ereal_nneg_series => n _; apply: adde_ge0 => //;
    [exact: mu_ext_ge0 | rewrite lee_fin // divr_ge0].
- by near=> n; apply: lee_sum => i _; exact: (PG i).2.
Unshelve. all: by end_near. Qed.

End measure_extension.

Canonical outer_measure_of_measure (R : realType) (T : semiRingOfSetsType)
  (mu : {additive_measure set T -> \bar R}) : {outer_measure set T -> \bar R} :=
    OuterMeasure (OuterMeasure.Axioms (mu_ext0 mu) (mu_ext_ge0 mu)
      (le_mu_ext mu) (mu_ext_sigma_subadditive mu)).


Section g_salgebra_measure_unique_trace.
Variables (R : realType) (T : measurableType) (G : set (set T)).
Variables (D : set T) (mD : measurable D).
Let H := [set X | G X /\ X `<=` D] (* "trace" of G wrt D *).
Hypotheses (Hm : H `<=` measurable) (setIH : setI_closed H) (HD : H D).
Variables m1 m2 : {measure set T -> \bar R}.
Hypotheses (m1m2 : forall A, H A -> m1 A = m2 A) (m1oo : (m1 D < +oo)%E).

Lemma g_salgebra_measure_unique_trace :
  (forall X, (s<| D, H |>) X -> X `<=` D) -> forall X, s<| D, H |> X ->
  m1 X = m2 X.
Proof.
move=> sDHD; set E := [set A | [/\ measurable A, m1 A = m2 A & A `<=` D] ].
have HE : H `<=` E.
  by move=> X HX; rewrite /E /=; split; [exact: Hm|exact: m1m2|case: HX].
have setDE : setD_closed E.
  move=> A B BA [mA m1m2A AD] [mB m1m2B BD]; split; first exact: measurableD.
  - rewrite measureD//; last first.
      by rewrite (le_lt_trans _ m1oo)//; apply: le_measure => //=; rewrite inE.
    rewrite setIidr// m1m2A m1m2B measureD// ?setIidr//.
    by rewrite (le_lt_trans _ m1oo)// -m1m2A; apply: le_measure => //;
      rewrite inE.
  - by rewrite setDE; apply: subIset; left.
have ndE : ndseq_closed E.
  move=> A ndA EA; split; have mA n : measurable (A n) by have [] := EA n.
  - exact: measurable_bigcup.
  - transitivity (lim (m1 \o A)).
      by apply/esym/cvg_lim=> //; exact/(cvg_mu_inc mA _ ndA)/measurable_bigcup.
    transitivity (lim (m2 \o A)).
      by congr (lim _); rewrite funeqE => n; have [] := EA n.
    by apply/cvg_lim => //; exact/(cvg_mu_inc mA _ ndA)/measurable_bigcup.
  - by apply: sub_bigcup => n; have [] := EA n.
have sDHE : s<| D, H |> `<=` E.
  by apply: monotone_class_subset => //; split => //; [move=> A []|exact/HE].
by move=> X /sDHE[mX ?] _.
Qed.

End g_salgebra_measure_unique_trace.

Section g_salgebra_measure_unique.
Variables (R : realType) (T : measurableType) (G : set (set T)).
Hypothesis (Gm : G `<=` measurable).
Variable g : (set T)^nat.
Hypotheses (Gg : forall i, G (g i)) (nd_g : nondecreasing_seq g).
Hypothesis g_cover : \bigcup_k (g k) = setT.
Variables m1 m2 : {measure set T -> \bar R}.

Lemma g_salgebra_measure_unique_cover :
  (forall n A, s<< G >> A -> m1 (g n `&` A) = m2 (g n `&` A)) ->
  (forall A, s<< G >> A -> m1 A = m2 A).
Proof.
move=> sGm1m2 A sGA.
have -> : A = \bigcup_n (g n `&` A) by rewrite -setI_bigcupl g_cover setTI.
have sGm : s<< G >> `<=` measurable.
  by apply: g_salgebra_smallest => //; exact: are_measurable_sets_measurable.
transitivity (lim (fun n => m1 (g n `&` A))).
  apply/esym/cvg_lim => //; apply: cvg_mu_inc => //.
  - by move=> n; apply: measurableI; [exact/Gm|exact/sGm].
  - by apply: measurable_bigcup => k; apply: measurableI; [exact/Gm|exact/sGm].
  - by move=> ? ? ?; apply/subsetPset; apply: setSI; exact/subsetPset/nd_g.
transitivity (lim (fun n => m2 (g n `&` A))).
  by congr (lim _); rewrite funeqE => x; apply: sGm1m2 => //; exact/sGm.
apply/cvg_lim => //; apply: cvg_mu_inc => //.
- by move=> k; apply: measurableI => //; [exact/Gm|exact/sGm].
- by apply: measurable_bigcup => k; apply: measurableI; [exact/Gm|exact/sGm].
- by move=> a b ab; apply/subsetPset; apply: setSI; exact/subsetPset/nd_g.
Qed.

Hypothesis setIG : setI_closed G.
Hypothesis m1m2 : forall A, G A -> m1 A = m2 A.
Hypothesis m1goo : forall k, (m1 (g k) < +oo)%E.

Lemma g_salgebra_measure_unique : forall E, s<< G >> E -> m1 E = m2 E.
Proof.
pose G_ n := [set X | G X /\ X `<=` g n]. (* "trace" *)
have G_E n : G_ n = [set g n `&` C | C in G].
  rewrite eqEsubset; split.
    by move=> X [GX Xgn] /=; exists X => //; rewrite setIidr.
  by rewrite /G_ => X [Y GY <-{X}]; split; [exact: setIG|apply: subIset; left].
have gIsGE n : [set g n `&` A | A in s<< G >>] =
               s<| g n, preimage_class (g n) id G |>.
  rewrite transfer eqEsubset; split.
    by move=> _ /= [Y sGY <-]; exists Y => //; rewrite preimage_id setIC.
  by move=> _ [Y mY <-] /=; exists Y => //; rewrite preimage_id setIC.
have preimg_gGE n : preimage_class (g n) id G = G_ n.
  rewrite eqEsubset; split => [_ [Y GY <-]|].
    by rewrite preimage_id G_E /=; exists Y => //; rewrite setIC.
  by move=> X [GX Xgn]; exists X => //; rewrite preimage_id setIidr.
apply: g_salgebra_measure_unique_cover => //.
move=> n A sGA; apply: (@g_salgebra_measure_unique_trace _ _ G (g n)) => //.
- exact: Gm.
- by move=> ? [? _]; exact/Gm.
- by move=> ? ? [? ?] [? ?]; split; [exact: setIG|apply: subIset; tauto].
- by split.
- by move=> ? [? ?]; exact: m1m2.
- move=> X; rewrite -/(G_ n) -preimg_gGE -gIsGE.
  by case=> B sGB <-{X}; apply: subIset; left.
- by rewrite -/(G_ n) -preimg_gGE -gIsGE; exists A.
Qed.

End g_salgebra_measure_unique.
