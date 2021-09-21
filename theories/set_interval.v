(* -*- company-coq-local-symbols: (("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
Require Import boolp reals ereal classical_sets posnum nngnum topology.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences.

(******************************************************************************)
(* This files contains lemmas about sets and intervals (WIP).                 *)
(*                                                                            *)
(*                 lte_bnd == multirule to simplify inequalities about        *)
(*                            interval bounds                                 *)
(*                miditv i == middle point of interval i                      *)
(*                 neitv i == the interval i is non-empty                     *)
(*                            when the support type is a numFieldType, this   *)
(*                            is equivalent to (i.1 < i.2)%O (lemma neitvE)   *)
(*                set_itvE == multirule to turn intervals into inequalities   *)
(*      contiguous_itv i j == intervals i and j are contiguous                *)
(*                    conv == convexity operator                              *)
(*        disjoint_itv i j == intervals i and j are disjoint                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lte_bnd.
Variables (d : unit) (T : porderType d).
Implicit Types (x y : T) (b : bool).

Local Lemma BLeft_ltE x y : (BLeft x < BLeft y)%O = (x < y)%O.
Proof. by []. Qed.
Local Lemma BRight_leE x y : (BRight x <= BRight y)%O = (x <= y)%O.
Proof. by []. Qed.
Local Lemma BRight_BLeft_leE x y : (BRight x <= BLeft y)%O = (x < y)%O.
Proof. by []. Qed.
Local Lemma BLeft_BRight_ltE x y : (BLeft x < BRight y)%O = (x <= y)%O.
Proof. by []. Qed.
Local Lemma BRight_BSide_ltE x y b : (BRight x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.
Local Lemma BLeft_BSide_leE x y b : (BLeft x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.

Definition lte_bnd := (BLeft_ltE, BLeft_BRight_ltE, BRight_BSide_ltE,
  BLeft_BSide_leE, BRight_BLeft_leE, BRight_leE).

Lemma BSide_BRight_leE x y b : (BSide b x <= BRight y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Lemma BSide_BLeft_leE x y b : (BSide b x < BLeft y)%O = (x < y)%O.
Proof. by case: b. Qed.
Lemma BSide_leE x y b : (BSide b x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Lemma BSide_ltE x y b : (BSide b x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.

End lte_bnd.

Lemma ltBRight_leBLeft (d : unit) (T : porderType d) (a : itv_bound T) (r : T) :
  (a < BRight r)%O -> (a <= BLeft r)%O.
Proof. by move: a => [[] a|[]]. Qed.

Lemma itv_meet_mem (d : unit) (T : orderType d) (i1 i2 j1 j2 : itv_bound T)
    (x : T) :
  x \in itv_meet (Interval i1 i2) (Interval j1 j2) <->
  x \in Interval i1 i2 /\ x \in Interval j1 j2.
Proof.
split.
  rewrite /= 3!itv_boundlr joinEtotal meetEtotal le_maxl le_minr.
  by move=> /andP[/andP[-> ->] /andP[-> ->]].
case; rewrite 2!itv_boundlr => /andP[i1x xi2] /andP[j1x xj2].
by rewrite /= itv_boundlr joinEtotal meetEtotal le_maxl le_minr i1x j1x xj2 xi2.
Qed.

Coercion pair_of_interval T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

Definition miditv (R : numDomainType) (i : interval R) : R :=
  match i with
  | Interval (BSide _ a) (BSide _ b) => (a + b) / 2
  | Interval -oo%O (BSide _ b) => b - 1
  | Interval (BSide _ a) +oo%O => a + 1
  | Interval -oo%O +oo%O => 0
  | _ => 0
  end.

Section miditv_lemmas.
Variable R : numFieldType.
Implicit Types i : interval R.

Lemma mem_miditv i : (i.1 < i.2)%O -> miditv i \in i.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //= ab; rewrite in_itv /=.
- by rewrite midf_lt // andbT midf_le // ltW.
- by rewrite midf_le // midf_le.
- by rewrite ler_addl ler01.
- by rewrite midf_lt // midf_lt.
- by rewrite midf_lt // midf_le // ltW.
- by rewrite ltr_addl ltr01.
- by rewrite ltr_subl_addr ltr_addl.
- by rewrite ler_subl_addr ler_addl.
Qed.

Lemma miditv_bnd2 i : (i.1 < i.2)%O -> forall b, (BSide b (miditv i) <= i.2)%O.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //= => ab; case; rewrite lte_bnd.
- by rewrite midf_le // ltW.
- by rewrite midf_lt.
- by rewrite midf_le.
- by rewrite midf_le.
- by rewrite midf_le // ltW.
- by rewrite midf_lt.
- by rewrite midf_le // ltW.
- by rewrite midf_le // ltW.
- by rewrite ler_subl_addl ler_addr.
- by rewrite ltr_subl_addl ltr_addr.
- by rewrite ler_subl_addl ler_addr.
- by rewrite ler_subl_addl ler_addr.
Qed.

Lemma miditv_bnd1 i : (i.1 < i.2)%O -> forall b, (i.1 <= BSide b (miditv i))%O.
Proof.
move: i => [[[]a|[]] [[]b|[]]] //= => ab; case; rewrite lte_bnd.
- by rewrite midf_le // ltW.
- by rewrite midf_le // ltW.
- by rewrite midf_le.
- by rewrite midf_le.
- by rewrite ler_addl.
- by rewrite ler_addl.
- by rewrite midf_lt.
- by rewrite midf_le // ltW.
- by rewrite midf_lt.
- by rewrite midf_le // ltW.
- by rewrite ltr_addl.
- by rewrite ler_addl.
Qed.

End miditv_lemmas.

(* definitions and lemmas to make a bridge between MathComp intervals and     *)
(* classical sets                                                             *)
Section set_itv_porderType.
Variables (d : unit) (T : porderType d).
Implicit Types (i j : interval T) (x y : T) (a : itv_bound T).

Definition neitv i := [set` i] != set0.

Lemma neitv_lt_bnd i : neitv i -> (i.1 < i.2)%O.
Proof.
case: i => a b; apply: contraNT => /= /itv_ge ab0.
by apply/eqP; rewrite predeqE => t; split => //=; rewrite ab0.
Qed.

Lemma set_itvP i j : [set` i] = [set` j] :> set _ <-> i =i j.
Proof.
split => [ij x|ij]; first by have /(congr1 (@^~ x))/=/is_true_inj := ij.
by rewrite predeqE => r /=; rewrite ij.
Qed.

Lemma subset_itvP i j : {subset i <= j} <-> [set` i] `<=` [set` j].
Proof. by []. Qed.

Lemma set_itvoo x y : `]x, y[%classic = (fun z => x < z < y)%O.
Proof. by []. Qed.

Lemma set_itvoo0 x : `]x, x[%classic = set0.
Proof.
rewrite set_itvoo predeqE => r; split => // /andP[/lt_trans] /[apply].
by rewrite ltxx.
Qed.

Lemma set_itvcc x y : `[x, y]%classic = (fun z => x <= z <= y)%O.
Proof. by []. Qed.

Lemma set_itvoc x y : `]x, y]%classic = (fun z => x < z <= y)%O.
Proof. by []. Qed.

Lemma set_itvoc0 x : `]x, x]%classic = set0.
Proof.
rewrite set_itvoc predeqE => r; split => // /andP[/lt_le_trans] /[apply].
by rewrite ltxx.
Qed.

Lemma set_itvco x y : `[x, y[%classic = (fun z => x <= z < y)%O.
Proof. by []. Qed.

Lemma set_itvco0 x : `[x, x[%classic = set0.
Proof.
rewrite set_itvco predeqE => r; split => // /andP[/le_lt_trans] /[apply].
by rewrite ltxx.
Qed.

Lemma set_itv_infty_infty : `]-oo, +oo[%classic = @setT T.
Proof. by rewrite predeqE. Qed.

Lemma set_itv_o_infty x : `]x, +oo[%classic = (fun z => x < z)%O.
Proof. by rewrite predeqE /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_itv_c_infty x : `[x, +oo[%classic = (fun z => x <= z)%O.
Proof. by rewrite predeqE /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_itv_infty_o x : `]-oo, x[%classic = (fun z => z < x)%O.
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itv_infty_c x : `]-oo, x]%classic = (fun z => z <= x)%O.
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itv_pinfty_bnd a : [set` Interval +oo%O a] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd. Qed.

Lemma set_itv_bnd_ninfty a : [set` Interval a -oo%O] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd /=; case: a => [[]a|[]]. Qed.

Definition set_itv_infty_set0 := (set_itv_bnd_ninfty, set_itv_pinfty_bnd).

Definition set_itvE := (set_itvoo0, set_itvoc0, set_itvco0, set_itvoo,
  set_itvcc, set_itvoc, set_itvco, set_itv_infty_infty, set_itv_o_infty,
  set_itv_c_infty, set_itv_infty_o, set_itv_infty_c, set_itv_infty_set0).

(* puncture interval *)
Lemma punct_itvoc x y : (x < y)%O -> (`]x, y] = `]x, y[ `|` [set y])%classic.
Proof.
move=> xy; rewrite !set_itvE predeqE => r; split=> [/andP[xr]|].
  by rewrite le_eqVlt => /predU1P[->|ry]; [right|left; rewrite xr].
by case=> [/andP[ar /ltW ->]|->]; [rewrite andbT|rewrite xy lexx].
Qed.

Lemma punct_itvco x y : (x < y)%O -> (`[x, y[ = [set x] `|` `]x, y[)%classic.
Proof.
move=> xy; rewrite !set_itvE predeqE => r; split=> [/andP[]|].
  by rewrite le_eqVlt => /predU1P[->|xr ry]; [left|right; rewrite xr].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma punct_itvccL x y : (x <= y)%O -> (`[x, y] = [set x] `|` `]x, y])%classic.
Proof.
move=> ab; rewrite !set_itvE predeqE => r; split=> [/andP[]|].
  by rewrite le_eqVlt => /predU1P[->|xr ry]; [left|right; rewrite xr].
by case=> [->|/andP[/ltW -> -> //]]; rewrite lexx.
Qed.

Lemma punct_itvccR x y : (x <= y)%O -> (`[x, y] = `[x, y[ `|` [set y])%classic.
Proof.
move=> xy; rewrite !set_itvE predeqE => r; split=> [/andP[xr]|].
  by rewrite le_eqVlt => /predU1P[->|ry]; [right|left; rewrite xr].
by case=> [/andP[-> /ltW //]|->]; rewrite lexx xy.
Qed.

Lemma punct_itv_c_infty x : (`[x, +oo[ = [set x] `|` `]x, +oo[ )%classic.
Proof.
rewrite predeqE => r; rewrite !set_itvE; split; last by case=> [->//|/ltW].
by rewrite le_eqVlt => /predU1P[->|?]; [left|right].
Qed.

Lemma punct_itv_infty_c x : (`]-oo, x] = `]-oo, x[ `|` [set x])%classic.
Proof.
rewrite predeqE => r; rewrite !set_itvE; split => [|[/ltW //|-> //=]].
by rewrite le_eqVlt => /predU1P[->|xr]; [right|left].
Qed.

End set_itv_porderType.
Arguments neitv {d T} _.

Section set_itv_numFieldType.
Variable R : numFieldType.
Implicit Types i : interval R.

Lemma neitvE i : neitv i = (i.1 < i.2)%O.
Proof.
apply/idP/idP; first exact: neitv_lt_bnd.
by move=> /mem_miditv ii; apply/set0P; exists (miditv i).
Qed.

Lemma neitvP i : reflect (i.1 < i.2)%O (neitv i).
Proof. by apply: (iffP idP); rewrite -neitvE. Qed.

End set_itv_numFieldType.

Lemma setitv0 (R : realDomainType) : [set` (0%O : interval R)] = set0.
Proof. by rewrite predeqE. Qed.

Section interval_has_bound.
Variable R : numDomainType.

Lemma has_lbound_itv (x : R) b (a : itv_bound R) :
  has_lbound [set` Interval (BSide b x) a].
Proof. by case: b; exists x => r /andP[]; rewrite lte_bnd // => /ltW. Qed.

Lemma has_ubound_itv (x : R) b (a : itv_bound R) :
  has_ubound [set` Interval a (BSide b x)].
Proof. by case: b; exists x => r /andP[]; rewrite lte_bnd // => _ /ltW. Qed.

End interval_has_bound.

Section interval_hasNbound.
Variable R : realDomainType.

Lemma hasNlbound_itv (a : itv_bound R) : a != -oo%O ->
  ~ has_lbound [set` Interval -oo%O a].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_lbound `]-oo, r[%classic.
    by case: b => //; apply/contra_not/subset_has_lbound => x /ltW.
  apply/has_lbPn => x; exists (minr (r - 1) (x - 1)).
    by rewrite !set_itvE lt_minl ltr_subl_addr ltr_addl ltr01.
  by rewrite lt_minl orbC ltr_subl_addr ltr_addl ltr01.
case=> r /(_ (r - 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltr_subl_addr ltr_addl.
Qed.

Lemma hasNubound_itv (a : itv_bound R) : a != +oo%O ->
  ~ has_ubound [set` Interval a +oo%O].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_ubound `]r, +oo[%classic.
    case: b => //; apply/contra_not/subset_has_ubound => x.
    by rewrite !set_itvE => /ltW.
  apply/has_ubPn => x; rewrite !set_itvE; exists (maxr (r + 1) (x + 1));
  by rewrite ?in_itv /= ?andbT lt_maxr ltr_addl ltr01 // orbT.
case=> r /(_ (r + 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltr_addl.
Qed.

End interval_hasNbound.

Hint Extern 0 (has_lbound _) => solve[apply: has_lbound_itv] : core.
Hint Extern 0 (has_ubound _) => solve[apply: has_ubound_itv] : core.
Hint Extern 0 (~ has_lbound _) => solve[by apply: hasNlbound_itv] : core.
Hint Extern 0 (~ has_ubound _) => solve[by apply: hasNubound_itv] : core.

Section interval_has.
Variable R : realType.
Implicit Types x : R.

Lemma has_sup_half x b (i : itv_bound R) : (i < BSide b x)%O ->
  has_sup [set` Interval i (BSide b x)].
Proof.
move: b i => [] [[]y|[]]; rewrite ?lte_bnd => xy; split=> //; do 1?[
  by exists ((x + y) / 2); rewrite !set_itvE addrC !(midf_le,midf_lt) //;
    exact: ltW
| by exists (x - 1); rewrite !set_itvE
    !(ltr_subl_addr, ler_subl_addr, ltr_addl,ler_addl)].
Qed.

Lemma has_inf_half x b (i : itv_bound R) : (BSide b x < i)%O ->
  has_inf [set` Interval (BSide b x) i].
Proof.
move: b i => [] [[]y|[]]; rewrite ?lte_bnd => xy; do 1?[
  by (split=> //; exists ((x + y) / 2); rewrite !set_itvE !(midf_le,midf_lt) //;
    exact: ltW)
| (by split => //; exists (x + 1); rewrite !set_itvE !(ltr_addl,ler_addl))].
Qed.

End interval_has.

Hint Extern 0 (has_sup _) => solve[apply: has_sup1 | exact: has_sup_half] : core.
Hint Extern 0 (has_inf _) => solve[apply: has_inf1 | exact: has_inf_half]: core.

Lemma minus_itv_bnd_infty (R : numDomainType) (x : R) b :
  -%R @` [set` Interval (BSide b x) +oo%O] =
  [set` Interval -oo%O (BSide (negb b) (- x))].
Proof.
rewrite predeqE => /= r; split=> [[y xy <-]|xr].
  by case: b xy; rewrite !in_itv/= andbT (ler_opp2, ltr_opp2).
exists (- r); rewrite ?opprK //.
by case: b xr; rewrite !in_itv/= andbT (ler_oppr, ltr_oppr).
Qed.

Lemma minus_itvoo (R : numDomainType) (x y : R) :
  -%R @` `]x, y[%classic = `](- y), (- x)[%classic.
Proof.
rewrite predeqE => /= r; split => [[{}r + <-]|].
  by rewrite !in_itv/= !ltr_opp2 andbC.
by exists (- r); rewrite ?opprK// !in_itv/= ltr_oppl ltr_oppr andbC.
Qed.

Section interval_sup_inf.
Variable R : realType.
Implicit Types x y : R.

Lemma sup_itv_infty_bnd x b : sup [set` Interval -oo%O (BSide b x)] = x.
Proof.
case: b; last first.
  by rewrite punct_itv_infty_c sup_setU ?sup1// => ? ? ? ->; exact/ltW.
set s := sup _; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub; last by move=> ? /ltW.
  by exists (x - 1); rewrite !set_itvE ltr_subl_addr ltr_addl.
- rewrite leNgt; apply/negP => sx; pose p := (s + x) / 2.
  suff /andP[?]: (p < x) && (s < p) by apply/negP; rewrite -leNgt sup_ub.
  by rewrite !midf_lt.
Qed.

Lemma inf_itv_bnd_infty x b : inf [set` Interval (BSide b x) +oo%O] = x.
Proof.
case: b; last by rewrite /inf minus_itv_bnd_infty sup_itv_infty_bnd opprK.
rewrite punct_itv_c_infty inf_setU ?inf1// => _ b ->.
by rewrite !set_itvE => /ltW.
Qed.

Let sup_itv_o_bnd x y b : x < y ->
  sup [set` Interval (BRight x) (BSide b y)] = y.
Proof.
case: b => xy; last first.
  by rewrite punct_itvoc// sup_setU ?sup1// => ? ? /andP[? /ltW ?] ->.
set B := [set` _]; set A := `]-oo, x]%classic.
rewrite -(@sup_setU _ A B) //.
- rewrite -(sup_itv_infty_bnd y true); congr sup.
  rewrite predeqE => u; split=> [[|/andP[]//]|yu].
  by rewrite /A !set_itvE => /le_lt_trans; apply.
  by have [xu|ux] := ltP x u; [right; rewrite /B !set_itvE xu| left].
- by move=> u v; rewrite /A /B => ? /andP[xv _]; rewrite (le_trans _ (ltW xv)).
Qed.

Lemma sup_itv_bounded x y a b : x < y ->
  sup [set` Interval (BSide a x) (BSide b y)] = y.
Proof.
case: a => xy; last exact: sup_itv_o_bnd.
case: b.
  by rewrite punct_itvco// sup_setU ?sup_itv_o_bnd// => ? ? -> /andP[/ltW].
by rewrite (punct_itvccR (ltW _))// sup_setU ?sup1// => ? ? /andP[_ /ltW ? ->].
Qed.

Lemma sup_itvcc x y : x <= y -> sup `[x, y]%classic = y.
Proof.
by move=> ?; rewrite punct_itvccR// sup_setU ?sup1// => ? ? /andP[_ /ltW ? ->].
Qed.

Let inf_itv_bnd_o x y b : x < y ->
  inf [set` Interval (BSide b x) (BLeft y)] = x.
Proof.
case: b => xy.
  by rewrite punct_itvco// inf_setU ?inf1// => _ ? -> /andP[/ltW].
by rewrite /inf minus_itvoo sup_itv_o_bnd ?opprK // ltr_oppl opprK.
Qed.

Lemma inf_itv_bounded x y a b : x < y ->
  inf [set` Interval (BSide a x) (BSide b y)] = x.
Proof.
case: b => xy; first exact: inf_itv_bnd_o.
case: a.
  by rewrite (punct_itvccL (ltW _))// inf_setU ?inf1// => ? ? -> /andP[/ltW].
by rewrite punct_itvoc// inf_setU ?inf_itv_bnd_o// => ? ? /andP[? /ltW ?] ->.
Qed.

Lemma inf_itvcc x y : x <= y -> inf `[x, y]%classic = x.
Proof.
by move=> ?; rewrite punct_itvccL// inf_setU ?inf1 // => ? ? -> /andP[/ltW].
Qed.

End interval_sup_inf.

(* lemmas between itv and set-theoretic operations *)
Section set_itv_porderType.
Variables (d : unit) (T : orderType d).
Implicit Types (x y : T) (i j : interval T) (b : bool).

Lemma set_itvC_infty_bnd b x :
  ~` [set` Interval -oo%O (BSide b x)] =
  [set` Interval (BSide b x) +oo%O].
Proof.
case: b; rewrite !set_itvE predeqE => r.
by split; rewrite leNgt => /negP.
by split; rewrite ltNge => /negP.
Qed.

Lemma set_itvC_bnd_infty b x :
  ~` [set` Interval (BSide b x) +oo%O] =  [set` Interval -oo%O (BSide b x)].
Proof. by rewrite -set_itvC_infty_bnd setCK. Qed.

Let set_itvC_bounded b0 b1 x y : ~` [set` Interval (BSide b0 x) (BSide b1 y)] =
  [set` Interval -oo%O (BSide b0 x)] `|` [set` Interval (BSide b1 y) +oo%O].
Proof.
move: b0 b1 => [] []; rewrite !set_itvE predeqE => r; split.
by move/negP; rewrite negb_and -ltNge -leNgt => /orP.
by move/orP; rewrite leNgt (ltNge r x) -negb_and => /negP.
by move/negP; rewrite negb_and -2!ltNge => /orP.
by move/orP; rewrite 2!ltNge -negb_and => /negP.
by move/negP; rewrite negb_and -2!leNgt => /orP.
by move/orP; rewrite 2!leNgt -negb_and => /negP.
by move/negP; rewrite negb_and -leNgt -ltNge => /orP.
by move/orP; rewrite leNgt (ltNge y r) -negb_and => /negP.
Qed.

Lemma set_itvC_itv i : ~` [set` i] =
  [set` Interval -oo%O i.1] `|` [set` Interval i.2 +oo%O].
Proof.
case: i => -[[] x|[]] [[] y|[]] /=.
by rewrite set_itvC_bounded.
by rewrite set_itvC_bounded.
by rewrite !set_itvE setUT setC0.
by rewrite set_itvC_bnd_infty !set_itvE setU0.
by rewrite set_itvC_bounded.
by rewrite set_itvC_bounded.
by rewrite !set_itvE setC0 setUT.
by rewrite set_itvC_bnd_infty !set_itvE setU0.
by rewrite set_itvC_infty_bnd !set_itvE set0U.
by rewrite set_itvC_infty_bnd !set_itvE set0U.
by rewrite set_itvE setC0 set0U set_itvE.
by rewrite !set_itvE setCT set0U.
by rewrite !set_itvE setTU setC0.
by rewrite !set_itvE setTU setC0.
by rewrite !set_itvE setC0 setTU.
by rewrite !set_itvE setC0 setU0.
Qed.

Definition set_itvC := (set_itvC_infty_bnd, set_itvC_bnd_infty, set_itvC_itv).

Lemma itv_boundedErays a x b y : [set` Interval (BSide a x) (BSide b y)] =
  [set` Interval (BSide a x) +oo%O] `\` [set` Interval (BSide b y) +oo%O].
Proof. by rewrite -[LHS]setCK set_itvC setCU /= set_itvC setDE. Qed.

Lemma set_itv_meet i j : [set` itv_meet i j] = [set` i] `&` [set` j].
Proof.
rewrite eqEsubset; split => x; move: i j => [i1 i2] [j1 j2] /=.
- rewrite itv_boundlr joinEtotal meetEtotal le_maxl le_minr.
  move=> /andP[/andP[i1x j1x] /andP[xi2 xj2]].
  by split; rewrite /= itv_boundlr ?i1x ?xi2 // j1x xj2.
- case; rewrite /= !itv_boundlr => /andP[i1x xi2] /andP[j1x xj2] /=.
  by rewrite joinEtotal meetEtotal le_maxl le_minr i1x xi2 j1x xj2.
Qed.

End set_itv_porderType.

Section set_itv_realType.
Variable R : realType.
Implicit Types x : R.

Lemma set_itvK : {in neitv, cancel (fun i => [set` i]) (@Rhull R)}.
Proof.
move=> [[[] x|[]] [[] y|[]]] /neitvP //;
  rewrite /Rhull /= !(in_itv, inE)/= ?lte_bnd => xy.
- rewrite asboolT// inf_itv_bounded// lexx/= xy asboolT// asboolT//=.
  by rewrite asboolF//= sup_itv_bounded//= ltxx ?andbF.
- by rewrite asboolT// inf_itvcc// ?asboolT// ?sup_itvcc// ?lexx ?xy.
- by rewrite asboolT//= inf_itv_bnd_infty lexx asboolT// asboolF.
- rewrite asboolT// inf_itv_bounded//= ltxx asboolF// asboolT//.
  by rewrite sup_itv_bounded// ltxx andbF asboolF.
  rewrite asboolT // inf_itv_bounded // ltxx asboolF // asboolT //.
  by rewrite sup_itv_bounded // xy lexx asboolT.
- by rewrite asboolT // inf_itv_bnd_infty ltxx asboolF // asboolF.
- by rewrite asboolF // asboolT // sup_itv_infty_bnd ltxx asboolF.
- by rewrite asboolF // asboolT // sup_itv_infty_bnd lexx asboolT.
- by rewrite asboolF // asboolF.
Qed.

Lemma RhullT : Rhull setT = `]-oo, +oo[%R :> interval R.
Proof. by rewrite /Rhull -set_itv_infty_infty asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)),
  cancel (@Rhull R) (fun i => [set` i])}.
Proof.
move=> X /asboolP iX; rewrite /Rhull /mkset /= predeqE => r.
case: ifPn => /asboolP bX; last first.
  case: ifPn => /asboolP aX; last by rewrite (interval_unbounded_setT _ bX aX).
  rewrite in_itv /= negbK; have [|] := asboolP (X (sup X)) => XsupX /=.
    split => [|Xr].
      rewrite le_eqVlt => /predU1P[->//|rX].
      move/has_lbPn : bX => /(_ r)[y Xy yr].
      by move: (iX _ _ Xy XsupX); apply; rewrite (ltW yr) (ltW rX).
    by rewrite /mkset sup_ub //; exact/asboolP.
  split => [rX|Xr]; last exact: sup_ub_strict.
  by apply: interior_subset; rewrite interval_left_unbounded_interior.
case: ifPn => /asboolP uX.
  have [|] := asboolP (X (inf X)) => XinfX.
    rewrite in_itv /= negbK; have [|] := asboolP (X (sup X)) => XsupX /=.
      split=> [|Xr]; last first.
        by rewrite /mkset sup_ub // andbT inf_lb.
      move => /andP[]; rewrite le_eqVlt => /predU1P[<-//|infXr].
      rewrite le_eqVlt => /predU1P[->//|rsupX]; apply: interior_subset.
      by rewrite interval_bounded_interior //; rewrite /mkset infXr.
    split => [/andP[]|Xr].
      rewrite le_eqVlt => /predU1P[<-//|infXr rsupX]; apply: interior_subset.
      by rewrite interval_bounded_interior //; rewrite /mkset infXr.
    by rewrite /mkset inf_lb //= sup_ub_strict.
  have [|] := asboolP (X (sup X)) => XsupX /=.
    rewrite in_itv /=; split=> [/andP[infXr]|Xr]; last first.
      by rewrite inf_lb_strict // sup_ub.
    rewrite le_eqVlt => /predU1P[->//|rsupX]; apply: interior_subset.
    by rewrite interval_bounded_interior //; rewrite /mkset infXr.
  rewrite in_itv /=; split=> [/andP[infXr rsupX]|Xr]; last first.
    by rewrite inf_lb_strict // sup_ub_strict.
  apply: interior_subset.
  by rewrite interval_bounded_interior //; rewrite /mkset infXr.
rewrite in_itv /=; have [|] := asboolP (X (inf X)) => XinfX /=.
  rewrite andbT; split => [|Xr]; last exact: inf_lb.
  rewrite le_eqVlt => /predU1P[<-//|infXr].
  move/has_ubPn : uX => /(_ r)[y Xy yr].
  by move: (iX _ _ XinfX Xy); apply; rewrite (ltW infXr) (ltW yr).
rewrite andbT.
split=> [infXr|Xr]; last exact: inf_lb_strict.
by apply: interior_subset; rewrite interval_right_unbounded_interior.
Qed.

Lemma itv_c_inftyEbigcap x :
  `[x, +oo[%classic = \bigcap_k `]x - k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split=> /= [|xy].
  rewrite in_itv /= andbT => xy z _ /=; rewrite in_itv /= andbT ltr_subl_addr.
  by rewrite (le_lt_trans xy) // ltr_addl invr_gt0 ltr0n.
rewrite in_itv /= andbT leNgt; apply/negP => yx.
have {}[k ykx] := ltr_add_invr yx.
have {xy}/= := xy k Logic.I.
by rewrite in_itv /= andbT; apply/negP; rewrite -leNgt ler_subr_addr ltW.
Qed.

Lemma itv_bnd_inftyEbigcup b x : [set` Interval (BSide b x) +oo%O] =
  \bigcup_k [set` Interval (BSide b x) (BLeft k%:R)].
Proof.
rewrite predeqE => y; split=> /=; last first.
  by move=> [n _]/=; rewrite in_itv => /andP[xy yn]; rewrite in_itv /= xy.
rewrite in_itv /= andbT => xy; exists (`|floor y|%N.+1) => //=.
rewrite in_itv /= xy /= -addn1 natrD.
have [y0|y0] := ltP 0 y; last by rewrite (le_lt_trans y0)// ltr_spaddr.
rewrite natr_absz ger0_norm; last by rewrite floor_ge0 ltW.
by rewrite -RfloorE lt_succ_Rfloor.
Qed.

Lemma itv_o_inftyEbigcup x :
  `]x, +oo[%classic = \bigcup_k `[x + k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split => [|[n _]]/=.
  rewrite in_itv /= andbT => xy.
  have {}[k xky] := ltr_add_invr xy.
  by exists k => //=; rewrite in_itv /= (ltW xky).
rewrite in_itv /= andbT => xny.
by rewrite in_itv /= andbT (lt_le_trans _ xny) // ltr_addl invr_gt0.
Qed.

Lemma set_itv_setT (i : interval R) : [set` i] = setT -> i = `]-oo, +oo[.
Proof.
have [i0  /(congr1 (@Rhull _))|] := boolP (neitv i).
  by rewrite set_itvK// => ->; exact: RhullT.
by rewrite negbK => /eqP ->; rewrite predeqE => /(_ 0)[_]/(_ Logic.I).
Qed.

End set_itv_realType.

Lemma set_itv_ge [disp : unit] [T : porderType disp] [b1 b2 : itv_bound T] :
  ~~ (b1 < b2)%O -> [set` Interval b1 b2] = set0.
Proof. by move=> Nb12; rewrite -subset0 => x /=; rewrite itv_ge. Qed.

Definition contiguous_itv (R : realType) (i j : interval R) : bool :=
  (i.2 == j.1 :> itv_bound R).

Section conv_Rhull.
Variable R : realType.
Implicit Types (a b t r : R) (A : set R).

Lemma N01 t : (0 <= t <= 1) = (0 <= 1 - t <= 1).
Proof.
apply/idP/idP => /andP[t0 t1]; apply/andP; split; first by rewrite subr_ge0.
by rewrite ler_subl_addr addrC -ler_subl_addr subrr.
by move: t1; rewrite ler_subl_addr addrC -ler_subl_addr subrr.
by move: t0; rewrite subr_ge0.
Qed.

Definition conv t a b : R := (1 - t) * a + t * b.

Lemma conv0 a b : conv 0 a b = a.
Proof. by rewrite /conv subr0 mul1r mul0r addr0. Qed.

Lemma conv1 a b : conv 1 a b = b.
Proof. by rewrite /conv subrr mul0r add0r mul1r. Qed.

Lemma convN a b t : conv t a b = conv (1 - t) b a.
Proof. by rewrite /conv opprB addrCA subrr addr0 addrC. Qed.

Lemma le_conv a b t : a <= b -> 0 <= t <= 1 -> a <= conv t a b <= b.
Proof.
move=> ab /andP[].
rewrite le_eqVlt => /predU1P[/esym ->{t} _|t0]; first by rewrite conv0 lexx.
rewrite le_eqVlt => /predU1P[->{t0 t}|t1]; first by rewrite conv1 lexx andbT.
have t1t : 1 - t + t = 1 by rewrite subrK.
rewrite /conv; apply/andP; split.
  by rewrite -{1}(mul1r a) -{1}t1t [in X in X <= _]mulrDl ler_add // ler_pmul2l.
rewrite -{2}(mul1r b) -{2}t1t [in X in _ <= X]mulrDl ler_add // ler_pmul2l //.
by rewrite subr_gt0.
Qed.

Definition factor a b x := (x - a) / (b - a).

Lemma factor01 a b x : a != b -> a <= x -> x <= b -> 0 <= factor a b x <= 1.
Proof.
move=> ab ax xb; rewrite divr_ge0 // ?subr_ge0 // ?(le_trans ax) //=.
by rewrite ler_pdivr_mulr ?mul1r ?ler_sub// subr_gt0 lt_neqAle ab (le_trans ax).
Qed.

Lemma conv_factor a b x : a != b -> conv (factor a b x) a b = x.
Proof.
move=> ab; rewrite /conv -(@divff _ (b - a)) ?subr_eq0 1?eq_sym// -mulrBl.
rewrite opprB addrA subrK mulrAC (mulrAC (x - a)) -mulrDl 2!mulrBl.
rewrite -addrA (addrC (b * a)) -addrA (mulrC a b) subrK.
by rewrite -mulrN addrC -mulrDr -mulrA mulfV ?mulr1 // subr_eq0 eq_sym.
Qed.

Lemma conv_subset_Rhull A :
  [set x | exists a b t, [/\ A a, A b, 0 <= t <= 1 & x = conv t a b]]
    `<=` [set` Rhull A].
Proof.
move=> r -[a [b [t [Aa Ab /andP[t0 t1] ->{r}]]]].
have iRhullA := @interval_is_interval _ (Rhull A).
have [ab|/ltW ba] := leP a b.
  apply: (iRhullA a b); rewrite ?set_itv_mem; try exact/sub_Rhull.
  by rewrite le_conv // t0.
apply: (iRhullA b a); rewrite ?set_itv_mem; try exact/sub_Rhull.
by rewrite convN le_conv => //; rewrite -N01 t0.
Qed.

Lemma Rhull_subset_conv A : A !=set0 -> [set` Rhull A] `<=`
  [set x | exists a b t, [/\ A a, A b, 0 <= t <= 1 & x = conv t a b]].
Proof.
move=> A0 r; rewrite /Rhull; set i : R := inf A; set s : R := sup A.
have [|] := asboolP (has_lbound A) => lA.
- have [|]:= asboolP (has_ubound A) => uA.
  + have [|] := asboolP (A i) => Ai.
    * have [|] := asboolP (A s) => As; rewrite /= in_itv /= => /andP[ir rs].
      - have [si|si] := eqVneq i s.
        + have /eqP <- : i == r by rewrite eq_le {2}si ir.
          by exists i, s, 0; rewrite conv0 lexx ler01.
        + by exists i, s, (factor i s r); rewrite factor01 // conv_factor.
      - pose e := s - r.
        have [u ? seu] : exists2 u, A u & s - e < u.
          by apply sup_adherent; rewrite ?subr_gt0.
        have ? : i < u.
          rewrite (le_lt_trans _ seu)// (le_trans ir)// opprB addrCA subrr.
          by rewrite addr0.
        exists i, u, (factor i u r); rewrite factor01 ?conv_factor// ?lt_eqF//.
        by rewrite (le_trans _ (ltW seu))// /e opprB addrCA subrr addr0.
    * have [|] := asboolP (A s) => As; rewrite /= in_itv /= => /andP[ir rs].
      - pose e := r - i.
        have [l ? lie] : exists2 l, A l & l < i + e.
          by apply inf_adherent; rewrite ?subr_gt0.
        have ? : l < s.
          by rewrite (lt_le_trans lie)// (le_trans _ rs)// addrCA subrr addr0.
        exists l, s, (factor l s r); rewrite factor01// ?conv_factor// ?lt_eqF//.
        by rewrite (le_trans (ltW lie)) // /e addrCA subrr addr0.
      - pose e := ((r - i) `&` (s - r))%O.
        have [u ? seu] : exists2 u, A u & s - e < u.
          by apply sup_adherent; rewrite ?ltxI 2?subr_gt0 ?ir.
        have [l ? lie] : exists2 l, A l & l < i + e.
          by apply inf_adherent; rewrite ?ltxI 2?subr_gt0 ?ir.
        have ? : i + e <= r by rewrite -ler_sub_addl leIx lexx.
        have ? : r <= s - e.
          by rewrite -ler_sub_addr opprK -ler_sub_addl leIx lexx orbT.
        have ? : l < u.
           rewrite (lt_le_trans lie)// (le_trans _ (ltW seu))//.
           by rewrite (@le_trans _ _ r).
        exists l, u, (factor l u r); rewrite factor01// ?conv_factor// ?lt_eqF//.
          by rewrite (le_trans (ltW lie)).
        by rewrite (le_trans _ (ltW seu)).
  + have [|] := asboolP (A i) => /= Ai; rewrite in_itv /= andbT => ir.
    * have [u Au ru] : exists2 u, A u & r < u by move/has_ubPn : uA => /(_ r).
      have ? : i < u by rewrite (le_lt_trans ir).
      exists i, u, (factor i u r).
      by rewrite factor01// ?conv_factor // ?lt_eqF// ltW.
    * pose e := r - i.
      have [l ? lie] : exists2 l, A l & l < i + e
        by apply inf_adherent; rewrite ?subr_gt0.
      have [u ? ru] : exists2 u, A u & r < u
        by move/has_ubPn : uA => /(_ r).
      have ? : l < u by rewrite (lt_le_trans lie) // addrCA subrr addr0 ltW.
      have ? : l <= r by rewrite (le_trans (ltW lie)) // addrCA subrr addr0.
      exists l, u, (factor l u r).
      by rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
- have [|] := asboolP (has_ubound A) => uA; last move=> _.
  + have [|] := asboolP (A s) => /= As; rewrite in_itv /= => rs.
    * have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
      have ? : l < s by rewrite (lt_le_trans lr).
      exists l, s, (factor l s r).
      by rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
    * pose e := s - r.
      have [u ? seu] : exists2 u, A u & s - e < u.
        by apply sup_adherent; rewrite ?subr_gt0.
      have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
      have ? : l < u.
        rewrite (le_lt_trans _ seu)// (le_trans (ltW lr))// opprB addrCA.
        by rewrite subrr addr0.
      have ? : r <= u.
        by rewrite (le_trans _ (ltW seu))// opprB addrCA subrr addr0.
      exists l, u, (factor l u r).
      by rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
  + have [l ? lr] : exists2 l, A l & l < r by move/has_lbPn : lA => /(_ r).
    have [u ? ru] : exists2 u, A u & r < u by move/has_ubPn : uA => /(_ r).
    have ? : l < u by rewrite (lt_trans lr).
    exists l, u, (factor l u r).
    by rewrite factor01// ?conv_factor// ?lt_eqF// ltW.
Qed.

Lemma le_Rhull : {homo (@Rhull R) : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A; have [A0 B AB r|/set0P A0 B AB r] := eqVneq A set0.
  by rewrite A0 Rhull0 in_itv /= lt_asym.
move/(Rhull_subset_conv A0) => -[a [b [t [Aa Ab /andP[t0 t1] ->]]]].
by apply/conv_subset_Rhull; exists a, b, t; rewrite t0 t1; split=> //; exact/AB.
Qed.

Lemma neitv_Rhull A : ~~ neitv (Rhull A) -> A = set0.
Proof.
move/negPn/eqP => A0; rewrite predeqE => r; split => // /sub_Rhull.
by rewrite A0.
Qed.

Lemma Rhull_involutive A : Rhull [set` Rhull A] = Rhull A.
Proof.
have [A0|/neitv_Rhull] := boolP (neitv (Rhull A)); first by rewrite set_itvK.
by move=> ->; rewrite ?Rhull0 set_itvE Rhull0.
Qed.

End conv_Rhull.

Coercion ereal_of_itv_bound T (b : itv_bound T) : \bar T :=
  match b with BSide _ y => y%:E | +oo%O => +oo%E | -oo%O => -oo%E end.
Arguments ereal_of_itv_bound T !b.

Lemma le_bnd_ereal (R : realDomainType) (a b : itv_bound R) :
  (a <= b)%O -> (a <= b)%E.
Proof.
move: a b => -[[] a|[]] [bb b|[]] //=; rewrite ?(lee_pinfty,lee_ninfty)//.
  by rewrite BLeft_BSide_leE lee_fin.
by case: bb => //; rewrite BRight_BLeft_leE => /ltW; rewrite lee_fin.
Qed.

Lemma lt_ereal_bnd (R : realDomainType) (a b : itv_bound R) :
  (a < b)%E -> (a < b)%O.
Proof.
by move: a b => -[[] a|[]] [[] b|[]] //=;
  rewrite ?(lee_pinfty,lee_ninfty,lte_fin)// => ab; rewrite lte_bnd ltW.
Qed.

Lemma neitv_bnd1 (R : numFieldType) (s : seq (interval R)) :
  all neitv s -> forall i, i \in s -> i.1 != +oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo; move: si.
by rewrite boo => /sne /negP; apply; rewrite set_itv_infty_set0.
Qed.

Lemma neitv_bnd2 (R : numFieldType) (s : seq (interval R)) :
  all neitv s -> forall i, i \in s -> i.2 != -oo%O.
Proof.
move=> /allP sne [a b] si /=; apply/negP => /eqP boo; move: si.
by rewrite boo => /sne /negP; apply; rewrite set_itv_infty_set0.
Qed.

Lemma Interval_ereal_mem (R : realDomainType) (r : R) (a b : itv_bound R) :
  r \in Interval a b -> (a <= r%:E <= b)%E.
Proof.
case: a b => [[] a|[]] [[] b|[]] => /[dup] rab /itvP rw//=;
rewrite ?lee_fin ?rw//= ?lee_pinfty ?lee_ninfty//.
by move: rab; rewrite in_itv//= andbF.
Qed.

Lemma ereal_mem_Interval (R : realDomainType) (r : R) (a b : itv_bound R) :
  (a < r%:E < b)%E -> r \in Interval a b.
Proof.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite ?lte_fin ?in_itv //= => /andP[] //;
by do ?[move->|move/ltW|move=>_].
Qed.

Lemma trivIset_set_itv_nth (R : numDomainType) def (s : seq (interval R))
  (D : set nat) : [set` def] = set0 ->
  trivIset D (fun i => [set` nth def s i]) <->
    trivIset D (fun i => nth set0 [seq [set` j] | j <- s] i).
Proof.
move=> def0; split=> /trivIsetP ss; apply/trivIsetP => i j Di Dj ij.
- have [si|si] := ltP i (size s); last first.
    by rewrite (nth_default set0) ?size_map// set0I.
  have [sj|sj] := ltP j (size s); last first.
    by rewrite setIC (nth_default set0) ?size_map// set0I.
  by rewrite (nth_map def) // (nth_map def) // ss.
- have [?|h] := ltP i (size s); last by rewrite (nth_default def h) def0 set0I.
  have [?|h] := ltP j (size s); last by rewrite (nth_default def h) def0 setI0.
  by have := ss _ _ Di Dj ij; rewrite (nth_map def) // (nth_map def).
Qed.
Arguments trivIset_set_itv_nth {R} _ {s}.

Section disjoint_itv.
Context {R : numDomainType}.

Definition disjoint_itv : rel (interval R) :=
  fun a b => [disjoint [set` a] & [set` b]].

Lemma disjoint_itvxx (i : interval R) : neitv i -> ~~ disjoint_itv i i.
Proof. by move=> i0; rewrite /disjoint_itv/= /disj_set /= setIid. Qed.

Lemma lt_disjoint (i j : interval R) :
  (forall x y, x \in i -> y \in j -> x < y) -> disjoint_itv i j.
Proof.
move=> ij; apply/eqP; rewrite predeqE => x; split => // -[xi xj].
by have := ij _ _ xi xj; rewrite ltxx.
Qed.

End disjoint_itv.

Lemma disjoint_neitv {R : realFieldType} (i j : interval R) :
  disjoint_itv i j <-> ~~ neitv (itv_meet i j).
Proof.
case: i j => [a b] [c d]; rewrite /disjoint_itv/disj_set /= -set_itv_meet.
by split => [/negPn//|?]; apply/negPn.
Qed.

Lemma disj_itv_Rhull {R : realType} (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B -> disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK ?inE.
Qed.
