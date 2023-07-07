(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Export set_interval.
From HB Require Import structures.
Require Import reals ereal signed topology normedtype sequences.

(******************************************************************************)
(* This files contains lemmas about sets and intervals on reals.              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section interval_has.
Variable R : realType.
Implicit Types x : R.

Lemma has_sup_half x b (i : itv_bound R) : (i < BSide b x)%O ->
  has_sup [set` Interval i (BSide b x)].
Proof.
move: b i => [] [[]y|[]]; rewrite ?bnd_simp => xy; split=> //; do 1?[
  by exists ((x + y) / 2); rewrite !set_itvE/= addrC !(midf_le,midf_lt) //;
    exact: ltW
| by exists (x - 1); rewrite !set_itvE/=
    !(ltr_subl_addr, ler_subl_addr, ltr_addl,ler_addl)].
Qed.

Lemma has_inf_half x b (i : itv_bound R) : (BSide b x < i)%O ->
  has_inf [set` Interval (BSide b x) i].
Proof.
move: b i => [] [[]y|[]]; rewrite ?bnd_simp => xy; do 1?[
  by split=> //; exists ((x + y) / 2);
     rewrite !set_itvE/= !(midf_le,midf_lt) //;
     exact: ltW
 | by split => //; exists (x + 1); rewrite !set_itvE/= !(ltr_addl,ler_addl)].
Qed.

End interval_has.

#[global]
Hint Extern 0 (has_sup _) => solve[apply: has_sup1 | exact: has_sup_half] : core.
#[global]
Hint Extern 0 (has_inf _) => solve[apply: has_inf1 | exact: has_inf_half]: core.

Section interval_sup_inf.
Variable R : realType.
Implicit Types x y : R.

Let sup_itv_infty_bnd x b : sup [set` Interval -oo%O (BSide b x)] = x.
Proof.
case: b; last first.
  by rewrite -setUitv1// sup_setU ?sup1// => ? ? ? ->; exact/ltW.
set s := sup _; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub; last by move=> ? /ltW.
  by exists (x - 1); rewrite !set_itvE/= ltr_subl_addr ltr_addl.
- rewrite leNgt; apply/negP => sx; pose p := (s + x) / 2.
  suff /andP[?]: (p < x) && (s < p) by apply/negP; rewrite -leNgt sup_ub.
  by rewrite !midf_lt.
Qed.

Let inf_itv_bnd_infty x b : inf [set` Interval (BSide b x) +oo%O] = x.
Proof.
case: b; last by rewrite /inf opp_itv_bnd_infty sup_itv_infty_bnd opprK.
rewrite -setU1itv// inf_setU ?inf1// => _ b ->.
by rewrite !set_itvE => /ltW.
Qed.

Let sup_itv_o_bnd x y b : x < y ->
  sup [set` Interval (BRight x) (BSide b y)] = y.
Proof.
case: b => xy; last first.
  by rewrite -setUitv1// sup_setU ?sup1// => ? ? /andP[? /ltW ?] ->.
set B := [set` _]; set A := `]-oo, x]%classic.
rewrite -(@sup_setU _ A B) //.
- rewrite -(sup_itv_infty_bnd y true); congr sup.
  rewrite predeqE => u; split=> [[|/andP[]//]|yu].
  by rewrite /A !set_itvE => /le_lt_trans; apply.
  by have [xu|ux] := ltP x u; [right; rewrite /B !set_itvE/= xu| left].
- by move=> u v; rewrite /A /B => ? /andP[xv _]; rewrite (le_trans _ (ltW xv)).
Qed.

Let sup_itv_bounded x y a b : (BSide a x < BSide b y)%O ->
  sup [set` Interval (BSide a x) (BSide b y)] = y.
Proof.
case: a => xy; last exact: sup_itv_o_bnd.
case: b in xy *.
  by rewrite -setU1itv// sup_setU ?sup_itv_o_bnd// => ? ? -> /andP[/ltW].
by rewrite -setUitv1// sup_setU ?sup1// => ? ? /andP[_ /ltW ? ->].
Qed.

Let inf_itv_bnd_o x y b : (BSide b x < BLeft y)%O ->
  inf [set` Interval (BSide b x) (BLeft y)] = x.
Proof.
case: b => xy.
  by rewrite -setU1itv// inf_setU ?inf1// => _ ? -> /andP[/ltW].
by rewrite /inf opp_itv_bnd_bnd sup_itv_o_bnd ?opprK // ltr_oppl opprK.
Qed.

Let inf_itv_bounded x y a b : (BSide a x < BSide b y)%O ->
  inf [set` Interval (BSide a x) (BSide b y)] = x.
Proof.
case: b => xy; first exact: inf_itv_bnd_o.
case: a in xy *.
  by rewrite -setU1itv// inf_setU ?inf1// => ? ? -> /andP[/ltW].
by rewrite -setUitv1// inf_setU ?inf_itv_bnd_o// => ? ? /andP[? /ltW ?] ->.
Qed.

Lemma sup_itv a b x : (a < BSide b x)%O ->
  sup [set` Interval a (BSide b x)] = x.
Proof. by case: a => [b' y|[]]; rewrite ?bnd_simp//= => /sup_itv_bounded->. Qed.

Lemma inf_itv a b x : (BSide b x < a)%O ->
  inf [set` Interval (BSide b x) a] = x.
Proof. by case: a => [b' y|[]]; rewrite ?bnd_simp//= => /inf_itv_bounded->. Qed.

Lemma sup_itvcc x y : x <= y -> sup `[x, y] = y.
Proof. by move=> *; rewrite sup_itv. Qed.

Lemma inf_itvcc x y : x <= y -> inf `[x, y] = x.
Proof. by move=> *; rewrite inf_itv. Qed.

End interval_sup_inf.

Section set_itv_realType.
Variable R : realType.
Implicit Types x : R.

Lemma set_itvK : {in neitv, cancel pred_set (@Rhull R)}.
Proof.
move=> [[[] x|[]] [[] y|[]]] /neitvP //;
  rewrite /Rhull /= !(in_itv, inE)/= ?bnd_simp => xy.
- rewrite asboolT// inf_itv// lexx/= xy asboolT// asboolT//=.
  by rewrite asboolF//= sup_itv//= ltxx ?andbF.
- by rewrite asboolT// inf_itv// ?asboolT// ?sup_itv// ?lexx ?xy.
- by rewrite asboolT//= inf_itv// lexx asboolT// asboolF.
- rewrite asboolT// inf_itv//= ltxx asboolF// asboolT//.
  by rewrite sup_itv// ltxx andbF asboolF.
  rewrite asboolT // inf_itv // ltxx asboolF // asboolT //.
  by rewrite sup_itv // xy lexx asboolT.
- by rewrite asboolT // inf_itv// ltxx asboolF // asboolF.
- by rewrite asboolF // asboolT // sup_itv// ltxx asboolF.
- by rewrite asboolF // asboolT // sup_itv// lexx asboolT.
- by rewrite asboolF // asboolF.
Qed.

Lemma RhullT : Rhull setT = `]-oo, +oo[%R :> interval R.
Proof. by rewrite /Rhull -set_itv_infty_infty asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)), cancel (@Rhull R) pred_set}.
Proof. by move=> X /asboolP iX; apply/esym/is_intervalP. Qed.

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
rewrite in_itv /= andbT => xy; exists `|floor y|%N.+1 => //=.
rewrite in_itv /= xy /=.
have [y0|y0] := ltP 0 y; last by rewrite (le_lt_trans y0)// ltr_spaddr.
by rewrite -natr1 natr_absz ger0_norm ?floor_ge0 1?ltW// lt_succ_floor.
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

Section Rhull_lemmas.
Variable R : realType.
Implicit Types (a b t r : R) (A : set R).

Lemma Rhull_smallest A : [set` Rhull A] = smallest (@is_interval R) A.
Proof.
apply/seteqP; split; last first.
  by apply: smallest_sub; [apply: interval_is_interval | apply: sub_Rhull].
move=> x /= + I [Iitv AI]; rewrite /Rhull.
have [|] := asboolP (has_lbound A) => lA; last first.
  have /forallNP/(_ x)/existsNP[a] := lA.
  move=> /existsNP[Aa /negP]; rewrite -ltNge => ax.
  have [|]:= asboolP (has_ubound A) => uA; last first.
    move=> ?; have /forallNP/(_ x)/existsNP[b] := uA.
    move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
    have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
    by rewrite ax xb.
  have [As|NAs]/= := asboolP (A _) => xA.
    by apply: (Iitv a (sup A)); by [apply: AI | rewrite ltW ?ax].
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists a | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [|]:= asboolP (has_ubound A) => uA; last first.
  have /forallNP/(_ x)/existsNP[b] := uA.
  move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
  have [Ai|NAi]/= := asboolP (A _) => xA.
    by apply: (Iitv (inf A) b); by [apply: AI | rewrite (ltW xb)].
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists b | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [Ai|NAi]/= := asboolP (A _); have [As|NAs]/= := asboolP (A _).
- by apply: Iitv; apply: AI.
- move=> xA.
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists (inf A) | rewrite (itvP xA)].
  have /(_ (inf A) b) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW xb).
- move=> xA.
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists (sup A) | rewrite (itvP xA)].
  have /(_ a (sup A)) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW ax).
have [->|/set0P AN0] := eqVneq A set0.
  by rewrite inf0 sup0 itv_ge//= ltBSide/= ltxx.
move=> xA.
have [||a Aa ax] := @inf_lt _ A x; do ?by [|rewrite (itvP xA)].
have [||b Ab xb] := @sup_gt _ A x; do ?by [|rewrite (itvP xA)].
have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
by rewrite ax xb.
Qed.

Lemma le_Rhull : {homo (@Rhull R) : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A B AB; suff: [set` Rhull A] `<=` [set` Rhull B] by [].
rewrite Rhull_smallest; apply: smallest_sub; first exact: interval_is_interval.
by rewrite Rhull_smallest; apply: sub_smallest.
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

End Rhull_lemmas.

Coercion ereal_of_itv_bound T (b : itv_bound T) : \bar T :=
  match b with BSide _ y => y%:E | +oo%O => +oo%E | -oo%O => -oo%E end.
Arguments ereal_of_itv_bound T !b.

Section itv_realDomainType.
Context (R : realDomainType).

Lemma le_bnd_ereal (a b : itv_bound R) : (a <= b)%O -> (a <= b)%E.
Proof.
move: a b => -[[] a|[]] [bb b|[]] //=; rewrite ?(leey,leNye)//.
  by rewrite bnd_simp.
by move=> /lteifW.
Qed.

Lemma lt_ereal_bnd (a b : itv_bound R) : (a < b)%E -> (a < b)%O.
Proof.
by move: a b => -[[] a|[]] [[] b|[]] //=;
  rewrite ?(lee_pinfty,lee_ninfty,lte_fin)// => ab; rewrite bnd_simp ltW.
Qed.

Lemma Interval_ereal_mem (r : R) (a b : itv_bound R) :
  r \in Interval a b -> (a <= r%:E <= b)%E.
Proof.
case: a b => [[] a|[]] [[] b|[]] => /[dup] rab /itvP rw//=;
by rewrite ?lee_fin ?rw//= ?leey ?leNye//; move: rab; rewrite in_itv//= andbF.
Qed.

Lemma ereal_mem_Interval (r : R) (a b : itv_bound R) :
  (a < r%:E < b)%E -> r \in Interval a b.
Proof.
move: a b => [[]a|[]] [[]b|[]] //=; rewrite ?lte_fin ?in_itv //= => /andP[] //;
by do ?[move->|move/ltW|move=>_].
Qed.

Lemma itv_cyy : `[+oo%E, +oo[%classic = [set +oo%E] :> set (\bar R).
Proof.
by rewrite set_itvE predeqE => t; split => /= [|<-//]; rewrite leye_eq => /eqP.
Qed.

Lemma itv_oyy : `]+oo%E, +oo[%classic = set0 :> set (\bar R).
Proof.
by rewrite set_itvE predeqE => t; split => //=; apply/negP; rewrite -leNgt leey.
Qed.

Lemma itv_cNyy : `[-oo%E, +oo[%classic = setT :> set (\bar R).
Proof. by rewrite set_itvE predeqE => t; split => //= _; rewrite leNye. Qed.

Lemma itv_oNyy : `]-oo%E, +oo[%classic = ~` [set -oo]%E :> set (\bar R).
Proof.
rewrite set_itvE predeqE => x; split => /=.
- by move: x => [x| |]; rewrite ?ltxx.
- by move: x => [x h|//|/(_ erefl)]; rewrite ?ltNyr.
Qed.

End itv_realDomainType.

Section set_ereal.
Context (R : realType) T (f g : T -> \bar R).
Local Open Scope ereal_scope.

Let E j := [set x | f x - g x >= j.+1%:R^-1%:E].

Lemma set_lte_bigcup : [set x | f x > g x] = \bigcup_j E j.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  by rewrite /E/= -sube_gt0; apply: lt_le_trans.
move gxE : (g x) => gx; case: gx gxE => [gx| |gxoo fxoo]; last 2 first.
  - by case: (f x).
  - by exists 0%N => //; rewrite /E/= gxoo addey// ?leey// -ltNye.
move fxE : (f x) => fx; case: fx fxE => [fx fxE gxE|fxoo gxE _|//]; last first.
  by exists 0%N => //; rewrite /E/= fxoo gxE// addye// leey.
rewrite lte_fin -subr_gt0 => fgx; exists `|floor (fx - gx)^-1%R|%N => //.
rewrite /E/= -natr1 natr_absz ger0_norm ?floor_ge0 ?invr_ge0; last exact/ltW.
rewrite fxE gxE lee_fin -[leRHS]invrK lef_pinv//.
- by apply/ltW; rewrite lt_succ_floor.
- by rewrite posrE// ltr_spaddr// ler0z floor_ge0 invr_ge0 ltW.
- by rewrite posrE invr_gt0.
Qed.

End set_ereal.

Lemma disj_itv_Rhull {R : realType} (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B -> disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK ?inE.
Qed.

Lemma set1_bigcap_oc (R : realType) (r : R) :
  [set r] = \bigcap_i `]r - i.+1%:R^-1, r]%classic.
Proof.
apply/seteqP; split=> [x ->|].
  by move=> i _/=; rewrite in_itv/= lexx ltr_subl_addr ltr_addl invr_gt0 ltr0n.
move=> x rx; apply/esym/eqP; rewrite eq_le (itvP (rx 0%N _))// andbT.
apply/ler_addgt0Pl => e e_gt0; rewrite -ler_subl_addl ltW//.
have := rx `|floor e^-1%R|%N I; rewrite /= in_itv => /andP[/le_lt_trans->]//.
rewrite ler_add2l ler_opp2 -lef_pinv ?invrK//; last by rewrite qualifE.
by rewrite -natr1 natr_absz ger0_norm ?floor_ge0 ?invr_ge0 1?ltW// lt_succ_floor.
Qed.

Lemma itv_bnd_open_bigcup (R : realType) b (r s : R) :
  [set` Interval (BSide b r) (BLeft s)] =
  \bigcup_n [set` Interval (BSide b r) (BRight (s - n.+1%:R^-1))].
Proof.
apply/seteqP; split => [x/=|]; last first.
  move=> x [n _ /=] /[!in_itv] /andP[-> /le_lt_trans]; apply.
  by rewrite ltr_subl_addr ltr_addl invr_gt0 ltr0n.
rewrite in_itv/= => /andP[sx xs]; exists `|ceil ((s - x)^-1)|%N => //=.
rewrite in_itv/= sx/= ler_subr_addl addrC -ler_subr_addl.
rewrite -[in X in _ <= X](invrK (s - x)) ler_pinv.
- rewrite -natr1 natr_absz ger0_norm; last first.
    by rewrite ceil_ge0// invr_ge0 subr_ge0 ltW.
  by rewrite (@le_trans _ _ (ceil (s - x)^-1)%:~R)// ?ler_addl// ceil_ge.
- by rewrite inE unitfE ltr0n andbT pnatr_eq0.
- by rewrite inE invr_gt0 subr_gt0 xs andbT unitfE invr_eq0 subr_eq0 gt_eqF.
Qed.

Lemma itv_open_bnd_bigcup (R : realType) b (r s : R) :
  [set` Interval (BRight s) (BSide b r)] =
  \bigcup_n [set` Interval (BLeft (s + n.+1%:R^-1)) (BSide b r)].
Proof.
have /(congr1 (fun x => -%R @` x)) := itv_bnd_open_bigcup (~~ b) (- r) (- s).
rewrite opp_itv_bnd_bnd/= !opprK negbK => ->; rewrite image_bigcup.
apply eq_bigcupr => k _; apply/seteqP; split=> [_/= [y ysr] <-|x/= xsr].
  by rewrite oppr_itv/= opprD.
by exists (- x); rewrite ?oppr_itv//= opprK// negbK opprB opprK addrC.
Qed.

Lemma itv_bnd_infty_bigcup (R : realType) b (x : R) :
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BRight (x + i%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists `|ceil (y - x)|%N => //=; rewrite in_itv/= xy/= -ler_subl_addl.
rewrite !natr_absz/= ger0_norm ?ceil_ge0 ?subr_ge0 ?ceil_ge//.
by case: b xy => //= /ltW.
Qed.

Lemma itv_infty_bnd_bigcup (R : realType) b (x : R) :
  [set` Interval -oo%O (BSide b x)] =
  \bigcup_i [set` Interval (BLeft (x - i%:R)) (BSide b x)].
Proof.
have /(congr1 (fun x => -%R @` x)) := itv_bnd_infty_bigcup (~~ b) (- x).
rewrite opp_itv_bnd_infty negbK opprK => ->; rewrite image_bigcup.
apply eq_bigcupr => k _; apply/seteqP; split=> [_ /= -[r rbxk <-]|y/= yxkb].
   by rewrite oppr_itv/= opprB addrC.
by exists (- y); [rewrite oppr_itv/= negbK opprD opprK|rewrite opprK].
Qed.

Lemma bigcup_itvT {R : realType} b :
  \bigcup_i [set` Interval (BSide b (- i%:R)) (BRight i%:R)] = [set: R].
Proof.
rewrite -subTset => x _ /=; exists `|(floor `|x| + 1)%R|%N => //=.
rewrite in_itv/= !natr_absz intr_norm intrD.
have : `|x| < `|(floor `|x|)%:~R + 1|.
  by rewrite [ltRHS]ger0_norm ?lt_succ_floor// addr_ge0// ler0z floor_ge0.
case: b => /=.
- by move/ltW; rewrite ler_norml => /andP[-> ->].
- by rewrite ltr_norml => /andP[-> /ltW->].
Qed.

Require Import nsatz_realtype.

Lemma geo_partial_tail {R : fieldType} (n m : nat) (x : R) : 
  \sum_(m <= i < m + n) x^+i = series (geometric (x^+m) x) n.
Proof.
elim: n; first by rewrite ?big_geq /series /= ?addn0 // big_geq.
move=> n IH; rewrite /series/geometric /= addnS ?big_nat_recl ?leq_addr //.
rewrite expr0 mulr1 -mulr_sumr ; under eq_fun => ? do rewrite exprS.
rewrite -?mulr_sumr IH /series/geometric/= -?mulr_sumr.
by rewrite mulrC -mulrA [_ * x]mulrC mulr_sumr.
Qed.

Lemma geometric_le_lim {R : realType} (n : nat) (a x : R) :
  (0 <= a) -> 0 < x -> `|x| < 1 -> series (geometric a x) n <= (a * (1 - x)^-1).
Proof.
move=> a0 x0 x1.
have /(@cvg_unique _ (@Rhausdorff R)) := @cvg_geometric_series _ a _ x1.
move/(_ _ (@is_cvg_geometric_series _ a _ x1)) => ->.
apply: nondecreasing_cvg_le; last exact: is_cvg_geometric_series.
by apply: nondecreasing_series => ? _ /=; rewrite pmulr_lge0 // exprn_gt0 //. 
Qed. 

Section UniformPointwise.
Context {U : topologicalType} {V : uniformType}.

Lemma pointwise_cvgP F (f: U -> V):
  Filter F -> {ptws, F --> f} <-> forall (t : U), (fun g => g t) @ F --> f t.
Proof.
move=> Ff; rewrite pointwise_cvg_family_singleton; split.
  move/fam_cvgP => + t A At => /(_ [set t]); rewrite uniform_set1; apply => //.
  by exists t.
move=> pf; apply/fam_cvgP => ? [t _ <-]; rewrite uniform_set1; apply: pf.
Qed.
End UniformPointwise.

Section Tietze.

Context {X : topologicalType} {R : realType} (A : set X).
Hypothesis clA : closed A.
Hypothesis urysohn_ext : forall A B x y,
  closed A -> closed B -> A `&` B = set0 -> x <= y ->
  exists (f : X -> R^o), 
    [/\ continuous f, f @` A = [set x], f @` B = [set y] & range f `<=` `[x,y]].

Let three0 : 0 < 3 :> R.
Proof. by rewrite (_ : 0 = 0%:R) // ltr_nat. Qed.

Let threen0 : 3 != 0 :> R.
Proof. exact: lt0r_neq0. Qed.

Let thirds : -1/3 < 1/3 :>R.
Proof.
by rewrite ltr_pdivr_mulr // div1r mulVf // ?gtr_opp.
Qed.

Local Lemma tietze_step' (f : X -> R^o) (M : R) :
  0 < M -> {within A, continuous f} ->
  (forall x, A x -> `|f x| <= M) ->
  exists (g : X -> R^o), [/\ continuous g, 
     (forall x, A x -> `|f x - g x| <= 2/3*M :>R)
     & (forall x, `|g x| <= 1/3*M)].
Proof.
move=> mpos ctsf fA1.
have [] := @urysohn_ext (A `&` f@^-1` `]-oo,-1/3 *M]) ( A `&` f@^-1` `[1/3 * M,+oo[) (-1/3 * M) (1/3 * M).
- by rewrite closed_setSI; apply: closed_comp => //.
- by rewrite closed_setSI; apply: closed_comp => //; exact: interval_closed.
- rewrite setIACA -preimage_setI eqEsubset; split => z //.
  case=> _ []; rewrite ?set_itvE /= => /[swap] /le_trans /[apply].
  rewrite ler_pmul2r //.
  by move=> W; move: thirds => /=; rewrite real_ltNge ?num_real // W.
- by rewrite ler_pmul2r //; exact: ltW.
move=> g [ctsg gL3 gR3 grng]; exists g; split => //; first last.
  by move=> x; rewrite ler_norml -?mulNr; apply: grng; exists x.
move=> x Ax; move: (fA1 _ Ax); rewrite ?ler_norml /= => /andP [? ?].
case xL : (f x <= -1/3 * M).
  have : [set g x | x in A `&` f@^-1` `]-oo, -1/3 * M]] (g x) by exists x.
  rewrite gL3 => ->; rewrite ?mulNr opprK; apply/andP; split.
    by rewrite -ler_subl_addr -opprD -?mulrDl (_ : 2+1 = 3) ?divrr ?unitfE ?mul1r // addrC. 
  rewrite -ler_subr_addr -?mulNr -?mulrDl (_ : 2-1 = 1).
    by apply: (le_trans xL); rewrite ler_pmul2r //; apply: ltW.
  by rewrite (_ : 2 = (1+1)) // -addrA subrr addr0.
case xR : (1/3 *M <= f x).
  have : [set g x | x in A `&` f@^-1` `[1/3 *M, +oo[] (g x).
    by exists x => //; split => //; rewrite /= in_itv //= xR.
  rewrite gR3 => ->; apply/andP; split.
    rewrite -ler_subl_addr opprK -?mulNr // -?mulrDl.
    rewrite (_ : 1*-2 = -(1 + 1)) // opprD -addrA [-_ + _]addrC -addrA subrr addr0. 
    by apply: (le_trans _ xR); rewrite ler_pmul2r //; apply: ltW.
  by rewrite -ler_subr_addr opprK -?mulrDl addrC divrr ?mul1r ?unitfE //; exact: threen0.
have /andP [/ltW nf3 /ltW pf3] : -1/3 *M < f x < 1/3 *M.
  by apply/andP; split; rewrite real_ltNge ?num_real //= ?xL ?xR.
have /andP [ng3 pg3] : -1/3 * M <= g x <= 1/3 * M by apply: grng; exists x.
apply/andP; split.
  by rewrite (_ : 2 = 1 + 1) // ?mulrDl ?opprD; apply: ler_sub; rewrite // -?mulNr.
by rewrite (_ : 2 = 1 + 1) // ?mulrDl; apply: ler_add; rewrite // ler_oppl -?mulNr.
Qed.

Let tietze_step (f : X -> R^o) M : 
  {g : X -> R^o | 
  {within A, continuous f} -> 0 < M -> 
  (forall x, A x -> `|f x| <= M) ->
   [/\ continuous g, 
     (forall x, A x -> `|f x - g x| <= 2/3*M :>R)
     & (forall x, `|g x| <= 1/3*M)]}.
Proof.
apply: cid.
case : (pselect ({within A, continuous f})); last by move => ?; exists point.
case : (pselect (0 < M)); last by move => ?; exists point.
case : (pselect (forall x, A x -> `|f x| <=M)); last by move => ?; exists point.
by move=> bd pm cf; have [g ?] := tietze_step' pm cf bd; exists g.
Qed.

Let twothirds_pos : 0 < 2/3 :>R.
Proof. exact: divr_gt0 => //. Qed.

Let onethird_pos : 0 < 1/3 :>R.
Proof. exact: divr_gt0 => //. Qed.

Let twothirds := PosNum twothirds_pos.
Let onethird := PosNum onethird_pos.

Lemma tietze (f : X -> R^o) M :
  (0 < M) -> {within A, continuous f} -> (forall x, A x -> `|f x| <= M) ->
  exists g, [/\ {in A, f =1 g}, continuous g & forall x, `|g x| <= M].
Proof.
move: M => _/posnumP[M] ctsf fbd; pose M2d3 n := M%:num*(twothirds%:num)^+n.
have MN0 n : 0 < M2d3 n by rewrite /M2d3.
pose f_ := fix F n := 
  if n is n.+1 then (F n - projT1 (tietze_step (F n) (M2d3 n))) else f.
pose g_ n := projT1 (tietze_step (f_ n) (M2d3 n)).
have fgE n : f_ n - f_ n.+1 = g_ n .
  by rewrite /= opprB addrC -addrA [-_ + _] addrC subrr addr0.
have twothirds1 : `|twothirds%:num| < 1 :> R.
 by rewrite ger0_norm // ltr_pdivr_mulr // mul1r (_ : 3 = 1 + 2) // ltr_addr. 
have f_geo n :
  {within A, continuous f_ n} /\
  (forall x, A x -> `|f_ n x| <= geometric M%:num twothirds%:num n).
  elim: n; first by split => // ? ?; rewrite /= expr0 mulr1; exact: fbd.
  move=> n [ctsN bdN].
  have [cg bdNS bd2] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdN.
  split; first by move=> x; apply: cvgB; [exact: ctsN | exact/continuous_subspaceT/cg].
  rewrite /geometric /= exprS mulrA [M%:num * (_/_)] mulrC -[_ * M%:num * _]mulrA.
  exact: bdNS.
have g_cts n : continuous (g_ n).
  have [ctsN bdfN] := f_geo n.
  by have [] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdfN.
have g_bd n : forall x, `|g_ n x| <= geometric (onethird%:num * M%:num) (twothirds%:num) n.
  have [ctsN bdfN] := f_geo n; rewrite /geometric /= -[_ * M%:num * _]mulrA.
  by have [] := projT2 (tietze_step (f_ n) _) ctsN (MN0 n) bdfN.
pose h_ : nat -> [completeType of {uniform X -> _}] := 
  @series [zmodType of {uniform X -> _}] g_.
have cvgh' : cvg (h_ @ \oo).
  apply/cauchy_cvgP/cauchy_ballP => eps epos; near_simpl.
  suff : \forall x & x' \near \oo, (x' <= x)%N -> ball (h_ x) eps (h_ x').
    move=>/[dup]; rewrite {1}near_swap; apply: filter_app2; near=> n m => /=.
    by have /orP [mn /(_ mn)/ball_sym + _| ? _] := leq_total n m; apply. 
  near=> n m; move=> /= MN; rewrite /ball /= /ball /= /h_ => t; rewrite /ball /=. 
  have -> : (series g_ n t - series g_ m t  = (series g_ n - series g_ m) t) by done.
  rewrite sub_series MN. 
  rewrite fct_sumE; (apply: le_lt_trans; first exact: ler_norm_sum) => /=.
  apply: le_lt_trans; first exact: (ler_sum _ (fun i _ => g_bd i t)).
  rewrite -mulr_sumr -(subnKC MN) geo_partial_tail.
  apply: (@le_lt_trans _ _ (onethird%:num * M%:num * ((twothirds%:num)^+m / (1-twothirds%:num)))).
    by rewrite ler_pmul2l //; apply geometric_le_lim => //. 
  have -> : (1-twothirds%:num = onethird%:num).
    rewrite -(@divrr _ 3) /= ?unitfE // -mulrBl; congr(_ _ _); apply/eqP.
    by rewrite subr_eq.
  rewrite [_^+_ * _^-1]mulrC mulrA -[x in x < _]ger0_norm; last done.
  near: m; near_simpl; move: eps epos; 
  apply: (@cvgr0_norm_lt _ _ _ _ _ (fun m => ( _ * _^+m):R^o)).
  exact: cvg_geometric.
have cvgh : {uniform, h_ @ \oo --> lim (h_ @ \oo)}. 
  by move=> ?; rewrite /= ?uniform_nbhsT; apply: cvgh'.
exists (lim (h_ @ \oo)); split.
- move=> t /set_mem At.
  have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) := !! pointwise_uniform_cvg _ cvgh.
  rewrite -fmap_comp /comp /h_ => <-; apply: esym. 
  apply: (@cvg_lim _ (@Rhausdorff R)). 
  apply: (@cvg_zero R [pseudoMetricNormedZmodType R of R^o]). 
  apply: norm_cvg0; under eq_fun => n. 
    rewrite distrC /series /cst /= -mulN1r fct_sumE mulr_sumr.
    under [fun (_ : nat) => _]eq_fun => ? do rewrite mulN1r -fgE opprB.
    rewrite telescope_sumr //= addrC -addrA [-_ + _]addrC subrr addr0.
    over.
  apply/norm_cvg0P/cvgr0Pnorm_lt => eps epos.
  have /(_ _ epos)  := @cvgr0_norm_lt R _ nat _ eventually_filter (_ : nat -> R^o)
    (cvg_geometric (M%:num :R^o) twothirds1).
  apply: filter_app; near_simpl; apply: nearW => n /le_lt_trans; apply.
  apply: le_trans; first by case: (f_geo n) => _; apply.
  exact: ler_norm.
- apply: (@uniform_limit_continuous X _ (h_ @\oo) (lim (h_ @ \oo))) =>//.
  near_simpl; apply: nearW; elim.
    by rewrite /h_ /=/series /= ?big_geq // => ?; exact: cvg_cst.
  move=> n; rewrite /h_ /series /= big_nat_recr /= // => IH t.
  rewrite [_ + g_ _]/GRing.add /=; apply: cvgD; first exact: (IH t).
  exact: g_cts.
- move=> t.
  have /pointwise_cvgP/(_ t)/(cvg_lim (@Rhausdorff _)) := !! pointwise_uniform_cvg _ cvgh.
  rewrite -fmap_comp /comp /h_ => <-. 
  under [fun (_:nat) => _]eq_fun => ? do rewrite /series /= fct_sumE.
  have ? : cvg ([normed series (g_^~ t)] : nat -> R^o).
    apply: (series_le_cvg _ _ (fun n => g_bd n t) ).
    - by move=> ?; done.
    - by move=> ?; rewrite /geometric /mk_sequence //.
    - exact: is_cvg_geometric_series.
  apply: le_trans; first exact: lim_series_norm. 
  apply: le_trans; first apply: (lim_series_le _ _ (fun n => g_bd n t)) => //.
    exact: is_cvg_geometric_series.
  rewrite (cvg_lim _ (cvg_geometric_series _)) => //.
  have -> : (1-twothirds%:num = onethird%:num).
    rewrite -(@divrr _ 3) /= ?unitfE // -mulrBl; congr(_ _ _); apply/eqP.
    by rewrite subr_eq.
  rewrite mulrAC divrr ?mul1r // unitfE //.
Unshelve. all: by end_near. Qed.
    
  apply: limr_le => //; apply: nearW => n.
  apply: le_trans. 
    rewrite /normed_series_of /=/series /=.
    Search ((\sum_(_ <= _ < _) _) <= _).
    apply: lee_sum.
    apply lee_nneseries.
  apply: le_nseries.
  have <- := (@lim_norm _ _ _ _ _ (fun x => \sum_(0 <= i < x) g_ i t)); first last.
    apply: normed_cvg.

    apply: series_le_cvg (geometric ).
    Search series cvg_to (_ <= _).

  
exists (lim h_).
  

fix C n := if n is n.+1 then u @` C n else A `\` B.










