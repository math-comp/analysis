(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import fingroup perm rat archimedean finmap.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Export set_interval.
From HB Require Import structures.
From mathcomp Require Import reals interval_inference constructive_ereal.

(**md**************************************************************************)
(* # Sets and intervals on $\overline{\mathbb{R}}$                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
From mathcomp Require Import mathcomp_extra unstable.

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
    !(ltrBlDr, lerBlDr, ltrDl,lerDl)].
Qed.

Lemma has_inf_half x b (i : itv_bound R) : (BSide b x < i)%O ->
  has_inf [set` Interval (BSide b x) i].
Proof.
move: b i => [] [[]y|[]]; rewrite ?bnd_simp => xy; do 1?[
  by split=> //; exists ((x + y) / 2);
     rewrite !set_itvE/= !(midf_le,midf_lt) //;
     exact: ltW
 | by split => //; exists (x + 1); rewrite !set_itvE/= !(ltrDl,lerDl)].
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
- apply: ge_sup; last by move=> ? /ltW.
  by exists (x - 1); rewrite !set_itvE/= ltrBlDr ltrDl.
- rewrite leNgt; apply/negP => sx; pose p := (s + x) / 2.
  suff /andP[?]: (p < x) && (s < p) by apply/negP; rewrite -leNgt ub_le_sup.
  by rewrite !midf_lt.
Qed.

Let inf_itv_bnd_infty x b : inf [set` Interval (BSide b x) +oo%O] = x.
Proof.
case: b; last by rewrite /inf opp_itv_bndy sup_itv_infty_bnd opprK.
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
by rewrite /inf opp_itv_bnd_bnd sup_itv_o_bnd ?opprK // ltrNl opprK.
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

Lemma itvNycEbigcap b x : `]-oo, x]%classic =
  \bigcap_k [set` Interval -oo%O (BSide b (x + k.+1%:R^-1))].
Proof.
apply/seteqP; split => /= [r/=|r].
- rewrite in_itv/= => xr k _/=; rewrite in_itv/=; case: b => /=.
  + by rewrite (le_lt_trans xr)// ltrDl.
  + by rewrite (le_trans xr)// lerDl.
- move=> br/=; rewrite in_itv/= leNgt; apply/negP => /ltr_add_invr[k rkx].
  have /= {br} := br k Logic.I; rewrite in_itv/=; case: b => /=.
  + by apply/negP; rewrite -leNgt ltW.
  + by rewrite leNgt rkx.
Qed.

Lemma itvcyEbigcap x :
  `[x, +oo[%classic = \bigcap_k `]x - k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split=> /= [|xy].
  rewrite in_itv /= andbT => xy z _ /=; rewrite in_itv /= andbT ltrBlDr.
  by rewrite (le_lt_trans xy) // ltrDl invr_gt0 ltr0n.
rewrite in_itv /= andbT leNgt; apply/negP => yx.
have {}[k ykx] := ltr_add_invr yx.
have {xy}/= := xy k Logic.I.
by rewrite in_itv /= andbT; apply/negP; rewrite -leNgt lerBrDr ltW.
Qed.

Lemma itvbndyEbigcup b x : [set` Interval (BSide b x) +oo%O] =
  \bigcup_k [set` Interval (BSide b x) (BLeft k%:R)].
Proof.
rewrite predeqE => y; split=> /=; last first.
  by move=> [n _]/=; rewrite in_itv => /andP[xy yn]; rewrite in_itv /= xy.
rewrite in_itv /= andbT => xy; exists (truncn y).+1 => //=.
by rewrite in_itv /= xy /= truncnS_gt.
Qed.

Lemma itvNybndEbigcup b x : [set` Interval -oo%O (BSide b x)] =
  \bigcup_k [set` Interval (BRight (- k%:R)) (BSide b x)].
Proof.
rewrite predeqE => y; split=> /=; last first.
  by move=> [n _]/=; rewrite in_itv => /andP[ny yx]; rewrite in_itv.
rewrite in_itv /= => yx; exists (truncn `|y|).+1 => //=; rewrite in_itv/=.
by rewrite yx /= andbT ltrNl (le_lt_trans (ler_norm _))// normrN truncnS_gt.
Qed.

Lemma itvoyEbigcup x :
  `]x, +oo[%classic = \bigcup_k `[x + k.+1%:R^-1, +oo[%classic.
Proof.
rewrite predeqE => y; split => [|[n _]]/=.
  rewrite in_itv /= andbT => xy.
  have {}[k xky] := ltr_add_invr xy.
  by exists k => //=; rewrite in_itv /= (ltW xky).
rewrite in_itv /= andbT => xny.
by rewrite in_itv /= andbT (lt_le_trans _ xny) // ltrDl invr_gt0.
Qed.

End set_itv_realType.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `itvcyEbigcap`")]
Notation itv_c_inftyEbigcap := itvcyEbigcap (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `itvbndyEbigcup`")]
Notation itv_bnd_inftyEbigcup := itvbndyEbigcup (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `itvoyEbigcup`")]
Notation itv_o_inftyEbigcup := itvoyEbigcup (only parsing).

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

Let E n := [set x | f x - g x >= n.+1%:R^-1%:E].

Lemma set_lte_bigcup : [set x | f x > g x] = \bigcup_n E n.
Proof.
apply/seteqP; split => [x/=|x [n _]]; last first.
  by rewrite /E/= -sube_gt0; apply: lt_le_trans.
move gxE : (g x) => gx; case: gx gxE => [gx| |gxoo fxoo]; last 2 first.
  - by case: (f x).
  - by exists 0%N => //; rewrite /E/= gxoo addey// ?leey// -ltNye.
move fxE : (f x) => fx; case: fx fxE => [fx fxE gxE|fxoo gxE _|//]; last first.
  by exists 0%N => //; rewrite /E/= fxoo gxE// addye// leey.
rewrite lte_fin -subr_gt0 => fgx; exists (truncn (fx - gx)^-1) => //.
by rewrite /E/= fxE gxE lee_fin invf_ple ?posrE//; apply/ltW/truncnS_gt.
Qed.

End set_ereal.

Lemma set1_bigcap_oc (R : realType) (r : R) :
  [set r] = \bigcap_i `]r - i.+1%:R^-1, r]%classic.
Proof.
apply/seteqP; split=> [x ->|].
  by move=> i _/=; rewrite in_itv/= lexx ltrBlDr ltrDl invr_gt0 ltr0n.
move=> x rx; apply/esym/eqP; rewrite eq_le (itvP (rx 0%N _))// andbT.
apply/ler_addgt0Pl => e e_gt0; rewrite -lerBlDl ltW//.
have := rx (truncn e^-1) I; rewrite /= in_itv => /andP[/le_lt_trans->]//.
by rewrite lerB// invf_ple ?posrE//; apply/ltW/truncnS_gt.
Qed.

Lemma itv_bnd_open_bigcup (R : realType) b (r s : R) :
  [set` Interval (BSide b r) (BLeft s)] =
  \bigcup_n [set` Interval (BSide b r) (BRight (s - n.+1%:R^-1))].
Proof.
apply/seteqP; split => [|]; last first.
  move=> x [n _ /=] /[!in_itv] /andP[-> /le_lt_trans]; apply.
  by rewrite ltrBlDr ltrDl invr_gt0 ltr0n.
move=> x/= /[!in_itv]/= /andP[sx xs]; exists (truncn (s - x)^-1) => //=.
rewrite in_itv/= sx/= lerBrDl addrC -lerBrDl -[leRHS]invrK.
by rewrite lef_pV2 ?posrE ?ltr0n// ?invr_gt0 ?subr_gt0// ltW// truncnS_gt.
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

Lemma itv_bndy_bigcup_BLeft_shift {R : archiRealDomainType} b (x : R) n:
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_i [set` Interval (BSide b x) (BLeft (x + (i + n)%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists (truncn (y - x)).+1 => //=.
by rewrite in_itv/= xy/= natrD addrA ltr_wpDr// -ltrBDl truncnS_gt.
Qed.

Lemma itv_bndy_bigcup_BRight (R : archiRealDomainType) b (x : R) :
  [set` Interval (BSide b x) +oo%O] =
  \bigcup_n [set` Interval (BSide b x) (BRight (x + n%:R))].
Proof.
apply/seteqP; split=> y; rewrite /= !in_itv/= andbT; last first.
  by move=> [k _ /=]; move: b => [|] /=; rewrite in_itv/= => /andP[//] /ltW.
move=> xy; exists (truncn (y - x)).+1 => //=; rewrite in_itv/= xy/= -lerBlDl.
by rewrite ltW// truncnS_gt.
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `itv_bndy_bigcup_BRight`")]
Notation itv_bnd_infty_bigcup := itv_bndy_bigcup_BRight (only parsing).

Lemma itv0y_bigcup0S (R : realType) :
  `[0, +oo[%classic = \bigcup_n `[0, n.+1%:R]%classic :> set R.
Proof.
rewrite eqEsubset; split; last first.
  by move=> /= x [n _]/=; rewrite !in_itv/= => /andP[->].
rewrite itv_bndy_bigcup_BRight => z [n _ /= zn].
exists n => //=; apply: subset_itvl zn.
by rewrite bnd_simp/= add0r ler_nat.
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `itv0y_bigcup0S`")]
Notation itv_bnd_infty_bigcup0S := itv0y_bigcup0S (only parsing).

Lemma itvNy_bnd_bigcup_BLeft (R : realType) b (x : R) :
  [set` Interval -oo%O (BSide b x)] =
  \bigcup_i [set` Interval (BLeft (x - i%:R)) (BSide b x)].
Proof.
have /(congr1 (fun x => -%R @` x)) := itv_bndy_bigcup_BRight (~~ b) (- x).
rewrite opp_itv_bndy negbK opprK => ->; rewrite image_bigcup.
apply eq_bigcupr => k _; apply/seteqP; split=> [_ /= -[r rbxk <-]|y/= yxkb].
  by rewrite oppr_itv/= opprB addrC.
by exists (- y); [rewrite oppr_itv/= negbK opprD opprK|rewrite opprK].
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `itvNy_bnd_bigcup_BLeft`")]
Notation itv_infty_bnd_bigcup := itvNy_bnd_bigcup_BLeft (only parsing).

Lemma bigcup_itvT {R : archiRealDomainType} b1 b2 :
  \bigcup_n [set` Interval (BSide b1 (- n%:R)) (BSide b2 n%:R)] = [set: R].
Proof.
rewrite -subTset => x _ /=; exists (truncn `|x|).+1 => //=.
have := truncnS_gt `|x|; rewrite in_itv/=; move: b1 b2 => [] []/=.
- by rewrite ltr_norml => /andP[/ltW ->].
- by move/ltW; rewrite ler_norml => /andP[-> ->].
- by rewrite ltr_norml => /andP[-> ->].
- by rewrite ltr_norml => /andP[-> /ltW].
Qed.
