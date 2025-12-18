(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions.

(**md**************************************************************************)
(* # Sets and Intervals                                                       *)
(*                                                                            *)
(* This files contains lemmas about sets and intervals.                       *)
(*                                                                            *)
(* ```                                                                        *)
(*              neitv i == the interval i is non-empty                        *)
(*                         when the support type is a numFieldType, this      *)
(*                         is equivalent to (i.1 < i.2)%O (lemma neitvE)      *)
(*   set_itv_infty_set0 == multirule to simplify empty intervals              *)
(*      line_path a b t := (1 - t) * a + t * b, convexity operator over a     *)
(*                         numDomainType                                      *)
(*          ndline_path == line_path a b with the constraint that a < b       *)
(*         factor a b x := (x - a) / (b - a)                                  *)
(*             set_itvE == multirule to turn intervals into inequalities      *)
(*     disjoint_itv i j == intervals i and j are disjoint                     *)
(*         itv_is_ray i == i is either `]x, +oo[ or `]-oo, x[                 *)
(*     itv_is_bd_open i == i is `]x, y[                                       *)
(*      itv_open_ends i == i has open endpoints, i.e., it is one of the two   *)
(*                         above                                              *)
(*        is_open_itv A == the set A can be written as an open interval       *)
(*     open_itv_cover A == the set A can be covered by open intervals         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** definitions and lemmas to make a bridge between MathComp intervals and
    classical sets *)
Section set_itv_porderType.
Variables (disp : Order.disp_t) (T : porderType disp).
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

Lemma in1_subset_itv (P : T -> Prop) i j :
  [set` j] `<=` [set` i] -> {in i, forall x, P x} -> {in j, forall x, P x}.
Proof. by move=> /subset_itvP ji iP z zB; apply: iP; exact: ji. Qed.

Lemma subset_itvW x y z u b0 b1 :
    (x <= y)%O -> (z <= u)%O ->
  `]y, z[ `<=` [set` Interval (BSide b0 x) (BSide b1 u)].
Proof.
move=> xy zu; apply: (@subset_trans _ `]x, u[%classic).
  move=> x0/=; rewrite 2!in_itv/= => /andP[].
  by move=> /(le_lt_trans xy) ->/= /lt_le_trans; exact.
by move: b0 b1 => [] [] /=; [exact: subset_itv_oo_co|exact: subset_itv_oo_cc|
  exact: subset_refl|exact: subset_itv_oo_oc].
Qed.

Lemma subset_itvl (a b c : itv_bound T) : (b <= c)%O ->
  [set` Interval a b] `<=` [set` Interval a c].
Proof. by move=> /subitvPr /subsetP h; apply/subsetP => x /h. Qed.

Lemma subset_itvr (a b c : itv_bound T) : (c <= a)%O ->
  [set` Interval a b] `<=` [set` Interval c b].
Proof. by move=> /subitvPl /subsetP h; apply/subsetP => x /h. Qed.

Lemma subset_itv (a b c d : itv_bound T) : (c <= a)%O -> (b <= d)%O ->
  [set` Interval a b] `<=` [set` Interval c d].
Proof. by move=> ac bd; apply/(subset_trans (subset_itvl _))/subset_itvr. Qed.

Lemma subset_itvScc (a b : itv_bound T) (c e : T) :
    (BLeft c <= a)%O -> (b <= BRight e)%O ->
  [set` Interval a b] `<=` [set` `[c, e]].
Proof.
move=> ca be z/=; rewrite !in_itv/==> /andP[az zb].
case: a ca az => [[|]/=|[|]//] a; rewrite bnd_simp => ca az.
- rewrite (le_trans ca az)/=.
  move: b be zb => [[|]/= b|[|]//]; rewrite bnd_simp => be.
    by move=> /ltW/le_trans; exact.
  by move=> /le_trans; exact.
- rewrite (le_trans ca (ltW az))/=.
  move: b be zb => [[|]/= b|[|]//]; rewrite bnd_simp => be.
    by move=> /ltW/le_trans; exact.
  by move=> /le_trans; exact.
Qed.

Lemma subset_itvSoo (a b : itv_bound T) (c e : T) :
    (BLeft c < a)%O -> (b < BRight e)%O ->
  [set` Interval a b] `<=` [set` `]c, e[].
Proof.
move=> ca be z/=; rewrite !in_itv/= => /andP[az zb].
case: a ca az => [[|]/=|[|]//] a; rewrite bnd_simp => ca az.
  rewrite (lt_le_trans ca az)/=.
  move: b be zb => [[|]/= b|[|]//]; rewrite bnd_simp => be.
    by move=> /lt_le_trans; exact.
  by move=> /le_lt_trans; exact.
rewrite (le_lt_trans ca az)/=.
move: b be zb => [[|]/= b|[|]//]; rewrite bnd_simp => be.
  by move=> /lt_le_trans; exact.
by move=> /le_lt_trans; exact.
Qed.

Lemma set_itvoo x y : `]x, y[%classic = [set z | (x < z < y)%O].
Proof. by []. Qed.

Lemma set_itvco x y : `[x, y[%classic = [set z | (x <= z < y)%O].
Proof. by []. Qed.

Lemma set_itvcc x y : `[x, y]%classic = [set z | (x <= z <= y)%O].
Proof. by []. Qed.

Lemma set_itvoc x y : `]x, y]%classic = [set z | (x < z <= y)%O].
Proof. by []. Qed.

Lemma set_itv1 x : `[x, x]%classic = [set x].
Proof. by apply/seteqP; split=> y /=; rewrite itvxx ?inE (rwP eqP). Qed.

Lemma set_itvoo0 x : `]x, x[%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itvoc0 x : `]x, x]%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itvco0 x : `[x, x[%classic = set0.
Proof. by rewrite -subset0 => y /=; rewrite itv_ge//= bnd_simp ltxx. Qed.

Lemma set_itvNyy : `]-oo, +oo[%classic = @setT T.
Proof. by rewrite predeqE. Qed.

Lemma set_itvoy x : `]x, +oo[%classic = [set z | (x < z)%O].
Proof. by rewrite predeqE => r /=; rewrite in_itv andbT. Qed.

Lemma set_itvcy x : `[x, +oo[%classic = [set z | (x <= z)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv andbT. Qed.

Lemma set_itvNyo x : `]-oo, x[%classic = [set z | (z < x)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itvNyc x : `]-oo, x]%classic = [set z | (z <= x)%O].
Proof. by rewrite predeqE /mkset => r; rewrite in_itv. Qed.

Lemma set_itv_ybnd a : [set` Interval +oo%O a] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd. Qed.

Lemma set_itv_bndNy a : [set` Interval a -oo%O] = set0.
Proof. by apply/eqP/negPn/negP => /neitv_lt_bnd /=; case: a => [[]a|[]]. Qed.

Definition set_itv_infty_set0 := (set_itv_bndNy, set_itv_ybnd).

Definition set_itvE := (set_itv1, set_itvoo0, set_itvoc0, set_itvco0, set_itvoo,
  set_itvcc, set_itvoc, set_itvco, set_itvNyy, set_itvoy,
  set_itvcy, set_itvNyo, set_itvNyc, set_itv_infty_set0).

Lemma set_itvxx a : [set` Interval a a] = set0.
Proof. by move: a => [[|] a |[|]]; rewrite !set_itvE. Qed.

Lemma setUitv1 a x : (a <= BLeft x)%O ->
  [set` Interval a (BLeft x)] `|` [set x] = [set` Interval a (BRight x)].
Proof.
move=> ax; apply/predeqP => z /=; rewrite itv_splitU1// [in X in _ <-> X]inE.
by rewrite (rwP eqP) (rwP orP) orbC.
Qed.

Lemma setU1itv a x : (BRight x <= a)%O ->
  x |` [set` Interval (BRight x) a] = [set` Interval (BLeft x) a].
Proof.
move=> ax; apply/predeqP => z /=; rewrite itv_split1U// [in X in _ <-> X]inE.
by rewrite (rwP eqP) (rwP orP) orbC.
Qed.

Lemma setDitv1r a x :
  [set` Interval a (BRight x)] `\ x = [set` Interval a (BLeft x)].
Proof.
apply/seteqP; split => [z|z] /=; rewrite !in_itv/=.
  by move=> [/andP[-> /= zx] /eqP xz]; rewrite lt_neqAle xz.
by rewrite lt_neqAle => /andP[-> /andP[/eqP ? ->]].
Qed.

Lemma setDitv1l a x :
  [set` Interval (BLeft x) a] `\ x = [set` Interval (BRight x) a].
Proof.
apply/seteqP; split => [z|z] /=; rewrite !in_itv/=.
  move=> [/andP[xz ->]]; rewrite andbT => /eqP.
  by rewrite lt_neqAle eq_sym => ->.
move=> /andP[]; rewrite lt_neqAle => /andP[xz zx ->].
by rewrite andbT; split => //; exact/nesym/eqP.
Qed.

End set_itv_porderType.
Arguments neitv {disp T} _.
#[deprecated(since="mathcomp-analysis 1.4.0", note="renamed to `subset_itvScc`")]
Notation subset_itvS := subset_itvScc (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itvNyy`")]
Notation set_itv_infty_infty := set_itvNyy (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itvoy`")]
Notation set_itv_o_infty := set_itvoy (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itvcy`")]
Notation set_itv_c_infty := set_itvcy (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itvNyo`")]
Notation set_itv_infty_o := set_itvNyo (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itvNyc`")]
Notation set_itv_infty_c := set_itvNyc (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itv_ybnd`")]
Notation set_itv_pinfty_bnd := set_itv_ybnd (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed to `set_itv_bndNy`")]
Notation set_itv_bnd_ninfty := set_itv_bndNy (only parsing).
#[deprecated(since="mathcomp-analysis 1.15.0", note="use `set_itv1` instead")]
Notation interval_set1 := set_itv1 (only parsing).

Section set_itv_orderType.
Variables (d : Order.disp_t) (T : orderType d).
Implicit Types a b x y : itv_bound T.

Lemma itv_bndbnd_setU a x y : (a <= x)%O -> (x <= y)%O ->
  ([set` Interval a y] = [set` Interval a x] `|` [set` Interval x y])%classic.
Proof.
rewrite le_eqVlt => /predU1P[<-{x} ay|]; first by rewrite set_itvxx set0U.
move=> /[swap].
rewrite le_eqVlt => /predU1P[-> ay|]; first by rewrite set_itvxx setU0.
move: y => [yb y/=|[|]]; last 2 first.
  by case: x => [|[|]].
  move=> _ ax; apply/seteqP; split => [z|z] /=.
    rewrite !in_itv/= !andbT => -> /=; apply/orP.
    by move: x => [[|] x/=|[|]//] in ax *; rewrite leNgt ?(orbN,orNb).
  rewrite !in_itv/= !andbT => -[/andP[]|]//.
  move: x => [[|] x/=|[|]//] in ax *; move: a => [[|] a/=|[|]//] in ax * => //.
  - by apply/le_trans; exact/ltW.
  - exact/lt_le_trans.
  - by move=> /(le_lt_trans ax) /ltW.
  - exact/lt_trans.
move=> xy ax; apply/seteqP; split => [z|z] /=.
  rewrite !in_itv /= => /andP[].
  move: a ax => [b t /=|[]//= oox _].
    move=> tx -> zxy /=; rewrite zxy andbT/=; apply/orP.
    by case: x xy tx => [[|] x/=|[|]//] xy tx; rewrite leNgt ?(orbN,orNb).
  move=> ->; rewrite andbT; apply/orP.
  by move: x => [[|] x/=|[|]//] in oox xy *; rewrite leNgt ?(orbN,orNb).
rewrite !in_itv/=.
move: a ax => [b t /= tx| [/= oox|/= oox]].
- move=> [/andP[-> zx]|].
    move: x => [[|] x|[|]//]/= in xy tx zx *.
      case: yb => /= in xy *.
        by rewrite (lt_trans zx _).
      by rewrite (ltW (lt_le_trans zx _)).
    rewrite bnd_simp in xy.
    case: yb => /=.
      by rewrite (le_lt_trans zx _).
    by rewrite (ltW (le_lt_trans zx _)).
  move: x => [[|] x|[|]//]/= in xy tx *; rewrite bnd_simp in xy tx.
  + move=> /andP[xz ->]; rewrite andbT.
    case: b => /=.
      by rewrite (le_trans _ xz)// ltW.
    by rewrite (lt_le_trans tx).
  move=> /andP[xz ->]; rewrite andbT.
  case: b tx => /= tx; rewrite bnd_simp in tx.
    by rewrite ltW// (le_lt_trans _ xz).
  by rewrite (lt_trans tx).
- move: x => [[|] x|[|]//]/= in xy oox *; move=> [|].
  + case: yb => /= in xy *.
      by move=> /lt_trans; exact.
    rewrite bnd_simp in xy.
    by move=> /lt_le_trans => /(_ _ xy)/ltW.
  + by move=> /andP[].
  + case: yb => /= in xy *.
      by move=> /le_lt_trans; apply.
    by move=> /le_trans; apply; exact/ltW.
  + by move=> /andP[].
- by move: x => [[|] x|[|]//]/= in xy oox *.
Qed.

Lemma set_itv_splitU a b (c : T) : c \in Interval a b ->
  [set` Interval a b] `\ c =
    [set` Interval a (BLeft c)] `|` [set` Interval (BRight c) b].
Proof.
move=> cab; apply/seteqP; split => [x /= [xab /eqP]|x[|]]/=.
- rewrite neq_lt => /orP[xc|cx]; [left|right].
  + move: cab xab; rewrite !itv_boundlr => /andP[ac cb] /andP[ax xb].
    by rewrite ax/= bnd_simp.
  + move: cab xab; rewrite !itv_boundlr => /andP[ac cb] /andP[ax xb].
    by rewrite xb andbT bnd_simp.
- move: cab; rewrite !itv_boundlr => /andP[ac cb] /andP[ax].
  rewrite bnd_simp => xc.
  rewrite ax/= (le_trans _ cb) ?bnd_simp ?(ltW xc)//; split => //.
  by apply/eqP; rewrite lt_eqF.
- move: cab; rewrite !itv_boundlr => /andP[ac cb] /andP[+ xb].
  rewrite bnd_simp => cx.
  rewrite xb/= andbT (le_trans ac)/= ?bnd_simp ?(ltW cx)//; split => //.
  by apply/eqP; rewrite gt_eqF.
Qed.

End set_itv_orderType.

Lemma set_itv_ge disp [T : porderType disp] [b1 b2 : itv_bound T] :
  ~~ (b1 < b2)%O -> [set` Interval b1 b2] = set0.
Proof. by move=> Nb12; rewrite -subset0 => x /=; rewrite itv_ge. Qed.

Section set_itv_latticeType.
Variables (d : Order.disp_t) (T : latticeType d).
Implicit Types (i j : interval T) (x y : T) (a : itv_bound T).

Lemma set_itvI i j :  [set` (i `&` j)%O] = [set` i] `&` [set` j].
Proof. by apply/seteqP; split=> x /=; rewrite in_itvI (rwP andP). Qed.

End set_itv_latticeType.

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

Lemma setitv0 (R : realDomainType) : [set` (\bot%O : interval R)] = set0.
Proof. by rewrite predeqE. Qed.

Section interval_has_bound.
Variable R : numDomainType.

Lemma has_lbound_itv (x : R) b (a : itv_bound R) :
  has_lbound [set` Interval (BSide b x) a].
Proof. by case: b; exists x => r /andP[]; rewrite bnd_simp // => /ltW. Qed.

Lemma has_ubound_itv (x : R) b (a : itv_bound R) :
  has_ubound [set` Interval a (BSide b x)].
Proof. by case: b; exists x => r /andP[]; rewrite bnd_simp // => _ /ltW. Qed.

End interval_has_bound.

Section subr_image.
Variable R : numDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma setNK : involutive (fun E => -%R @` E).
Proof.
move=> A; rewrite image_comp (_ : _ \o _ = id) ?image_id//.
by rewrite funeqE => r /=; rewrite opprK.
Qed.

Lemma lb_ubN E x : lbound E x <-> ubound (-%R @` E) (- x).
Proof.
split=> [/lbP xlbE|/ubP xlbE].
by move=> _ [z Ez <-]; rewrite lerNr opprK; apply xlbE.
by move=> y Ey; rewrite -(opprK x) lerNl; apply xlbE; exists y.
Qed.

Lemma ub_lbN E x : ubound E x <-> lbound (-%R @` E) (- x).
Proof.
split=> [? | /lb_ubN]; first by apply/lb_ubN; rewrite opprK setNK.
by rewrite opprK setNK.
Qed.

Lemma memNE E x : E x = (-%R @` E) (- x).
Proof. by rewrite image_inj //; exact: oppr_inj. Qed.

Lemma nonemptyN E : nonempty (-%R @` E) <-> nonempty E.
Proof.
split=> [[x ENx]|[x Ex]]; exists (- x); last by rewrite -memNE.
by rewrite memNE opprK.
Qed.

Lemma opp_set_eq0 E : (-%R @` E) = set0 <-> E = set0.
Proof. by split; apply: contraPP => /eqP/set0P/nonemptyN/set0P/eqP. Qed.

Lemma has_lb_ubN E : has_lbound E <-> has_ubound (-%R @` E).
Proof.
by split=> [[x /lb_ubN] | [x /ub_lbN]]; [|rewrite setNK]; exists (- x).
Qed.

End subr_image.

Section interval_hasNbound.
Variable R : realDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma has_ubPn {E} : ~ has_ubound E <-> (forall x, exists2 y, E y & x < y).
Proof.
split; last first.
  move=> h [x] /ubP hle; case/(_ x): h => y /hle.
  by rewrite leNgt => /negbTE ->.
move/forallNP => h x; have {h} := h x.
move=> /ubP /existsNP => -[y /not_implyP[Ey /negP]].
by rewrite -ltNge => ltx; exists y.
Qed.

Lemma has_lbPn E : ~ has_lbound E <-> (forall x, exists2 y, E y & y < x).
Proof.
split=> [/has_lb_ubN /has_ubPn NEnub x|Enlb /has_lb_ubN].
  have [y ENy ltxy] := NEnub (- x); exists (- y); rewrite 1?ltrNl //.
  by case: ENy => z Ez <-; rewrite opprK.
apply/has_ubPn => x; have [y Ey ltyx] := Enlb (- x).
exists (- y); last by rewrite ltrNr.
by exists y => //; rewrite opprK.
Qed.

Lemma hasNlbound_itv (a : itv_bound R) : a != -oo%O ->
  ~ has_lbound [set` Interval -oo%O a].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_lbound `]-oo, r[%classic.
    by case: b => //; apply/contra_not/subset_has_lbound => x /ltW.
  apply/has_lbPn => x; exists (minr (r - 1) (x - 1)).
    by rewrite !set_itvE/= gt_min ltrBlDr ltrDl ltr01.
  by rewrite gt_min orbC ltrBlDr ltrDl ltr01.
case=> r /(_ (r - 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltrBlDr ltrDl.
Qed.

Lemma hasNubound_itv (a : itv_bound R) : a != +oo%O ->
  ~ has_ubound [set` Interval a +oo%O].
Proof.
move: a => [b r|[|]] _ //.
  suff: ~ has_ubound `]r, +oo[%classic.
    case: b => //; apply/contra_not/subset_has_ubound => x.
    by rewrite !set_itvE => /ltW.
  apply/has_ubPn => x; rewrite !set_itvE; exists (maxr (r + 1) (x + 1));
  by rewrite ?in_itv /= ?andbT lt_max ltrDl ltr01 // orbT.
case=> r /(_ (r + 1)) /=; rewrite in_itv /= => /(_ erefl).
by apply/negP; rewrite -ltNge ltrDl.
Qed.

End interval_hasNbound.

#[global] Hint Extern 0 (has_lbound _) => solve[apply: has_lbound_itv] : core.
#[global] Hint Extern 0 (has_ubound _) => solve[apply: has_ubound_itv] : core.
#[global]
Hint Extern 0 (~ has_lbound _) => solve[by apply: hasNlbound_itv] : core.
#[global]
Hint Extern 0 (~ has_ubound _) => solve[by apply: hasNubound_itv] : core.

Lemma opp_itv_bndy (R : numDomainType) (x : R) b :
  -%R @` [set` Interval (BSide b x) +oo%O] =
  [set` Interval -oo%O (BSide (negb b) (- x))].
Proof.
rewrite predeqE => /= r; split=> [[y xy <-]|xr].
  by case: b xy; rewrite !in_itv/= andbT (lerN2, ltrN2).
exists (- r); rewrite ?opprK //.
by case: b xr; rewrite !in_itv/= andbT (lerNr, ltrNr).
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `opp_itv_bndy`")]
Notation opp_itv_bnd_infty := opp_itv_bndy (only parsing).

Lemma opp_itvNy_bnd (R : numDomainType) (x : R) b :
  -%R @` [set` Interval -oo%O (BSide b x)] =
  [set` Interval (BSide (negb b) (- x)) +oo%O].
Proof.
rewrite predeqE => /= r; split=> [[y xy <-]|xr].
  by case: b xy; rewrite !in_itv/= andbT (lerN2, ltrN2).
exists (- r); rewrite ?opprK //.
by case: b xr; rewrite !in_itv/= andbT (lerNl, ltrNl).
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `opp_itvNy_bnd`")]
Notation opp_itv_infty_bnd := opp_itvNy_bnd (only parsing).

Lemma opp_itv_bnd_bnd (R : numDomainType) a b (x y : R) :
  -%R @` [set` Interval (BSide a x) (BSide b y)] =
  [set` Interval (BSide (~~ b) (- y)) (BSide (~~ a) (- x))].
Proof.
rewrite predeqE => /= r; split => [[{}r + <-]|].
  by rewrite !in_itv/= 2!lteifN2 negbK andbC.
rewrite in_itv/= negbK => yrab.
by exists (- r); rewrite ?opprK// !in_itv lteifNr andbC lteifNl.
Qed.

Lemma opp_itvoo (R : numDomainType) (x y : R) :
  -%R @` `]x, y[%classic = `](- y), (- x)[%classic.
Proof.
rewrite predeqE => /= r; split => [[{}r + <-]|].
  by rewrite !in_itv/= !ltrN2 andbC.
by exists (- r); rewrite ?opprK// !in_itv/= ltrNl ltrNr andbC.
Qed.

(** lemmas between itv and set-theoretic operations *)
Section set_itv_porderType.
Variables (d : Order.disp_t) (T : porderType d).
Implicit Types (a : itv_bound T) (x y : T) (i j : interval T) (b : bool).

Lemma set_itv_splitI i : [set` i] = [set` Interval i.1 +oo%O] `&` [set` Interval -oo%O i.2].
Proof.
case: i => [a a']; apply/predeqP=> x/=.
by rewrite [in X in X <-> _]itv_splitI (rwP andP).
Qed.

End set_itv_porderType.

Section set_itv_orderType.
Variables (d : Order.disp_t) (T : orderType d).
Implicit Types (a : itv_bound T) (x y : T) (i j : interval T) (b : bool).

Lemma setCitvl a : ~` [set` Interval -oo%O a] = [set` Interval a +oo%O].
Proof. by apply/predeqP => y /=; rewrite -predC_itvl (rwP negP). Qed.

Lemma setCitvr a : ~` [set` Interval a +oo%O] = [set` Interval -oo%O a].
Proof. by rewrite -setCitvl setCK. Qed.

Lemma setCitv i :
  ~` [set` i] = [set` Interval -oo%O i.1] `|` [set` Interval i.2 +oo%O].
Proof.
by apply/predeqP => x /=; rewrite (rwP orP) (rwP negP) [x \notin i]predC_itv.
Qed.

Lemma set_itv_splitD i :
  [set` i] = [set` Interval i.1 +oo%O] `\` [set` Interval i.2 +oo%O].
Proof. by rewrite set_itv_splitI/= setDE setCitvr. Qed.

Lemma itv_setU_setT b x :
  [set` Interval -oo%O (BSide b x)] `|`
  [set` Interval (BSide b x) +oo%O] = [set: T].
Proof. by rewrite -itv_bndbnd_setU// set_itvE. Qed.

End set_itv_orderType.

Section line_path_factor_numDomainType.
Variable R : numDomainType.
Implicit Types (a b t r : R) (A : set R).

Lemma memB_itv (x y : bool) a b t :
  (b - t \in Interval (BSide x a) (BSide y b)) =
  (a + t \in Interval (BSide (~~ y) a) (BSide (~~ x) b)).
Proof.
rewrite !in_itv/= /Order.lteif !if_neg.
by rewrite gerBl gtrBl lerDl ltrDl lerBrDr ltrBrDr andbC.
Qed.

Lemma memB_itv0 (x y : bool) (a b : R) :
  (b - a \in Interval (BSide x 0) (BSide y b)) =
  (a \in Interval (BSide (~~ y) 0) (BSide (~~ x) b)).
Proof. by rewrite memB_itv add0r. Qed.

Lemma __deprepcated__mem_1B_itvcc t : (1 - t \in `[0, 1]) = (t \in `[0, 1]).
Proof. exact: memB_itv0. Qed.

Definition line_path a b t : R := (1 - t) * a + t * b.

Lemma line_path_id : line_path 0 1 = id.
Proof. by apply/funext => t; rewrite /line_path mulr0 add0r mulr1. Qed.

Lemma line_pathEl a b t : line_path a b t = t * (b - a) + a.
Proof. by rewrite /line_path mulrBl addrAC -addrA -mulrBr mul1r addrC. Qed.

Lemma line_pathEr a b t : line_path a b t = (1 - t) * (a - b) + b.
Proof. by rewrite mulrBl mul1r addrAC subrK -mulrN opprB addrC line_pathEl. Qed.

Lemma line_path10 t : line_path 1 0 t = 1 - t.
Proof. by rewrite /line_path mulr0 addr0 mulr1. Qed.

Lemma line_path0 a b : line_path a b 0 = a.
Proof. by rewrite /line_path subr0 mul1r mul0r addr0. Qed.

Lemma line_path1 a b : line_path a b 1 = b.
Proof. by rewrite /line_path subrr mul0r add0r mul1r. Qed.

Lemma line_path_sym a b t : line_path a b t = line_path b a (1 - t).
Proof. by rewrite /line_path subKr addrC. Qed.

Lemma line_path_flat a : line_path a a = cst a.
Proof. by apply/funext => t; rewrite line_pathEl subrr mulr0 add0r. Qed.

Lemma leW_line_path a b : a <= b -> {homo line_path a b : x y / x <= y}.
Proof.
by move=> ? ? ? ?; rewrite !line_pathEl lerD ?ler_wpM2r// subr_ge0.
Qed.

Definition factor a b x := (x - a) / (b - a).

Lemma leW_factor a b : a <= b -> {homo factor a b : x y / x <= y}.
Proof.
by move=> ? ? ? ?; rewrite /factor ler_wpM2r ?lerD// invr_ge0 subr_ge0.
Qed.

Lemma factor_flat a : factor a a = cst 0.
Proof. by apply/funext => x; rewrite /factor subrr invr0 mulr0. Qed.

Lemma factorl a b : factor a b a = 0.
Proof. by rewrite /factor subrr mul0r. Qed.

Definition ndline_path a b of a < b := line_path a b.

Lemma ndline_pathE a b (ab : a < b) : ndline_path ab = line_path a b.
Proof. by []. Qed.

End line_path_factor_numDomainType.
#[deprecated(since="mathcomp-analysis 1.12.0", note="use `memB_itv0` instead")]
Notation mem_1B_itvcc := __deprepcated__mem_1B_itvcc (only parsing).

Section line_path_factor_numFieldType.
Variable R : numFieldType.
Implicit Types (a b t r : R) (A : set R).

Lemma factorr a b : a != b -> factor a b b = 1.
Proof. by move=> Nab; rewrite /factor divff// subr_eq0 eq_sym. Qed.

Lemma factorK a b : a != b -> cancel (factor a b) (line_path a b).
Proof. by move=> ? x; rewrite line_pathEl mulfVK ?addrNK// subr_eq0 eq_sym. Qed.

Lemma line_pathK a b : a != b -> cancel (line_path a b) (factor a b).
Proof.
by move=> ? x; rewrite /factor line_pathEl addrK mulfK// subr_eq0 eq_sym.
Qed.

Lemma line_path_inj a b : a != b -> injective (line_path a b).
Proof. by move/line_pathK/can_inj. Qed.

Lemma factor_inj a b : a != b -> injective (factor a b).
Proof. by move/factorK/can_inj. Qed.

Lemma line_path_bij a b : a != b -> bijective (line_path a b).
Proof. by move=> ab; apply: Bijective (line_pathK ab) (factorK ab). Qed.

Lemma factor_bij a b : a != b -> bijective (factor a b).
Proof. by move=> ab; apply: Bijective (factorK ab) (line_pathK ab). Qed.

Lemma le_line_path a b : a < b -> {mono line_path a b : x y / x <= y}.
Proof.
move=> ltab; have leab := ltW ltab.
apply: homo_mono (line_pathK _) (leW_factor _) (leW_line_path _) => //.
by rewrite lt_eqF.
Qed.

Lemma le_factor a b : a < b -> {mono factor a b : x y / x <= y}.
Proof.
move=> ltab; have leab := ltW ltab.
apply: homo_mono (factorK _) (leW_line_path _) (leW_factor _) => //.
by rewrite lt_eqF.
Qed.

Lemma lt_line_path a b : a < b -> {mono line_path a b : x y / x < y}.
Proof. by move/le_line_path/leW_mono. Qed.

Lemma lt_factor a b : a < b -> {mono factor a b : x y / x < y}.
Proof. by move/le_factor/leW_mono. Qed.

Let ltNeq a b : a < b -> a != b. Proof. by move=> /lt_eqF->. Qed.

HB.instance Definition _ a b (ab : a < b) :=
  @Can2.Build _ _ setT setT (ndline_path ab) (factor a b)
    (fun _ _ => I) (fun _ _ => I)
    (in1W (line_pathK (ltNeq ab))) (in1W (factorK (ltNeq ab))).

Lemma line_path_itv_bij ba bb a b : a < b ->
  set_bij [set` Interval (BSide ba 0) (BSide bb 1)]
          [set` Interval (BSide ba a) (BSide bb b)] (line_path a b).
Proof.
move=> ltab; rewrite -ndline_pathE.
apply: bij_subr => //=; rewrite setTI ?ndline_pathE.
apply/predeqP => t /=; rewrite !in_itv/= {1}line_pathEl line_pathEr.
rewrite -lteifBlDr subrr -lteif_pdivrMr ?subr_gt0// mul0r.
rewrite -lteifBrDr subrr -lteif_ndivrMr ?subr_lt0// mul0r.
by rewrite lteifBrDl addr0.
Qed.

Lemma factor_itv_bij ba bb a b : a < b ->
  set_bij [set` Interval (BSide ba a) (BSide bb b)]
          [set` Interval (BSide ba 0) (BSide bb 1)] (factor a b).
Proof.
move=> ltab; have -> : factor a b = (ndline_path ltab)^-1%FUN by [].
by apply/splitbij_sub_sym => //; apply: line_path_itv_bij.
Qed.

Lemma mem_line_path_itv ba bb a b : a < b ->
  set_fun [set` Interval (BSide ba 0) (BSide bb 1)]
          [set` Interval (BSide ba a) (BSide bb b)] (line_path a b).
Proof. by case/(line_path_itv_bij ba bb). Qed.

Lemma mem_line_path_itvcc a b : a <= b -> set_fun `[0, 1] `[a, b] (line_path a b).
Proof.
rewrite le_eqVlt => /predU1P[<-|]; first by rewrite set_itv1 line_path_flat.
by move=> lt_ab; case: (line_path_itv_bij true false lt_ab).
Qed.

Lemma range_line_path ba bb a b : a < b ->
   line_path a b @` [set` Interval (BSide ba 0) (BSide bb 1)] =
               [set` Interval (BSide ba a) (BSide bb b)].
Proof. by move=> /(line_path_itv_bij ba bb)/Pbij[f ->]; rewrite image_eq. Qed.

Lemma range_factor ba bb a b : a < b ->
   factor a b @` [set` Interval (BSide ba a) (BSide bb b)] =
                 [set` Interval (BSide ba 0) (BSide bb 1)].
Proof. by move=> /(factor_itv_bij ba bb)/Pbij[f ->]; rewrite image_eq. Qed.

Lemma onem_factor a b x : a != b -> `1-(factor a b x) = factor b a x.
Proof.
rewrite eq_sym -subr_eq0 => ab; rewrite /onem /factor -(divff ab) -mulrBl.
by rewrite opprB addrA subrK -mulrNN opprB -invrN opprB.
Qed.

End line_path_factor_numFieldType.

Lemma mem_factor_itv (R : realFieldType) ba bb (a b : R) :
  set_fun [set` Interval (BSide ba a) (BSide bb b)]
          [set` Interval (BSide ba 0) (BSide bb 1)] (factor a b).
Proof.
have [|leba] := ltP a b; first by case/(factor_itv_bij ba bb).
move=> x /=; have [|/itv_ge->//] := (boolP (BSide ba a < BSide bb b)%O).
rewrite lteBSide; case: ba bb => [] []//=; rewrite ?le_gtF//.
by case: ltgtP leba => // -> _ _ _; rewrite factor_flat in_itv/= lexx ler01.
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
Context {disp : Order.disp_t} {T : porderType disp}.

Definition disjoint_itv : rel (interval T) :=
  fun a b => [disjoint [set` a] & [set` b]].

Lemma disjoint_itvxx (i : interval T) : neitv i -> ~~ disjoint_itv i i.
Proof. by move=> i0; rewrite /disjoint_itv/= /disj_set /= setIid. Qed.

Lemma disjoint_rays b (x : T) :
  disjoint_itv (Interval -oo%O (BSide b x)) (Interval (BSide b x) +oo%O).
Proof. by rewrite eq_opE -(set_itvxx (BSide b x)) [RHS]set_itv_splitI setIC. Qed.

End disjoint_itv.

Section disjoint_itv_orderType.
Context {disp : Order.disp_t} {T : orderType disp}.

Lemma disjoint_neitv (i j : interval T) :
  disjoint_itv i j <-> ~~ neitv (itv_meet i j).
Proof.
case: i j => [a b] [c d]; rewrite /disjoint_itv/disj_set /= -set_itvI.
by split => [/negPn//|?]; apply/negPn.
Qed.

End disjoint_itv_orderType.

Section disjoint_itv_numDomain.

Context {R : numDomainType}.

Import Order.Theory.

Lemma lt_disjoint (i j : interval R) :
  (forall x y, x \in i -> y \in j -> x < y) -> disjoint_itv i j.
Proof.
move=> ij; apply/eqP; rewrite predeqE => x; split => // -[xi xj].
by have := ij _ _ xi xj; rewrite ltxx.
Qed.

End disjoint_itv_numDomain.

Section open_endpoints.
Context {d} {T : porderType d}.

Definition is_open_itv (A : set T) := exists ab, A = `]ab.1, ab.2[%classic.

Definition open_itv_cover (A : set T) := [set F : nat -> set T |
  (forall i, is_open_itv (F i)) /\ A `<=` \bigcup_k (F k)].

Definition itv_is_ray (i : interval T) : Prop :=
  match i with
  | Interval -oo%O (BLeft _) => True
  | Interval (BRight _) +oo%O => True
  | Interval -oo%O +oo%O => True
  | _ => False
  end.

Definition itv_is_bd_open (i : interval T) : Prop :=
  match i with
  | Interval (BRight _) (BLeft _) => True
  | _ => False
  end.

Definition itv_open_ends (i : interval T) : Prop :=
  itv_is_ray i \/ itv_is_bd_open i.

Lemma itv_open_ends_rside l b (t : T) :
  itv_open_ends (Interval l (BSide b t)) -> b = true.
Proof. by case: b; move: l => [[]?|[]] // [] //. Qed.

Lemma itv_open_ends_rinfty l b :
  itv_open_ends (Interval l (BInfty T b)) -> b = false.
Proof. by case: b => //; move: l => [[]?|[]] // []. Qed.

Lemma itv_open_ends_lside l b (t : T) :
  itv_open_ends (Interval (BSide b t) l) -> b = false.
Proof. by case: b; move: l => [[]?|[]] // []. Qed.

Lemma itv_open_ends_linfty l b :
  itv_open_ends (Interval (BInfty T b) l) -> b = true.
Proof. by case: b => //; move: l => [[]?|[]] // []. Qed.

Lemma is_open_itv_itv_is_bd_openP (i : interval T) :
  itv_is_bd_open i -> is_open_itv [set` i].
Proof.
by case: i=> [] [[]l|[]] // [[]r|[]] // ?; exists (l,r).
Qed.

End open_endpoints.

Lemma itv_open_endsI {d} {T : orderType d} (i j : interval T) :
  itv_open_ends i -> itv_open_ends j -> itv_open_ends (i `&` j)%O.
Proof.
move: i => [][[]a|[]] [[]b|[]] []//= _; move: j => [][[]x|[]] [[]y|[]] []//= _;
by rewrite /itv_open_ends/= ?orbF ?andbT -?negb_or ?le_total//=;
  try ((by left)||(by right)).
Qed.

Lemma itv_setU {d} {T : orderType d} (i j : interval T) :
  [set` i] `&` [set` j] !=set0 -> [set` (i `|` j)%O] = [set` i] `|` [set` j].
Proof.
case=> p [ip jp]; have pij : p \in (i `|` j)%O by exact/(le_trans ip)/leUl.
move: i j ip jp pij => [x y] [a b] /andP[xp py] /andP[ap pb] pab.
rewrite eqEsubset; split => /= r /=; first last.
  by move=> -[ra|rb]; [exact/(le_trans ra)/leUl|exact/(le_trans rb)/leUr].
rewrite (@itv_splitUeq _ T p (x `&` a)%O)// => /orP[].
- move=> /andP[xar rp]; have /orP[ax|xa] := le_total a x.
  + right; apply/andP; split; first by rewrite (le_trans _ xar)// leIidr.
    by rewrite (le_trans rp)// (le_trans _ pb)// bnd_simp.
  + left; apply/andP; split; first by rewrite (le_trans _ xar)// leIidl.
    by rewrite (le_trans rp)// (le_trans _ py)//= bnd_simp.
- move=> /predU1P[->|/andP[pr ryb]]; first by left; apply/andP.
  have /orP[bly|ylb] := le_total b y.
  + left; apply/andP; split; last by rewrite (le_trans ryb)// leUidr.
    by rewrite (le_trans _ pr)// (le_trans xp)//= bnd_simp.
  + right; apply/andP; split; last by rewrite (le_trans ryb)// leUidl.
    by rewrite (le_trans ap)// (le_trans _ pr)//= bnd_simp.
Qed.

Lemma itv_setI {d} {T : orderType d} (i j : interval T) :
  [set` (i `&` j)%O] = [set` i] `&` [set` j].
Proof.
by rewrite eqEsubset; split => z; rewrite /in_mem/= /pred_of_itv/= lexI=> /andP.
Qed.
