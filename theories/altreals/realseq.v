(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import mathcomp.bigenough.bigenough.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import mathcomp_extra.
Require Import xfinmap ereal reals discrete topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.TTheory GRing.Theory Num.Theory BigEnough.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Notation "f '<=1' g" := (forall x, f x <= g x)
  (at level 70, no associativity).

Notation "f '<=2' g" := (forall x y, f x y <= g x y)
  (at level 70, no associativity).

(* -------------------------------------------------------------------- *)
Section FFTheory.
Context {R : realDomainType} (T : Type).

Implicit Types (f g h : T -> R).

Lemma leff f : f <=1 f.
Proof. by []. Qed.

Lemma lef_trans g f h : f <=1 g -> g <=1 h -> f <=1 h.
Proof. by move=> h1 h2 x; apply/(le_trans (h1 x)). Qed.
End FFTheory.

(* -------------------------------------------------------------------- *)
Section Nbh.
Context {R : realType}.

Inductive nbh : \bar R -> predArgType :=
| NFin  (c e : R) of (0 < e) : nbh c%:E
| NPInf (M   : R) : nbh +oo
| NNInf (M   : R) : nbh -oo.

Coercion pred_of_nbh l (v : nbh l) :=
  match v with
  | @NFin  l e _ => [pred x : R | `|x - l| < e]
  | @NPInf M     => [pred x : R | x > M]
  | @NNInf M     => [pred x : R | x < M]
  end.
End Nbh.

(* -------------------------------------------------------------------- *)
Section NbhElim.
Context {R : realType}.

Lemma nbh_finW c (P : forall x, nbh x -> Prop) :
    (forall e (h : 0 < e), P _ (@NFin R c e h))
  -> forall (v : nbh c%:E), P _ v.
Proof.
move=> ih; move: {-2}c%:E (erefl c%:E).
by move=> e eE v; case: v eE => // c' e' h [->].
Qed.

Lemma nbh_pinfW (P : forall x, nbh x -> Prop) :
  (forall M, P _ (@NPInf R M)) -> forall (v : nbh +oo), P _ v.
Proof.
move=> ih; move: {-2}+oo%E (erefl (@EPInf R)).
by move=> e eE v; case: v eE => // c' e' h [->].
Qed.

Lemma nbh_ninfW (P : forall x, nbh x -> Prop) :
  (forall M, P _ (@NNInf R M)) -> forall (v : nbh -oo), P _ v.
Proof.
move=> ih ; move: {-2}-oo%E (erefl (@ENInf R)).
by move=> e eE v; case: v eE => // c' e' h [->].
Qed.
End NbhElim.

Arguments nbh_finW  : clear implicits.
Arguments nbh_pinfW : clear implicits.
Arguments nbh_ninfW : clear implicits.

(* -------------------------------------------------------------------- *)
Definition eclamp {R : realType} (e : R) :=
  if e <= 0 then 1 else e.

Lemma gt0_clamp {R : realType} (e : R) : 0 < eclamp e.
Proof. by rewrite /eclamp; case: (lerP e 0) => h //; apply/ltr01. Qed.

Lemma eclamp_id {R : realType} (e : R) : 0 < e -> eclamp e = e.
Proof. by rewrite ltNge /eclamp => /negbTE ->. Qed.

Definition B1 {R : realType} (x : R) :=
  @NFin R x 1 ltr01.

Definition B {R : realType} (x e : R) :=
  @NFin R x (eclamp e) (gt0_clamp e).

(* -------------------------------------------------------------------- *)
Lemma separable_le {R : realType} (l1 l2 : \bar R) :
  (l1 < l2)%E -> exists (v1 : nbh l1) (v2 : nbh l2),
    forall x y, x \in v1 -> y \in v2 -> x < y.
Proof.
case: l1 l2 => [l1||] [l2||] //= lt_l12; last first.
+ exists (NNInf 0), (NPInf 1) => x y; rewrite !inE => lt1 lt2.
  by apply/(lt_trans lt1)/(lt_trans ltr01).
+ exists (NNInf (l2-1)), (B1 l2) => x y; rewrite !inE.
  rewrite ltr_norml [-1 < _]ltr_subr_addl.
  by move => lt1 /andP[lt2 _]; apply/(lt_trans lt1).
+ exists (B1 l1), (NPInf (l1+1)) => x y; rewrite !inE.
  rewrite ltr_norml ltr_subl_addr [1+_]addrC => /andP[_].
  by move=> lt1 lt2; apply/(lt_trans lt1).
pose e := l2 - l1; exists (B l1 (e/2%:R)), (B l2 (e/2%:R)).
have gt0_e: 0 < e by rewrite subr_gt0.
move=> x y; rewrite !inE/= /eclamp pmulr_rle0 // invr_le0.
rewrite lern0 /= !ltr_distl => /andP[_ lt1] /andP[lt2 _].
apply/(lt_trans lt1)/(le_lt_trans _ lt2).
rewrite ler_subr_addl addrCA -mulrDl -mulr2n -mulr_natr.
by rewrite mulfK ?pnatr_eq0 //= /e addrCA subrr addr0.
Qed.

Lemma separable {R : realType} (l1 l2 : \bar R) :
  l1 != l2 -> exists (v1 : nbh l1) (v2 : nbh l2),
    forall x, x \notin [predI v1 & v2].
Proof.
wlog: l1 l2 / (l1 < l2)%E => [wlog ne_l12|le_l12 _].
  case/boolP: (l1 < l2)%E => [/wlog/(_ ne_l12)//|].
  rewrite -leNgt le_eqVlt eq_sym (negbTE ne_l12) /=.
  case/wlog=> [|x [y h]]; first by rewrite eq_sym.
  by exists y, x=> z; rewrite inE andbC /= (h z).
case/separable_le: le_l12 => [v1] [v2] h; exists v1, v2.
move=> x; apply/negP; rewrite inE/= => /andP[] xv1 xv2.
by have := h _ _ xv1 xv2; rewrite ltxx.
Qed.

(* -------------------------------------------------------------------- *)
Section SequenceLim.
Variable (R : realType).

Implicit Types (u v : nat -> R).

Definition ncvg u l :=
  forall v : nbh l, exists K, forall n, (K <= n)%N -> u n \in v.

Definition iscvg (u : nat -> R) := exists l, ncvg u l%:E.

Definition nbounded u :=
  exists v : nbh 0%:E, forall n, u n \in v.

Lemma nboundedP u :
  reflect (exists2 M, 0 < M & forall n, `|u n| < M) `[< nbounded u >].
Proof.
apply: (iffP idP) => [/asboolP[]|]; first elim/nbh_finW.
  move=> M /= gt0_M cv; exists M => [|n] //.
  by have := cv n; rewrite inE subr0.
case=> M _ cv; apply/asboolP; exists (B 0 M) => n; rewrite inE subr0.
by rewrite eclamp_id // (@le_lt_trans _ _ `|u 0%N|).
Qed.
End SequenceLim.

(* -------------------------------------------------------------------- *)
Notation "c %:S" := (fun _ : nat => c) (at level 2, format "c %:S").

Section SeqLimTh.
Variable (R : realType).

Implicit Types (u v : nat -> R) (c : R) (l : \bar R).

Lemma ncvg_uniq u l1 l2 : ncvg u l1 -> ncvg u l2 -> l1 = l2.
Proof.
move=> cv1 cv2; apply/eqP; case: (l1 =P l2) => // /eqP.
case/separable=> [n1] [n2] h; move: (cv1 n1) (cv2 n2).
case=> [K1 c1] [K2 c2]; pose K := maxn K1 K2.
move/(_ (u K)): h; rewrite !inE/= !(c1, c2) //.
  by apply/leq_maxl. by apply/leq_maxr.
Qed.

Lemma ncvg_eq_from K v u l :
  (forall n, (K <= n)%N -> u n = v n) -> ncvg v l -> ncvg u l.
Proof.
move=> eq cu nb; case: (cu nb) => Ku {}cu; exists (maxn K Ku) => n.
by rewrite geq_max => /andP[leK leKu]; rewrite eq // cu.
Qed.

Lemma ncvg_eq v u l : u =1 v -> ncvg v l -> ncvg u l.
Proof. by move=> eq; apply: (@ncvg_eq_from 0). Qed.

Lemma ncvg_le_from K v u (lv lu : \bar R) :
  (forall n, (K <= n)%N -> u n <= v n) -> ncvg v lv -> ncvg u lu -> (lu <= lv)%E.
Proof.
move=> le_uv cv cu; rewrite leNgt; apply/negP=> /separable_le.
case=> [v1] [v2] h; have [] := (cv v1, cu v2).
case=> [K1 vv1] [K2 uv2]; pose_big_enough K'.
have []// := And3 (le_uv K' _) (vv1 K' _) (uv2 K' _). 2: by close.
by move=> le h1 h2; have := h _ _ h1 h2; rewrite ltNge le.
Qed.

Lemma ncvg_le v u (lv lu : \bar R) :
  u <=1 v -> ncvg v lv -> ncvg u lu -> (lu <= lv)%E.
Proof. by move=> le_uv; apply/(@ncvg_le_from 0). Qed.

Lemma ncvg_nbounded u x : ncvg u x%:E -> nbounded u.
Proof.                   (* FIXME: factor out `sup` of a finite set *)
case/(_ (B x 1)) => K cu; pose S := [seq `|u n| | n <- iota 0 K].
pose M : R := sup [set x : R | x \in S]; pose e := Num.max (`|x| + 1) (M + 1).
apply/asboolP/nboundedP; exists e => [|n]; first by rewrite lt_maxr ltr_paddl.
case: (ltnP n K); last first.
  move/cu; rewrite inE eclamp_id ?ltr01 // => ltunBx1.
  rewrite lt_maxr; apply/orP; left; rewrite -[u n](addrK x) addrAC.
  by apply/(le_lt_trans (ler_norm_add _ _)); rewrite addrC ltr_add2l.
move=> lt_nK; have: `|u n| \in S; first by apply/map_f; rewrite mem_iota.
move=> un_S; rewrite lt_maxr; apply/orP; right.
case E: {+}K lt_nK => [|k] // lt_nSk; apply/ltr_spaddr; first apply/ltr01.
suff : has_sup (fun x : R => x \in S) by move/sup_upper_bound/ubP => ->.
split; first by exists `|u 0%N|; rewrite /S E inE eqxx.
elim: {+}S => [|v s [ux /ubP hux]]; first by exists 0; apply/ubP.
exists (Num.max v ux); apply/ubP=> y; rewrite inE => /orP[/eqP->|].
  by rewrite le_maxr lexx.
by move/hux=> le_yux; rewrite le_maxr le_yux orbT.
Qed.

Lemma nboundedC c : nbounded c%:S.
Proof.
apply/asboolP/nboundedP; exists (`|c| + 1).
  by rewrite ltr_spaddr. by move=> _; rewrite ltr_addl.
Qed.

Lemma ncvgC c : ncvg c%:S c%:E.
Proof.
elim/nbh_finW => e /= gt0_e; exists 0%N => n _.
by rewrite inE subrr normr0.
Qed.

Lemma ncvgD u v lu lv : ncvg u lu%:E -> ncvg v lv%:E ->
  ncvg (u \+ v) (lu + lv)%:E.
Proof.
move=> cu cv; elim/nbh_finW => e /= gt0_e; pose z := e / 2%:R.
case: (cu (B lu z)) (cv (B lv z)) => [ku {}cu] [kv {}cv].
exists (maxn ku kv) => n; rewrite geq_max => /andP[leu lev].
rewrite inE opprD addrACA (le_lt_trans (ler_norm_add _ _)) //.
move: (cu _ leu) (cv _ lev); rewrite !inE eclamp_id.
  by rewrite mulr_gt0 // invr_gt0 ltr0Sn.
move=> cu' cv'; suff ->: e = z + z by rewrite ltr_add.
by rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0.
Qed.

Lemma ncvgN u lu : ncvg u lu -> ncvg (- u) (- lu).
Proof.
case: lu => [lu||] cu /=; first last.
+ elim/nbh_pinfW=> M; case: (cu (NNInf (-M))) => K {}cu.
  by exists K => n /cu; rewrite !inE ltr_oppr.
+ elim/nbh_ninfW=> M; case: (cu (NPInf (-M))) => K {}cu.
  by exists K => n /cu; rewrite !inE ltr_oppl.
elim/nbh_finW => e /= gt0_e; case: (cu (B lu e)).
by move=> K {}cu; exists K=> n /cu; rewrite !inE -opprD normrN eclamp_id.
Qed.

Lemma ncvgN_fin u lu : ncvg u lu%:E -> ncvg (- u) (- lu)%:E.
Proof. by apply/ncvgN. Qed.

Lemma ncvgB u v lu lv : ncvg u lu%:E -> ncvg v lv%:E ->
  ncvg (u \- v) (lu - lv)%:E.
Proof. by move=> cu cv; apply/ncvgD/ncvgN_fin. Qed.

Lemma ncvg_abs u lu : ncvg u lu%:E -> ncvg (fun n => `|u n|) `|lu|%:E.
Proof.
move=> cu; elim/nbh_finW => e /= gt0_e; case: (cu (B lu e)).
move=> K {}cu; exists K=> n /cu; rewrite !inE eclamp_id //.
by move/(le_lt_trans (ler_dist_dist _ _)).
Qed.

Lemma ncvg_abs0 u : ncvg (fun n => `|u n|) 0%:E -> ncvg u 0%:E.
Proof.
move=> cu; elim/nbh_finW => e /= gt0_e; case: (cu (B 0 e)).
by move=> K {}cu; exists K=> n /cu; rewrite !inE !subr0 eclamp_id // normr_id.
Qed.

Lemma ncvgMl u v : ncvg u 0%:E -> nbounded v -> ncvg (u \* v) 0%:E.
move=> cu /asboolP/nboundedP [M gt0_M ltM]; elim/nbh_finW => e /= gt0_e.
case: (cu (B 0 (e / (M + 1)))) => K {}cu; exists K => n le_Kn.
rewrite inE subr0 normrM; apply/(@lt_trans _ _ (e / (M + 1) * M)).
  apply/ltr_pmul => //; have /cu := le_Kn; rewrite inE subr0 eclamp_id //.
  by rewrite mulr_gt0 // invr_gt0 addr_gt0.
rewrite -mulrAC -mulrA gtr_pmulr // ltr_pdivr_mulr ?addr_gt0 //.
by rewrite mul1r ltr_addl.
Qed.

Lemma ncvgMr u v : ncvg v 0%:E -> nbounded u -> ncvg (u \* v) 0%:E.
Proof.
move=> cv bu; apply/(@ncvg_eq (v \* u)).
  by move=> x; rewrite /= mulrC.
by apply/ncvgMl.
Qed.

Lemma ncvgM u v lu lv : ncvg u lu%:E -> ncvg v lv%:E ->
  ncvg (u \* v) (lu * lv)%:E.
Proof.
move=> cu cv; pose a := u \- lu%:S; pose b := v \- lv%:S.
have eq: (u \* v) =1 (lu * lv)%:S \+ ((lu%:S \* b) \+ (a \* v)).
  move=> n; rewrite {}/a {}/b /= [u n+_]addrC [(_+_)*(v n)]mulrDl.
  rewrite !addrA -[LHS]add0r; congr (_ + _); rewrite mulrDr.
  by rewrite !(mulrN, mulNr) (addrCA (lu * lv)) subrr addr0 subrr.
apply/(ncvg_eq eq); rewrite -[X in X%:E]addr0; apply/ncvgD.
  by apply/ncvgC. rewrite -[X in X%:E]addr0; apply/ncvgD.
+ apply/ncvgMr; first rewrite -[X in X%:E](subrr lv).
    by apply/ncvgB/ncvgC. by apply/nboundedC.
+ apply/ncvgMl; first rewrite -[X in X%:E](subrr lu).
    by apply/ncvgB/ncvgC. by apply/(ncvg_nbounded cv).
Qed.

Lemma ncvgZ c u lu : ncvg u lu%:E -> ncvg (c \*o u) (c * lu)%:E.
Proof. by move=> cu; apply/ncvgM => //; apply/ncvgC. Qed.

Lemma ncvg_leC c u (lu : \bar R) :
  (forall n, u n <= c) -> ncvg u lu -> (lu <= c%:E)%E.
Proof. by move=> le cu; apply/(@ncvg_le c%:S u)=> //; apply/ncvgC. Qed.

Lemma ncvg_geC c u (lu : \bar R) :
  (forall n, c <= u n) -> ncvg u lu -> (c%:E <= lu)%E.
Proof. by move=> le cu; apply/(@ncvg_le u c%:S)=> //; apply/ncvgC. Qed.

Lemma iscvgC c : iscvg c%:S.
Proof. by exists c; apply/ncvgC. Qed.

Hint Resolve iscvgC : core.

Lemma iscvgD (u v : nat -> R) : iscvg u -> iscvg v -> iscvg (u \+ v).
Proof. by case=> [lu cu] [lv cv]; exists (lu + lv); apply/ncvgD. Qed.

Lemma iscvg_sum {I : eqType} (u : I -> nat -> R) r :
  (forall i, i \in r -> iscvg (u i)) ->
    iscvg (fun n => \sum_(i <- r) u i n).
Proof.
elim: r => [|i r ih] h.
  by exists 0; apply/(@ncvg_eq 0%:S)/ncvgC => n; rewrite big_nil.
case: ih => [j jr|c cv]; first by apply/h; rewrite inE jr orbT.
have [l cl]: iscvg (u i) by apply/h; rewrite inE eqxx.
exists (c + l); have := ncvgD cv cl; apply/ncvg_eq.
by move=> n; rewrite big_cons addrC.
Qed.

Lemma iscvg_eq (u v : nat -> R) :
  u =1 v -> iscvg v -> iscvg u.
Proof. by move=> equv [l h]; exists l; apply/(ncvg_eq equv). Qed.

Lemma ncvg_sub h u lu :
     {homo h : x y / (x < y)%N}
  -> ncvg u lu -> ncvg (fun n => u (h n)) lu.
Proof.
move=> mono_h cvu v; case: (cvu v)=> K {}cvu; exists K.
move=> n le_Kn; apply/cvu; apply/(leq_trans le_Kn).
elim: {le_Kn} n => [|n ih] //; apply/(leq_ltn_trans ih).
by rewrite mono_h.
Qed.

Lemma iscvg_sub σ u :
  {homo σ : x y / (x < y)%N} -> iscvg u -> iscvg (u \o σ).
Proof. by move=> homoσ [l h]; exists l; apply/ncvg_sub. Qed.

Lemma ncvg_shift k (u : nat -> R) l :
  ncvg u l <-> ncvg (fun n => u (n + k)%N) l.
Proof. split => h v; move/(_ v): h => [K h].
+ by exists K => n leKn; apply/h/(leq_trans leKn)/leq_addr.
+ exists (K + k)%N => n leKkn; rewrite -[n](@subnK k).
  * by apply/(leq_trans _ leKkn)/leq_addl.
  apply/h/(@leq_trans ((K+k) - k))/leq_sub2r => //.
  by rewrite addnK.
Qed.

Lemma iscvg_shift k (u : nat -> R) :
  iscvg u <-> iscvg (fun n => u (n + k)%N).
Proof. by split=> -[l h]; exists l; apply/(ncvg_shift _ u). Qed.

Lemma ncvg_gt (u : nat -> R) (l1 l2 : \bar R) :
  (l1 < l2)%E -> ncvg u l2 ->
    exists K, forall n, (K <= n)%N -> (l1 < (u n)%:E)%E.
Proof.
case: l1 l2 => [l1||] [l2||] //=; first last.
+ by move=> _ _; exists 0%N => ? ?; exact: ltNyr.
+ by move=> _ _; exists 0%N => ? ?; exact: ltNyr.
+ by move=> _ /(_ (NPInf l1)) [K cv]; exists K => n /cv.
move=> lt_12; pose e := l2 - l1 => /(_ (B l2 e)).
case=> K cv; exists K => n /cv; rewrite !inE eclamp_id ?subr_gt0 //.
rewrite ltr_distl => /andP[] /(le_lt_trans _) h _; apply: h.
by rewrite {cv}/e opprB addrCA subrr addr0.
Qed.

Lemma ncvg_lt (u : nat -> R) (l1 l2 : \bar R) :
  (l1 < l2)%E -> ncvg u l1 ->
    exists K, forall n, (K <= n)%N -> ((u n)%:E < l2)%E.
Proof.
move=> lt_12 cv_u_l1; case: (@ncvg_gt (- u) (-l2) (-l1)).
  by rewrite lte_opp2. by apply/ncvgN.
by move=> K cv; exists K => n /cv; rewrite (@lte_opp2 _ _ (u n)%:E).
Qed.

Lemma ncvg_homo_lt (u : nat -> R) (l1 l2 : \bar R) :
    (forall m n, (m <= n)%N -> u m <= u n)
  -> (l1 < l2)%E -> ncvg u l1 -> forall n, ((u n)%:E < l2)%E.
Proof.
move=> homo_u lt_12 cvu n; have [K {cvu}cv] := ncvg_lt lt_12 cvu.
case: (leqP n K) => [/homo_u|/ltnW /cv //].
by move/lee_tofin/le_lt_trans; apply; apply/cv.
Qed.

Lemma ncvg_homo_le (u : nat -> R) (l : \bar R) :
    (forall m n, (m <= n)%N -> u m <= u n)
  -> ncvg u l -> forall n, ((u n)%:E <= l)%E.
Proof.
move=> homo_u cvu n; rewrite leNgt.
by apply/negP => /ncvg_homo_lt /(_ cvu) -/(_ homo_u n); rewrite ltxx.
Qed.
End SeqLimTh.

(* -------------------------------------------------------------------- *)
Section LimOp.
Context {R : realType}.

Implicit Types (u v : nat -> R).

Definition nlim u : \bar R :=
  if @idP `[< exists l, `[< ncvg u l >] >] is ReflectT Px then
    xchoose (asboolP _ Px) else -oo.

Lemma nlim_ncvg u : (exists l, ncvg u l) -> ncvg u (nlim u).
Proof.
case=> l cv_u_l; rewrite /nlim; case: {-}_ / idP; last first.
  by case; apply/asboolP; exists l; apply/asboolP.
by move=> p; apply/asboolP/(xchooseP (asboolP _ p)).
Qed.

Lemma nlim_out u : ~ (exists l, ncvg u l) -> nlim u = -oo%E.
Proof.
move=> h; rewrite /nlim; case: {-}_ / idP => // p.
by case: h; case/asboolP: p => l /asboolP; exists l.
Qed.

CoInductive nlim_spec (u : nat -> R) : \bar R -> Type :=
| NLimCvg l : ncvg u l -> nlim_spec u l
| NLimOut   : ~ (exists l, ncvg u l) -> nlim_spec u -oo.

Lemma nlimP u : nlim_spec u (nlim u).
Proof.
case/boolP: `[< exists l, `[< ncvg u l >] >] => /asboolP/exists_asboolP/asboolP.
  by move/nlim_ncvg=> h; apply/NLimCvg.
by move=> h; rewrite nlim_out //; apply/NLimOut.
Qed.

Lemma nlimE (u : nat -> R) (l : \bar R) : ncvg u l -> nlim u = l.
Proof.
move=> cu; have: (ncvg u (nlim u)).
  by apply/nlim_ncvg; exists l. by move/(ncvg_uniq cu) => ->.
Qed.

Lemma nlimC c : nlim c%:S = c%:E :> \bar R.
Proof. by move/nlimE: (@ncvgC R c). Qed.

Lemma nlimD (u v : nat -> R) : iscvg u -> iscvg v ->
  nlim (u \+ v) = (nlim u + nlim v)%E.
Proof.
case=> [lu cu] [lv cv]; rewrite (nlimE cu) (nlimE cv) /=.
by rewrite (nlimE (ncvgD cu cv)).
Qed.

Lemma eq_from_nlim K (v u : nat -> R) :
  (forall n, (K <= n)%N -> u n = v n) -> nlim u = nlim v.
Proof.
move=> eq; have h := ncvg_eq_from eq; case: (nlimP v).
  by move=> l cv; have cu := h _ cv; rewrite (nlimE cu).
move=> Ncv; rewrite nlim_out //; case=> l cu.
apply: Ncv; exists l; apply/(@ncvg_eq_from _ K u) => //.
by move=> n /eq /esym.
Qed.

Lemma eq_nlim (v u : nat -> R) : u =1 v -> nlim u = nlim v.
Proof. by move=> eq; apply/(@eq_from_nlim 0) => n _; apply/eq. Qed.

Lemma nlim_bump (u : nat -> R) : nlim (fun n => u n.+1) = nlim u.
Proof.
case: (nlimP u) => [l cu|Ncu].
  suff: ncvg (fun n => u n.+1) l by move/nlimE.
  move=> v; case/(_ v): cu => K cu; exists K => n le_Kn.
  by apply/cu; apply/(leq_trans le_Kn).
rewrite nlim_out //; case=> l cu; apply/Ncu; exists l.
move=> v; case/(_ v): cu => K cu; exists K.+1 => n le_Kn.
rewrite -[n]prednK; first by apply/(leq_trans _ le_Kn).
by apply/cu; rewrite -ltnS prednK ?(leq_trans _ le_Kn).
Qed.

Lemma nlim_lift (u : nat -> R) p : nlim (fun n => u (n + p)%N) = nlim u.
Proof.
elim: p => [|p ih]; first by apply/eq_nlim=> k; rewrite addn0.
rewrite -ih -[in RHS]nlim_bump; apply/eq_nlim=> k /=.
by rewrite addSnnS.
Qed.

Lemma nlim_sum {I : eqType} (u : I -> nat -> R) (r : seq I) :
  (forall i, i \in r -> iscvg (u i)) ->
      nlim (fun n => \sum_(i <- r) (u i) n)
    = (\sum_(i <- r) nlim (u i))%E.
Proof.
elim: r => /= [|i r ih] h; first rewrite big_nil.
  by rewrite (@eq_nlim 0%:S) ?nlimC //= => n; rewrite big_nil.
rewrite big_cons -ih -?nlimD.
  by move=> j jr; apply/h; rewrite inE jr orbT.
  by apply/h; rewrite inE eqxx.
  by apply/iscvg_sum=> j jr; apply/h; rewrite inE jr orbT.
by apply/eq_nlim=> n /=; rewrite big_cons.
Qed.

Lemma nlim_sumR {I : eqType} (u : I -> nat -> R) (r : seq I) :
    (forall i, i \in r -> iscvg (u i)) ->
  nlim (fun n => \sum_(i <- r) (u i) n) = (\sum_(i <- r)
    (fine (nlim (u i)) : R))%:E.
Proof.
move=> h; rewrite nlim_sum //; elim: r h => [|i r ih] h.
  by rewrite !big_nil.
rewrite !big_cons; case: (h i); first by rewrite inE eqxx.
move=> c /nlimE ->; rewrite ih // => j jr.
by apply/h; rewrite inE jr orbT.
Qed.

Lemma nlim_sup (u : nat -> R) l :
    (forall n m, (n <= m)%N -> u n <= u m)
  -> ncvg u l%:E
  -> sup [set r | exists n, r = u n] = l.
Proof.
move=> mn_u cv_ul; set S := (X in sup X); suff: ncvg u (sup S)%:E.
  by move/nlimE; move/nlimE: cv_ul => -> [->].
elim/nbh_finW=> /= e gt0_e; have sS: has_sup S.
  split; first exists (u 0%N).
    by exists 0%N.
  exists l; apply/ubP => _ [n ->].
  by rewrite -lee_fin; apply/ncvg_homo_le.
have /sup_adherent := sS => /(_ _ gt0_e) [r] [N ->] lt_uN.
exists N => n le_Nn; rewrite !inE distrC ger0_norm ?subr_ge0.
  by move/ubP : (sup_upper_bound sS) => -> //; exists n.
by rewrite ltr_subl_addr -ltr_subl_addl (lt_le_trans lt_uN) ?mn_u.
Qed.

End LimOp.

(* -------------------------------------------------------------------- *)
