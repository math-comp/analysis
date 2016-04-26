(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From SsrReals Require Import finmap boolp reals discrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Notation "\- f" := (fun x => -(f x))
  (at level 20) : ring_scope.

Notation "f \* g" := (fun x => f x * g x)
  (at level 40, left associativity) : ring_scope.

(* -------------------------------------------------------------------- *)
Section Nbh.
Context {R : realType}.

Inductive nbh : {ereal R} -> predArgType :=
| NFin  (c e : R) of (0 < e) : nbh c%:E
| NPInf (M   : R) : nbh \+inf
| NNInf (M   : R) : nbh \-inf.

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
  (forall M, P _ (@NPInf R M)) -> forall (v : nbh \+inf), P _ v.
Proof.
move=> ih ; move: {-2}\+inf (erefl (@ERPInf R)).
by move=> e eE v; case: v eE => // c' e' h [->].
Qed.

Lemma nbh_ninfW (P : forall x, nbh x -> Prop) :
  (forall M, P _ (@NNInf R M)) -> forall (v : nbh \-inf), P _ v.
Proof.
move=> ih ; move: {-2}\-inf (erefl (@ERNInf R)).
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
Proof. by rewrite ltrNge /eclamp => /negbTE ->. Qed.

Definition B1 {R : realType} (x : R) :=
  @NFin R x 1 ltr01.

Definition B {R : realType} (x e : R) :=
  @NFin R x (eclamp e) (gt0_clamp e).

(* -------------------------------------------------------------------- *)
Lemma separable {R : realType} (l1 l2 : {ereal R}) :
  l1 != l2 -> exists (v1 : nbh l1) (v2 : nbh l2),
    forall x, x \notin [predI v1 & v2].
Proof.
wlog: l1 l2 / (l1 < l2)%E => [wlog ne_l12|le_l12 _].
  case/boolP: (l1 < l2)%E => [/wlog/(_ ne_l12)//|].
  rewrite -leeNgt lee_eqVlt eq_sym (negbTE ne_l12) /=.
  case/wlog=> [|x [y h]]; first by rewrite eq_sym.
  by exists y, x=> z; rewrite inE andbC /= (h z).
case: l1 l2 le_l12 => [l1||] [l2||] //= lt_l12; last first.
+ exists (NNInf 0), (NPInf 1) => x; rewrite !inE andbC.
  by apply/negP=> /andP[/ltr_trans h/h]; rewrite ltr10.
+ exists (NNInf (l2-1)), (B1 l2) => x; rewrite !inE.
  by rewrite ltr_norml [-1<_]ltr_subr_addl; case: (ltrgtP x).
+ exists (B1 l1), (NPInf (l1+1)) => x; rewrite !inE.
  rewrite ltr_norml ltr_subl_addr [1+_]addrC.
  by case: (ltrgtP x)=> //=; rewrite !andbF.
pose e := l2 - l1; exists (B l1 (e/2%:R)), (B l2 (e/2%:R)).
move=> x; rewrite !inE /= /eclamp lerNgt pmulr_rgt0 ?subr_gt0 //.
rewrite invr_gt0 ltr0n /=; apply/negP=> /andP[le1 le2].
have := ltr_add le1 le2; rewrite -mulrDl -mulr2n -mulr_natr.
rewrite mulfK ?pnatr_eq0 // distrC => /(ler_lt_trans (ler_norm_add _ _)).
rewrite [x-_]addrC addrACA addNr addr0 ltr0_norm.
  by rewrite subr_lt0. by rewrite opprB ltrr.
Qed.

(* -------------------------------------------------------------------- *)
Section SequenceLim.
Variable (R : realType).

Implicit Types (u v : nat -> R).

Definition ncvg u l :=
  forall v : nbh l, exists K, forall n, (K <= n)%N -> u n \in v.

Definition nbounded u :=
  exists v : nbh 0%:E, forall n, u n \in v.

Lemma nboundedP u :
  reflect (exists2 M, 0 < M & forall n, `|u n| < M) `[< nbounded u >].
Proof.
apply: (iffP idP) => [/asboolP[]|]; first elim/nbh_finW.
  move=> M /= gt0_M cv; exists M => [|n] //.
  by have := cv n; rewrite inE subr0.
case=> M _ cv; apply/asboolP; exists (B 0 M) => n; rewrite inE subr0.
by rewrite eclamp_id // (@ler_lt_trans _ `|u 0%N|).
Qed.
End SequenceLim.

(* -------------------------------------------------------------------- *)
Local Notation "c %:S" := (fun _ : nat => c) (at level 2, format "c %:S").

Section SeqLimTh.
Variable (R : realType).

Implicit Types (u v : nat -> R) (c : R) (l : {ereal R}).

Lemma ncvg_uniq u l1 l2 : ncvg u l1 -> ncvg u l2 -> l1 = l2.
Proof.
move=> cv1 cv2; apply/eqP; case: (l1 =P l2) => // /eqP.
case/separable=> [n1] [n2] h; move: (cv1 n1) (cv2 n2).
case=> [K1 c1] [K2 c2]; pose K := maxn K1 K2.
move/(_ (u K)): h; rewrite !inE /= !(c1, c2) //.
  by apply/leq_maxl. by apply/leq_maxr.
Qed.

Lemma ncvg_eq_from K v u l :
  (forall n, (K <= n)%N -> u n = v n) -> ncvg v l -> ncvg u l.
Proof.
move=> eq cu nb; case: (cu nb) => Ku {cu}cu; exists (maxn K Ku) => n.
by rewrite geq_max => /andP[leK leKu]; rewrite eq // cu.
Qed.

Lemma ncvg_eq v u l : u =1 v -> ncvg v l -> ncvg u l.
Proof. by move=> eq; apply: (@ncvg_eq_from 0). Qed.

Lemma ncvg_nbounded u x : ncvg u x%:E -> nbounded u.
Proof.                   (* FIXME: factor out `sup` of a finite set *)
case/(_ (B x 1)) => K cu; pose S := [seq `|u n| | n <- iota 0 K].
pose M : R := sup [pred x in S]; pose e := Num.max (`|x| + 1) (M + 1).
apply/asboolP/nboundedP; exists e => [|n]; first by rewrite ltr_maxr ltr_paddl.
case: (ltnP n K); last first.
  move/cu; rewrite inE eclamp_id ?ltr01 // => ltunBx1.
  rewrite ltr_maxr; apply/orP; left; rewrite -[u n](addrK x) addrAC.
  by apply/(ler_lt_trans (ler_norm_add _ _)); rewrite addrC ltr_add2l.
move=> lt_nK; have: `|u n| \in S; first by apply/map_f; rewrite mem_iota.
move=> un_S; rewrite ltr_maxr; apply/orP; right.
case E: {+}K lt_nK => [|k] // lt_nSk; apply/ltr_spaddr; first apply/ltr01.
apply/sup_upper_bound; last by apply/map_f; rewrite mem_iota E.
apply/has_supP; split; first by exists `|u 0%N|; rewrite /S E inE eqxx.
elim: {+}S => [|v s [ux /ubP hux]]; first by exists 0; apply/ubP.
exists (Num.max v ux); apply/ubP=> y; rewrite inE => /orP[/eqP->|].
  by rewrite ler_maxr lerr.
by move/hux=> le_yux; rewrite ler_maxr le_yux orbT.
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
case: (cu (B lu z)) (cv (B lv z)) => [ku {cu}cu] [kv {cv}cv].
exists (maxn ku kv) => n; rewrite geq_max => /andP[leu lev].
rewrite inE opprD addrACA (ler_lt_trans (ler_norm_add _ _)) //.
move: (cu _ leu) (cv _ lev); rewrite !inE eclamp_id.
  by rewrite mulr_gt0 // invr_gt0 ltr0Sn.
move=> cu' cv'; suff ->: e = z + z by rewrite ltr_add.
by rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0.
Qed.

Lemma ncvgN u lu : ncvg u lu -> ncvg (\- u) (- lu).
Proof.
case: lu => [lu||] cu /=; first last.
+ elim/nbh_pinfW=> M; case: (cu (NNInf (-M))) => K {cu}cu.
  by exists K => n /cu; rewrite !inE ltr_oppr.
+ elim/nbh_ninfW=> M; case: (cu (NPInf (-M))) => K {cu}cu.
  by exists K => n /cu; rewrite !inE ltr_oppl.
elim/nbh_finW => e /= gt0_e; case: (cu (B lu e)).
by move=> K {cu}cu; exists K=> n /cu; rewrite !inE -opprD normrN eclamp_id.
Qed.

Lemma ncvgN_fin u lu : ncvg u lu%:E -> ncvg (\- u) (- lu)%:E.
Proof. by apply/ncvgN. Qed.

Lemma ncvgB u v lu lv : ncvg u lu%:E -> ncvg v lv%:E ->
  ncvg (u \- v) (lu - lv)%:E.
Proof. by move=> cu cv; apply/ncvgD/ncvgN_fin. Qed.

Lemma ncvg_abs u lu : ncvg u lu%:E -> ncvg (fun n => `|u n|) `|lu|%:E.
Proof.
move=> cu; elim/nbh_finW => e /= gt0_e; case: (cu (B lu e)).
move=> K {cu}cu; exists K=> n /cu; rewrite !inE eclamp_id //.
by move/(ler_lt_trans (ler_dist_dist _ _)).
Qed.

Lemma ncvg_abs0 u : ncvg (fun n => `|u n|) 0%:E -> ncvg u 0%:E.
Proof.
move=> cu; elim/nbh_finW => e /= gt0_e; case: (cu (B 0 e)).
by move=> K {cu}cu; exists K=> n /cu; rewrite !inE !subr0 eclamp_id // normr_id.
Qed.

Lemma ncvgMl u v : ncvg u 0%:E -> nbounded v -> ncvg (u \* v) 0%:E.
move=> cu /asboolP/nboundedP [M gt0_M ltM]; elim/nbh_finW => e /= gt0_e.
case: (cu (B 0 (e / (M + 1)))) => K {cu}cu; exists K => n le_Kn.
rewrite inE subr0 normrM; apply/(@ltr_trans _ (e / (M + 1) * M)).
  apply/ltr_pmul => //; have /cu := le_Kn; rewrite inE subr0 eclamp_id //.
  by rewrite mulr_gt0 // invr_gt0 addr_gt0.
rewrite -mulrAC -mulrA gtr_pmulr // ltr_pdivr_mulr ?addr_gt0 //.
by rewrite mul1r ltr_addl.
Qed.

Lemma ncvgMr u v : ncvg v 0%:E -> nbounded u -> ncvg (u \* v) 0%:E.
Proof.
move=> cv bu; apply/(@ncvg_eq (v \* u)).
  by move=> x; rewrite mulrC. by apply/ncvgMl.
Qed.

Lemma ncvgM u v lu lv : ncvg u lu%:E -> ncvg v lv%:E ->
  ncvg (u \* v) (lu * lv)%:E.
Proof.
move=> cu cv; pose a := u \- lu%:S; pose b := v \- lv%:S.
have eq: (u \* v) =1 (lu * lv)%:S \+ ((lu%:S \* b) \+ (a \* v)).
  move=> n; rewrite {}/a {}/b /= [u n+_]addrC [(_+_)*(v n)]mulrDl.  
  rewrite !addrA -[LHS]add0r; congr (_ + _); rewrite mulrDr.
  by rewrite !(mulrN, mulNr) [X in X-_]addrCA subrr addr0 subrr.
apply/(ncvg_eq eq); rewrite -[X in X%:E]addr0; apply/ncvgD.
  by apply/ncvgC. rewrite -[X in X%:E]addr0; apply/ncvgD.
+ apply/ncvgMr; first rewrite -[X in X%:E](subrr lv).
    by apply/ncvgB/ncvgC. by apply/nboundedC.
+ apply/ncvgMl; first rewrite -[X in X%:E](subrr lu).
    by apply/ncvgB/ncvgC. by apply/(ncvg_nbounded cv).
Qed.

Lemma ncvgZ c u lu : ncvg u lu%:E -> ncvg (c \*o u) (c * lu)%:E.
Proof. by move=> cu; apply/ncvgM => //; apply/ncvgC. Qed.

Lemma ncvg_extract h u lu :
    {mono h : x y / (x < y)%N}
  -> ncvg u lu -> ncvg (fun n => u (h n)) lu.
Proof.
move=> mono_h cvu v; case: (cvu v)=> K {cvu}cvu; exists K.
move=> n le_Kn; apply/cvu; apply/(leq_trans le_Kn).
elim: {le_Kn} n => [|n ih] //; apply/(leq_ltn_trans ih).
by rewrite mono_h.
Qed.

Lemma ncvg_gt (u : nat -> R) (l1 l2 : {ereal R}) :
  (l1 < l2)%E -> ncvg u l2 ->
    exists K, forall n, (K <= n)%N -> (l1 < (u n)%:E)%E.
Proof.
case: l1 l2 => [l1||] [l2||] //=; first last.
+ by move=> _ _; exists 0%N. + by move=> _ _; exists 0%N.
+ by move=> _ /(_ (NPInf l1)) [K cv]; exists K => n /cv.
move=> lt_12; pose e := l2 - l1 => /(_ (B l2 e)).
case=> K cv; exists K => n /cv; rewrite !inE eclamp_id ?subr_gt0 //.
rewrite ltr_distl => /andP[] /(ler_lt_trans _) h _; apply: h.
by rewrite {cv}/e opprB addrCA subrr addr0.
Qed.

Lemma ncvg_lt (u : nat -> R) (l1 l2 : {ereal R}) :
  (l1 < l2)%E -> ncvg u l1 ->
    exists K, forall n, (K <= n)%N -> ((u n)%:E < l2)%E.
Proof.
move=> lt_12 cv_u_l1; case: (@ncvg_gt (\- u) (-l2) (-l1)).
  by rewrite lte_opp2. by apply/ncvgN.
by move=> K cv; exists K => n /cv; rewrite (@lte_opp2 _ _ (u n)%:E).
Qed.

Lemma ncvg_homo_lt (u : nat -> R) (l1 l2 : {ereal R}) :
    (forall m n, (m <= n)%N -> u m <= u n)
  -> (l1 < l2)%E -> ncvg u l1 -> forall n, ((u n)%:E < l2)%E.
Proof.
move=> homo_u lt_12 cvu n; have [K {cvu}cv] := ncvg_lt lt_12 cvu.
case: (leqP n K) => [/homo_u|/ltnW /cv //].
by move/lee_tofin/lee_lt_trans; apply; apply/cv.
Qed.

Lemma ncvg_homo_le (u : nat -> R) (l : {ereal R}) :
    (forall m n, (m <= n)%N -> u m <= u n)
  -> ncvg u l -> forall n, ((u n)%:E <= l)%E.
Proof.
move=> homo_u cvu n; case/boolP: (_ <= _)%E => //; rewrite -lteNgt.
by move/ncvg_homo_lt/(_ cvu) => -/(_ homo_u n); rewrite ltee.
Qed.
End SeqLimTh.

(* -------------------------------------------------------------------- *)
Section LimOp.
Context {R : realType}.

Implicit Types (u v : nat -> R).

Definition nlim u : {ereal R} :=
  if @idP `[exists l, `[< ncvg u l >]] is ReflectT Px then
    xchooseb Px else \-inf.

Lemma nlim_ncvg u : (exists l, ncvg u l) -> ncvg u (nlim u).
Proof.
case=> l cv_u_l; rewrite /nlim; case: {-}_ / idP; last first.
  by case; apply/existsbP; exists l; apply/asboolP.
move=> p; rewrite -[xchooseb _](ncvg_uniq cv_u_l) //.
by apply/asboolP/(xchoosebP p).
Qed.

Lemma nlim_out u : ~ (exists l, ncvg u l) -> nlim u = \-inf.
Proof.
move=> h; rewrite /nlim; case: {-}_ / idP => // p.
by case: h; case/existsbP: p => l /asboolP; exists l.
Qed.
End LimOp.

(* -------------------------------------------------------------------- *)
