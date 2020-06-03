(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import xfinmap boolp classical_sets ereal reals discrete.
Require Import realseq realsum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation simpm := Monoid.simpm.

(* -------------------------------------------------------------------- *)
Reserved Notation "\dlet_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dlet_ ( i  <-  d ) '/  '  E ']'").

Reserved Notation "\dlim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \dlim_ ( n ) '/  '  E ']'").

Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E?_[ mu ] f" (at level 2, format "\E?_[ mu ]  f").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").

Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

(* -------------------------------------------------------------------- *)
Section Distribution.
Variables (R : realType) (T : choiceType).

Structure distr := Distr {
  mu :> T -> R;
  _  :  forall x, 0 <= mu x;
  _  :  summable mu;
  _  :  psum mu <= 1
}.

Definition distr_of of phant R & phant T := distr.
End Distribution.

Notation "{ 'distr' T / R }" := (distr_of (Phant R) (Phant T))
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.

(* -------------------------------------------------------------------- *)
Section DistrCoreTh.
Context {R : realType} (T : choiceType) (mu : {distr T / R}).

Lemma ge0_mu : forall x, 0 <= mu x.
Proof. by case: mu. Qed.

Lemma le1_mu : psum mu <= 1.
Proof. by case: mu. Qed.

Lemma summable_mu : summable mu.
Proof. by case: mu. Qed.
End DistrCoreTh.

Hint Resolve ge0_mu le1_mu summable_mu : core.

(* -------------------------------------------------------------------- *)
Section Clamp.
Context {R : realType}.

Definition clamp (x : R) :=
  Num.max (Num.min x 1) 0.

Lemma ge0_clamp x : 0 <= clamp x.
Proof. by rewrite lexU lexx orbT. Qed.

Lemma le1_clamp x : clamp x <= 1.
Proof. by rewrite leUx leIx lexx ler01 orbT. Qed.

Definition cp01_clamp := (ge0_clamp, le1_clamp).

Lemma clamp_in01 x : 0 <= x <= 1 -> clamp x = x.
Proof.
case/andP=> ge0_x le1_x; rewrite /clamp (elimT join_idPr).
  by rewrite lexI ge0_x ler01. by rewrite (elimT meet_idPl).
Qed.

Lemma clamp_id x : clamp (clamp x) = clamp x.
Proof. by rewrite clamp_in01 // !cp01_clamp. Qed.

Lemma clamp0 : clamp 0 = 0.
Proof. by rewrite clamp_in01 // lexx ler01. Qed.

Lemma clamp1 : clamp 1 = 1.
Proof. by rewrite clamp_in01 // lexx ler01. Qed.
End Clamp.

(* -------------------------------------------------------------------- *)
Section StdDefs.
Context {R : realType} (T : choiceType).

Implicit Types (mu : {distr T / R}) (A B E : pred T) (f : T -> R).

Definition dinsupp mu := fun x => mu x != 0 :> R.

Lemma in_dinsupp x (mu : {distr T / R}) :
  (x \in dinsupp mu) = (mu x != 0).
Proof. by []. Qed.

Lemma dinsuppP mu x : reflect (mu x <> 0) (x \in dinsupp mu).
Proof. by apply: (iffP idP) => /eqP. Qed.

Lemma dinsuppPn mu x : reflect (mu x = 0) (x \notin dinsupp mu).
Proof. by rewrite -topredE /dinsupp /= negbK; apply/eqP. Qed.

Definition pr   mu E   := psum (fun x => (E x)%:R * mu x).
Definition prc  mu E A := pr mu [predI E & A] / pr mu A.
Definition esp  mu f   := sum (fun x => f x * mu x).
Definition espc mu f A := sum (fun x => f x * prc mu (pred1 x) A).

Definition has_esp mu f := summable (fun x => f x * mu x).
End StdDefs.

Notation "\P_[ mu ] E"     := (pr mu E).
Notation "\P_[ mu , A ] E" := (prc mu E A).
Notation "\E_[ mu ] f"     := (esp mu f).
Notation "\E_[ mu , A ] f" := (espc mu f A).
Notation "\E?_[ mu ] f"    := (has_esp mu f).
Notation dweight mu        := (\P_[mu] predT).

(* -------------------------------------------------------------------- *)
Section DistrTheory.
Context {R : realType} {T : choiceType} (mu : T -> R).

Definition isdistr :=
  (forall x, 0 <= mu x) /\ (forall J, uniq J -> \sum_(j <- J) mu j <= 1).

Hypothesis isd : isdistr.

Local Lemma isd1 : forall x, 0 <= mu x.
Proof. by case: isd. Qed.

Local Lemma isd2 : summable mu.
Proof.
case: isd=> _ h; apply/summable_seqP; exists 1=> //.
move=> s /h /(le_trans _); apply; rewrite le_eqVlt; apply/orP.
by left; apply/eqP/eq_bigr=> i _; rewrite ger0_norm ?isd1.
Qed.

Local Lemma isd3 : psum mu <= 1.
Proof.
rewrite psumE; [apply/isd1 | apply/isd2 | apply/sup_le_ub].
  by exists 0, fset0; rewrite big_fset0.
apply/ubP=> y [x ->]; rewrite big_fset_seq /=.
by case: isd => _; apply; case: x => x /= /canonical_uniq.
Qed.

Definition mkdistr := @Distr R T mu isd1 isd2 isd3.

Lemma mkdistrE : mkdistr =1 mu.
Proof. by []. Qed.

Definition ispredistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x & summable mu].
End DistrTheory.

Lemma isdistr_finP {R : realType} {I : finType} (mu : I -> R) :
  (isdistr mu) <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof. split=> -[ ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(le_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= ler_addl sumr_ge0.
Qed.

Lemma le1_mu1
  {R : realType} {T : choiceType} (mu : {distr T / R}) x : mu x <= 1.
Proof.
apply/(@le_trans _ _ (psum mu)) => //; rewrite -[mu x]ger0_norm //.
by apply/ger1_psum.
Qed.

(* -------------------------------------------------------------------- *)
Section DistrD.
Context {R : realType} {T : choiceType} (mu : T -> R).

Definition mnull := fun x : T => (0 : R).

Lemma isd_mnull : isdistr mnull.
Proof. by split=> // J _; rewrite big1 ?ler01. Qed.

Definition dnull := locked (mkdistr isd_mnull).

Lemma dnullE x : dnull x = 0.
Proof. by unlock dnull. Qed.

Definition mkdistrd : {distr T / R} :=
  if @idP `[< isdistr mu >] is ReflectT Px then
    mkdistr (asboolW Px)
  else dnull.
End DistrD.

(* -------------------------------------------------------------------- *)
Lemma lef_dnull {R : realType} {T : choiceType} (mu : {distr T / R}) :
  dnull <=1 mu.
Proof. by move=> x; rewrite dnullE ge0_mu. Qed.

(* -------------------------------------------------------------------- *)
Section Restr.
Context {R : realType} {T : choiceType} (p : pred T).

Definition mrestr (mu : {distr T / R}) :=
  fun x => if p x then mu x else 0.

Lemma isd_mrestr (mu : {distr T / R}) : isdistr (mrestr mu).
Proof.
split=> [x|J]; first by rewrite /mrestr; case: ifP.
move=> eqJ; apply/(@le_trans _ _ (\sum_(j <- J) `|mu j|)).
+ apply/ler_sum=> i _; rewrite /mrestr; case: ifPn=> _.
  by apply/ler_norm. by apply/normr_ge0.
+ by apply/(le_trans _ (le1_mu mu))/gerfinseq_psum.
Qed.

Definition drestr (mu : {distr T / R}) := locked (mkdistr (isd_mrestr mu)).

Lemma drestrE (mu : {distr T / R}) x :
  drestr mu x = if p x then mu x else 0.
Proof. by unlock drestr. Qed.
End Restr.

(* -------------------------------------------------------------------- *)
Section RestrTheory.
Context {R : realType} {T : choiceType}.

Lemma drestrD (mu : {distr T / R}) (p : pred T) x :
  mu x = drestr p mu x + drestr (predC p) mu x.
Proof. by rewrite !drestrE !inE; case: ifPn; rewrite /= (addr0, add0r). Qed.

Lemma dinsupp_restr (mu : {distr T / R}) (p : pred T) x :
  (x \in dinsupp (drestr p mu)) = (x \in dinsupp mu) && p x.
Proof.
apply/dinsuppP/idP.
- by rewrite drestrE; case: ifP=> // _ /dinsuppP ->.
- by case/andP; rewrite drestrE => /dinsuppP ? ->.
Qed.
End RestrTheory.

(* -------------------------------------------------------------------- *)
Section DRat.
Context {R : realType} (T : choiceType).

Local Notation distr := {distr T / R}.

Implicit Types (s : seq T).

Definition mrat (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma ge0_mrat s : forall x, 0 <= mrat s x.
Proof. by move=> x; rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Local Lemma has_sup_mrat s J : uniq J -> \sum_(i <- J) mrat s i <= 1.
Proof.
move=> uqJ; rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivr_mulr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
have ->: (size s = \sum_(i <- undup s) count_mem i s)%N.
  rewrite -sum1_size -big_undup_iterop_count; apply: eq_bigr => i _.
  by rewrite Monoid.iteropE iter_addn addn0 mul1n.
rewrite [X in (_<=X)%N](bigID (mem J)) /= -ltnS -addSn.
rewrite ltn_addr //= ltnS -big_filter -[X in (_<=X)%N]big_filter.
rewrite leq_eqVlt; apply/orP; left; apply/eqP/perm_big.
apply/uniq_perm_eq; rewrite ?filter_uniq ?undup_uniq //.
by move=> x; rewrite !mem_filter mem_undup andbC.
Qed.

Local Lemma mrat_sup s : (0 < size s)%N ->
  \sum_(i <- undup s) mrat s i = 1.
Proof.
move=> gt0_s; rewrite -mulr_suml -natr_sum.
apply/(mulIf (x := (size s)%:R)); first by rewrite pnatr_eq0 -lt0n.
rewrite mul1r -mulrA mulVf ?mulr1 ?pnatr_eq0 -?lt0n //; congr (_%:R).
rewrite -sum1_size -[in RHS]big_undup_iterop_count/=; apply: eq_bigr => i _.
by rewrite Monoid.iteropE iter_addn addn0 mul1n.
Qed.

Local Lemma summable_mrat s: summable (mrat s).
Proof.
apply/summable_seqP; exists 1=> // J uqJ; rewrite (eq_bigr (mrat s)).
  by move=> j _; rewrite ger0_norm ?ge0_mrat.
by apply/has_sup_mrat.
Qed.

Lemma isd_mrat s : isdistr (mrat s).
Proof. by split; [apply/ge0_mrat | apply/has_sup_mrat]. Qed.

Definition drat s := locked (mkdistr (isd_mrat s)).

Lemma drat1E s x :
  drat s x = (count_mem x s)%:R / (size s)%:R.
Proof. by unlock drat; rewrite mkdistrE. Qed.

Definition dunit x := locked (drat [:: x]).
Definition duni  s := locked (drat (undup s)).

Lemma dunit1E x y : (dunit x) y = (x == y)%:R.
Proof. by unlock dunit; rewrite drat1E /= !(simpm, invr1). Qed.

Lemma duni1E s x : (duni s) x = (x \in s)%:R / (size (undup s))%:R.
Proof.
by unlock duni; rewrite drat1E count_uniq_mem ?(mem_undup, undup_uniq).
Qed.

Lemma in_dunit t t' :
  t' \in dinsupp (dunit t) -> t' = t :> T.
Proof.
by rewrite in_dinsupp dunit1E pnatr_eq0 eqb0 negbK => /eqP.
Qed.
End DRat.

(* -------------------------------------------------------------------- *)
Section Flip.
Context {R : realType}.

Definition mflip (xt : R) :=
  fun b => if b then clamp xt else 1 - clamp xt.

Lemma isd_mflip xt : isdistr (mflip xt).
Proof. apply/isdistr_finP; split=> [b|].
+ by case: b; rewrite ?subr_ge0 cp01_clamp.
+ by rewrite /index_enum !unlock /= addr0 addrCA subrr addr0.
Qed.

Definition dflip (xt : R) := locked (mkdistr (isd_mflip xt)).

Lemma dflip1E xt : dflip xt =1 mflip xt.
Proof. by unlock dflip; apply/mkdistrE. Qed.
End Flip.

(* -------------------------------------------------------------------- *)
Section Std.
Context {R : realType}.

Local Notation distr T := {distr T / R}.

Implicit Types (T U : choiceType).

(* -------------------------------------------------------------------- *)
Section Bind.
Context {T U : choiceType} (f : T -> distr U) (mu : distr T).

Definition mlet := fun y : U => psum (fun x => mu x * f x y).

Lemma isd_mlet : isdistr mlet.
Proof.
split=> [x|J uqJ]; first by apply/ge0_psum.
rewrite /mlet psum_bigop; first by move=> y x; rewrite mulr_ge0.
  move=> u; apply/(le_summable (F2 := mu)) => //.
  by move=> x; rewrite mulr_ge0 //= ler_pimulr ?le1_mu1.
apply/(le_trans _ (le1_mu mu))/le_psum => //.
move=> x; rewrite sumr_ge0 /= => [y _|]; first by rewrite mulr_ge0.
rewrite -mulr_sumr ler_pimulr //; apply/(le_trans _ (le1_mu (f x))).
have := summable_mu (f x) => /gerfinseq_psum => /(_ _ uqJ).
by apply/(le_trans _)/ler_sum=> y _; apply/ler_norm.
Qed.

Definition dlet := locked (mkdistr isd_mlet).

Lemma dletE y : dlet y = psum (fun x => mu x * f x y).
Proof. by unlock dlet. Qed.
End Bind.

Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).

Definition dlift {A : choiceType} (f : A -> {distr A / R}) :=
  fun d => \dlet_(x <- d) f x.

Fixpoint diter {A : choiceType} n (f : A -> {distr A / R}) :=
  fun a => (iter n (dlift f) (dunit a)).

(* -------------------------------------------------------------------- *)
Section BindTheory.
Variables (T U : choiceType).

Implicit Types (f g : T -> distr U) (mu nu : distr T).

Lemma dlet_null f : dlet f dnull =1 dnull.
Proof.
move=> x; rewrite dletE dnullE /= /mlet psum_eq0 //.
by move=> y; rewrite dnullE mul0r.
Qed.

Lemma dlet_unit f v : \dlet_(y <- dunit v) f y =1 f v.
Proof.
move=> y; rewrite dletE (psum_finseq (r := [:: v])) //.
  move=> x; rewrite !inE dunit1E mulf_eq0 => /norP[].
  by rewrite pnatr_eq0 eqb0 negbK => /eqP->.
by rewrite big_seq1 dunit1E eqxx mul1r ger0_norm.
Qed.

Lemma dlet_dunit_id mu : \dlet_(t <- mu) (dunit t) =1 mu.
Proof.
move=> x; rewrite dletE (psum_finseq (r := [:: x])) //.
  move=> y; rewrite !inE dunit1E mulf_eq0 pnatr_eq0.
  by case/norP; rewrite eqb0 negbK.
by rewrite big_seq1 dunit1E eqxx mulr1 ger0_norm.
Qed.

Lemma eq_in_dlet f g mu nu : {in dinsupp mu, f =2 g} -> mu =1 nu ->
  dlet f mu =1 dlet g nu.
Proof.
move=> eq_f eq_mu; unlock dlet=> y /=; apply/eq_psum=> x.
rewrite -eq_mu; case/boolP: (x \in dinsupp mu) => [/eq_f ->//|].
by move/dinsuppPn=> ->; rewrite !mul0r.
Qed.

Lemma summable_mu_wgtd (f : T -> R) mu :
  (forall x, 0 <= f x <= 1) -> summable (fun x => mu x * f x).
Proof.
move=> in01_f; apply/summableMr=> //.
exists 1 => x; case/andP: (in01_f x) => ge0_fx le1_fx.
by rewrite ger0_norm.
Qed.

Lemma summable_mlet f mu y : summable (fun x : T => mu x * (f x) y).
Proof. by apply/summable_mu_wgtd=> x; rewrite ge0_mu le1_mu1. Qed.

Lemma le_in_dlet f g mu : {in dinsupp mu, f <=2 g} ->
  dlet f mu <=1 dlet g mu.
Proof.                          (* summable -> refactor *)
move=> le_f; unlock dlet=> y /=; apply/le_psum/summable_mlet.
move=> x; rewrite mulr_ge0 //=; case: (mu x =P 0).
  by move=> ->; rewrite !mul0r.
by move/dinsuppPn/le_f/(_ y) => h; rewrite ler_pmul.
Qed.

Lemma le_mu_dlet f mu nu : mu <=1 nu -> dlet f mu <=1 dlet f nu.
Proof.
move=> le_mu x; unlock dlet; rewrite /= /mlet.
apply/le_psum/summable_mlet => y; rewrite mulr_ge0 //=.
case: (mu y =P 0) => [->|]; first by rewrite mul0r mulr_ge0.
by move=>/dinsuppPn=> h; rewrite ler_pmul.
Qed.

Lemma le_dlet f g mu nu :
    mu <=1 nu
  -> {in dinsupp mu, forall x, f x <=1 g x}
  -> \dlet_(x <- mu) f x <=1 \dlet_(x <- nu) g x.
Proof. move=> le_mu le_fg x.
by apply/(le_trans (le_in_dlet le_fg _))/le_mu_dlet.
Qed.

Lemma dletC (mu : {distr T / R}) (nu : {distr U / R}) y :
  (\dlet_(_ <- mu) nu) y = (dweight mu) * (nu y).
Proof.
rewrite dletE /pr [_ * nu y]mulrC -psumZ //=; apply/eq_psum.
by move=> /= x; rewrite mul1r mulrC.
Qed.

Lemma dinsupp_dlet f mu y :
  y \in dinsupp (\dlet_(x <- mu) f x) ->
    exists2 x, x \in dinsupp mu & f x y != 0.
Proof.
move/dinsuppP; rewrite dletE => /neq0_psum [x /eqP]; rewrite mulf_eq0.
by case/norP=> /eqP/dinsuppPn mux nz_fxy; exists x.
Qed.

Lemma dlet_dinsupp f mu x y :
  x \in dinsupp mu -> f x y != 0 -> y \in dinsupp (dlet f mu).
Proof.
move=> /dinsuppP /eqP mux nz_fxy; apply/dinsuppP; rewrite dletE.
move/eq0_psum => /(_ (summable_mlet _ _ _) x) => /eqP.
by rewrite mulf_eq0 (negbTE mux) (negbTE nz_fxy).
Qed.

Lemma dlet_eq0 (f : T -> U) mu y :
  {in dinsupp mu, forall x, f x != y} -> (\dlet_(x <- mu) dunit (f x)) y = 0.
Proof.
move=> h; unlock dlet => /=; apply/psum_eq0 => x.
case/boolP: (x \in dinsupp mu) => [|/dinsuppPn->];
  last by rewrite mul0r.
by move/h; rewrite dunit1E => /negbTE ->; rewrite mulr0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eq0_dlet (mu : {distr T / R}) (F : T -> {distr U / R}) y :
  (\dlet_(x <- mu) F x) y = 0 -> forall x, x \in dinsupp mu -> F x y = 0.
Proof.
unlock dlet; rewrite /= /mlet => /eq0_psum h x /dinsuppP /eqP mu_x.
have {h}/h: summable (fun x => mu x * F x y).
  apply/(le_summable (F2 := mu)) => // z.
  by rewrite mulr_ge0 //= ler_pimulr // le1_mu1.
by move/(_ x)/eqP; rewrite mulf_eq0 (negbTE mu_x) /= => /eqP.
Qed.
End BindTheory.

(* -------------------------------------------------------------------- *)
Section DLetDLet.
Context {T U V : choiceType} (f1 : T -> distr U) (f2 : U -> distr V).

Lemma dlet_dlet (mu : {distr T / R}) :
     \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x
  =1 \dlet_(y <- mu) (\dlet_(x <- f1 y) f2 x).
Proof.
move=> z; unlock dlet => /=; rewrite /mlet /=.
pose S y x := mu x * (f1 x y * f2 y z).
rewrite (eq_psum (F2 := fun y => psum (S^~ y))) => [x|].
  by rewrite -psumZ //; apply/eq_psum => y /=.
rewrite interchange_psum.
+ by move=> x; apply/summableZ/summable_mlet.
+ rewrite {}/S; apply/(le_summable (F2 := mu)) => //.
  move=> x; rewrite ge0_psum /= psumZ ?ler_pimulr //.
  apply/(le_trans _ (le1_mu (f1 x)))/le_psum => //.
  by move=> y; rewrite mulr_ge0 //= ler_pimulr ?le1_mu1.
apply/eq_psum=> y /=; rewrite -psumZr //.
by apply/eq_psum=> x /=; rewrite {}/S mulrA.
Qed.
End DLetDLet.

(* -------------------------------------------------------------------- *)
Section DLetAlg.
Context {T U : choiceType} (mu mu1 mu2 : {distr T / R}).

Lemma dlet_additive (f : T -> {distr U / R}) z :
  (forall x, mu x = mu1 x + mu2 x) -> (\dlet_(x <- mu) f x) z =
    (\dlet_(x <- mu1) f x) z + (\dlet_(x <- mu2) f x) z.
Proof.
move=> muD; rewrite !dletE -psumD /=.
  by move=> x; rewrite mulr_ge0. by move=> x; rewrite mulr_ge0.
  by apply/summable_mlet. by apply/summable_mlet.
by apply/eq_psum=> x /=; rewrite -mulrDl -muD.
Qed.
End DLetAlg.

(* -------------------------------------------------------------------- *)
Definition mlim T (f : nat -> distr T) : T -> R :=
  fun x => real_of_er(*TODO: broken coercion*) (nlim (fun n => f n x)).

Lemma isd_mlim T (f : nat -> distr T) : isdistr (mlim f).
Proof. split=> [x|J]; rewrite /mlim.
+ case: nlimP=> // l cvSl; apply/le0R/(ncvg_geC _ cvSl).
  by move=> n; apply/ge0_mu.
move=> uqJ; pose F j :=
  if `[< iscvg (fun n => f n j) >] then fun n => f n j else 0%:S.
apply/(@le_trans _ _ (\sum_(j <- J) (real_of_er (*TODO: broken coercion*) (nlim (F j) (*: R*))))).
  apply/ler_sum=> j _; rewrite /F; case/boolP: `[< _ >] => //.
  move/asboolPn=> h; rewrite nlimC; case: nlimP=> //.
  by case=> // l cf; case: h; exists l.
rewrite -lee_fin -nlim_sumR => [i _|].
  rewrite /F; case/boolP: `[< _ >] => [/asboolP //|].
  by move=> _; apply/iscvgC.
rewrite leNgt; apply/negP; pose s n := \sum_(j <- J) F j n.
move/ncvg_gt=> -/(_ s (nlim_ncvg _)) [].
  suff: iscvg s by case=> l cs; exists l%:E.
  apply/iscvg_sum=> j _; rewrite /F; case/boolP: `[< _ >].
    by move/asboolP. by move=> _; apply/iscvgC.
move=> K /(_ _ (leqnn K)) /=; apply/negP; rewrite -leNgt.
apply/(@le_trans _ _ (\sum_(j <- J) f K j)); last first.
  have /(gerfinseq_psum uqJ) := summable_mu (f K).
  move/le_trans=> -/(_ _ (le1_mu (f K)))=> h.
  by apply/(le_trans _ h)/ler_sum=> i _; apply/ler_norm.
apply/ler_sum=> j _; rewrite /F; case/boolP: `[< _ >] => //.
by move=> _; apply/ge0_mu.
Qed.

Definition dlim T (f : nat -> distr T) :=
  locked (mkdistr (isd_mlim f)).

Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).

Lemma dlimE T (f : nat -> distr T) x :
  (\dlim_(n) f n) x = real_of_er(*TODO: broken coercion*) (nlim (fun n => f n x)).
Proof. by unlock dlim. Qed.

(* -------------------------------------------------------------------- *)
Section DLimTheory.
Variables (T U : choiceType).

Implicit Types (f g : nat -> distr T) (h : T -> {distr U / R}).
Implicit Types (mu : {distr T / R}).

Lemma dlimC mu : \dlim_(n) mu =1 mu.
Proof. by move=> x; rewrite !dlimE; rewrite nlimC. Qed.

Lemma eq_dlim f g : f =2 g -> dlim f =1 dlim g.
Proof.
move=> eq_f; unlock dlim=> x /=; rewrite /mlim; congr (_ _).
by apply/eq_nlim => n; rewrite eq_f.
Qed.

Lemma eq_from_dlim K f g :
  (forall n, (K <= n)%N -> f n =1 g n) -> dlim f =1 dlim g.
Proof.
move=> eq_fg x; rewrite !dlimE; congr (_ _).
by apply/(eq_from_nlim (K := K)); move=> n /eq_fg /(_ x).
Qed.

Definition dlim_bump (mu : nat -> {distr T / R}) :
  dlim (fun n => mu n.+1) =1 dlim mu.
Proof. by move=> x; rewrite !dlimE -[in RHS]nlim_bump. Qed.

Definition dlim_lift (mu : nat -> {distr T / R}) p :
  dlim (fun n => mu (n + p)%N) =1 dlim mu.
Proof. by move=> x; rewrite !dlimE (nlim_lift (fun n => (mu n) x)). Qed.

Definition dcvg {T : choiceType} (f : nat -> {distr T / R}) :=
  forall x, exists l, ncvg (fun n => f n x) l.

Definition ducvg {T : choiceType} (f : nat -> {distr T / R}) :=
  exists l, forall x, ncvg (fun n => f n x) l.

CoInductive dlim_spec f (x : T) : R -> Type :=
| DLimCvg : forall l : R, 0 <= l -> l <= 1 ->
    ncvg (fun n => f n x) l%:E -> dlim_spec f x l

| DLimOut : ~ (exists l : {ereal R}, ncvg (fun n => f n x) l) ->
    dlim_spec f x 0.

Lemma dlimP f x : dlim_spec f x (dlim f x).
Proof.
rewrite dlimE; case: nlimP => [l h|?] /=; last by apply/DLimOut.
have: (0%:E <= l)%E by apply/ncvg_geC: h => n; apply/ge0_mu.
have: (l <= 1%:E)%E by apply/ncvg_leC: h => n; apply/le1_mu1.
by case: l h => // l h /= ge0_l ge1_; apply/DLimCvg.
Qed.

Lemma dcvgP f : dcvg f -> forall x,
  exists2 l, (0 <= l <= 1) & ncvg (f^~ x) l%:E.
Proof.
move=> cv_f x; case: (dlimP f x) => [l ge0_l le1_l cv|].
  by exists l => //; apply/andP; split.
by case; case: (cv_f x).
Qed.

Lemma dcvg_homo f :
  (forall n m, (n <= m)%N -> f n <=1 f m) -> dcvg f.
Proof.
move=> mn_f x; have: forall n m, (n <= m)%N -> f n x <= f m x.
  by move=> n m /mn_f; apply.
case/ncvg_mono_bnd => {mn_f}; first apply/asboolP/nboundedP.
  exists 2%:R => // n; apply/(@le_lt_trans _ _ 1%:R)/ltr_nat.
  by rewrite ger0_norm // le1_mu1.
by move=> y h; exists y%:E.
Qed.

Lemma ge0_dlim f : forall x, 0 <= dlim f x.
Proof. by move=> x; case: dlimP. Qed.

Lemma le1_dlim f : forall x, dlim f x <= 1.
Proof. by move=> x; case: dlimP => // _; apply/ler01. Qed.

Lemma le_dlim f g :
  (forall n, f n <=1 g n) -> dcvg g -> dlim f <=1 dlim g.
Proof.
move=> le dcvg_g x; case: dlimP => [|_]; last by apply/ge0_dlim.
move=> l _ _ h; case: dlimP => [l' _ _ h'|]; last by case.
by rewrite -lee_fin; apply/(ncvg_le _ h' h).
Qed.

Lemma leub_dlim f mu : (forall n, f n <=1 mu) -> dlim f <=1 mu.
Proof.
move=> le x; apply/(@le_trans _ _ ((\dlim_(n) mu) x)).
  by apply/le_dlim => // y; exists (mu y)%:E; apply/ncvgC.
by rewrite dlimE nlimC.
Qed.

Lemma dlim_ub f k :
  (forall n m, (n <= m)%N -> f n <=1 f m) -> f k <=1 dlim f.
Proof.
move=> mn_f x; rewrite dlimE -lee_fin; pose u n := f n x.
apply/(ncvg_homo_le (u := u))=> [m n /mn_f|]; first by apply.
move/dcvg_homo: mn_f => /dcvgP /(_ x) [l _].
by move=> cv; rewrite (nlimE cv).
Qed.

Lemma dlet_lim f h : (forall n m, (n <= m)%N -> f n <=1 f m) ->
  \dlet_(x <- dlim f) h x =1 \dlim_(n) \dlet_(x <- f n) h x.
Proof. Admitted.

Lemma dlim_let (f : nat -> T -> {distr U / R}) (mu : {distr T / R}) :
  (forall x n m, (n <= m)%N -> f n x <=1 f m x) ->
  \dlim_(n) \dlet_(x <- mu) (f n x) =1
    \dlet_(x <- mu) \dlim_(n) (f n x).
Proof using Type. Admitted.
End DLimTheory.

(* -------------------------------------------------------------------- *)
Section Marginals.
Variable (T U : choiceType) (h : T -> U) (mu : distr T).

Definition dmargin := \dlet_(x <- mu) (dunit (h x)).

Lemma dmarginE : dmargin = \dlet_(y <- mu) (dunit (h y)).
Proof. by []. Qed.
End Marginals.

(* -------------------------------------------------------------------- *)
Section MarginalsTh.
Variable (T U V : choiceType).

Lemma dmargin_psumE (mu : {distr T / R}) (f : T -> U) y :
  (dmargin f mu) y = psum (fun x => (f x == y)%:R * mu x).
Proof.
rewrite dmarginE dletE; apply/eq_psum => x //=.
by rewrite mulrC dunit1E.
Qed.

Lemma dlet_dmargin (mu : {distr T / R}) (f : T -> U) (g : U -> {distr V / R}):
  \dlet_(u <- dmargin f mu) g u =1 \dlet_(t <- mu) (g (f t)).
Proof.
move=> x; rewrite dlet_dlet; apply: eq_in_dlet=> //.
by move=> y _ z; rewrite dlet_unit.
Qed.

Lemma dmargin_dlet (mu : {distr T / R}) (f : U -> V) (g : T -> {distr U / R}):
  dmargin f (\dlet_(t <- mu) g t) =1 \dlet_(t <- mu) (dmargin f (g t)).
Proof. by apply/dlet_dlet. Qed.

Lemma dmargin_dunit (t : T) (f : T -> U):
  dmargin f (dunit t) =1 dunit (f t) :> {distr U / R}.
Proof. by apply/dlet_unit. Qed.
End MarginalsTh.
End Std.

Notation dfst mu := (dmargin fst mu).
Notation dsnd mu := (dmargin snd mu).

(* -------------------------------------------------------------------- *)
Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).
Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).

(* -------------------------------------------------------------------- *)
Section DSwap.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B) / R}).

Definition dswap : {distr (B * A) / R} :=
  dmargin (fun xy => (xy.2, xy.1)) mu.
End DSwap.

(* -------------------------------------------------------------------- *)
Section DSwapCoreTheory.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B) / R}).

Lemma dswapE xy : dswap mu xy = mu (xy.2, xy.1).
Proof.
rewrite dletE /= (psum_finseq (r := [:: (xy.2, xy.1)])) //.
  case=> a b; rewrite !inE dunit1E /= mulf_eq0.
  by case/norP=> _; rewrite pnatr_eq0 eqb0 negbK=> /eqP <-.
by case: xy=> x y; rewrite big_seq1 dunit1E /= eqxx mulr1 ger0_norm.
Qed.
End DSwapCoreTheory.

(* -------------------------------------------------------------------- *)
Section DSwapTheory.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B) / R}).

Lemma dswapK : dswap (dswap mu) =1 mu.
Proof. by case=> x y; rewrite !dswapE. Qed.

Lemma dinsupp_swap xy : (xy.2, xy.1) \in dinsupp mu ->
  xy \in dinsupp (dswap mu).
Proof.
by move=> h; apply/dinsuppP; rewrite dswapE; apply/dinsuppPn.
Qed.

Lemma dfst_dswap : dfst (dswap mu) =1 dsnd mu.
Proof.
move=> z; rewrite dlet_dlet; apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.

Lemma dsnd_dswap : dsnd (dswap mu) =1 dfst mu.
Proof.
move=> z; rewrite dlet_dlet; apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.
End DSwapTheory.

(* -------------------------------------------------------------------- *)
Section DFst.
Context {R : realType} {T U : choiceType}.

Lemma dfstE (mu : {distr (T * U) /  R}) x :
  dfst mu x = psum (fun y => mu (x, y)).
Proof.
rewrite dmargin_psumE /=; pose h y : T * U := (x, y).
rewrite (reindex_psum (P := [pred z | z.1 == x]) (h := h)) /=.
+ case=> a b; rewrite !inE/= mulf_eq0 => /norP[].
  by rewrite pnatr_eq0 eqb0 negbK.
+ by exists snd => [z|[z1 z2]]; rewrite !inE //= => /eqP ->.
by apply/eq_psum => y; rewrite eqxx mul1r.
Qed.

Lemma summable_fst (mu : {distr (T * U) / R}) x :
  summable (fun y => mu (x, y)).
Proof.
have /summable_seqP /= := summable_mu mu => -[M ge0_M h].
apply/summable_seqP; exists M => // J uqJ; pose X := [seq (x, y) | y <- J].
apply/(le_trans _ (h X _)); last by rewrite map_inj_uniq // => y1 y2 [].
by rewrite le_eqVlt big_map eqxx.
Qed.
End DFst.

(* -------------------------------------------------------------------- *)
Section DSnd.
Context {R : realType} {T U : choiceType}.

Lemma dsndE (mu : {distr (T * U) / R}) y :
  dsnd mu y = psum (fun x => mu (x, y)).
Proof. by rewrite -dfst_dswap dfstE; apply/eq_psum=> x; rewrite dswapE. Qed.

Lemma summable_snd (mu : {distr (T * U) / R}) y :
  summable (fun x => mu (x, y)).
Proof.
have := summable_fst (dswap mu) y; apply/eq_summable.
by move=> x /=; rewrite dswapE.
Qed.
End DSnd.

(* -------------------------------------------------------------------- *)
Section PrCoreTheory.
Context {R : realType} {T : choiceType}.

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma summable_pr E mu : summable (fun x => (E x)%:R * mu x).
Proof.
apply/(le_summable (F2 := mu)) => [x|]; last by apply/summable_mu.
  by rewrite mulr_ge0 ?ler0n //= ler_pimull // lern1 leq_b1.
Qed.

Lemma pr_pred0 mu : \P_[mu] pred0 = 0.
Proof. by rewrite /pr psum_eq0 // => x /=; rewrite mul0r. Qed.

Lemma pr_pred1 mu x : mu x = \P_[mu] (pred1 x).
Proof.
rewrite /pr (psum_finseq (r := [:: x])) // => [y|].
  by rewrite !inE; case: (y =P x); rewrite ?(mul0r, eqxx).
by rewrite big_seq1 /= eqxx mul1r ger0_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma pr_exp mu (E : pred T) : \P_[mu] E = \E_[mu] (fun m => (E m)%:R).
Proof. by rewrite /pr psum_sum // => x; rewrite mulr_ge0 // ler0n. Qed.

Lemma pr_predT mu : \P_[mu] predT = psum mu.
Proof. by apply/eq_psum=> x; rewrite mul1r. Qed.

Lemma pr_dunit E x : \P_[dunit x] E = (E x)%:R :> R.
Proof.
rewrite /pr (psum_finseq (r := [:: x])) //.
  move=> y; rewrite !inE dunit1E [x==_]eq_sym.
  by case: (y =P x) => //; rewrite mulr0 eqxx.
by rewrite big_seq1 dunit1E eqxx mulr1 ger0_norm ?ler0n.
Qed.

Lemma exp_dunit (f : T -> R) (x : T) : \E_[dunit x] f = f x.
Proof.
rewrite /esp (sum_seq1 x) => [y|]; rewrite dunit1E.
  by case: (x == y) => //; rewrite mulr0 eqxx.
by rewrite eqxx mulr1.
Qed.

Lemma exp_cst mu r : \E_[mu] (fun _ => r) = \P_[mu] predT * r.
Proof.
by rewrite pr_predT psum_sum // [RHS]mulrC -sumZ; apply/eq_sum.
Qed.

Lemma exp0 mu : \E_[mu] (fun _ => 0) = 0.
Proof. by rewrite exp_cst mulr0. Qed.

Lemma has_expC mu c : \E?_[mu] (fun _ => c).
Proof. by apply/summableMl => //; exists `|c|. Qed.

Lemma has_exp0 mu : \E?_[mu] (fun _ => 0).
Proof. by apply/(has_expC mu 0). Qed.

Lemma has_exp1 mu : \E?_[mu] (fun _ => 1).
Proof. by apply/(has_expC mu 1). Qed.

Lemma has_expZ mu c F : \E?_[mu] F -> \E?_[mu] (c \*o F).
Proof.
move=> heF; have: summable (c \*o (F \* mu)) by apply/summableZ.
by apply/eq_summable => x /=; rewrite mulrA.
Qed.

Lemma expZ mu F c : \E_[mu] (c \*o F) = c * \E_[mu] F.
Proof. by rewrite -sumZ; apply/eq_sum=> x /=; rewrite mulrA. Qed.

Lemma ge0_pr A mu : 0 <= \P_[mu] A.
Proof. by apply/ge0_psum. Qed.

Lemma ge0_prc A B mu : 0 <= \P_[mu, B] A.
Proof. by rewrite /prc mulr_ge0 ?invr_ge0 // ge0_pr. Qed.

Lemma eq_in_pr A B mu :
  {in dinsupp mu, A =i B} -> \P_[mu] A = \P_[mu] B.
Proof.
move=> eq_AB; apply/eq_psum => x; case/boolP: (x \in dinsupp mu).
  by move/eq_AB; rewrite -!topredE => /= ->.
by move/dinsuppPn=> ->; rewrite !mulr0.
Qed.

Lemma eq_pr A B mu : A =i B -> \P_[mu] A = \P_[mu] B.
Proof. by move=> eq_AB; apply/eq_in_pr=> x _; apply/eq_AB. Qed.

Lemma eq_exp mu (f1 f2 : T -> R):
   {in dinsupp mu, f1 =1 f2} -> \E_[mu] f1 = \E_[mu] f2.
Proof.
move=> eq_f; apply/eq_sum => x; case/boolP: (x \in dinsupp mu).
  by move/eq_f=> ->. by move/dinsuppPn=> ->; rewrite !mulr0.
Qed.

Lemma pr_pred0_eq (mu : {distr T / R}) (E : pred T) :
  E =1 pred0 -> \P_[mu] E = 0.
Proof. by move=> eq; rewrite -(pr_pred0 mu); apply/eq_pr. Qed.
End PrCoreTheory.

(* -------------------------------------------------------------------- *)
Section PrTheory.
Context {R : realType} {T U : choiceType} {I : eqType}.

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma pr_dlet E f (mu : {distr U / R}) :
  \P_[dlet f mu] E = \E_[mu] (fun x => \P_[f x] E).
Proof.
rewrite /esp -psum_sum => [x|]; first by rewrite mulr_ge0 ?ge0_pr.
rewrite /pr; unlock dlet => /=; rewrite /mlet /=.
pose F x y := (E x)%:R * (mu y * f y x).
transitivity (psum (fun x => psum (fun y => F x y))); rewrite {}/F.
  by apply/eq_psum => x; rewrite -psumZ ?ler0n.
rewrite interchange_psum /=; last first.
  apply/eq_psum=> y /=; rewrite mulrC -psumZ //.
  by apply/eq_psum=> x /=; rewrite mulrCA.
+ have := summable_pr E (dlet f mu); apply/eq_summable.
  by move=> x; rewrite dletE psumZ ?ler0n.
+ by move=> y; apply/summable_condl/summable_mlet.
Qed.

Lemma pr_dmargin E f (mu : {distr U / R}) :
  \P_[dmargin f mu] E = \P_[mu] [pred x | f x \in E].
Proof.
by rewrite /dmargin pr_dlet pr_exp; apply/eq_exp=> x _; rewrite pr_dunit.
Qed.

Lemma eq0_pr A mu :
  (forall x, x \in dinsupp mu -> x \notin A) -> \P_[mu] A = 0.
Proof.
move=> h; apply/psum_eq0=> x; apply/eqP.
rewrite mulf_eq0 orbC; case/boolP: (mu x == 0) => //=.
by move/h; rewrite -topredE /= => /negbTE->.
Qed.

Lemma eq0_prc A B mu :
    (forall x, x \in dinsupp mu -> x \in B -> x \notin A)
  -> \P_[mu, B] A = 0.
Proof.
move=> h; rewrite /prc eq0_pr ?mul0r // => x /h {h} /orb_idl.
by rewrite negb_and /= => <-; rewrite orbAC orbN.
Qed.

Lemma subset_pr A B mu : {subset B <= A} -> \P_[mu] B <= \P_[mu] A.
Proof.
move=> le_BA; apply/le_psum; last first.
  apply/summableMl => //; exists 1=> // x.
  by rewrite ger0_norm ?(ler0n, lern1) ?leq_b1.
move=> x; rewrite mulr_ge0 ?ler0n ?ler_wpmul2r //.
rewrite ler_nat; have := le_BA x; rewrite -!topredE /=.
by case: (B x) => // ->.
Qed.

Lemma le1_pr A mu : \P_[mu] A <= 1.
Proof.
apply/(@le_trans _ _ \P_[mu] predT).
  by apply/subset_pr. by rewrite pr_predT le1_mu.
Qed.

Lemma le_exp mu f1 f2: \E?_[mu] f1 -> \E?_[mu] f2 ->
  f1 <=1 f2 -> \E_[mu] f1 <= \E_[mu] f2.
Proof.
move=> sm1 sm2 le_f; apply/le_sum => //.
by move=> x; rewrite ler_wpmul2r.
Qed.

Lemma le_in_pr E1 E2 mu :
  (forall x, x \in dinsupp mu -> x \in E1 -> x \in E2) ->
    \P_[mu] E1 <= \P_[mu] E2.
Proof.
move=> le; rewrite /pr; apply/le_psum; last by apply/summable_pr.
move=> x; rewrite mulr_ge0 ?ler0n //=; case/boolP: (x \in dinsupp mu).
  move/le; rewrite -!topredE /= => E12; rewrite ler_wpmul2r //.
  by rewrite ler_nat; case: (E1 x) E12 => // ->.
by move/dinsuppPn=> ->; rewrite !mulr0.
Qed.

Lemma le_mu_pr A mu nu :
    (forall x, x \in dinsupp nu -> x \in A -> nu x <= mu x)
  -> \P_[nu] A <= \P_[mu] A.
Proof.
move=> h; apply/le_psum; last by apply/summable_pr.
move=> x; rewrite mulr_ge0 ?ler0n //=.
case/boolP: (x \in dinsupp nu) => [/h {h}h|]; last first.
  by move/dinsuppPn=> ->; rewrite mulr0 mulr_ge0 ?ler0n.
by case/boolP: (A x) => [/h|]; rewrite ?(mul0r, mul1r).
Qed.

Lemma le1_prc A B mu : \P_[mu, B] A <= 1.
Proof.
have := ge0_pr B mu; rewrite /prc le_eqVlt.
case/orP=> [/eqP<-|]; first by rewrite invr0 mulr0 ler01.
by move/ler_pdivr_mulr=> ->; rewrite mul1r le_in_pr // => x _ /andP[].
Qed.

Lemma prc_sum A mu : 0 < \P_[mu] A ->
  psum (fun x => \P_[mu, A] (pred1 x)) = 1.
Proof.
move=> gt0_pE; rewrite psumZr ?(invr_ge0, ge0_pr) //.
rewrite (eq_psum (F2 := (fun x => (A x)%:R * mu x))); last first.
  by rewrite divff // gt_eqF.
move=> x /=; rewrite /pr (psum_finseq (r := [:: x])) ?big_seq1 //=.
  move=> y; rewrite !inE; case: (y == x) => //=.
  by rewrite mul0r eqxx.
by rewrite !inE eqxx -topredE ger0_norm ?mulr_ge0 ?ler0n.
Qed. 

Lemma pr_eq0 mu E : \P_[mu] E = 0 -> forall x, x \in E -> mu x = 0.
Proof.
move/eq0_psum=> /(_ (summable_pr _ _)) => h x xE; move/(_ x): h.
by move: xE; rewrite -topredE /= => ->; rewrite mul1r.
Qed.

Lemma prID A B mu :
  \P_[mu] A = \P_[mu] [predI A & B] + \P_[mu] [predI A & predC B].
Proof.
rewrite {1}/pr (psumID B); first by apply/summable_pr.
congr (_ + _); apply/eq_psum => x; rewrite !inE -!topredE /=;
  by rewrite mulrA -natrM mulnb andbC.
Qed.

Lemma pr_or_indep (A B : pred T) (mu : {distr T / R}) :
  (forall x, x \in A -> x \notin B) ->
    \P_[mu] [predU A & B] = \P_[mu] A + \P_[mu] B.
Proof.
move=> dsj; rewrite /pr -psumD; try solve [
  by apply/summable_pr | by move=> x; rewrite mulr_ge0 ?ler0n
].
apply/eq_psum=> x /=; rewrite -mulrDl -!topredE /= -natrD.
case/boolP: (A x) => Ax; case/boolP: (B x) => Bx //=.
by move/dsj: Ax; rewrite -topredE /= Bx.
Qed.

Lemma pr_mem_map f mu (r : seq U) : uniq r ->
    \P_[mu] [pred x | f x \in r]
  = \sum_(y <- r) \P_[mu] [pred x | f x == y].
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pr_pred0_eq //.
case/andP=> yNr /ih {ih}h; rewrite big_cons -h -pr_or_indep.
  by move=> x; rewrite !inE => /eqP->. by apply/eq_pr.
Qed.

Lemma pr_mem mu (r : seq T) : uniq r ->
  \P_[mu] [pred x | x \in r] = \sum_(x <- r) mu x.
Proof.
elim: r => [_|y r ih]; first by rewrite big_nil pr_pred0_eq //.
case/andP=> yNr /ih {ih}h; rewrite big_cons /= pr_pred1.
by rewrite -h -pr_or_indep // => x /eqP ->.
Qed.

Lemma pr_bigor_indep mu (P : I -> pred T) (r : seq I) :
    uniq r
  -> (forall p1 p2 x, p1 != p2 -> p1 \in r -> p2 \in r -> x \in P p1 -> x \notin P p2)
  -> \P_[mu] [pred x | has [pred p | x \in P p] r]
  = \sum_(p <- r) \P_[mu] (P p).
Proof.
move=> uq_r dj; pose S x := \big[orb/false]_(p <- r) (x \in P p).
rewrite (eq_pr (B := S)) => [x|]; first by rewrite !inE -big_has.
rewrite {}/S; elim: r uq_r dj => [_|p r ih /andP[pNr /ih {ih}h]] dj.
  by rewrite big_nil pr_pred0_eq // => x; rewrite big_nil.
rewrite big_cons -h => [p1 p2 x ne_p p1r p2r|].
  by apply/dj=> //; rewrite in_cons (p1r, p2r) orbT.
rewrite -pr_or_indep => [x xNPp|].
  rewrite -topredE /= big_has; apply/hasPn => y y_in_r.
  apply/(dj p); rewrite ?in_cons ?(eqxx, y_in_r, orbT) //.
  by apply/contra: pNr=> /eqP->.
by apply/eq_pr=> x; rewrite -!topredE /= big_cons.
Qed.

Lemma pr_or A B mu : \P_[mu] [predU A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predI A & B].
Proof.
apply/eqP; rewrite eq_sym subr_eq [in X in _==X]addrC; apply/eqP.
rewrite (prID _ B) -addrA -pr_or_indep => [x|].
  by rewrite !inE => /andP[].
congr (_ + _); apply/eq_pr => x; rewrite !inE -!topredE /=.
by apply/orb_id2r => /negbTE ->; rewrite andbT.
Qed.

Lemma pr_and A B mu : \P_[mu] [predI A & B] =
  \P_[mu] A + \P_[mu] B - \P_[mu] [predU A & B].
Proof. by rewrite pr_or opprB addrCA subrr addr0. Qed.

Lemma ler_pr_or A B mu :
  \P_[mu] [predU A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_or ler_subl_addr ler_addl ge0_pr. Qed.

Lemma ler_pr_and A B mu :
  \P_[mu] [predI A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_and ler_subl_addr ler_addl ge0_pr. Qed.

Lemma pr_predC E mu: \P_[mu](predC E) = \P_[mu] predT - \P_[mu] E.
Proof.
apply/esym/eqP; rewrite subr_eq -pr_or_indep //.
by apply/eqP/eq_pr=> x; rewrite !inE orNb.
Qed.

Lemma pr_split B A mu : \P_[mu] A =
    \P_[mu]        B  * \P_[mu,       B] A
  + \P_[mu] (predC B) * \P_[mu, predC B] A.
Proof.
suff h A' B': \P_[mu] [predI A' & B'] = \P_[mu] B' * \P_[mu, B'] A'.
  by rewrite (prID _ B); congr (_ + _); apply/h.
rewrite /prc mulrCA; have [] := eqVneq (\P_[mu] B') 0; last first.
  by move=> nzPB'; rewrite divff // mulr1.
move=> zPB'; rewrite zPB' invr0 !mulr0; apply/eq0_pr.
move=> x mux; move/pr_eq0: zPB' => /(_ x) h; rewrite !inE.
by apply/negP=> /andP[_ /h] /dinsuppP.
Qed.

Lemma exp_split A f mu : \E?_[mu] f -> \E_[mu] f =
    \P_[mu]        A  * \E_[mu,       A] f
  + \P_[mu] (predC A) * \E_[mu, predC A] f.
Proof using Type. Admitted.

Lemma has_esp_bounded f mu :
  (exists M, forall x, `|f x| < M) -> \E?_[mu] f.
Proof.                          (* TO BE REMOVED *)
case=> M ltM; rewrite /has_esp; apply/summable_seqP.
exists (Num.max M 0); first by rewrite lexU lexx orbT.
move=> J uqJ; apply/(@le_trans _ _ (\sum_(j <- J) M * mu j)).
  apply/ler_sum=> j _; rewrite normrM [X in _*X]ger0_norm //.
  by apply/ler_wpmul2r=> //; apply/ltW.
case: (ltrP M 0) => [lt0_M|ge0_M].
  rewrite (elimT join_idPl) ?(ltW lt0_M) // -mulr_sumr.
  by rewrite nmulr_rle0 //; apply/sumr_ge0.
by rewrite (elimT join_idPr) // -mulr_sumr ler_pimulr // -pr_mem ?le1_pr.
Qed.

Lemma bounded_has_exp mu F :
  (exists M, forall x, `|F x| <= M) -> \E?_[mu] F.
Proof. by move=> leM; apply/summableMl. Qed.

Lemma summable_has_exp mu F : summable F -> \E?_[mu] F.
Proof.
move=> smF; apply/summableMr => //; exists 1.
by move=> x; rewrite ger0_norm // le1_mu1.
Qed.

Lemma exp_le_bd mu F (M : R) :
  0 <= M -> (forall x, `|F x| <= M) -> \E_[mu] F <= M.
Proof.
move=> ge0M bd; apply/(@le_trans _ _ (\E_[mu] (fun _ => M))).
+ apply/le_exp.
  + by apply/bounded_has_exp; exists M.
  + by apply/has_expC.
  + by move=> x; apply/(le_trans _ (bd x))/ler_norm.
by rewrite exp_cst ler_pimull // le1_pr.
Qed.

Lemma exp_dlet mu (nu : T -> {distr U / R}) F :
  (forall eta, \E?_[eta] F) ->
    \E_[dlet nu mu] F = \E_[mu] (fun x => \E_[nu x] F).
Proof using Type*. Admitted.
End PrTheory.

(* -------------------------------------------------------------------- *)
Section Jensen.
Context {R : realType} {I : finType}.

Definition convexon (a b : {ereal R}) (f : R -> R) :=
  forall x y, (a <= x%:E <= b)%E -> (a <= y%:E <= b)%E ->
    forall t, 0 <= t <= 1 ->
      f (t * x + (1 - t) * y) <= t * (f x) + (1 - t) * (f y).

Notation convex f := (convexon -oo +oo f).

Section Jensen.
Context (f : R -> R) (x l : I -> R).

Hypothesis cvx_f : convex f.
Hypothesis ge0_l : forall x, 0 <= l x.
Hypothesis eq1_l : \sum_i (l i) = 1.

Lemma Jensen : f (\sum_i (l i * x i)) <= \sum_i (l i * f (x i)).
Proof.
case: (index_enum I) eq1_l => [|i s]; rewrite ?(big_nil, big_cons).
  by move/esym/eqP; rewrite oner_eq0.
elim: {i} s (l i) (ge0_l i) (x i) => [|j s ih] li ge0_li xi.
  by rewrite !big_nil !addr0 => ->; rewrite !mul1r.
rewrite !big_cons; have := ge0_l j; rewrite le_eqVlt.
case/orP => [/eqP<-|gt0_lj].
  by rewrite !Monoid.simpm /=; apply/ih.
rewrite !addrA => eq1; pose z := (li * xi + l j * x j) / (li + l j).
have nz_lij: li + l j != 0 by rewrite gt_eqF ?ltr_paddl.
have/ih := eq1 => -/(_ _ z); rewrite [_ * (_ / _)]mulrC.
rewrite mulfVK // => {ih}ih; apply/(le_trans (ih _)).
  by rewrite addr_ge0 ?ge0_l.
rewrite ler_add2r {ih}/z mulrDl ![_*_/_]mulrAC.
set c1 : R := _ / _; set c2 : R := _ / _; have eqc2: c2 = 1 - c1.
  apply/(mulfI nz_lij); rewrite mulrBr mulr1 ![(li + l j)*_]mulrC.
  by apply/eqP; rewrite !mulfVK // eq_sym subr_eq addrC.
set c := (li + l j); pose z := (c * c1 * f xi + c * c2 * f (x j)).
apply/(@le_trans _ _ z); last by rewrite /z ![_*(_/_)]mulrC !mulfVK.
rewrite {}/z -![c * _ * _]mulrA -mulrDr ler_wpmul2l ?addr_ge0 //.
rewrite eqc2 cvx_f // ?lee_ninfty ?lee_pinfty // divr_ge0 ?addr_ge0 //=.
by rewrite ler_pdivr_mulr ?mul1r ?ler_addl ?ltr_paddl.
Qed.
End Jensen.
End Jensen.

Notation convex f := (convexon \-inf \+inf f).

(* -------------------------------------------------------------------- *)
