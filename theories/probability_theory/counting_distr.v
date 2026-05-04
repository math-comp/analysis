From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra.
From mathcomp Require Import xfinmap constructive_ereal reals discrete.
From mathcomp Require Import realseq realsum.
From mathcomp Require Import esum sequences normedtype ereal cardinality fsbigop.

(* Should be removed *)
From mathcomp Require Import numfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.  (* remove this line when requiring MathComp >= 2.6 *)

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
Reserved Notation "\Ee_[ mu ] f" (at level 2, format "\Ee_[ mu ]  f").

Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

(* -------------------------------------------------------------------- *)

HB.mixin Record isDistribution (R : realType) (T : choiceType) (mu : T -> R) :=
  {
    mu_positive :  forall x, 0 <= mu x ;
    mu_summable :  summable [set: T] (EFin \o mu);
    mu_sum_le_one  :  (esum [set: T] (EFin \o mu) <= 1)%E;
  }.

HB.structure Definition Distribution (R : realType) (T : choiceType) :=
  {f of @isDistribution R T f}.

Notation "{ 'distr' T / R }" := (@Distribution.type R T)
  (at level 0, T at level 2, format "{ 'distr'  T  /  R }")
  : type_scope.

(* -------------------------------------------------------------------- *)
Section DistrCoreTh.
Context {R : realType} (T : choiceType) (mu : {distr T / R}).

Lemma ge0_mu : forall x, 0 <= mu x.
Proof. exact: mu_positive. Qed.

Lemma le1_mu : (esum [set: T] (EFin \o mu) <= 1)%E.
Proof. exact: mu_sum_le_one. Qed.

Lemma summable_mu : summable [set: T] (EFin \o mu).
Proof. exact: mu_summable.  Qed.
End DistrCoreTh.

#[global] Hint Extern 0 (is_true (0 <= _)) => solve [apply: ge0_mu] : core.
#[global] Hint Resolve le1_mu summable_mu : core.

(* -------------------------------------------------------------------- *)
Section Clamp.
Context {R : realType}.

Definition clamp (x : R) :=
  Num.max (Num.min x 1) 0.

Lemma ge0_clamp x : 0 <= clamp x.
Proof. by rewrite le_max lexx orbT. Qed.

Lemma le1_clamp x : clamp x <= 1.
Proof. by rewrite ge_max ge_min lexx ler01 orbT. Qed.

Definition cp01_clamp := (ge0_clamp, le1_clamp).

Lemma clamp_in01 x : 0 <= x <= 1 -> clamp x = x.
Proof. by case/andP=> ge0_x le1_x; rewrite /clamp min_l ?max_l. Qed.

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

Definition pr   mu E := fine (esum [set: T] (EFin \o (fun x => (E x)%:R * mu x))).
Definition prc  mu E A := pr mu [predI E & A] / pr mu A.
Definition esp  mu f   := fine (esum [set: T] (EFin \o (fun x => f x * mu x))).
Definition espc mu f A := fine (esum [set: T] (EFin \o (fun x => f x * prc mu (pred1 x) A))).

Definition has_esp mu f := summable [set: T] (EFin \o (fun x => f x * mu x)).
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

Local Lemma isd2 : summable [set: T] (EFin \o mu).
Proof.
case isd => ? h2.
rewrite /summable (@le_lt_trans _ _ 1%:E) ?ltey//.
rewrite ge0_esum //  ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin // lee_fin fsbig_finite //=.
rewrite (eq_bigr (fun x => mu x)).
+ by move => ??; rewrite ger0_norm.
by apply: h2.
Qed.

Local Lemma isd3 : (esum [set: T] (EFin \o mu) <= 1)%E.
Proof.
case isd => ? h2.
rewrite ge0_esum.
+ by move => ? _;rewrite lee_fin.
rewrite ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin // lee_fin fsbig_finite //=.
by apply: h2.
Qed.

Definition mkdistrd := @isDistribution.Build R T mu isd1 isd2 isd3.

Definition ispredistr {T : choiceType} (mu : T -> R) :=
  [/\ forall x, 0 <= mu x & summable [set: T] (EFin \o mu)].

End DistrTheory.

Lemma isdistr_finP {R : realType} {I : finType} (mu : I -> R) :
  (isdistr mu) <-> (forall x, 0 <= mu x) /\ (\sum_j mu j <= 1).
Proof. split=> -[ ge0_mu le1]; split=> //.
+ by apply/le1; rewrite /index_enum -enumT enum_uniq.
+ move=> J uqJ; rewrite big_uniq 1?(le_trans _ le1) //=.
  by rewrite [X in _<=X](bigID (mem J)) /= lerDl sumr_ge0.
Qed.

Lemma le1_mu1
  {R : realType} {T : choiceType} (mu : {distr T / R}) x : mu x <= 1.
Proof.
case mu => //= {}mu [[?]].
rewrite summableE => ??.
rewrite -lee_fin.
apply/(@le_trans _ _ ((esum [set: T] (EFin \o mu))))=> //.
rewrite esum_ge1 //.
by move => ? _;rewrite lee_fin.
Qed.

(* -------------------------------------------------------------------- *)
Section DistrD.
Context {R : realType} {T : choiceType}.

Definition dnull := fun x : T => (0 : R).

Lemma isd_mnull : isdistr dnull.
Proof. by split=> // J _; rewrite big1 ?ler01. Qed.

HB.instance Definition _ := @mkdistrd R T dnull isd_mnull.

Lemma dnullE x : dnull x = 0.
Proof. by []. Qed.

End DistrD.

(* -------------------------------------------------------------------- *)
Lemma lef_dnull {R : realType} {T : choiceType} (mu : {distr T / R}) :
  dnull <=1 mu.
Proof. by move=> x; rewrite dnullE ge0_mu. Qed.

(* -------------------------------------------------------------------- *)
Section Restr.
Context (R : realType) (T : choiceType) (p : pred T).

Definition drestr (mu : {distr T / R}) :=
  fun x => if p x then mu x else 0.

Lemma isd_drestr (mu : {distr T / R}) : isdistr (drestr mu).
Proof.
split=> [x|J]; first by rewrite /drestr; case: ifP.
move=> eqJ; apply/(@le_trans _ _ (\sum_(j <- J) `|mu j|)).
+ apply/ler_sum=> i _; rewrite /drestr; case: ifPn=> _.
  by apply/ler_norm. by apply/normr_ge0.
+ rewrite -lee_fin.
  apply/(le_trans _ (le1_mu mu)).
  case mu => //= {}mu [[?]]; rewrite summableE => ? _.
  rewrite (@eq_esum _ _ _ _ (fun y : T => `|(EFin \o mu) y|%E)) //=.
   +  by move => ??; rewrite ger0_norm.
  exact: sum_esum_ge.
Qed.

HB.instance Definition _ (mu : {distr T / R}) :=
  @mkdistrd R T (drestr mu) (isd_drestr mu).

Lemma drestrE (mu : {distr T / R}) x :
  drestr mu x = if p x then mu x else 0.
Proof. by []. Qed.
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
- by rewrite /= drestrE; case: ifP=> // _ /dinsuppP ->.
- by case/andP; rewrite /= drestrE => /dinsuppP ? ->.
Qed.
End RestrTheory.

(* -------------------------------------------------------------------- *)
Section DRat.
Context {R : realType} (T : choiceType).

Local Notation distr := {distr T / R}.

Implicit Types (s : seq T).

Definition drat (s : seq T) : T -> R :=
  fun x : T => (count (pred1 x) s)%:R / (size s)%:R.

Lemma ge0_drat s : forall x, 0 <= drat s x.
Proof. by move=> x; rewrite mulr_ge0 ?invr_ge0 // ler0n. Qed.

Local Lemma has_sup_drat s J : uniq J -> \sum_(i <- J) drat s i <= 1.
Proof.
move=> uqJ; rewrite -mulr_suml /= -natr_sum; case: (size s =P 0%N).
  by move=> ->; rewrite invr0 mulr0 ler01.
move=> /eqP nz_s; rewrite ler_pdivrMr ?ltr0n ?lt0n // mul1r.
rewrite ler_nat (bigID (mem s)) /= [X in (_+X)%N]big1 ?addn0.
   by move=> i /count_memPn.
have ->: (size s = \sum_(i <- undup s) count_mem i s)%N.
  rewrite -sum1_size -big_undup_iterop_count; apply: eq_bigr => i _.
  by rewrite Monoid.iteropE iter_addn addn0 mul1n.
rewrite [X in (_<=X)%N](bigID (mem J)) /= -ltnS -addSn.
rewrite ltn_addr //= ltnS -big_filter -[X in (_<=X)%N]big_filter.
rewrite leq_eqVlt; apply/orP; left; apply/eqP/perm_big.
apply/uniq_perm; rewrite ?filter_uniq ?undup_uniq //.
by move=> x; rewrite !mem_filter mem_undup andbC.
Qed.

Local Lemma drat_sup s : (0 < size s)%N ->
  \sum_(i <- undup s) drat s i = 1.
Proof.
move=> gt0_s; rewrite -mulr_suml -natr_sum.
apply/(mulIf (x := (size s)%:R)); first by rewrite pnatr_eq0 -lt0n.
rewrite mul1r divfK ?pnatr_eq0 -?lt0n//; congr (_%:R).
rewrite -sum1_size -[in RHS]big_undup_iterop_count/=; apply: eq_bigr => i _.
by rewrite Monoid.iteropE iter_addn addn0 mul1n.
Qed.

Local Lemma summable_drat s: summable [set :T] (EFin \o (drat s)).
Proof.
rewrite /summable (@le_lt_trans _ _ 1%:E) ?ltey//.
rewrite ge0_esum // ge_ereal_sup//= => _ [X [finX _]] <-.
rewrite fsumEFin // lee_fin fsbig_finite //=.
rewrite (eq_bigr (drat s)).
+ move => ??; rewrite ger0_norm ?ge0_drat //.
by apply/has_sup_drat.
Qed.

Lemma isd_drat s : isdistr (drat s).
Proof. by split; [apply/ge0_drat | apply/has_sup_drat]. Qed.

HB.instance Definition _ (s : seq T) :=
  @mkdistrd R T (drat s) (isd_drat s).

Lemma drat1E s x :
  drat s x = (count_mem x s)%:R / (size s)%:R.
Proof. by []. Qed.

Definition dunit x := @locked {distr T / R} (drat [:: x] ).
Definition duni  s := @locked {distr T / R} (drat (undup s)).

Lemma dunit1E x y : (dunit x) y = (x == y)%:R.
Proof. by unlock dunit; rewrite /= drat1E /= !(simpm, invr1). Qed.

Lemma dunit_id x : (dunit x) x = 1.
Proof. by unlock dunit; rewrite /= drat1E /= !(simpm, invr1) eq_refl. Qed.

Lemma dunit_diff x y: x <> y -> (dunit x) y = 0.
Proof.
  unlock dunit; rewrite /= drat1E /= !(simpm, invr1).
  by case_eq (x == y) => //= /eqP.
Qed.

Lemma duni1E s x : (duni s) x = (x \in s)%:R / (size (undup s))%:R.
Proof. by unlock duni; rewrite /= drat1E count_uniq_mem ?(mem_undup, undup_uniq). Qed.

Lemma in_dunit t t' :
  t' \in dinsupp (dunit t) -> t' = t :> T.
Proof. by rewrite in_dinsupp /= dunit1E  pnatr_eq0 eqb0 negbK => /eqP. Qed.
End DRat.

(* -------------------------------------------------------------------- *)
Section Flip.
Context {R : realType}.

Definition dflip (xt : R) :=
  fun b => if b then clamp xt else 1 - clamp xt.

Lemma isd_dflip xt : isdistr (dflip xt).
Proof. apply/isdistr_finP; split=> [b|].
+ by case: b; rewrite ?subr_ge0 cp01_clamp.
+ by rewrite /index_enum !unlock /= addr0 addrC subrK.
Qed.

HB.instance Definition _ (xt : R) :=
  @mkdistrd R _ (dflip xt) (isd_dflip xt).

Lemma dflip1E xt : dflip xt =1 (fun b => if b then clamp xt else 1 - clamp xt).
Proof. by []. Qed.
End Flip.

(* -------------------------------------------------------------------- *)
Section Bind.
  Context {R : realType} {T U : choiceType}
          (f : T -> {distr U / R}) (mu : {distr T /R}).

Definition dlet := fun y : U => fine (esum [set:T] (fun x => EFin (mu x * f x y))).

Lemma dlet_pos x : 0 <= fine (\esum_(x0 in [set: T]) (mu x0 * f x0 x)%:E).
Proof.
rewrite /fine.
case h : (\esum_(i in [set: T]) _) => //=.
rewrite -lee_fin -{}h esum_ge0 // => ??.
by rewrite EFinM mule_ge0 //= lee_tofin.
Qed.

Lemma isd_dlet : isdistr dlet.
Proof.
split=> [x|J uqJ].
+ exact: dlet_pos.
+ rewrite /dlet -lee_fin.
  have hpos : (forall x i, 0 <= (mu x * f x i)%:E )%E.
  + by move => ?? ;rewrite EFinM mule_ge0  //= lee_tofin.
  apply /le_trans.
  + apply sum_esum_ge => // x.
    exact: dlet_pos.
  apply/(le_trans _ (le1_mu mu)).
  apply/(le_trans (le_esum_fine hpos)).
  rewrite exchange_esum // le_esum //  => i ?.
  under eq_esum do rewrite EFinM.
  rewrite esumZ // ?lee_tofin // => [? |]; rewrite ?lee_tofin //=.
  rewrite muleC gee_pMl // ?lee_tofin //;last first. exact : (le1_mu (f i)).
  rewrite (eq_esum _ _ (fun x  => `|(EFin \o f i) x|%E)) //.
  + by move => ??; rewrite gee0_abs //= lee_tofin.
  by have := (summable_mu (f i)); rewrite summableE.
Qed.

HB.instance Definition _ :=  @mkdistrd R U dlet isd_dlet.

Lemma dletE y : dlet y = fine (esum [set:T] (fun x => EFin (mu x * f x y))).
Proof. by []. Qed.
End Bind.

Notation "\dlet_ ( i <- d ) E" := (dlet (fun i => E) d).

Definition dlift {R : realType} {T : choiceType} (f : T -> {distr T / R}) :=
  fun d => \dlet_(x <- d) f x.

Definition diter {R : realType} {T : choiceType} n (f : T -> {distr T / R}) :=
  fun a => (iter n (dlift f) (dunit a)).

(* -------------------------------------------------------------------- *)
Lemma esum_abse {R : realType} {T : choiceType}
  (f : T -> R) :
  (forall i, 0%R <= f i) ->
    (\esum_(x in [set: T]) (f x)%:E = \esum_(x in [set: T]) `|(f x)%:E|)%E.
Proof. by move => ?; apply eq_esum => ?? ; rewrite gee0_abs // lee_tofin. Qed.

Lemma summable_mu_wgtd {R : realType} {T : choiceType}
  (f : T -> R) (mu : {distr T / R})  :
  (forall x, 0 <= f x <= 1) -> summable [set: T] (fun x => EFin (mu x * f x)).
Proof.
rewrite /summable => h.
under eq_esum do rewrite EFinM.
apply: summableMr => //.
+ exists 1%E; split => // => i.
  case /andP: (h i) => ?? ; rewrite lee_tofin // ger0_norm //.
exact : (summable_mu mu).
Qed.

(* -------------------------------------------------------------------- *)
Section BindTheory.
Variables (R : realType) (T U : choiceType).

Implicit Types (f g : T -> {distr U / R}) (mu nu : {distr T / R}).

Lemma dlet_null f : dlet f dnull =1 dnull.
Proof.
  move=> x; rewrite dletE esum1; last first.
  + by rewrite dnullE.
  by move => ? ?; rewrite /= dnullE /= EFinM mul0e.
Qed.

Lemma dlet_unit f v : \dlet_(y <- dunit v) f y =1 f v.
Proof.
move=> y; rewrite dletE.
rewrite  (esumID ([set v]%classic)).
+ by move => ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move => i [? h]; rewrite dunit_diff // ?mul0r //=.
  by apply nesym.
by rewrite dunit_id addr0 mul1r.
Qed.

Lemma dlet_dunit_id mu : \dlet_(t <- mu) (dunit t) =1 mu.
Proof.
move=> v; rewrite dletE.
rewrite  (esumID ([set v]%classic)).
+ by move => ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move => i [? h]; rewrite dunit_diff // ?mulr0 //=.
by rewrite dunit_id  mulr1 addr0.
Qed.

Lemma eq_in_dlet f g mu nu : {in dinsupp mu, f =2 g} -> mu =1 nu ->
  dlet f mu =1 dlet g nu.
Proof.
move=> eq_f eq_mu; unlock dlet=> y /=.
rewrite /dlet.
have -> //= : (\esum_(x in [set: T]) (mu x * f x y)%:E =
            \esum_(x in [set: T]) (nu x * g x y)%:E).
apply /eq_esum.
move => x ?.
rewrite -eq_mu !EFinM.
case /boolP: (x \in dinsupp mu) => [/eq_f ->//|].
by move/dinsuppPn => ->; rewrite !mul0e.
Qed.

Lemma summable_dlet (f : T -> {distr U / R}) (mu : {distr T / R}) y :
  summable [set: T] (fun x : T => EFin (mu x * (f x) y)).
Proof. by apply/summable_mu_wgtd=> x; rewrite ge0_mu le1_mu1. Qed.

Lemma fin_esum (f : T -> {distr U / R}) (mu : {distr T / R}) y:
  \esum_(x' in [set: T]) (mu x' * f x' y)%:E \is a fin_num.
Proof.
rewrite esum_abse.
+ by move => ?; rewrite mulr_ge0.
by  have := (summable_dlet f mu y); rewrite summableE.
Qed.

Lemma le_in_dlet f g mu : {in dinsupp mu, f <=2 g} ->
  dlet f mu <=1 dlet g mu.
Proof.
move=> le_f; unlock dlet=> y /=;  rewrite /dlet  fine_le // ?fin_esum //.
apply: le_esum => x ?.
case /boolP: (x \in dinsupp mu) => [/le_f ?|].
rewrite !EFinM lee_pmul //= lee_tofin //=.
by move/dinsuppPn => ->; rewrite !EFinM !mul0e.
Qed.

Lemma le_mu_dlet f mu nu : mu <=1 nu -> dlet f mu <=1 dlet f nu.
Proof.
move => le_mu y; unlock dlet; rewrite /dlet  fine_le //= ?fin_esum //.
apply: le_esum => x ?.
by rewrite !EFinM lee_pmul //= lee_tofin.
Qed.

Lemma le_dlet f g mu nu :
    mu <=1 nu
  -> {in dinsupp mu, forall x, f x <=1 g x}
  -> \dlet_(x <- mu) f x <=1 \dlet_(x <- nu) g x.
Proof.
move=> le_mu le_fg x.
by apply/(le_trans (le_in_dlet le_fg _))/le_mu_dlet.
Qed.

Lemma dletC (mu : {distr T / R}) (nu : {distr U / R}) y :
  (\dlet_(_ <- mu) nu) y = (dweight mu) * (nu y).
Proof.
rewrite dletE /pr //=.
under eq_esum do rewrite mulrC EFinM.
rewrite esumZ ?lee_tofin //= => [?| ]; rewrite ?lee_tofin //.
rewrite fineM => //=;last first.
+ rewrite mulrC. symmetry.
  by under eq_esum do rewrite mul1r.
by rewrite esum_abse //; have := (summable_mu mu); rewrite summableE.
Qed.

Lemma dinsupp_dlet f mu y :
  y \in dinsupp (\dlet_(x <- mu) f x) ->
    exists2 x, x \in dinsupp mu & f x y != 0.
Proof.
move/dinsuppP; rewrite /= dletE.
case h :(esum _) => //= hr.
have /neq0_esum [x he] : (\esum_(x in [set: T]) (mu x * f x y)%:E <> 0)%E.
+ by rewrite h  => h1; case : h1.
case /boolP: (x \in dinsupp mu) => [ ?|].
+ exists x => //=.
  rewrite -contra.Internals.eqType_neqP => h1.
  by apply he; rewrite EFinM h1 //= mule0.
+ move/dinsuppPn => hmu.
  by exfalso;apply he; rewrite EFinM hmu //= mul0e.
Qed.

Lemma fine_esum0 (f : T -> {distr U / R}) (mu : {distr T / R}) x y:
  fine (\esum_(x in [set: T]) (mu x * f x y)%:E) = 0 ->
  ((mu x * f x y)%:E = 0).
Proof.
move => h0.
apply /(@esum_eq0P _ _  [set: T] (fun i => (mu i * f i y)%:E)) => //.
+ by move=> i _; rewrite lee_fin mulr_ge0.
+ by rewrite -(fineK (fin_esum f mu y)) h0.
Qed.

Lemma dlet_dinsupp f mu x y :
  x \in dinsupp mu -> f x y != 0 -> y \in dinsupp (dlet f mu).
Proof.
move => /dinsuppP mux nz_fxy.
apply /dinsuppP; rewrite /= dletE => /(fine_esum0 x).
move=> /eqP; rewrite eqe mulf_eq0 (negbTE nz_fxy) orbF => /eqP.
exact: mux.
Qed.

Lemma dlet_eq0 (f : T -> U) mu y :
  {in dinsupp mu, forall x, f x != y} -> (\dlet_(x <- mu) dunit (f x)) y = 0.
Proof.
move=> h; rewrite dletE.
have -> : \esum_(x in [set: T]) (mu x * dunit (f x) y)%:E = 0.
+ apply: esum1 => x _.
  case/boolP: (x \in dinsupp mu) => [xin|/dinsuppPn ->].
  - by have := h _ xin; rewrite dunit1E => /negbTE ->; rewrite mulr0.
  - by rewrite mul0r.
by [].
Qed.

Lemma eq0_dlet (mu : {distr T / R}) (F : T -> {distr U / R}) y :
  (\dlet_(x <- mu) F x) y = 0 -> forall x, x \in dinsupp mu -> F x y = 0.
Proof.
unlock dlet; rewrite /= /dlet => /fine_esum0 => h x.
move => /dinsuppP /eqP mu_x. move: (h x).
by  move=> /eqP ; rewrite eqe mulf_eq0 (negbTE mu_x) /= => /eqP.
Qed.

End BindTheory.

(* -------------------------------------------------------------------- *)
Section DLetDLet.
  Context {R:realType} {T U V : choiceType}
          (f1 : T -> {distr U / R}) (f2 : U -> {distr V / R}).

Lemma dlet_dlet (mu : {distr T / R}) :
     \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x
  =1 \dlet_(y <- mu) (\dlet_(x <- f1 y) f2 x).
Proof.
move=> z; unlock dlet => /=; rewrite /dlet /=.
pose S y x := mu x * f1 x y * f2 y z.
rewrite (eq_esum _ _ (fun y => \esum_(x in [set: T]) (S y x)%:E)%E).
+ move => y ?; subst S; rewrite EFinM fineK ?fin_esum //.
  + rewrite muleC -esumZ // ?lee_tofin // => [? |].
    + by rewrite EFinM lee_tofin // mulr_ge0.
    + by apply eq_esum => ??; rewrite -EFinM mulrC.
rewrite (eq_esum _ _ (fun x => \esum_(y in [set: U]) (S y x)%:E)%E).
+ move => x ?; subst S; rewrite EFinM fineK ?fin_esum //.
  + rewrite -esumZ // ?lee_tofin // => [? |].
    + by rewrite EFinM lee_tofin // mulr_ge0.
    + by apply eq_esum => ??; rewrite -EFinM mulrA.
by rewrite exchange_esum // => ??; rewrite /S EFinM lee_tofin // !mulr_ge0.
Qed.
End DLetDLet.

(* -------------------------------------------------------------------- *)
Section DLetAlg.
Context {R : realType} {T U : choiceType} (mu mu1 mu2 : {distr T / R}).

Lemma dlet_additive (f : T -> {distr U / R}) z :
  (forall x, mu x = mu1 x + mu2 x) -> (\dlet_(x <- mu) f x) z =
    (\dlet_(x <- mu1) f x) z + (\dlet_(x <- mu2) f x) z.
Proof.
move=> muD; rewrite !dletE.
under eq_esum do rewrite muD mulrDl EFinD.
rewrite esumD.
1-2: by move => ??; rewrite /S EFinM lee_tofin // !mulr_ge0.
by rewrite fineD //= fin_esum .
Qed.
End DLetAlg.

(* -------------------------------------------------------------------- *)

HB.mixin Record isNDistribution
  (R : realType) (T : choiceType) (nmu : nat -> {distr T / R}) :=
  { nmu_decrease :  forall x, nondecreasing_seq (fun n => (nmu n x)%:E); }.

HB.structure Definition NDistribution (R : realType) (T : choiceType) :=
  {f of @isNDistribution R T f }.

Notation "{ 'ndistr' T / R }" := (@NDistribution.type R T)
  (at level 0, T at level 2, format "{ 'ndistr'  T  /  R }")
  : type_scope.


(* -------------------------------------------------------------------- *)
Lemma sup_range_lim {R : realType} (u : (\bar R)^nat) :
  nondecreasing_seq u -> ereal_sup (range u) = limn u.
Proof.
by move=> ndu; apply/esym/cvg_lim => //; exact: ereal_nondecreasing_cvgn.
Qed.

(* -------------------------------------------------------------------- *)
Section dlim.
Context {R : realType} (T : choiceType).

Lemma nd_f (f : {ndistr T / R}) : forall x, nondecreasing_seq (fun n => (f n x)%:E).
Proof. exact: nmu_decrease. Qed.

Lemma id1 (f : {ndistr T / R}): forall x, cvgn (fun n => (f n x)%:E).
Proof.
case f => {}f [[nd_f] ?].
by move=> x; apply: ereal_nondecreasing_is_cvgn; exact: nd_f.
Qed.

(* Definition dlim  (f : {ndistr T / R}) : T -> R := *)
(*   fun x => fine (ereal_sup (range (fun n : nat => (f n x)%:E))). *)

Import numFieldNormedType.Exports.

Definition dlim  (f : {ndistr T / R}) : T -> R :=
  fun x => fine (limn (fun n : nat => (f n x)%:E)).

Lemma le1_lim (f : {ndistr T / R}) :
  forall x, (limn (fun n => (f n x)%:E) <= 1%:E)%E.
Proof.
  move=> x; apply: lime_le; [ exact: id1| apply: nearW].
  move=> n; rewrite lee_fin.
  exact: le1_mu1.
Qed.

Lemma fin_lim (f : {ndistr T / R}) :
  forall x, limn (fun n => (f n x)%:E) \is a fin_num.
Proof.
  move=> x; rewrite ge0_fin_numE //.
  + by apply: lime_ge; [exact: id1 | apply: nearW => n; rewrite lee_fin].
  apply: le_lt_trans;[ apply le1_lim | apply ltry].
Qed.

Lemma sumlim (f : {ndistr T / R}):
  forall L, uniq L ->
       (\sum_(j <- L) limn (fun n => (f n j)%:E) =
       limn (fun n => \sum_(j <- L) (f n j)%:E))%E.
Proof.
elim => [|a L IH] uqL.
- rewrite big_nil.
  apply/esym/cvg_lim => //.
  by apply: cvg_near_cst; apply: nearW => n; rewrite big_nil.
- case/andP: uqL => _ uqL.
  rewrite big_cons IH //.
  under [in RHS]eq_fun => n do rewrite big_cons.
  apply/esym/cvg_lim => //.
  apply: cvgeD.
  + apply: fin_num_adde_defr; exact: fin_lim.
  + exact: id1.
  + apply: ereal_nondecreasing_is_cvgn => n m nm.
    by apply: lee_sum => j _; exact : nd_f.
Qed.

Lemma dlim_EFin (f : {ndistr T / R}):
  forall x, (dlim f x)%:E = limn (fun n => (f n x)%:E).
Proof.
move=> x; rewrite /dlim fineK //.
exact: fin_lim.
Qed.

Lemma isd_dlim (f : {ndistr T / R}):  isdistr (dlim f).
Proof.
split=> [x|J uqJ]; rewrite /dlim.
+ case h: (limn _) => //=.
  rewrite -lee_fin -{}h.
  apply: lime_ge; first exact: id1.
  apply: nearW => n.
  by rewrite lee_fin.
+ rewrite -lee_fin -sumEFin.
  under eq_bigr => j _ do rewrite -/(dlim f j) dlim_EFin //.
  rewrite sumlim //.
  apply: lime_le.
  + apply: ereal_nondecreasing_is_cvgn => n m nm.
    by apply: lee_sum => j _ ; exact: nd_f.
  + apply: nearW => n; rewrite sumEFin.
    apply: (@le_trans _ _ (esum [set: T] (EFin \o f n))); last exact: le1_mu.
    exact: sum_esum_ge.
Qed.

HB.instance Definition _ (f : {ndistr T / R}) :=  @mkdistrd R T (dlim f) (isd_dlim f).

Lemma dlimE (f : {ndistr T / R}) x :
  (dlim f) x =  fine (limn (fun n => EFin(f n x))).
Proof. by []. Qed.

End dlim.

Lemma mono_nondecressing {R : realType} (T : choiceType) (f : nat -> T -> R)
  (hmono : forall n m, (n <= m)%N -> forall x, f n x <= f m x) :
  forall x, nondecreasing_seq (fun n => (f n x)%:E).
Proof. by move=> x n m nm; rewrite lee_fin; exact: hmono. Qed.

Notation "\dlim_ ( n ) E" := (dlim (fun n => E)).
(* -------------------------------------------------------------------- *)

Section DLimC.
Variables (R : realType) (T U : choiceType).

Implicit Types (mu : {distr T / R}).

Definition nmuc mu := fun (_:nat) => mu.

Lemma isnd_ndc mu : forall x, nondecreasing_seq (fun n => (nmuc mu n x)%:E).
Proof.
by apply: mono_nondecressing.
Qed.

HB.instance Definition _ mu:= @isNDistribution.Build R T (nmuc mu) (isnd_ndc mu).

Lemma dlimC mu : forall x, (dlim (nmuc mu)) x = mu x.
Proof.
move=> x; rewrite dlimE /= /nmuc.
have -> : limn (fun n : nat => (mu x)%:E) = (mu x)%:E.
  by apply/cvg_lim => //; exact: cvg_cst.
by [].
Qed.

End  DLimC.

Section DLimBump.
Variables (R : realType) (T U : choiceType).

Definition bump (nmu :{ndistr T / R}) := fun n => nmu (n.+1).

Lemma isnd_bump nmu : forall x, nondecreasing_seq (fun n => (bump nmu n x)%:E).
Proof.
apply: mono_nondecressing.
rewrite /bump => n m h x.
by apply: nmu_decrease.
Qed.

HB.instance Definition _ nmu :=
  @isNDistribution.Build R T (bump nmu) (isnd_bump nmu).

Lemma dlim_bump (nmu: {ndistr T / R}) : dlim (bump nmu) =1 dlim nmu.
Proof.
move=> x; rewrite /dlim /=.
congr (fine _).
apply/cvg_lim => //.
rewrite (cvg_shiftS (fun k => (nmu k x)%:E)).
exact: id1.
Qed.

End DLimBump.

Section DLimLift.

Variables (R : realType) (T U : choiceType).

Definition lift (nmu : {ndistr T / R}) p := fun n => nmu (n + p).

Lemma isnd_lift nmu p : forall x, nondecreasing_seq (fun n => (lift nmu p n x)%:E).
Proof.
apply: mono_nondecressing.
rewrite /lift => n m h x.
apply: nmu_decrease.
by rewrite leq_add2r.
Qed.

HB.instance Definition _ nmu p :=
  @isNDistribution.Build R T (lift nmu p ) (isnd_lift nmu p).

Lemma dlim_lift (nmu : {ndistr T / R}) p :
  dlim (lift nmu p) =1 dlim nmu.
Proof.
move=> x; rewrite /dlim /=.
congr (fine _).
apply/cvg_lim => //.
rewrite (cvg_shiftn p (fun k => (nmu k x)%:E)).
exact: id1.
Qed.

End DLimLift.

Section DLimTheory.
Variables (R : realType) (T U : choiceType).

Implicit Types (f g : {ndistr T / R}) (h : T -> {distr U / R}).
Implicit Types (mu : {distr T / R}).

Lemma ge0_dlim f : forall x, 0 <= dlim f x.
Proof. exact: mu_positive. Qed.

Lemma le1_dlim f : forall x, dlim f x <= 1.
Proof.
move => x; rewrite /= dlimE -lee_fin dlim_EFin.
exact: le1_lim.
Qed.

Lemma le_dlim f g :
  (forall n, f n <=1 g n) -> dlim f <=1 dlim g.
Proof.
move=> le x; rewrite -lee_fin !dlim_EFin.
apply: lee_lim; [exact: id1 | exact: id1 |].
by apply: nearW => n; rewrite lee_fin; apply: le.
Qed.

Lemma eq_dlim f g :  (forall n, f n =1 g n) -> dlim f =1 dlim g.
Proof.
move=> eq_fg x.
apply/eqP; rewrite eq_le; apply/andP; split.
1-2 : by apply le_dlim; move => ??; rewrite eq_fg.
Qed.

Lemma leub_dlim f mu : (forall n, f n <=1 mu) -> dlim f <=1 mu.
Proof.
  move => le x; rewrite -(dlimC mu x).
  by apply : le_dlim => n y.
Qed.

Lemma dlim_ub f k : f k <=1 dlim f.
Proof.
move=> x; rewrite -lee_fin dlim_EFin.
apply: lime_ge; first exact: id1.
near=> n; apply: (nd_f f x).
by near: n; apply: nbhs_infty_ge.
Unshelve. all: by end_near.
Qed.

End DLimTheory.

Section DletDLim.
Variables (R : realType) (T U : choiceType).

Implicit Types (f : {ndistr T / R}) (h : T -> {distr U / R}).

Definition ndlet f h: (nat -> {distr U / R}) := fun n => dlet h (f n).

Lemma isnd_dlet h f : forall x, nondecreasing_seq (fun n => (ndlet f h n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
apply: le_mu_dlet => y.
by apply nd_f.
Qed.

HB.instance Definition _ h f :=
  @isNDistribution.Build R U (ndlet f h) (isnd_dlet h f).

Lemma dlet_EFin h (mu : {distr T / R}) y :
  (dlet h mu y)%:E = esum [set:T] (fun x => (mu x * h x y)%:E).
Proof. by rewrite dletE fineK// ?fin_esum. Qed.

Lemma sup_mul (nf : {ndistr T / R}) (c : R) x : 0 <= c ->
  ((dlim nf x) * c)%:E = ereal_sup (range (fun n => (nf n x * c)%:E)).
Proof.
move=> c0.
rewrite EFinM dlim_EFin -(sup_range_lim (nd_f nf x)) muleC.
rewrite (@ge0_ereal_supZl_range R T (fun t n => (nf n t)%:E)) //=.
+ by move=> t n; rewrite lee_fin; exact: ge0_mu.
have -> :
  [set (c%:E * (nf i x)%:E)%E | i in [set: nat]]%classic =
    [set (nf i x * c)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  - by move=> ? [x0 ?]; rewrite -EFinM mulrC=> <- //=; exists x0.
  - by move=> ? [x0 ?]; rewrite mulrC EFinM => <- //=; exists x0.
reflexivity.
Qed.

Lemma dlet_lim f h : dlet h (dlim f) =1 dlim (ndlet f h).
Proof.
move=> y; apply: EFin_inj.
rewrite dlet_EFin dlim_EFin.
under eq_esum => x _ do rewrite sup_mul//.
rewrite -(sup_range_lim (nd_f (ndlet f h) y)).
rewrite (@exchange_esum_ereal_sup R T (fun x n => (f n x * h x y)%:E)) /=.
+ by move=> t n; rewrite lee_fin; apply: mulr_ge0; exact: ge0_mu.
+ move=> n m nm t; rewrite lee_fin; apply: ler_wpM2r; first exact: ge0_mu.
  by rewrite -lee_fin; apply: nd_f.
have -> :
[set \esum_(x in [set: T]) (f i x * h x y)%:E | i in [set: nat]]%classic =
[set ((\dlet_(i <- f i) h i) y)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  - by move=> ? [x0 ?]; rewrite -dlet_EFin => <- //=; exists x0.
  - by move=> ? [x0 ?]; rewrite /ndlet dlet_EFin => <- //=; exists x0.
reflexivity.
Qed.

End DletDLim.

Section DLimDlet.
Context (R : realType) (T U : choiceType) (f : nat -> T -> {distr U / R}).
Context (hmono: forall x n m, (n <= m)%N -> f n x <=1 f m x).

Definition reduce y : (nat -> {distr U / R}) := fun n => f n y.

Lemma isnd_reduce y :
  forall x, nondecreasing_seq (fun n => (reduce y n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
exact: hmono.
Qed.

HB.instance Definition _ y :=
  @isNDistribution.Build R U (reduce y)  (isnd_reduce y ).

Definition mu_dlet mu: (nat -> {distr U / R}) := fun n => dlet (f n) mu.

Lemma isnd_mu_dlet (mu : {distr T / R}) :
  forall x, nondecreasing_seq (fun n => (mu_dlet mu n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
apply: le_in_dlet => z _.
exact: hmono.
Qed.

HB.instance Definition _ mu :=
  @isNDistribution.Build R U (mu_dlet mu) (isnd_mu_dlet mu).

Lemma dlim_let (mu : {distr T / R}) :
  dlim (mu_dlet mu) =1 dlet (fun x => dlim (reduce x )) mu.
Proof.
move=> z; apply: EFin_inj.
rewrite dlim_EFin dlet_EFin.
under eq_esum => t _ do rewrite mulrC sup_mul//.
rewrite -(sup_range_lim (nd_f (mu_dlet mu) z)).
rewrite (@exchange_esum_ereal_sup R T (fun t n => (reduce t n z * mu t)%:E)) /=.
+ by move=> t n; rewrite /reduce lee_fin; apply: mulr_ge0; exact: ge0_mu.
+ move=> n m nm t; rewrite /reduce lee_fin; apply: ler_wpM2r; first exact: ge0_mu.
  exact: hmono.
have ->:
  [set ((\dlet_(i0 <- mu) f i i0) z)%:E | i in [set: nat]]%classic =
  [set \esum_(x in [set: T]) (reduce x i z * mu x)%:E | i in [set: nat]]%classic.
  apply/seteqP; split.
  -  move=> ? [x0 ?]; rewrite dlet_EFin=> <-//=; exists x0 => //=.
     by under eq_esum do rewrite  /reduce mulrC.
  - move=> ? [x0 ?]; under eq_esum do rewrite  /reduce mulrC.
    by move => <- //=; exists x0 => //=; rewrite -dlet_EFin.
reflexivity.
Qed.

End DLimDlet.

Section DLimDLim.
Context (R : realType) (T : choiceType) (f : nat -> nat -> {distr T / R}).
Context (hmono1: (forall k n1 n2, (n1 <= n2)%N -> f n1 k <=1 f n2 k)).
Context (hmono2: (forall k n1 n2, (n1 <= n2)%N -> f k n1 <=1 f k n2)).

Definition apply2 : (nat -> {distr T / R}) := (fun n => f n n).

Lemma isnd_apply2:
  forall x, nondecreasing_seq (fun n => (apply2 n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
rewrite /apply2.
apply /le_trans.
+ apply hmono1.  exact: hnm.
by apply: hmono2.
Qed.

HB.instance Definition _ :=
  @isNDistribution.Build R T apply2 isnd_apply2.

Definition apply (k:nat) : (nat -> {distr T / R}) := f k.

Lemma isnd_apply k:
  forall x, nondecreasing_seq (fun n => (apply k n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
by apply: hmono2.
Qed.

HB.instance Definition _ k :=
  @isNDistribution.Build R T (apply k) (isnd_apply k).

Definition dlim_apply : (nat -> {distr T / R}) := (fun n => dlim (apply n)).

Lemma isnd_dlim_apply:
  forall x, nondecreasing_seq (fun n => (dlim_apply n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
apply le_dlim => ??.
by apply: hmono1.
Qed.

HB.instance Definition _ :=
  @isNDistribution.Build R T dlim_apply isnd_dlim_apply.

Lemma leub_dlim_dlim1 :
  dlim dlim_apply <=1 dlim apply2.
Proof.
apply: leub_dlim => n.
apply: leub_dlim => m x.
apply: (@le_trans _ _ (apply2 (maxn n m) x)); last exact: dlim_ub.
apply: (@le_trans _ _ (f (maxn n m) m x)).
- apply: hmono1; exact: leq_maxl.
- apply: hmono2; exact: leq_maxr.
Qed.

Lemma dlim_dlim_ub1 :
  dlim apply2 <=1 dlim dlim_apply.
Proof.
apply: leub_dlim => n x.
apply: (@le_trans _ _ (dlim (apply n) x)).
- exact: (dlim_ub (apply n) n).
- exact: (dlim_ub dlim_apply n).
Qed.

Definition applyk (k:nat) : (nat -> {distr T / R}) := (fun n => f n k).

Lemma isnd_applyk k:
  forall x, nondecreasing_seq (fun n => (applyk k n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
by apply: hmono1.
Qed.

HB.instance Definition _ k :=
  @isNDistribution.Build R T (applyk k) (isnd_applyk k).

Definition dlim_applyk : (nat -> {distr T / R}) := (fun n => dlim (applyk n)).

Lemma isnd_dlim_applyk:
  forall x, nondecreasing_seq (fun n => (dlim_applyk n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
apply le_dlim => ??.
by apply: hmono2.
Qed.

HB.instance Definition _ :=
  @isNDistribution.Build R T dlim_applyk isnd_dlim_applyk.

Lemma leub_dlim_dlim2 :
  dlim dlim_applyk <=1 dlim apply2.
Proof.
apply: leub_dlim => n.
apply: leub_dlim => m x.
apply: (@le_trans _ _ (apply2 (maxn n m) x)); last exact: dlim_ub.
apply: (@le_trans _ _ (f (maxn n m) n x)).
- apply: hmono1; exact: leq_maxr.
- apply: hmono2; exact: leq_maxl.
Qed.

Lemma dlim_dlim_ub2 :
  dlim apply2 <=1 dlim dlim_applyk.
Proof.
apply: leub_dlim => n x.
apply: (@le_trans _ _ (dlim (applyk n) x)).
- exact: (dlim_ub (applyk n) n).
- exact: (dlim_ub dlim_applyk n).
Qed.

Lemma dlim_dlim_com :
  dlim dlim_apply =1 dlim dlim_applyk.
Proof.
move=> x; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (le_trans (leub_dlim_dlim1 x) (dlim_dlim_ub2 x)).
- exact: (le_trans (leub_dlim_dlim2 x) (dlim_dlim_ub1 x)).
Qed.

End DLimDLim.

Section dlet_dlim_diag.
Context (R : realType) (T U: choiceType).
Context (d : {ndistr T / R}) (h : nat -> T -> {distr U / R}).
Context (hmono: (forall k n1 n2, (n1 <= n2)%N -> h n1 k <=1 h n2 k)).

Definition nmu_dlet (nmu : {ndistr T / R}): (nat -> {distr U / R}) :=
  fun n => dlet (h n) (nmu n).

Lemma isnd_nmu_dlet (nmu : {ndistr T / R}) :
  forall x, nondecreasing_seq (fun n => (nmu_dlet nmu n x)%:E).
Proof.
apply: mono_nondecressing => n m hnm x.
rewrite /= /nmu_dlet.
apply: le_dlet.
+ move => ?.
  by apply: nmu_decrease.
move => ???; exact: hmono.
Qed.

HB.instance Definition _ nmu :=
  @isNDistribution.Build R U (nmu_dlet nmu) (isnd_nmu_dlet nmu).

Let hreduce := (reduce h).

HB.instance Definition _ y :=
  @isNDistribution.Build R U (hreduce y) (isnd_reduce hmono y).

Lemma key : forall n, dlet (fun x => dlim (hreduce x)) (d n) <=1 dlim (nmu_dlet d).
Proof.
move=> n u; rewrite -dlim_let.
apply: leub_dlim => m w; rewrite /mu_dlet.
apply: (@le_trans _ _ (nmu_dlet d (maxn m n) w)); last exact: dlim_ub.
rewrite /nmu_dlet; apply: le_dlet.
+ move=> x; rewrite -lee_fin; apply: (nd_f d x).
  exact: leq_maxr.
by move=> ? _; apply: hmono; exact: leq_maxl.
Qed.

Lemma dlet_dlim_diag :
  dlet (fun x => dlim (hreduce x)) (dlim d) =1 dlim (nmu_dlet d).
Proof.
move=> z; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite dlet_lim; apply: leub_dlim => n.
  rewrite /ndlet; exact: key.
- apply: leub_dlim => n; rewrite /nmu_dlet; apply: le_dlet.
  + exact: dlim_ub.
  by move=> x _; exact: (dlim_ub (hreduce x) n).
Qed.

End dlet_dlim_diag.

(* -------------------------------------------------------------------- *)
Section Marginals.
Variable (R : realType) (T U : choiceType) (h : T -> U) (mu : {distr T / R}).

Definition dmargin := \dlet_(x <- mu) (dunit (h x)).

Lemma dmarginE : dmargin = \dlet_(y <- mu) (dunit (h y)).
Proof. by []. Qed.
End Marginals.

(* -------------------------------------------------------------------- *)
Section MarginalsTh.
Variable (R: realType) (T U V : choiceType).

Lemma dmargin_psumE (mu : {distr T / R}) (f : T -> U) y :
  (dmargin f mu) y = fine (esum [set:T] (fun x => ((f x == y)%:R * mu x)%:E)).
Proof.
rewrite dmarginE dletE.
congr fine.
apply/eq_esum => x _.
by rewrite mulrC dunit1E.
Qed.

Lemma dlet_dmargin (mu : {distr T / R}) (f : T -> U) (g : U -> {distr V / R}):
  \dlet_(u <- dmargin f mu) g u =1 \dlet_(t <- mu) (g (f t)).
Proof.
move=> x; rewrite dlet_dlet; apply: eq_in_dlet=> //.
by move=> y _ z /=; rewrite dlet_unit.
Qed.

Lemma dmargin_dlet (mu : {distr T / R}) (f : U -> V) (g : T -> {distr U / R}):
  dmargin f (\dlet_(t <- mu) g t) =1 \dlet_(t <- mu) (dmargin f (g t)).
Proof. by apply/dlet_dlet. Qed.

Lemma dmargin_dunit (t : T) (f : T -> U):
  dmargin f (dunit t) =1 dunit (f t) :> {distr U / R}.
Proof. by apply/dlet_unit. Qed.
End MarginalsTh.

Notation dfst mu := (dmargin fst mu).
Notation dsnd mu := (dmargin snd mu).

(* -------------------------------------------------------------------- *)
Section DSwap.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B)%type / R}).

Definition dswap : {distr (B * A)%type / R} :=
  dmargin (fun xy => (xy.2, xy.1)) mu.
End DSwap.

(* -------------------------------------------------------------------- *)
Section DSwapCoreTheory.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B)%type / R}).

Lemma dswapE xy : dswap mu xy = mu (xy.2, xy.1).
Proof.
rewrite /= dletE (esumID ([set (xy.2, xy.1)]%classic)).
+ by move=> ??; rewrite lee_tofin // mulr_ge0.
rewrite setI1 //= in_setT esum_set1.
rewrite esum1 //=.
+ move=> ab [_ h] /=.
  rewrite dunit_diff ?mulr0 // => heq; apply: h.
  by rewrite -heq /= -surjective_pairing.
by case: xy => x y /=; rewrite dunit_id mulr1 addr0.
Qed.

End DSwapCoreTheory.

(* -------------------------------------------------------------------- *)
Section DSwapTheory.
Context {R : realType} {A B : choiceType} (mu : {distr (A * B)%type / R}).

Lemma dswapK : dswap (dswap mu) =1 mu.
Proof. by case=> x y; rewrite !dswapE. Qed.

Lemma dinsupp_swap xy : (xy.2, xy.1) \in dinsupp mu ->
  xy \in dinsupp (dswap mu).
Proof.
by move=> h; apply/dinsuppP; rewrite dswapE; apply/dinsuppPn.
Qed.

Lemma dfst_dswap : dfst (dswap mu) =1 dsnd mu.
Proof.
move=> z; rewrite /dmargin dlet_dlet => /= .
apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.

Lemma dsnd_dswap : dsnd (dswap mu) =1 dfst mu.
Proof.
move=> z; rewrite /dmargin dlet_dlet; apply/eq_in_dlet => // -[x y].
by move=> _ t /=; rewrite dlet_unit /=.
Qed.
End DSwapTheory.

(* -------------------------------------------------------------------- *)
Section DFst.
Context {R : realType} {T U : choiceType}.

Lemma dfstE (mu : {distr (T * U)%type /  R}) x :
  dfst mu x = fine (esum [set:U] (fun y => (mu (x, y))%:E)).
Proof.
rewrite dmarginE dletE; congr fine.
rewrite (esumID [set z : T * U | z.1 = x]).
+ by move=> z _; rewrite lee_tofin // mulr_ge0.
rewrite [X in _ + X]esum1.
+ by move=> z [_ /= zx]; rewrite dunit_diff // ?mulr0 //=.
rewrite adde0.
rewrite (reindex_esum [set: U] _ (fun y => (x, y))).
  split.
  - by move=> y _; split.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z [_ /= zx]; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
by apply: eq_esum => y _ /=; rewrite dunit_id mulr1.
Qed.

Lemma summable_fst (mu : {distr (T * U)%type / R}) x :
  summable [set:U] (fun y => (mu (x, y))%:E).
Proof.
rewrite /summable; apply: le_lt_trans (summable_mu mu).
rewrite -(reindex_esum [set:U] [set z : T * U | z.1 = x]
  (fun y => (x, y)) (fun z => (`|(mu z)%:E|)%E)).
+ split.
  - by move=> y _.
  - by move=> y1 y2 _ _ /(congr1 snd).
  - move=> z /= zx; exists z.2 => //=.
    by case: z zx => z1 z2 /= ->.
by apply: subset_esum.
Qed.
End DFst.

(* -------------------------------------------------------------------- *)
Section DSnd.
Context {R : realType} {T U : choiceType}.

Lemma dsndE (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = fine (esum [set:T] (fun x => (mu (x, y))%:E)).
Proof.
  by rewrite -dfst_dswap dfstE; congr fine; apply/eq_esum=> x; rewrite dswapE.
Qed.

Lemma summable_snd (mu : {distr (T * U)%type / R}) y :
  summable [set:T] (fun x => (mu (x, y))%:E).
Proof.
have := summable_fst (dswap mu) y; apply/eq_summable.
by move=> x /=; rewrite dswapE.
Qed.
End DSnd.

(* -------------------------------------------------------------------- *)
Section PrCoreTheory.
Context {R : realType} {T : choiceType}.

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma summable_pr E mu : summable [set:T] (fun x => ((E x)%:R * mu x)%:E).
Proof.
apply/(le_summable (g := EFin \o mu)) => [x|]; last by apply/summable_mu.
rewrite !lee_tofin => //=.
+ by rewrite mulr_ge0.
by rewrite ler_piMl //= lern1 leq_b1.
Qed.

Lemma pr_pred0 mu : \P_[mu] pred0 = 0.
Proof. by rewrite /pr esum1 // => x /=; rewrite mul0r. Qed.

Lemma pr_pred1 mu x : mu x = \P_[mu] (pred1 x).
Proof.
rewrite /pr.
rewrite (eq_esum _ _ (fun y => if x == y then (mu y)%:E else 0)); last first.
+ by rewrite esum_unit.
move=> y _ /=; rewrite [y == x]eq_sym.
by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
Qed.

(* -------------------------------------------------------------------- *)
Lemma pr_exp mu (E : pred T) : \P_[mu] E = \E_[mu] (fun m => (E m)%:R).
Proof.  by []. Qed.

Lemma pr_predT mu : \P_[mu] predT = fine (esum [set: T] (EFin \o mu)).
Proof.
rewrite /pr /esp; congr fine.
by apply/eq_esum=> x; rewrite mul1r.
Qed.

Lemma pr_dunit E x : \P_[dunit x] E = (E x)%:R :> R.
Proof.
rewrite /pr.
rewrite (eq_esum _ _ (fun y => if x == y then ((E y)%:R)%:E else 0)).
+ move=> y _ /=; rewrite dunit1E.
  by case: ifP => xy; rewrite ?xy /= ?mulr1 ?mulr0.
by rewrite esum_unit.
Qed.

Lemma exp_dunit (f : T -> R) (x : T) : \E_[dunit x] f = f x.
Proof.
rewrite /esp.
rewrite (eq_esum _ _ (fun y : T => if x == y then (f y)%:E else 0)%E).
+ move => x0 /=; rewrite dunit1E.
  by case (x == x0) => //=; rewrite ?mulr1  ?mulr0.
by rewrite esum_unit.
Qed.

Lemma fineMK (a b : \bar R):
  (0 <= b)%E -> a \is a fin_num ->
  fine (a * b) = fine a * fine b.
Proof.
move => hp.
move /(elimT (EFin_fin_numP a)) => [r] ->.
case h: b => //=; last first. by move : hp; rewrite h.
have [hc|hc|->] := comparable_ltgtP (comparableT r 0).
+ rewrite lt0_muley => //=.
  by rewrite mulr0.
+ rewrite  gt0_muley => //=.
  by rewrite mulr0.
by rewrite mul0e //= mulr0.
Qed.

Lemma expZ mu f c :
  (forall x, 0 <= f x) ->  \E_[mu] (fun x => c * (f x)) = c * (\E_[mu] f).
Proof.
move => h1; rewrite /esp.
under eq_esum => x do rewrite /= -mulrA EFinM.
have hpos :  forall x : T, (0%R <= (f x * mu x)%:E)%E.
+ by move=> x; rewrite lee_fin; apply: mulr_ge0; [exact: h1 | exact: ge0_mu].
rewrite esumZ //=.
have hsum : (0 <= \esum_(i in [set: T]) (f i * mu i)%:E)%E.
+ by apply esum_ge0 => ??.
by rewrite fineMK.
Qed.

Lemma exp_cst mu r : \E_[mu] (fun _ => r) = \P_[mu] predT * r.
Proof.
have := (expZ mu (f:= fun _ => 1%R) r).
rewrite mulr1 => -> //=.
by rewrite mulrC;  congr (_ * _).
Qed.

Lemma exp0 mu : \E_[mu] (fun _ => 0) = 0.
Proof. by rewrite exp_cst mulr0. Qed.

Lemma has_expC mu c : \E?_[mu] (fun _ => c).
Proof.
rewrite /has_esp.
have : summable [set: T] (fun x : T => (c%:E * (mu x)%:E)%E).
  by apply: summableZ => //; exact: summable_mu.
apply/eq_summable => x /=.
by rewrite EFinM.
Qed.

Lemma has_exp0 mu : \E?_[mu] (fun _ => 0).
Proof. by apply/(has_expC mu 0). Qed.

Lemma has_exp1 mu : \E?_[mu] (fun _ => 1).
Proof. by apply/(has_expC mu 1). Qed.

Lemma has_expZ mu c F : \E?_[mu] F -> \E?_[mu] (c \*o F).
Proof.
move=> heF; rewrite /has_esp.
have := summableZ (f := EFin \o (fun x => F x * mu x)) (c := c%:E) erefl heF.
apply/eq_summable => x /=.
by rewrite -EFinM mulrA.
Qed.

Lemma ge0_pr A mu : 0 <= \P_[mu] A.
Proof.
rewrite /pr.
case h: (esum _ _) => //=.
rewrite -lee_fin -h.
apply/esum_ge0 .
by move => ? _ ; rewrite lee_fin mulr_ge0.
Qed.

Lemma ge0_prc A B mu : 0 <= \P_[mu, B] A.
Proof. by rewrite /prc mulr_ge0 ?invr_ge0 // ge0_pr. Qed.

Lemma eq_in_pr A B mu :
  {in dinsupp mu, A =i B} -> \P_[mu] A = \P_[mu] B.
Proof.
move=> eq_AB; rewrite /pr; congr fine.
apply/eq_esum => x _ /=.
case/boolP: (x \in dinsupp mu).
+ by move/eq_AB; rewrite -!topredE => /= ->.
+ by move/dinsuppPn => ->; rewrite !mulr0.
Qed.

Lemma eq_pr A B mu : A =i B -> \P_[mu] A = \P_[mu] B.
Proof. by move=> eq_AB; apply/eq_in_pr=> x _; apply/eq_AB. Qed.

Lemma eq_exp mu (f1 f2 : T -> R):
   {in dinsupp mu, f1 =1 f2} -> \E_[mu] f1 = \E_[mu] f2.
Proof.
move=> eq_f; rewrite /esp; congr fine.
apply/eq_esum => x /=.
case/boolP: (x \in dinsupp mu).
+ by move/eq_f => ->.
+ by move/dinsuppPn => ->; rewrite !mulr0.
Qed.

Lemma pr_pred0_eq (mu : {distr T / R}) (E : pred T) :
  E =1 pred0 -> \P_[mu] E = 0.
Proof. by move=> eq; rewrite -(pr_pred0 mu); apply/eq_pr. Qed.
End PrCoreTheory.

(* -------------------------------------------------------------------- *)
Section Esp.
Context {R : realType} {T : choiceType}.

Implicit Types (mu : {distr T / R}) (f : T -> \bar R).

Definition espe  mu f := esum [set:T] (fun x => mule (f x) ((mu x)%:E)).

Notation "\Ee_[ mu ] f" := (espe mu f).
End Esp.

Section EspeCoreTheory.
Context {R : realType} {T : choiceType}.

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma eexp_eq (f g: T -> \bar R) mu:
  (f =1 g)%E ->
  espe mu f = espe mu g.
Proof.
move => h; rewrite /espe.
apply eq_esum => ??.
by congr (_ * _)%E.
Qed.

Lemma eexp_dunit (f : T -> \bar R) (x : T) :
  espe (dunit x) f = f x.
Proof.
rewrite /espe.
rewrite (eq_esum _ _ (fun y : T => if x == y then f y else 0%R)%E).
+ move => x0. rewrite dunit1E.
  by case (x == x0) => //=; rewrite ?mule1 ?mule0.
by rewrite esum_unit.
Qed.

Lemma eexp_cst mu r : (espe mu (fun _ => r) = (\P_[mu] predT)%:E * r)%E.
Proof.
rewrite pr_predT /espe //.
rewrite esumZ.
- move => ?; rewrite lee_fin //.
rewrite muleC;  congr ( _ * _)%E.
rewrite fineK //= esum_abse => //=.
by have := (summable_mu mu); rewrite summableE.
Qed.

Lemma eexp0 mu : espe mu (fun _ => 0) = 0.
Proof. by rewrite eexp_cst mule0. Qed.

Lemma eexp_dlet {U: choiceType} mu (nu : T -> {distr U / R}) F :
(forall x, 0%:E <= F x)%E ->
espe (dlet nu mu) F = espe mu (fun x => espe (nu x) F).
Proof.
move => HF.
have pos : (forall (i : T) (j : U), (0%R <= F j * ((mu i)%:E * (nu i j)%:E))%E).
- move => i j; rewrite mule_ge0 //.
  by rewrite mule_ge0 // lee_tofin.
rewrite /espe {1}(eq_esum _ _
    (fun x : U => (F x * esum [set:T] (fun y : T => (mu y * nu y x)%:E)))%E).
- move => x ?; rewrite /= dletE.
  congr ( _ * _)%E.
  rewrite fineK //= esum_abse => //=.
  - by move => i; rewrite mulr_ge0.
  - have : summable [set: T] (fun x0 : T => ((mu x0 * nu x0 x)%:E))%E.
    +  apply/(le_summable (g := EFin \o mu)) => //=.
       by move => x0; rewrite !lee_fin //=  mulr_ge0 //= ler_piMr //= le1_mu1.
    by rewrite summableE.
symmetry.
rewrite {1}(eq_esum _ _
    (fun x : T => (esum [set:U] (fun x0 : U => F x0 * ((mu x)%:E * (nu x x0)%:E))%E))).
- move => x ?; rewrite muleC.
  rewrite -esumZ.
  - move => x1; rewrite mule_ge0 //=.
  - exact:  (ge0_mu (nu x) x1).
  rewrite {1}(eq_esum _ _
           (fun x0 : U => F x0 * ((mu x)%:E * (nu x x0)%:E))%E) // ?esum_sum' //.
  - by move => ??; rewrite muleCA.
rewrite exchange_esum //.
rewrite {1}(eq_esum _ _
           (fun x => (F x * (\esum_(y in [set: T]) (mu y * nu y x)%:E))%E)) //.
- move => ??. rewrite esumZ //.
  by move => ?; rewrite  mule_ge0 // lee_tofin.
Qed.

Lemma eexpZ mu F c :
  (forall x, 0%:E <= F x)%E ->
  espe mu (fun x => mule c (F x)) = mule c (espe mu F).
Proof.
move => h.
rewrite -esumZ.
+ by move => x; rewrite mule_ge0 // lee_tofin.
by apply/eq_esum => x ?; rewrite muleA.
Qed.

Lemma eexpB mu (A B : T -> \bar R) :
  (forall x, A x \is a fin_num) ->
  summable [set: T] (fun x => (A x * (mu x)%:E)%E) ->
  summable [set: T] (fun x => (B x * (mu x)%:E)%E) ->
  espe mu (A \- B)%E = (espe mu A - espe mu B)%E.
Proof.
move=> fA sA sB; rewrite /espe.
rewrite (esum.eq_esum _ _ (fun x => (A x * (mu x)%:E - B x * (mu x)%:E)%E)).
  by move => x ? /=; rewrite muleBl//; apply: fin_num_adde_defr; exact: fA.
exact: (summable_esumB sA sB).
Qed.

Lemma espE  mu (g : T -> R) :
  esp mu g = fine (espe mu (EFin \o g)).
Proof.
by rewrite /esp /espe; congr (fine _); apply: esum.eq_esum => x ? /=; rewrite EFinM.
Qed.

Lemma espeEFin mu (g : T -> R) :
  espe mu (EFin \o g) = esum [set: T] (EFin \o (fun x => g x * mu x)).
Proof. by rewrite /espe; apply: esum.eq_esum => x ? /=; rewrite EFinM. Qed.

Lemma eexp_dlet_esp {U: choiceType} mu (nu : T -> {distr U / R}) (g : U -> R) :
  (forall y, 0 <= g y) -> (forall eta, \E?_[eta] g) ->
  espe (dlet nu mu) (EFin \o g) = espe mu (EFin \o (fun x => esp (nu x) g)).
Proof.
move=> ? sg.
rewrite (eexp_dlet mu nu ).
+ by move=> x; rewrite /= lee_fin.
apply eq_esum => ?? //=.
congr (_ * _)%E.
rewrite /esp fineK//.
exact: (summable_esum_fin_num (sg (nu _))).
Qed.

End EspeCoreTheory.

(* -------------------------------------------------------------------- *)
Section PrTheory.
Context {R : realType} {T U : choiceType} {I : eqType}.

Implicit Types (mu : {distr T / R}) (A B E : pred T).

Lemma prE (nu : {distr T / R}) (E : pred T) :
  (\P_[nu] E)%:E = \esum_(t in [set: T]) ((E t)%:R * nu t)%:E.
Proof.
rewrite /pr fineK// esum_abse//.
+ by move => ?; rewrite mulr_ge0.
by have := summable_pr E nu; rewrite summableE.
Qed.

Lemma EFin_esumZ {J : choiceType} {c : R} {a : J -> R} :
  0 <= c -> (forall i, 0 <= a i) ->
  \esum_(i in [set: J]) (c * a i)%:E = (c%:E * \esum_(i in [set: J]) (a i)%:E)%E.
Proof.
move=> c0 a0; rewrite -esumZ.
- by move=> i ?; rewrite lee_fin; exact: a0.
- by apply: eq_esum => i _; rewrite EFinM.
Qed.

Lemma pr_dlet E f (mu : {distr U / R}) :
  \P_[dlet f mu] E = \E_[mu] (fun x => \P_[f x] E).
Proof.
rewrite /pr /esp.
congr (fine _).
rewrite {1}(eq_esum _ _ (fun t => \esum_(x in [set: U]) ((E t)%:R * (mu x * f x t))%:E)%E).
+ by move => t _; rewrite EFinM dlet_EFin EFin_esumZ // => ?; rewrite mulr_ge0.
rewrite {1} exchange_esum//.
+ move=> t x;rewrite lee_fin.
  by apply: mulr_ge0; [exact: ler0n|apply: mulr_ge0; exact: ge0_mu].
apply: eq_esum => x _ //=.
rewrite EFinM prE muleC -EFin_esumZ //.
+ by move => ?; rewrite mulr_ge0.
by apply: eq_esum => t _; rewrite mulrCA.
Qed.

Lemma pr_dmargin E f (mu : {distr U / R}) :
  \P_[dmargin f mu] E = \P_[mu] [pred x | f x \in E].
Proof.
by rewrite /dmargin pr_dlet pr_exp; apply/eq_exp=> x _; rewrite pr_dunit.
Qed.

Lemma eq0_pr A mu :
  (forall x, x \in dinsupp mu -> x \notin A) -> \P_[mu] A = 0.
Proof.
move=> h; rewrite /pr esum1 //= => x ?.
have -> // : (A x)%:R * mu x = 0.
apply /eqP; rewrite mulf_eq0 orbC; case/boolP: (mu x == 0) => //=.
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
move=> le_BA; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
rewrite ler_wpM2r // ?ge0_mu.
rewrite ler_nat; have := le_BA x; rewrite -!topredE /=.
by case: (B x) => // ->.
Qed.

Lemma le1_pr A mu : \P_[mu] A <= 1.
Proof.
apply: (@le_trans _ _ \P_[mu] predT); first by apply/subset_pr.
rewrite pr_predT -fine1; apply: fine_le; [| by [] | exact: le1_mu].
rewrite ge0_fin_numE; last first.
+ apply: le_lt_trans; [exact: le1_mu|  by rewrite ltey].
by apply: esum_ge0 => x _; rewrite lee_fin ge0_mu.
Qed.

Lemma le_exp mu f1 f2: \E?_[mu] f1 -> \E?_[mu] f2 ->
  f1 <=1 f2 -> \E_[mu] f1 <= \E_[mu] f2.
Proof.
move=> sm1 sm2 le_f; rewrite /esp; apply: fine_le.
- exact: (summable_esum_fin_num sm1).
- exact: (summable_esum_fin_num sm2).
- apply: le_esum.
  move=> x /=; have hf := le_f x.
  by rewrite lee_fin ler_wpM2r // ?ge0_mu.
Qed.

Lemma le_in_pr E1 E2 mu :
  (forall x, x \in dinsupp mu -> x \in E1 -> x \in E2) ->
    \P_[mu] E1 <= \P_[mu] E2.
Proof.
move=> le; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP: (x \in dinsupp mu) => [xin|/dinsuppPn ->]; last by rewrite !mulr0.
have hE : (E1 x)%:R <= (E2 x)%:R :> R.
  rewrite ler_nat; have := le x xin; rewrite -!topredE /=.
  by case: (E1 x) => // ->.
by rewrite ler_wpM2r // ?ge0_mu.
Qed.

Lemma le_mu_pr A mu nu :
    (forall x, x \in dinsupp nu -> x \in A -> nu x <= mu x)
  -> \P_[nu] A <= \P_[mu] A.
Proof.
move=> h; rewrite -lee_fin !prE.
apply: le_esum => x _; rewrite lee_fin.
case/boolP: (x \in dinsupp nu) => [/h {}h|]; last first.
  by move/dinsuppPn=> ->; rewrite mulr0; apply: mulr_ge0; [exact: ler0n|exact: ge0_mu].
by case/boolP: (A x) => [/h|]; rewrite ?(mul0r, mul1r).
Qed.

Lemma le1_prc A B mu : \P_[mu, B] A <= 1.
Proof.
move: (ge0_pr B mu); rewrite /prc le_eqVlt.
case/orP=> [/eqP<-|]; first by rewrite invr0 mulr0 ler01.
move/ler_pdivrMr=> ->; rewrite mul1r.
by apply: le_in_pr => x _ /andP[].
Qed.

Lemma prc_sum A mu : 0 < \P_[mu] A ->
 fine(esum [set: T] (fun x => (\P_[mu, A] (pred1 x))%:E)) = 1.
Proof.
move=> gt0.
have a0 : forall i, 0 <= (A i)%:R * mu i.
  by move=> i; apply: mulr_ge0; [exact: ler0n|exact: ge0_mu].
have hpr1 : forall x, \P_[mu] [predI pred1 x & A] = (A x)%:R * mu x.
  move=> x; rewrite /pr.
  rewrite (eq_esum _ _ ( fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
    move=> y _ /=; rewrite !inE [y == x]eq_sym.
    by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
  by rewrite esum_unit.
rewrite (eq_esum _ _ (fun x => ((\P_[mu] A)^-1 * ((A x)%:R * mu x))%:E)).
 by move=> x _; rewrite /prc hpr1; congr (_ %:E); rewrite mulrC.
rewrite (EFin_esumZ _ a0); last first. rewrite -prE -EFinM mulVf //.
+ by rewrite gt_eqF.
 by rewrite invr_ge0; exact: ge0_pr.
Qed.

Lemma pr_eq0 mu E : \P_[mu] E = 0 -> forall x, x \in E -> mu x = 0.
Proof.
move=> hE x xE.
have hle : \P_[mu] (pred1 x) <= \P_[mu] E.
  by apply: subset_pr => y; rewrite !inE => /eqP ->.
move: hle; rewrite hE -pr_pred1 => h.
by apply/eqP; rewrite eq_le h /=; exact: ge0_mu.
Qed.

Lemma prID A B mu :
  \P_[mu] A = \P_[mu] [predI A & B] + \P_[mu] [predI A & predC B].
Proof.
have ge0 : forall (P : pred T) i, (0 <= ((P i)%:R * mu i)%:E)%E.
  by move=> P i; rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
by case: (A x); case: (B x).
Qed.

Lemma pr_or_indep (A B : pred T) (mu : {distr T / R}) :
  (forall x, x \in A -> x \notin B) ->
    \P_[mu] [predU A & B] = \P_[mu] A + \P_[mu] B.
Proof.
move=> dsj.
have ge0 : forall (P : pred T) i, (0 <= ((P i)%:R * mu i)%:E)%E.
  by move=> P i; rewrite lee_fin mulr_ge0 ?ler0n ?ge0_mu.
apply: EFin_inj; rewrite EFinD !prE.
rewrite -(esumD (fun i _ => ge0 _ i) (fun i _ => ge0 _ i)).
apply: eq_esum => x _; rewrite -EFinD; congr (_ %:E).
rewrite !inE -!topredE /= -mulrDl; congr (_ * _).
rewrite -natrD; congr (_ %:R).
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
Proof. by rewrite pr_or subKr. Qed.

Lemma ler_pr_or A B mu :
  \P_[mu] [predU A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_or lerBlDr lerDl ge0_pr. Qed.

Lemma ler_pr_and A B mu :
  \P_[mu] [predI A & B] <= \P_[mu] A + \P_[mu] B.
Proof. by rewrite pr_and lerBlDr lerDl ge0_pr. Qed.

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

Lemma prc_pred1 (mu : {distr T / R}) x A :
  prc mu (pred1 x) A = (A x)%:R * mu x / \P_[mu] A.
Proof.
rewrite /prc; congr (_ / _); rewrite /pr.
rewrite (eq_esum _ _ (fun y => if x == y then ((A y)%:R * mu y)%:E else 0)).
  move=> y _ /=; rewrite !inE [y == x]eq_sym.
  by case: ifP => xy; rewrite ?xy /= ?mul1r ?mul0r.
by rewrite esum_unit.
Qed.

Lemma summable_pr_f f mu (P : pred T):
  \E?_[mu] f ->
  summable [set: T] (EFin \o (fun x => (P x)%:R * (f x * mu x))).
Proof.
move=> sm; rewrite /summable //= .
rewrite (eq_esum _ _
           (fun x => `|((P x)%:R)%:E * (f x * mu x)%:E|)%E).
by move => i _ //; rewrite -abseM.
apply: summableMl; last exact: sm.
exists 1%:E; split => [x|]; last by [].
by rewrite gee0_abs ?lee_fin ?ler0n// lern1 leq_b1.
Qed.

Lemma sum_fin_num_mu_f f mu (P : pred T):
    \E?_[mu] f ->
    esum [set:T] (EFin \o (fun x => (P x)%:R * (f x * mu x))) \is a fin_num.
Proof.
  move=> ?; apply: summable_esum_fin_num;  exact: summable_pr_f.
Qed.

Lemma pr_esp_sum mu f (P : pred T):
  \E?_[mu] f ->
  \P_[mu] P * \E_[mu, P] f =
  fine (esum [set: T] (EFin \o (fun x => (P x)%:R * (f x * mu x)))).
Proof.
move => sm.
  have [c0|cn0] := eqVneq (\P_[mu] P) 0.
rewrite c0 mul0r.
  suff -> : esum [set:T] (EFin \o (fun x => (P x)%:R * (f x * mu x))) = 0 by rewrite fine0.
  rewrite (esum.eq_esum _ _ (fun=> 0%E)) ?esum0// => x.
  suff h0 : (P x)%:R * mu x = 0 :> R by rewrite /= mulrCA h0 mulr0.
  case Hpx: (P x); last by rewrite mul0r.
  by rewrite (pr_eq0 c0 Hpx) mulr0.
rewrite /espc.
rewrite (esum.eq_esum _ _ (fun x => ((\P_[mu] P)^-1 %:E *
                (EFin \o (fun x => ((P x)%:R * (f x * mu x))%R)) x)%E)).
  move=> x ?; rewrite /= prc_pred1 -EFinM; congr (_ %:E).
  by rewrite mulrA mulrC; congr (_ * _); exact: mulrCA.
rewrite (summable_esumZ _ (summable_pr_f P sm));
    first by rewrite abse_fin_num.
by rewrite fineM ?abse_fin_num ?sum_fin_num_mu_f// mulVKf.
Qed.

Lemma exp_split A f mu : \E?_[mu] f -> \E_[mu] f =
    \P_[mu]        A  * \E_[mu,       A] f
  + \P_[mu] (predC A) * \E_[mu, predC A] f.
Proof.
move=> sm.
rewrite (pr_esp_sum A) // (pr_esp_sum (predC A)) // /esp -fineD ?sum_fin_num_mu_f//.
congr fine; rewrite -(summable_esumD (summable_pr_f A sm) (summable_pr_f (predC A) sm)).
apply: esum.eq_esum => x ? /=; rewrite -EFinD; congr (_ %:E).
rewrite -mulrDl -[LHS]mul1r; congr (_ * _).
by rewrite -natrD; case: (A x).
Qed.

Lemma bounded_has_exp mu F :
  (exists M, forall x, `|F x| <= M) -> \E?_[mu] F.
Proof.
case=> M leM; rewrite /has_esp /summable.
rewrite (eq_esum _ _ (fun x=> `|(F x)%:E * (mu x)%:E|)%E).
  move=> x _; rewrite -EFinM //=.
apply: summableMl; last exact: summable_mu.
exists M%:E; split => [x ?|]; last by [].
by rewrite /= lee_fin; exact: leM x.
Qed.

Lemma summable_has_exp mu F : summable [set: T] (EFin \o F) -> \E?_[mu] F.
Proof.
move=> smF; rewrite /has_esp /summable.
rewrite (eq_esum _ _ (fun x=> `|(F x)%:E * (mu x)%:E|)%E).
  move=> x _; rewrite -EFinM //=.
apply: summableMr; last exact: smF.
exists 1%:E; split => [x ?|]; last by [].
by rewrite /= lee_fin (ger0_norm (ge0_mu _ _)); exact: le1_mu1.
Qed.

Lemma exp_le_bd mu F (M : R) :
  0 <= M -> (forall x, `|F x| <= M) -> \E_[mu] F <= M.
Proof.
move=> ge0M bd; apply/(@le_trans _ _ (\E_[mu] (fun _ => M))).
+ apply/le_exp.
  + by apply/bounded_has_exp; exists M.
  + by apply/has_expC.
  + by move=> x; apply/(le_trans _ (bd x))/ler_norm.
by rewrite exp_cst ler_piMl // le1_pr.
Qed.

Lemma ge0_esp {V : choiceType} (eta : {distr V / R}) (g : V -> R) :
  (forall y, 0 <= g y) -> 0 <= \E_[eta] g.
Proof.
move=> g0; rewrite /esp; apply: fine_ge0; apply: esum_ge0 => x ?.
by rewrite lee_fin mulr_ge0//; exact: g0.
Qed.

Lemma exp_dlet_ge0 (mu : {distr T / R}) (nu : T -> {distr U / R}) (g : U -> R) :
  (forall y, 0 <= g y) -> (forall eta, \E?_[eta] g) ->
  \E_[dlet nu mu] g = \E_[mu] (fun x => \E_[nu x] g).
Proof. by move=> g0 sg; rewrite espE (eexp_dlet_esp mu nu g0 sg) -espE. Qed.

Lemma has_esp_le {V:choiceType} (mu : {distr V / R}) (k h : V -> R) :
  (forall x, `|k x| <= `|h x|) -> \E?_[mu] h -> \E?_[mu] k.
Proof.
move=> kh; rewrite /has_esp => fh.
rewrite summableE ge0_fin_numE.
+ apply: esum_ge0 => i _; exact: abse_ge0.
apply: (le_lt_trans _ fh).
apply: le_esum.
by move => ??; rewrite lee_fin !normrM ler_wpM2r.
Qed.

Lemma hcomp (mu : {distr T / R}) (nu : T -> {distr U / R}) (g : U -> R) :
  (forall y, 0 <= g y) -> (forall eta, \E?_[eta] g) -> \E?_[mu] (fun x => \E_[nu x] g).
Proof.
move=> g0 sg.
have hge0 : forall x, 0 <= esp (nu x) g * mu x.
  by move=> x; apply: mulr_ge0; [exact: ge0_esp | exact: ge0_mu].
rewrite /has_esp summableE.
rewrite (esum.eq_esum _ _ (EFin \o (fun x => esp (nu x) g * mu x))).
+ move=> x _ /=; rewrite ger0_norm //.
rewrite -espeEFin -(eexp_dlet_esp mu nu g0 sg) espeEFin.
exact: (summable_esum_fin_num (sg (dlet nu mu))).
Qed.

Lemma expB {V: choiceType} (f g : V -> R) (eta : {distr V / R}) :
  \E?_[eta] f -> \E?_[eta] g -> \E_[eta] (f \- g) = \E_[eta] f - \E_[eta] g.
Proof.
move=> sf sg.
rewrite !espE -fineB //.
+ by rewrite espeEFin; exact: (summable_esum_fin_num sf).
+ by rewrite espeEFin; exact: (summable_esum_fin_num sg).
congr (fine _).
rewrite {1}(eexp_eq (g:=fun x => ((f x)%:E - (g x)%:E))%E).
+ move => ?. rewrite -EFinB //.
exact : eexpB.
Qed.

Lemma exp_dlet mu (nu : T -> {distr U / R}) F :
  (forall eta, \E?_[eta] F) ->
    \E_[dlet nu mu] F = \E_[mu] (fun x => \E_[nu x] F).
Proof.
move=> sF.
have spF : forall eta, \E?_[eta] F^\+.
+ by move=> eta //=; apply: (has_esp_le (le_funrpos F) (sF eta)).
have snF : forall eta, \E?_[eta] F^\-.
+ by move=> eta; apply: (has_esp_le (le_funrneg F) (sF eta)).
transitivity (\E_[mu] (fun x => \E_[nu x] F^\+)
            - \E_[mu] (fun x => \E_[nu x] F^\-)).
rewrite -(exp_dlet_ge0 mu nu _ spF) // -(exp_dlet_ge0 mu nu _ snF) //.
rewrite -(expB (spF _) (snF _)); congr (\E_[dlet nu mu] _); symmetry; exact :funrposBneg.
rewrite -(expB (hcomp mu nu _ spF) (hcomp mu nu _ snF)) //.
apply: eq_exp => x _ /=.
rewrite -(expB (spF _) (snF _)).
congr (\E_[nu x] _); exact : funrposBneg.
Qed.

End PrTheory.

(* -------------------------------------------------------------------- *)
Section mono_esum.
Context
  {R : realType}
  {T : choiceType}
  {f : {ndistr T/ R}}.

Lemma mono_esum_Efn (E: T -> \bar R):
  (forall m, 0 <= E m)%E ->
  forall m n, (m <= n)%N ->
         (esum [set:T] (fun x => E x * (f m x)%:E) <=
            esum [set:T] (fun x => E x * (f n x)%:E))%E.
Proof.
move=> hE m n le_mn.
apply /esum.le_esum.
move => ??; rewrite lee_pmul => //=.
- rewrite lee_tofin //.
- rewrite lee_tofin //; exact: nmu_decrease.
Qed.

Lemma distr_lub_sup a :
  ((dlim f) a)%:E = ereal_sup (range (fun n => (f n a)%:E)).
Proof. by rewrite dlim_EFin (sup_range_lim (nd_f f a)). Qed.

Lemma esum_dlim_r [E : T -> \bar R]  [r : \bar R]:
  (forall m, 0 <= E m)%E ->
  (forall (n : nat), esum [set:T] (fun x : T => E x * (f n x)%:E) <= r)%E ->
  (esum [set:T] (fun x : T => E x * ((dlim f ) x)%:E) <= r)%E.
Proof.
move => hE h.
rewrite (@esum.eq_esum _ _ _ _ (fun x => ereal_sup (range (fun n =>  E x * (f n x)%:E)%E))).
- move => ??; rewrite distr_lub_sup.
  rewrite (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
  move => ??; rewrite lee_tofin //.
rewrite exchange_esum_ereal_sup //.
- by move => ??; rewrite mule_ge0 // lee_tofin.
- by move => ????; rewrite lee_pmul // ?lee_tofin // ; exact: nmu_decrease.
rewrite ge_ereal_sup//= => x [n s] <-.
exact: h.
Qed.

Lemma esum_dlim_r_r [E : T -> R]  [r : \bar R]:
  (forall m, 0 <= E m) ->
  (forall (n : nat), esum [set:T] (fun x : T => (E x * f n x)%:E) <= r)%E ->
  (esum [set:T] (fun x : T => (E x * (dlim f ) x)%:E) <= r)%E.
Proof.
move=> hE h.
rewrite (eq_esum _ _ (fun x : T => ((E x)%:E * ((dlim f) x)%:E)%E)).
+ by move => ? _; rewrite EFinM.
apply: (esum_dlim_r (E := fun x => (E x)%:E)).
- by move=> m; exact: (lee_tofin (hE m)).
- move=> n; under eq_esum => x _ do rewrite -EFinM.
  exact: h n.
Qed.

Lemma esum_dlim (E : pred T) :
  esum [set:T] (fun x : T => ((E x)%:R * (dlim f) x)%:E) =
    limn (fun n => esum [set:T] (fun x : T => ((E x)%:R * f n x)%:E)).
Proof.
have hmono : forall n m, (n <= m)%N -> forall x,
    (((E x)%:R * f n x)%:E <= ((E x)%:R * f m x)%:E)%E.
  move=> n m nm x; rewrite lee_fin; apply: ler_wpM2l; first exact: ler0n.
  by rewrite -lee_fin; exact: (nd_f f x nm).
transitivity (ereal_sup (range
    (fun n => esum [set:T] (fun x : T => ((E x)%:R * f n x)%:E)))); last first.
  by apply: sup_range_lim => n m nm; apply: le_esum => x _; exact: (hmono n m nm x).
rewrite -(@exchange_esum_ereal_sup R T (fun x n => ((E x)%:R * f n x)%:E)) //.
+ by move=> x n; rewrite lee_fin; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
+ move => x n m nm. exact: (hmono n m nm x).
apply: eq_esum => x _.
rewrite EFinM distr_lub_sup (@ge0_ereal_supZl_range R T (fun a b => (f b a)%:E)) //.
+ by move=> t n; rewrite lee_fin; exact: ge0_mu.
Qed.

End mono_esum.

Lemma distr_eqP {R : realType} {T : choiceType} (f1 f2 : {distr T / R}):
  f1 =1 f2 <-> f1 = f2.
Proof.
split=> [|->] //.
case: f1 => f1 [[]ge0_1 s1 le1_1].
case: f2 => f2 [[]ge0_2 s2 le1_2].
move => /funext /= h.
subst;f_equal; f_equal; f_equal => //=.
Qed.

(* Lemma dlet_dlim_diag' {T U : choiceType} *)
(*   (d : nat -> Distr T) (h : nat -> T -> Distr U) : *)
(*   (forall n m, (n <= m)%N -> d n <=1 d m) -> *)
(*   (forall x n m, (n <= m)%N -> h n x <=1 h m x) -> *)
(*   \dlet_(x <- \dlim_(n) d n) \dlim_(n) h n x = *)
(*     \dlim_(n) \dlet_(x <- d n) h n x. *)
(* Proof. *)
(*   move => mono_n mono_k. *)
(*   by apply/distr_eqP /dlet_dlim_diag. *)
(* Qed. *)


(* TODO: move *)
(* -------------------------------------------------------------------- *)

Section Jensen.
Context {R : realType} {I : finType}.

Definition convexon (a b : \bar R) (f : R -> R) :=
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
  by rewrite !Monoid.simpm /= !Monoid.simpm; apply/ih.
rewrite !addrA => eq1; pose z := (li * xi + l j * x j) / (li + l j).
have nz_lij: li + l j != 0 by rewrite gt_eqF ?ltr_wpDl.
have/ih := eq1 => -/(_ _ z); rewrite [_ * (_ / _)]mulrC.
rewrite mulfVK // => {}ih; apply/(le_trans (ih _)).
  by rewrite addr_ge0 ?ge0_l.
rewrite lerD2r {ih}/z [_ / _]mulrDl ![_*_/_]mulrAC.
set c1 : R := _ / _; set c2 : R := _ / _; have eqc2: c2 = 1 - c1.
  apply/(mulfI nz_lij); rewrite mulrBr mulr1 ![(li + l j)*_]mulrC.
  by apply/eqP; rewrite !mulfVK // eq_sym subr_eq addrC.
set c := (li + l j); pose z := (c * c1 * f xi + c * c2 * f (x j)).
apply/(@le_trans _ _ z); last by rewrite /z ![_*(_/_)]mulrC !mulfVK.
rewrite {}/z -![c * _ * _]mulrA -mulrDr ler_wpM2l ?addr_ge0 //.
rewrite eqc2 cvx_f // ?leNye ?leey // divr_ge0 ?addr_ge0 //=.
by rewrite ler_pdivrMr ?mul1r ?lerDl ?ltr_wpDl.
Qed.
End Jensen.
End Jensen.

Notation convex f := (convexon \-inf \+inf f).
