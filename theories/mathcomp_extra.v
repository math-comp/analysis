(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat seq fintype bigop div prime path finmap.
From mathcomp Require Import ssralg ssrnum ssrint rat finset interval.

(******************************************************************************)
(* This files contains lemmas and definitions missing from MathComp.          *)
(*                                                                            *)
(*                oflit f := Some \of                                         *)
(*          pred_omap T D := [pred x | oapp (mem D) false x]                  *)
(*                   \- f := fun x => - f x                                   *)
(*                 f \* g := fun x => f x * g x                               *)
(*               f \max g := fun x => Num.max (f x) (g x)                     *)
(*     lteBSide, bnd_simp == multirule to simplify inequalities between       *)
(*                           interval bounds                                  *)
(*               miditv i == middle point of interval i                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \* g" (at level 40, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f"  (at level 35, f at level 35).
Reserved Notation "f \max g" (at level 50, left associativity).

(* Missing coercion *)
Coercion Choice.mixin : Choice.class_of >-> Choice.mixin_of.

Lemma all_sig2_cond {I : Type} {T : Type} (D : pred I)
   (P Q : I -> T -> Prop) : T ->
    (forall x : I, D x -> {y : T | P x y & Q x y}) ->
  {f : forall x : I, T | forall x : I, D x -> P x (f x) & forall x : I, D x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

Lemma enum_ord0 : enum 'I_0 = [::].
Proof. by apply/eqP; rewrite -size_eq0 size_enum_ord. Qed.

Lemma enum_ordS n : enum 'I_n.+1 =
  rcons (map (widen_ord (leqnSn _)) (enum 'I_n)) ord_max.
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite -[in iota _  _]addn1 iotaD/= cats1 map_rcons; congr (rcons _ _).
by rewrite -map_comp/= (@eq_map _ _ _ val) ?val_enum_ord.
Qed.

Definition olift aT rT (f : aT -> rT) := Some \o f.

Lemma obindEapp {aT rT} (f : aT -> option rT) : obind f = oapp f None.
Proof. by []. Qed.

Lemma omapEbind {aT rT} (f : aT -> rT) : omap f = obind (olift f).
Proof. by []. Qed.

Lemma omapEapp {aT rT} (f : aT -> rT) : omap f = oapp (olift f) None.
Proof. by []. Qed.

Lemma oappEmap {aT rT} (f : aT -> rT) (y0 : rT) x :
  oapp f y0 x = odflt y0 (omap f x).
Proof. by case: x. Qed.

Lemma omap_comp aT rT sT (f : aT -> rT) (g : rT -> sT) :
  omap (g \o f) =1 omap g \o omap f.
Proof. by case. Qed.

Lemma oapp_comp aT rT sT (f : aT -> rT) (g : rT -> sT) x :
  oapp (g \o f) x =1 (@oapp _ _)^~ x g \o omap f.
Proof. by case. Qed.

Lemma oapp_comp_f {aT rT sT} (f : aT -> rT) (g : rT -> sT) (x : rT) :
  oapp (g \o f) (g x) =1 g \o oapp f x.
Proof. by case. Qed.

Lemma olift_comp aT rT sT (f : aT -> rT) (g : rT -> sT) :
  olift (g \o f) = olift g \o f.
Proof. by []. Qed.

Lemma compA {A B C D : Type} (f : B -> A) (g : C -> B) (h : D -> C) :
  f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma can_in_pcan [rT aT : Type] (A : {pred aT}) [f : aT -> rT] [g : rT -> aT] :
  {in A, cancel f g} -> {in A, pcancel f (fun y : rT => Some (g y))}.
Proof. by move=> fK x Ax; rewrite fK. Qed.

Lemma pcan_in_inj [rT aT : Type] [A : {pred aT}] [f : aT -> rT] [g : rT -> option aT] :
  {in A, pcancel f g} -> {in A &, injective f}.
Proof. by move=> fK x y Ax Ay /(congr1 g); rewrite !fK// => -[]. Qed.

Lemma can_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B]
    [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, cancel f f'} -> {in D', cancel h h'} ->
  {in D', cancel (f \o h) (h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK ?hK ?hD. Qed.

Lemma in_inj_comp A B C (f : B -> A) (h : C -> B) (P : pred B) (Q : pred C) :
  {in P &, injective f} -> {in Q &, injective h} -> {homo h : x / Q x >-> P x} ->
  {in Q &, injective (f \o h)}.
Proof.
by move=> Pf Qh QP x y xQ yQ xy; apply Qh => //; apply Pf => //; apply QP.
Qed.

Lemma pcan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B]
    [f' : A -> option B] [h' : B -> option C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, pcancel f f'} -> {in D', pcancel h h'} ->
  {in D', pcancel (f \o h) (obind h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK/= ?hK ?hD. Qed.

Lemma ocan_comp [A B C : Type] [f : B -> option A] [h : C -> option B]
    [f' : A -> B] [h' : B -> C] :
  ocancel f f' -> ocancel h h' -> ocancel (obind f \o h) (h' \o f').
Proof.
move=> fK hK c /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
by rewrite -[b in RHS]fK; case: (f b) => //=; have := hK c; rewrite hcE.
Qed.

Definition pred_omap T (D : {pred T}) : pred (option T) :=
  [pred x | oapp (mem D) false x].

Lemma ocan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> option A] [h : C -> option B]
    [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in pred_omap D} ->
  {in D, ocancel f f'} -> {in D', ocancel h h'} ->
  {in D', ocancel (obind f \o h) (h' \o f')}.
Proof.
move=> hD fK hK c cD /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
have bD : b \in D by have := hD _ cD; rewrite hcE inE.
by rewrite -[b in RHS]fK; case: (f b) => //=; have /hK := cD; rewrite hcE.
Qed.

(* NB: in bigop.v since mathcomp 1.13.0 *)
Lemma big_nat_widenl (R : Type) (idx : R) (op : Monoid.law idx) (m1 m2 n : nat)
    (P : pred nat) (F : nat -> R) :
  m2 <= m1 ->
  \big[op/idx]_(m1 <= i < n | P i) F i =
  \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> le_m21; have [le_nm1|lt_m1n] := leqP n m1.
  rewrite big_geq// big_nat_cond big1//.
  by move=> i /and3P[/andP[_ /leq_trans/(_ le_nm1)/ltn_geF->]].
rewrite big_mkcond big_mkcondl (big_cat_nat _ _ _ le_m21) 1?ltnW//.
rewrite [X in op X]big_nat_cond [X in op X]big_pred0; last first.
  by move=> k; case: ltnP; rewrite andbF.
by rewrite Monoid.mul1m; apply: congr_big_nat => // k /andP[].
Qed.
Arguments big_nat_widenl [R idx op].

(* NB: in bigop.v since mathcomp 1.13.0 *)
Lemma big_geq_mkord (R : Type) (idx : R) (op : Monoid.law idx) (m n : nat)
    (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(m <= i < n | P i) F i =
  \big[op/idx]_(i < n | P i && (m <= i)) F i.
Proof. by rewrite (big_nat_widenl _ 0)// big_mkord. Qed.

Lemma eqbLR (b1 b2 : bool) : b1 = b2 -> b1 -> b2.
Proof. by move->. Qed.

Lemma eqbRL (b1 b2 : bool) : b1 = b2 -> b2 -> b1.
Proof. by move->. Qed.

Lemma fset_nat_maximum (X : choiceType) (A : {fset X})
    (f : X -> nat) : A != fset0 ->
  (exists i, i \in A /\ forall j, j \in A -> f j <= f i)%nat.
Proof.
move=> /fset0Pn[x Ax].
have [/= y _ /(_ _ isT) mf] := @arg_maxnP _ [` Ax]%fset xpredT (f \o val) isT.
exists (val y); split; first exact: valP.
by move=> z Az; have := mf [` Az]%fset.
Qed.

Lemma image_nat_maximum n (f : nat -> nat) :
  (exists i, i <= n /\ forall j, j <= n -> f j <= f i)%N.
Proof.
have [i _ /(_ _ isT) mf] := @arg_maxnP _ (@ord0 n) xpredT f isT.
by exists i; split; rewrite ?leq_ord// => j jn; have := mf (@Ordinal n.+1 j jn).
Qed.

Arguments big_rmcond {R idx op I r} P.
Arguments big_rmcond_in {R idx op I r} P.

Definition opp_fun T (R : zmodType) (f : T -> R) x := (- f x)%R.
Notation "\- f" := (opp_fun f) : ring_scope.
Arguments opp_fun {T R} _ _ /.

Definition mul_fun T (R : ringType) (f g : T -> R) x := (f x * g x)%R.
Notation "f \* g" := (mul_fun f g) : ring_scope.
Arguments mul_fun {T R} _ _ _ /.

Import Order.TTheory GRing.Theory Num.Theory.

Definition max_fun T (R : numDomainType) (f g : T -> R) x := Num.max (f x) (g x).
Notation "f \max g" := (max_fun f g) : ring_scope.
Arguments max_fun {T R} _ _ _ /.

Lemma gtr_opp (R : numDomainType) (r : R) : (0 < r)%R -> (- r < r)%R.
Proof. by move=> n0; rewrite -subr_lt0 -opprD oppr_lt0 addr_gt0. Qed.

Lemma le_le_trans {disp : unit} {T : porderType disp} (x y z t : T) :
  (z <= x)%O -> (y <= t)%O -> (x <= y)%O -> (z <= t)%O.
Proof. by move=> + /(le_trans _)/[apply]; apply: le_trans. Qed.

Notation eqLHS := (X in (X == _))%pattern.
Notation eqRHS := (X in (_ == X))%pattern.
Notation leLHS := (X in (X <= _)%O)%pattern.
Notation leRHS := (X in (_ <= X)%O)%pattern.
Notation ltLHS := (X in (X <= _)%O)%pattern.
Notation ltRHS := (X in (_ < X)%O)%pattern.
Inductive boxed T := Box of T.

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

Local Open Scope order_scope.
Local Open Scope ring_scope.
Import GRing.Theory Order.TTheory.

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

Lemma mulr_ge0_gt0 (R : numDomainType) (x y : R) : 0 <= x -> 0 <= y ->
  (0 < x * y) = (0 < x) && (0 < y).
Proof.
rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mul0r ltxx.
rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite mulr0 ltxx andbC.
by apply/idP/andP=> [|_]; rewrite pmulr_rgt0.
Qed.

Section lt_le_gt_ge.
Variable (R : numFieldType).
Implicit Types x y z a b : R.

Lemma splitr x : x = x / 2%:R + x / 2%:R.
Proof. by rewrite -mulr2n -mulr_natr mulfVK //= pnatr_eq0. Qed.

Lemma ler_addgt0Pr x y : reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy e e_gt0 | lexye]; first by rewrite ler_paddr// ltW.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye ?ltr01//.
  by rewrite ler_addl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
rewrite -(@addrK _ y y) addrAC -addrA 2!mulrDl -splitr lexye//.
by rewrite divr_gt0// ?ltr0n// subr_gt0.
Qed.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma in_segment_addgt0Pr x y z :
  reflect (forall e, e > 0 -> y \in `[x - e, z + e]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz e /[dup] e_gt0 /ltW e_ge0 | xyz_e].
  by rewrite in_itv /= ler_subl_addr !ler_paddr// (itvP xyz).
by rewrite in_itv /= ; apply/andP; split; apply/ler_addgt0Pr => ? /xyz_e;
   rewrite in_itv /= ler_subl_addr => /andP [].
Qed.

Lemma in_segment_addgt0Pl x y z :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite -ler_subl_addr ltW//.
by rewrite ab // ltr_subl_addr -ltr_subl_addl subrr.
Qed.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0.
by rewrite ltW// ab// -ltr_subl_addl subrr.
Qed.

End lt_le_gt_ge.

Coercion pair_of_interval T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

Section itv_simp.
Variables (d : unit) (T : porderType d).
Implicit Types (x y : T) (b : bool).

Lemma ltBSide x y b b' :
  ((BSide b x < BSide b' y) = (x < y ?<= if b && ~~ b'))%O.
Proof. by []. Qed.

Lemma leBSide x y b b' :
  ((BSide b x <= BSide b' y) = (x < y ?<= if b' ==> b))%O.
Proof. by []. Qed.

Definition lteBSide := (ltBSide, leBSide).

Let BLeft_ltE x y b : (BSide b x < BLeft y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BRight_leE x y b : (BSide b x <= BRight y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BRight_BLeft_leE x y : (BRight x <= BLeft y)%O = (x < y)%O.
Proof. by []. Qed.
Let BLeft_BRight_ltE x y : (BLeft x < BRight y)%O = (x <= y)%O.
Proof. by []. Qed.
Let BRight_BSide_ltE x y b : (BRight x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BLeft_BSide_leE x y b : (BLeft x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BSide_ltE x y b : (BSide b x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BSide_leE x y b : (BSide b x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BInfty_leE a : (a <= BInfty T false)%O. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_geE a : (BInfty T true <= a)%O. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_le_eqE a : (BInfty T false <= a)%O = (a == BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ge_eqE a : (a <= BInfty T true)%O = (a == BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltE a : (a < BInfty T false)%O = (a != BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtE a : (BInfty T true < a)%O = (a != BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltF a : (BInfty T false < a)%O = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtF a : (a < BInfty T true)%O = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_BInfty_ltE : (BInfty T true < BInfty T false)%O. Proof. by []. Qed.

Lemma ltBRight_leBLeft (a : itv_bound T) (r : T) :
  (a < BRight r)%O = (a <= BLeft r)%O.
Proof. by move: a => [[] a|[]]. Qed.
Lemma leBRight_ltBLeft (a : itv_bound T) (r : T) :
  (BRight r <= a)%O = (BLeft r < a)%O.
Proof. by move: a => [[] a|[]]. Qed.

Definition bnd_simp := (BLeft_ltE, BRight_leE,
  BRight_BLeft_leE, BLeft_BRight_ltE,
  BRight_BSide_ltE, BLeft_BSide_leE, BSide_ltE, BSide_leE,
  BInfty_leE, BInfty_geE, BInfty_BInfty_ltE,
  BInfty_le_eqE, BInfty_ge_eqE, BInfty_ltE, BInfty_gtE, BInfty_ltF, BInfty_gtF,
  @lexx _ T, @ltxx _ T, @eqxx T).

Lemma itv_splitU1 (a : itv_bound T) (x : T) : (a <= BLeft x)%O ->
  Interval a (BRight x) =i [predU1 x & Interval a (BLeft x)].
Proof.
move=> ax z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx ax.
Qed.

Lemma itv_split1U (a : itv_bound T) (x : T) : (BRight x <= a)%O ->
  Interval (BLeft x) a =i [predU1 x & Interval (BRight x) a].
Proof.
move=> ax z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx ax.
Qed.

End itv_simp.

Definition miditv (R : numDomainType) (i : interval R) : R :=
  match i with
  | Interval (BSide _ a) (BSide _ b) => (a + b) / 2%:R
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
move: i => [[ba a|[]] [bb b|[]]] //= ab; first exact: mid_in_itv.
  by rewrite !in_itv -lteif_subl_addl subrr lteif01.
by rewrite !in_itv lteif_subl_addr -lteif_subl_addl subrr lteif01.
Qed.

Lemma miditv_le_left i b : (i.1 < i.2)%O -> (BSide b (miditv i) <= i.2)%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[_ ].
by apply: le_trans; rewrite !bnd_simp.
Qed.

Lemma miditv_ge_right i b : (i.1 < i.2)%O -> (i.1 <= BSide b (miditv i))%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[+ _].
by move=> /le_trans; apply; rewrite !bnd_simp.
Qed.

End miditv_lemmas.

Section itv_porderType.
Variables (d : unit) (T : orderType d).
Implicit Types (a : itv_bound T) (x y : T) (i j : interval T) (b : bool).

Lemma predC_itvl a : [predC Interval -oo%O a] =i Interval a +oo%O.
Proof.
case: a => [b x|[]//] y.
by rewrite !inE !subitvE/= bnd_simp andbT !lteBSide/= lteifNE negbK.
Qed.

Lemma predC_itvr a : [predC Interval a +oo%O] =i Interval -oo%O a.
Proof. by move=> y; rewrite inE/= -predC_itvl negbK. Qed.

Lemma predC_itv i : [predC i] =i [predU Interval -oo%O i.1 & Interval i.2 +oo%O].
Proof.
case: i => [a a']; move=> x; rewrite inE/= itv_splitI negb_and.
by symmetry; rewrite inE/= -predC_itvl -predC_itvr.
Qed.

End itv_porderType.
