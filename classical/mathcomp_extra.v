(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
Require Import BinPos.
From mathcomp Require choice.
(* Missing coercion (done before Import to avoid redeclaration error,
   thanks to KS for the trick) *)
(* MathComp 1.15 addition *)
Coercion choice.Choice.mixin : choice.Choice.class_of >-> choice.Choice.mixin_of.

From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import finset interval.

(***************************)
(* MathComp 1.15 additions *)
(***************************)

(******************************************************************************)
(* This files contains lemmas and definitions missing from MathComp.          *)
(*                                                                            *)
(*               f \max g := fun x => Num.max (f x) (g x)                     *)
(*                oflit f := Some \o f                                        *)
(*          pred_oapp T D := [pred x | oapp (mem D) false x]                  *)
(*                 f \* g := fun x => f x * g x                               *)
(*                   \- f := fun x => - f x                                   *)
(*     lteBSide, bnd_simp == multirule to simplify inequalities between       *)
(*                           interval bounds                                  *)
(*               miditv i == middle point of interval i                       *)
(*                                                                            *)
(*               proj i f == f i, where f : forall i, T i                     *)
(*             dfwith f x == fun j => x if j = i, and f j otherwise           *)
(*                           given x : T i                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \* g" (at level 40, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f"  (at level 35, f at level 35).
Reserved Notation "f \max g" (at level 50, left associativity).

Number Notation positive Pos.of_num_int Pos.to_num_uint : AC_scope.

Lemma all_sig2_cond {I : Type} {T : Type} (D : pred I)
   (P Q : I -> T -> Prop) : T ->
    (forall x : I, D x -> {y : T | P x y & Q x y}) ->
  {f : forall x : I, T | forall x : I, D x -> P x (f x) & forall x : I, D x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

Definition olift aT rT (f : aT -> rT) := Some \o f.

Lemma oapp_comp aT rT sT (f : aT -> rT) (g : rT -> sT) x :
  oapp (g \o f) x =1 (@oapp _ _)^~ x g \o omap f.
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

Definition pred_oapp T (D : {pred T}) : pred (option T) :=
  [pred x | oapp (mem D) false x].

Lemma ocan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> option A] [h : C -> option B]
    [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in pred_oapp D} ->
  {in D, ocancel f f'} -> {in D', ocancel h h'} ->
  {in D', ocancel (obind f \o h) (h' \o f')}.
Proof.
move=> hD fK hK c cD /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
have bD : b \in D by have := hD _ cD; rewrite hcE inE.
by rewrite -[b in RHS]fK; case: (f b) => //=; have /hK := cD; rewrite hcE.
Qed.

Lemma eqbRL (b1 b2 : bool) : b1 = b2 -> b2 -> b1.
Proof. by move->. Qed.

Definition mul_fun T (R : ringType) (f g : T -> R) x := (f x * g x)%R.
Notation "f \* g" := (mul_fun f g) : ring_scope.
Arguments mul_fun {T R} _ _ _ /.

Definition opp_fun T (R : zmodType) (f : T -> R) x := (- f x)%R.
Notation "\- f" := (opp_fun f) : ring_scope.
Arguments opp_fun {T R} _ _ /.

Coercion pair_of_interval T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

Import Order.TTheory GRing.Theory Num.Theory.

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

Lemma sumr_le0 (R : numDomainType) I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> F i <= 0)%R -> (\sum_(i <- r | P i) F i <= 0)%R.
Proof. by move=> F0; elim/big_rec : _ => // i x Pi; apply/ler_naddl/F0. Qed.

Lemma enum_ord0 : enum 'I_0 = [::].
Proof. by apply/eqP; rewrite -size_eq0 size_enum_ord. Qed.

Lemma enum_ordSr n : enum 'I_n.+1 =
  rcons (map (widen_ord (leqnSn _)) (enum 'I_n)) ord_max.
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite -[in iota _  _]addn1 iotaD/= cats1 map_rcons; congr (rcons _ _).
by rewrite -map_comp/= (@eq_map _ _ _ val) ?val_enum_ord.
Qed.

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

Lemma oapp_comp_f {aT rT sT} (f : aT -> rT) (g : rT -> sT) (x : rT) :
  oapp (g \o f) (g x) =1 g \o oapp f x.
Proof. by case. Qed.

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

Lemma eqbLR (b1 b2 : bool) : b1 = b2 -> b1 -> b2.
Proof. by move->. Qed.

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
Notation ltLHS := (X in (X < _)%O)%pattern.
Notation ltRHS := (X in (_ < X)%O)%pattern.
Inductive boxed T := Box of T.

Lemma eq_bigl_supp [R : eqType] [idx : R] [op : Monoid.law idx] [I : Type]
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

Lemma itvxx d (T : porderType d) (x : T) : `[x, x] =i pred1 x.
Proof. by move=> y; rewrite in_itv/= -eq_le eq_sym. Qed.

Lemma itvxxP d (T : porderType d) (x y : T) : reflect (y = x) (y \in `[x, x]).
Proof. by rewrite itvxx; apply/eqP. Qed.

Lemma subset_itv_oo_cc d (T : porderType d) (a b : T) : {subset `]a, b[ <= `[a, b]}.
Proof. by apply: subitvP; rewrite subitvE !bound_lexx. Qed.

(**********************************)
(* End of MathComp 1.15 additions *)
(**********************************)

Reserved Notation "`1- r" (format "`1- r", at level 2).
Reserved Notation "f \^-1" (at level 3, format "f \^-1").

Lemma natr1 (R : ringType) (n : nat) : (n%:R + 1 = n.+1%:R :> R)%R.
Proof. by rewrite GRing.mulrSr. Qed.

Lemma nat1r (R : ringType) (n : nat) : (1 + n%:R = n.+1%:R :> R)%R.
Proof. by rewrite GRing.mulrS. Qed.

(* To be backported to finmap *)

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

Lemma card_fset_sum1 (T : choiceType) (A : {fset T}) :
  #|` A| = (\sum_(i <- A) 1)%N.
Proof. by rewrite big_seq_fsetE/= sum1_card cardfE. Qed.

Arguments big_rmcond {R idx op I r} P.
Arguments big_rmcond_in {R idx op I r} P.

(*******************************)
(* MathComp > 1.15.0 additions *)
(*******************************)

Section bigminr_maxr.
Import Num.Def.

Lemma bigminr_maxr (R : realDomainType) I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i = - \big[maxr/- x]_(i <- r | P i) - F i.
Proof.
by elim/big_rec2: _ => [|i y _ _ ->]; rewrite ?oppr_max opprK.
Qed.
End bigminr_maxr.

Section SemiGroupProperties.
Variables (R : Type) (op : R -> R -> R).
Hypothesis opA : associative op.

(* Convert an AC op : R -> R -> R to a com_law on option R *)
Definition AC_subdef of associative op & commutative op :=
  fun x => oapp (fun y => Some (oapp (op^~ y) y x)) x.
Definition oAC := nosimpl AC_subdef.

Hypothesis opC : commutative op.
Let opCA : left_commutative op. Proof. by move=> x *; rewrite !opA (opC x). Qed.
Let opAC : right_commutative op.
Proof. by move=> *; rewrite -!opA [X in op _ X]opC. Qed.

Hypothesis opyy : idempotent op.

Local Notation oop := (oAC opA opC).

Lemma opACE x y : oop (Some x) (Some y) = some (op x y). Proof. by []. Qed.

Lemma oopA_subdef : associative oop.
Proof. by move=> [x|] [y|] [z|]//; rewrite /oAC/= opA. Qed.

Lemma oopx1_subdef : left_id None oop. Proof. by case. Qed.
Lemma oop1x_subdef : right_id None oop. Proof. by []. Qed.

Lemma oopC_subdef : commutative oop.
Proof. by move=> [x|] [y|]//; rewrite /oAC/= opC. Qed.

Canonical opAC_law := Monoid.Law oopA_subdef oopx1_subdef oop1x_subdef.
Canonical opAC_com_law := Monoid.ComLaw oopC_subdef.

Context [x : R].

Lemma some_big_AC [I : Type] r P (F : I -> R) :
  Some (\big[op/x]_(i <- r | P i) F i) =
  oop (\big[oop/None]_(i <- r | P i) Some (F i)) (Some x).
Proof. by elim/big_rec2 : _ => //= i [y|] _ Pi [] -> //=; rewrite opA. Qed.

Lemma big_ACE [I : Type] r P (F : I -> R) :
  \big[op/x]_(i <- r | P i) F i =
  odflt x (oop (\big[oop/None]_(i <- r | P i) Some (F i)) (Some x)).
Proof. by apply: Some_inj; rewrite some_big_AC. Qed.

Lemma big_undup_AC [I : eqType] r P (F : I -> R) (opK : idempotent op) :
  \big[op/x]_(i <- undup r | P i) F i = \big[op/x]_(i <- r | P i) F i.
Proof. by rewrite !big_ACE !big_undup//; case=> //= ?; rewrite /oAC/= opK. Qed.

Lemma perm_big_AC [I : eqType] [r] s [P : pred I] [F : I -> R] :
 perm_eq r s -> \big[op/x]_(i <- r | P i) F i = \big[op/x]_(i <- s | P i) F i.
Proof. by rewrite !big_ACE => /(@perm_big _ _)->. Qed.

Section Id.
Hypothesis opxx : op x x = x.

Lemma big_const_idem I (r : seq I) P : \big[op/x]_(i <- r | P i) x = x.
Proof. by elim/big_ind : _ => // _ _ -> ->. Qed.

Lemma big_id_idem I (r : seq I) P F :
  op (\big[op/x]_(i <- r | P i) F i) x = \big[op/x]_(i <- r | P i) F i.
Proof. by elim/big_rec : _ => // ? ? ?; rewrite -opA => ->. Qed.

Lemma big_mkcond_idem I r (P : pred I) F :
  \big[op/x]_(i <- r | P i) F i = \big[op/x]_(i <- r) (if P i then F i else x).
Proof.
elim: r => [|i r]; rewrite ?(big_nil, big_cons)//.
by case: ifPn => Pi ->//; rewrite -[in LHS]big_id_idem.
Qed.

Lemma big_split_idem I r (P : pred I) F1 F2 :
  \big[op/x]_(i <- r | P i) op (F1 i) (F2 i) =
    op (\big[op/x]_(i <- r | P i) F1 i) (\big[op/x]_(i <- r | P i) F2 i).
Proof. by elim/big_rec3 : _ => [//|i ? ? _ _ ->]; rewrite // opCA -!opA opCA. Qed.

Lemma big_id_idem_AC I (r : seq I) P F :
  \big[op/x]_(i <- r | P i) op (F i) x = \big[op/x]_(i <- r | P i) F i.
Proof. by rewrite big_split_idem big_const_idem ?big_id_idem. Qed.

Lemma bigID_idem I r (a P : pred I) F :
  \big[op/x]_(i <- r | P i) F i =
    op (\big[op/x]_(i <- r | P i && a i) F i)
       (\big[op/x]_(i <- r | P i && ~~ a i) F i).
Proof.
rewrite -big_id_idem_AC big_mkcond_idem !(big_mkcond_idem _ _ F) -big_split_idem.
by apply: eq_bigr => i; case: ifPn => //=; case: ifPn.
Qed.

End Id.

Lemma big_rem_AC (I : eqType) (r : seq I) z (P : pred I) F : z \in r ->
  \big[op/x]_(y <- r | P y) F y =
    if P z then op (F z) (\big[op/x]_(y <- rem z r | P y) F y)
           else \big[op/x]_(y <- rem z r | P y) F y.
Proof.
by move=> /[!big_ACE] /(big_rem _)->//; case: ifP; case: (bigop _ _ _) => /=.
Qed.

Lemma bigD1_AC (I : finType) j (P : pred I) F : P j ->
  \big[op/x]_(i | P i) F i = op (F j) (\big[op/x]_(i | P i && (i != j)) F i).
Proof. by move=> /[!big_ACE] /(bigD1 _)->; case: (bigop _ _) => /=. Qed.

Variable le : rel R.
Hypothesis le_refl : reflexive le.
Hypothesis op_incr : forall x y, le x (op x y).

Lemma sub_big I [s] (P P' : {pred I}) (F : I -> R) : (forall i, P i -> P' i) ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s | P' i) F i).
Proof.
move=> PP'; rewrite !big_ACE (bigID P P')/=.
under [in X in le _ X]eq_bigl do rewrite (andb_idl (PP' _)).
case: (bigop _ _ _) (bigop _ _ _) => [y|] [z|]//=.
  by rewrite opAC op_incr.
by rewrite opC op_incr.
Qed.

Lemma sub_big_seq (I : eqType) s s' P (F : I -> R) :
  (forall i, count_mem i s <= count_mem i s')%N ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Proof.
rewrite !big_ACE => /count_subseqP[_ /subseqP[m sm ->]]/(perm_big _)->.
by rewrite big_mask big_tnth// -!big_ACE sub_big// => j /andP[].
Qed.

Lemma sub_big_seq_cond (I : eqType) s s' P P' (F : I -> R) :
    (forall i, count_mem i (filter P s) <= count_mem i (filter P' s'))%N ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Proof. by  move=> /(sub_big_seq xpredT F); rewrite !big_filter. Qed.

Lemma uniq_sub_big (I : eqType) s s' P (F : I -> R) : uniq s -> uniq s' ->
    {subset s <= s'} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Proof.
move=> us us' ss'; rewrite sub_big_seq => // i; rewrite !count_uniq_mem//.
by have /implyP := ss' i; case: (_ \in s) (_ \in s') => [] [].
Qed.

Lemma uniq_sub_big_cond (I : eqType) s s' P P' (F : I -> R) :
    uniq (filter P s) -> uniq (filter P' s') ->
    {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Proof. by move=> u u' /(uniq_sub_big xpredT F u u'); rewrite !big_filter. Qed.

Lemma sub_big_idem (I : eqType) s s' P (F : I -> R) :
    {subset s <= s'} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Proof.
move=> ss'; rewrite -big_undup_AC// -[X in le _ X]big_undup_AC//.
by rewrite uniq_sub_big ?undup_uniq// => i; rewrite !mem_undup; apply: ss'.
Qed.

Lemma sub_big_idem_cond (I : eqType) s s' P P' (F : I -> R) :
    {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Proof. by  move=> /(sub_big_idem xpredT F); rewrite !big_filter. Qed.

Lemma sub_in_big [I : eqType] (s : seq I) (P P' : {pred I}) (F : I -> R) :
    {in s, forall i, P i -> P' i} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s | P' i) F i).
Proof.
move=> PP'; apply: sub_big_seq_cond => i; rewrite leq_count_subseq//.
rewrite subseq_filter filter_subseq andbT; apply/allP => j.
by rewrite !mem_filter => /andP[/PP'/[apply]->].
Qed.

Lemma le_big_ord n m [P : {pred nat}] [F : nat -> R] : (n <= m)%N ->
  le (\big[op/x]_(i < n | P i) F i) (\big[op/x]_(i < m | P i) F i).
Proof.
by move=> nm; rewrite (big_ord_widen_cond m)// sub_big => //= ? /andP[].
Qed.

Lemma subset_big [I : finType] [A A' P : {pred I}] (F : I -> R) :
    A \subset A' ->
  le (\big[op/x]_(i in A | P i) F i) (\big[op/x]_(i in A' | P i) F i).
Proof.
move=> AA'; apply: sub_big => y /andP[yA yP]; apply/andP; split => //.
exact: subsetP yA.
Qed.

Lemma subset_big_cond (I : finType) (A A' P P' : {pred I}) (F : I -> R) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  le (\big[op/x]_(i in A | P i) F i) (\big[op/x]_(i in A' | P' i) F i).
Proof. by move=> /subsetP AP; apply: sub_big => i; have /[!inE] := AP i. Qed.

Lemma le_big_nat_cond n m n' m' (P P' : {pred nat}) (F : nat -> R) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  le (\big[op/x]_(n <= i < m | P i) F i) (\big[op/x]_(n' <= i < m' | P' i) F i).
Proof.
move=> len'n lemm' PP'i; rewrite uniq_sub_big_cond ?filter_uniq ?iota_uniq//.
move=> i; rewrite !mem_filter !mem_index_iota => /and3P[Pi ni im].
by rewrite PP'i ?ni//= (leq_trans _ ni)// (leq_trans im).
Qed.

Lemma le_big_nat n m n' m' [P] [F : nat -> R] : (n' <= n)%N -> (m <= m')%N ->
  le (\big[op/x]_(n <= i < m | P i) F i) (\big[op/x]_(n' <= i < m' | P i) F i).
Proof. by move=> len'n lemm'; rewrite le_big_nat_cond. Qed.

Lemma le_big_ord_cond n m (P P' : {pred nat}) (F : nat -> R) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  le (\big[op/x]_(i < n | P i) F i) (\big[op/x]_(i < m | P' i) F i).
Proof.
move=> nm PP'; rewrite -!big_mkord le_big_nat_cond//= => i ni.
by have := PP' (Ordinal ni).
Qed.

End SemiGroupProperties.

Section bigmaxmin.
Local Notation max := Order.max.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : _) (T : porderType d).
Variables (I : Type) (r : seq I) (f : I -> T) (x0 x : T) (P : pred I).

Lemma bigmax_le :
  x0 <= x -> (forall i, P i -> f i <= x) -> \big[max/x0]_(i <- r | P i) f i <= x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxEle; case: ifPn. Qed.

Lemma bigmax_lt :
  x0 < x -> (forall i, P i -> f i < x) -> \big[max/x0]_(i <- r | P i) f i < x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxElt; case: ifPn. Qed.

Lemma lt_bigmin :
  x < x0 -> (forall i, P i -> x < f i) -> x < \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minElt; case: ifPn. Qed.

Lemma le_bigmin :
  x <= x0 -> (forall i, P i -> x <= f i) -> x <= \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minEle; case: ifPn. Qed.

End bigmaxmin.

Section bigmax.
Local Notation max := Order.max.
Local Open Scope order_scope.
Variables (d : unit) (T : orderType d).

Section bigmax_Type.
Variables (I : Type) (r : seq I) (x : T).
Implicit Types (P a : pred I) (F : I -> T).

Lemma bigmax_mkcond P F : \big[max/x]_(i <- r | P i) F i =
  \big[max/x]_(i <- r) (if P i then F i else x).
Proof. by rewrite big_mkcond_idem ?maxxx//; [exact: maxA|exact: maxC]. Qed.

Lemma bigmax_split P F1 F2 :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
  max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem ?maxxx//; [exact: maxA|exact: maxC]. Qed.

Lemma bigmax_idl P F :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof. by rewrite maxC big_id_idem ?maxxx//; exact: maxA. Qed.

Lemma bigmax_idr P F :
  \big[max/x]_(i <- r | P i) F i = max (\big[max/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmax_idl maxC. Qed.

Lemma bigmaxID a P F : \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
      (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem maxA maxC _ _ a) ?maxxx. Qed.

End bigmax_Type.

Let le_maxr_id (x y : T) : x <= max x y. Proof. by rewrite le_maxr lexx. Qed.

Lemma sub_bigmax [x0] I s (P P' : {pred I}) (F : I -> T) :
     (forall i, P i -> P' i) ->
  \big[max/x0]_(i <- s | P i) F i <= \big[max/x0]_(i <- s | P' i) F i.
Proof. exact: (sub_big maxA maxC). Qed.

Lemma sub_bigmax_seq [x0] (I : eqType) s s' P (F : I -> T) : {subset s <= s'} ->
  \big[max/x0]_(i <- s | P i) F i <= \big[max/x0]_(i <- s' | P i) F i.
Proof. exact: (sub_big_idem maxA maxC maxxx). Qed.

Lemma sub_bigmax_cond [x0] (I : eqType) s s' P P' (F : I -> T) :
    {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  \big[max/x0]_(i <- s | P i) F i <= \big[max/x0]_(i <- s' | P' i) F i.
Proof. exact: (sub_big_idem_cond maxA maxC maxxx). Qed.

Lemma sub_in_bigmax [x0] [I : eqType] (s : seq I) (P P' : {pred I}) (F : I -> T) :
    {in s, forall i, P i -> P' i} ->
  \big[max/x0]_(i <- s | P i) F i <= \big[max/x0]_(i <- s | P' i) F i.
Proof. exact: (sub_in_big maxA maxC). Qed.

Lemma le_bigmax_nat [x0] n m n' m' P (F : nat -> T) : n' <= n -> m <= m' ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat maxA maxC). Qed.

Lemma le_bigmax_nat_cond [x0] n m n' m' (P P' : {pred nat}) (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, n <= i < m -> P i -> P' i) ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond maxA maxC). Qed.

Lemma le_bigmax_ord [x0] n m (P : {pred nat}) (F : nat -> T) : (n <= m)%N ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord maxA maxC). Qed.

Lemma le_bigmax_ord_cond [x0] n m (P P' : {pred nat}) (F : nat -> T) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond maxA maxC). Qed.

Lemma subset_bigmax [x0] [I : finType] (A A' P : {pred I}) (F : I -> T) :
    A \subset A' ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P i) F i.
Proof. exact: (subset_big maxA maxC). Qed.

Lemma subset_bigmax_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_big_cond maxA maxC). Qed.

Section bigmax_finType.
Variables (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmaxD1 j P F : P j ->
  \big[max/x]_(i | P i) F i = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1_AC maxA maxC) ->. Qed.

Lemma le_bigmax_cond j P F : P j -> F j <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigmaxD1 _ Pj) le_maxr lexx. Qed.

Lemma le_bigmax F j : F j <= \big[max/x]_i F i.
Proof. exact: le_bigmax_cond. Qed.

(* NB: as of [2022-08-02], bigop.bigmax_sup already exists for nat *)
Lemma bigmax_sup j P m F : P j -> m <= F j -> m <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj ?; apply: le_trans (le_bigmax_cond _ Pj). Qed.

Lemma bigmax_leP m P F : reflect (x <= m /\ forall i, P i -> F i <= m)
                                 (\big[max/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_le.
rewrite bigmax_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; exact: le_bigmax_cond.
Qed.

Lemma bigmax_ltP m P F :
  reflect (x < m /\ forall i, P i -> F i < m) (\big[max/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_lt.
rewrite bigmax_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; exact: le_bigmax_cond.
Qed.

Lemma bigmax_eq_arg j P F : P j -> (forall i, P i -> x <= F i) ->
  \big[max/x]_(i | P i) F i = F [arg max_(i > j | P i) F i].
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le le_bigmax_cond // andbT.
by apply/bigmax_leP; split => //; exact: PxF.
Qed.

Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in I & \big[max/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists. Qed.

Lemma le_bigmax2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[max/x]_(i | P i) F1 i <= \big[max/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_maxr 2!le_maxl ba fe /= andbT; have [//|/= af] := leP f a.
by rewrite (le_trans ba) // (le_trans _ fe) // ltW.
Qed.

End bigmax_finType.

End bigmax.
Arguments bigmax_mkcond {d T I r}.
Arguments bigmaxID {d T I r}.
Arguments bigmaxD1 {d T I x} j.
Arguments bigmax_sup {d T I x} j.
Arguments bigmax_eq_arg {d T I} x j.
Arguments eq_bigmax {d T I x} j.

Section bigmin.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : _) (T : orderType d).

Section bigmin_Type.
Variable (I : Type) (r : seq I) (x : T).
Implicit Types (P a : pred I) (F : I -> T).

Lemma bigmin_mkcond P F : \big[min/x]_(i <- r | P i) F i =
   \big[min/x]_(i <- r) (if P i then F i else x).
Proof. rewrite big_mkcond_idem ?minxx//; [exact: minA|exact: minC]. Qed.

Lemma bigmin_split P F1 F2 :
  \big[min/x]_(i <- r | P i) (min (F1 i) (F2 i)) =
  min (\big[min/x]_(i <- r | P i) F1 i) (\big[min/x]_(i <- r | P i) F2 i).
Proof. rewrite big_split_idem ?minxx//; [exact: minA|exact: minC]. Qed.

Lemma bigmin_idl P F :
  \big[min/x]_(i <- r | P i) F i = min x (\big[min/x]_(i <- r | P i) F i).
Proof. rewrite minC big_id_idem ?minxx//; exact: minA. Qed.

Lemma bigmin_idr P F :
  \big[min/x]_(i <- r | P i) F i = min (\big[min/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmin_idl minC. Qed.

Lemma bigminID a P F : \big[min/x]_(i <- r | P i) F i =
  min (\big[min/x]_(i <- r | P i && a i) F i)
      (\big[min/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem minA minC _ _ a) ?minxx. Qed.

End bigmin_Type.

Let le_minr_id (x y : T) : x >= min x y. Proof. by rewrite le_minl lexx. Qed.

Lemma sub_bigmin [x0] I s (P P' : {pred I}) (F : I -> T) :
     (forall i, P' i -> P i) ->
  \big[min/x0]_(i <- s | P i) F i <= \big[min/x0]_(i <- s | P' i) F i.
Proof. exact: (sub_big minA minC ge_refl). Qed.

Lemma sub_bigmin_cond [x0] (I : eqType) s s' P P' (F : I -> T) :
    {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  \big[min/x0]_(i <- s' | P' i) F i <= \big[min/x0]_(i <- s | P i) F i.
Proof. exact: (sub_big_idem_cond minA minC minxx ge_refl). Qed.

Lemma sub_bigmin_seq [x0] (I : eqType) s s' P (F : I -> T) : {subset s' <= s} ->
  \big[min/x0]_(i <- s | P i) F i <= \big[min/x0]_(i <- s' | P i) F i.
Proof. exact: (sub_big_idem minA minC minxx ge_refl). Qed.

Lemma sub_in_bigmin [x0] [I : eqType] (s : seq I) (P P' : {pred I}) (F : I -> T) :
    {in s, forall i, P' i -> P i} ->
  \big[min/x0]_(i <- s | P i) F i <= \big[min/x0]_(i <- s | P' i) F i.
Proof. exact: (sub_in_big minA minC ge_refl). Qed.

Lemma le_bigmin_nat [x0] n m n' m' P (F : nat -> T) :
  (n <= n')%N -> (m' <= m)%N ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat minA minC ge_refl). Qed.

Lemma le_bigmin_nat_cond [x0] n m n' m' (P P' : pred nat) (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N -> (forall i, n' <= i < m' -> P' i -> P i) ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond minA minC ge_refl). Qed.

Lemma le_bigmin_ord [x0] n m (P : pred nat) (F : nat -> T) : (m <= n)%N ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord minA minC ge_refl). Qed.

Lemma le_bigmin_ord_cond [x0] n m (P P' : pred nat) (F : nat -> T) :
    (m <= n)%N -> (forall i : 'I_m, P' i -> P i) ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond minA minC ge_refl). Qed.

Lemma subset_bigmin [x0] [I : finType] [A A' P : {pred I}] (F : I -> T) :
    A' \subset A ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P i) F i.
Proof. exact: (subset_big minA minC ge_refl). Qed.

Lemma subset_bigmin_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A' | P' i]  \subset [set i in A | P i] ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_big_cond minA minC ge_refl). Qed.

Section bigmin_finType.
Variable (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1_AC minA minC) ->. Qed.

Lemma bigmin_le_cond j P F : P j -> \big[min/x]_(i | P i) F i <= F j.
Proof.
have := mem_index_enum j; rewrite unlock; elim: (index_enum I) => //= i l ih.
rewrite inE => /orP [/eqP-> ->|/ih leminlfi Pi]; first by rewrite le_minl lexx.
by case: ifPn => Pj; [rewrite le_minl leminlfi// orbC|exact: leminlfi].
Qed.

Lemma bigmin_le j F : \big[min/x]_i F i <= F j.
Proof. exact: bigmin_le_cond. Qed.

Lemma bigmin_inf j P m F : P j -> F j <= m -> \big[min/x]_(i | P i) F i <= m.
Proof. by move=> Pj ?; apply: le_trans (bigmin_le_cond _ Pj) _. Qed.

Lemma bigmin_geP m P F : reflect (m <= x /\ forall i, P i -> m <= F i)
                                 (m <= \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: le_bigmin].
- by rewrite (le_trans lemFi)// bigmin_idl le_minl lexx.
- by move=> i Pi; rewrite (le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmin_gtP m P F :
  reflect (m < x /\ forall i, P i -> m < F i) (m < \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: lt_bigmin].
- by rewrite (lt_le_trans lemFi)// bigmin_idl le_minl lexx.
- by move=> i Pi; rewrite (lt_le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmin_eq_arg j P F : P j -> (forall i, P i -> F i <= x) ->
  \big[min/x]_(i | P i) F i = F [arg min_(i < j | P i) F i].
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigmin_le_cond //=.
by apply/bigmin_geP; split => //; exact: PFx.
Qed.

Lemma eq_bigmin j P F : P j -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in I & \big[min/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmin_eq_arg Pi0) //; eexists. Qed.

End bigmin_finType.

End bigmin.
Arguments bigmin_mkcond {d T I r}.
Arguments bigminID {d T I r}.
Arguments bigminD1 {d T I x} j.
Arguments bigmin_inf {d T I x} j.
Arguments bigmin_eq_arg {d T I} x j.
Arguments eq_bigmin {d T I x} j.

Section onem.
Variable R : numDomainType.
Implicit Types r : R.

Definition onem r := 1 - r.
Local Notation "`1- r" := (onem r).

Lemma onem0 : `1-0 = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : `1-1 = 0. Proof. by rewrite /onem subrr. Qed.

Lemma onemK r : `1-(`1-r) = r.
Proof. by rewrite /onem opprB addrCA subrr addr0. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < `1-r. Proof. by rewrite subr_gt0. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= `1-r.
Proof. by rewrite le_eqVlt => /predU1P[->|/onem_gt0/ltW]; rewrite ?onem1. Qed.

Lemma onem_le1 r : 0 <= r -> `1-r <= 1.
Proof. by rewrite ler_subl_addr ler_addl. Qed.

Lemma onem_lt1 r : 0 < r -> `1-r < 1.
Proof. by rewrite ltr_subl_addr ltr_addl. Qed.

Lemma onemX_ge0 r n : 0 <= r -> r <= 1 -> 0 <= `1-(r ^+ n).
Proof. by move=> ? ?; rewrite subr_ge0 exprn_ile1. Qed.

Lemma onemX_lt1 r n : 0 < r -> `1-(r ^+ n) < 1.
Proof. by move=> ?; rewrite onem_lt1// exprn_gt0. Qed.

Lemma onemD r s : `1-(r + s) = `1-r - s.
Proof. by rewrite /onem addrAC opprD addrA addrAC. Qed.

Lemma onemMr r s : s * `1-r = s - s * r.
Proof. by rewrite /onem mulrBr mulr1. Qed.

Lemma onemM r s : `1-(r * s) = `1-r + `1-s - `1-r * `1-s.
Proof.
rewrite /onem mulrBr mulr1 mulrBl mul1r opprB -addrA.
by rewrite (addrC (1 - r)) !addrA subrK opprB addrA subrK addrK.
Qed.

End onem.
Notation "`1- r" := (onem r) : ring_scope.

Lemma lez_abs2 (a b : int) : 0 <= a -> a <= b -> (`|a| <= `|b|)%N.
Proof. by case: a => //= n _; case: b. Qed.

Lemma ler_gtP (R : numFieldType) (x y : R) :
  reflect (forall z, z > y -> x <= z) (x <= y).
Proof.
apply: (equivP (ler_addgt0Pr _ _)); split=> [xy z|xz e e_gt0].
  by rewrite -subr_gt0 => /xy; rewrite addrC addrNK.
by apply: xz; rewrite -[ltLHS]addr0 ler_lt_add.
Qed.

Lemma ler_ltP (R : numFieldType) (x y : R) :
  reflect (forall z, z < x -> z <= y) (x <= y).
Proof.
apply: (equivP (ler_addgt0Pr _ _)); split=> [xy z|xz e e_gt0].
  by rewrite -subr_gt0 => /xy; rewrite addrCA -[leLHS]addr0 ler_add2l subr_ge0.
by rewrite -ler_subl_addr xz// -[ltRHS]subr0 ler_lt_sub.
Qed.

Definition inv_fun T (R : unitRingType) (f : T -> R) x := (f x)^-1%R.
Notation "f \^-1" := (inv_fun f) : ring_scope.
Arguments inv_fun {T R} _ _ /.

Definition bound_side d (T : porderType d) (c : bool) (x : itv_bound T) :=
  if x is BSide c' _ then c == c' else false.

Lemma real_ltr_distlC [R : numDomainType] [x y : R] (e : R) :
  x - y \is Num.real -> (`|x - y| < e) = (x - e < y < x + e).
Proof. by move=> ?; rewrite distrC real_ltr_distl// -rpredN opprB. Qed.

Definition proj {I} {T : I -> Type} i (f : forall i, T i) := f i.

Section DFunWith.
Variables (I : eqType) (T : I -> Type) (f : forall i, T i).

Definition dfwith i (x : T i) (j : I) : T j :=
  if (i =P j) is ReflectT ij then ecast j (T j) ij x else f j.

Lemma dfwithin i x : dfwith x i = x.
Proof. by rewrite /dfwith; case: eqP => // ii; rewrite eq_axiomK. Qed.

Lemma dfwithout i (x : T i) j : i != j -> dfwith x j = f j.
Proof. by rewrite /dfwith; case: eqP. Qed.

Variant dfwith_spec i (x : T i) : forall j, T j -> Type :=
  | DFunWithin : dfwith_spec x x
  | DFunWithout j : i != j -> dfwith_spec x (f j).

Lemma dfwithP i (x : T i) (j : I) : dfwith_spec x (dfwith x j).
Proof.
by case: (eqVneq i j) => [<-|nij];
   [rewrite dfwithin|rewrite dfwithout//]; constructor.
Qed.

Lemma projK i (x : T i) : cancel (@dfwith i) (proj i).
Proof. by move=> z; rewrite /proj dfwithin. Qed.

End DFunWith.
Arguments dfwith {I T} f i x.
