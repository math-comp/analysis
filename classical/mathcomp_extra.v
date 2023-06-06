(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
Require Import BinPos.
From mathcomp Require choice.
(* Missing coercion (done before Import to avoid redeclaration error,
   thanks to KS for the trick) *)
(* MathComp 1.15 addition *)

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
(*                 swap x := (x.2, x.1)                                       *)
(*                                                                            *)
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
  by rewrite !in_itv -lteifBlDl subrr lteif01.
by rewrite !in_itv lteifBlDr -lteifBlDl subrr lteif01.
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
Proof. by move=> F0; elim/big_rec : _ => // i x Pi; apply/ler_wnDl/F0. Qed.

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
apply/(iffP idP)=> [lexy e e_gt0 | lexye]; first by rewrite ler_wpDr// ltW.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye ?ltr01//.
  by rewrite lerDl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
rewrite -(subrKA y) addrACA 2!mulrDl -splitr lexye//.
by rewrite addrC divr_gt0// ?ltr0n// subr_gt0.
Qed.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma in_segment_addgt0Pr x y z :
  reflect (forall e, e > 0 -> y \in `[x - e, z + e]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz e /[dup] e_gt0 /ltW e_ge0 | xyz_e].
  by rewrite in_itv /= lerBlDr !ler_wpDr// (itvP xyz).
by rewrite in_itv /= ; apply/andP; split; apply/ler_addgt0Pr => ? /xyz_e;
   rewrite in_itv /= lerBlDr => /andP [].
Qed.

Lemma in_segment_addgt0Pl x y z :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite -lerBlDr ltW//.
by rewrite ab // ltrBlDr -ltrBlDl subrr.
Qed.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0.
by rewrite ltW// ab// -ltrBlDl subrr.
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

Section onem.
Variable R : numDomainType.
Implicit Types r : R.

Definition onem r := 1 - r.
Local Notation "`1- r" := (onem r).

Lemma onem0 : `1-0 = 1. Proof. by rewrite /onem subr0. Qed.

Lemma onem1 : `1-1 = 0. Proof. by rewrite /onem subrr. Qed.

Lemma onemK r : `1-(`1-r) = r.
Proof. by rewrite /onem opprB addrCA subrr addr0. Qed.

Lemma add_onemK r : r + `1- r = 1.
Proof. by rewrite /onem addrC subrK. Qed.

Lemma onem_gt0 r : r < 1 -> 0 < `1-r. Proof. by rewrite subr_gt0. Qed.

Lemma onem_ge0 r : r <= 1 -> 0 <= `1-r.
Proof. by rewrite le_eqVlt => /predU1P[->|/onem_gt0/ltW]; rewrite ?onem1. Qed.

Lemma onem_le1 r : 0 <= r -> `1-r <= 1.
Proof. by rewrite lerBlDr lerDl. Qed.

Lemma onem_lt1 r : 0 < r -> `1-r < 1.
Proof. by rewrite ltrBlDr ltrDl. Qed.

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
by apply: xz; rewrite -[ltLHS]addr0 ler_ltD.
Qed.

Lemma ler_ltP (R : numFieldType) (x y : R) :
  reflect (forall z, z < x -> z <= y) (x <= y).
Proof.
apply: (equivP (ler_addgt0Pr _ _)); split=> [xy z|xz e e_gt0].
  by rewrite -subr_gt0 => /xy; rewrite addrCA -[leLHS]addr0 lerD2l subr_ge0.
by rewrite -lerBlDr xz// -[ltRHS]subr0 ler_ltB.
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

Definition swap (T1 T2 : Type) (x : T1 * T2) := (x.2, x.1).

Lemma ler_sqrt {R : rcfType} (a b : R) :
  (0 <= b -> (Num.sqrt a <= Num.sqrt b) = (a <= b))%R.
Proof.
have [b_gt0 _|//|<- _] := ltgtP; last first.
  by rewrite sqrtr0 -sqrtr_eq0 le_eqVlt ltNge sqrtr_ge0 orbF.
have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt.
by rewrite ler0_sqrtr // sqrtr_ge0 (le_trans a_le0) ?ltW.
Qed.

Section order_min.
Variables (d : unit) (T : orderType d).
Import Order.
Local Open Scope order_scope.

Lemma lt_min_lt (x y z : T) : (min x z < min y z)%O -> (x < y)%O.
Proof.
rewrite /Order.min/=; case: ifPn => xz; case: ifPn => yz; rewrite ?ltxx//.
- by move=> /lt_le_trans; apply; rewrite leNgt.
- by rewrite ltNge (ltW yz).
Qed.

End order_min.

(**************************)
(* MathComp 2.1 additions *)
(**************************)

From mathcomp Require Import poly.

Definition coefE :=
  (coef0, coef1, coefC, coefX, coefXn,
   coefZ, coefMC, coefCM, coefXnM, coefMXn, coefXM, coefMX, coefMNn, coefMn,
   coefN, coefB, coefD,
   coef_cons, coef_Poly, coef_poly,
   coef_deriv, coef_nderivn, coef_derivn, coef_map, coef_sum,
   coef_comp_poly).

Module Export Pdeg2.

Module Export Field.

Section Pdeg2Field.
Variable F : fieldType.
Hypothesis nz2 : 2%:R != 0 :> F.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let a2neq0 : 2%:R * a != 0. Proof. by rewrite mulf_neq0. Qed.
Let sqa2neq0 : (2%:R * a) ^+ 2 != 0. Proof. exact: expf_neq0. Qed.

Let aa4 : 4%:R * a * a = (2%:R * a)^+2.
Proof. by rewrite expr2 mulrACA mulrA -natrM. Qed.

Let splitr (x : F) : x = x / 2%:R + x / 2%:R.
Proof.
apply: (mulIf nz2); rewrite -mulrDl mulfVK//.
by rewrite -[2%:R]/(1 + 1)%:R natrD mulrDr mulr1.
Qed.

Let pE : p = a *: 'X^2 + b *: 'X + c%:P.
Proof.
apply/polyP => + /[!coefE] => -[|[|[|i]]] /=; rewrite !Monoid.simpm//.
by rewrite nth_default// degp.
Qed.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg2_poly_canonical :
  p = a *: (('X + (b / (2%:R * a))%:P)^+2 - (delta / (4%:R * a ^+ 2))%:P).
Proof.
rewrite pE sqrrD -!addrA scalerDr; congr +%R; rewrite addrA scalerDr; congr +%R.
- rewrite -mulrDr -polyCD -!mul_polyC mulrA mulrAC -polyCM.
  by rewrite [a * _]mulrC mulrDl invfM -!mulrA mulVf// mulr1 -splitr.
- rewrite [a ^+ 2]expr2 mulrA aa4 -polyC_exp -polyCB expr_div_n -mulrBl subKr.
  by rewrite -mul_polyC -polyCM mulrCA mulrACA aa4 mulrCA mulfV// mulr1.
Qed.

Variable r : F.
Hypothesis r_sqrt_delta : r ^+ 2 = delta.

Let r1 := (- b - r) / (2%:R * a).
Let r2 := (- b + r) / (2%:R * a).

Lemma deg2_poly_factor : p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof.
rewrite [p]deg2_poly_canonical//= -/a -/b -/c -/delta /r1 /r2.
rewrite ![(- b + _) * _]mulrDl 2!polyCD 2!opprD 2!addrA !mulNr !polyCN !opprK.
rewrite -scalerAl [in RHS]mulrC -subr_sqr -polyC_exp -[4%:R]/(2 * 2)%:R natrM.
by rewrite -expr2 -exprMn [in RHS]exprMn exprVn r_sqrt_delta.
Qed.

End Pdeg2Field.
End Field.

Module Real.

Section Pdeg2Real.

Variable F : realFieldType.

Section Pdeg2RealConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis age0 : 0 <= a.

Let delta := b ^+ 2 - 4%:R * a * c.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a4gt0 : 0 < 4%:R * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Lemma deg2_poly_min x : p.[- b / (2%:R * a)] <= p.[x].
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c /delta !hornerE/=.
by rewrite ler_pM2l// lerD2r addrC mulNr subrr ?mulr0 ?expr0n sqr_ge0.
Qed.

Lemma deg2_poly_minE : p.[- b / (2%:R * a)] = - delta / (4%:R * a).
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c -/delta !hornerE/=.
rewrite -?expr2 [X in X^+2]addrC [in LHS]mulNr subrr expr0n add0r mulNr.
by rewrite mulrC mulNr invfM mulrA mulfVK.
Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2%:R * a)))]; last first.
  by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
apply: le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
Qed.

End Pdeg2RealConvex.

End Pdeg2Real.

Section Pdeg2RealClosed.

Variable F : rcfType.

Section Pdeg2RealClosedConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let nz2 : 2%:R != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Let delta := b ^+ 2 - 4%:R * a * c.

Let r1 := (- b - Num.sqrt delta) / (2%:R * a).
Let r2 := (- b + Num.sqrt delta) / (2%:R * a).

Lemma deg2_poly_factor : 0 <= delta -> p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

End Pdeg2RealClosedConvex.

End Pdeg2RealClosed.
End Real.

End Pdeg2.

Section Degle2PolyRealConvex.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg_le2_poly_delta_ge0 : 0 <= a -> (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
move=> age0 pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'.
  exact/(Real.deg2_poly_ge0 degp' age0).
have a0 : a = 0 by rewrite /a nth_default.
rewrite /delta a0 mulr0 mul0r subr0 exprn_even_le0//=.
have [//|/eqP nzb] := eqP; move: (pge0 ((- 1 - c) / b)).
have -> : p = b *: 'X + c%:P.
  apply/polyP => + /[!coefE] => -[|[|i]] /=; rewrite !Monoid.simpm//.
  by rewrite nth_default// -ltnS (leq_trans degp').
by rewrite !hornerE/= mulrAC mulfV// mul1r subrK ler0N1.
Qed.

End Degle2PolyRealConvex.

Section Degle2PolyRealClosedConvex.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4%:R * a * c.

Lemma deg_le2_poly_ge0 : (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
have [age0|alt0] := leP 0 a; first exact: deg_le2_poly_delta_ge0.
move=> pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'; last first.
  by move: alt0; rewrite /a nth_default ?ltxx.
have [//|dge0] := leP delta 0.
pose r1 := (- b - Num.sqrt delta) / (2%:R * a).
pose r2 := (- b + Num.sqrt delta) / (2%:R * a).
pose x0 := Num.max (r1 + 1) (r2 + 1).
move: (pge0 x0); rewrite (Real.deg2_poly_factor degp' (ltW dge0)).
rewrite !hornerE/= -mulrA nmulr_rge0// leNgt => /negbTE<-.
by apply: mulr_gt0; rewrite subr_gt0 lt_maxr ltrDl ltr01 ?orbT.
Qed.

End Degle2PolyRealClosedConvex.

(* not yet backported *)
Lemma deg_le2_ge0 (F : rcfType) (a b c : F) :
  (forall x, 0 <= a * x ^+ 2 + b * x + c)%R -> (b ^+ 2 - 4%:R * a * c <= 0)%R.
Proof.
move=> pge0; pose p := \poly_(i < 3) [:: c; b; a]`_i.
have := @deg_le2_poly_ge0 _ p (size_poly _ _); rewrite !coef_poly/=; apply=> r.
rewrite horner_poly !big_ord_recr !big_ord0/= !Monoid.simpm/= expr1.
by rewrite -mulrA -expr2 addrC addrA addrAC.
Qed.
