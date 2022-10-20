(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require choice.
(* Missing coercion (done before Import to avoid redeclaration error,
   thanks to KS for the trick) *)
(* MathComp 1.15 addition *)
Coercion choice.Choice.mixin : choice.Choice.class_of >-> choice.Choice.mixin_of.
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import finset interval.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Export mathcomp_extra.

(***************************)
(* MathComp 1.15 additions *)
(***************************)

(******************************************************************************)
(* This files contains lemmas and definitions missing from MathComp.          *)
(*                                                                            *)
(*               f \max g := fun x => Num.max (f x) (g x)                     *)
(*     lteBSide, bnd_simp == multirule to simplify inequalities between       *)
(*                           interval bounds                                  *)
(*               miditv i == middle point of interval i                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \max g" (at level 50, left associativity).

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

(**********************************)
(* End of MathComp 1.15 additions *)
(**********************************)

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

Section Id.
Variable x : R.
Hypothesis opxx : op x x = x.

Lemma big_const_idem I (r : seq I) P : \big[op/x]_(i <- r | P i) x = x.
Proof. by elim/big_ind : _ => // _ _ -> ->. Qed.

Lemma big_id_idem I (r : seq I) P F :
  op (\big[op/x]_(i <- r | P i) F i) x = \big[op/x]_(i <- r | P i) F i.
Proof. by elim/big_rec : _ => // ? ? ?; rewrite -opA => ->. Qed.

End Id.

Section Abelian.
Hypothesis opC : commutative op.

Let opCA : left_commutative op. Proof. by move=> x *; rewrite !opA (opC x). Qed.

Variable x : R.

Lemma big_rem_AC (I : eqType) (r : seq I) z (P : pred I) F : z \in r ->
  \big[op/x]_(y <- r | P y) F y =
    if P z then op (F z) (\big[op/x]_(y <- rem z r | P y) F y)
           else \big[op/x]_(y <- rem z r | P y) F y.
Proof.
elim: r =>// i r ih; rewrite big_cons rem_cons inE =>/predU1P[-> /[!eqxx]//|zr].
by case: eqP => [-> //|]; rewrite ih// big_cons; case: ifPn; case: ifPn.
Qed.

Lemma bigD1_AC (I : finType) j (P : pred I) F : P j ->
  \big[op/x]_(i | P i) F i = op (F j) (\big[op/x]_(i | P i && (i != j)) F i).
Proof.
rewrite (big_rem_AC _ _ (mem_index_enum j)) => ->.
by rewrite rem_filter ?index_enum_uniq// big_filter_cond big_andbC.
Qed.

Section Id.
Hypothesis opxx : op x x = x.

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

End Abelian.

End SemiGroupProperties.

Section bigmaxmin.
Local Notation max := Order.max.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : _) (T : porderType d).
Variables (I : finType) (f : I -> T) (x0 x : T) (P : pred I).

Lemma bigmax_le :
  x0 <= x -> (forall i, P i -> f i <= x) -> \big[max/x0]_(i | P i) f i <= x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxEle; case: ifPn. Qed.

Lemma bigmax_lt :
  x0 < x -> (forall i, P i -> f i < x) -> \big[max/x0]_(i | P i) f i < x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxElt; case: ifPn. Qed.

Lemma lt_bigmin :
  x < x0 -> (forall i, P i -> x < f i) -> x < \big[min/x0]_(i | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minElt; case: ifPn. Qed.

Lemma le_bigmin :
  x <= x0 -> (forall i, P i -> x <= f i) -> x <= \big[min/x0]_(i | P i) f i.
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

Section bigmin_finType.
Variable (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1_AC minA minC _ _) ->. Qed.

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

Reserved Notation "`1- r" (format "`1- r", at level 2).

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
