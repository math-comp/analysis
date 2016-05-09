(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra bigenough.
(* ------- *) Require Import boolp Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory BigEnough.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope real_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Module Real.
Section Mixin.

Variable (R : archiFieldType).

(* Real set non-emptyness. *)
Definition nonempty (E : pred R) :=
  exists x : R, x \in E.

(* Real upper bound set. *)
Definition ub (E : pred R) : pred R :=
  [pred z | `[forall y, (y \in E) ==> (y <= z)]].

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down (E : pred R) : pred R :=
  [pred x | `[exists y, (y \in E) && (x <= y)]].

(* Real set supremum existence condition. *)
Definition has_ub  (E : pred R) := nonempty (ub E).
Definition has_sup (E : pred R) := nonempty E /\ has_ub E.

Record mixin_of : Type := Mixin {
  sup : pred R -> R;
   _  :
    forall E : pred (Num.ArchimedeanField.sort R),
      has_sup E -> sup E \in ub E;
   _  :
    forall (E : pred (Num.ArchimedeanField.sort R)) (eps : R),
      has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e;
   _  :
    forall E : pred (Num.ArchimedeanField.sort R),
      ~ has_sup E -> sup E = 0
}.

End Mixin.

Definition EtaMixin R sup sup_upper_bound sup_adherent :=
  let _ := @Mixin R sup sup_upper_bound sup_adherent in
  @Mixin (Num.ArchimedeanField.Pack (Num.ArchimedeanField.class R) R)
         sup sup_upper_bound sup_adherent.
Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Num.ArchimedeanField.class_of R;
  mixin : mixin_of (Num.ArchimedeanField.Pack base R)
}.

Local Coercion base : class_of >-> Num.ArchimedeanField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Num.ArchimedeanField.Pack T b0 T)) :=
  fun bT b & phant_id (Num.ArchimedeanField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition join_numDomainType := @Num.NumDomain.Pack fieldType xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition join_realDomainType := @Num.RealDomain.Pack numFieldType xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archimedeanFieldType := @Num.ArchimedeanField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.ArchimedeanField.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Canonical join_numDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Coercion archimedeanFieldType : type >-> Num.ArchimedeanField.type.
Canonical archimedeanFieldType.

Notation realType := type.
Notation RealType T m := (@pack T _ m _ _ id _ id).
Notation RealMixin := EtaMixin.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.

End Exports.
End Real.

Export Real.Exports.

(* -------------------------------------------------------------------- *)
Definition sup {R : realType} := Real.sup (Real.class R).

Definition nonempty {R : realType} := @Real.nonempty R.
Definition ub       {R : realType} := @Real.ub R.
Definition down     {R : realType} := @Real.down R.
Definition has_ub   {R : realType} := @Real.has_ub R.
Definition has_sup  {R : realType} := @Real.has_sup R.

(* -------------------------------------------------------------------- *)
Section BaseReflect.
Context {R : realType}.

Implicit Types E : pred R.
Implicit Types x : R.

Lemma nonemptyP E : nonempty E <-> exists x, x \in E.
Proof. by []. Qed.

Lemma ubP E x : reflect (forall y, y \in E -> y <= x) (x \in ub E).
Proof. by apply: (iffP (forallbP _))=> h y; apply/implyP/h. Qed.

Lemma downP E x : reflect (exists2 y, y \in E & x <= y) (x \in down E).
Proof.
apply: (iffP (existsbP _))=> [[y /andP[]]|[y]].
  by exists y. by exists y; apply/andP; split.
Qed.

Lemma has_ubP {E} : has_ub E <-> nonempty (ub E).
Proof. by []. Qed.

Lemma has_supP {E} : has_sup E <-> (nonempty E /\ nonempty (ub E)).
Proof. by []. Qed.
End BaseReflect.

(* -------------------------------------------------------------------- *)
Lemma sup_upper_bound {R : realType} (E : pred R):
  has_sup E -> (forall x, x \in E -> x <= sup E).
Proof. by move=> supE; apply/ubP; case: R E supE=> ? [? []]. Qed.

Lemma sup_adherent {R : realType} (E : pred R) (eps : R) :
  has_sup E -> 0 < eps -> exists2 e : R, e \in E & (sup E - eps) < e.
Proof. by case: R E eps=> ? [? []]. Qed.

Lemma sup_out {R : realType} (E : pred R) : ~ has_sup E -> sup E = 0.
Proof. by case: R E => ? [? []]. Qed.

(* -------------------------------------------------------------------- *)
Section IsInt.
Context {R : realType}.

Definition Rint := [qualify a x : R | `[exists z, x == z%:~R]].
Fact Rint_key : pred_key Rint. Proof. by []. Qed.
Canonical Rint_keyed := KeyedQualifier Rint_key.

Lemma Rint_def x : (x \is a Rint) = (`[exists z, x == z%:~R]).
Proof. by []. Qed.

Lemma RintP x : reflect (exists z, x = z%:~R) (x \in Rint).
Proof. exact/(iffP (existsPP (fun x => eqP (y := x%:~R)))). Qed.

Lemma RintC z : z%:~R \is a Rint.
Proof. by apply/RintP; exists z. Qed.

Lemma Rint0 : 0 \is a Rint.
Proof. by rewrite -[0](mulr0z 1) RintC. Qed.

Lemma Rint1 : 1 \is a Rint.
Proof. by rewrite -[1]mulr1z RintC. Qed.

Hint Resolve Rint0 Rint1 RintC.

Lemma Rint_subring_closed : subring_closed Rint.
Proof.
split=> // _ _ /RintP[x ->] /RintP[y ->]; apply/RintP.
by exists (x - y); rewrite rmorphB. by exists (x * y); rewrite rmorphM.
Qed.

Canonical Rint_opprPred := OpprPred Rint_subring_closed.
Canonical Rint_addrPred := AddrPred Rint_subring_closed.
Canonical Rint_mulrPred := MulrPred Rint_subring_closed.
Canonical Rint_zmodPred := ZmodPred Rint_subring_closed.
Canonical Rint_semiringPred := SemiringPred Rint_subring_closed.
Canonical Rint_smulrPred := SmulrPred Rint_subring_closed.
Canonical Rint_subringPred := SubringPred Rint_subring_closed.

Lemma Rint_ler_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x + 1 <= y) = (x < y).
Proof.
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{2}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) lez_addr1.
Qed.

Lemma Rint_ltr_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x < y + 1) = (x <= y).
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{3}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) ltz_addr1.
Qed.

End IsInt.

(* -------------------------------------------------------------------- *)
Section ToInt.
Context {R : realType}.

Implicit Types x y : R.

Definition Rtoint (x : R) : int :=
  if insub x : {? x | x \is a Rint} is Some Px then
    xchooseb (tagged Px)
  else 0.

Lemma RtointK (x : R): x \is a Rint -> (Rtoint x)%:~R = x.
Proof.
move=> Ix; rewrite /Rtoint insubT /= [RHS](eqP (xchoosebP Ix)).
by congr _%:~R; apply/eq_xchoose.
Qed.

Lemma Rtointz (z : int): Rtoint z%:~R = z.
Proof. by apply/eqP; rewrite -(@eqr_int R) RtointK ?rpred_int. Qed.

Lemma Rtointn (n : nat): Rtoint n%:R = n%:~R.
Proof. by rewrite -{1}mulrz_nat Rtointz. Qed.

Lemma inj_Rtoint : {in Rint &, injective Rtoint}.
Proof. by move=> x y Ix Iy /= /(congr1 (@intmul R 1)); rewrite !RtointK. Qed.
End ToInt.

(* -------------------------------------------------------------------- *)
Section RealDerivedOps.
Variable R : realType.

Implicit Types x y : R.

Definition floor_set x := [pred y | (y \is a Rint) && (y <= x)].

Definition floor x : R := sup (floor_set x).

Definition ifloor x : int := Rtoint (floor x).

Definition range1 (x : R) := [pred y | x <= y < x + 1].
End RealDerivedOps.

(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType).

Implicit Types E : pred R.
Implicit Types x : R.

Lemma sup_ub {E} : has_ub E -> sup E \in ub E.
Proof.
move=> ubE; apply/ubP=> x x_in_E; apply/sup_upper_bound=> //.
by apply/has_supP; split; first by exists x.
Qed.

Lemma sup_total {E} x : has_sup E -> (x \in down E) || (sup E <= x).
Proof.
move=> has_supE; rewrite orbC; case: (lerP (sup E) x)=> hx //=.
have /(sup_adherent has_supE) : 0 < sup E - x by rewrite subr_gt0.
case=> e Ee hlte; apply/downP; exists e => //; move: hlte.
by rewrite opprB addrCA subrr addr0 => /ltrW.
Qed.

Lemma sup_le_ub {E} x : nonempty E -> x \in ub E -> sup E <= x.
Proof.
move=> hasE /ubP leEx; set y := sup E; pose z := (x + y) / 2%:R.
have Dz: 2%:R * z = x + y.
  by rewrite mulrCA divff ?mulr1 // pnatr_eq0.
have ubE: has_sup E by split; last by exists x; apply/ubP.
have /orP [/downP [t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(ler_add2l x) -Dz -mulr2n -[X in _<=X]mulr_natl.
  rewrite ler_pmul2l ?ltr0Sn //; exact/(ler_trans lezt)/leEx.
rewrite -(ler_add2r y) -Dz -mulr2n -[X in X<=_]mulr_natl.
by rewrite ler_pmul2l ?ltr0Sn.
Qed.

Lemma nonemptybP {E} :
  `[< nonempty E >] = `[< exists x : R, x \in E >].
Proof. by apply: (asbool_equiv_eq (nonemptyP _)). Qed.

Lemma nonemptyPn {E} :
  ~ nonempty E <-> (forall x, x \notin E).
Proof.
by apply: asbool_eq_equiv; rewrite asbool_neg nonemptybP asbool_forallNb.
Qed.

Lemma has_ubPn {E} :
  ~ has_ub E <-> (forall x, exists2 y, y \in E & x < y).
Proof. split; last first.
+ move=> h /has_ubP [x /ubP] hle; case/(_ x): h => y /hle.
  by rewrite lerNgt => /negbTE ->.
move/asboolPn; rewrite (asbool_equiv_eq has_ubP).
move/asboolPn/nonemptyPn=> h x; have /ubP {h} := h x.
case/asboolPn/existsp_asboolPn=> y /asboolPn /imply_asboolPn.
by case=> [yE /negP]; rewrite -ltrNge => ltx; exists y.
Qed.

Lemma has_supPn {E} : nonempty E ->
  ~ has_sup E <-> (forall x, exists2 y, y \in E & x < y).
Proof.
move=> nzE; split=> [/asboolPn|]; rewrite ?(asbool_equiv_eq has_supP).
  by rewrite asbool_and (asboolT nzE) /= => /asboolP/has_ubPn.
by move/has_ubPn=> h /has_supP [_].
Qed.

End RealLemmas.

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma has_sup_floor_set x: has_sup (floor_set x).
Proof.
split; [exists (- (Num.bound (-x))%:~R) | exists (Num.bound x)%:~R].
  rewrite inE rpredN rpred_int /= ler_oppl.
  case: (ger0P (-x)) => [/archi_boundP/ltrW//|].
  by move/ltrW/ler_trans; apply; rewrite ler0z.
apply/ubP=> y /andP[_] /ler_trans; apply.
case: (ger0P x)=> [/archi_boundP/ltrW|] //.
by move/ltrW/ler_trans; apply; rewrite ler0z.
Qed.

Lemma sup_in_floor_set x : sup (floor_set x) \in floor_set x.
Proof.
have /sup_adherent /(_ ltr01) [y Fy] := has_sup_floor_set x.
have /sup_upper_bound /(_ _ Fy) := has_sup_floor_set x.
rewrite ler_eqVlt=> /orP[/eqP<-//| lt_yFx].
rewrite ltr_subl_addr -ltr_subl_addl => lt1_FxBy.
pose e := sup (floor_set x) - y; have := has_sup_floor_set x.
move/sup_adherent=> -/(_ e) []; first by rewrite subr_gt0.
move=> z Fz; rewrite /e opprB addrCA subrr addr0 => lt_yz.
have /sup_upper_bound /(_ _ Fz) := has_sup_floor_set x.
rewrite -(ler_add2r (-y)) => /ler_lt_trans /(_ lt1_FxBy).
case/andP: Fy Fz lt_yz=> /RintP[yi -> _]. 
case/andP=> /RintP[zi -> _]; rewrite -rmorphB /= ltrz1 ltr_int.
rewrite ltr_neqAle => /andP[ne_yz le_yz].
rewrite -[_-_]gez0_abs ?subr_ge0 // ltz_nat ltnS leqn0.
by rewrite absz_eq0 subr_eq0 eq_sym (negbTE ne_yz).
Qed.

Lemma isint_floor x: floor x \is a Rint.
Proof. by case/andP: (sup_in_floor_set x). Qed.

Lemma floorE x : floor x = (ifloor x)%:~R.
Proof. by rewrite /ifloor RtointK ?isint_floor. Qed.

Lemma mem_rg1_floor (x : R) : x \in range1 (floor x).
Proof.
rewrite inE; have /andP[_ ->] /= := sup_in_floor_set x.
case: (boolP (floor x + 1 \in floor_set x)); last first.
  by rewrite inE negb_and -ltrNge rpredD // ?(Rint1, isint_floor).
by move/sup_upper_bound=> -/(_ (has_sup_floor_set x)); rewrite ger_addl ler10.
Qed.

Lemma floor_ler (x : R) : floor x <= x.
Proof. by case/andP: (mem_rg1_floor x). Qed.

Lemma floorS_gtr (x : R) : x < floor x + 1.
Proof. by case/andP: (mem_rg1_floor x). Qed.

Lemma range1z_inj (x : R) (m1 m2 : int) :
  x \in range1 m1%:~R -> x \in range1 m2%:~R -> m1 = m2.
Proof.
move=> /andP[m1x x_m1] /andP[m2x x_m2].
wlog suffices: m1 m2 m1x {x_m1 m2x} x_m2 / (m1 <= m2)%R.
  by move=> ih; apply/eqP; rewrite eqr_le !ih.
rewrite -(ler_add2r 1) lez_addr1 -(@ltr_int R) intrD.
by apply/(ler_lt_trans m1x).
Qed.

Lemma range1rr (x : R) : x \in range1 x.
Proof. by rewrite inE lerr /= ltr_addl ltr01. Qed.

Lemma range1zP (m : int) (x : R) :
  reflect (floor x = m%:~R) (x \in range1 m%:~R).
Proof.
apply: (iffP idP)=> [h|<-]; [apply/eqP | by apply/mem_rg1_floor].
rewrite floorE eqr_int; apply/eqP/(@range1z_inj x) => //.
by rewrite -floorE mem_rg1_floor.
Qed.

Lemma floor_natz (x : int) : floor x%:~R = x%:~R :> R.
Proof. by apply/range1zP/range1rr. Qed.

Lemma floor0 : floor 0 = 0 :> R.
Proof. by rewrite -{1}(mulr0z 1) floor_natz. Qed.

Lemma floor1 : floor 1 = 1 :> R.
Proof. by rewrite -{1}(mulr1z 1) floor_natz. Qed.

Lemma ler_floor (x y : R) : x <= y -> floor x <= floor y.
Proof.
move=> le_xy; case: lerP=> //=; rewrite -Rint_ler_addr1 ?isint_floor //.
move/(ltr_le_trans (floorS_gtr y))/ltr_le_trans/(_ (floor_ler x)).
by rewrite ltrNge le_xy.
Qed.

Lemma floor_ge0 (x : R) : (0 <= floor x) = (0 <= x).
Proof.
apply/idP/idP; last by move/ler_floor; rewrite floor0.
by move/ler_trans=> -/(_ _ (floor_ler x)).
Qed.

Lemma ifloor_ge0 (x : R) : (0 <= ifloor x) = (0 <= x).
Proof. by rewrite -(@ler_int R) -floorE floor_ge0. Qed.
End FloorTheory.

(* -------------------------------------------------------------------- *)
Section Sup.
Context {R : realType}.

Lemma le_down (S : pred R) : {subset S <= down S}.
Proof. by move=> x xS; apply/downP; exists x. Qed.

Lemma downK (S : pred R) : down (down S) =i down S.
Proof.
move=> x; apply/downP/downP=> -[y yS le_xy]; last first.
  by exists y=> //; apply/le_down.
by case/downP: yS => z zS le_yz; exists z => //; apply/(ler_trans le_xy).
Qed.

Lemma eq_ub (S1 S2 : pred R) : S2 =i S1 -> ub S2 =i ub S1.
Proof.
move=> eq_12 x; apply/ubP/ubP=> h y yS; apply/h;
  by rewrite (eq_12, =^~ eq_12).
Qed.

Lemma eq_has_sup (S1 S2 : pred R) :
  S2 =i S1 -> has_sup S2 -> has_sup S1.
Proof.
move=> eq_12 /has_supP[[x xS2] [u uS2]]; apply/has_supP; split.
  by exists x; rewrite -eq_12. by exists u; rewrite (@eq_ub S2).
Qed.

Lemma eq_has_supb (S1 S2 : pred R) :
  S2 =i S1 -> `[< has_sup S2 >] = `[< has_sup S1 >].
Proof. by move=> eq_12; apply/asboolP/asboolP; apply/eq_has_sup. Qed.

Lemma eq_sup (S1 S2 : pred R) : S2 =i S1 -> sup S2 = sup S1.
Proof.
wlog: S1 S2 / (sup S1 <= sup S2) => [wlog|le_S1S2] eq_12.
  by case: (lerP (sup S1) (sup S2)) => [|/ltrW] /wlog ->.
move: le_S1S2; rewrite ler_eqVlt => /orP[/eqP->//|lt_S1S2].
case/boolP: `[< has_sup S2 >] => [/asboolP|] h2; last first.
  by rewrite !sup_out // => /asboolPn; rewrite -?(eq_has_supb eq_12).
pose x : R := sup S2 - sup S1; have gt0_x: 0 < x by rewrite subr_gt0.
have [e eS2] := sup_adherent h2 gt0_x; rewrite subKr => lt_S1e.
have /(eq_has_sup eq_12) h1 := h2; have := eS2; rewrite eq_12.
by move/sup_upper_bound=> -/(_ h1); rewrite lerNgt lt_S1e.
Qed.

Lemma has_sup_down (S : pred R) : has_sup (down S) <-> has_sup S.
Proof.
split=> /has_supP [nzS nzubS]; apply/has_supP.
  case: nzS=> x /downP[y yS le_xy]; split; first by exists y.
  case: nzubS=> u /ubP ubS; exists u; apply/ubP=> z zS.
  by apply/ubS; apply/downP; exists z.
case: nzS=> x xS; split; first by exists x; apply/le_down.
case: nzubS=> u /ubP ubS; exists u; apply/ubP=> y /downP [].
by move=> z zS /ler_trans; apply; apply/ubS.
Qed.

Lemma le_sup (S1 S2 : pred R) :
  {subset S1 <= down S2} -> nonempty S1 -> has_sup S2
    -> sup S1 <= sup S2.
Proof.
move=> le_S12 nz_S1 hs_S2; have hs_S1: has_sup S1.
  apply/has_supP; split=> //; case/has_supP: hs_S2=> _ [x ubx].
  exists x; apply/ubP=> y /le_S12 /downP[z zS2 le_yz].
  by apply/(ler_trans le_yz); move/ubP: ubx; apply.
rewrite lerNgt -subr_gt0; apply/negP => lt_sup.
case: (sup_adherent hs_S1 lt_sup)=> x /le_S12 xdS2.
rewrite subKr => lt_S2x; case/downP: xdS2=> z zS2.
by move/(ltr_le_trans lt_S2x); rewrite ltrNge sup_upper_bound.
Qed.

Lemma sup_down (S : pred R) : sup (down S) = sup S.
Proof.
case/boolP: `[< has_sup S >] => [/asboolP|/asboolPn]; last first.
  by move=> supNS; rewrite !sup_out // => /has_sup_down.
move=> supS; have supDS: has_sup (down S) by apply/has_sup_down.
apply/eqP; rewrite eqr_le !le_sup //.
  by case/has_supP: supS => -[x xS] _; exists x; apply/le_down.
  by move=> x xS; rewrite downK le_down.
  by case/has_supP: supS.
Qed.

Lemma sup1 (c : R) : sup (pred1 c) = c.
Proof.
have hs: has_sup (pred1 c); first (apply/has_supP; split; exists c).
  by rewrite inE eqxx. by apply/ubP => y; rewrite inE => /eqP->.
apply/eqP; rewrite eqr_le sup_upper_bound ?inE // andbT.
apply/sup_le_ub; first by exists c; rewrite inE eqxx.
by apply/ubP=> y; rewrite inE => /eqP ->.
Qed.
End Sup.

(* -------------------------------------------------------------------- *)
Section ExtendedReals.
Variable (R : realType).

Inductive er := ERFin of R | ERPInf | ERNInf.

Coercion real_of_er (x : er) :=
  if x is ERFin v then v else 0.
End ExtendedReals.

Notation "\+inf" := (@ERPInf _).
Notation "\-inf" := (@ERNInf _).
Notation "x %:E" := (@ERFin _ x) (at level 2, format "x %:E").

Notation "{ 'ereal' R }" := (er R) (format "{ 'ereal'  R }").

Bind    Scope ereal_scope with er.
Delimit Scope ereal_scope with E.

(* -------------------------------------------------------------------- *)
Section ERealCode.
Variable (R : realType).

Definition code (x : {ereal R}) :=
  match x with
  | x%:E  => GenTree.Node 0 [:: GenTree.Leaf x]
  | \+inf => GenTree.Node 1 [::]
  | \-inf => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option {ereal R} :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf x] => Some x%:E
  | GenTree.Node 1 [::] => Some \+inf
  | GenTree.Node 2 [::] => Some \-inf
  | _ => None
  end.

Lemma codeK : pcancel code decode.
Proof. by case. Qed.

Definition ereal_eqMixin := PcanEqMixin codeK.
Canonical  ereal_eqType  := EqType {ereal R} ereal_eqMixin.
Definition ereal_choiceMixin := PcanChoiceMixin codeK.
Canonical  ereal_choiceType  := ChoiceType {ereal R} ereal_choiceMixin.
End ERealCode.

Lemma eqe {R : realType} (x1 x2 : R) :
  (x1%:E == x2%:E) = (x1 == x2).
Proof. by apply/eqP/eqP=> [[]|->]. Qed.

(* -------------------------------------------------------------------- *)
Section ERealOrder.
Context {R : realType}.

Definition lee (x1 x2 : {ereal R}) :=
  match x1, x2 with
  | \-inf, _ | _, \+inf => true
  | \+inf, _ | _, \-inf => false

  | x1%:E, x2%:E => (x1 <= x2)
  end.

Definition lte (x1 x2 : {ereal R}) :=
  match x1, x2 with
  | \-inf, \-inf | \+inf, \+inf => false
  | \-inf, _     | _    , \+inf => true
  | \+inf, _     | _    , \-inf => false

  | x1%:E, x2%:E => (x1 < x2)
  end.
End ERealOrder.

Notation "x <= y" := (lee x y) : ereal_scope.
Notation "x < y"  := (lte x y) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) : ereal_scope.

(* -------------------------------------------------------------------- *)
Section ERealArith.
Context {R : realType}.

Implicit Types (x y z : {ereal R}).

Definition eadd x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | \-inf, _     => \-inf
  | _    , \-inf => \-inf
  | \+inf, _     => \+inf
  | _    , \+inf => \+inf
  end.

Definition eopp x :=
  match x with
  | x%:E  => (-x)%:E
  | \-inf => \+inf
  | \+inf => \-inf
  end.
End ERealArith.

Notation "+%E"   := eadd.
Notation "-%E"   := eopp.
Notation "x + y" := (eadd x y) : ereal_scope.
Notation "x - y" := (eadd x (eopp y)) : ereal_scope.
Notation "- x"   := (eopp x) : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%:E]_(i <- r | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%:E]_(i <- r) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%:E]_(m <= i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%:E]_(m <= i < n) F%R) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%:E]_(i | P%B) F%R) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%:E]_i F%R) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%:E]_(i : t | P%B) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%:E]_(i : t) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%:E]_(i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%:E]_(i < n) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%:E]_(i in A | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%:E]_(i in A) F%R) : ereal_scope.

Local Open Scope ereal_scope.

(* -------------------------------------------------------------------- *)
Section ERealArithTh.
Context {R : realType}.

Implicit Types (x y z : {ereal R}).

Lemma adde0 : right_id (0%:E : {ereal R}) +%E.
Proof. by case=> //= x; rewrite addr0. Qed.

Lemma add0e : left_id (S := {ereal R}) 0%:E +%E.
Proof. by case=> //= x; rewrite add0r. Qed.

Lemma addeC : commutative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] //=; rewrite addrC. Qed.

Lemma addeA : associative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] [z||] //=; rewrite addrA. Qed.

Canonical adde_monoid := Monoid.Law addeA add0e adde0.
Canonical adde_comoid := Monoid.ComLaw addeC.

Lemma oppe0 : - (0%:E) = 0%:E :> {ereal R}.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := {ereal R}) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.
End ERealArithTh.

(* -------------------------------------------------------------------- *)
Section ERealOrderTheory.
Context {R : realType}.

Local Open Scope ereal_scope.

Implicit Types x y z : {ereal R}.

Local Tactic Notation "elift" constr(lm) ":" ident(x) :=
  by case: x => [?||]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) :=
  by case: x y => [?||] [?||]; first by rewrite ?eqe; apply: lm.

Local Tactic Notation "elift" constr(lm) ":" ident(x) ident(y) ident(z) :=
  by case: x y z => [?||] [?||] [?||]; first by rewrite ?eqe; apply: lm.

Lemma le0R (l : {ereal R}) : (0%:E <= l)%E -> (0 <= l :> R).
Proof. by case: l. Qed.

Lemma leee x : x <= x.
Proof. by elift lerr: x. Qed.

Lemma ltee x : (x < x) = false.
Proof. by elift ltrr: x. Qed.

Lemma lteW x y : x < y -> x <= y.
Proof. by elift ltrW: x y. Qed.

Lemma eqe_le x y : (x == y) = (x <= y <= x).
Proof. by elift eqr_le: x y. Qed.

Lemma leeNgt x y : (x <= y) = ~~ (y < x).
Proof. by elift lerNgt: x y. Qed.

Lemma lteNgt x y : (x < y) = ~~ (y <= x).
Proof. by elift ltrNge: x y. Qed.

Lemma lee_eqVlt x y : (x <= y) = ((x == y) || (x < y)).
Proof. by elift ler_eqVlt: x y. Qed.

Lemma lte_neqAle x y : (x < y) = ((x != y) && (x <= y)).
Proof. by elift ltr_neqAle: x y. Qed.

Lemma lee_fin (x y : R) : (x%:E <= y%:E)%E = (x <= y)%R.
Proof. by []. Qed.

Lemma lte_fin (x y : R) : (x%:E < y%:E)%E = (x < y)%R.
Proof. by []. Qed.

Lemma lee_tofin (x y : R) : (x <= y)%R -> (x%:E <= y%:E)%E.
Proof. by []. Qed.

Lemma lte_tofin (x y : R) : (x < y)%R -> (x%:E < y%:E)%E.
Proof. by []. Qed.

Lemma lee_trans : transitive _ (@lee R).
Proof. by move=> x y z; elift ler_trans : x y z. Qed.

Lemma lte_trans : transitive _ (@lte R).
Proof. by move=> x y z; elift ltr_trans : x y z. Qed.

Lemma lee_lt_trans y x z : (x <= y) -> (y < z) -> (x < z).
Proof. by elift ler_lt_trans : x y z. Qed.

Lemma lte_le_trans y x z : (x < y) -> (y <= z) -> (x < z).
Proof. by elift ltr_le_trans : x y z. Qed.

Lemma lee_opp2 : {mono @eopp R : x y /~ (x <= y)}.
Proof. by move=> x y; elift ler_opp2 : x y. Qed.

Lemma lte_opp2 : {mono @eopp R : x y /~ (x < y)}.
Proof. by move=> x y; elift ltr_opp2 : x y. Qed.
End ERealOrderTheory.
